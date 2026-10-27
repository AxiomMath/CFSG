module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open scoped MatrixGroups Pointwise

section Sup

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup_of_commute {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, Commute h k) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  let S : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
      mul_mem' := by
        rintro _ _ ⟨h, hh, k, hk, rfl⟩ ⟨h', hh', k', hk', rfl⟩
        refine ⟨h * h', H.mul_mem hh hh', k * k', K.mul_mem hk hk', ?_⟩
        rw [mul_assoc, ← mul_assoc k h', ← (hc h' hh' k hk).eq, mul_assoc, mul_assoc]
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by rw [mul_one]⟩
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
        rw [mul_inv_rev]
        exact ((hc h⁻¹ (H.inv_mem hh) k⁻¹ (K.inv_mem hk)).eq).symm }
  have hle : H ⊔ K ≤ S := sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, by rw [mul_one]⟩)
    (fun k hk => ⟨1, H.one_mem, k, hk, by rw [one_mul]⟩)
  exact hle hx

end Sup

section Plane

variable {G M : Type*} [Group G] [Group M] [Finite G] [Finite M] {p : ℕ} [hp : Fact p.Prime]

theorem isCyclic_of_isPGroup_of_centralizer
    (hcyc : ∀ g : M, orderOf g = p → IsCyclic (Subgroup.centralizer ({g} : Set M)))
    {P : Subgroup M} (hP : IsPGroup p P) : IsCyclic P := by
  classical
  by_cases hbot : P = ⊥
  · subst hbot
    infer_instance
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hbot
  have hZ : Nontrivial (Subgroup.center P) := hP.center_nontrivial
  have hZp : IsPGroup p (Subgroup.center P) := hP.to_subgroup _
  obtain ⟨k, hk⟩ := hZp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    have := (Nat.card_eq_one_iff_unique.1 hk).1
    exact (not_subsingleton _) this
  have hdvd : p ∣ Nat.card (Subgroup.center P) := by
    rw [hk]
    exact dvd_pow_self p hk0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  set z' : M := ((z : P) : M) with hz'
  have hz'o : orderOf z' = p := by
    rw [hz', Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hle : P ≤ Subgroup.centralizer ({z'} : Set M) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_center_iff.1 z.2 ⟨y, hy⟩
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_mul] at h'
    exact h'
  have := hcyc z' hz'o
  have hcyc' : IsCyclic ((P.subgroupOf (Subgroup.centralizer ({z'} : Set M)))) := inferInstance
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hle).surjective

theorem exists_conj_plane_of_frame (ψA ψB : M →* G) (hA : Function.Injective ψA)
    (hB : Function.Injective ψB) (hcomm : ∀ x y, Commute (ψA x) (ψB y))
    (hcyc : ∀ g : M, orderOf g = p → IsCyclic (Subgroup.centralizer ({g} : Set M)))
    (hAB : ¬ p ∣ Nat.card ↥(ψA.range ⊓ ψB.range))
    (hcard : (Nat.card G).factorization p = 2 * (Nat.card M).factorization p)
    (E : Subgroup G) (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    ∃ (g : G) (a : M), orderOf a = p ∧
      E.map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (ψA a) ⊔ Subgroup.zpowers (ψB a) := by
  classical
  obtain ⟨P⟩ : Nonempty (Sylow p M) := inferInstance
  have hPcyc : IsCyclic (P : Subgroup M) := isCyclic_of_isPGroup_of_centralizer hcyc P.isPGroup'
  let f : (P : Subgroup M) →* G := ψA.comp (P : Subgroup M).subtype
  let g' : (P : Subgroup M) →* G := ψB.comp (P : Subgroup M).subtype
  have hfg : ∀ x y, Commute (f x) (g' y) := fun x y => hcomm _ _
  let μ := f.noncommCoprod g' hfg
  have hμ : ∀ u v, μ (u, v) = ψA (u : M) * ψB (v : M) := fun u v => rfl
  have hfi : Function.Injective f := hA.comp Subtype.val_injective
  have hgi : Function.Injective g' := hB.comp Subtype.val_injective
  have hdisj : Disjoint f.range g'.range := by
    rw [disjoint_iff]
    have hle : f.range ⊓ g'.range ≤ ψA.range ⊓ ψB.range := by
      refine inf_le_inf ?_ ?_
      · rintro _ ⟨y, rfl⟩
        exact ⟨_, rfl⟩
      · rintro _ ⟨y, rfl⟩
        exact ⟨_, rfl⟩
    have hpg : IsPGroup p ↥(f.range ⊓ g'.range) :=
      (IsPGroup.of_surjective P.isPGroup' f.rangeRestrict f.rangeRestrict_surjective).to_le
        inf_le_left
    obtain ⟨k, hk⟩ := hpg.exists_card_eq
    have hdvd : Nat.card ↥(f.range ⊓ g'.range) ∣ Nat.card ↥(ψA.range ⊓ ψB.range) :=
      Subgroup.card_dvd_of_le hle
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq _ hk
    · exfalso
      apply hAB
      rw [hk] at hdvd
      exact (dvd_pow_self p (Nat.succ_ne_zero k)).trans hdvd
  have hμinj : Function.Injective μ :=
    (MonoidHom.noncommCoprod_injective f g' hfg).2 ⟨hfi, hgi, hdisj⟩
  have hcardS : Nat.card μ.range = p ^ (Nat.card G).factorization p := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hμinj).toEquiv, Nat.card_prod,
      P.card_eq_multiplicity, hcard, ← pow_add, two_mul]
  let S : Sylow p G := Sylow.ofCard μ.range hcardS
  obtain ⟨Q, hEQ⟩ := (IsPGroup.of_card hEc).exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G Q S
  set E' := E.map (MulAut.conj x).toMonoidHom with hE'
  have hE'S : E' ≤ μ.range := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : MulAut.conj x • y ∈ MulAut.conj x • (Q : Subgroup G) :=
      Subgroup.smul_mem_pointwise_smul y _ _ (hEQ hy)
    rw [← Sylow.coe_subgroup_smul, hx] at h1
    exact h1
  have hE'p : ∀ z ∈ E', z ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hEp y hy, map_one]
  have hE'c : Nat.card E' = p ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj x).injective, hEc]
  set Ehat := E'.comap μ with hEhat
  have hEhatc : Nat.card Ehat = p ^ 2 := by
    rw [← hE'c, ← Subgroup.map_comap_eq_self hE'S, hEhat,
      Subgroup.card_map_of_injective hμinj]
  have hEhatp : ∀ w ∈ Ehat, w.1 ^ p = 1 ∧ w.2 ^ p = 1 := by
    intro w hw
    have h1 : μ (w ^ p) = 1 := by rw [map_pow]; exact hE'p _ hw
    have h2 : w ^ p = 1 := hμinj (h1.trans (map_one μ).symm)
    exact ⟨by simpa using congrArg Prod.fst h2, by simpa using congrArg Prod.snd h2⟩
  have : Fintype (P : Subgroup M) := Fintype.ofFinite _
  let Ω : Finset (P : Subgroup M) := Finset.univ.filter fun u => u ^ p = 1
  have hΩ : Ω.card ≤ p := IsCyclic.card_pow_eq_one_le hp.out.pos
  let Eh : Finset (↥(P : Subgroup M) × ↥(P : Subgroup M)) := Finset.univ.filter fun w => w ∈ Ehat
  have hEhcard : Eh.card = p ^ 2 := by
    rw [← hEhatc, Nat.card_eq_fintype_card, ← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (by simp [Eh]))
  have hsub : Eh ⊆ Ω ×ˢ Ω := by
    intro w hw
    have hw' : w ∈ Ehat := (Finset.mem_filter.1 hw).2
    obtain ⟨h1, h2⟩ := hEhatp w hw'
    exact Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩⟩
  have hle2 : p ^ 2 ≤ Ω.card * Ω.card := by
    rw [← hEhcard, ← Finset.card_product]
    exact Finset.card_le_card hsub
  have hΩp : Ω.card = p := by
    by_contra hne
    have hlt : Ω.card < p := lt_of_le_of_ne hΩ hne
    have : Ω.card * Ω.card < p * p := Nat.mul_lt_mul'' hlt hlt
    nlinarith
  have hEq : Eh = Ω ×ˢ Ω := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_product, hΩp, hEhcard, sq])
  obtain ⟨a, haΩ, ha1⟩ : ∃ a ∈ Ω, a ≠ 1 :=
    Finset.exists_mem_ne (by rw [hΩp]; exact hp.out.one_lt) 1
  have hap : a ^ p = 1 := (Finset.mem_filter.1 haΩ).2
  have hao : orderOf (a : M) = p := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hap ha1
  have hΩa : ∀ u ∈ Ω, u ∈ Subgroup.zpowers a := by
    have hoa : orderOf a = p := orderOf_eq_prime hap ha1
    have hzc : (Finset.univ.filter fun u => u ∈ Subgroup.zpowers a).card = p := by
      calc (Finset.univ.filter fun u => u ∈ Subgroup.zpowers a).card
          = Nat.card (Subgroup.zpowers a) := by
            rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
            exact Fintype.card_congr (Equiv.subtypeEquivRight (by simp))
        _ = orderOf a := Nat.card_zpowers a
        _ = p := hoa
    have hzΩ : (Finset.univ.filter fun u => u ∈ Subgroup.zpowers a) ⊆ Ω := by
      intro u hu
      obtain ⟨k, rfl⟩ := (Finset.mem_filter.1 hu).2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      show (a ^ k) ^ p = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap, one_zpow]
    have heq := Finset.eq_of_subset_of_card_le hzΩ (by rw [hzc, hΩp])
    intro u hu
    rw [← heq] at hu
    exact (Finset.mem_filter.1 hu).2
  refine ⟨x, (a : M), hao, le_antisymm ?_ ?_⟩
  · intro z hz
    obtain ⟨⟨u, v⟩, rfl⟩ := hE'S hz
    have hw : ((u, v) : ↥(P : Subgroup M) × ↥(P : Subgroup M)) ∈ Eh :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hz⟩
    rw [hEq] at hw
    obtain ⟨hu, hv⟩ := Finset.mem_product.1 hw
    obtain ⟨i, rfl⟩ := hΩa u hu
    obtain ⟨j, rfl⟩ := hΩa v hv
    rw [hμ]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨i, ?_⟩) (Subgroup.mem_sup_right ⟨j, ?_⟩)
    · simp
    · simp
  · rw [sup_le_iff, Subgroup.zpowers_le, Subgroup.zpowers_le]
    have h1 : ((a, 1) : ↥(P : Subgroup M) × ↥(P : Subgroup M)) ∈ Eh := by
      rw [hEq]
      exact Finset.mem_product.2 ⟨haΩ, Finset.mem_filter.2 ⟨Finset.mem_univ _, one_pow p⟩⟩
    have h2 : ((1, a) : ↥(P : Subgroup M) × ↥(P : Subgroup M)) ∈ Eh := by
      rw [hEq]
      exact Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, one_pow p⟩, haΩ⟩
    have h1' := (Finset.mem_filter.1 h1).2
    have h2' := (Finset.mem_filter.1 h2).2
    refine ⟨?_, ?_⟩
    · have : μ (a, 1) = ψA (a : M) := by rw [hμ]; simp
      rw [← this]
      exact h1'
    · have : μ (1, a) = ψB (a : M) := by rw [hμ]; simp
      rw [← this]
      exact h2'

omit [Finite G] [Finite M] in
theorem commute_of_frame_mem_range {ψA ψB : M →* G} (hA : Function.Injective ψA)
    (hcomm : ∀ x y, Commute (ψA x) (ψB y)) {c : M} (hc : ψA c ∈ ψB.range) (x : M) :
    Commute x c := by
  obtain ⟨d, hd⟩ := hc
  apply hA
  rw [map_mul, map_mul, ← hd]
  exact (hcomm x d).eq

omit [Finite G] [Finite M] in
theorem eq_one_of_mem_frame_inf {ψA ψB : M →* G} (hAB : ¬ p ∣ Nat.card ↥(ψA.range ⊓ ψB.range))
    {z : G} (hz : z ∈ ψA.range ⊓ ψB.range) (hzp : z ^ p = 1) : z = 1 := by
  have h1 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
  have h2 : orderOf z ∣ Nat.card ↥(ψA.range ⊓ ψB.range) :=
    Subgroup.orderOf_dvd_natCard (ψA.range ⊓ ψB.range) hz
  rcases (Nat.dvd_prime hp.out).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ h2) hAB

omit [Finite G] [Finite M] in
theorem mem_centralizer_of_commute_frame {ψA ψB : M →* G} (hA : Function.Injective ψA)
    (hcomm : ∀ x y, Commute (ψA x) (ψB y)) (hAB : ¬ p ∣ Nat.card ↥(ψA.range ⊓ ψB.range))
    {a b u v : M} (ha : orderOf a = p)
    (h : Commute (ψA u * ψB v) (ψA a * ψB b)) : u ∈ Subgroup.centralizer ({a} : Set M) := by
  have h1 : ψA (u * a) * ψB (v * b) = ψA (a * u) * ψB (b * v) := by
    have e := h.eq
    have c1 := (hcomm a v).eq
    have c2 := (hcomm u b).eq
    simp only [map_mul]
    calc ψA u * ψA a * (ψB v * ψB b) = ψA u * (ψA a * ψB v) * ψB b := by group
      _ = ψA u * (ψB v * ψA a) * ψB b := by rw [c1]
      _ = ψA u * ψB v * (ψA a * ψB b) := by group
      _ = ψA a * ψB b * (ψA u * ψB v) := e
      _ = ψA a * (ψB b * ψA u) * ψB v := by group
      _ = ψA a * (ψA u * ψB b) * ψB v := by rw [c2]
      _ = ψA a * ψA u * (ψB b * ψB v) := by group
  set c : M := (a * u)⁻¹ * (u * a) with hcdef
  have hc : ψA c = ψB ((b * v) * (v * b)⁻¹) := by
    have eL : ψA c = (ψA (a * u))⁻¹ * ψA (u * a) := by rw [hcdef, map_mul, map_inv]
    have eR : ψB ((b * v) * (v * b)⁻¹) = ψB (b * v) * (ψB (v * b))⁻¹ := by
      rw [map_mul, map_inv]
    rw [eL, eR]
    calc (ψA (a * u))⁻¹ * ψA (u * a)
        = (ψA (a * u))⁻¹ * (ψA (u * a) * ψB (v * b)) * (ψB (v * b))⁻¹ := by group
      _ = (ψA (a * u))⁻¹ * (ψA (a * u) * ψB (b * v)) * (ψB (v * b))⁻¹ := by rw [h1]
      _ = ψB (b * v) * (ψB (v * b))⁻¹ := by group
  have hcB : ψA c ∈ ψB.range := ⟨_, hc.symm⟩
  have hcZ : ∀ x, Commute x c := commute_of_frame_mem_range hA hcomm hcB
  have h2 : a⁻¹ * (u * a * u⁻¹) = c := by
    calc a⁻¹ * (u * a * u⁻¹) = u * c * u⁻¹ := by rw [hcdef]; group
      _ = c := by rw [(hcZ u).eq]; group
  have hconj : u * a * u⁻¹ = a * c := by rw [← h2]; group
  have hap : a ^ p = 1 := ha ▸ pow_orderOf_eq_one a
  have hcp : c ^ p = 1 := by
    have e1 : (u * a * u⁻¹) ^ p = 1 := by rw [conj_pow, hap]; group
    rw [hconj, (hcZ a).mul_pow, hap, one_mul] at e1
    exact e1
  have hc1 : ψA c = 1 := eq_one_of_mem_frame_inf hAB ⟨⟨c, rfl⟩, hcB⟩
    (by rw [← map_pow, hcp, map_one])
  have hc1' : c = 1 := hA (hc1.trans (map_one ψA).symm)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have : u * a * u⁻¹ = a := by rw [hconj, hc1', mul_one]
  calc u * a = u * a * u⁻¹ * u := by group
    _ = a * u := by rw [this]

omit [Finite G] [Finite M] in
theorem commute_of_mem_centralizer_frame (ψA ψB : M →* G) (hA : Function.Injective ψA)
    (hB : Function.Injective ψB) (hcomm : ∀ x y, Commute (ψA x) (ψB y))
    (hcyc : ∀ g : M, orderOf g = p → IsCyclic (Subgroup.centralizer ({g} : Set M)))
    (hAB : ¬ p ∣ Nat.card ↥(ψA.range ⊓ ψB.range)) {a b : M} (ha : orderOf a = p)
    (hb : orderOf b = p) {y y' : G} (hy : y ∈ ψA.range ⊔ ψB.range)
    (hy' : y' ∈ ψA.range ⊔ ψB.range) (hye : Commute y (ψA a * ψB b))
    (hy'e : Commute y' (ψA a * ψB b)) : Commute y y' := by
  have hc : ∀ h ∈ ψA.range, ∀ k ∈ ψB.range, Commute h k := by
    rintro _ ⟨x, rfl⟩ _ ⟨z, rfl⟩
    exact hcomm x z
  have hcomm' : ∀ x y, Commute (ψB x) (ψA y) := fun x y => (hcomm y x).symm
  have hBA : ¬ p ∣ Nat.card ↥(ψB.range ⊓ ψA.range) := by rwa [inf_comm]
  obtain ⟨_, ⟨u, rfl⟩, _, ⟨v, rfl⟩, rfl⟩ := exists_mul_of_mem_sup_of_commute hc hy
  obtain ⟨_, ⟨u', rfl⟩, _, ⟨v', rfl⟩, rfl⟩ := exists_mul_of_mem_sup_of_commute hc hy'
  have swap : ∀ {s t : M}, Commute (ψA s * ψB t) (ψA a * ψB b) →
      Commute (ψB t * ψA s) (ψB b * ψA a) := fun {s t} h => by
    rw [← (hcomm s t).eq, ← (hcomm a b).eq]
    exact h
  have hu := mem_centralizer_of_commute_frame hA hcomm hAB ha hye
  have hu' := mem_centralizer_of_commute_frame hA hcomm hAB ha hy'e
  have hv := mem_centralizer_of_commute_frame hB hcomm' hBA hb (swap hye)
  have hv' := mem_centralizer_of_commute_frame hB hcomm' hBA hb (swap hy'e)
  have huu : Commute u u' := by
    have := hcyc a ha
    have h := (IsCyclic.commGroup (α := Subgroup.centralizer ({a} : Set M))).mul_comm ⟨u, hu⟩ ⟨u', hu'⟩
    exact congrArg Subtype.val h
  have hvv : Commute v v' := by
    have := hcyc b hb
    have h := (IsCyclic.commGroup (α := Subgroup.centralizer ({b} : Set M))).mul_comm ⟨v, hv⟩ ⟨v', hv'⟩
    exact congrArg Subtype.val h
  have e1 := (hcomm u' v).eq
  have e2 := (hcomm u v').eq
  show ψA u * ψB v * (ψA u' * ψB v') = ψA u' * ψB v' * (ψA u * ψB v)
  calc ψA u * ψB v * (ψA u' * ψB v') = ψA u * (ψB v * ψA u') * ψB v' := by group
    _ = ψA u * (ψA u' * ψB v) * ψB v' := by rw [e1]
    _ = ψA (u * u') * ψB (v * v') := by rw [map_mul, map_mul]; group
    _ = ψA (u' * u) * ψB (v' * v) := by rw [huu.eq, hvv.eq]
    _ = ψA u' * (ψA u * ψB v') * ψB v := by rw [map_mul, map_mul]; group
    _ = ψA u' * (ψB v' * ψA u) * ψB v := by rw [e2]
    _ = ψA u' * ψB v' * (ψA u * ψB v) := by group

end Plane

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
