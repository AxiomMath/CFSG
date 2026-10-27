module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Defs
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Plane
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
open scoped Pointwise

section Plane

variable {G M₁ M₂ : Type*} [Group G] [Group M₁] [Group M₂] {p : ℕ} [hp : Fact p.Prime]

omit [Fact p.Prime] in
theorem commute_of_twoFrames_mem_range {ψA : M₁ →* G} {ψB : M₂ →* G} (hA : Function.Injective ψA)
    (hcomm : ∀ x y, Commute (ψA x) (ψB y)) {c : M₁} (hc : ψA c ∈ ψB.range) (x : M₁) :
    Commute x c := by
  obtain ⟨d, hd⟩ := hc
  apply hA
  rw [map_mul, map_mul, ← hd]
  exact (hcomm x d).eq

theorem eq_one_of_mem_twoFrames_inf {ψA : M₁ →* G} {ψB : M₂ →* G}
    (hAB : ¬ p ∣ Nat.card ↥(ψA.range ⊓ ψB.range)) {z : G} (hz : z ∈ ψA.range ⊓ ψB.range)
    (hzp : z ^ p = 1) : z = 1 := by
  have h1 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
  have h2 : orderOf z ∣ Nat.card ↥(ψA.range ⊓ ψB.range) :=
    Subgroup.orderOf_dvd_natCard (ψA.range ⊓ ψB.range) hz
  rcases (Nat.dvd_prime hp.out).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ h2) hAB

theorem mem_centralizer_of_commute_twoFrames {ψA : M₁ →* G} {ψB : M₂ →* G}
    (hA : Function.Injective ψA) (hcomm : ∀ x y, Commute (ψA x) (ψB y))
    (hAB : ¬ p ∣ Nat.card ↥(ψA.range ⊓ ψB.range)) {a u : M₁} {b v : M₂} (ha : orderOf a = p)
    (h : Commute (ψA u * ψB v) (ψA a * ψB b)) : u ∈ Subgroup.centralizer ({a} : Set M₁) := by
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
  set c : M₁ := (a * u)⁻¹ * (u * a) with hcdef
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
  have hcZ : ∀ x, Commute x c := commute_of_twoFrames_mem_range hA hcomm hcB
  have h2 : a⁻¹ * (u * a * u⁻¹) = c := by
    calc a⁻¹ * (u * a * u⁻¹) = u * c * u⁻¹ := by rw [hcdef]; group
      _ = c := by rw [(hcZ u).eq]; group
  have hconj : u * a * u⁻¹ = a * c := by rw [← h2]; group
  have hap : a ^ p = 1 := ha ▸ pow_orderOf_eq_one a
  have hcp : c ^ p = 1 := by
    have e1 : (u * a * u⁻¹) ^ p = 1 := by rw [conj_pow, hap]; group
    rw [hconj, (hcZ a).mul_pow, hap, one_mul] at e1
    exact e1
  have hc1 : ψA c = 1 := eq_one_of_mem_twoFrames_inf hAB ⟨⟨c, rfl⟩, hcB⟩
    (by rw [← map_pow, hcp, map_one])
  have hc1' : c = 1 := hA (hc1.trans (map_one ψA).symm)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have : u * a * u⁻¹ = a := by rw [hconj, hc1', mul_one]
  calc u * a = u * a * u⁻¹ * u := by group
    _ = a * u := by rw [this]

theorem commute_of_mem_centralizer_twoFrames (ψA : M₁ →* G) (ψB : M₂ →* G)
    (hA : Function.Injective ψA) (hB : Function.Injective ψB)
    (hcomm : ∀ x y, Commute (ψA x) (ψB y))
    (hcycA : ∀ g : M₁, orderOf g = p → IsCyclic (Subgroup.centralizer ({g} : Set M₁)))
    (hcycB : ∀ g : M₂, orderOf g = p → IsCyclic (Subgroup.centralizer ({g} : Set M₂)))
    (hAB : ¬ p ∣ Nat.card ↥(ψA.range ⊓ ψB.range)) {a : M₁} {b : M₂} (ha : orderOf a = p)
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
  have swap : ∀ {s : M₁} {t : M₂}, Commute (ψA s * ψB t) (ψA a * ψB b) →
      Commute (ψB t * ψA s) (ψB b * ψA a) := fun {s t} h => by
    rw [← (hcomm s t).eq, ← (hcomm a b).eq]
    exact h
  have hu := mem_centralizer_of_commute_twoFrames hA hcomm hAB ha hye
  have hu' := mem_centralizer_of_commute_twoFrames hA hcomm hAB ha hy'e
  have hv := mem_centralizer_of_commute_twoFrames hB hcomm' hBA hb (swap hye)
  have hv' := mem_centralizer_of_commute_twoFrames hB hcomm' hBA hb (swap hy'e)
  have huu : Commute u u' := by
    have := hcycA a ha
    have h := (IsCyclic.commGroup (α := Subgroup.centralizer ({a} : Set M₁))).mul_comm ⟨u, hu⟩
      ⟨u', hu'⟩
    exact congrArg Subtype.val h
  have hvv : Commute v v' := by
    have := hcycB b hb
    have h := (IsCyclic.commGroup (α := Subgroup.centralizer ({b} : Set M₂))).mul_comm ⟨v, hv⟩
      ⟨v', hv'⟩
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

section Conj

variable {G M₁ M₂ : Type*} [Group G] [Group M₁] [Group M₂] [Finite G] [Finite M₁] [Finite M₂]
  {p : ℕ} [hp : Fact p.Prime]

theorem exists_conj_plane_of_twoFrames (ψA : M₁ →* G) (ψB : M₂ →* G) (hA : Function.Injective ψA)
    (hB : Function.Injective ψB) (hcomm : ∀ x y, Commute (ψA x) (ψB y))
    (hcycA : ∀ g : M₁, orderOf g = p → IsCyclic (Subgroup.centralizer ({g} : Set M₁)))
    (hcycB : ∀ g : M₂, orderOf g = p → IsCyclic (Subgroup.centralizer ({g} : Set M₂)))
    (hAB : ¬ p ∣ Nat.card ↥(ψA.range ⊓ ψB.range))
    (hcard : (Nat.card G).factorization p =
      (Nat.card M₁).factorization p + (Nat.card M₂).factorization p)
    (E : Subgroup G) (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    ∃ (g : G) (a : M₁) (b : M₂), orderOf a = p ∧ orderOf b = p ∧
      E.map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (ψA a) ⊔ Subgroup.zpowers (ψB b) := by
  classical
  obtain ⟨P₁⟩ : Nonempty (Sylow p M₁) := inferInstance
  obtain ⟨P₂⟩ : Nonempty (Sylow p M₂) := inferInstance
  have hP₁cyc : IsCyclic (P₁ : Subgroup M₁) :=
    isCyclic_of_isPGroup_of_centralizer hcycA P₁.isPGroup'
  have hP₂cyc : IsCyclic (P₂ : Subgroup M₂) :=
    isCyclic_of_isPGroup_of_centralizer hcycB P₂.isPGroup'
  let f : (P₁ : Subgroup M₁) →* G := ψA.comp (P₁ : Subgroup M₁).subtype
  let g' : (P₂ : Subgroup M₂) →* G := ψB.comp (P₂ : Subgroup M₂).subtype
  have hfg : ∀ x y, Commute (f x) (g' y) := fun x y => hcomm _ _
  let μ := f.noncommCoprod g' hfg
  have hμ : ∀ u v, μ (u, v) = ψA (u : M₁) * ψB (v : M₂) := fun u v => rfl
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
      (IsPGroup.of_surjective P₁.isPGroup' f.rangeRestrict f.rangeRestrict_surjective).to_le
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
      P₁.card_eq_multiplicity, P₂.card_eq_multiplicity, hcard, pow_add]
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
  have : Fintype (P₁ : Subgroup M₁) := Fintype.ofFinite _
  have : Fintype (P₂ : Subgroup M₂) := Fintype.ofFinite _
  let Ω₁ : Finset (P₁ : Subgroup M₁) := Finset.univ.filter fun u => u ^ p = 1
  let Ω₂ : Finset (P₂ : Subgroup M₂) := Finset.univ.filter fun u => u ^ p = 1
  have hΩ₁ : Ω₁.card ≤ p := IsCyclic.card_pow_eq_one_le hp.out.pos
  have hΩ₂ : Ω₂.card ≤ p := IsCyclic.card_pow_eq_one_le hp.out.pos
  let Eh : Finset (↥(P₁ : Subgroup M₁) × ↥(P₂ : Subgroup M₂)) :=
    Finset.univ.filter fun w => w ∈ Ehat
  have hEhcard : Eh.card = p ^ 2 := by
    rw [← hEhatc, Nat.card_eq_fintype_card, ← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (by simp [Eh]))
  have hsub : Eh ⊆ Ω₁ ×ˢ Ω₂ := by
    intro w hw
    have hw' : w ∈ Ehat := (Finset.mem_filter.1 hw).2
    obtain ⟨h1, h2⟩ := hEhatp w hw'
    exact Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩⟩
  have hle2 : p ^ 2 ≤ Ω₁.card * Ω₂.card := by
    rw [← hEhcard, ← Finset.card_product]
    exact Finset.card_le_card hsub
  have hΩ₁p : Ω₁.card = p := by
    by_contra hne
    have hlt : Ω₁.card < p := lt_of_le_of_ne hΩ₁ hne
    have : Ω₁.card * Ω₂.card < p * p := Nat.mul_lt_mul_of_lt_of_le hlt hΩ₂ hp.out.pos
    nlinarith
  have hΩ₂p : Ω₂.card = p := by
    by_contra hne
    have hlt : Ω₂.card < p := lt_of_le_of_ne hΩ₂ hne
    have : Ω₁.card * Ω₂.card < p * p := Nat.mul_lt_mul_of_le_of_lt hΩ₁ hlt hp.out.pos
    nlinarith
  have hEq : Eh = Ω₁ ×ˢ Ω₂ := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_product, hΩ₁p, hΩ₂p, hEhcard, sq])
  obtain ⟨a, haΩ, ha1⟩ : ∃ a ∈ Ω₁, a ≠ 1 :=
    Finset.exists_mem_ne (by rw [hΩ₁p]; exact hp.out.one_lt) 1
  obtain ⟨b, hbΩ, hb1⟩ : ∃ b ∈ Ω₂, b ≠ 1 :=
    Finset.exists_mem_ne (by rw [hΩ₂p]; exact hp.out.one_lt) 1
  have hap : a ^ p = 1 := (Finset.mem_filter.1 haΩ).2
  have hbp : b ^ p = 1 := (Finset.mem_filter.1 hbΩ).2
  have hao : orderOf (a : M₁) = p := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hap ha1
  have hbo : orderOf (b : M₂) = p := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hbp hb1
  have hΩa : ∀ u ∈ Ω₁, u ∈ Subgroup.zpowers a := by
    have hoa : orderOf a = p := orderOf_eq_prime hap ha1
    have hzc : (Finset.univ.filter fun u => u ∈ Subgroup.zpowers a).card = p := by
      calc (Finset.univ.filter fun u => u ∈ Subgroup.zpowers a).card
          = Nat.card (Subgroup.zpowers a) := by
            rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
            exact Fintype.card_congr (Equiv.subtypeEquivRight (by simp))
        _ = orderOf a := Nat.card_zpowers a
        _ = p := hoa
    have hzΩ : (Finset.univ.filter fun u => u ∈ Subgroup.zpowers a) ⊆ Ω₁ := by
      intro u hu
      obtain ⟨k, rfl⟩ := (Finset.mem_filter.1 hu).2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      show (a ^ k) ^ p = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap, one_zpow]
    have heq := Finset.eq_of_subset_of_card_le hzΩ (by rw [hzc, hΩ₁p])
    intro u hu
    rw [← heq] at hu
    exact (Finset.mem_filter.1 hu).2
  have hΩb : ∀ u ∈ Ω₂, u ∈ Subgroup.zpowers b := by
    have hob : orderOf b = p := orderOf_eq_prime hbp hb1
    have hzc : (Finset.univ.filter fun u => u ∈ Subgroup.zpowers b).card = p := by
      calc (Finset.univ.filter fun u => u ∈ Subgroup.zpowers b).card
          = Nat.card (Subgroup.zpowers b) := by
            rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
            exact Fintype.card_congr (Equiv.subtypeEquivRight (by simp))
        _ = orderOf b := Nat.card_zpowers b
        _ = p := hob
    have hzΩ : (Finset.univ.filter fun u => u ∈ Subgroup.zpowers b) ⊆ Ω₂ := by
      intro u hu
      obtain ⟨k, rfl⟩ := (Finset.mem_filter.1 hu).2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      show (b ^ k) ^ p = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hbp, one_zpow]
    have heq := Finset.eq_of_subset_of_card_le hzΩ (by rw [hzc, hΩ₂p])
    intro u hu
    rw [← heq] at hu
    exact (Finset.mem_filter.1 hu).2
  refine ⟨x, (a : M₁), (b : M₂), hao, hbo, le_antisymm ?_ ?_⟩
  · intro z hz
    obtain ⟨⟨u, v⟩, rfl⟩ := hE'S hz
    have hw : ((u, v) : ↥(P₁ : Subgroup M₁) × ↥(P₂ : Subgroup M₂)) ∈ Eh :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hz⟩
    rw [hEq] at hw
    obtain ⟨hu, hv⟩ := Finset.mem_product.1 hw
    obtain ⟨i, rfl⟩ := hΩa u hu
    obtain ⟨j, rfl⟩ := hΩb v hv
    rw [hμ]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨i, ?_⟩) (Subgroup.mem_sup_right ⟨j, ?_⟩)
    · simp
    · simp
  · rw [sup_le_iff, Subgroup.zpowers_le, Subgroup.zpowers_le]
    have h1 : ((a, 1) : ↥(P₁ : Subgroup M₁) × ↥(P₂ : Subgroup M₂)) ∈ Eh := by
      rw [hEq]
      exact Finset.mem_product.2 ⟨haΩ, Finset.mem_filter.2 ⟨Finset.mem_univ _, one_pow p⟩⟩
    have h2 : ((1, b) : ↥(P₁ : Subgroup M₁) × ↥(P₂ : Subgroup M₂)) ∈ Eh := by
      rw [hEq]
      exact Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, one_pow p⟩, hbΩ⟩
    have h1' := (Finset.mem_filter.1 h1).2
    have h2' := (Finset.mem_filter.1 h2).2
    refine ⟨?_, ?_⟩
    · have : μ (a, 1) = ψA (a : M₁) := by rw [hμ]; simp
      rw [← this]
      exact h1'
    · have : μ (1, b) = ψB (b : M₂) := by rw [hμ]; simp
      rw [← this]
      exact h2'

end Conj

section Main

variable {G M₁ M₂ : Type*} [Group G] [Group M₁] [Group M₂] [Finite G] [Finite M₁] [Finite M₂]
  {p : ℕ} [hp : Fact p.Prime]

theorem closure_centralizers_eq_top_of_twoFrames (ψA : M₁ →* G) (ψB : M₂ →* G)
    (hA : Function.Injective ψA) (hB : Function.Injective ψB)
    (hcomm : ∀ x y, Commute (ψA x) (ψB y))
    (hC : ∀ H : Subgroup G, ψA.range ⊔ ψB.range ≤ H →
      ¬ H ≤ Subgroup.normalizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G) → H = ⊤)
    (hN : ∀ P : Subgroup G, P ≤ Subgroup.normalizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G) →
      Group.IsSolvable ↥(P ⊓ (ψA.range ⊔ ψB.range)) → Group.IsSolvable ↥P)
    (hcycA : ∀ g : M₁, orderOf g = p → IsCyclic (Subgroup.centralizer ({g} : Set M₁)))
    (hcycB : ∀ g : M₂, orderOf g = p → IsCyclic (Subgroup.centralizer ({g} : Set M₂)))
    (hAB : ¬ p ∣ Nat.card ↥(ψA.range ⊓ ψB.range))
    (hcard : (Nat.card G).factorization p =
      (Nat.card M₁).factorization p + (Nat.card M₂).factorization p)
    (hthird : ∀ E : Subgroup G, Nat.card E = p ^ 2 → (∀ x ∈ E, x ^ p = 1) →
      ∀ a b : G, a ∈ E → b ∈ E → a ≠ 1 → b ≠ 1 →
        ∃ e ∈ E, e ∉ Subgroup.zpowers a ∧ e ∉ Subgroup.zpowers b ∧
          ∃ P : Subgroup G, P ≤ Subgroup.centralizer ({e} : Set G) ∧ ¬ Group.IsSolvable ↥P)
    (E : Subgroup G) (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    Subgroup.closure {k : G | ∃ x ∈ E, x ≠ 1 ∧ Commute k x} = ⊤ := by
  classical
  obtain ⟨g, a, b, hao, hbo, hEg⟩ :=
    exists_conj_plane_of_twoFrames ψA ψB hA hB hcomm hcycA hcycB hAB hcard E hEp hEc
  set E' := E.map (MulAut.conj g).toMonoidHom with hE'
  set T : Subgroup G → Set G := fun F => {k | ∃ x ∈ F, x ≠ 1 ∧ Commute k x} with hTdef
  have hTE : T E' = (MulAut.conj g).toMonoidHom '' T E := by
    ext k
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, hx1, hkx⟩
      refine ⟨g⁻¹ * k * g, ⟨x, hx, fun h => hx1 (by simp [h]), ?_⟩, by simp [MulAut.conj_apply]; group⟩
      have h := hkx.eq
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply] at h
      show g⁻¹ * k * g * x = x * (g⁻¹ * k * g)
      calc g⁻¹ * k * g * x = g⁻¹ * (k * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * k) * g := by rw [h]
        _ = x * (g⁻¹ * k * g) := by group
    · rintro ⟨k₀, ⟨x, hx, hx1, hkx⟩, rfl⟩
      refine ⟨(MulAut.conj g).toMonoidHom x, ⟨x, hx, rfl⟩, fun h => hx1 ?_, ?_⟩
      · exact (map_eq_one_iff _ (MulAut.conj g).injective).1 h
      · exact hkx.map _
  suffices hE'top : Subgroup.closure (T E') = ⊤ by
    rw [eq_top_iff]
    intro y _
    have hy : (MulAut.conj g).toMonoidHom y ∈ Subgroup.closure (T E') := by
      rw [hE'top]
      exact Subgroup.mem_top _
    rw [hTE, ← MonoidHom.map_closure] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := (MulAut.conj g).injective hzy
    rw [← this]
    exact hz
  set H := Subgroup.closure (T E') with hH
  have ha1 : a ≠ 1 := fun h => by
    rw [h, orderOf_one] at hao
    exact hp.out.one_lt.ne hao
  have hb1 : b ≠ 1 := fun h => by
    rw [h, orderOf_one] at hbo
    exact hp.out.one_lt.ne hbo
  have hA1 : ψA a ≠ 1 := fun h => ha1 (hA (h.trans (map_one ψA).symm))
  have hB1 : ψB b ≠ 1 := fun h => hb1 (hB (h.trans (map_one ψB).symm))
  have haE : ψA a ∈ E' := by
    rw [hEg]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hbE : ψB b ∈ E' := by
    rw [hEg]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hXH : ψA.range ⊔ ψB.range ≤ H := by
    refine sup_le ?_ ?_
    · rintro _ ⟨y, rfl⟩
      exact Subgroup.subset_closure ⟨ψB b, hbE, hB1, hcomm y b⟩
    · rintro _ ⟨y, rfl⟩
      exact Subgroup.subset_closure ⟨ψA a, haE, hA1, (hcomm a y).symm⟩
  have hE'c : Nat.card E' = p ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj g).injective, hEc]
  have hE'p : ∀ x ∈ E', x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hEp y hy, map_one]
  obtain ⟨e, heE, hea, heb, P, hPC, hPs⟩ := hthird E' hE'c hE'p (ψA a) (ψB b) haE hbE hA1 hB1
  have he1 : e ≠ 1 := fun h => hea (h ▸ Subgroup.one_mem _)
  have hPH : P ≤ H := fun z hz =>
    Subgroup.subset_closure ⟨e, heE, he1,
      (commute_iff_eq _ _).2 (Subgroup.mem_centralizer_singleton_iff.1 (hPC hz))⟩
  have hzc : ∀ h ∈ Subgroup.zpowers (ψA a), ∀ k ∈ Subgroup.zpowers (ψB b), Commute h k := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ((hcomm a b).zpow_left i).zpow_right j
  have heE' := heE
  rw [hEg] at heE'
  obtain ⟨_, ⟨i, hi0⟩, _, ⟨j, hj0⟩, hce⟩ := exists_mul_of_mem_sup_of_commute hzc heE'
  simp only at hi0 hj0
  rw [← hi0, ← hj0] at hce
  have hi : orderOf (a ^ i) = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hao,
        pow_orderOf_eq_one, one_zpow]
    · intro h
      apply heb
      have : ψA a ^ i = 1 := by rw [← map_zpow, h, map_one]
      rw [hce, this, one_mul]
      exact Subgroup.mem_zpowers_iff.2 ⟨j, rfl⟩
  have hj : orderOf (b ^ j) = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hbo,
        pow_orderOf_eq_one, one_zpow]
    · intro h
      apply hea
      have : ψB b ^ j = 1 := by rw [← map_zpow, h, map_one]
      rw [hce, this, mul_one]
      exact Subgroup.mem_zpowers_iff.2 ⟨i, rfl⟩
  have heq : e = ψA (a ^ i) * ψB (b ^ j) := by rw [hce, map_zpow, map_zpow]
  have hnot : ¬ H ≤ Subgroup.normalizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G) := by
    intro hle
    have hPN : P ≤ Subgroup.normalizer ((ψA.range ⊔ ψB.range : Subgroup G) : Set G) :=
      hPH.trans hle
    have hsol : Group.IsSolvable ↥(P ⊓ (ψA.range ⊔ ψB.range)) := by
      apply Group.isSolvable_of_comm
      rintro ⟨z, hzP, hzX⟩ ⟨z', hz'P, hz'X⟩
      apply Subtype.ext
      have hwe : Commute z (ψA (a ^ i) * ψB (b ^ j)) := by
        rw [← heq]
        exact (commute_iff_eq _ _).2 (Subgroup.mem_centralizer_singleton_iff.1 (hPC hzP))
      have hw'e : Commute z' (ψA (a ^ i) * ψB (b ^ j)) := by
        rw [← heq]
        exact (commute_iff_eq _ _).2 (Subgroup.mem_centralizer_singleton_iff.1 (hPC hz'P))
      exact (commute_of_mem_centralizer_twoFrames ψA ψB hA hB hcomm hcycA hcycB hAB hi hj hzX hz'X
        hwe hw'e).eq
    exact hPs (hN P hPN hsol)
  exact hC H hXH hnot

end Main

section Transfer

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem closing_of_map {X : Subgroup (ModGL τ K)} {Y : Subgroup ↥(adjointGroup τ K)}
    (hY : Y.map (adjointGroup τ K).subtype = X) (hC : TwFrameClosing τ K X) :
    ∀ H : Subgroup ↥(adjointGroup τ K), Y ≤ H →
      ¬ H ≤ Subgroup.normalizer (Y : Set ↥(adjointGroup τ K)) → H = ⊤ := by
  intro H hYH hnot
  have hXH : X ≤ H.map (adjointGroup τ K).subtype := hY ▸ Subgroup.map_mono hYH
  have hn : ¬ H.map (adjointGroup τ K).subtype ≤ Subgroup.normalizer (X : Set (ModGL τ K)) := by
    intro hle
    apply hnot
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := (Subgroup.mem_normalizer_iff.1 (hle ⟨z, hz, rfl⟩)) (y : ModGL τ K)
    have hmem : ∀ u : ↥(adjointGroup τ K), u ∈ Y ↔ (u : ModGL τ K) ∈ X := fun u => by
      rw [← hY]
      exact ⟨fun hu => ⟨u, hu, rfl⟩, fun ⟨v, hv, hvu⟩ => by
        have : v = u := Subtype.ext hvu
        rwa [← this]⟩
    rw [hmem, hmem]
    exact h1
  have htop := hC _ (Subgroup.map_subtype_le _) hXH hn
  rw [eq_top_iff]
  intro y _
  have hy : (y : ModGL τ K) ∈ H.map (adjointGroup τ K).subtype := by
    rw [htop]
    exact y.2
  obtain ⟨y₀, hy₀, hy₀e⟩ := hy
  have : y₀ = y := Subtype.ext hy₀e
  rw [← this]
  exact hy₀

theorem normalizerSolvable_of_map {X : Subgroup (ModGL τ K)} {Y : Subgroup ↥(adjointGroup τ K)}
    (hY : Y.map (adjointGroup τ K).subtype = X) (hN : TwFrameNormalizerSolvable τ K X) :
    ∀ P : Subgroup ↥(adjointGroup τ K), P ≤ Subgroup.normalizer (Y : Set ↥(adjointGroup τ K)) →
      Group.IsSolvable ↥(P ⊓ Y) → Group.IsSolvable ↥P := by
  intro P hPN hsol
  have hinj : Function.Injective (adjointGroup τ K).subtype := (adjointGroup τ K).subtype_injective
  have hPN' : P.map (adjointGroup τ K).subtype ≤ Subgroup.normalizer (X : Set (ModGL τ K)) := by
    calc P.map (adjointGroup τ K).subtype
        ≤ (Subgroup.normalizer (Y : Set ↥(adjointGroup τ K))).map (adjointGroup τ K).subtype :=
          Subgroup.map_mono hPN
      _ ≤ Subgroup.normalizer ((Y.map (adjointGroup τ K).subtype : Subgroup (ModGL τ K)) :
          Set (ModGL τ K)) := Subgroup.le_normalizer_map _
      _ = Subgroup.normalizer (X : Set (ModGL τ K)) := by rw [hY]
  have hsol' : Group.IsSolvable ↥(P.map (adjointGroup τ K).subtype ⊓ X) := by
    have hmap : P.map (adjointGroup τ K).subtype ⊓ X = (P ⊓ Y).map (adjointGroup τ K).subtype := by
      rw [Subgroup.map_inf _ _ _ hinj, hY]
    rw [hmap]
    let e1 := Subgroup.equivMapOfInjective (P ⊓ Y) (adjointGroup τ K).subtype hinj
    exact Group.isSolvable_of_surjective (f := e1.toMonoidHom) e1.surjective
  have hPsol := hN _ (Subgroup.map_subtype_le _) hPN' hsol'
  let e2 := Subgroup.equivMapOfInjective P (adjointGroup τ K).subtype hinj
  exact Group.isSolvable_of_surjective (f := e2.symm.toMonoidHom) e2.symm.surjective

theorem closure_centralizers_eq_top_of_subgroups {X₁ X₂ : Subgroup (ModGL τ K)}
    (h₁ : X₁ ≤ adjointGroup τ K) (h₂ : X₂ ≤ adjointGroup τ K)
    (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x)
    (hC : TwFrameClosing τ K (X₁ ⊔ X₂)) (hN : TwFrameNormalizerSolvable τ K (X₁ ⊔ X₂))
    {p : ℕ} [Fact p.Prime] (hD : TwFramePlaneData τ K X₁ X₂ p) (hthird : TwThirdLine τ K p)
    (E : Subgroup ↥(adjointGroup τ K)) (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    Subgroup.closure {k : ↥(adjointGroup τ K) | ∃ x ∈ E, x ≠ 1 ∧ Commute k x} = ⊤ := by
  have : Finite (ModGL τ K) := CFSG.LieType.Chevalley.finite_modGL
  have hinj : Function.Injective (adjointGroup τ K).subtype :=
    (adjointGroup τ K).subtype_injective
  have hY : ((Subgroup.inclusion h₁).range ⊔ (Subgroup.inclusion h₂).range).map
      (adjointGroup τ K).subtype = X₁ ⊔ X₂ := by
    rw [Subgroup.map_sup, Subgroup.inclusion_range, Subgroup.inclusion_range,
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 h₁,
      inf_eq_left.2 h₂]
  have hAB : ¬ p ∣ Nat.card ↥((Subgroup.inclusion h₁).range ⊓ (Subgroup.inclusion h₂).range) := by
    have hmap : ((Subgroup.inclusion h₁).range ⊓ (Subgroup.inclusion h₂).range).map
        (adjointGroup τ K).subtype = X₁ ⊓ X₂ := by
      rw [Subgroup.map_inf _ _ _ hinj, Subgroup.inclusion_range, Subgroup.inclusion_range,
        Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 h₁,
        inf_eq_left.2 h₂]
    rw [← Subgroup.card_map_of_injective hinj, hmap]
    exact hD.inter
  exact closure_centralizers_eq_top_of_twoFrames (Subgroup.inclusion h₁) (Subgroup.inclusion h₂)
    (Subgroup.inclusion_injective h₁) (Subgroup.inclusion_injective h₂)
    (fun x y => Subtype.ext (hcomm _ x.2 _ y.2)) (closing_of_map hY hC)
    (normalizerSolvable_of_map hY hN) hD.cyclic₁ hD.cyclic₂ hAB hD.card hthird E hEp hEc

end Transfer

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
