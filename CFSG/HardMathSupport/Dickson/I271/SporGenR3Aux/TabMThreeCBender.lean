module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveEmb
public import CFSG.LargeExtraspecial.AS35EBender

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeC

open Subgroup CFSG.Open CFSG.LargeExtraspecial.Asc77 CFSG.HardMathSupport.Dickson.I271.TabMFive

section NoOdd

@[expose] def NoOddSections (F : Type*) [Group F] : Prop :=
  (∀ K : Subgroup F, K.Normal → Odd (Nat.card K) → K = ⊥) ∧
    (∀ K : Subgroup F, K.Normal → Odd K.index → K = ⊤) ∧ ¬ Group.IsSolvable F

theorem NoOddSections.of_equiv {F F' : Type*} [Group F] [Group F'] (e : F ≃* F')
    (h : NoOddSections F) : NoOddSections F' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun K hK hodd => ?_, fun K hK hodd => ?_, fun hs => h3 ?_⟩
  · have hK1 : (K.map e.symm.toMonoidHom).Normal := hK.map _ e.symm.surjective
    have hcard : Nat.card (K.map e.symm.toMonoidHom) = Nat.card K :=
      Subgroup.card_map_of_injective e.symm.injective
    have h0 := h1 _ hK1 (hcard ▸ hodd)
    refine (Subgroup.eq_bot_iff_forall K).2 fun x hx => ?_
    have hx' : e.symm x ∈ K.map e.symm.toMonoidHom := ⟨x, hx, rfl⟩
    rw [h0, Subgroup.mem_bot] at hx'
    simpa using hx'
  · have hK1 : (K.comap e.toMonoidHom).Normal := hK.comap _
    have hidx : (K.comap e.toMonoidHom).index = K.index :=
      Subgroup.index_comap_of_surjective K (f := e.toMonoidHom) e.surjective
    have h0 := h2 _ hK1 (hidx ▸ hodd)
    refine (Subgroup.eq_top_iff' K).2 fun y => ?_
    have hy : e.symm y ∈ K.comap e.toMonoidHom := by
      rw [h0]
      exact Subgroup.mem_top _
    simpa using hy
  · haveI := hs
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem eq_one_of_pow_two_of_odd {A : Type*} [Group A] {x : A} {n m : ℕ} (hx : x ^ (2 ^ n) = 1)
    (hm : Odd m) (hxm : orderOf x ∣ m) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hx
  have h2 : Nat.Coprime (orderOf x) (2 ^ n) :=
    Nat.Coprime.coprime_dvd_left hxm (hm.coprime_two_right.pow_right n)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h2 h1)

theorem not_isSolvable_alternatingGroup_nine : ¬ Group.IsSolvable (alternatingGroup (Fin 9)) := by
  intro h
  haveI : IsSimpleGroup (alternatingGroup (Fin 9)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hc := IsSimpleGroup.comm_iff_isSolvable.2 h
  have hx : (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 9) :=
    Equiv.Perm.mem_alternatingGroup.2 (by decide)
  have hy : (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 2 3) ∈ alternatingGroup (Fin 9) :=
    Equiv.Perm.mem_alternatingGroup.2 (by decide)
  have h2 := congrArg Subtype.val (hc ⟨_, hx⟩ ⟨_, hy⟩)
  have h3 : (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 1 2) *
        (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 2 3) ≠
      (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 2 3) *
        (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 1 2) := by decide
  exact h3 h2

theorem noOddSections_of_alternating {F : Type*} [Group F] [Finite F] {Q : Subgroup F}
    (hQn : Q.Normal) (hQ : IsPGroup 2 Q) (hc : centralizer (Q : Set F) ≤ Q)
    (e : F ⧸ Q ≃* alternatingGroup (Fin 9)) : NoOddSections F := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 9)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup (F ⧸ Q) := MulEquiv.isSimpleGroup e
  have hcardA : Nat.card (F ⧸ Q) = 181440 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.card_eq_fintype_card, Nat.factorial]
  refine ⟨?_, ?_, ?_⟩
  · intro K hK hodd
    have hKQ : ∀ x, x ∈ K → x ∈ Q → x = 1 := by
      intro x hxK hxQ
      obtain ⟨n, hn⟩ := hQ ⟨x, hxQ⟩
      have hn' : x ^ (2 ^ n) = 1 := congrArg Subtype.val hn
      exact eq_one_of_pow_two_of_odd hn' hodd (Subgroup.orderOf_dvd_natCard K hxK)
    refine (Subgroup.eq_bot_iff_forall K).2 fun x hx => ?_
    have hxc : x ∈ centralizer (Q : Set F) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have h1 : q * x * q⁻¹ * x⁻¹ ∈ K := K.mul_mem (hK.conj_mem x hx q) (K.inv_mem hx)
      have h2 : q * (x * q⁻¹ * x⁻¹) ∈ Q := Q.mul_mem hq (hQn.conj_mem q⁻¹ (Q.inv_mem hq) x)
      have h3 : q * x * q⁻¹ * x⁻¹ = q * (x * q⁻¹ * x⁻¹) := by group
      have h4 := hKQ _ h1 (h3 ▸ h2)
      rw [mul_inv_eq_one] at h4
      exact mul_inv_eq_iff_eq_mul.1 h4
    exact hKQ x hx (hc hxc)
  · intro K hK hidx
    have hidx' : Odd (Nat.card (F ⧸ K)) := by rwa [← Subgroup.index_eq_card]
    have hQK : Q ≤ K := by
      intro x hx
      obtain ⟨n, hn⟩ := hQ ⟨x, hx⟩
      have hn' : x ^ (2 ^ n) = 1 := congrArg Subtype.val hn
      have h1 : ((x : F ⧸ K)) ^ (2 ^ n) = 1 := by
        rw [← QuotientGroup.mk_pow, hn']
        rfl
      have h2 : orderOf (x : F ⧸ K) ∣ Nat.card (F ⧸ K) := orderOf_dvd_natCard _
      exact (QuotientGroup.eq_one_iff x).1 (eq_one_of_pow_two_of_odd h1 hidx' h2)
    have hKn : (K.map (QuotientGroup.mk' Q)).Normal := hK.map _ (QuotientGroup.mk'_surjective Q)
    rcases hKn.eq_bot_or_eq_top with h | h
    · exfalso
      have hKQ : K ≤ Q := by
        intro x hx
        have hx' : (QuotientGroup.mk' Q) x ∈ K.map (QuotientGroup.mk' Q) := ⟨x, hx, rfl⟩
        rw [h, Subgroup.mem_bot] at hx'
        exact (QuotientGroup.eq_one_iff x).1 hx'
      have hKeq : K = Q := le_antisymm hKQ hQK
      have h2 : K.index = 181440 := by rw [hKeq, Subgroup.index_eq_card, hcardA]
      rw [h2] at hidx
      exact absurd (Nat.odd_iff.1 hidx) (by norm_num)
    · refine (Subgroup.eq_top_iff' K).2 fun f => ?_
      have hf : (QuotientGroup.mk' Q) f ∈ K.map (QuotientGroup.mk' Q) := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨x, hx, hxf⟩ := hf
      have hq : x⁻¹ * f ∈ Q := QuotientGroup.eq.1 hxf
      have e1 : f = x * (x⁻¹ * f) := by group
      rw [e1]
      exact K.mul_mem hx (hQK hq)
  · intro hs
    haveI := hs
    haveI : Group.IsSolvable (F ⧸ Q) :=
      Group.isSolvable_of_surjective (f := QuotientGroup.mk' Q) (QuotientGroup.mk'_surjective Q)
    exact not_isSolvable_alternatingGroup_nine
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

end NoOdd

section Bender

theorem false_of_sylow_cyclic_or_quaternion {X : Type} [Group X] [Finite X] {a b : X}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a * b = b * a)
    (hne : a ≠ b)
    (hS : ∀ S : Sylow 2 X, IsCyclic (S : Subgroup X) ∨
      ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2)))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set s : Set X := {a, b} with hsdef
  have hss : s ⊆ centralizer s := by
    intro u hu
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro v hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · rfl
    · exact hab.symm
    · exact hab
    · rfl
  have hEc : ∀ u ∈ closure s, ∀ v ∈ closure s, u * v = v * u := by
    intro u hu v hv
    have hu' := Subgroup.closure_le_centralizer_centralizer s hu
    have hv' : v ∈ centralizer s := (closure_le _).mpr hss hv
    exact (mem_centralizer_iff.mp hu' v hv').symm
  have hE2 : ∀ u ∈ closure s, u ^ 2 = 1 := by
    intro u hu
    induction hu using closure_induction with
    | mem u hu =>
      rcases hu with rfl | rfl
      · exact ha
      · exact hb
    | one => exact one_pow 2
    | mul u v hu hv ihu ihv =>
      rw [pow_two, show u * v * (u * v) = u * (v * u) * v by group, ← hEc u hu v hv,
        show u * (u * v) * v = (u * u) * (v * v) by group, ← pow_two, ← pow_two, ihu, ihv,
        one_mul]
    | inv u _ ih => rw [inv_pow, ih, inv_one]
  have hEp : IsPGroup 2 (closure s) := fun e =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (hE2 e e.2)⟩
  obtain ⟨S, hES⟩ := hEp.exists_le_sylow
  have haS : a ∈ (S : Subgroup X) := hES (subset_closure (Set.mem_insert a _))
  have hbS : b ∈ (S : Subgroup X) := hES (subset_closure (Set.mem_insert_of_mem a rfl))
  rcases hS S with hcyc | ⟨r, hr, ⟨e⟩⟩
  · have := eq_of_sq_eq_one_of_isCyclic (C := (S : Subgroup X)) (x := ⟨a, haS⟩)
      (y := ⟨b, hbS⟩) (Subtype.ext (by simpa using ha)) (Subtype.ext (by simpa using hb))
      (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
    exact hne (congrArg Subtype.val this)
  · have : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
    have := eq_of_sq_eq_one_quaternion (x := e ⟨a, haS⟩) (y := e ⟨b, hbS⟩)
      (by rw [← map_pow, show (⟨a, haS⟩ : (S : Subgroup X)) ^ 2 = 1 from
        Subtype.ext (by simpa using ha), map_one])
      (by rw [← map_pow, show (⟨b, hbS⟩ : (S : Subgroup X)) ^ 2 = 1 from
        Subtype.ext (by simpa using hb), map_one])
      (fun h => ha1 (congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h)))
      (fun h => hb1 (congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h)))
    exact hne (congrArg Subtype.val (e.injective this))

theorem false_of_stronglyEmbedded {X : Type} [Group X] [Finite X]
    {D : Subgroup X} (hD : fusionStronglyEmbedded D) {a b : X} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a * b = b * a) (hne : a ≠ b) {F : Subgroup X} {t : X}
    (htF : t ∈ F) (ht : orderOf t = 2) (hFt : F ≤ centralizer ({t} : Set X))
    (hF : NoOddSections ↥F) : False := by
  rcases CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_3 X D hD
    with hS | ⟨M, N, hMn, hNn, hMNn, hMN, hModd, hNodd, hB⟩
  · exact false_of_sylow_cyclic_or_quaternion ha hb ha1 hb1 hab hne hS
  · haveI := hMn
    haveI := hNn
    haveI := hMNn
    have hFN : F ≤ N := by
      have hnorm : (N.subgroupOf F).Normal := hNn.subgroupOf F
      have hodd : Odd (N.subgroupOf F).index :=
        Odd.of_dvd_nat hNodd (N.relIndex_dvd_index_of_normal F)
      exact Subgroup.subgroupOf_eq_top.1 (hF.2.1 _ hnorm hodd)
    have hMF : M.subgroupOf F = ⊥ := by
      have hnorm : (M.subgroupOf F).Normal := hMn.subgroupOf F
      refine hF.1 _ hnorm ?_
      let f : ↥(M.subgroupOf F) →* ↥M :=
        (F.subtype.comp (M.subgroupOf F).subtype).codRestrict M fun x => x.2
      have hf : Function.Injective f := by
        intro x y hxy
        have h1 : ((f x : ↥M) : X) = ((f y : ↥M) : X) := congrArg Subtype.val hxy
        exact Subtype.ext (Subtype.ext h1)
      exact Odd.of_dvd_nat hModd (Subgroup.card_dvd_of_injective f hf)
    let ψ : ↥F →* (↥N ⧸ M.subgroupOf N) :=
      (QuotientGroup.mk' (M.subgroupOf N)).comp (Subgroup.inclusion hFN)
    have hψ : Function.Injective ψ := by
      rw [injective_iff_map_eq_one]
      intro f hf
      have h1 : Subgroup.inclusion hFN f ∈ M.subgroupOf N := (QuotientGroup.eq_one_iff _).1 hf
      have h2 : f ∈ M.subgroupOf F := h1
      rw [hMF] at h2
      exact (Subgroup.mem_bot).1 h2
    let t' : ↥F := ⟨t, htF⟩
    have htb : orderOf (ψ t') = 2 := by
      rw [orderOf_injective ψ hψ t', Subgroup.orderOf_mk]
      exact ht
    have hcomm : ∀ f : ↥F, ψ f ∈ centralizer ({ψ t'} : Set (↥N ⧸ M.subgroupOf N)) := by
      intro f
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hFt f.2))
    let ψ' : ↥F →* centralizer ({ψ t'} : Set (↥N ⧸ M.subgroupOf N)) := ψ.codRestrict _ hcomm
    have hψ' : Function.Injective ψ' := fun x y h => hψ (congrArg Subtype.val h)
    have hsolv : Group.IsSolvable (centralizer ({ψ t'} : Set (↥N ⧸ M.subgroupOf N))) :=
      isSolvable_centralizer_of_fusionIsBenderGroup hB htb
    exact hF.2.2 (Group.isSolvable_of_isSolvable_injective hψ')

end Bender

section Recognition

theorem stronglyEmbedded_of_involutions {C : Type*} [Group C] [Finite C] {D : Subgroup C}
    (hD : D ≠ ⊤) (hcent : ∀ t ∈ D, orderOf t = 2 → Subgroup.centralizer ({t} : Set C) ≤ D)
    (hconj : ∀ t ∈ D, ∀ u ∈ D, orderOf t = 2 → orderOf u = 2 → ∃ k ∈ D, k * u * k⁻¹ = t)
    {t₀ : C} (ht₀ : t₀ ∈ D) (ho₀ : orderOf t₀ = 2) : fusionStronglyEmbedded D := by
  have hodd : ∀ g ∉ D, Odd (Nat.card (D ⊓ D.map (MulAut.conj g).toMonoidHom : Subgroup C)) := by
    intro g hg
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨u, hu, hu2⟩ := TabMSeven.exists_involution_mem_of_even hev
    obtain ⟨huD, huDg⟩ := Subgroup.mem_inf.1 hu
    have hd : g⁻¹ * u * g ∈ D := (TabMSeven.mem_map_conj_iff D g u).1 huDg
    have hd2 : orderOf (g⁻¹ * u * g) = 2 := by
      have := TabMSeven.orderOf_conj_eq g⁻¹ u
      rw [inv_inv] at this
      rw [this, hu2]
    obtain ⟨k, hk, hku⟩ := hconj _ hd u huD hd2 hu2
    have hgk : g * k ∈ Subgroup.centralizer ({u} : Set C) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * k * u = g * (k * u * k⁻¹) * k := by group
        _ = g * (g⁻¹ * u * g) * k := by rw [hku]
        _ = u * (g * k) := by group
    have h1 := D.mul_mem (hcent u huD hu2 hgk) (D.inv_mem hk)
    rw [mul_inv_cancel_right] at h1
    exact hg h1
  refine ⟨hD, ?_, fun g hg => hodd g⁻¹ fun h => hg (by simpa using D.inv_mem h)⟩
  have := Subgroup.orderOf_dvd_natCard D ht₀
  rw [ho₀] at this
  exact even_iff_two_dvd.2 this

variable {G : Type*} [Group G]

theorem card_prodSub_le [Finite G] {p : ℕ} {k : G} {H : Subgroup G}
    {hHk : H ≤ centralizer ({k} : Set G)} (hp : p.Prime) (hk : orderOf k = p) :
    Nat.card ↥(prodSub k H hHk) ≤ p * Nat.card ↥H := by
  let f : Fin p × ↥H → ↥(prodSub k H hHk) := fun x =>
    ⟨k ^ (x.1 : ℕ) * (x.2 : G), ⟨((x.1 : ℕ) : ℤ), x.2, x.2.2, by rw [zpow_natCast]⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨d, i, h, hh, rfl⟩
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
    have hk' : (orderOf k : ℤ) = p := by rw [hk]
    have hnn : 0 ≤ i % (p : ℤ) := Int.emod_nonneg _ hp0.ne'
    have hlt : (i % (p : ℤ)).toNat < p := by
      have := Int.emod_lt_of_pos i hp0
      omega
    have h1 : k ^ i = k ^ ((i % (p : ℤ)).toNat) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hnn, ← hk', zpow_mod_orderOf]
    refine ⟨(⟨(i % (p : ℤ)).toNat, hlt⟩, ⟨h, hh⟩), Subtype.ext ?_⟩
    show k ^ ((i % (p : ℤ)).toNat) * h = k ^ i * h
    rw [h1]
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin] at this

end Recognition

section Main

variable {G : Type} [Group G] [Finite G]

theorem centralizer_eq_prodSub {p : ℕ} {k : G} {H : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hk : orderOf k = p) {α : G} (hα : α * k * α⁻¹ = k⁻¹)
    (hHα : H ≤ centralizer ({α} : Set G)) (hHk : H ≤ centralizer ({k} : Set G))
    (hup : ∀ t ∈ H, orderOf t = 2 →
      Nat.card ↥(centralizer ({t} : Set G) ⊓ centralizer ({k} : Set G)) ≤
        p * Nat.card ↥(H ⊓ centralizer ({t} : Set G)))
    (hconj : ∀ t ∈ H, ∀ u ∈ H, orderOf t = 2 → orderOf u = 2 → ∃ g ∈ H, g * u * g⁻¹ = t)
    {a b : G} (ha : a ∈ H) (hb : b ∈ H) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2)
    (hab : a * b = b * a) (hne : a ≠ b) {t₀ : G} (ht₀ : t₀ ∈ H) (ho₀ : orderOf t₀ = 2)
    (hF : NoOddSections ↥(H ⊓ centralizer ({t₀} : Set G))) :
    centralizer ({k} : Set G) = prodSub k H hHk ∧
      Nat.card ↥(centralizer ({k} : Set G)) ≤ p * Nat.card ↥H := by
  set D := prodSub k H hHk with hD
  set X := centralizer ({k} : Set G) with hX
  have hkC : k ∈ X := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hDC : D ≤ X := prodSub_le hkC hHk
  have hHD : H ≤ D := le_prodSub
  have hkt : ∀ t ∈ H, k ∈ centralizer ({t} : Set G) ⊓ centralizer ({k} : Set G) := fun t ht =>
    ⟨Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_singleton_iff.1 (hHk ht)).symm, hkC⟩
  have hHt : ∀ t ∈ H, H ⊓ centralizer ({t} : Set G) ≤
      centralizer ({t} : Set G) ⊓ centralizer ({k} : Set G) := fun t _ x hx =>
    ⟨hx.2, hHk hx.1⟩
  have hsub : ∀ t ∈ H, orderOf t = 2 → X ⊓ centralizer ({t} : Set G) ≤ D := by
    intro t ht ho x hx
    have hx' : x ∈ centralizer ({t} : Set G) ⊓ centralizer ({k} : Set G) := ⟨hx.2, hx.1⟩
    obtain ⟨i, h, hh, rfl⟩ := eq_prod_of_card_le hp hp2 hk hα (H' := H ⊓ centralizer ({t} : Set G))
      (fun x hx => hHα hx.1) (hkt t ht) (hHt t ht) (hup t ht ho) x hx'
    exact ⟨(i : ℤ), h, hh.1, by rw [zpow_natCast]⟩
  have hDeq : D = X := by
    by_contra hne'
    have hD' : D.subgroupOf X ≠ ⊤ := by
      intro h
      exact hne' (le_antisymm hDC (Subgroup.subgroupOf_eq_top.1 h))
    have hinvH : ∀ t : ↥X, t ∈ D.subgroupOf X → orderOf t = 2 → (t : G) ∈ H := fun t ht ho =>
      mem_of_orderOf_two hp hp2 hk hα hHα (Subgroup.mem_subgroupOf.1 ht)
        ((Subgroup.orderOf_coe t).trans ho)
    have hSE : fusionStronglyEmbedded (D.subgroupOf X) := by
      refine stronglyEmbedded_of_involutions hD' ?_ ?_ (t₀ := ⟨t₀, hDC (hHD ht₀)⟩)
        (Subgroup.mem_subgroupOf.2 (hHD ht₀)) (by rw [← Subgroup.orderOf_coe]; exact ho₀)
      · intro t ht ho c hc
        have hc' : (c : G) ∈ X ⊓ centralizer ({(t : G)} : Set G) :=
          ⟨c.2, Subgroup.mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc))⟩
        exact Subgroup.mem_subgroupOf.2 (hsub (t : G) (hinvH t ht ho)
          ((Subgroup.orderOf_coe t).trans ho) hc')
      · intro t ht u hu hto huo
        obtain ⟨g, hg, hgu⟩ := hconj (t : G) (hinvH t ht hto) (u : G) (hinvH u hu huo)
          ((Subgroup.orderOf_coe t).trans hto) ((Subgroup.orderOf_coe u).trans huo)
        exact ⟨⟨g, hDC (hHD hg)⟩, Subgroup.mem_subgroupOf.2 (hHD hg), Subtype.ext hgu⟩
    have hleF : H ⊓ centralizer ({t₀} : Set G) ≤ X := fun x hx => hHk hx.1
    have hF' : NoOddSections ↥((H ⊓ centralizer ({t₀} : Set G)).subgroupOf X) :=
      hF.of_equiv (Subgroup.subgroupOfEquivOfLe hleF).symm
    let a' : ↥X := ⟨a, hHk ha⟩
    let b' : ↥X := ⟨b, hHk hb⟩
    let t' : ↥X := ⟨t₀, hHk ht₀⟩
    have ha' : orderOf a' = 2 := by rw [← Subgroup.orderOf_coe]; exact ha2
    have hb' : orderOf b' = 2 := by rw [← Subgroup.orderOf_coe]; exact hb2
    have ht' : orderOf t' = 2 := by rw [← Subgroup.orderOf_coe]; exact ho₀
    refine false_of_stronglyEmbedded hSE (a := a') (b := b')
      (by rw [← ha']; exact pow_orderOf_eq_one _) (by rw [← hb']; exact pow_orderOf_eq_one _)
      (fun h => by rw [h, orderOf_one] at ha'; omega)
      (fun h => by rw [h, orderOf_one] at hb'; omega)
      (Subtype.ext hab) (fun h => hne (congrArg Subtype.val h))
      (F := (H ⊓ centralizer ({t₀} : Set G)).subgroupOf X) (t := t')
      (Subgroup.mem_subgroupOf.2 ⟨ht₀, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩) ht' ?_ hF'
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.2
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 hy).2))
  refine ⟨hDeq.symm, ?_⟩
  rw [← hDeq]
  exact card_prodSub_le hp hk

end Main

end CFSG.HardMathSupport.Dickson.I271.TabMThreeC
