module

public import CFSG.LocalAnalysis.GH72.DDStructure
public import CFSG.CGT.Foote81L6.TStruct.Classes
public import CFSG.CGT.Foote81L6.TStruct.DihProd

public section

namespace CFSG.GH72

open Subgroup DihedralGroup
open CFSG.CGT.Foote81L6 (zc zc_mul_self zc_ne_one zc_comm mem_sup_iff_of_le_normalizer
  le_normalizer_of_comm card_sup_of_le_normalizer)
open CFSG.CGT.Foote81L6.TStruct (IsFourIn ElemBound isElemAbelian_two_iff comm_of_mul_self
  eq_one_or_eq_of_mem_zpowers card_zpowers_sup_zpowers mul_self_of_mem_zpowers_sup_zpowers
  liftSub lowerSub mem_liftSub coe_mem_liftSub symm_mem_liftSub liftSub_le card_liftSub
  isFourIn_liftSub_dihFour mem_dihFour mem_dihFour_of_comm sr_mem_dihFour zc_mem_dihFour
  r_eq_of_mul_self inf_centralizer_four card_inf_normalizer_four nonempty_inf_normalizer_four_equiv
  exists_involution_four exists_conj_four_iff exists_conj_four_rep fourClass fourClass_liftSub
  exists_dihedral_of_four mem_map_conj map_conj_eq_self_of_mem_normalizer
  mem_normalizer_of_map_conj_eq map_conj_inf map_conj_eq_of_agree map_conj_eq_self_of_comm
  inf_map_conj card_map_conj isFourIn_map_conj)

variable {G : Type*} [Group G]

namespace IsDih

variable {D : Subgroup G}

theorem isKleinFour_or_isDihNonab (hD : IsDih D) : IsKleinFour D ∨ IsDihNonab D := by
  obtain ⟨a, ha, ⟨e⟩⟩ := hD
  rcases Nat.lt_or_ge a 2 with h | h
  · obtain rfl : a = 1 := by omega
    refine Or.inl ⟨by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]; norm_num, ?_⟩
    rw [Monoid.exponent_eq_of_mulEquiv e, DihedralGroup.exponent]
    norm_num
  · exact Or.inr ⟨a, h, ⟨e⟩⟩

theorem isPGroup (hD : IsDih D) : IsPGroup 2 D := by
  obtain ⟨a, -, ⟨e⟩⟩ := hD
  exact IsPGroup.of_card (n := a + 1) (by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm])

theorem four_eq_of_isKleinFour (hD : IsKleinFour D) {V : Subgroup G} (hV : IsFourIn D V) :
    V = D := by
  haveI : Finite D := Nat.finite_of_card_ne_zero (by rw [IsKleinFour.card_four]; norm_num)
  exact eq_of_le_of_card_ge hV.1 (by rw [IsKleinFour.card_four, hV.2.2])

theorem isFourIn_self_of_isKleinFour (hD : IsKleinFour D) : IsFourIn D D :=
  ⟨le_rfl, fun x hx => congrArg Subtype.val (IsKleinFour.mul_self (⟨x, hx⟩ : D)),
    IsKleinFour.card_four⟩

theorem inf_centralizer_four (hD : IsDih D) {V : Subgroup G} (hV : IsFourIn D V) :
    D ⊓ centralizer (V : Set G) = V := by
  obtain ⟨a, ha, ⟨e⟩⟩ := hD
  exact CFSG.CGT.Foote81L6.TStruct.inf_centralizer_four e ha hV

theorem of_le (hD : IsDih D) {K V : Subgroup G} (hKD : K ≤ D) (hV : IsFourIn D V)
    (hVK : V ≤ K) : IsDih K := by
  obtain ⟨a, -, ⟨e⟩⟩ := hD
  exact exists_dihedral_of_four e hKD hV hVK

theorem isCyclic_of_le (hD : IsDih D) {K : Subgroup G} (hKD : K ≤ D)
    (hK : ∀ V, IsFourIn D V → ¬ V ≤ K) : IsCyclic K := by
  obtain ⟨a, ha, ⟨e⟩⟩ := hD
  let φ : K ≃* lowerSub e K := (subgroupOfEquivOfLe hKD).symm.trans
    ((K.subgroupOf D).equivMapOfInjective e.toMonoidHom e.injective)
  rcases CFSG.GorensteinWalter.subgroups_dihedral_twoGroup_cyclic_or_dihedral ha (lowerSub e K)
    with hc | ⟨j, hj, ⟨ψ⟩⟩
  · exact isCyclic_of_surjective φ.symm φ.symm.surjective
  · have hK' : IsDih K := ⟨j, hj, ⟨φ.trans ψ⟩⟩
    obtain ⟨V, hV⟩ := hK'.exists_four
    exact absurd hV.1 (hK V ⟨hV.1.trans hKD, hV.2⟩)

theorem exists_unique_involution (hD : IsDih D) {K : Subgroup G} (hKD : K ≤ D) (hK1 : K ≠ ⊥)
    (hK : ∀ V, IsFourIn D V → ¬ V ≤ K) :
    ∃ z ∈ K, orderOf z = 2 ∧ ∀ t ∈ K, orderOf t = 2 → t = z := by
  haveI := hD.finite
  haveI : Finite K := Finite.of_injective _ (inclusion_injective hKD)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic K := hD.isCyclic_of_le hKD hK
  have h2 : 2 ∣ Nat.card K := by
    rcases (hD.isPGroup.to_le hKD).card_eq_or_dvd with h | h
    · exact absurd ((Subgroup.card_eq_one).1 h) hK1
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine ⟨z, z.2, by rw [Subgroup.orderOf_coe, hz], fun t ht hto => ?_⟩
  by_contra hne
  have hzo : orderOf (z : G) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have hz2 : (z : G) * z = 1 := by rw [← pow_two, ← hzo]; exact pow_orderOf_eq_one _
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto]; exact pow_orderOf_eq_one t
  have hz1 : (z : G) ≠ 1 := by
    intro h
    rw [← Subgroup.orderOf_coe, h, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hto
    exact absurd hto (by norm_num)
  have hc : t * z = z * t := by
    letI := IsCyclic.commGroup (α := K)
    exact congrArg Subtype.val (mul_comm (⟨t, ht⟩ : K) z)
  have hle : zpowers t ⊔ zpowers (z : G) ≤ K :=
    sup_le (zpowers_le.2 ht) (zpowers_le.2 z.2)
  exact hK _ ⟨hle.trans hKD, fun g hg => mul_self_of_mem_zpowers_sup_zpowers ht2 hz2 hc hg,
    card_zpowers_sup_zpowers ht2 hz2 ht1 hz1 hne hc⟩ hle

theorem isFourIn_inf_centralizer (hD : IsDih D) {t : G} (htD : t ∈ D) (ht2 : t * t = 1)
    (hnc : ∃ y ∈ D, y * t ≠ t * y) : IsFourIn D (D ⊓ C t) := by
  obtain ⟨a, ha, ⟨e⟩⟩ := hD
  have hu2 : e ⟨t, htD⟩ * e ⟨t, htD⟩ = 1 := by
    rw [← map_mul, ← map_one e]
    exact congrArg e (Subtype.ext ht2)
  cases h : e ⟨t, htD⟩ with
  | r j =>
    exfalso
    obtain ⟨y, hyD, hy⟩ := hnc
    apply hy
    have hc : e ⟨y, hyD⟩ * r j = r j * e ⟨y, hyD⟩ := by
      rw [h] at hu2
      rcases r_eq_of_mul_self ha hu2 with h1 | h1
      · rw [h1, mul_one, one_mul]
      · rw [h1]
        exact zc_comm ha _
    have := congrArg e.symm hc
    rw [← h, ← map_mul, ← map_mul, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at this
    exact congrArg Subtype.val this
  | sr i =>
    have hV := isFourIn_liftSub_dihFour e ha i
    have heq : D ⊓ C t = liftSub e (CFSG.CGT.Foote81L6.TStruct.dihFour a i) := by
      ext x
      rw [mem_inf, mem_centralizer_singleton_iff, mem_liftSub]
      constructor
      · rintro ⟨hxD, hxt⟩
        refine ⟨hxD, mem_dihFour_of_comm ha ?_⟩
        rw [← h, ← map_mul, ← map_mul]
        exact congrArg e (Subtype.ext hxt)
      · rintro ⟨hxD, hx⟩
        refine ⟨hxD, ?_⟩
        have hc : e ⟨x, hxD⟩ * sr i = sr i * e ⟨x, hxD⟩ :=
          comm_of_mul_self (CFSG.CGT.Foote81L6.TStruct.mul_self_of_mem_dihFour ha i) hx
            (sr_mem_dihFour i)
        rw [← h, ← map_mul, ← map_mul] at hc
        exact congrArg Subtype.val (e.injective hc)
    rw [heq]
    exact hV

theorem map {G' : Type*} [Group G'] (hD : IsDih D) (f : G →* G') (hf : Function.Injective f) :
    IsDih (D.map f) := by
  obtain ⟨a, ha, ⟨e⟩⟩ := hD
  exact ⟨a, ha, ⟨(D.equivMapOfInjective f hf).symm.trans e⟩⟩

end IsDih

theorem isFourIn_map {G' : Type*} [Group G'] {D V : Subgroup G} (hV : IsFourIn D V)
    (f : G →* G') (hf : Function.Injective f) : IsFourIn (D.map f) (V.map f) :=
  ⟨map_mono hV.1, by rintro _ ⟨v, hv, rfl⟩; rw [← map_mul, hV.2.1 v hv, map_one],
    by rw [card_map_of_injective hf, hV.2.2]⟩

theorem IsE16.map {G' : Type*} [Group G'] {E : Subgroup G} (hE : IsE16 E) (f : G →* G')
    (hf : Function.Injective f) : IsE16 (E.map f) := by
  have hE2 := isElemAbelian_two_iff.1 hE.1
  refine ⟨isElemAbelian_two_iff.2 ?_, by rw [card_map_of_injective hf, hE.2]⟩
  rintro _ ⟨v, hv, rfl⟩
  rw [← map_mul, hE2 v hv, map_one]

namespace IsDihNonab

variable {D : Subgroup G}

theorem card_inf_normalizer_four (hD : IsDihNonab D) {V : Subgroup G} (hV : IsFourIn D V) :
    Nat.card ↥(D ⊓ normalizer (V : Set G)) = 8 := by
  obtain ⟨a, ha, ⟨e⟩⟩ := hD
  exact CFSG.CGT.Foote81L6.TStruct.card_inf_normalizer_four e ha hV

theorem exists_inf_normalizer_four_eq (hD : IsDihNonab D) {V : Subgroup G}
    (hV : IsFourIn D V) :
    ∃ f ∈ D, f * f = 1 ∧ f ∉ V ∧ D ⊓ normalizer (V : Set G) = V ⊔ zpowers f := by
  obtain ⟨a, ha, ⟨e⟩⟩ := hD
  obtain ⟨f, ⟨hfD, hfN⟩, hfV, hf2⟩ := exists_involution_four e ha hV
  refine ⟨f, hfD, hf2, hfV, ?_⟩
  have hle : V ⊔ zpowers f ≤ D ⊓ normalizer (V : Set G) :=
    sup_le (le_inf hV.1 (le_normalizer)) (le_inf (zpowers_le.2 hfD) (zpowers_le.2 hfN))
  haveI : Finite D := (isDih_of_isDihNonab ⟨a, ha, ⟨e⟩⟩).finite
  haveI : Finite ↥(D ⊓ normalizer (V : Set G)) :=
    Finite.of_injective _ (inclusion_injective (inf_le_left : D ⊓ normalizer (V : Set G) ≤ D))
  have hf1 : f ≠ 1 := fun h => hfV (h ▸ one_mem V)
  have hinf : V ⊓ zpowers f = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgV, hgf⟩
    rcases eq_one_or_eq_of_mem_zpowers hf2 hgf with rfl | rfl
    · exact one_mem _
    · exact absurd hgV hfV
  have hcard : Nat.card ↥(V ⊔ zpowers f) = 8 := by
    rw [card_sup_of_le_normalizer (zpowers_le.2 hfN) hinf, hV.2.2, Nat.card_zpowers,
      orderOf_eq_prime (by rw [pow_two]; exact hf2) hf1]
  exact (eq_of_le_of_card_ge hle (by
    rw [hcard, CFSG.CGT.Foote81L6.TStruct.card_inf_normalizer_four e ha hV])).symm

theorem exists_four_classes (hD : IsDihNonab D) :
    ∃ V₀ V₁ : Subgroup G, IsFourIn D V₀ ∧ IsFourIn D V₁ ∧
      (∀ d ∈ D, V₀.map (MulAut.conj d).toMonoidHom ≠ V₁) ∧
      ∀ V, IsFourIn D V → (∃ d ∈ D, V.map (MulAut.conj d).toMonoidHom = V₀) ∨
        (∃ d ∈ D, V.map (MulAut.conj d).toMonoidHom = V₁) := by
  obtain ⟨k, hk2, ⟨e⟩⟩ := hD
  have hk : 1 ≤ k := by omega
  have h₀ := isFourIn_liftSub_dihFour e hk 0
  have h₁ := isFourIn_liftSub_dihFour e hk 1
  refine ⟨_, _, h₀, h₁, fun d hd hconj => ?_, fun V hV => ?_⟩
  · have := (exists_conj_four_iff e hk hk2 h₀ h₁).1 ⟨d, hd, hconj⟩
    rw [fourClass_liftSub e hk hk2, fourClass_liftSub e hk hk2, map_zero, map_one] at this
    exact zero_ne_one this
  · obtain ⟨d, hd, hdV⟩ := exists_conj_four_rep e hk hk2 hV
    by_cases h0 : fourClass e hk V = 0
    · rw [if_pos h0] at hdV
      exact Or.inl ⟨d, hd, hdV⟩
    · rw [if_neg h0] at hdV
      exact Or.inr ⟨d, hd, hdV⟩

theorem exists_cyclic_index_two (hD : IsDihNonab D) :
    ∃ R : Subgroup G, R ≤ D ∧ IsCyclic R ∧ R.relIndex D = 2 ∧ (∀ t ∈ D, t ∉ R → t * t = 1) ∧
      ∀ t ∈ R, t * t = 1 → ∀ y ∈ D, y * t = t * y := by
  obtain ⟨k, hk2, ⟨e⟩⟩ := hD
  have hk : 1 ≤ k := by omega
  haveI : NeZero (2 ^ k) := ⟨by positivity⟩
  set R := liftSub e (zpowers (r 1 : DihedralGroup (2 ^ k))) with hR
  have hRD : R ≤ D := liftSub_le e _
  have hrot : ∀ x : D, (x : G) ∈ R ↔ ∃ j, e x = r j := by
    intro x
    rw [coe_mem_liftSub]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hx
      exact ⟨_, by rw [← hn, r_one_zpow]⟩
    · rintro ⟨j, hj⟩
      rw [hj]
      exact mem_zpowers_iff.2 ⟨(j.cast : ℤ), by rw [r_one_zpow, ZMod.intCast_zmod_cast]⟩
  refine ⟨R, hRD, ?_, ?_, ?_, ?_⟩
  · rw [hR, liftSub, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    infer_instance
  · have hcardD : Nat.card D = 2 * 2 ^ k := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hcardR : Nat.card R = 2 ^ k := by
      rw [hR, card_liftSub, Nat.card_zpowers, orderOf_r_one]
    have h := relIndex_mul_card R D
    rw [inf_of_le_left hRD, hcardR, hcardD] at h
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h
  · intro t htD htR
    have hnot : ∀ j, e ⟨t, htD⟩ ≠ r j := fun j hj => htR ((hrot ⟨t, htD⟩).2 ⟨j, hj⟩)
    cases h : e ⟨t, htD⟩ with
    | r j => exact absurd h (hnot j)
    | sr i =>
      have := congrArg (fun u => ((e.symm u : D) : G)) (sr_mul_self i)
      simp only [map_mul, map_one, MulEquiv.symm_apply_apply, ← h, coe_mul, OneMemClass.coe_one]
        at this
      exact this
  · intro t htR ht2 y hyD
    obtain ⟨j, hj⟩ := (hrot ⟨t, hRD htR⟩).1 htR
    have hu2 : r j * r j = (1 : DihedralGroup (2 ^ k)) := by
      rw [← hj, ← map_mul, ← map_one e]
      exact congrArg e (Subtype.ext ht2)
    have hc : e ⟨y, hyD⟩ * r j = r j * e ⟨y, hyD⟩ := by
      rcases r_eq_of_mul_self hk hu2 with h1 | h1
      · rw [h1, mul_one, one_mul]
      · rw [h1]
        exact zc_comm hk _
    have := congrArg e.symm hc
    rw [← hj, ← map_mul, ← map_mul, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at this
    exact congrArg Subtype.val this

theorem exists_inf_centralizer_self_eq (hD : IsDihNonab D) :
    ∃ z ∈ D, orderOf z = 2 ∧ D ⊓ centralizer (D : Set G) = zpowers z := by
  obtain ⟨k, hk2, ⟨e⟩⟩ := hD
  have hk : 1 ≤ k := by omega
  refine ⟨(e.symm (zc k) : G), (e.symm (zc k)).2, ?_, le_antisymm ?_ ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [pow_two]; exact zc_mul_self hk) (zc_ne_one hk)
  · intro x hx
    obtain ⟨hxD, hxc⟩ := mem_inf.1 hx
    have hc : ∀ g : DihedralGroup (2 ^ k), g * e ⟨x, hxD⟩ = e ⟨x, hxD⟩ * g := by
      intro g
      obtain ⟨y, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (mem_centralizer_iff.1 hxc y y.2))
    rcases CFSG.CGT.Foote81L6.eq_one_or_zc_of_comm hk2 hc with h | h
    · have : (⟨x, hxD⟩ : D) = 1 := e.injective (h.trans e.map_one.symm)
      rw [show x = 1 from congrArg Subtype.val this]
      exact one_mem _
    · have : (⟨x, hxD⟩ : D) = e.symm (zc k) := by rw [← h, MulEquiv.symm_apply_apply]
      rw [show x = (e.symm (zc k) : G) from congrArg Subtype.val this]
      exact mem_zpowers _
  · rw [zpowers_le]
    refine ⟨(e.symm (zc k)).2, mem_centralizer_iff.2 fun y hy => ?_⟩
    have h := congrArg e.symm (zc_comm hk (e ⟨y, hy⟩))
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h
    exact congrArg Subtype.val h

theorem map {G' : Type*} [Group G'] (hD : IsDihNonab D) (f : G →* G')
    (hf : Function.Injective f) : IsDihNonab (D.map f) := by
  obtain ⟨a, ha, ⟨e⟩⟩ := hD
  exact ⟨a, ha, ⟨(D.equivMapOfInjective f hf).symm.trans e⟩⟩

end IsDihNonab

namespace DDDecomp

variable {S S₁ S₂ : Subgroup G} (hd : DDDecomp S S₁ S₂)
include hd

theorem exists_mulEquiv : ∃ μ : ↥S₁ × ↥S₂ ≃* ↥S, ∀ p : ↥S₁ × ↥S₂, (μ p : G) = p.1 * p.2 := by
  have hcomm : ∀ (x : S₁) (y : S₂), Commute (S₁.subtype x) (S₂.subtype y) :=
    fun x y => hd.comm x.2 y.2
  set f := S₁.subtype.noncommCoprod S₂.subtype hcomm
  have hf : Function.Injective f := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨S₁.subtype_injective, S₂.subtype_injective, ?_⟩
    rw [range_subtype, range_subtype, disjoint_iff]
    exact hd.inf_eq
  have hrange : f.range = S := by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype, hd.sup_eq]
  exact ⟨(MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange), fun p => rfl⟩

theorem sup_inf_left {V₁ V₂ : Subgroup G} (h₁ : V₁ ≤ S₁) (h₂ : V₂ ≤ S₂) :
    (V₁ ⊔ V₂) ⊓ S₁ = V₁ := by
  refine le_antisymm (fun g ⟨hg, hg₁⟩ => ?_) (le_inf le_sup_left h₁)
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_iff_of_le_normalizer
    (le_normalizer_of_comm fun x hx y hy => hd.comm (h₁ hx) (h₂ hy))).1 hg
  have hy1 : y = 1 := (hd.eq_and_eq (h₁ hx) hg₁ (h₂ hy) (one_mem _) (mul_one (x * y)).symm).2
  rw [hy1, mul_one]
  exact hx

theorem sup_inf_right {V₁ V₂ : Subgroup G} (h₁ : V₁ ≤ S₁) (h₂ : V₂ ≤ S₂) :
    (V₁ ⊔ V₂) ⊓ S₂ = V₂ := by
  refine le_antisymm (fun g ⟨hg, hg₂⟩ => ?_) (le_inf le_sup_right h₂)
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_iff_of_le_normalizer
    (le_normalizer_of_comm fun x hx y hy => hd.comm (h₁ hx) (h₂ hy))).1 hg
  have hx1 : x = 1 := (hd.eq_and_eq (h₁ hx) (one_mem _) (h₂ hy) hg₂ (one_mul (x * y)).symm).1
  rw [hx1, one_mul]
  exact hy

theorem mul_mem_left_iff {x y : G} (hx : x ∈ S₁) (hy : y ∈ S₂) : x * y ∈ S₁ ↔ y = 1 := by
  refine ⟨fun h => (hd.eq_and_eq hx h hy (one_mem _) (mul_one _).symm).2, ?_⟩
  rintro rfl
  rwa [mul_one]

theorem mul_mem_right_iff {x y : G} (hx : x ∈ S₁) (hy : y ∈ S₂) : x * y ∈ S₂ ↔ x = 1 := by
  refine ⟨fun h => (hd.eq_and_eq hx (one_mem _) hy h (one_mul _).symm).1, ?_⟩
  rintro rfl
  rwa [one_mul]

theorem exists_of_mul_self {t : G} (ht : t ∈ S) (ht2 : t * t = 1) :
    ∃ x ∈ S₁, ∃ y ∈ S₂, t = x * y ∧ x * x = 1 ∧ y * y = 1 := by
  obtain ⟨x, hx, y, hy, rfl⟩ := hd.mem_iff.1 ht
  exact ⟨x, hx, y, hy, rfl, (hd.mul_self_iff hx hy).1 ht2⟩

theorem conj_left {s₁ s₂ g : G} (hs₁ : s₁ ∈ S₁) (hs₂ : s₂ ∈ S₂) (hg : g ∈ S₁) :
    s₁ * s₂ * g * (s₁ * s₂)⁻¹ = s₁ * g * s₁⁻¹ := by
  have h := hd.comm hg hs₂
  calc s₁ * s₂ * g * (s₁ * s₂)⁻¹ = s₁ * (s₂ * g) * s₂⁻¹ * s₁⁻¹ := by group
    _ = s₁ * g * s₁⁻¹ := by rw [← h]; group

theorem conj_right {s₁ s₂ g : G} (hs₁ : s₁ ∈ S₁) (hs₂ : s₂ ∈ S₂) (hg : g ∈ S₂) :
    s₁ * s₂ * g * (s₁ * s₂)⁻¹ = s₂ * g * s₂⁻¹ := by
  have h := hd.comm hs₁ (mul_mem (mul_mem hs₂ hg) (inv_mem hs₂))
  calc s₁ * s₂ * g * (s₁ * s₂)⁻¹ = s₁ * (s₂ * g * s₂⁻¹) * s₁⁻¹ := by group
    _ = s₂ * g * s₂⁻¹ := by rw [h]; group

theorem conj_mem_left {s g : G} (hs : s ∈ S) (hg : g ∈ S₁) : s * g * s⁻¹ ∈ S₁ := by
  obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := hd.mem_iff.1 hs
  rw [hd.conj_left hs₁ hs₂ hg]
  exact mul_mem (mul_mem hs₁ hg) (inv_mem hs₁)

theorem conj_mem_right {s g : G} (hs : s ∈ S) (hg : g ∈ S₂) : s * g * s⁻¹ ∈ S₂ := by
  obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := hd.mem_iff.1 hs
  rw [hd.conj_right hs₁ hs₂ hg]
  exact mul_mem (mul_mem hs₂ hg) (inv_mem hs₂)

theorem map_conj_left {s₁ s₂ : G} (hs₁ : s₁ ∈ S₁) (hs₂ : s₂ ∈ S₂) {V : Subgroup G}
    (hV : V ≤ S₁) :
    V.map (MulAut.conj (s₁ * s₂)).toMonoidHom = V.map (MulAut.conj s₁).toMonoidHom :=
  map_conj_eq_of_agree fun v hv => hd.conj_left hs₁ hs₂ (hV hv)

theorem map_conj_right {s₁ s₂ : G} (hs₁ : s₁ ∈ S₁) (hs₂ : s₂ ∈ S₂) {V : Subgroup G}
    (hV : V ≤ S₂) :
    V.map (MulAut.conj (s₁ * s₂)).toMonoidHom = V.map (MulAut.conj s₂).toMonoidHom :=
  map_conj_eq_of_agree fun v hv => hd.conj_right hs₁ hs₂ (hV hv)

theorem map_conj_inf_left {s : G} (hs : s ∈ S) (E : Subgroup G) :
    E.map (MulAut.conj s).toMonoidHom ⊓ S₁ = (E ⊓ S₁).map (MulAut.conj s).toMonoidHom :=
  inf_map_conj (fun _ hv => hd.conj_mem_left hs hv) fun v hv => by
    simpa using hd.conj_mem_left (inv_mem hs) hv

theorem map_conj_inf_right {s : G} (hs : s ∈ S) (E : Subgroup G) :
    E.map (MulAut.conj s).toMonoidHom ⊓ S₂ = (E ⊓ S₂).map (MulAut.conj s).toMonoidHom :=
  inf_map_conj (fun _ hv => hd.conj_mem_right hs hv) fun v hv => by
    simpa using hd.conj_mem_right (inv_mem hs) hv

theorem comm_left_of_comm {g₁ g₂ v : G} (hg₂ : g₂ ∈ S₂) (hv : v ∈ S₁)
    (h : v * (g₁ * g₂) = g₁ * g₂ * v) : v * g₁ = g₁ * v := by
  refine mul_right_cancel (b := g₂) ?_
  calc v * g₁ * g₂ = v * (g₁ * g₂) := mul_assoc _ _ _
    _ = g₁ * g₂ * v := h
    _ = g₁ * (g₂ * v) := mul_assoc _ _ _
    _ = g₁ * v * g₂ := by rw [← hd.comm hv hg₂, mul_assoc]

theorem comm_right_of_comm {g₁ g₂ v : G} (hg₁ : g₁ ∈ S₁) (hv : v ∈ S₂)
    (h : v * (g₁ * g₂) = g₁ * g₂ * v) : v * g₂ = g₂ * v := by
  refine mul_left_cancel (a := g₁) ?_
  calc g₁ * (v * g₂) = g₁ * v * g₂ := (mul_assoc _ _ _).symm
    _ = v * g₁ * g₂ := by rw [hd.comm hg₁ hv]
    _ = v * (g₁ * g₂) := mul_assoc _ _ _
    _ = g₁ * g₂ * v := h
    _ = g₁ * (g₂ * v) := mul_assoc _ _ _

theorem inf_centralizer_mul {x y : G} (hx : x ∈ S₁) (hy : y ∈ S₂) :
    S ⊓ C (x * y) = (S₁ ⊓ C x) ⊔ (S₂ ⊓ C y) := by
  apply le_antisymm
  · intro g hg'
    obtain ⟨hg, hgc⟩ := mem_inf.1 hg'
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hd.mem_iff.1 hg
    rw [mem_centralizer_singleton_iff] at hgc
    have h : g₁ * x * (g₂ * y) = x * g₁ * (y * g₂) := by
      calc g₁ * x * (g₂ * y) = g₁ * (x * g₂) * y := by group
        _ = g₁ * (g₂ * x) * y := by rw [hd.comm hx hg₂]
        _ = g₁ * g₂ * (x * y) := by group
        _ = x * y * (g₁ * g₂) := hgc
        _ = x * (y * g₁) * g₂ := by group
        _ = x * (g₁ * y) * g₂ := by rw [← hd.comm hg₁ hy]
        _ = x * g₁ * (y * g₂) := by group
    obtain ⟨h1, h2⟩ := hd.eq_and_eq (mul_mem hg₁ hx) (mul_mem hx hg₁) (mul_mem hg₂ hy)
      (mul_mem hy hg₂) h
    exact mul_mem (mem_sup_left ⟨hg₁, mem_centralizer_singleton_iff.2 h1⟩)
      (mem_sup_right ⟨hg₂, mem_centralizer_singleton_iff.2 h2⟩)
  · refine sup_le ?_ ?_
    · intro g hg'
      obtain ⟨hg, hgc⟩ := mem_inf.1 hg'
      refine ⟨hd.le_left hg, mem_centralizer_singleton_iff.2 ?_⟩
      rw [mem_centralizer_singleton_iff] at hgc
      calc g * (x * y) = g * x * y := (mul_assoc _ _ _).symm
        _ = x * g * y := by rw [hgc]
        _ = x * (g * y) := mul_assoc _ _ _
        _ = x * (y * g) := by rw [hd.comm hg hy]
        _ = x * y * g := (mul_assoc _ _ _).symm
    · intro g hg'
      obtain ⟨hg, hgc⟩ := mem_inf.1 hg'
      refine ⟨hd.le_right hg, mem_centralizer_singleton_iff.2 ?_⟩
      rw [mem_centralizer_singleton_iff] at hgc
      calc g * (x * y) = g * x * y := (mul_assoc _ _ _).symm
        _ = x * g * y := by rw [← hd.comm hx hg]
        _ = x * (g * y) := mul_assoc _ _ _
        _ = x * (y * g) := by rw [hgc]
        _ = x * y * g := (mul_assoc _ _ _).symm

theorem le_centralizer_mul {x y : G} (hx : x ∈ S₁) (hy : y ∈ S₂)
    (hxc : ∀ s ∈ S₁, s * x = x * s) (hyc : ∀ s ∈ S₂, s * y = y * s) : S ≤ C (x * y) := by
  have h := hd.inf_centralizer_mul hx hy
  have h₁ : S₁ ≤ S₁ ⊓ C x := le_inf le_rfl fun s hs => mem_centralizer_singleton_iff.2 (hxc s hs)
  have h₂ : S₂ ≤ S₂ ⊓ C y := le_inf le_rfl fun s hs => mem_centralizer_singleton_iff.2 (hyc s hs)
  have hle : S ≤ S ⊓ C (x * y) := by
    rw [h, ← hd.sup_eq]
    exact sup_le_sup h₁ h₂
  exact hle.trans inf_le_right

theorem inf_centralizer_left {x : G} (hx : x ∈ S₁) : S ⊓ C x = (S₁ ⊓ C x) ⊔ S₂ := by
  have h := hd.inf_centralizer_mul hx (one_mem S₂)
  rwa [mul_one, show C (1 : G) = ⊤ by simp, inf_top_eq] at h

theorem inf_centralizer_right {y : G} (hy : y ∈ S₂) : S ⊓ C y = S₁ ⊔ (S₂ ⊓ C y) := by
  have h := hd.inf_centralizer_mul (one_mem S₁) hy
  rwa [one_mul, show C (1 : G) = ⊤ by simp, inf_top_eq] at h

theorem inf_centralizer_self :
    S ⊓ centralizer (S : Set G) =
      (S₁ ⊓ centralizer (S₁ : Set G)) ⊔ (S₂ ⊓ centralizer (S₂ : Set G)) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgS, hgc⟩ := mem_inf.1 hg
    obtain ⟨x, hx, y, hy, rfl⟩ := hd.mem_iff.1 hgS
    have hC : S ≤ C (x * y) := fun s hs =>
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hgc s hs)
    obtain ⟨hxc, hyc⟩ := hd.central_components hx hy hC
    exact mul_mem (mem_sup_left ⟨hx, mem_centralizer_iff.2 hxc⟩)
      (mem_sup_right ⟨hy, mem_centralizer_iff.2 hyc⟩)
  · refine sup_le (fun x hx => ?_) (fun y hy => ?_)
    · obtain ⟨hx, hxc⟩ := mem_inf.1 hx
      refine ⟨hd.le_left hx, mem_centralizer_iff.2 fun s hs => ?_⟩
      obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := hd.mem_iff.1 hs
      rw [mul_assoc, ← hd.comm hx hs₂, ← mul_assoc, mem_centralizer_iff.1 hxc s₁ hs₁, mul_assoc]
    · obtain ⟨hy, hyc⟩ := mem_inf.1 hy
      refine ⟨hd.le_right hy, mem_centralizer_iff.2 fun s hs => ?_⟩
      obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := hd.mem_iff.1 hs
      rw [mul_assoc, mem_centralizer_iff.1 hyc s₂ hs₂, ← mul_assoc, hd.comm hs₁ hy, mul_assoc]

theorem map {G' : Type*} [Group G'] (f : G →* G') (hf : Function.Injective f) :
    DDDecomp (S.map f) (S₁.map f) (S₂.map f) := by
  refine ⟨by rw [← Subgroup.map_sup, hd.sup_eq],
    by rw [← map_inf_eq _ _ f hf, hd.inf_eq, Subgroup.map_bot], ?_, hd.dih₁.map f hf,
    hd.dih₂.map f hf⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_mul, ← map_mul, hd.comm hx hy]

theorem map_conj (g : G) :
    DDDecomp (S.map (MulAut.conj g).toMonoidHom) (S₁.map (MulAut.conj g).toMonoidHom)
      (S₂.map (MulAut.conj g).toMonoidHom) :=
  hd.map _ (MulAut.conj g).injective

theorem isE16_iff {A : Subgroup G} (hAS : A ≤ S) :
    IsE16 A ↔ IsFourIn S₁ (A ⊓ S₁) ∧ IsFourIn S₂ (A ⊓ S₂) ∧ A = (A ⊓ S₁) ⊔ (A ⊓ S₂) := by
  refine ⟨fun hA => ?_, fun ⟨h₁, h₂, h⟩ => h ▸ hd.isE16_sup h₁ h₂⟩
  obtain ⟨h, h₁, h₂⟩ := hd.e16_split hAS hA
  exact ⟨h₁, h₂, h⟩

theorem exists_e16_mem {t : G} (ht : t ∈ S) (ht2 : t * t = 1) :
    ∃ A ≤ S, IsE16 A ∧ t ∈ A := by
  obtain ⟨x, hx, y, hy, rfl, hx2, hy2⟩ := hd.exists_of_mul_self ht ht2
  obtain ⟨V₁, hV₁, hxV⟩ := hd.dih₁.exists_four_mem hx hx2
  obtain ⟨V₂, hV₂, hyV⟩ := hd.isDih₂.exists_four_mem hy hy2
  exact ⟨V₁ ⊔ V₂, sup_le (hV₁.1.trans hd.le_left) (hV₂.1.trans hd.le_right),
    hd.isE16_sup hV₁ hV₂, mul_mem (mem_sup_left hxV) (mem_sup_right hyV)⟩

theorem map_conj_sup {s₁ s₂ : G} (hs₁ : s₁ ∈ S₁) (hs₂ : s₂ ∈ S₂) {V₁ V₂ : Subgroup G}
    (h₁ : V₁ ≤ S₁) (h₂ : V₂ ≤ S₂) :
    (V₁ ⊔ V₂).map (MulAut.conj (s₁ * s₂)).toMonoidHom =
      V₁.map (MulAut.conj s₁).toMonoidHom ⊔ V₂.map (MulAut.conj s₂).toMonoidHom := by
  rw [Subgroup.map_sup, hd.map_conj_left hs₁ hs₂ h₁, hd.map_conj_right hs₁ hs₂ h₂]

theorem exists_conj_e16_iff {A B : Subgroup G} (hAS : A ≤ S) (hA : IsE16 A) (hBS : B ≤ S)
    (hB : IsE16 B) :
    (∃ s ∈ S, A.map (MulAut.conj s).toMonoidHom = B) ↔
      (∃ s₁ ∈ S₁, (A ⊓ S₁).map (MulAut.conj s₁).toMonoidHom = B ⊓ S₁) ∧
        ∃ s₂ ∈ S₂, (A ⊓ S₂).map (MulAut.conj s₂).toMonoidHom = B ⊓ S₂ := by
  obtain ⟨hAsplit, -, -⟩ := hd.e16_split hAS hA
  obtain ⟨hBsplit, -, -⟩ := hd.e16_split hBS hB
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := hd.mem_iff.1 hs
    refine ⟨⟨s₁, hs₁, ?_⟩, ⟨s₂, hs₂, ?_⟩⟩
    · rw [hd.map_conj_inf_left hs, hd.map_conj_left hs₁ hs₂ inf_le_right]
    · rw [hd.map_conj_inf_right hs, hd.map_conj_right hs₁ hs₂ inf_le_right]
  · rintro ⟨⟨s₁, hs₁, h₁⟩, ⟨s₂, hs₂, h₂⟩⟩
    refine ⟨s₁ * s₂, mul_mem (hd.le_left hs₁) (hd.le_right hs₂), ?_⟩
    rw [hAsplit, hd.map_conj_sup hs₁ hs₂ inf_le_right inf_le_right, h₁, h₂, ← hBsplit]

theorem e16_classes_of_isKleinFour (h₁ : IsKleinFour S₁) :
    ∃ Arep : Fin 2 → Subgroup G, (∀ j, Arep j ≤ S ∧ IsE16 (Arep j)) ∧
      (∀ B, B ≤ S → IsE16 B → ∃ j, ∃ s ∈ S, B.map (MulAut.conj s).toMonoidHom = Arep j) ∧
      ∀ j j', (∃ s ∈ S, (Arep j).map (MulAut.conj s).toMonoidHom = Arep j') → j = j' := by
  obtain ⟨V₀, V₁, hV₀, hV₁, hV, hVcov⟩ := hd.dih₂.exists_four_classes
  let V : Fin 2 → Subgroup G := ![V₀, V₁]
  have hVj : ∀ j, IsFourIn S₂ (V j) := by
    intro j; fin_cases j
    exacts [hV₀, hV₁]
  have hVne : ∀ j j', (∃ s ∈ S₂, (V j).map (MulAut.conj s).toMonoidHom = V j') → j = j' := by
    intro j j' ⟨s, hs, h⟩
    fin_cases j <;> fin_cases j'
    · rfl
    · exact absurd h (hV s hs)
    · refine absurd ?_ (hV s⁻¹ (inv_mem hs))
      change V₁.map _ = V₀ at h
      rw [← h, map_conj_map_conj, inv_mul_cancel, CFSG.CGT.Foote81L6.TStruct.map_conj_one]
    · rfl
  have hW := IsDih.isFourIn_self_of_isKleinFour h₁
  have hle : ∀ j, S₁ ⊔ V j ≤ S := fun j => sup_le hd.le_left ((hVj j).1.trans hd.le_right)
  have hE : ∀ j, IsE16 (S₁ ⊔ V j) := fun j => hd.isE16_sup hW (hVj j)
  have hinf₁ : ∀ j, (S₁ ⊔ V j) ⊓ S₁ = S₁ := fun j => hd.sup_inf_left le_rfl (hVj j).1
  have hinf₂ : ∀ j, (S₁ ⊔ V j) ⊓ S₂ = V j := fun j => hd.sup_inf_right le_rfl (hVj j).1
  refine ⟨fun j => S₁ ⊔ V j, fun j => ⟨hle j, hE j⟩, fun B hBS hB => ?_, fun j j' h => ?_⟩
  · obtain ⟨hB₁, hB₂, -⟩ := (hd.isE16_iff hBS).1 hB
    have hj : ∃ j, ∃ s ∈ S₂, (B ⊓ S₂).map (MulAut.conj s).toMonoidHom = V j := by
      rcases hVcov _ hB₂ with ⟨s, hs, h⟩ | ⟨s, hs, h⟩
      exacts [⟨0, s, hs, h⟩, ⟨1, s, hs, h⟩]
    obtain ⟨j, s₂, hs₂, h₂'⟩ := hj
    refine ⟨j, (hd.exists_conj_e16_iff hBS hB (hle j) (hE j)).2
      ⟨⟨1, one_mem _, ?_⟩, ⟨s₂, hs₂, by rw [h₂', hinf₂]⟩⟩⟩
    rw [CFSG.CGT.Foote81L6.TStruct.map_conj_one, hinf₁, IsDih.four_eq_of_isKleinFour h₁ hB₁]
  · obtain ⟨-, ⟨s₂, hs₂, h₂'⟩⟩ :=
      (hd.exists_conj_e16_iff (hle j) (hE j) (hle j') (hE j')).1 h
    rw [hinf₂, hinf₂] at h₂'
    exact hVne j j' ⟨s₂, hs₂, h₂'⟩

theorem inf_centralizer_e16 {A : Subgroup G} (hAS : A ≤ S) (hA : IsE16 A) :
    S ⊓ centralizer (A : Set G) = A := by
  obtain ⟨hsplit, hV₁, hV₂⟩ := hd.e16_split hAS hA
  have hA2 : ∀ x ∈ A, x * x = 1 := isElemAbelian_two_iff.1 hA.1
  apply le_antisymm
  · rintro g ⟨hg, hgc⟩
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hd.mem_iff.1 hg
    have h₁ : g₁ ∈ S₁ ⊓ centralizer ((A ⊓ S₁ : Subgroup G) : Set G) :=
      ⟨hg₁, mem_centralizer_iff.2 fun v hv =>
        hd.comm_left_of_comm hg₂ hv.2 (mem_centralizer_iff.1 hgc v hv.1)⟩
    have h₂ : g₂ ∈ S₂ ⊓ centralizer ((A ⊓ S₂ : Subgroup G) : Set G) :=
      ⟨hg₂, mem_centralizer_iff.2 fun v hv =>
        hd.comm_right_of_comm hg₁ hv.2 (mem_centralizer_iff.1 hgc v hv.1)⟩
    rw [hd.dih₁.inf_centralizer_four hV₁] at h₁
    rw [hd.isDih₂.inf_centralizer_four hV₂] at h₂
    rw [hsplit]
    exact mul_mem (mem_sup_left h₁) (mem_sup_right h₂)
  · intro a ha
    exact ⟨hAS ha, mem_centralizer_iff.2 fun b hb => comm_of_mul_self hA2 hb ha⟩

theorem inf_normalizer_e16 {A : Subgroup G} (hAS : A ≤ S) (hA : IsE16 A) :
    S ⊓ normalizer (A : Set G) = (S₁ ⊓ normalizer ((A ⊓ S₁ : Subgroup G) : Set G)) ⊔
      (S₂ ⊓ normalizer ((A ⊓ S₂ : Subgroup G) : Set G)) := by
  obtain ⟨hsplit, hV₁, hV₂⟩ := hd.e16_split hAS hA
  apply le_antisymm
  · rintro g ⟨hg, hgN⟩
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hd.mem_iff.1 hg
    have hAg := map_conj_eq_self_of_mem_normalizer hgN
    have k₁ : g₁ ∈ normalizer ((A ⊓ S₁ : Subgroup G) : Set G) := by
      apply mem_normalizer_of_map_conj_eq
      rw [← hd.map_conj_left hg₁ hg₂ inf_le_right, ← hd.map_conj_inf_left hg, hAg]
    have k₂ : g₂ ∈ normalizer ((A ⊓ S₂ : Subgroup G) : Set G) := by
      apply mem_normalizer_of_map_conj_eq
      rw [← hd.map_conj_right hg₁ hg₂ inf_le_right, ← hd.map_conj_inf_right hg, hAg]
    exact mul_mem (mem_sup_left ⟨hg₁, k₁⟩) (mem_sup_right ⟨hg₂, k₂⟩)
  · refine sup_le ?_ ?_
    · rintro g ⟨hg, hgN⟩
      refine ⟨hd.le_left hg, mem_normalizer_of_map_conj_eq ?_⟩
      rw [hsplit, Subgroup.map_sup, map_conj_eq_self_of_mem_normalizer hgN,
        map_conj_eq_self_of_comm (X := A ⊓ S₂) fun y hy => hd.comm hg (mem_inf.1 hy).2]
    · rintro g ⟨hg, hgN⟩
      refine ⟨hd.le_right hg, mem_normalizer_of_map_conj_eq ?_⟩
      rw [hsplit, Subgroup.map_sup, map_conj_eq_self_of_mem_normalizer hgN,
        map_conj_eq_self_of_comm (X := A ⊓ S₁) fun y hy => (hd.comm (mem_inf.1 hy).2 hg).symm]

theorem card_inf_normalizer_e16 {A : Subgroup G} (hAS : A ≤ S) (hA : IsE16 A) :
    Nat.card ↥(S ⊓ normalizer (A : Set G)) =
      Nat.card ↥(S₁ ⊓ normalizer ((A ⊓ S₁ : Subgroup G) : Set G)) *
        Nat.card ↥(S₂ ⊓ normalizer ((A ⊓ S₂ : Subgroup G) : Set G)) := by
  rw [hd.inf_normalizer_e16 hAS hA]
  refine card_sup_of_le_normalizer (le_normalizer_of_comm fun x hx y hy => ?_)
    (eq_bot_iff.2 ((inf_le_inf inf_le_left inf_le_left).trans hd.inf_eq.le))
  exact hd.comm (mem_inf.1 hx).1 (mem_inf.1 hy).1

theorem card_inf_normalizer_e16_of_isDihNonab (h₁ : IsDihNonab S₁) {A : Subgroup G}
    (hAS : A ≤ S) (hA : IsE16 A) : Nat.card ↥(S ⊓ normalizer (A : Set G)) = 64 := by
  obtain ⟨-, hV₁, hV₂⟩ := hd.e16_split hAS hA
  rw [hd.card_inf_normalizer_e16 hAS hA, h₁.card_inf_normalizer_four hV₁,
    hd.dih₂.card_inf_normalizer_four hV₂]

theorem inf_normalizer_e16_of_isKleinFour (h₁ : IsKleinFour S₁) {A : Subgroup G}
    (hAS : A ≤ S) (hA : IsE16 A) :
    S ⊓ normalizer (A : Set G) = S₁ ⊔ (S₂ ⊓ normalizer ((A ⊓ S₂ : Subgroup G) : Set G)) ∧
      Nat.card ↥(S ⊓ normalizer (A : Set G)) = 32 := by
  obtain ⟨-, hV₁, hV₂⟩ := hd.e16_split hAS hA
  have hX : A ⊓ S₁ = S₁ := IsDih.four_eq_of_isKleinFour h₁ hV₁
  have hN₁ : S₁ ⊓ normalizer ((A ⊓ S₁ : Subgroup G) : Set G) = S₁ := by
    rw [hX]
    exact inf_of_le_left le_normalizer
  refine ⟨by rw [hd.inf_normalizer_e16 hAS hA, hN₁], ?_⟩
  rw [hd.card_inf_normalizer_e16 hAS hA, hN₁, IsKleinFour.card_four,
    hd.dih₂.card_inf_normalizer_four hV₂]

theorem exists_normalizer_e16 (h₁ : IsDihNonab S₁) {A : Subgroup G} (hAS : A ≤ S)
    (hA : IsE16 A) :
    ∃ f₁ ∈ S₁, ∃ f₂ ∈ S₂, f₁ * f₁ = 1 ∧ f₂ * f₂ = 1 ∧
      S₁ ⊓ normalizer ((A ⊓ S₁ : Subgroup G) : Set G) = (A ⊓ S₁) ⊔ zpowers f₁ ∧
      S₂ ⊓ normalizer ((A ⊓ S₂ : Subgroup G) : Set G) = (A ⊓ S₂) ⊔ zpowers f₂ ∧
      S ⊓ normalizer (A : Set G) = A ⊔ (zpowers f₁ ⊔ zpowers f₂) ∧
      A ⊓ (zpowers f₁ ⊔ zpowers f₂) = ⊥ ∧ IsKleinFour ↥(zpowers f₁ ⊔ zpowers f₂) := by
  obtain ⟨hsplit, hV₁, hV₂⟩ := hd.e16_split hAS hA
  obtain ⟨f₁, hf₁, hf₁2, hf₁V, hN₁⟩ := h₁.exists_inf_normalizer_four_eq hV₁
  obtain ⟨f₂, hf₂, hf₂2, hf₂V, hN₂⟩ := hd.dih₂.exists_inf_normalizer_four_eq hV₂
  have hc : ∀ x ∈ zpowers f₁, ∀ y ∈ zpowers f₂, x * y = y * x := fun x hx y hy =>
    hd.comm (zpowers_le.2 hf₁ hx) (zpowers_le.2 hf₂ hy)
  have hf₁1 : f₁ ≠ 1 := fun h => hf₁V (h ▸ one_mem _)
  have hf₂1 : f₂ ≠ 1 := fun h => hf₂V (h ▸ one_mem _)
  have hne : f₁ ≠ f₂ := by
    intro h
    have : f₁ ∈ S₁ ⊓ S₂ := ⟨hf₁, h ▸ hf₂⟩
    rw [hd.inf_eq, mem_bot] at this
    exact hf₁1 this
  refine ⟨f₁, hf₁, f₂, hf₂, hf₁2, hf₂2, hN₁, hN₂, ?_, ?_, ?_⟩
  · rw [hd.inf_normalizer_e16 hAS hA, hN₁, hN₂, hsplit, sup_sup_sup_comm]
    simp only [← hsplit]
  · rw [eq_bot_iff]
    rintro g ⟨hgA, hgF⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hc)).1 hgF
    rw [hsplit] at hgA
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_le_normalizer
      (le_normalizer_of_comm (H := A ⊓ S₁) (K := A ⊓ S₂) fun x hx y hy =>
        hd.comm (mem_inf.1 hx).2 (mem_inf.1 hy).2)).1 hgA
    obtain ⟨hua, hvb⟩ := hd.eq_and_eq (zpowers_le.2 hf₁ hu) ha.2 (zpowers_le.2 hf₂ hv) hb.2 hab
    have hu1 : u = 1 := by
      rcases eq_one_or_eq_of_mem_zpowers hf₁2 hu with h | h
      · exact h
      · exact absurd (h ▸ hua ▸ ha.1 : f₁ ∈ A) fun h' => hf₁V ⟨h', hf₁⟩
    have hv1 : v = 1 := by
      rcases eq_one_or_eq_of_mem_zpowers hf₂2 hv with h | h
      · exact h
      · exact absurd (h ▸ hvb ▸ hb.1 : f₂ ∈ A) fun h' => hf₂V ⟨h', hf₂⟩
    rw [hu1, hv1, mul_one]
    exact one_mem _
  · exact isKleinFour_of_isFourIn (D := ⊤) ⟨le_top,
      fun g hg => mul_self_of_mem_zpowers_sup_zpowers hf₁2 hf₂2 (hc _ (mem_zpowers _) _
        (mem_zpowers _)) hg,
      card_zpowers_sup_zpowers hf₁2 hf₂2 hf₁1 hf₂1 hne (hc _ (mem_zpowers _) _ (mem_zpowers _))⟩

theorem sSup_e16 {𝒜 : Set (Subgroup G)} (h𝒜 : ∀ A ∈ 𝒜, A ≤ S ∧ IsE16 A) (hne : 𝒜.Nonempty) :
    sSup 𝒜 = (sSup 𝒜 ⊓ S₁) ⊔ (sSup 𝒜 ⊓ S₂) ∧ IsDih (sSup 𝒜 ⊓ S₁) ∧ IsDih (sSup 𝒜 ⊓ S₂) := by
  obtain ⟨A₀, hA₀⟩ := hne
  obtain ⟨-, hV₁, hV₂⟩ := hd.e16_split (h𝒜 A₀ hA₀).1 (h𝒜 A₀ hA₀).2
  refine ⟨le_antisymm (sSup_le fun A hA => ?_) (sup_le inf_le_left inf_le_left), ?_, ?_⟩
  · obtain ⟨hsplit, -, -⟩ := hd.e16_split (h𝒜 A hA).1 (h𝒜 A hA).2
    rw [hsplit]
    exact sup_le_sup (inf_le_inf_right _ (le_sSup hA)) (inf_le_inf_right _ (le_sSup hA))
  · exact hd.dih₁.of_le inf_le_right hV₁ (inf_le_inf_right _ (le_sSup hA₀))
  · exact hd.isDih₂.of_le inf_le_right hV₂ (inf_le_inf_right _ (le_sSup hA₀))

theorem exists_injective_of_inf_left_eq_bot {R : Subgroup G} (hRS : R ≤ S) (hR : R ⊓ S₁ = ⊥) :
    ∃ f : ↥R →* ↥S₂, Function.Injective f ∧ ∀ r : R, ∃ x ∈ S₁, (r : G) = x * (f r : G) := by
  obtain ⟨μ, hμ⟩ := hd.exists_mulEquiv
  refine ⟨(MonoidHom.snd _ _).comp (μ.symm.toMonoidHom.comp (inclusion hRS)), ?_, fun r => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro r hr
    have key : (r : G) = ((μ.symm (inclusion hRS r)).1 : G) := by
      have h := hμ (μ.symm (inclusion hRS r))
      rw [MulEquiv.apply_symm_apply] at h
      change (r : G) = _ * ((μ.symm (inclusion hRS r)).2 : G) at h
      have hr' : (μ.symm (inclusion hRS r)).2 = 1 := hr
      rw [hr', OneMemClass.coe_one, mul_one] at h
      exact h
    have : (r : G) ∈ R ⊓ S₁ := ⟨r.2, key ▸ (μ.symm (inclusion hRS r)).1.2⟩
    rw [hR, mem_bot] at this
    exact Subtype.ext this
  · refine ⟨((μ.symm (inclusion hRS r)).1 : G), (μ.symm (inclusion hRS r)).1.2, ?_⟩
    have h := hμ (μ.symm (inclusion hRS r))
    rw [MulEquiv.apply_symm_apply] at h
    exact h

theorem exists_injective_of_inf_right_eq_bot {R : Subgroup G} (hRS : R ≤ S) (hR : R ⊓ S₂ = ⊥) :
    ∃ f : ↥R →* ↥S₁, Function.Injective f ∧ ∀ r : R, ∃ y ∈ S₂, (r : G) = (f r : G) * y := by
  obtain ⟨μ, hμ⟩ := hd.exists_mulEquiv
  refine ⟨(MonoidHom.fst _ _).comp (μ.symm.toMonoidHom.comp (inclusion hRS)), ?_, fun r => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro r hr
    have key : (r : G) = ((μ.symm (inclusion hRS r)).2 : G) := by
      have h := hμ (μ.symm (inclusion hRS r))
      rw [MulEquiv.apply_symm_apply] at h
      change (r : G) = ((μ.symm (inclusion hRS r)).1 : G) * _ at h
      have hr' : (μ.symm (inclusion hRS r)).1 = 1 := hr
      rw [hr', OneMemClass.coe_one, one_mul] at h
      exact h
    have : (r : G) ∈ R ⊓ S₂ := ⟨r.2, key ▸ (μ.symm (inclusion hRS r)).2.2⟩
    rw [hR, mem_bot] at this
    exact Subtype.ext this
  · refine ⟨((μ.symm (inclusion hRS r)).2 : G), (μ.symm (inclusion hRS r)).2.2, ?_⟩
    have h := hμ (μ.symm (inclusion hRS r))
    rw [MulEquiv.apply_symm_apply] at h
    exact h

theorem relIndex_sup_left {R : Subgroup G} (hR : R ≤ S₂) : (S₁ ⊔ R).relIndex S = R.relIndex S₂ := by
  haveI := hd.dih₁.finite
  haveI := hd.isDih₂.finite
  haveI : Finite R := Finite.of_injective _ (inclusion_injective hR)
  have hle : S₁ ⊔ R ≤ S := sup_le hd.le_left (hR.trans hd.le_right)
  have hc : ∀ x ∈ S₁, ∀ y ∈ R, x * y = y * x := fun x hx y hy => hd.comm hx (hR hy)
  have hcard : Nat.card ↥(S₁ ⊔ R) = Nat.card S₁ * Nat.card R :=
    card_sup_of_le_normalizer (le_normalizer_of_comm hc)
      (eq_bot_iff.2 ((inf_le_inf le_rfl hR).trans hd.inf_eq.le))
  have hcardS : Nat.card S = Nat.card S₁ * Nat.card S₂ := by
    rw [← hd.sup_eq]
    exact card_sup_of_le_normalizer (le_normalizer_of_comm fun x hx y hy => hd.comm hx hy)
      hd.inf_eq
  have h1 := relIndex_mul_card (S₁ ⊔ R) S
  have h2 := relIndex_mul_card R S₂
  rw [inf_of_le_left hle, hcard, hcardS] at h1
  rw [inf_of_le_left hR] at h2
  have hpos : 0 < Nat.card S₁ * Nat.card R := Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1, ← h2]
  ring

theorem relIndex_sup_right {R : Subgroup G} (hR : R ≤ S₁) :
    (R ⊔ S₂).relIndex S = R.relIndex S₁ := by
  haveI := hd.dih₁.finite
  haveI := hd.isDih₂.finite
  haveI : Finite R := Finite.of_injective _ (inclusion_injective hR)
  have hle : R ⊔ S₂ ≤ S := sup_le (hR.trans hd.le_left) hd.le_right
  have hc : ∀ x ∈ R, ∀ y ∈ S₂, x * y = y * x := fun x hx y hy => hd.comm (hR hx) hy
  have hcard : Nat.card ↥(R ⊔ S₂) = Nat.card R * Nat.card S₂ :=
    card_sup_of_le_normalizer (le_normalizer_of_comm hc)
      (eq_bot_iff.2 ((inf_le_inf hR le_rfl).trans hd.inf_eq.le))
  have hcardS : Nat.card S = Nat.card S₁ * Nat.card S₂ := by
    rw [← hd.sup_eq]
    exact card_sup_of_le_normalizer (le_normalizer_of_comm fun x hx y hy => hd.comm hx hy)
      hd.inf_eq
  have h1 := relIndex_mul_card (R ⊔ S₂) S
  have h2 := relIndex_mul_card R S₁
  rw [inf_of_le_left hle, hcard, hcardS] at h1
  rw [inf_of_le_left hR] at h2
  have hpos : 0 < Nat.card R * Nat.card S₂ := Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1, ← h2]
  ring

end DDDecomp

section Sylow

variable [Finite G] {P : Sylow 2 G} {S₁ S₂ : Subgroup G}

private theorem coe_smul_sylow_eq (g : G) (P : Sylow 2 G) :
    ((g • P : Sylow 2 G) : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
  rfl

theorem DDDecomp.isSylowOf_centralizer_e16 (hd : DDDecomp (P : Subgroup G) S₁ S₂)
    {A : Subgroup G} (hAS : A ≤ P) (hA : IsE16 A) :
    CFSG.ABGLocalTools.IsSylowOf 2 A (centralizer (A : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 4) (by rw [hA.2]; norm_num)
  have hAC : A ≤ centralizer (A : Set G) := fun a ha =>
    mem_centralizer_iff.2 fun b hb => comm_of_mul_self (isElemAbelian_two_iff.1 hA.1) hb ha
  obtain ⟨T, hT⟩ := (hA2.comap_subtype (K := centralizer (A : Set G))).exists_le_sylow
  set T' := (T : Subgroup (centralizer (A : Set G))).map (centralizer (A : Set G)).subtype
  have hAT' : A ≤ T' := fun a ha =>
    ⟨⟨a, hAC ha⟩, hT (show (⟨a, hAC ha⟩ : centralizer (A : Set G)) ∈
      A.comap (centralizer (A : Set G)).subtype from ha), rfl⟩
  obtain ⟨R, hR⟩ := (T.isPGroup'.map (centralizer (A : Set G)).subtype).exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P R
  have hd' := hd.map_conj g
  rw [← coe_smul_sylow_eq] at hd'
  have hRA := hd'.inf_centralizer_e16 (hAT'.trans hR) hA
  exact ⟨T, le_antisymm ((le_inf hR (map_subtype_le _)).trans hRA.le) hAT'⟩

theorem DDDecomp.isSylowOf_normalizer_e16 (hd : DDDecomp (P : Subgroup G) S₁ S₂)
    {A : Subgroup G} (hAS : A ≤ P) (hA : IsE16 A) :
    CFSG.ABGLocalTools.IsSylowOf 2 ((P : Subgroup G) ⊓ normalizer (A : Set G))
      (normalizer (A : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (A : Set G)
  set U₀ := (P : Subgroup G) ⊓ N
  have hU₀2 : IsPGroup 2 U₀ := P.isPGroup'.to_inf_left
  obtain ⟨T, hT⟩ := (hU₀2.comap_subtype (K := N)).exists_le_sylow
  set T' := (T : Subgroup N).map N.subtype
  have hU₀T' : U₀ ≤ T' := fun x hx =>
    ⟨⟨x, hx.2⟩, hT (show (⟨x, hx.2⟩ : N) ∈ U₀.comap N.subtype from hx), rfl⟩
  obtain ⟨R, hR⟩ := (T.isPGroup'.map N.subtype).exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P R
  have hd' := hd.map_conj g
  rw [← coe_smul_sylow_eq] at hd'
  set R' := ((g • P : Sylow 2 G) : Subgroup G)
  have hAR : A ≤ R' := (le_inf hAS le_normalizer).trans (hU₀T'.trans hR)
  have hcard : Nat.card ↥(R' ⊓ N) = Nat.card U₀ := by
    rcases hd.dih₁.isKleinFour_or_isDihNonab with h₁ | h₁
    · have h₁' : IsKleinFour ↥(S₁.map (MulAut.conj g).toMonoidHom) :=
        isKleinFour_of_isFourIn (isFourIn_map (IsDih.isFourIn_self_of_isKleinFour h₁) _
          (MulAut.conj g).injective)
      rw [(hd'.inf_normalizer_e16_of_isKleinFour h₁' hAR hA).2,
        (hd.inf_normalizer_e16_of_isKleinFour h₁ hAS hA).2]
    · rw [hd'.card_inf_normalizer_e16_of_isDihNonab (h₁.map _ (MulAut.conj g).injective) hAR hA,
        hd.card_inf_normalizer_e16_of_isDihNonab h₁ hAS hA]
  have hT'le : T' ≤ R' ⊓ N := le_inf hR (map_subtype_le _)
  have h1 : T' = R' ⊓ N :=
    eq_of_le_of_card_ge hT'le (by rw [hcard]; exact card_le_of_le hU₀T')
  have h2 : U₀ = R' ⊓ N := eq_of_le_of_card_ge (hU₀T'.trans hT'le) (by rw [hcard])
  exact ⟨T, h1.trans h2.symm⟩

end Sylow

end CFSG.GH72
