module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarInvol
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.CoverOf
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSInvolutions

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.TwoHS
open scoped commutatorElement

section KeyLemma

theorem exists_conj_pi_z1E {E : Type} [Group E] (M : CoverModel E) :
    ∃ c ∈ hsP, (M.π M.z1E : Equiv.Perm (Fin 3850)) = c * hsT1 * c⁻¹ := by
  have hsift : ∀ (T : Table) (g : Equiv.Perm (Fin 3850)), Rep 3850 T g →
      (hsSift T = true ↔ g ∈ hsP) := fun T g hT => hs_groupData.sift T g hT
  have hrepr : Rep 3850 (hsCentTbl 5) (tp 3850 (hsCentTbl 5)) := by
    obtain ⟨r, hr, hrep⟩ : ∃ r ∈ hsRows, r.rep = hsCentTbl 5 := by
      refine ⟨_, List.mem_cons_self, ?_⟩
      simp
    rw [← hrep]
    exact rep_tp (hsRows_permOK r hr)
  obtain ⟨c, hcP, hc⟩ := conjOK_spec hsift hrepr harLiftOK_parts.1
  have hz1 : Rep 3850 (tUX [3, 3, 3, 3]) (M.π M.z1E : Equiv.Perm (Fin 3850)) := by
    rw [M.z1E_eq]
    exact M.rep_tUX _ (by decide)
  exact ⟨c, hcP, rep_unique hz1 hc⟩

theorem exists_mulEquiv_of_ker_eq {E Y Y' : Type} [Group E] [Group Y] [Group Y'] (q : E →* Y)
    (π : E →* Y') (hq : Function.Surjective q) (hπ : Function.Surjective π) (h : q.ker = π.ker) :
    ∃ θ : Y ≃* Y', ∀ x, θ (q x) = π x := by
  refine ⟨((QuotientGroup.quotientKerEquivOfSurjective q hq).symm.trans
    (QuotientGroup.quotientMulEquivOfEq h)).trans (QuotientGroup.quotientKerEquivOfSurjective π hπ),
    fun x => ?_⟩
  have : (QuotientGroup.quotientKerEquivOfSurjective q hq).symm (q x) = (x : E ⧸ q.ker) :=
    (MulEquiv.symm_apply_eq _).2 rfl
  simp [this]
  rfl

theorem card_centralizer_eq_of_sq_eq_one {E Y : Type} [Group E] [Finite E] [Group Y]
    (hperf : Group.IsPerfect E) (hZ : Nat.card (center E) = 2)
    (hq : IsSporadic (E ⧸ center E) .HS) (q : E →* Y) (hqs : Function.Surjective q)
    (hqk : q.ker = center E) {m : E} (hm : m ^ 2 = 1) (hm1 : q m ≠ 1) :
    Nat.card (centralizer ({q m} : Set Y)) = 7680 := by
  obtain ⟨M⟩ := exists_coverModel hperf hZ hq
  obtain ⟨θ, hθ⟩ := exists_mulEquiv_of_ker_eq q M.π hqs M.π_surj (by rw [hqk, M.ker_pi_eq])
  have hmt : m ≠ M.tE := fun h => hm1 (by
    rw [h]; exact (MonoidHom.mem_ker.1 (hqk ▸ M.tE_mem_center)))
  have hm1' : m ≠ 1 := fun h => hm1 (by rw [h, map_one])
  obtain ⟨e, he⟩ := M.exists_conj_of_involution hZ hm hm1' hmt
  obtain ⟨c, hc, hcz⟩ := exists_conj_pi_z1E M
  obtain ⟨hmem1, -⟩ := hsT1_mem_ord
  have hz : M.π M.z1E = (⟨c, hc⟩ : ↥hsP) * ⟨hsT1, hmem1⟩ * (⟨c, hc⟩ : ↥hsP)⁻¹ := Subtype.ext hcz
  have hpm : M.π m = (M.π e)⁻¹ * M.π M.z1E * M.π e := by
    have h' : M.π e * M.π m * (M.π e)⁻¹ = M.π M.z1E := by
      rcases he with h | h
      · rw [← map_mul, ← map_inv, ← map_mul, h]
      · have := congrArg M.π h
        simp only [map_mul, map_inv, M.pi_tE, one_mul] at this
        exact this
    calc M.π m = (M.π e)⁻¹ * (M.π e * M.π m * (M.π e)⁻¹) * M.π e := by group
      _ = _ := by rw [h']
  have hconj : IsConj (⟨hsT1, hmem1⟩ : ↥hsP) (M.π m) := by
    refine isConj_iff.2 ⟨(M.π e)⁻¹ * ⟨c, hc⟩, ?_⟩
    rw [hpm, hz]
    group
  have h7680 : Nat.card (centralizer ({(⟨hsT1, hmem1⟩ : ↥hsP)} : Set ↥hsP)) = 7680 := by
    rw [card_centralizer_hsP]
    exact hs_reps.2.2.1
  rw [← card_centralizer_equiv θ (q m), hθ, ← h7680]
  exact (card_centralizer_eq_of_isConj hconj).symm

end KeyLemma

section CenterBound

open CFSG.Sporadic.Recognition.HSMultiplier CFSG.Sporadic.Recognition.CoverRecipe

theorem card_center_eq_two_of_ne_bot
    {E : Type} [Group E] [Finite E] (hE : Group.IsPerfect E)
    (hq : IsSporadic (E ⧸ center E) .HS) (hne : center E ≠ ⊥) : Nat.card (center E) = 2 := by
  obtain ⟨e₀⟩ := hq
  have e : E ⧸ center E ≃* NativeSporadic.HS := e₀
  obtain ⟨hfin, hle⟩ := cover_card_le
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center E)
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.HS.card_HS] at h1
  have hk : 2 ≤ Nat.card (center E) := by
    have hpos : 0 < Nat.card (center E) := Nat.card_pos
    by_contra hlt
    have : Nat.card (center E) = 1 := by omega
    exact hne (Subgroup.card_eq_one.1 this)
  have hcard : 88704000 ≤ Nat.card E := by omega
  have := hfin
  obtain ⟨f⟩ := TwoHS.nonempty_mulEquiv_presentedCover
    isPresentation_hsGen_of_certificate
    hsCommW_mem_commutator (lift_hsCommW hsTabCheck_eq_true) hE
    (e.trans CFSG.Sporadic.Bridge.HS.nativeEquiv) (le_trans hle hcard)
  have h2 : Nat.card E ≤ 88704000 := by rw [← Nat.card_congr f.toEquiv]; exact hle
  omega

end CenterBound

section Perfect

theorem isPerfect_of_isSporadic_hs {Y : Type} [Group Y]
    (hY : IsSporadic Y .HS) : Group.IsPerfect Y := by
  obtain ⟨e₀⟩ := hY
  have e : Y ≃* NativeSporadic.HS := e₀
  have hs : IsSimpleGroup NativeSporadic.HS := CFSG.Sporadic.HS.fam_hs_simplicity.2.2
  have : IsSimpleGroup Y := @MulEquiv.isSimpleGroup Y _ NativeSporadic.HS _ hs e
  have hc : center Y = ⊥ := center_eq_bot_of_isSporadic_hs ⟨e₀⟩
  have hnc : ∃ a b : Y, a * b ≠ b * a := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    have hn : Nontrivial NativeSporadic.HS := CFSG.Sporadic.HS.fam_hs_simplicity.2.1
    have hnt : Nontrivial Y := e.toEquiv.nontrivial
    obtain ⟨y, hy⟩ := exists_ne (1 : Y)
    have : y ∈ center Y := mem_center_iff.2 fun g => h g y
    rw [hc, mem_bot] at this
    exact hy this
  exact TwoHS.isPerfect_of_simple_noncomm hnc

end Perfect

section Centralizer

theorem card_centralizer_quotient_ne_7680 {K : Type} [Group K] [Finite K] (W : Subgroup K)
    [W.Normal] (hW : Nat.card W ∣ 18) (u' : K)
    (h : 2880 * 18 ∣ Nat.card (centralizer ({u'} : Set K))) :
    Nat.card (centralizer ({(u' : K ⧸ W)} : Set (K ⧸ W))) ≠ 7680 := by
  intro h7680
  let C : Subgroup K := centralizer ({u'} : Set K)
  let f : C →* K ⧸ W := (QuotientGroup.mk' W).comp C.subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have hker : Nat.card f.ker ∣ 18 := by
    have hle : f.ker.map C.subtype ≤ W := by
      rintro _ ⟨c, hc, rfl⟩
      exact (QuotientGroup.eq_one_iff _).1 hc
    rw [← Subgroup.card_map_of_injective C.subtype_injective]
    exact (Subgroup.card_dvd_of_le hle).trans hW
  have hrange : Nat.card f.range ∣ 7680 := by
    rw [← h7680]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨c, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hc' := mem_centralizer_singleton_iff.1 c.2
    show ((c : K) : K ⧸ W) * (u' : K ⧸ W) = (u' : K ⧸ W) * ((c : K) : K ⧸ W)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc']
  have h2 : 2880 * 18 ∣ Nat.card f.ker * Nat.card f.range := by rw [h1]; exact h
  have h3 := h2.trans (Nat.mul_dvd_mul hker hrange)
  omega

end Centralizer

section ZStructure

variable {G : Type} [Group G] {J X : Subgroup G} {u₁ : G}

theorem exists_eq_of_mem_sup (hXJ : X ≤ J) (hu₁c : ∀ g ∈ J, u₁ * g = g * u₁)
    (hu₁ : orderOf u₁ = 2) {z : G} (hz : z ∈ X ⊔ zpowers u₁) :
    ∃ x ∈ X, z = x ∨ z = x * u₁ := by
  have hsq : u₁ * u₁ = 1 := by rw [← pow_two]; exact hu₁ ▸ pow_orderOf_eq_one u₁
  have hinv : u₁⁻¹ = u₁ := inv_eq_of_mul_eq_one_right hsq
  let S : Subgroup G :=
    { carrier := {z | ∃ x ∈ X, z = x ∨ z = x * u₁}
      one_mem' := ⟨1, X.one_mem, Or.inl rfl⟩
      mul_mem' := by
        rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
        have hc : u₁ * y = y * u₁ := hu₁c y (hXJ hy)
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact ⟨a * b, X.mul_mem hx hy, Or.inl rfl⟩
        · exact ⟨a * y, X.mul_mem hx hy, Or.inr (by rw [mul_assoc])⟩
        · refine ⟨x * b, X.mul_mem hx hy, Or.inr ?_⟩
          rw [mul_assoc x u₁ b, hu₁c b (hXJ hy), ← mul_assoc]
        · refine ⟨x * y, X.mul_mem hx hy, Or.inl ?_⟩
          rw [mul_assoc x u₁ (y * u₁), ← mul_assoc u₁ y u₁, hc, mul_assoc y u₁ u₁, hsq, mul_one]
      inv_mem' := by
        rintro a ⟨x, hx, ha | ha⟩
        · exact ⟨x⁻¹, X.inv_mem hx, Or.inl (by rw [ha])⟩
        · refine ⟨x⁻¹, X.inv_mem hx, Or.inr ?_⟩
          rw [ha, mul_inv_rev, hinv, hu₁c x⁻¹ (hXJ (X.inv_mem hx))] }
  have hle : X ⊔ zpowers u₁ ≤ S := by
    refine sup_le (fun x hx => ⟨x, hx, Or.inl rfl⟩) ((zpowers_le).2 ?_)
    exact ⟨1, X.one_mem, Or.inr (one_mul u₁).symm⟩
  exact hle hz

theorem mul_comm_of_mem_sup (hXc : ∀ x ∈ X, ∀ g ∈ J, x * g = g * x)
    (hu₁c : ∀ g ∈ J, u₁ * g = g * u₁) {z : G} (hz : z ∈ X ⊔ zpowers u₁) :
    ∀ g ∈ J, z * g = g * z := by
  have : X ⊔ zpowers u₁ ≤ centralizer (J : Set G) := by
    refine sup_le (fun x hx => mem_centralizer_iff.2 fun g hg => (hXc x hx g hg).symm)
      ((zpowers_le).2 (mem_centralizer_iff.2 fun g hg => (hu₁c g hg).symm))
  intro g hg
  exact (mem_centralizer_iff.1 (this hz) g hg).symm

theorem sq_mem_of_mem_sup (hXJ : X ≤ J) (hu₁c : ∀ g ∈ J, u₁ * g = g * u₁)
    (hu₁ : orderOf u₁ = 2) {z : G} (hz : z ∈ X ⊔ zpowers u₁) : z ^ 2 ∈ X := by
  have hsq : u₁ * u₁ = 1 := by rw [← pow_two]; exact hu₁ ▸ pow_orderOf_eq_one u₁
  obtain ⟨x, hx, rfl | rfl⟩ := exists_eq_of_mem_sup hXJ hu₁c hu₁ hz
  · exact X.pow_mem hx 2
  · have hcomm : u₁ * x = x * u₁ := hu₁c x (hXJ hx)
    have : (x * u₁) ^ 2 = x ^ 2 := by
      rw [pow_two, pow_two, mul_assoc x u₁ (x * u₁), ← mul_assoc u₁ x u₁, hcomm, mul_assoc x u₁ u₁,
        hsq, mul_one]
    rw [this]
    exact X.pow_mem hx 2

theorem card_sup_dvd (hXJ : X ≤ J) (hu₁c : ∀ g ∈ J, u₁ * g = g * u₁) (hu₁ : orderOf u₁ = 2)
    [Finite G] (hX : Nat.card X = 9) : Nat.card (X ⊔ zpowers u₁ : Subgroup G) ∣ 18 := by
  have hsub : ((X ⊔ zpowers u₁ : Subgroup G) : Set G) ⊆
      (X : Set G) ∪ (fun x => x * u₁) '' (X : Set G) := by
    intro z hz
    obtain ⟨x, hx, rfl | rfl⟩ := exists_eq_of_mem_sup hXJ hu₁c hu₁ hz
    · exact Or.inl hx
    · exact Or.inr ⟨x, hx, rfl⟩
  have hX' : (X : Set G).ncard = 9 := by rw [← Nat.card_coe_set_eq]; exact hX
  have hle : Nat.card (X ⊔ zpowers u₁ : Subgroup G) ≤ 18 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    calc ((X ⊔ zpowers u₁ : Subgroup G) : Set G).ncard
        ≤ ((X : Set G) ∪ (fun x => x * u₁) '' (X : Set G)).ncard := Set.ncard_le_ncard hsub
      _ ≤ (X : Set G).ncard + ((fun x => x * u₁) '' (X : Set G)).ncard := Set.ncard_union_le _ _
      _ ≤ 9 + 9 := by
        have := Set.ncard_image_le (f := fun x => x * u₁) (s := (X : Set G)) (Set.toFinite _)
        omega
  have hdvd : 9 ∣ Nat.card (X ⊔ zpowers u₁ : Subgroup G) := by
    rw [← hX]
    exact Subgroup.card_dvd_of_le le_sup_left
  have hpos : 0 < Nat.card (X ⊔ zpowers u₁ : Subgroup G) := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd
  have : k = 1 ∨ k = 2 := by omega
  rcases this with rfl | rfl
  · rw [hk]; norm_num
  · rw [hk]

end ZStructure

section Main

section CommutatorLemmas

variable {G : Type} [Group G]

theorem commutatorElement_mul_central_left {a z y : G} (h : z * y = y * z) :
    ⁅a * z, y⁆ = ⁅a, y⁆ := by
  have h' : z * y * z⁻¹ = y := mul_inv_eq_iff_eq_mul.2 h
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc a * z * y * (z⁻¹ * a⁻¹) * y⁻¹ = a * (z * y * z⁻¹) * a⁻¹ * y⁻¹ := by group
    _ = a * y * a⁻¹ * y⁻¹ := by rw [h']

theorem commutatorElement_mul_central_right {a b w : G} (h : w * a = a * w) :
    ⁅a, b * w⁆ = ⁅a, b⁆ := by
  have h' : w * a⁻¹ * w⁻¹ = a⁻¹ := by
    have : w * a⁻¹ = a⁻¹ * w := (Commute.inv_right (show Commute w a from h)).eq
    rw [this, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc a * (b * w) * a⁻¹ * (w⁻¹ * b⁻¹) = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h']

end CommutatorLemmas

set_option linter.unusedVariables false in
theorem isSporadic_commutator_of_quotient_hs
    {G : Type} [Group G] [Finite G] (J X : Subgroup G) (u₁ u : G)
    [((X ⊔ zpowers u₁).subgroupOf J).Normal]
    (hXJ : X ≤ J) (hu₁J : u₁ ∈ J) (huJ : u ∈ J)
    (hXc : ∀ x ∈ X, ∀ g ∈ J, x * g = g * x) (hu₁c : ∀ g ∈ J, u₁ * g = g * u₁)
    (hX : Nat.card X = 9) (hu₁ : orderOf u₁ = 2) (hu₁X : u₁ ∉ X) (hu : orderOf u = 2)
    (huZ : u ∉ X ⊔ zpowers u₁)
    (hY : IsSporadic (↥J ⧸ (X ⊔ zpowers u₁).subgroupOf J) .HS)
    (h2B : 2880 * 18 ∣ Nat.card ↥(J ⊓ centralizer ({u} : Set G))) :
    IsSporadic ↥(⁅J, J⁆) .HS ∧ ⁅J, J⁆ ⊓ (X ⊔ zpowers u₁) = ⊥ := by
  have hZc : ∀ z ∈ X ⊔ zpowers u₁, ∀ g ∈ J, z * g = g * z := fun z hz =>
    mul_comm_of_mem_sup hXc hu₁c hz
  have hZJ : X ⊔ zpowers u₁ ≤ J := sup_le hXJ ((zpowers_le).2 hu₁J)
  have hMJ : ⁅J, J⁆ ≤ J := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact J.mul_mem (J.mul_mem (J.mul_mem ha hb) (J.inv_mem ha)) (J.inv_mem hb)
  let Zs : Subgroup ↥J := (X ⊔ zpowers u₁).subgroupOf J
  let q : ↥J →* ↥J ⧸ Zs := QuotientGroup.mk' Zs
  let qM : ↥(⁅J, J⁆) →* ↥J ⧸ Zs := q.comp (Subgroup.inclusion hMJ)
  have hYperf : Group.IsPerfect (↥J ⧸ Zs) := isPerfect_of_isSporadic_hs hY
  have hqM_mem : ∀ m : ↥(⁅J, J⁆), qM m = 1 ↔ (m : G) ∈ X ⊔ zpowers u₁ := fun m => by
    show (QuotientGroup.mk (Subgroup.inclusion hMJ m) : ↥J ⧸ Zs) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact Iff.rfl
  have hsurj : Function.Surjective qM := by
    have hle : ⁅(⊤ : Subgroup (↥J ⧸ Zs)), ⊤⁆ ≤ qM.range := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨ja, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨jb, rfl⟩ := QuotientGroup.mk_surjective b
      refine ⟨⟨⁅(ja : G), (jb : G)⁆, Subgroup.commutator_mem_commutator ja.2 jb.2⟩, ?_⟩
      exact map_commutatorElement q ja jb
    have htop : ⁅(⊤ : Subgroup (↥J ⧸ Zs)), ⊤⁆ = (⊤ : Subgroup (↥J ⧸ Zs)) := by
      rw [← _root_.commutator_def]
      exact Group.isPerfect_def.1 hYperf
    rw [htop] at hle
    exact MonoidHom.range_eq_top.1 (eq_top_iff.2 hle)
  have hdecomp : ∀ (j : G) (hj : j ∈ J), ∃ m : ↥(⁅J, J⁆), ∃ z ∈ X ⊔ zpowers u₁,
      j = (m : G) * z ∧ qM m = q ⟨j, hj⟩ := by
    intro j hj
    obtain ⟨m, hm⟩ := hsurj (q ⟨j, hj⟩)
    have h := QuotientGroup.eq.1 hm
    rw [mem_subgroupOf] at h
    exact ⟨m, (m : G)⁻¹ * j, h, by group, hm⟩
  have hMperf : ⁅(⁅J, J⁆ : Subgroup G), ⁅J, J⁆⁆ = ⁅J, J⁆ := by
    refine le_antisymm (Subgroup.commutator_mono hMJ hMJ) ?_
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨m₁, z₁, hz₁, rfl, -⟩ := hdecomp a ha
    obtain ⟨m₂, z₂, hz₂, rfl, -⟩ := hdecomp b hb
    have h1 : z₁ * ((m₂ : G) * z₂) = ((m₂ : G) * z₂) * z₁ :=
      hZc z₁ hz₁ _ (J.mul_mem (hMJ m₂.2) (hZJ hz₂))
    have h2 : z₂ * (m₁ : G) = (m₁ : G) * z₂ := hZc z₂ hz₂ _ (hMJ m₁.2)
    rw [commutatorElement_mul_central_left h1, commutatorElement_mul_central_right h2]
    exact Subgroup.commutator_mem_commutator m₁.2 m₂.2
  have hMperf' : Group.IsPerfect ↥(⁅J, J⁆) := Subgroup.isPerfect_iff.2 hMperf
  have hcenter : center ↥(⁅J, J⁆) = qM.ker := by
    ext m
    constructor
    · intro hm
      rw [MonoidHom.mem_ker]
      have : qM m ∈ center (↥J ⧸ Zs) := by
        rw [mem_center_iff]
        intro y
        obtain ⟨m', rfl⟩ := hsurj y
        rw [← map_mul, ← map_mul, mem_center_iff.1 hm m']
      rwa [center_eq_bot_of_isSporadic_hs hY, mem_bot] at this
    · intro hm
      rw [mem_center_iff]
      intro g
      have hmZ := (hqM_mem m).1 hm
      exact Subtype.ext (hZc _ hmZ g (hMJ g.2)).symm
  have hq' : IsSporadic (↥(⁅J, J⁆) ⧸ center ↥(⁅J, J⁆)) .HS := by
    obtain ⟨e⟩ := hY
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientKerEquivOfSurjective qM hsurj)).trans e⟩
  by_cases hker : qM.ker = ⊥
  · have hinj : Function.Injective qM := (MonoidHom.ker_eq_bot_iff qM).1 hker
    refine ⟨?_, ?_⟩
    · obtain ⟨e⟩ := hY
      exact ⟨(MulEquiv.ofBijective qM ⟨hinj, hsurj⟩).trans e⟩
    · rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.1⟩ : ↥(⁅J, J⁆)) ∈ qM.ker := (hqM_mem _).2 hx.2
      rw [hker, mem_bot] at this
      exact mem_bot.2 (congrArg Subtype.val this)
  · exfalso
    have hcne : center ↥(⁅J, J⁆) ≠ ⊥ := by rw [hcenter]; exact hker
    have hZ2 : Nat.card (center ↥(⁅J, J⁆)) = 2 := card_center_eq_two_of_ne_bot hMperf' hq' hcne
    obtain ⟨m₀, z, hz, hu_eq, hqm⟩ := hdecomp u huJ
    have hu2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
    have hu1 : (⟨u, huJ⟩ : ↥J) ^ 2 = 1 := Subtype.ext hu2
    have hū1 : q ⟨u, huJ⟩ ≠ 1 := fun h =>
      huZ (mem_subgroupOf.1 ((QuotientGroup.eq_one_iff (N := Zs) (⟨u, huJ⟩ : ↥J)).1 h))
    by_cases hm2 : m₀ ^ 2 = 1
    · have hcard := card_centralizer_eq_of_sq_eq_one hMperf' hZ2 hq' qM hsurj hcenter.symm hm2
        (by rw [hqm]; exact hū1)
      rw [hqm] at hcard
      have hW : Nat.card Zs ∣ 18 := by
        rw [show Nat.card Zs = Nat.card (X ⊔ zpowers u₁ : Subgroup G) from
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZJ).toEquiv]
        exact card_sup_dvd hXJ hu₁c hu₁ hX
      have h2B' : 2880 * 18 ∣ Nat.card (centralizer ({(⟨u, huJ⟩ : ↥J)} : Set ↥J)) := by
        rw [← Nat.card_congr
          { toFun := fun x : ↥(J ⊓ centralizer ({u} : Set G)) =>
              (⟨⟨x.1, x.2.1⟩, mem_centralizer_singleton_iff.2
                (Subtype.ext (mem_centralizer_singleton_iff.1 x.2.2))⟩ :
                ↥(centralizer ({(⟨u, huJ⟩ : ↥J)} : Set ↥J)))
            invFun := fun y => ⟨y.1.1, y.1.2, mem_centralizer_singleton_iff.2
              (congrArg Subtype.val (mem_centralizer_singleton_iff.1 y.2))⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }]
        exact h2B
      exact card_centralizer_quotient_ne_7680 Zs hW ⟨u, huJ⟩ h2B' hcard
    · have hnker : m₀ ^ 2 ∈ qM.ker := by
        rw [MonoidHom.mem_ker, map_pow, hqm, ← map_pow, hu1, map_one]
      have hncen : m₀ ^ 2 ∈ center ↥(⁅J, J⁆) := by rw [hcenter]; exact hnker
      have hn2 : (m₀ ^ 2) ^ 2 = 1 := by
        have h := pow_card_eq_one' (G := ↥(center ↥(⁅J, J⁆))) (x := ⟨m₀ ^ 2, hncen⟩)
        rw [hZ2] at h
        exact congrArg Subtype.val h
      have hg2 : ((m₀ : G) ^ 2) ^ 2 = 1 := by
        have := congrArg Subtype.val hn2
        simpa using this
      have hmz : (m₀ : G) ^ 2 = (z ^ 2)⁻¹ := by
        have hcomm : z * (m₀ : G) = (m₀ : G) * z := hZc z hz _ (hMJ m₀.2)
        have h1 : u * u = 1 := by rw [← pow_two]; exact hu2
        rw [hu_eq] at h1
        have h3 : (m₀ : G) ^ 2 * z ^ 2 = 1 := by
          calc (m₀ : G) ^ 2 * z ^ 2 = (m₀ : G) * ((m₀ : G) * z) * z := by
                simp only [pow_two, mul_assoc]
            _ = (m₀ : G) * (z * (m₀ : G)) * z := by rw [hcomm]
            _ = (m₀ : G) * z * ((m₀ : G) * z) := by simp only [mul_assoc]
            _ = 1 := h1
        exact eq_inv_of_mul_eq_one_left h3
      have hgX : (m₀ : G) ^ 2 ∈ X := by
        rw [hmz]
        exact X.inv_mem (sq_mem_of_mem_sup hXJ hu₁c hu₁ hz)
      have h9 : ((m₀ : G) ^ 2) ^ 9 = 1 := by
        have h := pow_card_eq_one' (G := ↥X) (x := ⟨(m₀ : G) ^ 2, hgX⟩)
        rw [hX] at h
        exact congrArg Subtype.val h
      have hg1 : (m₀ : G) ^ 2 = 1 := by
        calc (m₀ : G) ^ 2 = (((m₀ : G) ^ 2) ^ 2) ^ 4 * (m₀ : G) ^ 2 := by
              rw [hg2, one_pow, one_mul]
          _ = ((m₀ : G) ^ 2) ^ 9 := by rw [← pow_mul, ← pow_succ]
          _ = 1 := h9
      exact hm2 (Subtype.ext hg1)

end Main

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
