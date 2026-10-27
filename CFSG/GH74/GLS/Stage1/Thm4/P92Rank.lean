module

public import CFSG.GH74.GLS.Stage1.Thm4.P92Basic
public import CFSG.GH74.GLS.IVK.Lifted.Alt51g
public import CFSG.GH74.GLS.Stage1.Thm4.L96Sylow
public import CFSG.GH74.GLS.Stage1.Thm4.Alt51Q1

public section

namespace CFSG.GH74.GLS.Stage1.Thm4.P92

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.ABGLocalTools
open scoped commutatorElement

theorem exists_E16 {Lh : Type} [Group Lh] [Finite Lh] {n : ℕ} (hn : 8 ≤ n) (hL : IsDoubleCoverOfAlt Lh n) :
    ∃ E : Subgroup Lh, (∀ a ∈ E, a * a = 1) ∧ Nat.card E = 2 ^ 4 := by
  obtain ⟨π, hπ, -⟩ := L97.exists_twoCover hL
  obtain ⟨R, hRcard, hR⟩ := IVK.Lifted.exists_subgroup_eight_cycleType_two_four hn
  have hcard : Nat.card (R.comap π) = 2 ^ 4 := by
    rw [IVK.Lifted.card_comap_of_surjective_two hπ.surj, hRcard, hπ.card_ker]
    norm_num
  refine ⟨R.comap π, fun x hx => ?_, hcard⟩
  have : x ^ 2 = 1 := by
    by_cases h1 : π x = 1
    · exact hπ.sq_eq_one_of_mem_ker' (MonoidHom.mem_ker.2 h1)
    · exact hπ.sq_eq_one_of_cycleType_two_two_two_two hn (hR _ hx h1)
  rwa [sq] at this

section A4n

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_le_sylow {K P E : Subgroup G} (hP : IsSylowOf 2 P K) (hEK : E ≤ K)
    (hE : IsPGroup 2 ↥E) : ∃ k ∈ K, ∀ x ∈ E, k * x * k⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE' : IsPGroup 2 ↥(E.subgroupOf K) := hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEK).symm
  obtain ⟨Q, hQ⟩ := hE'.exists_le_sylow
  have hQK : IsSylowOf 2 ((Q : Subgroup ↥K).map K.subtype) K := ⟨Q, rfl⟩
  obtain ⟨k, hk, hconj⟩ := hQK.exists_mem_conj hP
  refine ⟨k, hk, fun x hx => ?_⟩
  rw [hconj]
  have : k⁻¹ * (k * x * k⁻¹) * k = x := by group
  rw [this]
  exact ⟨⟨x, hEK hx⟩, hQ hx, rfl⟩

theorem mem_of_rank {E : Subgroup G} {r : ℕ} (hrk : pRank 2 G ≤ 4) (hE2 : ∀ a ∈ E, a * a = 1)
    (hcard : Nat.card E = 2 ^ r) (hr : 4 ≤ r) {y : G} (hy : y * y = 1)
    (hyE : ∀ a ∈ E, y * a = a * y) : y ∈ E := by
  by_contra hyn
  have hy1 : y ≠ 1 := fun h => hyn (h ▸ E.one_mem)
  have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy) hy1
  have hQ2 : ∀ x ∈ zpowers y, x * x = 1 := by
    intro x hx
    rcases mem_zpowers_involution hy hx with rfl | rfl
    · exact one_mul 1
    · exact hy
  have hQcard : Nat.card (zpowers y) = 2 ^ 1 := by
    rw [Nat.card_zpowers, hyo]; norm_num
  have hcent : E ≤ centralizer ((zpowers y : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left (show Commute y a from hyE a ha) j)).eq.symm ▸ rfl
  have hdisj : Disjoint E (zpowers y) := by
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxE, hxQ⟩
    rcases mem_zpowers_involution hy hxQ with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hxE hyn
  obtain ⟨R, -, -, hR, hRc, -⟩ :=
    CFSG.LargeEvenClassification.Helpers.commuting_disjoint_elementary_product
      (prime := 2) (firstRank := r) (secondRank := 1) E (zpowers y)
      (L97.isElemAbelian_of_sq E hE2) (L97.isElemAbelian_of_sq _ hQ2) hcard hQcard hcent hdisj
  have h5 : r + 1 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup G) :=
    CFSG.SectionRank.le_pRank one_lt_two le_top hR hRc
  have hG : CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ 4 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]; exact hrk
  omega

theorem a4n {Lh : Type} [Group Lh] {n : ℕ} (hrk : pRank 2 G ≤ 4) (hn8 : 8 ≤ n) (hn11 : n ≤ 11)
    (hL : IsDoubleCoverOfAlt Lh n) {K : Subgroup G} (e : HatT K ≃* Lh) {P : Subgroup G}
    (hP : IsSylowOf 2 P K) {y : G} (hy : y * y = 1) (hyP : ∀ p ∈ P, y * p = p * y) :
    y ∈ P ∧ y ∈ zStar K := by
  have : Finite Lh := Finite.of_equiv (HatT K) e.toEquiv
  obtain ⟨E, hE2, hEc⟩ := exists_E16 hn8 hL
  let E₁ : Subgroup (HatT K) := E.map e.symm.toMonoidHom
  have hE₁2 : ∀ a ∈ E₁, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, hE2 a ha, map_one]
  have hE₁card : Nat.card E₁ = 2 ^ 4 := by
    rw [Subgroup.card_map_of_injective e.symm.injective]; exact hEc
  have hrange : E₁ ≤ (hatMk K).range := by
    rw [MonoidHom.range_eq_top.mpr (hatMk_surjective K)]; exact le_top
  obtain ⟨E', hE'c, hE'2, hE'card⟩ := L96.exists_elemAbelian_of_odd_kernel (hatMk K)
    (odd_card_ker_hatMk K) E₁ hrange (comm_of_sq hE₁2) (fun a ha => by rw [sq]; exact hE₁2 a ha)
  have hE'sq : ∀ a ∈ E', a * a = 1 := fun a ha => by rw [← sq]; exact hE'2 a ha
  let E'' : Subgroup G := E'.map K.subtype
  have hE''K : E'' ≤ K := Subgroup.map_subtype_le _
  have hE''2 : ∀ a ∈ E'', a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (hE'sq a ha)
  have hE''card : Nat.card E'' = Nat.card E' := Subgroup.card_map_of_injective K.subtype_injective
  have hE''p : IsPGroup 2 ↥E'' := isPGroup_two_of_sq hE''2
  obtain ⟨k, hkK, hk⟩ := exists_conj_le_sylow hP hE''K hE''p
  let E₂ : Subgroup G := E''.map (MulAut.conj k).toMonoidHom
  have hE₂P : E₂ ≤ P := by
    rintro _ ⟨a, ha, rfl⟩
    exact hk a ha
  have hE₂2 : ∀ a ∈ E₂, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, hE''2 a ha, map_one]
  have hE₂card : Nat.card E₂ = Nat.card E'' :=
    Subgroup.card_map_of_injective (MulAut.conj k).injective
  have hE₂p : IsPGroup 2 ↥E₂ := isPGroup_two_of_sq hE₂2
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hE₂p
  have hr4 : 4 ≤ r := by
    have h1 : 2 ^ 4 ≤ 2 ^ r := by
      rw [← hr, hE₂card, hE''card, ← hE₁card]; exact hE'card
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have hyE : ∀ a ∈ E₂, y * a = a * y := fun a ha => hyP a (hE₂P ha)
  have hyE₂ : y ∈ E₂ := mem_of_rank hrk hE₂2 hr hr4 hy hyE
  have hyP' : y ∈ P := hE₂P hyE₂
  have hyK : y ∈ K := hP.le hyP'
  have hH : Hyp5B (HatT K) ⊤ n :=
    ⟨inferInstance, hn8, hn11, isDoubleCoverOfAlt_congr (Subgroup.topEquiv.trans e).symm hL,
      fun h _ => Subgroup.mem_top h⟩
  have hSyl : IsSylowOf 2 (hatImg K P) ⊤ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isSylowOf_iff.2 (isSylow2In_hatImg (isSylowOf_iff.1 hP))
  have hw : hatMk K ⟨y, hyK⟩ ∈ hatImg K P := mem_hatImg.mpr ⟨⟨y, hyK⟩, hyP', rfl⟩
  have hwc : ∀ s ∈ hatImg K P, s * hatMk K ⟨y, hyK⟩ = hatMk K ⟨y, hyK⟩ * s := by
    intro s hs
    obtain ⟨a, ha, rfl⟩ := mem_hatImg.mp hs
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hyP a ha).symm
  obtain ⟨-, hcen⟩ := IVK.Lifted.ivk_5_1g (HatT K) ⊤ n hH (hatImg K P) hSyl _ hw hwc
  have hcenter : hatMk K ⟨y, hyK⟩ ∈ center (HatT K) :=
    Subgroup.mem_center_iff.2 fun g => hcen g (Subgroup.mem_top g)
  exact ⟨hyP', (Alt51.mem_zStar_iff_hat_mem_center ⟨y, hyK⟩).2 hcenter⟩

end A4n

end CFSG.GH74.GLS.Stage1.Thm4.P92
