module

public import CFSG.GH74.Uniqueness.Section123
public import CFSG.GH74.Uniqueness.Section1214
public import CFSG.GH74.Uniqueness.Section12BenderDict

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.zHull_eq_L_or_unitary
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n i : ℕ}
    (h : LData c n i) {F : Subgroup X} (hLF : c.L ≤ F) (hF : F ≠ ⊤) :
    zHull Z F = c.L ∨ (i = 1 ∧ ∃ e, BenderSub Z M (zHull Z F) n 3 e) := by
  have hZ := S.invariant
  have hLv : c.L ≤ zHull Z F := by
    calc c.L = zHull Z c.L := (IsProductDisconnected.zHull_lSubgroup S.invariant c.ht c.hz M).symm
      _ ≤ zHull Z F := closure_mono fun x hx => ⟨hx.1, hLF hx.2⟩
  by_cases heq : zHull Z F = c.L
  · exact Or.inl heq
  right
  have hFM : ¬ F ≤ M := fun hle => c.htM (hle (hLF c.t_mem_L))
  have hne : (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).Nonempty :=
    ⟨c.z, c.hz, mem_inf.mpr ⟨hLF c.z_mem_L, c.hzM⟩⟩
  have hns : ¬ Group.IsSolvable ↥(zHull Z F) := by
    intro hsol
    have : IsSimpleGroup ↥c.L := h.bender.isSimple
    have hLsol : Group.IsSolvable ↥c.L :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLv)
        (Subgroup.inclusion_injective hLv)
    exact h.bender.isSimpleBenderGroup.not_commutative
      ((IsSimpleGroup.comm_iff_isSolvable (G := ↥c.L)).mpr hLsol)
  obtain ⟨n', i', e', hB⟩ := S.benderSub_exists hF hFM hne hns
  have hZM : Z ∩ ((zHull Z F ⊓ M : Subgroup X) : Set X) = Z ∩ (M : Set X) := by
    ext x
    constructor
    · rintro ⟨hxZ, hxLM⟩
      exact ⟨hxZ, (mem_inf.mp hxLM).2⟩
    · rintro ⟨hxZ, hxM⟩
      refine ⟨hxZ, mem_inf.mpr ⟨hLv ?_, hxM⟩⟩
      exact IsProductDisconnected.inter_le_lSubgroup hZ S.prodDisc c.ht c.htM c.hz c.hzM ⟨hxZ, hxM⟩
  have hn : n' = n := by
    have h1 := A2.ncard_inter_of_benderSub S hB
    rw [hZM, A2.ncard_zM h] at h1
    have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h3 : 1 ≤ 2 ^ n' := Nat.one_le_two_pow
    exact Nat.pow_right_injective le_rfl (by omega : 2 ^ n' = 2 ^ n)
  subst n'
  have hcL : center ↥c.L = ⊥ := h.center_eq_bot
  let ι : ↥c.L →* ↥(zHull Z F) ⧸ center ↥(zHull Z F) :=
    (QuotientGroup.mk' (center ↥(zHull Z F))).comp (Subgroup.inclusion hLv)
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have hmem : Subgroup.inclusion hLv l ∈ center ↥(zHull Z F) :=
      (QuotientGroup.eq_one_iff _).mp hl
    have hlc : l ∈ center ↥c.L := by
      rw [mem_center_iff]
      intro g
      apply Subtype.ext
      have h1 := congrArg Subtype.val (mem_center_iff.mp hmem (Subgroup.inclusion hLv g))
      exact h1
    rw [hcL, mem_bot] at hlc
    exact hlc
  rcases Bender.BenderType.embedding_index h.bender hB.bender ι hιinj with hii | ⟨hi1, hi3⟩
  · exfalso
    apply heq
    subst hii
    have he' : e' = 1 := by
      rcases hB.bender.cases' with ⟨-, he, -⟩ | ⟨-, he, -⟩ | ⟨hi3, -, -⟩
      · exact he
      · exact he
      · rcases h.hi with h1 | h1 <;> omega
    subst he'
    have hcard : Nat.card (↥(zHull Z F) ⧸ center ↥(zHull Z F)) ≤ Nat.card ↥c.L := by
      rw [h.bender.card_eq, hB.bender.card_eq]
    have hsurj : Function.Surjective ι := (hιinj.bijective_of_nat_card_le hcard).2
    have hodd := A2.odd_card_center_of_benderSub hB
    refine le_antisymm ((closure_le _).mpr ?_) hLv
    rintro s ⟨hsZ, hsC⟩
    have hsF : s ∈ zHull Z F := subset_closure ⟨hsZ, hsC⟩
    obtain ⟨l, hl⟩ := hsurj (QuotientGroup.mk' (center ↥(zHull Z F)) ⟨s, hsF⟩)
    have hc : (Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩ ∈ center ↥(zHull Z F) :=
      QuotientGroup.eq.mp hl
    have hss : (⟨s, hsF⟩ : ↥(zHull Z F)) * ⟨s, hsF⟩ = 1 :=
      Subtype.ext (hZ.mul_self_eq_one hsZ)
    have hbo : (⟨s, hsF⟩ : ↥(zHull Z F)) = Subgroup.inclusion hLv l *
        ((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩) := by
      rw [mul_inv_cancel_left]
    have hoa : Subgroup.inclusion hLv l * ((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩) =
        ((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩) * Subgroup.inclusion hLv l :=
      mem_center_iff.mp hc _
    have h1 : (Subgroup.inclusion hLv l * Subgroup.inclusion hLv l) *
        (((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩) * ((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩)) =
          1 := by
      rw [← hss]
      conv_rhs => rw [hbo]
      calc (Subgroup.inclusion hLv l * Subgroup.inclusion hLv l) *
            (((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩) * ((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩))
          = Subgroup.inclusion hLv l * (Subgroup.inclusion hLv l *
              ((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩)) *
              ((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩) := by group
        _ = Subgroup.inclusion hLv l * (((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩) *
              Subgroup.inclusion hLv l) * ((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩) := by
            rw [hoa]
        _ = (Subgroup.inclusion hLv l * ((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩)) *
              (Subgroup.inclusion hLv l * ((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩)) := by group
    have haa : Subgroup.inclusion hLv l * Subgroup.inclusion hLv l ∈ center ↥(zHull Z F) := by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact (center _).inv_mem ((center _).mul_mem hc hc)
    have hll : l * l = 1 := by
      apply hιinj
      rw [map_mul, map_one]
      change QuotientGroup.mk' (center ↥(zHull Z F)) (Subgroup.inclusion hLv l) *
        QuotientGroup.mk' (center ↥(zHull Z F)) (Subgroup.inclusion hLv l) = 1
      rw [← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr haa
    have haa1 : Subgroup.inclusion hLv l * Subgroup.inclusion hLv l = 1 := by
      rw [← map_mul, hll, map_one]
    rw [haa1, one_mul] at h1
    have ho1 := eq_one_of_mem_of_sq_eq_one hodd hc h1
    have hsl : (⟨s, hsF⟩ : ↥(zHull Z F)) = Subgroup.inclusion hLv l := by
      rw [hbo, ho1, mul_one]
    have hsl' : s = (l : X) := congrArg Subtype.val hsl
    rw [SetLike.mem_coe, hsl']
    exact l.2
  · exact ⟨hi1, e', hi3 ▸ hB⟩

omit [Finite X] in
theorem conjugate_fixed_of_normalizes {Y F : Subgroup X} (hYM : Y ≤ M)
    (hFY : F ≤ normalizer (Y : Set X)) {y : X} (hy : y ∈ Y) {f : X} (hf : f ∈ F)
    (hM : ∀ g ∈ M, conjugate M g = M) :
    conjugate (conjugate M f) y = conjugate M f := by
  have hfy : f * y * f⁻¹ ∈ Y := (mem_normalizer_iff.mp (hFY hf) y).mp hy
  rw [conjugate_conjugate]
  have e : f * y = (f * y * f⁻¹) * f := by group
  rw [e, ← conjugate_conjugate, hM _ (hYM hfy)]

theorem ZDSetup.normalizer_le_normalizer_L
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n : ℕ}
    (h : LData c n 1) (hΩ : (omega M).ncard = (2 ^ n) ^ 3 + 1) {Y : Subgroup X}
    (hYJ : Y ≤ centralizer (c.L : Set X)) (hY : Y ≠ ⊥) :
    normalizer (Y : Set X) ≤ normalizer (c.L : Set X) := by
  set N : Subgroup X := normalizer (Y : Set X) with hN
  have hYM : Y ≤ M := fun y hy => (mem_inf.mp (h.centralizer_le (hYJ hy))).1
  have hLN : c.L ≤ N := by
    intro l hl
    rw [hN, mem_normalizer_iff]
    intro y
    have hyl : ∀ y ∈ Y, l * y * l⁻¹ = y := fun y hy => by
      rw [mem_centralizer_iff.mp (hYJ hy) l hl, mul_inv_cancel_right]
    constructor
    · intro hy
      rw [hyl y hy]
      exact hy
    · intro hy
      have h1 := hyl _ hy
      have h3 : l⁻¹ * (l * y * l⁻¹) * l = l * y * l⁻¹ := by
        calc l⁻¹ * (l * y * l⁻¹) * l = l⁻¹ * (l * (l * y * l⁻¹) * l⁻¹) * l := by rw [h1]
          _ = l * y * l⁻¹ := by group
      have h4 : y = l * y * l⁻¹ := by
        rw [← h3]
        group
      rw [h4]
      exact hy
  have hNtop : N ≠ ⊤ := by
    intro htop
    have hsimp : IsSimpleGroup X := S.theorem1_unconditional.1
    have hYn : Y.Normal := by
      rw [← normalizer_eq_top_iff]
      exact htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y with hb | ht
    · exact hY hb
    · exact S.prodDisc.1 (top_le_iff.mp (ht ▸ hYM))
  have hM : ∀ g ∈ M, conjugate M g = M := fun g hg =>
    (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr hg
  rcases S.zHull_eq_L_or_unitary h hLN hNtop with heq | ⟨-, e, hB⟩
  · calc N ≤ normalizer (zHull Z N : Set X) := le_normalizer_zHull S.invariant N
      _ = normalizer (c.L : Set X) := by rw [heq]
  · exfalso
    apply hY
    rw [eq_bot_iff]
    intro y hy
    rw [mem_bot]
    have hidx := hB.index_eq S
    have horb := S.ncard_alphaOrbit (zHull Z N)
    have hsub : alphaOrbit M (zHull Z N) ⊆ omega M := by
      rintro _ ⟨f, -, rfl⟩
      exact ⟨f, rfl⟩
    have heqΩ : alphaOrbit M (zHull Z N) = omega M :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [horb, hidx, hΩ]) (Set.toFinite _)
    apply S.eq_one_of_fixes_omega
    intro β hβ
    rw [← heqΩ] at hβ
    obtain ⟨f, hf, rfl⟩ := hβ
    exact conjugate_fixed_of_normalizes hYM (Cor713.zHull_le N) hy hf hM

end CFSG.GH74.Uniqueness
