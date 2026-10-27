module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransfer
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open CFSG.Open CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

theorem map_member_le_wSup {M X I : Subgroup G} (hX : X ≤ M) (hI : I ∈ cZero X) :
    (I.subgroupOf X).map (hatHom M X hX) ≤
      wSup (↥(barM M X) ⧸ CFSG.pCore 2 ↥(barM M X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hIX : I ≤ X := hI.le
  set T := (I.subgroupOf X).map (hatHom M X hX) with hT
  have hTs : IsSubnormal T ⊤ := by
    have h1 : IsSubnormal (I.subgroupOf X) ⊤ :=
      IsSubnormal.of_mathlib ((IsSubnormal.iff_subgroupOf hIX).mp hI.subnormal)
    have h2 := h1.map (hatHom M X hX)
    rwa [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (hatHom_surjective M X hX)] at h2
  have hTO := CZeroLift.pCore_eq_bot_of_isSubnormal hTs (pCore_hat_eq_bot M X)
  obtain ⟨hpI, ⟨e⟩⟩ := CZeroLift.pCore_eq_and_equiv (hatHom M X hX) hIX
    (isPGroup_ker_hatHom M X hX) hTO
  refine le_iSup₂ (f := fun T (_ : T ∈ {T : Subgroup (↥(barM M X) ⧸ CFSG.pCore 2 ↥(barM M X)) |
    IsSubnormal T ⊤ ∧ (IsComponentOf T ⊤ ∨ IsSymThreeOrSUThreeTwo ↥T)}) => T) T ⟨hTs, ?_⟩
  rcases hI.shape with hc | ⟨-, hb⟩
  · left
    refine ⟨le_top, hTs, ?_⟩
    have hq := hc.component.2.2
    have htop : barM I I = ⊤ := by
      rw [barM, subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
      exact QuotientGroup.mk'_surjective _
    rw [htop] at hq
    exact CFSG.Open.IsQuasisimple.of_mulEquiv (e.symm.trans Subgroup.topEquiv.symm) hq
  · right
    exact IsSymThreeOrSUThreeTwo.of_mulEquiv e hb

theorem map_jZero_eq_wSup (M H L : Subgroup G) (hX : H ⊓ L ≤ M) :
    ((jZero H L).subgroupOf (H ⊓ L)).map (hatHom M (H ⊓ L) hX) =
      wSup (↥(barM M (H ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM M (H ⊓ L))) := by
  refine le_antisymm ?_ (wSup_le_map_jZero M H L hX)
  rw [map_le_iff_le_comap]
  set W' : Subgroup G := ((wSup (↥(barM M (H ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM M (H ⊓ L)))).comap
    (hatHom M (H ⊓ L) hX)).map (H ⊓ L).subtype with hW'
  have hJ : jZero H L ≤ W' := by
    refine iSup₂_le fun I hI => ?_
    intro x hx
    have hxX : x ∈ H ⊓ L := hI.le hx
    exact ⟨⟨x, hxX⟩, map_member_le_wSup hX hI ⟨⟨x, hxX⟩, hx, rfl⟩, rfl⟩
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hJ hx
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy

theorem not_two_dvd_relIndex_map {M H L T : Subgroup G} (hX : H ⊓ L ≤ M) (hTJ : T ≤ jZero H L)
    (hT : ¬ 2 ∣ T.relIndex (jZero H L)) :
    ¬ 2 ∣ ((T.subgroupOf (H ⊓ L)).map (hatHom M (H ⊓ L) hX)).relIndex
      (wSup (↥(barM M (H ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM M (H ⊓ L)))) := by
  rw [← map_jZero_eq_wSup M H L hX, ← relIndex_comap]
  intro h2
  apply hT
  have h1 := relIndex_dvd_of_le_left ((jZero H L).subgroupOf (H ⊓ L))
    (le_comap_map (hatHom M (H ⊓ L) hX) (T.subgroupOf (H ⊓ L)))
  rw [relIndex_subgroupOf (jZero_le H L)] at h1
  exact h2.trans h1

theorem exists_nontrivial_of_not_commutator {M H L : Subgroup G} (hX : H ⊓ L ≤ M) {b : G}
    (hb : b ∈ M) (hbX : b ∈ normalizer ((H ⊓ L : Subgroup G) : Set G)) {x : G}
    (hx : x ∈ jZero H L) (hbx : b * x * b⁻¹ * x⁻¹ ∉ pCoreOf 2 (jZero H L)) :
    ∃ w, ∃ hw : w ∈ barM M (H ⊓ L),
      QuotientGroup.mk' (CFSG.pCore 2 ↥(barM M (H ⊓ L))) ⟨w, hw⟩ ∈
        wSup (↥(barM M (H ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM M (H ⊓ L))) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩ * w *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩)⁻¹ * w⁻¹ ∉ pCoreOf 2 (barM M (H ⊓ L)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxX : x ∈ H ⊓ L := jZero_le H L hx
  set u : ↥(H ⊓ L) := ⟨x, hxX⟩
  refine ⟨(barHom M (H ⊓ L) hX u : ↥(barM M (H ⊓ L))), (barHom M (H ⊓ L) hX u).2, ?_, ?_⟩
  · rw [← map_jZero_eq_wSup M H L hX]
    exact ⟨u, hx, rfl⟩
  · intro hmem
    have hbJ : b ∈ normalizer (jZero H L : Set G) := le_normalizer_jZero H L hbX
    have hcJ : b * x * b⁻¹ * x⁻¹ ∈ jZero H L :=
      mul_mem ((mem_normalizer_iff.mp hbJ x).mp hx) (inv_mem hx)
    have hcX : b * x * b⁻¹ * x⁻¹ ∈ H ⊓ L := jZero_le H L hcJ
    have hcomm : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩ *
        ((barHom M (H ⊓ L) hX u : ↥(barM M (H ⊓ L))) : ↥M ⧸ CFSG.pCore 2 ↥M) *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩)⁻¹ *
        ((barHom M (H ⊓ L) hX u : ↥(barM M (H ⊓ L))) : ↥M ⧸ CFSG.pCore 2 ↥M)⁻¹ =
        ((barHom M (H ⊓ L) hX ⟨_, hcX⟩ : ↥(barM M (H ⊓ L))) : ↥M ⧸ CFSG.pCore 2 ↥M) := by
      rw [coe_barHom, coe_barHom]
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    rw [hcomm] at hmem
    have hker : (⟨_, hcX⟩ : ↥(H ⊓ L)) ∈ (hatHom M (H ⊓ L) hX).ker := by
      rw [MonoidHom.mem_ker, hatHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      obtain ⟨y, hy, hyc⟩ := hmem
      have : y = barHom M (H ⊓ L) hX ⟨_, hcX⟩ := Subtype.ext hyc
      rwa [← this]
    have hcO : b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (H ⊓ L) := by
      rw [pCoreOf_eq_map_ker M (H ⊓ L) hX]
      exact ⟨_, hker, rfl⟩
    have hle : jZero H L ⊓ pCoreOf 2 (H ⊓ L) ≤ pCoreOf 2 (jZero H L) := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left (fun j hj => ?_)
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
      rw [mem_normalizer_iff]
      intro y
      have h1 := mem_normalizer_iff.mp (le_normalizer hj : j ∈ normalizer (jZero H L : Set G)) y
      have h2 := mem_normalizer_iff.mp (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2
        (H ⊓ L) (le_normalizer (jZero_le H L hj))) y
      exact ⟨fun hy => ⟨h1.mp hy.1, h2.mp hy.2⟩, fun hy => ⟨h1.mpr hy.1, h2.mpr hy.2⟩⟩
    exact hbx (hle ⟨hcJ, hcO⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
