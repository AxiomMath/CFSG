module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairF4Theta
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.BlockSp
public import CFSG.ClassicalInvolution.Q3.Q3VF4CNodes
public import CFSG.ClassicalInvolution.Q3.Q3VCollCert
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCover

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit

section GroupTheory

theorem exists_central_preimage_of_commute_range {S G : Type} [Group S] [Group G]
    [Group.IsPerfect S] (Ψ : S →* G) (hker : Ψ.ker ≤ Subgroup.center S) {d : G}
    (hd : d ∈ Ψ.range) (hcomm : ∀ x ∈ Ψ.range, x * d = d * x) :
    ∃ y ∈ Subgroup.center S, Ψ y = d := by
  obtain ⟨y, rfl⟩ := hd
  refine ⟨y, ?_, rfl⟩
  have hc : (y : S ⧸ Subgroup.center S) ∈ Subgroup.center (S ⧸ Subgroup.center S) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, hcomm (Ψ s) ⟨s, rfl⟩,
      inv_mul_cancel]
  rw [Group.IsPerfect.center_quotient_center_eq_bot, Subgroup.mem_bot] at hc
  exact (QuotientGroup.eq_one_iff y).1 hc

theorem orderOf_and_injective_of_center_card_two {S G : Type} [Group S] [Group G]
    (Ψ : S →* G) (hker : Ψ.ker ≤ Subgroup.center S) (hcard : Nat.card ↥(Subgroup.center S) = 2)
    {y : S} (hy : y ∈ Subgroup.center S) (hy1 : Ψ y ≠ 1) :
    orderOf y = 2 ∧ Function.Injective Ψ := by
  have hne : (⟨y, hy⟩ : ↥(Subgroup.center S)) ≠ 1 := fun h => hy1 (by
    have : y = 1 := congrArg Subtype.val h
    rw [this, map_one])
  refine ⟨?_, ?_⟩
  · have hdvd := orderOf_dvd_natCard (⟨y, hy⟩ : ↥(Subgroup.center S))
    rw [hcard] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.1 h1) hne
    · rwa [Subgroup.orderOf_mk] at h2
  · rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : z ∈ Subgroup.center S := hker hz
    by_contra hz1
    have hzne : (⟨z, hzc⟩ : ↥(Subgroup.center S)) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
    obtain ⟨w, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(Subgroup.center S))).1 hcard
    have : (⟨z, hzc⟩ : ↥(Subgroup.center S)) = ⟨y, hy⟩ := (huniq _ hzne).trans (huniq _ hne).symm
    have hzy : z = y := congrArg Subtype.val this
    exact hy1 (hzy ▸ hz)

end GroupTheory

section Pair

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.ModelFacts.Levi
  CFSG.StandardType.RootCentExc


theorem hasCleanFullClassBMember_of_lieModel_f4
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {Q : Type} [Group Q]
    [Finite Q] [IsSimpleGroup Q] (h : CFSG.Blueprint.LieModel Q .F4 0 3 1) :
    HasCleanFullClassBMember Q := by
  have hK3 : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]
    norm_num
  have hF : ringChar (GaloisField 3 1) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 1) 3]
    norm_num
  obtain ⟨α, hα, hαk⟩ : ∃ α : ↥(adjointGroup .F4 (GaloisField 3 1)) →* Q,
      Function.Surjective α ∧
        α.ker ≤ Subgroup.center ↥(adjointGroup .F4 (GaloisField 3 1)) :=
    Upgrade.lieModelCentralCover .F4 0 3 1 Nat.prime_three (by norm_num) trivial
      ⟨Nat.prime_three, le_rfl, rfl⟩ Q h
  obtain ⟨Ψ, hker, hrange, -⟩ := Q3V.exists_psi_C3_F4_three Q3V.v6Collapse_proved
  have hX := blockData_statedSp hGA hK3 (by norm_num : 2 ≤ 3)
  haveI : Group.IsPerfect ↥(StatedSp 3 (GaloisField 3 1)) := hX.quasisimple.1
  obtain ⟨d, hdmat, hd1, hdmem, hdcomm⟩ := exists_dtheta_f4 (F := GaloisField 3 1) hF
  have hN : Ψ.range.map (adjointGroup .F4 (GaloisField 3 1)).subtype =
      Subgroup.closure (leviGens .F4 (GaloisField 3 1) JF4) := by
    rw [hrange]
    exact f4_map_subtype_layer
  have hdr : d ∈ Ψ.range := by
    have h1 : (d : ModGL .F4 (GaloisField 3 1)) ∈
        Ψ.range.map (adjointGroup .F4 (GaloisField 3 1)).subtype := by
      rw [hN]
      exact hdmem
    obtain ⟨y, hy, hyd⟩ := h1
    have : y = d := Subtype.ext hyd
    rwa [← this]
  have hcomm : ∀ x ∈ Ψ.range, x * d = d * x := by
    intro x hx
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    apply hdcomm
    rw [← hN]
    exact ⟨x, hx, rfl⟩
  obtain ⟨y, hyc, hyd⟩ := exists_central_preimage_of_commute_range Ψ hker hdr hcomm
  obtain ⟨hord, hΨinj⟩ := orderOf_and_injective_of_center_card_two Ψ hker
    (card_center_statedSp_three hK3 (by norm_num)) hyc (by rw [hyd]; exact hd1)
  have hαinj : Function.Injective α := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hz' := hαk hz
    rw [center_adjointGroup_eq_bot] at hz'
    exact Subgroup.mem_bot.1 hz'
  have hnorm := f4_normal_c3_centralizer hF Ψ.range hN (Ψ y) (by rw [hyd, hdmat])
  exact hasCleanFullClassBMember_of_block α hα hαk Ψ (hαinj.comp hΨinj) hord hyc hnorm hX

end Pair

end CFSG.OddStandard.HigherRank.F3
