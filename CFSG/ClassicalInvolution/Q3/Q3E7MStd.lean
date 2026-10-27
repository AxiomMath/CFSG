module

public import CFSG.ClassicalInvolution.Q3.Q3WAEDict
public import CFSG.ClassicalInvolution.Q3.Q3WLift
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclFrame
public import CFSG.ClassicalInvolution.Q3.Q3WADict
public import CFSG.ClassicalInvolution.Q3.Q3WMain

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.E7Model
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false


local notation "M₇" => E7sc 3 1
local notation "D₇" => e7Datum (GaloisField 3 1)

section Standard

theorem yData3_E7' : YData3 .E7 0 := yData3_E7 ⟨Nat.prime_three, le_rfl, rfl⟩

theorem std_mem_fund3 {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    stdRankOne D₇ γ ∈ Generic.fundamentalSubgroups .E7 D₇ := by
  have hadm : StatedLieAdmissible .E7 0 3 1 := ⟨Nat.prime_three, le_rfl, rfl⟩
  have hlong := isLongestRoot_single .E7 0 3 1 Nat.prime_three trivial hadm
  have hγlong : Generic.IsLongestRoot D₇ γ :=
    isLongestRoot_of_mem_roots_of_forall_single _ rfl (fun k => hlong k trivial)
      ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField 3 1)).2 hγ)
  exact ⟨1, γ, Or.inl hγlong, (conjSub_one _).symm⟩

theorem no_central_fund3 {R : Subgroup M₇} (hR : R ∈ Generic.fundamentalSubgroups .E7 D₇) {r : M₇}
    (hr : r ∈ R) (hrc : r ∈ Subgroup.center M₇) : r = 1 :=
  yData3_E7'.central R hR r hr hrc

theorem pow3_fund3 {R : Subgroup M₇} (hR : R ∈ Generic.fundamentalSubgroups .E7 D₇) : Pow3 R :=
  yData3_E7'.pow3 R hR

theorem cop_ker3 : ∀ n ∈ (εm (GaloisField 3 1)).ker, ¬ 3 ∣ orderOf n :=
  fun n hn => yData3_E7'.cop n (εm_ker_le_center hn)

theorem commutes_std3 {α β : Fin (Tag.rank .E7) → ℤ} (hα : IsRoot .E7 α) (hβ : IsRoot .E7 β)
    (h : iform α β = 0) : Commutes (stdRankOne D₇ α) (stdRankOne D₇ β) := by
  have hc : ∀ a ∈ rootRankOneGroup .E7 (GaloisField 3 1) α,
      ∀ b ∈ rootRankOneGroup .E7 (GaloisField 3 1) β, a * b = b * a :=
    (isLongRoot_of_isRoot_of_simplyLaced (Or.inr (Or.inl rfl)) hα).commute_rootRankOneGroup hβ h
  refine commutes_of_map_commute_exponent3 (εm (GaloisField 3 1)) εm_ker_le_center cop_ker3
    (A := stdRankOne D₇ α) (L := stdRankOne D₇ β) (pow3_fund3 (std_mem_fund3 hβ))
    (fun a ha l hl => ?_)
  have hεa : εm (GaloisField 3 1) a ∈ rootRankOneGroup .E7 (GaloisField 3 1) α := by
    rw [← map_stdRankOne_εm hα]
    exact Subgroup.mem_map_of_mem _ ha
  have hεl : εm (GaloisField 3 1) l ∈ rootRankOneGroup .E7 (GaloisField 3 1) β := by
    rw [← map_stdRankOne_εm hβ]
    exact Subgroup.mem_map_of_mem _ hl
  exact hc _ hεa _ hεl

theorem exists_involution_std3 {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    ∃ r ∈ stdRankOne D₇ γ, orderOf r = 2 := by
  have hF : ringChar (GaloisField 3 1) ≠ 2 := ringChar_galoisField_ne_two (by norm_num)
  have hγF := std_mem_fund3 hγ
  have hmem : rootTorusSL2 .E7 (GaloisField 3 1) γ (-1) ∈
      (stdRankOne D₇ γ).map (εm (GaloisField 3 1)) := by
    rw [map_stdRankOne_εm hγ]
    exact ⟨HSL (-1), rfl⟩
  obtain ⟨r, hr, hεr⟩ := Subgroup.mem_map.1 hmem
  have hr2 : r * r = 1 := by
    have hker : r * r ∈ (εm (GaloisField 3 1)).ker := by
      rw [MonoidHom.mem_ker, map_mul, hεr, rootTorusSL2_neg_one_mul_self]
    exact no_central_fund3 hγF (mul_mem hr hr) (εm_ker_le_center hker)
  have hr1 : r ≠ 1 := by
    rintro rfl
    exact rootTorusSL2_neg_one_ne_one hF γ (by rw [← hεr, map_one])
  exact ⟨r, hr, orderOf_eq_prime (by rwa [pow_two]) hr1⟩

theorem εm_involution_std3 {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) {r : M₇}
    (hr : r ∈ stdRankOne D₇ γ) (h2 : orderOf r = 2) :
    εm (GaloisField 3 1) r = rootDiagUnit .E7 (thetaDiag γ (-1 : (GaloisField 3 1)ˣ)) := by
  have hF : ringChar (GaloisField 3 1) ≠ 2 := ringChar_galoisField_ne_two (by norm_num)
  have hγF := std_mem_fund3 hγ
  have hεr : εm (GaloisField 3 1) r ∈ rootRankOneGroup .E7 (GaloisField 3 1) γ := by
    rw [← map_stdRankOne_εm hγ]
    exact Subgroup.mem_map_of_mem _ hr
  have hss : r * r = 1 := by rw [← sq]; exact h2 ▸ pow_orderOf_eq_one r
  have hz2 : εm (GaloisField 3 1) r * εm (GaloisField 3 1) r = 1 := by
    rw [← map_mul, hss, map_one]
  have hz1 : εm (GaloisField 3 1) r ≠ 1 := by
    intro h1
    have := no_central_fund3 hγF hr (εm_ker_le_center (MonoidHom.mem_ker.2 h1))
    rw [this, orderOf_one] at h2
    omega
  rw [eq_rootTorusSL2_neg_one_of_mul_self_eq_one hF odd_gf3 hεr hz2 hz1,
    rootTorusSL2_eq_thetaDiag hγ]

end Standard

section Relations

theorem modelAdj_std3 {δ δ' : Fin (Tag.rank .E7) → ℤ} (hδ : IsRoot .E7 δ) (hδ' : IsRoot .E7 δ')
    (h : iform δ δ' = -1) :
    Gaps.ModelAdj (Subgroup.center M₇) (stdRankOne D₇ δ) (stdRankOne D₇ δ') ∧
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (stdRankOne D₇ δ) (stdRankOne D₇ δ') := by
  obtain ⟨W, hW⟩ := linearPair_of_roots (GaloisField 3 1) hδ hδ' (Or.inr h)
  obtain ⟨r₁, hr₁, hr₁2⟩ := exists_involution_std3 hδ
  obtain ⟨r₂, hr₂, hr₂2⟩ := exists_involution_std3 hδ'
  have hc : r₁ * r₂ = r₂ * r₁ :=
    Gaps.standardPair_involutions_commute two_ne_zero_gf3 hW hr₁ hr₂ hr₁2 hr₂2
  refine ⟨⟨ne_of_linearBlockStandardPair hW, not_commutes_of_linearBlockStandardPair hW, r₁, r₂,
    ⟨hr₁, hr₁2⟩, ⟨hr₂, hr₂2⟩, ?_, ?_⟩, W, hW⟩
  · have : ⁅r₁, r₂⁆ = 1 := by
      rw [commutatorElement_def, hc]
      group
    rw [this]
    exact Subgroup.one_mem _
  · intro x hx
    have := Gaps.conjSub_eq_of_standardPair two_ne_zero_gf3 hW hr₂ hr₂2
    rw [← this]
    exact conj_mem_conjSub hx

theorem e7FrameRelations3 : TypeE8.E7FrameRelations 3 1 := by
  intro g δ δ' hδ hδ'
  have hδr : IsRoot .E7 δ := mem_rootFinset.1 ((TypeE8.mem_roots_D7_iff 3 1 δ).1 hδ)
  have hδ'r : IsRoot .E7 δ' := mem_rootFinset.1 ((TypeE8.mem_roots_D7_iff 3 1 δ').1 hδ')
  refine ⟨conjSub_mem_fundamentalSubgroups (std_mem_fund3 hδr) g, fun h => ?_, fun h => ?_⟩
  · exact (commutes_std3 hδr hδ'r h).conjSub g
  · obtain ⟨hadj, W, hW⟩ := modelAdj_std3 hδr hδ'r h
    exact ⟨Gaps.ModelAdj.map_equiv (MulAut.conj g) hadj, _,
      Gaps.linearBlockStandardPair_map_equiv (MulAut.conj g) hW⟩

end Relations

section Involutions

theorem frameInvolutions_std3 {δ₁ δ₂ : Fin (Tag.rank .E7) → ℤ} (h₁ : IsRoot .E7 δ₁)
    (h₂ : IsRoot .E7 δ₂) (horth : iform δ₁ δ₂ = 0) {r₁ r₂ : M₇} (hr₁ : r₁ ∈ stdRankOne D₇ δ₁)
    (hr₂ : r₂ ∈ stdRankOne D₇ δ₂) (h₁2 : orderOf r₁ = 2) (h₂2 : orderOf r₂ = 2) :
    r₁ ∉ Subgroup.center M₇ ∧ r₂ ∉ Subgroup.center M₇ ∧ r₁ * r₂ ∉ Subgroup.center M₇ ∧
      ∀ δ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 δ → (iform δ δ₁ + iform δ δ₂) % 2 = 0 →
        stdRankOne D₇ δ ≤ Subgroup.centralizer ({r₁ * r₂} : Set M₇) := by
  have hF : ringChar (GaloisField 3 1) ≠ 2 := ringChar_galoisField_ne_two (by norm_num)
  have hεz : εm (GaloisField 3 1) (r₁ * r₂) = rootDiagUnit .E7
      (thetaDiag δ₁ (-1 : (GaloisField 3 1)ˣ) * thetaDiag δ₂ (-1)) := by
    rw [map_mul, εm_involution_std3 h₁ hr₁ h₁2, εm_involution_std3 h₂ hr₂ h₂2,
      ← rootDiagUnit_mul]
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_, fun δ hδ hev => ?_⟩
  · have := no_central_fund3 (std_mem_fund3 h₁) hr₁ hc
    rw [this, orderOf_one] at h₁2
    omega
  · have := no_central_fund3 (std_mem_fund3 h₂) hr₂ hc
    rw [this, orderOf_one] at h₂2
    omega
  · obtain ⟨j, hodd⟩ := exists_odd_total h₁ h₂ horth
    have hσr : IsRoot .E7 (Pi.single j 1 : Fin (Tag.rank .E7) → ℤ) := isRoot_single .E7 j
    have hmem : rootSL2 .E7 (GaloisField 3 1) (Pi.single j 1) (uSL 1) ∈
        (stdRankOne D₇ (Pi.single j 1)).map (εm (GaloisField 3 1)) := by
      rw [map_stdRankOne_εm hσr]
      exact ⟨uSL 1, rfl⟩
    obtain ⟨y, hy, hyε⟩ := Subgroup.mem_map.1 hmem
    have hcomm : y * (r₁ * r₂) = (r₁ * r₂) * y := Subgroup.mem_center_iff.1 hc y
    have h1 : εm (GaloisField 3 1) y * εm (GaloisField 3 1) (r₁ * r₂) =
        εm (GaloisField 3 1) (r₁ * r₂) * εm (GaloisField 3 1) y := by
      rw [← map_mul, ← map_mul, hcomm]
    rw [hεz, hyε] at h1
    have h2 := rootDiagUnit_conj_rootSL2_gen
      (thetaDiag δ₁ (-1 : (GaloisField 3 1)ˣ) * thetaDiag δ₂ (-1)) hσr (uSL 1)
    rw [mul_inv_eq_iff_eq_mul.2 h1.symm, rootChar_signProd, hodd.neg_one_zpow,
      diagConj2_uSL_gen] at h2
    have hinj := ((exceptional_Lang_root_rank_one_data .E7 (GaloisField 3 1)
      (Pi.single j 1)).2.2.2.2.2.2.2.1 hF).1
    have h3 := uSL_injective_of_field (hinj h2.symm)
    simp only [Units.val_neg, Units.val_one, mul_one] at h3
    exact Ring.neg_one_ne_one_of_char_ne_two hF h3
  · have hδF := std_mem_fund3 hδ
    set b := thetaDiag δ₁ (-1 : (GaloisField 3 1)ˣ) * thetaDiag δ₂ (-1) with hb
    have hbδ : rootChar b δ = 1 := by
      rw [hb, rootChar_signProd, iform_comm δ₁, iform_comm δ₂]
      exact (Int.even_iff.2 hev).neg_one_zpow
    have hc : ∀ a ∈ Subgroup.zpowers (r₁ * r₂), ∀ l ∈ stdRankOne D₇ δ,
        εm (GaloisField 3 1) a * εm (GaloisField 3 1) l =
          εm (GaloisField 3 1) l * εm (GaloisField 3 1) a := by
      intro a ha l hl
      have hl' : εm (GaloisField 3 1) l ∈ rootRankOneGroup .E7 (GaloisField 3 1) δ := by
        rw [← map_stdRankOne_εm hδ]
        exact Subgroup.mem_map_of_mem _ hl
      obtain ⟨A, hA⟩ := hl'
      have h4 := rootDiagUnit_conj_rootSL2_gen b hδ A
      rw [hbδ] at h4
      have h5 : diagConj2 (1 : (GaloisField 3 1)ˣ) 1 A = A := by
        refine SL2_ext ?_ ?_ ?_ ?_ <;>
          simp [coe_diagConj2, Matrix.mul_apply, Matrix.diagonal_apply]
      rw [h5] at h4
      have hcomm1 : rootDiagUnit .E7 b * εm (GaloisField 3 1) l =
          εm (GaloisField 3 1) l * rootDiagUnit .E7 b := by
        rw [← hA]
        calc rootDiagUnit .E7 b * rootSL2 .E7 (GaloisField 3 1) δ A =
            (rootDiagUnit .E7 b * rootSL2 .E7 (GaloisField 3 1) δ A * (rootDiagUnit .E7 b)⁻¹) *
              rootDiagUnit .E7 b := by group
          _ = rootSL2 .E7 (GaloisField 3 1) δ A * rootDiagUnit .E7 b := by rw [h4]
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [map_zpow, hεz]
      exact ((Commute.zpow_left (show Commute (rootDiagUnit .E7 b) (εm (GaloisField 3 1) l) from
        hcomm1) k)).eq
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commutes_of_map_commute_exponent3 (εm (GaloisField 3 1)) εm_ker_le_center cop_ker3
      (A := Subgroup.zpowers (r₁ * r₂)) (L := stdRankOne D₇ δ) (pow3_fund3 hδF) hc (r₁ * r₂)
      (Subgroup.mem_zpowers _) w hw).symm

theorem e7FrameInvolutions_sc3 :
    ∀ (g : M₇) (δ₁ δ₂ : Fin (Tag.rank .E7) → ℤ), IsRoot .E7 δ₁ → IsRoot .E7 δ₂ →
      iform δ₁ δ₂ = 0 →
      ∀ r₁ ∈ conjSub g (stdRankOne D₇ δ₁), ∀ r₂ ∈ conjSub g (stdRankOne D₇ δ₂), orderOf r₁ = 2 →
        orderOf r₂ = 2 → r₁ ∉ Subgroup.center M₇ ∧ r₂ ∉ Subgroup.center M₇ ∧
          r₁ * r₂ ∉ Subgroup.center M₇ ∧
          ∀ δ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 δ → (iform δ δ₁ + iform δ δ₂) % 2 = 0 →
            conjSub g (stdRankOne D₇ δ) ≤ Subgroup.centralizer ({r₁ * r₂} : Set M₇) := by
  intro g δ₁ δ₂ hδ₁r hδ₂r horth r₁ hr₁ r₂ hr₂ h₁2 h₂2
  obtain ⟨a₁, ha₁, rfl⟩ := Subgroup.mem_map.1 hr₁
  obtain ⟨a₂, ha₂, rfl⟩ := Subgroup.mem_map.1 hr₂
  have ha₁2 : orderOf a₁ = 2 := by
    rw [← h₁2]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a₁).symm
  have ha₂2 : orderOf a₂ = 2 := by
    rw [← h₂2]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a₂).symm
  obtain ⟨c₁, c₂, c₃, c₄⟩ := frameInvolutions_std3 hδ₁r hδ₂r horth ha₁ ha₂ ha₁2 ha₂2
  refine ⟨?_, ?_, ?_, fun δ hδr hev => ?_⟩
  · exact fun h => c₁ ((MulEquivClass.apply_mem_center_iff (MulAut.conj g)).1 h)
  · exact fun h => c₂ ((MulEquivClass.apply_mem_center_iff (MulAut.conj g)).1 h)
  · intro h
    apply c₃
    refine (MulEquivClass.apply_mem_center_iff (MulAut.conj g)).1 ?_
    have e : (MulAut.conj g) (a₁ * a₂) = g * a₁ * g⁻¹ * (g * a₂ * g⁻¹) := by
      simp only [MulAut.conj_apply]
      group
    rw [e]
    exact h
  · intro w hw
    obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.1 hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.1 (c₄ δ hδr hev hw')
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * w' * g⁻¹ * (g * a₁ * g⁻¹ * (g * a₂ * g⁻¹)) = g * (w' * (a₁ * a₂)) * g⁻¹ := by group
      _ = g * (a₁ * a₂ * w') * g⁻¹ := by rw [this]
      _ = g * a₁ * g⁻¹ * (g * a₂ * g⁻¹) * (g * w' * g⁻¹) := by group

theorem e7FrameInvolutions3 : TypeE8.E7FrameInvolutions 3 1 := by
  intro g δ₁ δ₂ hδ₁ hδ₂ horth r₁ hr₁ r₂ hr₂ h₁2 h₂2
  have hδ₁r : IsRoot .E7 δ₁ := mem_rootFinset.1 ((TypeE8.mem_roots_D7_iff 3 1 δ₁).1 hδ₁)
  have hδ₂r : IsRoot .E7 δ₂ := mem_rootFinset.1 ((TypeE8.mem_roots_D7_iff 3 1 δ₂).1 hδ₂)
  obtain ⟨c₁, c₂, c₃, c₄⟩ := e7FrameInvolutions_sc3 g δ₁ δ₂ hδ₁r hδ₂r horth r₁ hr₁ r₂ hr₂ h₁2 h₂2
  exact ⟨c₁, c₂, c₃, fun δ hδ hev =>
    c₄ δ (mem_rootFinset.1 ((TypeE8.mem_roots_D7_iff 3 1 δ).1 hδ)) hev⟩

end Involutions

end CFSG.ClassicalInvolution.Q3.Q3W
