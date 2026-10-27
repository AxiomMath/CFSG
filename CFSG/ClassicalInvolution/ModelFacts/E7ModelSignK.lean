module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelSign
public import CFSG.ClassicalInvolution.RouteD.TypeELocal
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld

variable {p f : ℕ} [Fact p.Prime]

local notation "M₇" => E7sc p f
local notation "D₇" => e7Datum (GaloisField p f)

theorem e7_fund_class (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    Generic.FundamentalSingleClass .E7 D₇ ∧
      stdRankOne D₇ thetaE7 ∈ fundamentalSubgroups .E7 D₇ ∧
      ∀ R ∈ fundamentalSubgroups .E7 D₇, ⁅R, R⁆ = R := by
  have : NeZero f := ⟨by rintro rfl; simp at hq⟩
  have hadm : StatedLieAdmissible .E7 0 p f :=
    ⟨Fact.out, Nat.one_le_iff_ne_zero.2 (NeZero.ne f), rfl⟩
  have hsingle : Generic.FundamentalSingleClass .E7 D₇ :=
    fundamentalSingleClass .E7 0 p f Fact.out trivial hadm (by decide) (by decide)
  have hlong := isLongestRoot_single .E7 0 p f Fact.out trivial hadm
  have hθ : Generic.IsLongestRoot D₇ thetaE7 :=
    isLongestRoot_of_mem_roots_of_forall_single _ rfl (fun k => hlong k trivial)
      ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField p f)).2
        isRoot_thetaE7)
  have hRθF : stdRankOne D₇ thetaE7 ∈ fundamentalSubgroups .E7 D₇ :=
    ⟨1, thetaE7, Or.inl hθ, (conjSub_one _).symm⟩
  exact ⟨hsingle, hRθF, fun R hR => le_antisymm (commutator_self_le R)
    (fundPerfect_core .E7 0 p f hp2 trivial hadm (by omega) R hR)⟩

theorem no_central_fund (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {R : Subgroup M₇}
    (hR : R ∈ fundamentalSubgroups .E7 D₇) {r : M₇} (hr : r ∈ R)
    (hrc : r ∈ Subgroup.center M₇) : r = 1 := by
  obtain ⟨hsingle, hRθF, -⟩ := e7_fund_class hp2 hq
  obtain ⟨W, hW⟩ := CFSG.ClassicalInvolution.RouteD.stdPair_edge_E7 (F := GaloisField p f)
    (i := 0) (j := 2) (by decide)
  have : NeZero f := ⟨by rintro rfl; simp at hq⟩
  have hadm : StatedLieAdmissible .E7 0 p f :=
    ⟨Fact.out, Nat.one_le_iff_ne_zero.2 (NeZero.ne f), rfl⟩
  have hl := ModelFacts.isLongestRoot_single .E7 0 p f Fact.out trivial hadm
  let a0 : Fin 7 := 0
  have h0 : rankOne (D₇).rootGroup (0 : Fin 7) ∈ fundamentalSubgroups .E7 D₇ :=
    rankOne_mem_fundamental _ (hl a0 trivial)
  obtain ⟨g, hg⟩ := hsingle _ h0 R hR
  have hW' := linearBlockStandardPair_map_conj hW g
  rw [hg] at hr
  exact (eq_one_of_mem_center_of_stdPair hW').1 r hr hrc


theorem εm_involution_of_mem_fund (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {h r : M₇}
    (hr : r ∈ conjSub h (stdRankOne D₇ thetaE7)) (h2 : orderOf r = 2) :
    εm (GaloisField p f) r = εm (GaloisField p f) h *
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) *
        (εm (GaloisField p f) h)⁻¹ := by
  have hF : ringChar (GaloisField p f) ≠ 2 := ringChar_galoisField_ne_two hp2
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  obtain ⟨-, hRθF, -⟩ := e7_fund_class hp2 hq
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hr
  have hs2 : orderOf s = 2 := by
    rw [← h2]
    exact (orderOf_injective _ (MulAut.conj h).injective s).symm
  have hss : s * s = 1 := by rw [← sq]; exact hs2 ▸ pow_orderOf_eq_one s
  have hεs : εm (GaloisField p f) s ∈ rootRankOneGroup .E7 (GaloisField p f) thetaE7 := by
    rw [← map_stdRankOne_εm isRoot_thetaE7]
    exact Subgroup.mem_map_of_mem _ hs
  have hz2 : εm (GaloisField p f) s * εm (GaloisField p f) s = 1 := by
    rw [← map_mul, hss, map_one]
  have hz1 : εm (GaloisField p f) s ≠ 1 := by
    intro h1
    have := no_central_fund hp2 hq hRθF hs (εm_ker_le_center (MonoidHom.mem_ker.2 h1))
    rw [this, orderOf_one] at hs2
    omega
  have := eq_rootTorusSL2_neg_one_of_mul_self_eq_one hF hodd hεs hz2 hz1
  rw [rootTorusSL2_thetaE7] at this
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, this]

theorem eq_of_orderOf_two_fund (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {R : Subgroup M₇}
    (hR : R ∈ fundamentalSubgroups .E7 D₇) {r r' : M₇} (hr : r ∈ R) (hr' : r' ∈ R)
    (h2 : orderOf r = 2) (h2' : orderOf r' = 2) : r = r' := by
  obtain ⟨hsingle, hRθF, -⟩ := e7_fund_class hp2 hq
  obtain ⟨g, hg⟩ := hsingle _ hRθF R hR
  rw [hg] at hr hr'
  have e1 := εm_involution_of_mem_fund hp2 hq hr h2
  have e2 := εm_involution_of_mem_fund hp2 hq hr' h2'
  have hker : r⁻¹ * r' ∈ (εm (GaloisField p f)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, e1, e2]
    group
  have hmem : r⁻¹ * r' ∈ R := R.mul_mem (R.inv_mem (by rw [hg]; exact hr)) (by rw [hg]; exact hr')
  have := no_central_fund hp2 hq hR hmem (εm_ker_le_center hker)
  exact (inv_mul_eq_one.1 this)


theorem std_mem_fund (hq : 5 ≤ p ^ f) {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    stdRankOne D₇ γ ∈ fundamentalSubgroups .E7 D₇ := by
  have : NeZero f := ⟨by rintro rfl; simp at hq⟩
  have hadm : StatedLieAdmissible .E7 0 p f :=
    ⟨Fact.out, Nat.one_le_iff_ne_zero.2 (NeZero.ne f), rfl⟩
  have hlong := isLongestRoot_single .E7 0 p f Fact.out trivial hadm
  have hγlong : Generic.IsLongestRoot D₇ γ :=
    isLongestRoot_of_mem_roots_of_forall_single _ rfl (fun k => hlong k trivial)
      ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField p f)).2 hγ)
  exact ⟨1, γ, Or.inl hγlong, (conjSub_one _).symm⟩

theorem sign_step (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Subgroup M₇}
    (hX : X ∈ fundamentalSubgroups .E7 D₇) {r₁ r₂ : M₇} (hr₁ : r₁ ∈ X) (hr₁2 : orderOf r₁ = 2)
    (hr₂ : r₂ ∈ stdRankOne D₇ thetaE7) (hr₂2 : orderOf r₂ = 2)
    (hnorm : ∀ x ∈ X, r₂ * x * r₂⁻¹ ∈ X)
    (hcomm : Commutes (stdRankOne D₇ (Pi.single (e7Idx 0) 1)) X) :
    ∃ x : M₇, conjSub x (stdRankOne D₇ thetaE7) = stdRankOne D₇ thetaE7 ∧
      conjSub x (stdRankOne D₇ (Pi.single (e7Idx 0) 1)) =
        stdRankOne D₇ (Pi.single (e7Idx 0) 1) ∧
      ∃ γ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 γ ∧ conjSub x X = stdRankOne D₇ γ := by
  have hF : ringChar (GaloisField p f) ≠ 2 := ringChar_galoisField_ne_two hp2
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  obtain ⟨hsingle, hRθF, hperf⟩ := e7_fund_class hp2 hq
  have he0 : IsRoot .E7 (Pi.single (e7Idx 0) 1 : V7) := isRoot_single .E7 (e7Idx 0)
  have he0F := std_mem_fund hq he0
  have hεr₂ : εm (GaloisField p f) r₂ =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) := by
    have := εm_involution_of_mem_fund hp2 hq (h := 1) (by rw [conjSub_one]; exact hr₂) hr₂2
    simpa using this
  have hr₁₂ : r₂ * r₁ * r₂⁻¹ = r₁ := by
    refine eq_of_orderOf_two_fund hp2 hq hX (hnorm r₁ hr₁) hr₁ ?_ hr₁2
    rw [← hr₁2]
    exact (orderOf_injective (MulAut.conj r₂).toMonoidHom (MulAut.conj r₂).injective r₁)
  obtain ⟨h, hh⟩ := hsingle _ hRθF X hX
  have hεr₁ := εm_involution_of_mem_fund hp2 hq (h := h) (by rw [← hh]; exact hr₁) hr₁2
  set y := εm (GaloisField p f) r₁ with hy
  have hr1sq : r₁ * r₁ = 1 := by rw [← sq]; exact hr₁2 ▸ pow_orderOf_eq_one r₁
  have hy2 : y * y = 1 := by
    rw [hy, ← map_mul, hr1sq, map_one]
  have hyd : y * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) * y := by
    rw [← hεr₂, hy, ← map_mul, ← map_mul]
    congr 1
    have := hr₁₂
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hye : ∀ A : SL2 (GaloisField p f),
      y * rootSL2 .E7 (GaloisField p f) (Pi.single (e7Idx 0) 1) A =
        rootSL2 .E7 (GaloisField p f) (Pi.single (e7Idx 0) 1) A * y := by
    intro A
    have hmem : rootSL2 .E7 (GaloisField p f) (Pi.single (e7Idx 0) 1) A ∈
        (stdRankOne D₇ (Pi.single (e7Idx 0) 1)).map (εm (GaloisField p f)) := by
      rw [map_stdRankOne_εm he0]
      exact ⟨A, rfl⟩
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.1 hmem
    rw [← hxe, hy, ← map_mul, ← map_mul, (hcomm x hx r₁ hr₁).symm]
  obtain ⟨δ, hδ, u, huG, hu, hudθ, hude0⟩ := sign_core hp2 hq (εm_mem r₁) (εm_mem h) hy2
    hεr₁.symm hyd hye
  obtain ⟨x, hx⟩ := εm_surjective huG
  have hxL : conjSub x (stdRankOne D₇ thetaE7) = stdRankOne D₇ thetaE7 := by
    apply eq_of_map_εm_eq (by rw [conjSub_commutator, hperf _ hRθF]) (hperf _ hRθF)
    rw [map_conjSub, hx, map_stdRankOne_εm isRoot_thetaE7,
      map_conj_rootRankOneGroup_of_commute hF huG hudθ]
  have hxE : conjSub x (stdRankOne D₇ (Pi.single (e7Idx 0) 1)) =
      stdRankOne D₇ (Pi.single (e7Idx 0) 1) := by
    apply eq_of_map_εm_eq (by rw [conjSub_commutator, hperf _ he0F]) (hperf _ he0F)
    have hwd : u * rootTorusSL2 .E7 (GaloisField p f) (Pi.single (e7Idx 0) 1) (-1) =
        rootTorusSL2 .E7 (GaloisField p f) (Pi.single (e7Idx 0) 1) (-1) * u := by
      rw [rootTorusSL2_eq_thetaDiag_gen he0 (-1)]
      exact hude0
    rw [map_conjSub, hx, map_stdRankOne_εm he0,
      map_conj_rootRankOneGroup_of_commute_gen hF hodd he0 huG hwd]
  have hconj : (u * εm (GaloisField p f) h) * rootTorusSL2 .E7 (GaloisField p f) thetaE7 (-1) *
      (u * εm (GaloisField p f) h)⁻¹ =
      rootDiagUnit .E7 (thetaDiag δ (-1 : (GaloisField p f)ˣ)) := by
    rw [rootTorusSL2_thetaE7]
    calc (u * εm (GaloisField p f) h) *
          rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) *
          (u * εm (GaloisField p f) h)⁻¹ =
        u * (εm (GaloisField p f) h *
          rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) *
          (εm (GaloisField p f) h)⁻¹) * u⁻¹ := by group
      _ = u * y * u⁻¹ := by rw [← hεr₁]
      _ = _ := hu
  obtain ⟨γ, hγ, hLγ, -, -⟩ := exists_rootRankOneGroup_of_conj_toral hp2 hq
    (isLongRoot_of_isRoot_of_simplyLaced (Or.inr (Or.inl rfl)) isRoot_thetaE7)
    (mul_mem huG (εm_mem h)) (fun i => thetaDiag_neg_one_sign_E7 δ i) hconj
  have hγr : IsRoot .E7 γ := hγ.1
  refine ⟨x, hxL, hxE, γ, hγr, ?_⟩
  have hγF := std_mem_fund hq hγr
  rw [hh, ← conjSub_mul]
  apply eq_of_map_εm_eq (by rw [conjSub_commutator, hperf _ hRθF]) (hperf _ hγF)
  rw [map_conjSub, map_mul, hx, map_stdRankOne_εm isRoot_thetaE7, map_stdRankOne_εm hγr]
  exact hLγ

end CFSG.ClassicalInvolution.ModelFacts.E7Model
