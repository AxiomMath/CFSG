module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelSylow
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthAdj
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
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.ClassicalInvolution.Balance.BootstrapDischarge
public import CFSG.ClassicalInvolution.Balance.LayerGenerationInner
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTriple
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE6
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcReduce
public import CFSG.ClassicalInvolution.Models.SymplecticPairs
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts.Levi
  CFSG.ClassicalInvolution.ModelFacts

section Normalizer

variable {F : Type} [Field F]

local notation "ρθ" => rootSL2 Tag.E7 F thetaE7

theorem map_conj_rootRankOneGroup_of_commute (hF : ringChar F ≠ 2) {w : ModGL .E7 F}
    (hwG : w ∈ adjointGroup .E7 F)
    (hwd : w * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Fˣ)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Fˣ)) * w) :
    (rootRankOneGroup .E7 F thetaE7).map (MulAut.conj w).toMonoidHom =
      rootRankOneGroup .E7 F thetaE7 := by
  have key : ∀ {w : ModGL .E7 F}, w ∈ adjointGroup .E7 F →
      w * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Fˣ)) =
        rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Fˣ)) * w → ∀ B : SL2 F,
      ∃ B' : SL2 F, w * ρθ B * w⁻¹ = ρθ B' := by
    intro w hwG hwd B
    have hcT : w ∈ toralCentralizer .E7 F (thetaDiag thetaE7 (-1 : Fˣ)) := by
      rw [mem_toralCentralizer]
      refine ⟨hwG, ?_⟩
      rw [mul_inv_eq_iff_eq_mul]
      exact hwd.symm
    obtain ⟨n, hn, A, rfl⟩ := toralRootGroup_le_leviMulRank1 hF
      (toralCentralizer_le_toralRootGroup_thetaE7 hF hcT)
    obtain ⟨B', hB'⟩ := exists_levi_conj_rootSL2_eq_E7 hn (A * B * A⁻¹)
    refine ⟨B', ?_⟩
    rw [← hB', map_mul, map_mul, map_inv]
    group
  have hwd' : w⁻¹ * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Fˣ)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Fˣ)) * w⁻¹ := by
    exact (Commute.inv_left (show Commute w (rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Fˣ))) from
      hwd))
  ext x
  constructor
  · rintro ⟨_, ⟨B, rfl⟩, rfl⟩
    obtain ⟨B', hB'⟩ := key hwG hwd B
    exact ⟨B', by simpa [MulAut.conj_apply] using hB'.symm⟩
  · rintro ⟨B, rfl⟩
    obtain ⟨B', hB'⟩ := key (inv_mem hwG) hwd' B
    refine ⟨ρθ B', ⟨B', rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hB']
    group

end Normalizer

section Frame

variable {p f : ℕ} [Fact p.Prime]

local notation "ρθ" => rootSL2 Tag.E7 (GaloisField p f) thetaE7
local notation "dθ" => rootDiagUnit Tag.E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ))
local notation "Lθ" => rootRankOneGroup Tag.E7 (GaloisField p f) thetaE7

theorem exists_frame_adj_e7 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {u₂ : ModGL .E7 (GaloisField p f)} (hu₂ : u₂ ∈ adjointGroup .E7 (GaloisField p f))
    (hcd : (u₂ * dθ * u₂⁻¹) * dθ = dθ * (u₂ * dθ * u₂⁻¹))
    {U : Subgroup (SL2 (GaloisField p f))} (hU : Nat.card U = Nat.card (GaloisField p f))
    (hinv : ∀ A ∈ U, (u₂ * dθ * u₂⁻¹) * ρθ A * (u₂ * dθ * u₂⁻¹)⁻¹ = (ρθ A)⁻¹)
    (hne : (Lθ).map (MulAut.conj u₂).toMonoidHom ≠ Lθ)
    (hnc : ¬ ∀ x ∈ Lθ, ∀ y ∈ (Lθ).map (MulAut.conj u₂).toMonoidHom, x * y = y * x) :
    ∃ (γ : Fin (Tag.rank .E7) → ℤ) (w : ModGL .E7 (GaloisField p f)), IsRoot .E7 γ ∧
      (iform thetaE7 γ = 1 ∨ iform thetaE7 γ = -1) ∧ w ∈ adjointGroup .E7 (GaloisField p f) ∧
      w * dθ = dθ * w ∧ (Lθ).map (MulAut.conj (w * u₂)).toMonoidHom = rootRankOneGroup .E7 _ γ := by
  have hF : ringChar (GaloisField p f) ≠ 2 := ringChar_galoisField_ne_two hp2
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf0
  have hdθ : dθ = ρθ (HSL (-1)) := (rootTorusSL2_thetaE7 (-1)).symm
  have hdG : dθ ∈ adjointGroup .E7 (GaloisField p f) := by
    rw [hdθ]
    exact rootSL2_mem_adjointGroup _ _
  have hd2 : dθ * dθ = 1 := by
    rw [hdθ, ← map_mul, HSL_neg_one_mul_self, map_one]
  set c := u₂ * dθ * u₂⁻¹ with hc
  have hcG : c ∈ adjointGroup .E7 (GaloisField p f) := mul_mem (mul_mem hu₂ hdG) (inv_mem hu₂)
  have hc2 : c * c = 1 := by
    rw [hc]
    calc u₂ * dθ * u₂⁻¹ * (u₂ * dθ * u₂⁻¹) = u₂ * (dθ * dθ) * u₂⁻¹ := by group
      _ = 1 := by rw [hd2]; group
  obtain ⟨e, hcL, hcU⟩ := exists_conj_mem_levi_of_inverts Fact.out hcard hF hcG hcd hU hinv
  set r := ρθ e with hr
  have hrG : r ∈ adjointGroup .E7 (GaloisField p f) := rootSL2_mem_adjointGroup _ _
  have hrd : r * dθ = dθ * r := by
    rw [hdθ, hr, ← map_mul, ← map_mul, HSL_neg_one_mul]
  set c' := r * c * r⁻¹ with hc'
  have hc'G : c' ∈ adjointGroup .E7 (GaloisField p f) :=
    mul_mem (mul_mem hrG hcG) (inv_mem hrG)
  have hc'2 : c' * c' = 1 := by
    rw [hc']
    calc r * c * r⁻¹ * (r * c * r⁻¹) = r * (c * c) * r⁻¹ := by group
      _ = 1 := by rw [hc2]; group
  have hgG : r * u₂ ∈ adjointGroup .E7 (GaloisField p f) := mul_mem hrG hu₂
  have hgc : (r * u₂) * dθ * (r * u₂)⁻¹ = c' := by rw [hc', hc]; group
  obtain ⟨δ, hδ, hδθ, w₀, hw₀G, hw₀c, hw₀d⟩ :=
    exists_rational_conj_e7_adj hodd hc'G hgG hc'2 hcL hcU hgc
  set w := w₀ * r with hw
  have hwG : w ∈ adjointGroup .E7 (GaloisField p f) := mul_mem hw₀G hrG
  have hwd : w * dθ = dθ * w := by
    rw [hw]
    calc w₀ * r * dθ = w₀ * (r * dθ) := by group
      _ = w₀ * (dθ * r) := by rw [hrd]
      _ = (w₀ * dθ) * r := by group
      _ = (dθ * w₀) * r := by rw [hw₀d]
      _ = dθ * (w₀ * r) := by group
  have hwc : w * c * w⁻¹ = rootDiagUnit .E7 (thetaDiag δ (-1 : (GaloisField p f)ˣ)) := by
    rw [hw]
    calc w₀ * r * c * (w₀ * r)⁻¹ = w₀ * (r * c * r⁻¹) * w₀⁻¹ := by group
      _ = _ := hw₀c
  have hconj : (w * u₂) * rootTorusSL2 .E7 (GaloisField p f) thetaE7 (-1) * (w * u₂)⁻¹ =
      rootDiagUnit .E7 (thetaDiag δ (-1 : (GaloisField p f)ˣ)) := by
    rw [rootTorusSL2_thetaE7, ← hwc, hc]
    group
  obtain ⟨γ, hγ, hLγ, -, -⟩ := exists_rootRankOneGroup_of_conj_toral hp2 hq
    (isLongRoot_of_isRoot_of_simplyLaced (Or.inr (Or.inl rfl)) isRoot_thetaE7)
    (mul_mem hwG hu₂) (fun i => thetaDiag_neg_one_sign_E7 δ i) hconj
  have hγroot : IsRoot .E7 γ := hγ.1
  have hnormw : (Lθ).map (MulAut.conj w).toMonoidHom = Lθ :=
    map_conj_rootRankOneGroup_of_commute hF hwG hwd
  have hcomp : (Lθ).map (MulAut.conj (w * u₂)).toMonoidHom =
      ((Lθ).map (MulAut.conj u₂).toMonoidHom).map (MulAut.conj w).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
  have hLγ' : ((Lθ).map (MulAut.conj u₂).toMonoidHom).map (MulAut.conj w).toMonoidHom =
      rootRankOneGroup .E7 (GaloisField p f) γ := by rw [← hcomp]; exact hLγ
  have hne' : rootRankOneGroup .E7 (GaloisField p f) γ ≠ Lθ := by
    intro h
    apply hne
    refine Subgroup.map_injective (f := (MulAut.conj w).toMonoidHom) (MulAut.conj w).injective ?_
    rw [hLγ', h, hnormw]
  have hnc' : ¬ ∀ x ∈ Lθ, ∀ y ∈ rootRankOneGroup .E7 (GaloisField p f) γ, x * y = y * x := by
    intro h
    apply hnc
    intro x hx y hy
    have hx' : w * x * w⁻¹ ∈ Lθ := by
      rw [← hnormw]
      exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    have hy' : w * y * w⁻¹ ∈ rootRankOneGroup .E7 (GaloisField p f) γ := by
      rw [← hLγ']
      exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
    have h1 := h _ hx' _ hy'
    have h2 : w * (x * y) * w⁻¹ = w * (y * x) * w⁻¹ := by
      calc w * (x * y) * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹) := by group
        _ = (w * y * w⁻¹) * (w * x * w⁻¹) := h1
        _ = w * (y * x) * w⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hodd' : ¬ Even (iform thetaE7 γ) := by
    intro hev
    rcases eq_or_iform_eq_zero_of_even_E7 hγroot hev with rfl | rfl | h0
    · exact hne' rfl
    · apply hne'
      rw [rootRankOneGroup_eq_sup hγroot, rootRankOneGroup_eq_sup isRoot_thetaE7, neg_neg,
        sup_comm]
    · exact hnc' ((isLongRoot_of_isRoot_of_simplyLaced (Or.inr (Or.inl rfl))
        isRoot_thetaE7).commute_rootRankOneGroup hγroot h0)
  have hpair : iform thetaE7 γ = 1 ∨ iform thetaE7 γ = -1 := by
    have hb := abs_iform_le_two_E7 isRoot_thetaE7 hγroot
    rw [abs_le] at hb
    have : Odd (iform thetaE7 γ) := Int.not_even_iff_odd.1 hodd'
    obtain ⟨m, hm⟩ := this
    omega
  exact ⟨γ, w, hγroot, hpair, hwG, hwd, hLγ⟩

end Frame

end CFSG.ClassicalInvolution.ModelFacts.E7Model
