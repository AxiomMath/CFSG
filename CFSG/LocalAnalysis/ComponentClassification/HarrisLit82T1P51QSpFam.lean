module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QSpNs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QF
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eComp
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Props
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.Burgoyne.Sp CFSG.ComponentClassification.Burgoyne.Proj

variable {r : ℕ} {K : Type} [Field K]

theorem exists_smul_of_projH_eq_one {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Subgroup (GL ι K)} {s : H} (hs : projH H s = 1) :
    ∃ μ : K, ((s : GL ι K) : Matrix ι ι K) = μ • 1 := by
  have h1 := (QuotientGroup.eq_one_iff _).1 hs
  rw [mem_subgroupOf] at h1
  obtain ⟨c, hc⟩ := h1
  refine ⟨(c : K), ?_⟩
  rw [← hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem coe_eq_smul_of_conj {s H : StatedSp r K} {μ : K}
    (h : (((H * s * H⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = μ • 1) :
    ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = μ • 1 := by
  have e : s = H⁻¹ * (H * s * H⁻¹) * H := by group
  rw [e, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, h, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
    OneMemClass.coe_one, Units.val_one]

variable [Finite K]

theorem famF_concl_sp (hK : ringChar K ≠ 2) {p f : ℕ} (hp : p.Prime) (hKc : Nat.card K = p ^ f)
    (hK3 : Nat.card K ≠ 3) (hr : 2 ≤ r) {X : Type} [Group X] [Finite X]
    (θ : X ≃* StatedProj (StatedSp r K)) {z : X} (hz : orderOf z = 2) {P : Subgroup X}
    (hPC : P ≤ centralizer ({z} : Set X)) (h8 : Nat.card P = 8)
    (hP : ∀ L : Subgroup (centralizer ({z} : Set X)), IsComponent L → Even (Nat.card L) →
      ∀ k ∈ L, ∀ g ∈ P, (k : X) * g = g * k) :
    ¬ ((∃ u ∈ P, ∃ v ∈ P, u * v ≠ v * u) ∧ ∀ q ∈ P, q * q = 1 → q = 1 ∨ q = z) ∧
      ¬ ∀ q ∈ P, q * q = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have : NeZero r := ⟨by omega⟩
  have hp2 : p ≠ 2 := fun h => hK (by rw [ringChar.eq K p, h])
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h
    · rw [h0, pow_zero] at hKc
      have := Finite.one_lt_card (α := K)
      omega
    · exact h
  have hq5 : 5 ≤ p ^ f := by
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have h3 : 3 ≤ p ^ f := le_trans (by have := hp.two_le; omega)
      (Nat.le_self_pow (by omega : f ≠ 0) p)
    obtain ⟨k, hk⟩ := hodd
    rw [← hKc] at hk h3
    rw [← hKc]
    omega
  have h4 : 4 ≤ Nat.card K := by omega
  set π₀ := θ.symm.toMonoidHom.comp (projH (StatedSp r K)) with hπ₀def
  have hπ₀ : Function.Surjective π₀ := θ.symm.surjective.comp projH_surjective
  have hker₀ : ∀ s, π₀ s = 1 → ∃ μ : K,
      ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = μ • 1 := by
    intro s hs
    refine exists_smul_of_projH_eq_one ?_
    have e : θ.symm (projH _ s) = 1 := hs
    rwa [MulEquiv.map_eq_one_iff] at e
  have hz2 : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    exact absurd hz (by norm_num)
  obtain ⟨a, ha⟩ := hπ₀ z
  obtain ⟨μ, hμ⟩ := hker₀ (a * a) (by rw [map_mul, ha, hz2])
  have hAns : ∀ c : Kˣ,
      (a : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
    intro c hc
    apply hz1
    rw [← ha]
    change θ.symm (projH _ a) = 1
    rw [MulEquiv.map_eq_one_iff]
    exact (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 ⟨c, hc.symm⟩)
  have hJa := mem_statedSp_iff.1 a.2
  have hconj : ∀ H : StatedSp r K,
      Function.Surjective (π₀.comp (MulAut.conj H).toMonoidHom) ∧
        (∀ s, (π₀.comp (MulAut.conj H).toMonoidHom) s = 1 → ∃ ν : K,
          ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = ν • 1) ∧
        (π₀.comp (MulAut.conj H).toMonoidHom) (H⁻¹ * a * H) = z := by
    intro H
    refine ⟨hπ₀.comp (MulAut.conj H).surjective, fun s hs => ?_, ?_⟩
    · obtain ⟨ν, hν⟩ := hker₀ _ hs
      exact ⟨ν, coe_eq_smul_of_conj hν⟩
    · change π₀ (H * (H⁻¹ * a * H) * H⁻¹) = z
      rw [show H * (H⁻¹ * a * H) * H⁻¹ = a by group, ha]
  rcases eq_one_or_neg_of_coe_eq_smul (s := a * a) hμ with h1 | h1
  ·
    exfalso
    subst ha
    have hker₀' : ∀ s, π₀ s = 1 → s ∈ center (StatedSp r K) := fun s hs => by
      obtain ⟨ν, hν⟩ := hker₀ s hs
      exact mem_center_of_coe_eq_smul_one hν
    have hinj : Function.Injective (fun s : StatedSp r K =>
        ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) :=
      fun s t h => Subtype.ext (Units.ext h)
    have hcard := card_le_of_forall_lift_mem π₀ hinj
      ({1, -1, ((a : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K),
        -((a : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)} : Finset _)
      fun g hg => ⟨Function.surjInv hπ₀ g, Function.surjInv_eq hπ₀ g, by
        rcases lift_cases_self hK hK3 hr hAns h1 π₀ hπ₀ hker₀'
          (fun L hL he k hk => hP L hL he k hk g hg) (Function.surjInv_eq hπ₀ g) with
          h | h | h | h <;> simp [h]⟩
    have e1 := Finset.card_insert_le (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
      ({-1, ((a : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K),
        -((a : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)} : Finset _)
    have e2 := Finset.card_insert_le (-1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
      ({((a : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K),
        -((a : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)} : Finset _)
    have e3 := Finset.card_insert_le
      ((a : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
      ({-((a : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)} : Finset _)
    rw [Finset.card_singleton] at e3
    omega
  ·
    by_cases hsq : ∃ l : K, l ^ 2 = -1
    · obtain ⟨l, hl⟩ := hsq
      have hl0 : l ≠ 0 := by
        rintro rfl
        have : (0 : K) = -1 := by rw [← hl]; ring
        exact one_ne_zero (neg_eq_zero.1 this.symm)
      obtain ⟨H, hH⟩ := exists_skew_split_normal_form hK
        (A := ⟨(a : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp a.2⟩) hl0
        (by rw [hl, neg_one_smul]; exact h1) (by rw [hl, neg_neg, one_smul]; exact hJa)
      obtain ⟨hπ', hker', hz'⟩ := hconj H
      have ha' : (((H⁻¹ * a * H : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = l • stdSkew r K := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul]
        exact hH
      subst hz'
      exact famF_concl_sp_split hK h4 hr hl _ hπ' hker' ha' hz2 hPC h8 hP
    · push Not at hsq
      obtain ⟨H, hH⟩ := exists_skew_nonsplit_normal_form hp hp2 hf hKc (by omega)
        (A := ⟨(a : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp a.2⟩) hAns hsq
        (by rw [neg_one_smul]; exact h1) (by rw [neg_neg, one_smul]; exact hJa)
      obtain ⟨hπ', hker', hz'⟩ := hconj H
      have ha' : (((H⁻¹ * a * H : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = skewNs r K (-1) := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul]
        exact hH
      subst hz'
      exact famF_concl_sp_nonsplit hp hp2 hf hKc hq5 hr hsq _ hπ' hker' ha' hz2 hPC h8 hP

theorem famF_PSp : FamF .PSp := by
  intro X _ _ _ n p f hp hp2 hX hq z hz P hPC _ h8 hP
  obtain ⟨⟨-, -, hn, -⟩, F, _, _, hFc, ⟨θ⟩⟩ :=
    P51e.Comp.statedClassicalModel_of_lieModel (by decide) hX
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  exact famF_concl_sp hF hp hFc (by rwa [hFc]) hn θ hz hPC h8 hP

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
