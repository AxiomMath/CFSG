module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292LinUniDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291NilpAbs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291NilpKappa
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291NilpTwist
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALinAut
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCoverLie
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291N1Comp

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291N

open CFSG.Open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.LocalAnalysis.RankFourTheoremC (l212in_descend l212in_alpha_phi exists_cover_linear)

theorem kd291Nilp_lin (hGA : CFSG.Open.GriessAllModelsStatement) {p : ℕ} {Y : Type} [Group Y]
    [Finite Y] {P : Subgroup Y} {x z : Y} {L : Subgroup Y} (hcfg : LinUniCfg p P x z L)
    (hmodel : LinUniModelLin p x L) :
    CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set Y)) := by
  have hYD := hcfg.data
  have hY := hYD.cfg
  have hp : p.Prime := hY.prime
  have hp5 : 5 ≤ p := hY.five_le
  have hp2 : p ≠ 2 := by omega
  have hn3 : 3 ≤ p := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  have hL := hcfg.comp
  haveI hLn : L.Normal := I291.normal_of_unique hL hcfg.uniq
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hZp : IsPGroup p (center ↥L) := I291.isPGroup_center hY.core hL
  have hx1 : x ≠ 1 := by
    intro h
    have h2 := hYD.rank_cent
    have h3 : centralizer ({x} : Set Y) = ⊤ := by
      rw [h]
      simp
    rw [h3] at h2
    have h4 := hYD.four_le
    omega
  have hxord : orderOf x = p := orderOf_eq_prime hY.x_pow hx1
  obtain ⟨K, instF, instFin, e, ŷ, ω, hpK, hŷp, hω, hact⟩ := hmodel
  have hKcard : 1 < Nat.card K := Finite.one_lt_card
  have hωnp : ∀ b : K, b ^ p ≠ (ω : K) := by
    have ha : 1 ≤ (Nat.card K - 1).factorization p :=
      Nat.Prime.factorization_pos_of_dvd hp (by omega) hpK
    exact I292CaseA.not_pow_of_orderOf hp ha hω (Nat.pow_succ_factorization_not_dvd (by omega) hp)
  have hŷp' : ((ŷ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) ^ p =
      Matrix.scalar (Fin p) (ω : K) := by
    rw [← Units.val_pow_eq_pow_val, hŷp, GeneralLinearGroup.coe_scalar]
  have hdet := I292CaseA.not_pow_det hp hp2 hŷp' hωnp
  set eP := e.trans (I292CaseA.statedEquivL p K) with heP
  have hxθ : I292CaseA.thetaP L eP x = conjAut p K ŷ := I292CaseA.thetaP_eq_conjAut e ŷ hact
  have hxL : x ∉ L := by
    intro hx
    have h1 := I292CaseA.thetaP_of_mem L eP ⟨x, hx⟩
    rw [hxθ] at h1
    exact I292CaseA.conjAut_not_mem_inner hn3 ŷ hdet ⟨_, h1.symm⟩
  obtain ⟨φ, -, hφπ⟩ := exists_cover_linear hp hp5 hGA hq hZp hn3 eP
  haveI hperfS : Group.IsPerfect (SpecialLinearGroup (Fin p) K) :=
    LinearGroups.special_linear_isPerfect (by omega) (Or.inl hn3)
  have hφker : ∀ k ∈ φ.ker, k ∈ scalars p K := fun k hk => by
    apply proj_eq_one_iff.1
    rw [← hφπ k, MonoidHom.mem_ker.1 hk]
    simp
  have hker : ∀ k ∈ φ.ker, ∀ s : SpecialLinearGroup (Fin p) K, k * s = s * k := by
    intro k hk s
    have hkc : k ∈ Subgroup.center (SpecialLinearGroup (Fin p) K) :=
      scalars_le_center p K (hφker k hk)
    exact (Subgroup.mem_center_iff.1 hkc s).symm
  set cy : SpecialLinearGroup (Fin p) K →* SpecialLinearGroup (Fin p) K :=
    (slConjugation p K ŷ).toMonoidHom with hcydef
  have hdesc : l212in_descend eP (MulAut.conjNormal x) = conjAut p K ŷ := hxθ
  have hπcy : ∀ s, proj p K (cy s) = l212in_descend eP (MulAut.conjNormal x) (proj p K s) :=
    fun s => by
      rw [hdesc]
      exact (conjAut_proj ŷ s).symm
  have hcy : ∀ s, x * (φ s : Y) * x⁻¹ = (φ (cy s) : Y) := fun s => by
    have h1 := l212in_alpha_phi eP (proj p K) φ hφπ (MulAut.conjNormal x) cy hπcy s
    have h2 := congrArg Subtype.val h1
    simpa [MulAut.conjNormal_apply] using h2
  have hcyscal : ∀ k ∈ scalars p K, cy k = k := by
    intro k hk
    obtain ⟨c0, -, hk0⟩ := mem_scalars.1 hk
    apply Subtype.ext
    show ((slConjugation p K ŷ k : SpecialLinearGroup (Fin p) K) : Matrix (Fin p) (Fin p) K) = k
    rw [coe_slConjugation, hk0,
      ← (Matrix.scalar_commute (c0 : K) (fun _ => Commute.all _ _)
        ((ŷ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)).eq, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  have hcyker : ∀ k ∈ φ.ker, cy k = k := fun k hk => hcyscal k (hφker k hk)
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_units])
  have hτp : τ ^ p = 1 := by
    have := pow_orderOf_eq_one τ
    rwa [hτ] at this
  have hτ1 : τ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hτ
    exact hp.one_lt.ne hτ
  have hτK : (τ : K) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hτp, Units.val_one]
  set ζ : SpecialLinearGroup (Fin p) K :=
    scalarElement (n := p) (K := K) τ⁻¹ (by rw [inv_pow, hτp, inv_one]) with hζdef
  have hζmem : ζ ∈ scalars p K := scalarElement_mem_scalars _ _
  have hζc : ∀ s, ζ * s = s * ζ := fun s =>
    (Subgroup.mem_center_iff.1 (scalars_le_center p K hζmem) s).symm
  have hζp : ζ ^ p = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hζdef, coe_scalarElement, ← map_pow,
      ← Units.val_pow_eq_pow_val, inv_pow, hτp, inv_one]
    simp
  have hζ1 : ζ ≠ 1 := by
    intro h
    have h' := congrArg (fun s : SpecialLinearGroup (Fin p) K =>
      (s : Matrix (Fin p) (Fin p) K) ⟨0, hp.pos⟩ ⟨0, hp.pos⟩) h
    simp only [hζdef, coe_scalarElement, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at h'
    exact hτ1 (inv_eq_one.1 (Units.ext h'))
  have hcyζ : cy ζ = ζ := hcyscal ζ hζmem
  obtain ⟨Φm, hΦdet, hΦp', hΦM⟩ :=
    exists_twist hp (hp.odd_of_ne_two hp2) hŷp' hωnp hτK
  set Φ : SpecialLinearGroup (Fin p) K := ⟨Φm, hΦdet⟩ with hΦdef
  have hΦp : Φ ^ p = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow]
    exact hΦp')
  have hcyΦ : cy Φ = ζ * Φ := by
    apply Subtype.ext
    show ((slConjugation p K ŷ Φ : SpecialLinearGroup (Fin p) K) : Matrix (Fin p) (Fin p) K) =
      ((ζ * Φ : SpecialLinearGroup (Fin p) K) : Matrix (Fin p) (Fin p) K)
    rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul, hζdef, coe_scalarElement,
      Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    have h1 : ((ŷ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) * Φm =
        ((τ : K))⁻¹ • (Φm * ((ŷ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)) := by
      rw [hΦM, smul_smul, inv_mul_cancel₀ τ.ne_zero, one_smul]
    show ((ŷ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) * Φm *
      ((ŷ⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = ((τ⁻¹ : Kˣ) : K) • Φm
    rw [h1, Matrix.smul_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one,
      Units.val_inv_eq_inv_val]
  have hκ : ∀ g ∈ centralizer ({x} : Set Y), ∃ Ã : SpecialLinearGroup (Fin p) K →*
      SpecialLinearGroup (Fin p) K,
      (∀ s, (φ (Ã s) : Y) = g * (φ s : Y) * g⁻¹) ∧ Ã ζ = ζ := by
    intro g hg
    have hgx : g * x = x * g := mem_centralizer_singleton_iff.1 hg
    have hα : l212in_descend eP (MulAut.conjNormal g) * conjAut p K ŷ =
        conjAut p K ŷ * l212in_descend eP (MulAut.conjNormal g) := by
      rw [← hdesc, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hgx]
    obtain ⟨Ã, hπÃ, hÃζ⟩ := lift_kappa hp hn3 hŷp' hωnp _ hα
    refine ⟨Ã, fun s => ?_, hÃζ ζ hζmem⟩
    have h1 := l212in_alpha_phi eP (proj p K) φ hφπ (MulAut.conjNormal g) Ã hπÃ s
    have h2 := congrArg Subtype.val h1
    simpa [MulAut.conjNormal_apply] using h2.symm
  exact hasNormalPComplement_of_cover hp2 hxord hYD.rank_cent L hxL φ hker cy hcy hcyker ζ Φ
    hζc hζp hζ1 hcyζ hcyΦ hΦp hκ

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291N
