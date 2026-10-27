module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291NilpAbs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291NilpKappaUni
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291NilpUniTwist
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBUni

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291N

open Polynomial Subgroup Matrix CFSG.Open
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LieType.Universal.Unitary (conjTr SUid mem_SUid)
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry (Uid mem_Uid_iff)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.RankFourTheoremC (l212in_descend l212in_alpha_phi exists_cover_unitary
  l212in_suConj l212in_suConj_coe l212in_suPhi l212in_suPhi_mk l212in_conj_scalar
  scalar_mem_statedSU_iff)

theorem kd291Nilp_uni (hGA : CFSG.Open.GriessAllModelsStatement) {p : ℕ} {Y : Type} [Group Y]
    [Finite Y] {P : Subgroup Y} {x z : Y} {L : Subgroup Y} (hcfg : LinUniCfg p P x z L)
    (hmodel : LinUniModelUni p x L) :
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
  obtain ⟨q, K, instF, instFin, e, ŷ, ω, hK, hpq, hŷu, hŷp, hω, hact⟩ := hmodel
  have hq2 : 2 ≤ q := by
    have := Nat.le_of_dvd (by omega) hpq
    omega
  obtain ⟨r, f, rfl, ⟨hU⟩⟩ := I292CaseA.exists_unitaryFieldData hK hq2
  haveI : Fact r.Prime := ⟨hU.prime⟩
  haveI : CharP K r := hU.charP
  have hn1 : 1 ≤ p := by omega
  have hq3 : ¬(p = 3 ∧ r ^ f = 2) := fun ⟨h3, _⟩ => by omega
  have hŷU : ŷ ∈ primeFormUnitary hU ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) := by
    rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one]
    exact hŷu
  have hŷp' : ((ŷ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) ^ p =
      Matrix.scalar (Fin p) (ω : K) := by
    rw [← Units.val_pow_eq_pow_val, hŷp, GeneralLinearGroup.coe_scalar]
  have hωnp : ∀ b : K, b ^ p ≠ (ω : K) := I292CaseA.not_pow_omega hp hp2 hpq hK hω
  have hdet := I292CaseA.not_pow_det hp hp2 hŷp' hωnp
  have hxθ : I292CaseA.thetaP L (e.trans (I292CaseA.statedEquiv hU hn1)) x =
      primeFormConjHom hU _ ⟨ŷ, hŷU⟩ := I292CaseA.thetaP_eq_conjHom hU hn1 e ŷ hŷU hact
  have hxL : x ∉ L := by
    intro hx
    have h1 := I292CaseA.thetaP_of_mem L (e.trans (I292CaseA.statedEquiv hU hn1)) ⟨x, hx⟩
    rw [hxθ] at h1
    exact I292CaseB.conjHom_not_mem_inner hU hn3 hq3 ⟨ŷ, hŷU⟩ hdet ⟨_, h1.symm⟩
  have hŷB : ŷ ∈ Uid (unitaryInvolution K r f) p := by
    rw [mem_Uid_iff]
    have : conjTr (unitaryInvolution K r f) (ŷ : Matrix (Fin p) (Fin p) K) =
        ((ŷ : Matrix (Fin p) (Fin p) K).map (· ^ (r ^ f)))ᵀ := by
      ext i j
      simp [conjTr, unitaryInvolution_apply, iterateFrobenius_def]
    rw [this]
    exact hŷu
  set ŷB : Uid (unitaryInvolution K r f) p := ⟨ŷ, hŷB⟩ with hŷBdef
  obtain ⟨φ, -, hφπ⟩ := exists_cover_unitary hp hp5 hGA hq hZp hp5 hK e
  haveI hperfS : Group.IsPerfect (StatedSU p (r ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK (by omega) (by
      intro h
      simp only [Prod.mk.injEq] at h
      omega)
  set π := QuotientGroup.mk' ((StatedScalars (Fin p) K).subgroupOf (StatedSU p (r ^ f) K))
    with hπdef
  have hker1 : ∀ k ∈ φ.ker,
      k ∈ (StatedScalars (Fin p) K).subgroupOf (StatedSU p (r ^ f) K) := by
    intro k hk
    have h1 : (QuotientGroup.mk k : StatedProj (StatedSU p (r ^ f) K)) = 1 := by
      rw [← hφπ k, MonoidHom.mem_ker.1 hk]
      simp
    exact (QuotientGroup.eq_one_iff k).1 h1
  have hker : ∀ k ∈ φ.ker, ∀ s : StatedSU p (r ^ f) K, k * s = s * k := fun k hk s =>
    (Subgroup.mem_center_iff.1
      (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _ (hker1 k hk)) s).symm
  set cy : StatedSU p (r ^ f) K →* StatedSU p (r ^ f) K :=
    (l212in_suConj hK ŷB).toMonoidHom with hcydef
  have hdesc : l212in_descend e (MulAut.conjNormal x) = l212in_suPhi hK ŷB := by
    ext z
    obtain ⟨w, rfl⟩ := e.surjective z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨A, hA⟩ := QuotientGroup.mk_surjective (e (QuotientGroup.mk g))
    rw [l212in_descend_apply, ← hA, l212in_suPhi_mk]
    exact hact g (MulAut.conjNormal x g) A (l212in_suConj hK ŷB A)
      (by simp [MulAut.conjNormal_apply]) hA.symm (l212in_suConj_coe hK ŷB A)
  have hπcy : ∀ s, π (cy s) = l212in_descend e (MulAut.conjNormal x) (π s) := fun s => by
    rw [hdesc]
    exact (l212in_suPhi_mk hK ŷB s).symm
  have hcy : ∀ s, x * (φ s : Y) * x⁻¹ = (φ (cy s) : Y) := fun s => by
    have h1 := l212in_alpha_phi e π φ hφπ (MulAut.conjNormal x) cy hπcy s
    have h2 := congrArg Subtype.val h1
    simpa [MulAut.conjNormal_apply] using h2
  have hcyscal : ∀ k ∈ (StatedScalars (Fin p) K).subgroupOf (StatedSU p (r ^ f) K),
      cy k = k := by
    intro k hk
    obtain ⟨c0, hc0⟩ := Subgroup.mem_subgroupOf.1 hk
    apply Subtype.ext
    show (ŷ : GL (Fin p) K) * (k : GL (Fin p) K) * (ŷ : GL (Fin p) K)⁻¹ = (k : GL (Fin p) K)
    rw [← hc0, l212in_conj_scalar]
  have hcyker : ∀ k ∈ φ.ker, cy k = k := fun k hk => hcyscal k (hker1 k hk)
  obtain ⟨τ, hτprim, hστ⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.I294OD.od_exists_zeta hp hK hpq
  have hτp : τ ^ p = 1 := hτprim.pow_eq_one
  have hτ0 : τ ≠ 0 := hτprim.ne_zero hp.ne_zero
  have hτ1 : τ ≠ 1 := hτprim.ne_one hp.one_lt
  set τu : Kˣ := Units.mk0 τ hτ0 with hτu
  have hτup : τu ^ p = 1 := Units.ext (by simpa [hτu] using hτp)
  have hτuq : τu ^ (r ^ f + 1) = 1 := by
    obtain ⟨m, hm⟩ := hpq
    rw [hm, pow_mul, hτup, one_pow]
  have hζS : GeneralLinearGroup.scalar (Fin p) τu⁻¹ ∈ StatedSU p (r ^ f) K :=
    (scalar_mem_statedSU_iff hK hn1 τu⁻¹).2 ⟨by rw [inv_pow, hτup, inv_one],
      by rw [inv_pow, hτuq, inv_one]⟩
  set ζ : StatedSU p (r ^ f) K := ⟨GeneralLinearGroup.scalar (Fin p) τu⁻¹, hζS⟩ with hζdef
  have hζmem : ζ ∈ (StatedScalars (Fin p) K).subgroupOf (StatedSU p (r ^ f) K) :=
    Subgroup.mem_subgroupOf.2 ⟨τu⁻¹, rfl⟩
  have hζc : ∀ s, ζ * s = s * ζ := fun s =>
    (Subgroup.mem_center_iff.1
      (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _ hζmem) s).symm
  have hζp : ζ ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hζdef]
    show (GeneralLinearGroup.scalar (Fin p) τu⁻¹) ^ p = 1
    rw [← map_pow, inv_pow, hτup, inv_one, map_one]
  have hζ1 : ζ ≠ 1 := by
    intro h
    have h1 := congrArg (fun s : StatedSU p (r ^ f) K =>
      ((s : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) ⟨0, hp.pos⟩ ⟨0, hp.pos⟩) h
    simp only [hζdef, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Subgroup.coe_one, Units.val_one, Matrix.one_apply_eq] at h1
    have h3 : τu⁻¹ = 1 := Units.ext (by rw [Units.val_one]; exact h1)
    have h2 : τu = 1 := inv_eq_one.1 h3
    exact hτ1 (by simpa [hτu] using congrArg (fun u : Kˣ => (u : K)) h2)
  have hcyζ : cy ζ = ζ := hcyscal ζ hζmem
  haveI : Fact (Irreducible (X ^ p - C (ω : K) : K[X])) :=
    ⟨X_pow_sub_C_irreducible_of_prime hp hωnp⟩
  have hωq : (ω : K) ^ (r ^ f + 1) = 1 := by
    have h2 : orderOf ω ∣ r ^ f + 1 := by
      rw [hω]
      exact Nat.ordProj_dvd _ _
    have h3 := congrArg Units.val (orderOf_dvd_iff_pow_eq_one.1 h2)
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h3
  have hSet : CFSG.LocalAnalysis.RankFourTheoremC.I294OD.OdSetup r f p (ω : K)
      (unitaryInvolution K r f) (ŷ : GL (Fin p) K) :=
    ⟨hŷB, ω.ne_zero, hŷp', fun k => unitaryInvolution_apply K r f k,
      CFSG.LieType.BorelTits.unitaryInvolution_involutive hK, hK, hp.odd_of_ne_two hp2, hpq, hωq⟩
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨b, hb, hBb⟩ := exists_orbit_basis hSet hσ
  obtain ⟨Φm, hΦU, hΦdet, hΦp', hΦB⟩ := exists_twist_uni hp (hp.odd_of_ne_two hp2)
    (CFSG.LieType.BorelTits.unitaryInvolution_involutive hK) hb hBb hτp
    (by rw [hστ, inv_mul_cancel₀ hτ0])
  have hΦne : Φm.det ≠ 0 := by rw [hΦdet]; exact one_ne_zero
  have hΦmem : Matrix.GeneralLinearGroup.mkOfDetNeZero Φm hΦne ∈ StatedSU p (r ^ f) K := by
    rw [← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK p,
      CFSG.LieType.Universal.Unitary.mem_SUid]
    exact ⟨by simpa using hΦdet, by simpa using hΦU⟩
  set Φ : StatedSU p (r ^ f) K := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Φm hΦne, hΦmem⟩
    with hΦdef
  have hΦp : Φ ^ p = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    simpa [hΦdef] using hΦp'
  have hcyΦ : cy Φ = ζ * Φ := by
    apply Subtype.ext
    apply Units.ext
    have h1 : (ŷ : Matrix (Fin p) (Fin p) K) * Φm =
        (τ : K)⁻¹ • (Φm * (ŷ : Matrix (Fin p) (Fin p) K)) := hΦB
    show (((ŷ : GL (Fin p) K) * (Φ : GL (Fin p) K) * (ŷ : GL (Fin p) K)⁻¹ : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K) =
      (((GeneralLinearGroup.scalar (Fin p) τu⁻¹ * (Φ : GL (Fin p) K) : GL (Fin p) K)) :
        Matrix (Fin p) (Fin p) K)
    rw [Units.val_mul, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
    have hΦcoe : ((Φ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = Φm := rfl
    rw [hΦcoe, h1, Matrix.smul_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one,
      Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    simp [hτu]
  have hκ : ∀ g ∈ centralizer ({x} : Set Y), ∃ Ã : StatedSU p (r ^ f) K →*
      StatedSU p (r ^ f) K,
      (∀ s, (φ (Ã s) : Y) = g * (φ s : Y) * g⁻¹) ∧ Ã ζ = ζ := by
    intro g hg
    have hgx : g * x = x * g := mem_centralizer_singleton_iff.1 hg
    have hα : l212in_descend e (MulAut.conjNormal g) * l212in_suPhi hK ŷB =
        l212in_suPhi hK ŷB * l212in_descend e (MulAut.conjNormal g) := by
      rw [← hdesc, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hgx]
    obtain ⟨Ã, hπÃ, hÃζ⟩ := lift_kappa_uni hp5 hK hŷp' hωnp _ hα
    refine ⟨Ã, fun s => ?_, hÃζ ζ hζmem⟩
    have h1 := l212in_alpha_phi e π φ hφπ (MulAut.conjNormal g) Ã hπÃ s
    have h2 := congrArg Subtype.val h1
    simpa [MulAut.conjNormal_apply] using h2.symm
  exact hasNormalPComplement_of_cover hp2 hxord hYD.rank_cent L hxL φ hker cy hcy hcyker ζ Φ
    hζc hζp hζ1 hcyζ hcyΦ hΦp hκ

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291N
