module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonInn

open CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.Held Matrix
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup map_fixSubgroup_le
  le_map_fixSubgroup_of_perfect)

theorem component_psu_fixed (hScal : UniScalar) {K : Type} [Field K] [Finite K] {Q d : ℕ}
    {τ : K ≃+* K} (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q) (hK : Nat.card K = Q ^ 2)
    (h2 : (2 : K) = 0) (hd : 3 ≤ d) (hdQ : (d, Q) ≠ (3, 2))
    (A : GL (Fin d) K) (hA : A ∈ heldGU d K τ hτ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (u : MulAut (LargeEvenProj (StatedSU d Q K)))
    (hu : ∀ h h' : ↥(StatedSU d Q K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSU d Q K) h) = LargeEvenProjMk (StatedSU d Q K) h')
    (hpow : u ^ p = 1) (J : Subgroup (LargeEvenProj (StatedSU d Q K)))
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup u)) :
    (∃ (a dd : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ' : E ≃+* E) (hτ' : ∀ x, τ' (τ' x) = x),
        2 ≤ a ∧ (∀ x : E, τ' x = x ^ (Q ^ dd)) ∧ Nat.card E = (Q ^ dd) ^ 2 ∧
        Nonempty (J ⧸ Subgroup.center J ≃* heldSU a E τ' hτ' ⧸ Subgroup.center (heldSU a E τ' hτ'))) ∨
    (∃ (b e : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ b ∧ Nat.card E = Q ^ (2 * e) ∧
        Nonempty (J ⧸ Subgroup.center J ≃* StatedProj (StatedSL b E))) := by
  have hH : heldSU d K τ hτ = StatedSU d Q K := hct_heldSU_eq_statedSU (a := d) hτQ
  have hnorm : ∀ g : GL (Fin d) K, g ∈ heldGU d K τ hτ → ∀ x ∈ StatedSU d Q K,
      g * x * g⁻¹ ∈ StatedSU d Q K := by
    intro g hg x hx
    rw [← hH] at hx ⊢
    exact heldSU_normal_in_heldGU hτ g hg x hx
  let cA : MulAut ↥(StatedSU d Q K) :=
    uniConjSub (StatedSU d Q K) A (hnorm A hA) (hnorm A⁻¹ (inv_mem hA))
  have hpowk : ∀ (k : ℕ) (h h' : ↥(StatedSU d Q K)),
      (h' : GL (Fin d) K) = A ^ k * (h : GL (Fin d) K) * (A ^ k)⁻¹ →
      (u ^ k) (LargeEvenProjMk (StatedSU d Q K) h) = LargeEvenProjMk (StatedSU d Q K) h' := by
    intro k
    induction k with
    | zero =>
      intro h h' hk
      have : h' = h := by
        apply Subtype.ext
        simpa using hk
      subst this
      simp
    | succ k ih =>
      intro h h' hk
      have step1 : u (LargeEvenProjMk (StatedSU d Q K) h) = LargeEvenProjMk (StatedSU d Q K) (cA h) :=
        hu h (cA h) rfl
      have step2 := ih (cA h) h' (by
        rw [hk, uniConjSub_apply_val, pow_succ]
        group)
      rw [pow_succ, MulAut.mul_apply, step1, step2]
  have hAp : A ^ p ∈ heldGU d K τ hτ := pow_mem hA p
  have hconjB : ∀ g : GL (Fin d) K, g ∈ StatedSU d Q K → ∃ c : K,
      ((A ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) *
        (((A ^ p)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = c • (g : Matrix (Fin d) (Fin d) K) := by
    intro g hg
    let h : ↥(StatedSU d Q K) := ⟨g, hg⟩
    let h' : ↥(StatedSU d Q K) := ⟨A ^ p * g * (A ^ p)⁻¹, hnorm (A ^ p) hAp g hg⟩
    have hk : (h' : GL (Fin d) K) = A ^ p * (h : GL (Fin d) K) * (A ^ p)⁻¹ := rfl
    have hmk : LargeEvenProjMk (StatedSU d Q K) h' = LargeEvenProjMk (StatedSU d Q K) h := by
      have h1 := hpowk p h h' hk
      rw [hpow] at h1
      simpa using h1.symm
    obtain ⟨c, hc⟩ := (projMk_eq_iff_uni (StatedSU d Q K) h' h).mp hmk
    have hh' : (h' : GL (Fin d) K) = (h : GL (Fin d) K) * (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := by
      rw [hc]
      group
    have hGL : A ^ p * g * (A ^ p)⁻¹ = g * (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := hh'
    refine ⟨(c : K)⁻¹, ?_⟩
    have hM := congrArg (fun X : GL (Fin d) K => (X : Matrix (Fin d) (Fin d) K)) hGL
    simp only [Units.val_mul] at hM
    rw [hM, ← map_inv, CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.val_scalar_gl, Units.val_inv_eq_inv_val,
      Matrix.mul_smul, Matrix.mul_one]
  obtain ⟨c0, hc0⟩ := hScal K Q d τ hτ hτQ hK hd hdQ (A ^ p) hconjB
  have hodd : Odd (orderOf A) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.odd_orderOf_of_pow_scalar h2 (by omega) A
      (hp.odd_of_ne_two hp2) hc0
  have hord : ((orderOf A : ℕ) : K) ≠ 0 :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.cast_orderOf_ne_zero_of_odd h2 A hodd
  have hker := ker_projMk_uni_le_center (StatedSU d Q K)
  have hαβ : ∀ k, LargeEvenProjMk (StatedSU d Q K) (cA k) = u (LargeEvenProjMk (StatedSU d Q K) k) :=
    fun k => (hu k (cA k) rfl).symm
  have hJle : J ≤ (fixSubgroup cA).map (LargeEvenProjMk (StatedSU d Q K)) :=
    le_map_fixSubgroup_of_perfect _ hker cA u hαβ QuotientGroup.mk_surjective hJ.1
      (CFSG.LocalAnalysis.GLTheoremA.I142N.comm_self_eq_of_commutator_top hJ.2.2.1)
  have hJc : CFSG.Open.IsComponentOf J ((fixSubgroup cA).map (LargeEvenProjMk (StatedSU d Q K))) :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_of_le hJ hJle
      (map_fixSubgroup_le _ hker cA u hαβ)
  obtain ⟨M, hMc, hMJ⟩ := CFSG.LocalAnalysis.GLTheoremA.I142N.exists_component_lift _
    (fun g hg => hker (MonoidHom.mem_ker.2 hg)) hJc
  have hMinj : Function.Injective (StatedSU d Q K).subtype := Subtype.val_injective
  have hcomp : CFSG.Open.IsComponentOf (M.map (StatedSU d Q K).subtype)
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ StatedSU d Q K) := by
    rw [← map_fixSubgroup_uniConjSub (StatedSU d Q K) A (hnorm A hA) (hnorm A⁻¹ (inv_mem hA))]
    refine CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map _ (fun g hg => ?_) hMc
    rw [show g = 1 from hMinj (by rw [hg, map_one])]
    exact one_mem _
  have hcompH : CFSG.Open.IsComponentOf (M.map (StatedSU d Q K).subtype)
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ heldSU d K τ hτ) := by
    rw [hH]
    exact hcomp
  have hcompGU := isComponentOf_centralizer_gu_of_su hτ A hcompH
  have hsized := held_unitary_components_gu_sized SUComponentsTrivial_holds SLComponentsTrivial_holds hτ
    hτQ hK A hA hord (M.map (StatedSU d Q K).subtype) hcompGU
  have hperf : commutator ↥(M.map (StatedSU d Q K).subtype) = ⊤ := hcomp.2.2.1
  have hmemJ : ∀ x : ↥M, LargeEvenProjMk (StatedSU d Q K) (x : ↥(StatedSU d Q K)) ∈ J := fun x => by
    rw [← hMJ]
    exact Subgroup.mem_map_of_mem _ x.2
  let fJ : ↥M →* ↥J := MonoidHom.codRestrict ((LargeEvenProjMk (StatedSU d Q K)).comp M.subtype) J hmemJ
  have hfJ : Function.Surjective fJ := by
    rintro ⟨y, hy⟩
    rw [← hMJ] at hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨z, hz⟩, rfl⟩
  have hkerJ : fJ.ker ≤ Subgroup.center ↥M := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hπ : LargeEvenProjMk (StatedSU d Q K) (x : ↥(StatedSU d Q K)) = 1 := congrArg Subtype.val hx
    have hxc : (x : ↥(StatedSU d Q K)) ∈ Subgroup.center ↥(StatedSU d Q K) :=
      ker_projMk_uni_le_center (StatedSU d Q K) (MonoidHom.mem_ker.mpr hπ)
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.mp hxc _
  let e : ↥M ≃* ↥(M.map (StatedSU d Q K).subtype) := Subgroup.equivMapOfInjective M _ hMinj
  let f' : ↥(M.map (StatedSU d Q K).subtype) →* ↥J := fJ.comp e.symm.toMonoidHom
  have hsurj' : Function.Surjective f' := hfJ.comp e.symm.surjective
  have hker' : f'.ker ≤ Subgroup.center ↥(M.map (StatedSU d Q K).subtype) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hw : (e.symm x : ↥M) ∈ fJ.ker := by
      rw [MonoidHom.mem_ker]
      exact hx
    have hwc := hkerJ hw
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    have hx' : x = e (e.symm x) := (e.apply_symm_apply x).symm
    rw [hx', ← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_center_iff.mp hwc z
  obtain ⟨φ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective hperf f' hsurj' hker'
  rcases hsized with ⟨a, dd, E, hE, hEfin, τ', hτ', ha2, hτ'Q, hcardE, ⟨eM⟩⟩ |
    ⟨b, e', E, hE, hEfin, ha2, hcardE, ⟨eM⟩⟩
  · exact Or.inl ⟨a, dd, E, hE, hEfin, τ', hτ', ha2, hτ'Q, hcardE, ⟨φ.trans eM⟩⟩
  · exact Or.inr ⟨b, e', E, hE, hEfin, ha2, hcardE, ⟨φ.trans eM⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.CanonInn

end
