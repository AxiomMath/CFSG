module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundNonCommUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenBaseW
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenTypeOneW
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShCompDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryScalar
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.T171Sh
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

theorem uniTypeOneW_nonComm
    {G : Type} [Group G] [Finite G] {p N n : ℕ} {L J A : Subgroup G} {d b : G}
    {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 n K) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hN : 3 ≤ N) (hNq : (N, 2 ^ n) ≠ (3, 2))
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 n K N)}
    {hact : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (unitarySU 2 n K N)) (LargeEvenGUSet (Fin N) K (2 ^ n)),
      LargeEvenInduces θ (conjRel a) φ}
    {hS : LargeEvenGUSet (Fin N) K (2 ^ n) ⊆ Subgroup.normalizer
      (unitarySU 2 n K N : Set (GL (Fin N) K))}
    (hsetup : WSetup p L J A d b)
    (M : LiftMap (L := L) (A := A) (S := LargeEvenGUSet (Fin N) K (2 ^ n)) θ hact hS)
    (hc : ∃ c : Kˣ, (M.mat ⟨d, hsetup.d_mem⟩) ^ p =
      Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ p))
    (hnc : M.mat ⟨b, hsetup.b_mem⟩ * M.mat ⟨d, hsetup.d_mem⟩ ≠
      M.mat ⟨d, hsetup.d_mem⟩ * M.mat ⟨b, hsetup.b_mem⟩) : False := by
  classical
  obtain ⟨c, hc⟩ := hc
  set s : GL (Fin N) K := Matrix.GeneralLinearGroup.scalar (Fin N) c⁻¹ with hsdef
  set D : GL (Fin N) K := s * M.mat ⟨d, hsetup.d_mem⟩ with hDdef
  set Mb : GL (Fin N) K := M.mat ⟨b, hsetup.b_mem⟩ with hMbdef
  have hs : s ∈ LargeEvenScalars (Fin N) K := by
    rw [largeEvenScalars_def]
    exact ⟨c⁻¹, rfl⟩
  have hDgu : D ∈ LargeEvenGUSet (Fin N) K (2 ^ n) :=
    scalar_mul_mem_guSet h (M.mem ⟨d, hsetup.d_mem⟩) c⁻¹
  have hBgu : Mb ∈ LargeEvenGUSet (Fin N) K (2 ^ n) := M.mem ⟨b, hsetup.b_mem⟩
  have hsMd : s * M.mat ⟨d, hsetup.d_mem⟩ = M.mat ⟨d, hsetup.d_mem⟩ * s :=
    (Subgroup.mem_center_iff.mp (TableB.scalar_mem_center c⁻¹)
      (M.mat ⟨d, hsetup.d_mem⟩)).symm
  have hDpow : D ^ p = 1 := by
    have hsp : s ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) ((c⁻¹ : Kˣ) ^ p) :=
      (map_pow (Matrix.GeneralLinearGroup.scalar (Fin N)) c⁻¹ p).symm
    rw [show D = s * M.mat ⟨d, hsetup.d_mem⟩ from rfl,
      Commute.mul_pow hsMd p, hsp, hc, ← map_mul, inv_pow, inv_mul_cancel, map_one]
  have hDnorm : D ∈ Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K)) :=
    TableBUE.gu_subset_normalizer h hDgu
  have hDind : LargeEvenInduces θ (conjRel d)
      (TableB.projConj (unitarySU 2 n K N) ⟨D, hDnorm⟩) := by
    have hsub : (⟨D, hDnorm⟩ :
          Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K))) =
        (⟨s, TableB.scalar_mem_normalizer (unitarySU 2 n K N) hs⟩ :
          Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K))) *
        ⟨M.mat ⟨d, hsetup.d_mem⟩, hS (M.mem ⟨d, hsetup.d_mem⟩)⟩ := Subtype.ext rfl
    have hscalar : TableB.projConj (unitarySU 2 n K N)
        (⟨s, TableB.scalar_mem_normalizer (unitarySU 2 n K N) hs⟩ :
          Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K))) = 1 :=
      TableB.projConj_of_scalar (unitarySU 2 n K N) hs
    rw [hsub, map_mul, hscalar, one_mul]
    exact M.ind ⟨d, hsetup.d_mem⟩
  have hA : D ∈ primeFormUnitary h (idGram K N) :=
    mem_primeFormUnitary_of_gu_pow_eq_one (h := h) (by omega) hDgu hDpow hp hsetup.odd hpq
  have hAnorm : A ≤ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S11.le_normalizer_of_innerDiag hsetup.idiag
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := hAnorm hsetup.d_mem
  let α : MulAut ↥L := L.normalizerMonoidHom ⟨d⁻¹, Subgroup.inv_mem _ hdN⟩
  let π : ↥L →* StatedProj (StatedSU N (2 ^ n) K) := piCenterQuot θ
  set JP : Subgroup (StatedProj (StatedSU N (2 ^ n) K)) :=
    (J.subgroupOf L).map π with hJPdef
  have hJ0 : GLAPComponent p (fixSubgroup α) (J.subgroupOf L) := by
    have hfix : fixSubgroup α = (L ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L := by
      rw [show α = L.normalizerMonoidHom ⟨d⁻¹, Subgroup.inv_mem _ hdN⟩ from rfl]
      rw [fixSubgroup_normalizerMonoidHom]
      congr 1
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨hxL, hx⟩
        refine ⟨hxL, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
        have hx' : x = d⁻¹ * x * d := by
          have := congrArg (fun t => t * d) hx
          simpa [mul_assoc] using this
        have := congrArg (fun t => d * t) hx'
        simpa [mul_assoc] using this.symm
      · rintro ⟨hxL, hx⟩
        refine ⟨hxL, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
        have hx' : x = d * x * d⁻¹ := by
          have := congrArg (fun t => t * d⁻¹) hx
          simpa [mul_assoc] using this
        have := congrArg (fun t => d⁻¹ * t) hx'
        simpa [mul_assoc] using this.symm
    rw [hfix]
    exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Prop126b.glaPComponent_subgroupOf hp
      inf_le_left hsetup.pcomp
  have hcompat : ∀ x : ↥L, π (α x) = TableB.projConj (unitarySU 2 n K N) ⟨D, hDnorm⟩ (π x) := by
    intro x
    have hrel : conjRel d x (α x) := by
      rw [conjRel]
      show ((α x : ↥L) : G) = d⁻¹ * (x : G) * d
      rw [show α = L.normalizerMonoidHom ⟨d⁻¹, Subgroup.inv_mem _ hdN⟩ from rfl,
        Subgroup.normalizerMonoidHom_apply_apply_coe]
      simp
    exact (hDind x (α x) hrel).symm
  have hπsurj : Function.Surjective π := by
    intro y
    obtain ⟨q, rfl⟩ := θ.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨x, rfl⟩
  have hπker : π.ker ≤ Subgroup.center ↥L := by
    rw [show π.ker = Subgroup.center ↥L from by
      dsimp only [π, piCenterQuot]
      rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center ↥L))
        θ.toMonoidHom θ.injective, QuotientGroup.ker_mk']]
  have hJP : GLAPComponent p (fixSubgroup (TableB.projConj (unitarySU 2 n K N) ⟨D, hDnorm⟩)) JP :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_fixSubgroup π hπker α
      (TableB.projConj (unitarySU 2 n K N) ⟨D, hDnorm⟩) hcompat hπsurj hp hJ0
  have hu : ∀ g g' : ↥(StatedSU N (2 ^ n) K),
      (g' : GL (Fin N) K) = D * (g : GL (Fin N) K) * D⁻¹ →
      TableB.projConj (unitarySU 2 n K N) ⟨D, hDnorm⟩
        (LargeEvenProjMk (unitarySU 2 n K N) g) =
      LargeEvenProjMk (unitarySU 2 n K N) g' := by
    intro g g' hgg
    change TableB.projConj (unitarySU 2 n K N) ⟨D, hDnorm⟩
      ((g : LargeEvenProj (unitarySU 2 n K N))) =
      LargeEvenProjMk (unitarySU 2 n K N) g'
    rw [TableB.projConj_mk]
    apply congrArg (LargeEvenProjMk (unitarySU 2 n K N))
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, ← hgg]
  obtain ⟨H, a, hblocks⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K155X.l154_uni_good_block h.one_le hN h hp hsetup.odd D hA
      (by rw [hDpow, map_one]) (TableB.projConj (unitarySU 2 n K N) ⟨D, hDnorm⟩) hu JP hJP
  let x : Module.End K (Fin N → K) := Matrix.GeneralLinearGroup.toLin D
  let xL : LinearMap.GeneralLinearGroup K (Fin N → K) := Matrix.GeneralLinearGroup.toLin D
  let dlin : (Fin N → K) ≃ₗ[K] (Fin N → K) := (Matrix.GeneralLinearGroup.toLin D).toLinearEquiv
  have hlinpow : (Matrix.GeneralLinearGroup.toLin D) ^ p = 1 := by
    rw [← map_pow, hDpow, map_one]
  have hpow_to : ∀ k : ℕ, ((Matrix.GeneralLinearGroup.toLin D) ^ k).toLinearEquiv =
      ((Matrix.GeneralLinearGroup.toLin D).toLinearEquiv) ^ k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ, pow_succ, LinearMap.GeneralLinearGroup.toLinearEquiv_mul, ih]
  have hxpow : dlin ^ p = 1 := by
    have h := congrArg LinearMap.GeneralLinearGroup.toLinearEquiv hlinpow
    rw [hpow_to p] at h
    have h1 : LinearMap.GeneralLinearGroup.toLinearEquiv (1 : LinearMap.GeneralLinearGroup K
        (Fin N → K)) = 1 := rfl
    rw [h1] at h
    simpa [dlin] using h
  have hcardK : Nat.card K = (2 ^ n) ^ 2 := by
    rw [h.card, show 2 * n = n * 2 by omega, pow_mul]
  have hpdvd : p ∣ Nat.card K - 1 := by
    rw [hcardK]
    refine hpq.trans ?_
    rw [show (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) by
      simpa [mul_comm] using (Nat.sq_sub_sq (2 ^ n) 1)]
    exact dvd_mul_right _ _
  haveI : CharP K 2 := h.charP
  obtain ⟨ε, hεp, haeq⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T173S.exists_eq_X_sub_C_of_mem_primaryFactors hp hpdvd hxpow
      (h := a.1.1) (by
        have hmem : a.1.1 ∈ RankThree.PartOne.KCPrimary.primaryFactors
            ((Matrix.GeneralLinearGroup.toLin D : Module.End K (Fin N → K))) := a.1.2
        exact hmem)
  have hεval : (ε : K) ^ p = 1 := by simpa using congrArg Units.val hεp
  have hεbar : h.bar (ε : K) = (ε : K)⁻¹ := by
    rw [h.bar_apply]
    have h1 : (ε : K) ^ (2 ^ n + 1) = 1 := by
      obtain ⟨k, hk⟩ := hpq
      rw [hk, pow_mul, hεval, one_pow]
    have h2 : (ε : K) ^ (2 ^ n) * (ε : K) = 1 := by
      rwa [← pow_succ]
    have h3 := congrArg (fun t : K => t * (ε : K)⁻¹) h2
    simpa [mul_assoc] using h3
  have hdual : dualPoly h.bar (X - C (ε : K)) = X - C (ε : K) := by
    rw [CFSG.RankThree.PartOne.KCUnitaryBlock.dualPoly_X_sub_C]
    · congr 2
      rw [hεbar, inv_inv]
    · rw [hεbar]
      exact inv_ne_zero (Units.ne_zero ε)
  have hεne : (ε : K) ≠ 0 := Units.ne_zero ε
  have hsMb : s * Mb = Mb * s :=
    (Subgroup.mem_center_iff.mp (TableB.scalar_mem_center c⁻¹) Mb).symm
  have hscentral : ∀ X : GL (Fin N) K, s * X = X * s := fun X =>
    Matrix.GeneralLinearGroup.scalar_commute c⁻¹ X
  have hcommScal : Mb * D * Mb⁻¹ * D⁻¹ ∈ LargeEvenScalars (Fin N) K := by
    have h1 : Mb * D * Mb⁻¹ * D⁻¹ =
        Mb * M.mat ⟨d, hsetup.d_mem⟩ * Mb⁻¹ * (M.mat ⟨d, hsetup.d_mem⟩)⁻¹ := by
      calc Mb * D * Mb⁻¹ * D⁻¹
          = Mb * (s * M.mat ⟨d, hsetup.d_mem⟩) * Mb⁻¹ *
              (s * M.mat ⟨d, hsetup.d_mem⟩)⁻¹ := rfl
        _ = Mb * (s * M.mat ⟨d, hsetup.d_mem⟩) * Mb⁻¹ *
              ((M.mat ⟨d, hsetup.d_mem⟩)⁻¹ * s⁻¹) := by rw [mul_inv_rev]
        _ = Mb * s * M.mat ⟨d, hsetup.d_mem⟩ * Mb⁻¹ *
              (M.mat ⟨d, hsetup.d_mem⟩)⁻¹ * s⁻¹ := by group
        _ = s * Mb * M.mat ⟨d, hsetup.d_mem⟩ * Mb⁻¹ *
              (M.mat ⟨d, hsetup.d_mem⟩)⁻¹ * s⁻¹ := by rw [hscentral Mb]
        _ = s * (Mb * M.mat ⟨d, hsetup.d_mem⟩ * Mb⁻¹ *
              (M.mat ⟨d, hsetup.d_mem⟩)⁻¹) * s⁻¹ := by group
        _ = (s * (Mb * M.mat ⟨d, hsetup.d_mem⟩ * Mb⁻¹ *
              (M.mat ⟨d, hsetup.d_mem⟩)⁻¹)) * s⁻¹ := by rw [mul_assoc]
        _ = ((Mb * M.mat ⟨d, hsetup.d_mem⟩ * Mb⁻¹ *
              (M.mat ⟨d, hsetup.d_mem⟩)⁻¹) * s) * s⁻¹ := by rw [hscentral]
        _ = (Mb * M.mat ⟨d, hsetup.d_mem⟩ * Mb⁻¹ *
              (M.mat ⟨d, hsetup.d_mem⟩)⁻¹) := by rw [mul_assoc, mul_inv_cancel, mul_one]
    rw [h1]
    exact M.commutator_mem_scalars_of_wSetup hsetup ⟨b, hsetup.b_mem⟩
      (uniKernelScalar h hN hNq hp hpq)
  rw [largeEvenScalars_def] at hcommScal
  obtain ⟨ζ, hζ⟩ := hcommScal
  have hcommDef : Mb * D * Mb⁻¹ * D⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) ζ := hζ.symm
  have hconj : Mb * D * Mb⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) ζ * D := by
    calc Mb * D * Mb⁻¹ = (Mb * D * Mb⁻¹ * D⁻¹) * D := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin N) ζ * D := by rw [hcommDef]
  have hζne : ζ ≠ 1 := by
    intro hζ1
    have hcommD : Mb * D = D * Mb := by
      have h1 : Mb * D * Mb⁻¹ = D := by
        rw [hζ1, map_one, one_mul] at hconj
        exact hconj
      calc Mb * D = (Mb * D * Mb⁻¹) * Mb := by group
        _ = D * Mb := by rw [h1]
    have h1 : s * (Mb * M.mat ⟨d, hsetup.d_mem⟩) =
        s * (M.mat ⟨d, hsetup.d_mem⟩ * Mb) := by
      calc s * (Mb * M.mat ⟨d, hsetup.d_mem⟩)
          = (s * Mb) * M.mat ⟨d, hsetup.d_mem⟩ := by rw [mul_assoc]
        _ = (Mb * s) * M.mat ⟨d, hsetup.d_mem⟩ := by rw [hsMb]
        _ = Mb * (s * M.mat ⟨d, hsetup.d_mem⟩) := by rw [mul_assoc]
        _ = Mb * D := rfl
        _ = D * Mb := hcommD
        _ = (s * M.mat ⟨d, hsetup.d_mem⟩) * Mb := rfl
        _ = (M.mat ⟨d, hsetup.d_mem⟩ * s) * Mb := by rw [hsMd]
        _ = M.mat ⟨d, hsetup.d_mem⟩ * (s * Mb) := by rw [mul_assoc]
        _ = M.mat ⟨d, hsetup.d_mem⟩ * (Mb * s) := by rw [hsMb]
        _ = (M.mat ⟨d, hsetup.d_mem⟩ * Mb) * s := by rw [mul_assoc]
        _ = s * (M.mat ⟨d, hsetup.d_mem⟩ * Mb) := (hscentral _).symm
    exact hnc (mul_left_cancel h1)
  haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hζp : ζ ^ p = 1 := by
    have hpow := congrArg (fun X : GL (Fin N) K => X ^ p) hconj
    have hconjpow : ∀ k : ℕ, (Mb * D * Mb⁻¹) ^ k = Mb * D ^ k * Mb⁻¹ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ih, pow_succ]; group
    have hcommS : Commute (Matrix.GeneralLinearGroup.scalar (Fin N) ζ) D :=
      (commute_iff_eq _ _).mpr (Matrix.GeneralLinearGroup.scalar_commute ζ D)
    have hL : (Mb * D * Mb⁻¹) ^ p = 1 := by
      simpa [hDpow] using hconjpow p
    have hR : (Matrix.GeneralLinearGroup.scalar (Fin N) ζ * D) ^ p =
        Matrix.GeneralLinearGroup.scalar (Fin N) (ζ ^ p) := by
      rw [hcommS.mul_pow, map_pow, hDpow, mul_one]
    rw [hL, hR] at hpow
    have hinj : Function.Injective
        (Matrix.GeneralLinearGroup.scalar (Fin N) : Kˣ → GL (Fin N) K) := by
      intro a b hab
      have h1 : Matrix.scalar (Fin N) (a : K) = Matrix.scalar (Fin N) (b : K) := by
        simpa only [Matrix.GeneralLinearGroup.coe_scalar] using congrArg Units.val hab
      exact Units.ext (Matrix.scalar_inj.mp h1)
    exact hinj (by simpa using hpow.symm)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hζprim : IsPrimitiveRoot ζ p :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hζp hζne)
  have hMD : Mb * D = Matrix.GeneralLinearGroup.scalar (Fin N) ζ * D * Mb := by
    calc Mb * D = (Mb * D * Mb⁻¹) * Mb := by group
      _ = (Matrix.GeneralLinearGroup.scalar (Fin N) ζ * D) * Mb := by rw [hconj]
  have hDM : D * Mb = Matrix.GeneralLinearGroup.scalar (Fin N) ζ⁻¹ * Mb * D := by
    have h1 : Matrix.GeneralLinearGroup.scalar (Fin N) ζ⁻¹ * (Mb * D) = D * Mb := by
      calc Matrix.GeneralLinearGroup.scalar (Fin N) ζ⁻¹ * (Mb * D)
          = Matrix.GeneralLinearGroup.scalar (Fin N) ζ⁻¹ *
              (Matrix.GeneralLinearGroup.scalar (Fin N) ζ * D * Mb) := by rw [hMD]
        _ = (Matrix.GeneralLinearGroup.scalar (Fin N) ζ⁻¹ *
              Matrix.GeneralLinearGroup.scalar (Fin N) ζ) * D * Mb := by group
        _ = D * Mb := by rw [← map_mul, inv_mul_cancel, map_one, one_mul]
    rw [← h1, ← mul_assoc]
  let Glin : (Fin N → K) ≃ₗ[K] (Fin N → K) :=
    (Matrix.GeneralLinearGroup.toLin Mb).toLinearEquiv
  have hGx : ∀ v : Fin N → K, x (Glin v) = (ζ : K)⁻¹ • Glin (x v) := by
    intro v
    have hmat : (D : Matrix (Fin N) (Fin N) K) * (Mb : Matrix (Fin N) (Fin N) K) =
        (ζ : K)⁻¹ • ((Mb : Matrix (Fin N) (Fin N) K) *
          (D : Matrix (Fin N) (Fin N) K)) := by
      have hval := congrArg (fun X : GL (Fin N) K => (X : Matrix (Fin N) (Fin N) K)) hDM
      have hdiaginv : (Matrix.diagonal (fun _ : Fin N => (ζ : K)))⁻¹ =
          (ζ : K)⁻¹ • (1 : Matrix (Fin N) (Fin N) K) := by
        rw [Matrix.inv_eq_right_inv]
        ext i j
        by_cases hij : i = j
        · subst hij
          simp [Matrix.diagonal, Matrix.one_apply, Matrix.smul_apply, Units.ne_zero ζ]
        · simp [Matrix.diagonal, Matrix.one_apply, Matrix.smul_apply, hij]
      simpa [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        hdiaginv, Matrix.smul_mul, Matrix.one_mul] using hval
    have hvec : (D : Matrix (Fin N) (Fin N) K).mulVec
        ((Mb : Matrix (Fin N) (Fin N) K).mulVec v) =
        (ζ : K)⁻¹ • (Mb : Matrix (Fin N) (Fin N) K).mulVec
          ((D : Matrix (Fin N) (Fin N) K).mulVec v) := by
      calc (D : Matrix (Fin N) (Fin N) K).mulVec
            ((Mb : Matrix (Fin N) (Fin N) K).mulVec v)
          = ((D : Matrix (Fin N) (Fin N) K) *
              (Mb : Matrix (Fin N) (Fin N) K)).mulVec v := by rw [← Matrix.mulVec_mulVec]
        _ = ((ζ : K)⁻¹ • ((Mb : Matrix (Fin N) (Fin N) K) *
              (D : Matrix (Fin N) (Fin N) K))).mulVec v := by rw [hmat]
        _ = (ζ : K)⁻¹ • ((Mb : Matrix (Fin N) (Fin N) K) *
              (D : Matrix (Fin N) (Fin N) K)).mulVec v := by rw [Matrix.smul_mulVec]
        _ = (ζ : K)⁻¹ • (Mb : Matrix (Fin N) (Fin N) K).mulVec
              ((D : Matrix (Fin N) (Fin N) K).mulVec v) := by rw [Matrix.mulVec_mulVec]
    simpa [x, Glin, Matrix.GeneralLinearGroup.toLin_apply,
      LinearMap.GeneralLinearGroup.coe_toLinearEquiv] using hvec
  have hmem_shift : ∀ ν : K, ∀ v ∈ primaryComponent x (X - C ν),
      Glin v ∈ primaryComponent x (X - C ((ζ : K)⁻¹ * ν)) := by
    intro ν v hv
    rw [mem_primaryComponent_X_sub_C] at hv ⊢
    rw [hGx, hv, map_smul, smul_smul]
  have hmem_inv_shift : ∀ v ∈ primaryComponent x (X - C (ε : K)),
      Glin.symm v ∈ primaryComponent x (X - C ((ζ : K) * (ε : K))) := by
    intro v hv
    rw [mem_primaryComponent_X_sub_C] at hv ⊢
    have h1 : Glin (x (Glin.symm v)) = ((ζ : K) * (ε : K)) • Glin (Glin.symm v) := by
      have h2 := hGx (Glin.symm v)
      rw [LinearEquiv.apply_symm_apply, hv] at h2
      have h3 := congrArg (fun w : Fin N → K => (ζ : K) • w) h2
      simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using h3.symm
    have h4 := congrArg (fun w : Fin N → K => Glin.symm w) h1
    simpa using h4
  let F : Subgroup (LinearMap.GeneralLinearGroup K (Fin N → K)) :=
    specialBlock (idForm h N) xL (a.1 : K[X])
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.one_le
  have hFq : CFSG.IsQuasisimple ↥F :=
    (specialBlockFacts_of_good H hq2 (x := xL) a.1 a.2).quasisimple a.2.1
  have hF_support : ∀ g ∈ F, ∀ b ∈ primaryFactors x, b ≠ (a.1 : K[X]) →
      ∀ v ∈ primaryComponent x b, (g : Module.End K (Fin N → K)) v = v := by
    intro g hg b hb hbne v hv
    have horbit := specialBlock_le_orbitFactor hg
    have hmem : g ∈ supportedUnitary (idForm h N) xL ({(a.1 : K[X])} : Set K[X]) := by
      simpa [F, orbitFactor, haeq, hdual] using horbit
    exact hmem.2 b hb (by simpa using hbne) v hv
  have hex_nonscalar : ∃ g ∈ F, ¬ ∃ c : K, ∀ v ∈ primaryComponent x (a.1 : K[X]),
      (g : Module.End K (Fin N → K)) v = c • v := by
    by_contra h
    rw [not_exists] at h
    have hscalar : ∀ g ∈ F, ∃ c : K, ∀ v ∈ primaryComponent x (a.1 : K[X]),
        (g : Module.End K (Fin N → K)) v = c • v := by
      intro g hg
      by_contra hg'
      exact h g ⟨hg, hg'⟩
    have hcommF : ∀ g ∈ F, ∀ h' ∈ F, g * h' = h' * g := by
      intro g hg h' hh'
      apply Units.ext
      apply ext_primaryComponent H.squarefree
      intro b hb v hv
      by_cases hba : b = (a.1 : K[X])
      · subst hba
        obtain ⟨cg, hcg⟩ := hscalar g hg
        obtain ⟨ch, hch⟩ := hscalar h' hh'
        show (((g * h' : LinearMap.GeneralLinearGroup K (Fin N → K)) : Module.End K _) v) =
          (((h' * g : LinearMap.GeneralLinearGroup K (Fin N → K)) : Module.End K _) v)
        rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
          hch v hv, hcg v hv,
          hcg (ch • v) (Submodule.smul_mem _ ch hv),
          hch (cg • v) (Submodule.smul_mem _ cg hv)]
        rw [smul_smul, smul_smul, mul_comm]
      · rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
          hF_support h' hh' b hb hba v hv]
        have hgc : Commute ((g : LinearMap.GeneralLinearGroup K (Fin N → K)) :
            Module.End K (Fin N → K)) (xL : Module.End K (Fin N → K)) :=
          mem_gl_centralizer.mp (orbitFactor_le_gl_centralizer
            (specialBlock_le_orbitFactor hg))
        have hgv : ((g : LinearMap.GeneralLinearGroup K (Fin N → K)) :
            Module.End K (Fin N → K)) v ∈ primaryComponent x b :=
          apply_mem_primaryComponent hgc hv
        rw [hF_support h' hh' b hb hba ((g : Module.End K (Fin N → K)) v) hgv]
    have htriv : ∀ g : ↥F, g = 1 := by
      intro g
      exact eq_one_of_perfect_of_comm hFq.1 (fun a b => Subtype.ext (hcommF a.1 a.2 b.1 b.2))
        (MonoidHom.id ↥F) g
    obtain ⟨u, v, huv⟩ := hFq.2.2
    haveI : Subsingleton ↥F := ⟨fun x y => by rw [htriv x, htriv y]⟩
    haveI : Subsingleton (↥F ⧸ Subgroup.center ↥F) := inferInstance
    exact huv (Subsingleton.elim (u * v) (v * u))
  obtain ⟨gF, hgF, hgF_non⟩ := hex_nonscalar
  have hgF_sesq : gF ∈ sesqSpecialUnitaryGroup (idForm h N) :=
    specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq2 a.1 a.2 hgF
  obtain ⟨gSU, hgSU_eq⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.mem_range_toLinSU
      hgF_sesq
  let gGL : GL (Fin N) K := gSU
  have hgGL_SU : gGL ∈ unitarySU 2 n K N := by
    rw [unitarySU_eq_gramSU]
    exact gSU.2
  have htoLin : Matrix.GeneralLinearGroup.toLin gGL = gF := by
    change (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.toLinSU
      h N gSU : LinearMap.GeneralLinearGroup K (Fin N → K)) = gF
    exact hgSU_eq
  have hgGL_non : ¬ ∃ c : K, ∀ v ∈ primaryComponent x (a.1 : K[X]),
      ((Matrix.GeneralLinearGroup.toLin gGL : Module.End K (Fin N → K)) v) = c • v := by
    intro hc
    apply hgF_non
    obtain ⟨c, hc⟩ := hc
    refine ⟨c, fun v hv => ?_⟩
    have h1 : ((Matrix.GeneralLinearGroup.toLin gGL : Module.End K (Fin N → K)) v) =
        ((gF : Module.End K (Fin N → K)) v) :=
      congrArg (fun x : LinearMap.GeneralLinearGroup K (Fin N → K) =>
        (x : Module.End K (Fin N → K)) v) htoLin
    exact h1.symm.trans (hc v hv)
  have hMbNorm : Mb ∈ Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K)) :=
    hS hBgu
  let β : MulAut (StatedProj (StatedSU N (2 ^ n) K)) :=
    TableB.projConj (unitarySU 2 n K N) ⟨Mb, hMbNorm⟩
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hAnorm hsetup.b_mem
  have hbInvN : b⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hbN
  have hbInvJ : ∀ y ∈ J, b⁻¹ * y * b ∈ J := fun y hy =>
    (by simpa using
      (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hsetup.b_norm) y).1 hy)
  have hbJ : ∀ y ∈ J, b * y * b⁻¹ ∈ J := fun y hy =>
    (Subgroup.mem_normalizer_iff.1 hsetup.b_norm y).1 hy
  have hmap_le : JP.map β.toMonoidHom ≤ JP := by
    rintro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    rw [hJPdef] at hw
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hw
    have hyL : (y : G) ∈ L := y.2
    have hyJ : (y : G) ∈ J := hy
    have hmemL : b⁻¹ * (y : G) * b ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.1 hbInvN (y : G)).1 hyL
    have hmemJ : b⁻¹ * (y : G) * b ∈ J := hbInvJ (y : G) hyJ
    let yinv : ↥L := ⟨b⁻¹ * (y : G) * b, hmemL⟩
    have hrel : conjRel b y yinv := by
      rw [conjRel]
    have hind := M.ind ⟨b, hsetup.b_mem⟩ y yinv hrel
    rw [hJPdef]
    exact Subgroup.mem_map.mpr ⟨yinv, Subgroup.mem_subgroupOf.mpr hmemJ,
      by simpa [π, piCenterQuot, β] using hind.symm⟩
  have hle_map : JP ≤ JP.map β.toMonoidHom := by
    intro z hz
    rw [hJPdef] at hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
    have hyL : (y : G) ∈ L := y.2
    have hyJ : (y : G) ∈ J := hy
    have hmemL : b * (y : G) * b⁻¹ ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.1 hbN (y : G)).1 hyL
    have hmemJ : b * (y : G) * b⁻¹ ∈ J := hbJ (y : G) hyJ
    let yconj : ↥L := ⟨b * (y : G) * b⁻¹, hmemL⟩
    have hrel : conjRel b yconj y := by
      rw [conjRel]
      show (y : G) = b⁻¹ * (b * (y : G) * b⁻¹) * b
      group
    have hind := M.ind ⟨b, hsetup.b_mem⟩ yconj y hrel
    refine Subgroup.mem_map.mpr ⟨π yconj, ?_, by simpa [π, piCenterQuot, β] using hind⟩
    rw [hJPdef]
    exact Subgroup.mem_map.mpr ⟨yconj, Subgroup.mem_subgroupOf.mpr hmemJ, rfl⟩
  have hmap_eq : JP.map β.toMonoidHom = JP := le_antisymm hmap_le hle_map
  let gU : ↥(unitarySU 2 n K N) := ⟨gGL, hgGL_SU⟩
  let z : StatedProj (StatedSU N (2 ^ n) K) := LargeEvenProjMk (unitarySU 2 n K N) gU
  have hzJP : z ∈ JP := by
    rw [hblocks]
    exact ⟨gGL, by rw [htoLin]; exact hgF, hgGL_SU, rfl⟩
  have hzmap : z ∈ JP.map β.toMonoidHom := by rw [hmap_eq]; exact hzJP
  obtain ⟨z', hz'JP, hz'eq⟩ := Subgroup.mem_map.1 hzmap
  rw [hblocks] at hz'JP
  obtain ⟨g₀, hg₀F, hg₀SU, hg₀eq⟩ := hz'JP
  let g₀U : ↥(unitarySU 2 n K N) := ⟨g₀, hg₀SU⟩
  let h' : ↥(unitarySU 2 n K N) :=
    (unitarySU 2 n K N).normalizerMonoidHom ⟨Mb, hMbNorm⟩ g₀U
  have hh'β : β z' = LargeEvenProjMk (unitarySU 2 n K N) h' := by
    rw [← hg₀eq]
    exact TableB.projConj_mk (unitarySU 2 n K N) ⟨Mb, hMbNorm⟩ g₀U
  have hquot : LargeEvenProjMk (unitarySU 2 n K N) h' =
      LargeEvenProjMk (unitarySU 2 n K N) gU := by
    calc LargeEvenProjMk (unitarySU 2 n K N) h'
        = β z' := hh'β.symm
      _ = z := hz'eq
      _ = LargeEvenProjMk (unitarySU 2 n K N) gU := rfl
  have hscalar : ∃ lam : Kˣ, (h' : GL (Fin N) K) =
      Matrix.GeneralLinearGroup.scalar (Fin N) lam * gGL := by
    have hmem : h'⁻¹ * gU ∈ (LargeEvenScalars (Fin N) K).subgroupOf
        (unitarySU 2 n K N) :=
      (QuotientGroup.eq (s := (LargeEvenScalars (Fin N) K).subgroupOf
        (unitarySU 2 n K N))).mp hquot
    rw [Subgroup.mem_subgroupOf, largeEvenScalars_def] at hmem
    obtain ⟨lam, hlam⟩ := hmem
    have hvalGL0 : (↑(h'⁻¹ * gU) : GL (Fin N) K) =
        Matrix.GeneralLinearGroup.scalar (Fin N) lam := hlam.symm
    have hvalGL : (h' : GL (Fin N) K)⁻¹ * gGL =
        Matrix.GeneralLinearGroup.scalar (Fin N) lam := by
      simpa using hvalGL0
    refine ⟨lam⁻¹, ?_⟩
    have h1 : gGL = (h' : GL (Fin N) K) * Matrix.GeneralLinearGroup.scalar (Fin N) lam := by
      calc gGL = (h' : GL (Fin N) K) * ((h' : GL (Fin N) K)⁻¹ * gGL) := by group
        _ = (h' : GL (Fin N) K) * Matrix.GeneralLinearGroup.scalar (Fin N) lam := by
          rw [hvalGL]
    have h2 : (h' : GL (Fin N) K) =
        gGL * (Matrix.GeneralLinearGroup.scalar (Fin N) lam)⁻¹ := by
      rw [h1]; group
    rw [h2, ← map_inv]
    exact (commute_iff_eq _ _).mpr (Matrix.GeneralLinearGroup.scalar_commute lam⁻¹ gGL).symm
  have hlininv : (Matrix.GeneralLinearGroup.toLin Mb)⁻¹ =
      Matrix.GeneralLinearGroup.toLin (Mb⁻¹) := by
    rw [← map_inv]
  have hGsymm : Glin.symm =
      (Matrix.GeneralLinearGroup.toLin (Mb⁻¹)).toLinearEquiv := rfl
  have hGsymmV : ∀ v : Fin N → K,
      (Matrix.GeneralLinearGroup.toLin (Mb⁻¹) : Module.End K (Fin N → K)) v =
        Glin.symm v := by
    intro v
    rfl
  have hh'val : (h' : GL (Fin N) K) = Mb * g₀ * Mb⁻¹ := by
    change ((unitarySU 2 n K N).normalizerMonoidHom ⟨Mb, hMbNorm⟩ g₀U :
      ↥(unitarySU 2 n K N)) = Mb * g₀ * Mb⁻¹
    rfl
  have hfac_a : (X - C (ε : K)) ∈ primaryFactors x := by
    have h := a.1.2
    rwa [haeq] at h
  have hVεne : primaryComponent x (X - C (ε : K)) ≠ ⊥ :=
    primaryComponent_ne_bot H.squarefree hfac_a
  obtain ⟨v0, hv0, hv0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVεne
  have hw0 : Glin.symm v0 ∈ primaryComponent x (X - C ((ζ : K) * (ε : K))) :=
    hmem_inv_shift v0 hv0
  have hw0ne : Glin.symm v0 ≠ 0 := by
    intro h
    apply hv0ne
    have := congrArg Glin h
    simpa using this
  have hfac_shift : (X - C ((ζ : K) * (ε : K))) ∈ primaryFactors x := by
    have hev : x.HasEigenvalue ((ζ : K) * (ε : K)) := by
      refine Module.End.hasEigenvalue_of_hasEigenvector (f := x)
        (μ := (ζ : K) * (ε : K)) ⟨?_, hw0ne⟩
      exact Module.End.mem_eigenspace_iff.mpr (mem_primaryComponent_X_sub_C.mp hw0)
    exact X_sub_C_mem_primaryFactors hev
  have hfac_ne : (X - C ((ζ : K) * (ε : K))) ≠ X - C (ε : K) := by
    intro h
    have hcoeff : (ζ : K) * (ε : K) = (ε : K) := by
      have := congrArg (fun p : K[X] => p.coeff 0) h
      simpa using this
    have hζval : (ζ : K) = 1 := by
      have h1 : (ζ : K) * (ε : K) = (1 : K) * (ε : K) := by simpa using hcoeff
      exact mul_right_cancel₀ (Units.ne_zero ε) h1
    exact hζne (Units.ext hζval)
  have hh'_triv : ∀ v ∈ primaryComponent x (X - C (ε : K)),
      (Matrix.GeneralLinearGroup.toLin (h' : GL (Fin N) K) : Module.End K (Fin N → K)) v = v := by
    intro v hv
    have hfac_ne' : X - C ((ζ : K) * (ε : K)) ≠ (a.1 : K[X]) := by rwa [haeq]
    have hg₀_triv : (Matrix.GeneralLinearGroup.toLin g₀ : Module.End K (Fin N → K))
        (Glin.symm v) = Glin.symm v :=
      hF_support (Matrix.GeneralLinearGroup.toLin g₀) (by simpa [F] using hg₀F)
        (X - C ((ζ : K) * (ε : K)))
        hfac_shift hfac_ne' (Glin.symm v) (hmem_inv_shift v hv)
    calc (Matrix.GeneralLinearGroup.toLin (h' : GL (Fin N) K) : Module.End K (Fin N → K)) v
        = (Matrix.GeneralLinearGroup.toLin Mb : Module.End K (Fin N → K))
            ((Matrix.GeneralLinearGroup.toLin g₀ : Module.End K (Fin N → K))
            ((Matrix.GeneralLinearGroup.toLin (Mb⁻¹) : Module.End K (Fin N → K)) v)) := by
          rw [hh'val, map_mul, map_mul, Units.val_mul, Units.val_mul,
            Module.End.mul_apply, Module.End.mul_apply]
      _ = (Matrix.GeneralLinearGroup.toLin Mb : Module.End K (Fin N → K))
            ((Matrix.GeneralLinearGroup.toLin g₀ : Module.End K (Fin N → K))
            (Glin.symm v)) := by rw [hGsymmV]
      _ = (Matrix.GeneralLinearGroup.toLin Mb : Module.End K (Fin N → K))
            (Glin.symm v) := by rw [hg₀_triv]
      _ = v := by
        rw [show (Matrix.GeneralLinearGroup.toLin Mb : Module.End K (Fin N → K))
          (Glin.symm v) = Glin (Glin.symm v) from rfl,
          LinearEquiv.apply_symm_apply]
  obtain ⟨lam, hlam⟩ := hscalar
  apply hgGL_non
  refine ⟨(lam : K)⁻¹, fun v hv => ?_⟩
  have hv' : v ∈ primaryComponent x (X - C (ε : K)) := by rwa [haeq] at hv
  have h1 := hh'_triv v hv'
  rw [hlam] at h1
  have h1' : (Matrix.diagonal (fun _ : Fin N => (lam : K))).mulVec
      ((gGL : Matrix (Fin N) (Fin N) K).mulVec v) = v := by
    simpa [Matrix.GeneralLinearGroup.toLin_apply, Units.val_mul,
      Matrix.mulVec_mulVec, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply] using h1
  have h1'' : (lam : K) • ((gGL : Matrix (Fin N) (Fin N) K).mulVec v) = v := by
    funext i
    have := congrFun h1' i
    simpa [Matrix.mulVec_diagonal] using this
  have h2 := congrArg (fun w : Fin N → K => (lam : K)⁻¹ • w) h1''
  simpa [smul_smul, inv_mul_cancel₀ (Units.ne_zero lam)] using h2

theorem t158UniTypeOneW_of_block (hUB : UniBlockInnDiag) : T158UniTypeOneW := by
  intro G _ _ p N n L J A d b K _ _ h hp hpq hN hNq θ hact hS hw _ hnonID M hc
  by_cases hcomm : M.mat ⟨b, hw.b_mem⟩ * M.mat ⟨d, hw.d_mem⟩ =
      M.mat ⟨d, hw.d_mem⟩ * M.mat ⟨b, hw.b_mem⟩
  · exact uniTypeOne_commuting_of_wSetup hUB h hp hpq hN hNq hw hnonID M hc hcomm
  · exact uniTypeOneW_nonComm h hp hpq hN hNq hw M hc hcomm

end CFSG.LocalAnalysis.GLTheoremA.T158

end
