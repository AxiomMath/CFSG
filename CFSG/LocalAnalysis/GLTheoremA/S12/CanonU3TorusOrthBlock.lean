module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SympOrthOrthIdent
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3TorusSU3
public import CFSG.LocalAnalysis.StandardType.UnitaryCenterOrders

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3.OrthMinus

open Polynomial Module
open scoped Matrix
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

theorem commute_of_commute_specialMat {K : Type} [Field K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {y : V ≃ₗ[K] V} (hy : OddOrderIsometry Q 3 y) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors y.toLinearMap) (hself : h = reciprocalPolynomial h)
    {k : ℕ} (b : Basis (Fin k) (AdjoinRoot h) (primaryComponent y.toLinearMap h))
    (z : ↥(Subgroup.centralizer ({y} : Set (V ≃ₗ[K] V))))
    (g : ↥(specialBlock Q y h))
    (hc : Commute (toMatGL b (centralizerGL y h z)) (specialMat Q y h b g)) :
    Commute (z : V ≃ₗ[K] V) (g : V ≃ₗ[K] V) := by
  classical
  have hcomm : Commute (centralizerGL y h z) (specialBlockGL Q y h g) := by
    refine (toMatGL b).injective ?_
    rw [map_mul, map_mul]
    exact hc.eq
  have hcomm_end : ((centralizerGL y h z : BlockGL y h) : Module.End (AdjoinRoot h)
      (primaryComponent y.toLinearMap h)) * ((specialBlockGL Q y h g : BlockGL y h) :
        Module.End (AdjoinRoot h) (primaryComponent y.toLinearMap h)) =
      ((specialBlockGL Q y h g : BlockGL y h) : Module.End (AdjoinRoot h)
        (primaryComponent y.toLinearMap h)) * ((centralizerGL y h z : BlockGL y h) :
          Module.End (AdjoinRoot h) (primaryComponent y.toLinearMap h)) := by
    simpa only [Units.val_mul] using congrArg (fun u : BlockGL y h => (u : Module.End
      (AdjoinRoot h) (primaryComponent y.toLinearMap h))) hcomm.eq
  have hkey : ∀ u : primaryComponent y.toLinearMap h,
      (z : V ≃ₗ[K] V) ((g : V ≃ₗ[K] V) (u : V)) =
        (g : V ≃ₗ[K] V) ((z : V ≃ₗ[K] V) (u : V)) := by
    intro u
    have h1 := congrArg (fun w : primaryComponent y.toLinearMap h => (w : V))
      (congrArg (fun T : Module.End (AdjoinRoot h) (primaryComponent y.toLinearMap h) => T u)
        hcomm_end)
    rw [Module.End.mul_apply, Module.End.mul_apply] at h1
    have h2 : ∀ v : primaryComponent y.toLinearMap h,
        (((specialBlockGL Q y h g : BlockGL y h) : Module.End (AdjoinRoot h)
          (primaryComponent y.toLinearMap h)) v : V) = (g : V ≃ₗ[K] V) (v : V) := by
      intro v
      have hsp : specialBlockGL Q y h g =
          blockGL Q y h ((Subgroup.inclusion (specialBlock_le_supportedBlock h)) g) := rfl
      rw [hsp, coe_blockGL]
      rfl
    have h3 : ∀ v : primaryComponent y.toLinearMap h,
        (((centralizerGL y h z : BlockGL y h) : Module.End (AdjoinRoot h)
          (primaryComponent y.toLinearMap h)) v : V) = (z : V ≃ₗ[K] V) (v : V) :=
      fun v => coe_centralizerGL y h z v
    rw [h3, h2, h2, h3] at h1
    exact h1
  have hkey' : ∀ r ∈ othersSpace y.toLinearMap h,
      (z : V ≃ₗ[K] V) ((g : V ≃ₗ[K] V) r) =
        (g : V ≃ₗ[K] V) ((z : V ≃ₗ[K] V) r) := by
    intro r hr
    have hg : (g : V ≃ₗ[K] V) r = r :=
      (mem_supportedBlock.mp (specialBlock_le_supportedBlock h g.2)).2 r hr
    have hz : (z : V ≃ₗ[K] V) r ∈ othersSpace y.toLinearMap h :=
      mem_othersSpace_of_apply z.2 hr
    rw [hg, (mem_supportedBlock.mp (specialBlock_le_supportedBlock h g.2)).2 _ hz]
  refine LinearEquiv.ext fun v => ?_
  have horb : orbitSpace y.toLinearMap h = primaryComponent y.toLinearMap h := by
    rw [orbitSpace, ← hself, sup_idem]
  have hcompl : IsCompl (primaryComponent y.toLinearMap h) (othersSpace y.toLinearMap h) := by
    simpa only [horb] using hy.isCompl_orbit_others hh
  obtain ⟨u, hu, r, hr, rfl⟩ := CFSG.RankThree.PartOne.KCOrthogonal.exists_add_of_isCompl hcompl v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_add, map_add, map_add, map_add]
  rw [hkey ⟨u, hu⟩, hkey' r hr]

theorem toMatGL_centralizerGL_unitary {K : Type} [Field K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {y : V ≃ₗ[K] V} (hy : OddOrderIsometry Q 3 y) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors y.toLinearMap) {k : ℕ}
    (b : Basis (Fin k) (AdjoinRoot h) (primaryComponent y.toLinearMap h))
    (hb : ∀ γ : BlockGL y h, γ ∈ (blockGL Q y h).range ↔
      (((toMatGL b γ : Matrix.GeneralLinearGroup (Fin k) (AdjoinRoot h)) :
        Matrix (Fin k) (Fin k) (AdjoinRoot h)).map (· ^ Nat.card K))ᵀ *
        ((toMatGL b γ : Matrix.GeneralLinearGroup (Fin k) (AdjoinRoot h)) :
          Matrix (Fin k) (Fin k) (AdjoinRoot h)) = 1)
    {z : V ≃ₗ[K] V} (hz : z ∈ isometryCentralizer Q y) :
    (((toMatGL b (centralizerGL y h ⟨z, (Subgroup.mem_inf.mp hz).2⟩) :
        Matrix.GeneralLinearGroup (Fin k) (AdjoinRoot h)) :
          Matrix (Fin k) (Fin k) (AdjoinRoot h)).map (· ^ Nat.card K))ᵀ *
      ((toMatGL b (centralizerGL y h ⟨z, (Subgroup.mem_inf.mp hz).2⟩) :
        Matrix.GeneralLinearGroup (Fin k) (AdjoinRoot h)) :
          Matrix (Fin k) (Fin k) (AdjoinRoot h)) = 1 := by
  classical
  let zc : ↥(Subgroup.centralizer ({y} : Set (V ≃ₗ[K] V))) :=
    ⟨z, (Subgroup.mem_inf.mp hz).2⟩
  let gc : ↥(supportedBlock Q y h) :=
    ⟨(CFSG.RankThree.PartOne.KCOrthogonal.blockComponent hy zc h).1,
      hy.blockComponent_mem hz hh⟩
  have hzc : centralizerGL y h zc = blockGL Q y h gc := by
    refine Units.ext (LinearMap.ext fun v => Subtype.ext ?_)
    rw [coe_centralizerGL, coe_blockGL,
      CFSG.RankThree.PartOne.KCOrthogonal.blockComponent_apply_of_mem hy zc h hh v.2]
    simp
  have hgoal := (hb (blockGL Q y h gc)).mp ⟨gc, rfl⟩
  rw [← hzc] at hgoal
  simpa only [zc] using hgoal

theorem isSolvable_statedSU_of_isSolvable_specialBlock {K : Type} [Field K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {y : V ≃ₗ[K] V} (hy : OddOrderIsometry Q 3 y) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors y.toLinearMap) (hself : h = reciprocalPolynomial h)
    {k : ℕ} (b : Basis (Fin k) (AdjoinRoot h) (primaryComponent y.toLinearMap h))
    (ε : ↥(specialBlock Q y h) ≃* ↥(StatedSU k (Nat.card K) (AdjoinRoot h)))
    (hε : ∀ g, ((ε g : ↥(StatedSU k (Nat.card K) (AdjoinRoot h))) :
      Matrix.GeneralLinearGroup (Fin k) (AdjoinRoot h)) = specialMat Q y h b g)
    {z : V ≃ₗ[K] V} (hz : z ∈ isometryCentralizer Q y)
    (hsol : IsSolvable ↥(specialBlock Q y h ⊓
      Subgroup.centralizer ({z} : Set (V ≃ₗ[K] V)))) :
    IsSolvable ↥(StatedSU k (Nat.card K) (AdjoinRoot h) ⊓
      Subgroup.centralizer ({toMatGL b (centralizerGL y h
        ⟨z, (Subgroup.mem_inf.mp hz).2⟩)} :
          Set (Matrix.GeneralLinearGroup (Fin k) (AdjoinRoot h)))) := by
  classical
  let zc : ↥(Subgroup.centralizer ({y} : Set (V ≃ₗ[K] V))) :=
    ⟨z, (Subgroup.mem_inf.mp hz).2⟩
  let M : Matrix.GeneralLinearGroup (Fin k) (AdjoinRoot h) :=
    toMatGL b (centralizerGL y h zc)
  let ψ : ↥(StatedSU k (Nat.card K) (AdjoinRoot h) ⊓
      Subgroup.centralizer ({M} :
        Set (Matrix.GeneralLinearGroup (Fin k) (AdjoinRoot h)))) →*
      ↥(specialBlock Q y h) :=
    ε.symm.toMonoidHom.comp (Subgroup.inclusion inf_le_left)
  have hψ : ∀ A : ↥(StatedSU k (Nat.card K) (AdjoinRoot h) ⊓
      Subgroup.centralizer ({M} :
        Set (Matrix.GeneralLinearGroup (Fin k) (AdjoinRoot h)))),
      ψ A = ε.symm ⟨A.1, (Subgroup.mem_inf.mp A.2).1⟩ := fun A => rfl
  let ψV : ↥(StatedSU k (Nat.card K) (AdjoinRoot h) ⊓
      Subgroup.centralizer ({M} :
        Set (Matrix.GeneralLinearGroup (Fin k) (AdjoinRoot h)))) →* (V ≃ₗ[K] V) :=
    (specialBlock Q y h).subtype.comp ψ
  let φ : ↥(StatedSU k (Nat.card K) (AdjoinRoot h) ⊓
      Subgroup.centralizer ({M} :
        Set (Matrix.GeneralLinearGroup (Fin k) (AdjoinRoot h)))) →*
      ↥(specialBlock Q y h ⊓ Subgroup.centralizer ({z} : Set (V ≃ₗ[K] V))) :=
    ψV.codRestrict _ (fun A => by
      refine Subgroup.mem_inf.mpr ⟨(ψ A).2, ?_⟩
      have hMA : (A.1 : Matrix.GeneralLinearGroup (Fin k) (AdjoinRoot h)) * M =
          M * (A.1 : Matrix.GeneralLinearGroup (Fin k) (AdjoinRoot h)) :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp A.2).2
      have hsp : specialMat Q y h b (ψ A) =
          (A.1 : Matrix.GeneralLinearGroup (Fin k) (AdjoinRoot h)) := by
        rw [← hε (ψ A)]
        rw [hψ]
        simp
      have hc : Commute M (specialMat Q y h b (ψ A)) := by
        rw [hsp]
        exact hMA.symm
      have hAz : Commute z ((ψ A : ↥(specialBlock Q y h)) : V ≃ₗ[K] V) :=
        commute_of_commute_specialMat hy hh hself b zc (ψ A) hc
      exact Subgroup.mem_centralizer_singleton_iff.mpr hAz.eq.symm)
  have hψinj : Function.Injective ψ := by
    intro A B hAB
    have h1 : Subgroup.inclusion inf_le_left A = Subgroup.inclusion inf_le_left B :=
      ε.symm.injective hAB
    exact Subgroup.inclusion_injective inf_le_left h1
  have hinj : Function.Injective φ := by
    intro A B hAB
    apply hψinj
    apply Subtype.ext
    exact congrArg (fun x : ↥(specialBlock Q y h ⊓
      Subgroup.centralizer ({z} : Set (V ≃ₗ[K] V))) => (x : V ≃ₗ[K] V)) hAB
  haveI : Group.IsSolvable ↥(specialBlock Q y h ⊓
      Subgroup.centralizer ({z} : Set (V ≃ₗ[K] V))) := hsol
  exact Group.isSolvable_of_isSolvable_injective (f := φ) hinj

theorem not_isSolvable_and_of_specialBlock {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : Odd m) (hm2 : 2 ≤ m)
    {y y₁ y₂ : V ≃ₗ[K] V} (hy : OddOrderIsometry Q 3 y)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors y.toLinearMap)
    (hne1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h)
    (hk : primaryMultiplicity y.toLinearMap h = 3)
    (hy₁ : y₁ ∈ isometryCentralizer Q y) (hy₂ : y₂ ∈ isometryCentralizer Q y)
    (h₁ : y₁ ^ 3 = 1) (h₂ : y₂ ^ 3 = 1) (hc₁₂ : Commute y₁ y₂)
    (hmoves : ∀ k : ℕ, ∃ g ∈ specialBlock Q y h,
      g * (y₂ * y₁ ^ k) ≠ (y₂ * y₁ ^ k) * g) :
    ¬ (IsSolvable ↥(specialBlock Q y h ⊓
        Subgroup.centralizer ({y₁} : Set (V ≃ₗ[K] V))) ∧
      IsSolvable ↥(specialBlock Q y h ⊓
        Subgroup.centralizer ({y₂} : Set (V ≃ₗ[K] V)))) := by
  classical
  obtain ⟨hdeg, b, hb⟩ := exists_selfDual_matrix_data hy hh hne1 hself hk
  have hfin : finrank K (AdjoinRoot h) = h.natDegree := by
    rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
  have hcardE : Nat.card (AdjoinRoot h) = Nat.card K ^ h.natDegree := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot h), hfin]
  have hcardQ : Nat.card (AdjoinRoot h) = (2 ^ m) ^ 2 := by
    rw [hcardE, hdeg, hK]
  have hE : UnitaryFieldData 2 m (AdjoinRoot h) :=
    ⟨Nat.prime_two, by omega, by rw [hcardQ, ← pow_mul, mul_comm]⟩
  have hbar : (fun z : AdjoinRoot h => z ^ Nat.card K) = ⇑hE.bar := by
    funext c
    rw [UnitaryFieldData.bar_apply, hK]
  obtain ⟨ε, hε⟩ := exists_specialBlock_equiv_SU hy hh b hb
  let z₁ : ↥(Subgroup.centralizer ({y} : Set (V ≃ₗ[K] V))) :=
    ⟨y₁, (Subgroup.mem_inf.mp hy₁).2⟩
  let z₂ : ↥(Subgroup.centralizer ({y} : Set (V ≃ₗ[K] V))) :=
    ⟨y₂, (Subgroup.mem_inf.mp hy₂).2⟩
  set M₁ : Matrix.GeneralLinearGroup (Fin 3) (AdjoinRoot h) :=
    toMatGL b (centralizerGL y h z₁) with hM₁def
  set M₂ : Matrix.GeneralLinearGroup (Fin 3) (AdjoinRoot h) :=
    toMatGL b (centralizerGL y h z₂) with hM₂def
  have hu₁ : M₁ ∈ primeFormUnitary hE (idGram (AdjoinRoot h) 3) := by
    rw [hM₁def, mem_primeFormUnitary, ← hbar, idGram, Units.val_one, Matrix.mul_one]
    exact toMatGL_centralizerGL_unitary hy hh b hb hy₁
  have hu₂ : M₂ ∈ primeFormUnitary hE (idGram (AdjoinRoot h) 3) := by
    rw [hM₂def, mem_primeFormUnitary, ← hbar, idGram, Units.val_one, Matrix.mul_one]
    exact toMatGL_centralizerGL_unitary hy hh b hb hy₂
  have hz₁3 : z₁ ^ 3 = 1 := Subtype.ext (by simpa using h₁)
  have hz₂3 : z₂ ^ 3 = 1 := Subtype.ext (by simpa using h₂)
  have hM₁3 : M₁ ^ 3 = 1 := by
    have hcg : (centralizerGL y h z₁) ^ 3 = 1 := by
      rw [← map_pow, hz₁3, map_one]
    calc M₁ ^ 3 = (toMatGL b (centralizerGL y h z₁)) ^ 3 := by rw [hM₁def]
      _ = toMatGL b ((centralizerGL y h z₁) ^ 3) := (map_pow (toMatGL b) _ 3).symm
      _ = 1 := by rw [hcg, map_one]
  have hM₂3 : M₂ ^ 3 = 1 := by
    have hcg : (centralizerGL y h z₂) ^ 3 = 1 := by
      rw [← map_pow, hz₂3, map_one]
    calc M₂ ^ 3 = (toMatGL b (centralizerGL y h z₂)) ^ 3 := by rw [hM₂def]
      _ = toMatGL b ((centralizerGL y h z₂) ^ 3) := (map_pow (toMatGL b) _ 3).symm
      _ = 1 := by rw [hcg, map_one]
  have hc₁₂' : Commute z₁ z₂ := by
    show z₁ * z₂ = z₂ * z₁
    exact Subtype.ext (by simpa using hc₁₂.eq)
  have hc : Commute M₁ M₂ := by
    rw [hM₁def, hM₂def]
    exact Commute.map (Commute.map hc₁₂' (centralizerGL y h)) (toMatGL b).toMonoidHom
  have hyk : ∀ k : ℕ, y₂ * y₁ ^ k ∈ isometryCentralizer Q y := fun k =>
    Subgroup.mul_mem _ hy₂ (Subgroup.pow_mem _ hy₁ k)
  have hMk : ∀ k : ℕ, M₂ * M₁ ^ k = toMatGL b (centralizerGL y h
      ⟨y₂ * y₁ ^ k, (Subgroup.mem_inf.mp (hyk k)).2⟩) := by
    intro k
    have hzc : (⟨y₂ * y₁ ^ k, (Subgroup.mem_inf.mp (hyk k)).2⟩ :
        ↥(Subgroup.centralizer ({y} : Set (V ≃ₗ[K] V)))) = z₂ * z₁ ^ k :=
      Subtype.ext (by simp [z₁, z₂])
    rw [hM₂def, hM₁def, hzc, map_mul, map_pow, map_mul, map_pow]
  have hk' : ∀ k : ℕ, ∃ G ∈ StatedSU 3 (Nat.card K) (AdjoinRoot h),
      G * (M₂ * M₁ ^ k) ≠ (M₂ * M₁ ^ k) * G := by
    intro k
    obtain ⟨g, hg, hne⟩ := hmoves k
    let zk : ↥(Subgroup.centralizer ({y} : Set (V ≃ₗ[K] V))) :=
      ⟨y₂ * y₁ ^ k, (Subgroup.mem_inf.mp (hyk k)).2⟩
    refine ⟨(ε ⟨g, hg⟩ : Matrix.GeneralLinearGroup (Fin 3) (AdjoinRoot h)),
      (ε ⟨g, hg⟩).2, ?_⟩
    intro hcomm
    have hsp : ((ε ⟨g, hg⟩ : ↥(StatedSU 3 (Nat.card K) (AdjoinRoot h))) :
        Matrix.GeneralLinearGroup (Fin 3) (AdjoinRoot h)) =
        specialMat Q y h b ⟨g, hg⟩ := hε ⟨g, hg⟩
    rw [hsp] at hcomm
    have hcM : Commute (toMatGL b (centralizerGL y h zk))
        (specialMat Q y h b ⟨g, hg⟩) := by
      rw [← hMk k]
      exact hcomm.symm
    have hAz : Commute (zk : V ≃ₗ[K] V) ((⟨g, hg⟩ : ↥(specialBlock Q y h)) :
      V ≃ₗ[K] V) :=
      commute_of_commute_specialMat hy hh hself b zk ⟨g, hg⟩ hcM
    apply hne
    have hzk : (zk : V ≃ₗ[K] V) = y₂ * y₁ ^ k := rfl
    rw [hzk] at hAz
    exact hAz.eq.symm
  have h3 : 3 ∣ 2 ^ m + 1 :=
    CFSG.StandardType.UnitaryCenter.three_dvd_two_pow_add_one_of_odd hm
  have hnot := not_isSolvable_and_of_unitary_three hE hm2 h3 hu₁ hu₂ hM₁3 hM₂3 hc
    (by
      intro k
      obtain ⟨G, hG, hneG⟩ := hk' k
      exact ⟨G, by simpa [hK] using hG, hneG⟩)
  rintro ⟨hsol₁, hsol₂⟩
  have hs₁ : IsSolvable ↥(StatedSU 3 (Nat.card K) (AdjoinRoot h) ⊓
      Subgroup.centralizer ({M₁} :
        Set (Matrix.GeneralLinearGroup (Fin 3) (AdjoinRoot h)))) :=
    isSolvable_statedSU_of_isSolvable_specialBlock hy hh hself b ε hε hy₁ hsol₁
  have hs₂ : IsSolvable ↥(StatedSU 3 (Nat.card K) (AdjoinRoot h) ⊓
      Subgroup.centralizer ({M₂} :
        Set (Matrix.GeneralLinearGroup (Fin 3) (AdjoinRoot h)))) :=
    isSolvable_statedSU_of_isSolvable_specialBlock hy hh hself b ε hε hy₂ hsol₂
  rw [hK] at hs₁ hs₂
  exact hnot ⟨hs₁, hs₂⟩

end CFSG.LocalAnalysis.GLTheoremA.CanonU3.OrthMinus
