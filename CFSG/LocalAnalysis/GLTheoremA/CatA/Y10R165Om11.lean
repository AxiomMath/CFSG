module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om10

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks QuadraticMap Polynomial
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

namespace OmEngine

variable {F V : Type} [Field F] [Finite F] [CharP F 2] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {n p q : ℕ}
  {Ã : Subgroup ↥(orthDerived Q)}

theorem exists_qTorus (hT : OmTorusThree) (hn : Nat.card F = 2 ^ n)
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hqdiv : q ∣ 2 ^ n - 1 ∨ q ∣ 2 ^ n + 1)
    {xD : V ≃ₗ[F] V} (hxodd : OddOrderIsometry Q p xD)
    (hfixD : 8 ≤ Module.finrank F ↥(fixedSpace xD))
    (J : Subgroup ↥(orthDerived Q))
    (eJ : ↥J ≃* ↥(orthDerived (Q.comp (fixedSpace xD).subtype)))
    (DK : Subgroup ↥(orthDerived Q))
    (hJle : J ≤ Subgroup.centralizer (DK : Set ↥(orthDerived Q))) :
    ∃ FK : Subgroup ↥(orthDerived Q),
      IsElemAbelian q FK ∧ 3 ≤ CFSG.Open.pRank q FK ∧
      FK ≤ Subgroup.centralizer (DK : Set ↥(orthDerived Q)) ∧
      FK ≤ Subgroup.normalizer (J : Set ↥(orthDerived Q)) := by
  classical
  have hWnd : (polarBilin (Q.comp (fixedSpace xD).subtype)).Nondegenerate :=
    hxodd.polarBilin_fixed_nondegenerate
  have hdimW : 8 ≤ Module.finrank F ↥(fixedSpace xD) := le_trans (by norm_num) hfixD
  have hqdivW : q ∣ Nat.card F - 1 ∨ q ∣ Nat.card F + 1 := by
    rcases hqdiv with h | h
    · exact Or.inl (by rwa [hn])
    · exact Or.inr (by rwa [hn])
  obtain ⟨T, hTle, hTe, hTr⟩ :=
    hT F ↥(fixedSpace xD) (Q.comp (fixedSpace xD).subtype) hWnd hdimW q hq hq2 hqdivW
  let TΩ : Subgroup ↥(orthDerived (Q.comp (fixedSpace xD).subtype)) :=
    T.comap (orthDerived (Q.comp (fixedSpace xD).subtype)).subtype
  have hmapTΩ : TΩ.map (orthDerived (Q.comp (fixedSpace xD).subtype)).subtype = T := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, hTle hy⟩, hy, rfl⟩
  haveI : IsMulCommutative ↥T := hTe.1
  have hTΩe : IsElemAbelian q TΩ := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · intro a b
      apply Subtype.ext
      apply Subtype.ext
      have haT : ((a : ↥(orthDerived (Q.comp (fixedSpace xD).subtype))) :
          ↥(fixedSpace xD) ≃ₗ[F] ↥(fixedSpace xD)) ∈ T :=
        Subgroup.mem_comap.mp a.2
      have hbT : ((b : ↥(orthDerived (Q.comp (fixedSpace xD).subtype))) :
          ↥(fixedSpace xD) ≃ₗ[F] ↥(fixedSpace xD)) ∈ T :=
        Subgroup.mem_comap.mp b.2
      have h := mul_comm' (⟨_, haT⟩ : ↥T) ⟨_, hbT⟩
      simpa using congrArg Subtype.val h
    · intro x hx
      have hxT : ((x : ↥(orthDerived (Q.comp (fixedSpace xD).subtype))) :
          ↥(fixedSpace xD) ≃ₗ[F] ↥(fixedSpace xD)) ∈ T :=
        Subgroup.mem_comap.mp hx
      exact Subtype.ext (hTe.2 _ hxT)
  have hTΩrank : CFSG.Open.pRank q TΩ = CFSG.Open.pRank q T := by
    rw [← hmapTΩ,
      CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hq.one_lt
        (orthDerived (Q.comp (fixedSpace xD).subtype)).subtype
        (orthDerived (Q.comp (fixedSpace xD).subtype)).subtype_injective TΩ]
  let FJ : Subgroup ↥J := TΩ.comap eJ.toMonoidHom
  let FK : Subgroup ↥(orthDerived Q) := FJ.map (Subgroup.subtype (G := ↥(orthDerived Q)) J)
  have hFJeq : FJ = TΩ.map eJ.symm.toMonoidHom := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_map]
    constructor
    · intro hx; exact ⟨eJ x, hx, eJ.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  have hFJe : IsElemAbelian q FJ := by
    rw [hFJeq]; exact CFSG.SectionRank.isElemAbelian_map hTΩe eJ.symm.toMonoidHom
  have hFKe : IsElemAbelian q FK :=
    CFSG.SectionRank.isElemAbelian_map hFJe
      (Subgroup.subtype (G := ↥(orthDerived Q)) J)
  have hFKle : FK ≤ J := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hrankFJ : CFSG.Open.pRank q FJ = CFSG.Open.pRank q T := by
    rw [pRank_comap_mulEquiv hq.one_lt eJ TΩ, hTΩrank]
  have hrankFK : CFSG.Open.pRank q FK = CFSG.Open.pRank q FJ :=
    CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hq.one_lt J.subtype
      J.subtype_injective FJ
  have hF3 : 3 ≤ CFSG.Open.pRank q FK := by
    rw [hrankFK, hrankFJ]; exact hTr
  have hFcent : FK ≤ Subgroup.centralizer (DK : Set ↥(orthDerived Q)) :=
    hFKle.trans hJle
  have hFJN : FK ≤ Subgroup.normalizer (J : Set ↥(orthDerived Q)) :=
    hFKle.trans Subgroup.le_normalizer
  exact ⟨FK, hFKe, hF3, hFcent, hFJN⟩

theorem exists_restriction_fixed (hp : p.Prime) (hpF : (p : F) ≠ 0)
    {xD xE : V ≃ₗ[F] V} (hxodd : OddOrderIsometry Q p xD)
    (hxEpow : xE ^ p = 1)
    (hxEsupp : xE ∈ supportedBlock Q xD (X - 1)) :
    ∃ xE' : ↥(fixedSpace xD) ≃ₗ[F] ↥(fixedSpace xD),
      (∀ z : ↥(fixedSpace xD), ((xE' z : ↥(fixedSpace xD)) : V) = xE (z : V)) ∧
      OddOrderIsometry (Q.comp (fixedSpace xD).subtype) p xE' := by
  classical
  let xE' : ↥(fixedSpace xD) ≃ₗ[F] ↥(fixedSpace xD) :=
    restrictFixed Q xD ⟨xE, hxEsupp⟩
  have hxE'coe : ∀ z : ↥(fixedSpace xD), ((xE' z : ↥(fixedSpace xD)) : V) = xE (z : V) :=
    fun z => coe_restrictFixed (Q := Q) (x := xD) ⟨xE, hxEsupp⟩ z
  have hxE'odd : OddOrderIsometry (Q.comp (fixedSpace xD).subtype) p xE' := by
    refine ⟨restrictFixed_mem_orthogonalGroup _, ?_, hpF, ?_⟩
    · refine LinearEquiv.ext fun z => Subtype.ext ?_
      have hcoe : ∀ (m : ℕ) (z : ↥(fixedSpace xD)),
          (((xE' ^ m) z : ↥(fixedSpace xD)) : V) = (xE ^ m) (z : V) := by
        intro m
        induction m with
        | zero => intro z; simp
        | succ m ih =>
            intro z
            calc (((xE' ^ (m + 1)) z : ↥(fixedSpace xD)) : V)
                = (((xE' ^ m) (xE' z) : ↥(fixedSpace xD)) : V) := by
                  rw [pow_succ, LinearEquiv.mul_apply]
              _ = (xE ^ m) (xE (z : V)) := by rw [ih, hxE'coe]
              _ = (xE ^ (m + 1)) (z : V) := by rw [pow_succ, LinearEquiv.mul_apply]
      rw [hcoe p z, hxEpow]
      rfl
    · intro z hz
      refine hxodd.polarBilin_fixed_nondegenerate.1 z fun w => ?_
      have h := hz w
      simpa [polarBilin_apply_apply] using h
  exact ⟨xE', hxE'coe, hxE'odd⟩


theorem exists_restriction_third_block (hp : p.Prime) (hpF : (p : F) ≠ 0)
    {xD xE xG : V ≃ₗ[F] V} {xE' : ↥(fixedSpace xD) ≃ₗ[F] ↥(fixedSpace xD)}
    (hxE'coe : ∀ z : ↥(fixedSpace xD), ((xE' z : ↥(fixedSpace xD)) : V) = xE (z : V))
    (hxE'odd : OddOrderIsometry (Q.comp (fixedSpace xD).subtype) p xE')
    (hxGquad : ∀ v : V, Q (xG v) = Q v) (hxGpow : xG ^ p = 1)
    (hcommGD : Commute xG xD) (hcommEG : Commute xE xG) :
    ∃ xGW : ↥(fixedSpace xD) ≃ₗ[F] ↥(fixedSpace xD),
      (∀ w : ↥(fixedSpace xD), ((xGW w : ↥(fixedSpace xD)) : V) = xG (w : V)) ∧
      ∃ xGZ : ↥(fixedSpace xE') ≃ₗ[F] ↥(fixedSpace xE'),
        (∀ z : ↥(fixedSpace xE'), ((xGZ z : ↥(fixedSpace xE')) : V) = xG (z : V)) ∧
        OddOrderIsometry
          ((Q.comp (fixedSpace xD).subtype).comp (fixedSpace xE').subtype) p xGZ := by
  classical
  let Z : Submodule F ↥(fixedSpace xD) := fixedSpace xE'
  let QZ : QuadraticForm F ↥Z := (Q.comp (fixedSpace xD).subtype).comp Z.subtype
  have hZnd : (polarBilin QZ).Nondegenerate := hxE'odd.polarBilin_fixed_nondegenerate
  have hxG_W : ∀ w ∈ fixedSpace xD, xG w ∈ fixedSpace xD := by
    intro w hw
    have hwD : xD w = w := mem_fixedSpace.mp hw
    refine mem_fixedSpace.mpr ?_
    rw [← LinearEquiv.mul_apply, ← hcommGD.eq, LinearEquiv.mul_apply, hwD]
  have hxG_Winv : ∀ w ∈ fixedSpace xD, xG⁻¹ w ∈ fixedSpace xD := by
    intro w hw
    have hwD : xD w = w := mem_fixedSpace.mp hw
    have hc : Commute xG⁻¹ xD := hcommGD.inv_left
    refine mem_fixedSpace.mpr ?_
    rw [← LinearEquiv.mul_apply, ← hc.eq, LinearEquiv.mul_apply, hwD]
  let xGW : ↥(fixedSpace xD) ≃ₗ[F] ↥(fixedSpace xD) :=
    restrictEquiv (fixedSpace xD) xG hxG_W hxG_Winv
  have hxGWcoe : ∀ w : ↥(fixedSpace xD), ((xGW w : ↥(fixedSpace xD)) : V) = xG (w : V) :=
    fun w => by dsimp only [xGW]; exact coe_restrictEquiv (fixedSpace xD) xG hxG_W hxG_Winv w
  have hxE'_of_mem : ∀ z : ↥(fixedSpace xD), z ∈ Z → xE (z : V) = (z : V) := by
    intro z hz
    have hz' : xE' z = z := mem_fixedSpace.mp hz
    have h1 : ((xE' z : ↥(fixedSpace xD)) : V) = xE (z : V) := hxE'coe z
    have h2 : ((xE' z : ↥(fixedSpace xD)) : V) = (z : V) :=
      congrArg (fun w : ↥(fixedSpace xD) => (w : V)) hz'
    exact h1.symm.trans h2
  have hxGW_Z : ∀ z ∈ Z, xGW z ∈ Z := by
    intro z hz
    refine mem_fixedSpace.mpr ?_
    apply Subtype.ext
    show ((xE' (xGW z) : ↥(fixedSpace xD)) : V) = ((xGW z : ↥(fixedSpace xD)) : V)
    rw [show ((xE' (xGW z) : ↥(fixedSpace xD)) : V) = xE ((xGW z : ↥(fixedSpace xD)) : V) from
      hxE'coe (xGW z)]
    rw [hxGWcoe]
    calc xE (xG ((z : ↥(fixedSpace xD)) : V))
        = (xE * xG) ((z : ↥(fixedSpace xD)) : V) := rfl
      _ = (xG * xE) ((z : ↥(fixedSpace xD)) : V) := by rw [hcommEG.eq]
      _ = xG (xE ((z : ↥(fixedSpace xD)) : V)) := rfl
      _ = xG ((z : ↥(fixedSpace xD)) : V) := by rw [hxE'_of_mem z hz]
  have hxGW_inv_coe : ∀ z : ↥(fixedSpace xD),
      ((xGW⁻¹ z : ↥(fixedSpace xD)) : V) = xG⁻¹ (z : V) := by
    intro z
    have h1 : xGW (xGW⁻¹ z) = z := xGW.apply_symm_apply z
    have h2 : ((xGW (xGW⁻¹ z) : ↥(fixedSpace xD)) : V) = ((z : ↥(fixedSpace xD)) : V) :=
      congrArg (fun w : ↥(fixedSpace xD) => (w : V)) h1
    rw [hxGWcoe] at h2
    have h3 := congrArg (fun v : V => xG⁻¹ v) h2
    simpa using h3
  have hxGW_Zinv : ∀ z ∈ Z, xGW⁻¹ z ∈ Z := by
    intro z hz
    refine mem_fixedSpace.mpr ?_
    apply Subtype.ext
    show ((xE' (xGW⁻¹ z) : ↥(fixedSpace xD)) : V) = ((xGW⁻¹ z : ↥(fixedSpace xD)) : V)
    rw [show ((xE' (xGW⁻¹ z) : ↥(fixedSpace xD)) : V) =
      xE ((xGW⁻¹ z : ↥(fixedSpace xD)) : V) from hxE'coe (xGW⁻¹ z)]
    rw [hxGW_inv_coe]
    have hcEG : Commute xE xG⁻¹ := hcommEG.inv_right
    calc xE (xG⁻¹ ((z : ↥(fixedSpace xD)) : V))
        = (xE * xG⁻¹) ((z : ↥(fixedSpace xD)) : V) := rfl
      _ = (xG⁻¹ * xE) ((z : ↥(fixedSpace xD)) : V) := by rw [hcEG.eq]
      _ = xG⁻¹ (xE ((z : ↥(fixedSpace xD)) : V)) := rfl
      _ = xG⁻¹ ((z : ↥(fixedSpace xD)) : V) := by rw [hxE'_of_mem z hz]
  let xGZ : Z ≃ₗ[F] Z := restrictEquiv Z xGW hxGW_Z hxGW_Zinv
  have hxGZcoe : ∀ z : Z,
      (((xGZ z : Z) : ↥(fixedSpace xD)) : V) =
        xG (((z : Z) : ↥(fixedSpace xD)) : V) := by
    intro z
    rw [show (((xGZ z : Z) : ↥(fixedSpace xD)) : V) =
      (((xGW z : ↥(fixedSpace xD)) : V)) from by rw [coe_restrictEquiv]]
    rw [coe_restrictEquiv]
  have hxGZ : OddOrderIsometry QZ p xGZ := by
    refine ⟨?_, ?_, hpF, ?_⟩
    · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro z
      show Q (((xGZ z : Z) : ↥(fixedSpace xD)) : V) =
        Q (((z : Z) : ↥(fixedSpace xD)) : V)
      rw [hxGZcoe]
      exact hxGquad (((z : Z) : ↥(fixedSpace xD)) : V)
    · refine LinearEquiv.ext fun z => Subtype.ext (Subtype.ext ?_)
      have hcoe : ∀ (m : ℕ) (z : Z),
          ((((xGZ ^ m) z : Z) : ↥(fixedSpace xD)) : V) =
            (xG ^ m) (((z : Z) : ↥(fixedSpace xD)) : V) := by
        intro m
        induction m with
        | zero => intro z; simp
        | succ m ih =>
            intro z
            calc ((((xGZ ^ (m + 1)) z : Z) : ↥(fixedSpace xD)) : V)
                = ((((xGZ ^ m) (xGZ z) : Z) : ↥(fixedSpace xD)) : V) := by
                  rw [pow_succ, LinearEquiv.mul_apply]
              _ = (xG ^ m) (((xGZ z : Z) : ↥(fixedSpace xD)) : V) := by rw [ih]
              _ = (xG ^ m) (xG (((z : Z) : ↥(fixedSpace xD)) : V)) := by rw [hxGZcoe]
              _ = (xG ^ (m + 1)) (((z : Z) : ↥(fixedSpace xD)) : V) := by
                  rw [pow_succ, LinearEquiv.mul_apply]
      rw [hcoe p z, hxGpow]
      rfl
    · intro z hz
      refine hZnd.1 z fun w => ?_
      have h := hz w
      simpa [polarBilin_apply_apply] using h
  refine ⟨xGW, hxGWcoe, xGZ, hxGZcoe, ?_⟩
  exact hxGZ

theorem map_fixedSpace_eq_common_fixed [Fintype ↥(orthImage Ã)]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hAe : IsElemAbelian p (orthImage Ã))
    (t : Hyperplane (orthImage Ã) p → ↥(orthImage Ã)) (ht : ∀ D, t D ∉ D.1)
    {D E G : Hyperplane (orthImage Ã) p} (hGD : G ≠ D) (hGE : G ≠ E)
    {xE' : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)) ≃ₗ[F]
      ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))}
    (hxE'coe : ∀ z : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)),
      ((xE' z : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V) =
        blockEnd (orthImage Ã) hp hpF hAe t ht E (z : V))
    {Zv : Submodule F V}
    (hZvdef : Zv = LinearMap.ker (projBlock (orthImage Ã) hp hpF hAe D) ⊓
      LinearMap.ker (projBlock (orthImage Ã) hp hpF hAe E)) :
    blockSpace (orthImage Ã) G.1 ≤
        (fixedSpace xE').map (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype ∧
      (fixedSpace xE').map (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype = Zv ∧
      Module.finrank F ↥(fixedSpace xE') = Module.finrank F ↥Zv := by
  classical
  have hxE'_of_mem : ∀ z : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)),
      z ∈ fixedSpace xE' → blockEnd (orthImage Ã) hp hpF hAe t ht E (z : V) = (z : V) := by
    intro z hz
    have hz' : xE' z = z := mem_fixedSpace.mp hz
    have h1 : ((xE' z : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V) =
        blockEnd (orthImage Ã) hp hpF hAe t ht E (z : V) := hxE'coe z
    have h2 : ((xE' z : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V) =
        (z : V) := congrArg (fun w : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)) =>
          (w : V)) hz'
    exact h1.symm.trans h2
  have hVG_le_Zmap : blockSpace (orthImage Ã) G.1 ≤
      (fixedSpace xE').map (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype := by
    intro v hv
    have hvW : v ∈ fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D) := by
      have h : v ∈ LinearMap.ker (projBlock (orthImage Ã) hp hpF hAe D) := by
        rw [LinearMap.mem_ker]
        exact projBlock_apply_of_mem_block (orthImage Ã) hp hpF hAe (D := D) (E := G) hGD hv
      rwa [← fixedSpace_blockEnd_eq_ker_projBlock (orthImage Ã) hp hpF hAe t ht D] at h
    have hvE : v ∈ fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht E) := by
      rw [fixedSpace_blockEnd_eq_ker_projBlock (orthImage Ã) hp hpF hAe t ht E]
      rw [LinearMap.mem_ker]
      exact projBlock_apply_of_mem_block (orthImage Ã) hp hpF hAe (D := E) (E := G) hGE hv
    refine Submodule.mem_map.mpr ⟨⟨v, hvW⟩, ?_, rfl⟩
    refine mem_fixedSpace.mpr ?_
    apply Subtype.ext
    show ((xE' ⟨v, hvW⟩ : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V) = v
    rw [hxE'coe]
    exact mem_fixedSpace.mp hvE
  have hZmap :
      (fixedSpace xE').map
        (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype = Zv := by
    rw [hZvdef]
    ext v
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · rw [← fixedSpace_blockEnd_eq_ker_projBlock (orthImage Ã) hp hpF hAe t ht D]
        exact z.2
      · rw [← fixedSpace_blockEnd_eq_ker_projBlock (orthImage Ã) hp hpF hAe t ht E]
        exact mem_fixedSpace.mpr (hxE'_of_mem z hz)
    · intro hv
      refine Submodule.mem_map.mpr ⟨⟨v, ?_⟩, ?_, rfl⟩
      · have h : v ∈ fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D) := by
          rw [fixedSpace_blockEnd_eq_ker_projBlock (orthImage Ã) hp hpF hAe t ht D]
          exact hv.1
        exact h
      · refine mem_fixedSpace.mpr ?_
        apply Subtype.ext
        show ((xE' ⟨v, _⟩ : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V) = v
        rw [hxE'coe]
        have h : v ∈ fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht E) := by
          rw [fixedSpace_blockEnd_eq_ker_projBlock (orthImage Ã) hp hpF hAe t ht E]
          exact hv.2
        exact mem_fixedSpace.mp h
  have hZdim : Module.finrank F ↥(fixedSpace xE') = Module.finrank F ↥Zv := by
    rw [← Submodule.finrank_map_subtype_eq
      (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)) (fixedSpace xE'), hZmap]
  exact ⟨hVG_le_Zmap, hZmap, hZdim⟩

theorem four_le_finrank_fixedSpace [Fintype ↥(orthImage Ã)]
    (hQ : (polarBilin Q).Nondegenerate) (hn : Nat.card F = 2 ^ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0) (h2 : (2 : F) = 0)
    (hAe : IsElemAbelian p (orthImage Ã))
    (hB : ∀ a : ↥(orthImage Ã), ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v)
    (t : Hyperplane (orthImage Ã) p → ↥(orthImage Ã)) (ht : ∀ D, t D ∉ D.1)
    {D E G : Hyperplane (orthImage Ã) p} (hDE : D ≠ E) (hGD : G ≠ D) (hGE : G ≠ E)
    (hGne : blockSpace (orthImage Ã) G.1 ≠ ⊥)
    {Zv : Submodule F V}
    (hZvdim : Module.finrank F ↥Zv =
      Module.finrank F V - Module.finrank F ↥(blockSpace (orthImage Ã) D.1) -
        Module.finrank F ↥(blockSpace (orthImage Ã) E.1))
    (hregD : 3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ∨
      ∃ ℓ : ℕ, Module.finrank F V = 2 * ℓ ∧ Odd ℓ ∧ 5 ≤ ℓ ∧
        Module.finrank F ↥(blockSpace (orthImage Ã) D.1) = 2 ∧
        Module.finrank F ↥(blockSpace (orthImage Ã) E.1) = 2)
    {xE' : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)) ≃ₗ[F]
      ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))}
    (hxE'odd : OddOrderIsometry
      (Q.comp (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype) p xE')
    (hZdim : Module.finrank F ↥(fixedSpace xE') = Module.finrank F ↥Zv) :
    4 ≤ Module.finrank F ↥(fixedSpace xE') ∧ Even (Module.finrank F ↥(fixedSpace xE')) ∧
      (Module.finrank F ↥(fixedSpace xE') = 4 ∨ 6 ≤ Module.finrank F ↥(fixedSpace xE')) := by
  classical
  have hZge : 4 ≤ Module.finrank F ↥(fixedSpace xE') := by
    rw [hZdim]
    rcases hregD with hm0 | ⟨ℓ, hdim, hodd, h5, hdD, hdE⟩
    · have hsum := sum_finrank_blockSpace_le_finrank (orthImage Ã) hp hpF hAe
      have hle : (∑ x ∈ ({D, E, G} : Finset (Hyperplane (orthImage Ã) p)),
          Module.finrank F ↥(blockSpace (orthImage Ã) x.1)) ≤ Module.finrank F V := by
        refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_).trans hsum
        intro x _ _; exact Nat.zero_le _
      have hsum3 : (∑ x ∈ ({D, E, G} : Finset (Hyperplane (orthImage Ã) p)),
          Module.finrank F ↥(blockSpace (orthImage Ã) x.1)) =
          Module.finrank F ↥(blockSpace (orthImage Ã) D.1) +
            Module.finrank F ↥(blockSpace (orthImage Ã) E.1) +
            Module.finrank F ↥(blockSpace (orthImage Ã) G.1) := by
        simp [Finset.sum_insert, hDE, Ne.symm hGD, Ne.symm hGE, add_assoc]
      have hsum_le : Module.finrank F ↥(blockSpace (orthImage Ã) D.1) +
          Module.finrank F ↥(blockSpace (orthImage Ã) E.1) +
          Module.finrank F ↥(blockSpace (orthImage Ã) G.1) ≤ Module.finrank F V := by
        rw [← hsum3]; exact hle
      have hdG4 : 4 ≤ Module.finrank F ↥(blockSpace (orthImage Ã) G.1) := by
        have hpos : 0 < Module.finrank F ↥(blockSpace (orthImage Ã) G.1) := by
          rw [Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot]
          exact hGne
        have hdvd := finrank_blockSpace_dvd_rk2Ord (orthImage Ã) hp hp2 hAe t ht G hGne hn
        have hev := even_finrank_blockSpace (orthImage Ã) h2 hQ hp hpF hAe hB G
        obtain ⟨k, hk⟩ := hev
        have h3 : 3 ≤ Module.finrank F ↥(blockSpace (orthImage Ã) G.1) :=
          le_trans hm0 (Nat.le_of_dvd hpos hdvd)
        omega
      rw [hZvdim]
      omega
    · rw [hZvdim, hdim, hdD, hdE]
      omega
  have hZeven : Even (Module.finrank F ↥(fixedSpace xE')) := even_finrank_fixedSpace hxE'odd h2
  have hZcases : Module.finrank F ↥(fixedSpace xE') = 4 ∨
      6 ≤ Module.finrank F ↥(fixedSpace xE') := by
    obtain ⟨k, hk⟩ := hZeven
    omega
  exact ⟨hZge, hZeven, hZcases⟩


end OmEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
