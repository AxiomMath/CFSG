module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
import CFSG.Adapters.LinearCatalogStated
import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3Mat
import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitParab
import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitRadical
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoInf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
import CFSG.Quasithin.H13.NQTermUnipotentPlane
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAssembly
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.NQTerm (flagNil flagUnipotent mem_flagUnipotent
  elationSubgroup_eq_flagUnipotent det_one_add_of_mem_flagNil exists_sub_smul_mem_flagNil
  pow_char_of_mem_flagUnipotent mul_eq_zero_of_mem_flagNil smul_mem_flagNil)
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis heisEquivBar theta)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueSchreierAssembly (classical_model_outer_solvable)

section Model

variable {F : Type} [Field F]

theorem elationSubgroup_flagSpace_le_upperTriangular (n d : ℕ) :
    elationSubgroup (flagSpace n F d) ≤ upperTriangular n F := by
  intro A hA i j hij
  obtain ⟨h1, h2⟩ := LinearThreeKit.mem_elationGenerators_iff.mp
    (LinearThreeKit.mem_elationGenerators_of_mem hA)
  have hji : (j : ℕ) < i := hij
  by_cases hjd : (j : ℕ) < d
  · have hmem : (Pi.single j (1 : F) : Fin n → F) ∈ flagSpace n F d :=
      mem_flagSpace.mpr fun k hk => Pi.single_eq_of_ne (fun h => by subst h; omega) _
    have hi := congrFun (h2 _ hmem) i
    rw [mulVec_single_one, col_apply] at hi
    rw [hi, Pi.single_eq_of_ne (Fin.ne_of_gt hij)]
  · have hi := mem_flagSpace.mp (h1 (Pi.single j 1)) i (by omega)
    rw [Pi.sub_apply, mulVec_single_one, col_apply, Pi.single_eq_of_ne (Fin.ne_of_gt hij),
      sub_zero] at hi
    exact hi

theorem projElationSubgroup_flagSpace_le_projUpperTriangular (n d : ℕ) :
    projElationSubgroup (flagSpace n F d) ≤ projUpperTriangular n F :=
  map_mono (elationSubgroup_flagSpace_le_upperTriangular n d)

theorem projStabilizer_le_normalizer_projElationSubgroup {n : ℕ} (W : Submodule F (Fin n → F)) :
    projStabilizer W ≤ normalizer (projElationSubgroup W : Set (projectiveSL n F)) :=
  (map_mono (LinearThreeKit.stabilizer_le_normalizer_elationSubgroup W)).trans
    (le_normalizer_map _)

private theorem eq_one_of_mem_scalars_of_pow_char {p : ℕ} [Fact p.Prime] [CharP F p]
    {z : Matrix.SpecialLinearGroup (Fin 3) F} (hz : z ∈ scalars 3 F) (hzp : z ^ p = 1) :
    z = 1 := by
  obtain ⟨c, -, hc⟩ := hz
  have h1 : (c : F) ^ p = 1 := by
    have h := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) F =>
      (A : Matrix (Fin 3) (Fin 3) F) 0 0) hzp
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hc,
      scalar_apply, diagonal_pow, diagonal_apply_eq, one_apply_eq, Pi.pow_apply] at h
    exact h
  have h2 : ((c : F) - 1) ^ p = 0 := by rw [sub_pow_char, h1, one_pow, sub_self]
  have h3 : (c : F) = 1 := sub_eq_zero.mp (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.mp h2)
  apply Subtype.ext
  rw [hc, h3, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem centralizer_projElationSubgroup_le {p : ℕ} [Fact p.Prime] [CharP F p]
    {V : Submodule F (Fin 3 → F)} (hV : Module.finrank F V = 1 ∨ Module.finrank F V = 2) :
    centralizer (projElationSubgroup V : Set (projectiveSL 3 F)) ≤ projElationSubgroup V := by
  intro x hx
  obtain ⟨g, rfl⟩ := proj_surjective 3 F x
  have hU : ∀ u ∈ flagUnipotent V, g * u = u * g := by
    intro u hu
    have hu' : u ∈ elationSubgroup V := by rw [elationSubgroup_eq_flagUnipotent]; exact hu
    have h1 := mem_centralizer_iff.mp hx (proj 3 F u) (proj_mem_projElationSubgroup hu')
    set v := g * u * g⁻¹ with hv
    have h2 : proj 3 F u = proj 3 F v := by
      rw [hv, map_mul, map_mul, map_inv, ← h1, mul_inv_cancel_right]
    have hz := proj_eq_proj_iff.mp h2
    have hup : u ^ p = 1 := pow_char_of_mem_flagUnipotent hu
    have hvp : v ^ p = 1 := by rw [hv, conj_pow, hup, mul_one, mul_inv_cancel]
    have hzc : u⁻¹ * v ∈ center (Matrix.SpecialLinearGroup (Fin 3) F) := scalars_le_center 3 F hz
    have hzp : (u⁻¹ * v) ^ p = 1 := by
      have h3 : (u * (u⁻¹ * v)) ^ p = u ^ p * (u⁻¹ * v) ^ p :=
        Commute.mul_pow (mem_center_iff.mp hzc u) p
      rw [mul_inv_cancel_left, hvp, hup, one_mul] at h3
      exact h3.symm
    have hvu : u = v := inv_mul_eq_one.mp (eq_one_of_mem_scalars_of_pow_char hz hzp)
    calc g * u = v * g := by rw [hv]; group
      _ = u * g := by rw [← hvu]
  have hA : ∀ n ∈ flagNil V, (g : Matrix (Fin 3) (Fin 3) F) * n = n * g := by
    intro n hn
    obtain ⟨u, hu⟩ : ∃ u : Matrix.SpecialLinearGroup (Fin 3) F,
        (u : Matrix (Fin 3) (Fin 3) F) = 1 + n :=
      ⟨⟨1 + n, det_one_add_of_mem_flagNil (p := p) hn⟩, rfl⟩
    have huV : u ∈ flagUnipotent V :=
      mem_flagUnipotent.mpr (by rw [hu, add_sub_cancel_left]; exact hn)
    have h := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) F =>
      (A : Matrix (Fin 3) (Fin 3) F)) (hU u huV)
    simp only [Matrix.SpecialLinearGroup.coe_mul, hu, mul_add, add_mul, mul_one, one_mul] at h
    exact add_left_cancel h
  obtain ⟨a, ha⟩ := exists_sub_smul_mem_flagNil hV hA
  set N := (g : Matrix (Fin 3) (Fin 3) F) - a • 1 with hN
  have hga : (g : Matrix (Fin 3) (Fin 3) F) = a • 1 + N := by rw [hN]; abel
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hdet : (g : Matrix (Fin 3) (Fin 3) F).det = 1 := g.2
    rw [hga, zero_smul, zero_add] at hdet
    have h2 : N.det ^ 2 = 0 := by rw [sq, ← det_mul, mul_eq_zero_of_mem_flagNil ha ha, det_zero]
    rw [hdet, one_pow] at h2
    exact one_ne_zero h2
  have hNa : a⁻¹ • N ∈ flagNil V := smul_mem_flagNil a⁻¹ ha
  obtain ⟨w, hwd⟩ : ∃ w : Matrix.SpecialLinearGroup (Fin 3) F,
      (w : Matrix (Fin 3) (Fin 3) F) = 1 + a⁻¹ • N :=
    ⟨⟨1 + a⁻¹ • N, det_one_add_of_mem_flagNil (p := p) hNa⟩, rfl⟩
  have hw : w ∈ elationSubgroup V := by
    rw [elationSubgroup_eq_flagUnipotent]
    exact mem_flagUnipotent.mpr (by rw [hwd, add_sub_cancel_left]; exact hNa)
  have hgw : (g : Matrix (Fin 3) (Fin 3) F) = a • (w : Matrix (Fin 3) (Fin 3) F) := by
    rw [hwd, smul_add, smul_smul, mul_inv_cancel₀ ha0, one_smul, hga]
  have hmat : ((w⁻¹ * g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      scalar (Fin 3) a := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hgw, Matrix.mul_smul,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
      scalar_apply, smul_one_eq_diagonal]
  have hs : w⁻¹ * g ∈ scalars 3 F := by
    refine ⟨Units.mk0 a ha0, Units.ext ?_, hmat⟩
    have hdet := (w⁻¹ * g).2
    rw [hmat, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdet
    simpa using hdet
  rw [(proj_eq_proj_iff.mpr hs).symm]
  exact proj_mem_projElationSubgroup hw

theorem linThree_model_overgroups [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (T : Sylow p (projectiveSL 3 F)) (J : Subgroup (projectiveSL 3 F))
    (hJ : normalizer ((T : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) ≤ J)
    (hJt : J ≠ ⊤) :
    ∃ N : Subgroup (projectiveSL 3 F), N ≤ J ∧ IsPGroup p N ∧
      J ≤ normalizer (N : Set (projectiveSL 3 F)) ∧
      centralizer (N : Set (projectiveSL 3 F)) ⊓ J ≤ N := by
  obtain ⟨g, I, hI, hT, rfl⟩ :=
    LinearThreeKit.exists_eq_map_conj_flagStabilizer p (n := 3) (by norm_num) T J hJ
  obtain ⟨d, hd⟩ : I.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    apply hJt
    rw [flagStabilizer_empty, map_top_of_surjective _ (proj_surjective 3 F),
      map_top_of_surjective _ (MulAut.conj g).surjective]
  obtain ⟨hd1, hd3⟩ := hI d hd
  have hV : Module.finrank F (flagSpace 3 F d) = 1 ∨ Module.finrank F (flagSpace 3 F d) = 2 := by
    rw [finrank_flagSpace (by omega)]
    omega
  refine ⟨(projElationSubgroup (flagSpace 3 F d)).map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_,
    ?_⟩
  · refine (map_mono (projElationSubgroup_flagSpace_le_projUpperTriangular 3 d)).trans ?_
    rw [← hT]
    exact hJ
  · exact ((LinearThreeKit.isPGroup_elationSubgroup p _).map (proj 3 F)).map _
  · refine (map_mono ?_).trans (le_normalizer_map _)
    refine (map_mono fun x hx => mem_flagStabilizer.mp hx d hd).trans ?_
    exact projStabilizer_le_normalizer_projElationSubgroup _
  · intro x hx
    obtain ⟨hxC, -⟩ := mem_inf.mp hx
    have hy : g⁻¹ * x * g ∈ centralizer
        (projElationSubgroup (flagSpace 3 F d) : Set (projectiveSL 3 F)) := by
      refine mem_centralizer_iff.mpr fun n hn => ?_
      have h := mem_centralizer_iff.mp hxC (g * n * g⁻¹) (mem_map_of_mem _ hn)
      calc n * (g⁻¹ * x * g) = g⁻¹ * ((g * n * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * n * g⁻¹)) * g := by rw [h]
        _ = g⁻¹ * x * g * n := by group
    refine ⟨g⁻¹ * x * g, centralizer_projElationSubgroup_le hV hy, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group

end Model

section Sylow

variable {F : Type} [Field F]

theorem card_center_projUnitriangular_three :
    Nat.card (center (projUnitriangular 3 F)) = Nat.card F := by
  rw [← CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3.map_center_mulEquiv heisEquivBar,
    card_map_of_injective heisEquivBar.injective,
    CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3.Heis.card_center]

theorem two_le_pRank_projUnitriangular_three [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = p) : 2 ≤ CFSG.Open.pRank p (projUnitriangular 3 F) := by
  let φ : Multiplicative (F × F) →* Heis F :=
    { toFun := fun x => ⟨0, (Multiplicative.toAdd x).1, (Multiplicative.toAdd x).2⟩
      map_one' := rfl
      map_mul' := fun x y => Heis.ext (by simp) (by simp) (by simp) }
  have hφ : Function.Injective φ := fun x y h =>
    Multiplicative.toAdd.injective (Prod.ext (congrArg Heis.b h) (congrArg Heis.c h))
  have hθ : Function.Injective (theta (F := F)) := fun x y h =>
    heisEquivBar.injective (Subtype.ext h)
  refine CFSG.SectionRank.le_pRank_of_injective (Fact.out : p.Prime).one_lt
    (fun a b => mul_comm a b) (fun a => ?_) ?_ (theta.comp φ) (hθ.comp hφ) ?_
  · apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    ext <;> simp [nsmul_eq_mul, CharP.cast_eq_zero]
  · rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, hF, sq]
  · rintro _ ⟨x, rfl⟩
    exact (heisEquivBar (φ x)).2

end Sylow

private theorem linThree_nonempty_mulEquiv {q : TauCeti.PrimePower} [Fact q.p.Prime]
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .A 2 q) :
    Nonempty ((TauCeti.CFSGIndex.lie d).Group ≃*
      projectiveSL 3 (GaloisField q.p q.exponent)) := by
  obtain ⟨x, hv⟩ := d
  change x = _ at hd
  subst hd
  exact ⟨(CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 _)⟩

private theorem not_dvd_two_mul_gcd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ 2 * 1 * CFSG.RankThree.OuterOrder.determinantParameter .PSL 3 (p ^ 1) := by
  intro h
  simp only [CFSG.RankThree.OuterOrder.determinantParameter, pow_one, mul_one] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h3 | h3
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  · have h4 := h3.trans (Nat.gcd_dvd_right 3 (p - 1))
    have h5 : 0 < p - 1 := by have := hp.two_le; omega
    have h6 := Nat.le_of_dvd h5 h4
    omega

theorem linThree_catalog_facts {p : ℕ} (hp : p.Prime) {q : TauCeti.PrimePower}
    {d : TauCeti.ValidLieTypeIndex} (hqp : q.p = p) (hq1 : q.exponent = 1) (hd : d.1 = .A 2 q) :
    IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group ∧
      (∃ a b : (TauCeti.CFSGIndex.lie d).Group, a * b ≠ b * a) ∧
      Group.IsSolvable (Outer (TauCeti.CFSGIndex.lie d).Group) := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨eM⟩ := linThree_nonempty_mulEquiv hd
  obtain ⟨x, hv⟩ := d
  change x = _ at hd
  subst hd
  have hS := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv (MulEquiv.refl _)
  obtain ⟨hfin, -, hsimple⟩ := CFSG.LieType.Simplicity.fam_classical_converse _ ⟨_, _, _, _, hS⟩
  refine ⟨hsimple, ?_, classical_model_outer_solvable hS⟩
  refine exists_mul_ne_of_sq_dvd_card q.prime_p ?_ Nat.card_pos.ne'
  rw [Nat.card_congr eM.toEquiv]
  have hU : Nat.card (projUnitriangular 3 (GaloisField q.p q.exponent)) = q.p ^ 3 := by
    rw [← Nat.card_congr heisEquivBar.toEquiv, CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3.Heis.card_eq,
      GaloisField.card _ _ (by omega), hq1, pow_one]
  exact (pow_dvd_pow _ (by norm_num : 2 ≤ 3)).trans (hU ▸ card_subgroup_dvd_card _)

theorem threeFourTwoLinThree_inf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {q : TauCeti.PrimePower}
    {d : TauCeti.ValidLieTypeIndex} (hqp : q.p = p) (hq1 : q.exponent = 1) (hd : d.1 = .A 2 q)
    {Y : Type} [Group Y] [Finite Y] {K Y₀ E : Subgroup Y} (R : Sylow p Y) (hK : K.Normal)
    (hKX : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) (hER : E ≤ R)
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hcore : (if 3 ≤ pRank p (R : Subgroup Y) then GLBWeakCore p (R : Subgroup Y)
      else GLBCore p 1 E) ≤ Y₀)
    (hKY₀ : ¬ K ≤ Y₀) :
    ∃ N : Subgroup Y, N ≤ K ⊓ Y₀ ∧ IsPGroup p N ∧ K ⊓ Y₀ ≤ normalizer (N : Set Y) ∧
      centralizer (N : Set Y) ⊓ (K ⊓ Y₀) ≤ N := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hX, ⟨a, b, hab⟩, -⟩ := linThree_catalog_facts hp hqp hq1 hd
  obtain ⟨eK⟩ := hKX
  subst hqp
  obtain ⟨eM⟩ := linThree_nonempty_mulEquiv hd
  set F := GaloisField q.p q.exponent
  have hF : Nat.card F = q.p := by rw [GaloisField.card _ _ (by omega), hq1, pow_one]
  set e : K ≃* projectiveSL 3 F := eK.trans eM
  haveI : IsSimpleGroup K := (MulEquiv.isSimpleGroup_congr eK).2 hX
  have hZ : K ⊓ centralizer (K : Set Y) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyK, hyC⟩ := mem_inf.mp hy
    have hc : (⟨y, hyK⟩ : K) ∈ center K :=
      mem_center_iff.mpr fun k => Subtype.ext (mem_centralizer_iff.mp hyC k k.2)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with h | h
    · rw [h, mem_bot] at hc
      exact mem_bot.mpr (congrArg Subtype.val hc)
    · refine absurd ?_ hab
      apply eK.symm.injective
      rw [map_mul, map_mul]
      exact mem_center_iff.mp (h ▸ mem_top (eK.symm b)) (eK.symm a)
  have hout : ¬ q.p ∣ Nat.card (Outer K) := by
    obtain ⟨x, hv⟩ := d
    change x = _ at hd
    subst hd
    have hS := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv eK
    have hb := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inl rfl) (le_refl 3) q.prime_p q.exponent_pos hS).1
    rw [hq1] at hb
    exact fun h => not_dvd_two_mul_gcd q.prime_p hp2 (h.trans hb)
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := F) q.p (n := 3) (by norm_num)
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow e S.isPGroup' S.not_dvd_index T
  set ι : projectiveSL 3 F →* Y := K.subtype.comp Φ.toMonoidHom with hιdef
  have hι : Function.Injective ι := K.subtype_injective.comp Φ.injective
  have hTι : (projUnitriangular 3 F).map ι = (R : Subgroup Y) ⊓ K := by
    rw [← hT, hΦ, ← hS, hιdef, ← Subgroup.map_map]
  have h2 : 2 ≤ CFSG.Open.pRank q.p ((R : Subgroup Y) ⊓ K) := by
    rw [← hTι]
    exact (two_le_pRank_projUnitriangular_three hF).trans
      (CFSG.SectionRank.pRank_le_map (Fact.out : q.p.Prime).one_lt ι hι _)
  have hZT : Nat.card (center ((R : Subgroup Y) ⊓ K : Subgroup Y)) = q.p := by
    have e₁ := (projUnitriangular 3 F).equivMapOfInjective ι hι
    rw [← hTι, ← CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3.map_center_mulEquiv e₁,
      card_map_of_injective e₁.injective, card_center_projUnitriangular_three, hF]
  have hN := normalizer_inf_le_of_card_center_eq R hER hE hEc hcore hZ hout h2 hZT
  exact exists_pCore_inf_of_forall_normalizer_le R
    (fun T H hTH hH => exists_pCore_of_normalizer_le_of_mulEquiv e
      (fun T' H' h1 h2 => linThree_model_overgroups T' H' h1 h2) T H hTH hH)
    (inf_le_left.trans hN) hKY₀

theorem threeFourTwoLinThree_holds : ThreeFourTwoLinThree := by
  intro p hp hp2 q d hqp hq1 hd
  obtain ⟨hX, hnab, hout⟩ := linThree_catalog_facts hp hqp hq1 hd
  refine threeFourTwoNoneAt_of_inf hX hnab hout ?_
  intro Y _ _ K Y₀ E R _ _ hK hKX _ _ _ hER hE hEc hcore _ hKY₀
  exact Or.inr (threeFourTwoLinThree_inf hp hp2 hqp hq1 hd R hK hKX hER hE hEc hcore hKY₀)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
