module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Basic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Split
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearThreeTwo

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

namespace AQ2

section Transport

open CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem noNormalPPrime_map_iff {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) (L : Subgroup G) {p : ℕ} :
    NoNormalPPrime p (L.map f) ↔ NoNormalPPrime p L := by
  constructor
  · intro h N hNL hNn hcop
    have hmap : N.map f = ⊥ := by
      refine h (N.map f) (Subgroup.map_mono hNL) ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩ _ ⟨x, hx, rfl⟩
        exact ⟨y * x * y⁻¹, hNn y hy x hx, by simp⟩
      · rwa [Subgroup.card_map_of_injective hf]
    exact (Subgroup.map_eq_bot_iff_of_injective N hf).1 hmap
  · intro h M hML hMn hcop
    set N : Subgroup G := M.comap f ⊓ L
    have hNM : N.map f = M := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx.1
      · intro hy
        obtain ⟨x, hxL, rfl⟩ := hML hy
        exact ⟨x, ⟨hy, hxL⟩, rfl⟩
    have hNbot : N = ⊥ := by
      refine h N inf_le_right ?_ ?_
      · intro y hy x hx
        refine ⟨?_, L.mul_mem (L.mul_mem hy hx.2) (L.inv_mem hy)⟩
        have : f y * f x * (f y)⁻¹ ∈ M := hMn (f y) (Subgroup.mem_map_of_mem f hy) (f x) hx.1
        simpa using this
      · rwa [← Subgroup.card_map_of_injective hf, hNM]
    rw [← hNM, hNbot, Subgroup.map_bot]

theorem core_eq_bot_of_noNormalPPrime {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    {L : Subgroup K} (h : NoNormalPPrime p L) : CFSG.Open.GLAPPrimeCoreOf p L = ⊥ :=
  h _ (CFSG.HardMathSupport.Timmesfeld.Balance.gLAPPrimeCoreOf_le_self' L)
    (fun g hg x hx => CFSG.HardMathSupport.Timmesfeld.Balance.gLAPPrimeCoreOf_conj_mem' g hg x hx)
    (CFSG.HardMathSupport.Timmesfeld.Balance.coprime_card_gLAPPrimeCoreOf' hp L)

end Transport

section GeneralLinear

open Matrix CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne

variable {E : Type} [Field E] [Finite E]

theorem noNormalPPrime_three_gl (hE : Nat.card E = 2 ∨ Nat.card E = 4) (m : ℕ) :
    NoNormalPPrime 3 (⊤ : Subgroup (GL (Fin m) E)) := by
  intro M _ hMn hMc
  have hMnorm : M.Normal := ⟨fun x hx g => by simpa using hMn g (Subgroup.mem_top g) x hx⟩
  have hunits : Nat.card Eˣ ∣ 3 := by
    rw [Nat.card_units]; rcases hE with h | h <;> rw [h] <;> norm_num
  by_cases hbig : 3 ≤ m ∨ (2 ≤ m ∧ Nat.card E = 4)
  ·
    have hm2 : 2 ≤ m := by omega
    have hqs : CFSG.IsQuasisimple (SpecialLinearGroup (Fin m) E) := by
      refine KCUnitary.isQuasisimple_SL hm2 ?_
      rcases hbig with h | ⟨-, h4⟩
      · exact Or.inl h
      · right
        have : Fintype E := Fintype.ofFinite E
        exact ⟨Finset.univ, by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4⟩
    have h3SL : 3 ∣ Nat.card (SpecialLinearGroup (Fin m) E) := by
      rcases hE with h2 | h4
      · exact dvd_card_SL_of_dvd_pow_sub_one (e := 2) Nat.prime_three (by norm_num [h2])
          (by norm_num) hm2 (by norm_num [h2])
      · exact dvd_card_SL_of_dvd_card_sub_one Nat.prime_three hm2 (by norm_num [h4])
    set S' : Subgroup (SpecialLinearGroup (Fin m) E) := M.comap SpecialLinearGroup.toGL
    have hS'n : S'.Normal := hMnorm.comap SpecialLinearGroup.toGL
    have hS'M : Nat.card S' ∣ Nat.card M := by
      rw [← Subgroup.card_map_of_injective (K := S') (f := SpecialLinearGroup.toGL)
        SpecialLinearGroup.toGL_injective]
      exact Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)
    have hS'c : Nat.Coprime 3 (Nat.card S') := hMc.coprime_dvd_right hS'M
    have hS'bot : S' = ⊥ := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hqs hS'n with htop | hcen
      · exfalso
        have h3 : 3 ∣ Nat.card S' := by rw [htop, Subgroup.card_top]; exact h3SL
        exact absurd (Nat.Coprime.eq_one_of_dvd hS'c h3) (by norm_num)
      · have hz := CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd
          (by omega : 1 ≤ m) E
        have hd3 : Nat.card S' ∣ 3 := by
          refine (Subgroup.card_dvd_of_le hcen).trans (hz.trans ((Nat.gcd_dvd_right _ _).trans ?_))
          rcases hE with h | h <;> rw [h] <;> norm_num
        exact Subgroup.eq_bot_of_card_eq _ (Nat.Coprime.eq_one_of_dvd hS'c.symm hd3)
    have hdet : Function.Injective
        ((GeneralLinearGroup.det : GL (Fin m) E →* Eˣ).comp M.subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hx' : (x : GL (Fin m) E) ∈
          (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) E →* _).range := by
        rw [SpecialLinearGroup.range_toGL_eq_ker_det]
        exact hx
      obtain ⟨s, hs⟩ := hx'
      have hsS' : s ∈ S' := Subgroup.mem_comap.2 (hs ▸ x.2)
      rw [hS'bot, Subgroup.mem_bot] at hsS'
      exact Subtype.ext (by rw [← hs, hsS', map_one]; rfl)
    have hMd : Nat.card M ∣ 3 := (Subgroup.card_dvd_of_injective _ hdet).trans hunits
    exact Subgroup.eq_bot_of_card_eq _ (Nat.Coprime.eq_one_of_dvd hMc.symm hMd)
  ·
    have hm : m ≤ 2 := by omega
    have hm2 : m = 2 → Nat.card E = 2 := by intro h; omega
    have : Fintype E := Fintype.ofFinite E
    have hGL := Matrix.card_GL_field (𝔽 := E) m
    rw [← Nat.card_eq_fintype_card] at hGL
    have hMd : Nat.card M ∣ Nat.card (GL (Fin m) E) := Subgroup.card_subgroup_dvd_card M
    have hpos : 0 < Nat.card M := Nat.card_pos
    interval_cases m
    · have h1 : Nat.card M ∣ 1 := by simpa [hGL] using hMd
      exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 h1)
    · have h1 : Nat.card (GL (Fin 1) E) = Nat.card E - 1 := by
        rw [hGL, Fin.prod_univ_one]; simp
      rw [h1] at hMd
      have h3 : Nat.card M ∣ 3 := hMd.trans (by rcases hE with h | h <;> rw [h] <;> norm_num)
      exact Subgroup.eq_bot_of_card_eq _ (Nat.Coprime.eq_one_of_dvd hMc.symm h3)
    ·
      have h2 : Nat.card E = 2 := hm2 rfl
      have h6 : Nat.card (GL (Fin 2) E) = 6 := by
        rw [hGL, Fin.prod_univ_two, h2]; norm_num
      rw [h6] at hMd
      have hle : Nat.card M ≤ 6 := Nat.le_of_dvd (by norm_num) hMd
      have hM12 : Nat.card M = 1 ∨ Nat.card M = 2 := by
        generalize Nat.card M = k at hMd hMc hpos hle
        interval_cases k <;> first | omega | (exfalso; revert hMc; decide) | (exfalso; omega)
      rcases hM12 with h1 | h2'
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        obtain ⟨y, hy1, huniq⟩ := (Nat.card_eq_two_iff' (1 : M)).1 h2'
        have hcentral : ∀ g : GL (Fin 2) E, g * (y : GL (Fin 2) E) * g⁻¹ = y := by
          intro g
          have hz : (⟨g * y * g⁻¹, hMn g (Subgroup.mem_top g) y y.2⟩ : M) = y := by
            refine huniq _ fun h1' => hy1 ?_
            have h2'' : g * (y : GL (Fin 2) E) * g⁻¹ = 1 := congrArg Subtype.val h1'
            have h3 : (y : GL (Fin 2) E) = 1 := by
              have := congrArg (fun z => g⁻¹ * z * g) h2''
              simpa [mul_assoc] using this
            exact Subtype.ext h3
          exact congrArg Subtype.val hz
        have hycenter : (y : GL (Fin 2) E) ∈ Subgroup.center (GL (Fin 2) E) := by
          rw [Subgroup.mem_center_iff]
          intro g
          have := hcentral g
          calc g * (y : GL (Fin 2) E) = g * y * g⁻¹ * g := by group
            _ = y * g := by rw [this]
        rw [GeneralLinearGroup.center_eq_range_scalar] at hycenter
        obtain ⟨c, hc⟩ := hycenter
        have hc1 : c = 1 := units_eq_one_of_card_two h2 c
        subst hc1
        apply hy1
        exact Subtype.ext (by rw [← hc, map_one]; rfl)

theorem noNormalPPrime_three_pi {ι : Type*} [DecidableEq ι] {E : ι → Type} [∀ b, Field (E b)]
    [∀ b, Finite (E b)] (hE : ∀ b, Nat.card (E b) = 2 ∨ Nat.card (E b) = 4) (m : ι → ℕ) :
    NoNormalPPrime 3 (⊤ : Subgroup (∀ b, GL (Fin (m b)) (E b))) := by
  intro N _ hNn hNc
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  funext b
  set Nb : Subgroup (GL (Fin (m b)) (E b)) :=
    N.map (Pi.evalMonoidHom (fun b => GL (Fin (m b)) (E b)) b)
  have hNb : Nb = ⊥ := by
    refine noNormalPPrime_three_gl (hE b) (m b) Nb le_top ?_ ?_
    · rintro y - _ ⟨n, hn, rfl⟩
      refine ⟨Pi.mulSingle b y * n * (Pi.mulSingle b y)⁻¹,
        hNn _ (Subgroup.mem_top _) n hn, ?_⟩
      simp
    · exact hNc.coprime_dvd_right (Subgroup.card_map_dvd N _)
  have : g b ∈ Nb := ⟨g, hg, rfl⟩
  rw [hNb, Subgroup.mem_bot] at this
  simpa using this

end GeneralLinear

section Centralizer

open Polynomial Matrix CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm

theorem noNormalPPrime_three_centralizer_gl {n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) {a : GL (Fin n) F} (ha : a ^ 3 = 1) :
    NoNormalPPrime 3 (Subgroup.centralizer ({a} : Set (GL (Fin n) F))) := by
  classical
  set x : Module.End F (Fin n → F) := Matrix.toLin' (a : Matrix (Fin n) (Fin n) F)
  have hpK : ((3 : ℕ) : F) ≠ 0 := CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card
    Nat.prime_three (by rw [hF]; norm_num)
  have haeval : Polynomial.aeval x (Polynomial.X ^ 3 - Polynomial.C (1 : F)) = 0 := by
    have hX : x = Matrix.toLinAlgEquiv' (a : Matrix (Fin n) (Fin n) F) :=
      (KCLinComm.toLinAlgEquiv'_eq_toLin' _).symm
    have ha3 : (a : Matrix (Fin n) (Fin n) F) ^ 3 = 1 := by
      have := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) ha
      simpa [Units.val_pow_eq_pow_val] using this
    rw [hX]
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [← map_pow, ha3]
    simp
  have hsq : Squarefree (minpoly F x) :=
    KCPrimary.squarefree_minpoly_of_aeval_eq_zero
      (Polynomial.separable_X_pow_sub_C (1 : F) hpK one_ne_zero).squarefree haeval
  have hrange : Subgroup.centralizer ({a} : Set (GL (Fin n) F)) =
      (⊤ : Subgroup (PiGL (Efac x) (mult x))).map (blockTheta hsq) := by
    rw [← MonoidHom.range_eq_map, range_blockTheta hsq,
      range_commutantUnitsToGL_eq_centralizer (x := x) a rfl]
  rw [hrange, noNormalPPrime_map_iff _ (blockTheta_injective hsq)]
  refine noNormalPPrime_three_pi (fun b => ?_) _
  obtain ⟨hirr, -, hdvd⟩ := mem_primaryFactors.1 b.2
  have hdvd3 : (b : F[X]) ∣ X ^ 3 - C (1 : F) := hdvd.trans (minpoly.dvd F x haeval)
  have hfac : (X ^ 3 - C (1 : F) : F[X]) = (X - C 1) * (X ^ 2 + X + C 1) := by
    simp only [map_one]; ring
  have hdeg : (b : F[X]).natDegree = 1 ∨ (b : F[X]).natDegree = 2 := by
    have hpos : 0 < (b : F[X]).natDegree :=
      Polynomial.natDegree_pos_iff_degree_pos.2 (Polynomial.degree_pos_of_irreducible hirr)
    rw [hfac] at hdvd3
    rcases hirr.prime.dvd_or_dvd hdvd3 with h | h
    · have := Polynomial.natDegree_le_of_dvd h (Polynomial.X_sub_C_ne_zero 1)
      rw [Polynomial.natDegree_X_sub_C] at this
      omega
    · have hq : (X ^ 2 + X + C (1 : F) : F[X]).natDegree = 2 := by compute_degree!
      have hq0 : (X ^ 2 + X + C (1 : F) : F[X]) ≠ 0 := by
        intro h0; rw [h0] at hq; simp at hq
      have := Polynomial.natDegree_le_of_dvd h hq0
      omega
  have hfin : Module.Finite F (Efac x b) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have hcard := Module.natCard_eq_pow_finrank (K := F) (V := Efac x b)
  rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hF] at hcard
  rcases hdeg with h | h <;> rw [h] at hcard <;> simp [hcard]

end Centralizer

end AQ2

section Psl

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem core_free_centralizer_psl_two {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) {e : Matrix.ProjectiveSpecialLinearGroup (Fin n) F} (he : e ^ 3 = 1) :
    GLAPPrimeCoreOf 3
      (Subgroup.centralizer ({e} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin n) F))) = ⊥ := by
  have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F) = ⊥ := by
    have h := CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (by omega : 1 ≤ n) F
    rw [hF, show 2 - 1 = 1 from rfl, Nat.gcd_one_right, Nat.dvd_one] at h
    exact Subgroup.eq_bot_of_card_eq _ h
  have hπinj : Function.Injective (toPSL n F) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_toPSL, hZ]
  have hGLsurj : Function.Surjective
      (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin n) F →* Matrix.GeneralLinearGroup (Fin n) F) := by
    intro A
    have hdet : (A : Matrix (Fin n) (Fin n) F).det = 1 := by
      have h := congrArg Units.val (units_eq_one_of_card_two hF (Matrix.GeneralLinearGroup.det A))
      rwa [Matrix.GeneralLinearGroup.val_det_apply] at h
    exact ⟨⟨_, hdet⟩, Units.ext rfl⟩
  let ψ : Matrix.SpecialLinearGroup (Fin n) F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) F :=
    MulEquiv.ofBijective (toPSL n F) ⟨hπinj, toPSL_surjective⟩
  let χ : Matrix.SpecialLinearGroup (Fin n) F ≃* Matrix.GeneralLinearGroup (Fin n) F :=
    MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
      ⟨Matrix.SpecialLinearGroup.toGL_injective, hGLsurj⟩
  let θ : Matrix.ProjectiveSpecialLinearGroup (Fin n) F ≃* Matrix.GeneralLinearGroup (Fin n) F :=
    ψ.symm.trans χ
  obtain ⟨s, rfl⟩ := toPSL_surjective (n := n) (F := F) e
  have hθ : θ (toPSL n F s) = Matrix.SpecialLinearGroup.toGL s := by
    show χ (ψ.symm (ψ s)) = _
    rw [ψ.symm_apply_apply]
    rfl
  have hs3 : s ^ 3 = 1 := by
    apply hπinj
    rw [map_pow, he, map_one]
  have ha : (Matrix.SpecialLinearGroup.toGL s) ^ 3 = 1 := by
    rw [← map_pow, hs3, map_one]
  have hcent : (Subgroup.centralizer
      ({toPSL n F s} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin n) F))).map θ.toMonoidHom =
      Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL s} :
        Set (Matrix.GeneralLinearGroup (Fin n) F)) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hθ, ← map_mul, ← map_mul, hx]
    · intro hy
      refine ⟨θ.symm y, ?_, θ.apply_symm_apply y⟩
      apply θ.injective
      rw [map_mul, map_mul, θ.apply_symm_apply, hθ]
      exact hy
  have hNN : NoNormalPPrime 3 (Subgroup.centralizer
      ({toPSL n F s} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin n) F))) := by
    rw [← AQ2.noNormalPPrime_map_iff θ.toMonoidHom θ.injective, hcent]
    exact AQ2.noNormalPPrime_three_centralizer_gl hF ha
  exact AQ2.core_eq_bot_of_noNormalPPrime Nat.prime_three hNN

end Psl

namespace AQ2

section Balance

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem isLocallyBalancedAbs_three_two_psl_two {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2)
    (hinj : Function.Injective (MulAut.conj : Matrix.ProjectiveSpecialLinearGroup (Fin n) F →*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) F))) :
    IsLocallyBalancedAbs 3 2 (Matrix.ProjectiveSpecialLinearGroup (Fin n) F) := by
  intro D hD hcard H hH _
  have hDin : D ≤ innerAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) F) := fun x hx =>
    mem_innerAut_psl_of_odd_card_two hF hn (by
      rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one (hD.2 x hx)) with h | h
      · rw [h]; exact odd_one
      · rw [h]; decide)
  have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F) = ⊥ := by
    have h := CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (by omega : 1 ≤ n) F
    rw [hF, show 2 - 1 = 1 from rfl, Nat.gcd_one_right, Nat.dvd_one] at h
    exact Subgroup.eq_bot_of_card_eq _ h
  set E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) F) :=
    D.comap (MulAut.conj : Matrix.ProjectiveSpecialLinearGroup (Fin n) F →* _)
  have hEmap : E.map (MulAut.conj : Matrix.ProjectiveSpecialLinearGroup (Fin n) F →* _) = D :=
    Subgroup.map_comap_eq_self hDin
  have hEel : IsElemAbelian 3 E := isElemAbelian_comap _ hinj hD
  have hEcard : Nat.card E = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hEmap, hcard]
    norm_num
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEexp : ∀ x ∈ E, x ^ 3 = 1 := hEel.2
  have h3 : (3 : F) ≠ 0 := by
    exact_mod_cast CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card Nat.prime_three
      (by rw [hF]; norm_num)
  have hZ' : ¬ 3 ∣ Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)) := by
    rw [hZ, Subgroup.card_bot]
    norm_num
  have hgen := CFSG.LieType.SeitzGeneration.closure_centralizers_psl_three_ab (by omega) h3 hZ' E
    hEcomm hEexp hEcard
  refine localDeltaIn_eq_bot_of_closure_centralizers Nat.prime_three hinj hH ?_ ?_
  · refine eq_top_iff.2 (hgen ▸ Subgroup.closure_mono ?_)
    rintro k ⟨x, hxE, hx1, hkx⟩
    refine ⟨MulAut.conj x, hxE, fun h => hx1 (hinj (by rw [h, map_one])), ?_⟩
    rw [mem_centralizerOf, ← map_mul, ← map_mul, hkx]
  · intro d hd hd1
    obtain ⟨x, rfl⟩ := hDin hd
    have hxE : x ∈ E := hd
    have hcent : centralizerOf (MulAut.conj x) = Subgroup.centralizer ({x} : Set _) := by
      ext k
      rw [mem_centralizerOf, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      exact ⟨fun h => hinj h, fun h => by rw [h]⟩
    rw [hcent]
    exact noNormalPPrime_of_core_eq_bot (core_free_centralizer_psl_two hn hF (hEexp x hxE))

end Balance

end AQ2

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.DefChar

theorem localTwoCrossFamAt_three_A_two :
    LocalTwoCrossFamAt 3 .A fun idx =>
      ∃ (m : ℕ) (q : TauCeti.PrimePower), idx.1 = .A m q ∧ 2 ≤ m ∧ q.card = 2 := by
  rintro ⟨d, hv⟩ _ ⟨m, q, hd, hm2, hq⟩ _ _
  change d = _ at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hm3 : 3 ≤ m + 1 := by omega
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  let e := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv
  have hsimple := (CFSG.LinearGroups.linear_projective_simple (n := m + 1)
    (K := GaloisField q.p q.exponent) (by omega) (Or.inl hm3)).2.1
  have hperf := (CFSG.LinearGroups.linear_projective_perfect (n := m + 1)
    (K := GaloisField q.p q.exponent) (by omega) (Or.inl hm3)).commutator_eq_top
  have hinjP := CFSG.LieType.SeitzGeneration.conj_injective_of_simple_perfect hperf
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (AQ2.isLocallyBalancedAbs_three_two_psl_two (n := m + 1) hm3 (by rw [hcardF, hq]) hinjP)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
