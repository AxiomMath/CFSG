module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaOuter
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.NonsplitPlane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreA
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out
public import CFSG.Adapters.LinearCatalog
public import CFSG.RankThree.PartTwo.KFacts.AutPSL
public import CFSG.HardMathSupport.Timmesfeld.Balance.Reduction
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.DefChar.Families
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Matrix
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne.KCLinearSubfield
  CFSG.RankThree.PartTwo.KFacts

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem exists_cube_root_of_not_dvd (h : ¬ 3 ∣ Nat.card F - 1) (u : Fˣ) :
    ∃ v : Fˣ, v ^ 3 = u := by
  have hc : Nat.Coprime 3 (Nat.card Fˣ) := by
    rw [Nat.card_units, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    exact h
  obtain ⟨v, hv⟩ := (powCoprime hc.symm).surjective u
  exact ⟨v, hv⟩

omit [Finite F] in
theorem conjAut_mem_innerAut_of_not_dvd (h : ¬ 3 ∣ Nat.card F - 1) (A : GL (Fin 3) F) :
    conjAut 3 F A ∈ innerAut (projectiveSL 3 F) := by
  obtain ⟨v, hv⟩ := exists_cube_root_of_not_dvd h (Matrix.GeneralLinearGroup.det A)
  have hdet : Matrix.GeneralLinearGroup.det (A * Matrix.GeneralLinearGroup.scalar (Fin 3) v⁻¹) =
      1 := by
    rw [map_mul]
    have : Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.scalar (Fin 3) v⁻¹) = v⁻¹ ^ 3 := by
      apply Units.ext
      simp [Matrix.GeneralLinearGroup.det, Matrix.det_diagonal, Matrix.scalar_apply]
    rw [this, ← hv, inv_pow, mul_inv_cancel]
  have hmem : A * Matrix.GeneralLinearGroup.scalar (Fin 3) v⁻¹ ∈
      (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 3) F →* GL (Fin 3) F).range := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet
  obtain ⟨S, hS⟩ := hmem
  refine ⟨proj 3 F S, ?_⟩
  rw [conj_proj_eq_conjAut, hS, map_mul, conjAut_scalar, mul_one]

theorem exists_plane_gens {D : Subgroup (MulAut (projectiveSL 3 F))}
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 9) :
    ∃ x ∈ D, ∃ y ∈ D, x ≠ 1 ∧ y ∉ Subgroup.zpowers x := by
  have hD1 : D ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hD1
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ D, y ∉ Subgroup.zpowers x := by
    by_contra hcon
    push Not at hcon
    have hle : D ≤ Subgroup.zpowers x := hcon
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf x ≤ 3 :=
      Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hD.2 x hx))
    omega
  exact ⟨x, hx, y, hy, hx1', hyx⟩

omit [Finite F] in
theorem mul_scalar_comm_of_comm {A B : GL (Fin 3) F} (hAB : A * B = B * A) (a b : Fˣ) :
    (A * GeneralLinearGroup.scalar (Fin 3) a) * (B * GeneralLinearGroup.scalar (Fin 3) b) =
      (B * GeneralLinearGroup.scalar (Fin 3) b) * (A * GeneralLinearGroup.scalar (Fin 3) a) := by
  have h1 : ∀ (e : Fˣ) (M : GL (Fin 3) F), GeneralLinearGroup.scalar (Fin 3) e * M =
      M * GeneralLinearGroup.scalar (Fin 3) e := fun e M =>
    Matrix.GeneralLinearGroup.scalar_commute e M
  have aux : ∀ (X Y : GL (Fin 3) F) (x y : Fˣ),
      (X * GeneralLinearGroup.scalar (Fin 3) x) * (Y * GeneralLinearGroup.scalar (Fin 3) y) =
        (X * Y) * (GeneralLinearGroup.scalar (Fin 3) x * GeneralLinearGroup.scalar (Fin 3) y) := by
    intro X Y x y
    calc _ = X * (GeneralLinearGroup.scalar (Fin 3) x * Y) * GeneralLinearGroup.scalar (Fin 3) y := by
          simp only [mul_assoc]
      _ = X * (Y * GeneralLinearGroup.scalar (Fin 3) x) * GeneralLinearGroup.scalar (Fin 3) y := by
          rw [h1]
      _ = _ := by simp only [mul_assoc]
  rw [aux, aux, hAB, ← map_mul, ← map_mul, mul_comm a b]

omit [Finite F] in
theorem comm_of_elemAbelian {D : Subgroup (MulAut (projectiveSL 3 F))} (hD : IsElemAbelian 3 D)
    {x y : MulAut (projectiveSL 3 F)} (hx : x ∈ D) (hy : y ∈ D) : x * y = y * x :=
  CFSG.Open.IsElemAbelian.comm hD hx hy

theorem localDeltaIn_eq_bot_of_abelian_plane {D : Subgroup (MulAut (projectiveSL 3 F))}
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 9) (hDl : D ≤ linearAutGroup 3 F)
    (hF3 : 3 ∣ Nat.card F - 1)
    (hab : ∀ A ∈ D.comap (conjAut 3 F), ∀ B ∈ D.comap (conjAut 3 F), A * B = B * A)
    {H : Subgroup (MulAut (projectiveSL 3 F))} (hH : innerAut (projectiveSL 3 F) ≤ H) :
    localDeltaIn 3 H D = ⊥ := by
  obtain ⟨x, hx, y, hy, hx1, hyx⟩ := exists_plane_gens hD hcard
  rw [linearAutGroup_eq_range] at hDl
  obtain ⟨A, rfl⟩ := hDl hx
  obtain ⟨B, rfl⟩ := hDl hy
  have hAB : A * B = B * A := hab A hx B hy
  have hA3 : conjAut 3 F A ^ 3 = 1 := hD.2 _ hx
  have hB3 : conjAut 3 F B ^ 3 = 1 := hD.2 _ hy
  have hE : Subgroup.closure {conjAut 3 F A, conjAut 3 F B} ≤ D := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hE0 : localDeltaIn 3 H (Subgroup.closure {conjAut 3 F A, conjAut 3 F B}) = ⊥ := by
    by_cases hsp : (∃ c : Fˣ, A ^ 3 = GeneralLinearGroup.scalar (Fin 3) (c ^ 3)) ∧
        ∃ d : Fˣ, B ^ 3 = GeneralLinearGroup.scalar (Fin 3) (d ^ 3)
    · obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := hsp
      have hcA : conjAut 3 F (A * GeneralLinearGroup.scalar (Fin 3) c⁻¹) = conjAut 3 F A := by
        rw [map_mul, conjAut_scalar, mul_one]
      have hcB : conjAut 3 F (B * GeneralLinearGroup.scalar (Fin 3) d⁻¹) = conjAut 3 F B := by
        rw [map_mul, conjAut_scalar, mul_one]
      have hpow : ∀ (M : GL (Fin 3) F) (e : Fˣ),
          M ^ 3 = GeneralLinearGroup.scalar (Fin 3) (e ^ 3) →
            (M * GeneralLinearGroup.scalar (Fin 3) e⁻¹) ^ 3 = 1 := by
        intro M e hM
        rw [Commute.mul_pow (show Commute M (GeneralLinearGroup.scalar (Fin 3) e⁻¹) from
          (Matrix.GeneralLinearGroup.scalar_commute e⁻¹ M).symm), hM, ← map_pow, ← map_mul,
          inv_pow, mul_inv_cancel, map_one]
      have hcomm := mul_scalar_comm_of_comm hAB c⁻¹ d⁻¹
      have := localDeltaIn_eq_bot_of_split (le_refl 3) Nat.prime_three (by norm_num) hF3 hcomm
        (hpow A c hc) (hpow B d hd) (by rwa [hcA]) (by rw [hcA, hcB]; exact hyx) hH
      rwa [hcA, hcB] at this
    · exact localDeltaIn_eq_bot_of_nonsplit (le_refl 3) Nat.prime_three (by norm_num) hF3 hAB
        hA3 hB3 hx1 hyx hsp hH
  exact eq_bot_iff.2 ((localDeltaIn_antitone H hE).trans hE0.le)

theorem gLAPPrimeCoreOf_eq_bot_of_char_three (h3 : 3 ∣ Nat.card F)
    {x : MulAut (projectiveSL 3 F)} (hx : x ∈ innerAut (projectiveSL 3 F)) (hxo : orderOf x = 3)
    {H : Subgroup (MulAut (projectiveSL 3 F))} (hH : innerAut (projectiveSL 3 F) ≤ H) :
    GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({x} : Set (MulAut (projectiveSL 3 F)))) = ⊥ := by
  have := Fintype.ofFinite F
  obtain ⟨p, hp⟩ := CharP.exists F
  have hpp : p.Prime := CharP.char_is_prime F p
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  rw [← Nat.card_eq_fintype_card] at hn
  have hnz : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have hp3 : p = 3 := by
    rw [hn] at h3
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).1
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let q : TauCeti.PrimePower := ⟨3, n, Nat.prime_three, n.pos⟩
  have h32 : 3 ^ (n : ℕ) ≠ 2 := by
    have : 3 ≤ 3 ^ (n : ℕ) := Nat.le_self_pow n.ne_zero 3
    omega
  have hv : (TauCeti.LieTypeIndex.A 2 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [q, TauCeti.PrimePower.card_def]
    simp
    omega
  have : Fact (Nat.Prime q.p) := ⟨Nat.prime_three⟩
  have : Fintype (GaloisField 3 n) := Fintype.ofFinite _
  have hcard : Fintype.card F = Fintype.card (GaloisField 3 n) := by
    have h1 : Nat.card (GaloisField 3 n) = 3 ^ (n : ℕ) := GaloisField.card 3 n n.ne_zero
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hn, h1]
  let e : projectiveSL 3 F ≃* (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group :=
    (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr (FiniteField.ringEquivOfCardEq hcard)).trans
      ((LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 _).symm.trans
        (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).symm)
  have hnab : ∃ a b : projectiveSL 3 F, a * b ≠ b * a := by
    have := not_commutative_projectiveSL (n := 3) (K := F) le_rfl
    push Not at this
    exact this
  exact CFSG.HardMathSupport.Timmesfeld.DefChar.defCharInnerCoreFreeFamA_of_two_le
    (projectiveSL 3 F) (isSimpleGroup_projectiveSL (n := 3) (K := F) le_rfl) hnab ⟨.A 2 q, hv⟩ ⟨2, q, rfl, le_rfl⟩
    ⟨e⟩ 3 Nat.prime_three (by norm_num) (by simp [q]) x hx hxo H hH

theorem localDeltaIn_eq_bot_inner_plane (h4 : 4 ≤ Nat.card F) (hpF : ¬ 3 ∣ Nat.card F)
    (hpq : ¬ 3 ∣ Nat.card F - 1) (E₁ : Subgroup (projectiveSL 3 F)) (hE : IsElemAbelian 3 E₁)
    (hc : Nat.card E₁ = 3 ^ 2) {H : Subgroup (MulAut (projectiveSL 3 F))}
    (hH : innerAut (projectiveSL 3 F) ≤ H) :
    localDeltaIn 3 H (E₁.map (MulAut.conj : projectiveSL 3 F →* _)) = ⊥ := by
  set θ := LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F with hθ
  set ψ : MulAut (projectiveSL 3 F) ≃* MulAut (ProjectiveSpecialLinearGroup (Fin 3) F) :=
    (MulAut.congr θ.symm) with hψ
  have hψc : ∀ x : projectiveSL 3 F, ψ (MulAut.conj x) = MulAut.conj (θ.symm x) := fun x =>
    congr_conj_apply θ.symm x
  have hinj : Function.Injective
      (MulAut.conj : ProjectiveSpecialLinearGroup (Fin 3) F →* _) := by
    intro a b hab
    have h1 : MulAut.conj (θ a) = MulAut.conj (θ b) := by
      rw [← congr_conj_apply θ, ← congr_conj_apply θ]
      have h2 : ψ.symm (MulAut.conj a) = ψ.symm (MulAut.conj b) := by rw [hab]
      simpa [hψ] using h2
    exact θ.injective (CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := F)
      (le_refl 3) h1)
  have hE' : IsElemAbelian 3 (E₁.map θ.symm.toMonoidHom) :=
    isEkIn_map_mulEquiv 3 2 θ.symm
      (A := ⊤) (D := E₁) ⟨le_top, hE, hc⟩ |>.2.1
  have hc' : Nat.card (E₁.map θ.symm.toMonoidHom) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective θ.symm.injective, hc]
  have hH' : innerAut (ProjectiveSpecialLinearGroup (Fin 3) F) ≤ H.map ψ.toMonoidHom := by
    rintro _ ⟨y, rfl⟩
    refine ⟨MulAut.conj (θ y), hH ⟨θ y, rfl⟩, ?_⟩
    simp [hψc]
  have key := localDeltaIn_eq_bot_psl_nonsplit (n := 3) (F := F) Nat.prime_three (Or.inr h4) hpF
    hpq (by norm_num) hinj (E₁.map θ.symm.toMonoidHom) hE' hc' hH'
  have hmapD : (E₁.map (MulAut.conj : projectiveSL 3 F →* _)).map ψ.toMonoidHom =
      (E₁.map θ.symm.toMonoidHom).map (MulAut.conj : ProjectiveSpecialLinearGroup (Fin 3) F →* _) := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    exact MonoidHom.ext fun x => hψc x
  rw [← hmapD, localDeltaIn_map_mulEquiv] at key
  exact (Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).1 key

theorem localDeltaIn_eq_bot_of_not_dvd {D : Subgroup (MulAut (projectiveSL 3 F))}
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 9) (hDl : D ≤ linearAutGroup 3 F)
    (hF3 : ¬ 3 ∣ Nat.card F - 1) {H : Subgroup (MulAut (projectiveSL 3 F))}
    (hH : innerAut (projectiveSL 3 F) ≤ H) : localDeltaIn 3 H D = ⊥ := by
  have hinj := CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := F) (le_refl 3)
  have hDi : D ≤ innerAut (projectiveSL 3 F) := by
    intro z hz
    rw [linearAutGroup_eq_range] at hDl
    obtain ⟨A, rfl⟩ := hDl hz
    exact conjAut_mem_innerAut_of_not_dvd hF3 A
  by_cases hchar : 3 ∣ Nat.card F
  · obtain ⟨x, hx, y, hy, hx1, hyx⟩ := exists_plane_gens hD hcard
    have hxo : orderOf x = 3 := orderOf_eq_prime (hD.2 x hx) hx1
    refine eq_bot_iff.2 fun g hg => ?_
    have := le_core_of_mem_localDeltaIn hg hx hx1
    rw [gLAPPrimeCoreOf_eq_bot_of_char_three hchar (hDi hx) hxo hH] at this
    exact this
  · set E₁ : Subgroup (projectiveSL 3 F) := D.comap (MulAut.conj : projectiveSL 3 F →* _) with hE₁
    have hmap : E₁.map (MulAut.conj : projectiveSL 3 F →* _) = D :=
      Subgroup.map_comap_eq_self (show D ≤ (MulAut.conj : projectiveSL 3 F →* _).range from hDi)
    have hc : Nat.card E₁ = 3 ^ 2 := by
      rw [← Subgroup.card_map_of_injective hinj, hmap, hcard]
      norm_num
    have hE : IsElemAbelian 3 E₁ := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
      · apply Subtype.ext
        apply hinj
        have := comm_of_elemAbelian hD (x := MulAut.conj (a : projectiveSL 3 F))
          (y := MulAut.conj (b : projectiveSL 3 F)) a.2 b.2
        simpa using this
      · apply hinj
        rw [map_pow, map_one]
        exact hD.2 _ hz
    by_cases h4 : 4 ≤ Nat.card F
    · have := localDeltaIn_eq_bot_inner_plane h4 hchar hF3 E₁ hE hc hH
      rwa [hmap] at this
    · exfalso
      have hq2 : Nat.card F = 2 := by
        have := Finite.one_lt_card (α := F)
        omega
      have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) = 168 := by
        have := Fintype.ofFinite F
        rw [Matrix.card_SL, Matrix.card_GL_field, Nat.card_units, hq2]
        have hq : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card]; exact hq2
        simp [hq, Fin.prod_univ_three]
      have h1 : Nat.card (projectiveSL 3 F) ∣ 168 := by
        rw [← hSL]
        exact ⟨Nat.card (scalars 3 F), (Subgroup.card_eq_card_quotient_mul_card_subgroup _)⟩
      have h2 : Nat.card E₁ ∣ Nat.card (projectiveSL 3 F) := Subgroup.card_subgroup_dvd_card E₁
      rw [hc] at h2
      have := h2.trans h1
      omega

theorem conjAut_eq_one_of_mem_localDeltaIn {D H : Subgroup (MulAut (projectiveSL 3 F))}
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 9) (hH : innerAut (projectiveSL 3 F) ≤ H)
    {A : GL (Fin 3) F} (hα : conjAut 3 F A ∈ localDeltaIn 3 H D) : conjAut 3 F A = 1 := by
  by_cases hDl : D ≤ linearAutGroup 3 F
  swap
  · rw [localDeltaIn_eq_bot_of_not_le_linearAutGroup_three hD hDl hH] at hα
    exact Subgroup.mem_bot.1 hα
  by_cases hab : ∀ A ∈ D.comap (conjAut 3 F), ∀ B ∈ D.comap (conjAut 3 F), A * B = B * A
  · have hbot : localDeltaIn 3 H D = ⊥ := by
      by_cases hF3 : 3 ∣ Nat.card F - 1
      · exact localDeltaIn_eq_bot_of_abelian_plane hD hcard hDl hF3 hab hH
      · exact localDeltaIn_eq_bot_of_not_dvd hD hcard hDl hF3 hH
    rw [hbot] at hα
    exact Subgroup.mem_bot.1 hα
  · obtain ⟨-, -, hC, -⟩ :=
      ProjectivePlane.linear_projective_nonabelian_plane_coprime_centralizer_central (p := 3)
        Nat.prime_three (by norm_num) D hDl (fun x hx y hy => comm_of_elemAbelian hD hx hy) hD.2
        (by rw [hcard]; norm_num) hab
    have hmem : conjAut 3 F A ∈ Subgroup.centralizer (D : Set (MulAut (projectiveSL 3 F))) ⊓
        linearAutGroup 3 F :=
      ⟨Subgroup.mem_centralizer_iff.2 fun d hd => (commute_of_mem_localDeltaIn hα hd).symm,
        conjAut_mem_linearAutGroup A⟩
    rw [hC] at hmem
    obtain ⟨x, hx, -, -, hx1, -⟩ := exists_plane_gens hD hcard
    have hcop := coprime_orderOf_of_mem_localDeltaIn Nat.prime_three hα hx hx1
    have hdvd : orderOf (conjAut 3 F A) ∣ 3 := orderOf_dvd_of_pow_eq_one (hD.2 _ hmem)
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop.symm hdvd)

end CFSG.HardMathSupport.Solomon.Coordinator
