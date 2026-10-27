module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.BalanceFromYS
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CrossCharOdd
public import CFSG.HardMathSupport.Solomon.Coordinator.WeakHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.BalanceLp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut localDeltaIn)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open Matrix

section Groups

theorem exists_pGroup_image {G A : Type*} [Group G] [Group A] [Finite G] {p : ℕ} [Fact p.Prime]
    (ρ : G →* A) {D : Subgroup A} (hD : IsPGroup p D) (hDr : D ≤ ρ.range) :
    ∃ P : Subgroup G, IsPGroup p P ∧ (∀ g ∈ P, ρ g ∈ D) ∧ ∀ d ∈ D, ∃ g ∈ P, ρ g = d := by
  set W := D.comap ρ with hW
  let f : W →* D := (ρ.comp W.subtype).codRestrict D fun w => w.2
  have hf : Function.Surjective f := by
    rintro ⟨d, hd⟩
    obtain ⟨g, rfl⟩ := hDr hd
    exact ⟨⟨g, hd⟩, rfl⟩
  obtain ⟨S₀⟩ : Nonempty (Sylow p W) := Sylow.nonempty
  have htop : ((S₀.mapSurjective hf : Sylow p D) : Subgroup D) = ⊤ :=
    ((S₀.mapSurjective hf).is_maximal' (hD.to_subgroup ⊤) le_top).symm
  refine ⟨(S₀ : Subgroup W).map W.subtype, S₀.isPGroup'.map _, ?_, ?_⟩
  · rintro _ ⟨w, -, rfl⟩
    exact w.2
  · intro d hd
    have hmem : (⟨d, hd⟩ : D) ∈ ((S₀.mapSurjective hf : Sylow p D) : Subgroup D) :=
      htop ▸ Subgroup.mem_top _
    rw [Sylow.coe_mapSurjective] at hmem
    obtain ⟨w, hw, hwd⟩ := hmem
    exact ⟨w, ⟨w, hw, rfl⟩, congrArg Subtype.val hwd⟩

theorem mul_comm_of_central {G : Type*} [Group G] {a b c d : G} (hc : ∀ g, c * g = g * c)
    (hd : ∀ g, d * g = g * d) (h : (a * c) * (b * d) = (b * d) * (a * c)) : a * b = b * a := by
  have e1 : (a * c) * (b * d) = a * b * (c * d) := by
    calc (a * c) * (b * d) = a * (c * b) * d := by group
      _ = a * (b * c) * d := by rw [hc b]
      _ = a * b * (c * d) := by group
  have e2 : (b * d) * (a * c) = b * a * (c * d) := by
    calc (b * d) * (a * c) = b * (d * a) * c := by group
      _ = b * (a * d) * c := by rw [hd a]
      _ = b * a * (d * c) := by group
      _ = b * a * (c * d) := by rw [hd c]
  rw [e1, e2] at h
  exact mul_right_cancel h

end Groups

section Transfer

variable {Y M : Type*} [Group Y] [Group M]

@[expose] noncomputable def modelHom (ε : (Y ⧸ Subgroup.center Y) ≃* M) : MulAut Y →* MulAut M :=
  (MulAut.congr ε).toMonoidHom.comp (Lemma123.autQ Y)

theorem modelHom_apply (ε : (Y ⧸ Subgroup.center Y) ≃* M) (b : MulAut Y) :
    modelHom ε b = MulAut.congr ε (Lemma123.autQ Y b) := rfl

theorem modelHom_injective (hY : commutator Y = ⊤) (ε : (Y ⧸ Subgroup.center Y) ≃* M) :
    Function.Injective (modelHom ε) :=
  (MulAut.congr ε).injective.comp (Lemma123.autQ_injective hY)

theorem innerAut_le_map_modelHom (ε : (Y ⧸ Subgroup.center Y) ≃* M) :
    innerAut M ≤ (innerAut Y).map (modelHom ε) := by
  rintro _ ⟨m, rfl⟩
  obtain ⟨q, rfl⟩ := ε.surjective m
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨MulAut.conj y, ⟨y, rfl⟩, ?_⟩
  rw [modelHom_apply, Lemma123.autQ_conj, Inputs123a.congr_conj]

theorem not_balanced_modelHom [Finite Y] [Finite M] {p : ℕ} (hY : commutator Y = ⊤)
    (ε : (Y ⧸ Subgroup.center Y) ≃* M) {B : Subgroup (MulAut Y)} (h : ¬ IsLocallyOTwoBalanced p 2 B) :
    ¬ IsLocallyOTwoBalanced p 2 (B.map (modelHom ε)) := fun h' =>
  h (Inputs123a.isLocallyOTwoBalanced_of_map (modelHom ε) (modelHom_injective hY ε)
    (innerAut_le_map_modelHom ε) h')

theorem exists_delta_of_not_balanced {K : Type*} [Group K] {p : ℕ} (hp : p.Prime)
    {D : Subgroup (MulAut K)} (hDc : Nat.card D = p ^ 2) (h : ¬ IsLocallyOTwoBalanced p 2 D) :
    ∃ H : Subgroup (MulAut K), innerAut K ≤ H ∧ D ≤ Subgroup.normalizer (H : Set (MulAut K)) ∧
      localDeltaTwoIn H D ≠ ⊥ := by
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hDc]; exact pow_ne_zero 2 hp.ne_zero)
  unfold IsLocallyOTwoBalanced at h
  push Not at h
  obtain ⟨D', ⟨hD'D, -, hD'c⟩, H, hH, hD'H, hΔ⟩ := h
  obtain rfl : D' = D := Subgroup.eq_of_le_of_card_ge hD'D (by rw [hDc, hD'c])
  exact ⟨H, hH, hD'H, hΔ⟩

end Transfer

section Cores

theorem linear_heis_core {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : p ∣ Nat.card F - 1) {D : Subgroup (MulAut (projectiveSL p F))} (hD : IsElemAbelian p D)
    (hDc : Nat.card D = p ^ 2) (hnb : ¬ IsLocallyOTwoBalanced p 2 D) :
    ∃ P : Subgroup (GL (Fin p) F), IsPGroup p P ∧ (∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x) ∧
      (∀ g ∈ P, conjAut p F g ∈ D) ∧ ∀ d ∈ D, ∃ g ∈ P, conjAut p F g = d := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨H, hH, hDH, hΔ⟩ := exists_delta_of_not_balanced hp hDc hnb
  have hΔ' : localDeltaIn p H D ≠ ⊥ := fun h0 =>
    hΔ (le_bot_iff.1 ((BalanceFromYS.localDeltaTwoIn_le_localDeltaIn hp hp2 H D).trans h0.le))
  have hDl : D ≤ linearAutGroup p F := by
    by_contra hDl
    exact hΔ' (CFSG.HardMathSupport.Timmesfeld.CrossChar.localDeltaIn_eq_bot_of_not_le_linearAutGroup
      hn hp hp2 hpF hD hDl hH)
  have hDr : D ≤ (conjAut p F).range := fun d hd => by
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 (hDl hd)
    exact ⟨A, hA⟩
  obtain ⟨x, hx, y, hy, hx1, hyx, hgen⟩ :=
    CFSG.HardMathSupport.Timmesfeld.LocalTwo.exists_gen_pair hp hD hDc
  obtain ⟨A0, rfl⟩ := hDr hx
  obtain ⟨B0, rfl⟩ := hDr hy
  have hAB : A0 * B0 ≠ B0 * A0 := by
    intro hAB
    apply hΔ'
    rw [← hgen]
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.diagAbelianPlaneBalance_holds p F hn p hp hp2 hpF dvd_rfl
      A0 B0 hAB (hD.2 _ hx) (hD.2 _ hy) hx1 hyx H hH (hgen ▸ hDH)
  obtain ⟨P, hP, hPD, hDP⟩ := exists_pGroup_image (conjAut p F) hD.isPGroup hDr
  refine ⟨P, hP, ?_, hPD, hDP⟩
  obtain ⟨x', hx'P, hx'⟩ := hDP _ hx
  obtain ⟨y', hy'P, hy'⟩ := hDP _ hy
  refine ⟨x', hx'P, y', hy'P, fun hxy => hAB ?_⟩
  obtain ⟨c, hc⟩ := CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis.eq_scalar_of_conjAut_eq_one hn
    (B := A0⁻¹ * x') (by rw [map_mul, map_inv, hx', inv_mul_cancel])
  obtain ⟨d, hd⟩ := CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis.eq_scalar_of_conjAut_eq_one hn
    (B := B0⁻¹ * y') (by rw [map_mul, map_inv, hy', inv_mul_cancel])
  have hx'e : x' = A0 * GeneralLinearGroup.scalar (Fin p) c := by rw [hc]; group
  have hy'e : y' = B0 * GeneralLinearGroup.scalar (Fin p) d := by rw [hd]; group
  rw [hx'e, hy'e] at hxy
  exact mul_comm_of_central (fun g => GeneralLinearGroup.scalar_commute c g)
    (fun g => GeneralLinearGroup.scalar_commute d g) hxy

theorem unitary_heis_core {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hne : ¬(p = 3 ∧ ℓ ^ f = 2)) (hpq : p ∣ ℓ ^ f + 1)
    {D : Subgroup (MulAut (primeFormP h (idGram K p)))} (hD : IsElemAbelian p D)
    (hDc : Nat.card D = p ^ 2) (hnb : ¬ IsLocallyOTwoBalanced p 2 D) :
    ∃ P : Subgroup (primeFormUnitary h (idGram K p)), IsPGroup p P ∧ (∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x) ∧
      (∀ g ∈ P, primeFormConjHom h (idGram K p) g ∈ D) ∧
        ∀ d ∈ D, ∃ g ∈ P, primeFormConjHom h (idGram K p) g = d := by
  have := h.finite
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨H, hH, hDH, hΔ⟩ := exists_delta_of_not_balanced hp hDc hnb
  have hΔ' : localDeltaIn p H D ≠ ⊥ := fun h0 =>
    hΔ (le_bot_iff.1 ((BalanceFromYS.localDeltaTwoIn_le_localDeltaIn hp hp2 H D).trans h0.le))
  by_cases h8 : p = 3 ∧ ℓ ^ f = 8
  · obtain ⟨rfl, h8'⟩ := h8
    obtain ⟨hl2, hf3⟩ := CFSG.HardMathSupport.Solomon.Coordinator.w3_pp_eq_eight h.prime h8'
    exact (hΔ' (CFSG.HardMathSupport.Solomon.Coordinator.u38_isLocallyBalancedAbs' h hl2 hf3 D hD hDc H hH
      hDH)).elim
  have hDl : D ≤ primeFormD h (idGram K p) := by
    by_contra hDl
    exact hΔ' (CFSG.HardMathSupport.Timmesfeld.CrossChar.localDeltaIn_eq_bot_of_not_le_primeFormD h hn hne hp
      hp2 hpq (CFSG.HardMathSupport.Solomon.Coordinator.not_three_pow_div_eq_two h hne h8 hD hDl) hD hDl hH)
  have hDr : D ≤ (primeFormConjHom h (idGram K p)).range := hDl
  obtain ⟨x, hx, y, hy, hx1, hyx, hgen⟩ :=
    CFSG.HardMathSupport.Timmesfeld.LocalTwo.exists_gen_pair hp hD hDc
  obtain ⟨A0, rfl⟩ := hDr hx
  obtain ⟨B0, rfl⟩ := hDr hy
  have hq3 := CFSG.HardMathSupport.Solomon.Coordinator.three_lt_of_dvd_add_one h hp hp2 hne hpq
  have hAB : A0 * B0 ≠ B0 * A0 := by
    intro hAB
    apply hΔ'
    rw [← hgen]
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.localDeltaIn_eq_bot_of_unitary_plane hn hne hq3 hp hp2 hpq
      hAB (hD.2 _ hx) (hD.2 _ hy) hx1 hyx hH
  obtain ⟨P, hP, hPD, hDP⟩ := exists_pGroup_image (primeFormConjHom h (idGram K p)) hD.isPGroup hDr
  refine ⟨P, hP, ?_, hPD, hDP⟩
  obtain ⟨x', hx'P, hx'⟩ := hDP _ hx
  obtain ⟨y', hy'P, hy'⟩ := hDP _ hy
  refine ⟨x', hx'P, y', hy'P, fun hxy => hAB ?_⟩
  have hc : primeFormConjHom h (idGram K p) (A0⁻¹ * x') = 1 := by
    rw [map_mul, map_inv, hx', inv_mul_cancel]
  have hd : primeFormConjHom h (idGram K p) (B0⁻¹ * y') = 1 := by
    rw [map_mul, map_inv, hy', inv_mul_cancel]
  have hx'e : x' = A0 * (A0⁻¹ * x') := by group
  have hy'e : y' = B0 * (B0⁻¹ * y') := by group
  rw [hx'e, hy'e] at hxy
  exact mul_comm_of_central
    (fun g => (CFSG.RankThree.PartOne.KCUnitaryModel.commute_of_mem_ker_of_ne hn hne hc g).eq)
    (fun g => (CFSG.RankThree.PartOne.KCUnitaryModel.commute_of_mem_ker_of_ne hn hne hd g).eq) hxy

end Cores

section Glue

theorem congr_apply_apply {G H : Type*} [Group G] [Group H] (ϕ : G ≃* H) (f : MulAut G) (x : H) :
    MulAut.congr ϕ f x = ϕ (f (ϕ.symm x)) := rfl

variable {n : ℕ} {F : Type} [Field F]

@[expose] noncomputable def statedProjEquivProjectiveSL (n : ℕ) (F : Type) [Field F] :
    StatedProj (StatedSL n F) ≃* projectiveSL n F :=
  (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n F).symm.trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL n F)

theorem statedProjEquivProjectiveSL_mk (s : SpecialLinearGroup (Fin n) F) :
    statedProjEquivProjectiveSL n F
        (QuotientGroup.mk (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n F s)) =
      proj n F s := by
  have h1 : CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n F (QuotientGroup.mk s) =
      QuotientGroup.mk (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n F s) := rfl
  rw [statedProjEquivProjectiveSL, MulEquiv.trans_apply, ← h1, MulEquiv.symm_apply_apply]
  rfl

theorem conjAut_statedProjEquiv (g : GL (Fin n) F) (A A' : StatedSL n F)
    (hA : (A' : GL (Fin n) F) = g * A * g⁻¹) :
    conjAut n F g (statedProjEquivProjectiveSL n F (QuotientGroup.mk A)) =
      statedProjEquivProjectiveSL n F (QuotientGroup.mk A') := by
  obtain ⟨s, rfl⟩ := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n F).surjective A
  obtain ⟨s', rfl⟩ := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n F).surjective A'
  rw [statedProjEquivProjectiveSL_mk, statedProjEquivProjectiveSL_mk, conjAut_proj]
  congr 1
  ext i j
  rw [coe_slConjugation]
  have h1 := congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F) i j) hA
  simp only [Units.val_mul, CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe] at h1
  exact h1.symm

theorem mem_normalizer_statedSL (g : GL (Fin n) F) :
    g ∈ Subgroup.normalizer (StatedSL n F : Set (GL (Fin n) F)) := by
  have hN : (StatedSL n F).Normal := by
    rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det]
    exact MonoidHom.normal_ker _
  rw [Subgroup.mem_normalizer_iff]
  intro A
  refine ⟨fun hA => hN.conj_mem A hA g, fun hA => ?_⟩
  have := hN.conj_mem _ hA g⁻¹
  simpa [mul_assoc] using this

theorem actsAsConj_linear {Y : Type*} [Group Y] (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL n F))
    (b : MulAut Y) (g : GL (Fin n) F)
    (hb : modelHom (θ.trans (statedProjEquivProjectiveSL n F)) b = conjAut n F g) :
    Prop1116Design.ActsAsConj (StatedSL n F) θ g b := by
  refine ⟨MulAut.congr θ (Lemma123.autQ Y b), ⟨mem_normalizer_statedSL g, fun A A' hA => ?_⟩,
    fun y => ?_⟩
  · have h1 := conjAut_statedProjEquiv g A A' hA
    rw [← hb, modelHom_apply, congr_apply_apply, MulEquiv.symm_trans_apply, MulEquiv.symm_apply_apply,
      MulEquiv.trans_apply] at h1
    rw [congr_apply_apply]
    exact (statedProjEquivProjectiveSL n F).injective h1
  · rw [congr_apply_apply, MulEquiv.symm_apply_apply, Lemma123.autQ_mk]

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

theorem statedSU_eq_gramSU (n : ℕ) : StatedSU n (ℓ ^ f) K = gramSU h (idGram K n) :=
  unitarySU_eq_gramSU h n

@[expose] noncomputable def unitaryPSUEquivPrimeFormI (n : ℕ) :
    unitaryPSU h n ≃* primeFormP h (idGram K n) :=
  QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n)) (by
    ext z
    constructor
    · rintro ⟨y, ⟨c, hcN, hcn, hy⟩, rfl⟩
      exact ⟨c, hcN, hcn, hy⟩
    · rintro ⟨c, hcN, hcn, hz⟩
      exact ⟨(MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n)).symm z, ⟨c, hcN, hcn, hz⟩,
        MulEquiv.apply_symm_apply _ _⟩)

@[expose] noncomputable def statedProjEquivPrimeFormP {n : ℕ} (hn : 1 ≤ n) :
    StatedProj (StatedSU n (ℓ ^ f) K) ≃* primeFormP h (idGram K n) :=
  (unitaryPSUEquiv h hn).symm.trans (unitaryPSUEquivPrimeFormI h n)

theorem statedProjEquivPrimeFormP_mk {n : ℕ} (hn : 1 ≤ n) (A : StatedSU n (ℓ ^ f) K) :
    statedProjEquivPrimeFormP h hn (QuotientGroup.mk A) =
      QuotientGroup.mk (⟨A, statedSU_eq_gramSU h n ▸ A.2⟩ : gramSU h (idGram K n)) := by
  have h1 : unitaryPSUEquiv h hn (unitaryProj h n A) = QuotientGroup.mk A :=
    unitaryPSUEquiv_unitaryProj h hn A
  rw [statedProjEquivPrimeFormP, MulEquiv.trans_apply, ← h1, MulEquiv.symm_apply_apply]
  rfl

theorem primeFormConjHom_statedProjEquiv {n : ℕ} (hn : 1 ≤ n) (g : primeFormUnitary h (idGram K n))
    (A A' : StatedSU n (ℓ ^ f) K) (hA : (A' : GL (Fin n) K) = g * A * (g : GL (Fin n) K)⁻¹) :
    primeFormConjHom h (idGram K n) g (statedProjEquivPrimeFormP h hn (QuotientGroup.mk A)) =
      statedProjEquivPrimeFormP h hn (QuotientGroup.mk A') := by
  rw [statedProjEquivPrimeFormP_mk, statedProjEquivPrimeFormP_mk, primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  exact hA.symm

theorem mem_normalizer_statedSU {n : ℕ} (g : primeFormUnitary h (idGram K n)) :
    (g : GL (Fin n) K) ∈ Subgroup.normalizer (StatedSU n (ℓ ^ f) K : Set (GL (Fin n) K)) := by
  rw [statedSU_eq_gramSU h n, Subgroup.mem_normalizer_iff]
  intro A
  refine ⟨fun hA => conj_mem_gramSU h _ g.2 hA, fun hA => ?_⟩
  have := conj_mem_gramSU h _ (inv_mem g.2) hA
  simpa [mul_assoc] using this

theorem primeFormUnitary_le_GUn (n : ℕ) :
    primeFormUnitary h (idGram K n) ≤ Prop1116Design.GUn n (ℓ ^ f) K := by
  intro g hg
  apply Subgroup.subset_closure
  have hg' : ((g : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (g : Matrix (Fin n) (Fin n) K) = 1 := by
    have := (mem_primeFormUnitary (h := h)).1 hg
    simpa [idGram] using this
  have hbar : (g : Matrix (Fin n) (Fin n) K).map h.bar = (g : Matrix (Fin n) (Fin n) K).map (· ^ (ℓ ^ f)) :=
    Matrix.ext fun i j => h.bar_apply _
  show ((g : Matrix (Fin n) (Fin n) K).map (· ^ (ℓ ^ f)))ᵀ * (g : Matrix (Fin n) (Fin n) K) = 1
  rw [← hbar]
  exact hg'

theorem actsAsConj_unitary {n : ℕ} (hn : 1 ≤ n) {Y : Type*} [Group Y]
    (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSU n (ℓ ^ f) K)) (b : MulAut Y)
    (g : primeFormUnitary h (idGram K n))
    (hb : modelHom (θ.trans (statedProjEquivPrimeFormP h hn)) b = primeFormConjHom h (idGram K n) g) :
    Prop1116Design.ActsAsConj (StatedSU n (ℓ ^ f) K) θ (g : GL (Fin n) K) b := by
  refine ⟨MulAut.congr θ (Lemma123.autQ Y b), ⟨mem_normalizer_statedSU h g, fun A A' hA => ?_⟩,
    fun y => ?_⟩
  · have h1 := primeFormConjHom_statedProjEquiv h hn g A A' hA
    rw [← hb, modelHom_apply, congr_apply_apply, MulEquiv.symm_trans_apply, MulEquiv.symm_apply_apply,
      MulEquiv.trans_apply] at h1
    rw [congr_apply_apply]
    exact (statedProjEquivPrimeFormP h hn).injective h1
  · rw [congr_apply_apply, MulEquiv.symm_apply_apply, Lemma123.autQ_mk]

end Glue

section Cases

theorem linear_case {m : ℕ} (hp : (m + 1).Prime) (hp2 : m + 1 ≠ 2) {Y : Type} [Group Y] [Finite Y]
    (hY : commutator Y = ⊤) (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A m Q).Valid)
    (hQ : Q.card % (m + 1) = 1)
    (e : (Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.lie ⟨.A m Q, hv⟩).Group)
    (B' : Subgroup (MulAut Y)) (hB'el : IsElemAbelian (m + 1) B') (hB'c : Nat.card B' = (m + 1) ^ 2)
    (hnb : ¬ IsLocallyOTwoBalanced (m + 1) 2 B') :
    IsLpType (m + 1) (Q.p ^ Q.exponent) (Y ⧸ Subgroup.center Y) ∧ m + 1 ∣ Q.p ^ Q.exponent - 1 ∧
      Prop1116Design.HeisenbergImageL (m + 1) (Q.p ^ Q.exponent) B' := by
  have : Fact Q.p.Prime := ⟨Q.prime_p⟩
  have hF : Nat.card (GaloisField Q.p Q.exponent) = Q.p ^ Q.exponent :=
    GaloisField.card _ _ Q.exponent_pos.ne'
  have hpF : m + 1 ∣ Nat.card (GaloisField Q.p Q.exponent) - 1 :=
    CFSG.HardMathSupport.Solomon.Coordinator.dvd_card_galoisField_sub_one hp.one_lt Q hQ
  let θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL (m + 1) (GaloisField Q.p Q.exponent)) :=
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m Q hv)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (m + 1) _)
  let ε := θ.trans (statedProjEquivProjectiveSL (m + 1) (GaloisField Q.p Q.exponent))
  have : Finite (Y ⧸ Subgroup.center Y) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have : Finite (projectiveSL (m + 1) (GaloisField Q.p Q.exponent)) := Finite.of_equiv _ ε.toEquiv
  have hD : IsElemAbelian (m + 1) (B'.map (modelHom ε)) := hB'el.map _
  have hDc : Nat.card (B'.map (modelHom ε)) = (m + 1) ^ 2 := by
    rw [Subgroup.card_map_of_injective (modelHom_injective hY ε), hB'c]
  obtain ⟨P, hP, hnab, hPD, hDP⟩ := linear_heis_core hp hp2 hpF hD hDc (not_balanced_modelHom hY ε hnb)
  refine ⟨⟨GaloisField Q.p Q.exponent, inferInstance, inferInstance, hF, ⟨θ⟩⟩, by rw [← hF]; exact hpF,
    GaloisField Q.p Q.exponent, inferInstance, inferInstance, θ, hF, P, le_top, hP, hnab, fun b hb => ?_,
    fun g hg => ?_⟩
  · obtain ⟨g, hgP, hg⟩ := hDP _ ⟨b, hb, rfl⟩
    exact ⟨g, hgP, actsAsConj_linear θ b g hg.symm⟩
  · obtain ⟨b, hb, hbg⟩ := hPD g hg
    exact ⟨b, hb, actsAsConj_linear θ b g hbg⟩

theorem unitary_case {m : ℕ} (hp : (m + 1).Prime) (hp2 : m + 1 ≠ 2) {Y : Type} [Group Y] [Finite Y]
    (hY : commutator Y = ⊤) (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA m Q).Valid)
    (hQ : (Q.card + 1) % (m + 1) = 0)
    (e : (Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA m Q, hv⟩).Group)
    (B' : Subgroup (MulAut Y)) (hB'el : IsElemAbelian (m + 1) B') (hB'c : Nat.card B' = (m + 1) ^ 2)
    (hnb : ¬ IsLocallyOTwoBalanced (m + 1) 2 B') :
    IsUpType (m + 1) (Q.p ^ Q.exponent) (Y ⧸ Subgroup.center Y) ∧ m + 1 ∣ Q.p ^ Q.exponent + 1 ∧
      Prop1116Design.HeisenbergImageU (m + 1) (Q.p ^ Q.exponent) B' := by
  have : Fact Q.p.Prime := ⟨Q.prime_p⟩
  obtain ⟨⟨hℓ, hf, -, hq⟩, K, _, _, hK, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m Q hv e
  have h : UnitaryFieldData Q.p Q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hne : ¬(m + 1 = 3 ∧ Q.p ^ Q.exponent = 2) := fun h2 => hq (by rw [h2.1, h2.2])
  have hpq : m + 1 ∣ Q.p ^ Q.exponent + 1 := by
    rw [← TauCeti.PrimePower.card_def]
    exact Nat.dvd_of_mod_eq_zero hQ
  have hn1 : 1 ≤ m + 1 := by omega
  let ε := eT.trans (statedProjEquivPrimeFormP h hn1)
  have : Finite (Y ⧸ Subgroup.center Y) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have : Finite (primeFormP h (idGram K (m + 1))) := Finite.of_equiv _ ε.toEquiv
  have hD : IsElemAbelian (m + 1) (B'.map (modelHom ε)) := hB'el.map _
  have hDc : Nat.card (B'.map (modelHom ε)) = (m + 1) ^ 2 := by
    rw [Subgroup.card_map_of_injective (modelHom_injective hY ε), hB'c]
  obtain ⟨P, hP, ⟨x, hx, y, hy, hxy⟩, hPD, hDP⟩ :=
    unitary_heis_core h hp hp2 hne hpq hD hDc (not_balanced_modelHom hY ε hnb)
  refine ⟨⟨K, inferInstance, inferInstance, hK, ⟨eT⟩⟩, hpq, K, inferInstance, inferInstance, eT, hK,
    P.map (primeFormUnitary h (idGram K (m + 1))).subtype, ?_, hP.map _,
    ⟨x, ⟨x, hx, rfl⟩, y, ⟨y, hy, rfl⟩, fun h' => hxy (Subtype.ext h')⟩, fun b hb => ?_, ?_⟩
  · rintro _ ⟨g, -, rfl⟩
    exact primeFormUnitary_le_GUn h (m + 1) g.2
  · obtain ⟨g, hgP, hg⟩ := hDP _ ⟨b, hb, rfl⟩
    exact ⟨g, ⟨g, hgP, rfl⟩, actsAsConj_unitary h hn1 eT b g hg.symm⟩
  · rintro _ ⟨g, hgP, rfl⟩
    obtain ⟨b, hb, hbg⟩ := hPD g hgP
    exact ⟨b, hb, actsAsConj_unitary h hn1 eT b g hbg⟩

end Cases

section Char

set_option linter.unusedSectionVars false


open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieSylowExponent lieOrderDivisor
  lieOrderNumerator)

theorem eq_three_of_sylow_le_six {p k N : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hk : 1 ≤ k) (hN : N ≤ 6)
    (h : p * (p - 1) / 2 * k = N) : p = 3 ∧ 3 * k = N := by
  have hp5 : p < 5 := by
    by_contra hc
    have h1 : 20 ≤ p * (p - 1) := by
      have : 4 ≤ p - 1 := by omega
      nlinarith
    have h2 : 10 ≤ p * (p - 1) / 2 := by omega
    have h3 : 10 ≤ p * (p - 1) / 2 * k := le_trans h2 (Nat.le_mul_of_pos_right _ hk)
    omega
  interval_cases p
  · exact ⟨rfl, by simpa using h⟩
  · exact absurd hp (by decide)

theorem char_eq_of_model {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2) {S : Type} [Group S]
    (hchev : IsChevSimple q S) (idx : TauCeti.ValidLieTypeIndex)
    (e : S ≃* (TauCeti.CFSGIndex.lie idx).Group) {t : StatedLieTag} {r k : ℕ}
    (hX : CFSG.Blueprint.LieModel S t p r k)
    (ht : (t = .PSL ∧ r ^ k % p = 1) ∨ (t = .PSU ∧ (r ^ k + 1) % p = 0)) : r = q := by
  have hO : LieOrderFormulasInput := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have hadm := hX.admissible
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have htLU : t = .PSL ∨ t = .PSU := by
    rcases ht with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hsyl : lieSylowExponent t p = p * (p - 1) / 2 := by
    rcases htLU with rfl | rfl <;> rfl
  rcases hchev with hc | hc
  · obtain ⟨-, -, t', n', f', hY⟩ := CrossCharOdd.lie_cases hc
    by_cases hr2 : r = 2
    · subst hr2
      exfalso
      have hadm' := hY.admissible
      rcases CFSG.SeitzReduction.CrossChar.crossChar_arith hadm hadm' hq2 (hO S _ _ _ _ hadm hX).2.1
          (hO S _ _ _ _ hadm' hY).2.1 with ⟨-, h2, -⟩ | ⟨htP, h3, hk1, -⟩ | ⟨-, h4, -⟩
      · exact hp2 h2
      · subst h3 hk1
        rcases ht with ⟨-, h⟩ | ⟨h, -⟩
        · norm_num at h
        · rw [htP] at h
          exact absurd h (by decide)
      · subst h4
        exact absurd hp (by decide)
    · exact CFSG.ComponentClassification.GS82PumpInputs.oddLieCharUnique_holds S t p r k t' n' q f' hr2 hq2
        hX hY
  · exfalso
    rcases CrossCharOdd.ambig_cases hq2 hc with ⟨⟨a⟩, -⟩ | ⟨⟨a⟩, -⟩ | ⟨-, -, -, hY | hY⟩
    · exact (AltFacts4.inputAltNotLie_holds 5 idx (by norm_num)).false (a.symm.trans e)
    · exact (AltFacts4.inputAltNotLie_holds 6 idx (by norm_num)).false (a.symm.trans e)
    ·
      have hadmY := hY.admissible
      by_cases hr2 : r = 2
      · subst hr2
        have h1 := (hO S _ _ _ _ hadm hX).2.2
        have h2 := (hO S _ _ _ _ hadmY hY).2.2
        rw [h1, hsyl] at h2
        have h3 : lieSylowExponent .PSL 2 * 3 = 3 := by decide
        rw [h3] at h2
        obtain ⟨rfl, hk⟩ := eq_three_of_sylow_le_six hp hp3 hadm.2.1 (by norm_num) h2
        obtain rfl : k = 1 := by omega
        rcases ht with ⟨-, h⟩ | ⟨rfl, -⟩
        · norm_num at h
        · exact hadm.2.2.2 (by norm_num)
      · rcases CFSG.SeitzReduction.CrossChar.crossChar_arith hadmY hadm hr2 (hO S _ _ _ _ hadmY hY).2.1
            (hO S _ _ _ _ hadm hX).2.1 with ⟨-, -, h, -⟩ | ⟨-, h, -⟩ | ⟨h, -⟩
        · exact absurd h (by norm_num)
        · exact absurd h (by norm_num)
        · exact absurd h (by decide)
    ·
      have hadmY := hY.admissible
      by_cases hr2 : r = 2
      · subst hr2
        have h1 := (hO S _ _ _ _ hadm hX).2.2
        have h2 := (hO S _ _ _ _ hadmY hY).2.2
        rw [h1, hsyl] at h2
        have h3 : lieSylowExponent .PSU 4 * 1 = 6 := by decide
        rw [h3] at h2
        obtain ⟨rfl, hk⟩ := eq_three_of_sylow_le_six hp hp3 hadm.2.1 le_rfl h2
        obtain rfl : k = 2 := by omega
        rcases ht with ⟨rfl, -⟩ | ⟨-, h⟩
        ·
          have o1 := (hO S _ _ _ _ hadm hX).2.1
          have o2 := (hO S _ _ _ _ hadmY hY).2.1
          have e1 : lieOrderDivisor .PSL 3 (2 ^ 2) = 3 := by decide
          have e2 : lieOrderNumerator .PSL 3 (2 ^ 2) = 60480 := by decide
          have e3 : lieOrderDivisor .PSU 4 (2 ^ 1) = 1 := by decide
          have e4 : lieOrderNumerator .PSU 4 (2 ^ 1) = 25920 := by decide
          rw [e1, e2] at o1
          rw [e3, e4] at o2
          omega
        · norm_num at h
      · rcases CFSG.SeitzReduction.CrossChar.crossChar_arith hadmY hadm hr2 (hO S _ _ _ _ hadmY hY).2.1
            (hO S _ _ _ _ hadm hX).2.1 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, h, -⟩
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · rcases htLU with rfl | rfl
          · exact absurd h (by decide)
          · exact absurd h (by decide)

theorem input19_7_3Lp_holds : BalanceFromYS.Input19_7_3Lp := by
  intro p q hp hp2 _ hq2 _ Y _ _ hY _ hchev hL B' hB'el hB'c hnb
  obtain ⟨idx, hidx, ⟨e⟩⟩ := hL
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  obtain ⟨d, hv⟩ := idx
  change CFSG.HardMathSupport.Timmesfeld.LocalTwo.IsLpEpsIndex (m + 1) d at hidx
  rcases hidx with ⟨Q, hd, hQ⟩ | ⟨Q, hd, hQ⟩
  · simp only [Nat.add_sub_cancel] at hd
    subst hd
    have : Fact Q.p.Prime := ⟨Q.prime_p⟩
    have hX : CFSG.Blueprint.LieModel (Y ⧸ Subgroup.center Y) .PSL (m + 1) Q.p Q.exponent :=
      CFSG.Blueprint.LieModel.of_mulEquiv e.symm
        (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
          (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA m Q hv))
    obtain rfl : Q.p = q := char_eq_of_model hp hp2 hq2 hchev _ e hX
      (Or.inl ⟨rfl, by rw [← TauCeti.PrimePower.card_def]; exact hQ⟩)
    obtain ⟨h1, h2, h3⟩ := linear_case hp hp2 hY.1 Q hv hQ e B' hB'el hB'c hnb
    exact ⟨Q.exponent, Or.inl ⟨h1, h2, h3⟩⟩
  · simp only [Nat.add_sub_cancel] at hd
    subst hd
    have : Fact Q.p.Prime := ⟨Q.prime_p⟩
    have hX : CFSG.Blueprint.LieModel (Y ⧸ Subgroup.center Y) .PSU (m + 1) Q.p Q.exponent :=
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
        (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_of_classical
          (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m Q hv e))
    obtain rfl : Q.p = q := char_eq_of_model hp hp2 hq2 hchev _ e hX
      (Or.inr ⟨rfl, by rw [← TauCeti.PrimePower.card_def]; exact hQ⟩)
    obtain ⟨h1, h2, h3⟩ := unitary_case hp hp2 hY.1 Q hv hQ e B' hB'el hB'c hnb
    exact ⟨Q.exponent, Or.inr ⟨h1, h2, h3⟩⟩

end Char

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.BalanceLp
