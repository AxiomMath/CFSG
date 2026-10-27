module

public import CFSG.ClassicalInvolution.Asc77.AscT7Z4
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenDihedral
public import CFSG.ClassicalInvolution.Asc77.AscT7Z3
public import CFSG.ClassicalInvolution.Asc77.WP3Layer
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement MatrixGroups

namespace C22G

set_option linter.unusedSectionVars false

section Layer

variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] {Φ : Set (Subgroup X)}


structure PSULayer (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Φ : Set (Subgroup G)) where
  ψ : (modelUniv .PSU 4 p f Fact.out).K →* G
  ker_le : ψ.ker ≤ Subgroup.center (modelUniv .PSU 4 p f Fact.out).K
  range_eq : ψ.range = omegaGen Φ
  fund : ∀ L ∈ Φ, ∃ R ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p f Fact.out).D,
    L = R.map ψ

theorem admissible_psu4 (hq : 5 ≤ p ^ f) :
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 4 p f := by
  refine ⟨Fact.out, ?_, by norm_num, ?_⟩
  · rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  · simp

theorem nonempty_psuLayer_of_lieSystemData [Finite X] (D : LieSystemData p f X Φ)
    (hcard : D.card = 1) (i : Fin D.card) (hit : D.tag i = .PSU) (hir : D.rank i = 4)
    (hie : D.exp i = f) (hgen : omegaGen Φ = ⊤) : Nonempty (PSULayer p f Φ) := by
  have hsub : Subsingleton (Fin D.card) := by
    rw [hcard]
    infer_instance
  have key : ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e : ℕ)
      (ψ : (modelUniv t k p e Fact.out).K →* X),
      t = .PSU → k = 4 → e = f → ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K →
      ψ.range = omegaGen Φ →
      (∀ L ∈ Φ, ∃ R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D, L = R.map ψ) →
      Nonempty (PSULayer p f Φ) := by
    rintro t k e ψ rfl rfl rfl hker hr hf
    exact ⟨⟨ψ, hker, hr, hf⟩⟩
  refine key _ _ _ (D.hom i) hit hir hie (D.ker_le_center i) ?_ ?_
  · have h1 : ⨆ j, (D.hom j).range = (D.hom i).range :=
      le_antisymm (iSup_le fun j => by rw [Subsingleton.elim j i])
        (le_iSup (fun j => (D.hom j).range) i)
    rw [← h1, D.generate, hgen]
  · intro L hL
    obtain ⟨j, R, hR, hLR⟩ := D.fundamental L hL
    obtain rfl : j = i := Subsingleton.elim j i
    exact ⟨R, hR, hLR⟩

theorem card_center_su_four_le {K : Type} [Field K] [Finite K] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card (Subgroup.center (Phan.Su K p f 4)) ≤ 4 := by
  classical
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK
  have hu : ∀ z : Subgroup.center (Phan.Su K p f 4), ∃ u : Kˣ,
      (((z : Phan.Su K p f 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        Matrix.scalar (Fin 4) (u : K) := fun z =>
    Phan.exists_scalar_of_mem_center hσ (by norm_num) z.2
  choose φ hφ using hu
  have hdet : ∀ z : Subgroup.center (Phan.Su K p f 4), φ z ^ 4 = 1 := by
    intro z
    have h1 := (CFSG.ClassicalGroups.Unitary.mem_SUid_iff
      (σ := CFSG.LieType.BorelTits.unitaryInvolution K p f)).mp (z : Phan.Su K p f 4).2
    have h2 := h1.1
    rw [hφ z, Matrix.scalar_apply, Matrix.det_diagonal] at h2
    have h3 : ((φ z : Kˣ) : K) ^ 4 = 1 := by simpa using h2
    exact Units.ext (by simpa using h3)
  have hinj : Function.Injective fun z : Subgroup.center (Phan.Su K p f 4) =>
      (⟨φ z, (mem_rootsOfUnity 4 (φ z)).mpr (hdet z)⟩ : rootsOfUnity 4 K) := by
    intro z z' h
    have h1 : φ z = φ z' := congrArg (fun x : rootsOfUnity 4 K => (x : Kˣ)) h
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rw [hφ z, hφ z', h1]
  have h := Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card (rootsOfUnity 4 K) ≤ 4 := card_rootsOfUnity K 4
  exact h.trans h2

namespace PSULayer

theorem finite_U (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    Finite (modelUniv .PSU 4 p f Fact.out).K :=
  ModelFacts.finite_modelUniv hp2 Fact.out (by trivial) (admissible_psu4 hq)

theorem perfect_U (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    Group.IsPerfect (modelUniv .PSU 4 p f Fact.out).K := by
  obtain ⟨φ, -⟩ := RouteD.psu_model_equiv hp2 (admissible_psu4 hq)
  have hf1 : 1 ≤ f := (admissible_psu4 hq).2.1
  have hK := CFSG.LieType.Universal.card_galoisField_two_mul p f hf1
  have := RouteD.isPerfect_su_gen hK hq (n := 4) (by norm_num)
  exact Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective

theorem injOn_fund' (hq : 5 ≤ p ^ f) (P : PSULayer p f Φ)
    {R : Subgroup (modelUniv .PSU 4 p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p f Fact.out).D) :
    ∀ x ∈ R, P.ψ x = 1 → x = 1 := fun x hx hψ =>
  fund_noncentral_modelUniv (p := p) (e := f) (t := .PSU) (n := 4) (by trivial)
    (admissible_psu4 hq) (by rintro ⟨h, -⟩; cases h) R hR x hx
    (P.ker_le (MonoidHom.mem_ker.mpr hψ))

theorem oddCoreOf_fund (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (P : PSULayer p f Φ)
    {L : Subgroup X} {R : Subgroup (modelUniv .PSU 4 p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p f Fact.out).D)
    (hLR : L = R.map P.ψ) : oddCoreOf L = ⊥ := by
  have have_fin := finite_U (p := p) (f := f) hp2 hq
  obtain ⟨eR⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSU)
    (n := 4) (by trivial) (admissible_psu4 hq) (by decide) (by decide) hR
  have hinj : Function.Injective (P.ψ.comp R.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (injOn_fund' hq P hR x.1 x.2 hx)
  obtain ⟨eL⟩ := Balance.nonempty_equiv_of_map_eq R.subtype P.ψ hinj
    (K := L) (by rw [hLR, Subgroup.range_subtype])
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f
    (by rintro rfl; simp at hq)
  have h2F : (2 : GaloisField p f) ≠ 0 := by
    intro h
    have : (2 : ℕ) = 0 ∨ p = 2 := by
      have := (CharP.cast_eq_zero_iff (GaloisField p f) p 2).mp (by exact_mod_cast h)
      exact Or.inr ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)
    rcases this with h' | h'
    · omega
    · exact hp2 h'
  have h4F : 4 ≤ Nat.card (GaloisField p f) := by omega
  have hO1 := ModelFacts.LinearAut.oddCore_sl2_eq_bot h2F h4F
  have hO2 : classicalInvolutionOddCore ↥L = ⊥ := by
    have e : (classicalInvolutionOddCore ↥L).map (eL.trans eR).toMonoidHom =
        classicalInvolutionOddCore SL(2, GaloisField p f) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant (eL.trans eR)
    rw [hO1] at e
    exact (Subgroup.map_eq_bot_iff_of_injective _ (eL.trans eR).injective).mp e
  unfold oddCoreOf
  rw [hO2, Subgroup.map_bot]

end PSULayer

theorem psu_pair_of_lifts (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (ψ : (modelUniv .PSU 4 p f Fact.out).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv .PSU 4 p f Fact.out).K)
    {R₁ R₂ : Subgroup (modelUniv .PSU 4 p f Fact.out).K}
    (h₁ : R₁ ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p f Fact.out).D)
    (h₂ : R₂ ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p f Fact.out).D)
    {c₁ c₂ : (modelUniv .PSU 4 p f Fact.out).K} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (hc : c₁ * c₂ = c₂ * c₁)
    (hne : R₁.map ψ ≠ R₂.map ψ) (hnc : ¬ Commutes (R₁.map ψ) (R₂.map ψ)) :
    (∃ W, Phan.UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W R₁ R₂) ∧
      ∃ W, Phan.UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (R₁.map ψ) (R₂.map ψ) := by
  have hf : 1 ≤ f := (admissible_psu4 hq).2.1
  have hl₁ := ModelFacts.fundamentalSubgroups_subset_longest (t := .PSU) (by decide) (by decide)
    _ h₁
  have hl₂ := ModelFacts.fundamentalSubgroups_subset_longest (t := .PSU) (by decide) (by decide)
    _ h₂
  rcases ModelFacts.standardPairDichotomyTypes_psu (admissible_psu4 hq) hp2 hq R₁ hl₁ R₂ hl₂ c₁
    c₂ hc₁ hc₂ ho₁ ho₂ hc with h | h | ⟨hF, -⟩ | ⟨-, W, hW⟩
  · exact absurd (by rw [h]) hne
  · exact absurd (fun x hx y hy => by
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hy
      rw [← map_mul, ← map_mul, h x hx y hy]) hnc
  · exact hF.elim
  · exact ⟨⟨W, hW⟩, _, Balance.unitaryBlockStandardPair_map_of_ker_le_center
      (K₀ := GaloisField p (2 * f)) (CFSG.LieType.Universal.card_galoisField_two_mul p f hf) hq
      hW ψ hker⟩

theorem PSULayer.pair_of_member_ne (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (P : PSULayer p f Φ)
    {K K' L : Subgroup X}
    {RK RK' RL : Subgroup (modelUniv .PSU 4 p f Fact.out).K}
    (hRK : RK ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p f Fact.out).D)
    (hRL : RL ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p f Fact.out).D)
    (hKR : K = RK.map P.ψ) (hKR' : K' = RK'.map P.ψ) (hLR : L = RL.map P.ψ) {z t e a b : X}
    (hzK : IsUniqueInvolution K z) (htL : IsUniqueInvolution L t) (ha : a ∈ K) (hb : b ∈ K')
    (haa : a * a = z) (hcomm : Commutes K K') (he : e ∈ omegaGen Φ)
    (hec : ∀ y ∈ omegaGen Φ, e * y = y * e) (htab : t = a * b * e) (hne : K ≠ L)
    (hnc : ¬ Commutes K L) :
    (∃ W, Phan.UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W RK RL) ∧
      ∃ W, Phan.UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W K L := by
  have have_perf := PSULayer.perfect_U (p := p) (f := f) hp2 hq
  have := PSULayer.finite_U (p := p) (f := f) hp2 hq
  have hU : (⊤ : Subgroup (modelUniv .PSU 4 p f Fact.out).K) ≤
      ⁅(⊤ : Subgroup (modelUniv .PSU 4 p f Fact.out).K),
        (⊤ : Subgroup (modelUniv .PSU 4 p f Fact.out).K)⁆ :=
    (Subgroup.commutator_eq_self (H := (⊤ : Subgroup (modelUniv .PSU 4 p f Fact.out).K))).ge
  have hR₁ : RK ≤ ⁅RK, RK⁆ :=
    RouteD.Gaps.fundPerfect_modelUniv hp2 (by trivial) (admissible_psu4 hq) (by omega) RK hRK
  have hi₁ := PSULayer.injOn_fund' hq P hRK
  have hi₃ := PSULayer.injOn_fund' hq P hRL
  have hcomm' : Commutes (RK.map P.ψ) (RK'.map P.ψ) := by
    rw [← hKR, ← hKR']
    exact hcomm
  obtain ⟨c₁, hc₁, c₂, hc₂, ho₁, ho₂, -, -, hcc⟩ := T7Z.exists_commuting_lifts P.ψ P.ker_le hU hR₁
    hi₁ hi₃ (hKR ▸ ha) (hKR' ▸ hb) hcomm' (P.range_eq ▸ he)
    (fun y hy => hec y (P.range_eq ▸ hy)) haa hzK.sq hzK.ne_one (hLR ▸ htL.mem) htab htL.sq
    htL.ne_one
  have hne' : RK.map P.ψ ≠ RL.map P.ψ := by
    rw [← hKR, ← hLR]
    exact hne
  have hnc' : ¬ Commutes (RK.map P.ψ) (RL.map P.ψ) := by
    rw [← hKR, ← hLR]
    exact hnc
  obtain ⟨h1, h2⟩ := psu_pair_of_lifts hp2 hq P.ψ P.ker_le hRK hRL hc₁ hc₂ ho₁ ho₂ hcc hne' hnc'
  exact ⟨h1, by rw [← hKR, ← hLR] at h2; exact h2⟩

theorem unitaryBlockStandardPair_eq_sup' {K : Type} [Field K] [Finite K] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) {W U V : Subgroup X}
    (h : Phan.UnitaryBlockStandardPair K p f W U V) : W = U ⊔ V := by
  obtain ⟨θ, hrange, -, h1, h2⟩ := Phan.pair_normalize h
  rw [← hrange, MonoidHom.range_eq_map, ← Phan.B12_sup_B23 hK hq, Subgroup.map_sup, h1, h2]

theorem sup_eq_top_of_chain_psu (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {R₁ R₂ R₃ : Subgroup (modelUniv .PSU 4 p f Fact.out).K}
    (h12 : ∃ W, Phan.UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W R₁ R₂)
    (h23 : ∃ W, Phan.UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W R₂ R₃)
    (h13 : Commutes R₁ R₃) : R₁ ⊔ R₂ ⊔ R₃ = ⊤ := by
  classical
  have hf : 1 ≤ f := (admissible_psu4 hq).2.1
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hf
  have hq2 : p ^ f ≠ 2 := by omega
  have hfin := PSULayer.finite_U (p := p) (f := f) hp2 hq
  have hperf := PSULayer.perfect_U (p := p) (f := f) hp2 hq
  obtain ⟨φ, -⟩ := RouteD.psu_model_equiv hp2 (admissible_psu4 hq)
  set H : Subgroup (modelUniv .PSU 4 p f Fact.out).K := R₁ ⊔ R₂ ⊔ R₃ with hH
  have hR₁ : R₁ ≤ H := le_sup_left.trans le_sup_left
  have hR₂ : R₂ ≤ H := le_sup_right.trans le_sup_left
  have hR₃ : R₃ ≤ H := le_sup_right
  obtain ⟨W₁, hW₁⟩ := h12
  obtain ⟨W₂, hW₂⟩ := h23
  have hW₁H : W₁ ≤ H := by
    rw [unitaryBlockStandardPair_eq_sup' hK hq2 hW₁]
    exact sup_le hR₁ hR₂
  have hW₂H : W₂ ≤ H := by
    rw [unitaryBlockStandardPair_eq_sup' hK hq2 hW₂]
    exact sup_le hR₂ hR₃
  let U' : Fin 3 → Subgroup ↥H := ![R₁.subgroupOf H, R₂.subgroupOf H, R₃.subgroupOf H]
  have hcomm : ∀ i j : Fin 3, (i : ℕ) + 1 < j → ∀ x ∈ U' i, ∀ y ∈ U' j, x * y = y * x := by
    intro i j hij x hx y hy
    fin_cases i <;> fin_cases j <;> simp at hij
    exact Subtype.ext (h13 _ hx _ hy)
  have hpair : ∀ i j : Fin 3, (j : ℕ) = i + 1 →
      ∃ W, Phan.UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (U' i) (U' j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    · exact ⟨_, Generic.unitaryBlockStandardPair_subgroupOf hW₁H hW₁⟩
    · exact ⟨_, Generic.unitaryBlockStandardPair_subgroupOf hW₂H hW₂⟩
  have hgen : ⨆ i, U' i = ⊤ := by
    have h1 := Subgroup.subgroupOf_sup (A := R₁ ⊔ R₂) (A' := R₃) (B := H) (sup_le hR₁ hR₂) hR₃
    have h2 := Subgroup.subgroupOf_sup (A := R₁) (A' := R₂) (B := H) hR₁ hR₂
    have h3 : (R₁ ⊔ R₂ ⊔ R₃).subgroupOf H = ⊤ := Subgroup.subgroupOf_self H
    refine eq_top_iff.mpr ?_
    rw [← h3, h1, h2]
    exact sup_le (sup_le (le_iSup U' 0) (le_iSup U' 1)) (le_iSup U' 2)
  have hP₀₁ := hpair 0 1 rfl
  have hP₁₂ := hpair 1 2 rfl
  have hW : Phan.WeakPhanA (GaloisField p (2 * f)) p f 3 U' (fun i j => U' i ⊔ U' j) := by
    refine ⟨?_, fun _ _ _ => rfl, hcomm, ?_, hgen⟩
    · intro i
      obtain ⟨W, hW⟩ := hP₀₁
      obtain ⟨W', hW'⟩ := hP₁₂
      fin_cases i
      · exact (Phan.nonempty_mulEquiv_of_standardPair hK hW).1
      · exact (Phan.nonempty_mulEquiv_of_standardPair hK hW).2
      · exact (Phan.nonempty_mulEquiv_of_standardPair hK hW').2
    · intro i j hj
      obtain ⟨W, hW⟩ := hpair i j hj
      rwa [unitaryBlockStandardPair_eq_sup' hK hq2 hW] at hW
  obtain ⟨θ, hsurj, hker⟩ := Phan.weakPhan_recognition (GaloisField p (2 * f)) p f hK hq
    (n := 3) (by norm_num) hW
  have hcent : Nat.card θ.ker ≤ 4 :=
    (Subgroup.card_le_of_le hker).trans (card_center_su_four_le hK)
  have hkeridx : θ.ker.index = Nat.card ↥H := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hsurj).toEquiv
  have hcard : Nat.card (Phan.Su (GaloisField p (2 * f)) p f 4) =
      Nat.card (modelUniv .PSU 4 p f Fact.out).K := Nat.card_congr φ.symm.toEquiv
  have h1 : H.index * Nat.card ↥H = Nat.card (modelUniv .PSU 4 p f Fact.out).K :=
    Subgroup.index_mul_card H
  have h2 : θ.ker.index * Nat.card θ.ker = Nat.card (Phan.Su (GaloisField p (2 * f)) p f 4) :=
    Subgroup.index_mul_card θ.ker
  have hpos : 0 < Nat.card ↥H := Nat.card_pos
  have hidx : H.index = Nat.card θ.ker := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, ← hcard, ← h2, hkeridx, mul_comm]
  exact T7Z.eq_top_of_index_le_four H (hidx ▸ hcent)

theorem PSULayer.sup_eq_omegaGen (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (P : PSULayer p f Φ)
    {K J J' : Subgroup X} {RK RJ RJ' : Subgroup (modelUniv .PSU 4 p f Fact.out).K}
    (hRJ' : RJ' ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p f Fact.out).D)
    (hKR : K = RK.map P.ψ) (hJR : J = RJ.map P.ψ) (hJ'R : J' = RJ'.map P.ψ)
    (h1 : ∃ W, Phan.UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W RJ' RK)
    (h2 : ∃ W, Phan.UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W RK RJ)
    (hc : Commutes J J') : J' ⊔ K ⊔ J = omegaGen Φ := by
  have have_perf := PSULayer.perfect_U (p := p) (f := f) hp2 hq
  have := PSULayer.finite_U (p := p) (f := f) hp2 hq
  have hR₃ : RJ' ≤ ⁅RJ', RJ'⁆ :=
    RouteD.Gaps.fundPerfect_modelUniv hp2 (by trivial) (admissible_psu4 hq) (by omega) RJ' hRJ'
  have hcomm : Commutes RJ' RJ := by
    refine T7Z.commutes_of_map_commutes P.ψ P.ker_le hR₃ ?_
    rw [← hJR, ← hJ'R]
    exact hc.symm
  have htop : RJ' ⊔ RK ⊔ RJ = ⊤ := sup_eq_top_of_chain_psu hp2 hq h1 h2 hcomm
  rw [hKR, hJR, hJ'R, ← Subgroup.map_sup, ← Subgroup.map_sup, htop, Subgroup.map_top,
    P.range_eq]

theorem PSULayer.sup_eq_of_chain (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (P : PSULayer p f Φ)
    {K K' L L' : Subgroup X}
    {RK RK' RL RL' : Subgroup (modelUniv .PSU 4 p f Fact.out).K}
    (hRK : RK ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p f Fact.out).D)
    (hRL : RL ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p f Fact.out).D)
    (hRL' : RL' ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p f Fact.out).D)
    (hKR : K = RK.map P.ψ) (hKR' : K' = RK'.map P.ψ) (hLR : L = RL.map P.ψ)
    (hL'R : L' = RL'.map P.ψ) {z t e a b : X} (hzK : IsUniqueInvolution K z)
    (htL : IsUniqueInvolution L t) (htL' : IsUniqueInvolution L' t) (ha : a ∈ K) (hb : b ∈ K')
    (haa : a * a = z) (hcomm : Commutes K K') (hcomm' : Commutes L L')
    (he : e ∈ omegaGen Φ) (hec : ∀ y ∈ omegaGen Φ, e * y = y * e) (htab : t = a * b * e)
    (hne : K ≠ L) (hnc : ¬ Commutes K L) (hne' : K ≠ L') (hnc' : ¬ Commutes K L') :
    L' ⊔ K ⊔ L = omegaGen Φ := by
  obtain ⟨h1, -⟩ := PSULayer.pair_of_member_ne hp2 hq P hRK hRL hKR hKR' hLR hzK htL ha hb haa
    hcomm he hec htab hne hnc
  obtain ⟨⟨W₁, hW₁⟩, -⟩ := PSULayer.pair_of_member_ne hp2 hq P hRK hRL' hKR hKR' hL'R hzK htL'
    ha hb haa hcomm he hec htab hne' hnc'
  exact PSULayer.sup_eq_omegaGen hp2 hq P hRL' hKR hLR hL'R
    ⟨W₁, Generic.unitaryBlockStandardPair_symm hW₁⟩ h1 hcomm'

end Layer

end C22G

end CFSG.ClassicalInvolution.Asc77
