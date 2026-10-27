module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.SectionRank.OddCover.ScalarCover
public import CFSG.LocalAnalysis.SectionRank.OddCover.PrimeThree
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearSplit
public import CFSG.LocalAnalysis.SectionRank.EvenCover.UnitaryThree
public import CFSG.LocalAnalysis.SectionRank.ExceptionalEvenCover
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.SectionAssembly
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312Facts
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
public import Certificates.Certificate8026Base

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.SectionRank.OddCover Subgroup

section Scalars

variable {F : Type} [Field F] [Finite F]

theorem card_scalars_dvd_dim {n p f : ℕ} (hn : 1 ≤ n) {H : Subgroup (GL (Fin n) F)}
    (hH : (Nat.card F = p ^ f ∧ H = StatedSL n F) ∨
      (Nat.card F = (p ^ f) ^ 2 ∧ H = StatedSU n (p ^ f) F)) :
    Nat.card ((StatedScalars (Fin n) F).subgroupOf H) ∣ n :=
  card_scalars_dvd hn H fun x c hc => by
    have hdet := det_eq_one_of_linUni hH x.1.2
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])

theorem card_scalars_dvd_three {p f : ℕ} {H : Subgroup (GL (Fin 3) F)}
    (hH : (Nat.card F = p ^ f ∧ H = StatedSL 3 F) ∨
      (Nat.card F = (p ^ f) ^ 2 ∧ H = StatedSU 3 (p ^ f) F)) :
    Nat.card ((StatedScalars (Fin 3) F).subgroupOf H) ∣ 3 :=
  card_scalars_dvd_dim (by norm_num) hH

theorem card_scalars_statedSL_dvd_pred :
    Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)) ∣ Nat.card F - 1 :=
  card_scalars_dvd (by norm_num) _ fun _ c _ => by
    rw [← card_units_eq]
    exact pow_card_eq_one'

theorem card_scalars_statedSU_dvd_succ {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hK : Nat.card F = (p ^ f) ^ 2) (hq0 : p ^ f ≠ 0) :
    Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (p ^ f) F)) ∣ p ^ f + 1 :=
  card_scalars_dvd (by norm_num) _ fun x c hc => by
    have hu := unitary_of_mem_statedSU hK x.1.2
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar] at hu
    have h00 := congrFun (congrFun hu (0 : Fin 3)) (0 : Fin 3)
    rw [Matrix.scalar_apply, Matrix.diagonal_map (by simp [zero_pow hq0]),
      Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.one_apply_eq,
      Matrix.diagonal_apply_eq] at h00
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_succ, Units.val_one]
    exact h00

end Scalars

section Cover

variable {X : Type} [Group X] [Finite X] [Group.IsPerfect X]

theorem triple_cover_linear (h3 : Nat.card (Subgroup.center X) = 3) {F : Type} [Field F] [Finite F]
    {p f : ℕ} (hF : Nat.card F = p ^ f)
    (e : X ⧸ Subgroup.center X ≃* StatedProj (StatedSL 3 F))
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* StatedSL 3 F), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ s : StatedSL 3 F →* E, ∀ g, π (s g) = g) :
    3 ∣ Nat.card F - 1 ∧ Nonempty (X ≃* ↥(StatedSL 3 F)) := by
  have hodd : Odd (Nat.card (Subgroup.center X)) := by rw [h3]; decide
  obtain ⟨φ, hφ, -, -⟩ := exists_cover_map_of_odd_splitting hodd e hsplit
  obtain ⟨hD, hbij⟩ := bijective_of_scalar_cover e h3
    (card_scalars_dvd_three (p := p) (f := f) (Or.inl ⟨hF, rfl⟩)) hφ
  refine ⟨?_, ⟨(MulEquiv.ofBijective φ hbij).symm⟩⟩
  have := card_scalars_statedSL_dvd_pred (F := F)
  rwa [hD] at this

theorem triple_cover_unitary (h3 : Nat.card (Subgroup.center X) = 3) {F : Type} [Field F] [Finite F]
    {p f : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2)
    (e : X ⧸ Subgroup.center X ≃* StatedProj (StatedSU 3 (p ^ f) F))
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* StatedSU 3 (p ^ f) F),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ s : StatedSU 3 (p ^ f) F →* E, ∀ g, π (s g) = g) :
    3 ∣ p ^ f + 1 ∧ Nonempty (X ≃* ↥(StatedSU 3 (p ^ f) F)) := by
  have hodd : Odd (Nat.card (Subgroup.center X)) := by rw [h3]; decide
  have hq0 : p ^ f ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  obtain ⟨φ, hφ, -, -⟩ := exists_cover_map_of_odd_splitting hodd e hsplit
  obtain ⟨hD, hbij⟩ := bijective_of_scalar_cover e h3
    (card_scalars_dvd_three (p := p) (f := f) (Or.inr ⟨hF, rfl⟩)) hφ
  refine ⟨?_, ⟨(MulEquiv.ofBijective φ hbij).symm⟩⟩
  have := card_scalars_statedSU_dvd_succ (F := F) (p := p) (f := f) hF hq0
  rwa [hD] at this

end Cover

theorem modEq_one_of_dvd_two_pow_sub_one {f : ℕ} (h : 3 ∣ 2 ^ f - 1) :
    Int.ModEq 3 ((2 ^ f : ℕ) : ℤ) 1 := by
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  obtain ⟨k, hk⟩ := h
  have : ((2 ^ f : ℕ) : ℤ) = 3 * k + 1 := by omega
  rw [this]
  unfold Int.ModEq
  omega

theorem modEq_neg_one_of_dvd_two_pow_add_one {f : ℕ} (h : 3 ∣ 2 ^ f + 1) :
    Int.ModEq 3 ((2 ^ f : ℕ) : ℤ) (-1) := by
  obtain ⟨k, hk⟩ := h
  have : ((2 ^ f : ℕ) : ℤ) = 3 * k - 1 := by omega
  rw [this]
  unfold Int.ModEq
  omega

variable {X : Type} [Group X] [Finite X]

theorem a36Case2List_of_linear_even
    (hX : CFSG.IsQuasisimple X)
    (h3 : Nat.card (Subgroup.center X) = 3) {f : ℕ} (hf : 1 ≤ f)
    (h : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 3 2 f) : A36Case2List X := by
  have : Group.IsPerfect X := hX.1
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have : CharP F 2 := CFSG.SectionRank.charP_two_of_card hF
  obtain ⟨hdvd, ⟨iso⟩⟩ := triple_cover_linear h3 hF e fun E _ _ π hπ hC hodd => by
    obtain ⟨s, hs, -⟩ := CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting_stated
      (by norm_num) hπ hC hodd
    exact ⟨s, hs⟩
  rw [hF] at hdvd
  exact Or.inl ⟨true, 2, f, Nat.prime_two, hf, Or.inl ⟨rfl, modEq_one_of_dvd_two_pow_sub_one hdvd⟩,
    F, inferInstance, inferInstance, hF, ⟨iso⟩⟩

theorem false_of_linear_even_cover
    (hX : CFSG.IsQuasisimple X)
    (h3 : Nat.card (Subgroup.center X) = 3) {n f : ℕ} (hn : 2 ≤ n) (hn3 : ¬ 3 ∣ n)
    (h : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL n 2 f) : False := by
  have : Group.IsPerfect X := hX.1
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have : CharP F 2 := CFSG.SectionRank.charP_two_of_card hF
  have hodd : Odd (Nat.card (Subgroup.center X)) := by rw [h3]; decide
  obtain ⟨φ, -, -, hD⟩ := exists_cover_map_of_odd_splitting hodd e
    fun E _ _ π hπ hC hodd => by
      obtain ⟨s, hs, -⟩ :=
        CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting_stated hn hπ hC hodd
      exact ⟨s, hs⟩
  have h1 : Nat.card (Subgroup.center X) ∣ Nat.card ((StatedScalars (Fin n) F).subgroupOf
      (StatedSL n F)) := hD ▸ Subgroup.card_map_dvd _ φ
  have h2 := card_scalars_dvd_dim (n := n) (p := 2) (f := f) (by omega) (H := StatedSL n F)
    (Or.inl ⟨hF, rfl⟩)
  rw [h3] at h1
  exact hn3 (h1.trans h2)

theorem a36Case2List_of_unitary_even
    (hX : CFSG.IsQuasisimple X)
    (h3 : Nat.card (Subgroup.center X) = 3) {f : ℕ} (hf : 2 ≤ f)
    (h : StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 2 f) : A36Case2List X := by
  have : Group.IsPerfect X := hX.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have : CharP F 2 := CFSG.SectionRank.charP_two_of_card (f := f * 2) (by rw [hF, pow_mul])
  obtain ⟨hdvd, ⟨iso⟩⟩ := triple_cover_unitary h3 (p := 2) (f := f) hF e
    fun E _ _ π hπ hC hodd => by
      obtain ⟨s, hs, -⟩ :=
        CFSG.SectionRank.EvenCover.even_unitary_three_central_odd_extension_splitting hF hf hπ hC
          hodd
      exact ⟨s, hs⟩
  exact Or.inl ⟨false, 2, f, Nat.prime_two, by omega,
    Or.inl ⟨rfl, modEq_neg_one_of_dvd_two_pow_add_one hdvd⟩, F, inferInstance, inferInstance, hF,
    ⟨iso⟩⟩

theorem a36Case2List_of_classical_odd_three (hX : CFSG.IsQuasisimple X)
    (h3 : Nat.card (Subgroup.center X) = 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU)
    (h : StatedClassicalModel (X ⧸ Subgroup.center X) t 3 p 1) : A36Case2List X := by
  have : Group.IsPerfect X := hX.1
  have : Fact p.Prime := ⟨hp⟩
  rcases ht with rfl | rfl
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
    have hF' : Nat.card F = p := by rw [hF, pow_one]
    obtain ⟨-, ⟨iso⟩⟩ := triple_cover_linear (p := p) (f := 1) h3 hF e
      fun E _ _ π hπ hC hodd => by
        obtain ⟨⟨s, hs, -⟩, -⟩ := prime_classical_three_central_odd_extension_splitting hp hp2
          (Or.inl ⟨rfl, hF', rfl⟩) π hπ hC hodd
        exact ⟨s, fun g => DFunLike.congr_fun hs g⟩
    exact Or.inl ⟨true, p, 1, hp, le_rfl, Or.inr ⟨hp2, rfl⟩, F, inferInstance, inferInstance, hF,
      ⟨iso⟩⟩
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
    have := Fintype.ofFinite F
    have : CharP F p := charP_of_card_eq_prime_pow (f := 2) (by
      rw [← Nat.card_eq_fintype_card, hF]
      ring)
    have hsplit : ∀ q : ℕ, q = p → ∀ (E : Type) [Group E] [Finite E] (π : E →* StatedSU 3 q F),
        Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
        ∃ s : StatedSU 3 q F →* E, ∀ g, π (s g) = g := by
      rintro q rfl E _ _ π hπ hC hodd
      obtain ⟨⟨s, hs, -⟩, -⟩ := prime_classical_three_central_odd_extension_splitting hp hp2
        (Or.inr ⟨rfl, by rw [hF, pow_one], rfl⟩) π hπ hC hodd
      exact ⟨s, fun g => DFunLike.congr_fun hs g⟩
    obtain ⟨-, ⟨iso⟩⟩ := triple_cover_unitary (p := p) (f := 1) h3 hF e
      (hsplit (p ^ 1) (pow_one p))
    exact Or.inl ⟨false, p, 1, hp, le_rfl, Or.inr ⟨hp2, rfl⟩, F, inferInstance, inferInstance, hF,
      ⟨iso⟩⟩

end CFSG.QuasithinUnique.Ch1
