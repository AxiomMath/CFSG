module

public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.I43SemidihedralCharTwo
public import CFSG.CharacterTheory.Semidihedral.CentralizerStructure
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.FourPointBranchClassification
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.Adapters.LinearFieldTransport

public section

namespace CFSG.QuasithinUnique

open scoped MatrixGroups

private theorem i43_index_ne_two {A : Type} [Group A] [Finite A] [IsSimpleGroup A]
    (hnonab : ∃ a b : A, a * b ≠ b * a) (U : Subgroup A) : U.index ≠ 2 := by
  intro hindex
  have hU : U.Normal := Subgroup.normal_of_index_eq_two hindex
  rcases hU.eq_bot_or_eq_top with rfl | rfl
  · rw [Subgroup.index_bot] at hindex
    have : Fact (Nat.Prime (Nat.card A)) := ⟨hindex ▸ Nat.prime_two⟩
    have : IsCyclic A := isCyclic_of_prime_card rfl
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (IsCyclic.commGroup.mul_comm a b)
  · rw [Subgroup.index_top] at hindex
    omega

private theorem i43_odd_normal_eq_bot {A : Type} [Group A] [Finite A] [IsSimpleGroup A]
    (k : ℕ) (hk : 4 ≤ k) (S : Sylow 2 A) (f : CFSG.Open.SemidihedralGroup k ≃* S) :
    ∀ K : Subgroup A, K.Normal → Odd (Nat.card K) → K = ⊥ := by
  intro K hK hKodd
  rcases hK.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hz : orderOf (f (CFSG.Semidihedral.z k)) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact CFSG.Semidihedral.orderOf_z k (by omega)
    have h2 : 2 ∣ Nat.card A := by
      rw [← hz, ← Subgroup.orderOf_coe]
      exact orderOf_dvd_natCard _
    rw [h, Subgroup.card_top] at hKodd
    exact (Nat.not_even_iff_odd.mpr hKodd) (even_iff_two_dvd.mpr h2)

theorem i43_semidihedral
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (heven : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G) (P : Sylow 2 G) {n : ℕ}
    (hn : 4 ≤ n) (hP : Nonempty ((P : Subgroup G) ≃* CFSG.Open.SemidihedralGroup n)) :
    Nonempty (G ≃* PSL(3, ZMod 3)) ∨ Nonempty (G ≃* CFSG.Open.M11) := by
  obtain ⟨f⟩ : Nonempty (CFSG.Open.SemidihedralGroup n ≃* P) := ⟨hP.some.symm⟩
  have hA : ∀ V : Subgroup G, V.index ≠ 2 := i43_index_ne_two hnonab
  have hodd := i43_odd_normal_eq_bot n hn P f
  have ht : orderOf (CFSG.Semidihedral.CentralizerResidual.centeredInvolution n P f) = 2 := by
    rw [← CFSG.Semidihedral.CentralizerResidual.centralInvolution_order n hn P f,
      Subgroup.orderOf_mk]
    rfl
  rcases CFSG.Semidihedral.CentralizerStructure.centered_structural_alternatives n hn P f hA with
    hfour | hlayer
  ·
    obtain ⟨-, φ, -⟩ := hfour
    obtain ⟨-, -, -, -, hxor⟩ :=
      CFSG.Semidihedral.GL2Recognition.four_point_reduced_centralizer_branch_classification hA hodd
        n hn P f (CFSG.Semidihedral.CentralizerResidual.centeredInvolution n P f) ht φ
    rcases hxor with ⟨⟨-, hpsl⟩, -⟩ | ⟨⟨-, ⟨e11⟩, -⟩, -⟩
    · obtain ⟨e3⟩ :=
        CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField G 3 3 1 hpsl
      let eF : ZMod 3 ≃+* GaloisField 3 1 :=
        CFSG.ClassicalModels.finiteFieldEquivGaloisField (ZMod 3) 3 1 Nat.one_pos
          (by rw [Nat.card_zmod, pow_one])
      exact Or.inl
        ⟨e3.trans (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin 3)).symm⟩
    · exact Or.inr ⟨e11.trans CFSG.Adapters.RankTwoModelTransports.statedM11EquivM11⟩
  ·
    exfalso
    obtain ⟨hsimple, hLnonab, -, hcentral, -, -, -⟩ := hlayer
    have hz : (P : Subgroup G) ≤
        Subgroup.centralizer ({CFSG.Semidihedral.CentralizerResidual.centeredInvolution n P f} :
          Set G) :=
      CFSG.Semidihedral.CentralizerResidual.sylow_le_involutionCentralizer n hn P f
    have hCharTwo : CharTwo (CFSG.Semidihedral.CentralizerResidual.involutionCentralizer n P f) :=
      charTwo_centralizer_of_isSylowTwoOf heven (isSylowTwoOf_top_of_sylow P) ht hz
    have hchar := EscapingLocal.isCharacteristicP_of_charTwo hCharTwo
    have hN : CFSG.pPrimeCore 2
        (CFSG.Semidihedral.CentralizerResidual.involutionCentralizer n P f) = ⊥ :=
      pPrimeCore_eq_bot_of_charTwo hCharTwo
    have hKz : CFSG.Semidihedral.ReducedQuotients.centralizerFullKernel n P f =
        Subgroup.zpowers (CFSG.Semidihedral.CentralizerResidual.centralInvolution n P f) := by
      change CFSG.pPrimeCore 2
        (CFSG.Semidihedral.CentralizerResidual.involutionCentralizer n P f) ⊔
          Subgroup.zpowers (CFSG.Semidihedral.CentralizerResidual.centralInvolution n P f) = _
      rw [hN, bot_sup_eq]
    let : IsSimpleGroup (CFSG.generalizedFitting
        (CFSG.Semidihedral.CentralizerResidual.involutionCentralizer n P f ⧸
          CFSG.Semidihedral.ReducedQuotients.centralizerFullKernel n P f)) := hsimple
    have hΓ : ∀ Q : Subgroup (CFSG.Semidihedral.CentralizerResidual.involutionCentralizer n P f ⧸
        CFSG.Semidihedral.ReducedQuotients.centralizerFullKernel n P f),
        Q.Normal → IsPGroup 2 Q → Q = ⊥ := by
      intro Q hQ hQp
      have := hQ
      exact eq_bot_of_normal_isPGroup_of_simple_layer hLnonab hcentral Q hQp
    have hle := card_le_two_of_selfCentralizing_normal_two_subgroup
      (CFSG.pCore 2 (CFSG.Semidihedral.CentralizerResidual.involutionCentralizer n P f))
      CFSG.pCore_isPGroup hchar
      (CFSG.Semidihedral.CentralizerResidual.centralInvolution_mem_center n P f)
      (CFSG.Semidihedral.CentralizerResidual.centralInvolution_order n hn P f)
      (CFSG.Semidihedral.ReducedQuotients.centralizerFullKernel n P f) hKz hΓ
    have hcardP : Nat.card (P : Subgroup G) = 2 ^ n := by
      rw [← Nat.card_congr f.toEquiv, CFSG.Semidihedral.card n (by omega)]
    have hPC : Nat.card (P : Subgroup G) ≤
        Nat.card (CFSG.Semidihedral.CentralizerResidual.involutionCentralizer n P f) :=
      Subgroup.card_le_of_le
        (CFSG.Semidihedral.CentralizerResidual.sylow_le_involutionCentralizer n hn P f)
    have h16 : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega

end CFSG.QuasithinUnique
