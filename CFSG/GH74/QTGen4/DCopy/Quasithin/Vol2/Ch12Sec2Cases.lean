module

public import CFSG.Quasithin.Vol2.Ch12Sec2Cases
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

section Cases

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem false_of_concl328_one_F4
    (h6220 : Stmt6_2_20_F4) (hNat : NaturalSL24NotA5Sum)
    (hH : Hyp1223 G T L V) [IsMulCommutative ↥V] (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)))
    (hM : quasithinIsMaxTwoLocal (Subgroup.normalizer (L : Set G)))
    (h : ∃ n : ℕ, LieModel ↥(autOn L V) .PSL 2 2 n ∧
      BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ((Subgroup.centralizer (L : Set G)).subgroupOf V)
        2 n) :
    False := by
  obtain ⟨n, hLie, hnat⟩ := h
  have hLV := le_normalizer_of_hyp1223 hH
  have hc := commutator_eq_of_hyp1223 hH
  have hO2 := pCoreOf_le_centralizer_of_hyp1223 hH hred
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ :=
    LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hLie
  obtain ⟨-, hn1, -, hne, -⟩ := hadm
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn : n = 1 := by omega
    subst hn
    exact hne (by norm_num)
  have : CharP K 2 := CFSG.SectionRank.charP_two_of_card hK
  have e' : ↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    e.trans (QuasithinUnique.Setup.Family.statedProjSL_two_equiv K)
  obtain ⟨eQ⟩ := nonempty_quot_mulEquiv_sl_of_autOn hLV hO2 hH.quasisimple (n := 2) le_rfl e'
  have hLieQ : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (eQ.trans e'.symm).symm hLie
  rcases h6220 G T (Subgroup.normalizer (L : Set G)) L V n hH.simple hH.nonabelian hH.qtke
      hH.sylow hM hH.normalizes hH.maximal hH.faithful Subgroup.le_normalizer le_rfl hn2 hLieQ
      (le_sup_of_hyp1223 hH) hred (by rw [hc]; exact hH.irrPlus.2.1) with
    ⟨rfl, hA5, -⟩ | hLie2 | hM22 | hM23
  · rw [hc] at hA5
    exact hNat G L V hLV hnat (irreducible_of_hyp1223 hH) hA5
  · exact hH.notAlt (alt12_2_2_of_alt12_2_2Lie hLie2)
  · exact hH.notAlt (Or.inr (Or.inr (Or.inl hM22)))
  · exact hH.notAlt (Or.inr (Or.inr (Or.inr (Or.inl hM23))))

theorem modules_of_concl328_two_a_F4
    (h1101 : Stmt11_0_1_F4) (hH : Hyp1223 G T L V)
    [IsMulCommutative ↥V] (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)))
    (h : ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin 3) K) ∧
      BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ 3 n) :
    Modules12_2_2 L V := by
  obtain ⟨n, K, _, _, hK, ⟨e⟩, hnat⟩ := h
  have hLV := le_normalizer_of_hyp1223 hH
  have hO2 := pCoreOf_le_centralizer_of_hyp1223 hH hred
  have : CharP K 2 := CFSG.SectionRank.charP_two_of_card hK
  obtain ⟨eQ⟩ := nonempty_quot_mulEquiv_sl_of_autOn hLV hO2 hH.quasisimple (n := 3) (by norm_num) e
  have hn1 := one_le_of_card_eq_two_pow hK
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · exact absurd ⟨n, h1, Or.inl ⟨K, inferInstance, inferInstance, hK, ⟨eQ⟩⟩⟩
      (h1101 G T L hH.simple hH.nonabelian hH.qtke hH.sylow hH.maximal hH.faithful)
  · have hn : n = 1 := by omega
    subst hn
    rw [pow_one] at hK
    exact Or.inl ⟨3, Or.inl rfl, ⟨eQ.trans (slCongr (ringEquivZModTwo hK))⟩, hnat⟩

theorem false_of_concl328_three_F4
    (h1101 : Stmt11_0_1_F4) (hH : Hyp1223 G T L V)
    [IsMulCommutative ↥V] (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)))
    (h : ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥(autOn L V) ≃* ↥(Assembly.LowTwoRank.StatedSp 2 K)) ∧
      BinaryNaturalSp4 (V := ↥V) (autOn L V) ⊤
        ((Subgroup.centralizer (L : Set G)).subgroupOf V) n) :
    False := by
  obtain ⟨n, K, _, _, hK, ⟨e⟩, -⟩ := h
  have hLV := le_normalizer_of_hyp1223 hH
  have hO2 := pCoreOf_le_centralizer_of_hyp1223 hH hred
  have hnc := not_le_centralizer_of_hyp1223 hH
  have hqV := isQuasisimple_autOn_of_pCoreOf_le hLV hH.quasisimple hO2 hnc
  have hn1 := one_le_of_card_eq_two_pow hK
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · have : CharP K 2 := CFSG.SectionRank.charP_two_of_card hK
    obtain ⟨-, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hH.quasisimple
    set φ := e.toMonoidHom.comp (autOnQuot hLV hO2) with hφ
    have hφs : Function.Surjective φ := e.surjective.comp (autOnQuot_surjective hLV hO2)
    obtain ⟨a, ha⟩ := exists_ne_one_autOn hLV hnc
    have hinj := injective_of_quasisimple_of_split hH.quasisimple hodd φ hφs
      ⟨e a, fun h => ha (e.injective (h.trans (map_one e).symm))⟩ fun hcen hoddk => by
        obtain ⟨σ, -, -, e₂, -⟩ :=
          CFSG.SectionRank.EvenCover.even_symplectic_central_odd_extension_splitting 2 hφs hcen
            hoddk
        exact ⟨σ.range, ⟨e₂⟩⟩
    exact h1101 G T L hH.simple hH.nonabelian hH.qtke hH.sylow hH.maximal hH.faithful
      ⟨n, h1, Or.inr (Or.inr (Or.inl (lieModel_psp_of_mulEquiv_statedSp h1 hK
        (MulEquiv.ofBijective φ ⟨hinj, hφs⟩))))⟩
  · have hn : n = 1 := by omega
    subst hn
    rw [pow_one] at hK
    have : Group.IsPerfect ↥(autOn L V) := hqV.1
    exact not_isPerfect_statedSp_of_card_two hK
      (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)

theorem modules_of_concl328_four_F4 (h1101 : Stmt11_0_1_F4) (hG2 : G2ZornQuotientModel)
    (hH : Hyp1223 G T L V) [IsMulCommutative ↥V] (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)))
    (h : ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥(autOn L V) ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆) ∧
      G2NaturalDerived (V := ↥V) (autOn L V) ⊤
        ((Subgroup.centralizer (L : Set G)).subgroupOf V) n) :
    Modules12_2_2 L V := by
  obtain ⟨n, K, _, _, hK, ⟨e⟩, hnat⟩ := h
  have hLV := le_normalizer_of_hyp1223 hH
  have hO2 := pCoreOf_le_centralizer_of_hyp1223 hH hred
  have hn1 := one_le_of_card_eq_two_pow hK
  obtain ⟨-, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hH.quasisimple
  obtain ⟨hU, hG⟩ := hG2 _ hH.quasisimple hodd K n hK hn1 (e.toMonoidHom.comp (autOnQuot hLV hO2))
    (e.surjective.comp (autOnQuot_surjective hLV hO2))
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · exact absurd ⟨n, h1, Or.inr (Or.inr (Or.inr (hG h1)))⟩
      (h1101 G T L hH.simple hH.nonabelian hH.qtke hH.sylow hH.maximal hH.faithful)
  · have hn : n = 1 := by omega
    subst hn
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hU rfl, hnat⟩)))))

theorem false_of_concl701_orth_F4
    (h6220 : Stmt6_2_20_F4) (hH : Hyp1223 G T L V) [IsMulCommutative ↥V]
    (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)))
    (hM : quasithinIsMaxTwoLocal (Subgroup.normalizer (L : Set G))) {n : ℕ} (hn : 1 < n)
    (h : BinaryOrthogonalFour (V := ↥V) (autOn L V) ⊤ ⊥ n) : False := by
  obtain ⟨K, _, _, _, hK, π, hπ, -⟩ := h
  have hLV := le_normalizer_of_hyp1223 hH
  have hO2 := pCoreOf_le_centralizer_of_hyp1223 hH hred
  have hnc := not_le_centralizer_of_hyp1223 hH
  have : Fintype K := Fintype.ofFinite K
  have hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    QuasithinUnique.AppE.sl2_isSimpleGroup (n := 2 * n) (by omega)
      (by rw [← Nat.card_eq_fintype_card, hK])
  have hsimple' : IsSimpleGroup ↥(Assembly.LowTwoRank.StatedSL 2 K) :=
    (specialLinearGroupEquivStatedSL 2 K).symm.isSimpleGroup
  have : IsSimpleGroup (FFModel.twistTensor n (Assembly.LowTwoRank.StatedSL 2 K)).Gam := hsimple'
  obtain ⟨eA⟩ := nonempty_mulEquiv_of_surjective_of_isSimpleGroup (exists_ne_one_autOn hLV hnc) π hπ
  obtain ⟨eQ⟩ := nonempty_quot_mulEquiv_sl_of_autOn hLV hO2 hH.quasisimple (n := 2) le_rfl
    (eA.trans (specialLinearGroupEquivStatedSL 2 K).symm)
  set eS := eQ.trans (specialLinearGroupEquivStatedSL 2 K)
  have : Nontrivial (↥L ⧸ CFSG.pCore 2 ↥L) := eS.toEquiv.nontrivial
  have hLieQ : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 (2 * n) :=
    lieModel_psl_two_of_mulEquiv hH.quasisimple.1 hK eS
  rcases h6220 G T (Subgroup.normalizer (L : Set G)) L V (2 * n) hH.simple hH.nonabelian hH.qtke
      hH.sylow hM hH.normalizes hH.maximal hH.faithful Subgroup.le_normalizer le_rfl (by omega)
      hLieQ (le_sup_of_hyp1223 hH) hred
      (by rw [commutator_eq_of_hyp1223 hH]; exact hH.irrPlus.2.1) with
    ⟨h2, -⟩ | hLie2 | hM22 | hM23
  · omega
  · exact hH.notAlt (alt12_2_2_of_alt12_2_2Lie hLie2)
  · exact hH.notAlt (Or.inr (Or.inr (Or.inl hM22)))
  · exact hH.notAlt (Or.inr (Or.inr (Or.inr (Or.inl hM23))))

end Cases

end CFSG.Quasithin.H13
