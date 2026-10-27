module

public import CFSG.Quasithin.H13.A5S136p
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S135
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL3

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.Quasithin.E3
open CFSG.Blueprint CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Setting

variable {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem exists_ident_F4
    (h1336 : Input1336_F4)
    (hC : S.Concl136) (h523 : Stmt5_2_3_F4)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h312 : A312ForSQTK) (h128 : Lemma128Four) :
    ∃ K ∈ cComp S.G1, S.G1 ≤ Subgroup.normalizer (K : Set G) ∧
      (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* NativeSporadic.J2) ∨
        Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* NativeSporadic.M23) ∨
        IsPSL 3 2 2 (↥K ⧸ CFSG.pCore 2 ↥K) ∨ Is3D4 2 1 (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hM
  have := S.h13.simple
  have hloc : LocalSQTK G := (QuasithinUnique.qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  have hG1 := S.G1_mem_Hz_F4 h1336
  have hTG1 : T ≤ S.G1 := le_sup_right.trans hG1.1.1
  have hG1O : pCoreOf 2 S.G1 ≠ ⊥ := hG1.1.2
  have hTsyl1 : IsSylowTwoOf T S.G1 := isSylowTwoOf_of_le S.h13.sylow hTG1

  obtain ⟨H₁, hH₁, -⟩ := exists_isHStar_le' (M := M) ⟨hTG1, hG1O⟩ hG1.2.2
  have hn := hC.hn H₁ hH₁.1 hH₁.2.1

  have hV := S.isCh5Module
  obtain ⟨KZ, hKZ, hK₁KZ, hqZ, hcase⟩ : CentralizerComponentClause T H₁ := by
    rcases h523 G T M L H₁ V 2 S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow
        S.uniqueM.1.1 S.T_le_NL S.maximal S.h13.faithful Subgroup.le_normalizer le_rfl le_rfl
        S.lieModel_L hH₁ hn hV.1 hV.2.1 hV.2.2 with ⟨-, -, hcc⟩ | hM23 | hLie
    · exact hcc
    · exact (S.h13.not_excluded (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM23)))))).elim
    · exfalso
      apply S.h13.not_excluded
      rcases hLie with ⟨t, n, f, hf, -, hadm, hlie⟩ | hlie
      · exact Or.inl ⟨t, n, f, hf, hadm, hlie⟩
      · refine Or.inl ⟨.PSU, 5, 2, le_rfl, ?_, hlie⟩
        refine ⟨Nat.prime_two, by norm_num, ?_⟩
        exact ⟨by norm_num, by decide⟩
  set CZ := Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) with hCZ
  set K₁ := oTwoUpper H₁ with hK₁
  have hTH₁ : T ≤ H₁ := hH₁.1.1
  have hTsyl : IsSylowTwoOf T H₁ := isSylowTwoOf_of_le S.h13.sylow hTH₁
  have hH₁eq : H₁ = K₁ ⊔ T := eq_oTwoUpper_sup_of_isSylowTwoOf' hTsyl
  have hTK₁ : T ≤ Subgroup.normalizer (K₁ : Set G) := hTH₁.trans (le_normalizer_oTwoUpper H₁)
  have hK₁M : ¬ K₁ ≤ M := fun h => hH₁.2.1 (by rw [hH₁eq]; exact sup_le h S.T_le_NL)

  have hq₁ : CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := by
    rcases hcase with ⟨⟨e5⟩, -⟩ | ⟨heq, -⟩ | ⟨h28, -⟩
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e5.symm isQuasisimple_alt5
    · have heq' : K₁ = KZ := heq
      rw [heq']
      exact hqZ
    ·
      have : IsSimpleGroup (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := isSimpleGroup_of_lieModel_PSL2 h28
      have hc : Nat.card (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) = 504 := by
        rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h28]
        decide +kernel
      exact isQuasisimple_of_simple_not_prime136 (by rw [hc]; norm_num)
  have hK₁c : K₁ ∈ cComp H₁ :=
    mem_cComp_of_quasisimple_quotient (oTwoUpper_eq_top_of_isPGroup H₁) hq₁
      (A3.subnormal_of_normal (oTwoUpper_le H₁)
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le H₁)).2
          (le_normalizer_oTwoUpper H₁)))
  have hK₁l : K₁ ∈ lFamily T := cComp_subset_lFamily hTH₁ hK₁c

  have hZT : quasithinOmegaOneCenter T ≤ T := fun x hx =>
    (mem_quasithinOmegaOneCenter_iff.mp hx).1
  have hZCZ : quasithinOmegaOneCenter T ≤ CZ := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.mp hy).2.1 x
      (hZT hx)).symm
  have hCZO : pCoreOf 2 CZ ≠ ⊥ := by
    intro h
    have hle : quasithinOmegaOneCenter T ≤ pCoreOf 2 CZ :=
      le_pCoreOf_of_le_normalizer 2 hZCZ (fun x hx => Subgroup.centralizer_le_normalizer _ hx)
        (S.isPGroup_T.to_le hZT)
    rw [h, le_bot_iff] at hle
    have hz := S.z_mem_omegaOneCenter
    rw [hle, Subgroup.mem_bot] at hz
    exact S.z_ne_one hz

  have hTCZ : T ≤ CZ := T_le_centralizer_omegaOneCenter T
  have hTKZ : T ≤ Subgroup.normalizer (KZ : Set G) := by
    intro t ht
    have hKs : KZ.map (MulAut.conj t).toMonoidHom ∈ cComp CZ :=
      CFSG.Quasithin.map_conj_mem_cComp hKZ (hTCZ ht)
    have hK₁s : K₁ ≤ KZ.map (MulAut.conj t).toMonoidHom := by
      have hK₁t : K₁.map (MulAut.conj t).toMonoidHom = K₁ := A38.map_conj_eq_iff.mpr (hTK₁ ht)
      rw [← hK₁t]
      exact Subgroup.map_mono hK₁KZ
    exact A38.map_conj_eq_iff.mp
      (Vol2Native.lemma_1_2_4_unique hloc h37 hCZO hK₁l hKZ hKs hK₁KZ hK₁s).symm

  have hCZG1 : CZ ≤ S.G1 :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr S.z_mem_omegaOneCenter)
  have hKZG : KZ ≤ S.G1 := (le_of_mem_cComp hKZ).trans hCZG1
  have hKZl : KZ ∈ lFamily T := cComp_subset_lFamily hTCZ hKZ
  obtain ⟨K, hK, hKZK⟩ := Vol2Native.lemma_1_2_4_exists hloc h37 h39 hG1O hTsyl1 hKZG hKZl
  have hKG : K ≤ S.G1 := le_of_mem_cComp hK
  have hKn : S.G1 ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKG).mp
      (Vol2Native.lemma_1_2_4_normal hloc h37 h38 hG1O hTsyl1 hKZl hKZK hK hTKZ)
  refine ⟨K, hK, hKn, ?_⟩

  have hlocal : ∀ X : Subgroup G, X ∈ lFamily T → X ≤ S.G1 → quasithinIsLocal T X :=
    fun X hX hXG => ⟨S.isPGroup_T, hX, (isSylowTwoOf_of_le S.h13.sylow le_sup_right).2.2,
      S.pCoreOf_ne_bot_of_le_G1 le_sup_right (sup_le hXG hTG1)⟩
  have hKl : K ∈ lFamily T := cComp_subset_lFamily hTG1 hK
  have hKeq : A128FourList (ModO2 KZ) → K = KZ := fun hlist =>
    (h128 G S.h13.qtke S.h13.simple S.h13.nonabelian T KZ (hlocal KZ hKZl hKZG) hlist).2 K
      (hlocal K hKl hKG) hKZK
  rcases hcase with ⟨-, hA7 | hJ2 | hM23⟩ | ⟨heq, hL34⟩ | ⟨-, h3D4⟩
  ·
    exfalso
    have hXT : InH T (KZ ⊔ T) :=
      ⟨le_sup_right, S.pCoreOf_ne_bot_of_le_G1 le_sup_right (sup_le hKZG hTG1)⟩
    have hnZ := hC.hn (KZ ⊔ T) hXT (fun h => hK₁M (hK₁KZ.trans (le_sup_left.trans h)))
    have hKZc : KZ ∈ cComp (KZ ⊔ T) := hKZl
    have hle : E1.nParam (KZ ⊔ T) ≤ 1 :=
      A7NP.nParam_le_one_of_alt7_noE (isSylowTwoOf_of_le S.h13.sylow le_sup_right) hKZc rfl
        hTKZ hA7
    exact absurd hnZ (not_lt_of_ge hle)
  ·
    have hlist : A128FourList (ModO2 KZ) :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hJ2)))))))
    rw [hKeq hlist]
    exact Or.inl hJ2
  ·
    have hlist : A128FourList (ModO2 KZ) :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM23)))))
    rw [hKeq hlist]
    exact Or.inr (Or.inl hM23)
  ·
    have hpsl : IsPSL 3 2 2 (ModO2 KZ) := by
      rcases hL34 with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact h
      all_goals exact absurd h0 (by norm_num)
    obtain ⟨e⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv (H := S.G1) hKZG
    have hD : ModL34 (modO2Image S.G1 KZ) := ⟨isPSL_of_mulEquiv e.symm hpsl⟩
    rcases lemma_1_2_4_list S.h13.qtke S.h13.simple S.h13.nonabelian h312 hG1O hTsyl1 hKZG hKZl
        hK hKZK with heqI | hcaseI | hnq
    · right
      right
      have hDK : ModL34 (modO2Image S.G1 K) := heqI ▸ hD
      obtain ⟨eK⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv (H := S.G1) hKG
      exact Or.inl (isPSL_of_mulEquiv eK hDK.psl)
    · right
      left
      obtain ⟨eM⟩ := hD.isSporadic_M23_of_a312Case hcaseI
      obtain ⟨eK⟩ := modO2_mulEquiv hK
      exact ⟨eK.trans eM⟩
    · exfalso
      have hperf : Group.IsPerfect ↥(modO2Image S.G1 KZ) := by
        refine Subgroup.isPerfect_iff.mpr ?_
        have hA : ⁅KZ.subgroupOf S.G1, KZ.subgroupOf S.G1⁆ = KZ.subgroupOf S.G1 := by
          apply Subgroup.map_injective S.G1.subtype_injective
          rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKZG, hKZ.2.1]
        unfold modO2Image
        rw [← Subgroup.map_commutator, hA]
      exact hD.false_of_a312Nonquasi (Subgroup.map_mono fun x hx => hKZK hx) hperf hnq
  ·
    have hc := card_of_is3D4_two h3D4
    have hR : IsRank2LieChar2 (ModO2 KZ) :=
      Or.inl ⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨le_rfl, h3D4⟩))))⟩
    have h321 : ¬ IsPSL 3 2 1 (ModO2 KZ) := fun h => by
      have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
      rw [hc] at h1
      exact absurd h1 (by decide +kernel)
    have h322 : ¬ IsPSL 3 2 2 (ModO2 KZ) := fun h => by
      have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
      rw [hc] at h1
      exact absurd h1 (by decide +kernel)
    have hlist : A128FourList (ModO2 KZ) := by
      unfold A128FourList
      iterate 14 right
      exact ⟨hR, h321, h322⟩
    rw [hKeq hlist]
    exact Or.inr (Or.inr (Or.inr h3D4))

end Setting

end CFSG.Quasithin.H13.A5
