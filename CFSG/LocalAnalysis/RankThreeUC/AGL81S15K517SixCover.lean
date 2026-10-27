module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517SixComm

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K517Six

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding.ParabHub
  CFSG.QuasithinUnique

section Cover

variable {W : Type} [Group W] [Finite W] {L : Subgroup W} {K : Type} [Group K] [Finite K]
  {D : UniversalRootDatum K}

@[expose] def NodeIn (L A : Subgroup W) (π : K →* ↥L ⧸ Subgroup.center ↥L) (i : Fin D.rank) :
    Prop :=
  (rankOne D.rootGroup i).map π ≤ (A.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))

@[expose] def BadPairMat {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r) : Prop :=
  i ≠ j ∧ (A i j = 0 ∨ A i j * A j i = 2)

instance {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r) : Decidable (BadPairMat A i j) := by
  unfold BadPairMat
  infer_instance

@[expose] def BadPair (D : UniversalRootDatum K) (i j : Fin D.rank) : Prop :=
  BadPairMat D.cartan i j

theorem two_le_pRank_of_subgroupOf {A : Subgroup W} (hA : A ≤ L)
    (h : 2 ≤ CFSG.Open.pRank 3 (A.subgroupOf L)) : 2 ≤ CFSG.Open.pRank 3 A := by
  have h1 := CFSG.SectionRank.pRank_le_map (by norm_num : 1 < 3) L.subtype L.subtype_injective
    (A.subgroupOf L)
  rw [Subgroup.map_subgroupOf_eq_of_le hA] at h1
  exact h.trans h1

variable {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ}
  {π : K →* ↥L ⧸ Subgroup.center ↥L}

theorem two_le_pRank_of_badPair (hbq : BorelQuotient D n H π M) (hdiv : D.divisible = ∅)
    (hodd : ∀ i, OddNode (rankOne D.rootGroup i) 3) {A : Subgroup W} (hA : A ≤ L) {i j : Fin D.rank}
    (hb : BadPair D i j) (hi : NodeIn L A π i) (hj : NodeIn L A π j) :
    2 ≤ CFSG.Open.pRank 3 A := by
  have hq : (QuotientGroup.mk' (Subgroup.center ↥L)).ker ≤ Subgroup.center ↥L := by
    rw [QuotientGroup.ker_mk']
  have hπ := hbq.ker_central
  refine two_le_pRank_of_subgroupOf hA ?_
  obtain ⟨hij, h0 | h2⟩ := (hb : BadPairMat D.cartan i j)
  · exact two_le_pRank_of_orthogonal_nodes hq hπ hi hj (hodd i) (hodd j)
      (rankOne_commute_of_cartan_zero hbq.extras hij h0)
  · rcases cartan_pair_cases D.isFiniteType hij with ⟨h1, h2'⟩ | ⟨h1, h2'⟩ | ⟨h1, h2'⟩ | ⟨h1, h2'⟩ |
      ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · rw [h1, h2'] at h2
      norm_num at h2
    · rw [h1, h2'] at h2
      norm_num at h2
    · exact two_le_pRank_of_conj_nodes hq hπ (g := n j) hi
        (hj ⟨n j, hbq.ct.n_mem j, rfl⟩) (hodd i)
        (rankOne_conj_commute_of_cartan_B2 hbq.ct hbq.extras hdiv hij h1 h2')
    · exact two_le_pRank_of_conj_nodes hq hπ (g := n i) hj
        (hi ⟨n i, hbq.ct.n_mem i, rfl⟩) (hodd j)
        (rankOne_conj_commute_of_cartan_B2 hbq.ct hbq.extras hdiv hij.symm h2' h1)
    · rw [h1, h2'] at h2
      norm_num at h2
    · rw [h1, h2'] at h2
      norm_num at h2

theorem cover_classes {S₀ A₁ A₂ : Subgroup W} (hS : IsSylowTwoOf S₀ L)
    (hcov : CoveredByTwo L S₀ A₁ A₂) (hbq : BorelQuotient D n H π M) :
    ∃ π' : K →* ↥L ⧸ Subgroup.center ↥L, BorelQuotient D n H π' M ∧
      ∀ i, NodeIn (D := D) L A₁ π' i ∨ NodeIn (D := D) L A₂ π' i := by
  obtain ⟨π', hπ', hT⟩ := exists_borelQuotient_conj hS hbq
  exact ⟨π', hπ', fun i =>
    CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.cover_of_borelQuotient hS hcov hπ' hT i⟩

end Cover

section Combinatorics

@[expose] def NoCliqueCover (r : ℕ) (bad : Fin r → Fin r → Prop) : Prop :=
  ∀ J₀ J₁ : Fin r → Bool, (∀ i, J₀ i = true ∨ J₁ i = true) →
    (∀ i j, J₀ i = true → J₀ j = true → ¬ bad i j) →
    (∀ i j, J₁ i = true → J₁ j = true → ¬ bad i j) → False

theorem false_of_noCliqueCover {r : ℕ} {bad : Fin r → Fin r → Prop} (h : NoCliqueCover r bad)
    {c₀ c₁ : Fin r → Prop} (hcov : ∀ i, c₀ i ∨ c₁ i) (h₀ : ∀ i j, c₀ i → c₀ j → ¬ bad i j)
    (h₁ : ∀ i j, c₁ i → c₁ j → ¬ bad i j) : False := by
  classical
  refine h (fun i => decide (c₀ i)) (fun i => decide (c₁ i)) (fun i => ?_) (fun i j hi hj => ?_)
    (fun i j hi hj => ?_)
  · simpa using hcov i
  · exact h₀ i j (by simpa using hi) (by simpa using hj)
  · exact h₁ i j (by simpa using hi) (by simpa using hj)

theorem noCliqueCover_of_triple {r : ℕ} {bad : Fin r → Fin r → Prop} {a b c : Fin r}
    (hab : bad a b) (hac : bad a c) (hbc : bad b c) : NoCliqueCover r bad := by
  intro J₀ J₁ hcov h₀ h₁
  rcases hcov a with ha | ha <;> rcases hcov b with hb | hb <;> rcases hcov c with hc | hc
  · exact h₀ a b ha hb hab
  · exact h₀ a b ha hb hab
  · exact h₀ a c ha hc hac
  · exact h₁ b c hb hc hbc
  · exact h₀ b c hb hc hbc
  · exact h₁ a c ha hc hac
  · exact h₁ a b ha hb hab
  · exact h₁ a b ha hb hab

end Combinatorics

section False

variable {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W} {K : Type} [Group K] [Finite K]
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ}
  {π : K →* ↥L ⧸ Subgroup.center ↥L}

theorem false_of_cover (hS : IsSylowTwoOf S₀ L) (hcov : CoveredByTwo L S₀ A₁ A₂)
    (hbq : BorelQuotient D n H π M) (hdiv : D.divisible = ∅)
    (hodd : ∀ i, OddNode (rankOne D.rootGroup i) 3) (hA₁ : A₁ ≤ L) (hA₂ : A₂ ≤ L)
    (h₁ : CFSG.Open.pRank 3 A₁ ≤ 1) (h₂ : CFSG.Open.pRank 3 A₂ ≤ 1)
    (hno : NoCliqueCover D.rank (BadPair D)) : False := by
  obtain ⟨π', hπ', hcl⟩ := cover_classes hS hcov hbq
  refine false_of_noCliqueCover hno (c₀ := fun i => NodeIn (D := D) L A₁ π' i)
    (c₁ := fun i => NodeIn (D := D) L A₂ π' i) hcl (fun i j hi hj hb => ?_) (fun i j hi hj hb => ?_)
  · have := two_le_pRank_of_badPair hπ' hdiv hodd hA₁ hb hi hj
    omega
  · have := two_le_pRank_of_badPair hπ' hdiv hodd hA₂ hb hi hj
    omega

end False


end CFSG.LocalAnalysis.RankThreeUC.S15.K517Six
