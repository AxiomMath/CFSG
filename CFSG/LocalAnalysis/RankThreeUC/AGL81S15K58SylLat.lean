module

public import CFSG.Quasithin.Background.GoldschmidtS146RLatSmall
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC3LocU33
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.TightCensus
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.AutFactsU33

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K58Proof

open Subgroup CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

structure SylLatAt {Y : Type} [Group Y] (S A B : Subgroup Y) (n : ℕ) : Prop where
  le_A : S ≤ A
  le_B : S ≤ B
  lattice : ∀ H : Subgroup Y, S ≤ H → H = S ∨ H = A ∨ H = B ∨ H = ⊤
  index_A : A.index = n
  index_B : B.index = n
  lt_index : n < S.index
  one_lt : 1 < n
  normalizer_eq : normalizer (S : Set Y) = S
  normalizer_A : normalizer (A : Set Y) = A
  normalizer_B : normalizer (B : Set Y) = B

@[expose] def SylLat (Y : Type) [Group Y] (n : ℕ) : Prop :=
  ∀ S : Subgroup Y, IsSylowTwoOf S ⊤ → ∃ A B : Subgroup Y, SylLatAt S A B n

section Transport

variable {Y Y' : Type} [Group Y] [Group Y']

theorem SylLatAt.map (e : Y ≃* Y') {S A B : Subgroup Y} {n : ℕ} (h : SylLatAt S A B n) :
    SylLatAt (S.map e.toMonoidHom) (A.map e.toMonoidHom) (B.map e.toMonoidHom) n where
  le_A := map_mono h.le_A
  le_B := map_mono h.le_B
  lattice H hSH := by
    have hH : (H.comap e.toMonoidHom).map e.toMonoidHom = H :=
      map_comap_eq_self_of_surjective e.surjective H
    rcases h.lattice _ (map_le_iff_le_comap.mp hSH) with h1 | h1 | h1 | h1 <;>
      rw [← hH, h1]
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (map_top_of_surjective _ e.surjective)))
  index_A := by rw [index_map_of_bijective e.bijective]; exact h.index_A
  index_B := by rw [index_map_of_bijective e.bijective]; exact h.index_B
  lt_index := by rw [index_map_of_bijective e.bijective]; exact h.lt_index
  one_lt := h.one_lt
  normalizer_eq := by rw [← map_equiv_normalizer_eq, h.normalizer_eq]
  normalizer_A := by rw [← map_equiv_normalizer_eq, h.normalizer_A]
  normalizer_B := by rw [← map_equiv_normalizer_eq, h.normalizer_B]

theorem SylLat.of_sylLatAt [Finite Y] {S₀ A B : Subgroup Y} {n : ℕ} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (h : SylLatAt S₀ A B n) : SylLat Y n := by
  intro S hS
  obtain ⟨g, hg⟩ := CFSG.Quasithin.GoldS146R.exists_conj_of_isSylowTwoOf_top hS₀ hS
  refine ⟨A.map (MulAut.conj g).toMonoidHom, B.map (MulAut.conj g).toMonoidHom, ?_⟩
  rw [hg]
  exact h.map (MulAut.conj g)

theorem SylLat.of_mulEquiv (e : Y ≃* Y') {n : ℕ} (h : SylLat Y' n) : SylLat Y n := by
  intro S hS
  obtain ⟨A, B, hAB⟩ := h _ (CFSG.Quasithin.GoldS146R.isSylowTwoOf_top_map_equiv e hS)
  refine ⟨A.map e.symm.toMonoidHom, B.map e.symm.toMonoidHom, ?_⟩
  have h1 := hAB.map e.symm
  have h2 : (S.map e.toMonoidHom).map e.symm.toMonoidHom = S := by
    rw [map_map]
    have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id Y := by
      ext x
      simp
    rw [this, map_id]
  rwa [h2] at h1

end Transport

section MinOver

variable {Y : Type} [Group Y] {S A B : Subgroup Y} {n : ℕ}

theorem SylLatAt.eq_of_le_index (h : SylLatAt S A B n) {Q P : Subgroup Y} (hQP : Q ≤ P)
    (hQ : Q.index = n) (hP : P.index = n) : Q = P := by
  have h1 := relIndex_mul_index hQP
  rw [hQ, hP] at h1
  have hn : 0 < n := by have := h.one_lt; omega
  have h2 : Q.relIndex P = 1 := Nat.eq_of_mul_eq_mul_right hn (by rw [h1, one_mul])
  exact le_antisymm hQP (relIndex_eq_one.1 h2)

theorem SylLatAt.isMinOverBorel_left (h : SylLatAt S A B n) : IsMinOverBorel ⊤ S A := by
  have hN : (⊤ : Subgroup Y) ⊓ normalizer (S : Set Y) = S := by rw [top_inf_eq, h.normalizer_eq]
  refine ⟨le_top, ?_, fun Q hSQ hQA => ?_⟩
  · rw [hN]
    refine lt_of_le_of_ne h.le_A fun hSA => ?_
    have := h.lt_index
    rw [hSA, h.index_A] at this
    omega
  · rw [hN] at hSQ ⊢
    rcases h.lattice Q hSQ with hQ | hQ | hQ | hQ
    · exact Or.inl hQ
    · exact Or.inr hQ
    · rw [hQ] at hQA ⊢
      exact Or.inr (h.eq_of_le_index hQA h.index_B h.index_A)
    · exfalso
      rw [hQ, top_le_iff] at hQA
      have h1 := h.index_A
      rw [hQA, index_top] at h1
      have := h.one_lt
      omega

theorem SylLatAt.swap (h : SylLatAt S A B n) : SylLatAt S B A n where
  le_A := h.le_B
  le_B := h.le_A
  lattice H hSH := by
    rcases h.lattice H hSH with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inr h1))
  index_A := h.index_B
  index_B := h.index_A
  lt_index := h.lt_index
  one_lt := h.one_lt
  normalizer_eq := h.normalizer_eq
  normalizer_A := h.normalizer_B
  normalizer_B := h.normalizer_A

theorem SylLatAt.isMinOverBorel_right (h : SylLatAt S A B n) : IsMinOverBorel ⊤ S B :=
  h.swap.isMinOverBorel_left

end MinOver

section U33

open CFSG.Quasithin CFSG.Quasithin.H13.U3
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
  (nonempty_mulEquiv_u33G_of_statedClassicalModel)


theorem sylLatAt_u33G : SylLatAt u33Data.T u33Data.A u33Data.B 63 where
  le_A := u33Data.T_le_A
  le_B := u33Data.T_le_B
  lattice := u33Data.lattice
  index_A := index_u33_A
  index_B := index_u33_B
  lt_index := by rw [index_u33_T]; norm_num
  one_lt := by norm_num
  normalizer_eq := CFSG.Quasithin.GoldC3.u33_normalizer_T
  normalizer_A := normalizer_u33_A
  normalizer_B := normalizer_u33_B

theorem sylLat_u33G : SylLat U33G 63 :=
  SylLat.of_sylLatAt CFSG.Quasithin.GoldS146R.isSylowTwoOf_u33_T sylLatAt_u33G

theorem sylLat_of_isUThreeThree {Y : Type} [Group Y] (h : IsUThreeThree Y) : SylLat Y 63 := by
  obtain ⟨d, ⟨q, hq3, hqd⟩, ⟨e⟩⟩ := h
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hqd
  subst hqd
  have hm0 := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  obtain ⟨hp3, he1⟩ : q.p = 3 ∧ q.exponent = 1 :=
    (Nat.Prime.pow_eq_iff Nat.prime_three).mp (by rw [← TauCeti.PrimePower.card_def]; exact hq3)
  rw [hp3, he1] at hm0
  have hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSU 3 3 1 := hm0
  obtain ⟨eU⟩ := nonempty_mulEquiv_u33G_of_statedClassicalModel hm
  exact SylLat.of_mulEquiv eU sylLat_u33G

end U33

end CFSG.LocalAnalysis.RankThreeUC.S15.K58Proof
