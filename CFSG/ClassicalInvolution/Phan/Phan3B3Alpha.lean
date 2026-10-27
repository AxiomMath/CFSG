module

public import CFSG.ClassicalInvolution.Phan.Phan3B3Twist
public import CFSG.ClassicalInvolution.Phan.Phan3B3SpRel
public import CFSG.ClassicalInvolution.Phan.PhanB10Family
public import CFSG.ClassicalInvolution.Phan.Phan3ASound

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock)
open CFSG.ClassicalInvolution.Asc77.B3C (twShort SymplecticPhanPair)
open CFSG.ClassicalInvolution.PhanB3 (PhanFamilyB3)
open CFSG.LieType.Multipliers.U43 (F9)

@[expose] noncomputable def su2Elt (k : Fin 24) : Su K9 3 1 2 :=
  wordVal gen2 (su2Words.getD k.val [])

theorem su2Elt_injective : Function.Injective su2Elt := fun k k' h =>
  su2Words_inj k k' (wordMat_eq_of_wordVal_eq gen2 mat2 hg2 hU2 h)

theorem su2Elt_surjective : Function.Surjective su2Elt := by
  have : Finite (Su K9 3 1 2) := Nat.finite_of_card_ne_zero (by rw [card_su2]; norm_num)
  exact (su2Elt_injective.bijective_of_nat_card_le (by
    rw [card_su2, Nat.card_eq_fintype_card, Fintype.card_fin])).2

@[expose] def su2RelCodes : List (List Nat) := [[2, 2, 2], [0, 2, 0, 2, 1, 2]]

@[expose] def su2Rels : List (List (Fin 2 × Bool)) := su2RelCodes.map (decodeWord 2)

theorem wordMat_su2Rels : ∀ r ∈ su2Rels, wordMat mat2 r = 1 := by decide +kernel

theorem wordVal_su2Rels : ∀ r ∈ su2Rels, wordVal gen2 r = 1 := fun r hr =>
  wordVal_eq_one gen2 mat2 hg2 hU2 (wordMat_su2Rels r hr)

@[expose] def pairMat (k₁ k₂ : Fin 24) : Fin 2 → Matrix (Fin 2) (Fin 2) F9 :=
  ![wordMat mat2 (su2Words.getD k₁.val []), wordMat mat2 (su2Words.getD k₂.val [])]

@[expose] def torusIdx : List (Fin 24) := [0, 1, 2, 5]

theorem hUw : ∀ k : Fin 24, ct9 (wordMat mat2 (su2Words.getD k.val [])) *
    wordMat mat2 (su2Words.getD k.val []) = 1 := by decide +kernel

theorem pair_cases : ∀ k₁ k₂ : Fin 24, (∀ r ∈ su2Rels, wordMat (pairMat k₁ k₂) r = 1) →
    k₁ ∈ torusIdx ∨ (k₁, k₂) ∈ b3BadPairs := by decide +kernel

theorem torusIdx_of_diag : ∀ k : Fin 24, (wordMat mat2 (su2Words.getD k.val [])) 0 1 = 0 →
    (wordMat mat2 (su2Words.getD k.val [])) 1 0 = 0 → k ∈ torusIdx := by decide +kernel

theorem su2Elt_zero : su2Elt 0 = 1 := by simp [su2Elt, su2Words, decodeWord, wordVal]

theorem su2Elt_one : su2Elt 1 = A2 := by
  simp [su2Elt, su2Words, decodeWord, decodeLetter, wordVal, letterVal, gen2]

theorem su2Elt_two : su2Elt 2 = A2⁻¹ := by
  simp [su2Elt, su2Words, decodeWord, decodeLetter, wordVal, letterVal, gen2]

theorem su2Elt_five : su2Elt 5 = A2 * A2 := by
  simp [su2Elt, su2Words, decodeWord, decodeLetter, wordVal, letterVal, gen2]

theorem A2_mem_torus : A2 ∈ (torusTwo (unitaryInvolution K9 3 1)).range := by
  have h : ((A2 : GL (Fin 2) K9) : Matrix (Fin 2) (Fin 2) K9) = mA.map phi9r := rfl
  refine mem_range_torusTwo_of_offDiag A2 ?_ ?_
  · rw [h]
    simp [mA]
  · rw [h]
    simp [mA]

theorem su2Elt_mem_torus {k : Fin 24} (hk : k ∈ torusIdx) :
    su2Elt k ∈ (torusTwo (unitaryInvolution K9 3 1)).range := by
  simp only [torusIdx, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · rw [su2Elt_zero]
    exact Subgroup.one_mem _
  · rw [su2Elt_one]
    exact A2_mem_torus
  · rw [su2Elt_two]
    exact Subgroup.inv_mem _ A2_mem_torus
  · rw [su2Elt_five]
    exact Subgroup.mul_mem _ A2_mem_torus A2_mem_torus

theorem exists_idx_of_mem_torus {t : Su K9 3 1 2}
    (ht : t ∈ (torusTwo (unitaryInvolution K9 3 1)).range) :
    ∃ k ∈ torusIdx, t = su2Elt k := by
  obtain ⟨k, rfl⟩ := su2Elt_surjective t
  refine ⟨k, torusIdx_of_diag k ?_ ?_, rfl⟩
  · obtain ⟨u, hu⟩ := ht
    have h1 := val_wordVal gen2 mat2 hg2 hU2 (su2Words.getD k.val [])
    have h2 : ((su2Elt k : GL (Fin 2) K9) : Matrix (Fin 2) (Fin 2) K9) 0 1 = 0 := by
      rw [← hu]
      simp [coe_torusTwo]
    have h3 : (wordMat mat2 (su2Words.getD k.val [])).map phi9r 0 1 = 0 := by
      rw [← h1]
      exact h2
    simpa using h3
  · obtain ⟨u, hu⟩ := ht
    have h1 := val_wordVal gen2 mat2 hg2 hU2 (su2Words.getD k.val [])
    have h2 : ((su2Elt k : GL (Fin 2) K9) : Matrix (Fin 2) (Fin 2) K9) 1 0 = 0 := by
      rw [← hu]
      simp [coe_torusTwo]
    have h3 : (wordMat mat2 (su2Words.getD k.val [])).map phi9r 1 0 = 0 := by
      rw [← h1]
      exact h2
    simpa using h3

theorem torus_map_le_of_idx (α : Su K9 3 1 2 ≃* Su K9 3 1 2) {k₁ : Fin 24} (hk : k₁ ∈ torusIdx)
    (h : α A2 = su2Elt k₁) :
    (torusTwo (unitaryInvolution K9 3 1)).range.map α.toMonoidHom ≤
      (torusTwo (unitaryInvolution K9 3 1)).range := by
  have hαA : α A2 ∈ (torusTwo (unitaryInvolution K9 3 1)).range := by
    rw [h]
    exact su2Elt_mem_torus hk
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨k, hkk, rfl⟩ := exists_idx_of_mem_torus ht
  simp only [torusIdx, List.mem_cons, List.not_mem_nil, or_false] at hkk
  show α (su2Elt k) ∈ _
  rcases hkk with rfl | rfl | rfl | rfl
  · rw [su2Elt_zero, map_one]
    exact Subgroup.one_mem _
  · rw [su2Elt_one]
    exact hαA
  · rw [su2Elt_two, map_inv]
    exact Subgroup.inv_mem _ hαA
  · rw [su2Elt_five, map_mul]
    exact Subgroup.mul_mem _ hαA hαA

section Collapse

variable {G : Type} [Group G]

@[expose] noncomputable def sixGens (θ₀ : Su K9 3 1 3 →* G) (ϑ : StatedSp 2 F3F →* G) :
    Fin 6 → G :=
  ![θ₀ (embSUid (unitaryInvolution K9 3 1) 2 A2), θ₀ (embSUid (unitaryInvolution K9 3 1) 2 B2),
    θ₀ (embSUid (unitaryInvolution K9 3 1) 0 A2), θ₀ (embSUid (unitaryInvolution K9 3 1) 0 B2),
    ϑ (b2Coord3.s A2), ϑ (b2Coord3.s B2)]

@[expose] def castL : Fin 4 → Fin 6 := Fin.castLE (by decide)

theorem decodeWord_six_su3 : ∀ c ∈ su3Codes,
    decodeWord 6 c = (decodeWord 4 c).map fun l => (castL l.1, l.2) := by
  decide +kernel

theorem sixGens_su3 (θ₀ : Su K9 3 1 3 →* G) (ϑ : StatedSp 2 F3F →* G) :
    ∀ r ∈ su3Codes.map (decodeWord 6), wordVal (sixGens θ₀ ϑ) r = 1 := by
  intro r hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
  rw [decodeWord_six_su3 c hc, wordVal_reindex]
  have h : (fun i : Fin 4 => sixGens θ₀ ϑ (castL i)) = fun i => θ₀ (x3 i) := by
    funext i
    fin_cases i <;> rfl
  rw [h, wordVal_map θ₀ x3, wordVal_x3_su3Rels _ (List.mem_map.2 ⟨c, hc, rfl⟩), map_one]

theorem sixGens_comm (θ₀ : Su K9 3 1 3 →* G) (ϑ : StatedSp 2 F3F →* G)
    (hcomm : ∀ x ∈ (B12 K9 3 1).map θ₀, ∀ y ∈ b2Coord3.s.range.map ϑ, x * y = y * x) :
    ∀ r ∈ b3CommCodes.map (decodeWord 6), wordVal (sixGens θ₀ ϑ) r = 1 := by
  have hx : ∀ A : Su K9 3 1 2, θ₀ (embSUid (unitaryInvolution K9 3 1) 2 A) ∈
      (B12 K9 3 1).map θ₀ := fun A => ⟨_, ⟨A, rfl⟩, rfl⟩
  have hy : ∀ A : Su K9 3 1 2, ϑ (b2Coord3.s A) ∈ b2Coord3.s.range.map ϑ :=
    fun A => ⟨_, ⟨A, rfl⟩, rfl⟩
  intro r hr
  simp only [b3CommCodes, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (wordVal_comm_iff (sixGens θ₀ ϑ) [(0, true)] [(4, true)]).2
      (by simpa [wordVal, letterVal, sixGens] using hcomm _ (hx A2) _ (hy A2))
  · exact (wordVal_comm_iff (sixGens θ₀ ϑ) [(0, true)] [(5, true)]).2
      (by simpa [wordVal, letterVal, sixGens] using hcomm _ (hx A2) _ (hy B2))
  · exact (wordVal_comm_iff (sixGens θ₀ ϑ) [(1, true)] [(4, true)]).2
      (by simpa [wordVal, letterVal, sixGens] using hcomm _ (hx B2) _ (hy A2))
  · exact (wordVal_comm_iff (sixGens θ₀ ϑ) [(1, true)] [(5, true)]).2
      (by simpa [wordVal, letterVal, sixGens] using hcomm _ (hx B2) _ (hy B2))

end Collapse

section Twist

variable {G : Type} [Group G] {θ₀ : Su K9 3 1 3 →* G} {ϑ : StatedSp 2 F3F →* G}

theorem su2Words_getD (k : Fin 24) :
    su2Words.getD k.val [] = decodeWord 2 (b3Su2Codes.getD k.val []) := by
  revert k
  decide +kernel

theorem wordVal_sixGens_twWord (k : Fin 24) :
    wordVal (sixGens θ₀ ϑ) (twWord k) = θ₀ (embSUid (unitaryInvolution K9 3 1) 0 (su2Elt k)) := by
  rw [twWord, wordVal_reindex, ← su2Words_getD k]
  have h : (fun i : Fin 2 => sixGens θ₀ ϑ (twIdx i)) =
      fun i => (θ₀.comp (embSUid (unitaryInvolution K9 3 1) 0)) (gen2 i) := by
    funext i
    fin_cases i <;> rfl
  rw [h, wordVal_map (θ₀.comp (embSUid (unitaryInvolution K9 3 1) 0)) gen2]
  rfl

theorem wordVal_sixGens_twSubst (α : Su K9 3 1 2 ≃* Su K9 3 1 2)
    (hα : ∀ g, θ₀ (embSUid (unitaryInvolution K9 3 1) 0 (α g)) = ϑ (b2Coord3.ℓ g))
    {k₁ k₂ : Fin 24} (h₁ : α A2 = su2Elt k₁) (h₂ : α B2 = su2Elt k₂) (l : Fin 4 × Bool) :
    wordVal (sixGens θ₀ ϑ) (twSubst k₁ k₂ l) = letterVal (fun i => ϑ (spGens i)) l := by
  have e₁ : θ₀ (embSUid (unitaryInvolution K9 3 1) 0 (su2Elt k₁)) = ϑ (spGens 0) := by
    rw [← h₁]
    exact hα A2
  have e₂ : θ₀ (embSUid (unitaryInvolution K9 3 1) 0 (su2Elt k₂)) = ϑ (spGens 1) := by
    rw [← h₂]
    exact hα B2
  obtain ⟨⟨i, hi⟩, b⟩ := l
  interval_cases i
  · cases b
    · simp [twSubst, wordVal_invWord, wordVal_sixGens_twWord, e₁, letterVal]
    · simp [twSubst, wordVal_sixGens_twWord, e₁, letterVal]
  · cases b
    · simp [twSubst, wordVal_invWord, wordVal_sixGens_twWord, e₂, letterVal]
    · simp [twSubst, wordVal_sixGens_twWord, e₂, letterVal]
  · cases b <;> simp [twSubst, letterVal, wordVal, sixGens, spGens]
  · cases b <;> simp [twSubst, letterVal, wordVal, sixGens, spGens]

theorem sixGens_sp4 (α : Su K9 3 1 2 ≃* Su K9 3 1 2)
    (hα : ∀ g, θ₀ (embSUid (unitaryInvolution K9 3 1) 0 (α g)) = ϑ (b2Coord3.ℓ g))
    {k₁ k₂ : Fin 24} (h₁ : α A2 = su2Elt k₁) (h₂ : α B2 = su2Elt k₂) :
    ∀ r ∈ b3Sp4Rels.map (List.flatMap (twSubst k₁ k₂)), wordVal (sixGens θ₀ ϑ) r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  rw [wordVal_flatMap (sixGens θ₀ ϑ) (fun i => ϑ (spGens i)) (twSubst k₁ k₂)
    (wordVal_sixGens_twSubst α hα h₁ h₂) w, wordVal_map ϑ spGens w, wordVal_spGens_b3Sp4Rels w hw,
    map_one]

end Twist

theorem A2_ne_one : A2 ≠ 1 := by
  intro h
  have h1 : (mA.map phi9r) 0 0 = (1 : Matrix (Fin 2) (Fin 2) K9) 0 0 :=
    congrArg (fun g : Su K9 3 1 2 => ((g : GL (Fin 2) K9) : Matrix (Fin 2) (Fin 2) K9) 0 0) h
  have h2 : i9 = 1 := phi9r.injective (by simpa [mA] using h1)
  exact absurd h2 (by decide)

theorem alpha_torus_three (htw : ∀ p ∈ b3BadPairs, Subsingleton (CFSG.CosetTable.PG 6 (b3TwistRels p.1 p.2))) {G : Type} [Group G]
    {θ₀ : Su K9 3 1 3 →* G}
    (hi2 : Function.Injective (θ₀.comp (embSUid (unitaryInvolution K9 3 1) 2)))
    {ϑ : StatedSp 2 F3F →* G}
    (hcomm : ∀ x ∈ (B12 K9 3 1).map θ₀, ∀ y ∈ b2Coord3.s.range.map ϑ, x * y = y * x)
    (α : Su K9 3 1 2 ≃* Su K9 3 1 2)
    (hα : ∀ g, θ₀ (embSUid (unitaryInvolution K9 3 1) 0 (α g)) = ϑ (b2Coord3.ℓ g)) :
    (torusTwo (unitaryInvolution K9 3 1)).range.map α.toMonoidHom ≤
      (torusTwo (unitaryInvolution K9 3 1)).range := by
  obtain ⟨k₁, hk₁⟩ := su2Elt_surjective (α A2)
  obtain ⟨k₂, hk₂⟩ := su2Elt_surjective (α B2)
  have hrel : ∀ r ∈ su2Rels, wordMat (pairMat k₁ k₂) r = 1 := by
    intro r hr
    set g' : Fin 2 → Su K9 3 1 2 := ![su2Elt k₁, su2Elt k₂] with hg'def
    have hg' : ∀ i, (((g' i : Su K9 3 1 2) : GL (Fin 2) K9) : Matrix (Fin 2) (Fin 2) K9) =
        (pairMat k₁ k₂ i).map phi9r := by
      intro i
      fin_cases i
      · exact val_wordVal gen2 mat2 hg2 hU2 (su2Words.getD k₁.val [])
      · exact val_wordVal gen2 mat2 hg2 hU2 (su2Words.getD k₂.val [])
    have hU' : ∀ i, ct9 (pairMat k₁ k₂ i) * pairMat k₁ k₂ i = 1 := by
      intro i
      fin_cases i
      · exact hUw k₁
      · exact hUw k₂
    have h1 : wordVal g' r = wordVal g' [] := by
      have e : g' = fun i => α.toMonoidHom (gen2 i) := by
        funext i
        fin_cases i
        · exact hk₁
        · exact hk₂
      rw [e, wordVal_map α.toMonoidHom gen2 r, wordVal_su2Rels r hr, map_one]
      rfl
    exact wordMat_eq_of_wordVal_eq g' (pairMat k₁ k₂) hg' hU' h1
  rcases pair_cases k₁ k₂ hrel with hk | hbad
  · exact torus_map_le_of_idx α hk hk₁.symm
  · exfalso
    have hy : ∀ r ∈ b3TwistRels k₁ k₂, wordVal (sixGens θ₀ ϑ) r = 1 := by
      intro r hr
      simp only [b3TwistRels, List.mem_append] at hr
      rcases hr with (hr | hr) | hr
      · exact sixGens_su3 θ₀ ϑ r hr
      · exact sixGens_sp4 α hα hk₁.symm hk₂.symm r hr
      · exact sixGens_comm θ₀ ϑ hcomm r hr
    have h0 := twist_trivial htw hbad (sixGens θ₀ ϑ) hy 0
    have h1 : θ₀ (embSUid (unitaryInvolution K9 3 1) 2 A2) = 1 := h0
    exact A2_ne_one (hi2 (by simpa using h1))

theorem exists_familyB3_three (htw : ∀ p ∈ b3BadPairs, Subsingleton (CFSG.CosetTable.PG 6 (b3TwistRels p.1 p.2))) {G : Type} [Group G]
    {U : Fin 3 → Subgroup G} (hcomm : Commutes (U 0) (U 2))
    (h01 : ∃ W, UnitaryBlockStandardPair K9 3 1 W (U 0) (U 1))
    (h12 : ∃ W, SymplecticPhanPair F3F h2F W (U 1) (U 2)) :
    ∃ E : PhanFamilyB3 b2Coord3 G, (∀ i, (E.ι i).range = U i) ∧
      E.ϑ.ker ≤ Subgroup.center (StatedSp 2 F3F) := by
  obtain ⟨W₁, h01⟩ := h01
  obtain ⟨θ₀, -, hker0, hU0, hU1⟩ := pair_normalize h01
  obtain ⟨hi2, hr0, hj, hr1⟩ := pair_block_inj card_K9 hker0 hU0 hU1
  obtain ⟨W₂, h12⟩ := h12
  obtain ⟨θ, c, -, hkerθ, hinjL, hLU, hSV⟩ := h12
  set ϑ : StatedSp 2 F3F →* G := θ.comp (MulAut.conj c⁻¹).toMonoidHom with hϑ
  have hLϑ : (longBlock F3F 2 1).range.map ϑ = U 1 := by
    rw [hϑ, map_comp_mulEquiv]
    exact hLU
  have hSϑ : (twShort h2F).range.map ϑ = U 2 := by
    rw [hϑ, map_comp_mulEquiv]
    exact hSV
  have hkinj : Function.Injective (ϑ.comp b2Coord3.ℓ) := by
    intro x y hxy
    have hx : b2Coord3.ℓ x ∈ (longBlock F3F 2 1).range := b2Coord3.ℓ_range ▸ ⟨x, rfl⟩
    have hy : b2Coord3.ℓ y ∈ (longBlock F3F 2 1).range := b2Coord3.ℓ_range ▸ ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    have hab : a = b := by
      apply hinjL
      show ϑ (longBlock F3F 2 1 a) = ϑ (longBlock F3F 2 1 b)
      rw [ha, hb]
      exact hxy
    exact b2Coord3.ℓ_inj (by rw [← ha, ← hb, hab])
  have hkrange : (ϑ.comp b2Coord3.ℓ).range = U 1 := by
    rw [MonoidHom.range_comp, b2Coord3.ℓ_range, ← hLϑ]
  obtain ⟨α, hα⟩ := exists_mulEquiv_comp_eq hkinj hj (by rw [hkrange, hr1])
  have hαϑ : ∀ g, θ₀ (embSUid (unitaryInvolution K9 3 1) 0 (α g)) = ϑ (b2Coord3.ℓ g) :=
    fun g => hα g
  have hsrange : b2Coord3.s.range.map ϑ = U 2 := by
    rw [b2Coord3.s_range]
    exact hSϑ
  have hcomm' : ∀ x ∈ (B12 K9 3 1).map θ₀, ∀ y ∈ b2Coord3.s.range.map ϑ, x * y = y * x := by
    rw [hU0, hsrange]
    exact hcomm
  have htor := alpha_torus_three htw hi2 hcomm' α hαϑ
  obtain ⟨β, hβ0, hβ12, hβ23⟩ := CFSG.ClassicalInvolution.PhanB3.exists_mulAut_extend_zero
    card_K9 α htor
  set θ₁ : Su K9 3 1 3 →* G := θ₀.comp β.toMonoidHom with hθ₁
  have hℓ : ϑ.comp b2Coord3.ℓ = θ₁.comp (embSUid (unitaryInvolution K9 3 1) 0) := by
    refine MonoidHom.ext fun g => ?_
    show ϑ (b2Coord3.ℓ g) = θ₀ (β (embSUid (unitaryInvolution K9 3 1) 0 g))
    rw [hβ0, hαϑ]
  have hr0' : (θ₁.comp (embSUid (unitaryInvolution K9 3 1) 2)).range = U 0 := by
    rw [MonoidHom.range_comp]
    show (B12 K9 3 1).map θ₁ = U 0
    rw [hθ₁, map_comp_mulEquiv, hβ12, hU0]
  have hr2' : (ϑ.comp b2Coord3.s).range = U 2 := by
    rw [MonoidHom.range_comp]
    exact hsrange
  have hr1' : (θ₁.comp (embSUid (unitaryInvolution K9 3 1) 0)).range = U 1 := by
    rw [← hℓ]
    exact hkrange
  refine ⟨⟨![θ₁.comp (embSUid (unitaryInvolution K9 3 1) 2),
      θ₁.comp (embSUid (unitaryInvolution K9 3 1) 0), ϑ.comp b2Coord3.s], θ₁, ϑ, rfl, rfl, hℓ,
      rfl, fun a b => ?_⟩, fun i => ?_, ?_⟩
  · have ha : (θ₁.comp (embSUid (unitaryInvolution K9 3 1) 2)) a ∈ U 0 := by
      rw [← hr0']
      exact ⟨a, rfl⟩
    have hb : (ϑ.comp b2Coord3.s) b ∈ U 2 := by
      rw [← hr2']
      exact ⟨b, rfl⟩
    exact hcomm _ ha _ hb
  · fin_cases i
    · exact hr0'
    · exact hr1'
    · exact hr2'
  · exact ker_comp_mulEquiv_le_center hkerθ _

end CFSG.ClassicalInvolution.Phan.Q3G
