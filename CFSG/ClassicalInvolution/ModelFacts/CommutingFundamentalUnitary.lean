module

public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalLinear
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTransfer
public import CFSG.ClassicalInvolution.RouteD.TypeULocal

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open Matrix Module CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply Su blockEmb blockEmb2)
open scoped MatrixGroups

section Frame

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem exists_su_frame_signs (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) ≠ 0) (hn : 0 < n)
    {i₁ i₂ : SUid σ n} (h₁ : suMat i₁ * suMat i₁ = 1) (h₂ : suMat i₂ * suMat i₂ = 1)
    (hc : suMat i₁ * suMat i₂ = suMat i₂ * suMat i₁) :
    ∃ (g : SUid σ n) (ε : Fin n → Bool × Bool),
      suMat i₁ * suMat g = suMat g * Matrix.diagonal (fun j => signOf K (ε j).1) ∧
      suMat i₂ * suMat g = suMat g * Matrix.diagonal (fun j => signOf K (ε j).2) := by
  have hint := isInternal_jointEigenspace h2 (toLin'_mul_self h₁) (toLin'_mul_self h₂)
    (toLin'_mul_comm hc)
  have hsum : ∑ s, finrank K (jointEig (suMat i₁) (suMat i₂) s) = n := by
    have := finrank_eq_sum_of_isInternal (jointEig (suMat i₁) (suMat i₂)) hint
    simpa using this.symm
  obtain ⟨ε, hε⟩ := exists_fibre_map (fun s => finrank K (jointEig (suMat i₁) (suMat i₂) s)) n hsum
  obtain ⟨g, hg⟩ := exists_su_frame hσ h2 hn h₁ h₂ hc ε hε
  exact ⟨g, ε, hg⟩

theorem commute_conj_of_diagonal_su {P i y : SUid σ n} (d : Fin n → K)
    (hi : suMat i * suMat P = suMat P * Matrix.diagonal d)
    (hy : Matrix.diagonal d * suMat y = suMat y * Matrix.diagonal d) :
    i * (P * y * P⁻¹) = (P * y * P⁻¹) * i := by
  have hD : suMat (P⁻¹ * i * P) = Matrix.diagonal d := by
    rw [suMat_mul, suMat_mul, Matrix.mul_assoc, hi, ← Matrix.mul_assoc, suMat_inv_mul_suMat,
      Matrix.one_mul]
  have hcomm : (P⁻¹ * i * P) * y = y * (P⁻¹ * i * P) := by
    apply suMat_injective
    have e1 : suMat ((P⁻¹ * i * P) * y) = suMat (P⁻¹ * i * P) * suMat y := suMat_mul _ _
    have e2 : suMat (y * (P⁻¹ * i * P)) = suMat y * suMat (P⁻¹ * i * P) := suMat_mul _ _
    rw [e1, e2, hD, hy]
  have hi' : i = P * (P⁻¹ * i * P) * P⁻¹ := by group
  calc i * (P * y * P⁻¹) = P * (P⁻¹ * i * P) * P⁻¹ * (P * y * P⁻¹) := by rw [← hi']
    _ = P * ((P⁻¹ * i * P) * y) * P⁻¹ := by group
    _ = P * (y * (P⁻¹ * i * P)) * P⁻¹ := by rw [hcomm]
    _ = (P * y * P⁻¹) * (P * (P⁻¹ * i * P) * P⁻¹) := by group
    _ = (P * y * P⁻¹) * i := by rw [← hi']

end Frame

section Main

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem iSup_longRootSetU_centralizing (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {m : ℕ}
    (hn : 3 ≤ m + 1) {i₁ i₂ : Su K p f (m + 1)} (h₁ : i₁ * i₁ = 1) (h₂ : i₂ * i₂ = 1)
    (hc : i₁ * i₂ = i₂ * i₁) :
    (⊤ : Subgroup (Su K p f (m + 1))) ≤
      ⨆ R ∈ longRootSetU (K := K) (p := p) (f := f) (by omega : 2 ≤ m + 1),
        ⨆ (_ : R ≤ Subgroup.centralizer ({i₁} : Set (Su K p f (m + 1))) ∨
          R ≤ Subgroup.centralizer ({i₂} : Set (Su K p f (m + 1))) ∨
          R ≤ Subgroup.centralizer ({i₁ * i₂} : Set (Su K p f (m + 1)))), R := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hq2 : p ^ f ≠ 2 := by
    intro h
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at h
    · have hdvd : p ∣ 2 := h ▸ dvd_pow_self p hf.ne'
      exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 hdvd)
  have hmat : ∀ {x : Su K p f (m + 1)}, x * x = 1 → suMat x * suMat x = 1 := fun h => by
    rw [← suMat_mul, h, suMat_one]
  obtain ⟨P, ε, hP₁, hP₂⟩ := exists_su_frame_signs hσ h2 (by omega) (hmat h₁) (hmat h₂)
    (by rw [← suMat_mul, ← suMat_mul, hc])
  have hP₃ : suMat (i₁ * i₂) * suMat P = suMat P *
      Matrix.diagonal (fun j => signOf K (ε j).1 * signOf K (ε j).2) := by
    rw [suMat_mul, Matrix.mul_assoc, hP₂, ← Matrix.mul_assoc, hP₁, Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal]
  set blk : Fin m → Subgroup (Su K p f (m + 1)) :=
    fun k => ((blockEmb2 K p f m k).range).map (MulAut.conj P).toMonoidHom with hblk
  have hmem : ∀ k, blk k ∈ longRootSetU (K := K) (p := p) (f := f) (by omega : 2 ≤ m + 1) :=
    fun k => longRootSetU_conjInvariant (by omega) P _
      ⟨_, isLongRootSU2_range_blockEmb hK hp (j := k.val) (by have := k.isLt; omega)⟩
  have hblock : ∀ (k : Fin m) (d : Fin (m + 1) → K) (i : Su K p f (m + 1)),
      suMat i * suMat P = suMat P * Matrix.diagonal d →
      d ⟨k.val, by omega⟩ = d ⟨k.val + 1, by have := k.isLt; omega⟩ →
      blk k ≤ Subgroup.centralizer ({i} : Set (Su K p f (m + 1))) := by
    intro k d i hi hd
    rintro _ ⟨y, ⟨A, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy : Matrix.diagonal d * suMat (blockEmb2 K p f m k A) =
        suMat (blockEmb2 K p f m k A) * Matrix.diagonal d := by
      have e : suMat (blockEmb2 K p f m k A) = blockMat (m + 1) k.val (suMat A) :=
        suMat_blockEmb (by have := k.isLt; omega) A
      rw [e]
      refine diagonal_mul_blockMat_comm (j := k.val) d (fun a b ha hb => ?_) (suMat A)
      have ha' : a = ⟨k.val, by omega⟩ ∨ a = ⟨k.val + 1, by have := k.isLt; omega⟩ := by
        rcases ha with ⟨ha1, ha2⟩
        rcases Nat.lt_or_ge a.val (k.val + 1) with h | h
        · exact Or.inl (Fin.ext (by simp only; omega))
        · exact Or.inr (Fin.ext (by simp only; omega))
      have hb' : b = ⟨k.val, by omega⟩ ∨ b = ⟨k.val + 1, by have := k.isLt; omega⟩ := by
        rcases hb with ⟨hb1, hb2⟩
        rcases Nat.lt_or_ge b.val (k.val + 1) with h | h
        · exact Or.inl (Fin.ext (by simp only; omega))
        · exact Or.inr (Fin.ext (by simp only; omega))
      rcases ha' with h | h <;> rcases hb' with h' | h' <;> rw [h, h'] <;>
        first | rfl | exact hd | exact hd.symm
    exact (commute_conj_of_diagonal_su d hi hy).symm
  have hcent : ∀ k : Fin m, blk k ≤ Subgroup.centralizer ({i₁} : Set (Su K p f (m + 1))) ∨
      blk k ≤ Subgroup.centralizer ({i₂} : Set (Su K p f (m + 1))) ∨
      blk k ≤ Subgroup.centralizer ({i₁ * i₂} : Set (Su K p f (m + 1))) := by
    intro k
    by_cases h1 : (ε ⟨k.val, by omega⟩).1 = (ε ⟨k.val + 1, by have := k.isLt; omega⟩).1
    · exact Or.inl (hblock k _ i₁ hP₁ (by simp only [h1]))
    · by_cases h2' : (ε ⟨k.val, by omega⟩).2 = (ε ⟨k.val + 1, by have := k.isLt; omega⟩).2
      · exact Or.inr (Or.inl (hblock k _ i₂ hP₂ (by simp only [h2'])))
      · exact Or.inr (Or.inr (hblock k _ (i₁ * i₂) hP₃ (signOf_mul_eq_of_ne h1 h2')))
  have hgen : (⊤ : Subgroup (Su K p f (m + 1))) ≤ ⨆ k, blk k := by
    have h1 : ⨆ k : Fin m, blk k =
        (⨆ k : Fin m, (blockEmb2 K p f m k).range).map (MulAut.conj P).toMonoidHom := by
      rw [Subgroup.map_iSup]
    rw [h1, Phan.iSup_range_blockEmb2 hK hq2 m,
      Subgroup.map_top_of_surjective _ (MulAut.conj P).surjective]
  exact hgen.trans (iSup_le fun k =>
    le_iSup₂_of_le (blk k) (hmem k) (le_iSup_of_le (hcent k) le_rfl))

theorem commutingGeneration_longRootSetU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {n : ℕ}
    (hn : 3 ≤ n) : CommutingGeneration (longRootSetU (K := K) (p := p) (f := f)
      (by omega : 2 ≤ n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro R₁ hR₁ R₂ hR₂ c₁ hc₁ c₂ hc₂ hz₁ hz₂ hx₂₁ hx₁₂
  obtain ⟨d₁, h₁⟩ := hR₁
  obtain ⟨d₂, h₂⟩ := hR₂
  have h2F : (2 : CFSG.LieType.Steinberg.fixedSubfield K p f) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card _ (odd_natCard_fixedSubfield hK hp)
  have hsq : ∀ {R : Subgroup (Su K p f (m + 1))} {d c : Su K p f (m + 1)},
      IsLongRootSU2 K p f (by omega : 2 ≤ m + 1) R d → c ∈ R → (∀ r ∈ R, c * r = r * c) →
        c * c = 1 := by
    intro R d c h hc hcc
    have hcl := h.isClassicalSL2 hK hp
    rcases eq_one_or_eq_of_isClassicalSL2_center h2F hcl hc hcc with rfl | rfl
    · exact mul_one 1
    · have := pow_orderOf_eq_one c
      rwa [hcl.orderOf_eq_two, sq] at this
  exact iSup_longRootSetU_centralizing hK hp hn (hsq h₁ hc₁ hz₁) (hsq h₂ hc₂ hz₂)
    (hx₂₁ c₁ hc₁).symm

end Main

section Model

variable {p : ℕ} [Fact p.Prime] {n e : ℕ}

theorem commutingFundamentalGeneration_psu (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSU n p e) : CommutingFundamentalGeneration p .PSU n e := by
  have hf : 1 ≤ e := hadm.2.1
  have hn3 : 3 ≤ n := hadm.2.2.1
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  have hK := CFSG.LieType.Universal.card_galoisField_two_mul p e hf
  refine (commutingFundamentalGeneration_iff p .PSU n e).2 ?_
  exact CommutingGeneration.of_mulEquiv φ hφ (commutingGeneration_longRootSetU hK hp2 hn3)

end Model

end CFSG.ClassicalInvolution.ModelFacts
