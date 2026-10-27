module

public import CFSG.ClassicalInvolution.Phan.PhanQ51Conj

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan

section QA

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem vecK_stdFrame3_mem_G (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) (a c : F)
    (hac : a ^ 2 + ε * c ^ 2 = -1) (i : Fin 3) :
    vecK D (stdFrame3 ε a c hac i) ∈ solidOf D (jGK K ε) := by
  rw [vecK_mem_solidOf_iff h2 hε (jG ε) (jGK_extV K ε) (jG_jG ε)]
  fin_cases i
  · exact jG_stdNP1 ε
  · exact jG_stdNP2 ε
  · exact jG_stdNP3 ε a c hac

theorem exists_npairs_of_orthonormal [Finite F] {n : ℕ} (hodd : Odd (Nat.card F))
    (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) (u : Fin n → V8 K) (hQ : ∀ i, Q8 (u i) = 0)
    (hB : ∀ i j, B8 (u i) (u j) = 0) (hH : ∀ i j, her D (u i) (u j) = if i = j then 1 else 0) :
    ∃ (κ : Fin n → K) (z : Fin n → NPair ε), (∀ i, κ i ≠ 0 ∧ u i = κ i • vecK D (z i)) ∧
      ∀ i j, i ≠ j → B8 (z i).x (z j).x = 0 ∧ B8 (z i).x (z j).y = 0 ∧
        B8 (z i).y (z j).x = 0 ∧ B8 (z i).y (z j).y = 0 := by
  have hff : ∀ i, ffK D (u i) := fun i => ⟨hQ i, by rw [hH]; simp⟩
  choose κ hκ z hz using fun i => exists_npair_of_ffK D hodd h2 hε (hff i)
  refine ⟨κ, z, fun i => ⟨hκ i, hz i⟩, fun i j hij => ?_⟩
  have e1 : ∀ i, vecK D (z i) = (κ i)⁻¹ • u i := fun i => by
    rw [hz i, smul_smul, inv_mul_cancel₀ (hκ i), one_smul]
  refine npair_orth_of_vecK D h2 hε ?_ ?_
  · rw [e1 i, e1 j, B8_smul_left, B8_smul_right, hB, mul_zero, mul_zero]
  · rw [e1 i, e1 j, her_smul_left, her_smul_right, hH]
    simp [hij]

theorem exists_phanSolid_of_nondeg [Finite F] [Finite K] {H : Submodule K (V8 K)}
    (hts : ∀ u ∈ H, ∀ v ∈ H, B8 u v = 0)
    (hnd : ∀ u ∈ H, (∀ v ∈ H, her D u v = 0) → u = 0) (hdim : Module.finrank K H ≤ 3)
    (hodd : Odd (Nat.card F)) (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) {σ : K ≃+* K}
    (hσ : ∀ x, σ x = D.τ x) : ∃ W, PhanSolid D W ∧ H ≤ W := by
  have h2F : (2 : F) ≠ 0 := two_ne_zero_of_algebra (F := F) h2
  have hsq : σ ^ 2 = 1 := by
    ext x
    simp [pow_two, hσ, D.tau_tau]
  have hne : σ ≠ 1 := by
    intro h
    have h1 : D.τ D.θ = D.θ := by rw [← hσ, h]; rfl
    rw [D.tau_theta] at h1
    have h22 : (2 : K) * D.θ = 0 := by linear_combination -h1
    exact theta_ne_zero D hε ((mul_eq_zero.1 h22).resolve_left h2)
  have hnd' : (herW D H σ hσ).Nondegenerate := by
    constructor
    · intro x hx
      apply Subtype.ext
      apply hnd x.1 x.2
      intro v hv
      have := hx ⟨v, hv⟩
      rw [herW_apply] at this
      rw [her_conj_symm, this, map_zero]
    · intro y hy
      apply Subtype.ext
      apply hnd y.1 y.2
      intro v hv
      have := hy ⟨v, hv⟩
      rw [herW_apply] at this
      exact this
  obtain ⟨b, hb⟩ := CFSG.ComponentClassification.CatalogueBHermitian.exists_orthonormal_basis
    (herW D H σ hσ) (herW_isSymm D H σ hσ) hnd' hsq hne
  let u : Fin (Module.finrank K H) → V8 K := fun i => (b i : V8 K)
  have hu_her : ∀ i j, her D (u i) (u j) = if i = j then 1 else 0 := by
    intro i j
    have := hb j i
    rw [herW_apply] at this
    show her D (b i : V8 K) (b j : V8 K) = _
    rw [this]
    simp [eq_comm]
  have hu_Q : ∀ i, Q8 (u i) = 0 := by
    intro i
    have h1 := hts _ (b i).2 _ (b i).2
    rw [B8_self] at h1
    exact (mul_eq_zero.1 h1).resolve_left h2
  have hu_B : ∀ i j, B8 (u i) (u j) = 0 := fun i j => hts _ (b i).2 _ (b j).2
  obtain ⟨κ, z, hκz, hzorth⟩ := exists_npairs_of_orthonormal D hodd h2 hε u hu_Q hu_B hu_her
  obtain ⟨s, t, hst⟩ := exists_norm_eq hodd hε (-1)
  have hac : s ^ 2 + ε * (t / ε) ^ 2 = -1 := by
    rw [← hst]
    field_simp
  let z0 : Fin (Module.finrank K H) → NPair ε := fun i =>
    stdFrame3 ε s (t / ε) hac (Fin.castLE hdim i)
  obtain ⟨g, hg⟩ := exists_spin_frames hdim hodd h2F hε z z0 hzorth
    (fun i j hij =>
      stdFrame3_orth ε s (t / ε) hac _ _ (fun h => hij (Fin.castLE_injective hdim h)))
  have hWG := (phanJK_jGK D).phanSolid h2 hε
  refine ⟨_, hWG.map_gK D g, fun v hv => ?_⟩
  have hu_mem : ∀ i, u i ∈ (solidOf D (jGK K ε)).map (gK K g) := by
    intro i
    rw [(hκz i).2]
    refine Submodule.smul_mem _ _ ?_
    rw [← hg i, ← gK_vecK]
    exact ⟨_, vecK_stdFrame3_mem_G D h2 hε s (t / ε) hac _, rfl⟩
  have hsum := b.sum_repr ⟨v, hv⟩
  have : v = ∑ i, (b.repr ⟨v, hv⟩ i) • u i := by
    have h1 := congrArg Subtype.val hsum
    rw [Submodule.coe_sum] at h1
    exact h1.symm
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hu_mem i)

end QA

end CFSG.ClassicalInvolution.PhanQ
