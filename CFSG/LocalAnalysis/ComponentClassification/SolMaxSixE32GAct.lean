module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32Frame
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.ComponentClassification.SolMax.Sig36.E32

open CFSG Subgroup Equiv

variable {X : Type} [Group X] [Finite X] {M : Subgroup X}
  {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} {t s : X} {H Q : Subgroup X}

private theorem fc_w : ∀ a0 a2 a3 a4 : ZMod 2,
    (σ₀ ^ a0.val * (p 1 * p 2) ^ a2.val * (p 0 * p 2) ^ a3.val * πx ^ a4.val = p 1 * p 2 ∨
      σ₀ ^ a0.val * (p 1 * p 2) ^ a2.val * (p 0 * p 2) ^ a3.val * πx ^ a4.val = p 0 * p 2 ∨
      σ₀ ^ a0.val * (p 1 * p 2) ^ a2.val * (p 0 * p 2) ^ a3.val * πx ^ a4.val = p 0 * p 1) →
    a0 = 0 ∧ a4 = 0 := by
  unfold σ₀ πx p
  decide

private theorem fc_x : ∀ a0 a2 a3 a4 : ZMod 2,
    (∀ i : Fin 9, i.val < 6 →
      (πx⁻¹ * (σ₀ ^ a0.val * (p 1 * p 2) ^ a2.val * (p 0 * p 2) ^ a3.val * πx ^ a4.val)) i = i) →
    Perm.sign
      (πx⁻¹ * (σ₀ ^ a0.val * (p 1 * p 2) ^ a2.val * (p 0 * p 2) ^ a3.val * πx ^ a4.val)) = 1 →
    a0 = 0 ∧ a2 = 0 ∧ a3 = 0 ∧ a4 = 1 := by
  unfold σ₀ πx p
  decide

namespace IsFrame

variable {Z : Ctx M θ ρ t s H Q} {w₀ w₁ x : X} (F : IsFrame Z w₀ w₁ x)
include F

private theorem c_mem_N {c : X} (hc : c ∈ centralizer ({s, t} : Set X)) :
    c ∈ normalizer (M : Set X) :=
  Z.mem_normalizer_of_mem_C (mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp hc t (by simp)).symm)

private theorem rho_comm {c : X} (hc : c ∈ centralizer ({s, t} : Set X)) :
    rhoX ρ c * σ₀ = σ₀ * rhoX ρ c := by
  have hcs : s * c = c * s := mem_centralizer_iff.mp hc s (by simp)
  have h := congrArg (rhoX ρ) hcs
  rw [rhoX_mul Z.s_mem_N (F.c_mem_N hc), rhoX_mul (F.c_mem_N hc) Z.s_mem_N, Z.hρs] at h
  exact h.symm

private theorem rhoX_mono (a : Fin 5 → ZMod 2) :
    rhoX ρ (mono ![s, t, w₀, w₁, x] a) =
      σ₀ ^ (a 0).val * (p 1 * p 2) ^ (a 2).val * (p 0 * p 2) ^ (a 3).val * πx ^ (a 4).val := by
  have hs : s ∈ normalizer (M : Set X) := Z.s_mem_N
  have ht : t ∈ normalizer (M : Set X) := Z.t_mem_N
  have h0 : w₀ ∈ normalizer (M : Set X) := le_normalizer F.w₀M
  have h1 : w₁ ∈ normalizer (M : Set X) := le_normalizer F.w₁M
  have h4 : x ∈ normalizer (M : Set X) := le_normalizer F.xM
  unfold mono
  show rhoX ρ (s ^ (a 0).val * t ^ (a 1).val * w₀ ^ (a 2).val * w₁ ^ (a 3).val *
    x ^ (a 4).val) = _
  rw [rhoX_mul (mul_mem (mul_mem (mul_mem (pow_mem hs _) (pow_mem ht _)) (pow_mem h0 _))
      (pow_mem h1 _)) (pow_mem h4 _),
    rhoX_mul (mul_mem (mul_mem (pow_mem hs _) (pow_mem ht _)) (pow_mem h0 _)) (pow_mem h1 _),
    rhoX_mul (mul_mem (pow_mem hs _) (pow_mem ht _)) (pow_mem h0 _),
    rhoX_mul (pow_mem hs _) (pow_mem ht _),
    Z.rhoX_pow hs, Z.rhoX_pow ht, Z.rhoX_pow h0, Z.rhoX_pow h1, Z.rhoX_pow h4,
    Z.hρs, Z.rho_t, F.ρw₀, F.ρw₁, F.ρx, one_pow, mul_one]

private theorem coord_one {a : Fin 5 → ZMod 2} (ha0 : a 0 = 0)
    (hM : mono ![s, t, w₀, w₁, x] a ∈ M) : a 1 = 0 := by
  by_contra hne
  have h1 : a 1 = 1 := by
    revert hne
    generalize a 1 = b
    revert b
    decide
  apply Z.t_not_mem_M
  have hm : w₀ ^ (a 2).val * w₁ ^ (a 3).val * x ^ (a 4).val ∈ M :=
    mul_mem (mul_mem (pow_mem F.w₀M _) (pow_mem F.w₁M _)) (pow_mem F.xM _)
  have hfac : mono ![s, t, w₀, w₁, x] a =
      t * (w₀ ^ (a 2).val * w₁ ^ (a 3).val * x ^ (a 4).val) := by
    have e0 : (0 : ZMod 2).val = 0 := rfl
    have e1 : (1 : ZMod 2).val = 1 := rfl
    unfold mono
    show s ^ (a 0).val * t ^ (a 1).val * w₀ ^ (a 2).val * w₁ ^ (a 3).val * x ^ (a 4).val = _
    rw [ha0, h1, e0, e1, pow_zero, one_mul, pow_one]
    simp only [mul_assoc]
  have h := mul_mem hM (inv_mem hm)
  rwa [hfac, mul_inv_cancel_right] at h

private theorem conj_gen_mem {c : X}
    (hcA : (Subgroup.closure (Set.range ![s, t, w₀, w₁, x])).map (MulAut.conj c).toMonoidHom =
      Subgroup.closure (Set.range ![s, t, w₀, w₁, x])) (i : Fin 5) :
    ∃ a, c * ![s, t, w₀, w₁, x] i * c⁻¹ = mono ![s, t, w₀, w₁, x] a := by
  have hmem : c * ![s, t, w₀, w₁, x] i * c⁻¹ ∈
      (Subgroup.closure (Set.range ![s, t, w₀, w₁, x])).map (MulAut.conj c).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨_, Subgroup.subset_closure (Set.mem_range_self i), by simp⟩
  rw [hcA] at hmem
  exact (F.E5.mem_closure_iff _).mp hmem

private theorem conj_w₀ {c : X} (hc : c ∈ centralizer ({s, t} : Set X))
    (hcA : (Subgroup.closure (Set.range ![s, t, w₀, w₁, x])).map (MulAut.conj c).toMonoidHom =
      Subgroup.closure (Set.range ![s, t, w₀, w₁, x])) :
    ∃ a : Fin 5 → ZMod 2, c * w₀ * c⁻¹ = mono ![s, t, w₀, w₁, x] a ∧
      a 0 = 0 ∧ a 1 = 0 ∧ a 4 = 0 := by
  obtain ⟨a, ha⟩ := F.conj_gen_mem hcA 2
  have ha' : c * w₀ * c⁻¹ = mono ![s, t, w₀, w₁, x] a := ha
  have hM : c * w₀ * c⁻¹ ∈ M := (mem_normalizer_iff.mp (F.c_mem_N hc) w₀).mp F.w₀M
  have hF : σ₀ ^ (a 0).val * (p 1 * p 2) ^ (a 2).val * (p 0 * p 2) ^ (a 3).val *
      πx ^ (a 4).val = rhoX ρ c * (p 1 * p 2) * (rhoX ρ c)⁻¹ := by
    rw [← F.rhoX_mono, ← ha', rhoX_conj (F.c_mem_N hc) (le_normalizer F.w₀M), F.ρw₀]
  have h04 := fc_w (a 0) (a 2) (a 3) (a 4) (by rw [hF]; exact Zs_conj_U12 (F.rho_comm hc))
  exact ⟨a, ha', h04.1, F.coord_one h04.1 (by rw [← ha']; exact hM), h04.2⟩

private theorem conj_w₁ {c : X} (hc : c ∈ centralizer ({s, t} : Set X))
    (hcA : (Subgroup.closure (Set.range ![s, t, w₀, w₁, x])).map (MulAut.conj c).toMonoidHom =
      Subgroup.closure (Set.range ![s, t, w₀, w₁, x])) :
    ∃ a : Fin 5 → ZMod 2, c * w₁ * c⁻¹ = mono ![s, t, w₀, w₁, x] a ∧
      a 0 = 0 ∧ a 1 = 0 ∧ a 4 = 0 := by
  obtain ⟨a, ha⟩ := F.conj_gen_mem hcA 3
  have ha' : c * w₁ * c⁻¹ = mono ![s, t, w₀, w₁, x] a := ha
  have hM : c * w₁ * c⁻¹ ∈ M := (mem_normalizer_iff.mp (F.c_mem_N hc) w₁).mp F.w₁M
  have hF : σ₀ ^ (a 0).val * (p 1 * p 2) ^ (a 2).val * (p 0 * p 2) ^ (a 3).val *
      πx ^ (a 4).val = rhoX ρ c * (p 0 * p 2) * (rhoX ρ c)⁻¹ := by
    rw [← F.rhoX_mono, ← ha', rhoX_conj (F.c_mem_N hc) (le_normalizer F.w₁M), F.ρw₁]
  have h04 := fc_w (a 0) (a 2) (a 3) (a 4) (by rw [hF]; exact Zs_conj_U02 (F.rho_comm hc))
  exact ⟨a, ha', h04.1, F.coord_one h04.1 (by rw [← ha']; exact hM), h04.2⟩

private theorem conj_x {c : X} (hc : c ∈ centralizer ({s, t} : Set X))
    (hcA : (Subgroup.closure (Set.range ![s, t, w₀, w₁, x])).map (MulAut.conj c).toMonoidHom =
      Subgroup.closure (Set.range ![s, t, w₀, w₁, x])) :
    c * x * c⁻¹ = x := by
  obtain ⟨a, ha⟩ := F.conj_gen_mem hcA 4
  have ha' : c * x * c⁻¹ = mono ![s, t, w₀, w₁, x] a := ha
  have hM : c * x * c⁻¹ ∈ M := (mem_normalizer_iff.mp (F.c_mem_N hc) x).mp F.xM
  have hF : σ₀ ^ (a 0).val * (p 1 * p 2) ^ (a 2).val * (p 0 * p 2) ^ (a 3).val *
      πx ^ (a 4).val = rhoX ρ c * πx * (rhoX ρ c)⁻¹ := by
    rw [← F.rhoX_mono, ← ha', rhoX_conj (F.c_mem_N hc) (le_normalizer F.xM), F.ρx]
  have hz := Zs_conj_πx (F.rho_comm hc)
  rw [← hF] at hz
  obtain ⟨h0, h2, h3, h4⟩ := fc_x (a 0) (a 2) (a 3) (a 4) (fun i hi => hz.1 i hi)
    (Perm.mem_alternatingGroup.mp hz.2)
  have h1 : a 1 = 0 := F.coord_one h0 (by rw [← ha']; exact hM)
  have e0 : (0 : ZMod 2).val = 0 := rfl
  have e1 : (1 : ZMod 2).val = 1 := rfl
  rw [ha']
  unfold mono
  show s ^ (a 0).val * t ^ (a 1).val * w₀ ^ (a 2).val * w₁ ^ (a 3).val * x ^ (a 4).val = x
  rw [h0, h1, h2, h3, h4, e0, e1]
  simp

theorem gamma_action {c : X} (hc : c ∈ centralizer ({s, t} : Set X))
    (hcA : (Subgroup.closure (Set.range ![s, t, w₀, w₁, x])).map (MulAut.conj c).toMonoidHom =
      Subgroup.closure (Set.range ![s, t, w₀, w₁, x])) (v : Fin 5 → ZMod 2) :
    ∃ u : Fin 5 → ZMod 2, u 0 = 0 ∧ u 1 = 0 ∧ u 4 = 0 ∧
      c * mono ![s, t, w₀, w₁, x] v * c⁻¹ =
        mono ![s, t, w₀, w₁, x] v * mono ![s, t, w₀, w₁, x] u := by
  have hcs : s * c = c * s := mem_centralizer_iff.mp hc s (by simp)
  have hct : t * c = c * t := mem_centralizer_iff.mp hc t (by simp)
  have hs : c * s * c⁻¹ = s := by rw [← hcs, mul_inv_cancel_right]
  have ht : c * t * c⁻¹ = t := by rw [← hct, mul_inv_cancel_right]
  obtain ⟨a₀, ha₀, h00, h01, h04⟩ := F.conj_w₀ hc hcA
  obtain ⟨a₁, ha₁, h10, h11, h14⟩ := F.conj_w₁ hc hcA
  have hx := F.conj_x hc hcA
  let cv : Fin 5 → Fin 5 → ZMod 2 := ![Pi.single 0 1, Pi.single 1 1, a₀, a₁, Pi.single 4 1]
  have hν : ∀ i, c * ![s, t, w₀, w₁, x] i * c⁻¹ = mono ![s, t, w₀, w₁, x] (cv i) := by
    intro i
    fin_cases i
    · show c * s * c⁻¹ = mono _ (Pi.single 0 1)
      rw [F.E5.mono_single 0]
      exact hs
    · show c * t * c⁻¹ = mono _ (Pi.single 1 1)
      rw [F.E5.mono_single 1]
      exact ht
    · exact ha₀
    · exact ha₁
    · show c * x * c⁻¹ = mono _ (Pi.single 4 1)
      rw [F.E5.mono_single 4]
      exact hx
  have h2 : (2 : ZMod 2) = 0 := rfl
  refine ⟨v 2 • (Pi.single 2 1 + a₀) + v 3 • (Pi.single 3 1 + a₁), ?_, ?_, ?_, ?_⟩
  · simp [h00, h10]
  · simp [h01, h11]
  · simp [h04, h14]
  · rw [F.E5.conj_mono c cv hν v, ← F.E5.mono_add]
    congr 1
    funext j
    fin_cases j
    · simp [Fin.sum_univ_five, cv, h00, h10]
    · simp [Fin.sum_univ_five, cv, h01, h11]
    · simp [Fin.sum_univ_five, cv]
      linear_combination (-(v 2)) * h2
    · simp [Fin.sum_univ_five, cv]
      linear_combination (-(v 3)) * h2
    · simp [Fin.sum_univ_five, cv, h04, h14]

end IsFrame

end CFSG.ComponentClassification.SolMax.Sig36.E32
