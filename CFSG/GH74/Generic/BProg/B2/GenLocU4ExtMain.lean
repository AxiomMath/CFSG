module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtClass
public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtMu
public import CFSG.GH74.Generic.S1.UniGraph

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.GH74 CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace GenLocU4ExtMain

variable {K : Type} [Field K]

@[expose] def smulGL (u : K) (hu : u ≠ 0) (N : GL (Fin 4) K) : GL (Fin 4) K :=
  ⟨u • (N : Matrix (Fin 4) (Fin 4) K), u⁻¹ • ((N⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K),
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hu, one_smul, Units.mul_inv],
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hu, one_smul, Units.inv_mul]⟩

theorem coe_smulGL (u : K) (hu : u ≠ 0) (N : GL (Fin 4) K) :
    ((smulGL u hu N : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = u • (N : Matrix (Fin 4) (Fin 4) K) := rfl

theorem conj_congr (A A' : GL (Fin 4) K) {ν : K} (hν : ν ≠ 0)
    (h : (A : Matrix (Fin 4) (Fin 4) K) = ν • (A' : Matrix (Fin 4) (Fin 4) K)) (g : GL (Fin 4) K) :
    A * g * A⁻¹ = A' * g * A'⁻¹ := by
  have h1 : (A : Matrix (Fin 4) (Fin 4) K) * (ν⁻¹ • ((A'⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) = 1 := by
    rw [h, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hν, one_smul]
    exact A'.mul_inv
  have hinv : ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ν⁻¹ • ((A'⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := Units.inv_eq_of_mul_eq_one_right h1
  apply Units.ext
  simp only [Units.val_mul]
  rw [h, hinv]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [inv_mul_cancel₀ hν, one_smul]

theorem rho_sq_scalar_U {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) [Finite K]
    (β : MulAut ↥(StatedSU 4 (p ^ f) K)) (u : GL (Fin 4) K) (hβ2 : β * β = 1)
    (hu : ∀ g : ↥(StatedSU 4 (p ^ f) K), (((β g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (u : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((u⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
    ∃ l : K, l ≠ 0 ∧ (u : Matrix (Fin 4) (Fin 4) K) * (u : Matrix (Fin 4) (Fin 4) K) =
      l • (1 : Matrix (Fin 4) (Fin 4) K) := by
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  obtain ⟨l, hl⟩ := CFSG.GH74.Generic.S1.Uni.commutant_scalar h hp2
    (S := (u : Matrix (Fin 4) (Fin 4) K) * (u : Matrix (Fin 4) (Fin 4) K)) (fun m hm => by
      have h2 := congrArg (fun φ : MulAut ↥(StatedSU 4 (p ^ f) K) =>
        (((φ ⟨m, hm⟩ : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hβ2
      simp only [MulAut.mul_apply, MulAut.one_apply, hu] at h2
      have h2' : u * (u * m * u⁻¹) * u⁻¹ = m := Units.ext (by simpa [Units.val_mul] using h2)
      have h3 : m * (u * u) = u * u * m := by
        calc m * (u * u) = (u * (u * m * u⁻¹) * u⁻¹) * (u * u) := by rw [h2']
          _ = u * u * m := by group
      simpa [Units.val_mul] using congrArg (fun z : GL (Fin 4) K => (z : Matrix (Fin 4) (Fin 4) K)) h3.symm)
  refine ⟨l, fun h0 => ?_, hl⟩
  have hu1 := (u * u).mul_inv
  rw [Units.val_mul, hl, h0, zero_smul, zero_mul] at hu1
  exact zero_ne_one hu1

theorem index_le_two_of_cover' {A : Type} [Group A] (H : Subgroup A) (b₀ : A)
    (h : ∀ b : A, b ∈ H ∨ b * b₀ ∈ H) : H.index ≤ 2 := by
  by_cases hb : b₀ ∈ H
  · have : H = ⊤ := eq_top_iff.2 fun b _ => (h b).elim id fun hb' => by
      simpa using H.mul_mem hb' (H.inv_mem hb)
    rw [this, Subgroup.index_top]
    omega
  · have : H.index = 2 := by
      refine Subgroup.index_eq_two_iff.2 ⟨b₀, fun b => ?_⟩
      by_cases hbH : b ∈ H
      · exact Or.inr ⟨hbH, fun hh => hb (by simpa using H.mul_mem (H.inv_mem hbH) hh)⟩
      · exact Or.inl ⟨(h b).resolve_left hbH, hbH⟩
    omega

theorem mem_gammaAct_of_fix' {J : Type} [Group J] {A : Type} [Group A] [Finite A]
    (hA : CFSG.IsElementaryAbelian 2 A) (α : A →* MulAut J) (x : MulAut J)
    (hidx : ((Subgroup.zpowers x).comap α).index ≤ 2) (g : J) (hg : x g = g) : g ∈ gammaAct α := by
  refine le_gammaAct α ((GenLocBasic.adm_iff_index hA _).2 hidx)
    ((GenLocBasic.mem_fixedIn_map α _ g).2 fun e he => ?_)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (show α e ∈ Subgroup.zpowers x from he)
  have hx : x ∈ MulAction.stabilizer (MulAut J) g := by
    rw [MulAction.mem_stabilizer_iff]
    exact hg
  have h1 := (MulAction.stabilizer (MulAut J) g).zpow_mem hx k
  rw [MulAction.mem_stabilizer_iff] at h1
  rw [← hk]
  exact h1

theorem smul_unitary_eq4 {q : ℕ} (d : K) (B : Matrix (Fin 4) (Fin 4) K) :
    ((d • B).map (· ^ q))ᵀ * (d • B) = (d ^ q * d) • ((B.map (· ^ q))ᵀ * B) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    mul_pow, Fin.sum_univ_four]
  ring

theorem norm_one_of_sq {p f : ℕ} (h : UnitaryFieldData p f K) (M : Matrix (Fin 4) (Fin 4) K) (c : K)
    (hU : (M.map (· ^ (p ^ f)))ᵀ * M = 1) (hsq : M * M = c • (1 : Matrix (Fin 4) (Fin 4) K)) :
    c ^ (p ^ f) * c = 1 := by
  rw [← GenLocU4ExtFrame.map_bar_eq h] at hU
  have hc0 : c ≠ 0 := by
    intro h0
    have hM : M = 0 := by
      calc M = ((M.map h.bar)ᵀ * M) * M := by rw [hU, Matrix.one_mul]
        _ = (M.map h.bar)ᵀ * (M * M) := by rw [Matrix.mul_assoc]
        _ = 0 := by rw [hsq, h0, zero_smul, Matrix.mul_zero]
    rw [hM, Matrix.mul_zero] at hU
    exact zero_ne_one hU
  have hI : (M.map h.bar)ᵀ = c⁻¹ • M := by
    refine left_inv_eq_right_inv hU ?_
    rw [Matrix.mul_smul, hsq, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have e1 : (M.map h.bar * M.map h.bar)ᵀ = (c⁻¹ • M) * (c⁻¹ • M) := by
    rw [Matrix.transpose_mul, hI]
  have e2 : M.map h.bar * M.map h.bar = (h.bar c) • (1 : Matrix (Fin 4) (Fin 4) K) := by
    rw [← Matrix.map_mul, hsq]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [e2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsq, smul_smul] at e1
  have e3 := congrFun (congrFun e1 0) 0
  simp only [Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e3
  have e4 : c ^ (p ^ f) = c⁻¹ := by
    rw [← UnitaryFieldData.bar_apply h]
    rw [e3]
    field_simp
  rw [e4, inv_mul_cancel₀ hc0]

theorem smulGL_mul_smulGL {u v : K} (hu : u ≠ 0) (hv : v ≠ 0) (M M' : GL (Fin 4) K) :
    smulGL u hu M * smulGL v hv M' = smulGL (u * v) (mul_ne_zero hu hv) (M * M') := by
  apply Units.ext
  simp only [Units.val_mul, coe_smulGL, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm v u]

theorem mul_smulGL_comm {u : K} (hu : u ≠ 0) (M g : GL (Fin 4) K) :
    g * smulGL u hu M = smulGL u hu M * g ↔ g * M = M * g := by
  constructor
  · intro h
    apply Units.ext
    have := congrArg (fun z : GL (Fin 4) K => (z : Matrix (Fin 4) (Fin 4) K)) h
    simp only [Units.val_mul, coe_smulGL, Matrix.mul_smul, Matrix.smul_mul] at this ⊢
    exact smul_right_injective _ hu this
  · intro h
    apply Units.ext
    have := congrArg (fun z : GL (Fin 4) K => (z : Matrix (Fin 4) (Fin 4) K)) h
    simp only [Units.val_mul, coe_smulGL, Matrix.mul_smul, Matrix.smul_mul] at this ⊢
    rw [this]

theorem conj_fix (N g : GL (Fin 4) K) (h : g * N = N * g) : N * g * N⁻¹ = g := by
  rw [← h]; group

theorem core_split {p f : ℕ} [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) {A : Type} [Group A] [Finite A] (hA : CFSG.IsElementaryAbelian 2 A)
    (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (ρ : A → GL (Fin 4) K)
    (hU : ∀ a, ((ρ a : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (ρ a : Matrix (Fin 4) (Fin 4) K) = 1)
    (hρ : ∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
      ((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) = ρ a * g * (ρ a)⁻¹)
    (a₀ : A) (c : K) (hc : ∀ μ : K, μ ^ (p ^ f + 1) = 1 → μ * μ ≠ c)
    (hsq : (ρ a₀ : Matrix (Fin 4) (Fin 4) K) * (ρ a₀ : Matrix (Fin 4) (Fin 4) K) = c • (1 : Matrix (Fin 4) (Fin 4) K))
    (N : GL (Fin 4) K) (b₀ : A)
    (hb₀ : ∀ g : ↥(StatedSU 4 (p ^ f) K), ((α b₀ g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) = N * g * N⁻¹)
    (hNU : ((N : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (N : Matrix (Fin 4) (Fin 4) K) = 1)
    {s : K} (hs : s ^ (p ^ f + 1) = 1)
    (hN2 : (N : Matrix (Fin 4) (Fin 4) K) * (N : Matrix (Fin 4) (Fin 4) K) = (s * s) • (1 : Matrix (Fin 4) (Fin 4) K))
    (hcomm : ∀ b, ρ b * N = N * ρ b) (hN1 : ∀ l : K, (N : Matrix (Fin 4) (Fin 4) K) ≠ l • (1 : Matrix (Fin 4) (Fin 4) K))
    (hab : ∀ a b, ρ a * ρ b = ρ b * ρ a) : gammaAct α = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2 : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  have hq0 : p ^ f ≠ 0 := by omega
  have hc1 : c ^ (p ^ f + 1) = 1 := by
    rw [pow_succ]; exact norm_one_of_sq h (ρ a₀ : Matrix (Fin 4) (Fin 4) K) c (hU a₀) hsq
  obtain ⟨ω, hω, hωc⟩ := GenLocU4ExtMu.exists_omega hp hp2 hK hq hc1 (fun ⟨μ, hμ, hμ2⟩ => hc μ hμ hμ2)
  have hω' : ω ^ (p ^ f) * ω = 1 := by rw [← pow_succ]; exact hω
  have hs' : s ^ (p ^ f) * s = 1 := by rw [← pow_succ]; exact hs
  have hs0 : s ≠ 0 := fun h0 => by rw [h0] at hs; simp at hs
  have hω0 : ω ≠ 0 := fun h0 => by rw [h0] at hω; simp at hω
  have hsi0 : s⁻¹ ≠ 0 := inv_ne_zero hs0
  have hsi : (s⁻¹) ^ (p ^ f) * s⁻¹ = 1 := by
    rw [inv_pow, ← mul_inv, hs', inv_one]
  set i : GL (Fin 4) K := ρ a₀ with hi
  let x : GL (Fin 4) K := smulGL s⁻¹ hsi0 N
  let y : GL (Fin 4) K := smulGL ω hω0 i
  have hx2 : x * x = 1 := by
    apply Units.ext
    rw [Units.val_mul, coe_smulGL, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hN2, smul_smul, Units.val_one]
    have : s⁻¹ * s⁻¹ * (s * s) = 1 := by field_simp
    rw [this, one_smul]
  have hxU : ((x : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (x : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [coe_smulGL, smul_unitary_eq4, hNU, hsi, one_smul]
  have hyU : ((y : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (y : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [coe_smulGL, smul_unitary_eq4, hU a₀, hω', one_smul]
  have hy2 : (y * y : GL (Fin 4) K) = -1 := by
    apply Units.ext
    rw [Units.val_mul, coe_smulGL, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsq, smul_smul, Units.val_neg,
      Units.val_one, hωc, neg_smul, one_smul]
  have hNi : (i : GL (Fin 4) K) * N = N * i := hcomm a₀
  have hNim : (i : Matrix (Fin 4) (Fin 4) K) * (N : Matrix (Fin 4) (Fin 4) K) =
      (N : Matrix (Fin 4) (Fin 4) K) * (i : Matrix (Fin 4) (Fin 4) K) := by
    simpa [Units.val_mul] using congrArg (fun z : GL (Fin 4) K => (z : Matrix (Fin 4) (Fin 4) K)) hNi
  have hxi : x * i = i * x := by
    apply Units.ext
    simp only [x, Units.val_mul, coe_smulGL, Matrix.smul_mul, Matrix.mul_smul]
    rw [hNim]
  have hxy : x * y = y * x := by
    apply Units.ext
    simp only [x, y, Units.val_mul, coe_smulGL, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hNim, mul_comm ω s⁻¹]
  have hxn : ∀ l : K, (x : Matrix (Fin 4) (Fin 4) K) ≠ l • (1 : Matrix (Fin 4) (Fin 4) K) := by
    intro l hl
    rw [coe_smulGL] at hl
    apply hN1 (s * l)
    have : (N : Matrix (Fin 4) (Fin 4) K) = s • (s⁻¹ • (N : Matrix (Fin 4) (Fin 4) K)) := by
      rw [smul_smul, mul_inv_cancel₀ hs0, one_smul]
    rw [this, hl, smul_smul]
  have htr := GenLocU4ExtClass.trace_x_zero hp hp2 hK x i hxU hx2 hxn (hU a₀) c hsq hc hxi
  have := hA
  have hPP : α a₀ * α a₀ = 1 := by
    rw [← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA a₀, map_one]
  have hQQ : α b₀ * α b₀ = 1 := by
    rw [← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA b₀, map_one]
  have hPQ : α a₀ * α b₀ = α b₀ * α a₀ := by
    rw [← map_mul, ← map_mul, mul_comm' a₀ b₀]
  have four : ∀ b, α b = 1 ∨ α b = α a₀ ∨ α b = α b₀ ∨ α b = α a₀ * α b₀ := by
    intro b
    have hβ2 : α b * α b = 1 := by
      rw [← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA b, map_one]
    obtain ⟨l, hl0, hl⟩ := rho_sq_scalar_U hp hp2 hK (α b) (ρ b) hβ2
      (fun g => by rw [hρ b g, Units.val_mul, Units.val_mul])
    have hxg : x * ρ b = ρ b * x := ((mul_smulGL_comm hsi0 N (ρ b)).2 (hcomm b)).symm
    obtain ⟨μ, hμ, h1 | h1 | h1 | h1⟩ := GenLocU4ExtClass.four_class_U hp hp2 hK hq x i (ρ b) hxU hx2 htr
      (hU a₀) c hsq (hU b) l hl hxi hxg (hab a₀ b) ω hω' hωc
    · left
      refine MulEquiv.ext fun g => Subtype.ext ?_
      rw [hρ b g, conj_congr (ρ b) 1 hμ (by rw [Units.val_one]; exact h1) g]
      simp
    · right; right; left
      refine MulEquiv.ext fun g => Subtype.ext ?_
      rw [hρ b g, hb₀ g, conj_congr (ρ b) N (mul_ne_zero hμ hsi0)
        (by rw [h1]; show μ • (s⁻¹ • (N : Matrix (Fin 4) (Fin 4) K)) = (μ * s⁻¹) • (N : Matrix (Fin 4) (Fin 4) K)
            rw [smul_smul]) g]
    · right; left
      refine MulEquiv.ext fun g => Subtype.ext ?_
      rw [hρ b g, hρ a₀ g, conj_congr (ρ b) (ρ a₀) hμ h1 g]
    · right; right; right
      refine MulEquiv.ext fun g => Subtype.ext ?_
      rw [hρ b g, MulAut.mul_apply, hρ a₀, hb₀ g, conj_congr (ρ b) (i * N) (mul_ne_zero hμ hsi0)
        (by rw [h1]
            show μ • ((i * smulGL s⁻¹ hsi0 N : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
              (μ * s⁻¹) • ((i * N : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
            rw [Units.val_mul, coe_smulGL, Matrix.mul_smul, smul_smul, Units.val_mul]) g]
      group
      rfl
  have hHP : ((Subgroup.zpowers (α a₀)).comap α).index ≤ 2 := by
    refine index_le_two_of_cover' _ b₀ (fun b => ?_)
    rcases four b with h | h | h | h
    · left; show α b ∈ Subgroup.zpowers (α a₀); rw [h]; exact one_mem _
    · left; show α b ∈ Subgroup.zpowers (α a₀); rw [h]; exact Subgroup.mem_zpowers _
    · right; show α (b * b₀) ∈ Subgroup.zpowers (α a₀); rw [map_mul, h, hQQ]; exact one_mem _
    · right; show α (b * b₀) ∈ Subgroup.zpowers (α a₀)
      rw [map_mul, h, mul_assoc, hQQ, mul_one]; exact Subgroup.mem_zpowers _
  have hHQ : ((Subgroup.zpowers (α b₀)).comap α).index ≤ 2 := by
    refine index_le_two_of_cover' _ a₀ (fun b => ?_)
    rcases four b with h | h | h | h
    · left; show α b ∈ Subgroup.zpowers (α b₀); rw [h]; exact one_mem _
    · right; show α (b * a₀) ∈ Subgroup.zpowers (α b₀); rw [map_mul, h, hPP]; exact one_mem _
    · left; show α b ∈ Subgroup.zpowers (α b₀); rw [h]; exact Subgroup.mem_zpowers _
    · right; show α (b * a₀) ∈ Subgroup.zpowers (α b₀)
      rw [map_mul, h, hPQ, mul_assoc, hPP, mul_one]; exact Subgroup.mem_zpowers _
  have hHPQ : ((Subgroup.zpowers (α a₀ * α b₀)).comap α).index ≤ 2 := by
    refine index_le_two_of_cover' _ a₀ (fun b => ?_)
    rcases four b with h | h | h | h
    · left; show α b ∈ Subgroup.zpowers (α a₀ * α b₀); rw [h]; exact one_mem _
    · right; show α (b * a₀) ∈ Subgroup.zpowers (α a₀ * α b₀); rw [map_mul, h, hPP]; exact one_mem _
    · right; show α (b * a₀) ∈ Subgroup.zpowers (α a₀ * α b₀)
      rw [map_mul, h, ← hPQ]; exact Subgroup.mem_zpowers _
    · left; show α b ∈ Subgroup.zpowers (α a₀ * α b₀); rw [h]; exact Subgroup.mem_zpowers _
  refine GenLocU4ExtCore.eq_top_of_centralizers_ext_aux hp hp2 hK hq (gammaAct α) x y hx2 hy2 hxy hxU hyU htr
    ?_ ?_ ?_
  · intro g hg
    have hgN : (g : GL (Fin 4) K) * N = N * g := (mul_smulGL_comm hsi0 N g).1 hg
    refine mem_gammaAct_of_fix' hA α (α b₀) hHQ g (Subtype.ext ?_)
    rw [hb₀ g]
    exact conj_fix N g hgN
  · intro g hg
    have hgi : (g : GL (Fin 4) K) * i = i * g := (mul_smulGL_comm hω0 i g).1 hg
    refine mem_gammaAct_of_fix' hA α (α a₀) hHP g (Subtype.ext ?_)
    rw [hρ a₀ g]
    exact conj_fix i g hgi
  · intro g hg
    have hxy' : x * y = smulGL (s⁻¹ * ω) (mul_ne_zero hsi0 hω0) (N * i) := smulGL_mul_smulGL hsi0 hω0 N i
    rw [hxy'] at hg
    have hgNi : (g : GL (Fin 4) K) * (N * i) = (N * i) * g := (mul_smulGL_comm _ (N * i) g).1 hg
    have hgiN : (g : GL (Fin 4) K) * (i * N) = (i * N) * g := by rw [hNi]; exact hgNi
    refine mem_gammaAct_of_fix' hA α (α a₀ * α b₀) hHPQ g (Subtype.ext ?_)
    rw [MulAut.mul_apply, hρ a₀, hb₀ g]
    calc ρ a₀ * (N * (g : GL (Fin 4) K) * N⁻¹) * (ρ a₀)⁻¹ = (ρ a₀ * N) * g * (ρ a₀ * N)⁻¹ := by group
      _ = g := conj_fix (ρ a₀ * N) g hgiN

theorem gammaAct_su4_ext_aux {p f : ℕ} [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) {A : Type} [Group A] [Finite A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K))
    (hA : IsRank23 A) (ρ : A → GL (Fin 4) K)
    (hU : ∀ a, ((ρ a : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (ρ a : Matrix (Fin 4) (Fin 4) K) = 1)
    (hρ : ∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
      (((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (ρ a : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((ρ a)⁻¹ : GL (Fin 4) K))
    (hab : ∀ a b, ρ a * ρ b = ρ b * ρ a) (a₀ : A) (c : K) (hc : ∀ μ : K, μ ^ (p ^ f + 1) = 1 → μ * μ ≠ c)
    (hsq : (ρ a₀ : Matrix (Fin 4) (Fin 4) K) * (ρ a₀ : Matrix (Fin 4) (Fin 4) K) =
      c • (1 : Matrix (Fin 4) (Fin 4) K)) :
    gammaAct α = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hA' := hA.1
  have hρ' : ∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
      ((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) = ρ a * g * (ρ a)⁻¹ := fun a g =>
    Units.ext (by rw [hρ a g, Units.val_mul, Units.val_mul])
  have hsqs : ∀ a, ∃ l : K, l ≠ 0 ∧ (ρ a : Matrix (Fin 4) (Fin 4) K) * (ρ a : Matrix (Fin 4) (Fin 4) K) =
      l • (1 : Matrix (Fin 4) (Fin 4) K) := fun a =>
    rho_sq_scalar_U hp hp2 hK (α a) (ρ a) (by
      rw [← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA' a, map_one]) (hρ a)
  have hc1 : c ^ (p ^ f + 1) = 1 := by
    rw [pow_succ]; exact norm_one_of_sq h (ρ a₀ : Matrix (Fin 4) (Fin 4) K) c (hU a₀) hsq
  have hcnot : ¬ GenLocU4ExtMu.IsSqM (p ^ f) c := fun ⟨μ, hμ, hμ2⟩ => hc μ hμ hμ2
  have hPP : α a₀ * α a₀ = 1 := by
    rw [← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA' a₀, map_one]
  by_cases hall : ∀ a, ∃ l : K, l ≠ 0 ∧ ((ρ a : Matrix (Fin 4) (Fin 4) K) = l • (1 : Matrix (Fin 4) (Fin 4) K) ∨
      (ρ a : Matrix (Fin 4) (Fin 4) K) = l • (ρ a₀ : Matrix (Fin 4) (Fin 4) K))
  · have hcls : ∀ b, α b = 1 ∨ α b = α a₀ := by
      intro b
      obtain ⟨l, hl, h1 | h1⟩ := hall b
      · left
        refine MulEquiv.ext fun g => Subtype.ext ?_
        rw [hρ' b g, conj_congr (ρ b) 1 hl (by rw [Units.val_one]; exact h1) g]
        simp
      · right
        refine MulEquiv.ext fun g => Subtype.ext ?_
        rw [hρ' b g, hρ' a₀ g, conj_congr (ρ b) (ρ a₀) hl h1 g]
    have hidx : α.ker.index ≤ 2 := by
      refine index_le_two_of_cover' _ a₀ (fun b => ?_)
      rcases hcls b with h | h
      · left; exact MonoidHom.mem_ker.2 h
      · right; rw [MonoidHom.mem_ker, map_mul, h, hPP]
    exact gammaAct_eq_top_of_le_ker α (E := α.ker) ((GenLocBasic.adm_iff_index hA' _).2 hidx) le_rfl
  · push Not at hall
    obtain ⟨a₁, ha₁⟩ := hall
    obtain ⟨d, hd0, hd⟩ := hsqs a₁
    have hd1 : d ^ (p ^ f + 1) = 1 := by
      rw [pow_succ]; exact norm_one_of_sq h (ρ a₁ : Matrix (Fin 4) (Fin 4) K) d (hU a₁) hd
    have hunit : ∀ u : GL (Fin 4) K, (u : Matrix (Fin 4) (Fin 4) K) ≠ (0 : K) • (1 : Matrix (Fin 4) (Fin 4) K) := by
      intro u hu
      rw [zero_smul] at hu
      have := u.mul_inv
      rw [hu, Matrix.zero_mul] at this
      exact zero_ne_one this
    by_cases hdsq : GenLocU4ExtMu.IsSqM (p ^ f) d
    · obtain ⟨s, hs, hss⟩ := hdsq
      refine core_split hp hp2 hK hq hA' α ρ hU hρ' a₀ c hc hsq (ρ a₁) a₁ (hρ' a₁) (hU a₁) hs
        (by rw [hd, hss]) (fun b => hab b a₁) (fun l hl => ?_) hab
      by_cases hl0 : l = 0
      · rw [hl0] at hl; exact hunit _ hl
      · exact (ha₁ l hl0).1 hl
    · obtain ⟨s, hs, hss⟩ := GenLocU4ExtMu.isSqM_mul hp hp2 hK hd1 hc1 hdsq hcnot
      have hcm : (ρ a₀ : Matrix (Fin 4) (Fin 4) K) * (ρ a₁ : Matrix (Fin 4) (Fin 4) K) =
          (ρ a₁ : Matrix (Fin 4) (Fin 4) K) * (ρ a₀ : Matrix (Fin 4) (Fin 4) K) := by
        simpa [Units.val_mul] using congrArg (fun z : GL (Fin 4) K => (z : Matrix (Fin 4) (Fin 4) K)) (hab a₀ a₁)
      have hc0 : c ≠ 0 := fun h0 => by rw [h0] at hc1; simp at hc1
      refine core_split hp hp2 hK hq hA' α ρ hU hρ' a₀ c hc hsq (ρ a₁ * ρ a₀) (a₁ * a₀) ?_ ?_ hs ?_
        (fun b => ?_) (fun l hl => ?_) hab
      · intro g
        rw [map_mul, MulAut.mul_apply, hρ' a₁, hρ' a₀]
        group
      · exact GenLocU4ExtCore.unitary_of_mem h (mul_mem (GenLocU4ExtCore.mem_primeFormUnitary_of h (hU a₁))
          (GenLocU4ExtCore.mem_primeFormUnitary_of h (hU a₀)))
      · calc ((ρ a₁ * ρ a₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            ((ρ a₁ * ρ a₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
            = (ρ a₁ : Matrix (Fin 4) (Fin 4) K) * ((ρ a₀ : Matrix (Fin 4) (Fin 4) K) *
                (ρ a₁ : Matrix (Fin 4) (Fin 4) K)) * (ρ a₀ : Matrix (Fin 4) (Fin 4) K) := by
              simp only [Units.val_mul, Matrix.mul_assoc]
          _ = (ρ a₁ : Matrix (Fin 4) (Fin 4) K) * ((ρ a₁ : Matrix (Fin 4) (Fin 4) K) *
                (ρ a₀ : Matrix (Fin 4) (Fin 4) K)) * (ρ a₀ : Matrix (Fin 4) (Fin 4) K) := by rw [hcm]
          _ = ((ρ a₁ : Matrix (Fin 4) (Fin 4) K) * (ρ a₁ : Matrix (Fin 4) (Fin 4) K)) *
                ((ρ a₀ : Matrix (Fin 4) (Fin 4) K) * (ρ a₀ : Matrix (Fin 4) (Fin 4) K)) := by
              simp only [Matrix.mul_assoc]
          _ = (s * s) • (1 : Matrix (Fin 4) (Fin 4) K) := by
              rw [hd, hsq, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, ← hss]
      · calc ρ b * (ρ a₁ * ρ a₀) = (ρ b * ρ a₁) * ρ a₀ := by group
          _ = (ρ a₁ * ρ b) * ρ a₀ := by rw [hab b a₁]
          _ = ρ a₁ * (ρ b * ρ a₀) := by group
          _ = ρ a₁ * (ρ a₀ * ρ b) := by rw [hab b a₀]
          _ = (ρ a₁ * ρ a₀) * ρ b := by group
      · by_cases hl0 : l = 0
        · rw [hl0] at hl; exact hunit _ hl
        · have key : (ρ a₁ : Matrix (Fin 4) (Fin 4) K) = (c⁻¹ * l) • (ρ a₀ : Matrix (Fin 4) (Fin 4) K) := by
            have e1 : ((ρ a₁ : Matrix (Fin 4) (Fin 4) K) * (ρ a₀ : Matrix (Fin 4) (Fin 4) K)) *
                (ρ a₀ : Matrix (Fin 4) (Fin 4) K) = (l • (1 : Matrix (Fin 4) (Fin 4) K)) *
                  (ρ a₀ : Matrix (Fin 4) (Fin 4) K) := by
              have hl' : (ρ a₁ : Matrix (Fin 4) (Fin 4) K) * (ρ a₀ : Matrix (Fin 4) (Fin 4) K) =
                  l • (1 : Matrix (Fin 4) (Fin 4) K) := by simpa [Units.val_mul] using hl
              rw [hl']
            rw [Matrix.mul_assoc, hsq, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] at e1
            calc (ρ a₁ : Matrix (Fin 4) (Fin 4) K) = c⁻¹ • (c • (ρ a₁ : Matrix (Fin 4) (Fin 4) K)) := by
                  rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
              _ = c⁻¹ • (l • (ρ a₀ : Matrix (Fin 4) (Fin 4) K)) := by rw [e1]
              _ = (c⁻¹ * l) • (ρ a₀ : Matrix (Fin 4) (Fin 4) K) := by rw [smul_smul]
          exact (ha₁ (c⁻¹ * l) (mul_ne_zero (inv_ne_zero hc0) hl0)).2 key

end GenLocU4ExtMain
end CFSG.GH74.Generic.BProg.B2
