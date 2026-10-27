module

public import CFSG.ClassicalInvolution.Phan.PhanP7Rot

public section

namespace CFSG.ClassicalInvolution.PhanP

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap CFSG.ClassicalInvolution.PhanD4
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.MF15
open scoped MatrixGroups Pointwise

section Orient

variable {F K : Type} [Field F] [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {S : PhanFamilyD4 K p f (spinGroup (quadPlus 4 F))} {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0}

theorem torusSub_comm_jOp_B (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (hS : ModelSpec S ε hε h4) (hq : 5 ≤ p ^ f) (h2 : (2 : F) ≠ 0) (h2K : (2 : K) ≠ 0)
    {g : spinGroup (quadPlus 4 F)} (hgT : g ∈ torusSub S) {x : Fin 4 ⊕ Fin 4 → F}
    (hx : x ∈ planeB ε hε h4) :
    spinAction (quadPlus 4 F) g (jOp ε x) = jOp ε (spinAction (quadPlus 4 F) g x) := by
  obtain ⟨t₀, ht₀, a, b, hb, hab⟩ := exists_regular_tor_zero hK hg hS hq h2 h2K
  have hcomm : g * t₀ = t₀ * g := torusSub_comm S hgT (tor_range_le_torusSub 0 ht₀)
  have hgx : spinAction (quadPlus 4 F) g x ∈ planeB ε hε h4 :=
    (torusSub_le_stabOf_eigSpace hK hg hS h2 h2K (-1) (-1) 1 hgT x).2 hx
  have h1 := LinearEquiv.congr_fun (congrArg (spinAction (quadPlus 4 F)) hcomm) x
  simp only [map_mul, LinearEquiv.mul_apply] at h1
  rw [hab x hx, map_sub, map_smul, map_smul, hab _ hgx] at h1
  have h3 : b • (spinAction (quadPlus 4 F) g (jOp ε x) - jOp ε (spinAction (quadPlus 4 F) g x)) =
      0 := by
    have : a • spinAction (quadPlus 4 F) g x - b • spinAction (quadPlus 4 F) g (jOp ε x) =
        a • spinAction (quadPlus 4 F) g x - b • jOp ε (spinAction (quadPlus 4 F) g x) := h1
    rw [smul_sub]
    have := sub_right_injective this
    rw [this]
    exact sub_self _
  have h4' := (smul_eq_zero.1 h3).resolve_left hb
  exact sub_eq_zero.1 h4'

theorem spinAction_mem_span_of_mem_range_zero (hS : ModelSpec S ε hε h4)
    {ρ : spinGroup (quadPlus 4 F)} (hρ : ρ ∈ (S.ι 0).range) {x : Fin 4 ⊕ Fin 4 → F}
    (hx : x ∈ (frame0 (F := F)).span) : spinAction (quadPlus 4 F) ρ x ∈ (frame0 (F := F)).span := by
  have hmem : spinAction (quadPlus 4 F) ρ ∈ (frame0 (F := F)).La.range := by
    have : spinAction (quadPlus 4 F) ρ ∈ (S.ι 0).range.map (spinAction (quadPlus 4 F)) :=
      ⟨ρ, hρ, rfl⟩
    rw [hS.map_range 0] at this
    exact this
  obtain ⟨M, hM⟩ := hmem
  obtain ⟨X, rfl⟩ := hx
  rw [← hM, Frame.La_apply_incl]
  exact ⟨_, rfl⟩

theorem mem_planeB_of_orth (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) {x : Fin 4 ⊕ Fin 4 → F}
    (hx : x ∈ (frame0 (F := F)).span)
    (h1 : polar (quadPlus 4 F) x (vecA1 F) = 0)
    (h2 : polar (quadPlus 4 F) x (jOp ε (vecA1 F)) = 0) : x ∈ planeB ε hε h4 := by
  obtain ⟨X, rfl⟩ := hx
  rw [vecA1, Frame.polar_incl_right, Frame.coords_incl] at h1
  rw [jOp_vecA1, Frame.polar_incl_right, Frame.coords_incl] at h2
  refine incl_mem_planeB_of_FJ' ε hε h4 ⟨?_, ?_⟩
  · simp at h1
    linear_combination h1
  · simp [Jm] at h2
    linear_combination h2

theorem polar_planeB_planeA (h2 : (2 : F) ≠ 0) {a b : Fin 4 ⊕ Fin 4 → F}
    (ha : a ∈ planeA ε hε h4) (hb : b ∈ planeB ε hε h4) :
    polar (quadPlus 4 F) b a = 0 := by
  have hO := (stdFrames ε hε h4 1).La_mem_orthogonalGroup (-1)
  have h1 := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hO b a
  have e1 : (stdFrames ε hε h4 1).La (-1) b = -b := by
    have := hb.2.1
    change (stdFrames ε hε h4 1).La (-1) b = (-1 : F) • b at this
    simpa using this
  have e2 : (stdFrames ε hε h4 1).La (-1) a = a := by
    have := ha.2.1
    change (stdFrames ε hε h4 1).La (-1) a = (1 : F) • a at this
    simpa using this
  rw [e1, e2, polar_neg_left] at h1
  have : (2 : F) * polar (quadPlus 4 F) b a = 0 := by linear_combination -h1
  exact (mul_eq_zero.1 this).resolve_left h2

theorem planeB_le_span (h2 : (2 : F) ≠ 0) {b : Fin 4 ⊕ Fin 4 → F} (hb : b ∈ planeB ε hε h4) :
    b ∈ (frame0 (F := F)).span :=
  ⟨_, ((mem_planeB_iff h2).1 hb).1.symm⟩

theorem planeA_le_span (h2 : (2 : F) ≠ 0) {a : Fin 4 ⊕ Fin 4 → F} (ha : a ∈ planeA ε hε h4) :
    a ∈ (frame0 (F := F)).span :=
  ⟨_, ((mem_planeA_iff h2).1 ha).1.symm⟩

theorem exists_tor_eq_on_span [Finite F] (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (hS : ModelSpec S ε hε h4) (hq : 5 ≤ p ^ f) (h2 : (2 : F) ≠ 0) (h2K : (2 : K) ≠ 0)
    {h : spinGroup (quadPlus 4 F)} (hh : h ∈ stabJ ε hε h4)
    (hW : ∀ x ∈ (frame0 (F := F)).span, spinAction (quadPlus 4 F) h x ∈ (frame0 (F := F)).span)
    (hJ : ∀ x ∈ (frame0 (F := F)).span,
      spinAction (quadPlus 4 F) h (jOp ε x) = jOp ε (spinAction (quadPlus 4 F) h x)) :
    ∃ t ∈ torusSub S, ∀ x ∈ (frame0 (F := F)).span,
      spinAction (quadPlus 4 F) t x = spinAction (quadPlus 4 F) h x := by
  obtain ⟨pr₁, hpr₁⟩ := exists_param_A h2 hh.1
  obtain ⟨t₀, ht₀, ht₀a⟩ := exists_tor_zero_of_param hK hg hS hq h2 h2K pr₁
  have ht₀R : t₀ ∈ (S.ι 0).range := by
    obtain ⟨y, rfl⟩ := ht₀
    exact ⟨_, rfl⟩
  have ht₀R' : t₀⁻¹ ∈ (S.ι 0).range := inv_mem ht₀R
  have hA1 : spinAction (quadPlus 4 F) h (vecA1 F) = spinAction (quadPlus 4 F) t₀ (vecA1 F) := by
    rw [hpr₁, ht₀a]
  have hinv : ∀ y, spinAction (quadPlus 4 F) t₀⁻¹ (spinAction (quadPlus 4 F) t₀ y) = y :=
      fun y => by
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hinv' : ∀ y, spinAction (quadPlus 4 F) t₀ (spinAction (quadPlus 4 F) t₀⁻¹ y) = y :=
      fun y => by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  set g₁ := t₀⁻¹ * h with hg₁
  have hg₁act : ∀ y, spinAction (quadPlus 4 F) g₁ y =
      spinAction (quadPlus 4 F) t₀⁻¹ (spinAction (quadPlus 4 F) h y) := fun y => by
    rw [hg₁, map_mul, LinearEquiv.mul_apply]
  have hc1 : ∀ x ∈ planeA ε hε h4, spinAction (quadPlus 4 F) g₁ x = x := by
    intro x hx
    obtain ⟨α, β, rfl⟩ := exists_comb_of_mem_planeA h2 hx
    have e1 : spinAction (quadPlus 4 F) g₁ (vecA1 F) = vecA1 F := by
      rw [hg₁act, hA1, hinv]
    have e2 : spinAction (quadPlus 4 F) g₁ (jOp ε (vecA1 F)) = jOp ε (vecA1 F) := by
      rw [hg₁act, hh.2 _ (vecA1_mem_planeA ε hε h4), hA1,
        ← spinAction_comm_jOp_of_mem_range_zero hS ht₀R, hinv]
    rw [map_add, map_smul, map_smul, e1, e2]
  have hc2 : ∀ x ∈ (frame0 (F := F)).span,
      spinAction (quadPlus 4 F) g₁ x ∈ (frame0 (F := F)).span := fun x hx => by
    rw [hg₁act]
    exact spinAction_mem_span_of_mem_range_zero hS ht₀R' (hW x hx)
  have hc3 : ∀ x ∈ (frame0 (F := F)).span, spinAction (quadPlus 4 F) g₁ (jOp ε x) =
      jOp ε (spinAction (quadPlus 4 F) g₁ x) := fun x hx => by
    rw [hg₁act, hg₁act, hJ x hx, spinAction_comm_jOp_of_mem_range_zero hS ht₀R']
  have hc4 : ∀ b ∈ planeB ε hε h4, spinAction (quadPlus 4 F) g₁ b ∈ planeB ε hε h4 := by
    intro b hb
    refine mem_planeB_of_orth ε hε h4 (hc2 b (planeB_le_span h2 hb)) ?_ ?_
    · have := polar_spinAction (quadPlus 4 F) g₁ b (vecA1 F)
      rw [hc1 _ (vecA1_mem_planeA ε hε h4)] at this
      rw [this]
      exact polar_planeB_planeA h2 (vecA1_mem_planeA ε hε h4) hb
    · have := polar_spinAction (quadPlus 4 F) g₁ b (jOp ε (vecA1 F))
      rw [hc1 _ (jOp_mem_planeA h2 (vecA1_mem_planeA ε hε h4))] at this
      rw [this]
      exact polar_planeB_planeA h2 (jOp_mem_planeA h2 (vecA1_mem_planeA ε hε h4)) hb
  obtain ⟨pr₂, hpr₂⟩ := exists_param_B_of_mem h2 (hc4 _ (vecB1_mem_planeB ε hε h4))
  obtain ⟨t₁, ht₁, ht₁b⟩ := exists_tor_one_of_param hK hg hS hq h2 h2K pr₂
  have ht₁R : t₁ ∈ (S.ι 1).range := by
    obtain ⟨y, rfl⟩ := ht₁
    exact ⟨_, rfl⟩
  have ht₁T : t₁ ∈ torusSub S := tor_range_le_torusSub 1 ht₁
  have hB1 : spinAction (quadPlus 4 F) t₁ (vecB1 F) = spinAction (quadPlus 4 F) g₁ (vecB1 F) := by
    rw [ht₁b, hpr₂]
  refine ⟨t₀ * t₁, mul_mem (tor_range_le_torusSub 0 ht₀) ht₁T, fun x hx => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_decomp_span (ε := ε) (hε := hε) (h4 := h4) h2 x
    ((Frame.mem_span_iff (frame0 (F := F))).1 hx)
  have hta : spinAction (quadPlus 4 F) t₁ a = a := spinAction_fix_planeA hS h2 (by decide) ht₁R a ha
  have htb : spinAction (quadPlus 4 F) t₁ b = spinAction (quadPlus 4 F) g₁ b := by
    obtain ⟨α, β, rfl⟩ := exists_comb_of_mem_planeB h2 hb
    rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul,
      torusSub_comm_jOp_B hK hg hS hq h2 h2K ht₁T (vecB1_mem_planeB ε hε h4),
      hc3 _ (planeB_le_span h2 (vecB1_mem_planeB ε hε h4)), hB1]
  have hga : spinAction (quadPlus 4 F) t₀ a = spinAction (quadPlus 4 F) h a := by
    have := hc1 a ha
    rw [hg₁act] at this
    calc spinAction (quadPlus 4 F) t₀ a =
        spinAction (quadPlus 4 F) t₀ (spinAction (quadPlus 4 F) t₀⁻¹
          (spinAction (quadPlus 4 F) h a)) := by rw [this]
      _ = spinAction (quadPlus 4 F) h a := hinv' _
  have hgb : spinAction (quadPlus 4 F) t₀ (spinAction (quadPlus 4 F) g₁ b) =
      spinAction (quadPlus 4 F) h b := by
    rw [hg₁act, hinv']
  rw [map_mul, LinearEquiv.mul_apply, map_add, hta, htb, map_add, hga, hgb, map_add]

end Orient

end CFSG.ClassicalInvolution.PhanP
