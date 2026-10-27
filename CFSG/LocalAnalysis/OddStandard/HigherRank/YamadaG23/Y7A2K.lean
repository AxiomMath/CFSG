module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2Ab2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2Ab3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2I
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2Hlp

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7aK_I_comm (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    ∀ x ∈ centIn (M2 c.s) c.s.fr.F, ∀ y ∈ centIn (M2 c.s) c.s.fr.F, x * y = y * x := by
  haveI : IsMulCommutative ↥(M3 c.s) := (y7a_M3_elemAbelian c hH).1
  intro x hx y hy
  exact congrArg Subtype.val (mul_comm' (⟨x, hF.2.2.1.2.2.1 hx⟩ : ↥(M3 c.s))
    ⟨y, hF.2.2.1.2.2.1 hy⟩)

private lemma y7aK_F_le_I (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    c.s.fr.F ≤ centIn (M2 c.s) c.s.fr.F := by
  intro f hf
  exact Subgroup.mem_inf.mpr
    ⟨y54_B_le_M2 c.s (y54_F_le_B hH hf),
      Subgroup.mem_centralizer_iff.mpr (fun y hy => y54_F_comm hH y hy f hf)⟩

private lemma y7aK_W_cent_M (c : Ctx7 G L) (hH : F33Hyp c.s c.e) :
    ∀ x ∈ M2 c.s, ∀ w ∈ cen c.s.fr.B, x * w = w * x := by
  intro x hx w hw
  have h := y54_C2_cent_V (s := c.s) (e := c.e) hH x
    (y54_M2_le_C2 c.toCtx5 hH hx) w hw
  calc x * w = (x * w * x⁻¹) * x := by group
    _ = w * x := by rw [h]

private lemma y7aK_VF (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : V2 c.e ⊓ c.s.fr.F ≤ cen c.s.fr.B := by
  have h : V2 c.e ⊓ c.s.fr.F ≤ V2 c.e ⊓ c.s.fr.A := inf_le_inf_left _ (s3_F_le_A c.s)
  rwa [y7a_V2_inf_A c hH hF h71] at h

private lemma y7aK_cent_le_V2 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : ∀ x ∈ M2 c.s, (∀ y ∈ M2 c.s, x * y = y * x) → x ∈ V2 c.e := by
  intro x hxM2 hxcomm
  rw [y7a_V2_mem_iff c hH hF h71]
  have hxI : x ∈ centIn (M2 c.s) c.s.fr.F :=
    Subgroup.mem_inf.mpr ⟨hxM2, Subgroup.mem_centralizer_iff.mpr
      (fun f hf => (hxcomm f (y54_B_le_M2 c.s (y54_F_le_B hH hf))).symm)⟩
  exact ⟨h71.2.2.2.1 (hF.2.2.1.2.2.1 hxI),
    fun e he => hxcomm e (y54_B_le_M2 c.s (y56_E_le_B hH he)),
    fun f hf => hxcomm f (y54_B_le_M2 c.s (y54_F_le_B hH hf))⟩

private lemma y7aK_F_eq (c : Ctx7 G L) (hH : F33Hyp c.s c.e) :
    c.s.fr.F = cen c.s.fr.B ⊔ zpowers (c.s.fr.a₁ * c.s.fr.a₂) := by
  have hcen : cen c.s.fr.B = Subgroup.closure {c.s.fr.b₁ * c.s.fr.b₂, c.s.fr.z} :=
    hH.hLF.fact14.2.2.1.1
  rw [SFrame.F, hcen]
  rw [show ({c.s.fr.a₁ * c.s.fr.a₂, c.s.fr.b₁ * c.s.fr.b₂, c.s.fr.z} : Set G) =
      {c.s.fr.a₁ * c.s.fr.a₂} ∪ {c.s.fr.b₁ * c.s.fr.b₂, c.s.fr.z} by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]]
  rw [Subgroup.closure_union, Subgroup.zpowers_eq_closure, sup_comm]

private lemma y7aK_fpf_I (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    {k : G} (hkB : k ∈ normIn L c.s.fr.B)
    (hkfix : ∀ v ∈ cen c.s.fr.B, k * v * k⁻¹ = v → v = 1) :
    ∀ x ∈ centIn (M2 c.s) c.s.fr.F, k * x * k⁻¹ * x⁻¹ ∈ c.s.fr.F → x ∈ c.s.fr.F := by
  have hkL : k ∈ L := (Subgroup.mem_inf.mp hkB).1
  have hkNormB : k ∈ Subgroup.normalizer (c.s.fr.B : Set G) := (Subgroup.mem_inf.mp hkB).2
  have hkH : k ∈ c.s.H := s3_L_le_H c.s hH.hS hkL
  have hkF_norm : k ∈ Subgroup.normalizer (c.s.fr.F : Set G) :=
    (Subgroup.mem_inf.mp (hH.hLF.fact18.2.1.2.1 hkB)).2
  have hkM : ∀ x ∈ M2 c.s, k * x * k⁻¹ ∈ M2 c.s := y54_M2_inv hH k ⟨hkH, hkNormB⟩
  refine y7a_fpf_I (I := centIn (M2 c.s) c.s.fr.F) (F := c.s.fr.F) (W := cen c.s.fr.B)
    (t := c.s.t) (k := k) (y7aK_I_comm c hH hF) (y7aK_F_le_I c hH hF) (y54_V_le_F hH)
    (s3_comm_t_of_mem_L c.s hkL) (fun f hf => y54_t_comm_F c.s f hf) ?_ ?_ ?_ ?_ hkfix
  · intro x hx
    exact y54_C2_comm_V c.toCtx5 hH x
      (y54_M2_le_C2 c.toCtx5 hH (Subgroup.mem_inf.mp hx).1) c.s.t (y54_t_mem_C2 hH)
  · intro x hx hxt
    have hxM3 : x ∈ M3 c.s := hF.2.2.1.2.2.1 hx
    have hxH : x ∈ c.s.H := Subgroup.mem_centralizer_singleton_iff.mpr hxt
    have hx' : x ∈ c.s.H ⊓ M3 c.s := ⟨hxH, hxM3⟩
    rwa [hF.2.2.1.1.2.1] at hx'
  · intro x hx
    exact y7a_conj_mem_centIn hkM hkF_norm hx
  · intro w hw
    exact y7a_conj_mem_cen hkNormB hw

private lemma y7aK_fpf_B (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    {k : G} (hkB : k ∈ normIn L c.s.fr.B) (hk3 : k ^ 3 = 1)
    (hkfix : ∀ v ∈ cen c.s.fr.B, k * v * k⁻¹ = v → v = 1) :
    ∀ b ∈ c.s.fr.B, k * b * k⁻¹ * b⁻¹ ∈ c.s.fr.F → b ∈ c.s.fr.F := by
  have hkNormB : k ∈ Subgroup.normalizer (c.s.fr.B : Set G) := (Subgroup.mem_inf.mp hkB).2
  have hkF_norm : k ∈ Subgroup.normalizer (c.s.fr.F : Set G) :=
    (Subgroup.mem_inf.mp (hH.hLF.fact18.2.1.2.1 hkB)).2
  have hkB' : ∀ b ∈ c.s.fr.B, k * b * k⁻¹ ∈ c.s.fr.B :=
    fun b hb => (Subgroup.mem_normalizer_iff.mp hkNormB b).mp hb
  have hkF : ∀ f ∈ c.s.fr.F, k * f * k⁻¹ ∈ c.s.fr.F :=
    fun f hf => (Subgroup.mem_normalizer_iff.mp hkF_norm f).mp hf
  have hkW : ∀ w ∈ cen c.s.fr.B, k * w * k⁻¹ ∈ cen c.s.fr.B :=
    fun w hw => y7a_conj_mem_cen hkNormB hw
  have hf0F : c.s.fr.a₁ * c.s.fr.a₂ ∈ c.s.fr.F := Subgroup.subset_closure (by simp)
  have hf0W : c.s.fr.a₁ * c.s.fr.a₂ ∉ cen c.s.fr.B := by
    intro h
    have hFW : c.s.fr.F = cen c.s.fr.B := by
      rw [y7aK_F_eq c hH, sup_eq_left.mpr (Subgroup.zpowers_le.mpr h)]
    have h1 : Nat.card ↥c.s.fr.F = Nat.card ↥(cen c.s.fr.B) := by rw [hFW]
    have hcF : Nat.card ↥c.s.fr.F = 8 := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]; exact (y54_F_isE3 hH).2
    rw [y54_V_card hH, hcF] at h1
    norm_num at h1
  have hWB : ∀ w ∈ cen c.s.fr.B, ∀ b ∈ c.s.fr.B, b * w = w * b :=
    fun w hw b hb => Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hw).2 b hb
  have hBB : ∀ b ∈ c.s.fr.B, ∀ b' ∈ c.s.fr.B, ⁅b, b'⁆ ∈ cen c.s.fr.B :=
    fun b hb b' hb' => y54_C2_comm_V c.toCtx5 hH b (y54_B_le_C2 hH hb) b' (y54_B_le_C2 hH hb')
  have hcentF : ∀ b ∈ c.s.fr.B, (∀ f ∈ c.s.fr.F, b * f = f * b) → b ∈ c.s.fr.F := by
    intro b hb hcomm
    have hbcent : b ∈ centIn L c.s.fr.F :=
      Subgroup.mem_inf.mpr ⟨s3_S_le_L c.s (s3_B_le_S c.s hb),
        Subgroup.mem_centralizer_iff.mpr (fun f hf => (hcomm f hf).symm)⟩
    simpa [hH.hLF.fact18.2.2.2.1, f3_zL_eq_bot hH] using hbcent
  exact y7a_fpf_B (B := c.s.fr.B) (F := c.s.fr.F) (W := cen c.s.fr.B) (k := k)
    (f₀ := c.s.fr.a₁ * c.s.fr.a₂) (y54_F_le_B hH) (y54_V_le_F hH) (y7aK_F_eq c hH)
    (y54_F_comm hH) (fun f hf => by simpa [pow_two] using y54_F_sq hH f hf)
    hf0F hf0W hWB hBB hcentF hkB' hkF hkW hk3 hkfix

private lemma y7aK_B_gen (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    {k : G} (hkB : k ∈ normIn L c.s.fr.B) (hk3 : k ^ 3 = 1)
    (hfpfB : ∀ b ∈ c.s.fr.B, k * b * k⁻¹ * b⁻¹ ∈ c.s.fr.F → b ∈ c.s.fr.F) :
    c.s.fr.B ≤ c.s.fr.F ⊔ c.s.fr.E ⊔ conjSub k c.s.fr.E := by
  have hkNormB : k ∈ Subgroup.normalizer (c.s.fr.B : Set G) := (Subgroup.mem_inf.mp hkB).2
  have hkF_norm : k ∈ Subgroup.normalizer (c.s.fr.F : Set G) :=
    (Subgroup.mem_inf.mp (hH.hLF.fact18.2.1.2.1 hkB)).2
  have hkB' : ∀ b ∈ c.s.fr.B, k * b * k⁻¹ ∈ c.s.fr.B :=
    fun b hb => (Subgroup.mem_normalizer_iff.mp hkNormB b).mp hb
  have hkF : ∀ f ∈ c.s.fr.F, k * f * k⁻¹ ∈ c.s.fr.F :=
    fun f hf => (Subgroup.mem_normalizer_iff.mp hkF_norm f).mp hf
  have hcF : Nat.card ↥c.s.fr.F = 8 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]; exact (y54_F_isE3 hH).2
  have hEF : ¬ c.s.fr.E ≤ c.s.fr.F := by
    intro h
    have hEFeq : c.s.fr.E ⊓ c.s.fr.F = cen c.s.fr.B := hH.hLF.fact14.2.2.2.1.2.2.2
    have h1 : Nat.card ↥c.s.fr.E = Nat.card ↥(cen c.s.fr.B) := by
      rw [← hEFeq, inf_eq_left.mpr h]
    have hcE : Nat.card ↥c.s.fr.E = 8 := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]; exact (y56_E_isE3 hH).2
    rw [y54_V_card hH, hcE] at h1
    norm_num at h1
  have hFn : ∀ b ∈ c.s.fr.B, ∀ f ∈ c.s.fr.F, b * f * b⁻¹ ∈ c.s.fr.F :=
    fun b hb f hf => (Subgroup.mem_normalizer_iff.mp (y54_S_le_N hH (s3_B_le_S c.s hb)).2 f).mp hf
  exact y7a_B_gen (B := c.s.fr.B) (F := c.s.fr.F) (E := c.s.fr.E) (k := k)
    (y54_card_B hH) hcF (y54_F_le_B hH) (y56_E_le_B hH) hEF hFn hkB' hkF hk3 hfpfB

theorem y7a_B_V2_comm (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : ∀ b ∈ c.s.fr.B, ∀ v ∈ V2 c.e, b * v = v * b := by
  obtain ⟨k, hkB, hk3, -, hkfix, -, -⟩ := f3_exists_k hH
  have hkL : k ∈ L := (Subgroup.mem_inf.mp hkB).1
  have hkNormB : k ∈ Subgroup.normalizer (c.s.fr.B : Set G) := (Subgroup.mem_inf.mp hkB).2
  have hkH : k ∈ c.s.H := s3_L_le_H c.s hH.hS hkL
  have hkF_norm : k ∈ Subgroup.normalizer (c.s.fr.F : Set G) :=
    (Subgroup.mem_inf.mp (hH.hLF.fact18.2.1.2.1 hkB)).2
  have hkM : ∀ x ∈ M2 c.s, k * x * k⁻¹ ∈ M2 c.s := y54_M2_inv hH k ⟨hkH, hkNormB⟩
  have hkW : ∀ w ∈ cen c.s.fr.B, k * w * k⁻¹ ∈ cen c.s.fr.B :=
    fun w hw => y7a_conj_mem_cen hkNormB hw
  have hcV : Nat.card ↥(V2 c.e) = 16 := by
    have h := (y7a_V2_data c hH hF h71).1
    rw [h]; norm_num
  have hVE : ∀ v ∈ V2 c.e, ∀ e ∈ c.s.fr.E, v * e = e * v :=
    fun v hv e he => ((y7a_V2_mem_iff c hH hF h71 v).mp hv).2.1 e he
  have hVF' : ∀ v ∈ V2 c.e, ∀ f ∈ c.s.fr.F, v * f = f * v :=
    fun v hv f hf => ((y7a_V2_mem_iff c hH hF h71 v).mp hv).2.2 f hf
  have hfpfB := y7aK_fpf_B c hH hF hkB hk3 hkfix
  have hcent := y7a_central_of_k (M := M2 c.s) (I := centIn (M2 c.s) c.s.fr.F)
    (B := c.s.fr.B) (V := V2 c.e) (E := c.s.fr.E) (F := c.s.fr.F) (W := cen c.s.fr.B) (k := k)
    (hMIB := le_of_eq hF.2.2.1.2.2.2.1) (hIM := inf_le_left) (hBM := y54_B_le_M2 c.s)
    (hVI := y7a_V2_le_I c hH hF h71) (hI := y7aK_I_comm c hH hF) (hFI := y7aK_F_le_I c hH hF)
    (hWF := y54_V_le_F hH) (hWV := y7a_cenB_le_V2 c hH hF h71) (hWM := y7aK_W_cent_M c hH)
    (hcI := y7a_card_I c hH hF) (hcV := hcV) (hcW := y54_V_card hH)
    (hVF := y7aK_VF c hH hF h71) (hVE := hVE) (hVF' := hVF') (hZV := y7aK_cent_le_V2 c hH hF h71)
    (hkM := hkM) (hkI := fun x hx => y7a_conj_mem_centIn hkM hkF_norm hx) (hkW := hkW)
    (hk3 := hk3) (hfpf := y7aK_fpf_I c hH hF hkB hkfix)
    (hBgen := y7aK_B_gen c hH hF hkB hk3 hfpfB)
  exact fun b hb v hv => hcent b (y54_B_le_M2 c.s hb) v hv

end CFSG.OddStandard.HigherRank.YamadaG23
