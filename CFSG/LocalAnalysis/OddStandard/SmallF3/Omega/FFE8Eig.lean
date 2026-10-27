module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem ffE8Eig_coe_mul_self {t : OGroup Q} (htt : t * t = 1) :
    (t : V ≃ₗ[ZMod 3] V) * (t : V ≃ₗ[ZMod 3] V) = 1 := by
  simpa using congrArg (fun e : OGroup Q => (e : V ≃ₗ[ZMod 3] V)) htt

private theorem ffE8Eig_apply_apply {t : OGroup Q} (htt : t * t = 1) (v : V) :
    (t : V ≃ₗ[ZMod 3] V) ((t : V ≃ₗ[ZMod 3] V) v) = v := by
  rw [← LinearEquiv.mul_apply, ffE8Eig_coe_mul_self htt, LinearEquiv.coe_one, id]

private theorem ffE8Eig_mul_apply (f g : OGroup Q) (v : V) :
    ((f * g : OGroup Q) : V ≃ₗ[ZMod 3] V) v =
      (f : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) v) := by
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply]

private theorem ffE8Eig_mem_commSp_of_comm {t e : OGroup Q} (ht : t * t = 1)
    (hcomm : t * e = e * t) {v : V} (hv : v ∈ commSp t) :
    (e : V ≃ₗ[ZMod 3] V) v ∈ commSp t := by
  rw [mem_commSp_iff ht]
  have hcoe : (t : V ≃ₗ[ZMod 3] V) * (e : V ≃ₗ[ZMod 3] V) =
      (e : V ≃ₗ[ZMod 3] V) * (t : V ≃ₗ[ZMod 3] V) := by
    simpa using congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V)) hcomm
  have hte : (t : V ≃ₗ[ZMod 3] V) ((e : V ≃ₗ[ZMod 3] V) v) =
      (e : V ≃ₗ[ZMod 3] V) ((t : V ≃ₗ[ZMod 3] V) v) := by
    rw [← LinearEquiv.mul_apply, hcoe, LinearEquiv.mul_apply]
  rw [hte, (mem_commSp_iff ht).mp hv, map_neg]

private theorem ffE8Eig_mem_fixSp_of_comm {s e : OGroup Q} (hcomm : s * e = e * s) {v : V}
    (hv : v ∈ fixSp s) : (e : V ≃ₗ[ZMod 3] V) v ∈ fixSp s := by
  rw [mem_fixSp_iff]
  have hcoe : (s : V ≃ₗ[ZMod 3] V) * (e : V ≃ₗ[ZMod 3] V) =
      (e : V ≃ₗ[ZMod 3] V) * (s : V ≃ₗ[ZMod 3] V) := by
    simpa using congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V)) hcomm
  have hse : (s : V ≃ₗ[ZMod 3] V) ((e : V ≃ₗ[ZMod 3] V) v) =
      (e : V ≃ₗ[ZMod 3] V) ((s : V ≃ₗ[ZMod 3] V) v) := by
    rw [← LinearEquiv.mul_apply, hcoe, LinearEquiv.mul_apply]
  rw [hse, (mem_fixSp_iff).mp hv]

private theorem ffE8Eig_sup_eq {e : OGroup Q} (he : e * e = 1) {S : Submodule (ZMod 3) V}
    (hS : ∀ v ∈ S, (e : V ≃ₗ[ZMod 3] V) v ∈ S) :
    S ⊓ fixSp e ⊔ S ⊓ commSp e = S := by
  apply le_antisymm (sup_le inf_le_left inf_le_left)
  intro v hv
  rw [Submodule.mem_sup]
  refine ⟨(2 : ZMod 3) • (v + (e : V ≃ₗ[ZMod 3] V) v), ?_,
    (2 : ZMod 3) • (v - (e : V ≃ₗ[ZMod 3] V) v), ?_, ?_⟩
  · rw [Submodule.mem_inf]
    exact ⟨S.smul_mem _ (S.add_mem hv (hS v hv)), by
      rw [mem_fixSp_iff, map_smul, map_add, ffE8Eig_apply_apply he v, add_comm]⟩
  · rw [Submodule.mem_inf]
    exact ⟨S.smul_mem _ (S.sub_mem hv (hS v hv)), by
      rw [mem_commSp_iff he, map_smul, map_sub, ffE8Eig_apply_apply he v, ← smul_neg, neg_sub]⟩
  · rw [← smul_add]
    have hsum : (v + (e : V ≃ₗ[ZMod 3] V) v) + (v - (e : V ≃ₗ[ZMod 3] V) v) =
        (2 : ZMod 3) • v := by
      rw [two_smul]; abel
    rw [hsum, smul_smul]
    have h4 : (2 : ZMod 3) * 2 = 1 := by decide
    rw [h4, one_smul]

theorem ffE8Eig_finrank_split {e : OGroup Q} (he : e * e = 1) {S : Submodule (ZMod 3) V}
    (hS : ∀ v ∈ S, (e : V ≃ₗ[ZMod 3] V) v ∈ S) :
    Module.finrank (ZMod 3) S =
      Module.finrank (ZMod 3) ↥(S ⊓ fixSp e) + Module.finrank (ZMod 3) ↥(S ⊓ commSp e) := by
  have hsup : S ⊓ fixSp e ⊔ S ⊓ commSp e = S := ffE8Eig_sup_eq he hS
  have hinf : S ⊓ fixSp e ⊓ (S ⊓ commSp e) = ⊥ := by
    refine le_antisymm ?_ bot_le
    refine (inf_le_inf inf_le_right inf_le_right).trans ?_
    rw [(isCompl_fixSp_commSp he).inf_eq_bot]
  have hmain := Submodule.finrank_sup_add_finrank_inf_eq (S ⊓ fixSp e) (S ⊓ commSp e)
  rw [hsup, hinf, finrank_bot, add_zero] at hmain
  exact hmain

theorem ffE8Eig_lines {t e₁ e₂ : OGroup Q} (ht : t * t = 1) (h₁ : e₁ * e₁ = 1)
    (h₂ : e₂ * e₂ = 1) (hte₁ : t * e₁ = e₁ * t) (hte₂ : t * e₂ = e₂ * t)
    (h₁₂ : e₁ * e₂ = e₂ * e₁) (hdt : invDim t = 4) (hd₁ : invDim e₁ = 2) (hd₂ : invDim e₂ = 2)
    (hd₃ : invDim (e₁ * e₂) = 2) (hle₁ : commSp e₁ ≤ commSp t) (hle₂ : commSp e₂ ≤ commSp t)
    (hle₃ : commSp (e₁ * e₂) ≤ commSp t) :
    ∃ f : Fin 4 → V, (∀ k, f k ∈ commSp t ∧ f k ≠ 0) ∧ LinearIndependent (ZMod 3) f ∧
      Submodule.span (ZMod 3) (Set.range f) = commSp t ∧
      (∀ k, (e₁ : V ≃ₗ[ZMod 3] V) (f k) = ![1, -1, 1, -1] k • f k) ∧
      (∀ k, (e₂ : V ≃ₗ[ZMod 3] V) (f k) = ![1, 1, -1, -1] k • f k) := by
  set W : Submodule (ZMod 3) V := commSp t with hWdef
  have hW4 : Module.finrank (ZMod 3) W = 4 := by rw [hWdef]; simpa only [invDim] using hdt
  have hle₁' : commSp e₁ ≤ W := by rw [hWdef]; exact hle₁
  have hle₂' : commSp e₂ ≤ W := by rw [hWdef]; exact hle₂
  have hle₃' : commSp (e₁ * e₂) ≤ W := by rw [hWdef]; exact hle₃
  have he₁W : ∀ v ∈ W, (e₁ : V ≃ₗ[ZMod 3] V) v ∈ W := by
    intro v hv
    rw [hWdef] at hv ⊢
    exact ffE8Eig_mem_commSp_of_comm ht hte₁ hv
  have he₂W : ∀ v ∈ W, (e₂ : V ≃ₗ[ZMod 3] V) v ∈ W := by
    intro v hv
    rw [hWdef] at hv ⊢
    exact ffE8Eig_mem_commSp_of_comm ht hte₂ hv
  have h₁₂sq : (e₁ * e₂) * (e₁ * e₂) = 1 := by rw [mul_assoc e₁ e₂ (e₁ * e₂),
    ← mul_assoc e₂ e₁ e₂, ← h₁₂, mul_assoc e₁ e₂ e₂, h₂, mul_one, h₁]
  set Wpp : Submodule (ZMod 3) V := W ⊓ fixSp e₁ ⊓ fixSp e₂ with hWpp
  set Wmp : Submodule (ZMod 3) V := W ⊓ commSp e₁ ⊓ fixSp e₂ with hWmp
  set Wpm : Submodule (ZMod 3) V := W ⊓ fixSp e₁ ⊓ commSp e₂ with hWpm
  set Wmm : Submodule (ZMod 3) V := W ⊓ commSp e₁ ⊓ commSp e₂ with hWmm
  have hS1 : ∀ v ∈ W ⊓ fixSp e₁, (e₂ : V ≃ₗ[ZMod 3] V) v ∈ W ⊓ fixSp e₁ := by
    intro v hv; rw [Submodule.mem_inf] at hv ⊢
    exact ⟨he₂W v hv.1, ffE8Eig_mem_fixSp_of_comm h₁₂ hv.2⟩
  have hS2 : ∀ v ∈ W ⊓ commSp e₁, (e₂ : V ≃ₗ[ZMod 3] V) v ∈ W ⊓ commSp e₁ := by
    intro v hv; rw [Submodule.mem_inf] at hv ⊢
    exact ⟨he₂W v hv.1, ffE8Eig_mem_commSp_of_comm h₁ h₁₂ hv.2⟩
  have hT1 : ∀ v ∈ W ⊓ fixSp e₂, (e₁ : V ≃ₗ[ZMod 3] V) v ∈ W ⊓ fixSp e₂ := by
    intro v hv; rw [Submodule.mem_inf] at hv ⊢
    exact ⟨he₁W v hv.1, ffE8Eig_mem_fixSp_of_comm h₁₂.symm hv.2⟩
  have hT2 : ∀ v ∈ W ⊓ commSp e₂, (e₁ : V ≃ₗ[ZMod 3] V) v ∈ W ⊓ commSp e₂ := by
    intro v hv; rw [Submodule.mem_inf] at hv ⊢
    exact ⟨he₁W v hv.1, ffE8Eig_mem_commSp_of_comm h₂ h₁₂.symm hv.2⟩
  have hWc1eq : W ⊓ commSp e₁ = commSp e₁ := le_antisymm inf_le_right (le_inf hle₁' le_rfl)
  have hWc1 : Module.finrank (ZMod 3) (W ⊓ commSp e₁ : Submodule (ZMod 3) V) = 2 := by
    rw [hWc1eq]; simpa only [invDim] using hd₁
  have hWf1 : Module.finrank (ZMod 3) (W ⊓ fixSp e₁ : Submodule (ZMod 3) V) = 2 := by
    have h := ffE8Eig_finrank_split (e := e₁) h₁ he₁W
    omega
  have hWc2eq : W ⊓ commSp e₂ = commSp e₂ := le_antisymm inf_le_right (le_inf hle₂' le_rfl)
  have hWc2 : Module.finrank (ZMod 3) (W ⊓ commSp e₂ : Submodule (ZMod 3) V) = 2 := by
    rw [hWc2eq]; simpa only [invDim] using hd₂
  have hWf2 : Module.finrank (ZMod 3) (W ⊓ fixSp e₂ : Submodule (ZMod 3) V) = 2 := by
    have h := ffE8Eig_finrank_split (e := e₂) h₂ he₂W
    omega
  have hsplit1 := ffE8Eig_finrank_split (e := e₂) h₂ hS1
  have hx1 : Module.finrank (ZMod 3) Wpp + Module.finrank (ZMod 3) Wpm = 2 := by
    rw [← hWpp, ← hWpm, hWf1] at hsplit1; exact hsplit1.symm
  have hsplit2 := ffE8Eig_finrank_split (e := e₂) h₂ hS2
  have hx2 : Module.finrank (ZMod 3) Wmp + Module.finrank (ZMod 3) Wmm = 2 := by
    rw [← hWmp, ← hWmm, hWc1] at hsplit2; exact hsplit2.symm
  have hsplit3 := ffE8Eig_finrank_split (e := e₁) h₁ hT1
  have hx3 : Module.finrank (ZMod 3) Wpp + Module.finrank (ZMod 3) Wmp = 2 := by
    have e3 : (W ⊓ fixSp e₂) ⊓ fixSp e₁ = Wpp := by rw [hWpp]; ac_rfl
    have e4 : (W ⊓ fixSp e₂) ⊓ commSp e₁ = Wmp := by rw [hWmp]; ac_rfl
    rw [e3, e4, hWf2] at hsplit3; exact hsplit3.symm
  have hsplit4 := ffE8Eig_finrank_split (e := e₁) h₁ hT2
  have hx4 : Module.finrank (ZMod 3) Wpm + Module.finrank (ZMod 3) Wmm = 2 := by
    have e5 : (W ⊓ commSp e₂) ⊓ fixSp e₁ = Wpm := by rw [hWpm]; ac_rfl
    have e6 : (W ⊓ commSp e₂) ⊓ commSp e₁ = Wmm := by rw [hWmm]; ac_rfl
    rw [e5, e6, hWc2] at hsplit4; exact hsplit4.symm
  have he₁stab3 : ∀ v ∈ commSp (e₁ * e₂), (e₁ : V ≃ₗ[ZMod 3] V) v ∈ commSp (e₁ * e₂) := by
    intro v hv
    rw [mem_commSp_iff h₁₂sq]
    have hv' : (e₁ : V ≃ₗ[ZMod 3] V) ((e₂ : V ≃ₗ[ZMod 3] V) v) = -v := by
      have h := (mem_commSp_iff h₁₂sq).mp hv
      rwa [ffE8Eig_mul_apply] at h
    have hcomm : (e₂ : V ≃ₗ[ZMod 3] V) ((e₁ : V ≃ₗ[ZMod 3] V) v) =
        (e₁ : V ≃ₗ[ZMod 3] V) ((e₂ : V ≃ₗ[ZMod 3] V) v) := by
      have hc := congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V)) h₁₂
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at hc
      rw [← LinearEquiv.mul_apply, ← hc, LinearEquiv.mul_apply]
    have h2v : (e₂ : V ≃ₗ[ZMod 3] V) v = -((e₁ : V ≃ₗ[ZMod 3] V) v) := by
      rw [← ffE8Eig_apply_apply h₁ ((e₂ : V ≃ₗ[ZMod 3] V) v), hv', map_neg]
    rw [ffE8Eig_mul_apply, hcomm, ← LinearEquiv.mul_apply, ffE8Eig_coe_mul_self h₁,
      LinearEquiv.coe_one, id]
    exact h2v
  have hsplit5 := ffE8Eig_finrank_split (e := e₁) h₁ he₁stab3
  have hc3 : Module.finrank (ZMod 3) (commSp (e₁ * e₂)) = 2 := by
    simpa only [invDim] using hd₃
  have e7 : commSp (e₁ * e₂) ⊓ fixSp e₁ = Wpm := by
    rw [hWpm]
    apply le_antisymm
    · intro v hv
      rw [Submodule.mem_inf] at hv ⊢
      refine ⟨⟨hle₃' hv.1, hv.2⟩, ?_⟩
      rw [mem_commSp_iff h₂]
      have hv' : (e₁ : V ≃ₗ[ZMod 3] V) ((e₂ : V ≃ₗ[ZMod 3] V) v) = -v := by
        have h := (mem_commSp_iff h₁₂sq).mp hv.1
        rwa [ffE8Eig_mul_apply] at h
      rw [← ffE8Eig_apply_apply h₁ ((e₂ : V ≃ₗ[ZMod 3] V) v), hv', map_neg,
        (mem_fixSp_iff).mp hv.2]
    · intro v hv
      rw [Submodule.mem_inf] at hv
      obtain ⟨⟨_, hvc1⟩, hvc2⟩ := hv
      rw [Submodule.mem_inf]
      refine ⟨?_, hvc1⟩
      rw [mem_commSp_iff h₁₂sq, ffE8Eig_mul_apply]
      have h2v : (e₂ : V ≃ₗ[ZMod 3] V) v = -v := (mem_commSp_iff h₂).mp hvc2
      have h1v : (e₁ : V ≃ₗ[ZMod 3] V) v = v := (mem_fixSp_iff).mp hvc1
      rw [h2v, map_neg, h1v]
  have e8 : commSp (e₁ * e₂) ⊓ commSp e₁ = Wmp := by
    rw [hWmp]
    apply le_antisymm
    · intro v hv
      rw [Submodule.mem_inf] at hv ⊢
      refine ⟨⟨hle₃' hv.1, hv.2⟩, ?_⟩
      rw [mem_fixSp_iff]
      have hv' : (e₁ : V ≃ₗ[ZMod 3] V) ((e₂ : V ≃ₗ[ZMod 3] V) v) = -v := by
        have h := (mem_commSp_iff h₁₂sq).mp hv.1
        rwa [ffE8Eig_mul_apply] at h
      have h1v : (e₁ : V ≃ₗ[ZMod 3] V) v = -v := (mem_commSp_iff h₁).mp hv.2
      rw [← ffE8Eig_apply_apply h₁ ((e₂ : V ≃ₗ[ZMod 3] V) v), hv', map_neg, h1v, neg_neg]
    · intro v hv
      rw [Submodule.mem_inf] at hv
      obtain ⟨⟨_, hvc1⟩, hvc2⟩ := hv
      rw [Submodule.mem_inf]
      refine ⟨?_, hvc1⟩
      rw [mem_commSp_iff h₁₂sq, ffE8Eig_mul_apply]
      have h2v : (e₂ : V ≃ₗ[ZMod 3] V) v = v := (mem_fixSp_iff).mp hvc2
      have h1v : (e₁ : V ≃ₗ[ZMod 3] V) v = -v := (mem_commSp_iff h₁).mp hvc1
      rw [h2v, h1v]
  have hx5 : Module.finrank (ZMod 3) Wpm + Module.finrank (ZMod 3) Wmp = 2 := by
    rw [e7, e8, hc3] at hsplit5; exact hsplit5.symm
  have hxpp : Module.finrank (ZMod 3) Wpp = 1 := by omega
  have hxmp : Module.finrank (ZMod 3) Wmp = 1 := by omega
  have hxpm : Module.finrank (ZMod 3) Wpm = 1 := by omega
  have hxmm : Module.finrank (ZMod 3) Wmm = 1 := by omega
  have hnepp : Wpp ≠ ⊥ := Submodule.one_le_finrank_iff.mp hxpp.ge
  have hnemm : Wmm ≠ ⊥ := Submodule.one_le_finrank_iff.mp hxmm.ge
  have hnepm : Wpm ≠ ⊥ := Submodule.one_le_finrank_iff.mp hxpm.ge
  have hnempm : Wmp ≠ ⊥ := Submodule.one_le_finrank_iff.mp hxmp.ge
  obtain ⟨f0, hf0mem, hf0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnepp
  obtain ⟨f1, hf1mem, hf1ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnempm
  obtain ⟨f2, hf2mem, hf2ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnepm
  obtain ⟨f3, hf3mem, hf3ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnemm
  let f : Fin 4 → V := ![f0, f1, f2, f3]
  have hfW : ∀ k, f k ∈ W := by
    intro k; fin_cases k
    · simpa [f] using hf0mem.1.1
    · simpa [f] using hf1mem.1.1
    · simpa [f] using hf2mem.1.1
    · simpa [f] using hf3mem.1.1
  have hfne : ∀ k, f k ≠ 0 := by
    intro k; fin_cases k
    · simpa [f] using hf0ne
    · simpa [f] using hf1ne
    · simpa [f] using hf2ne
    · simpa [f] using hf3ne
  have hWdecomp : W = Wpp ⊔ Wpm ⊔ (Wmp ⊔ Wmm) := by
    have h1 : W ⊓ fixSp e₁ = Wpp ⊔ Wpm := by
      rw [hWpp, hWpm]; exact (ffE8Eig_sup_eq (e := e₂) h₂ hS1).symm
    have h2 : W ⊓ commSp e₁ = Wmp ⊔ Wmm := by
      rw [hWmp, hWmm]; exact (ffE8Eig_sup_eq (e := e₂) h₂ hS2).symm
    rw [← h1, ← h2]
    exact (ffE8Eig_sup_eq (e := e₁) h₁ he₁W).symm
  have hspan_le : Submodule.span (ZMod 3) (Set.range f) ≤ W := by
    rw [Submodule.span_le]
    rintro v ⟨k, rfl⟩
    exact hfW k
  have hpp_le : Wpp ≤ Submodule.span (ZMod 3) (Set.range f) := by
    have hEq : Wpp = Submodule.span (ZMod 3) ({f0} : Set V) := by
      refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
      · rw [Submodule.span_le]; rintro x rfl; exact hf0mem
      · rw [finrank_span_singleton hf0ne, hxpp]
    rw [hEq]
    exact Submodule.span_mono (by rintro x (rfl : x = f0); exact ⟨0, by simp [f]⟩)
  have hmp_le : Wmp ≤ Submodule.span (ZMod 3) (Set.range f) := by
    have hEq : Wmp = Submodule.span (ZMod 3) ({f1} : Set V) := by
      refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
      · rw [Submodule.span_le]; rintro x rfl; exact hf1mem
      · rw [finrank_span_singleton hf1ne, hxmp]
    rw [hEq]
    exact Submodule.span_mono (by rintro x (rfl : x = f1); exact ⟨1, by simp [f]⟩)
  have hpm_le : Wpm ≤ Submodule.span (ZMod 3) (Set.range f) := by
    have hEq : Wpm = Submodule.span (ZMod 3) ({f2} : Set V) := by
      refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
      · rw [Submodule.span_le]; rintro x rfl; exact hf2mem
      · rw [finrank_span_singleton hf2ne, hxpm]
    rw [hEq]
    exact Submodule.span_mono (by rintro x (rfl : x = f2); exact ⟨2, by simp [f]⟩)
  have hmm_le : Wmm ≤ Submodule.span (ZMod 3) (Set.range f) := by
    have hEq : Wmm = Submodule.span (ZMod 3) ({f3} : Set V) := by
      refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
      · rw [Submodule.span_le]; rintro x rfl; exact hf3mem
      · rw [finrank_span_singleton hf3ne, hxmm]
    rw [hEq]
    exact Submodule.span_mono (by rintro x (rfl : x = f3); exact ⟨3, by simp [f]⟩)
  have hW_le_span : W ≤ Submodule.span (ZMod 3) (Set.range f) := by
    rw [hWdecomp]; exact sup_le (sup_le hpp_le hpm_le) (sup_le hmp_le hmm_le)
  have hspan : Submodule.span (ZMod 3) (Set.range f) = W := le_antisymm hspan_le hW_le_span
  have hli : LinearIndependent (ZMod 3) f := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    change Fintype.card (Fin 4) = Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range f))
    rw [Fintype.card_fin, hspan, hW4]
  have hsign₁ : ∀ k, (e₁ : V ≃ₗ[ZMod 3] V) (f k) = ![1, -1, 1, -1] k • f k := by
    intro k; fin_cases k
    · have h : (e₁ : V ≃ₗ[ZMod 3] V) f0 = f0 := (mem_fixSp_iff).mp hf0mem.1.2; simpa [f, h]
    · have h : (e₁ : V ≃ₗ[ZMod 3] V) f1 = -f1 := (mem_commSp_iff h₁).mp hf1mem.1.2
      simpa [f, h]
    · have h : (e₁ : V ≃ₗ[ZMod 3] V) f2 = f2 := (mem_fixSp_iff).mp hf2mem.1.2; simpa [f, h]
    · have h : (e₁ : V ≃ₗ[ZMod 3] V) f3 = -f3 := (mem_commSp_iff h₁).mp hf3mem.1.2
      simpa [f, h]
  have hsign₂ : ∀ k, (e₂ : V ≃ₗ[ZMod 3] V) (f k) = ![1, 1, -1, -1] k • f k := by
    intro k; fin_cases k
    · have h : (e₂ : V ≃ₗ[ZMod 3] V) f0 = f0 := (mem_fixSp_iff).mp hf0mem.2; simpa [f, h]
    · have h : (e₂ : V ≃ₗ[ZMod 3] V) f1 = f1 := (mem_fixSp_iff).mp hf1mem.2; simpa [f, h]
    · have h : (e₂ : V ≃ₗ[ZMod 3] V) f2 = -f2 := (mem_commSp_iff h₂).mp hf2mem.2
      simpa [f, h]
    · have h : (e₂ : V ≃ₗ[ZMod 3] V) f3 = -f3 := (mem_commSp_iff h₂).mp hf3mem.2
      simpa [f, h]
  exact ⟨f, fun k => ⟨hfW k, hfne k⟩, hli, hspan, hsign₁, hsign₂⟩

end CFSG.OddStandard.SmallF3.Omega
