module

public import CFSG.Certificates.Kernel.A3E6.Glue
public import CFSG.Certificates.Kernel.ThDemp.ChainEx

public section

namespace CFSG.StandardType.LieCore.A3E6K

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType CFSG.StandardType.GGFinModel
open CFSG.LieType.Steinberg.Adjoint (iform iform_comm iform_add_left iform_add_right
  iform_smul_left iform_smul_right iform_sub_left iform_sub_right iform_self_pos
  iform_self_of_isRoot iform_sq_lt)
open Matrix

structure Frame where
  p : E6V
  q : E6V
  r : E6V
  b₀ : E6V
  b₁ : E6V
  v : E6V
  A : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ

@[expose] def Frame.col (f : Frame) : Fin 6 → E6V := ![f.p, f.q, f.r, f.b₀, f.b₁, f.v]

@[expose] def Frame.B (f : Frame) : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  Matrix.of fun i j => f.col j i

@[expose] def Frame.perp (f : Frame) : Set E6V :=
  {γ | IsRoot Tag.E6 γ ∧ iform γ f.b₀ = 0 ∧ iform γ f.b₁ = 0}


structure FrameFacts (f : Frame) : Prop where
  hp : IsRoot Tag.E6 f.p
  hq : IsRoot Tag.E6 f.q
  hr : IsRoot Tag.E6 f.r
  hb₀ : IsRoot Tag.E6 f.b₀
  hb₁ : IsRoot Tag.E6 f.b₁
  hbb : iform f.b₀ f.b₁ = 0
  perp_iff : ∀ γ, IsRoot Tag.E6 γ →
    ((iform γ f.p = 0 ∧ iform γ f.q = 0 ∧ iform γ f.r = 0) ↔
      (γ = f.b₀ ∨ γ = -f.b₀ ∨ γ = f.b₁ ∨ γ = -f.b₁))
  perp_card : f.perp.ncard = 12
  vp : iform f.v f.p = 0
  vq : iform f.v f.q = 0
  vr : iform f.v f.r = 0
  vb₀ : iform f.v f.b₀ = 0
  vb₁ : iform f.v f.b₁ = 0
  hBA : f.B * f.A = (8 : ℤ) • (1 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ)

@[expose] def Cover (Fs : Set Frame) : Prop :=
  ∀ i j k : E6V, IsRoot Tag.E6 i → IsRoot Tag.E6 j → IsRoot Tag.E6 k → IsChain i j k →
    ∃ f ∈ Fs, (iform i f.b₀ = 0 ∧ iform i f.b₁ = 0) ∧ (iform j f.b₀ = 0 ∧ iform j f.b₁ = 0) ∧
      (iform k f.b₀ = 0 ∧ iform k f.b₁ = 0)

@[expose] def Fixes (f : Frame) (z : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) : Prop :=
  z *ᵥ f.p = f.p ∧ z *ᵥ f.q = f.q ∧ z *ᵥ f.r = f.r

@[expose] def ColImages (f : Frame) (z : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ)
    (sw : Bool) (e₀ e₁ e₂ : ℤ) : Prop :=
  (e₀ = 1 ∨ e₀ = -1) ∧ (e₁ = 1 ∨ e₁ = -1) ∧ (e₂ = 1 ∨ e₂ = -1) ∧
    z *ᵥ f.b₀ = e₀ • (if sw then f.b₁ else f.b₀) ∧
    z *ᵥ f.b₁ = e₁ • (if sw then f.b₀ else f.b₁) ∧ z *ᵥ f.v = e₂ • f.v

@[expose] def rr : E6V := ![4, 3, 5, 6, 4, 2]

@[expose] def TwFacts (f : Frame) : Prop :=
  ∀ (z : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) (sw : Bool) (e₀ e₁ e₂ : ℤ),
    Fixes f z → ColImages f z sw e₀ e₁ e₂ → (∀ i, (3 : ℤ) ∣ (z *ᵥ rr) i + rr i) →
    ∃ g : E6V, IsRoot Tag.E6 g ∧ ¬(iform g f.b₀ = 0 ∧ iform g f.b₁ = 0) ∧
      (iform f.p g ≠ 0 ∨ iform f.q g ≠ 0 ∨ iform f.r g ≠ 0) ∧
      ∀ c : Fin Tag.E6.rank → ZMod 3, (∀ γ, ggLiePair (z *ᵥ γ) c = -ggLiePair γ c) →
        ggLiePair f.p c = 0 → ggLiePair f.q c = 0 → ggLiePair f.r c = 0 → ggLiePair g c = 0

@[expose] def UnFacts (f : Frame) : Prop :=
  ∀ (z : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) (sw : Bool) (e₀ e₁ e₂ : ℤ),
    Fixes f z → ColImages f z sw e₀ e₁ e₂ → (∀ i, (3 : ℤ) ∣ (z *ᵥ rr) i - rr i) →
    sw = false ∧ e₂ = 1

@[expose] def comb (i j k : E6V) (t : ℤ × ℤ × ℤ) : E6V := t.1 • i + t.2.1 • j + t.2.2 • k

@[expose] def coeffs : List (ℤ × ℤ × ℤ) :=
  [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (0, 1, 1), (1, 1, 1),
    (-1, 0, 0), (0, -1, 0), (0, 0, -1), (-1, -1, 0), (0, -1, -1), (-1, -1, -1)]

theorem coeffs_nodup : coeffs.Nodup := by decide

theorem coeffs_sum : ∀ t ∈ coeffs, ∃ t₁ ∈ coeffs, ∃ t₂ ∈ coeffs, t = t₁ + t₂ := by decide

theorem comb_add (i j k : E6V) (t₁ t₂ : ℤ × ℤ × ℤ) :
    comb i j k (t₁ + t₂) = comb i j k t₁ + comb i j k t₂ := by
  simp only [comb, Prod.fst_add, Prod.snd_add, add_smul]
  abel

theorem iform_comb_left (i j k : E6V) (t : ℤ × ℤ × ℤ) (y : E6V) :
    iform (comb i j k t) y = t.1 * iform i y + t.2.1 * iform j y + t.2.2 * iform k y := by
  simp only [comb, iform_add_left, iform_smul_left]

theorem comb_injective {i j k : E6V} (hi : IsRoot Tag.E6 i) (hj : IsRoot Tag.E6 j)
    (hk : IsRoot Tag.E6 k) (hch : IsChain i j k) : Function.Injective (comb i j k) := by
  obtain ⟨hij, hjk, hik⟩ := hch
  have hii := iform_root_self hi
  have hjj := iform_root_self hj
  have hkk := iform_root_self hk
  have hji : iform j i = -1 := by rw [iform_comm]; exact hij
  have hkj : iform k j = -1 := by rw [iform_comm]; exact hjk
  have hki : iform k i = 0 := by rw [iform_comm]; exact hik
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have e1 := congrArg (fun x => iform x i) h
  have e2 := congrArg (fun x => iform x j) h
  have e3 := congrArg (fun x => iform x k) h
  simp only [iform_comb_left, hii, hjj, hkk, hij, hjk, hik, hji, hkj, hki] at e1 e2 e3
  have ha : a = a' := by linarith
  have hb : b = b' := by linarith
  have hc : c = c' := by linarith
  rw [ha, hb, hc]

section Comp

variable {c₁ c₂ : Fin Tag.E6.rank → ZMod 3} {m : E6V}

theorem comb_mem_comp {i j k : E6V} (hi : i ∈ a3Comp Tag.E6 c₁ c₂ m)
    (hj : j ∈ a3Comp Tag.E6 c₁ c₂ m) (hk : k ∈ a3Comp Tag.E6 c₁ c₂ m) (hch : IsChain i j k) :
    ∀ t ∈ coeffs, comb i j k t ∈ a3Comp Tag.E6 c₁ c₂ m := by
  obtain ⟨hij, hjk, hik⟩ := hch
  have h4 := add_mem_comp hi hj hij
  have h5 := add_mem_comp hj hk hjk
  have h6 := add_mem_comp h4 hk (by rw [iform_add_left, hik, hjk, zero_add])
  intro t ht
  simp only [coeffs, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · convert hi using 1; simp [comb]
  · convert hj using 1; simp [comb]
  · convert hk using 1; simp [comb]
  · convert h4 using 1; simp [comb]
  · convert h5 using 1; simp [comb]
  · convert h6 using 1; simp [comb]
  · convert neg_mem_comp hi using 1; simp [comb]
  · convert neg_mem_comp hj using 1; simp [comb]
  · convert neg_mem_comp hk using 1; simp [comb]
  · convert neg_mem_comp h4 using 1; simp [comb]; abel
  · convert neg_mem_comp h5 using 1; simp [comb]; abel
  · convert neg_mem_comp h6 using 1; simp [comb]; abel

theorem ncard_coeffs : {t | t ∈ coeffs}.ncard = 12 := by
  have h : {t | t ∈ coeffs} = (coeffs.toFinset : Set (ℤ × ℤ × ℤ)) := by
    ext t
    simp
  rw [h, Set.ncard_coe_finset, List.toFinset_card_of_nodup coeffs_nodup]
  rfl

theorem comp_eq_frame {Fs : Set Frame} (hcov : Cover Fs) (hfr : ∀ f ∈ Fs, FrameFacts f)
    (hm : m ∈ a3Ker Tag.E6 c₁ c₂) (hn : (a3Comp Tag.E6 c₁ c₂ m).ncard = 12) :
    ∃ f ∈ Fs, a3Comp Tag.E6 c₁ c₂ m = f.perp ∧
      (∃ ψ₀ ∈ a3Comp Tag.E6 c₁ c₂ m, ∃ ψ₁ ∈ a3Comp Tag.E6 c₁ c₂ m, iform ψ₀ ψ₁ = 0) ∧
      (∀ ψ ∈ a3Comp Tag.E6 c₁ c₂ m, ∃ x ∈ a3Comp Tag.E6 c₁ c₂ m,
        ∃ y ∈ a3Comp Tag.E6 c₁ c₂ m, ψ = x + y) := by
  obtain ⟨i, hi, j, hj, k, hk, hch⟩ := exists_chain hm hn
  obtain ⟨f, hf, hiβ, hjβ, hkβ⟩ := hcov i j k hi.1.1 hj.1.1 hk.1.1 hch
  have hff := hfr f hf
  set T : Set E6V := comb i j k '' {t | t ∈ coeffs} with hT
  have hTC : T ⊆ a3Comp Tag.E6 c₁ c₂ m := by
    rintro _ ⟨t, ht, rfl⟩
    exact comb_mem_comp hi hj hk hch t ht
  have hTP : T ⊆ f.perp := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨(hTC ⟨t, ht, rfl⟩).1.1, ?_, ?_⟩
    · rw [iform_comb_left, hiβ.1, hjβ.1, hkβ.1]
      ring
    · rw [iform_comb_left, hiβ.2, hjβ.2, hkβ.2]
      ring
  have hTn : T.ncard = 12 := by
    rw [hT, Set.ncard_image_of_injective _ (comb_injective hi.1.1 hj.1.1 hk.1.1 hch),
      ncard_coeffs]
  have hCT : T = a3Comp Tag.E6 c₁ c₂ m :=
    Set.eq_of_subset_of_ncard_le hTC (by omega) (Set.finite_of_ncard_ne_zero (by omega))
  have hPT : T = f.perp :=
    Set.eq_of_subset_of_ncard_le hTP (by rw [hff.perp_card]; omega)
      (Set.finite_of_ncard_ne_zero (by rw [hff.perp_card]; omega))
  refine ⟨f, hf, hCT.symm.trans hPT, ⟨i, hi, k, hk, hch.2.2⟩, ?_⟩
  rw [← hCT]
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := coeffs_sum t ht
  exact ⟨comb i j k t₁, ⟨t₁, ht₁, rfl⟩, comb i j k t₂, ⟨t₂, ht₂, rfl⟩, comb_add i j k t₁ t₂⟩

end Comp

theorem Frame.mulVec_eq_sum (f : Frame) (u : E6V) : f.B *ᵥ u = ∑ j : Fin 6, u j • f.col j := by
  ext i
  simp [Frame.B, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rfl

theorem Frame.B_mulVec_A (f : Frame) (hf : FrameFacts f) (u : E6V) :
    f.B *ᵥ (f.A *ᵥ u) = (8 : ℤ) • u := by
  rw [Matrix.mulVec_mulVec, hf.hBA]
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

theorem eq_zero_of_perp {f : Frame} (hf : FrameFacts f) {y : E6V}
    (h : ∀ j : Fin 6, iform y (f.col j) = 0) : y = 0 := by
  have hB : ∀ u, iform y (f.B *ᵥ u) = 0 := by
    intro u
    rw [Frame.mulVec_eq_sum, iform_finset_sum_right]
    exact Finset.sum_eq_zero fun j _ => by rw [iform_smul_right, h j, mul_zero]
  have hk : ∀ k : Fin Tag.E6.rank, iform y (Pi.single k 1) = 0 := by
    intro k
    have := hB (f.A *ᵥ Pi.single k 1)
    rw [Frame.B_mulVec_A f hf, iform_smul_right] at this
    omega
  have hyy : iform y y = 0 := by
    have hy : y = ∑ k, y k • (Pi.single k 1 : E6V) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    have h0 : iform y (∑ k, y k • (Pi.single k 1 : E6V)) = 0 := by
      rw [iform_finset_sum_right]
      exact Finset.sum_eq_zero fun k _ => by rw [iform_smul_right, hk k, mul_zero]
    rwa [← hy] at h0
  by_contra hne
  exact (iform_self_pos hne).ne' hyy

theorem perp_of_frame {f : Frame} (hf : FrameFacts f) {b : E6V}
    (hb : b = f.b₀ ∨ b = -f.b₀ ∨ b = f.b₁ ∨ b = -f.b₁) :
    iform b f.p = 0 ∧ iform b f.q = 0 ∧ iform b f.r = 0 := by
  have hroot : IsRoot Tag.E6 b := by
    rcases hb with rfl | rfl | rfl | rfl
    exacts [hf.hb₀, IsRoot.neg hf.hb₀, hf.hb₁, IsRoot.neg hf.hb₁]
  exact (hf.perp_iff b hroot).mpr hb

theorem images_of_fix {f : Frame} (hf : FrameFacts f) (L : E6V →ₗ[ℤ] E6V)
    (hroot : ∀ γ, IsRoot Tag.E6 γ → IsRoot Tag.E6 (L γ))
    (hform : ∀ x y, iform (L x) (L y) = iform x y)
    (hfix : L f.p = f.p ∧ L f.q = f.q ∧ L f.r = f.r) :
    ∃ (sw : Bool) (e₀ e₁ e₂ : ℤ), (e₀ = 1 ∨ e₀ = -1) ∧ (e₁ = 1 ∨ e₁ = -1) ∧
      (e₂ = 1 ∨ e₂ = -1) ∧ L f.b₀ = e₀ • (if sw then f.b₁ else f.b₀) ∧
      L f.b₁ = e₁ • (if sw then f.b₀ else f.b₁) ∧ L f.v = e₂ • f.v := by
  obtain ⟨hLp, hLq, hLr⟩ := hfix
  have hLb : ∀ b, (b = f.b₀ ∨ b = f.b₁) →
      (L b = f.b₀ ∨ L b = -f.b₀ ∨ L b = f.b₁ ∨ L b = -f.b₁) := by
    intro b hb
    have hbr : IsRoot Tag.E6 b := by
      rcases hb with rfl | rfl
      exacts [hf.hb₀, hf.hb₁]
    have hperp := perp_of_frame hf (b := b) (by rcases hb with rfl | rfl <;> simp)
    refine (hf.perp_iff (L b) (hroot b hbr)).mp ⟨?_, ?_, ?_⟩
    · rw [← hLp, hform]; exact hperp.1
    · rw [← hLq, hform]; exact hperp.2.1
    · rw [← hLr, hform]; exact hperp.2.2
  have h00 := iform_root_self hf.hb₀
  have h11 := iform_root_self hf.hb₁
  have h01 := hf.hbb
  have h10 : iform f.b₁ f.b₀ = 0 := by rw [iform_comm]; exact h01
  have horth : iform (L f.b₀) (L f.b₁) = 0 := by rw [hform]; exact h01
  obtain ⟨sw, e₀, e₁, he₀, he₁, hL0, hL1⟩ : ∃ (sw : Bool) (e₀ e₁ : ℤ), (e₀ = 1 ∨ e₀ = -1) ∧
      (e₁ = 1 ∨ e₁ = -1) ∧ L f.b₀ = e₀ • (if sw then f.b₁ else f.b₀) ∧
      L f.b₁ = e₁ • (if sw then f.b₀ else f.b₁) := by
    rcases hLb f.b₀ (Or.inl rfl) with h0 | h0 | h0 | h0 <;>
      rcases hLb f.b₁ (Or.inr rfl) with h1 | h1 | h1 | h1 <;>
      rw [h0, h1] at horth <;>
      simp only [iform_neg_left, iform_neg_right, h00, h11, h01, h10, neg_neg, neg_zero] at horth <;>
      norm_num at horth
    · exact ⟨false, 1, 1, by norm_num, by norm_num, by simp [h0], by simp [h1]⟩
    · exact ⟨false, 1, -1, by norm_num, by norm_num, by simp [h0], by simp [h1]⟩
    · exact ⟨false, -1, 1, by norm_num, by norm_num, by simp [h0], by simp [h1]⟩
    · exact ⟨false, -1, -1, by norm_num, by norm_num, by simp [h0], by simp [h1]⟩
    · exact ⟨true, 1, 1, by norm_num, by norm_num, by simp [h0], by simp [h1]⟩
    · exact ⟨true, 1, -1, by norm_num, by norm_num, by simp [h0], by simp [h1]⟩
    · exact ⟨true, -1, 1, by norm_num, by norm_num, by simp [h0], by simp [h1]⟩
    · exact ⟨true, -1, -1, by norm_num, by norm_num, by simp [h0], by simp [h1]⟩
  set x := L f.v with hx
  have hxp : iform x f.p = 0 := by rw [hx, ← hLp, hform]; exact hf.vp
  have hxq : iform x f.q = 0 := by rw [hx, ← hLq, hform]; exact hf.vq
  have hxr : iform x f.r = 0 := by rw [hx, ← hLr, hform]; exact hf.vr
  have hxL0 : iform x (L f.b₀) = 0 := by rw [hx, hform]; exact hf.vb₀
  have hxL1 : iform x (L f.b₁) = 0 := by rw [hx, hform]; exact hf.vb₁
  have hsign : ∀ e : ℤ, (e = 1 ∨ e = -1) → ∀ b, iform x (e • b) = 0 → iform x b = 0 := by
    intro e he b h
    rw [iform_smul_right] at h
    rcases he with rfl | rfl <;> linarith
  have hxb : iform x f.b₀ = 0 ∧ iform x f.b₁ = 0 := by
    rw [hL0] at hxL0
    rw [hL1] at hxL1
    cases sw
    · exact ⟨hsign e₀ he₀ _ hxL0, hsign e₁ he₁ _ hxL1⟩
    · exact ⟨hsign e₁ he₁ _ hxL1, hsign e₀ he₀ _ hxL0⟩
  set s := iform f.v f.v with hs
  set t := iform f.v x with ht
  have hxx : iform x x = s := by rw [hx, hform]
  have hy : s • x - t • f.v = 0 := by
    refine eq_zero_of_perp hf fun j => ?_
    fin_cases j <;>
      simp only [Frame.col, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
        Matrix.cons_val_zero, Matrix.cons_val_one, iform_sub_left, iform_smul_left, hxp, hxq,
        hxr, hxb.1, hxb.2, hf.vp, hf.vq, hf.vr, hf.vb₀, hf.vb₁, mul_zero, sub_zero]
    rw [iform_comm x f.v, ← ht, ← hs]
    ring
  have hsx : s • x = t • f.v := sub_eq_zero.mp hy
  by_cases hv0 : f.v = 0
  · refine ⟨sw, e₀, e₁, 1, he₀, he₁, Or.inl rfl, hL0, hL1, ?_⟩
    rw [hx, hv0, map_zero, smul_zero]
  have hspos : 0 < s := iform_self_pos hv0
  have hst : s * s * s = t * t * s := by
    have := congrArg (fun u => iform u u) hsx
    simp only [iform_smul_left, iform_smul_right, hxx] at this
    rw [← hs] at this
    linarith
  have hst' : (s - t) * (s + t) = 0 := by
    have : (s * s - t * t) * s = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hspos.ne'
  have hs0 : s ≠ 0 := hspos.ne'
  rcases mul_eq_zero.mp hst' with h | h
  · refine ⟨sw, e₀, e₁, 1, he₀, he₁, Or.inl rfl, hL0, hL1, ?_⟩
    have htv : t = s := by linarith
    rw [htv] at hsx
    rw [one_smul]
    exact smul_right_injective E6V hs0 hsx
  · refine ⟨sw, e₀, e₁, -1, he₀, he₁, Or.inr rfl, hL0, hL1, ?_⟩
    have htv : t = -s := by linarith
    rw [htv, neg_smul, ← smul_neg] at hsx
    rw [neg_one_smul]
    exact smul_right_injective E6V hs0 hsx

end CFSG.StandardType.LieCore.A3E6K
