module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldDef

public section

open CFSG.GH74.BNPair
open scoped Pointwise

namespace CFSG.GH74.GLS.SP

variable {X : Type*} [Group X]
variable {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X} {root : ℤ → Subgroup X}

private theorem bruhat_rt_0 : Rt 6 0 = 1 := by decide
private theorem bruhat_rt_4 : Rt 6 4 = 5 := by decide
private theorem bruhat_rt_10 : Rt 6 10 = -5 := by decide
private theorem bruhat_rt_m6 : Rt 6 (((6 : ℕ) : ℤ) - 2 - 10) = -1 := by decide
private theorem bruhat_rt_m2 : Rt 6 (((6 : ℕ) : ℤ) - 4 - 4) = -5 := by decide
private theorem bruhat_rt_2 : Rt 6 (((6 : ℕ) : ℤ) - 2 - 0) = 5 := by decide

private theorem bruhat_foldIdx_one : foldIdx 1 = 1 := by decide
private theorem bruhat_foldIdx_neg_one : foldIdx (-1) = -1 := by decide
private theorem bruhat_foldIdx_three : foldIdx ((3 : ℕ) : ℤ) = 5 := by decide
private theorem bruhat_foldIdx_neg_three : foldIdx (-((3 : ℕ) : ℤ)) = -5 := by decide

theorem bruhat_unique (R : RGD2 6 H r₁ r₂ U root) {Xp Xm : Subgroup X} (hXp : Xp ≤ U)
    (hXm : Xm ≤ negGen 6 root) (hH : ∀ h ∈ H, ∀ x ∈ Xp, h * x * h⁻¹ ∈ Xp)
    {r : X} (hr : ∀ x ∈ Xp, r * x * r⁻¹ ∈ Xm) {a a' b b' h h' : X}
    (ha : a ∈ Xp) (ha' : a' ∈ Xp) (hb : b ∈ Xp) (hb' : b' ∈ Xp) (hh : h ∈ H) (hh' : h' ∈ H)
    (he : a * h * r * b = a' * h' * r * b') : a = a' ∧ h = h' ∧ b = b' := by
  have hu : a'⁻¹ * a ∈ Xp := Xp.mul_mem (Xp.inv_mem ha') ha
  have hz : r * (b' * b⁻¹) * r⁻¹ ∈ Xm := hr _ (Xp.mul_mem hb' (Xp.inv_mem hb))
  have h1 : h'⁻¹ * (a'⁻¹ * a) * h'⁻¹⁻¹ ∈ Xp := hH _ (H.inv_mem hh') _ hu
  rw [inv_inv] at h1
  have heq : r * (b' * b⁻¹) * r⁻¹ = (h'⁻¹ * (a'⁻¹ * a) * h') * (h'⁻¹ * h) := by
    have e2 : a * h = a' * h' * (r * (b' * b⁻¹) * r⁻¹) := by
      calc a * h = (a * h * r * b) * b⁻¹ * r⁻¹ := by group
        _ = (a' * h' * r * b') * b⁻¹ * r⁻¹ := by rw [he]
        _ = a' * h' * (r * (b' * b⁻¹) * r⁻¹) := by group
    calc r * (b' * b⁻¹) * r⁻¹ = (a' * h')⁻¹ * (a * h) := by rw [e2]; group
      _ = _ := by group
  have hz1 : r * (b' * b⁻¹) * r⁻¹ = 1 := by
    refine R.meet_one _ ?_ (hXm hz)
    rw [heq]
    exact (H ⊔ U).mul_mem ((le_sup_right : U ≤ H ⊔ U) (hXp h1))
      ((le_sup_left : H ≤ H ⊔ U) (H.mul_mem (H.inv_mem hh') hh))
  rw [heq] at hz1
  have hmem : h'⁻¹ * (a'⁻¹ * a) * h' ∈ U ⊓ H := by
    refine ⟨hXp h1, ?_⟩
    have : h'⁻¹ * (a'⁻¹ * a) * h' = (h'⁻¹ * h)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]; exact hz1
    rw [this]
    exact H.inv_mem (H.mul_mem (H.inv_mem hh') hh)
  rw [R.U_inf_H, Subgroup.mem_bot] at hmem
  have hmem2 : h'⁻¹ * h = 1 := by
    rw [hmem, one_mul] at hz1; exact hz1
  have hu1 : a'⁻¹ * a = 1 := by
    have : a'⁻¹ * a = h' * (h'⁻¹ * (a'⁻¹ * a) * h') * h'⁻¹ := by group
    rw [this, hmem]; group
  have hhh : h = h' := by
    have : h = h' * (h'⁻¹ * h) := by group
    rw [this, hmem2, mul_one]
  have haa : a = a' := by
    have : a = a' * (a'⁻¹ * a) := by group
    rw [this, hu1, mul_one]
  refine ⟨haa, hhh, ?_⟩
  have hz2 : r * (b' * b⁻¹) * r⁻¹ = 1 := by
    rw [heq, hmem, hmem2]; group
  have h3 : b' * b⁻¹ = 1 := by
    have h4 : r⁻¹ * (r * (b' * b⁻¹) * r⁻¹) * r = b' * b⁻¹ := by group
    rw [← h4, hz2]; group
  exact (mul_inv_eq_one.1 h3).symm

theorem bruhat_rank_alpha (R : RGD2 6 H r₁ r₂ U root) {y : X} (hy : y ∈ root (-5)) (hy1 : y ≠ 1) :
    y ∈ (root 5 : Set X) * (H : Set X) * {r₂ * r₁ * r₂⁻¹} * (root 5 : Set X) := by
  have hconj : r₂⁻¹ * y * r₂ ∈ root (-1) := by
    have h : r₂⁻¹ * y * r₂⁻¹⁻¹ ∈ root (Rt 6 (((6 : ℕ) : ℤ) - 2 - 10)) :=
      R.actsPos_inv_of_sq R.sq₂ R.actsPos_r₂ 10 y (by rw [bruhat_rt_10]; exact hy)
    rwa [inv_inv, bruhat_rt_m6] at h
  have hne : r₂⁻¹ * y * r₂ ≠ 1 := by
    intro h
    apply hy1
    have : y = r₂ * (r₂⁻¹ * y * r₂) * r₂⁻¹ := by group
    rw [this, h]; group
  obtain ⟨c, hc, b, hb, hcb⟩ := Set.mem_mul.1 (R.rank₁ _ hconj hne)
  obtain ⟨d, hd, r', hr', hdr⟩ := Set.mem_mul.1 hc
  obtain ⟨a, ha, h, hh, hah⟩ := Set.mem_mul.1 hd
  rw [Set.mem_singleton_iff] at hr'
  have hroot : ∀ z ∈ root 1, r₂ * z * r₂⁻¹ ∈ root 5 := fun z hz => by
    have h' : r₂ * z * r₂⁻¹ ∈ root (Rt 6 (((6 : ℕ) : ℤ) - 2 - 0)) :=
      R.actsPos_r₂ 0 z (by rw [bruhat_rt_0]; exact hz)
    rwa [bruhat_rt_2] at h'
  have hy2 : r₂ * a * r₂⁻¹ * (r₂ * h * r₂⁻¹) * (r₂ * r₁ * r₂⁻¹) * (r₂ * b * r₂⁻¹) = y := by
    have : a * h * r₁ * b = r₂⁻¹ * y * r₂ := by rw [← hcb, ← hdr, ← hah, hr']
    calc _ = r₂ * (a * h * r₁ * b) * r₂⁻¹ := by group
      _ = y := by rw [this]; group
  exact Set.mem_mul.2 ⟨_, Set.mem_mul.2 ⟨_, Set.mem_mul.2 ⟨_, hroot a ha, _,
    R.conj_H₂ h hh, rfl⟩, _, rfl, rfl⟩, _, hroot b hb, hy2⟩

theorem bruhat_assemble (R : RGD2 6 H r₁ r₂ U root) {φ : X ≃* X} {r r' : X} (hrN : r ∈ R.N)
    (hr' : r⁻¹ * r' ∈ H) (hφr' : φ r' = r') {A : Subgroup X} {a b h y : X} (ha : a ∈ A)
    (hb : b ∈ A) (hh : h ∈ H) (hφ : φ (h * r) = h * r) (hy : y = a * (h * r) * b) :
    y ∈ (A : Set X) * ((H ⊓ foldFix φ : Subgroup X) : Set X) * {r'} * (A : Set X) := by
  have hk : h * r * r'⁻¹ ∈ H ⊓ foldFix φ := by
    refine ⟨?_, ?_⟩
    · have h1 : r * (r⁻¹ * r')⁻¹ * r⁻¹ ∈ H := (R.N_normalizes_H hrN _ (H.inv_mem hr')).1
      have e : h * r * r'⁻¹ = h * (r * (r⁻¹ * r')⁻¹ * r⁻¹) := by group
      rw [e]
      exact H.mul_mem hh h1
    · show φ (h * r * r'⁻¹) = h * r * r'⁻¹
      rw [map_mul, map_inv, hφ, hφr']
  exact Set.mem_mul.2 ⟨_, Set.mem_mul.2 ⟨_, Set.mem_mul.2 ⟨a, ha, _, hk, rfl⟩, r', rfl, rfl⟩, b, hb,
    by rw [hy]; group⟩

namespace FoldData

variable {R : RGD2 6 H r₁ r₂ U root} {φ : X ≃* X}

theorem lift_mem (hf : FoldData R φ) {m : X} (hm : m ∈ R.N) : m⁻¹ * φ m ∈ H := by
  unfold RGD2.N at hm
  induction hm using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact H.mul_mem (H.inv_mem hx) (hf.mem_H x hx)
    · rcases hx with rfl | rfl
      · exact hf.r₁_mem
      · exact hf.r₂_mem
  | one => simp
  | mul x y hx hy ihx ihy =>
    have h1 : y⁻¹ * (x⁻¹ * φ x) * y ∈ H := (R.N_normalizes_H hy _ ihx).2
    have e : (x * y)⁻¹ * φ (x * y) = y⁻¹ * (x⁻¹ * φ x) * y * (y⁻¹ * φ y) := by
      rw [map_mul]; group
    rw [e]
    exact H.mul_mem h1 ihy
  | inv x hx ihx =>
    have h1 : x * (x⁻¹ * φ x)⁻¹ * x⁻¹ ∈ H := (R.N_normalizes_H hx _ (H.inv_mem ihx)).1
    have e : (x⁻¹)⁻¹ * φ x⁻¹ = x * (x⁻¹ * φ x)⁻¹ * x⁻¹ := by
      rw [map_inv]; group
    rw [e]
    exact h1

theorem fixed_bruhat (hf : FoldData R φ) {Xp Xm : Subgroup X} (hXp : Xp ≤ U)
    (hXm : Xm ≤ negGen 6 root) (hH : ∀ h ∈ H, ∀ x ∈ Xp, h * x * h⁻¹ ∈ Xp)
    (hφ : ∀ x ∈ Xp, φ x ∈ Xp) {r : X} (hrN : r ∈ R.N) (hr : ∀ x ∈ Xp, r * x * r⁻¹ ∈ Xm) {y : X}
    (hy : y ∈ (Xp : Set X) * (H : Set X) * {r} * (Xp : Set X)) (hfix : φ y = y) :
    ∃ a ∈ Xp, ∃ h ∈ H, ∃ b ∈ Xp, φ a = a ∧ φ (h * r) = h * r ∧ φ b = b ∧
      y = a * (h * r) * b := by
  obtain ⟨c, hc, b, hb, rfl⟩ := Set.mem_mul.1 hy
  obtain ⟨d, hd, r', hr', rfl⟩ := Set.mem_mul.1 hc
  obtain ⟨a, ha, h, hh, rfl⟩ := Set.mem_mul.1 hd
  obtain rfl : r = r' := (Set.mem_singleton_iff.1 hr').symm
  obtain ⟨c₀, hc0, hcdef⟩ : ∃ c₀ ∈ H, φ r = r * c₀ := ⟨r⁻¹ * φ r, hf.lift_mem hrN, by group⟩
  have hc1 : r * c₀ * r⁻¹ ∈ H := (R.N_normalizes_H hrN c₀ hc0).1
  have hfix' : φ a * φ h * (r * c₀) * φ b = a * h * r * b := by
    simpa only [map_mul, hcdef] using hfix
  obtain ⟨haa, hhh, hbb⟩ := bruhat_unique R hXp hXm hH hr (a := φ a) (a' := a) (b := φ b)
    (b' := b) (h := φ h * (r * c₀ * r⁻¹)) (h' := h) (hφ a ha) ha (hφ b hb) hb
    (H.mul_mem (hf.mem_H h hh) hc1) hh
    (by rw [← hfix']; group)
  refine ⟨a, ha, h, hh, b, hb, haa, ?_, hbb, by group⟩
  calc φ (h * r) = φ h * (r * c₀) := by rw [map_mul, hcdef]
    _ = (φ h * (r * c₀ * r⁻¹)) * r := by group
    _ = h * r := by rw [hhh]

theorem bruhat_decomp₁ (hf : FoldData R φ) {y : X} (hy : y ∈ root (-1)) (hy1 : y ≠ 1)
    (hfix : φ y = y) :
    ∃ a ∈ root 1, ∃ h ∈ H, ∃ b ∈ root 1, φ a = a ∧ φ (h * r₁) = h * r₁ ∧ φ b = b ∧
      y = a * (h * r₁) * b := by
  obtain ⟨a1, -, -⟩ := R.act₁
  refine hf.fixed_bruhat (Xp := root 1) (Xm := root (-1)) (R.root_le_U (by norm_num) (by norm_num))
    (fun z hz => mem_negGen_of_mem (k := 1) (by norm_num) (by norm_num) hz)
    (fun h hh x hx => R.invariant 1 ⟨by norm_num, by norm_num⟩ h hh x hx)
    (fun x hx => hf.mem_root 1 ⟨by norm_num, by norm_num⟩ x hx) R.r₁_mem_N
    (fun x hx => mem_of_conjBy_inv a1 hx) (R.rank₁ y hy hy1) hfix

theorem bruhat_decomp₂ (hf : FoldData R φ) {y : X} (hy : y ∈ root (-5)) (hy1 : y ≠ 1)
    (hfix : φ y = y) :
    ∃ a ∈ root 5, ∃ h ∈ H, ∃ b ∈ root 5, φ a = a ∧
      φ (h * (r₂ * r₁ * r₂⁻¹)) = h * (r₂ * r₁ * r₂⁻¹) ∧ φ b = b ∧
      y = a * (h * (r₂ * r₁ * r₂⁻¹)) * b := by
  refine hf.fixed_bruhat (Xp := root 5) (Xm := root (-5)) (R.root_le_U (by norm_num) (by norm_num))
    (fun z hz => mem_negGen_of_mem (k := 5) (by norm_num) (by norm_num) hz)
    (fun h hh x hx => R.invariant 5 ⟨by norm_num, by norm_num⟩ h hh x hx)
    (fun x hx => hf.mem_root 5 ⟨by norm_num, by norm_num⟩ x hx) R.r_alpha_mem_N
    (fun x hx => ?_) (bruhat_rank_alpha R hy hy1) hfix
  have h' : r₂ * r₁ * r₂⁻¹ * x * (r₂ * r₁ * r₂⁻¹)⁻¹ ∈ root (Rt 6 (((6 : ℕ) : ℤ) - 4 - 4)) :=
    R.actsPos_alpha 4 x (by rw [bruhat_rt_4]; exact hx)
  rwa [bruhat_rt_m2] at h'

theorem exists_fixed_lift₁ (hf : FoldData R φ) : ∃ r₁' : X, φ r₁' = r₁' ∧ r₁⁻¹ * r₁' ∈ H := by
  obtain ⟨y, hy, hy1, hyfix⟩ := hf.odd_fix (-1) ⟨by norm_num, by norm_num⟩ (by norm_num)
  obtain ⟨a, -, h, hh, b, -, -, hfix, -, -⟩ := hf.bruhat_decomp₁ hy hy1 hyfix
  exact ⟨h * r₁, hfix, by simpa only [mul_assoc] using R.conj_H₁' hh⟩

theorem exists_fixed_lift₂ (hf : FoldData R φ) :
    ∃ r₂' : X, φ r₂' = r₂' ∧ (r₂ * r₁ * r₂⁻¹)⁻¹ * r₂' ∈ H := by
  obtain ⟨y, hy, hy1, hyfix⟩ := hf.odd_fix (-5) ⟨by norm_num, by norm_num⟩ (by norm_num)
  obtain ⟨a, -, h, hh, b, -, -, hfix, -, -⟩ := hf.bruhat_decomp₂ hy hy1 hyfix
  refine ⟨h * (r₂ * r₁ * r₂⁻¹), hfix, ?_⟩
  have := (R.N_normalizes_H R.r_alpha_mem_N h hh).2
  simpa only [mul_assoc] using this

theorem rank₁_F (hf : FoldData R φ) {r₁' : X} (h1 : φ r₁' = r₁') (h1H : r₁⁻¹ * r₁' ∈ H) :
    ∀ y ∈ foldRoot φ root (-1), y ≠ 1 →
      y ∈ (foldRoot φ root 1 : Set X) * ((H ⊓ foldFix φ : Subgroup X) : Set X) * {r₁'} *
        (foldRoot φ root 1 : Set X) := by
  intro y hy hy1
  obtain ⟨hy', hyfix⟩ := mem_foldRoot.1 hy
  rw [bruhat_foldIdx_neg_one] at hy'
  obtain ⟨a, ha, h, hh, b, hb, haφ, hhφ, hbφ, hyeq⟩ := hf.bruhat_decomp₁ hy' hy1 hyfix
  exact bruhat_assemble R R.r₁_mem_N h1H h1 (A := foldRoot φ root 1)
    (mem_foldRoot.2 ⟨by rw [bruhat_foldIdx_one]; exact ha, haφ⟩)
    (mem_foldRoot.2 ⟨by rw [bruhat_foldIdx_one]; exact hb, hbφ⟩) hh hhφ hyeq

theorem rank₂_F (hf : FoldData R φ) {r₂' : X} (h2 : φ r₂' = r₂')
    (h2H : (r₂ * r₁ * r₂⁻¹)⁻¹ * r₂' ∈ H) :
    ∀ y ∈ foldRoot φ root (-((3 : ℕ) : ℤ)), y ≠ 1 →
      y ∈ (foldRoot φ root ((3 : ℕ) : ℤ) : Set X) * ((H ⊓ foldFix φ : Subgroup X) : Set X) *
        {r₂'} * (foldRoot φ root ((3 : ℕ) : ℤ) : Set X) := by
  intro y hy hy1
  obtain ⟨hy', hyfix⟩ := mem_foldRoot.1 hy
  rw [bruhat_foldIdx_neg_three] at hy'
  obtain ⟨a, ha, h, hh, b, hb, haφ, hhφ, hbφ, hyeq⟩ := hf.bruhat_decomp₂ hy' hy1 hyfix
  exact bruhat_assemble R R.r_alpha_mem_N h2H h2 (A := foldRoot φ root ((3 : ℕ) : ℤ))
    (mem_foldRoot.2 ⟨by rw [bruhat_foldIdx_three]; exact ha, haφ⟩)
    (mem_foldRoot.2 ⟨by rw [bruhat_foldIdx_three]; exact hb, hbφ⟩) hh hhφ hyeq

end FoldData

end CFSG.GH74.GLS.SP
