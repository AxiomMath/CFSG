module

public import CFSG.GH74.GLS.LU.Local.SL2Aut2
public import CFSG.GH74.GLS.LU.Local.SL2Four

public section

open Subgroup
open CFSG.Semidihedral.MatrixCoverData (slConjugation)
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local

variable {G : Type} [Group G] {F : Type} [Field F] {K : Subgroup G}

theorem conj_mem_of_mem_normalizer {s : G} (hs : s ∈ normalizer (K : Set G)) {k : G} (hk : k ∈ K) :
    s * k * s⁻¹ ∈ K := (mem_normalizer_iff.mp hs k).mp hk

theorem conj_inv_mem_of_mem_normalizer {s : G} (hs : s ∈ normalizer (K : Set G)) {k : G}
    (hk : k ∈ K) : s⁻¹ * k * s ∈ K := by
  have := (mem_normalizer_iff.mp ((normalizer (K : Set G)).inv_mem hs) k).mp hk
  simpa using this

@[expose] noncomputable def actAut (e : SL(2, F) ≃* ↥K) (s : G) (hs : s ∈ normalizer (K : Set G)) :
    MulAut SL(2, F) where
  toFun M := e.symm ⟨s * (e M : G) * s⁻¹, conj_mem_of_mem_normalizer hs (e M).2⟩
  invFun M := e.symm ⟨s⁻¹ * (e M : G) * s, conj_inv_mem_of_mem_normalizer hs (e M).2⟩
  left_inv M := by
    apply e.injective
    simp only [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    simp [mul_assoc]
  right_inv M := by
    apply e.injective
    simp only [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' M N := by
    apply e.injective
    simp only [MulEquiv.apply_symm_apply, map_mul]
    apply Subtype.ext
    simp [mul_assoc]

theorem coe_actAut (e : SL(2, F) ≃* ↥K) {s : G} (hs : s ∈ normalizer (K : Set G)) (M : SL(2, F)) :
    ((e (actAut e s hs M) : ↥K) : G) = s * (e M : G) * s⁻¹ := by
  show ((e (e.symm ⟨s * (e M : G) * s⁻¹, _⟩) : ↥K) : G) = _
  simp

@[expose] noncomputable def actHom (e : SL(2, F) ≃* ↥K) : ↥(normalizer (K : Set G)) →* MulAut SL(2, F) :=
  MonoidHom.mk' (fun s => actAut e s.1 s.2) (by
    intro a b
    refine MulEquiv.ext fun M => ?_
    apply e.injective
    apply Subtype.ext
    show ((e (actAut e (a.1 * b.1) _ M) : ↥K) : G) = ((e (actAut e a.1 a.2 (actAut e b.1 b.2 M)) : ↥K) : G)
    rw [coe_actAut, coe_actAut, coe_actAut]
    simp [mul_assoc])

theorem actHom_apply (e : SL(2, F) ≃* ↥K) (s : ↥(normalizer (K : Set G))) :
    actHom e s = actAut e s.1 s.2 := rfl

theorem actAut_eq_one_iff (e : SL(2, F) ≃* ↥K) {s : G} (hs : s ∈ normalizer (K : Set G)) :
    actAut e s hs = 1 ↔ ∀ k ∈ K, s * k = k * s := by
  constructor
  · intro h k hk
    have := congrArg (fun α : MulAut SL(2, F) => ((e (α (e.symm ⟨k, hk⟩)) : ↥K) : G)) h
    simp only [coe_actAut, MulAut.one_apply, MulEquiv.apply_symm_apply] at this
    calc s * k = (s * k * s⁻¹) * s := by group
      _ = k * s := by rw [this]
  · intro h
    refine MulEquiv.ext fun M => ?_
    apply e.injective
    apply Subtype.ext
    rw [coe_actAut]
    have := h (e M : G) (e M).2
    calc s * (e M : G) * s⁻¹ = (e M : G) * s * s⁻¹ := by rw [this]
      _ = (e M : G) := by group
    

theorem actAut_mul (e : SL(2, F) ≃* ↥K) {a b : G} (ha : a ∈ normalizer (K : Set G))
    (hb : b ∈ normalizer (K : Set G)) :
    actAut e (a * b) ((normalizer (K : Set G)).mul_mem ha hb) = actAut e a ha * actAut e b hb :=
  (actHom e).map_mul ⟨a, ha⟩ ⟨b, hb⟩

theorem actAut_one (e : SL(2, F) ≃* ↥K) :
    actAut e 1 ((normalizer (K : Set G)).one_mem) = 1 := (actHom e).map_one

theorem actAut_pow (e : SL(2, F) ≃* ↥K) {a : G} (ha : a ∈ normalizer (K : Set G)) (n : ℕ) :
    actAut e (a ^ n) ((normalizer (K : Set G)).pow_mem ha n) = actAut e a ha ^ n :=
  (actHom e).map_pow ⟨a, ha⟩ n

theorem actAut_inv (e : SL(2, F) ≃* ↥K) {a : G} (ha : a ∈ normalizer (K : Set G)) :
    actAut e a⁻¹ ((normalizer (K : Set G)).inv_mem ha) = (actAut e a ha)⁻¹ :=
  (actHom e).map_inv ⟨a, ha⟩

theorem actAut_congr (e : SL(2, F) ≃* ↥K) {s s' : G} (hs : s ∈ normalizer (K : Set G))
    (hs' : s' ∈ normalizer (K : Set G)) (h : s = s') : actAut e s hs = actAut e s' hs' := by
  subst h; rfl

theorem actAut_fixed_iff (e : SL(2, F) ≃* ↥K) {s : G} (hs : s ∈ normalizer (K : Set G))
    (M : SL(2, F)) : actAut e s hs M = M ↔ (e M : G) * s = s * (e M : G) := by
  constructor
  · intro h
    have := congrArg (fun N : SL(2, F) => ((e N : ↥K) : G)) h
    simp only [coe_actAut] at this
    calc (e M : G) * s = (s * (e M : G) * s⁻¹) * s := by rw [this]
      _ = s * (e M : G) := by group
  · intro h
    apply e.injective
    apply Subtype.ext
    rw [coe_actAut]
    calc s * (e M : G) * s⁻¹ = (e M : G) * s * s⁻¹ := by rw [h]
      _ = (e M : G) := by group

theorem aut_fix_of_commute {α : MulAut SL(2, F)} {y : SL(2, F)} {r : ℕ} (hr : Odd r)
    (hyr : y ^ r = 1) (hcomm : α * MulAut.conj y = MulAut.conj y * α) : α y = y := by
  set d : SL(2, F) := y⁻¹ * α y with hd
  have hdc : ∀ N : SL(2, F), N * d = d * N := by
    intro N
    obtain ⟨M, rfl⟩ := α.surjective N
    have h1 := congrArg (fun β : MulAut SL(2, F) => β M) hcomm
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at h1
    rw [hd]
    calc α M * (y⁻¹ * α y) = y⁻¹ * (y * α M * y⁻¹) * α y := by group
      _ = y⁻¹ * (α y * α M * (α y)⁻¹) * α y := by rw [h1]
      _ = (y⁻¹ * α y) * α M := by group
  have hdz : d ∈ Subgroup.center SL(2, F) := Subgroup.mem_center_iff.mpr (fun g => hdc g)
  have hdd : d * d = 1 := CFSG.GH74.GLS.IVK.Lifted.sq_eq_one_of_mem_center_sl2 hdz
  have hαy : α y = y * d := by rw [hd]; group
  have hαr : (α y) ^ r = 1 := by rw [← map_pow, hyr, map_one]
  have hcommyd : Commute y d := hdc y
  rw [hαy, hcommyd.mul_pow, hyr, one_mul] at hαr
  obtain ⟨m, hm⟩ := hr
  have hd2 : d ^ 2 = 1 := by rw [pow_two]; exact hdd
  have : d = 1 := by
    have : d ^ r = d := by
      rw [hm, pow_succ, pow_mul, hd2, one_pow, one_mul]
    rw [← this]; exact hαr
  rw [hαy, this, mul_one]

theorem exists_odd_lift [Finite F] {p f r : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ f)
    (hp2 : p ≠ 2) (h3 : 3 < p ^ f) (hr : r.Prime) (hr2 : r ≠ 2) (hrf : ¬ r ∣ f)
    {α : MulAut SL(2, F)} (hα : α ^ r = 1) : ∃ y : SL(2, F), y ^ r = 1 ∧ α = MulAut.conj y := by
  obtain ⟨y₀, hy₀⟩ := sl2_aut_inner_of_prime hp hF hp2 h3 hr hr2 hrf α hα
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  have hc0 : y₀ ^ r ∈ Subgroup.center SL(2, F) := by
    refine Subgroup.mem_center_iff.mpr (fun g => ?_)
    have h1 : (MulAut.conj y₀) ^ r = 1 := by rw [← hy₀]; exact hα
    have h2 := congrArg (fun β : MulAut SL(2, F) => β g) h1
    simp only [MulAut.one_apply] at h2
    rw [← map_pow] at h2
    simp only [MulAut.conj_apply] at h2
    calc g * y₀ ^ r = (y₀ ^ r * g * (y₀ ^ r)⁻¹) * y₀ ^ r := by rw [h2]
      _ = y₀ ^ r * g := by group
  have hc2 : y₀ ^ r * y₀ ^ r = 1 := CFSG.GH74.GLS.IVK.Lifted.sq_eq_one_of_mem_center_sl2 hc0
  refine ⟨y₀ ^ (r + 1), ?_, ?_⟩
  · obtain ⟨m, hm⟩ := hrodd
    have : (y₀ ^ (r + 1)) ^ r = (y₀ ^ r) ^ (r + 1) := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    rw [this]
    have hh : r + 1 = 2 * (m + 1) := by omega
    rw [hh, pow_mul, pow_two, hc2, one_pow]
  · rw [map_pow, ← hy₀, pow_succ, hα, one_mul]

theorem centralizes_of_four_group [Finite F] {p f r : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ f)
    (hp2 : p ≠ 2) (h3 : 3 < p ^ f) (hr : r.Prime) (hr2 : r ≠ 2) (hrf : ¬ r ∣ f)
    (e : SL(2, F) ≃* ↥K) {z₁ z₂ y : G}
    (hz₁ : z₁ ∈ normalizer (K : Set G)) (hz₂ : z₂ ∈ normalizer (K : Set G))
    (hy : y ∈ normalizer (K : Set G))
    (hz₁sq : z₁ * z₁ = 1) (hz₂sq : z₂ * z₂ = 1) (h12 : z₁ * z₂ = z₂ * z₁)
    (hy1 : y * z₁ = z₁ * y) (hy2 : y * z₂ = z₂ * y) (hyr : y ^ r = 1)
    (hnc₁ : ∃ k ∈ K, z₁ * k ≠ k * z₁) (hnc₂ : ∃ k ∈ K, z₂ * k ≠ k * z₂)
    (hnc₁₂ : ∃ k ∈ K, (z₁ * z₂) * k ≠ k * (z₁ * z₂))
    (hab₁ : ∀ a ∈ K, ∀ b ∈ K, a * z₁ = z₁ * a → b * z₁ = z₁ * b → a * b = b * a)
    (hab₂ : ∀ a ∈ K, ∀ b ∈ K, a * z₂ = z₂ * a → b * z₂ = z₂ * b → a * b = b * a) :
    ∀ k ∈ K, y * k = k * y := by
  have hodd : Odd (Nat.card F) := by
    rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  have h3' : 3 < Nat.card F := by rw [hF]; exact h3
  have hh2 : (2 : F) ≠ 0 := by
    have := Fintype.ofFinite F
    refine Ring.two_ne_zero ?_
    intro h2
    have h := (FiniteField.even_card_iff_char_two (F := F)).mp h2
    rw [← Nat.card_eq_fintype_card] at h
    have := Nat.odd_iff.mp hodd
    omega
  set α₁ := actAut e z₁ hz₁ with hα₁
  set α₂ := actAut e z₂ hz₂ with hα₂
  set γ := actAut e y hy with hγ
  have hα₁sq : α₁ * α₁ = 1 := by
    have h := (actHom e).map_mul ⟨z₁, hz₁⟩ ⟨z₁, hz₁⟩
    have h1 : (⟨z₁, hz₁⟩ * ⟨z₁, hz₁⟩ : ↥(normalizer (K : Set G))) = 1 := Subtype.ext hz₁sq
    rw [h1, map_one] at h
    exact h.symm
  have hα₂sq : α₂ * α₂ = 1 := by
    have h := (actHom e).map_mul ⟨z₂, hz₂⟩ ⟨z₂, hz₂⟩
    have h1 : (⟨z₂, hz₂⟩ * ⟨z₂, hz₂⟩ : ↥(normalizer (K : Set G))) = 1 := Subtype.ext hz₂sq
    rw [h1, map_one] at h
    exact h.symm
  have hne : ∀ (z : G) (hz : z ∈ normalizer (K : Set G)), (∃ k ∈ K, z * k ≠ k * z) →
      actAut e z hz ≠ 1 := by
    intro z hz hnc h
    obtain ⟨k, hk, hkc⟩ := hnc
    exact hkc ((actAut_eq_one_iff e hz).mp h k hk)
  have hα₁ne : α₁ ≠ 1 := hne z₁ hz₁ hnc₁
  have hα₂ne : α₂ ≠ 1 := hne z₂ hz₂ hnc₂
  have hα₁₂ne : α₁ * α₂ ≠ 1 := by
    have := hne (z₁ * z₂) ((normalizer (K : Set G)).mul_mem hz₁ hz₂) hnc₁₂
    rwa [actAut_mul e hz₁ hz₂] at this
  have hfix : ∀ (z : G) (hz : z ∈ normalizer (K : Set G)),
      (∀ a ∈ K, ∀ b ∈ K, a * z = z * a → b * z = z * b → a * b = b * a) →
      ∀ a b : SL(2, F), actAut e z hz a = a → actAut e z hz b = b → a * b = b * a := by
    intro z hz hab a b ha hb
    have h1 := (actAut_fixed_iff e hz a).mp ha
    have h2 := (actAut_fixed_iff e hz b).mp hb
    have := hab _ (e a).2 _ (e b).2 h1 h2
    apply e.injective
    apply Subtype.ext
    simpa using this
  obtain ⟨G₁, hG₁, ⟨c₁, hc₁⟩, hn₁⟩ :=
    sl2_aut_matrix_form_of_involution hodd h3' α₁ hα₁sq hα₁ne (hfix z₁ hz₁ hab₁)
  obtain ⟨G₂, hG₂, ⟨c₂, hc₂⟩, hn₂⟩ :=
    sl2_aut_matrix_form_of_involution hodd h3' α₂ hα₂sq hα₂ne (hfix z₂ hz₂ hab₂)
  have hγr : γ ^ r = 1 := by
    have h1 : (⟨y, hy⟩ ^ r : ↥(normalizer (K : Set G))) = 1 := Subtype.ext hyr
    have := (actHom e).map_pow ⟨y, hy⟩ r
    rw [h1, map_one] at this
    exact this.symm
  obtain ⟨y₀, hy₀⟩ := sl2_aut_inner_of_prime hp hF hp2 h3 hr hr2 hrf γ hγr
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  have hc0 : y₀ ^ r ∈ Subgroup.center SL(2, F) := by
    refine Subgroup.mem_center_iff.mpr (fun g => ?_)
    have h1 : (MulAut.conj y₀) ^ r = 1 := by rw [← hy₀]; exact hγr
    have h2 := congrArg (fun β : MulAut SL(2, F) => β g) h1
    simp only [MulAut.one_apply] at h2
    rw [← map_pow] at h2
    simp only [MulAut.conj_apply] at h2
    calc g * y₀ ^ r = (y₀ ^ r * g * (y₀ ^ r)⁻¹) * y₀ ^ r := by rw [h2]
      _ = y₀ ^ r * g := by group
  have hc2 : y₀ ^ r * y₀ ^ r = 1 := CFSG.GH74.GLS.IVK.Lifted.sq_eq_one_of_mem_center_sl2 hc0
  set y₁ : SL(2, F) := y₀ ^ (r + 1) with hy₁
  have hy₁γ : MulAut.conj y₁ = γ := by
    rw [hy₁, map_pow, ← hy₀, pow_succ, hγr, one_mul]
  have hy₁r : y₁ ^ r = 1 := by
    obtain ⟨m, hm⟩ := hrodd
    have : y₁ ^ r = (y₀ ^ r) ^ (r + 1) := by
      rw [hy₁, ← pow_mul, ← pow_mul, mul_comm]
    rw [this]
    have hh : r + 1 = 2 * (m + 1) := by omega
    rw [hh, pow_mul, pow_two, hc2, one_pow]
  have hcomm_of : ∀ (z : G) (hz : z ∈ normalizer (K : Set G)), y * z = z * y →
      actAut e z hz * γ = γ * actAut e z hz := by
    intro z hz hyz
    have h1 := (actHom e).map_mul ⟨z, hz⟩ ⟨y, hy⟩
    have h2 := (actHom e).map_mul ⟨y, hy⟩ ⟨z, hz⟩
    have h3 : (⟨z, hz⟩ * ⟨y, hy⟩ : ↥(normalizer (K : Set G))) = ⟨y, hy⟩ * ⟨z, hz⟩ :=
      Subtype.ext hyz.symm
    rw [h3] at h1
    exact h2.symm.trans h1 |>.symm
  have hfix₁ : α₁ y₁ = y₁ := by
    refine aut_fix_of_commute hrodd hy₁r ?_
    rw [hy₁γ]; exact hcomm_of z₁ hz₁ hy1
  have hfix₂ : α₂ y₁ = y₁ := by
    refine aut_fix_of_commute hrodd hy₁r ?_
    rw [hy₁γ]; exact hcomm_of z₂ hz₂ hy2
  have hmat : ∀ (G' : GL (Fin 2) F) (α : MulAut SL(2, F)), α = slConjugation F G' → α y₁ = y₁ →
      (G' : Matrix (Fin 2) (Fin 2) F) * (y₁ : Matrix (Fin 2) (Fin 2) F) =
        (y₁ : Matrix (Fin 2) (Fin 2) F) * (G' : Matrix (Fin 2) (Fin 2) F) := by
    intro G' α hα hfix
    have h := congrArg (fun N : SL(2, F) => (N : Matrix (Fin 2) (Fin 2) F)) hfix
    simp only [hα, slConjugation_coe] at h
    have hinv : ((G'⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (G' : Matrix (Fin 2) (Fin 2) F) = 1 := Units.inv_mul G'
    calc (G' : Matrix (Fin 2) (Fin 2) F) * (y₁ : Matrix (Fin 2) (Fin 2) F)
        = ((G' : Matrix (Fin 2) (Fin 2) F) * (y₁ : Matrix (Fin 2) (Fin 2) F) *
            ((G'⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) * (G' : Matrix (Fin 2) (Fin 2) F) := by
          rw [Matrix.mul_assoc ((G' : Matrix (Fin 2) (Fin 2) F) * (y₁ : Matrix (Fin 2) (Fin 2) F)), hinv,
            Matrix.mul_one]
      _ = (y₁ : Matrix (Fin 2) (Fin 2) F) * (G' : Matrix (Fin 2) (Fin 2) F) := by rw [h]
  have hG₁y := hmat G₁ α₁ hG₁ hfix₁
  have hG₂y := hmat G₂ α₂ hG₂ hfix₂
  have hdist : ∀ c : F, (G₁ : Matrix (Fin 2) (Fin 2) F) *
      ((G₂⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ≠ c • 1 := by
    intro c hc
    have h1 : slConjugation F (G₁ * G₂⁻¹) = 1 := by
      refine slConjugation_eq_one_of_scalar _ c ?_
      rw [Units.val_mul]; exact hc
    rw [map_mul, map_inv, ← hG₁, ← hG₂] at h1
    have h2 : α₁ = α₂ := by
      have := mul_inv_eq_one.mp h1
      exact this
    apply hα₁₂ne
    rw [← h2]; exact hα₁sq
  have hα₁₂comm : α₁ * α₂ = α₂ * α₁ := by
    have h1 := (actHom e).map_mul ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩
    have h2 := (actHom e).map_mul ⟨z₂, hz₂⟩ ⟨z₁, hz₁⟩
    have h3 : (⟨z₁, hz₁⟩ * ⟨z₂, hz₂⟩ : ↥(normalizer (K : Set G))) = ⟨z₂, hz₂⟩ * ⟨z₁, hz₁⟩ :=
      Subtype.ext h12
    rw [h3] at h1
    exact h1.symm.trans h2
  have hcomm : ∃ c : F, (G₁ : Matrix (Fin 2) (Fin 2) F) * (G₂ : Matrix (Fin 2) (Fin 2) F) =
      c • ((G₂ : Matrix (Fin 2) (Fin 2) F) * (G₁ : Matrix (Fin 2) (Fin 2) F)) := by
    set H : GL (Fin 2) F := G₁ * G₂ * (G₂ * G₁)⁻¹ with hH
    have h1 : slConjugation F H = 1 := by
      rw [hH, map_mul, map_inv, map_mul, map_mul, ← hG₁, ← hG₂, hα₁₂comm]
      group
    obtain ⟨c, hc⟩ := exists_scalar_of_slConjugation_eq_one H h1
    refine ⟨c, ?_⟩
    have : G₁ * G₂ = H * (G₂ * G₁) := by rw [hH]; group
    have h2 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) this
    simp only [Units.val_mul] at h2
    rw [h2, hc, Matrix.smul_mul, Matrix.one_mul]
  have hy₁1 : y₁ = 1 :=
    odd_centralizer_four_group hh2 G₁ G₂ y₁ ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ hn₁ hn₂ hdist hcomm hG₁y hG₂y
      hrodd hy₁r
  have hγ1 : γ = 1 := by rw [← hy₁γ, hy₁1, map_one]
  exact (actAut_eq_one_iff e hy).mp hγ1

end CFSG.GH74.GLS.LU.Local
