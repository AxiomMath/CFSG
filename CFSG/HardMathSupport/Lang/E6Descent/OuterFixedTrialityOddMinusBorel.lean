module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnFinal

public section

open scoped Pointwise

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP Multiplicative

section Layer

variable {X : Type*} [Group X] (D : RankTwoSystem X 3) {k : Type} [Field k]

structure Layer1 (x₁ : Multiplicative k →* X) : Prop where
  inj : Function.Injective x₁
  mem : ∀ a, x₁ a ∈ D.root 1
  torus : ∀ h ∈ D.B ⊓ D.N, ∃ χ : kˣ, ∀ a : k, h * x₁ (ofAdd a) * h⁻¹ = x₁ (ofAdd ((χ : k) * a))
  ab₁ : ∀ a ∈ D.root 1, ∀ b ∈ D.root 1, a * b = b * a
  ab₃ : ∀ a ∈ D.root 3, ∀ b ∈ D.root 3, a * b = b * a
  tor : ∀ h ∈ D.B ⊓ D.N, ∀ y ∈ D.root 1, y ≠ 1 → ∀ z ∈ D.root 3, z ≠ 1 →
    h * y = y * h → h * z = z * h → h = 1

variable {D}

theorem un_conj_root₂_of_mem_B {b : X} (hb : b ∈ D.B) {y : X} (hy : y ∈ D.root 2) :
    b * y * b⁻¹ ∈ D.root 2 := by
  have hb' : b ∈ ((D.B ⊓ D.N : Subgroup X) : Set X) * (D.U : Set X) := D.isSplit.2 ▸ hb
  obtain ⟨h, hh, v, hv, rfl⟩ := Set.mem_mul.1 hb'
  have e : h * v * y * (h * v)⁻¹ = h * (v * y * v⁻¹) * h⁻¹ := by group
  rw [e]
  exact D.roots.invariant 2 ⟨by norm_num, by norm_num⟩ h hh _ (D.conj_root₂_mem hv hy)

theorem un_eq_of_mul_root₂ {y₁ y₂ e₁ e₂ f₁ f₂ : X} (hy₁ : y₁ ∈ D.root 1) (hy₂ : y₂ ∈ D.root 1)
    (he₁ : e₁ ∈ D.root 2) (he₂ : e₂ ∈ D.root 2) (hf₁ : f₁ ∈ D.root 2) (hf₂ : f₂ ∈ D.root 2)
    (h : e₁ * y₁ * f₁ = e₂ * y₂ * f₂) : y₁ = y₂ := by
  have hU1 : D.root 1 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  have key : ∀ {y e f : X}, y ∈ D.root 1 → e ∈ D.root 2 → f ∈ D.root 2 →
      e * y * f = y * (y⁻¹ * e * y * f) * 1 := fun {y e f} _ _ _ => by group
  have hc : ∀ {y e : X}, y ∈ D.root 1 → e ∈ D.root 2 → y⁻¹ * e * y ∈ D.root 2 := by
    intro y e hy he
    have := D.conj_root₂_mem (u := y⁻¹) (D.U.inv_mem (hU1 hy)) he
    simpa using this
  rw [key hy₁ he₁ hf₁, key hy₂ he₂ hf₂] at h
  exact (un_unique D hy₁ hy₂ ((D.root 2).mul_mem (hc hy₁ he₁) hf₁)
    ((D.root 2).mul_mem (hc hy₂ he₂) hf₂) (D.root 3).one_mem (D.root 3).one_mem h).1

variable {x₁ : Multiplicative k →* X}

@[expose] def XCond (x₁ : Multiplicative k →* X) (b : X) (c : kˣ) : Prop :=
  ∀ a : k, ∃ e ∈ D.root 2, b * x₁ (ofAdd a) * b⁻¹ = x₁ (ofAdd ((c : k) * a)) * e

theorem XCond.unique (L : Layer1 D x₁) {b : X} {c c' : kˣ} (h : XCond (D := D) x₁ b c)
    (h' : XCond (D := D) x₁ b c') : c = c' := by
  obtain ⟨e, he, h1⟩ := h 1
  obtain ⟨e', he', h2⟩ := h' 1
  have h3 : x₁ (ofAdd ((c : k) * 1)) * e = x₁ (ofAdd ((c' : k) * 1)) * e' := h1.symm.trans h2
  have := (un_unique D (L.mem _) (L.mem _) he he' (D.root 3).one_mem (D.root 3).one_mem
    (by simpa using h3)).1
  have h4 := L.inj this
  apply Units.ext
  simpa using congrArg toAdd h4

theorem XCond.one : XCond (D := D) x₁ 1 1 := fun a => ⟨1, (D.root 2).one_mem, by simp⟩

theorem XCond.mul {b b' : X} {c c' : kˣ} (hb : b ∈ D.B) (h : XCond (D := D) x₁ b c)
    (h' : XCond (D := D) x₁ b' c') : XCond (D := D) x₁ (b * b') (c * c') := by
  intro a
  obtain ⟨e', he', h2⟩ := h' a
  obtain ⟨e, he, h1⟩ := h ((c' : k) * a)
  refine ⟨e * (b * e' * b⁻¹), (D.root 2).mul_mem he (un_conj_root₂_of_mem_B hb he'), ?_⟩
  have : b * b' * x₁ (ofAdd a) * (b * b')⁻¹ =
      b * (b' * x₁ (ofAdd a) * b'⁻¹) * b⁻¹ := by group
  rw [this, h2]
  have e2 : b * (x₁ (ofAdd ((c' : k) * a)) * e') * b⁻¹ =
      (b * x₁ (ofAdd ((c' : k) * a)) * b⁻¹) * (b * e' * b⁻¹) := by group
  rw [e2, h1, mul_assoc]
  congr 3
  push_cast
  ring

theorem XCond.torus (L : Layer1 D x₁) {h : X} (hh : h ∈ D.B ⊓ D.N) :
    ∃ c : kˣ, XCond (D := D) x₁ h c := by
  obtain ⟨χ, hχ⟩ := L.torus h hh
  exact ⟨χ, fun a => ⟨1, (D.root 2).one_mem, by rw [hχ, mul_one]⟩⟩

theorem XCond.of_mem_U (L : Layer1 D x₁) {u : X} (hu : u ∈ D.U) :
    XCond (D := D) x₁ u 1 := by
  intro a
  have hU1 : D.root 1 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  have hx := hU1 (L.mem (ofAdd a))
  have hc := D.commutator_mem_root₂ L.ab₁ L.ab₃ (D.U.inv_mem hx) hu
  refine ⟨_, hc, ?_⟩
  simp only [Units.val_one, one_mul]
  group

theorem XCond.exists (L : Layer1 D x₁) {b : X} (hb : b ∈ D.B) : ∃ c : kˣ, XCond (D := D) x₁ b c := by
  have hb' : b ∈ ((D.B ⊓ D.N : Subgroup X) : Set X) * (D.U : Set X) := D.isSplit.2 ▸ hb
  obtain ⟨h, hh, v, hv, rfl⟩ := Set.mem_mul.1 hb'
  obtain ⟨c, hc⟩ := XCond.torus L hh
  exact ⟨c * 1, XCond.mul hh.1 hc (XCond.of_mem_U L hv)⟩


noncomputable def xchar (L : Layer1 D x₁) : D.B →* kˣ where
  toFun b := Classical.choose (XCond.exists L b.2)
  map_one' := XCond.unique L (Classical.choose_spec (XCond.exists L (1 : D.B).2))
    (XCond.one (D := D) (x₁ := x₁))
  map_mul' b b' := by
    refine XCond.unique L (Classical.choose_spec (XCond.exists L (b * b' : D.B).2)) ?_
    exact XCond.mul b.2 (Classical.choose_spec (XCond.exists L b.2))
      (Classical.choose_spec (XCond.exists L b'.2))

theorem xchar_spec (L : Layer1 D x₁) (b : D.B) : XCond (D := D) x₁ (b : X) (xchar L b) :=
  Classical.choose_spec (XCond.exists L b.2)

section Fixed

variable {θ : X ≃* X} {ε : k ≃+* k} {ν : kˣ}

theorem XCond.eps_fixed (L : Layer1 D x₁) (hθ2 : ∀ y ∈ D.root 2, θ y ∈ D.root 2)
    (hθ₁₁ : ∀ a : k, ∃ b ∈ D.root 2,
      θ (θ (x₁ (ofAdd a))) = b * x₁ (ofAdd ((ν : k) * ε (ε a))))
    {b : X} (hb : b ∈ D.B) (hθb : θ b = b) {c : kˣ} (h : XCond (D := D) x₁ b c) :
    ε (ε (c : k)) = c := by
  obtain ⟨d, hd, hdd⟩ := hθ₁₁ 1
  obtain ⟨e, he, hbe⟩ := h 1
  obtain ⟨d₂, hd₂, hdd₂⟩ := hθ₁₁ ((c : k) * 1)
  obtain ⟨e₂, he₂, hbe₂⟩ := h ((ν : k) * ε (ε 1))
  have h1 : θ (θ (b * x₁ (ofAdd 1) * b⁻¹)) = (b * d * b⁻¹) *
      (x₁ (ofAdd ((c : k) * ((ν : k) * ε (ε 1)))) * e₂) := by
    simp only [map_mul, map_inv, hθb]
    rw [hdd, ← hbe₂]
    group
  have h2 : θ (θ (b * x₁ (ofAdd 1) * b⁻¹)) = (d₂ * x₁ (ofAdd ((ν : k) * ε (ε ((c : k) * 1))))) *
      θ (θ e) := by
    rw [hbe, map_mul, map_mul, hdd₂]
  rw [h1] at h2
  have hθθ : θ (θ e) ∈ D.root 2 := hθ2 _ (hθ2 _ he)
  have h3 := un_eq_of_mul_root₂ (L.mem _) (L.mem _)
    (un_conj_root₂_of_mem_B hb hd) hd₂ he₂ hθθ (by simpa only [mul_assoc] using h2)
  have h4 := congrArg toAdd (L.inj h3)
  simp only [toAdd_ofAdd, map_one, mul_one] at h4
  have hν : (ν : k) ≠ 0 := ν.ne_zero
  have : (ν : k) * ε (ε (c : k)) = (ν : k) * c := by rw [← h4]; ring
  exact mul_left_cancel₀ hν this

theorem XCond.mem_U_of_fixed (L : Layer1 D x₁) (hθ2 : ∀ y ∈ D.root 2, θ y ∈ D.root 2)
    (hθ2' : ∀ y, θ y ∈ D.root 2 → y ∈ D.root 2)
    (hθ₁ : ∀ y ∈ D.root 1, ∃ b ∈ D.root 2, ∃ z ∈ D.root 3, θ y = b * z)
    {b : X} (hb : b ∈ D.B) (hθb : θ b = b) (h : XCond (D := D) x₁ b 1) : b ∈ D.U := by
  have hU1 : D.root 1 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  have hU3 : D.root 3 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  have hb' : b ∈ ((D.B ⊓ D.N : Subgroup X) : Set X) * (D.U : Set X) := D.isSplit.2 ▸ hb
  obtain ⟨h₀, hh₀, v, hv, rfl⟩ := Set.mem_mul.1 hb'
  obtain ⟨χ, hχ⟩ := XCond.torus L hh₀
  have hχ1 : χ = 1 := by
    have := XCond.unique L (XCond.mul hh₀.1 hχ (XCond.of_mem_U L hv)) h
    simpa using this
  subst hχ1
  have hfix₁ : ∀ a : k, h₀ * x₁ (ofAdd a) * h₀⁻¹ = x₁ (ofAdd a) := by
    intro a
    obtain ⟨χ', hχ'⟩ := L.torus h₀ hh₀
    have h1 : χ' = 1 := by
      have e1 := XCond.torus L hh₀
      obtain ⟨c, hc⟩ := e1
      have hc' : XCond (D := D) x₁ h₀ χ' := fun a => ⟨1, (D.root 2).one_mem, by rw [hχ', mul_one]⟩
      exact (XCond.unique L hc' hχ)
    subst h1
    rw [hχ']
    simp
  set y₀ : X := x₁ (ofAdd 1) with hy₀
  have hy₀1 : y₀ ∈ D.root 1 := L.mem _
  have hy₀ne : y₀ ≠ 1 := by
    intro h1
    have := L.inj (h1.trans (map_one x₁).symm)
    exact one_ne_zero (congrArg toAdd this)
  obtain ⟨b₂, hb₂, z₀, hz₀, hθy₀⟩ := hθ₁ y₀ hy₀1
  have hz₀ne : z₀ ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hθy₀
    have hy2 : y₀ ∈ D.root 2 := hθ2' _ (hθy₀ ▸ hb₂)
    have := un_unique D hy₀1 (D.root 1).one_mem (D.root 2).one_mem hy2 (D.root 3).one_mem
      (D.root 3).one_mem (by simp)
    exact hy₀ne this.1
  set z₁ : X := h₀ * z₀ * h₀⁻¹ with hz₁
  have hz₁mem : z₁ ∈ D.root 3 := D.roots.invariant 3 ⟨by norm_num, by norm_num⟩ h₀ hh₀ _ hz₀
  obtain ⟨e, he, hbe⟩ := h 1
  have hbU : h₀ * v ∈ D.B := (D.B.mul_mem hh₀.1 (D.U_le_B hv))
  have hzz : z₁ = z₀ := by
    have hcomm := D.commutator_mem_root₂ L.ab₁ L.ab₃ hv (hU3 hz₀)
    have hbz : h₀ * v * z₀ * (h₀ * v)⁻¹ =
        (h₀ * (v * z₀ * v⁻¹ * z₀⁻¹) * h₀⁻¹) * z₁ := by
      simp only [hz₁]
      group
    have hmem1 : h₀ * (v * z₀ * v⁻¹ * z₀⁻¹) * h₀⁻¹ ∈ D.root 2 :=
      D.roots.invariant 2 ⟨by norm_num, by norm_num⟩ h₀ hh₀ _ hcomm
    have hθe : θ e ∈ D.root 2 := hθ2 _ he
    have hconj : z₀ * θ e * z₀⁻¹ ∈ D.root 2 := D.conj_root₂_mem (hU3 hz₀) hθe
    have hmain : θ (h₀ * v * x₁ (ofAdd 1) * (h₀ * v)⁻¹) =
        h₀ * v * θ (x₁ (ofAdd 1)) * (h₀ * v)⁻¹ := by
      simp only [map_mul, map_inv, hθb]
    have hlhs : θ (h₀ * v * x₁ (ofAdd 1) * (h₀ * v)⁻¹) = (b₂ * (z₀ * θ e * z₀⁻¹)) * z₀ := by
      rw [hbe]
      simp only [Units.val_one, one_mul, map_mul]
      rw [← hy₀, hθy₀]
      group
    rw [hmain, hθy₀] at hlhs
    have hrhs : h₀ * v * (b₂ * z₀) * (h₀ * v)⁻¹ =
        ((h₀ * v) * b₂ * (h₀ * v)⁻¹ * (h₀ * (v * z₀ * v⁻¹ * z₀⁻¹) * h₀⁻¹)) * z₁ := by
      simp only [hz₁]
      group
    rw [hrhs] at hlhs
    have hB2 := un_conj_root₂_of_mem_B hbU hb₂
    exact (un_unique D (D.root 1).one_mem (D.root 1).one_mem
      ((D.root 2).mul_mem hB2 hmem1) ((D.root 2).mul_mem hb₂ hconj) hz₁mem hz₀
      (by simpa only [one_mul] using hlhs)).2.2
  have hh₁ : h₀ = 1 := by
    refine L.tor h₀ hh₀ y₀ hy₀1 hy₀ne z₀ hz₀ hz₀ne ?_ ?_
    · have := hfix₁ 1
      exact mul_inv_eq_iff_eq_mul.1 this
    · exact mul_inv_eq_iff_eq_mul.1 hzz
  rw [hh₁, one_mul]
  exact hv


variable [Finite k]

theorem card_B_fix_dvd (L : Layer1 D x₁) (hθ2 : ∀ y ∈ D.root 2, θ y ∈ D.root 2)
    (hθ2' : ∀ y, θ y ∈ D.root 2 → y ∈ D.root 2)
    (hθ₁ : ∀ y ∈ D.root 1, ∃ b ∈ D.root 2, ∃ z ∈ D.root 3, θ y = b * z)
    (hθ₁₁ : ∀ a : k, ∃ b ∈ D.root 2,
      θ (θ (x₁ (ofAdd a))) = b * x₁ (ofAdd ((ν : k) * ε (ε a))))
    (N : ℕ) (hN : ∀ c : kˣ, ε (ε (c : k)) = c → c ^ N = 1) :
    ∃ m : ℕ, m ∣ N ∧
      Nat.card ↥(D.B ⊓ foldFix θ) = Nat.card ↥(D.U ⊓ foldFix θ) * m := by
  let ψ : ↥(D.B ⊓ foldFix θ) →* kˣ :=
    (xchar L).comp (Subgroup.inclusion (inf_le_left : D.B ⊓ foldFix θ ≤ D.B))
  have hψ : ∀ b : ↥(D.B ⊓ foldFix θ), XCond (D := D) x₁ (b : X) (ψ b) := fun b =>
    xchar_spec L ⟨b.1, b.2.1⟩
  have hker : ψ.ker = (D.U ⊓ foldFix θ).subgroupOf (D.B ⊓ foldFix θ) := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have hc : XCond (D := D) x₁ (b : X) 1 := h1 ▸ hψ b
      exact ⟨XCond.mem_U_of_fixed L hθ2 hθ2' hθ₁ b.2.1 (mem_foldFix.1 b.2.2) hc, b.2.2⟩
    · intro h1
      exact XCond.unique L (hψ b) (XCond.of_mem_U L h1.1)
  have hU : D.U ⊓ foldFix θ ≤ D.B ⊓ foldFix θ :=
    inf_le_inf_right _ D.U_le_B
  have hkc : Nat.card ψ.ker = Nat.card ↥(D.U ⊓ foldFix θ) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv
  refine ⟨Nat.card ψ.range, ?_, ?_⟩
  · have hcyc : IsCyclic ψ.range := inferInstance
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one ?_
    rintro ⟨_, b, rfl⟩
    apply Subtype.ext
    show ψ b ^ N = 1
    exact hN _ (XCond.eps_fixed L hθ2 hθ₁₁ b.2.1 (mem_foldFix.1 b.2.2) (hψ b))
  · rw [← hkc]
    exact (Subgroup.card_ker_mul_card_range ψ).symm

end Fixed

end Layer

end CFSG.GH74.GLS.Stage2.Bender.Thm1
