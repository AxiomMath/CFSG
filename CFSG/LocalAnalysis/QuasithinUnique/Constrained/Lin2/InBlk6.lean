module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InBlk5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2412h
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InData

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups commutatorElement

section Abstract

theorem conj_mem_commutator' {G : Type} [Group G] {A B A' B' : Subgroup G} {g : G}
    (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A') (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ B') :
    ∀ θ ∈ ⁅A, B⁆, g * θ * g⁻¹ ∈ ⁅A', B'⁆ := by
  have h : ⁅A, B⁆ ≤ (⁅A', B'⁆).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    show g * ⁅a, b⁆ * g⁻¹ ∈ ⁅A', B'⁆
    have e : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
      simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact Subgroup.commutator_mem_commutator (hA a ha) (hB b hb)
  intro θ hθ
  exact h hθ

theorem trans_fixed {G : Type} [Group G] {D Z : Subgroup G} {f : G}
    (hfD : ∀ d ∈ D, f * d * f⁻¹ ∈ D)
    (hfree : ∀ z ∈ Z, z ≠ 1 → ∀ d ∈ D, d⁻¹ * z * d = z → d = 1)
    (htr : ∀ a ∈ Z, a ≠ 1 → ∀ b ∈ Z, b ≠ 1 → ∃ d ∈ D, d⁻¹ * a * d = b)
    {a b : G} (ha : a ∈ Z) (ha1 : a ≠ 1) (hb : b ∈ Z) (hb1 : b ≠ 1)
    (hfa : f * a * f⁻¹ = a) (hfb : f * b * f⁻¹ = b) :
    ∃ d ∈ D, f * d * f⁻¹ = d ∧ d⁻¹ * a * d = b := by
  obtain ⟨d, hd, hdab⟩ := htr a ha ha1 b hb hb1
  refine ⟨d, hd, ?_, hdab⟩
  set d₂ := f * d * f⁻¹ with hd₂
  have hd₂D : d₂ ∈ D := hfD d hd
  have hfa' : f⁻¹ * a * f = a := by
    have : f⁻¹ * (f * a * f⁻¹) * f = a := by group
    rwa [hfa] at this
  have hd₂ab : d₂⁻¹ * a * d₂ = b := by
    have e : d₂⁻¹ * a * d₂ = f * (d⁻¹ * (f⁻¹ * a * f) * d) * f⁻¹ := by
      rw [hd₂]; group
    rw [e, hfa', hdab, hfb]
  have hfix : (d * d₂⁻¹)⁻¹ * a * (d * d₂⁻¹) = a := by
    calc (d * d₂⁻¹)⁻¹ * a * (d * d₂⁻¹) = d₂ * d⁻¹ * a * d * d₂⁻¹ := by group
      _ = d₂ * (d⁻¹ * a * d) * d₂⁻¹ := by group
      _ = d₂ * (d₂⁻¹ * a * d₂) * d₂⁻¹ := by rw [hdab, hd₂ab]
      _ = a := by group
  have h1 : d * d₂⁻¹ = 1 := hfree a ha ha1 _ (D.mul_mem hd (D.inv_mem hd₂D)) hfix
  have : d = d₂ := mul_inv_eq_one.1 h1
  exact this.symm

theorem nonsplit_core {G : Type} [Group G] {Θ Yf Zf Zf' Df : Subgroup G} {x : G}
    (hY : ∀ a ∈ Yf, ∀ b ∈ Yf, a * b = b * a)
    (hZY : Zf ≤ Yf) (hZ'Y : Zf' ≤ Yf)
    (hx1 : ∀ y ∈ Yf, x⁻¹ * y * x ∈ Yf) (hxΘ : ∀ θ ∈ Θ, x * θ * x⁻¹ ∈ Θ)
    (hxZ : ∀ z ∈ Zf, x * z * x⁻¹ ∈ Zf')
    (hΘ : ∀ y ∈ Yf, ∃ θ ∈ Θ, ∃ z ∈ Zf, y = θ * z)
    (hDΘ : ∀ d ∈ Df, ∀ θ ∈ Θ, d * θ * d⁻¹ ∈ Θ)
    (hDZ : ∀ d ∈ Df, ∀ z ∈ Zf, d * z * d⁻¹ = z)
    (hDtr : ∀ a ∈ Zf', a ≠ 1 → ∀ b ∈ Zf', b ≠ 1 → ∃ d ∈ Df, d * a * d⁻¹ = b)
    (h3 : ∀ a ∈ Zf', a ≠ 1 → ∃ b ∈ Zf', b ≠ 1 ∧ b ≠ a)
    (hne : ∃ a ∈ Zf', a ≠ 1) :
    Zf ≤ Θ := by
  have hΘ' : ∀ y ∈ Yf, ∃ θ ∈ Θ, ∃ z' ∈ Zf', y = θ * z' := by
    intro y hy
    obtain ⟨θ₁, hθ₁, z₁, hz₁, h1⟩ := hΘ (x⁻¹ * y * x) (hx1 y hy)
    refine ⟨x * θ₁ * x⁻¹, hxΘ θ₁ hθ₁, x * z₁ * x⁻¹, hxZ z₁ hz₁, ?_⟩
    calc y = x * (x⁻¹ * y * x) * x⁻¹ := by group
      _ = x * (θ₁ * z₁) * x⁻¹ := by rw [← h1]
      _ = x * θ₁ * x⁻¹ * (x * z₁ * x⁻¹) := by group
  obtain ⟨a, ha, ha1⟩ := hne
  obtain ⟨θ, hθ, z₁, hz₁, hθz⟩ := hΘ a (hZ'Y ha)
  obtain ⟨b, hb, hb1, hba⟩ := h3 a ha ha1
  obtain ⟨d, hd, hdab⟩ := hDtr a ha ha1 b hb hb1
  have hθa : θ = a * z₁⁻¹ := by
    rw [hθz]; group
  have hdθ : d * θ * d⁻¹ = b * z₁⁻¹ := by
    rw [hθa]
    calc d * (a * z₁⁻¹) * d⁻¹ = (d * a * d⁻¹) * (d * z₁⁻¹ * d⁻¹) := by group
      _ = b * z₁⁻¹ := by
        rw [hdab]
        congr 1
        have := hDZ d hd z₁⁻¹ (Zf.inv_mem hz₁)
        exact this
  have hc : a⁻¹ * b ∈ Θ := by
    have h1 : θ⁻¹ * (d * θ * d⁻¹) ∈ Θ := Θ.mul_mem (Θ.inv_mem hθ) (hDΘ d hd θ hθ)
    have e : θ⁻¹ * (d * θ * d⁻¹) = a⁻¹ * b := by
      rw [hdθ, hθa]
      have hz₁Y : z₁ ∈ Yf := hZY hz₁
      have haY : a ∈ Yf := hZ'Y ha
      have hbY : b ∈ Yf := hZ'Y hb
      have hc1 : z₁ * a⁻¹ = a⁻¹ * z₁ := hY _ hz₁Y _ (Yf.inv_mem haY)
      calc (a * z₁⁻¹)⁻¹ * (b * z₁⁻¹) = z₁ * a⁻¹ * (b * z₁⁻¹) := by group
        _ = a⁻¹ * z₁ * (b * z₁⁻¹) := by rw [hc1]
        _ = a⁻¹ * (z₁ * b) * z₁⁻¹ := by group
        _ = a⁻¹ * (b * z₁) * z₁⁻¹ := by rw [hY _ hz₁Y _ hbY]
        _ = a⁻¹ * b := by group
    rwa [e] at h1
  have hc1 : a⁻¹ * b ≠ 1 := by
    intro h
    rw [mul_eq_one_iff_eq_inv] at h
    exact hba (inv_inj.1 h).symm
  have hcZ' : a⁻¹ * b ∈ Zf' := Zf'.mul_mem (Zf'.inv_mem ha) hb
  have hZ'Θ : ∀ e ∈ Zf', e ≠ 1 → e ∈ Θ := by
    intro e he he1
    obtain ⟨d', hd', hd'e⟩ := hDtr _ hcZ' hc1 e he he1
    rw [← hd'e]
    exact hDΘ d' hd' _ hc
  intro z hz
  obtain ⟨θ'', hθ'', z'', hz'', hzz⟩ := hΘ' z (hZY hz)
  have hz''Θ : z'' ∈ Θ := by
    by_cases h1 : z'' = 1
    · rw [h1]; exact Θ.one_mem
    · exact hZ'Θ z'' hz'' h1
  rw [hzz]
  exact Θ.mul_mem hθ'' hz''Θ

theorem exists_ne_one_of_card {G : Type} [Group G] [Finite G] {W : Subgroup G}
    (h : 4 ≤ Nat.card W) :
    (∃ a ∈ W, a ≠ 1) ∧ ∀ a ∈ W, a ≠ 1 → ∃ b ∈ W, b ≠ 1 ∧ b ≠ a := by
  classical
  constructor
  · by_contra hcon
    have hbot : W = ⊥ := (Subgroup.eq_bot_iff_forall W).2 fun a ha => by
      by_contra h1
      exact hcon ⟨a, ha, h1⟩
    rw [hbot, Subgroup.card_bot] at h
    omega
  · intro a ha ha1
    by_contra hcon
    have hsub : (W : Set G) ⊆ {1, a} := by
      intro b hb
      by_cases h1 : b = 1
      · exact Or.inl h1
      · refine Or.inr ?_
        by_contra h2
        exact hcon ⟨b, hb, h1, h2⟩
    have h2 : (W : Set G).ncard ≤ ({1, a} : Set G).ncard := Set.ncard_le_ncard hsub
    have h3 : ({1, a} : Set G).ncard = 2 := Set.ncard_pair (Ne.symm ha1)
    have h4 : Nat.card W = (W : Set G).ncard := Nat.card_coe_set_eq _
    omega

theorem mem_centralizer_of_conj {G : Type} [Group G] {x f y : G} (hxf : x * f = f * x)
    (hy : x * y * x⁻¹ ∈ Subgroup.centralizer ({f} : Set G)) :
    y ∈ Subgroup.centralizer ({f} : Set G) := by
  have hxf'' : x⁻¹ * f = f * x⁻¹ := by
    calc x⁻¹ * f = x⁻¹ * f * x * x⁻¹ := by group
      _ = x⁻¹ * (f * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * f) * x⁻¹ := by rw [hxf]
      _ = f * x⁻¹ := by group
  rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
  have h1 : x * (y * f) * x⁻¹ = x * (f * y) * x⁻¹ := by
    calc x * (y * f) * x⁻¹ = x * y * (f * x⁻¹) := by group
      _ = x * y * (x⁻¹ * f) := by rw [hxf'']
      _ = x * y * x⁻¹ * f := by group
      _ = f * (x * y * x⁻¹) := hy
      _ = (f * x) * y * x⁻¹ := by group
      _ = (x * f) * y * x⁻¹ := by rw [hxf]
      _ = x * (f * y) * x⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h1)

section Coord

variable {G : Type} [Group G] {F : Type} [Field F]

theorem coord_central {C V : Subgroup G} (α : ↥C →* SL(2, F))
    (β : ↥V →* Multiplicative (Fin 2 → F))
    (hβe : ∀ c : ↥C, ∀ u v : ↥V, (v : G) = c * u * c⁻¹ →
      Multiplicative.toAdd (β v) =
        (α c : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    {r : ↥C} (hr : α r = slUpper (1 : F)) {v : ↥V} (hcomm : (r : G) * v = v * r) :
    Multiplicative.toAdd (β v) 1 = 0 := by
  have h1 := hβe r v v (by
    show (v : G) = (r : G) * v * (r : G)⁻¹
    rw [hcomm]
    group)
  rw [hr, mulVec_slUpper] at h1
  have h2 := congrFun h1 0
  simp at h2
  exact h2

theorem coord_comm {C V : Subgroup G} (α : ↥C →* SL(2, F))
    (β : ↥V →* Multiplicative (Fin 2 → F))
    (hβe : ∀ c : ↥C, ∀ u v : ↥V, (v : G) = c * u * c⁻¹ →
      Multiplicative.toAdd (β v) =
        (α c : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (hVn : ∀ c ∈ C, ∀ v ∈ V, c * v * c⁻¹ ∈ V)
    {w : ↥C} {s : F} (hw : α w = slUpper s) (v : ↥V) :
    Multiplicative.toAdd (β (v * ⟨(w : G) * v * (w : G)⁻¹, hVn w w.2 v v.2⟩⁻¹)) =
      ![-(s * Multiplicative.toAdd (β v) 1), 0] := by
  have h1 := hβe w v ⟨(w : G) * v * (w : G)⁻¹, hVn w w.2 v v.2⟩ rfl
  rw [hw, mulVec_slUpper] at h1
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, h1]
  ext i
  fin_cases i <;> simp

theorem coord_theta {C V V' Z Y : Subgroup G}
    (α : ↥C →* SL(2, F)) (β : ↥V →* Multiplicative (Fin 2 → F))
    (hβs : Function.Surjective β) (hβk : ∀ v : ↥V, β v = 1 ↔ (v : G) ∈ Z)
    (hβe : ∀ c : ↥C, ∀ u v : ↥V, (v : G) = c * u * c⁻¹ →
      Multiplicative.toAdd (β v) =
        (α c : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (hVn : ∀ c ∈ C, ∀ v ∈ V, c * v * c⁻¹ ∈ V)
    {w₀ : ↥C} {s₀ : F} (hs₀ : s₀ ≠ 0) (hw₀ : α w₀ = slUpper s₀) (hw₀V' : (w₀ : G) ∈ V')
    (hY2 : ∀ v : ↥V, (v : G) ∈ Y → Multiplicative.toAdd (β v) 1 = 0) :
    ∀ y ∈ Y, y ∈ V → ∃ θ ∈ ⁅V, V'⁆, ∃ z ∈ V, (z ∈ Z) ∧ y = θ * z := by
  intro y hyY hyV
  have hy2 := hY2 ⟨y, hyV⟩ hyY
  set e₀ := Multiplicative.toAdd (β ⟨y, hyV⟩) 0 with he₀
  have hβy : Multiplicative.toAdd (β ⟨y, hyV⟩) = ![e₀, 0] := by
    ext i
    fin_cases i
    · rfl
    · simpa using hy2
  obtain ⟨v, hv⟩ := hβs (Multiplicative.ofAdd ![0, -(s₀⁻¹ * e₀)])
  set θ' : ↥V := v * ⟨(w₀ : G) * v * (w₀ : G)⁻¹, hVn w₀ w₀.2 v v.2⟩⁻¹ with hθ'
  have hcomm := coord_comm α β hβe hVn hw₀ v
  have hvβ : Multiplicative.toAdd (β v) 1 = -(s₀⁻¹ * e₀) := by
    rw [hv]; rfl
  rw [hvβ] at hcomm
  have hβθ : Multiplicative.toAdd (β θ') = ![e₀, 0] := by
    rw [hcomm]
    ext i
    fin_cases i
    · simp
      field_simp
    · simp
  refine ⟨(θ' : G), ?_, ((θ'⁻¹ * ⟨y, hyV⟩ : ↥V) : G), (θ'⁻¹ * ⟨y, hyV⟩ : ↥V).2, ?_, ?_⟩
  · have e : (θ' : G) = ⁅(v : G), (w₀ : G)⁆ := by
      simp [hθ', commutatorElement_def, mul_assoc]
    rw [e]
    exact Subgroup.commutator_mem_commutator v.2 hw₀V'
  · rw [← hβk]
    apply Multiplicative.toAdd.injective
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hβθ, hβy]
    ext i
    fin_cases i <;> simp
  · simp

end Coord

theorem nonsplit_main {G : Type} [Group G] {L U R Y Z D V' Z' Zf' : Subgroup G} {f x : G}
    {F : Type} [Field F]
    (α : ↥(L ⊓ Subgroup.centralizer ({f} : Set G)) →* SL(2, F))
    (β : ↥(U ⊓ Subgroup.centralizer ({f} : Set G)) →* Multiplicative (Fin 2 → F))
    (hαs : Function.Surjective α) (hαk : ∀ c, α c = 1 ↔ (c : G) ∈ U)
    (hRα : ∀ c : ↥(L ⊓ Subgroup.centralizer ({f} : Set G)),
      (c : G) ∈ R ↔ ∃ s : F, α c = slUpper s)
    (hβs : Function.Surjective β) (hβk : ∀ v, β v = 1 ↔ (v : G) ∈ Z)
    (hβe : ∀ (c : ↥(L ⊓ Subgroup.centralizer ({f} : Set G)))
        (u v : ↥(U ⊓ Subgroup.centralizer ({f} : Set G))),
        (v : G) = c * u * c⁻¹ →
          Multiplicative.toAdd (β v) =
            (α c : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (hVn : ∀ c ∈ L ⊓ Subgroup.centralizer ({f} : Set G),
      ∀ v ∈ U ⊓ Subgroup.centralizer ({f} : Set G),
        c * v * c⁻¹ ∈ U ⊓ Subgroup.centralizer ({f} : Set G))
    (hxf : x * f = f * x)
    (hV' : ∀ y, y ∈ V' ↔ x * y * x⁻¹ ∈ U ⊓ Subgroup.centralizer ({f} : Set G))
    (hZ' : ∀ y, y ∈ Z' ↔ x * y * x⁻¹ ∈ Z)
    (hZf' : ∀ y, y ∈ Zf' ↔ x * y * x⁻¹ ∈ Z ⊓ Subgroup.centralizer ({f} : Set G))
    (hV'C : ∀ w ∈ V', w ∈ L ⊓ Subgroup.centralizer ({f} : Set G))
    (hV'R : ∀ w ∈ V', w ∈ R)
    (hYU' : ∀ y, y ∈ U → x * y * x⁻¹ ∈ U → y ∈ Y)
    (hYc : ∀ y ∈ Y, ∀ r ∈ R, r * y = y * r)
    (hYR : Y ≤ R) (hYU : Y ≤ U) (hZY : Z ≤ Y)
    (hYx : ∀ y ∈ Y, x * y * x⁻¹ ∈ Y ∧ x⁻¹ * y * x ∈ Y)
    (hx2 : ∀ u ∈ U, x⁻¹ * (x⁻¹ * u * x) * x ∈ U)
    (hDZc : ∀ d ∈ D, ∀ z ∈ Z, d * z = z * d)
    (hDV : ∀ d ∈ D ⊓ Subgroup.centralizer ({f} : Set G),
      ∀ v ∈ U ⊓ Subgroup.centralizer ({f} : Set G),
        d * v * d⁻¹ ∈ U ⊓ Subgroup.centralizer ({f} : Set G))
    (hDV' : ∀ d ∈ D ⊓ Subgroup.centralizer ({f} : Set G), ∀ w ∈ V', d * w * d⁻¹ ∈ V')
    (hfD : ∀ d ∈ D, f * d * f⁻¹ ∈ D)
    (hfree : ∀ z ∈ Z', z ≠ 1 → ∀ d ∈ D, d⁻¹ * z * d = z → d = 1)
    (htr : ∀ a ∈ Z', a ≠ 1 → ∀ b ∈ Z', b ≠ 1 → ∃ d ∈ D, d⁻¹ * a * d = b) :
    (∃ w ∈ V', w ∉ U) ∧
      ((∀ a ∈ Zf', a ≠ 1 → ∃ b ∈ Zf', b ≠ 1 ∧ b ≠ a) → (∃ a ∈ Zf', a ≠ 1) →
        Z ⊓ Subgroup.centralizer ({f} : Set G) ≤
          ⁅U ⊓ Subgroup.centralizer ({f} : Set G),
            L ⊓ Subgroup.centralizer ({f} : Set G)⁆) := by
  classical
  obtain ⟨r₁, hr₁⟩ := hαs (slUpper (1 : F))
  have hr₁R : (r₁ : G) ∈ R := (hRα r₁).2 ⟨1, hr₁⟩
  have hβ2 : ∀ v : ↥(U ⊓ Subgroup.centralizer ({f} : Set G)), (v : G) ∈ Y →
      Multiplicative.toAdd (β v) 1 = 0 := fun v hv =>
    coord_central α β hβe hr₁ (hYc _ hv _ hr₁R)
  have hxf'' : x⁻¹ * f = f * x⁻¹ := by
    calc x⁻¹ * f = x⁻¹ * f * x * x⁻¹ := by group
      _ = x⁻¹ * (f * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * f) * x⁻¹ := by rw [hxf]
      _ = f * x⁻¹ := by group
  have hcf : ∀ y : G, y ∈ Subgroup.centralizer ({f} : Set G) →
      x * y * x⁻¹ ∈ Subgroup.centralizer ({f} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    calc x * y * x⁻¹ * f = x * y * (x⁻¹ * f) := by group
      _ = x * y * (f * x⁻¹) := by rw [hxf'']
      _ = x * (y * f) * x⁻¹ := by group
      _ = x * (f * y) * x⁻¹ := by rw [hy]
      _ = (x * f) * y * x⁻¹ := by group
      _ = (f * x) * y * x⁻¹ := by rw [hxf]
      _ = f * (x * y * x⁻¹) := by group
  have hcf' : ∀ y : G, x * y * x⁻¹ ∈ Subgroup.centralizer ({f} : Set G) →
      y ∈ Subgroup.centralizer ({f} : Set G) := fun y hy => mem_centralizer_of_conj hxf hy
  have hcf₂ : ∀ y : G, y ∈ Subgroup.centralizer ({f} : Set G) →
      x⁻¹ * y * x ∈ Subgroup.centralizer ({f} : Set G) := by
    intro y hy
    apply hcf'
    have : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rw [this]
    exact hy
  obtain ⟨w₀, hw₀V', hw₀U⟩ : ∃ w ∈ V', w ∉ U := by
    by_contra hcon
    have hall : ∀ w ∈ V', w ∈ U := fun w hw => by
      by_contra h
      exact hcon ⟨w, hw, h⟩
    have hVY : ∀ v : ↥(U ⊓ Subgroup.centralizer ({f} : Set G)), (v : G) ∈ Y := by
      intro v
      have e : x * (x⁻¹ * (v : G) * x) * x⁻¹ = v := by group
      have h1 : x⁻¹ * (v : G) * x ∈ V' := by
        rw [hV', e]
        exact v.2
      have h2 := hall _ h1
      have h3' : x * (x⁻¹ * (v : G) * x) * x⁻¹ ∈ U := by
        rw [e]
        exact v.2.1
      have h4 : x⁻¹ * (v : G) * x ∈ Y := hYU' _ h2 h3'
      have h5 := (hYx _ h4).1
      rw [e] at h5
      exact h5
    obtain ⟨v, hv⟩ := hβs (Multiplicative.ofAdd ![0, 1])
    have := hβ2 v (hVY v)
    rw [hv] at this
    simp at this
  refine ⟨⟨w₀, hw₀V', hw₀U⟩, fun h3 hne => ?_⟩
  have hw₀C : w₀ ∈ L ⊓ Subgroup.centralizer ({f} : Set G) := hV'C w₀ hw₀V'
  obtain ⟨s₀, hs₀⟩ := (hRα ⟨w₀, hw₀C⟩).1 (hV'R w₀ hw₀V')
  have hs₀ne : s₀ ≠ 0 := by
    intro h
    rw [h, slUpper_zero] at hs₀
    exact hw₀U ((hαk _).1 hs₀)
  have hΘ : ∀ y ∈ Y ⊓ Subgroup.centralizer ({f} : Set G),
      ∃ θ ∈ ⁅U ⊓ Subgroup.centralizer ({f} : Set G), V'⁆,
        ∃ z ∈ Z ⊓ Subgroup.centralizer ({f} : Set G), y = θ * z := by
    intro y hy
    have hyV : y ∈ U ⊓ Subgroup.centralizer ({f} : Set G) := ⟨hYU hy.1, hy.2⟩
    obtain ⟨θ, hθ, z, hzV, hzZ, hyθz⟩ :=
      coord_theta α β hβs hβk hβe hVn hs₀ne hs₀ hw₀V' hβ2 y hy.1 hyV
    exact ⟨θ, hθ, z, ⟨hzZ, hzV.2⟩, hyθz⟩
  have hΘC : ⁅U ⊓ Subgroup.centralizer ({f} : Set G), V'⁆ ≤
      ⁅U ⊓ Subgroup.centralizer ({f} : Set G), L ⊓ Subgroup.centralizer ({f} : Set G)⁆ :=
    Subgroup.commutator_mono le_rfl (fun w hw => hV'C w hw)
  refine le_trans ?_ hΘC
  refine nonsplit_core (x := x⁻¹) (Yf := Y ⊓ Subgroup.centralizer ({f} : Set G))
    (Zf := Z ⊓ Subgroup.centralizer ({f} : Set G)) (Zf' := Zf')
    (Df := D ⊓ Subgroup.centralizer ({f} : Set G)) ?_ ?_ ?_ ?_ ?_ ?_ hΘ ?_ ?_ ?_ h3 hne
  ·
    exact fun a ha b hb => (hYc a ha.1 b (hYR hb.1)).symm
  · exact fun z hz => ⟨hZY hz.1, hz.2⟩
  ·
    intro y hy
    have h1 := (hZf' y).1 hy
    refine ⟨?_, hcf' y h1.2⟩
    have := (hYx _ (hZY h1.1)).2
    have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    rw [e] at this
    exact this
  · intro y hy
    rw [inv_inv]
    exact ⟨(hYx y hy.1).1, hcf y hy.2⟩
  · intro θ hθ
    have hA : ∀ a ∈ U ⊓ Subgroup.centralizer ({f} : Set G), x⁻¹ * a * x⁻¹⁻¹ ∈ V' := by
      intro a ha
      rw [hV']
      have e : x * (x⁻¹ * a * x⁻¹⁻¹) * x⁻¹ = a := by group
      rw [e]
      exact ha
    have hB : ∀ b ∈ V', x⁻¹ * b * x⁻¹⁻¹ ∈ U ⊓ Subgroup.centralizer ({f} : Set G) := by
      intro b hb
      have hv := (hV' b).1 hb
      have e : x⁻¹ * b * x⁻¹⁻¹ = x⁻¹ * (x⁻¹ * (x * b * x⁻¹) * x) * x := by group
      rw [e]
      refine ⟨hx2 _ hv.1, ?_⟩
      have hbC := (hV'C b hb).2
      have : x⁻¹ * b * x⁻¹⁻¹ ∈ Subgroup.centralizer ({f} : Set G) := by
        rw [inv_inv]
        exact hcf₂ b hbC
      rw [← e]
      exact this
    have := conj_mem_commutator' hA hB θ hθ
    rwa [Subgroup.commutator_comm] at this
  · intro z hz
    rw [hZf']
    have e : x * (x⁻¹ * z * x⁻¹⁻¹) * x⁻¹ = z := by group
    rw [e]
    exact hz
  · intro d hd θ hθ
    exact conj_mem_commutator' (hDV d hd) (hDV' d hd) θ hθ
  · intro d hd z hz
    have := hDZc d hd.1 z hz.1
    rw [this]
    group
  · intro a ha ha1 b hb hb1
    have haC : a ∈ Subgroup.centralizer ({f} : Set G) := hcf' a ((hZf' a).1 ha).2
    have hbC : b ∈ Subgroup.centralizer ({f} : Set G) := hcf' b ((hZf' b).1 hb).2
    have hfa : f * a * f⁻¹ = a := by
      have := Subgroup.mem_centralizer_singleton_iff.1 haC
      rw [← this]; group
    have hfb : f * b * f⁻¹ = b := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hbC
      rw [← this]; group
    obtain ⟨d, hd, hfd, hdab⟩ := trans_fixed hfD hfree htr
      ((hZ' a).2 ((hZf' a).1 ha).1) ha1 ((hZ' b).2 ((hZf' b).1 hb).1) hb1 hfa hfb
    have hdinv : d⁻¹ ∈ Subgroup.centralizer ({f} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hfd' : f * d = d * f := by
        calc f * d = f * d * f⁻¹ * f := by group
          _ = d * f := by rw [hfd]
      calc d⁻¹ * f = d⁻¹ * f * d * d⁻¹ := by group
        _ = d⁻¹ * (f * d) * d⁻¹ := by group
        _ = d⁻¹ * (d * f) * d⁻¹ := by rw [hfd']
        _ = f * d⁻¹ := by group
    exact ⟨d⁻¹, ⟨D.inv_mem hd, hdinv⟩, by simpa using hdab⟩

end Abstract

section Config

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem Lin2Cfg.exists_x_fD (h8 : Lemma2_4_8) (hcfg : Lin2Cfg G T M H S L n D)
    {B : Subgroup G} (hB : Lin2BProps T S (thompsonJ S) D B) (hc : centerOf L ≠ ⊥) {f : G}
    (hf : f ∈ S ⊓ Subgroup.normalizer (B : Set G)) (hff : f * f = 1) (hf1 : f ≠ 1) :
    ∃ x ∈ T, x ∉ S ∧ x ∈ Subgroup.normalizer (B : Set G) ∧ f * x = x * f ∧
      (∀ d ∈ D, f * d * f⁻¹ ∈ D) := by
  have hB0 := hB
  obtain ⟨hDB, -, hBab, -, -, -, -, -, hRT, -, hBx⟩ := hB
  obtain ⟨⟨-, hTnS, -⟩, -, -, h4, -, -, -, -, -⟩ := h8 G T M H S L D n hcfg
  obtain ⟨x, hxTB, hxS⟩ : ∃ x ∈ T ⊓ Subgroup.normalizer (B : Set G), x ∉ S := by
    by_contra hcon
    obtain ⟨x₀, hx₀T, hx₀S⟩ := hcfg.exists_mem_T_not_mem_S
    apply hx₀S
    have hle : T ⊓ Subgroup.normalizer (B : Set G) ≤ S := fun y hy => by
      by_contra hyS
      exact hcon ⟨y, hy, hyS⟩
    exact sup_le (thompsonJ_le_self S) hle (hRT.ge hx₀T)
  have hxT : x ∈ T := hxTB.1
  have hxB : x ∈ Subgroup.normalizer (B : Set G) := hxTB.2
  obtain ⟨-, hreg⟩ := h4 x hxT hxS
  obtain ⟨-, -, hDreg⟩ := hreg.resolve_left hc
  have hBeq : B = D ⊔ conjR D x := hBx x hxTB hxS
  have hD'B : conjR D x ≤ B := by rw [hBeq]; exact le_sup_right
  have hZcent : ∀ d ∈ D, ∀ z ∈ centerOf L, d * z = z * d := fun d hd z hz =>
    Subgroup.mem_centralizer_iff.1 hz.2 d (hcfg.D_le_L hd)
  have hfNL : f ∈ Subgroup.normalizer (L : Set G) := hcfg.S_le_normalizer hf.1
  have hfZ : ∀ z ∈ centerOf L, f * z * f⁻¹ ∈ centerOf L := fun z hz =>
    (Subgroup.mem_normalizer_iff.1 (mem_normalizer_centerOf_of_mem hfNL) z).1 hz
  obtain ⟨⟨z₀, hz₀⟩, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc
  have hz₀1' : z₀ ≠ 1 := fun h => hz₀1 (Subtype.ext h)
  have hfree : ∀ b ∈ conjR D x, (∀ z ∈ centerOf L, b * z = z * b) → b = 1 := by
    intro b hb hbz
    refine hDreg.2.2 z₀ ⟨hz₀, hz₀1'⟩ b hb ?_
    have h1 := hbz z₀ hz₀
    calc b⁻¹ * z₀ * b = b⁻¹ * (z₀ * b) := by group
      _ = b⁻¹ * (b * z₀) := by rw [h1]
      _ = z₀ := by group
  have hFcyc : IsCyclic ↥(S ⊓ Subgroup.normalizer (B : Set G)) :=
    (lemma2_4_12_one h8 G T M H S L D n hcfg B hB0).1
  have hxf : x * f * x⁻¹ = f := by
    have hxfS : x * f * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (hTnS hxT) f).1 hf.1
    have hxfB : x * f * x⁻¹ ∈ Subgroup.normalizer (B : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hxB hf.2) (Subgroup.inv_mem _ hxB)
    have hsq : (x * f * x⁻¹) ^ 2 = 1 := by
      rw [sq]
      calc (x * f * x⁻¹) * (x * f * x⁻¹) = x * (f * f) * x⁻¹ := by group
        _ = 1 := by rw [hff]; group
    have hne : x * f * x⁻¹ ≠ 1 := fun h => hf1 (by
      calc f = x⁻¹ * (x * f * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group)
    have hf2 : f ^ 2 = 1 := by rw [sq]; exact hff
    have := hFcyc
    have := eq_of_sq_eq_one_of_isCyclic
      (x := (⟨x * f * x⁻¹, hxfS, hxfB⟩ : ↥(S ⊓ Subgroup.normalizer (B : Set G))))
      (y := (⟨f, hf⟩ : ↥(S ⊓ Subgroup.normalizer (B : Set G))))
      (Subtype.ext hsq) (Subtype.ext hf2) (fun h => hne (congrArg Subtype.val h))
      (fun h => hf1 (congrArg Subtype.val h))
    exact congrArg Subtype.val this
  have hxf' : f * x = x * f := by
    calc f * x = (x * f * x⁻¹) * x := by rw [hxf]
      _ = x * f := by group
  have hBD : ∀ b ∈ B, ∃ d ∈ D, ∃ d' ∈ conjR D x, d * d' = b := by
    intro b hb
    have hD'norm : conjR D x ≤ Subgroup.normalizer (D : Set G) := by
      intro y hy
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact hBab d (hDB hd) y (hD'B hy)
    rw [hBeq] at hb
    obtain ⟨d, hd, d', hd', hdd⟩ := (mem_sup_iff_of_le_normalizer hD'norm).1 hb
    exact ⟨d, hd, d', hd', hdd.symm⟩
  have hfD : ∀ d ∈ D, f * d * f⁻¹ ∈ D := by
    intro d hd
    have hdB : f * d * f⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 hf.2 d).1 (hDB hd)
    obtain ⟨d₁, hd₁, d₁', hd₁', hdd⟩ := hBD _ hdB
    have hcz : ∀ z ∈ centerOf L, (f * d * f⁻¹) * z = z * (f * d * f⁻¹) := by
      intro z hz
      have hz' : f⁻¹ * z * f ∈ centerOf L := by
        have := (Subgroup.mem_normalizer_iff.1
          (Subgroup.inv_mem _ (mem_normalizer_centerOf_of_mem hfNL)) z).1 hz
        simpa using this
      have e := hZcent d hd _ hz'
      calc (f * d * f⁻¹) * z = f * (d * (f⁻¹ * z * f)) * f⁻¹ := by group
        _ = f * ((f⁻¹ * z * f) * d) * f⁻¹ := by rw [e]
        _ = z * (f * d * f⁻¹) := by group
    have hd₁'c : ∀ z ∈ centerOf L, d₁' * z = z * d₁' := by
      intro z hz
      have e := hcz z hz
      rw [← hdd] at e
      have e2 : d₁ * z = z * d₁ := hZcent d₁ hd₁ z hz
      calc d₁' * z = d₁⁻¹ * (d₁ * d₁' * z) := by group
        _ = d₁⁻¹ * (z * (d₁ * d₁')) := by rw [e]
        _ = d₁⁻¹ * (z * d₁) * d₁' := by group
        _ = d₁⁻¹ * (d₁ * z) * d₁' := by rw [e2]
        _ = z * d₁' := by group
    have hd₁'1 : d₁' = 1 := hfree d₁' hd₁' hd₁'c
    rw [← hdd, hd₁'1, mul_one]
    exact hd₁
  exact ⟨x, hxT, hxS, hxB, hxf', hfD⟩

theorem Lin2Cfg.nonsplit (h8 : Lemma2_4_8) (hcfg : Lin2Cfg G T M H S L n D)
    {B : Subgroup G} (hB : Lin2BProps T S (thompsonJ S) D B) (hc : centerOf L ≠ ⊥) {f : G}
    (hf : f ∈ S ⊓ Subgroup.normalizer (B : Set G)) (hf1 : f ≠ 1) (hff : f * f = 1)
    {F : Type} [Field F]
    (α : ↥(L ⊓ Subgroup.centralizer ({f} : Set G)) →* SL(2, F))
    (β : ↥(blockU L ⊓ Subgroup.centralizer ({f} : Set G)) →* Multiplicative (Fin 2 → F))
    (hαs : Function.Surjective α) (hαk : ∀ c, α c = 1 ↔ (c : G) ∈ blockU L)
    (hRα : ∀ c : ↥(L ⊓ Subgroup.centralizer ({f} : Set G)),
      (c : G) ∈ thompsonJ S ↔ ∃ s : F, α c = slUpper s)
    (hβs : Function.Surjective β) (hβk : ∀ v, β v = 1 ↔ (v : G) ∈ blockZ L)
    (hβe : ∀ (c : ↥(L ⊓ Subgroup.centralizer ({f} : Set G)))
        (u v : ↥(blockU L ⊓ Subgroup.centralizer ({f} : Set G))),
        (v : G) = c * u * c⁻¹ →
          Multiplicative.toAdd (β v) =
            (α c : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))) :
    (∃ t ∈ L ⊓ Subgroup.centralizer ({f} : Set G), t * t = 1 ∧ t ∉ blockU L) ∧
      (4 ≤ Nat.card (blockZ L ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) →
        blockZ L ⊓ Subgroup.centralizer ({f} : Set G) ≤
          ⁅blockU L ⊓ Subgroup.centralizer ({f} : Set G),
            L ⊓ Subgroup.centralizer ({f} : Set G)⁆) := by
  obtain ⟨x, hxT, hxS, hxB, hfx, hfD⟩ := hcfg.exists_x_fD h8 hB hc hf hff hf1
  obtain ⟨hOL, hUel, hLU⟩ := hcfg.block_facts h8
  obtain ⟨⟨hidx, hTnS, hTnR⟩, -, ⟨-, hRsyl, h3⟩, h4, -, -, -, -, -⟩ := h8 G T M H S L D n hcfg
  obtain ⟨hRUU, hZR, -, -⟩ := h3 x hxT hxS
  obtain ⟨hDB, -, -, -, -, -, -, -, -, -, hBx⟩ := hB
  have hxf : x * f = f * x := hfx.symm
  have hZeq : blockZ L = centerOf L := blockZ_eq_centerOf hcfg.charTwo_L hOL
  have hRL : thompsonJ S ≤ L := hRsyl.1
  have hUR : blockU L ≤ thompsonJ S := by rw [hRUU]; exact le_sup_left
  have hU'R : conjR (blockU L) x ≤ thompsonJ S := by rw [hRUU]; exact le_sup_right
  have hxR : x ∈ Subgroup.normalizer (thompsonJ S : Set G) := hTnR hxT
  have hxN : x ∈ Subgroup.normalizer ((centerOf (thompsonJ S) : Subgroup G) : Set G) :=
    mem_normalizer_centerOf_of_mem hxR
  have hx2S : x * x ∈ S := by
    have hSN : (S.subgroupOf T).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hcfg.S_le_T).2 hTnS
    have h1 := Subgroup.pow_index_mem (S.subgroupOf T) (⟨x, hxT⟩ : ↥T)
    rw [show (S.subgroupOf T).index = 2 from hidx, pow_two] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  have hx2 : ∀ u ∈ blockU L, x⁻¹ * (x⁻¹ * u * x) * x ∈ blockU L := by
    intro u hu
    have hN : x * x ∈ Subgroup.normalizer (blockU L : Set G) :=
      mem_normalizer_blockU_of (hcfg.S_le_normalizer hx2S)
    have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hN) u).1 hu
    have e : (x * x)⁻¹ * u * ((x * x)⁻¹)⁻¹ = x⁻¹ * (x⁻¹ * u * x) * x := by
      simp only [mul_inv_rev, inv_inv, mul_assoc]
    rwa [e] at h1
  have hDxL := (h4 x hxT hxS).1
  have hBeq : B = D ⊔ conjR D x := hBx x ⟨hxT, hxB⟩ hxS
  have hBN : B ≤ Subgroup.normalizer (blockU L : Set G) := by
    rw [hBeq]
    refine sup_le (fun d hd => ?_) (fun y hy => ?_)
    · exact mem_normalizer_blockU_of (Subgroup.le_normalizer (hcfg.D_le_L hd))
    · exact mem_normalizer_blockU_of (hDxL hy)
  have hBU : ∀ b ∈ B, ∀ u ∈ blockU L, b * u * b⁻¹ ∈ blockU L :=
    fun b hb u hu => (Subgroup.mem_normalizer_iff.1 (hBN hb) u).1 hu
  have hxinvT : x⁻¹ ∈ T := T.inv_mem hxT
  have hxinvS : x⁻¹ ∉ S := fun h => hxS (by simpa using S.inv_mem h)
  obtain ⟨-, hreg'⟩ := h4 x⁻¹ hxinvT hxinvS
  obtain ⟨-, -, -, hDtrans, hDfree⟩ := hreg'.resolve_left hc
  have hZmem : ∀ y, y ∈ conjR (blockZ L) x → x * y * x⁻¹ ∈ centerOf L := fun y hy => by
    rw [← hZeq]
    exact mem_conjR.1 hy
  have hfree : ∀ z ∈ conjR (blockZ L) x, z ≠ 1 → ∀ d ∈ D, d⁻¹ * z * d = z → d = 1 := by
    intro z hz hz1 d hd hdz
    have hz₀1 : x * z * x⁻¹ ≠ 1 := fun h => hz1 (by
      calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group)
    have hb : x * d * x⁻¹ ∈ conjR D x⁻¹ := by
      rw [mem_conjR]
      have e : x⁻¹ * (x * d * x⁻¹) * x⁻¹⁻¹ = d := by group
      rw [e]
      exact hd
    have hfix : (x * d * x⁻¹)⁻¹ * (x * z * x⁻¹) * (x * d * x⁻¹) = x * z * x⁻¹ := by
      calc (x * d * x⁻¹)⁻¹ * (x * z * x⁻¹) * (x * d * x⁻¹) = x * (d⁻¹ * z * d) * x⁻¹ := by group
        _ = x * z * x⁻¹ := by rw [hdz]
    have h1 := hDfree _ ⟨hZmem z hz, hz₀1⟩ _ hb hfix
    calc d = x⁻¹ * (x * d * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  have htr : ∀ a ∈ conjR (blockZ L) x, a ≠ 1 → ∀ b ∈ conjR (blockZ L) x, b ≠ 1 →
      ∃ d ∈ D, d⁻¹ * a * d = b := by
    intro a ha ha1 b hb hb1
    have ha₀1 : x * a * x⁻¹ ≠ 1 := fun h => ha1 (by
      calc a = x⁻¹ * (x * a * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group)
    have hb₀1 : x * b * x⁻¹ ≠ 1 := fun h => hb1 (by
      calc b = x⁻¹ * (x * b * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group)
    obtain ⟨b', hb', hb'e⟩ := hDtrans _ ⟨hZmem a ha, ha₀1⟩ _ ⟨hZmem b hb, hb₀1⟩
    refine ⟨x⁻¹ * b' * x, ?_, ?_⟩
    · have := mem_conjR.1 hb'
      simpa using this
    · have e : (x⁻¹ * b' * x)⁻¹ * a * (x⁻¹ * b' * x) = x⁻¹ * (b'⁻¹ * (x * a * x⁻¹) * b') * x := by
        group
      rw [e, hb'e]
      group
  have hV'R : ∀ w ∈ conjR (blockU L ⊓ Subgroup.centralizer ({f} : Set G)) x,
      w ∈ thompsonJ S := by
    intro w hw
    exact hU'R (mem_conjR.2 (mem_conjR.1 hw).1)
  have hV'C : ∀ w ∈ conjR (blockU L ⊓ Subgroup.centralizer ({f} : Set G)) x,
      w ∈ L ⊓ Subgroup.centralizer ({f} : Set G) := fun w hw =>
    ⟨hRL (hV'R w hw), mem_centralizer_of_conj hxf (mem_conjR.1 hw).2⟩
  have hDV' : ∀ d ∈ D ⊓ Subgroup.centralizer ({f} : Set G),
      ∀ w ∈ conjR (blockU L ⊓ Subgroup.centralizer ({f} : Set G)) x,
        d * w * d⁻¹ ∈ conjR (blockU L ⊓ Subgroup.centralizer ({f} : Set G)) x := by
    intro d hd w hw
    rw [mem_conjR] at hw ⊢
    have hd₃B : x * d * x⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 hxB d).1 (hDB hd.1)
    have hxfc : Commute x f := hxf
    have hdfc : Commute d f := Subgroup.mem_centralizer_singleton_iff.1 hd.2
    have hwfc : Commute (x * w * x⁻¹) f := Subgroup.mem_centralizer_singleton_iff.1 hw.2
    have hd₃c : Commute (x * d * x⁻¹) f := (hxfc.mul_left hdfc).mul_left hxfc.inv_left
    have e : x * (d * w * d⁻¹) * x⁻¹ = (x * d * x⁻¹) * (x * w * x⁻¹) * (x * d * x⁻¹)⁻¹ := by group
    rw [e]
    exact ⟨hBU _ hd₃B _ hw.1, Subgroup.mem_centralizer_singleton_iff.2
      ((hd₃c.mul_left hwfc).mul_left hd₃c.inv_left)⟩
  have hmain := nonsplit_main (R := thompsonJ S) (Y := centerOf (thompsonJ S)) (U := blockU L)
    (Z := blockZ L) (D := D) (V' := conjR (blockU L ⊓ Subgroup.centralizer ({f} : Set G)) x)
    (Z' := conjR (blockZ L) x)
    (Zf' := conjR (blockZ L ⊓ Subgroup.centralizer ({f} : Set G)) x) α β hαs hαk hRα hβs hβk hβe
    (blockV_conj hLU) hxf (fun y => mem_conjR) (fun y => mem_conjR) (fun y => mem_conjR)
    hV'C hV'R
    (fun y hy hy' => by
      rw [← hZR]
      exact ⟨hy, mem_conjR.2 hy'⟩)
    (fun y hy r hr => Subgroup.mem_centralizer_iff.1 hy.2 r hr)
    (fun y hy => hy.1)
    (fun y hy => by
      rw [← hZR] at hy
      exact hy.1)
    (fun z hz => ⟨hUR hz.1, Subgroup.mem_centralizer_iff.2 fun r hr =>
      Subgroup.mem_centralizer_iff.1 hz.2 r (hRL hr)⟩)
    (fun y hy => ⟨(Subgroup.mem_normalizer_iff.1 hxN y).1 hy, by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hxN) y).1 hy
      simpa using this⟩)
    hx2
    (fun d hd z hz => Subgroup.mem_centralizer_iff.1 hz.2 d (hcfg.D_le_L hd))
    (fun d hd v hv => blockV_conj hLU d ⟨hcfg.D_le_L hd.1, hd.2⟩ v hv)
    hDV' hfD hfree htr
  refine ⟨?_, fun hZcard => ?_⟩
  · obtain ⟨w, hwV', hwU⟩ := hmain.1
    have hu : x * w * x⁻¹ ∈ blockU L := (mem_conjR.1 hwV').1
    have hsq : (x * w * x⁻¹) * (x * w * x⁻¹) = 1 := by
      rw [← sq]
      exact hUel.2 _ hu
    have hww : w * w = 1 := by
      calc w * w = x⁻¹ * ((x * w * x⁻¹) * (x * w * x⁻¹)) * x := by group
        _ = 1 := by rw [hsq]; group
    exact ⟨w, hV'C w hwV', hww, hwU⟩
  · have hcardZ' : 4 ≤ Nat.card (conjR (blockZ L ⊓ Subgroup.centralizer ({f} : Set G)) x) := by
      rw [card_conjR]
      exact hZcard
    obtain ⟨hne, h3'⟩ := exists_ne_one_of_card hcardZ'
    exact hmain.2 h3' hne

end Config

end CFSG.QuasithinUnique.Lin2
