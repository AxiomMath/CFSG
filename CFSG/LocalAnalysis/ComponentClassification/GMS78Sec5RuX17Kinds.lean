module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuX16

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS RuSModel

namespace RuSModel

theorem dCode_fix_one : ∀ d : Fin 8, linApply (dCode d) 1 = 1 := by decide

theorem fin8_split2 : ∀ t : Fin 8, t = fin8Of (2 * (t.val / 2)) ^^^ fin8Of (t.val % 2) := by
  decide

theorem fin8Of_mod2 (t : Fin 8) : fin8Of (t.val % 2) = 0 ∨ fin8Of (t.val % 2) = 1 := by
  rcases Nat.mod_two_eq_zero_or_one t.val with h | h <;> rw [h] <;> decide

theorem code_fix_d8 : ∀ r ∈ glList, r.1 = 1 → (r.2.1 = 2 ∨ r.2.1 = 3) →
    ∃ d : Fin 8, r = dCode d := by
  decide +kernel

theorem fin8_eq_of_xor2 : ∀ a b s : Fin 8, a.val % 2 = 0 → b.val % 2 = 0 → (s = 0 ∨ s = 1) →
    b = a ^^^ s → s = 0 := by decide

theorem eta_mem : ((1, 6, 2) : Lin8) ∈ glList := by decide +kernel

theorem eta_inv : ∀ t : Fin 8, linApply (1, 6, 2) (linApply (1, 4, 6) t) = t ∧
    linApply (1, 4, 6) (linApply (1, 6, 2) t) = t := by decide

theorem eta_conj : ∀ t : Fin 8,
    linApply (1, 6, 2) (linApply (dCode 1) (linApply (1, 4, 6) t)) = linApply (dCode 4) t ∧
    linApply (1, 4, 6) (linApply (dCode 5) (linApply (1, 6, 2) t)) = linApply (dCode 4) t := by
  decide

theorem eta_fix : linApply (1, 6, 2) 1 = 1 ∧ linApply (1, 4, 6) 1 = 1 := by decide

theorem inX17_256 : inX17 256 = true := by decide

theorem mul17_zero : ∀ ε : Bool, mul17 ε 0 0 = 0 := by
  intro ε
  rw [mul17_eq]
  cases ε <;> decide

theorem mul17_256 : ∀ ε : Bool, mul17 ε 256 256 = 0 := by
  intro ε
  rw [mul17_eq]
  cases ε <;> decide

theorem xor_lt_four : ∀ s t : Fin 8, s.val < 4 → t.val < 4 → (s ^^^ t).val < 4 := by decide

theorem sMul_one_one (ε : Bool) : sMul ε (0, 1, 0) (0, 1, 0) = (0, 0, 0) := by
  cases ε <;> decide

theorem lift17_256 : lift17 256 = (0, 2, 0) := by decide

theorem enc17_div {x : ℕ × Fin 8 × Fin 8} (hx : x.1 < 256) : enc17 x / 1024 = x.2.2.val := by
  have h1 : x.2.1.val / 2 ≤ 3 := by have := x.2.1.isLt; omega
  simp only [enc17]
  omega

theorem enc17_mod {x : ℕ × Fin 8 × Fin 8} (hx : x.1 < 256) : enc17 x % 256 = x.1 := by
  simp only [enc17]
  omega

theorem lift17_snd (p : ℕ) : (lift17 p).2.2 = fin8Of (p / 1024) := rfl

theorem mem_inv17 {ε : Bool} {u : ℕ} :
    u ∈ inv17 ε ↔ u < 8192 ∧ mul17 ε u u = 0 ∧ u ≠ 0 ∧ u ≠ 256 := by
  simp [inv17, and_assoc]

end RuSModel

section Seventeen

variable {Γ : Type} [Group Γ] {ε : Bool} {φ : ℕ → Γ} {z : Γ}
  (hφ : IsCodeModel 8192 (mul17 ε) φ z) (hz : φ 256 = z)
include hφ hz

theorem mem_inv17_of_conj {g : Γ} {a : ℕ} (ha : a < 8192) (hga : φ a = g * z * g⁻¹)
    (hne : g * z * g⁻¹ ≠ z) : a ∈ inv17 ε := by
  have h1 : φ 0 = 1 := hφ.eq_one (mul17_zero ε)
  have hzz : z * z = 1 := by rw [← hz, ← hφ.mul, mul17_256, h1]
  refine mem_inv17.mpr ⟨ha, ?_, fun h => ?_, fun h => hne ?_⟩
  · refine hφ.inj _ (hφ.lt _ _) _ (by norm_num) ?_
    rw [hφ.mul, hga, h1, show g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, hzz]
    group
  · have hz1 : z = 1 := by
      have : g * z * g⁻¹ = 1 := by rw [← hga, h, h1]
      simpa using this
    have := hφ.inj 256 (by norm_num) 0 (by norm_num) (by rw [hz, h1, hz1])
    norm_num at this
  · rw [← hga, h, hz]

theorem div_of_check17 (hchk : check17 ε = true) {g : Γ}
    (hg : g * z * g⁻¹ * z = z * (g * z * g⁻¹)) {a : ℕ} (ha : a < 8192) (hga : φ a = g * z * g⁻¹)
    (hne : g * z * g⁻¹ ≠ z) (hX : inX17 a = false) : a / 1024 = 1 ∨ a / 1024 = 5 := by
  obtain ⟨-, hK1⟩ := check17_spec hchk
  set V := centralizer ({z} : Set Γ) with hVdef
  have hV : ∀ w, w ∈ V ↔ w * z = z * w := fun w => mem_centralizer_singleton_iff
  have hyV : g⁻¹ * z * g ∈ V := swap_mem hV ((hV _).mpr hg)
  obtain ⟨b, hb, hgb⟩ := hφ.surj _ ((hV _).mp hyV)
  have hyne : g⁻¹ * z * g ≠ z := fun h => hne (by
    calc g * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [h]
      _ = z := by group)
  have hau := mem_inv17_of_conj hφ hz ha hga hne
  have hbu := mem_inv17_of_conj hφ hz (g := g⁻¹) hb (by rw [hgb]; group) (by simpa using hyne)
  have e1 := nCV_swap (g := g) hV
  have e2 := nRV_swap (g := g) hV (g * z * g⁻¹)
  have e3 := nRV_swap (g := g) hV z
  have e4 := nZV_swap (g := g) hV (g * z * g⁻¹)
  have e5 := nZV_swap (g := g) hV z
  rw [show g⁻¹ * (g * z * g⁻¹) * g = z by group] at e2 e4
  rw [← hga, ← hgb, hφ.nCV_eq a, hφ.nCV_eq b] at e1
  rw [← hga, ← hgb, ← hz, hφ.nRV_eq a ha, hφ.nRV_eq b (by norm_num)] at e2
  rw [← hga, ← hgb, ← hz, hφ.nRV_eq a (by norm_num), hφ.nRV_eq b hb] at e3
  rw [← hga, ← hgb, ← hz, hφ.nZV_eq a a, hφ.nZV_eq b 256] at e4
  rw [← hga, ← hgb, ← hz, hφ.nZV_eq a 256, hφ.nZV_eq b b] at e5
  rcases hK1 a hau hX b hbu e1 e2 e3 with ⟨-, h⟩ | h | h
  · exact h
  · exact absurd e4 h
  · exact absurd e5 h

theorem inX17_of_check17 (hchk : check17 ε = true)
    (heta : ∀ a < 8192, (a / 1024 = 1 ∨ a / 1024 = 5) →
      ∃ k : Γ, ∃ a' < 8192, a' / 1024 = 4 ∧ φ a' = k * φ a * k⁻¹)
    {g : Γ} (hg : g * z * g⁻¹ * z = z * (g * z * g⁻¹)) {a : ℕ} (ha : a < 8192)
    (hga : φ a = g * z * g⁻¹) : inX17 a = true := by
  by_contra hX
  rw [Bool.not_eq_true] at hX
  by_cases hne : g * z * g⁻¹ = z
  · have := hφ.inj a ha 256 (by norm_num) (by rw [hga, hne, hz])
    rw [this, inX17_256] at hX
    exact absurd hX (by decide)
  have hdiv := div_of_check17 hφ hz hchk hg ha hga hne hX
  obtain ⟨k, a', ha', hdiv', hka⟩ := heta a ha hdiv
  have hga' : φ a' = (k * g) * z * (k * g)⁻¹ := by rw [hka, hga]; group
  have hg' : (k * g) * z * (k * g)⁻¹ * z = z * ((k * g) * z * (k * g)⁻¹) := by
    rw [← hga']
    exact hφ.mem _ ha'
  have hne' : (k * g) * z * (k * g)⁻¹ ≠ z := by
    intro h
    have := hφ.inj a' ha' 256 (by norm_num) (by rw [hga', h, hz])
    rw [this] at hdiv'
    norm_num at hdiv'
  have hX' : inX17 a' = false := by
    simp [inX17, hdiv']
  have := div_of_check17 hφ hz hchk hg' ha' hga' hne' hX'
  omega

end Seventeen

namespace Sec3.SzR

variable {G : Type} [Group G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8} {ε : Bool}
  {Φ : ℕ × Fin 8 × Fin 8 → G}

omit [Group G] in
theorem mem_zpowers_of_sq [Group G] {f x : G} (hf : f * f = 1) :
    x ∈ zpowers f ↔ x = 1 ∨ x = f := by
  constructor
  · rintro ⟨k, rfl⟩
    have h2 : f ^ (2 : ℤ) = 1 := by rw [zpow_two, hf]
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · left
      show f ^ k = 1
      rw [hm, zpow_mul, h2, one_zpow]
    · right
      show f ^ k = f
      rw [hm, zpow_add_one, zpow_mul, h2, one_zpow, one_mul]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

omit [Group G] in
theorem normal_zpowers_subgroupOf [Group G] {f : G} :
    ((zpowers f).subgroupOf (centralizer ({f} : Set G))).Normal := by
  refine ⟨fun n hn c => ?_⟩
  have hc : (c : G) * f = f * c := mem_centralizer_singleton_iff.mp c.2
  have hle : zpowers f ≤ centralizer ({(c : G)} : Set G) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hc.symm)
  have hnc : (n : G) * c = c * n := mem_centralizer_singleton_iff.mp (hle hn)
  have hcn : (c : G) * n * (c : G)⁻¹ = n := by rw [← hnc]; group
  show ((c * n * c⁻¹ : centralizer ({f} : Set G)) : G) ∈ zpowers f
  simp only [coe_mul, coe_inv, hcn]
  exact hn

section Kinds

variable [Finite G] (hM : MaskCoords L T R μ ν) (hΦ : SModel L T R μ ν ε Φ)
include hM hΦ

omit [Finite G] in
theorem lift17_mem_centralizer (p : ℕ) :
    Φ (lift17 p) ∈ centralizer ({Φ (0, 1, 0)} : Set G) := by
  refine mem_centralizer_singleton_iff.mpr ?_
  have h1 : Φ (lift17 p) * Φ (0, 1, 0) * (Φ (lift17 p))⁻¹ = Φ (0, 1, 0) :=
    hM.eq_of_ν_eq (hM.normA _ (hΦ.mem _) _ (hΦ.mem_A 1)) (hΦ.mem_A 1) (by
      rw [hΦ.code _ _ (hΦ.mem_A 1), hΦ.ν_eq, dCode_fix_one])
  calc Φ (lift17 p) * Φ (0, 1, 0) = Φ (lift17 p) * Φ (0, 1, 0) * (Φ (lift17 p))⁻¹ *
      Φ (lift17 p) := by group
    _ = Φ (0, 1, 0) * Φ (lift17 p) := by rw [h1]

omit [Finite G] hM in
theorem f0_sq : Φ (0, 1, 0) * Φ (0, 1, 0) = 1 := by
  rw [← hΦ.mul, sMul_one_one, hΦ.one]

omit [Finite G] hM in
theorem eq_lift17_mul {r : ℕ × Fin 8 × Fin 8} (hr : r.1 < 256) :
    ∃ k ∈ zpowers (Φ (0, 1, 0)), Φ r = Φ (lift17 (enc17 r)) * k := by
  obtain ⟨c, t, d⟩ := r
  refine ⟨Φ (0, fin8Of (t.val % 2), 0), ?_, ?_⟩
  · rcases fin8Of_mod2 t with h | h <;> rw [h]
    · rw [hΦ.one]; exact one_mem _
    · exact mem_zpowers _
  · have hs : linApply (dCode d) (fin8Of (t.val % 2)) = fin8Of (t.val % 2) := by
      rcases fin8Of_mod2 t with h | h <;> rw [h]
      · exact RuSimCode.linApply_zero _
      · exact dCode_fix_one d
    rw [lift17_enc17 hr, ← hΦ.mul_zero hs, ← fin8_split2 t]

omit [Finite G] in
theorem exists_F₁ : ∃ F : Subgroup G, F ≤ gmsA L T ∧ Nat.card F = 4 ∧
    ∀ b, b ∈ F ↔ b ∈ gmsA L T ∧ (ν b).val < 4 := by
  let F : Subgroup G :=
    { carrier := {b | b ∈ gmsA L T ∧ (ν b).val < 4}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [hM.ν_mul _ ha.1 _ hb.1]; exact xor_lt_four _ _ ha.2 hb.2⟩
      one_mem' := ⟨one_mem _, by rw [hM.ν_one]; decide⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [hM.ν_inv ha.1]; exact ha.2⟩ }
  have hmem : ∀ b, b ∈ F ↔ b ∈ gmsA L T ∧ (ν b).val < 4 := fun b => Iff.rfl
  refine ⟨F, fun b hb => ((hmem b).mp hb).1, ?_, hmem⟩
  have e : F ≃ {s : Fin 8 // s.val < 4} :=
    { toFun := fun b => ⟨ν b, ((hmem b).mp b.2).2⟩
      invFun := fun s => ⟨Φ (0, s, 0), (hmem _).mpr ⟨hΦ.mem_A _, by rw [hΦ.ν_eq]; exact s.2⟩⟩
      left_inv := fun b => Subtype.ext (hM.eq_of_ν_eq (hΦ.mem_A _) ((hmem _).mp b.2).1
        (hΦ.ν_eq _))
      right_inv := fun s => Subtype.ext (hΦ.ν_eq _) }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide

theorem kinds_of_model
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168)
    (h216 : ∀ F₁ : Subgroup G, F₁ ≤ gmsA L T → Nat.card F₁ = 4 →
      normalizer (F₁ : Set G) ≤ normalizer (R : Set G)) :
    ∀ h ∈ centralizer ({Φ (0, 1, 0)} : Set G), ∀ p : ℕ × Fin 8 × Fin 8, p.1 < 256 →
      Φ p = h * Φ (0, 2, 0) * h⁻¹ → Φ p ∈ R ∧ μ (Φ p) ∈ [0, 1, 2, 3] := by
  classical
  have := normal_zpowers_subgroupOf (f := Φ (0, 1, 0))
  set f₀ := Φ (0, 1, 0) with hf₀def
  set f₁ := Φ (0, 2, 0) with hf₁def
  set C := centralizer ({f₀} : Set G) with hCdef
  have hC : ∀ p, Φ (lift17 p) ∈ C := lift17_mem_centralizer hM hΦ
  have hf₀2 : f₀ * f₀ = 1 := f0_sq hΦ
  set π := QuotientGroup.mk' ((zpowers f₀).subgroupOf C) with hπdef
  have hπ : ∀ a b : C, π a = π b ↔ (a : G)⁻¹ * b ∈ zpowers f₀ := fun a b => by
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      mem_subgroupOf]
    rfl
  set φ : ℕ → C ⧸ (zpowers f₀).subgroupOf C := fun p => π ⟨Φ (lift17 p), hC p⟩ with hφdef
  have hf₁C : f₁ ∈ C := by rw [hf₁def, ← lift17_256]; exact hC 256
  have hφ256 : φ 256 = π ⟨f₁, hf₁C⟩ := by simp only [hφdef, lift17_256]; rfl
  have hchk : check17 ε = true := by
    cases ε
    · exact Certificates.certificate15095.2.2.1
    · exact Certificates.certificate15095.2.2.2
  obtain ⟨hK0, -⟩ := check17_spec hchk
  have hφenc : ∀ p : ℕ × Fin 8 × Fin 8, ∀ hp : p.1 < 256, ∀ hpC : Φ p ∈ C,
      φ (enc17 p) = π ⟨Φ p, hpC⟩ := by
    intro p hp hpC
    obtain ⟨k, hk, hpk⟩ := eq_lift17_mul hΦ hp
    simp only [hφdef]
    rw [hπ]
    show (Φ (lift17 (enc17 p)))⁻¹ * Φ p ∈ zpowers f₀
    rw [hpk, inv_mul_cancel_left]
    exact hk
  have hmul : ∀ p q, φ (mul17 ε p q) = φ p * φ q := by
    intro p q
    rw [mul17_eq, hφenc _ (sMul_fst_lt ε (lift17_fst_lt p) _) (by
      rw [hΦ.mul]; exact mul_mem (hC p) (hC q))]
    show π ⟨_, _⟩ = π ⟨Φ (lift17 p), hC p⟩ * π ⟨Φ (lift17 q), hC q⟩
    rw [← map_mul]
    exact congrArg π (Subtype.ext (hΦ.mul _ _))
  have hf₁ν : ν f₁ = 2 := hΦ.ν_eq 2
  have hf₁A : f₁ ∈ gmsA L T := hΦ.mem_A 2
  have hf₀A : f₀ ∈ gmsA L T := hΦ.mem_A 1
  have hf₀ν : ν f₀ = 1 := hΦ.ν_eq 1
  have hfix : ∀ c : C, π c * φ 256 = φ 256 * π c → ∃ p : ℕ × Fin 8 × Fin 8, p.1 < 256 ∧
      Φ p = c := by
    intro c hc
    rw [hφ256, ← map_mul, ← map_mul, hπ] at hc
    have hc' : (c : G)⁻¹ * f₁ * c = f₁ ∨ (c : G)⁻¹ * f₁ * c = f₁ * f₀ := by
      have h1 : f₁⁻¹ * ((c : G)⁻¹ * f₁ * c) ∈ zpowers f₀ := by simpa [mul_assoc] using hc
      rcases (mem_zpowers_of_sq hf₀2).mp h1 with h | h
      · left
        calc (c : G)⁻¹ * f₁ * c = f₁ * (f₁⁻¹ * ((c : G)⁻¹ * f₁ * c)) := by group
          _ = f₁ := by rw [h, mul_one]
      · right
        calc (c : G)⁻¹ * f₁ * c = f₁ * (f₁⁻¹ * ((c : G)⁻¹ * f₁ * c)) := by group
          _ = f₁ * f₀ := by rw [h]
    have hcf₀ : (c : G) * f₀ = f₀ * c := mem_centralizer_singleton_iff.mp c.2
    obtain ⟨F, hFA, hFc, hFm⟩ := exists_F₁ hM hΦ
    have hcN : (c : G) ∈ normalizer (R : Set G) := by
      refine h216 F hFA hFc ?_
      have hinv : (c : G)⁻¹ ∈ normalizer (F : Set G) := by
        refine mem_normalizer_of_conj_mem_of_finite fun b hb => ?_
        rw [inv_inv]
        obtain ⟨hbA, hb4⟩ := (hFm b).mp hb
        have hbΦ : Φ (0, ν b, 0) = b := hM.eq_of_ν_eq (hΦ.mem_A _) hbA (hΦ.ν_eq _)
        have hf₀c : (c : G)⁻¹ * f₀ * c = f₀ := by rw [mul_assoc, ← hcf₀]; group
        have hf₀F : f₀ ∈ F := (hFm _).mpr ⟨hf₀A, by rw [hf₀ν]; decide⟩
        have hf₁F : (c : G)⁻¹ * f₁ * c ∈ F := by
          rcases hc' with h | h <;> rw [h]
          · exact (hFm _).mpr ⟨hf₁A, by rw [hf₁ν]; decide⟩
          · exact mul_mem ((hFm _).mpr ⟨hf₁A, by rw [hf₁ν]; decide⟩) hf₀F
        rw [← hbΦ]
        rcases fin8_lt_four _ hb4 with h | h | h | h <;> rw [h]
        · rw [hΦ.one]; simp
        · rw [hf₀c]; exact hf₀F
        · exact hf₁F
        · have e : Φ (0, 1 ^^^ 2, 0) = f₀ * f₁ := hΦ.mul_zero (by decide)
          rw [e, show (c : G)⁻¹ * (f₀ * f₁) * c = ((c : G)⁻¹ * f₀ * c) * ((c : G)⁻¹ * f₁ * c) by
            group, hf₀c]
          exact mul_mem hf₀F hf₁F
      simpa using inv_mem hinv
    obtain ⟨r, hrGL, hrA, -⟩ := hM.act c hcN
    have hr1 : r.1 = 1 := by
      rw [← RuSimCode.linApply_one, ← hf₀ν, ← hrA _ hf₀A, hcf₀, mul_inv_cancel_right]
    have hr2 : r.2.1 = 2 ∨ r.2.1 = 3 := by
      rw [← RuSimCode.linApply_two, ← hf₁ν, ← hrA _ hf₁A]
      have hcf₀' : (c : G) * f₀ * (c : G)⁻¹ = f₀ := by rw [hcf₀, mul_inv_cancel_right]
      have hcf : (c : G) * f₁ * (c : G)⁻¹ = f₁ ∨ (c : G) * f₁ * (c : G)⁻¹ = f₁ * f₀ := by
        rcases hc' with h | h
        · left
          calc (c : G) * f₁ * (c : G)⁻¹ = (c : G) * ((c : G)⁻¹ * f₁ * c) * (c : G)⁻¹ := by rw [h]
            _ = f₁ := by group
        · right
          have h2 : f₁ = (c : G) * f₁ * (c : G)⁻¹ * f₀ := by
            calc f₁ = (c : G) * ((c : G)⁻¹ * f₁ * c) * (c : G)⁻¹ := by group
              _ = (c : G) * (f₁ * f₀) * (c : G)⁻¹ := by rw [h]
              _ = (c : G) * f₁ * (c : G)⁻¹ * ((c : G) * f₀ * (c : G)⁻¹) := by group
              _ = (c : G) * f₁ * (c : G)⁻¹ * f₀ := by rw [hcf₀']
          calc (c : G) * f₁ * (c : G)⁻¹ = (c : G) * f₁ * (c : G)⁻¹ * f₀ * f₀ := by
                rw [mul_assoc _ f₀ f₀, hf₀2, mul_one]
            _ = f₁ * f₀ := by rw [← h2]
      rcases hcf with h | h <;> rw [h]
      · left; rfl
      · right
        rw [hM.ν_mul _ hf₁A _ hf₀A, hf₁ν, hf₀ν]
        decide
    obtain ⟨d₀, rfl⟩ := code_fix_d8 r hrGL hr1 hr2
    obtain ⟨p₀, hp₀, -, hp₀c⟩ := hΦ.surj c hcN d₀ hrA
    exact ⟨p₀, hp₀, hp₀c⟩
  have hφ : IsCodeModel 8192 (mul17 ε) φ (φ 256) := by
    refine ⟨hmul, mul17_lt ε, fun p hp q hq h => ?_, fun p hp => ?_, fun w hw => ?_⟩
    ·
      have h1 := (hπ _ _).mp h
      obtain ⟨s, hs01, hs⟩ : ∃ s : Fin 8, (s = 0 ∨ s = 1) ∧
          Φ (0, s, 0) = (Φ (lift17 p))⁻¹ * Φ (lift17 q) := by
        rcases (mem_zpowers_of_sq hf₀2).mp h1 with h2 | h2
        · exact ⟨0, Or.inl rfl, by rw [hΦ.one]; exact h2.symm⟩
        · exact ⟨1, Or.inr rfl, h2.symm⟩
      have hfix1 : linApply (dCode (lift17 p).2.2) s = s := by
        rcases hs01 with rfl | rfl
        · exact RuSimCode.linApply_zero _
        · exact dCode_fix_one _
      have h2 : Φ (lift17 q) = Φ ((lift17 p).1, (lift17 p).2.1 ^^^ s, (lift17 p).2.2) := by
        rw [hΦ.mul_zero hfix1, hs]
        group
      have h3 := hΦ.inj (lift17 q) ((lift17 p).1, (lift17 p).2.1 ^^^ s, (lift17 p).2.2)
        (lift17_fst_lt q) (lift17_fst_lt p) h2
      have h4 := fin8_eq_of_xor2 _ _ s (lift17_code p) (lift17_code q) hs01
        (congrArg (fun x => x.2.1) h3)
      rw [h4, RuSimCode.fin8_xor_zero] at h3
      rw [← enc17_lift17 hp, ← enc17_lift17 hq, h3]
    ·
      rw [← hmul, ← hmul, hK0 p hp]
    ·
      obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective ((zpowers f₀).subgroupOf C) w
      obtain ⟨p₀, hp₀, hp₀c⟩ := hfix c hw
      refine ⟨enc17 p₀, enc17_lt hp₀, ?_⟩
      rw [hφenc p₀ hp₀ (by rw [hp₀c]; exact c.2)]
      exact congrArg π (Subtype.ext hp₀c)
  obtain ⟨η, hηN, hηA, -⟩ := hM.exists_code_eq hNC hidx eta_mem
  have hηiA : ∀ b ∈ gmsA L T, ν (η⁻¹ * b * η⁻¹⁻¹) = linApply (1, 4, 6) (ν b) := by
    intro b hb
    have hb' : η⁻¹ * b * η ∈ gmsA L T := hM.inv_conj_mem hηN hb
    have h1 := hηA _ hb'
    rw [show η * (η⁻¹ * b * η) * η⁻¹ = b by group] at h1
    rw [inv_inv, h1, (eta_inv _).2]
  have hηC : η ∈ C := by
    refine mem_centralizer_singleton_iff.mpr ?_
    have h1 : η * f₀ * η⁻¹ = f₀ :=
      hM.eq_of_ν_eq (hM.normA _ hηN _ hf₀A) hf₀A (by rw [hηA _ hf₀A, hf₀ν, eta_fix.1])
    calc η * f₀ = η * f₀ * η⁻¹ * η := by group
      _ = f₀ * η := by rw [h1]
  have heta : ∀ a < 8192, (a / 1024 = 1 ∨ a / 1024 = 5) →
      ∃ k : C ⧸ (zpowers f₀).subgroupOf C, ∃ a' < 8192, a' / 1024 = 4 ∧
        φ a' = k * φ a * k⁻¹ := by
    intro a ha hdiv
    obtain ⟨κ, hκC, hκN, hκ⟩ : ∃ κ ∈ C, κ ∈ normalizer (R : Set G) ∧ ∀ b ∈ gmsA L T,
        ν (κ * Φ (lift17 a) * κ⁻¹ * b * (κ * Φ (lift17 a) * κ⁻¹)⁻¹) =
          linApply (dCode 4) (ν b) := by
      have hd : (lift17 a).2.2 = 1 ∨ (lift17 a).2.2 = 5 := by
        rw [lift17_snd]
        rcases hdiv with h | h <;> [left; right] <;> ext <;> simp [fin8Of, h]
      rcases hd with hd | hd
      · refine ⟨η, hηC, hηN, fun b hb => ?_⟩
        rw [hM.code_mul (inv_mem hηN) (hM.code_mul (hΦ.mem _) hηA (hΦ.code _)) hηiA b hb,
          RuSimCode.linApply_linComp, RuSimCode.linApply_linComp, hd, (eta_conj _).1]
      · refine ⟨η⁻¹, inv_mem hηC, inv_mem hηN, fun b hb => ?_⟩
        have hηA' : ∀ b ∈ gmsA L T, ν (η⁻¹⁻¹ * b * η⁻¹⁻¹⁻¹) = linApply (1, 6, 2) (ν b) := by
          simpa using hηA
        rw [hM.code_mul (inv_mem (inv_mem hηN)) (hM.code_mul (hΦ.mem _) hηiA (hΦ.code _))
          hηA' b hb, RuSimCode.linApply_linComp, RuSimCode.linApply_linComp, hd,
          (eta_conj _).2]
    have hxN : κ * Φ (lift17 a) * κ⁻¹ ∈ normalizer (R : Set G) :=
      mul_mem (mul_mem hκN (hΦ.mem _)) (inv_mem hκN)
    obtain ⟨p', hp', hp'd, hp'c⟩ := hΦ.surj _ hxN 4 hκ
    have hxC : κ * Φ (lift17 a) * κ⁻¹ ∈ C := mul_mem (mul_mem hκC (hC a)) (inv_mem hκC)
    refine ⟨π ⟨κ, hκC⟩, enc17 p', enc17_lt hp', by rw [enc17_div hp', hp'd]; rfl, ?_⟩
    rw [hφenc p' hp' (by rw [hp'c]; exact hxC)]
    simp only [hφdef, ← map_mul, ← map_inv]
    exact congrArg π (Subtype.ext hp'c)
  intro h hh p hp hph
  have hpC : Φ p ∈ C := by rw [hph]; exact mul_mem (mul_mem hh hf₁C) (inv_mem hh)
  have hga : φ (enc17 p) = π ⟨h, hh⟩ * φ 256 * (π ⟨h, hh⟩)⁻¹ := by
    rw [hφenc p hp hpC, hφ256, ← map_mul, ← map_inv, ← map_mul]
    exact congrArg π (Subtype.ext hph)
  have hg : π ⟨h, hh⟩ * φ 256 * (π ⟨h, hh⟩)⁻¹ * φ 256 =
      φ 256 * (π ⟨h, hh⟩ * φ 256 * (π ⟨h, hh⟩)⁻¹) := by
    rw [← hga]
    exact hφ.mem _ (enc17_lt hp)
  have hX := inX17_of_check17 hφ rfl hchk heta hg (enc17_lt hp) hga
  simp only [inX17, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hX
  rw [enc17_div hp, enc17_mod hp] at hX
  obtain ⟨hd0, hm4⟩ := hX
  have hp0 : p = (p.1, p.2.1, 0) := by
    ext <;> simp [hd0]
  rw [hp0]
  refine ⟨hΦ.mem_R _ _, ?_⟩
  rw [hΦ.μ_eq]
  have : sMask p.1 < 4 := hm4
  interval_cases (sMask p.1) <;> simp

end Kinds

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
