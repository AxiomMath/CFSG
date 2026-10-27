module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

public section

namespace CFSG

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem inv_mul_commutatorElement_mul_mem {P V : Subgroup G}
    (hPP : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ V) {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) {x y : G} (hx : x ∈ P) (hy : y ∈ P) :
    (⁅g, x⁆ * ⁅g, y⁆)⁻¹ * ⁅g, x * y⁆ ∈ V := by
  have hgx : g * x * g⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hgy : g * y * g⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  have hx' : ⁅g, x⁆ ∈ P := by
    have := P.mul_mem hgx (P.inv_mem hx)
    simpa only [commutatorElement_def] using this
  have hy' : ⁅g, y⁆ ∈ P := by
    have := P.mul_mem hgy (P.inv_mem hy)
    simpa only [commutatorElement_def] using this
  have heq : (⁅g, x⁆ * ⁅g, y⁆)⁻¹ * ⁅g, x * y⁆ = ⁅⁅g, y⁆⁻¹, x⁆ := by
    simp only [commutatorElement_def]
    group
  rw [heq]
  exact hPP _ (P.inv_mem hy') _ hx

theorem inv_mul_commutatorElement_commutatorElement_mul_mem {P V : Subgroup G}
    (hPP : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ V) {a b : G}
    (ha : a ∈ Subgroup.normalizer (P : Set G)) (hb : b ∈ Subgroup.normalizer (P : Set G))
    (haV : ∀ v ∈ V, a * v = v * a) {x y : G} (hx : x ∈ P) (hy : y ∈ P) :
    (⁅a, ⁅b, x⁆⁆ * ⁅a, ⁅b, y⁆⁆)⁻¹ * ⁅a, ⁅b, x * y⁆⁆ ∈ V := by
  have hbxy := inv_mul_commutatorElement_mul_mem hPP hb hx hy
  have hmemx : ⁅b, x⁆ ∈ P := by
    have h1 : b * x * b⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hb x).mp hx
    simpa only [commutatorElement_def] using P.mul_mem h1 (P.inv_mem hx)
  have hmemy : ⁅b, y⁆ ∈ P := by
    have h1 : b * y * b⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hb y).mp hy
    simpa only [commutatorElement_def] using P.mul_mem h1 (P.inv_mem hy)
  obtain ⟨r, hrV, hr⟩ : ∃ r ∈ V, ⁅b, x * y⁆ = ⁅b, x⁆ * ⁅b, y⁆ * r := by
    exact ⟨(⁅b, x⁆ * ⁅b, y⁆)⁻¹ * ⁅b, x * y⁆, hbxy, by group⟩
  have har : r * a⁻¹ = a⁻¹ * r := by
    have h := congrArg (fun t => a⁻¹ * t * a⁻¹) (haV r hrV)
    simpa [mul_assoc] using h
  have heq : ⁅a, ⁅b, x * y⁆⁆ = ⁅a, ⁅b, x⁆ * ⁅b, y⁆⁆ := by
    rw [hr]
    simp only [commutatorElement_def]
    calc
      a * (⁅b, x⁆ * ⁅b, y⁆ * r) * a⁻¹ * (⁅b, x⁆ * ⁅b, y⁆ * r)⁻¹
          = a * (⁅b, x⁆ * ⁅b, y⁆) * (r * a⁻¹) * r⁻¹ * (⁅b, x⁆ * ⁅b, y⁆)⁻¹ := by
            group
      _ = a * (⁅b, x⁆ * ⁅b, y⁆) * (a⁻¹ * r) * r⁻¹ * (⁅b, x⁆ * ⁅b, y⁆)⁻¹ := by
            rw [har]
      _ = a * (⁅b, x⁆ * ⁅b, y⁆) * a⁻¹ * (⁅b, x⁆ * ⁅b, y⁆)⁻¹ := by
            group
  have hmain := inv_mul_commutatorElement_mul_mem hPP ha hmemx hmemy
  rw [heq]
  exact hmain

private theorem inv_mul_mem_of_spread_of_not_mem {V E : Subgroup G}
    (hVE : ∀ v ∈ V, ∀ x ∈ E, v * x = x * v) {𝒜 : Set (Subgroup G)}
    (hVA : ∀ A ∈ 𝒜, V ≤ A) (hAE : ∀ A ∈ 𝒜, A ≤ E)
    (hcover : ∀ x ∈ E, ∃ A ∈ 𝒜, x ∈ A)
    (hdisj : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A = B ∨ A ⊓ B = V) {f : G → G}
    (hadd : ∀ x ∈ E, ∀ y ∈ E, (f x * f y)⁻¹ * f (x * y) ∈ V)
    (hf : ∀ A ∈ 𝒜, ∀ x ∈ A, f x ∈ A) {A₀ : Subgroup G} (hA₀ : A₀ ∈ 𝒜) {x₀ : G}
    (hx₀ : x₀ ∈ A₀) (hx₀V : x₀ ∉ V) (hfx₀ : x₀⁻¹ * f x₀ ∈ V) {x : G} (hx : x ∈ E)
    (hxA₀ : x ∉ A₀) : x⁻¹ * f x ∈ V := by
  have hx₀E : x₀ ∈ E := hAE A₀ hA₀ hx₀
  obtain ⟨B, hB, hxB⟩ := hcover x hx
  obtain ⟨C, hC, hx₀xC⟩ := hcover (x₀ * x) (E.mul_mem hx₀E hx)
  have hBC : B ≠ C := by
    intro hEq
    have hx₀B : x₀ ∈ B := by
      have hxinv : x⁻¹ ∈ B := B.inv_mem hxB
      have hx₀eq : x₀ = (x₀ * x) * x⁻¹ := by group
      rw [hx₀eq]
      exact B.mul_mem (hEq ▸ hx₀xC) hxinv
    have hA₀B : A₀ ≠ B := by
      intro hAB
      apply hxA₀
      rw [hAB]
      exact hxB
    rcases hdisj A₀ hA₀ B hB with hAB | hAB
    · exact hA₀B hAB
    · have hmem : x₀ ∈ A₀ ⊓ B := ⟨hx₀, hx₀B⟩
      rw [hAB] at hmem
      exact hx₀V hmem
  have hxuB : x⁻¹ * f x ∈ B :=
    B.mul_mem (B.inv_mem hxB) (hf B hB x hxB)
  have hxuC : x⁻¹ * f x ∈ C := by
    let v₂ : G := x₀⁻¹ * f x₀
    let v₁ : G := (f x₀ * f x)⁻¹ * f (x₀ * x)
    have hv₂ : v₂ ∈ V := hfx₀
    have hv₁ : v₁ ∈ V := hadd x₀ hx₀E x hx
    have hz : f (x₀ * x) = x₀ * v₂ * f x * v₁ := by
      dsimp only [v₂, v₁]
      group
    have hxinv : x⁻¹ * v₂ = v₂ * x⁻¹ := by
      have h := congrArg (fun t => x⁻¹ * t * x⁻¹) (hVE v₂ hv₂ x hx)
      simpa [mul_assoc] using h
    have hw : (x₀ * x)⁻¹ * f (x₀ * x) = v₂ * (x⁻¹ * f x) * v₁ := by
      rw [hz]
      calc
        (x₀ * x)⁻¹ * (x₀ * v₂ * f x * v₁) = x⁻¹ * v₂ * f x * v₁ := by group
        _ = v₂ * (x⁻¹ * f x) * v₁ := by rw [hxinv]; group
    have hstep : x⁻¹ * f x =
        v₂⁻¹ * ((x₀ * x)⁻¹ * f (x₀ * x)) * v₁⁻¹ := by
      rw [hw]
      group
    rw [hstep]
    refine C.mul_mem (C.mul_mem (hVA C hC (V.inv_mem hv₂)) ?_)
      (hVA C hC (V.inv_mem hv₁))
    exact C.mul_mem (C.inv_mem hx₀xC) (hf C hC (x₀ * x) hx₀xC)
  have hBCdisj : B ⊓ C = V := by
    rcases hdisj B hB C hC with hEq | hInf
    · exact absurd hEq hBC
    · exact hInf
  rw [← hBCdisj]
  exact ⟨hxuB, hxuC⟩

theorem inv_mul_mem_of_spread {V E : Subgroup G}
    (hVE : ∀ v ∈ V, ∀ x ∈ E, v * x = x * v) {𝒜 : Set (Subgroup G)}
    (hVA : ∀ A ∈ 𝒜, V ≤ A) (hAE : ∀ A ∈ 𝒜, A ≤ E)
    (hcover : ∀ x ∈ E, ∃ A ∈ 𝒜, x ∈ A)
    (hdisj : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A = B ∨ A ⊓ B = V)
    (hout : ∀ A ∈ 𝒜, ∃ x ∈ E, x ∉ A) {f : G → G}
    (hadd : ∀ x ∈ E, ∀ y ∈ E, (f x * f y)⁻¹ * f (x * y) ∈ V)
    (hf : ∀ A ∈ 𝒜, ∀ x ∈ A, f x ∈ A) {x₀ : G} (hx₀ : x₀ ∈ E) (hx₀V : x₀ ∉ V)
    (hfx₀ : x₀⁻¹ * f x₀ ∈ V) : ∀ x ∈ E, x⁻¹ * f x ∈ V := by
  obtain ⟨A₀, hA₀, hx₀A₀⟩ := hcover x₀ hx₀
  intro x hx
  by_cases hxA₀ : x ∈ A₀
  · obtain ⟨w, hwE, hwA₀⟩ := hout A₀ hA₀
    have hxwA₀ : x * w ∉ A₀ := by
      intro hxw
      apply hwA₀
      have hw_eq : w = x⁻¹ * (x * w) := by group
      rw [hw_eq]
      exact A₀.mul_mem (A₀.inv_mem hxA₀) hxw
    have hwV : w⁻¹ * f w ∈ V :=
      inv_mul_mem_of_spread_of_not_mem hVE hVA hAE hcover hdisj hadd hf hA₀ hx₀A₀ hx₀V
        hfx₀ hwE hwA₀
    have hxwV : (x * w)⁻¹ * f (x * w) ∈ V :=
      inv_mul_mem_of_spread_of_not_mem hVE hVA hAE hcover hdisj hadd hf hA₀ hx₀A₀ hx₀V
        hfx₀ (E.mul_mem hx hwE) hxwA₀
    let u : G := x⁻¹ * f x
    let v : G := (f x * f w)⁻¹ * f (x * w)
    let z : G := w⁻¹ * f w
    have hv : v ∈ V := hadd x hx w hwE
    have hz : z ∈ V := hwV
    have hcalc : w⁻¹ * u * w = ((x * w)⁻¹ * f (x * w)) * v⁻¹ * z⁻¹ := by
      dsimp only [u, v, z]
      group
    have huw : w⁻¹ * u * w ∈ V := by
      rw [hcalc]
      exact V.mul_mem (V.mul_mem hxwV (V.inv_mem hv)) (V.inv_mem hz)
    have hcent : w * (w⁻¹ * u * w) = (w⁻¹ * u * w) * w :=
      (hVE (w⁻¹ * u * w) huw w hwE).symm
    have hu_eq : u = w⁻¹ * u * w := by
      calc
        u = w * (w⁻¹ * u * w) * w⁻¹ := by group
        _ = (w⁻¹ * u * w) * w * w⁻¹ := by rw [hcent]
        _ = w⁻¹ * u * w := by group
    change u ∈ V
    rwa [hu_eq]
  · exact inv_mul_mem_of_spread_of_not_mem hVE hVA hAE hcover hdisj hadd hf hA₀ hx₀A₀ hx₀V
      hfx₀ hx hxA₀


theorem braid_cube_eq {Q : Type*} [Group Q] (hcomm : ∀ x y : Q, x * y = y * x)
    (hQ : ∀ y : Q, y * y = 1) (α β : Q →* Q)
    (hαα : ∀ y, α (α y) = 1) (hββ : ∀ y, β (β y) = 1)
    (hαβα : ∀ y, α (β (α y)) = α y) (hβαβ : ∀ y, β (α (β y)) = β y)
    {s t : Q → Q} (hs : ∀ y, s y = α y * y) (ht : ∀ y, t y = β y * y) (y : Q) :
    s (t (s (t (s (t y))))) = y := by
  letI : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
  have hconj : ∀ x z : Q, x * z * x = z := by
    intro x z
    calc
      x * z * x = z * x * x := by rw [mul_comm x z]
      _ = z * (x * x) := by rw [mul_assoc]
      _ = z * 1 := by rw [hQ x]
      _ = z := by rw [mul_one]
  have h1 : t y = β y * y := ht y
  have h2 : s (t y) = α (β y) * α y * β y * y := by
    rw [h1, hs, map_mul]
    group
  have h3 : t (s (t y)) = β (α y) * α (β y) * α y * β y * y := by
    rw [h2, ht]
    simp only [map_mul, hβαβ, hββ, mul_one]
    rw [hconj (β y) (β (α y))]
    group
  have h4 : s (t (s (t y))) = β (α y) * α y * β y * y := by
    rw [h3, hs]
    simp only [map_mul, hαα, hαβα, mul_one]
    calc
      (α y * α (β y) * α y) * (β (α y) * α (β y) * α y * β y * y)
          = α (β y) * (β (α y) * α (β y) * α y * β y * y) := by
            rw [hconj (α y) (α (β y))]
      _ = (α (β y) * β (α y) * α (β y)) * (α y * β y * y) := by group
      _ = β (α y) * (α y * β y * y) := by
            rw [hconj (α (β y)) (β (α y))]
      _ = β (α y) * α y * β y * y := by group
  have h5 : t (s (t (s (t y)))) = α y * y := by
    rw [h4, ht]
    simp only [map_mul, hββ, mul_one, one_mul]
    calc
      (β (α y) * β y) * (β (α y) * α y * β y * y)
          = (β (α y) * β y * β (α y)) * (α y * β y * y) := by group
      _ = β y * (α y * β y * y) := by
            rw [hconj (β (α y)) (β y)]
      _ = (β y * α y * β y) * y := by group
      _ = α y * y := by rw [hconj (β y) (α y)]
  rw [h5, hs]
  simp only [map_mul, hαα, mul_one, one_mul]
  calc
    α y * (α y * y) = (α y * α y) * y := by group
    _ = y := by rw [hQ (α y), one_mul]

private theorem quotient_comm_and_mul_self {P V : Subgroup G} [(V.subgroupOf P).Normal]
    (hPP : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ V) (hsq : ∀ x ∈ P, x * x ∈ V) :
    (∀ x y : ↥P ⧸ V.subgroupOf P, x * y = y * x) ∧
      ∀ x : ↥P ⧸ V.subgroupOf P, x * x = 1 := by
  constructor
  · intro x y
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        rw [Subgroup.mem_subgroupOf]
        have h := hPP (y : G)⁻¹ (P.inv_mem y.2) (x : G)⁻¹ (P.inv_mem x.2)
        convert h using 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow,
          commutatorElement_def]
        group
  · intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hsq (x : G) x.2


private def commutatorIn (P : Subgroup G) {a : G}
    (haP : a ∈ Subgroup.normalizer (P : Set G)) (x : ↥P) : ↥P :=
  ⟨⁅a, (x : G)⁆, by
    have h1 : a * (x : G) * a⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp haP (x : G)).mp x.2
    simpa only [commutatorElement_def] using P.mul_mem h1 (P.inv_mem x.2)⟩

private noncomputable def quotientConjAut (P V : Subgroup G) [(V.subgroupOf P).Normal] (a : G)
    (haP : a ∈ Subgroup.normalizer (P : Set G))
    (haV : a ∈ Subgroup.normalizer (V : Set G)) :
    ↥P ⧸ V.subgroupOf P ≃* ↥P ⧸ V.subgroupOf P :=
  QuotientGroup.congr (V.subgroupOf P) (V.subgroupOf P)
    (Subgroup.normalizerMonoidHom P ⟨a, haP⟩) (by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [Subgroup.mem_subgroupOf]
        have hy' : (y : G) ∈ V := hy
        change a * (y : G) * a⁻¹ ∈ V
        exact (Subgroup.mem_normalizer_iff.mp haV (y : G)).mp hy'
      · intro hx
        rw [Subgroup.mem_subgroupOf] at hx
        refine ⟨⟨a⁻¹ * (x : G) * a, ?_⟩, ?_, ?_⟩
        · simpa using
            (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haP) (x : G)).mp x.2
        · exact Subgroup.mem_subgroupOf.mpr (by
            simpa using
              (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haV) (x : G)).mp hx)
        · apply Subtype.ext
          show a * (a⁻¹ * (x : G) * a) * a⁻¹ = (x : G)
          group)

private theorem quotientConjAut_mk {P V : Subgroup G} [(V.subgroupOf P).Normal] (a : G)
    (haP : a ∈ Subgroup.normalizer (P : Set G))
    (haV : a ∈ Subgroup.normalizer (V : Set G)) (x : ↥P) :
    quotientConjAut P V a haP haV (QuotientGroup.mk x) =
      QuotientGroup.mk ⟨a * (x : G) * a⁻¹,
        (Subgroup.mem_normalizer_iff.mp haP (x : G)).mp x.2⟩ := by
  rw [quotientConjAut, QuotientGroup.congr_mk]
  apply congrArg QuotientGroup.mk
  apply Subtype.ext
  rfl

private theorem quotientConjAut_mk_mul_inv {P V : Subgroup G} [(V.subgroupOf P).Normal] (a : G)
    (haP : a ∈ Subgroup.normalizer (P : Set G))
    (haV : a ∈ Subgroup.normalizer (V : Set G)) (x : ↥P) :
    quotientConjAut P V a haP haV (QuotientGroup.mk x) * (QuotientGroup.mk x)⁻¹ =
      QuotientGroup.mk (commutatorIn P haP x) := by
  rw [quotientConjAut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  rfl

private def transvectionHom {Q : Type*} [Group Q] (s : Q ≃* Q)
    (hcomm : ∀ x y : Q, x * y = y * x) : Q →* Q :=
  MonoidHom.mk' (fun q => s q * q⁻¹) (by
    intro p q
    calc
      s (p * q) * (p * q)⁻¹ = (s p * s q) * (q⁻¹ * p⁻¹) := by
        rw [map_mul, mul_inv_rev]
      _ = s p * ((s q * q⁻¹) * p⁻¹) := by group
      _ = s p * (p⁻¹ * (s q * q⁻¹)) := by rw [hcomm (s q * q⁻¹) p⁻¹]
      _ = s p * p⁻¹ * (s q * q⁻¹) := by group)

private noncomputable def quotientTransvection (P V : Subgroup G) [(V.subgroupOf P).Normal]
    (hPP : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ V) (hsq : ∀ x ∈ P, x * x ∈ V) (a : G)
    (haP : a ∈ Subgroup.normalizer (P : Set G))
    (haV : a ∈ Subgroup.normalizer (V : Set G)) :
    (↥P ⧸ V.subgroupOf P) →* (↥P ⧸ V.subgroupOf P) :=
  transvectionHom (quotientConjAut P V a haP haV) (quotient_comm_and_mul_self hPP hsq).1

private theorem quotientTransvection_apply {P V : Subgroup G} [(V.subgroupOf P).Normal]
    (hPP : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ V) (hsq : ∀ x ∈ P, x * x ∈ V) (a : G)
    (haP : a ∈ Subgroup.normalizer (P : Set G))
    (haV : a ∈ Subgroup.normalizer (V : Set G)) (q : ↥P ⧸ V.subgroupOf P) :
    quotientTransvection P V hPP hsq a haP haV q =
      quotientConjAut P V a haP haV q * q⁻¹ := rfl

private theorem quotientTransvection_mk {P V : Subgroup G} [(V.subgroupOf P).Normal]
    (hPP : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ V) (hsq : ∀ x ∈ P, x * x ∈ V) (a : G)
    (haP : a ∈ Subgroup.normalizer (P : Set G))
    (haV : a ∈ Subgroup.normalizer (V : Set G)) (x : ↥P) :
    quotientTransvection P V hPP hsq a haP haV (QuotientGroup.mk x) =
      QuotientGroup.mk (commutatorIn P haP x) := by
  rw [quotientTransvection_apply, quotientConjAut_mk_mul_inv]

private theorem quotientTransvection_sq {P V : Subgroup G} [(V.subgroupOf P).Normal]
    (hPP : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ V) (hsq : ∀ x ∈ P, x * x ∈ V) {a : G}
    (haP : a ∈ Subgroup.normalizer (P : Set G))
    (haV : a ∈ Subgroup.normalizer (V : Set G))
    (hαα : ∀ x ∈ P, ⁅a, ⁅a, x⁆⁆ ∈ V) :
    ∀ q : ↥P ⧸ V.subgroupOf P,
      quotientTransvection P V hPP hsq a haP haV
        (quotientTransvection P V hPP hsq a haP haV q) = 1 := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    simp only [quotientTransvection_mk]
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa only [commutatorIn] using hαα (x : G) x.2

private theorem quotientTransvection_beta_sq {P V : Subgroup G} [(V.subgroupOf P).Normal]
    (hPP : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ V) (hsq : ∀ x ∈ P, x * x ∈ V) {b : G}
    (hbP : b ∈ Subgroup.normalizer (P : Set G))
    (hbV : b ∈ Subgroup.normalizer (V : Set G))
    (hββ : ∀ x ∈ P, ⁅b, ⁅b, x⁆⁆ ∈ V) :
    ∀ q : ↥P ⧸ V.subgroupOf P,
      quotientTransvection P V hPP hsq b hbP hbV
        (quotientTransvection P V hPP hsq b hbP hbV q) = 1 := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    simp only [quotientTransvection_mk]
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa only [commutatorIn] using hββ (x : G) x.2

private theorem quotientTransvection_alpha_beta_alpha {P V : Subgroup G}
    [(V.subgroupOf P).Normal]
    (hPP : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ V) (hsq : ∀ x ∈ P, x * x ∈ V) {a b : G}
    (haP : a ∈ Subgroup.normalizer (P : Set G))
    (haV : a ∈ Subgroup.normalizer (V : Set G))
    (hbP : b ∈ Subgroup.normalizer (P : Set G))
    (hbV : b ∈ Subgroup.normalizer (V : Set G))
    (hαβα : ∀ x ∈ P, ⁅a, x⁆⁻¹ * ⁅a, ⁅b, ⁅a, x⁆⁆⁆ ∈ V) :
    ∀ q : ↥P ⧸ V.subgroupOf P,
      quotientTransvection P V hPP hsq a haP haV
        (quotientTransvection P V hPP hsq b hbP hbV
          (quotientTransvection P V hPP hsq a haP haV q)) =
        quotientTransvection P V hPP hsq a haP haV q := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    simp only [quotientTransvection_mk]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa only [commutatorIn, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev,
      inv_inv] using V.inv_mem (hαβα (x : G) x.2)

private theorem quotientTransvection_beta_alpha_beta {P V : Subgroup G}
    [(V.subgroupOf P).Normal]
    (hPP : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ V) (hsq : ∀ x ∈ P, x * x ∈ V) {a b : G}
    (haP : a ∈ Subgroup.normalizer (P : Set G))
    (haV : a ∈ Subgroup.normalizer (V : Set G))
    (hbP : b ∈ Subgroup.normalizer (P : Set G))
    (hbV : b ∈ Subgroup.normalizer (V : Set G))
    (hβαβ : ∀ x ∈ P, ⁅b, x⁆⁻¹ * ⁅b, ⁅a, ⁅b, x⁆⁆⁆ ∈ V) :
    ∀ q : ↥P ⧸ V.subgroupOf P,
      quotientTransvection P V hPP hsq b hbP hbV
        (quotientTransvection P V hPP hsq a haP haV
          (quotientTransvection P V hPP hsq b hbP hbV q)) =
        quotientTransvection P V hPP hsq b hbP hbV q := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    simp only [quotientTransvection_mk]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa only [commutatorIn, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev,
      inv_inv] using V.inv_mem (hβαβ (x : G) x.2)

private theorem normal_subgroupOf_of_commutator_le {P V : Subgroup G}
    (hPP : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ V) : (V.subgroupOf P).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn
  change (g : G) * (n : G) * (g : G)⁻¹ ∈ V
  have hconj : (g : G) * (n : G) * (g : G)⁻¹ = ⁅(g : G), (n : G)⁆ * (n : G) := by
    simp only [commutatorElement_def]
    group
  rw [hconj]
  exact V.mul_mem (hPP (g : G) g.2 (n : G) n.2) hn

private theorem quotientConjAut_braid_cube {P V : Subgroup G} [(V.subgroupOf P).Normal]
    (hPP : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ V) (hsq : ∀ x ∈ P, x * x ∈ V) {a b : G}
    (haP : a ∈ Subgroup.normalizer (P : Set G)) (hbP : b ∈ Subgroup.normalizer (P : Set G))
    (haV : a ∈ Subgroup.normalizer (V : Set G)) (hbV : b ∈ Subgroup.normalizer (V : Set G))
    (hαα : ∀ x ∈ P, ⁅a, ⁅a, x⁆⁆ ∈ V) (hββ : ∀ x ∈ P, ⁅b, ⁅b, x⁆⁆ ∈ V)
    (hαβα : ∀ x ∈ P, ⁅a, x⁆⁻¹ * ⁅a, ⁅b, ⁅a, x⁆⁆⁆ ∈ V)
    (hβαβ : ∀ x ∈ P, ⁅b, x⁆⁻¹ * ⁅b, ⁅a, ⁅b, x⁆⁆⁆ ∈ V) :
    ∀ x : ↥P,
      quotientConjAut P V a haP haV
        (quotientConjAut P V b hbP hbV
          (quotientConjAut P V a haP haV
            (quotientConjAut P V b hbP hbV
              (quotientConjAut P V a haP haV
                (quotientConjAut P V b hbP hbV (QuotientGroup.mk x)))))) =
        QuotientGroup.mk x := by
  intro x
  have hcommQ := (quotient_comm_and_mul_self hPP hsq).1
  have hsqQ := (quotient_comm_and_mul_self hPP hsq).2
  let Q := ↥P ⧸ V.subgroupOf P
  letI : Group Q := inferInstanceAs (Group (↥P ⧸ V.subgroupOf P))
  let s : Q ≃* Q := quotientConjAut P V a haP haV
  let t : Q ≃* Q := quotientConjAut P V b hbP hbV
  let α : Q →* Q := quotientTransvection P V hPP hsq a haP haV
  let β : Q →* Q := quotientTransvection P V hPP hsq b hbP hbV
  have hs : ∀ q : Q, s q = α q * q := by
    intro q
    change s q = (s q * q⁻¹) * q
    group
  have ht : ∀ q : Q, t q = β q * q := by
    intro q
    change t q = (t q * q⁻¹) * q
    group
  have hcube := braid_cube_eq hcommQ hsqQ α β
    (quotientTransvection_sq hPP hsq haP haV hαα)
    (quotientTransvection_beta_sq hPP hsq hbP hbV hββ)
    (quotientTransvection_alpha_beta_alpha hPP hsq haP haV hbP hbV hαβα)
    (quotientTransvection_beta_alpha_beta hPP hsq haP haV hbP hbV hβαβ)
    hs ht (QuotientGroup.mk x)
  change s (t (s (t (s (t (QuotientGroup.mk x)))))) = QuotientGroup.mk x
  exact hcube

theorem commutator_pow_three_mem_of_braid {P V : Subgroup G}
    (hPP : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ V) (hsq : ∀ x ∈ P, x * x ∈ V) {a b : G}
    (haP : a ∈ Subgroup.normalizer (P : Set G)) (hbP : b ∈ Subgroup.normalizer (P : Set G))
    (haV : a ∈ Subgroup.normalizer (V : Set G)) (hbV : b ∈ Subgroup.normalizer (V : Set G))
    (hαα : ∀ x ∈ P, ⁅a, ⁅a, x⁆⁆ ∈ V) (hββ : ∀ x ∈ P, ⁅b, ⁅b, x⁆⁆ ∈ V)
    (hαβα : ∀ x ∈ P, ⁅a, x⁆⁻¹ * ⁅a, ⁅b, ⁅a, x⁆⁆⁆ ∈ V)
    (hβαβ : ∀ x ∈ P, ⁅b, x⁆⁻¹ * ⁅b, ⁅a, ⁅b, x⁆⁆⁆ ∈ V) :
    ∀ x ∈ P, ⁅(a * b) ^ 3, x⁆ ∈ V := by
  haveI hNV : (V.subgroupOf P).Normal := normal_subgroupOf_of_commutator_le hPP
  intro x hx
  have hcube := quotientConjAut_braid_cube hPP hsq haP hbP haV hbV hαα hββ hαβα hβαβ
    ⟨x, hx⟩
  have hmem : (a * b) ^ 3 * x * ((a * b) ^ 3)⁻¹ ∈ P := by
    have habP : a * b ∈ Subgroup.normalizer (P : Set G) := Subgroup.mul_mem _ haP hbP
    have h3 : (a * b) ^ 3 = (a * b) * (a * b) * (a * b) := by
      rw [pow_succ, pow_succ]
      group
    have hab3P : (a * b) ^ 3 ∈ Subgroup.normalizer (P : Set G) := by
      rw [h3]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ habP habP) habP
    exact (Subgroup.mem_normalizer_iff.mp hab3P x).mp hx
  let u : ↥P := ⟨(a * b) ^ 3 * x * ((a * b) ^ 3)⁻¹, hmem⟩
  have hleft : quotientConjAut P V a haP haV
      (quotientConjAut P V b hbP hbV
        (quotientConjAut P V a haP haV
          (quotientConjAut P V b hbP hbV
            (quotientConjAut P V a haP haV
              (quotientConjAut P V b hbP hbV (QuotientGroup.mk ⟨x, hx⟩)))))) =
      QuotientGroup.mk u := by
    rw [quotientConjAut_mk, quotientConjAut_mk, quotientConjAut_mk,
      quotientConjAut_mk, quotientConjAut_mk, quotientConjAut_mk]
    congr 1
    apply Subtype.ext
    dsimp only [u]
    rw [pow_succ, pow_succ]
    group
  have hq : (QuotientGroup.mk u : ↥P ⧸ V.subgroupOf P) = QuotientGroup.mk ⟨x, hx⟩ := by
    rw [← hleft]
    exact hcube
  have hdiv := (QuotientGroup.eq_iff_div_mem).mp hq
  rw [Subgroup.mem_subgroupOf] at hdiv
  have hdiv' : (u : G) * (x : G)⁻¹ ∈ V := by
    simpa only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv]
      using hdiv
  rw [show ⁅(a * b) ^ 3, x⁆ = (u : G) * (x : G)⁻¹ by
    dsimp only [u]
    simp only [commutatorElement_def]]
  exact hdiv'

end CFSG

end
