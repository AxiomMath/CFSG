module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2412d
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2412b
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InTorus

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups

section Coordinates

variable {G : Type} [Group G] {L R : Subgroup G} {n : ℕ} {K : Type} [Field K]

theorem entry01_mul {A B : SL(2, K)} (hA : A ∈ slUni K) (hB : B ∈ slUni K) :
    ((A * B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 1 =
      (A : Matrix (Fin 2) (Fin 2) K) 0 1 + (B : Matrix (Fin 2) (Fin 2) K) 0 1 := by
  obtain ⟨x, rfl⟩ := mem_slUni.1 hA
  obtain ⟨y, rfl⟩ := mem_slUni.1 hB
  rw [← slUpper_add]
  simp [slUpper_val]

theorem exists_gamma_top [Fintype K] {U : Subgroup G} (A : Adapted L R n K)
    (hU : ∀ ℓ : L, (ℓ : G) ∈ U ↔ A.α ℓ = 1) :
    ∃ γ : R →* Multiplicative K, Function.Surjective γ ∧ (∀ r : R, γ r = 1 ↔ (r : G) ∈ U) ∧
      ∀ r : R, Multiplicative.toAdd (γ r) =
        (A.α ⟨r, A.P_le r.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 1 := by
  let γ : R →* Multiplicative K :=
    { toFun := fun r => Multiplicative.ofAdd
        ((A.α ⟨r, A.P_le r.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 1)
      map_one' := by
        show Multiplicative.ofAdd
          ((A.α ⟨(1 : R), A.P_le (1 : R).2⟩ : Matrix (Fin 2) (Fin 2) K) 0 1) = 1
        have : A.α ⟨(1 : R), A.P_le (1 : R).2⟩ = 1 := by
          rw [show (⟨(1 : R), A.P_le (1 : R).2⟩ : L) = 1 from rfl, map_one]
        rw [this]
        simp
      map_mul' := by
        intro r r'
        have h1 := (A.mem_P ⟨r, A.P_le r.2⟩).1 r.2
        have h2 := (A.mem_P ⟨r', A.P_le r'.2⟩).1 r'.2
        have h3 := entry01_mul h1 h2
        have e : A.α ⟨((r * r' : R) : G), A.P_le (r * r').2⟩ =
            A.α ⟨r, A.P_le r.2⟩ * A.α ⟨r', A.P_le r'.2⟩ := by
          rw [← map_mul]; rfl
        show Multiplicative.ofAdd ((A.α ⟨((r * r' : R) : G), A.P_le (r * r').2⟩ :
          Matrix (Fin 2) (Fin 2) K) 0 1) = _
        rw [e, h3, ofAdd_add] }
  refine ⟨γ, ?_, ?_, fun r => rfl⟩
  · intro v
    obtain ⟨ℓ, hℓ⟩ := A.α_surj (slUpper (Multiplicative.toAdd v))
    have hℓR : (ℓ : G) ∈ R := (A.mem_P ℓ).2 (hℓ ▸ slUpper_mem_slUni _)
    refine ⟨⟨ℓ, hℓR⟩, ?_⟩
    show Multiplicative.ofAdd ((A.α ⟨ℓ, A.P_le hℓR⟩ : Matrix (Fin 2) (Fin 2) K) 0 1) = _
    rw [show (⟨(ℓ : G), A.P_le hℓR⟩ : L) = ℓ from rfl, hℓ]
    simp [slUpper_val]
  · intro r
    show Multiplicative.ofAdd ((A.α ⟨r, A.P_le r.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 1) = 1 ↔ _
    have hU' := hU ⟨r, A.P_le r.2⟩
    obtain ⟨x, hx⟩ := mem_slUni.1 ((A.mem_P ⟨r, A.P_le r.2⟩).1 r.2)
    rw [show ((r : G) ∈ U) ↔ A.α ⟨r, A.P_le r.2⟩ = 1 from hU', hx]
    constructor
    · intro h
      have : x = 0 := by simpa [slUpper_val] using h
      rw [this, slUpper_zero]
    · intro h
      have := congrArg (fun M : SL(2, K) => (M : Matrix (Fin 2) (Fin 2) K) 0 1) h
      simpa [slUpper_val] using this

variable {U Z : Subgroup G}

theorem exists_gamma_mid (β : U →* Multiplicative (Fin 2 → K)) (hβ : Function.Surjective β)
    (hker : ∀ u : U, β u = 1 ↔ (u : G) ∈ Z) :
    ∃ (N' : Subgroup G) (hN'U : N' ≤ U) (γ₂ : U →* Multiplicative K)
      (γ₁ : N' →* Multiplicative K),
      Function.Surjective γ₂ ∧ (∀ u : U, γ₂ u = 1 ↔ (u : G) ∈ N') ∧
      (∀ u : U, Multiplicative.toAdd (γ₂ u) = Multiplicative.toAdd (β u) 1) ∧
      Function.Surjective γ₁ ∧ (∀ n : N', γ₁ n = 1 ↔ (n : G) ∈ Z) ∧
      (∀ n : N', Multiplicative.toAdd (γ₁ n) = Multiplicative.toAdd (β ⟨n, hN'U n.2⟩) 0) ∧
      (∀ x : G, x ∈ N' ↔ ∃ h : x ∈ U, Multiplicative.toAdd (β ⟨x, h⟩) 1 = 0) := by
  let γ₂ : U →* Multiplicative K :=
    (AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : Fin 2 => K) 1)).comp β
  have hγ₂ : ∀ u : U, Multiplicative.toAdd (γ₂ u) = Multiplicative.toAdd (β u) 1 := fun _ => rfl
  let N' : Subgroup G := γ₂.ker.map U.subtype
  have hN'U : N' ≤ U := Subgroup.map_subtype_le _
  have hmem : ∀ x : G, x ∈ N' ↔ ∃ h : x ∈ U, Multiplicative.toAdd (β ⟨x, h⟩) 1 = 0 := by
    intro x
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.2, ?_⟩
      have : γ₂ u = 1 := hu
      have h2 := congrArg Multiplicative.toAdd this
      rw [hγ₂] at h2
      simpa using h2
    · rintro ⟨h, h2⟩
      refine ⟨⟨x, h⟩, MonoidHom.mem_ker.2 (Multiplicative.toAdd.injective ?_), rfl⟩
      rw [hγ₂, toAdd_one]
      exact h2
  let γ₁ : N' →* Multiplicative K :=
    (AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : Fin 2 => K) 0)).comp
      (β.comp (Subgroup.inclusion hN'U))
  have hγ₁ : ∀ n : N', Multiplicative.toAdd (γ₁ n) = Multiplicative.toAdd (β ⟨n, hN'U n.2⟩) 0 :=
    fun _ => rfl
  refine ⟨N', hN'U, γ₂, γ₁, ?_, ?_, hγ₂, ?_, ?_, hγ₁, hmem⟩
  · intro y
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd ![0, Multiplicative.toAdd y])
    refine ⟨u, Multiplicative.toAdd.injective ?_⟩
    rw [hγ₂, hu]
    simp
  · intro u
    constructor
    · intro h
      exact ⟨u, MonoidHom.mem_ker.2 h, rfl⟩
    · rintro ⟨u', hu', hu'u⟩
      have : u' = u := Subtype.ext hu'u
      subst this
      exact hu'
  · intro x
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd ![Multiplicative.toAdd x, 0])
    have hu1 : Multiplicative.toAdd (β u) 1 = 0 := by rw [hu]; simp
    have hN : (u : G) ∈ N' := (hmem u).2 ⟨u.2, hu1⟩
    refine ⟨⟨u, hN⟩, Multiplicative.toAdd.injective ?_⟩
    rw [hγ₁]
    show Multiplicative.toAdd (β u) 0 = _
    rw [hu]
    simp
  · intro n
    have hn1 := ((hmem n).1 n.2)
    obtain ⟨h, h1⟩ := hn1
    rw [← hker ⟨n, hN'U n.2⟩]
    constructor
    · intro h0
      have h0' : Multiplicative.toAdd (γ₁ n) = 0 := by rw [h0]; rfl
      rw [hγ₁] at h0'
      apply Multiplicative.toAdd.injective
      ext i
      fin_cases i
      · simpa using h0'
      · simpa using h1
    · intro h0
      apply Multiplicative.toAdd.injective
      have : β ⟨n, hN'U n.2⟩ = 1 := h0
      rw [hγ₁, this]
      simp

end Coordinates

section Link

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem Lin2Cfg.link (h : Lin2Cfg G T M H S L n D) {K : Type} [Field K] [Fintype K]
    {R : Subgroup G} (A : Adapted L R n K) (hOL : pCoreOf 2 L = blockU L)
    {f : G} (hff : f * f = 1) (hfL : ∀ x ∈ L, f * x * f⁻¹ ∈ L)
    (hfU : ∀ x ∈ blockU L, f * x * f⁻¹ ∈ blockU L) (hfR : ∀ x ∈ R, f * x * f⁻¹ ∈ R) :
    ∃ (σ : K ≃+* K) (a c' : K), a ≠ 0 ∧ (∀ v, σ (σ v) = v) ∧ a * a * σ (a * a) = 1 ∧
      c' * a⁻¹ * σ (c' * a⁻¹) = 1 ∧ c' * a * σ (c' * a) = 1 ∧
      (∀ r : L, (r : G) ∈ R →
        (A.α ⟨f * r * f⁻¹, hfL r r.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 1 =
          a * a * σ ((A.α r : Matrix (Fin 2) (Fin 2) K) 0 1)) ∧
      (∀ u : blockU L, (Multiplicative.toAdd (A.β ⟨f * u * f⁻¹, hfU u u.2⟩)) 1 =
        c' * a⁻¹ * σ (Multiplicative.toAdd (A.β u) 1)) ∧
      (∀ u : blockU L, Multiplicative.toAdd (A.β u) 1 = 0 →
        (Multiplicative.toAdd (A.β ⟨f * u * f⁻¹, hfU u u.2⟩)) 0 =
          c' * a * σ (Multiplicative.toAdd (A.β u) 0)) ∧
      (∀ ℓ : L, (A.α ℓ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 →
        (A.α ⟨f * ℓ * f⁻¹, hfL ℓ ℓ.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 0 =
          σ ((A.α ℓ : Matrix (Fin 2) (Fin 2) K) 0 0)) ∧
      (∃ Gm : SL(2, K), (Gm : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
        (Gm : Matrix (Fin 2) (Fin 2) K) 0 0 = a ∧
        σ ((Gm : Matrix (Fin 2) (Fin 2) K) 0 1) = (Gm : Matrix (Fin 2) (Fin 2) K) 0 1 ∧
        (∀ ℓ : L, A.α ⟨f * ℓ * f⁻¹, hfL ℓ ℓ.2⟩ * Gm =
          Gm * Matrix.SpecialLinearGroup.map σ.toRingHom (A.α ℓ)) ∧
        (∀ u : blockU L, Multiplicative.toAdd (A.β ⟨f * u * f⁻¹, hfU u u.2⟩) =
          (Gm : Matrix (Fin 2) (Fin 2) K).mulVec
            (fun i => c' * σ (Multiplicative.toAdd (A.β u) i)))) ∧
      (σ = 1 → ∃ k : SL(2, K), ∀ ℓ : L, A.α ⟨f * ℓ * f⁻¹, hfL ℓ ℓ.2⟩ = k * A.α ℓ * k⁻¹) := by
  have hff2 : ∀ x : G, f * (f * x * f⁻¹) * f⁻¹ = x := by
    intro x
    calc f * (f * x * f⁻¹) * f⁻¹ = (f * f) * x * (f * f)⁻¹ := by group
      _ = x := by rw [hff]; group
  have hnorm : ∀ {X : Subgroup G}, (∀ x ∈ X, f * x * f⁻¹ ∈ X) →
      f ∈ Subgroup.normalizer (X : Set G) := by
    intro X hX
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨hX x, fun hx => by have := hX _ hx; rwa [hff2] at this⟩
  have hfHn : f ∈ Subgroup.normalizer (L : Set G) ⊓
      Subgroup.normalizer ((blockU L : Subgroup G) : Set G) := ⟨hnorm hfL, hnorm hfU⟩
  have hLU : ∀ ℓ ∈ L, ∀ u ∈ blockU L, ℓ * u * ℓ⁻¹ ∈ blockU L := by
    intro ℓ hℓ u hu
    have hn : L ≤ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) := by
      rw [← hOL]
      exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L
    exact (Subgroup.mem_normalizer_iff.1 (hn hℓ) u).1 hu
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card h.one_pos A.card_eq
  have : Finite K := Finite.of_fintype K
  let Hn : Subgroup G := Subgroup.normalizer (L : Set G) ⊓
    Subgroup.normalizer ((blockU L : Subgroup G) : Set G)
  let act : Hn →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_left)
  have hact : ∀ (g : Hn) (ℓ : L), ((act g ℓ : L) : G) = (g : G) * (ℓ : G) * (g : G)⁻¹ :=
    fun _ _ => rfl
  have hker : ∀ g : Hn, ∀ ℓ : L, A.α (act g ℓ) = 1 ↔ A.α ℓ = 1 := by
    intro g ℓ
    rw [← A.mem_pCoreOf_iff, ← A.mem_pCoreOf_iff, hact, hOL]
    exact (Subgroup.mem_normalizer_iff.1 g.2.2 (ℓ : G)).symm
  obtain ⟨Ψ', hΨ'⟩ := exists_act_quot A.α A.α_surj act hker
  let Ψ : MulAut SL(2, K) := Ψ' ⟨f, hfHn⟩
  have hΨ : ∀ ℓ : L, Ψ (A.α ℓ) = A.α ⟨f * ℓ * f⁻¹, hfL ℓ ℓ.2⟩ := fun ℓ => hΨ' ⟨f, hfHn⟩ ℓ
  let actU : Hn →* MulAut (blockU L) :=
    (blockU L).normalizerMonoidHom.comp (Subgroup.inclusion inf_le_right)
  have hactU : ∀ (g : Hn) (u : blockU L),
      ((actU g u : blockU L) : G) = (g : G) * (u : G) * (g : G)⁻¹ := fun _ _ => rfl
  have hβk : ∀ u : blockU L, A.β u = 1 ↔ (u : G) ∈ blockZ L := fun u => by
    rw [← MonoidHom.mem_ker, A.β_ker, Subgroup.mem_subgroupOf]
  have hcent : ∀ g : G, g ∈ Subgroup.normalizer (L : Set G) → ∀ u : G,
      (g * u * g⁻¹ ∈ Subgroup.centralizer (L : Set G) ↔ u ∈ Subgroup.centralizer (L : Set G)) := by
    intro g hg u
    have hg' : ∀ x ∈ L, g * x * g⁻¹ ∈ L := fun x hx => (Subgroup.mem_normalizer_iff.1 hg x).1 hx
    have hg'' : ∀ x ∈ L, g⁻¹ * x * g ∈ L := by
      intro x hx
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) x).1 hx
      simpa using this
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hc ℓ hℓ
      have h1 := hc (g * ℓ * g⁻¹) (hg' ℓ hℓ)
      have e1 : g * ℓ * g⁻¹ * (g * u * g⁻¹) = g * (ℓ * u) * g⁻¹ := by group
      have e2 : g * u * g⁻¹ * (g * ℓ * g⁻¹) = g * (u * ℓ) * g⁻¹ := by group
      rw [e1, e2] at h1
      have := mul_left_cancel (mul_right_cancel h1)
      exact this
    · intro hc ℓ hℓ
      have h1 := hc (g⁻¹ * ℓ * g) (hg'' ℓ hℓ)
      have e1 : ℓ * (g * u * g⁻¹) = g * ((g⁻¹ * ℓ * g) * u) * g⁻¹ := by group
      have e2 : g * u * g⁻¹ * ℓ = g * (u * (g⁻¹ * ℓ * g)) * g⁻¹ := by group
      rw [e1, e2, h1]
  have hkerU : ∀ g : Hn, ∀ u : blockU L, A.β (actU g u) = 1 ↔ A.β u = 1 := by
    intro g u
    rw [hβk, hβk, hactU]
    unfold blockZ
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hcent g g.2.1 u]
    constructor
    · rintro ⟨-, hc⟩
      exact ⟨u.2, hc⟩
    · rintro ⟨-, hc⟩
      exact ⟨(actU g u).2, hc⟩
  obtain ⟨Φ', hΦ'⟩ := exists_act_quot A.β A.β_surj actU hkerU
  let Φ : MulAut (Multiplicative (Fin 2 → K)) := Φ' ⟨f, hfHn⟩
  have hΦ : ∀ u : blockU L, Φ (A.β u) = A.β ⟨f * u * f⁻¹, hfU u u.2⟩ :=
    fun u => hΦ' ⟨f, hfHn⟩ u
  exact link_core hK2 A.α A.α_surj A.β A.β_surj A.β_equiv hLU A.mem_P hff hfL hfU hfR Ψ hΨ Φ hΦ
    (exists_semilinear_of_aut hK2 Ψ)

end Link

end CFSG.QuasithinUnique.Lin2
