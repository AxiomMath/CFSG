module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open
open scoped Pointwise

@[expose] def NormProps {Y : Type*} [Group Y] (E : Subgroup Y) : Prop :=
  (∀ R W : Subgroup Y, E < R → R ≤ Subgroup.normalizer (E : Set Y) → R ≤ W →
      (∀ g ∈ Subgroup.normalizer (E : Set Y), ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
        Subgroup.normalizer (E : Set Y) ≤ W) ∧
    ∀ y ∈ E, (∀ g ∈ Subgroup.normalizer (E : Set Y), g * y * g⁻¹ = y) → y = 1

section Generic

variable {Y Y' : Type*} [Group Y] [Group Y']

theorem mem_normalizer_map_iff (φ : Y ≃* Y') (E : Subgroup Y) (g : Y) :
    φ g ∈ Subgroup.normalizer ((E.map φ.toMonoidHom : Subgroup Y') : Set Y') ↔
      g ∈ Subgroup.normalizer (E : Set Y) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have := h (φ y)
    constructor
    · intro hy
      have h1 := this.1 ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzz⟩ := h1
      have : z = g * y * g⁻¹ := φ.injective (by simpa using hzz)
      rwa [← this]
    · intro hy
      have h2 : φ y ∈ E.map φ.toMonoidHom := by
        apply this.2
        refine ⟨g * y * g⁻¹, hy, ?_⟩
        simp
      obtain ⟨z, hz, hzz⟩ := h2
      have : z = y := φ.injective hzz
      rwa [← this]
  · intro h y'
    obtain ⟨y, rfl⟩ := φ.surjective y'
    constructor
    · rintro ⟨z, hz, hzz⟩
      have : z = y := φ.injective hzz
      subst this
      exact ⟨g * z * g⁻¹, (h z).1 hz, by simp⟩
    · rintro ⟨z, hz, hzz⟩
      have : z = g * y * g⁻¹ := φ.injective (by simpa using hzz)
      subst this
      exact ⟨y, (h y).2 hz, rfl⟩

theorem NormProps.of_map (φ : Y ≃* Y') {E : Subgroup Y}
    (h : NormProps (E.map φ.toMonoidHom)) : NormProps E := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun R W hER hRN hRW hW g hg => ?_, fun y hy hfix => ?_⟩
  · have hlt : E.map φ.toMonoidHom < R.map φ.toMonoidHom := by
      refine lt_of_le_of_ne (Subgroup.map_mono hER.le) fun heq => ?_
      have := Subgroup.map_injective φ.injective heq
      exact hER.ne this
    have hRN' : R.map φ.toMonoidHom ≤ Subgroup.normalizer ((E.map φ.toMonoidHom : Subgroup Y') : Set Y') := by
      rintro _ ⟨r, hr, rfl⟩
      exact (mem_normalizer_map_iff φ E r).2 (hRN hr)
    have hW' : ∀ g' ∈ Subgroup.normalizer ((E.map φ.toMonoidHom : Subgroup Y') : Set Y'),
        ∀ w' ∈ W.map φ.toMonoidHom, g' * w' * g'⁻¹ ∈ W.map φ.toMonoidHom := by
      intro g' hg' w' hw'
      obtain ⟨g'', rfl⟩ := φ.surjective g'
      obtain ⟨w, hw, rfl⟩ := hw'
      exact ⟨g'' * w * g''⁻¹, hW g'' ((mem_normalizer_map_iff φ E g'').1 hg') w hw, by simp⟩
    have h3 := h1 _ _ hlt hRN' (Subgroup.map_mono hRW) hW' ((mem_normalizer_map_iff φ E g).2 hg)
    obtain ⟨z, hz, hzz⟩ := h3
    have : z = g := φ.injective hzz
    rwa [← this]
  · have := h2 (φ y) ⟨y, hy, rfl⟩ (fun g' hg' => by
      obtain ⟨g, rfl⟩ := φ.surjective g'
      have hgN := (mem_normalizer_map_iff φ E g).1 hg'
      calc φ g * φ y * (φ g)⁻¹ = φ (g * y * g⁻¹) := by simp
        _ = φ y := by rw [hfix g hgN])
    exact φ.injective (by simpa using this)

end Generic

section Sylow

variable {Y : Type*} [Group Y] [Finite Y]

theorem normProps_of_sylow (U : Sylow 2 Y)
    (h : ∀ E : Subgroup Y, E ≤ (U : Subgroup Y) → IsElemAbelian 2 E → Nat.card E = 16 →
      NormProps E) :
    ∀ E : Subgroup Y, IsElemAbelian 2 E → Nat.card E = 16 → NormProps E := by
  intro E hE hcard
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨P, hEP⟩ := hE2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P U
  have hEU : E.map (MulAut.conj g).toMonoidHom ≤ (U : Subgroup Y) := by
    rintro _ ⟨x, hx, rfl⟩
    have h : ((g • P : Sylow 2 Y) : Subgroup Y) = MulAut.conj g • (P : Subgroup Y) := by
      rw [Sylow.smul_def, Sylow.pointwise_smul_def]
    have h2 : (MulAut.conj g) x ∈ ((g • P : Sylow 2 Y) : Subgroup Y) := by
      rw [h]
      have h1 := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (P : Subgroup Y) (hEP hx)
      simpa [MulAut.smul_def] using h1
    rw [hg] at h2
    exact h2
  have hcard' : Nat.card (E.map (MulAut.conj g).toMonoidHom) = 16 := by
    rw [← hcard]
    exact card_map_equiv (MulAut.conj g) E
  exact NormProps.of_map (MulAut.conj g)
    (h _ hEU ((isElemAbelian_map_equiv_iff (MulAut.conj g) E).2 hE) hcard')

end Sylow

section Quotient

variable {S : Type*} [Group S]

theorem normProps_quotient {Z : Subgroup S} [hZ : Z.Normal] {X P : Subgroup S} {T : Type*} [Group T]
    [IsSimpleGroup T]
    (hPN : ∀ g : S, g ∈ P ↔ g ∈ Subgroup.normalizer ((X ⊔ Z : Subgroup S) : Set S))
    (ψ : ↥P →* T) (hψ : Function.Surjective ψ)
    (hker : ∀ g : ↥P, ψ g = 1 ↔ (g : S) ∈ X ⊔ Z)
    (hfix : ∀ x ∈ X, (∀ g ∈ P, g * x * g⁻¹ * x⁻¹ ∈ Z) → x = 1) :
    NormProps (X.map (QuotientGroup.mk' Z)) := by
  classical
  set π : S →* S ⧸ Z := QuotientGroup.mk' Z with hπ
  set E : Subgroup (S ⧸ Z) := X.map π with hE
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hF0 : ∀ s : S, π s ∈ E ↔ s ∈ X ⊔ Z := by
    intro s
    have h1 : s ∈ Subgroup.comap π E ↔ π s ∈ E := Iff.rfl
    rw [hE, Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk'] at h1
    exact h1.symm
  have hF1 : ∀ s : S, π s ∈ Subgroup.normalizer (E : Set (S ⧸ Z)) ↔ s ∈ P := by
    intro s
    rw [hPN, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro h t
      have := h (π t)
      rw [hF0, ← map_inv, ← map_mul, ← map_mul, hF0] at this
      exact this
    · intro h y
      obtain ⟨t, rfl⟩ := hπs y
      rw [hF0, ← map_inv, ← map_mul, ← map_mul, hF0]
      exact h t
  refine ⟨fun R W hER hRN hRW hW => ?_, fun y hy hfix' => ?_⟩
  · set R' : Subgroup S := R.comap π with hR'
    set W' : Subgroup S := W.comap π with hW'
    have hRP : ∀ s ∈ R', s ∈ P := fun s hs => (hF1 s).1 (hRN hs)
    have hXZR : X ⊔ Z ≤ R' := fun s hs => hER.le ((hF0 s).2 hs)
    obtain ⟨r, hr, hrE⟩ := IsConcreteLE.exists_of_lt hER
    obtain ⟨s₀, rfl⟩ := hπs r
    have hs₀R : s₀ ∈ R' := hr
    have hs₀ : s₀ ∉ X ⊔ Z := fun h => hrE ((hF0 s₀).2 h)
    set A : Subgroup ↥P := W'.subgroupOf P with hA
    have hAinv : ∀ (p : ↥P) (a : ↥P), a ∈ A → p * a * p⁻¹ ∈ A := by
      intro p a ha
      have hpN : π p ∈ Subgroup.normalizer (E : Set (S ⧸ Z)) := (hF1 _).2 p.2
      have haW : π a ∈ W := ha
      have := hW (π p) hpN (π a) haW
      show π (((p * a * p⁻¹ : ↥P)) : S) ∈ W
      simpa using this
    have hB : (A.map ψ).Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨a, ha, rfl⟩ := hn
      obtain ⟨p, rfl⟩ := hψ g
      exact ⟨p * a * p⁻¹, hAinv p a ha, by simp⟩
    have hRA : (R'.subgroupOf P) ≤ A := Subgroup.subgroupOf_mono P (fun s hs => hRW hs)
    have hBtop : A.map ψ = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.map ψ) with hb | hb
      · exfalso
        have hs₀P : s₀ ∈ P := hRP s₀ hs₀R
        have h1 : ψ ⟨s₀, hs₀P⟩ ∈ A.map ψ := ⟨⟨s₀, hs₀P⟩, hRA hs₀R, rfl⟩
        rw [hb, Subgroup.mem_bot, hker] at h1
        exact hs₀ h1
      · exact hb
    have hPW : ∀ p : ↥P, (p : S) ∈ W' := by
      intro p
      have : ψ p ∈ A.map ψ := by rw [hBtop]; trivial
      obtain ⟨a, ha, hap⟩ := this
      have h1 : ψ (p * a⁻¹) = 1 := by rw [map_mul, map_inv, ← hap, mul_inv_cancel]
      have h2 : ((p * a⁻¹ : ↥P) : S) ∈ X ⊔ Z := (hker _).1 h1
      have h3 : ((p * a⁻¹ : ↥P) : S) ∈ W' := hRW (hXZR h2)
      have h4 : (a : S) ∈ W' := ha
      have : (p : S) = ((p * a⁻¹ : ↥P) : S) * (a : S) := by simp
      rw [this]
      exact W'.mul_mem h3 h4
    intro g1 hg1
    obtain ⟨g, rfl⟩ := hπs g1
    exact hPW ⟨g, (hF1 g).1 hg1⟩
  · obtain ⟨x, hx, rfl⟩ := hy
    have : x = 1 := hfix x hx (fun g hg => by
      have hgN := (hF1 g).2 hg
      have e : π g * π x * (π g)⁻¹ = π x := hfix' (π g) hgN
      have h1 : π (g * x * g⁻¹ * x⁻¹) = 1 := by
        calc π (g * x * g⁻¹ * x⁻¹) = (π g * π x * (π g)⁻¹) * (π x)⁻¹ := by
              simp only [map_mul, map_inv]
          _ = π x * (π x)⁻¹ := by rw [e]
          _ = 1 := mul_inv_cancel _
      exact (QuotientGroup.eq_one_iff (N := Z) _).1 h1)
    rw [this, map_one]

end Quotient

end CFSG.QuasithinUnique.Lin2
