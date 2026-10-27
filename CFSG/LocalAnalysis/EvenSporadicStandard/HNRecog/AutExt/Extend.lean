module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.IsoOn

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G']

theorem IsIsoOn.agree_on_closure {K : Subgroup G} {K₁ K₂ : Subgroup G'} {f g : G → G'}
    (hf : IsIsoOn K K₁ f) (hg : IsIsoOn K K₂ g) {S : Set G} (hS : S ⊆ K)
    (hfg : ∀ x ∈ S, f x = g x) : ∀ x ∈ Subgroup.closure S, f x = g x := by
  let H : Subgroup G :=
    { carrier := {x | x ∈ K ∧ f x = g x}
      mul_mem' := by
        rintro x y ⟨hxK, hx⟩ ⟨hyK, hy⟩
        exact ⟨K.mul_mem hxK hyK, by
          rw [hf.map_mul x hxK y hyK, hx, hy, hg.map_mul x hxK y hyK]⟩
      one_mem' := ⟨K.one_mem, by rw [hf.map_one, hg.map_one]⟩
      inv_mem' := by
        rintro x ⟨hxK, hx⟩
        exact ⟨K.inv_mem hxK, by rw [hf.map_inv hxK, hg.map_inv hxK, hx]⟩ }
  have hcl : Subgroup.closure S ≤ H :=
    (Subgroup.closure_le H).mpr fun x hx => ⟨hS hx, hfg x hx⟩
  exact fun x hx => (hcl hx).2

theorem exists_isIsoOn_fix {M : Subgroup G} {M' : Subgroup G'} {β₀ : G → G'}
    (hβ₀ : IsIsoOn M M' β₀) {x : G} {x' : G'} (h : ConjIn M' (β₀ x) x') :
    ∃ β : G → G', IsIsoOn M M' β ∧ β x = x' := by
  obtain ⟨k, hk, hkx⟩ := h
  refine ⟨fun y => k * β₀ y * k⁻¹, hβ₀.comp (isIsoOn_conj hk), hkx⟩

theorem extend_iso_of_inner {M Y N Z : Subgroup G} {M' Y' : Subgroup G'} {α β : G → G'}
    (hYM : Y ≤ M) (hZY : Z ≤ Y) (hNY : N ≤ Y)
    (hdec : ∀ y ∈ Y, ∃ u ∈ Z, ∃ n ∈ N, y = u * n)
    (hZc : ∀ u ∈ Z, ∀ y ∈ Y, u * y = y * u)
    (hα : IsIsoOn Y Y' α) (hβ : IsIsoOn M M' β) (hZ : ∀ u ∈ Z, β u = α u)
    (hinn : ∃ g ∈ N, ∀ x ∈ N, α x = β (g * x * g⁻¹)) :
    ∃ β₁ : G → G', IsIsoOn M M' β₁ ∧ ∀ y ∈ Y, β₁ y = α y := by
  obtain ⟨g, hgN, hginn⟩ := hinn
  have hgM : g ∈ M := hYM (hNY hgN)
  refine ⟨fun x => β (g * x * g⁻¹), (isIsoOn_conj hgM).comp hβ, ?_⟩
  intro y hy
  obtain ⟨u, hu, n, hn, rfl⟩ := hdec y hy
  have hgY : g ∈ Y := hNY hgN
  have hgu : g * u = u * g := (hZc u hu g hgY).symm
  have huM : u ∈ M := hYM (hZY hu)
  have huY : u ∈ Y := hZY hu
  have hnY : n ∈ Y := hNY hn
  have hgnM : g * n * g⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem (hYM hgY) (hYM hnY)) (M.inv_mem (hYM hgY))
  have hconj : g * (u * n) * g⁻¹ = u * (g * n * g⁻¹) := by
    rw [← mul_assoc g u n, hgu, mul_assoc u g n, mul_assoc u (g * n) g⁻¹]
  calc β (g * (u * n) * g⁻¹)
      = β (u * (g * n * g⁻¹)) := by rw [hconj]
    _ = β u * β (g * n * g⁻¹) := hβ.map_mul u huM _ hgnM
    _ = α u * α n := by rw [hZ u hu, hginn n hn]
    _ = α (u * n) := (hα.map_mul u huY n hnY).symm

theorem extend_iso {M Y N Z : Subgroup G} {M' Y' : Subgroup G'} {α β : G → G'}
    (hYM : Y ≤ M) (hZY : Z ≤ Y) (hNY : N ≤ Y)
    (hdec : ∀ y ∈ Y, ∃ u ∈ Z, ∃ n ∈ N, y = u * n)
    (hZc : ∀ u ∈ Z, ∀ y ∈ Y, u * y = y * u)
    (hα : IsIsoOn Y Y' α) (hβ : IsIsoOn M M' β) (hβY : ∀ y ∈ Y, β y ∈ Y')
    (hβY' : ∀ y' ∈ Y', ∃ y ∈ Y, β y = y') (hZ : ∀ u ∈ Z, β u = α u)
    (hNN : ∀ y' ∈ Y', (∃ n ∈ N, α n = y') ↔ (∃ n ∈ N, β n = y'))
    {η : G → G} (hη : IsIsoOn M M η) (hηZ : ∀ u ∈ Z, η u = u) (hηN : IsIsoOn N N η)
    (hηout : ¬ ∃ g ∈ N, ∀ x ∈ N, η x = g * x * g⁻¹)
    (hout : ∀ ψ₁ ψ₂ : G → G, IsIsoOn N N ψ₁ → IsIsoOn N N ψ₂ →
      (¬ ∃ g ∈ N, ∀ x ∈ N, ψ₁ x = g * x * g⁻¹) → (¬ ∃ g ∈ N, ∀ x ∈ N, ψ₂ x = g * x * g⁻¹) →
      ∃ g ∈ N, ∀ x ∈ N, ψ₁ (ψ₂ x) = g * x * g⁻¹) :
    ∃ β₁ : G → G', IsIsoOn M M' β₁ ∧ ∀ y ∈ Y, β₁ y = α y := by
  have himg : ∀ y', y' ∈ Y' ↔ ∃ x ∈ Y, β x = y' := fun y' =>
    ⟨fun hy' => hβY' y' hy', fun ⟨x, hx, hxy⟩ => hxy ▸ hβY x hx⟩
  have hβYiso : IsIsoOn Y Y' β := hβ.restrict hYM himg
  obtain ⟨γ, hγ, hγβ, hβγ⟩ := hβYiso.exists_inv
  let ψ : G → G := fun x => γ (α x)
  have hψY : IsIsoOn Y Y ψ := hα.comp hγ
  have hψN : ∀ x ∈ N, ψ x ∈ N := by
    intro x hx
    obtain ⟨n₀, hn₀N, hn₀⟩ := (hNN (α x) (hα.mem x (hNY hx))).mp ⟨x, hx, rfl⟩
    have hx' : ψ x = n₀ := by
      change γ (α x) = n₀
      rw [← hn₀, hγβ n₀ (hNY hn₀N)]
    rw [hx']; exact hn₀N
  have hβψ : ∀ x ∈ N, β (ψ x) = α x := by
    intro x hx
    obtain ⟨n₀, hn₀N, hn₀⟩ := (hNN (α x) (hα.mem x (hNY hx))).mp ⟨x, hx, rfl⟩
    have hx' : ψ x = n₀ := by
      change γ (α x) = n₀
      rw [← hn₀, hγβ n₀ (hNY hn₀N)]
    rw [hx', hn₀]
  have himgN : ∀ y, y ∈ N ↔ ∃ x ∈ N, ψ x = y := by
    intro y
    constructor
    · intro hy
      obtain ⟨n, hnN, hn⟩ := (hNN (β y) (hβY y (hNY hy))).mpr ⟨y, hy, rfl⟩
      refine ⟨n, hnN, ?_⟩
      change γ (α n) = y
      rw [hn, hγβ y (hNY hy)]
    · rintro ⟨x, hx, rfl⟩
      exact hψN x hx
  have hψNiso : IsIsoOn N N ψ := hψY.restrict hNY himgN
  by_cases hin : ∃ g ∈ N, ∀ x ∈ N, ψ x = g * x * g⁻¹
  · obtain ⟨g, hgN, hginner⟩ := hin
    exact extend_iso_of_inner hYM hZY hNY hdec hZc hα hβ hZ
      ⟨g, hgN, fun x hx => by rw [← hβψ x hx, hginner x hx]⟩
  · obtain ⟨η', hη'Niso, hη'η, hηη'⟩ := hηN.exists_inv
    have hη'out : ¬ ∃ g ∈ N, ∀ x ∈ N, η' x = g * x * g⁻¹ := by
      rintro ⟨g, hgN, hg⟩
      refine hηout ⟨g⁻¹, N.inv_mem hgN, fun x hx => ?_⟩
      have hηxN : η x ∈ N := hηN.mem x hx
      have h1 : x = g * η x * g⁻¹ := (hη'η x hx).symm.trans (hg (η x) hηxN)
      have h2 : g⁻¹ * x * g = η x := by
        have h := congrArg (fun t => g⁻¹ * t * g) h1
        rw [h]; group
      simpa [inv_inv] using h2.symm
    obtain ⟨g, hgN, hg⟩ := hout η' ψ hη'Niso hψNiso hη'out hin
    have hαη : ∀ x ∈ N, α x = β (η (g * x * g⁻¹)) := by
      intro x hx
      have hψxN : ψ x ∈ N := hψN x hx
      calc α x = β (ψ x) := (hβψ x hx).symm
        _ = β (η (η' (ψ x))) := by rw [hηη' (ψ x) hψxN]
        _ = β (η (g * x * g⁻¹)) := by rw [hg x hx]
    let β₂ : G → G' := fun x => β (η x)
    have hβ₂ : IsIsoOn M M' β₂ := hη.comp hβ
    have hZ₂ : ∀ u ∈ Z, β₂ u = α u := by
      intro u hu
      change β (η u) = α u
      rw [hηZ u hu, hZ u hu]
    exact extend_iso_of_inner hYM hZY hNY hdec hZc hα hβ₂ hZ₂
      ⟨g, hgN, fun x hx => hαη x hx⟩

end CFSG.EvenSporadicStandard.HNRecog.Section4
