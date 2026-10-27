module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigSig
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Catalog
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.U43

open Subgroup CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

theorem mem_centralizer_of_derived {X : Type} [Group X] {t l : X} (hl : l ∈ centralizerDerived t) :
    l ∈ centralizer ({t} : Set X) := by
  obtain ⟨l', -, rfl⟩ := hl
  exact l'.2

theorem sigRel_of_sigmaConfig {X : Type} [Group X] {t y c k : X} (h : SigmaConfig t y c k) :
    SigRel t y c k := by
  obtain ⟨hy3, hyd, hc3, hkk, hk1, hyc, hycp, hccp, hyk, h27, hkc, hkcp, hkkp⟩ := h
  exact ⟨(mem_centralizer_singleton_iff.1 (mem_centralizer_of_derived hyd)).symm, hy3, hc3, hkk,
    hk1, hyc, hycp, hccp, hyk, h27, hkc, hkcp, hkkp⟩

theorem card_centralizer_map {X M : Type*} [Group X] [Group M] (ι : X →* M)
    (hι : Function.Injective ι) (S : Set X) :
    Nat.card ↥(centralizer S) = Nat.card ↥(ι.range ⊓ centralizer (ι '' S)) := by
  have : (centralizer S).map ι = ι.range ⊓ centralizer (ι '' S) := by
    ext z
    simp only [mem_map, mem_inf, MonoidHom.mem_range, mem_centralizer_iff,
      Set.forall_mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, rfl⟩, fun s hs => by rw [← map_mul, ← map_mul, hx s hs]⟩
    · rintro ⟨⟨x, rfl⟩, hc⟩
      exact ⟨x, fun s hs => hι (by rw [map_mul, map_mul]; exact hc hs), rfl⟩
  rw [← this]
  exact (Subgroup.card_map_of_injective hι).symm

theorem card_five_conj {M : Type*} [Group M] (G : Subgroup M) {a : M} (ha : a ∈ G)
    (T y c k : M) :
    Nat.card ↥(G ⊓ centralizer ({a * y * a⁻¹, a * c * a⁻¹,
      (a * T * a⁻¹) * (a * c * a⁻¹) * (a * T * a⁻¹)⁻¹, a * k * a⁻¹,
      (a * T * a⁻¹) * (a * k * a⁻¹) * (a * T * a⁻¹)⁻¹} : Set M)) =
    Nat.card ↥(G ⊓ centralizer ({y, c, T * c * T⁻¹, k, T * k * T⁻¹} : Set M)) := by
  have hset : (fun x => a * x * a⁻¹) '' ({y, c, T * c * T⁻¹, k, T * k * T⁻¹} : Set M) =
      {a * y * a⁻¹, a * c * a⁻¹, (a * T * a⁻¹) * (a * c * a⁻¹) * (a * T * a⁻¹)⁻¹, a * k * a⁻¹,
        (a * T * a⁻¹) * (a * k * a⁻¹) * (a * T * a⁻¹)⁻¹} := by
    simp only [Set.image_insert_eq, Set.image_singleton]
    have e1 : a * (T * c * T⁻¹) * a⁻¹ = (a * T * a⁻¹) * (a * c * a⁻¹) * (a * T * a⁻¹)⁻¹ := by group
    have e2 : a * (T * k * T⁻¹) * a⁻¹ = (a * T * a⁻¹) * (a * k * a⁻¹) * (a * T * a⁻¹)⁻¹ := by group
    rw [e1, e2]
  rw [← hset]
  exact card_inf_centralizer_conj_set G ha _

theorem eq_one_or_of_mem_zpowers {M : Type*} [Group M] {T : M} (hT2 : T * T = 1) {x : M}
    (hx : x ∈ zpowers T) : x = 1 ∨ x = T := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hx
  have hsq : T ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hT2
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    have : n = 2 * (n / 2) := by omega
    rw [this, zpow_mul, hsq, one_zpow]
  · right
    have : n = 2 * (n / 2) + 1 := by omega
    rw [this, zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]

theorem centre_transport {X M : Type} [Group X] [Group M] (ι : X →* M)
    (hι : Function.Injective ι) {t : X} (hT2 : ι t * ι t = 1)
    (hZX : ∀ g ∈ centralizer ({t} : Set X),
      (∀ l ∈ centralizerDerived t, g * l = l * g) → g ∈ zpowers t) {a : M} (ha : a ∈ ι.range) :
    ∀ z ∈ ι.range ⊓ centralizer ({a * ι t * a⁻¹} : Set M),
      (∀ x ∈ ι.range ⊓ centralizer ({a * ι t * a⁻¹} : Set M), z * x = x * z) →
        z = 1 ∨ z = a * ι t * a⁻¹ := by
  intro z hz hcomm
  obtain ⟨a₀, rfl⟩ := MonoidHom.mem_range.1 ha
  obtain ⟨hzr, hzc⟩ := mem_inf.1 hz
  obtain ⟨z₀, rfl⟩ := MonoidHom.mem_range.1 hzr
  have hzc' : ι z₀ * ι (a₀ * t * a₀⁻¹) = ι (a₀ * t * a₀⁻¹) * ι z₀ := by
    have := mem_centralizer_singleton_iff.1 hzc
    simpa only [map_mul, map_inv] using this
  have hzc'' : z₀ * (a₀ * t * a₀⁻¹) = (a₀ * t * a₀⁻¹) * z₀ := by
    apply hι
    have := hzc'
    rwa [← map_mul, ← map_mul] at this
  set g := a₀⁻¹ * z₀ * a₀ with hg
  have hgt : g ∈ centralizer ({t} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    calc g * t = a₀⁻¹ * (z₀ * (a₀ * t * a₀⁻¹)) * a₀ := by rw [hg]; group
      _ = a₀⁻¹ * ((a₀ * t * a₀⁻¹) * z₀) * a₀ := by rw [hzc'']
      _ = t * g := by rw [hg]; group
  have hgl : ∀ l ∈ centralizerDerived t, g * l = l * g := by
    intro l hl
    have hlt := mem_centralizer_singleton_iff.1 (mem_centralizer_of_derived hl)
    have hmem : ι (a₀ * l * a₀⁻¹) ∈ ι.range ⊓ centralizer ({ι a₀ * ι t * (ι a₀)⁻¹} : Set M) := by
      refine mem_inf.2 ⟨⟨_, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
      have : ι (a₀ * l * a₀⁻¹) * ι (a₀ * t * a₀⁻¹) = ι (a₀ * t * a₀⁻¹) * ι (a₀ * l * a₀⁻¹) := by
        rw [← map_mul, ← map_mul]
        congr 1
        calc a₀ * l * a₀⁻¹ * (a₀ * t * a₀⁻¹) = a₀ * (l * t) * a₀⁻¹ := by group
          _ = a₀ * (t * l) * a₀⁻¹ := by rw [hlt]
          _ = a₀ * t * a₀⁻¹ * (a₀ * l * a₀⁻¹) := by group
      simpa only [map_mul, map_inv] using this
    have h1 := hcomm _ hmem
    have h2 : z₀ * (a₀ * l * a₀⁻¹) = (a₀ * l * a₀⁻¹) * z₀ := by
      apply hι
      have := h1
      rwa [← map_mul, ← map_mul] at this
    calc g * l = a₀⁻¹ * (z₀ * (a₀ * l * a₀⁻¹)) * a₀ := by rw [hg]; group
      _ = a₀⁻¹ * ((a₀ * l * a₀⁻¹) * z₀) * a₀ := by rw [h2]
      _ = l * g := by rw [hg]; group
  have hgz := hZX g hgt hgl
  have hι2 : ι t * ι t = 1 := hT2
  have hmap : ι g ∈ zpowers (ι t) := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hgz
    exact mem_zpowers_iff.2 ⟨n, by rw [← hn, map_zpow]⟩
  rcases eq_one_or_of_mem_zpowers hι2 hmap with h | h
  · left
    have : g = 1 := hι (by rw [h, map_one])
    have hz0 : z₀ = 1 := by
      calc z₀ = a₀ * g * a₀⁻¹ := by rw [hg]; group
        _ = 1 := by rw [this]; group
    rw [hz0, map_one]
  · right
    have : g = t := hι h
    have hz0 : z₀ = a₀ * t * a₀⁻¹ := by
      calc z₀ = a₀ * g * a₀⁻¹ := by rw [hg]; group
        _ = a₀ * t * a₀⁻¹ := by rw [this]
    rw [hz0, map_mul, map_mul, map_inv]

end CFSG.EvenSporadicStandard.HSStd.U43
