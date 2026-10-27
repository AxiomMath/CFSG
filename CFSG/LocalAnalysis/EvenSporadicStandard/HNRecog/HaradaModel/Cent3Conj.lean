module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Facts3

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup

variable {G : Type} [Group G]

@[expose] def OddNormalAt (x : G) : Prop :=
  ∀ N : Subgroup G, N ≤ centralizer ({x} : Set G) →
    (∀ c ∈ centralizer ({x} : Set G), ∀ n ∈ N, c * n * c⁻¹ ∈ N) → Odd (Nat.card N) →
      N ≤ zpowers x

@[expose] def CardTTAt (a z z₁ x : G) : Prop :=
  Set.ncard {y : G | y ∈ centralizer ({x} : Set G) ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧ tTH a z z₁ y} = 46

@[expose] def Perfect60At (x : G) : Prop :=
  ∃ M : Subgroup G, M ≤ centralizer ({x} : Set G) ∧ ⁅M, M⁆ = M ∧ Nat.card M = 60 ∧
    M ⊓ zpowers x = ⊥

@[expose] def WCommAt (a z z₁ x : G) : Prop :=
  ∃ s : G, s ∈ centralizer ({x} : Set G) ∧ s ^ 2 = 1 ∧ s ≠ 1 ∧ tTH a z z₁ s ∧
    s ∈ ⁅WsubH a z z₁ x, WsubH a z z₁ x⁆

private lemma isConj_conj_iff {g y w : G} : IsConj (g * y * g⁻¹) w ↔ IsConj y w := by
  constructor
  · intro h
    exact (isConj_iff.2 ⟨g, rfl⟩).trans h
  · intro h
    exact (isConj_iff.2 ⟨g⁻¹, by group⟩).trans h

theorem tTH_conj_iff (a z z₁ g y : G) : tTH a z z₁ (g * y * g⁻¹) ↔ tTH a z z₁ y := by
  unfold tTH
  rw [isConj_conj_iff, isConj_conj_iff, isConj_conj_iff]

private lemma mem_centralizer_conj_singleton_iff {c x w : G} :
    w ∈ centralizer ({c * x * c⁻¹} : Set G) ↔ c⁻¹ * w * c ∈ centralizer ({x} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc c⁻¹ * w * c * x = c⁻¹ * (w * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * x * c⁻¹) * w) * c := by rw [h]
      _ = x * (c⁻¹ * w * c) := by group
  · intro h
    calc w * (c * x * c⁻¹) = c * (c⁻¹ * w * c * x) * c⁻¹ := by group
      _ = c * (x * (c⁻¹ * w * c)) * c⁻¹ := by rw [h]
      _ = (c * x * c⁻¹) * w := by group

private lemma conj_conj_apply (c d : G) : (MulAut.conj c⁻¹) ((MulAut.conj c) d) = d := by
  simp only [MulAut.conj_apply]
  group

private lemma conj_conj_apply' (c d : G) : (MulAut.conj c) ((MulAut.conj c⁻¹) d) = d := by
  simp only [MulAut.conj_apply]
  group

private lemma conjHom_injective (c : G) : Function.Injective (MulAut.conj c).toMonoidHom :=
  fun _ _ h => (MulAut.conj c).injective h

private lemma tT_set_conj (a z z₁ c x : G) :
    {w : G | w ∈ centralizer ({c * x * c⁻¹} : Set G) ∧ w ^ 2 = 1 ∧ w ≠ 1 ∧ tTH a z z₁ w} =
    (MulAut.conj c) ''
      {w : G | w ∈ centralizer ({x} : Set G) ∧ w ^ 2 = 1 ∧ w ≠ 1 ∧ tTH a z z₁ w} := by
  ext w
  constructor
  · rintro ⟨hwc, hw2, hw1, hwt⟩
    refine ⟨(MulAut.conj c⁻¹) w, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa [MulAut.conj_apply] using
        (mem_centralizer_conj_singleton_iff (c := c) (x := x) (w := w)).mp hwc
    · rw [← map_pow, hw2, map_one]
    · intro h
      exact hw1 (by
        have := congrArg (MulAut.conj c) h
        rw [conj_conj_apply'] at this
        simpa using this)
    · exact (tTH_conj_iff a z z₁ c⁻¹ w).mpr hwt
    · exact conj_conj_apply' c w
  · rintro ⟨u, ⟨huc, hu2, hu1, hut⟩, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine (mem_centralizer_conj_singleton_iff (c := c) (x := x)
        (w := (MulAut.conj c) u)).mpr ?_
      have h : c⁻¹ * (MulAut.conj c) u * c = u := by simpa using conj_conj_apply c u
      rw [h]
      exact huc
    · rw [← map_pow, hu2, map_one]
    · intro h
      exact hu1 (by
        have := congrArg (MulAut.conj c⁻¹) h
        rw [conj_conj_apply] at this
        simpa using this)
    · exact (tTH_conj_iff a z z₁ c u).mpr hut

private lemma WsubH_conj (a z z₁ c x : G) :
    WsubH a z z₁ (c * x * c⁻¹) = (WsubH a z z₁ x).map (MulAut.conj c).toMonoidHom := by
  unfold WsubH
  rw [MonoidHom.map_closure, tT_set_conj]
  rfl

theorem OddNormalAt.of_isConj {x y : G} (h : OddNormalAt x) (hxy : IsConj x y) :
    OddNormalAt y := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
  intro N hNle hNnorm hNodd
  let φ : G →* G := (MulAut.conj c).toMonoidHom
  let ψ : G →* G := (MulAut.conj c⁻¹).toMonoidHom
  let N₀ : Subgroup G := N.map ψ
  have hψinj : Function.Injective ψ := conjHom_injective c⁻¹
  have hN₀le : N₀ ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨n, hn, rfl⟩
    simpa [ψ, MulAut.conj_apply] using
      (mem_centralizer_conj_singleton_iff (c := c) (x := x) (w := n)).mp (hNle hn)
  have hN₀norm : ∀ d ∈ centralizer ({x} : Set G), ∀ m ∈ N₀, d * m * d⁻¹ ∈ N₀ := by
    rintro d hd _ ⟨n, hn, rfl⟩
    refine ⟨(MulAut.conj c) d * n * ((MulAut.conj c) d)⁻¹, ?_, ?_⟩
    · apply hNnorm ((MulAut.conj c) d)
      · refine (mem_centralizer_conj_singleton_iff (c := c) (x := x)
          (w := (MulAut.conj c) d)).mpr ?_
        have h : c⁻¹ * (MulAut.conj c) d * c = d := by simpa using conj_conj_apply c d
        rw [h]
        exact hd
      · exact hn
    · have h1 : ψ ((MulAut.conj c) d) = d := conj_conj_apply c d
      rw [map_mul, map_mul, map_inv, h1]
  have hN₀card : Nat.card N₀ = Nat.card N := by
    show Nat.card (N.map ψ) = Nat.card N
    rw [Subgroup.card_map_of_injective (f := ψ) hψinj]
  have hN₀odd : Odd (Nat.card N₀) := by rw [hN₀card]; exact hNodd
  have hle : N₀ ≤ zpowers x := h N₀ hN₀le hN₀norm hN₀odd
  intro n hn
  have hψn : ψ n ∈ N₀ := ⟨n, hn, rfl⟩
  have hmem : ψ n ∈ zpowers x := hle hψn
  rw [Subgroup.mem_zpowers_iff] at hmem ⊢
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, ?_⟩
  have hn_eq : n = φ (ψ n) := by
    show n = (MulAut.conj c) ((MulAut.conj c⁻¹) n)
    rw [conj_conj_apply']
  rw [hn_eq, ← hk]
  show (c * x * c⁻¹) ^ k = (MulAut.conj c) (x ^ k)
  rw [map_zpow]
  rfl

theorem CardTTAt.of_isConj {a z z₁ x y : G} (h : CardTTAt a z z₁ x) (hxy : IsConj x y) :
    CardTTAt a z z₁ y := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
  unfold CardTTAt at h ⊢
  rw [tT_set_conj a z z₁ c x,
    Set.ncard_image_of_injective (f := MulAut.conj c) _ (MulAut.conj c).injective]
  exact h

theorem Perfect60At.of_isConj {x y : G} (h : Perfect60At x) (hxy : IsConj x y) :
    Perfect60At y := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
  obtain ⟨M, hMle, hMcomm, hMcard, hMinf⟩ := h
  let φ : G →* G := (MulAut.conj c).toMonoidHom
  refine ⟨M.map φ, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨m, hm, rfl⟩
    refine (mem_centralizer_conj_singleton_iff (c := c) (x := x)
      (w := (MulAut.conj c) m)).mpr ?_
    have h : c⁻¹ * (MulAut.conj c) m * c = m := by simpa using conj_conj_apply c m
    rw [h]
    exact hMle hm
  · rw [← Subgroup.map_commutator, hMcomm]
  · rw [Subgroup.card_map_of_injective (f := φ) (conjHom_injective c)]
    exact hMcard
  · have hz : zpowers (c * x * c⁻¹) = (zpowers x).map φ := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [hz, ← Subgroup.map_inf M (zpowers x) φ (conjHom_injective c), hMinf, Subgroup.map_bot]

theorem WCommAt.of_isConj {a z z₁ x y : G} (h : WCommAt a z z₁ x) (hxy : IsConj x y) :
    WCommAt a z z₁ y := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
  obtain ⟨s, hsx, hs2, hs1, hst, hscomm⟩ := h
  refine ⟨c * s * c⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · refine (mem_centralizer_conj_singleton_iff (c := c) (x := x)
      (w := c * s * c⁻¹)).mpr ?_
    have h : c⁻¹ * (c * s * c⁻¹) * c = s := by group
    rw [h]
    exact hsx
  · show (c * s * c⁻¹) ^ 2 = 1
    rw [conj_pow, hs2]
    group
  · intro h
    exact hs1 (by
      calc s = c⁻¹ * (c * s * c⁻¹) * c := by group
        _ = c⁻¹ * 1 * c := by rw [h]
        _ = 1 := by group)
  · exact (tTH_conj_iff a z z₁ c s).mpr hst
  · rw [WsubH_conj a z z₁ c x, ← Subgroup.map_commutator]
    exact Subgroup.mem_map.mpr ⟨s, hscomm, rfl⟩

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
