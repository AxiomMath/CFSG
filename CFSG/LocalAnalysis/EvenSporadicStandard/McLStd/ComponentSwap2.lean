module

public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.ComponentSwap

public section

namespace CFSG.EvenSporadicStandard.McLStd

open Subgroup CFSG

variable {Y : Type*} [Group Y]

@[expose] def SwapCommuting (s : Y) (K : Subgroup Y) : Prop :=
  ∀ x y : Y, x ∈ centralizer ({s} : Set Y) → y ∈ centralizer ({s} : Set Y) →
    (∀ k ∈ K ⊔ conjSub s K, x * k = k * x) → (∀ k ∈ K ⊔ conjSub s K, y * k = k * y) →
    x * y = y * x

variable [Finite Y]

theorem eq_of_swapped_component' {s : Y} (hs : s * s = 1) {K : Subgroup Y} (hK : IsComponent K)
    (hD : SwapCommuting s K) {N : Subgroup Y} (hN : IsComponent N) (hNs : conjSub s N ≠ N) :
    N = K ∨ N = conjSub s K := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hNK, hNKs⟩ := hcon
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hKc : IsComponent (conjSub s K) := LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hK
  have hNc : IsComponent (conjSub s N) := LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hN
  have hcomm : ∀ {A C : Subgroup Y}, IsComponent A → IsComponent C → A ≠ C →
      ∀ a ∈ A, ∀ c ∈ C, a * c = c * a := by
    intro A C hA hC hne a ha c hc
    have h0 := (LocalCores.distinct_components_commute hA hC).resolve_left hne
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h0 ha
    exact ((mem_centralizer_iff.1 h1) c hc).symm
  have hN_Ns : N ≠ conjSub s N := fun h => hNs h.symm
  have hNs_K : conjSub s N ≠ K := by
    intro h
    apply hNKs
    rw [← conjSub_conjSub hs N, h]
  have hNs_Ks : conjSub s N ≠ conjSub s K := by
    intro h
    apply hNK
    rw [← conjSub_conjSub hs N, h, conjSub_conjSub hs K]
  have hm : ∀ n ∈ N, s * n * s ∈ conjSub s N := by
    intro n hn
    rw [mem_conjSub, hsi]
    have : s * (s * n * s) * s = n := by
      calc s * (s * n * s) * s = (s * s) * n * (s * s) := by group
        _ = n := by rw [hs]; group
    rw [this]; exact hn
  have hNNs : ∀ a ∈ N, ∀ c ∈ conjSub s N, a * c = c * a := hcomm hN hNc hN_Ns
  have hNK' : ∀ a ∈ N, ∀ c ∈ K, a * c = c * a := hcomm hN hK hNK
  have hNKs' : ∀ a ∈ N, ∀ c ∈ conjSub s K, a * c = c * a := hcomm hN hKc hNKs
  have hNsK : ∀ a ∈ conjSub s N, ∀ c ∈ K, a * c = c * a := hcomm hNc hK hNs_K
  have hNsKs : ∀ a ∈ conjSub s N, ∀ c ∈ conjSub s K, a * c = c * a := hcomm hNc hKc hNs_Ks
  have hcE : ∀ x : Y, (∀ k ∈ K, x * k = k * x) → (∀ k ∈ conjSub s K, x * k = k * x) →
      ∀ k ∈ K ⊔ conjSub s K, x * k = k * x := by
    intro x h1 h2
    have hle : K ⊔ conjSub s K ≤ centralizer ({x} : Set Y) :=
      sup_le (fun k hk => mem_centralizer_singleton_iff.2 (h1 k hk).symm)
        (fun k hk => mem_centralizer_singleton_iff.2 (h2 k hk).symm)
    exact fun k hk => (mem_centralizer_singleton_iff.1 (hle hk)).symm
  have hdata : ∀ n ∈ N, n * (s * n * s) ∈ centralizer ({s} : Set Y) ∧
      ∀ k ∈ K ⊔ conjSub s K, (n * (s * n * s)) * k = k * (n * (s * n * s)) := by
    intro n hn
    have hmn := hm n hn
    have hcomm1 : (s * n * s) * n = n * (s * n * s) := (hNNs n hn _ hmn).symm
    have hds : (n * (s * n * s)) * s = s * (n * (s * n * s)) := by
      have h1 : (n * (s * n * s)) * s = ((s * n * s) * n) * s := by rw [hcomm1]
      rw [h1]; group
    refine ⟨mem_centralizer_singleton_iff.2 hds, hcE _ (fun k hk => ?_) (fun k hk => ?_)⟩
    · calc n * (s * n * s) * k = n * ((s * n * s) * k) := mul_assoc _ _ _
        _ = n * (k * (s * n * s)) := by rw [← hNsK _ hmn k hk]
        _ = (n * k) * (s * n * s) := (mul_assoc _ _ _).symm
        _ = (k * n) * (s * n * s) := by rw [hNK' n hn k hk]
        _ = k * (n * (s * n * s)) := mul_assoc _ _ _
    · calc n * (s * n * s) * k = n * ((s * n * s) * k) := mul_assoc _ _ _
        _ = n * (k * (s * n * s)) := by rw [← hNsKs _ hmn k hk]
        _ = (n * k) * (s * n * s) := (mul_assoc _ _ _).symm
        _ = (k * n) * (s * n * s) := by rw [hNKs' n hn k hk]
        _ = k * (n * (s * n * s)) := mul_assoc _ _ _
  obtain ⟨n₁, hn₁, n₂, hn₂, hnc⟩ := exists_noncentral_commutator hN.1
  have hm₁ := hm n₁ hn₁
  have hm₂ := hm n₂ hn₂
  obtain ⟨hs₁, hE₁⟩ := hdata n₁ hn₁
  obtain ⟨hs₂, hE₂⟩ := hdata n₂ hn₂
  have hdd : (n₁ * (s * n₁ * s)) * (n₂ * (s * n₂ * s)) =
      (n₂ * (s * n₂ * s)) * (n₁ * (s * n₁ * s)) := hD _ _ hs₁ hs₂ hE₁ hE₂
  have key : n₁ * n₂ * ((s * n₁ * s) * (s * n₂ * s)) =
      n₂ * n₁ * ((s * n₂ * s) * (s * n₁ * s)) := by
    have c1 : n₂ * (s * n₁ * s) = (s * n₁ * s) * n₂ := hNNs n₂ hn₂ _ hm₁
    have c2 : n₁ * (s * n₂ * s) = (s * n₂ * s) * n₁ := hNNs n₁ hn₁ _ hm₂
    calc n₁ * n₂ * ((s * n₁ * s) * (s * n₂ * s))
        = n₁ * (n₂ * (s * n₁ * s)) * (s * n₂ * s) := by group
      _ = n₁ * ((s * n₁ * s) * n₂) * (s * n₂ * s) := by rw [c1]
      _ = (n₁ * (s * n₁ * s)) * (n₂ * (s * n₂ * s)) := by group
      _ = (n₂ * (s * n₂ * s)) * (n₁ * (s * n₁ * s)) := hdd
      _ = n₂ * ((s * n₂ * s) * n₁) * (s * n₁ * s) := by group
      _ = n₂ * (n₁ * (s * n₂ * s)) * (s * n₁ * s) := by rw [← c2]
      _ = n₂ * n₁ * ((s * n₂ * s) * (s * n₁ * s)) := by group
  have hc_eq : (n₂ * n₁)⁻¹ * (n₁ * n₂) =
      ((s * n₂ * s) * (s * n₁ * s)) * ((s * n₁ * s) * (s * n₂ * s))⁻¹ := by
    calc (n₂ * n₁)⁻¹ * (n₁ * n₂)
        = (n₂ * n₁)⁻¹ * (n₁ * n₂ * ((s * n₁ * s) * (s * n₂ * s))) *
            ((s * n₁ * s) * (s * n₂ * s))⁻¹ := by group
      _ = (n₂ * n₁)⁻¹ * (n₂ * n₁ * ((s * n₂ * s) * (s * n₁ * s))) *
            ((s * n₁ * s) * (s * n₂ * s))⁻¹ := by rw [key]
      _ = ((s * n₂ * s) * (s * n₁ * s)) * ((s * n₁ * s) * (s * n₂ * s))⁻¹ := by group
  have hcmem : (n₂ * n₁)⁻¹ * (n₁ * n₂) ∈ conjSub s N := by
    rw [hc_eq]
    exact (conjSub s N).mul_mem ((conjSub s N).mul_mem hm₂ hm₁)
      ((conjSub s N).inv_mem ((conjSub s N).mul_mem hm₁ hm₂))
  exact hnc fun x hx => hNNs x hx _ hcmem

theorem exists_hom_of_swapped_component' {s : Y} (hs : s * s = 1) {K : Subgroup Y}
    (hK : IsComponent K) (hKs : conjSub s K ≠ K) (hD : SwapCommuting s K) :
    ∃ φ : Y →* Multiplicative (ZMod 2), φ s ≠ 1 := by
  classical
  have : Fintype {N : Subgroup Y // IsComponent N} := Fintype.ofFinite _
  refine ⟨unitsToZMod2.comp (Equiv.Perm.sign.comp compAct), ?_⟩
  apply unitsToZMod2_ne_one
  intro hsign
  have hsq : compAct s * compAct s = 1 := by rw [← map_mul, hs, map_one]
  have h4 := M11Std.four_dvd_card_support_of_sign_eq_one hsq hsign
  have hKc : IsComponent (conjSub s K) := LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hK
  have hne : (⟨K, hK⟩ : {N : Subgroup Y // IsComponent N}) ≠ ⟨conjSub s K, hKc⟩ :=
    fun h => hKs (congrArg Subtype.val h).symm
  have hsupp : (compAct s).support = {⟨K, hK⟩, ⟨conjSub s K, hKc⟩} := by
    ext N
    rw [Equiv.Perm.mem_support, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hmoved
      have hmoved' : conjSub s N.1 ≠ N.1 := fun h => hmoved (Subtype.ext h)
      rcases eq_of_swapped_component' hs hK hD N.2 hmoved' with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact fun h => hKs (congrArg Subtype.val h)
      · intro h
        have h' : conjSub s (conjSub s K) = conjSub s K := congrArg Subtype.val h
        rw [conjSub_conjSub hs] at h'
        exact hKs h'.symm
  rw [hsupp, Finset.card_pair hne] at h4
  omega

end CFSG.EvenSporadicStandard.McLStd
