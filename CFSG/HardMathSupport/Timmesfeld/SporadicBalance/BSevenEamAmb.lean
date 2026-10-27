module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenEam

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving

section Transport

variable {G Y : Type*} [Group G] [Group Y] {v : G}

private lemma exists_transport (ψ : ↥(Subgroup.centralizer ({v} : Set G)) ≃* Y) {K : Subgroup G}
    (hKD : K ≤ Subgroup.centralizer ({v} : Set G)) :
    ∃ K' : Subgroup Y, (∀ k : ↥(Subgroup.centralizer ({v} : Set G)), ψ k ∈ K' ↔ (k : G) ∈ K) ∧
      Nat.card K' = Nat.card K := by
  refine ⟨(K.subgroupOf (Subgroup.centralizer ({v} : Set G))).map ψ.toMonoidHom, fun k => ?_, ?_⟩
  · exact Subgroup.mem_map_iff_mem (f := ψ.toMonoidHom) ψ.injective
  · rw [Subgroup.card_map_of_injective ψ.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKD).toEquiv

private lemma image_mem_centralizer_iff (ψ : ↥(Subgroup.centralizer ({v} : Set G)) ≃* Y) {x : G}
    (hxv : x ∈ Subgroup.centralizer ({v} : Set G)) (g : ↥(Subgroup.centralizer ({v} : Set G))) :
    ψ g ∈ Subgroup.centralizer ({ψ ⟨x, hxv⟩} : Set Y) ↔
      g.1 ∈ Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
    ← map_mul, ← map_mul, ψ.injective.eq_iff, Subtype.ext_iff]
  rfl

private lemma transport_core (ψ : ↥(Subgroup.centralizer ({v} : Set G)) ≃* Y) {x : G}
    (hxv : x ∈ Subgroup.centralizer ({v} : Set G)) {K : Subgroup G} {K' : Subgroup Y}
    (hK' : ∀ k : ↥(Subgroup.centralizer ({v} : Set G)), ψ k ∈ K' ↔ (k : G) ∈ K)
    (hK : K ≤ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({v} : Set G))
    (hKn : ∀ g ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({v} : Set G),
      ∀ k ∈ K, g * k * g⁻¹ ∈ K) :
    K' ≤ Subgroup.centralizer ({ψ ⟨x, hxv⟩} : Set Y) ∧
      ∀ g ∈ Subgroup.centralizer ({ψ ⟨x, hxv⟩} : Set Y), ∀ k ∈ K', g * k * g⁻¹ ∈ K' := by
  refine ⟨fun k' hk' => ?_, fun g' hg' k' hk' => ?_⟩
  · obtain ⟨k, rfl⟩ := ψ.surjective k'
    exact (image_mem_centralizer_iff ψ hxv k).2 (hK ((hK' k).1 hk')).1
  · obtain ⟨g, rfl⟩ := ψ.surjective g'
    obtain ⟨k, rfl⟩ := ψ.surjective k'
    have hgx : g.1 ∈ Subgroup.centralizer ({x} : Set G) :=
      (image_mem_centralizer_iff ψ hxv g).1 hg'
    have hmem : g.1 * k.1 * g.1⁻¹ ∈ K := hKn g.1 ⟨hgx, g.2⟩ k.1 ((hK' k).1 hk')
    rw [← map_mul, ← map_inv, ← map_mul]
    exact (hK' (g * k * g⁻¹)).2 hmem

private lemma image_mem_iff (ψ : ↥(Subgroup.centralizer ({v} : Set G)) ≃* Y) {Z : Subgroup Y}
    (hZ2 : Nat.card Z = 2) (hv1 : v ≠ 1) {hv : v ∈ Subgroup.centralizer ({v} : Set G)}
    (hψv : ψ ⟨v, hv⟩ ∈ Z) (g : ↥(Subgroup.centralizer ({v} : Set G))) :
    ψ g ∈ Z ↔ g.1 = 1 ∨ g.1 = v := by
  constructor
  · intro hg
    obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : Z)).1 hZ2
    have hne : (⟨ψ ⟨v, hv⟩, hψv⟩ : Z) ≠ 1 := by
      intro h
      have h1 : ψ ⟨v, hv⟩ = 1 := congrArg Subtype.val h
      have h2 : (⟨v, hv⟩ : ↥(Subgroup.centralizer ({v} : Set G))) = 1 :=
        ψ.injective (h1.trans (map_one ψ).symm)
      exact hv1 (congrArg Subtype.val h2)
    by_cases h1 : (⟨ψ g, hg⟩ : Z) = 1
    · left
      have h1' : ψ g = 1 := congrArg Subtype.val h1
      have h2 : g = 1 := ψ.injective (h1'.trans (map_one ψ).symm)
      exact congrArg Subtype.val h2
    · right
      have hb : (⟨ψ g, hg⟩ : Z) = ⟨ψ ⟨v, hv⟩, hψv⟩ := by
        have h1u : (⟨ψ g, hg⟩ : Z) = u := hu _ h1
        have h2u : (⟨ψ ⟨v, hv⟩, hψv⟩ : Z) = u := hu _ hne
        exact h1u.trans h2u.symm
      have hψ : ψ g = ψ ⟨v, hv⟩ := congrArg Subtype.val hb
      exact congrArg Subtype.val (ψ.injective hψ)
  · rintro (h | h)
    · have : g = 1 := Subtype.ext h
      rw [this, map_one]
      exact Z.one_mem
    · have : g = ⟨v, hv⟩ := Subtype.ext h
      rw [this]
      exact hψv

end Transport

section Ambient

variable {G Y R : Type*} [Group G] [Finite G] [Group Y] [Group R] {p : ℕ} {Z Y' : Subgroup Y}
  [Z.Normal]

theorem eam_odd_eq_bot_ambient (hp : p.Prime) (hp2 : p ≠ 2) (hZc : Z ≤ Subgroup.center Y)
    (hZ2 : Nat.card Z = 2) (hY' : Y'.index = 2) (hZY' : Z ≤ Y')
    (φ : Y' ⧸ Z.subgroupOf Y' ≃* R)
    (hR : ∀ s : R, orderOf s = p →
      GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set R)) = ⊥)
    {v : G} (ψ : ↥(Subgroup.centralizer ({v} : Set G)) ≃* Y) {x : G}
    (hxv : x ∈ Subgroup.centralizer ({v} : Set G)) (hx : orderOf x = p) {K : Subgroup G}
    (hK : K ≤ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({v} : Set G))
    (hKn : ∀ g ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({v} : Set G),
      ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hodd : Odd (Nat.card K)) (hKp : ¬ p ∣ Nat.card K) : K = ⊥ := by
  haveI : Finite Y := Finite.of_equiv _ ψ.toEquiv
  have hKD : K ≤ Subgroup.centralizer ({v} : Set G) := hK.trans inf_le_right
  obtain ⟨K', hK'mem, hK'card⟩ := exists_transport ψ hKD
  obtain ⟨hle, hn⟩ := transport_core ψ hxv hK'mem hK hKn
  have hx' : orderOf (ψ ⟨x, hxv⟩) = p := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx]
  have hbot : K' = ⊥ :=
    eam_odd_eq_bot hp hp2 hZc hZ2 hY' hZY' φ hR hx' hle hn (hK'card ▸ hodd) (hK'card ▸ hKp)
  rw [eq_bot_iff]
  intro k hk
  have hkD : k ∈ Subgroup.centralizer ({v} : Set G) := hKD hk
  have hk' : ψ ⟨k, hkD⟩ ∈ K' := (hK'mem ⟨k, hkD⟩).2 hk
  rw [hbot, Subgroup.mem_bot] at hk'
  have h1 : (⟨k, hkD⟩ : ↥(Subgroup.centralizer ({v} : Set G))) = 1 :=
    ψ.injective (hk'.trans (map_one ψ).symm)
  exact congrArg Subtype.val h1

theorem eam_le_center_ambient (hp : p.Prime) (hp2 : p ≠ 2) (hZc : Z ≤ Subgroup.center Y)
    (hZ2 : Nat.card Z = 2) (hY' : Y'.index = 2) (hZY' : Z ≤ Y')
    (φ : Y' ⧸ Z.subgroupOf Y' ≃* R)
    (hR : ∀ s : R, orderOf s = p →
      GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set R)) = ⊥)
    (hR6 : ∀ s : R, orderOf s = p → ∀ r ∈ Subgroup.centralizer ({s} : Set R), orderOf r ≠ 6)
    {v : G} (ψ : ↥(Subgroup.centralizer ({v} : Set G)) ≃* Y) (hv2 : v ^ 2 = 1) (hv1 : v ≠ 1)
    (hψv : ∃ hv : v ∈ Subgroup.centralizer ({v} : Set G), ψ ⟨v, hv⟩ ∈ Z) {x : G}
    (hxv : x ∈ Subgroup.centralizer ({v} : Set G)) (hx : orderOf x = p) {w y : G}
    (hwx : w ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({v} : Set G))
    (hyx : y ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({v} : Set G))
    (hw6 : w ^ 6 = 1) (hw2 : w ^ 2 ≠ 1 ∧ w ^ 2 ≠ v) (hw3 : w ^ 3 ≠ 1 ∧ w ^ 3 ≠ v)
    (hwy : w ^ 3 * y * (w ^ 3)⁻¹ * y⁻¹ ≠ 1 ∧ w ^ 3 * y * (w ^ 3)⁻¹ * y⁻¹ ≠ v)
    {K : Subgroup G}
    (hK : K ≤ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({v} : Set G))
    (hKn : ∀ g ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({v} : Set G),
      ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hKp : ¬ p ∣ Nat.card K) : ∀ k ∈ K, k = 1 ∨ k = v := by
  obtain ⟨hv, hψv⟩ := hψv
  haveI : Finite Y := Finite.of_equiv _ ψ.toEquiv
  have hKD : K ≤ Subgroup.centralizer ({v} : Set G) := hK.trans inf_le_right
  obtain ⟨K', hK'mem, hK'card⟩ := exists_transport ψ hKD
  obtain ⟨hle, hn⟩ := transport_core ψ hxv hK'mem hK hKn
  have hx' : orderOf (ψ ⟨x, hxv⟩) = p := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx]
  have hZmem := image_mem_iff ψ hZ2 hv1 hψv
  have hwD : w ∈ Subgroup.centralizer ({v} : Set G) := hwx.2
  have hyD : y ∈ Subgroup.centralizer ({v} : Set G) := hyx.2
  have hwx' : ψ ⟨w, hwD⟩ ∈ Subgroup.centralizer ({ψ ⟨x, hxv⟩} : Set Y) :=
    (image_mem_centralizer_iff ψ hxv ⟨w, hwD⟩).2 hwx.1
  have hyx' : ψ ⟨y, hyD⟩ ∈ Subgroup.centralizer ({ψ ⟨x, hxv⟩} : Set Y) :=
    (image_mem_centralizer_iff ψ hxv ⟨y, hyD⟩).2 hyx.1
  have hw6' : (ψ ⟨w, hwD⟩) ^ 6 = 1 := by
    rw [← map_pow]
    have : (⟨w, hwD⟩ : ↥(Subgroup.centralizer ({v} : Set G))) ^ 6 = 1 := Subtype.ext hw6
    rw [this, map_one]
  have hw2' : (ψ ⟨w, hwD⟩) ^ 2 ∉ Z := by
    rw [← map_pow, hZmem]
    rintro (h | h)
    · exact hw2.1 h
    · exact hw2.2 h
  have hw3' : (ψ ⟨w, hwD⟩) ^ 3 ∉ Z := by
    rw [← map_pow, hZmem]
    rintro (h | h)
    · exact hw3.1 h
    · exact hw3.2 h
  have hwy' : (ψ ⟨w, hwD⟩) ^ 3 * ψ ⟨y, hyD⟩ * ((ψ ⟨w, hwD⟩) ^ 3)⁻¹ * (ψ ⟨y, hyD⟩)⁻¹ ∉ Z := by
    rw [← map_pow, ← map_mul, ← map_inv, ← map_mul, ← map_inv, ← map_mul, hZmem]
    rintro (h | h)
    · exact hwy.1 h
    · exact hwy.2 h
  have hKZ : K' ≤ Z :=
    eam_le_center hp hp2 hZc hZ2 hY' hZY' φ hR hR6 hx' hwx' hyx' hw6' hw2' hw3' hwy' hle hn
      (hK'card ▸ hKp)
  intro k hk
  exact (hZmem ⟨k, hKD hk⟩).1 (hKZ ((hK'mem ⟨k, hKD hk⟩).2 hk))

end Ambient

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven
