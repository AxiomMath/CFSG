
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7Base

public import Certificates.Certificate4128

public section

namespace CFSG.QuasithinUnique.L246.C123

open Equiv

section Explicit

theorem sylowSet_mul :
    ∀ a ∈ sylowSet, ∀ b ∈ sylowSet, a * b ∈ sylowSet :=
  Certificates.certificate4128.1
theorem sylowSet_inv : ∀ a ∈ sylowSet, a⁻¹ ∈ sylowSet :=
  Certificates.certificate4128.2.1
theorem sylowSet_one : (1 : Perm (Fin 7)) ∈ sylowSet :=
  Certificates.certificate4128.2.2.1
theorem sylowSet_card : sylowSet.card = 8 :=
  Certificates.certificate4128.2.2.2.1
theorem sylowSet_sign : ∀ a ∈ sylowSet, Perm.sign a = 1 :=
  Certificates.certificate4128.2.2.2.2.1
theorem kleinSet_mul :
    ∀ a ∈ kleinSet, ∀ b ∈ kleinSet, a * b ∈ kleinSet :=
  Certificates.certificate4128.2.2.2.2.2.1
theorem kleinSet_inv : ∀ a ∈ kleinSet, a⁻¹ ∈ kleinSet :=
  Certificates.certificate4128.2.2.2.2.2.2.1
theorem kleinSet_one : (1 : Perm (Fin 7)) ∈ kleinSet :=
  Certificates.certificate4128.2.2.2.2.2.2.2.1
theorem kleinSet_card : kleinSet.card = 4 :=
  Certificates.certificate4128.2.2.2.2.2.2.2.2.1
theorem kleinSet_subset : kleinSet ⊆ sylowSet :=
  Certificates.certificate4128.2.2.2.2.2.2.2.2.2.1
theorem x7_mem : x7 ∈ kleinSet :=
  Certificates.certificate4128.2.2.2.2.2.2.2.2.2.2.1
theorem y7_mem : y7 ∈ kleinSet :=
  Certificates.certificate4128.2.2.2.2.2.2.2.2.2.2.2.1
theorem z7_mem : z7 ∈ sylowSet :=
  Certificates.certificate4128.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem normalizer_sylowSet : ∀ g : Perm (Fin 7), Perm.sign g = 1 →
    g * x7 * g⁻¹ ∈ sylowSet → g * y7 * g⁻¹ ∈ sylowSet → g * z7 * g⁻¹ ∈ sylowSet →
      g ∈ sylowSet :=
  Certificates.certificate4128.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem klein_unique : ∀ c : Perm (Fin 7), Perm.sign c = 1 →
    c * x7 * c⁻¹ ∈ sylowSet → c * y7 * c⁻¹ ∈ sylowSet →
      (c * x7 * c⁻¹ ∈ kleinSet ∧ c * y7 * c⁻¹ ∈ kleinSet) :=
  Certificates.certificate4128.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem card_normalizer_kleinSet :
    (Finset.univ.filter fun g : Perm (Fin 7) =>
      Perm.sign g = 1 ∧ g * x7 * g⁻¹ ∈ kleinSet ∧ g * y7 * g⁻¹ ∈ kleinSet).card = 72 :=
  Certificates.certificate4128.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[expose] def sylowP : Subgroup (Perm (Fin 7)) where
  carrier := {g | g ∈ sylowSet}
  mul_mem' := fun {a b} ha hb => sylowSet_mul a ha b hb
  one_mem' := sylowSet_one
  inv_mem' := fun {a} ha => sylowSet_inv a ha

@[expose] def kleinP : Subgroup (Perm (Fin 7)) where
  carrier := {g | g ∈ kleinSet}
  mul_mem' := fun {a b} ha hb => kleinSet_mul a ha b hb
  one_mem' := kleinSet_one
  inv_mem' := fun {a} ha => kleinSet_inv a ha

theorem mem_kleinP {g : Perm (Fin 7)} : g ∈ kleinP ↔ g ∈ kleinSet := Iff.rfl

theorem sylowP_le : sylowP ≤ alternatingGroup (Fin 7) := fun _ hg =>
  Equiv.Perm.mem_alternatingGroup.2 (sylowSet_sign _ hg)

theorem kleinP_le_sylowP : kleinP ≤ sylowP := fun _ hg => kleinSet_subset hg

theorem kleinP_le : kleinP ≤ alternatingGroup (Fin 7) := kleinP_le_sylowP.trans sylowP_le

theorem card_kleinP : Nat.card kleinP = 4 := by
  rw [card_eq_of_mem_iff kleinP kleinSet (fun _ => Iff.rfl), kleinSet_card]

theorem card_sylowP : Nat.card sylowP = 8 := by
  rw [card_eq_of_mem_iff sylowP sylowSet (fun _ => Iff.rfl), sylowSet_card]

@[expose] def sylowA : Subgroup A7 := sylowP.subgroupOf (alternatingGroup (Fin 7))

@[expose] def kleinA : Subgroup A7 := kleinP.subgroupOf (alternatingGroup (Fin 7))

theorem mem_sylowA {x : A7} : x ∈ sylowA ↔ (x : Perm (Fin 7)) ∈ sylowSet := Iff.rfl

theorem mem_kleinA {x : A7} : x ∈ kleinA ↔ (x : Perm (Fin 7)) ∈ kleinSet := Iff.rfl

theorem card_sylowA : Nat.card sylowA = 8 := by
  rw [← card_sylowP]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylowP_le).toEquiv

theorem card_kleinA : Nat.card kleinA = 4 := by
  rw [← card_kleinP]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe kleinP_le).toEquiv

def x7A : A7 := ⟨x7, sylowP_le (kleinP_le_sylowP x7_mem)⟩

def y7A : A7 := ⟨y7, sylowP_le (kleinP_le_sylowP y7_mem)⟩

def z7A : A7 := ⟨z7, sylowP_le z7_mem⟩

theorem x7A_mem : x7A ∈ kleinA := x7_mem

theorem y7A_mem : y7A ∈ kleinA := y7_mem

theorem z7A_mem : z7A ∈ sylowA := z7_mem

theorem kleinA_le_sylowA : kleinA ≤ sylowA := fun _ hx => kleinSet_subset hx

theorem normalizer_sylowA : Subgroup.normalizer (sylowA : Set A7) = sylowA := by
  apply le_antisymm _ Subgroup.le_normalizer
  intro n hn
  rw [Subgroup.mem_normalizer_iff] at hn
  have h1 := (hn x7A).1 (kleinA_le_sylowA x7A_mem)
  have h2 := (hn y7A).1 (kleinA_le_sylowA y7A_mem)
  have h3 := (hn z7A).1 z7A_mem
  rw [mem_sylowA] at h1 h2 h3 ⊢
  exact normalizer_sylowSet (n : Perm (Fin 7)) (Equiv.Perm.mem_alternatingGroup.1 n.2) h1 h2 h3

theorem normalizer_eq_of_card_eight {T : Subgroup A7} (hT : Nat.card T = 8) :
    Subgroup.normalizer (T : Set A7) = T := by
  obtain ⟨g, hg⟩ := exists_conj_of_card_sylow (P := sylowA) (Q := T)
    (by rw [card_sylowA, fac_card_A7]; norm_num) (by rw [hT, fac_card_A7]; norm_num)
  have hT' : T = conjSub g sylowA := by ext x; exact hg x
  rw [hT']
  apply le_antisymm _ Subgroup.le_normalizer
  intro n hn
  rw [normalizer_conjSub, normalizer_sylowA] at hn
  exact hn

end Explicit

section Klein

theorem eq_klein_cases {k : A7} (hk : k ∈ kleinA) :
    k = 1 ∨ k = x7A ∨ k = y7A ∨ k = x7A * y7A := by
  rw [mem_kleinA] at hk
  simp only [kleinSet, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))

theorem conj_mem_klein_of_gens {n : A7} (h1 : n * x7A * n⁻¹ ∈ kleinA)
    (h2 : n * y7A * n⁻¹ ∈ kleinA) : ∀ k ∈ kleinA, n * k * n⁻¹ ∈ kleinA := by
  intro k hk
  rcases eq_klein_cases hk with rfl | rfl | rfl | rfl
  · simp
  · exact h1
  · exact h2
  · have : n * (x7A * y7A) * n⁻¹ = (n * x7A * n⁻¹) * (n * y7A * n⁻¹) := by group
    rw [this]; exact kleinA.mul_mem h1 h2

theorem mem_normalizer_kleinA_iff (n : A7) :
    n ∈ Subgroup.normalizer (kleinA : Set A7) ↔
      ((n : Perm (Fin 7)) * x7 * (n : Perm (Fin 7))⁻¹ ∈ kleinSet ∧
        (n : Perm (Fin 7)) * y7 * (n : Perm (Fin 7))⁻¹ ∈ kleinSet) := by
  constructor
  · intro hn
    rw [Subgroup.mem_normalizer_iff] at hn
    exact ⟨(hn x7A).1 x7A_mem, (hn y7A).1 y7A_mem⟩
  · rintro ⟨h1, h2⟩
    exact mem_normalizer_of_conj_le (conj_mem_klein_of_gens h1 h2)

theorem card_normalizer_kleinA : Nat.card (Subgroup.normalizer (kleinA : Set A7)) = 72 := by
  classical
  set nset : Finset (Perm (Fin 7)) := Finset.univ.filter fun g =>
      Perm.sign g = 1 ∧ g * x7 * g⁻¹ ∈ kleinSet ∧ g * y7 * g⁻¹ ∈ kleinSet with hnset
  have himg : Subtype.val '' ((Subgroup.normalizer (kleinA : Set A7) : Subgroup A7) : Set A7) =
      (nset : Set (Perm (Fin 7))) := by
    ext g
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [Finset.mem_coe, hnset, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Equiv.Perm.mem_alternatingGroup.1 n.2,
        (mem_normalizer_kleinA_iff n).1 hn⟩
    · intro hg
      rw [Finset.mem_coe, hnset, Finset.mem_filter] at hg
      obtain ⟨-, hs, h1, h2⟩ := hg
      exact ⟨⟨g, Equiv.Perm.mem_alternatingGroup.2 hs⟩,
        (mem_normalizer_kleinA_iff _).2 ⟨h1, h2⟩, rfl⟩
  have h1 : Nat.card (Subgroup.normalizer (kleinA : Set A7)) =
      ((Subgroup.normalizer (kleinA : Set A7) : Subgroup A7) : Set A7).ncard :=
    Nat.card_coe_set_eq _
  rw [h1, ← Set.ncard_image_of_injective _ Subtype.val_injective, himg, Set.ncard_coe_finset]
  exact card_normalizer_kleinSet

@[expose] def IsKleinConj (A : Subgroup A7) : Prop := ∃ c : A7, A = conjSub c kleinA

theorem IsKleinConj.card {A : Subgroup A7} (h : IsKleinConj A) : Nat.card A = 4 := by
  obtain ⟨c, rfl⟩ := h
  rw [card_conjSub, card_kleinA]

theorem IsKleinConj.card_normalizer {A : Subgroup A7} (h : IsKleinConj A) :
    Nat.card (Subgroup.normalizer (A : Set A7)) = 72 := by
  obtain ⟨c, rfl⟩ := h
  rw [card_normalizer_conjSub, card_normalizer_kleinA]

theorem klein_conj_stable {d : A7} (h : ∀ x ∈ kleinA, d * x * d⁻¹ ∈ sylowA) :
    ∀ x, d * x * d⁻¹ ∈ kleinA ↔ x ∈ kleinA := by
  have h1 := h x7A x7A_mem
  have h2 := h y7A y7A_mem
  rw [mem_sylowA] at h1 h2
  have hs := Equiv.Perm.mem_alternatingGroup.1 d.2
  obtain ⟨k1, k2⟩ := klein_unique (d : Perm (Fin 7)) hs h1 h2
  have hn : d ∈ Subgroup.normalizer (kleinA : Set A7) :=
    (mem_normalizer_kleinA_iff d).2 ⟨k1, k2⟩
  rw [Subgroup.mem_normalizer_iff] at hn
  exact fun x => (hn x).symm

theorem IsKleinConj.eq_of_le {T A A' : Subgroup A7} (hT : Nat.card T = 8)
    (hA : IsKleinConj A) (hA' : IsKleinConj A') (h1 : A ≤ T) (h2 : A' ≤ T) : A = A' := by
  obtain ⟨g, hg⟩ := exists_conj_of_card_sylow (P := sylowA) (Q := T)
    (by rw [card_sylowA, fac_card_A7]; norm_num) (by rw [hT, fac_card_A7]; norm_num)
  have key : ∀ {B : Subgroup A7}, IsKleinConj B → B ≤ T → B = conjSub g kleinA := by
    rintro B ⟨c, rfl⟩ hB
    have hd : ∀ x ∈ kleinA, (g⁻¹ * c) * x * (g⁻¹ * c)⁻¹ ∈ sylowA := by
      intro x hx
      have hmem : c * x * c⁻¹ ∈ conjSub c kleinA := by
        rw [mem_conjSub]; simpa [mul_assoc] using hx
      have h' := (hg _).1 (hB hmem)
      have e : (g⁻¹ * c) * x * (g⁻¹ * c)⁻¹ = g⁻¹ * (c * x * c⁻¹) * g := by group
      rw [e]; exact h'
    have hstable := klein_conj_stable hd
    ext y
    rw [mem_conjSub, mem_conjSub]
    have hy := hstable (c⁻¹ * y * c)
    have e : (g⁻¹ * c) * (c⁻¹ * y * c) * (g⁻¹ * c)⁻¹ = g⁻¹ * y * g := by group
    rw [e] at hy
    exact hy.symm
  rw [key hA h1, key hA' h2]

end Klein

section Module

variable {U : Type} [CommGroup U]

theorem card_stabU (ρ : A7 →* MulAut U) (hcard : Nat.card U = 16)
    (hinj : Function.Injective ρ) {T : Subgroup A7} (hT : Nat.card T = 8) {u : U} (hu : u ≠ 1)
    (hTu : u ∈ fixU ρ T) : Nat.card (stabU ρ u) = 168 := by
  have hmul := orbit_card_mul ρ u
  have hle := ncard_orbU_le ρ hcard hu
  have hTle : T ≤ stabU ρ u := fun t ht => hTu t ht
  have h8 : 8 ∣ Nat.card (stabU ρ u) := by
    have := Subgroup.card_dvd_of_le hTle
    rwa [hT] at this
  have h5 := not_dvd_five_card_stabU ρ hcard hinj hu
  have hidx := index_stabU ρ u
  set n := (orbU ρ u).ncard with hn
  set s := Nat.card (stabU ρ u) with hs
  have hn7 : n = 1 ∨ 7 ≤ n := by
    by_cases htop : stabU ρ u = ⊤
    · left
      rw [← hidx, htop, Subgroup.index_top]
    · right
      rw [← hidx]
      exact index_ge_seven htop
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hmul; omega
    · exact h
  interval_cases n <;> omega

theorem exists_apply_eq (ρ : A7 →* MulAut U) (hcard : Nat.card U = 16)
    (hinj : Function.Injective ρ) {T : Subgroup A7} (hT : Nat.card T = 8) {u : U} (hu : u ≠ 1)
    (hTu : u ∈ fixU ρ T) {v : U} (hv : v ≠ 1) : ∃ g : A7, ρ g u = v := by
  have hfin : Finite U := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h168 := card_stabU ρ hcard hinj hT hu hTu
  have hmul := orbit_card_mul ρ u
  rw [h168] at hmul
  have h15 : (orbU ρ u).ncard = 15 := by omega
  have hall : ({v : U | v ≠ 1} : Set U).ncard = 15 := by
    have : ({v : U | v ≠ 1} : Set U) = Set.univ \ {1} := by ext; simp
    rw [this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, hcard]
  have heq : orbU ρ u = {v : U | v ≠ 1} :=
    Set.eq_of_subset_of_ncard_le (orbU_subset ρ hu) (by omega) (Set.toFinite _)
  have : v ∈ orbU ρ u := by rw [heq]; exact hv
  exact this

end Module

section Module2

variable {U : Type} [CommGroup U]

theorem fixU_eq_of_card_eight (ρ : A7 →* MulAut U) (hcard : Nat.card U = 16)
    (hinj : Function.Injective ρ) {T : Subgroup A7} (hT : Nat.card T = 8) {u₀ : U}
    (hu₀ : u₀ ≠ 1) (hTu₀ : u₀ ∈ fixU ρ T) {u : U} (hu : u ∈ fixU ρ T) (hu1 : u ≠ 1) :
    u = u₀ := by
  obtain ⟨g, hg⟩ := exists_apply_eq ρ hcard hinj hT hu₀ hTu₀ hu1
  have hHcard : Nat.card (stabU ρ u₀) = 168 := card_stabU ρ hcard hinj hT hu₀ hTu₀
  have hTH : T ≤ stabU ρ u₀ := fun t ht => hTu₀ t ht
  have hT'card : Nat.card (conjSub g⁻¹ T) = 8 := by rw [card_conjSub, hT]
  have hgi : ρ g⁻¹ u = u₀ := by
    rw [← hg, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  have hT'H : conjSub g⁻¹ T ≤ stabU ρ u₀ := by
    intro x hx
    have hx0 : (g⁻¹)⁻¹ * x * g⁻¹ ∈ T := hx
    have hx' : g * x * g⁻¹ ∈ T := by simpa using hx0
    show ρ x u₀ = u₀
    have h1 : ρ (g * x * g⁻¹) u = u := hu _ hx'
    have h2 : ρ (g * x * g⁻¹) u = ρ g (ρ x (ρ g⁻¹ u)) := by
      simp only [map_mul, MulAut.mul_apply]
    rw [h2, hgi] at h1
    have h3 : ρ g (ρ x u₀) = ρ g u₀ := by rw [h1, hg]
    exact (ρ g).injective h3
  obtain ⟨h, hhH, hh⟩ := exists_conj_in_of_card_sylow hTH hT'H hHcard hT hT'card
  have hn : g * h ∈ Subgroup.normalizer (T : Set A7) := by
    apply mem_normalizer_of_conj_le
    intro x hx
    have hy : h * x * h⁻¹ ∈ conjSub g⁻¹ T := by
      rw [hh]
      have e : h⁻¹ * (h * x * h⁻¹) * h = x := by group
      rw [e]; exact hx
    have hy0 : (g⁻¹)⁻¹ * (h * x * h⁻¹) * g⁻¹ ∈ T := hy
    have e : g * h * x * (g * h)⁻¹ = (g⁻¹)⁻¹ * (h * x * h⁻¹) * g⁻¹ := by group
    rw [e]; exact hy0
  rw [normalizer_eq_of_card_eight hT] at hn
  have h1 : ρ (g * h) u₀ = u₀ := hTu₀ _ hn
  have h2 : ρ (g * h) u₀ = u := by
    rw [map_mul, MulAut.mul_apply]
    have : ρ h u₀ = u₀ := hhH
    rw [this, hg]
  rw [← h2, h1]

theorem exists_order_seven_fixing (ρ : A7 →* MulAut U) (hcard : Nat.card U = 16)
    (hinj : Function.Injective ρ) {T : Subgroup A7} (hT : Nat.card T = 8) {u₀ : U}
    (hu₀ : u₀ ≠ 1) (hTu₀ : u₀ ∈ fixU ρ T) : ∃ x : A7, orderOf x = 7 ∧ ρ x u₀ = u₀ := by
  have hp : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h168 := card_stabU ρ hcard hinj hT hu₀ hTu₀
  have hdvd : 7 ∣ Nat.card (stabU ρ u₀) := by rw [h168]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(stabU ρ u₀)) 7 hdvd
  exact ⟨x, by rw [Subgroup.orderOf_coe]; exact hx, x.2⟩

theorem fix_of_fix_one (ρ : A7 →* MulAut U) (hcard : Nat.card U = 16)
    (hinj : Function.Injective ρ) {T : Subgroup A7} (hT : Nat.card T = 8) {u₀ : U}
    (hu₀ : u₀ ≠ 1) (hTu₀ : u₀ ∈ fixU ρ T) {x : A7} (hx : ρ x u₀ = u₀) {u : U}
    (hu : u ∈ fixU ρ T) : ρ x u = u := by
  by_cases h1 : u = 1
  · rw [h1, map_one]
  · rw [fixU_eq_of_card_eight ρ hcard hinj hT hu₀ hTu₀ hu h1]; exact hx

theorem card_fixU_le_two (ρ : A7 →* MulAut U) (hcard : Nat.card U = 16)
    (hinj : Function.Injective ρ) {T : Subgroup A7} (hT : Nat.card T = 8) :
    Nat.card (fixU ρ T) ≤ 2 := by
  have hfin : Finite U := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  by_cases hex : ∃ u₀ ∈ fixU ρ T, u₀ ≠ 1
  · obtain ⟨u₀, hu₀, hne⟩ := hex
    have hsub : ((fixU ρ T : Subgroup U) : Set U) ⊆ {1, u₀} := by
      intro u hu
      by_cases h1 : u = 1
      · simp [h1]
      · right; exact fixU_eq_of_card_eight ρ hcard hinj hT hne hu₀ hu h1
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, u₀} : Set U).ncard ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      simp
    have h3 : Nat.card (fixU ρ T) = ((fixU ρ T : Subgroup U) : Set U).ncard :=
      Nat.card_coe_set_eq _
    omega
  · push Not at hex
    have : fixU ρ T = ⊥ := by
      ext u
      rw [Subgroup.mem_bot]
      exact ⟨fun hu => hex u hu, fun h => h ▸ (fixU ρ T).one_mem⟩
    rw [this, Subgroup.card_bot]
    norm_num

theorem mem_of_centralizes_fixU (ρ : A7 →* MulAut U) (hcard : Nat.card U = 16)
    (hinj : Function.Injective ρ) {T A : Subgroup A7} (hT : Nat.card T = 8) (hA : Nat.card A = 4)
    (hAT : A ≤ T) (hfix : 4 ≤ Nat.card (fixU ρ A)) {t : A7} (ht : t ∈ T)
    (hc : ∀ u ∈ fixU ρ A, ρ t u = u) : t ∈ A := by
  have hfin : Finite U := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let C : Subgroup A7 :=
    { carrier := {t | t ∈ T ∧ ∀ u ∈ fixU ρ A, ρ t u = u}
      one_mem' := ⟨T.one_mem, fun u _ => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨T.mul_mem ha.1 hb.1, fun u hu => by
        rw [map_mul, MulAut.mul_apply, hb.2 u hu, ha.2 u hu]⟩
      inv_mem' := fun {a} ha => ⟨T.inv_mem ha.1, fun u hu => by
        calc ρ a⁻¹ u = ρ a⁻¹ (ρ a u) := by rw [ha.2 u hu]
          _ = u := by rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl⟩ }
  have hAC : A ≤ C := fun a ha => ⟨hAT ha, fun u hu => hu a ha⟩
  have hCT : C ≤ T := fun c hc => hc.1
  have hdvd1 : Nat.card A ∣ Nat.card C := Subgroup.card_dvd_of_le hAC
  have hdvd2 : Nat.card C ∣ Nat.card T := Subgroup.card_dvd_of_le hCT
  rw [hA] at hdvd1
  rw [hT] at hdvd2
  have hC4 : Nat.card C = 4 ∨ Nat.card C = 8 := by
    have h8 : Nat.card C ∈ Nat.divisors 8 := by simpa using hdvd2
    have : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [this] at h8
    simp only [Finset.mem_insert, Finset.mem_singleton] at h8
    omega
  rcases hC4 with h4 | h8
  · have hCA : A = C := Subgroup.eq_of_le_of_card_ge hAC (by rw [h4, hA])
    have htC : t ∈ C := ⟨ht, hc⟩
    rw [hCA]; exact htC
  · exfalso
    have hCTeq : C = T := Subgroup.eq_of_le_of_card_ge hCT (by rw [h8, hT])
    have hsub : fixU ρ A ≤ fixU ρ T := by
      intro u hu s hs
      have : s ∈ C := by rw [hCTeq]; exact hs
      exact this.2 u hu
    have := Subgroup.card_le_of_le hsub
    have h2 := card_fixU_le_two ρ hcard hinj hT
    omega

end Module2

theorem z7_y7_noncomm : z7 * y7 ≠ y7 * z7 :=
  Certificates.certificate4128.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem exists_noncomm_of_card_eight {P : Subgroup A7} (hP : Nat.card P = 8) :
    ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
  obtain ⟨g, hg⟩ := exists_conj_of_card_sylow (P := sylowA) (Q := P)
    (by rw [card_sylowA, fac_card_A7]; norm_num) (by rw [hP, fac_card_A7]; norm_num)
  refine ⟨g * z7A * g⁻¹, ?_, g * y7A * g⁻¹, ?_, fun h => z7_y7_noncomm ?_⟩
  · rw [hg]
    have : g⁻¹ * (g * z7A * g⁻¹) * g = z7A := by group
    rw [this]; exact z7A_mem
  · rw [hg]
    have : g⁻¹ * (g * y7A * g⁻¹) * g = y7A := by group
    rw [this]; exact kleinA_le_sylowA y7A_mem
  · have h' : z7A * y7A = y7A * z7A := by
      have e1 : g * z7A * g⁻¹ * (g * y7A * g⁻¹) = g * (z7A * y7A) * g⁻¹ := by group
      have e2 : g * y7A * g⁻¹ * (g * z7A * g⁻¹) = g * (y7A * z7A) * g⁻¹ := by group
      rw [e1, e2] at h
      exact mul_left_cancel (mul_right_cancel h)
    exact congrArg Subtype.val h'

theorem card_le_four {B : Subgroup A7} (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (h2 : ∀ a ∈ B, a ^ 2 = 1) : Nat.card B ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : IsPGroup 2 B := fun x => ⟨1, by
    apply Subtype.ext; simpa using h2 x x.2⟩
  obtain ⟨P, hBP⟩ := hB.exists_le_sylow
  have hP : Nat.card (P : Subgroup A7) = 8 := by
    rw [P.card_eq_multiplicity, fac_card_A7]; norm_num
  have hdvd : Nat.card B ∣ 8 := hP ▸ Subgroup.card_dvd_of_le hBP
  by_contra hlt
  push Not at hlt
  have h8 : Nat.card B = 8 := by
    have h' : Nat.card B ∈ Nat.divisors 8 := by simpa using hdvd
    have e : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [e] at h'
    simp only [Finset.mem_insert, Finset.mem_singleton] at h'
    omega
  have hBP' : B = P := Subgroup.eq_of_le_of_card_ge hBP (by rw [h8, hP])
  obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_of_card_eight hP
  rw [← hBP'] at ha hb
  exact hab (hc a ha b hb)

section Sq

variable {U : Type} [CommGroup U]

theorem card_fixU_le_four (ρ : A7 →* MulAut U) (hcard : Nat.card U = 16)
    (hinj : Function.Injective ρ) (hU2 : ∀ u : U, u ^ 2 = 1) {T A : Subgroup A7}
    (hT : Nat.card T = 8) (hA : Nat.card A = 4) (hAT : A ≤ T) : Nat.card (fixU ρ A) ≤ 4 := by
  have hfin : Finite U := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨t, htT, htA⟩ : ∃ t ∈ T, t ∉ A := by
    by_contra h
    push Not at h
    have hle : T ≤ A := fun x hx => h x hx
    have := Subgroup.card_le_of_le hle
    omega
  have hidx : (A.subgroupOf T).index = 2 := by
    have h1 := (A.subgroupOf T).index_mul_card
    have h2 : Nat.card (A.subgroupOf T) = 4 := by
      rw [← hA]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv
    rw [h2, hT] at h1
    omega
  have hnorm : (A.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hidx
  have hconj : ∀ a ∈ A, ∀ s ∈ T, s * a * s⁻¹ ∈ A := by
    intro a ha s hs
    have := hnorm.conj_mem ⟨a, hAT ha⟩ (Subgroup.mem_subgroupOf.2 ha) ⟨s, hs⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hjoin : A ⊔ Subgroup.zpowers t = T := by
    have hle : A ⊔ Subgroup.zpowers t ≤ T :=
      sup_le hAT ((Subgroup.zpowers_le).2 htT)
    have hd1 : 4 ∣ Nat.card ↥(A ⊔ Subgroup.zpowers t) := by
      rw [← hA]; exact Subgroup.card_dvd_of_le le_sup_left
    have hd2 : Nat.card ↥(A ⊔ Subgroup.zpowers t) ∣ 8 := by
      rw [← hT]; exact Subgroup.card_dvd_of_le hle
    have hne : Nat.card ↥(A ⊔ Subgroup.zpowers t) ≠ 4 := by
      intro h4
      have : A = A ⊔ Subgroup.zpowers t :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h4, hA])
      apply htA
      rw [this]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    have h8 : Nat.card ↥(A ⊔ Subgroup.zpowers t) = 8 := by
      have h' : Nat.card ↥(A ⊔ Subgroup.zpowers t) ∈ Nat.divisors 8 := by simpa using hd2
      have e : Nat.divisors 8 = {1, 2, 4, 8} := by decide
      rw [e] at h'
      simp only [Finset.mem_insert, Finset.mem_singleton] at h'
      omega
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h8, hT])
  have hCt : ∀ c ∈ fixU ρ A, ρ t c ∈ fixU ρ A := by
    intro c hc
    rw [mem_fixU] at hc ⊢
    intro a ha
    have h1 : t⁻¹ * a * t ∈ A := by
      have := hconj a ha t⁻¹ (T.inv_mem htT)
      simpa using this
    have e : ρ a (ρ t c) = ρ t (ρ (t⁻¹ * a * t) c) := by
      simp only [← MulAut.mul_apply, ← map_mul]
      congr 2
      group
    rw [e, hc _ h1]
  have ht2 : t ^ 2 ∈ A := by
    have h1 := Subgroup.pow_index_mem (A.subgroupOf T) (⟨t, htT⟩ : ↥T)
    rw [hidx] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  have hτ : ∀ c ∈ fixU ρ A, ρ t (ρ t c) = c := by
    intro c hc
    rw [mem_fixU] at hc
    rw [← MulAut.mul_apply, ← map_mul, ← pow_two]
    exact hc _ ht2
  have hsq := card_le_sq hU2 (ρ t) (fixU ρ A) hCt hτ
  have hsub : fixU ρ A ⊓ fixedBy (ρ t) ≤ fixU ρ T := by
    intro u hu
    have hA' : A ≤ stabU ρ u := fun a ha => (mem_fixU.1 hu.1) a ha
    have ht' : t ∈ stabU ρ u := hu.2
    have : A ⊔ Subgroup.zpowers t ≤ stabU ρ u :=
      sup_le hA' ((Subgroup.zpowers_le).2 ht')
    rw [hjoin] at this
    exact mem_fixU.2 fun g hg => this hg
  have h2 := card_fixU_le_two ρ hcard hinj hT
  have h3 : Nat.card ↥(fixU ρ A ⊓ fixedBy (ρ t)) ≤ 2 :=
    (Subgroup.card_le_of_le hsub).trans h2
  calc Nat.card (fixU ρ A) ≤ Nat.card ↥(fixU ρ A ⊓ fixedBy (ρ t)) ^ 2 := hsq
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_left h3 2
    _ = 4 := by norm_num

end Sq

end CFSG.QuasithinUnique.L246.C123
