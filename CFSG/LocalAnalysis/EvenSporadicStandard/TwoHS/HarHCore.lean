module

public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionZStarSylow

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] noncomputable def harSqCard (X : Subgroup G) (y : G) : ℕ :=
  Nat.card {x : X // (x : G) ^ 2 = y}

structure HarCoreData (t z1 : G) (S Eg T0 T0' W0 : Subgroup G) : Prop where
  t_sq : t ^ 2 = 1
  t_ne_one : t ≠ 1
  z1_ne_one : z1 ≠ 1
  z1_ne_t : z1 ≠ t
  t_mem : t ∈ T0
  z1_mem : z1 ∈ T0
  S_comm_t : ∀ s ∈ S, s * t = t * s
  T0_eq : T0 = S ⊓ Eg
  Eg_norm : ∀ s ∈ S, ∀ e ∈ Eg, s * e * s⁻¹ ∈ Eg
  z1_comm : ∀ y ∈ T0, z1 * y = y * z1
  cent_le : ∀ x : G, x * t = t * x → (∀ y ∈ T0, x * y = y * x) → x ∈ Eg
  centre : ∀ x ∈ T0, (∀ y ∈ T0, x * y = y * x) → x = 1 ∨ x = t ∨ x = z1 ∨ x = t * z1
  derived : ⁅S, S⁆ = T0'
  W0_eq : W0 = Subgroup.closure ((T0' : Set G) ∪ {y | y ∈ T0 ∧ y ^ 2 = 1})
  card_T0_t : harSqCard T0 t = 80
  card_T0_z2 : harSqCard T0 (t * z1) = 48
  card_T0'_t : harSqCard T0' t = 16
  card_T0'_z1 : harSqCard T0' z1 = 32
  card_T0'_z2 : harSqCard T0' (t * z1) = 16
  card_W0_t : harSqCard W0 t = 48
  card_W0_z2 : harSqCard W0 (t * z1) = 16

theorem harSqCard_conj (X : Subgroup G) {n : G} (hn : n ∈ normalizer (X : Set G)) (y : G) :
    harSqCard X (n * y * n⁻¹) = harSqCard X y := by
  unfold harSqCard
  refine (Nat.card_congr (Equiv.subtypeEquiv (X.normalizerMonoidHom ⟨n, hn⟩).toEquiv
    fun x => ?_)).symm
  change (x : G) ^ 2 = y ↔ ((X.normalizerMonoidHom ⟨n, hn⟩ x : X) : G) ^ 2 = n * y * n⁻¹
  rw [normalizerMonoidHom_apply_apply_coe, conj_pow]
  exact ⟨fun h => by rw [h], fun h => mul_left_cancel (mul_right_cancel h)⟩

theorem harCore_mem_normalizer_commutator {S : Subgroup G} {n : G}
    (hn : n ∈ normalizer (S : Set G)) : n ∈ normalizer ((⁅S, S⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hn ⊢
  rw [map_commutator, hn]

theorem harCore_NS {t z1 : G} {S Eg T0 T0' W0 : Subgroup G}
    (D : HarCoreData t z1 S Eg T0 T0' W0) {n : G} (hn : n ∈ normalizer (S : Set G))
    (hnt : n * t * n⁻¹ ≠ t) :
    (∃ s ∈ S, s ∉ Eg) ∧ ∃ v ∈ S, v ^ 2 = 1 ∧ v ∉ Eg := by
  have hT0S : T0 ≤ S := by rw [D.T0_eq]; exact inf_le_left
  have hmem : ∀ x, x ∈ S → x ∈ Eg → x ∈ T0 := fun x hS hE => by
    rw [D.T0_eq]; exact mem_inf.mpr ⟨hS, hE⟩
  have hnorm : ∀ m ∈ normalizer (S : Set G), m ∈ normalizer (T0' : Set G) := fun m hm => by
    rw [← D.derived]; exact harCore_mem_normalizer_commutator hm
  have htS : t ∈ S := hT0S D.t_mem
  have hwS : n * t * n⁻¹ ∈ S := (mem_normalizer_iff.mp hn t).mp htS
  have hwcomm : ∀ s ∈ S, n * t * n⁻¹ * s = s * (n * t * n⁻¹) := by
    intro s hs
    have hc := D.S_comm_t _ ((mem_normalizer_iff''.mp hn s).mp hs)
    calc n * t * n⁻¹ * s = n * (t * (n⁻¹ * s * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * s * n) * t) * n⁻¹ := by rw [hc]
      _ = s * (n * t * n⁻¹) := by group
  have hwE : n * t * n⁻¹ ∈ Eg := D.cent_le _ (hwcomm t htS) fun y hy => hwcomm y (hT0S hy)
  have hw_ne_one : n * t * n⁻¹ ≠ 1 := by
    intro h
    apply D.t_ne_one
    calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  have hw_ne_z1 : n * t * n⁻¹ ≠ z1 := by
    intro h
    have h1 := harSqCard_conj T0' (hnorm n hn) t
    rw [h, D.card_T0'_z1, D.card_T0'_t] at h1
    omega
  have hw : n * t * n⁻¹ = t * z1 := by
    rcases D.centre _ (hmem _ hwS hwE) fun y hy => hwcomm y (hT0S hy) with h | h | h | h
    · exact absurd h hw_ne_one
    · exact absurd h hnt
    · exact absurd h hw_ne_z1
    · exact h
  refine ⟨?_, ?_⟩
  · by_contra hcon
    have hT0 : T0 = S := le_antisymm hT0S fun s hs =>
      hmem s hs (by_contra fun hs' => hcon ⟨s, hs, hs'⟩)
    have hnT0 : n ∈ normalizer (T0 : Set G) := by
      rw [hT0]
      exact hn
    have h1 := harSqCard_conj T0 hnT0 t
    rw [hw, D.card_T0_z2, D.card_T0_t] at h1
    omega
  · by_contra hcon
    have hset : {y : G | y ∈ T0 ∧ y ^ 2 = 1} = {y | y ∈ S ∧ y ^ 2 = 1} := by
      ext y
      refine ⟨fun ⟨hy, hy2⟩ => ⟨hT0S hy, hy2⟩, fun ⟨hy, hy2⟩ => ⟨hmem y hy ?_, hy2⟩⟩
      exact by_contra fun hy' => hcon ⟨y, hy, hy2, hy'⟩
    have hM : normalizer (S : Set G) ≤
        normalizer ((T0' : Set G) ∪ {y | y ∈ S ∧ y ^ 2 = 1}) := by
      rw [le_set_normalizer_iff]
      intro m hm g hg
      rcases hg with hg | ⟨hgS, hg2⟩
      · exact Or.inl ((mem_normalizer_iff.mp (hnorm m hm) g).mp hg)
      · refine Or.inr ⟨(mem_normalizer_iff.mp hm g).mp hgS, ?_⟩
        rw [conj_pow, hg2]
        group
    have hnW0 : n ∈ normalizer (W0 : Set G) := by
      have hW0 : W0 = closure ((T0' : Set G) ∪ {y | y ∈ S ∧ y ^ 2 = 1}) := by
        rw [D.W0_eq, hset]
      rw [hW0]
      exact normalizer_le_normalizer_closure _ (hM hn)
    have h1 := harSqCard_conj W0 hnW0 t
    rw [hw, D.card_W0_z2, D.card_W0_t] at h1
    omega

theorem harCore_S {t z1 : G} {S Eg T0 T0' W0 : Subgroup G}
    (D : HarCoreData t z1 S Eg T0 T0' W0) [Finite G] (P : Sylow 2 G)
    (hP : (P : Subgroup G) = S)
    (hN : ∀ n ∈ normalizer (S : Set G), n * t * n⁻¹ = t)
    (hinv : ∀ u ∈ Eg, u ^ 2 = 1 → u ≠ 1 → u ≠ t →
      ∃ e ∈ Eg, e * u * e⁻¹ = z1 ∨ e * u * e⁻¹ = t * z1) :
    ∀ g : G, g⁻¹ * t * g ∈ Eg → g⁻¹ * t * g = t := by
  have hT0S : T0 ≤ S := by rw [D.T0_eq]; exact inf_le_left
  have hT0E : T0 ≤ Eg := by rw [D.T0_eq]; exact inf_le_right
  have hmem : ∀ x, x ∈ S → x ∈ Eg → x ∈ T0 := fun x hS hE => by
    rw [D.T0_eq]; exact mem_inf.mpr ⟨hS, hE⟩
  have hnorm : ∀ m ∈ normalizer (S : Set G), m ∈ normalizer (T0' : Set G) := fun m hm => by
    rw [← D.derived]; exact harCore_mem_normalizer_commutator hm
  have hz1 : ∀ x ∈ S, x * z1 * x⁻¹ = z1 := by
    intro x hx
    have hxT0 : x * z1 * x⁻¹ ∈ T0 :=
      hmem _ (S.mul_mem (S.mul_mem hx (hT0S D.z1_mem)) (S.inv_mem hx))
        (D.Eg_norm x hx z1 (hT0E D.z1_mem))
    have hcomm : ∀ y ∈ T0, x * z1 * x⁻¹ * y = y * (x * z1 * x⁻¹) := by
      intro y hy
      have hyE := D.Eg_norm x⁻¹ (S.inv_mem hx) y (hT0E hy)
      rw [inv_inv] at hyE
      have hy' : x⁻¹ * y * x ∈ T0 :=
        hmem _ (S.mul_mem (S.mul_mem (S.inv_mem hx) (hT0S hy)) hx) hyE
      calc x * z1 * x⁻¹ * y = x * (z1 * (x⁻¹ * y * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * y * x) * z1) * x⁻¹ := by rw [D.z1_comm _ hy']
        _ = y * (x * z1 * x⁻¹) := by group
    rcases D.centre _ hxT0 hcomm with h | h | h | h
    · exfalso
      apply D.z1_ne_one
      calc z1 = x⁻¹ * (x * z1 * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    · exfalso
      apply D.z1_ne_t
      calc z1 = x⁻¹ * (x * z1 * x⁻¹) * x := by group
        _ = x⁻¹ * t * x := by rw [h]
        _ = t := by rw [D.S_comm_t x⁻¹ (S.inv_mem hx), inv_mul_cancel_right]
    · exact h
    · exfalso
      have h1 := harSqCard_conj T0' (hnorm x (le_normalizer hx)) z1
      rw [h, D.card_T0'_z2, D.card_T0'_z1] at h1
      omega
  have htz1 : ∀ x ∈ S, x * (t * z1) * x⁻¹ = t * z1 := by
    intro x hx
    calc x * (t * z1) * x⁻¹ = (x * t * x⁻¹) * (x * z1 * x⁻¹) := by group
      _ = t * z1 := by rw [hz1 x hx, D.S_comm_t x hx, mul_inv_cancel_right]
  intro g hg
  by_contra hne
  have hu2 : (g⁻¹ * t * g) ^ 2 = 1 := by
    have h := conj_pow (a := g⁻¹) (b := t) (i := 2)
    rw [inv_inv] at h
    rw [h, D.t_sq]
    group
  have hu1 : g⁻¹ * t * g ≠ 1 := by
    intro h
    apply D.t_ne_one
    calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨e, -, he⟩ := hinv _ hg hu2 hu1 hne
  have hv : e * (g⁻¹ * t * g) * e⁻¹ = (e * g⁻¹) * t * (e * g⁻¹)⁻¹ := by group
  have htS : (P : Subgroup G) ≤ centralizer ({t} : Set G) := fun x hx => by
    rw [hP] at hx
    exact mem_centralizer_singleton_iff.mpr (D.S_comm_t x hx)
  have hvS : (P : Subgroup G) ≤ centralizer ({(e * g⁻¹) * t * (e * g⁻¹)⁻¹} : Set G) := by
    intro x hx
    rw [hP] at hx
    rw [mem_centralizer_singleton_iff, ← hv]
    rcases he with he | he
    · rw [he]
      calc x * z1 = (x * z1 * x⁻¹) * x := by group
        _ = z1 * x := by rw [hz1 x hx]
    · rw [he]
      calc x * (t * z1) = (x * (t * z1) * x⁻¹) * x := by group
        _ = t * z1 * x := by rw [htz1 x hx]
  obtain ⟨n, hn, hnt⟩ :=
    CFSG.ComponentClassification.StandardRecognition.exists_mem_normalizer_conj_eq_of_le_centralizer
      P htS hvS
  rw [hP] at hn
  have hvt : e * (g⁻¹ * t * g) * e⁻¹ = t := by rw [hv, ← hnt, hN n hn]
  rcases he with he | he
  · exact D.z1_ne_t (he.symm.trans hvt)
  · apply D.z1_ne_one
    have h2 : t * z1 = t * 1 := by rw [mul_one]; exact he.symm.trans hvt
    exact mul_left_cancel h2

end CFSG.EvenSporadicStandard.TwoHS
