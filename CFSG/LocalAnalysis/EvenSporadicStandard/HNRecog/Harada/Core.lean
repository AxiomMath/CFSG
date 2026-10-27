module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarHCore

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.TwoHS

variable {G : Type} [Group G] {t z : G} {S Eg T T' W0 : Subgroup G}

theorem HarCoreData.T_le_S (D : HarCoreData t z S Eg T T' W0) : T ≤ S := by
  rw [D.T0_eq]; exact inf_le_left

theorem HarCoreData.T_le_Eg (D : HarCoreData t z S Eg T T' W0) : T ≤ Eg := by
  rw [D.T0_eq]; exact inf_le_right

theorem HarCoreData.mem_T (D : HarCoreData t z S Eg T T' W0) {x : G} (hS : x ∈ S) (hE : x ∈ Eg) :
    x ∈ T := by
  rw [D.T0_eq]; exact mem_inf.mpr ⟨hS, hE⟩

theorem HarCoreData.normalizer_T' (D : HarCoreData t z S Eg T T' W0) {n : G}
    (hn : n ∈ normalizer (S : Set G)) : n ∈ normalizer (T' : Set G) := by
  rw [← D.derived]; exact harCore_mem_normalizer_commutator hn

theorem HarCoreData.z_central (D : HarCoreData t z S Eg T T' W0) {x : G} (hx : x ∈ S) :
    x * z * x⁻¹ = z := by
  have hT0S : T ≤ S := HarCoreData.T_le_S D
  have hT0E : T ≤ Eg := HarCoreData.T_le_Eg D
  have hmem : ∀ y, y ∈ S → y ∈ Eg → y ∈ T := fun y hS hE => HarCoreData.mem_T D hS hE
  have hnorm : ∀ m ∈ normalizer (S : Set G), m ∈ normalizer (T' : Set G) :=
    fun m hm => HarCoreData.normalizer_T' D hm
  have hxT0 : x * z * x⁻¹ ∈ T :=
    hmem _ (S.mul_mem (S.mul_mem hx (hT0S D.z1_mem)) (S.inv_mem hx))
      (D.Eg_norm x hx z (hT0E D.z1_mem))
  have hcomm : ∀ y ∈ T, x * z * x⁻¹ * y = y * (x * z * x⁻¹) := by
    intro y hy
    have hyE := D.Eg_norm x⁻¹ (S.inv_mem hx) y (hT0E hy)
    rw [inv_inv] at hyE
    have hy' : x⁻¹ * y * x ∈ T :=
      hmem _ (S.mul_mem (S.mul_mem (S.inv_mem hx) (hT0S hy)) hx) hyE
    calc x * z * x⁻¹ * y = x * (z * (x⁻¹ * y * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * y * x) * z) * x⁻¹ := by rw [D.z1_comm _ hy']
      _ = y * (x * z * x⁻¹) := by group
  rcases D.centre _ hxT0 hcomm with h | h | h | h
  · exfalso
    apply D.z1_ne_one
    calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  · exfalso
    apply D.z1_ne_t
    calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
      _ = x⁻¹ * t * x := by rw [h]
      _ = t := by rw [D.S_comm_t x⁻¹ (S.inv_mem hx), inv_mul_cancel_right]
  · exact h
  · exfalso
    have h1 := harSqCard_conj T' (hnorm x (le_normalizer hx)) z
    rw [h, D.card_T0'_z2, D.card_T0'_z1] at h1
    omega

theorem HarCoreData.conj_mem_V (D : HarCoreData t z S Eg T T' W0) {n : G}
    (hn : n ∈ normalizer (S : Set G)) {y : G} (hyS : y ∈ S) (hyc : ∀ s ∈ S, s * y = y * s) :
    n * y * n⁻¹ = 1 ∨ n * y * n⁻¹ = t ∨ n * y * n⁻¹ = z ∨ n * y * n⁻¹ = t * z := by
  have hT0S : T ≤ S := HarCoreData.T_le_S D
  have hwS : n * y * n⁻¹ ∈ S := (mem_normalizer_iff.mp hn y).mp hyS
  have hwcomm : ∀ s ∈ S, n * y * n⁻¹ * s = s * (n * y * n⁻¹) := by
    intro s hs
    have hc := hyc _ ((mem_normalizer_iff''.mp hn s).mp hs)
    calc n * y * n⁻¹ * s = n * (y * (n⁻¹ * s * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * s * n) * y) * n⁻¹ := by rw [hc]
      _ = s * (n * y * n⁻¹) := by group
  have hwE : n * y * n⁻¹ ∈ Eg :=
    D.cent_le _ (hwcomm t (hT0S D.t_mem)) fun z hz => hwcomm z (hT0S hz)
  exact D.centre _ (HarCoreData.mem_T D hwS hwE) fun z hz => hwcomm z (hT0S hz)

theorem HarCoreData.conj_z_eq (D : HarCoreData t z S Eg T T' W0) {n : G}
    (hn : n ∈ normalizer (S : Set G)) : n * z * n⁻¹ = z := by
  have hzS : z ∈ S := HarCoreData.T_le_S D D.z1_mem
  have hzc : ∀ s ∈ S, s * z = z * s := by
    intro s hs
    calc s * z = (s * z * s⁻¹) * s := by group
      _ = z * s := by rw [HarCoreData.z_central D hs]
  have hnT' : n ∈ normalizer (T' : Set G) := HarCoreData.normalizer_T' D hn
  rcases HarCoreData.conj_mem_V D hn hzS hzc with h | h | h | h
  · exfalso
    apply D.z1_ne_one
    calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  · exfalso
    have h1 := harSqCard_conj T' hnT' z
    rw [h, D.card_T0'_t, D.card_T0'_z1] at h1
    omega
  · exact h
  · exfalso
    have h1 := harSqCard_conj T' hnT' z
    rw [h, D.card_T0'_z2, D.card_T0'_z1] at h1
    omega

theorem HarCoreData.conj_t_eq (D : HarCoreData t z S Eg T T' W0) {n : G}
    (hn : n ∈ normalizer (S : Set G)) (hnt : n * t * n⁻¹ ≠ t) : n * t * n⁻¹ = t * z := by
  have htS : t ∈ S := HarCoreData.T_le_S D D.t_mem
  have htc : ∀ s ∈ S, s * t = t * s := fun s hs => D.S_comm_t s hs
  have hnT' : n ∈ normalizer (T' : Set G) := HarCoreData.normalizer_T' D hn
  rcases HarCoreData.conj_mem_V D hn htS htc with h | h | h | h
  · exfalso
    apply D.t_ne_one
    calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  · exact absurd h hnt
  · exfalso
    have h1 := harSqCard_conj T' hnT' t
    rw [h, D.card_T0'_z1, D.card_T0'_t] at h1
    omega
  · exact h

theorem HarCoreData.exists_invol_conj_not_mem [Finite G]
    (D : HarCoreData t z S Eg T T' W0) {u : G} (hu : u ∈ normalizer (S : Set G))
    (hut : u * t * u⁻¹ = t * z) : ∃ i ∈ T, i ^ 2 = 1 ∧ u * i * u⁻¹ ∉ Eg := by
  by_contra hcon
  have hcon' : ∀ i ∈ T, i ^ 2 = 1 → u * i * u⁻¹ ∈ Eg := by
    intro i hi hi2
    by_contra hmem
    exact hcon ⟨i, hi, hi2, hmem⟩
  have huT' : u ∈ normalizer (T' : Set G) := HarCoreData.normalizer_T' D hu
  have hmap : W0.map (MulAut.conj u) = W0 := by
    have hW0 : W0 = closure ((T' : Set G) ∪ {y | y ∈ T ∧ y ^ 2 = 1}) := D.W0_eq
    rw [hW0]
    apply Subgroup.eq_of_le_of_card_ge
    · rw [MonoidHom.map_closure, closure_le]
      rintro _ ⟨a, ha, rfl⟩
      change u * a * u⁻¹ ∈ Subgroup.closure ((T' : Set G) ∪ {y | y ∈ T ∧ y ^ 2 = 1})
      rcases ha with ha | ha
      · exact subset_closure (Or.inl ((mem_normalizer_iff.mp huT' a).mp ha))
      · obtain ⟨haT, ha2⟩ := ha
        refine subset_closure (Or.inr ⟨HarCoreData.mem_T D ((mem_normalizer_iff.mp hu a).mp (HarCoreData.T_le_S D haT))
          (hcon' a haT ha2), ?_⟩)
        rw [conj_pow (a := u) (b := a) (i := 2), ha2]
        group
    · rw [Subgroup.card_map_of_injective (MulAut.conj u).injective]
  have huW0 : u ∈ normalizer (W0 : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    exact hmap
  have h1 := harSqCard_conj W0 huW0 t
  rw [hut, D.card_W0_z2, D.card_W0_t] at h1
  omega

theorem HarCoreData.normalizer_fixes_t [Finite G] (D : HarCoreData t z S Eg T T' W0)
    (hz : z ^ 2 = 1) (hidx : ¬ 2 ∣ S.index) {n : G}
    (hn : n ∈ normalizer (S : Set G)) : n * t * n⁻¹ = t := by
  by_contra hne
  have hnt : n * t * n⁻¹ = t * z := HarCoreData.conj_t_eq D hn hne
  have hzn : n * z * n⁻¹ = z := HarCoreData.conj_z_eq D hn
  have hn2 : n ^ 2 * t * (n ^ 2)⁻¹ = t := by
    calc n ^ 2 * t * (n ^ 2)⁻¹
        = n * (n * t * n⁻¹) * n⁻¹ := by rw [pow_two, mul_inv_rev]; group
      _ = n * (t * z) * n⁻¹ := by rw [hnt]
      _ = (n * t * n⁻¹) * (n * z * n⁻¹) := by group
      _ = (t * z) * z := by rw [hnt, hzn]
      _ = t := by rw [mul_assoc, ← pow_two, hz, mul_one]
  have h2k : ∀ k : ℕ, n ^ (2 * k) * t * (n ^ (2 * k))⁻¹ = t := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hp : n ^ (2 * (k + 1)) = n ^ (2 * k) * n ^ 2 := by
        rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
      rw [hp]
      calc n ^ (2 * k) * n ^ 2 * t * (n ^ (2 * k) * n ^ 2)⁻¹
          = n ^ (2 * k) * (n ^ 2 * t * (n ^ 2)⁻¹) * (n ^ (2 * k))⁻¹ := by group
        _ = n ^ (2 * k) * t * (n ^ (2 * k))⁻¹ := by rw [hn2]
        _ = t := ih
  have h2k1 : ∀ k : ℕ, n ^ (2 * k + 1) * t * (n ^ (2 * k + 1))⁻¹ = t * z := by
    intro k
    induction k with
    | zero => simpa using hnt
    | succ k ih =>
      have hp : n ^ (2 * (k + 1) + 1) = n ^ (2 * k + 1) * n ^ 2 := by
        rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, pow_add]
      rw [hp]
      calc n ^ (2 * k + 1) * n ^ 2 * t * (n ^ (2 * k + 1) * n ^ 2)⁻¹
          = n ^ (2 * k + 1) * (n ^ 2 * t * (n ^ 2)⁻¹) * (n ^ (2 * k + 1))⁻¹ := by group
        _ = n ^ (2 * k + 1) * t * (n ^ (2 * k + 1))⁻¹ := by rw [hn2]
        _ = t * z := ih
  let N : Subgroup G := normalizer (S : Set G)
  let m : ℕ := S.relIndex N
  have hSN : S ≤ N := Subgroup.le_normalizer
  have hrel : m * N.index = S.index := Subgroup.relIndex_mul_index hSN
  have hodd : ¬ 2 ∣ m := by
    intro h2
    exact hidx (hrel ▸ dvd_mul_of_dvd_left h2 N.index)
  have hm_odd : Odd m := by
    rcases Nat.even_or_odd m with he | ho
    · exact absurd (even_iff_two_dvd.mp he) hodd
    · exact ho
  obtain ⟨k, hk⟩ := hm_odd
  haveI : (S.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hm_mem : n ^ m ∈ S := by
    have h := Subgroup.pow_index_mem (S.subgroupOf N) (⟨n, hn⟩ : N)
    rw [Subgroup.mem_subgroupOf] at h
    simpa [m, Subgroup.relIndex, Subgroup.coe_pow] using h
  have hfix : n ^ m * t * (n ^ m)⁻¹ = t := by
    rw [D.S_comm_t (n ^ m) hm_mem]
    group
  have hoddm : n ^ m * t * (n ^ m)⁻¹ = t * z := by
    rw [hk]
    exact h2k1 k
  have hzt : t * z = t := hoddm ▸ hfix
  exact D.z1_ne_one (mul_left_cancel (show t * z = t * 1 from by rw [hzt, mul_one]))

theorem harCore_S' (D : HarCoreData t z S Eg T T' W0) [Finite G] (P : Sylow 2 G)
    (hP : (P : Subgroup G) = S)
    (hN : ∀ n ∈ normalizer (S : Set G), n * t * n⁻¹ = t)
    (hinv : ∀ u ∈ Eg, u ^ 2 = 1 → u ≠ 1 → u ≠ t →
      ∃ e : G, e * u * e⁻¹ = z ∨ e * u * e⁻¹ = t * z) :
    ∀ g : G, g⁻¹ * t * g ∈ Eg → g⁻¹ * t * g = t := by
  have hz1 : ∀ x ∈ S, x * z * x⁻¹ = z := fun x hx => HarCoreData.z_central D hx
  have htz1 : ∀ x ∈ S, x * (t * z) * x⁻¹ = t * z := by
    intro x hx
    calc x * (t * z) * x⁻¹ = (x * t * x⁻¹) * (x * z * x⁻¹) := by group
      _ = t * z := by rw [hz1 x hx, D.S_comm_t x hx, mul_inv_cancel_right]
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
  obtain ⟨e, he⟩ := hinv _ hg hu2 hu1 hne
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
      calc x * z = (x * z * x⁻¹) * x := by group
        _ = z * x := by rw [hz1 x hx]
    · rw [he]
      calc x * (t * z) = (x * (t * z) * x⁻¹) * x := by group
        _ = t * z * x := by rw [htz1 x hx]
  obtain ⟨n, hn, hnt⟩ :=
    CFSG.ComponentClassification.StandardRecognition.exists_mem_normalizer_conj_eq_of_le_centralizer
      P htS hvS
  rw [hP] at hn
  have hvt : e * (g⁻¹ * t * g) * e⁻¹ = t := by rw [hv, ← hnt, hN n hn]
  rcases he with he | he
  · exact D.z1_ne_t (he.symm.trans hvt)
  · apply D.z1_ne_one
    have h2 : t * z = t * 1 := by rw [mul_one]; exact he.symm.trans hvt
    exact mul_left_cancel h2

end CFSG.EvenSporadicStandard.HNRecog.Harada
