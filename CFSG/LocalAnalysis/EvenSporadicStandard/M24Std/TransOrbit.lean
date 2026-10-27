module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Orbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Setting

public section

namespace CFSG.EvenSporadicStandard.M24Std.Trans

open Subgroup

variable {G : Type} [Group G] {L A : Subgroup G} {z : G}

theorem NL_normalizes {n : G} (hn : n ∈ egNL L A) : n ∈ normalizer (A : Set G) :=
  (mem_inf.1 hn).1

theorem NL_mem {n : G} (hn : n ∈ egNL L A) : n ∈ L :=
  (mem_inf.1 hn).2

theorem mem_V_of_mem {a : G} (ha : a ∈ A) : a ∈ egV A z := mem_sup_left ha

theorem z_mem_V : z ∈ egV A z := mem_sup_right (mem_zpowers z)

theorem mem_M_of_mem_V {v : G} (hv : v ∈ egV A z) : v ∈ egM A z := le_normalizer hv

variable [Finite G]

section Local

variable (hs : LocalSetting G L z)
include hs

theorem mul_self_z : z * z = 1 := by
  rw [← pow_two, ← hs.order_z, pow_orderOf_eq_one]

theorem z_ne_one : z ≠ 1 := by
  intro h
  have := hs.order_z
  rw [h, orderOf_one] at this
  exact absurd this (by decide)

theorem z_not_mem : z ∉ L := by
  intro hz
  have : z ∈ L ⊓ zpowers z := ⟨hz, mem_zpowers z⟩
  rw [disjoint_iff.1 hs.disjoint] at this
  exact z_ne_one hs (mem_bot.1 this)

theorem comm_z {l : G} (hl : l ∈ L) : l * z = z * l :=
  mem_centralizer_iff.1 (hs.z_central (mem_zpowers z)) l hl

theorem zpowers_le_centralizer (hAL : A ≤ L) : zpowers z ≤ centralizer (A : Set G) :=
  hs.z_central.trans (centralizer_le (SetLike.coe_subset_coe.2 hAL))

theorem mem_V (hAL : A ≤ L) {v : G} (hv : v ∈ egV A z) : ∃ a ∈ A, v = a ∨ v = a * z := by
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (zpowers_le_centralizer hs hAL) hv
  rcases eq_one_or_eq_of_mul_self (mul_self_z hs) hb with rfl | rfl
  · exact ⟨a, ha, Or.inl (mul_one a)⟩
  · exact ⟨a, ha, Or.inr rfl⟩

theorem mul_self_of_mem_V (hAL : A ≤ L) (hAe : EgElemAb A) {v : G} (hv : v ∈ egV A z) :
    v * v = 1 := by
  obtain ⟨a, ha, h | h⟩ := mem_V hs hAL hv
  · rw [h]
    exact hAe.2 a ha
  · rw [h]
    calc a * z * (a * z) = a * (z * a) * z := by group
      _ = a * (a * z) * z := by rw [comm_z hs (hAL ha)]
      _ = (a * a) * (z * z) := by group
      _ = 1 := by rw [hAe.2 a ha, mul_self_z hs, mul_one]

theorem card_V (hAL : A ≤ L) (hA : Nat.card A = 64) : Nat.card (egV A z) = 2 ^ 7 := by
  have e := mulEquivProdSup (zpowers_le_centralizer hs hAL) (hs.disjoint.mono_left hAL)
  rw [show egV A z = A ⊔ zpowers z from rfl, ← Nat.card_congr e.toEquiv, Nat.card_prod,
    Nat.card_zpowers, hs.order_z, hA]
  norm_num

theorem conj_eq (hAL : A ≤ L) {m : G} (hm : m ∈ egM A z) : ∃ a ∈ A, m * z * m⁻¹ = z * a := by
  have h1 : m * z * m⁻¹ ∈ egV A z := (mem_normalizer_iff.1 hm z).1 z_mem_V
  obtain ⟨a, ha, h | h⟩ := mem_V hs hAL h1
  · exact absurd (by rw [h]; exact hAL ha) (hs.conj_not_mem m)
  · exact ⟨a, ha, by rw [h, comm_z hs (hAL ha)]⟩

theorem conj_mem_V_of_mem_NL (hAL : A ≤ L) {n v : G} (hn : n ∈ egNL L A) (hv : v ∈ egV A z) :
    n * v * n⁻¹ ∈ egV A z := by
  have hnA : ∀ a ∈ A, n * a * n⁻¹ ∈ A := fun a ha =>
    (mem_normalizer_iff.1 (NL_normalizes hn) a).1 ha
  obtain ⟨a, ha, h | h⟩ := mem_V hs hAL hv
  · rw [h]
    exact mem_V_of_mem (hnA a ha)
  · rw [h]
    have : n * (a * z) * n⁻¹ = (n * a * n⁻¹) * z := by
      calc n * (a * z) * n⁻¹ = n * a * (z * n⁻¹) := by group
        _ = n * a * (n⁻¹ * z) := by rw [comm_z hs (L.inv_mem (NL_mem hn))]
        _ = (n * a * n⁻¹) * z := by group
    rw [this]
    exact mul_mem (mem_V_of_mem (hnA a ha)) z_mem_V

theorem mem_M_of_mem_NL (hAL : A ≤ L) {n : G} (hn : n ∈ egNL L A) : n ∈ egM A z := by
  refine mem_normalizer_iff.2 fun v => ⟨conj_mem_V_of_mem_NL hs hAL hn, fun h => ?_⟩
  have := conj_mem_V_of_mem_NL hs hAL (inv_mem hn) h
  rwa [show n⁻¹ * (n * v * n⁻¹) * n⁻¹⁻¹ = v by group] at this

theorem mem_NL_of_mem_M (hAL : A ≤ L) {d : G} (hd : d ∈ egM A z) (hdL : d ∈ L) :
    d ∈ egNL L A := by
  have key : ∀ d ∈ egM A z, d ∈ L → ∀ a ∈ A, d * a * d⁻¹ ∈ A := by
    intro d hd hdL a ha
    have h1 : d * a * d⁻¹ ∈ egV A z := (mem_normalizer_iff.1 hd a).1 (mem_V_of_mem ha)
    obtain ⟨b, hb, h | h⟩ := mem_V hs hAL h1
    · rw [h]
      exact hb
    · exfalso
      apply z_not_mem hs
      have hz : z = b⁻¹ * (d * a * d⁻¹) := by rw [h]; group
      rw [hz]
      exact L.mul_mem (L.inv_mem (hAL hb)) (L.mul_mem (L.mul_mem hdL (hAL ha)) (L.inv_mem hdL))
  refine mem_inf.2 ⟨mem_normalizer_iff.2 fun a => ⟨key d hd hdL a, fun h => ?_⟩, hdL⟩
  have := key d⁻¹ (inv_mem hd) (L.inv_mem hdL) _ h
  rwa [show d⁻¹ * (d * a * d⁻¹) * d⁻¹⁻¹ = a by group] at this

theorem mem_V_of_comm (hAL : A ≤ L) (hcent : ∀ l ∈ L, (∀ a ∈ A, l * a = a * l) → l ∈ A) {g : G}
    (hgz : g * z = z * g) (hgA : ∀ a ∈ A, g * a = a * g) : g ∈ egV A z := by
  have hg : g ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hgz
  rw [hs.centralizer_eq] at hg
  obtain ⟨l, hl, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hs.z_central hg
  have hlA : l ∈ A := by
    refine hcent l hl fun a ha => ?_
    rcases eq_one_or_eq_of_mul_self (mul_self_z hs) hb with hb1 | hbz
    · rw [hb1] at hgA
      simpa using hgA a ha
    · rw [hbz] at hgA
      have h1 := hgA a ha
      have h2 : a * z = z * a := comm_z hs (hAL ha)
      have : l * a * z = a * l * z := by
        calc l * a * z = l * (a * z) := by group
          _ = l * (z * a) := by rw [h2]
          _ = l * z * a := by group
          _ = a * (l * z) := h1
          _ = a * l * z := by group
      exact mul_right_cancel this
  exact mul_mem (mem_V_of_mem hlA) (mem_sup_right hb)

theorem not_dvd_card_M (hAL : A ≤ L) (hF : SextetFacts L A) {p : ℕ} [Fact p.Prime] (hp2 : 2 < p)
    (hmod : ∀ d < 7, ¬ 2 ^ d ≡ 2 ^ 7 [MOD p]) : ¬ p ∣ Nat.card (egM A z) := by
  intro hdvd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  rw [← Subgroup.orderOf_coe] at hg
  have hn : ∀ v ∈ egV A z, (g : G) * v * (g : G)⁻¹ ∈ egV A z := fun v hv =>
    (mem_normalizer_iff.1 g.2 v).1 hv
  have hc : ∀ v ∈ egV A z, (g : G) * v = v * g := by
    by_contra hne
    push Not at hne
    obtain ⟨d, hd, hmd⟩ :=
      J4Std.exists_pow_modEq_of_prime_orderOf hg (card_V hs hAL hF.card_A) hn hne
    exact hmod d hd hmd
  have hgV := mem_V_of_comm hs hAL hF.cent (hc z z_mem_V) fun a ha => hc a (mem_V_of_mem ha)
  have h2 : orderOf (g : G) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact mul_self_of_mem_V hs hAL hF.elem hgV)
  rw [hg] at h2
  exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)

end Local

omit [Finite G] in
theorem ne_one_of_mem_egOrb {a x : G} (ha : a ≠ 1) (hx : x ∈ egOrb L A a) : x ≠ 1 := by
  obtain ⟨n, -, rfl⟩ := hx
  intro h
  apply ha
  have : a = n⁻¹ * (n * a * n⁻¹) * n := by group
  rw [this, h]
  group

theorem ncard_eq_of_orbit (T : Set G) {b : G} (hb : b ≠ 1)
    (hT : ∀ x, x ∈ T ↔ x = 1 ∨ x ∈ egOrb L A b) :
    T.ncard = Nat.card (egOrb L A b) + 1 := by
  have hT' : T = insert 1 (egOrb L A b) := by
    ext x
    rw [hT, Set.mem_insert_iff]
  rw [hT', Set.ncard_insert_of_notMem (fun h => ne_one_of_mem_egOrb hb h rfl) (Set.toFinite _),
    Nat.card_coe_set_eq]

theorem invariant_cases (hF : SextetFacts L A) (T : Set G) (hTA : T ⊆ A) (h1 : (1 : G) ∈ T)
    (hinv : ∀ n ∈ egNL L A, ∀ a ∈ T, n * a * n⁻¹ ∈ T) :
    T = {1} ∨ T.ncard = 46 ∨ T.ncard = 19 ∨ (A : Set G) ⊆ T := by
  obtain ⟨a₁, ha₁, a₂, ha₂, h₁, h₂, hcov, -, hc₁, hc₂⟩ := hF.orbits
  have horb : ∀ a b, a ∈ egOrb L A b → a ∈ T → b ∈ T := by
    rintro a b ⟨n, hn, rfl⟩ ha
    have := hinv n⁻¹ (inv_mem hn) _ ha
    rwa [show n⁻¹ * (n * b * n⁻¹) * n⁻¹⁻¹ = b by group] at this
  have hsub : ∀ b ∈ T, ∀ x ∈ egOrb L A b, x ∈ T := by
    rintro b hb _ ⟨n, hn, rfl⟩
    exact hinv n hn b hb
  by_cases h₁T : a₁ ∈ T <;> by_cases h₂T : a₂ ∈ T
  · refine Or.inr (Or.inr (Or.inr fun x hx => ?_))
    by_cases hx1 : x = 1
    · rw [hx1]
      exact h1
    · rcases hcov x hx hx1 with h | h
      · exact hsub a₁ h₁T x h
      · exact hsub a₂ h₂T x h
  · refine Or.inr (Or.inl ?_)
    rw [ncard_eq_of_orbit T h₁ fun x => ⟨fun hx => ?_, fun hx => ?_⟩, hc₁]
    · by_cases hx1 : x = 1
      · exact Or.inl hx1
      · rcases hcov x (hTA hx) hx1 with h | h
        · exact Or.inr h
        · exact absurd (horb x a₂ h hx) h₂T
    · rcases hx with rfl | hx
      · exact h1
      · exact hsub a₁ h₁T x hx
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [ncard_eq_of_orbit T h₂ fun x => ⟨fun hx => ?_, fun hx => ?_⟩, hc₂]
    · by_cases hx1 : x = 1
      · exact Or.inl hx1
      · rcases hcov x (hTA hx) hx1 with h | h
        · exact absurd (horb x a₁ h hx) h₁T
        · exact Or.inr h
    · rcases hx with rfl | hx
      · exact h1
      · exact hsub a₂ h₂T x hx
  · refine Or.inl (Set.eq_singleton_iff_unique_mem.2 ⟨h1, fun x hx => ?_⟩)
    by_contra hx1
    rcases hcov x (hTA hx) hx1 with h | h
    · exact h₁T (horb x a₁ h hx)
    · exact h₂T (horb x a₂ h hx)

theorem exists_conj_eq (hs : LocalSetting G L z) (hAL : A ≤ L) (hF : SextetFacts L A)
    (hcase : ¬ egM A z ≤ centralizer ({z} : Set G)) :
    ∀ a ∈ A, ∃ m ∈ egM A z, m * z * m⁻¹ = z * a := by
  set T : Set G := {a | a ∈ A ∧ ∃ m ∈ egM A z, m * z * m⁻¹ = z * a} with hTdef
  have hTA : T ⊆ A := fun a ha => ha.1
  have h1 : (1 : G) ∈ T := ⟨one_mem A, 1, one_mem _, by group⟩
  have hinv : ∀ n ∈ egNL L A, ∀ a ∈ T, n * a * n⁻¹ ∈ T := by
    rintro n hn a ⟨ha, m, hm, hmz⟩
    refine ⟨(mem_normalizer_iff.1 (NL_normalizes hn) a).1 ha, n * m,
      mul_mem (mem_M_of_mem_NL hs hAL hn) hm, ?_⟩
    have hnz : n * z = z * n := comm_z hs (NL_mem hn)
    calc n * m * z * (n * m)⁻¹ = n * (m * z * m⁻¹) * n⁻¹ := by group
      _ = n * z * a * n⁻¹ := by rw [hmz]; group
      _ = z * (n * a * n⁻¹) := by rw [hnz]; group
  set C : Set G := {x | ∃ k ∈ egM A z, x = k * z * k⁻¹} with hCdef
  have hC : C = (fun a => z * a) '' T := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨a, ha, hka⟩ := conj_eq hs hAL hk
      exact ⟨a, ⟨ha, k, hk, hka⟩, hka.symm⟩
    · rintro ⟨a, ⟨-, m, hm, hma⟩, rfl⟩
      exact ⟨m, hm, hma.symm⟩
  have hCcard : C.ncard = T.ncard := by
    rw [hC]
    exact Set.ncard_image_of_injective _ (mul_right_injective z)
  have hdvd : C.ncard ∣ Nat.card (egM A z) := J4Std.ncard_conj_class_dvd _ z
  rw [hCcard] at hdvd
  rcases invariant_cases hF T hTA h1 hinv with hT | hT | hT | hT
  · exfalso
    apply hcase
    intro m hm
    obtain ⟨a, ha, hma⟩ := conj_eq hs hAL hm
    have : a ∈ T := ⟨ha, m, hm, hma⟩
    rw [hT, Set.mem_singleton_iff] at this
    rw [this, mul_one] at hma
    rw [mem_centralizer_singleton_iff]
    calc m * z = m * z * m⁻¹ * m := by group
      _ = z * m := by rw [hma]
  · exfalso
    have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    refine not_dvd_card_M hs hAL hF (p := 23) (by norm_num) (by decide) ?_
    rw [hT] at hdvd
    exact dvd_trans ⟨2, rfl⟩ hdvd
  · exfalso
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    refine not_dvd_card_M hs hAL hF (p := 19) (by norm_num) (by decide) ?_
    rw [hT] at hdvd
    exact hdvd
  · intro a ha
    obtain ⟨-, m, hm, hma⟩ := hT ha
    exact ⟨m, hm, hma⟩

end CFSG.EvenSporadicStandard.M24Std.Trans
