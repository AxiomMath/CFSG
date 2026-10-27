module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Orbit
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup

variable {G : Type} [Group G]

@[expose] def Hloc (L U : Subgroup G) : Subgroup G := normalizer (U : Set G) ⊓ L

@[expose] def hOrbit (L U : Subgroup G) (a : G) : Set G := {u | ∃ h ∈ Hloc L U, h * a * h⁻¹ = u}

structure LocalData (L U T0 : Subgroup G) : Prop where
  U_le_T0 : U ≤ T0
  T0_le_L : T0 ≤ L
  T0_pGroup : IsPGroup 2 T0
  T0_index_odd : ¬ 2 ∣ T0.relIndex L
  U_sq : ∀ u ∈ U, u * u = 1
  U_comm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u
  card_U : Nat.card U = 2 ^ 11
  unique : ∀ A : Subgroup G, A ≤ T0 → (∀ a ∈ A, a * a = 1) →
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → 2 ^ 11 ≤ Nat.card A → A = U
  selfCentralizing : ∀ l ∈ L, (∀ u ∈ U, l * u = u * l) → l ∈ U
  card_H : Nat.card (Hloc L U) = 501397585920
  orbits : ∃ a b : G, a ∈ U ∧ b ∈ U ∧ a ≠ 1 ∧ b ≠ 1 ∧ b ∉ hOrbit L U a ∧
    (∀ u ∈ U, u ≠ 1 → u ∈ hOrbit L U a ∨ u ∈ hOrbit L U b) ∧
    (hOrbit L U a).ncard = 1771 ∧ (hOrbit L U b).ncard = 276
  irred : ∀ D : Subgroup G, D ≤ U → (∀ h ∈ Hloc L U, ∀ d ∈ D, h * d * h⁻¹ ∈ D) →
    D = ⊥ ∨ D = U

@[expose] def Vsub (U : Subgroup G) (z : G) : Subgroup G := U ⊔ zpowers z

@[expose] def Nsub (U : Subgroup G) (z : G) : Subgroup G := normalizer (Vsub U z : Set G)

section Basic

variable {L U T0 : Subgroup G} {z : G}

theorem mem_Hloc {h : G} : h ∈ Hloc L U ↔ h ∈ L ∧ ∀ u : G, u ∈ U ↔ h * u * h⁻¹ ∈ U := by
  unfold Hloc
  rw [mem_inf, mem_normalizer_iff]
  exact and_comm

theorem mem_Hloc_of {h : G} (hL : h ∈ L) (h1 : ∀ u ∈ U, h * u * h⁻¹ ∈ U)
    (h2 : ∀ u ∈ U, h⁻¹ * u * h ∈ U) : h ∈ Hloc L U := by
  refine mem_Hloc.2 ⟨hL, fun u => ⟨h1 u, fun hu => ?_⟩⟩
  have := h2 _ hu
  simpa [mul_assoc] using this

theorem Hloc_conj_mem {h : G} (hh : h ∈ Hloc L U) {u : G} (hu : u ∈ U) : h * u * h⁻¹ ∈ U :=
  ((mem_Hloc.1 hh).2 u).1 hu

theorem Hloc_le_L : Hloc L U ≤ L := fun _ h => (mem_inf.1 h).2

variable (hS : Setting L z) (hU : U ≤ L)
include hS hU

theorem z_comm_U {u : G} (hu : u ∈ U) : z * u = u * z := hS.z_comm u (hU hu)

theorem mem_Vsub_iff {x : G} : x ∈ Vsub U z ↔ ∃ u ∈ U, x = u ∨ x = z * u := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hS.z_mul_self
  constructor
  · intro hx
    let P : Subgroup G :=
      { carrier := {x | ∃ u ∈ U, x = u ∨ x = z * u}
        mul_mem' := by
          intro x y hx hy
          obtain ⟨u, hu, hx⟩ := hx
          obtain ⟨u', hu', hy⟩ := hy
          refine ⟨u * u', mul_mem hu hu', ?_⟩
          rcases hx with hx | hx <;> rcases hy with hy | hy <;> subst hx hy
          · exact Or.inl rfl
          · exact Or.inr (by rw [← mul_assoc, ← z_comm_U hS hU hu, mul_assoc])
          · exact Or.inr (by rw [mul_assoc])
          · refine Or.inl ?_
            calc z * u * (z * u') = z * (u * z) * u' := by simp only [mul_assoc]
              _ = z * (z * u) * u' := by rw [z_comm_U hS hU hu]
              _ = (z * z) * u * u' := by simp only [mul_assoc]
              _ = u * u' := by rw [hS.z_mul_self, one_mul]
        one_mem' := ⟨1, one_mem _, Or.inl rfl⟩
        inv_mem' := by
          intro x hx
          obtain ⟨u, hu, hx⟩ := hx
          rcases hx with hx | hx
          · exact ⟨u⁻¹, inv_mem hu, Or.inl (by rw [hx])⟩
          · refine ⟨u⁻¹, inv_mem hu, Or.inr ?_⟩
            rw [hx, mul_inv_rev, hzi]
            exact (z_comm_U hS hU (inv_mem hu)).symm }
    have hle : Vsub U z ≤ P := sup_le (fun u hu => ⟨u, hu, Or.inl rfl⟩) (by
      rw [zpowers_le]
      exact ⟨1, one_mem _, Or.inr (by rw [mul_one])⟩)
    exact hle hx
  · rintro ⟨u, hu, hx⟩
    rcases hx with hx | hx <;> subst hx
    · exact mem_sup_left hu
    · exact mul_mem (mem_sup_right (mem_zpowers z)) (mem_sup_left hu)

omit hS hU in
theorem U_le_V : U ≤ Vsub U z := le_sup_left

omit hS hU in
theorem z_mem_V : z ∈ Vsub U z := mem_sup_right (mem_zpowers z)

theorem Vsub_inf_L {x : G} (hxV : x ∈ Vsub U z) (hxL : x ∈ L) : x ∈ U := by
  obtain ⟨u, hu, hx⟩ := (mem_Vsub_iff hS hU).1 hxV
  rcases hx with hx | hx <;> subst hx
  · exact hu
  · exfalso
    apply hS.z_not_mem
    have : z = z * u * u⁻¹ := by group
    rw [this]
    exact L.mul_mem hxL (L.inv_mem (hU hu))

theorem z_not_mem_U : z ∉ U := fun h => hS.z_not_mem (hU h)

theorem card_Vsub [Finite G] : Nat.card (Vsub U z) = 2 * Nat.card U := by
  have hzU : z ∉ U := z_not_mem_U hS hU
  have hinl : ∀ u : U, (u : G) ∈ Vsub U z := fun u => mem_sup_left u.2
  have hinr : ∀ u : U, z * (u : G) ∈ Vsub U z := fun u =>
    mul_mem (mem_sup_right (mem_zpowers z)) (mem_sup_left u.2)
  let e : (U ⊕ U) ≃ Vsub U z :=
    Equiv.ofBijective
      (fun s => match s with
        | Sum.inl u => ⟨u, hinl u⟩
        | Sum.inr u => ⟨z * u, hinr u⟩)
      ⟨by
        rintro (u | u) (u' | u') h
        · have := congrArg Subtype.val h
          exact congrArg Sum.inl (Subtype.ext this)
        · exfalso
          have h' : (u : G) = z * u' := congrArg Subtype.val h
          apply hzU
          have : z = (u : G) * (u' : G)⁻¹ := by rw [h']; group
          rw [this]
          exact mul_mem u.2 (inv_mem u'.2)
        · exfalso
          have h' : z * (u : G) = u' := congrArg Subtype.val h
          apply hzU
          have : z = (u' : G) * (u : G)⁻¹ := by rw [← h']; group
          rw [this]
          exact mul_mem u'.2 (inv_mem u.2)
        · have h' : z * (u : G) = z * u' := congrArg Subtype.val h
          exact congrArg Sum.inr (Subtype.ext (mul_left_cancel h')),
       by
        rintro ⟨x, hx⟩
        obtain ⟨u, hu, hxu⟩ := (mem_Vsub_iff hS hU).1 hx
        rcases hxu with hxu | hxu
        · exact ⟨Sum.inl ⟨u, hu⟩, Subtype.ext hxu.symm⟩
        · exact ⟨Sum.inr ⟨u, hu⟩, Subtype.ext hxu.symm⟩⟩
  rw [← Nat.card_congr e, Nat.card_sum, two_mul]

omit hS hU in
theorem conj_mem_V_of_N {n : G} (hn : n ∈ Nsub U z) {x : G} (hx : x ∈ Vsub U z) :
    n * x * n⁻¹ ∈ Vsub U z := (mem_normalizer_iff.1 hn x).1 hx

theorem conj_mem_V_of_Hloc {h : G} (hh : h ∈ Hloc L U) {x : G} (hx : x ∈ Vsub U z) :
    h * x * h⁻¹ ∈ Vsub U z := by
  obtain ⟨u, hu, hxu⟩ := (mem_Vsub_iff hS hU).1 hx
  have hzh : z * h = h * z := hS.z_comm h (Hloc_le_L hh)
  rcases hxu with hxu | hxu
  · rw [hxu]; exact mem_sup_left (Hloc_conj_mem hh hu)
  · rw [hxu]
    have : h * (z * u) * h⁻¹ = z * (h * u * h⁻¹) := by
      calc h * (z * u) * h⁻¹ = (h * z) * u * h⁻¹ := by group
        _ = z * h * u * h⁻¹ := by rw [← hzh]
        _ = z * (h * u * h⁻¹) := by group
    rw [this]
    exact mul_mem (mem_sup_right (mem_zpowers z)) (mem_sup_left (Hloc_conj_mem hh hu))

theorem Hloc_le_N : Hloc L U ≤ Nsub U z := by
  intro h hh
  rw [Nsub, mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_V_of_Hloc hS hU hh, fun hx => ?_⟩
  have := conj_mem_V_of_Hloc hS hU (inv_mem hh) hx
  have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
  rwa [e] at this

omit hS hU in
theorem V_le_N : Vsub U z ≤ Nsub U z := Subgroup.le_normalizer

theorem exists_Hloc_of_mem_N_comm {n : G} (hn : n ∈ Nsub U z) (hc : z * n = n * z) :
    ∃ l ∈ Hloc L U, n = l ∨ n = l * z := by
  obtain ⟨l, hl, hnl⟩ := hS.centralizer_z n hc
  have hlN : l ∈ Nsub U z := by
    rcases hnl with hnl | hnl
    · rw [← hnl]; exact hn
    · have : l = n * z⁻¹ := by rw [hnl]; group
      rw [this]
      exact mul_mem hn (inv_mem (V_le_N (z_mem_V)))
  have hconj : ∀ k ∈ Nsub U z, k ∈ L → ∀ u ∈ U, k * u * k⁻¹ ∈ U := by
    intro k hk hkL u hu
    exact Vsub_inf_L hS hU (conj_mem_V_of_N hk (U_le_V hu))
      (mul_mem (mul_mem hkL (hU hu)) (inv_mem hkL))
  refine ⟨l, mem_Hloc_of hl (hconj l hlN hl) (fun u hu => ?_), hnl⟩
  have := hconj l⁻¹ (inv_mem hlN) (inv_mem hl) u hu
  rwa [inv_inv] at this

@[expose] def Dset (U : Subgroup G) (z : G) : Set G :=
  {u | u ∈ U ∧ ∃ n ∈ Nsub U z, n * z * n⁻¹ = z * u}

theorem conj_eq_mul_of_N {n : G} (hn : n ∈ Nsub U z) : ∃ u ∈ U, n * z * n⁻¹ = z * u := by
  obtain ⟨u, hu, hxu⟩ := (mem_Vsub_iff hS hU).1 (conj_mem_V_of_N hn z_mem_V)
  rcases hxu with hxu | hxu
  · exfalso
    exact hS.conj_not_mem_of_mul_self (g := n) (by rw [hxu]; exact hU hu)
  · exact ⟨u, hu, hxu⟩

theorem Dset_card_eq [Finite G] :
    {m | ∃ k ∈ Nsub U z, m = k * z * k⁻¹}.ncard = (Dset U z).ncard := by
  have : {m | ∃ k ∈ Nsub U z, m = k * z * k⁻¹} = (fun u => z * u) '' Dset U z := by
    ext m
    constructor
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨u, hu, hku⟩ := conj_eq_mul_of_N hS hU hk
      exact ⟨u, ⟨hu, k, hk, hku⟩, hku.symm⟩
    · rintro ⟨u, ⟨hu, k, hk, hku⟩, rfl⟩
      exact ⟨k, hk, hku.symm⟩
  rw [this]
  exact Set.ncard_image_of_injective _ (mul_right_injective z)

theorem orbit_dichotomy [Finite G] (hD : LocalData L U T0) :
    (∀ n ∈ Nsub U z, n * z = z * n) ∨ (∀ u ∈ U, ∃ n ∈ Nsub U z, n * z * n⁻¹ = z * u) := by
  classical
  obtain ⟨a, b, haU, hbU, ha1, hb1, hba, hcov, hca, hcb⟩ := hD.orbits
  have h1 : (1 : G) ∈ Dset U z := ⟨one_mem U, 1, one_mem _, by simp⟩
  have hinv : ∀ h ∈ Hloc L U, ∀ u ∈ Dset U z, h * u * h⁻¹ ∈ Dset U z := by
    rintro h hh u ⟨huU, n, hn, hnu⟩
    refine ⟨Hloc_conj_mem hh huU, h * n, mul_mem (Hloc_le_N hS hU hh) hn, ?_⟩
    have hzh : z * h = h * z := hS.z_comm h (Hloc_le_L hh)
    calc h * n * z * (h * n)⁻¹ = h * (n * z * n⁻¹) * h⁻¹ := by group
      _ = h * (z * u) * h⁻¹ := by rw [hnu]
      _ = (h * z) * u * h⁻¹ := by group
      _ = z * h * u * h⁻¹ := by rw [← hzh]
      _ = z * (h * u * h⁻¹) := by group
  have hsub : ∀ c ∈ Dset U z, hOrbit L U c ⊆ Dset U z := by
    rintro c hc u ⟨h, hh, rfl⟩
    exact hinv h hh c hc
  have hback : ∀ c u : G, u ∈ hOrbit L U c → u ∈ Dset U z → c ∈ Dset U z := by
    rintro c u ⟨h, hh, rfl⟩ hu
    have := hinv h⁻¹ (inv_mem hh) _ hu
    have e : h⁻¹ * (h * c * h⁻¹) * h⁻¹⁻¹ = c := by group
    rwa [e] at this
  have key : ∀ p : ℕ, [Fact p.Prime] → p ≠ 2 → p ∣ (Dset U z).ncard →
      ¬ p ∣ 501397585920 → (∀ d < 12, ¬ 2 ^ d ≡ 2 ^ 12 [MOD p]) → False := by
    intro p hp hp2 hpd hpH hmod
    have hdvdN : p ∣ Nat.card (Nsub U z) :=
      hpd.trans (Dset_card_eq hS hU ▸ ncard_conj_class_dvd (Nsub U z) z)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvdN
    have hxG : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe]; exact hx
    have hxN : (x : G) ∈ Nsub U z := x.2
    have hnc : z * (x : G) ≠ x * z := by
      intro hc
      obtain ⟨l, hl, hxl⟩ := exists_Hloc_of_mem_N_comm hS hU hxN hc
      have hlcomm : Commute l z := (hS.z_comm l (Hloc_le_L hl)).symm
      rcases hxl with hxl | hxl
      · apply hpH
        rw [← hD.card_H]
        have := orderOf_dvd_natCard (⟨l, hl⟩ : Hloc L U)
        rw [Subgroup.orderOf_mk, ← hxl, hxG] at this
        exact this
      ·
        have hodd : Odd p := hp.1.odd_of_ne_two hp2
        have hxp : (x : G) ^ p = 1 := by rw [← hxG]; exact pow_orderOf_eq_one _
        obtain ⟨k, hk⟩ := hodd
        have hzp : z ^ p = z := by
          rw [hk, pow_succ, pow_mul, sq, hS.z_mul_self, one_pow, one_mul]
        have : (l * z) ^ p = l ^ p * z := by rw [hlcomm.mul_pow, hzp]
        rw [hxl, this] at hxp
        apply hS.z_not_mem
        have hz : z = (l ^ p)⁻¹ := eq_inv_of_mul_eq_one_right hxp
        rw [hz]
        exact inv_mem (pow_mem (Hloc_le_L hl) p)
    obtain ⟨d, hd, hdmod⟩ := exists_pow_modEq_of_prime_orderOf (V := Vsub U z) (m := 12) hxG
      (by rw [card_Vsub hS hU, hD.card_U]; norm_num) (fun v hv => conj_mem_V_of_N hxN hv)
      ⟨z, z_mem_V, fun h => hnc h.symm⟩
    exact hmod d hd hdmod
  have hone_notin : ∀ c : G, c ≠ 1 → (1 : G) ∉ hOrbit L U c := by
    rintro c hc ⟨h, hh, h1'⟩
    apply hc
    have : c = h⁻¹ * (h * c * h⁻¹) * h := by group
    rw [this, h1']; group
  have hcard_union : ∀ c : G, c ≠ 1 → ((({1} : Set G) ∪ hOrbit L U c)).ncard =
      1 + (hOrbit L U c).ncard := by
    intro c hc
    rw [Set.ncard_union_eq (Set.disjoint_singleton_left.2 (hone_notin c hc)) (Set.toFinite _)
      (Set.toFinite _), Set.ncard_singleton]
  by_cases hA : a ∈ Dset U z <;> by_cases hB : b ∈ Dset U z
  · right
    intro u hu
    by_cases hu1 : u = 1
    · exact ⟨1, one_mem _, by simp [hu1]⟩
    · rcases hcov u hu hu1 with huA | huB
      · exact (hsub a hA huA).2
      · exact (hsub b hB huB).2
  · exfalso
    have hEq : Dset U z = {1} ∪ hOrbit L U a := by
      ext u
      constructor
      · intro hu
        by_cases hu1 : u = 1
        · exact Or.inl hu1
        · rcases hcov u hu.1 hu1 with huA | huB
          · exact Or.inr huA
          · exact absurd (hback b u huB hu) hB
      · rintro (rfl | hu)
        · exact h1
        · exact hsub a hA hu
    have : Fact (Nat.Prime 443) := ⟨by norm_num⟩
    refine key 443 (by norm_num) ?_ (by norm_num) no_pow_modEq_443
    · have h1772 : (Dset U z).ncard = 4 * 443 := by rw [hEq, hcard_union a ha1, hca]
      rw [h1772]; exact Dvd.intro_left _ rfl
  · exfalso
    have hEq : Dset U z = {1} ∪ hOrbit L U b := by
      ext u
      constructor
      · intro hu
        by_cases hu1 : u = 1
        · exact Or.inl hu1
        · rcases hcov u hu.1 hu1 with huA | huB
          · exact absurd (hback a u huA hu) hA
          · exact Or.inr huB
      · rintro (rfl | hu)
        · exact h1
        · exact hsub b hB hu
    have : Fact (Nat.Prime 277) := ⟨by norm_num⟩
    refine key 277 (by norm_num) ?_ (by norm_num) no_pow_modEq_277
    · have h277 : (Dset U z).ncard = 277 := by rw [hEq, hcard_union b hb1, hcb]
      rw [h277]
  · left
    intro n hn
    obtain ⟨u, hu, hnu⟩ := conj_eq_mul_of_N hS hU hn
    have hu1 : u = 1 := by
      by_contra hu1
      rcases hcov u hu hu1 with huA | huB
      · exact hA (hback a u huA ⟨hu, n, hn, hnu⟩)
      · exact hB (hback b u huB ⟨hu, n, hn, hnu⟩)
    rw [hu1, mul_one] at hnu
    calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [hnu]

end Basic

end CFSG.EvenSporadicStandard.J4Std
