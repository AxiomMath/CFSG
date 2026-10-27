module

public import CFSG.Goldschmidt.StatementsH
import CFSG.Goldschmidt.Steps.Fusion
import CFSG.Goldschmidt.Steps.ZStarLemma
import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open scoped commutatorElement

theorem N31_exists : S_N31_exists := by
  classical
  intro G _ _ S A hAS hA1 hcl
  have hex : ∃ n : ℕ, ∃ U : Subgroup G, U ≤ A ∧ U ≠ ⊥ ∧
      fusionStronglyClosed (U : Set G) (S : Subgroup G) ∧ Nat.card U = n :=
    ⟨_, A, le_rfl, hA1, hcl, rfl⟩
  obtain ⟨U, hUA, hU1, hUcl, hUn⟩ := Nat.find_spec hex
  refine ⟨U, hUA, hUA.trans hAS, hU1, hUcl, fun V hVU hV1 hVcl => ?_⟩
  refine Subgroup.eq_of_le_of_card_ge hVU ?_
  rw [hUn]
  exact Nat.find_min' hex ⟨V, hVU.trans hUA, hV1, hVcl, rfl⟩

namespace PropHSetup

variable {G : Type*} [Group G]

theorem isMulCommutative_of_le {A U : Subgroup G} (hA : IsMulCommutative A) (hUA : U ≤ A) :
    IsMulCommutative U := by
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have h : (a : G) * b = b * a := congrArg Subtype.val (hA.is_comm.comm ⟨a, hUA a.2⟩ ⟨b, hUA b.2⟩)
  exact h

theorem center_eq_bot [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) :
    Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    have hb : b ∈ Subgroup.center G := by
      rw [h]
      exact Subgroup.mem_top b
    exact absurd (Subgroup.mem_center_iff.1 hb a) hab

theorem commutator_eq_top [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) :
    commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · obtain ⟨a, b, hab⟩ := hnab
    have hc : ⁅a, b⁆ ∈ commutator G := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact absurd hc hab
  · exact h

theorem exists_orderOf_eq_two [Finite G] {U : Subgroup G} (hUp : IsPGroup 2 U) (hU1 : U ≠ ⊥) :
    ∃ u ∈ U, orderOf u = 2 := by
  obtain ⟨n, hn⟩ := hUp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hU1 (Subgroup.card_eq_one.1 (by simpa using hn))
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := U) 2
    (by rw [hn]; exact dvd_pow_self 2 hn0)
  exact ⟨u, u.2, by rw [Subgroup.orderOf_coe, hu]⟩

end PropHSetup

open PropHSetup in
theorem N31 : S_N31 := by
  intro G _ _ _ hnab S A U hAS hAab hcl hUA hU
  obtain ⟨hUS, hU1, hUcl, hUmin⟩ := hU
  have hUab : IsMulCommutative U := isMulCommutative_of_le hAab hUA
  have hUp : IsPGroup 2 U := (S.isPGroup').to_le hUS
  have hsq : ∀ x ∈ U, x ^ 2 = 1 := by
    obtain ⟨V, hV⟩ : ∃ V : Subgroup G, ∀ x, x ∈ V ↔ x ∈ U ∧ x ^ 2 = 1 := by
      refine ⟨{ carrier := {x | x ∈ U ∧ x ^ 2 = 1}
                mul_mem' := ?_
                one_mem' := ⟨U.one_mem, one_pow 2⟩
                inv_mem' := ?_ }, fun x => Iff.rfl⟩
      · rintro x y ⟨hx, hx2⟩ ⟨hy, hy2⟩
        have hxy : Commute x y := congrArg Subtype.val (hUab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
        exact ⟨U.mul_mem hx hy, by rw [hxy.mul_pow, hx2, hy2, one_mul]⟩
      · rintro x ⟨hx, hx2⟩
        exact ⟨U.inv_mem hx, by rw [inv_pow, hx2, inv_one]⟩
    have hVset : (V : Set G) = {x | x ∈ U ∧ x ^ 2 = 1} := Set.ext hV
    have hVcl : fusionStronglyClosed (V : Set G) (S : Subgroup G) := by
      rw [hVset]
      exact stronglyClosed_sq_eq_one hUcl
    have hV1 : V ≠ ⊥ := by
      obtain ⟨u, hu, huo⟩ := exists_orderOf_eq_two hUp hU1
      have hu2 : u ^ 2 = 1 := huo ▸ pow_orderOf_eq_one u
      have hu1 : u ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at huo
        exact absurd huo (by norm_num)
      intro hVbot
      have huV : u ∈ V := (hV u).2 ⟨hu, hu2⟩
      rw [hVbot, Subgroup.mem_bot] at huV
      exact hu1 huV
    have hVU : V = U := hUmin V (fun x hx => ((hV x).1 hx).1) hV1 hVcl
    intro x hx
    exact ((hV x).1 (hVU ▸ hx)).2
  have hel : IsElemAbelian 2 U := ⟨hUab, hsq⟩
  have hNA : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (U : Set G) :=
    N3a G S U A hUS hUcl ((S.isPGroup').to_le hAS) hUA
  have hctl : ∀ x g : G, x ∈ Subgroup.normalizer (U : Set G) →
      g⁻¹ * x * g ∈ Subgroup.normalizer (U : Set G) → (∃ k : ℕ, x ^ (2 ^ k) = 1) →
      ∃ m ∈ Subgroup.normalizer (U : Set G), m⁻¹ * x * m = g⁻¹ * x * g :=
    N5a G S A _ hAS hAab hcl hNA
  refine ⟨hel, ?_, hNA, hctl, fun H hH => N5c G S A _ hAS hAab hcl (commutator_eq_top hnab) hNA
    H hH, ?_⟩
  ·
    by_contra h4
    obtain ⟨n, hn⟩ := hUp.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hU1 (Subgroup.card_eq_one.1 (by simpa using hn))
    have hn1 : n = 1 := by
      by_contra hn1
      have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hU2 : Nat.card U = 2 := by rw [hn, hn1, pow_one]
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hU1
    have heq : ∀ y : U, y ≠ 1 → y = u := fun y hy =>
      ((Nat.card_eq_two_iff' (1 : U)).1 hU2).unique hy hu1
    have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
    have hu2 : (u : G) * u = 1 := by rw [← sq]; exact hsq u u.2
    have hwc : ∀ g : G, g⁻¹ * (u : G) * g ∈ (S : Subgroup G) → g⁻¹ * (u : G) * g = u := by
      intro g hg
      have hmem : g⁻¹ * (u : G) * g ∈ U := hUcl u u.2 g hg
      have hne : (⟨_, hmem⟩ : U) ≠ 1 := by
        intro h
        apply hu1'
        have h' : g⁻¹ * (u : G) * g = 1 := congrArg Subtype.val h
        calc (u : G) = g * (g⁻¹ * u * g) * g⁻¹ := by group
          _ = 1 := by rw [h']; group
      exact congrArg Subtype.val (heq _ hne)
    let _ : Fintype G := Fintype.ofFinite G
    obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar G u hu1' hu2
      (conj_eq_of_commute_of_weakClosure S hu2 hwc)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN0 | hNtop
    · have hz : (u : G) ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h := hN g
        rw [hN0, Subgroup.mem_bot] at h
        calc g * (u : G) = (g * u * g⁻¹ * (u : G)⁻¹) * u * g := by group
          _ = u * g := by rw [h, one_mul]
      rw [center_eq_bot hnab, Subgroup.mem_bot] at hz
      exact hu1' hz
    · rw [hNtop, Subgroup.card_top] at hNodd
      have huo : orderOf (u : G) = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1'
      have h2 : 2 ∣ Nat.card G := huo ▸ orderOf_dvd_natCard (u : G)
      exact (Nat.not_even_iff_odd.2 hNodd) (even_iff_two_dvd.2 h2)
  ·
    intro V hVU hNV
    by_cases hV1 : V = ⊥
    · exact Or.inl hV1
    · refine Or.inr (hUmin V hVU hV1 fun v hv g hg => ?_)
      have hgU : g⁻¹ * v * g ∈ U := hUcl v (hVU hv) g hg
      obtain ⟨m, hm, hmv⟩ := hctl v g (Subgroup.le_normalizer (hVU hv))
        (Subgroup.le_normalizer hgU) ⟨1, by rw [pow_one]; exact hsq v (hVU hv)⟩
      rw [← hmv]
      have hm' : m⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ (hNV hm)
      have := (Subgroup.mem_normalizer_iff.1 hm' v).1 hv
      simpa using this

end CFSG.Goldschmidt
