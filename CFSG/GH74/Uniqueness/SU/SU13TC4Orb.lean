module

public import CFSG.GH74.Uniqueness.SU.SU13TC3Free

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] [Finite G]

theorem card_modEq_card_inf_centralizer_pgroup {p : ℕ} [Fact p.Prime] {D V : Subgroup G}
    (hD : IsPGroup p D) (hDV : D ≤ normalizer (V : Set G)) :
    Nat.card V ≡ Nat.card (V ⊓ centralizer (D : Set G) : Subgroup G) [MOD p] := by
  classical
  let _ : MulDistribMulAction D V :=
    { smul := fun t k => ⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hDV t.2) k).mp k.2⟩
      one_smul := fun k => Subtype.ext (by change (1 : G) * k * 1⁻¹ = k; group)
      mul_smul := fun s t k => Subtype.ext (by
        change (s * t : G) * k * (s * t : G)⁻¹ = s * (t * k * (t : G)⁻¹) * (s : G)⁻¹
        group)
      smul_mul := fun t k l => Subtype.ext (by
        change (t : G) * (k * l) * (t : G)⁻¹ = (t * k * (t : G)⁻¹) * (t * l * (t : G)⁻¹)
        group)
      smul_one := fun t => Subtype.ext (by change (t : G) * 1 * (t : G)⁻¹ = 1; group) }
  have key := hD.card_modEq_card_fixedPoints V
  have hfix : ∀ a : MulAction.fixedPoints D V, ∀ g : D, (g : G) * (a.1 : G) * (g : G)⁻¹ = a.1 :=
    fun a g => congrArg Subtype.val (a.2 g)
  have h1 : ∀ a : MulAction.fixedPoints D V, (a.1 : G) ∈ V ⊓ centralizer (D : Set G) := by
    intro a
    refine mem_inf.mpr ⟨a.1.2, mem_centralizer_iff.mpr fun g hg => ?_⟩
    have h2 := hfix a ⟨g, hg⟩
    calc g * (a.1 : G) = g * a.1 * g⁻¹ * g := by group
      _ = (a.1 : G) * g := by rw [show g * (a.1 : G) * g⁻¹ = a.1 from h2]
  have h3 : ∀ a : ↥(V ⊓ centralizer (D : Set G)),
      (⟨(a : G), (mem_inf.mp a.2).1⟩ : V) ∈ MulAction.fixedPoints D V := by
    intro a g
    have hac : (a : G) ∈ centralizer (D : Set G) := (mem_inf.mp a.2).2
    have hga := mem_centralizer_iff.mp hac g g.2
    apply Subtype.ext
    change (g : G) * (a : G) * (g : G)⁻¹ = a
    calc (g : G) * (a : G) * (g : G)⁻¹ = (a : G) * g * (g : G)⁻¹ := by rw [← hga]
      _ = a := by group
  have heq : Nat.card (MulAction.fixedPoints D V) =
      Nat.card (V ⊓ centralizer (D : Set G) : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨(a.1 : G), h1 a⟩
        invFun := fun a => ⟨⟨(a : G), (mem_inf.mp a.2).1⟩, h3 a⟩
        left_inv := fun a => rfl
        right_inv := fun a => rfl }
  rw [heq] at key
  exact key

theorem exists_central_mod {p : ℕ} (hp : p.Prime) {P N Z : Subgroup G} (hP : IsPGroup p P) (hNP : N ≤ P)
    (hNn : ∀ g ∈ P, ∀ u ∈ N, g * u * g⁻¹ ∈ N) (hZN : Z ≤ N)
    (hZn : ∀ g ∈ P, ∀ u ∈ Z, g * u * g⁻¹ ∈ Z) (hlt : Z < N) :
    ∃ v ∈ N, v ∉ Z ∧ ∀ g ∈ P, g * v * g⁻¹ * v⁻¹ ∈ Z := by
  have : Fact p.Prime := ⟨hp⟩
  have hZP : Z ≤ P := hZN.trans hNP
  let Z' : Subgroup ↥P := Z.subgroupOf P
  have hZ'n : Z'.Normal :=
    (Subgroup.normal_subgroupOf_iff hZP).mpr (fun h k hh hk => hZn k hk h hh)
  let N' : Subgroup ↥P := N.subgroupOf P
  have hN'n : N'.Normal :=
    (Subgroup.normal_subgroupOf_iff hNP).mpr (fun h k hh hk => hNn k hk h hh)
  let π : ↥P →* ↥P ⧸ Z' := QuotientGroup.mk' Z'
  have hQ : IsPGroup p (↥P ⧸ Z') := hP.to_quotient Z'
  have hNn' : (N'.map π).Normal := hN'n.map π (QuotientGroup.mk'_surjective Z')
  obtain ⟨n, hnN, hnZ⟩ := Set.exists_of_ssubset hlt
  have hnP : n ∈ P := hNP hnN
  have hne : N'.map π ≠ ⊥ := by
    intro hbot
    have h1 : π ⟨n, hnP⟩ ∈ N'.map π := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hnN)
    rw [hbot, mem_bot] at h1
    exact hnZ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1))
  obtain ⟨ν, hνN, hν1, hνc⟩ := SU1.exists_central_of_normal hp
    (IsPGroup.of_equiv hQ (Subgroup.topEquiv : (⊤ : Subgroup (↥P ⧸ Z')) ≃* _).symm) le_top
    (fun g _ u hu => hNn'.conj_mem u hu g) hne
  obtain ⟨⟨v, hvP⟩, hvN', rfl⟩ := Subgroup.mem_map.mp hνN
  have hvN : v ∈ N := Subgroup.mem_subgroupOf.mp hvN'
  refine ⟨v, hvN, fun hvZ => hν1 ?_, fun g hg => ?_⟩
  · exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hvZ)
  · have h1 := hνc (π ⟨g, hg⟩) (mem_top _)
    have h2 : π (⟨g, hg⟩ * ⟨v, hvP⟩ * ⟨g, hg⟩⁻¹ * ⟨v, hvP⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)

theorem card_pow_even_of_r8 {r z : G} (hr : orderOf r = 8) (hr4 : r ^ 4 = z) {U : Subgroup G}
    (hU3 : IsPGroup 3 U) (hrU : ∀ u ∈ U, r * u * r⁻¹ ∈ U) (hzU : ∀ u ∈ U, z * u * z⁻¹ = u⁻¹) :
    ∃ k : ℕ, Nat.card U = 9 ^ k := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h8 : r ^ 8 = 1 := by rw [← hr]; exact pow_orderOf_eq_one r
  have hrpow : ∀ n : ℕ, ∀ u ∈ U, r ^ n * u * (r ^ n)⁻¹ ∈ U := by
    intro n
    induction n with
    | zero => intro u hu; simpa using hu
    | succ n ih =>
      intro u hu
      have := hrU _ (ih u hu)
      have h : r ^ (n + 1) * u * (r ^ (n + 1))⁻¹ = r * (r ^ n * u * (r ^ n)⁻¹) * r⁻¹ := by
        rw [pow_succ']; group
      rw [h]; exact this
  have hrinv : ∀ u ∈ U, r⁻¹ * u * r ∈ U := by
    intro u hu
    have h7 : r ^ 7 = r⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_succ]; exact h8
    have := hrpow 7 u hu
    rwa [h7, inv_inv] at this
  set σ : G := r * r with hσ
  have hσ2 : σ = r ^ 2 := by rw [hσ, pow_two]
  have hσz : σ * σ = z := by
    rw [← hr4, hσ2, ← pow_add]
  have hσn : σ ∈ normalizer (U : Set G) := by
    rw [mem_normalizer_iff]
    intro u
    refine ⟨fun hu => ?_, fun hu => ?_⟩
    · have h1 := hrU _ (hrU u hu)
      have : σ * u * σ⁻¹ = r * (r * u * r⁻¹) * r⁻¹ := by rw [hσ]; group
      rw [this]; exact h1
    · have h1 := hrinv _ (hrinv _ hu)
      have : r⁻¹ * (r⁻¹ * (σ * u * σ⁻¹) * r) * r = u := by rw [hσ]; group
      rw [this] at h1; exact h1
  have hσ4 : orderOf σ = 4 := by
    rw [hσ2, orderOf_pow' _ (by norm_num), hr]
    norm_num
  have hD4 : Nat.card (zpowers σ) = 4 := by rw [Nat.card_zpowers, hσ4]
  have hDU : zpowers σ ≤ normalizer (U : Set G) := (zpowers_le).mpr hσn
  have hmod := card_modEq_one_of_free (D := zpowers σ) (V := U) hDU (fun d hd hd1 v hv hdv => by
    have hvc : Commute v d := by
      have : v * d = d * v := by
        calc v * d = (d * v * d⁻¹) * d := by rw [hdv]
          _ = d * v := by group
      exact this
    have hzfix : z * v * z⁻¹ = v := by
      obtain ⟨j, rfl⟩ := hd
      beta_reduce at hd1 hdv hvc ⊢
      have hjm : σ ^ j = σ ^ (j % 4) := by
        have := zpow_mod_orderOf σ j
        rw [hσ4] at this
        simpa using this.symm
      have hm : j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by
        have h0 : j % 4 ≠ 0 := by
          intro h0
          apply hd1
          rw [hjm, h0, zpow_zero]
        omega
      have hcz : Commute v z := by
        rcases hm with h | h | h
        · rw [h] at hjm
          have hz' : z = (σ ^ j) * (σ ^ j) := by rw [hjm, zpow_one, hσz]
          rw [hz']
          exact hvc.mul_right hvc
        · rw [h] at hjm
          have hz' : z = σ ^ j := by
            rw [hjm]
            have : σ ^ (2 : ℤ) = σ * σ := by rw [zpow_two]
            rw [this, hσz]
          rw [hz']; exact hvc
        · rw [h] at hjm
          have hz' : z = (σ ^ j) * (σ ^ j) := by
            rw [hjm]
            have h3 : σ ^ (3 : ℤ) = σ ^ 3 := by norm_cast
            rw [h3, ← pow_add]
            have h4 : σ ^ (3 + 3) = σ * σ := by
              have : σ ^ (3 + 3) = σ ^ 4 * σ ^ 2 := by rw [← pow_add]
              rw [this, ← hσ4, pow_orderOf_eq_one, one_mul, pow_two]
            rw [h4, hσz]
          rw [hz']
          exact hvc.mul_right hvc
      calc z * v * z⁻¹ = v * z * z⁻¹ := by rw [← hcz.eq]
        _ = v := by group
    have hvinv : v = v⁻¹ := (hzfix.symm.trans (hzU v hv))
    have hvv : v * v = 1 := by
      calc v * v = v * v⁻¹ := by rw [← hvinv]
        _ = 1 := mul_inv_cancel v
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp hU3 ⟨v, hv⟩
    rw [Subgroup.orderOf_mk] at hk
    by_contra hv1
    have hord : orderOf v = 2 := by
      refine orderOf_eq_prime ?_ hv1
      rw [pow_two]; exact hvv
    rw [hord] at hk
    have hodd : Odd (3 ^ k) := Odd.pow (by decide)
    rw [← hk] at hodd
    exact absurd hodd (by decide))
  rw [hD4] at hmod
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 3)).mp hU3
  rw [hm] at hmod
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k, by rw [hm, hk, ← two_mul, pow_mul]; norm_num⟩
  · exfalso
    have h1 : 3 ^ m = 3 * 9 ^ k := by rw [hk, pow_succ, pow_mul]; norm_num; ring
    have h2 : 9 ^ k % 4 = 1 := by
      rw [Nat.pow_mod]; norm_num
    have h3 : (3 * 9 ^ k) % 4 = 3 := by omega
    have h4 : 3 ^ m % 4 = 1 % 4 := hmod
    rw [h1, h3] at h4
    omega

end CFSG.GH74.Uniqueness.SU.SU13
