module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.NoM125Fusion2
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NonabFB0

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.NoM125

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

private theorem tr_exists_not_comm {S : Sylow p G} (h : IsM125 p (S : Subgroup G)) :
    ∃ a ∈ (S : Subgroup G), ∃ b ∈ (S : Subgroup G), a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  apply h.nonab
  exact ⟨⟨fun x y => Subtype.ext (hcon x.1 x.2 y.1 y.2)⟩⟩

private theorem tr_exists_E_not_Z {S : Sylow p G} (h : IsM125 p (S : Subgroup G)) :
    ∃ b ∈ h.E, b ∉ centralizer ((S : Subgroup G) : Set G) ⊓ (S : Subgroup G) := by
  by_contra hcon
  push Not at hcon
  have hle : h.E ≤ centralizer ((S : Subgroup G) : Set G) ⊓ (S : Subgroup G) := fun b hb => hcon b hb
  have h1 : Nat.card h.E ≤ Nat.card ↥(centralizer ((S : Subgroup G) : Set G) ⊓ (S : Subgroup G)) :=
    Subgroup.card_le_of_le hle
  rw [h.card_E, h.card_Z] at h1
  have h2 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right h.prime.one_lt (by norm_num)
  rw [pow_one] at h2
  omega

private theorem tr_map_comm_eq_one {K A : Type*} [Group K] [CommGroup A] (f : K →* A)
    (x y : K) : f (x * y * x⁻¹ * y⁻¹) = 1 := by
  rw [← commutatorElement_def, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

private theorem tr_of_comm_eq_one {K : Type*} [Group K] (x y : K) :
    Abelianization.of (x * y * x⁻¹ * y⁻¹ : K) = 1 := by
  apply MonoidHom.mem_ker.1
  rw [Abelianization.ker_of, _root_.commutator_def, ← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem tr_of_eq_one_of_mem_cent {S : Sylow p G} (h : IsM125 p (S : Subgroup G))
    {w : (S : Subgroup G)} (hw : (w : G) ∈ centralizer ((S : Subgroup G) : Set G)) :
    Abelianization.of w = 1 := by
  obtain ⟨a, ha, b, hb, hab⟩ := tr_exists_not_comm h
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = a * b * a⁻¹ * b⁻¹ := ⟨_, rfl⟩
  have hcZ : c ∈ centralizer ((S : Subgroup G) : Set G) ⊓ (S : Subgroup G) := by
    rw [hcdef]
    exact h.commutator_mem_Z ha hb
  have hc1 : c ≠ 1 := by
    intro h1
    apply hab
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = c * (b * a) := by rw [hcdef]
      _ = 1 * (b * a) := by rw [h1]
      _ = b * a := one_mul _
  have hcp : c ^ p = 1 := (h.mem_E.1 (h.Z_le_E hcZ)).2
  have hord : orderOf c = p := orderOf_eq_prime hcp hc1
  have hZc : Subgroup.zpowers c = centralizer ((S : Subgroup G) : Set G) ⊓ (S : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hcZ)
      (le_of_eq (by rw [h.card_Z, Nat.card_zpowers, hord]))
  have hwZ : (w : G) ∈ Subgroup.zpowers c := by
    rw [hZc]
    exact Subgroup.mem_inf.2 ⟨hw, w.2⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hwZ
  obtain ⟨γ, hγ⟩ : ∃ γ : (S : Subgroup G), γ = ⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ :=
    ⟨_, rfl⟩
  have hγc : (γ : G) = c := by
    rw [hγ]
    exact hcdef.symm
  have hγ1 : Abelianization.of γ = 1 := by
    rw [hγ]
    exact tr_of_comm_eq_one _ _
  have hwγ : w = γ ^ k := Subtype.ext (by rw [Subgroup.coe_zpow, hγc, hk])
  rw [hwγ, map_zpow, hγ1, one_zpow]

private theorem tr_mem_Z_of_of_eq_one {S : Sylow p G} (h : IsM125 p (S : Subgroup G))
    {w : (S : Subgroup G)} (hw : Abelianization.of w = 1) :
    (w : G) ∈ centralizer ((S : Subgroup G) : Set G) ⊓ (S : Subgroup G) := by
  have hk : w ∈ (Abelianization.of : (S : Subgroup G) →* Abelianization (S : Subgroup G)).ker :=
    MonoidHom.mem_ker.2 hw
  rw [Abelianization.ker_of] at hk
  have hle : commutator (S : Subgroup G) ≤
      (centralizer ((S : Subgroup G) : Set G) ⊓ (S : Subgroup G)).subgroupOf (S : Subgroup G) := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.2 (fun x _ y _ => ?_)
    rw [Subgroup.mem_subgroupOf]
    exact h.commutator_mem_Z x.2 y.2
  exact Subgroup.mem_subgroupOf.1 (hle hk)

private theorem tr_factor_eq {S : Sylow p G} (h : IsM125 p (S : Subgroup G)) {b : G}
    (hbE : b ∈ h.E) (hbZ : b ∉ centralizer ((S : Subgroup G) : Set G) ⊓ (S : Subgroup G)) (n : ℕ) (g : G)
    (hy : g⁻¹ * b ^ n * g ∈ (S : Subgroup G)) :
    Abelianization.of (⟨g⁻¹ * b ^ n * g, hy⟩ : (S : Subgroup G)) =
      Abelianization.of (⟨b, (h.mem_E.1 hbE).1⟩ : (S : Subgroup G)) ^ n := by
  have hbS : b ∈ (S : Subgroup G) := (h.mem_E.1 hbE).1
  have hbp : b ^ p = 1 := (h.mem_E.1 hbE).2
  by_cases hx1 : b ^ n = 1
  · have e1 : (⟨g⁻¹ * b ^ n * g, hy⟩ : (S : Subgroup G)) = 1 :=
      Subtype.ext (by simp [hx1])
    have e2 : (⟨b, hbS⟩ : (S : Subgroup G)) ^ n = 1 :=
      Subtype.ext (by simp [hx1])
    rw [e1, map_one, ← map_pow, e2, map_one]
  · have hnd : ¬ p ∣ n := by
      rintro ⟨m, rfl⟩
      apply hx1
      rw [pow_mul, hbp, one_pow]
    have hcop : Nat.Coprime n p := ((Nat.Prime.coprime_iff_not_dvd h.prime).2 hnd).symm
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h.prime.one_lt
    have hdm := Nat.div_add_mod (n * m) p
    rw [hm] at hdm
    have hnm : b ^ (n * m) = b := by
      rw [← hdm, pow_add, pow_mul, hbp, one_pow, one_mul, pow_one]
    have hxZ : b ^ n ∉ centralizer ((S : Subgroup G) : Set G) := by
      intro hxC
      apply hbZ
      have hbC : b ∈ centralizer ((S : Subgroup G) : Set G) := by
        have hm' := (centralizer ((S : Subgroup G) : Set G)).pow_mem hxC m
        rwa [← pow_mul, hnm] at hm'
      exact Subgroup.mem_inf.2 ⟨hbC, hbS⟩
    have hxE : b ^ n ∈ h.E :=
      h.mem_E.2 ⟨(S : Subgroup G).pow_mem hbS n, by rw [pow_right_comm, hbp, one_pow]⟩
    have hconj := h.conj_mul_inv_mem_Z_of_mem_E hxE hxZ (g := g⁻¹)
      (by rw [inv_inv]; exact hy)
    rw [inv_inv] at hconj
    have hwC : (((⟨g⁻¹ * b ^ n * g, hy⟩ : (S : Subgroup G)) * (⟨b, hbS⟩ ^ n)⁻¹ :
        (S : Subgroup G)) : G) ∈ centralizer ((S : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.1 hconj).1
    have hφw : Abelianization.of
        ((⟨g⁻¹ * b ^ n * g, hy⟩ : (S : Subgroup G)) * (⟨b, hbS⟩ ^ n)⁻¹) = 1 :=
      tr_of_eq_one_of_mem_cent h hwC
    have hdec : (⟨g⁻¹ * b ^ n * g, hy⟩ : (S : Subgroup G)) =
        (⟨g⁻¹ * b ^ n * g, hy⟩ : (S : Subgroup G)) * (⟨b, hbS⟩ ^ n)⁻¹ * ⟨b, hbS⟩ ^ n :=
      (inv_mul_cancel_right _ _).symm
    rw [hdec, map_mul, hφw, one_mul, map_pow]

private theorem tr_transfer_eq {S : Sylow p G} (h : IsM125 p (S : Subgroup G)) {b : G}
    (hbE : b ∈ h.E) (hbZ : b ∉ centralizer ((S : Subgroup G) : Set G) ⊓ (S : Subgroup G)) :
    MonoidHom.transfer (Abelianization.of : (S : Subgroup G) →* Abelianization (S : Subgroup G)) b =
      Abelianization.of (⟨b, (h.mem_E.1 hbE).1⟩ : (S : Subgroup G)) ^ (S : Subgroup G).index := by
  haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers b) (G ⧸ (S : Subgroup G)))) :=
    Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot
      (Abelianization.of : (S : Subgroup G) →* Abelianization (S : Subgroup G)) b,
    Subgroup.index_eq_sum_minimalPeriod (S : Subgroup G) b, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl (fun q _ => tr_factor_eq h hbE hbZ _ _ _)

private theorem tr_transfer_ne_one {S : Sylow p G} (h : IsM125 p (S : Subgroup G)) {b : G}
    (hbE : b ∈ h.E) (hbZ : b ∉ centralizer ((S : Subgroup G) : Set G) ⊓ (S : Subgroup G)) :
    MonoidHom.transfer (Abelianization.of : (S : Subgroup G) →* Abelianization (S : Subgroup G)) b
      ≠ 1 := by
  rw [tr_transfer_eq h hbE hbZ]
  intro h1
  have hbS : b ∈ (S : Subgroup G) := (h.mem_E.1 hbE).1
  have hβp : (⟨b, hbS⟩ : (S : Subgroup G)) ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact (h.mem_E.1 hbE).2
  have hβne : Abelianization.of (⟨b, hbS⟩ : (S : Subgroup G)) ≠ 1 := fun h2 =>
    hbZ (tr_mem_Z_of_of_eq_one h h2)
  have hord : orderOf (Abelianization.of (⟨b, hbS⟩ : (S : Subgroup G))) = p := by
    refine orderOf_eq_prime ?_ hβne
    rw [← map_pow, hβp, map_one]
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  rw [hord] at hdvd
  exact Sylow.not_dvd_index S hdvd

private theorem tr_comm_of_simple {K A : Type*} [Group K] [CommGroup A] (hK : IsSimpleGroup K)
    (V : K →* A) (b : K) (hVb : V b ≠ 1) (x y : K) : x * y = y * x := by
  have hker : V.ker = ⊥ := by
    rcases hK.eq_bot_or_eq_top_of_normal V.ker with h1 | h1
    · exact h1
    · exfalso
      have hbk : b ∈ V.ker := by
        rw [h1]
        exact Subgroup.mem_top b
      exact hVb (MonoidHom.mem_ker.1 hbk)
  have hmem : x * y * x⁻¹ * y⁻¹ ∈ V.ker := MonoidHom.mem_ker.2 (tr_map_comm_eq_one V x y)
  rw [hker, Subgroup.mem_bot, ← commutatorElement_def] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.1 hmem

theorem IsM125.not_isSimpleGroup {S : Sylow p G} (h : IsM125 p (S : Subgroup G)) :
    ¬ IsSimpleGroup G := by
  intro hG
  obtain ⟨b, hbE, hbZ⟩ := tr_exists_E_not_Z h
  obtain ⟨x, _, y, _, hxy⟩ := tr_exists_not_comm h
  exact hxy (tr_comm_of_simple hG
    (MonoidHom.transfer (Abelianization.of : (S : Subgroup G) →* Abelianization (S : Subgroup G)))
    b (tr_transfer_ne_one h hbE hbZ) x y)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.NoM125

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

theorem kFactNoM125Sylow'_holds : KFactNoM125Sylow' := by
  intro K _ _ hsimple _ _ S hS
  obtain ⟨hcard, hnc, hexp, hbig⟩ := hS
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h : NoM125.IsM125 5 (S : Subgroup K) :=
    { prime := Nat.prime_five
      odd := by norm_num
      card := hcard.trans (by norm_num)
      nonab := hnc
      exp := fun s hs => hexp s hs
      big := hbig }
  exact NoM125.IsM125.not_isSimpleGroup h hsimple

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
