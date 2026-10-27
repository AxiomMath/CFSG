module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.Chevalley

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def sec63PowSub (R : Subgroup G) (e : ℕ) : Subgroup G :=
  Subgroup.closure {g | ∃ r ∈ R, g = r ^ e}

theorem sec63PowSub_le {R U : Subgroup G} {e : ℕ} (h : ∀ r ∈ R, r ^ e ∈ U) :
    sec63PowSub R e ≤ U := by
  change Subgroup.closure {g : G | ∃ r ∈ R, g = r ^ e} ≤ U
  rw [Subgroup.closure_le]
  rintro g ⟨r, hr, rfl⟩
  exact h r hr

theorem sec63PowSub_conj {R : Subgroup G} {e : ℕ} {a : G} (ha : a ∈ normalizer (R : Set G))
    {q : G} (hq : q ∈ sec63PowSub R e) : a * q * a⁻¹ ∈ sec63PowSub R e := by
  change q ∈ Subgroup.closure {g : G | ∃ r ∈ R, g = r ^ e} at hq
  change a * q * a⁻¹ ∈ Subgroup.closure {g : G | ∃ r ∈ R, g = r ^ e}
  induction hq using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨r, hr, rfl⟩ := hx
      rw [← conj_pow]
      exact Subgroup.subset_closure
        ⟨a * r * a⁻¹, (Subgroup.mem_normalizer_iff.mp ha r).mp hr, rfl⟩
  | one => simp
  | mul x y _ _ hx hy =>
      rw [show a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) by group]
      exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
      rw [show a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ hx

theorem sec63_mem_powSub [Finite G] {R U : Subgroup G} {y : G} {e : ℕ} (hU2 : IsPGroup 2 U)
    (hU : IsCyclic ↥U) (hUR : U ≤ R) (hy : orderOf y = 2) (hyU : y ∈ U) (he : e = 2 ∨ e = 4)
    (hcard : 2 * e ≤ Nat.card U) : y ∈ sec63PowSub R e := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU2
  haveI : IsCyclic ↥U := hU
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := ↥U)
  have htop : Subgroup.zpowers γ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact hγ x
  have horder : orderOf γ = 2 ^ k := by
    rw [← Nat.card_zpowers, htop, Subgroup.card_top]
    exact hk
  have hyγ : (⟨y, hyU⟩ : ↥U) ∈ Subgroup.zpowers γ := hγ ⟨y, hyU⟩
  rw [mem_zpowers_iff_mem_range_orderOf] at hyγ
  obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hyγ
  have hpow : γ ^ (2 * m) = 1 := by
    have hsq : (γ ^ m) ^ 2 = 1 := by
      have ho : orderOf (γ ^ m) = 2 := by
        rw [hm, Subgroup.orderOf_mk y hyU, hy]
      simpa [ho] using pow_orderOf_eq_one (γ ^ m)
    rwa [← pow_mul, Nat.mul_comm] at hsq
  have hdvd : 2 ^ k ∣ 2 * m := by
    have := orderOf_dvd_iff_pow_eq_one.mpr hpow
    rwa [horder] at this
  have h2e_dvd : 2 * e ∣ 2 ^ k := by
    rcases he with rfl | rfl
    · have h4le : 4 ≤ 2 ^ k := by
        rw [hk] at hcard
        norm_num at hcard
        exact hcard
      have hk2 : 2 ≤ k := by
        apply (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp
        simpa using h4le
      simpa using Nat.pow_dvd_pow 2 hk2
    · have h8le : 8 ≤ 2 ^ k := by
        rw [hk] at hcard
        norm_num at hcard
        exact hcard
      have hk3 : 3 ≤ k := by
        apply (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp
        simpa using h8le
      simpa using Nat.pow_dvd_pow 2 hk3
  have he_dvd : e ∣ m := by
    have h2em : 2 * e ∣ 2 * m := h2e_dvd.trans hdvd
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp h2em
  obtain ⟨j, hj⟩ := he_dvd
  have hcoe : (γ : G) ^ m = y := by
    have := congrArg Subtype.val hm
    simpa [Subgroup.coe_pow] using this
  exact Subgroup.subset_closure ⟨(γ : G) ^ j, hUR (pow_mem γ.2 j), by
    rw [← hcoe, hj, pow_mul']⟩

theorem sec63_eq_of_char_cyclic [Finite G] {T R Q : Subgroup G} {y : G} (hT : IsPGroup 2 T)
    (hRT : R ≤ T) (hy : orderOf y = 2) (hyQ : y ∈ Q) (hQ : IsCyclic ↥Q)
    (hcent : ∀ r ∈ T, r * y = y * r → r ∈ R)
    (hchar : ∀ a ∈ normalizer (R : Set G), ∀ q ∈ Q, a * q * a⁻¹ ∈ Q) : R = T := by
  classical
  have hy2 : y ^ 2 = 1 := by simpa [hy] using pow_orderOf_eq_one y
  have hyne : y ≠ 1 := by
    intro h
    have h1 : orderOf y = 1 := orderOf_eq_one_iff.mpr h
    rw [hy] at h1
    exact absurd h1 (by norm_num)
  have hN : ∀ a ∈ T, a ∈ normalizer (R : Set G) → a ∈ R := by
    intro a haT haN
    set z : G := a * y * a⁻¹ with hz
    have hzQ : z ∈ Q := hchar a haN y hyQ
    have hz2 : z ^ 2 = 1 := by
      rw [hz, conj_pow, hy2]
      group
    have hz1 : z ≠ 1 := by
      intro h
      apply hyne
      calc y = a⁻¹ * (a * y * a⁻¹) * a := by group
        _ = 1 := by rw [← hz, h]; group
    haveI : IsCyclic ↥Q := hQ
    haveI : Finite ↥Q := Subtype.finite
    haveI : Fintype ↥Q := Fintype.ofFinite ↥Q
    set ys : ↥Q := ⟨y, hyQ⟩ with hysdef
    set zs : ↥Q := ⟨z, hzQ⟩ with hzsdef
    have hys2 : ys ^ 2 = 1 := by
      rw [hysdef]
      apply Subtype.ext
      simpa using hy2
    have hzs2 : zs ^ 2 = 1 := by
      rw [hzsdef]
      apply Subtype.ext
      simpa using hz2
    have hS : (Finset.univ.filter (fun a : ↥Q => a ^ 2 = 1)).card ≤ 2 :=
      IsCyclic.card_pow_eq_one_le (α := ↥Q) (n := 2) (by norm_num)
    have hone : (1 : ↥Q) ∈ Finset.univ.filter (fun a : ↥Q => a ^ 2 = 1) := by simp
    have hysmem : ys ∈ Finset.univ.filter (fun a : ↥Q => a ^ 2 = 1) := by simp [hys2]
    have hzsmem : zs ∈ Finset.univ.filter (fun a : ↥Q => a ^ 2 = 1) := by simp [hzs2]
    have hysne : ys ≠ 1 := by
      intro h
      apply hyne
      simpa [hysdef] using congrArg Subtype.val h
    have hzsne : zs ≠ 1 := by
      intro h
      apply hz1
      simpa [hzsdef] using congrArg Subtype.val h
    have herase : ((Finset.univ.filter (fun a : ↥Q => a ^ 2 = 1)).erase 1).card ≤ 1 := by
      rw [Finset.card_erase_of_mem hone]
      omega
    have hyseq : ys = zs :=
      Finset.card_le_one.mp herase ys (Finset.mem_erase.mpr ⟨hysne, hysmem⟩)
        zs (Finset.mem_erase.mpr ⟨hzsne, hzsmem⟩)
    have hyz : y = z := by
      simpa [hysdef, hzsdef] using congrArg Subtype.val hyseq
    exact hcent a haT (by
      calc a * y = (a * y * a⁻¹) * a := by group
        _ = y * a := by rw [← hz, ← hyz])
  by_contra hne
  have hneTop : R.subgroupOf T ≠ ⊤ := by
    intro htop
    apply hne
    refine le_antisymm hRT ?_
    intro t ht
    have : (⟨t, ht⟩ : ↥T) ∈ R.subgroupOf T := by
      rw [htop]
      exact Subgroup.mem_top _
    simpa using Subgroup.mem_subgroupOf.mp this
  have hlt : R.subgroupOf T < ⊤ := lt_of_le_of_ne le_top hneTop
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥T := Subtype.finite
  haveI : Group.IsNilpotent ↥T := hT.isNilpotent
  have hltN : R.subgroupOf T < normalizer (R.subgroupOf T) :=
    (Group.normalizerCondition_of_isNilpotent (G := ↥T)) (R.subgroupOf T) hlt
  have hex : ∃ a : ↥T, a ∈ normalizer (R.subgroupOf T) ∧ a ∉ R.subgroupOf T := by
    by_contra h
    push Not at h
    exact hltN.ne (le_antisymm h hltN.le).symm
  obtain ⟨a, haN, haR⟩ := hex
  have haNG : (a : G) ∈ normalizer (R : Set G) := by
    have hnorm : normalizer (R.subgroupOf T) = (normalizer (R : Set G)).subgroupOf T :=
      (Subgroup.subgroupOf_normalizer_eq hRT).symm
    have : a ∈ (normalizer (R : Set G)).subgroupOf T := hnorm ▸ haN
    exact Subgroup.mem_subgroupOf.mp this
  have haR' : (a : G) ∈ R := hN (a : G) a.2 haNG
  exact haR (Subgroup.mem_subgroupOf.mpr haR')

theorem sec63_rank_of_power [Finite G] {T R U : Subgroup G} {y : G} {e : ℕ} (hT : IsPGroup 2 T)
    (hRT : R ≤ T) (hcent : ∀ r ∈ T, r * y = y * r → r ∈ R) (hy : orderOf y = 2)
    (hU : IsCyclic ↥U) (hUR : U ≤ R) (hyU : y ∈ U) (he : e = 2 ∨ e = 4)
    (hpow : ∀ r ∈ R, r ^ e ∈ U) (hcard : 2 * e ≤ Nat.card U)
    (hE : ∀ E : Subgroup G, E ≤ R → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≤ 4) :
    R = T ∧ CFSG.Open.pRank 2 T ≤ 2 := by
  have hU2 : IsPGroup 2 U := hT.to_le (hUR.trans hRT)
  have hyQ : y ∈ sec63PowSub R e := sec63_mem_powSub hU2 hU hUR hy hyU he hcard
  have hQcyc : IsCyclic ↥(sec63PowSub R e) := by
    haveI : IsCyclic ↥U := hU
    exact Subgroup.isCyclic_of_le (sec63PowSub_le hpow)
  have hRT' : R = T :=
    sec63_eq_of_char_cyclic hT hRT hy hyQ hQcyc hcent
      (fun a ha q hq => sec63PowSub_conj (R := R) (e := e) ha hq)
  refine ⟨hRT', ?_⟩
  rw [← hRT']
  refine CFSG.SectionRank.pRank_le (p := 2) (k := 2) (by norm_num) ?_
  intro E hER hEab
  calc Nat.card E ≤ 4 := hE E hER hEab
    _ = 2 ^ 2 := by norm_num

end CFSG.OddStandard.SmallF3.Omega
