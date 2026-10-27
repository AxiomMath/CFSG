module

public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeAutCore
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallF12Red
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeCosetPoints

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallReeBorel

open CFSG.LieType.Ree CFSG.ComponentClassification.LiteratureLocal.SmallRee CFSG.Walter.Ree.Model
open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Red (KleinFour3)
open scoped Pointwise


variable (K : Type) [Field K] [Finite K] [CharP K ReeTag.G2.prime]

@[expose] noncomputable def ub : Subgroup (ReeTag.G2.reeGamma K 1) :=
  (ReeTag.G2.reeFixedPosUnipotent K 1).subgroupOf (ReeTag.G2.reeGamma K 1)

@[expose] noncomputable def bor : Subgroup (ReeTag.G2.reeGamma K 1) :=
  (ReeTag.G2.reeFixedBorel K 1).subgroupOf (ReeTag.G2.reeGamma K 1)

variable {K}

section Coord

variable (hK : Nat.card K = 3 ^ (2 * 1 + 1))

include hK

theorem uIn_mem_ub (t b c : K) : uIn hK t b c ∈ ub K :=
  Subgroup.mem_subgroupOf.2 (uIn_mem hK t b c)

theorem exists_uIn_of_mem_ub {x : ReeTag.G2.reeGamma K 1} (hx : x ∈ ub K) :
    ∃ t b c : K, x = uIn hK t b c :=
  exists_uIn_eq hK (Subgroup.mem_subgroupOf.1 hx)

theorem hIn_mul (s s' : Kˣ) : hIn hK s * hIn hK s' = hIn hK (s * s') := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, hIn_val, hIn_val, hIn_val, smallReeH_mul]

theorem hIn_one : hIn hK 1 = 1 := by
  apply Subtype.ext
  rw [hIn_val, OneMemClass.coe_one, smallReeH_one]

theorem commute_z (t b c : K) : uIn hK t b c * uIn hK 0 0 1 = uIn hK 0 0 1 * uIn hK t b c := by
  rw [uIn_mul, uIn_mul]
  congr 1 <;> simp [smallReeSigma_zero] <;> ring

theorem central_z {u : ReeTag.G2.reeGamma K 1} (hu : u ∈ ub K) :
    u * uIn hK 0 0 1 = uIn hK 0 0 1 * u := by
  obtain ⟨t, b, c, rfl⟩ := exists_uIn_of_mem_ub hK hu
  exact commute_z hK t b c

theorem conj_z (s : Kˣ) : hIn hK s * uIn hK 0 0 1 * (hIn hK s)⁻¹ = uIn hK 0 0 ((s : K) ^ 3) := by
  rw [hIn_conj_uIn hK s 0 0 1]
  simp

theorem hIn_conj_mem_ub (s : Kˣ) {u : ReeTag.G2.reeGamma K 1} (hu : u ∈ ub K) :
    hIn hK s * u * (hIn hK s)⁻¹ ∈ ub K := by
  obtain ⟨t, b, c, rfl⟩ := exists_uIn_of_mem_ub hK hu
  rw [hIn_conj_uIn hK s t b c]
  exact uIn_mem_ub hK _ _ _

theorem eq_one_of_hIn_mem_ub {s : Kˣ} (hs : hIn hK s ∈ ub K) : s = 1 := by
  have hcomm : hIn hK s * uIn hK 0 0 1 = uIn hK 0 0 1 * hIn hK s := central_z hK hs
  have hz : hIn hK s * uIn hK 0 0 1 * (hIn hK s)⁻¹ = uIn hK 0 0 1 := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rw [conj_z hK s] at hz
  have h3 : (s : K) ^ 3 = 1 := (uIn_inj hK hz).2.2
  haveI := Fintype.ofFinite K
  have hc : Fintype.card K = 27 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
  have h26 : (s : K) ^ 26 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one (s : K) s.ne_zero
    rw [hc] at this
    simpa using this
  have hs3 : s ^ 3 = 1 := Units.ext (by simpa using h3)
  have hs26 : s ^ 26 = 1 := Units.ext (by simpa using h26)
  have h1 : s ^ Nat.gcd 3 26 = 1 := pow_gcd_eq_one.2 ⟨hs3, hs26⟩
  simpa using h1

theorem eq_one_of_sq_mem_ub {x : ReeTag.G2.reeGamma K 1} (hx : x ∈ ub K) (hx2 : x * x = 1) :
    x = 1 := by
  obtain ⟨t, b, c, rfl⟩ := exists_uIn_of_mem_ub hK hx
  have h2 : uIn hK (t + t) (b + b + smallReeSigma 1 t * t) (c + c - b * t + smallReeSigma 1 t * t ^ 2)
      = uIn hK 0 0 0 := by
    rw [← uIn_mul, hx2, uIn_zero]
  obtain ⟨ht2, hb2, hc2⟩ := uIn_inj hK h2
  have ht : t = 0 := by
    have h : (2 : K) * t = 0 := by linear_combination ht2
    exact (mul_eq_zero.1 h).resolve_left (two_ne_zero_of_charP)
  subst ht
  simp only [smallReeSigma_zero, mul_zero, zero_mul, add_zero, zero_add, sub_zero] at hb2 hc2
  have hb : b = 0 := by
    have h : (2 : K) * b = 0 := by linear_combination hb2
    exact (mul_eq_zero.1 h).resolve_left (two_ne_zero_of_charP)
  subst hb
  have hc : c = 0 := by
    have h : (2 : K) * c = 0 := by linear_combination hc2
    exact (mul_eq_zero.1 h).resolve_left (two_ne_zero_of_charP)
  subst hc
  exact uIn_zero hK

theorem bor_decomp {x : ReeTag.G2.reeGamma K 1} (hx : x ∈ bor K) :
    ∃ u ∈ ub K, ∃ s : Kˣ, x = u * hIn hK s := by
  have hx' : (x : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedBorel K 1 :=
    Subgroup.mem_subgroupOf.1 hx
  rw [← SetLike.mem_coe, ReeTag.reeFixedBorel_eq_mul' (t := ReeTag.G2)] at hx'
  obtain ⟨u, hu, h, hh, huh⟩ := Set.mem_mul.1 hx'
  have hu' : u ∈ ReeTag.G2.reeGamma K 1 := ReeTag.reeFixedPosUnipotent_le_reeGamma hu
  obtain ⟨s, hs⟩ := exists_smallReeH_eq (a := 1) (K := K) hh
  refine ⟨⟨u, hu'⟩, Subgroup.mem_subgroupOf.2 hu, s, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, hIn_val, hs, huh]

theorem invol_bor {x : ReeTag.G2.reeGamma K 1} (hx : x ∈ bor K) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ∃ u ∈ ub K, x = u * hIn hK (-1) := by
  obtain ⟨u, hu, s, rfl⟩ := bor_decomp hK hx
  have hu' : hIn hK s * u * (hIn hK s)⁻¹ ∈ ub K := hIn_conj_mem_ub hK s hu
  have key : u * (hIn hK s * u * (hIn hK s)⁻¹) * (hIn hK s * hIn hK s) = 1 := by
    rw [← hx2]; group
  have hsq : hIn hK s * hIn hK s ∈ ub K := by
    have h := eq_inv_of_mul_eq_one_right key
    rw [h]
    exact (ub K).inv_mem ((ub K).mul_mem hu hu')
  rw [hIn_mul] at hsq
  have hss : s * s = 1 := eq_one_of_hIn_mem_ub hK hsq
  have hK' : (s : K) * s = 1 := by
    have := congrArg Units.val hss
    simpa using this
  rcases mul_self_eq_one_iff.1 hK' with h1 | h1
  · have hs1 : s = 1 := Units.ext (by simpa using h1)
    subst hs1
    rw [hIn_one, mul_one] at hx2 hx1
    exact (hx1 (eq_one_of_sq_mem_ub hK hu hx2)).elim
  · have hs1 : s = -1 := Units.ext (by simpa using h1)
    subst hs1
    exact ⟨u, hu, rfl⟩

theorem eq_of_commute_invol_bor {x₁ x₂ : ReeTag.G2.reeGamma K 1} (h₁ : x₁ ∈ bor K) (h₂ : x₂ ∈ bor K)
    (hs₁ : x₁ * x₁ = 1) (hs₂ : x₂ * x₂ = 1) (hn₁ : x₁ ≠ 1) (hn₂ : x₂ ≠ 1)
    (hc : x₁ * x₂ = x₂ * x₁) : x₁ = x₂ := by
  obtain ⟨u₁, hu₁, hx₁⟩ := invol_bor hK h₁ hs₁ hn₁
  obtain ⟨u₂, hu₂, hx₂⟩ := invol_bor hK h₂ hs₂ hn₂
  have hhh : hIn hK (-1) * hIn hK (-1) = 1 := by
    rw [hIn_mul, neg_one_mul, neg_neg, hIn_one]
  have hinv : (hIn hK (-1))⁻¹ = hIn hK (-1) := inv_eq_of_mul_eq_one_right hhh
  have hw : x₁ * x₂ ∈ ub K := by
    have e : x₁ * x₂ = u₁ * (hIn hK (-1) * u₂ * (hIn hK (-1))⁻¹) := by
      rw [hx₁, hx₂, hinv]
      group
    rw [e]
    exact (ub K).mul_mem hu₁ (hIn_conj_mem_ub hK (-1) hu₂)
  have hsq : (x₁ * x₂) * (x₁ * x₂) = 1 := by
    calc x₁ * x₂ * (x₁ * x₂) = x₁ * (x₂ * x₁) * x₂ := by group
      _ = x₁ * (x₁ * x₂) * x₂ := by rw [hc]
      _ = (x₁ * x₁) * (x₂ * x₂) := by group
      _ = 1 := by rw [hs₁, hs₂, one_mul]
  have h1 := eq_one_of_sq_mem_ub hK hw hsq
  have h2 : x₂ = x₁⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [h2]
  exact (inv_eq_of_mul_eq_one_right hs₁).symm

end Coord

section Action

theorem borel_facts (hK : Nat.card K = 3 ^ (2 * 1 + 1)) :
    (∀ ω ω' : ReeTag.G2.reeGamma K 1 ⧸ bor K, ω ≠ QuotientGroup.mk 1 → ω' ≠ QuotientGroup.mk 1 →
        ∃! u : ub K, (u : ReeTag.G2.reeGamma K 1) • ω = ω') ∧
    MulAction.stabilizer (ReeTag.G2.reeGamma K 1) (QuotientGroup.mk 1 : ReeTag.G2.reeGamma K 1 ⧸ bor K)
        = bor K ∧
    ∃ P : Sylow 3 (ReeTag.G2.reeGamma K 1), (P : Subgroup (ReeTag.G2.reeGamma K 1)) = ub K := by
  obtain ⟨w₀, hw₀, -⟩ := CFSG.LieType.Chevalley.weyl_longest_element ReeTag.G2.tag
  obtain ⟨-, -, -, -, -, -, hreg, -, -, -, hP, hstab, -, -, -⟩ :=
    small_Ree_Borel_coset_Sylow_action 1 K hK w₀ hw₀
  exact ⟨hreg, hstab, hP⟩

theorem ub_le_bor : ub K ≤ bor K := by
  intro x hx
  exact Subgroup.mem_subgroupOf.2
    (ReeTag.reeFixedPosUnipotent_le_reeFixedBorel (Subgroup.mem_subgroupOf.1 hx))

theorem smul_base_eq_iff (hK : Nat.card K = 3 ^ (2 * 1 + 1)) (x : ReeTag.G2.reeGamma K 1) :
    x • (QuotientGroup.mk 1 : ReeTag.G2.reeGamma K 1 ⧸ bor K) = QuotientGroup.mk 1 ↔ x ∈ bor K := by
  rw [← MulAction.mem_stabilizer_iff, (borel_facts hK).2.1]

theorem reg_ub (hK : Nat.card K = 3 ^ (2 * 1 + 1)) {u : ReeTag.G2.reeGamma K 1} (hu : u ∈ ub K)
    (hu1 : u ≠ 1) {ω : ReeTag.G2.reeGamma K 1 ⧸ bor K} (h : u • ω = ω) :
    ω = QuotientGroup.mk 1 := by
  by_contra hω
  obtain ⟨v, -, huniq⟩ := (borel_facts hK).1 ω ω hω hω
  have e1 : (⟨u, hu⟩ : ub K) = v := huniq _ h
  have e2 : (1 : ub K) = v := huniq _ (by simp)
  exact hu1 (congrArg Subtype.val (e1.trans e2.symm))

end Action

section Klein

theorem exists_fix_three (hK : Nat.card K = 3 ^ (2 * 1 + 1)) {k : ReeTag.G2.reeGamma K 1}
    (hk3 : k ^ 3 = 1) (hk : k ≠ 1) :
    ∃ g : ReeTag.G2.reeGamma K 1, ∀ ω : ReeTag.G2.reeGamma K 1 ⧸ bor K,
      k • ω = ω ↔ ω = g • (QuotientGroup.mk 1 : ReeTag.G2.reeGamma K 1 ⧸ bor K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf k = 3 := orderOf_eq_prime hk3 hk
  have hzk : IsPGroup 3 (Subgroup.zpowers k) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  obtain ⟨P, hP⟩ := hzk.exists_le_sylow
  obtain ⟨P0, hP0⟩ := (borel_facts hK).2.2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ReeTag.G2.reeGamma K 1) P0 P
  have hkP : k ∈ (P : Subgroup (ReeTag.G2.reeGamma K 1)) := hP (Subgroup.mem_zpowers k)
  rw [← hg, Sylow.coe_subgroup_smul, hP0, Subgroup.mem_smul_pointwise_iff_exists] at hkP
  obtain ⟨u, hu, huk⟩ := hkP
  have hk_eq : g * u * g⁻¹ = k := huk
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply hk
    rw [← hk_eq]
    simp
  refine ⟨g, fun ω => ⟨fun hω => ?_, fun hω => ?_⟩⟩
  · rw [← hk_eq] at hω
    have h1 : u • (g⁻¹ • ω) = g⁻¹ • ω := by
      have e : u • (g⁻¹ • ω) = g⁻¹ • ((g * u * g⁻¹) • ω) := by
        rw [smul_smul, smul_smul]
        congr 1
        group
      rw [e, hω]
    have h2 := reg_ub hK hu hu1 h1
    rw [← smul_inv_smul g ω, h2]
  · rw [← hk_eq, hω]
    have h3 : u • (QuotientGroup.mk 1 : ReeTag.G2.reeGamma K 1 ⧸ bor K) = QuotientGroup.mk 1 :=
      (smul_base_eq_iff hK u).2 (ub_le_bor hu)
    have e : (g * u * g⁻¹) • (g • (QuotientGroup.mk 1 : ReeTag.G2.reeGamma K 1 ⧸ bor K))
        = g • (u • (QuotientGroup.mk 1 : ReeTag.G2.reeGamma K 1 ⧸ bor K)) := by
      rw [smul_smul, smul_smul]
      congr 1
      group
    rw [e, h3]

theorem klein_gamma (hK : Nat.card K = 3 ^ (2 * 1 + 1)) {x₁ x₂ k : ReeTag.G2.reeGamma K 1}
    (hs₁ : x₁ * x₁ = 1) (hs₂ : x₂ * x₂ = 1) (hn₁ : x₁ ≠ 1) (hn₂ : x₂ ≠ 1) (hne : x₁ ≠ x₂)
    (hc : x₁ * x₂ = x₂ * x₁) (hk3 : k ^ 3 = 1) (hk1 : k * x₁ = x₁ * k) (hk2 : k * x₂ = x₂ * k) :
    k = 1 := by
  by_contra hk
  obtain ⟨g, hfix⟩ := exists_fix_three hK hk3 hk
  have hω₀ : k • (g • (QuotientGroup.mk 1 : ReeTag.G2.reeGamma K 1 ⧸ bor K)) =
      g • (QuotientGroup.mk 1 : ReeTag.G2.reeGamma K 1 ⧸ bor K) := (hfix _).2 rfl
  have hfixed : ∀ x : ReeTag.G2.reeGamma K 1, k * x = x * k → g⁻¹ * x * g ∈ bor K := by
    intro x hx
    have h1 : k • (x • (g • (QuotientGroup.mk 1 : ReeTag.G2.reeGamma K 1 ⧸ bor K))) =
        x • (g • (QuotientGroup.mk 1 : ReeTag.G2.reeGamma K 1 ⧸ bor K)) := by
      rw [← mul_smul, hx, mul_smul, hω₀]
    have h2 := (hfix _).1 h1
    rw [← smul_base_eq_iff hK]
    calc (g⁻¹ * x * g) • (QuotientGroup.mk 1 : ReeTag.G2.reeGamma K 1 ⧸ bor K)
        = g⁻¹ • (x • (g • (QuotientGroup.mk 1 : ReeTag.G2.reeGamma K 1 ⧸ bor K))) := by
          rw [smul_smul, smul_smul, mul_assoc]
      _ = g⁻¹ • (g • (QuotientGroup.mk 1 : ReeTag.G2.reeGamma K 1 ⧸ bor K)) := by rw [h2]
      _ = QuotientGroup.mk 1 := inv_smul_smul g _
  have h₁ := hfixed x₁ hk1
  have h₂ := hfixed x₂ hk2
  have hc' : (g⁻¹ * x₁ * g) * (g⁻¹ * x₂ * g) = (g⁻¹ * x₂ * g) * (g⁻¹ * x₁ * g) := by
    calc (g⁻¹ * x₁ * g) * (g⁻¹ * x₂ * g) = g⁻¹ * (x₁ * x₂) * g := by group
      _ = g⁻¹ * (x₂ * x₁) * g := by rw [hc]
      _ = (g⁻¹ * x₂ * g) * (g⁻¹ * x₁ * g) := by group
  have hs₁' : (g⁻¹ * x₁ * g) * (g⁻¹ * x₁ * g) = 1 := by
    calc (g⁻¹ * x₁ * g) * (g⁻¹ * x₁ * g) = g⁻¹ * (x₁ * x₁) * g := by group
      _ = 1 := by rw [hs₁]; group
  have hs₂' : (g⁻¹ * x₂ * g) * (g⁻¹ * x₂ * g) = 1 := by
    calc (g⁻¹ * x₂ * g) * (g⁻¹ * x₂ * g) = g⁻¹ * (x₂ * x₂) * g := by group
      _ = 1 := by rw [hs₂]; group
  have hn₁' : g⁻¹ * x₁ * g ≠ 1 := by
    intro h
    apply hn₁
    calc x₁ = g * (g⁻¹ * x₁ * g) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [h]
      _ = 1 := by group
  have hn₂' : g⁻¹ * x₂ * g ≠ 1 := by
    intro h
    apply hn₂
    calc x₂ = g * (g⁻¹ * x₂ * g) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [h]
      _ = 1 := by group
  have hne' : g⁻¹ * x₁ * g ≠ g⁻¹ * x₂ * g := by
    intro h
    apply hne
    calc x₁ = g * (g⁻¹ * x₁ * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * x₂ * g) * g⁻¹ := by rw [h]
      _ = x₂ := by group
  exact hne' (eq_of_commute_invol_bor hK h₁ h₂ hs₁' hs₂' hn₁' hn₂' hc')

theorem conj_eq_one_iff (hK : Nat.card K = 3 ^ (2 * 1 + 1)) (x : ReeTag.G2.reeGamma K 1) :
    MulAut.conj x = 1 ↔ x = 1 := by
  constructor
  · intro h
    have hc : x ∈ Subgroup.center (ReeTag.G2.reeGamma K 1) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h' := DFunLike.congr_fun h g
      rw [MulAut.conj_apply, MulAut.one_apply] at h'
      calc g * x = (x * g * x⁻¹) * x := by rw [h']
        _ = x * g := by group
    rw [(small_Ree_fixed_group_center_trivial 1 K hK).1, Subgroup.mem_bot] at hc
    exact hc
  · rintro rfl
    exact map_one MulAut.conj

theorem conj_inj (hK : Nat.card K = 3 ^ (2 * 1 + 1)) {x y : ReeTag.G2.reeGamma K 1}
    (h : MulAut.conj x = MulAut.conj y) : x = y := by
  have h1 : MulAut.conj (x * y⁻¹) = 1 := by
    rw [map_mul MulAut.conj, map_inv MulAut.conj, h, mul_inv_cancel]
  exact mul_inv_eq_one.1 ((conj_eq_one_iff hK _).1 h1)

theorem kleinFour_inner (hK : Nat.card K = 3 ^ (2 * 1 + 1)) :
    KleinFour3 (inner (ReeTag.G2.reeGamma K 1)) := by
  intro g₁ g₂ k h₁ h₂ hs₁ hs₂ hn₁ hn₂ hne hc hkI hk3 hk1 hk2
  obtain ⟨x₁, rfl⟩ := h₁
  obtain ⟨x₂, rfl⟩ := h₂
  obtain ⟨y, rfl⟩ := hkI
  have e1 : x₁ * x₁ = 1 := by
    rw [← sq]; exact (conj_eq_one_iff hK _).1 (by rw [map_pow]; exact hs₁)
  have e2 : x₂ * x₂ = 1 := by
    rw [← sq]; exact (conj_eq_one_iff hK _).1 (by rw [map_pow]; exact hs₂)
  have n1 : x₁ ≠ 1 := fun h => hn₁ (by rw [h, map_one])
  have n2 : x₂ ≠ 1 := fun h => hn₂ (by rw [h, map_one])
  have ne : x₁ ≠ x₂ := fun h => hne (by rw [h])
  have c : x₁ * x₂ = x₂ * x₁ := conj_inj hK (by rw [map_mul, map_mul]; exact hc)
  have k1 : y * x₁ = x₁ * y := conj_inj hK (by rw [map_mul, map_mul]; exact hk1)
  have k2 : y * x₂ = x₂ * y := conj_inj hK (by rw [map_mul, map_mul]; exact hk2)
  have k3 : y ^ 3 = 1 := (conj_eq_one_iff hK _).1 (by rw [map_pow]; exact hk3)
  rw [klein_gamma hK e1 e2 n1 n2 ne c k3 k1 k2, map_one]

end Klein

end CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallReeBorel
