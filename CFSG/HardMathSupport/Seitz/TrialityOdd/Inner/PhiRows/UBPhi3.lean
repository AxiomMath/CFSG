module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.UBPlaneData
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.UBLines
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.UBKey
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.QPlusModel

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.LieType.Universal
  CFSG.ClassicalInvolution.G2D4Models CFSG.ClassicalInvolution.ModelFacts CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.SEITZ11.G2Seven
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open scoped MatrixGroups

section Abstract

variable {G : Type*} [Group G]

theorem exists_zpow_mul_zpow_of_mem_sup {z c x : G} (hzc : Commute z c)
    (hx : x ∈ zpowers z ⊔ zpowers c) : ∃ i j : ℤ, x = z ^ i * c ^ j := by
  let S : Subgroup G :=
    { carrier := {g | ∃ i j : ℤ, g = z ^ i * c ^ j}
      mul_mem' := by
        rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
        refine ⟨i + k, j + l, ?_⟩
        rw [zpow_add, zpow_add]
        have h : c ^ j * z ^ k = z ^ k * c ^ j := (hzc.symm.zpow_zpow j k).eq
        calc z ^ i * c ^ j * (z ^ k * c ^ l) = z ^ i * (c ^ j * z ^ k) * c ^ l := by group
          _ = z ^ i * (z ^ k * c ^ j) * c ^ l := by rw [h]
          _ = z ^ i * z ^ k * (c ^ j * c ^ l) := by group
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, j, rfl⟩
        refine ⟨-i, -j, ?_⟩
        rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
        exact (hzc.symm.zpow_zpow (-j) (-i)).eq }
  have hle : zpowers z ⊔ zpowers c ≤ S :=
    sup_le (zpowers_le.2 ⟨1, 0, by simp⟩) (zpowers_le.2 ⟨0, 1, by simp⟩)
  exact hle hx

theorem exists_nat_pow_eq_zpow {g : G} {r : ℕ} (hr : 0 < r) (hg : orderOf g = r) (i : ℤ) :
    ∃ a : ℕ, g ^ i = g ^ a := by
  refine ⟨(i % (r : ℤ)).toNat, ?_⟩
  have h1 : g ^ (i % (orderOf g : ℤ)) = g ^ i := zpow_mod_orderOf g i
  rw [hg] at h1
  have h2 : 0 ≤ i % (r : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hr.ne')
  rw [← h1, ← zpow_natCast, Int.toNat_of_nonneg h2]

theorem exists_good_generator {r : ℕ} [Fact r.Prime] {z c : G} (hz : orderOf z = r)
    (hc : orderOf c = r) (hzc : Commute z c) (M : Fin 4 → Subgroup G)
    (hM : ∀ i, M i ≤ zpowers z ⊔ zpowers c) (hcard : ∀ i, Nat.card (M i) = r)
    (hdist : ∀ i j, i ≠ j → M i ≠ M j) (P : G → Prop)
    (hP : ∀ i, ∀ x ∈ M i, x ≠ 1 → P x) :
    ∃ a b : ℕ, ¬ r ∣ a ∧ ¬ r ∣ b ∧ z ^ a * c ^ b ≠ 1 ∧ P (z ^ a * c ^ b) := by
  have hr : r.Prime := Fact.out
  have hfM : ∀ i, Finite ↥(M i) := fun i =>
    Nat.finite_of_card_ne_zero (by rw [hcard i]; exact hr.ne_zero)
  have hfz : Finite ↥(zpowers z) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hz]; exact hr.ne_zero)
  have hfc : Finite ↥(zpowers c) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hc]; exact hr.ne_zero)
  obtain ⟨i, hiz, hic⟩ : ∃ i, M i ≠ zpowers z ∧ M i ≠ zpowers c := by
    by_contra hno
    push Not at hno
    have h : ∀ j, M j = zpowers z ∨ M j = zpowers c := fun j => by
      by_cases hj : M j = zpowers z
      · exact Or.inl hj
      · exact Or.inr (hno j hj)
    rcases h 0 with h0 | h0 <;> rcases h 1 with h1 | h1 <;> rcases h 2 with h2 | h2 <;>
      first
      | exact hdist 0 1 (by decide) (h0.trans h1.symm)
      | exact hdist 0 2 (by decide) (h0.trans h2.symm)
      | exact hdist 1 2 (by decide) (h1.trans h2.symm)
  obtain ⟨x, hxM, hx1⟩ : ∃ x ∈ M i, x ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : M i = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hno
    have := hcard i
    rw [hbot, Subgroup.card_bot] at this
    exact hr.one_lt.ne this
  obtain ⟨u, v, hxuv⟩ := exists_zpow_mul_zpow_of_mem_sup hzc (hM i hxM)
  obtain ⟨a, ha⟩ := exists_nat_pow_eq_zpow hr.pos hz u
  obtain ⟨b, hb⟩ := exists_nat_pow_eq_zpow hr.pos hc v
  have hxab : x = z ^ a * c ^ b := by rw [hxuv, ha, hb]
  have hzr : z ^ r = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hcr : c ^ r = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hxr : x ^ r = 1 := by
    rw [hxab, (hzc.pow_pow a b).mul_pow, ← pow_mul, mul_comm a r, pow_mul, hzr, one_pow,
      ← pow_mul, mul_comm b r, pow_mul, hcr, one_pow, one_mul]
  have hxord : orderOf x = r := orderOf_eq_prime hxr hx1
  have hMi : zpowers x = M i :=
    haveI := hfM i
    Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hxM) (by rw [Nat.card_zpowers, hxord, hcard i])
  have hza : ¬ r ∣ a := by
    intro hra
    obtain ⟨k, rfl⟩ := hra
    have hz1 : z ^ (r * k) = 1 := by rw [pow_mul, hzr, one_pow]
    have hxc : x ∈ zpowers c := by
      rw [hxab, hz1, one_mul]
      exact Subgroup.pow_mem _ (mem_zpowers c) b
    have : zpowers x = zpowers c :=
      Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hxc) (by
        rw [Nat.card_zpowers, Nat.card_zpowers, hc, hxord])
    exact hic (hMi.symm.trans this)
  have hzb : ¬ r ∣ b := by
    intro hrb
    obtain ⟨k, rfl⟩ := hrb
    have hc1 : c ^ (r * k) = 1 := by rw [pow_mul, hcr, one_pow]
    have hxz : x ∈ zpowers z := by
      rw [hxab, hc1, mul_one]
      exact Subgroup.pow_mem _ (mem_zpowers z) a
    have : zpowers x = zpowers z :=
      Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hxz) (by
        rw [Nat.card_zpowers, Nat.card_zpowers, hz, hxord])
    exact hiz (hMi.symm.trans this)
  refine ⟨a, b, hza, hzb, hxab ▸ hx1, ?_⟩
  rw [← hxab]
  exact hP i x hxM hx1

end Abstract

section ModelPlane

@[expose] def LongTorusClosing {K : Type} [Field K] (σ : K →+* K) : Prop :=
  ∀ H : Subgroup (twistedGroup σ), longSub 6 (hexGroup (twistedX σ)) ≤ H → (⨆ i, hHat σ i) ≤ H →
    (∃ y ∈ H, y ∉ Subgroup.normalizer (longSub 6 (hexGroup (twistedX σ)) : Set (twistedGroup σ))) →
      H = ⊤

theorem center_twistedGroup_eq_bot {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hK2 : ringChar K ≠ 2) {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3)
    (hσq : ∀ c, σ c = c ^ q) : Subgroup.center (twistedGroup σ.toRingHom) = ⊥ := by
  have hcenY := center_graphFixedRootGroup_eq_bot (t := TwistTag.D4) (K := K) (σ := σ.toRingHom) σ.surjective
  let ε₁ := twistedEquivRoot σ hK2 hq hK hσq
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  have h1 : ε₁ g ∈ Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨w, rfl⟩ := ε₁.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hg w]
  rw [hcenY, Subgroup.mem_bot] at h1
  exact ε₁.injective (h1.trans (map_one ε₁).symm)

set_option maxHeartbeats 1600000 in
theorem exists_plane_cenGen_top {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hClose : LongTorusClosing σ.toRingHom) {r : ℕ}
    (hr : r.Prime) (hr3 : r ≠ 3) (hrd : r ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) :
    ∃ E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      CFSG.IsElementaryAbelian r ↥E ∧ Nat.card E = r ^ 2 ∧
        Subgroup.closure (cenGen E) = ⊤ := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact r.Prime := ⟨hr⟩
  have hK3 : Nat.card K = ℓ ^ (f * 3) := by rw [hK, pow_mul]
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega) hK3
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have hq2 : 2 ≤ ℓ ^ f := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := hσ
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c :=
    sigma_three_of_card (σ := σ.toRingHom) hK hσ'
  have hcen := center_twistedGroup_eq_bot σ hK2 hq2 hK hσ
  obtain ⟨t, c, hnorm, htord, hzord, hcord, hcL, hLz, hZ3, hCc, hperf⟩ :=
    exists_explicit_plane (σ := σ.toRingHom) hσ3 hcen hq2 hK hσ' hr hr3 hrd
  have hr3' : ¬ r ∣ 3 := fun h => hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h)
  have hr5 : 3 < r := by
    have h2 : r ≠ 2 := odd_of_dvd_phi3 hr hrd
    have := hr.two_le
    omega
  have hzc : Commute (slShort σ.toRingHom hσ3 (HSL t)) c := (hLz c hcL).symm
  have hnot : c ∉ zpowers (slShort σ.toRingHom hσ3 (HSL t)) := by
    intro hc
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc
    have hcent : ∀ l ∈ longSub 6 (hexGroup (twistedX σ.toRingHom)), c * l = l * c := by
      intro l hl
      rw [← hk]
      exact ((Commute.zpow_right (show Commute l _ from hLz l hl) k).eq).symm
    have h3 : c ^ 3 = 1 := hZ3 c hcL hcent
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hcord] at this
    exact hr3' this
  obtain ⟨E', hzE, hcE, hEp, hEcard, hEmin⟩ := exists_plane_of_commute hzord hcord hzc hnot
  set z := slShort σ.toRingHom hσ3 (HSL t) with hz
  let E₀ : Subgroup (twistedGroup σ.toRingHom) := zpowers z ⊔ zpowers c
  have hzE0 : z ∈ E₀ := Subgroup.mem_sup_left (mem_zpowers z)
  have hcE0 : c ∈ E₀ := Subgroup.mem_sup_right (mem_zpowers c)
  have hE'eq : E' = E₀ :=
    le_antisymm (hEmin E₀ hzE0 hcE0) (sup_le (zpowers_le.2 hzE) (zpowers_le.2 hcE))
  have hzpow : z ^ r = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
  have hcpow : c ^ r = 1 := by rw [← hcord]; exact pow_orderOf_eq_one c
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzord
    exact hr.one_lt.ne hzord
  have : IsElementaryAbelian r (zpowers z) := IsElementaryAbelian.zpowers_of_pow_eq_one hzpow
  have : IsElementaryAbelian r (zpowers c) := IsElementaryAbelian.zpowers_of_pow_eq_one hcpow
  have hCE : zpowers c ≤ Subgroup.centralizer (zpowers z : Set (twistedGroup σ.toRingHom)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (hzc.zpow_zpow i j).eq
  have hE0ab : IsElementaryAbelian r ↥E₀ := IsElementaryAbelian.sup_of_le_centralizer hCE
  have hE0card : Nat.card E₀ = r ^ 2 := hE'eq ▸ hEcard
  let ε₁ := twistedEquivRoot σ hK2 hq2 hK hσ
  let E_Y : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := E₀.map ε₁.toMonoidHom
  have hEYab : IsElementaryAbelian r ↥E_Y := IsElementaryAbelian.map ε₁.toMonoidHom
  have hEYcard : Nat.card E_Y = r ^ 2 := by
    rw [Subgroup.card_map_of_injective ε₁.injective]
    exact hE0card
  have hpd : (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (1 : ℤ) * ((ℓ ^ f : ℕ) : ℤ) + 1 := by
    have := Int.natCast_dvd_natCast.2 hrd
    push_cast at this ⊢
    simpa using this
  obtain ⟨M, hMle, hMcard, hMdist, hMsing⟩ :=
    exists_four_singular_lines hℓ hf K hK σ hσ (ε := 1) (Or.inl rfl) hr hr5 hpd E_Y hEYab hEYcard
  let M' : Fin 4 → Subgroup (twistedGroup σ.toRingHom) := fun i => (M i).map ε₁.symm.toMonoidHom
  have hM'le : ∀ i, M' i ≤ zpowers z ⊔ zpowers c := by
    intro i y hy
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨e, he, hme⟩ := Subgroup.mem_map.1 (hMle i hm)
    have : ε₁.symm.toMonoidHom m = e := by
      rw [← hme]
      exact ε₁.symm_apply_apply e
    rw [this]
    exact he
  have hM'card : ∀ i, Nat.card (M' i) = r := fun i => by
    rw [Subgroup.card_map_of_injective ε₁.symm.injective]
    exact hMcard i
  have hM'dist : ∀ i j, i ≠ j → M' i ≠ M' j := fun i j hij h =>
    hMdist i j hij (Subgroup.map_injective ε₁.symm.injective h)
  have hM'sing : ∀ i, ∀ x ∈ M' i, x ≠ 1 → CenDerivedPerfect x := by
    intro i x hx hx1
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hx
    have hm1 : m ≠ 1 := by
      rintro rfl
      exact hx1 (map_one _)
    exact (hMsing i m hm hm1).map ε₁.symm
  obtain ⟨a, b, ha, hb, hx1, hx2⟩ := exists_good_generator hzord hcord hzc M' hM'le hM'card
    hM'dist CenDerivedPerfect hM'sing
  obtain ⟨y, hyC, hyN⟩ := exists_mem_centralizer_not_mem_normalizer hr hr3'
    (longSub 6 (hexGroup (twistedX σ.toRingHom))) z c hzord hcord hLz hcL hZ3 hCc hperf ha hb
    hx2.1 hx2.2
  have hx2E : z ^ a * c ^ b ∈ E₀ :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ hzE0 a) (Subgroup.pow_mem _ hcE0 b)
  have hyH : y ∈ Subgroup.closure (cenGen E₀) :=
    Subgroup.subset_closure ⟨z ^ a * c ^ b, hx2E, hx1, Subgroup.mem_centralizer_singleton_iff.1 hyC⟩
  have hLH : longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ Subgroup.closure (cenGen E₀) :=
    fun l hl => Subgroup.subset_closure ⟨z, hzE0, hz1, hLz l hl⟩
  have hzHat : z ∈ hHat σ.toRingHom (ng 1) := slShort_HSL_mem_hHat hσ3 t
  have hTH : (⨆ i, hHat σ.toRingHom i) ≤ Subgroup.closure (cenGen E₀) :=
    iSup_le fun i h hh => Subgroup.subset_closure ⟨z, hzE0, hz1, (hHat_commute σ.toRingHom hh hzHat).eq⟩
  have htop : Subgroup.closure (cenGen E₀) = ⊤ := hClose _ hLH hTH ⟨y, hyH, hyN⟩
  refine ⟨E_Y, hEYab, hEYcard, ?_⟩
  refine closure_cenGen_eq_top_of_map ε₁.symm E_Y ?_
  have hmap : E_Y.map ε₁.symm.toMonoidHom = E₀ := by
    ext x
    constructor
    · intro hx
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hx
      obtain ⟨e, he, hme⟩ := Subgroup.mem_map.1 hm
      have : ε₁.symm.toMonoidHom m = e := by
        rw [← hme]
        exact ε₁.symm_apply_apply e
      rw [this]
      exact he
    · intro hx
      refine Subgroup.mem_map.2 ⟨ε₁.toMonoidHom x, Subgroup.mem_map_of_mem _ hx, ?_⟩
      exact ε₁.symm_apply_apply x
  rw [hmap]
  exact htop

theorem closure_cenGen_eq_top_of_conj_plane {G : Type*} [Group G] [Finite G] {p e : ℕ}
    [Fact p.Prime] (hshape : SylowShape p 2 e G) (E₀ : Subgroup G) (hE₀p : ∀ x ∈ E₀, x ^ p = 1)
    (hE₀c : Nat.card E₀ = p ^ 2) (htop : Subgroup.closure (cenGen E₀) = ⊤) (F : Subgroup G)
    (hFp : ∀ x ∈ F, x ^ p = 1) (hFc : Nat.card F = p ^ 2) :
    Subgroup.closure (cenGen F) = ⊤ := by
  have hE₀p' : IsPGroup p E₀ := IsPGroup.of_card (n := 2) hE₀c
  obtain ⟨S, hS⟩ := hE₀p'.exists_le_sylow
  obtain ⟨g, hg⟩ := plane_conj S (T := (S : Subgroup G)) le_rfl (E := E₀)
    (eq_of_pow_eq_one_of_sylowShape hshape S hS hE₀c hE₀p) hE₀c hFp hFc
  rw [hg, closure_cenGen_cj, htop, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]

set_option maxHeartbeats 1600000 in
theorem phi3_cenGen_top {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hClose : LongTorusClosing σ.toRingHom) {r : ℕ}
    (hr : r.Prime) (hr3 : r ≠ 3) (hrd : r ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1)
    (F : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hF : CFSG.IsElementaryAbelian r ↥F) (hFcard : Nat.card F = r ^ 2) :
    Subgroup.closure (cenGen F) = ⊤ := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨E, hEab, hEcard, hEtop⟩ := exists_plane_cenGen_top hℓ hℓ2 hf hK σ hσ hClose hr hr3 hrd
  have hr5 : 5 ≤ r := by
    have h2 : r ≠ 2 := odd_of_dvd_phi3 hr hrd
    have h4 : r ≠ 4 := by rintro rfl; exact absurd hr (by decide)
    have := hr.two_le
    omega
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hshape := CFSG.RankThree.PartOne.K128.sylowShape_D4 (ℓ := ℓ) hf K hK σ hσ (m := 3)
    (by decide) hr hr5 hrd
  exact closure_cenGen_eq_top_of_conj_plane hshape E
    (fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx) hEcard hEtop F
    (fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx) hFcard

end ModelPlane

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
