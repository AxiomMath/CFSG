module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step34
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3BR
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped Pointwise

namespace G2

variable {K : Type} [Field K] [CharP K 2]

theorem ringEquiv_apply_apply [Finite K] (hK : Nat.card K = 4) (σ : K ≃+* K) (t : K) :
    σ (σ t) = t := by
  by_cases h0 : t = 0
  · rw [h0, map_zero, map_zero]
  by_cases h1 : t = 1
  · rw [h1, map_one, map_one]
  have ht := sq_add_self_add_one_of_ne hK h0 h1
  have hst : σ t ^ 2 + σ t + 1 = 0 := by
    have h := congrArg σ ht
    rwa [map_add, map_add, map_pow, map_one, map_zero] at h
  have hprod : (σ t + t) * (σ t + t + 1) = 0 := by
    linear_combination (norm := char2_ring) hst + ht
  rcases mul_eq_zero.mp hprod with h | h
  · have h' : σ t = t := by linear_combination (norm := char2_ring) h
    rw [h', h']
  · have h' : σ t = t + 1 := by linear_combination (norm := char2_ring) h
    rw [h', map_add, map_one, h']
    linear_combination (norm := char2_ring)

theorem exists_conj_eq_of_pow
    [Finite K] (hK : Nat.card K = 4) {α : MulAut ↥(adjointGroup .G2 K)} {k : ℕ}
    (hα : α ^ 3 ^ k = 1) : ∃ c : ↥(adjointGroup .G2 K), α = MulAut.conj c := by
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    even_G2_exact_automorphism_normal_form (f := 2) le_rfl K (by rw [hK]; norm_num)
  have h2 : Θ α ^ 2 = 1 := RingEquiv.ext fun t => by exact ringEquiv_apply_apply hK (Θ α) t
  have h3 : Θ α ^ 3 ^ k = 1 := by rw [← map_pow, hα, map_one]
  have h1 : Θ α = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨h2, h3⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right _ (by norm_num)), pow_one] at h
  have hmem : α ∈ Θ.ker := MonoidHom.mem_ker.mpr h1
  rw [hker] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc.symm⟩

end G2

section Y1

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G} {x : G}
  {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U : Subgroup G}

theorem isPGroup_zpowers_of_pow_three {M : Type*} [Group M] {k : M} {n : ℕ} (hk : k ^ 3 ^ n = 1) :
    IsPGroup 3 (zpowers k) := by
  rintro ⟨_, hy⟩
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
  refine ⟨n, Subtype.ext ?_⟩
  change (k ^ i) ^ 3 ^ n = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]

omit [Finite G] in
theorem inv_mul_mul_eq_of_comm {a b : G} (h : b * a = a * b) : a⁻¹ * b * a = b := by
  rw [mul_assoc, h, inv_mul_cancel_left]

theorem exists_y₁
    (hSz : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y) :
    ∃ y₁ : G, y₁ ∈ centralizer (A : Set G) ∧ y₁ ∈ normalizer (R : Set G) ∧
      (∀ r ∈ R, r ≠ 1 → y₁⁻¹ * r * y₁ ≠ r) ∧ (∃ k : ℕ, y₁ ^ 3 ^ k = 1) ∧
      y₁ ∈ normalizer (E : Set G) ∧ y₁ ∈ normalizer (P : Set G) := by
  have hS := hSz.setting
  have hFr := hS.frame
  obtain ⟨K, _, _, _, hK, f, hM⟩ := exists_sec3Model hS
  have hNA : normalizer (R : Set G) ≤ normalizer (A : Set G) := by
    have h := AS76b.Lemma36.normalizer_le hS.base.hyp31 hS.sylowR 1
    rwa [rightConjugate_one, rightConjugate_one] at h
  have hRA : R ≤ centralizer (A : Set G) := hS.sylowR.le
  have hEAR : E ≤ A ⊔ R := hFr.E_le.trans (sup_le_sup_right hS.le _)
  obtain ⟨hyB, hyR⟩ := hSz.y_mem
  have hyA := hNA hyR
  obtain ⟨k, hk⟩ := hSz.y_three
  have hα : hM.act ⟨y, hyA⟩ ^ 3 ^ k = 1 := by
    rw [← map_pow]
    have h1 : (⟨y, hyA⟩ : normalizer (A : Set G)) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [h1, map_one]
  obtain ⟨c, hc⟩ := G2.exists_conj_eq_of_pow hK hα
  have hfcA : f c ∈ A := by
    rw [← hM.range_eq]
    exact ⟨c, rfl⟩
  have hy₁A : y * (f c)⁻¹ ∈ centralizer (A : Set G) := by
    have h1 : hM.act ⟨f c, le_normalizer hfcA⟩ = hM.act ⟨y, hyA⟩ := by
      rw [hM.act_of_mem hfcA, hc]
      congr 1
      exact hM.equivA.symm_apply_eq.mpr (Subtype.ext rfl)
    have h2 : hM.act (⟨y, hyA⟩ * ⟨f c, le_normalizer hfcA⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    exact (hM.isActionHom_act.eq_one_iff _).mp h2
  have hfcR : f c ∈ centralizer (R : Set G) :=
    mem_centralizer_iff.mpr fun r hr => (mem_centralizer_iff.mp (hRA hr) (f c) hfcA).symm
  have hy₁R : y * (f c)⁻¹ ∈ normalizer (R : Set G) :=
    mul_mem hyR (inv_mem (centralizer_le_normalizer _ hfcR))
  have hAK : ∀ v ∈ A, v ∈ centralizer (A : Set G) → v = 1 := fun v hv hvc => by
    have h1 : (⟨v, hv⟩ : ↥A) ∈ center ↥A := mem_center_iff.mpr fun a =>
      Subtype.ext (mem_centralizer_iff.mp hvc a a.2)
    rw [hS.center_eq, mem_bot] at h1
    exact congrArg Subtype.val h1
  have hy₁3 : (y * (f c)⁻¹) ^ 3 ^ k = 1 := by
    have hcomm : Commute (y * (f c)⁻¹) (f c) :=
      (mem_centralizer_iff.mp hy₁A (f c) hfcA).symm
    have h1 := hcomm.mul_pow (3 ^ k)
    rw [inv_mul_cancel_right, hk] at h1
    have h2 : (y * (f c)⁻¹) ^ 3 ^ k = ((f c) ^ 3 ^ k)⁻¹ := eq_inv_of_mul_eq_one_left h1.symm
    have h3 : (y * (f c)⁻¹) ^ 3 ^ k ∈ A := by
      rw [h2]
      exact inv_mem (pow_mem hfcA _)
    exact hAK _ h3 (pow_mem hy₁A _)
  have hy₁E : y * (f c)⁻¹ ∈ normalizer (E : Set G) := by
    rw [eq_inf_sup_of_le_sup hRA hFr.R_le_E hEAR]
    exact mem_normalizer_sup (centralizer_le_normalizer _
      (centralizer_le (by exact_mod_cast (inf_le_right : E ⊓ A ≤ A)) hy₁A)) hy₁R
  have hxA : x ∈ A := hS.le (Sec3.mem_centerIn_A₁ hS.toSec3Pre).1
  have hy₁x : y * (f c)⁻¹ ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hy₁A x hxA).symm
  have hy₁P : y * (f c)⁻¹ ∈ normalizer (P : Set G) := by
    rw [hSz.P_eq]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      (mem_normalizer_inf (Sec3.centralizer_le_normalizer_sec3B A₁ x hy₁x)
        (mem_normalizer_normalizer hy₁E))
  refine ⟨y * (f c)⁻¹, hy₁A, hy₁R, fun r hr hr1 => ?_, ⟨k, hy₁3⟩, hy₁E, hy₁P⟩
  have hs : y⁻¹ * r * y ∈ R := by
    have h := (mem_normalizer_iff.mp (inv_mem hyR) r).mp hr
    simpa using h
  have hcs : f c * (y⁻¹ * r * y) = (y⁻¹ * r * y) * f c :=
    mem_centralizer_iff.mp (hRA hs) (f c) hfcA
  rw [show (y * (f c)⁻¹)⁻¹ * r * (y * (f c)⁻¹) = f c * (y⁻¹ * r * y) * (f c)⁻¹ by group, hcs,
    mul_inv_cancel_right]
  exact hSz.y_trans r hr hr1

theorem inf_centralizer_le (hSz : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y) {y₁ : G}
    (hy₁A : y₁ ∈ centralizer (A : Set G)) (hy₁R : y₁ ∈ normalizer (R : Set G))
    (hy₁t : ∀ r ∈ R, r ≠ 1 → y₁⁻¹ * r * y₁ ≠ r) :
    P ⊓ centralizer ({y₁} : Set G) ≤ E ⊓ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hSz.setting
  have hFr := hS.frame
  have hRA : R ≤ centralizer (A : Set G) := hS.sylowR.le
  have hEAR : E ≤ A ⊔ R := hFr.E_le.trans (sup_le_sup_right hS.le _)
  have hEA₁ : E ⊓ A = E ⊓ A₁ := (Sec3.frame_inf_A₁ hS).1
  have hEP : E ≤ P := hSz.P_cE ▸ inf_le_left
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hFr.elemE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsq : ∀ a ∈ E, a ^ 2 = 1 := fun a ha => hFr.elemE.2 a ha
  have hτR : ∀ r ∈ R, y₁⁻¹ * r * y₁ ∈ R := fun r hr => by
    have h := (mem_normalizer_iff.mp (inv_mem hy₁R) r).mp hr
    simpa using h
  rintro p ⟨hp, hpy⟩
  have hpy' : p * y₁ = y₁ * p := mem_centralizer_singleton_iff.mp hpy
  have hc : ∀ r ∈ R, p⁻¹ * r * p * r⁻¹ ∈ E ⊓ A := fun r hr => by
    have h := hSz.P_comm p⁻¹ (inv_mem hp) r (hEP (hFr.R_le_E hr))
    rw [inv_inv] at h
    rw [hEA₁]
    exact h
  have hpτ : ∀ w : G, p⁻¹ * (y₁⁻¹ * w * y₁) * p = y₁⁻¹ * (p⁻¹ * w * p) * y₁ := fun w => by
    calc p⁻¹ * (y₁⁻¹ * w * y₁) * p = (y₁ * p)⁻¹ * w * (y₁ * p) := by group
      _ = (p * y₁)⁻¹ * w * (p * y₁) := by rw [hpy']
      _ = y₁⁻¹ * (p⁻¹ * w * p) * y₁ := by group
  have hpR : R ≤ centralizer ({p} : Set G) := by
    have hR1 : R ≠ ⊥ := by
      intro h
      have h4 := hFr.cardR
      rw [h, Subgroup.card_bot] at h4
      omega
    obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR1
    have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
    obtain ⟨t, ht⟩ : ∃ t, t = y₁⁻¹ * r * y₁ := ⟨_, rfl⟩
    have htR : t ∈ R := ht ▸ hτR r hr
    have htr : t ≠ r := ht ▸ hy₁t r hr hr1'
    obtain ⟨c, hcdef⟩ : ∃ c, c = p⁻¹ * r * p * r⁻¹ := ⟨_, rfl⟩
    have hcr : c ∈ E ⊓ A := hcdef ▸ hc r hr
    have hct : p⁻¹ * t * p * t⁻¹ = c := by
      have h1 : p⁻¹ * t * p * t⁻¹ = y₁⁻¹ * (p⁻¹ * r * p * r⁻¹) * y₁ := by
        rw [ht, hpτ r]
        group
      rw [h1, ← hcdef]
      exact inv_mul_mul_eq_of_comm (mem_centralizer_iff.mp hy₁A _ hcr.2)
    obtain ⟨s, hs⟩ : ∃ s, s = r * t := ⟨_, rfl⟩
    have hsR : s ∈ R := hs ▸ mul_mem hr htR
    have hs1 : s ≠ 1 := by
      intro h
      apply htr
      have h1 : t = r⁻¹ := eq_inv_of_mul_eq_one_right (hs ▸ h)
      have h2 : r⁻¹ = r := by
        rw [inv_eq_iff_mul_eq_one, ← pow_two]
        exact hsq r (hFr.R_le_E hr)
      rw [h1, h2]
    have hps : p⁻¹ * s * p = s := by
      have hcE : c ∈ E := hcr.1
      have e1 : p⁻¹ * r * p = c * r := by rw [hcdef]; group
      have e2 : p⁻¹ * t * p = c * t := by rw [← hct]; group
      have hcc : c * c = 1 := by rw [← pow_two]; exact hsq c hcE
      calc p⁻¹ * s * p = (p⁻¹ * r * p) * (p⁻¹ * t * p) := by rw [hs]; group
        _ = c * (r * c) * t := by rw [e1, e2]; group
        _ = c * (c * r) * t := by rw [hcomm r (hFr.R_le_E hr) c hcE]
        _ = (c * c) * (r * t) := by group
        _ = s := by rw [hcc, one_mul, hs]
    have hsC : s ∈ R ⊓ centralizer ({p} : Set G) := by
      refine ⟨hsR, mem_centralizer_singleton_iff.mpr ?_⟩
      calc s * p = p * (p⁻¹ * s * p) := by group
        _ = p * s := by rw [hps]
    have hτs : y₁⁻¹ * s * y₁ ∈ R ⊓ centralizer ({p} : Set G) := by
      refine ⟨hτR s hsR, mem_centralizer_singleton_iff.mpr ?_⟩
      calc y₁⁻¹ * s * y₁ * p = p * (p⁻¹ * (y₁⁻¹ * s * y₁) * p) := by group
        _ = p * (y₁⁻¹ * s * y₁) := by rw [hpτ s, hps]
    have hτs1 : y₁⁻¹ * s * y₁ ≠ s := hy₁t s hsR hs1
    have hτs1' : y₁⁻¹ * s * y₁ ≠ 1 := by
      intro h
      apply hs1
      rw [show s = y₁ * (y₁⁻¹ * s * y₁) * y₁⁻¹ by group, h, mul_one, mul_inv_cancel]
    have hdvd : Nat.card ↥(R ⊓ centralizer ({p} : Set G)) ∣ 4 :=
      hFr.cardR ▸ Subgroup.card_dvd_of_le inf_le_left
    have h4 : Nat.card ↥(R ⊓ centralizer ({p} : Set G)) = 4 := by
      have hmem : Nat.card ↥(R ⊓ centralizer ({p} : Set G)) ∈ Nat.divisors 4 :=
        Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
      rw [hdiv] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h
      · exfalso
        rw [Subgroup.card_eq_one] at h
        rw [h, mem_bot] at hsC
        exact hs1 hsC
      · exfalso
        have hs2 : orderOf s = 2 := orderOf_eq_prime (hsq s (hFr.R_le_E hsR)) hs1
        have hz : zpowers s = R ⊓ centralizer ({p} : Set G) :=
          eq_of_le_of_card_ge (zpowers_le.mpr hsC) (by rw [h, Nat.card_zpowers, hs2])
        have h1 : y₁⁻¹ * s * y₁ ∈ zpowers s := hz ▸ hτs
        exact hτs1 (Sec3.eq_of_mem_zpowers hs2 h1 hτs1')
      · exact h
    have hCR : R ⊓ centralizer ({p} : Set G) = R :=
      eq_of_le_of_card_ge inf_le_left (by rw [h4, hFr.cardR])
    rw [← hCR]
    exact inf_le_right
  have hEeq := eq_inf_sup_of_le_sup hRA hFr.R_le_E hEAR
  have hpcA : E ⊓ A ≤ centralizer ({p} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hSz.P_cent hp) a (hEA₁ ▸ ha))
  have hEp : E ≤ centralizer ({p} : Set G) := by
    rw [hEeq]
    exact sup_le hpcA hpR
  have hpE : p ∈ E := by
    have h1 : p ∈ P ⊓ centralizer (E : Set G) :=
      ⟨hp, mem_centralizer_iff.mpr fun e he => (mem_centralizer_singleton_iff.mp (hEp he))⟩
    rwa [hSz.P_cE] at h1
  obtain ⟨a, ha, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hFr.R_le_E hEAR hpE
  have hya : y₁⁻¹ * a * y₁ = a := inv_mul_mul_eq_of_comm (mem_centralizer_iff.mp hy₁A a ha.2)
  have hyr : y₁⁻¹ * r * y₁ = r := by
    have h1 : y₁⁻¹ * (a * r) * y₁ = a * r := inv_mul_mul_eq_of_comm hpy'
    rw [show y₁⁻¹ * (a * r) * y₁ = (y₁⁻¹ * a * y₁) * (y₁⁻¹ * r * y₁) by group, hya] at h1
    exact mul_left_cancel h1
  by_cases hr1 : r = 1
  · rw [hr1, mul_one]
    exact ha
  · exact absurd hyr (hy₁t r hr hr1)

theorem R_inf_centralizer_P (hSz : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y) :
    R ⊓ centralizer (P : Set G) = ⊥ := by
  have hS := hSz.setting
  have hFr := hS.frame
  have hKte := AS76b.tightlyEmbedded_centralizer hS.base.hyp.standard
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hFr.elemE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hPX := P_le_X hSz
  have hRA1 := Sec3.R_inf_A hS
  have hEA1 : E ⊓ A₁ ≠ ⊥ := by
    intro h
    have h16 := (Sec3.frame_inf_A₁ hS).2.2.2.2.1
    rw [h, Subgroup.card_bot] at h16
    omega
  obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hEA1
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hR1 : R ≠ ⊥ := by
    intro h
    have h4 := hFr.cardR
    rw [h, Subgroup.card_bot] at h4
    omega
  obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR1
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have heA : a * r ∉ A₁ := by
    intro h
    apply hr1'
    have h1 : r ∈ R ⊓ A := ⟨hr, hS.le (by simpa using mul_mem (inv_mem (mem_inf.mp ha).2) h)⟩
    rwa [hRA1, mem_bot] at h1
  obtain ⟨p, hp, hep⟩ := hSz.P_cover (a * r) (mul_mem (mem_inf.mp ha).1 (hFr.R_le_E hr)) heA
  have hRp : rightConjugate R p ∈ pointsIn R E := by
    refine ⟨fun v hv => ?_, p, rfl⟩
    rw [mem_rightConjugate_iff] at hv
    have h1 := (mem_normalizer_iff.mp (inv_mem (hPX hp).1) _).mp (hFr.R_le_E hv)
    simpa [mul_assoc] using h1
  have hRR : R ∈ pointsIn R E := ⟨hFr.R_le_E, 1, by rw [rightConjugate_one]⟩
  have hne : R ≠ rightConjugate R p := by
    intro h
    apply ha1'
    have h1 : a * r ∈ R := h ▸ hep
    have h2 : a ∈ R ⊓ A := ⟨by simpa using mul_mem h1 (inv_mem hr), hS.le (mem_inf.mp ha).2⟩
    rwa [hRA1, mem_bot] at h2
  have hinf := inf_eq_bot_of_mem_pointsIn hKte hS.sylowR hcomm hRR hRp hne
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwR, hwc⟩ := mem_inf.mp hw
  have hw : w ∈ R ⊓ rightConjugate R p := by
    refine mem_inf.mpr ⟨hwR, ?_⟩
    rw [mem_rightConjugate_iff]
    have h1 : p * w = w * p := mem_centralizer_iff.mp hwc p hp
    rw [h1, mul_inv_cancel_right]
    exact hwR
  rwa [hinf] at hw

end Y1

section DP

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G} {x : G}
  {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U : Subgroup G}

theorem P_le_centralizer_D
    (hD : Sec3D G A A₁ R g E F x Zs P T Q B₀ z y D J U) : P ≤ centralizer (D : Set G) := by
  have hSz := hD.suz
  obtain ⟨y₁, hy₁A, hy₁R, hy₁t, ⟨k, hk⟩, -, hy₁P⟩ := exists_y₁ hSz
  obtain ⟨hDxA, -, -⟩ := sec3D_model hD
  have hDA : D ≤ A := (le_sup_left.trans hDxA).trans inf_le_left
  have hPD := P_le_normalizer_D hD
  have hY3 := isPGroup_zpowers_of_pow_three hk
  have hYP : zpowers y₁ ≤ normalizer (P : Set G) := zpowers_le.mpr hy₁P
  have hcop : Nat.Coprime 3 (Nat.card P) := by
    rw [hSz.P_card]
    norm_num
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 3
    Nat.prime_three (zpowers y₁) P hY3 hYP hcop
  have hYD : zpowers y₁ ≤ centralizer (D : Set G) :=
    zpowers_le.mpr (centralizer_le (by exact_mod_cast hDA) hy₁A)
  have hDP : ⁅D, P⁆ ≤ D := by
    rw [commutator_le]
    intro d hd p hp
    rw [commutatorElement_def, show d * p * d⁻¹ * p⁻¹ = d * (p * d⁻¹ * p⁻¹) by group]
    exact mul_mem hd ((mem_normalizer_iff.mp (hPD hp) d⁻¹).mp (inv_mem hd))
  have h1 : ⁅⁅zpowers y₁, D⁆, P⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer.mpr hYD, commutator_bot_left]
  have h2 : ⁅⁅D, P⁆, zpowers y₁⁆ = ⊥ := by
    refine le_bot_iff.mp ((commutator_mono hDP le_rfl).trans (le_of_eq ?_))
    rw [commutator_comm, commutator_eq_bot_iff_le_centralizer.mpr hYD]
  have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
  have hC : P ⊓ centralizer ((zpowers y₁ : Subgroup G) : Set G) ≤ centralizer (D : Set G) := by
    rw [Sec3.centralizer_zpowers]
    refine (inf_centralizer_le hSz hy₁A hy₁R hy₁t).trans ?_
    rw [hD.center_D]
    exact fun w hw => hw.2
  rw [← hfac]
  exact sup_le (commutator_eq_bot_iff_le_centralizer.mp h3) hC

theorem step35_of
    :
    ∀ (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G) (E F : Subgroup G) (x : G)
      (Zs P T Q B₀ : Subgroup G) (z y : G) (D J U : Subgroup G),
      Sec3D G A A₁ R g E F x Zs P T Q B₀ z y D J U →
        D = pCoreOf 2 (centralizer (P : Set G)) ∧ IsSylowOf 2 D (centralizer (P : Set G)) := by
  intro G _ _ A A₁ R g E F x Zs P T Q B₀ z y D J U hD
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSz := hD.suz
  have hS := hSz.setting
  have hFr := hS.frame
  obtain ⟨-, -, hmem, -⟩ := DR_facts hD
  obtain ⟨hDxA, -, -⟩ := sec3D_model hD
  have hDA : D ≤ A := (le_sup_left.trans hDxA).trans inf_le_left
  have hRA : R ≤ centralizer (A : Set G) := hS.sylowR.le
  have hDP : D ≤ centralizer (P : Set G) := le_centralizer_iff.mp (P_le_centralizer_D hD)
  have hRP1 := R_inf_centralizer_P hSz
  have hEP : E ≤ P := hSz.P_cE ▸ inf_le_left
  have hD2 : IsPGroup 2 D := hD.D_eq ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRD : R ≤ normalizer (D : Set G) := fun r hr => centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun d hd => mem_centralizer_iff.mp (hRA hr) d (hDA hd))
  have hCE : centralizer (P : Set G) ≤ centralizer (E : Set G) :=
    centralizer_le (by exact_mod_cast hEP)
  have hmax : ∀ W : Subgroup G, D ≤ W → W ≤ centralizer (P : Set G) → IsPGroup 2 W → W ≤ D := by
    intro W hDW hWP hW w hw
    obtain ⟨n, hn⟩ := hW ⟨w, hw⟩
    have hwDR := hmem w (hCE (hWP hw)) n (by simpa using congrArg Subtype.val hn)
    have hw' : w ∈ (D : Set G) * (R : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left D R hRD]
      exact hwDR
    obtain ⟨d, hd, r, hr, hdr⟩ := hw'
    have hdr : d * r = w := hdr
    have hrW : r ∈ W := by
      rw [show r = d⁻¹ * w by rw [← hdr, inv_mul_cancel_left]]
      exact mul_mem (inv_mem (hDW hd)) hw
    have hr1 : r = 1 := by
      have h1 : r ∈ R ⊓ centralizer (P : Set G) := ⟨hr, hWP hrW⟩
      rwa [hRP1, mem_bot] at h1
    rw [← hdr, hr1, mul_one]
    exact hd
  have hsyl : IsSylowOf 2 D (centralizer (P : Set G)) := by
    obtain ⟨S, hS'⟩ := (hD2.comap_subtype :
      IsPGroup 2 (D.subgroupOf (centralizer (P : Set G)))).exists_le_sylow
    have hDS : D ≤ (S : Subgroup ↥(centralizer (P : Set G))).map
        (centralizer (P : Set G)).subtype := fun d hd => ⟨⟨d, hDP hd⟩, hS' hd, rfl⟩
    exact ⟨S, le_antisymm (hmax _ hDS (map_subtype_le _) (S.isPGroup'.map _)) hDS⟩
  refine ⟨le_antisymm ?_ ?_, hsyl⟩
  ·
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hDP (fun w hw => ?_) hD2
    have hwE : w ∈ normalizer (E : Set G) := centralizer_le_normalizer _ (hCE hw)
    have hwR : w ∈ normalizer (R : Set G) := centralizer_le_normalizer _
      (centralizer_le (by exact_mod_cast hFr.R_le_E) (hCE hw))
    have hwA : w ∈ normalizer (A : Set G) := by
      have h := AS76b.Lemma36.normalizer_le hS.base.hyp31 hS.sylowR 1
      rw [rightConjugate_one, rightConjugate_one] at h
      exact h hwR
    have hwI : w ∈ normalizer
        ((A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G) : Subgroup G) : Set G) :=
      mem_normalizer_inf hwA (mem_normalizer_normalizer (mem_normalizer_inf hwE hwA))
    rw [hD.D_eq]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hwI
  ·
    have hO2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (centralizer (P : Set G))
    have hON := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (centralizer (P : Set G))
    have hsup : IsPGroup 2 ↥(D ⊔ pCoreOf 2 (centralizer (P : Set G))) :=
      hD2.to_sup_of_normal_right' hO2 (hDP.trans hON)
    exact le_sup_right.trans (hmax _ le_sup_left
      (sup_le hDP (CFSG.LieType.BorelTits.pCoreOf_le 2 _)) hsup)

end DP

end CFSG.ComponentClassification.AS81
