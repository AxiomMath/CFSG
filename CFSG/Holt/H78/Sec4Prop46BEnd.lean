module

public import CFSG.Holt.H78.Sec4Prop46BWit
public import CFSG.Holt.NotStar.Lemma213
public import CFSG.Holt.H78.TwoPoint
public import CFSG.Holt.H78.Sec4Bender
public import CFSG.Holt.H78.Sec4SEAutFix
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure
public import CFSG.Timmesfeld.Bridge.SchurNarrow

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise

section Normal

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] {α β : Ω}

theorem twoPointHom_mem_normalizer {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω)) :
    twoPointHom G Ω α β ⟨g, hg⟩ ∈
      Subgroup.normalizer (twoPointJ G Ω α β : Set (Equiv.Perm (holtDelta G Ω α β))) := by
  refine Subgroup.mem_normalizer_iff.mpr fun n => ⟨fun hn => conj_mem_twoPointJ hg hn,
    fun hn => ?_⟩
  have := conj_mem_twoPointJ (inv_mem hg) hn
  rwa [show (⟨g⁻¹, inv_mem hg⟩ : stabilizer G ({α, β} : Set Ω)) = (⟨g, hg⟩)⁻¹ from rfl, map_inv,
    inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
    mul_one] at this

theorem eq_one_of_isPGroup_of_odd {K : Subgroup G} (hK : Odd (Nat.card K)) {g : G} (hg : g ∈ K)
    {k : ℕ} (hgk : g ^ 2 ^ k = 1) : g = 1 := by
  have hodd : Odd (orderOf g) := hK.of_dvd_nat (K.orderOf_dvd_natCard hg)
  have hdvd : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hgk
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
    ((Nat.coprime_two_right.mpr hodd).pow_right k) hdvd)

end Normal

section YGroups

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β γ : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

namespace Prop46CaseB

variable (hC : Prop46CaseB G Ω α β γ v P)
include hC

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem conj_mem_caseBRad {k : G} (hkα : k • α = α) (hkβ : k • β = β) (hkγ : k • γ = γ) {g : G}
    (hg : g ∈ caseBRad G Ω α β ⟨γ, hC.mem_holtDelta⟩) :
    k * g * k⁻¹ ∈ caseBRad G Ω α β ⟨γ, hC.mem_holtDelta⟩ := by
  obtain ⟨hgP, hgα, hgβ, hgZ⟩ := mem_caseBRad.mp hg
  have hkP : k ∈ stabilizer G ({α, β} : Set Ω) := stabilizer_inf_le_stabilizer_pair α β
    (Subgroup.mem_inf.mpr ⟨mem_stabilizer_iff.mpr hkα, mem_stabilizer_iff.mpr hkβ⟩)
  have hP : k * g * k⁻¹ ∈ stabilizer G ({α, β} : Set Ω) := mul_mem (mul_mem hkP hgP) (inv_mem hkP)
  have hkα' : k⁻¹ • α = α := by rw [inv_smul_eq_iff, hkα]
  have hkβ' : k⁻¹ • β = β := by rw [inv_smul_eq_iff, hkβ]
  refine mem_caseBRad.mpr ⟨hP, by rw [mul_smul, mul_smul, hkα', hgα, hkα],
    by rw [mul_smul, mul_smul, hkβ', hgβ, hkβ], ?_⟩
  rw [show (⟨k * g * k⁻¹, hP⟩ : stabilizer G ({α, β} : Set Ω)) = ⟨k, hkP⟩ * ⟨g, hgP⟩ * ⟨k, hkP⟩⁻¹
    from rfl, map_mul, map_mul, map_inv]
  have hkγ' : twoPointHom G Ω α β ⟨k, hkP⟩ ⟨γ, hC.mem_holtDelta⟩ = ⟨γ, hC.mem_holtDelta⟩ :=
    Subtype.ext hkγ
  exact conj_mem_rootCenter_seRadical (twoPointHom_mem_normalizer hkP) hkγ' hgZ

theorem exists_Y (hS : Sec4Setting G Ω) {r : G} (hrv : Commute r v) (hr2 : r * r = 1) :
    ∃ Y : Subgroup G, Y ≤ caseBRad G Ω α β ⟨γ, hC.mem_holtDelta⟩ ∧ v ∈ Y ∧
      (∀ y ∈ Y, y * y = 1 ∧ Commute y v ∧ ∀ ω : Ω, v • ω = ω → y • ω = ω) ∧
      (∀ y ∈ Y, r * y * r⁻¹ ∈ Y) ∧
      ∀ z ∈ rootCenter (seRadical (twoPointJ G Ω α β) ⟨γ, hC.mem_holtDelta⟩),
        ∃ y ∈ Y, ∃ hyP : y ∈ stabilizer G ({α, β} : Set Ω), twoPointHom G Ω α β ⟨y, hyP⟩ = z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Φ := fixSet Ω (Subgroup.zpowers v) with hΦ
  set Kv := Subgroup.centralizer (Subgroup.zpowers v : Set G) ⊓ fixingSubgroup G (Φ : Set Ω)
    with hKv
  set Bv := Kv ⊓ caseBRad G Ω α β ⟨γ, hC.mem_holtDelta⟩ with hBv
  have hmemKv : ∀ {g : G}, g ∈ Kv ↔ Commute g v ∧ ∀ ω : Ω, v • ω = ω → g • ω = ω := fun {g} => by
    rw [hKv, Subgroup.mem_inf, mem_centralizer_zpowers_iff_commute, mem_fixingSubgroup_iff]
    refine and_congr Iff.rfl ⟨fun h ω hω => h ω ?_, fun h ω hω => h ω ?_⟩
    · rw [hΦ, fixSet_zpowers]; exact hω
    · rw [hΦ, fixSet_zpowers] at hω; exact hω
  have hKvfix : ∀ {k : G}, k ∈ Kv → k • α = α ∧ k • β = β ∧ k • γ = γ := fun hk =>
    ⟨(hmemKv.mp hk).2 α hC.smul_α, (hmemKv.mp hk).2 β hC.smul_β, (hmemKv.mp hk).2 γ hC.smul_γ⟩
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hconjKv : ∀ {k : G}, k ∈ Kv → r * k * r⁻¹ ∈ Kv := fun {k} hk => by
    obtain ⟨hkv, hkf⟩ := hmemKv.mp hk
    refine hmemKv.mpr ⟨(hrv.mul_left hkv).mul_left hrv.inv_left, fun ω hω => ?_⟩
    have hω' : v • (r⁻¹ • ω) = r⁻¹ • ω := by
      rw [← mul_smul, ← hrv.inv_left.eq, mul_smul, hω]
    rw [mul_smul, mul_smul, hkf _ hω', smul_inv_smul]
  have hrN : r ∈ Subgroup.normalizer (Kv : Set G) := Subgroup.mem_normalizer_iff.mpr fun k =>
    ⟨fun hk => hconjKv hk, fun hk => by
      have := hconjKv hk
      rwa [hrinv, ← mul_assoc, ← mul_assoc, hr2, one_mul, mul_assoc, hr2, mul_one] at this⟩
  obtain ⟨K₂, hK₂, hrK₂⟩ := exists_fusionIsSylowIn_mem_normalizer
    (isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one, sq, hr2])) hrN
  have hBvN : Kv ≤ Subgroup.normalizer (Bv : Set G) := fun k hk =>
    Subgroup.mem_normalizer_iff.mpr fun g => by
      obtain ⟨hkα, hkβ, hkγ⟩ := hKvfix hk
      obtain ⟨hk'α, hk'β, hk'γ⟩ := hKvfix (inv_mem hk)
      refine ⟨fun hg => Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hk hg.1) (inv_mem hk),
        hC.conj_mem_caseBRad hkα hkβ hkγ hg.2⟩, fun hg => ?_⟩
      have h1 := Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hk) hg.1) (inv_mem (inv_mem hk)),
        hC.conj_mem_caseBRad hk'α hk'β hk'γ hg.2⟩
      rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc,
        inv_mul_cancel, mul_one] at h1
  have hY : fusionIsSylowIn 2 (K₂ ⊓ Bv) Bv :=
    fusionIsSylowIn_inf_of_le_normalizer hK₂ inf_le_left hBvN
  have hK₂Kv : K₂ ≤ Kv := hK₂.1
  have hYmem : ∀ {y : G}, y ∈ K₂ ⊓ Bv →
      y * y = 1 ∧ Commute y v ∧ ∀ ω : Ω, v • ω = ω → y • ω = ω := fun {y} hy => by
    obtain ⟨hyK, hyKv, hyR⟩ : y ∈ K₂ ∧ y ∈ Kv ∧ y ∈ caseBRad G Ω α β ⟨γ, hC.mem_holtDelta⟩ :=
      ⟨hy.1, hy.2.1, hy.2.2⟩
    obtain ⟨hyv, hyf⟩ := hmemKv.mp hyKv
    refine ⟨?_, hyv, hyf⟩
    obtain ⟨hyP, hyα, hyβ, hyZ⟩ := mem_caseBRad.mp hyR
    have hyyP : y * y ∈ stabilizer G ({α, β} : Set Ω) := mul_mem hyP hyP
    have hK0 : y * y ∈ twoPointKernel G Ω α β :=
      mem_twoPointKernel_of_twoPointHom_eq_one hyyP (by rw [mul_smul, hyα, hyα])
        (by rw [mul_smul, hyβ, hyβ]) (by
          rw [show (⟨y * y, hyyP⟩ : stabilizer G ({α, β} : Set Ω)) = ⟨y, hyP⟩ * ⟨y, hyP⟩ from rfl,
            map_mul]
          exact hC.isNaturalSE.mul_self_eq_one_of_mem_rootCenter hyZ)
    obtain ⟨k, hk⟩ := hK₂.2.1 ⟨y * y, mul_mem hyK hyK⟩
    exact eq_one_of_isPGroup_of_odd hC.odd_card hK0 (k := k) (by
      have := congrArg Subtype.val hk
      simpa using this)
  refine ⟨K₂ ⊓ Bv, fun y hy => hy.2.2, ?_, fun y hy => hYmem hy, ?_, ?_⟩
  ·
    have hvKv : v ∈ Kv := hmemKv.mpr ⟨Commute.refl v, fun ω h => h⟩
    have hvK₂ : v ∈ K₂ := mem_of_fusionIsSylowIn_of_commute hK₂ hvKv
      (isPGroup_zpowers_of_orderOf_eq_two hC.orderOf_v)
      (fun x hx => ((hmemKv.mp (hK₂Kv hx)).1).eq)
    exact ⟨hvK₂, hvKv, hC.v_mem_caseBRad hS⟩
  ·
    intro y hy
    have hyK₂ : r * y * r⁻¹ ∈ K₂ := (Subgroup.mem_normalizer_iff.mp hrK₂ y).mp hy.1
    refine ⟨hyK₂, hconjKv hy.2.1, ?_⟩
    by_cases hy1 : y = 1
    · rw [hy1, mul_one, mul_inv_cancel]; exact one_mem _
    obtain ⟨hy2, -, hyf⟩ := hYmem hy
    have hyc : IsConj v y := hC.isConj_of_mem_caseBRad hS hy.2.2 hy2 hy1
    have hFy : fixedBy Ω y = fixedBy Ω v :=
      (Set.eq_of_subset_of_ncard_le (fun ω hω => hyf ω hω)
        (ncard_fixedBy_of_isConj hyc).le (Set.toFinite _)).symm
    have hc' : IsConj v (r * y * r⁻¹) := hyc.trans (isConj_iff.mpr ⟨r, rfl⟩)
    have hF' : fixedBy Ω (r * y * r⁻¹) = fixedBy Ω v := by
      rw [← smul_fixedBy, hFy, smul_fixedBy, hrv.eq, mul_inv_cancel_right]
    exact hC.mem_caseBRad_of_fixedBy_eq hS hc' hF'
  ·
    intro z hz
    obtain ⟨y, hyP, hyR, hyv, hy2, hyz⟩ := hC.exists_mem_caseBRad_mul_self_eq_one hS hz
    have hyKv : y ∈ Kv :=
      hmemKv.mpr ⟨hyv, fun ω hω => hC.smul_eq_of_mem_caseBRad hS hyv hy2 hyR hω⟩
    obtain ⟨Y', hyY', hY'⟩ := exists_fusionIsSylowIn_ge
      (isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one, sq, hy2]))
      (Subgroup.zpowers_le.mpr (show y ∈ Bv from ⟨hyKv, hyR⟩))
    obtain ⟨k, hkB, hk⟩ := exists_mem_conj_of_fusionIsSylowIn hY hY'
    have hkyk : k⁻¹ * y * k ∈ K₂ ⊓ Bv := (hk y).mp (hyY' (Subgroup.mem_zpowers y))
    obtain ⟨hkP, -, -, hkZ⟩ := mem_caseBRad.mp hkB.2
    refine ⟨k⁻¹ * y * k, hkyk, mul_mem (mul_mem (inv_mem hkP) hyP) hkP, ?_⟩
    rw [show (⟨k⁻¹ * y * k, mul_mem (mul_mem (inv_mem hkP) hyP) hkP⟩ :
      stabilizer G ({α, β} : Set Ω)) = ⟨k, hkP⟩⁻¹ * ⟨y, hyP⟩ * ⟨k, hkP⟩ from rfl, map_mul,
      map_mul, map_inv, hyz, mul_assoc, Subgroup.mem_centralizer_iff.mp hkZ.2 z hz.1,
      inv_mul_cancel_left]

omit [FaithfulSMul G Ω] in
theorem isConj_and_fixedBy_eq (hS : Sec4Setting G Ω) {Y : Subgroup G}
    (hYR : Y ≤ caseBRad G Ω α β ⟨γ, hC.mem_holtDelta⟩)
    (hYmem : ∀ y ∈ Y, y * y = 1 ∧ Commute y v ∧ ∀ ω : Ω, v • ω = ω → y • ω = ω) {y : G}
    (hy : y ∈ Y) (hy1 : y ≠ 1) : IsConj v y ∧ fixedBy Ω y = fixedBy Ω v := by
  obtain ⟨hy2, -, hyf⟩ := hYmem y hy
  have hyc : IsConj v y := hC.isConj_of_mem_caseBRad hS (hYR hy) hy2 hy1
  exact ⟨hyc, (Set.eq_of_subset_of_ncard_le (fun ω hω => hyf ω hω)
    (ncard_fixedBy_of_isConj hyc).le (Set.toFinite _)).symm⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] hC in
theorem commute_of_forall_mul_self {Y : Subgroup G} (hY : ∀ y ∈ Y, y * y = 1) {y y' : G}
    (hy : y ∈ Y) (hy' : y' ∈ Y) : Commute y y' := by
  have h1 := hY _ (mul_mem hy hy')
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hY y hy)
  have hy'inv : y'⁻¹ = y' := inv_eq_of_mul_eq_one_right (hY y' hy')
  have h := (inv_eq_of_mul_eq_one_right h1).symm
  rw [mul_inv_rev, hyinv, hy'inv] at h
  exact h

theorem false_of_witness_commute (hS : Sec4Setting G Ω) {s : G} (hs : IsConj v s)
    (hsv : Commute s v) (hsΦ : fixedBy Ω s ≠ fixedBy Ω v) {Y : Subgroup G}
    (hYR : Y ≤ caseBRad G Ω α β ⟨γ, hC.mem_holtDelta⟩)
    (hYmem : ∀ y ∈ Y, y * y = 1 ∧ Commute y v ∧ ∀ ω : Ω, v • ω = ω → y • ω = ω) {u₁ u₂ : G}
    (hu₁ : u₁ ∈ Y) (hu₂ : u₂ ∈ Y) (h1 : u₁ ≠ 1) (h2 : u₂ ≠ 1) (h12 : u₁ ≠ u₂)
    (hs₁ : Commute s u₁) (hs₂ : Commute s u₂) : False := by
  have hY2 : ∀ y ∈ Y, y * y = 1 := fun y hy => (hYmem y hy).1
  have hc : Commute u₁ u₂ := commute_of_forall_mul_self hY2 hu₁ hu₂
  have h12' : u₁ * u₂ ≠ 1 := fun h => h12 (by
    rw [mul_eq_one_iff_eq_inv, inv_eq_of_mul_eq_one_right (hY2 u₂ hu₂)] at h; exact h)
  obtain ⟨hc₁, hF₁⟩ := hC.isConj_and_fixedBy_eq hS hYR hYmem hu₁ h1
  obtain ⟨-, hF₂⟩ := hC.isConj_and_fixedBy_eq hS hYR hYmem hu₂ h2
  obtain ⟨-, hF₁₂⟩ := hC.isConj_and_fixedBy_eq hS hYR hYmem (mul_mem hu₁ hu₂) h12'
  obtain ⟨g, rfl⟩ := isConj_iff.mp hs
  have hconj : ∀ {u : G}, Commute (g * v * g⁻¹) u → Commute (g⁻¹ * u * g) v := fun {u} h => by
    change g⁻¹ * u * g * v = v * (g⁻¹ * u * g)
    have := h.eq
    calc g⁻¹ * u * g * v = g⁻¹ * (u * (g * v * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * v * g⁻¹) * u) * g := by rw [this]
      _ = v * (g⁻¹ * u * g) := by group
  have hF : ∀ {u : G}, fixedBy Ω u = fixedBy Ω v → fixedBy Ω (g⁻¹ * u * g) = g⁻¹ • fixedBy Ω v :=
    fun {u} h => by rw [← h, smul_fixedBy, inv_inv]
  have key := hC.fixedBy_eq_of_commute hS (hconj hs₁) (hconj hs₂)
    (show Commute (g⁻¹ * u₁ * g) (g⁻¹ * u₂ * g) by
      change g⁻¹ * u₁ * g * (g⁻¹ * u₂ * g) = g⁻¹ * u₂ * g * (g⁻¹ * u₁ * g)
      have := hc.eq
      calc g⁻¹ * u₁ * g * (g⁻¹ * u₂ * g) = g⁻¹ * (u₁ * u₂) * g := by group
        _ = g⁻¹ * (u₂ * u₁) * g := by rw [this]
        _ = g⁻¹ * u₂ * g * (g⁻¹ * u₁ * g) := by group)
    (hc₁.trans (isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩))
    (by rw [show g⁻¹ * u₂ * g * (g⁻¹ * u₂ * g) = g⁻¹ * (u₂ * u₂) * g by group, hY2 u₂ hu₂,
      mul_one, inv_mul_cancel])
    (by rw [hF hF₁, hF hF₂])
    (by rw [hF hF₁, show g⁻¹ * u₁ * g * (g⁻¹ * u₂ * g) = g⁻¹ * (u₁ * u₂) * g by group,
      hF hF₁₂])
  rw [hF hF₁] at key
  apply hsΦ
  calc fixedBy Ω (g * v * g⁻¹) = g • fixedBy Ω v := (smul_fixedBy Ω v g).symm
    _ = g • (g⁻¹ • fixedBy Ω v) := by rw [key]
    _ = fixedBy Ω v := smul_inv_smul g _

theorem exists_Y_of_witness (hS : Sec4Setting G Ω) {s : G} (hs : IsConj v s)
    (hsv : Commute s v) (hsΦ : fixedBy Ω s ≠ fixedBy Ω v) :
    Nat.card (rootCenter (seRadical (twoPointJ G Ω α β) ⟨γ, hC.mem_holtDelta⟩)) = 4 ∧
    ∃ Y : Subgroup G, Y ≤ caseBRad G Ω α β ⟨γ, hC.mem_holtDelta⟩ ∧ v ∈ Y ∧
      (∀ y ∈ Y, y * y = 1 ∧ Commute y v ∧ ∀ ω : Ω, v • ω = ω → y • ω = ω) ∧
      (∀ y ∈ Y, s * y * s⁻¹ ∈ Y) ∧
      (∀ z ∈ rootCenter (seRadical (twoPointJ G Ω α β) ⟨γ, hC.mem_holtDelta⟩),
        ∃ y ∈ Y, ∃ hyP : y ∈ stabilizer G ({α, β} : Set Ω), twoPointHom G Ω α β ⟨y, hyP⟩ = z) ∧
      ¬ ∀ y ∈ Y, Commute s y := by
  classical
  have hs2 := hC.mul_self_eq_one_of_isConj hs
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  obtain ⟨Y, hYR, hvY, hYmem, hYs, hYz⟩ := hC.exists_Y hS hsv hs2
  have hY2 : ∀ y ∈ Y, y * y = 1 := fun y hy => (hYmem y hy).1
  have hcomm : ∀ {y y' : G}, y ∈ Y → y' ∈ Y → Commute y y' := fun hy hy' =>
    commute_of_forall_mul_self hY2 hy hy'
  let f : Y →* Y :=
    { toFun := fun y => ⟨(y : G) * (s * y * s⁻¹), mul_mem y.2 (hYs y y.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun y₁ y₂ => Subtype.ext (by
        change (y₁ * y₂ : G) * (s * (y₁ * y₂) * s⁻¹) = (y₁ * (s * y₁ * s⁻¹)) * (y₂ * (s * y₂ * s⁻¹))
        have h := (hcomm y₂.2 (hYs _ y₁.2)).eq
        calc (y₁ * y₂ : G) * (s * (y₁ * y₂) * s⁻¹) =
            y₁ * (y₂ * (s * y₁ * s⁻¹)) * (s * y₂ * s⁻¹) := by group
          _ = y₁ * ((s * y₁ * s⁻¹) * y₂) * (s * y₂ * s⁻¹) := by rw [h]
          _ = (y₁ * (s * y₁ * s⁻¹)) * (y₂ * (s * y₂ * s⁻¹)) := by group) }
  have hker : ∀ y : Y, y ∈ f.ker → Commute s y := fun y hy => by
    have h : (y : G) * (s * y * s⁻¹) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
    have h' : s * y * s⁻¹ = y := by
      have := eq_inv_of_mul_eq_one_right h
      rwa [inv_eq_of_mul_eq_one_right (hY2 y y.2)] at this
    change s * y = y * s
    calc s * (y : G) = s * y * s⁻¹ * s := by group
      _ = y * s := by rw [h']
  have hrange : f.range ≤ f.ker := by
    rintro _ ⟨y, rfl⟩
    refine MonoidHom.mem_ker.mpr (Subtype.ext ?_)
    change (y : G) * (s * y * s⁻¹) * (s * ((y : G) * (s * y * s⁻¹)) * s⁻¹) = 1
    have h1 : s * ((y : G) * (s * y * s⁻¹)) * s⁻¹ = (s * y * s⁻¹) * y := by
      calc s * ((y : G) * (s * y * s⁻¹)) * s⁻¹ = (s * y * s⁻¹) * ((s * s) * y * (s⁻¹ * s⁻¹)) := by
            group
        _ = (s * y * s⁻¹) * y := by rw [hs2, hsinv, hs2, one_mul, mul_one]
    rw [h1, ← (hcomm y.2 (hYs _ y.2)).eq]
    exact hY2 _ (mul_mem y.2 (hYs _ y.2))
  have hker2 : Nat.card f.ker ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have hlt' : 2 < (f.ker : Set Y).ncard := by rwa [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
      (Set.two_lt_ncard_iff (Set.toFinite _)).mp hlt'
    have key : ∀ x y : Y, x ∈ f.ker → y ∈ f.ker → x ≠ 1 → y ≠ 1 → x ≠ y → False :=
      fun x y hx hy hx1 hy1 hxy => hC.false_of_witness_commute hS hs hsv hsΦ hYR hYmem x.2 y.2
        (fun h => hx1 (Subtype.ext h)) (fun h => hy1 (Subtype.ext h))
        (fun h => hxy (Subtype.ext h)) (hker x hx) (hker y hy)
    by_cases ha1 : a = 1
    · exact key b c hb hc (fun h => hab (ha1.trans h.symm)) (fun h => hac (ha1.trans h.symm)) hbc
    by_cases hb1 : b = 1
    · exact key a c ha hc ha1 (fun h => hbc (hb1.trans h.symm)) hac
    · exact key a b ha hb ha1 hb1 hab
  have hYcard : Nat.card Y ≤ 4 := by
    rw [← Subgroup.card_ker_mul_card_range f]
    have := Subgroup.card_le_of_le hrange
    nlinarith
  set Z := rootCenter (seRadical (twoPointJ G Ω α β) ⟨γ, hC.mem_holtDelta⟩)
  have hZY : Nat.card Z ≤ Nat.card Y := by
    refine Nat.card_le_card_of_surjective (fun y : Y => (⟨twoPointHom G Ω α β
      ⟨y, (mem_caseBRad.mp (hYR y.2)).1⟩, (mem_caseBRad.mp (hYR y.2)).2.2.2⟩ : Z)) ?_
    rintro ⟨z, hz⟩
    obtain ⟨y, hy, hyP, hyz⟩ := hYz z hz
    exact ⟨⟨y, hy⟩, Subtype.ext hyz⟩
  obtain ⟨n, i, e, hA⟩ := isNaturalSE_iff.mp hC.isNaturalSE
  have hZ4 : 4 ≤ Nat.card Z := by
    rw [hA.card_rootCenter_seRadical]; exact hA.four_le_q
  refine ⟨by omega, Y, hYR, hvY, hYmem, hYs, hYz, fun hall => ?_⟩
  have htop : f.ker = ⊤ := eq_top_iff.mpr fun y _ => MonoidHom.mem_ker.mpr (Subtype.ext (by
    change (y : G) * (s * y * s⁻¹) = 1
    rw [(hall y y.2).eq, mul_inv_cancel_right]
    exact hY2 y y.2))
  rw [htop, Subgroup.card_top] at hker2
  omega

end Prop46CaseB

end YGroups

section LemmaA

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]

theorem Sec4Setting.exists_mem_longInvAt_centralizer_of_mem_holtDelta (hS : Sec4Setting G Ω)
    {α ζ η : Ω} (hζη : ζ ≠ η) (hα : α ∈ holtDelta G Ω ζ η) {X₀ : Subgroup G}
    (hX₀ : IsPGroup 2 X₀) (hX₀le : X₀ ≤ stabilizer G ({ζ, η} : Set Ω) ⊓ stabilizer G α) :
    ∃ t' ∈ longInvAt G Ω α, t' • ζ = η ∧ t' ∈ Subgroup.centralizer (X₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, -, hT⟩ := exists_fusionIsSylowIn_ge (p := 2) (Q := ⊥) IsPGroup.of_bot
    (bot_le : ⊥ ≤ stabilizer G ζ ⊓ stabilizer G η ⊓ stabilizer G α)
  obtain ⟨hT', u, hu, huα, huT⟩ := hS.sylow_twoPoint hζη hα hT
  have hTα : T ≤ stabilizer G α := hT.1.trans inf_le_right
  have hR := fusionIsSylowIn_sup_zpowers_inf_stabilizer hζη hT' hu huT hTα huα
  obtain ⟨R', hX₀R', hR'⟩ := exists_fusionIsSylowIn_ge hX₀ hX₀le
  obtain ⟨k, hk, hkR⟩ := exists_mem_conj_of_fusionIsSylowIn hR hR'
  have huR : T ⊔ Subgroup.zpowers u ≤ Subgroup.centralizer (Subgroup.zpowers u : Set G) :=
    sup_le (fun x hx =>
      mem_centralizer_zpowers_iff_commute.mpr (Subgroup.mem_centralizer_iff.mp huT x hx))
      (Subgroup.zpowers_le.mpr (mem_centralizer_zpowers_iff_commute.mpr (Commute.refl u)))
  obtain ⟨hkP, hkα⟩ := Subgroup.mem_inf.mp hk
  have huP : u ∈ stabilizer G ({ζ, η} : Set Ω) :=
    closure_longInvSwap_le_stabilizer_pair ζ η (Subgroup.subset_closure hu)
  have ht'J : k * u * k⁻¹ ∈ longInvAt G Ω α := by
    have := conj_mem_longInvAt (show u ∈ longInvAt G Ω α from ⟨hu.1, huα⟩) k
    rwa [mem_stabilizer_iff.mp hkα] at this
  refine ⟨k * u * k⁻¹, ht'J, ?_, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  · have hζα : ζ ≠ α := fun h => hζη (by rw [← hu.2, h, huα])
    rcases smul_pair_of_mem_stabilizer_pair (mul_mem (mul_mem hkP huP) (inv_mem hkP)) with
      ⟨h1, -⟩ | ⟨h1, -⟩
    · obtain ⟨ω, -, hω⟩ := ht'J.1.2
      exact absurd ((hω ζ h1).trans (hω α ht'J.2).symm) hζα
    · exact h1
  · have hxR : k⁻¹ * x * k ∈ T ⊔ Subgroup.zpowers u := (hkR x).mp (hX₀R' hx)
    have hc := (mem_centralizer_zpowers_iff_commute.mp (huR hxR)).eq
    calc x * (k * u * k⁻¹) = k * ((k⁻¹ * x * k) * u) * k⁻¹ := by group
      _ = k * (u * (k⁻¹ * x * k)) * k⁻¹ := by rw [hc]
      _ = k * u * k⁻¹ * x := by group

end LemmaA

section CorC

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  {α β γ : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

namespace Prop46CaseB

variable (hC : Prop46CaseB G Ω α β γ v P)
include hC

omit [Finite G] [DecidableEq Ω] in
theorem smul_eq_inv_of_fix {r : G} (hrv : Commute r v) (hr2 : r * r = 1) (hrα : r • α = α)
    (hrC : ∀ p ∈ P, r • ((p • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) : _) : Ω) =
      ((p • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) : _) : Ω) →
        p • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) = ⟨α, hC.α_mem⟩)
    {p : typeLSection G Ω v} (hp : p ∈ P) :
    r • ((p • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) : _) : Ω) =
      ((p⁻¹ • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) : _) : Ω) := by
  have hr : typeLElt (Ω := Ω) hrv * typeLElt hrv = 1 := by
    rw [typeLElt_mul]
    exact Subtype.ext (Equiv.ext fun ω => Subtype.ext (by
      change (r * r) • (ω : Ω) = ω; rw [hr2, one_smul]))
  have h := smul_smul_eq_inv_smul_of_normal hC.normal hC.P_comm hr (Subtype.ext hrα)
    (fun q hq hqf => hrC q hq (congrArg Subtype.val hqf)) hp
  exact congrArg Subtype.val h

theorem exists_mem_longInvAt_centralizer_sup (hS : Sec4Setting G Ω) {r : G} (hrv : Commute r v)
    (hr2 : r * r = 1) (hrα : r • α = α) {Y₁ : Subgroup G} (hY₁ : IsPGroup 2 Y₁)
    (hY₁C : ∀ y ∈ Y₁, ∀ p ∈ P,
      y • ((p • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) : _) : Ω) =
        ((p • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) : _) : Ω))
    (hY₁r : ∀ y ∈ Y₁, r * y * r⁻¹ ∈ Y₁) :
    ∃ t' ∈ longInvAt G Ω α,
      t' ∈ Subgroup.centralizer ((Y₁ ⊔ Subgroup.zpowers r : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a : fixSet Ω (Subgroup.zpowers v) := ⟨α, hC.α_mem⟩ with ha
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hrN : Subgroup.zpowers r ≤ Subgroup.normalizer (Y₁ : Set G) := Subgroup.zpowers_le.mpr
    (Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => hY₁r h hh, fun hh => by
      have := hY₁r _ hh
      rwa [hrinv, ← mul_assoc, ← mul_assoc, hr2, one_mul, mul_assoc, hr2, mul_one] at this⟩)
  have hX₀ : IsPGroup 2 ↥(Y₁ ⊔ Subgroup.zpowers r) :=
    hY₁.to_sup_of_normal_left' (isPGroup_zpowers_of_pow_eq_one (k := 1) (by
      rw [pow_one, sq, hr2])) hrN
  have hY₁α : ∀ y ∈ Y₁, y • α = α := fun y hy => by
    have := hY₁C y hy 1 (one_mem _)
    simpa using this
  have hX₀α : Y₁ ⊔ Subgroup.zpowers r ≤ stabilizer G α :=
    sup_le (fun y hy => mem_stabilizer_iff.mpr (hY₁α y hy))
      (Subgroup.zpowers_le.mpr (mem_stabilizer_iff.mpr hrα))
  by_cases hfix : ∃ p ∈ P, p • a ≠ a ∧ r • ((p • a : _) : Ω) = ((p • a : _) : Ω)
  · obtain ⟨p, hp, hpa, hpr⟩ := hfix
    have hfp : ((p • a : _) : Ω) ∈ fixSet Ω (Y₁ ⊔ Subgroup.zpowers r) :=
      mem_fixSet_iff_le_stabilizer.mpr (sup_le (fun y hy => mem_stabilizer_iff.mpr (hY₁C y hy p hp))
        (Subgroup.zpowers_le.mpr (mem_stabilizer_iff.mpr hpr)))
    have hfα : α ∈ fixSet Ω (Y₁ ⊔ Subgroup.zpowers r) := mem_fixSet_iff_le_stabilizer.mpr hX₀α
    have h1 : 1 < Nat.card (fixSet Ω (Y₁ ⊔ Subgroup.zpowers r)) :=
      Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨⟨α, hfα⟩, ⟨_, hfp⟩, fun h =>
        hpa (Subtype.ext (congrArg Subtype.val h).symm)⟩⟩
    obtain ⟨t', ht', ht'c⟩ := hS.star.star α _ hX₀ hX₀α
      ((three_le_card_fixSet_iff hS.star.odd_card hX₀).mpr h1)
    exact ⟨t', ht', ht'c⟩
  push Not at hfix
  have hrC : ∀ p ∈ P, r • ((p • a : _) : Ω) = ((p • a : _) : Ω) → p • a = a :=
    fun p hp h => by_contra fun hne => hfix p hp hne h
  obtain ⟨p₀, hp₀, hp₀a⟩ := hC.exists_mem_P_smul_α_eq_β
  obtain ⟨t, ht, u, -, -, htu, htuv, -⟩ := hC.isTypeL
  have htv : Commute t v := htuv ▸ (Commute.refl t).mul_right htu
  have htC : ∀ p ∈ P, t • ((p • a : _) : Ω) = ((p • a : _) : Ω) → p • a = a := fun p _ h => by
    obtain ⟨ω, -, hω⟩ := ht.1.2
    exact Subtype.ext ((hω _ h).trans (hω α ht.2).symm)
  have hrβ := hC.smul_eq_inv_of_fix hrv hr2 hrα hrC hp₀
  have htβ := hC.smul_eq_inv_of_fix htv (mul_self_eq_one_of_mem_longInv ht.1) ht.2 htC hp₀
  have hζη : ((p₀ • a : _) : Ω) ≠ ((p₀⁻¹ • a : _) : Ω) := fun h => by
    have := hrC p₀ hp₀ (hrβ.trans h.symm)
    rw [hp₀a] at this
    exact hC.ne (congrArg Subtype.val this).symm
  have hαΔ : α ∈ holtDelta G Ω ((p₀ • a : _) : Ω) ((p₀⁻¹ • a : _) : Ω) := ⟨t, ⟨ht.1, htβ⟩, ht.2⟩
  have hrη : r • ((p₀⁻¹ • a : _) : Ω) = ((p₀ • a : _) : Ω) := by
    rw [← hrβ, ← mul_smul, hr2, one_smul]
  have hX₀P : Y₁ ⊔ Subgroup.zpowers r ≤
      stabilizer G ({((p₀ • a : _) : Ω), ((p₀⁻¹ • a : _) : Ω)} : Set Ω) :=
    sup_le (fun y hy => stabilizer_inf_le_stabilizer_pair _ _ (Subgroup.mem_inf.mpr
        ⟨mem_stabilizer_iff.mpr (hY₁C y hy p₀ hp₀),
          mem_stabilizer_iff.mpr (hY₁C y hy p₀⁻¹ (inv_mem hp₀))⟩))
      (Subgroup.zpowers_le.mpr (by
        rw [mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton, hrβ, hrη,
          Set.pair_comm]))
  obtain ⟨t', ht', -, ht'c⟩ := hS.exists_mem_longInvAt_centralizer_of_mem_holtDelta hζη hαΔ hX₀
    (le_inf hX₀P hX₀α)
  exact ⟨t', ht', ht'c⟩

end Prop46CaseB

end CorC

section Unitary

variable {Δ : Type} [Finite Δ] {L : Subgroup (Equiv.Perm Δ)} {n i e : ℕ} {b : Δ}

theorem IsBenderAction.commute_of_unitary (hA : IsBenderAction ↥L Δ n 3 e) {x : Equiv.Perm Δ}
    (hxN : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hxb : x b = b) (hx2 : x * x = 1)
    {z : Equiv.Perm Δ} (hz : z ∈ rootCenter (seRadical L b)) : x * z = z * x := by
  by_cases hxL : x ∈ L
  · exact Subgroup.mem_centralizer_iff.mp hz.2 x
      (mem_seRadical_of_pow_eq_one hxL hxb (k := 1) (by rw [pow_one, sq, hx2]))
  · exact (hA.commute_iff_mem_rootCenter_of_unitary hxN hx2 hxL hxb hz.1).mpr hz

theorem IsNaturalSE.card_eq_five_of_not_commute (hL : IsNaturalSE L) {x z : Equiv.Perm Δ}
    (hxN : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hxb : x b = b) (hx2 : x * x = 1)
    (hz : z ∈ rootCenter (seRadical L b)) (hxz : x * z ≠ z * x)
    (h4 : Nat.card (rootCenter (seRadical L b)) = 4) :
    x ∉ L ∧ Nat.card Δ = 5 ∧ 60 ∣ Nat.card L := by
  have hxL : x ∉ L := fun hxL => hxz (Subgroup.mem_centralizer_iff.mp hz.2 x
    (mem_seRadical_of_pow_eq_one hxL hxb (k := 1) (by rw [pow_one, sq, hx2])))
  obtain ⟨n, i, e, hA⟩ := isNaturalSE_iff.mp hL
  have hn : n = 2 := by
    rw [hA.card_rootCenter_seRadical] at h4
    exact Nat.pow_right_injective le_rfl (h4.trans (by norm_num))
  obtain ⟨hi1, hi3, -⟩ := hA.params
  have hi : i = 1 := by
    rcases (show i = 1 ∨ i = 2 ∨ i = 3 by omega) with h | h | h
    · exact h
    · subst h; exact absurd (hA.mem_of_mul_self_eq_one_of_suzuki hxN hx2) hxL
    · subst h; exact absurd (hA.commute_of_unitary hxN hxb hx2 hz) hxz
  subst hn hi
  have h5 : Nat.card Δ = 5 := by rw [hA.card_eq]; norm_num
  refine ⟨hxL, h5, ?_⟩
  have := hA.isPretransitive
  have hd5 : 5 ∣ Nat.card L := by
    have h := index_stabilizer (↥L) b
    rw [orbit_eq_univ, Set.ncard_univ, h5] at h
    rw [← h]
    exact Subgroup.index_dvd_card _
  have hd4 : 4 ∣ Nat.card L := by
    have h := Subgroup.card_dvd_of_le (seRadical_le (L := L) (b := b))
    rwa [hA.card_seRadical] at h
  have hd3 : 3 ∣ Nat.card L := by
    have : Nontrivial Δ := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨c, hc⟩ := exists_ne b
    have h := Subgroup.card_subgroup_dvd_card (stabilizer (↥L) b ⊓ stabilizer (↥L) c)
    rw [hA.card_stabilizer_inf (Ne.symm hc)] at h
    exact (Dvd.intro e rfl).trans (by norm_num at h ⊢; exact h)
  have h20 : 20 ∣ Nat.card L :=
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 5 4) hd5 hd4)
  exact (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 20 3) h20 hd3)

end Unitary

section FourGroup

variable {G : Type*} [Group G] [Finite G]

theorem exists_ne_one_forall_commute_of_card_eq_four {R Y : Subgroup G} (hR : Nat.card R = 4)
    (hY : Nat.card Y = 4) (hRY : ∀ ρ ∈ R, ∀ y ∈ Y, ρ * y * ρ⁻¹ ∈ Y) :
    ∃ ρ ∈ R, ρ ≠ 1 ∧ ∀ y ∈ Y, Commute ρ y := by
  classical
  have : Fintype Y := Fintype.ofFinite Y
  have hT : Nat.card {y : Y // y ≠ 1} = 3 := by
    rw [Nat.card_eq_fintype_card]
    have h4 : Fintype.card Y = 4 := by rw [← Nat.card_eq_fintype_card, hY]
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, h4]
  have hconj : ∀ (ρ : R) (y : Y), (ρ : G) * y * (ρ : G)⁻¹ ∈ Y := fun ρ y => hRY ρ ρ.2 y y.2
  have hconj' : ∀ (ρ : R) (y : Y), (ρ : G)⁻¹ * y * ρ ∈ Y := fun ρ y => by
    have := hRY _ (inv_mem ρ.2) y y.2
    rwa [inv_inv] at this
  let conjT : R → Equiv.Perm {y : Y // y ≠ 1} := fun ρ =>
    { toFun := fun t => ⟨⟨ρ * t * (ρ : G)⁻¹, hconj ρ t⟩, fun h => t.2 (Subtype.ext (by
        have h' := congrArg Subtype.val h
        change (ρ : G) * t * (ρ : G)⁻¹ = 1 at h'
        rw [mul_inv_eq_one, mul_eq_left] at h'
        exact h'))⟩
      invFun := fun t => ⟨⟨(ρ : G)⁻¹ * t * ρ, hconj' ρ t⟩, fun h => t.2 (Subtype.ext (by
        have h' := congrArg Subtype.val h
        change (ρ : G)⁻¹ * t * ρ = 1 at h'
        rw [mul_eq_one_iff_eq_inv, inv_mul_eq_iff_eq_mul, mul_inv_cancel] at h'
        exact h'))⟩
      left_inv := fun t => Subtype.ext (Subtype.ext (by
        change (ρ : G)⁻¹ * ((ρ : G) * t * (ρ : G)⁻¹) * ρ = t; group))
      right_inv := fun t => Subtype.ext (Subtype.ext (by
        change (ρ : G) * ((ρ : G)⁻¹ * t * ρ) * (ρ : G)⁻¹ = t; group)) }
  let ψ : R →* Equiv.Perm {y : Y // y ≠ 1} :=
    { toFun := conjT
      map_one' := Equiv.ext fun t => Subtype.ext (Subtype.ext (by
        change ((1 : R) : G) * t * ((1 : R) : G)⁻¹ = t; simp))
      map_mul' := fun ρ₁ ρ₂ => Equiv.ext fun t => Subtype.ext (Subtype.ext (by
        change ((ρ₁ * ρ₂ : R) : G) * t * ((ρ₁ * ρ₂ : R) : G)⁻¹ =
          (ρ₁ : G) * ((ρ₂ : G) * t * (ρ₂ : G)⁻¹) * (ρ₁ : G)⁻¹
        simp only [Subgroup.coe_mul]; group)) }
  have h1 : Nat.card ψ.range ∣ 4 := hR ▸ Subgroup.card_range_dvd ψ
  have h2 : Nat.card ψ.range ∣ 6 := by
    have := Subgroup.card_subgroup_dvd_card ψ.range
    rwa [Nat.card_perm, hT] at this
  have h3 : Nat.card ψ.range ≤ 2 :=
    Nat.le_of_dvd (by norm_num) ((Nat.dvd_gcd h1 h2).trans (by norm_num))
  have hker : 1 < Nat.card ψ.ker := by
    have := Subgroup.card_ker_mul_card_range ψ
    rw [hR] at this
    have hpos : 0 < Nat.card ψ.range := Nat.card_pos
    by_contra hle
    push Not at hle
    have : Nat.card ψ.ker * Nat.card ψ.range ≤ 1 * 2 := Nat.mul_le_mul hle h3
    omega
  obtain ⟨⟨ρ, hρ⟩, hρ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    ((Subgroup.one_lt_card_iff_ne_bot _).mp hker)
  refine ⟨ρ, ρ.2, fun h => hρ1 (Subtype.ext (Subtype.ext h)), fun y hy => ?_⟩
  by_cases hy1 : (⟨y, hy⟩ : Y) = 1
  · rw [show y = 1 from congrArg Subtype.val hy1]; exact Commute.one_right _
  · have h := congrArg (fun π : Equiv.Perm {y : Y // y ≠ 1} =>
      (((π ⟨⟨y, hy⟩, hy1⟩ : {y : Y // y ≠ 1}) : Y) : G)) (MonoidHom.mem_ker.mp hρ)
    change (ρ : G) * y * (ρ : G)⁻¹ = y at h
    change (ρ : G) * y = y * ρ
    calc (ρ : G) * y = (ρ : G) * y * (ρ : G)⁻¹ * ρ := by group
      _ = y * ρ := by rw [h]

end FourGroup

section TwoNe

theorem exists_ne_one_ne_of_two_lt_card {G : Type*} [Group G] [Finite G] {Y : Subgroup G}
    (h : 2 < Nat.card Y) : ∃ u₁ ∈ Y, ∃ u₂ ∈ Y, u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₁ ≠ u₂ := by
  have h' : 2 < (Y : Set G).ncard := by rwa [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).mp h'
  by_cases ha1 : a = 1
  · exact ⟨b, hb, c, hc, fun h => hab (ha1.trans h.symm), fun h => hac (ha1.trans h.symm), hbc⟩
  by_cases hb1 : b = 1
  · exact ⟨a, ha, c, hc, ha1, fun h => hbc (hb1.trans h.symm), hac⟩
  exact ⟨a, ha, b, hb, ha1, hb1, hab⟩

end TwoNe

section Lemma52

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β γ : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

namespace Prop46CaseB

variable (hC : Prop46CaseB G Ω α β γ v P)
include hC

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem card_eq_card_rootCenter {Y : Subgroup G}
    (hYR : Y ≤ caseBRad G Ω α β ⟨γ, hC.mem_holtDelta⟩) (hY2 : ∀ y ∈ Y, y * y = 1)
    (hYz : ∀ z ∈ rootCenter (seRadical (twoPointJ G Ω α β) ⟨γ, hC.mem_holtDelta⟩),
      ∃ y ∈ Y, ∃ hyP : y ∈ stabilizer G ({α, β} : Set Ω), twoPointHom G Ω α β ⟨y, hyP⟩ = z) :
    Nat.card Y = Nat.card (rootCenter (seRadical (twoPointJ G Ω α β) ⟨γ, hC.mem_holtDelta⟩)) := by
  refine Nat.card_eq_of_bijective (fun y : Y => (⟨twoPointHom G Ω α β
    ⟨y, (mem_caseBRad.mp (hYR y.2)).1⟩, (mem_caseBRad.mp (hYR y.2)).2.2.2⟩ : rootCenter _))
    ⟨fun y₁ y₂ h => ?_, fun ⟨z, hz⟩ => ?_⟩
  · have h' := congrArg Subtype.val h
    obtain ⟨h₁P, h₁α, h₁β, -⟩ := mem_caseBRad.mp (hYR y₁.2)
    obtain ⟨h₂P, h₂α, h₂β, -⟩ := mem_caseBRad.mp (hYR y₂.2)
    have hP : (y₁ : G)⁻¹ * y₂ ∈ stabilizer G ({α, β} : Set Ω) := mul_mem (inv_mem h₁P) h₂P
    have h1 : twoPointHom G Ω α β ⟨_, hP⟩ = 1 := by
      rw [show (⟨_, hP⟩ : stabilizer G ({α, β} : Set Ω)) = ⟨y₁, h₁P⟩⁻¹ * ⟨y₂, h₂P⟩ from rfl,
        map_mul, map_inv]
      exact inv_mul_eq_one.mpr h'
    have hα' : (y₁ : G)⁻¹ • α = α := by rw [inv_smul_eq_iff, h₁α]
    have hβ' : (y₁ : G)⁻¹ • β = β := by rw [inv_smul_eq_iff, h₁β]
    have := hC.eq_one_of_twoPointHom_eq_one hP (by rw [mul_smul, h₂α, hα'])
      (by rw [mul_smul, h₂β, hβ']) (hY2 _ (mul_mem (inv_mem y₁.2) y₂.2)) h1
    exact Subtype.ext (inv_mul_eq_one.mp this)
  · obtain ⟨y, hy, hyP, hyz⟩ := hYz z hz
    exact ⟨⟨y, hy⟩, Subtype.ext hyz⟩

omit [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem surj_of_fusionIsSylowIn {B Y : Subgroup G}
    (hB : B ≤ caseBRad G Ω α β ⟨γ, hC.mem_holtDelta⟩) (hYB : fusionIsSylowIn 2 Y B)
    (hBz : ∀ z ∈ rootCenter (seRadical (twoPointJ G Ω α β) ⟨γ, hC.mem_holtDelta⟩),
      ∃ y ∈ B, y * y = 1 ∧ ∃ hyP : y ∈ stabilizer G ({α, β} : Set Ω),
        twoPointHom G Ω α β ⟨y, hyP⟩ = z) :
    ∀ z ∈ rootCenter (seRadical (twoPointJ G Ω α β) ⟨γ, hC.mem_holtDelta⟩),
      ∃ y ∈ Y, ∃ hyP : y ∈ stabilizer G ({α, β} : Set Ω), twoPointHom G Ω α β ⟨y, hyP⟩ = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro z hz
  obtain ⟨y, hyB, hy2, hyP, hyz⟩ := hBz z hz
  obtain ⟨Y', hyY', hY'⟩ := exists_fusionIsSylowIn_ge
    (isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one, sq, hy2]))
    (Subgroup.zpowers_le.mpr hyB)
  obtain ⟨k, hkB, hk⟩ := exists_mem_conj_of_fusionIsSylowIn hYB hY'
  obtain ⟨hkP, -, -, hkZ⟩ := mem_caseBRad.mp (hB hkB)
  refine ⟨k⁻¹ * y * k, (hk y).mp (hyY' (Subgroup.mem_zpowers y)),
    mul_mem (mul_mem (inv_mem hkP) hyP) hkP, ?_⟩
  rw [show (⟨k⁻¹ * y * k, mul_mem (mul_mem (inv_mem hkP) hyP) hkP⟩ :
    stabilizer G ({α, β} : Set Ω)) = ⟨k, hkP⟩⁻¹ * ⟨y, hyP⟩ * ⟨k, hkP⟩ from rfl, map_mul,
    map_mul, map_inv, hyz, mul_assoc, Subgroup.mem_centralizer_iff.mp hkZ.2 z hz.1,
    inv_mul_cancel_left]

theorem false_of_witness_fix (hS : Sec4Setting G Ω) {β' γ' : Ω}
    (hC' : Prop46CaseB G Ω α β' γ' v P) {s : G} (hs : IsConj v s) (hsv : Commute s v)
    (hsΦ : fixedBy Ω s ≠ fixedBy Ω v) (hsα : s • α = α) (hsβ' : s • β' = β') : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h4, -⟩ := hC.exists_Y_of_witness hS hs hsv hsΦ
  obtain ⟨h4', -⟩ := hC'.exists_Y_of_witness hS hs hsv hsΦ
  obtain ⟨g, rfl⟩ := isConj_iff.mp hs
  have hrv : Commute (g⁻¹ * v * g) v := by
    have := hsv.eq
    change g⁻¹ * v * g * v = v * (g⁻¹ * v * g)
    calc g⁻¹ * v * g * v = g⁻¹ * (v * (g * v * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * v * g⁻¹) * v) * g := by rw [this]
      _ = v * (g⁻¹ * v * g) := by group
  have hr2 : g⁻¹ * v * g * (g⁻¹ * v * g) = 1 := by
    rw [show g⁻¹ * v * g * (g⁻¹ * v * g) = g⁻¹ * (v * v) * g by group, hC.v_mul_v, mul_one,
      inv_mul_cancel]
  obtain ⟨Y, hYR, hvY, hYmem, hYr, hYz⟩ := hC.exists_Y hS hrv hr2
  have hY4 : Nat.card Y = 4 :=
    (hC.card_eq_card_rootCenter hYR (fun y hy => (hYmem y hy).1) hYz).trans h4
  set R := Y.map (MulAut.conj g).toMonoidHom with hR
  have hmemR : ∀ {x : G}, x ∈ R ↔ ∃ y ∈ Y, g * y * g⁻¹ = x := fun {x} => by
    simp only [hR, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hR4 : Nat.card R = 4 := by
    rw [hR, Subgroup.card_map_of_injective (MulEquiv.injective _), hY4]
  have hRfix : ∀ x ∈ R, ∀ ω : Ω, (g * v * g⁻¹) • ω = ω → x • ω = ω := fun x hx ω hω => by
    obtain ⟨y, hy, rfl⟩ := hmemR.mp hx
    have hω' : v • (g⁻¹ • ω) = g⁻¹ • ω := by
      rw [← mul_smul, show v * g⁻¹ = g⁻¹ * (g * v * g⁻¹) by group, mul_smul, hω]
    rw [mul_smul, mul_smul, (hYmem y hy).2.2 _ hω', smul_inv_smul]
  have hR2 : IsPGroup 2 R := fun x => ⟨1, Subtype.ext (by
    obtain ⟨y, hy, hyx⟩ := hmemR.mp x.2
    simp only [pow_one, sq, Subgroup.coe_mul, Subgroup.coe_one, ← hyx]
    rw [show g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ by group, (hYmem y hy).1, mul_one,
      mul_inv_cancel])⟩
  have hvconj : ∀ x ∈ R, v * x * v⁻¹ ∈ R := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hmemR.mp hx
    exact hmemR.mpr ⟨(g⁻¹ * v * g) * y * (g⁻¹ * v * g)⁻¹, hYr y hy, by group⟩
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hC.v_mul_v
  have hvN : Subgroup.zpowers v ≤ Subgroup.normalizer (R : Set G) := Subgroup.zpowers_le.mpr
    (Subgroup.mem_normalizer_iff.mpr fun x => ⟨hvconj x, fun hx => by
      have := hvconj _ hx
      rwa [hvinv, ← mul_assoc, ← mul_assoc, hC.v_mul_v, one_mul, mul_assoc, hC.v_mul_v,
        mul_one] at this⟩)
  have hsP' : g * v * g⁻¹ ∈ stabilizer G ({α, β'} : Set Ω) :=
    stabilizer_inf_le_stabilizer_pair α β'
      (Subgroup.mem_inf.mpr ⟨mem_stabilizer_iff.mpr hsα, mem_stabilizer_iff.mpr hsβ'⟩)
  have hsγ' : (g * v * g⁻¹) • γ' = γ' :=
    (hC'.fixed_iff _ (smul_mem_holtDelta_of_mem_pair hsP' hC'.mem_holtDelta)).mp (by
      rw [← mul_smul, ← hsv.eq, mul_smul, hC'.smul_γ])
  have hRv : IsPGroup 2 ↥(R ⊔ Subgroup.zpowers v) :=
    hR2.to_sup_of_normal_left' (isPGroup_zpowers_of_orderOf_eq_two hC.orderOf_v) hvN
  have hRvle : R ⊔ Subgroup.zpowers v ≤ stabilizer G α ⊓ stabilizer G β' ⊓ stabilizer G γ' :=
    sup_le (fun x hx => Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
        ⟨mem_stabilizer_iff.mpr (hRfix x hx α hsα), mem_stabilizer_iff.mpr (hRfix x hx β' hsβ')⟩,
        mem_stabilizer_iff.mpr (hRfix x hx γ' hsγ')⟩)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
        ⟨mem_stabilizer_iff.mpr hC'.smul_α, mem_stabilizer_iff.mpr hC'.smul_β⟩,
        mem_stabilizer_iff.mpr hC'.smul_γ⟩))
  obtain ⟨T₁, hRT₁, hT₁⟩ := exists_fusionIsSylowIn_ge hRv hRvle
  set B' := caseBRad G Ω α β' ⟨γ', hC'.mem_holtDelta⟩ with hB'
  have hB'le : B' ≤ stabilizer G α ⊓ stabilizer G β' ⊓ stabilizer G γ' := fun x hx => by
    obtain ⟨hxP, hxα, hxβ, hxZ⟩ := mem_caseBRad.mp hx
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨mem_stabilizer_iff.mpr hxα,
      mem_stabilizer_iff.mpr hxβ⟩,
      mem_stabilizer_iff.mpr (congrArg Subtype.val (apply_eq_of_mem_seRadical hxZ.1))⟩
  have hB'N : stabilizer G α ⊓ stabilizer G β' ⊓ stabilizer G γ' ≤
      Subgroup.normalizer (B' : Set G) := fun k hk =>
    Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hC'.conj_mem_caseBRad
      (mem_stabilizer_iff.mp hk.1.1) (mem_stabilizer_iff.mp hk.1.2) (mem_stabilizer_iff.mp hk.2)
      hx, fun hx => by
        have hk' := inv_mem hk
        have := hC'.conj_mem_caseBRad (mem_stabilizer_iff.mp hk'.1.1)
          (mem_stabilizer_iff.mp hk'.1.2) (mem_stabilizer_iff.mp hk'.2) hx
        rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc,
          inv_mul_cancel, mul_one] at this⟩
  have hY'' : fusionIsSylowIn 2 (T₁ ⊓ B') B' :=
    fusionIsSylowIn_inf_of_le_normalizer hT₁ hB'le hB'N
  have hY''2 : ∀ y ∈ T₁ ⊓ B', y * y = 1 := fun y hy => by
    obtain ⟨hyP, hyα, hyβ, hyZ⟩ := mem_caseBRad.mp hy.2
    have hyyP : y * y ∈ stabilizer G ({α, β'} : Set Ω) := mul_mem hyP hyP
    have hK0 : y * y ∈ twoPointKernel G Ω α β' :=
      mem_twoPointKernel_of_twoPointHom_eq_one hyyP (by rw [mul_smul, hyα, hyα])
        (by rw [mul_smul, hyβ, hyβ]) (by
          rw [show (⟨y * y, hyyP⟩ : stabilizer G ({α, β'} : Set Ω)) = ⟨y, hyP⟩ * ⟨y, hyP⟩ from
            rfl, map_mul]
          exact hC'.isNaturalSE.mul_self_eq_one_of_mem_rootCenter hyZ)
    obtain ⟨k, hk⟩ := hT₁.2.1 ⟨y * y, mul_mem hy.1 hy.1⟩
    exact eq_one_of_isPGroup_of_odd hC'.odd_card hK0 (k := k) (by
      have := congrArg Subtype.val hk
      simpa using this)
  have hvY'' : v ∈ T₁ ⊓ B' :=
    ⟨hRT₁ ((le_sup_right : Subgroup.zpowers v ≤ _) (Subgroup.mem_zpowers v)),
      hC'.v_mem_caseBRad hS⟩
  have hY''mem : ∀ y ∈ T₁ ⊓ B', y * y = 1 ∧ Commute y v ∧ ∀ ω : Ω, v • ω = ω → y • ω = ω :=
    fun y hy => by
      have hyv : Commute y v := commute_of_forall_mul_self hY''2 hy hvY''
      exact ⟨hY''2 y hy, hyv, fun ω hω => hC'.smul_eq_of_mem_caseBRad hS hyv (hY''2 y hy) hy.2 hω⟩
  have hY''z := hC'.surj_of_fusionIsSylowIn le_rfl hY'' fun z hz => by
    obtain ⟨y, hyP, hyR, -, hy2, hyz⟩ := hC'.exists_mem_caseBRad_mul_self_eq_one hS hz
    exact ⟨y, hyR, hy2, hyP, hyz⟩
  have hY''4 : Nat.card ↥(T₁ ⊓ B') = 4 :=
    (hC'.card_eq_card_rootCenter inf_le_right hY''2 hY''z).trans h4'
  have hRY'' : ∀ ρ ∈ R, ∀ y ∈ T₁ ⊓ B', ρ * y * ρ⁻¹ ∈ T₁ ⊓ B' := fun ρ hρ y hy => by
    have hρT : ρ ∈ T₁ := hRT₁ ((le_sup_left : R ≤ _) hρ)
    have hρs := hRvle ((le_sup_left : R ≤ _) hρ)
    exact ⟨T₁.mul_mem (T₁.mul_mem hρT hy.1) (T₁.inv_mem hρT), hC'.conj_mem_caseBRad
      (mem_stabilizer_iff.mp hρs.1.1) (mem_stabilizer_iff.mp hρs.1.2) (mem_stabilizer_iff.mp hρs.2)
      hy.2⟩
  obtain ⟨ρ, hρR, hρ1, hρc⟩ := exists_ne_one_forall_commute_of_card_eq_four hR4 hY''4 hRY''
  obtain ⟨y₀, hy₀Y, rfl⟩ := hmemR.mp hρR
  have hy₀1 : y₀ ≠ 1 := fun h => hρ1 (by rw [h, mul_one, mul_inv_cancel])
  obtain ⟨hy₀c, hy₀F⟩ := hC.isConj_and_fixedBy_eq hS hYR hYmem hy₀Y hy₀1
  have hρc' : IsConj v (g * y₀ * g⁻¹) := hy₀c.trans (isConj_iff.mpr ⟨g, rfl⟩)
  have hρΦ : fixedBy Ω (g * y₀ * g⁻¹) ≠ fixedBy Ω v := by
    rw [← smul_fixedBy, hy₀F, smul_fixedBy]; exact hsΦ
  obtain ⟨u₁, hu₁, u₂, hu₂, h1, h2, h12⟩ :=
    exists_ne_one_ne_of_two_lt_card (Y := T₁ ⊓ B') (by rw [hY''4]; norm_num)
  exact hC'.false_of_witness_commute hS hρc' (hρc v hvY'') hρΦ (Y := T₁ ⊓ B') inf_le_right
    hY''mem hu₁ hu₂ h1 h2 h12 (hρc u₁ hu₁) (hρc u₂ hu₂)

end Prop46CaseB

end Lemma52

section B5

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β γ : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

namespace Prop46CaseB

variable (hC : Prop46CaseB G Ω α β γ v P)
include hC

open CFSG.Timmesfeld.Connectivity in
theorem exists_witness (hS : Sec4Setting G Ω) :
    ∃ s : G, IsConj v s ∧ Commute s v ∧ fixedBy Ω s ≠ fixedBy Ω v := by
  by_contra hno
  push Not at hno
  set D : Set G := {s | IsConj v s} with hD
  have hN : IsNormalSet D := fun g x hx => hx.trans (isConj_iff.mpr ⟨g, rfl⟩)
  have hD2 : CFSG.Timmesfeld.Bridge.IsInvolutionSet D := fun d hd =>
    (CFSG.Holt.orderOf_eq_of_isConj hd).symm.trans hC.orderOf_v
  have hfixD : ∀ x ∈ D, ∀ y ∈ D, Commute x y → fixedBy Ω x = fixedBy Ω y :=
    fun x hx y hy hxy => by
      obtain ⟨g, rfl⟩ := isConj_iff.mp hx
      have hy' : IsConj v (g⁻¹ * y * g) := (show IsConj v y from hy).trans
        (isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩)
      have hc : Commute (g⁻¹ * y * g) v := by
        have := hxy.eq
        change g⁻¹ * y * g * v = v * (g⁻¹ * y * g)
        calc g⁻¹ * y * g * v = g⁻¹ * (y * (g * v * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * v * g⁻¹) * y) * g := by rw [this]
          _ = v * (g⁻¹ * y * g) := by group
      have h := hno _ hy' hc
      rw [← smul_fixedBy, ← h, smul_fixedBy]
      congr 1; group
  have hnp : CFSG.Timmesfeld.Moufang.NoPolar D := fun x hx y hy hxy hne =>
    hC.isConj_mul hS hx hy hxy hne (hfixD x hx y hy hxy)
  obtain ⟨g, hg⟩ : ∃ g : G, fixedBy Ω (g * v * g⁻¹) ≠ fixedBy Ω v := by
    by_contra h
    push Not at h
    have := hS.star.isPretransitive
    have hv1 : v = 1 := eq_of_smul_eq_smul (α := Ω) fun ω => by
      obtain ⟨g, rfl⟩ := exists_smul_eq G α ω
      have hω : g • α ∈ fixedBy Ω (g * v * g⁻¹) := by
        rw [← smul_fixedBy]; exact Set.smul_mem_smul_set hC.smul_α
      rw [h g] at hω
      rw [one_smul]; exact hω
    have := hC.orderOf_v
    rw [hv1, orderOf_one] at this
    omega
  have hdisc : Disconnected D := ⟨v, IsConj.refl v, g * v * g⁻¹, isConj_iff.mpr ⟨g, rfl⟩,
    fun hreach => hg (by
      have key : ∀ z, Reach D v z → fixedBy Ω z = fixedBy Ω v := fun z hz => by
        induction hz with
        | refl => rfl
        | tail _ hbc ih => exact (hfixD _ hbc.1 _ hbc.2.1 hbc.2.2).symm.trans ih
      exact key _ hreach)⟩
  obtain ⟨M, hM⟩ := CFSG.Timmesfeld.Bridge.exists_fusionStronglyEmbedded_closure
    CFSG.ShultStronglyClosedTI.theoremTwo CFSG.Timmesfeld.Bridge.schurNarrowInput hN hD2 hnp hdisc
  have := hS.preprimitive
  have hLn : (Subgroup.closure D).Normal := ⟨fun n hn k => by
    induction hn using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hN k x hx)
    | one => simp
    | mul x y _ _ hx hy =>
      rw [show k * (x * y) * k⁻¹ = k * x * k⁻¹ * (k * y * k⁻¹) by group]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [show k * x⁻¹ * k⁻¹ = (k * x * k⁻¹)⁻¹ by group]
      exact inv_mem hx⟩
  have hvJ := mem_longInv_of_mem_of_fusionStronglyEmbedded hS.star hS.pPrimeCore_eq_bot hLn
    ⟨M, hM⟩ (Subgroup.subset_closure (IsConj.refl v)) hC.orderOf_v
  obtain ⟨-, -, -, -, -, -, -, hvnJ⟩ := hC.isTypeL
  exact hvnJ hvJ

theorem card_rootCenter_eq_four (hS : Sec4Setting G Ω) :
    Nat.card (rootCenter (seRadical (twoPointJ G Ω α β) ⟨γ, hC.mem_holtDelta⟩)) = 4 := by
  obtain ⟨s, hs, hsv, hsΦ⟩ := hC.exists_witness hS
  exact (hC.exists_Y_of_witness hS hs hsv hsΦ).1

end Prop46CaseB

end B5

end CFSG.Holt.H78
