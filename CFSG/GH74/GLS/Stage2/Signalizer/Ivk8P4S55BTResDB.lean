module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResDA
public import CFSG.GH74.GLS.Stage2.Local.P27.P1Main

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResD

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
open CFSG.GH74.GLS.Stage2.Final.Thm6.L20 (PairShape)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem barOf_perfect {A : Subgroup G} (hAC : A ≤ Cen z) (hA : ⁅A, A⁆ = A) :
    ⁅barOf z A, barOf z A⁆ = barOf z A := by
  have h1 : ⁅A.subgroupOf (Cen z), A.subgroupOf (Cen z)⁆ = A.subgroupOf (Cen z) := by
    apply Subgroup.map_injective (Cen z).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hAC, hA]
  rw [barOf, ← Subgroup.map_commutator, h1]

omit [Finite G] in
theorem swaps_conj {L₁ L₂ : Subgroup (CentralizerBar z)} {s : G} (hsC : s ∈ Cen z)
    (hsw : Swaps z s L₁ L₂) :
    (∀ a ∈ L₁, toBar z ⟨s, hsC⟩ * a * (toBar z ⟨s, hsC⟩)⁻¹ ∈ L₂) ∧
      ∀ b ∈ L₂, toBar z ⟨s, hsC⟩ * b * (toBar z ⟨s, hsC⟩)⁻¹ ∈ L₁ := by
  obtain ⟨ht', h1, h2⟩ := hsw
  constructor
  · intro a ha
    have ha' : a ∈ conjugate L₂ (toBar z ⟨s, hsC⟩) := h2 ▸ ha
    obtain ⟨b, hb, hba⟩ := ha'
    have e : toBar z ⟨s, hsC⟩ * a * (toBar z ⟨s, hsC⟩)⁻¹ = b := by
      rw [← hba]
      simp [mul_assoc]
    rw [e]
    exact hb
  · intro b hb
    have hb' : b ∈ conjugate L₁ (toBar z ⟨s, hsC⟩) := h1 ▸ hb
    obtain ⟨a, ha, hab⟩ := hb'
    have e : toBar z ⟨s, hsC⟩ * b * (toBar z ⟨s, hsC⟩)⁻¹ = a := by
      rw [← hab]
      simp [mul_assoc]
    rw [e]
    exact ha

theorem diag_perfect {L₁ L₂ : Subgroup (CentralizerBar z)} (h : PairShape L₁ L₂)
    {s : CentralizerBar z} (hs₁ : ∀ a ∈ L₁, s * a * s⁻¹ ∈ L₂) :
    ⁅(CFSG.GH74.GLS.Stage2.Final.Thm6.L20.diagHom L₁ L₂ s hs₁ h.comm).range,
      (CFSG.GH74.GLS.Stage2.Final.Thm6.L20.diagHom L₁ L₂ s hs₁ h.comm).range⁆ =
      (CFSG.GH74.GLS.Stage2.Final.Thm6.L20.diagHom L₁ L₂ s hs₁ h.comm).range := by
  have hperf : ⁅(⊤ : Subgroup ↥L₁), (⊤ : Subgroup ↥L₁)⁆ = ⊤ := by
    have := h.c₁.1.1
    rw [← commutator_def]
    exact Group.isPerfect_def.mp this
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hperf]

theorem diag_le_barOf {S : Subgroup G} {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hz : IsCentralInvolution z) (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z))
    (hP : Stage1Pair G z S q L₁ L₂) {s : G} (hsS : s ∈ S) (hsc : IsConj z s)
    (hsw : Swaps z s L₁ L₂) (hsC : s ∈ Cen z) {I : Subgroup G} (hIC : I ≤ Cen z)
    (hIs : I ≤ centralizer ({s} : Set G)) (hIp : ⁅I, I⁆ = I) {O : Subgroup G} (hOC : O ≤ Cen z)
    (hOodd : Odd (Nat.card ↥O))
    (hOn : ∀ l ∈ Ixz z (s * z), ∀ o ∈ O, l * o * l⁻¹ ∈ O)
    (hcov : ∀ l ∈ Ixz z (s * z), ∃ i ∈ I, ∃ o ∈ O, l = i * o) :
    ∀ a ∈ L₁, a * (toBar z ⟨s, hsC⟩ * a * (toBar z ⟨s, hsC⟩)⁻¹) ∈ barOf z I := by
  set sb : CentralizerBar z := toBar z ⟨s, hsC⟩ with hsb
  have h := CFSG.GH74.GLS.Stage2.Final.Thm6.L20.PairShape.of_stage1Pair hP
  obtain ⟨hs₁, hs₂⟩ := swaps_conj hsC hsw
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz.1, pow_two] at this
  have hss : s * s = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hsc
    rw [← hc]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hsb2 : sb * sb = 1 := by
    rw [hsb, ← map_mul]
    have : (⟨s, hsC⟩ : ↥(Cen z)) * ⟨s, hsC⟩ = 1 := Subtype.ext hss
    rw [this, map_one]
  set δf := CFSG.GH74.GLS.Stage2.Final.Thm6.L20.diagHom L₁ L₂ sb hs₁ h.comm with hδf
  have hIbar_le : barOf z I ≤ δf.range := by
    refine CFSG.GH74.GLS.Stage2.Final.Thm6.L20.perfect_le_diag h.comm hs₁ hs₂
      (barOf_perfect hIC hIp) ?_ ?_
    · rw [← h.fitting]
      exact CFSG.GH74.GLS.Stage2.Final.Thm6.L20.PairShape.perfect_le h (barOf_perfect hIC hIp)
        |>.trans (by rw [h.fitting])
    · rintro _ ⟨i, hi, rfl⟩
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have hcomm : (i : G) * s = s * i :=
        Subgroup.mem_centralizer_singleton_iff.mp (hIs (Subgroup.mem_subgroupOf.mp hi))
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hcomm]
      group
  obtain ⟨-, A, hA, -, -, hmax⟩ := P27.ixz_L2_ext hz hS hP hsS hsc hsw
  have hΔK : δf.range ≤ L₁ ⊔ L₂ := by
    rintro _ ⟨a, rfl⟩
    exact CFSG.GH74.GLS.Stage2.Final.Thm6.L20.diagHom_mem_sup h.comm hs₁ a
  have hΔCL : δf.range ≤ CL z s := by
    rintro _ ⟨a, rfl⟩
    have hmem := CFSG.GH74.GLS.Stage2.Final.Thm6.L20.diagHom_mem h.comm hsb2 hs₁ a
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← hP.prod.1]
      exact hmem.1
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hy)
      have hyk : y = (⟨s, hsC⟩ : ↥(Cen z)) ^ k := Subtype.ext (by simp [hk])
      have hc : sb * δf a = δf a * sb :=
        (Subgroup.mem_centralizer_singleton_iff.mp hmem.2).symm
      rw [hyk, map_zpow]
      exact ((Commute.zpow_left hc k)).eq
  have hΔA : δf.range ≤ A := hmax _ hΔCL (diag_perfect h hs₁)
  have hoddO : Odd (Nat.card ↥(barOf z O)) := by
    have h1 := Subgroup.card_map_dvd (O.subgroupOf (Cen z)) (toBar z)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOC).toEquiv] at h1
    exact Odd.of_dvd_nat hOodd h1
  have hN₀ : δf.range ⊓ barOf z O = ⊥ := by
    refine eq_bot_of_odd h hsb2 hs₁ hs₂ (inf_le_left.trans hΔK)
      (Odd.of_dvd_nat hoddO (Subgroup.card_dvd_of_le inf_le_right)) ?_
    intro a' ha' n hn
    have hδ' : δf ⟨a', ha'⟩ ∈ δf.range := ⟨⟨a', ha'⟩, rfl⟩
    change δf ⟨a', ha'⟩ * n * (δf ⟨a', ha'⟩)⁻¹ ∈ δf.range ⊓ barOf z O
    refine ⟨δf.range.mul_mem (δf.range.mul_mem hδ' hn.1) (δf.range.inv_mem hδ'), ?_⟩
    have hδA := hΔA hδ'
    rw [← hA] at hδA
    obtain ⟨l, hl, hle⟩ := hδA
    obtain ⟨o, ho, rfl⟩ := hn.2
    rw [← hle, ← map_inv, ← map_mul, ← map_mul]
    refine ⟨l * o * l⁻¹, ?_, rfl⟩
    exact hOn l (Subgroup.mem_subgroupOf.mp hl) o (Subgroup.mem_subgroupOf.mp ho)
  intro a ha
  have hδ : δf ⟨a, ha⟩ ∈ A := hΔA ⟨⟨a, ha⟩, rfl⟩
  rw [← hA] at hδ
  obtain ⟨l, hl, hle⟩ := hδ
  obtain ⟨i, hi, o, ho, hlio⟩ := hcov l (Subgroup.mem_subgroupOf.mp hl)
  have hiC : i ∈ Cen z := hIC hi
  have hoC : o ∈ Cen z := hOC ho
  have hsplit : toBar z ⟨i, hiC⟩ * toBar z ⟨o, hoC⟩ = δf ⟨a, ha⟩ := by
    rw [← hle, ← map_mul]
    congr 1
    exact Subtype.ext hlio.symm
  have hφi : toBar z ⟨i, hiC⟩ ∈ δf.range := hIbar_le ⟨⟨i, hiC⟩, hi, rfl⟩
  have hφo : toBar z ⟨o, hoC⟩ ∈ δf.range ⊓ barOf z O := by
    refine ⟨?_, ⟨⟨o, hoC⟩, ho, rfl⟩⟩
    have e : toBar z ⟨o, hoC⟩ = (toBar z ⟨i, hiC⟩)⁻¹ * δf ⟨a, ha⟩ := by
      rw [← hsplit]
      group
    rw [e]
    exact δf.range.mul_mem (δf.range.inv_mem hφi) ⟨⟨a, ha⟩, rfl⟩
  rw [hN₀, Subgroup.mem_bot] at hφo
  have e : δf ⟨a, ha⟩ = toBar z ⟨i, hiC⟩ := by rw [← hsplit, hφo, mul_one]
  change δf ⟨a, ha⟩ ∈ barOf z I
  rw [e]
  exact ⟨⟨i, hiC⟩, hi, rfl⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResD
