module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P09Syl

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits
open scoped Pointwise

section Abstract

variable {Γ : Type*} [Group Γ]

theorem p05_mem_normalizer_centralizer {g t : Γ} (hg : g * t = t * g) :
    g ∈ normalizer ((centralizer ({t} : Set Γ) : Subgroup Γ) : Set Γ) := by
  have hc : Commute g t := hg
  rw [mem_normalizer_iff]
  intro h
  simp only [SetLike.mem_coe, mem_centralizer_singleton_iff]
  constructor
  · intro hh
    have : Commute (g * h * g⁻¹) t := (hc.mul_left (show Commute h t from hh)).mul_left hc.inv_left
    exact this
  · intro hh
    have h1 : Commute (g * h * g⁻¹) t := hh
    have h2 : Commute (g⁻¹ * (g * h * g⁻¹) * g) t := (hc.inv_left.mul_left h1).mul_left hc
    have e : g⁻¹ * (g * h * g⁻¹) * g = h := by group
    rw [e] at h2
    exact h2

theorem p05_card_sup_eq [Finite Γ] {K H M' : Subgroup Γ} (hKM : K ≤ M') (hHM : H ≤ M')
    (hn : M' ≤ normalizer (K : Set Γ)) :
    Nat.card (K ⊔ H : Subgroup Γ) = K.relIndex H * Nat.card K := by
  haveI : (K.subgroupOf M').Normal := (normal_subgroupOf_iff_le_normalizer hKM).2 hn
  have h := Subgroup.relIndex_sup_right (H := H.subgroupOf M') (K := K.subgroupOf M')
  rw [← Subgroup.subgroupOf_sup hHM hKM, Subgroup.relIndex_subgroupOf (sup_le hHM hKM),
    Subgroup.relIndex_subgroupOf hHM] at h
  have h2 := Subgroup.relIndex_mul_card (H := K) (K := H ⊔ K)
  rw [inf_of_le_left le_sup_right, h, sup_comm] at h2
  exact h2.symm

end Abstract

section Sylow

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem p05_sylT_le_N (hd : d.Hyp) : sylT d ≤ d.N := by
  intro g hg
  obtain ⟨hgt, hρ⟩ := p09_mem_sylT_iff.1 hg
  have hS : (d.ρ ⟨g, hgt⟩ : Equiv.Perm (Fin 1755)) ∈ CFSG.Quasithin.twoF4S := by
    rw [Model.twoF4S_eq_closure]
    exact hρ
  have hN : (d.ρ ⟨g, hgt⟩ : Equiv.Perm (Fin 1755)) ∈
      normalizer (Model.parrottF : Set (Equiv.Perm (Fin 1755))) := by
    have h := CFSG.Quasithin.twoF4S_le_twoF4N hS
    rw [← Model.titsA_inf_normalizer_parrottF] at h
    exact (mem_inf.1 h).2
  exact (hd.mem_normalizer_tSup_iff Model.parrottF_le_titsD hgt).2 hN

theorem p05_orbit_Q0 (h49 : d.Thm49Statement) (hd : d.Hyp) :
    {y | ∃ k ∈ d.s56Q0, k * d.t * k⁻¹ = y} = (fun e => d.t * e) '' (d.E : Set G) := by
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨d.s56Eps k, hd.s56_eps_mem_E (hd.s56_Q0_le_M h49 hk), (hd.s56_conj_t k).symm⟩
  · rintro ⟨e, he, rfl⟩
    obtain ⟨-, -, htrans, -⟩ := hd.s56_structure_M h49
    obtain ⟨q, hq, hqt⟩ := htrans e he
    exact ⟨q, hd.s56_Q2_le_Q0 h49 hq, hqt⟩

theorem p05_card_Q0 (h49 : d.Thm49Statement) (hd : d.Hyp) :
    Nat.card d.s56Q0 = 32 * Nat.card (d.s56Q0 ⊓ centralizer ({d.t} : Set G) : Subgroup G) := by
  have hcE : ((d.E : Set G)).ncard = 32 := by
    rw [← Nat.card_coe_set_eq]
    exact hd.A_facts.1
  have h := card_eq_ncard_conj_mul d.s56Q0 d.t
  rw [p05_orbit_Q0 h49 hd, Set.ncard_image_of_injective _ (mul_right_injective d.t), hcE] at h
  exact h

theorem p05_card_N_Q0 (h49 : d.Thm49Statement) (hd : d.Hyp) :
    Nat.card (d.N ⊓ d.s56Q0 : Subgroup G) =
      16 * Nat.card (d.s56Q0 ⊓ centralizer ({d.t} : Set G) : Subgroup G) := by
  have hC : (d.N ⊓ d.s56Q0) ⊓ centralizer ({d.t} : Set G) =
      d.s56Q0 ⊓ centralizer ({d.t} : Set G) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxNQ, hxC⟩ := mem_inf.1 hx
      exact mem_inf.2 ⟨(mem_inf.1 hxNQ).2, hxC⟩
    · intro hx
      obtain ⟨hxQ, hxC⟩ := mem_inf.1 hx
      have hxt : x * d.t = d.t * x := mem_centralizer_singleton_iff.1 hxC
      have hε : d.s56Eps x = 1 := by
        have e : x * d.t * x⁻¹ = d.t := by rw [hxt]; group
        rw [Data.s56Eps, e]
        exact hd.t_mul_self
      have hxN : x ∈ d.N := (hd.s56_mem_N_iff_eps h49 hxQ).2 (by rw [hε]; exact one_mem _)
      exact mem_inf.2 ⟨mem_inf.2 ⟨hxN, hxQ⟩, hxC⟩
  have horb : {y | ∃ k ∈ d.N ⊓ d.s56Q0, k * d.t * k⁻¹ = y} =
      (fun f => d.t * f) '' ((d.E ⊓ d.F : Subgroup G) : Set G) := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨hkN, hkQ⟩ := mem_inf.1 hk
      exact ⟨d.s56Eps k, mem_inf.2 ⟨hd.s56_eps_mem_E (hd.s56_Q0_le_M h49 hkQ),
        hd.s56_eps_mem_F_of_N h49 hkN⟩, (hd.s56_conj_t k).symm⟩
    · rintro ⟨f, hf, rfl⟩
      obtain ⟨hfE, hfF⟩ := mem_inf.1 hf
      obtain ⟨-, -, htrans, -⟩ := hd.s56_structure_M h49
      obtain ⟨q, hq, hqt⟩ := htrans f hfE
      have hq0 := hd.s56_Q2_le_Q0 h49 hq
      have hqε : d.s56Eps q = f := by
        rw [Data.s56Eps, hqt, ← mul_assoc, hd.t_mul_self, one_mul]
      have hqN : q ∈ d.N := (hd.s56_mem_N_iff_eps h49 hq0).2 (by rw [hqε]; exact hfF)
      exact ⟨q, mem_inf.2 ⟨hqN, hq0⟩, hqt⟩
  have hcEF : (((d.E ⊓ d.F : Subgroup G) : Set G)).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact hd.s56_card_E_inf_F
  have h := card_eq_ncard_conj_mul (d.N ⊓ d.s56Q0) d.t
  rw [horb, Set.ncard_image_of_injective _ (mul_right_injective d.t), hcEF, hC] at h
  exact h

theorem p05_relIndex_Q0 (h49 : d.Thm49Statement) (hd : d.Hyp) : d.N.relIndex d.s56Q0 = 2 := by
  have h1 := Subgroup.relIndex_mul_card (H := d.N) (K := d.s56Q0)
  rw [p05_card_N_Q0 h49 hd, p05_card_Q0 h49 hd] at h1
  have hpos : 0 < 16 * Nat.card (d.s56Q0 ⊓ centralizer ({d.t} : Set G) : Subgroup G) :=
    Nat.mul_pos (by norm_num) Nat.card_pos
  have h5 : d.N.relIndex d.s56Q0 *
      (16 * Nat.card (d.s56Q0 ⊓ centralizer ({d.t} : Set G) : Subgroup G)) =
      2 * (16 * Nat.card (d.s56Q0 ⊓ centralizer ({d.t} : Set G) : Subgroup G)) := by
    rw [h1]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos h5

theorem p05_CQ0t_le_sylT (hd : d.Hyp) :
    d.s56Q0 ⊓ centralizer ({d.t} : Set G) ≤ sylT d := by
  have hsyl := p09_sylow hd
  have hTM := p09_sylT_le_M hd
  have hXp : IsPGroup 2 (d.s56Q0 ⊓ centralizer ({d.t} : Set G) : Subgroup G) :=
    (d.s56_Q0_isPGroup).to_inf_left
  have hN : sylT d ≤ normalizer ((d.s56Q0 ⊓ centralizer ({d.t} : Set G) : Subgroup G) : Set G) := by
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf (mem_inf.2
      ⟨d.s56_M_le_normalizer_Q0 (hTM hg),
        p05_mem_normalizer_centralizer (mem_centralizer_singleton_iff.1 (p09_sylT_le_C hg))⟩)
  have hpg : IsPGroup 2 (d.s56Q0 ⊓ centralizer ({d.t} : Set G) ⊔ sylT d : Subgroup G) :=
    hXp.to_sup_of_normal_left' hsyl.2.1 hN
  have heq := hsyl.2.2 _ (sup_le inf_le_right p09_sylT_le_C) hpg le_sup_right
  exact le_sup_left.trans heq.le

theorem p05_card_sup (h49 : d.Thm49Statement) (hd : d.Hyp) :
    Nat.card (d.s56Q0 ⊔ sylT d : Subgroup G) = 32 * Nat.card (sylT d) := by
  have h1 := p05_card_sup_eq (hd.s56_Q0_le_M h49) (p09_sylT_le_M hd) (d.s56_M_le_normalizer_Q0)
  have h2 := Subgroup.relIndex_mul_card (H := d.s56Q0) (K := sylT d)
  have h3 : d.s56Q0 ⊓ sylT d = d.s56Q0 ⊓ centralizer ({d.t} : Set G) :=
    le_antisymm (inf_le_inf_left _ p09_sylT_le_C) (le_inf inf_le_left (p05_CQ0t_le_sylT hd))
  rw [h3] at h2
  rw [h1, p05_card_Q0 h49 hd, ← h2]
  ring

theorem p05_isPGroup_sup (hd : d.Hyp) : IsPGroup 2 (d.s56Q0 ⊔ sylT d : Subgroup G) :=
  (d.s56_Q0_isPGroup).to_sup_of_normal_left' (p09_sylow hd).2.1
    ((p09_sylT_le_M hd).trans (d.s56_M_le_normalizer_Q0))

theorem p05_sylow_M (h49 : d.Thm49Statement) (hd : d.Hyp) :
    fusionIsSylowIn 2 (d.s56Q0 ⊔ sylT d) d.M := by
  have hsyl := p09_sylow hd
  refine ⟨sup_le (hd.s56_Q0_le_M h49) (p09_sylT_le_M hd), p05_isPGroup_sup hd,
    fun P hPM hP hSP => ?_⟩
  have hTP : sylT d ≤ P := le_sup_right.trans hSP
  have hCP : P ⊓ centralizer ({d.t} : Set G) = sylT d :=
    hsyl.2.2 _ inf_le_right hP.to_inf_left (le_inf hTP p09_sylT_le_C)
  have horb : {y | ∃ k ∈ P, k * d.t * k⁻¹ = y} ⊆ (fun e => d.t * e) '' (d.E : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨d.s56Eps k, hd.s56_eps_mem_E (hPM hk), (hd.s56_conj_t k).symm⟩
  have hcE : ((fun e => d.t * e) '' (d.E : Set G)).ncard = 32 := by
    rw [Set.ncard_image_of_injective _ (mul_right_injective d.t), ← Nat.card_coe_set_eq]
    exact hd.A_facts.1
  have hcard := card_eq_ncard_conj_mul P d.t
  rw [hCP] at hcard
  have hle : Nat.card P ≤ 32 * Nat.card (sylT d) := by
    rw [hcard]
    exact Nat.mul_le_mul_right _ ((Set.ncard_le_ncard horb (Set.toFinite _)).trans hcE.le)
  exact (Subgroup.eq_of_le_of_card_ge hSP (by rw [p05_card_sup h49 hd]; exact hle)).symm

theorem p05_relIndex_sup (h49 : d.Thm49Statement) (hd : d.Hyp) :
    d.N.relIndex (d.s56Q0 ⊔ sylT d) = 2 := by
  have hTN := p05_sylT_le_N hd
  have hTM := p09_sylT_le_M hd
  have hQM := hd.s56_Q0_le_M h49
  have hnQ : d.M ≤ normalizer (d.s56Q0 : Set G) := d.s56_M_le_normalizer_Q0
  have hsup : d.N ⊓ (d.s56Q0 ⊔ sylT d) = (d.N ⊓ d.s56Q0) ⊔ sylT d := by
    apply le_antisymm
    · intro s hs
      obtain ⟨hsN, hsS⟩ := mem_inf.1 hs
      have hmul := coe_mul_of_right_le_normalizer_left d.s56Q0 (sylT d) (hTM.trans hnQ)
      have hs' : s ∈ (d.s56Q0 : Set G) * (sylT d : Set G) := by
        rw [← hmul]
        exact hsS
      obtain ⟨q, hq, t', ht', rfl⟩ := hs'
      have hqN : q ∈ d.N := by
        have h := mul_mem hsN (inv_mem (hTN ht'))
        simpa using h
      exact mul_mem (mem_sup_left (mem_inf.2 ⟨hqN, hq⟩)) (mem_sup_right ht')
    · exact sup_le (inf_le_inf_left _ le_sup_left) (le_inf hTN le_sup_right)
  have hn' : d.N ⊓ d.M ≤ normalizer ((d.N ⊓ d.s56Q0 : Subgroup G) : Set G) := by
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf (mem_inf.2
      ⟨Subgroup.le_normalizer (mem_inf.1 hg).1, hnQ (mem_inf.1 hg).2⟩)
  have h1 := p05_card_sup_eq (inf_le_inf_left d.N hQM) (le_inf hTN hTM) hn'
  have h2 := p05_card_sup_eq hQM hTM hnQ
  have hrel : (d.N ⊓ d.s56Q0).relIndex (sylT d) = d.s56Q0.relIndex (sylT d) := by
    have e : d.N ⊓ d.s56Q0 ⊓ sylT d = d.s56Q0 ⊓ sylT d := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxNQ, hxT⟩ := mem_inf.1 hx
        exact mem_inf.2 ⟨(mem_inf.1 hxNQ).2, hxT⟩
      · intro hx
        obtain ⟨hxQ, hxT⟩ := mem_inf.1 hx
        exact mem_inf.2 ⟨mem_inf.2 ⟨hTN hxT, hxQ⟩, hxT⟩
    rw [← Subgroup.inf_relIndex_right (d.N ⊓ d.s56Q0) (sylT d), e, Subgroup.inf_relIndex_right]
  have hQ : Nat.card d.s56Q0 = 2 * Nat.card (d.N ⊓ d.s56Q0 : Subgroup G) := by
    have h := Subgroup.relIndex_mul_card (H := d.N) (K := d.s56Q0)
    rw [p05_relIndex_Q0 h49 hd] at h
    exact h.symm
  have hS : Nat.card (d.s56Q0 ⊔ sylT d : Subgroup G) =
      2 * Nat.card (d.N ⊓ (d.s56Q0 ⊔ sylT d) : Subgroup G) := by
    rw [hsup, h1, h2, hrel, hQ]
    ring
  have h3 := Subgroup.relIndex_mul_card (H := d.N) (K := d.s56Q0 ⊔ sylT d)
  rw [hS] at h3
  have hpos : 0 < Nat.card (d.N ⊓ (d.s56Q0 ⊔ sylT d) : Subgroup G) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos h3

theorem node05_index_sylow (h49 : d.Thm49Statement) (hd : d.Hyp) :
    d.N.relIndex d.s56Q0 = 2 ∧ fusionIsSylowIn 2 (d.s56Q0 ⊔ sylT d) d.M ∧
      d.N.relIndex (d.s56Q0 ⊔ sylT d) = 2 :=
  ⟨p05_relIndex_Q0 h49 hd, p05_sylow_M h49 hd, p05_relIndex_sup h49 hd⟩

end Sylow

end CFSG.LocalAnalysis.EvenBN.Tits.N
