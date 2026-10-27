module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Defs
public import CFSG.LocalAnalysis.EvenBN.Tits.S56P11

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits

section Syl

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem p09_mem_sylT_iff {g : G} :
    g ∈ sylT d ↔ ∃ hg : g ∈ centralizer ({d.t} : Set G),
      (d.ρ ⟨g, hg⟩ : Equiv.Perm (Fin 1755)) ∈ Model.parrottU 1 := by
  unfold sylT
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, by simpa [Subgroup.mem_comap, Subgroup.mem_subgroupOf] using hx⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, by simpa [Subgroup.mem_comap, Subgroup.mem_subgroupOf] using h, rfl⟩

theorem p09_sylT_le_C : sylT d ≤ centralizer ({d.t} : Set G) := fun _ hg =>
  (p09_mem_sylT_iff.1 hg).1

theorem p09_t_mem_sylT (hd : d.Hyp) : d.t ∈ sylT d := by
  rw [p09_mem_sylT_iff]
  refine ⟨d.t_mem_centralizer, ?_⟩
  rw [hd.ρ_t]
  exact one_mem _

theorem p09_sylT_le_M (hd : d.Hyp) : sylT d ≤ d.M := by
  intro g hg
  obtain ⟨hgt, hρ⟩ := p09_mem_sylT_iff.1 hg
  have hS : (d.ρ ⟨g, hgt⟩ : Equiv.Perm (Fin 1755)) ∈ CFSG.Quasithin.twoF4S := by
    rw [Model.twoF4S_eq_closure]
    exact hρ
  have hN : (d.ρ ⟨g, hgt⟩ : Equiv.Perm (Fin 1755)) ∈
      normalizer (Model.hatE : Set (Equiv.Perm (Fin 1755))) :=
    Model.twoF4H_le_normalizer_hatE (Model.twoF4S_le_twoF4H hS)
  exact (hd.mem_normalizer_tSup_iff (X := Model.hatE)
    (Model.hatE_le_titsJ.trans titsJ_le_titsD) hgt).2 hN

theorem p09_parrottV_mem (i : ℕ) : Model.parrottV i ∈ Model.parrottU 1 := by
  rw [← Model.twoF4S_eq_closure]
  exact Model.parrottV_mem_twoF4S i

theorem p09_parrottU_le_titsA : Model.parrottU 1 ≤ titsA := by
  rw [← Model.twoF4S_eq_closure]
  exact Model.twoF4S_le_twoF4H.trans Model.twoF4H_le_titsA

theorem p09_card_parrottU : Nat.card ((Model.parrottU 1).subgroupOf titsA) = 4096 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe p09_parrottU_le_titsA).toEquiv,
    ← Model.twoF4S_eq_closure]
  exact Model.card_twoF4S.1

theorem p09_card_sylT (hd : d.Hyp) :
    Nat.card (sylT d) =
      2 * Nat.card (d.ρ.range ⊓ (Model.parrottU 1).subgroupOf titsA : Subgroup titsA) := by
  have hsub : (sylT d).subgroupOf (centralizer ({d.t} : Set G)) =
      ((Model.parrottU 1).subgroupOf titsA).comap d.ρ :=
    Subgroup.comap_map_eq_self_of_injective (subtype_injective _) _
  rw [hd.card_eq_two_mul_map p09_sylT_le_C (p09_t_mem_sylT hd), hsub, Subgroup.map_comap_eq]

theorem p09_card_cases (hd : d.Hyp) :
    (Nat.card (sylT d) = 2 ^ 12 ∧ Nat.card (centralizer ({d.t} : Set G)) = 2 ^ 12 * 8775) ∨
      (Nat.card (sylT d) = 2 ^ 13 ∧ Nat.card (centralizer ({d.t} : Set G)) = 2 ^ 13 * 8775) := by
  have hT := p09_card_sylT hd
  have hC := hd.card_centralizer_eq_two_mul Model.hypothesisOneStar_titsD
  rcases hd.range_ρ with hR | hR
  · left
    rw [hR] at hT hC
    have hD : Nat.card (titsD.subgroupOf titsA) = 17971200 :=
      (Nat.card_congr (subgroupOfEquivOfLe titsD_le_titsA).toEquiv).trans card_titsD
    have hI : Nat.card (titsD.subgroupOf titsA ⊓ (Model.parrottU 1).subgroupOf titsA :
        Subgroup titsA) = 2048 := by
      rw [inf_comm, Data.card_inf_titsD p09_parrottU_le_titsA, ← Model.twoF4S_eq_closure,
        Model.card_twoF4S.2]
      exact titsQS_facts.2.2.2
    rw [hI] at hT
    rw [hD] at hC
    exact ⟨by rw [hT]; norm_num, by rw [hC]; norm_num⟩
  · right
    rw [hR] at hT hC
    rw [top_inf_eq, p09_card_parrottU] at hT
    rw [Subgroup.card_top, card_titsA] at hC
    exact ⟨by rw [hT]; norm_num, by rw [hC]; norm_num⟩

theorem p09_sylow (hd : d.Hyp) :
    fusionIsSylowIn 2 (sylT d) (centralizer ({d.t} : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, hkC⟩ : ∃ k : ℕ, Nat.card (sylT d) = 2 ^ k ∧
      Nat.card (centralizer ({d.t} : Set G)) = 2 ^ k * 8775 := by
    rcases p09_card_cases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨12, h1, h2⟩
    · exact ⟨13, h1, h2⟩
  refine ⟨p09_sylT_le_C, IsPGroup.of_card hk, fun P hPC hP hTP => ?_⟩
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  have hdvd := Subgroup.card_dvd_of_le hPC
  rw [hm, hkC] at hdvd
  have hcop : Nat.Coprime (2 ^ m) 8775 := Nat.Coprime.pow_left m (by norm_num)
  have hle : 2 ^ m ≤ 2 ^ k := Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right hdvd)
  exact (Subgroup.eq_of_le_of_card_ge hTP (by rw [hm, hk]; exact hle)).symm

theorem p09_t_not_mem (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    d.t ∉ sylT d ⊓ centralizer ({z₀} : Set G) := by
  intro h
  have h1 : d.t * z₀ = z₀ * d.t := mem_centralizer_singleton_iff.1 (mem_inf.1 h).2
  have h2 : z₀ * d.t * z₀⁻¹ = d.t := by rw [← h1]; group
  have h3 := hd.s56_z0_conj_t hz
  rw [h2] at h3
  exact hd.s56_z_ne_one (mul_left_cancel (h3.symm.trans (mul_one d.t).symm))

theorem p09_comm_or (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) {g : G}
    (hg : g ∈ sylT d) : g * z₀ = z₀ * g ∨ d.t * g * z₀ = z₀ * (d.t * g) := by
  have hc := hd.s56_M_comm_z0 h49 hz (p09_sylT_le_M hd hg)
  rcases hd.s56_mem_zpowers_z hc with h | h
  · left
    calc g * z₀ = (g * z₀ * g⁻¹ * z₀⁻¹) * (z₀ * g) := by group
      _ = z₀ * g := by rw [h, one_mul]
  · right
    have h1 : g * z₀ = d.z * z₀ * g :=
      calc g * z₀ = (g * z₀ * g⁻¹ * z₀⁻¹) * z₀ * g := by group
        _ = d.z * z₀ * g := by rw [h]
    have h2 : z₀ * d.t = d.t * d.z * z₀ :=
      calc z₀ * d.t = (z₀ * d.t * z₀⁻¹) * z₀ := by group
        _ = d.t * d.z * z₀ := by rw [hd.s56_z0_conj_t hz]
    calc d.t * g * z₀ = d.t * (g * z₀) := by group
      _ = d.t * (d.z * z₀ * g) := by rw [h1]
      _ = (d.t * d.z * z₀) * g := by group
      _ = (z₀ * d.t) * g := by rw [h2]
      _ = z₀ * (d.t * g) := by group

theorem p09_adjust (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) {g : G}
    (hg : g ∈ sylT d) :
    ∃ g' : G, g' ∈ sylT d ∧ g' * z₀ = z₀ * g' ∧ (g' = g ∨ g' = d.t * g) ∧
      ∃ hg' : g' ∈ centralizer ({d.t} : Set G),
        (d.ρ ⟨g', hg'⟩ : Equiv.Perm (Fin 1755)) = d.ρ ⟨g, p09_sylT_le_C hg⟩ := by
  rcases p09_comm_or h49 hd hz hg with h | h
  · exact ⟨g, hg, h, Or.inl rfl, p09_sylT_le_C hg, rfl⟩
  · have hgC := p09_sylT_le_C hg
    have htC : d.t * g ∈ centralizer ({d.t} : Set G) := mul_mem d.t_mem_centralizer hgC
    have e : (⟨d.t * g, htC⟩ : centralizer ({d.t} : Set G)) =
        ⟨d.t, d.t_mem_centralizer⟩ * ⟨g, hgC⟩ := rfl
    refine ⟨d.t * g, mul_mem (p09_t_mem_sylT hd) hg, h, Or.inr rfl, htC, ?_⟩
    rw [e, map_mul, hd.ρ_t, one_mul]

theorem p09_sylT_eq (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    sylT d = zpowers d.t ⊔ (sylT d ⊓ centralizer ({z₀} : Set G)) := by
  apply le_antisymm
  · intro g hg
    rcases p09_comm_or h49 hd hz hg with h | h
    · exact mem_sup_right (mem_inf.2 ⟨hg, mem_centralizer_singleton_iff.2 h⟩)
    · have htg : d.t * g ∈ sylT d ⊓ centralizer ({z₀} : Set G) :=
        mem_inf.2 ⟨mul_mem (p09_t_mem_sylT hd) hg, mem_centralizer_singleton_iff.2 h⟩
      have e : g = d.t * (d.t * g) := by rw [← mul_assoc, hd.t_mul_self, one_mul]
      rw [e]
      exact mul_mem (mem_sup_left (mem_zpowers d.t)) (mem_sup_right htg)
  · exact sup_le (zpowers_le.2 (p09_t_mem_sylT hd)) inf_le_left

theorem p09_v1v5_mem_titsD : Model.parrottV 1 * Model.parrottV 5 ∈ titsD := by
  have h15 : (([1, 5] : List ℕ).map Model.parrottV).prod ∈ titsK :=
    Model.kWords_mem_titsK [1, 5] (by decide)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h15
  exact titsK_le_titsD h15

theorem p09_sq_v1v5 :
    (Model.parrottV 1 * Model.parrottV 5) * (Model.parrottV 1 * Model.parrottV 5) =
      Model.parrottV 2 * Model.parrottV 12 := by
  obtain ⟨s1, -, s5, -, -⟩ := Model.parrott_squares
  have hcomm : Model.parrottV 1 * Model.parrottV 5 = Model.parrottV 5 * Model.parrottV 1 :=
    Model.parrottV_commute le_rfl (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide)
  calc (Model.parrottV 1 * Model.parrottV 5) * (Model.parrottV 1 * Model.parrottV 5)
      = Model.parrottV 1 * (Model.parrottV 5 * Model.parrottV 1) * Model.parrottV 5 := by group
    _ = Model.parrottV 1 * (Model.parrottV 1 * Model.parrottV 5) * Model.parrottV 5 := by
        rw [← hcomm]
    _ = (Model.parrottV 1 * Model.parrottV 1) * (Model.parrottV 5 * Model.parrottV 5) := by group
    _ = Model.parrottV 2 * Model.parrottV 12 := by rw [s1, s5]

theorem p09_lift_sq :
    d.lift (Model.parrottV 1 * Model.parrottV 5) * d.lift (Model.parrottV 1 * Model.parrottV 5) =
      d.pv 2 * d.z := by
  have h2 : Model.parrottV 2 ∈ titsD :=
    (Model.parrottV_mem_titsD_iff (by norm_num)).2 (by decide)
  have h12 : Model.parrottV 12 ∈ titsD := by
    rw [Model.parrottV_twelve]
    exact titsZ_mem_titsD
  rw [← d.lift_mul p09_v1v5_mem_titsD p09_v1v5_mem_titsD, p09_sq_v1v5, d.lift_mul h2 h12]
  exact congrArg _ (Data.s56_pv12 d)

theorem p09_exists_y1 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    ∃ y₁ : G, IsV1 d z₀ y₁ ∧ y₁ * y₁ = d.pv 2 * d.z := by
  obtain ⟨y, hy⟩ : ∃ y : G, y = d.lift (Model.parrottV 1 * Model.parrottV 5) := ⟨_, rfl⟩
  have hyC : y ∈ centralizer ({d.t} : Set G) := hy ▸ hd.L_le (d.lift_mem _)
  have hρ : (d.ρ ⟨y, hyC⟩ : Equiv.Perm (Fin 1755)) = Model.parrottV 1 * Model.parrottV 5 := by
    subst hy
    exact hd.ρ_lift p09_v1v5_mem_titsD
  have hyT : y ∈ sylT d := p09_mem_sylT_iff.2 ⟨hyC, by
    rw [hρ]
    exact mul_mem (p09_parrottV_mem 1) (p09_parrottV_mem 5)⟩
  have hsq : y * y = d.pv 2 * d.z := by
    rw [hy]
    exact p09_lift_sq
  obtain ⟨y', hy'T, hy'z, hy', hy'C, hy'ρ⟩ := p09_adjust h49 hd hz hyT
  refine ⟨y', ?_, ?_⟩
  · unfold IsV1
    exact ⟨hy'T, hy'z, hy'C, Or.inr (hy'ρ.trans hρ)⟩
  · rw [← hsq]
    rcases hy' with rfl | rfl
    · rfl
    · have hc : y * d.t = d.t * y := mem_centralizer_singleton_iff.1 hyC
      calc d.t * y * (d.t * y) = d.t * (y * d.t) * y := by group
        _ = d.t * (d.t * y) * y := by rw [hc]
        _ = (d.t * d.t) * (y * y) := by group
        _ = y * y := by rw [hd.t_mul_self, one_mul]

theorem p09_pv2_mem (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    d.pv 2 ∈ centralizer ({z₀} : Set G) := by
  obtain ⟨y₁, hy₁, hsq⟩ := p09_exists_y1 h49 hd hz
  have hyz : Commute z₀ y₁ := hy₁.2.1.symm
  have hzz : Commute z₀ d.z := hz.cen hd.s56_z_mem_E
  have e : d.pv 2 = y₁ * y₁ * d.z⁻¹ := eq_mul_inv_of_mul_eq hsq.symm
  rw [mem_centralizer_singleton_iff, e]
  exact ((hyz.mul_right hyz).mul_right hzz.inv_right).eq.symm

theorem p09_exists_y5 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    (hR : d.ρ.range = ⊤) : ∃ y, IsV5 d y ∧ y ∈ sylT d ∧ y * z₀ = z₀ * y := by
  obtain ⟨y, hyC, hρ, -⟩ := hd.s56_exists_y hR
  have hyT : y ∈ sylT d := p09_mem_sylT_iff.2 ⟨hyC, by
    rw [hρ]
    exact p09_parrottV_mem 5⟩
  obtain ⟨y', hy'T, hy'z, -, hy'C, hy'ρ⟩ := p09_adjust h49 hd hz hyT
  exact ⟨y', ⟨hy'C, hy'ρ.trans hρ⟩, hy'T, hy'z⟩

theorem node09_syl (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    fusionIsSylowIn 2 (sylT d) (centralizer ({d.t} : Set G)) ∧
      d.t ∉ sylT d ⊓ centralizer ({z₀} : Set G) ∧
      sylT d = zpowers d.t ⊔ (sylT d ⊓ centralizer ({z₀} : Set G)) ∧
      d.pv 2 ∈ centralizer ({z₀} : Set G) ∧
      (d.ρ.range = ⊤ → ∃ y, IsV5 d y ∧ y ∈ sylT d ∧ y * z₀ = z₀ * y) ∧
      ∃ y₁, IsV1 d z₀ y₁ :=
  ⟨p09_sylow hd, p09_t_not_mem hd hz, p09_sylT_eq h49 hd hz, p09_pv2_mem h49 hd hz,
    fun hR => p09_exists_y5 h49 hd hz hR, (p09_exists_y1 h49 hd hz).imp fun _ h => h.1⟩

end Syl

end CFSG.LocalAnalysis.EvenBN.Tits.N
