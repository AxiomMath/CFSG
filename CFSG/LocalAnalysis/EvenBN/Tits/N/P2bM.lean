module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P2bQ2
public import CFSG.LocalAnalysis.EvenBN.Tits.N.Steps

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Open
open CFSG.LocalAnalysis.EvenBN.Tits CFSG.LocalAnalysis.EvenBN.Tits.Data

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem P2b.maxElemAbelian2_M (h49 : d.Thm49Statement) (hd : d.Hyp)
    (hV : IsElemAbelian 2 d.s56V) (hVcard : Nat.card d.s56V = 2 ^ 10)
    (hQ2 : maxElemAbelian2 d.s56Q2 = {d.s56V})
    (hinv : ∀ s ∈ d.s56Q2, s ∉ d.s56V → s * s = 1 → s * d.t = d.t * s →
      ∃ e ∈ d.E, s = d.t * e) :
    maxElemAbelian2 d.M = {d.s56V} := by
  have hX : ((fun e => d.t * e) '' (d.E : Set G)).ncard = 2 ^ 5 := by
    rw [Set.ncard_image_of_injective _ (mul_right_injective d.t), ← Nat.card_coe_set_eq]
    change Nat.card d.E = 2 ^ 5
    rw [hd.A_facts.1]
    norm_num
  have hrank : ∀ K : Subgroup G, K ≤ centralizer ({d.t} : Set G) → IsElemAbelian 2 K →
      Nat.card K ≤ 2 ^ 6 := fun K hK hKa => hd.card_le_of_isElemAbelian hK hKa
  have hoff : ∀ D : Subgroup G, D ≤ d.M → IsElemAbelian 2 D →
      Nat.card D ≤ 2 ^ 10 ∧ (2 ^ 10 ≤ Nat.card D → d.t ∉ D ∧
        Nat.card (D ⊓ centralizer ({d.t} : Set G) : Subgroup G) = 2 ^ 5 ∧
        {y | ∃ k ∈ D, k * d.t * k⁻¹ = y} = (fun e => d.t * e) '' (d.E : Set G) ∧
        ∀ r ∈ D, r * d.t = d.t * r → ∀ x ∈ (fun e => d.t * e) '' (d.E : Set G),
          r * x = x * r) :=
    fun D hDM hDe => P2b.offender hd.t_mul_self hX hrank hDe
      (fun k hk => ⟨d.s56Eps k, hd.s56_eps_mem_E (hDM hk), (hd.s56_conj_t k).symm⟩)
  have hB : ∀ D : Subgroup G, D ≤ d.M → IsElemAbelian 2 D → 2 ^ 10 ≤ Nat.card D →
      D = d.s56V := by
    intro D hDM hDe hge
    obtain ⟨htD, hR, hO, hcent⟩ := (hoff D hDM hDe).2 hge
    have hRE : (D ⊓ centralizer ({d.t} : Set G) : Subgroup G) ≤ d.E := by
      intro r hr
      obtain ⟨hrD, hrC⟩ := mem_inf.1 hr
      have hrt : r * d.t = d.t * r := mem_centralizer_singleton_iff.1 hrC
      have hrE : ∀ e ∈ d.E, e * r = r * e := by
        intro e he
        have h1 := hcent r hrD hrt (d.t * e) ⟨e, he, rfl⟩
        have h2 : d.t * (r * e) = d.t * (e * r) :=
          calc d.t * (r * e) = (d.t * r) * e := by group
            _ = (r * d.t) * e := by rw [hrt]
            _ = r * (d.t * e) := by group
            _ = d.t * e * r := h1
            _ = d.t * (e * r) := by group
        exact (mul_left_cancel h2).symm
      have hrQ2 : r ∈ d.s56Q2 := s56_mem_Q2_iff.2 ⟨hDM hrD, hrE⟩
      have hr2 : r * r = 1 := P2b.elemAb_mul_self hDe hrD
      by_cases hrV : r ∈ d.s56V
      · refine (hd.s56_V_eps_eq_one_iff h49 hrV).1 ?_
        have e1 : r * d.t * r⁻¹ = d.t := by rw [hrt]; group
        rw [s56Eps, e1, hd.t_mul_self]
      · exfalso
        obtain ⟨e, he, rfl⟩ := hinv r hrQ2 hrV hr2 hrt
        have hte : d.t * e ∈ (fun e => d.t * e) '' (d.E : Set G) := ⟨e, he, rfl⟩
        rw [← hO] at hte
        obtain ⟨k, hk, hkt⟩ := hte
        have he1 : e = 1 := P2b.eq_one_of_mem hDe hrD hk hkt
        apply htD
        have e2 : d.t = d.t * e := by rw [he1, mul_one]
        rw [e2]
        exact hrD
    have hEeq : (D ⊓ centralizer ({d.t} : Set G) : Subgroup G) = d.E := by
      refine Subgroup.eq_of_le_of_card_ge hRE ?_
      rw [hR, hd.A_facts.1]
      norm_num
    have hED : d.E ≤ D := by
      rw [← hEeq]
      exact inf_le_left
    have hDQ : D ≤ d.s56Q2 := fun a ha =>
      s56_mem_Q2_iff.2 ⟨hDM ha, fun e he => P2b.elemAb_comm hDe (hED he) ha⟩
    have hDmax : D ∈ maxElemAbelian2 d.s56Q2 := by
      refine ⟨hDQ, hDe, fun D' hD'Q hD'e => ?_⟩
      have hV' : d.s56V ∈ maxElemAbelian2 d.s56Q2 := by rw [hQ2]; rfl
      have h := hV'.2.2 D' hD'Q hD'e
      rw [hVcard] at h
      omega
    rw [hQ2] at hDmax
    exact hDmax
  ext D
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hDM, hDe, hDmax⟩
    refine hB D hDM hDe ?_
    have h := hDmax d.s56V (s56_V_le_M d) hV
    rw [hVcard] at h
    exact h
  · rintro rfl
    refine ⟨s56_V_le_M d, hV, fun D hDM hDe => ?_⟩
    rw [hVcard]
    exact (hoff D hDM hDe).1

theorem step12_holds : Step12 := by
  intro G _ _ d z₀ h49 hd hz _hinv _h06 h09 h10 _h11
  obtain ⟨-, -, -, -, -, -, -, -, ht9, -, -, hex, -⟩ := h09
  obtain ⟨h10y, hV, hVcard, -, hD, htop, -, -, -⟩ := h10
  have hyc : ∀ y, IsV5 d y → y ∈ sylT d → y * z₀ = z₀ * y → ∀ q ∈ d.s56Q2, y * q = q * y :=
    fun y h1 h2 h3 => (h10y y h1 h2 h3).1
  have hb : ∀ x ∈ d.s56Q2, x ∉ d.s56V → x * x = 1 → ∀ D : Subgroup G, D ≤ d.s56Q2 →
      (∀ a ∈ D, a * x = x * a) → IsElemAbelian 2 D → Nat.card D ≤ 64 :=
    fun x hx hxV hx2 D hDQ hDx hDe =>
      P2b.card_le_64 h49 hd hz hV hyc hD htop hex ht9 hx hxV hx2 hDQ hDx hDe
  have hQ2 := P2b.maxElemAbelian2_Q2 hV hVcard hb
  refine ⟨⟨P2b.orbit_t_Q2 h49 hd hz, P2b.orbit_t_V h49 hd hz⟩, ?_,
    P2b.inv_set_eq h49 hd hz hV hyc hD htop hex ht9, hQ2, ?_, ?_⟩
  · intro y hy5 hyT hyz
    exact P2b.orbit_tyz0 h49 hd hz (htop y hy5) (hyc y hy5 hyT hyz)
      (P2b.y_sq hd hz hy5 hyT hyz ht9) hyz
  · intro x hx hxV hx2
    exact P2b.pRank_Q2_centralizer hd hb h49 hx hxV hx2
  · exact P2b.maxElemAbelian2_M h49 hd hV hVcard hQ2
      (fun s hs hsV hs2 hst => P2b.inv_comm_t h49 hd hz hV hyc hD htop hex ht9 hs hsV hs2 hst)

end CFSG.LocalAnalysis.EvenBN.Tits.N
