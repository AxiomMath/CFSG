module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S16Fin
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S16A

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits

section S16End

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem card_CK_le (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    Nat.card ↥(Cv d ⊓ centralizer ({d.t} : Set G)) ≤ 2 ^ 6 ∧
      (Nat.card ↥(Cv d ⊓ centralizer ({d.t} : Set G)) = 2 ^ 6 → d.ρ.range = ⊤) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCA := hd.s56_centralizer_A
  have hVc : ∀ v ∈ d.s56V, ∀ k ∈ Cv d, v * k = k * v := fun v hv k hk =>
    (Subgroup.mem_centralizer_iff.1 hk) v hv
  have hAeq : d.A = d.E ⊔ zpowers d.t := rfl
  have hKC : Cv d ⊓ centralizer ({d.t} : Set G) ≤ centralizer (d.A : Set G) ⊓ Cv d := by
    intro k hk
    obtain ⟨hkK, hkt⟩ := Subgroup.mem_inf.1 hk
    refine Subgroup.mem_inf.2 ⟨?_, hkK⟩
    have hle : d.A ≤ centralizer ({k} : Set G) := by
      rw [hAeq]
      refine sup_le (fun e he => mem_centralizer_singleton_iff.2
        (hVc e (hd.s56_E_le_V h49 he) k hkK)) (zpowers_le.2 (mem_centralizer_singleton_iff.2 ?_))
      exact (mem_centralizer_singleton_iff.1 hkt).symm
    exact mem_centralizer_iff.2 fun a ha => mem_centralizer_singleton_iff.1 (hle ha)
  have htC : d.t ∈ centralizer (d.A : Set G) := by
    have hle : d.A ≤ centralizer ({d.t} : Set G) := by
      rw [hAeq]
      exact sup_le (fun e he => mem_centralizer_singleton_iff.2 (hd.L_comm_t (d.liftSub_le _ he)))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
    exact mem_centralizer_iff.2 fun a ha => mem_centralizer_singleton_iff.1 (hle ha)
  have hD'C : centralizer (d.A : Set G) ⊓ Cv d ≤ centralizer (d.A : Set G) := inf_le_left
  have hlt : Nat.card ↥(centralizer (d.A : Set G) ⊓ Cv d) < Nat.card ↥(centralizer (d.A : Set G)) := by
    by_contra hge
    push Not at hge
    have heq := Subgroup.eq_of_le_of_card_ge hD'C hge
    have : d.t ∈ centralizer (d.A : Set G) ⊓ Cv d := by
      rw [heq]
      exact htC
    exact t_not_mem_Cv h49 hd hz (Subgroup.mem_inf.1 this).2
  obtain ⟨c, hc⟩ := hCA.1.exists_card_eq
  have hdvd : Nat.card ↥(centralizer (d.A : Set G) ⊓ Cv d) ∣ 2 ^ c := by
    have := Subgroup.card_dvd_of_le hD'C
    rwa [hc] at this
  obtain ⟨a, ha, haD⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hac : a < c := by
    by_contra hca
    push Not at hca
    have h1 : 2 ^ c ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hca
    rw [← hc, ← haD] at h1
    omega
  have hKCle : Nat.card ↥(Cv d ⊓ centralizer ({d.t} : Set G)) ≤ 2 ^ a := by
    rw [← haD]
    exact Subgroup.card_le_of_le hKC
  rcases hCA.2 with ⟨hr, hC6⟩ | ⟨hr, hC7⟩
  · have hc6 : c = 6 := Nat.pow_right_injective (le_refl 2) (hc.symm.trans hC6)
    have ha5 : a ≤ 5 := by omega
    have h1 : 2 ^ a ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) ha5
    exact ⟨by omega, fun h => by omega⟩
  · have hc7 : c ≤ 7 := by
      by_contra h
      push Not at h
      have h1 : 2 ^ 8 ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) h
      rw [← hc] at h1
      omega
    have ha6 : a ≤ 6 := by omega
    have h1 : 2 ^ a ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) ha6
    exact ⟨le_trans hKCle h1, fun _ => hr⟩

theorem node16 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀)
    (h10 : Node10 d z₀) (h12 : Node12 d z₀) (h15 : Node15 d z₀) (h17s : Node17s d z₀) :
    Node16 d z₀ := by
  have hVab : IsElemAbelian 2 d.s56V := h10.isElemAbelian_V
  have hVK : d.s56V ≤ Cv d := V_le_Cv h10
  have hVc : ∀ v ∈ d.s56V, ∀ k ∈ Cv d, v * k = k * v := fun v hv k hk =>
    (Subgroup.mem_centralizer_iff.1 hk) v hv
  have ht2 : d.t * d.t = 1 := hd.t_mul_self
  have htK : d.t ∉ Cv d := t_not_mem_Cv h49 hd hz
  have htNK : d.t ∈ normalizer ((Cv d : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro k
    refine ⟨fun hk => t_mul_Cv_mul_inv h49 hd hk, fun hk => ?_⟩
    have h1 := t_mul_Cv_mul_inv h49 hd hk
    have e : d.t * (d.t * k * d.t⁻¹) * d.t⁻¹ = k := by
      calc d.t * (d.t * k * d.t⁻¹) * d.t⁻¹ = (d.t * d.t) * k * (d.t * d.t)⁻¹ := by group
        _ = k := by rw [ht2]; group
    rwa [e] at h1
  have htNV : d.t ∈ normalizer (d.s56V : Set G) := t_mem_Hg h49 hd
  have hti : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right ht2
  have hVt : ∀ w ∈ d.s56V, d.t * w * d.t⁻¹ = w → ∃ v ∈ d.s56V, w = v * (d.t * v⁻¹ * d.t⁻¹) := by
    intro w hw hwt
    have hwE : w ∈ d.E := by
      rw [E_eq_V_inf_Ct h49 hd]
      refine ⟨hw, mem_centralizer_singleton_iff.2 ?_⟩
      calc w * d.t = (d.t * w * d.t⁻¹) * d.t := by rw [hwt]
        _ = d.t * w := by group
    have hmem : d.t * w ∈ (fun e => d.t * e) '' (d.E : Set G) := ⟨w, hwE, rfl⟩
    rw [← h12.1.2] at hmem
    obtain ⟨v, hv, hvt⟩ := hmem
    have hv₁ : d.t * v * d.t⁻¹ ∈ d.s56V := (mem_normalizer_iff.1 htNV v).1 hv
    refine ⟨v⁻¹, inv_mem hv, ?_⟩
    have e1 : w = d.t * (v * d.t * v⁻¹) := by rw [hvt, ← mul_assoc, ht2, one_mul]
    calc w = d.t * (v * d.t * v⁻¹) := e1
      _ = (d.t * v * d.t⁻¹) * v⁻¹ := by rw [hti]; group
      _ = v⁻¹ * (d.t * v * d.t⁻¹) := h10.comm_V hv₁ (inv_mem hv)
      _ = v⁻¹ * (d.t * v⁻¹⁻¹ * d.t⁻¹) := by rw [inv_inv]
  have hE5 : Nat.card ↥(d.s56V ⊓ centralizer ({d.t} : Set G)) = 2 ^ 5 := by
    rw [← E_eq_V_inf_Ct h49 hd]
    exact hd.A_facts.1
  obtain ⟨hCK1, hCK2⟩ := card_CK_le h49 hd hz h10
  have hCle : Nat.card ↥(Cv d ⊓ centralizer ({d.t} : Set G)) ≤
      2 * Nat.card ↥(d.s56V ⊓ centralizer ({d.t} : Set G)) := by
    rw [hE5]
    omega
  refine ⟨fun S hS hSt => ?_, fun S hS hSt => ?_⟩
  · rcases S16A.sixNine hVab hVK hVc ht2 htK htNK htNV hVt hCle hS hSt with
      hK | ⟨hcard, hnormal, hDS, hfusion, -⟩
    · exact Or.inl hK
    · refine Or.inr ⟨hCK2 ?_, hnormal, hDS, hfusion⟩
      rw [hcard, hE5]
      norm_num
  · refine node16_b h49 hd hz h09 h10 h12 h15 h17s hS hSt ?_
    rcases S16A.sixNine hVab hVK hVc ht2 htK htNK htNV hVt hCle hS hSt with
      hK | ⟨-, -, -, hfusion, hb⟩
    · exact Or.inl hK
    · exact Or.inr ⟨hfusion, hb⟩

theorem step16_holds : Step16 := by
  intro G _ _ d z₀ h49 hd hz h09 h10 h12 _h14 h15 h17s
  exact node16 h49 hd hz h09 h10 h12 h15 h17s

end S16End

end CFSG.LocalAnalysis.EvenBN.Tits.N
