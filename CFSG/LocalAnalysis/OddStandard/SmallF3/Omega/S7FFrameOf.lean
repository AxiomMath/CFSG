module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FFrameLem
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FFratt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec710Kap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Final

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem s7f_t_not_mem_B [Finite G] (hP : Asc82Tab6P) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hc : Sec7Choice G t L S z g B) : t ∉ B := by
  intro htB
  have htL : t ∈ L := (hc.normalE16.1 htB).2
  have htC : t ∈ centralizer (L : Set G) := hc.ctx.t_mem_centralizer
  have htZ : t ∈ centerIn L :=
    Subgroup.mem_map.mpr ⟨⟨t, htL⟩,
      Subgroup.mem_center_iff.mpr fun y =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp htC (y : G) y.2), rfl⟩
  have ht1 : t = 1 := Subgroup.mem_bot.mp (hP.center_triv G L hc.ctx.isOm6P ▸ htZ)
  have h2 : orderOf t = 2 := hc.ctx.involution
  rw [ht1, orderOf_one] at h2
  norm_num at h2

theorem s7f_conj_t_mem [Finite G] (hP : Asc82Tab6P) (h78 : Asc82Lemma78)
    (h710c : Asc82Lemma710c) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) {h : G} (hh : h ∈ MSub S B) : t⁻¹ * (h * t * h⁻¹) ∈ B := by
  have htA : t ∈ ASub S B := sec79_t_mem_A hc
  have hconjA : h * t * h⁻¹ ∈ ASub S B := (Subgroup.mem_normalizer_iff.mp hh t).mp htA
  obtain ⟨j, b, hb, hjb⟩ := (sec710_mem_A h78 hc).mp hconjA
  have hmod : t ^ (j % 2) = t ^ j := by
    simpa [hc.ctx.involution] using zpow_mod_orderOf t j
  rcases Int.emod_two_eq_zero_or_one j with h0 | h1
  · exfalso
    have htjeq : t ^ j = 1 := by rw [← hmod, h0, zpow_zero]
    have hb' : h * t * h⁻¹ = b := by rw [hjb, htjeq, one_mul]
    apply s7f_t_not_mem_B hP hc
    have hmem := s7f_B_normal h710c hc h⁻¹ ((MSub S B).inv_mem hh) b hb
    rw [← hb'] at hmem
    have e : h⁻¹ * (h * t * h⁻¹) * h⁻¹⁻¹ = t := by group
    rwa [e] at hmem
  · have htjeq : t ^ j = t := by rw [← hmod, h1, zpow_one]
    rw [hjb, htjeq]
    have e : t⁻¹ * (t * b) = b := by group
    rw [e]
    exact hb

theorem s7f_acts_of_mem_M [Finite G] (h78 : Asc82Lemma78) (h710c : Asc82Lemma710c)
    (h710d : Asc82Lemma710d) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) {φ : (Fin 5 → ZMod 2) → G}
    (hφ : IsPermModuleVia IsEvenVec φ B (L ⊓ normalizer (B : Set G)) ⊤) {h : G}
    (hh : h ∈ MSub S B) : ∃ σ : Equiv.Perm (Fin 5), s7fActs φ h σ := by
  obtain ⟨k, hk, n, hn, rfl⟩ := s7f_M_decomp h710c h710d hc h hh
  have hn' : n ∈ L ⊓ normalizer (B : Set G) := by
    rw [← sec710_inf_M_eq h78 h710c hc]
    exact hn
  obtain ⟨σ, -, hσ⟩ := hφ.2.2.2.1 n hn'
  refine ⟨σ, fun v hv => ?_⟩
  have hφB : φ (permVec σ v) ∈ B := (hφ.2.2.1 _).mpr ⟨_, isEvenVec_permVec σ hv, rfl⟩
  have hkc : k * φ (permVec σ v) = φ (permVec σ v) * k :=
    (Subgroup.mem_centralizer_iff.mp hk.2 _ hφB).symm
  calc k * n * φ v * (k * n)⁻¹ = k * (n * φ v * n⁻¹) * k⁻¹ := by group
    _ = k * φ (permVec σ v) * k⁻¹ := by rw [hσ v hv]
    _ = φ (permVec σ v) := by rw [hkc]; group

theorem s7f_realize [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) (h710c : Asc82Lemma710c)
    (h710d : Asc82Lemma710d) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) {E : Subgroup G}
    (hE : IsSylow2Of E (MSub S B ⊓ centralizer (B : Set G))) (hAE : ASub S B ≤ E)
    {φ : (Fin 5 → ZMod 2) → G}
    (hφ : IsPermModuleVia IsEvenVec φ B (L ⊓ normalizer (B : Set G)) ⊤)
    (σ : Equiv.Perm (Fin 5)) : ∃ h ∈ MSub S B ⊓ normalizer (E : Set G), s7fActs φ h σ := by
  obtain ⟨n, hn, hσ⟩ := hφ.2.2.2.2 σ (Subgroup.mem_top σ)
  have hnM : n ∈ MSub S B := by
    have hn' : n ∈ L ⊓ MSub S B := by
      rw [sec710_inf_M_eq h78 h710c hc]
      exact hn
    exact hn'.2
  obtain ⟨o, ho, h, hh, rfl⟩ :=
    s7f_frattini h36 h76 hP h77b h78 h710c h710d hc hE hAE n hnM
  refine ⟨h, hh, fun v hv => ?_⟩
  have hφv : φ v ∈ B := (hφ.2.2.1 _).mpr ⟨v, hv, rfl⟩
  have hhv : h * φ v * h⁻¹ ∈ B := s7f_B_normal h710c hc h hh.1 _ hφv
  have hoc : o * (h * φ v * h⁻¹) = (h * φ v * h⁻¹) * o := s7f_oddCore_comm_B hc o ho _ hhv
  calc h * φ v * h⁻¹ = o * (h * φ v * h⁻¹) * o⁻¹ := by rw [hoc]; group
    _ = o * h * φ v * (o * h)⁻¹ := by group
    _ = φ (permVec σ v) := hσ v hv

theorem s7f_triv [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) (h710d : Asc82Lemma710d) {t : G}
    {L S : Subgroup G} {z g : G} {B E : Subgroup G} (hE : Sec7E G t L S z g B E) :
    ∀ h ∈ MSub S B ⊓ normalizer (E : Set G), (∀ b ∈ B, h * b = b * h) →
      ∀ e ∈ E, e⁻¹ * (h * e * h⁻¹) ∈ B := by
  intro h hh hhB e he
  have hc := hE.choice
  have hK : h ∈ MSub S B ⊓ centralizer (B : Set G) :=
    ⟨hh.1, Subgroup.mem_centralizer_iff.mpr fun b hb => (hhB b hb).symm⟩
  obtain ⟨e₁, he₁, o, ho, rfl⟩ :=
    s7f_K_eq_mul h36 h76 hP h77b h78 h710d hc hE.sylow hE.A_le h hK
  have hoN : ∀ x ∈ E, o * x * o⁻¹ ∈ E := by
    intro x hx
    have h1 : o * x * o⁻¹ = e₁⁻¹ * ((e₁ * o) * x * (e₁ * o)⁻¹) * e₁ := by group
    rw [h1]
    have h2 : (e₁ * o) * x * (e₁ * o)⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hh.2 x).mp hx
    exact E.mul_mem (E.mul_mem (E.inv_mem he₁) h2) he₁
  have hEM : E ≤ MSub S B := fun x hx => (hE.sylow.1 hx).1
  have hoc : o * e = e * o := s7f_oddCore_comm_of_normalizes hEM hE.sylow.2.1 ho hoN e he
  have h3 : e₁ * o * e * (e₁ * o)⁻¹ = e₁ * e * e₁⁻¹ := by
    calc e₁ * o * e * (e₁ * o)⁻¹ = e₁ * (o * e) * o⁻¹ * e₁⁻¹ := by group
      _ = e₁ * (e * o) * o⁻¹ * e₁⁻¹ := by rw [hoc]
      _ = e₁ * e * e₁⁻¹ := by group
  rw [h3]
  have hcomm : ∀ x ∈ E, ∀ b ∈ B, x * b = b * x := fun x hx b hb =>
    (Subgroup.mem_centralizer_iff.mp (hE.sylow.1 hx).2 b hb).symm
  have hsq : ∀ x ∈ E, x * x ∈ B := fun x hx => by rw [← pow_two]; exact hE.sq_mem x hx
  have h4 := s7f_comm_mod hcomm hsq (E.inv_mem he₁) he
  have h5 : (e₁⁻¹ * e)⁻¹ * (e * e₁⁻¹) = e⁻¹ * (e₁ * e * e₁⁻¹) := by group
  rwa [h5] at h4

theorem s7f_frame_of_sec7E [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76)
    (hP : Asc82Tab6P) (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) (h710c : Asc82Lemma710c)
    (h710d : Asc82Lemma710d) {t : G} {L S : Subgroup G} {z g : G} {B E : Subgroup G}
    (hE : Sec7E G t L S z g B E) :
    ∃ φ : (Fin 5 → ZMod 2) → G,
      IsPermModuleVia IsEvenVec φ B (L ⊓ normalizer (B : Set G)) ⊤ ∧
        S7FFrame t B E (MSub S B ⊓ normalizer (E : Set G)) φ := by
  have hc := hE.choice
  obtain ⟨φ, hφ⟩ :=
    (hP.aut_B G L hc.ctx.isOm6P (S ⊓ L) (hc.ctx.isSylow2Of_inf h36) B hc.normalE16).2.2
  have htA : t ∈ ASub S B := sec79_t_mem_A hc
  have hBA : B ≤ ASub S B := sec79_B_le_A hc
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hc.ctx.involution]
    exact pow_orderOf_eq_one t
  have htB : ∀ b ∈ B, t * b = b * t := fun b hb =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hc.ctx.sylow.1 (hc.normalE16.1 hb).1)).symm
  refine ⟨φ, hφ, ⟨hE.A_le htA, ht2, s7f_t_not_mem_B hP hc, hBA.trans hE.A_le, ?_, ?_, ?_,
    hE.comm_t, ?_, ?_, ?_, ?_, ?_, s7f_triv h36 h76 hP h77b h78 h710d hE⟩⟩
  · rw [hc.normalE16.2.1.2]
    norm_num
  · exact fun e he b hb => (Subgroup.mem_centralizer_iff.mp (hE.sylow.1 he).2 b hb).symm
  · exact fun e he => by rw [← pow_two]; exact hE.sq_mem e he
  · intro e he hk
    have het : e * t = t * e := by
      have h1 : e * t * e⁻¹ * t⁻¹ = 1 := hk
      calc e * t = (e * t * e⁻¹ * t⁻¹) * (t * e) := by group
        _ = t * e := by rw [h1, one_mul]
    obtain ⟨j, b, hb, hjb⟩ := (sec710_mem_A h78 hc).mp (hE.cent_t e he het)
    have hmod : t ^ (j % 2) = t ^ j := by
      simpa [hc.ctx.involution] using zpow_mod_orderOf t j
    rcases Int.emod_two_eq_zero_or_one j with h0 | h1
    · left
      have htjeq : t ^ j = 1 := by rw [← hmod, h0, zpow_zero]
      rw [hjb, htjeq, one_mul]
      exact hb
    · right
      have htjeq : t ^ j = t := by rw [← hmod, h1, zpow_one]
      rw [hjb, htjeq, ← mul_assoc, ht2, one_mul]
      exact hb
  · intro b hb
    obtain ⟨e, he, het⟩ := hE.trans (t * b) ⟨b, hb, rfl⟩
    refine ⟨e, he, ?_⟩
    show e * t * e⁻¹ * t⁻¹ = b
    rw [het, htB b hb]
    group
  · exact fun h hh e he => (Subgroup.mem_normalizer_iff.mp hh.2 e).mp he
  · exact fun h hh => s7f_conj_t_mem hP h78 h710c hc hh.1
  · refine ⟨hφ.1, hφ.2.1, hφ.2.2.1, fun h hh => ?_, fun σ _ => ?_⟩
    · obtain ⟨σ, hσ⟩ := s7f_acts_of_mem_M h78 h710c h710d hc hφ hh.1
      exact ⟨σ, Subgroup.mem_top σ, hσ⟩
    · exact s7f_realize h36 h76 hP h77b h78 h710c h710d hc hE.sylow hE.A_le hφ σ

end CFSG.OddStandard.SmallF3.Omega
