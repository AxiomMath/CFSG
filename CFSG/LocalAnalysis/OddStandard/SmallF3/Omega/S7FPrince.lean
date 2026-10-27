module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FEven
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FFrameOf
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Prince
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L120G

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem s7f_U_normalized [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) (h710c : Asc82Lemma710c)
    (h710d : Asc82Lemma710d) {t : G} {L S : Subgroup G} {z g : G} {B E U : Subgroup G}
    (hU : Sec7U G t L S z g B E U) :
    ∀ h ∈ MSub S B ⊓ normalizer (E : Set G), ∀ u ∈ U, h * u * h⁻¹ ∈ U := by
  intro h hh u hu
  have hE := hU.hE
  have hc := hE.choice
  obtain ⟨k, hk, n, hn, rfl⟩ := s7f_M_decomp h710c h710d hc h hh.1
  obtain ⟨e, he, o₁, ho₁, rfl⟩ :=
    s7f_K_eq_mul h36 h76 hP h77b h78 h710d hc hE.sylow hE.A_le k hk
  obtain ⟨u', hu', o, ho, hnu⟩ := hU.inv n hn u hu
  set O : Subgroup G := oddCoreIn (MSub S B) with hO
  have hEM : E ≤ MSub S B := fun x hx => (hE.sylow.1 hx).1
  have hu'E : u' ∈ E := hU.le hu'
  have ho₂ : u'⁻¹ * o₁ * u' * o * o₁⁻¹ ∈ O := by
    have h1 : u'⁻¹ * o₁ * u' ∈ O := by
      have h2 := conj_mem_oddCoreIn (Subgroup.le_normalizer (hEM (E.inv_mem hu'E))) ho₁
      rwa [inv_inv] at h2
    exact O.mul_mem (O.mul_mem h1 ho) (O.inv_mem ho₁)
  have hcomm : ∀ x ∈ E, ∀ b ∈ B, x * b = b * x := fun x hx b hb =>
    (Subgroup.mem_centralizer_iff.mp (hE.sylow.1 hx).2 b hb).symm
  have hsq : ∀ x ∈ E, x * x ∈ B := fun x hx => by rw [← pow_two]; exact hE.sq_mem x hx
  have heu : e * u' * e⁻¹ ∈ U := by
    have h1 := s7f_comm_mod hcomm hsq (E.inv_mem he) hu'E
    have h2 : e * u' * e⁻¹ = u' * ((e⁻¹ * u')⁻¹ * (u' * e⁻¹)) := by group
    rw [h2]
    exact U.mul_mem hu' (hU.B_le h1)
  have ho₃ : e * (u'⁻¹ * o₁ * u' * o * o₁⁻¹) * e⁻¹ ∈ O :=
    conj_mem_oddCoreIn (Subgroup.le_normalizer (hEM he)) ho₂
  have heq : e * o₁ * n * u * (e * o₁ * n)⁻¹ =
      (e * u' * e⁻¹) * (e * (u'⁻¹ * o₁ * u' * o * o₁⁻¹) * e⁻¹) := by
    calc e * o₁ * n * u * (e * o₁ * n)⁻¹ = e * o₁ * (n * u * n⁻¹) * o₁⁻¹ * e⁻¹ := by group
      _ = e * o₁ * (u' * o) * o₁⁻¹ * e⁻¹ := by rw [hnu]
      _ = (e * u' * e⁻¹) * (e * (u'⁻¹ * o₁ * u' * o * o₁⁻¹) * e⁻¹) := by group
  have hlhs : e * o₁ * n * u * (e * o₁ * n)⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp hh.2 u).mp (hU.le hu)
  have ho₃E : e * (u'⁻¹ * o₁ * u' * o * o₁⁻¹) * e⁻¹ ∈ E := by
    have h1 : e * (u'⁻¹ * o₁ * u' * o * o₁⁻¹) * e⁻¹ =
        (e * u' * e⁻¹)⁻¹ * (e * o₁ * n * u * (e * o₁ * n)⁻¹) := by
      rw [heq]
      group
    rw [h1]
    exact E.mul_mem (E.inv_mem (hU.le heu)) hlhs
  have h1 := s7f_eq_one_of_mem_oddCore hE.sylow.2.1 ho₃E ho₃
  rw [heq, h1, mul_one]
  exact heu

theorem s7f_prince_of_frame [Finite G] {t : G} {B E H : Subgroup G}
    {φ : (Fin 5 → ZMod 2) → G} (F : S7FFrame t B E H φ) {U : Subgroup G} (hUE : U ≤ E)
    (hBU : B ≤ U) (hsup : zpowers t ⊔ U = E) (hinf : zpowers t ⊓ U = ⊥)
    (hHU : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U) : IsElemAb2 U 8 ∨ IsZ4Pow4 U := by
  have hHH : s7fEven φ H ≤ H := s7fEven_le φ H
  have hnormU : s7fEven φ H ≤ normalizer (U : Set G) := fun h hh =>
    s7f_mem_normalizer_of_conj_le fun u hu => hHU h (hHH hh) u hu
  have hnormB : s7fEven φ H ≤ normalizer (B : Set G) := fun h hh =>
    s7f_mem_normalizer_of_conj_le fun b hb => F.H_B (hHH hh) hb
  have hUB : U ≤ normalizer (B : Set G) := fun u hu =>
    s7f_mem_normalizer_of_conj_le fun b hb => by
      have h1 : u * b * u⁻¹ = b := by rw [F.comm_B u (hUE hu) b hb]; group
      rw [h1]
      exact hb
  have htU : t ∉ U := by
    intro htU
    have ht1 : t ∈ zpowers t ⊓ U := ⟨Subgroup.mem_zpowers t, htU⟩
    rw [hinf, Subgroup.mem_bot] at ht1
    exact F.t_not_mem (ht1 ▸ B.one_mem)
  have hker : ∀ v ∈ U, s7fKap t v = 1 ↔ v ∈ B := by
    intro v hv
    refine ⟨fun h1 => ?_, fun hb => F.kap_B hb⟩
    rcases F.kap_ker v (hUE hv) h1 with hb | hb
    · exact hb
    · exfalso
      apply htU
      have h2 : t = (t * v) * v⁻¹ := by group
      rw [h2]
      exact U.mul_mem (hBU hb) (U.inv_mem hv)
  have htnorm : zpowers t ≤ normalizer (U : Set G) := by
    rw [Subgroup.zpowers_le]
    exact s7f_mem_normalizer_of_conj_le fun u hu => F.conj_mem_of_B_le hUE hBU F.t_mem hu
  have hsurj : ∀ b ∈ B, ∃ v ∈ U, s7fKap t v = b := by
    intro b hb
    obtain ⟨e, he, hkb⟩ := F.kap_surj b hb
    have he' : e ∈ U ⊔ zpowers t := by rw [sup_comm, hsup]; exact he
    obtain ⟨u, hu, y, hy, rfl⟩ :=
      (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left htnorm).mp he'
    have hyE : y ∈ E := (Subgroup.zpowers_le.mpr F.t_mem) hy
    have hy1 : s7fKap t y = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      unfold s7fKap
      group
    refine ⟨u, hu, ?_⟩
    rw [← hkb, F.kap_mul (hUE hu) hyE, hy1, mul_one]
  obtain ⟨φ', hmod, hφ'⟩ := exists_natMod_lift_of_hom (V := U) (K := B) (B := B)
    (H := s7fEven φ H) (s7fKap t) hBU hUB hnormU hnormB (fun v hv => F.kap_mem v (hUE hv))
    (fun v hv w hw => F.kap_mul (hUE hv) (hUE hw)) hker hsurj
    (fun h hh v hv => F.kap_conj (hHH hh) (hUE hv)) F.even_perm
  refine asc82Prince_of G B U (s7fEven φ H) φ' φ hmod F.even_perm ?_
  intro h hh σ _ hσ v hv
  have hv' : φ' v ∈ U := hmod.2.2.2.2.1 v hv
  have hσv : φ' (permVec σ v) ∈ U := hmod.2.2.2.2.1 _ (isEvenVec_permVec σ hv)
  have hx : h * φ' v * h⁻¹ ∈ E := F.H_E h (hHH hh) _ (hUE hv')
  have h1 : s7fKap t ((h * φ' v * h⁻¹)⁻¹ * φ' (permVec σ v)) = 1 := F.kap_B (hσ v hv)
  rw [F.kap_mul (E.inv_mem hx) (hUE hσv), F.kap_inv hx, F.kap_conj (hHH hh) (hUE hv'),
    hφ' v hv, hφ' _ (isEvenVec_permVec σ hv)] at h1
  exact inv_mul_eq_one.mp h1

theorem asc82Final7Prince_of_sec7 (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) (h710c : Asc82Lemma710c)
    (h710d : Asc82Lemma710d) : Asc82Final7Prince := by
  intro G _ _ t L S z g B E U hU
  obtain ⟨φ, -, F⟩ := s7f_frame_of_sec7E h36 h76 hP h77b h78 h710c h710d hU.hE
  exact s7f_prince_of_frame F hU.le hU.B_le hU.sup hU.inf
    (s7f_U_normalized h36 h76 hP h77b h78 h710c h710d hU)

end CFSG.OddStandard.SmallF3.Omega
