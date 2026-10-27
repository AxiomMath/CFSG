module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7E1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Final
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec710Kap

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec7E_comm_t [Finite G] (hP : Asc82Tab6P) (h78 : Asc82Lemma78) (h710c : Asc82Lemma710c)
    {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B)
    {E : Subgroup G} (hE : IsSylow2Of E (MSub S B ⊓ centralizer (B : Set G))) :
    ∀ e ∈ E, e * t * e⁻¹ * t⁻¹ ∈ B := by
  intro e he
  exact sec710_comm_mem_B hP h78 h710c hc (hE.1 he)

theorem sec7E_trans [Finite G] (h710d : Asc82Lemma710d) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hc : Sec7Choice G t L S z g B) {E : Subgroup G}
    (hE : IsSylow2Of E (MSub S B ⊓ centralizer (B : Set G))) :
    ∀ x ∈ cosetSet t B, ∃ e ∈ E, e * t * e⁻¹ = x := by
  intro x hx
  have ht : t ∈ cosetSet t B := ⟨1, B.one_mem, (mul_one t).symm⟩
  obtain ⟨n, hn, hnxt⟩ := (h710d G t L S z g B hc).2.2.2.2.1 t ht x hx
  obtain ⟨e, he, c, hcC, hnc⟩ := sec7E_exists_mul h710d hc hE n hn
  have hct : c * t = t * c :=
    (Subgroup.mem_centralizer_iff.mp hcC t (sec79_t_mem_A hc)).symm
  have hct' : c * t * c⁻¹ = t := by rw [hct]; group
  refine ⟨e, he, ?_⟩
  calc e * t * e⁻¹ = e * (c * t * c⁻¹) * e⁻¹ := by rw [hct']
    _ = (e * c) * t * (e * c)⁻¹ := by group
    _ = n * t * n⁻¹ := by rw [hnc]
    _ = x := hnxt

theorem sec7E_cent_t [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hc : Sec7Choice G t L S z g B) {E : Subgroup G}
    (hE : IsSylow2Of E (MSub S B ⊓ centralizer (B : Set G))) (hAE : ASub S B ≤ E) :
    ∀ e ∈ E, e * t = t * e → e ∈ ASub S B := by
  intro e he het
  have heK : e ∈ MSub S B ⊓ centralizer (B : Set G) := hE.1 he
  have hcentA : ASub S B ≤ centralizer ({e} : Set G) := by
    rw [h78 G t L S z g B hc]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr het.symm
    · intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp heK.2 b hb)
  have heCentA : e ∈ centralizer (ASub S B : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mp (hcentA ha)
  have hmem : e ∈ E ⊓ centralizer (ASub S B : Set G) := ⟨he, heCentA⟩
  rw [sec7E_inf_cent h36 h76 hP h77b h78 hc hE hAE] at hmem
  exact hmem

theorem sec7E_sq_mem [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) (h710d : Asc82Lemma710d) {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B)
    {E : Subgroup G} (hE : IsSylow2Of E (MSub S B ⊓ centralizer (B : Set G)))
    (hAE : ASub S B ≤ E) : ∀ e ∈ E, e ^ 2 ∈ B := by
  intro e he
  obtain ⟨φ, -, hφker⟩ := sec7E_quot h36 h76 hP h77b h78 h710d hc hE hAE
  let x : ↥E := ⟨e, he⟩
  have hx1 : φ (x ^ 2) = 1 := by
    rw [map_pow, pow_two]
    exact e16_mul_self (φ x)
  have he2A : e ^ 2 ∈ ASub S B := by
    have h2 : x ^ 2 ∈ φ.ker := MonoidHom.mem_ker.mpr hx1
    rw [hφker] at h2
    have h3 : (x ^ 2 : G) ∈ ASub S B := Subgroup.mem_subgroupOf.mp h2
    simpa [x] using h3
  obtain ⟨j, b, hb, hjb⟩ := (sec710_mem_A h78 hc).mp he2A
  by_cases heA : e ∈ ASub S B
  · have h1 : e ^ 2 = 1 := (sec7E_A_elem h78 hc).2 e heA
    rw [h1]
    exact B.one_mem
  · have hne : e * t ≠ t * e := fun h =>
      heA (sec7E_cent_t h36 h76 hP h77b h78 hc hE hAE e he h)
    have hmod : t ^ (j % 2) = t ^ j := by
      simpa [hc.ctx.involution] using zpow_mod_orderOf t j
    rcases Int.emod_two_eq_zero_or_one j with h0 | h1
    · have htjeq : t ^ j = 1 := by rw [← hmod, h0, zpow_zero]
      rw [hjb, htjeq, one_mul]
      exact hb
    · exfalso
      have htjeq : t ^ j = t := by rw [← hmod, h1, zpow_one]
      have hsq : e ^ 2 = t * b := by rw [hjb, htjeq]
      have hcomm : e * (t * b) = (t * b) * e := by rw [← hsq]; group
      have hbe : b * e = e * b := Subgroup.mem_centralizer_iff.mp (hE.1 he).2 b hb
      have h1' : e * t * b = t * e * b := by
        calc e * t * b = e * (t * b) := by group
          _ = (t * b) * e := hcomm
          _ = t * (b * e) := by group
          _ = t * (e * b) := by rw [hbe]
          _ = t * e * b := by group
      exact hne (mul_right_cancel h1')

theorem sec7_exists_E [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) (h710c : Asc82Lemma710c)
    (h710d : Asc82Lemma710d) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) : ∃ E : Subgroup G, Sec7E G t L S z g B E := by
  obtain ⟨E, hE, hAE⟩ := sec7E_exists_sylow h78 hc
  exact ⟨E, hc, hE, hAE, sec7E_quot h36 h76 hP h77b h78 h710d hc hE hAE,
    sec7E_comm_t hP h78 h710c hc hE, sec7E_trans h710d hc hE,
    sec7E_cent_t h36 h76 hP h77b h78 hc hE hAE,
    sec7E_sq_mem h36 h76 hP h77b h78 h710d hc hE hAE⟩

theorem asc82Final7E_of (hU : Asc82Final7U) (h36 : Asc82Lemma36) (h76 : Asc82Lemma76)
    (hP : Asc82Tab6P) (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) (h710c : Asc82Lemma710c)
    (h710d : Asc82Lemma710d) : Asc82Final7E := by
  intro G _ _ t L S z g B hc
  obtain ⟨E, hE⟩ := sec7_exists_E h36 h76 hP h77b h78 h710c h710d hc
  obtain ⟨U, hU'⟩ := hU G t L S z g B E hE
  exact ⟨E, U, hU'⟩

end CFSG.OddStandard.SmallF3.Omega
