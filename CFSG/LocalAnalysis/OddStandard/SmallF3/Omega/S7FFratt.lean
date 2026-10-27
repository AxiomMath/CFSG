module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7E1
public import TauCeti.GroupTheory.PGroup
public import TauCeti.GroupTheory.SemidirectProduct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem s7f_mem_normalizer_of_conj_le [Finite G] {H : Subgroup G} {c : G}
    (h : ∀ x ∈ H, c * x * c⁻¹ ∈ H) : c ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro x ⟨s, hs, rfl⟩
    simpa [MulAut.conj_apply] using h s hs
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]

theorem s7f_eq_one_of_mem_oddCore [Finite G] {E K : Subgroup G} (hE : IsPGroup 2 E) {x : G}
    (hxE : x ∈ E) (hxO : x ∈ oddCoreIn K) : x = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ¬ 2 ∣ Nat.card (oddCoreIn K) := fun h2 =>
    (Nat.not_even_iff_odd.mpr (odd_card_oddCoreIn K)) (even_iff_two_dvd.mpr h2)
  exact Subgroup.disjoint_def.mp (TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup hodd hE) hxO hxE

theorem s7f_oddCore_comm_of_normalizes [Finite G] {M E : Subgroup G} (hEM : E ≤ M)
    (hE : IsPGroup 2 E) {o : G} (ho : o ∈ oddCoreIn M) (hoE : ∀ e ∈ E, o * e * o⁻¹ ∈ E) :
    ∀ e ∈ E, o * e = e * o := by
  intro e he
  have h1 : o * e * o⁻¹ * e⁻¹ ∈ E := E.mul_mem (hoE e he) (E.inv_mem he)
  have h2 : e * o⁻¹ * e⁻¹ ∈ oddCoreIn M :=
    conj_mem_oddCoreIn (Subgroup.le_normalizer (hEM he)) ((oddCoreIn M).inv_mem ho)
  have h3 : o * e * o⁻¹ * e⁻¹ ∈ oddCoreIn M := by
    have h4 : o * e * o⁻¹ * e⁻¹ = o * (e * o⁻¹ * e⁻¹) := by group
    rw [h4]
    exact (oddCoreIn M).mul_mem ho h2
  have h5 : o * e * o⁻¹ * e⁻¹ = 1 := s7f_eq_one_of_mem_oddCore hE h1 h3
  calc o * e = (o * e * o⁻¹ * e⁻¹) * (e * o) := by group
    _ = e * o := by rw [h5, one_mul]

theorem s7f_oddCore_comm_B [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) :
    ∀ o ∈ oddCoreIn (MSub S B), ∀ b ∈ B, o * b = b * o := by
  intro o ho b hb
  exact (Subgroup.mem_centralizer_iff.mp (sec79_oddCore_M_le_cent_A hc ho) b
    (sec79_B_le_A hc hb)).symm

theorem s7f_B_normal [Finite G] (h710c : Asc82Lemma710c) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    ∀ m ∈ MSub S B, ∀ b ∈ B, m * b * m⁻¹ ∈ B := by
  intro m hm b hb
  have hBM : B ≤ MSub S B := (sec79_B_le_A hc).trans Subgroup.le_normalizer
  exact (Subgroup.normal_subgroupOf_iff hBM).mp (h710c G t L S z g B hc).2.2 b m hb hm

theorem s7f_K_normal [Finite G] (h710c : Asc82Lemma710c) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    ∀ m ∈ MSub S B, ∀ k ∈ MSub S B ⊓ centralizer (B : Set G),
      m * k * m⁻¹ ∈ MSub S B ⊓ centralizer (B : Set G) := by
  intro m hm k hk
  refine ⟨(MSub S B).mul_mem ((MSub S B).mul_mem hm hk.1) ((MSub S B).inv_mem hm), ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
  have hb' : m⁻¹ * b * m ∈ B := by
    simpa using s7f_B_normal h710c hc m⁻¹ ((MSub S B).inv_mem hm) b hb
  have hkb : (m⁻¹ * b * m) * k = k * (m⁻¹ * b * m) :=
    Subgroup.mem_centralizer_iff.mp hk.2 _ hb'
  calc b * (m * k * m⁻¹) = m * ((m⁻¹ * b * m) * k) * m⁻¹ := by group
    _ = m * (k * (m⁻¹ * b * m)) * m⁻¹ := by rw [hkb]
    _ = m * k * m⁻¹ * b := by group

theorem s7f_M_decomp [Finite G] (h710c : Asc82Lemma710c) (h710d : Asc82Lemma710d) {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    ∀ m ∈ MSub S B, ∃ k ∈ MSub S B ⊓ centralizer (B : Set G), ∃ n ∈ L ⊓ MSub S B, m = k * n := by
  intro m hm
  have hle : L ⊓ MSub S B ≤ normalizer ((MSub S B ⊓ centralizer (B : Set G) : Subgroup G) :
      Set G) := fun n hn =>
    s7f_mem_normalizer_of_conj_le fun k hk => s7f_K_normal h710c hc n hn.2 k hk
  have hm' : m ∈ (MSub S B ⊓ centralizer (B : Set G)) ⊔ (L ⊓ MSub S B) := by
    rw [← (h710d G t L S z g B hc).1]
    exact hm
  exact (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left hle).mp hm'

theorem s7f_K_eq_mul [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) (h710d : Asc82Lemma710d) {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B)
    {E : Subgroup G} (hE : IsSylow2Of E (MSub S B ⊓ centralizer (B : Set G)))
    (hAE : ASub S B ≤ E) :
    ∀ k ∈ MSub S B ⊓ centralizer (B : Set G), ∃ e ∈ E, ∃ o ∈ oddCoreIn (MSub S B), k = e * o := by
  intro k hk
  obtain ⟨e, he, c, hcC, rfl⟩ := sec7E_exists_mul h710d hc hE k hk
  have hcA : c ∈ ASub S B ⊔ oddCoreIn (MSub S B) := by
    rw [(asc82Lemma79b_of h36 h76 hP h77b h78 G t L S z g B hc).2]
    exact hcC
  have hle : oddCoreIn (MSub S B) ≤ normalizer ((ASub S B : Subgroup G) : Set G) :=
    (oddCoreIn_normal (MSub S B)).1
  obtain ⟨a, ha, o, ho, rfl⟩ :=
    (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left hle).mp hcA
  exact ⟨e * a, E.mul_mem he (hAE ha), o, ho, by group⟩

theorem s7f_frattini [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) (h710c : Asc82Lemma710c)
    (h710d : Asc82Lemma710d) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) {E : Subgroup G}
    (hE : IsSylow2Of E (MSub S B ⊓ centralizer (B : Set G))) (hAE : ASub S B ≤ E) :
    ∀ m ∈ MSub S B, ∃ o ∈ oddCoreIn (MSub S B),
      ∃ h ∈ MSub S B ⊓ normalizer (E : Set G), m = o * h := by
  intro m hm
  set E' : Subgroup G := E.map (MulAut.conj m).toMonoidHom with hE'
  have hE'2 : IsPGroup 2 E' := hE.2.1.map _
  have hE'K : E' ≤ MSub S B ⊓ centralizer (B : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact s7f_K_normal h710c hc m hm x (hE.1 hx)
  obtain ⟨c, hcK, hcE⟩ := exists_conj_le_of_isSylow2Of hE hE'2 hE'K
  have hcmN : c * m ∈ normalizer (E : Set G) := by
    refine s7f_mem_normalizer_of_conj_le fun x hx => ?_
    have hx' : m * x * m⁻¹ ∈ E' := ⟨x, hx, by simp [MulAut.conj_apply]⟩
    have h1 := hcE _ hx'
    have h2 : c * m * x * (c * m)⁻¹ = c * (m * x * m⁻¹) * c⁻¹ := by group
    rw [h2]
    exact h1
  obtain ⟨e, he, o, ho, rfl⟩ := s7f_K_eq_mul h36 h76 hP h77b h78 h710d hc hE hAE c hcK
  have hoM : o ∈ MSub S B := (oddCoreIn_normal (MSub S B)).1 ho
  have hom : o * m ∈ normalizer (E : Set G) := by
    have h1 : o * m = e⁻¹ * (e * o * m) := by group
    rw [h1]
    exact (normalizer (E : Set G)).mul_mem
      ((normalizer (E : Set G)).inv_mem (Subgroup.le_normalizer he)) hcmN
  exact ⟨o⁻¹, (oddCoreIn (MSub S B)).inv_mem ho, o * m,
    ⟨(MSub S B).mul_mem hoM hm, hom⟩, by group⟩

end CFSG.OddStandard.SmallF3.Omega
