module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XInner
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173
open scoped commutatorElement

variable {Ω : Type} [Group Ω] {S B : Subgroup Ω} {G₀ : Type} [Group G₀]

@[expose] def piImg (M : S172X.S172Model S B G₀) (X : Subgroup Ω) : Subgroup G₀ := (X.subgroupOf S).map M.π

theorem K_le_of_cfg173 {p : ℕ} [Finite Ω] {N D K : Subgroup Ω} {x : Ω} (hcfg : Cfg173 p S B N D K x) : K ≤ S := by
  rw [hcfg.std.2.2.2.2.1]
  exact (Y10F.glaLayer_le _).trans inf_le_left

theorem closureIn_le_of_normal {K H : Subgroup Ω} (hS : S.Normal) (hK : K ≤ S) : closureIn K H ≤ S := by
  refine iSup₂_le fun a _ => ?_
  rintro _ ⟨k, hk, rfl⟩
  exact hS.conj_mem k (hK hk) a

private lemma exists_two_subgroup_of_hb_aux1 (M : S172X.S172Model S B G₀) {T : Subgroup Ω}
    (hTn : B ≤ Subgroup.normalizer (T : Set Ω)) :
    M.β.range ≤ Subgroup.normalizer (piImg M T : Set G₀) := by
  rintro _ ⟨b, rfl⟩
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hh
    have htT : (t : Ω) ∈ T := Subgroup.mem_subgroupOf.1 ht
    have hconj := Subgroup.mem_normalizer_iff.1 (hTn b.2) (t : Ω)
    have hmem : M.conjHom b t ∈ T.subgroupOf S := by
      rw [Subgroup.mem_subgroupOf, M.coe_conjHom]
      exact hconj.1 htT
    exact Subgroup.mem_map.2 ⟨M.conjHom b t, hmem, M.π_conjHom b t⟩
  · intro hh
    obtain ⟨t, rfl⟩ := M.surj h
    obtain ⟨t', ht', ht'eq⟩ := Subgroup.mem_map.1 hh
    have htT : (t' : Ω) ∈ T := Subgroup.mem_subgroupOf.1 ht'
    have hconj := Subgroup.mem_normalizer_iff''.1 (hTn b.2) (t' : Ω)
    have hmem : M.conjHom (b⁻¹) t' ∈ T.subgroupOf S := by
      rw [Subgroup.mem_subgroupOf, M.coe_conjHom]
      simpa only [Subgroup.coe_inv, inv_inv] using hconj.1 htT
    refine Subgroup.mem_map.2 ⟨M.conjHom (b⁻¹) t', hmem, ?_⟩
    simp only [M.π_conjHom, map_inv, ht'eq]
    group

private lemma exists_two_subgroup_of_hb_aux2 (M : S172X.S172Model S B G₀) {T : Subgroup Ω}
    (hTS : T ≤ S) (hcomm : (⁅T, B⁆ : Subgroup Ω) ≠ ⊥) : piImg M T ≠ ⊥ := by
  intro hbot
  apply hcomm
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hker : T.subgroupOf S ≤ M.π.ker :=
    (Subgroup.map_eq_bot_iff (T.subgroupOf S)).1 (by simpa only [piImg] using hbot)
  have htS : t ∈ S := hTS ht
  have hz : (⟨t, htS⟩ : ↥S) ∈ Subgroup.center ↥S := by
    rw [← M.ker_π]
    exact hker (Subgroup.mem_subgroupOf.2 ht)
  obtain ⟨s, c, hc, hb', -⟩ := M.split ⟨b, hb⟩
  have hb'' : b = (s : Ω) * c := hb'
  have hct : c * t = t * c := (Subgroup.mem_centralizer_iff.1 hc t htS).symm
  have hst : (s : Ω) * t = t * (s : Ω) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hz s)
  calc b * t = (s : Ω) * c * t := by rw [hb'']
    _ = (s : Ω) * (c * t) := by group
    _ = (s : Ω) * (t * c) := by rw [hct]
    _ = ((s : Ω) * t) * c := by group
    _ = (t * (s : Ω)) * c := by rw [hst]
    _ = t * ((s : Ω) * c) := by group
    _ = t * b := by rw [hb'']

theorem exists_two_subgroup_of_hb {p : ℕ} [Finite Ω] {N D K : Subgroup Ω} {x : Ω} (hcfg : Cfg173 p S B N D K x)
    (M : S172X.S172Model S B G₀) :
    ∃ T' : Subgroup G₀, T' ≠ ⊥ ∧ IsPGroup 2 T' ∧ M.β.range ≤ Subgroup.normalizer (T' : Set G₀) := by
  obtain ⟨T, hTS, hT2, hBn, hcomm⟩ := hcfg.hb
  exact ⟨piImg M T, exists_two_subgroup_of_hb_aux2 M hTS hcomm,
    (hT2.comap_subtype (K := S)).map M.π, exists_two_subgroup_of_hb_aux1 M hBn⟩

private lemma exists_two_subgroup_of_hc_aux1 (M : S172X.S172Model S B G₀) {T I : Subgroup Ω}
    (hIn : I ≤ Subgroup.normalizer (T : Set Ω)) :
    piImg M I ≤ Subgroup.normalizer (piImg M T : Set G₀) := by
  rintro _ ⟨i, hi, rfl⟩
  have hiI : (i : Ω) ∈ I := Subgroup.mem_subgroupOf.1 hi
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hh
    have htT : (t : Ω) ∈ T := Subgroup.mem_subgroupOf.1 ht
    have hconj := Subgroup.mem_normalizer_iff.1 (hIn hiI) (t : Ω)
    have hmem : i * t * i⁻¹ ∈ T.subgroupOf S := by
      rw [Subgroup.mem_subgroupOf]
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hconj.1 htT
    exact Subgroup.mem_map.2 ⟨i * t * i⁻¹, hmem, by simp only [map_mul, map_inv]⟩
  · intro hh
    obtain ⟨t, rfl⟩ := M.surj h
    obtain ⟨t', ht', ht'eq⟩ := Subgroup.mem_map.1 hh
    have htT : (t' : Ω) ∈ T := Subgroup.mem_subgroupOf.1 ht'
    have hconj := Subgroup.mem_normalizer_iff''.1 (hIn hiI) (t' : Ω)
    have hmem : i⁻¹ * t' * i ∈ T.subgroupOf S := by
      rw [Subgroup.mem_subgroupOf]
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hconj.1 htT
    refine Subgroup.mem_map.2 ⟨i⁻¹ * t' * i, hmem, ?_⟩
    simp only [map_mul, map_inv, ht'eq]
    group

private lemma exists_two_subgroup_of_hc_aux2 (M : S172X.S172Model S B G₀) {T I : Subgroup Ω}
    (hTS : T ≤ S) (hIS : I ≤ S) (hbot : piImg M T = ⊥) : (⁅I, T⁆ : Subgroup Ω) = ⊥ := by
  have hker : T.subgroupOf S ≤ M.π.ker :=
    (Subgroup.map_eq_bot_iff (T.subgroupOf S)).1 (by simpa only [piImg] using hbot)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro i hi
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have htS : t ∈ S := hTS ht
  have hz : (⟨t, htS⟩ : ↥S) ∈ Subgroup.center ↥S := by
    rw [← M.ker_π]
    exact hker (Subgroup.mem_subgroupOf.2 ht)
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨i, hIS hi⟩)).symm

theorem exists_two_subgroup_of_hc {p : ℕ} [Finite Ω] {N D K : Subgroup Ω} {x : Ω} (hcfg : Cfg173 p S B N D K x)
    (M : S172X.S172Model S B G₀) :
    ∃ T' : Subgroup G₀, T' ≠ ⊥ ∧ IsPGroup 2 T' ∧
      piImg M (closureIn K N) ⊔ M.β.range ≤ Subgroup.normalizer (T' : Set G₀) := by
  obtain ⟨T, hTS, hT2, hInB, hcomm⟩ := hcfg.hc
  have hKS : K ≤ S := K_le_of_cfg173 hcfg
  have hIS : closureIn K N ≤ S := closureIn_le_of_normal hcfg.normal hKS
  refine ⟨piImg M T, ?_, (hT2.comap_subtype (K := S)).map M.π, ?_⟩
  · intro hbot
    exact hcomm (exists_two_subgroup_of_hc_aux2 M hTS hIS hbot)
  · exact sup_le (exists_two_subgroup_of_hc_aux1 M (le_trans le_sup_left hInB))
      (exists_two_subgroup_of_hb_aux1 M (le_trans le_sup_right hInB))

end CFSG.LocalAnalysis.GLTheoremA.T173X

end
