module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BHeartAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BAlt8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5InputsB2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {t : G} {L : Subgroup G} {z r : G} {A : Subgroup G}
  {φ : (Fin 6 → ZMod 2) → G}

private lemma sec5b_mem_wclass_iff {φ : (Fin 6 → ZMod 2) → G}
    (hinj : Function.Injective φ) (v : Fin 6 → ZMod 2) (k : ℕ) :
    φ v ∈ wclass φ k ↔ vecWeight v = k := by
  constructor
  · rintro ⟨u, hu, hφ⟩
    rw [hinj hφ] at hu
    exact hu
  · intro hv
    exact ⟨v, hv, rfl⟩

private lemma sec5b_mem_pairSet6_def (v : Fin 6 → ZMod 2) :
    v ∈ pairSet6 ↔ vecWeight v = 1 ∨ vecWeight v = 2 ∨ vecWeight v = 5 ∨ vecWeight v = 6 :=
  Iff.rfl

private lemma sec5b_conjClassIn_conj_iff {H : Subgroup G} {t m x : G} (hm : m ∈ H) :
    m * x * m⁻¹ ∈ conjClassIn H t ↔ x ∈ conjClassIn H t := by
  constructor
  · rintro ⟨h, hh, hhx⟩
    refine ⟨m⁻¹ * h, H.mul_mem (H.inv_mem hm) hh, ?_⟩
    have hx : x = m⁻¹ * (m * x * m⁻¹) * m := by group
    rw [hx, hhx]
    group
  · rintro ⟨h, hh, hhx⟩
    refine ⟨m * h, H.mul_mem hm hh, ?_⟩
    rw [hhx]
    group

theorem sec5b_mem_pairSet6_iff (hm : Sec5Model58 t L z r A φ)
    (ht : conjClassIn (normalizer (A : Set G)) t =
      wclass φ 1 ∪ wclass φ 2 ∪ wclass φ 5 ∪ wclass φ 6) (v : Fin 6 → ZMod 2) :
    v ∈ pairSet6 ↔ φ v ∈ conjClassIn (normalizer (A : Set G)) t := by
  have hinj : Function.Injective φ := hm.perm.injective
  have hw : ∀ k, (φ v ∈ wclass φ k) ↔ vecWeight v = k := fun k =>
    sec5b_mem_wclass_iff hinj v k
  rw [ht]
  have hiff : (v ∈ pairSet6) ↔
      (φ v ∈ wclass φ 1 ∪ wclass φ 2 ∪ wclass φ 5 ∪ wclass φ 6) := by
    rw [sec5b_mem_pairSet6_def]
    simp only [Set.mem_union, hw]
    tauto
  exact hiff

theorem sec5b_conjCoord_mem_pairSet6 (hm : Sec5Model58 t L z r A φ)
    (ht : conjClassIn (normalizer (A : Set G)) t =
      wclass φ 1 ∪ wclass φ 2 ∪ wclass φ 5 ∪ wclass φ 6) {m : G}
    (hmM : m ∈ normalizer (A : Set G)) (v : Fin 6 → ZMod 2) :
    conjCoord φ m v ∈ pairSet6 ↔ v ∈ pairSet6 := by
  have h1 := sec5b_mem_pairSet6_iff hm ht (conjCoord φ m v)
  have h2 := sec5b_mem_pairSet6_iff hm ht v
  have h3 : φ (conjCoord φ m v) ∈ conjClassIn (normalizer (A : Set G)) t ↔
      φ v ∈ conjClassIn (normalizer (A : Set G)) t := by
    rw [hm.perm.conjCoord_spec hmM]
    exact sec5b_conjClassIn_conj_iff hmM
  exact h1.trans (h3.trans h2.symm)

theorem sec5b_exists_perm (f59 : Asc82Fact59) (hm : Sec5Model58 t L z r A φ)
    (ht : conjClassIn (normalizer (A : Set G)) t =
      wclass φ 1 ∪ wclass φ 2 ∪ wclass φ 5 ∪ wclass φ 6) {m : G}
    (hmM : m ∈ normalizer (A : Set G)) :
    ∃ σ : Equiv.Perm (Fin 8), ∀ w : Fin 8 → ZMod 2, IsEvenVec w →
      conjCoord φ m (heartCoord w) = heartCoord (permVec σ w) := by
  refine f59 (conjCoord φ m) (fun v w => hm.perm.conjCoord_add hmM v w) (fun v => ?_)
  exact (sec5b_conjCoord_mem_pairSet6 hm ht hmM v).symm

theorem sec5b_extPerm_mem_heartAlt (hm : Sec5Model58 t L z r A φ) {σ : Equiv.Perm (Fin 6)}
    (hσ : σ ∈ alternatingGroup (Fin 6)) : extPerm σ ∈ hm.perm.heartAlt := by
  have hlift : ∀ σ ∈ alternatingGroup (Fin 6), ∃ h ∈ L ⊓ normalizer (A : Set G),
      ∀ v, True → h * φ v * h⁻¹ = φ (permVec σ v) := by
    have h := hm.perm
    unfold IsPerm6 IsPermModuleVia at h
    exact h.2.2.2.2
  obtain ⟨a, ha, hact⟩ := hlift σ hσ
  have haN : a ∈ normalizer (A : Set G) := ha.2
  show extPerm σ ∈ heartAltSet φ A
  refine ⟨a, haN, fun w _ => ?_⟩
  rw [hm.perm.conjCoord_eq_iff haN, sec5b_heartCoord_extPerm]
  exact hact (heartCoord w) trivial

private lemma sec5b_vecWeight_e01 :
    vecWeight (Pi.single (0 : Fin 6) (1 : ZMod 2) + Pi.single (1 : Fin 6) (1 : ZMod 2)) = 2 := by
  decide +kernel

private lemma sec5b_isEvenVec_e67 :
    IsEvenVec (Pi.single (6 : Fin 8) (1 : ZMod 2) + Pi.single (7 : Fin 8) (1 : ZMod 2)) := by
  unfold IsEvenVec
  decide +kernel

theorem sec5b_heartAlt_move (f59 : Asc82Fact59) (hm : Sec5Model58 t L z r A φ)
    (ht : conjClassIn (normalizer (A : Set G)) t =
      wclass φ 1 ∪ wclass φ 2 ∪ wclass φ 5 ∪ wclass φ 6) :
    ∃ x ∈ hm.perm.heartAlt, (x 6).val < 6 ∧ (x 7).val < 6 := by
  set e : Fin 6 → ZMod 2 :=
    Pi.single (0 : Fin 6) (1 : ZMod 2) + Pi.single (1 : Fin 6) (1 : ZMod 2) with he
  have hwe : vecWeight e = 2 := by rw [he]; exact sec5b_vecWeight_e01
  have hφe : φ e ∈ conjClassIn (normalizer (A : Set G)) t := by
    rw [ht]
    have he2 : φ e ∈ wclass φ 2 := (sec5b_mem_wclass_iff hm.perm.injective e 2).mpr hwe
    exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ he2))
  obtain ⟨m, hmN, hmeq⟩ := hφe
  have hconj : conjCoord φ m 1 = e := by
    rw [hm.perm.conjCoord_eq_iff hmN]
    rw [show (1 : Fin 6 → ZMod 2) = (fun _ => 1) from rfl, hm.map_one]
    exact hmeq.symm
  obtain ⟨σ, hσ⟩ := sec5b_exists_perm f59 hm ht hmN
  set w₀ : Fin 8 → ZMod 2 :=
    Pi.single (6 : Fin 8) (1 : ZMod 2) + Pi.single (7 : Fin 8) (1 : ZMod 2) with hw₀
  have hw₀even : IsEvenVec w₀ := by rw [hw₀]; exact sec5b_isEvenVec_e67
  have hheart : heartCoord (permVec σ w₀) = e := by
    rw [← hσ w₀ hw₀even]
    rw [hw₀, sec5b_heartCoord_pair_six_seven, hconj]
  have hweight : vecWeight (heartCoord (permVec σ w₀)) = 2 := by
    rw [hheart, hwe]
  refine ⟨σ, ?_, sec5b_move_of_heartCoord hweight⟩
  show σ ∈ heartAltSet φ A
  exact ⟨m, hmN, hσ⟩

theorem sec5b_heartA8 (f59 : Asc82Fact59) (hm : Sec5Model58 t L z r A φ)
    (ht : conjClassIn (normalizer (A : Set G)) t =
      wclass φ 1 ∪ wclass φ 2 ∪ wclass φ 5 ∪ wclass φ 6) :
    ∃ Alt : Subgroup (Equiv.Perm (Fin 8)), (Alt = alternatingGroup (Fin 8) ∨ Alt = ⊤) ∧
      IsHeartA8 A (normalizer (A : Set G)) Alt := by
  refine ⟨hm.perm.heartAlt, sec5b_alt8_cases ?_, hm.perm.isHeartA8_heartAlt ?_⟩
  · exact sec5b_alt8_le (fun σ hσ => sec5b_extPerm_mem_heartAlt hm hσ)
      (sec5b_heartAlt_move f59 hm ht)
  · intro m hmM
    exact sec5b_exists_perm f59 hm ht hmM

end CFSG.OddStandard.SmallF3.Omega
