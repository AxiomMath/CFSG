module

public import Certificates.Certificate442001
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameSylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ComponentClassification.GSThmB

local notation "P45" => Equiv.Perm (Fin 45)

theorem sylowChk_true : Certificates.OmegaT0.sylowChk () = true :=
  (Bool.and_eq_true_iff.1 Certificates.certificate442001).1

theorem n7Chk_true : Certificates.OmegaT0.n7Chk () = true :=
  (Bool.and_eq_true_iff.1 Certificates.certificate442001).2

theorem card_centerIn_QT0 :
    Nat.card (centerIn QT0.originalSubgroup) = 2 := by
  rw [card_centerIn_originalSubgroup QT0 QT0_valid.1]
  have hs := sylowChk_true
  simp only [Certificates.OmegaT0.sylowChk, Bool.and_eq_true, decide_eq_true_eq] at hs
  exact hs.1

theorem centralizer_QT0_le
    {a : P45} (ha : a ∈ QA45.originalSubgroup)
    (h : ∀ t ∈ QT0.originalSubgroup, a * t = t * a) : a ∈ centerIn QT0.originalSubgroup := by
  have hs := sylowChk_true
  simp only [Certificates.OmegaT0.sylowChk, Bool.and_eq_true, decide_eq_true_eq] at hs
  have h2 := forall_of_all QA45 QA45_ok hs.2 a ha
  have hT : (elemsT QT0).all (fun t => decide (a * t = t * a)) = true := by
    rw [List.all_eq_true]
    intro t ht
    exact decide_eq_true (h t ((mem_elemsT QT0 QT0_valid.1 t).1 ht))
  rw [hT] at h2
  have h3 : a ∈ elemsT QT0 := by simpa using h2
  exact mem_centerIn_iff.2 ⟨(mem_elemsT QT0 QT0_valid.1 a).1 h3, h⟩

theorem exists_cover {p : P45}
    (hp : p ∈ QP45.originalSubgroup) (h2 : orderOf p = 2) :
    ∃ c ∈ QP45.originalSubgroup,
      c * p * c⁻¹ = Certificates.OmegaT0.z0 () ∨ c * p * c⁻¹ = Certificates.OmegaT0.yB () := by
  have hn := n7Chk_true
  simp only [Certificates.OmegaT0.n7Chk, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hn
  have hcov := hn.1
  have hp2 : p * p = 1 := by
    have := pow_orderOf_eq_one p
    rwa [h2, pow_two] at this
  have hp1 : p ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at h2
    omega
  have h1 := List.all_eq_true.1 hcov p ((mem_elemsT QP45 QP45_ok p).2 hp)
  rcases Bool.or_eq_true_iff.1 h1 with hA | hB
  · exfalso
    rw [decide_eq_true ⟨hp2, hp1⟩] at hA
    exact absurd hA (by decide)
  · obtain ⟨g, hg, hg2⟩ := List.any_eq_true.1 hB
    obtain ⟨r, hr, hrt⟩ := List.any_eq_true.1 hg2
    have hrt' := of_decide_eq_true hrt
    refine ⟨g, (mem_elemsT QP45 QP45_ok g).1 hg, ?_⟩
    rcases List.mem_cons.1 hr with rfl | hr'
    · exact Or.inl hrt'
    · rw [List.mem_singleton.1 hr'] at hrt'
      exact Or.inr hrt'

theorem isSylow2Of_inf_centralizer
    {r : P45} {k m : ℕ}
    (h1 : Nat.card ↥(QT0.originalSubgroup ⊓ centralizer ({r} : Set P45)) = 2 ^ k)
    (h2 : Nat.card ↥(QP45.originalSubgroup ⊓ centralizer ({r} : Set P45)) = 2 ^ k * m)
    (hm : m % 2 = 1) :
    IsSylow2Of (QT0.originalSubgroup ⊓ centralizer ({r} : Set P45))
      (QP45.originalSubgroup ⊓ centralizer ({r} : Set P45)) := by
  have hle : QT0.originalSubgroup ⊓ centralizer ({r} : Set P45) ≤
      QP45.originalSubgroup ⊓ centralizer ({r} : Set P45) := inf_le_inf_right _ X11.QT0_le
  refine ⟨hle, IsPGroup.of_card h1, ?_⟩
  have h := Subgroup.relIndex_mul_card (H := QT0.originalSubgroup ⊓ centralizer ({r} : Set P45))
    (K := QP45.originalSubgroup ⊓ centralizer ({r} : Set P45))
  rw [inf_eq_left.2 hle, h1, h2] at h
  have h' : (QT0.originalSubgroup ⊓ centralizer ({r} : Set P45)).relIndex
      (QP45.originalSubgroup ⊓ centralizer ({r} : Set P45)) * 2 ^ k = m * 2 ^ k := by
    rw [h, mul_comm]
  have hR := Nat.eq_of_mul_eq_mul_right (by positivity) h'
  rintro ⟨q, hq⟩
  omega

theorem n7_model
    {r : P45}
    (hr : r = Certificates.OmegaT0.z0 () ∨ r = Certificates.OmegaT0.yB ()) :
    r ∈ QT0.originalSubgroup ∧
      IsSylow2Of (QT0.originalSubgroup ⊓ centralizer ({r} : Set P45))
        (QP45.originalSubgroup ⊓ centralizer ({r} : Set P45)) ∧
      r ∈ ⁅QT0.originalSubgroup ⊓ centralizer ({r} : Set P45),
        QT0.originalSubgroup ⊓ centralizer ({r} : Set P45)⁆ := by
  have hn := n7Chk_true
  simp only [Certificates.OmegaT0.n7Chk, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hn
  obtain ⟨-, hzT, hyT, hz576, hzT64, hy96, hyT32, haT, hbT, haz, hbz, hab, hcT, hdT, hcy, hdy,
    hcd⟩ := hn
  have hT := mem_elemsT QT0 QT0_valid.1
  have hTc : ∀ {a r' : P45}, a ∈ elemsT QT0 → a * r' = r' * a →
      a ∈ QT0.originalSubgroup ⊓ centralizer ({r'} : Set P45) := fun ha hc =>
    Subgroup.mem_inf.2 ⟨(hT _).1 ha, Subgroup.mem_centralizer_singleton_iff.2 hc⟩
  rcases hr with rfl | rfl
  · refine ⟨(hT _).1 hzT, isSylow2Of_inf_centralizer (k := 6) (m := 9) ?_ ?_ (by norm_num), ?_⟩
    · rw [card_inf_centralizer QT0 QT0_valid.1]
      exact hzT64
    · rw [card_inf_centralizer QP45 QP45_ok]
      exact hz576
    · have := Subgroup.commutator_mem_commutator (hTc haT haz) (hTc hbT hbz)
      rwa [commutatorElement_def, hab] at this
  · refine ⟨(hT _).1 hyT, isSylow2Of_inf_centralizer (k := 5) (m := 3) ?_ ?_ (by norm_num), ?_⟩
    · rw [card_inf_centralizer QT0 QT0_valid.1]
      exact hyT32
    · rw [card_inf_centralizer QP45 QP45_ok]
      exact hy96
    · have := Subgroup.commutator_mem_commutator (hTc hcT hcy) (hTc hdT hdy)
      rwa [commutatorElement_def, hcd] at this

end CFSG.OddStandard.SmallF3.Omega
