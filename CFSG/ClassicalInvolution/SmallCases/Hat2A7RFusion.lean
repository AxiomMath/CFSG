module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7RDiag
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7ROmega5
public import CFSG.ClassicalInvolution.Asc77.AscFusionB

public section

namespace CFSG.ClassicalInvolution.Hat2A7R

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.AscFusion CFSG.ComponentClassification.CatalogueBPrimeJoin
open scoped commutatorElement

section Order4

variable {F : Type} [Group F] [Finite F] {J K : Subgroup F} {t z : F}

theorem mem_normalizer_of_commute_orderOf_four (hJ : IsClassical2A7 ⊤ J t)
    (hK : IsClassical2A7 ⊤ K z) {a : F} (haJ : a ∈ J) (ha4 : orderOf a = 4)
    (haz : a * z = z * a) : t ∈ Subgroup.normalizer (K : Set F) := by
  classical
  by_contra hu
  have ha2 : a * a = t := by
    have h2 : orderOf (a ^ 2) = 2 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [ha4]; norm_num), ha4]
    rw [← pow_two]
    exact hJ.eq_of_orderOf_eq_two (J.pow_mem haJ 2) h2
  have hu2 : t * t = 1 := hJ.mul_self
  have hua : t * a = a * t := by rw [← ha2]; group
  have hur : t * z = z * t := by
    rw [← ha2, mul_assoc, haz, ← mul_assoc, haz, mul_assoc]
  have hne : K ≠ conjSub t K := fun h => hu (map_conj_eq_iff_mem_normalizer.mp h.symm)
  obtain ⟨hK'mem, hK'N, hKN', -⟩ := twin_facts_a7 hK hur hne
  obtain ⟨L, hLM, hLfix, hLperf, hLqs, hLsub, hLnc⟩ := exists_twin_diagonal_a7 hK hu2 hur hne
  set K' : Subgroup F := conjSub t K with hK'def
  set M : Subgroup F := K ⊔ K' with hMdef
  have hKHz : K ≤ Subgroup.centralizer ({z} : Set F) := hK.le_centralizer
  have hK'Hz : K' ≤ Subgroup.centralizer ({z} : Set F) := hK'mem.le_centralizer
  have hMK : M ≤ Subgroup.normalizer (K : Set F) := sup_le Subgroup.le_normalizer hK'N
  set Ct : Subgroup F := Subgroup.centralizer ({t} : Set F) with hCt
  set R : Subgroup F := Subgroup.centralizer ({z} : Set F) ⊓ Ct with hRdef
  have hLR : L ≤ R := by
    intro x hx
    refine ⟨sup_le hKHz hK'Hz (hLM hx), ?_⟩
    show x ∈ Subgroup.centralizer ({t} : Set F)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hLfix x hx
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hLcomp : IsPComponent 2 (L.subgroupOf R) := by
    refine (pComponent_subgroupOf_iff 2 L R hLR).mpr ⟨hLsub, ?_, hLqs⟩
    have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLperf
    exact primeResidual_two_eq_top_of_isPerfect ↥L
  have hJsn : (J.subgroupOf Ct).IsSubnormal := subnormal_subgroupOf_centralizer hJ
  have hJsnR : (J.subgroupOf R).IsSubnormal := by
    have h1 := hJsn.comap (Subgroup.inclusion (inf_le_right : R ≤ Ct))
    have h2 : (J.subgroupOf Ct).comap (Subgroup.inclusion (inf_le_right : R ≤ Ct)) =
        J.subgroupOf R := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [h2] at h1
  have haR : a ∈ R := by
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr haz, ?_⟩
    show a ∈ Subgroup.centralizer ({t} : Set F)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hua.symm
  have haJR : (⟨a, haR⟩ : ↥R) ∈ J.subgroupOf R := haJ
  rcases contains_or_normalizes_core 2 (L.subgroupOf R) (J.subgroupOf R) hLcomp hJsnR with
    hle | ⟨hnorm, -⟩
  ·
    have hLJ : ∀ x ∈ L, x ∈ J := fun x hx => hle (show (⟨x, hLR hx⟩ : ↥R) ∈ L.subgroupOf R from hx)
    obtain ⟨q, hq', ℓ, hℓ, hqℓ⟩ : ∃ q ∈ K, ∃ ℓ ∈ L, ⁅q, ℓ⁆ ∉ oddCoreOf K := by
      by_contra h
      push Not at h
      exact hLnc h
    have hℓ1 : ℓ ≠ 1 := by
      rintro rfl
      exact hqℓ (by rw [commutatorElement_one_right]; exact Subgroup.one_mem _)
    have hLperf' : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLperf
    have : Nontrivial ↥L := ⟨⟨⟨ℓ, hℓ⟩, 1, fun h => hℓ1 (congrArg Subtype.val h)⟩⟩
    have hevenL : 2 ∣ Nat.card ↥L := by
      by_contra h2
      have hodd : Odd (Nat.card ↥L) := Nat.odd_iff.mpr (by omega)
      exact Group.IsPerfect.not_isSolvable ↥L (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
    obtain ⟨ℓ₂, hℓ₂⟩ := exists_prime_orderOf_dvd_card' 2 hevenL
    have hℓ₂t : (ℓ₂ : F) = t :=
      hJ.eq_of_orderOf_eq_two (hLJ _ ℓ₂.2) (by rw [Subgroup.orderOf_coe]; exact hℓ₂)
    exact hu (hMK (hLM (hℓ₂t ▸ ℓ₂.2)))
  ·
    have hnormA : (⟨a, haR⟩ : ↥R) ∈ Subgroup.normalizer ((L.subgroupOf R : Subgroup ↥R) : Set ↥R) :=
      hnorm haJR
    have hnormAinv : (⟨a, haR⟩ : ↥R)⁻¹ ∈
        Subgroup.normalizer ((L.subgroupOf R : Subgroup ↥R) : Set ↥R) :=
      (Subgroup.normalizer _).inv_mem hnormA
    have hLconj : L ≤ conjSub a M := by
      intro x hx
      rw [mem_conjSub_iff]
      have hxR : (⟨x, hLR hx⟩ : ↥R) ∈ L.subgroupOf R := hx
      have h1 := ((Subgroup.mem_normalizer_iff.mp hnormAinv) _).mp hxR
      have h2 : a⁻¹ * x * a⁻¹⁻¹ ∈ L := h1
      rw [inv_inv] at h2
      exact hLM h2
    have hMconj : conjSub a M = conjSub a K ⊔ conjSub a K' := by
      rw [hMdef, conjSub, Subgroup.map_sup]
      rfl
    have hKaK : K ≠ conjSub a K := by
      intro h
      apply hu
      have hanorm : a ∈ Subgroup.normalizer (K : Set F) :=
        map_conj_eq_iff_mem_normalizer.mp h.symm
      have := Subgroup.mul_mem _ hanorm hanorm
      rwa [ha2] at this
    have hK'aK : K ≠ conjSub a K' := by
      intro h
      apply hu
      have h1 : conjSub (a * t) K = K := by
        rw [conjSub_mul]
        exact h.symm
      have hau : a * t ∈ Subgroup.normalizer (K : Set F) :=
        map_conj_eq_iff_mem_normalizer.mp h1
      have hinv : a⁻¹ = a * t :=
        inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ha2, hu2])
      rw [← hinv] at hau
      have hanorm : a ∈ Subgroup.normalizer (K : Set F) := by
        simpa using (Subgroup.normalizer (K : Set F)).inv_mem hau
      have := Subgroup.mul_mem _ hanorm hanorm
      rwa [ha2] at this
    have hatz : a * t * z = z * (a * t) := by
      rw [mul_assoc, hur, ← mul_assoc, haz, mul_assoc]
    have hK'a : conjSub a K' ∈ omegaAt K z z := by
      rw [hK'def, ← conjSub_mul]
      exact conjSub_mem_omegaAt hatz
    obtain ⟨hKaN, -, hKKa⟩ := twins_oddCoreOf hK (conjSub_mem_omegaAt haz) (Ne.symm hKaK)
    obtain ⟨hK'aN, -, hKK'a⟩ := twins_oddCoreOf hK hK'a (Ne.symm hK'aK)
    have hcommK : ⁅conjSub a K ⊔ conjSub a K', K⁆ ≤ oddCoreOf K :=
      CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize _ _ _ _
        (by rw [Subgroup.commutator_comm]; exact hKKa.trans inf_le_left)
        (by rw [Subgroup.commutator_comm]; exact hKK'a.trans inf_le_left)
        (fun g hg => mem_normalizer_oddCoreOf' (hKaN hg))
        (fun g hg => mem_normalizer_oddCoreOf' (hK'aN hg))
    apply hLnc
    intro q hq' ℓ hℓ
    have hℓM : ℓ ∈ conjSub a K ⊔ conjSub a K' := hMconj ▸ hLconj hℓ
    have h1 : ⁅ℓ, q⁆ ∈ ⁅conjSub a K ⊔ conjSub a K', K⁆ :=
      Subgroup.commutator_mem_commutator hℓM hq'
    have h2 := hcommK h1
    rw [← commutatorElement_inv]
    exact (oddCoreOf K).inv_mem h2

end Order4

section Assembly

theorem prop369iii : Prop369iii := by
  intro F _ _ _ _ J K t z hJ hK _ htK a haJ ha4 haz
  exact htK (mem_normalizer_of_commute_orderOf_four hJ hK haJ ha4 haz)

theorem prop366i_of_prop37x (h : Prop37x) : Prop366i :=
  prop366i_of_steps prop369iii h

theorem a7Omega5_of_prop37x (h : Prop37x) : A7Omega5 :=
  a7Omega5_of_prop366i (prop366i_of_prop37x h)

theorem citSimplePerfect_of_thmI_prop37x (h1 : Generic.CITSimplePerfectSL2) (T : A7ThmI)
    (h : Prop37x) : CITSimplePerfect :=
  citSimplePerfect_of_thmI h1 T (a7Omega5_of_prop37x h)

end Assembly

end CFSG.ClassicalInvolution.Hat2A7R
