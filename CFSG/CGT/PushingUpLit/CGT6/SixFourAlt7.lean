module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourPrinted

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open Equiv
open scoped commutatorElement

section FixedPoint

variable {M : Type*} [Group M] [Finite M]

theorem exists_fixed_point_fin7 [IsSimpleGroup M] (h60 : Nat.card M = 60) (f : M →* Perm (Fin 7)) :
    ∃ p : Fin 7, ∀ m : M, f m p = p := by
  classical
  let _ : MulAction M (Fin 7) := MulAction.compHom (Fin 7) f
  have hsmall : ∀ p : Fin 7, (∀ m : M, f m p = p) ∨ 5 ≤ (MulAction.orbit M p).ncard := by
    intro p
    rw [← MulAction.index_stabilizer M p]
    set S := MulAction.stabilizer M p with hS
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S.normalCore with h | h
    · right
      have hdvd := S.index_normalCore_dvd_factorial_index
      rw [h, Subgroup.index_bot, h60] at hdvd
      by_contra hlt
      push Not at hlt
      obtain ⟨d, hd⟩ : ∃ d, d = S.index := ⟨_, rfl⟩
      rw [← hd] at hdvd hlt
      interval_cases d <;> simp [Nat.factorial] at hdvd
    · left
      intro m
      have hST : S = ⊤ := top_le_iff.mp (h ▸ S.normalCore_le)
      have hm : m ∈ S := hST ▸ Subgroup.mem_top m
      exact MulAction.mem_stabilizer_iff.mp hm
  by_contra hno
  push Not at hno
  have h5 : ∀ p : Fin 7, 5 ≤ (MulAction.orbit M p).ncard := by
    intro p
    rcases hsmall p with h | h
    · obtain ⟨m, hm⟩ := hno p
      exact absurd (h m) hm
    · exact h
  have hO0le : (MulAction.orbit M (0 : Fin 7)).ncard ≤ 7 := by
    have := Set.ncard_le_ncard (Set.subset_univ (MulAction.orbit M (0 : Fin 7)))
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have hO0ne : (MulAction.orbit M (0 : Fin 7)).ncard ≠ 7 := by
    intro h7
    rw [← MulAction.index_stabilizer M (0 : Fin 7)] at h7
    have hdvd := Subgroup.index_dvd_card (MulAction.stabilizer M (0 : Fin 7))
    rw [h7, h60] at hdvd
    omega
  have hex : ∃ p₁ : Fin 7, p₁ ∉ MulAction.orbit M (0 : Fin 7) := by
    by_contra hall
    push Not at hall
    have : MulAction.orbit M (0 : Fin 7) = Set.univ := Set.eq_univ_of_forall hall
    rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hO0ne
    exact hO0ne rfl
  obtain ⟨p₁, hp₁⟩ := hex
  have hdisj : Disjoint (MulAction.orbit M (0 : Fin 7)) (MulAction.orbit M p₁) := by
    rw [Set.disjoint_left]
    intro x hx0 hx1
    apply hp₁
    have e0 : MulAction.orbit M x = MulAction.orbit M (0 : Fin 7) := MulAction.orbit_eq_iff.mpr hx0
    have e1 : MulAction.orbit M x = MulAction.orbit M p₁ := MulAction.orbit_eq_iff.mpr hx1
    rw [← e0, e1]
    exact MulAction.mem_orbit_self p₁
  have hU := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  have hle : (MulAction.orbit M (0 : Fin 7) ∪ MulAction.orbit M p₁).ncard ≤ 7 := by
    have := Set.ncard_le_ncard (Set.subset_univ (MulAction.orbit M (0 : Fin 7) ∪ MulAction.orbit M p₁))
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have h50 := h5 0
  have h51 := h5 p₁
  omega

end FixedPoint

section Stabilizer

theorem exists_stab_alt7 (p : Fin 7) :
    ∃ P : Subgroup (alternatingGroup (Fin 7)), (∀ k : alternatingGroup (Fin 7), k ∈ P ↔ (k : Perm (Fin 7)) p = p) ∧
      Nonempty (P ≃* alternatingGroup (Fin 6)) := by
  classical
  let s : Finset (Fin 7) := Finset.univ.erase p
  refine ⟨(alternatingGroup.ofSubtype s).range, ?_, ?_⟩
  · intro k
    rw [alternatingGroup.mem_range_ofSubtype_iff]
    constructor
    · intro h
      by_contra hne
      have h1 : p ∈ (k : Perm (Fin 7)).support := Equiv.Perm.mem_support.mpr hne
      have h2 := h h1
      simp [s] at h2
    · intro hk x hx
      simp only [s, Finset.mem_erase, Finset.mem_univ, and_true]
      rintro rfl
      exact (Equiv.Perm.mem_support.mp hx) hk
  · have hcard : Fintype.card s = 6 := by simp [s]
    let e : s ≃ Fin 6 := Fintype.equivFinOfCardEq hcard
    exact ⟨(MonoidHom.ofInjective (alternatingGroup.ofSubtype_injective (s := s))).symm.trans
      e.altCongrHom⟩

end Stabilizer

section Descent

theorem exists_alt6_sub_of_alt7 {K : Type*} [Group K] [Finite K]
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 7))
    (hodd : Odd (Nat.card (Subgroup.center K))) {Y₀ : Subgroup K} (hY : IsSimpleGroup Y₀)
    (h60 : Nat.card Y₀ = 60) :
    ∃ K' : Subgroup K, Y₀ ≤ K' ∧ commutator K' = ⊤ ∧ Odd (Nat.card (Subgroup.center K')) ∧
      Nonempty (K' ⧸ Subgroup.center K' ≃* alternatingGroup (Fin 6)) := by
  classical
  have := hY
  let ε : K →* alternatingGroup (Fin 7) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hε : Function.Surjective ε := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ∀ k : K, ε k = 1 ↔ k ∈ Subgroup.center K := by
    intro k
    show e (QuotientGroup.mk' (Subgroup.center K) k) = 1 ↔ k ∈ Subgroup.center K
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff k
  let f : Y₀ →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp (ε.comp Y₀.subtype)
  obtain ⟨p, hp⟩ := exists_fixed_point_fin7 h60 f
  obtain ⟨P, hPmem, ⟨eP⟩⟩ := exists_stab_alt7 p
  have hPperf : Group.IsPerfect P := by
    have : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
    exact Group.IsPerfect.ofSurjective (f := eP.symm.toMonoidHom) eP.symm.surjective
  have hPP : ⁅P, P⁆ = P := Subgroup.isPerfect_iff.mp hPperf
  obtain ⟨Pt, hPt⟩ : ∃ Pt : Subgroup K, Pt = P.comap ε := ⟨_, rfl⟩
  have hmemPt : ∀ x : K, x ∈ Pt ↔ ε x ∈ P := fun x => by rw [hPt]; rfl
  have hmapPt : Pt.map ε = P := by
    rw [hPt]
    exact Subgroup.map_comap_eq_self_of_surjective hε P
  obtain ⟨K', hK'⟩ : ∃ K' : Subgroup K, K' = ⁅Pt, Pt⁆ := ⟨_, rfl⟩
  have hmapK' : K'.map ε = P := by
    rw [hK', Subgroup.map_commutator, hmapPt, hPP]
  have hK'Pt : K' ≤ Pt := by
    rw [hK']
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    rw [commutatorElement_def]
    exact Pt.mul_mem (Pt.mul_mem (Pt.mul_mem hx hy) (Pt.inv_mem hx)) (Pt.inv_mem hy)
  have hdec : ∀ x ∈ Pt, ∃ z ∈ Subgroup.center K, ∃ k ∈ K', x = z * k := by
    intro x hx
    have h1 : ε x ∈ K'.map ε := hmapK'.symm ▸ (hmemPt x).mp hx
    obtain ⟨k, hk, hkx⟩ := h1
    refine ⟨x * k⁻¹, (hker _).mp (by rw [map_mul, map_inv, hkx, mul_inv_cancel]), k, hk, ?_⟩
    group
  have hK'K' : ⁅K', K'⁆ = K' := by
    apply le_antisymm
    · refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
      rw [commutatorElement_def]
      exact K'.mul_mem (K'.mul_mem (K'.mul_mem hx hy) (K'.inv_mem hx)) (K'.inv_mem hy)
    · rw [hK']
      refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
      obtain ⟨z, hz, k, hk, rfl⟩ := hdec x hx
      obtain ⟨w, hw, l, hl, rfl⟩ := hdec y hy
      rw [commutatorElement_central_mul hz hw, ← hK']
      exact Subgroup.commutator_mem_commutator hk hl
  have hperf : commutator K' = ⊤ :=
    (Subgroup.isPerfect_iff.mpr hK'K').commutator_eq_top
  have hY₀perf : ⁅Y₀, Y₀⁆ = Y₀ := by
    have hnc := not_comm_of_simple_card_sixty h60
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Y₀) with h | h
    · exfalso
      apply hnc
      intro a b
      have h1 : ⁅a, b⁆ ∈ commutator Y₀ := by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    · exact Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr h)
  have hY₀Pt : Y₀ ≤ Pt := fun y hy => (hmemPt y).mpr ((hPmem _).mpr (hp ⟨y, hy⟩))
  have hY₀K' : Y₀ ≤ K' := by
    calc Y₀ = ⁅Y₀, Y₀⁆ := hY₀perf.symm
      _ ≤ ⁅Pt, Pt⁆ := Subgroup.commutator_mono hY₀Pt hY₀Pt
      _ = K' := hK'.symm
  have hmemP : ∀ k : K', ε (k : K) ∈ P := fun k => (hmemPt k).mp (hK'Pt k.2)
  let g : K' →* P := (ε.comp K'.subtype).codRestrict P hmemP
  have hgval : ∀ k : K', ((g k : P) : alternatingGroup (Fin 7)) = ε (k : K) := fun k => rfl
  have hg : Function.Surjective g := by
    intro π
    have h1 : (π : alternatingGroup (Fin 7)) ∈ K'.map ε := hmapK'.symm ▸ π.2
    obtain ⟨k, hk, hkπ⟩ := h1
    exact ⟨⟨k, hk⟩, Subtype.ext hkπ⟩
  have hgker : ∀ k : K', g k = 1 ↔ (k : K) ∈ Subgroup.center K := by
    intro k
    rw [← hker, ← hgval k]
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      exact Subtype.ext h
  have hcenP : ∀ π : P, π ∈ Subgroup.center P → π = 1 := by
    intro π hπ
    have h1 : eP π ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro a
      have h2 := Subgroup.mem_center_iff.mp hπ (eP.symm a)
      have h3 := congrArg eP h2
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
      exact h3
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at h1
    exact eP.injective (h1.trans (map_one eP).symm)
  have hcen : Subgroup.center K' = g.ker := by
    refine Subgroup.ext fun k => ?_
    show k ∈ Subgroup.center K' ↔ g k = 1
    rw [hgker]
    constructor
    · intro hk
      have h1 : g k ∈ Subgroup.center P := by
        rw [Subgroup.mem_center_iff]
        intro π
        obtain ⟨k', rfl⟩ := hg π
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hk k']
      have := hcenP _ h1
      exact (hgker k).mp this
    · intro hk
      rw [Subgroup.mem_center_iff]
      intro k'
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp hk k')
  refine ⟨K', hY₀K', hperf, ?_, ?_⟩
  ·
    have hle : (Subgroup.center K').map K'.subtype ≤ Subgroup.center K := by
      rintro _ ⟨k, hk, rfl⟩
      have hk' : g k = 1 := by
        have : k ∈ g.ker := hcen ▸ hk
        exact this
      exact (hgker k).mp hk'
    have hdvd : Nat.card (Subgroup.center K') ∣ Nat.card (Subgroup.center K) := by
      rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective K')]
      exact Subgroup.card_dvd_of_le hle
    exact Odd.of_dvd_nat hodd hdvd
  · refine ⟨((QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)).trans eP⟩

end Descent

end CFSG.CGT.PushingUpLit.CGT6
