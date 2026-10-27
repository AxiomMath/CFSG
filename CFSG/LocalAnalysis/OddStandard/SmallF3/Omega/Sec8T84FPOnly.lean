module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPSub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPList
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ElemAbList

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open Certificates.Asc82NormA6 (Facts)
open Certificates.T84P (Elt mulE oneE commE P0l Vl F0l InvP span4)

private lemma sec8t84Prod4_eq_adjoinL {M : Type*} [Group M] (a b c d : M) :
    sec8t84Prod4 a b c d = adjoinL d (adjoinL c (adjoinL b (adjoinL a [1]))) := by
  simp [sec8t84Prod4, adjoinL, mul_one]

private lemma nodup_of_toFinset_card_eq_length {α : Type*} [DecidableEq α] {l : List α}
    (h : l.toFinset.card = l.length) : l.Nodup := by
  rw [List.nodup_iff_length_dedup_eq, ← List.card_toFinset]
  exact h

private lemma nodup_of_forall_mem_iff {M : Type*} [Group M] {A : Subgroup M} {L : List M}
    (hspan : ∀ x, x ∈ A ↔ x ∈ L) (hcard : Nat.card A = 16) (hlen : L.length = 16) :
    L.Nodup := by
  classical
  have hcardL : L.toFinset.card = Nat.card A := by
    rw [← Set.ncard_coe_finset]
    have hset : (L.toFinset : Set M) = (A : Set M) := by
      ext x
      rw [Finset.mem_coe, List.mem_toFinset]
      exact (hspan x).symm
    rw [hset]
    exact (Nat.card_coe_set_eq (A : Set M)).symm
  exact nodup_of_toFinset_card_eq_length (by rw [hcardL, hcard, hlen])

private lemma sec8t84_prod4_basis_of_ne_one_aux {M : Type} [Group M] {A : Subgroup M}
    (hA : IsElemAb2 A 4) {a : M} (ha : a ∈ A) (ha1 : a ≠ 1) :
    ∃ b c d : M, b ∈ A ∧ c ∈ A ∧ d ∈ A ∧ (sec8t84Prod4 a b c d).Nodup ∧
      (∀ x : M, x ∈ A ↔ x ∈ sec8t84Prod4 a b c d) ∧ b ≠ 1 ∧ c ≠ 1 ∧ d ≠ 1 := by
  classical
  have hcard : Nat.card A = 16 := by rw [hA.2]; norm_num
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ x ∈ A, x * x = 1 := by
    intro x hx
    have := hA.1.2 x hx
    simpa [pow_two] using this
  obtain ⟨b, c, d, hb, hc, hd, hbT, hcT, hdT, hspan0⟩ :=
    exists_basis_four A hcard hcomm hsq ha ha1
  have hlist : sec8t84Prod4 a b c d =
      adjoinL d (adjoinL c (adjoinL b (adjoinL a [1]))) :=
    sec8t84Prod4_eq_adjoinL a b c d
  have hlen : (adjoinL d (adjoinL c (adjoinL b (adjoinL a [1])))).length = 16 := by
    simp [length_adjoinL]
  have hspan : ∀ x : M, x ∈ A ↔ x ∈ sec8t84Prod4 a b c d := by
    intro x
    rw [hlist]
    exact hspan0 x
  have h1T1 : (1 : M) ∈ adjoinL a [1] := mem_adjoinL.2 (Or.inl (List.mem_singleton_self _))
  have h1T2 : (1 : M) ∈ adjoinL b (adjoinL a [1]) := mem_adjoinL.2 (Or.inl h1T1)
  have h1T3 : (1 : M) ∈ adjoinL c (adjoinL b (adjoinL a [1])) := mem_adjoinL.2 (Or.inl h1T2)
  refine ⟨b, c, d, hb, hc, hd, ?_, hspan, fun h => hbT (h ▸ h1T1),
    fun h => hcT (h ▸ h1T2), fun h => hdT (h ▸ h1T3)⟩
  rw [hlist]
  exact nodup_of_forall_mem_iff hspan0 hcard hlen

theorem sec8t84FPonly (F : Facts) (G : Certificates.T84P.Facts) :
    ∀ F' : Subgroup (Sec8T84FPM0 F), F' ≤ sec8t84FPP0 F G → IsElemAb2 F' 4 →
      F' = Sec8T84FPV0 F ∨ F' = sec8t84FPF0 F G := by
  intro F' hF'P hF'
  by_cases hle : F' ≤ Sec8T84FPV0 F
  · left
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [sec8t84FPV0_card, hF'.2]
    norm_num
  · right
    obtain ⟨a, haF', haV⟩ := SetLike.not_le_iff_exists.mp hle
    have ha1 : a ≠ 1 := fun h => haV (h ▸ (Sec8T84FPV0 F).one_mem)
    obtain ⟨b, c, d, hbF', hcF', hdF', hnd, hspan, hb1, hc1, hd1⟩ :=
      sec8t84_prod4_basis_of_ne_one_aux hF' haF' ha1
    have hcommF' : ∀ {x y : Sec8T84FPM0 F}, x ∈ F' → y ∈ F' → x * y = y * x :=
      fun {x y} hx hy => congrArg Subtype.val (hF'.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hsqF' : ∀ {x : Sec8T84FPM0 F}, x ∈ F' → x * x = 1 := by
      intro x hx
      have := hF'.1.2 x hx
      simpa [pow_two] using this
    have hrawP : ∀ {x : Sec8T84FPM0 F}, x ∈ F' → sec8t84FPRaw F x ∈ P0l := by
      intro x hx
      have hxP : x ∈ sec8t84FPOfList F P0l G.p0.2.2.1 G.p0.2.2.2.2 := by
        simpa only [sec8t84FPP0] using hF'P hx
      exact (sec8t84FPOfList_mem F G.p0.2.2.1 G.p0.2.2.2.2 x).mp hxP
    have hrawInv : ∀ {x : Sec8T84FPM0 F}, x ∈ F' → x ≠ 1 → sec8t84FPRaw F x ∈ InvP := by
      intro x hx hx1
      rw [InvP, List.mem_filter]
      refine ⟨hrawP hx, ?_⟩
      rw [decide_eq_true_eq]
      exact ⟨fun h => hx1 ((sec8t84FPRaw_eq_oneE_iff F x).mp h),
        (sec8t84FPRaw_mul_self_iff F x).mpr (hsqF' hx)⟩
    have hIa : sec8t84FPRaw F a ∈ InvP := hrawInv haF' ha1
    have hIb : sec8t84FPRaw F b ∈ InvP := hrawInv hbF' hb1
    have hIc : sec8t84FPRaw F c ∈ InvP := hrawInv hcF' hc1
    have hId : sec8t84FPRaw F d ∈ InvP := hrawInv hdF' hd1
    have hIaV : sec8t84FPRaw F a ∉ Vl := fun h => haV ((sec8t84FPV0_mem F a).mpr h)
    have hcommE : ∀ {x y : Sec8T84FPM0 F}, x ∈ F' → y ∈ F' →
        commE (sec8t84FPRaw F x) (sec8t84FPRaw F y) := by
      intro x y hx hy
      rw [sec8t84FPRaw_commE_iff]
      exact hcommF' hx hy
    have hndM : (span4 (sec8t84FPRaw F a) (sec8t84FPRaw F b) (sec8t84FPRaw F c)
        (sec8t84FPRaw F d)).Nodup := by
      rw [← sec8t84FPRaw_prod4 F a b c d]
      exact List.Nodup.map (fun x y h => sec8t84FPRaw_injective F h) hnd
    have hspanF0 : ∀ x ∈ span4 (sec8t84FPRaw F a) (sec8t84FPRaw F b) (sec8t84FPRaw F c)
        (sec8t84FPRaw F d), x ∈ F0l :=
      G.only (sec8t84FPRaw F a) hIa hIaV (sec8t84FPRaw F b) hIb (hcommE haF' hbF')
        (sec8t84FPRaw F c) hIc (hcommE haF' hcF') (hcommE hbF' hcF') (sec8t84FPRaw F d) hId
        (hcommE haF' hdF') (hcommE hbF' hdF') (hcommE hcF' hdF') hndM
    have hF'leF0 : F' ≤ sec8t84FPF0 F G := by
      intro x hx
      have hxspan : sec8t84FPRaw F x ∈
          span4 (sec8t84FPRaw F a) (sec8t84FPRaw F b) (sec8t84FPRaw F c)
            (sec8t84FPRaw F d) := by
        have hxmem : x ∈ sec8t84Prod4 a b c d := (hspan x).mp hx
        rw [← sec8t84FPRaw_prod4 F a b c d]
        exact List.mem_map.mpr ⟨x, hxmem, rfl⟩
      have hxof : x ∈ sec8t84FPOfList F F0l (sec8t84_oneE_F0l G) G.vf.2.1.2.2.2.1 :=
        (sec8t84FPOfList_mem F (sec8t84_oneE_F0l G) G.vf.2.1.2.2.2.1 x).mpr
          (hspanF0 _ hxspan)
      simpa only [sec8t84FPF0] using hxof
    refine Subgroup.eq_of_le_of_card_ge hF'leF0 ?_
    have hcardF0 : Nat.card (sec8t84FPF0 F G) = 16 := by
      have hc : Nat.card (sec8t84FPOfList F F0l (sec8t84_oneE_F0l G)
          G.vf.2.1.2.2.2.1) = 16 := by
        rw [sec8t84FPOfList_card_eq_length F (sec8t84_oneE_F0l G) G.vf.2.1.2.2.2.1
          (fun z hz => G.p0.2.2.2.1 z (G.vf.2.1.2.2.1 z hz)) G.vf.2.1.1, G.vf.2.1.2.1]
      simpa only [sec8t84FPF0] using hc
    rw [hcardF0, hF'.2]
    norm_num

end CFSG.OddStandard.SmallF3.Omega
