module

public import CFSG.GroupTheory.SmallFixedTwoGroup.LemmaA
public import CFSG.GroupTheory.SmallFixedTwoGroup.PropBTransfer
public import CFSG.LargeExtraspecial.GLRTransfer

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

theorem exists_sylow_eq_centralizer_of_perfect {E : Type*} [Group E] [Finite E]
    (hE : _root_.commutator E = ⊤) {t : E} (ht : orderOf t = 2)
    (hab : ∀ a ∈ centralizer ({t} : Set E), ∀ b ∈ centralizer ({t} : Set E), a * b = b * a)
    (hcard : Nat.card (centralizer ({t} : Set E)) = 8) :
    ∃ S : Sylow 2 E, (S : Subgroup E) = centralizer ({t} : Set E) := by
  classical
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    norm_num at ht
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    simpa [pow_two] using h
  have htmem : t ∈ centralizer ({t} : Set E) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hCp : IsPGroup 2 (centralizer ({t} : Set E)) :=
    IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  obtain ⟨S, hCS⟩ := hCp.exists_le_sylow
  refine ⟨S, le_antisymm ?_ hCS⟩
  by_contra hSC
  have hneCS : centralizer ({t} : Set E) ≠ (S : Subgroup E) :=
    fun h => hSC (le_of_eq h.symm)
  have hlt : Nat.card (centralizer ({t} : Set E)) < Nat.card (S : Subgroup E) :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hCS hneCS)
  have hdvd : 8 ∣ Nat.card (S : Subgroup E) := by
    simpa [hcard] using Subgroup.card_dvd_of_le hCS
  have h16 : 16 ≤ Nat.card (S : Subgroup E) := by
    have hlt8 : 8 < Nat.card (S : Subgroup E) := by
      rw [← hcard]
      exact hlt
    obtain ⟨m, hm⟩ := hdvd
    omega
  let s : S := ⟨t, hCS htmem⟩
  have hCs : Nat.card (centralizer ({s} : Set S)) =
      Nat.card (centralizer ({t} : Set E)) :=
    card_centralizer_subtype_eq (S := (S : Subgroup E)) (t := t) (hCS htmem) hCS
  have h8s : Nat.card (centralizer ({s} : Set S)) ≤ 8 := by
    rw [hCs, hcard]
  have hs : s * s = 1 := by
    apply Subtype.ext
    simpa [s] using ht2
  have hs1 : s ≠ 1 := by
    intro h
    exact ht1 (Subtype.ext_iff.mp h)
  have hsz : s ∉ center S := by
    intro hz
    have htop : centralizer ({s} : Set S) = ⊤ := by
      rw [Subgroup.centralizer_eq_top_iff_subset]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hz
    have h8card : Nat.card (centralizer ({s} : Set S)) = Nat.card S := by
      rw [htop, Subgroup.card_top]
    rw [hCs, hcard] at h8card
    omega
  have hab' : ∀ a ∈ centralizer ({s} : Set S),
      ∀ b ∈ centralizer ({s} : Set S), a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    have haC : (a : E) ∈ centralizer ({t} : Set E) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      simpa [s] using congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp ha)
    have hbC : (b : E) ∈ centralizer ({t} : Set E) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      simpa [s] using congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hb)
    simpa only [Subgroup.coe_mul] using hab (a : E) haC (b : E) hbC
  obtain ⟨M, hMidx, hMinv⟩ :=
    exists_index_two_card_centralizer_ge_sixteen S.isPGroup' h16 hs hs1 hsz hab' h8s
  let U : Subgroup E := M.map (S : Subgroup E).subtype
  have hUle : U ≤ (S : Subgroup E) := Subgroup.map_subtype_le M
  have hUidx : U.relIndex (S : Subgroup E) = 2 := by
    have h := Subgroup.relIndex_map_map_of_injective M (⊤ : Subgroup S)
      (S : Subgroup E).subtype_injective
    simp only [Subgroup.map_top, Subgroup.range_subtype, Subgroup.relIndex_top_right,
      hMidx] at h
    simpa [U] using h
  have htU : t ∉ U := by
    intro htU
    have htU' : t ∈ M.map (S : Subgroup E).subtype := htU
    rw [Subgroup.mem_map] at htU'
    obtain ⟨m, hmM, hm⟩ := htU'
    have hms : m = s := Subtype.ext (by simpa [s] using hm)
    rw [hms] at hmM
    have := hMinv s hmM hs hs1
    omega
  obtain ⟨x, hxU, -⟩ := CFSG.LargeExtraspecial.GLR.exists_extremal_conj_mem_of_sq_eq
    (fun N => index_ne_two_of_commutator_eq_top hE N)
    (T := (S : Subgroup E)) (U := U) (g := t) (d := 1)
    S.isPGroup' S.not_dvd_index hUle hUidx
    (hCS htmem) htU ht2 (by simp) (by intro y hy; simpa using U.one_mem)
  set u : E := x⁻¹ * t * x with hu_def
  have hu_sq : u * u = 1 := by
    rw [hu_def]
    rw [show x⁻¹ * t * x * (x⁻¹ * t * x) = x⁻¹ * (t * t) * x by group, ht2]
    group
  have hxU' : u ∈ M.map (S : Subgroup E).subtype := hxU
  obtain ⟨u', hu'M, hu'eq⟩ := Subgroup.mem_map.mp hxU'
  have hu'val : (u' : E) = u := hu'eq
  have hu'sq : u' * u' = 1 := by
    apply Subtype.ext
    change (u' : E) * (u' : E) = 1
    rw [hu'val]
    exact hu_sq
  have hu'ne : u' ≠ 1 := by
    intro h
    have hu1 : u = 1 := by rw [← hu'eq, h]; rfl
    have hx1 : x⁻¹ * t * x = 1 := by rw [← hu_def]; exact hu1
    have ht_eq : t = 1 := by
      calc t = x * (x⁻¹ * t * x) * x⁻¹ := by group
        _ = x * 1 * x⁻¹ := by rw [hx1]
        _ = 1 := by group
    exact ht1 ht_eq
  have hle16 := hMinv u' hu'M hu'sq hu'ne
  have hle8 : Nat.card (centralizer ({u'} : Set S)) ≤ 8 := by
    calc Nat.card (centralizer ({u'} : Set S))
        ≤ Nat.card (centralizer ({(u' : E)} : Set E)) :=
          card_centralizer_subtype_le (S : Subgroup E) u'
      _ = Nat.card (centralizer ({x⁻¹ * t * x} : Set E)) := by rw [hu'val, hu_def]
      _ = Nat.card (centralizer ({t} : Set E)) := card_centralizer_conj x t
      _ = 8 := hcard
  omega

end CFSG.GroupTheory.SmallFixedTwoGroup
