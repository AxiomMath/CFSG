module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2B
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2Fam
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open Matrix
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.SecIdE2

namespace TwinDisc

namespace ExitO2

variable {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)}

theorem fam_mem_omegaStarNbr_of_elt (F : Q8Fam Y Δ) {L L' : Subgroup Y} (hL' : L' ∈ Δ)
    (hne : L' ≠ L) {x : Y} (hx : x ∈ L') (hx4 : orderOf x = 4)
    (hxN : x ∈ Subgroup.normalizer (L : Set Y)) : L' ∈ omegaStarNbr Δ L := by
  refine ⟨hL', hne, Subgroup.zpowers x, ?_, Subgroup.zpowers_le.mpr hx,
    Subgroup.zpowers_le.mpr hxN⟩
  exact mem_USet_of_natCard hL' ⟨le_rfl, F.two L' hL', fun V hV _ hLV => le_antisymm hV hLV⟩
    (Subgroup.zpowers_le.mpr hx) inferInstance
    (by rw [F.card L' hL', Nat.card_zpowers, hx4]; norm_num)

theorem Q8Fam.exists_orderOf_four (F : Q8Fam Y Δ) {L : Subgroup Y} (hL : L ∈ Δ) :
    ∃ x ∈ L, orderOf x = 4 := by
  obtain ⟨x, hxL, hxx⟩ := F.exists_mul_self_ne_one L hL
  refine ⟨x, hxL, ?_⟩
  have := orderOf_eq_prime_pow (x := x) (p := 2) (n := 1) (by rw [pow_one, pow_two]; exact hxx)
    (by rw [show 2 ^ (1 + 1) = 4 by norm_num]; exact F.pow_four L hL x hxL)
  simpa using this

theorem fam_twin_adj (F : Q8Fam Y Δ) {L M : Subgroup Y} (hL : L ∈ Δ) (hM : M ∈ Δ) (hne : M ≠ L)
    {u : Y} (hLu : IsUniqueInvolution L u) (hMu : IsUniqueInvolution M u) :
    M ∈ omegaStarNbr Δ L := by
  obtain ⟨x, hxM, hx4⟩ := Q8Fam.exists_orderOf_four F hM
  exact fam_mem_omegaStarNbr_of_elt F hM hne hxM hx4
    (Sec6Gen.le_normalizer_of_twin F.hyp hM hL hne hMu hLu hxM)

theorem fam_mem_of_e8 (F : Q8Fam Y Δ) {E : Subgroup Y} (hE : E8Struct ⊤ E) {K : Subgroup Y}
    (hK : K ∈ Δ) {t : Y} (ht : IsUniqueInvolution K t) : t ∈ E := by
  obtain ⟨P, hPn, hP2, htP⟩ := F.inO2 K hK t ht
  exact hE.core P le_top (fun x _ q hq => hPn.conj_mem q hq x) hP2 htP

theorem fam_exists_omegaStar_e8 (F : Q8Fam Y Δ) {E : Subgroup Y} (hE : E8Struct ⊤ E)
    {K : Subgroup Y} (hK : K ∈ Δ) {t : Y} (hut : IsUniqueInvolution K t) :
    ∃ y : Y, y * t * y⁻¹ ≠ t ∧ K ∈ omegaStarNbr Δ (conjSub y K) := by
  have htE : t ∈ E := fam_mem_of_e8 F hE hK hut
  obtain ⟨e, he⟩ := exists_e8Basis hE.sq hE.card
  have htE' : e8Coord e (e8Inv he t) = t := e8Coord_e8Inv he htE
  obtain ⟨q⟩ := F.q8 K hK
  set j : Y := ((q.symm (QuaternionGroup.a 1) : K) : Y) with hjdef
  have hjK : j ∈ K := (q.symm (QuaternionGroup.a 1)).2
  have hj4 : orderOf j = 4 := by
    rw [hjdef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one]
  have hjj : j * j = t := by
    have hsq : j * j * (j * j) = 1 :=
      calc j * j * (j * j) = j ^ 4 := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
        _ = 1 := hj4 ▸ pow_orderOf_eq_one j
    have hne : j * j ≠ 1 := fun h => by
      have := orderOf_dvd_of_pow_eq_one (show j ^ 2 = 1 by rw [pow_two, h])
      rw [hj4] at this
      exact absurd this (by norm_num)
    exact (hut.unique _ (mul_mem hjK hjK) hsq).resolve_left hne
  have hAA : e8Hom hE he ⟨j, Subgroup.mem_top j⟩ * e8Hom hE he ⟨j, Subgroup.mem_top j⟩ = 1 := by
    rw [← map_mul, e8Hom_eq_one_iff]
    show j * j ∈ E
    rw [hjj]
    exact htE
  obtain ⟨v, hv0, hvt, hAv⟩ := exists_fixed_ne _ hAA (e8Inv he t)
  set a := e8Coord e v with hadef
  have hja : j * a * j⁻¹ = a := by
    have h1 := conj_e8Coord_e8Hom hE he ⟨j, Subgroup.mem_top j⟩ v
    rw [hAv] at h1
    exact h1
  have hat : a ≠ t := fun h => hvt (e8Coord_injective he (h.trans htE'.symm))
  have hw0 : e8Inv he t ≠ 0 := fun h => hut.ne_one (by rw [← htE', h, e8Coord_zero])
  obtain ⟨M, hM⟩ := sl3Two_transitive v (e8Inv he t) hv0 hw0
  obtain ⟨y, hy⟩ := e8Hom_surjective hE he M
  have hyt : (y : Y) * t * (y : Y)⁻¹ = a := by
    rw [← htE', conj_e8Coord_e8Hom hE he y, hy, hM]
  have hKy : conjSub (y : Y) K ∈ Δ := F.hyp.conjInvariant y K hK
  have hune : IsUniqueInvolution (conjSub (y : Y) K) a := hyt ▸ hut.conj (y : Y)
  have hne : conjSub (y : Y) K ≠ K := fun h => by
    rw [h] at hune
    exact hat (hut.eq hune).symm
  have hja' : j * a = a * j :=
    calc j * a = j * a * j⁻¹ * j := by group
      _ = a * j := by rw [hja]
  have hnc : ¬ ∀ w ∈ K, j * w = w * j := by
    intro hall
    have h1 := hall ((q.symm (QuaternionGroup.xa 0) : K) : Y) (q.symm (QuaternionGroup.xa 0)).2
    have h2 : q.symm (QuaternionGroup.a 1) * q.symm (QuaternionGroup.xa 0) =
        q.symm (QuaternionGroup.xa 0) * q.symm (QuaternionGroup.a 1) := Subtype.ext h1
    have h3 := congrArg q h2
    rw [map_mul, map_mul] at h3
    simp only [MulEquiv.apply_symm_apply] at h3
    exact absurd h3 (by decide)
  have hjN : j ∈ Subgroup.normalizer ((conjSub (y : Y) K : Subgroup Y) : Set Y) :=
    F.hyp.omega5 (conjSub (y : Y) K) hKy K hK hne a hune j hjK hnc
      ((F.two K hK).to_le (Subgroup.zpowers_le.mpr hjK)) hja'
  exact ⟨y, fun h => hat (hyt.symm.trans h), fam_mem_omegaStarNbr_of_elt F hK hne.symm hjK hj4 hjN⟩

theorem dstarAdj_of_omegaStarNbr {A B : Subgroup Y} (hA : A ∈ Δ) (hB : B ∈ Δ)
    (h : B ∈ omegaStarNbr Δ A) :
    Relation.ReflTransGen (dstarAdj Δ) A B ∧ Relation.ReflTransGen (dstarAdj Δ) B A :=
  ⟨Relation.ReflTransGen.single ⟨hB, Or.inl h⟩, Relation.ReflTransGen.single ⟨hA, Or.inr h⟩⟩

theorem fam_twin_path (F : Q8Fam Y Δ) {A B : Subgroup Y} (hA : A ∈ Δ) (hB : B ∈ Δ) {u : Y}
    (hAu : IsUniqueInvolution A u) (hBu : IsUniqueInvolution B u) :
    Relation.ReflTransGen (dstarAdj Δ) A B := by
  by_cases h : B = A
  · rw [h]
  · exact Relation.ReflTransGen.single ⟨hB, Or.inl (fam_twin_adj F hA hB h hAu hBu)⟩

theorem fam_dstarConnected_of_e8 (F : Q8Fam Y Δ) {E : Subgroup Y} (hE : E8Struct ⊤ E) :
    T3.DStarConnected Δ := by
  intro K hK
  obtain ⟨t, hut⟩ := (F.hyp.omega1 K hK).1
  have htE : t ∈ E := fam_mem_of_e8 F hE hK hut
  have hconjE : ∀ g : Y, g * t * g⁻¹ ∈ E := fun g => hE.normal g (Subgroup.mem_top g) t htE
  have hne1 : ∀ g : Y, g * t * g⁻¹ ≠ 1 := fun g h => hut.ne_one (by
    have := congrArg (fun x => g⁻¹ * x * g) h
    simpa [mul_assoc] using this)
  obtain ⟨y, hyt, hedge⟩ := fam_exists_omegaStar_e8 F hE hK hut
  obtain ⟨e, he, he0⟩ := exists_e8Basis_of_mem hE.sq hE.card htE hut.ne_one
  have hte : e8Coord e (Pi.single 0 1) = t := by rw [e8Coord_single, he0]
  have hcoord : ∀ x ∈ E, x ≠ 1 → x ≠ t →
      e8Inv he x ≠ 0 ∧ e8Inv he x ≠ Pi.single 0 1 := fun x hx hx1 hxt =>
    ⟨fun h => hx1 (by rw [← e8Coord_e8Inv he hx, h, e8Coord_zero]),
      fun h => hxt (by rw [← e8Coord_e8Inv he hx, h, hte])⟩
  have hmem : ∀ g : Y, conjSub g K ∈ Δ := fun g => F.hyp.conjInvariant g K hK
  intro L hL
  obtain ⟨g, rfl⟩ := F.trans K hK L hL
  by_cases hgt : g * t * g⁻¹ = t
  · exact fam_twin_path F hK hL hut (hgt ▸ hut.conj g)
  · obtain ⟨hw0, hw1⟩ := hcoord _ (hconjE y) (hne1 y) hyt
    obtain ⟨hw0', hw1'⟩ := hcoord _ (hconjE g) (hne1 g) hgt
    obtain ⟨M, hM0, hM⟩ := sl3Two_stab_transitive _ _ hw0 hw1 hw0' hw1'
    obtain ⟨h, hh⟩ := e8Hom_surjective hE he M
    have hht : (h : Y) * t * (h : Y)⁻¹ = t := by
      rw [← hte, conj_e8Coord_e8Hom hE he h, hh, hM0]
    have hhc : (h : Y) * (y * t * y⁻¹) * (h : Y)⁻¹ = g * t * g⁻¹ := by
      rw [← e8Coord_e8Inv he (hconjE y), conj_e8Coord_e8Hom hE he h, hh, hM,
        e8Coord_e8Inv he (hconjE g)]
    have h1 := omegaStarNbr_conj F.hyp.conjInvariant hedge (h : Y)
    rw [← conjSub_mul] at h1
    have hs1 : Relation.ReflTransGen (dstarAdj Δ) K (conjSub (h : Y) K) :=
      fam_twin_path F hK (hmem _) hut (hht ▸ hut.conj (h : Y))
    have hs2 : Relation.ReflTransGen (dstarAdj Δ) (conjSub (h : Y) K) (conjSub ((h : Y) * y) K) :=
      (dstarAdj_of_omegaStarNbr (hmem _) (hmem _) h1).2
    have hinv : IsUniqueInvolution (conjSub ((h : Y) * y) K) (g * t * g⁻¹) := by
      have := hut.conj ((h : Y) * y)
      rwa [show (h : Y) * y * t * ((h : Y) * y)⁻¹ = g * t * g⁻¹ by
        rw [← hhc]; group] at this
    have hs3 : Relation.ReflTransGen (dstarAdj Δ) (conjSub ((h : Y) * y) K) (conjSub g K) :=
      fam_twin_path F (hmem _) (hmem _) hinv (hut.conj g)
    exact (hs1.trans hs2).trans hs3

end ExitO2

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
