module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigX5
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigX8
public import CFSG.ClassicalInvolution.Q3.TL4LinkB2b4R

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2SetR.false_of_type22 (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u) {y : Y}
    (hyA : y ∈ edgeCent (P : Subgroup Y) t u) {L : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) (hyL : IsUniqueInvolution L y)
    (hyt : y ≠ t) (hyu : y ≠ u) {Vt Vu : Subgroup Y}
    (hVt : IsSylow2In Vt (L ⊓ Subgroup.centralizer ({t} : Set Y))) (h2t : Vt = Subgroup.zpowers y)
    (hVu : IsSylow2In Vu (L ⊓ Subgroup.centralizer ({u} : Set Y))) (h2u : Vu = Subgroup.zpowers y) :
    False := by
  obtain ⟨Ry, hRy, -, hEN⟩ := hs.exists_sylow_E_invariant hyA hL hyL (W := ⊥) bot_le bot_le bot_le
  obtain ⟨e⟩ := (TightLargeHypR.typeRFam hs.large).quat L hL Ry hRy
  have htE : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have huE : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have houter : ∀ {z : Y} {V : Subgroup Y},
      IsSylow2In V (L ⊓ Subgroup.centralizer ({z} : Set Y)) → V = Subgroup.zpowers y →
        LinkDisc.B2b.Outer Ry z := by
    intro z V hV hVy w hw hwz
    have hw2 : IsPGroup 2 ↥(Subgroup.zpowers w) :=
      hRy.2.1.to_le (Subgroup.zpowers_le.mpr hw)
    obtain ⟨V', hV', hwV'⟩ := IsSylow2In.exists_ge hw2
      (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr
        ⟨hRy.1 hw, Subgroup.mem_centralizer_singleton_iff.mpr hwz⟩))
    obtain ⟨x, -, hxV⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hV hV'
    have hcard : Nat.card ↥V' = 2 := by
      rw [← hxV, natCard_conjSub', hVy, Nat.card_zpowers,
        orderOf_eq_prime (by rw [sq]; exact hyL.sq) hyL.ne_one]
    have h1 : orderOf w ∣ 2 := by
      rw [← hcard, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le hwV'
    rw [← sq]
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hnot := (LinkDisc.B2b.quatAutFacts_of_four_le hr).not_outer_triple e (hEN t htE)
    (hEN u huE) hs.tu_comm hs.t2 hs.u2
  have htu : ¬ LinkDisc.B2b.Outer Ry (t * u) := fun h =>
    hnot ⟨houter hVt h2t, houter hVu h2u, h⟩
  simp only [LinkDisc.B2b.Outer, not_forall] at htu
  obtain ⟨w, hw, hwa, hww⟩ := htu
  have hw2 : IsPGroup 2 ↥(Subgroup.zpowers w) := hRy.2.1.to_le (Subgroup.zpowers_le.mpr hw)
  have hw4 : 2 < Nat.card ↥(Subgroup.zpowers w) := by
    rw [Nat.card_zpowers]
    by_contra hle
    push Not at hle
    have hpos := orderOf_pos w
    interval_cases h : orderOf w
    · exact hww (by rw [orderOf_eq_one_iff.mp h, one_mul])
    · exact hww (by rw [← sq, ← h, pow_orderOf_eq_one])
  have hyE := hs.mem_E_of_two_lt_card hr h1 hL hyL hyA.1.1 hw2
    (Subgroup.zpowers_le.mpr (hRy.1 hw))
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hwa)) hw4
  rcases mem_closure_pair_cases hs.t2 hs.u2 hs.tu_comm hyE with h | h | h | h
  · exact hyL.ne_one h
  · exact hyt h
  · exact hyu h
  · exact hs.ne_tu_of_mem_cls hL hyL h

theorem z2BigXPlusT_holds (r n : ℕ) :
    4 ≤ r → ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
      (J : Subgroup Y) (u : Y) (R₀ T₀ : Subgroup Y) (P : Sylow 2 Y),
      Z2SetR r n R S t J u R₀ T₀ P → C264One (CoreAssembly.conjClass (tightCore R)) t u →
        ∀ y ∈ edgeCent (P : Subgroup Y) t u, y * y = 1 →
          (¬ InnerModOdd (linkLayer R t) y ∨
            ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) y) →
          ∀ g : Y, g * y * g⁻¹ ≠ t := by
  intro hr Y _ _ R S t J u R₀ T₀ P hs h1 y hyA hy2 hout g hg
  have hyg : y = g⁻¹ * t * g := by rw [← hg]; group
  have hL : conjSub g⁻¹ (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨g⁻¹, rfl⟩
  have hyL : IsUniqueInvolution (conjSub g⁻¹ (tightCore R)) y := by
    have h2 := hs.large.datum.isUniqueInvolution_core.conj g⁻¹
    rwa [inv_inv, ← hyg] at h2
  have hyt_c : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hyA.1.2
  have hyu_c : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hyA.2
  have hne_t : y ≠ t := by
    intro he
    rcases hout with h | h
    · exact h (by rw [he]; exact hs.innerModOdd_t_t)
    · exact h (by rw [he]; exact hs.innerModOdd_u_t)
  have hne_u : y ≠ u := by
    intro he
    rcases hout with h | h
    · exact h (by rw [he]; exact hs.innerModOdd_t_u)
    · exact h (by rw [he]; exact hs.innerModOdd_u_u)
  obtain ⟨Vt, Vu, hVt, hyVt, hVu, hyVu, ht', hu'⟩ := hs.pair_types hyA hL hyL hne_t hne_u
  rcases ht' with h2t | h3t | ⟨h4tL, h4tc⟩
  · rcases hu' with h2u | h3u | ⟨h4uL, h4uc⟩
    · exact hs.false_of_type22 hr h1 hyA hL hyL hne_t hne_u hVt h2t hVu h2u
    · exact z2BigNoType3U_holds r n hr Y R S t J u R₀ T₀ P hs h1 _ hL y hyL hne_u hyu_c Vu hVu
        hyVu h3u
    · exact hout.elim (fun h => h (hs.innerModOdd_t_of_type4 hr hyA hy2 hyVu h4uc))
        (fun h => h (hs.innerModOdd_u_of_mem_omegaNbr hyA h4uL hyL))
  · exact z2BigNoType3_holds r n hr Y R S t J u R₀ T₀ P hs h1 _ hL y hyL hne_t hyt_c Vt hVt hyVt
      h3t
  · exact hout.elim (fun h => h (hs.innerModOdd_t_of_mem_omegaNbr hyA h4tL hyL))
      (fun h => h (hs.innerModOdd_u_of_type4 hr hyA hy2 hyVt h4tc))

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
