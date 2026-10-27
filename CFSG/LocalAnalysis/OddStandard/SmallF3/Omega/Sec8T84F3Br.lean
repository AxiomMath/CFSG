module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F3Yd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F3Tr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F3Sub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F3Fin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F5Lft
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private lemma sec8t84_card_subgroupOf {G : Type} [Group G] {Y O : Subgroup G} (h : O ≤ Y) :
    Nat.card (O.subgroupOf Y) = Nat.card O :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

private lemma sec8t84_isElemAb2_subgroupOf {G : Type} [Group G] {Y V : Subgroup G}
    (h : IsElemAb2 V 4) (hV : V ≤ Y) : IsElemAb2 (V.subgroupOf Y) 4 :=
  ⟨h.1.subgroupOf Y, by rw [sec8t84_card_subgroupOf hV, h.2]⟩

private lemma sec8t84_comm_subgroupOf {G : Type} [Group G] {Y O V : Subgroup G}
    (h : ∀ v ∈ V, ∀ o ∈ O, v * o = o * v) :
    ∀ v ∈ V.subgroupOf Y, ∀ o ∈ O.subgroupOf Y, v * o = o * v :=
  fun v hv o ho => Subtype.ext (h v hv o ho)

private lemma sec8t84_isSylow2Of_subgroupOf {G : Type} [Group G] {Y P : Subgroup G}
    (hPY : IsSylow2Of P Y) : IsSylow2Of (P.subgroupOf Y) ⊤ := by
  refine ⟨le_top, hPY.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPY.1).symm, ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact hPY.2.2

private lemma sec8t84_subgroupOf_sup {G : Type} [Group G] {Y V O : Subgroup G}
    (hV : V ≤ Y) (hO : O ≤ Y) :
    (V ⊔ O).subgroupOf Y = V.subgroupOf Y ⊔ O.subgroupOf Y :=
  Subgroup.subgroupOf_sup hV hO

private theorem sec8t84_factP_quot_subgroupOf (hP : Sec8T84FactP) {G : Type} [Group G]
    [Finite G] {Y O V H : Subgroup G} (hY : Sec8T84YData G Y O V H)
    [hN : (O.subgroupOf Y).Normal] {P' : Subgroup ↥Y} (hP' : IsSylow2Of P' ⊤) :
    ∃ Fb : Subgroup (↥Y ⧸ O.subgroupOf Y),
      Sec8T84PFacts (↥Y ⧸ O.subgroupOf Y)
        ((V.subgroupOf Y).map (QuotientGroup.mk' (O.subgroupOf Y)))
        (P'.map (QuotientGroup.mk' (O.subgroupOf Y))) Fb := by
  haveI : (V.subgroupOf Y).Normal := hY.V_norm
  have hNodd : Odd (Nat.card (O.subgroupOf Y)) := by
    rw [sec8t84_card_subgroupOf hY.O_le]; exact hY.O_odd
  have hV : IsElemAb2 (V.subgroupOf Y) 4 :=
    sec8t84_isElemAb2_subgroupOf hY.V_e16 hY.V_le
  have hA6 : ∃ φ : ↥Y →* alternatingGroup (Fin 6), Function.Surjective φ ∧
      φ.ker = V.subgroupOf Y ⊔ O.subgroupOf Y := by
    obtain ⟨φ, hφ, hker⟩ := hY.quot
    exact ⟨φ, hφ, by rw [hker, sec8t84_subgroupOf_sup hY.V_le hY.O_le]⟩
  have hHN : H.subgroupOf Y ⊓ (V.subgroupOf Y ⊔ O.subgroupOf Y) ≤ O.subgroupOf Y := by
    intro x hx
    have hxH : (x : G) ∈ H := hx.1
    have hxVO : (x : G) ∈ V ⊔ O := by
      rw [← sec8t84_subgroupOf_sup hY.V_le hY.O_le] at hx
      exact hx.2
    exact hY.H_inf (Subgroup.mem_inf.mpr ⟨hxH, hxVO⟩)
  have hHsup : H.subgroupOf Y ⊔ (V.subgroupOf Y ⊔ O.subgroupOf Y) = ⊤ := by
    have h1 : (H ⊔ (V ⊔ O)).subgroupOf Y = ⊤ := by
      rw [hY.H_sup, Subgroup.subgroupOf_self]
    rw [Subgroup.subgroupOf_sup hY.H_le (sup_le hY.V_le hY.O_le),
      Subgroup.subgroupOf_sup hY.V_le hY.O_le] at h1
    exact h1
  have htrans : ∀ v ∈ V.subgroupOf Y, v ≠ 1 → ∀ w ∈ V.subgroupOf Y, w ≠ 1 →
      ∃ y : ↥Y, y * v * y⁻¹ = w := by
    intro v hv hv1 w hw hw1
    obtain ⟨y, hy, hconj⟩ := hY.trans (v : G) hv (fun h => hv1 (Subtype.ext h))
      (w : G) hw (fun h => hw1 (Subtype.ext h))
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hconj)⟩
  exact sec8t84_factP_quot hP (A := ↥Y) (N := O.subgroupOf Y) (V := V.subgroupOf Y)
    (H := H.subgroupOf Y) (P := P') hNodd hV (sec8t84_comm_subgroupOf hY.V_O)
    hA6 hHN hHsup htrans hP'

theorem sec8t84_pmod_of (hP : Sec8T84FactP) {G : Type} [Group G] [Finite G]
    {Y O V H P : Subgroup G} (hY : Sec8T84YData G Y O V H) (hPY : IsSylow2Of P Y)
    (hVP : V ≤ P) (hVPn : (V.subgroupOf P).Normal) :
    ∃ F : Subgroup G, Sec8T84PMod G V P F := by
  haveI : (O.subgroupOf Y).Normal := hY.O_norm
  haveI : (V.subgroupOf Y).Normal := hY.V_norm
  have hP' : IsSylow2Of (P.subgroupOf Y) ⊤ := sec8t84_isSylow2Of_subgroupOf hPY
  obtain ⟨Fb, hFb⟩ := sec8t84_factP_quot_subgroupOf hP hY hP'
  obtain ⟨hdisj, -⟩ := sec8t84_sylow_map_quot (O.subgroupOf Y) (P.subgroupOf Y)
    (by rw [sec8t84_card_subgroupOf hY.O_le]; exact hY.O_odd) hP'
  have hinj : P.subgroupOf Y ⊓ (QuotientGroup.mk' (O.subgroupOf Y)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk']; exact hdisj
  have hV'P' : V.subgroupOf Y ≤ P.subgroupOf Y := fun _ hv => hVP hv
  have hV'n : ((V.subgroupOf Y).subgroupOf (P.subgroupOf Y)).Normal := by
    have heq : (V.subgroupOf Y).subgroupOf (P.subgroupOf Y) =
        (V.subgroupOf P).comap (Subgroup.subgroupOfEquivOfLe hPY.1).toMonoidHom := by
      ext x
      exact Iff.rfl
    rw [heq]
    exact hVPn.comap _
  have hpmod : Sec8T84PMod ↥Y (V.subgroupOf Y) (P.subgroupOf Y)
      (Fb.comap (QuotientGroup.mk' (O.subgroupOf Y)) ⊓ P.subgroupOf Y) :=
    sec8t84_pmod_of_hom (A := ↥Y) (B := ↥Y ⧸ O.subgroupOf Y)
      (QuotientGroup.mk' (O.subgroupOf Y)) hV'P' hinj
      (sec8t84_isElemAb2_subgroupOf hY.V_e16 hY.V_le) hV'n hFb
  refine ⟨(Fb.comap (QuotientGroup.mk' (O.subgroupOf Y)) ⊓ P.subgroupOf Y).map
    Y.subtype, ?_⟩
  have h := sec8t84_pmod_subtype (Y := Y) hpmod
  rw [Subgroup.map_subgroupOf_eq_of_le hY.V_le,
    Subgroup.map_subgroupOf_eq_of_le hPY.1] at h
  exact h

theorem sec8t84_rank_piece (hP : Sec8T84FactP) {G : Type} [Group G] [Finite G]
    {Y O V H : Subgroup G} (hY : Sec8T84YData G Y O V H) {s : G} (hsY : s ∈ Y)
    (hs : s * s = 1) :
    ∃ D : Subgroup G, O ≤ D ∧ D ≤ Y ∧ s ∈ D ∧ (∀ x ∈ D, x * x ∈ O) ∧
      (∀ x ∈ D, ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ O) ∧ Nat.card D = 16 * Nat.card O := by
  haveI : (O.subgroupOf Y).Normal := hY.O_norm
  haveI : (V.subgroupOf Y).Normal := hY.V_norm
  obtain ⟨P', hP'⟩ := exists_isSylow2Of (⊤ : Subgroup ↥Y)
  obtain ⟨Fb, hFb⟩ := sec8t84_factP_quot_subgroupOf hP hY hP'
  have hrk : ∀ t : ↥Y ⧸ O.subgroupOf Y, orderOf t = 2 →
      CFSG.Open.pRank 2 (centralizer ({t} : Set (↥Y ⧸ O.subgroupOf Y))) = 4 :=
    fun t ht => hFb.rank_cent t ht
  have hs' : (⟨s, hsY⟩ : ↥Y) * ⟨s, hsY⟩ = 1 := Subtype.ext (by simpa using hs)
  obtain ⟨D', hND', hsD', hsq, hcomm, hcard⟩ :=
    sec8t84_rank_lift (O.subgroupOf Y) (V.subgroupOf Y)
      (by rw [sec8t84_card_subgroupOf hY.O_le]; exact hY.O_odd)
      (sec8t84_isElemAb2_subgroupOf hY.V_e16 hY.V_le) (sec8t84_comm_subgroupOf hY.V_O)
      hrk ⟨s, hsY⟩ hs'
  refine ⟨D'.map Y.subtype, ?_, Subgroup.map_subtype_le D', ?_, ?_, ?_, ?_⟩
  · intro o ho
    exact Subgroup.mem_map_of_mem Y.subtype (hND' (x := ⟨o, hY.O_le ho⟩) ho)
  · exact Subgroup.mem_map_of_mem Y.subtype hsD'
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact hsq y hy
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    exact hcomm a ha b hb
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective Y), hcard,
      sec8t84_card_subgroupOf hY.O_le]

end CFSG.OddStandard.SmallF3.Omega
