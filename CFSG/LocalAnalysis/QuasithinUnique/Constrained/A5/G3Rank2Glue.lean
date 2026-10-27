module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3LatSix
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem not_isDelta5_bot {G : Type} [Group G] [Finite G] : ¬ IsDelta5Group ↥(⊥ : Subgroup G) := by
  intro h
  have := h.card
  rw [Subgroup.card_bot] at this
  omega

theorem perfectCore_parabolic_cases {S : Type} [Group S] [Finite S] {U : Subgroup S}
    (hU : IsSylowTwoOf U ⊤) {P : Fin 2 → Subgroup S} (hP : ResidualOvergroupsAt S U P)
    {Pa : Subgroup S} (hpar : IsParabolic2 (⊤ : Subgroup S) Pa) (hne : Pa ≠ ⊤) :
    perfectCore Pa = ⊥ ∨ ∃ j, Nonempty (↥(perfectCore Pa) ≃* ↥(perfectCore (P j))) := by
  obtain ⟨-, S₁, hS₁, hN⟩ := hpar
  obtain ⟨g, hg⟩ := exists_conj_eq_of_isSylowTwoOf hU hS₁
  set c : S ≃* S := (MulAut.conj g).symm with hc
  set Pa' : Subgroup S := Pa.map c.toMonoidHom with hPa'
  have hS₁P : S₁ ≤ Pa := fun x hx => hN ⟨Subgroup.mem_top x, Subgroup.le_normalizer hx⟩
  have hUP : U ≤ Pa' := by
    intro u hu
    have hmem : (MulAut.conj g).toMonoidHom u ∈ S₁ := by
      rw [← hg]
      exact ⟨u, hu, rfl⟩
    refine ⟨(MulAut.conj g).toMonoidHom u, hS₁P hmem, ?_⟩
    simp [hc]
    group
  have hne' : Pa' ≠ ⊤ := by
    intro htop
    apply hne
    have := congrArg (Subgroup.map c.symm.toMonoidHom) htop
    rw [hPa', Subgroup.map_map] at this
    have h' : c.symm.toMonoidHom.comp c.toMonoidHom = MonoidHom.id S := by
      ext x
      simp
    rw [h', Subgroup.map_id, Subgroup.map_top_of_surjective _ c.symm.surjective] at this
    exact this
  have hcore : (perfectCore Pa).map c.toMonoidHom = perfectCore Pa' :=
    map_perfectCore c.toMonoidHom Pa
  by_cases hs : Group.IsSolvable ↥Pa'
  · left
    have h1 : perfectCore Pa' = ⊥ := (isSolvable_iff_perfectCore_eq_bot Pa').mp hs
    rw [← hcore] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ c.injective).mp h1
  · right
    obtain ⟨j, -, hd⟩ := hP.2.2.2.2.1 Pa' hUP hne' hs
    have hj : perfectCore Pa' = perfectCore (P j) := by
      rw [← CFSG.QuasithinUnique.Vol2Native.A312L.dInf_eq_perfectCore,
        ← CFSG.QuasithinUnique.Vol2Native.A312L.dInf_eq_perfectCore, hd]
    refine ⟨j, ⟨?_⟩⟩
    exact ((perfectCore Pa).equivMapOfInjective c.toMonoidHom c.injective).trans
      (MulEquiv.subgroupCongr (hcore.trans hj))

theorem not_isDelta5_perfectCore_parabolic {S : Type} [Group S] [Finite S] {U : Subgroup S}
    (hU : IsSylowTwoOf U ⊤) {P : Fin 2 → Subgroup S} (hP : ResidualOvergroupsAt S U P)
    (hPj : ∀ j, ¬ IsDelta5Group ↥(perfectCore (P j))) {Pa : Subgroup S}
    (hpar : IsParabolic2 (⊤ : Subgroup S) Pa) (hne : Pa ≠ ⊤) :
    ¬ IsDelta5Group ↥(perfectCore Pa) := by
  intro hD
  rcases perfectCore_parabolic_cases hU hP hpar hne with h | ⟨j, ⟨e⟩⟩
  · rw [h] at hD
    exact not_isDelta5_bot hD
  · exact hPj j (hD.of_equiv e)

theorem not_isDelta5_perfectCore_of_equiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) {Pa : Subgroup X}
    (h : ¬ IsDelta5Group ↥(perfectCore (Pa.map e.toMonoidHom))) :
    ¬ IsDelta5Group ↥(perfectCore Pa) := fun hD =>
  h (hD.of_equiv (((perfectCore Pa).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_perfectCore e.toMonoidHom Pa))))

theorem not_isDelta5_perfectCore_of_subgroupOf {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    (hP : IsParabolic2 L P) (hne : P ≠ L)
    (h : ∀ Pa : Subgroup ↥L, IsParabolic2 (⊤ : Subgroup ↥L) Pa → Pa ≠ ⊤ →
      ¬ IsDelta5Group ↥(perfectCore Pa)) : ¬ IsDelta5Group ↥(perfectCore P) := by
  have hPL : P ≤ L := hP.1
  have hmap : (P.subgroupOf L).map L.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPL
  have hpar : IsParabolic2 (⊤ : Subgroup ↥L) (P.subgroupOf L) := by
    rw [A312.isParabolic2_top_iff, hmap]
    exact hP
  have hne' : P.subgroupOf L ≠ ⊤ := by
    intro htop
    apply hne
    have := congrArg (Subgroup.map L.subtype) htop
    rw [hmap, Subgroup.map_top, Subgroup.range_subtype] at this
    exact this
  intro hD
  refine h _ hpar hne' ?_
  have hcore : (perfectCore (P.subgroupOf L)).map L.subtype = perfectCore P := by
    rw [map_perfectCore, hmap]
  exact hD.of_equiv (((perfectCore (P.subgroupOf L)).equivMapOfInjective L.subtype
    L.subtype_injective).trans (MulEquiv.subgroupCongr hcore)).symm

theorem map_ne_top_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {Pa : Subgroup X}
    (h : Pa ≠ ⊤) : Pa.map e.toMonoidHom ≠ ⊤ := by
  intro htop
  apply h
  have := congrArg (Subgroup.map e.symm.toMonoidHom) htop
  rw [Subgroup.map_map] at this
  have h' : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X := by
    ext x
    simp
  rw [h', Subgroup.map_id, Subgroup.map_top_of_surjective _ e.symm.surjective] at this
  exact this

theorem not_isDelta5_perfectCore_subgroupOf_of {G : Type} [Group G] [Finite G] {C P : Subgroup G}
    (hPC : P ≤ C) (h : ¬ IsDelta5Group ↥(perfectCore P)) :
    ¬ IsDelta5Group ↥(perfectCore (P.subgroupOf C)) := fun hD => by
  have hcore : (perfectCore (P.subgroupOf C)).map C.subtype = perfectCore P := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hPC]
  exact h (hD.of_equiv (((perfectCore (P.subgroupOf C)).equivMapOfInjective C.subtype
    C.subtype_injective).trans (MulEquiv.subgroupCongr hcore)))

end CFSG.QuasithinUnique.A5.G3
