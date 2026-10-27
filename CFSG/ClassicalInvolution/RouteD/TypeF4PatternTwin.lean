module

public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternMain
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Pair

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {z : G}

namespace Frame

theorem exists_twinPair (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z) {i j : Fin (m + 1)}
    (hij : i ≠ j) :
    ∃ (M : Subgroup G) (w : G), M ∈ Ω ∧ IsClassicalMember p f M w ∧ M ≠ K ∧ Commutes K M ∧
      conjSub (Fr.gf i) M = Fr.Kf j ∧ Fr.zf i * Fr.zf j = Fr.gf i * (z * w) * (Fr.gf i)⁻¹ := by
  refine ⟨conjSub (Fr.gf i)⁻¹ (Fr.Kf j), (Fr.gf i)⁻¹ * Fr.zf j * Fr.gf i,
    S.conjInvariant _ _ (Fr.mem j), ?_, ?_, ?_, conjSub_conjSub_inv _ _, ?_⟩
  · have := (Fr.cls S j).conj (Fr.gf i)⁻¹
    rwa [inv_inv] at this
  · intro h
    apply Fr.ne_of_ne S hij
    have h' := congrArg (conjSub (Fr.gf i)) h
    rw [conjSub_conjSub_inv] at h'
    rw [Fr.eq_conj i]
    exact h'.symm
  · have := (Fr.commute i j hij).conjSub (Fr.gf i)⁻¹
    rwa [Fr.eq_conj i, conjSub_inv_conjSub] at this
  · have hzi : Fr.zf i = Fr.gf i * z * (Fr.gf i)⁻¹ := rfl
    rw [hzi]
    group

end Frame

namespace NonClassical

section Exotic

open scoped commutatorElement

variable [Finite G]

theorem eq_one_of_mem_planeGroup_of_mem_center {F : Type} [Field F]
    {P : Submodule F (Fin 3 ⊕ Fin 3 → F)} (hP : Models.SymplecticPairs.IsHyperbolicPlane P)
    {a : StatedSp 3 F} (haP : a ∈ Models.SymplecticPairs.planeGroup P)
    (ha : a ∈ Subgroup.center (StatedSp 3 F)) : a = 1 := by
  obtain ⟨g, hg⟩ := Models.SymplecticPairs.exists_planeGroup_eq_conj_longBlock hP (0 : Fin 3)
  rw [hg] at haP
  obtain ⟨b, ⟨A, rfl⟩, rfl⟩ := haP
  have hb : Models.SymplecticPairs.longBlock F 3 0 A ∈ Subgroup.center (StatedSp 3 F) :=
    Models.SymplecticPairs.mem_center_of_conj_mem_center (g := g) ha
  have h1 : Models.SymplecticPairs.longBlock F 3 0 A = 1 :=
    Models.SymplecticPairs.eq_one_of_mem_center_of_mem_suppGroup hb
      (Models.SymplecticPairs.isSupp_longBlock _ A) (t := Sum.inl (1 : Fin 3)) (by
        rintro (h | h)
        · have := Sum.inl_injective h
          simp at this
        · exact Sum.inl_ne_inr h)
  simp [h1]

theorem not_mem_of_commutes_ne (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hK : K ∈ Ω) (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z})
    (d : ShapeCDict p f 3 Ω z) {M : Subgroup G} (hM : M ∈ Ω) (hMK : M ≠ K)
    (hKM : Commutes K M) : z ∉ M := by
  intro hzM
  have h4 : 4 ≤ Nat.card (GaloisField p f) := four_le_natCard_galoisField hq
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hMz : M ∈ centralizingMembers Ω {z} :=
    ⟨hM, le_centralizer_of_commutes (Commutes.symm hKM) hz.mem⟩
  obtain ⟨P, hP, hMP⟩ := typeC_exists_plane_of_ne (by norm_num) hq hΩ hex hK hz hP1 d hMz hMK
  have hzY : z ∈ locLayer Ω z := le_centralizingLayer hKz hz.mem
  have hzbM : locElt Ω z z hzY ∈ locImg Ω z M := locElt_mem_locImg (le_centralizingLayer hMz) hzM
  have hzbK : locElt Ω z z hzY ∈ d.Q₀ :=
    typeC_locImg_self_le_Q₀ (by norm_num) hq hK hz d (locElt_mem_locImg
      (le_centralizingLayer hKz) hz.mem)
  rw [hMP] at hzbM
  obtain ⟨a, haP, haz⟩ := hzbM
  have hcomm : ∀ g : StatedSp 3 (GaloisField p f), ⁅a, g⁆ ∈ Subgroup.center (StatedSp 3 _) := by
    intro g
    apply d.ker_le
    rw [MonoidHom.mem_ker, map_commutatorElement, haz, commutatorElement_eq_one_iff_mul_comm]
    exact d.commutes _ hzbK _ ⟨g, rfl⟩
  have ha : a ∈ Subgroup.center (StatedSp 3 (GaloisField p f)) :=
    Models.SymplecticPairs.mem_center_of_forall_commutator_mem_center
      (Models.SymplecticPairs.isPerfect_statedSp_of_four_le h4) hcomm
  have ha1 : a = 1 := eq_one_of_mem_planeGroup_of_mem_center hP haP ha
  have hord : orderOf (locElt Ω z z hzY) = 2 := orderOf_locElt hzY hz.orderOf_eq_two
  rw [← haz, ha1, map_one, orderOf_one] at hord
  omega

theorem twinProductNoExotic_of_sharedInvolution (hSI : G2D4.G2D4SharedInvolution p) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hK : K ∈ Ω)
    (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z}) (d : ShapeCDict p f 3 Ω z)
    (hP1x : TwinProductP1 p f Ω K z) : TwinProductNoExotic p f Ω K z := by
  intro M hM w hw hMK hKM D c hKc hMc
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hKx : K ∈ centralizingMembers Ω {z * w} := by
    have : K ∈ centralizingMembers Ω {z * w, z} := by
      rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair]
      exact ⟨hKz, le_centralizer_of_commutes hKM hw.mem⟩
    exact (mem_centralizingMembers_pair.mp this).1
  have hMx : M ∈ centralizingMembers Ω {z * w} := by
    have : M ∈ centralizingMembers Ω {z * w, z} := by
      rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair]
      exact ⟨⟨hM, le_centralizer_of_commutes (Commutes.symm hKM) hz.mem⟩,
        le_centralizer_of_isClassicalMember hw⟩
    exact (mem_centralizingMembers_pair.mp this).1
  have hzw : z ≠ w := fun h =>
    not_mem_of_commutes_ne hq hΩ hex hK hz hP1 d hM hMK hKM (h ▸ hw.mem)
  by_contra hexo
  have ht : D.tag c = .G2 ∨ D.tag c = .trialityD4 := by
    by_contra h
    exact hexo (not_or.mp h)
  exact hzw (G2D4.eq_involution_of_commuting_pair hSI hp2 hΩ (hP1x M hM w hw hMK hKM) D ht
    ⟨hKx, hKc⟩ ⟨hMx, hMc⟩ hz hw hKM)

end Exotic

end NonClassical

end CFSG.ClassicalInvolution.RouteD
