module

public import CFSG.ClassicalInvolution.RouteD.GapsR2
public import CFSG.ClassicalInvolution.RouteD.TypeCBlock
public import CFSG.ClassicalInvolution.RouteD.TypeCThreeLayers

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  isHyperbolicPlane_stdPlane longBlock planeTorus longInv suppGroup coords)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem exists_layer_conj (S : CSetupW p f 2 Ω K z) (Fr : Frame p f 2 Ω K z) (i : Fin 3)
    {L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ centralizingMembers Ω {Fr.zf i})
    (h₂ : L₂ ∈ centralizingMembers Ω {Fr.zf i}) (n₁ : L₁ ≠ Fr.Kf i) (n₂ : L₂ ≠ Fr.Kf i) :
    ∃ y ∈ locLayer Ω (Fr.zf i), L₂ = conjSub y L₁ := by
  obtain ⟨d⟩ := LocalShapeC.nonempty_dict S.inClass (Fr.mem i) (Fr.clsW S i)
    (S.shape.conj S.conjInvariant (Fr.gf i))
  have hP1 := Fr.p1W S i
  obtain ⟨P₁, hP₁, hL₁⟩ := typeC_exists_plane_of_ne S.two_le S.five S.inClass S.exact (Fr.mem i)
    (Fr.clsW S i) hP1 d h₁ n₁
  obtain ⟨P₂, hP₂, hL₂⟩ := typeC_exists_plane_of_ne S.two_le S.five S.inClass S.exact (Fr.mem i)
    (Fr.clsW S i) hP1 d h₂ n₂
  obtain ⟨g₁, hg₁⟩ := Models.SymplecticPairs.exists_planeGroup_eq_conj_longBlock hP₁
    (⟨0, by omega⟩ : Fin 2)
  obtain ⟨g₂, hg₂⟩ := Models.SymplecticPairs.exists_planeGroup_eq_conj_longBlock hP₂
    (⟨0, by omega⟩ : Fin 2)
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (d.ψ (g₂ * g₁⁻¹))
  refine ⟨(y : G), y.2, ?_⟩
  have hcent : conjSub (y : G) L₁ ∈ centralizingMembers Ω {Fr.zf i} := by
    refine ⟨S.inClass.conjInvariant _ L₁ h₁.1, fun a ha => ?_⟩
    have hyx : (y : G) ∈ Subgroup.centralizer ({Fr.zf i} : Set G) :=
      centralizingLayer_le_centralizer Ω {Fr.zf i} y.2
    rw [mem_conjSub_iff] at ha
    have hx' := h₁.2 ha
    have : a = (y : G) * ((y : G)⁻¹ * a * (y : G)) * (y : G)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyx hx') ((Subgroup.inv_mem _) hyx)
  refine (locImg_injOn S.inClass hP1 hcent h₂ ?_).symm
  rw [Gaps.locImg_conjSub_layer, hL₁, hL₂,
    show Gaps.locMk Ω (Fr.zf i) y = d.ψ (g₂ * g₁⁻¹) from hy, hg₁, hg₂, Subgroup.map_map,
    Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp [mul_assoc]

theorem eq_top_of_swap (S : CSetupW p f 2 Ω K z) (hconn : DeltaConnected Ω)
    (Fr : Frame p f 2 Ω K z) {i j : Fin 3} (hij : i ≠ j) {H : Subgroup G}
    (hH : locLayer Ω (Fr.zf i) ≤ H) {r : G} (hr : r ∈ H) (hrK : conjSub r (Fr.Kf i) = Fr.Kf j) :
    H = ⊤ := by
  set 𝔖 : Set (Subgroup G) := {L | ∃ h ∈ H, L = conjSub h (Fr.Kf i)} with h𝔖
  have hsub : 𝔖 ⊆ Ω := by
    rintro _ ⟨h, -, rfl⟩
    exact S.inClass.conjInvariant _ _ (Fr.mem i)
  have hne : 𝔖.Nonempty := ⟨Fr.Kf i, 1, H.one_mem, (conjSub_one _).symm⟩
  have hcl : ∀ N ∈ 𝔖, ∀ L ∈ Ω, L ≠ N → Commutes N L → L ∈ 𝔖 := by
    rintro _ ⟨h, hh, rfl⟩ L hL hLN hc
    have hL' : conjSub h⁻¹ L ∈ Ω := S.inClass.conjInvariant _ _ hL
    have hcomm : Commutes (Fr.Kf i) (conjSub h⁻¹ L) := by
      have := (commutes_conjSub_iff h⁻¹).mpr hc
      rwa [conjSub_inv_conjSub] at this
    have hne' : conjSub h⁻¹ L ≠ Fr.Kf i := by
      intro e
      apply hLN
      rw [← e, conjSub_conjSub_inv]
    have hcent : conjSub h⁻¹ L ∈ centralizingMembers Ω {Fr.zf i} :=
      ⟨hL', fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
        (hcomm _ (Frame.zf_memW S i) a ha).symm⟩
    obtain ⟨y, hy, hyL⟩ := exists_layer_conj S Fr i (Fr.mem_centW S j i) hcent
      (Fr.ne_of_neW S hij.symm) hne'
    refine ⟨h * (y * r), H.mul_mem hh (H.mul_mem (hH hy) hr), ?_⟩
    rw [conjSub_mul h (y * r), conjSub_mul y r, hrK, ← hyL, conjSub_conjSub_inv]
  have hall := subset_of_adj_closed hconn hsub hne hcl
  rw [eq_top_iff, ← S.inClass.generated]
  refine iSup₂_le fun L hL => ?_
  obtain ⟨h, hh, rfl⟩ := hall hL
  intro a ha
  rw [mem_conjSub_iff] at ha
  have hK : Fr.Kf i ≤ H := (Fr.Kf_le_locLayerW S i i).trans hH
  have := hK ha
  have e : a = h * (h⁻¹ * a * h) * h⁻¹ := by group
  rw [e]
  exact H.mul_mem (H.mul_mem hh this) (H.inv_mem hh)

theorem exists_swap_in_layer (S : CSetupW p f 2 Ω K z) (Fr : Frame p f 2 Ω K z) {l : Fin 3}
    (LF : LocalFrameI Fr l) :
    ∃ r ∈ locLayer Ω (Fr.zf l), ∃ _ : r ∈ Mf Fr (l.succAbove 0) (l.succAbove 1),
      conjSub r (Fr.Kf (l.succAbove 0)) = Fr.Kf (l.succAbove 1) := by
  have hab : (0 : Fin 2) ≠ 1 := by decide
  obtain ⟨g, hg⟩ := Models.SymplecticPairs.exists_planeGroup_eq_conj_longBlock
    (isHyperbolicPlane_stdPlane (K := GaloisField p f) (n := 2) 1) 0
  have hmem : g ∈ (suppGroup (coords (0 : Fin 2) ∪ coords (1 : Fin 2)) :
      Subgroup (StatedSp 2 (GaloisField p f))) := by
    rw [Models.SymplecticPairs.suppGroup_coords_zero_union_one]
    exact Subgroup.mem_top _
  set u := LF.layerEquiv S hab ⟨g, hmem⟩ with hu
  have hrM : ((u : ↥(Mf Fr (l.succAbove 0) (l.succAbove 1))) : G) ∈
      Mf Fr (l.succAbove 0) (l.succAbove 1) := u.2
  have hrY : ((u : ↥(Mf Fr (l.succAbove 0) (l.succAbove 1))) : G) ∈ locLayer Ω (Fr.zf l) :=
    LocalFrame.Mf_le_locLayerW S 0 1 hrM
  refine ⟨_, hrY, hrM, ?_⟩
  have hKa : Fr.Kf (l.succAbove 0) ∈ centralizingMembers Ω {Fr.zf l} := Fr.mem_centW S _ l
  have hKb : Fr.Kf (l.succAbove 1) ∈ centralizingMembers Ω {Fr.zf l} := Fr.mem_centW S _ l
  have hcent : conjSub ((u : ↥(Mf Fr (l.succAbove 0) (l.succAbove 1))) : G)
      (Fr.Kf (l.succAbove 0)) ∈ centralizingMembers Ω {Fr.zf l} := by
    refine ⟨S.inClass.conjInvariant _ _ hKa.1, fun a ha => ?_⟩
    have hyx : ((u : ↥(Mf Fr (l.succAbove 0) (l.succAbove 1))) : G) ∈
        Subgroup.centralizer ({Fr.zf l} : Set G) :=
      centralizingLayer_le_centralizer Ω {Fr.zf l} hrY
    rw [mem_conjSub_iff] at ha
    have hx' := hKa.2 ha
    have : a = ((u : ↥(Mf Fr (l.succAbove 0) (l.succAbove 1))) : G) *
        (((u : ↥(Mf Fr (l.succAbove 0) (l.succAbove 1))) : G)⁻¹ * a *
          ((u : ↥(Mf Fr (l.succAbove 0) (l.succAbove 1))) : G)) *
        ((u : ↥(Mf Fr (l.succAbove 0) (l.succAbove 1))) : G)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyx hx') ((Subgroup.inv_mem _) hyx)
  refine locImg_injOn S.inClass (Fr.p1W S l) hcent hKb ?_
  have hlay := Gaps.locImg_conjSub_layer (Ω := Ω) (x := Fr.zf l) (Fr.Kf (l.succAbove 0))
    ⟨_, hrY⟩
  rw [hlay]
  have hpi : Gaps.locMk Ω (Fr.zf l) ⟨((u : ↥(Mf Fr (l.succAbove 0) (l.succAbove 1))) : G), hrY⟩ =
      LF.d.ψ g := LF.locHom_layerEquiv S hab ⟨g, hmem⟩
  rw [hpi, ← LF.adapted 0, ← LF.adapted 1, Subgroup.map_map]
  have hb : (longBlock (GaloisField p f) 2 1).range = planeGroup (stdPlane (GaloisField p f) 2 1) :=
    (Models.SymplecticPairs.planeGroup_stdPlane 1).symm
  rw [hb, hg, Subgroup.map_map]
  congr 1
  ext a
  simp

theorem zf_mul_commutes (S : CSetupW p f 2 Ω K z) (Fr : Frame p f 2 Ω K z) (l : Fin 3)
    {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {Fr.zf l}) :
    ∀ a ∈ L, a * (Fr.zf (l.succAbove 0) * Fr.zf (l.succAbove 1)) =
      (Fr.zf (l.succAbove 0) * Fr.zf (l.succAbove 1)) * a := by
  have hab : (0 : Fin 2) ≠ 1 := by decide
  have hne : ∀ c : Fin 2, l ≠ l.succAbove c := fun c => (Fin.succAbove_ne l c).symm
  by_cases hLK : L = Fr.Kf l
  · subst hLK
    intro a ha
    have h0 : a * Fr.zf (l.succAbove 0) = Fr.zf (l.succAbove 0) * a :=
      Fr.commute _ _ (hne 0) a ha _ (Frame.zf_memW S _)
    have h1 : a * Fr.zf (l.succAbove 1) = Fr.zf (l.succAbove 1) * a :=
      Fr.commute _ _ (hne 1) a ha _ (Frame.zf_memW S _)
    rw [← mul_assoc, h0, mul_assoc, h1, ← mul_assoc]
  · obtain ⟨LF⟩ := exists_localFrameIW S Fr l
    have hle : ∀ c : Fin 2, Fr.zf (l.succAbove c) ∈ locLayer Ω (Fr.zf l) := fun c =>
      Fr.Kf_le_locLayerW S _ l (Frame.zf_memW S _)
    have hy : Fr.zf (l.succAbove 0) * Fr.zf (l.succAbove 1) ∈ locLayer Ω (Fr.zf l) :=
      Subgroup.mul_mem _ (hle 0) (hle 1)
    obtain ⟨P, hP, hLP⟩ := typeC_exists_plane_of_ne S.two_le S.five S.inClass S.exact (Fr.mem l)
      (Fr.clsW S l) (Fr.p1W S l) LF.d hL hLK
    refine commutes_elem_of_commutes_locImg S.inClass (Fr.p1W S l) hL hy ?_
    intro w hw
    rw [hLP] at hw
    obtain ⟨s, -, rfl⟩ := hw
    have hmk : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω (Fr.zf l)))
        ⟨Fr.zf (l.succAbove 0) * Fr.zf (l.succAbove 1), hy⟩ =
        LF.d.ψ (longInv (GaloisField p f) 2 0 * longInv (GaloisField p f) 2 1) := by
      rw [show (⟨Fr.zf (l.succAbove 0) * Fr.zf (l.succAbove 1), hy⟩ : ↥(locLayer Ω (Fr.zf l))) =
        ⟨Fr.zf (l.succAbove 0), hle 0⟩ * ⟨Fr.zf (l.succAbove 1), hle 1⟩ from rfl, map_mul,
        LF.mk_zfW S 0, LF.mk_zfW S 1, map_mul]
    have hs : s ∈ (suppGroup (coords (0 : Fin 2) ∪ coords (1 : Fin 2)) :
        Subgroup (StatedSp 2 (GaloisField p f))) := by
      rw [Models.SymplecticPairs.suppGroup_coords_zero_union_one]
      exact Subgroup.mem_top _
    have hc := Models.SymplecticPairs.commute_longInv_mul_longInv hab hs
    rw [hmk, ← map_mul, ← map_mul, hc.eq]

theorem locLayer_le_centralizer_of_eq (S : CSetupW p f 2 Ω K z) (Fr : Frame p f 2 Ω K z)
    (l : Fin 3) {x : G}
    (hx : x = Fr.zf l * (Fr.zf (l.succAbove 0) * Fr.zf (l.succAbove 1))) :
    locLayer Ω (Fr.zf l) ≤ Subgroup.centralizer ({x} : Set G) := by
  refine iSup₂_le fun L hL a ha => ?_
  rw [Subgroup.mem_centralizer_singleton_iff, hx]
  have h1 : a * Fr.zf l = Fr.zf l * a :=
    Subgroup.mem_centralizer_singleton_iff.mp (hL.2 ha)
  rw [← mul_assoc, h1, mul_assoc, zf_mul_commutes S Fr l hL a ha, ← mul_assoc]

theorem zf_mul_zf_mul_zf (S : CSetupW p f 2 Ω K z) (hconn : DeltaConnected Ω)
    (hZ : Subgroup.center G = ⊥) (Fr : Frame p f 2 Ω K z) :
    Fr.zf 0 * Fr.zf 1 * Fr.zf 2 = 1 := by
  set x := Fr.zf 0 * Fr.zf 1 * Fr.zf 2 with hx
  have e00 : (0 : Fin 3).succAbove 0 = 1 := by decide
  have e01 : (0 : Fin 3).succAbove 1 = 2 := by decide
  have e20 : (2 : Fin 3).succAbove 0 = 0 := by decide
  have e21 : (2 : Fin 3).succAbove 1 = 1 := by decide
  have h0 : locLayer Ω (Fr.zf 0) ≤ Subgroup.centralizer ({x} : Set G) :=
    locLayer_le_centralizer_of_eq S Fr 0 (by rw [e00, e01, hx, mul_assoc])
  have h2 : locLayer Ω (Fr.zf 2) ≤ Subgroup.centralizer ({x} : Set G) := by
    refine locLayer_le_centralizer_of_eq S Fr 2 ?_
    rw [e20, e21, hx]
    have hc : Fr.zf 2 * (Fr.zf 0 * Fr.zf 1) = (Fr.zf 0 * Fr.zf 1) * Fr.zf 2 := by
      rw [← mul_assoc, Fr.zf_commW S 2 0, mul_assoc, Fr.zf_commW S 2 1, ← mul_assoc]
    rw [hc]
  obtain ⟨LF⟩ := exists_localFrameIW S Fr 2
  obtain ⟨r, hrY, hrM, hrK⟩ := exists_swap_in_layer S Fr LF
  rw [e20, e21] at hrK
  have hH : locLayer Ω (Fr.zf 0) ⊔ locLayer Ω (Fr.zf 2) = ⊤ :=
    eq_top_of_swap S hconn Fr (i := 0) (j := 1) (by decide) le_sup_left
      (le_sup_right (a := locLayer Ω (Fr.zf 0)) (b := locLayer Ω (Fr.zf 2)) hrY) hrK
  have hxc : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ locLayer Ω (Fr.zf 0) ⊔ locLayer Ω (Fr.zf 2) := by
      rw [hH]
      exact Subgroup.mem_top g
    have := (sup_le h0 h2) hg
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  rw [hZ, Subgroup.mem_bot] at hxc
  exact hxc

theorem Mf_sup_Mf_eq_top (S : CSetupW p f 2 Ω K z) (hconn : DeltaConnected Ω)
    (Fr : Frame p f 2 Ω K z) : Mf Fr 0 1 ⊔ Mf Fr 1 2 = ⊤ := by
  have e20 : (2 : Fin 3).succAbove 0 = 0 := by decide
  have e21 : (2 : Fin 3).succAbove 1 = 1 := by decide
  obtain ⟨LF⟩ := exists_localFrameIW S Fr 2
  obtain ⟨r, -, hrM, hrK⟩ := exists_swap_in_layer S Fr LF
  rw [e20, e21] at hrM hrK
  obtain ⟨d⟩ := LocalShapeC.nonempty_dict S.inClass (Fr.mem 0) (Fr.clsW S 0)
    (S.shape.conj S.conjInvariant (Fr.gf 0))
  refine eq_top_of_swap S hconn Fr (i := 0) (j := 1) (by decide) ?_
    (le_sup_left (b := Mf Fr 1 2) hrM) hrK
  refine iSup₂_le fun L hL => ?_
  by_cases hLK : L = Fr.Kf 0
  · subst hLK
    exact (Kf_le_Mf Fr 0 (Or.inl rfl)).trans le_sup_left
  · refine (le_Mf Fr (i := 1) (j := 2) ⟨hL.1, fun k hk1 hk2 => ?_⟩).trans le_sup_right
    have hk0 : k = 0 := by
      fin_cases k <;> simp_all
    subst hk0
    exact (typeC_commutes_K_of_ne S.two_le S.five S.inClass S.exact (Fr.mem 0) (Fr.clsW S 0)
      (Fr.p1W S 0) d hL hLK).symm

end CFSG.ClassicalInvolution.RouteD
