module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinBWeakNodes

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair longBlock shortBlock
  planeGroup IsHyperbolicPlane symplecticBlockStandardPair_conj
  exists_planeGroup_eq_conj_longBlock shortBlock_sup_longBlock_eq_top)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}

structure SpLayer (p f a : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (x : G) where
  D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)
  card_eq : D.card = a + 1
  i₁ : Fin D.card
  tag_eq : D.tag i₁ = .PSp
  rank_eq : D.rank i₁ = 2
  rest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2

theorem LocalShapeT.nonempty_spLayer {a : ℕ} (h : LocalShapeT p f a .PSp 2 Ω x) :
    Nonempty (SpLayer p f a Ω x) := by
  obtain ⟨D, hcard, i₁, ht, hr, hrest⟩ := h
  exact ⟨⟨D, hcard, i₁, ht, hr, hrest⟩⟩

namespace SpLayer

variable {a : ℕ} (Λ : SpLayer p f a Ω x)

noncomputable def ψ : StatedSp 2 (GaloisField p f) →* locQuot Ω x :=
  (exists_psp_hom Λ.D Λ.i₁ Λ.tag_eq (m := 2) Λ.rank_eq).choose

theorem ψ_spec : Λ.ψ.ker ≤ Subgroup.center (StatedSp 2 (GaloisField p f)) ∧
    Λ.ψ.range = (Λ.D.hom Λ.i₁).range ∧
    ∀ K : Subgroup (locQuot Ω x), (∃ R ∈ fundamentalSubgroups (Λ.D.tag Λ.i₁)
        (modelUniv (Λ.D.tag Λ.i₁) (Λ.D.rank Λ.i₁) p (Λ.D.exp Λ.i₁) Fact.out).D,
          K = R.map (Λ.D.hom Λ.i₁)) ↔
      ∃ P, IsHyperbolicPlane P ∧ K = (planeGroup P).map Λ.ψ :=
  (exists_psp_hom Λ.D Λ.i₁ Λ.tag_eq (m := 2) Λ.rank_eq).choose_spec

theorem ψ_ker : Λ.ψ.ker ≤ Subgroup.center (StatedSp 2 (GaloisField p f)) := Λ.ψ_spec.1

theorem ψ_range : Λ.ψ.range = (Λ.D.hom Λ.i₁).range := Λ.ψ_spec.2.1

theorem exists_plane_of_mem [Finite G] (hΩ : InClass p f Ω) (hP1 : LocalOddCentral Ω {x})
    {M : Subgroup G} (hM : M ∈ centralizingMembers Ω {x})
    (hMi : locImg Ω x M ≤ (Λ.D.hom Λ.i₁).range) :
    ∃ P, IsHyperbolicPlane P ∧ locImg Ω x M = (planeGroup P).map Λ.ψ := by
  have hmem : locImg Ω x M ∈ locFamily Ω x := mem_locFamily_iff.mpr ⟨M, hM, rfl⟩
  obtain ⟨i, R, hR, hMR⟩ := Λ.D.fundamental _ hmem
  by_cases hi : i = Λ.i₁
  · subst hi
    exact (Λ.ψ_spec.2.2 _).mp ⟨R, hR, hMR⟩
  · exfalso
    have h1 : locImg Ω x M ≤ (Λ.D.hom i).range := hMR ▸ Subgroup.map_le_range _ _
    have h2 : ∀ w ∈ locImg Ω x M, w ∈ Subgroup.center (locQuot Ω x) := fun w hw =>
      range_inf_le_center Λ.D hi ⟨h1 hw, hMi hw⟩
    have hc : Commutes (locImg Ω x M) (locImg Ω x M) := fun u hu v _ =>
      (Subgroup.mem_center_iff.mp (h2 u hu) v).symm
    obtain ⟨z, hz⟩ := hΩ.classical M hM.1
    exact not_commutes_self_of_isClassicalMember hz
      (commutes_of_commutes_locImg_perfect hP1 (le_centralizingLayer hM) (le_centralizingLayer hM)
        (commutator_eq_of_isClassicalMember hz).ge hc)

@[expose] def IsShortNode (M Us : Subgroup G) : Prop :=
  Us ≤ locLayer Ω x ∧ ⁅Us, Us⁆ = Us ∧ locImg Ω x Us ≤ (Λ.D.hom Λ.i₁).range ∧
    (∃ W, SymplecticBlockPair (GaloisField p f) W M Us) ∧
    (∀ N ∈ centralizingMembers Ω {x}, ∀ j, j ≠ Λ.i₁ → locImg Ω x N ≤ (Λ.D.hom j).range →
      Commutes N Us) ∧
    locImg Ω x M ⊔ locImg Ω x Us = (Λ.D.hom Λ.i₁).range

theorem exists_shortNode [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hP1 : LocalOddCentral Ω {x}) {M : Subgroup G} (hM : M ∈ centralizingMembers Ω {x})
    (hMi : locImg Ω x M ≤ (Λ.D.hom Λ.i₁).range) :
    ∃ Us : Subgroup G, Λ.IsShortNode M Us := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by rw [hcard]; omega
  have h5 : 5 ≤ Nat.card (GaloisField p f) := by rw [hcard]; exact hq
  obtain ⟨P, hP, hMP⟩ := Λ.exists_plane_of_mem hΩ hP1 hM hMi
  obtain ⟨g, hg⟩ := exists_planeGroup_eq_conj_longBlock hP (1 : Fin 2)
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hstd := symplecticBlockStandardPair_conj (K := GaloisField p f) (n := 2) h01 g
  have hpairX := symplecticBlockPair_map_central h5 hstd Λ.ψ Λ.ψ_ker
  set Rs : Subgroup (StatedSp 2 (GaloisField p f)) :=
    (shortBlock (GaloisField p f) h01).range.map (MulAut.conj g).toMonoidHom with hRs
  have hSperf : Rs.map Λ.ψ ≤ ⁅Rs.map Λ.ψ, Rs.map Λ.ψ⁆ :=
    (symplecticBlockPair_perfect h4 hpairX).2
  obtain ⟨A, hAperf, hAmap⟩ := exists_perfect_lift hP1 hSperf
  set Yl : Subgroup G := locLayer Ω x with hYl
  let Us : Subgroup G := A.map Yl.subtype
  have hUsimg : locImg Ω x Us = Rs.map Λ.ψ := by
    show locImg Ω x (A.map Yl.subtype) = _
    rw [locImg_map_subtype, hAmap]
  have hUsY : Us ≤ Yl := Subgroup.map_subtype_le _
  have hUsperf : Us ≤ ⁅Us, Us⁆ := by
    show A.map Yl.subtype ≤ ⁅A.map Yl.subtype, A.map Yl.subtype⁆
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hAperf
  have hMY : M ≤ Yl := le_centralizingLayer hM
  have hMperf : M ≤ ⁅M, M⁆ := by
    obtain ⟨z, hz⟩ := hΩ.classical M hM.1
    exact (commutator_eq_of_isClassicalMember hz).ge
  have hUsrange : locImg Ω x Us ≤ (Λ.D.hom Λ.i₁).range := by
    rw [hUsimg, ← Λ.ψ_range]
    exact Subgroup.map_le_range _ _
  have hMUs : (locImg Ω x M) = ((longBlock (GaloisField p f) 2 1).range.map
      (MulAut.conj g).toMonoidHom).map Λ.ψ := by
    rw [hMP, hg]
  have hsup : (longBlock (GaloisField p f) 2 1).range.map (MulAut.conj g).toMonoidHom ⊔ Rs = ⊤ := by
    rw [hRs, ← Subgroup.map_sup, sup_comm, shortBlock_sup_longBlock_eq_top, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective
  obtain ⟨W, hW⟩ : ∃ W, SymplecticBlockPair (GaloisField p f) W (locImg Ω x M)
      (locImg Ω x Us) := ⟨_, by rw [hMUs, hUsimg]; exact hpairX⟩
  refine ⟨Us, hUsY, le_antisymm (commutator_self_le _) hUsperf, hUsrange, ?_, ?_, ?_⟩
  · exact symplecticBlockPair_of_locImg_perfect hp2 hq hP1 hMY hUsY hMperf hUsperf hW
  · intro N hN j hj hNj
    have hNY : N ≤ Yl := le_centralizingLayer hN
    have hNperf : N ≤ ⁅N, N⁆ := by
      obtain ⟨z, hz⟩ := hΩ.classical N hN.1
      exact (commutator_eq_of_isClassicalMember hz).ge
    refine commutes_of_commutes_locImg_perfect hP1 hNY hUsY hNperf ?_
    intro u hu w hw
    exact range_commute_of_ne Λ.D hj u (hNj hu) w (hUsrange hw)
  · rw [hMUs, hUsimg, ← Subgroup.map_sup, hsup, Subgroup.map_top, Λ.ψ_range]

theorem exists_other_of_self [Finite G] (h5 : 5 ≤ p ^ f) {K : Subgroup G} (hK : K ∈ Ω)
    (hz : IsClassicalMember p f K x) (Λ : SpLayer p f a Ω x) :
    ∃ j, j ≠ Λ.i₁ ∧ locImg Ω x K ≤ (Λ.D.hom j).range := by
  have hKx : K ∈ centralizingMembers Ω {x} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hmem : locImg Ω x K ∈ locFamily Ω x := mem_locFamily_iff.mpr ⟨K, hKx, rfl⟩
  obtain ⟨i, R, hR, hKR⟩ := Λ.D.fundamental _ hmem
  by_cases hi : i = Λ.i₁
  · exfalso
    subst hi
    obtain ⟨P, hP, hPK⟩ := (Λ.ψ_spec.2.2 _).mp ⟨R, hR, hKR⟩
    let zY : ↥(locLayer Ω x) := ⟨x, le_centralizingLayer hKx hz.mem⟩
    have hzK : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) zY ∈
        locImg Ω x K := ⟨zY, Subgroup.mem_subgroupOf.mpr hz.mem, rfl⟩
    rw [hPK] at hzK
    obtain ⟨r, hrP, hr⟩ := hzK
    have hcentral : ∀ w : locQuot Ω x,
        w * QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) zY =
          QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) zY * w := by
      intro w
      obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective _ w
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (centralizingLayer_le_centralizer Ω {x} w'.2)
    have hrc : r ∈ Subgroup.center (StatedSp 2 (GaloisField p f)) := by
      refine Models.SymplecticPairs.mem_center_of_forall_commutator_mem_center
        (Models.SymplecticPairs.isPerfect_statedSp_of_four_le (four_le_natCard_galoisField h5))
        fun s => Λ.ψ_ker ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, hr]
      rw [commutatorElement_def, ← hcentral (Λ.ψ s), mul_inv_cancel_right, mul_inv_cancel]
    have hr1 : r = 1 := eq_one_of_mem_planeGroup_of_mem_center le_rfl hP hrP hrc
    rw [hr1, map_one] at hr
    have hO : zY ∈ classicalInvolutionOddCore ↥(locLayer Ω x) :=
      (QuotientGroup.eq_one_iff _).mp hr.symm
    have h2 : orderOf zY = 2 := by
      rw [Subgroup.orderOf_mk]; exact hz.orderOf_eq_two
    have h3 := orderOf_dvd_natCard (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x))
    have h4 : orderOf (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact h2
    rw [h4] at h3
    have := (CFSG.ComponentClassification.OddCore.odd_card (↥(locLayer Ω x)))
    exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h3)
  · exact ⟨i, hi, hKR ▸ Subgroup.map_le_range _ _⟩

theorem range_eq_top (ha : a = 0) : (Λ.D.hom Λ.i₁).range = ⊤ := by
  have hall : ∀ i : Fin Λ.D.card, i = Λ.i₁ := fun i => Fin.ext (by
    have h1 := i.2
    have h2 := Λ.i₁.2
    have hc : Λ.D.card = 1 := by rw [Λ.card_eq, ha]
    omega)
  rw [eq_top_iff, ← Λ.D.generate]
  exact iSup_le fun i => by rw [hall i]

theorem layer_le_sup [Finite G] (ha : a = 0) (hΩ : InClass p f Ω) (hP1 : LocalOddCentral Ω {x})
    {M Us : Subgroup G} (hsn : Λ.IsShortNode M Us) :
    locLayer Ω x ≤ M ⊔ Us := by
  set Y : Subgroup G := locLayer Ω x with hY
  have hperfY : Y ≤ ⁅Y, Y⁆ := iSup₂_le fun L hL => by
    obtain ⟨z, hz⟩ := hΩ.classical L hL.1
    exact (commutator_eq_of_isClassicalMember hz).ge.trans
      (Subgroup.commutator_mono (le_centralizingLayer hL) (le_centralizingLayer hL))
  have hperfT : (⊤ : Subgroup ↥Y) ≤ ⁅(⊤ : Subgroup ↥Y), ⊤⁆ := by
    have := perfect_subgroupOf (le_refl Y) hperfY
    rwa [Subgroup.subgroupOf_self] at this
  set O := classicalInvolutionOddCore ↥Y with hO
  set N' : Subgroup ↥Y := M.subgroupOf Y ⊔ Us.subgroupOf Y with hN'
  have hTop : (⊤ : Subgroup ↥Y) ≤ N' ⊔ O := by
    intro y _
    have hrange : QuotientGroup.mk' O y ∈ locImg Ω x M ⊔ locImg Ω x Us := by
      rw [hsn.2.2.2.2.2, Λ.range_eq_top ha]
      trivial
    have himg : locImg Ω x M ⊔ locImg Ω x Us = N'.map (QuotientGroup.mk' O) := by
      unfold locImg
      rw [Subgroup.map_sup]
    rw [himg] at hrange
    obtain ⟨w, hw, hwy⟩ := hrange
    have hmem : w⁻¹ * y ∈ O := QuotientGroup.eq.mp hwy
    have hyw : y = w * (w⁻¹ * y) := by group
    rw [hyw]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right hmem)
  have hTop' := le_of_perfect_of_le_sup_center hP1 hperfT hTop
  intro g hg
  have h1 : (⟨g, hg⟩ : ↥Y) ∈ N' := hTop' (Subgroup.mem_top _)
  have h2 : N' ≤ (M ⊔ Us).subgroupOf Y := sup_le
    (fun u hu => Subgroup.mem_subgroupOf.mpr
      ((show M ≤ M ⊔ Us from le_sup_left) (Subgroup.mem_subgroupOf.mp hu)))
    (fun u hu => Subgroup.mem_subgroupOf.mpr
      ((show Us ≤ M ⊔ Us from le_sup_right) (Subgroup.mem_subgroupOf.mp hu)))
  exact Subgroup.mem_subgroupOf.mp (h2 h1)

end SpLayer

end CFSG.ClassicalInvolution.RouteD
