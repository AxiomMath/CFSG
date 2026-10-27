module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25N2
public import CFSG.ClassicalInvolution.Asc77.AscC25V33
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25N1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S.N

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.C25V
open CFSG.ClassicalInvolution.Asc77.T3
open CFSG.ClassicalInvolution.Hat2A7M.Asc77.T7F2 (Hyp25T)
open scoped MatrixGroups commutatorElement

section TwinSec

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem fs_twinSect0 (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
    {a : G}
    (hat : a * t' = t' * a) {e₀ : ℕ} (hp : p ≠ 2) (h5 : 5 ≤ p ^ e₀)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K' a) ⟨z, hzA⟩)
    (hy : ∃ y ∈ R', orderOf y = 4 ∧ y * a = a * y ∧
      y ∈ perfectResidualOf (K' ⊓ Subgroup.centralizer ({a} : Set G))) :
    ∃ (ht'a : t' ∈ Subgroup.centralizer ({a} : Set G))
      (hzX : (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈
        conjGen (perfectCoreIn K' a))
      (a₀ b₀ : ↥(conjGen (perfectCoreIn K' a)) ⧸
        classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K' a))),
      TwinSect0 (oddQuotientFamily (restrictFamily (conjFamily (perfectCoreIn K' a))
        (conjGen (perfectCoreIn K' a))))
        (secImg (conjGen (perfectCoreIn K' a)) (perfectCoreIn K' a))
        (secImg (conjGen (perfectCoreIn K' a)) (conjSub (⟨t', ht'a⟩ :
          ↥(Subgroup.centralizer ({a} : Set G))) (perfectCoreIn K' a)))
        (QuotientGroup.mk ⟨⟨z, hzA⟩, hzX⟩) a₀ b₀ := by
  have ht'a : t' ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hat.symm
  refine ⟨ht'a, ?_⟩
  have d' := twinCtx'_of_hyp25 h
  have hΛ := fs_hypOmegaMod_conjFamily h.hΩ h.hK' h.hz' hzA hL
  have hzKa : z ∈ perfectResidualOf (K' ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.mem_subgroupOf.mp hL.mem
  set w : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨t', ht'a⟩ with hwdef
  have hw : conjSub (w : G) K' = K := conjSub_t'_K' h
  set L := perfectCoreIn K' a with hLdef
  set X := conjGen L with hX
  have hXn : X.Normal := conjGen_normal L
  have hLmem : L ∈ conjFamily L := ⟨1, conjSub_one L⟩
  have hL'mem : conjSub w L ∈ conjFamily L := ⟨w, rfl⟩
  have hLX : L ≤ X := le_conjGen hLmem
  have hL'X : conjSub w L ≤ X := le_conjGen hL'mem
  have hzw : w * ⟨z, hzA⟩ * w⁻¹ = (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) := by
    apply Subtype.ext
    change t' * z * t'⁻¹ = z
    calc t' * z * t'⁻¹ = z * t' * t'⁻¹ := by rw [t'_comm_z h]
      _ = z := by group
  have hu₁ : IsUniqueInvolution L ⟨z, hzA⟩ := by
    have := fs_isUniqueInvolution_conjSub h.hz' hzA hzKa 1
    simpa [conjSub_one] using this
  have hu₂ : IsUniqueInvolution (conjSub w L) ⟨z, hzA⟩ := by
    have := fs_isUniqueInvolution_conjSub h.hz' hzA hzKa w
    rwa [hzw] at this
  have hne : conjSub w L ≠ L := fs_swap_ne d' hp hzA hL hw
  have hN : Odd (Nat.card (classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hΛ₁ : HypOmegaMod p e₀ (restrictFamily (conjFamily L) X) := hΛ.restrict X
  have hΛ' : HypOmegaMod p e₀
      (quotFamily (restrictFamily (conjFamily L) X) (classicalInvolutionOddCore ↥X)) :=
    oddQuotHyp p e₀ hp h5 ↥X _ hΛ₁ _ hN
  have hzX : (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ X := hLX hu₁.mem
  set z₀ : ↥X ⧸ classicalInvolutionOddCore ↥X := QuotientGroup.mk ⟨⟨z, hzA⟩, hzX⟩ with hz₀
  have hz₀A : IsUniqueInvolution (secImg X L) z₀ := by
    have h1 := fs_isUniqueInvolution_secImg h.hz' hzA hzKa 1
    have e1 : (QuotientGroup.mk' _ ⟨1 * ⟨z, hzA⟩ * 1⁻¹, le_conjGen ⟨1, rfl⟩
        (fs_isUniqueInvolution_conjSub h.hz' hzA hzKa 1).mem⟩ :
          ↥X ⧸ classicalInvolutionOddCore ↥X) = z₀ := by
      apply congrArg QuotientGroup.mk
      apply Subtype.ext
      simp
    rw [e1, conjSub_one] at h1
    exact h1
  have hz₀A' : IsUniqueInvolution (secImg X (conjSub w L)) z₀ := by
    have h1 := fs_isUniqueInvolution_secImg h.hz' hzA hzKa w
    have e1 : (QuotientGroup.mk' _ ⟨w * ⟨z, hzA⟩ * w⁻¹, le_conjGen ⟨w, rfl⟩
        (fs_isUniqueInvolution_conjSub h.hz' hzA hzKa w).mem⟩ :
          ↥X ⧸ classicalInvolutionOddCore ↥X) = z₀ := by
      apply congrArg QuotientGroup.mk
      apply Subtype.ext
      exact hzw
    rw [e1] at h1
    exact h1
  obtain ⟨V₁, V₂, hV₁, hV₂, hc⟩ := T7A.exists_commuting_sylow_twin hΛ hLmem hL'mem hne hu₁ hu₂
  have hcomm : Commutes (V₁.subgroupOf X) (V₂.subgroupOf X) := by
    intro x hx y hy
    apply Subtype.ext
    exact hc (x : ↥(Subgroup.centralizer ({a} : Set G))) (Subgroup.mem_subgroupOf.mp hx) y
      (Subgroup.mem_subgroupOf.mp hy)
  have hne_img : secImg X L ≠ secImg X (conjSub w L) :=
    map_ne_of_commutes_sylow hp hΛ' hN (M₁ := L.subgroupOf X) (M₂ := (conjSub w L).subgroupOf X)
      (V₁ := V₁.subgroupOf X) (V₂ := V₂.subgroupOf X) ⟨L, hLmem, hLX, rfl⟩
      (Hall196.isSylow2In_subgroupOf_of_le hV₁ hLX)
      (Hall196.isSylow2In_subgroupOf_of_le hV₂ hL'X) hcomm
  obtain ⟨y, hyR', hy4, hya, hyP⟩ := hy
  have hyC : y ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hya
  have hyL : (⟨y, hyC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ L :=
    Subgroup.mem_subgroupOf.mpr hyP
  have hyX : (⟨y, hyC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ X := hLX hyL
  have hysq : y * y = z := C25X.sq_eq_of_orderOf_four h.hz' (h.hR'syl.1 hyR') hy4
  have hbL' : w * ⟨y, hyC⟩ * w⁻¹ ∈ conjSub w L := conj_mem_conjSub hyL
  have hbX : w * ⟨y, hyC⟩ * w⁻¹ ∈ X := hL'X hbL'
  refine ⟨hzX, QuotientGroup.mk ⟨⟨y, hyC⟩, hyX⟩, QuotientGroup.mk ⟨w * ⟨y, hyC⟩ * w⁻¹, hbX⟩,
    ⟨(mem_secFamily_iff L _).mpr ⟨1, by rw [conjSub_one]⟩, (mem_secFamily_iff L _).mpr ⟨w, rfl⟩,
      hne_img, hz₀A, hz₀A',
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyL),
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hbL'), ?_, ?_, ?_, ?_⟩⟩
  · rw [← QuotientGroup.mk_mul]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    apply Subtype.ext
    exact hysq
  · rw [← QuotientGroup.mk_mul]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    have e : w * ⟨y, hyC⟩ * w⁻¹ * (w * ⟨y, hyC⟩ * w⁻¹) =
        w * (⟨y, hyC⟩ * ⟨y, hyC⟩) * w⁻¹ := by group
    have e2 : (⟨y, hyC⟩ * ⟨y, hyC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) = ⟨z, hzA⟩ :=
      Subtype.ext hysq
    change w * ⟨y, hyC⟩ * w⁻¹ * (w * ⟨y, hyC⟩ * w⁻¹) = ⟨z, hzA⟩
    rw [e, e2, hzw]
  · intro M hM hMn
    have := fs_nbr_quot d' hp h5 hzA hL hΛ hw 1 (M := M) (by rwa [conjSub_one])
    simpa using this
  · intro M hM hMn
    have := fs_nbr_quot d' hp h5 hzA hL hΛ hw w (M := M) hMn
    have hww : w * w = 1 := Subtype.ext h.ht'2
    rwa [hww, conjSub_one] at this

theorem fs_nc4_excl (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') {a : G} {e₀ : ℕ}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K' a) ⟨z, hzA⟩) :
    ∀ {J₁ J₂ : Subgroup (↥(conjGen (perfectCoreIn K' a)) ⧸
        classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K' a)))},
      J₁ ∈ oddQuotientFamily (restrictFamily (conjFamily (perfectCoreIn K' a))
        (conjGen (perfectCoreIn K' a))) →
      J₂ ∈ oddQuotientFamily (restrictFamily (conjFamily (perfectCoreIn K' a))
        (conjGen (perfectCoreIn K' a))) →
      ∀ {y z₂ : ↥(conjGen (perfectCoreIn K' a)) ⧸
        classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K' a))},
        y ∈ J₁ → y * y * y * y = 1 → y * y ≠ 1 → z₂ ∈ J₂ → z₂ * z₂ = 1 → z₂ ≠ 1 →
        z₂ ≠ y * y → z₂ * y = y * z₂ → False := by
  have hzKa : z ∈ perfectResidualOf (K' ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.mem_subgroupOf.mp hL.mem
  intro J₁ J₂ hJ₁ hJ₂ y z₂ hy hy4 hy2 hz₂ hz₂2 hz₂1 hne hcomm
  have hNC4 : ∀ c₁ c₂ y₁ : ↥(Subgroup.centralizer ({a} : Set G)),
      y₁ ∈ conjSub c₁ (perfectCoreIn K' a) → orderOf y₁ = 4 →
      y₁ * (c₂ * ⟨z, hzA⟩ * c₂⁻¹) = (c₂ * ⟨z, hzA⟩ * c₂⁻¹) * y₁ →
      c₂ * ⟨z, hzA⟩ * c₂⁻¹ = c₁ * ⟨z, hzA⟩ * c₁⁻¹ := by
    intro c₁ c₂ y₁ hy₁ hy₁4 hcomm
    have hy₁4' : orderOf (y₁ : G) = 4 := by rw [Subgroup.orderOf_coe]; exact hy₁4
    have hcomm' : ((c₂ : G) * z * (c₂ : G)⁻¹) * (y₁ : G) =
        (y₁ : G) * ((c₂ : G) * z * (c₂ : G)⁻¹) := (congrArg Subtype.val hcomm).symm
    have := eq_conj_z_of_commute_order_four h (c := (c₁ : G)) (g := (c₂ : G)) (y₀ := (y₁ : G))
      (le_conjSub_of_mem c₁ hy₁) hy₁4' hcomm'
    exact Subtype.ext this
  exact nc4_excl_generic (perfectCoreIn K' a) ⟨z, hzA⟩
    (fun c => fs_isUniqueInvolution_conjSub h.hz' hzA hzKa c) hNC4 hJ₁ hJ₂ hy hy4 hy2 hz₂ hz₂2
    hz₂1 hne hcomm

theorem fs_typed {e₀ : ℕ} (hp : p ≠ 2) (h5 : 5 ≤ p ^ e₀) (hIH : CITBelowU p e₀ (Nat.card G))
    (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') {a : G}
    (hat : a * t' = t' * a)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K' a) ⟨z, hzA⟩)
    (hy : ∃ y ∈ R', orderOf y = 4 ∧ y * a = a * y ∧
      y ∈ perfectResidualOf (K' ⊓ Subgroup.centralizer ({a} : Set G)))
    (hlt : Nat.card ↥(Subgroup.centralizer ({a} : Set G)) < Nat.card G) :
    z ∈ zStarOf (Subgroup.centralizer ({a} : Set G)) ∨
      SectionOrthType p e₀ (conjFamily (perfectCoreIn K' a)) (conjGen (perfectCoreIn K' a))
        5 true ∨
      SectionOrthType p e₀ (conjFamily (perfectCoreIn K' a)) (conjGen (perfectCoreIn K' a))
        6 (!piSign p e₀) := by
  classical
  obtain ⟨ht'a, hzX, a₀, b₀, T⟩ := fs_twinSect0 h hat hp h5 hzA hL hy
  have hΛ := fs_hypOmegaMod_conjFamily h.hΩ h.hK' h.hz' hzA hL
  have hS := genSection_conjFamily hp h5 hL hΛ (aEmpty_conjFamily_perfectCore h hp hzA hL)
  have hlt' : Nat.card (↥(conjGen (perfectCoreIn K' a)) ⧸
      classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K' a))) < Nat.card G := by
    have h1 : Nat.card (↥(conjGen (perfectCoreIn K' a)) ⧸
        classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K' a))) ≤
          Nat.card ↥(conjGen (perfectCoreIn K' a)) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
    have h2 : Nat.card ↥(conjGen (perfectCoreIn K' a)) ≤
        Nat.card ↥(Subgroup.centralizer ({a} : Set G)) := Subgroup.card_le_card_group _
    omega
  rcases C25X.twinSection_cases0 hp h5 hIH hlt' hS T with hconn | ⟨D, hcard, i, hsix⟩
  · left
    have hzKa : z ∈ perfectResidualOf (K' ⊓ Subgroup.centralizer ({a} : Set G)) :=
      Subgroup.mem_subgroupOf.mp hL.mem
    have hu : ∀ c : ↥(Subgroup.centralizer ({a} : Set G)),
        IsUniqueInvolution (conjSub c (perfectCoreIn K' a)) (c * ⟨z, hzA⟩ * c⁻¹) :=
      fun c => fs_isUniqueInvolution_conjSub h.hz' hzA hzKa c
    have hconn' : ∀ c : ↥(Subgroup.centralizer ({a} : Set G)),
        secImg (conjGen (perfectCoreIn K' a)) (conjSub c (perfectCoreIn K' a)) =
          secImg (conjGen (perfectCoreIn K' a)) (perfectCoreIn K' a) ∨
        secImg (conjGen (perfectCoreIn K' a)) (conjSub c (perfectCoreIn K' a)) =
          secImg (conjGen (perfectCoreIn K' a)) (conjSub (⟨t', ht'a⟩ :
            ↥(Subgroup.centralizer ({a} : Set G))) (perfectCoreIn K' a)) :=
      fun c => hconn _ ((mem_secFamily_iff (perfectCoreIn K' a) _).mpr ⟨c, rfl⟩)
    unfold zStarOf
    refine Subgroup.mem_map.mpr ⟨⟨z, hzA⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective g
    exact (central_of_connected (perfectCoreIn K' a) ⟨z, hzA⟩ hu hzX _ T.hzA' hconn' c).symm
  · right
    have hmf : C25X.NC4Fact p := C25X.nc4Fact_proved p
    let M := T7L.toModelOfGen hS.hyp D hcard hS.gen i
    have hodd : Odd (p ^ e₀) := (Nat.Prime.odd_of_ne_two Fact.out hp).pow
    have hmod : p ^ e₀ % 4 = 1 ∨ p ^ e₀ % 4 = 3 := by
      obtain ⟨j, hj⟩ := hodd
      omega
    have key : ((D.tag i = .PSL ∧ D.rank i = 4 ∧ p ^ e₀ % 4 = 1) ∨
        (D.tag i = .PSU ∧ D.rank i = 4 ∧ p ^ e₀ % 4 = 3) ∨ (D.tag i = .POmegaOdd ∧ D.rank i = 3) ∨
        (D.tag i = .POmegaPlus ∧ D.rank i = 4) ∨ (D.tag i = .POmegaMinus ∧ D.rank i = 4)) →
        False := by
      intro hS4
      obtain ⟨J₁, hJ₁, J₂, hJ₂, y, hy, z₂, hz₂, hy4, hy2, hz₂2, hz₂1, hne, hcomm⟩ :=
        C25X.s4_excl hmf hp h5 M ⟨_, T.hA⟩ hS4
      exact fs_nc4_excl h hzA hL hJ₁ hJ₂ hy hy4 hy2 hz₂ hz₂2 hz₂1 hne hcomm
    rcases hsix with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact sectionOrthType_of_hasOrthType hS.gen
        ⟨_, _, Or.inl ⟨rfl, h1, h2⟩, D, hcard, i, rfl, rfl⟩
    · rcases hmod with h3 | h3
      · exact (key (Or.inl ⟨h1, h2, h3⟩)).elim
      · right
        have hπ : piSign p e₀ = false := by
          unfold piSign
          simp [h3]
        rw [hπ]
        exact sectionOrthType_of_hasOrthType hS.gen
          ⟨_, _, Or.inr (Or.inl ⟨rfl, rfl, h1, h2⟩), D, hcard, i, rfl, rfl⟩
    · rcases hmod with h3 | h3
      · right
        have hπ : piSign p e₀ = true := by
          unfold piSign
          simp [h3]
        rw [hπ]
        exact sectionOrthType_of_hasOrthType hS.gen
          ⟨_, _, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h1, h2⟩)), D, hcard, i, rfl, rfl⟩
      · exact (key (Or.inr (Or.inl ⟨h1, h2, h3⟩))).elim
    · exact (key (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))).elim
    · exact (key (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))).elim
    · exact (key (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))))).elim

end TwinSec

end CFSG.ClassicalInvolution.Hat2A7S.N
