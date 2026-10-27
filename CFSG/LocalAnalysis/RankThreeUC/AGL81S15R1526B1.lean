module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526Defs
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0b
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
  KFactsPair
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem isNatSum_tiM_aux_commute_bar {L L' : Subgroup X} (hL : IsC2 L) (hL' : IsC2 L')
    (hne : L ≠ L') {l l' : X} (hl : l ∈ L) (hl' : l' ∈ L') :
    QuotientGroup.mk' (CFSG.pCore 2 X) l * QuotientGroup.mk' (CFSG.pCore 2 X) l' =
      QuotientGroup.mk' (CFSG.pCore 2 X) l' * QuotientGroup.mk' (CFSG.pCore 2 X) l := by
  have h := isC2_commute_of_ne hL hL' hne
  have h1 : ⁅QuotientGroup.mk' (CFSG.pCore 2 X) l, QuotientGroup.mk' (CFSG.pCore 2 X) l'⁆ ∈
      ⁅barO2 L, barO2 L'⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem _ hl)
      (Subgroup.mem_map_of_mem _ hl')
  rw [h, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

theorem isNatSum_tiM_aux_commute {T : Subgroup X} (hX : GNSetting X T) {L L' : Subgroup X}
    (hL : IsC2 L) (hL' : IsC2 L') (hne : L ≠ L') {l l' : X} (hl : l ∈ L) (hl' : l' ∈ L') :
    toStar T l * toStar T l' = toStar T l' * toStar T l := by
  have h1 := isNatSum_tiM_aux_commute_bar hL hL' hne hl hl'
  have h2 : ⁅l, l'⁆ ∈ CFSG.pCore 2 X := by
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 X), MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 h1
  have h3 : ⁅l, l'⁆ ∈ gnC T := pCore_le_gnC hX h2
  have h4 : toStar T ⁅l, l'⁆ = 1 := (QuotientGroup.eq_one_iff _).2 h3
  rw [map_commutatorElement] at h4
  exact commutatorElement_eq_one_iff_mul_comm.1 h4

theorem isNatSum_tiM_aux_normalizer {L L' : Subgroup X} (hL : IsC2 L) (hL' : IsC2 L')
    (hne : L ≠ L') : L ≤ Subgroup.normalizer (L' : Set X) := by
  intro l hl
  have hcomm : ∀ l' ∈ L', QuotientGroup.mk' (CFSG.pCore 2 X) (l * l' * l⁻¹) =
      QuotientGroup.mk' (CFSG.pCore 2 X) l' := by
    intro l' hl'
    rw [map_mul, map_mul, map_inv, isNatSum_tiM_aux_commute_bar hL hL' hne hl hl']
    group
  have hC2 : IsC2 (L'.map (MulAut.conj l).toMonoidHom) := liftOf_conj_aux4 hL' l
  have hbar : barO2 (L'.map (MulAut.conj l).toMonoidHom) = barO2 L' := by
    ext y
    constructor
    · rintro ⟨_, ⟨l', hl', rfl⟩, rfl⟩
      exact ⟨l', hl', (hcomm l' hl').symm⟩
    · rintro ⟨l', hl', rfl⟩
      exact ⟨l * l' * l⁻¹, ⟨l', hl', rfl⟩, hcomm l' hl'⟩
  exact mem_normalizer_iff_map_conj_eq.2 (isC2_eq_of_barO2_eq hC2 hL' hbar)

theorem isNatSum_tiM_aux_conj_commutator {T : Subgroup X} (L : Subgroup X) (m : X) :
    conjSub m ⁅L, gnV T⁆ = ⁅conjSub m L, gnV T⁆ := by
  haveI : (gnV T).Normal := Subgroup.normalClosure_normal
  have hVm : (gnV T).map (MulAut.conj m).toMonoidHom = gnV T := by
    have : m ∈ Subgroup.normalizer ((gnV T : Subgroup X) : Set X) := by
      rw [Subgroup.normalizer_eq_top_iff.2 ‹(gnV T).Normal›]
      exact Subgroup.mem_top m
    exact mem_normalizer_iff_map_conj_eq.1 this
  unfold conjSub
  rw [Subgroup.map_commutator, hVm]

theorem isNatSum_tiM_aux_centralizes {T : Subgroup X} (hX : GNSetting X T)
    {Ls : Subgroup (X ⧸ gnC T)} {L L' U' : Subgroup X} (hL : LiftOf T L Ls) (hL' : IsC2 L')
    (hne : L ≠ L') (hN' : IsNatSum L' U') (hU'V : U' ≤ gnV T)
    (hnL : L ≤ Subgroup.normalizer (U' : Set X)) : ∀ l ∈ L, ∀ u ∈ U', l * u * l⁻¹ = u := by
  have hab' := comm_of_le_gnV hX hU'V
  have hn' : L' ≤ Subgroup.normalizer (U' : Set X) := IsNatSum.fixed_eq_one_aux_le_normalizer hN'
  have hLcomm : ∀ l ∈ L, ∀ l' ∈ L', ∀ u ∈ U',
      l' * (l * u * l⁻¹) * l'⁻¹ = l * (l' * u * l'⁻¹) * l⁻¹ := by
    intro l hl l' hl' u hu
    have hx : toStar T l' ∈ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [← hL.2] at hy
      obtain ⟨l₀, hl₀, rfl⟩ := hy
      exact isNatSum_tiM_aux_commute hX hL.1 hL' hne hl₀ hl'
    exact commute_action_of_mem_cMLStar hL.2 hx hU'V l hl u hu
  let ψ : ↥L →* ↥(Subgroup.centralizer
      (((actOn L' U' hn').range : Subgroup (MulAut ↥U')) : Set (MulAut ↥U'))) :=
    (actOn L U' hnL).codRestrict _ (by
      intro l
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨l', rfl⟩
      ext u
      exact hLcomm l l.2 l' l'.2 u u.2)
  have hψ : ψ = 1 :=
    IsC2.hom_eq_one_of_card_dvd_six hL.1 ψ
      (IsNatSum.card_centralizer_dvd_six_of_comm hN' hab' hn')
  intro l hl u hu
  have h1 : (actOn L U' hnL ⟨l, hl⟩ : MulAut ↥U') = 1 := by
    have := congrArg (fun f => ((f ⟨l, hl⟩ : _) : MulAut ↥U')) hψ
    exact this
  have h2 := congrArg (fun f : MulAut ↥U' => ((f ⟨u, hu⟩ : _) : X)) h1
  exact h2

theorem isNatSum_tiM {T : Subgroup X} (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls) (hN : IsNatSum L ⁅L, gnV T⁆)
    (m : X) : conjSub m ⁅L, gnV T⁆ = ⁅L, gnV T⁆ ∨ ⁅L, gnV T⁆ ⊓ conjSub m ⁅L, gnV T⁆ = ⊥ := by
  haveI : (gnV T).Normal := Subgroup.normalClosure_normal
  have hUm := isNatSum_tiM_aux_conj_commutator (T := T) L m
  by_cases hLm : conjSub m L = L
  · left
    rw [hUm, hLm]
  · right
    have hC2' : IsC2 (conjSub m L) := liftOf_conj_aux4 hL.1 m
    have hne : L ≠ conjSub m L := fun h => hLm h.symm
    have hnormL := isNatSum_tiM_aux_normalizer hL.1 hC2' hne
    have hUV : (⁅L, gnV T⁆ : Subgroup X) ≤ gnV T := by
      rw [Subgroup.commutator_comm]; exact commutator_gnV_le T L
    have hU'V : conjSub m ⁅L, gnV T⁆ ≤ gnV T := by
      rw [hUm, Subgroup.commutator_comm]; exact commutator_gnV_le T _
    have hnL : L ≤ Subgroup.normalizer ((conjSub m ⁅L, gnV T⁆ : Subgroup X) : Set X) := by
      rw [hUm]
      intro l hl
      exact mem_normalizer_commutator (V := gnV T) (liftOf_conj_aux1 (hnormL hl))
    have hfix := isNatSum_tiM_aux_centralizes hX hL hC2' hne (IsNatSum.conj hN m) hU'V hnL
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    exact IsNatSum.fixed_eq_one_of_comm hN (comm_of_le_gnV hX hUV) hu.1
      (fun l hl => hfix l hl u hu.2)

end CFSG.LocalAnalysis.RankThreeUC.S15
