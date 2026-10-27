module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCoverMore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverLift

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup CFSG.QuasithinUnique.Id2519 CFSG.QuasithinUnique.I32
  CFSG.EvenSporadicStandard.Solomon78 CFSG.Blueprint.NativeSporadic
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem componentProduct_eq_of_noOther_out {L K : Subgroup H} {t u : H}
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hZ : center H = ⊥)
    (hB : BTheoremAt u) (hCt : centralizer ({t} : Set H) ≤ normalizer (L : Set H))
    (ht : t ∈ centralizer (L : Set H)) (ht2 : orderOf t = 2) (hut : u * t = t * u)
    (hu2 : orderOf u = 2)
    (hKL : K ≤ L) (hKq : CFSG.IsQuasisimple ↥K) (hKu : K ≤ centralizer ({u} : Set H))
    (hKn : (K.subgroupOf (centralizer ({u} : Set H) ⊓ centralizer ({t} : Set H))).Normal)
    (hΛs : Group.IsSolvable ↥(lam L K)) (hemb : NoFixedEmbeds ↥K ↥(lam L K))
    (hex : NoOtherComponent K t u) : K = componentProduct K u := by
  classical
  set X : Subgroup H := centralizer ({u} : Set H) with hX
  have ht2' : t * t = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 ht2.dvd
  have htK : t ∈ centralizer (K : Set H) :=
    mem_centralizer_iff.2 fun k hk => mem_centralizer_iff.1 ht k (hKL hk)
  have htH : t ∈ X := mem_centralizer_singleton_iff.2 hut.symm
  have hBt : K ≤ centralizer ({t} : Set H) := fun k hk =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht k (hKL hk))
  have hKM : IsCompIn K X := by
    rcases layer_dichotomy_of_quasisimple_Q hkp hZ htH ht2 hu2 (B := K) hKu hBt hKq hKn with
      ⟨hA, -⟩ | ⟨J, hJ, hJne, hJeq, -⟩
    · set M : Subgroup H := ⨆ g ∈ oddLayer X, CFSG.conjugate K g with hMdef
      have hMcomp : IsCompIn M X := hB M hA
      have hKleM : K ≤ M :=
        le_iSup₂_of_le (f := fun g (_ : g ∈ oddLayer X) => CFSG.conjugate K g) 1 (one_mem _)
          (by rw [conjugate_one])
      by_cases hMK : M = K
      · rw [hMK] at hMcomp
        exact hMcomp
      · exact (hex M hMcomp (le_sup_of_le_left hKleM) hMK).elim
    · exfalso
      have hJcomp : IsCompIn J X := hB J hJ
      have hKJ : K ≤ J ⊔ CFSG.conjugate J t := by
        rw [← hJeq]
        exact le_iSup₂_of_le (f := fun g (_ : g ∈ oddLayer X) => CFSG.conjugate K g) 1 (one_mem _)
          (by rw [conjugate_one])
      have hJK : J ≠ K := by
        intro hJK
        apply hJne
        rw [hJK, conjugate_eq_of_mem_centralizer htK]
      exact hex J hJcomp hKJ hJK
  have hn : (K.subgroupOf X).Normal :=
    normal_of_component_emb hKM htH htK ht2' hCt hΛs hemb
  apply le_antisymm
  · exact le_sSup ⟨hKM.1, hn, ⟨MulEquiv.refl _⟩⟩
  · refine sSup_le ?_
    rintro N ⟨hNH, hNn, ⟨e⟩⟩
    by_cases hNK : N = K
    · exact hNK.le
    · exfalso
      have hNq : CFSG.IsQuasisimple ↥N := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hKq
      have hNcomp : IsCompIn N X := isCompIn_of_normal hNH hNq hNn
      have hcentK : N ≤ centralizer (K : Set H) := fun a ha =>
        mem_centralizer_iff.2 fun b hb => (hNcomp.commute_of_ne hKM hNK a ha b hb).symm
      have htN : t ∈ normalizer (N : Set H) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).1 hNn htH
      exact false_of_second_copy_emb ht2' hCt htK hKq hΛs hemb hcentK e htN


omit [Finite H] in
theorem bar_le_fix_of_commute {L K : Subgroup H} {u : H} (huN : u ∈ normalizer (L : Set H))
    (hKu : ∀ k ∈ K, k * u = u * k) :
    Cover.bar (K.subgroupOf L) ≤ fixSubgroup (normalizerAction L ⟨u, huN⟩) := by
  set ν := normalizerAction L ⟨u, huN⟩ with hν
  intro y hy
  obtain ⟨k, hk, rfl⟩ := Cover.mem_bar.1 hy
  have hkK : (k : H) ∈ K := Subgroup.mem_subgroupOf.1 hk
  show ν (k : ↥L ⧸ center ↥L) = k
  rw [hν, Closing.act_mk]
  congr 1
  refine Subtype.ext ?_
  show u * (k : H) * u⁻¹ = k
  calc u * (k : H) * u⁻¹ = ((k : H) * u) * u⁻¹ := by rw [hKu _ hkK]
    _ = k := by group

theorem bar_eq_fix_of_outer (hF : Fi24OuterFixed) {L K : Subgroup H} {u : H}
    (hq : CFSG.IsQuasisimple ↥L) (hodd : Odd (Nat.card ↥(center ↥L)))
    (hY : IsSporadic (↥L ⧸ center ↥L) .Fi24Prime) (huN : u ∈ normalizer (L : Set H))
    (hu2 : orderOf u = 2) (hunot : u ∉ L ⊔ centralizer (L : Set H)) (hKL : K ≤ L)
    (hKq : CFSG.IsQuasisimple ↥K) (hKu : ∀ k ∈ K, k * u = u * k)
    (hcard : 4089470473293004800 ≤ Nat.card (↥K ⧸ CFSG.oddCore ↥K)) :
    Cover.bar (K.subgroupOf L) = fixSubgroup (normalizerAction L ⟨u, huN⟩) := by
  have hLperf : commutator ↥L = ⊤ := Group.isPerfect_def.1 hq.1
  have hu1 : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two hu2
  set ν := normalizerAction L ⟨u, huN⟩ with hν
  have hνν : ν * ν = 1 := Closing.act_mul_self huN hu1
  have hout : ¬ ∃ g, ν = MulAut.conj g := by
    rintro ⟨g, hg⟩
    exact hunot ((normalizerAction_mem_range_conj_iff hLperf ⟨u, huN⟩).1 ⟨g, hg.symm⟩)
  have hK' := commutator_subgroupOf_eq_self hKL hKq
  have hB : Cover.bar (K.subgroupOf L) ≤ fixSubgroup ν := bar_le_fix_of_commute huN hKu
  have hperf : ⁅Cover.bar (K.subgroupOf L), Cover.bar (K.subgroupOf L)⁆ =
      Cover.bar (K.subgroupOf L) := by
    unfold Cover.bar
    rw [← Subgroup.map_commutator, hK']
  have hcard' : 4089470473293004800 ≤ Nat.card (Cover.bar (K.subgroupOf L)) :=
    hcard.trans (card_quotient_oddCore_le_bar hodd hKL)
  exact hF _ hY ν hνν hout _ hB hperf hcard'

omit [Finite H] in
theorem exists_mul_of_comm_outer {L K : Subgroup H} {u : H} (huN : u ∈ normalizer (L : Set H))
    (hbar : Cover.bar (K.subgroupOf L) = fixSubgroup (normalizerAction L ⟨u, huN⟩)) {x : H}
    (hxL : x ∈ L) (hxu : u * x = x * u) :
    ∃ k : ↥L, k ∈ K.subgroupOf L ∧ ∃ z ∈ center ↥L, (⟨x, hxL⟩ : ↥L) = k * z := by
  have hfix : normalizerAction L ⟨u, huN⟩ ((⟨x, hxL⟩ : ↥L) : ↥L ⧸ center ↥L) =
      ((⟨x, hxL⟩ : ↥L) : ↥L ⧸ center ↥L) := by
    rw [Closing.act_mk huN]
    congr 1
    refine Subtype.ext ?_
    show u * x * u⁻¹ = x
    rw [hxu]
    group
  have hmem : ((⟨x, hxL⟩ : ↥L) : ↥L ⧸ center ↥L) ∈ Cover.bar (K.subgroupOf L) := by
    rw [hbar]
    exact hfix
  obtain ⟨k, hk, z, hz, hkz⟩ := Cover.mem_bar_iff_exists_mem_mul.1 hmem
  exact ⟨k, hk, z, hz, hkz⟩

omit [Finite H] in
theorem characteristic_of_outer {L K : Subgroup H} {u : H} (huN : u ∈ normalizer (L : Set H))
    (hKL : K ≤ L) (hKq : CFSG.IsQuasisimple ↥K) (hKu : ∀ k ∈ K, k * u = u * k)
    (hbar : Cover.bar (K.subgroupOf L) = fixSubgroup (normalizerAction L ⟨u, huN⟩)) :
    (K.subgroupOf (L ⊓ centralizer ({u} : Set H))).Characteristic := by
  set C : Subgroup H := L ⊓ centralizer ({u} : Set H) with hCdef
  have hKC : K ≤ C := fun k hk => ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  have hperf := commutator_subgroupOf_eq_self hKC hKq
  have heq : K.subgroupOf C = commutator ↥C := by
    apply le_antisymm
    · calc K.subgroupOf C = ⁅K.subgroupOf C, K.subgroupOf C⁆ := hperf.symm
        _ ≤ ⁅(⊤ : Subgroup ↥C), (⊤ : Subgroup ↥C)⁆ := Subgroup.commutator_mono le_top le_top
        _ = commutator ↥C := (_root_.commutator_def _).symm
    · rw [_root_.commutator_def]
      refine Subgroup.commutator_le.2 fun x _ y _ => ?_
      have hx' : (⟨(x : H), x.2.1⟩ : ↥L) ∈ K.subgroupOf L ⊔ center ↥L := by
        obtain ⟨k, hk, z, hz, hkz⟩ := exists_mul_of_comm_outer huN hbar x.2.1
          (mem_centralizer_singleton_iff.1 x.2.2).symm
        rw [hkz]
        exact Subgroup.mul_mem_sup hk hz
      have hy' : (⟨(y : H), y.2.1⟩ : ↥L) ∈ K.subgroupOf L ⊔ center ↥L := by
        obtain ⟨k, hk, z, hz, hkz⟩ := exists_mul_of_comm_outer huN hbar y.2.1
          (mem_centralizer_singleton_iff.1 y.2.2).symm
        rw [hkz]
        exact Subgroup.mul_mem_sup hk hz
      have h1 := Subgroup.commutator_mem_commutator hx' hy'
      have h2 : ⁅(⟨(x : H), x.2.1⟩ : ↥L), (⟨(y : H), y.2.1⟩ : ↥L)⁆ ∈ K.subgroupOf L :=
        Cover.commutator_self_le _ (Cover.commutator_sup_center_le _ h1)
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_subgroupOf.1 h2
  rw [heq]
  infer_instance

omit [Finite H] in
theorem normal_of_outer {L K : Subgroup H} {t u : H} (huN : u ∈ normalizer (L : Set H))
    (hKL : K ≤ L) (hKq : CFSG.IsQuasisimple ↥K) (hKu : ∀ k ∈ K, k * u = u * k)
    (hbar : Cover.bar (K.subgroupOf L) = fixSubgroup (normalizerAction L ⟨u, huN⟩))
    (ht : t ∈ centralizer (L : Set H)) (hCt : centralizer ({t} : Set H) ≤ normalizer (L : Set H)) :
    (K.subgroupOf (centralizer ({u} : Set H) ⊓ centralizer ({t} : Set H))).Normal :=
  normal_subgroupOf_of_characteristic ht hCt
    (fun k hk => ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩)
    (characteristic_of_outer huN hKL hKq hKu hbar)

end CFSG.EvenSporadicStandard.Induction.Fi.V3
