module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabRealThreeModels
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycThreeMain
public import CFSG.RankThree.PartTwo.Sec4.Census.Open43
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ONanBlockInnerParabolic
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltCentralExtThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.ParabRealThree
open CFSG.RankThree.PartTwo.Sec4.Census (TripleCoverAlternating TripleCoverLie
  TripleCoverLieIndex)
open scoped commutatorElement

theorem perm_six_exists_inv_of_pow_three : ∀ σ : Equiv.Perm (Fin 6), σ ^ 3 = 1 →
    ∃ τ : Equiv.Perm (Fin 6), Equiv.Perm.sign τ = 1 ∧ τ * σ * τ⁻¹ = σ⁻¹ := by
  decide +kernel

theorem exists_pow_three_eq_one_of_real {X Y : Type*} [Group X] [Group Y] (ψ : X →* Y)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center X) {P : Subgroup X}
    (hkP : ψ.ker ≤ P) {g w : Y} (hg : g ∈ P.map ψ) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    (hw : w * g * w⁻¹ = g⁻¹) : ∃ x ∈ P, x ^ 3 = 1 ∧ ψ x ≠ 1 := by
  obtain ⟨x, hx, hx3⟩ := AltCentralExtThree.exists_lift_pow_three_eq_one ψ hψ hker hg3 hw
  obtain ⟨p, hp, hpg⟩ := hg
  refine ⟨x, ?_, hx3, hx ▸ hg1⟩
  have hk : p⁻¹ * x ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpg, hx, inv_mul_cancel]
  simpa using mul_mem hp (hkP hk)

theorem isElemAbelian_closure_pair_of_commute {X : Type*} [Group X] {r : ℕ} {x y : X}
    (hxr : x ^ r = 1) (hyr : y ^ r = 1) (hxy : Commute x y) :
    IsElemAbelian r (Subgroup.closure ({x, y} : Set X)) := by
  have hcomm : ({x, y} : Set X).Pairwise Commute := by
    intro u hu v hv _
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    exacts [Commute.refl _, hxy, hxy.symm, Commute.refl _]
  have := Subgroup.isMulCommutative_closure hcomm
  refine ⟨this, fun g hg => ?_⟩
  induction hg using Subgroup.closure_induction with
  | mem u hu =>
    rcases hu with rfl | rfl
    exacts [hxr, hyr]
  | one => exact one_pow r
  | mul u v hu hv ihu ihv =>
    have huv : Commute u v :=
      congrArg Subtype.val (this.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
    rw [huv.mul_pow, ihu, ihv, one_mul]
  | inv u hu ihu => rw [inv_pow, ihu, inv_one]

theorem card_closure_pair_of_commute {X : Type*} [Group X] {p : ℕ} (hp : p.Prime) {a b : X}
    (hab : Commute a b) (ha : orderOf a = p) (hb : orderOf b = p)
    (hind : b ∉ Subgroup.zpowers a) :
    Nat.card ↥(Subgroup.closure ({a, b} : Set X)) = p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, Commute x y := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact hab.zpow_zpow m n
  have hcb : Nat.card ↥(Subgroup.zpowers b) = p := by rw [Nat.card_zpowers, hb]
  have hca : Nat.card ↥(Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, ha]
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    have : Fact (Nat.card ↥(Subgroup.zpowers b)).Prime := ⟨by rw [hcb]; exact hp⟩
    have h := Subgroup.eq_bot_or_eq_top_of_prime_card
      ((Subgroup.zpowers a ⊓ Subgroup.zpowers b).subgroupOf (Subgroup.zpowers b))
    rcases h with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      have h' := disjoint_iff.1 h
      rwa [inf_assoc, inf_idem] at h'
    · exfalso
      apply hind
      have hbb : (⟨b, Subgroup.mem_zpowers b⟩ : ↥(Subgroup.zpowers b)) ∈
          (Subgroup.zpowers a ⊓ Subgroup.zpowers b).subgroupOf (Subgroup.zpowers b) := by
        rw [h]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 hbb).1
  let φ : Subgroup.zpowers a × Subgroup.zpowers b →* X :=
    MonoidHom.noncommCoprod (Subgroup.zpowers a).subtype (Subgroup.zpowers b).subtype
      fun x y => hcomm x x.2 y y.2
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    have hxy' : (x : X) * y = 1 := hxy
    have hx : (x : X) = (y : X)⁻¹ := eq_inv_of_mul_eq_one_left hxy'
    have hmem : (x : X) ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b :=
      ⟨x.2, by rw [hx]; exact (Subgroup.zpowers b).inv_mem y.2⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hy : (y : X) = 1 := inv_eq_one.1 (hx.symm.trans hmem)
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hy)
  have hrange : φ.range = Subgroup.closure ({a, b} : Set X) := by
    have h1 : φ.range = (Subgroup.zpowers a).subtype.range ⊔ (Subgroup.zpowers b).subtype.range :=
      MonoidHom.noncommCoprod_range _ _ _
    rw [h1, Subgroup.range_subtype, Subgroup.range_subtype, Set.insert_eq,
      Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod, hca, hcb,
    sq]

variable {G : Type} [Group G]

theorem center_le_blockPL_of_nineThreeTwo {M S L : Subgroup G} (h2 : NineThreeTwo M S L) :
    Subgroup.center ↥(barM M L) ≤ (blockPL M S L).subgroupOf (barM M L) := by
  obtain ⟨-, ⟨-, T, hT, hNT⟩, -⟩ := h2
  intro z hz
  rw [Subgroup.mem_subgroupOf]
  refine hNT ⟨z.2, Subgroup.centralizer_le_normalizer _ ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨t, hT.1 ht⟩)

theorem isQuasisimple_of_open' {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨h1⟩, h2, ?_⟩
  by_contra hc
  push Not at hc
  have hZ : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (Subgroup.center Q) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc _ _
  rw [h1] at hZ
  have hall : ∀ q : Q ⧸ Subgroup.center Q, q = 1 := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact (QuotientGroup.eq_one_iff x).mpr (hZ (Subgroup.mem_top x))
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  exact hab ((hall a).trans (hall b).symm)

variable [Finite G]

theorem exists_real_three_of_nineThreeTwo (hTA : TripleCoverAlternating) (hTL : TripleCoverLie)
    {M S L : Subgroup G} (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (h2 : NineThreeTwo M S L)
    (h3 : 3 ∣ Nat.card (Subgroup.center ↥(barM M L))) :
    ∃ g ∈ ((blockPL M S L).subgroupOf (barM M L)).map
        (QuotientGroup.mk' (Subgroup.center ↥(barM M L))), g ^ 3 = 1 ∧ g ≠ 1 ∧
      ∃ w, w * g * w⁻¹ = g⁻¹ := by
  obtain ⟨hcl, T, J, hT, hNJ, hJN, -, hJ⟩ := BlockCyc.nineThreeTwo_parabolic hA hL hS h2
  rw [← hJ]
  have hq₀ := hL.component.2.2
  have hq : CFSG.IsQuasisimple ↥(barM M L) := isQuasisimple_of_open' hq₀
  obtain ⟨T', hT'⟩ := exists_sylow_of_isSylowTwoOf_top hT
  rcases hcl with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · obtain ⟨g, hgJ, hg3, hg1, w, -, hw⟩ :=
      realThreeOver_lieIndex d hd e T' J (hT' ▸ hNJ) (hT' ▸ hJN)
    exact ⟨g, hgJ, hg3, hg1, w, hw⟩
  · have h67 := hTA n ↥(barM M L) (by omega) ⟨hq, h3, ⟨e⟩⟩
    obtain rfl : n = 6 := by omega
    have hTJ : T ≤ J := le_trans (Subgroup.le_normalizer) hNJ
    have hJT : J ≠ T := fun h => hJN (by
      rw [h]
      exact le_antisymm Subgroup.le_normalizer (h ▸ hNJ))
    have h3J : 3 ∣ Nat.card J :=
      ParabHub.ThreeDvdOver.of_mulEquiv e.symm ParabHub.threeDvdOver_alt_six T J hT hTJ hJT
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3J
    have hg3 : (g : ↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← hg, pow_orderOf_eq_one, Subgroup.coe_one]
    have hg1 : (g : ↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ≠ 1 := by
      intro h1
      have : g = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hg
      omega
    set σ : alternatingGroup (Fin 6) := e (g : ↥(barM M L) ⧸ Subgroup.center ↥(barM M L))
      with hσ
    have hσ3 : σ ^ 3 = 1 := by rw [hσ, ← map_pow, hg3, map_one]
    obtain ⟨τ, hτs, hτ⟩ := perm_six_exists_inv_of_pow_three (σ : Equiv.Perm (Fin 6))
      (by rw [← Subgroup.coe_pow, hσ3]; rfl)
    set τ' : alternatingGroup (Fin 6) := ⟨τ, by rw [Equiv.Perm.mem_alternatingGroup]; exact hτs⟩
    have hτ' : τ' * σ * τ'⁻¹ = σ⁻¹ := Subtype.ext hτ
    refine ⟨g, g.2, hg3, hg1, e.symm τ', e.injective ?_⟩
    rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply, ← hσ, hτ']
  · exfalso
    have h := hTL d ↥(barM M L) ⟨hq, h3, ⟨e⟩⟩
    obtain ⟨dd, hv⟩ := d
    rcases hd with ⟨q, hq7, rfl⟩ | ⟨q, hq3, rfl⟩
    · simp only [TripleCoverLieIndex] at h
      omega
    · simp only [TripleCoverLieIndex] at h
      omega

theorem exists_noncentral_three_of_nineThreeTwo (hTA : TripleCoverAlternating)
    (hTL : TripleCoverLie)
    {M S L : Subgroup G} (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (h2 : NineThreeTwo M S L)
    (h3 : 3 ∣ Nat.card (Subgroup.center ↥(barM M L))) :
    ∃ y ∈ blockPL M S L, y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨g, hgJ, hg3, hg1, w, hw⟩ := exists_real_three_of_nineThreeTwo hTA hTL hA hL hS h2 h3
  obtain ⟨x, hxP, hx3, hx1⟩ := exists_pow_three_eq_one_of_real
    (QuotientGroup.mk' (Subgroup.center ↥(barM M L))) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk'])
    (by rw [QuotientGroup.ker_mk']; exact center_le_blockPL_of_nineThreeTwo h2) hgJ hg3 hg1 hw
  refine ⟨(x : ↥M ⧸ CFSG.pCore 2 ↥M), Subgroup.mem_subgroupOf.mp hxP, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, hx3, Subgroup.coe_one]
  · intro hxC
    apply hx1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC l l.2)

theorem kFactBlockAltFiveSectionParabolic_of (hTA : TripleCoverAlternating)
    (hTL : TripleCoverLie) :
    KFactBlockAltFiveSectionParabolic := by
  intro G _ _ M S L U _ hA hL _ hS _ h2 h3 _ _ _ _ _ _
  refine Or.inr ?_
  obtain ⟨y, hyP, hy3, hyC⟩ := exists_noncentral_three_of_nineThreeTwo hTA hTL hA hL hS h2 h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
  set z' : ↥M ⧸ CFSG.pCore 2 ↥M := ((z : ↥(barM M L)) : ↥M ⧸ CFSG.pCore 2 ↥M) with hz'
  have hPL : blockPL M S L ≤ barM M L := h2.2.1.1
  have hzP : z' ∈ blockPL M S L :=
    Subgroup.mem_subgroupOf.mp (center_le_blockPL_of_nineThreeTwo h2 z.2)
  have hzC : z' ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨t, ht⟩)
  have hz3 : orderOf z' = 3 := by
    rw [hz', Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hy1 : y ≠ 1 := fun h1 => hyC (h1 ▸ Subgroup.one_mem _)
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hcomm : Commute z' y := (Subgroup.mem_centralizer_iff.mp hzC y (hPL hyP)).symm
  have hind : y ∉ Subgroup.zpowers z' := fun h =>
    hyC ((Subgroup.zpowers_le.mpr hzC) h)
  refine ⟨Subgroup.closure {z', y}, ?_,
    isElemAbelian_closure_pair_of_commute (hz3 ▸ pow_orderOf_eq_one z') hy3 hcomm,
    card_closure_pair_of_commute Nat.prime_three hcomm hz3 hyo hind, ?_⟩
  · rw [Subgroup.closure_le]
    intro t ht
    rcases ht with rfl | rfl
    exacts [hzP, hyP]
  · intro hle
    exact hyC (hle (Subgroup.subset_closure (by simp)))

end CFSG.AGLEmbeddingD2
