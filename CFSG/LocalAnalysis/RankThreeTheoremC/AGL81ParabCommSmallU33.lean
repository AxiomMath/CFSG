module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSmallAut
public import CFSG.HardMathSupport.Curtis.Proving.SmallOvergroupOrder
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSmall
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm

open CFSG.Open CFSG.AGLEmbedding CFSG.ComponentClassification CFSG.QuasithinUnique
open scoped commutatorElement

theorem mem_inner_of_odd {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (hA : Nat.card (MulAut X) = 2 * Nat.card X) {σ : MulAut X} (hσ : Odd (orderOf σ)) :
    σ ∈ OuterAutomorphisms.inner X := by
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    intro a b hab
    have hc : a⁻¹ * b ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut X => φ g) hab
      simp only [MulAut.conj_apply] at h1
      calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
        _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h1]
        _ = a⁻¹ * b * g := by group
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact hc
  have hI : Nat.card (OuterAutomorphisms.inner X) = Nat.card X := by
    rw [OuterAutomorphisms.inner, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj,
      Subgroup.card_top]
  have hO : Nat.card (OuterAutomorphisms.Outer X) = 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (OuterAutomorphisms.inner X)
    rw [hI, hA] at h
    have hX : 0 < Nat.card X := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hX h).symm
  set s : OuterAutomorphisms.Outer X := QuotientGroup.mk' (OuterAutomorphisms.inner X) σ with hs
  have hcop : Nat.Coprime (orderOf σ) 2 := Nat.coprime_two_right.mpr hσ
  have hord : orderOf s = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_map_dvd _ σ) (hO ▸ orderOf_dvd_natCard s)
  rw [orderOf_eq_one_iff, hs, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hord
  exact hord

section Parab

variable {A : Type} [Group A] {Y P B : Subgroup A}

abbrev quotSub (Y P : Subgroup A) : Subgroup (↥Y ⧸ Subgroup.center ↥Y) :=
  (P.subgroupOf Y).map (QuotientGroup.mk' (Subgroup.center ↥Y))

theorem quotAut_map_le (hBY : B ≤ Subgroup.normalizer (Y : Set A))
    (hBP : B ≤ Subgroup.normalizer (P : Set A)) (b : ↥B) :
    (quotSub Y P).map (quotAut hBY b).toMonoidHom ≤ quotSub Y P := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  refine ⟨Y.normalizerMonoidHom (Subgroup.inclusion hBY b) y, ?_, (quotAut_apply_mk hBY b y).symm⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Y.normalizerMonoidHom_apply_apply_coe]
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
  exact (Subgroup.mem_normalizer_iff.mp (hBP b.2) _).mp hy

theorem quotSub_ne_top (hpar : IsParabolicTwo Y P) (hne : P ≠ Y) : quotSub Y P ≠ ⊤ := by
  obtain ⟨hPY, T, hT, hTP⟩ := hpar
  intro htop
  apply hne
  refine le_antisymm hPY fun y hy => ?_
  have hmem : QuotientGroup.mk' (Subgroup.center ↥Y) ⟨y, hy⟩ ∈ quotSub Y P :=
    htop ▸ Subgroup.mem_top _
  obtain ⟨y', hy', hyy⟩ := hmem
  set z : ↥Y := y'⁻¹ * ⟨y, hy⟩ with hzdef
  have hz : z ∈ Subgroup.center ↥Y := (QuotientGroup.eq).mp hyy
  have key : ∀ w ∈ Y, (z : A) * w * (z : A)⁻¹ = w := fun w hw => by
    have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨w, hw⟩)
    simp only [Subgroup.coe_mul] at hc
    rw [← hc, mul_inv_cancel_right]
  have hzN : (z : A) ∈ Subgroup.normalizer (T : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      rw [key t (hT.1 ht)]
      exact ht
    · intro ht
      have htY : t ∈ Y := by
        have h1 : (z : A)⁻¹ * ((z : A) * t * (z : A)⁻¹) * z = t := by group
        rw [← h1]
        exact Y.mul_mem (Y.mul_mem (Y.inv_mem z.2) (hT.1 ht)) z.2
      rwa [key t htY] at ht
  have hzP : (z : A) ∈ P := hTP ⟨z.2, hzN⟩
  have hy'P : ((y' : ↥Y) : A) ∈ P := hy'
  have hyz : y = (y' : A) * (z : A) := by
    rw [hzdef, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [hyz]
  exact P.mul_mem hy'P hzP

theorem exists_sylow_le_quotSub (hpar : IsParabolicTwo Y P) :
    ∃ T : Subgroup (↥Y ⧸ Subgroup.center ↥Y), IsSylowTwoOf T ⊤ ∧ T ≤ quotSub Y P := by
  obtain ⟨-, T, ⟨hTY, hT2, hTi⟩, hTP⟩ := hpar
  refine ⟨(T.subgroupOf Y).map (QuotientGroup.mk' (Subgroup.center ↥Y)), ⟨le_top, ?_, ?_⟩, ?_⟩
  · exact (hT2.comap_of_injective Y.subtype Y.subtype_injective).map _
  · rw [show (((T.subgroupOf Y).map (QuotientGroup.mk' (Subgroup.center ↥Y))).subgroupOf ⊤).index =
        ((T.subgroupOf Y).map (QuotientGroup.mk' (Subgroup.center ↥Y))).index from
      Subgroup.relIndex_top_right _]
    intro h2
    exact hTi (h2.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)))
  · exact Subgroup.map_mono fun t ht => by
      rw [Subgroup.mem_subgroupOf] at ht ⊢
      exact hTP ⟨hTY ht, Subgroup.le_normalizer ht⟩

theorem conj_injective_of_center {X : Type} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  intro a b hab
  have hc : a⁻¹ * b ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut X => φ g) hab
    simp only [MulAut.conj_apply] at h1
    calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
      _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h1]
      _ = a⁻¹ * b * g := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc

theorem quotAut_comm_of_overgroup96 [Finite A] (hY : Open.IsQuasisimple ↥Y)
    (hpar : IsParabolicTwo Y P) (hne : P ≠ Y) (hBY : B ≤ Subgroup.normalizer (Y : Set A))
    (hBP : B ≤ Subgroup.normalizer (P : Set A)) (hB : IsPGroup 3 ↥B)
    (hA : Nat.card (MulAut (↥Y ⧸ Subgroup.center ↥Y)) = 2 * Nat.card (↥Y ⧸ Subgroup.center ↥Y))
    (hX2 : 2 ∣ Nat.card (↥Y ⧸ Subgroup.center ↥Y))
    (h96 : CFSG.HardMathSupport.Curtis.Proving.OvergroupOrder96 (↥Y ⧸ Subgroup.center ↥Y)) :
    ∀ a b : ↥B, quotAut hBY a * quotAut hBY b = quotAut hBY b * quotAut hBY a := by
  haveI : IsSimpleGroup (↥Y ⧸ Subgroup.center ↥Y) := hY.2
  have hZ : Subgroup.center (↥Y ⧸ Subgroup.center ↥Y) = ⊥ := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥Y hY
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (↥Y ⧸ Subgroup.center ↥Y)) with h | h
    · exact h
    · exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm hab
  have hinj := conj_injective_of_center hZ
  have hS : IsPGroup 3 ↥(quotAut hBY).range :=
    hB.of_surjective (quotAut hBY).rangeRestrict (quotAut hBY).rangeRestrict_surjective
  have hin : ∀ b : ↥B, ∃ x, MulAut.conj x = quotAut hBY b := fun b => by
    refine mem_inner_of_odd hZ hA ?_
    obtain ⟨k, hk⟩ := hS ⟨_, ⟨b, rfl⟩⟩
    have hdvd : orderOf (quotAut hBY b) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one
      (by simpa using congrArg Subtype.val hk)
    exact Odd.of_dvd_nat (Odd.pow (by decide)) hdvd
  choose x hx using hin
  set D : Subgroup (↥Y ⧸ Subgroup.center ↥Y) :=
    (quotAut hBY).range.comap (MulAut.conj : _ →* MulAut (↥Y ⧸ Subgroup.center ↥Y)) with hDdef
  set N := Subgroup.normalizer ((quotSub Y P : Subgroup (↥Y ⧸ Subgroup.center ↥Y)) :
    Set (↥Y ⧸ Subgroup.center ↥Y)) with hNdef
  have hDN : D ≤ N := by
    intro y hy
    obtain ⟨b, hb⟩ := hy
    have hle := quotAut_map_le hBY hBP b
    rw [hb] at hle
    have heq : (quotSub Y P).map (MulAut.conj y).toMonoidHom = quotSub Y P :=
      Subgroup.eq_of_le_of_card_ge hle
        (Subgroup.card_map_of_injective (MulAut.conj y).injective).ge
    rw [hNdef, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hle ⟨h, hh, rfl⟩
    · intro hh
      rw [← heq] at hh
      obtain ⟨h', hh', hhh⟩ := hh
      have : h' = h := (MulAut.conj y).injective hhh
      exact this ▸ hh'
  obtain ⟨T, hT, hTP⟩ := exists_sylow_le_quotSub hpar
  have hNtop : N ≠ ⊤ := by
    intro hN
    haveI hnorm : (quotSub Y P).Normal := Subgroup.normalizer_eq_top_iff.mp hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (quotSub Y P) with h | h
    · apply hT.2.2
      have hTb : T = ⊥ := le_bot_iff.mp (h ▸ hTP)
      rw [hTb, show ((⊥ : Subgroup (↥Y ⧸ Subgroup.center ↥Y)).subgroupOf ⊤).index =
        (⊥ : Subgroup (↥Y ⧸ Subgroup.center ↥Y)).index from Subgroup.relIndex_top_right _,
        Subgroup.index_bot]
      exact hX2
    · exact quotSub_ne_top hpar hne h
  have hN96 : Nat.card N ∣ 96 := h96 T N hT (hTP.trans Subgroup.le_normalizer) hNtop
  have hD3 : IsPGroup 3 ↥D := by
    rintro ⟨y, hy⟩
    obtain ⟨k, hk⟩ := hS ⟨_, hy⟩
    refine ⟨k, Subtype.ext (hinj ?_)⟩
    simpa using congrArg Subtype.val hk
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hD3
  have hDdvd : 3 ^ k ∣ 96 := hk ▸ (Subgroup.card_dvd_of_le hDN).trans hN96
  have hk1 : k ≤ 1 := by
    by_contra h
    have : 3 ^ 2 ∣ 96 := (pow_dvd_pow 3 (by omega)).trans hDdvd
    norm_num at this
  have hDc : ∀ u v : ↥D, u * v = v * u := by
    interval_cases k
    · haveI : Subsingleton ↥D := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
      exact fun u v => Subsingleton.elim _ _
    · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      haveI : IsCyclic ↥D := isCyclic_of_prime_card (by simpa using hk)
      exact fun u v => mul_comm' u v
  have hxD : ∀ b : ↥B, x b ∈ D := fun b => ⟨b, (hx b).symm⟩
  intro a b
  rw [← hx a, ← hx b, ← map_mul, ← map_mul]
  congr 1
  exact congrArg Subtype.val (hDc ⟨x a, hxD a⟩ ⟨x b, hxD b⟩)

end Parab

theorem parabCommGroupOn_psu33 :
    ParabCommGroupOn fun X _ => ∃ d : TauCeti.ValidLieTypeIndex,
      (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q) ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  intro A _ _ Y P B p hp hp2 hY _ hF hpar hne _ hB hBY hBP _
  left
  obtain ⟨d, ⟨q, hq, hd⟩, ⟨e⟩⟩ := hF
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hpq, hf⟩ := CFSG.AGLEmbedding.ParabHub.primePower_eq_of_card_eq Nat.prime_three hq
  have hM := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  rw [hpq, hf] at hM
  obtain ⟨eU⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (Or.inl ⟨by decide, hM⟩)
  have hAut : Nat.card (MulAut (↥Y ⧸ Subgroup.center ↥Y)) = 12096 :=
    CFSG.GH74.KGroups.U33.card_mulAut eU
  have hXc : Nat.card (↥Y ⧸ Subgroup.center ↥Y) = 6048 := by
    rw [Nat.card_congr eU.toEquiv, CFSG.GH74.KGroups.card_group _ CFSG.GH74.KGroups.U33.QP_ok,
      CFSG.GH74.KGroups.U33.QP_valid.2]
  refine commutator_centralizes_of_quotAut_comm hY hBY ?_
  by_cases hp3 : p = 3
  · subst hp3
    exact quotAut_comm_of_overgroup96 hY hpar hne hBY hBP hB (by rw [hAut, hXc])
      (by rw [hXc]; norm_num) (CFSG.HardMathSupport.Curtis.Proving.ordBound_psu_three_three hM)
  · have hS : IsPGroup p ↥(quotAut hBY).range :=
      hB.of_surjective (quotAut hBY).rangeRestrict (quotAut hBY).rangeRestrict_surjective
    have hc := isPGroup_commutative_of_dvd hp hS (by
      rw [hAut, show (12096 : ℕ) = 2 ^ 6 * 189 by norm_num]
      intro h3
      have hcop : Nat.Coprime (p ^ 3) (2 ^ 6) :=
        Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
      have h' := hcop.dvd_of_dvd_mul_left h3
      have hle := Nat.le_of_dvd (by norm_num) h'
      have hp5 : p ≤ 5 := by
        by_contra h
        have : 6 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
        omega
      have hp3' : 3 ≤ p := by have := hp.two_le; omega
      interval_cases p
      · exact hp3 rfl
      · norm_num at hp
      · norm_num at h')
    exact fun a b => hc _ ⟨a, rfl⟩ _ ⟨b, rfl⟩

theorem parabCommGroupOn_small :
    ParabCommGroupOn IsSmallTwoOrG2 := by
  refine ParabCommGroupOn.mono (parabCommGroupOn_or parabCommGroupOn_alternating
    (parabCommGroupOn_or parabCommGroupOn_psl27 parabCommGroupOn_psu33)) ?_
  rintro X _ (h | ⟨d, h7 | h3, e⟩)
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨d, h7, e⟩)
  · exact Or.inr (Or.inr ⟨d, h3, e⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm
