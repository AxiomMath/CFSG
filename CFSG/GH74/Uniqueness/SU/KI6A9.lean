module

public import CFSG.GH74.Uniqueness.SU.KI6A
public import CFSG.GH74.Uniqueness.SU.KI6BGroup
public import CFSG.GH74.Uniqueness.SU.KI6A9Stab
public import CFSG.GH74.Uniqueness.SU.SU13TB3Gen
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Glue

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup CFSG CFSG.Blueprint CFSG.ProperTwoGeneratedCore CFSG.GH74.Uniqueness.SU.K.R3
open CFSG.ProperTwoGeneratedCore.Lemma37 CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

variable {H : Type} [Group H] [Finite H] {T : Sylow 2 H} {H₀ : Subgroup H}

theorem Cfg.mem_of_conj_mem (h : Cfg H T H₀) {t : H} (htc : t ∈ center H) (ht2 : orderOf t = 2)
    {m y : H} (hy : y ∈ H₀) (hy2 : orderOf y = 2) (hyt : y ≠ t) (hm : m⁻¹ * y * m ∈ H₀) :
    m ∈ H₀ := by
  have hy2' : y * y = 1 := mul_self_eq_one_of_orderOf_two hy2
  have ht2' : t * t = 1 := mul_self_eq_one_of_orderOf_two ht2
  have hy1 : y ≠ 1 := by intro h1; rw [h1, orderOf_one] at hy2; omega
  have hnot : t ∉ zpowers y := by
    intro hmem
    rcases LemmaYAux.eq_one_or_eq_of_mem_zpowers hy2' hmem with h1 | h1
    · rw [h1, orderOf_one] at ht2; omega
    · exact hyt h1.symm
  have hcomm : y * t = t * y := Subgroup.mem_center_iff.mp htc y
  obtain ⟨hel, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two (a := y) (y := t)
    (by rw [pow_two]; exact hy2') (by rw [pow_two]; exact ht2') hy1 hnot hcomm
  have hQH : zpowers y ⊔ zpowers t ≤ H₀ :=
    sup_le (Subgroup.zpowers_le.mpr hy) (Subgroup.zpowers_le.mpr (h.center_le htc))
  have hrank : 2 ≤ Open.pRank 2 (zpowers y ⊔ zpowers t) :=
    SU1.le_pRank (p := 2) (by norm_num) le_rfl hel (k := 2) (by simp [hcard])
  have hQ : IsPGroup 2 ↥(zpowers y ⊔ zpowers t) := fun g =>
    ⟨1, Subtype.ext (by simpa using hel.2 g g.2)⟩
  refine transporter_mem T H₀ 2 h.sylow_le h.gamma _ hQ hQH hrank m ?_
  rw [Subgroup.conjBy, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
  · simpa [MulAut.conj_apply] using hm
  · have : m⁻¹ * t * m = t := by
      rw [Subgroup.mem_center_iff.mp htc m⁻¹]; group
    simpa [MulAut.conj_apply, this] using h.center_le htc


section TwoA9

open Equiv in
def c458 : alternatingGroup (Fin 9) :=
  ⟨swap 4 5 * swap 4 8, Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem isThreeCycle_c458 : (c458 : Equiv.Perm (Fin 9)).IsThreeCycle := by
  unfold c458
  exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem commute_genA_c458 : Commute aNineSylowGenA c458 := by
  refine Subtype.ext ?_
  unfold c458 aNineSylowGenA
  decide

theorem c458_apply_eight : (c458 : Equiv.Perm (Fin 9)) 8 ≠ 8 := by
  unfold c458
  decide

end TwoA9

theorem Cfg.ki6TwoA9 (h : Cfg H T H₀) {L : Subgroup H} (hL : IsComponent L)
    (hrank : 2 ≤ Open.pRank 2 L) (hA : IsTwoAlt ↥L 9) :
    (L = ⊤ ∧ IsTwoAlt ↥L 9 ∧ IsTwoAlt ↥H₀ 8) ∧ IsCyclic ↥(center ↥(T : Subgroup H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLn, hLnot, hCle, hrk, TL, hTL, hΓL, hDlt⟩ := h.rank2_component hL hrank
  have := hLn
  obtain ⟨t, htc, ht2⟩ := exists_central_involution h.odd h.cen
  have ht1 : t ≠ 1 := by intro h1; rw [h1, orderOf_one] at ht2; omega
  have ht2' : t * t = 1 := mul_self_eq_one_of_orderOf_two ht2
  have hZp := h.isPGroup_center_component hL
  have hA' := hA
  obtain ⟨hq, hfin, hcard, ⟨e₀⟩⟩ := hA
  have hZne : center ↥L ≠ ⊥ := by intro hc; rw [hc] at hcard; simp at hcard
  have htL := central_involution_mem_component htc ht2 hZp hZne hrk
  have hJ : IsTwoANine ↥L := ⟨hq.1, hcard, ⟨e₀⟩⟩
  have hzb : ((zbar ↥L : ↥L) : H) = t := coe_zbar_eq_of_mem_center hJ htL htc ht1
  obtain ⟨e, he⟩ := exists_mulEquiv_proj_mem_of_sylow_le (J := L) (B := (T : Subgroup H)) hJ T
    le_rfl
  have hsylH : ∀ x : ↥L, proj e x ∈ ANineSylow → (x : H) ∈ H₀ := fun x hx => h.sylow_le (he x hx)
  have hnorm : ∀ D : Subgroup H, D ≤ H₀ → 2 ≤ CFSG.Open.pRank 2 D →
      normalizer (D : Set H) ≤ H₀ := fun D hD hr =>
    two_generated_core_subgroup_normalizer_le T H₀ h.sylow_le h.gamma D hD hr
  have hK := map_subgroupOf_eq_stabilizer_eight hJ e hsylH hnorm hLnot
  have hC1 : ∀ k ∈ (T : Subgroup H), k ∈ centralizer (L : Set H) → k = 1 ∨ k = t := by
    intro k hkT hkC
    by_contra hcon
    push Not at hcon
    obtain ⟨hk1, hkt⟩ := hcon
    obtain ⟨x, hx⟩ := proj_surjective e aNineSylowGenA
    have hxA : ((proj e x : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9)).cycleType = {2, 2} := by
      rw [hx]; exact cycleType_aNineSylowGenA
    have hxT : (x : H) ∈ (T : Subgroup H) := he x (hx ▸ aNineSylowGenA_mem)
    have hxx : (x : H) * x = t := by
      have := hJ.sq_eq_zbar_of_cycleType_two_two e hxA
      have h' := congrArg Subtype.val this
      rwa [Subgroup.coe_pow, hzb, sq] at h'
    have hx4 : orderOf (x : H) = 4 := by
      rw [Subgroup.orderOf_coe]; exact hJ.orderOf_eq_four_of_cycleType_two_two e hxA
    have hcommxk : (x : H) * k = k * x := Subgroup.mem_centralizer_iff.mp hkC (x : H) x.2
    have hknot : k ∉ zpowers t := by
      intro hmem
      rcases LemmaYAux.eq_one_or_eq_of_mem_zpowers ht2' hmem with h1 | h1
      · exact hk1 h1
      · exact hkt h1
    have hk2 : ∃ n : ℕ, k ^ (2 ^ n) = 1 := by
      obtain ⟨n, hn⟩ := T.isPGroup' ⟨k, hkT⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    have hint : ∀ g : H, g ∈ zpowers (x : H) → g ∈ zpowers k → g ∈ zpowers t := by
      intro g hg1 hg2
      have hgL : g ∈ L := Subgroup.zpowers_le.mpr x.2 hg1
      have hgC : g ∈ centralizer (L : Set H) := Subgroup.zpowers_le.mpr hkC hg2
      have hgZ : (⟨g, hgL⟩ : ↥L) ∈ center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgC (y : H) y.2)
      rcases (hJ.mem_center_iff.mp hgZ) with h1 | h1
      · have : g = 1 := congrArg Subtype.val h1
        rw [this]; exact one_mem _
      · have : g = t := by rw [← hzb]; exact congrArg Subtype.val h1
        rw [this]; exact Subgroup.mem_zpowers t
    have hrankD := two_le_pRank_sup_zpowers ht2' hx4 hxx hcommxk hknot hk2 hint
    have hDT : zpowers (x : H) ⊔ zpowers k ≤ (T : Subgroup H) :=
      sup_le (Subgroup.zpowers_le.mpr hxT) (Subgroup.zpowers_le.mpr hkT)
    have hNle := hnorm _ (hDT.trans h.sylow_le) hrankD
    obtain ⟨g, ⟨hgc, hg3⟩, -⟩ := hJ.existsUnique_lift_of_isThreeCycle e isThreeCycle_c458
    have hg3' : g ^ 3 = 1 := by rw [← hg3]; exact pow_orderOf_eq_one g
    have hcomm : Commute x g := hJ.commute_of_pow_three_eq_one e hg3'
      (by rw [hx, hgc]; exact commute_genA_c458)
    have hgx : (x : H) * g = g * x := congrArg Subtype.val hcomm.eq
    have hgk : (g : H) * k = k * g := Subgroup.mem_centralizer_iff.mp hkC (g : H) g.2
    have hDc : zpowers (x : H) ⊔ zpowers k ≤ centralizer ({(g : H)} : Set H) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]; exact hgx
      · rw [Subgroup.mem_centralizer_singleton_iff]; exact hgk.symm
    have hgN : (g : H) ∈ normalizer ((zpowers (x : H) ⊔ zpowers k : Subgroup H) : Set H) := by
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact Subgroup.mem_centralizer_singleton_iff.mp (hDc hd)
    have hgH₀ : (g : H) ∈ H₀ := hNle hgN
    have hgmem : proj e g ∈ (H₀.subgroupOf L).map (proj e) :=
      ⟨g, Subgroup.mem_subgroupOf.mpr hgH₀, rfl⟩
    rw [hK, hgc] at hgmem
    exact c458_apply_eight hgmem
  have hs : GlueSetting L H₀ t :=
    { normal := hLn
      isTwoANine := hJ
      mem := htL
      mem_center := htc
      ne_one := ht1
      oddCore_eq_bot := h.odd
      not_le := hLnot
      exists_sylow_le := ⟨T, h.sylow_le⟩
      normalizer_le := hnorm
      mem_of_conj_mem := fun {m y} hy hy2 hyt hm => h.mem_of_conj_mem htc ht2 hy hy2 hyt hm
      exists_sylow_centralizer := ⟨T, hC1⟩ }
  have hLtop : L = ⊤ := hs.eq_top
  have hH₀L : H₀ ≤ L := by rw [hLtop]; exact le_top
  have hzH₀ : ((zbar ↥L : ↥L) : H) ∈ H₀ := by rw [hzb]; exact h.center_le htc
  have hB : H₀.subgroupOf L =
      (MulAction.stabilizer (alternatingGroup (Fin 9)) (8 : Fin 9)).comap (proj e) := by
    ext y
    constructor
    · intro hy
      have hy' : proj e y ∈ (H₀.subgroupOf L).map (proj e) := ⟨y, hy, rfl⟩
      rw [hK] at hy'
      exact hy'
    · intro hy
      have hy' : proj e y ∈ (H₀.subgroupOf L).map (proj e) := by rw [hK]; exact hy
      obtain ⟨b, hb, hby⟩ := hy'
      rcases (hJ.proj_eq_proj_iff' e).mp hby with h1 | h1
      · rw [h1]; exact hb
      · rw [h1]
        exact (H₀.subgroupOf L).mul_mem hb (Subgroup.mem_subgroupOf.mpr hzH₀)
  have hTA := isTwoAlt_comap_stabilizer hJ e
  have hTA' : IsTwoAlt ↥(H₀.subgroupOf L) 8 :=
    CFSG.GH74.Uniqueness.SU.SU13.isTwoAlt_of_mulEquiv (MulEquiv.subgroupCongr hB).symm hTA
  have hTL' : Subgroup.map L.subtype (TL : Subgroup ↥L) = (T : Subgroup H) := by
    rw [hTL, hLtop, inf_top_eq]
  have hc2 : Nat.card (center ↥(TL : Subgroup ↥L)) = 2 := hJ.card_center_sylow TL
  let φ : ↥(TL : Subgroup ↥L) ≃* ↥(T : Subgroup H) :=
    ((TL : Subgroup ↥L).equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hTL')
  have hcard' : Nat.card (center ↥(T : Subgroup H)) = 2 := by
    have := Nat.card_congr (Subgroup.centerCongr φ).toEquiv
    omega
  refine ⟨⟨hLtop, hA', CFSG.GH74.Uniqueness.SU.SU13.isTwoAlt_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hH₀L) hTA'⟩, isCyclic_of_prime_card hcard'⟩

end CFSG.GH74.Uniqueness.SU.K.R6
