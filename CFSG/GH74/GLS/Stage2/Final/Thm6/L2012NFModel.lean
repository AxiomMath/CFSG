module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.SL2BoundBar
public import CFSG.GH74.GLS.Stage2.Local.Lemma23e
public import CFSG.GH74.GLS.IVK.Lifted.YModelOuter
public import CFSG.GH74.GLS.Stage2.Final.Thm6.SL2BoundGrp
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Lifted CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound


variable {F : Type} [Field F] [Finite F]

theorem fixed_outer_cyclic {Q : Type} [Group Q] (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (φ : MulAut Q) (hφ2 : φ * φ = 1)
    (hout : φ ∉ (MulAut.conj : Q →* MulAut Q).range)
    (hσ : (gammaOf hodd h3 (MulAut.congr e φ)).right = 1) :
    IsCyclic ↥(fixedSubgroup Q φ) ∧
      Nat.card ↥(fixedSubgroup Q φ) = if Nat.card F % 4 = 1 then Nat.card F + 1 else Nat.card F - 1 := by
  have hα2 : MulAut.congr e φ * MulAut.congr e φ = 1 := by rw [← map_mul, hφ2, map_one]
  obtain ⟨G, hG⟩ := eq_slConjugation_of_right_eq_one hodd h3 _ hσ
  have hsq := sq_scalar_of_conj_sq_one G (by rw [← hG]; exact hα2)
  have hdet : ¬ IsSquare ((G : Matrix (Fin 2) (Fin 2) F).det) := by
    intro hsqr
    apply hout
    apply inn_of_congr_inn e
    rw [hG]
    exact (slConjugation_mem_inn_iff hodd h3 G).2 hsqr
  have hns : ¬ ∃ s : F, (G : Matrix (Fin 2) (Fin 2) F) = s • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rintro ⟨s, hs⟩
    exact hdet (isSquare_det_of_scalar G s hs)
  have hF : L2Field F := ⟨hodd, h3⟩
  have hmod : Nat.card F % 4 = 1 ∨ Nat.card F % 4 = 3 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hqpos : 0 < Nat.card F := Nat.card_pos
  have hmapeq : fixedSubgroup Q φ ≃* ↥(slCentralizer G) := by
    refine (fixedEquivCongr e φ).trans ?_
    rw [hG, slCentralizer_eq_map]
    exact (Subgroup.equivMapOfInjective _ (specialLinearGroupEquivStatedSL 2 F).toMonoidHom
      (specialLinearGroupEquivStatedSL 2 F).injective)
  have hcc : IsCyclic ↥(slCentralizer G) ∧ Nat.card ↥(slCentralizer G) =
      (if Nat.card F % 4 = 1 then Nat.card F + 1 else Nat.card F - 1) := by
    rcases hmod with h1 | h3'
    · simp only [h1, ↓reduceIte]
      refine slCentralizer_outer_involution hF 1 (Or.inl rfl) ?_ (Nat.card F + 1) ?_ G ⟨hsq.choose, hsq.choose_spec⟩ hns hdet
      · rw [Int.ModEq]; omega
      · push_cast; ring
    · simp only [show ¬ (Nat.card F % 4 = 1) by omega, ↓reduceIte]
      refine slCentralizer_outer_involution hF (-1) (Or.inr rfl) ?_ (Nat.card F - 1) ?_ G ⟨hsq.choose, hsq.choose_spec⟩ hns hdet
      · rw [Int.ModEq]; omega
      · rw [Nat.cast_sub (by omega)]; push_cast; ring
  exact ⟨hmapeq.isCyclic.2 hcc.1, by rw [Nat.card_congr hmapeq.toEquiv]; exact hcc.2⟩


section SubgroupLevel

variable {G : Type} [Group G]

theorem outer_inf_cyclic {K : Subgroup G} (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) {t : G} (ht : t ∈ normalizer (K : Set G))
    (ht2 : t * t = 1) (hout : ¬ ∃ a ∈ K, ∀ k ∈ K, t * k * t⁻¹ = a * k * a⁻¹)
    (hfld : (gammaOf hodd h3 (MulAut.congr e (conjAut K t ht))).right = 1) :
    IsCyclic ↥(K ⊓ centralizer ({t} : Set G)) ∧
      Nat.card ↥(K ⊓ centralizer ({t} : Set G)) =
        if Nat.card F % 4 = 1 then Nat.card F + 1 else Nat.card F - 1 := by
  have hφ2 := conjAut_mul_self ht ht2
  have hout' : conjAut K t ht ∉ (MulAut.conj : ↥K →* MulAut ↥K).range :=
    fun h => hout ((conjAut_mem_range_iff ht).1 h)
  obtain ⟨hc, hn⟩ := fixed_outer_cyclic e hodd h3 _ hφ2 hout' hfld
  have hX := map_fixedSubgroup_conjAut ht
  let eD : ↥(fixedSubgroup ↥K (conjAut K t ht)) ≃* ↥(K ⊓ centralizer ({t} : Set G)) :=
    ((fixedSubgroup ↥K (conjAut K t ht)).equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr hX)
  exact ⟨eD.isCyclic.1 hc, by rw [← Nat.card_congr eD.toEquiv]; exact hn⟩


theorem outer_of_pgl [Finite G] {K : Subgroup G} (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) {t : G} (ht : t ∈ normalizer (K : Set G))
    (ht2 : t * t = 1) {z₀ : G} (hz₀ : z₀ ∈ K) (hzc : ∀ a ∈ K, a * z₀ = z₀ * a) (hz1 : z₀ ≠ 1)
    (hn : ((zpowers z₀).subgroupOf (K ⊔ zpowers t)).Normal)
    (hPGL : IsPGL2 (↥(K ⊔ zpowers t) ⧸ (zpowers z₀).subgroupOf (K ⊔ zpowers t))
      (fun r => r = Nat.card F)) :
    (¬ ∃ a ∈ K, ∀ k ∈ K, t * k * t⁻¹ = a * k * a⁻¹) ∧
      (gammaOf hodd h3 (MulAut.congr e (conjAut K t ht))).right = 1 := by
  have : Finite ↥K := inferInstance
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hSn⟩ := CFSG.GH74.GLS.Stage1.Thm2.Recip.exists_invariant_sylow
    (CFSG.GH74.GLS.Stage1.Thm2.Recip.isPGroup_zpowers_of_mul_self_eq_one ht2) (zpowers_le.2 ht)
  obtain ⟨T, hT'⟩ := (CFSG.ABGLocalTools.isSylowOf_iff.2 hS).exists_sylow_eq_subgroupOf
  have hT : ∀ x ∈ (T : Subgroup ↥K), TwoThin.conjAut ht x ∈ (T : Subgroup ↥K) := by
    intro x hx
    rw [hT', Subgroup.mem_subgroupOf] at hx ⊢
    have := (Subgroup.mem_normalizer_iff.1 (hSn (Subgroup.mem_zpowers t)) (x : G)).1 hx
    exact this
  obtain ⟨hout, hfld⟩ := model_outer hodd h3 e hz₀ hzc hz1 ht ht2 hn hPGL T hT
  refine ⟨fun ⟨a, ha, hk⟩ => hout ?_, hfld⟩
  have : conjAut K t ht ∈ (MulAut.conj : ↥K →* MulAut ↥K).range := (conjAut_mem_range_iff ht).2 ⟨a, ha, hk⟩
  exact this

end SubgroupLevel



section PglOver

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem mem_sup_zpowers_cases' {L : Subgroup Y} {t : Y} (ht : t ∈ normalizer (L : Set Y)) (ht2 : t * t = 1)
    {x : Y} (hx : x ∈ L ⊔ zpowers t) : x ∈ L ∨ ∃ n ∈ L, x = n * t := by
  have hnorm : zpowers t ≤ normalizer (L : Set Y) := by rwa [zpowers_le]
  have hx' : x ∈ ((L ⊔ zpowers t : Subgroup Y) : Set Y) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hx'
  obtain ⟨h, hh, _, ⟨k, rfl⟩, rfl⟩ := hx'
  have hsq : t ^ 2 = 1 := by rw [pow_two]; exact ht2
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    show h * t ^ (2 * m) ∈ L
    rw [zpow_mul, zpow_two, ht2]
    simpa using hh
  · right
    refine ⟨h, hh, ?_⟩
    show h * t ^ (2 * m + 1) = h * t
    rw [zpow_add, zpow_mul, zpow_one, zpow_two, ht2]
    simp


omit [Finite Y] in
theorem card_sup_zpowers_of_invol {L : Subgroup Y} {t : Y} (ht : t ∈ normalizer (L : Set Y))
    (ht2 : t * t = 1) (htL : t ∉ L) :
    Nat.card ↥(L ⊔ zpowers t) = 2 * Nat.card ↥L := by
  set X' := L ⊔ zpowers t with hX'
  have hLX : L ≤ X' := le_sup_left
  have htX : t ∈ X' := mem_sup_right (mem_zpowers t)
  have hidx : (L.subgroupOf X').index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨t, htX⟩, fun b => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rcases mem_sup_zpowers_cases' ht ht2 b.2 with hb | ⟨n, hn, hbn⟩
    · right
      refine ⟨hb, fun h => htL ?_⟩
      have : t = (b : Y)⁻¹ * ((b : Y) * t) := by group
      rw [this]
      exact L.mul_mem (L.inv_mem hb) h
    · left
      refine ⟨?_, fun h => htL ?_⟩
      · show (b : Y) * t ∈ L
        rw [hbn, mul_assoc, ht2, mul_one]
        exact hn
      · have : t = n⁻¹ * (b : Y) := by rw [hbn]; group
        rw [this]
        exact L.mul_mem (L.inv_mem hn) h
  have h1 := Subgroup.card_mul_index (L.subgroupOf X')
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLX).toEquiv] at h1
  rw [← h1, mul_comm]


theorem pgl_of_nrm {L A' : Subgroup Y} {r : ℕ} (hodd : Odd r)
    (hsl : HasSL2Model ↥L (fun q => q = r)) (hpgl : InducedPGL2 L A' r) {t : Y} (htA : t ∈ A')
    (ht2 : t * t = 1) (htN : t ∈ normalizer (L : Set Y)) (hnin : t ∉ L ⊔ centralizer (L : Set Y)) :
    PGLOver L (zpowers t) r := by
  have hcardLQ : Nat.card ↥L =
      Nat.card (↥(L ⊔ A') ⧸ (centralizer (L : Set Y)).subgroupOf (L ⊔ A')) := bar_card_eq_of_pgl L A' hsl hpgl
  obtain ⟨hZn, hPGL⟩ := hpgl
  set X := L ⊔ A' with hX
  set X' := L ⊔ zpowers t with hX'
  have hX'X : X' ≤ X := sup_le_sup_left (zpowers_le.2 htA) L
  have htL : t ∉ L := fun h => hnin (Subgroup.mem_sup_left h)
  set Zm : Subgroup Y := (center ↥L).map L.subtype with hZm
  have hZmL : Zm ≤ L := Subgroup.map_subtype_le _
  have hZmX' : Zm ≤ X' := hZmL.trans le_sup_left
  have hcardZm : Nat.card ↥Zm = 2 := by
    have := (sl2_model_center_inv hodd hsl).1
    rw [hZm, Subgroup.card_map_of_injective L.subtype_injective]
    exact this
  set Zc : Subgroup ↥X := (centralizer (L : Set Y)).subgroupOf X with hZc
  let f : ↥X' →* ↥X ⧸ Zc := (QuotientGroup.mk' Zc).comp (Subgroup.inclusion hX'X)
  have hker : f.ker = Zm.subgroupOf X' := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (QuotientGroup.mk' Zc) (Subgroup.inclusion hX'X x) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hZc, Subgroup.mem_subgroupOf]
    show (x : Y) ∈ centralizer (L : Set Y) ↔ (x : Y) ∈ Zm
    constructor
    · intro hc
      rcases mem_sup_zpowers_cases' htN ht2 x.2 with hxL | ⟨n, hn, hxn⟩
      · have : (⟨(x : Y), hxL⟩ : ↥L) ∈ center ↥L := by
          rw [Subgroup.mem_center_iff]
          intro g
          apply Subtype.ext
          exact (Subgroup.mem_centralizer_iff.1 hc g g.2)
        exact ⟨_, this, rfl⟩
      · exfalso
        apply hnin
        have h1 : t = n⁻¹ * (x : Y) := by rw [hxn]; group
        rw [h1]
        exact Subgroup.mul_mem_sup (L.inv_mem hn) hc
    · rintro ⟨c, hc, hcx⟩
      rw [← hcx]
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨g, hg⟩)
  have hcardX' : Nat.card ↥X' = 2 * Nat.card ↥L := card_sup_zpowers_of_invol htN ht2 htL
  have hcardker : Nat.card ↥f.ker = 2 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZmX').toEquiv]
    exact hcardZm
  have hcardQ' : Nat.card (↥X' ⧸ f.ker) = Nat.card ↥L := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [hcardX', hcardker] at h1
    omega
  have hinj : Function.Injective (QuotientGroup.kerLift f) := QuotientGroup.kerLift_injective f
  have hbij : Function.Bijective (QuotientGroup.kerLift f) :=
    hinj.bijective_of_nat_card_le (by rw [hcardQ', hcardLQ])
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨q, hq⟩ := hbij.2 y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨x, hq⟩
  have hnormZ : (Zm.subgroupOf X').Normal := hker ▸ f.normal_ker
  refine ⟨hnormZ, ?_⟩
  obtain ⟨F₀, hF₀, hFin₀, hF₀r, ⟨e₀⟩⟩ := hPGL
  refine ⟨F₀, hF₀, hFin₀, hF₀r, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)).trans e₀

end PglOver


end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
