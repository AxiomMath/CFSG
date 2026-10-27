module

public import CFSG.GH74.Generic.BProg.B3.Thm9S45Fusion
public import CFSG.GH74.Generic.S45.LDiagMain
public import CFSG.GH74.Generic.BProg.Vocab
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace Thm9S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.Generic.S45 CFSG.GH74.L5U5 CFSG.ABGLocalTools
  CFSG.Blueprint CFSG.GH74.GLS Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Core

theorem eq_bot_of_perfect_comm_ker' {U Y₁ Y₂ : Type} [Group U] [Finite U] [Group Y₁] [Group Y₂]
    (f₁ : U →* Y₁) (f₂ : U →* Y₂)
    (h₁ : ∀ g, f₁ g = 1 → Odd (orderOf g)) (h₂ : ∀ g, f₂ g = 1 → Odd (orderOf g))
    {W : Subgroup U} (hWs : IsSimpleGroup ↥(W.map f₁)) (hWp : ⁅W, W⁆ = W)
    {e : U} (heW : e ∈ W) (he2 : e * e = 1) (he1 : e ≠ 1)
    {Q : Subgroup U} (hQ : ⁅Q, Q⁆ = Q) (hQW : Q.map f₁ ≤ W.map f₁)
    (hcomm : ∀ q ∈ Q, ∀ w ∈ W, q * w * q⁻¹ * w⁻¹ ∈ f₂.ker) : Q = ⊥ := by
  have he_ord : orderOf e = 2 := orderOf_eq_prime (by rw [sq]; exact he2) he1
  have hf₁e : f₁ e ≠ 1 := fun h => by
    have := h₁ e h
    rw [he_ord] at this
    exact absurd this (by decide)
  have hf₁e_ord : orderOf (f₁ e) = 2 :=
    orderOf_eq_prime (by rw [sq, ← map_mul, he2, map_one]) hf₁e
  set W' : Subgroup Y₁ := W.map f₁ with hW'
  set N₂' : Subgroup Y₁ := f₂.ker.map f₁ with hN₂'
  have hN₂odd : ∀ n ∈ N₂', Odd (orderOf n) := by
    rintro _ ⟨k, hk, rfl⟩
    exact (h₂ k (MonoidHom.mem_ker.1 hk)).of_dvd_nat (orderOf_map_dvd f₁ k)
  let A₀ : Subgroup ↥W' := N₂'.comap W'.subtype
  have hA₀n : A₀.Normal := by
    constructor
    intro a ha w
    obtain ⟨k, hk, hka⟩ := ha
    obtain ⟨w₀, hw₀, hw₀w⟩ := w.2
    have hk' : f₂ k = 1 := hk
    refine ⟨w₀ * k * w₀⁻¹, ?_, ?_⟩
    · show f₂ (w₀ * k * w₀⁻¹) = 1
      rw [map_mul, map_mul, hk', mul_one, map_inv, mul_inv_cancel]
    · have hka' : f₁ k = (a : Y₁) := hka
      show f₁ (w₀ * k * w₀⁻¹) = ((w * a * w⁻¹ : ↥W') : Y₁)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      simp only [map_mul, map_inv, hka', hw₀w]
  have hA₀ : A₀ = ⊥ := by
    have : A₀.Normal := hA₀n
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A₀ with h | h
    · exact h
    · exfalso
      have hmem : (⟨f₁ e, ⟨e, heW, rfl⟩⟩ : ↥W') ∈ A₀ := by rw [h]; trivial
      have h1 : f₁ e ∈ N₂' := hmem
      have h2 := hN₂odd _ h1
      rw [hf₁e_ord] at h2
      exact absurd h2 (by decide)
  have hZ : center ↥W' = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥W') with h | h
    · exact h
    · exfalso
      have hab : ∀ a b : ↥W', a * b = b * a := fun a b => by
        have : a ∈ center ↥W' := by rw [h]; trivial
        exact (Subgroup.mem_center_iff.1 this b).symm
      have hperf : ⁅W', W'⁆ = W' := by rw [hW', ← Subgroup.map_commutator, hWp]
      have hbot : ⁅W', W'⁆ ≤ ⊥ := by
        rw [Subgroup.commutator_le]
        intro g₁ h₁ g₂ h₂
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact congrArg Subtype.val (hab ⟨g₁, h₁⟩ ⟨g₂, h₂⟩)
      have hW'bot : W' = ⊥ := by rw [← hperf]; exact le_bot_iff.1 hbot
      have hmem : f₁ e ∈ W' := ⟨e, heW, rfl⟩
      rw [hW'bot, Subgroup.mem_bot] at hmem
      exact hf₁e hmem
  have hker : ∀ q ∈ Q, f₁ q = 1 := by
    intro q hq
    obtain ⟨w₀, hw₀, hw₀q⟩ := hQW ⟨q, hq, rfl⟩
    have hw₀W' : f₁ w₀ ∈ W' := ⟨w₀, hw₀, rfl⟩
    have hcen : (⟨f₁ w₀, hw₀W'⟩ : ↥W') ∈ center ↥W' := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨w₁, hw₁, hw₁w⟩ := w.2
      have hc := hcomm q hq w₁ hw₁
      have hmemA : (⟨f₁ w₀ * (w : Y₁) * (f₁ w₀)⁻¹ * (w : Y₁)⁻¹,
          mul_mem (mul_mem (mul_mem hw₀W' w.2) (inv_mem hw₀W')) (inv_mem w.2)⟩ : ↥W') ∈ A₀ := by
        refine ⟨q * w₁ * q⁻¹ * w₁⁻¹, hc, ?_⟩
        show f₁ (q * w₁ * q⁻¹ * w₁⁻¹) = f₁ w₀ * (w : Y₁) * (f₁ w₀)⁻¹ * (w : Y₁)⁻¹
        simp only [map_mul, map_inv]
        rw [hw₀q, hw₁w]
      rw [hA₀, Subgroup.mem_bot] at hmemA
      have h1 : ⁅f₁ w₀, (w : Y₁)⁆ = 1 := congrArg Subtype.val hmemA
      have h3 : f₁ w₀ * (w : Y₁) = (w : Y₁) * f₁ w₀ := commutatorElement_eq_one_iff_mul_comm.1 h1
      exact Subtype.ext h3.symm
    rw [hZ, Subgroup.mem_bot] at hcen
    have : f₁ w₀ = 1 := congrArg Subtype.val hcen
    rw [← hw₀q]
    exact this
  exact eq_bot_of_perfect_of_odd hQ (odd_card_of_forall_odd_orderOf fun q hq => h₁ q (hker q hq))

theorem map_eq_of_KCent {X U : Type} [Group X] [Finite X] [Group U] {K : Subgroup X} {z : X}
    (hd : KData X K z) (hKC : KCent ↥K) (f : U →* X) {t : X} (htK : t ∈ K) (ht : orderOf t = 2)
    (hfc : ∀ u, f u * t = t * f u) (hsurj : ∀ y : X, y * t = t * y → ∃ u, f u = y)
    {W : Subgroup U} (hWsub : W.IsSubnormal) (hW : ⁅W, W⁆ = W) {e : U} (heW : e ∈ W)
    (hfe : f e ≠ 1) :
    IsSimpleGroup ↥(W.map f) ∧ ∀ Q : Subgroup U, ⁅Q, Q⁆ = Q → Q.map f ≤ W.map f := by
  set H₀ : Subgroup X := K ⊓ centralizer ({t} : Set X) with hH₀
  set S : Subgroup X := ⁅H₀, H₀⁆ with hS
  have hmapS : ∀ R : Subgroup U, ⁅R, R⁆ = R → R.map f ≤ S := by
    intro R hR
    have hRp : ⁅R.map f, R.map f⁆ = R.map f := by rw [← Subgroup.map_commutator, hR]
    have hK1 : R.map f ≤ K := hd.perfect_le hRp
    have hC1 : R.map f ≤ centralizer ({t} : Set X) := by
      rintro _ ⟨u, -, rfl⟩
      exact mem_centralizer_singleton_iff.2 (hfc u)
    calc R.map f = ⁅R.map f, R.map f⁆ := hRp.symm
      _ ≤ ⁅H₀, H₀⁆ := Subgroup.commutator_mono (le_inf hK1 hC1) (le_inf hK1 hC1)
  have hSsimple : IsSimpleGroup ↥S := by
    let s : ↥K := ⟨t, htK⟩
    have hs2 : orderOf s = 2 := by rw [Subgroup.orderOf_mk]; exact ht
    obtain ⟨hsimple, -, -⟩ := hKC s hs2
    have hmapC : (centralizer ({s} : Set ↥K)).map K.subtype = H₀ := by
      ext y
      constructor
      · rintro ⟨c, hc, rfl⟩
        have hc' : c * s = s * c := mem_centralizer_singleton_iff.1 hc
        exact ⟨c.2, mem_centralizer_singleton_iff.2 (congrArg Subtype.val hc')⟩
      · intro hy
        obtain ⟨hyK, hyc⟩ := hy
        refine ⟨⟨y, hyK⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
        exact Subtype.ext (mem_centralizer_singleton_iff.1 hyc)
    have hSeq : (⁅centralizer ({s} : Set ↥K), centralizer ({s} : Set ↥K)⁆).map K.subtype = S := by
      rw [Subgroup.map_commutator, hmapC]
    exact (MulEquiv.isSimpleGroup_congr
      ((Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).trans
        (MulEquiv.subgroupCongr hSeq))).1 hsimple
  have hBS : W.map f ≤ S := hmapS W hW
  have hSB : S ≤ W.map f := by
    set Ct : Subgroup X := centralizer ({t} : Set X) with hCt
    let g : U →* ↥Ct := f.codRestrict Ct (fun u => mem_centralizer_singleton_iff.2 (hfc u))
    have hg : Function.Surjective g := by
      intro c
      obtain ⟨u, hu⟩ := hsurj (c : X) (mem_centralizer_singleton_iff.1 c.2)
      exact ⟨u, Subtype.ext hu⟩
    have h1 : (W.map g).IsSubnormal := hWsub.map hg
    have h2 : W.map g = (W.map f).subgroupOf Ct := by
      ext c
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, rfl⟩
      · rintro ⟨w, hw, hwc⟩
        exact ⟨w, hw, Subtype.ext hwc⟩
    rw [h2] at h1
    have hSCt : S ≤ Ct := (Subgroup.commutator_le_self H₀).trans inf_le_right
    have h3 : ((W.map f).subgroupOf S).IsSubnormal :=
      TwoThin.isSubnormal_inf_subgroupOf h1 hSCt
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hSsimple h3 with h | h
    · exfalso
      have hmem : (⟨f e, hBS ⟨e, heW, rfl⟩⟩ : ↥S) ∈ (W.map f).subgroupOf S := ⟨e, heW, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact hfe (congrArg Subtype.val hmem)
    · intro y hy
      have hmem : (⟨y, hy⟩ : ↥S) ∈ (W.map f).subgroupOf S := by rw [h]; trivial
      exact hmem
  have hEq : W.map f = S := le_antisymm hBS hSB
  refine ⟨(MulEquiv.isSimpleGroup_congr (MulEquiv.subgroupCongr hEq)).2 hSsimple,
    fun Q hQ => (hmapS Q hQ).trans hSB⟩

end Core

section Diagonal

variable {G : Type} [Group G] [Finite G]

theorem false_of_diagonal_pumpup_H {x v : G} (hxord : orderOf x = 2) (hvord : orderOf v = 2)
    (hvx : v ∈ centralizer ({x} : Set G)) (hxv : x ∈ centralizer ({v} : Set G))
    {K : Subgroup (CentralizerBar x)} (hd : KData (CentralizerBar x) K (xbar x)) (hKC : KCent ↥K)
    (hvK : proj x ⟨v, hvx⟩ ∈ K)
    {W : Subgroup G} (hWY : W ≤ centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G))
    (hWsub : (W.subgroupOf (centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G))).IsSubnormal)
    (hWperf : ⁅W, W⁆ = W) (hWne : W ≠ ⊥)
    (hxc : proj v ⟨x, hxv⟩ ∈ _root_.commutator (CentralizerBar v))
    {L : Subgroup (CentralizerBar v)} (hL : IsComponent L)
    (hne : conjSub (proj v ⟨x, hxv⟩)⁻¹ L ≠ L) (hAB : ⁅L, conjSub (proj v ⟨x, hxv⟩)⁻¹ L⁆ = ⊥)
    (hle : barSub v W ≤ (swapDiag hAB).range) : False := by
  classical
  have hv2 : v * v = 1 := by
    have := pow_orderOf_eq_one v
    rwa [hvord, pow_two] at this
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxord, pow_two] at this
  have hv1 : v ≠ 1 := fun h => by rw [h, orderOf_one] at hvord; omega
  set t : CentralizerBar v := proj v ⟨x, hxv⟩ with ht
  have ht2 : t * t = 1 := by
    rw [ht, ← map_mul]
    have : (⟨x, hxv⟩ * ⟨x, hxv⟩ : ↥(centralizer ({v} : Set G))) = 1 := Subtype.ext hx2
    rw [this, map_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hinvol : ∀ M : Subgroup (CentralizerBar v), conjSub t⁻¹ (conjSub t⁻¹ M) = M := fun M => by
    rw [← conjSub_mul_comp, ← mul_inv_rev, ht2, inv_one, conjSub_one_comp]
  obtain ⟨B, hB, hBne, hBL, hBLt⟩ := exists_second_swapped hxc ht2 hL hne
  have hAB' : ⁅B, conjSub t⁻¹ B⁆ = ⊥ := commutator_conjSub_eq_bot hB hBne
  have hBt : IsComponent (conjSub t⁻¹ B) := isComponent_conjSub hB t⁻¹
  have hLt : IsComponent (conjSub t⁻¹ L) := isComponent_conjSub hL t⁻¹
  have hBtL : conjSub t⁻¹ B ≠ L := fun h => hBLt (by rw [← h, hinvol])
  have hBtLt : conjSub t⁻¹ B ≠ conjSub t⁻¹ L := fun h => hBL (by
    have := congrArg (conjSub t⁻¹) h
    rwa [hinvol, hinvol] at this)
  have hcomm2 := comm_sup_sup (comm_of_ne_components hB hL hBL) (comm_of_ne_components hB hLt hBLt)
    (comm_of_ne_components hBt hL hBtL) (comm_of_ne_components hBt hLt hBtLt)
  have hBq : CFSG.Assembly.IsQuasisimple ↥B := assembly_isQuasisimple_of_isComponent hB
  have hΔq := isQuasisimple_range_swapDiag hAB' hBq
  have hΔperf : ⁅(swapDiag hAB').range, (swapDiag hAB').range⁆ = (swapDiag hAB').range :=
    Subgroup.isPerfect_iff.1 ⟨hΔq.1⟩
  have hΔne : (swapDiag hAB').range ≠ ⊥ := by
    intro hbot
    have hsimple : IsSimpleGroup (↥(swapDiag hAB').range ⧸ center ↥(swapDiag hAB').range) := hΔq.2
    have hnt : Nontrivial ↥(swapDiag hAB').range :=
      (QuotientGroup.mk'_surjective (center ↥(swapDiag hAB').range)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt hbot
  set X₀ : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G) with hX₀
  let f₁ : ↥X₀ →* CentralizerBar x := (proj x).comp (Subgroup.inclusion inf_le_left)
  let f₂ : ↥X₀ →* CentralizerBar v := (proj v).comp (Subgroup.inclusion inf_le_right)
  have hf₁ : ∀ g : ↥X₀, f₁ g = proj x ⟨g.1, g.2.1⟩ := fun g => rfl
  have hf₂ : ∀ g : ↥X₀, f₂ g = proj v ⟨g.1, g.2.2⟩ := fun g => rfl
  have h₁ : ∀ g : ↥X₀, f₁ g = 1 → Odd (orderOf g) := by
    intro g hg
    have h := proj_odd x ⟨g.1, g.2.1⟩ hg
    have hord : orderOf (Subgroup.inclusion (inf_le_left : X₀ ≤ centralizer ({x} : Set G)) g) =
        orderOf g := orderOf_injective _ (Subgroup.inclusion_injective _) g
    rw [← hord]
    exact h
  have h₂ : ∀ g : ↥X₀, f₂ g = 1 → Odd (orderOf g) := by
    intro g hg
    have h := proj_odd v ⟨g.1, g.2.2⟩ hg
    have hord : orderOf (Subgroup.inclusion (inf_le_right : X₀ ≤ centralizer ({v} : Set G)) g) =
        orderOf g := orderOf_injective _ (Subgroup.inclusion_injective _) g
    rw [← hord]
    exact h
  have hWeven : ¬ Odd (Nat.card ↥W) := fun hodd => hWne (eq_bot_of_perfect_of_odd hWperf hodd)
  have h2dvd : 2 ∣ Nat.card ↥W := by
    rcases Nat.even_or_odd (Nat.card ↥W) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hWeven
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e', he'⟩ := exists_prime_orderOf_dvd_card' (G := ↥W) 2 h2dvd
  have he'ord : orderOf (e' : G) = 2 := by rw [Subgroup.orderOf_coe]; exact he'
  have heW : (e' : G) ∈ W := e'.2
  have he2 : (e' : G) * (e' : G) = 1 := by
    have := pow_orderOf_eq_one (e' : G)
    rwa [he'ord, pow_two] at this
  have he1 : (e' : G) ≠ 1 := fun h => by rw [h, orderOf_one] at he'ord; omega
  let Wu : Subgroup ↥X₀ := W.subgroupOf X₀
  have hWuperf : ⁅Wu, Wu⁆ = Wu := by
    apply Subgroup.map_injective X₀.subtype_injective
    rw [Subgroup.map_commutator]
    have hmap : Wu.map X₀.subtype = W := Subgroup.map_subgroupOf_eq_of_le hWY
    rw [hmap, hWperf]
  let eU : ↥X₀ := ⟨(e' : G), hWY heW⟩
  have heU : eU ∈ Wu := heW
  have heU2 : eU * eU = 1 := Subtype.ext he2
  have heU1 : eU ≠ 1 := fun h => he1 (congrArg Subtype.val h)
  have hfe : f₁ eU ≠ 1 := fun h =>
    he1 (eq_one_of_proj_eq_one_of_sq (v := x) (hWY heW).1 h he2)
  have ht1ord : orderOf (proj x ⟨v, hvx⟩) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← map_mul]
      have : (⟨v, hvx⟩ * ⟨v, hvx⟩ : ↥(centralizer ({x} : Set G))) = 1 := Subtype.ext hv2
      rw [this, map_one]
    · intro h1
      exact hv1 (eq_one_of_proj_eq_one_of_sq (v := x) hvx h1 hv2)
  have hfc : ∀ u : ↥X₀, f₁ u * proj x ⟨v, hvx⟩ = proj x ⟨v, hvx⟩ * f₁ u := by
    intro u
    rw [hf₁, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show u.1 * v = v * u.1
    exact mem_centralizer_singleton_iff.1 u.2.2
  have hsurj : ∀ y : CentralizerBar x, y * proj x ⟨v, hvx⟩ = proj x ⟨v, hvx⟩ * y →
      ∃ u : ↥X₀, f₁ u = y := by
    intro y hy
    obtain ⟨g, hg, hgy⟩ := proj_cent x (u := ⟨v, hvx⟩) (Subtype.ext hv2) y hy
    have hgv : g.1 ∈ centralizer ({v} : Set G) :=
      mem_centralizer_singleton_iff.2 (congrArg Subtype.val hg)
    exact ⟨⟨g.1, ⟨g.2, hgv⟩⟩, hgy⟩
  have hΔrange : (swapDiag hAB').range ≤ f₂.range := by
    rintro _ ⟨b, rfl⟩
    have hyc : swapDiag hAB' b * t = t * swapDiag hAB' b :=
      mem_centralizer_singleton_iff.1 (swapDiag_mem_centralizer hAB' htinv b)
    obtain ⟨g, hg, hgy⟩ := proj_cent v (u := ⟨x, hxv⟩) (Subtype.ext hx2) (swapDiag hAB' b) hyc
    have hgx : g.1 ∈ centralizer ({x} : Set G) :=
      mem_centralizer_singleton_iff.2 (congrArg Subtype.val hg)
    exact ⟨⟨g.1, ⟨hgx, g.2⟩⟩, hgy⟩
  obtain ⟨Q, hQperf, hQmap⟩ := exists_perfect_lift_hom f₂ hΔperf hΔrange
  obtain ⟨hWs', hQWall⟩ := map_eq_of_KCent hd hKC f₁ hvK ht1ord hfc hsurj hWsub hWuperf heU hfe
  have hQW : Q.map f₁ ≤ Wu.map f₁ := hQWall Q hQperf
  have hcomm : ∀ q ∈ Q, ∀ w ∈ W.subgroupOf X₀, q * w * q⁻¹ * w⁻¹ ∈ f₂.ker := by
    intro q hq w hw
    have hq' : f₂ q ∈ (swapDiag hAB').range := by rw [← hQmap]; exact ⟨q, hq, rfl⟩
    obtain ⟨b, hb⟩ := hq'
    have hq'' : f₂ q ∈ B ⊔ conjSub t⁻¹ B := by rw [← hb]; exact swapDiag_mem_sup hAB' b
    have hw' : f₂ w ∈ barSub v W := proj_mem_barSub (v := v) (J := W) w.2.2 hw
    obtain ⟨a, ha⟩ := hle hw'
    have hw'' : f₂ w ∈ L ⊔ conjSub t⁻¹ L := by rw [← ha]; exact swapDiag_mem_sup hAB a
    have hc := hcomm2 _ hq'' _ hw''
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv]
    exact commutatorElement_eq_one_iff_mul_comm.2 hc
  have hQ0 : Q = ⊥ :=
    eq_bot_of_perfect_comm_ker' f₁ f₂ h₁ h₂ hWs' hWuperf heU heU2 heU1 hQperf hQW hcomm
  apply hΔne
  rw [← hQmap, hQ0, Subgroup.map_bot]


end Diagonal

section Translate

variable {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup G}

theorem isPCompIn_of_le {H H' K : Subgroup G} (h : IsPCompIn 2 H K) (hKH' : K ≤ H') (hH'H : H' ≤ H) :
    IsPCompIn 2 H' K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hKH', ?_⟩
  have h2 : K.subgroupOf H ≤ H'.subgroupOf H := fun x hx => hKH' hx
  have h3 := CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_restrict_overgroup 2 h.2 h2
  exact (CFSG.ComponentClassification.UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hH'H 2
    Nat.prime_two).mp h3

theorem pLayerOf_self {X K : Subgroup G} (hK : IsPCompIn 2 X K) : pLayerOf 2 K = K :=
  le_antisymm (sSup_le fun _ hL => hL.1) (le_sSup (isPCompIn_of_le hK le_rfl hK.1))

theorem isComponent_imgBar (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) :
    IsComponent (S3.imgBar x K) :=
  TwoThin.isComponent_map_barMk (TwoThin.isPCompIn_two_iff.mp hK).2

theorem exists_equiv_imgBar (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) :
    Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* ↥(S3.imgBar x K)) := by
  obtain ⟨hKC, K', -, hsub, -⟩ := hK
  obtain ⟨e1⟩ := TwoThin.hat_equiv_map (M := K.subgroupOf (centralizer ({x} : Set G))) hsub
  obtain ⟨e2⟩ := TwoThin.hat_equiv_subgroupOf hKC
  exact ⟨e2.trans e1⟩

theorem kbar_data
    (hyp : Hyp2 G) (hx : orderOf x = 2) (hKC : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hP : QShape4 (↥K ⧸ pPrimeCore 2 ↥K) ∨ QShape5 (↥K ⧸ pPrimeCore 2 ↥K)) :
    KData (CentralizerBar x) (S3.imgBar x K) (xbar x) ∧ KCent ↥(S3.imgBar x K) := by
  have hcomp : IsComponent (S3.imgBar x K) := isComponent_imgBar hKC
  obtain ⟨e⟩ := exists_equiv_imgBar hKC
  have hj : IsJ1OrRee ↥(S3.imgBar x K) := by
    rcases hP with hP4 | hP5
    · obtain ⟨f, hf⟩ := hP4
      exact Or.inr ⟨f, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hf⟩
    · obtain ⟨e'⟩ := hP5
      exact Or.inl ⟨e.symm.trans e'⟩
  have hKB := b_S45_KFacts ↥(S3.imgBar x K) hj
  have hnab := exists_noncomm_of_isQuasisimple hcomp.1
  have hnot : xbar x ∉ S3.imgBar x K := by
    intro hmem
    have : (⟨xbar x, hmem⟩ : ↥(S3.imgBar x K)) = 1 := by
      apply eq_one_of_central_of_simple hKB.1 hnab
      intro w
      exact Subtype.ext (xbar_comm x w)
    exact xbar_ne_one hx (congrArg Subtype.val this)
  exact ⟨{ gen4 := gen4_centralizerBar hyp.gen4 x
           oddcore := pPrimeCore_quotient_pPrimeCore_eq_bot _ 2
           central := fun g => xbar_comm x g
           sq := xbar_mul_self hx
           ne := xbar_ne_one hx
           comp := hcomp
           notin := hnot
           facts := hKB }, kCent_of_isJ1OrRee hj⟩

end Translate

section Conjugate

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mulEquiv_centralizerBar {x y g : G} (hg : g * x * g⁻¹ = y) :
    Nonempty (CentralizerBar x ≃* CentralizerBar y) := by
  subst hg
  have h1 : ∀ a : ↥(centralizer ({x} : Set G)),
      g * (a : G) * g⁻¹ ∈ centralizer ({g * x * g⁻¹} : Set G) := by
    intro a
    have ha := Subgroup.mem_centralizer_singleton_iff.1 a.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * (a : G) * g⁻¹ * (g * x * g⁻¹) = g * ((a : G) * x) * g⁻¹ := by group
      _ = g * (x * (a : G)) * g⁻¹ := by rw [ha]
      _ = g * x * g⁻¹ * (g * (a : G) * g⁻¹) := by group
  have h2 : ∀ b : ↥(centralizer ({g * x * g⁻¹} : Set G)),
      g⁻¹ * (b : G) * g ∈ centralizer ({x} : Set G) := by
    intro b
    have hb := Subgroup.mem_centralizer_singleton_iff.1 b.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * (b : G) * g * x = g⁻¹ * ((b : G) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (b : G)) * g := by rw [hb]
      _ = x * (g⁻¹ * (b : G) * g) := by group
  let φ : ↥(centralizer ({x} : Set G)) ≃* ↥(centralizer ({g * x * g⁻¹} : Set G)) :=
    { toFun := fun a => ⟨g * (a : G) * g⁻¹, h1 a⟩
      invFun := fun b => ⟨g⁻¹ * (b : G) * g, h2 b⟩
      left_inv := fun a => Subtype.ext (by show g⁻¹ * (g * (a : G) * g⁻¹) * g = a; group)
      right_inv := fun b => Subtype.ext (by show g * (g⁻¹ * (b : G) * g) * g⁻¹ = b; group)
      map_mul' := fun a b => Subtype.ext (by
        show g * ((a : G) * (b : G)) * g⁻¹ = g * (a : G) * g⁻¹ * (g * (b : G) * g⁻¹)
        group) }
  exact ⟨QuotientGroup.congr (pPrimeCore 2 ↥(centralizer ({x} : Set G)))
    (pPrimeCore 2 ↥(centralizer ({g * x * g⁻¹} : Set G))) φ (CFSG.pPrimeCore_map_iso 2 φ)⟩

theorem not_conj_of_components {x y : G} {Kb : Subgroup (CentralizerBar x)}
    (hd : KData (CentralizerBar x) Kb (xbar x)) {L L' : Subgroup (CentralizerBar y)}
    (hL : IsComponent L) (hL' : IsComponent L') (hne : L ≠ L') : ¬ ∃ g : G, g * x * g⁻¹ = y := by
  rintro ⟨g, hg⟩
  obtain ⟨e⟩ := exists_mulEquiv_centralizerBar hg
  have h1 : L.map e.symm.toMonoidHom = Kb :=
    hd.component_eq (CFSG.LocalCores.isComponent_map_mulEquiv e.symm hL)
  have h2 : L'.map e.symm.toMonoidHom = Kb :=
    hd.component_eq (CFSG.LocalCores.isComponent_map_mulEquiv e.symm hL')
  apply hne
  calc L = (L.map e.symm.toMonoidHom).map e.symm.symm.toMonoidHom :=
        (CFSG.LocalCores.map_map_symm e.symm L).symm
    _ = (L'.map e.symm.toMonoidHom).map e.symm.symm.toMonoidHom := by rw [h1, h2]
    _ = L' := CFSG.LocalCores.map_map_symm e.symm L'

end Conjugate

section Position

variable {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup G}

theorem piC_mem_or_of_mem_sup (hx : orderOf x = 2) (hKC : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    {y : G} (hy : y ∈ K ⊔ zpowers x) :
    y ∈ centralizer ({x} : Set G) ∧
      (piC x y ∈ S3.imgBar x K ∨ piC x (x * y) ∈ S3.imgBar x K) := by
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hx2 : xbar x * xbar x = 1 := xbar_mul_self hx
  have hord : orderOf (xbar x) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) (xbar_ne_one hx)
  have hzn : (zpowers (xbar x)).Normal := by
    constructor
    intro n hn g
    obtain ⟨k, rfl⟩ := hn
    have hc : g * xbar x * g⁻¹ = xbar x := by
      rw [mul_inv_eq_iff_eq_mul]
      exact xbar_comm x g
    have : g * xbar x ^ k * g⁻¹ = xbar x ^ k := by
      have h := map_zpow (MulAut.conj g) (xbar x) k
      rw [MulAut.conj_apply, MulAut.conj_apply, hc] at h
      exact h
    rw [this]
    exact zpow_mem (mem_zpowers _) k
  set Kb : Subgroup (CentralizerBar x) := S3.imgBar x K with hKb
  have hKle : K ≤ Pre x (Kb ⊔ zpowers (xbar x)) := by
    intro k hk
    refine ⟨hKC.1 hk, ?_⟩
    rw [piC_of_mem x (hKC.1 hk)]
    exact mem_sup_left ⟨⟨k, hKC.1 hk⟩, hk, rfl⟩
  have hxle : zpowers x ≤ Pre x (Kb ⊔ zpowers (xbar x)) := by
    rw [zpowers_le]
    refine ⟨hxC, ?_⟩
    rw [piC_x]
    exact mem_sup_right (mem_zpowers _)
  have hyD : y ∈ Pre x (Kb ⊔ zpowers (xbar x)) := sup_le hKle hxle hy
  refine ⟨hyD.1, ?_⟩
  have hmem := hyD.2
  obtain ⟨k, hk, n, hn, hkn⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
  rcases (CFSG.Walter.JT.mem_zpowers_of_orderOf_eq_two hord).1 hn with rfl | rfl
  · left
    rw [← hkn, mul_one]
    exact hk
  · right
    have hxy : piC x (x * y) = xbar x * piC x y := by rw [piC_mul x hxC hyD.1, piC_x]
    rw [hxy, ← hkn]
    have : xbar x * (k * xbar x) = k := by
      calc xbar x * (k * xbar x) = k * (xbar x * xbar x) := by
            rw [← mul_assoc, ← xbar_comm x k, mul_assoc]
        _ = k := by rw [hx2, mul_one]
    rw [this]
    exact hk

end Position

section Vertical

open CFSG.ComponentClassification

variable {Y : Type} [Group Y] [Finite Y]

theorem pumpupY_isTwoComponent_of_vertical {s : Y} {Λ : Subgroup Y}
    (hΛC : Λ ≤ centralizer ({s} : Set Y))
    (hΛ : TwoComponents.IsTwoComponent (Λ.subgroupOf (centralizer ({s} : Set Y))))
    (hJsub : (TwoThin.pumpupY Λ).IsSubnormal) {L : Subgroup (TwoThin.barQ Y)}
    (hL : CFSG.IsComponent L) (hΛL : Λ.map (TwoThin.barMk Y) ≤ L)
    (hLJ : L ≤ (TwoThin.pumpupY Λ).map (TwoThin.barMk Y)) :
    TwoComponents.IsTwoComponent (TwoThin.pumpupY Λ) := by
  classical
  have hLtwo : TwoComponents.IsTwoComponent L :=
    TwoLayerTransport.ordinary_isTwoComponent_of_corefree TwoThin.oddCore_barQ L
      ((CFSG.isComponent_iff_open L).mp hL)
  obtain ⟨L', hL'2, hL'map⟩ := OddKernelTwoComponents.exists_lift (TwoThin.barMk Y)
    TwoThin.barMk_surjective TwoThin.odd_card_ker_barMk L hLtwo
  have hJchain : Open.IsSubnormal (TwoThin.pumpupY Λ) ⊤ :=
    Components.chain_of_mathlib_subnormal hJsub
  have hL'J : L' ≤ TwoThin.pumpupY Λ :=
    TwoComponentSubnormal.le_of_odd_kernel_map_le (TwoThin.barMk Y) TwoThin.barMk_surjective
      TwoThin.odd_card_ker_barMk L' (TwoThin.pumpupY Λ) hL'2 hJchain (by rw [hL'map]; exact hLJ)
  have hres := TwoComponentSubnormal.ambient_residual_preimage (TwoThin.barMk Y)
    TwoThin.barMk_surjective TwoThin.odd_card_ker_barMk L' hL'2
  rw [hL'map] at hres
  have hΛPre : Λ ≤ L.comap (TwoThin.barMk Y) := fun a ha => hΛL ⟨a, ha, rfl⟩
  have hΛL' : Λ ≤ L' := by
    let ψ : ↥(Λ.subgroupOf (centralizer ({s} : Set Y))) →* ↥(L.comap (TwoThin.barMk Y)) :=
      { toFun := fun a => ⟨((a : ↥(centralizer ({s} : Set Y))) : Y), hΛPre a.2⟩
        map_one' := rfl
        map_mul' := fun a b => rfl }
    have hres' : TwoResidual.subgroup ↥(Λ.subgroupOf (centralizer ({s} : Set Y))) = ⊤ :=
      TwoComponentConvention.residual_eq_top_of_twoComponent hΛ
    have hmapψ := TwoResidual.map_le ψ
    rw [hres'] at hmapψ
    intro a ha
    have hmem : (⟨a, hΛPre ha⟩ : ↥(L.comap (TwoThin.barMk Y))) ∈
        TwoResidual.subgroup ↥(L.comap (TwoThin.barMk Y)) :=
      hmapψ ⟨⟨⟨a, hΛC ha⟩, Subgroup.mem_subgroupOf.2 ha⟩, Subgroup.mem_top _, rfl⟩
    rw [← hres]
    exact ⟨⟨a, hΛPre ha⟩, hmem, rfl⟩
  have hnorm : ∀ g ∈ TwoLayer.subgroup Y, g ∈ Subgroup.normalizer (L' : Set Y) := by
    intro g hg
    have hg1 : TwoThin.barMk Y g ∈ CFSG.layer (TwoThin.barQ Y) :=
      TwoThin.map_twoLayer_le_layer ⟨g, hg, rfl⟩
    have hg2 : TwoThin.barMk Y g ∈ Layer.subgroup (TwoThin.barQ Y) := by
      rwa [TwoThin.layer_subgroup_eq_layer]
    have hg3 : TwoThin.barMk Y g ∈ Subgroup.normalizer (L : Set (TwoThin.barQ Y)) :=
      ClassicalInvolution.layer_le_normalizer_of_isComponentOf
        ((CFSG.isComponent_iff_open L).mp hL) hg2
    have hg4 : g ∈ Subgroup.normalizer ((L.comap (TwoThin.barMk Y) : Subgroup Y) : Set Y) :=
      Subgroup.le_normalizer_comap (TwoThin.barMk Y) hg3
    have hg5 := TwoResidual.normalizer_le_normalizer (L.comap (TwoThin.barMk Y)) hg4
    rw [hres] at hg5
    exact hg5
  have hJL' : TwoThin.pumpupY Λ ≤ L' := by
    refine TwoThin.pumpupY_le_of_forall fun g hg => ?_
    rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (hnorm g hg) a).1 (hΛL' ha)
  rw [le_antisymm hJL' hL'J]
  exact hL'2

end Vertical

end Thm9S45

section Main

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Generic.S45 CFSG.GH74.L5U5
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.GH74.GLS Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification Thm9S45 Thm9S45Fusion
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup G}

theorem thm9_s45
    (hyp : Hyp2 G) (ht : IsTwoTerminal x K)
    (hP : QShape4 (↥K ⧸ pPrimeCore 2 ↥K) ∨ QShape5 (↥K ⧸ pPrimeCore 2 ↥K)) {y : G}
    (hy : orderOf y = 2) (hyK : y ∈ K ⊔ zpowers x) (hyx : y ≠ x) {H : Subgroup G}
    (hH : IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) H) :
    IsPCompIn 2 (centralizer ({y} : Set G)) (pumpUp 2 H y) ∧
      x ∈ normalizer ((pumpUp 2 H y : Subgroup G) : Set G) := by
  classical
  have _ := hyx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx : orderOf x = 2 := ht.1.1
  have hKC : IsPCompIn 2 (centralizer ({x} : Set G)) K := ht.1.2.2
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hKle : K ⊔ zpowers x ≤ centralizer ({x} : Set G) :=
    sup_le hKC.1 (by rw [zpowers_le]; exact hxC)
  have hyC : y ∈ centralizer ({x} : Set G) := hKle hyK
  have hxy : x ∈ centralizer ({y} : Set G) := TwoThin.mem_centralizer_symm hyC
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy, pow_two] at this
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy; omega
  set W : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) with hW
  have hHX := TwoThin.isPCompIn_two_iff.mp hH
  have hXW : K ⊓ centralizer ({y} : Set G) ≤ W := le_inf (inf_le_left.trans hKC.1) inf_le_right
  have hKsub : (K.subgroupOf (centralizer ({x} : Set G))).IsSubnormal :=
    Components.mathlib_subnormal_of_chain (TwoThin.isPCompIn_two_iff.mp hKC).2.1
      Subgroup.IsSubnormal.top
  have hsub : ((K ⊓ centralizer ({y} : Set G)).subgroupOf W).IsSubnormal := by
    have h1 := TwoThin.isSubnormal_inf_subgroupOf hKsub (inf_le_left : W ≤ centralizer ({x} : Set G))
    have h2 : (K ⊓ centralizer ({y} : Set G)).subgroupOf W = K.subgroupOf W := by
      ext a
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, (Subgroup.mem_inf.mp a.2).2⟩⟩
    rwa [h2]
  have hHU : IsPCompIn 2 W H :=
    TwoThin.isPCompIn_two_iff.mpr ⟨hHX.1.trans hXW,
      TwoComponentTransport.extend_nested H _ W hHX.1 hXW hsub hHX.2⟩
  have hHy : H ≤ centralizer ({y} : Set G) := (hHX.1.trans inf_le_right)
  set Yc : Subgroup G := centralizer ({y} : Set G) with hYc
  have hs : orderOf (⟨x, hxy⟩ : ↥Yc) = 2 := TwoThin.orderOf_mk_centralizer hxy hx
  have hΛC := TwoThin.le_centralizer_mk hHU.1 hxy
  have hΛ2 := TwoThin.isTwoComponent_centralizer_mk hHU hxy
  obtain ⟨hΛE, hJsub, L, hL, hcases, hLJ, hLsJ, hK'⟩ := TwoThin.pumpupY_structure hs hΛC hΛ2
  have hJeq : pumpUp 2 H y = (TwoThin.pumpupY (H.subgroupOf Yc)).map Yc.subtype := by
    rw [TwoThin.pumpUp_eq_map_pumpupY, inf_eq_left.2 hHy, pLayerOf_self hH]
  refine ⟨?_, ?_⟩
  · rcases hcases with ⟨-, hΛL⟩ | ⟨hne, hAB, hdiag⟩
    ·
      have hJ2 := pumpupY_isTwoComponent_of_vertical hΛC hΛ2 hJsub hL hΛL hLJ
      rw [hJeq]
      refine TwoThin.isPCompIn_two_iff.mpr ⟨Subgroup.map_subtype_le _, ?_⟩
      have hcm : ((TwoThin.pumpupY (H.subgroupOf Yc)).map Yc.subtype).subgroupOf Yc =
          TwoThin.pumpupY (H.subgroupOf Yc) :=
        Subgroup.comap_map_eq_self_of_injective Yc.subtype_injective _
      rw [hcm]
      exact hJ2
    ·
      exfalso
      obtain ⟨hd, hKCent⟩ := kbar_data hyp hx hKC hP
      obtain ⟨T, hT⟩ := exists_conf9 hyp.simple hyp.nonab hx hd
      obtain ⟨-, hdich⟩ := piC_mem_or_of_mem_sup hx hKC hyK
      have hyKb : piC x y ∈ S3.imgBar x K := by
        rcases hdich with h | h
        · exact h
        · exfalso
          obtain ⟨g, hg⟩ := hT.exists_conj_x hyC hy2 ⟨mul_mem hxC hyC, h⟩
          exact not_conj_of_components hd hL (isComponent_conjSub hL _) hne.symm ⟨g, hg⟩
      have hyPre : y ∈ Pre x (S3.imgBar x K) := ⟨hyC, hyKb⟩
      obtain ⟨hxy', hcomm⟩ := hT.x_mem_commutator hyp.simple hyp.nonab hx hyPre hy2 hy1
      have hxc : proj y ⟨x, hxy⟩ ∈ _root_.commutator (CentralizerBar y) := by
        have h1 : proj y ⟨x, hxy⟩ ∈ (_root_.commutator ↥(centralizer ({y} : Set G))).map (proj y) :=
          ⟨⟨x, hxy⟩, hcomm, rfl⟩
        have h2 : (_root_.commutator ↥(centralizer ({y} : Set G))).map (proj y) ≤
            _root_.commutator (CentralizerBar y) := by
          rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
          exact Subgroup.commutator_mono le_top le_top
        exact h2 h1
      have hvK : proj x ⟨y, hyC⟩ ∈ S3.imgBar x K := by
        rw [← piC_of_mem x hyC]
        exact hyKb
      have hWsub : (H.subgroupOf W).IsSubnormal :=
        Components.mathlib_subnormal_of_chain (TwoThin.isPCompIn_two_iff.mp hHU).2.1
          Subgroup.IsSubnormal.top
      have hWperf : ⁅H, H⁆ = H :=
        TwoThin.commutator_self_of_isTwoComponent hHU.1 (TwoThin.isPCompIn_two_iff.mp hHU).2
      have hWne : H ≠ ⊥ := by
        intro hbot
        have := TwoThin.ne_bot_of_isTwoComponent (TwoThin.isPCompIn_two_iff.mp hHU).2
        exact this hbot
      exact false_of_diagonal_pumpup_H hx hy hyC hxy hd hKCent hvK hHU.1 hWsub hWperf hWne hxc hL
        hne hAB hdiag
  ·
    have h1 := TwoThin.map_conj_pumpupY_le_of_le_centralizer (H.subgroupOf Yc) hΛC
    have hfwd : ∀ j ∈ pumpUp 2 H y, x * j * x⁻¹ ∈ pumpUp 2 H y := by
      intro j hj
      rw [hJeq] at hj ⊢
      obtain ⟨j', hj', rfl⟩ := hj
      have h2 := h1 ⟨j', hj', rfl⟩
      exact ⟨_, h2, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro j
    constructor
    · exact hfwd j
    · intro hj
      have := hfwd _ hj
      have e : x * (x * j * x⁻¹) * x⁻¹ = j := by
        have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
        rw [hxinv]
        calc x * (x * j * x) * x = (x * x) * j * (x * x) := by group
          _ = j := by rw [hx2]; group
      rwa [e] at this

end Main

end CFSG.GH74.Generic.BProg.B3
