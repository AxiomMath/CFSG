module

public import CFSG.GH74.Generic.S45.LVert
public import CFSG.GH74.Generic.S45.LDiagPerm
public import CFSG.GH74.Generic.S45.LDiagStruct
public import CFSG.GH74.GLS.TwoThin.PumpData
public import CFSG.GH74.Generic.S45.PumpC2

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.ABGLocalTools CFSG.Blueprint CFSG.GH74.GLS Subgroup
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Small

theorem diag_isPerfect {F : Type} [Group F] (hs : IsSimpleGroup F) (hnab : ∃ a b : F, a * b ≠ b * a) :
    Group.IsPerfect F := by
  refine ⟨?_⟩
  rcases hs.eq_bot_or_eq_top_of_normal (commutator F) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (((commutator_eq_bot_iff F).1 h).is_comm.comm a b)
  · exact h

theorem diag_isQuasisimple {F : Type} [Group F] (hs : IsSimpleGroup F) (hnab : ∃ a b : F, a * b ≠ b * a) :
    CFSG.IsQuasisimple F := by
  have hperf : Group.IsPerfect F := diag_isPerfect hs hnab
  have hcenter : Subgroup.center F = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center F) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  let e : F ⧸ Subgroup.center F ≃* F :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  refine ⟨hperf, MulEquiv.isSimpleGroup e, ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this

theorem comm_of_ne_components {Z : Type} [Group Z] [Finite Z] {M₁ M₂ : Subgroup Z} (h₁ : IsComponent M₁)
    (h₂ : IsComponent M₂) (hne : M₁ ≠ M₂) : ∀ a ∈ M₁, ∀ b ∈ M₂, a * b = b * a := by
  intro a ha b hb
  rcases CFSG.LocalCores.distinct_components_commute h₁ h₂ with h | h
  · exact absurd h hne
  · have := Subgroup.commutator_mem_commutator ha hb
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this

theorem comm_sup_sup {Z : Type} [Group Z] {B B' L L' : Subgroup Z}
    (h₁ : ∀ b ∈ B, ∀ l ∈ L, b * l = l * b) (h₂ : ∀ b ∈ B, ∀ l ∈ L', b * l = l * b)
    (h₃ : ∀ b ∈ B', ∀ l ∈ L, b * l = l * b) (h₄ : ∀ b ∈ B', ∀ l ∈ L', b * l = l * b) :
    ∀ y ∈ B ⊔ B', ∀ z ∈ L ⊔ L', y * z = z * y := by
  intro y hy z hz
  have hLy : ∀ l ∈ L, l ∈ centralizer ({y} : Set Z) := by
    intro l hl
    have : B ⊔ B' ≤ centralizer ({l} : Set Z) :=
      sup_le (fun b hb => mem_centralizer_singleton_iff.2 (h₁ b hb l hl))
        (fun b hb => mem_centralizer_singleton_iff.2 (h₃ b hb l hl))
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 (this hy)).symm
  have hL'y : ∀ l ∈ L', l ∈ centralizer ({y} : Set Z) := by
    intro l hl
    have : B ⊔ B' ≤ centralizer ({l} : Set Z) :=
      sup_le (fun b hb => mem_centralizer_singleton_iff.2 (h₂ b hb l hl))
        (fun b hb => mem_centralizer_singleton_iff.2 (h₄ b hb l hl))
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 (this hy)).symm
  have : L ⊔ L' ≤ centralizer ({y} : Set Z) := sup_le hLy hL'y
  exact (mem_centralizer_singleton_iff.1 (this hz)).symm

end Small

section Diagonal

variable {G : Type} [Group G] [Finite G]

theorem false_of_diagonal_pumpup {x v : G} (hxord : orderOf x = 2) (hvord : orderOf v = 2)
    (hvx : v ∈ centralizer ({x} : Set G)) (hxv : x ∈ centralizer ({v} : Set G))
    {K : Subgroup (CentralizerBar x)} (hd : KData (CentralizerBar x) K (xbar x)) (hKC : KCent ↥K)
    (hvK : proj x ⟨v, hvx⟩ ∈ K)
    {W : Subgroup G} (hWY : W ≤ centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G))
    (hWn : (W.subgroupOf (centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G))).Normal)
    (hWs : IsSimpleGroup ↥W) (hWnab : ∃ a b : ↥W, a * b ≠ b * a)
    {e : G} (heW : e ∈ W) (he2 : e * e = 1) (he1 : e ≠ 1)
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
  have hWUn : (W.subgroupOf X₀).Normal := hWn
  let eW : ↥(W.subgroupOf X₀) ≃* ↥W := Subgroup.subgroupOfEquivOfLe hWY
  have hWsU : IsSimpleGroup ↥(W.subgroupOf X₀) := (MulEquiv.isSimpleGroup_congr eW).2 hWs
  have hWnabU : ∃ a b : ↥(W.subgroupOf X₀), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hWnab
    refine ⟨eW.symm a, eW.symm b, fun h => hab ?_⟩
    have := congrArg eW h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  have hWperf : ⁅W.subgroupOf X₀, W.subgroupOf X₀⁆ = W.subgroupOf X₀ :=
    Subgroup.isPerfect_iff.1 (diag_isPerfect hWsU hWnabU)
  let eU : ↥X₀ := ⟨e, hWY heW⟩
  have heU : eU ∈ W.subgroupOf X₀ := heW
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
  have hQW : Q.map f₁ ≤ (W.subgroupOf X₀).map f₁ :=
    map_perfect_le_map_of_KCent hd hKC f₁ hvK ht1ord hfc hsurj hWperf heU hfe hQperf
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
    eq_bot_of_perfect_comm_ker f₁ f₂ h₁ h₂ hWsU hWnabU heU heU2 heU1 hQperf hQW hcomm
  apply hΔne
  rw [← hQmap, hQ0, Subgroup.map_bot]

end Diagonal

section Final

variable {G : Type} [Group G] [Finite G]

theorem diag_isPCompIn {V B : Subgroup G} (hBV : B ≤ V) (hsub : (B.subgroupOf V).IsSubnormal)
    (hq : IsQuasisimple ↥B) : IsPCompIn 2 V B := by
  have hcomp : IsComponent (B.subgroupOf V) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hBV).symm hq, hsub⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCO : Group.IsSolvable (pPrimeCore 2 ↥V) := by
    apply CFSG.FeitThompson.isSolvable_of_odd_natCard _
    have := pPrimeCore_coprime_card (p := 2) (G := ↥V)
    exact (Nat.coprime_two_left.1 this)
  exact ⟨hBV, isPComponent_of_isComponent_of_not_le 2 hcomp
    (not_le_of_isComponent_of_isSolvable hcomp hCO)⟩

end Final

theorem b_S45_vertical_of_III8
    (hK : B_S45_KFacts) (h63 : B_III8_6_3) : B_S45_vertical := by
  intro G _ _ hs hn hgen hKGH x hx K hKc hj hnot T hT v hvT hvK hv1 W hWY hWn hWs hWnab hWL
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvx : v ∈ centralizer ({x} : Set G) := hvK.1
  have hv2 : v * v = 1 := hT.sq v hvT
  have hvord : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1
  have hTv : T ≤ centralizer ({v} : Set G) := fun t ht => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hT.comm t ht v hvT
  have hxv : x ∈ centralizer ({v} : Set G) := hTv hT.x_mem
  obtain ⟨hE4, -⟩ := hT.exists_normalizing_in_W hvT hvK hv1 W hWY hWn hWs hWnab
  obtain ⟨e, heE, he1⟩ : ∃ e ∈ T ⊓ W, e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : T ⊓ W = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [h1, Subgroup.card_bot] at hE4
    omega
  have he2 : e * e = 1 := hT.sq e heE.1
  have hcent := hT.exists_two_central hvT hvK hv1
  obtain ⟨hxv', hxcomm⟩ := h63 G hs hn x hx T hT.sylow v hvT (fun p hp => hT.comm p hp v hvT) hvord
    hcent (fun g hg _ => hT.controls_fusion hvT hvK hv1 g hg)
  have hxc : proj v ⟨x, hxv⟩ ∈ _root_.commutator (CentralizerBar v) := by
    have h1 : proj v ⟨x, hxv⟩ ∈ (_root_.commutator ↥(centralizer ({v} : Set G))).map (proj v) :=
      ⟨⟨x, hxv⟩, hxcomm, rfl⟩
    have h2 : (_root_.commutator ↥(centralizer ({v} : Set G))).map (proj v) ≤
        _root_.commutator (CentralizerBar v) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact h2 h1
  have hd : KData (CentralizerBar x) K (xbar x) :=
    { gen4 := gen4_centralizerBar hgen x
      oddcore := pPrimeCore_quotient_pPrimeCore_eq_bot _ 2
      central := fun g => xbar_comm x g
      sq := xbar_mul_self hx
      ne := xbar_ne_one hx
      comp := hKc
      notin := hnot
      facts := hK ↥K hj }
  have hKC : KCent ↥K := kCent_of_isJ1OrRee hj
  have hvK' : proj x ⟨v, hvx⟩ ∈ K := by
    have := hvK.2
    rwa [piC_of_mem x hvx] at this
  have hWq : IsQuasisimple ↥W := diag_isQuasisimple hWs hWnab
  have hPC : IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G)) W :=
    diag_isPCompIn hWY hWn.isSubnormal hWq
  have hs' : orderOf (⟨x, hxv⟩ : ↥(centralizer ({v} : Set G))) = 2 :=
    TwoThin.orderOf_mk_centralizer hxv hx
  have hΛC := TwoThin.le_centralizer_mk hPC.1 hxv
  have hΛ := TwoThin.isTwoComponent_centralizer_mk hPC hxv
  obtain ⟨-, -, L, hL, hcases, -⟩ := TwoThin.pumpupY_structure hs' hΛC hΛ
  rcases hcases with ⟨-, hle⟩ | ⟨hne, hAB, hle⟩
  · exact ⟨L, hL, hle⟩
  · exact (false_of_diagonal_pumpup hx hvord hvx hxv hd hKC hvK' hWY hWn hWs hWnab heE.2 he2 he1 hxc
      hL hne hAB hle).elim

end CFSG.GH74.Generic.S45
