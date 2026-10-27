module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B6Three
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBInputs

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.Common
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open CFSG.EvenSmallLie.UnitarySix.YamadaD (oTwo le_oTwo oTwo_le isPGroup_oTwo
  le_normalizer_oTwo)
open scoped Matrix MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem B₆_eq_oTwo (d : Data G h) :
    d.B₆ = oTwo (normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G)) :=
  pCore_map_eq_oTwo _

theorem Hyp.FB₃_le_normalizer_F (hd : d.Hyp) : d.F ⊔ d.B₃ ≤ normalizer (d.F : Set G) :=
  sup_le le_normalizer hd.B₃_le_normalizer_F

theorem Hyp.FA₃_le_normalizer_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.F ⊔ d.A₃ ≤ normalizer (d.F : Set G) :=
  sup_le le_normalizer (hd.A₃_le_normalizer_F hGMS)

theorem Hyp.B₆_eq_lift (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.B₆ = lift (oTwo (HB d)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [B₆_eq_oTwo]
  have hHN := hd.normalizer_FB₃_le_normalizer_F hGMS
  have hFH : d.F ≤ normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G) :=
    le_sup_left.trans le_normalizer
  have hFS : d.F ≤ oTwo (normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G)) :=
    le_oTwo hFH hHN hd.isPGroup_F
  refine le_antisymm (fun x hx => ?_) (le_oTwo ?_ (fun g hg => ?_)
    (isPGroup_lift hd.isPGroup_F (isPGroup_oTwo _)))
  · have hxN := hHN (oTwo_le _ hx)
    refine mem_lift_of_proj_mem (x := ⟨x, hxN⟩) ?_
    exact le_oTwo (bar_mono (oTwo_le _)) (bar_le_normalizer_bar hFS (le_normalizer_oTwo _))
      (isPGroup_bar (isPGroup_oTwo _)) (proj_mem_bar hx)
  · calc lift (oTwo (HB d)) ≤ lift (HB d) := lift_mono (oTwo_le _)
      _ = normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G) := lift_bar hFH hHN
  · exact mem_normalizer_lift_of_proj (g := ⟨g, hHN hg⟩) (le_normalizer_oTwo _ (proj_mem_bar hg))

theorem B₆_le_normalizer (d : Data G h) :
    d.B₆ ≤ normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G) := by
  rw [B₆_eq_oTwo]
  exact oTwo_le _

theorem Hyp.B₆_le_normalizer_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.B₆ ≤ normalizer (d.F : Set G) :=
  d.B₆_le_normalizer.trans (hd.normalizer_FB₃_le_normalizer_F hGMS)

theorem isPGroup_B₆ (d : Data G h) : IsPGroup 2 d.B₆ := by
  rw [B₆_eq_oTwo]
  exact isPGroup_oTwo _

theorem Hyp.FB₃_le_B₆ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.F ⊔ d.B₃ ≤ d.B₆ := by
  obtain ⟨-, h3, -, -⟩ := hd.two_core_bar hGMS
  intro x hx
  rw [hd.B₆_eq_lift hGMS]
  refine mem_lift_of_proj_mem (x := ⟨x, hd.FB₃_le_normalizer_F hx⟩) ?_
  have : proj d.F ⟨x, hd.FB₃_le_normalizer_F hx⟩ ∈ BB d := proj_mem_bar hx
  rw [← h3] at this
  exact (Subgroup.mem_inf.1 this).1

theorem Hyp.commutator_B₆_FA₃_mem_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {s x : G} (hs : s ∈ d.B₆) (hx : x ∈ d.F ⊔ d.A₃) : s * x * s⁻¹ * x⁻¹ ∈ d.F := by
  obtain ⟨h1, -, -, -⟩ := hd.two_core_bar hGMS
  rw [hd.B₆_eq_lift hGMS] at hs
  obtain ⟨hsN, hsO⟩ := mem_lift_iff.1 hs
  have hxN := hd.FA₃_le_normalizer_F hGMS hx
  have hcomm := mem_centralizer_iff.1 (h1 hsO) _ (proj_mem_bar (x := ⟨x, hxN⟩) hx)
  have h2 : proj d.F (⟨s, hsN⟩ * ⟨x, hxN⟩ * ⟨s, hsN⟩⁻¹ * ⟨x, hxN⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm, mul_inv_cancel_right,
      mul_inv_cancel]
  exact proj_eq_one_iff.1 h2

theorem Hyp.mem_FB₃_of_mem_B₆ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {s : G} (hs : s ∈ d.B₆) (hst : (s * d.t)⁻¹ * (d.t * s) ∈ d.F) : s ∈ d.F ⊔ d.B₃ := by
  obtain ⟨-, h3, -, -⟩ := hd.two_core_bar hGMS
  rw [hd.B₆_eq_lift hGMS] at hs
  obtain ⟨hsN, hsO⟩ := mem_lift_iff.1 hs
  have : proj d.F ⟨s, hsN⟩ ∈ BB d := by
    rw [← h3]
    refine Subgroup.mem_inf.2 ⟨hsO, mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, proj_eq_proj_iff]
    exact hst
  exact (mem_bar_iff le_sup_left _).1 this

theorem Hyp.exists_mul_B₆_of_mem_normalizer (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) {g : G} (hg : g ∈ normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G)) :
    ∃ c ∈ normalizer (d.B₃ : Set G) ⊓ centralizer ({d.t} : Set G), ∃ s ∈ d.B₆, g = c * s := by
  obtain ⟨-, -, -, h5⟩ := hd.two_core_bar hGMS
  have hgF := hd.normalizer_FB₃_le_normalizer_F hGMS hg
  obtain ⟨cb, hcb, ob, hob, hgco⟩ := h5 _ (proj_mem_bar (x := ⟨g, hgF⟩) hg)
  obtain ⟨c, hc, hcF, rfl⟩ := hd.exists_proj_eq_of_mem_HB hGMS hcb
  obtain ⟨s₀, rfl⟩ := proj_surjective ob
  have hs₀ : (s₀ : G) ∈ d.B₆ := by
    rw [hd.B₆_eq_lift hGMS]
    exact mem_lift_of_proj_mem hob
  rw [← map_mul, proj_eq_proj_iff] at hgco
  change g⁻¹ * (c * s₀) ∈ d.F at hgco
  have hfB : (g⁻¹ * (c * s₀))⁻¹ ∈ d.B₆ := hd.FB₃_le_B₆ hGMS (mem_sup_left (inv_mem hgco))
  exact ⟨c, Subgroup.mem_inf.2 ⟨hd.normalizer_B₁_le hc.1, hc.2⟩, s₀ * (g⁻¹ * (c * s₀))⁻¹,
    mul_mem hs₀ hfB, by group⟩

theorem Hyp.card_B₆ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    Nat.card d.B₆ = (2 ^ f) ^ 4 * Nat.card (d.F ⊔ d.B₃ : Subgroup G) := by
  obtain ⟨h1, h3, h4, -⟩ := hd.two_core_bar hGMS
  have hc := hd.cosetData_bar hGMS
  have hBO : BB d ≤ oTwo (HB d) := by
    rw [← h3]
    exact inf_le_left
  have : ((BB d).subgroupOf (oTwo (HB d))).Normal := hc.normal_subgroupOf (oTwo_le _) h1 h3
  obtain ⟨φ, -, -⟩ := hc.exists_mulEquiv_quotient (oTwo_le _) h1 h3 h4
  have hY : Nat.card (YB d) = (2 ^ f) ^ 4 := by
    rw [← Nat.card_congr (hd.ιB hGMS).toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, h.card_eq_sq, ← pow_mul]
  have hq : Nat.card (oTwo (HB d) ⧸ (BB d).subgroupOf (oTwo (HB d))) = (2 ^ f) ^ 4 := by
    rw [Nat.card_congr φ.toEquiv, hY]
  have hOcard : Nat.card (oTwo (HB d)) = (2 ^ f) ^ 4 * Nat.card (BB d) := by
    rw [← hq, ← Nat.card_congr (subgroupOfEquivOfLe hBO).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  rw [hd.B₆_eq_lift hGMS, card_lift, hOcard, mul_assoc,
    card_bar_mul le_sup_left hd.FB₃_le_normalizer_F]

omit [Finite G] in
instance normal_A₁_subgroupOf_A₃ (d : Data G h) : (d.A₁.subgroupOf d.A₃).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [mem_subgroupOf] at hx ⊢
  obtain ⟨v, hv, hvx⟩ := hx
  obtain ⟨s, hs, hsg⟩ := g.2
  have hc : s * v = v * s := (central_Ssub_iff (Vsub_le_Ssub hv)).2 hv s hs
  have e : (g : G) * x * (g : G)⁻¹ = x := by
    rw [← hvx, ← hsg, ← map_inv, ← map_mul, ← map_mul, hc, mul_inv_cancel_right]
  simp only [coe_mul, coe_inv, e]
  exact ⟨v, hv, hvx⟩

theorem Hyp.exists_A₃_equiv (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    ∃ θ : d.A₃ ⧸ d.A₁.subgroupOf d.A₃ ≃* YB d, ∀ a : d.A₃,
      (θ (QuotientGroup.mk a) : Bar d.F) = proj d.F ⟨a, hd.A₃_le_normalizer_F hGMS a.2⟩ := by
  let θ₀ : d.A₃ →* YB d :=
    { toFun := fun a => ⟨proj d.F ⟨a, hd.A₃_le_normalizer_F hGMS a.2⟩,
        proj_mem_bar (mem_sup_right a.2)⟩
      map_one' := by
        apply Subtype.ext
        change proj d.F ⟨1, _⟩ = 1
        exact proj_eq_one_iff.2 (one_mem _)
      map_mul' := fun a b => by
        apply Subtype.ext
        change proj d.F ⟨(a : G) * b, _⟩ = proj d.F ⟨a, _⟩ * proj d.F ⟨b, _⟩
        rw [← map_mul]
        rfl }
  have hker : θ₀.ker = d.A₁.subgroupOf d.A₃ := by
    ext a
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← hd.F_inf_A₃ hGMS]
    constructor
    · intro e
      exact Subgroup.mem_inf.2 ⟨proj_eq_one_iff.1 (congrArg Subtype.val e), a.2⟩
    · intro e
      exact Subtype.ext (proj_eq_one_iff.2 (Subgroup.mem_inf.1 e).1)
  have hsurj : Function.Surjective θ₀ := by
    rintro ⟨y, hy⟩
    obtain ⟨⟨x, hxN⟩, hx, rfl⟩ := exists_proj_of_mem_bar hy
    obtain ⟨y₁, hy₁, a, ha, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_normalizer (hd.A₃_le_normalizer_F hGMS) hx
    refine ⟨⟨a, ha⟩, Subtype.ext ?_⟩
    change proj d.F ⟨a, _⟩ = proj d.F ⟨y₁ * a, hxN⟩
    rw [proj_eq_proj_iff]
    change a⁻¹ * (y₁ * a) ∈ d.F
    have := (mem_normalizer_iff.1 (inv_mem (hd.A₃_le_normalizer_F hGMS ha)) y₁).1 hy₁
    rw [inv_inv] at this
    rw [← mul_assoc]
    exact this
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective θ₀ hsurj), fun a => rfl⟩

theorem Hyp.exists_B₆_hom (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    ∃ ψ : d.B₆ →* d.A₃ ⧸ d.A₁.subgroupOf d.A₃, Function.Surjective ψ ∧
      ψ.ker = (d.F ⊔ d.B₃).subgroupOf d.B₆ ∧
      (∀ (s : d.B₆) (a : d.A₃), ∀ y ∈ d.F, (s : G)⁻¹ * d.t * s * d.t = y * a →
        ψ s = QuotientGroup.mk a) ∧
      ∀ c ∈ normalizer (d.B₃ : Set G) ⊓ centralizer ({d.t} : Set G), ∀ (s : d.B₆) (a : d.A₃)
        (hs : c * s * c⁻¹ ∈ d.B₆) (ha : c * a * c⁻¹ ∈ d.A₃),
        ψ s = QuotientGroup.mk a → ψ ⟨c * s * c⁻¹, hs⟩ = QuotientGroup.mk ⟨c * a * c⁻¹, ha⟩ := by
  obtain ⟨h1, -, h4, -⟩ := hd.two_core_bar hGMS
  have hc := hd.cosetData_bar hGMS
  have htinv : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right hd.t_mul_t
  obtain ⟨θ, hθ⟩ := hd.exists_A₃_equiv hGMS
  have hB₆N := hd.B₆_le_normalizer_F hGMS
  have hB₆L : d.B₆ ≤ lift (oTwo (HB d)) := (hd.B₆_eq_lift hGMS).le
  have hB₆O : ∀ s : d.B₆, proj d.F ⟨s, hB₆N s.2⟩ ∈ oTwo (HB d) := fun s =>
    proj_mem_of_mem_lift (hB₆L s.2)
  let π : d.B₆ →* oTwo (HB d) :=
    ((proj d.F).comp (Subgroup.inclusion hB₆N)).codRestrict _ hB₆O
  let χ : oTwo (HB d) →* YB d := CFSG.EvenSmallLie.UnitarySix.YamadaD.crossedHom hc.mul_self
    (YB d) (oTwo (HB d)) h1 fun o ho => hc.crossed_mem o (oTwo_le _ ho)
  have hcrN : ∀ s : d.B₆, (s : G)⁻¹ * d.t * s * d.t ∈ normalizer (d.F : Set G) := fun s =>
    mul_mem (mul_mem (mul_mem (inv_mem (hB₆N s.2)) hd.t_mem_normalizer_F) (hB₆N s.2))
      hd.t_mem_normalizer_F
  have hχπ : ∀ s : d.B₆, ((χ (π s) : YB d) : Bar d.F) = proj d.F ⟨_, hcrN s⟩ := by
    intro s
    rw [CFSG.EvenSmallLie.UnitarySix.YamadaD.crossedHom_apply]
    change (proj d.F ⟨s, hB₆N s.2⟩)⁻¹ * hd.tB * proj d.F ⟨s, hB₆N s.2⟩ * hd.tB = _
    rw [Hyp.tB, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  let ψ : d.B₆ →* d.A₃ ⧸ d.A₁.subgroupOf d.A₃ := θ.symm.toMonoidHom.comp (χ.comp π)
  have hψ : ∀ (s : d.B₆) (a : d.A₃), ψ s = QuotientGroup.mk a ↔
      ((s : G)⁻¹ * d.t * s * d.t)⁻¹ * a ∈ d.F := by
    intro s a
    change θ.symm (χ (π s)) = QuotientGroup.mk a ↔ _
    rw [MulEquiv.symm_apply_eq, Subtype.ext_iff, hθ, hχπ, proj_eq_proj_iff]
  refine ⟨ψ, ?_, ?_, fun s a y hy hsy => (hψ s a).2 ?_, fun c hc' s a hs ha hsa => ?_⟩
  ·
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    have haY : proj d.F ⟨a, hd.A₃_le_normalizer_F hGMS a.2⟩ ∈ YB d :=
      proj_mem_bar (mem_sup_right a.2)
    obtain ⟨o, ho, hot⟩ := h4 _ haY
    obtain ⟨s₀, rfl⟩ := proj_surjective o
    have hs₀ : (s₀ : G) ∈ d.B₆ := by
      rw [hd.B₆_eq_lift hGMS]
      exact mem_lift_of_proj_mem ho
    refine ⟨⟨s₀, hs₀⟩, (hψ _ a).2 ?_⟩
    rw [Hyp.tB, ← map_inv, ← map_mul, ← map_mul, ← map_mul, proj_eq_proj_iff] at hot
    change ((s₀ : G)⁻¹ * d.t * s₀)⁻¹ * (d.t * a) ∈ d.F at hot
    change ((s₀ : G)⁻¹ * d.t * s₀ * d.t)⁻¹ * a ∈ d.F
    have hta : d.t * a = a * d.t := (hd.comm_t (d.A₃_le_P.trans d.P_le_L a.2)).symm
    rw [hta] at hot
    have e : ((s₀ : G)⁻¹ * d.t * s₀ * d.t)⁻¹ * a =
        d.t * (((s₀ : G)⁻¹ * d.t * s₀)⁻¹ * (a * d.t)) * d.t⁻¹ := by
      calc ((s₀ : G)⁻¹ * d.t * s₀ * d.t)⁻¹ * a = d.t⁻¹ * (((s₀ : G)⁻¹ * d.t * s₀)⁻¹ * a) := by
            group
        _ = d.t * (((s₀ : G)⁻¹ * d.t * s₀)⁻¹ * a) := by rw [htinv]
        _ = d.t * (((s₀ : G)⁻¹ * d.t * s₀)⁻¹ * (a * d.t)) * d.t⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 hd.t_mem_normalizer_F _).1 hot
  ·
    ext s
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    have e1 : ψ s = 1 ↔ ψ s = QuotientGroup.mk (1 : d.A₃) := by rw [QuotientGroup.mk_one]
    rw [e1, hψ, Subgroup.coe_one, mul_one, inv_mem_iff]
    constructor
    · intro hst
      refine hd.mem_FB₃_of_mem_B₆ hGMS s.2 ?_
      have e : ((s : G) * d.t)⁻¹ * (d.t * s) = d.t * ((s : G)⁻¹ * d.t * s * d.t) * d.t⁻¹ := by
        calc ((s : G) * d.t)⁻¹ * (d.t * s) = d.t⁻¹ * ((s : G)⁻¹ * d.t * s) := by group
          _ = d.t * ((s : G)⁻¹ * d.t * s) := by rw [htinv]
          _ = d.t * ((s : G)⁻¹ * d.t * s * d.t) * d.t⁻¹ := by group
      rw [e]
      exact (mem_normalizer_iff.1 hd.t_mem_normalizer_F _).1 hst
    · intro hs
      have := hd.elemAbMod_F_FB₃.2 _ (inv_mem hs) _ d.t_mem_FB₃
      rw [commutatorElement_def, htinv, inv_inv] at this
      exact this
  ·
    rw [hsy, mul_inv_rev]
    have := (mem_normalizer_iff.1 (inv_mem (hd.A₃_le_normalizer_F hGMS a.2)) _).1 (inv_mem hy)
    rwa [inv_inv] at this
  ·
    have hcF : c ∈ normalizer (d.F : Set G) :=
      hd.normalizer_B₁_le_normalizer_F hGMS (hd.normalizer_B₃_le hc'.1)
    rw [hψ] at hsa ⊢
    change ((c * s * c⁻¹)⁻¹ * d.t * (c * s * c⁻¹) * d.t)⁻¹ * (c * a * c⁻¹) ∈ d.F
    rw [CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj (mem_centralizer_singleton_iff.1 hc'.2)]
    have := (mem_normalizer_iff.1 hcF _).1 hsa
    rwa [show c * (((s : G)⁻¹ * d.t * s * d.t)⁻¹ * a) * c⁻¹ =
      (c * ((s : G)⁻¹ * d.t * s * d.t) * c⁻¹)⁻¹ * (c * a * c⁻¹) by group] at this

theorem Hyp.sec3_7 (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.F ⊔ d.B₃ ≤ d.B₆ ∧
      (∀ g ∈ normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G),
        ∃ c ∈ normalizer (d.B₃ : Set G) ⊓ centralizer ({d.t} : Set G), ∃ s ∈ d.B₆, g = c * s) ∧
      Nat.card d.B₆ = (2 ^ f) ^ 4 * Nat.card (d.F ⊔ d.B₃ : Subgroup G) ∧
      (∀ s ∈ d.B₆, ∀ x ∈ d.F ⊔ d.A₃, s * x * s⁻¹ * x⁻¹ ∈ d.F) ∧
      ∃ ψ : d.B₆ →* d.A₃ ⧸ d.A₁.subgroupOf d.A₃, Function.Surjective ψ ∧
        ψ.ker = (d.F ⊔ d.B₃).subgroupOf d.B₆ ∧
        (∀ (s : d.B₆) (a : d.A₃), ∀ y ∈ d.F, (s : G)⁻¹ * d.t * s * d.t = y * a →
          ψ s = QuotientGroup.mk a) ∧
        ∀ c ∈ normalizer (d.B₃ : Set G) ⊓ centralizer ({d.t} : Set G), ∀ (s : d.B₆) (a : d.A₃)
          (hs : c * s * c⁻¹ ∈ d.B₆) (ha : c * a * c⁻¹ ∈ d.A₃),
          ψ s = QuotientGroup.mk a →
            ψ ⟨c * s * c⁻¹, hs⟩ = QuotientGroup.mk ⟨c * a * c⁻¹, ha⟩ :=
  ⟨hd.FB₃_le_B₆ hGMS, fun _ hg => hd.exists_mul_B₆_of_mem_normalizer hGMS hg, hd.card_B₆ hGMS,
    fun _ hs _ hx => hd.commutator_B₆_FA₃_mem_F hGMS hs hx, hd.exists_B₆_hom hGMS⟩

end Data

end CFSG.LocalAnalysis.EvenBN.U5
