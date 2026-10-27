module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyStatements
public import CFSG.LocalAnalysis.SectionRank.Induction
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG CFSG.LocalCores

section CentralProduct

variable {Y : Type*} [Group Y] {N₁ N₂ : Subgroup Y}

theorem exists_mul_of_mem_sup (hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x) {v : Y}
    (hv : v ∈ N₁ ⊔ N₂) : ∃ x ∈ N₁, ∃ y ∈ N₂, v = x * y := by
  let S : Subgroup Y :=
    { carrier := {v | ∃ x ∈ N₁, ∃ y ∈ N₂, v = x * y}
      one_mem' := ⟨1, N₁.one_mem, 1, N₂.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨x₁, hx₁, y₁, hy₁, rfl⟩ ⟨x₂, hx₂, y₂, hy₂, rfl⟩
        refine ⟨x₁ * x₂, N₁.mul_mem hx₁ hx₂, y₁ * y₂, N₂.mul_mem hy₁ hy₂, ?_⟩
        calc x₁ * y₁ * (x₂ * y₂) = x₁ * (y₁ * x₂) * y₂ := by group
          _ = x₁ * (x₂ * y₁) * y₂ := by rw [← hcomm x₂ hx₂ y₁ hy₁]
          _ = x₁ * x₂ * (y₁ * y₂) := by group
      inv_mem' := by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        refine ⟨x⁻¹, N₁.inv_mem hx, y⁻¹, N₂.inv_mem hy, ?_⟩
        calc (x * y)⁻¹ = y⁻¹ * x⁻¹ := mul_inv_rev x y
          _ = x⁻¹ * y⁻¹ := by
            have h := hcomm x⁻¹ (N₁.inv_mem hx) y⁻¹ (N₂.inv_mem hy)
            exact h.symm }
  have hle : N₁ ⊔ N₂ ≤ S := sup_le (fun x hx => ⟨x, hx, 1, N₂.one_mem, (mul_one x).symm⟩)
    (fun y hy => ⟨1, N₁.one_mem, y, hy, (one_mul y).symm⟩)
  exact hle hv

@[expose] def mulHomSup (hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x) :
    ↥N₁ × ↥N₂ →* ↥(N₁ ⊔ N₂) where
  toFun p := ⟨(p.1 : Y) * p.2,
    Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    show ((a.1 : Y) * b.1) * ((a.2 : Y) * b.2) = ((a.1 : Y) * a.2) * ((b.1 : Y) * b.2)
    calc ((a.1 : Y) * b.1) * ((a.2 : Y) * b.2) = (a.1 : Y) * (b.1 * a.2) * b.2 := by group
      _ = (a.1 : Y) * (a.2 * b.1) * b.2 := by rw [← hcomm b.1 b.1.2 a.2 a.2.2]
      _ = ((a.1 : Y) * a.2) * ((b.1 : Y) * b.2) := by group

theorem mulHomSup_surjective (hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x) :
    Function.Surjective (mulHomSup hcomm) := by
  rintro ⟨v, hv⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup hcomm hv
  exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩

theorem ker_mulHomSup_quotient (hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x) :
    ((QuotientGroup.mk' (Subgroup.center ↥(N₁ ⊔ N₂))).comp (mulHomSup hcomm)).ker =
      (Subgroup.center ↥N₁).prod (Subgroup.center ↥N₂) := by
  ext ⟨x, y⟩
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_prod, Subgroup.mem_center_iff, Subgroup.mem_center_iff,
    Subgroup.mem_center_iff]
  constructor
  · intro h
    refine ⟨fun n => ?_, fun n => ?_⟩
    · have h1 := h ⟨(n : Y), Subgroup.mem_sup_left n.2⟩
      have h2 : (n : Y) * ((x : Y) * y) = ((x : Y) * y) * n := congrArg Subtype.val h1
      have h3 : (y : Y) * n = n * y := (hcomm n n.2 y y.2).symm
      apply Subtype.ext
      show (n : Y) * x = x * n
      calc (n : Y) * x = ((n : Y) * (x * y)) * (y : Y)⁻¹ := by group
        _ = (((x : Y) * y) * n) * (y : Y)⁻¹ := by rw [h2]
        _ = (x : Y) * (y * n) * (y : Y)⁻¹ := by group
        _ = (x : Y) * (n * y) * (y : Y)⁻¹ := by rw [h3]
        _ = x * n := by group
    · have h1 := h ⟨(n : Y), Subgroup.mem_sup_right n.2⟩
      have h2 : (n : Y) * ((x : Y) * y) = ((x : Y) * y) * n := congrArg Subtype.val h1
      have h3 : (x : Y) * n = n * x := hcomm x x.2 n n.2
      apply Subtype.ext
      show (n : Y) * y = y * n
      calc (n : Y) * y = (x : Y)⁻¹ * ((x : Y) * n) * y := by group
        _ = (x : Y)⁻¹ * (n * x) * y := by rw [h3]
        _ = (x : Y)⁻¹ * (n * (x * y)) := by group
        _ = (x : Y)⁻¹ * ((x * y) * n) := by rw [h2]
        _ = y * n := by group
  · rintro ⟨hx, hy⟩ g
    obtain ⟨g, hg⟩ := g
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm hg
    apply Subtype.ext
    have hxa : (a : Y) * x = x * a := congrArg Subtype.val (hx ⟨a, ha⟩)
    have hyb : (b : Y) * y = y * b := congrArg Subtype.val (hy ⟨b, hb⟩)
    have hxb : (x : Y) * b = b * x := hcomm x x.2 b hb
    have hay : (a : Y) * y = y * a := hcomm a ha y y.2
    show (a * b) * ((x : Y) * y) = ((x : Y) * y) * (a * b)
    calc (a * b) * ((x : Y) * y) = a * (b * x) * y := by group
      _ = a * (x * b) * y := by rw [← hxb]
      _ = (a * x) * (b * y) := by group
      _ = (x * a) * (y * b) := by rw [hxa, hyb]
      _ = x * (a * y) * b := by group
      _ = x * (y * a) * b := by rw [hay]
      _ = ((x : Y) * y) * (a * b) := by group

theorem centralProductQuotientEquiv (hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x) :
    Nonempty ((↥N₁ ⧸ Subgroup.center ↥N₁) × (↥N₂ ⧸ Subgroup.center ↥N₂) ≃*
      ↥(N₁ ⊔ N₂) ⧸ Subgroup.center ↥(N₁ ⊔ N₂)) := by
  let Φ := (QuotientGroup.mk' (Subgroup.center ↥(N₁ ⊔ N₂))).comp (mulHomSup hcomm)
  let Ψ : ↥N₁ × ↥N₂ →* (↥N₁ ⧸ Subgroup.center ↥N₁) × (↥N₂ ⧸ Subgroup.center ↥N₂) :=
    (QuotientGroup.mk' (Subgroup.center ↥N₁)).prodMap (QuotientGroup.mk' (Subgroup.center ↥N₂))
  have hΦ : Function.Surjective Φ :=
    (QuotientGroup.mk'_surjective _).comp (mulHomSup_surjective hcomm)
  have hΨ : Function.Surjective Ψ := by
    rintro ⟨a, b⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨(x, y), rfl⟩
  have hker : Ψ.ker = Φ.ker := by
    rw [ker_mulHomSup_quotient hcomm]
    simp only [Ψ, MonoidHom.ker_prodMap, QuotientGroup.ker_mk']
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective Ψ hΨ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective Φ hΦ))⟩

end CentralProduct

section TwoComponents

theorem false_of_two_components (hcent : CFSG.SectionRank.OddKernelCentralization)
    (hcat : CFSG.SectionRank.CatalogStepHyp) {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.SectionRank.IsSQTKCat Y) {N₁ N₂ : Subgroup Y} (h₁ : CFSG.IsComponent N₁)
    (h₂ : CFSG.IsComponent N₂) (hne : N₁ ≠ N₂) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr₁ : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥N₁ ⧸ Subgroup.center ↥N₁)))
    (hr₂ : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥N₂ ⧸ Subgroup.center ↥N₂))) : False := by
  have hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x := by
    rcases distinct_components_commute h₁ h₂ with h | h
    · exact absurd h hne
    · intro x hx y hy
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hx) y hy).symm
  obtain ⟨e⟩ := centralProductQuotientEquiv hcomm
  have hEV : layer ↥(N₁ ⊔ N₂) = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    obtain ⟨x, hx, y, hy, hv⟩ := exists_mul_of_mem_sup hcomm v.2
    have h₁' := component_overgroup h₁ (le_sup_left : N₁ ≤ N₁ ⊔ N₂)
    have h₂' := component_overgroup h₂ (le_sup_right : N₂ ≤ N₁ ⊔ N₂)
    have hxl : (⟨x, Subgroup.mem_sup_left hx⟩ : ↥(N₁ ⊔ N₂)) ∈ layer ↥(N₁ ⊔ N₂) :=
      component_le_layer h₁' (Subgroup.mem_subgroupOf.2 hx)
    have hyl : (⟨y, Subgroup.mem_sup_right hy⟩ : ↥(N₁ ⊔ N₂)) ∈ layer ↥(N₁ ⊔ N₂) :=
      component_le_layer h₂' (Subgroup.mem_subgroupOf.2 hy)
    have hvxy : v = ⟨x, Subgroup.mem_sup_left hx⟩ * ⟨y, Subgroup.mem_sup_right hy⟩ :=
      Subtype.ext hv
    rw [hvxy]
    exact Subgroup.mul_mem _ hxl hyl
  have hEQ : layer (↥(N₁ ⊔ N₂) ⧸ Subgroup.center ↥(N₁ ⊔ N₂)) = ⊤ :=
    layer_eq_top_of_surjective hEV (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hSQT : CFSG.IsStronglyQuasithin (↥(N₁ ⊔ N₂) ⧸ Subgroup.center ↥(N₁ ⊔ N₂)) :=
    CFSG.SectionRank.sqtk_semisimple_section_rank_of_catalog hcent hcat hY (N₁ ⊔ N₂)
      (Subgroup.center ↥(N₁ ⊔ N₂)) hEQ
  obtain ⟨E₁, -, hE₁, hc₁⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
    (⊤ : Subgroup (↥N₁ ⧸ Subgroup.center ↥N₁))
  obtain ⟨E₂, -, hE₂, hc₂⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
    (⊤ : Subgroup (↥N₂ ⧸ Subgroup.center ↥N₂))
  have hA : Nat.card (↥E₁ × ↥E₂) =
      p ^ (CFSG.Open.pRank p (⊤ : Subgroup (↥N₁ ⧸ Subgroup.center ↥N₁)) +
      CFSG.Open.pRank p (⊤ : Subgroup (↥N₂ ⧸ Subgroup.center ↥N₂))) := by
    rw [Nat.card_prod, hc₁, hc₂, pow_add]
  have hcommA : ∀ a b : ↥E₁ × ↥E₂, a * b = b * a := by
    have := hE₁.1
    have := hE₂.1
    intro a b
    exact Prod.ext (mul_comm' a.1 b.1) (mul_comm' a.2 b.2)
  have hpowA : ∀ a : ↥E₁ × ↥E₂, a ^ p = 1 := by
    intro a
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact hE₁.2 a.1 a.1.2
    · exact hE₂.2 a.2 a.2.2
  let f : ↥E₁ × ↥E₂ →* ↥(N₁ ⊔ N₂) ⧸ Subgroup.center ↥(N₁ ⊔ N₂) :=
    e.toMonoidHom.comp (E₁.subtype.prodMap E₂.subtype)
  have hf : Function.Injective f :=
    e.injective.comp (Function.Injective.prodMap E₁.subtype_injective E₂.subtype_injective)
  have hrank := CFSG.SectionRank.le_pRank_of_injective hp.one_lt hcommA hpowA hA f hf
    (H := ⊤) le_top
  have hle := (CFSG.SectionRank.isStronglyQuasithin_iff.1 hSQT) p hp hp2
  omega

theorem pRank_centerQuotient_eq {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) {p : ℕ} (hp : 1 < p) :
    CFSG.Open.pRank p (⊤ : Subgroup (A ⧸ Subgroup.center A)) =
      CFSG.Open.pRank p (⊤ : Subgroup (B ⧸ Subgroup.center B)) :=
  CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp
    (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))

theorem componentOddRankTwoNormal (hcent : CFSG.SectionRank.OddKernelCentralization)
    (hcat : CFSG.SectionRank.CatalogStepHyp) : ComponentOddRankTwoNormalProp := by
  intro G _ _ H L hH hL p hp hp2 hrank
  have hLH : L ≤ H := hL.1
  have hN : CFSG.IsComponent (L.subgroupOf H) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLH).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open L H).2 hL)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hrank
  refine ⟨fun n hn h => ?_⟩
  by_contra hcon
  let c : ↥H ≃* ↥H := MulAut.conj h
  have hN₂ : CFSG.IsComponent ((L.subgroupOf H).map c.toMonoidHom) := isComponent_map_mulEquiv c hN
  have hmem : h * n * h⁻¹ ∈ (L.subgroupOf H).map c.toMonoidHom := ⟨n, hn, rfl⟩
  have hne : L.subgroupOf H ≠ (L.subgroupOf H).map c.toMonoidHom := fun heq => hcon (heq ▸ hmem)
  have hr₁ : 2 ≤ CFSG.Open.pRank p
      (⊤ : Subgroup (↥(L.subgroupOf H) ⧸ Subgroup.center ↥(L.subgroupOf H))) := by
    rw [pRank_centerQuotient_eq (Subgroup.subgroupOfEquivOfLe hLH) hp.one_lt]
    exact hrank
  have hr₂ : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥((L.subgroupOf H).map c.toMonoidHom) ⧸
      Subgroup.center ↥((L.subgroupOf H).map c.toMonoidHom))) := by
    rw [← pRank_centerQuotient_eq (Subgroup.equivMapOfInjective (L.subgroupOf H) c.toMonoidHom
      c.injective) hp.one_lt]
    exact hr₁
  exact false_of_two_components hcent hcat hH hN hN₂ hne hp hp2 hr₁ hr₂

end TwoComponents

end CFSG.QuasithinUnique.Setup.Family
