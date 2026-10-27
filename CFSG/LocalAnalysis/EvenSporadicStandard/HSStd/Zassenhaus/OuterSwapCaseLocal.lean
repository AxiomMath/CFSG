module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterBad
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpSylowGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpType

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup Equiv CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard CFSG.Open
  CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {S : Subgroup G}
  {z n v s : G}

theorem exists_swap_element (h : HSOuterSetup G L t S z n v s) (hnF : ¬ F v t) :
    ∃ x : G, x * v = v * x ∧ (∀ l ∈ derivedCentralizerIn L v, x * l = l * x) ∧
      x * t * x⁻¹ = t * v ∧ (x * x = 1 ∨ x * x = v) := by
  obtain ⟨g, hg, hgt⟩ := not_not.1 hnF
  have hv2 : v * v = 1 := h.ctx.v_sq
  have ht2 : t * t = 1 := t_sq h
  have htv : t * v = v * t := h.t_comm_v
  have hgv : g * v = v * g := mem_centralizer_singleton_iff.1 hg
  obtain ⟨y, hy, hyl⟩ := exists_inner_Y h (mem_normalizer_derived h hgv hgt)
  have hyt : y * t = t * y := mem_centralizer_iff.1 h.t_mem y hy.2
  have hyv : y * v = v * y := mem_centralizer_singleton_iff.1 hy.1
  obtain ⟨x, hxdef⟩ : ∃ x : G, x = y⁻¹ * g := ⟨_, rfl⟩
  have hxv : x * v = v * x := by
    have h1 : y⁻¹ * v = v * y⁻¹ := (Commute.inv_left (show Commute y v from hyv)).eq
    calc x * v = y⁻¹ * (g * v) := by rw [hxdef, mul_assoc]
      _ = y⁻¹ * (v * g) := by rw [hgv]
      _ = (y⁻¹ * v) * g := by simp only [mul_assoc]
      _ = (v * y⁻¹) * g := by rw [h1]
      _ = v * x := by rw [hxdef, mul_assoc]
  have hxvi : x * v * x⁻¹ = v := by rw [hxv]; group
  have hxl : ∀ l ∈ derivedCentralizerIn L v, x * l = l * x := by
    intro l hl
    have h1 := hyl l hl
    calc x * l = y⁻¹ * (g * l * g⁻¹) * g := by rw [hxdef]; group
      _ = y⁻¹ * (y * l * y⁻¹) * g := by rw [h1]
      _ = l * x := by rw [hxdef]; group
  have hxt : x * t * x⁻¹ = t * v := by
    have h1 : y⁻¹ * (t * v) * y = t * v := by
      have h2 : y * (t * v) = (t * v) * y := by
        calc y * (t * v) = (y * t) * v := by simp only [mul_assoc]
          _ = (t * y) * v := by rw [hyt]
          _ = t * (y * v) := by simp only [mul_assoc]
          _ = t * (v * y) := by rw [hyv]
          _ = (t * v) * y := by simp only [mul_assoc]
      calc y⁻¹ * (t * v) * y = y⁻¹ * ((t * v) * y) := by simp only [mul_assoc]
        _ = y⁻¹ * (y * (t * v)) := by rw [h2]
        _ = t * v := by group
    calc x * t * x⁻¹ = y⁻¹ * (g * t * g⁻¹) * y := by rw [hxdef]; group
      _ = t * v := by rw [hgt, h1]
  have hxne : ¬ (x * t = t * x) := by
    intro hc
    have : x * t * x⁻¹ = t := by rw [hc]; group
    rw [hxt] at this
    apply h.v_ne_one
    exact (mul_left_cancel (a := t) (by rw [this, mul_one]) : v = 1)
  have hx2t : (x * x) * t = t * (x * x) := by
    have h1 : (x * x) * t * (x * x)⁻¹ = t := by
      calc (x * x) * t * (x * x)⁻¹ = x * (x * t * x⁻¹) * x⁻¹ := by group
        _ = x * (t * v) * x⁻¹ := by rw [hxt]
        _ = (x * t * x⁻¹) * (x * v * x⁻¹) := by group
        _ = (t * v) * v := by rw [hxt, hxvi]
        _ = t := by rw [mul_assoc, hv2, mul_one]
    calc (x * x) * t = ((x * x) * t * (x * x)⁻¹) * (x * x) := by group
      _ = t * (x * x) := by rw [h1]
  have hx2v : (x * x) * v = v * (x * x) := by
    calc (x * x) * v = x * (x * v) := by simp only [mul_assoc]
      _ = x * (v * x) := by rw [hxv]
      _ = (x * v) * x := by simp only [mul_assoc]
      _ = (v * x) * x := by rw [hxv]
      _ = v * (x * x) := by simp only [mul_assoc]
  obtain ⟨β, hβ, a, b, hxx⟩ := decomp_Y h hx2t hx2v
  obtain ⟨hct, hcv⟩ := bp_mem h a b
  have hβc : ∀ l ∈ derivedCentralizerIn L v, β * l = l * β := by
    intro l hl
    have hlY := derivedCentralizerIn_le_Y L v hl
    have hcl : (bp t a * bp v b) * l = l * (bp t a * bp v b) :=
      (bp_comm a b (d := l) (mem_centralizer_iff.1 h.t_mem l hlY.2)
        (mem_centralizer_singleton_iff.1 hlY.1)).symm
    have h1 : (x * x) * l = l * (x * x) := by
      calc (x * x) * l = x * (x * l) := by simp only [mul_assoc]
        _ = x * (l * x) := by rw [hxl l hl]
        _ = (x * l) * x := by simp only [mul_assoc]
        _ = (l * x) * x := by rw [hxl l hl]
        _ = l * (x * x) := by simp only [mul_assoc]
    rw [hxx] at h1
    have h2 : (β * l) * (bp t a * bp v b) = (l * β) * (bp t a * bp v b) := by
      calc (β * l) * (bp t a * bp v b) = β * (l * (bp t a * bp v b)) := by simp only [mul_assoc]
        _ = β * ((bp t a * bp v b) * l) := by rw [hcl]
        _ = β * (bp t a * bp v b) * l := by simp only [mul_assoc]
        _ = l * (β * (bp t a * bp v b)) := h1
        _ = (l * β) * (bp t a * bp v b) := by simp only [mul_assoc]
    exact mul_right_cancel h2
  have hβ1 : β = 1 := eq_one_of_comm_derived h hβ hβc
  rw [hβ1, one_mul] at hxx
  refine ⟨x, hxv, hxl, hxt, ?_⟩
  cases a <;> cases b
  · left; simpa [bp] using hxx
  · right; simpa [bp] using hxx
  · exfalso
    apply hxne
    have h1 : x * x = t := by simpa [bp] using hxx
    calc x * t = x * (x * x) := by rw [h1]
      _ = (x * x) * x := by simp only [mul_assoc]
      _ = t * x := by rw [h1]
  · exfalso
    have h1 : x * x = t * v := by simpa [bp] using hxx
    have h2 : x * (t * v) = (t * v) * x := by
      calc x * (t * v) = x * (x * x) := by rw [h1]
        _ = (x * x) * x := by simp only [mul_assoc]
        _ = (t * v) * x := by rw [h1]
    have h3 : x * (t * v) * x⁻¹ = t * v := by rw [h2]; group
    have h4 : x * (t * v) * x⁻¹ = (x * t * x⁻¹) * (x * v * x⁻¹) := by group
    rw [h4, hxt, hxvi, mul_assoc, hv2, mul_one] at h3
    apply h.v_ne_one
    have : t * 1 = t * v := by rw [mul_one]; exact h3
    exact (mul_left_cancel this).symm

theorem exists_swap_involution (h : HSOuterSetup G L t S z n v s) (hnF : ¬ F v t) :
    ∃ g' : G, g' ∈ centralizer ({v} : Set G) ∧
      g' ∈ centralizer ((derivedCentralizerIn L v : Subgroup G) : Set G) ∧
      g' * t * g'⁻¹ = t * v ∧ g' * g' = 1 := by
  obtain ⟨x, hxv, hxl, hxt, hxx⟩ := exists_swap_element h hnF
  have hv2 : v * v = 1 := h.ctx.v_sq
  have ht2 : t * t = 1 := t_sq h
  have htv : t * v = v * t := h.t_comm_v
  have htl : ∀ l ∈ derivedCentralizerIn L v, l * t = t * l := fun l hl =>
    mem_centralizer_iff.1 h.t_mem l (derivedCentralizerIn_le L v hl)
  rcases hxx with h1 | h1
  · refine ⟨x, mem_centralizer_singleton_iff.2 hxv, ?_, hxt, h1⟩
    rw [mem_centralizer_iff]
    intro l hl
    exact (hxl l hl).symm
  · have hxt' : x * t = t * v * x := by
      calc x * t = (x * t * x⁻¹) * x := by group
        _ = t * v * x := by rw [hxt]
    refine ⟨x * t, ?_, ?_, ?_, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      calc x * t * v = x * (t * v) := by rw [mul_assoc]
        _ = x * (v * t) := by rw [htv]
        _ = (x * v) * t := by rw [mul_assoc]
        _ = v * x * t := by rw [hxv]
        _ = v * (x * t) := by rw [mul_assoc]
    · rw [mem_centralizer_iff]
      intro l hl
      calc l * (x * t) = (l * x) * t := by rw [mul_assoc]
        _ = (x * l) * t := by rw [(hxl l hl).symm]
        _ = x * (l * t) := by rw [mul_assoc]
        _ = x * (t * l) := by rw [htl l hl]
        _ = x * t * l := by rw [mul_assoc]
    · calc x * t * t * (x * t)⁻¹ = x * t * x⁻¹ := by group
        _ = t * v := hxt
    · calc x * t * (x * t) = (t * v * x) * (x * t) := by rw [hxt']
        _ = t * v * (x * x) * t := by simp only [mul_assoc]
        _ = t * (v * v) * t := by rw [h1]; simp only [mul_assoc]
        _ = 1 := by rw [hv2, mul_one, ht2]

theorem swap_mul_sq (h : HSOuterSetup G L t S z n v s) {g' : G} (hg2 : g' * g' = 1)
    (hgt : g' * t * g'⁻¹ = t * v) : (t * g') * (t * g') = v := by
  have ht2 : t * t = 1 := t_sq h
  have hv2 : v * v = 1 := h.ctx.v_sq
  have e : g' * t = t * v * g' := by
    calc g' * t = (g' * t * g'⁻¹) * g' := by group
      _ = t * v * g' := by rw [hgt]
  calc t * g' * (t * g') = t * (g' * t) * g' := by simp only [mul_assoc]
    _ = t * (t * v * g') * g' := by rw [e]
    _ = (t * t) * v * (g' * g') := by simp only [mul_assoc]
    _ = v := by rw [ht2, hg2, one_mul, mul_one]

theorem mem_pair_of_centralizes (h : HSOuterSetup G L t S z n v s)
    (hK : ∀ β ∈ L, (∀ l ∈ derivedCentralizerIn L v, β * l = l * β) → β = 1) {x : G}
    (hxt : x * t = t * x) (hxl : ∀ l ∈ derivedCentralizerIn L v, x * l = l * x) :
    ∃ a b : Bool, x = bp t a * bp v b := by
  obtain ⟨β, hβ, a, b, rfl⟩ := exists_decomp h (d := x) (mem_centralizer_singleton_iff.2 hxt)
  have hβc : ∀ l ∈ derivedCentralizerIn L v, β * l = l * β := by
    intro l hl
    have hlY := derivedCentralizerIn_le_Y L v hl
    have hcl : (bp t a * bp v b) * l = l * (bp t a * bp v b) :=
      (bp_comm a b (d := l) (mem_centralizer_iff.1 h.t_mem l hlY.2)
        (mem_centralizer_singleton_iff.1 hlY.1)).symm
    have h2 : (β * l) * (bp t a * bp v b) = (l * β) * (bp t a * bp v b) := by
      calc (β * l) * (bp t a * bp v b) = β * (l * (bp t a * bp v b)) := by simp only [mul_assoc]
        _ = β * ((bp t a * bp v b) * l) := by rw [hcl]
        _ = β * (bp t a * bp v b) * l := by simp only [mul_assoc]
        _ = l * (β * (bp t a * bp v b)) := by simpa [mul_assoc] using hxl l hl
        _ = (l * β) * (bp t a * bp v b) := by simp only [mul_assoc]
    exact mul_right_cancel h2
  have hβ1 : β = 1 := hK β hβ hβc
  exact ⟨a, b, by rw [hβ1, one_mul]⟩

theorem card_le_four_of_subset_pair {Q : Type*} [Finite Q] (f : Q → G) (hf : Function.Injective f)
    (hQ : ∀ q, f q = 1 ∨ f q = t ∨ f q = v ∨ f q = t * v) : Nat.card Q ≤ 4 := by
  classical
  let F : Finset G := {1, t, v, t * v}
  let g : Q → ↥F := fun q => ⟨f q, by
    rcases hQ q with h | h | h | h <;> simp [F, h]⟩
  have hg : Function.Injective g := fun a b hab => hf (congrArg Subtype.val hab)
  have h1 := Nat.card_le_card_of_injective g hg
  have h2 : Nat.card ↥F ≤ 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact Finset.card_le_four
  omega

theorem card_le_four_of_le_centralizer_derived (h : HSOuterSetup G L t S z n v s)
    (hK : ∀ β ∈ L, (∀ l ∈ derivedCentralizerIn L v, β * l = l * β) → β = 1) {E : Subgroup G}
    (hE : E ≤ centralizer ((derivedCentralizerIn L v : Subgroup G) : Set G))
    (hE2 : ∀ e ∈ E, e * e = 1) : Nat.card E ≤ 4 := by
  set Y : Subgroup G := centralizer ((derivedCentralizerIn L v : Subgroup G) : Set G) with hY
  have htY : t ∈ Y := by
    rw [hY, mem_centralizer_iff]
    intro l hl
    exact mem_centralizer_iff.1 h.t_mem l (derivedCentralizerIn_le L v hl)
  set tY : Y := ⟨t, htY⟩ with htYdef
  have hx : orderOf tY = 2 := by rw [htYdef, Subgroup.orderOf_mk]; exact h.t_two
  have hc : ∀ Q : Subgroup Y, Q ≤ centralizer ({tY} : Set Y) → IsPGroup 2 Q → Nat.card Q ≤ 4 := by
    intro Q hQc _
    refine card_le_four_of_subset_pair (t := t) (v := v) (fun q : Q => ((q : Y) : G))
      (fun a b hab => Subtype.ext (Subtype.ext hab)) fun q => ?_
    have hqt : (((q : Y) : G)) * t = t * ((q : Y) : G) := by
      have := mem_centralizer_iff.1 (hQc q.2) tY (Set.mem_singleton _)
      exact (congrArg Subtype.val this).symm
    have hql : ∀ l ∈ derivedCentralizerIn L v,
        (((q : Y) : G)) * l = l * (((q : Y) : G)) := fun l hl =>
      (mem_centralizer_iff.1 (q : Y).2 l hl).symm
    obtain ⟨a, b, hab⟩ := mem_pair_of_centralizes h hK hqt hql
    rw [hab]
    cases a <;> cases b <;> simp [bp]
  have h4 := card_le_four_of_centralizer_two_subgroups hx hc (E.subgroupOf Y)
    (by
      intro e he
      apply Subtype.ext
      exact hE2 _ (Subgroup.mem_subgroupOf.mp he))
  have hcE : Nat.card (E.subgroupOf Y) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
  omega

@[expose] def conjOn (L : Subgroup G) (g : G) (hg : g ∈ normalizer (L : Set G)) : MulAut L where
  toFun l := ⟨g * l * g⁻¹, (mem_set_normalizer_iff.1 hg l).1 l.2⟩
  invFun l := ⟨g⁻¹ * l * g, by
    refine (mem_set_normalizer_iff.1 hg (g⁻¹ * l * g)).2 ?_
    have : g * (g⁻¹ * (l : G) * g) * g⁻¹ = l := by group
    rw [this]
    exact l.2⟩
  left_inv l := Subtype.ext (by simp [mul_assoc])
  right_inv l := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

omit [Finite G] in
theorem conjOn_apply (L : Subgroup G) (g : G) (hg : g ∈ normalizer (L : Set G)) (l : L) :
    ((conjOn L g hg l : L) : G) = g * l * g⁻¹ := rfl

section HS

theorem eq_one_of_comm_derived_of_hs (hKG : KGHSA8) (h : HSOuterSetup G L t S z n v s) {β : G}
    (hβ : β ∈ L) (hc : ∀ l ∈ derivedCentralizerIn L v, β * l = l * β) : β = 1 := by
  by_contra hβ1
  have hhs : IsSporadic ↥L .HS := h.setting.2.1
  obtain ⟨e₀⟩ := hhs
  have e : ↥L ≃* NativeSporadic.HS := e₀
  have hs : IsSimpleGroup NativeSporadic.HS := CFSG.Sporadic.HS.isSimpleGroup_HS
  have hsimple : IsSimpleGroup ↥L := @MulEquiv.isSimpleGroup _ _ NativeSporadic.HS _ hs e
  have hcard : Nat.card ↥L = 44352000 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HS.card_HS
  have hcat : Catalog ↥L := Or.inr (Or.inr (Or.inr (Or.inr ⟨.HS, ⟨e₀⟩⟩)))
  have hZ : center ↥L = ⊥ := center_eq_bot_of_isSporadic_hs h.setting.2.1
  set A : Subgroup ↥L := (derivedCentralizerIn L v).subgroupOf L with hA
  have hA8 : Nonempty (↥A ≃* alternatingGroup (Fin 8)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe (derivedCentralizerIn_le L v)).trans
      (derivedCentralizerIn_equiv h.ctx.v_cls).some⟩
  have hle := hKG ↥L hcat hsimple hcard A hA8
  have hvN : v ∈ normalizer (L : Set G) :=
    centralizer_t_le_normalizer h (v_mem_centralizer_t h)
  have hβN : β ∈ normalizer (L : Set G) := le_normalizer hβ
  have : Finite (MulAut ↥L) :=
    Finite.of_injective (fun σ : MulAut ↥L => (σ : ↥L → ↥L)) DFunLike.coe_injective
  let σv : MulAut ↥L := conjOn L v hvN
  let σβ : MulAut ↥L := conjOn L β hβN
  have hfixv : ∀ a ∈ A, σv a = a := by
    intro a ha
    apply Subtype.ext
    have hal : (a : G) ∈ derivedCentralizerIn L v := mem_subgroupOf.1 ha
    have hav : v * (a : G) = (a : G) * v :=
      (mem_centralizer_singleton_iff.1 (derivedCentralizerIn_le_centralizer L v hal)).symm
    show v * (a : G) * v⁻¹ = a
    rw [hav]; group
  have hfixβ : ∀ a ∈ A, σβ a = a := by
    intro a ha
    apply Subtype.ext
    have hal : (a : G) ∈ derivedCentralizerIn L v := mem_subgroupOf.1 ha
    show β * (a : G) * β⁻¹ = a
    rw [hc _ hal]; group
  have hcentL : ∀ y : G, (∀ l ∈ L, y * l * y⁻¹ = l) → y * t = t * y → y ∈ zpowers t := by
    intro y hyL hyt
    have hyC : y ∈ centralizer (L : Set G) := by
      rw [mem_centralizer_iff]
      intro l hl
      have := hyL l hl
      calc l * y = (y * l * y⁻¹) * y := by rw [this]
        _ = y * l := by group
    have hker : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
      h.setting.1.centralizer_inf_centralizer_eq_zpowers h.setting.2.2.1 h.t_mem h.t_two
    rw [← hker]
    exact ⟨hyC, mem_centralizer_singleton_iff.2 hyt⟩
  have hzp : ∀ a : G, a ∈ zpowers t → a ∈ L ⊔ zpowers t := fun a ha =>
    (le_sup_right : zpowers t ≤ L ⊔ zpowers t) ha
  have hv_ne : σv ≠ 1 := by
    intro h1
    apply h.ctx.v_outer
    have hvt : v ∈ zpowers t := by
      refine hcentL v (fun l hl => ?_) h.t_comm_v.symm
      have := congrArg (fun σ : MulAut ↥L => ((σ ⟨l, hl⟩ : ↥L) : G)) h1
      simpa [σv, conjOn_apply] using this
    exact hzp v hvt
  have hβ_ne : σβ ≠ 1 := by
    intro h1
    apply hβ1
    have hmem : (⟨β, hβ⟩ : ↥L) ∈ center ↥L := by
      rw [mem_center_iff]
      intro g
      have := congrArg (fun σ : MulAut ↥L => ((σ g : ↥L) : G)) h1
      apply Subtype.ext
      have h2 : β * (g : G) * β⁻¹ = g := by simpa [σβ, conjOn_apply] using this
      calc (g : G) * β = (β * (g : G) * β⁻¹) * β := by rw [h2]
        _ = β * g := by group
    rw [hZ, mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hvβ_ne : σv ≠ σβ := by
    intro h1
    apply h.ctx.v_outer
    set y : G := β⁻¹ * v with hy
    have hyL : ∀ l ∈ L, y * l * y⁻¹ = l := by
      intro l hl
      have := congrArg (fun σ : MulAut ↥L => ((σ ⟨l, hl⟩ : ↥L) : G)) h1
      have h2 : v * l * v⁻¹ = β * l * β⁻¹ := by simpa [σv, σβ, conjOn_apply] using this
      calc y * l * y⁻¹ = β⁻¹ * (v * l * v⁻¹) * β := by rw [hy]; group
        _ = β⁻¹ * (β * l * β⁻¹) * β := by rw [h2]
        _ = l := by group
    have hyt : y * t = t * y := by
      have hβt : β * t = t * β := mem_centralizer_iff.1 h.t_mem β hβ
      have hβit : β⁻¹ * t = t * β⁻¹ :=
        (Commute.inv_left (show Commute β t from hβt)).eq
      calc y * t = β⁻¹ * (v * t) := by rw [hy, mul_assoc]
        _ = β⁻¹ * (t * v) := by rw [h.t_comm_v]
        _ = (β⁻¹ * t) * v := by rw [mul_assoc]
        _ = (t * β⁻¹) * v := by rw [hβit]
        _ = t * y := by rw [hy]; simp only [mul_assoc]
    have hyt' := hcentL y hyL hyt
    have hvy : v = β * y := by rw [hy]; group
    rw [hvy]
    exact Subgroup.mul_mem _ ((le_sup_left : L ≤ L ⊔ zpowers t) hβ) (hzp y hyt')
  let f : Fin 3 → {σ : MulAut ↥L // ∀ a ∈ A, σ a = a} :=
    ![⟨1, fun a _ => rfl⟩, ⟨σv, hfixv⟩, ⟨σβ, hfixβ⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | (exfalso
         have key := congrArg Subtype.val hij
         simp only [f] at key
         first
         | exact hv_ne key | exact hv_ne key.symm | exact hβ_ne key | exact hβ_ne key.symm
         | exact hvβ_ne key | exact hvβ_ne key.symm)
  have h3 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin] at h3
  have h4 : Nat.card {σ : MulAut ↥L // ∀ a ∈ A, σ a = a} ≤ 2 := hle
  omega

theorem card_le_four_of_le_centralizer_derived_of_hs (hKG : KGHSA8)
    (h : HSOuterSetup G L t S z n v s) {E : Subgroup G}
    (hE : E ≤ centralizer ((derivedCentralizerIn L v : Subgroup G) : Set G))
    (hE2 : ∀ e ∈ E, e * e = 1) : Nat.card E ≤ 4 :=
  card_le_four_of_le_centralizer_derived h
    (fun _ hβ hc => eq_one_of_comm_derived_of_hs hKG h hβ hc) hE hE2

end HS

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
