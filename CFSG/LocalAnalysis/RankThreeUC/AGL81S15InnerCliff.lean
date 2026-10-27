module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerFaith

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerDef

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

section Min

variable {K : Type*} [Group K] {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z]

structure LMin (L : Subgroup K) (κ : Representation (ZMod 2) K Z) (Y : Submodule (ZMod 2) Z) :
    Prop where
  ne_bot : Y ≠ ⊥
  inv : ∀ l ∈ L, ∀ y ∈ Y, κ l y ∈ Y
  min : ∀ W : Submodule (ZMod 2) Z, W ≤ Y → (∀ l ∈ L, ∀ w ∈ W, κ l w ∈ W) → W = ⊥ ∨ W = Y

theorem exists_lMin [Finite Z] [Nontrivial Z] (L : Subgroup K)
    (κ : Representation (ZMod 2) K Z) : ∃ Y, LMin L κ Y := by
  haveI : Module.Finite (ZMod 2) Z := Module.Finite.of_finite
  let S : Set (Submodule (ZMod 2) Z) := {W | W ≠ ⊥ ∧ ∀ l ∈ L, ∀ w ∈ W, κ l w ∈ W}
  have hS : S.Nonempty := ⟨⊤, top_ne_bot, fun _ _ _ _ => Submodule.mem_top⟩
  obtain ⟨Y, ⟨hYb, hYi⟩, hmin⟩ :=
    (measure fun W : Submodule (ZMod 2) Z => Module.finrank (ZMod 2) ↥W).wf.has_min S hS
  refine ⟨Y, hYb, hYi, fun W hWY hWi => ?_⟩
  by_contra hcon
  push Not at hcon
  have hlt : W < Y := lt_of_le_of_ne hWY hcon.2
  exact hmin W ⟨hcon.1, hWi⟩ (Submodule.finrank_lt_finrank_of_lt hlt)

variable {L B : Subgroup K}

theorem LMin.nontriv (h : InnerCtx L B) {κ : Representation (ZMod 2) K Z}
    (hd : ChiefData L B κ) {Y : Submodule (ZMod 2) Z} (hY : LMin L κ Y) :
    ∃ l ∈ L, ∃ y ∈ Y, κ l y ≠ y := by
  by_contra hcon
  push Not at hcon
  haveI := h.normal_L
  let W : Submodule (ZMod 2) Z := Submodule.span (ZMod 2) {z | ∃ g : K, ∃ y ∈ Y, z = κ g y}
  have hWinv : ∀ k : K, ∀ z ∈ W, κ k z ∈ W := by
    intro k z hz
    refine Submodule.span_induction (p := fun z _ => κ k z ∈ W) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨g, y, hy, rfl⟩
      exact Submodule.subset_span ⟨k * g, y, hy, (repMulApply κ k g y).symm⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact W.add_mem hx hy
    · intro c x _ hx
      rw [map_smul]
      exact W.smul_mem c hx
  have hWne : W ≠ ⊥ := by
    intro hbot
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY.ne_bot
    have hyW : y ∈ W := Submodule.subset_span ⟨1, y, hy, by rw [map_one]; rfl⟩
    rw [hbot, Submodule.mem_bot] at hyW
    exact hy0 hyW
  have hWtop : W = ⊤ := (hd.irr W hWinv).resolve_left hWne
  have hLW : ∀ l ∈ L, ∀ z ∈ W, κ l z = z := by
    intro l hl z hz
    refine Submodule.span_induction (p := fun z _ => κ l z = z) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨g, y, hy, rfl⟩
      have hconj : g⁻¹ * l * g ∈ L := by
        have := ‹L.Normal›.conj_mem l hl g⁻¹
        simpa using this
      calc κ l (κ g y) = κ (l * g) y := (repMulApply κ l g y).symm
        _ = κ (g * (g⁻¹ * l * g)) y := by rw [show g * (g⁻¹ * l * g) = l * g by group]
        _ = κ g (κ (g⁻¹ * l * g) y) := repMulApply κ g _ y
        _ = κ g y := by rw [hcon _ hconj y hy]
    · simp
    · intro x y _ _ hx hy
      rw [map_add, hx, hy]
    · intro c x _ hx
      rw [map_smul, hx]
  obtain ⟨l, hl, z, hz⟩ := hd.hL
  exact hz (hLW l hl z (by rw [hWtop]; exact Submodule.mem_top))

theorem InnerCtx.central_of_commute (h : InnerCtx L B) {c : K}
    (hL : ∀ k ∈ L, c * k = k * c) (hB : ∀ k ∈ B, c * k = k * c) : ∀ k : K, c * k = k * c := by
  have hL' : L ≤ Subgroup.centralizer ({c} : Set K) := fun l hl => by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hL l hl
  have hB' : B ≤ Subgroup.centralizer ({c} : Set K) := fun b hb => by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hB b hb
  have htop : (⊤ : Subgroup K) ≤ Subgroup.centralizer ({c} : Set K) := by
    rw [← h.top]
    exact sup_le hL' hB'
  intro k
  exact (Subgroup.mem_centralizer_iff.mp (htop (Subgroup.mem_top k))) c (Set.mem_singleton c)

theorem InnerCtx.kappa_eq_of_conjAgree [Nontrivial Z] (h : InnerCtx L B)
    (κ : Representation (ZMod 2) K Z)
    (hirr : ∀ W : Submodule (ZMod 2) Z, (∀ k : K, ∀ z ∈ W, κ k z ∈ W) → W = ⊥ ∨ W = ⊤)
    {b l₀ : K} (hb : b ∈ B) (hl₀ : l₀ ∈ L) (hsq : l₀ * l₀ = 1) (hag : ConjAgree L b l₀)
    (z : Z) : κ b z = κ l₀ z := by
  have hcommB : ∀ k ∈ B, k * l₀ = l₀ * k := by
    intro k hk
    have hkl : k * l₀ * k⁻¹ ∈ L := h.normalizes k hk l₀ hl₀
    have hkb : k * b * k⁻¹ = b := by
      calc k * b * k⁻¹ = (b * k) * k⁻¹ := by rw [h.comm k hk b hb]
        _ = b := by group
    have hag' : ConjAgree L b (k * l₀ * k⁻¹) := by
      intro x hx
      have hkx : k⁻¹ * x * k ∈ L := by
        have h1 := h.normalizes k hk x hx
        rw [h.inv_eq hk] at h1 ⊢
        exact h1
      calc b * x * b⁻¹ = (k * b * k⁻¹) * x * (k * b * k⁻¹)⁻¹ := by rw [hkb]
        _ = k * (b * (k⁻¹ * x * k) * b⁻¹) * k⁻¹ := by group
        _ = k * (l₀ * (k⁻¹ * x * k) * l₀⁻¹) * k⁻¹ := by rw [hag (k⁻¹ * x * k) hkx]
        _ = (k * l₀ * k⁻¹) * x * (k * l₀ * k⁻¹)⁻¹ := by group
    have hsq' : (k * l₀ * k⁻¹) * (k * l₀ * k⁻¹) = 1 := by
      calc (k * l₀ * k⁻¹) * (k * l₀ * k⁻¹) = k * (l₀ * l₀) * k⁻¹ := by group
        _ = 1 := by rw [hsq]; group
    have heq := ConjAgree.eq_of_sq_eq_one h.hZ hl₀ hkl hag hag' hsq hsq'
    calc k * l₀ = (k * l₀ * k⁻¹) * k := by group
      _ = l₀ * k := by rw [heq]
  have hcL : ∀ k ∈ L, (l₀⁻¹ * b) * k = k * (l₀⁻¹ * b) := by
    intro k hk
    have e : (l₀⁻¹ * b) * k * (l₀⁻¹ * b)⁻¹ = k := by
      calc (l₀⁻¹ * b) * k * (l₀⁻¹ * b)⁻¹ = l₀⁻¹ * (b * k * b⁻¹) * l₀ := by group
        _ = l₀⁻¹ * (l₀ * k * l₀⁻¹) * l₀ := by rw [hag k hk]
        _ = k := by group
    calc (l₀⁻¹ * b) * k = ((l₀⁻¹ * b) * k * (l₀⁻¹ * b)⁻¹) * (l₀⁻¹ * b) := by group
      _ = k * (l₀⁻¹ * b) := by rw [e]
  have hcB : ∀ k ∈ B, (l₀⁻¹ * b) * k = k * (l₀⁻¹ * b) := by
    intro k hk
    have h1 := hcommB k hk
    have h2 := h.comm b hb k hk
    have h3 : l₀⁻¹ * k = k * l₀⁻¹ := by
      calc l₀⁻¹ * k = l₀⁻¹ * (k * l₀) * l₀⁻¹ := by group
        _ = l₀⁻¹ * (l₀ * k) * l₀⁻¹ := by rw [h1]
        _ = k * l₀⁻¹ := by group
    calc (l₀⁻¹ * b) * k = l₀⁻¹ * (b * k) := by group
      _ = l₀⁻¹ * (k * b) := by rw [h2]
      _ = (l₀⁻¹ * k) * b := by group
      _ = (k * l₀⁻¹) * b := by rw [h3]
      _ = k * (l₀⁻¹ * b) := by group
  have hc := h.central_of_commute hcL hcB
  have hbl : b * l₀⁻¹ = l₀⁻¹ * b := by
    have := hcommB b hb
    calc b * l₀⁻¹ = l₀⁻¹ * (l₀ * b) * l₀⁻¹ := by group
      _ = l₀⁻¹ * (b * l₀) * l₀⁻¹ := by rw [this]
      _ = l₀⁻¹ * b := by group
  have hc2 : (l₀⁻¹ * b) * (l₀⁻¹ * b) = 1 := by
    calc (l₀⁻¹ * b) * (l₀⁻¹ * b) = l₀⁻¹ * (b * l₀⁻¹) * b := by group
      _ = l₀⁻¹ * (l₀⁻¹ * b) * b := by rw [hbl]
      _ = (l₀ * l₀)⁻¹ * (b * b) := by group
      _ = 1 := by rw [hsq, h.sq b hb]; group
  have h1 := kappa_eq_one_of_central κ hirr hc hc2 z
  calc κ b z = κ (l₀ * (l₀⁻¹ * b)) z := by rw [show l₀ * (l₀⁻¹ * b) = b by group]
    _ = κ l₀ (κ (l₀⁻¹ * b) z) := repMulApply κ l₀ _ z
    _ = κ l₀ z := by rw [h1]

@[expose] def stabIn (h : InnerCtx L B) (κ : Representation (ZMod 2) K Z)
    (Y : Submodule (ZMod 2) Z) : Subgroup K where
  carrier := {b | b ∈ B ∧ ∀ y ∈ Y, κ b y ∈ Y}
  mul_mem' := by
    rintro a b ⟨ha, hay⟩ ⟨hb, hby⟩
    exact ⟨B.mul_mem ha hb, fun y hy => by rw [repMulApply]; exact hay _ (hby y hy)⟩
  one_mem' := ⟨B.one_mem, fun y hy => by rw [map_one]; exact hy⟩
  inv_mem' := by
    rintro b ⟨hb, hby⟩
    refine ⟨B.inv_mem hb, ?_⟩
    rw [h.inv_eq hb]
    exact hby

theorem stabIn_le (h : InnerCtx L B) (κ : Representation (ZMod 2) K Z)
    (Y : Submodule (ZMod 2) Z) : stabIn h κ Y ≤ B := fun _ hb => hb.1

theorem innerPart_le_stab [Nontrivial Z] (h : InnerCtx L B) (κ : Representation (ZMod 2) K Z)
    (hirr : ∀ W : Submodule (ZMod 2) Z, (∀ k : K, ∀ z ∈ W, κ k z ∈ W) → W = ⊥ ∨ W = ⊤)
    {Y : Submodule (ZMod 2) Z} (hY : ∀ l ∈ L, ∀ y ∈ Y, κ l y ∈ Y) :
    innerPart L B ≤ stabIn h κ Y := by
  intro b hb
  obtain ⟨hbB, l, hl, hag⟩ := mem_innerPart.mp hb
  obtain ⟨l₀, hl₀, hag₀, hsq⟩ := exists_involutory_lift h.hZ (h.sq b hbB) hl hag
  have hκ := h.kappa_eq_of_conjAgree κ hirr hbB hl₀ hsq hag₀
  refine ⟨hbB, fun y hy => ?_⟩
  rw [hκ y]
  exact hY l₀ hl₀ y hy

theorem translate_inv (h : InnerCtx L B) (κ : Representation (ZMod 2) K Z)
    {Y : Submodule (ZMod 2) Z} (hY : ∀ l ∈ L, ∀ y ∈ Y, κ l y ∈ Y) {a : K} (ha : a ∈ B) :
    ∀ l ∈ L, ∀ w ∈ Y.map (κ a), κ l w ∈ Y.map (κ a) := by
  rintro l hl _ ⟨y, hy, rfl⟩
  have hconj : a * l * a ∈ L := by
    have := h.normalizes a ha l hl
    rwa [h.inv_eq ha] at this
  refine ⟨κ (a * l * a) y, hY _ hconj y hy, ?_⟩
  calc κ a (κ (a * l * a) y) = κ (a * (a * l * a)) y := (repMulApply κ a _ y).symm
    _ = κ (l * a) y := by
        rw [show a * (a * l * a) = (a * a) * l * a by group, h.sq a ha, one_mul]
    _ = κ l (κ a y) := repMulApply κ l a y

theorem inf_translate_eq_bot (h : InnerCtx L B) (κ : Representation (ZMod 2) K Z)
    {Y : Submodule (ZMod 2) Z} (hY : LMin L κ Y) {a : K} (ha : a ∈ B)
    (hna : a ∉ stabIn h κ Y) : Y ⊓ Y.map (κ a) = ⊥ := by
  have hinv : ∀ l ∈ L, ∀ w ∈ Y ⊓ Y.map (κ a), κ l w ∈ Y ⊓ Y.map (κ a) := fun l hl w hw =>
    ⟨hY.inv l hl w hw.1, translate_inv h κ hY.inv ha l hl w hw.2⟩
  rcases hY.min _ inf_le_left hinv with hbot | htop
  · exact hbot
  · exfalso
    apply hna
    refine ⟨ha, fun y hy => ?_⟩
    have hyle : y ∈ Y ⊓ Y.map (κ a) := by rw [htop]; exact hy
    obtain ⟨y', hy', hyy'⟩ := hyle.2
    have : κ a y = y' := by
      rw [← hyy', ← repMulApply, h.sq a ha, map_one]
      rfl
    rw [this]
    exact hy'

end Min

end CFSG.LocalAnalysis.RankThreeUC.S15
