module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureOrthCompl
public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureOrthFlag

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace OrthClosure

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal LinClosure

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

@[expose] noncomputable def eichlerΓ (u w : V) : elementaryGroup Q :=
  ⟨eichler Q u w, eichler_mem_elementaryGroup Q u w⟩

theorem eichlerΓ_smul (u w x : V) : eichlerΓ Q u w • x = eichler Q u w x := rfl

@[expose] def perpQ (U : Submodule K V) : Submodule K V :=
  LinearMap.BilinForm.orthogonal (polarBilin Q) U

variable {Q}

theorem mem_perpQ {U : Submodule K V} {y : V} : y ∈ perpQ Q U ↔ ∀ n ∈ U, polar Q n y = 0 := by
  simp [perpQ, LinearMap.BilinForm.mem_orthogonal_iff]

theorem map_smul_elem (g : elementaryGroup Q) (x : V) : Q (g • x) = Q x :=
  map_of_mem (elementaryGroup_le_orthogonalGroup Q g.2) x

theorem polar_smul_elem (g : elementaryGroup Q) (x y : V) : polar Q (g • x) (g • y) = polar Q x y :=
  polar_map_of_mem (elementaryGroup_le_orthogonalGroup Q g.2) x y

theorem polar_inv_smul_elem (g : elementaryGroup Q) (x y : V) :
    polar Q (g⁻¹ • x) y = polar Q x (g • y) := by
  rw [← polar_smul_elem g (g⁻¹ • x) y, smul_inv_smul]

theorem smul_mem_perpQ_iff {U : Submodule K V} {g : elementaryGroup Q}
    (hg : g ∈ stabG (elementaryGroup Q) U) (y : V) :
    g • y ∈ perpQ Q U ↔ y ∈ perpQ Q U := by
  simp only [mem_perpQ]
  constructor
  · intro h n hn
    have := h (g • n) (smul_mem_of_mem_stabG hg hn)
    rwa [polar_smul_elem] at this
  · intro h n hn
    rw [← polar_inv_smul_elem]
    exact h _ (inv_smul_mem_of_mem_stabG hg hn)

theorem le_perpQ_of_ts {W : Submodule K V} (hW : ∀ w ∈ W, Q w = 0) : W ≤ perpQ Q W := by
  intro w hw
  rw [mem_perpQ]
  intro n hn
  have := hW (n + w) (W.add_mem hn hw)
  simp only [polar, this, hW n hn, hW w hw, sub_zero]

theorem eichlerΓ_inv (u t : V) : (eichlerΓ Q u t)⁻¹ = eichlerΓ Q u (-t) := by
  by_cases h : polar Q u t = 0
  · apply Subtype.ext
    exact eichler_inv h
  · have h' : polar Q u (-t) ≠ 0 := by rwa [polar_neg_right, neg_ne_zero]
    apply Subtype.ext
    show (eichler Q u t)⁻¹ = eichler Q u (-t)
    rw [eichler_of_polar_ne_zero h, eichler_of_polar_ne_zero h', inv_one]

theorem eichler_apply_mem_of_mem {W : Submodule K V} (hW : ∀ w ∈ W, Q w = 0) {u : V}
    (hu : u ∈ W) (t : V) {x : V} (hx : x ∈ W) : eichler Q u t x ∈ W := by
  by_cases h : Q u = 0 ∧ polar Q u t = 0
  · rw [eichler_apply h.1 h.2]
    have hxu : polar Q x u = 0 := mem_perpQ.1 (le_perpQ_of_ts hW hu) x hx
    rw [hxu, zero_smul, add_zero]
    exact W.sub_mem hx (W.smul_mem _ hu)
  · rw [eichler_of_not h]
    exact hx

theorem eichlerΓ_mem_stabG {W : Submodule K V} (hW : ∀ w ∈ W, Q w = 0) {u : V} (hu : u ∈ W)
    (t : V) : eichlerΓ Q u t ∈ stabG (elementaryGroup Q) W := by
  apply mem_stabG_of_forall
  · intro x hx
    exact eichler_apply_mem_of_mem hW hu t hx
  · intro x hx
    rw [eichlerΓ_inv]
    exact eichler_apply_mem_of_mem hW hu (-t) hx

@[expose] noncomputable def flagUQ (W : Submodule K V) (hW : ∀ w ∈ W, Q w = 0) :
    Subgroup (elementaryGroup Q) :=
  flagU (elementaryGroup Q) (perpQ Q) W (le_perpQ_of_ts hW)

theorem eichlerΓ_mem_flagUQ {W : Submodule K V} (hW : ∀ w ∈ W, Q w = 0) {u s : V}
    (hu : u ∈ W) (hs : s ∈ perpQ Q W) : eichlerΓ Q u s ∈ flagUQ W hW := by
  have hus : polar Q u s = 0 := mem_perpQ.1 hs u hu
  have hQu : Q u = 0 := hW u hu
  have huW : u ∈ perpQ Q W := le_perpQ_of_ts hW hu
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x => ?_⟩
  · exact eichler_apply_of_polar_eq_zero (mem_perpQ.1 huW x hx) (mem_perpQ.1 hs x hx)
  · have hxu : polar Q x u = 0 := by rw [polar_comm]; exact mem_perpQ.1 hx u hu
    show eichler Q u s x - x ∈ W
    rw [eichler_apply hQu hus, hxu, zero_smul, add_zero, mul_zero, add_zero]
    have : x - polar Q x s • u - x = -(polar Q x s • u) := by abel
    rw [this]
    exact W.neg_mem (W.smul_mem _ hu)
  · show eichler Q u s x - x ∈ perpQ Q W
    rw [eichler_apply hQu hus]
    have key : ∀ A B : V, x + A - B - x = A - B := fun A B => by abel
    rw [key]
    exact (perpQ Q W).sub_mem ((perpQ Q W).smul_mem _ hs) ((perpQ Q W).smul_mem _ huW)

theorem flagUQ_ne_bot [FiniteDimensional K V] (hnd : (polarBilin Q).Nondegenerate)
    (hd : 3 ≤ Module.finrank K V) {W : Submodule K V} (hW0 : W ≠ ⊥)
    (hW : ∀ w ∈ W, Q w = 0) : flagUQ W hW ≠ ⊥ := by
  obtain ⟨u, huW, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hex : ∃ s ∈ perpQ Q W, s ∉ Submodule.span K {u} := by
    by_contra hcon
    push Not at hcon
    have h1 : perpQ Q W ≤ Submodule.span K {u} := hcon
    have h2 : W ≤ Submodule.span K {u} := (le_perpQ_of_ts hW).trans h1
    have h3 := Submodule.finrank_mono h1
    have h4 := Submodule.finrank_mono h2
    have h5 : Module.finrank K (perpQ Q W) = Module.finrank K V - Module.finrank K W :=
      LinearMap.BilinForm.finrank_orthogonal hnd W
    have h6 := Submodule.finrank_le W
    have h7 : Module.finrank K (Submodule.span K {u}) = 1 := finrank_span_singleton hu0
    have h8 : 1 ≤ Module.finrank K W := Submodule.one_le_finrank_iff.2 hW0
    omega
  obtain ⟨s, hs, hsu⟩ := hex
  intro hbot
  have hmem := eichlerΓ_mem_flagUQ hW huW hs
  rw [hbot, Subgroup.mem_bot] at hmem
  obtain ⟨y, hy⟩ : ∃ y, polar Q y u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (hnd.1 u (fun y => by simpa [polar_comm] using hcon y))
  have hus : polar Q u s = 0 := mem_perpQ.1 hs u huW
  have := congrArg (fun g : elementaryGroup Q => g • y) hmem
  simp only [eichlerΓ_smul, one_smul] at this
  rw [eichler_apply (hW u huW) hus] at this
  apply hsu
  have h9 : polar Q y u • s - (polar Q y s + Q s * polar Q y u) • u = 0 := by
    simpa [add_sub_assoc] using this
  have h10 : s = (polar Q y u)⁻¹ • ((polar Q y s + Q s * polar Q y u) • u) := by
    rw [← sub_eq_zero.1 h9, smul_smul, inv_mul_cancel₀ hy, one_smul]
  rw [h10]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))

theorem isCompl_perpQ [FiniteDimensional K V] (hnd : (polarBilin Q).Nondegenerate)
    {W X : Submodule K V} (hc : IsCompl X (perpQ Q W)) : IsCompl W (perpQ Q X) := by
  have hdisj : W ⊓ perpQ Q X = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    obtain ⟨hwW, hwX⟩ := hw
    apply hnd.2 w
    intro v
    have hv : v ∈ X ⊔ perpQ Q W := by rw [hc.sup_eq_top]; trivial
    obtain ⟨x, hx, a, ha, rfl⟩ := Submodule.mem_sup.1 hv
    rw [polarBilin_apply_apply, polar_add_left, mem_perpQ.1 hwX x hx, zero_add, polar_comm]
    exact mem_perpQ.1 ha w hwW
  have hX : Module.finrank K X = Module.finrank K W := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hc
    have h2 : Module.finrank K (perpQ Q W) = Module.finrank K V - Module.finrank K W :=
      LinearMap.BilinForm.finrank_orthogonal hnd W
    have h3 := Submodule.finrank_le W
    omega
  refine ⟨disjoint_iff.2 hdisj, codisjoint_iff.2 ?_⟩
  apply Submodule.eq_top_of_finrank_eq
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq W (perpQ Q X)
  rw [hdisj, finrank_bot] at h4
  have h5 : Module.finrank K (perpQ Q X) = Module.finrank K V - Module.finrank K X :=
    LinearMap.BilinForm.finrank_orthogonal hnd X
  have h6 := Submodule.finrank_le X
  omega

theorem eichler_move [CharP K 2] {W₁ W₂ : Submodule K V} (h1 : ∀ w ∈ W₁, Q w = 0)
    (h2 : ∀ x ∈ W₂, Q x = 0) {x a : V} (hx : x ∈ W₂) (ha : a ∈ perpQ Q W₁)
    (hxW : x ∉ perpQ Q W₁) (hu : Q (x + a) = 0) :
    ∃ w ∈ W₁, ∃ t, eichler Q w t (x + a) = x := by
  obtain ⟨w, hw, hc⟩ : ∃ w ∈ W₁, polar Q w x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hxW (mem_perpQ.2 hcon)
  have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdbl : ∀ y : V, y + y = 0 := fun y => by rw [← two_smul K y, h2', zero_smul]
  set c := polar Q x w with hcdef
  have hc' : c ≠ 0 := by rw [hcdef, polar_comm]; exact hc
  have hQw : Q w = 0 := h1 w hw
  have hwa : polar Q w a = 0 := mem_perpQ.1 ha w hw
  have haw : polar Q a w = 0 := by rw [polar_comm]; exact hwa
  have haa : polar Q a a = 0 := by rw [polar_self_eq_two_mul, h2', zero_mul]
  have hxa : Q a + polar Q x a = 0 := by
    have := QuadraticMap.map_add Q x a
    rw [hu, h2 x hx, zero_add] at this
    exact this.symm
  refine ⟨w, hw, c⁻¹ • a, ?_⟩
  have hwt : polar Q w (c⁻¹ • a) = 0 := by rw [polar_smul_right_eq, hwa, mul_zero]
  rw [eichler_apply hQw hwt]
  have e1 : polar Q (x + a) w = c := by rw [polar_add_left, ← hcdef, haw, add_zero]
  have e2 : polar Q (x + a) (c⁻¹ • a) = c⁻¹ * polar Q x a := by
    rw [polar_smul_right_eq, polar_add_left, haa, add_zero]
  have e3 : Q (c⁻¹ • a) = c⁻¹ ^ 2 * Q a := map_smul_eq_sq Q _ _
  have e4 : polar Q (x + a) (c⁻¹ • a) + Q (c⁻¹ • a) * polar Q (x + a) w = 0 := by
    rw [e2, e3, e1]
    have : c⁻¹ * polar Q x a + c⁻¹ ^ 2 * Q a * c = c⁻¹ * (Q a + polar Q x a) := by
      field_simp
      ring
    rw [this, hxa, mul_zero]
  rw [e4, zero_smul, sub_zero, e1, smul_smul, mul_inv_cancel₀ hc', one_smul, add_assoc, hdbl,
    add_zero]

section Move

variable [CharP K 2] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem exists_mem_move {W₁ W₂ : Submodule K V} (h1 : ∀ w ∈ W₁, Q w = 0)
    (h2 : ∀ x ∈ W₂, Q x = 0) {C : Subgroup (elementaryGroup Q)}
    (hC : stabG (elementaryGroup Q) W₁ ≤ C) {x a : V} (hx : x ∈ W₂) (ha : a ∈ perpQ Q W₁)
    (hxW : x ∉ perpQ Q W₁) (hu : Q (x + a) = 0) : ∃ g ∈ C, g • (x + a) = x := by
  obtain ⟨w, hw, t, ht⟩ := eichler_move h1 h2 hx ha hxW hu
  exact ⟨eichlerΓ Q w t, hC (eichlerΓ_mem_stabG h1 hw t), ht⟩

theorem eichlerΓ_mem_of_stab_le (hnd : (polarBilin Q).Nondegenerate) {W X : Submodule K V}
    (hW0 : W ≠ ⊥) (hWs : ∀ w ∈ W, Q w = 0) (hXs : ∀ x ∈ X, Q x = 0)
    (hc : IsCompl X (perpQ Q W)) {C : Subgroup (elementaryGroup Q)}
    (hWC : stabG (elementaryGroup Q) W ≤ C) (hXC : stabG (elementaryGroup Q) X ≤ C) (u s : V) :
    eichlerΓ Q u s ∈ C := by
  by_cases hu : Q u = 0 ∧ polar Q u s = 0
  swap
  · have : eichlerΓ Q u s = 1 := Subtype.ext (eichler_of_not hu)
    rw [this]
    exact C.one_mem
  obtain ⟨hu0, hus⟩ := hu
  by_cases hu00 : u = 0
  · have : eichlerΓ Q u s = 1 := Subtype.ext (by rw [hu00]; exact eichler_zero_left Q s)
    rw [this]
    exact C.one_mem
  have hc' := isCompl_perpQ hnd hc
  have hrefl : (polarBilin Q).IsRefl := fun x y h => by
    rw [polarBilin_apply_apply] at h ⊢
    rwa [polar_comm]
  have claim2 : ∀ w' a' : V, w' ∈ W → a' ∈ perpQ Q X → w' ≠ 0 → Q (w' + a') = 0 →
      ∃ g ∈ C, g • (w' + a') ∈ W := fun w' a' hw' ha' hw'0 hQ => by
    have hw'X : w' ∉ perpQ Q X := fun h => hw'0 (by
      have : w' ∈ W ⊓ perpQ Q X := ⟨hw', h⟩
      rwa [hc'.inf_eq_bot, Submodule.mem_bot] at this)
    obtain ⟨g, hgC, hg⟩ := exists_mem_move hXs hWs hXC hw' ha' hw'X hQ
    exact ⟨g, hgC, by rw [hg]; exact hw'⟩
  obtain ⟨g, hgC, hgu⟩ : ∃ g ∈ C, g • u ∈ W ∨ g • u ∈ X := by
    have huv : u ∈ X ⊔ perpQ Q W := by rw [hc.sup_eq_top]; trivial
    obtain ⟨x, hx, a, ha, huxa⟩ := Submodule.mem_sup.1 huv
    by_cases hx0 : x = 0
    ·
      subst hx0
      rw [zero_add] at huxa
      subst huxa
      have huv' : a ∈ W ⊔ perpQ Q X := by rw [hc'.sup_eq_top]; trivial
      obtain ⟨w', hw', a', ha', hwa⟩ := Submodule.mem_sup.1 huv'
      by_cases hw'0 : w' = 0
      ·
        subst hw'0
        rw [zero_add] at hwa
        subst hwa
        have huW : a' ∉ W := fun h => hu00 (by
          have : a' ∈ W ⊓ perpQ Q X := ⟨h, ha'⟩
          rwa [hc'.inf_eq_bot, Submodule.mem_bot] at this)
        obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
        obtain ⟨t₀, ht₀, hut₀⟩ : ∃ t₀ ∈ perpQ Q W, polar Q a' t₀ ≠ 0 := by
          by_contra hcon
          push Not at hcon
          apply huW
          have hmem : a' ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (perpQ Q W) := by
            rw [LinearMap.BilinForm.mem_orthogonal_iff]
            intro n hn
            rw [polarBilin_apply_apply, polar_comm]
            exact hcon n hn
          rwa [show LinearMap.BilinForm.orthogonal (polarBilin Q) (perpQ Q W) = W from
            LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl W] at hmem
        have hg₀C : eichlerΓ Q w₀ t₀ ∈ C := hWC (eichlerΓ_mem_stabG hWs hw₀ t₀)
        have hw₀t₀ : polar Q w₀ t₀ = 0 := mem_perpQ.1 ht₀ w₀ hw₀
        have hg₀u : eichlerΓ Q w₀ t₀ • a' = (-(polar Q a' t₀)) • w₀ + a' := by
          show eichler Q w₀ t₀ a' = _
          rw [eichler_apply (hWs w₀ hw₀) hw₀t₀]
          have : polar Q a' w₀ = 0 := by rw [polar_comm]; exact mem_perpQ.1 ha w₀ hw₀
          rw [this, zero_smul, add_zero, mul_zero, add_zero, sub_eq_add_neg, add_comm, neg_smul]
        obtain ⟨g₁, hg₁C, hg₁⟩ := claim2 ((-(polar Q a' t₀)) • w₀) a'
          (W.smul_mem _ hw₀) ha' (smul_ne_zero (neg_ne_zero.2 hut₀) hw₀0)
          (by rw [← hg₀u]; exact (map_smul_elem _ _).trans hu0)
        refine ⟨g₁ * eichlerΓ Q w₀ t₀, C.mul_mem hg₁C hg₀C, Or.inl ?_⟩
        rw [mul_smul, hg₀u]
        exact hg₁
      · obtain ⟨g, hgC, hg⟩ := claim2 w' a' hw' ha' hw'0 (by rw [hwa]; exact hu0)
        exact ⟨g, hgC, Or.inl (by rw [hwa] at hg; exact hg)⟩
    ·
      subst huxa
      have hxW : x ∉ perpQ Q W := fun h => hx0 (by
        have : x ∈ X ⊓ perpQ Q W := ⟨hx, h⟩
        rwa [hc.inf_eq_bot, Submodule.mem_bot] at this)
      obtain ⟨g, hgC, hg⟩ := exists_mem_move hWs hXs hWC hx ha hxW hu0
      exact ⟨g, hgC, Or.inr (by rw [hg]; exact hx)⟩
  have hconj : eichlerΓ Q u s = g⁻¹ * eichlerΓ Q (g • u) (g • s) * g := by
    have : g * eichlerΓ Q u s * g⁻¹ = eichlerΓ Q (g • u) (g • s) :=
      Subtype.ext (eichler_conj (elementaryGroup_le_orthogonalGroup Q g.2) u s)
    rw [← this]
    group
  rw [hconj]
  refine C.mul_mem (C.mul_mem (C.inv_mem hgC) ?_) hgC
  rcases hgu with h | h
  · exact hWC (eichlerΓ_mem_stabG hWs h _)
  · exact hXC (eichlerΓ_mem_stabG hXs h _)

end Move

section Main

variable [Finite K] [CharP K 2] [FiniteDimensional K V]

theorem twoLocalClosure_eq_top_elementary (hnd : (polarBilin Q).Nondegenerate)
    (hd : 3 ≤ Module.finrank K V) (β₀ : LinearMap.BilinForm K V) (hβ₀ : ∀ x, β₀ x x = Q x)
    (E : Subgroup (elementaryGroup Q)) (hE : Odd (Nat.card E)) {W : Submodule K V}
    (hW0 : W ≠ ⊥) (hWs : ∀ w ∈ W, Q w = 0) (hWE : ∀ e ∈ E, ∀ x ∈ W, e • x ∈ W) :
    twoLocalClosure E = ⊤ := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V))
    (fun a b h => LinearEquiv.ext (congrFun h))
  have : Finite E := inferInstance
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨X, hc, hXs, hXE⟩ := exists_singular_compl Q hnd β₀ hβ₀ map_smul_elem E hE hWs hWE
  have hX0 : X ≠ ⊥ := by
    intro hXbot
    have htop : perpQ Q W = ⊤ := by
      have := hc.sup_eq_top
      rwa [hXbot, bot_sup_eq] at this
    apply hW0
    rw [Submodule.eq_bot_iff]
    intro w hw
    apply hnd.1 w
    intro y
    rw [polarBilin_apply_apply]
    exact mem_perpQ.1 (htop ▸ Submodule.mem_top : y ∈ perpQ Q W) w hw
  have hc' := isCompl_perpQ hnd hc
  have hWC : stabG (elementaryGroup Q) W ≤ twoLocalClosure E :=
    stabG_le_twoLocalClosure (P := perpQ Q) (fun hh y => smul_mem_perpQ_iff hh y) h2
      (flagUQ_ne_bot hnd hd hW0 hWs) (le_stabG_of_invariant hWE)
  have hXC : stabG (elementaryGroup Q) X ≤ twoLocalClosure E :=
    stabG_le_twoLocalClosure (P := perpQ Q) (fun hh y => smul_mem_perpQ_iff hh y) h2
      (flagUQ_ne_bot hnd hd hX0 hXs) (le_stabG_of_invariant hXE)
  have hall := eichlerΓ_mem_of_stab_le hnd hW0 hWs hXs hc hWC hXC
  rw [eq_top_iff]
  have hle : elementaryGroup Q ≤ (twoLocalClosure E).map (elementaryGroup Q).subtype := by
    apply elementaryGroup_le_of_eichler_mem
    intro u w _ _
    exact ⟨eichlerΓ Q u w, hall u w, rfl⟩
  intro g _
  obtain ⟨c, hcC, hcg⟩ := hle g.2
  have : c = g := Subtype.ext hcg
  rw [← this]
  exact hcC

end Main

end OrthClosure

end CFSG.LocalAnalysis.RankThreeUC
