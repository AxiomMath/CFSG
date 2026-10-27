module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureUnitCompl

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace UnitClosure

open Subgroup CFSG.LieType.BorelTits LinClosure

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {F : ReflForm K V}
  {Γ : Subgroup (V ≃ₗ[K] V)}

theorem mem_stabG_of_eichler [Finite V] {W : Submodule K V} (hW : F.IsTotallyIsotropic W)
    {w y : V} {c : K} (hw : w ∈ W) {g : Γ}
    (hg : ∀ v, g • v = v + F.β w v • (y + c • w) - F.β y v • w) : g ∈ stabG Γ W := by
  apply mem_stabG_of_forall_fin
  intro v hv
  rw [hg, F.mem_perp.1 (hW hv) w hw, zero_smul, add_zero]
  exact W.sub_mem hv (W.smul_mem _ hw)

theorem mem_stabG_of_tv [Finite V] {W : Submodule K V} {a : V} {c : K} (ha : a ∈ W) {g : Γ}
    (hg : ∀ v, g • v = v + (c * F.β a v) • a) : g ∈ stabG Γ W := by
  apply mem_stabG_of_forall_fin
  intro v hv
  rw [hg]
  exact W.add_mem hv (W.smul_mem _ ha)

theorem UnitData.conj_tv (hU : UnitData F Γ) {T : Γ} {a : V} {c : K}
    (hT : ∀ v, T • v = v + (c * F.β a v) • a) (h : Γ) (v : V) :
    (h * T * h⁻¹) • v = v + (c * F.β (h • a) v) • (h • a) := by
  rw [mul_smul, mul_smul, hT, smul_add, smul_inv_smul, smul_smul_K]
  congr 3
  rw [← hU.iso h a (h⁻¹ • v), smul_inv_smul]

theorem flagU_ne_bot [FiniteDimensional K V] (hU : UnitData F Γ)
    (hd : 3 ≤ Module.finrank K V) {W : Submodule K V} (hW0 : W ≠ ⊥)
    (hW : F.IsTotallyIsotropic W) : flagU Γ F.perp W hW ≠ ⊥ := by
  obtain ⟨u, huW, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hex : ∃ s ∈ F.perp W, s ∉ Submodule.span K {u} := by
    by_contra hcon
    push Not at hcon
    have h1 : F.perp W ≤ Submodule.span K {u} := hcon
    have h2 : W ≤ Submodule.span K {u} := hW.trans h1
    have h3 := Submodule.finrank_mono h1
    have h4 := Submodule.finrank_mono h2
    have h5 := F.finrank_perp W
    have h7 : Module.finrank K (Submodule.span K {u}) = 1 := finrank_span_singleton hu0
    have h8 : 1 ≤ Module.finrank K W := Submodule.one_le_finrank_iff.2 hW0
    omega
  obtain ⟨s, hs, hsu⟩ := hex
  have huu : F.β u u = 0 := F.mem_perp.1 (hW huW) u huW
  have hus : F.β u s = 0 := F.mem_perp.1 hs u huW
  obtain ⟨γ, hγ⟩ := hU.trace (-F.β s s) (by rw [map_neg, hU.herm])
  obtain ⟨g, hg⟩ := hU.eichler u s γ huu hus hγ
  have huW' : u ∈ F.perp W := hW huW
  have hmem : g ∈ flagU Γ F.perp W hW := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x => ?_⟩
    · have : F.β s x = 0 := by rw [← hU.herm x s, F.mem_perp.1 hs x hx, map_zero]
      rw [hg, F.mem_perp.1 (hW hx) u huW, zero_smul, add_zero, this, zero_smul, sub_zero]
    · show g • x - x ∈ W
      rw [hg, F.mem_perp.1 hx u huW, zero_smul, add_zero]
      have : x - F.β s x • u - x = -(F.β s x • u) := by abel
      rw [this]
      exact W.neg_mem (W.smul_mem _ huW)
    · show g • x - x ∈ F.perp W
      rw [hg]
      have key : ∀ A B : V, x + A - B - x = A - B := fun A B => by abel
      rw [key]
      exact (F.perp W).sub_mem ((F.perp W).smul_mem _
        ((F.perp W).add_mem hs ((F.perp W).smul_mem _ huW'))) ((F.perp W).smul_mem _ huW')
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hmem
  obtain ⟨y, hy⟩ : ∃ y, F.β u y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (F.nondeg u hcon)
  have h1 := hg y
  rw [hmem, one_smul] at h1
  have h9 : F.β u y • s - (F.β s y - F.β u y * γ) • u = 0 := by
    calc F.β u y • s - (F.β s y - F.β u y * γ) • u
        = (y + F.β u y • (s + γ • u) - F.β s y • u) - y := by module
      _ = 0 := sub_eq_zero.2 h1.symm
  have h10 : s = (F.β u y)⁻¹ • ((F.β s y - F.β u y * γ) • u) := by
    rw [← sub_eq_zero.1 h9, smul_smul, inv_mul_cancel₀ hy, one_smul]
  apply hsu
  rw [h10]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))

theorem isCompl_perp [FiniteDimensional K V] (herm : ∀ u v, F.σ (F.β u v) = F.β v u)
    {W X : Submodule K V} (hc : IsCompl X (F.perp W)) : IsCompl W (F.perp X) := by
  have hdisj : W ⊓ F.perp X = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    obtain ⟨hwW, hwX⟩ := hw
    apply F.nondeg w
    intro v
    have hv : v ∈ X ⊔ F.perp W := by rw [hc.sup_eq_top]; trivial
    obtain ⟨x, hx, a, ha, rfl⟩ := Submodule.mem_sup.1 hv
    have h1 : F.β w x = 0 := by rw [← herm x w, F.mem_perp.1 hwX x hx, map_zero]
    rw [F.add_right, h1, F.mem_perp.1 ha w hwW, add_zero]
  have hX : Module.finrank K X = Module.finrank K W := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hc
    have h2 := F.finrank_perp W
    omega
  refine ⟨disjoint_iff.2 hdisj, codisjoint_iff.2 ?_⟩
  apply Submodule.eq_top_of_finrank_eq
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq W (F.perp X)
  rw [hdisj, finrank_bot] at h4
  have h5 := F.finrank_perp X
  omega

section Move

variable [Finite V] [CharP K 2]

theorem exists_eichler_move (hU : UnitData F Γ) {W₁ W₂ : Submodule K V}
    (h1 : F.IsTotallyIsotropic W₁) (h2 : F.IsTotallyIsotropic W₂) {x a : V} (hx : x ∈ W₂)
    (ha : a ∈ F.perp W₁) (hxW : x ∉ F.perp W₁) (hu : F.β (x + a) (x + a) = 0) :
    ∃ g : Γ, g ∈ stabG Γ W₁ ∧ g • (x + a) = x := by
  obtain ⟨w, hw, hc⟩ : ∃ w ∈ W₁, F.β w x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hxW (F.mem_perp.2 hcon)
  have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdbl : ∀ y : V, y + y = 0 := fun y => by rw [← two_smul K y, h2', zero_smul]
  have hww : F.β w w = 0 := F.mem_perp.1 (h1 hw) w hw
  have hwa : F.β w a = 0 := F.mem_perp.1 ha w hw
  have hxx : F.β x x = 0 := F.mem_perp.1 (h2 hx) x hx
  set c := F.β w x with hcdef
  have hσc : F.σ c ≠ 0 := fun h => hc ((map_eq_zero_iff _ F.σ.injective).1 h)
  set N := F.σ c * c with hN
  have hN0 : N ≠ 0 := mul_ne_zero hσc hc
  have hwt : F.β w (c⁻¹ • a) = 0 := by rw [F.smul_right, hwa, mul_zero]
  have hsigma : F.σ N = N := by rw [hN, map_mul, hU.invol, mul_comm]
  have hiso : F.β a x + F.β x a + F.β a a = 0 := by
    have := hu
    rw [F.add_left, F.add_right, F.add_right, hxx, zero_add] at this
    linear_combination this
  set γ := (F.β a x + F.β a a) * N⁻¹ with hγdef
  have hγ : γ + F.σ γ = -F.β (c⁻¹ • a) (c⁻¹ • a) := by
    rw [F.smul_left, F.smul_right, hγdef, map_mul, map_add, hU.herm a x, hU.herm a a,
      map_inv₀, hsigma, map_inv₀]
    field_simp
    rw [hN]
    linear_combination (F.σ c * c) * hiso + (F.σ c * c) * F.β a a * h2'
  obtain ⟨g, hg⟩ := hU.eichler w (c⁻¹ • a) γ hww hwt hγ
  refine ⟨g, mem_stabG_of_eichler h1 hw hg, ?_⟩
  rw [hg]
  have e1 : F.β w (x + a) = c := by rw [F.add_right, hwa, add_zero]
  have e2 : F.β (c⁻¹ • a) (x + a) = (F.σ c)⁻¹ * (F.β a x + F.β a a) := by
    rw [F.smul_left, F.add_right, map_inv₀]
  have e3 : c • (c⁻¹ • a + γ • w) = a + (c * γ) • w := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hc, one_smul, smul_smul]
  have e4 : c * γ = (F.σ c)⁻¹ * (F.β a x + F.β a a) := by
    rw [hγdef, hN]
    field_simp
  rw [e1, e2, e3, e4]
  have : x + a + (a + ((F.σ c)⁻¹ * (F.β a x + F.β a a)) • w) -
      ((F.σ c)⁻¹ * (F.β a x + F.β a a)) • w = x + (a + a) := by abel
  rw [this, hdbl, add_zero]

end Move

section Main

variable [CharP K 2] [FiniteDimensional K V] [Finite K]

theorem tv_mem_of_stab_le (hU : UnitData F Γ) {W X : Submodule K V} (hW0 : W ≠ ⊥)
    (hW : F.IsTotallyIsotropic W) (hX : F.IsTotallyIsotropic X) (hc : IsCompl X (F.perp W))
    {C : Subgroup Γ} (hWC : stabG Γ W ≤ C) (hXC : stabG Γ X ≤ C) {T : Γ} {a : V} {c : K}
    (ha : F.β a a = 0) (hT : ∀ v, T • v = v + (c * F.β a v) • a) : T ∈ C := by
  have : Finite V := Module.finite_of_finite K
  by_cases ha0 : a = 0
  · have : T = 1 := ext_smul fun v => by
      rw [hT, ha0, smul_zero, add_zero, one_smul]
    rw [this]
    exact C.one_mem
  have hc' := isCompl_perp hU.herm hc
  have claim2 : ∀ w' a' : V, w' ∈ W → a' ∈ F.perp X → w' ≠ 0 →
      F.β (w' + a') (w' + a') = 0 → ∃ g ∈ C, g • (w' + a') ∈ W :=
    fun w' a' hw' ha' hw'0 hQ => by
      have hw'X : w' ∉ F.perp X := fun h => hw'0 (by
        have : w' ∈ W ⊓ F.perp X := ⟨hw', h⟩
        rwa [hc'.inf_eq_bot, Submodule.mem_bot] at this)
      obtain ⟨g, hg, hgw⟩ := exists_eichler_move hU hX hW hw' ha' hw'X hQ
      exact ⟨g, hXC hg, by rw [hgw]; exact hw'⟩
  obtain ⟨g, hgC, hga⟩ : ∃ g ∈ C, g • a ∈ W ∨ g • a ∈ X := by
    have hav : a ∈ X ⊔ F.perp W := by rw [hc.sup_eq_top]; trivial
    obtain ⟨x, hx, a₁, ha₁, hxa⟩ := Submodule.mem_sup.1 hav
    by_cases hx0 : x = 0
    ·
      subst hx0
      rw [zero_add] at hxa
      subst hxa
      have hav' : a₁ ∈ W ⊔ F.perp X := by rw [hc'.sup_eq_top]; trivial
      obtain ⟨w', hw', a', ha', hwa⟩ := Submodule.mem_sup.1 hav'
      by_cases hw'0 : w' = 0
      · subst hw'0
        rw [zero_add] at hwa
        subst hwa
        have haW : a' ∉ W := fun h => ha0 (by
          have : a' ∈ W ⊓ F.perp X := ⟨h, ha'⟩
          rwa [hc'.inf_eq_bot, Submodule.mem_bot] at this)
        obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
        obtain ⟨t₀, ht₀, hat₀⟩ : ∃ t₀ ∈ F.perp W, F.β t₀ a' ≠ 0 := by
          by_contra hcon
          push Not at hcon
          apply haW
          rw [← F.perp_perp W]
          exact hcon
        have hww₀ : F.β w₀ w₀ = 0 := F.mem_perp.1 (hW hw₀) w₀ hw₀
        have hwt₀ : F.β w₀ t₀ = 0 := F.mem_perp.1 ht₀ w₀ hw₀
        obtain ⟨γ₀, hγ₀⟩ := hU.trace (-F.β t₀ t₀) (by rw [map_neg, hU.herm])
        obtain ⟨g₀, hg₀⟩ := hU.eichler w₀ t₀ γ₀ hww₀ hwt₀ hγ₀
        have hg₀C : g₀ ∈ C := hWC (mem_stabG_of_eichler hW hw₀ hg₀)
        have hg₀a : g₀ • a' = (-F.β t₀ a') • w₀ + a' := by
          rw [hg₀, F.mem_perp.1 ha₁ w₀ hw₀, zero_smul, add_zero]
          rw [sub_eq_add_neg, add_comm, neg_smul]
        obtain ⟨g₁, hg₁C, hg₁⟩ := claim2 ((-F.β t₀ a') • w₀) a' (W.smul_mem _ hw₀) ha'
          (smul_ne_zero (neg_ne_zero.2 hat₀) hw₀0)
          (by rw [← hg₀a, hU.iso]; exact ha)
        exact ⟨g₁ * g₀, C.mul_mem hg₁C hg₀C, Or.inl (by rw [mul_smul, hg₀a]; exact hg₁)⟩
      · obtain ⟨g, hgC, hg⟩ := claim2 w' a' hw' ha' hw'0 (by rw [hwa]; exact ha)
        exact ⟨g, hgC, Or.inl (by rw [hwa] at hg; exact hg)⟩
    ·
      subst hxa
      have hxW : x ∉ F.perp W := fun h => hx0 (by
        have : x ∈ X ⊓ F.perp W := ⟨hx, h⟩
        rwa [hc.inf_eq_bot, Submodule.mem_bot] at this)
      obtain ⟨g, hg, hgx⟩ := exists_eichler_move hU hW hX hx ha₁ hxW ha
      exact ⟨g, hWC hg, Or.inr (by rw [hgx]; exact hx)⟩
  have hconj := hU.conj_tv hT g
  have hmem : g * T * g⁻¹ ∈ C := by
    rcases hga with h | h
    · exact hWC (mem_stabG_of_tv h (hconj))
    · exact hXC (mem_stabG_of_tv h (hconj))
  have : T = g⁻¹ * (g * T * g⁻¹) * g := by group
  rw [this]
  exact C.mul_mem (C.mul_mem (C.inv_mem hgC) hmem) hgC

theorem tv_mem_twoLocalClosure (hU : UnitData F Γ) (hd : 3 ≤ Module.finrank K V)
    (E : Subgroup Γ) (hE : Odd (Nat.card E)) {W : Submodule K V} (hW0 : W ≠ ⊥)
    (hW : F.IsTotallyIsotropic W) (hWE : ∀ e ∈ E, ∀ x ∈ W, e • x ∈ W) {T : Γ} {a : V} {c : K}
    (ha : F.β a a = 0) (hT : ∀ v, T • v = v + (c * F.β a v) • a) : T ∈ twoLocalClosure E := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V))
    (fun a b h => LinearEquiv.ext (congrFun h))
  have : Finite E := inferInstance
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨X, hc, hX, hXE⟩ := exists_isotropic_compl hU E hE hW hWE
  have hX0 : X ≠ ⊥ := by
    intro hXbot
    have htop : F.perp W = ⊤ := by
      have := hc.sup_eq_top
      rwa [hXbot, bot_sup_eq] at this
    apply hW0
    rw [Submodule.eq_bot_iff]
    intro w hw
    apply F.nondeg w
    intro y
    exact F.mem_perp.1 (htop ▸ Submodule.mem_top : y ∈ F.perp W) w hw
  have hP : ∀ {h : Γ}, h ∈ stabG Γ W → ∀ y, h • y ∈ F.perp W ↔ y ∈ F.perp W :=
    fun hh y => hU.smul_mem_perp_iff hh y
  have hWC : stabG Γ W ≤ twoLocalClosure E :=
    stabG_le_twoLocalClosure hP h2 (flagU_ne_bot hU hd hW0 hW) (le_stabG_of_invariant hWE)
  have hXC : stabG Γ X ≤ twoLocalClosure E :=
    stabG_le_twoLocalClosure (hW := hX) (fun {h} hh y => hU.smul_mem_perp_iff hh y) h2
      (flagU_ne_bot hU hd hX0 hX) (le_stabG_of_invariant hXE)
  exact tv_mem_of_stab_le hU hW0 hW hX hc hWC hXC ha hT

end Main

end UnitClosure

end CFSG.LocalAnalysis.RankThreeUC
