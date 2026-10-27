module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderDefs

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

open CFSG.RankThree.FFModules
open scoped commutatorElement

section Abstract

theorem eq_bot_of_le_commutator {Q : Type*} [Group Q] [Finite Q] {N B : Subgroup Q}
    (hN : IsPGroup 2 N) (hB : IsPGroup 2 B) (hBN : B ≤ Subgroup.normalizer N)
    (h : N ≤ ⁅N, B⁆) : N = ⊥ := by
  have hP : IsPGroup 2 (B ⊔ N : Subgroup Q) := hB.to_sup_of_normal_right' hN hBN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hP.isNilpotent
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries (B ⊔ N)).1 inferInstance
  have key : ∀ k, N ≤ (B ⊔ N).lowerCentralSeries k := by
    intro k
    induction k with
    | zero => exact le_sup_right
    | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      exact h.trans (Subgroup.commutator_mono ih le_sup_left)
  exact le_bot_iff.1 (hn ▸ key n)

theorem isPGroup_two_of_mul_self_eq_one {Q : Type*} [Group Q] {N : Subgroup Q}
    (h : ∀ n ∈ N, n * n = 1) : IsPGroup 2 N := by
  intro g
  have h2 : (g : N) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using h g g.2
  exact ⟨1, by simpa using h2⟩

theorem le_normalizer_of_conj_mem {Q : Type*} [Group Q] {N B : Subgroup Q}
    (h : ∀ b ∈ B, ∀ n ∈ N, b * n * b⁻¹ ∈ N) : B ≤ Subgroup.normalizer N := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨h b hb n, fun hn => ?_⟩
  have := h b⁻¹ (B.inv_mem hb) _ hn
  simpa [mul_assoc] using this

end Abstract

section CommOn

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem two_nsmul_eq_zero' (w : V) : w + w = 0 := by
  have : (2 : ZMod 2) = 0 := by decide
  rw [← two_smul (ZMod 2) w, this, zero_smul]

theorem sub_mem_commOn {ρ : Representation (ZMod 2) G V} {A : Subgroup G}
    {U : Submodule (ZMod 2) V} {a : G} (ha : a ∈ A) {u : V} (hu : u ∈ U) :
    ρ a u - u ∈ commOn ρ A U :=
  Submodule.subset_span ⟨a, ha, u, hu, rfl⟩

theorem commOn_mono_right {ρ : Representation (ZMod 2) G V} {A : Subgroup G}
    {U U' : Submodule (ZMod 2) V} (h : U ≤ U') : commOn ρ A U ≤ commOn ρ A U' :=
  Submodule.span_mono fun _ ⟨a, ha, u, hu, hw⟩ => ⟨a, ha, u, h hu, hw⟩

theorem commOn_mono_left {ρ : Representation (ZMod 2) G V} {A B : Subgroup G}
    {U : Submodule (ZMod 2) V} (h : A ≤ B) : commOn ρ A U ≤ commOn ρ B U :=
  Submodule.span_mono fun _ ⟨a, ha, u, hu, hw⟩ => ⟨a, h ha, u, hu, hw⟩

theorem rep_conj_apply (ρ : Representation (ZMod 2) G V) (g b : G) (u : V) :
    ρ (g * b * g⁻¹) (ρ g u) = ρ g (ρ b u) := by
  simp [map_mul, Module.End.mul_apply]

theorem rep_mem_commOn {ρ : Representation (ZMod 2) G V} {B : Subgroup G} {g : G}
    (hg : ∀ b ∈ B, g * b * g⁻¹ ∈ B) {U : Submodule (ZMod 2) V}
    (hU : ∀ u ∈ U, ρ g u ∈ U) {w : V} (hw : w ∈ commOn ρ B U) : ρ g w ∈ commOn ρ B U := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, hb, u, hu, rfl⟩ := hw
    have : ρ g (ρ b u - u) = ρ (g * b * g⁻¹) (ρ g u) - ρ g u := by
      rw [rep_conj_apply, map_sub]
    rw [this]
    exact sub_mem_commOn (hg b hb) (hU u hu)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

def stabSub (ρ : Representation (ZMod 2) G V) (W : Submodule (ZMod 2) V) : Subgroup G where
  carrier := {g | (∀ w ∈ W, ρ g w ∈ W) ∧ ∀ w ∈ W, ρ g⁻¹ w ∈ W}
  mul_mem' {g h} hg hh := by
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rw [map_mul, Module.End.mul_apply]; exact hg.1 _ (hh.1 w hw)
    · rw [mul_inv_rev, map_mul, Module.End.mul_apply]; exact hh.2 _ (hg.2 w hw)
  one_mem' := ⟨fun w hw => by simpa using hw, fun w hw => by simpa using hw⟩
  inv_mem' {g} hg := ⟨hg.2, by simpa using hg.1⟩

theorem le_stabSub {ρ : Representation (ZMod 2) G V} {W : Submodule (ZMod 2) V}
    {B : Subgroup G} (h : ∀ g ∈ B, ∀ w ∈ W, ρ g w ∈ W) : B ≤ stabSub ρ W :=
  fun g hg => ⟨h g hg, h g⁻¹ (B.inv_mem hg)⟩

noncomputable def quotHom (ρ : Representation (ZMod 2) G V) (W : Submodule (ZMod 2) V) :
    stabSub ρ W →* (Module.End (ZMod 2) (V ⧸ W))ˣ :=
  MonoidHom.toHomUnits
    (Representation.quotient (ρ.comp (stabSub ρ W).subtype) W
      (fun g w hw => g.2.1 w hw))

theorem quotHom_mk (ρ : Representation (ZMod 2) G V) (W : Submodule (ZMod 2) V)
    (s : stabSub ρ W) (v : V) :
    (quotHom ρ W s : Module.End (ZMod 2) (V ⧸ W)) (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (ρ s v) := by
  rfl

theorem invariant_commOn_top {ρ : Representation (ZMod 2) G V} {A L : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    (∀ g ∈ L, ∀ u ∈ commOn ρ L ⊤, ρ g u ∈ commOn ρ L ⊤) ∧
      (∀ g ∈ A, ∀ u ∈ commOn ρ L ⊤, ρ g u ∈ commOn ρ L ⊤) := by
  refine ⟨fun g hg u hu => rep_mem_commOn (U := ⊤) (fun b hb => ?_) (fun _ _ => Submodule.mem_top) hu,
    fun g hg u hu => rep_mem_commOn (U := ⊤) (fun b hb => ?_) (fun _ _ => Submodule.mem_top) hu⟩
  · exact L.mul_mem (L.mul_mem hg hb) (L.inv_mem hg)
  · exact (Subgroup.mem_normalizer_iff.1 (hAL hg) b).1 hb

theorem commOn_commOn_eq [Finite V] {ρ : Representation (ZMod 2) G V} {A L : Subgroup G}
    (hA2 : CFSG.IsElementaryAbelian 2 A) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hLA : ⁅L, A⁆ = L) : commOn ρ L (commOn ρ L ⊤) = commOn ρ L ⊤ := by
  set V₁ := commOn ρ L ⊤ with hV₁
  set V₂ := commOn ρ L V₁ with hV₂
  have hle : V₂ ≤ V₁ := commOn_mono_right le_top
  refine le_antisymm hle ?_
  obtain ⟨hL1, hA1⟩ := invariant_commOn_top (ρ := ρ) hAL
  have hL2 : ∀ g ∈ L, ∀ u ∈ V₂, ρ g u ∈ V₂ := fun g hg u hu =>
    rep_mem_commOn (fun b hb => L.mul_mem (L.mul_mem hg hb) (L.inv_mem hg)) (hL1 g hg) hu
  have hA2' : ∀ g ∈ A, ∀ u ∈ V₂, ρ g u ∈ V₂ := fun g hg u hu =>
    rep_mem_commOn (fun b hb => (Subgroup.mem_normalizer_iff.1 (hAL hg) b).1 hb) (hA1 g hg) hu
  have hLS : L ≤ stabSub ρ V₂ := le_stabSub hL2
  have hAS : A ≤ stabSub ρ V₂ := le_stabSub hA2'
  set S := stabSub ρ V₂ with hS
  set τ := quotHom ρ V₂ with hτ
  set N : Subgroup (Module.End (ZMod 2) (V ⧸ V₂))ˣ := (L.subgroupOf S).map τ with hN
  set B : Subgroup (Module.End (ZMod 2) (V ⧸ V₂))ˣ := (A.subgroupOf S).map τ with hB
  have hτk : ∀ (s : S) (v : V), (τ s : Module.End (ZMod 2) (V ⧸ V₂)) (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (ρ s v) := quotHom_mk ρ V₂
  have hfin : Finite (Module.End (ZMod 2) (V ⧸ V₂))ˣ := by
    have : Finite (V ⧸ V₂) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective V₂)
    have : Finite (Module.End (ZMod 2) (V ⧸ V₂)) :=
      Finite.of_injective (fun f : Module.End (ZMod 2) (V ⧸ V₂) => (f : V ⧸ V₂ → V ⧸ V₂))
        DFunLike.coe_injective
    exact Finite.of_injective (fun u : (Module.End (ZMod 2) (V ⧸ V₂))ˣ =>
      (u : Module.End (ZMod 2) (V ⧸ V₂))) Units.val_injective
  have hsq : ∀ l ∈ L, ∀ hl : l ∈ S, τ ⟨l, hl⟩ * τ ⟨l, hl⟩ = 1 := by
    intro l hl hlS
    apply Units.ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      simp only [Units.val_mul, Module.End.mul_apply, hτk, Units.val_one,
        Module.End.one_apply]
      rw [Submodule.Quotient.eq]
      have hw : ρ l v - v ∈ V₁ := sub_mem_commOn hl Submodule.mem_top
      have h2 : ρ l (ρ l v - v) - (ρ l v - v) ∈ V₂ := sub_mem_commOn hl hw
      have e : ρ l (ρ l v) - v = ρ l (ρ l v - v) - (ρ l v - v) := by
        rw [← sub_eq_zero]
        have : (ρ l (ρ l v) - v) - (ρ l (ρ l v - v) - (ρ l v - v)) =
            (ρ l v + ρ l v) - (v + v) := by
          rw [map_sub]; abel
        rw [this, two_nsmul_eq_zero', two_nsmul_eq_zero', sub_zero]
      rw [e]; exact h2
  have hNsq : ∀ n ∈ N, n * n = 1 := by
    rintro _ ⟨⟨l, hlS⟩, hl, rfl⟩
    exact hsq l hl hlS
  have hNp : IsPGroup 2 N := isPGroup_two_of_mul_self_eq_one hNsq
  have hBp : IsPGroup 2 B := by
    have := hA2
    exact ((IsElementaryAbelian.isPGroup 2 A).of_equiv
      (Subgroup.subgroupOfEquivOfLe hAS).symm).map τ
  have hBN : B ≤ Subgroup.normalizer N := by
    refine le_normalizer_of_conj_mem ?_
    rintro _ ⟨t, ht, rfl⟩ _ ⟨s, hs, rfl⟩
    refine ⟨t * s * t⁻¹, ?_, by simp [map_mul]⟩
    exact (Subgroup.mem_normalizer_iff.1 (hAL ht) _).1 hs
  have hcomm : N ≤ ⁅N, B⁆ := by
    have h1 : L ≤ ((⁅N, B⁆).comap τ).map S.subtype := by
      refine hLA.symm.le.trans (Subgroup.commutator_le.2 fun l hl a ha => ?_)
      refine ⟨⁅(⟨l, hLS hl⟩ : S), (⟨a, hAS ha⟩ : S)⁆, ?_, rfl⟩
      show τ _ ∈ ⁅N, B⁆
      rw [map_commutatorElement]
      exact Subgroup.commutator_mem_commutator ⟨_, hl, rfl⟩ ⟨_, ha, rfl⟩
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨t, ht, hts⟩ := h1 hs
    obtain rfl : t = s := Subtype.ext hts
    exact ht
  have hbot : N = ⊥ := eq_bot_of_le_commutator hNp hBp hBN hcomm
  refine Submodule.span_le.2 ?_
  rintro _ ⟨l, hl, v, -, rfl⟩
  have hmem : τ ⟨l, hLS hl⟩ ∈ N := ⟨_, hl, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have := congrArg (fun f : (Module.End (ZMod 2) (V ⧸ V₂))ˣ =>
    (f : Module.End (ZMod 2) (V ⧸ V₂)) (Submodule.Quotient.mk v)) hmem
  simp only [hτk, Units.val_one, Module.End.one_apply] at this
  exact (Submodule.Quotient.eq V₂).1 this

theorem ms1_two_nine [Finite V] {ρ : Representation (ZMod 2) G V} {A L : Subgroup G}
    (hA2 : CFSG.IsElementaryAbelian 2 A) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hLA : ⁅L, A⁆ = L) (a : G) (_haA : a ∈ A)
    (hcent : ∀ l ∈ L, ∀ w ∈ commOn ρ L ⊤, ρ a (ρ l w) = ρ l (ρ a w))
    (hfix : a ∈ cenOn ρ A (commOn ρ A (commOn ρ L ⊤))) :
    ∀ w ∈ commOn ρ L ⊤, ρ a w = w := by
  set V₁ := commOn ρ L ⊤ with hV₁
  have hL1 : commOn ρ L V₁ = V₁ := commOn_commOn_eq hA2 hAL hLA
  obtain ⟨hinvL, hinvA⟩ := invariant_commOn_top (ρ := ρ) hAL
  set Y : Subgroup G := Subgroup.closure {x | ∃ l ∈ L, ∃ a' ∈ A, x = l * a' * l⁻¹} with hY
  have hLS : L ≤ stabSub ρ V₁ := le_stabSub hinvL
  have hAS : A ≤ stabSub ρ V₁ := le_stabSub hinvA
  have hYS : Y ≤ stabSub ρ V₁ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨l, hl, a', ha', rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hLS hl) (hAS ha')) (Subgroup.inv_mem _ (hLS hl))
  have hAY : A ≤ Y := fun a' ha' => Subgroup.subset_closure ⟨1, L.one_mem, a', ha', by simp⟩
  have hLY : L ≤ Y := by
    refine hLA.symm.le.trans (Subgroup.commutator_le.2 fun l hl a' ha' => ?_)
    have h1 : l * a' * l⁻¹ ∈ Y := Subgroup.subset_closure ⟨l, hl, a', ha', rfl⟩
    have h2 : a'⁻¹ ∈ Y := Y.inv_mem (hAY ha')
    simpa [commutatorElement_def, mul_assoc] using Y.mul_mem h1 h2
  have hfixw : ∀ w ∈ commOn ρ A V₁, ρ a w = w := fun w hw => hfix.2 w hw
  have hcomm : ∀ l ∈ L, ∀ w ∈ V₁, ρ a (ρ l w) = ρ l (ρ a w) := hcent
  have key : ∀ x ∈ Y, ∀ u ∈ V₁, ρ a (ρ x u - u) = ρ x u - u := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, a', ha', rfl⟩ := hx
      intro u hu
      have hu' : ρ l⁻¹ u ∈ V₁ := hinvL l⁻¹ (L.inv_mem hl) u hu
      have hw : ρ a' (ρ l⁻¹ u) - ρ l⁻¹ u ∈ commOn ρ A V₁ := sub_mem_commOn ha' hu'
      have e : ρ (l * a' * l⁻¹) u - u = ρ l (ρ a' (ρ l⁻¹ u) - ρ l⁻¹ u) := by
        rw [map_sub, ← Module.End.mul_apply (ρ l) (ρ l⁻¹), ← map_mul, mul_inv_cancel,
          map_one, Module.End.one_apply, map_mul, map_mul, Module.End.mul_apply,
          Module.End.mul_apply]
      have hw1 : ρ a' (ρ l⁻¹ u) - ρ l⁻¹ u ∈ V₁ := V₁.sub_mem (hinvA a' ha' _ hu') hu'
      rw [e, hcomm l hl _ hw1, hfixw _ hw]
    | one => intro u hu; simp
    | mul x y hx hy hx' hy' =>
      intro u hu
      have hyu : ρ y u ∈ V₁ := (hYS hy).1 u hu
      have e : ρ (x * y) u - u = (ρ x (ρ y u) - ρ y u) + (ρ y u - u) := by
        rw [map_mul, Module.End.mul_apply]; abel
      rw [e, map_add, hx' _ hyu, hy' u hu]
    | inv x hx hx' =>
      intro u hu
      have hu' : ρ x⁻¹ u ∈ V₁ := (hYS hx).2 u hu
      have e : ρ x⁻¹ u - u = -(ρ x (ρ x⁻¹ u) - ρ x⁻¹ u) := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        abel
      rw [e, map_neg, hx' _ hu']
  intro w hw
  have hw' : w ∈ commOn ρ L V₁ := hL1.ge hw
  have : commOn ρ L V₁ ≤ LinearMap.ker (ρ a - LinearMap.id) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨l, hl, u, hu, rfl⟩
    have := key l (hLY hl) u hu
    simpa [sub_eq_zero] using this
  have := this hw'
  simpa [sub_eq_zero] using this

end CommOn

end CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
