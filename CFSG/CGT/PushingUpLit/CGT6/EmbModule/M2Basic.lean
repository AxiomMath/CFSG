module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModDefs

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin

theorem eq_one_of_perfect {G A : Type*} [Group G] [CommGroup A] [Group.IsPerfect G]
    (f : G →* A) (g : G) : f g = 1 := by
  have h : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : Subsingleton f.range := inferInstance
  have h1 : (⟨f g, g, rfl⟩ : f.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h1

abbrev zmodModuleOfSq {V : Type*} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) :
    Module (ZMod 2) (Additive V) :=
  AddCommGroup.zmodModule fun x => by
    have h := hV (Additive.toMul x)
    calc (2 : ℕ) • x = Additive.ofMul (Additive.toMul x ^ 2) := by simp [ofMul_pow]
      _ = 0 := by rw [h]; rfl

theorem exists_hom_ne_one {V : Type*} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
    {v : V} (hv : v ∉ U) :
    ∃ ψ : V →* Multiplicative (ZMod 2), (∀ u ∈ U, ψ u = 1) ∧ ψ v ≠ 1 := by
  have hQ : ∀ q : V ⧸ U, q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x => rw [← QuotientGroup.mk_pow, hV x, QuotientGroup.mk_one]
  let _ : Module (ZMod 2) (Additive (V ⧸ U)) := zmodModuleOfSq hQ
  have hm : (Additive.ofMul (QuotientGroup.mk v : V ⧸ U)) ≠ 0 := by
    intro h
    apply hv
    have h' : (QuotientGroup.mk v : V ⧸ U) = 1 := h
    exact (QuotientGroup.eq_one_iff v).1 h'
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (ZMod 2) (Additive (V ⧸ U)),
      φ (Additive.ofMul (QuotientGroup.mk v : V ⧸ U)) ≠ 0 := by
    by_contra h
    push Not at h
    exact hm ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).1 h)
  refine ⟨{ toFun := fun x => Multiplicative.ofAdd (φ (Additive.ofMul (QuotientGroup.mk x)))
            map_one' := by simp
            map_mul' := fun x y => by
              simp only [QuotientGroup.mk_mul, ofMul_mul, map_add, ofAdd_add] }, ?_, ?_⟩
  · intro u hu
    show Multiplicative.ofAdd (φ (Additive.ofMul (QuotientGroup.mk u))) = 1
    have : (QuotientGroup.mk u : V ⧸ U) = 1 := (QuotientGroup.eq_one_iff u).2 hu
    rw [this]
    simp
  · intro h
    apply hφ
    exact Multiplicative.ofAdd.injective h

theorem exists_hom_section {U N : Type*} [CommGroup U] [CommGroup N] (hU : ∀ u : U, u ^ 2 = 1)
    (hN : ∀ x : N, x ^ 2 = 1) (β : U →* N) (hβ : Function.Surjective β) :
    ∃ s : N →* U, ∀ x, β (s x) = x := by
  let _ : Module (ZMod 2) (Additive U) := zmodModuleOfSq hU
  let _ : Module (ZMod 2) (Additive N) := zmodModuleOfSq hN
  let f : Additive U →ₗ[ZMod 2] Additive N :=
    AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive β)
  have hf : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨u, hu⟩ := hβ (Additive.toMul y)
    exact ⟨Additive.ofMul u, congrArg Additive.ofMul hu⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective f hf
  refine ⟨{ toFun := fun x => Additive.toMul (g (Additive.ofMul x))
            map_one' := by simp
            map_mul' := fun x y => by simp }, fun x => ?_⟩
  have h := LinearMap.congr_fun hg (Additive.ofMul x)
  exact congrArg Additive.toMul h

theorem fixV_le_commV {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1)
    {G : Subgroup (MulAut V)}
    (hind : ∀ A B : Subgroup V, GInv G A → GInv G B → A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥)
    (hne : commV G ≠ ⊥) : fixV G ≤ commV G := by
  intro v hv
  by_contra hvU
  obtain ⟨ψ, hψU, hψv⟩ := exists_hom_ne_one hV (commV G) hvU
  have hψ : ∀ g ∈ G, ∀ w, ψ (g w) = ψ w := by
    intro g hg w
    have h1 : g w = (g w * w⁻¹) * w := by group
    rw [h1, map_mul, hψU _ (Subgroup.subset_closure ⟨g, hg, w, rfl⟩), one_mul]
  have hz : ∀ a ∈ Subgroup.zpowers v, a = 1 ∨ a = v := by
    rintro _ ⟨k, rfl⟩
    show v ^ k = 1 ∨ v ^ k = v
    have h2 : v ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, hV]
    have e : v ^ k = v ^ (k % 2) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
    rw [e]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h] <;> simp
  have hA : GInv G (Subgroup.zpowers v) := by
    intro g hg a ha
    rcases hz a ha with rfl | rfl
    · rw [map_one]
      exact Subgroup.one_mem _
    · rw [mem_fixV.1 hv g hg]
      exact Subgroup.mem_zpowers _
  have hB : GInv G ψ.ker := by
    intro g hg b hb
    rw [MonoidHom.mem_ker] at hb ⊢
    rw [hψ g hg, hb]
  have hAB : Subgroup.zpowers v ⊓ ψ.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨ha, hb⟩
    rcases hz a ha with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd (MonoidHom.mem_ker.1 hb) hψv
  have hsup : Subgroup.zpowers v ⊔ ψ.ker = ⊤ := by
    rw [eq_top_iff]
    intro w _
    by_cases hw : ψ w = 1
    · exact Subgroup.mem_sup_right hw
    · have h2 : ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a = b := by decide
      have h3 : w * v⁻¹ ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h2 _ _ hw hψv]
        exact mul_inv_cancel _
      have h4 : w = v * (w * v⁻¹) := by rw [mul_comm w v⁻¹, mul_inv_cancel_left]
      rw [h4]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers v))
        (Subgroup.mem_sup_right h3)
  rcases hind _ _ hA hB hAB hsup with h | h
  · apply hvU
    have : v ∈ Subgroup.zpowers v := Subgroup.mem_zpowers v
    rw [h, Subgroup.mem_bot] at this
    rw [this]
    exact Subgroup.one_mem _
  · apply hne
    rw [eq_bot_iff]
    intro u hu
    have := hψU u hu
    rw [← MonoidHom.mem_ker] at this
    rwa [h] at this

@[expose] def zmod2Dual {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (f : M →+ ZMod 2) :
    Module.Dual (ZMod 2) M where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hc c with rfl | rfl <;> simp

theorem zmod2Dual_apply {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (f : M →+ ZMod 2)
    (x : M) : zmod2Dual f x = f x := rfl

theorem card_hom_zmod2 {C : Type*} [CommGroup C] [Finite C] (hC : ∀ c : C, c ^ 2 = 1) :
    Nat.card (Additive C →+ ZMod 2) = Nat.card C := by
  let _ : Module (ZMod 2) (Additive C) := zmodModuleOfSq hC
  have : Fintype (Additive C) := Fintype.ofFinite _
  let b := Module.Free.chooseBasis (ZMod 2) (Additive C)
  have h1 : Nat.card (Additive C) = Nat.card (Module.Free.ChooseBasisIndex (ZMod 2) (Additive C) →
      ZMod 2) := Nat.card_congr b.equivFun.toEquiv
  have h2 : Nat.card (Additive C →+ ZMod 2) =
      Nat.card (Module.Free.ChooseBasisIndex (ZMod 2) (Additive C) → ZMod 2) :=
    Nat.card_congr
      { toFun := fun f i => f (b i)
        invFun := fun g => (b.constr (ZMod 2) g : Additive C →ₗ[ZMod 2] ZMod 2).toAddMonoidHom
        left_inv := fun f => by
          apply AddMonoidHom.ext
          intro x
          have : (zmod2Dual f : Additive C →ₗ[ZMod 2] ZMod 2) =
              b.constr (ZMod 2) (fun i => f (b i)) :=
            b.ext fun i => by simp [zmod2Dual_apply]
          exact (congrArg (fun l : Additive C →ₗ[ZMod 2] ZMod 2 => l x) this).symm.trans
            (zmod2Dual_apply f x)
        right_inv := fun g => by
          funext i
          simp }
  exact h2.trans h1.symm

end CFSG.CGT.PushingUpLit.CGT6
