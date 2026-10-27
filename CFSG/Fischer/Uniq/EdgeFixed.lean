module

public import CFSG.Fischer.Uniq.F23Hyperoval
public import CFSG.Fischer.Uniq.RigidTransfer
public import CFSG.Fischer.Uniq.F23Local

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X Y Z : Type} [Group X] [Group Y] [Group Z] {E : Set X} {F : Set Y} {G : Set Z}

@[expose] def conjStar (hE : Pair X E) (g d : X) :
    LocalClass E d ≃ LocalClass E (g * d * g⁻¹) where
  toFun f := ⟨g * f * g⁻¹, (Pair.conj_mem_localClass_iff hE g).2 f.2⟩
  invFun f := ⟨g⁻¹ * f * g, by
    have := (Pair.conj_mem_localClass_iff hE g⁻¹ (e := g * d * g⁻¹) (f := (f : X))).2 f.2
    rwa [show g⁻¹ * (g * d * g⁻¹) * g⁻¹⁻¹ = d by group, inv_inv] at this⟩
  left_inv f := Subtype.ext (by show g⁻¹ * (g * (f : X) * g⁻¹) * g = f; group)
  right_inv f := Subtype.ext (by show g * (g⁻¹ * (f : X) * g) * g⁻¹ = f; group)

theorem conjStar_symm_val (hE : Pair X E) (g d : X) (f : LocalClass E (g * d * g⁻¹)) :
    ((conjStar hE g d).symm f : X) = g⁻¹ * f * g := rfl

@[expose] noncomputable def LocalPoints.conj {P : Type} {M : LocalModel P} (hE : Pair X E)
    {d : X} (L : LocalPoints M E d) (g : X) : LocalPoints M E (g * d * g⁻¹) where
  χ := (conjStar hE g d).symm.trans L.χ
  comm f f' := by
    rw [Equiv.trans_apply, Equiv.trans_apply, ← L.comm, conjStar_symm_val, conjStar_symm_val,
      show g⁻¹ * (f : X) * g * (g⁻¹ * f' * g) = g⁻¹ * (f * f') * g by group,
      show g⁻¹ * (f' : X) * g * (g⁻¹ * f * g) = g⁻¹ * (f' * f) * g by group]
    exact ⟨fun h => by rw [h], fun h => mul_left_cancel (mul_right_cancel h)⟩
  tau f f' h := by
    have h' := LocalPoints.mul_mul_mem_localClass hE ((conjStar hE g d).symm f)
      ((conjStar hE g d).symm f')
    rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, ← L.tau _ _ h']
    congr 1
    apply Subtype.ext
    show g⁻¹ * ((f : X) * f' * f) * g = g⁻¹ * f * g * (g⁻¹ * f' * g) * (g⁻¹ * f * g)
    group

theorem nonempty_localPoints_of_mem {P : Type} {M : LocalModel P} (hE : Pair X E) {d : X}
    (hd : d ∈ E) (L : LocalPoints M E d) : ∀ x ∈ E, Nonempty (LocalPoints M E x) := by
  intro x hx
  obtain ⟨g, rfl⟩ := isConj_iff.1 (Pair.isConj hE hd hx)
  exact ⟨L.conj hE g⟩

theorem exists_fixed_of_edgeLocal (hE : Pair X E) (hG : Pair Z G)
    (hNFP : HasFixedPointProperty hG)
    (hloc : ∀ a b : E, (a : X) ≠ b → (a : X) * b = b * a →
      ∃ ψ : ↥(LocalClass E a ∩ LocalClass E b) ≃ G,
        (∀ x y : ↥(LocalClass E a ∩ LocalClass E b),
          (x : X) * y = y * x ↔ (ψ x : Z) * ψ y = ψ y * ψ x) ∧
        ∀ x y : ↥(LocalClass E a ∩ LocalClass E b),
          ∃ h : (x : X) * y * x ∈ LocalClass E a ∩ LocalClass E b,
            (ψ ⟨_, h⟩ : Z) = ψ x * ψ y * ψ x)
    {σ : Equiv.Perm E} (hσ : σ ∈ tauGroup hE) (hσ2 : ∀ x, σ (σ x) = x) : ∃ x, σ x = x := by
  obtain ⟨e₀, he₀⟩ := hE.2.1
  have he : e₀ ∈ E := by rw [he₀]; exact IsConj.refl e₀
  set a : E := ⟨e₀, he⟩
  set b := σ a with hbdef
  by_cases hab : b = a
  · exact ⟨a, hab⟩
  have hab' : (a : X) ≠ b := fun h => hab (Subtype.ext h).symm
  have hσb : σ b = a := hσ2 a
  by_cases hc : (a : X) * b = b * a
  ·
    have hmemW : ∀ w : ↥(LocalClass E a ∩ LocalClass E b),
        ((σ ⟨w, w.2.1.1⟩ : E) : X) ∈ LocalClass E a ∩ LocalClass E b := by
      intro w
      have h1 := (tauGroup_mem_localClass_iff hE hσ ⟨w, w.2.1.1⟩ a).1 w.2.1
      have h2 := (tauGroup_mem_localClass_iff hE hσ ⟨w, w.2.1.1⟩ b).1 w.2.2
      rw [hσb] at h2
      exact ⟨h2, h1⟩
    obtain ⟨ψ, hψc, hψt⟩ := hloc a b hab' hc
    let σW : Equiv.Perm ↥(LocalClass E a ∩ LocalClass E b) :=
      { toFun := fun w => ⟨_, hmemW w⟩
        invFun := fun w => ⟨_, hmemW w⟩
        left_inv := fun w => Subtype.ext (show ((σ (σ ⟨w, w.2.1.1⟩) : E) : X) = w from
          congrArg Subtype.val (hσ2 ⟨w, w.2.1.1⟩))
        right_inv := fun w => Subtype.ext (show ((σ (σ ⟨w, w.2.1.1⟩) : E) : X) = w from
          congrArg Subtype.val (hσ2 ⟨w, w.2.1.1⟩)) }
    have hσW : ∀ w, ((σW w : ↥(LocalClass E a ∩ LocalClass E b)) : X) =
        ((σ ⟨w, w.2.1.1⟩ : E) : X) := fun _ => rfl
    let g : Equiv.Perm G := ψ.symm.trans (σW.trans ψ)
    have hg : ∀ u, g (ψ u) = ψ (σW u) := fun u => by
      show ψ (σW (ψ.symm (ψ u))) = ψ (σW u)
      rw [Equiv.symm_apply_apply]
    have hinv : ∀ y, g (g y) = y := by
      intro y
      obtain ⟨u, rfl⟩ := ψ.surjective y
      rw [hg, hg]
      congr 1
      exact Subtype.ext (show ((σ (σ ⟨u, u.2.1.1⟩) : E) : X) = u from
        congrArg Subtype.val (hσ2 ⟨u, u.2.1.1⟩))
    have hcomm : ∀ x y : G, (x : Z) * y = y * x ↔ (g x : Z) * g y = g y * g x := by
      intro x y
      obtain ⟨u, rfl⟩ := ψ.surjective x
      obtain ⟨v, rfl⟩ := ψ.surjective y
      rw [hg, hg, ← hψc, ← hψc, hσW, hσW]
      exact tauGroup_commute_iff hE hσ ⟨u, u.2.1.1⟩ ⟨v, v.2.1.1⟩
    have htau : ∀ x y : G, g (tauE hG x y) = tauE hG (g x) (g y) := by
      intro x y
      obtain ⟨u, rfl⟩ := ψ.surjective x
      obtain ⟨v, rfl⟩ := ψ.surjective y
      obtain ⟨huv, e1⟩ := hψt u v
      have e1' : tauE hG (ψ u) (ψ v) = ψ ⟨_, huv⟩ := Subtype.ext e1.symm
      obtain ⟨huv', e2⟩ := hψt (σW u) (σW v)
      have e2' : ψ ⟨_, huv'⟩ = tauE hG (ψ (σW u)) (ψ (σW v)) := Subtype.ext e2
      rw [e1', hg, hg, hg, ← e2']
      congr 1
      apply Subtype.ext
      simp only [hσW]
      exact congrArg Subtype.val (mem_tauGroup.1 hσ ⟨u, u.2.1.1⟩ ⟨v, v.2.1.1⟩)
    obtain ⟨y, hy⟩ := hNFP g hinv hcomm htau
    obtain ⟨u, rfl⟩ := ψ.surjective y
    refine ⟨⟨u, u.2.1.1⟩, ?_⟩
    rw [hg] at hy
    have := congrArg Subtype.val (ψ.injective hy)
    exact Subtype.ext this
  · refine ⟨tauE hE a b, ?_⟩
    rw [mem_tauGroup.1 hσ a b, ← hbdef, hσb]
    apply Subtype.ext
    show (b : X) * a * b = a * b * a
    exact (Pair.mul_mul_eq hE a.2 b.2 hc).symm

theorem edgeLocal_of_localPoints (hE : Pair X E) (hF : Pair Y F) (hG : Pair Z G)
    (hlocE : ∀ a ∈ E, Nonempty (LocalPoints (pairModel hF) E a))
    (hlocF : ∀ y ∈ F, Nonempty (LocalPoints (pairModel hG) F y)) (a b : E)
    (hab : (a : X) ≠ b) (hc : (a : X) * b = b * a) :
    ∃ ψ : ↥(LocalClass E a ∩ LocalClass E b) ≃ G,
      (∀ x y : ↥(LocalClass E a ∩ LocalClass E b),
        (x : X) * y = y * x ↔ (ψ x : Z) * ψ y = ψ y * ψ x) ∧
      ∀ x y : ↥(LocalClass E a ∩ LocalClass E b),
        ∃ h : (x : X) * y * x ∈ LocalClass E a ∩ LocalClass E b,
          (ψ ⟨_, h⟩ : Z) = ψ x * ψ y * ψ x := by
  obtain ⟨L⟩ := hlocE a a.2
  have hb : (b : X) ∈ LocalClass E a := ⟨b.2, hab.symm, hc.symm⟩
  obtain ⟨L'⟩ := hlocF _ (L.χ ⟨b, hb⟩).2
  refine ⟨(L.restrictStar hF ⟨b, hb⟩).trans L'.χ, fun x y => ?_, fun x y => ?_⟩
  · rw [L.restrictStar_comm hF ⟨b, hb⟩ x y, Equiv.trans_apply, Equiv.trans_apply]
    exact L'.comm _ _
  · obtain ⟨hm, e⟩ := L.restrictStar_tau hF hE ⟨b, hb⟩ x y
    refine ⟨hm, ?_⟩
    rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply]
    have h2 := L'.tau (L.restrictStar hF ⟨b, hb⟩ x) (L.restrictStar hF ⟨b, hb⟩ y)
      (LocalPoints.mul_mul_mem_localClass hF _ _)
    have h3 : L.restrictStar hF ⟨b, hb⟩ ⟨_, hm⟩ =
        ⟨_, LocalPoints.mul_mul_mem_localClass hF (L.restrictStar hF ⟨b, hb⟩ x)
          (L.restrictStar hF ⟨b, hb⟩ y)⟩ := Subtype.ext e
    rw [h3]
    exact (congrArg Subtype.val h2).trans (pairModel_tv hG _ _)

theorem exists_fixed_of_localPoints (hE : Pair X E) (hF : Pair Y F) (hG : Pair Z G)
    (hNFP : HasFixedPointProperty hG)
    (hlocE : ∀ a ∈ E, Nonempty (LocalPoints (pairModel hF) E a))
    (hlocF : ∀ y ∈ F, Nonempty (LocalPoints (pairModel hG) F y))
    {σ : Equiv.Perm E} (hσ : σ ∈ tauGroup hE) (hσ2 : ∀ x, σ (σ x) = x) : ∃ x, σ x = x :=
  exists_fixed_of_edgeLocal hE hG hNFP
    (fun a b hab hc => edgeLocal_of_localPoints hE hF hG hlocE hlocF a b hab hc) hσ hσ2

theorem exists_commute_of_involution (hE : Pair X E) (hF : Pair Y F) (hG : Pair Z G)
    (hNFP : HasFixedPointProperty hG)
    (hlocE : ∀ a ∈ E, Nonempty (LocalPoints (pairModel hF) E a))
    (hlocF : ∀ y ∈ F, Nonempty (LocalPoints (pairModel hG) F y)) {t : X} (ht : t * t = 1) :
    ∃ x ∈ E, t * x = x * t := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  obtain ⟨x, hx⟩ := exists_fixed_of_localPoints hE hF hG hNFP hlocE hlocF
    (σ := Pair.conjPerm hE t) (conjPerm_mem_tauGroup hE t) (fun x => by
      apply Subtype.ext
      rw [Pair.conjPerm_apply, Pair.conjPerm_apply, hti]
      calc t * (t * (x : X) * t) * t = (t * t) * x * (t * t) := by group
        _ = x := by rw [ht, one_mul, mul_one])
  refine ⟨x, x.2, ?_⟩
  have h := congrArg Subtype.val hx
  rw [Pair.conjPerm_apply] at h
  calc t * (x : X) = t * x * t⁻¹ * t := by group
    _ = x * t := by rw [h]

end CFSG.Fischer
