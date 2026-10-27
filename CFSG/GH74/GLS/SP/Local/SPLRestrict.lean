module

public import CFSG.GH74.GLS.SP.GlueDefs

public section

namespace CFSG.GH74.GLS.SP

open Subgroup CFSG.GH74.BNPair
open scoped Pointwise

variable {X : Type*} [Group X]

theorem conjBy_subgroupOf (G₀ : Subgroup X) (m : G₀) (A : Subgroup X) :
    conjBy m (A.subgroupOf G₀) = (conjBy (m : X) A).subgroupOf G₀ := by
  ext x
  rw [mem_conjBy_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_conjBy_iff]
  rfl

theorem chainProd_subgroupOf (root : ℤ → Subgroup X) (G₀ : Subgroup X) :
    ∀ l : List ℤ, (∀ k ∈ l, root k ≤ G₀) →
      (chainProd (fun k => (root k).subgroupOf G₀) l : Set G₀) =
        G₀.subtype ⁻¹' (chainProd root l)
  | [], _ => by
    ext x
    simp only [chainProd, List.map_nil, List.prod_nil, Set.mem_one, Set.mem_preimage,
      Subgroup.coe_subtype]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact Subtype.ext h
  | k :: l, hl => by
    have ih := chainProd_subgroupOf root G₀ l (fun k' hk' => hl k' (List.mem_cons_of_mem _ hk'))
    have hk : root k ≤ G₀ := hl k List.mem_cons_self
    rw [chainProd_cons, chainProd_cons, ih]
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
    · rintro ⟨a, ha, b, hb, hab⟩
      have hab' : a * b = (x : X) := hab
      have haG : a ∈ G₀ := hk ha
      have hbG : b ∈ G₀ := by
        have : b = a⁻¹ * (x : X) := by rw [← hab']; group
        rw [this]
        exact G₀.mul_mem (G₀.inv_mem haG) x.2
      exact ⟨⟨a, haG⟩, ha, ⟨b, hbG⟩, hb, Subtype.ext hab'⟩

theorem RGD2.restrict {n : ℕ} {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
    {root : ℤ → Subgroup X} (R : RGD2 n H r₁ r₂ U root) (G₀ : Subgroup X) (hH : H ≤ G₀)
    (h₁ : r₁ ∈ G₀) (h₂ : r₂ ∈ G₀) (hU : U ≤ G₀) (hroot : ∀ i, IsRoot n i → root i ≤ G₀) :
    RGD2 n (H.subgroupOf G₀) ⟨r₁, h₁⟩ ⟨r₂, h₂⟩ (U.subgroupOf G₀)
      (fun i => (root i).subgroupOf G₀) where
  three_le := R.three_le
  comm_H a b ha hb := Subtype.ext (R.comm_H a b ha hb)
  nilpotent := by
    have := R.nilpotent
    exact Group.nilpotent_of_surjective (Subgroup.subgroupOfEquivOfLe hU).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hU).symm.surjective
  conj_H₁ h hh := R.conj_H₁ h hh
  conj_H₂ h hh := R.conj_H₂ h hh
  sq₁ := R.sq₁
  sq₂ := R.sq₂
  pow := by
    have := R.pow
    show (((⟨r₁, h₁⟩ * ⟨r₂, h₂⟩ : G₀) ^ n : G₀) : X) ∈ H
    simpa using this
  U_inf_H := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : X) ∈ U ⊓ H := ⟨hx.1, hx.2⟩
    rw [R.U_inf_H] at h1
    exact Subtype.ext (Subgroup.mem_bot.1 h1)
  ne_bot i hi h := by
    apply R.ne_bot i hi
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hroot i hi hx⟩ : G₀) ∈ (root i).subgroupOf G₀ := hx
    rw [h] at hx'
    have := Subgroup.mem_bot.1 hx'
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  invariant i hi h hh x hx := R.invariant i hi h hh x hx
  carrier_eq := by
    have hl : ∀ k ∈ intList 1 n, root k ≤ G₀ := fun k hk =>
      hroot k (isRoot_of_pos_le (mem_intList_iff.1 hk).1 (mem_intList_iff.1 hk).2)
    rw [chainProd_subgroupOf root G₀ _ hl, ← R.carrier_eq]
    rfl
  unique f g hf hg hfg k hk := by
    have hf' : ∀ k ∈ intList 1 n, ((f k : G₀) : X) ∈ root k := fun k hk => hf k hk
    have hg' : ∀ k ∈ intList 1 n, ((g k : G₀) : X) ∈ root k := fun k hk => hg k hk
    have hfg' : ((intList 1 n).map (fun k => ((f k : G₀) : X))).prod =
        ((intList 1 n).map (fun k => ((g k : G₀) : X))).prod := by
      have := congrArg (fun y : G₀ => (y : X)) hfg
      simpa [Subgroup.val_list_prod, List.map_map, Function.comp_def] using this
    exact Subtype.ext (R.unique (fun k => ((f k : G₀) : X)) (fun k => ((g k : G₀) : X)) hf' hg'
      hfg' k hk)
  reverse_eq i j hi hij hj := by
    have hl : ∀ l : List ℤ, (∀ k ∈ l, k ∈ intList i j) → ∀ k ∈ l, root k ≤ G₀ := fun l hl k hk =>
      hroot k (isRoot_of_pos_le (by have := (mem_intList_iff.1 (hl k hk)).1; omega)
        (by have := (mem_intList_iff.1 (hl k hk)).2; omega))
    rw [chainProd_subgroupOf root G₀ _ (hl _ (fun k hk => hk)),
      chainProd_subgroupOf root G₀ _ (hl _ (fun k hk => by simpa using hk)), R.reverse_eq i j hi hij hj]
  subgroup i j hi hij hj := by
    obtain ⟨V, hV, hVU, hl, hr⟩ := R.subgroup i j hi hij hj
    refine ⟨V.subgroupOf G₀, ?_, Subgroup.subgroupOf_mono G₀ hVU, ?_, ?_⟩
    · have hl' : ∀ k ∈ intList i j, root k ≤ G₀ := fun k hk =>
        hroot k (isRoot_of_pos_le (by have := (mem_intList_iff.1 hk).1; omega)
          (by have := (mem_intList_iff.1 hk).2; omega))
      rw [chainProd_subgroupOf root G₀ _ hl', ← hV]
      rfl
    · intro hi1 x hx v hv
      exact hl hi1 x hx v hv
    · intro hj1 x hx v hv
      exact hr hj1 x hx v hv
  act₁ := by
    obtain ⟨a1, a2, a3⟩ := R.act₁
    have e : (⟨r₁, h₁⟩ : G₀)⁻¹ = ⟨r₁⁻¹, G₀.inv_mem h₁⟩ := rfl
    refine ⟨?_, ?_, fun i h1 h2 => ?_⟩
    · rw [conjBy_subgroupOf, e]
      exact congrArg (fun A => A.subgroupOf G₀) a1
    · rw [conjBy_subgroupOf, e]
      exact congrArg (fun A => A.subgroupOf G₀) a2
    · obtain ⟨b1, b2⟩ := a3 i h1 h2
      refine ⟨?_, ?_⟩
      · rw [conjBy_subgroupOf, e]
        exact congrArg (fun A => A.subgroupOf G₀) b1
      · rw [conjBy_subgroupOf, e]
        exact congrArg (fun A => A.subgroupOf G₀) b2
  act₂ := by
    obtain ⟨a1, a2, a3⟩ := R.act₂
    have e : (⟨r₂, h₂⟩ : G₀)⁻¹ = ⟨r₂⁻¹, G₀.inv_mem h₂⟩ := rfl
    refine ⟨?_, ?_, fun i h1 h2 => ?_⟩
    · rw [conjBy_subgroupOf, e]
      exact congrArg (fun A => A.subgroupOf G₀) a1
    · rw [conjBy_subgroupOf, e]
      exact congrArg (fun A => A.subgroupOf G₀) a2
    · obtain ⟨b1, b2⟩ := a3 i h1 h2
      refine ⟨?_, ?_⟩
      · rw [conjBy_subgroupOf, e]
        exact congrArg (fun A => A.subgroupOf G₀) b1
      · rw [conjBy_subgroupOf, e]
        exact congrArg (fun A => A.subgroupOf G₀) b2
  meet_one x hx hn := by
    have hx1 : (x : X) ∈ H ⊔ U := by
      have : H.subgroupOf G₀ ⊔ U.subgroupOf G₀ ≤ (H ⊔ U).subgroupOf G₀ :=
        sup_le (Subgroup.subgroupOf_mono G₀ le_sup_left) (Subgroup.subgroupOf_mono G₀ le_sup_right)
      exact this hx
    have hx2 : (x : X) ∈ negGen n root := by
      have : negGen n (fun i => (root i).subgroupOf G₀) ≤ (negGen n root).subgroupOf G₀ := by
        refine iSup₂_le fun k hk y hy => ?_
        have hy' : (y : X) ∈ root (-k) := hy
        exact mem_negGen_of_mem hk.1 hk.2 hy'
      exact this hn
    exact Subtype.ext (R.meet_one _ hx1 hx2)
  rank₁ y hy hy1 := by
    have hn := R.three_le
    have hy' : (y : X) ∈ root (-1) := hy
    have hne : (y : X) ≠ 1 := fun h => hy1 (Subtype.ext h)
    obtain ⟨u, hu, b, hb, hub⟩ := Set.mem_mul.1 (R.rank₁ _ hy' hne)
    obtain ⟨u2, hu2, r, hr, hu2r⟩ := Set.mem_mul.1 hu
    obtain ⟨a, ha, h, hh, hah⟩ := Set.mem_mul.1 hu2
    have hr' : r = r₁ := Set.mem_singleton_iff.1 hr
    have ha1 : a ∈ G₀ := hroot 1 ⟨by omega, by omega⟩ ha
    have hhG : h ∈ G₀ := hH hh
    have hb1 : b ∈ G₀ := hroot 1 ⟨by omega, by omega⟩ hb
    have e : y = ⟨a, ha1⟩ * ⟨h, hhG⟩ * ⟨r₁, h₁⟩ * ⟨b, hb1⟩ := by
      apply Subtype.ext
      have h1 : a * h * r * b = (y : X) := by
        rw [← hub, ← hu2r, ← hah]
      rw [hr'] at h1
      exact h1.symm
    rw [e]
    exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul ha hh) (Set.mem_singleton _)) hb
  rank₂ y hy hy1 := by
    have hn := R.three_le
    have hy' : (y : X) ∈ root (-(n : ℤ)) := hy
    have hne : (y : X) ≠ 1 := fun h => hy1 (Subtype.ext h)
    obtain ⟨u, hu, b, hb, hub⟩ := Set.mem_mul.1 (R.rank₂ _ hy' hne)
    obtain ⟨u2, hu2, r, hr, hu2r⟩ := Set.mem_mul.1 hu
    obtain ⟨a, ha, h, hh, hah⟩ := Set.mem_mul.1 hu2
    have hr' : r = r₂ := Set.mem_singleton_iff.1 hr
    have ha1 : a ∈ G₀ := hroot n ⟨by omega, by omega⟩ ha
    have hhG : h ∈ G₀ := hH hh
    have hb1 : b ∈ G₀ := hroot n ⟨by omega, by omega⟩ hb
    have e : y = ⟨a, ha1⟩ * ⟨h, hhG⟩ * ⟨r₂, h₂⟩ * ⟨b, hb1⟩ := by
      apply Subtype.ext
      have h1 : a * h * r * b = (y : X) := by
        rw [← hub, ← hu2r, ← hah]
      rw [hr'] at h1
      exact h1.symm
    rw [e]
    exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul ha hh) (Set.mem_singleton _)) hb

end CFSG.GH74.GLS.SP
