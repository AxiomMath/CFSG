module

public import CFSG.GH74.GLS.SP.Transfer
public import CFSG.GH74.GLS.SP.GlueDefs

public section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair
open scoped Pointwise

universe u v

variable {X : Type u} {Y : Type v} [Group X] [Group Y]

theorem negGen_map (n : ℕ) (root : ℤ → Subgroup X) (π : X →* Y) :
    negGen n (fun i => (root i).map π) = (negGen n root).map π := by
  unfold negGen
  simp only [Subgroup.map_iSup]

namespace RGD2

variable {n : ℕ} {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X} {root : ℤ → Subgroup X}

theorem map (R : RGD2 n H r₁ r₂ U root) (π : X →* Y) (hker : π.ker ≤ H) (hU : U ⊓ π.ker = ⊥) :
    RGD2 n (H.map π) (π r₁) (π r₂) (U.map π) (fun i => (root i).map π) where
  three_le := R.three_le
  comm_H := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, R.comm_H a ha b hb]
  nilpotent := by
    have := R.nilpotent
    exact Group.nilpotent_of_surjective (π.subgroupMap U) (π.subgroupMap_surjective U)
  conj_H₁ := by
    rintro _ ⟨h, hh, rfl⟩
    exact ⟨r₁ * h * r₁⁻¹, R.conj_H₁ h hh, by simp [map_mul, map_inv]⟩
  conj_H₂ := by
    rintro _ ⟨h, hh, rfl⟩
    exact ⟨r₂ * h * r₂⁻¹, R.conj_H₂ h hh, by simp [map_mul, map_inv]⟩
  sq₁ := ⟨r₁ * r₁, R.sq₁, by simp [map_mul]⟩
  sq₂ := ⟨r₂ * r₂, R.sq₂, by simp [map_mul]⟩
  pow := ⟨(r₁ * r₂) ^ n, R.pow, by simp [map_pow, map_mul]⟩
  U_inf_H := by
    rw [eq_bot_iff]
    rintro x ⟨⟨u, hu, rfl⟩, ⟨h, hh, hhu⟩⟩
    have hk : h⁻¹ * u ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hhu, inv_mul_cancel]
    have hu' : u ∈ H := by
      have : u = h * (h⁻¹ * u) := by group
      rw [this]
      exact H.mul_mem hh (hker hk)
    have h2 : u ∈ U ⊓ H := ⟨hu, hu'⟩
    rw [R.U_inf_H] at h2
    rw [Subgroup.mem_bot.1 h2, map_one]
    exact Subgroup.one_mem _
  ne_bot := by
    intro i hi hbot
    apply R.ne_bot i hi
    rw [eq_bot_iff]
    intro x hx
    have hx1 : π x = 1 := by
      have h1 : π x ∈ (root i).map π := ⟨x, hx, rfl⟩
      have h2 : (root i).map π = ⊥ := hbot
      rw [h2] at h1
      exact Subgroup.mem_bot.1 h1
    have hxk : x ∈ π.ker := hx1
    have hxH : x ∈ H := hker hxk
    have hi2 := hi.2
    rcases lt_or_gt_of_ne hi.1 with hneg | hpos
    · have hxneg : x ∈ negGen n root :=
        mem_negGen_of_mem (k := -i) (by omega) (by omega) (by rwa [neg_neg])
      exact Subgroup.mem_bot.2 (R.meet_one x ((le_sup_left : H ≤ H ⊔ U) hxH) hxneg)
    · have hxU : x ∈ U := R.root_le_U (by omega) (by omega) hx
      have h3 : x ∈ U ⊓ π.ker := ⟨hxU, hxk⟩
      rw [hU] at h3
      exact h3
  invariant := by
    intro i hi h' hh' x' hx'
    obtain ⟨h, hh, rfl⟩ := hh'
    obtain ⟨x, hx, rfl⟩ := hx'
    exact ⟨h * x * h⁻¹, R.invariant i hi h hh x hx, by simp [map_mul, map_inv]⟩
  carrier_eq := by
    rw [Subgroup.coe_map, R.carrier_eq, image_chainProd]
  unique := by
    intro f g hf hg hfg k hk
    have hmemU : ∀ f : ℤ → X, (∀ k ∈ intList 1 n, f k ∈ root k) →
        ((intList 1 n).map f).prod ∈ U := by
      intro f hf
      have := list_prod_mem_chainProd root f (intList 1 n) hf
      rw [← R.carrier_eq] at this
      exact this
    have hf' : ∀ k ∈ intList 1 n, ∃ a ∈ root k, π a = f k := fun k hk => hf k hk
    have hg' : ∀ k ∈ intList 1 n, ∃ a ∈ root k, π a = g k := fun k hk => hg k hk
    choose! f₀ hf₀ hf₀π using hf'
    choose! g₀ hg₀ hg₀π using hg'
    have hπf : π (((intList 1 n).map f₀).prod) = ((intList 1 n).map f).prod := by
      rw [map_list_prod, List.map_map]
      congr 1
      exact List.map_congr_left fun k hk => hf₀π k hk
    have hπg : π (((intList 1 n).map g₀).prod) = ((intList 1 n).map g).prod := by
      rw [map_list_prod, List.map_map]
      congr 1
      exact List.map_congr_left fun k hk => hg₀π k hk
    have hker1 : (((intList 1 n).map f₀).prod)⁻¹ * ((intList 1 n).map g₀).prod ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπf, hπg, hfg, inv_mul_cancel]
    have hU1 : (((intList 1 n).map f₀).prod)⁻¹ * ((intList 1 n).map g₀).prod ∈ U :=
      U.mul_mem (U.inv_mem (hmemU f₀ hf₀)) (hmemU g₀ hg₀)
    have h0 : (((intList 1 n).map f₀).prod)⁻¹ * ((intList 1 n).map g₀).prod = 1 := by
      have h5 : (((intList 1 n).map f₀).prod)⁻¹ * ((intList 1 n).map g₀).prod ∈ U ⊓ π.ker :=
        Subgroup.mem_inf.2 ⟨hU1, hker1⟩
      rw [hU] at h5
      exact Subgroup.mem_bot.1 h5
    have heq : ((intList 1 n).map f₀).prod = ((intList 1 n).map g₀).prod :=
      inv_mul_eq_one.1 h0
    have h6 := R.unique f₀ g₀ hf₀ hg₀ heq k hk
    rw [← hf₀π k hk, ← hg₀π k hk, h6]
  reverse_eq := by
    intro i j h1 h2 h3
    rw [← image_chainProd, ← image_chainProd, R.reverse_eq i j h1 h2 h3]
  subgroup := by
    intro i j h1 h2 h3
    obtain ⟨V, hV, hVU, hl, hr⟩ := R.subgroup i j h1 h2 h3
    refine ⟨V.map π, ?_, Subgroup.map_mono hVU, ?_, ?_⟩
    · rw [Subgroup.coe_map, hV, image_chainProd]
    · intro hi x' hx' v' hv'
      obtain ⟨x, hx, rfl⟩ := hx'
      obtain ⟨v, hv, rfl⟩ := hv'
      exact ⟨x * v * x⁻¹, hl hi x hx v hv, by simp [map_mul, map_inv]⟩
    · intro hj x' hx' v' hv'
      obtain ⟨x, hx, rfl⟩ := hx'
      obtain ⟨v, hv, rfl⟩ := hv'
      exact ⟨x * v * x⁻¹, hr hj x hx v hv, by simp [map_mul, map_inv]⟩
  act₁ := by
    obtain ⟨a1, a2, a3⟩ := R.act₁
    have key : ∀ i j : ℤ, conjBy r₁⁻¹ (root i) = root j →
        conjBy (π r₁)⁻¹ ((root i).map π) = (root j).map π := by
      intro i j h
      rw [← map_inv, conjBy_map, h]
    refine ⟨key _ _ a1, key _ _ a2, fun i h2 hin => ?_⟩
    obtain ⟨b1, b2⟩ := a3 i h2 hin
    exact ⟨key _ _ b1, key _ _ b2⟩
  act₂ := by
    obtain ⟨a1, a2, a3⟩ := R.act₂
    have key : ∀ i j : ℤ, conjBy r₂⁻¹ (root i) = root j →
        conjBy (π r₂)⁻¹ ((root i).map π) = (root j).map π := by
      intro i j h
      rw [← map_inv, conjBy_map, h]
    refine ⟨key _ _ a1, key _ _ a2, fun i h2 hin => ?_⟩
    obtain ⟨b1, b2⟩ := a3 i h2 hin
    exact ⟨key _ _ b1, key _ _ b2⟩
  meet_one := by
    intro x' hx' hxn'
    rw [← Subgroup.map_sup] at hx'
    rw [negGen_map] at hxn'
    obtain ⟨b, hb, rfl⟩ := hx'
    obtain ⟨c, hc, hcb⟩ := hxn'
    have hk : b⁻¹ * c ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcb, inv_mul_cancel]
    have hcB : c ∈ H ⊔ U := by
      have : c = b * (b⁻¹ * c) := by group
      rw [this]
      exact (H ⊔ U).mul_mem hb ((le_sup_left : H ≤ H ⊔ U) (hker hk))
    have h7 := R.meet_one c hcB hc
    rw [← hcb, h7, map_one]
  rank₁ := by
    intro y' hy' hy1
    obtain ⟨y, hy, rfl⟩ := hy'
    have hy1' : y ≠ 1 := fun h => hy1 (by rw [h, map_one])
    obtain ⟨a, ha, v, hv, rfl⟩ := Set.mem_mul.1 (R.rank₁ y hy hy1')
    obtain ⟨b, hb, r, hr, rfl⟩ := Set.mem_mul.1 ha
    obtain ⟨u, hu, c, hc, rfl⟩ := Set.mem_mul.1 hb
    rw [Set.mem_singleton_iff] at hr
    subst hr
    exact Set.mem_mul.2 ⟨π u * π c * π r, Set.mem_mul.2 ⟨π u * π c,
      Set.mem_mul.2 ⟨π u, Subgroup.mem_map_of_mem π hu, π c, Subgroup.mem_map_of_mem π hc, rfl⟩,
      π r, rfl, rfl⟩, π v, Subgroup.mem_map_of_mem π hv, by simp [map_mul]⟩
  rank₂ := by
    intro y' hy' hy1
    obtain ⟨y, hy, rfl⟩ := hy'
    have hy1' : y ≠ 1 := fun h => hy1 (by rw [h, map_one])
    obtain ⟨a, ha, v, hv, rfl⟩ := Set.mem_mul.1 (R.rank₂ y hy hy1')
    obtain ⟨b, hb, r, hr, rfl⟩ := Set.mem_mul.1 ha
    obtain ⟨u, hu, c, hc, rfl⟩ := Set.mem_mul.1 hb
    rw [Set.mem_singleton_iff] at hr
    subst hr
    exact Set.mem_mul.2 ⟨π u * π c * π r, Set.mem_mul.2 ⟨π u * π c,
      Set.mem_mul.2 ⟨π u, Subgroup.mem_map_of_mem π hu, π c, Subgroup.mem_map_of_mem π hc, rfl⟩,
      π r, rfl, rfl⟩, π v, Subgroup.mem_map_of_mem π hv, by simp [map_mul]⟩

theorem N_map (R : RGD2 n H r₁ r₂ U root) (π : X →* Y) (hker : π.ker ≤ H)
    (hU : U ⊓ π.ker = ⊥) : (R.map π hker hU).N = R.N.map π := by
  unfold N
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  simp [Set.image_insert_eq]

theorem map_gen (R : RGD2 n H r₁ r₂ U root) (π : X →* Y) (hπ : Function.Surjective π)
    (hker : π.ker ≤ H) (hU : U ⊓ π.ker = ⊥) (hgen : (H ⊔ U) ⊔ R.N = ⊤) :
    (H.map π ⊔ U.map π) ⊔ (R.map π hker hU).N = ⊤ := by
  rw [N_map R π hker hU, ← Subgroup.map_sup, ← Subgroup.map_sup, hgen, Subgroup.map_top_of_surjective π hπ]

end RGD2

end CFSG.GH74.GLS.SP
