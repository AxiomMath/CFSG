module

import CFSG.Holt.H78.Sec4KnownKV
public import CFSG.Holt.H78.Sec4Prop49S4

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open Equiv
open scoped Pointwise

section Perm7

variable {Ψ : Type*} [Fintype Ψ] [DecidableEq Ψ]

theorem exists_mem_longInvAt_perm_sq {v : Perm Ψ} (h7 : Fintype.card Ψ = 7) (hv : v * v = 1)
    {p a b : Ψ} (hpa : p ≠ a) (hpb : p ≠ b) (hab : a ≠ b)
    (hfix : ∀ z, v z = z ↔ z = p ∨ z = a ∨ z = b) :
    ∃ y ∈ longInvAt (Perm Ψ) Ψ p, ((y * v) ^ 2) ^ 2 = 1 ∧ ((y * v) ^ 2) a = b := by
  have hvv : ∀ z, v (v z) = z := fun z => by rw [← Perm.mul_apply, hv, Perm.one_apply]
  have hvp : v p = p := (hfix p).mpr (Or.inl rfl)
  have hva : v a = a := (hfix a).mpr (Or.inr (Or.inl rfl))
  have hvb : v b = b := (hfix b).mpr (Or.inr (Or.inr rfl))
  have hmov : ∀ z, z ≠ p → z ≠ a → z ≠ b → v z ≠ z := fun z h1 h2 h3 h => by
    rcases (hfix z).mp h with h | h | h
    exacts [h1 h, h2 h, h3 h]
  have hF : ({p, a, b} : Finset Ψ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hpa, hpb]), Finset.card_pair hab]
  obtain ⟨x, hx⟩ : (Finset.univ \ ({p, a, b} : Finset Ψ)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      h7, hF]
    norm_num
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    not_or, true_and] at hx
  obtain ⟨hxp, hxa, hxb⟩ := hx
  obtain ⟨y₀, hvx⟩ : ∃ y₀, v x = y₀ := ⟨_, rfl⟩
  have hvy₀ : v y₀ = x := by rw [← hvx, hvv]
  have hxy₀ : x ≠ y₀ := fun h => hmov x hxp hxa hxb (by rw [hvx, h])
  have hy₀F : y₀ ≠ p ∧ y₀ ≠ a ∧ y₀ ≠ b := by
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      exact hxy₀ (by rw [← hvy₀, (hfix y₀).mpr (by simp [h])])
  obtain ⟨hy₀p, hy₀a, hy₀b⟩ := hy₀F
  have hF5 : ({p, a, b, x, y₀} : Finset Ψ).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hpa, hpb, Ne.symm hxp, Ne.symm hy₀p]),
      Finset.card_insert_of_notMem (by simp [hab, Ne.symm hxa, Ne.symm hy₀a]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hxb, Ne.symm hy₀b]),
      Finset.card_pair hxy₀]
  obtain ⟨u, hu⟩ : (Finset.univ \ ({p, a, b, x, y₀} : Finset Ψ)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      h7, hF5]
    norm_num
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    not_or, true_and] at hu
  obtain ⟨hup, hua, hub, hux, huy₀⟩ := hu
  obtain ⟨u', hvu⟩ : ∃ u', v u = u' := ⟨_, rfl⟩
  have hvu' : v u' = u := by rw [← hvu, hvv]
  have huu' : u ≠ u' := fun h => hmov u hup hua hub (by rw [hvu, h])
  have hu'F : u' ≠ p ∧ u' ≠ a ∧ u' ≠ b := by
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      exact huu' (by rw [← hvu', (hfix u').mpr (by simp [h])])
  obtain ⟨hu'p, hu'a, hu'b⟩ := hu'F
  have hu'x : u' ≠ x := fun h => huy₀ (by rw [← hvu', h, hvx])
  have hu'y₀ : u' ≠ y₀ := fun h => hux (by rw [← hvu', h, hvy₀])
  have hall : ∀ z, z = p ∨ z = a ∨ z = b ∨ z = x ∨ z = y₀ ∨ z = u ∨ z = u' := by
    have hcard : ({p, a, b, x, y₀, u, u'} : Finset Ψ).card = 7 := by
      rw [Finset.card_insert_of_notMem (by simp [hpa, hpb, Ne.symm hxp, Ne.symm hy₀p,
          Ne.symm hup, Ne.symm hu'p]),
        Finset.card_insert_of_notMem (by simp [hab, Ne.symm hxa, Ne.symm hy₀a, Ne.symm hua,
          Ne.symm hu'a]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hxb, Ne.symm hy₀b, Ne.symm hub,
          Ne.symm hu'b]),
        Finset.card_insert_of_notMem (by simp [hxy₀, Ne.symm hux, Ne.symm hu'x]),
        Finset.card_insert_of_notMem (by simp [Ne.symm huy₀, Ne.symm hu'y₀]),
        Finset.card_pair huu']
    have huniv := Finset.eq_univ_of_card _ (hcard.trans h7.symm)
    intro z
    have hz : z ∈ ({p, a, b, x, y₀, u, u'} : Finset Ψ) := huniv ▸ Finset.mem_univ z
    simpa using hz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hap := Ne.symm hpa
  have hbp := Ne.symm hpb
  have hba := Ne.symm hab
  have hpx := Ne.symm hxp
  have hax := Ne.symm hxa
  have hbx := Ne.symm hxb
  have hy₀x := Ne.symm hxy₀
  have hpy₀ := Ne.symm hy₀p
  have hay₀ := Ne.symm hy₀a
  have hby₀ := Ne.symm hy₀b
  have hpu := Ne.symm hup
  have hau := Ne.symm hua
  have hbu := Ne.symm hub
  have hxu := Ne.symm hux
  have hy₀u := Ne.symm huy₀
  have hu'u := huu'.symm
  have hpu' := hu'p.symm
  have hau' := hu'a.symm
  have hbu' := hu'b.symm
  have hxu' := hu'x.symm
  have hy₀u' := hu'y₀.symm
  set y : Perm Ψ := swap a x * swap b y₀ * swap u u' with hy
  have hyp : y p = p := by simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have hya : y a = x := by simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have hyx : y x = a := by simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have hyb : y b = y₀ := by simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have hyy₀ : y y₀ = b := by simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have hyu : y u = u' := by simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have hyu' : y u' = u := by simp [Perm.mul_apply, swap_apply_of_ne_of_ne, *]
  have hyy : y * y = 1 := Equiv.ext fun z => by
    rcases hall z with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Perm.mul_apply, Perm.one_apply, hyp, hya, hyx, hyb, hyy₀, hyu, hyu']
  have hy1 : y ≠ 1 := fun h => hxa (by rw [← hya, h, Perm.one_apply])
  refine ⟨y, ⟨⟨orderOf_eq_prime (by rw [sq]; exact hyy) hy1, p, hyp, fun z hz => ?_⟩, hyp⟩, ?_, ?_⟩
  · change y z = z at hz
    rcases hall z with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact absurd (hz.symm.trans hya) hax
    · exact absurd (hz.symm.trans hyb) hby₀
    · exact absurd (hz.symm.trans hyx) hxa
    · exact absurd (hz.symm.trans hyy₀) hy₀b
    · exact absurd (hz.symm.trans hyu) huu'
    · exact absurd (hz.symm.trans hyu') hu'u
  · refine Equiv.ext fun z => ?_
    rcases hall z with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sq, Perm.mul_apply, Perm.one_apply, hvp, hva, hvb, hvx, hvy₀, hvu, hvu', hyp,
        hya, hyx, hyb, hyy₀, hyu, hyu']
  · simp only [sq, Perm.mul_apply, hva, hya, hvx, hyy₀]

end Perm7

section Blocks

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {hS : Sec4Setting G Ω} {C : P49Config G Ω α v}

theorem P49K3.ncard_coord_eq (K : P49K3 hS C) (p p' : K.D'.Ψc K.j₀) :
    {δ : holtDelta G Ω α C.β | K.D'.coord δ K.j₀ = p}.ncard =
      {δ : holtDelta G Ω α C.β | K.D'.coord δ K.j₀ = p'}.ncard := by
  have := (K.D'.factor K.j₀).isPretransitive
  obtain ⟨⟨g, hg⟩, hgp⟩ := exists_smul_eq (K.D'.M K.j₀) p p'
  obtain ⟨h, -, rfl⟩ := mem_factorImage.mp hg
  change K.D'.ρ K.j₀ h p = p' at hgp
  refine Set.ncard_congr (fun δ _ => (h : twoPointSection G Ω α C.β) • δ) (fun δ hδ => ?_)
    (fun δ δ' _ _ e => smul_left_cancel _ e) (fun δ' hδ' => ⟨(h⁻¹ : jHull _ _) • δ', ?_, ?_⟩)
  · change K.D'.coord ((h : twoPointSection G Ω α C.β) • δ) K.j₀ = p'
    rw [K.D'.coord_smul, show K.D'.coord δ K.j₀ = p from hδ, hgp]
  · change K.D'.coord (((h⁻¹ : jHull _ _) : twoPointSection G Ω α C.β) • δ') K.j₀ = p
    rw [K.D'.coord_smul, map_inv, show K.D'.coord δ' K.j₀ = p' from hδ', ← hgp]
    simp
  · change (h : twoPointSection G Ω α C.β) • ((h⁻¹ : jHull _ _) : twoPointSection G Ω α C.β) •
      δ' = δ'
    rw [smul_smul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, one_smul]

theorem P49K3.mem_fixSet_iff (K : P49K3 hS C) (hι : ∀ j, j = K.j₀) (δ : holtDelta G Ω α C.β) :
    (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ↔
      K.D'.ρ K.j₀ ⟨C.vHat, C.vHat_mem_jHull hS⟩ (K.D'.coord δ K.j₀) = K.D'.coord δ K.j₀ := by
  rw [C.mem_fixSet_iff_rho hS K.D' δ]
  refine ⟨fun h => h K.j₀, fun h j => ?_⟩
  rcases hι j with rfl
  exact h

theorem P49K3.ncard_B (K : P49K3 hS C) (hι : ∀ j, j = K.j₀) (p : K.D'.Ψc K.j₀) :
    {δ : holtDelta G Ω α C.β | (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v)}.ncard =
      3 * {δ : holtDelta G Ω α C.β | K.D'.coord δ K.j₀ = p}.ncard := by
  obtain ⟨p₁, p₂, p₃, h12, h13, h23, hF⟩ := Finset.card_eq_three.mp K.fix_three
  have hmemF : ∀ x : K.D'.Ψc K.j₀, K.D'.ρ K.j₀ ⟨C.vHat, C.vHat_mem_jHull hS⟩ x = x ↔
      x = p₁ ∨ x = p₂ ∨ x = p₃ := fun x => by
    have h := congrArg (fun F : Finset (K.D'.Ψc K.j₀) => x ∈ F) hF
    simpa using h
  have hB : {δ : holtDelta G Ω α C.β | (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v)} =
      {δ | K.D'.coord δ K.j₀ = p₁} ∪ {δ | K.D'.coord δ K.j₀ = p₂} ∪
        {δ | K.D'.coord δ K.j₀ = p₃} := by
    ext δ
    simp only [Set.mem_ofPred_eq, Set.mem_union, K.mem_fixSet_iff hι, hmemF]
    tauto
  have hd : ∀ {x y : K.D'.Ψc K.j₀}, x ≠ y →
      Disjoint {δ : holtDelta G Ω α C.β | K.D'.coord δ K.j₀ = x} {δ | K.D'.coord δ K.j₀ = y} :=
    fun hxy => Set.disjoint_left.mpr fun δ h h' => hxy (h.symm.trans h')
  rw [hB, Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hd h13, hd h23⟩),
    Set.ncard_union_eq (hd h12), K.ncard_coord_eq p₁ p, K.ncard_coord_eq p₂ p,
    K.ncard_coord_eq p₃ p]
  ring

theorem P49Config.ncard_B_eq (C : P49Config G Ω α v) (hS : Sec4Setting G Ω) :
    {δ : holtDelta G Ω α C.β | (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v)}.ncard =
      (holtDelta (C.D.M C.i) (C.D.Ψc C.i) (C.D.coord C.a C.i) (C.D.coord C.b C.i)).ncard := by
  refine Set.ncard_congr (fun δ hδ => C.D.coord ⟨δ, hδ⟩ C.i)
    (fun δ hδ => ((C.mem_holtDelta_iff hS ⟨δ, hδ⟩).mp δ.2).2) (fun δ δ' hδ hδ' e => ?_)
    (fun x hx => ?_)
  · have h1 := ((C.mem_holtDelta_iff hS ⟨δ, hδ⟩).mp δ.2).1
    have h2 := ((C.mem_holtDelta_iff hS ⟨δ', hδ'⟩).mp δ'.2).1
    have h : (⟨δ, hδ⟩ : fixSet Ω (Subgroup.zpowers v)) = ⟨δ', hδ'⟩ :=
      C.coord_injective (funext fun j => by
        rcases eq_or_ne j C.i with rfl | hj
        · exact e
        · rw [h1 j hj, h2 j hj])
    exact Subtype.ext (congrArg (fun y : fixSet Ω (Subgroup.zpowers v) => (y : Ω)) h)
  · obtain ⟨ε, hε⟩ := C.exists_coord_eq_update x
    have hεΔ : (ε : Ω) ∈ holtDelta G Ω α C.β := (C.mem_holtDelta_iff hS ε).mpr
      ⟨fun j hj => by rw [hε, Function.update_of_ne hj], by rw [hε, Function.update_self]; exact hx⟩
    exact ⟨⟨ε, hεΔ⟩, ε.2, by
      show C.D.coord ε C.i = x
      rw [hε, Function.update_self]⟩

end Blocks

section Sigma

theorem HoltData.sq_mem_socPre {K X : Type*} [Group K] [MulAction K X] (D : HoltData K X)
    (x : jHull K X) : ((x ^ 2 : jHull K X) : K) ∈ D.socPre := by
  rcases (Nat.dvd_prime Nat.prime_two).mp D.relIndex_socPre_jHull_dvd_two with h1 | h2
  · have htop : D.socPre.subgroupOf (jHull K X) = ⊤ := Subgroup.index_eq_one.mp h1
    have hx : x ^ 2 ∈ D.socPre.subgroupOf (jHull K X) := htop ▸ Subgroup.mem_top _
    exact hx
  · exact Subgroup.sq_mem_of_index_two h2 x

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {hS : Sec4Setting G Ω} {C : P49Config G Ω α v}

theorem P49K3.exists_sigma (K : P49K3 hS C) (hι : ∀ j, j = K.j₀)
    (hT : Odd (Nat.card (twoPointKernel G Ω α C.β))) :
    ∃ p : K.D'.Ψc K.j₀, K.D'.ρ K.j₀ ⟨C.vHat, C.vHat_mem_jHull hS⟩ p = p ∧
      ∃ σ ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G),
        σ • α = α ∧ σ • C.β = C.β ∧
        (∀ δ : holtDelta G Ω α C.β, K.D'.coord δ K.j₀ = p → σ • (δ : Ω) = δ) ∧
        ∃ δ : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ∧
          σ • (δ : Ω) ≠ δ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 := C.three_le_card_holtDelta hS
  obtain ⟨p₁, p₂, p₃, h12, h13, h23, hF⟩ := Finset.card_eq_three.mp K.fix_three
  set vH : jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    ⟨C.vHat, C.vHat_mem_jHull hS⟩ with hvH
  have hmemF : ∀ x, K.D'.ρ K.j₀ vH x = x ↔ x = p₁ ∨ x = p₂ ∨ x = p₃ := fun x => by
    have h := congrArg (fun F : Finset (K.D'.Ψc K.j₀) => x ∈ F) hF
    simpa using h
  have hvv : vH * vH = 1 := Subtype.ext C.vHat_mul_vHat
  have hvj : K.D'.ρ K.j₀ vH * K.D'.ρ K.j₀ vH = 1 := by rw [← map_mul, hvv, map_one]
  obtain ⟨yb, hyb, hπ4, hπa⟩ := exists_mem_longInvAt_perm_sq K.card_eq hvj h12 h13 h23 hmemF
  obtain ⟨c₃, hc₃, hρ₃⟩ := hS.exists_mem_longInvSwap_rho_eq_of_twoPoint C.ne h3 K.D'
    (Function.update (fun j => K.D'.ρ j K.D'.tHull) K.j₀ yb) fun j => by
      rcases hι j with rfl
      rw [Function.update_self]
      exact ⟨K.D'.mem_range_rho_of_alternating K.alt hyb.1, hyb.1⟩
  set cH := twoPointJHom hS.star α C.β c₃ with hcH
  have hρc : K.D'.ρ K.j₀ cH = yb := by rw [hcH, hρ₃, Function.update_self]
  set gH := cH * vH with hgH
  set g : G := (c₃ : G) * v with hg
  set π := yb * K.D'.ρ K.j₀ vH with hπ
  have hρg : K.D'.ρ K.j₀ gH = π := by rw [hgH, map_mul, hρc]
  have hgΔ : ∀ (n : ℕ) (δ : holtDelta G Ω α C.β),
      g ^ n • (δ : Ω) = ((((gH ^ n : jHull _ _) : twoPointSection G Ω α C.β) • δ :
        holtDelta G Ω α C.β) : Ω) := fun n => by
    induction n with
    | zero => intro δ; simp
    | succ n ih =>
      intro δ
      rw [pow_succ', mul_smul, ih, pow_succ', Subgroup.coe_mul, mul_smul]
      rfl
  have hker : ∀ x : jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β),
      K.D'.ρ K.j₀ x = 1 → (x : twoPointSection G Ω α C.β) ∈
        jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) := fun x hx => by
    have hout : ∃ i, IsOuterFactor (factorImage _ _ (K.D'.L i) (K.D'.ρ i)) :=
      ⟨K.j₀, K.alt, by rw [K.card_eq]⟩
    rw [← K.D'.ker_outer hout]
    exact (K.D'.mem_jOrbitKernel_iff_rho (h := x)).mpr fun i => by
      rcases hι i with rfl
      exact hx
  have hπ4' : π ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hπ4]
  have hg4 : ((gH ^ 4 : jHull _ _) : twoPointSection G Ω α C.β) ∈
      jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    hker _ (by rw [map_pow, hρg, hπ4'])
  set o₁ := orderOf ((gH ^ 4 : jHull _ _) : twoPointSection G Ω α C.β) with ho₁def
  have ho₁ : Odd o₁ := Odd.of_dvd_nat odd_card_jOddCore (Subgroup.orderOf_dvd_natCard _ hg4)
  have hgα : g • α = C.β := by rw [hg, mul_smul, C.v_smul_α, hc₃.2]
  have hgβ : g • C.β = α := by rw [hg, mul_smul, C.v_smul_β, smul_eq_of_mem_longInvSwap hc₃]
  have hg2α : g ^ 2 ∈ stabilizer G α := mem_stabilizer_iff.mpr (by rw [sq, mul_smul, hgα, hgβ])
  have hg2β : g ^ 2 ∈ stabilizer G C.β :=
    mem_stabilizer_iff.mpr (by rw [sq, mul_smul, hgβ, hgα])
  have hk : (g ^ 4) ^ o₁ ∈ twoPointKernel G Ω α C.β := by
    have h4 : (g ^ 4) ^ o₁ = (g ^ 2) ^ (2 * o₁) := by
      rw [← pow_mul, ← pow_mul, show 2 * (2 * o₁) = 4 * o₁ by ring]
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨h4 ▸ pow_mem hg2α _,
      h4 ▸ pow_mem hg2β _⟩, (mem_fixingSubgroup_iff G).mpr fun δ hδ => ?_⟩
    rw [← pow_mul, hgΔ (4 * o₁) ⟨δ, hδ⟩, pow_mul, Subgroup.coe_pow, pow_orderOf_eq_one,
      one_smul]
  have hm₁ : Odd (orderOf (g ^ 4)) := by
    have hdvd : orderOf (g ^ 4) ∣ o₁ * orderOf ((g ^ 4) ^ o₁) :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_mul, pow_orderOf_eq_one])
    exact Odd.of_dvd_nat (ho₁.mul (Odd.of_dvd_nat hT (Subgroup.orderOf_dvd_natCard _ hk))) hdvd
  set m₁ := orderOf (g ^ 4) with hm₁def
  set σ := (g ^ 2) ^ m₁ with hσ
  have hσσ : σ * σ = 1 := by
    rw [hσ, ← pow_two, ← pow_mul, mul_comm, pow_mul, ← pow_mul g 2 2, pow_orderOf_eq_one]
  have hv2 : v * v = 1 := C.v_mul_v
  have hc2 : (c₃ : G) * c₃ = 1 := mul_self_eq_one_of_mem_longInv hc₃.1
  have hvg : v * g * v⁻¹ = g⁻¹ := by
    rw [hg, mul_inv_rev, inv_eq_of_mul_eq_one_right hv2, inv_eq_of_mul_eq_one_right hc2,
      mul_assoc, mul_assoc, hv2, mul_one]
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσσ
  have hvσ : v * σ * v⁻¹ = σ := by
    rw [hσ, ← conj_pow, ← conj_pow, hvg, inv_pow, inv_pow, ← hσ, hσinv]
  have hσC : σ ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    mem_centralizer_zpowers_iff.mpr (by
      calc σ * v = v * σ * v⁻¹ * v := by rw [hvσ]
        _ = v * σ := by group)
  have hσα : σ • α = α := mem_stabilizer_iff.mp (pow_mem hg2α _)
  have hσβ : σ • C.β = C.β := mem_stabilizer_iff.mp (pow_mem hg2β _)
  set σH : jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) := gH ^ (2 * m₁) with hσH
  have hσΔ : ∀ δ : holtDelta G Ω α C.β,
      σ • (δ : Ω) = (((σH : twoPointSection G Ω α C.β) • δ : holtDelta G Ω α C.β) : Ω) :=
    fun δ => by rw [hσ, ← pow_mul, hgΔ]
  obtain ⟨k, hk'⟩ := hm₁
  have hρσ : K.D'.ρ K.j₀ σH = π ^ 2 := by
    rw [hσH, map_pow, hρg, pow_mul, hk', pow_succ, pow_mul, hπ4, one_pow, one_mul]
  have hπp : (π ^ 2) p₁ = p₁ := by
    have h1 : π p₁ = p₁ := by
      rw [hπ, Perm.mul_apply, (hmemF p₁).mpr (Or.inl rfl)]
      exact hyb.2
    rw [sq, Perm.mul_apply, h1, h1]
  have hσH1 : (σH : twoPointSection G Ω α C.β) ≠ 1 := fun h => by
    have h1 : K.D'.ρ K.j₀ σH = 1 := by rw [show σH = 1 from Subtype.ext h, map_one]
    rw [hρσ] at h1
    exact h23 (by rw [← hπa, h1, Perm.one_apply])
  have hσH2 : (σH : twoPointSection G Ω α C.β) ^ 2 = 1 := by
    refine Subtype.ext (Equiv.ext fun δ => Subtype.ext ?_)
    rw [Subgroup.coe_pow, sq, Perm.mul_apply]
    change (((σH : twoPointSection G Ω α C.β) • ((σH : twoPointSection G Ω α C.β) • δ) :
      holtDelta G Ω α C.β) : Ω) = (((1 : Perm (holtDelta G Ω α C.β)) δ : holtDelta G Ω α C.β) : Ω)
    rw [← hσΔ, ← hσΔ, smul_smul, hσσ, one_smul]
    rfl
  have hord : orderOf (σH : twoPointSection G Ω α C.β) = 2 := orderOf_eq_prime hσH2 hσH1
  have hsoc : (σH : twoPointSection G Ω α C.β) ∈ K.D'.socPre := by
    rw [show σH = (gH ^ m₁) ^ 2 by rw [hσH, ← pow_mul, mul_comm]]
    exact K.D'.sq_mem_socPre _
  have hfixp : ∀ δ : holtDelta G Ω α C.β, K.D'.coord δ K.j₀ = p₁ → σ • (δ : Ω) = δ :=
    fun δ hδ => by
      have horb : (σH : twoPointSection G Ω α C.β) • δ ∈
          orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) δ :=
        (K.D'.coord_eq_iff _ _).mp (funext fun i => by
          rcases hι i with rfl
          rw [K.D'.coord_smul, hρσ, hδ, hπp])
      have h := (hS.lemma_2_4_iv_twoPointSection h3 K.D' σH.2 hord horb).1 hsoc δ
        (mem_orbit_self _)
      rw [hσΔ, h]
  obtain ⟨δ₂, hδ₂⟩ := K.D'.exists_coord_apply_eq K.j₀ p₂
  refine ⟨p₁, (hmemF p₁).mpr (Or.inl rfl), σ, hσC, hσα, hσβ, hfixp, δ₂,
    (K.mem_fixSet_iff hι δ₂).mpr (by rw [hδ₂]; exact (hmemF p₂).mpr (Or.inr (Or.inl rfl))),
    fun h => ?_⟩
  have h1 : (σH : twoPointSection G Ω α C.β) • δ₂ = δ₂ := Subtype.ext ((hσΔ δ₂).symm.trans h)
  have hc := congrArg (fun ε => K.D'.coord ε K.j₀) h1
  rw [K.D'.coord_smul, hρσ, hδ₂, hπa] at hc
  exact h23 hc.symm

theorem P49K3.ncard_coord_le_one_of_odd (K : P49K3 hS C) (hι : ∀ j, j = K.j₀)
    (hSEf : SEFieldFixBound) (hT : Odd (Nat.card (twoPointKernel G Ω α C.β)))
    (p₀ : K.D'.Ψc K.j₀) :
    {δ : holtDelta G Ω α C.β | K.D'.coord δ K.j₀ = p₀}.ncard ≤ 1 := by
  classical
  obtain ⟨p, hp, σ, hσC, hσα, hσβ, hfix, δ₂, hδ₂F, hδ₂⟩ := K.exists_sigma hι hT
  rw [K.ncard_coord_eq p₀ p]
  set m := {δ : holtDelta G Ω α C.β | K.D'.coord δ K.j₀ = p}.ncard with hm
  set σv := centralizerImageElt (Ω := Ω) hσC with hσv
  have hσa : σv • C.a = C.a := Subtype.ext (by
    change σ • (C.a : Ω) = C.a
    rw [C.coe_a, hσα])
  have hσb : σv • C.b = C.b := Subtype.ext hσβ
  obtain ⟨x, hxN, hxa, hxb, hx⟩ :=
    C.D.exists_mem_normalizer_M_of_smul_eq C.coord_eq C.coord_ne hσa hσb
  set ΔM := holtDelta (C.D.M C.i) (C.D.Ψc C.i) (C.D.coord C.a C.i) (C.D.coord C.b C.i) with hΔM
  set f : holtDelta G Ω α C.β → C.D.Ψc C.i := fun δ =>
    if h : (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) then C.D.coord ⟨δ, h⟩ C.i
    else C.D.coord C.a C.i with hf
  have hfB : ∀ δ : holtDelta G Ω α C.β, ∀ h : (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v),
      f δ = C.D.coord ⟨δ, h⟩ C.i := fun δ h => by simp [hf, h]
  have hline : ∀ δ : holtDelta G Ω α C.β, ∀ h : (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v),
      ∀ j, j ≠ C.i → C.D.coord ⟨δ, h⟩ j = C.D.coord C.a j := fun δ h =>
    ((C.mem_holtDelta_iff hS ⟨δ, h⟩).mp δ.2).1
  have hσline : ∀ δ : holtDelta G Ω α C.β, ∀ h : (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v),
      x (f δ) = f δ ↔ σ • (δ : Ω) = δ := fun δ h => by
    obtain ⟨hoff, hi⟩ := hx ⟨δ, h⟩ (hline δ h)
    rw [hfB δ h, ← hi]
    constructor
    · intro e
      have he : σv • (⟨δ, h⟩ : fixSet Ω (Subgroup.zpowers v)) = ⟨δ, h⟩ :=
        C.coord_injective (funext fun j => by
          rcases eq_or_ne j C.i with rfl | hj
          · exact e
          · rw [hoff j hj, hline δ h j hj])
      exact congrArg (fun y : fixSet Ω (Subgroup.zpowers v) => (y : Ω)) he
    · intro e
      have he : σv • (⟨δ, h⟩ : fixSet Ω (Subgroup.zpowers v)) = ⟨δ, h⟩ := Subtype.ext e
      rw [he]
  have hmF : ∀ δ : holtDelta G Ω α C.β, K.D'.coord δ K.j₀ = p →
      (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) := fun δ hδ =>
    (K.mem_fixSet_iff hι δ).mpr (by rw [hδ]; exact hp)
  have hle : m ≤ (ΔM ∩ {y | x y = y}).ncard := by
    refine Set.ncard_le_ncard_of_injOn f (fun δ hδ => ?_) (fun δ hδ δ' hδ' e => ?_)
      (Set.toFinite _)
    · have hδF := hmF δ hδ
      refine ⟨?_, (hσline δ hδF).mpr (hfix δ hδ)⟩
      rw [hfB δ hδF]
      exact ((C.mem_holtDelta_iff hS ⟨δ, hδF⟩).mp δ.2).2
    · have hδF := hmF δ hδ
      have hδ'F := hmF δ' hδ'
      rw [hfB δ hδF, hfB δ' hδ'F] at e
      have h : (⟨δ, hδF⟩ : fixSet Ω (Subgroup.zpowers v)) = ⟨δ', hδ'F⟩ :=
        C.coord_injective (funext fun j => by
          rcases eq_or_ne j C.i with rfl | hj
          · exact e
          · rw [hline δ hδF j hj, hline δ' hδ'F j hj])
      exact Subtype.ext (congrArg (fun y : fixSet Ω (Subgroup.zpowers v) => (y : Ω)) h)
  have hmove : ∃ y ∈ ΔM, x y ≠ y := by
    refine ⟨f δ₂, ?_, fun e => hδ₂ ((hσline δ₂ hδ₂F).mp e)⟩
    rw [hfB δ₂ hδ₂F]
    exact ((C.mem_holtDelta_iff hS ⟨δ₂, hδ₂F⟩).mp δ₂.2).2
  have hbound := hSEf (C.D.Ψc C.i) (C.D.M C.i) (C.isNaturalSE C.i) C.coord_ne x hxN hxa hxb
    hmove
  have hΔM : ΔM.ncard = 3 * m := by rw [hΔM, ← C.ncard_B_eq hS, K.ncard_B hι p]
  rw [hΔM] at hbound
  nlinarith

end Sigma

end CFSG.Holt.H78
