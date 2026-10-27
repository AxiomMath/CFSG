module

import CFSG.Holt.H78.Sec4Known
import CFSG.Holt.H78.Sec4Box
import CFSG.Holt.H78.SEModelFive
public import CFSG.Holt.H78.Sec4Toolkit

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt Equiv
open scoped Pointwise


section Fibre


variable {X Y : Type*} (f : X → Y)

private def fibrePermSubgroup : Subgroup (Perm X) where
  carrier := {π | ∃ σ : Perm Y, ∀ x, f (π x) = σ (f x)}
  mul_mem' := by
    rintro π τ ⟨σ, hσ⟩ ⟨σ', hσ'⟩
    exact ⟨σ * σ', fun x => by rw [Perm.mul_apply, hσ, hσ', Perm.mul_apply]⟩
  one_mem' := ⟨1, fun _ => rfl⟩
  inv_mem' := by
    rintro π ⟨σ, hσ⟩
    exact ⟨σ⁻¹, fun x => Perm.eq_inv_iff_eq.mpr (by rw [← hσ]; simp)⟩

variable {f}

private theorem fibre_perm_unique (hf : Function.Surjective f) {π : Perm X} {σ τ : Perm Y}
    (hσ : ∀ x, f (π x) = σ (f x)) (hτ : ∀ x, f (π x) = τ (f x)) : σ = τ :=
  Equiv.ext fun y => by
    obtain ⟨x, rfl⟩ := hf y
    rw [← hσ, hτ]

private noncomputable def fibreActHom (hf : Function.Surjective f) :
    fibrePermSubgroup f →* Perm Y where
  toFun π := π.2.choose
  map_one' := fibre_perm_unique hf (1 : fibrePermSubgroup f).2.choose_spec fun _ => rfl
  map_mul' π τ := fibre_perm_unique hf (π * τ).2.choose_spec fun x => by
    rw [Subgroup.coe_mul, Perm.mul_apply, π.2.choose_spec, τ.2.choose_spec, Perm.mul_apply]

private theorem fibreActHom_eq (hf : Function.Surjective f) (π : fibrePermSubgroup f)
    {σ : Perm Y} (hσ : ∀ x, f ((π : Perm X) x) = σ (f x)) : fibreActHom hf π = σ :=
  fibre_perm_unique hf π.2.choose_spec hσ

end Fibre

section Simple

private theorem closure_orderOf_eq_two_eq_top {M : Type*} [Group M] [IsSimpleGroup M] {x : M}
    (hx : orderOf x = 2) : Subgroup.closure {y : M | orderOf y = 2} = ⊤ := by
  have hconj : Group.conjugatesOfSet {y : M | orderOf y = 2} ⊆ {y : M | orderOf y = 2} := by
    intro z hz
    obtain ⟨a, ha, c, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hz
    exact (SemiconjBy.orderOf_eq _ hc).symm.trans ha
  have hle : Subgroup.normalClosure {y : M | orderOf y = 2} ≤
      Subgroup.closure {y : M | orderOf y = 2} := Subgroup.closure_mono hconj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure {y : M | orderOf y = 2}) with h | h
  · have hx1 : x ∈ (⊥ : Subgroup M) := h ▸ Subgroup.subset_normalClosure hx
    rw [Subgroup.mem_bot] at hx1
    rw [hx1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  · exact eq_top_iff.mpr (h ▸ hle)

theorem IsNaturalSE.isEmpty_mulEquiv_alternatingGroup_fin {Δ : Type*} [Finite Δ]
    {M : Subgroup (Perm Δ)} (hM : IsNaturalSE M) (h5 : Nat.card Δ ≠ 5) {m : ℕ} (hm : 5 ≤ m) :
    IsEmpty (M ≃* alternatingGroup (Fin m)) := by
  rcases (show m = 5 ∨ 6 ≤ m by omega) with rfl | h6
  · refine ⟨fun φ => h5 ?_⟩
    obtain ⟨n, i, e, hA⟩ := hM.exists_isBenderAction
    have hA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      have h := two_mul_card_alternatingGroup (α := Fin 5)
      rw [Fintype.card_perm, Fintype.card_fin] at h
      rw [Nat.card_eq_fintype_card]
      have : Nat.factorial 5 = 120 := rfl
      omega
    have hcard : Nat.card M = 60 := by rw [Nat.card_congr φ.toEquiv, hA5]
    have := hA.isPretransitive
    have : Nonempty Δ := by
      have h0 : 0 < Nat.card Δ := by rw [hA.card_eq]; omega
      exact (Nat.card_pos_iff.mp h0).1
    have hdvd : Nat.card Δ ∣ 60 := by
      rw [← hcard, ← index_stabilizer_of_transitive M (Classical.arbitrary Δ)]
      exact Subgroup.index_dvd_card _
    have h4 := hA.four_le_pow
    rw [hA.card_eq] at hdvd ⊢
    rw [← pow_mul] at hdvd h4 ⊢
    have hle : 2 ^ (n * i) < 2 ^ 6 := by
      have := Nat.le_of_dvd (by norm_num) hdvd
      norm_num
      omega
    have hlo : 2 ^ 2 ≤ 2 ^ (n * i) := by norm_num; omega
    have h6' := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hle
    have h2' := (Nat.pow_le_pow_iff_right (by norm_num)).mp hlo
    interval_cases (n * i) <;> first | rfl | (norm_num at hdvd)
  · exact hM.not_mulEquiv_alternatingGroup (by simpa using h6)

end Simple

section Line

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]

private abbrev lineSet {α β : Ω} (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β))
    (i : D.ι) (γ : holtDelta G Ω α β) : Set Ω :=
  Subtype.val '' {δ : holtDelta G Ω α β | ∀ j, j ≠ i → D.coord δ j = D.coord γ j}

private theorem exists_mem_centralizer_rho_eq (hS : Sec4Setting G Ω) {α β : Ω} (hαβ : α ≠ β)
    (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) {i : D.ι}
    (hi : IsNaturalSE (D.M i)) (γ : holtDelta G Ω α β) {V : Subgroup G} (hV : IsPGroup 2 V)
    (hVαβ : V ≤ stabilizer G α ⊓ stabilizer G β) (hℓV : lineSet D i γ ⊆ fixSet Ω V)
    {x : Perm (D.Ψc i)} (hxM : x ∈ D.M i) (hx : orderOf x = 2) :
    ∃ (c : G) (hc : c ∈ longInvSwap G Ω α β), c ∈ Subgroup.centralizer (V : Set G) ∧
      D.ρ i ⟨twoPointElt (closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure hc)),
        twoPointElt_mem_jHull hS.star (Subgroup.subset_closure hc)⟩ = x := by
  classical
  have h3Δ := three_le_card_holtDelta_of_holtData hS.star D
  have hxJ : x ∈ longInv (Perm (D.Ψc i)) (D.Ψc i) := by
    refine ⟨hx, ?_⟩
    have := hi.existsUnique_fixed (x := ⟨x, hxM⟩) (by rwa [Subgroup.orderOf_mk])
    simpa using this
  obtain ⟨w, hw, hwγ⟩ := γ.2
  set wΔ : jHull (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
    ⟨twoPointElt (closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure hw)),
      twoPointElt_mem_jHull hS.star (Subgroup.subset_closure hw)⟩
  have hwΔJ : (wΔ : twoPointSection G Ω α β) ∈
      longInv (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
    (hS.mem_longInv_twoPointSection_iff hαβ h3Δ _).mpr ⟨w, hw, fun δ => rfl⟩
  set y : ∀ j, Perm (D.Ψc j) := Function.update (fun j => D.ρ j wΔ) i x with hy
  have hyr : ∀ j, y j ∈ (D.ρ j).range := by
    intro j
    rcases eq_or_ne j i with rfl | hj
    · rw [hy, Function.update_self]
      exact Subgroup.map_le_range _ _ hxM
    · rw [hy, Function.update_of_ne hj]
      exact ⟨wΔ, rfl⟩
  have hyJ : ∀ j, y j ∈ longInv (Perm (D.Ψc j)) (D.Ψc j) := by
    intro j
    rcases eq_or_ne j i with rfl | hj
    · rw [hy, Function.update_self]
      exact hxJ
    · rw [hy, Function.update_of_ne hj]
      exact D.rho_mem_longInv hwΔJ j
  obtain ⟨u, huJ, hu⟩ := D.exists_mem_longInv_rho_eq y hyr hyJ
  obtain ⟨c₀, hc₀, hc₀u⟩ := (hS.mem_longInv_twoPointSection_iff hαβ h3Δ _).mp huJ
  have hline : ∀ δ : holtDelta G Ω α β, (∀ j, j ≠ i → D.coord δ j = D.coord γ j) →
      ∀ j, j ≠ i → D.coord ((u : twoPointSection G Ω α β) • δ) j = D.coord γ j := by
    intro δ hδ j hj
    rw [D.coord_smul, hu j, hy, Function.update_of_ne hj, hδ j hj, ← D.coord_smul]
    congr 1
    exact Subtype.ext hwγ
  have hc₀mem : ∀ ω ∈ lineSet D i γ, c₀ • ω ∈ lineSet D i γ := by
    rintro _ ⟨δ, hδ, rfl⟩
    exact ⟨(u : twoPointSection G Ω α β) • δ, hline δ hδ, hc₀u δ⟩
  have hc₀ℓ : c₀ ∈ stabilizer G (lineSet D i γ) := by
    rw [mem_stabilizer_set]
    intro ω
    refine ⟨fun h => ?_, hc₀mem ω⟩
    have := hc₀mem _ h
    rwa [smul_smul, mul_self_eq_one_of_mem_longInv hc₀.1, one_smul] at this
  obtain ⟨c, hc, hcV, hcℓ⟩ := hS.exists_mem_longInvSwap_centralizer_eqOn hαβ hV hVαβ
    (⟨(γ : Ω), γ, fun j _ => rfl, rfl⟩ : (lineSet D i γ).Nonempty) hℓV hc₀ hc₀ℓ
  refine ⟨c, hc, hcV, Equiv.ext fun ψ => ?_⟩
  obtain ⟨δ, hδ⟩ := D.exists_coord_eq_update γ i ψ
  have hδℓ : ∀ j, j ≠ i → D.coord δ j = D.coord γ j := fun j hj => by
    rw [hδ, Function.update_of_ne hj]
  have hψ : D.coord δ i = ψ := by rw [hδ, Function.update_self]
  have hx' : x = y i := by rw [hy, Function.update_self]
  rw [hx', ← hu i, ← hψ, ← D.coord_smul, ← D.coord_smul]
  congr 1
  apply Subtype.ext
  exact (hcℓ δ ⟨δ, hδℓ, rfl⟩).trans (hc₀u δ).symm

end Line

section Key

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

theorem Sec4Setting.false_of_line_subset_fixSet (hS : Sec4Setting G Ω) {α β : Ω} (hαβ : α ≠ β)
    (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) {i : D.ι}
    (hi : IsNaturalSE (D.M i)) (h5 : Fintype.card (D.Ψc i) ≠ 5) (γ : holtDelta G Ω α β)
    {V : Subgroup G} (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥)
    (hVαβ : V ≤ stabilizer G α ⊓ stabilizer G β)
    (hℓV : ∀ δ : holtDelta G Ω α β, (∀ j, j ≠ i → D.coord δ j = D.coord γ j) →
      (δ : Ω) ∈ fixSet Ω V) : False := by
  classical
  have hα : α ∈ fixSet Ω V := mem_fixSet_iff_le_stabilizer.mpr (hVαβ.trans inf_le_left)
  have hβ : β ∈ fixSet Ω V := mem_fixSet_iff_le_stabilizer.mpr (hVαβ.trans inf_le_right)
  have hab : (⟨α, hα⟩ : fixSet Ω V) ≠ ⟨β, hβ⟩ := fun h => hαβ (congrArg Subtype.val h)
  have h3 := hS.three_le_card_fixSet_of_ne hV hab
  obtain ⟨DK⟩ := hS.holtData_centralizerImage hV hV1 h3
  have hgen := fun π => hS.mem_longInvSwap_centralizerImage_iff hV h3 (a := ⟨α, hα⟩)
    (b := ⟨β, hβ⟩) π
  set k := longInvSwap (centralizerImage Ω V) (fixSet Ω V) ⟨α, hα⟩ ⟨β, hβ⟩
  set Λ : Set (fixSet Ω V) := {p | (p : Ω) ∈ holtDelta G Ω α β}
  have hCΛ : Subgroup.closure k ≤ stabilizer (centralizerImage Ω V) Λ := by
    rw [Subgroup.closure_le]
    intro π hπ
    obtain ⟨c, hc, -, hcπ⟩ := (hgen π).mp hπ
    rw [SetLike.mem_coe, mem_stabilizer_set]
    intro p
    show ((π • p : fixSet Ω V) : Ω) ∈ holtDelta G Ω α β ↔ (p : Ω) ∈ holtDelta G Ω α β
    rw [show ((π • p : fixSet Ω V) : Ω) = c • (p : Ω) from hcπ p]
    exact mem_stabilizer_set.mp (mem_stabilizer_holtDelta_of_mem_longInvSwap hc) _
  set r := inducedHom (Subgroup.closure k) Λ hCΛ
  set f : Λ → D.Ψc i := fun p => D.coord ⟨((p : fixSet Ω V) : Ω), p.2⟩ i with hfdef
  have hf : Function.Surjective f := by
    intro ψ
    obtain ⟨δ, hδ⟩ := D.exists_coord_eq_update γ i ψ
    have hδV := hℓV δ fun j hj => by rw [hδ, Function.update_of_ne hj]
    refine ⟨⟨⟨δ, hδV⟩, δ.2⟩, ?_⟩
    show D.coord δ i = ψ
    rw [hδ, Function.update_self]
  have hgenσ : ∀ (π : centralizerImage Ω V) (c : G) (hc : c ∈ longInvSwap G Ω α β),
      (∀ ω : fixSet Ω V, ((π : Perm (fixSet Ω V)) ω : Ω) = c • (ω : Ω)) →
      ∀ (hπ : π ∈ Subgroup.closure k) (p : Λ), f (r ⟨π, hπ⟩ p) =
        D.ρ i ⟨twoPointElt (closure_longInvSwap_le_stabilizer_pair α β
          (Subgroup.subset_closure hc)), twoPointElt_mem_jHull hS.star
            (Subgroup.subset_closure hc)⟩ (f p) := by
    intro π c hc hcπ hπ p
    simp only [hfdef]
    rw [← D.coord_smul]
    congr 1
    apply Subtype.ext
    exact hcπ p
  have hle : r.range ≤ fibrePermSubgroup f := by
    rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage (k := k),
      MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨⟨π, hπC⟩, hπ, rfl⟩
    obtain ⟨c, hc, -, hcπ⟩ := (hgen π).mp hπ
    exact ⟨_, hgenσ π c hc hcπ hπC⟩
  set φ : Subgroup.closure k →* Perm (D.Ψc i) :=
    (fibreActHom hf).comp (r.codRestrict _ fun x => hle ⟨x, rfl⟩)
  have hφ : ∀ (π : centralizerImage Ω V) (hπ : π ∈ k) (c : G) (hc : c ∈ longInvSwap G Ω α β),
      (∀ ω : fixSet Ω V, ((π : Perm (fixSet Ω V)) ω : Ω) = c • (ω : Ω)) →
      φ ⟨π, Subgroup.subset_closure hπ⟩ = D.ρ i ⟨twoPointElt
        (closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure hc)),
          twoPointElt_mem_jHull hS.star (Subgroup.subset_closure hc)⟩ :=
    fun π _ c hc hcπ => fibreActHom_eq hf _ (hgenσ π c hc hcπ _)
  have hrange : φ.range = D.M i := by
    apply le_antisymm
    · rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage (k := k),
        MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨⟨π, hπC⟩, hπ, rfl⟩
      obtain ⟨c, hc, -, hcπ⟩ := (hgen π).mp hπ
      rw [SetLike.mem_coe, hφ π hπ c hc hcπ]
      exact rho_twoPointElt_mem_M_of_isNaturalSE hS.star D hi (Subgroup.subset_closure hc)
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := D.isSimpleGroup_M i
      obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' 2 (D.factor i).two_dvd_card
      intro x hx
      have hx' : x ∈ (Subgroup.closure {y : D.M i | orderOf y = 2}).map (D.M i).subtype := by
        rw [closure_orderOf_eq_two_eq_top hx₀]
        exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
      rw [MonoidHom.map_closure] at hx'
      refine (Subgroup.closure_le _).mpr ?_ hx'
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨c, hc, hcV, hcy⟩ := exists_mem_centralizer_rho_eq hS hαβ D hi γ hV hVαβ
        (by rintro _ ⟨δ, hδ, rfl⟩; exact hℓV δ hδ) y.2 (by rwa [Subgroup.orderOf_coe])
      have hπ : centralizerImageElt (Ω := Ω) hcV ∈ k :=
        (hgen _).mpr ⟨c, hc, hcV, fun ω => rfl⟩
      exact ⟨⟨_, Subgroup.subset_closure hπ⟩, (hφ _ hπ c hc fun ω => rfl).trans hcy⟩
  have := D.isSimpleGroup_M i
  have hN : ∃ a b : D.M i, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact D.not_isMulCommutative_M i (isMulCommutative_iff.mpr h)
  set ψ : (⊤ : Subgroup (Subgroup.closure k)) →* D.M i :=
    (MulEquiv.subgroupCongr hrange).toMonoidHom.comp
      (φ.rangeRestrict.comp (⊤ : Subgroup (Subgroup.closure k)).subtype)
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨a, ha⟩ := φ.rangeRestrict_surjective ((MulEquiv.subgroupCongr hrange).symm z)
    refine ⟨⟨a, Subgroup.mem_top a⟩, ?_⟩
    show (MulEquiv.subgroupCongr hrange) (φ.rangeRestrict a) = z
    rw [ha, MulEquiv.apply_symm_apply]
  obtain ⟨m, hm, ⟨e⟩⟩ := DK.exists_mulEquiv_alternatingGroup ⟨α, hα⟩ ⟨β, hβ⟩
    (L := ⊤) Subgroup.normal_top hN hψ
  exact (hi.isEmpty_mulEquiv_alternatingGroup_fin (by rwa [Nat.card_eq_fintype_card]) hm).false e

end Key

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

theorem Sec4Setting.odd_card_twoPointKernel_of_isNaturalSE (hS : Sec4Setting G Ω) {α β : Ω}
    (hαβ : α ≠ β) (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) {i : D.ι}
    (hi : IsNaturalSE (D.M i)) (h5 : Fintype.card (D.Ψc i) ≠ 5) :
    Odd (Nat.card (twoPointKernel G Ω α β)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3Δ := three_le_card_holtDelta_of_holtData hS.star D
  obtain ⟨γ⟩ : Nonempty (holtDelta G Ω α β) := (Nat.card_pos_iff.mp (by omega)).1
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
  refine hS.false_of_line_subset_fixSet hαβ D hi h5 γ (V := Subgroup.zpowers (x : G)) ?_ ?_
    (Subgroup.zpowers_le.mpr (twoPointKernel_le_inf x.2)) fun δ _ => ?_
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one])
  · rw [Ne, Subgroup.zpowers_eq_bot]
    intro h1
    rw [← Subgroup.orderOf_coe, h1, orderOf_one] at hx
    omega
  · rw [mem_fixSet_iff_le_stabilizer, Subgroup.zpowers_le]
    exact mem_stabilizer_iff.mpr
      ((mem_fixingSubgroup_iff G).mp (twoPointKernel_le_fixingSubgroup x.2) δ δ.2)

private theorem HoltData.exists_mem_M_orderOf_eq_two_apply_eq {K X : Type*} [Group K]
    [Finite K] [MulAction K X] (D : HoltData K X) (l : D.ι) (b : D.Ψc l) :
    ∃ x ∈ D.M l, orderOf x = 2 ∧ x b = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 (D.factor l).two_dvd_card
  have hyP : IsPGroup 2 (Subgroup.zpowers (y : Perm (D.Ψc l))) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy, pow_one])
  obtain ⟨p, hp⟩ := fixSet_nonempty_of_odd (Ω := D.Ψc l)
    (by rw [Nat.card_eq_fintype_card]; exact D.odd_card_Ψc l) hyP
  have hyp : (y : Perm (D.Ψc l)) p = p :=
    mem_fixSet_iff_le_stabilizer.mp hp (Subgroup.mem_zpowers _)
  have := (D.factor l).isPretransitive
  obtain ⟨g, hg⟩ := exists_smul_eq (D.M l) p b
  refine ⟨(g : Perm (D.Ψc l)) * y * (g : Perm (D.Ψc l))⁻¹,
    mul_mem (mul_mem g.2 y.2) (inv_mem g.2), ?_, ?_⟩
  · have h' : SemiconjBy (g : Perm (D.Ψc l)) (y : Perm (D.Ψc l))
        ((g : Perm (D.Ψc l)) * y * (g : Perm (D.Ψc l))⁻¹) := by
      simp [SemiconjBy, mul_assoc]
    rw [← SemiconjBy.orderOf_eq _ h', Subgroup.orderOf_coe, hy]
  · have hgb : (g : Perm (D.Ψc l)) p = b := hg
    rw [Perm.mul_apply, Perm.mul_apply, ← hgb]
    simp [hyp]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
private theorem exists_mem_inf_twoPointHom_eq_of_mem_commutator {α β : Ω}
    {L' : Subgroup (jHull (twoPointSection G Ω α β) (holtDelta G Ω α β))}
    {h : jHull (twoPointSection G Ω α β) (holtDelta G Ω α β)} (hh : h ∈ ⁅L', L'⁆) :
    ∃ s : stabilizer G ({α, β} : Set Ω), (s : G) ∈ stabilizer G α ⊓ stabilizer G β ∧
      twoPointHom G Ω α β s = ((h : twoPointSection G Ω α β) : Perm (holtDelta G Ω α β)) := by
  set F := (twoPointSection G Ω α β).subtype.comp
    (jHull (twoPointSection G Ω α β) (holtDelta G Ω α β)).subtype
  have h1 : F h ∈ ⁅(twoPointHom G Ω α β).range, (twoPointHom G Ω α β).range⁆ := by
    have h2 := Subgroup.mem_map_of_mem F hh
    rw [Subgroup.map_commutator] at h2
    have hle : L'.map F ≤ (twoPointHom G Ω α β).range := by
      rintro _ ⟨z, -, rfl⟩
      exact (z : twoPointSection G Ω α β).2
    exact Subgroup.commutator_mono hle hle h2
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator] at h1
  obtain ⟨s, hs, hsh⟩ := h1
  refine ⟨s, ?_, hsh⟩
  have h3 := Subgroup.mem_map_of_mem (stabilizer G ({α, β} : Set Ω)).subtype hs
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h3
  exact commutator_stabilizer_pair_le α β h3

theorem Sec4Setting.card_ι_eq_one_of_isNaturalSE (hS : Sec4Setting G Ω) {α β : Ω}
    (hαβ : α ≠ β) (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) {i : D.ι}
    (hi : IsNaturalSE (D.M i)) (h5 : Fintype.card (D.Ψc i) ≠ 5)
    (hO : jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β) = ⊥) :
    Fintype.card D.ι = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3Δ := three_le_card_holtDelta_of_holtData hS.star D
  obtain ⟨γ⟩ : Nonempty (holtDelta G Ω α β) := (Nat.card_pos_iff.mp (by omega)).1
  by_contra hι
  obtain ⟨l, hl⟩ : ∃ l, l ≠ i := by
    by_contra h
    push Not at h
    exact hι (Fintype.card_eq_one_iff.mpr ⟨i, h⟩)
  obtain ⟨x, hxM, hx2, hxγ⟩ := D.exists_mem_M_orderOf_eq_two_apply_eq l (D.coord γ l)
  have := D.isPerfect_M l
  have hxC : x ∈ (⁅(D.L l).subgroupOf (jHull (twoPointSection G Ω α β) (holtDelta G Ω α β)),
      (D.L l).subgroupOf (jHull (twoPointSection G Ω α β) (holtDelta G Ω α β))⁆).map
        (D.ρ l) := by
    rw [Subgroup.map_commutator]
    exact (Subgroup.commutator_eq_self (H := D.M l)).symm ▸ hxM
  obtain ⟨h, hhC, hhx⟩ := hxC
  have hhL : (h : twoPointSection G Ω α β) ∈ D.L l := by
    refine Subgroup.mem_subgroupOf.mp ((Subgroup.commutator_le.mpr fun a ha b hb => ?_) hhC)
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  obtain ⟨s, hsαβ, hsh⟩ := exists_mem_inf_twoPointHom_eq_of_mem_commutator hhC
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (s : G)).ne'
  have hxm : x ^ m = x := by
    obtain ⟨t, rfl⟩ := hm
    rw [pow_succ, pow_mul, ← hx2, pow_orderOf_eq_one, one_pow, one_mul]
  have hρl : D.ρ l (h ^ m) = x := by rw [map_pow, hhx, hxm]
  have hρj : ∀ j, j ≠ l → D.ρ j (h ^ m) = 1 := fun j hj => by
    rw [map_pow, D.rho_eq_one_of_mem_L (Ne.symm hj) hhL, one_pow]
  have hfix : ∀ δ : holtDelta G Ω α β, (∀ j, j ≠ i → D.coord δ j = D.coord γ j) →
      ((h ^ m : jHull _ _) : twoPointSection G Ω α β) • δ = δ := by
    intro δ hδ
    have hc : D.coord (((h ^ m : jHull _ _) : twoPointSection G Ω α β) • δ) = D.coord δ := by
      funext j
      rw [D.coord_smul]
      rcases eq_or_ne j l with hj | hj
      · rw [hj, hρl, hδ l hl, hxγ]
      · rw [hρj j hj, Perm.one_apply]
    obtain ⟨g, hg⟩ := (D.coord_eq_iff _ _).mp hc
    have hg' : (g : twoPointSection G Ω α β) •
        (((h ^ m : jHull _ _) : twoPointSection G Ω α β) • δ) = δ := hg
    rwa [(Subgroup.eq_bot_iff_forall _).mp hO _ g.2, one_smul] at hg'
  have hg₀Δ : ∀ δ : holtDelta G Ω α β, (s : G) ^ m • (δ : Ω) =
      ((((h ^ m : jHull _ _) : twoPointSection G Ω α β) • δ : holtDelta G Ω α β) : Ω) := by
    intro δ
    have hpow : twoPointHom G Ω α β (s ^ m) =
        (((h ^ m : jHull _ _) : twoPointSection G Ω α β) : Perm (holtDelta G Ω α β)) := by
      rw [map_pow, hsh]
      rfl
    rw [← Subgroup.coe_pow, ← coe_twoPointHom_apply, hpow]
    rfl
  have hP : IsPGroup 2 (Subgroup.zpowers ((s : G) ^ m)) := by
    have hdvd : orderOf ((s : G) ^ m) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
      rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one])
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hV1 : Subgroup.zpowers ((s : G) ^ m) ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    intro h1
    have hone : h ^ m = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      refine Equiv.ext fun δ => Subtype.ext ?_
      have := hg₀Δ δ
      rw [h1, one_smul] at this
      exact this.symm
    have hx1 := hρl
    rw [hone, map_one] at hx1
    rw [← hx1, orderOf_one] at hx2
    omega
  refine hS.false_of_line_subset_fixSet hαβ D hi h5 γ hP hV1
    (Subgroup.zpowers_le.mpr (pow_mem hsαβ m)) fun δ hδ => ?_
  rw [mem_fixSet_iff_le_stabilizer, Subgroup.zpowers_le, mem_stabilizer_iff, hg₀Δ δ, hfix δ hδ]

theorem Sec4Setting.lemma_4_2 (hS : Sec4Setting G Ω) {α β : Ω} (hαβ : α ≠ β)
    (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) (i : D.ι)
    (hi : IsNaturalSE (factorImage _ _ (D.L i) (D.ρ i))) (h5 : Fintype.card (D.Ψc i) ≠ 5) :
    Odd (Nat.card (twoPointKernel G Ω α β)) ∧
      (jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β) = ⊥ → Fintype.card D.ι = 1) :=
  ⟨hS.odd_card_twoPointKernel_of_isNaturalSE hαβ D hi h5,
    hS.card_ι_eq_one_of_isNaturalSE hαβ D hi h5⟩

end Main

end CFSG.Holt.H78
