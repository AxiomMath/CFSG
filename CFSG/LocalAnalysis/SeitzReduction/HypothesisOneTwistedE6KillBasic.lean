module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassKillBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6InnerBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6TwoRoots

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem twKill_cocycle_aux {a z y : G} (haz : a * z = z * a) (hzy : z * y = y * z)
    (hyy : y * y = 1) (hcoc : a * (z * y) * a = (z * y)⁻¹) :
    z * z * (y⁻¹ * (a * y * a)) = 1 := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have h0 : z * (a * y * a) = (z * y)⁻¹ := by
    rw [← hcoc]
    calc z * (a * y * a) = (z * a) * y * a := by group
      _ = (a * z) * y * a := by rw [haz]
      _ = a * (z * y) * a := by group
  have h1 : a * y * a = z⁻¹ * (z * y)⁻¹ := by
    calc a * y * a = z⁻¹ * (z * (a * y * a)) := by group
      _ = _ := by rw [h0]
  have hzy' : z⁻¹ * y = y * z⁻¹ := by
    calc z⁻¹ * y = z⁻¹ * (y * z) * z⁻¹ := by group
      _ = z⁻¹ * (z * y) * z⁻¹ := by rw [hzy]
      _ = y * z⁻¹ := by group
  rw [h1, mul_inv_rev, hyinv]
  calc z * z * (y * (z⁻¹ * (y * z⁻¹))) = z * z * (y * (z⁻¹ * y) * z⁻¹) := by group
    _ = z * z * (y * (y * z⁻¹) * z⁻¹) := by rw [hzy']
    _ = z * z * ((y * y) * z⁻¹ * z⁻¹) := by group
    _ = 1 := by rw [hyy]; group

theorem twKill_kill_aux {a z y p : G} (hzp : z * (a * p * a) = a * p * a * z)
    (hyp : y * p = p * y) (hk : a * p * a * p⁻¹ * y = 1) :
    a * p * a * (z * y) * p⁻¹ = z := by
  have hyp' : y * p⁻¹ = p⁻¹ * y := by
    calc y * p⁻¹ = p⁻¹ * (p * y) * p⁻¹ := by group
      _ = p⁻¹ * (y * p) * p⁻¹ := by rw [hyp]
      _ = p⁻¹ * y := by group
  calc a * p * a * (z * y) * p⁻¹ = (a * p * a * z) * (y * p⁻¹) := by group
    _ = (z * (a * p * a)) * (p⁻¹ * y) := by rw [← hzp, hyp']
    _ = z * (a * p * a * p⁻¹ * y) := by group
    _ = z := by rw [hk, mul_one]

theorem twKill_cocycle {V N : Subgroup G} (hNV : N ≤ V)
    (hnorm : ∀ v ∈ V, ∀ m ∈ N, v * m * v⁻¹ ∈ N)
    {a z y n : G} (ha : a ∈ V) (hz : z ∈ V) (hy : y ∈ V) (hn : n ∈ N)
    (haz : a * z = z * a) (hzy : ⁅z, y⁆ ∈ N) (hyy : y * y ∈ N)
    (hcoc : a * (z * (y * n)) * a = (z * (y * n))⁻¹) :
    z * z * (y⁻¹ * (a * y * a)) ∈ N := by
  have hnormal : (N.subgroupOf V).Normal :=
    ⟨fun x hx b => Subgroup.mem_subgroupOf.2 (hnorm b.1 b.2 x.1 (Subgroup.mem_subgroupOf.1 hx))⟩
  set π : V →* V ⧸ N.subgroupOf V := QuotientGroup.mk' (N.subgroupOf V) with hπ
  have key : ∀ x : V, π x = 1 ↔ (x : G) ∈ N := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set a' : V := ⟨a, ha⟩
  set z' : V := ⟨z, hz⟩
  set y' : V := ⟨y, hy⟩
  set n' : V := ⟨n, hNV hn⟩
  have czy : π z' * π y' = π y' * π z' := (classKill_quot_commute π ((key _).2 hzy)).eq
  have haz' : π a' * π z' = π z' * π a' := by
    rw [← map_mul, ← map_mul]; congr 1; exact Subtype.ext haz
  have hyy' : π y' * π y' = 1 := by rw [← map_mul]; exact (key _).2 hyy
  have hn1 : π n' = 1 := (key _).2 hn
  have hcoc' : π (a' * (z' * (y' * n')) * a') = π ((z' * (y' * n'))⁻¹) := by
    congr 1; exact Subtype.ext hcoc
  simp only [map_mul, map_inv, hn1, mul_one] at hcoc'
  have goal : π (z' * z' * (y'⁻¹ * (a' * y' * a'))) = 1 := by
    simp only [map_mul, map_inv]
    exact twKill_cocycle_aux haz' czy hyy' hcoc'
  exact (key _).1 goal

theorem twKill_kill {V N : Subgroup G} (hNV : N ≤ V)
    (hnorm : ∀ v ∈ V, ∀ m ∈ N, v * m * v⁻¹ ∈ N)
    {a z y p n : G} (ha : a ∈ V) (hz : z ∈ V) (hy : y ∈ V) (hp : p ∈ V) (hn : n ∈ N)
    (hzp : ⁅z, a * p * a⁆ ∈ N) (hyp : ⁅y, p⁆ ∈ N) (hk : a * p * a * p⁻¹ * y ∈ N) :
    z⁻¹ * (a * p * a * (z * (y * n)) * p⁻¹) ∈ N := by
  have hnormal : (N.subgroupOf V).Normal :=
    ⟨fun x hx b => Subgroup.mem_subgroupOf.2 (hnorm b.1 b.2 x.1 (Subgroup.mem_subgroupOf.1 hx))⟩
  set π : V →* V ⧸ N.subgroupOf V := QuotientGroup.mk' (N.subgroupOf V) with hπ
  have key : ∀ x : V, π x = 1 ↔ (x : G) ∈ N := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set a' : V := ⟨a, ha⟩
  set z' : V := ⟨z, hz⟩
  set y' : V := ⟨y, hy⟩
  set p' : V := ⟨p, hp⟩
  set n' : V := ⟨n, hNV hn⟩
  have czp : π z' * π (a' * p' * a') = π (a' * p' * a') * π z' :=
    (classKill_quot_commute π ((key _).2 hzp)).eq
  have cyp : π y' * π p' = π p' * π y' := (classKill_quot_commute π ((key _).2 hyp)).eq
  have hk' : π (a' * p' * a' * p'⁻¹ * y') = 1 := (key _).2 hk
  have hn1 : π n' = 1 := (key _).2 hn
  simp only [map_mul, map_inv] at czp hk'
  have goal : π (z'⁻¹ * (a' * p' * a' * (z' * (y' * n')) * p'⁻¹)) = 1 := by
    simp only [map_mul, map_inv, hn1, mul_one]
    rw [twKill_kill_aux czp cyp hk', inv_mul_cancel]
  exact (key _).1 goal

end Group

section Detect

variable {τ : Tag} {K : Type} [Field K]

theorem twKill_detect {S : Set (Fin τ.rank → ℤ)} (hS : ∀ β ∈ S, IsRoot τ β ∧ 0 < height β)
    (hSc : ∀ β ∈ S, ∀ γ ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • γ) →
      a • β + b • γ ∈ S)
    {k : ℕ} (β : Fin k → Fin τ.rank → ℤ) (hβ : Function.Injective β)
    (hβpos : ∀ j, IsRoot τ (β j) ∧ 0 < height (β j)) (hβS : ∀ j, β j ∉ S) {e : Fin k → K}
    (h : (List.ofFn fun j => pinnedX τ K (β j) (e j)).prod ∈ rootSpan τ K S) : e = 0 := by
  classical
  obtain ⟨l, t, ht⟩ :=
    ((finite_setOf_isRoot τ).subset fun γ (hγ : γ ∈ S) => (hS γ hγ).1).fin_embedding
  have htS : ∀ j, t j ∈ S := fun j => ht ▸ Set.mem_range_self j
  obtain ⟨d, -, hd⟩ := (bijOn_prod_pinnedX K hS hSc t t.injective ht).surjOn h
  have hd' : (List.ofFn fun j => pinnedX τ K (t j) (d j)).prod =
      (List.ofFn fun j => pinnedX τ K (β j) (e j)).prod := hd
  have hinj : Function.Injective (Fin.append β ⇑t) :=
    Fin.append_injective_iff.2 ⟨hβ, t.injective, fun a b hab => hβS a (by rw [hab]; exact htS b)⟩
  have hpos : ∀ j, IsRoot τ (Fin.append β ⇑t j) ∧ 0 < height (Fin.append β ⇑t j) := by
    intro j
    induction j using Fin.addCases with
    | left j => rw [Fin.append_left]; exact hβpos j
    | right j => rw [Fin.append_right]; exact hS _ (htS j)
  have hsplit : ∀ (d₁ : Fin k → K) (d₂ : Fin l → K),
      (List.ofFn fun j => pinnedX τ K (Fin.append β ⇑t j) (Fin.append d₁ d₂ j)).prod =
        (List.ofFn fun j => pinnedX τ K (β j) (d₁ j)).prod *
          (List.ofFn fun j => pinnedX τ K (t j) (d₂ j)).prod := by
    intro d₁ d₂
    have e : (fun j => pinnedX τ K (Fin.append β ⇑t j) (Fin.append d₁ d₂ j)) =
        Fin.append (fun j => pinnedX τ K (β j) (d₁ j)) (fun j => pinnedX τ K (t j) (d₂ j)) := by
      funext j
      induction j using Fin.addCases with
      | left j => rw [Fin.append_left, Fin.append_left, Fin.append_left]
      | right j => rw [Fin.append_right, Fin.append_right, Fin.append_right]
    rw [e, List.ofFn_fin_append, List.prod_append]
  have hone : ∀ {m : ℕ} (γ : Fin m → Fin τ.rank → ℤ),
      (List.ofFn fun j => pinnedX τ K (γ j) ((0 : Fin m → K) j)).prod = 1 := by
    intro m γ
    simp only [Pi.zero_apply, pinnedX_zero, List.ofFn_const, List.prod_replicate, one_pow]
  have h1 : (List.ofFn fun j => pinnedX τ K (Fin.append β ⇑t j) (Fin.append e 0 j)).prod =
      (List.ofFn fun j => pinnedX τ K (β j) (e j)).prod := by
    rw [hsplit, hone, mul_one]
  have h2 : (List.ofFn fun j => pinnedX τ K (Fin.append β ⇑t j) (Fin.append 0 d j)).prod =
      (List.ofFn fun j => pinnedX τ K (β j) (e j)).prod := by
    rw [hsplit, hone, one_mul, hd']
  have hde := (positive_root_product_injectivity τ K _ hinj hpos).2 (h1.trans h2.symm)
  funext j
  have := congrFun hde (Fin.castAdd l j)
  simpa only [Fin.append_left] using this

theorem twKill_detect₃ {S : Set (Fin τ.rank → ℤ)} (hS : ∀ β ∈ S, IsRoot τ β ∧ 0 < height β)
    (hSc : ∀ β ∈ S, ∀ γ ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • γ) →
      a • β + b • γ ∈ S)
    {β₁ β₂ β₃ : Fin τ.rank → ℤ} (h₁ : IsRoot τ β₁ ∧ 0 < height β₁)
    (h₂ : IsRoot τ β₂ ∧ 0 < height β₂) (h₃ : IsRoot τ β₃ ∧ 0 < height β₃)
    (h12 : β₁ ≠ β₂) (h13 : β₁ ≠ β₃) (h23 : β₂ ≠ β₃) (hS₁ : β₁ ∉ S) (hS₂ : β₂ ∉ S)
    (hS₃ : β₃ ∉ S) {e₁ e₂ e₃ : K}
    (h : pinnedX τ K β₁ e₁ * pinnedX τ K β₂ e₂ * pinnedX τ K β₃ e₃ ∈ rootSpan τ K S) :
    e₁ = 0 ∧ e₂ = 0 ∧ e₃ = 0 := by
  have hinj : Function.Injective ![β₁, β₂, β₃] := by
    intro a b hab
    fin_cases a <;> fin_cases b
    all_goals first
      | rfl
      | exact absurd hab h12 | exact absurd hab h13 | exact absurd hab h23
      | exact absurd hab.symm h12 | exact absurd hab.symm h13 | exact absurd hab.symm h23
  have hp : (List.ofFn fun j => pinnedX τ K (![β₁, β₂, β₃] j) (![e₁, e₂, e₃] j)).prod =
      pinnedX τ K β₁ e₁ * pinnedX τ K β₂ e₂ * pinnedX τ K β₃ e₃ := by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
      List.prod_cons, List.prod_cons, List.prod_nil, mul_one, ← mul_assoc]
    rfl
  have he := twKill_detect hS hSc ![β₁, β₂, β₃] hinj
    (fun j => by fin_cases j <;> assumption) (fun j => by fin_cases j <;> assumption)
    (hp ▸ h)
  exact ⟨congrFun he 0, congrFun he 1, congrFun he 2⟩

theorem twKill_detect₄ {S : Set (Fin τ.rank → ℤ)} (hS : ∀ β ∈ S, IsRoot τ β ∧ 0 < height β)
    (hSc : ∀ β ∈ S, ∀ γ ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • γ) →
      a • β + b • γ ∈ S)
    {β₁ β₂ β₃ β₄ : Fin τ.rank → ℤ} (h₁ : IsRoot τ β₁ ∧ 0 < height β₁)
    (h₂ : IsRoot τ β₂ ∧ 0 < height β₂) (h₃ : IsRoot τ β₃ ∧ 0 < height β₃)
    (h₄ : IsRoot τ β₄ ∧ 0 < height β₄)
    (h12 : β₁ ≠ β₂) (h13 : β₁ ≠ β₃) (h14 : β₁ ≠ β₄) (h23 : β₂ ≠ β₃) (h24 : β₂ ≠ β₄)
    (h34 : β₃ ≠ β₄) (hS₁ : β₁ ∉ S) (hS₂ : β₂ ∉ S) (hS₃ : β₃ ∉ S) (hS₄ : β₄ ∉ S)
    {e₁ e₂ e₃ e₄ : K}
    (h : pinnedX τ K β₁ e₁ * pinnedX τ K β₂ e₂ * pinnedX τ K β₃ e₃ * pinnedX τ K β₄ e₄ ∈
      rootSpan τ K S) :
    e₁ = 0 ∧ e₂ = 0 ∧ e₃ = 0 ∧ e₄ = 0 := by
  have hinj : Function.Injective ![β₁, β₂, β₃, β₄] := by
    intro a b hab
    fin_cases a <;> fin_cases b
    all_goals first
      | rfl
      | exact absurd hab h12 | exact absurd hab h13 | exact absurd hab h14
      | exact absurd hab h23 | exact absurd hab h24 | exact absurd hab h34
      | exact absurd hab.symm h12 | exact absurd hab.symm h13 | exact absurd hab.symm h14
      | exact absurd hab.symm h23 | exact absurd hab.symm h24 | exact absurd hab.symm h34
  have hp : (List.ofFn fun j => pinnedX τ K (![β₁, β₂, β₃, β₄] j) (![e₁, e₂, e₃, e₄] j)).prod =
      pinnedX τ K β₁ e₁ * pinnedX τ K β₂ e₂ * pinnedX τ K β₃ e₃ * pinnedX τ K β₄ e₄ := by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero,
      List.prod_cons, List.prod_cons, List.prod_cons, List.prod_cons, List.prod_nil, mul_one,
      ← mul_assoc, ← mul_assoc]
    rfl
  have he := twKill_detect hS hSc ![β₁, β₂, β₃, β₄] hinj
    (fun j => by fin_cases j <;> assumption) (fun j => by fin_cases j <;> assumption)
    (hp ▸ h)
  exact ⟨congrFun he 0, congrFun he 1, congrFun he 2, congrFun he 3⟩

end Detect


section Twist

variable {K : Type} [Field K]
theorem twKill_mem_graphFixedRootGroup
    {σ : K →+* K} {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hS : ∀ β ∈ S, IsRoot TwistTag.E6.tag β ∧ 0 < height β) {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ rootSpan TwistTag.E6.tag K S) (hF : twistHom TwistTag.E6 K σ g = g) :
    g ∈ graphFixedRootGroup TwistTag.E6 K σ :=
  graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
    (Subgroup.mem_inf.2 ⟨rootSpan_le_posUnipotent hS hg, Subgroup.mem_inf.2
      ⟨(iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α :
        rootSpan TwistTag.E6.tag K S ≤ adjointGroup TwistTag.E6.tag K) hg, hF⟩⟩)


theorem twKill_F_pinnedX [CharP K 2] (σ : K →+* K) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) (d : K) :
    twistHom TwistTag.E6 K σ (pinnedX TwistTag.E6.tag K β d) =
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm β) (σ d) :=
  twistHom_pinnedX_eq_of_charTwo (CharP.cast_eq_zero K 2) σ hβ d

theorem twKill_F_mem_rootSpan [CharP K 2] (σ : K →+* K)
    {S T : Set (Fin TwistTag.E6.tag.rank → ℤ)} (hS : ∀ β ∈ S, IsRoot TwistTag.E6.tag β)
    (hST : ∀ β ∈ S, permLattice TwistTag.E6.perm β ∈ T) {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ rootSpan TwistTag.E6.tag K S) :
    twistHom TwistTag.E6 K σ g ∈ rootSpan TwistTag.E6.tag K T := by
  have hle : rootSpan TwistTag.E6.tag K S ≤
      (rootSpan TwistTag.E6.tag K T).comap (twistHom TwistTag.E6 K σ) := by
    refine iSup₂_le fun β hβ => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨d, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, twKill_F_pinnedX σ (hS β hβ)]
    exact classKill_pinnedX_mem (hST β hβ) _
  exact hle hg

theorem twKill_FF [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    {S : Set (Fin TwistTag.E6.tag.rank → ℤ)} (hS : ∀ β ∈ S, IsRoot TwistTag.E6.tag β)
    {g : ModGL TwistTag.E6.tag K} (hg : g ∈ rootSpan TwistTag.E6.tag K S) :
    twistHom TwistTag.E6 K σ (twistHom TwistTag.E6 K σ g) = g := by
  have hle : rootSpan TwistTag.E6.tag K S ≤ MonoidHom.eqLocus
      ((twistHom TwistTag.E6 K σ).comp (twistHom TwistTag.E6 K σ)) (MonoidHom.id _) := by
    refine iSup₂_le fun β hβ => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨d, rfl⟩
    change twistHom TwistTag.E6 K σ (twistHom TwistTag.E6 K σ (pinnedX TwistTag.E6.tag K β d)) =
      pinnedX TwistTag.E6.tag K β d
    rw [twKill_F_pinnedX σ (hS β hβ),
      twKill_F_pinnedX σ ((hS β hβ).permLattice TwistTag.E6.cartan_perm),
      permLattice_twistedE6_perm_perm, hσσ]
  exact hle hg

end Twist

@[expose] def twKillDeg (i : Fin TwistTag.E6.tag.rank) (v : Fin TwistTag.E6.tag.rank → ℤ) : ℤ :=
  ∑ l, if l = i ∨ l = TwistTag.E6.perm i then 0 else v l

@[expose] def twKillLev (i : Fin TwistTag.E6.tag.rank) (v : Fin TwistTag.E6.tag.rank → ℤ) : ℤ :=
  ∑ l, if l = i ∨ l = TwistTag.E6.perm i then v l else 0

theorem twKillDeg_add (i : Fin TwistTag.E6.tag.rank) (v w : Fin TwistTag.E6.tag.rank → ℤ) :
    twKillDeg i (v + w) = twKillDeg i v + twKillDeg i w := by
  simp only [twKillDeg, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem twKillLev_add (i : Fin TwistTag.E6.tag.rank) (v w : Fin TwistTag.E6.tag.rank → ℤ) :
    twKillLev i (v + w) = twKillLev i v + twKillLev i w := by
  simp only [twKillLev, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem twKillDeg_sub (i : Fin TwistTag.E6.tag.rank) (v w : Fin TwistTag.E6.tag.rank → ℤ) :
    twKillDeg i (v - w) = twKillDeg i v - twKillDeg i w := by
  simp only [twKillDeg, Pi.sub_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem twKillLev_sub (i : Fin TwistTag.E6.tag.rank) (v w : Fin TwistTag.E6.tag.rank → ℤ) :
    twKillLev i (v - w) = twKillLev i v - twKillLev i w := by
  simp only [twKillLev, Pi.sub_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem twKillDeg_nsmul (i : Fin TwistTag.E6.tag.rank) (m : ℕ) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    twKillDeg i (m • v) = m * twKillDeg i v := by
  simp only [twKillDeg, Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem twKillLev_nsmul (i : Fin TwistTag.E6.tag.rank) (m : ℕ) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    twKillLev i (m • v) = m * twKillLev i v := by
  simp only [twKillLev, Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem twKillDeg_single {i j : Fin TwistTag.E6.tag.rank} (hj : j = i ∨ j = TwistTag.E6.perm i) :
    twKillDeg i (Pi.single j 1) = 0 := by
  simp only [twKillDeg]
  refine Finset.sum_eq_zero fun l _ => ?_
  split_ifs with h
  · rfl
  · rw [Pi.single_eq_of_ne]
    rintro rfl
    exact h hj

theorem twKillLev_single {i j : Fin TwistTag.E6.tag.rank} (hj : j = i ∨ j = TwistTag.E6.perm i) :
    twKillLev i (Pi.single j 1) = 1 := by
  simp only [twKillLev]
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro l _ hl
    split_ifs <;> simp [Pi.single_eq_of_ne hl]
  · simp

theorem twKill_perm_eq_iff {i m : Fin TwistTag.E6.tag.rank} :
    TwistTag.E6.perm m = i ↔ m = TwistTag.E6.perm i := by
  constructor
  · rintro rfl
    rw [twistedE6_perm_perm]
  · rintro rfl
    rw [twistedE6_perm_perm]

theorem twKillDeg_permLattice (i : Fin TwistTag.E6.tag.rank) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    twKillDeg i (permLattice TwistTag.E6.perm v) = twKillDeg i v := by
  unfold twKillDeg
  rw [← Equiv.sum_comp TwistTag.E6.perm]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [permLattice, Function.comp_apply, twistedE6_perm_symm_apply, twistedE6_perm_perm,
    twKill_perm_eq_iff, TwistTag.E6.perm.injective.eq_iff, or_comm]

theorem twKillLev_permLattice (i : Fin TwistTag.E6.tag.rank) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    twKillLev i (permLattice TwistTag.E6.perm v) = twKillLev i v := by
  unfold twKillLev
  rw [← Equiv.sum_comp TwistTag.E6.perm]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [permLattice, Function.comp_apply, twistedE6_perm_symm_apply, twistedE6_perm_perm,
    twKill_perm_eq_iff, TwistTag.E6.perm.injective.eq_iff, or_comm]

theorem twKill_classKillPair_permLattice (i : Fin TwistTag.E6.tag.rank)
    (v : Fin TwistTag.E6.tag.rank → ℤ) :
    classKillPair i (permLattice TwistTag.E6.perm v) = classKillPair (TwistTag.E6.perm i) v :=
  coPair_permLattice_twistedE6 i v

theorem twKill_check_supp :
    ∀ i : Fin TwistTag.E6.tag.rank,
      ∀ k ∈ List.range TwistTag.E6.tag.rootCertificate.roots.length,
        0 < height (TwistTag.E6.tag.rootCertificate.root k) →
        (∀ l : Fin TwistTag.E6.tag.rank, l ≠ i → l ≠ TwistTag.E6.perm i →
          TwistTag.E6.tag.rootCertificate.root k l = 0) →
        List.ofFn (TwistTag.E6.tag.rootCertificate.root k) =
            List.ofFn (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) ∨
          List.ofFn (TwistTag.E6.tag.rootCertificate.root k) =
            List.ofFn (Pi.single (TwistTag.E6.perm i) 1 : Fin TwistTag.E6.tag.rank → ℤ) := by
  decide +kernel

theorem twKill_check_string :
    ∀ i : Fin TwistTag.E6.tag.rank, TwistTag.E6.perm i ≠ i →
      ∀ k ∈ List.range TwistTag.E6.tag.rootCertificate.roots.length,
        0 < height (TwistTag.E6.tag.rootCertificate.root k) →
        isRootB TwistTag.E6.tag (TwistTag.E6.tag.rootCertificate.root k - Pi.single i 1) = false →
        isRootB TwistTag.E6.tag (TwistTag.E6.tag.rootCertificate.root k -
          Pi.single (TwistTag.E6.perm i) 1) = false →
        isRootB TwistTag.E6.tag (TwistTag.E6.tag.rootCertificate.root k + Pi.single i 1) = true →
        isRootB TwistTag.E6.tag (TwistTag.E6.tag.rootCertificate.root k +
          Pi.single (TwistTag.E6.perm i) 1) = false →
        isRootB TwistTag.E6.tag (TwistTag.E6.tag.rootCertificate.root k + Pi.single i 1 +
            Pi.single (TwistTag.E6.perm i) 1) = false ∧
          isRootB TwistTag.E6.tag (TwistTag.E6.tag.rootCertificate.root k + Pi.single i 1 -
            Pi.single (TwistTag.E6.perm i) 1) = false := by
  decide +kernel

theorem twKill_check_square :
    ∀ i : Fin TwistTag.E6.tag.rank, TwistTag.E6.perm i ≠ i →
      ∀ k ∈ List.range TwistTag.E6.tag.rootCertificate.roots.length,
        0 < height (TwistTag.E6.tag.rootCertificate.root k) →
        isRootB TwistTag.E6.tag (TwistTag.E6.tag.rootCertificate.root k - Pi.single i 1) = false →
        isRootB TwistTag.E6.tag (TwistTag.E6.tag.rootCertificate.root k -
          Pi.single (TwistTag.E6.perm i) 1) = false →
        isRootB TwistTag.E6.tag (TwistTag.E6.tag.rootCertificate.root k + Pi.single i 1) = true →
        isRootB TwistTag.E6.tag (TwistTag.E6.tag.rootCertificate.root k +
          Pi.single (TwistTag.E6.perm i) 1) = true →
        List.ofFn (permLattice TwistTag.E6.perm (TwistTag.E6.tag.rootCertificate.root k)) =
            List.ofFn (TwistTag.E6.tag.rootCertificate.root k) ∧
          isRootB TwistTag.E6.tag (TwistTag.E6.tag.rootCertificate.root k + Pi.single i 1 +
            Pi.single (TwistTag.E6.perm i) 1) = true ∧
          isRootB TwistTag.E6.tag (TwistTag.E6.tag.rootCertificate.root k + Pi.single i 1 -
            Pi.single (TwistTag.E6.perm i) 1) = false ∧
          isRootB TwistTag.E6.tag (TwistTag.E6.tag.rootCertificate.root k - Pi.single i 1 +
            Pi.single (TwistTag.E6.perm i) 1) = false ∧
          isRootB TwistTag.E6.tag (TwistTag.E6.tag.rootCertificate.root k + Pi.single i 1 +
            Pi.single (TwistTag.E6.perm i) 1 + Pi.single i 1) = false ∧
          isRootB TwistTag.E6.tag (TwistTag.E6.tag.rootCertificate.root k + Pi.single i 1 +
            Pi.single (TwistTag.E6.perm i) 1 + Pi.single (TwistTag.E6.perm i) 1) = false := by
  decide +kernel

theorem twKill_check_pair :
    ∀ i : Fin TwistTag.E6.tag.rank, TwistTag.E6.perm i ≠ i →
      isRootB TwistTag.E6.tag (Pi.single i 1 + Pi.single (TwistTag.E6.perm i) 1) = false := by
  decide +kernel

end CFSG.SeitzReduction
