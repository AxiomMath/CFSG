module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLLift
public import CFSG.Open.StatedDefs
import CFSG.Open.StatedAPI
public import CFSG.RankThree.PartOne.CTP.SeitzDiag
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CriticalSubgroupLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection2.EndFieldRep
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ConjugateRep

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open Matrix CFSG.HardMathSupport.Timmesfeld.LinearRank

variable {Ω : Type} [Group Ω] {S : Subgroup Ω}
variable {n : ℕ} {K : Type} [Field K] {H : Subgroup (GL (Fin n) K)}

section ActsAs

@[expose] def ActsAs (φ : ↥H →* Ω) (x : Ω) (A : GL (Fin n) K) : Prop :=
  ∀ k : ↥H, ∃ k' : ↥H, (k' : GL (Fin n) K) = A * k * A⁻¹ ∧ φ k' = x * φ k * x⁻¹

variable {φ : ↥H →* Ω}

theorem actsAs_one : ActsAs φ 1 1 := fun k => ⟨k, by simp, by simp⟩

theorem ActsAs.mul {x y : Ω} {A A' : GL (Fin n) K} (h : ActsAs φ x A) (h' : ActsAs φ y A') :
    ActsAs φ (x * y) (A * A') := by
  intro k
  obtain ⟨k₁, hk₁, hφ₁⟩ := h' k
  obtain ⟨k₂, hk₂, hφ₂⟩ := h k₁
  refine ⟨k₂, ?_, ?_⟩
  · rw [hk₂, hk₁]
    group
  · rw [hφ₂, hφ₁]
    group

theorem ActsAs.inv {x : Ω} {A : GL (Fin n) K}
    (hA : A⁻¹ ∈ Subgroup.normalizer (H : Set (GL (Fin n) K))) (h : ActsAs φ x A) :
    ActsAs φ x⁻¹ A⁻¹ := by
  intro k
  have hk : A⁻¹ * k * A⁻¹⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hA k).1 k.2
  refine ⟨⟨_, hk⟩, rfl, ?_⟩
  obtain ⟨k'', hk'', hφ⟩ := h ⟨_, hk⟩
  have he : k'' = k := Subtype.ext (by rw [hk'']; simp only; group)
  rw [he] at hφ
  rw [hφ]
  group

theorem ActsAs.mul_center {x : Ω} {A c : GL (Fin n) K} (h : ActsAs φ x A)
    (hc : c ∈ Subgroup.center (GL (Fin n) K)) : ActsAs φ x (A * c) := by
  intro k
  obtain ⟨k', hk', hφ⟩ := h k
  refine ⟨k', ?_, hφ⟩
  have hck : (k : GL (Fin n) K) * c = c * k := Subgroup.mem_center_iff.1 hc k
  calc (k' : GL (Fin n) K) = A * ((k : GL (Fin n) K) * c) * c⁻¹ * A⁻¹ := by rw [hk']; group
    _ = A * (c * k) * c⁻¹ * A⁻¹ := by rw [hck]
    _ = A * c * k * (A * c)⁻¹ := by group

theorem actsAs_center_iff {x : Ω} {c : GL (Fin n) K}
    (hc : c ∈ Subgroup.center (GL (Fin n) K)) :
    ActsAs φ x c ↔ ∀ k : ↥H, x * φ k = φ k * x := by
  constructor
  · intro h k
    obtain ⟨k', hk', hφ⟩ := h k
    have he : k' = k := Subtype.ext (by
      rw [hk', ← (Subgroup.mem_center_iff.1 hc k)]
      group)
    rw [he] at hφ
    calc x * φ k = x * φ k * x⁻¹ * x := by group
      _ = φ k * x := by rw [← hφ]
  · intro h k
    refine ⟨k, ?_, ?_⟩
    · rw [← (Subgroup.mem_center_iff.1 hc k)]
      group
    · rw [h k]
      group

end ActsAs

section InnerDiag

variable (φ : ↥H →* Ω) (Y : Subgroup (GL (Fin n) K))
  (hY : Y ≤ Subgroup.normalizer (H : Set (GL (Fin n) K))) (B : Subgroup Ω)

@[expose] def innerDiag : Subgroup Ω where
  carrier := {x | x ∈ B ∧ ∃ A ∈ Y, ActsAs φ x A}
  one_mem' := ⟨B.one_mem, 1, Y.one_mem, actsAs_one⟩
  mul_mem' := fun {x y} hx hy => by
    obtain ⟨hxB, A, hA, hxA⟩ := hx
    obtain ⟨hyB, A', hA', hyA'⟩ := hy
    exact ⟨B.mul_mem hxB hyB, A * A', Y.mul_mem hA hA', hxA.mul hyA'⟩
  inv_mem' := fun {x} hx => by
    obtain ⟨hxB, A, hA, hxA⟩ := hx
    exact ⟨B.inv_mem hxB, A⁻¹, Y.inv_mem hA, hxA.inv (hY (Y.inv_mem hA))⟩

variable {φ Y hY B}

theorem mem_innerDiag {x : Ω} : x ∈ innerDiag φ Y hY B ↔ x ∈ B ∧ ∃ A ∈ Y, ActsAs φ x A :=
  Iff.rfl

theorem innerDiag_le : innerDiag φ Y hY B ≤ B := fun _ hx => hx.1

theorem inf_centralizer_le_innerDiag (hφS : φ.range = S) :
    B ⊓ Subgroup.centralizer (S : Set Ω) ≤ innerDiag φ Y hY B := by
  rintro x ⟨hxB, hxC⟩
  refine ⟨hxB, 1, Y.one_mem, (actsAs_center_iff (one_mem _)).2 fun k => ?_⟩
  have hk : φ k ∈ S := hφS ▸ ⟨k, rfl⟩
  exact ((Subgroup.mem_centralizer_iff.1 hxC) _ hk).symm

theorem inv_mul_mem_center_of_actsAs (hYN : Y ≤ Subgroup.normalizer (H : Set (GL (Fin n) K)))
    (hcent : ∀ c ∈ Y, (∀ k ∈ H, c * k * c⁻¹ * k⁻¹ ∈ StatedScalars (Fin n) K) →
      c ∈ Subgroup.center (GL (Fin n) K))
    (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf H) {x : Ω} {A A' : GL (Fin n) K}
    (hA : A ∈ Y) (hA' : A' ∈ Y) (h : ActsAs φ x A) (h' : ActsAs φ x A') :
    A⁻¹ * A' ∈ Subgroup.center (GL (Fin n) K) := by
  have h1 : ActsAs φ 1 (A⁻¹ * A') := by
    have := (h.inv (hYN (Y.inv_mem hA))).mul h'
    rwa [inv_mul_cancel] at this
  refine hcent _ (Y.mul_mem (Y.inv_mem hA) hA') fun k hk => ?_
  obtain ⟨k', hk', hφ⟩ := h1 ⟨k, hk⟩
  rw [one_mul, inv_one, mul_one] at hφ
  have hker : k' * ⟨k, hk⟩⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, mul_inv_cancel]
  have := hφk hker
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hk'] at this
  exact this

variable (hφS : φ.range = S)
  (hcent : ∀ c ∈ Y, (∀ k ∈ H, c * k * c⁻¹ * k⁻¹ ∈ StatedScalars (Fin n) K) →
      c ∈ Subgroup.center (GL (Fin n) K))
  (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf H)

include hcent hφk in
@[expose] noncomputable def innerDiagHom : ↥(innerDiag φ Y hY B) →* PGL n K :=
  MonoidHom.mk' (fun x => pglMk n K x.2.2.choose) fun x y => by
    have hx := x.2.2.choose_spec
    have hy := y.2.2.choose_spec
    have hxy := (x * y).2.2.choose_spec
    have hc := inv_mul_mem_center_of_actsAs hY hcent hφk hxy.1 (Y.mul_mem hx.1 hy.1) hxy.2
      (hx.2.mul hy.2)
    have h1 : pglMk n K ((x * y).2.2.choose⁻¹ * (x.2.2.choose * y.2.2.choose)) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hc
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [h1, map_mul]

theorem innerDiagHom_spec (x : ↥(innerDiag φ Y hY B)) :
    ∃ A ∈ Y, ActsAs φ x A ∧ innerDiagHom hcent hφk x = pglMk n K A :=
  ⟨_, x.2.2.choose_spec.1, x.2.2.choose_spec.2, rfl⟩

theorem actsAs_of_pglMk_eq {x : ↥(innerDiag φ Y hY B)} {A : GL (Fin n) K}
    (hA : pglMk n K A = innerDiagHom hcent hφk x) : ActsAs φ x A := by
  obtain ⟨A₀, -, hA₀, hψ⟩ := innerDiagHom_spec hcent hφk x
  have h1 : pglMk n K A₀ = pglMk n K A := hψ.symm.trans hA.symm
  have h2 : A₀⁻¹ * A ∈ Subgroup.center (GL (Fin n) K) := QuotientGroup.eq.1 h1
  have : A = A₀ * (A₀⁻¹ * A) := by group
  rw [this]
  exact hA₀.mul_center h2

include hφS in
theorem innerDiagHom_eq_one_iff (x : ↥(innerDiag φ Y hY B)) :
    innerDiagHom hcent hφk x = 1 ↔ (x : Ω) ∈ Subgroup.centralizer (S : Set Ω) := by
  obtain ⟨A, hAY, hA, hψ⟩ := innerDiagHom_spec hcent hφk x
  rw [hψ, pglMk_eq_one_iff, ← mem_center_iff]
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff]
    rintro _ hs
    rw [← hφS] at hs
    obtain ⟨k, rfl⟩ := hs
    exact ((actsAs_center_iff hc).1 hA k).symm
  · intro hx
    have h1 : ActsAs φ (x : Ω) 1 := (actsAs_center_iff (one_mem _)).2 fun k => by
      have hk : φ k ∈ S := hφS ▸ ⟨k, rfl⟩
      exact ((Subgroup.mem_centralizer_iff.1 hx) _ hk).symm
    have h2 := inv_mul_mem_center_of_actsAs hY hcent hφk hAY Y.one_mem hA h1
    rw [mul_one] at h2
    have := Subgroup.inv_mem _ h2
    rwa [inv_inv] at this

theorem innerDiagHom_range_le :
    (innerDiagHom (hY := hY) (B := B) hcent hφk).range ≤ Y.map (pglMk n K) := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨A, hAY, -, hψ⟩ := innerDiagHom_spec hcent hφk x
  exact ⟨A, hAY, hψ.symm⟩

include hφS in
theorem card_innerDiag [Finite Ω] :
    Nat.card ↥(innerDiag φ Y hY B) =
      Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) *
        Nat.card (innerDiagHom (hY := hY) (B := B) hcent hφk).range := by
  have h := Subgroup.card_ker_mul_card_range (innerDiagHom (hY := hY) (B := B) hcent hφk)
  have hker : Nat.card (innerDiagHom (hY := hY) (B := B) hcent hφk).ker =
      Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) := by
    have hle := inf_centralizer_le_innerDiag (Y := Y) (hY := hY) (B := B) hφS
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    have heq : (innerDiagHom (hY := hY) (B := B) hcent hφk).ker =
        (B ⊓ Subgroup.centralizer (S : Set Ω)).subgroupOf (innerDiag φ Y hY B) := by
      ext x
      rw [MonoidHom.mem_ker, innerDiagHom_eq_one_iff hφS hcent hφk, Subgroup.mem_subgroupOf,
        Subgroup.mem_inf]
      exact ⟨fun h => ⟨innerDiag_le x.2, h⟩, fun h => h.2⟩
    rw [heq]
  rw [← h, hker]

include hφS in
theorem exists_theta_of_lift {A' : Subgroup (GL (Fin n) K)}
    (hA'Z : A' ⊓ Subgroup.center (GL (Fin n) K) = ⊥)
    (hA'E : A'.map (pglMk n K) = (innerDiagHom (hY := hY) (B := B) hcent hφk).range) :
    ∃ θ : ↥(innerDiag φ Y hY B) →* GL (Fin n) K, θ.range = A' ∧
      (∀ x : ↥(innerDiag φ Y hY B), pglMk n K (θ x) = innerDiagHom hcent hφk x) ∧
      (∀ x : ↥(innerDiag φ Y hY B), ActsAs φ x (θ x)) ∧
      ∀ x : ↥(innerDiag φ Y hY B), θ x = 1 ↔ (x : Ω) ∈ Subgroup.centralizer (S : Set Ω) := by
  set ψ := innerDiagHom (hY := hY) (B := B) hcent hφk with hψ
  set f : ↥A' →* PGL n K := (pglMk n K).comp A'.subtype with hf
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, Subgroup.coe_subtype,
      pglMk_eq_one_iff, ← mem_center_iff] at ha
    have : (a : GL (Fin n) K) ∈ A' ⊓ Subgroup.center (GL (Fin n) K) := ⟨a.2, ha⟩
    rw [hA'Z, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (Subtype.ext this)
  have hfr : f.range = ψ.range := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype, hA'E]
  set e := MonoidHom.ofInjective hfinj with he
  have hmem : ∀ x, ψ x ∈ f.range := fun x => hfr ▸ ⟨x, rfl⟩
  set θ₀ : ↥(innerDiag φ Y hY B) →* ↥A' :=
    e.symm.toMonoidHom.comp (ψ.codRestrict f.range hmem) with hθ₀
  have hθ₀f : ∀ x, f (θ₀ x) = ψ x := fun x => by
    have h1 := MonoidHom.ofInjective_apply hfinj (x := e.symm ⟨ψ x, hmem x⟩)
    rw [← he, MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  refine ⟨A'.subtype.comp θ₀, ?_, fun x => hθ₀f x, fun x => actsAs_of_pglMk_eq hcent hφk
    (hθ₀f x), fun x => ?_⟩
  · ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact (θ₀ x).2
    · intro ha
      obtain ⟨x, hx⟩ : f ⟨a, ha⟩ ∈ ψ.range := hfr ▸ ⟨⟨a, ha⟩, rfl⟩
      refine ⟨x, ?_⟩
      have h1 : θ₀ x = ⟨a, ha⟩ := hfinj (by rw [hθ₀f, hx])
      exact congrArg Subtype.val h1
  · rw [← innerDiagHom_eq_one_iff hφS hcent hφk, ← hθ₀f, MonoidHom.comp_apply,
      Subgroup.coe_subtype]
    constructor
    · intro h
      rw [hf, MonoidHom.comp_apply, Subgroup.coe_subtype, h, map_one]
    · intro h
      have : θ₀ x = 1 := hfinj (by rw [h, map_one])
      rw [this, OneMemClass.coe_one]

end InnerDiag

section Split

theorem eq_or_exists_zpowers_of_isCyclic [Finite Ω] {p : ℕ} (hp : p.Prime) {B B₁ : Subgroup Ω}
    (hB : IsElemAbelian p B) (hB₁ : B₁ ≤ B) {C : Type*} [Group C] [IsCyclic C] (f : ↥B →* C)
    (hf : ∀ x : ↥B, f x = 1 ↔ (x : Ω) ∈ B₁) :
    B₁ = B ∨ ∃ b ∈ B, b ∉ B₁ ∧ B = B₁ ⊔ Subgroup.zpowers b ∧
      Subgroup.zpowers b ⊓ B₁ = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hle : B ≤ B₁
  · exact Or.inl (le_antisymm hB₁ hle)
  right
  obtain ⟨b, hbB, hbB₁⟩ := Set.not_subset.1 hle
  have hbp : b ^ p = 1 := hB.2 b hbB
  have hfb : f ⟨b, hbB⟩ ≠ 1 := fun h => hbB₁ ((hf _).1 h)
  have hfbp : f ⟨b, hbB⟩ ^ p = 1 := by
    rw [← map_pow, show (⟨b, hbB⟩ : ↥B) ^ p = 1 from Subtype.ext hbp, map_one]
  have hord : orderOf (f ⟨b, hbB⟩) = p := orderOf_eq_prime hfbp hfb
  have hpow : ∀ x : ↥B, ∃ m : ℤ, f x = f ⟨b, hbB⟩ ^ m := by
    intro x
    haveI : Finite ↥f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    have hexp : Monoid.exponent ↥f.range ∣ p := by
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_
      obtain ⟨z, hz⟩ := y.2
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, ← hz, ← map_pow, show z ^ p = 1 from Subtype.ext (hB.2 z z.2),
        map_one, OneMemClass.coe_one]
    have hcard : Nat.card ↥f.range ∣ p := by
      rw [← IsCyclic.exponent_eq_card]
      exact hexp
    set y : ↥f.range := ⟨_, ⟨⟨b, hbB⟩, rfl⟩⟩
    have hy : orderOf y = p := by rw [← Subgroup.orderOf_coe]; exact hord
    have hzc : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, hy]
    have hge : p ≤ Nat.card ↥f.range := hzc ▸ Subgroup.card_le_card_group _
    have heq : Nat.card ↥f.range = p := le_antisymm (Nat.le_of_dvd hp.pos hcard) hge
    have htop : Subgroup.zpowers y = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hzc, heq])
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1
      (htop ▸ Subgroup.mem_top (⟨f x, ⟨x, rfl⟩⟩ : ↥f.range))
    refine ⟨m, ?_⟩
    have h1 := congrArg Subtype.val hm
    rw [SubgroupClass.coe_zpow] at h1
    exact h1.symm
  refine ⟨b, hbB, hbB₁, le_antisymm (fun x hx => ?_)
    (sup_le hB₁ (Subgroup.zpowers_le.2 hbB)), ?_⟩
  · obtain ⟨m, hm⟩ := hpow ⟨x, hx⟩
    have h1 : x * b ^ (-m) ∈ B₁ := by
      have := (hf (⟨x, hx⟩ * ⟨b, hbB⟩ ^ (-m))).1 (by
        rw [map_mul, map_zpow, hm, ← _root_.zpow_add, add_neg_cancel, zpow_zero])
      simpa using this
    have hx' : x = x * b ^ (-m) * b ^ m := by group
    rw [hx']
    exact Subgroup.mul_mem_sup h1 (Subgroup.zpow_mem_zpowers b m)
  · rw [eq_bot_iff]
    rintro y ⟨hy, hyB₁⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [Subgroup.mem_bot]
    have h1 : f ⟨b, hbB⟩ ^ m = 1 := by
      have := (hf (⟨b, hbB⟩ ^ m)).2 (by simpa using hyB₁)
      rwa [map_zpow] at this
    rw [← orderOf_dvd_iff_zpow_eq_one, hord] at h1
    obtain ⟨k, rfl⟩ := h1
    rw [_root_.zpow_mul, zpow_natCast, hbp, _root_.one_zpow]

end Split

section Perfect

theorem eq_of_inv_mul_mem_centralizer {G : Type*} [Group G] (hG : commutator G = ⊤)
    (f₁ f₂ : G →* Ω) (h₁ : ∀ g, f₁ g ∈ S) (h₂ : ∀ g, f₂ g ∈ S)
    (h : ∀ g, (f₁ g)⁻¹ * f₂ g ∈ Subgroup.centralizer (S : Set Ω)) : f₁ = f₂ := by
  have hmem : ∀ g, (f₁ g)⁻¹ * f₂ g ∈ S ⊓ Subgroup.centralizer (S : Set Ω) := fun g =>
    ⟨S.mul_mem (S.inv_mem (h₁ g)) (h₂ g), h g⟩
  have hcomm : ∀ a ∈ S ⊓ Subgroup.centralizer (S : Set Ω),
      ∀ b ∈ S ⊓ Subgroup.centralizer (S : Set Ω), a * b = b * a := fun a ha b hb =>
    ((Subgroup.mem_centralizer_iff.1 hb.2) a ha.1)
  let δ : G →* ↥(S ⊓ Subgroup.centralizer (S : Set Ω)) :=
    { toFun := fun g => ⟨_, hmem g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g g' => Subtype.ext (by
        show (f₁ (g * g'))⁻¹ * f₂ (g * g') = (f₁ g)⁻¹ * f₂ g * ((f₁ g')⁻¹ * f₂ g')
        have hc : (f₁ g)⁻¹ * f₂ g * (f₁ g')⁻¹ = (f₁ g')⁻¹ * ((f₁ g)⁻¹ * f₂ g) :=
          ((Subgroup.mem_centralizer_iff.1 (h g)) _ (S.inv_mem (h₁ g'))).symm
        rw [map_mul, map_mul]
        calc (f₁ g * f₁ g')⁻¹ * (f₂ g * f₂ g') = (f₁ g')⁻¹ * ((f₁ g)⁻¹ * f₂ g) * f₂ g' := by
              group
          _ = (f₁ g)⁻¹ * f₂ g * (f₁ g')⁻¹ * f₂ g' := by rw [hc]
          _ = (f₁ g)⁻¹ * f₂ g * ((f₁ g')⁻¹ * f₂ g') := by group) }
  have hker : commutator G ≤ δ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (hcomm _ (δ a).2 _ (δ b).2)
  rw [hG] at hker
  refine MonoidHom.ext fun g => ?_
  have h1 : δ g = 1 := hker (Subgroup.mem_top g)
  have h2 : (f₁ g)⁻¹ * f₂ g = 1 := congrArg Subtype.val h1
  exact (inv_mul_eq_one.1 h2)

end Perfect

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
