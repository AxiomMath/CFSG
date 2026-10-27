module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerAffine
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSingerAffine
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.ProperTwoGeneratedCore.CosetNormalizer
open CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger
open scoped IsMulCommutative

variable {G : Type*} [Group G]

@[expose] def involutionDisplacement (u x : G) : G := u * (x * u * x⁻¹)

theorem mul_comm_of_mul_self_eq_one {U : Subgroup G} (hUsq : ∀ x ∈ U, x * x = 1) {x y : G}
    (hx : x ∈ U) (hy : y ∈ U) : x * y = y * x := by
  have hxy := hUsq (x * y) (U.mul_mem hx hy)
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_left (hUsq x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_left (hUsq y hy)
  have h : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_left hxy
  rw [mul_inv_rev, hx', hy'] at h
  exact h.symm

theorem le_normalizer_centralizer {U : Subgroup G} :
    Subgroup.normalizer (U : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) := by
  have key : ∀ n ∈ Subgroup.normalizer (U : Set G), ∀ x ∈ Subgroup.centralizer (U : Set G),
      n * x * n⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
    intro n hn x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro b hb
    have hb' : n⁻¹ * b * n⁻¹⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) b).mp hb
    rw [inv_inv] at hb'
    have h := hx _ hb'
    calc b * (n * x * n⁻¹) = n * ((n⁻¹ * b * n) * x) * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * b * n)) * n⁻¹ := by rw [h]
      _ = n * x * n⁻¹ * b := by group
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key n hn x, fun hx => ?_⟩
  have h := key n⁻¹ (Subgroup.inv_mem _ hn) _ hx
  have h2 : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
  rwa [h2] at h

theorem mem_translate_self (U : Subgroup G) (u : G) :
    u ∈ (fun v : G => u * v) '' (U : Set G) :=
  ⟨1, U.one_mem, mul_one u⟩

theorem conj_mem_translate_of_mem_normalizer {U : Subgroup G} {u n : G}
    (hn : n ∈ Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))) :
    n * u * n⁻¹ ∈ (fun v : G => u * v) '' (U : Set G) :=
  (hn u).mp (mem_translate_self U u)

theorem involutionDisplacement_mem {U : Subgroup G} {u n : G} (hu : u * u = 1)
    (hn : n ∈ Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))) :
    involutionDisplacement u n ∈ U := by
  obtain ⟨v, hv, hvn⟩ := conj_mem_translate_of_mem_normalizer hn
  change u * (n * u * n⁻¹) ∈ U
  rw [← hvn, ← mul_assoc, hu, one_mul]
  exact hv

theorem conj_eq_mul_involutionDisplacement {u : G} (hu : u * u = 1) (n : G) :
    n * u * n⁻¹ = u * involutionDisplacement u n := by
  rw [involutionDisplacement, ← mul_assoc, hu, one_mul]

theorem involutionDisplacement_mul {U : Subgroup G} {u x y : G} (hu : u * u = 1)
    (hx : x ∈ Subgroup.centralizer (U : Set G)) (hy : involutionDisplacement u y ∈ U) :
    involutionDisplacement u (x * y) = involutionDisplacement u x * involutionDisplacement u y := by
  have hc : x * involutionDisplacement u y = involutionDisplacement u y * x :=
    (Subgroup.mem_centralizer_iff.mp hx _ hy).symm
  have hyu := conj_eq_mul_involutionDisplacement hu y
  calc involutionDisplacement u (x * y) = u * (x * (y * u * y⁻¹) * x⁻¹) := by
        simp only [involutionDisplacement, mul_inv_rev]; group
    _ = u * (x * u * x⁻¹) * (x * involutionDisplacement u y * x⁻¹) := by rw [hyu]; group
    _ = involutionDisplacement u x * involutionDisplacement u y := by
        rw [hc, mul_inv_cancel_right]; rfl

theorem involutionDisplacement_eq_one_iff {u : G} (hu : u * u = 1) (x : G) :
    involutionDisplacement u x = 1 ↔ x * u = u * x := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu
  constructor
  · intro h
    have h1 : x * u * x⁻¹ = u := by
      have := eq_inv_of_mul_eq_one_right h
      rwa [huinv] at this
    calc x * u = x * u * x⁻¹ * x := by group
      _ = u * x := by rw [h1]
  · intro h
    change u * (x * u * x⁻¹) = 1
    rw [h, mul_inv_cancel_right, hu]

theorem involutionDisplacement_conj {u a : G} (ha : a * u = u * a) (x : G) :
    involutionDisplacement u (a * x * a⁻¹) = a * involutionDisplacement u x * a⁻¹ := by
  have ha' : a⁻¹ * u = u * a⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ha, mul_inv_cancel_right]
  simp only [involutionDisplacement, mul_inv_rev, inv_inv]
  calc u * (a * x * a⁻¹ * u * (a * (x⁻¹ * a⁻¹))) = u * a * x * (a⁻¹ * u) * a * x⁻¹ * a⁻¹ := by
        group
    _ = a * (u * (x * u * x⁻¹)) * a⁻¹ := by
        rw [ha', ← ha]; group

theorem sup_le_translate_normalizer {U : Subgroup G} {u : G}
    (hcomm : ∀ x ∈ U, Commute u x) (hUsq : ∀ x ∈ U, x * x = 1) :
    Subgroup.zpowers u ⊔ U ≤ Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) := by
  have hcent : ∀ g : G, (∀ x ∈ (fun v : G => u * v) '' (U : Set G), g * x = x * g) →
      g ∈ Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) := fun g hg =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (hg x hx).symm)
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le]
    apply hcent
    rintro _ ⟨v, hv, rfl⟩
    change u * (u * v) = u * v * u
    rw [mul_assoc, (hcomm v hv).eq]
  · intro b hb
    apply hcent
    rintro _ ⟨v, hv, rfl⟩
    change b * (u * v) = u * v * b
    rw [← mul_assoc, ← (hcomm b hb).eq, mul_assoc, mul_assoc,
      mul_comm_of_mul_self_eq_one hUsq hb hv]

theorem translation_iff_mem_centralizer {U : Subgroup G} [IsElementaryAbelian 2 U] {u : G}
    (hu : u * u = 1)
    (hcomm : ∀ x ∈ U, Commute u x)
    (j : Additive U ≃ ((fun v : G => u * v) '' (U : Set G)))
    (hj : ∀ v : U, (j (Additive.ofMul v) : G) = u * v)
    (n : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))) :
    (∃ g ∈ translationGroup (Additive U),
        cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G)) n = j.permCongr g.toEquiv) ↔
      (n : G) ∈ Subgroup.centralizer (U : Set G) := by
  have hNU := involution_translate_normalizer_le_unit_normalizer U u hu hcomm
  constructor
  · rintro ⟨g, hg, hng⟩
    obtain ⟨w, rfl⟩ := mem_translationGroup.mp hg
    have hval : ∀ v : U, (n : G) * (u * v) * (n : G)⁻¹ = u * ((Additive.toMul w : U) * v) := by
      intro v
      have h := congrArg (fun σ : Equiv.Perm _ => ((σ (j (Additive.ofMul v)) : _) : G)) hng
      simp only [cosetNormalizerPerm_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply,
        AffineEquiv.coe_toEquiv, AffineEquiv.constVAdd_apply, vadd_eq_add, hj] at h
      have hw : w + Additive.ofMul v = Additive.ofMul (Additive.toMul w * v) := rfl
      rw [h, hw, hj, Subgroup.coe_mul]
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    have h1 := hval ⟨x, hx⟩
    have h0 := hval 1
    simp only [OneMemClass.coe_one, mul_one] at h0
    have : (n : G) * x * (n : G)⁻¹ = x := by
      have hsplit : (n : G) * (u * x) * (n : G)⁻¹ =
          ((n : G) * u * (n : G)⁻¹) * ((n : G) * x * (n : G)⁻¹) := by group
      rw [hsplit, h0] at h1
      simpa only [mul_assoc, mul_right_inj] using h1
    calc x * (n : G) = (n : G) * x * (n : G)⁻¹ * n := by rw [this]
      _ = n * x := by group
  · intro hn
    have hθ := involutionDisplacement_mem hu n.2
    refine ⟨AffineEquiv.constVAdd (ZMod 2) (Additive U)
      (Additive.ofMul ⟨involutionDisplacement u n, hθ⟩),
      mem_translationGroup.mpr ⟨_, rfl⟩, ?_⟩
    apply Equiv.ext
    intro x
    obtain ⟨v, rfl⟩ := j.surjective x
    apply Subtype.ext
    obtain ⟨v, rfl⟩ := Additive.ofMul.surjective v
    simp only [cosetNormalizerPerm_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply,
      AffineEquiv.coe_toEquiv, AffineEquiv.constVAdd_apply, vadd_eq_add, ← ofMul_mul, hj,
      Subgroup.coe_mul]
    have hc : (n : G) * v * (n : G)⁻¹ = v := by
      rw [(Subgroup.mem_centralizer_iff.mp hn v v.2).symm, mul_inv_cancel_right]
    calc (n : G) * (u * v) * (n : G)⁻¹ = ((n : G) * u * (n : G)⁻¹) * ((n : G) * v * (n : G)⁻¹) := by
          group
      _ = u * (involutionDisplacement u n * v) := by
          rw [hc, conj_eq_mul_involutionDisplacement hu, mul_assoc]

theorem exists_displacement_eq_of_translations {U : Subgroup G} [IsElementaryAbelian 2 U] {u : G}
    (hu : u * u = 1)
    (hcomm : ∀ x ∈ U, Commute u x)
    (j : Additive U ≃ ((fun v : G => u * v) '' (U : Set G)))
    (hj : ∀ v : U, (j (Additive.ofMul v) : G) = u * v)
    (htr : ∀ g ∈ translationGroup (Additive U), j.permCongr g.toEquiv ∈
      (cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G))).range) :
    ∀ b ∈ U, ∃ x ∈ Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) ⊓
      Subgroup.centralizer (U : Set G), involutionDisplacement u x = b := by
  intro b hb
  obtain ⟨n, hn⟩ := htr _ (mem_translationGroup.mpr ⟨Additive.ofMul ⟨b, hb⟩, rfl⟩)
  have hnC := (translation_iff_mem_centralizer hu hcomm j hj n).mp ⟨_,
    mem_translationGroup.mpr ⟨Additive.ofMul ⟨b, hb⟩, rfl⟩, hn⟩
  refine ⟨n, ⟨n.2, hnC⟩, ?_⟩
  have h := congrArg (fun σ : Equiv.Perm _ => ((σ (j (Additive.ofMul 1)) : _) : G)) hn
  simp only [cosetNormalizerPerm_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    AffineEquiv.coe_toEquiv, AffineEquiv.constVAdd_apply, vadd_eq_add, ← ofMul_mul, hj,
    mul_one, OneMemClass.coe_one] at h
  change u * ((n : G) * u * (n : G)⁻¹) = b
  rw [h, ← mul_assoc, hu, one_mul]

@[expose] def translationDisplacementHom {U : Subgroup G} {u : G} (hu : u * u = 1) :
    ↥(Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) ⊓
      Subgroup.centralizer (U : Set G)) →* U where
  toFun x := ⟨involutionDisplacement u x, involutionDisplacement_mem hu x.2.1⟩
  map_one' := Subtype.ext (by simp [involutionDisplacement, hu])
  map_mul' x y := Subtype.ext (involutionDisplacement_mul hu x.2.2
    (involutionDisplacement_mem hu y.2.1))

theorem mul_self_eq_one_of_mem_sup {U : Subgroup G} {u : G} (hu : u * u = 1)
    (hcomm : ∀ x ∈ U, Commute u x) (hUsq : ∀ x ∈ U, x * x = 1) {x : G}
    (hx : x ∈ Subgroup.zpowers u ⊔ U) : x * x = 1 := by
  rw [Subgroup.zpowers_eq_closure, mem_closure_singleton_sup_iff hu hcomm] at hx
  rcases hx with hx | ⟨v, hv, rfl⟩
  · exact hUsq x hx
  · calc u * v * (u * v) = u * (v * u) * v := by group
      _ = u * u * (v * v) := by rw [← (hcomm v hv).eq]; group
      _ = 1 := by rw [hu, hUsq v hv, one_mul]

theorem translation_subgroup_structure [Finite G] {U : Subgroup G} {u : G} (hu : u * u = 1)
    (hcomm : ∀ x ∈ U, Commute u x) (hUsq : ∀ x ∈ U, x * x = 1) (huU : u ∉ U)
    (htr : ∀ b ∈ U, ∃ x ∈ Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) ⊓
      Subgroup.centralizer (U : Set G), involutionDisplacement u x = b)
    (hE : Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (U : Set G) ≤
      Subgroup.zpowers u ⊔ U) :
    Subgroup.zpowers u ⊔ U ≤ Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) ⊓
        Subgroup.centralizer (U : Set G) ∧
      Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) ⊓
          Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer ({u} : Set G) =
        Subgroup.zpowers u ⊔ U ∧
      Nat.card (Subgroup.zpowers u ⊔ U : Subgroup G) = 2 * Nat.card U ∧
      Nat.card (Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) ⊓
          Subgroup.centralizer (U : Set G) : Subgroup G) = 2 * Nat.card U ^ 2 ∧
      (∀ x ∈ Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) ⊓
          Subgroup.centralizer (U : Set G), x * x ∈ U) ∧
      ∀ x ∈ Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) ⊓
          Subgroup.centralizer (U : Set G),
        ∀ y ∈ Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) ⊓
          Subgroup.centralizer (U : Set G), x * y * x⁻¹ * y⁻¹ ∈ U := by
  set Q := Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) ⊓
    Subgroup.centralizer (U : Set G) with hQ
  have huC : u ∈ Subgroup.centralizer (U : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => (hcomm x hx).symm.eq
  have hUC : U ≤ Subgroup.centralizer (U : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => mul_comm_of_mul_self_eq_one hUsq hy hx
  have hEC : Subgroup.zpowers u ⊔ U ≤ Subgroup.centralizer ({u} : Set G) := by
    refine sup_le ?_ fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx).symm.eq
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hEQ : Subgroup.zpowers u ⊔ U ≤ Q :=
    le_inf (sup_le_translate_normalizer hcomm hUsq)
      (sup_le (Subgroup.zpowers_le.mpr huC) hUC)
  have hQE : Q ⊓ Subgroup.centralizer ({u} : Set G) = Subgroup.zpowers u ⊔ U := by
    apply le_antisymm
    · rintro x ⟨⟨-, hxU⟩, hxu⟩
      exact hE ⟨hxu, hxU⟩
    · exact le_inf hEQ hEC
  have hu1 : u ≠ 1 := fun h => huU (h ▸ U.one_mem)
  have horder : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu) hu1
  have hEcard : Nat.card (Subgroup.zpowers u ⊔ U : Subgroup G) = 2 * Nat.card U := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer, Nat.card_zpowers,
      horder]
    · intro x hx
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((hcomm x hx).zpow_left k).eq
    · rw [Subgroup.disjoint_def]
      intro x hx hxU
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hk : u ^ k = u ^ (k % 2) := by
        rw [← zpow_mod_orderOf, horder]; rfl
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · rw [hk, h0, zpow_zero]
      · rw [hk, h1, zpow_one] at hxU
        exact absurd hxU huU
  let θ := translationDisplacementHom (U := U) hu
  have hθsurj : Function.Surjective θ := by
    rintro ⟨b, hb⟩
    obtain ⟨x, hx, hxb⟩ := htr b hb
    exact ⟨⟨x, hx⟩, Subtype.ext hxb⟩
  have hker : θ.ker = (Subgroup.centralizer ({u} : Set G)).subgroupOf Q := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    change (⟨involutionDisplacement u x, _⟩ : U) = 1 ↔ _
    rw [← Subtype.coe_inj, OneMemClass.coe_one, involutionDisplacement_eq_one_iff hu]
  have hkercard : Nat.card θ.ker = 2 * Nat.card U := by
    rw [hker, ← Subgroup.inf_subgroupOf_left, ← hEcard, ← hQE]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hQcard : Nat.card Q = 2 * Nat.card U ^ 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθsurj).toEquiv, hkercard]
    ring
  have hsq : ∀ x ∈ Q, x * x ∈ U := by
    intro x hx
    have hθx : involutionDisplacement u (x * x) = 1 := by
      rw [involutionDisplacement_mul hu hx.2 (involutionDisplacement_mem hu hx.1)]
      exact hUsq _ (involutionDisplacement_mem hu hx.1)
    have hxxE : x * x ∈ Subgroup.zpowers u ⊔ U := by
      rw [← hQE]
      exact ⟨Q.mul_mem hx hx, Subgroup.mem_centralizer_singleton_iff.mpr
        ((involutionDisplacement_eq_one_iff hu _).mp hθx)⟩
    have hxxE' := hxxE
    rw [Subgroup.zpowers_eq_closure, mem_closure_singleton_sup_iff hu hcomm] at hxxE'
    rcases hxxE' with h | ⟨b, hb, hbx⟩
    · exact h
    · exfalso
      have hxb : x * b = b * x := (Subgroup.mem_centralizer_iff.mp hx.2 b hb).symm
      have hxu : x * u = u * x := by
        have hu' : u = x * x * b⁻¹ := by rw [← hbx, mul_inv_cancel_right]
        have hxb' : x * b⁻¹ = b⁻¹ * x := (show Commute x b from hxb).inv_right.eq
        rw [hu']
        calc x * (x * x * b⁻¹) = x * x * (x * b⁻¹) := by group
          _ = x * x * (b⁻¹ * x) := by rw [hxb']
          _ = x * x * b⁻¹ * x := by group
      have hxE : x ∈ Subgroup.zpowers u ⊔ U := by
        rw [← hQE]
        exact ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxu⟩
      have h1 := mul_self_eq_one_of_mem_sup hu hcomm hUsq hxE
      rw [h1] at hbx
      apply huU
      have : u = b⁻¹ := eq_inv_of_mul_eq_one_left hbx
      rw [this]
      exact U.inv_mem hb
  refine ⟨hEQ, hQE, hEcard, hQcard, hsq, ?_⟩
  intro x hx y hy
  have hs : x⁻¹ = x * (x * x)⁻¹ := by group
  have ht : y⁻¹ = y * (y * y)⁻¹ := by group
  have hc : (x * x)⁻¹ * y = y * (x * x)⁻¹ :=
    Subgroup.mem_centralizer_iff.mp hy.2 _ (U.inv_mem (hsq x hx))
  have heq : x * y * x⁻¹ * y⁻¹ = (x * y) * (x * y) * (x * x)⁻¹ * (y * y)⁻¹ := by
    calc x * y * x⁻¹ * y⁻¹ = x * y * (x * (x * x)⁻¹) * (y * (y * y)⁻¹) := by rw [← hs, ← ht]
      _ = x * y * x * ((x * x)⁻¹ * y) * (y * y)⁻¹ := by group
      _ = x * y * x * (y * (x * x)⁻¹) * (y * y)⁻¹ := by rw [hc]
      _ = (x * y) * (x * y) * (x * x)⁻¹ * (y * y)⁻¹ := by group
  rw [heq]
  exact U.mul_mem (U.mul_mem (hsq _ (Q.mul_mem hx hy)) (U.inv_mem (hsq x hx)))
    (U.inv_mem (hsq y hy))

end CFSG.ProperTwoGeneratedCore.HighRankPair
