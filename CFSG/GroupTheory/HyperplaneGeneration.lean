module

public import CFSG.GroupTheory.SolvableHallNodes
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.GroupTheory.Nilpotent

public section

open scoped IsMulCommutative

namespace CFSG.SolvableHall

theorem abelian_irreducible_action_cyclic_image {k V A : Type*} [Field k] [Finite k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V] [CommGroup A] [Finite A]
    (ρ : A →* LinearMap.GeneralLinearGroup k V)
    (hirr : ∀ W : Submodule k V, (∀ a : A, ∀ v ∈ W, (ρ a : V →ₗ[k] V) v ∈ W) → W = ⊥ ∨ W = ⊤) :
    IsCyclic ρ.range := by
  classical
  set s : Set (V →ₗ[k] V) := Set.range fun a => ((ρ a : LinearMap.GeneralLinearGroup k V) :
    V →ₗ[k] V) with hs
  have hcomm : s.Pairwise Commute := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _
    change ((ρ a : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) * (ρ b : V →ₗ[k] V) =
      (ρ b : V →ₗ[k] V) * (ρ a : V →ₗ[k] V)
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_comm]
  set R : Subalgebra k (V →ₗ[k] V) := Algebra.adjoin k s with hR
  have : IsMulCommutative R := Algebra.isMulCommutative_adjoin k hcomm
  have hself : ∀ a : A, ((ρ a : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) ∈
      Subalgebra.centralizer k s := by
    intro a
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨b, rfl⟩
    dsimp only
    by_cases hab : ((ρ b : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) =
      (ρ a : V →ₗ[k] V)
    · rw [hab]
    · exact hcomm ⟨b, rfl⟩ ⟨a, rfl⟩ hab
  have hcent : ∀ r ∈ R, ∀ a : A,
      r * ((ρ a : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) = (ρ a : V →ₗ[k] V) * r := by
    intro r hr a
    have h := Algebra.adjoin_le_centralizer_centralizer k s hr
    rw [Subalgebra.mem_centralizer_iff] at h
    exact (h _ (hself a)).symm
  have hinj : ∀ r ∈ R, r ≠ 0 → Function.Injective r := by
    intro r hr hr0
    have hker := hirr (LinearMap.ker r) (fun a v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      have h := congrArg (fun f : V →ₗ[k] V => f v) (hcent r hr a)
      simp only [Module.End.mul_apply] at h
      rw [h, hv, map_zero])
    rcases hker with h | h
    · exact LinearMap.ker_eq_bot.mp h
    · exfalso
      apply hr0
      ext v
      have hv : v ∈ LinearMap.ker r := h ▸ Submodule.mem_top
      exact hv
  have hnzd : NoZeroDivisors R := by
    refine ⟨fun {x y} hxy => ?_⟩
    by_contra hne'
    have hne := not_or.mp hne'
    have hx : (x : V →ₗ[k] V) ≠ 0 := fun h => hne.1 (Subtype.ext h)
    have hy : (y : V →ₗ[k] V) ≠ 0 := fun h => hne.2 (Subtype.ext h)
    apply hy
    ext v
    have h := congrArg (fun z : R => (z : V →ₗ[k] V) v) hxy
    simp only [Subalgebra.coe_mul, Module.End.mul_apply, ZeroMemClass.coe_zero,
      LinearMap.zero_apply] at h
    exact hinj x x.2 hx (h.trans (map_zero _).symm)
  have hnt : Nontrivial R := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h' := congrArg (fun z : R => (z : V →ₗ[k] V) v) h
    simp only [ZeroMemClass.coe_zero, LinearMap.zero_apply, OneMemClass.coe_one,
      Module.End.one_apply] at h'
    exact hv h'.symm
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  let φ : ρ.range →* R :=
    { toFun := fun g => ⟨((g : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V), by
        obtain ⟨a, ha⟩ := g.2
        rw [← ha]
        exact Algebra.subset_adjoin ⟨a, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun g h => by
        apply Subtype.ext
        simp }
  have hφ : Function.Injective φ := by
    intro g h hgh
    apply Subtype.ext
    apply Units.ext
    exact congrArg Subtype.val hgh
  have : Finite ρ.range := Finite.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  exact isCyclic_of_injective_ringHom φ hφ

theorem exists_index_eq_prime {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [Finite A]
    (hA : IsPGroup p A) [Nontrivial A] : ∃ B : Subgroup A, B.index = p := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hn
  obtain ⟨B, hB⟩ := Sylow.exists_subgroup_card_pow_prime p (n := n - 1)
    (by rw [hn]; exact pow_dvd_pow p (Nat.sub_le n 1))
  refine ⟨B, ?_⟩
  have h := B.card_mul_index
  have hpow : p ^ n = p ^ (n - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0)]
  rw [hB, hn, hpow] at h
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos _) h

theorem exists_hyperplane_acting_trivially_of_irreducible {p : ℕ} [Fact p.Prime]
    {A H : Type*} [Group A] [Finite A] [IsElementaryAbelian p A] [Nontrivial A]
    [CommGroup H] [Finite H] [Nontrivial H] [MulDistribMulAction A H]
    (hirr : ∀ U : Subgroup H, (∀ a : A, ∀ x ∈ U, a • x ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∃ B : Subgroup A, B.index = p ∧ ∀ b ∈ B, ∀ x : H, b • x = x := by
  classical
  let φ : A →* AddMonoid.End (Additive H) :=
    { toFun := fun a => MonoidHom.toAdditive (MulDistribMulAction.toMonoidHom H a)
      map_one' := by
        ext x
        change Additive.ofMul ((1 : A) • Additive.toMul x) = x
        rw [one_smul, ofMul_toMul]
      map_mul' := fun a b => by
        ext x
        change Additive.ofMul ((a * b) • Additive.toMul x) =
          Additive.ofMul (a • Additive.toMul (Additive.ofMul (b • Additive.toMul x)))
        rw [toMul_ofMul, mul_smul] }
  have hφ : ∀ (a : A) (x : H), φ a (Additive.ofMul x) = Additive.ofMul (a • x) :=
    fun _ _ => rfl
  set S : Set (AddMonoid.End (Additive H)) := Set.range φ with hS
  have hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm']
  set R : Subring (AddMonoid.End (Additive H)) := Subring.centralizer (Set.centralizer S) with hR
  have hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x :=
    Set.centralizer_centralizer_comm_of_comm (fun x hx y hy _ => hcomm x hx y hy)
  have hSR : ∀ a : A, φ a ∈ R := fun a => Set.subset_centralizer_centralizer ⟨a, rfl⟩
  have hSc : ∀ a : A, φ a ∈ Set.centralizer S := fun a y hy => (hcomm _ hy _ ⟨a, rfl⟩)
  have : IsMulCommutative R := ⟨⟨fun x y => Subtype.ext (hRcomm _ x.2 _ y.2)⟩⟩
  have hinj : ∀ r ∈ R, r ≠ 0 → ∀ x : Additive H, r x = 0 → x = 0 := by
    intro r hr hr0
    let U : Subgroup H := AddSubgroup.toSubgroup' (AddMonoidHom.ker r)
    have hU : ∀ x : H, x ∈ U ↔ r (Additive.ofMul x) = 0 := fun x => Iff.rfl
    have hinv : ∀ a : A, ∀ x ∈ U, a • x ∈ U := by
      intro a x hx
      rw [hU] at hx ⊢
      rw [← hφ]
      have h := congrArg (fun f : AddMonoid.End (Additive H) => f (Additive.ofMul x))
        (hr (φ a) (hSc a))
      change φ a (r (Additive.ofMul x)) = r (φ a (Additive.ofMul x)) at h
      rw [← h, hx, map_zero]
    rcases hirr U hinv with h | h
    · intro x hx
      have hx' : Additive.toMul x ∈ U := by rw [hU, ofMul_toMul]; exact hx
      rw [h, Subgroup.mem_bot] at hx'
      rw [← ofMul_toMul x, hx', ofMul_one]
    · exfalso
      apply hr0
      ext x
      have hx' : Additive.toMul x ∈ U := by rw [h]; exact Subgroup.mem_top _
      rw [hU, ofMul_toMul] at hx'
      exact hx'
  have hnzd : NoZeroDivisors R := by
    refine ⟨fun {x y} hxy => ?_⟩
    by_contra hne'
    have hne := not_or.mp hne'
    have hx : (x : AddMonoid.End (Additive H)) ≠ 0 := fun h => hne.1 (Subtype.ext h)
    apply hne.2
    apply Subtype.ext
    ext v
    have h := congrArg (fun z : R => (z : AddMonoid.End (Additive H)) v) hxy
    change (x : AddMonoid.End (Additive H)) ((y : AddMonoid.End (Additive H)) v) = 0 at h
    exact hinj x x.2 hx _ h
  have hnt : Nontrivial R := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    obtain ⟨v, hv⟩ := exists_ne (1 : H)
    have h' := congrArg (fun z : R => (z : AddMonoid.End (Additive H)) (Additive.ofMul v)) h
    change (0 : Additive H) = Additive.ofMul v at h'
    exact hv (Additive.ofMul.injective h'.symm)
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  let ψ : A →* R :=
    { toFun := fun a => ⟨φ a, hSR a⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun a b => Subtype.ext (map_mul φ a b) }
  let ψu : A →* Rˣ := MonoidHom.toHomUnits ψ
  have hcyc : IsCyclic (A ⧸ ψu.ker) :=
    isCyclic_of_injective_ringHom ((Units.coeHom R).comp (QuotientGroup.kerLift ψu))
      ((Units.val_injective).comp (QuotientGroup.kerLift_injective ψu))
  have hexp : ∀ g : A ⧸ ψu.ker, g ^ p = 1 := by
    intro g
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_pow, (Monoid.exponent_dvd_iff_forall_pow_eq_one).mp
      (IsElementaryAbelian.exponent_dvd_p p A) a, QuotientGroup.mk_one]
  have hcard : ψu.ker.index ∣ p := by
    rw [Subgroup.index, ← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hexp
  have hker : ∀ a ∈ ψu.ker, ∀ x : H, a • x = x := by
    intro a ha x
    have h := congrArg (fun z : Rˣ => ((z : R) : AddMonoid.End (Additive H)) (Additive.ofMul x))
      (MonoidHom.mem_ker.mp ha)
    change Additive.ofMul (a • x) = Additive.ofMul x at h
    exact Additive.ofMul.injective h
  rcases (Nat.dvd_prime Fact.out).mp hcard with h1 | hp
  ·
    have htop : ψu.ker = ⊤ := Subgroup.index_eq_one.mp h1
    obtain ⟨B, hB⟩ := exists_index_eq_prime (IsElementaryAbelian.isPGroup p A)
    exact ⟨B, hB, fun b _ x => hker b (htop ▸ Subgroup.mem_top b) x⟩
  · exact ⟨ψu.ker, hp, hker⟩

section Generation

universe u v

variable {p : ℕ} [Fact p.Prime] {A : Type v} [Group A] [Finite A] [IsElementaryAbelian p A]

theorem exists_fixed_of_coset_fixed {G : Type u} {B : Type v} [Group G] [Finite G] [Group B]
    [Finite B] [MulDistribMulAction B G] (N : Subgroup G) [N.Normal]
    (hNinv : IsInvariant B G N) (hNsolv : Group.IsSolvable N)
    (hcop : Nat.Coprime (Nat.card B) (Nat.card N)) (g : G) (hg : ∀ b : B, g⁻¹ * (b • g) ∈ N) :
    ∃ c ∈ fixedPointSubgroup B G, c⁻¹ * g ∈ N := by
  have h := coprime_solvable_kernel_fixed_point_lifting N hNinv hNsolv hcop
  let : MulDistribMulAction B (G ⧸ N) := quotientMulDistribMulAction (A := B) (G := G) N hNinv
  let : MulAction.QuotientAction B N := quotientAction_of_isInvariant (A := B) N hNinv
  have hmem : (g : G ⧸ N) ∈ fixedPointSubgroup B (G ⧸ N) := by
    intro b
    change b • (g : G ⧸ N) = (g : G ⧸ N)
    rw [MulAction.Quotient.smul_coe]
    exact (QuotientGroup.eq.mpr (hg b)).symm
  rw [h] at hmem
  obtain ⟨c, hc, hcg⟩ := hmem
  exact ⟨c, hc, QuotientGroup.eq.mp hcg⟩

theorem coprime_card_subgroup (B : Subgroup A) {n : ℕ} (hn : ¬ p ∣ n) :
    Nat.Coprime (Nat.card B) n := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((IsElementaryAbelian.isPGroup p A).to_subgroup B)
  rw [hk]
  exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hn)

omit [Fact p.Prime] [Finite A] [IsElementaryAbelian p A] in
theorem le_hyperplane_join_of_invariant {H : Type u} [Group H] [MulDistribMulAction A H]
    (U : Subgroup H) [IsInvariant A H U]
    (hU : ⨆ (B : Subgroup A) (_ : B.index = p), fixedPointSubgroup B U = ⊤) :
    U ≤ ⨆ (B : Subgroup A) (_ : B.index = p), fixedPointSubgroup B H := by
  intro u hu
  have h1 : (⟨u, hu⟩ : U) ∈ ⨆ (B : Subgroup A) (_ : B.index = p), fixedPointSubgroup B U :=
    hU ▸ Subgroup.mem_top _
  have h2 := Subgroup.mem_map_of_mem U.subtype h1
  simp only [Subgroup.map_iSup] at h2
  have hle : (⨆ (B : Subgroup A) (_ : B.index = p),
      (fixedPointSubgroup B U).map U.subtype) ≤
      ⨆ (B : Subgroup A) (_ : B.index = p), fixedPointSubgroup B H := by
    refine iSup_mono fun B => iSup_mono fun _ => ?_
    rintro _ ⟨y, hy, rfl⟩
    intro b
    exact congrArg Subtype.val (hy b)
  exact hle h2

theorem hyperplane_join_eq_top_of_normal {H : Type u} [Group H] [Finite H]
    [MulDistribMulAction A H] (hp : ¬ p ∣ Nat.card H) (U : Subgroup H) [U.Normal]
    [hUinv : IsInvariant A H U] (hUsolv : Group.IsSolvable U)
    (hU : ⨆ (B : Subgroup A) (_ : B.index = p), fixedPointSubgroup B U = ⊤)
    (hQ : letI : MulDistribMulAction A (H ⧸ U) :=
        quotientMulDistribMulAction (A := A) (G := H) U hUinv
      ⨆ (B : Subgroup A) (_ : B.index = p), fixedPointSubgroup B (H ⧸ U) = ⊤) :
    ⨆ (B : Subgroup A) (_ : B.index = p), fixedPointSubgroup B H = ⊤ := by
  classical
  set X := ⨆ (B : Subgroup A) (_ : B.index = p), fixedPointSubgroup B H with hX
  have hUp : ¬ p ∣ Nat.card U := fun h => hp (h.trans (Subgroup.card_subgroup_dvd_card U))
  have hUX : U ≤ X := le_hyperplane_join_of_invariant U hU
  let : MulDistribMulAction A (H ⧸ U) := quotientMulDistribMulAction (A := A) (G := H) U hUinv
  let : MulAction.QuotientAction A U := quotientAction_of_isInvariant (A := A) U hUinv
  have himage : ∀ B : Subgroup A, B.index = p →
      fixedPointSubgroup B (H ⧸ U) ≤ (fixedPointSubgroup B H).map (QuotientGroup.mk' U) := by
    intro B _ x hx
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    have hBinv : IsInvariant B H U :=
      ⟨fun b g => hUinv.invariant (b : A) g⟩
    have hg : ∀ b : B, h⁻¹ * (b • h) ∈ U := by
      intro b
      have hb := hx b
      change (b : A) • (h : H ⧸ U) = (h : H ⧸ U) at hb
      rw [MulAction.Quotient.smul_coe] at hb
      exact QuotientGroup.eq.mp hb.symm
    obtain ⟨c, hc, hcg⟩ := exists_fixed_of_coset_fixed U hBinv hUsolv
      (coprime_card_subgroup B hUp) h hg
    exact ⟨c, hc, (QuotientGroup.eq.mpr hcg)⟩
  have hXmap : X.map (QuotientGroup.mk' U) = ⊤ := by
    rw [eq_top_iff, ← hQ, hX]
    simp only [Subgroup.map_iSup]
    exact iSup_mono fun B => iSup_mono fun hB => himage B hB
  rw [eq_top_iff]
  intro h _
  have hmem : (h : H ⧸ U) ∈ X.map (QuotientGroup.mk' U) := hXmap ▸ Subgroup.mem_top _
  obtain ⟨x, hx, hxh⟩ := hmem
  have hxu : x⁻¹ * h ∈ U := QuotientGroup.eq.mp hxh
  have : h = x * (x⁻¹ * h) := by group
  rw [this]
  exact X.mul_mem hx (hUX hxu)

omit [Finite A] in
theorem isInvariant_of_forall_smul_mem {H : Type*} [Group H] [MulDistribMulAction A H]
    {U : Subgroup H} (hU : ∀ a : A, ∀ x ∈ U, a • x ∈ U) : IsInvariant A H U :=
  ⟨fun a g => ⟨fun hg => hU a g hg, fun hag => by
    have := hU a⁻¹ _ hag
    rwa [inv_smul_smul] at this⟩⟩

theorem abelian_hyperplane_generation [Nontrivial A] {H : Type u} [CommGroup H] [Finite H]
    [MulDistribMulAction A H] (hp : ¬ p ∣ Nat.card H) :
    ⨆ (B : Subgroup A) (_ : B.index = p), fixedPointSubgroup B H = ⊤ := by
  classical
  suffices key : ∀ n : ℕ, ∀ (H : Type u) [CommGroup H] [Finite H] [MulDistribMulAction A H],
      Nat.card H = n → ¬ p ∣ Nat.card H →
      ⨆ (B : Subgroup A) (_ : B.index = p), fixedPointSubgroup B H = ⊤ from key _ H rfl hp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ _ hn hp
  by_cases hU : ∃ U : Subgroup H, U ≠ ⊥ ∧ U ≠ ⊤ ∧ ∀ a : A, ∀ x ∈ U, a • x ∈ U
  · obtain ⟨U, hU1, hUtop, hUinv⟩ := hU
    have : IsInvariant A H U := isInvariant_of_forall_smul_mem hUinv
    have hUlt : Nat.card U < n := by
      rw [← hn, ← Subgroup.card_top (G := H)]
      exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hUtop)
    have hUp : ¬ p ∣ Nat.card U := fun h => hp (h.trans (Subgroup.card_subgroup_dvd_card U))
    let : MulDistribMulAction A (H ⧸ U) := quotientMulDistribMulAction (A := A) (G := H) U this
    have hQlt : Nat.card (H ⧸ U) < n := by
      rw [← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup U]
      have h1 : 1 < Nat.card U := by
        rw [Finite.one_lt_card_iff_nontrivial]
        exact (Subgroup.nontrivial_iff_ne_bot U).mpr hU1
      have h0 : 0 < Nat.card (H ⧸ U) := Nat.card_pos
      nlinarith
    have hQp : ¬ p ∣ Nat.card (H ⧸ U) := fun h => hp (h.trans (Subgroup.card_quotient_dvd_card U))
    exact hyperplane_join_eq_top_of_normal hp U inferInstance (ih _ hUlt U rfl hUp)
      (ih _ hQlt (H ⧸ U) rfl hQp)
  · have hirr : ∀ U : Subgroup H, (∀ a : A, ∀ x ∈ U, a • x ∈ U) → U = ⊥ ∨ U = ⊤ := by
      intro U hUinv
      by_contra hne
      exact hU ⟨U, fun h => hne (Or.inl h), fun h => hne (Or.inr h), hUinv⟩
    rcases subsingleton_or_nontrivial H with hsub | hnt
    · exact Subsingleton.elim _ _
    · obtain ⟨B, hB, hBfix⟩ := exists_hyperplane_acting_trivially_of_irreducible (p := p) hirr
      rw [eq_top_iff]
      refine le_trans ?_ (le_iSup₂ (f := fun (B : Subgroup A) (_ : B.index = p) =>
        fixedPointSubgroup B H) B hB)
      intro x _ b
      exact hBfix b b.2 x

theorem solvable_hyperplane_generation [Nontrivial A] {H : Type u} [Group H] [Finite H]
    [MulDistribMulAction A H] (hH : Group.IsSolvable H) (hp : ¬ p ∣ Nat.card H) :
    ⨆ (B : Subgroup A) (_ : B.index = p), fixedPointSubgroup B H = ⊤ := by
  classical
  suffices key : ∀ n : ℕ, ∀ (H : Type u) [Group H] [Finite H] [MulDistribMulAction A H],
      Nat.card H = n → Group.IsSolvable H → ¬ p ∣ Nat.card H →
      ⨆ (B : Subgroup A) (_ : B.index = p), fixedPointSubgroup B H = ⊤ from key _ H rfl hH hp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ _ hn hH hp
  by_cases hab : commutator H = ⊥
  ·
    let : CommGroup H :=
      { (inferInstance : Group H) with
        mul_comm := fun x y => by
          rw [commutator_def] at hab
          have h := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hab (Subgroup.mem_top x)
          exact (Subgroup.mem_centralizer_iff.mp h y (Subgroup.mem_top y)).symm }
    exact abelian_hyperplane_generation hp
  · rcases subsingleton_or_nontrivial H with hsub | hnt
    · exact Subsingleton.elim _ _
    set U := commutator H with hUdef
    have hUtop : U ≠ ⊤ := (Group.IsSolvable.commutator_lt_top_of_nontrivial H).ne
    have hUinv : ∀ a : A, ∀ x ∈ U, a • x ∈ U := by
      intro a x hx
      have hmem : a • x ∈ U.map (MulDistribMulAction.toMonoidHom H a) :=
        Subgroup.mem_map_of_mem _ hx
      rw [hUdef, commutator_def, Subgroup.map_commutator] at hmem
      rw [hUdef, commutator_def]
      exact Subgroup.commutator_mono le_top le_top hmem
    have : IsInvariant A H U := isInvariant_of_forall_smul_mem hUinv
    have hUlt : Nat.card U < n := by
      rw [← hn, ← Subgroup.card_top (G := H)]
      exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hUtop)
    have hUp : ¬ p ∣ Nat.card U := fun h => hp (h.trans (Subgroup.card_subgroup_dvd_card U))
    let : MulDistribMulAction A (H ⧸ U) := quotientMulDistribMulAction (A := A) (G := H) U this
    have hQlt : Nat.card (H ⧸ U) < n := by
      rw [← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup U]
      have h1 : 1 < Nat.card U := by
        rw [Finite.one_lt_card_iff_nontrivial]
        exact (Subgroup.nontrivial_iff_ne_bot U).mpr hab
      have h0 : 0 < Nat.card (H ⧸ U) := Nat.card_pos
      nlinarith
    have hQp : ¬ p ∣ Nat.card (H ⧸ U) := fun h => hp (h.trans (Subgroup.card_quotient_dvd_card U))
    have hUsolv : Group.IsSolvable U := inferInstance
    exact hyperplane_join_eq_top_of_normal hp U hUsolv (ih _ hUlt U rfl hUsolv hUp)
      (ih _ hQlt (H ⧸ U) rfl inferInstance hQp)

omit [Finite A] in
theorem exists_invariant_sylow {H : Type*} [Group H] [Finite H] [MulDistribMulAction A H]
    (hp : ¬ p ∣ Nat.card H) (q : ℕ) [Fact q.Prime] :
    ∃ Q : Sylow q H, ∀ a : A, ∀ x ∈ (Q : Subgroup H), a • x ∈ (Q : Subgroup H) := by
  classical
  have hcard : ¬ p ∣ Nat.card (Sylow q H) := by
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow q H))
    intro h
    exact hp (h.trans ((Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card _)))
  obtain ⟨Q, hQ⟩ :=
    (IsElementaryAbelian.isPGroup p A).nonempty_fixed_point_of_prime_not_dvd_card (Sylow q H)
      hcard
  refine ⟨Q, fun a x hx => ?_⟩
  have hmem : a • x ∈ ((a • Q : Sylow q H) : Subgroup H) := by
    rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    exact ⟨x, hx, rfl⟩
  rwa [hQ a] at hmem

theorem coprime_hyperplane_generation [Nontrivial A] {H : Type u} [Group H] [Finite H]
    [MulDistribMulAction A H] (hp : ¬ p ∣ Nat.card H) :
    ⨆ (B : Subgroup A) (_ : B.index = p), fixedPointSubgroup B H = ⊤ := by
  classical
  set X := ⨆ (B : Subgroup A) (_ : B.index = p), fixedPointSubgroup B H with hX
  have hsyl : ∀ (q : ℕ) [Fact q.Prime], ∃ Q : Sylow q H, (Q : Subgroup H) ≤ X := by
    intro q _
    obtain ⟨Q, hQ⟩ := exists_invariant_sylow (A := A) hp q
    have : IsInvariant A H Q := isInvariant_of_forall_smul_mem hQ
    have hQp : ¬ p ∣ Nat.card (Q : Subgroup H) :=
      fun h => hp (h.trans (Subgroup.card_subgroup_dvd_card _))
    have : Group.IsNilpotent (Q : Subgroup H) := Q.isPGroup'.isNilpotent
    exact ⟨Q, le_hyperplane_join_of_invariant (A := A) (p := p) (Q : Subgroup H)
      (solvable_hyperplane_generation (A := A) inferInstance hQp)⟩
  have hdvd : Nat.card H ∣ Nat.card X := by
    apply (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mp
    intro q
    by_cases hq : q.Prime
    · have : Fact q.Prime := ⟨hq⟩
      obtain ⟨Q, hQX⟩ := hsyl q
      have h2 : Nat.card (Q : Subgroup H) ∣ Nat.card X := Subgroup.card_dvd_of_le hQX
      rw [Sylow.card_eq_multiplicity Q] at h2
      exact (hq.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h2
    · simp [Nat.factorization_eq_zero_of_not_prime _ hq]
  exact (Subgroup.card_eq_iff_eq_top X).mp
    (Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card X) hdvd)

omit [Fact p.Prime] [Finite A] [IsElementaryAbelian p A] in
theorem mem_fixedPointSubgroup_zpowers_iff {H : Type*} [Group H] [MulDistribMulAction A H]
    (a : A) (x : H) : x ∈ fixedPointSubgroup (Subgroup.zpowers a) H ↔ a • x = x := by
  constructor
  · intro h
    exact h ⟨a, Subgroup.mem_zpowers a⟩
  · rintro h ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact MulAction.mem_fixedBy_zpow (α := H) h k

theorem coprime_centralizer_generation {H : Type u} [Group H] [Finite H]
    [MulDistribMulAction A H] (hA : p ^ 2 ≤ Nat.card A) (hp : ¬ p ∣ Nat.card H) :
    ⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (Subgroup.zpowers a) H = ⊤ := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hA1 : 1 < Nat.card A := lt_of_lt_of_le (by nlinarith) hA
  have : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp hA1
  rw [eq_top_iff, ← coprime_hyperplane_generation (A := A) hp]
  refine iSup₂_le fun B hB => ?_
  have hBcard : 1 < Nat.card B := by
    have h := B.card_mul_index
    rw [hB] at h
    by_contra hle
    have hle' := Nat.mul_le_mul_right p (not_lt.mp hle)
    nlinarith
  have : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp hBcard
  obtain ⟨⟨a, haB⟩, ha1⟩ := exists_ne (1 : B)
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  refine le_trans ?_ (le_iSup₂ (f := fun (a : A) (_ : a ≠ 1) =>
    fixedPointSubgroup (Subgroup.zpowers a) H) a ha1')
  intro x hx g
  exact hx ⟨g, (Subgroup.zpowers_le.mpr haB) g.2⟩

end Generation

end CFSG.SolvableHall
