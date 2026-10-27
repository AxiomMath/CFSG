module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256e
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympAut

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256f

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open scoped commutatorElement

section Generic

theorem qGen_of_lieCompsExport {T : Type} [Group T] {q : ℕ} {β : MulAut T}
    (hβ : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LieCompsExport q β)
    (hgen : ∀ s : T, β s = s → (∃ n : ℕ, s ^ q ^ n = 1) →
      ∃ P : Subgroup T, P ≤ fixSubgroup β ∧ ⁅P, P⁆ = P ∧ s ∈ P) : Inputs256e.QGen q β := by
  intro s hs hsq
  obtain ⟨P, hPC, hP, hsP⟩ := hgen s hs hsq
  have hle : GLALayer (fixSubgroup β) ≤
      ⨆ (J : Subgroup T) (_ : Inputs256e.IsChevSub q β J), J := by
    refine sSup_le fun K hK => ?_
    obtain ⟨X, _, _, hX, f, hf, hfk⟩ := hβ.comps K hK
    obtain ⟨e⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hX.perfect f hf hfk
    exact le_iSup₂_of_le (f := fun (J : Subgroup T) (_ : Inputs256e.IsChevSub q β J) => J) K
      ⟨hK.2.1, hK.2.2, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr e hX.chev⟩
      le_rfl
  exact hle (hβ.layer P hPC hP hsP)

theorem exists_fixed_lift {X T : Type} [Group X] [Finite X] [Group T] {q : ℕ} (π : X →* T)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center X)
    (hcop : Nat.Coprime (Nat.card π.ker) q) (α : MulAut X) (β : MulAut T)
    (hαβ : ∀ x, π (α x) = β (π x)) {s : T} (hs : β s = s) {n : ℕ} (hn : s ^ q ^ n = 1) :
    ∃ x : X, π x = s ∧ α x = x ∧ x ^ q ^ n = 1 := by
  obtain ⟨x, hx, hxn⟩ := Inputs256e.exists_pow_lift π hπ hcop hn
  have hzk : x⁻¹ * α x ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hαβ, hx, hs, inv_mul_cancel]
  have hcomm : Commute x (α x) := by
    have hz : Commute x (x⁻¹ * α x) := Subgroup.mem_center_iff.1 (hker hzk) x
    have e : α x = x * (x⁻¹ * α x) := by group
    rw [e]
    exact (Commute.refl x).mul_right hz
  have hzq : (x⁻¹ * α x) ^ q ^ n = 1 := by
    rw [(hcomm.inv_left).mul_pow, inv_pow, hxn, ← map_pow, hxn, map_one, inv_one, one_mul]
  have h1 := Inputs256e.eq_one_of_mem_of_coprime hcop hzk hzq
  rw [inv_mul_eq_one] at h1
  exact ⟨x, hx, h1.symm, hxn⟩

theorem exists_perfect_of_centralQuotient {X T : Type} [Group X] [Finite X] [Group T] {q : ℕ}
    (π : X →* T) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center X)
    (hcop : Nat.Coprime (Nat.card π.ker) q) (α : MulAut X) (β : MulAut T)
    (hαβ : ∀ x, π (α x) = β (π x)) {N : Subgroup X} (hNα : N ≤ fixSubgroup α) (hN : ⁅N, N⁆ = N)
    (hgen : ∀ x ∈ fixSubgroup α, (∃ n : ℕ, x ^ q ^ n = 1) → x ∈ N) :
    ∀ s : T, β s = s → (∃ n : ℕ, s ^ q ^ n = 1) →
      ∃ P : Subgroup T, P ≤ fixSubgroup β ∧ ⁅P, P⁆ = P ∧ s ∈ P := by
  rintro s hs ⟨n, hn⟩
  obtain ⟨x, rfl, hx, hxn⟩ := exists_fixed_lift π hπ hker hcop α β hαβ hs hn
  refine ⟨N.map π, (Subgroup.map_mono hNα).trans
    (CFSG.HardMathSupport.Solomon.Coordinator.map_fixSubgroup_le π hker α β hαβ), ?_,
    Subgroup.mem_map_of_mem π (hgen x (mem_fixSubgroup.2 hx) ⟨n, hxn⟩)⟩
  rw [← Subgroup.map_commutator, hN]

theorem commutator_le_self' {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem h₁ h₂) (H.inv_mem h₁)) (H.inv_mem h₂)

theorem commutator_self_of_perfect {G : Type*} [Group G] {F : Subgroup G}
    (h : commutator ↥F = ⊤) : ⁅F, F⁆ = F := by
  rw [← Subgroup.map_subtype_commutator, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem commutator_iSup_eq {G : Type*} [Group G] {ι : Type*} (F : ι → Subgroup G)
    (hF : ∀ i, ⁅F i, F i⁆ = F i) : ⁅⨆ i, F i, ⨆ i, F i⁆ = ⨆ i, F i :=
  le_antisymm (commutator_le_self' _) (iSup_le fun i =>
    (hF i).symm.le.trans (Subgroup.commutator_mono (le_iSup F i) (le_iSup F i)))

theorem mem_of_mem_iSup_commute {G : Type*} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    {ι : Type*} [Finite ι] (A : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b) (N : Subgroup G)
    (hA : ∀ i, ∀ a ∈ A i, (∃ n : ℕ, a ^ q ^ n = 1) → a ∈ N) {g : G} (hg : g ∈ ⨆ i, A i)
    {n : ℕ} (hgn : g ^ q ^ n = 1) : g ∈ N := by
  classical
  cases nonempty_fintype ι
  have hcomm : Pairwise fun i j => ∀ x y : G, x ∈ A i → y ∈ A j → Commute x y :=
    fun i j hij x y hx hy => hc i j hij x hx y hy
  rw [← Subgroup.noncommPiCoprod_range (hcomm := hcomm)] at hg
  obtain ⟨a, rfl⟩ := hg
  obtain ⟨e, m, hqm, hcard⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := G)).ne' q hq.ne_one
  have hcop : Nat.Coprime m (orderOf (Subgroup.noncommPiCoprod hcomm a)) := by
    have h1 : orderOf (Subgroup.noncommPiCoprod hcomm a) ∣ q ^ n := orderOf_dvd_of_pow_eq_one hgn
    have h2 : Nat.Coprime m q := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hq).2 hqm)
    exact Nat.Coprime.coprime_dvd_right h1 (Nat.Coprime.pow_right n h2)
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hu, ← map_pow, ← map_pow, Subgroup.noncommPiCoprod_apply]
  refine Subgroup.noncommProd_mem _ _ fun i _ => hA i _ (((a ^ m) ^ u) i).2 ⟨e, ?_⟩
  have h1 : (a i : G) ^ (q ^ e * m) = 1 := by rw [← hcard]; exact pow_card_eq_one'
  change (((a i : G) ^ m) ^ u) ^ q ^ e = 1
  rw [← pow_mul, ← pow_mul, show m * (u * q ^ e) = q ^ e * m * u by ring, pow_mul, h1, one_pow]

end Generic

section Tame

variable {q : ℕ}

private def QTameGrp (q : ℕ) (H : Type*) [Group H] : Prop :=
  (CFSG.IsQuasisimple ↥(commutator H) ∧ ∀ h : H, (∃ n : ℕ, h ^ q ^ n = 1) → h ∈ commutator H) ∨
    ∀ h : H, (∃ n : ℕ, h ^ q ^ n = 1) → h = 1

private def QTame (q : ℕ) {G : Type*} [Group G] (A : Subgroup G) : Prop :=
  (CFSG.IsQuasisimple ↥⁅A, A⁆ ∧ ∀ a ∈ A, (∃ n : ℕ, a ^ q ^ n = 1) → a ∈ ⁅A, A⁆) ∨
    ∀ a ∈ A, (∃ n : ℕ, a ^ q ^ n = 1) → a = 1

private theorem map_commutator_mulEquiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) :
    (commutator A).map φ.toMonoidHom = commutator B := by
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 φ.surjective]

private theorem qTame_of_mulEquiv {G H : Type*} [Group G] [Group H] {A : Subgroup G} (φ : A ≃* H)
    (h : QTameGrp q H) : QTame q A := by
  have e : ↥(commutator ↥A) ≃* ↥(commutator H) :=
    ((commutator ↥A).equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr (map_commutator_mulEquiv φ))
  have e' : ↥(commutator ↥A) ≃* ↥⁅A, A⁆ :=
    ((commutator ↥A).equivMapOfInjective A.subtype A.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator A))
  have hpow : ∀ a (ha : a ∈ A) (n : ℕ), a ^ q ^ n = 1 → (φ ⟨a, ha⟩) ^ q ^ n = 1 := by
    intro a ha n hn
    rw [← map_pow]
    exact (map_eq_one_iff φ φ.injective).2 (Subtype.ext (by simpa using hn))
  rcases h with ⟨hq, hel⟩ | hel
  · refine Or.inl ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (e.symm.trans e') hq, ?_⟩
    rintro a ha ⟨n, hn⟩
    have h1 : φ ⟨a, ha⟩ ∈ commutator H := hel _ ⟨n, hpow a ha n hn⟩
    have h2 : (⟨a, ha⟩ : A) ∈ commutator ↥A := by
      rw [← map_commutator_mulEquiv φ.symm]
      exact ⟨φ ⟨a, ha⟩, h1, φ.symm_apply_apply _⟩
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨⟨a, ha⟩, h2, rfl⟩
  · refine Or.inr fun a ha ⟨n, hn⟩ => ?_
    have h1 := hel (φ ⟨a, ha⟩) ⟨n, hpow a ha n hn⟩
    have h2 : (⟨a, ha⟩ : A) = 1 := (map_eq_one_iff φ φ.injective).1 h1
    exact congrArg Subtype.val h2

private theorem qTameGrp_of_isQuasisimple {H : Type*} [Group H] (h : CFSG.IsQuasisimple H) :
    QTameGrp q H := by
  have h1 : commutator H = ⊤ := Group.isPerfect_def.mp h.1
  refine Or.inl ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((MulEquiv.subgroupCongr h1).trans Subgroup.topEquiv).symm h, fun g _ => ?_⟩
  rw [h1]
  exact Subgroup.mem_top g

private theorem qTameGrp_of_ker {H Ab : Type*} [Group H] [CommGroup Ab] (D : H →* Ab)
    (hq : CFSG.IsQuasisimple ↥D.ker) (hD : ∀ h : H, (∃ n : ℕ, h ^ q ^ n = 1) → D h = 1) :
    QTameGrp q H := by
  have hle : commutator H ≤ D.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  have hge : D.ker ≤ commutator H := by
    have h1 := Subgroup.isPerfect_iff.mp hq.1
    calc D.ker = ⁅D.ker, D.ker⁆ := h1.symm
      _ ≤ ⁅(⊤ : Subgroup H), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator H := (_root_.commutator_def H).symm
  have heq : D.ker = commutator H := le_antisymm hge hle
  refine Or.inl ⟨?_, fun g hg => hge (hD g hg)⟩
  rw [← heq]
  exact hq

private theorem qTameGrp_of_injective {H H' : Type*} [Group H] [Group H'] [Finite H'] (ι : H →* H')
    (hι : Function.Injective ι) (hcop : Nat.Coprime (Nat.card H') q) : QTameGrp q H :=
  Or.inr fun g ⟨n, hn⟩ => (map_eq_one_iff ι hι).1
    (Inputs256e.eq_one_of_coprime_card hcop (by rw [← map_pow, hn, map_one]))

open CFSG.LocalAnalysis.ComponentInitial

private theorem finite_gl {E W : Type*} [Field E] [Finite E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] : Finite (LinearMap.GeneralLinearGroup E W) := by
  have : Finite W := Module.finite_of_finite E
  have : Finite (Module.End E W) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := W →ₗ[E] W))
  exact Finite.of_injective _ Units.val_injective

private theorem qTameGrp_gl {E W : Type*} [Field E] [Finite E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (hq : q.Prime) (hE : ringChar E = q) (h4 : 4 ≤ Nat.card E) :
    QTameGrp q (LinearMap.GeneralLinearGroup E W) := by
  haveI := finite_gl (E := E) (W := W)
  by_cases hm : 2 ≤ Module.finrank E W
  · refine qTameGrp_of_ker (Units.map (LinearMap.det : Module.End E W →* E))
      (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_ker_det hm
        (Or.inr (CFSG.RankThree.PartOne.KCSpIsotypic.exists_finset_card_four_of_card h4)))
      fun g ⟨n, hn⟩ => Inputs256e.eq_one_of_coprime_card (Inputs256e.coprime_card_units hq hE)
        (by rw [← map_pow, hn, map_one])
  · exact qTameGrp_of_injective (MonoidHom.id _) Function.injective_id
      (Inputs256e.coprime_card_gl_of_finrank_le_one hq hE (by omega))

private theorem qTameGrp_unitary {ℓ g : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData ℓ g E)
    (h5 : 5 ≤ ℓ) {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft) :
    QTameGrp ℓ ↥(sesqUnitaryGroup Hf) := by
  haveI := hE.finite
  have hℓ : ℓ.Prime := hE.prime
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP E ℓ := hE.charP
  have hEℓ : ringChar E = ℓ := ringChar.eq E ℓ
  have hQ : 5 ≤ ℓ ^ g := h5.trans (Nat.le_self_pow (by have := hE.one_le; omega) ℓ)
  haveI := finite_gl (E := E) (W := W)
  by_cases hm : 2 ≤ Module.finrank E W
  · obtain ⟨-, -, -, -, hker, -⟩ :=
      CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl rfl (by omega)
    refine qTameGrp_of_ker (CFSG.LinearGroups.unitaryDet Hf) ?_
      fun u ⟨n, hn⟩ => Inputs256e.eq_one_of_coprime_card (Inputs256e.coprime_card_units hℓ hEℓ)
        (by rw [← map_pow, hn, map_one])
    rw [hker]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).symm
      (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf hHfl hm
        ⟨fun _ => by omega, fun _ => by omega⟩)
  · exact qTameGrp_of_injective (sesqUnitaryGroup Hf).subtype Subtype.val_injective
      (Inputs256e.coprime_card_gl_of_finrank_le_one hℓ hEℓ (by omega))

end Tame

section SympInner

open Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {r : ℕ} {K : Type} [Field K]

private theorem qTame_spSupported_of_factor [Finite K] {ℓ f p : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ)
    (hKℓ : ringChar K = ℓ) (hK : Nat.card K = ℓ ^ f) {x : StatedSp r K}
    {a : StatedProj (StatedSp r K)} (hsq : Squarefree (minpoly K (spEnd x)))
    (blocks : SpPrimaryBlocks ℓ f p x a) (h : primaryFactors (spEnd x)) :
    QTame ℓ (spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) := by
  have hK5 : 5 ≤ Nat.card K := by
    rw [hK]
    rcases Nat.eq_zero_or_pos f with hf0 | hf0
    · exfalso
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK, hf0, pow_zero] at h1
      omega
    · exact h5.trans (Nat.le_self_pow (by omega) ℓ)
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  · have hO : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
      rw [hself, Set.pair_eq_singleton]
    rw [hO]
    by_cases h1 : (h : K[X]) = X - 1
    · obtain ⟨h0, hm⟩ := h
      change h0 = X - 1 at h1
      subst h1
      obtain ⟨φ, -⟩ := blocks.fixedFactor hm
      have : Nontrivial (primaryComponent (spEnd x) (X - 1)) :=
        Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hm)
      obtain ⟨s, hs, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp
        (B := (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)))
        (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate
      have hs1 : 1 ≤ s := by
        have := Module.finrank_pos (R := K) (M := primaryComponent (spEnd x) (X - 1))
        omega
      exact qTame_of_mulEquiv (φ.trans e) (qTameGrp_of_isQuasisimple
        (CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs1 (Or.inl (Or.inr (by omega)))))
    · obtain ⟨d, -, -, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, -⟩ :=
        (blocks.selfDual h h1 hself).exists_half
      exact qTame_of_mulEquiv φ (qTameGrp_unitary hE h5 hHf hHfl)
  · have hP := blocks.paired h (fun e => hself e.symm)
    obtain ⟨φ, -, -⟩ := hP.factor
    haveI : Finite (AdjoinRoot (h : K[X])) := Module.finite_of_finite K
    have hEℓ : ringChar (AdjoinRoot (h : K[X])) = ℓ :=
      (Algebra.ringChar_eq K (AdjoinRoot (h : K[X]))).symm.trans hKℓ
    have h4 : 4 ≤ Nat.card (AdjoinRoot (h : K[X])) := by
      have hdeg : 1 ≤ (h : K[X]).natDegree :=
        Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
      have hf1 : 1 ≤ f := by
        rcases Nat.eq_zero_or_pos f with hf0 | hf0
        · exfalso
          have h1 : 1 < Nat.card K := Finite.one_lt_card
          rw [hK, hf0, pow_zero] at h1
          omega
        · exact hf0
      have h1 : ℓ ≤ ℓ ^ f := Nat.le_self_pow (by omega) ℓ
      have h2 : ℓ ^ f ≤ (ℓ ^ f) ^ (h : K[X]).natDegree := Nat.le_self_pow (by omega) _
      rw [hP.card_field]
      omega
    exact qTame_of_mulEquiv φ (qTameGrp_gl hℓ hEℓ h4)

theorem qGen_conj_sp {ℓ f p : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hr : 1 ≤ r) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (x : StatedSp r K) (hx : x ^ p = 1)
    (hx1 : x ≠ 1) : Inputs256e.QGen ℓ (MulAut.conj (SymplecticFlag.proj r K x)) := by
  classical
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero f hℓ.ne_zero
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq0)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI := Fintype.ofFinite K
  have hcardK : Fintype.card K = ℓ ^ f := by rw [Fintype.card_eq_nat_card, hK]
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) hcardK
  have hKℓ : ringChar K = ℓ := ringChar.eq K ℓ
  have hZc : (SymplecticFlag.proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  have hcard2 : Nat.card (SymplecticFlag.proj r K).ker ∣ 2 := by
    rw [SymplecticHigher.ker_proj, card_spScalars_eq_gcd K hr]
    exact Nat.gcd_dvd_left 2 _
  have hZp : Nat.Coprime (Nat.card (SymplecticFlag.proj r K).ker) p :=
    Nat.Coprime.coprime_dvd_left hcard2 ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hZℓ : Nat.Coprime (Nat.card (SymplecticFlag.proj r K).ker) ℓ :=
    Nat.Coprime.coprime_dvd_left hcard2 ((Nat.coprime_primes Nat.prime_two hℓ).mpr (by omega))
  have ha1 : SymplecticFlag.proj r K x ≠ 1 := fun h =>
    hx1 (CFSG.RankThree.Classical.eq_of_map_eq_of_pow_eq_one_of_coprime (a := 1) (b := 0)
      (SymplecticFlag.proj r K) hZc hZp (by rwa [pow_one]) (by simp) (by rw [h, map_one]))
  have ha : orderOf (SymplecticFlag.proj r K x) = p :=
    orderOf_eq_prime (by rw [← map_pow, hx, map_one]) ha1
  have hxp : orderOf x = p := orderOf_eq_prime hx hx1
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks hℓ hf hK hp hp2 hpℓ hr _
    ha).2 x rfl hxp
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K ℓ] at h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h).symm
  have hsq := (altPrimaryData_spLin hpK hx).squarefree
  haveI : Finite (reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  set A : reciprocalOrbits (spEnd x) → Subgroup (StatedSp r K) :=
    fun O => spSupported x (O : Set K[X]) with hA
  have htame : ∀ O, QTame ℓ (A O) := by
    rintro ⟨O, h, hh, rfl⟩
    exact qTame_spSupported_of_factor hℓ h5 hKℓ hK hsq blocks ⟨h, hh⟩
  set N : Subgroup (StatedSp r K) :=
    ⨆ O : {O : reciprocalOrbits (spEnd x) // CFSG.IsQuasisimple ↥⁅A O, A O⁆}, ⁅A O.1, A O.1⁆
    with hN
  have hfix : fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set (StatedSp r K)) := by
    ext g
    rw [mem_fixSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hNperf : ⁅N, N⁆ = N :=
    commutator_iSup_eq _ fun O => commutator_self_of_perfect (Group.isPerfect_def.mp O.2.1)
  have hNC : N ≤ fixSubgroup (MulAut.conj x) := by
    rw [hfix, ← hjoin]
    exact iSup_le fun O => (commutator_le_self' _).trans (le_iSup A O.1)
  have hgen : ∀ y ∈ fixSubgroup (MulAut.conj x), (∃ n : ℕ, y ^ ℓ ^ n = 1) → y ∈ N := by
    rintro y hy ⟨n, hn⟩
    rw [hfix, ← hjoin] at hy
    refine mem_of_mem_iSup_commute hℓ A
      (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb) N
      (fun O a ha haq => ?_) hy hn
    rcases htame O with ⟨hq, hel⟩ | hel
    · exact (le_iSup (fun O : {O : reciprocalOrbits (spEnd x) //
        CFSG.IsQuasisimple ↥⁅A O, A O⁆} => ⁅A O.1, A O.1⁆) ⟨O, hq⟩) (hel a ha haq)
    · rw [hel a ha haq]
      exact N.one_mem
  refine qGen_of_lieCompsExport
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsExport_conj_sp
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFourTwoFacts_holds hp hp2 hℓ hf hK hr hpℓ x
      hx) ?_
  exact exists_perfect_of_centralQuotient (SymplecticFlag.proj r K) SymplecticHigher.proj_surjective
    hZc hZℓ (MulAut.conj x) (MulAut.conj (SymplecticFlag.proj r K x))
    (fun g => by simp [MulAut.conj_apply]) hNC hNperf hgen

end SympInner

section SympOuter

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

variable {r : ℕ} {K : Type} [Field K]

theorem ringChar_eq_of_card {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hK : Nat.card K = ℓ ^ f) : ringChar K = ℓ := by
  haveI := Fintype.ofFinite K
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  exact ringChar.eq K ℓ

theorem qGen_fieldAut_sp [Finite K] {ℓ : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) (hKℓ : ringChar K = ℓ)
    (hr : 2 ≤ r) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    Inputs256e.QGen ℓ (fieldAut r K σ) := by
  haveI : NeZero r := ⟨by omega⟩
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hfix : fixSubgroup (fieldAut r K σ) =
      (CFSG.RankThree.PartOne.KCSpComm.subfieldInj (r := r) σ).range := by
    rw [CFSG.RankThree.PartOne.KCSpComm.range_subfieldInj,
      ← CFSG.RankThree.PartOne.KCSpComm.spFixedGroup_fieldAut_eq_range (hp.odd_of_ne_two hp2) hσp]
    exact Subgroup.ext fun x =>
      mem_fixSubgroup.trans CFSG.RankThree.PartOne.KCSpComm.mem_spFixedGroup.symm
  have hchar : ringChar (descentField σ) = ℓ := by rw [Algebra.ringChar_eq (descentField σ) K, hKℓ]
  obtain ⟨j, hj, hcard⟩ := Inputs256e.exists_card_eq_pow hℓ hchar
  have hne : ¬(r = 2 ∧ Nat.card (descentField σ) = 2) := fun ⟨_, h2⟩ => by
    have : ℓ ≤ ℓ ^ j := Nat.le_self_pow (by omega) ℓ
    omega
  obtain ⟨-, hperf⟩ := CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj
    (k := descentField σ) hr hne
  have hβ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsExport_fieldAut_sp
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFourTwoFacts_holds hp hp2 hr σ hσ
  rw [hKℓ] at hβ
  refine qGen_of_lieCompsExport hβ fun s hs _ => ⟨fixSubgroup (fieldAut r K σ), le_rfl, ?_,
    mem_fixSubgroup.2 hs⟩
  rw [hfix, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
    hperf.commutator_eq_top]

private theorem center_eq_bot_of_simple_perfect {T : Type*} [Group T] (hs : IsSimpleGroup T)
    (hperf : Group.IsPerfect T) : Subgroup.center T = ⊥ := by
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    have hcomm : commutator T = ⊥ := by
      rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro g _
      rw [Subgroup.mem_centralizer_iff]
      intro k _
      have : k ∈ Subgroup.center T := h ▸ Subgroup.mem_top k
      exact (Subgroup.mem_center_iff.mp this g).symm
    have htop : (⊤ : Subgroup T) = ⊥ := by rw [← hcomm]; exact hperf.commutator_eq_top.symm
    obtain ⟨a, b, hab⟩ := exists_pair_ne T
    have ha : a ∈ (⊥ : Subgroup T) := htop ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup T) := htop ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    exact hab (ha.trans hb.symm)

theorem qGen_projSp {ℓ f p : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hr : 2 ≤ r) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (β : MulAut (StatedProj (StatedSp r K)))
    (hβ : orderOf β = p) : Inputs256e.QGen ℓ β := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  have hβp : β ^ p = 1 := by rw [← hβ]; exact pow_orderOf_eq_one β
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := K) hℓ hf hr hK
  have hodd : Odd (orderOf β) := by rw [hβ]; exact hp.odd_of_ne_two hp2
  have hE : β ∈ spSemilinearAutGroup r K :=
    CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  have hK5 : 5 ≤ Nat.card K := by
    rw [hK]
    exact h5.trans (Nat.le_self_pow (by omega) ℓ)
  by_cases hD : β ∈ spLinearAutGroup r K
  · have : (inner (StatedProj (StatedSp r K))).Normal := inner_normal _
    have hrel : (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    obtain ⟨t, rfl⟩ := CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two hrel
      hp hp2 hD hβp
    obtain ⟨hsimple, hperf⟩ := CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := K) hr
      (fun h => by omega)
    have ht : t ^ p = 1 := by
      have hc : t ^ p ∈ Subgroup.center (StatedProj (StatedSp r K)) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h1 := congrArg (fun φ : MulAut (StatedProj (StatedSp r K)) => φ g)
          (show MulAut.conj (t ^ p) = 1 by rw [map_pow]; exact hβp)
        simp only [MulAut.conj_apply, MulAut.one_apply] at h1
        calc g * t ^ p = t ^ p * g * (t ^ p)⁻¹ * t ^ p := by rw [h1]
          _ = t ^ p * g := by group
      rw [center_eq_bot_of_simple_perfect hsimple hperf, Subgroup.mem_bot] at hc
      exact hc
    obtain ⟨x, hx, hxp⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_proj_eq_pow_eq_one_sp (by omega)
        hp hp2 ht
    have hx1 : x ≠ 1 := by
      rintro rfl
      rw [map_one] at hx
      subst hx
      rw [map_one, orderOf_one] at hβ
      exact hp.one_lt.ne hβ
    rw [← hx]
    exact qGen_conj_sp hℓ h5 hf hK (by omega) hp hp2 hpℓ x hxp hx1
  · obtain ⟨-, σ, hσ, h, -, hβeq⟩ := hO.descent p hp β hE hD hβ
    rw [hβeq]
    exact Inputs256e.qGen_conj h _
      (qGen_fieldAut_sp hℓ h5 (ringChar_eq_of_card hℓ hK) hr hp hp2 σ hσ)

end SympOuter

section Catalogue

open TauCeti
open CFSG.LieType.SeitzGeneration (Cat)

@[expose] def QGenOrth : Prop :=
  Inputs256e.QGenOn fun d => (∃ r Q, d.1 = .B r Q ∧ 3 ≤ r) ∨ (∃ r Q, d.1 = .D r Q) ∨
    ∃ r Q, d.1 = .twistedD r Q

theorem orderOf_congr {S T : Type} [Group S] [Group T] (e : S ≃* T) (β : MulAut S) :
    orderOf (MulAut.congr e β) = orderOf β :=
  orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective β

theorem qGenSympOrth_of_orth (hO : QGenOrth) : Inputs256e.QGenSympOrth := by
  rintro ⟨d, hv⟩ hF hd5 p hp hp2 hpd β hβ
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | B r Q =>
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · have : Fact Q.p.Prime := ⟨Q.prime_p⟩
      have hK : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B 2 Q, hv⟩) = Q.p ^ Q.exponent :=
        CFSG.Models.card_fixedField_of (LieTypeIndex.characteristic_B 2 Q)
          (LieTypeIndex.fieldExponent_B 2 Q)
      have hQc : (LieTypeIndex.B 2 Q).characteristic = Q.p := LieTypeIndex.characteristic_B 2 Q
      change 5 ≤ (LieTypeIndex.B 2 Q).characteristic at hd5
      change p ≠ (LieTypeIndex.B 2 Q).characteristic at hpd
      change Inputs256e.QGen (LieTypeIndex.B 2 Q).characteristic β
      rw [hQc] at hd5 hpd ⊢
      let e : Cat ⟨.B 2 Q, hv⟩ ≃*
          StatedProj (StatedSp 2 ↥(ValidLieTypeIndex.fixedField ⟨.B 2 Q, hv⟩)) :=
        CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj Q hv
      exact Inputs256e.qGen_of_congr e β (qGen_projSp Q.prime_p hd5 Q.exponent_pos hK le_rfl hp hp2
        hpd _ (by rw [orderOf_congr, hβ]))
    · exact hO ⟨_, hv⟩ (Or.inl ⟨r, Q, rfl, hr3⟩) hd5 p hp hp2 hpd β hβ
  | C r Q =>
    have : Fact Q.p.Prime := ⟨Q.prime_p⟩
    have hK : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.C r Q, hv⟩) = Q.p ^ Q.exponent :=
      CFSG.Models.card_fixedField_of (LieTypeIndex.characteristic_C r Q)
        (LieTypeIndex.fieldExponent_C r Q)
    have hQc : (LieTypeIndex.C r Q).characteristic = Q.p := LieTypeIndex.characteristic_C r Q
    change 5 ≤ (LieTypeIndex.C r Q).characteristic at hd5
    change p ≠ (LieTypeIndex.C r Q).characteristic at hpd
    change Inputs256e.QGen (LieTypeIndex.C r Q).characteristic β
    rw [hQc] at hd5 hpd ⊢
    have hr2 : 2 ≤ r := by
      simp only at hr
      omega
    let e : Cat ⟨.C r Q, hv⟩ ≃*
        StatedProj (StatedSp r ↥(ValidLieTypeIndex.fixedField ⟨.C r Q, hv⟩)) :=
      CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r Q hv
    exact Inputs256e.qGen_of_congr e β (qGen_projSp Q.prime_p hd5 Q.exponent_pos hK hr2 hp hp2 hpd
      _ (by rw [orderOf_congr, hβ]))
  | D r Q => exact hO ⟨_, hv⟩ (Or.inr (Or.inl ⟨r, Q, rfl⟩)) hd5 p hp hp2 hpd β hβ
  | twistedD r Q => exact hO ⟨_, hv⟩ (Or.inr (Or.inr ⟨r, Q, rfl⟩)) hd5 p hp hp2 hpd β hβ
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hF

end Catalogue

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256f

end
