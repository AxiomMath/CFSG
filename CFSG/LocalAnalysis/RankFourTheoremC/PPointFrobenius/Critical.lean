module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.RepHyp
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.RepHypBil
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.TorusData
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.LiftData
public import CFSG.LocalAnalysis.RankThreeTheoremC.OddCriticalNormal
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open CFSG.Open Subgroup
open scoped MatrixGroups commutatorElement

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

section Actions

variable {J : Type} [Group J]

@[instance_reducible] private def conjAction (D : Subgroup J) [D.Normal] :
    MulDistribMulAction J D :=
  MulDistribMulAction.compHom D (MulAut.conjNormal : J →* MulAut D)

private theorem smul_mem_center {D : Type*} [Group D] [MulDistribMulAction J D] (g : J) {z : D}
    (hz : z ∈ Subgroup.center D) : g • z ∈ Subgroup.center D := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro d
  have h : d = g • (g⁻¹ • d) := (smul_inv_smul g d).symm
  rw [h, ← smul_mul', ← smul_mul', hz]

@[instance_reducible] private def centerAction {D : Type*} [Group D] [MulDistribMulAction J D] :
    MulDistribMulAction J (Subgroup.center D) where
  smul g z := ⟨g • (z : D), smul_mem_center g z.2⟩
  one_smul z := Subtype.ext (one_smul J (z : D))
  mul_smul g h z := Subtype.ext (mul_smul g h (z : D))
  smul_mul g a b := Subtype.ext (smul_mul' g (a : D) (b : D))
  smul_one g := Subtype.ext (smul_one g)

@[instance_reducible] private def quotientAction {D : Type*} [Group D]
    [MulDistribMulAction J D] (N : Subgroup D) [N.Normal] (hN : ∀ (g : J), ∀ x ∈ N, g • x ∈ N) :
    MulDistribMulAction J (D ⧸ N) where
  smul g q := QuotientGroup.map N N (MulDistribMulAction.toMonoidHom D g) (hN g) q
  one_smul q := by
    induction q using QuotientGroup.induction_on with
    | H x =>
      change (((1 : J) • x : D) : D ⧸ N) = x
      rw [one_smul]
  mul_smul g h q := by
    induction q using QuotientGroup.induction_on with
    | H x =>
      change (((g * h) • x : D) : D ⧸ N) = ((g • (h • x) : D) : D ⧸ N)
      rw [mul_smul]
  smul_mul g a b := map_mul (QuotientGroup.map N N (MulDistribMulAction.toMonoidHom D g) (hN g)) a b
  smul_one g := map_one (QuotientGroup.map N N (MulDistribMulAction.toMonoidHom D g) (hN g))

private theorem isElementaryAbelian_center (q : ℕ) {D : Type*} [Group D]
    (hexp : ∀ d : D, d ^ q = 1) :
    IsElementaryAbelian q (Subgroup.center D) where
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun z => Subtype.ext (by
    simpa using hexp z)

private theorem isElementaryAbelian_quotient_center (q : ℕ) {D : Type*} [Group D]
    (hexp : ∀ d : D, d ^ q = 1) (hcl : ∀ a b : D, ⁅a, b⁆ ∈ Subgroup.center D) :
    IsElementaryAbelian q (D ⧸ Subgroup.center D) where
  is_comm := ⟨fun a b => by
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have := hcl y⁻¹ x⁻¹
        simpa [commutatorElement_def, mul_assoc] using this⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
    induction a using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, hexp x]
      rfl

private theorem smul_eq_of_inv_smul_mem_center {D : Type*} [Group D] [MulDistribMulAction J D]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hexp : ∀ d : D, d ^ q = 1) {u : J}
    (hu : u ^ p = 1) (hZ : ∀ z ∈ Subgroup.center D, u • z = z)
    (hx : ∀ x : D, x⁻¹ * (u • x) ∈ Subgroup.center D) (x : D) : u • x = x := by
  set z : D := x⁻¹ * (u • x) with hz
  have hzc : u • z = z := hZ z (hx x)
  have hux : u • x = x * z := by rw [hz, mul_inv_cancel_left]
  have hk : ∀ k : ℕ, (u ^ k) • x = x * z ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_smul, ih, smul_mul', hux, smul_pow', hzc, pow_succ', mul_assoc]
  have hzp : z ^ p = 1 := by
    have := hk p
    rw [hu, one_smul] at this
    exact (mul_eq_left.mp this.symm)
  have hzq : z ^ q = 1 := hexp z
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hz1 : z = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hzp, hzq⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  rw [hux, hz1, mul_one]

private theorem le_card_center_of_exponent {D : Type*} [Group D] [Finite D] [Nontrivial D] (q : ℕ)
    [Fact q.Prime] (hexp : ∀ d : D, d ^ q = 1) : q ≤ Nat.card (Subgroup.center D) := by
  have hpg : IsPGroup q D := fun d => ⟨1, by simpa using hexp d⟩
  have : Nontrivial (Subgroup.center D) := hpg.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center D)
  have hzq : z ^ q = 1 := Subtype.ext (by simpa using hexp z)
  have hord : orderOf z = q :=
    (Nat.dvd_prime Fact.out).1 (orderOf_dvd_of_pow_eq_one hzq) |>.resolve_left
      (fun h => hz (orderOf_eq_one_iff.mp h))
  have hdvd := Subgroup.orderOf_dvd_natCard (Subgroup.center D) z.2
  rw [Subgroup.orderOf_coe, hord] at hdvd
  exact Nat.le_of_dvd Nat.card_pos hdvd

end Actions

private theorem isElemAbelian_map_subtype {J : Type} [Group J] (D : Subgroup J) (q : ℕ)
    (E : Subgroup D) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ d : D, d ^ q = 1) :
    IsElemAbelian q (E.map D.subtype) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    apply Subtype.ext
    change (x : J) * y = y * x
    exact congrArg Subtype.val (hcomm x hx y hy)
  · rintro _ ⟨x, -, rfl⟩
    rw [Subgroup.subtype_apply, ← Subgroup.coe_pow, hexp x, Subgroup.coe_one]

private theorem isElemAbelian_map_hom {G H : Type*} [Group G] [Group H] {q : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian q E) (f : G →* H) :
    IsElemAbelian q (E.map f) := by
  exact CFSG.Open.IsElemAbelian.map hE f

private theorem isPGroup_of_isElemAbelian {G : Type*} [Group G] {q : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian q E) : IsPGroup q E :=
  fun y => ⟨1, Subtype.ext (by simpa using hE.2 y y.2)⟩

theorem exists_rank_four_of_critical {J : Type} [Group J] [Finite J] {p q n : ℕ} [Fact p.Prime]
    [Fact q.Prime] (hpq : p ≠ q) (hn : 2 ≤ n) {D : Subgroup J} [D.Normal] (hD1 : D ≠ ⊥)
    (hDexp : ∀ x ∈ D, x ^ q = 1) (hDcl : ⁅⁅D, D⁆, D⁆ = ⊥) {U : Subgroup J}
    (hU : Nat.card U = p ^ n) (hUexp : ∀ u ∈ U, u ^ p = 1)
    (hUcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) {σ : J} (hσ : MovesHyperplanes p U σ)
    (hUD : ⁅U, D⁆ ≠ ⊥) :
    ∃ E : Subgroup J, E ≤ D ∧ CFSG.Open.IsElemAbelian q E ∧ q ^ 4 ≤ Nat.card E := by
  classical
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  let actD : MulDistribMulAction J D := conjAction D
  have hexpD : ∀ d : D, d ^ q = 1 := fun d => Subtype.ext (by simpa using hDexp d d.2)
  have hclD : ∀ a b : D, ⁅a, b⁆ ∈ Subgroup.center D := by
    intro a b
    rw [Subgroup.mem_center_iff]
    intro c
    have h3 : ⁅⁅(a : J), (b : J)⁆, (c : J)⁆ ∈ ⁅⁅D, D⁆, D⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator a.2 b.2) c.2
    rw [hDcl, Subgroup.mem_bot] at h3
    apply Subtype.ext
    exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
  have : IsElementaryAbelian q (Subgroup.center D) := isElementaryAbelian_center q hexpD
  have : IsElementaryAbelian q (D ⧸ Subgroup.center D) :=
    isElementaryAbelian_quotient_center q hexpD hclD
  let actZ : MulDistribMulAction J (Subgroup.center D) := centerAction
  let actQ : MulDistribMulAction J (D ⧸ Subgroup.center D) :=
    quotientAction (Subgroup.center D) (fun g x hx => smul_mem_center g hx)
  have hcompat : ∀ (g : J) (x : D),
      g • (x : D ⧸ Subgroup.center D) = ((g • x : D) : D ⧸ Subgroup.center D) := fun g x => rfl
  have : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).mpr hD1
  by_cases hUZ : ∀ u ∈ U, ∀ z ∈ Subgroup.center D, u • z = z
  ·
    have hnt : ∃ u ∈ U, ∃ x : D,
        u • (x : D ⧸ Subgroup.center D) ≠ (x : D ⧸ Subgroup.center D) := by
      by_contra hcon
      push Not at hcon
      apply hUD
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have key : u • (⟨d, hd⟩ : D) = ⟨d, hd⟩ := by
        refine smul_eq_of_inv_smul_mem_center hp hq hpq hexpD (hUexp u hu) (hUZ u hu) ?_
          ⟨d, hd⟩
        intro x
        have h2 : (x : D ⧸ Subgroup.center D) = (((u • x : D)) : D ⧸ Subgroup.center D) :=
          (hcon u hu x).symm
        rw [QuotientGroup.eq] at h2
        exact h2
      have h3 : u * d * u⁻¹ = d := congrArg Subtype.val key
      calc d * u = (u * d * u⁻¹) * u := by rw [h3]
        _ = u * d := by group
    obtain ⟨E, hEcomm, -, hEcard⟩ :=
      exists_abelian_of_hyperplane_action hpq hn hclD hcompat hU hUexp hUcomm hσ hUZ hnt
    have hab := isElemAbelian_map_subtype D q E hEcomm hexpD
    have hZ := le_card_center_of_exponent (D := D) q hexpD
    refine ⟨E.map D.subtype, Subgroup.map_subtype_le E, hab, ?_⟩
    rw [Subgroup.card_map_of_injective D.subtype_injective]
    calc q ^ 4 = q ^ 3 * q := by ring
      _ ≤ q ^ 3 * Nat.card (Subgroup.center D) := Nat.mul_le_mul_left _ hZ
      _ ≤ Nat.card E := hEcard
  ·
    push Not at hUZ
    obtain ⟨u, hu, z, hz, hne⟩ := hUZ
    have h4 := four_le_card_of_hyperplane_action (J := J) (A := Subgroup.center D) hpq hn hU
      hUexp hUcomm hσ ⟨u, hu, ⟨z, hz⟩, fun h => hne (congrArg Subtype.val h)⟩
    have hab := isElemAbelian_map_subtype D q (Subgroup.center D)
      (fun x _ y hy => Subgroup.mem_center_iff.mp hy x) hexpD
    refine ⟨(Subgroup.center D).map D.subtype, Subgroup.map_subtype_le _, hab, ?_⟩
    rw [Subgroup.card_map_of_injective D.subtype_injective]
    exact h4

theorem criticalRankFour :
    ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (n : ℕ), 3 ≤ n →
      ∀ J O : Subgroup X, O ≤ J → Odd (Nat.card O) → ¬ p ∣ Nat.card O → ⁅J, J⁆ = J →
      ∀ (Q : Type) [Group Q] (ψ : ↥J →* Q), Function.Surjective ψ → ψ.ker = O.subgroupOf J →
      Nonempty (Q ≃* PSL(2, GaloisField p n)) → ⁅J, O⁆ ≠ ⊥ →
      ∃ (q : ℕ) (D : Subgroup X), q.Prime ∧ D ≤ O ∧ (D.subgroupOf J).Normal ∧ IsPGroup q D ∧
        4 ≤ CFSG.Open.pRank q D := by
  intro X _ _ p _ hp5 n hn J O hOJ hodd hpO hperf Q _ ψ hψ hker he hO0
  obtain ⟨e⟩ := he
  have hp : p.Prime := Fact.out
  have hcard : Nat.card ψ.ker = Nat.card O := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv
  have hodd' : Odd (Nat.card ψ.ker) := hcard ▸ hodd
  have hpk : ¬ p ∣ Nat.card ψ.ker := hcard ▸ hpO
  have hperf' : commutator ↥J = ⊤ := (Subgroup.isPerfect_iff.mpr hperf).commutator_eq_top
  have hsolv : Group.IsSolvable ψ.ker := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
  have hO : ⁅(⊤ : Subgroup ↥J), ψ.ker⁆ ≠ ⊥ := by
    intro h
    apply hO0
    have h1 := congrArg (Subgroup.map J.subtype) h
    rw [Subgroup.map_commutator, Subgroup.map_bot, hker, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hOJ, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    exact h1
  obtain ⟨U₀, σ₀, hU₀card, hU₀exp, hU₀comm, hσ₀⟩ := psl2_torus_data_hyperplane p hp5 n hn
  let π : ↥J →* PSL(2, GaloisField p n) := e.toMonoidHom.comp ψ
  have hπ : Function.Surjective π := e.surjective.comp hψ
  have hπker : π.ker = ψ.ker := by
    ext x
    simp [π, MonoidHom.mem_ker]
  obtain ⟨U, σ, hUcard, hUexp, hUcomm, hUinj, hσ⟩ :=
    exists_hyperplane_data π hπ (by rw [hπker]; exact hpk) U₀ σ₀ hU₀card hU₀exp hU₀comm hσ₀
  have hK : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField p n) := by
    rw [hK]
    have h1 : p ^ 1 < p ^ n := Nat.pow_lt_pow_right hp.one_lt (by omega)
    rw [pow_one] at h1
    exact le_trans (by omega) h1.le
  have hsimple : IsSimpleGroup Q := by
    have : IsSimpleGroup PSL(2, GaloisField p n) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    exact e.isSimpleGroup
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : U = ⊥ := (Subgroup.eq_bot_iff_forall U).mpr hcon
    rw [this, Subgroup.card_bot] at hUcard
    have : 1 < p ^ n := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  have hJ : Subgroup.normalClosure (U : Set ↥J) ⊔ ψ.ker = ⊤ := by
    set K := Subgroup.normalClosure (U : Set ↥J) with hKdef
    have hKn : (K.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
    have hKne : K.map ψ ≠ ⊥ := by
      intro hbot
      have hu' : ψ u = 1 := by
        have hmem : ψ u ∈ K.map ψ :=
          Subgroup.mem_map_of_mem ψ (Subgroup.subset_normalClosure hu)
        rw [hbot] at hmem
        exact Subgroup.mem_bot.mp hmem
      apply hu1
      apply hUinj u hu
      show e (ψ u) = 1
      rw [hu', map_one]
    have htop : K.map ψ = ⊤ := by
      have := hKn
      exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map ψ)).resolve_left hKne
    rw [eq_top_iff]
    intro g _
    have hg : ψ g ∈ K.map ψ := htop ▸ Subgroup.mem_top _
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hg
    have hker' : k⁻¹ * g ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkg, inv_mul_cancel]
    have := Subgroup.mul_mem_sup hk hker'
    simpa using this
  have hUp : IsPGroup p U := IsPGroup.of_card (n := n) hUcard
  obtain ⟨q, D, hq, -, hqp, hDn, hD1, hDO, hDexp, hDcl, hUD⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_critical_normal hsolv hodd' hO hpk hUp hJ hperf'
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨E, hED, hEab, hEcard⟩ :=
    exists_rank_four_of_critical hqp.symm (by omega) hD1 hDexp hDcl hUcard hUexp hUcomm hσ hUD
  obtain ⟨m, hm⟩ := (isPGroup_of_isElemAbelian hEab).exists_card_eq
  have hm4 : 4 ≤ m := by
    by_contra hlt
    push Not at hlt
    have h5 : q ^ m < q ^ 4 := Nat.pow_lt_pow_right hq.one_lt hlt
    rw [hm] at hEcard
    exact absurd hEcard (not_le.mpr h5)
  refine ⟨q, D.map J.subtype, hq, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have h1 : x ∈ ψ.ker := hDO hx
    rw [hker, Subgroup.mem_subgroupOf] at h1
    exact h1
  · have hsub : (D.map J.subtype).subgroupOf J = D :=
      Subgroup.comap_map_eq_self_of_injective J.subtype_injective D
    rw [hsub]
    exact hDn
  · have hexpX : ∀ y ∈ D.map J.subtype, y ^ q = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hDexp x hx, map_one]
    exact fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hexpX g g.2)⟩
  · have hcardE : Nat.card (E.map J.subtype) = q ^ m :=
      (Subgroup.card_map_of_injective J.subtype_injective).trans hm
    have hbdd : BddAbove {k | ∃ F : Subgroup X, F ≤ D.map J.subtype ∧
        CFSG.Open.IsElemAbelian q F ∧ Nat.card F = q ^ k} := by
      refine ⟨Nat.card X, ?_⟩
      rintro k ⟨F, -, -, hF⟩
      have h1 : k < q ^ k := Nat.lt_pow_self hq.one_lt
      have h2 : Nat.card F ≤ Nat.card X := Subgroup.card_le_card_group F
      rw [hF] at h2
      exact le_trans h1.le h2
    have hle : m ≤ CFSG.Open.pRank q (D.map J.subtype) := by
      unfold CFSG.Open.pRank
      exact le_csSup hbdd ⟨E.map J.subtype, Subgroup.map_mono hED,
        isElemAbelian_map_hom hEab J.subtype, hcardE⟩
    exact le_trans hm4 hle

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
