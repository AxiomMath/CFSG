module

public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneModuleActions
public import CFSG.LocalAnalysis.RankThreeTheoremC.Psl2TorusData
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneDataLift
public import CFSG.LocalAnalysis.RankThreeTheoremC.OddCriticalNormal
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open scoped MatrixGroups commutatorElement

section Actions

variable {J : Type} [Group J]

@[expose, instance_reducible] def conjAction (D : Subgroup J) [D.Normal] :
    MulDistribMulAction J D :=
  MulDistribMulAction.compHom D (MulAut.conjNormal : J →* MulAut D)

theorem smul_mem_center {D : Type*} [Group D] [MulDistribMulAction J D] (g : J) {z : D}
    (hz : z ∈ Subgroup.center D) : g • z ∈ Subgroup.center D := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro d
  have h : d = g • (g⁻¹ • d) := (smul_inv_smul g d).symm
  rw [h, ← smul_mul', ← smul_mul', hz]

@[expose, instance_reducible] def centerAction {D : Type*} [Group D] [MulDistribMulAction J D] :
    MulDistribMulAction J (Subgroup.center D) where
  smul g z := ⟨g • (z : D), smul_mem_center g z.2⟩
  one_smul z := Subtype.ext (one_smul J (z : D))
  mul_smul g h z := Subtype.ext (mul_smul g h (z : D))
  smul_mul g a b := Subtype.ext (smul_mul' g (a : D) (b : D))
  smul_one g := Subtype.ext (smul_one g)

@[expose, instance_reducible] def quotientAction {D : Type*} [Group D]
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

theorem isElementaryAbelian_center (q : ℕ) {D : Type*} [Group D] (hexp : ∀ d : D, d ^ q = 1) :
    IsElementaryAbelian q (Subgroup.center D) where
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun z => Subtype.ext (by
    simpa using hexp z)

theorem isElementaryAbelian_quotient_center (q : ℕ) {D : Type*} [Group D]
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

theorem smul_eq_of_inv_smul_mem_center {D : Type*} [Group D] [MulDistribMulAction J D] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hexp : ∀ d : D, d ^ q = 1) {u : J}
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

theorem isElemAbelian_map_subtype {J : Type} [Group J] (D : Subgroup J) (q : ℕ)
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

theorem le_card_center_of_exponent {D : Type*} [Group D] [Finite D] [Nontrivial D] (q : ℕ)
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

theorem false_of_critical {J : Type} [Group J] [Finite J] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp5 : 5 ≤ p) (hpq : p ≠ q) {D : Subgroup J} [D.Normal] (hD1 : D ≠ ⊥)
    (hDexp : ∀ x ∈ D, x ^ q = 1) (hDcl : ⁅⁅D, D⁆, D⁆ = ⊥)
    (hrank : ∀ E : Subgroup J, E ≤ D → IsElemAbelian q E → Nat.card E ≤ q ^ 3)
    {U : Subgroup J} (hU : Nat.card U = p ^ 2) (hUexp : ∀ u ∈ U, u ^ p = 1)
    (hUcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) {τ σ : J}
    (hτ : τ ∈ Subgroup.normalizer (U : Set J)) (hτinv : ∀ u ∈ U, τ * u * τ⁻¹ = u⁻¹)
    (hσ : σ ∈ Subgroup.normalizer (U : Set J))
    (hσ1 : ∀ H : Subgroup J, H ≤ U → Nat.card H = p → ∃ h ∈ H, σ * h * σ⁻¹ ∉ H)
    (hσ2 : ∀ H : Subgroup J, H ≤ U → Nat.card H = p →
      ∃ h ∈ H, σ * (σ * h * σ⁻¹) * σ⁻¹ ∉ H)
    (hUD : ⁅U, D⁆ ≠ ⊥) : False := by
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
    obtain ⟨E, hEcomm, -, hEcard⟩ := exists_abelian_of_action hpq hclD hcompat hU hUexp hUcomm hσ
      hσ1 hσ2 hUZ hnt
    have hab := isElemAbelian_map_subtype D q E hEcomm hexpD
    have hcard : Nat.card (E.map D.subtype) = Nat.card E :=
      Subgroup.card_map_of_injective D.subtype_injective
    have h1 := hrank _ (Subgroup.map_subtype_le E) hab
    have hZ := le_card_center_of_exponent (D := D) q hexpD
    rw [hcard] at h1
    have h2 : q ^ 3 * q ≤ q ^ 3 * 1 :=
      calc q ^ 3 * q ≤ q ^ 3 * Nat.card (Subgroup.center D) := Nat.mul_le_mul_left _ hZ
        _ ≤ Nat.card E := hEcard
        _ ≤ q ^ 3 := h1
        _ = q ^ 3 * 1 := (mul_one _).symm
    have := Nat.le_of_mul_le_mul_left h2 (pow_pos hq.pos 3)
    exact hq.one_lt.ne' (le_antisymm this hq.one_lt.le)
  ·
    push Not at hUZ
    obtain ⟨u, hu, z, hz, hne⟩ := hUZ
    have h4 := four_le_card_of_action (J := J) (A := Subgroup.center D) hpq hp5 hU hUexp hUcomm
      hτ hτinv hσ hσ1 hσ2 ⟨u, hu, ⟨z, hz⟩, fun h => hne (congrArg Subtype.val h)⟩
    have hab := isElemAbelian_map_subtype D q (Subgroup.center D)
      (fun x _ y hy => Subgroup.mem_center_iff.mp hy x) hexpD
    have hcard : Nat.card ((Subgroup.center D).map D.subtype) = Nat.card (Subgroup.center D) :=
      Subgroup.card_map_of_injective D.subtype_injective
    have h1 := hrank _ (Subgroup.map_subtype_le _) hab
    rw [hcard] at h1
    have h5 : q ^ 3 < q ^ 4 := Nat.pow_lt_pow_right hq.one_lt (by norm_num)
    omega

end Actions

section Core

theorem central_of_rank_le_three_psl_core {J Q : Type} [Group J] [Finite J] [Group Q] {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (ψ : J →* Q) (hψ : Function.Surjective ψ)
    (hodd : Odd (Nat.card ψ.ker)) (hpk : ¬ p ∣ Nat.card ψ.ker) (hperf : commutator J = ⊤)
    (hsolv : Group.IsSolvable ψ.ker) (e : Q ≃* PSL(2, GaloisField p 2))
    (hrank : ∀ q : ℕ, q.Prime → ∀ E : Subgroup J, E ≤ ψ.ker → IsElemAbelian q E →
      Nat.card E ≤ q ^ 3) :
    ψ.ker ≤ Subgroup.center J := by
  by_contra hcen
  have hO : ⁅(⊤ : Subgroup J), ψ.ker⁆ ≠ ⊥ := by
    intro h
    apply hcen
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro g
    have hmem : ⁅g, k⁆ ∈ ⁅(⊤ : Subgroup J), ψ.ker⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top g) hk
    rw [h, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  have hK : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
  obtain ⟨U₀, τ₀, σ₀, hU₀card, hU₀exp, hU₀comm, hτ₀, hτ₀inv, hσ₀, hσ₀1, hσ₀2⟩ :=
    psl2_torus_data p hp5
  let π : J →* PSL(2, GaloisField p 2) := e.toMonoidHom.comp ψ
  have hπ : Function.Surjective π := e.surjective.comp hψ
  have hπker : π.ker = ψ.ker := by
    ext x
    simp [π, MonoidHom.mem_ker]
  obtain ⟨U, τ, σ, hUcard, hUexp, hUcomm, hUinj, hτ, hτinv, hσ, hσ1, hσ2⟩ :=
    exists_plane_data π hπ (by rw [hπker]; exact hpk) U₀ τ₀ σ₀ hU₀card hU₀exp hU₀comm hτ₀
      hτ₀inv hσ₀ hσ₀1 hσ₀2
  have hsimple : IsSimpleGroup Q := by
    have : IsSimpleGroup PSL(2, GaloisField p 2) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hK]; nlinarith)
    exact e.isSimpleGroup
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : U = ⊥ := (Subgroup.eq_bot_iff_forall U).mpr hcon
    rw [this, Subgroup.card_bot] at hUcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) (Fact.out : p.Prime).one_lt
    omega
  have hJ : Subgroup.normalClosure (U : Set J) ⊔ ψ.ker = ⊤ := by
    set K := Subgroup.normalClosure (U : Set J) with hKdef
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
    have hker : k⁻¹ * g ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkg, inv_mul_cancel]
    have := Subgroup.mul_mem_sup hk hker
    simpa using this
  have hUp : IsPGroup p U := IsPGroup.of_card (n := 2) hUcard
  obtain ⟨q, D, hq, -, hqp, hDn, hD1, hDO, hDexp, hDcl, hUD⟩ :=
    exists_critical_normal hsolv hodd hO hpk hUp hJ hperf
  have : Fact q.Prime := ⟨hq⟩
  have := hDn
  exact false_of_critical hp5 hqp.symm hD1 hDexp hDcl
    (fun E hE hab => hrank q hq E (hE.trans hDO) hab) hUcard hUexp hUcomm hτ hτinv hσ hσ1 hσ2 hUD

theorem isElemAbelian_map_subtype' {X : Type} [Group X] (J : Subgroup X) (q : ℕ)
    (E : Subgroup J) (hE : IsElemAbelian q E) : IsElemAbelian q (E.map J.subtype) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem central_of_rank_le_three_psl :
    ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ J O : Subgroup X,
      O ≤ J → Odd (Nat.card O) → ¬ p ∣ Nat.card O → ⁅J, J⁆ = J →
      ∀ (Q : Type) [Group Q] (ψ : ↥J →* Q), Function.Surjective ψ → ψ.ker = O.subgroupOf J →
      Nonempty (Q ≃* PSL(2, GaloisField p 2)) →
      (∀ q : ℕ, q.Prime → ∀ E : Subgroup X, E ≤ O → IsElemAbelian q E → Nat.card E ≤ q ^ 3) →
      ⁅J, O⁆ = ⊥ := by
  intro X _ _ p _ hp5 J O hOJ hodd hpO hperf Q _ ψ hψ hker he hrank
  obtain ⟨e⟩ := he
  have hcard : Nat.card ψ.ker = Nat.card O := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv
  have hodd' : Odd (Nat.card ψ.ker) := hcard ▸ hodd
  have hpk : ¬ p ∣ Nat.card ψ.ker := hcard ▸ hpO
  have hperf' : commutator ↥J = ⊤ := (Subgroup.isPerfect_iff.mpr hperf).commutator_eq_top
  have hsolv : Group.IsSolvable ψ.ker := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
  have hcent : ψ.ker ≤ Subgroup.center ↥J :=
    central_of_rank_le_three_psl_core hp5 ψ hψ hodd' hpk hperf' hsolv e fun q hq E hEk hab => by
      have hEO : E.map J.subtype ≤ O := by
        rintro _ ⟨x, hx, rfl⟩
        have := hEk hx
        rw [hker, Subgroup.mem_subgroupOf] at this
        exact this
      have h1 := hrank q hq _ hEO (isElemAbelian_map_subtype' J q E hab)
      rwa [Subgroup.card_map_of_injective J.subtype_injective] at h1
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hb' : (⟨b, hOJ hb⟩ : ↥J) ∈ ψ.ker := by
    rw [hker, Subgroup.mem_subgroupOf]
    exact hb
  have := Subgroup.mem_center_iff.mp (hcent hb') ⟨a, ha⟩
  exact (congrArg Subtype.val this).symm

end Core

end CFSG.LocalAnalysis.RankThreeTheoremC
