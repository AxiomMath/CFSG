module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements2
public import CFSG.HardMathSupport.Solomon.LocalBalance.GlueTools
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma29Order3
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Center
public import CFSG.CharacterTheory.Burnside
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.ClassicalGroups.Unitary.Simple
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open scoped LinearAlgebra.Projectivization

namespace Lemma513Ns

universe u

variable {G : Type u} [Group G]

@[expose] def IsDiagAutPSL3 {Y : Type*} [Group Y] (α : MulAut Y) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K)
    (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL 3 K)) (A : GL (Fin 3) K),
    (∀ M : ↥(StatedSL 3 K), ∃ M' : ↥(StatedSL 3 K), (M' : GL (Fin 3) K) = A * M * A⁻¹) ∧
    ∀ (y : Y) (M M' : ↥(StatedSL 3 K)), θ (QuotientGroup.mk y) = QuotientGroup.mk M →
      (M' : GL (Fin 3) K) = A * M * A⁻¹ → θ (QuotientGroup.mk (α y)) = QuotientGroup.mk M'

@[expose] def IsDiagAutPSU3 {Y : Type*} [Group Y] (α : MulAut Y) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ)
    (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSU 3 q K)) (A : GL (Fin 3) K),
    Nat.card K = q ^ 2 ∧
    (∀ M : ↥(StatedSU 3 q K), ∃ M' : ↥(StatedSU 3 q K), (M' : GL (Fin 3) K) = A * M * A⁻¹) ∧
    ∀ (y : Y) (M M' : ↥(StatedSU 3 q K)), θ (QuotientGroup.mk y) = QuotientGroup.mk M →
      (M' : GL (Fin 3) K) = A * M * A⁻¹ → θ (QuotientGroup.mk (α y)) = QuotientGroup.mk M'

@[expose] def diagAut (Y : Type*) [Group Y] : Subgroup (MulAut Y) :=
  Subgroup.closure {α | IsDiagAutPSL3 α ∨ IsDiagAutPSU3 α}

@[expose] def innerDiag (Y : Type*) [Group Y] : Subgroup (MulAut Y) :=
  innerAut Y ⊔ diagAut Y

theorem innerAut_le_innerDiag (Y : Type*) [Group Y] : innerAut Y ≤ innerDiag Y := le_sup_left

structure IsThreeCover {Y : Type*} [Group Y] {Ŵ : Type*} [Group Ŵ] (π : Ŵ →* MulAut Y)
    (ι : Y →* Ŵ) : Prop where
  inj : Function.Injective ι
  conj : ∀ l, π (ι l) = MulAut.conj l
  inner : ∀ x, π x ∈ innerAut Y → x ∈ Set.range ι
  central : π.ker ≤ Subgroup.center Ŵ
  card : Nat.card π.ker = 3

@[expose] def Lemma510ii : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBZeroMax 3 B → ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G,
      IsUpsilonComponent B b L →
      Nat.card ↥(autBar 3 B L ⊓ innerDiag (barOf 3 L)) = 9 ∧
      (∀ x : barOf 3 L, MulAut.conj x ∈ autBar 3 B L → x ^ 3 = 1) ∧
      ∀ (Ŵ : Type) [Group Ŵ] (π : Ŵ →* MulAut (barOf 3 L)) (ι : barOf 3 L →* Ŵ),
        IsThreeCover π ι → (∀ x, π x ∈ innerDiag (barOf 3 L)) →
        autBar 3 B L ⊓ innerDiag (barOf 3 L) ≤ π.range →
        ∃ x ∈ (autBar 3 B L ⊓ innerDiag (barOf 3 L)).comap π,
          ∃ y ∈ (autBar 3 B L ⊓ innerDiag (barOf 3 L)).comap π, x * y ≠ y * x

@[expose] def InputInnDiagStructure : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    (IsExtremalType Y ∨ IsSLThreeEps Y) →
    ((innerAut Y).subgroupOf (innerDiag Y)).index ≤ 3 ∧
    ∀ α : MulAut Y, α ^ 3 = 1 → α ∉ innerDiag Y → IsFieldAutThree α

theorem exists_fixed_mem_coset [Finite G] {p : ℕ} (hp : p.Prime)
    (P N : Subgroup G) (hP : IsPGroup p P) (hN : Nat.Coprime p (Nat.card N))
    (hPN : P ≤ Subgroup.normalizer (N : Set G)) (x : G)
    (hx : ∀ g ∈ P, x⁻¹ * (g * x * g⁻¹) ∈ N) :
    ∃ n ∈ N, ∀ g ∈ P, g * (x * n) * g⁻¹ = x * n := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let S : Type _ := {z : G // x⁻¹ * z ∈ N}
  have hclosed : ∀ (g : P) (z : S), x⁻¹ * ((g : G) * (z : G) * (g : G)⁻¹) ∈ N := by
    intro g z
    have h1 : x⁻¹ * ((g : G) * (z : G) * (g : G)⁻¹) =
        (x⁻¹ * ((g : G) * x * (g : G)⁻¹)) * ((g : G) * (x⁻¹ * (z : G)) * (g : G)⁻¹) := by
      group
    rw [h1]
    refine N.mul_mem (hx g g.2) ?_
    have := (Subgroup.mem_normalizer_iff.1 (hPN g.2) (x⁻¹ * (z : G))).1 z.2
    simpa using this
  let _ : MulAction P S :=
    { smul := fun g z => ⟨(g : G) * (z : G) * (g : G)⁻¹, hclosed g z⟩
      one_smul := fun z => by
        apply Subtype.ext
        show ((1 : P) : G) * (z : G) * ((1 : P) : G)⁻¹ = z
        simp
      mul_smul := fun g h z => by
        apply Subtype.ext
        show ((g * h : P) : G) * (z : G) * ((g * h : P) : G)⁻¹ =
          (g : G) * ((h : G) * (z : G) * (h : G)⁻¹) * (g : G)⁻¹
        simp [mul_assoc] }
  have hcard : Nat.card S = Nat.card N := by
    refine Nat.card_congr
      { toFun := fun z => ⟨x⁻¹ * (z : G), z.2⟩
        invFun := fun n => ⟨x * (n : G), by simp⟩
        left_inv := fun z => by apply Subtype.ext; simp
        right_inv := fun n => by apply Subtype.ext; simp }
  have hndvd : ¬ p ∣ Nat.card S := by
    rw [hcard]
    exact fun h => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hN h)
  obtain ⟨z, hz⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card S hndvd
  refine ⟨x⁻¹ * (z : G), z.2, fun g hg => ?_⟩
  have h1 := hz ⟨g, hg⟩
  have h2 : (g : G) * (z : G) * (g : G)⁻¹ = (z : G) := congrArg Subtype.val h1
  simpa using h2

theorem isBOneMax_of_isBZeroMax [Finite G] {B : Subgroup G} (h : IsBZeroMax 3 B) :
    IsBOneMax 3 B := by
  obtain ⟨hmax, D, hDB, hD, -, hev⟩ := h
  refine ⟨hmax, D, hDB, hD, ?_⟩
  have hev' := hev rfl
  have hcomm : ∀ g ∈ B, ∀ d ∈ B, g * d = d * g := fun g hg d hd =>
    congrArg Subtype.val (hmax.1.1.is_comm.comm ⟨g, hg⟩ ⟨d, hd⟩)
  have hconj : ∀ g ∈ B, ∀ x ∈ GLADelta 3 D, g * x * g⁻¹ ∈ GLADelta 3 D := by
    intro g hg x hx
    simp only [GLADelta, Subgroup.mem_iInf] at hx ⊢
    intro d hd hd1
    have hgC : g ∈ Subgroup.centralizer ({d} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (hcomm g hg z (hDB hd)).symm
    have h1 := le_normalizer_glaPPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) hgC
    have h2 := (Subgroup.mem_normalizer_iff.1 h1 x).1 (hx d hd hd1)
    exact h2
  have hle : (⁅GLADelta 3 D, B⁆ : Subgroup G) ≤ GLADelta 3 D := by
    rw [Subgroup.commutator_le]
    intro x hx g hg
    rw [commutatorElement_def]
    have h3 : x * (g * x⁻¹ * g⁻¹) ∈ GLADelta 3 D :=
      (GLADelta 3 D).mul_mem hx (hconj g hg x⁻¹ ((GLADelta 3 D).inv_mem hx))
    simpa [mul_assoc] using h3
  have hdvd : Nat.card ↥⁅GLADelta 3 D, B⁆ ∣ Nat.card ↥(GLADelta 3 D) := Subgroup.card_dvd_of_le hle
  exact (even_iff_two_dvd.2 (dvd_trans (even_iff_two_dvd.1 hev') hdvd))

private theorem center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [← Subgroup.map_center_eq e.symm, h, Subgroup.map_bot]

private theorem center_psl_eq_bot {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) : Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin n) K) = ⊥ := by
  obtain ⟨-, -, -, -, hfaith, h2, -⟩ := CFSG.LinearGroups.linear_projective_action (K := K) hn
  have hcard : 3 ≤ Nat.card (ℙ K (Fin n → K)) := by
    rw [Projectivization.card_of_finrank K (Fin n → K) (by simp : Module.finrank K (Fin n → K) = n)]
    have hK : 2 ≤ Nat.card K := Finite.one_lt_card
    have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range n := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rw [Finset.mem_range]
      omega
    have hle := Finset.sum_le_sum_of_subset (f := fun i => Nat.card K ^ i) hsub
    rw [Finset.sum_pair (by norm_num)] at hle
    simp only [pow_zero, pow_one] at hle
    omega
  exact CFSG.GorensteinWalter.center_eq_bot_of_two_pretransitive h2 hcard

private theorem card_center_le_one_of_center_eq_bot {Y : Type} [Group Y]
    (h : Subgroup.center Y = ⊥) : Nat.card (Subgroup.center Y) ≤ 3 := by
  rw [h]; simp

private theorem center_eq_bot_of_simple {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) (hs : IsSimpleGroup Y) : Subgroup.center Y = ⊥ := by
  have hn : Nontrivial (Y ⧸ Subgroup.center Y) := hq.2.toNontrivial
  rcases (Subgroup.center Y).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have : Subsingleton (Y ⧸ Subgroup.center Y) := by
      rw [h]; exact QuotientGroup.subsingleton_quotient_top
    exact not_subsingleton _ this

private theorem psu_center {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) {K : Type} [Field K] [Finite K] {q : ℕ}
    (e : Y ≃* StatedProj (StatedSU 3 q K)) (hK : Nat.card K = q ^ 2) (hq3 : q % 3 = 2) :
    Subgroup.center Y = ⊥ := by
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hqd : q ∣ ringChar K ^ (n : ℕ) := by
    rw [← Nat.card_eq_fintype_card] at hn
    rw [← hn, hK]; exact Dvd.intro _ (sq q).symm
  have hp' : (ringChar K).Prime := hp
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hp').1 hqd
  subst hf
  have : Fact (ringChar K).Prime := ⟨hp'⟩
  have hnt : Nontrivial Y := by
    have := hq.2.toNontrivial
    exact (QuotientGroup.mk_surjective (s := Subgroup.center Y)).nontrivial
  by_cases h2 : ringChar K ^ f = 2
  ·
    exfalso
    have hf1 : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with h0 | h0
      · subst h0; simp at h2
      · exact h0
    have hcard := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) (p := ringChar K)
      (f := f) hp' hf1 hK (by norm_num : 2 ≤ 3)
    have h72 : Nat.card (StatedProj (StatedSU 3 (ringChar K ^ f) K)) = 72 := by
      refine hcard.trans ?_
      rw [h2, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
      norm_num
    have : Fintype (StatedProj (StatedSU 3 (ringChar K ^ f) K)) := Fintype.ofFinite _
    have hsolv : Group.IsSolvable (StatedProj (StatedSU 3 (ringChar K ^ f) K)) :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 2)
        Nat.prime_two Nat.prime_three (by norm_num)
        (by rw [← Nat.card_eq_fintype_card, h72]; norm_num)
    have hY : Group.IsSolvable Y := Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    have : Group.IsPerfect Y := ⟨hq.1⟩
    exact Group.IsPerfect.not_isSolvable (G := Y) hY
  · have hnq : (3, ringChar K ^ f) ≠ (3, 2) := fun h => h2 (by simpa using congrArg Prod.snd h)
    have hs : IsSimpleGroup (StatedProj (StatedSU 3 (ringChar K ^ f) K)) :=
      CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K (ringChar K) f hK
        3 le_rfl hnq
    exact center_eq_bot_of_simple hq
      (IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective)

theorem card_center_le_three_of_type {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) (h : IsExtremalType Y ∨ IsSLThreeEps Y) :
    Nat.card (Subgroup.center Y) ≤ 3 := by
  rcases h with (⟨K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, q, hK, hq3, hq8, ⟨e⟩⟩) |
      (⟨K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, q, hK, hq3, hq8, ⟨e⟩⟩)
  · refine card_center_le_one_of_center_eq_bot (center_eq_bot_of_mulEquiv
      (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm)
      (center_psl_eq_bot (n := 3) (by norm_num)))
  · refine card_center_le_one_of_center_eq_bot (psu_center hq (e := e) hK hq3)
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact (CFSG.Quasithin.Vol2.Ch11.SecA.C10KG.card_center_statedSL_three
      (by omega)).le
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact (CFSG.Quasithin.Vol2.Ch11.SecA.C10KG.card_center_statedSU_three hK
      (by omega)).le


private theorem conj_mem_gLAPPrimeCoreOf' {p : ℕ} {J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (J : Set G)) {y : G} (hy : y ∈ GLAPPrimeCoreOf p J) :
    g * y * g⁻¹ ∈ GLAPPrimeCoreOf p J := by
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨J.normalizerMonoidHom ⟨g, hg⟩ y',
    map_gLAPPrimeCore_le p (J.normalizerMonoidHom ⟨g, hg⟩) ⟨y', hy', rfl⟩, ?_⟩
  rfl

theorem mem_centralizerQuot_iff_barAut' (p : ℕ) {J : Subgroup G}
    (g : ↥(Subgroup.normalizer (J : Set G))) :
    (g : G) ∈ centralizerQuot J (GLAPPrimeCoreOf p J) ↔ barAut p J g = 1 := by
  have hs : ∀ y : ↥J, ((J.normalizerMonoidHom g y : ↥J) : G) = g * y * (g : G)⁻¹ := fun _ => rfl
  constructor
  · rintro ⟨-, -, hc⟩
    ext z
    induction z using QuotientGroup.induction_on with | H y => ?_
    rw [barAut_mk, MulAut.one_apply, eq_comm, QuotientGroup.eq]
    have := hc (y : G)⁻¹ (J.inv_mem y.2)
    refine (Subgroup.mem_map_iff_mem J.subtype_injective).1
      (?_ : J.subtype _ ∈ GLAPPrimeCoreOf p J)
    simpa [mul_assoc, hs] using this
  · intro h
    refine ⟨g.2, ?_, fun x hx => ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => conj_mem_gLAPPrimeCoreOf' g.2 hy, fun hy => ?_⟩
      have := conj_mem_gLAPPrimeCoreOf' (inv_mem g.2) hy
      simpa [mul_assoc] using this
    · have h1 := congrArg (fun φ => φ (QuotientGroup.mk (⟨x, hx⟩⁻¹ : ↥J))) h
      simp only [barAut_mk, MulAut.one_apply] at h1
      rw [eq_comm, QuotientGroup.eq] at h1
      have h2 : J.subtype _ ∈ GLAPPrimeCoreOf p J := Subgroup.mem_map_of_mem J.subtype h1
      simpa [mul_assoc, hs] using h2


theorem normalizer_le_normalizer_glaPPrimeCoreOf (p : ℕ) (I : Subgroup G) :
    Subgroup.normalizer (I : Set G) ≤ Subgroup.normalizer (GLAPPrimeCoreOf p I : Set G) := by
  intro g hg
  have h1 := hg
  rw [mem_normalizer_iff_gLBConj_eq] at h1 ⊢
  rw [← glaPPrimeCoreOf_gLBConj, h1]


open Classical in
noncomputable def rho (L : Subgroup G) (g : G) : MulAut (barOf 3 L) :=
  if h : g ∈ Subgroup.normalizer (L : Set G) then barAut 3 L ⟨g, h⟩ else 1

theorem rho_of_mem {L : Subgroup G} {g : G} (h : g ∈ Subgroup.normalizer (L : Set G)) :
    rho L g = barAut 3 L ⟨g, h⟩ := by
  simp [rho, h]

theorem rho_mul {L : Subgroup G} {g h : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hh : h ∈ Subgroup.normalizer (L : Set G)) : rho L (g * h) = rho L g * rho L h := by
  rw [rho_of_mem hg, rho_of_mem hh, rho_of_mem (mul_mem hg hh)]
  have e : (⟨g * h, mul_mem hg hh⟩ : ↥(Subgroup.normalizer (L : Set G))) = ⟨g, hg⟩ * ⟨h, hh⟩ := rfl
  rw [e, map_mul]

theorem rho_one (L : Subgroup G) : rho L 1 = 1 := by
  rw [rho_of_mem (one_mem _)]
  have e : (⟨1, one_mem _⟩ : ↥(Subgroup.normalizer (L : Set G))) = 1 := rfl
  rw [e, map_one]

theorem rho_inv {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    rho L g⁻¹ = (rho L g)⁻¹ := by
  rw [rho_of_mem hg, rho_of_mem (inv_mem hg)]
  have e : (⟨g⁻¹, inv_mem hg⟩ : ↥(Subgroup.normalizer (L : Set G))) = (⟨g, hg⟩)⁻¹ := rfl
  rw [e, map_inv]

theorem rho_pow {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) (n : ℕ) :
    rho L (g ^ n) = rho L g ^ n := by
  rw [rho_of_mem hg, rho_of_mem (pow_mem hg n)]
  have e : (⟨g ^ n, pow_mem hg n⟩ : ↥(Subgroup.normalizer (L : Set G))) = (⟨g, hg⟩) ^ n := rfl
  rw [e, map_pow]

theorem rho_mk {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) (l : ↥L) :
    rho L g (QuotientGroup.mk l) =
      QuotientGroup.mk (⟨g * l * g⁻¹, by
        have := (Subgroup.mem_normalizer_iff.1 hg l).1 l.2
        simpa using this⟩ : ↥L) := by
  rw [rho_of_mem hg, barAut_mk]
  rfl

theorem le_normalizer_self (L : Subgroup G) : L ≤ Subgroup.normalizer (L : Set G) :=
  Subgroup.le_normalizer

theorem rho_of_mem_L {L : Subgroup G} {l : G} (hl : l ∈ L) :
    rho L l = MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : barOf 3 L) := by
  ext z
  induction z using QuotientGroup.induction_on with | H x => ?_
  rw [rho_mk (le_normalizer_self L hl), MulAut.conj_apply, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  rfl

theorem rho_mem_innerAut_of_mem {L : Subgroup G} {l : G} (hl : l ∈ L) :
    rho L l ∈ innerAut (barOf 3 L) :=
  ⟨_, (rho_of_mem_L hl).symm⟩

theorem rho_eq_one_iff {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    rho L g = 1 ↔ g ∈ centralizerQuot L (GLAPPrimeCoreOf 3 L) := by
  rw [rho_of_mem hg]
  exact (mem_centralizerQuot_iff_barAut' 3 ⟨g, hg⟩).symm

theorem le_normalizer_of_centralizerQuot (L U : Subgroup G) {g : G}
    (hg : g ∈ centralizerQuot L U) : g ∈ Subgroup.normalizer (L : Set G) := hg.1

theorem rho_eq_one_of_commute {L : Subgroup G} {b : G} (hbN : b ∈ Subgroup.normalizer (L : Set G))
    (hbc : ∀ l ∈ L, b * l = l * b) : rho L b = 1 := by
  ext z
  induction z using QuotientGroup.induction_on with | H l => ?_
  rw [rho_mk hbN, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  show b * (l : G) * b⁻¹ = l
  rw [hbc l l.2]; group

theorem mem_center_of_aut {Y : Type*} [Group Y] (α : MulAut Y) {z : Y}
    (hz : z ∈ Subgroup.center Y) : α z ∈ Subgroup.center Y := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro y
  have := hz (α.symm y)
  have h2 := congrArg α this
  simpa using h2

theorem aut_fixes_center_of_card_three {Y : Type*} [Group Y]
    (hZ : Nat.card (Subgroup.center Y) = 3) (α : MulAut Y) (hα : α ^ 3 = 1) {z : Y}
    (hz : z ∈ Subgroup.center Y) : α z = z := by
  by_contra hne
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hne (map_one α)
  have : Finite ↥(Subgroup.center Y) := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have hz3 : z ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥(Subgroup.center Y)) (x := ⟨z, hz⟩)
    rw [hZ] at this
    exact congrArg Subtype.val this
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hmemZ : α z ∈ Subgroup.center Y := mem_center_of_aut α hz
  have hzp : Subgroup.zpowers z = Subgroup.center Y := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact hz
    · rw [Nat.card_zpowers, hord, hZ]
  have hαz : α z ∈ Subgroup.zpowers z := by rw [hzp]; exact hmemZ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hαz
  have hk3 : z ^ (k % 3) = z ^ k := by
    have := zpow_mod_orderOf z k
    rw [hord] at this
    simpa using this
  have h3 : (α ^ 3) z = z := by rw [hα]; rfl
  have h3' : (α ^ 3) z = α (α (α z)) := by simp [pow_succ, MulAut.mul_apply]
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h | h | h
  · rw [h, zpow_zero] at hk3
    have : α z = 1 := by rw [← hk, ← hk3]
    exact hz1 (α.injective (this.trans (map_one α).symm))
  · rw [h, zpow_one] at hk3
    exact hne (by rw [← hk, ← hk3])
  · rw [h] at hk3
    have e : α z = z ^ 2 := by rw [← hk, ← hk3]; norm_num
    have e2 : α (α z) = z := by
      rw [e, map_pow, e, ← pow_mul]
      have : z ^ 4 = z := by
        have : z ^ 4 = z ^ 3 * z := by rw [pow_succ]
        rw [this, hz3, one_mul]
      simpa using this
    rw [e2] at h3'
    exact hne (h3'.symm.trans h3)


def sgp (L : Subgroup G) (w : G) (hw : w ∈ Subgroup.normalizer (L : Set G)) (hw3 : w ^ 3 = 1) :
    Subgroup G where
  carrier := {g | ∃ l ∈ L, ∃ k : ℕ, g = l * w ^ k}
  one_mem' := ⟨1, one_mem _, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨l, hl, k, rfl⟩ ⟨l', hl', k', rfl⟩
    have hc : w ^ k * l' * (w ^ k)⁻¹ ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (pow_mem hw k) l').1 hl'
      exact this
    refine ⟨l * (w ^ k * l' * (w ^ k)⁻¹), L.mul_mem hl hc, k + k', ?_⟩
    rw [pow_add]
    group
  inv_mem' := by
    rintro _ ⟨l, hl, k, rfl⟩
    have h2k : (w ^ k)⁻¹ = w ^ (2 * k) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show k + 2 * k = 3 * k by omega, pow_mul, hw3, one_pow]
    have hc : (w ^ k)⁻¹ * l⁻¹ * w ^ k ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem (pow_mem hw k)) l⁻¹).1 (L.inv_mem hl)
      simpa using this
    refine ⟨(w ^ k)⁻¹ * l⁻¹ * w ^ k, hc, 2 * k, ?_⟩
    rw [mul_inv_rev, ← h2k]
    group

theorem le_sgp (L : Subgroup G) {w : G} (hw : w ∈ Subgroup.normalizer (L : Set G)) (hw3 : w ^ 3 = 1) :
    L ≤ sgp L w hw hw3 := fun l hl => ⟨l, hl, 0, by simp⟩

theorem w_mem_sgp (L : Subgroup G) {w : G} (hw : w ∈ Subgroup.normalizer (L : Set G))
    (hw3 : w ^ 3 = 1) : w ∈ sgp L w hw hw3 := ⟨1, one_mem _, 1, by simp⟩

theorem sgp_le_normalizer (L : Subgroup G) {w : G} (hw : w ∈ Subgroup.normalizer (L : Set G))
    (hw3 : w ^ 3 = 1) : sgp L w hw hw3 ≤ Subgroup.normalizer (L : Set G) := by
  rintro _ ⟨l, hl, k, rfl⟩
  exact mul_mem (le_normalizer_self L hl) (pow_mem hw k)

theorem rho_pow_mem_innerAut {Y : Type*} [Group Y] {a : MulAut Y} (ha3 : a ^ 3 = 1)
    (hout : a ∉ innerAut Y) {k : ℕ} (hk : a ^ k ∈ innerAut Y) : 3 ∣ k := by
  by_contra hk3
  have hk' : k % 3 = 1 ∨ k % 3 = 2 := by omega
  have hmod : a ^ k = a ^ (k % 3) := by
    conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, ha3, one_pow, one_mul]
  rw [hmod] at hk
  rcases hk' with h | h
  · rw [h, pow_one] at hk
    exact hout hk
  · rw [h] at hk
    apply hout
    have : a = (a ^ 2) ^ 2 := by
      rw [← pow_mul]
      have : a ^ 4 = a ^ 3 * a := by rw [pow_succ]
      rw [show 2 * 2 = 4 from rfl, this, ha3, one_mul]
    rw [this]
    exact pow_mem hk 2

theorem mk_eq_one_iff_mem {L : Subgroup G} {u : G} (hu : u ∈ L) :
    (QuotientGroup.mk ⟨u, hu⟩ : barOf 3 L) = 1 ↔ u ∈ GLAPPrimeCoreOf 3 L := by
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨⟨u, hu⟩, h, rfl⟩
  · rintro ⟨u', hu', rfl⟩
    exact hu'

theorem conj_eq_one_iff_mem_center {Y : Type*} [Group Y] (l : Y) :
    MulAut.conj l = 1 ↔ l ∈ Subgroup.center Y := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h g
    have := congrArg (fun φ : MulAut Y => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · intro h
    ext g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [mul_inv_eq_iff_eq_mul, h]

theorem exists_outer_cover (L : Subgroup G) {w : G} (hw : w ∈ Subgroup.normalizer (L : Set G))
    (hw3 : w ^ 3 = 1) (hout : rho L w ∉ innerAut (barOf 3 L))
    (hZ : Nat.card (Subgroup.center (barOf 3 L)) = 3) :
    ∃ (Ŵ : Type u) (_ : Group Ŵ) (π : Ŵ →* MulAut (barOf 3 L)) (ι : barOf 3 L →* Ŵ) (ŵ : Ŵ),
      IsThreeCover π ι ∧ π ŵ = rho L w ∧
      (∀ x : Ŵ, ∃ (l : barOf 3 L) (k : ℕ), x = ι l * ŵ ^ k) ∧
      (∀ (y : G) (hy : y ∈ L), y * w = w * y →
        ι (QuotientGroup.mk ⟨y, hy⟩) * ŵ = ŵ * ι (QuotientGroup.mk ⟨y, hy⟩)) := by
  classical
  set S := sgp L w hw hw3 with hS
  have hLS : L ≤ S := le_sgp L hw hw3
  have hwS : w ∈ S := w_mem_sgp L hw hw3
  have hSN : S ≤ Subgroup.normalizer (L : Set G) := sgp_le_normalizer L hw hw3
  set U := GLAPPrimeCoreOf 3 L with hU
  have hUL : U ≤ L := Subgroup.map_subtype_le _
  have hLU : L ≤ Subgroup.normalizer (U : Set G) := le_normalizer_glaPPrimeCoreOf 3 L
  have hSU : S ≤ Subgroup.normalizer (U : Set G) := fun g hg =>
    normalizer_le_normalizer_glaPPrimeCoreOf 3 L (hSN hg)
  have hnorm : (U.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hUL.trans hLS)).2 hSU
  let φ : ↥S →* MulAut (barOf 3 L) := (barAut 3 L).comp (Subgroup.inclusion hSN)
  have hφ : ∀ s : ↥S, φ s = rho L (s : G) := fun s => (rho_of_mem (hSN s.2)).symm
  have hkerφ : U.subgroupOf S ≤ φ.ker := by
    intro s hs
    rw [MonoidHom.mem_ker, hφ]
    have hsU : (s : G) ∈ U := hs
    have hsL : (s : G) ∈ L := hUL hsU
    rw [rho_of_mem_L hsL, (mk_eq_one_iff_mem hsL).2 hsU, map_one]
  let π : (↥S ⧸ U.subgroupOf S) →* MulAut (barOf 3 L) := QuotientGroup.lift _ φ hkerφ
  let j : ↥L →* ↥S := Subgroup.inclusion hLS
  let ι₀ : ↥L →* (↥S ⧸ U.subgroupOf S) := (QuotientGroup.mk' (U.subgroupOf S)).comp j
  have hkerι : GLAPPrimeCore 3 ↥L ≤ ι₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' (U.subgroupOf S) (j x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨x, hx, rfl⟩
  let ι : barOf 3 L →* (↥S ⧸ U.subgroupOf S) := QuotientGroup.lift _ ι₀ hkerι
  have hι_mk : ∀ l : ↥L, ι (QuotientGroup.mk l) = QuotientGroup.mk (j l) := fun l => rfl
  have hπ_mk : ∀ s : ↥S, π (QuotientGroup.mk s) = φ s := fun s => rfl
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro x hx
    induction x using QuotientGroup.induction_on with | H l => ?_
    rw [hι_mk, QuotientGroup.eq_one_iff] at hx
    have hl : (l : G) ∈ U := hx
    exact (mk_eq_one_iff_mem l.2).2 hl
  have hπι : ∀ l : barOf 3 L, π (ι l) = MulAut.conj l := by
    intro l
    induction l using QuotientGroup.induction_on with | H l => ?_
    rw [hι_mk, hπ_mk, hφ]
    exact rho_of_mem_L l.2
  set ŵ : ↥S ⧸ U.subgroupOf S := QuotientGroup.mk ⟨w, hwS⟩ with hŵ
  have hπŵ : π ŵ = rho L w := by
    rw [hŵ, hπ_mk, hφ]
  have hŵ3 : ŵ ^ 3 = 1 := by
    rw [hŵ, ← QuotientGroup.mk_pow]
    have : (⟨w, hwS⟩ : ↥S) ^ 3 = 1 := Subtype.ext (by simpa using hw3)
    rw [this]; rfl
  have hdecomp : ∀ x : ↥S ⧸ U.subgroupOf S, ∃ (l : barOf 3 L) (k : ℕ), x = ι l * ŵ ^ k := by
    intro x
    induction x using QuotientGroup.induction_on with | H s => ?_
    obtain ⟨l, hl, k, hk⟩ := s.2
    refine ⟨QuotientGroup.mk ⟨l, hl⟩, k, ?_⟩
    rw [hι_mk, hŵ, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hk
  have hŵι : ∀ l : barOf 3 L, ŵ * ι l * ŵ⁻¹ = ι (rho L w l) := by
    intro l
    induction l using QuotientGroup.induction_on with | H l => ?_
    rw [rho_mk hw, hι_mk, hι_mk, hŵ, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    rfl
  have hrw3 : rho L w ^ 3 = 1 := by rw [← rho_pow hw, hw3, rho_one]
  have h3k : ∀ k : ℕ, 3 ∣ k → ŵ ^ k = 1 := by
    rintro k ⟨q, rfl⟩
    rw [pow_mul, hŵ3, one_pow]
  have hπdec : ∀ (l : barOf 3 L) (k : ℕ), π (ι l * ŵ ^ k) = MulAut.conj l * rho L w ^ k := by
    intro l k
    rw [map_mul, map_pow, hπι, hπŵ]
  have hkerπ : ∀ x, π x = 1 ↔ ∃ z ∈ Subgroup.center (barOf 3 L), x = ι z := by
    intro x
    constructor
    · intro hx
      obtain ⟨l, k, rfl⟩ := hdecomp x
      rw [hπdec] at hx
      have hmem : rho L w ^ k ∈ innerAut (barOf 3 L) := by
        rw [eq_inv_of_mul_eq_one_right hx]
        exact inv_mem ⟨l, rfl⟩
      have hk3 : 3 ∣ k := rho_pow_mem_innerAut hrw3 hout hmem
      obtain ⟨q, rfl⟩ := hk3
      have hk1 : rho L w ^ (3 * q) = 1 := by rw [pow_mul, hrw3, one_pow]
      rw [hk1, mul_one] at hx
      exact ⟨l, (conj_eq_one_iff_mem_center l).1 hx, by rw [h3k _ ⟨q, rfl⟩, mul_one]⟩
    · rintro ⟨z, hz, rfl⟩
      rw [hπι]
      exact (conj_eq_one_iff_mem_center z).2 hz
  have hcover : IsThreeCover π ι :=
    { inj := hinj
      conj := hπι
      inner := by
        intro x hx
        obtain ⟨l, k, rfl⟩ := hdecomp x
        rw [hπdec] at hx
        have hmem : rho L w ^ k ∈ innerAut (barOf 3 L) := by
          have : rho L w ^ k = (MulAut.conj l)⁻¹ * (MulAut.conj l * rho L w ^ k) := by group
          rw [this]
          exact mul_mem (inv_mem ⟨l, rfl⟩) hx
        have hk3 : 3 ∣ k := rho_pow_mem_innerAut hrw3 hout hmem
        exact ⟨l, by rw [h3k k hk3, mul_one]⟩
      central := by
        intro x hx
        obtain ⟨z, hz, rfl⟩ := (hkerπ x).1 hx
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨l, k, rfl⟩ := hdecomp g
        have h1 : ι z * ŵ ^ k = ŵ ^ k * ι z := by
          have hc : Commute (ι z) ŵ := by
            have := hŵι z
            rw [aut_fixes_center_of_card_three hZ (rho L w) hrw3 hz] at this
            show ι z * ŵ = ŵ * ι z
            exact (mul_inv_eq_iff_eq_mul.1 this).symm
          exact (hc.pow_right k).eq
        have h2 : ι z * ι l = ι l * ι z := by
          rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz l]
        calc ι l * ŵ ^ k * ι z = ι l * (ŵ ^ k * ι z) := by rw [mul_assoc]
          _ = ι l * (ι z * ŵ ^ k) := by rw [h1]
          _ = ι z * (ι l * ŵ ^ k) := by rw [← mul_assoc, ← mul_assoc, ← h2]
      card := by
        have : π.ker = (Subgroup.center (barOf 3 L)).map ι := by
          ext x
          rw [MonoidHom.mem_ker, hkerπ, Subgroup.mem_map]
          constructor
          · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
          · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
        rw [this, Subgroup.card_map_of_injective hinj, hZ] }
  refine ⟨↥S ⧸ U.subgroupOf S, inferInstance, π, ι, ŵ, hcover, hπŵ, hdecomp, ?_⟩
  intro y hy hyw
  rw [hι_mk, hŵ, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext hyw
theorem exists_mul_of_mem_sup {Q N : Subgroup G} (hQN : Q ≤ Subgroup.normalizer (N : Set G))
    {x : G} (hx : x ∈ Q ⊔ N) : ∃ q ∈ Q, ∃ n ∈ N, x = q * n := by
  let T : Subgroup G :=
    { carrier := {x | ∃ q ∈ Q, ∃ n ∈ N, x = q * n}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨q, hq, n, hn, rfl⟩ ⟨q', hq', n', hn', rfl⟩
        refine ⟨q * q', mul_mem hq hq', q'⁻¹ * n * q' * n', ?_, by group⟩
        refine N.mul_mem ?_ hn'
        have := (Subgroup.mem_normalizer_iff.1 (hQN (inv_mem hq')) n).1 hn
        simpa using this
      inv_mem' := by
        rintro _ ⟨q, hq, n, hn, rfl⟩
        refine ⟨q⁻¹, inv_mem hq, q * n⁻¹ * q⁻¹, ?_, by group⟩
        have := (Subgroup.mem_normalizer_iff.1 (hQN hq) n⁻¹).1 (N.inv_mem hn)
        exact this }
  have hle : Q ⊔ N ≤ T :=
    sup_le (fun q hq => ⟨q, hq, 1, one_mem _, by simp⟩) (fun n hn => ⟨1, one_mem _, n, hn, by simp⟩)
  exact hle hx

theorem le_layer_sup_of_covers [Finite G] {I Q : Subgroup G}
    (hQI : Q ≤ I) (hcov : I ≤ Q ⊔ GLAPPrimeCoreOf 3 I)
    (hqs : CFSG.Open.IsQuasisimple (↥I ⧸ GLAPPrimeCore 3 ↥I)) :
    I ≤ GLAPLayer 3 Q ⊔ GLAPPrimeCoreOf 3 I := by
  classical
  set N' := GLAPPrimeCoreOf 3 I with hN'
  set cI := GLAPPrimeCore 3 ↥I with hcI
  set cQ := GLAPPrimeCore 3 ↥Q with hcQ
  have hIN : I ≤ Subgroup.normalizer (N' : Set G) := le_normalizer_glaPPrimeCoreOf 3 I
  have hN'I : N' ≤ I := Subgroup.map_subtype_le _
  let ψ : ↥Q →* (↥I ⧸ cI) := (QuotientGroup.mk' cI).comp (Subgroup.inclusion hQI)
  have hψ : ∀ q : ↥Q, ψ q = QuotientGroup.mk (Subgroup.inclusion hQI q) := fun _ => rfl
  have hdec : ∀ i ∈ I, ∃ q ∈ Q, ∃ n ∈ N', i = q * n := fun i hi =>
    exists_mul_of_mem_sup (hQI.trans hIN) (hcov hi)
  have hψsurj : Function.Surjective ψ := by
    intro x
    induction x using QuotientGroup.induction_on with | H i => ?_
    obtain ⟨q, hq, n, hn, hi⟩ := hdec i i.2
    refine ⟨⟨q, hq⟩, ?_⟩
    rw [hψ]
    have e : i = Subgroup.inclusion hQI ⟨q, hq⟩ * ⟨n, hN'I hn⟩ := Subtype.ext hi
    rw [e, QuotientGroup.mk_mul, (mk_eq_one_iff_mem (hN'I hn)).2 hn, mul_one]
  have hker1 : cQ ≤ ψ.ker := by
    intro x hx
    have hnorm : (cQ.map ψ).Normal := (GLAPPrimeCore.normal 3 ↥Q).map ψ hψsurj
    have hcop : Nat.Coprime 3 (Nat.card (cQ.map ψ)) :=
      (coprime_card_gLAPPrimeCore_aux 3 ↥Q).coprime_dvd_right (Subgroup.card_map_dvd cQ ψ)
    have hle : cQ.map ψ ≤ GLAPPrimeCore 3 (↥I ⧸ cI) := le_sSup ⟨hnorm, hcop⟩
    rw [glaPPrimeCore_quotient_eq_bot Nat.prime_three] at hle
    have := hle (Subgroup.mem_map_of_mem ψ hx)
    exact Subgroup.mem_bot.1 this
  have hker2 : ψ.ker ≤ cQ := by
    have hnorm : ψ.ker.Normal := MonoidHom.normal_ker ψ
    have hsub : ψ.ker.map Q.subtype ≤ N' := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : ψ x = 1 := hx
      rw [hψ] at hx'
      exact (mk_eq_one_iff_mem (hQI x.2)).1 hx'
    have hcop : Nat.Coprime 3 (Nat.card ψ.ker) := by
      have h1 : Nat.card (ψ.ker.map Q.subtype) = Nat.card ψ.ker :=
        Subgroup.card_map_of_injective Q.subtype_injective
      have h2 := Subgroup.card_dvd_of_le hsub
      rw [h1] at h2
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
        (not_dvd_card_glaPPrimeCoreOf Nat.prime_three I)).coprime_dvd_right h2 |>.symm.symm
    exact le_sSup ⟨hnorm, hcop⟩
  have hker : ψ.ker = cQ := le_antisymm hker2 hker1
  let ψb : (↥Q ⧸ cQ) →* (↥I ⧸ cI) := QuotientGroup.lift cQ ψ hker1
  have hψb : ∀ q : ↥Q, ψb (QuotientGroup.mk q) = ψ q := fun _ => rfl
  have hψbinj : Function.Injective ψb := by
    rw [injective_iff_map_eq_one]
    intro x hx
    induction x using QuotientGroup.induction_on with | H q => ?_
    rw [hψb] at hx
    exact (QuotientGroup.eq_one_iff q).2 (hker2 hx)
  have hψbsurj : Function.Surjective ψb := by
    intro x
    obtain ⟨q, hq⟩ := hψsurj x
    exact ⟨QuotientGroup.mk q, by rw [hψb, hq]⟩
  let e : (↥Q ⧸ cQ) ≃* (↥I ⧸ cI) := MulEquiv.ofBijective ψb ⟨hψbinj, hψbsurj⟩
  have hQsimple : CFSG.Open.IsQuasisimple (↥Q ⧸ cQ) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hqs
  have hkerN : ∀ z : ↥Q, ψ z = 1 → (z : G) ∈ N' := by
    intro z hz
    rw [hψ] at hz
    exact (mk_eq_one_iff_mem (hQI z.2)).1 hz
  set S : Set (Subgroup G) :=
    {J | J ≤ Q ∧ IsSubnormal J Q ∧ (J.subgroupOf Q).map ψ = ⊤} with hS
  have hQS : Q ∈ S := by
    refine ⟨le_rfl, IsSubnormal.refl Q, ?_⟩
    rw [Subgroup.subgroupOf_self, Subgroup.map_top]
    exact MonoidHom.range_eq_top.2 hψsurj
  obtain ⟨J, hJS, hJmin⟩ := Set.exists_min_image S (fun J => Nat.card J) (Set.toFinite S) ⟨Q, hQS⟩
  obtain ⟨hJQ, hJsub, hJψ⟩ := hJS
  have hJbar : (J.subgroupOf Q).map (QuotientGroup.mk' cQ) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    induction x using QuotientGroup.induction_on with | H q => ?_
    have hq : ψ q ∈ (J.subgroupOf Q).map ψ := by rw [hJψ]; exact Subgroup.mem_top _
    obtain ⟨j, hj, hjq⟩ := Subgroup.mem_map.1 hq
    refine ⟨j, hj, ?_⟩
    show QuotientGroup.mk j = QuotientGroup.mk q
    rw [QuotientGroup.eq, ← hker]
    rw [MonoidHom.mem_ker, map_mul, map_inv, hjq, inv_mul_cancel]
  have hQtop : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup (↥Q ⧸ cQ)) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hQsimple
  have hcomp : IsComponentOf ((J.subgroupOf Q).map (QuotientGroup.mk' cQ)) ⊤ := by
    rw [hJbar]
    exact ⟨le_rfl, IsSubnormal.refl _, hQtop⟩
  have hmin : ∀ J' : Subgroup G, J' < J → IsSubnormal J' Q →
      (J'.subgroupOf Q).map (QuotientGroup.mk' cQ) ≠ (J.subgroupOf Q).map (QuotientGroup.mk' cQ) := by
    intro J' hJ' hsub heq
    rw [hJbar] at heq
    have hJ'S : J' ∈ S := by
      refine ⟨hJ'.le.trans hJQ, hsub, ?_⟩
      rw [eq_top_iff]
      intro x _
      obtain ⟨q, rfl⟩ := hψsurj x
      have hmem : (QuotientGroup.mk q : ↥Q ⧸ cQ) ∈ (J'.subgroupOf Q).map (QuotientGroup.mk' cQ) := by
        rw [heq]; exact Subgroup.mem_top _
      obtain ⟨j', hj', hj'q⟩ := Subgroup.mem_map.1 hmem
      refine Subgroup.mem_map.2 ⟨j', hj', ?_⟩
      have : ψb (QuotientGroup.mk j') = ψb (QuotientGroup.mk q) := by
        rw [show (QuotientGroup.mk j' : ↥Q ⧸ cQ) = QuotientGroup.mk q from hj'q]
      simpa [hψb] using this
    have hle := hJmin J' hJ'S
    have hlt : Nat.card J' < Nat.card J := by
      by_contra hge
      push Not at hge
      have : J' = J := Subgroup.eq_of_le_of_card_ge hJ'.le hge
      exact hJ'.ne this
    omega
  have hJcomp : GLAPComponent 3 Q J := ⟨hJQ, hJsub, hcomp, hmin⟩
  have hJlayer : J ≤ GLAPLayer 3 Q := le_sSup hJcomp
  intro i hi
  obtain ⟨q, hq, n, hn, rfl⟩ := hdec i hi
  have hqψ : ψ ⟨q, hq⟩ ∈ (J.subgroupOf Q).map ψ := by rw [hJψ]; exact Subgroup.mem_top _
  obtain ⟨j, hj, hjq⟩ := Subgroup.mem_map.1 hqψ
  have h1 : ((j⁻¹ * ⟨q, hq⟩ : ↥Q) : G) ∈ N' := by
    apply hkerN
    rw [map_mul, map_inv, hjq, inv_mul_cancel]
  have hjJ : (j : G) ∈ J := hj
  have e : q * n = (j : G) * ((j : G)⁻¹ * q * n) := by group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (hJlayer hjJ)) (Subgroup.mem_sup_right ?_)
  exact N'.mul_mem h1 hn

theorem upsilon_le_of_comm (h53 : Lemma53) (h56 : Lemma56)
    {G : Type} [Group G] [Finite G] (m : ℕ) (hstd : GLStanding G m 3) (hc4 : GLCaseFour G 3)
    {B : Subgroup G} (hB : IsBZeroMax 3 B) {b x : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    (hx : x ∈ B) (hx1 : x ≠ 1)
    (hcomm : ⁅upsilonOf B x, Subgroup.zpowers b⁆ ≤ GLAPPrimeCoreOf 3 (upsilonOf B x)) :
    upsilonOf B x ≤ upsilonOf B b ⊔ GLAPPrimeCoreOf 3 (upsilonOf B x) := by
  have hb3 : b ^ 3 = 1 := hB.1.1.2 b hb
  have hB1 : IsBOneMax 3 B := isBOneMax_of_isBZeroMax hB
  refine sSup_le fun I hI => ?_
  have hBN : B ≤ Subgroup.normalizer (I : Set G) := (h56 G m hstd hc4 B hB x hx hx1).2 I hI
  have hbN : b ∈ Subgroup.normalizer (I : Set G) := hBN hb
  have hIU : I ≤ upsilonOf B x := le_sSup hI
  have hUC : upsilonOf B x ≤ Subgroup.centralizer ({x} : Set G) :=
    sSup_le fun J hJ => hJ.1.1
  have hsub : IsSubnormal I (upsilonOf B x) :=
    isSubnormal_of_le_of_le hI.1.2.1 hIU hUC
  set N' := GLAPPrimeCoreOf 3 I with hN'
  have hN'U : N' ≤ GLAPPrimeCoreOf 3 (upsilonOf B x) :=
    glaPPrimeCoreOf_le_of_isSubnormal 3 hsub
  have hbN' : b ∈ Subgroup.normalizer (N' : Set G) :=
    normalizer_le_normalizer_glaPPrimeCoreOf 3 I hbN
  have hbq : b ∈ centralizerQuot I N' := by
    refine ⟨hbN, hbN', fun i hi => ?_⟩
    have h1 : i * b * i⁻¹ * b⁻¹ ∈ ⁅upsilonOf B x, Subgroup.zpowers b⁆ :=
      Subgroup.commutator_mem_commutator (hIU hi) (Subgroup.mem_zpowers b)
    have h2 : i * b * i⁻¹ * b⁻¹ ∈ I := by
      have := (Subgroup.mem_normalizer_iff.1 hbN i⁻¹).1 (I.inv_mem hi)
      have h3 : i * b * i⁻¹ * b⁻¹ = i * (b * i⁻¹ * b⁻¹) := by group
      rw [h3]
      exact I.mul_mem hi this
    have h4 := gLAPPrimeCoreOf_inf_le Nat.prime_three (upsilonOf B x) I ⟨hcomm h1, h2⟩
    rwa [inf_eq_right.2 hIU] at h4
  have hbtriv : barAut 3 I ⟨b, hbN⟩ = 1 :=
    (mem_centralizerQuot_iff_barAut' 3 ⟨b, hbN⟩).1 hbq
  have hcop : Nat.Coprime 3 (Nat.card N') :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (not_dvd_card_glaPPrimeCoreOf Nat.prime_three I)
  have hP : IsPGroup 3 (Subgroup.zpowers b) := by
    refine IsPGroup.iff_card.2 ⟨1, ?_⟩
    rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1, pow_one]
  have hcov : I ≤ (I ⊓ Subgroup.centralizer ({b} : Set G)) ⊔ N' := by
    intro x hxI
    have hPN : Subgroup.zpowers b ≤ Subgroup.normalizer (N' : Set G) := by
      rw [Subgroup.zpowers_le]; exact hbN'
    have hzq : Subgroup.zpowers b ≤ centralizerQuot I N' := by
      rw [Subgroup.zpowers_le]; exact hbq
    obtain ⟨n, hn, hfix⟩ := exists_fixed_mem_coset Nat.prime_three (Subgroup.zpowers b) N' hP hcop
      hPN x (fun g hg => by
        have := (hzq hg).2.2 x⁻¹ (I.inv_mem hxI)
        simpa [mul_assoc] using this)
    have hnI : n ∈ I := Subgroup.map_subtype_le _ hn
    have hxn : x * n ∈ I ⊓ Subgroup.centralizer ({b} : Set G) := by
      refine Subgroup.mem_inf.2 ⟨I.mul_mem hxI hnI, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      have := hfix z (Subgroup.mem_zpowers z)
      exact (mul_inv_eq_iff_eq_mul.1 this)
    have : x = (x * n) * n⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem_sup hxn (N'.inv_mem hn)
  have hqs : CFSG.Open.IsQuasisimple (↥I ⧸ GLAPPrimeCore 3 ↥I) :=
    isQuasisimple_quotient_of_glaPComponent hI.1
  have hlayer := le_layer_sup_of_covers (inf_le_left : I ⊓ Subgroup.centralizer ({b} : Set G) ≤ I)
    hcov hqs
  have hfa : InducesFieldAut 3 I b := ⟨hbN, by rw [hbtriv]; exact Or.inl rfl⟩
  have h53' := h53 G m hstd hc4 B hB1 x hx hx1 I hI b hb hb1 hfa
  have hJ : GLAPLayer 3 (I ⊓ Subgroup.centralizer ({b} : Set G)) ≤ upsilonOf B b := by
    refine le_trans ?_ h53'
    refine le_iSup₂_of_le (1 : G) (one_mem _) ?_
    rw [gLBConj_one]
  calc I ≤ GLAPLayer 3 (I ⊓ Subgroup.centralizer ({b} : Set G)) ⊔ N' := hlayer
    _ ≤ upsilonOf B b ⊔ GLAPPrimeCoreOf 3 (upsilonOf B x) := sup_le_sup hJ hN'U

theorem comm_of_comap_zpowers {Ŵ M : Type*} [Group Ŵ] [Group M] (π : Ŵ →* M) (p q : Ŵ)
    (hpq : p * q = q * p) (hK : π.ker ≤ Subgroup.center Ŵ) (H : Subgroup M)
    (hH : H = Subgroup.zpowers (π p) ⊔ Subgroup.zpowers (π q)) (u v : Ŵ) (hu : π u ∈ H)
    (hv : π v ∈ H) : u * v = v * u := by
  have hmap : H = (Subgroup.zpowers p ⊔ Subgroup.zpowers q).map π := by
    rw [hH, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  have hmem : ∀ x : Ŵ, π x ∈ H →
      x ∈ Subgroup.zpowers p ⊔ Subgroup.zpowers q ⊔ π.ker := by
    intro x hx
    rw [hmap] at hx
    obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 hx
    have : x = t * (t⁻¹ * x) := by group
    rw [this]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right ?_)
    rw [MonoidHom.mem_ker, map_mul, map_inv, hte, inv_mul_cancel]
  have hQ : Subgroup.zpowers p ⊔ Subgroup.zpowers q ⊔ π.ker =
      Subgroup.closure (({p} ∪ {q} ∪ (π.ker : Set Ŵ)) : Set Ŵ) := by
    rw [Subgroup.closure_union, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
      Subgroup.zpowers_eq_closure, Subgroup.closure_eq]
  have hcomm : IsMulCommutative ↥(Subgroup.zpowers p ⊔ Subgroup.zpowers q ⊔ π.ker) := by
    rw [hQ]
    apply Subgroup.isMulCommutative_closure
    intro x hx y hy _
    have hc : ∀ k ∈ (π.ker : Set Ŵ), ∀ z : Ŵ, Commute k z := fun k hk z =>
      (Subgroup.mem_center_iff.1 (hK hk) z).symm
    rcases hx with (hx | hx) | hx
    · rcases hy with (hy | hy) | hy
      · rw [Set.mem_singleton_iff] at hx hy; subst hx; subst hy; exact Commute.refl _
      · rw [Set.mem_singleton_iff] at hx hy; subst hx; subst hy; exact hpq
      · exact (hc y hy x).symm
    · rcases hy with (hy | hy) | hy
      · rw [Set.mem_singleton_iff] at hx hy; subst hx; subst hy; exact hpq.symm
      · rw [Set.mem_singleton_iff] at hx hy; subst hx; subst hy; exact Commute.refl _
      · exact (hc y hy x).symm
    · exact hc x hx y
  have := hcomm.is_comm.comm ⟨u, hmem u hu⟩ ⟨v, hmem v hv⟩
  exact congrArg Subtype.val this

theorem conj_ker_eq_center (Y : Type*) [Group Y] :
    (MulAut.conj : Y →* MulAut Y).ker = Subgroup.center Y := by
  ext x
  rw [MonoidHom.mem_ker]
  exact conj_eq_one_iff_mem_center x

theorem key_claim {L B' : Subgroup G} {Bt : Subgroup (MulAut (barOf 3 L))}
    (hZ : Nat.card (Subgroup.center (barOf 3 L)) = 3)
    (hW9 : Nat.card ↥(Bt ⊓ innerDiag (barOf 3 L)) = 9)
    (hcov : ∀ (Ŵ : Type u) [Group Ŵ] (π : Ŵ →* MulAut (barOf 3 L)) (ι : barOf 3 L →* Ŵ),
        IsThreeCover π ι → (∀ x, π x ∈ innerDiag (barOf 3 L)) →
        Bt ⊓ innerDiag (barOf 3 L) ≤ π.range →
        ∃ x ∈ (Bt ⊓ innerDiag (barOf 3 L)).comap π,
          ∃ y ∈ (Bt ⊓ innerDiag (barOf 3 L)).comap π, x * y ≠ y * x)
    (hBel : IsElemAbelian 3 B') (hBN : B' ≤ Subgroup.normalizer (L : Set G))
    (hBt : ∀ g ∈ B', rho L g ∈ Bt)
    {y : G} (hyL : y ∈ L) (hyB : y ∈ B') (hy1 : rho L y ≠ 1)
    {w : G} (hw : w ∈ B') (hwW : rho L w ∈ innerDiag (barOf 3 L)) :
    rho L w ∈ Subgroup.zpowers (rho L y) := by
  by_contra hc
  set W := innerDiag (barOf 3 L) with hWdef
  set a := rho L y with ha
  set c := rho L w with hcdef
  have hy3 : y ^ 3 = 1 := hBel.2 y hyB
  have hw3 : w ^ 3 = 1 := hBel.2 w hw
  have ha3 : a ^ 3 = 1 := by rw [ha, ← rho_pow (hBN hyB), hy3, rho_one]
  have hc3 : c ^ 3 = 1 := by rw [hcdef, ← rho_pow (hBN hw), hw3, rho_one]
  have hyw : y * w = w * y := by
    have := hBel.1.is_comm.comm ⟨y, hyB⟩ ⟨w, hw⟩
    exact congrArg Subtype.val this
  have hac : a * c = c * a := by
    rw [ha, hcdef, ← rho_mul (hBN hyB) (hBN hw), ← rho_mul (hBN hw) (hBN hyB), hyw]
  have haInn : a ∈ innerAut (barOf 3 L) := rho_mem_innerAut_of_mem hyL
  have haW : a ∈ W := innerAut_le_innerDiag _ haInn
  have haBt : a ∈ Bt := hBt y hyB
  have hcBt : c ∈ Bt := hBt w hw
  set H := Subgroup.zpowers a ⊔ Subgroup.zpowers c with hH
  have hHle : H ≤ Bt ⊓ W := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]; exact ⟨haBt, haW⟩
    · rw [Subgroup.zpowers_le]; exact ⟨hcBt, hwW⟩
  have hHcard : Nat.card H = 9 := by
    rw [hH, card_sup_zpowers_of_pow_three_eq_one hc3 hc ?_]
    · rw [Nat.card_zpowers, orderOf_eq_prime ha3 hy1]
    · intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact (Commute.zpow_left (show Commute a c from hac) k).eq
  have hfin : Finite ↥(Bt ⊓ W) := Nat.finite_of_card_ne_zero (by rw [hW9]; norm_num)
  have hHeq : H = Bt ⊓ W := by
    apply Subgroup.eq_of_le_of_card_ge hHle
    rw [hHcard, hW9]
  have hwy : c (QuotientGroup.mk ⟨y, hyL⟩) = QuotientGroup.mk ⟨y, hyL⟩ := by
    rw [hcdef, rho_mk (hBN hw)]
    congr 1
    apply Subtype.ext
    show w * y * w⁻¹ = y
    rw [← hyw]; group
  by_cases hcInn : c ∈ innerAut (barOf 3 L)
  ·
    obtain ⟨y₂, hy₂⟩ := hcInn
    set ŷ : barOf 3 L := QuotientGroup.mk ⟨y, hyL⟩ with hŷ
    have haeq : a = MulAut.conj ŷ := rho_of_mem_L hyL
    have hcomm₂ : ŷ * y₂ = y₂ * ŷ := by
      have h1 := hwy
      rw [← hy₂, MulAut.conj_apply] at h1
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    have hcover : IsThreeCover (MulAut.conj : barOf 3 L →* MulAut (barOf 3 L))
        (MonoidHom.id (barOf 3 L)) :=
      { inj := Function.injective_id
        conj := fun l => rfl
        inner := fun x _ => ⟨x, rfl⟩
        central := by
          rw [conj_ker_eq_center]
        card := by rw [conj_ker_eq_center, hZ] }
    have hrange : Bt ⊓ W ≤ (MulAut.conj : barOf 3 L →* MulAut (barOf 3 L)).range := by
      rw [← hHeq, hH]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]; exact haInn
      · rw [Subgroup.zpowers_le]; exact ⟨y₂, hy₂⟩
    obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ := hcov (barOf 3 L)
      (MulAut.conj : barOf 3 L →* MulAut (barOf 3 L)) (MonoidHom.id (barOf 3 L)) hcover
      (fun x => innerAut_le_innerDiag _ ⟨x, rfl⟩) hrange
    refine hne (comm_of_comap_zpowers (MulAut.conj : barOf 3 L →* MulAut (barOf 3 L)) ŷ y₂
      hcomm₂ (by rw [conj_ker_eq_center]) (Bt ⊓ W) ?_ x₁ x₂ hx₁ hx₂)
    rw [← hHeq, hH, ← haeq, ← hy₂]
  ·
    obtain ⟨Ŵ, _, π, ι, ŵ, hcover, hπŵ, hdec, hcommy⟩ :=
      exists_outer_cover L (hBN hw) hw3 hcInn hZ
    have hπŷ : π (ι (QuotientGroup.mk ⟨y, hyL⟩)) = a := by
      rw [hcover.conj, ha, rho_of_mem_L hyL]
    have hall : ∀ x, π x ∈ W := by
      intro x
      obtain ⟨l, k, rfl⟩ := hdec x
      rw [map_mul, map_pow, hcover.conj, hπŵ]
      exact mul_mem (innerAut_le_innerDiag _ ⟨l, rfl⟩) (pow_mem hwW k)
    have hrange : Bt ⊓ W ≤ π.range := by
      rw [← hHeq, hH]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]; exact ⟨_, hπŷ⟩
      · rw [Subgroup.zpowers_le]; exact ⟨ŵ, hπŵ⟩
    obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ := hcov Ŵ π ι hcover hall hrange
    refine hne (comm_of_comap_zpowers π (ι (QuotientGroup.mk ⟨y, hyL⟩)) ŵ
      (hcommy y hyL hyw) hcover.central (Bt ⊓ W) ?_ x₁ x₂ hx₁ hx₂)
    rw [← hHeq, hH, hπŷ, hπŵ]

theorem conj_conj_apply {Y : Type*} [Group Y] (α : MulAut Y) (x : Y) :
    α * MulAut.conj x * α⁻¹ = MulAut.conj (α x) := by
  ext z
  simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]

theorem mem_autBar_iff {B L : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (α : MulAut (barOf 3 L)) : α ∈ autBar 3 B L ↔ ∃ g ∈ B, rho L g = α := by
  unfold autBar
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(x : G), (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).1, ?_⟩
    rw [rho_of_mem x.2]
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨g, hBN hg⟩, ?_, (rho_of_mem (hBN hg)).symm⟩
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hg, hBN hg⟩)

theorem exists_three_part {L : Subgroup G} [Finite G] {y : G} (hy : y ∈ L)
    (h3 : (QuotientGroup.mk ⟨y, hy⟩ : barOf 3 L) ^ 3 = 1) :
    ∃ k : ℕ, (y ^ k) ^ 3 = 1 ∧ ∃ hk : y ^ k ∈ L, (QuotientGroup.mk ⟨y ^ k, hk⟩ : barOf 3 L) =
      QuotientGroup.mk ⟨y, hy⟩ := by
  set n := orderOf y with hn
  have hnpos : 0 < n := orderOf_pos y
  set a := n.factorization 3 with ha
  set m := n / 3 ^ a with hm
  have hcop : Nat.Coprime 3 m := Nat.coprime_ordCompl Nat.prime_three hnpos.ne'
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop 1 0
  have hnm : 3 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 3
  have hkmod : k % 3 = 1 := by
    have := hk1
    unfold Nat.ModEq at this
    simpa using this
  have hmk : m ∣ k := (Nat.modEq_zero_iff_dvd).1 hk2
  have hyk : y ^ k ∈ L := pow_mem hy k
  have hmkk : (QuotientGroup.mk ⟨y ^ k, hyk⟩ : barOf 3 L) = QuotientGroup.mk ⟨y, hy⟩ := by
    have e : (⟨y ^ k, hyk⟩ : ↥L) = (⟨y, hy⟩ : ↥L) ^ k := rfl
    rw [e, QuotientGroup.mk_pow]
    conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, h3, one_pow, one_mul, hkmod, pow_one]
  refine ⟨k, ?_, hyk, hmkk⟩
  set u := (y ^ k) ^ 3 with hu
  have huL : u ∈ L := pow_mem hyk 3
  have huU : u ∈ GLAPPrimeCoreOf 3 L := by
    rw [← mk_eq_one_iff_mem huL]
    have e : (⟨u, huL⟩ : ↥L) = (⟨y ^ k, hyk⟩ : ↥L) ^ 3 := rfl
    rw [e, QuotientGroup.mk_pow, hmkk, h3]
  have hyk1 : (y ^ k) ^ (3 ^ a) = 1 := by
    rw [← pow_mul]
    refine orderOf_dvd_iff_pow_eq_one.1 ?_
    have h1 : 3 ^ a * m ∣ 3 ^ a * k := Nat.mul_dvd_mul_left (3 ^ a) hmk
    rw [hnm, mul_comm] at h1
    exact h1
  have hord1 : u ^ (3 ^ a) = 1 := by
    rw [hu, ← pow_mul, mul_comm, pow_mul, hyk1, one_pow]
  have hd1 : orderOf u ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one hord1
  have hd2 : orderOf u ∣ Nat.card (GLAPPrimeCoreOf 3 L) := Subgroup.orderOf_dvd_natCard _ huU
  have hcop2 : Nat.Coprime (3 ^ a) (Nat.card (GLAPPrimeCoreOf 3 L)) :=
    Nat.Coprime.pow_left a
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
        (not_dvd_card_glaPPrimeCoreOf Nat.prime_three L))
  have hd3 : orderOf u ∣ 1 := by
    have := Nat.dvd_gcd hd1 hd2
    rwa [hcop2.gcd_eq_one] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd3)


theorem exists_inner_elem {L : Subgroup G} [Finite G] {Bt : Subgroup (MulAut (barOf 3 L))}
    (hW9 : Nat.card ↥(Bt ⊓ innerDiag (barOf 3 L)) = 9)
    (hidx : ((innerAut (barOf 3 L)).subgroupOf (innerDiag (barOf 3 L))).index ≤ 3) :
    ∃ α : MulAut (barOf 3 L), α ∈ Bt ∧ α ∈ innerDiag (barOf 3 L) ∧
      α ∈ innerAut (barOf 3 L) ∧ α ≠ 1 := by
  by_contra hcon
  push Not at hcon
  set Bt₁ := Bt ⊓ innerDiag (barOf 3 L) with hBt₁
  have hle : Bt₁ ≤ innerDiag (barOf 3 L) := inf_le_right
  have hne0 : (innerAut (barOf 3 L)).relIndex (innerDiag (barOf 3 L)) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have h1 := Subgroup.relIndex_le_of_le_right (H := innerAut (barOf 3 L)) hle hne0
  have h2 : (innerAut (barOf 3 L)).relIndex Bt₁ ≤ 3 := h1.trans hidx
  have hbot : (innerAut (barOf 3 L)).subgroupOf Bt₁ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : (x : MulAut (barOf 3 L)) ∈ innerAut (barOf 3 L) := hx
    have := hcon x (Subgroup.mem_inf.1 x.2).1 (Subgroup.mem_inf.1 x.2).2 hx'
    exact Subtype.ext this
  have h3 := Subgroup.card_mul_index ((innerAut (barOf 3 L)).subgroupOf Bt₁)
  have hc : Nat.card ↥((innerAut (barOf 3 L)).subgroupOf Bt₁) = 1 := by
    rw [hbot]; exact Subgroup.card_bot
  rw [hc, one_mul] at h3
  have h4 : ((innerAut (barOf 3 L)).subgroupOf Bt₁).index = 9 := by
    rw [h3, hW9]
  unfold Subgroup.relIndex at h2
  omega

def fixerSub (B L : Subgroup G) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (x : barOf 3 L) : Subgroup G where
  carrier := {g | g ∈ B ∧ rho L g x = x}
  one_mem' := ⟨one_mem _, by rw [rho_one]; rfl⟩
  mul_mem' := by
    rintro g h ⟨hg, hgx⟩ ⟨hh, hhx⟩
    refine ⟨mul_mem hg hh, ?_⟩
    rw [rho_mul (hBN hg) (hBN hh)]
    show rho L g (rho L h x) = x
    rw [hhx, hgx]
  inv_mem' := by
    rintro g ⟨hg, hgx⟩
    refine ⟨inv_mem hg, ?_⟩
    rw [rho_inv (hBN hg)]
    show (rho L g)⁻¹ x = x
    have : (rho L g).symm x = x := by rw [MulEquiv.symm_apply_eq]; exact hgx.symm
    exact this

theorem mem_fixerSub {B L : Subgroup G} {hBN : B ≤ Subgroup.normalizer (L : Set G)}
    {x : barOf 3 L} {g : G} : g ∈ fixerSub B L hBN x ↔ g ∈ B ∧ rho L g x = x := Iff.rfl

theorem fixerSub_le {B L : Subgroup G} {hBN : B ≤ Subgroup.normalizer (L : Set G)}
    {x : barOf 3 L} : fixerSub B L hBN x ≤ B := fun _ h => h.1

theorem card_le_three_mul_fixerSub [Finite G] {B L : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hZ : Nat.card (Subgroup.center (barOf 3 L)) = 3) {x : barOf 3 L}
    (hx : ∀ g ∈ B, MulAut.conj (rho L g x) = MulAut.conj x) :
    Nat.card B ≤ 3 * Nat.card (fixerSub B L hBN x) := by
  set F : Subgroup ↥B := (fixerSub B L hBN x).subgroupOf B with hF
  have hcen : ∀ g : ↥B, x⁻¹ * rho L (g : G) x ∈ Subgroup.center (barOf 3 L) := by
    intro g
    rw [← conj_eq_one_iff_mem_center, map_mul, map_inv, hx g g.2, inv_mul_cancel]
  let φ : ↥B → ↥(Subgroup.center (barOf 3 L)) := fun g => ⟨x⁻¹ * rho L (g : G) x, hcen g⟩
  have hmemF : ∀ g h : ↥B, g⁻¹ * h ∈ F ↔ φ g = φ h := by
    intro g h
    rw [hF, Subgroup.mem_subgroupOf, mem_fixerSub]
    have hgN : (g : G) ∈ Subgroup.normalizer (L : Set G) := hBN g.2
    have hhN : (h : G) ∈ Subgroup.normalizer (L : Set G) := hBN h.2
    constructor
    · rintro ⟨-, h1⟩
      apply Subtype.ext
      show x⁻¹ * rho L (g : G) x = x⁻¹ * rho L (h : G) x
      congr 1
      have e : rho L (h : G) = rho L (g : G) * rho L ((g : G)⁻¹ * (h : G)) := by
        rw [← rho_mul hgN (mul_mem (inv_mem hgN) hhN)]; congr 1; group
      have h1' : rho L ((g : G)⁻¹ * (h : G)) x = x := h1
      rw [e, MulAut.mul_apply, h1']
    · intro h1
      refine ⟨(B.mul_mem (B.inv_mem g.2) h.2), ?_⟩
      have h2 : rho L (g : G) x = rho L (h : G) x := by
        have h3 : x⁻¹ * rho L (g : G) x = x⁻¹ * rho L (h : G) x := congrArg Subtype.val h1
        exact mul_left_cancel h3
      have e : rho L ((g : G)⁻¹ * (h : G)) = (rho L g)⁻¹ * rho L h := by
        rw [rho_mul (inv_mem hgN) hhN, rho_inv hgN]
      show rho L ((g : G)⁻¹ * (h : G)) x = x
      rw [e, MulAut.mul_apply, ← h2]
      show (rho L g).symm (rho L g x) = x
      simp
  let f : (↥B ⧸ F) → ↥(Subgroup.center (barOf 3 L)) :=
    Quotient.lift φ (fun a b hab => (hmemF a b).1 (QuotientGroup.leftRel_apply.1 hab))
  have hinj : Function.Injective f := by
    intro u v huv
    induction u using QuotientGroup.induction_on with | H a => ?_
    induction v using QuotientGroup.induction_on with | H b => ?_
    exact QuotientGroup.eq.2 ((hmemF a b).2 huv)
  have hidx : F.index ≤ 3 := by
    rw [Subgroup.index_eq_card]
    have := Nat.card_le_card_of_injective f hinj
    have : Finite ↥(Subgroup.center (barOf 3 L)) := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
    omega
  have h1 := Subgroup.card_mul_index F
  have h2 : Nat.card F = Nat.card (fixerSub B L hBN x) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe fixerSub_le).toEquiv
  rw [← h1, h2]
  calc Nat.card (fixerSub B L hBN x) * F.index ≤ Nat.card (fixerSub B L hBN x) * 3 :=
        Nat.mul_le_mul_left _ hidx
    _ = 3 * Nat.card (fixerSub B L hBN x) := mul_comm _ _

theorem isPGroup_of_isElemAbelian {B : Subgroup G} (hB : IsElemAbelian 3 B) : IsPGroup 3 ↥B :=
  CFSG.Open.IsElemAbelian.isPGroup hB

theorem construct_Bstar [Finite G] {B L : Subgroup G} {b : G}
    (hBel : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hZ : Nat.card (Subgroup.center (barOf 3 L)) = 3)
    (hbB : b ∈ B) (hbc : ∀ l ∈ L, b * l = l * b)
    (hW9 : Nat.card ↥(autBar 3 B L ⊓ innerDiag (barOf 3 L)) = 9)
    (hexp : ∀ x : barOf 3 L, MulAut.conj x ∈ autBar 3 B L → x ^ 3 = 1)
    (hidx : ((innerAut (barOf 3 L)).subgroupOf (innerDiag (barOf 3 L))).index ≤ 3) :
    ∃ (y : G) (C : Subgroup G), y ∈ L ∧ y ^ 3 = 1 ∧ rho L y ≠ 1 ∧ rho L y ∈ autBar 3 B L ∧
      C ≤ B ∧ b ∈ C ∧ B ⊓ centralizerQuot L (GLAPPrimeCoreOf 3 L) ≤ C ∧
      (∀ c ∈ C, y * c = c * y) ∧ Nat.card B ≤ 3 * Nat.card C ∧ (y ∈ B → B ≤ C) := by
  obtain ⟨α, hαBt, -, hαInn, hα1⟩ := exists_inner_elem hW9 hidx
  obtain ⟨yb, hyb⟩ := hαInn
  obtain ⟨β₀, hβ₀B, hβ₀⟩ := (mem_autBar_iff hBN α).1 hαBt
  have hyb3 : yb ^ 3 = 1 := hexp yb (by rw [hyb]; exact hαBt)
  have hcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hBel.1.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩)
  have hx : ∀ g ∈ B, MulAut.conj (rho L g yb) = MulAut.conj yb := by
    intro g hg
    have h1 := conj_conj_apply (rho L g) yb
    have h2 : rho L g * α = α * rho L g := by
      rw [← hβ₀, ← rho_mul (hBN hg) (hBN hβ₀B), ← rho_mul (hBN hβ₀B) (hBN hg), hcomm g hg β₀ hβ₀B]
    rw [← h1, hyb, h2]
    group
  have hcard := card_le_three_mul_fixerSub hBN hZ hx
  set C := fixerSub B L hBN yb with hC
  have hCB : C ≤ B := fixerSub_le
  obtain ⟨y₁, rfl⟩ := QuotientGroup.mk_surjective yb
  set U := GLAPPrimeCoreOf 3 L with hU
  have hUN : Nat.Coprime 3 (Nat.card U) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (not_dvd_card_glaPPrimeCoreOf Nat.prime_three L)
  have hCN : C ≤ Subgroup.normalizer (U : Set G) := fun g hg =>
    normalizer_le_normalizer_glaPPrimeCoreOf 3 L (hBN (hCB hg))
  have hCp : IsPGroup 3 ↥C := (isPGroup_of_isElemAbelian hBel).to_le hCB
  obtain ⟨n, hnU, hfix⟩ := exists_fixed_mem_coset Nat.prime_three C U hCp hUN hCN (y₁ : G)
    (fun g hg => by
      have h1 := hg.2
      rw [rho_mk (hBN hg.1)] at h1
      have h2 := (QuotientGroup.eq.1 h1.symm)
      exact Subgroup.mem_map_of_mem L.subtype h2)
  have hnL : n ∈ L := Subgroup.map_subtype_le _ hnU
  set y' : G := (y₁ : G) * n with hy'
  have hy'L : y' ∈ L := L.mul_mem y₁.2 hnL
  have hmk' : (QuotientGroup.mk ⟨y', hy'L⟩ : barOf 3 L) = QuotientGroup.mk y₁ := by
    have e : (⟨y', hy'L⟩ : ↥L) = y₁ * ⟨n, hnL⟩ := rfl
    rw [e, QuotientGroup.mk_mul, (mk_eq_one_iff_mem hnL).2 hnU, mul_one]
  obtain ⟨k, hk3, hkL, hkmk⟩ := exists_three_part hy'L (by rw [hmk']; exact hexp _ (by rw [hyb]; exact hαBt))
  have hrho : rho L (y' ^ k) = α := by
    rw [rho_of_mem_L hkL, hkmk, hmk', ← hyb]
  refine ⟨y' ^ k, C, hkL, hk3, by rw [hrho]; exact hα1, by rw [hrho]; exact hαBt, hCB, ?_, ?_, ?_, hcard, ?_⟩
  · refine ⟨hbB, ?_⟩
    rw [rho_mk (hBN hbB)]
    congr 1
    apply Subtype.ext
    show b * (y₁ : G) * b⁻¹ = y₁
    rw [hbc y₁ y₁.2]; group
  · intro g hg
    refine ⟨hg.1, ?_⟩
    rw [(rho_eq_one_iff (hBN hg.1)).2 hg.2]
    rfl
  · intro c hc
    have h1 := hfix c hc
    have h2 : c * y' = y' * c := mul_inv_eq_iff_eq_mul.1 h1
    exact ((Commute.pow_right (show Commute c y' from h2) k).eq).symm
  · intro hyB g hg
    refine ⟨hg, ?_⟩
    have e : rho L g (QuotientGroup.mk y₁) = rho L g (QuotientGroup.mk ⟨y' ^ k, hkL⟩) := by
      rw [hkmk, hmk']
    show rho L g (QuotientGroup.mk y₁) = QuotientGroup.mk y₁
    rw [e, rho_mk (hBN hg), ← hmk', ← hkmk]
    congr 1
    apply Subtype.ext
    show g * y' ^ k * g⁻¹ = y' ^ k
    rw [← hcomm _ hyB g hg]; group

theorem card_Bstar [Finite G] {B L : Subgroup G} {y : G} {C : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hBcard : Nat.card B = 3 ^ 4) (hyL : y ∈ L) (hy3 : y ^ 3 = 1) (hy1 : rho L y ≠ 1)
    (hCB : C ≤ B) (hcomm : ∀ c ∈ C, y * c = c * y)
    (hcard : Nat.card B ≤ 3 * Nat.card C) (hyB : y ∈ B → B ≤ C)
    (hW9 : Nat.card ↥(autBar 3 B L ⊓ innerDiag (barOf 3 L)) = 9)
    (hkey : ∀ w ∈ Subgroup.zpowers y ⊔ C, rho L w ∈ innerDiag (barOf 3 L) →
      rho L w ∈ Subgroup.zpowers (rho L y)) :
    y ∉ C ∧ Nat.card C = 27 ∧ Nat.card ↥(Subgroup.zpowers y ⊔ C) = 3 ^ 4 := by
  have hcontra : ¬ B ≤ Subgroup.zpowers y ⊔ C := by
    intro hle
    have hy3' : rho L y ^ 3 = 1 := by
      rw [← rho_pow (le_normalizer_self L hyL), hy3, rho_one]
    have hsub : autBar 3 B L ⊓ innerDiag (barOf 3 L) ≤ Subgroup.zpowers (rho L y) := by
      intro δ hδ
      obtain ⟨g, hg, rfl⟩ := (mem_autBar_iff hBN δ).1 (Subgroup.mem_inf.1 hδ).1
      exact hkey g (hle hg) (Subgroup.mem_inf.1 hδ).2
    have h1 : Nat.card ↥(Subgroup.zpowers (rho L y)) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hy3' hy1]
    have : Finite ↥(Subgroup.zpowers (rho L y)) := Nat.finite_of_card_ne_zero (by rw [h1]; norm_num)
    have := Subgroup.card_le_of_le hsub
    omega
  have hyC : y ∉ C := fun hy => hcontra ((hyB (hCB hy)).trans (le_sup_right))
  have hC81 : Nat.card C ≠ 3 ^ 4 := by
    intro h
    apply hcontra
    have : C = B := Subgroup.eq_of_le_of_card_ge hCB (by rw [h, hBcard])
    rw [← this]
    exact le_sup_right
  have hdvd : Nat.card C ∣ 3 ^ 4 := hBcard ▸ Subgroup.card_dvd_of_le hCB
  have hC27 : Nat.card C = 27 := by
    have h1 : 3 ^ 4 ≤ 3 * Nat.card C := hBcard ▸ hcard
    have h2 : Nat.card C ≤ 3 ^ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have h3 : 27 ≤ Nat.card C := by omega
    rcases (Nat.dvd_prime_pow Nat.prime_three).1 hdvd with ⟨k, hk, hkc⟩
    have hk4 : k ≤ 4 := hk
    interval_cases k <;> simp_all
  refine ⟨hyC, hC27, ?_⟩
  rw [sup_comm, card_sup_zpowers_of_pow_three_eq_one hy3 hyC (fun h hh => hcomm h hh |>.symm), hC27]
  norm_num

theorem exists_hyperplane {E : Type*} [CommGroup E] [Finite E] (hE : ∀ x : E, x ^ 3 = 1)
    (K : Subgroup E) {y : E} (hy : y ∉ K) :
    ∃ A : Subgroup E, K ≤ A ∧ y ∉ A ∧ Nat.card A * 3 = Nat.card E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : ∀ x : Additive E, 3 • x = 0 := fun x => by
    show Additive.ofMul ((Additive.toMul x) ^ 3) = 0
    rw [hE]; rfl
  let _ : Module (ZMod 3) (Additive E) := AddCommGroup.zmodModule h3
  have hyp : Additive.ofMul y ∉ AddSubgroup.toZModSubmodule 3 (Subgroup.toAddSubgroup K) := by
    intro h
    exact hy h
  obtain ⟨f, hfy, hKf⟩ := Submodule.exists_le_ker_of_notMem hyp
  let φ : E →* Multiplicative (ZMod 3) :=
    { toFun := fun e => Multiplicative.ofAdd (f (Additive.ofMul e))
      map_one' := by simp
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (f (Additive.ofMul (a * b))) = _
        rw [ofMul_mul, map_add]; rfl }
  refine ⟨φ.ker, ?_, ?_, ?_⟩
  · intro k hk
    rw [MonoidHom.mem_ker]
    have : Additive.ofMul k ∈ LinearMap.ker f := hKf hk
    exact congrArg Multiplicative.ofAdd this
  · intro h
    rw [MonoidHom.mem_ker] at h
    exact hfy (congrArg Multiplicative.toAdd h)
  · have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker] at h1
    have hr : Nat.card ↥φ.range = 3 := by
      have hd : Nat.card ↥φ.range ∣ Nat.card (Multiplicative (ZMod 3)) := Subgroup.card_subgroup_dvd_card _
      rw [Nat.card_congr (Multiplicative.toAdd), Nat.card_zmod] at hd
      have hne : Nat.card ↥φ.range ≠ 1 := by
        intro h1'
        have := Subgroup.card_eq_one.1 h1'
        have hm : φ y ∈ φ.range := ⟨y, rfl⟩
        rw [this, Subgroup.mem_bot] at hm
        exact hfy (congrArg Multiplicative.toAdd hm)
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
      · exact absurd h hne
      · exact h
    rw [hr] at h1
    exact h1

theorem exists_A' [Finite G] {L B' : Subgroup G} (hBel : IsElemAbelian 3 B')
    (hB'N : B' ≤ Subgroup.normalizer (L : Set G)) (hB'card : Nat.card B' = 3 ^ 4)
    {y : G} (hyB : y ∈ B') (hy1 : rho L y ≠ 1)
    (hkey : ∀ w ∈ B', rho L w ∈ innerDiag (barOf 3 L) → rho L w ∈ Subgroup.zpowers (rho L y)) :
    ∃ A : Subgroup G, A ≤ B' ∧ Nat.card A = 3 ^ 3 ∧ y ∉ A ∧
      ∀ a ∈ A, rho L a ∈ innerDiag (barOf 3 L) → rho L a = 1 := by
  let _ : CommGroup ↥B' := { (inferInstance : Group ↥B') with mul_comm := hBel.1.is_comm.comm }
  let ρ' : ↥B' →* MulAut (barOf 3 L) := (barAut 3 L).comp (Subgroup.inclusion hB'N)
  have hρ' : ∀ g : ↥B', ρ' g = rho L (g : G) := fun g => (rho_of_mem (hB'N g.2)).symm
  have hE : ∀ x : ↥B', x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hBel.2 x x.2)
  set yE : ↥B' := ⟨y, hyB⟩ with hyE
  have hyK : yE ∉ ρ'.ker := by
    intro h
    rw [MonoidHom.mem_ker, hρ'] at h
    exact hy1 h
  obtain ⟨A, hKA, hyA, hAcard⟩ := exists_hyperplane hE ρ'.ker hyK
  refine ⟨A.map B'.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective B'.subtype_injective]
    rw [hB'card] at hAcard
    omega
  · rintro ⟨e, he, hey⟩
    exact hyA (by
      have : e = yE := Subtype.ext hey
      rw [← this]; exact he)
  · rintro _ ⟨e, he, rfl⟩ hW
    have hmem := hkey e e.2 hW
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hmem)
    have hker : e * (yE ^ n)⁻¹ ∈ ρ'.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hρ', hρ' yE, ← hn]
      show (rho L y) ^ n * ((rho L y) ^ n)⁻¹ = 1
      exact mul_inv_cancel _
    have hyn : yE ^ n ∈ A := by
      have h1 := A.mul_mem (A.inv_mem (hKA hker)) he
      simpa [mul_assoc] using h1
    have h3 : n % 3 = 0 := by
      by_contra hne
      have hn' : n % 3 = 1 ∨ n % 3 = 2 := by omega
      have hpow : yE ^ n = yE ^ (n % 3) := by
        conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hE yE, one_pow, one_mul]
      rw [hpow] at hyn
      rcases hn' with h | h
      · rw [h, pow_one] at hyn; exact hyA hyn
      · rw [h] at hyn
        apply hyA
        have : yE = (yE ^ 2) ^ 2 := by
          rw [← pow_mul]
          have : yE ^ 4 = yE ^ 3 * yE := by rw [pow_succ]
          rw [show 2 * 2 = 4 from rfl, this, hE yE, one_mul]
        rw [this]
        exact A.pow_mem hyn 2
    obtain ⟨q, hq⟩ : 3 ∣ n := Nat.dvd_of_mod_eq_zero h3
    have hy3' : rho L y ^ 3 = 1 := by
      rw [← rho_pow (hB'N hyB), show y ^ 3 = 1 from hBel.2 y hyB, rho_one]
    show rho L (e : G) = 1
    rw [← hn, hq, pow_mul, hy3', one_pow]

theorem mem_center_of_mem_pCore {Y : Type*} [Group Y] [Finite Y]
    (hQ : CFSG.Open.IsQuasisimple Y) {z : Y} (hz : z ∈ CFSG.pCore 3 Y) :
    z ∈ Subgroup.center Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnt : Nontrivial Y := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    have := hQ.2.toNontrivial
    have : Subsingleton (Y ⧸ Subgroup.center Y) := (QuotientGroup.mk'_surjective _).subsingleton
    exact not_subsingleton _ this
  have hN : (CFSG.pCore 3 Y).Normal := CFSG.pCore_normal
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hQ
    (CFSG.pCore 3 Y) with h | h
  · exact h hz
  · exfalso
    have hpg : IsPGroup 3 Y := by
      have h0 : IsPGroup 3 (CFSG.pCore 3 Y) := CFSG.pCore_isPGroup
      rw [h] at h0
      exact h0.of_surjective Subgroup.topEquiv.toMonoidHom
        (fun y => ⟨Subgroup.topEquiv.symm y, by simp⟩)
    have := hpg.isNilpotent
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial Y
    exact hlt.ne hQ.1

theorem not_mem_oPrimePOf_of_rho_ne_one [Finite G] {L : Subgroup G}
    (hqs : CFSG.Open.IsQuasisimple (barOf 3 L)) {y : G} (hyL : y ∈ L) (hy1 : rho L y ≠ 1) :
    y ∉ oPrimePOf 3 L := by
  rintro ⟨y', hy', hyy⟩
  have hyL' : y' = ⟨y, hyL⟩ := Subtype.ext hyy
  subst hyL'
  have hmem : (QuotientGroup.mk ⟨y, hyL⟩ : barOf 3 L) ∈ CFSG.pCore 3 (barOf 3 L) := hy'
  have := (conj_eq_one_iff_mem_center _).2 (mem_center_of_mem_pCore (Y := barOf 3 L) hqs hmem)
  exact hy1 (by rw [rho_of_mem_L hyL]; exact this)

theorem isElemAbelian_sup_comm {p : ℕ} {A B : Subgroup G} (hA : IsElemAbelian p A)
    (hB : IsElemAbelian p B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian p (A ⊔ B) := by
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcomm : ∀ x ∈ (A : Set G) ∪ (B : Set G), ∀ y ∈ (A : Set G) ∪ (B : Set G),
      x ≠ y → Commute x y := by
    rintro x (hx | hx) y (hy | hy) _
    · exact hAc x hx y hy
    · exact hAB x hx y hy
    · exact (hAB y hy x hx).symm
    · exact hBc x hx y hy
  have hsup : A ⊔ B = Subgroup.closure ((A : Set G) ∪ (B : Set G)) := Subgroup.sup_eq_closure A B
  have hc : IsMulCommutative ↥(A ⊔ B) := by
    rw [hsup]
    exact Subgroup.isMulCommutative_closure (fun x hx y hy hxy => hcomm x hx y hy hxy)
  refine ⟨hc, fun x hx => ?_⟩
  rw [hsup] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact hA.2 x hx
    · exact hB.2 x hx
  | one => simp
  | mul x y hx hy hx' hy' =>
    have hxy : Commute x y := by
      have := hc.is_comm.comm ⟨x, by rw [hsup]; exact hx⟩ ⟨y, by rw [hsup]; exact hy⟩
      exact congrArg Subtype.val this
    rw [hxy.mul_pow, hx', hy', one_mul]
  | inv x hx hx' => rw [inv_pow, hx', inv_one]

theorem isElemAbelian_of_le {p : ℕ} {A B : Subgroup G} (hB : IsElemAbelian p B) (hAB : A ≤ B) :
    IsElemAbelian p A := CFSG.Open.IsElemAbelian.mono hB hAB

theorem isElemAbelian_zpowers {p : ℕ} {w : G} (hw : w ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers w) :=
  CFSG.Open.isElemAbelian_zpowers hw

def rhoSub (L : Subgroup G) (R : Subgroup (MulAut (barOf 3 L))) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (L : Set G) ∧ rho L g ∈ R}
  one_mem' := ⟨one_mem _, by rw [rho_one]; exact one_mem _⟩
  mul_mem' := by
    rintro g h ⟨hg, hgR⟩ ⟨hh, hhR⟩
    exact ⟨mul_mem hg hh, by rw [rho_mul hg hh]; exact mul_mem hgR hhR⟩
  inv_mem' := by
    rintro g ⟨hg, hgR⟩
    exact ⟨inv_mem hg, by rw [rho_inv hg]; exact inv_mem hgR⟩

theorem mem_rhoSub {L : Subgroup G} {R : Subgroup (MulAut (barOf 3 L))} {g : G} :
    g ∈ rhoSub L R ↔ g ∈ Subgroup.normalizer (L : Set G) ∧ rho L g ∈ R := Iff.rfl

theorem exists_mem_inf_not_mem_zpowers [Finite G] {A' C B' : Subgroup G} {b : G} (hb3 : b ^ 3 = 1)
    (hb1 : b ≠ 1) (hCB' : C ≤ B') (hA'B' : A' ≤ B') (hCcard : Nat.card C = 27)
    (hB'card : Nat.card B' = 81) (hA'card : Nat.card A' = 27) :
    ∃ c ∈ C, c ∈ A' ∧ c ∉ Subgroup.zpowers b := by
  by_contra hcon
  push Not at hcon
  have hb3c : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  have hidx : (A'.subgroupOf B').index = 3 := by
    have h1 := Subgroup.card_mul_index (A'.subgroupOf B')
    have h2 : Nat.card (A'.subgroupOf B') = Nat.card A' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'B').toEquiv
    rw [h2, hA'card, hB'card] at h1
    omega
  have hne : A'.relIndex B' ≠ 0 := by
    unfold Subgroup.relIndex; rw [hidx]; norm_num
  have hrel : A'.relIndex C ≤ 3 := by
    have := Subgroup.relIndex_le_of_le_right (H := A') hCB' hne
    unfold Subgroup.relIndex at this ⊢
    omega
  have hsub : A'.subgroupOf C ≤ (Subgroup.zpowers b).subgroupOf C := by
    intro x hx
    exact hcon x x.2 hx
  have hcard1 : Nat.card ↥((Subgroup.zpowers b).subgroupOf C) ≤ 3 := by
    have : Function.Injective (fun x : ↥((Subgroup.zpowers b).subgroupOf C) =>
        (⟨(x.1 : G), x.2⟩ : ↥(Subgroup.zpowers b))) := by
      intro u v h
      have h' : ((u.1 : ↥C) : G) = ((v.1 : ↥C) : G) := by
        have := congrArg (fun z : ↥(Subgroup.zpowers b) => (z : G)) h
        simpa using this
      exact Subtype.ext (Subtype.ext h')
    have := Nat.card_le_card_of_injective _ this
    omega
  have hcard2 : Nat.card ↥(A'.subgroupOf C) ≤ 3 :=
    (Subgroup.card_le_of_le hsub).trans hcard1
  have h3 := Subgroup.card_mul_index (A'.subgroupOf C)
  rw [hCcard] at h3
  unfold Subgroup.relIndex at hrel
  have : Nat.card ↥(A'.subgroupOf C) * (A'.subgroupOf C).index ≤ 3 * 3 :=
    Nat.mul_le_mul hcard2 hrel
  omega

end Lemma513Ns

open Lemma513Ns in
theorem lemma513_of_inputs (h53 : Lemma53) (h54 : Lemma54) (h55 : Lemma55) (h56 : Lemma56)
    (h510 : Lemma510) (h510ii : Lemma510ii) (h512 : Lemma512)
    (hAut : InputInnDiagStructure) : Lemma513 := by
  intro G _ _ m hstd hc4 B hB b hb hb1 L hL hbL
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := (h56 G m hstd hc4 B hB b hb hb1).2 L hL
  have hBel : IsElemAbelian 3 B := hB.1.1
  have hBcard : Nat.card B = 3 ^ 4 := by rw [hB.1.2.1, hc4.2.1]
  have hqs : CFSG.Open.IsQuasisimple (barOf 3 L) := isQuasisimple_quotient_of_glaPComponent hL.1
  have hT := (h510 G m hstd hc4 B hB b hb hb1 L hL).1
  have hZle := card_center_le_three_of_type hqs hT
  have hbc : ∀ l ∈ L, b * l = l * b := fun l hl => by
    have := Subgroup.mem_centralizer_iff.1 (hL.1.1 hl) b rfl
    exact this
  have hb3 : b ^ 3 = 1 := hBel.2 b hb
  have hZ : Nat.card (Subgroup.center (barOf 3 L)) = 3 := by
    set bb : barOf 3 L := QuotientGroup.mk ⟨b, hbL⟩ with hbb
    have hbbc : bb ∈ Subgroup.center (barOf 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      induction g using QuotientGroup.induction_on with | H l => ?_
      rw [hbb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hbc l l.2).symm
    have hbb1 : bb ≠ 1 := by
      intro h1
      have hbO : b ∈ GLAPPrimeCoreOf 3 L := (mk_eq_one_iff_mem hbL).1 h1
      have hd := Subgroup.orderOf_dvd_natCard _ hbO
      rw [orderOf_eq_prime hb3 hb1] at hd
      exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three L hd
    have hbb3 : bb ^ 3 = 1 := by
      rw [hbb, ← QuotientGroup.mk_pow]
      have : (⟨b, hbL⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
      rw [this]; rfl
    have hd : 3 ∣ Nat.card (Subgroup.center (barOf 3 L)) := by
      have := Subgroup.orderOf_dvd_natCard _ hbbc
      rwa [orderOf_eq_prime hbb3 hbb1] at this
    have hpos : 0 < Nat.card (Subgroup.center (barOf 3 L)) := Nat.card_pos
    obtain ⟨t, ht⟩ := hd
    omega
  obtain ⟨hW9, hexp, hcov⟩ := h510ii G m hstd hc4 B hB b hb hb1 L hL
  obtain ⟨hidx, hfield⟩ := hAut (barOf 3 L) hqs hT
  obtain ⟨y, C, hyL, hy3, hy1, hyBt, hCB, hbC, hcq, hyC, hCcard, hyBC⟩ :=
    construct_Bstar hBel hBN hZ hb hbc hW9 hexp hidx
  set B' := Subgroup.zpowers y ⊔ C with hB'
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := le_normalizer_self L hyL
  have hB'el : IsElemAbelian 3 B' :=
    isElemAbelian_sup_comm (Lemma513Ns.isElemAbelian_zpowers hy3) (isElemAbelian_of_le hBel hCB)
      (fun a ha c hc => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        exact (Commute.zpow_left (show Commute y c from hyC c hc) k).eq)
  have hB'N : B' ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (by rw [Subgroup.zpowers_le]; exact hyN) (hCB.trans hBN)
  have hB'BL : B' ≤ B ⊔ L :=
    sup_le (by rw [Subgroup.zpowers_le]; exact Subgroup.mem_sup_right hyL)
      (hCB.trans le_sup_left)
  have hyB' : y ∈ B' := Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  have hbB' : b ∈ B' := Subgroup.mem_sup_right hbC
  have hrhoB' : ∀ g ∈ B', rho L g ∈ autBar 3 B L := by
    have hle : B' ≤ rhoSub L (autBar 3 B L) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]; exact ⟨hyN, hyBt⟩
      · intro c hc
        exact ⟨hBN (hCB hc), (mem_autBar_iff hBN _).2 ⟨c, hCB hc, rfl⟩⟩
    exact fun g hg => (hle hg).2
  have hkey : ∀ w ∈ B', rho L w ∈ innerDiag (barOf 3 L) → rho L w ∈ Subgroup.zpowers (rho L y) :=
    fun w hw hwW => key_claim hZ hW9 hcov hB'el hB'N hrhoB' hyL hyB' hy1 hw hwW
  obtain ⟨hyC', hC27, hB'card⟩ := card_Bstar hBN hBcard hyL hy3 hy1 hCB hyC hCcard hyBC hW9 hkey
  have hrank : 4 ≤ CFSG.Open.pRank 3 B' := by
    rw [pRank_eq_of_card Nat.prime_three hB'el hB'card]
  obtain ⟨A', hA'B', hA'card, hyA', hA'W⟩ := exists_A' hB'el hB'N hB'card hyB' hy1 hkey
  have hA'el : IsElemAbelian 3 A' := isElemAbelian_of_le hB'el hA'B'
  have hA'E : IsEkIn 3 3 B' A' := ⟨hA'B', hA'el, hA'card⟩
  have hA'N : A' ≤ Subgroup.normalizer (L : Set G) := hA'B'.trans hB'N
  have hfieldA : ∀ a ∈ A', InducesFieldAut 3 L a := by
    intro a ha
    have haN := hA'N ha
    refine ⟨haN, ?_⟩
    rw [← rho_of_mem haN]
    by_cases hW : rho L a ∈ innerDiag (barOf 3 L)
    · rw [hA'W a ha hW]; exact Or.inl rfl
    · apply hfield _ _ hW
      rw [← rho_pow haN, hB'el.2 a (hA'B' ha), rho_one]
  have hCB' : C ≤ B' := le_sup_right
  obtain ⟨c, hcC, hcA, hcb⟩ := exists_mem_inf_not_mem_zpowers hb3 hb1 hCB' hA'B' hC27 hB'card hA'card
  have hc3 : c ^ 3 = 1 := hBel.2 c (hCB hcC)
  have hbcomm : ∀ g ∈ B', ∀ h ∈ B', g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hB'el.1.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩)
  have hbB'c : b * c = c * b := hbcomm b hbB' c (hCB' hcC)
  set D := Subgroup.zpowers b ⊔ Subgroup.zpowers c with hD
  have hDel : IsElemAbelian 3 D :=
    isElemAbelian_sup_comm (Lemma513Ns.isElemAbelian_zpowers hb3)
      (Lemma513Ns.isElemAbelian_zpowers hc3)
      (fun a ha d hd => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
        exact (Commute.zpow_zpow (show Commute b c from hbB'c) i j).eq)
  have hDcard : Nat.card D = 3 ^ 2 := by
    rw [hD, card_sup_zpowers_of_pow_three_eq_one hc3 hcb ?_]
    · rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]; norm_num
    · intro h hh
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact (Commute.zpow_left (show Commute b c from hbB'c) i).eq
  have hDB : IsEkIn 3 2 B D :=
    ⟨sup_le (by rw [Subgroup.zpowers_le]; exact hb)
      (by rw [Subgroup.zpowers_le]; exact hCB hcC), hDel, hDcard⟩
  have hbD : b ∈ D := Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hDB' : D ≤ B' :=
    sup_le (by rw [Subgroup.zpowers_le]; exact hbB')
      (by rw [Subgroup.zpowers_le]; exact hCB' hcC)
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hBN hb
  have hrhob : rho L b = 1 := rho_eq_one_of_commute hbN hbc
  have hfieldAb : ∀ g ∈ A' ⊔ Subgroup.zpowers b, InducesFieldAut 3 L g := by
    have hle : A' ⊔ Subgroup.zpowers b ≤ rhoSub L (autBar 3 A' L) := by
      refine sup_le (fun a ha => ⟨hA'N ha, (mem_autBar_iff hA'N _).2 ⟨a, ha, rfl⟩⟩) ?_
      rw [Subgroup.zpowers_le]
      exact ⟨hbN, by rw [hrhob]; exact one_mem _⟩
    intro g hg
    obtain ⟨hgN, hgR⟩ := hle hg
    obtain ⟨a, ha, hag⟩ := (mem_autBar_iff hA'N _).1 hgR
    obtain ⟨_, hfa⟩ := hfieldA a ha
    refine ⟨hgN, ?_⟩
    rw [← rho_of_mem hgN, ← hag, rho_of_mem (hA'N ha)]
    exact hfa
  have hb12 : ∀ a ∈ A', a ≠ 1 → b ∈ oPrimePOf 3 (Subgroup.centralizer ({a} : Set G)) := by
    intro a ha ha1
    have haB' : a ∈ B' := hA'B' ha
    have ha3 : orderOf a = 3 := orderOf_eq_prime (hB'el.2 a haB') ha1
    refine h512 G m hstd hc4 B hB b hb hb1 L hL hbL D hDB hbD a ?_ ha3 ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hbcomm h hbB' a haB'
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hbcomm h (hDB' hh) a haB'
    · intro g hg
      apply hfieldAb g
      have hle : D ⊔ Subgroup.zpowers a ≤ A' ⊔ Subgroup.zpowers b :=
        sup_le (sup_le (by rw [Subgroup.zpowers_le]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
          (by rw [Subgroup.zpowers_le]; exact Subgroup.mem_sup_left hcA))
          (by rw [Subgroup.zpowers_le]; exact Subgroup.mem_sup_left ha)
      exact hle hg
  obtain ⟨hB'0, hcommU⟩ := h55 G m hstd hc4 B' hB'el hrank b hbB' hb1 A' hA'E L hL.1 hfieldA hb12
  have hnotU : ¬ IsUpsilonComponent B' b L := by
    intro hU
    have h2 := h54 G m hstd hc4 B' (isBOneMax_of_isBZeroMax hB'0) b hbB' hb1 L hU A' hA'B' hfieldA
    rw [pRank_eq_of_card Nat.prime_three hA'el hA'card] at h2
    omega
  refine ⟨B', hB'0, ⟨hbB', hB'BL, ?_, fun g hg => Subgroup.mem_sup_right (hcq hg)⟩,
    ⟨A', hA'E, hfieldA⟩, hnotU, fun x hx hx1 =>
      upsilon_le_of_comm h53 h56 m hstd hc4 hB'0 hbB' hb1 hx hx1 (hcommU x hx hx1)⟩
  intro h
  exact not_mem_oPrimePOf_of_rho_ne_one hqs hyL hy1 (h ⟨hyB', hyL⟩)


end CFSG.HardMathSupport.Solomon.LocalBalance
