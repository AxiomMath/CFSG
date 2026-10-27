module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.AGL81I811CycDefs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Sections

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811

variable {X : Type} [Group X]

theorem map_conj_eq_of_mem_normalizer' {H : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (H : Set X)) : H.map (MulAut.conj g).toMonoidHom = H := by
  refine SetLike.coe_injective ?_
  rw [Subgroup.coe_map]
  exact Subgroup.mem_normalizer_iff_conj_image_eq.1 hg

@[expose] noncomputable def conjAut {J : Subgroup X} {l : X}
    (hl : l ∈ Subgroup.normalizer (J : Set X)) :
    ↥J ≃* ↥J :=
  (MulEquiv.subgroupMap (MulAut.conj l) J).trans
    (MulEquiv.subgroupCongr (map_conj_eq_of_mem_normalizer' hl))

theorem conjAut_coe {J : Subgroup X} {l : X} (hl : l ∈ Subgroup.normalizer (J : Set X))
    (x : J) :
    ((conjAut hl x : J) : X) = l * (x : X) * l⁻¹ :=
  rfl

@[expose] noncomputable def conjQuotAut {J Y : Subgroup X} [(Y.subgroupOf J).Normal] {l : X}
    (hlJ : l ∈ Subgroup.normalizer (J : Set X)) (hlY : l ∈ Subgroup.normalizer (Y : Set X)) :
    (↥J ⧸ Y.subgroupOf J) ≃* (↥J ⧸ Y.subgroupOf J) :=
  QuotientGroup.congr (Y.subgroupOf J) (Y.subgroupOf J) (conjAut hlJ) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
      rw [Subgroup.mem_subgroupOf]
      change ((conjAut hlJ y : J) : X) ∈ Y
      rw [conjAut_coe]
      exact (Subgroup.mem_normalizer_iff.mp hlY _).mp hy
    · intro hx
      refine ⟨(conjAut hlJ).symm x, ?_, by simp⟩
      rw [Subgroup.mem_subgroupOf] at hx
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      have h1 : ((conjAut hlJ).symm x : X) = l⁻¹ * (x : X) * l := by
        have h2 := conjAut_coe hlJ ((conjAut hlJ).symm x)
        rw [MulEquiv.apply_symm_apply] at h2
        rw [h2]
        group
      rw [h1]
      have h3 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlY) (x : X)).mp hx
      simpa using h3)

theorem conjQuotAut_mk {J Y : Subgroup X} [(Y.subgroupOf J).Normal] {l : X}
    (hlJ : l ∈ Subgroup.normalizer (J : Set X)) (hlY : l ∈ Subgroup.normalizer (Y : Set X))
    (x : J) :
    conjQuotAut hlJ hlY (x : ↥J ⧸ Y.subgroupOf J) = ((conjAut hlJ x : J) : ↥J ⧸ Y.subgroupOf J) :=
  QuotientGroup.congr_mk _ _ _ _ _

@[expose] noncomputable def conjQuotHom {J Y L : Subgroup X} [(Y.subgroupOf J).Normal]
    (hLJ : L ≤ Subgroup.normalizer (J : Set X)) (hLY : L ≤ Subgroup.normalizer (Y : Set X)) :
    ↥L →* MulAut (↥J ⧸ Y.subgroupOf J) where
  toFun l := conjQuotAut (hLJ l.2) (hLY l.2)
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [conjQuotAut_mk]
      congr 1
      ext
      simp [conjAut_coe]
  map_mul' a b := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [MulAut.mul_apply, conjQuotAut_mk, conjQuotAut_mk, conjQuotAut_mk]
      congr 1
      ext
      simp only [conjAut_coe, Subgroup.coe_mul]
      group

theorem conjQuotHom_mk {J Y L : Subgroup X} [(Y.subgroupOf J).Normal]
    (hLJ : L ≤ Subgroup.normalizer (J : Set X)) (hLY : L ≤ Subgroup.normalizer (Y : Set X))
    (l : L) (x : J) :
    conjQuotHom hLJ hLY l (x : ↥J ⧸ Y.subgroupOf J) =
      ((conjAut (hLJ l.2) x : J) : ↥J ⧸ Y.subgroupOf J) :=
  conjQuotAut_mk (hLJ l.2) (hLY l.2) x

variable [Finite X]

theorem exists_mem_centralizer_of_fix {Y A : Subgroup X}
    (hAY : A ≤ Subgroup.normalizer (Y : Set X)) (hA : IsPGroup 3 A)
    (hY3 : ¬ 3 ∣ Nat.card Y) {j : X} (hfix : ∀ a ∈ A, j⁻¹ * (a * j * a⁻¹) ∈ Y) :
    ∃ c : X, c ∈ Subgroup.centralizer (A : Set X) ∧ c⁻¹ * j ∈ Y := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let α := {x : X // x⁻¹ * j ∈ Y}
  have hmem : ∀ (a : A) (x : α), ((a : X) * x.1 * (a : X)⁻¹)⁻¹ * j ∈ Y := by
    intro a x
    have h1 : (a : X) * (x.1⁻¹ * j) * (a : X)⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hAY a.2) _).mp x.2
    have h2 : (j⁻¹ * ((a : X) * j * (a : X)⁻¹))⁻¹ ∈ Y := Y.inv_mem (hfix a a.2)
    have h3 := Y.mul_mem h1 h2
    have he : (a : X) * (x.1⁻¹ * j) * (a : X)⁻¹ * (j⁻¹ * ((a : X) * j * (a : X)⁻¹))⁻¹ =
        ((a : X) * x.1 * (a : X)⁻¹)⁻¹ * j := by group
    rwa [he] at h3
  let _ : MulAction ↥A α :=
    { smul := fun a x => ⟨(a : X) * x.1 * (a : X)⁻¹, hmem a x⟩
      one_smul := fun x => Subtype.ext (by
        change ((1 : ↥A) : X) * x.1 * ((1 : ↥A) : X)⁻¹ = x.1
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        change ((a * b : A) : X) * x.1 * ((a * b : A) : X)⁻¹ =
          (a : X) * ((b : X) * x.1 * (b : X)⁻¹) * (a : X)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hcard : Nat.card α = Nat.card Y := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1⁻¹ * j, x.2⟩
        invFun := fun y => ⟨j * (y : X)⁻¹, by simp [mul_assoc]⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun y => Subtype.ext (by simp [mul_assoc]) }
  have hmod := hA.card_modEq_card_fixedPoints α
  have hne : (MulAction.fixedPoints ↥A α).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have h0 : Nat.card (MulAction.fixedPoints ↥A α) = 0 := by rw [h]; simp
    rw [h0, hcard] at hmod
    exact hY3 (Nat.modEq_zero_iff_dvd.mp hmod)
  obtain ⟨x, hx⟩ := hne
  refine ⟨x.1, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_, x.2⟩
  have h := congrArg Subtype.val (hx ⟨a, ha⟩)
  change a * x.1 * a⁻¹ = x.1 at h
  calc a * x.1 = a * x.1 * a⁻¹ * a := by group
    _ = x.1 * a := by rw [h]

theorem conj_mem_of_perfect_of_card_le_four {J Y L : Subgroup X} [(Y.subgroupOf J).Normal]
    (hLJ : L ≤ Subgroup.normalizer (J : Set X)) (hLY : L ≤ Subgroup.normalizer (Y : Set X))
    [Group.IsPerfect ↥L] (h4 : Nat.card (↥J ⧸ Y.subgroupOf J) ≤ 4) :
    ∀ l ∈ L, ∀ j ∈ J, j⁻¹ * (l * j * l⁻¹) ∈ Y := by
  classical
  set ρ := conjQuotHom (Y := Y) hLJ hLY with hρ
  have hsolv : Group.IsSolvable (MulAut (↥J ⧸ Y.subgroupOf J)) := by
    have := Equiv.Perm.isSolvable h4
    exact Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm _) fun a b h =>
      MulEquiv.ext fun x => congrArg (fun e : Equiv.Perm _ => e x) h
  obtain ⟨n, hn⟩ := hsolv.solvable
  have hρ1 : ∀ l : L, ρ l = 1 := by
    intro l
    have hl : l ∈ derivedSeries ↥L n := by
      rw [Group.IsPerfect.derivedSeries_eq_top]
      exact Subgroup.mem_top l
    have := map_derivedSeries_le_derivedSeries ρ n ⟨l, hl, rfl⟩
    rwa [hn, Subgroup.mem_bot] at this
  intro l hl j hj
  have h := congrArg (fun φ : MulAut (↥J ⧸ Y.subgroupOf J) => φ ((⟨j, hj⟩ : J) : ↥J ⧸ _))
    (hρ1 ⟨l, hl⟩)
  simp only [hρ, conjQuotHom_mk, MulAut.one_apply] at h
  have h2 := QuotientGroup.eq.mp h
  rw [Subgroup.mem_subgroupOf] at h2
  have h3 : ((conjAut (hLJ hl) ⟨j, hj⟩ : J) : X) = l * j * l⁻¹ := conjAut_coe _ _
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, h3] at h2
  have h4 := Y.inv_mem h2
  simpa [mul_assoc] using h4

theorem exists_fix_of_card_eight {J Y A : Subgroup X} [(Y.subgroupOf J).Normal]
    (hAJ : A ≤ Subgroup.normalizer (J : Set X)) (hAY : A ≤ Subgroup.normalizer (Y : Set X))
    (hA : IsPGroup 3 A) (h8 : Nat.card (↥J ⧸ Y.subgroupOf J) = 8) :
    ∃ j ∈ J, j ∉ Y ∧ ∀ a ∈ A, j⁻¹ * (a * j * a⁻¹) ∈ Y := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ := conjQuotHom (Y := Y) hAJ hAY with hρ
  let _ : MulAction ↥A (↥J ⧸ Y.subgroupOf J) := MulAction.compHom _ ρ
  have hmod := hA.card_modEq_card_fixedPoints (↥J ⧸ Y.subgroupOf J)
  rw [h8] at hmod
  have h1 : (1 : ↥J ⧸ Y.subgroupOf J) ∈ MulAction.fixedPoints ↥A (↥J ⧸ Y.subgroupOf J) :=
    fun a => map_one (ρ a)
  by_contra hno
  push Not at hno
  have hsub : MulAction.fixedPoints ↥A (↥J ⧸ Y.subgroupOf J) ⊆ {1} := by
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H x =>
      by_contra hx1
      have hxY : (x : X) ∉ Y := by
        intro h
        apply hx1
        rw [Set.mem_singleton_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact h
      obtain ⟨a, ha, hfa⟩ := hno x x.2 hxY
      apply hfa
      have h := hq ⟨a, ha⟩
      change ρ ⟨a, ha⟩ (x : ↥J ⧸ Y.subgroupOf J) = (x : ↥J ⧸ Y.subgroupOf J) at h
      rw [hρ, conjQuotHom_mk] at h
      have h2 := QuotientGroup.eq.mp h
      rw [Subgroup.mem_subgroupOf] at h2
      have h3 : ((conjAut (hAJ ha) x : J) : X) = a * x * a⁻¹ := conjAut_coe _ _
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, h3] at h2
      have h4 := Y.inv_mem h2
      simpa [mul_assoc] using h4
  have hc : Nat.card (MulAction.fixedPoints ↥A (↥J ⧸ Y.subgroupOf J)) = 1 := by
    have heq : MulAction.fixedPoints ↥A (↥J ⧸ Y.subgroupOf J) = {1} :=
      Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr h1)
    rw [heq]
    simp
  rw [hc] at hmod
  exact absurd hmod (by decide)

theorem not_two_dvd_relIndex_of_comm {J Z L₀ A₀ U : Subgroup X} (hZJ : Z ≤ J)
    [hZn : (Z.subgroupOf J).Normal] (hcomm : ∀ a ∈ J, ∀ b ∈ J, a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hLJ : L₀ ≤ Subgroup.normalizer (J : Set X)) (hLZ : L₀ ≤ Subgroup.normalizer (Z : Set X))
    [Group.IsPerfect ↥L₀] (hAL : A₀ ≤ L₀) (hA3 : IsPGroup 3 A₀) (hJ3 : ¬ 3 ∣ Nat.card J)
    (hC : J ⊓ Subgroup.centralizer (A₀ : Set X) ≤ Z) (hUZ : U ≤ Z) (hU2 : IsPGroup 2 U)
    (hbd : ∀ S : Subgroup X, S ≤ J → IsPGroup 2 S → Nat.card S ≤ 8 * Nat.card U) :
    ¬ 2 ∣ Z.relIndex J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h2
  set π := QuotientGroup.mk' (Z.subgroupOf J) with hπ
  have hπmem : ∀ x : J, π x = 1 ↔ (x : X) ∈ Z := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hQc : ∀ q₁ q₂ : ↥J ⧸ Z.subgroupOf J, q₁ * q₂ = q₂ * q₁ := by
    intro q₁ q₂
    induction q₁ using QuotientGroup.induction_on with
    | H x =>
      induction q₂ using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have := hcomm (y : X)⁻¹ (J.inv_mem y.2) (x : X)⁻¹ (J.inv_mem x.2)
        simpa [mul_assoc] using this
  have hpow : ∀ x : J, ∀ k : ℕ, ((x : X) ^ 2 ^ k ∈ Z ↔ π x ^ 2 ^ k = 1) := fun x k => by
    rw [← map_pow, hπmem, Subgroup.coe_pow]
  let Z₃ : Subgroup X :=
    { carrier := {x | ∃ hx : x ∈ J, ∃ k : ℕ, π ⟨x, hx⟩ ^ 2 ^ k = 1}
      one_mem' := ⟨J.one_mem, 0, by
        change π 1 ^ 2 ^ 0 = 1
        simp⟩
      mul_mem' := by
        rintro a b ⟨ha, k, hk⟩ ⟨hb, l, hl⟩
        refine ⟨J.mul_mem ha hb, k + l, ?_⟩
        have hab : π ⟨a * b, J.mul_mem ha hb⟩ = π ⟨a, ha⟩ * π ⟨b, hb⟩ := by
          rw [← map_mul]
          rfl
        rw [hab, (Commute.mul_pow (hQc _ _) _), pow_add, pow_mul, hk, one_pow, one_mul,
          mul_comm (2 ^ k), pow_mul, hl, one_pow]
      inv_mem' := by
        rintro a ⟨ha, k, hk⟩
        refine ⟨J.inv_mem ha, k, ?_⟩
        have : π ⟨a⁻¹, J.inv_mem ha⟩ = (π ⟨a, ha⟩)⁻¹ := by
          rw [← map_inv]
          rfl
        rw [this, inv_pow, hk, inv_one] }
  have hZ₃J : Z₃ ≤ J := fun x hx => hx.1
  have hZZ₃ : Z ≤ Z₃ := fun x hx => ⟨hZJ hx, 0, by
    rw [pow_zero, pow_one]
    exact (hπmem ⟨x, hZJ hx⟩).mpr hx⟩
  have hZn₃ : (Z.subgroupOf Z₃).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 := hZn.conj_mem ⟨n, hZ₃J n.2⟩ hn ⟨g, hZ₃J g.2⟩
    rw [Subgroup.mem_subgroupOf] at h1 ⊢
    exact h1
  have hLZ₃ : L₀ ≤ Subgroup.normalizer (Z₃ : Set X) := by
    have key : ∀ l ∈ L₀, ∀ x ∈ Z₃, l * x * l⁻¹ ∈ Z₃ := by
      rintro l hl x ⟨hx, k, hk⟩
      have hlx : l * x * l⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hLJ hl) x).mp hx
      refine ⟨hlx, k, ?_⟩
      rw [← hpow] at hk ⊢
      have : (l * x * l⁻¹) ^ 2 ^ k = l * x ^ 2 ^ k * l⁻¹ := by
        rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply]
      change (l * x * l⁻¹) ^ 2 ^ k ∈ Z
      rw [this]
      exact (Subgroup.mem_normalizer_iff.mp (hLZ hl) _).mp hk
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key l hl x, fun hx => ?_⟩
    have := key l⁻¹ (L₀.inv_mem hl) _ hx
    simpa [mul_assoc] using this
  have hR2 : IsPGroup 2 (↥Z₃ ⧸ Z.subgroupOf Z₃) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨hx, k, hk⟩ := x.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow]
      exact (hpow ⟨x, hx⟩ k).mpr hk
  have hQ2 : 2 ∣ Nat.card (↥J ⧸ Z.subgroupOf J) := by
    rwa [← Subgroup.index, ← Subgroup.relIndex]
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 2 hQ2
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf J) q
  have hjZ : (j : X) ∉ Z := by
    intro h
    rw [(hπmem j).mpr h, orderOf_one] at hq
    omega
  have hjZ₃ : (j : X) ∈ Z₃ := ⟨j.2, 1, by
    rw [pow_one, ← hq]
    exact pow_orderOf_eq_one _⟩
  obtain ⟨n, hn⟩ := hR2.exists_card_eq
  have hn1 : 1 ≤ n := by
    by_contra hn0
    have : n = 0 := by omega
    rw [this, pow_zero] at hn
    have hsub : Subsingleton (↥Z₃ ⧸ Z.subgroupOf Z₃) := (Nat.card_eq_one_iff_unique.mp hn).1
    have : ((⟨(j : X), hjZ₃⟩ : Z₃) : ↥Z₃ ⧸ Z.subgroupOf Z₃) = 1 := Subsingleton.elim _ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
    exact hjZ this
  have hn3 : n ≤ 3 := by
    obtain ⟨u, hu⟩ := hU2.exists_card_eq
    have hdvd : 2 ^ (u + n) ∣ Nat.card Z₃ := by
      rw [pow_add, ← hu, ← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf Z₃),
        mul_comm, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZZ₃).toEquiv]
      exact Nat.mul_dvd_mul_left _ (Subgroup.card_dvd_of_le hUZ)
    obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
    have hSle : S.map Z₃.subtype ≤ J := (Subgroup.map_subtype_le S).trans hZ₃J
    have hS2 : IsPGroup 2 (S.map Z₃.subtype) :=
      (IsPGroup.of_card hS).map _
    have hb := hbd _ hSle hS2
    rw [Subgroup.card_map_of_injective Z₃.subtype_injective, hS, hu, pow_add] at hb
    have hu0 : 0 < 2 ^ u := by positivity
    have : 2 ^ n ≤ 8 := by
      rw [mul_comm 8] at hb
      exact Nat.le_of_mul_le_mul_left hb hu0
    by_contra h
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hnofix : ∀ x ∈ Z₃, x ∉ Z → ¬ ∀ a ∈ A₀, x⁻¹ * (a * x * a⁻¹) ∈ Z := by
    intro x hx hxZ hfix
    have hZ3 : ¬ 3 ∣ Nat.card Z := fun h => hJ3 (h.trans (Subgroup.card_dvd_of_le hZJ))
    obtain ⟨c, hcA, hcx⟩ := exists_mem_centralizer_of_fix (hAL.trans hLZ) hA3 hZ3 hfix
    have hcJ : c ∈ J := by
      have : c = x * (c⁻¹ * x)⁻¹ := by group
      rw [this]
      exact J.mul_mem (hZ₃J hx) (J.inv_mem (hZJ hcx))
    have hcZ : c ∈ Z := hC ⟨hcJ, hcA⟩
    apply hxZ
    have : x = c * (c⁻¹ * x) := by group
    rw [this]
    exact Z.mul_mem hcZ hcx
  rcases (show n ≤ 2 ∨ n = 3 by omega) with hn2 | hn3'
  · have h4 : Nat.card (↥Z₃ ⧸ Z.subgroupOf Z₃) ≤ 4 := by
      rw [hn]
      calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
        _ = 4 := by norm_num
    have htriv := conj_mem_of_perfect_of_card_le_four (J := Z₃) (Y := Z) hLZ₃ hLZ h4
    exact hnofix _ hjZ₃ hjZ fun a ha => htriv a (hAL ha) _ hjZ₃
  · have h8 : Nat.card (↥Z₃ ⧸ Z.subgroupOf Z₃) = 8 := by rw [hn, hn3']; norm_num
    obtain ⟨x, hx, hxZ, hfix⟩ :=
      exists_fix_of_card_eight (J := Z₃) (Y := Z) (hAL.trans hLZ₃) (hAL.trans hLZ) hA3 h8
    exact hnofix x hx hxZ hfix

theorem relIndex_sup_of_normal {J A Y : Subgroup X} (hAJ : A ≤ J) (hYJ : Y ≤ J)
    [(Y.subgroupOf J).Normal] : A.relIndex (Y ⊔ A) = A.relIndex Y := by
  have h1 := Subgroup.relIndex_sup_right (A.subgroupOf J) (Y.subgroupOf J)
  rw [← Subgroup.subgroupOf_sup hAJ hYJ, Subgroup.relIndex_subgroupOf (sup_le hAJ hYJ),
    Subgroup.relIndex_subgroupOf hAJ] at h1
  have e1 := Subgroup.relIndex_mul_card A (Y ⊔ A)
  have e2 := Subgroup.relIndex_mul_card Y (A ⊔ Y)
  have e3 := Subgroup.relIndex_mul_card Y A
  have e4 := Subgroup.relIndex_mul_card A Y
  rw [inf_of_le_left le_sup_right] at e1
  rw [inf_of_le_left le_sup_right, h1, sup_comm] at e2
  rw [inf_comm] at e3
  have hpos : 0 < Y.relIndex A * Nat.card ↥(A ⊓ Y) := by
    rw [e3]
    exact Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc A.relIndex (Y ⊔ A) * (Y.relIndex A * Nat.card ↥(A ⊓ Y))
      = A.relIndex (Y ⊔ A) * Nat.card A := by rw [e3]
    _ = Y.relIndex A * Nat.card Y := by rw [e1, e2]
    _ = A.relIndex Y * (Y.relIndex A * Nat.card ↥(A ⊓ Y)) := by rw [← e4]; ring

omit [Finite X] in
theorem mem_normalizer_sup {A B : Subgroup X} {g : X} (hA : g ∈ Subgroup.normalizer (A : Set X))
    (hB : g ∈ Subgroup.normalizer (B : Set X)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have h := congrArg (fun H : Subgroup X => (H : Set X))
    (show (A ⊔ B).map (MulAut.conj g).toMonoidHom = A ⊔ B by
      rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer' hA, map_conj_eq_of_mem_normalizer' hB])
  simpa [Subgroup.coe_map] using h

omit [Finite X] in
theorem mem_normalizer_inf {A B : Subgroup X} {g : X} (hA : g ∈ Subgroup.normalizer (A : Set X))
    (hB : g ∈ Subgroup.normalizer (B : Set X)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have h := congrArg (fun H : Subgroup X => (H : Set X))
    (show (A ⊓ B).map (MulAut.conj g).toMonoidHom = A ⊓ B by
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, map_conj_eq_of_mem_normalizer' hA,
        map_conj_eq_of_mem_normalizer' hB])
  simpa [Subgroup.coe_map] using h

omit [Finite X] in
theorem mem_normalizer_commutator {A : Subgroup X} {g : X}
    (hA : g ∈ Subgroup.normalizer (A : Set X)) :
    g ∈ Subgroup.normalizer ((⁅A, A⁆ : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have h := congrArg (fun H : Subgroup X => (H : Set X))
    (show (⁅A, A⁆).map (MulAut.conj g).toMonoidHom = ⁅A, A⁆ by
      rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer' hA])
  simpa [Subgroup.coe_map] using h

omit [Finite X] in
theorem normal_subgroupOf_of_commutator_le {J Z : Subgroup X} (h : ⁅J, J⁆ ≤ Z) :
    (Z.subgroupOf J).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hc : (g : X) * n * (g : X)⁻¹ * (n : X)⁻¹ ∈ Z :=
    h (Subgroup.commutator_mem_commutator g.2 n.2)
  have : ((g * n * g⁻¹ : J) : X) = ((g : X) * n * (g : X)⁻¹ * (n : X)⁻¹) * n := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [this]
  exact Z.mul_mem hc hn

omit [Finite X] in
theorem isCatalogGroup_of_isKGroup_quotient {E : Type*} [Group E] (hE : CFSG.Open.IsKGroup E)
    (N : Subgroup E) [N.Normal] (hs : IsSimpleGroup (E ⧸ N))
    (hnab : ∃ a b : E ⧸ N, a * b ≠ b * a) : CFSG.Open.IsCatalogGroup (E ⧸ N) := by
  have hNn : (N.subgroupOf (⊤ : Subgroup E)).Normal := Subgroup.normal_subgroupOf
  have hT : (N.subgroupOf (⊤ : Subgroup E)).map
      (Subgroup.topEquiv : ↥(⊤ : Subgroup E) ≃* E).toMonoidHom = N := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hy
    · intro hx
      exact ⟨⟨x, Subgroup.mem_top x⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  let e := QuotientGroup.congr (N.subgroupOf (⊤ : Subgroup E)) N Subgroup.topEquiv hT
  have hs' : IsSimpleGroup (↥(⊤ : Subgroup E) ⧸ N.subgroupOf ⊤) := e.isSimpleGroup_congr.2 hs
  have hnab' : ∃ a b : ↥(⊤ : Subgroup E) ⧸ N.subgroupOf ⊤, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  obtain ⟨i, ⟨f⟩⟩ := hE ⊤ N le_top hs' hnab'
  exact ⟨i, ⟨e.symm.trans f⟩⟩

theorem not_two_dvd_relIndex_inf_of_perfect (hSz : KFactCoprimeThreeTwoPart)
    (hK : CFSG.Open.IsKGroup X) {U B₀ L₀ A₀ : Subgroup X} (hU2 : IsPGroup 2 U) (hUB : U ≤ B₀)
    (hLU : L₀ ≤ Subgroup.normalizer (U : Set X)) (hLB : L₀ ≤ Subgroup.normalizer (B₀ : Set X))
    [Group.IsPerfect ↥L₀] (hAL : A₀ ≤ L₀) (hA3 : IsPGroup 3 A₀) :
    ∀ J : Subgroup X, U ≤ J → J ≤ Subgroup.normalizer (U : Set X) →
      L₀ ≤ Subgroup.normalizer (J : Set X) → ¬ 3 ∣ Nat.card J →
      J ⊓ Subgroup.centralizer (A₀ : Set X) ≤ B₀ →
      (∀ S : Subgroup X, S ≤ J → IsPGroup 2 S → Nat.card S ≤ 8 * Nat.card U) →
      ¬ 2 ∣ (J ⊓ B₀).relIndex J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro J
  induction hn : Nat.card J using Nat.strong_induction_on generalizing J with
  | _ n ih =>
  intro hUJ hJU hLJ hJ3 hC hbd
  rw [← hn] at hJ3
  by_cases hJeq : J = U
  · subst hJeq
    rw [inf_of_le_left hUB, Subgroup.relIndex_self]
    norm_num
  set Y := ⁅J, J⁆ ⊔ U with hYdef
  have hcJ : ⁅J, J⁆ ≤ J := Subgroup.commutator_le_self J
  have hYJ : Y ≤ J := sup_le hcJ hUJ
  have hLY : L₀ ≤ Subgroup.normalizer (Y : Set X) := fun l hl =>
    mem_normalizer_sup (mem_normalizer_commutator (hLJ hl)) (hLU hl)
  by_cases hYeq : Y = J
  · exfalso
    have hUn : (U.subgroupOf J).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hUJ).mpr hJU
    have hEnt : Nontrivial (↥J ⧸ U.subgroupOf J) := by
      rw [QuotientGroup.nontrivial_iff]
      intro h
      apply hJeq
      refine le_antisymm (fun x hx => ?_) hUJ
      have : (⟨x, hx⟩ : J) ∈ U.subgroupOf J := h ▸ Subgroup.mem_top _
      exact this
    have hEperf : Group.IsPerfect (↥J ⧸ U.subgroupOf J) := by
      rw [Group.isPerfect_def]
      have hsurj := QuotientGroup.mk'_surjective (U.subgroupOf J)
      have h1 : (commutator ↥J).map (QuotientGroup.mk' (U.subgroupOf J)) =
          commutator (↥J ⧸ U.subgroupOf J) := by
        rw [commutator_def, commutator_def, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ hsurj]
      have hcom : (⁅J, J⁆).subgroupOf J = commutator ↥J := by
        rw [← Subgroup.map_subtype_commutator J]
        exact Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
      have h2 : commutator ↥J ⊔ U.subgroupOf J = ⊤ := by
        rw [← hcom, ← Subgroup.subgroupOf_sup hcJ hUJ, ← hYdef, hYeq, Subgroup.subgroupOf_self]
      have h3 := congrArg (Subgroup.map (QuotientGroup.mk' (U.subgroupOf J))) h2
      rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ hsurj, h1,
        QuotientGroup.map_mk'_self, sup_bot_eq] at h3
      exact h3
    obtain ⟨N, hNn, -, hsimple⟩ :=
      CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.exists_normal_isSimpleGroup_quotient
        (↥J ⧸ U.subgroupOf J)
    have hnab : ∃ a b : (↥J ⧸ U.subgroupOf J) ⧸ N, a * b ≠ b * a := by
      by_contra hcomm
      push Not at hcomm
      have : Group.IsPerfect ((↥J ⧸ U.subgroupOf J) ⧸ N) :=
        Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
      have : IsMulCommutative ((↥J ⧸ U.subgroupOf J) ⧸ N) := ⟨⟨fun a b => hcomm a b⟩⟩
      have : Nontrivial ((↥J ⧸ U.subgroupOf J) ⧸ N) := hsimple.toNontrivial
      exact Group.IsPerfect.not_isMulCommutative ((↥J ⧸ U.subgroupOf J) ⧸ N) inferInstance
    have hKE : CFSG.Open.IsKGroup (↥J ⧸ U.subgroupOf J) :=
      CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient'
        (CFSG.LocalAnalysis.GLTheoremB.isKGroup_subgroup' hK J) _
    have hcat := isCatalogGroup_of_isKGroup_quotient hKE N hsimple hnab
    have hdvdE : Nat.card ((↥J ⧸ U.subgroupOf J) ⧸ N) ∣ Nat.card (↥J ⧸ U.subgroupOf J) :=
      Subgroup.card_quotient_dvd_card N
    have hEJ : Nat.card (↥J ⧸ U.subgroupOf J) ∣ Nat.card J :=
      Subgroup.card_quotient_dvd_card _
    have h3S : ¬ 3 ∣ Nat.card ((↥J ⧸ U.subgroupOf J) ⧸ N) := fun h =>
      hJ3 (h.trans (hdvdE.trans hEJ))
    have h64 := hSz _ hsimple hnab hcat h3S
    obtain ⟨u, hu⟩ := hU2.exists_card_eq
    have hJcard : Nat.card J = Nat.card U * Nat.card (↥J ⧸ U.subgroupOf J) := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (U.subgroupOf J)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUJ).toEquiv] at h
      rw [h, mul_comm]
    have hdvd : 2 ^ (u + 6) ∣ Nat.card J := by
      rw [hJcard, pow_add, ← hu]
      exact Nat.mul_dvd_mul_left _ ((show 2 ^ 6 = 64 by norm_num) ▸ h64.trans hdvdE)
    obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
    have hb := hbd (S.map J.subtype) (Subgroup.map_subtype_le S) ((IsPGroup.of_card hS).map _)
    rw [Subgroup.card_map_of_injective J.subtype_injective, hS, hu, pow_add] at hb
    have : 0 < 2 ^ u := by positivity
    nlinarith
  · have hYlt : Y < J := lt_of_le_of_ne hYJ hYeq
    have hcard : Nat.card Y < n := hn ▸ Subgroup.card_lt_of_lt hYlt
    have hYind := ih (Nat.card Y) hcard Y rfl le_sup_right (hYJ.trans hJU) hLY
      (fun h => hJ3 (h.trans (Subgroup.card_dvd_of_le hYJ)))
      (le_trans (inf_le_inf_right _ hYJ) hC) (fun S hS => hbd S (hS.trans hYJ))
    set Z := Y ⊔ (J ⊓ B₀) with hZdef
    have hZJ : Z ≤ J := sup_le hYJ inf_le_left
    have hcZ : ⁅J, J⁆ ≤ Z := le_sup_left.trans le_sup_left
    have : (Z.subgroupOf J).Normal := normal_subgroupOf_of_commutator_le hcZ
    have : (Y.subgroupOf J).Normal := normal_subgroupOf_of_commutator_le le_sup_left
    have hLZ : L₀ ≤ Subgroup.normalizer (Z : Set X) := fun l hl =>
      mem_normalizer_sup (hLY hl) (mem_normalizer_inf (hLJ hl) (hLB hl))
    have hZodd := not_two_dvd_relIndex_of_comm (J := J) (Z := Z) (L₀ := L₀) (A₀ := A₀) (U := U)
      hZJ (fun a ha b hb => hcZ (Subgroup.commutator_mem_commutator ha hb)) hLJ hLZ hAL hA3 hJ3
      (fun x hx => (le_sup_right : J ⊓ B₀ ≤ Z) ⟨hx.1, hC hx⟩) (le_sup_right.trans le_sup_left)
      hU2 hbd
    have hprod : (J ⊓ B₀).relIndex J = (J ⊓ B₀).relIndex Z * Z.relIndex J :=
      (Subgroup.relIndex_mul_relIndex (J ⊓ B₀) Z J le_sup_right hZJ).symm
    have hsup : (J ⊓ B₀).relIndex Z = (J ⊓ B₀).relIndex Y :=
      relIndex_sup_of_normal (J := J) inf_le_left hYJ
    have hYB : (J ⊓ B₀).relIndex Y = (Y ⊓ B₀).relIndex Y := by
      rw [← Subgroup.inf_relIndex_right (J ⊓ B₀) Y, ← Subgroup.inf_relIndex_right (Y ⊓ B₀) Y]
      congr 1
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨⟨-, hb⟩, hy⟩
        exact ⟨⟨hy, hb⟩, hy⟩
      · rintro ⟨⟨hy, hb⟩, -⟩
        exact ⟨⟨hYJ hy, hb⟩, hy⟩
    rw [hprod, hsup, hYB]
    intro h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · exact hYind h
    · exact hZodd h

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811
