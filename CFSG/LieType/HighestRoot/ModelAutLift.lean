module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieModelDefs
public import CFSG.ClassicalInvolution.ModelFacts.CentralLiftE6
public import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
public import CFSG.ClassicalInvolution.ModelFacts.Models

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (modelUniv IsFundTag)
open scoped commutatorElement

theorem eq_of_inv_mul_mem_center_of_isPerfect {Y H : Type*} [Group Y] [Group H]
    [Group.IsPerfect Y] (a b : Y →* H) (hab : ∀ y, (a y)⁻¹ * b y ∈ center H) : a = b := by
  let χ : Y →* center H :=
    { toFun := fun y => ⟨(a y)⁻¹ * b y, hab y⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun y y' => by
        apply Subtype.ext
        have hc : (a y')⁻¹ * ((a y)⁻¹ * b y) = ((a y)⁻¹ * b y) * (a y')⁻¹ :=
          Subgroup.mem_center_iff.1 (hab y) ((a y')⁻¹)
        change (a (y * y'))⁻¹ * b (y * y') = (a y)⁻¹ * b y * ((a y')⁻¹ * b y')
        rw [map_mul, map_mul, _root_.mul_inv_rev]
        calc (a y')⁻¹ * (a y)⁻¹ * (b y * b y') = ((a y')⁻¹ * ((a y)⁻¹ * b y)) * b y' := by
              simp only [mul_assoc]
          _ = ((a y)⁻¹ * b y) * (a y')⁻¹ * b y' := by rw [hc]
          _ = (a y)⁻¹ * b y * ((a y')⁻¹ * b y') := by simp only [mul_assoc] }
  have hker : _root_.commutator Y ≤ χ.ker := Abelianization.commutator_subset_ker χ
  have htop : _root_.commutator Y = ⊤ := Group.IsPerfect.commutator_eq_top
  refine MonoidHom.ext fun y => ?_
  have hy : y ∈ χ.ker := hker (htop ▸ Subgroup.mem_top y)
  exact inv_mul_eq_one.1 (congrArg Subtype.val (MonoidHom.mem_ker.1 hy))

theorem mem_center_of_commutator_mem_center {K : Type*} [Group K]
    (hK : CFSG.Open.IsQuasisimple K) {x : K} (hx : ∀ k : K, x * k * x⁻¹ * k⁻¹ ∈ center K) :
    x ∈ center K := by
  have : IsSimpleGroup (K ⧸ center K) := hK.2
  have : Group.IsPerfect K := ⟨hK.1⟩
  have hperf : Group.IsPerfect (K ⧸ center K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center K))
  have hZ : center (K ⧸ center K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (K ⧸ center K)) with h | h
    · exact h
    · exfalso
      have hab : _root_.commutator (K ⧸ center K) = ⊥ := by
        rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer, ← h]
        intro y _
        exact Subgroup.mem_centralizer_iff.mpr fun g hg => (Subgroup.mem_center_iff.mp hg y).symm
      rw [hperf.commutator_eq_top] at hab
      exact (bot_ne_top hab.symm)
  have hxZ : (QuotientGroup.mk x : K ⧸ center K) ∈ center (K ⧸ center K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 := hx k
    rw [← QuotientGroup.eq_one_iff] at h1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hxZ
  exact hxZ

theorem mulEquiv_mem_center_iff {G H : Type*} [Group G] [Group H] (τ : G ≃* H) {g : G} :
    τ g ∈ center H ↔ g ∈ center G := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h k
    apply τ.injective
    rw [map_mul, map_mul, h]
  · intro h k
    obtain ⟨k, rfl⟩ := τ.surjective k
    rw [← map_mul, ← map_mul, h]

theorem map_mem_center_of_surjective {K X : Type*} [Group K] [Group X] {f : K →* X}
    (hf : Function.Surjective f) {x : K} (hx : x ∈ center K) : f x ∈ center X := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨k, rfl⟩ := hf y
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx k]

theorem commutatorElement_mul_mem_center {Y : Type*} [Group Y] {a b z w : Y}
    (hz : z ∈ center Y) (hw : w ∈ center Y) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  have hw' := Subgroup.mem_center_iff.mp hw
  rw [commutatorElement_def, commutatorElement_def]
  have hzw : z * w * z⁻¹ = w := by rw [← hz' w]; group
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹ =
      a * (z * b) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by rw [← hz' b]
    _ = a * b * (z * w * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by rw [hzw]; group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [← hw' a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem modelAutLift :
    ModelAutLift := by
  intro t n p e hp hp2 hfund hadm X G _ _ _ _ ψ₀ ψ hψ₀ hker₀ hodd hZX hψ hkerψ τ
  have hf : CFSG.ClassicalInvolution.ModelFacts.IsFundTag t := by cases t <;> trivial
  have : Finite (modelUniv t n p e hp).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 hp hf hadm
  have hK : CFSG.Open.IsQuasisimple (modelUniv t n p e hp).K :=
    (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero t n p e hp hf hadm).1
  have : Group.IsPerfect (modelUniv t n p e hp).K := ⟨hK.1⟩
  have hXperf : Group.IsPerfect X := Group.IsPerfect.ofSurjective hψ₀
  have hP1 : ∀ x, ψ₀ x ∈ center X → x ∈ center (modelUniv t n p e hp).K := by
    intro x hx
    refine mem_center_of_commutator_mem_center hK fun k => hker₀ ?_
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      (Subgroup.mem_center_iff.1 hx (ψ₀ k)).symm]
    group
  have hP2 : ∀ x, ψ (ψ₀ x) ∈ center G → x ∈ center (modelUniv t n p e hp).K := by
    intro x hx
    refine mem_center_of_commutator_mem_center hK fun k => hP1 _ (hkerψ ?_)
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul,
      map_mul, map_inv, map_inv, (Subgroup.mem_center_iff.1 hx (ψ (ψ₀ k))).symm]
    group
  have hP3 : ∀ y, ψ y ∈ center G ↔ y ∈ center X := by
    intro y
    refine ⟨fun hy => ?_, fun hy => map_mem_center_of_surjective hψ hy⟩
    obtain ⟨x, rfl⟩ := hψ₀ y
    exact map_mem_center_of_surjective hψ₀ (hP2 x hy)
  have hτZ : ∀ g : G, τ g ∈ center G ↔ g ∈ center G := fun g => mulEquiv_mem_center_iff τ
  set q := QuotientGroup.mk' (center G) with hq
  set π : X →* G ⧸ center G := q.comp ψ with hπ
  set φ : (modelUniv t n p e hp).K →* G ⧸ center G :=
    q.comp (τ.toMonoidHom.comp (ψ.comp ψ₀)) with hφ
  have hπs : Function.Surjective π := fun s => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center G) s
    obtain ⟨y, rfl⟩ := hψ g
    exact ⟨y, rfl⟩
  have hφs : Function.Surjective φ := fun s => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center G) s
    obtain ⟨y, hy⟩ := hψ (τ.symm g)
    obtain ⟨k, rfl⟩ := hψ₀ y
    refine ⟨k, ?_⟩
    change q (τ (ψ (ψ₀ k))) = q g
    rw [hy, MulEquiv.apply_symm_apply]
  have hπker : π.ker = center X := by
    ext y
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hP3]
  have hφker : φ.ker = center (modelUniv t n p e hp).K := by
    ext x
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hτZ]
    refine ⟨hP2 x, fun hx => ?_⟩
    exact map_mem_center_of_surjective hψ (map_mem_center_of_surjective hψ₀ hx)
  have hS : IsSimpleGroup (G ⧸ center G) := by
    have e1 := QuotientGroup.quotientKerEquivOfSurjective φ hφs
    have e2 := QuotientGroup.quotientMulEquivOfEq hφker
    have : IsSimpleGroup ((modelUniv t n p e hp).K ⧸ center (modelUniv t n p e hp).K) := hK.2
    exact (e2.symm.trans e1).symm.isSimpleGroup
  have hSnc : ∃ a b : G ⧸ center G, a * b ≠ b * a := by
    by_contra hcon'
    have hcon : ∀ a b : G ⧸ center G, a * b = b * a := fun a b =>
      not_not.mp fun h => hcon' ⟨a, b, h⟩
    have hSperf : Group.IsPerfect (G ⧸ center G) := Group.IsPerfect.ofSurjective hφs
    have hab : _root_.commutator (G ⧸ center G) = ⊥ := by
      rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _ b _
      exact (hcon a b).symm
    rw [hSperf.commutator_eq_top] at hab
    obtain ⟨a, b, hab'⟩ := exists_pair_ne (G ⧸ center G)
    have ha : a ∈ (⊥ : Subgroup (G ⧸ center G)) := hab ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup (G ⧸ center G)) := hab ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    exact hab' (ha.trans hb.symm)
  obtain ⟨lam, hlam⟩ := CFSG.ClassicalInvolution.ModelFacts.centralLift p hp2 t n e hp hfund hadm
    X (G ⧸ center G) hSnc π φ hπs hφs hXperf (by rw [hπker]; exact hZX) hπker.le hφker
  have hlamk : ∀ k, q (ψ (lam k)) = q (τ (ψ (ψ₀ k))) := fun k => DFunLike.congr_fun hlam k
  have hkill : ψ₀.ker ≤ lam.ker := by
    intro k hk
    have h1 : lam k ∈ center X := by
      rw [← hπker, MonoidHom.mem_ker]
      change q (ψ (lam k)) = 1
      rw [hlamk]
      change φ k = 1
      rw [← MonoidHom.mem_ker, hφker]
      exact hker₀ hk
    have hko : Odd (orderOf k) := by
      have hdvd : orderOf (⟨k, hk⟩ : ψ₀.ker) ∣ Nat.card ψ₀.ker := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at hdvd
      exact Odd.of_dvd_nat hodd hdvd
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hZX) ⟨lam k, h1⟩
    rw [Subgroup.orderOf_mk] at hm
    have hlo : Odd (orderOf (lam k)) := Odd.of_dvd_nat hko (orderOf_map_dvd lam k)
    rw [hm] at hlo
    have hm0 : m = 0 := by
      by_contra hm0
      rw [Nat.odd_pow_iff hm0] at hlo
      exact absurd hlo (by decide)
    rw [hm0, pow_zero, orderOf_eq_one_iff] at hm
    exact hm
  set e₀ := QuotientGroup.quotientKerEquivOfSurjective ψ₀ hψ₀ with he₀
  set lam' : X →* X := (QuotientGroup.lift ψ₀.ker lam hkill).comp e₀.symm.toMonoidHom with hlam'
  have hlam'k : ∀ k, lam' (ψ₀ k) = lam k := by
    intro k
    have : e₀.symm (ψ₀ k) = (k : (modelUniv t n p e hp).K ⧸ ψ₀.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hlam', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this, QuotientGroup.lift_mk]
  have hsurj : Function.Surjective lam' := by
    have hXZ : ∀ y : X, ∃ k, (lam k)⁻¹ * y ∈ center X := by
      intro y
      obtain ⟨k, hk⟩ := hφs (π y)
      refine ⟨k, ?_⟩
      rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv]
      change (q (ψ (lam k)))⁻¹ * π y = 1
      rw [hlamk, ← hk]
      exact inv_mul_cancel _
    have hrange : lam'.range = ⊤ := by
      rw [eq_top_iff, ← hXperf.commutator_eq_top, _root_.commutator_def, Subgroup.commutator_le]
      intro y₁ _ y₂ _
      obtain ⟨k₁, hk₁⟩ := hXZ y₁
      obtain ⟨k₂, hk₂⟩ := hXZ y₂
      have e1 : y₁ = lam k₁ * ((lam k₁)⁻¹ * y₁) := by group
      have e2 : y₂ = lam k₂ * ((lam k₂)⁻¹ * y₂) := by group
      rw [e1, e2, commutatorElement_mul_mem_center hk₁ hk₂, ← map_commutatorElement]
      exact ⟨_, hlam'k _⟩
    exact MonoidHom.range_eq_top.mp hrange
  have hinj : Function.Injective lam' := Finite.injective_iff_surjective.mpr hsurj
  refine ⟨MulEquiv.ofBijective lam' ⟨hinj, hsurj⟩, fun x => ?_⟩
  have hagree := eq_of_inv_mul_mem_center_of_isPerfect (τ.toMonoidHom.comp ψ) (ψ.comp lam')
    (fun y => by
      obtain ⟨k, rfl⟩ := hψ₀ y
      rw [← QuotientGroup.eq_one_iff (N := center G)]
      change (q (τ (ψ (ψ₀ k))))⁻¹ * q (ψ (lam' (ψ₀ k))) = 1
      rw [hlam'k, hlamk, inv_mul_cancel])
  exact (DFunLike.congr_fun hagree x).symm

end CFSG.ComponentClassification.RankTwoOddLie
