module

public import CFSG.LieType.SeitzGeneration.HyperAnisoBlocks
public import CFSG.LieType.SeitzGeneration.HyperAveraging
public import CFSG.LieType.SeitzGeneration.SpFourMix

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.CTP Module

variable {p r : ℕ} {K : Type} [Field K]

structure SpAnisoSetup (p r : ℕ) (K : Type) [Field K] (A : Subgroup (StatedSp r K)) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  cast_ne_zero : (p : K) ≠ 0
  comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  pow_eq_one : ∀ a ∈ A, a ^ p = 1
  card_eq : Nat.card A = p ^ 3
  aniso : ∀ W : Submodule K (Fin r ⊕ Fin r → K), (∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0) →
    (∀ a ∈ A, ∀ w ∈ W, spEnd a w ∈ W) → W = ⊥

@[expose] def spRep (A : Subgroup (StatedSp r K)) : A →* Module.End K (Fin r ⊕ Fin r → K) where
  toFun a := spEnd (a : StatedSp r K)
  map_one' := spEnd_one
  map_mul' a b := spEnd_mul a.1 b.1

theorem spRep_apply (A : Subgroup (StatedSp r K)) (a : A) (v : Fin r ⊕ Fin r → K) :
    spRep A a v = spEnd (a : StatedSp r K) v := rfl

namespace SpAnisoSetup

variable {A : Subgroup (StatedSp r K)} (S : SpAnisoSetup p r K A)
include S

theorem comm' (a b : A) : a * b = b * a := Subtype.ext (S.comm a a.2 b b.2)

theorem pow' (a : A) : a ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact S.pow_eq_one a a.2)

theorem fact : Fact p.Prime := ⟨S.prime⟩

theorem finite : Finite A :=
  Nat.finite_of_card_ne_zero (by rw [S.card_eq]; exact pow_ne_zero 3 S.prime.ne_zero)

theorem eq_zero_of_line {v : Fin r ⊕ Fin r → K} (hv : ∀ a ∈ A, spEnd a v ∈ K ∙ v) : v = 0 := by
  have h := S.aniso (K ∙ v) (fun x hx y hy => ?_) (fun a ha w hw => ?_)
  · exact Submodule.span_singleton_eq_bot.mp h
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_smul, map_smul, LinearMap.smul_apply, spForm_isAlt.self_eq_zero, smul_zero,
      smul_zero]
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul]
    exact Submodule.smul_mem _ _ (hv a ha)

theorem fixed_eq_zero {v : Fin r ⊕ Fin r → K} (hv : v ∈ hyperFixed (spRep A) ⊤) : v = 0 :=
  S.eq_zero_of_line fun a ha => by
    have : spRep A ⟨a, ha⟩ v = v := mem_hyperFixed.1 hv _ (Subgroup.mem_top _)
    rw [← spRep_apply A ⟨a, ha⟩, this]
    exact Submodule.mem_span_singleton_self v

theorem blk_stable (F : Subgroup A) (a : A) {v : Fin r ⊕ Fin r → K}
    (hv : v ∈ hyperFixed (spRep A) F) : spRep A a v ∈ hyperFixed (spRep A) F :=
  apply_mem_hyperFixed S.comm' a hv

theorem sup_zpowers {F : Subgroup A} (hF : F.index = p) {x : A} (hx : x ∉ F) :
    F ⊔ Subgroup.zpowers x = ⊤ :=
  HyperBlocks.sup_zpowers_eq S.prime le_top (by rwa [Subgroup.relIndex_top_right])
    (Subgroup.mem_top x) hx

theorem eq_zero_of_fixed {F : Subgroup A} (hF : F.index = p) {x : A} (hx : x ∉ F)
    {v : Fin r ⊕ Fin r → K} (hv : v ∈ hyperFixed (spRep A) F) (hxv : spRep A x v = v) :
    v = 0 :=
  S.fixed_eq_zero (by rw [← S.sup_zpowers hF hx]; exact mem_hyperFixed_sup_zpowers hv hxv)

theorem card_hyperplane {F : Subgroup A} (hF : F.index = p) : Nat.card F = p ^ 2 := by
  have h := F.card_mul_index
  rw [hF, S.card_eq] at h
  have hp := S.prime.pos
  have : Nat.card F * p = p ^ 2 * p := by rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_right hp this

theorem sup_eq_top {F₁ F₂ : Subgroup A} (hF₁ : F₁.index = p) (hF₂ : F₂.index = p)
    (hne : F₁ ≠ F₂) : F₁ ⊔ F₂ = ⊤ :=
  HyperBlocks.sup_eq_of_ne_relIndex_prime S.prime le_top le_top
    (by rwa [Subgroup.relIndex_top_right]) (by rwa [Subgroup.relIndex_top_right]) hne

theorem blk_orth {F₁ F₂ : Subgroup A} (hF₁ : F₁.index = p) (hF₂ : F₂.index = p)
    (hne : F₁ ≠ F₂) {v w : Fin r ⊕ Fin r → K} (hv : v ∈ hyperFixed (spRep A) F₁)
    (hw : w ∈ hyperFixed (spRep A) F₂) : spForm r K v w = 0 := by
  classical
  have := S.finite
  have : Fintype F₁ := Fintype.ofFinite F₁
  set T : Module.End K (Fin r ⊕ Fin r → K) := ∑ f : F₁, spRep A f with hT
  have hTv : T v = (Fintype.card F₁ : K) • v := by
    rw [hT, LinearMap.sum_apply]
    rw [Finset.sum_congr rfl fun (f : F₁) _ => mem_hyperFixed.1 hv (f : A) f.prop, Finset.sum_const,
      Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hTw : T w = 0 := by
    apply S.fixed_eq_zero
    rw [mem_hyperFixed]
    have hstab : F₁ ⊔ F₂ ≤ HyperBlocks.stabVec (spRep A) (T w) := by
      refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · show spRep A g (T w) = T w
        rw [hT, LinearMap.sum_apply, map_sum]
        simp_rw [← Module.End.mul_apply, ← map_mul]
        exact Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : F₁))
          (fun f : F₁ => spRep A (g * f) w) (fun f : F₁ => spRep A f w) (fun f => rfl)
      · show spRep A g (T w) = T w
        rw [hT, LinearMap.sum_apply, map_sum]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [← Module.End.mul_apply, ← map_mul, S.comm' g f, map_mul, Module.End.mul_apply,
          mem_hyperFixed.1 hw g hg]
    intro g _
    exact (S.sup_eq_top hF₁ hF₂ hne ▸ hstab) (Subgroup.mem_top g)
  have hadj : spForm r K (T v) w = spForm r K v (T w) := by
    rw [hT, LinearMap.sum_apply, map_sum, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    have h : ∀ f : F₁, spForm r K (spRep A f v) w = spForm r K v (spRep A (f⁻¹ : F₁) w) :=
      fun f => by
        rw [← spEnd_isometry (f : StatedSp r K) v (spRep A (f⁻¹ : F₁) w)]
        congr 1
        rw [spRep_apply, ← Module.End.mul_apply, ← spEnd_mul]
        simp [spEnd_one]
    simp_rw [h]
    exact Fintype.sum_equiv (Equiv.inv F₁) _ _ (fun f => rfl)
  rw [hTv, hTw, map_zero, map_smul, LinearMap.smul_apply, smul_eq_mul] at hadj
  have hc : (Fintype.card F₁ : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, S.card_hyperplane hF₁]
    push_cast
    exact pow_ne_zero 2 S.cast_ne_zero
  exact (mul_eq_zero.mp hadj).resolve_left hc

theorem iSup_blk [Finite K] :
    ⨆ F : {F : Subgroup A // F.index = p}, hyperFixed (spRep A) F.1 = ⊤ := by
  have := S.fact
  refine eq_top_iff.2 fun m _ => ?_
  have h := mem_iSup_hyperFixed_top S.cast_ne_zero S.comm' S.pow' (spRep A) ⊤
    (fun _ _ _ => Submodule.mem_top) (k := 3) (by norm_num) S.card_eq (Submodule.mem_top (x := m))
  refine (iSup₂_le fun F hF => ?_ : (⨆ (F' : Subgroup A) (_ : F'.index = p),
    hyperFixed (spRep A) F' ⊓ ⊤) ≤ ⨆ F : {F : Subgroup A // F.index = p},
      hyperFixed (spRep A) F.1) h
  exact inf_le_left.trans (le_iSup (fun F : {F : Subgroup A // F.index = p} =>
    hyperFixed (spRep A) F.1) ⟨F, hF⟩)

theorem blk_nondeg [Finite K] {F : Subgroup A} (hF : F.index = p) :
    ((spForm r K).restrict (hyperFixed (spRep A) F)).Nondegenerate := by
  have hrefl : ((spForm r K).restrict (hyperFixed (spRep A) F)).IsRefl :=
    (show ((spForm r K).restrict (hyperFixed (spRep A) F)).IsAlt from
      fun w => spForm_isAlt (w : Fin r ⊕ Fin r → K)).isRefl
  refine hrefl.nondegenerate_iff_separatingLeft.mpr fun x hx => ?_
  have hall : ⨆ F' : {F : Subgroup A // F.index = p}, hyperFixed (spRep A) F'.1 ≤
      LinearMap.ker (spForm r K (x : Fin r ⊕ Fin r → K)) := by
    refine iSup_le fun F' y hy => ?_
    rw [LinearMap.mem_ker]
    by_cases hFF : F'.1 = F
    · subst hFF
      exact hx ⟨y, hy⟩
    · exact S.blk_orth hF F'.2 (Ne.symm hFF) x.2 hy
  rw [S.iSup_blk] at hall
  apply Subtype.ext
  exact spForm_nondegenerate.1 _ fun z => LinearMap.mem_ker.mp (hall Submodule.mem_top)

theorem two_le_finrank {F : Subgroup A} (h0 : hyperFixed (spRep A) F ≠ ⊥) :
    2 ≤ finrank K (hyperFixed (spRep A) F) := by
  by_contra hlt
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hle : K ∙ v ≤ hyperFixed (spRep A) F := (Submodule.span_singleton_le_iff_mem _ _).2 hv
  have h1 : finrank K (K ∙ v) = 1 := finrank_span_singleton hv0
  have heq : K ∙ v = hyperFixed (spRep A) F :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  exact hv0 (S.eq_zero_of_line fun a ha => heq ▸ S.blk_stable F ⟨a, ha⟩ hv)

theorem sq_add_add_one {F : Subgroup A} (hp3 : p = 3) (hF : F.index = p) {x : A} (hx : x ∉ F)
    {v : Fin r ⊕ Fin r → K} (hv : v ∈ hyperFixed (spRep A) F) :
    spRep A (x ^ 2) v + spRep A x v + v = 0 := by
  apply S.eq_zero_of_fixed hF hx
  · exact Submodule.add_mem _ (Submodule.add_mem _ (S.blk_stable F _ hv) (S.blk_stable F _ hv)) hv
  · have h3 : x ^ 3 = 1 := hp3 ▸ S.pow' x
    rw [map_add, map_add, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul,
      ← map_mul, ← pow_succ', show x ^ (2 + 1) = 1 from h3, map_one, Module.End.one_apply,
      show x * x = x ^ 2 from (sq x).symm]
    abel

theorem finrank_le_two_of_three [Finite K] {F : Subgroup A} (hp3 : p = 3) (hF : F.index = p) :
    finrank K (hyperFixed (spRep A) F) ≤ 2 := by
  classical
  by_contra hlt
  push Not at hlt
  set B := hyperFixed (spRep A) F with hB
  obtain ⟨x, hx⟩ : ∃ x : A, x ∉ F := by
    by_contra h
    push Not at h
    have : F = ⊤ := eq_top_iff.2 fun y _ => h y
    rw [this, Subgroup.index_top] at hF
    exact S.prime.one_lt.ne hF
  set b := Module.finBasis K B with hb
  set d := finrank K B
  let M : Matrix (Fin d) (Fin d) K := fun i j =>
    spForm r K (b i : Fin r ⊕ Fin r → K) (spRep A x (b j))
  obtain ⟨c, hc0, hc⟩ := exists_nonzero_zero_quadratic (σ := Fin d)
    (by rw [Fintype.card_fin]; omega) M
  set v : Fin r ⊕ Fin r → K := ∑ i, c i • (b i : Fin r ⊕ Fin r → K) with hvdef
  have hvB : v ∈ B := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2
  have hv0 : v ≠ 0 := by
    intro h
    apply hc0
    have h' : (∑ i, c i • b i : B) = 0 := by
      apply Subtype.ext
      simpa [hvdef] using h
    have := (Fintype.linearIndependent_iff.mp b.linearIndependent) c h'
    exact funext this
  have hform : spForm r K v (spRep A x v) = 0 := by
    rw [← hc]
    simp only [hvdef, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      dotProduct, Matrix.mulVec, M, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  set W : Submodule K (Fin r ⊕ Fin r → K) := Submodule.span K {v, spRep A x v} with hW
  have hiso : ∀ y ∈ W, ∀ z ∈ W, spForm r K y z = 0 := by
    intro y hy z hz
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hy
    obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.mp hz
    have h1 : spForm r K (spRep A x v) v = 0 := by
      rw [← spForm_isAlt.neg_eq, hform, neg_zero]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      spForm_isAlt.self_eq_zero, hform, h1]
    ring
  have hxW : ∀ w ∈ W, spRep A x w ∈ W := by
    intro w hw
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hw
    have hx2 := S.sq_add_add_one hp3 hF hx hvB
    have hx2' : spRep A x (spRep A x v) = -v - spRep A x v := by
      rw [← Module.End.mul_apply, ← map_mul, show x * x = x ^ 2 from (sq x).symm]
      linear_combination (norm := module) hx2
    rw [map_add, map_smul, map_smul, hx2']
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.neg_mem _
        (Submodule.subset_span (by simp))) (Submodule.subset_span (by simp))))
  have hFW : ∀ f ∈ F, ∀ w ∈ W, spRep A f w = w := by
    intro f hf w hw
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hw
    rw [map_add, map_smul, map_smul, mem_hyperFixed.1 hvB f hf,
      mem_hyperFixed.1 (S.blk_stable F x hvB) f hf]
  have hAW : ∀ a : A, ∀ w ∈ W, spRep A a w ∈ W := by
    intro a w hw
    have : Finite A := Nat.finite_of_card_ne_zero (by
      rw [S.card_eq]; exact pow_ne_zero 3 S.prime.ne_zero)
    have hnorm : (Subgroup.zpowers x).Normal :=
      ⟨fun n hn g => by rw [S.comm' g n, mul_inv_cancel_right]; exact hn⟩
    have ha : a ∈ F ⊔ Subgroup.zpowers x := by
      rw [S.sup_zpowers hF hx]; exact Subgroup.mem_top a
    obtain ⟨f, hf, y, hy, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hy)
    have hpow : ∀ n : ℕ, ∀ w ∈ W, spRep A (x ^ n) w ∈ W := by
      intro n
      induction n with
      | zero => intro w hw; simpa using hw
      | succ n ih =>
        intro w hw
        rw [pow_succ, map_mul, Module.End.mul_apply]
        exact ih _ (hxW w hw)
    rw [map_mul, Module.End.mul_apply, hFW f hf _ (hpow n w hw)]
    exact hpow n w hw
  have hW0 : W = ⊥ := S.aniso W hiso fun a ha w hw => hAW ⟨a, ha⟩ w hw
  exact hv0 ((Submodule.eq_bot_iff W).mp hW0 v (Submodule.subset_span (by simp)))

theorem card_blk_modEq [Finite K] (F : Subgroup A) :
    Nat.card (hyperFixed (spRep A) F) ≡ 1 [MOD p] := by
  have := S.fact
  have := S.finite
  set B := hyperFixed (spRep A) F with hB
  let _ : MulAction A B :=
    { smul := fun a v => ⟨spRep A a v, S.blk_stable F a v.2⟩
      one_smul := fun v => Subtype.ext (by
        change spRep A 1 v = v
        rw [map_one]
        rfl)
      mul_smul := fun a b v => Subtype.ext (by
        change spRep A (a * b) v = spRep A a (spRep A b v)
        rw [map_mul]
        rfl) }
  have hfix : MulAction.fixedPoints A B = {0} := by
    ext v
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hv
      apply Subtype.ext
      apply S.fixed_eq_zero
      rw [mem_hyperFixed]
      intro a _
      exact congrArg Subtype.val (hv a)
    · rintro rfl a
      apply Subtype.ext
      change spRep A a 0 = 0
      exact map_zero _
  have h := (IsPGroup.of_card S.card_eq).card_modEq_card_fixedPoints B
  rw [hfix] at h
  simpa using h

theorem card_inf {F₁ F₂ : Subgroup A} (hF₁ : F₁.index = p) (hF₂ : F₂.index = p)
    (hne : F₁ ≠ F₂) : Nat.card (F₁ ⊓ F₂ : Subgroup A) = p := by
  have := S.finite
  have hp := S.prime
  have hidx : (F₁ ⊓ F₂).index ≤ p * p :=
    (Subgroup.index_inf_le (H := F₁) (K := F₂)).trans (by rw [hF₁, hF₂])
  have hcm := (F₁ ⊓ F₂).card_mul_index
  rw [S.card_eq] at hcm
  have hdvd : Nat.card (F₁ ⊓ F₂ : Subgroup A) ∣ Nat.card F₁ :=
    Subgroup.card_dvd_of_le inf_le_left
  rw [S.card_hyperplane hF₁] at hdvd
  obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hk2 : k ≠ 2 := by
    rintro rfl
    have hle : F₁ ≤ F₂ := by
      have heq : F₁ ⊓ F₂ = F₁ := Subgroup.eq_of_le_of_card_ge inf_le_left
        (by rw [hkc, S.card_hyperplane hF₁])
      exact heq ▸ inf_le_right
    exact hne (Subgroup.eq_of_le_of_card_ge hle
      (by rw [S.card_hyperplane hF₁, S.card_hyperplane hF₂]))
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [hkc, pow_zero, one_mul] at hcm
    have : p ^ 3 ≤ p * p := hcm ▸ hidx
    have h1 := hp.one_lt
    nlinarith
  rw [hkc]
  interval_cases k <;> simp_all

theorem blk_inf_eq_bot {F₁ F₂ : Subgroup A} (hF₁ : F₁.index = p) (hF₂ : F₂.index = p)
    (hne : F₁ ≠ F₂) : hyperFixed (spRep A) F₁ ⊓ hyperFixed (spRep A) F₂ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro v ⟨hv₁, hv₂⟩
  apply S.fixed_eq_zero
  rw [mem_hyperFixed]
  have hstab : F₁ ⊔ F₂ ≤ HyperBlocks.stabVec (spRep A) v :=
    sup_le (fun g hg => mem_hyperFixed.1 hv₁ g hg) (fun g hg => mem_hyperFixed.1 hv₂ g hg)
  intro g _
  exact (S.sup_eq_top hF₁ hF₂ hne ▸ hstab) (Subgroup.mem_top g)

end SpAnisoSetup

end CFSG.LieType.SeitzGeneration
