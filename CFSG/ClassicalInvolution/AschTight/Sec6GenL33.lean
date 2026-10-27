module

public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Aut

variable {Q : Type} [Group Q] [Finite Q]

theorem mulAut_eq_one_of_sq_eq_one {z : Q} (hz2 : orderOf z = 2)
    (hU : ∀ x : Q, orderOf x = 2 → x = z) (hO : classicalInvolutionOddCore Q = ⊥)
    (P : Sylow 2 Q) {γ : MulAut Q} (hγ : γ ^ 2 = 1) (hfix : ∀ x ∈ (P : Subgroup Q), γ x = x) :
    γ = 1 := by
  by_contra hγ1
  have : Finite (Q ⋊[MonoidHom.id (MulAut Q)] MulAut Q) :=
    Finite.of_equiv _ SemidirectProduct.equivProd.symm
  set ι : Q →* Q ⋊[MonoidHom.id (MulAut Q)] MulAut Q := SemidirectProduct.inl with hι
  have hιinj : Function.Injective ι := SemidirectProduct.inl_injective
  set t : Q ⋊[MonoidHom.id (MulAut Q)] MulAut Q := SemidirectProduct.inr γ with ht_def
  have ht2 : orderOf t = 2 := by
    rw [ht_def, orderOf_injective _ SemidirectProduct.inr_injective γ]
    exact orderOf_eq_prime hγ hγ1
  have hconj : ∀ x : Q, t * ι x * t⁻¹ = ι (γ x) := by
    intro x
    rw [show t⁻¹ = SemidirectProduct.inr γ⁻¹ from (map_inv _ γ).symm]
    exact (SemidirectProduct.inl_aut γ x).symm
  set K : Subgroup (Q ⋊[MonoidHom.id (MulAut Q)] MulAut Q) := ι.range with hK
  have hKn : K.Normal := by
    rw [hK, hι, SemidirectProduct.range_inl_eq_ker_rightHom]
    exact MonoidHom.normal_ker _
  have htN : t ∈ Subgroup.normalizer (K : Set (Q ⋊[MonoidHom.id (MulAut Q)] MulAut Q)) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top t
  have hzK : ι z ∈ K := ⟨z, rfl⟩
  have hz2' : orderOf (ι z) = 2 := by rw [orderOf_injective ι hιinj, hz2]
  have hUK : ∀ x ∈ K, orderOf x = 2 → x = ι z := by
    rintro _ ⟨y, rfl⟩ hy
    rw [orderOf_injective ι hιinj] at hy
    rw [hU y hy]
  have hR : IsSylow2Of ((P : Subgroup Q).map ι) K := by
    refine ⟨Subgroup.map_le_range ι _, P.isPGroup'.map ι, fun P' hP'K hP'2 hle => ?_⟩
    have hP''2 : IsPGroup 2 (P'.comap ι) := hP'2.comap_of_injective ι hιinj
    have hPle : (P : Subgroup Q) ≤ P'.comap ι := fun x hx => hle ⟨x, hx, rfl⟩
    have hPeq : P'.comap ι = (P : Subgroup Q) := P.is_maximal' hP''2 hPle
    rw [← hPeq, Subgroup.map_comap_eq_self hP'K]
  have htR : ∀ r ∈ (P : Subgroup Q).map ι, r * t = t * r := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hconj x
    rw [hfix x hx] at h1
    calc ι x * t = (t * ι x * t⁻¹) * t := by rw [h1]
      _ = t * ι x := by group
  have hOK : classicalInvolutionOddCore ↥K = ⊥ := by
    have e := CFSG.ComponentClassification.OddCore.equiv_invariant (MonoidHom.ofInjective hιinj)
    change componentClassificationOddCore ↥K = ⊥
    rw [← e]
    change (classicalInvolutionOddCore Q).map _ = ⊥
    rw [hO, Subgroup.map_bot]
  apply hγ1
  ext x
  have hx := commutator_mem_oddCore_of_centralizes_sylow hz2' hzK hUK ht2 htN hR htR
    (k := ι x) ⟨x, rfl⟩
  rw [hOK, Subgroup.map_bot, Subgroup.mem_bot] at hx
  have hcomm : ι x * t = t * ι x := by
    calc ι x * t = (ι x * t * (ι x)⁻¹ * t⁻¹) * (t * ι x) := by group
      _ = t * ι x := by rw [hx, one_mul]
  have h1 : t * ι x * t⁻¹ = ι x := by
    rw [← hcomm]
    group
  rw [hconj] at h1
  exact hιinj h1

omit [Finite Q] in
theorem mulAut_pow_apply_eq {β : MulAut Q} {x : Q} (hx : β x = x) (m : ℕ) : (β ^ m) x = x := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ, MulAut.mul_apply, hx, ih]

theorem mulAut_eq_one_of_pow_two_pow {z : Q} (hz2 : orderOf z = 2)
    (hU : ∀ x : Q, orderOf x = 2 → x = z) (hO : classicalInvolutionOddCore Q = ⊥)
    (P : Sylow 2 Q) {β : MulAut Q} {n : ℕ} (hβ : β ^ 2 ^ n = 1)
    (hfix : ∀ x ∈ (P : Subgroup Q), β x = x) : β = 1 := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hβ)
  rcases i with _ | i
  · rw [pow_zero] at hi
    exact orderOf_eq_one_iff.mp hi
  · exfalso
    have hγ2 : (β ^ 2 ^ i) ^ 2 = 1 := by
      rw [← pow_mul, ← pow_succ, ← hi, pow_orderOf_eq_one]
    have hγ1 := mulAut_eq_one_of_sq_eq_one hz2 hU hO P hγ2
      fun x hx => mulAut_pow_apply_eq (hfix x hx) _
    have hdvd := orderOf_dvd_of_pow_eq_one hγ1
    rw [hi] at hdvd
    have hlt : 2 ^ i < 2 ^ (i + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self i)
    exact absurd (Nat.le_of_dvd (by positivity) hdvd) (by omega)

end Aut

section Member

variable {G : Type} [Group G] [Finite G]

theorem quot_unique_involution {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z) :
    orderOf ((⟨z, hz.mem⟩ : ↥K) : ↥K ⧸ classicalInvolutionOddCore ↥K) = 2 ∧
      ∀ x : ↥K ⧸ classicalInvolutionOddCore ↥K, orderOf x = 2 →
        x = ((⟨z, hz.mem⟩ : ↥K) : ↥K ⧸ classicalInvolutionOddCore ↥K) := by
  have hzT : IsUniqueInvolution (⊤ : Subgroup ↥K) ⟨z, hz.mem⟩ :=
    ⟨Subgroup.mem_top _, fun h => hz.ne_one (congrArg Subtype.val h), Subtype.ext hz.sq,
      fun y _ hy => by
        rcases hz.unique (y : G) y.2 (congrArg Subtype.val hy) with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)⟩
  have hodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥K ⊓ ⊤)) := by
    rw [inf_top_eq]
    exact CFSG.ComponentClassification.OddCore.odd_card ↥K
  have h := isUniqueInvolution_map_mk_of_odd hodd hzT
  refine ⟨orderOf_eq_prime (by rw [pow_two]; exact h.sq) h.ne_one, fun x hx => ?_⟩
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have hxT : x ∈ (⊤ : Subgroup ↥K).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥K)) := by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥K) x
    exact ⟨y, Subgroup.mem_top y, rfl⟩
  exact (h.unique x hxT hxx).resolve_left hx1

theorem commutator_mem_oddCoreOf_of_centralizes {K R V : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (hR : IsSylow2In R K) (hV2 : IsPGroup 2 ↥V)
    (hVK : ∀ y ∈ V, conjSub y K = K) (hcomm : ∀ r ∈ R, ∀ v ∈ V, r * v = v * r) :
    ∀ k ∈ K, ∀ v ∈ V, ⁅v, k⁆ ∈ oddCoreOf K := by
  intro k hk v hv
  have hvK : K.map (MulAut.conj v).toMonoidHom = K := hVK v hv
  set α : ↥K ≃* ↥K := ((MulAut.conj v).subgroupMap K).trans (MulEquiv.subgroupCongr hvK)
    with hα
  have hαapp : ∀ x : ↥K, ((α x : ↥K) : G) = v * (x : G) * v⁻¹ := fun x => rfl
  have hαO : (classicalInvolutionOddCore ↥K).map (α : ↥K →* ↥K) = classicalInvolutionOddCore ↥K :=
    CFSG.ComponentClassification.OddCore.equiv_invariant α
  set β : MulAut (↥K ⧸ classicalInvolutionOddCore ↥K) :=
    QuotientGroup.congr (classicalInvolutionOddCore ↥K) (classicalInvolutionOddCore ↥K) α hαO
    with hβ
  have hβapp : ∀ x : ↥K, β (x : ↥K ⧸ classicalInvolutionOddCore ↥K) =
      ((α x : ↥K) : ↥K ⧸ classicalInvolutionOddCore ↥K) := fun x => rfl
  obtain ⟨hz2, hU⟩ := quot_unique_involution hz
  have hO : classicalInvolutionOddCore (↥K ⧸ classicalInvolutionOddCore ↥K) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥K
  set P : Sylow 2 (↥K ⧸ classicalInvolutionOddCore ↥K) :=
    (AscL62.sylowOfIsSylow2In'' hR).mapSurjective
      (QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥K)) with hP
  have hfix : ∀ x ∈ (P : Subgroup (↥K ⧸ classicalInvolutionOddCore ↥K)), β x = x := by
    intro x hx
    rw [hP, Sylow.coe_mapSurjective] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    have hrR : (r : G) ∈ R := hr
    change β (r : ↥K ⧸ classicalInvolutionOddCore ↥K) = (r : ↥K ⧸ classicalInvolutionOddCore ↥K)
    rw [hβapp]
    congr 1
    apply Subtype.ext
    rw [hαapp]
    calc v * (r : G) * v⁻¹ = ((r : G) * v) * v⁻¹ := by rw [hcomm r hrR v hv]
      _ = r := by group
  obtain ⟨n, hn⟩ : ∃ n : ℕ, orderOf v = 2 ^ n := AscL62.orderOf_eq_two_pow_of_isPGroup hV2 hv
  have hαpow : ∀ m : ℕ, ∀ x : ↥K, (((α ^ m) x : ↥K) : G) = v ^ m * (x : G) * (v ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih, hαapp, pow_succ]
      group
  have hβpow : ∀ m : ℕ, ∀ x : ↥K, (β ^ m) (x : ↥K ⧸ classicalInvolutionOddCore ↥K) =
      (((α ^ m) x : ↥K) : ↥K ⧸ classicalInvolutionOddCore ↥K) := by
    intro m
    induction m with
    | zero => intro x; rfl
    | succ m ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, hβapp, ih, pow_succ, MulAut.mul_apply]
  have hβ1 : β ^ 2 ^ n = 1 := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥K) x
    change (β ^ 2 ^ n) (y : ↥K ⧸ classicalInvolutionOddCore ↥K) = (y : ↥K ⧸ _)
    rw [hβpow]
    congr 1
    apply Subtype.ext
    rw [hαpow, ← hn, pow_orderOf_eq_one]
    group
  have hβeq : β = 1 := mulAut_eq_one_of_pow_two_pow hz2 hU hO P hβ1 hfix
  have hk1 : β ((⟨k, hk⟩ : ↥K) : ↥K ⧸ classicalInvolutionOddCore ↥K) =
      ((⟨k, hk⟩ : ↥K) : ↥K ⧸ classicalInvolutionOddCore ↥K) := by
    rw [hβeq]
    rfl
  rw [hβapp, QuotientGroup.eq] at hk1
  have hmem : α ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹ ∈ classicalInvolutionOddCore ↥K := by
    have h1 := (classicalInvolutionOddCore ↥K).inv_mem hk1
    have h2 := (classicalInvolutionOddCore_normal ↥K).conj_mem _ h1 ⟨k, hk⟩
    have e : (⟨k, hk⟩ : ↥K) * ((α ⟨k, hk⟩)⁻¹ * ⟨k, hk⟩)⁻¹ * (⟨k, hk⟩ : ↥K)⁻¹ =
        α ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹ := by group
    rwa [e] at h2
  refine ⟨α ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹, hmem, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hαapp,
    commutatorElement_def]

theorem centSylow {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) : AscL62.CentSylow Ω := by
  intro K R V hK hR hV2 hVK hcomm
  obtain ⟨z, hz⟩ := exists_uniqueInvolution hΩ hK
  exact commutator_mem_oddCoreOf_of_centralizes hz hR hV2 hVK hcomm

end Member

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
