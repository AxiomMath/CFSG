module

public import CFSG.ClassicalInvolution.Asc77.AscQuot613

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

@[expose] def L6_2On (Ω : Set (Subgroup G)) : Prop :=
  ∀ K ∈ Ω, ∀ z : G, IsUniqueInvolution K z →
    ∀ J ∈ Ω, J ∉ twinSet Ω K → ∀ t : G, IsUniqueInvolution J t →
      ∀ V : Subgroup G, IsSylow2In V (J ⊓ Subgroup.centralizer ({z} : Set G)) → t ∈ V →
        (V = Subgroup.zpowers t ∧ conjSub t K ≠ K) ∨
        (V = Subgroup.zpowers t ∧ V ≤ Subgroup.normalizer (K : Set G) ∧
          ∃ R ∈ RSet Ω, R ≤ K ∧ V ≤ Subgroup.normalizer (R : Set G) ∧
            IsSemidihedral (R ⊔ V)) ∨
        (V ∈ USet Ω ∧ V ≤ Subgroup.normalizer (K : Set G) ∧
          ∃ R ∈ RSet Ω, R ≤ K ∧ V ≤ Subgroup.normalizer (R : Set G) ∧
            IsWreathed (R ⊔ V)) ∨
        (V ∈ RSet Ω ∧ ⁅V, K⁆ ≤ oddCoreOf K)

@[expose] def L6_9On (Ω : Set (Subgroup G)) : Prop :=
  ∀ S : Sylow 2 G,
    (∃ η ∈ etaSet Ω (S : Subgroup G), ∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) ∧
    ∀ η ∈ etaSet Ω (S : Subgroup G), (∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) →
      (∀ x ∈ ⨆ U ∈ η, U, ∀ y ∈ ⨆ U ∈ η, U, x * y = y * x) ∧
        {U | U ∈ USet Ω ∧ U ≤ ⨆ V ∈ η, V} = η

@[expose] def L6_11On (Ω : Set (Subgroup G)) : Prop :=
  ∀ S : Sylow 2 G, ∀ η ∈ etaG Ω, (∀ V ∈ η, V ≤ (S : Subgroup G)) →
    ∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) → K ⊓ (⨆ V ∈ η, V) ∈ η

theorem l6_2On_of_l6_2 [Finite G] (h : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) : L6_2On Ω :=
  h hp hq G Ω hΩ

theorem l6_9On_of_l6_9 [Finite G] (h : L6_9 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) : L6_9On Ω :=
  h hp hq G Ω hΩ

theorem l6_11On_of_l6_11 [Finite G] (h : L6_11 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) : L6_11On Ω :=
  h hp hq G Ω hΩ

variable (p f) in
@[expose] def L6_14' : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      ∀ (X : Subgroup G) [X.Normal], oddCoreOf X = ⊥ → (∀ K ∈ Ω, Odd (Nat.card ↥(X ⊓ K))) →
        (∀ R ∈ RSet Ω, Commutes R X) ∧
          HypOmegaMod p f (Set.image (fun K : Subgroup G => K.map (QuotientGroup.mk' X)) Ω)

theorem oddCoreOf_normal_eq_inf [Finite G] (X : Subgroup G) [X.Normal] :
    oddCoreOf X = X ⊓ classicalInvolutionOddCore G :=
  CFSG.ComponentClassification.OddCore.normal_intersection G X

theorem oddCoreOf_eq_bot_of_normal [Finite G] (X : Subgroup G) [X.Normal]
    (hO : classicalInvolutionOddCore G = ⊥) : oddCoreOf X = ⊥ := by
  rw [oddCoreOf_normal_eq_inf, hO, inf_bot_eq]

theorem oddCoreOf_eq_bot_of_normal_of_top [Finite G] (X : Subgroup G) [X.Normal]
    (hO : oddCoreOf (⊤ : Subgroup G) = ⊥) : oddCoreOf X = ⊥ := by
  have h : oddCoreOf (⊤ : Subgroup G) = classicalInvolutionOddCore G := by
    rw [oddCoreOf_normal_eq_inf, top_inf_eq]
  exact oddCoreOf_eq_bot_of_normal X (h ▸ hO)

namespace AscQuot

theorem four_le_natCard_galoisField (hq : 5 ≤ p ^ f) :
    4 ≤ Nat.card (GaloisField p f) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  rw [GaloisField.card p f hf]
  omega

theorem le_of_forall_isSylow2In [Finite G] (_hp : p ≠ 2) (_hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {J M : Subgroup G} (hJ : J ∈ Ω)
    (hM : ∀ V : Subgroup G, IsSylow2In V J → V ≤ M) : J ≤ M :=
  hΩ.le_of_forall_isSylow2In hJ hM

theorem mem_of_uniqueInvolution [Finite G] {K A : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (hAK : A ≤ K) (hA : IsPGroup 2 A) (h2 : 2 ≤ Nat.card A) :
    z ∈ A := by
  have h2dvd : 2 ∣ Nat.card ↥A := by
    rcases hA.card_eq_or_dvd with h | h
    · omega
    · exact h
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have htG : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have htsq : (t : G) * (t : G) = 1 := by
    have := pow_orderOf_eq_one (t : G)
    rwa [htG, pow_two] at this
  have htne : (t : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htG
    omega
  rcases hz.unique (t : G) (hAK t.2) htsq with h | h
  · exact absurd h htne
  · exact h ▸ t.2

theorem inf_eq_bot_of_isPGroup_of_odd [Finite G] {J R : Subgroup G} (X : Subgroup G) [X.Normal]
    (hR : IsPGroup 2 R) (hRJ : R ≤ J) (hodd : Odd (Nat.card ↥(X ⊓ J))) : R ⊓ X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    hR.to_le (Subgroup.zpowers_le.mpr hx.1)
  have := eq_one_of_isPGroup_of_mem_odd hodd (show x ∈ X ⊓ J from ⟨hx.2, hRJ hx.1⟩) hx2
  rw [this]
  exact Subgroup.one_mem _

theorem conjSub_eq_of_normal (X : Subgroup G) [X.Normal] (y : G) : conjSub y X = X := by
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro h
    have := ‹X.Normal›.conj_mem _ h y
    simpa [mul_assoc] using this
  · intro h
    have := ‹X.Normal›.conj_mem _ h y⁻¹
    simpa [mul_assoc] using this

theorem commutes_of_mem_RSet [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) (h67 : L6_7On Ω)
    (X : Subgroup G) [X.Normal] (hO : oddCoreOf X = ⊥) (hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(X ⊓ K)))
    {R : Subgroup G} (hR : R ∈ RSet Ω) : Commutes R X := by
  obtain ⟨J, hJ, hRJ, hR2, -⟩ := mem_RSet_iff.mp hR
  have hRX : R ⊓ X = ⊥ := inf_eq_bot_of_isPGroup_of_odd X hR2 hRJ (hXK J hJ)
  have h := (l6_13_on hp hΩ h67 R hR ⊤ X le_top le_top (fun y _ => conjSub_eq_of_normal X y)
    hRX).2
  rw [hO] at h
  intro r hr x hx
  have h1 : ⁅r, x⁆ ∈ ⁅R, X⁆ := Subgroup.commutator_mem_commutator hr hx
  have h2 := h h1
  rw [Subgroup.mem_bot] at h2
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

theorem commutes_of_mem [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (X : Subgroup G) (hRX : ∀ R ∈ RSet Ω, Commutes R X) {K : Subgroup G} (hK : K ∈ Ω) :
    Commutes K X := by
  have hle : K ≤ Subgroup.centralizer (X : Set G) := by
    refine le_of_forall_isSylow2In hp hq hΩ hK fun V hV => ?_
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hRX V (mem_RSet_of_isSylow2In hK hV) r hr x hx).symm
  intro k hk x hx
  exact (Subgroup.mem_centralizer_iff.mp (hle hk) x hx).symm

@[expose] def quotRestrict (K X : Subgroup G) [X.Normal] :
    ↥K →* ↥(K.map (QuotientGroup.mk' X)) :=
  ((QuotientGroup.mk' X).comp K.subtype).codRestrict (K.map (QuotientGroup.mk' X))
    fun x => ⟨x, x.2, rfl⟩

theorem quotRestrict_apply (K X : Subgroup G) [X.Normal] (x : ↥K) :
    ((quotRestrict K X x : ↥(K.map (QuotientGroup.mk' X))) : G ⧸ X) =
      QuotientGroup.mk' X (x : G) :=
  rfl

theorem quotRestrict_injective {K X : Subgroup G} [X.Normal] (h : K ⊓ X = ⊥) :
    Function.Injective (quotRestrict K X) := by
  intro a b hab
  have h1 : QuotientGroup.mk' X (a : G) = QuotientGroup.mk' X (b : G) :=
    congrArg Subtype.val hab
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
  have h2 : (a : G)⁻¹ * b ∈ K ⊓ X := ⟨K.mul_mem (K.inv_mem a.2) b.2, h1⟩
  rw [h, Subgroup.mem_bot] at h2
  exact Subtype.ext (inv_mul_eq_one.mp h2)

theorem quotRestrict_surjective (K X : Subgroup G) [X.Normal] :
    Function.Surjective (quotRestrict K X) := by
  rintro ⟨_, k, hk, rfl⟩
  exact ⟨⟨k, hk⟩, rfl⟩

@[expose] noncomputable def quotRestrictEquiv {K X : Subgroup G} [X.Normal] (h : K ⊓ X = ⊥) :
    ↥K ≃* ↥(K.map (QuotientGroup.mk' X)) :=
  MulEquiv.ofBijective (quotRestrict K X) ⟨quotRestrict_injective h, quotRestrict_surjective K X⟩

theorem subgroupOf_le_oddCore_of_odd [Finite G] {K : Subgroup G} (X : Subgroup G) [X.Normal]
    (hodd : Odd (Nat.card ↥(X ⊓ K))) :
    X.subgroupOf K ≤ classicalInvolutionOddCore ↥K := by
  intro x hx
  have h := inf_le_oddCoreOf_of_odd X hodd (show (x : G) ∈ K ⊓ X from ⟨x.2, hx⟩)
  obtain ⟨hxK, h'⟩ := mem_oddCoreOf_iff.mp h
  exact h'

theorem map_quotRestrict_oddCore [Finite G] {K X : Subgroup G} [X.Normal]
    (hodd : Odd (Nat.card ↥(X ⊓ K))) :
    (classicalInvolutionOddCore ↥K).map (quotRestrict K X) =
      classicalInvolutionOddCore ↥(K.map (QuotientGroup.mk' X)) := by
  refine Subgroup.map_injective (f := (K.map (QuotientGroup.mk' X)).subtype)
    (Subgroup.subtype_injective _) ?_
  have h := oddCoreOf_map_mk_of_odd (K := K) (X := X) hodd
  unfold oddCoreOf at h
  rw [Subgroup.map_map] at h
  rw [Subgroup.map_map]
  exact h.symm

theorem nonempty_quotOddCoreEquiv [Finite G] {K X : Subgroup G} [X.Normal]
    (hodd : Odd (Nat.card ↥(X ⊓ K))) :
    Nonempty (↥K ⧸ classicalInvolutionOddCore ↥K ≃*
      ↥(K.map (QuotientGroup.mk' X)) ⧸
        classicalInvolutionOddCore ↥(K.map (QuotientGroup.mk' X))) := by
  have hmap := map_quotRestrict_oddCore hodd
  have hle : classicalInvolutionOddCore ↥K ≤
      (classicalInvolutionOddCore ↥(K.map (QuotientGroup.mk' X))).comap (quotRestrict K X) := by
    rw [← hmap]
    exact Subgroup.le_comap_map _ _
  let ψ := QuotientGroup.map (classicalInvolutionOddCore ↥K)
    (classicalInvolutionOddCore ↥(K.map (QuotientGroup.mk' X))) (quotRestrict K X) hle
  refine ⟨MulEquiv.ofBijective ψ ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_one]
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H a =>
      have h1 : quotRestrict K X a ∈
          classicalInvolutionOddCore ↥(K.map (QuotientGroup.mk' X)) := by
        have := hq
        simpa [ψ] using this
      rw [← hmap] at h1
      obtain ⟨n, hn, hna⟩ := h1
      have hker : n⁻¹ * a ∈ X.subgroupOf K := by
        rw [Subgroup.mem_subgroupOf]
        have h2 : QuotientGroup.mk' X (a : G) = QuotientGroup.mk' X (n : G) :=
          (congrArg Subtype.val hna).symm
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h2
        have := X.inv_mem h2
        simpa using this
      have h3 : n⁻¹ * a ∈ classicalInvolutionOddCore ↥K :=
        subgroupOf_le_oddCore_of_odd X hodd hker
      have h4 : a ∈ classicalInvolutionOddCore ↥K := by
        have := (classicalInvolutionOddCore ↥K).mul_mem hn h3
        simpa using this
      exact (QuotientGroup.eq_one_iff a).mpr h4
  · intro q
    induction q using QuotientGroup.induction_on with
    | H b =>
      obtain ⟨a, rfl⟩ := quotRestrict_surjective K X b
      exact ⟨QuotientGroup.mk a, rfl⟩

end AscQuot

end CFSG.ClassicalInvolution.Asc77
