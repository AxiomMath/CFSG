module

public import CFSG.LieType.Ree.SmallReeSylowTorusSchreier
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSmallRee

open CFSG.LocalAnalysis.ComponentInitial CFSG.OrderReductions.FrattiniAutomorphisms
open CFSG.LieType.Ree
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Semilinear

variable {K : Type*} [Field K] [Finite K]

def semilinearFieldAut
    (f : Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K)))) : K ≃+* K :=
  Classical.choose (Classical.choose_spec ((mem_normalizer_scalarAddAut_iff f.1).1 f.2))

theorem exists_apply_eq_mul_semilinearFieldAut
    (f : Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K)))) :
    ∃ c : Kˣ, ∀ x, (f : Multiplicative (AddAut K)).toAdd x = c * semilinearFieldAut f x :=
  ⟨_, Classical.choose_spec (Classical.choose_spec ((mem_normalizer_scalarAddAut_iff f.1).1 f.2))⟩

theorem semilinearFieldAut_eq
    {f : Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K)))} {c : Kˣ}
    {σ : K ≃+* K} (h : ∀ x, (f : Multiplicative (AddAut K)).toAdd x = c * σ x) :
    semilinearFieldAut f = σ := by
  obtain ⟨c₀, h₀⟩ := exists_apply_eq_mul_semilinearFieldAut f
  have h1 : (c₀ : K) = c := by
    have := (h₀ 1).symm.trans (h 1)
    rwa [map_one, map_one, mul_one, mul_one] at this
  refine RingEquiv.ext fun x => ?_
  have := (h₀ x).symm.trans (h x)
  rw [h1] at this
  exact mul_left_cancel₀ c.ne_zero this

theorem semilinearFieldAut_eq_one_iff
    (f : Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K)))) :
    semilinearFieldAut f = 1 ↔ (f : Multiplicative (AddAut K)) ∈ scalarAddAut K := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := exists_apply_eq_mul_semilinearFieldAut f
    exact ⟨c, fun x => by rw [hc, h]; rfl⟩
  · rintro ⟨c, hc⟩
    exact semilinearFieldAut_eq (c := c) fun x => by rw [hc]; rfl

def semilinearFieldAutHom :
    Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K))) →* (K ≃+* K) where
  toFun := semilinearFieldAut
  map_one' := semilinearFieldAut_eq (c := 1) fun x => by
    rw [Units.val_one, one_mul]
    rfl
  map_mul' f g := by
    obtain ⟨c, hc⟩ := exists_apply_eq_mul_semilinearFieldAut f
    obtain ⟨d, hd⟩ := exists_apply_eq_mul_semilinearFieldAut g
    refine semilinearFieldAut_eq
      (c := c * Units.map (semilinearFieldAut f).toRingHom.toMonoidHom d) fun x => ?_
    change (f : Multiplicative (AddAut K)).toAdd ((g : Multiplicative (AddAut K)).toAdd x) = _
    rw [hd, hc, map_mul, Units.val_mul, Units.coe_map, RingAut.mul_apply, mul_assoc]
    rfl

end Semilinear

theorem Sylow_scalar_Frattini_outer_prime_support {G Ω : Type*} [Group G] [Finite G]
    [MulAction G Ω] [Finite Ω] [MulAction.IsPretransitive G Ω] [FaithfulSMul G Ω]
    (hΩ : 3 ≤ Nat.card Ω) (ξ : Ω) {p : ℕ} [Fact p.Prime] (U : Sylow p G)
    (hUξ : (U : Subgroup G) ≤ MulAction.stabilizer G ξ)
    (hUn : ((U : Subgroup G).subgroupOf (MulAction.stabilizer G ξ)).Normal)
    (htr : ∀ ω ω' : Ω, ω ≠ ξ → ω' ≠ ξ → ∃ u : (U : Subgroup G), (u : G) • ω = ω')
    (w : G) (hw : w • ξ ≠ ξ) {n : ℕ} (hn : 1 ≤ n) {K : Type*} [Field K]
    (hK : Nat.card K = p ^ n)
    (e : Additive ((U : Subgroup G) ⧸ frattini (U : Subgroup G)) ≃+ K)
    (hT : (((Subgroup.normalizer (((U : Subgroup G).map (MulAut.conj w).toMonoidHom :
        Subgroup G) : Set G)).subgroupOf (Subgroup.normalizer ((U : Subgroup G) : Set G))).map
          (U : Subgroup G).normalizerMonoidHom).map (frattiniScalarRep e) = scalarAddAut K) :
    (∃ (R : Subgroup (Outer G)) (_ : R.Normal), IsPGroup p R ∧ IsCyclic (Outer G ⧸ R) ∧
      Nat.card (Outer G ⧸ R) ∣ n) ∧
    ∃ b d : ℕ, 0 < d ∧ d ∣ n ∧ Nat.card (Outer G) = p ^ b * d := by
  have hp : p.Prime := Fact.out
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero n hp.ne_zero)
  set V := (U : Subgroup G).map (MulAut.conj w).toMonoidHom with hV
  set Th : Subgroup (MulAut (U : Subgroup G)) :=
    ((Subgroup.normalizer (V : Set G)).subgroupOf
      (Subgroup.normalizer ((U : Subgroup G) : Set G))).map
        (U : Subgroup G).normalizerMonoidHom with hTh
  obtain ⟨-, hinj, hprod, -⟩ := Suzuki_opposite_Sylow_restriction hΩ ξ U hUξ hUn htr w hw
  set A := pairAutSubgroup (U : Subgroup G) V with hA
  set r := pairAutRestrict (U : Subgroup G) V with hr
  set ρ := frattiniScalarRep e with hρ
  have hconj : ∀ (α : A) (t : Subgroup.normalizer ((U : Subgroup G) : Set G)),
      r α * (U : Subgroup G).normalizerMonoidHom t * (r α)⁻¹ =
        (U : Subgroup G).normalizerMonoidHom
          ⟨(α : MulAut G) t, apply_mem_normalizer_of_map_eq α.2.1 t.2⟩ := by
    intro α t
    refine MulEquiv.ext fun u => Subtype.ext ?_
    change (α : MulAut G) ((t : G) * (α : MulAut G).symm (u : G) * (t : G)⁻¹) =
      (α : MulAut G) t * u * ((α : MulAut G) t)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hmapTh : ∀ (α : A), ∀ φ ∈ Th, r α * φ * (r α)⁻¹ ∈ Th := by
    intro α φ hφ
    rw [hTh] at hφ ⊢
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hφ
    rw [hconj]
    refine Subgroup.mem_map.2 ⟨⟨(α : MulAut G) t, apply_mem_normalizer_of_map_eq α.2.1 t.2⟩,
      ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    exact apply_mem_normalizer_of_map_eq α.2.2 ht
  have hrN : ∀ α : A, r α ∈ Subgroup.normalizer (Th : Set (MulAut (U : Subgroup G))) := by
    intro α
    rw [Subgroup.mem_normalizer_iff]
    intro φ
    refine ⟨hmapTh α φ, fun h => ?_⟩
    have h2 := hmapTh α⁻¹ _ h
    rw [map_inv, inv_inv] at h2
    have h3 : (r α)⁻¹ * (r α * φ * (r α)⁻¹) * r α = φ := by group
    rwa [h3] at h2
  have hNS : ∀ α : A,
      ρ (r α) ∈ Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K))) := by
    intro α
    have hα := hrN α
    rw [Subgroup.mem_normalizer_iff] at hα ⊢
    intro y
    rw [← hT]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨r α * s * (r α)⁻¹, (hα s).1 hs, by rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨s, hs, hseq⟩
      refine ⟨(r α)⁻¹ * s * r α, ?_, ?_⟩
      · have h := (hα ((r α)⁻¹ * s * r α)).2
        rw [show r α * ((r α)⁻¹ * s * r α) * (r α)⁻¹ = s by group] at h
        exact h hs
      · rw [map_mul, map_mul, map_inv, hseq]
        group
  let ρA : A →* Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K))) :=
    (ρ.comp r).codRestrict _ hNS
  let ψ : A →* (K ≃+* K) := semilinearFieldAutHom.comp ρA
  have hψ : ∀ α : A, ψ α = 1 ↔ ρ (r α) ∈ scalarAddAut K := fun α =>
    semilinearFieldAut_eq_one_iff (ρA α)
  let φ : A →* Outer G := (QuotientGroup.mk' (inner G)).comp A.subtype
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner G) q
    obtain ⟨g, β, hβ, rfl⟩ := hprod α
    refine ⟨⟨β, hβ⟩, ?_⟩
    change ((β : MulAut G) : Outer G) = ((MulAut.conj g * β : MulAut G) : Outer G)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (N := inner G) (MulAut.conj g)).2 ⟨g, rfl⟩,
      one_mul]
  have hconjA : ∀ t : Subgroup.normalizer ((U : Subgroup G) : Set G),
      (t : G) ∈ Subgroup.normalizer (V : Set G) → MulAut.conj (t : G) ∈ A := fun t ht =>
    ⟨Subgroup.mem_normalizer_iff_map_conj_eq.1 t.2, Subgroup.mem_normalizer_iff_map_conj_eq.1 ht⟩
  have hker : φ.ker ≤ ψ.ker := by
    intro α hα
    have hαi : (α : MulAut G) ∈ inner G := (QuotientGroup.eq_one_iff (N := inner G) _).1 hα
    obtain ⟨g, hg⟩ := hαi
    have hgU : g ∈ Subgroup.normalizer ((U : Subgroup G) : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.2 (by rw [hg]; exact α.2.1)
    have hgV : g ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.2 (by rw [hg]; exact α.2.2)
    have hrα : r α ∈ Th := by
      refine ⟨⟨g, hgU⟩, Subgroup.mem_subgroupOf.2 hgV, MulEquiv.ext fun u => Subtype.ext ?_⟩
      change g * (u : G) * g⁻¹ = (α : MulAut G) u
      rw [← hg]
      rfl
    have hρα : ρ (r α) ∈ scalarAddAut K := by
      rw [← hT]
      exact ⟨r α, hrα, rfl⟩
    exact MonoidHom.mem_ker.2 ((hψ α).2 hρα)
  let χ : Outer G →* (K ≃+* K) := φ.liftOfSurjective hφ ⟨ψ, hker⟩
  have hχ : ∀ α : A, χ (φ α) = ψ α := fun α =>
    φ.liftOfRightInverse_comp_apply _ _ ⟨ψ, hker⟩ α
  have hQ : IsPGroup p (ρ.comp r).ker := by
    have hmem : ∀ β : (ρ.comp r).ker,
        r β ∈ (quotientAutomorphism (frattini (U : Subgroup G))).ker := fun β =>
      mem_ker_of_frattiniScalarRep_eq_one e (MonoidHom.mem_ker.1 β.2)
    let ι : (ρ.comp r).ker →* (quotientAutomorphism (frattini (U : Subgroup G))).ker :=
      (r.comp (ρ.comp r).ker.subtype).codRestrict _ hmem
    have hι : Function.Injective ι := fun x y h =>
      Subtype.ext (hinj (congrArg Subtype.val h))
    exact (CFSG.GroupTheory.frattini_automorphism_kernel U.isPGroup').2.of_injective ι hι
  have hle : χ.ker ≤ (ρ.comp r).ker.map φ := by
    intro x hx
    obtain ⟨α, rfl⟩ := hφ x
    have hψα : ψ α = 1 := by
      rw [← hχ α]
      exact hx
    have hρα := (hψ α).1 hψα
    rw [← hT] at hρα
    obtain ⟨τ, ⟨t, ht, rfl⟩, hτ⟩ := hρα
    have htV : (t : G) ∈ Subgroup.normalizer (V : Set G) := Subgroup.mem_subgroupOf.1 ht
    set γ : A := ⟨MulAut.conj (t : G), hconjA t htV⟩ with hγ
    have hrγ : r γ = (U : Subgroup G).normalizerMonoidHom t :=
      MulEquiv.ext fun u => Subtype.ext rfl
    have hφγ : φ γ = 1 := (QuotientGroup.eq_one_iff (N := inner G) _).2 ⟨t, rfl⟩
    refine ⟨α * γ⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.comp_apply,
        MonoidHom.comp_apply, hrγ, hτ, mul_inv_cancel]
    · rw [map_mul, map_inv, hφγ, inv_one, mul_one]
  have hR : IsPGroup p χ.ker := (hQ.map φ).to_le hle
  obtain ⟨σ, -, -, hσ, -, hsub⟩ := finite_field_automorphism_fixed_field_cardinality hp hn hK
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨σ, hσ⟩
  let E := QuotientGroup.quotientKerEquivRange χ
  have hcyc : IsCyclic (Outer G ⧸ χ.ker) := E.isCyclic.2 inferInstance
  have hdvd : Nat.card (Outer G ⧸ χ.ker) ∣ n := by
    rw [Nat.card_congr E.toEquiv]
    exact (hsub χ.range).1
  refine ⟨⟨χ.ker, inferInstance, hR, hcyc, hdvd⟩, ?_⟩
  obtain ⟨b, hb⟩ := hR.exists_card_eq
  refine ⟨b, Nat.card (Outer G ⧸ χ.ker), Nat.pos_of_dvd_of_pos hdvd hn, hdvd, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup χ.ker, hb, mul_comm]

end CFSG.ComponentClassification.CatalogueBSmallRee
