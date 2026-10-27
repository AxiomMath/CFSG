module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FCover
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma82
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def c25Fix {Y : Type*} [Group Y] (S : Subgroup (MulAut Y)) : Subgroup Y where
  carrier := {y | ∀ α ∈ S, α y = y}
  mul_mem' := fun {a b} ha hb α hα => by rw [map_mul, ha α hα, hb α hα]
  one_mem' := fun α _ => map_one α
  inv_mem' := fun {a} ha α hα => by rw [map_inv, ha α hα]

theorem mem_c25Fix {Y : Type*} [Group Y] {S : Subgroup (MulAut Y)} {y : Y} :
    y ∈ c25Fix S ↔ ∀ α ∈ S, α y = y := Iff.rfl

variable {G : Type} [Group G]

@[expose] noncomputable def c25Rho {K B : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (K : Set G)) : ↥B →* MulAut (barOf 3 K) :=
  (barAut 3 K).comp (Subgroup.inclusion hBN)

@[expose] noncomputable def c25Img (K E : Subgroup G) : Subgroup (MulAut (barOf 3 K)) :=
  (E.subgroupOf (Subgroup.normalizer (K : Set G))).map (barAut 3 K)

theorem c25Rho_ker {K B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (K : Set G)) :
    (c25Rho hBN).ker = (dQ K).subgroupOf B := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact (LocalBalance.Lemma54Ns.mem_centralizerQuot_iff_barAut' 3 (J := K)
    (Subgroup.inclusion hBN b)).symm

theorem c25Rho_apply_mk {K B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (K : Set G)) (b : B)
    (x : ↥K) : c25Rho hBN b (QuotientGroup.mk x) =
      QuotientGroup.mk (K.normalizerMonoidHom (Subgroup.inclusion hBN b) x) :=
  barAut_mk 3 K _ x

theorem c25Rho_range {K B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (K : Set G)) :
    (c25Rho hBN).range = c25Img K B := by
  unfold c25Img c25Rho
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

variable [Finite G]

theorem c25_exists_centralized {K E : Subgroup G} (hEN : E ≤ Subgroup.normalizer (K : Set G))
    (hE : IsPGroup 3 ↥E) {y : barOf 3 K}
    (hy : ∀ (e : G) (he : e ∈ E), barAut 3 K ⟨e, hEN he⟩ y = y) :
    ∃ k : G, ∃ hk : k ∈ K, k ∈ Subgroup.centralizer (E : Set G) ∧
      (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : barOf 3 K) = y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective y
  have hUK := glaPPrimeCoreOf_le (p := 3) K
  have hnormU : ∀ a ∈ K, a ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) := fun a ha => by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact fun hn => conj_mem_glaPPrimeCoreOf ha hn
    · intro hn
      have := conj_mem_glaPPrimeCoreOf (K.inv_mem ha) hn
      simpa [mul_assoc] using this
  have hVp : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 K) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (coprime_card_glaPPrimeCoreOf K)
  have hUV : E ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) :=
    le_normalizer_glaPPrimeCoreOf_of_le_normalizer hEN
  obtain ⟨v, hv, hfix⟩ := exists_fixed_in_coset' (p := 3) (U := E) (V := GLAPPrimeCoreOf 3 K) hE
    hVp hUV (hnormU k₀ k₀.2) (fun e he => by
      have h1 := hy e he
      rw [barAut_mk, QuotientGroup.eq] at h1
      have h2 : e * (k₀ : G)⁻¹ * e⁻¹ * (k₀ : G) ∈ GLAPPrimeCoreOf 3 K := by
        refine ⟨_, h1, ?_⟩
        show ((e * (k₀ : G) * e⁻¹)⁻¹ * (k₀ : G)) = e * (k₀ : G)⁻¹ * e⁻¹ * (k₀ : G)
        group
      have h3 := (GLAPPrimeCoreOf 3 K).inv_mem h2
      have h4 := conj_mem_glaPPrimeCoreOf (A := K) (a := (k₀ : G)) k₀.2 h3
      simpa [mul_assoc] using h4)
  obtain ⟨hvK, hv'⟩ := mem_glaPPrimeCoreOf_iff.1 hv
  refine ⟨(k₀ : G) * v, K.mul_mem k₀.2 hvK, Subgroup.mem_centralizer_iff.2 fun e he => ?_, ?_⟩
  · exact mul_inv_eq_iff_eq_mul.1 (hfix e he)
  · show QuotientGroup.mk (k₀ * ⟨v, hvK⟩ : ↥K) = QuotientGroup.mk k₀
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (⟨v, hvK⟩ : ↥K)).2 hv']
    simp

theorem c25_barX_centralizer {K E : Subgroup G} (hEN : E ≤ Subgroup.normalizer (K : Set G))
    (hE : IsPGroup 3 ↥E) :
    barX 3 K (K ⊓ Subgroup.centralizer (E : Set G)) = c25Fix (c25Img K E) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨-, hxC⟩ := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)
    rintro _ ⟨γ, hγ, rfl⟩
    have hγE : ((γ : ↥(Subgroup.normalizer (K : Set G))) : G) ∈ E := Subgroup.mem_subgroupOf.1 hγ
    have hc := Subgroup.mem_centralizer_iff.1 hxC _ hγE
    show barAut 3 K γ (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) x) = _
    rw [QuotientGroup.mk'_apply, barAut_mk]
    congr 1
    apply Subtype.ext
    show (γ : G) * (x : G) * (γ : G)⁻¹ = (x : G)
    rw [hc]
    group
  · intro hy
    obtain ⟨k, hk, hkC, hkm⟩ := c25_exists_centralized hEN hE (fun e he =>
      hy _ ⟨⟨e, hEN he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩)
    exact ⟨⟨k, hk⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hk, hkC⟩), hkm⟩

end CFSG.HardMathSupport.Solomon.Coordinator
