module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.Core
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KGD


theorem commutator_eq_top_of_simple_of_not_comm_inner {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ∃ x y : G, x * y ≠ y * x) : commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with hb | ht
  · exfalso
    obtain ⟨x, y, hxy⟩ := h
    have hc : IsMulCommutative G := (commutator_eq_bot_iff G).1 hb
    exact hxy (hc.is_comm.comm x y)
  · exact ht

section Descent

variable {ℓ f : ℕ} {K L : Type} [Field K] [Field L] [Algebra K L] [IsAlgClosure K L]

theorem langDescent_triD4_inner (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (D : LangDatum Tag.D4 L) (hΦ : D.Φ = twistHom TwistTag.D4 L Fr) {p : ℕ} :
    LangDescent D p (triEmb K σ L) := by
  classical
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hK0
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hrange := triEmb_range (K := K) (σ := σ) (L := L) hℓ hf hK hσ Fr hFr
  have hfix : D.fix = (triEmb K σ L).range := by
    rw [hrange]
    ext x
    rw [LangDatum.mem_fix, hΦ]
    rfl
  obtain ⟨-, -, -, hsimple, hnc⟩ :=
    triality_both_field_orientations_simple_full_ambient_fixed_group ℓ f hℓ hf K hK L 1
      (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c) Fr hFr
  haveI := hsimple
  have hperf := commutator_eq_top_of_simple_of_not_comm_inner hnc
  have hperfI : ⁅(triEmb K σ L).range, (triEmb K σ L).range⁆ = (triEmb K σ L).range := by
    have h1 : (triEmb K σ L).range = Subgroup.map (triEmb K σ L) ⊤ := MonoidHom.range_eq_map _
    calc ⁅(triEmb K σ L).range, (triEmb K σ L).range⁆
        = ⁅Subgroup.map (triEmb K σ L) ⊤, Subgroup.map (triEmb K σ L) ⊤⁆ := by rw [← h1]
      _ = Subgroup.map (triEmb K σ L) ⁅(⊤ : Subgroup (graphFixedRootGroup TwistTag.D4 K
            σ.toRingHom)), (⊤ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ :=
          (Subgroup.map_commutator _ _ _).symm
      _ = Subgroup.map (triEmb K σ L) ⊤ := by rw [← commutator_def, hperf]
      _ = (triEmb K σ L).range := h1.symm
  refine ⟨?_, hfix.ge, fun P hP _ => hfix ▸ hP, ?_⟩
  · rw [hfix]
    exact Finite.of_surjective (triEmb K σ L).rangeRestrict (triEmb K σ L).rangeRestrict_surjective
  · rw [hfix]
    exact hperfI

end Descent

theorem exists_langSetup_of_inner_triD4_of_prime {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀ℓ : p₀ ≠ ℓ) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ ℓ ^ f)
    (hmon : MonomialToralAt Tag.D4 p)
    (x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hp1 : x ^ p = 1) (hx1 : x ≠ 1) :
    ∃ (S : LangSetup Tag.D4 (AlgebraicClosure K) p₀)
      (a : Fin Tag.D4.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* ModGL Tag.D4 (AlgebraicClosure K)),
      S.D.q = ℓ ^ f ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ (ℓ ^ f)) ∧
        S.D.Φ = twistHom TwistTag.D4 (AlgebraicClosure K) Fr) ∧
      rootDiagUnit Tag.D4 a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit Tag.D4 a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      ∀ c, ι (MulAut.conj x c) = rootDiagUnit Tag.D4 a * ι c * (rootDiagUnit Tag.D4 a)⁻¹ := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hK0
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  set L := AlgebraicClosure K with hLdef
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ (ℓ ^ f) := fun c =>
    iterateFrobenius_def ℓ f c
  have hcomm : (algebraMap K L).comp σ.toRingHom =
      (iterateFrobenius L ℓ f).comp (algebraMap K L) := by
    refine RingHom.ext fun c => ?_
    change algebraMap K L (σ c) = iterateFrobenius L ℓ f (algebraMap K L c)
    rw [hσ c, iterateFrobenius_def, map_pow]
  set u : ModGL TwistTag.D4.tag L := triEmb K σ L x with hu
  have huG : u ∈ adjointGroup TwistTag.D4.tag L := triEmb_mem_adjointGroup x
  have hufix : twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) u = u := triEmb_fixed _ hcomm x
  have hup : u ^ p = 1 := by rw [hu, ← map_pow, hp1, map_one]
  have hu1 : u ≠ 1 := fun h' => hx1 (triEmb_injective (by rw [map_one]; exact h'))
  have hconj := exists_conj_torusGroup_of_pow_eq_one hp hmon hpℓ.symm
    (isAlgebraic_zmod_algebraicClosure_of_finite K ℓ) huG hup
  obtain ⟨D, hΦ, hDq, hmem⟩ := exists_langDatum_of_toral_twisted TwistTag.D4 f hf hufix hconj
  have hd := langDescent_triD4_inner (K := K) (L := L) hℓ hf hK σ hσ hFr D hΦ (p := p)
  have hβ' : ∀ c, triEmb K σ L (MulAut.conj x c) = u * triEmb K σ L c * u⁻¹ := fun c => by
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hq' : 5 ≤ p₀ ∨ 4 ≤ D.q := by
    rw [hDq]
    exact hq₀
  obtain ⟨S, a, ι, rfl, hT, hap, h1, hinj, hrange, hconjι⟩ :=
    exists_langSetup_of_toral_datum_of_prime hℓ hf D hDq hp₀ hp₀ℓ hq' hd.finite_model
      (triEmb K σ L) triEmb_injective hd.Γ_eq (MulAut.conj x) hβ' hmem hup hu1
  exact ⟨S, a, ι, hDq, ⟨iterateFrobenius L ℓ f, hFr, hΦ⟩, hT, hap, h1, hinj, hrange, hconjι⟩

theorem exists_langSetup_of_inner_triD4 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hq : 5 ≤ p ∨ 4 ≤ ℓ ^ f) (hmon : MonomialToralAt Tag.D4 p)
    (x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hp1 : x ^ p = 1) (hx1 : x ≠ 1) :
    ∃ (S : LangSetup Tag.D4 (AlgebraicClosure K) p)
      (a : Fin Tag.D4.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* ModGL Tag.D4 (AlgebraicClosure K)),
      S.D.q = ℓ ^ f ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ (ℓ ^ f)) ∧
        S.D.Φ = twistHom TwistTag.D4 (AlgebraicClosure K) Fr) ∧
      rootDiagUnit Tag.D4 a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit Tag.D4 a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      ∀ c, ι (MulAut.conj x c) = rootDiagUnit Tag.D4 a * ι c * (rootDiagUnit Tag.D4 a)⁻¹ :=
  exists_langSetup_of_inner_triD4_of_prime hℓ hf hK σ hσ hp hpℓ hp hpℓ hq hmon x hp1 hx1

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
