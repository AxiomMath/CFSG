module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73C
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73A
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RZ
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73F

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.LieType.Universal.Spin
open CFSG.GH74.GLS.Bg.Thompson (IsSylowIn)

section Transport

variable {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')

theorem map_subgroupOf_equivMapOfInjective (J A : Subgroup G) :
    (J.subgroupOf A).map (A.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom =
      (J.map e.toMonoidHom).subgroupOf (A.map e.toMonoidHom) := by
  ext y
  rw [mem_map, mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨x', hx'A, hx'y⟩ := y.2
    have hxx' : x = x' := e.injective (hxy.trans hx'y.symm)
    exact ⟨⟨x, hxx' ▸ hx'A⟩, hx, Subtype.ext hxy⟩

theorem normal_subgroupOf_map_mulEquiv {J A : Subgroup G} (h : (J.subgroupOf A).Normal) :
    ((J.map e.toMonoidHom).subgroupOf (A.map e.toMonoidHom)).Normal := by
  rw [← map_subgroupOf_equivMapOfInjective]
  exact h.map _ (A.equivMapOfInjective e.toMonoidHom e.injective).surjective

theorem map_pPrimeCore_map_mulEquiv (J : Subgroup G) :
    (pPrimeCore 2 ↥(J.map e.toMonoidHom)).map (J.map e.toMonoidHom).subtype =
      ((pPrimeCore 2 ↥J).map J.subtype).map e.toMonoidHom := by
  rw [← pPrimeCore_map_iso 2 (J.equivMapOfInjective e.toMonoidHom e.injective),
    Subgroup.map_map, Subgroup.map_map]
  rfl

theorem isSolvableTwoComponentIn_map_mulEquiv {J A : Subgroup G}
    (h : IsSolvableTwoComponentIn J A) :
    IsSolvableTwoComponentIn (J.map e.toMonoidHom) (A.map e.toMonoidHom) := by
  obtain ⟨hJA, hsn, hO, hiso⟩ := h
  set φJ := J.equivMapOfInjective e.toMonoidHom e.injective with hφJ
  refine ⟨map_mono hJA, ?_, ?_, ?_⟩
  · rw [← map_subgroupOf_equivMapOfInjective]
    exact hsn.map (A.equivMapOfInjective e.toMonoidHom e.injective).surjective
  · rw [map_pPrimeCore_map_mulEquiv, map_pPrimeCore_map_mulEquiv, hO]
  · have ψ : ↥(J.map e.toMonoidHom) ⧸ pPrimeCore 2 ↥(J.map e.toMonoidHom) ≃*
        ↥J ⧸ pPrimeCore 2 ↥J :=
      QuotientGroup.congr _ _ φJ.symm (pPrimeCore_map_iso 2 φJ.symm)
    rcases hiso with h | h
    · obtain ⟨ε⟩ := h
      exact Or.inl ⟨ψ.trans ε⟩
    · obtain ⟨ε⟩ := h
      exact Or.inr ⟨ψ.trans ε⟩

theorem map_symm_map_mulEquiv (J : Subgroup G) :
    (J.map e.toMonoidHom).map e.symm.toMonoidHom = J := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id J
  ext x
  exact e.symm_apply_apply x

end Transport

section Model

variable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
include hK

theorem spinSeven_lemma410c_three :
    (∀ J : Subgroup (spinGroup (quadOdd 3 K)), ¬ IsTwoComponentIn J (centralizer {tSeven K})) ∧
    (∀ J : Subgroup (spinGroup (quadOdd 3 K)),
      IsSolvableTwoComponentIn J (centralizer {tSeven K}) →
        IsSLTwoOver 3 (↥J ⧸ pPrimeCore 2 ↥J) ∧
          (spinZ K ∈ J ∨ tSeven K ∈ J ∨ spinZ K * tSeven K ∈ J)) ∧
    (∀ J J' : Subgroup (spinGroup (quadOdd 3 K)),
      IsSolvableTwoComponentIn J (centralizer {tSeven K}) →
      IsSolvableTwoComponentIn J' (centralizer {tSeven K}) →
      ∀ e ∈ ({spinZ K, tSeven K, spinZ K * tSeven K} : Set (spinGroup (quadOdd 3 K))),
        e ∈ J → e ∈ J' → J = J') ∧
    (∀ e ∈ ({spinZ K, tSeven K, spinZ K * tSeven K} : Set (spinGroup (quadOdd 3 K))),
      ∃ J : Subgroup (spinGroup (quadOdd 3 K)),
        IsSolvableTwoComponentIn J (centralizer {tSeven K}) ∧
          (J.subgroupOf (centralizer {tSeven K})).Normal ∧ e ∈ J) := by
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK, pow_one]
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨hzz, hz1, hzc, htt, ht1, htc, hzJ₁, htJ₂, hztJ₃, -⟩ :=
    spinZ_facts Nat.prime_three hp2 hK'
  have hzt1 : spinZ K * tSeven K ≠ 1 := fun h => htc (by
    rw [(eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right hzz)]; exact hzc)
  obtain ⟨o1, o2, o3⟩ := pPrimeCore_spinJ_odd (K := K) Nat.prime_three hp2 hK'
  obtain ⟨s1, s2, s3⟩ := isSLTwoOver_spinJ (K := K) hK'
  have hinf := fun y : spinGroup (quadOdd 3 K) =>
    spinJ_inf_eq_one_odd (K := K) Nat.prime_three hp2 hK' (y := y)
  refine ⟨not_isTwoComponentIn_three hK, fun J hJ => ?_, fun J J' hJ hJ' e he heJ heJ' => ?_,
    fun e he => ?_⟩
  · rcases eq_spinJ_of_isSolvableTwoComponentIn_three hK hJ with rfl | rfl | rfl
    · exact ⟨isSLTwoOver_quotient_of_pPrimeCore_eq_bot o1 s1, Or.inl hzJ₁⟩
    · exact ⟨isSLTwoOver_quotient_of_pPrimeCore_eq_bot o2 s2, Or.inr (Or.inl htJ₂)⟩
    · exact ⟨isSLTwoOver_quotient_of_pPrimeCore_eq_bot o3 s3, Or.inr (Or.inr hztJ₃)⟩
  · have he1 : e ≠ 1 := by
      rcases he with rfl | rfl | rfl
      · exact hz1
      · exact ht1
      · exact hzt1
    rcases eq_spinJ_of_isSolvableTwoComponentIn_three hK hJ with rfl | rfl | rfl <;>
      rcases eq_spinJ_of_isSolvableTwoComponentIn_three hK hJ' with rfl | rfl | rfl
    · rfl
    · exact absurd ((hinf e).1 heJ heJ') he1
    · exact absurd ((hinf e).2.1 heJ heJ') he1
    · exact absurd ((hinf e).1 heJ' heJ) he1
    · rfl
    · exact absurd ((hinf e).2.2 heJ heJ') he1
    · exact absurd ((hinf e).2.1 heJ' heJ) he1
    · exact absurd ((hinf e).2.2 heJ' heJ) he1
    · rfl
  · rcases he with rfl | rfl | rfl
    · obtain ⟨h1, h2⟩ := isSolvableTwoComponentIn_spinJ_three hK (Or.inl rfl)
      exact ⟨_, h1, h2, hzJ₁⟩
    · obtain ⟨h1, h2⟩ := isSolvableTwoComponentIn_spinJ_three hK (Or.inr (Or.inl rfl))
      exact ⟨_, h1, h2, htJ₂⟩
    · obtain ⟨h1, h2⟩ := isSolvableTwoComponentIn_spinJ_three hK (Or.inr (Or.inr rfl))
      exact ⟨_, h1, h2, hztJ₃⟩

end Model

theorem lemma410a_three {X : Type} [Group X] [Finite X] {p f : ℕ} (h3 : p ^ f = 3)
    (hX : IsCoverOf .POmegaOdd 3 p f 2 X) {z : X} (hz : z ∈ center X) (hz1 : z ≠ 1)
    {S₀ : Subgroup X} (hS₀ : IsSylowIn 2 S₀ ⊤) {x : X} (hx : x ∈ S₀)
    (hxc : ∀ y ∈ S₀, x * y = y * x) : x = 1 ∨ x = z := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_spinSeven_three h3 hX
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK, pow_one]
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hez : e z = spinZ K := eq_spinZ_of_mem_center Nat.prime_three hp2 hK'
    ((mem_center_mulEquiv_iff e z).mpr hz) (fun h => hz1 (e.injective (h.trans (map_one e).symm)))
  have hS := isSylowIn_map_mulEquiv e hS₀
  rw [map_top_of_surjective e.toMonoidHom e.surjective] at hS
  rcases spinSeven_lemma410a_odd Nat.prime_three hp2 hK' hS (mem_map_of_mem e.toMonoidHom hx)
      (fun y hy => by
        obtain ⟨y', hy', rfl⟩ := hy
        show e x * e y' = e y' * e x
        rw [← map_mul, ← map_mul, hxc y' hy']) with h | h
  · left
    exact e.injective (h.trans (map_one e).symm)
  · right
    exact e.injective (h.trans hez.symm)

theorem lemma410f_three {X : Type} [Group X] [Finite X] {p f : ℕ} (h3 : p ^ f = 3)
    (hX : IsCoverOf .POmegaOdd 3 p f 2 X) {t : X} (ht : orderOf t = 2) (htZ : t ∉ center X)
    {T₀ : Subgroup X} (hT₀ : IsSylowIn 2 T₀ (centralizer {t})) :
    closure {x | x ∈ T₀ ∧ x * x = 1} = T₀ := by
  obtain ⟨K, _, _, e, hK, het⟩ := exists_mulEquiv_spinSeven_three h3 hX ht htZ
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK, pow_one]
  have hT := isSylowIn_map_mulEquiv e hT₀
  rw [map_centralizer_singleton_mulEquiv e t, het] at hT
  have h := closure_involutions_eq_of_isSylowIn_odd Nat.prime_three (by norm_num) hK' hT
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [MonoidHom.map_closure, ← h]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, mem_map]
  constructor
  · rintro ⟨x, ⟨hx, hxx⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rw [← map_mul, hxx, map_one]⟩
  · rintro ⟨⟨x, hx, rfl⟩, hyy⟩
    refine ⟨x, ⟨hx, e.injective ?_⟩, rfl⟩
    rw [map_mul, map_one]
    exact hyy

theorem lemma410c_three {X : Type} [Group X] [Finite X] {p f : ℕ} (h3 : p ^ f = 3)
    (hX : IsCoverOf .POmegaOdd 3 p f 2 X) {z : X} (hz : z ∈ center X) (hz1 : z ≠ 1) {t : X}
    (ht : orderOf t = 2) (htZ : t ∉ center X) :
    (∀ J : Subgroup X, ¬ IsTwoComponentIn J (centralizer {t})) ∧
    (∀ J : Subgroup X, IsSolvableTwoComponentIn J (centralizer {t}) →
      IsSLTwoOver (p ^ f) (↥J ⧸ pPrimeCore 2 ↥J) ∧ (z ∈ J ∨ t ∈ J ∨ z * t ∈ J)) ∧
    (∀ J J' : Subgroup X, IsSolvableTwoComponentIn J (centralizer {t}) →
      IsSolvableTwoComponentIn J' (centralizer {t}) → ∀ e ∈ ({z, t, z * t} : Set X),
        e ∈ J → e ∈ J' → J = J') ∧
    (∀ e ∈ ({z, t, z * t} : Set X), ∃ J : Subgroup X,
      IsSolvableTwoComponentIn J (centralizer {t}) ∧
        (J.subgroupOf (centralizer {t})).Normal ∧ e ∈ J) := by
  obtain ⟨K, _, _, φ, hK, hφt⟩ := exists_mulEquiv_spinSeven_three h3 hX ht htZ
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK, pow_one]
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hφz : φ z = spinZ K := eq_spinZ_of_mem_center Nat.prime_three hp2 hK'
    ((mem_center_mulEquiv_iff φ z).mpr hz) (fun h => hz1 (φ.injective (h.trans (map_one φ).symm)))
  obtain ⟨c0, c1, c2, c3⟩ := spinSeven_lemma410c_three hK
  have hC : (centralizer ({t} : Set X)).map φ.toMonoidHom = centralizer {tSeven K} := by
    rw [map_centralizer_singleton_mulEquiv φ t, hφt]
  have hCs : (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))).map φ.symm.toMonoidHom =
      centralizer {t} := by
    rw [← hC, map_symm_map_mulEquiv]
  have hmem : ∀ {J : Subgroup X} {x : X}, φ x ∈ J.map φ.toMonoidHom → x ∈ J := by
    intro J x hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← φ.injective hyx]
    exact hy
  have hset : ∀ x ∈ ({z, t, z * t} : Set X),
      φ x ∈ ({spinZ K, tSeven K, spinZ K * tSeven K} : Set (spinGroup (quadOdd 3 K))) := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inl hφz
    · exact Or.inr (Or.inl hφt)
    · exact Or.inr (Or.inr (by rw [map_mul, hφz, hφt]; exact Set.mem_singleton _))
  refine ⟨fun J hJ => ?_, fun J hJ => ?_, fun J J' hJ hJ' x hx hxJ hxJ' => ?_, fun x hx => ?_⟩
  · have h := L35.isTwoComponentIn_map_of_injective φ.toMonoidHom φ.injective hJ
    rw [hC] at h
    exact c0 _ h
  · have h := isSolvableTwoComponentIn_map_mulEquiv φ hJ
    rw [hC] at h
    obtain ⟨hsl, hzt⟩ := c1 _ h
    refine ⟨?_, ?_⟩
    · rw [h3]
      exact isSLTwoOver_quotient_of_mulEquiv (J.equivMapOfInjective φ.toMonoidHom φ.injective) hsl
    · rcases hzt with h1 | h1 | h1
      · exact Or.inl (hmem (hφz ▸ h1))
      · exact Or.inr (Or.inl (hmem (hφt ▸ h1)))
      · refine Or.inr (Or.inr (hmem ?_))
        rw [map_mul, hφz, hφt]
        exact h1
  · have h := isSolvableTwoComponentIn_map_mulEquiv φ hJ
    have h' := isSolvableTwoComponentIn_map_mulEquiv φ hJ'
    rw [hC] at h h'
    have heq := c2 _ _ h h' (φ x) (hset x hx) (mem_map_of_mem _ hxJ) (mem_map_of_mem _ hxJ')
    exact map_injective (f := φ.toMonoidHom) φ.injective heq
  · obtain ⟨J₀, hJ₀, hJ₀n, hxJ₀⟩ := c3 (φ x) (hset x hx)
    refine ⟨J₀.map φ.symm.toMonoidHom, ?_, ?_, ?_⟩
    · have h := isSolvableTwoComponentIn_map_mulEquiv φ.symm hJ₀
      rwa [hCs] at h
    · have h := normal_subgroupOf_map_mulEquiv φ.symm hJ₀n
      rwa [hCs] at h
    · refine ⟨φ x, hxJ₀, ?_⟩
      show φ.symm (φ x) = x
      exact φ.symm_apply_apply x

theorem harris82Lemma410RestThree_holds :
    ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p.Prime → p ^ f = 3 →
      IsCoverOf .POmegaOdd 3 p f 2 X → ∀ z ∈ center X, z ≠ 1 →
      (∀ S₀ : Subgroup X, IsSylowIn 2 S₀ ⊤ →
        ∀ x ∈ S₀, (∀ y ∈ S₀, x * y = y * x) → x = 1 ∨ x = z) ∧
      ∀ t : X, orderOf t = 2 → t ∉ center X →
        (∀ J : Subgroup X, ¬ IsTwoComponentIn J (centralizer {t})) ∧
        (∀ J : Subgroup X, IsSolvableTwoComponentIn J (centralizer {t}) →
          IsSLTwoOver (p ^ f) (↥J ⧸ pPrimeCore 2 ↥J) ∧ (z ∈ J ∨ t ∈ J ∨ z * t ∈ J)) ∧
        (∀ J J' : Subgroup X, IsSolvableTwoComponentIn J (centralizer {t}) →
          IsSolvableTwoComponentIn J' (centralizer {t}) → ∀ e ∈ ({z, t, z * t} : Set X),
            e ∈ J → e ∈ J' → J = J') ∧
        (∀ e ∈ ({z, t, z * t} : Set X), ∃ J : Subgroup X,
          IsSolvableTwoComponentIn J (centralizer {t}) ∧
            (J.subgroupOf (centralizer {t})).Normal ∧ e ∈ J) ∧
        ∀ T₀ : Subgroup X, IsSylowIn 2 T₀ (centralizer {t}) →
          closure {x | x ∈ T₀ ∧ x * x = 1} = T₀ := by
  intro X _ _ p f _ h3 hX z hz hz1
  refine ⟨fun S₀ hS₀ x hx hxc => lemma410a_three h3 hX hz hz1 hS₀ hx hxc, fun t ht htZ => ?_⟩
  obtain ⟨c0, c1, c2, c3⟩ := lemma410c_three h3 hX hz hz1 ht htZ
  exact ⟨c0, c1, c2, c3, fun T₀ hT₀ => lemma410f_three h3 hX ht htZ hT₀⟩

end CFSG.ComponentClassification.HarrisLit.T1
