module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentBlocks
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6

public section

namespace CFSG.AGLEmbedding.ToralCensus

open Module Polynomial CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SteinbergBR.EvenSp (planeHom tGL planeHom_mem_statedSp det_of_mem_zpowers
  planeHom_injective tGL_pow_three tGL_ne_one)

theorem card_eq_two_or_four_le (K : Type) [Field K] [Finite K] [CharP K 2] :
    Nat.card K = 2 ∨ 4 ≤ Nat.card K := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn]
  rcases Nat.lt_or_ge (n : ℕ) 2 with h | h
  · left
    rw [show (n : ℕ) = 1 by have := n.pos; omega, pow_one]
  · right
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) h

section Torus

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def spPlaneHom (s : ℕ) (K : Type) [Field K] [CharP K 2] :
    (Fin s → Subgroup.zpowers (tGL (K := K))) →* StatedSp s K :=
  (planeHom.comp (MonoidHom.compLeft (Subgroup.zpowers tGL).subtype (Fin s))).codRestrict
    (StatedSp s K) fun x => planeHom_mem_statedSp _ fun j => det_of_mem_zpowers (x j).2

theorem spPlaneHom_injective (s : ℕ) : Function.Injective (spPlaneHom s K) := by
  intro x y hxy
  have h := planeHom_injective (congrArg Subtype.val hxy)
  funext j
  exact Subtype.ext (congrFun h j)

@[expose] def tGen : Subgroup.zpowers (tGL (K := K)) := ⟨tGL, Subgroup.mem_zpowers _⟩

theorem tGen_pow_three : tGen (K := K) ^ 3 = 1 := Subtype.ext tGL_pow_three

theorem tGen_ne_one : tGen (K := K) ≠ 1 := fun h => tGL_ne_one (congrArg Subtype.val h)

theorem spPlane_first {s : ℕ} (hs : 1 ≤ s) :
    spPlaneHom s K (Pi.mulSingle ⟨0, by omega⟩ tGen) ^ 3 = 1 ∧
      spPlaneHom s K (Pi.mulSingle ⟨0, by omega⟩ tGen) ≠ 1 := by
  refine ⟨by rw [← map_pow, ← Pi.mulSingle_pow, tGen_pow_three, Pi.mulSingle_one, map_one],
    fun h => tGen_ne_one (K := K) ?_⟩
  have h1 := congrFun (spPlaneHom_injective (K := K) s (h.trans (map_one _).symm)) ⟨0, by omega⟩
  rwa [Pi.mulSingle_eq_same] at h1

theorem spPlane_pair {s : ℕ} (hs : 2 ≤ s) :
    let x := spPlaneHom s K (Pi.mulSingle ⟨0, by omega⟩ tGen)
    let y := spPlaneHom s K (Pi.mulSingle ⟨1, by omega⟩ tGen)
    Commute x y ∧ x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x ≠ 1 ∧ y ∉ Subgroup.zpowers x := by
  intro x y
  have h01 : (⟨0, by omega⟩ : Fin s) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  refine ⟨(Pi.mulSingle_commute h01 _ _).map _, (spPlane_first (by omega)).1,
    by rw [← map_pow, ← Pi.mulSingle_pow, tGen_pow_three, Pi.mulSingle_one, map_one],
    (spPlane_first (by omega)).2,
    map_not_mem_zpowers (spPlaneHom_injective s) (not_mem_zpowers_of_apply (j := ⟨1, by omega⟩)
      (Pi.mulSingle_eq_of_ne (Ne.symm h01) _)
      (by rw [Pi.mulSingle_eq_same]; exact tGen_ne_one (K := K)))⟩

end Torus

section Alternating

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type*} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {B : LinearMap.BilinForm K W}

omit [Finite K] [CharP K 2] in
theorem finite_sesqUnitaryGroup [Finite K] : Finite (sesqUnitaryGroup B) := by
  have := finite_generalLinearGroup (E := K) (W := W)
  infer_instance

theorem perfectNoncycThreeIn_sesqUnitary_alt (hB : B.IsAlt) (hn : B.Nondegenerate)
    (hd : 4 ≤ finrank K W) : PerfectNoncycThreeIn (⊤ : Subgroup (sesqUnitaryGroup B)) := by
  have := finite_sesqUnitaryGroup (B := B)
  obtain ⟨s, hs, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hB hn
  have hs2 : 2 ≤ s := by omega
  obtain ⟨hc, hx3, hy3, hx1, hyx⟩ := spPlane_pair (K := K) hs2
  set ψ := e.symm.toMonoidHom
  have hψ : Function.Injective ψ := e.symm.injective
  have hx3' : ψ (spPlaneHom s K (Pi.mulSingle ⟨0, by omega⟩ tGen)) ^ 3 = 1 := by
    rw [← map_pow, hx3, map_one]
  have hy3' : ψ (spPlaneHom s K (Pi.mulSingle ⟨1, by omega⟩ tGen)) ^ 3 = 1 := by
    rw [← map_pow, hy3, map_one]
  have hx1' : ψ (spPlaneHom s K (Pi.mulSingle ⟨0, by omega⟩ tGen)) ≠ 1 :=
    fun h => hx1 (hψ (h.trans (map_one ψ).symm))
  rcases card_eq_two_or_four_le K with hK2 | hK4
  · rcases (show s = 2 ∨ 3 ≤ s by omega) with rfl | hs3
    · obtain ⟨e4⟩ := CFSG.RankThree.PartOne.nonempty_mulEquiv_sympFour hK2 hB hn (by omega)
      obtain ⟨hq, hodd⟩ := CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour e4
      exact PerfectNoncycThreeIn.of_pair le_top (Subgroup.isPerfect_iff.mp hq.1)
        (hodd Nat.prime_three (by norm_num) _ hx3') (hodd Nat.prime_three (by norm_num) _ hy3')
        (hc.map ψ) hx3' hy3' hx1' (map_not_mem_zpowers hψ hyx)
    · have : Group.IsPerfect (StatedSp s K) :=
        CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp s K (Or.inr (Or.inr ⟨hK2, hs3⟩))
      have : Group.IsPerfect (sesqUnitaryGroup B) :=
        Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
      exact PerfectNoncycThreeIn.of_pair le_rfl Group.IsPerfect.commutator_eq_top
        (Subgroup.mem_top _) (Subgroup.mem_top _) (hc.map ψ) hx3' hy3' hx1'
        (map_not_mem_zpowers hψ hyx)
  · have : Fintype K := Fintype.ofFinite K
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hK4)
    have : Group.IsPerfect (StatedSp s K) :=
      CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp s K (Or.inl ⟨t, ht⟩)
    have : Group.IsPerfect (sesqUnitaryGroup B) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact PerfectNoncycThreeIn.of_pair le_rfl Group.IsPerfect.commutator_eq_top
      (Subgroup.mem_top _) (Subgroup.mem_top _) (hc.map ψ) hx3' hy3' hx1'
      (map_not_mem_zpowers hψ hyx)

theorem perfectThreeIn_sesqUnitary_alt (hB : B.IsAlt) (hn : B.Nondegenerate)
    (hd : 2 ≤ finrank K W) (hK4 : 4 ≤ Nat.card K) :
    PerfectThreeIn (⊤ : Subgroup (sesqUnitaryGroup B)) := by
  obtain ⟨s, hs, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hB hn
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hK4)
  have : Group.IsPerfect (StatedSp s K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp s K (Or.inl ⟨t, ht⟩)
  have : Group.IsPerfect (sesqUnitaryGroup B) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨hx3, hx1⟩ := spPlane_first (K := K) (s := s) (by omega)
  exact ⟨⊤, le_rfl, Group.IsPerfect.commutator_eq_top, _, Subgroup.mem_top _,
    by rw [← map_pow, hx3, map_one], fun h => hx1 (e.symm.injective (h.trans (map_one _).symm))⟩

end Alternating

section Divisors

variable {K : Type*} [Field K]

theorem dvd_X_sq_add_X_add_one {h : K[X]} (hirr : Irreducible h) (hmon : h.Monic)
    (hdvd : h ∣ X ^ 3 - C 1) (hX : h ≠ X - 1) : h ∣ X ^ 2 + X + 1 := by
  have h1 : h ∣ (X - C 1) * (X ^ 2 + X + 1) := by
    convert hdvd using 1
    simp only [map_one]
    ring
  rcases hirr.prime.dvd_or_dvd h1 with h2 | h2
  · exact absurd ((eq_of_monic_of_associated hmon (monic_X_sub_C 1)
      (hirr.associated_of_dvd (irreducible_X_sub_C 1) h2)).trans (by rw [map_one])) hX
  · exact h2

theorem natDegree_X_sq_add_X_add_one : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by
  compute_degree!

theorem monic_X_sq_add_X_add_one : (X ^ 2 + X + 1 : K[X]).Monic := by monicity!

theorem X_sq_add_X_add_one_ne_zero : (X ^ 2 + X + 1 : K[X]) ≠ 0 :=
  monic_X_sq_add_X_add_one.ne_zero

theorem eq_of_dvd_of_natDegree_eq_two {h₀ h : K[X]} (hirr₀ : Irreducible h₀) (hmon₀ : h₀.Monic)
    (hdvd₀ : h₀ ∣ X ^ 2 + X + 1) (hdeg : h₀.natDegree = 2) (hirr : Irreducible h)
    (hmon : h.Monic) (hdvd : h ∣ X ^ 2 + X + 1) : h = h₀ := by
  have heq : X ^ 2 + X + 1 = h₀ := eq_of_monic_of_dvd_of_natDegree_le hmon₀
    monic_X_sq_add_X_add_one hdvd₀ (by rw [natDegree_X_sq_add_X_add_one, hdeg])
  rw [heq] at hdvd
  exact eq_of_monic_of_associated hmon hmon₀ (hirr.associated_of_dvd hirr₀ hdvd)

theorem isCoprime_of_ne {h h' : K[X]} (hirr : Irreducible h) (hmon : h.Monic)
    (hirr' : Irreducible h') (hmon' : h'.Monic) (hne : h ≠ h') : IsCoprime h h' := by
  rw [hirr.coprime_iff_not_dvd]
  exact fun hd => hne (eq_of_monic_of_associated hmon hmon' (hirr.associated_of_dvd hirr' hd))

theorem natDegree_eq_one_of_pair {h h' : K[X]} (hirr : Irreducible h) (hmon : h.Monic)
    (hdvd : h ∣ X ^ 2 + X + 1) (hirr' : Irreducible h') (hmon' : h'.Monic)
    (hdvd' : h' ∣ X ^ 2 + X + 1) (hne : h ≠ h') (hdeg : h.natDegree = h'.natDegree) :
    h.natDegree = 1 ∧ h * h' = X ^ 2 + X + 1 := by
  have hmul := (isCoprime_of_ne hirr hmon hirr' hmon' hne).mul_dvd hdvd hdvd'
  have hle := natDegree_le_of_dvd hmul X_sq_add_X_add_one_ne_zero
  rw [natDegree_mul hmon.ne_zero hmon'.ne_zero, natDegree_X_sq_add_X_add_one] at hle
  have hpos := hirr.natDegree_pos
  have h1 : h.natDegree = 1 := by omega
  refine ⟨h1, (eq_of_monic_of_dvd_of_natDegree_le (hmon.mul hmon') monic_X_sq_add_X_add_one hmul
    ?_).symm⟩
  rw [natDegree_mul hmon.ne_zero hmon'.ne_zero, natDegree_X_sq_add_X_add_one]
  omega

theorem eq_or_eq_of_pair {h h' g : K[X]} (hmon : h.Monic) (hirr : Irreducible h)
    (hmon' : h'.Monic) (hirr' : Irreducible h') (hprod : h * h' = X ^ 2 + X + 1)
    (hirrg : Irreducible g) (hmong : g.Monic) (hdvd : g ∣ X ^ 2 + X + 1) : g = h ∨ g = h' := by
  rw [← hprod] at hdvd
  rcases hirrg.prime.dvd_or_dvd hdvd with h2 | h2
  · exact Or.inl (eq_of_monic_of_associated hmong hmon (hirrg.associated_of_dvd hirr h2))
  · exact Or.inr (eq_of_monic_of_associated hmong hmon' (hirrg.associated_of_dvd hirr' h2))

end Divisors

end CFSG.AGLEmbedding.ToralCensus
