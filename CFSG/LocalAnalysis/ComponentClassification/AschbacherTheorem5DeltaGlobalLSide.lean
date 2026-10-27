module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalTAbelian
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalTwo

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem centralizes_rightConjugate {i j : Fin r} {k t : G}
    (hkH : k ∈ Subgroup.normalizer (D : Set G))
    (hk : rightConjugate (aschbacherThm5Preimage D (Abar i)) k = aschbacherThm5Preimage D (Abar j))
    (ht : aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i)) t) :
    aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar j))
      (k⁻¹ * t * k) := by
  intro x hx
  rw [← hk, mem_rightConjugate_iff] at hx
  have h1 := ht _ hx
  have heq : (k⁻¹ * t * k)⁻¹ * x⁻¹ * (k⁻¹ * t * k) * x =
      k⁻¹ * (t⁻¹ * (k * x * k⁻¹)⁻¹ * t * (k * x * k⁻¹)) * k := by group
  rw [heq]
  have hkO := normalizer_le_normalizer_core D hkH
  have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkO) _).mp h1
  simpa [mul_assoc] using h2

theorem centralizes_of_mem_factorZStar (hC : Counterexample G D r Abar) {a : Fin r} (j : Fin r)
    {v : G} (hv : v ∈ factorZStar D Abar a) :
    aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar j)) v := by
  by_cases hja : j = a
  · subst hja
    exact ((mem_centralizing_iff _ v).mp hv.2).2
  · exact cross_factor_centralizes D Abar hC.hyp.hcomm j a hja v hv.1

theorem centralizes_commutator (hC : Counterexample G D r Abar) {a : Fin r} {x v : G}
    (hxH : x ∈ Subgroup.normalizer (D : Set G)) (hv : v ∈ factorZStar D Abar a) :
    aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar a))
      (x⁻¹ * v⁻¹ * x * v) := by
  obtain ⟨j, hj⟩ := exists_conj_eq hC hxH a
  have hj' : rightConjugate (aschbacherThm5Preimage D (Abar a)) x⁻¹ =
      aschbacherThm5Preimage D (Abar j) := by
    rw [← hj, rightConjugate, inv_inv]
  have hk : rightConjugate (aschbacherThm5Preimage D (Abar j)) x =
      aschbacherThm5Preimage D (Abar a) := by
    rw [← hj', rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
  have hvD : v ∈ D := preimage_le D _ hv.1
  have h1 := centralizes_rightConjugate hxH hk
    (centralizes_of_mem_factorZStar hC j ((factorZStar D Abar a).inv_mem hv))
  have hD1 : x⁻¹ * v⁻¹ * x ∈ D := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxH) v⁻¹).mp (D.inv_mem hvD)
    simpa [mul_assoc] using this
  have m1 : x⁻¹ * v⁻¹ * x ∈ centralizing D (Abar a) := (mem_centralizing_iff _ _).mpr ⟨hD1, h1⟩
  exact ((mem_centralizing_iff _ _).mp ((centralizing D (Abar a)).mul_mem m1 hv.2)).2

theorem comm_of_mem_inf (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    {P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hPL : P ≤ rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g)
    (hWP : d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ≤
      Subgroup.normalizer (P : Set G))
    (hVZ : AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) ≤ factorZStar D Abar a)
    {x : G} (hx : x ∈ P ⊓ Subgroup.normalizer (D : Set G)) {v : G}
    (hv : v ∈ AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) :
    x * v = v * x := by
  set W := d.S ⊓ Subgroup.normalizer
    (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) with hWdef
  have hvW : v ∈ W := AschbacherTheorem3.omegaOne_le W hv
  have hcP : x⁻¹ * v⁻¹ * x * v ∈ P := by
    have h1 : v⁻¹ * x * v ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hWP hvW)) x).mp hx.1
      simpa [mul_assoc] using this
    have : x⁻¹ * v⁻¹ * x * v = x⁻¹ * (v⁻¹ * x * v) := by group
    rw [this]
    exact P.mul_mem (P.inv_mem hx.1) h1
  have hc := centralizes_commutator hC hx.2 (hVZ hv)
  have hc1 : x⁻¹ * v⁻¹ * x * v = 1 := by
    by_contra hne
    exact not_centralizes_of_mem_conj hC a (datum_g_not_mem d) (twoElt_of_mem hP2 hcP) hne
      (hPL hcP) hc
  calc x * v = x * v * (x⁻¹ * v⁻¹ * x * v)⁻¹ := by rw [hc1, inv_one, mul_one]
    _ = v * x := by group

theorem inf_centralizer_eq (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    {P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hPL : P ≤ rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g)
    (hWP : d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ≤
      Subgroup.normalizer (P : Set G))
    (hVZ : AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) ≤ factorZStar D Abar a)
    {v : G} (hv : v ∈ AschbacherTheorem3.omegaOne (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) (hv1 : v ≠ 1) :
    P ⊓ Subgroup.centralizer {v} = P ⊓ Subgroup.normalizer (D : Set G) := by
  apply le_antisymm
  · refine inf_le_inf_left P ?_
    have hvA : v ∈ aschbacherThm5Preimage D (Abar a) :=
      d.sylowS.le (AschbacherTheorem3.omegaOne_le _ hv).1
    have h2 : ∃ k : ℕ, v ^ (2 ^ k) = 1 :=
      twoElt_of_mem d.sylowS.isPGroup (AschbacherTheorem3.omegaOne_le _ hv).1
    exact centralizer_le hC a h2 hv1 (centralizes_of_mem_factorZStar hC a (hVZ hv))
  · intro x hx
    refine ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact comm_of_mem_inf hC d hP2 hPL hWP hVZ hx hv

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
