module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BFi24QR
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BFi24Aut
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BDefs
import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenHyp
import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenFour

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
open CFSG.Sporadic.Fi24 (R jR)

section Core

variable {X G : Type*} [Group X] [Group G] [Finite G]

private theorem isExtraspecial_of_fi24Local (e : X ≃* G) {Q J : Subgroup G} {a : G} {z : X}
    (hez : e z = a) (hQ : timmesfeldIsExtraspecial ↥Q)
    (hZ : (Subgroup.center ↥Q).map Q.subtype = Subgroup.zpowers a)
    (hF : ∀ F : Subgroup G, F ≤ J → F ≤ Subgroup.centralizer ({a} : Set G) →
      IsElemAbelian 3 F → Nat.card F = 243 →
      Q ⊓ Subgroup.centralizer (F : Set G) ≤ Subgroup.zpowers a ∧
        (∀ H : Subgroup G, H ≤ F → Nat.card H * 3 = Nat.card F →
          Nat.card ↥(Q ⊓ Subgroup.centralizer (H : Set G)) ≤ 2 ^ 3) ∧
        (∀ T : Subgroup G, IsPGroup 2 T → T ≤ Subgroup.centralizer ({a} : Set G) →
          F ≤ Subgroup.normalizer (T : Set G) → T ≤ Q) ∧
        F ≤ Subgroup.normalizer (Q : Set G))
    {A B R0 R1 : Subgroup X} (hBJ : ∀ x ∈ B, e x ∈ J) (hB : IsElemAbelian 3 B)
    (hBc : Nat.card B = 243) (hBA : B ≤ A) (hBz : ∀ x ∈ B, x * z = z * x) (hzR0 : z ∈ R0)
    (hR0z : ∀ r ∈ R0, r * z = z * r) (hR0 : IsPGroup 2 R0)
    (hAR0 : A ≤ Subgroup.normalizer (R0 : Set X)) (hR1 : IsPGroup 2 R1)
    (hAR1 : A ≤ Subgroup.normalizer (R1 : Set X)) (h01 : R0 < R1) :
    timmesfeldIsExtraspecial ↥R1 := by
  set f := e.toMonoidHom
  have hinj : Function.Injective f := e.injective
  have hcomm : ∀ x : X, x * z = z * x → f x ∈ Subgroup.centralizer ({a} : Set G) :=
    fun x hx => by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hez]
      exact (map_mul e x z).symm.trans ((congrArg e hx).trans (map_mul e z x))
  have hnorm : ∀ Y : Subgroup X, A ≤ Subgroup.normalizer (Y : Set X) →
      A.map f ≤ Subgroup.normalizer ((Y.map f : Subgroup G) : Set G) :=
    fun Y hY => (Subgroup.map_mono hY).trans (Subgroup.le_normalizer_map _)
  have hBJ' : B.map f ≤ J := by
    rintro _ ⟨x, hx, rfl⟩
    exact hBJ x hx
  have hBM : B.map f ≤ Subgroup.centralizer ({a} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcomm x (hBz x hx)
  have hR0M : R0.map f ≤ Subgroup.centralizer ({a} : Set G) := by
    rintro _ ⟨r, hr, rfl⟩
    exact hcomm r (hR0z r hr)
  have hB' := hB.map f
  obtain ⟨hCB, hH, hU, hBQ⟩ := hF _ hBJ' hBM hB' ((Subgroup.card_map_of_injective hinj).trans hBc)
  have hZa : Subgroup.centralizer
      (((Subgroup.center ↥Q).map Q.subtype : Subgroup G) : Set G) ≤
        Subgroup.centralizer ({a} : Set G) := by
    refine Subgroup.centralizer_le ?_
    rw [hZ, Set.singleton_subset_iff]
    exact Subgroup.mem_zpowers a
  have hU' : ∀ T : Subgroup G, IsPGroup 2 T → A.map f ≤ Subgroup.normalizer (T : Set G) →
      T ≤ Subgroup.centralizer (((Subgroup.center ↥Q).map Q.subtype : Subgroup G) : Set G) →
        T ≤ Q :=
    fun T hT hAT hTZ => hU T hT (hTZ.trans hZa) ((Subgroup.map_mono hBA).trans hAT)
  have hZR0 : (Subgroup.center ↥Q).map Q.subtype ≤ R0.map f := by
    rw [hZ, Subgroup.zpowers_le, ← hez]
    exact ⟨z, hzR0, rfl⟩
  have hCB' : Q ⊓ Subgroup.centralizer ((B.map f : Subgroup G) : Set G) ≤
      (Subgroup.center ↥Q).map Q.subtype := by
    rw [hZ]
    exact hCB
  have hM : ∀ T : Subgroup G, R0.map f ≤ T → T ≤ Q → A.map f ≤ Subgroup.normalizer (T : Set G) →
      ∀ s ∈ T, (∀ t ∈ T, s * t = t * s) → s ∈ (Subgroup.center ↥Q).map Q.subtype :=
    fun T hR0T hTQ hAT => radical_le_of_hyperplane_bound (p := 3) (k := 2) (by norm_num)
      (fun j hj0 hj2 => by interval_cases j <;> decide) hQ rfl hB' hBQ hCB' hH
      (hZR0.trans hR0T) hTQ ((Subgroup.map_mono hBA).trans hAT)
  have h := (isExtraspecial_of_nondeg_chain hQ rfl hZR0
    (hU _ (hR0.map f) hR0M ((Subgroup.map_mono hBA).trans (hnorm R0 hAR0))) (hnorm R0 hAR0) hU'
    hM (hR1.map f) (hnorm R1 hAR1) ((Subgroup.map_lt_map_iff_of_injective hinj).2 h01)).2
  exact CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_of_mulEquiv
    (MulEquiv.subgroupMap e R1).symm h

end Core

section Row


theorem rowFi24_holds : I301BRow .fi24 := by
  intro S _ _ hS B I K R0 R1 y hBi hBe hBc _ _ _ _ _ _ hR0 hR0c _ _ hKB hR1 hKB1 h01
  have hR0c' : Nat.card R0 = 2 ^ 9 := hR0c
  have hBe' : IsElemAbelian 3 B := hBe
  have hBc' : Nat.card B = 3 ^ 5 := hBc
  have hR0e : timmesfeldIsExtraspecial ↥R0 := hR0.resolve_right (by rw [hR0c']; norm_num)
  obtain ⟨c, hc1, -⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center ↥R0)).mp hR0e.2.2.2
  set z : MulAut S := ((c : ↥R0) : MulAut S) with hz
  have hzR0 : z ∈ R0 := (c : ↥R0).2
  have hzc : ∀ r ∈ R0, r * z = z * r := fun r hr =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 c.2 ⟨r, hr⟩)
  have hz1 : z ≠ 1 := fun h => hc1 (Subtype.ext (Subtype.ext h))
  have hBz : ∀ x ∈ B, x * z = z * x := fun x hx =>
    comm_of_mem_normalizer hR0e hzR0 hzc hz1 (hKB (le_sup_right (a := K) hx))
  obtain ⟨e, hez, hinn⟩ := exists_mulEquiv_fi24R hS hR0e (by rw [hR0c']; norm_num) hzR0 hzc
    hz1 hBi hBe' hBc' hBz (le_sup_right.trans hKB)
  obtain ⟨hQ, hZ, hloc⟩ := fi24QR_local
  have key := isExtraspecial_of_fi24Local (X := MulAut S) (G := ↥R) (Q := fi24QR) (J := jR.range)
    (a := zR) (z := z) (A := K ⊔ B) (B := B) (R0 := R0) (R1 := R1)
  exact key e hez hQ hZ hloc (fun x hx => hinn x (hBi hx)) hBe' (hBc'.trans (by norm_num))
    le_sup_right hBz hzR0 hzc hR0e.1 hKB hR1 hKB1 h01

end Row

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
