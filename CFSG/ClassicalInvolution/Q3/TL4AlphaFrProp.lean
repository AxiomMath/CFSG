module

public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrTri
public import CFSG.ClassicalInvolution.Q3.TL4OddFrLinkP

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.AlphaFr

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)
open CFSG.ClassicalInvolution.Q3.TL4

section Conj

variable {G : Type} [Group G]

theorem alphaOf_conj_eq {z u g : G} (hgz : g * z * g⁻¹ = z)
    (hgN : g ∈ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G)) :
    alphaOf (Subgroup.closure ({g * u * g⁻¹, z} : Set G)) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have h1 : Subgroup.closure ({g * u * g⁻¹, z} : Set G) =
      conjSub g (Subgroup.closure ({u, z} : Set G)) := by
    rw [T7A.conjSub_closure_pair, hgz]
  rw [h1, alphaOf_conjSub]
  exact mem_normalizer_iff_conjSub_eq.mp hgN

theorem conj_eq_of_mem_centralizer {z g : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G)) :
    g * z * g⁻¹ = z := by
  rw [mul_inv_eq_iff_eq_mul]
  exact Subgroup.mem_centralizer_singleton_iff.mp hg

end Conj

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}

theorem alphaOf_eq_of_secImg_conj (hL : TightLargeHypR r n Y Rd Sd z) {A M : Subgroup Y}
    {a m : Y} (hA : A ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (ha : IsUniqueInvolution A a) (hm : IsUniqueInvolution M m)
    (hO : oddCoreOf (layerY (CoreAssembly.conjClass (tightCore Rd)) z) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({a, z} : Set Y)) : Set Y))
    {g : ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) z)}
    (hgN : (g : Y) ∈ Subgroup.normalizer (alphaOf (Subgroup.closure ({a, z} : Set Y)) : Set Y))
    (hg : conjSub (QuotientGroup.mk'
        (classicalInvolutionOddCore ↥(layerY (CoreAssembly.conjClass (tightCore Rd)) z)) g)
      (secImg (CoreAssembly.conjClass (tightCore Rd)) z A) =
        secImg (CoreAssembly.conjClass (tightCore Rd)) z M) :
    alphaOf (Subgroup.closure ({m, z} : Set Y)) =
      alphaOf (Subgroup.closure ({a, z} : Set Y)) := by
  have h := TightLargeHypR.typeRFam hL
  have hgz : (g : Y) ∈ Subgroup.centralizer ({z} : Set Y) := layerY_le_centralizer g.2
  have hXA := XMem.conj' h.hyp.conjInvariant (xMem_of_mem_omegaNbr_core hL hA) hgz
  rw [conjSub_secImg] at hg
  obtain ⟨ν, hν, hMν⟩ := exists_conj_of_secImg_eq h hXA (xMem_of_mem_omegaNbr_core hL hM) hg
  have hνz : (ν : Y) ∈ Subgroup.centralizer ({z} : Set Y) := layerY_le_centralizer ν.2
  have hcM : M = conjSub ((ν : Y) * g) A := by rw [hMν, conjSub_mul]
  have hm' : IsUniqueInvolution M (((ν : Y) * g) * a * ((ν : Y) * g)⁻¹) := by
    rw [hcM]
    exact ha.conj _
  have hcN : (ν : Y) * g ∈
      Subgroup.normalizer (alphaOf (Subgroup.closure ({a, z} : Set Y)) : Set Y) :=
    Subgroup.mul_mem _ (hO ⟨ν, hν, rfl⟩) hgN
  rw [hm.eq hm']
  exact alphaOf_conj_eq
    (conj_eq_of_mem_centralizer (Subgroup.mul_mem _ hνz hgz)) hcN

theorem alphaOf_eq_of_linkConn (hH : TightHyp51TriR r n) (hL : TightLargeHypR r n Y Rd Sd z)
    {A : Subgroup Y} {a : Y}
    (hA : A ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (ha : IsUniqueInvolution A a)
    (hO : oddCoreOf (layerY (CoreAssembly.conjClass (tightCore Rd)) z) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({a, z} : Set Y)) : Set Y))
    (hconn : DConnected (coreLinkFam Rd z)) :
    ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ u : Y,
      IsUniqueInvolution J u →
        alphaOf (Subgroup.closure ({u, z} : Set Y)) =
          alphaOf (Subgroup.closure ({a, z} : Set Y)) := by
  have h := TightLargeHypR.typeRFam hL
  have hΦ := (h.secFam (x := z)).hyp
  have key : ∀ b, Relation.ReflTransGen
      (fun Mb Nb => Nb ∈ coreLinkFam Rd z ∧ dAdj (coreLinkFam Rd z) Mb Nb)
      (secImg (CoreAssembly.conjClass (tightCore Rd)) z A) b →
      b ∈ coreLinkFam Rd z ∧
        ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
          secImg (CoreAssembly.conjClass (tightCore Rd)) z M = b → ∀ m : Y,
            IsUniqueInvolution M m →
              alphaOf (Subgroup.closure ({m, z} : Set Y)) =
                alphaOf (Subgroup.closure ({a, z} : Set Y)) := by
    intro b hb
    induction hb with
    | refl =>
      refine ⟨⟨A, hA, rfl⟩, fun M hM hMb m hm => ?_⟩
      refine alphaOf_eq_of_secImg_conj hL hA hM ha hm hO (g := 1) (Subgroup.one_mem _) ?_
      rw [map_one, conjSub_one, hMb]
    | @tail b c _ hbc ih =>
      obtain ⟨⟨M₁, hM₁, rfl⟩, hP⟩ := ih
      obtain ⟨hc, hadj⟩ := hbc
      refine ⟨hc, fun M hM hMc m hm => ?_⟩
      subst hMc
      have hnbr : secImg (CoreAssembly.conjClass (tightCore Rd)) z M ∈
          omegaNbr (secFam (CoreAssembly.conjClass (tightCore Rd)) z)
            (secImg (CoreAssembly.conjClass (tightCore Rd)) z M₁) := by
        rcases hadj with h1 | h2
        · exact omegaNbr_secFam_of_coreLinkFam hL h1
        · exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΦ
            (secImg_mem (xMem_of_mem_omegaNbr_core hL hM))
            (secImg_mem (xMem_of_mem_omegaNbr_core hL hM₁))
            (omegaNbr_secFam_of_coreLinkFam hL h2)
      obtain ⟨ν, hν, hMν⟩ := exists_conj_omegaNbr_of_secImg h
        (xMem_of_mem_omegaNbr_core hL hM₁) (xMem_of_mem_omegaNbr_core hL hM) hnbr
      have hνz : (ν : Y) ∈ Subgroup.centralizer ({z} : Set Y) := layerY_le_centralizer ν.2
      obtain ⟨m₁, hm₁⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hM₁.1
      have e1 := alphaOf_eq_of_link_edge hH hL (conjSub_mem_omegaNbr_core hL hM₁ hνz) hM hMν
        (hm₁.conj (ν : Y)) hm
      have e2 := hP M₁ hM₁ rfl m₁ hm₁
      have hνN : (ν : Y) ∈
          Subgroup.normalizer (alphaOf (Subgroup.closure ({m₁, z} : Set Y)) : Set Y) := by
        rw [e2]
        exact hO ⟨ν, hν, rfl⟩
      rw [e1, alphaOf_conj_eq (conj_eq_of_mem_centralizer hνz) hνN, e2]
  exact fun J hJ u hu =>
    (key _ (hconn _ ⟨A, hA, rfl⟩ _ ⟨J, hJ, rfl⟩)).2 J hJ rfl u hu

theorem alphaOf_eq_of_layerY_le (hL : TightLargeHypR r n Y Rd Sd z) {A J : Subgroup Y}
    {a u : Y} (hA : A ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (ha : IsUniqueInvolution A a)
    (hY : layerY (CoreAssembly.conjClass (tightCore Rd)) z ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({a, z} : Set Y)) : Set Y))
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hu : IsUniqueInvolution J u)
    (hconj : ∃ g, conjSub g (secImg (CoreAssembly.conjClass (tightCore Rd)) z A) =
      secImg (CoreAssembly.conjClass (tightCore Rd)) z J) :
    alphaOf (Subgroup.closure ({u, z} : Set Y)) =
      alphaOf (Subgroup.closure ({a, z} : Set Y)) := by
  obtain ⟨g, hg⟩ := hconj
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  exact alphaOf_eq_of_secImg_conj hL hA hJ ha hu ((oddCoreOf_le_self _).trans hY) (hY g'.2) hg

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4.AlphaFr
