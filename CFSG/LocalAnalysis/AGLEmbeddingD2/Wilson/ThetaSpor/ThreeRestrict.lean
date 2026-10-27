module

public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.RadicalBot
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.AschbacherCoreTransport
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThetaSpor

open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CFSG.RankThree.LocalRank
open scoped Pointwise

variable {N m : ℕ} {P : Subgroup (Equiv.Perm (Fin N))} {b : Equiv.Perm (Fin N)}
  {C : Subgroup (Equiv.Perm (Fin N))} {δ : Fin m → Fin N}

theorem dvd_card_of_orderOf_eq {M : Type*} [Group M] [Finite M] (H : Subgroup M) {g : M}
    (hg : g ∈ H) {k : ℕ} (hk : orderOf g = k) : k ∣ Nat.card H := by
  have h := orderOf_dvd_natCard (⟨g, hg⟩ : H)
  rwa [Subgroup.orderOf_mk, hk] at h

theorem thetaCore_eq_bot_of_restrict_three (hCle : C ≤ centralizerIn P b) (hbC : b ∈ C)
    (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1) (hδ : Function.Injective δ)
    (hstab : C ≤ MulAction.stabilizer (Equiv.Perm (Fin N)) (Set.range δ))
    (hbfix : ∀ k, b (δ k) = δ k) {X : Subgroup (Equiv.Perm (Fin m))}
    (hrange : (restrictHom hδ C hstab).range = X)
    (hrad : ∀ K : Subgroup X, K.Normal → Group.IsSolvable K → K = ⊥)
    (hcard : Nat.card (centralizerIn P b) = 3 * Nat.card X) :
    C = centralizerIn P b ∧ aschbacherSolvableCore 3 (centralizerIn P b) = ⊥ := by
  have hfin : Finite C := inferInstance
  have hkt : (⟨b, hbC⟩ : C) ∈ (restrictHom hδ C hstab).ker := by
    rw [MonoidHom.mem_ker]
    exact (restrictHom_eq_one_iff hδ hstab _).2 hbfix
  have hord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hker3 : 3 ≤ Nat.card (restrictHom hδ C hstab).ker := by
    have hord' : orderOf (⟨b, hbC⟩ : C) = 3 := by rw [Subgroup.orderOf_mk, hord]
    have hd := dvd_card_of_orderOf_eq (restrictHom hδ C hstab).ker hkt hord'
    exact Nat.le_of_dvd Nat.card_pos hd
  have hCcard : Nat.card C = Nat.card (restrictHom hδ C hstab).ker * Nat.card X := by
    rw [← hrange, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hle : Nat.card (centralizerIn P b) ≤ Nat.card C := by
    rw [hcard, hCcard]
    exact Nat.mul_le_mul_right _ hker3
  have hCeq : C = centralizerIn P b := Subgroup.eq_of_le_of_card_ge hCle hle
  have hXpos : 0 < Nat.card X := Nat.card_pos
  have hker : Nat.card (restrictHom hδ C hstab).ker = 3 := by
    have h1 : Nat.card C = 3 * Nat.card X := by rw [hCeq, hcard]
    rw [hCcard] at h1
    exact Nat.eq_of_mul_eq_mul_right hXpos h1
  have hpg : IsPGroup 3 (restrictHom hδ C hstab).ker :=
    IsPGroup.of_card (n := 1) (by rw [hker]; norm_num)
  have e := MulEquiv.subgroupCongr hrange
  have hrad' : ∀ K : Subgroup (restrictHom hδ C hstab).range, K.Normal → Group.IsSolvable K →
      K = ⊥ := by
    intro K hKn hKs
    have hKn' : (K.map e.toMonoidHom).Normal := Subgroup.Normal.map hKn _ e.surjective
    have hKs' : Group.IsSolvable (K.map e.toMonoidHom) :=
      Group.isSolvable_of_surjective (f := (e.subgroupMap K).toMonoidHom)
        (e.subgroupMap K).surjective
    have hb := hrad _ hKn' hKs'
    exact (Subgroup.map_eq_bot_iff_of_injective K e.injective).1 hb
  have hθC : aschbacherSolvableCore 3 C = ⊥ :=
    aschbacherSolvableCore_eq_bot_of_hom (restrictHom hδ C hstab) hpg hrad'
  refine ⟨hCeq, ?_⟩
  have hfin' : Finite C := hfin
  have hmap := CFSG.AGLEmbeddingD2.Wilson.Proving.aschbacherSolvableCore_map_mulEquiv
    Nat.prime_three (MulEquiv.subgroupCongr hCeq)
  rw [hmap, hθC, Subgroup.map_bot]

end CFSG.AGLEmbeddingD2.Wilson.ThetaSpor

end
