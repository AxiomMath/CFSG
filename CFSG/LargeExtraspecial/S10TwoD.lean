module

public import CFSG.LargeExtraspecial.S10One
public import CFSG.LargeExtraspecial.S10TwoA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem Abar_mul_eq_map (X : Hyp10 S g t) {k : S.M} (hk : S.ρ k ∈ Rbar S g t) :
    S.Lbar ((k : G) * g) ⊓ Nbar S g t =
      (S.Lbar g ⊓ Nbar S g t).map (MulAut.conj (S.ρ k)).toMonoidHom := by
  have hc := commute_of_mem_Rbar X.haQ hk
  have hNmap : (Nbar S g t).map (MulAut.conj (S.ρ k)).toMonoidHom = Nbar S g t := by
    refine le_antisymm ?_ fun x hx => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact conj_mem_Nbar X.haQ hc hx
    · refine ⟨(S.ρ k)⁻¹ * x * S.ρ k, ?_, by simp [mul_assoc]⟩
      have hc' : S.ρ k⁻¹ * t = t * S.ρ k⁻¹ := by
        rw [map_inv]
        exact commute_inv hc
      have := conj_mem_Nbar X.haQ hc' hx
      simpa [map_inv] using this
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj (S.ρ k)).injective, hNmap, ← Lbar_mul S k g]

theorem card_Abar_mul (X : Hyp10 S g t) {k : S.M} (hk : S.ρ k ∈ Rbar S g t) :
    Nat.card (S.Lbar ((k : G) * g) ⊓ Nbar S g t : Subgroup S.O) =
      Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := by
  rw [Abar_mul_eq_map X hk, Subgroup.card_map_of_injective (MulAut.conj (S.ρ k)).injective]

theorem Nbar_le_normalizer_Abar_mul (X : Hyp10 S g t) {k : S.M} (hk : S.ρ k ∈ Rbar S g t) :
    Nbar S g t ≤ normalizer (S.Lbar ((k : G) * g) ⊓ Nbar S g t : Subgroup S.O) := by
  have hDb := Lbar_mul_mem_Dset (mem_Lbar_mul_of_mem_Rbar X.H X.ht hk)
  intro x hx
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_of_mem_Nbar X.H hDb hx hy, fun hy => ?_⟩
  have := conj_mem_of_mem_Nbar X.H hDb (inv_mem hx) hy
  simpa [mul_assoc] using this

theorem two_mul_card_Nbar (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) :
    2 * Nat.card (Nbar S g t) =
      Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) *
        Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := by
  obtain ⟨k, hk, hβ, -⟩ := X.exists_pair
  obtain ⟨hR, hN, -⟩ := timmesfeld_4_7_b hCE X.H X.hNo X.C X.ht X.ht1 X.hVQ (Or.inr X.hΩ) hk hβ
  have hAn : (S.Lbar g ⊓ Nbar S g t) ≤
      normalizer (S.Lbar ((k : G) * g) ⊓ Nbar S g t : Subgroup S.O) :=
    inf_le_right.trans (Nbar_le_normalizer_Abar_mul X hk)
  have h1 := card_sup_mul_card_inf hAn
  rw [← hN] at h1
  have hinf : (S.Lbar g ⊓ Nbar S g t) ⊓ (S.Lbar ((k : G) * g) ⊓ Nbar S g t) = zpowers t := by
    refine le_antisymm ?_ ((zpowers_le).mpr ⟨X.t_mem_Abar, mem_Lbar_mul_of_mem_Rbar X.H X.ht hk,
      self_mem_Nbar X.H X.ht⟩)
    rw [← timmesfeld_4_7_c X.H X.C X.ht X.ht1 X.hVQ]
    intro x hx
    refine ⟨mem_centralizer_iff.mpr fun y hy => ?_, hx.1.1⟩
    rw [SetLike.mem_coe, hR] at hy
    have hle : S.Lbar g ⊔ S.Lbar ((k : G) * g) ≤ centralizer ({x} : Set S.O) := by
      refine sup_le (fun z hz => ?_) (fun z hz => ?_)
      · exact mem_centralizer_singleton_iff.mpr (S4.Lbar_comm S X.haQ hz hx.1.1)
      · exact mem_centralizer_singleton_iff.mpr
          (S4.Lbar_comm S (X.H.mul k).conj_mem hz hx.2.1)
    exact mem_centralizer_singleton_iff.mp (hle hy)
  rw [hinf, Nat.card_zpowers, X.orderOf_t, card_Abar_mul X hk] at h1
  linarith

theorem Nbar_eq_sup_of_inf (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {k : S.M}
    (hk : S.ρ k ∈ Rbar S g t)
    (hinf : (S.Lbar g ⊓ Nbar S g t) ⊓ S.Lbar ((k : G) * g) = zpowers t) :
    Nbar S g t = (S.Lbar g ⊓ Nbar S g t) ⊔ (S.Lbar ((k : G) * g) ⊓ Nbar S g t) := by
  have hAn : (S.Lbar g ⊓ Nbar S g t) ≤
      normalizer (S.Lbar ((k : G) * g) ⊓ Nbar S g t : Subgroup S.O) :=
    inf_le_right.trans (Nbar_le_normalizer_Abar_mul X hk)
  have h1 := card_sup_mul_card_inf hAn
  have hinf' : (S.Lbar g ⊓ Nbar S g t) ⊓ (S.Lbar ((k : G) * g) ⊓ Nbar S g t) = zpowers t := by
    rw [← hinf]
    ext x
    simp only [mem_inf]
    tauto
  rw [hinf', Nat.card_zpowers, X.orderOf_t, card_Abar_mul X hk] at h1
  have h2 := two_mul_card_Nbar hCE X
  have hle : (S.Lbar g ⊓ Nbar S g t) ⊔ (S.Lbar ((k : G) * g) ⊓ Nbar S g t) ≤ Nbar S g t :=
    sup_le inf_le_right inf_le_right
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  omega

theorem comm_of_mem_sup_of_mem_inf (X : Hyp10 S g t) {k : S.M} {y : S.O}
    (hy : y ∈ S.Lbar g ⊓ S.Lbar ((k : G) * g)) {n : S.O}
    (hn : n ∈ (S.Lbar g ⊓ Nbar S g t) ⊔ (S.Lbar ((k : G) * g) ⊓ Nbar S g t)) :
    n * y = y * n := by
  have hle : (S.Lbar g ⊓ Nbar S g t) ⊔ (S.Lbar ((k : G) * g) ⊓ Nbar S g t) ≤
      centralizer ({y} : Set S.O) := by
    refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · exact mem_centralizer_singleton_iff.mpr (S4.Lbar_comm S X.haQ hz.1 hy.1)
    · exact mem_centralizer_singleton_iff.mpr
        (S4.Lbar_comm S (X.H.mul k).conj_mem hz.1 hy.2)
  exact mem_centralizer_singleton_iff.mp (hle hn)

end CFSG.LargeExtraspecial.S10
