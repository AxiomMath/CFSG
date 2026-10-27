module

public import CFSG.LargeExtraspecial.S14C10Apply
public import CFSG.LargeExtraspecial.S14NQNine

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial.S4
open scoped MatrixGroups

@[expose] def PSLPSU10Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (Nonempty (X ≃* PSL(10, ZMod 2)) ∨ Nonempty (X ≃* timmesfeldPSU 10)) →
    ∀ t : X, orderOf t = 2 →
      timmesfeldIsExtraspecial (timmesfeldFStar (centralizer ({t} : Set X))) →
      Nat.card (timmesfeldFStar (centralizer ({t} : Set X))) = 2 ^ 17 →
      ∀ K : Subgroup (centralizer ({t} : Set X)), K.Normal → ⁅K, K⁆ = K →
        timmesfeldFStar (centralizer ({t} : Set X)) ≤ K → 2 ^ 45 ∣ Nat.card K

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem mem_isometryGroup_polar {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {e : V ≃ₗ[ZMod 2] V}
    (he : e ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    e ∈ TauCeti.BilinForm.isometryGroup Q.polarBilin := by
  rw [TauCeti.BilinForm.mem_isometryGroup_iff]
  intro x y
  have h := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp he
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, h]

theorem RmodN_le_isometryGroup {H : Hyp4 S g} {C : Cons311 S g} {t : S.O}
    {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1} {hVQ : ¬ V S g t ≤ S.Qa g}
    (hcase : OmegaCase H C ht ht1 hVQ ∨ SpCase H C ht ht1 hVQ) :
    RmodN S g t ≤ TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ) := by
  rcases hcase with hΩ | hSp
  · obtain ⟨Q, hQ, hβ, hR, -⟩ := hΩ.exists_form
    rw [hR, ← hβ]
    exact fun e he => mem_isometryGroup_polar
      (CFSG.RankThree.OrthogonalInvolutions.omegaGroup_le Q hQ he)
  · rw [hSp.eq_sp]

theorem not_two_pow_dvd_card_RmodN {H : Hyp4 S g} {C : Cons311 S g} {t : S.O}
    {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1} {hVQ : ¬ V S g t ≤ S.Qa g}
    (hcase : OmegaCase H C ht ht1 hVQ ∨ SpCase H C ht ht1 hVQ)
    (hd : finrank (ZMod 2) (Vt S g t) = 8 ∨ finrank (ZMod 2) (Vt S g t) = 10) :
    ¬ 2 ^ 28 ∣ Nat.card (RmodN S g t) := by
  intro hdvd
  have h1 := Subgroup.card_dvd_of_le (RmodN_le_isometryGroup hcase)
  have hcard := fun m (hm : finrank (ZMod 2) (Vt S g t) = 2 * m) =>
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_isometryGroup m
      (beta H C ht ht1 hVQ) (beta_isAlt H C ht ht1 hVQ) (beta_nondegenerate H C ht ht1 hVQ) hm
  rcases hd with hd | hd
  · rw [hcard 4 (by rw [hd]), Nat.card_zmod] at h1
    exact absurd (hdvd.trans h1) (by decide)
  · rw [hcard 5 (by rw [hd]), Nat.card_zmod] at h1
    exact absurd (hdvd.trans h1) (by decide)

theorem card_Rbar_eq (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O) :
    Nat.card (Rbar S g t) = Nat.card (Nbar S g t) * Nat.card (RmodN S g t) := by
  have hker : (resV haQ t).ker = (Nbar S g t).subgroupOf (Rbar S g t) := by
    ext x
    rw [MonoidHom.mem_ker, resV_eq_one_iff, mem_subgroupOf]
  have h1 := Subgroup.card_mul_index (resV haQ t).ker
  rw [Subgroup.index_ker, range_resV, hker] at h1
  rw [← h1, Nat.card_congr (subgroupOfEquivOfLe Nbar_le_Rbar).toEquiv]

theorem false_of_alt2 (h2 : PSLPSU10Input) {t0 : Mbar0 S} {H : Hyp4 S g} {C : Cons311 S g}
    {ht : ((t0 : S.Mbar) : S.O) ∈ S.Lbar g} {ht1 : ((t0 : S.Mbar) : S.O) ≠ 1}
    {hVQ : ¬ V S g ((t0 : S.Mbar) : S.O) ≤ S.Qa g}
    (hcase : OmegaCase H C ht ht1 hVQ ∨ SpCase H C ht ht1 hVQ)
    (hd : finrank (ZMod 2) (Vt S g ((t0 : S.Mbar) : S.O)) = 8 ∨
      finrank (ZMod 2) (Vt S g ((t0 : S.Mbar) : S.O)) = 10)
    (hcardN : Nat.card (Nbar S g ((t0 : S.Mbar) : S.O)) = 2 ^ 17)
    (hperf : ⁅Rbar S g ((t0 : S.Mbar) : S.O), Rbar S g ((t0 : S.Mbar) : S.O)⁆ =
      Rbar S g ((t0 : S.Mbar) : S.O))
    (hR0 : Rbar S g ((t0 : S.Mbar) : S.O) ≤ Ct0 (Mbar0 S) ((t0 : S.Mbar) : S.O))
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set (Mbar0 S)))).map (inclC (Mbar0 S) t0) =
      Nbar S g ((t0 : S.Mbar) : S.O))
    (hext : timmesfeldIsExtraspecial (timmesfeldFStar (centralizer ({t0} : Set (Mbar0 S)))))
    (hcard : Nat.card (timmesfeldFStar (centralizer ({t0} : Set (Mbar0 S)))) = 2 ^ 17)
    (ht2 : orderOf t0 = 2)
    (hX : Nonempty (Mbar0 S ≃* PSL(10, ZMod 2)) ∨ Nonempty (Mbar0 S ≃* timmesfeldPSU 10)) :
    False := by
  have hK := h2 (Mbar0 S) hX t0 ht2 hext hcard _
    (comap_inclC_normal fun k hk r hr => conj_mem_Rbar_of_mem_Ct hk hr)
    (comap_inclC_perfect hR0 hperf) (fstar_le_comap_inclC hmap Nbar_le_Rbar)
  have hc1 : Nat.card ((Rbar S g ((t0 : S.Mbar) : S.O)).comap (inclC (Mbar0 S) t0)) =
      Nat.card (Rbar S g ((t0 : S.Mbar) : S.O)) := by
    rw [← card_map_of_injective (inclC_injective (t0 := t0)), map_comap_inclC hR0]
  have hc2 : Nat.card (Rbar S g ((t0 : S.Mbar) : S.O)) =
      2 ^ 17 * Nat.card (RmodN S g ((t0 : S.Mbar) : S.O)) :=
    (card_Rbar_eq H.conj_mem _).trans (congrArg (· * Nat.card (RmodN S g _)) hcardN)
  have key : ¬ 2 ^ 28 ∣ Nat.card (RmodN S g ((t0 : S.Mbar) : S.O)) :=
    not_two_pow_dvd_card_RmodN hcase hd
  have hK3 : 2 ^ 45 ∣ 2 ^ 17 * Nat.card (RmodN S g ((t0 : S.Mbar) : S.O)) :=
    (hK.trans (dvd_of_eq hc1)).trans (dvd_of_eq hc2)
  generalize Nat.card (RmodN S g ((t0 : S.Mbar) : S.O)) = n at key hK3
  omega

end CFSG.LargeExtraspecial.S14
