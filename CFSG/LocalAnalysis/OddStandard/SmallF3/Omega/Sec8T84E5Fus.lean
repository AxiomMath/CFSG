module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E1Lem35
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E3Low

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private lemma isElemAbelian_map_hom {G : Type*} [Group G] {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 2 E) (f : G →* G) :
    CFSG.Open.IsElemAbelian 2 (E.map f) := by
  haveI : IsMulCommutative E := hE.1
  refine ⟨?_, ?_⟩
  · infer_instance
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_pow, hE.2 y hy, map_one]

theorem sec8t84_no_conj_T0 {G : Type} [Group G] [Finite G] {t : G} {S1 S2 E1 E2 : Subgroup G}
    (ht : t * t = 1)
    (hcomm : ∀ a ∈ S1, ∀ b ∈ S2, a * b = b * a) (hinf : S1 ⊓ S2 = ⊥)
    (hE1 : E1 ≤ S1) (hE2 : E2 ≤ S2)
    (he1 : CFSG.Open.IsElemAbelian 2 E1) (hc1 : Nat.card E1 = 16)
    (he2 : CFSG.Open.IsElemAbelian 2 E2) (hc2 : Nat.card E2 = 16)
    (hn1 : ∀ a ∈ S1, ∀ e ∈ E1, a * e * a⁻¹ ∈ E1) (hn2 : ∀ a ∈ S2, ∀ e ∈ E2, a * e * a⁻¹ ∈ E2)
    (hrank : ∀ A : Subgroup G, A ≤ centralizer ({t} : Set G) → CFSG.Open.IsElemAbelian 2 A →
      Nat.card A < 2 ^ 6) :
    ∀ u ∈ S1 ⊔ S2, ¬ IsConj t u := by
  intro u huS hconj
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hu2 : u * u = 1 := by
    rw [← hc]
    calc
      (c * t * c⁻¹) * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
      _ = 1 := by rw [ht]; group
  obtain ⟨A, hAcent, hAea, hAcard⟩ :=
    sec8t84_rank_low hcomm hinf hE1 hE2 he1 hc1 he2 hc2 hn1 hn2 huS hu2
  let φ : G →* G := (MulAut.conj c⁻¹).toMonoidHom
  have hφu : φ u = t := by
    change (MulAut.conj c⁻¹) u = t
    rw [MulAut.conj_apply, inv_inv, ← hc]
    group
  have hA'le : A.map φ ≤ centralizer ({t} : Set G) := by
    have h1 : A.map φ ≤ (centralizer ({u} : Set G)).map φ := Subgroup.map_mono hAcent
    have h2 : (centralizer ({u} : Set G)).map φ ≤
        centralizer (φ '' ({u} : Set G)) :=
      Subgroup.map_centralizer_le_centralizer_image _ φ
    rw [Set.image_singleton, hφu] at h2
    exact le_trans h1 h2
  have hA'ea : CFSG.Open.IsElemAbelian 2 (A.map φ) := isElemAbelian_map_hom hAea φ
  have hinj : Function.Injective φ := fun _ _ h => (MulAut.conj c⁻¹).injective h
  have hA'card : Nat.card (A.map φ) = Nat.card A :=
    Subgroup.card_map_of_injective (f := φ) hinj
  have hlt := hrank (A.map φ) hA'le hA'ea
  rw [hA'card] at hlt
  omega

theorem sec8t84_fusion {G : Type} [Group G] [Finite G] {t : G} {S1 S2 E1 E2 T0 T : Subgroup G}
    (ht : t * t = 1) (hT0 : T0 = S1 ⊔ S2) (hT : T = zpowers t ⊔ T0)
    (hcomm : ∀ a ∈ S1, ∀ b ∈ S2, a * b = b * a) (hinf : S1 ⊓ S2 = ⊥)
    (h12 : ∀ a ∈ S1, t * a * t⁻¹ ∈ S2) (h21 : ∀ a ∈ S2, t * a * t⁻¹ ∈ S1)
    (hE1 : E1 ≤ S1) (hE2 : E2 ≤ S2)
    (he1 : CFSG.Open.IsElemAbelian 2 E1) (hc1 : Nat.card E1 = 16)
    (he2 : CFSG.Open.IsElemAbelian 2 E2) (hc2 : Nat.card E2 = 16)
    (hn1 : ∀ a ∈ S1, ∀ e ∈ E1, a * e * a⁻¹ ∈ E1) (hn2 : ∀ a ∈ S2, ∀ e ∈ E2, a * e * a⁻¹ ∈ E2)
    (hrank : ∀ A : Subgroup G, A ≤ centralizer ({t} : Set G) → CFSG.Open.IsElemAbelian 2 A →
      Nat.card A < 2 ^ 6) :
    ∀ u ∈ T, IsConj t u → ∃ a ∈ T, u = a * t * a⁻¹ := by
  intro u huT hconj
  have hu2 : u * u = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    rw [← hc]
    calc
      (c * t * c⁻¹) * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
      _ = 1 := by rw [ht]; group
  have huNotT0 : u ∉ T0 := by
    intro huT0
    exact sec8t84_no_conj_T0 ht hcomm hinf hE1 hE2 he1 hc1 he2 hc2 hn1 hn2 hrank u
      (hT0 ▸ huT0) hconj
  obtain ⟨a, haS1, ha⟩ := sec8t84_lemma35 ht hT0 hT hcomm hinf h12 h21 u huT hu2 huNotT0
  have hS1T : S1 ≤ T := by
    rw [hT]
    exact le_sup_of_le_right (hT0 ▸ le_sup_left)
  exact ⟨a, hS1T haS1, ha⟩

end CFSG.OddStandard.SmallF3.Omega
