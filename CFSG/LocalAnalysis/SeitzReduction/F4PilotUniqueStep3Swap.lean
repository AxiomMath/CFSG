module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Basic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsSwapUnique
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainRows
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsSwapRee

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)

section Diagonal

variable {G : Type*} [Group G] {M₁ M₂ : Subgroup G} {t : G}

theorem conj_mem_of_map_conj_eq_swapRow (hswap : M₁.map (MulAut.conj t).toMonoidHom = M₂) {x : G}
    (hx : x ∈ M₁) : t * x * t⁻¹ ∈ M₂ := by
  rw [← hswap]
  exact ⟨x, hx, rfl⟩

@[expose] def swapRowDiag (h₁₂ : M₂ ≤ centralizer (M₁ : Set G))
    (hswap : M₁.map (MulAut.conj t).toMonoidHom = M₂) : M₁ →* G where
  toFun x := (x : G) * (t * x * t⁻¹)
  map_one' := by simp
  map_mul' x y := by
    have h := mem_centralizer_iff.1 (h₁₂ (conj_mem_of_map_conj_eq_swapRow hswap x.2)) y y.2
    simp only [Subgroup.coe_mul]
    calc (x : G) * y * (t * (x * y) * t⁻¹) = x * (y * (t * x * t⁻¹)) * (t * y * t⁻¹) := by
          group
      _ = x * ((t * x * t⁻¹) * y) * (t * y * t⁻¹) := by rw [h]
      _ = x * (t * x * t⁻¹) * (y * (t * y * t⁻¹)) := by group

theorem swapRowDiag_apply (h₁₂ : M₂ ≤ centralizer (M₁ : Set G))
    (hswap : M₁.map (MulAut.conj t).toMonoidHom = M₂) (x : M₁) :
    swapRowDiag h₁₂ hswap x = (x : G) * (t * x * t⁻¹) :=
  rfl

theorem swapRowDiag_injective (h₁₂ : M₂ ≤ centralizer (M₁ : Set G))
    (hswap : M₁.map (MulAut.conj t).toMonoidHom = M₂) (hdisj : M₁ ⊓ M₂ = ⊥) :
    Function.Injective (swapRowDiag h₁₂ hswap) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, swapRowDiag_apply] at hx
  have hx1 : (x : G) = (t * x * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hx
  have hxM₂ : (x : G) ∈ M₂ := by
    rw [hx1]
    exact inv_mem (conj_mem_of_map_conj_eq_swapRow hswap x.2)
  have hbot : (x : G) ∈ M₁ ⊓ M₂ := mem_inf.2 ⟨x.2, hxM₂⟩
  rw [hdisj, mem_bot] at hbot
  exact (Subgroup.mem_bot).2 (Subtype.ext hbot)

theorem range_swapRowDiag_le (h₁₂ : M₂ ≤ centralizer (M₁ : Set G))
    (hswap : M₁.map (MulAut.conj t).toMonoidHom = M₂) (ht2 : t * t = 1) :
    (swapRowDiag h₁₂ hswap).range ≤ (M₁ ⊔ M₂) ⊓ centralizer ({t} : Set G) := by
  rintro _ ⟨x, rfl⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hx₂ := conj_mem_of_map_conj_eq_swapRow hswap x.2
  refine mem_inf.2 ⟨mul_mem (mem_sup_left x.2) (mem_sup_right hx₂), ?_⟩
  have h := mem_centralizer_iff.1 (h₁₂ hx₂) x x.2
  rw [mem_centralizer_singleton_iff, swapRowDiag_apply]
  rw [htinv] at h ⊢
  calc (x : G) * (t * x * t) * t = ((t * x * t) * x) * t := by rw [h]
    _ = t * ((x : G) * (t * x * t)) := by group

theorem range_swapRowDiag_eq [Finite G] {L : Subgroup G} (h₁₂ : M₂ ≤ centralizer (M₁ : Set G))
    (hswap : M₁.map (MulAut.conj t).toMonoidHom = M₂) (hdisj : M₁ ⊓ M₂ = ⊥) (ht2 : t * t = 1)
    (hC : (M₁ ⊔ M₂) ⊓ centralizer ({t} : Set G) = L) (hcard : Nat.card L ≤ Nat.card M₁) :
    (swapRowDiag h₁₂ hswap).range = L := by
  refine Subgroup.eq_of_le_of_card_ge ((range_swapRowDiag_le h₁₂ hswap ht2).trans hC.le) ?_
  rw [← Nat.card_congr (MonoidHom.ofInjective (swapRowDiag_injective h₁₂ hswap hdisj)).toEquiv]
  exact hcard

end Diagonal

section Step3


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]

theorem le_iSup_perfectCore_of_swap (hq : 4 ≤ Nat.card K) (e : L ≃* adjointGroup .F4 K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht2 : t * t = 1) {M₁ M₂ : Subgroup G}
    (h₁₂ : M₂ ≤ centralizer (M₁ : Set G)) (hswap : M₁.map (MulAut.conj t).toMonoidHom = M₂)
    (hdisj : M₁ ⊓ M₂ = ⊥) (htN : t ∈ normalizer ((M₁ ⊔ M₂ : Subgroup G) : Set G))
    (hC : (M₁ ⊔ M₂) ⊓ centralizer ({t} : Set G) = L) (hcard : Nat.card L ≤ Nat.card M₁) :
    M₁ ⊔ M₂ ≤ ⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2},
      perfectCore ((M₁ ⊔ M₂) ⊓ centralizer (modelToG e (leviTorus K J.1) : Set G)) := by
  have hδinj := swapRowDiag_injective h₁₂ hswap hdisj
  have hδL := range_swapRowDiag_eq h₁₂ hswap hdisj ht2 hC hcard
  set E : M₁ ≃* L := (MonoidHom.ofInjective hδinj).trans (MulEquiv.subgroupCongr hδL) with hE
  have hEδ : ∀ x : M₁, ((E x : L) : G) = swapRowDiag h₁₂ hswap x := fun x => rfl
  set Φ₁ : adjointGroup .F4 K →* G := M₁.subtype.comp (E.trans e).symm.toMonoidHom with hΦ₁
  have hΦ₁inj : Function.Injective Φ₁ := M₁.subtype_injective.comp (E.trans e).symm.injective
  have hΦ₁range : Φ₁.range = M₁ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ((E.trans e).symm y).2
    · intro hx
      exact ⟨(E.trans e) ⟨x, hx⟩, by simp [hΦ₁]⟩
  have hkey : ∀ y : adjointGroup .F4 K,
      swapRowDiag h₁₂ hswap ((E.trans e).symm y) = ((e.symm y : L) : G) := by
    intro y
    rw [MulEquiv.symm_trans_apply, ← hEδ, MulEquiv.apply_symm_apply]
  have hgen₁ := range_le_iSup_perfectCore_leviTorus hq hΦ₁inj
  rw [hΦ₁range] at hgen₁
  have hle₁ : ∀ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2},
      perfectCore (M₁ ⊓ centralizer
        ((((leviTorus K J.1).subgroupOf (adjointGroup .F4 K)).map Φ₁ : Subgroup G) : Set G)) ≤
      perfectCore ((M₁ ⊔ M₂) ⊓ centralizer (modelToG e (leviTorus K J.1) : Set G)) := by
    intro J
    refine CFSG.Quasithin.perfectCore_mono (le_inf (inf_le_left.trans le_sup_left) ?_)
    intro y hy
    obtain ⟨hyM₁, hyc⟩ := mem_inf.1 hy
    rw [mem_centralizer_iff]
    intro τ hτ
    obtain ⟨x, hxT, rfl⟩ := (mem_modelToG e).1 hτ
    rw [← hkey x, swapRowDiag_apply]
    set z : M₁ := (E.trans e).symm x with hz
    have hzT : (z : G) ∈ ((leviTorus K J.1).subgroupOf (adjointGroup .F4 K)).map Φ₁ :=
      ⟨x, mem_subgroupOf.2 hxT, rfl⟩
    have h1 : (z : G) * y = y * z := mem_centralizer_iff.1 hyc _ hzT
    have h2 : y * (t * z * t⁻¹) = (t * z * t⁻¹) * y :=
      mem_centralizer_iff.1 (h₁₂ (conj_mem_of_map_conj_eq_swapRow hswap z.2)) y hyM₁
    calc (z : G) * (t * z * t⁻¹) * y = z * ((t * z * t⁻¹) * y) := by group
      _ = z * (y * (t * z * t⁻¹)) := by rw [← h2]
      _ = (z * y) * (t * z * t⁻¹) := by group
      _ = (y * z) * (t * z * t⁻¹) := by rw [h1]
      _ = y * (z * (t * z * t⁻¹)) := by group
  have hM₁ := hgen₁.trans (iSup_mono hle₁)
  have htP : ∀ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2},
      (perfectCore ((M₁ ⊔ M₂) ⊓ centralizer (modelToG e (leviTorus K J.1) : Set G))).map
        (MulAut.conj t).toMonoidHom =
      perfectCore ((M₁ ⊔ M₂) ⊓ centralizer (modelToG e (leviTorus K J.1) : Set G)) := by
    intro J
    refine mem_normalizer_iff_map_conj_toMonoidHom.1
      (CFSG.Quasithin.normalizer_le_normalizer_perfectCore _
        (inf_normalizer_le_normalizer_inf ⟨htN, le_normalizer ?_⟩))
    exact centralizer_le (SetLike.coe_subset_coe.2 (modelToG_le e _)) htC
  have hM₂ : M₂ ≤ ⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2},
      perfectCore ((M₁ ⊔ M₂) ⊓ centralizer (modelToG e (leviTorus K J.1) : Set G)) := by
    calc M₂ = M₁.map (MulAut.conj t).toMonoidHom := hswap.symm
      _ ≤ (⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2},
            perfectCore ((M₁ ⊔ M₂) ⊓ centralizer (modelToG e (leviTorus K J.1) : Set G))).map
            (MulAut.conj t).toMonoidHom := Subgroup.map_mono hM₁
      _ = _ := by rw [Subgroup.map_iSup]; exact iSup_congr htP
  exact sup_le hM₁ hM₂


theorem unique_of_swap_F4 (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {G₁ : Subgroup G} {K₁ : Type}
    [Field K₁] (hK₁ : Nat.card K₁ = 2 ^ f) (e₁ : G₁ ≃* adjointGroup .F4 K₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hJ : ∀ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2},
      pieceCore e J.1 ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom) :
    ∀ g : G, g⁻¹ * t * g ∈
        normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) →
      g ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  have : Finite K₁ := finite_of_natCard_eq_two_pow hK₁
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have e₂ : G₁.map (MulAut.conj t).toMonoidHom ≃* adjointGroup .F4 K₁ :=
    (G₁.equivMapOfInjective _ (MulAut.conj t).injective).symm.trans e₁
  refine unique_of_forall_conjugate_generation
    (J := fun J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2} => modelToG e (leviTorus K J.1))
    hJ fun h htM => ?_
  rw [conjugate_sup_eq_sup_conjugate] at htM ⊢
  have e₁' := (conjugateSymmEquiv G₁ h).trans e₁
  have e₂' := (conjugateSymmEquiv (G₁.map (MulAut.conj t).toMonoidHom) h).trans e₂
  have h₁₂' := conjugate_le_centralizer_conjugate_of_le h₁₂ h
  obtain ⟨hswap, hC⟩ := swap_and_inf_centralizer_eq_of_mem_normalizer_F4 hset hf hK e htC ht hK₁
    hK₁ e₁' e₂' h₁₂' htM
  have hdisj := inf_eq_bot_of_le_centralizer_F4 e₁' h₁₂'
  have hcard : Nat.card L ≤ Nat.card (CFSG.conjugate G₁ h) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr e₁'.toEquiv,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hK, hK₁]
  exact le_iSup_perfectCore_of_swap hq e htC ht2 h₁₂' hswap hdisj htM hC hcard

end Step3

section Input


theorem swapRowUniqueInput_holds : SwapRowUniqueInput := by
  intro G _ _ L K _ _ _ e t f hw hf _ _ G₁ ⟨e₁⟩ h₁₂ hsup g hg
  have hJ : ∀ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2},
      pieceCore e J.1 ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := fun J => by
    rw [hsup]
    exact le_iSup (fun J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2} => pieceCore e J.1) J
  have h := unique_of_swap_F4 hw.standard hf hw.card_eq e hw.mem_centralizer hw.orderOf_eq
    hw.card_eq e₁ h₁₂ hJ g
  rw [hsup] at h
  exact h hg

end Input

end CFSG.SeitzReduction.F4Pilot
