module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionTransport
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect
  map_perfectCore)

section Maps

variable {A G : Type*} [Group A] [Group G] {f : A →* G}

theorem map_inf_centralizer_of_injective (hf : Function.Injective f) (M H : Subgroup A) :
    (M ⊓ centralizer (H : Set A)).map f = M.map f ⊓ centralizer ((H.map f : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨hmM, hmC⟩ := mem_inf.1 hm
    refine mem_inf.2 ⟨⟨m, hmM, rfl⟩, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hmC h hh]
  · intro hx
    obtain ⟨⟨m, hmM, rfl⟩, hC⟩ := mem_inf.1 hx
    refine ⟨m, mem_inf.2 ⟨hmM, mem_centralizer_iff.2 fun h hh => ?_⟩, rfl⟩
    apply hf
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.1 hC (f h) ⟨h, hh, rfl⟩

theorem map_centralizer_singleton_of_injective (hf : Function.Injective f) (a : A) :
    (centralizer ({a} : Set A)).map f = f.range ⊓ centralizer ({f a} : Set G) := by
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine mem_inf.2 ⟨⟨b, rfl⟩, ?_⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hb
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hb]
  · intro hx
    obtain ⟨⟨b, rfl⟩, hb⟩ := mem_inf.1 hx
    refine ⟨b, ?_, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at hb
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact hf hb

theorem map_perfectCore_centralizer_singleton [Finite A] [Finite G] (hf : Function.Injective f)
    (a : A) :
    (perfectCore (centralizer ({a} : Set A))).map f =
      perfectCore (f.range ⊓ centralizer ({f a} : Set G)) := by
  rw [map_perfectCore, map_centralizer_singleton_of_injective hf]

end Maps

section Intrinsic

variable {G : Type*} [Group G] [Finite G]

theorem perfectCore_subgroupOf {H M : Subgroup G} (hHM : H ≤ M) :
    perfectCore (H.subgroupOf M) = (perfectCore H).subgroupOf M := by
  apply map_injective M.subtype_injective
  rw [map_perfectCore, subgroupOf_map_subtype, inf_of_le_left hHM,
    subgroupOf_map_subtype, inf_of_le_left ((perfectCore_le H).trans hHM)]

theorem inf_sup_eq_of_perfectCore_inf_centralizer {Q M M' Z : Subgroup G}
    (hMN : M ≤ normalizer (Q : Set G)) (hQM : Disjoint Q M) (hQM' : Disjoint Q M')
    (hMM' : Q ⊔ M = Q ⊔ M') (hQZ : Q ≤ centralizer (Z : Set G)) :
    (perfectCore (M ⊓ centralizer (Z : Set G)) ⊔ Q) ⊓ M' =
      perfectCore (M' ⊓ centralizer (Z : Set G)) := by
  set ι := EPilot.mulEquivOfComplements hMN hQM hQM' hMM' with hι
  set f : M →* G := M'.subtype.comp ι.toMonoidHom with hf
  have hfinj : Function.Injective f := M'.subtype_injective.comp ι.injective
  have hspec : ∀ m : M, ((ι m : M') : G)⁻¹ * m ∈ Q :=
    EPilot.mulEquivOfComplements_inv_mul_mem hMN hQM hQM' hMM'
  have hcen : ((M ⊓ centralizer (Z : Set G)).subgroupOf M).map f =
      M' ⊓ centralizer (Z : Set G) := by
    apply le_antisymm
    · rintro _ ⟨m, hm, rfl⟩
      have hmC : (m : G) ∈ centralizer (Z : Set G) := (mem_subgroupOf.1 hm).2
      have hq := hQZ (hspec m)
      refine mem_inf.2 ⟨(ι m).2, ?_⟩
      have e : f m = (m : G) * (((ι m : M') : G)⁻¹ * m)⁻¹ := by
        rw [hf, MonoidHom.comp_apply]
        simp only [MulEquiv.coe_toMonoidHom, coe_subtype]
        group
      rw [e]
      exact Subgroup.mul_mem _ hmC (Subgroup.inv_mem _ hq)
    · intro x hx
      obtain ⟨hxM', hxC⟩ := mem_inf.1 hx
      set m := ι.symm ⟨x, hxM'⟩ with hm
      have hιm : ι m = ⟨x, hxM'⟩ := by rw [hm, MulEquiv.apply_symm_apply]
      have hq := hQZ (hspec m)
      rw [hιm] at hq
      refine ⟨m, mem_subgroupOf.2 ⟨m.2, ?_⟩, ?_⟩
      · have e : (m : G) = x * (x⁻¹ * m) := by group
        rw [e]
        exact Subgroup.mul_mem _ hxC hq
      · rw [hf, MonoidHom.comp_apply]
        simp only [MulEquiv.coe_toMonoidHom, coe_subtype]
        rw [hιm]
  have hcore : ((perfectCore (M ⊓ centralizer (Z : Set G))).subgroupOf M).map f =
      perfectCore (M' ⊓ centralizer (Z : Set G)) := by
    rw [← perfectCore_subgroupOf inf_le_left, map_perfectCore, hcen]
  rw [← hcore, hf, ← Subgroup.map_map]
  exact (EPilot.map_mulEquivOfComplements hMN hQM hQM' hMM'
    ((perfectCore_le _).trans inf_le_left)).symm

theorem sup_eq_sup_of_perfectCore_inf_centralizer {Q M M' Z : Subgroup G}
    (hMN : M ≤ normalizer (Q : Set G)) (hQM : Disjoint Q M) (hQM' : Disjoint Q M')
    (hMM' : Q ⊔ M = Q ⊔ M') (hQZ : Q ≤ centralizer (Z : Set G)) :
    Q ⊔ perfectCore (M ⊓ centralizer (Z : Set G)) =
      Q ⊔ perfectCore (M' ⊓ centralizer (Z : Set G)) := by
  have h1 := inf_sup_eq_of_perfectCore_inf_centralizer hMN hQM hQM' hMM' hQZ
  have h2 := inf_sup_eq_of_perfectCore_inf_centralizer
    (EPilot.le_normalizer_of_sup_eq hMN hMM') hQM' hQM hMM'.symm hQZ
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [← h2]
    refine inf_le_left.trans (sup_le le_sup_right le_sup_left)
  · refine sup_le le_sup_left ?_
    rw [← h1]
    refine inf_le_left.trans (sup_le le_sup_right le_sup_left)

end Intrinsic

section Transport

variable {A G : Type*} [Group A] [Group G] {φ φ' : A →* G} {Λ₀ Λ₁ : Subgroup A}

theorem map_comap_map_eq (hΛ : Λ₀.map φ = Λ₁.map φ') {H : Subgroup A} (hH : H ≤ Λ₀) :
    ((H.map φ).comap φ').map φ' = H.map φ :=
  map_comap_eq_self ((map_mono hH).trans (hΛ ▸ map_le_range φ' Λ₁))

theorem comap_map_le (hφ' : Function.Injective φ') (hΛ : Λ₀.map φ = Λ₁.map φ')
    {H : Subgroup A} (hH : H ≤ Λ₀) : (H.map φ).comap φ' ≤ Λ₁ := fun _ hx =>
  (mem_map_iff_mem hφ').1 (hΛ ▸ map_mono hH hx)

theorem le_normalizer_comap_map (hΛ : Λ₀.map φ = Λ₁.map φ') {H : Subgroup A}
    (hN : Λ₀ ≤ normalizer (H : Set A)) :
    Λ₁ ≤ normalizer (((H.map φ).comap φ' : Subgroup A) : Set A) := by
  intro x hx
  obtain ⟨x₀, hx₀, hxx₀⟩ : φ' x ∈ Λ₀.map φ := hΛ ▸ mem_map_of_mem φ' hx
  have hN' : φ' x ∈ normalizer ((H.map φ : Subgroup G) : Set G) :=
    hxx₀ ▸ le_normalizer_map φ ⟨x₀, hN hx₀, rfl⟩
  rw [mem_normalizer_iff] at hN' ⊢
  intro g
  rw [mem_comap, mem_comap, hN' (φ' g), map_mul, map_mul, map_inv]

theorem isPGroup_comap_map (hφ' : Function.Injective φ') {p : ℕ} {H : Subgroup A}
    (hH : IsPGroup p H) : IsPGroup p ((H.map φ).comap φ') :=
  (hH.map φ).comap_of_injective φ' hφ'

theorem le_comap_map_of_forall (hφ : Function.Injective φ)
    (hΛ : Λ₀.map φ = Λ₁.map φ') {p : ℕ} {Q : Subgroup A}
    (hmax : ∀ T : Subgroup A, IsPGroup p T → T ≤ Λ₀ → Λ₀ ≤ normalizer (T : Set A) → T ≤ Q)
    {T : Subgroup A} (hT : IsPGroup p T) (hTΛ : T ≤ Λ₁) (hN : Λ₁ ≤ normalizer (T : Set A)) :
    T ≤ (Q.map φ).comap φ' := by
  have hT₀ := hmax ((T.map φ').comap φ) (isPGroup_comap_map hφ hT)
    (comap_map_le hφ hΛ.symm hTΛ) (le_normalizer_comap_map hΛ.symm hN)
  rw [← map_le_iff_le_comap, ← map_comap_map_eq hΛ.symm hTΛ]
  exact map_mono hT₀

theorem map_commutator_comap_map (hΛ : Λ₀.map φ = Λ₁.map φ') {H : Subgroup A} (hH : H ≤ Λ₀) :
    (⁅(H.map φ).comap φ', (H.map φ).comap φ'⁆).map φ' = ⁅H, H⁆.map φ := by
  rw [map_commutator, map_comap_map_eq hΛ hH, map_commutator]

theorem commutator_comap_map_eq (hφ' : Function.Injective φ') (hΛ : Λ₀.map φ = Λ₁.map φ')
    {H : Subgroup A} (hH : H ≤ Λ₀) (hp : ⁅H, H⁆ = H) :
    ⁅(H.map φ).comap φ', (H.map φ).comap φ'⁆ = (H.map φ).comap φ' := by
  apply map_injective hφ'
  rw [map_commutator_comap_map hΛ hH, hp, map_comap_map_eq hΛ hH]

theorem comap_map_ne_bot (hφ : Function.Injective φ) (hΛ : Λ₀.map φ = Λ₁.map φ')
    {H : Subgroup A} (hH : H ≤ Λ₀) (h1 : H ≠ ⊥) : (H.map φ).comap φ' ≠ ⊥ := by
  intro h
  apply h1
  have h2 := map_comap_map_eq hΛ hH
  rw [h, Subgroup.map_bot] at h2
  exact (map_eq_bot_iff_of_injective H hφ).1 h2.symm

theorem comap_map_le_centralizer (hφ' : Function.Injective φ') {S Z : Subgroup A}
    (hSZ : S ≤ centralizer (Z : Set A)) :
    (S.map φ).comap φ' ≤ centralizer (((Z.map φ).comap φ' : Subgroup A) : Set A) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro z hz
  apply hφ'
  have hx' : φ' x ∈ S.map φ := hx
  have hz' : φ' z ∈ Z.map φ := hz
  obtain ⟨s, hs, hsx⟩ := hx'
  obtain ⟨w, hw, hwz⟩ := hz'
  rw [map_mul, map_mul, ← hsx, ← hwz, ← map_mul, ← map_mul, mem_centralizer_iff.1 (hSZ hs) w hw]

end Transport

section Card

open Matrix

variable {K : Type*} [Field K] [Fintype K]

theorem card_GL_lt_card_GL_succ {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (GL (Fin m) K) < Nat.card (GL (Fin (m + 1)) K) := by
  rw [card_GL_field, card_GL_field, Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  set q := Fintype.card K with hq
  have hq2 : 1 < q := Fintype.one_lt_card
  have hA : 1 ≤ ∏ i : Fin m, (q ^ m - q ^ (i : ℕ)) := by
    refine Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    exact Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_right hq2 i.2)
  have hAB : ∏ i : Fin m, (q ^ m - q ^ (i : ℕ)) ≤ ∏ i : Fin m, (q ^ (m + 1) - q ^ (i : ℕ)) :=
    Finset.prod_le_prod fun i _ =>
      Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega) (Nat.le_succ m)) _
  have hC : 2 ≤ q ^ (m + 1) - q ^ m := by
    have h1 : 2 * q ^ m ≤ q ^ (m + 1) := by
      rw [pow_succ, mul_comm]
      exact Nat.mul_le_mul_left _ hq2
    have h2 : 2 ≤ q ^ m := le_trans hq2 (by
      calc q = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ m := Nat.pow_le_pow_right (by omega) hm)
    omega
  calc ∏ i : Fin m, (q ^ m - q ^ (i : ℕ))
      < 2 * ∏ i : Fin m, (q ^ m - q ^ (i : ℕ)) := by omega
    _ ≤ 2 * ∏ i : Fin m, (q ^ (m + 1) - q ^ (i : ℕ)) := Nat.mul_le_mul_left _ hAB
    _ ≤ (q ^ (m + 1) - q ^ m) * ∏ i : Fin m, (q ^ (m + 1) - q ^ (i : ℕ)) :=
        Nat.mul_le_mul_right _ hC
    _ = (∏ i : Fin m, (q ^ (m + 1) - q ^ (i : ℕ))) * (q ^ (m + 1) - q ^ m) := mul_comm _ _

theorem card_GL_lt_card_GL {m m' : ℕ} (hm : 1 ≤ m) (hmm' : m < m') :
    Nat.card (GL (Fin m) K) < Nat.card (GL (Fin m') K) := by
  obtain ⟨d, rfl⟩ : ∃ d, m' = m + d + 1 := ⟨m' - m - 1, by omega⟩
  induction d with
  | zero => exact card_GL_lt_card_GL_succ hm
  | succ d ih =>
    exact (ih (by omega)).trans (card_GL_lt_card_GL_succ (by omega))

theorem eq_of_card_specialLinearGroup_eq {m m' : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (h : Nat.card (SpecialLinearGroup (Fin m) K) = Nat.card (SpecialLinearGroup (Fin m') K)) :
    m = m' := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have : Nonempty (Fin m') := ⟨⟨0, hm'⟩⟩
  have hGL : Nat.card (GL (Fin m) K) = Nat.card (GL (Fin m') K) := by
    rw [← card_SL_mul_card_units, ← card_SL_mul_card_units, h]
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exact absurd hGL (card_GL_lt_card_GL hm hlt).ne
  · exact heq
  · exact absurd hGL (card_GL_lt_card_GL hm' hgt).ne'

end Card

end CFSG.SeitzReduction.LinearPilot
