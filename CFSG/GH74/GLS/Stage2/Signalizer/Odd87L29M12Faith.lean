module

public import CFSG.GH74.GLS.Stage2.Local.Defs
import CFSG.GH74.GLS.IVK.L2.Transport
import CFSG.GH74.GLS.TwoThin.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29M12

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

theorem index_subgroupOf_sup_eq_two {G : Type} [Group G] [Finite G] {K : Subgroup G} {y : G}
    {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q)
    (hL : IVK.IsL2 (↥K ⧸ pPrimeCore 2 ↥K) (fun r => r = q))
    (hP : PGLModO K (zpowers y) q) : (K.subgroupOf (K ⊔ zpowers y)).index = 2 := by
  classical
  obtain ⟨hN, F₁, iF₁, fF₁, hF₁, ⟨e⟩⟩ := hP
  obtain ⟨F₀, iF₀, fF₀, hF₀, ⟨e₀⟩⟩ := hL
  set A : Subgroup G := K ⊔ zpowers y with hA
  set O' : Subgroup G := pPrimeCoreOf 2 K with hO'
  have hKA : K ≤ A := le_sup_left
  have hO'K : O' ≤ K := TwoThin.pPrimeCoreOf_le K
  have hO'A : O' ≤ A := hO'K.trans hKA
  have hL0 : IVK.L2Field F₀ := ⟨by rw [hF₀]; exact hq, by rw [hF₀]; omega⟩
  have hL1 : IVK.L2Field F₁ := ⟨by rw [hF₁]; exact hq, by rw [hF₁]; omega⟩
  have hcardPSL : Nat.card (GorensteinWalter.PSL2 F₁) = Nat.card (GorensteinWalter.PSL2 F₀) := by
    rw [GorensteinWalter.psl2_card_formula F₁ (IVK.isOddPrimePower_of_L2Field hL1),
      GorensteinWalter.psl2_card_formula F₀ (IVK.isOddPrimePower_of_L2Field hL0), hF₀, hF₁]
  have hcardK : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) = Nat.card (GorensteinWalter.PSL2 F₀) :=
    Nat.card_congr (e₀.trans (IVK.L2.equivPSL F₀)).toEquiv
  have hcardAbar :
      Nat.card (↥A ⧸ O'.subgroupOf A) = 2 * Nat.card (GorensteinWalter.PSL2 F₀) := by
    rw [Nat.card_congr e.toEquiv, IVK.card_pgl2_eq_two_mul hL1, hcardPSL]
  have hO'card : Nat.card ↥(O'.subgroupOf A) = Nat.card ↥(pPrimeCore 2 ↥K) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hO'A).toEquiv, hO']
    exact Subgroup.card_map_of_injective K.subtype_injective
  have hcardA : Nat.card ↥A =
      Nat.card ↥(pPrimeCore 2 ↥K) * (2 * Nat.card (GorensteinWalter.PSL2 F₀)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (O'.subgroupOf A), hcardAbar, hO'card]
    ring
  have hcardK' : Nat.card ↥K =
      Nat.card ↥(pPrimeCore 2 ↥K) * Nat.card (GorensteinWalter.PSL2 F₀) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K), hcardK]
    ring
  have hpos : 0 < Nat.card ↥(pPrimeCore 2 ↥K) * Nat.card (GorensteinWalter.PSL2 F₀) := by
    rw [← hcardK']
    exact Nat.card_pos
  have h1 := Subgroup.index_mul_card (K.subgroupOf A)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv, hcardA, hcardK'] at h1
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1]
  ring

private theorem commutator_le_of_index_two {A : Type*} [Group A] {H : Subgroup A}
    (h : H.index = 2) : commutator A ≤ H := by
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two h,
    Subgroup.mul_mem_iff_of_index_two h, Subgroup.mul_mem_iff_of_index_two h, inv_mem_iff,
    inv_mem_iff]
  tauto

private theorem eq_one_of_commute_commutator {F : Type} [Field F] [Finite F]
    (hK : GorensteinWalter.IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    {x : GorensteinWalter.PGL2 F} (hx : ∀ c ∈ commutator (GorensteinWalter.PGL2 F), c * x = x * c) :
    x = 1 := by
  have h1 : x ∈ centralizer
      ((commutator (GorensteinWalter.PGL2 F) : Subgroup (GorensteinWalter.PGL2 F)) :
        Set (GorensteinWalter.PGL2 F)) := by
    rw [Subgroup.mem_centralizer_iff]
    exact hx
  rw [GorensteinWalter.pgl2_commutator_eq_psl2_range_of_card_gt_three F hK hcard,
    GorensteinWalter.pgl2_psl2Range_centralizer_eq_bot F hK] at h1
  exact Subgroup.mem_bot.mp h1

private theorem map_eq_one_of_commutes {A : Type} [Group A] {F : Type} [Field F] [Finite F]
    (hodd : GorensteinWalter.IsOddPrimePower (Nat.card F)) (hgt : 3 < Nat.card F)
    (φ : A →* GorensteinWalter.PGL2 F) (hφ : Function.Surjective φ) {Kb : Subgroup A}
    (hKb : Kb.index = 2) {a : A} (hcomm : ∀ k ∈ Kb, φ (a * k * a⁻¹ * k⁻¹) = 1) : φ a = 1 := by
  have h1 : (commutator A).map φ = commutator (GorensteinWalter.PGL2 F) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hφ]
    rfl
  refine eq_one_of_commute_commutator hodd hgt fun c hc => ?_
  rw [← h1] at hc
  obtain ⟨k, hk, rfl⟩ := Subgroup.map_mono (commutator_le_of_index_two hKb) hc
  have h2 := hcomm k hk
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
  exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h2)).symm

private theorem mem_of_commutes_of_index_two {G : Type} [Group G] {A K O' : Subgroup G}
    {F : Type} [Field F] [Finite F] (hodd : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (hgt : 3 < Nat.card F) [(O'.subgroupOf A).Normal]
    (e : (↥A ⧸ O'.subgroupOf A) ≃* GorensteinWalter.PGL2 F)
    (hidx : (K.subgroupOf A).index = 2) {p : G} (hp : p ∈ A)
    (hcomm : ∀ k ∈ K, p * k * p⁻¹ * k⁻¹ ∈ O') : p ∈ O' := by
  let φ : ↥A →* GorensteinWalter.PGL2 F :=
    (e : ↥A ⧸ O'.subgroupOf A →* GorensteinWalter.PGL2 F).comp
      (QuotientGroup.mk' (O'.subgroupOf A))
  have hφker : ∀ a : ↥A, φ a = 1 ↔ (a : G) ∈ O' := fun a => by
    show e (QuotientGroup.mk a) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hφsurj : Function.Surjective φ := e.surjective.comp QuotientGroup.mk_surjective
  refine (hφker ⟨p, hp⟩).1 (map_eq_one_of_commutes hodd hgt φ hφsurj hidx fun k hk => ?_)
  exact (hφker _).2 (hcomm k hk)

theorem mem_pPrimeCoreOf_of_commutes {G : Type} [Group G] [Finite G] {K : Subgroup G} {y : G}
    {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q)
    (hL : IVK.IsL2 (↥K ⧸ pPrimeCore 2 ↥K) (fun r => r = q))
    (hP : PGLModO K (zpowers y) q) {p : G} (hp : p ∈ K ⊔ zpowers y)
    (hcomm : ∀ k ∈ K, p * k * p⁻¹ * k⁻¹ ∈ pPrimeCoreOf 2 K) : p ∈ pPrimeCoreOf 2 K := by
  have hidx := index_subgroupOf_sup_eq_two hq h5 hL hP
  obtain ⟨hN, F₁, iF₁, fF₁, hF₁, ⟨e⟩⟩ := hP
  have hL1 : IVK.L2Field F₁ := ⟨by rw [hF₁]; exact hq, by rw [hF₁]; omega⟩
  exact mem_of_commutes_of_index_two (IVK.isOddPrimePower_of_L2Field hL1) hL1.2 e hidx hp hcomm

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29M12
