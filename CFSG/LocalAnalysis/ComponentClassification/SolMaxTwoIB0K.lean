module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutA
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAReciprocalFusion

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped commutatorElement

variable {X : Type} [Group X]

theorem mul_mul_self_eq_one_of_commute {u v : X} (hu : u * u = 1) (hv : v * v = 1)
    (huv : u * v = v * u) : u * v * (u * v) = 1 := by
  calc u * v * (u * v) = u * (v * u) * v := by group
    _ = u * (u * v) * v := by rw [← huv]
    _ = u * u * (v * v) := by group
    _ = 1 := by rw [hu, hv, one_mul]

theorem commutatorElement_mul_eq_of_commute_left {l a t : X} (hla : l * a = a * l)
    (hat : a * t = t * a) : ⁅l, a * t⁆ = ⁅l, t⁆ := by
  have h0 : a * l⁻¹ = l⁻¹ * a := by
    calc a * l⁻¹ = l⁻¹ * (l * a) * l⁻¹ := by group
      _ = l⁻¹ * (a * l) * l⁻¹ := by rw [hla]
      _ = l⁻¹ * a := by group
  calc ⁅l, a * t⁆ = l * (t * a) * l⁻¹ * (t * a)⁻¹ := by rw [commutatorElement_def, hat]
    _ = l * t * (a * l⁻¹) * a⁻¹ * t⁻¹ := by group
    _ = l * t * (l⁻¹ * a) * a⁻¹ * t⁻¹ := by rw [h0]
    _ = ⁅l, t⁆ := by rw [commutatorElement_def]; group

theorem le_of_perfect_of_le_odd_sup [Finite X] {L O K : Subgroup X} (hperf : ⁅L, L⁆ = L)
    (hO : Odd (Nat.card O)) (hOK : O ≤ normalizer (K : Set X)) (hL : L ≤ O ⊔ K) : L ≤ K := by
  set G : Subgroup X := O ⊔ K with hGdef
  have hOG : O ≤ G := le_sup_left
  have hKG : K ≤ G := le_sup_right
  have hGN : G ≤ normalizer (K : Set X) := sup_le hOK le_normalizer
  set K' : Subgroup ↥G := K.subgroupOf G with hK'def
  have hK'n : K'.Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [hK'def, mem_subgroupOf] at hk ⊢
    simpa using (mem_normalizer_iff.mp (hGN g.2) k).mp hk
  let π : ↥G →* ↥G ⧸ K' := QuotientGroup.mk' K'
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective K'
  have hsup : O.subgroupOf G ⊔ K' = ⊤ := by
    have h1 : (O ⊔ K).subgroupOf G = ⊤ := subgroupOf_self G
    rwa [subgroupOf_sup hOG hKG] at h1
  have hOπ : (O.subgroupOf G).map π = ⊤ := by
    have h1 := congrArg (Subgroup.map π) hsup
    have h2 : K'.map π = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨k, hk, rfl⟩
      exact (QuotientGroup.eq_one_iff k).mpr hk
    rwa [Subgroup.map_sup, h2, sup_bot_eq, Subgroup.map_top_of_surjective _ hπ] at h1
  have hodd : Odd (Nat.card (↥G ⧸ K')) := by
    have h1 : Nat.card ((O.subgroupOf G).map π) ∣ Nat.card (O.subgroupOf G) :=
      Subgroup.card_map_dvd _ π
    rw [hOπ, Subgroup.card_top, Nat.card_congr (subgroupOfEquivOfLe hOG).toEquiv] at h1
    exact hO.of_dvd_nat h1
  have : Group.IsSolvable (↥G ⧸ K') := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  set L' : Subgroup ↥G := L.subgroupOf G with hL'def
  have hL'perf : ⁅L', L'⁆ = L' := by
    apply map_injective G.subtype_injective
    rw [map_commutator, hL'def, subgroupOf_map_subtype, inf_of_le_left hL, hperf]
  have hLπ : L'.map π = ⊥ :=
    eq_bot_of_perfect_of_le_range (MonoidHom.id _) (by rw [← map_commutator, hL'perf])
      fun y _ => MonoidHom.mem_range.mpr ⟨y, rfl⟩
  intro x hx
  have h1 : π ⟨x, hL hx⟩ ∈ L'.map π :=
    ⟨⟨x, hL hx⟩, by rw [hL'def]; exact hx, rfl⟩
  rw [hLπ, mem_bot] at h1
  have h2 := (QuotientGroup.eq_one_iff (⟨x, hL hx⟩ : ↥G)).mp h1
  rwa [hK'def, mem_subgroupOf] at h2

theorem thetaFunctor_eq_of_inf_le [Finite X] {E : Subgroup X} (hEel : IsElementaryAbelian 2 E)
    {b : X} (hEb : E ≤ centralizer ({b} : Set X))
    (h : (pPrimeCore 2 (centralizer ({b} : Set X))).map (centralizer ({b} : Set X)).subtype ⊓
        centralizer (E : Set X) ≤
      (pPrimeCore 2 (centralizer (E : Set X))).map (centralizer (E : Set X)).subtype) :
    SolAltLit.thetaFunctor E b =
      (pPrimeCore 2 (centralizer ({b} : Set X))).map (centralizer ({b} : Set X)).subtype := by
  set O := (pPrimeCore 2 (centralizer ({b} : Set X))).map (centralizer ({b} : Set X)).subtype
    with hOdef
  have hEO : E ≤ normalizer (O : Set X) :=
    hEb.trans (Sol78.le_normalizer_map_subtype (pPrimeCore 2 (centralizer ({b} : Set X))))
  have : IsElementaryAbelian 2 E := hEel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 E := IsElementaryAbelian.isPGroup 2 E
  have hcop : Nat.Coprime 2 (Nat.card O) := by
    rw [hOdef, Subgroup.card_map_of_injective (centralizer ({b} : Set X)).subtype_injective]
    exact pPrimeCore_coprime_card
  apply le_antisymm
  · refine sup_le ?_ inf_le_left
    rw [commutator_le]
    intro x hx g hg
    have h1 : g * x⁻¹ * g⁻¹ ∈ O := (mem_normalizer_iff.mp (hEO hg) _).mp (inv_mem hx)
    have h2 : ⁅x, g⁆ = x * (g * x⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
    rw [h2]
    exact mul_mem hx h1
  · rw [← SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2 Nat.prime_two
      E O hE2 hEO hcop]
    exact sup_le le_sup_left ((le_inf inf_le_left h).trans le_sup_right)

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem normalizer_closure_le_of_diag (hbal : Sol78.BalanceTwoComponentInput)
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35) {F : Subgroup X}
    {DF : Finset (Fin n)} (hFJ : F ≤ J)
    (hFk : Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hDF : DF.card = 4) (hFs : ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω)
    (hδ : ∀ a ∈ F, a ≠ 1 →
      (pPrimeCore 2 ↥(centralizer ({a * t} : Set X))).map
          (centralizer ({a * t} : Set X)).subtype ⊓ centralizer (F : Set X) ≤
        (pPrimeCore 2 ↥(centralizer (F : Set X))).map (centralizer (F : Set X)).subtype)
    {x x' : X} (hx : x ∈ F) (hx1 : x ≠ 1) (hx' : x' ∈ F) (hx'1 : x' ≠ 1) (hxx' : x ≠ x') :
    normalizer (closure ({x, x' * t} : Set X) : Set X) ≤
      normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hFsq⟩ := card_sq_of_klein hFk
  have hFel : IsElementaryAbelian 2 F := isElementaryAbelian_of_klein hFk
  have hFne : F ≠ ⊥ := fun h => hx1 (by rw [h] at hx; exact mem_bot.mp hx)
  have hcF : ∀ y ∈ F, ∀ z ∈ F, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hFel.toIsMulCommutative.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hJt : ∀ y ∈ J, y * t = t * y := fun y hy =>
    mem_centralizer_singleton_iff.mp (S.pair.1.2.1 hy)
  have ht2 : orderOf t = 2 := S.pair.1.1
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have hsq : ∀ y ∈ F, y * y = 1 := fun y hy => by rw [← sq]; exact hFsq y hy
  have hx2 : orderOf x = 2 := orderOf_eq_prime (hFsq x hx) hx1
  have hx't : x' * t = t * x' := hJt x' (hFJ hx')
  have hx't1 : x' * t ≠ 1 := fun h =>
    S.t_not_mem (by rw [eq_inv_of_mul_eq_one_right h]; exact J.inv_mem (hFJ hx'))
  have hx't2 : orderOf (x' * t) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact mul_mul_self_eq_one_of_commute (hsq x' hx') htt hx't)
      hx't1
  have hxx't : x * (x' * t) = x' * t * x := by
    calc x * (x' * t) = x * x' * t := (mul_assoc _ _ _).symm
      _ = x' * x * t := by rw [hcF x hx x' hx']
      _ = x' * (x * t) := mul_assoc _ _ _
      _ = x' * (t * x) := by rw [hJt x (hFJ hx)]
      _ = x' * t * x := (mul_assoc _ _ _).symm
  have hne : x ≠ x' * t := fun h => S.t_not_mem (by
    have h1 : t = x'⁻¹ * x := by rw [h]; group
    rw [h1]
    exact J.mul_mem (J.inv_mem (hFJ hx')) (hFJ hx))
  set B₀ := closure ({x, x' * t} : Set X) with hB₀def
  have : IsKleinFour ↥B₀ :=
    UnbalancedGS.ReciprocalFusion.isKleinFour_closure_pair hx2 hx't2 hxx't hne
  have hxB : x ∈ B₀ := subset_closure (Set.mem_insert _ _)
  have hx'tB : x' * t ∈ B₀ := subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hB₀4 : Nat.card B₀ = 4 := IsKleinFour.card_four
  have hB₀el : IsElementaryAbelian 2 B₀ := isElementaryAbelian_of_klein
    (klein_of_card_sq hB₀4 fun y hy => ABGLocalTools.kleinFour_mul_self (T := B₀) hy)
  have hB₀ne : B₀ ≠ ⊥ := fun h => hx1 (by rw [h] at hxB; exact mem_bot.mp hxB)
  have hB₀le : B₀ ≤ F ⊔ zpowers t := by
    rw [hB₀def, closure_le]
    rintro g (rfl | rfl)
    · exact mem_sup_left hx
    · exact mul_mem (mem_sup_left hx') (mem_sup_right (mem_zpowers t))
  have hSF := S.ofFour hFJ hFk hDF hFs
  have htF : t ∈ centralizer (F : Set X) := hSF.t_mem_centralizer
  have hW1 := (Sol78.signalizerCompletion_of_balanceLemma h33 X S.nonab S.kProper S.unbal S.notU
    S.pair e hFJ hFk ⟨DF, hDF, hFs⟩ ht2 htF S.t_mem_coreActionKernel S.t_not_mem).2.2 B₀ hB₀le
    hB₀4
  have hW2 := hSF.completion_eq_completion_self h33 ht2 htF S.t_mem_coreActionKernel S.t_not_mem
  have hW3 := S.completion_eq_of_four h33 h35 hFJ hFk hDF hFs
  have hFat : ∀ a ∈ F, F ≤ centralizer ({a * t} : Set X) := fun a ha y hy =>
    mem_centralizer_singleton_iff.mpr (by
      calc y * (a * t) = y * a * t := (mul_assoc _ _ _).symm
        _ = a * y * t := by rw [hcF y hy a ha]
        _ = a * (y * t) := mul_assoc _ _ _
        _ = a * (t * y) := by rw [hJt y (hFJ hy)]
        _ = a * t * y := (mul_assoc _ _ _).symm)
  have hθ : ∀ b ∈ B₀, b ≠ 1 → SolAltLit.thetaFunctor F b = SolAltLit.thetaFunctor B₀ b := by
    intro b hb hb1
    rw [thetaFunctor_eq_of_balance hbal hB₀el hB₀ne hb hb1]
    rcases ABGLocalTools.kleinFour_mem_cases (T := B₀) hxB hx'tB hb hx1 hx't1 hne with
      h | h | h | h
    · exact absurd h hb1
    · rw [h]
      exact thetaFunctor_eq_of_balance hbal hFel hFne hx hx1
    · rw [h]
      exact thetaFunctor_eq_of_inf_le hFel (hFat x' hx') (hδ x' hx' hx'1)
    · have hxx'F : x * x' ∈ F := mul_mem hx hx'
      have hxx'1 : x * x' ≠ 1 := fun h' => hxx' (by
        rw [eq_inv_of_mul_eq_one_left h', inv_eq_of_mul_eq_one_right (hsq x' hx')])
      rw [h, ← mul_assoc]
      exact thetaFunctor_eq_of_inf_le hFel (hFat _ hxx'F) (hδ _ hxx'F hxx'1)
  have hWB : Sol78.signalizerCompletion B₀ B₀ = Sol78.signalizerCompletion F B₀ := by
    unfold Sol78.signalizerCompletion
    exact iSup_congr fun b => iSup_congr fun hb => iSup_congr fun hb1 => (hθ b hb hb1).symm
  have hN := normalizer_le_normalizer_signalizerCompletion_self B₀
  rwa [hWB, ← hW1, hW2, hW3] at hN

end Sig36

end CFSG.ComponentClassification.SolMax
