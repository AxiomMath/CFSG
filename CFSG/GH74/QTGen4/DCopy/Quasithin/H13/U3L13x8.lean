module

public import CFSG.Quasithin.H13.U3L13x8
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

@[expose] def Stmt13_3_4K_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L K X : Subgroup G), QTH13 G T L →
    quasithinIsFaithfulLocal T K → T ≤ X → X ≤ normalizer (K : Set G) →
    ¬ normalizer (K : Set G) ≤
      X ⊔ centralizerMod (pCoreOf 2 K) (normalizer (K : Set G)) K →
    ∀ p : ℕ, p.Prime →
      p ∣ (centralizerMod (pCoreOf 2 K) (normalizer (K : Set G)) K).relIndex X → p = 2 ∨ p = 3

theorem not_le_sup_centralizerMod_F4 (h1332 : Stmt13_3_2_F4) {T L K H Y : Subgroup G}
    (hH13 : QTH13 G T L) (hK : quasithinIsFaithfulLocal T K) (hH : InH T H)
    (hHK : ¬ H ≤ normalizer (K : Set G)) (hYH : Y ≤ H) (hHY : H ≤ normalizer (Y : Set G))
    (hYK : Y ≤ normalizer (K : Set G)) :
    ¬ K ≤ Y ⊔ centralizerMod (pCoreOf 2 K) (normalizer (K : Set G)) K := by
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h5, ⟨hTK, -, hMK, huniq⟩, ⟨⟨VK, hVK⟩, hallK⟩, -⟩ := h1332 G T L hH13 K hK
  have hq := (hallK VK hVK).2.2.1.quasisimple
  obtain ⟨heven, hnp⟩ := even_not_prime_of_qt13Five h5

  have hU : IsUniqueM (K ⊔ T) (normalizer (K : Set G)) :=
    ⟨⟨hMK, sup_le le_normalizer hTK⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
  have hstar := pCoreOf_sup_eq_bot_of_isUniqueM hU hHK
  have hsyl : IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, hH13.sylow.1, ?_⟩
    show ¬ 2 ∣ T.relIndex ⊤
    rw [relIndex_top_right]
    exact hH13.sylow.2
  have hsylT : IsSylowTwoOf T (K ⊔ T) := isSylowTwoOf_of_le hsyl le_sup_right
  have hTY : T ≤ normalizer (Y : Set G) := hH.1.trans hHY

  have hYC : Y ≤ normalizer
      (centralizerMod (pCoreOf 2 K) (normalizer (K : Set G)) K : Set G) :=
    le_normalizer_centralizerMod
      (hYK.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (hYK.trans le_normalizer) hYK

  have hcomm : ⁅K, T ⊓ K⁆ ≤ (K ⊓ Y) ⊔ pCoreOf 2 K := by
    rw [commutator_le]
    intro k hk s hs
    obtain ⟨c, hc, y, hy, rfl⟩ := exists_mul_of_mem_sup hYC (sup_comm Y _ ▸ hle hk)
    have hsK : s ∈ K := (mem_inf.1 hs).2
    have hu : y * s * y⁻¹ ∈ K := (mem_normalizer_iff.1 (hYK hy) s).1 hsK
    have ho : c * (y * s * y⁻¹) * c⁻¹ * (y * s * y⁻¹)⁻¹ ∈ pCoreOf 2 K :=
      (mem_centralizerMod.1 hc).2.2 _ hu
    have hwK : y * s * y⁻¹ * s⁻¹ ∈ K := mul_mem hu (inv_mem hsK)
    have hwY : y * s * y⁻¹ * s⁻¹ ∈ Y := by
      have h1 : s * y⁻¹ * s⁻¹ ∈ Y :=
        (mem_normalizer_iff.1 (hTY (mem_inf.1 hs).1) _).1 (inv_mem hy)
      have e : y * s * y⁻¹ * s⁻¹ = y * (s * y⁻¹ * s⁻¹) := by group
      rw [e]
      exact mul_mem hy h1
    have e : ⁅c * y, s⁆ = (c * (y * s * y⁻¹) * c⁻¹ * (y * s * y⁻¹)⁻¹) * (y * s * y⁻¹ * s⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (mem_sup_right ho) (mem_sup_left (mem_inf.2 ⟨hwK, hwY⟩))

  have hK1 : K ≤ (K ⊓ Y) ⊔ pCoreOf 2 K :=
    (le_commutator_inf_sup_pCoreOf hsylT hTK hq heven hnp).trans (sup_le hcomm le_sup_right)
  have hO2T : pCoreOf 2 K ≤ T :=
    (pCoreOf_le_pCoreOf_sup hTK).trans (pCoreOf_two_le_of_isSylowTwoOf hsylT)
  have hO2N : pCoreOf 2 K ≤ normalizer ((K ⊓ Y : Subgroup G) : Set G) := fun o ho =>
    inf_normalizer_le_normalizer_inf
      ⟨le_normalizer (LieType.BorelTits.pCoreOf_le 2 K ho), hTY (hO2T ho)⟩
  have hKY : K ≤ K ⊓ Y := by
    calc K = oTwoUpper K := eq_oTwoUpper_of_perfect hK.1.2.1.2.1
      _ ≤ oTwoUpper ((K ⊓ Y) ⊔ pCoreOf 2 K) := oTwoUpper_mono hK1
      _ ≤ K ⊓ Y := oTwoUpper_le_of_sup (LieType.BorelTits.pCoreOf_isPGroup 2 K) hO2N
  have hKH : K ≤ H := (hKY.trans inf_le_right).trans hYH
  rw [sup_eq_right.2 (sup_le hKH hH.1)] at hstar
  exact hH.2 hstar

theorem isTwoThreeGroup_of_F4 (h1332 : Stmt13_3_2_F4) (h1334K : Stmt13_3_4K_F4) {T L K H Y : Subgroup G}
    (hH13 : QTH13 G T L) (hK : quasithinIsFaithfulLocal T K) (hH : InH T H)
    (hHK : ¬ H ≤ normalizer (K : Set G)) (hYH : Y ≤ H) (hHY : H ≤ normalizer (Y : Set G))
    (hYK : Y ≤ normalizer (K : Set G)) : A6.IsTwoThreeGroup Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨hTK, -, hMK, huniq⟩, -, -⟩ := h1332 G T L hH13 K hK
  have hU : IsUniqueM (K ⊔ T) (normalizer (K : Set G)) :=
    ⟨⟨hMK, sup_le le_normalizer hTK⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
  have hstar := pCoreOf_sup_eq_bot_of_isUniqueM hU hHK
  have hTY : T ≤ normalizer (Y : Set G) := hH.1.trans hHY
  set C := centralizerMod (pCoreOf 2 K) (normalizer (K : Set G)) K with hCdef
  have hNC : ∀ {X : Subgroup G}, X ≤ normalizer (K : Set G) → X ≤ normalizer (C : Set G) :=
    fun hX => le_normalizer_centralizerMod
      (hX.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (hX.trans le_normalizer) hX
  have hYTK : Y ⊔ T ≤ normalizer (K : Set G) := sup_le hYK hTK

  have hnot : ¬ normalizer (K : Set G) ≤ (Y ⊔ T) ⊔ C := by
    intro hN
    apply not_le_sup_centralizerMod_F4 h1332 hH13 hK hH hHK hYH hHY hYK
    have hYCN : T ≤ normalizer ((Y ⊔ C : Subgroup G) : Set G) := fun t ht =>
      inf_normalizer_le_normalizer_sup _ _ ⟨hTY ht, hNC hTK ht⟩
    have hD : (Y ⊔ T) ⊔ C = (Y ⊔ C) ⊔ T := by
      rw [sup_assoc, sup_comm T C, ← sup_assoc]
    calc K = oTwoUpper K := eq_oTwoUpper_of_perfect hK.1.2.1.2.1
      _ ≤ oTwoUpper ((Y ⊔ C) ⊔ T) := oTwoUpper_mono (hD ▸ le_normalizer.trans hN)
      _ ≤ Y ⊔ C := oTwoUpper_le_of_sup hH13.sylow.1 hYCN
  have hprimes := h1334K G T L K (Y ⊔ T) hH13 hK le_sup_right hYTK hnot

  have hYC6 : ∀ y ∈ Y, Nat.Coprime (orderOf y) 6 → y ∈ C := by
    intro y hy hy6
    have hn : (C.subgroupOf (Y ⊔ T)).Normal := ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      simpa using (mem_normalizer_iff.1 (hNC hYTK g.2) n).1 hn⟩
    have h1 : y ^ (C.subgroupOf (Y ⊔ T)).index ∈ C := by
      have := Subgroup.pow_index_mem (C.subgroupOf (Y ⊔ T)) (⟨y, mem_sup_left hy⟩ : ↥(Y ⊔ T))
      rw [mem_subgroupOf] at this
      simpa using this
    have hcop : Nat.Coprime (C.subgroupOf (Y ⊔ T)).index (orderOf y) := by
      refine Nat.coprime_of_dvd fun k hk hkm hky => ?_
      have hk23 := hprimes k hk hkm
      have h6 : k ∣ 6 := by rcases hk23 with rfl | rfl <;> norm_num
      have := Nat.dvd_gcd hky h6
      rw [hy6] at this
      exact hk.one_lt.ne' (Nat.dvd_one.1 this)
    exact (zpowers_le.2 h1) (A4.mem_zpowers_pow_of_coprime hcop)

  set S6 : Set G := {y | y ∈ Y ∧ Nat.Coprime (orderOf y) 6} with hS6
  set Y₀ : Subgroup G := closure S6 with hY₀
  have hodd : ∀ y ∈ S6, Odd (orderOf y) := fun y hy =>
    Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) hy.2).symm
  have hY₀Y : Y₀ ≤ Y := (closure_le _).2 fun y hy => hy.1
  have hY₀C : Y₀ ≤ C := (closure_le _).2 fun y hy => hYC6 y hy.1 hy.2

  have hconj : ∀ g : G, (∀ s ∈ S6, g * s * g⁻¹ ∈ Y₀) → ∀ x ∈ Y₀, g * x * g⁻¹ ∈ Y₀ := by
    intro g hg x hx
    have hle : Y₀ ≤ Y₀.comap (MulAut.conj g).toMonoidHom := (closure_le _).2 fun s hs => hg s hs
    exact hle hx
  have hnorm : ∀ {A : Subgroup G}, (∀ g ∈ A, ∀ s ∈ S6, g * s * g⁻¹ ∈ Y₀) →
      A ≤ normalizer (Y₀ : Set G) := by
    intro A hA g hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hconj g (hA g hg) x, fun hx => ?_⟩
    have := hconj g⁻¹ (hA g⁻¹ (inv_mem hg)) _ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at this

  have hHY₀ : H ≤ normalizer (Y₀ : Set G) := hnorm fun g hg s hs => subset_closure
    ⟨(mem_normalizer_iff.1 (hHY hg) s).1 hs.1, by
      have := MulEquiv.orderOf_eq (MulAut.conj g) s
      rw [MulAut.conj_apply] at this
      rw [this]
      exact hs.2⟩

  have hO2T : pCoreOf 2 K ≤ T := (pCoreOf_le_pCoreOf_sup hTK).trans
    (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le (by
      refine ⟨le_top, hH13.sylow.1, ?_⟩
      show ¬ 2 ∣ T.relIndex ⊤
      rw [relIndex_top_right]
      exact hH13.sylow.2) le_sup_right))
  have hKY₀ : K ≤ normalizer (Y₀ : Set G) := hnorm fun k hk s hs => by
    have hsC : s⁻¹ ∈ C := inv_mem (hYC6 s hs.1 hs.2)
    have ho : s⁻¹ * k * s⁻¹⁻¹ * k⁻¹ ∈ pCoreOf 2 K := (mem_centralizerMod.1 hsC).2.2 k hk
    have hmem : k * s * k⁻¹ ∈ Y₀ ⊔ pCoreOf 2 K := by
      have e : k * s * k⁻¹ = s * (s⁻¹ * k * s⁻¹⁻¹ * k⁻¹) := by group
      rw [e]
      exact mul_mem (mem_sup_left (subset_closure hs)) (mem_sup_right ho)
    have hord : Odd (orderOf (k * s * k⁻¹)) := by
      have := MulEquiv.orderOf_eq (MulAut.conj k) s
      rw [MulAut.conj_apply] at this
      rw [this]
      exact hodd s hs
    exact oTwoUpper_le_of_sup (LieType.BorelTits.pCoreOf_isPGroup 2 K)
      ((hO2T.trans hH.1).trans hHY₀) (mem_oTwoUpper_of_odd hmem hord)

  have hO2 : pCoreOf 2 Y₀ = ⊥ := by
    rw [eq_bot_iff, ← hstar]
    refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (((LieType.BorelTits.pCoreOf_le 2 Y₀).trans (hY₀Y.trans hYH)).trans le_sup_right) ?_
      (LieType.BorelTits.pCoreOf_isPGroup 2 Y₀)
    exact (sup_le (sup_le hKY₀ (hH.1.trans hHY₀)) hHY₀).trans
      (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀)

  have hCT : CharTwo H := by
    obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo hH13.sylow
    subst hP
    exact CFSG.Quasithin.charTwo_of_inH hH13.qtke.2.1 P hH
  have hY₀2 : oTwoUpper Y₀ = Y₀ :=
    le_antisymm (oTwoUpper_le Y₀) ((closure_le _).2 fun y hy =>
      mem_oTwoUpper_of_odd (subset_closure hy) (hodd y hy))
  have hY₀1 : Y₀ = ⊥ := by
    by_contra hne
    exact C1Pack153.pCoreOf_ne_bot_of_normal hCT (hY₀Y.trans hYH) hHY₀ hne hY₀2 hO2

  intro p hp hpY
  by_contra hne
  push Not at hne
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) p hpY
  have hy' : orderOf (y : G) = p := by rw [Subgroup.orderOf_coe]; exact hy
  have hcop : Nat.Coprime (orderOf (y : G)) 6 := by
    rw [hy', show (6 : ℕ) = 2 * 3 by norm_num]
    exact Nat.Coprime.mul_right ((Nat.coprime_primes hp Nat.prime_two).2 hne.1)
      ((Nat.coprime_primes hp Nat.prime_three).2 hne.2)
  have h1 : (y : G) ∈ Y₀ := subset_closure ⟨y.2, hcop⟩
  rw [hY₀1, mem_bot] at h1
  rw [h1, orderOf_one] at hy'
  exact hp.one_lt.ne hy'

theorem stmt13_3_8_of_F4 (h1332 : Stmt13_3_2_F4) (h1334K : Stmt13_3_4K_F4) : A6.Stmt13_3_8_F4 := by
  intro G _ _ T L K H Y hH13 hK hH hHK _ hYH hHY hYK
  exact ⟨not_le_sup_centralizerMod_F4 h1332 hH13 hK hH hHK hYH hHY hYK,
    isTwoThreeGroup_of_F4 h1332 h1334K hH13 hK hH hHK hYH hHY hYK⟩

end CFSG.Quasithin.H13.U3
