module

public import CFSG.ClassicalInvolution.RouteD.TypeAModel
public import CFSG.ClassicalInvolution.RouteD.TypeUFrame
public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Pairs

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg Module Matrix
open scoped MatrixGroups

section Helpers

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem typeU_suMat_commute {i j : Su K p f n} (h : Commute i j) :
    suMat i * suMat j = suMat j * suMat i := by
  rw [← suMat_mul, ← suMat_mul, h.eq]

theorem spaces_of_commutes_su (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {hn : 2 ≤ n}
    (hn3 : 3 ≤ n) {L₁ L₂ : Subgroup (Su K p f n)} {i₁ i₂ : Su K p f n}
    (h₁ : IsLongRootSU2 K p f hn L₁ i₁) (h₂ : IsLongRootSU2 K p f hn L₂ i₂) (hne : i₁ ≠ i₂)
    (hc : Commutes L₁ L₂) :
    minusSpaceSU i₁ ≤ fixSpaceSU i₂ ∧ minusSpaceSU i₂ ≤ fixSpaceSU i₁ ∧
      minusSpaceSU i₁ ⊓ minusSpaceSU i₂ = ⊥ := by
  have hcomm : Commute i₁ i₂ := hc i₁ h₁.mem i₂ h₂.mem
  rcases lemma_6_5_su hK hp hn3 h₁ h₂ hcomm hne with ⟨-, h1, h2', h3⟩ | ⟨hnot, -⟩
  · exact ⟨h1, h2', h3⟩
  · exact absurd (Subgroup.mem_centralizer_iff.mpr fun x hx => hc x hx i₂ h₂.mem) hnot

theorem inf_ne_bot_of_not_commutes_su (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n}
    {L₁ L₂ : Subgroup (Su K p f n)} {i₁ i₂ : Su K p f n} (h₁ : IsLongRootSU2 K p f hn L₁ i₁)
    (h₂ : IsLongRootSU2 K p f hn L₂ i₂) (hc : Commute i₁ i₂) (hnc : ¬ Commutes L₁ L₂) :
    minusSpaceSU i₁ ⊓ minusSpaceSU i₂ ≠ ⊥ := by
  intro h
  apply hnc
  intro x hx y hy
  rw [h₁.eq_longRootGroupSU h2] at hx
  rw [h₂.eq_longRootGroupSU h2] at hy
  exact mul_comm_of_inf_eq_bot_su h2 h₁.coe_mul_self h₂.coe_mul_self (typeU_suMat_commute hc) h
    hx hy

end Helpers

section Middle

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem commutes_middle_su (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {hn : 2 ≤ n}
    (hn3 : 3 ≤ n) {R₁ R₂ R₃ R : Subgroup (Su K p f n)} {i₁ i₂ i₃ i : Su K p f n}
    (h₁ : IsLongRootSU2 K p f hn R₁ i₁) (h₂ : IsLongRootSU2 K p f hn R₂ i₂)
    (h₃ : IsLongRootSU2 K p f hn R₃ i₃) (h : IsLongRootSU2 K p f hn R i)
    (c12 : Commute i₁ i₂) (c23 : Commute i₂ i₃) (c13 : Commute i₁ i₃) (n13 : i₁ ≠ i₃)
    (n1 : i ≠ i₁) (n3 : i ≠ i₃) (hR13 : Commutes R₁ R₃) (hn12 : ¬ Commutes R₁ R₂)
    (hn23 : ¬ Commutes R₂ R₃) (hR1 : Commutes R R₁) (hR3 : Commutes R R₃) : Commutes R R₂ := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  obtain ⟨-, -, h13⟩ := spaces_of_commutes_su hK hp hn3 h₁ h₃ n13 hR13
  obtain ⟨a1, a1', -⟩ := spaces_of_commutes_su hK hp hn3 h h₁ n1 hR1
  obtain ⟨a3, a3', -⟩ := spaces_of_commutes_su hK hp hn3 h h₃ n3 hR3
  have h12 := inf_ne_bot_of_not_commutes_su h2 h₁ h₂ c12 hn12
  have h23 := inf_ne_bot_of_not_commutes_su h2 h₂ h₃ c23 hn23
  obtain ⟨hc, hV⟩ := middle_core h2 h₁.coe_mul_self h₂.coe_mul_self h₃.coe_mul_self
    h.coe_mul_self (typeU_suMat_commute c12) (typeU_suMat_commute c23) (typeU_suMat_commute c13)
    (h₂.finrank_minusSpaceSU h2) h13 h12 h23 a1 a1' a3 a3'
  intro x hx y hy
  rw [h.eq_longRootGroupSU h2] at hx
  rw [h₂.eq_longRootGroupSU h2] at hy
  exact mul_comm_of_inf_eq_bot_su h2 h.coe_mul_self h₂.coe_mul_self hc hV hx hy

end Middle

section Partner

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem typeU_LcU_congr {T T' : Pair n} (h : T.1 = T'.1) : LcU K p f T = LcU K p f T' := by
  have : T = T' := Subtype.ext h
  rw [this]

theorem typeU_zEltU_ne_of_mem (h2 : (2 : K) ≠ 0) {T T' : Pair n} {x : Fin n} (hx : x ∈ T.1)
    (hx' : x ∉ T'.1) : zEltU K p f T ≠ zEltU K p f T' := by
  intro h
  have := congrArg Subtype.val (Subtype.ext (zMat_inj h2 (congrArg suMat h)) : T = T')
  rw [this] at hx
  exact hx' hx

theorem exists_partner_su (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {k : ℕ} (hk : 2 ≤ k)
    {hn2 : 2 ≤ k + 3} {R₀ : Subgroup (Su K p f (k + 3))} {i₀ : Su K p f (k + 3)}
    (h₀ : IsLongRootSU2 K p f hn2 R₀ i₀) {R : ℕ → Subgroup (Su K p f (k + 3))}
    {i : ℕ → Su K p f (k + 3)} (hR : ∀ a < k, IsLongRootSU2 K p f hn2 (R a) (i a))
    (hcomm : ∀ a < k, Commute i₀ (i a)) (hcomm' : ∀ a < k, ∀ b < k, Commute (i a) (i b))
    (hinj : ∀ a < k, ∀ b < k, a ≠ b → i a ≠ i b) (h0ne : ∀ a < k, i₀ ≠ i a)
    (hR0 : ∀ a < k, Commutes R₀ (R a))
    (hfar : ∀ a < k, ∀ b < k, a + 2 ≤ b → Commutes (R a) (R b))
    (hadj : ∀ a, a + 1 < k → ¬ Commutes (R a) (R (a + 1))) :
    ∃ (B : Subgroup (Su K p f (k + 3))) (iB : Su K p f (k + 3)), IsLongRootSU2 K p f hn2 B iB ∧
      Commute iB i₀ ∧ iB ≠ i₀ ∧ ¬ Commutes B R₀ ∧
      Commute iB (i 0) ∧ iB ≠ i 0 ∧ ¬ Commutes B (R 0) ∧
      ∀ a, 1 ≤ a → a < k → Commute iB (i a) ∧ iB ≠ i a ∧ Commutes B (R a) := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  have hn3 : 3 ≤ k + 3 := by omega
  obtain ⟨u, hu⟩ : ∃ u : ℕ → Su K p f (k + 3), ∀ a < k, u a = i a :=
    ⟨fun a => if a < k then i a else 1, fun a ha => by simp [ha]⟩
  have hchain : IsInvChain (fun a => suMat (u a)) k :=
    { sq := fun a ha => by
        simp only [hu a ha]
        exact (hR a ha).coe_mul_self
      comm := fun a ha b hb => by
        simp only [hu a ha, hu b hb]
        exact typeU_suMat_commute (hcomm' a ha b hb)
      dim := fun a ha => by
        show finrank K (eigSpace (suMat (u a)) (-1)) = 2
        rw [hu a ha]
        exact (hR a ha).finrank_minusSpaceSU h2
      far := fun a ha b hb hab => by
        simp only [hu a ha, hu b hb]
        exact (spaces_of_commutes_su hK hp hn3 (hR a ha) (hR b hb) (hinj a ha b hb (by omega))
          (hfar a ha b hb hab)).2.2
      adj := fun a ha => by
        simp only [hu a (by omega), hu (a + 1) ha]
        exact inf_ne_bot_of_not_commutes_su h2 (hR a (by omega)) (hR (a + 1) ha)
          (hcomm' a (by omega) (a + 1) ha) (hadj a ha)
      ne := fun a ha h => by
        simp only [hu a (by omega), hu (a + 1) ha] at h
        exact hinj a (by omega) (a + 1) ha (by omega) (suMat_injective h) }
  obtain ⟨hkN, P, hPI, hPJ⟩ := hchain.exists_su_frame hσ h2 hk
  have hJ : suMat i₀ * suMat P = suMat P * negTail K (k + 3) k := by
    refine hPJ _ h₀.coe_mul_self ?_ ?_ ?_
    · intro a ha
      simp only [hu a ha]
      exact typeU_suMat_commute (hcomm a ha)
    · intro v hv
      rw [chainFix, Submodule.mem_iInf]
      intro a
      show v ∈ eigSpace (suMat (u (a : ℕ))) 1
      rw [hu a a.2]
      exact (spaces_of_commutes_su hK hp hn3 h₀ (hR a a.2) (h0ne a a.2) (hR0 a a.2)).1 hv
    · have := h₀.finrank_minusSpaceSU h2
      rw [show k + 3 - (k + 1) = 2 by omega]
      exact this
  have hcinj : Function.Injective (MulAut.conj P).toMonoidHom := (MulAut.conj P).injective
  let T : ∀ a, a < k → Pair (k + 3) := fun a ha =>
    natPair (k + 3) a (a + 1) (by omega) (by omega) (by omega)
  let T₀ : Pair (k + 3) := natPair (k + 3) (k + 1) (k + 2) (by omega) (by omega) (by omega)
  let Tb : Pair (k + 3) := natPair (k + 3) 0 (k + 1) (by omega) (by omega) (by omega)
  have hia : ∀ a (ha : a < k), i a = P * zEltU K p f (T a ha) * P⁻¹ := by
    intro a ha
    have h := hPI a ha
    rw [hu a ha, negBlock_eq_zMat (by omega : a + 2 ≤ k + 3)] at h
    have h' : i a * P = P * zEltU K p f (T a ha) := by
      apply suMat_injective
      rw [suMat_mul, suMat_mul, suMat_zEltU]
      exact h
    rw [eq_mul_inv_iff_mul_eq, h']
  have hRa : ∀ a (ha : a < k), R a = (LcU K p f (T a ha)).map (MulAut.conj P).toMonoidHom := by
    intro a ha
    have h := hPI a ha
    rw [hu a ha, negBlock_eq_zMat (by omega : a + 2 ≤ k + 3)] at h
    rw [(hR a ha).eq_longRootGroupSU h2, longRootGroupSU_eq_map_conj_of_mul_eq P h]
    rfl
  have hJ' : suMat i₀ * suMat P = suMat P * zMat K (k + 3) T₀.1 := by
    rw [hJ, negTail_eq_zMat]
    rfl
  have hi0 : i₀ = P * zEltU K p f T₀ * P⁻¹ := by
    have h' : i₀ * P = P * zEltU K p f T₀ := by
      apply suMat_injective
      rw [suMat_mul, suMat_mul, suMat_zEltU]
      exact hJ'
    rw [eq_mul_inv_iff_mul_eq, h']
  have hR0' : R₀ = (LcU K p f T₀).map (MulAut.conj P).toMonoidHom := by
    rw [h₀.eq_longRootGroupSU h2, longRootGroupSU_eq_map_conj_of_mul_eq P hJ']
    rfl
  have hconjne : ∀ {x y : Su K p f (k + 3)}, x ≠ y → P * x * P⁻¹ ≠ P * y * P⁻¹ := by
    intro x y hxy h
    exact hxy (mul_left_cancel (mul_right_cancel h))
  have hmemb : ∀ {T' : Pair (k + 3)}, ∀ x : Fin (k + 3), x ∈ Tb.1 → x ∉ T'.1 →
      P * zEltU K p f Tb * P⁻¹ ≠ P * zEltU K p f T' * P⁻¹ := fun {T'} x hx hx' =>
    hconjne (typeU_zEltU_ne_of_mem h2 hx hx')
  have hcz : ∀ T' : Pair (k + 3), Commute (P * zEltU K p f Tb * P⁻¹)
      (P * zEltU K p f T' * P⁻¹) := fun T' =>
    commute_conj (signGroupU_comm (zEltU_mem_signGroupU Tb) (zEltU_mem_signGroupU T')) P
  have hk0 : (⟨0, by omega⟩ : Fin (k + 3)) ∈ Tb.1 := by simp [Tb, natPair]
  refine ⟨(LcU K p f Tb).map (MulAut.conj P).toMonoidHom, P * zEltU K p f Tb * P⁻¹,
    (isLongRootSU2_LcU h2 hn2 Tb).conj P, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hi0]; exact hcz T₀
  · rw [hi0]
    exact hmemb ⟨0, by omega⟩ hk0 (by simp [T₀, natPair, Fin.ext_iff])
  · rw [hR0', commutes_map_iff _ hcinj]
    exact not_commutes_LcU_overlap hK hp hn3 (i := ⟨0, by omega⟩) (j := ⟨k + 1, by omega⟩)
      (k := ⟨k + 2, by omega⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff])
  · rw [hia 0 (by omega)]; exact hcz _
  · rw [hia 0 (by omega)]
    exact hmemb ⟨k + 1, by omega⟩ (by simp [Tb, natPair]) (by simp [T, natPair, Fin.ext_iff]; omega)
  · rw [hRa 0 (by omega), commutes_map_iff _ hcinj]
    have hswap : LcU K p f Tb = LcU K p f (⟨{⟨k + 1, by omega⟩, ⟨0, by omega⟩},
        Finset.card_pair (by simp)⟩ : Pair (k + 3)) :=
      typeU_LcU_congr (Finset.pair_comm _ _)
    rw [hswap]
    exact not_commutes_LcU_overlap hK hp hn3 (i := ⟨k + 1, by omega⟩) (j := ⟨0, by omega⟩)
      (k := ⟨1, by omega⟩) (by simp) (by simp)
      (by simp [Fin.ext_iff]; omega)
  · intro a ha1 ha
    refine ⟨?_, ?_, ?_⟩
    · rw [hia a ha]; exact hcz _
    · rw [hia a ha]
      exact hmemb ⟨0, by omega⟩ hk0 (by simp [T, natPair, Fin.ext_iff]; omega)
    · rw [hRa a ha, commutes_map_iff _ hcinj]
      refine commutes_LcU_of_disjoint h2 ?_
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Tb, T, natPair, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at hx hx'
      omega

end Partner

end CFSG.ClassicalInvolution.RouteD
