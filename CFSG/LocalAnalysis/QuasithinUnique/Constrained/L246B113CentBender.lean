module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Rank2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinBender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25RankOne
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.Assembly.OrderReductions.CharacterInflation
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.QuasithinUnique.Bridge

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Unc25G2.BenderBorel
open CFSG.Assembly.LowTwoRank CFSG.Quasithin

section Regular

variable {X : Type} [Group X]

theorem mem_normalizer_of_fixes {Q : Subgroup X} (β : MulAut X) (hβ : ∀ t ∈ Q, β t = t) {x : X}
    (hx : x ∈ Subgroup.normalizer (Q : Set X)) : β x ∈ Subgroup.normalizer (Q : Set X) := by
  have hQ : ∀ y : X, y ∈ Q ↔ β y ∈ Q := by
    intro y
    refine ⟨fun hy => by rw [hβ y hy]; exact hy, fun hy => ?_⟩
    have h1 : β⁻¹ (β y) = β y := by
      have : β⁻¹ (β y) = (β⁻¹ : MulAut X) (β y) := rfl
      rw [MulAut.inv_def, MulEquiv.symm_apply_eq]
      exact (hβ _ hy).symm
    have h2 : β⁻¹ (β y) = y := by simp
    rw [← h2, h1]
    exact hy
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro h
  have hh : β (β⁻¹ h) = h := by simp
  have e1 : β x * h * (β x)⁻¹ = β (x * β⁻¹ h * x⁻¹) := by rw [map_mul, map_mul, map_inv, hh]
  rw [e1, ← hQ, ← hx, hQ (β⁻¹ h), hh]

theorem aut_eq_one_of_regular [Finite X] [IsSimpleGroup X] {Q : Subgroup X} (hQ : IsPGroup 2 Q)
    (hN : Subgroup.normalizer (Q : Set X) ≠ ⊤)
    (hreg : ∀ a b : X ⧸ Subgroup.normalizer (Q : Set X), a ≠ QuotientGroup.mk 1 →
      b ≠ QuotientGroup.mk 1 → ∃ r ∈ Q, r • a = b)
    (α : MulAut X) (hα : Odd (orderOf α)) (hfix : ∀ t ∈ Q, α t = t) : α = 1 := by
  set N := Subgroup.normalizer (Q : Set X) with hNdef
  have hαinv : ∀ t ∈ Q, α⁻¹ t = t := by
    intro t ht
    rw [MulAut.inv_def, MulEquiv.symm_apply_eq]
    exact (hfix t ht).symm
  have hαN : ∀ x ∈ N, α x ∈ N := fun x hx => mem_normalizer_of_fixes α hfix hx
  have hαN' : ∀ x, α x ∈ N → x ∈ N := fun x hx => by
    have := mem_normalizer_of_fixes α⁻¹ hαinv hx
    simpa using this
  have hbase : ∀ x : X, (QuotientGroup.mk x : X ⧸ N) = QuotientGroup.mk 1 ↔ x ∈ N := by
    intro x
    rw [QuotientGroup.eq, mul_one]
    exact N.inv_mem_iff
  have step1 : ∀ x : X, x⁻¹ * α x ∈ N := by
    intro x
    by_cases hx : x ∈ N
    · exact N.mul_mem (N.inv_mem hx) (hαN x hx)
    · have hax : α x ∉ N := fun h => hx (hαN' x h)
      obtain ⟨r, hr, hrx⟩ := hreg (QuotientGroup.mk x) (QuotientGroup.mk (α x))
        (fun h => hx ((hbase x).1 h)) (fun h => hax ((hbase (α x)).1 h))
      have hnx : (r * x)⁻¹ * α x ∈ N := QuotientGroup.eq.1 hrx
      have hpow : ∀ k : ℕ, (r ^ k * x)⁻¹ * (α ^ k) x ∈ N := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have h1 : α ((α ^ k) x) = α (r ^ k * x * ((r ^ k * x)⁻¹ * (α ^ k) x)) := by
            rw [mul_inv_cancel_left]
          have h2 : α x = r * x * ((r * x)⁻¹ * α x) := by rw [mul_inv_cancel_left]
          have h3 : (α ^ (k + 1)) x = α ((α ^ k) x) := by rw [pow_succ']; rfl
          have h4 : α (r ^ k) = r ^ k := by rw [map_pow, hfix r hr]
          have h5 : (r ^ (k + 1) * x)⁻¹ * (α ^ (k + 1)) x =
              ((r * x)⁻¹ * α x) * α ((r ^ k * x)⁻¹ * (α ^ k) x) := by
            rw [h3, h1, map_mul, map_mul, h4]
            nth_rewrite 2 [h2]
            group
          rw [h5]
          exact N.mul_mem hnx (hαN _ ih)
      have hm := hpow (orderOf α)
      rw [pow_orderOf_eq_one, MulAut.one_apply] at hm
      have hm' : x⁻¹ * r ^ orderOf α * x ∈ N := by
        have := N.inv_mem hm
        simpa [mul_assoc] using this
      obtain ⟨j, hj⟩ := hQ ⟨r, hr⟩
      have hrj : r ^ 2 ^ j = 1 := congrArg Subtype.val hj
      have hcop : IsCoprime (orderOf α : ℤ) ((2 ^ j : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right j hα.coprime_two_right)
      obtain ⟨a, b, hab⟩ := hcop
      have hrr : r = (r ^ orderOf α) ^ a := by
        have e1 : r ^ (((2 ^ j : ℕ) : ℤ) * b) = 1 := by
          rw [zpow_mul, zpow_natCast, hrj, one_zpow]
        have e2 : r ^ ((orderOf α : ℤ) * a) = (r ^ orderOf α) ^ a := by
          rw [zpow_mul, zpow_natCast]
        calc r = r ^ (a * (orderOf α : ℤ) + b * ((2 ^ j : ℕ) : ℤ)) := by rw [hab, zpow_one]
          _ = r ^ ((orderOf α : ℤ) * a) * r ^ (((2 ^ j : ℕ) : ℤ) * b) := by
              rw [← zpow_add]
              congr 1
              ring
          _ = (r ^ orderOf α) ^ a := by rw [e1, e2, mul_one]
      have hxr : x⁻¹ * r * x ∈ N := by
        have h6 : x⁻¹ * r * x = (x⁻¹ * r ^ orderOf α * x) ^ a := by
          have := conj_zpow (a := x⁻¹) (b := r ^ orderOf α) (i := a)
          rw [inv_inv] at this
          rw [this, ← hrr]
        rw [h6]
        exact zpow_mem hm' a
      have e : x⁻¹ * α x = (x⁻¹ * r * x) * ((r * x)⁻¹ * α x) := by group
      rw [e]
      exact N.mul_mem hxr hnx
  have step2 : ∀ g : X, g⁻¹ * α g ∈ N.normalCore := by
    intro g b
    have e1 := step1 (g * b⁻¹)
    have e2 := step1 b⁻¹
    have := N.mul_mem e1 (N.inv_mem e2)
    have e3 : b * (g⁻¹ * α g) * b⁻¹ =
        (g * b⁻¹)⁻¹ * α (g * b⁻¹) * (b⁻¹⁻¹ * α b⁻¹)⁻¹ := by
      rw [map_mul]
      group
    rw [e3]
    exact this
  have hcore : N.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N.normalCore with h | h
    · exact h
    · exfalso
      apply hN
      rw [eq_top_iff]
      rw [← h]
      exact Subgroup.normalCore_le N
  ext g
  have h1 := step2 g
  rw [hcore, Subgroup.mem_bot, inv_mul_eq_one] at h1
  rw [MulAut.one_apply]
  exact h1.symm

end Regular

section Bender

open MulAction

theorem sylowAutTrivial_of_bender {X : Type} [Group X] [Finite X] (hB : fusionIsBenderGroup X) :
    SylowAutTrivial X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup X := RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  intro Q α hα hfix
  obtain ⟨q, _, hq4, hBor⟩ := exists_borel_of_bender hB
  obtain ⟨hSE, ⟨D, hDcyc, -, -, hsup⟩, -, -, -⟩ := hBor Q
  have hsolvN := isSolvable_normalizer_of_sup_cyclic Q.isPGroup' hDcyc hsup
  have hreg := regular_of_borel (isSimpleBenderGroup_of_fusion hB) Q hsolvN
  exact aut_eq_one_of_regular Q.isPGroup' hSE.1 (fun a b ha hb => by
    obtain ⟨⟨r, hr⟩, hrb, -⟩ := hreg ha hb
    exact ⟨r, hr, hrb⟩) α hα hfix

theorem sylowAutTrivial_isPSL_two {X : Type} [Group X] [Finite X] {f : ℕ} (h : IsPSL 2 2 f X) :
    SylowAutTrivial X :=
  sylowAutTrivial_of_bender (A5.C25.fusionIsBenderGroup_of_isPSL h)

theorem sylowAutTrivial_isSz {X : Type} [Group X] [Finite X] {f : ℕ} (h : IsSz f X) :
    SylowAutTrivial X :=
  sylowAutTrivial_of_bender (A5.C25.fusionIsBenderGroup_of_isSz h)

theorem sylowAutTrivial_isPSU_three {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (h : IsPSU 3 2 f X) : SylowAutTrivial X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hcard : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  let e' : X ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ f)) := e
  exact sylowAutTrivial_of_bender
    (Or.inr (Or.inl ⟨f, hf, ⟨e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative f hf hcard)⟩⟩))

end Bender


end CFSG.QuasithinUnique.Bridge
