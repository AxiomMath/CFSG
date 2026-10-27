module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcToral
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcTools

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup

variable {T : Type} [Group T]

theorem pPrimeCore_eq_bot_of_isSimpleGroup [Finite T] [IsSimpleGroup T]
    (hna : ∃ a b : T, a * b ≠ b * a) : pPrimeCore 2 T = ⊥ := by
  rw [pPrimeCore_eq_bot_iff]
  intro N hN hNodd
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have hodd : Odd (Nat.card T) := by
      rw [← Subgroup.card_top, ← h]
      exact Nat.coprime_two_left.1 hNodd
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard T hodd
    obtain ⟨a, b, hab⟩ := hna
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 hsolv a b)

theorem pPrimeCore_eq_bot_of_solvable [Finite T]
    (h : ∀ N : Subgroup T, N.Normal → Group.IsSolvable N → N = ⊥) : pPrimeCore 2 T = ⊥ := by
  rw [pPrimeCore_eq_bot_iff]
  intro N hN hNodd
  exact h N hN (CFSG.FeitThompson.isSolvable_of_odd_natCard N (Nat.coprime_two_left.1 hNodd))

theorem pPrimeCore_eq_bot_of_mulEquiv {T' : Type*} [Group T'] (e : T ≃* T')
    (h : pPrimeCore 2 T' = ⊥) : pPrimeCore 2 T = ⊥ := by
  rw [← pPrimeCore_map_iso 2 e.symm, h, Subgroup.map_bot]

theorem innerPart_eq_bot_of_pPrimeCore [Finite T] (hZ : center T = ⊥) {i : MulAut T}
    {F : Subgroup T} (hF : ∀ s, i s = s ↔ s ∈ F) (hO : pPrimeCore 2 F = ⊥)
    {R : Subgroup (MulAut T)} (hRodd : Odd (Nat.card R))
    (hRc : ∀ s : T, i s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) : innerPart i R = ⊥ := by
  have hTF : oddFixed i ≤ F := by
    rw [oddFixed, closure_le]
    rintro s ⟨hs, -⟩
    exact (hF s).1 hs
  have hWF : innerPart i R ≤ F := inf_le_left.trans hTF
  have hAn : ∀ t ∈ F, ∀ a ∈ oddFixed i, t * a * t⁻¹ ∈ oddFixed i := by
    intro t ht a ha
    have hle : oddFixed i ≤ (oddFixed i).comap (MulAut.conj t).toMonoidHom := by
      rw [oddFixed, closure_le]
      rintro s ⟨hs, hso⟩
      refine subset_closure ⟨?_, ?_⟩
      · change i (t * s * t⁻¹) = t * s * t⁻¹
        rw [map_mul, map_mul, map_inv, (hF t).2 ht, hs]
      · change Odd (orderOf ((MulAut.conj t) s))
        rw [MulEquiv.orderOf_eq]
        exact hso
    exact hle ha
  have hsub : ((innerPart i R).subgroupOf F).IsSubnormal :=
    isSubnormal_subgroupOf_of_conj inf_le_left hAn fun a ha _ e he =>
      conj_mem_innerPart hRc ha he
  have hodd : Odd (Nat.card ((innerPart i R).subgroupOf F)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWF).toEquiv]
    exact odd_card_innerPart hZ hRodd
  have h1 := Walter.map_pPrimeCore_le_of_isSubnormal hsub
  have htop : pPrimeCore 2 ((innerPart i R).subgroupOf F) = ⊤ := by
    apply le_antisymm le_top
    apply le_sSup
    exact ⟨Subgroup.normal_top, by
      rw [Subgroup.card_top]
      exact Nat.coprime_two_left.mpr hodd⟩
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hO] at h1
  rw [eq_bot_iff]
  intro n hn
  have h2 := h1 (show (⟨n, hWF hn⟩ : F) ∈ (innerPart i R).subgroupOf F from hn)
  rw [Subgroup.mem_bot] at h2 ⊢
  exact congrArg Subtype.val h2

theorem eq_one_of_conj_mem_of_pPrimeCore [Finite T] (hZ : center T = ⊥) {i : MulAut T}
    {F : Subgroup T} (hF : ∀ s, i s = s ↔ s ∈ F) (hO : pPrimeCore 2 F = ⊥)
    {R : Subgroup (MulAut T)} (hRodd : Odd (Nat.card R)) (hRi : ∀ r ∈ R, r * i = i * r)
    (hRc : ∀ s : T, i s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) {n : T} (hn : MulAut.conj n ∈ R) : n = 1 := by
  have hin : i n = n := by
    apply conj_injective hZ
    rw [conj_apply_eq, ← hRi _ hn, mul_inv_cancel_right]
  have hno : Odd (orderOf n) := by
    rw [← orderOf_injective _ (conj_injective hZ) n]
    exact odd_orderOf_of_mem hRodd hn
  have hnW : n ∈ innerPart i R := mem_inf.2 ⟨subset_closure ⟨hin, hno⟩, hn⟩
  rw [innerPart_eq_bot_of_pPrimeCore hZ hF hO hRodd hRc, mem_bot] at hnW
  exact hnW

theorem outerCoreAt_of_pPrimeCore [Finite T] (hZ : center T = ⊥) {i : MulAut T}
    {F : Subgroup T} (hF : ∀ s, i s = s ↔ s ∈ F) (hO : pPrimeCore 2 F = ⊥)
    (hcomm : ∀ a b : MulAut T, Odd (orderOf a) → Odd (orderOf b) →
      a * b * a⁻¹ * b⁻¹ ∈ (MulAut.conj : T →* MulAut T).range) :
    OuterCoreAt i := by
  intro R hRodd hRi hRc r₁ h₁ r₂ h₂
  obtain ⟨n, hn⟩ := hcomm r₁ r₂ (odd_orderOf_of_mem hRodd h₁) (odd_orderOf_of_mem hRodd h₂)
  have hnR : MulAut.conj n ∈ R := by
    rw [hn]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have hn1 := eq_one_of_conj_mem_of_pPrimeCore hZ hF hO hRodd hRi hRc hnR
  rw [hn1, map_one] at hn
  calc r₁ * r₂ = (r₁ * r₂ * r₁⁻¹ * r₂⁻¹) * (r₂ * r₁) := by group
    _ = r₂ * r₁ := by rw [← hn, one_mul]

theorem commutator_mem_range_conj_of_forall {φ : MulAut T}
    (h : ∀ a : MulAut T, ∃ (g : T) (k : ℕ), a = MulAut.conj g * φ ^ k) (a b : MulAut T) :
    a * b * a⁻¹ * b⁻¹ ∈ (MulAut.conj : T →* MulAut T).range := by
  obtain ⟨g, k, rfl⟩ := h a
  obtain ⟨g', l, rfl⟩ := h b
  have hPQ : (φ ^ k)⁻¹ * φ ^ l = φ ^ l * (φ ^ k)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, (Commute.pow_pow_self φ k l).eq, mul_assoc,
      mul_inv_cancel, mul_one]
  refine ⟨g * (φ ^ k) g' * (φ ^ l) g⁻¹ * g'⁻¹, ?_⟩
  rw [map_mul, map_mul, map_mul, conj_apply_eq, conj_apply_eq, map_inv, map_inv]
  calc MulAut.conj g * (φ ^ k * MulAut.conj g' * (φ ^ k)⁻¹) *
        (φ ^ l * (MulAut.conj g)⁻¹ * (φ ^ l)⁻¹) * (MulAut.conj g')⁻¹ =
      MulAut.conj g * φ ^ k * MulAut.conj g' * ((φ ^ k)⁻¹ * φ ^ l) * (MulAut.conj g)⁻¹ *
        (φ ^ l)⁻¹ * (MulAut.conj g')⁻¹ := by group
    _ = MulAut.conj g * φ ^ k * MulAut.conj g' * (φ ^ l * (φ ^ k)⁻¹) * (MulAut.conj g)⁻¹ *
        (φ ^ l)⁻¹ * (MulAut.conj g')⁻¹ := by rw [hPQ]
    _ = MulAut.conj g * φ ^ k * (MulAut.conj g' * φ ^ l) * (MulAut.conj g * φ ^ k)⁻¹ *
        (MulAut.conj g' * φ ^ l)⁻¹ := by group

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
