module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Assembly
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.L2Data
import CFSG.LocalAnalysis.AGLEmbeddingD2.U3Data
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

theorem commutative_of_barM_commutative {G : Type} [Group G] {M R : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hRM : R ≤ M) (hR : IsPGroup p R)
    (hc : ∀ x ∈ barM M R, ∀ x' ∈ barM M R, x * x' = x' * x) :
    ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  intro a ha b hb
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set a' : ↥M := ⟨a, hRM ha⟩ with ha'
  set b' : ↥M := ⟨b, hRM hb⟩ with hb'
  have hxa : mk a' ∈ barM M R := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ha)
  have hxb : mk b' ∈ barM M R := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hb)
  have h1 : mk ((b' * a')⁻¹ * (a' * b')) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, hc _ hxa _ hxb]
    exact inv_mul_cancel _
  have hmem : (((b' * a')⁻¹ * (a' * b') : ↥M) : G) ∈ R :=
    R.mul_mem (R.inv_mem (R.mul_mem hb ha)) (R.mul_mem ha hb)
  have h2 := CFSG.AGLEmbedding.eq_one_of_mem_pCoreOf_two hp hp2 hR hmem
    (coe_mem_pCoreOf_two_of_mk_eq_one _ h1)
  have h3 : (b * a)⁻¹ * (a * b) = 1 := h2
  exact (inv_mul_eq_one.mp h3).symm

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G}

theorem _root_.CFSG.AGLEmbeddingD2.D2Escape.elemNine_of_map (h : D2Escape 3 P M A H R)
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    (hRbar : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) =
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
    (hel : IsElemAbelian 3 (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)))
    (hcard : Nat.card (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) = 9) :
    IsElemAbelian 3 R ∧ Nat.card R = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  refine ⟨?_, by rw [← h.card_map_eq le_rfl, ← hRbar]; exact hcard⟩
  have hmemR : ∀ x ∈ R, ∃ a : H, (a : G) = x ∧ π a ∈ (Rbar : Subgroup _) := fun x hx =>
    ⟨⟨x, h.le_H hx⟩, rfl, by
      rw [hRbar]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)⟩
  have hinj : ∀ a b : H, (a : G) ∈ R → (b : G) ∈ R → π a = π b → a = b :=
    fun a b ha hb hab => eq_of_mk_eq_of_mem h.isPGroup ha hb hab
  have hcommR : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, rfl, ha⟩ := hmemR x hx
    obtain ⟨b, rfl, hb⟩ := hmemR y hy
    have h1 := congrArg Subtype.val (hel.1.is_comm.comm (⟨π a, ha⟩ : (Rbar : Subgroup _))
      ⟨π b, hb⟩)
    have h2 : a * b = b * a := hinj _ _ (R.mul_mem hx hy) (R.mul_mem hy hx)
      (by rw [map_mul, map_mul]; exact h1)
    exact congrArg Subtype.val h2
  have hpowR : ∀ x ∈ R, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨a, rfl, ha⟩ := hmemR x hx
    have h1 := hel.2 (π a) ha
    have h2 : a ^ 3 = 1 := hinj _ _ (R.pow_mem hx 3) R.one_mem (by rw [map_pow, map_one]; exact h1)
    exact congrArg Subtype.val h2
  have : IsMulCommutative R := ⟨⟨fun a b => Subtype.ext (hcommR a a.2 b b.2)⟩⟩
  exact ⟨inferInstance, hpowR⟩

theorem _root_.CFSG.AGLEmbeddingD2.D2Escape.elemNine_of_card (h : D2Escape 3 P M A H R)
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hRbar : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) =
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
    (hK : D2AlmostSimple 3 (H ⧸ primeComplementCore (G := H) 3) Rbar
      ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) K)
    (hcard : Nat.card (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) = 3 ^ 2) :
    IsElemAbelian 3 R ∧ Nat.card R = 9 := by
  have hAR : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) =
      (Rbar : Subgroup _) :=
    Subgroup.eq_of_le_of_card_ge hK.A_le (by rw [hcard, hK.card_A])
  refine h.elemNine_of_map hRbar ?_ (by rw [hcard]; norm_num)
  rw [← hAR]
  exact hK.elem

theorem _root_.CFSG.AGLEmbeddingD2.D2Escape.elemNine_of_abelian (h : D2Escape 3 P M A H R)
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hRbar : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) =
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
    (hK : D2AlmostSimple 3 (H ⧸ primeComplementCore (G := H) 3) Rbar
      ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) K)
    (hK4 : (∀ x ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
        ∀ y ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)), x * y = y * x) →
      (∃ E : Subgroup (H ⧸ primeComplementCore (G := H) 3),
        E ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ∧
        IsElemAbelian 3 E ∧ Nat.card E = 9) →
      IsElemAbelian 3 (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ∧
        Nat.card (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) = 9)
    (hcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) :
    IsElemAbelian 3 R ∧ Nat.card R = 9 := by
  have hcommbar : ∀ x ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
      ∀ y ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)), x * y = y * x := by
    intro x hx y hy
    rw [hRbar] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (hcomm a (Subgroup.mem_subgroupOf.mp ha) b
      (Subgroup.mem_subgroupOf.mp hb)))
  obtain ⟨hel, hcard⟩ := hK4 hcommbar ⟨_, hK.A_le, hK.elem, by rw [hK.card_A]; norm_num⟩
  exact h.elemNine_of_map hRbar hel hcard

end CFSG.LocalAnalysis.RankThreeTheoremC
