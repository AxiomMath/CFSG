module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309ModelSyl
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309ModelUni
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreUnits

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB
open CFSG.Open

theorem det_monEmb_monSub {C : Type} [CommGroup C] [Finite C] {a : ℕ} (hC : Nat.card C = 5 ^ a)
    {F : Type} [Field F] (e : C →* Fˣ) (m : ↥(monSub C)) :
    ((monEmb (F := F) e 5 (m : Mon C 5) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).det = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hodd : Odd (orderOf (m : Mon C 5)) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_monSub hC)) m
    rw [← Subgroup.orderOf_coe m] at hk
    rw [hk]
    exact Odd.pow (by decide)
  have h1 := monEmb_det_of_odd e (m : Mon C 5) hodd
  have h2 : monDet (m : Mon C 5) = 1 := m.2.2
  rw [h2, map_one] at h1
  have h3 := congrArg Units.val h1
  rw [Matrix.GeneralLinearGroup.val_det_apply] at h3
  exact h3

theorem sylow_statedSL {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
    (e0 : G ≃* StatedSL 5 K) (hpK : 5 ∣ Nat.card K - 1) (T : Sylow 5 G)
    (hT5 : Nat.card (T : Subgroup G) ≤ 5 ^ 5) :
    Nat.card (T : Subgroup G) = 5 ^ 5 ∧ (∀ t ∈ (T : Subgroup G), t ^ 5 = 1) ∧
      ∃ s ∈ (T : Subgroup G), ∃ t ∈ (T : Subgroup G), s * t ≠ t * s := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hC : Nat.card (unitsPPart K 5) = 5 ^ padicValNat 5 (Fintype.card K - 1) :=
    card_unitsPPart K 5
  have hKc : Fintype.card K - 1 = Nat.card K - 1 := by rw [Nat.card_eq_fintype_card]
  have ha : 1 ≤ padicValNat 5 (Fintype.card K - 1) := by
    refine one_le_padicValNat_of_dvd ?_ (by rw [hKc]; exact hpK)
    have := Fintype.one_lt_card (α := K)
    omega
  have hmem : ∀ m : ↥(monSub ↥(unitsPPart K 5)),
      monEmb (unitsPPart K 5).subtype 5 (m : Mon ↥(unitsPPart K 5) 5) ∈ StatedSL 5 K :=
    fun m => Subgroup.subset_closure (det_monEmb_monSub hC _ m)
  let ψ : ↥(monSub ↥(unitsPPart K 5)) →* G :=
    e0.symm.toMonoidHom.comp
      (((monEmb (unitsPPart K 5).subtype 5).comp (monSub ↥(unitsPPart K 5)).subtype).codRestrict
        (StatedSL 5 K) hmem)
  have hψ : Function.Injective ψ := by
    intro a b hab
    have h1 := e0.symm.injective hab
    have h2 := monEmb_injective (F := K) (unitsPPart K 5).subtype_injective 5
      (congrArg Subtype.val h1)
    exact Subtype.ext h2
  exact sylow_monSub T hT5 hC ha ψ hψ

theorem sylow_statedSU {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] {q : ℕ}
    (e0 : G ≃* StatedSU 5 q K) (hK : Nat.card K = q ^ 2) (hpq : 5 ∣ q + 1) (T : Sylow 5 G)
    (hT5 : Nat.card (T : Subgroup G) ≤ 5 ^ 5) :
    Nat.card (T : Subgroup G) = 5 ^ 5 ∧ (∀ t ∈ (T : Subgroup G), t ^ 5 = 1) ∧
      ∃ s ∈ (T : Subgroup G), ∃ t ∈ (T : Subgroup G), s * t ≠ t * s := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hq2 : 2 ≤ q := by
    have := Nat.le_of_dvd (by omega) hpq
    omega
  obtain ⟨r, f, rfl, ⟨hU⟩⟩ := exists_unitaryFieldData hK hq2
  have hF : Fintype.card K = (r ^ f) ^ 2 := by rw [Fintype.card_eq_nat_card]; exact hK
  have hC : Nat.card (unitsPPart K 5) = 5 ^ padicValNat 5 (r ^ f + 1) :=
    card_unitsPPart_of_dvd_add_one (by norm_num) hF hpq
  have ha : 1 ≤ padicValNat 5 (r ^ f + 1) := one_le_padicValNat_of_dvd (by omega) hpq
  have hnorm : ∀ u : ↥(unitsPPart K 5), hU.norm ((((unitsPPart K 5).subtype u : Kˣ)) : K) = 1 := by
    intro u
    have h1 := pow_add_one_eq_one_of_mem_unitsPPart (by norm_num) hF hpq u.2
    have h2 : ((u : Kˣ) : K) ^ (r ^ f + 1) = 1 := by
      have := congrArg Units.val h1
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
    change ((u : Kˣ) : K) * hU.bar ((u : Kˣ) : K) = 1
    rw [hU.bar_apply, ← pow_succ']
    exact h2
  have hmem : ∀ m : ↥(monSub ↥(unitsPPart K 5)),
      monEmb (unitsPPart K 5).subtype 5 (m : Mon ↥(unitsPPart K 5) 5) ∈
        StatedSU 5 (r ^ f) K := by
    intro m
    refine mem_stated_of_mem_gramSU_one hU ⟨?_, det_monEmb_monSub hC _ m⟩
    rw [monEmb_apply]
    exact mul_mem (diagHom_mem_primeFormUnitary hU fun i => hnorm _)
      (monPermGL_mem_primeFormUnitary hU _)
  let ψ : ↥(monSub ↥(unitsPPart K 5)) →* G :=
    e0.symm.toMonoidHom.comp
      (((monEmb (unitsPPart K 5).subtype 5).comp (monSub ↥(unitsPPart K 5)).subtype).codRestrict
        (StatedSU 5 (r ^ f) K) hmem)
  have hψ : Function.Injective ψ := by
    intro a b hab
    have h1 := e0.symm.injective hab
    have h2 := monEmb_injective (F := K) (unitsPPart K 5).subtype_injective 5
      (congrArg Subtype.val h1)
    exact Subtype.ext h2
  exact sylow_monSub T hT5 hC ha ψ hψ

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M
