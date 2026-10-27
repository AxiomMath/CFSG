module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sec
public import CFSG.GH74.GLS.IVK.Defs
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Cases
import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1

open CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.KGroups.L3Eps
open scoped MatrixGroups

theorem isSection_L2_sl2 (F : Type) [Field F] : IsSection (IVK.L2 F) SL(2, F) := by
  refine IsSection.of_equiv (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F) ?_
  refine ⟨⊤, (IVK.L2.mk F).comp (⊤ : Subgroup (IVK.SL2 F)).subtype, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
  exact ⟨⟨x, trivial⟩, rfl⟩

theorem isSection_centralizer_singleton_of_mulEquiv {G H Z : Type} [Group G] [Group H] [Group Z]
    (e : G ≃* H) (t : G) (h : IsSection Z ↥(Subgroup.centralizer ({e t} : Set H))) :
    IsSection Z ↥(Subgroup.centralizer ({t} : Set G)) := by
  refine IsSection.of_surjective
    ((e.toMonoidHom.comp (Subgroup.centralizer ({t} : Set G)).subtype).codRestrict
      (Subgroup.centralizer ({e t} : Set H)) ?_) ?_ h
  · rintro ⟨x, hx⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    show e x ∈ Subgroup.centralizer ({e t} : Set H)
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hx]
  · intro y
    refine ⟨⟨e.symm y, ?_⟩, Subtype.ext (by simp)⟩
    have hy := Subgroup.mem_centralizer_singleton_iff.1 y.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy

private theorem two_ne_zero_of_odd_card' {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  classical
  let _ : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by
    intro h
    have he := FiniteField.even_card_of_char_two h
    have ho : Fintype.card F % 2 = 1 := by
      simpa only [← Nat.card_eq_fintype_card] using Nat.odd_iff.mp hF
    omega
  intro hzero
  exact hchar (CharP.ringChar_of_prime_eq_zero Nat.prime_two hzero)

theorem fl3_L2_section {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime) (_hf : 1 ≤ f)
    (hp2 : p ≠ 2) (hLie : LieModel Y .PSL 3 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      ∀ t : Y, orderOf t = 2 →
        Odd87.IsSection (IVK.L2 F) ↥(Subgroup.centralizer ({t} : Set Y)) := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hLie
  refine ⟨F, hF, hFin, hcard, fun t ht => ?_⟩
  have hodd : Odd (Nat.card F) := hcard ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card' hodd
  have htt : t * t = 1 := by
    rw [← sq, ← ht]
    exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  obtain ⟨e', he'⟩ := exists_equiv_tInv h2 e htt ht1
  refine isSection_centralizer_singleton_of_mulEquiv e' t ?_
  rw [he']
  refine IsSection.of_le_le blockSub_le_centralizer ?_
  exact IsSection.of_equiv (MonoidHom.ofInjective (blockEmb_injective (F := F))).symm
    (isSection_L2_sl2 F)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1
