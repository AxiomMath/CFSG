module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiFamilies
import all CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_11_15
public import Certificates.Certificate43
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open scoped Pointwise

theorem hall_sylow_map_subtype {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) (hA : Nat.Coprime (Nat.card A) A.index)
    (p : ℕ) [Fact p.Prime] (hpA : p ∣ Nat.card A) (P : Sylow p A) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = (P : Subgroup A).map A.subtype := by
  have hpIndex : ¬ p ∣ A.index := by
    intro hp
    exact (Fact.out : p.Prime).ne_one (Nat.eq_one_of_dvd_coprimes hA hpA hp)
  have hmapIndex : ¬ p ∣ ((P : Subgroup A).map A.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact (Fact.out : p.Prime).not_dvd_mul P.not_dvd_index hpIndex
  exact ⟨(P.isPGroup'.map A.subtype).toSylow hmapIndex, IsPGroup.toSylow_coe _ _⟩

theorem whole_centralizer_conjugate_of_card_not_coprime
    {G : Type*} [Group G] [Finite G] (A B : Subgroup G)
    (hA : ∀ x : G, x ∈ A → x ≠ 1 → Subgroup.centralizer ({x} : Set G) = A)
    (hB : ∀ x : G, x ∈ B → x ≠ 1 → Subgroup.centralizer ({x} : Set G) = B)
    (hcop : ¬ Nat.Coprime (Nat.card A) (Nat.card B)) :
    ∃ g : G, A = B.map (MulAut.conj g).toMonoidHom := by
  classical
  obtain ⟨p, hp, hpA, hpB⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  let : Fact p.Prime := ⟨hp⟩
  let P : Sylow p A := Classical.choice inferInstance
  let Q : Sylow p B := Classical.choice inferInstance
  obtain ⟨PA, hPA⟩ := hall_sylow_map_subtype A
    (xi1115_centralizer_card_coprime_index_core A hA) p hpA P
  obtain ⟨QB, hQB⟩ := hall_sylow_map_subtype B
    (xi1115_centralizer_card_coprime_index_core B hB) p hpB Q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G QB PA
  have hPne : (P : Subgroup A) ≠ ⊥ := P.ne_bot_of_dvd_card hpA
  obtain ⟨x, hxP, hxbot⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.mpr hPne)
  have hx1 : x ≠ 1 := by simpa only [Subgroup.mem_bot] using hxbot
  have hxG1 : (x : G) ≠ 1 := by intro h; exact hx1 (Subtype.ext h)
  have hxPA : (x : G) ∈ (PA : Subgroup G) := by
    rw [hPA]
    exact ⟨x, hxP, rfl⟩
  have hxConj : (x : G) ∈ ((Q : Subgroup B).map B.subtype).map
      (MulAut.conj g).toMonoidHom := by
    rw [← hQB]
    change (x : G) ∈ (MulAut.conj g) • (QB : Subgroup G)
    rw [← Sylow.coe_subgroup_smul, hg]
    exact hxPA
  obtain ⟨y, ⟨b, hbQ, hby⟩, hyx⟩ := hxConj
  have hb1 : (b : G) ≠ 1 := by
    intro hb
    apply hxG1
    calc
      (x : G) = (MulAut.conj g) y := hyx.symm
      _ = (MulAut.conj g) (b : G) := congrArg (MulAut.conj g) hby.symm
      _ = 1 := by rw [hb, map_one]
  have hxb : (x : G) = g * (b : G) * g⁻¹ := by
    rw [← hyx, ← hby]
    rfl
  refine ⟨g, ?_⟩
  calc
    A = Subgroup.centralizer ({(x : G)} : Set G) := (hA x x.property hxG1).symm
    _ = Subgroup.centralizer ({g * (b : G) * g⁻¹} : Set G) := by rw [hxb]
    _ = (Subgroup.centralizer ({(b : G)} : Set G)).map (MulAut.conj g).toMonoidHom :=
      xi1115_centralizer_conj_eq (b : G) g
    _ = B.map (MulAut.conj g).toMonoidHom := by rw [hB (b : G) b.property hb1]

theorem suzuki_derangement_distinct_family_coprime (m : ℕ) (hm : 0 < m)
    (c d : suzukiDerangementCentralizerClasses m) (hcd : c ≠ d) :
    Nat.Coprime (Nat.card (suzukiDerangementCentralizerRepresentative m c).val)
      (Nat.card (suzukiDerangementCentralizerRepresentative m d).val) := by
  by_contra hcop
  let A := suzukiDerangementCentralizerRepresentative m c
  let B := suzukiDerangementCentralizerRepresentative m d
  obtain ⟨g, hg⟩ := whole_centralizer_conjugate_of_card_not_coprime A.val B.val
    (suzuki_derangement_family_centralizer_exact m hm A)
    (suzuki_derangement_family_centralizer_exact m hm B) hcop
  apply hcd
  exact (Quotient.out_eq c).symm.trans
    (suzuki_derangement_conjugate_family_class m d A ⟨g, hg⟩)

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
