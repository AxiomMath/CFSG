module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Close
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma83
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma85

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Timmesfeld.Coordinator
open scoped commutatorElement

namespace S8

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem lie_characteristic_prime (d : TauCeti.LieTypeIndex) : d.characteristic.Prime := by
  cases d with
  | A _ q => simpa using q.prime_p
  | twistedA _ q => simpa using q.prime_p
  | B _ q => simpa using q.prime_p
  | C _ q => simpa using q.prime_p
  | D _ q => simpa using q.prime_p
  | twistedD _ q => simpa using q.prime_p
  | E6 q => simpa using q.prime_p
  | E7 q => simpa using q.prime_p
  | E8 q => simpa using q.prime_p
  | F4 q => simpa using q.prime_p
  | G2 q => simpa using q.prime_p
  | twistedE6 q => simpa using q.prime_p
  | trialityD4 q => simpa using q.prime_p
  | suzuki _ => simpa using Nat.prime_two
  | reeG2 _ => simpa using Nat.prime_three
  | reeF4 _ => simpa using Nat.prime_two
  | tits => simpa using Nat.prime_two

theorem not_sporadic (hc : S8Ctx G p) (hOut : SporadicOuterLeTwo) (h66 : I66At) (h1017 : I1017At G p)
    (h1016 : I1016RowAt G p) (h301 : I301AAt G p) (hTim : TimmesfeldAt) (hNo5 : No5PumpupAt) (in83 : Inputs83 G p)
    (in84 : Inputs84 G p) (in8910 : Inputs8910 G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) : ¬ catalogIs (PSimple p L) isSporIndex := by
  intro hsp
  have h82 := lemma82 hc hOut h66 h hsp
  have h83 := lemma83 hc in83 h h82
  have h84 := lemma84 hc in84 h h82
  obtain ⟨row, hrow, E, hEL, hE, hbig⟩ := lemma85 hc h1017 h82 hsp h83 h84
  have hodd := lemma86 hc h82 hEL hE hbig
  have hx : orderOf x = p :=
    orderOf_eq_of_isElemAbelian hc.ctx.prime h82.hB.1 h82.hxB h82.hx1
  obtain ⟨cfg⟩ := lemma87 hc h1016 h301 h82 hrow hodd
  by_cases h5 : row = Row.m5
  · subst h5
    have hp5 : p = 5 := hrow.1
    subst hp5
    exact cfg_five hc in8910 hTim hNo5 hx h82.hL (normalizer_of_unique h82.hL h82.huniq) hrow hodd cfg
  · have hp3 : p = 3 := by
      have := hrow.1
      cases row <;> simp_all [Row.prime]
    subst hp3
    exact cfg_three hc in8910 hx h82.hL hrow hodd cfg

theorem prop81 (hc : S8Ctx G p) (hOut : SporadicOuterLeTwo) (h66 : I66At) (h1017 : I1017At G p)
    (h1016 : I1016RowAt G p) (h301 : I301AAt G p) (hTim : TimmesfeldAt) (hNo5 : No5PumpupAt) (in83 : Inputs83 G p)
    (in84 : Inputs84 G p) (in8910 : Inputs8910 G p) :
    ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax p B x L →
      IsChevSimple 2 (PSimple p L) := by
  intro B x L h
  obtain ⟨-, -, hx1, hL, -⟩ := sStarFacts hc h
  obtain ⟨-, hna, i, ⟨e⟩⟩ := catalog_of_component hc.ctx hx1 hL
  cases i with
  | cyclic q hq =>
    exfalso
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm (G := Multiplicative (ZMod q)) _ _
  | alternating n hn => exact absurd ⟨.alternating n hn, trivial, ⟨e⟩⟩ (hc.stage7 B x L h)
  | sporadic s =>
    exact absurd ⟨.sporadic s, trivial, ⟨e⟩⟩
      (not_sporadic hc hOut h66 h1017 h1016 h301 hTim hNo5 in83 in84 in8910 h)
  | lie d =>
    by_cases hch : d.1.characteristic = 2
    · exact Or.inl ⟨.lie d, hch, ⟨e⟩⟩
    · exact absurd (Or.inl ⟨.lie d, rfl, ⟨e⟩⟩)
        (hc.stage6 B x L h d.1.characteristic (lie_characteristic_prime d.1) hch)

end S8

end CFSG.LocalAnalysis.GLTheoremA
