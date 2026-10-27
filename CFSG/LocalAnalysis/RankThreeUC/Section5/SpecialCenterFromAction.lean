module

public import CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow
public import CFSG.LocalAnalysis.RankThreeUC.Section5.AbelianCentrality

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.SpecialCenterFromAction

open CFSG.LocalAnalysis.RankThreeUC.Section5

variable {G : Type} [Group G] [Finite G]

private theorem conj_mem_of_char {X : Type} [Group X] {S U : Subgroup X} (hUS : U ≤ S)
    (hc : (U.subgroupOf S).Characteristic) {b : X} (hb : b ∈ Subgroup.normalizer (S : Set X))
    {u : X} (hu : u ∈ U) : b * u * b⁻¹ ∈ U := by
  have hbS : ∀ s, s ∈ S → b * s * b⁻¹ ∈ S := fun s hs =>
    ((Subgroup.mem_normalizer_iff.mp hb) s).mp hs
  let φ : S ≃* S :=
    { toFun := fun s => ⟨b * s * b⁻¹, hbS s s.2⟩
      invFun := fun s => ⟨b⁻¹ * s * b, by
        have := ((Subgroup.mem_normalizer_iff.mp (inv_mem hb)) s.1).mp s.2
        simpa using this⟩
      left_inv := fun s => by ext; simp [mul_assoc]
      right_inv := fun s => by ext; simp [mul_assoc]
      map_mul' := fun x y => by ext; simp [mul_assoc] }
  have h1 : Subgroup.comap φ.toMonoidHom (U.subgroupOf S) = U.subgroupOf S := hc.fixed φ
  have : (⟨u, hUS hu⟩ : S) ∈ Subgroup.comap φ.toMonoidHom (U.subgroupOf S) := by
    rw [h1]; exact hu
  exact this

theorem special_and_center {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) (hpi : p ∉ piOf B) :
    CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.IsSpecialPGroup (Sstar P T B) ∧
      (Subgroup.center (Sstar P T B)).map (Sstar P T B).subtype =
        Sstar P T B ⊓ Subgroup.centralizer (Bstar P B : Set (MulAut ↥P)) := by
  haveI : Fact p.Prime := ⟨h.oddPrimeClassTwoAction.setting.prime⟩
  haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨h.oddPrimeClassTwoAction.setting.class_le_two⟩
  haveI : Fact (Monoid.exponent ↥P = p) := ⟨h.oddPrimeClassTwoAction.setting.exponent⟩
  have hodd := SstarCoprimeStructure.odd_card h
  have hcop : Nat.Coprime 2 (Nat.card (Bstar P B)) :=
    (Nat.coprime_two_left).mpr hodd
  rcases CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.exists_characteristic_abelian_not_centralized_or_special_center_eq_centralizer 2 Nat.prime_two (Sstar P T B) (Bstar P B)
    (SstarQuotientFaithful.isPGroup h) (SstarCoprimeStructure.nontrivial h) hcop
    (SstarCoprimeStructure.normalizes h) (SstarCoprimeStructure.generated h) with
    ⟨U, hUS, _, hcomm, hnc⟩ | hres
  · exfalso
    have hN := SstarCoprimeStructure.normalizes h
    have hSn : ∀ b ∈ Bstar P B, b ∈ Subgroup.normalizer (Sstar P T B : Set (MulAut ↥P)) :=
      fun b hb => hN hb
    refine hnc (AbelianCentrality.centralizes h hpi U hUS ?_ )
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hb' : b⁻¹ ∈ Bstar P B := inv_mem hb
    constructor
    · exact fun hx => conj_mem_of_char hUS ‹_› (hSn b hb) hx
    · intro hx
      have := conj_mem_of_char hUS ‹_› (hSn b⁻¹ hb') hx
      simpa [mul_assoc] using this
  · exact hres

end CFSG.LocalAnalysis.RankThreeUC.Section5.SpecialCenterFromAction
