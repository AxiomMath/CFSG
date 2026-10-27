module

public import CFSG.LieType.Chevalley.RootOps.Instance
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

theorem conjRange_trans {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (h₁ : conjRange τ a b = true)
    (h₂ : conjRange τ b c = true) : conjRange τ a c = true := by
  simp only [conjRange, List.all_eq_true, List.mem_range'] at h₁ h₂ ⊢
  rintro x ⟨m, hm, rfl⟩
  by_cases hx : a + m < b
  · exact h₁ _ ⟨m, by omega, rfl⟩
  · exact h₂ _ ⟨a + m - b, by omega, by omega⟩

@[expose] def simpleRow (τ : Tag) (j : Fin τ.rank) : Bool :=
  [1, 2, 3].all fun k => simpleCheck τ j k && negSimpleCheck τ j k

theorem simpleRow_spec {j : Fin τ.rank} (h : simpleRow τ j = true) {k : ℕ} (h1 : 1 ≤ k)
    (h3 : k ≤ 3) : simpleCheck τ j k = true ∧ negSimpleCheck τ j k = true := by
  simp only [simpleRow, List.all_eq_true, Bool.and_eq_true] at h
  exact h k (mem_one_two_three h1 h3)

theorem dataChecks_of (htab : tabCheck τ = true) (hvalid : allValid τ = true)
    (hconj : conjRange τ 0 τ.rootCertificate.roots.length = true)
    (hsimple : ∀ j, simpleRow τ j = true) : DataChecks τ where
  tab := htab
  valid := hvalid
  conj a ha i _ hk := conjRange_spec hconj (Nat.zero_le a) ha i hk
  simple _ _ j _ h1 h3 := entriesOp_eq_xCoeff (simpleRow_spec (hsimple j) h1 h3).1
  negSimple _ _ j _ h1 h3 := entriesOp_eq_yCoeff (simpleRow_spec (hsimple j) h1 h3).2

end CFSG.LieType.Chevalley.RootOps
