module

public import CFSG.Blueprint.ChevalleyStringsInputs
public import Certificates.Certificate114

public import CFSG.Blueprint.ChevalleyRoots
public import Certificates.Certificate113

public section

namespace CFSG.Blueprint.Chevalley

namespace StringData

variable {τ : Tag} (S : StringData τ) (C : RootCertificate τ)

variable {S C}

end StringData

namespace StringData

variable {τ : Tag} {S : StringData τ} {C : RootCertificate τ}

end StringData

theorem g2StringData_check : g2StringData.check g2Certificate = true := by
  exact Certificates.certificate114.1

theorem f4StringData_check : f4StringData.check f4Certificate = true := by
  exact Certificates.certificate114.2.1

theorem d4StringData_check : d4StringData.check d4Certificate = true := by
  exact Certificates.certificate114.2.2.1

theorem e6StringData_check : e6StringData.check e6Certificate = true := by
  exact Certificates.certificate114.2.2.2.1

theorem e7StringData_check : e7StringData.check e7Certificate = true := by
  exact Certificates.certificate114.2.2.2.2.1

theorem e8StringData_check : e8StringData.check e8Certificate = true := by
  exact Certificates.certificate114.2.2.2.2.2

theorem Tag.stringData_check : ∀ τ : Tag, τ.stringData.check τ.rootCertificate = true
  | .G2 => g2StringData_check
  | .F4 => f4StringData_check
  | .D4 => d4StringData_check
  | .E6 => e6StringData_check
  | .E7 => e7StringData_check
  | .E8 => e8StringData_check

theorem exists_string_interval {τ : Tag} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (i : Fin τ.rank)
    (hne : α ≠ Pi.single i 1) (hne' : α ≠ -Pi.single i 1) :
    ∃ p q : ℕ, p + q ≤ 3 ∧ ∀ m : ℤ, IsRoot τ (α + m • Pi.single i 1) ↔ -(q : ℤ) ≤ m ∧ m ≤ p := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hα
  exact ⟨_, _, StringData.isRoot_root_add_iff τ.rootCertificate_check τ.stringData_check hk i
    hne hne'⟩

theorem isRoot_add_smul_single_iff {τ : Tag} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (i : Fin τ.rank) (hne : α ≠ Pi.single i 1) (hne' : α ≠ -Pi.single i 1) :
    stringUp τ i α + stringDown τ i α ≤ 3 ∧ ∀ m : ℤ,
      IsRoot τ (α + m • Pi.single i 1) ↔
        -(stringDown τ i α : ℤ) ≤ m ∧ m ≤ stringUp τ i α := by
  obtain ⟨p, q, hpq, h⟩ := exists_string_interval hα i hne hne'
  have hup : stringUp τ i α = p := by
    have : {k : ℕ | IsRoot τ (α + (k : ℤ) • Pi.single i 1)} = {k : ℕ | k ≤ p} := by
      ext k
      simp only [Set.mem_ofPred_eq, h]
      omega
    rw [stringUp, this, sSup_setOf_le]
  have hdown : stringDown τ i α = q := by
    have : {k : ℕ | IsRoot τ (α - (k : ℤ) • Pi.single i 1)} = {k : ℕ | k ≤ q} := by
      ext k
      simp only [Set.mem_ofPred_eq, sub_eq_add_neg, ← neg_smul, h]
      omega
    rw [stringDown, this, sSup_setOf_le]
  rw [hup, hdown]
  exact ⟨hpq, h⟩

theorem root_string_transport {τ : Tag} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (i : Fin τ.rank)
    (hne : α ≠ Pi.single i 1) (hne' : α ≠ -Pi.single i 1) :
    (∀ m : ℤ, IsRoot τ (α + m • Pi.single i 1) ↔
        -(stringDown τ i α : ℤ) ≤ m ∧ m ≤ stringUp τ i α) ∧
      stringUp τ i α + stringDown τ i α ≤ 3 ∧
      ∀ k : ℤ, -(stringDown τ i α : ℤ) ≤ k → k ≤ stringUp τ i α →
        IsRoot τ (α + k • Pi.single i 1) ∧ α + k • Pi.single i 1 ≠ Pi.single i 1 ∧
          α + k • Pi.single i 1 ≠ -Pi.single i 1 ∧
          (stringUp τ i (α + k • Pi.single i 1) : ℤ) = stringUp τ i α - k ∧
          (stringDown τ i (α + k • Pi.single i 1) : ℤ) = stringDown τ i α + k := by
  obtain ⟨hpq, h⟩ := isRoot_add_smul_single_iff hα i hne hne'
  refine ⟨h, hpq, fun k hk1 hk2 => ?_⟩
  have hβ : IsRoot τ (α + k • Pi.single i 1) := (h k).2 ⟨hk1, hk2⟩
  have hneβ : ∀ s : ℤ, s = 1 ∨ s = -1 → α + k • Pi.single i 1 ≠ s • Pi.single i 1 := by
    intro s _ heq
    have hαs : α = (s - k) • Pi.single i 1 := by rw [sub_smul, ← heq]; abel
    rcases hα.eq_one_or_neg_one_of_eq_smul hαs with h1 | h1
    · exact hne (by rw [hαs, h1, one_smul])
    · exact hne' (by rw [hαs, h1, neg_one_smul])
  have hβ1 : α + k • Pi.single i 1 ≠ Pi.single i 1 := by simpa using hneβ 1 (Or.inl rfl)
  have hβ2 : α + k • Pi.single i 1 ≠ -Pi.single i 1 := by simpa using hneβ (-1) (Or.inr rfl)
  obtain ⟨-, hβs⟩ := isRoot_add_smul_single_iff hβ i hβ1 hβ2
  have key : ∀ m : ℤ, -(stringDown τ i (α + k • Pi.single i 1) : ℤ) ≤ m ∧
      m ≤ stringUp τ i (α + k • Pi.single i 1) ↔
        -(stringDown τ i α : ℤ) ≤ k + m ∧ k + m ≤ stringUp τ i α := by
    intro m
    rw [← hβs m, ← h (k + m), add_smul, add_assoc]
  refine ⟨hβ, hβ1, hβ2, ?_, ?_⟩
  · have h1 := (key (stringUp τ i (α + k • Pi.single i 1))).1 ⟨by omega, le_rfl⟩
    have h2 := (key (stringUp τ i α - k)).2 ⟨by omega, by omega⟩
    omega
  · have h1 := (key (-(stringDown τ i (α + k • Pi.single i 1) : ℤ))).1 ⟨le_rfl, by omega⟩
    have h2 := (key (-(stringDown τ i α : ℤ) - k)).2 ⟨by omega, by omega⟩
    omega

theorem root_string_reflection {τ : Tag} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (i : Fin τ.rank) :
    (∑ j, τ.cartan i j * α j) = (stringDown τ i α : ℤ) - stringUp τ i α ∧
      reflect τ i α = α + ((stringUp τ i α : ℤ) - stringDown τ i α) • Pi.single i 1 ∧
      stringUp τ i (reflect τ i α) = stringDown τ i α ∧
      stringDown τ i (reflect τ i α) = stringUp τ i α := by
  have hm : ∀ m' : ℤ, (∑ j, τ.cartan i j * α j) = m' →
      reflect τ i α = α + (-m') • Pi.single i 1 := by
    intro m' hm'
    have := reflect_add_smul_single τ i α 0
    rw [zero_smul, add_zero, add_zero, hm'] at this
    rw [this, sub_eq_add_neg, neg_smul]
  by_cases h1 : α = Pi.single i 1
  · subst h1
    have hsum := sum_cartan_mul_single τ i
    rw [reflect_single_self, stringUp_single, stringDown_single, stringUp_neg_single,
      stringDown_neg_single, hsum]
    refine ⟨by norm_num, ?_, rfl, rfl⟩
    ext j
    simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  by_cases h2 : α = -Pi.single i 1
  · subst h2
    have hsum : (∑ j, τ.cartan i j * (-Pi.single i 1 : Fin τ.rank → ℤ) j) = -2 := by
      simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, sum_cartan_mul_single]
    have hr : reflect τ i (-Pi.single i 1) = Pi.single i 1 := by
      rw [← reflect_single_self, reflect_reflect]
    rw [hr, stringUp_single, stringDown_single, stringUp_neg_single, stringDown_neg_single, hsum]
    refine ⟨by norm_num, ?_, rfl, rfl⟩
    ext j
    simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  obtain ⟨hint, -, htr⟩ := root_string_transport hα i h1 h2
  set m := ∑ j, τ.cartan i j * α j with hmdef
  set p := stringUp τ i α
  set q := stringDown τ i α
  have hrefl : ∀ k : ℤ, IsRoot τ (α + k • Pi.single i 1) ↔
      IsRoot τ (α + (-(m + k)) • Pi.single i 1) := by
    intro k
    rw [← isRoot_reflect_iff i, reflect_add_smul_single, ← hmdef, sub_eq_add_neg, neg_smul]
  have hp := (hrefl p).1 ((hint p).2 ⟨by omega, le_rfl⟩)
  have hq := (hrefl (-q)).1 ((hint (-q)).2 ⟨le_rfl, by omega⟩)
  rw [hint] at hp hq
  have hmpq : m = (q : ℤ) - p := by omega
  have hreflα : reflect τ i α = α + ((p : ℤ) - q) • Pi.single i 1 := by
    rw [hm m rfl, hmpq]
    congr 2
    ring
  obtain ⟨-, -, -, hu, hd⟩ := htr ((p : ℤ) - q) (by omega) (by omega)
  refine ⟨hmpq, hreflα, ?_, ?_⟩
  · rw [hreflα]
    omega
  · rw [hreflα]
    omega

end CFSG.Blueprint.Chevalley
