module

public import CFSG.GH74.E2.OuterAlpha
public import CFSG.GH74.KGroups.Checks

public section

namespace CFSG.GH74.E2

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups

variable {n : ℕ}

@[expose] def q8c2at (c : Equiv.Perm (Fin n)) (C : List (Equiv.Perm (Fin n))) : Bool :=
  C.all fun a => bif decide (a ^ 4 = 1) && decide (a ^ 2 ≠ 1) && decide (c ≠ a ^ 2) then
    C.all fun b => !(decide (b ^ 2 = a ^ 2) && decide (b * a * b⁻¹ = a⁻¹)) else true

@[expose] def q8c2free (L : List (Equiv.Perm (Fin n))) : Bool :=
  L.all fun c => bif decide (c ^ 2 = 1) && decide (c ≠ 1) then
    q8c2at c (L.filter fun g => decide (g * c = c * g)) else true

theorem q8c2free_sound (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    (h : q8c2free (elemsT Q) = true) {a b c : Equiv.Perm (Fin n)} (ha : a ∈ Q.originalSubgroup)
    (hb : b ∈ Q.originalSubgroup) (hc : c ∈ Q.originalSubgroup) (hrel : Q8C2Rel a b c) :
    False := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hrel
  have e1 := (bif_imp _ _).1 (List.all_eq_true.1 h c ((mem_elemsT Q hQ c).2 hc))
    (by simp [h5, h6])
  have e2 := List.all_eq_true.1 e1 a (by
    rw [List.mem_filter]
    exact ⟨(mem_elemsT Q hQ a).2 ha, by simpa using h8.symm⟩)
  have e3 := (bif_imp _ _).1 e2 (by simp [h1, h2, h7])
  have e4 := List.all_eq_true.1 e3 b (by
    rw [List.mem_filter]
    exact ⟨(mem_elemsT Q hQ b).2 hb, by simpa using h9.symm⟩)
  simp [h3, h4] at e4

theorem noQ8C2_mulAut_of_check {K : Type*} [Group K] (M : AutModel K (Equiv.Perm (Fin n)))
    (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) (hA : M.A = Q.originalSubgroup)
    (h : q8c2free (elemsT Q) = true) : NoQ8C2 (MulAut K) := by
  rintro ⟨a, b, c, hrel⟩
  have hrel' := hrel.map (M.A.subtype.comp M.Φ.toMonoidHom)
    (M.A.subtype_injective.comp M.Φ.injective)
  have hmem : ∀ x : MulAut K, (M.Φ x : Equiv.Perm (Fin n)) ∈ Q.originalSubgroup :=
    fun x => hA.le (M.Φ x).2
  exact q8c2free_sound Q hQ h (hmem a) (hmem b) (hmem c) hrel'

end CFSG.GH74.E2
