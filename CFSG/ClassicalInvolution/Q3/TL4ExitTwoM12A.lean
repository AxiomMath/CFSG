module

public import Certificates.Certificate55112
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M12

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.M12

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.ClassicalInvolution
open CFSG.ClassicalInvolution.Q3.TL4.MF163

@[expose] def q8L {X : Type*} [Group X] (i j : X) : List X :=
  [1, i, i * i, i * i * i, j, i * j, i * i * j, i * i * i * j]

theorem q8L_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (i j : X) :
    (q8L i j).map f = q8L (f i) (f j) := by
  simp [q8L, map_mul]

theorem mem_q8L_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {i j x : X}
    (hx : x ∈ q8L i j) : f x ∈ q8L (f i) (f j) := by
  rw [← q8L_map]
  exact List.mem_map_of_mem hx

@[expose] def qL : Bool → List (Equiv.Perm (Fin 12))
  | false => quatL0 ()
  | true => quatL1 ()

theorem qL_length (b : Bool) : (qL b).length = 8 := by
  cases b <;> rfl

theorem qL_one (b : Bool) : (1 : Equiv.Perm (Fin 12)) ∈ qL b := by
  cases b <;> simp [qL, quatL0, quatL1, q8List]

theorem gens_mem : ∀ g ∈ [m12gA, m12gB], g ∈ NativeSporadic.M12 := by
  intro g hg
  rcases List.mem_pair.1 hg with rfl | rfl
  · exact m12a.2
  · exact m12b.2

theorem rep1_mem : m12Rep1 ∈ NativeSporadic.M12 := by
  rw [← m12Certificate_originalSubgroup]
  exact m12_rep_data1.1

theorem rep1_mul_self : m12Rep1 * m12Rep1 = 1 := by
  rw [← sq, ← m12_rep_data1.2.1, pow_orderOf_eq_one]

theorem rep1_ne_one : m12Rep1 ≠ 1 := by
  intro h
  have h2 := m12_rep_data1.2.1
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem rep1_inv : m12Rep1⁻¹ = m12Rep1 :=
  inv_eq_of_mul_eq_one_right rep1_mul_self

theorem mem_enum1_iff
    {g : Equiv.Perm (Fin 12)} :
    g ∈ enumerationTab m12CentQ1 ↔ g ∈ NativeSporadic.M12 ∧ g * m12Rep1 = m12Rep1 * g := by
  have h : centralizerIn m12Certificate.originalSubgroup m12Rep1 = m12CentQ1.originalSubgroup :=
    m12_cover_and_centralizers.2 (m12Rep1, m12CentQ1.originalSubgroup) (by simp)
  rw [mem_enumerationTab_iff m12CentQ1 m12_oddcore_cent1.1, ← h, mem_centralizerIn,
    m12Certificate_originalSubgroup]

section Checks

theorem qL_mul {b : Bool} {x y : Equiv.Perm (Fin 12)} (hx : x ∈ qL b) (hy : y ∈ qL b) :
    x * y ∈ qL b := by
  have h := Certificates.certificate55112.2.1
  simp only [chkClosed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  cases b
  · exact h.1.1.1 x hx y hy
  · exact h.1.1.2 x hx y hy

theorem qL_inv {b : Bool} {x : Equiv.Perm (Fin 12)} (hx : x ∈ qL b) : x⁻¹ ∈ qL b := by
  have h := Certificates.certificate55112.2.1
  simp only [chkClosed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  cases b
  · exact h.1.2 x hx
  · exact h.2 x hx

theorem q8L_mem {b : Bool} {i j x : Equiv.Perm (Fin 12)} (hi : i ∈ qL b) (hj : j ∈ qL b)
    (hx : x ∈ q8L i j) : x ∈ qL b := by
  simp only [q8L, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact qL_one b
    | assumption
    | repeat (first | apply qL_mul | assumption)

theorem qL_meet {x : Equiv.Perm (Fin 12)} (h0 : x ∈ qL false) (h1 : x ∈ qL true) :
    x = 1 ∨ x = m12Rep1 := by
  have h := Certificates.certificate55112.2.2.2.2.2.2
  simp only [chkMeet, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq] at h
  rcases h.1.1 x h0 with (h2 | h2) | h2
  · exact absurd h1 h2
  · exact Or.inl h2
  · exact Or.inr h2

theorem beta_lists : (∀ x ∈ betaL0 (), x ∈ quatL1 ()) ∧ ∀ x ∈ betaL1 (), x ∈ quatL0 () := by
  have h := Certificates.certificate55112.2.2.2.2.1
  simp only [chkBeta, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h

theorem qL_memC {b : Bool} {x : Equiv.Perm (Fin 12)} (hx : x ∈ qL b) :
    x ∈ NativeSporadic.M12 ∧ x * m12Rep1 = m12Rep1 * x := by
  have h := Certificates.certificate55112.1
  simp only [chkMemC, List.all_eq_true, decide_eq_true_eq] at h
  refine mem_enum1_iff.1 (h x (List.mem_append.2 ?_))
  cases b
  · exact Or.inl hx
  · exact Or.inr hx

theorem qL_conj {b : Bool} {g x : Equiv.Perm (Fin 12)} (hg : g ∈ NativeSporadic.M12)
    (hgc : g * m12Rep1 = m12Rep1 * g) (hx : x ∈ qL b) : g * x * g⁻¹ ∈ qL b := by
  have h := Certificates.certificate55112.2.2.2.1
  simp only [chkNorm, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  have h1 := h g (mem_enum1_iff.2 ⟨hg, hgc⟩)
  cases b
  · exact h1.1 x hx
  · exact h1.2 x hx

theorem roots_spec {x : Equiv.Perm (Fin 12)} (hx : x ∈ NativeSporadic.M12)
    (hx2 : x * x = m12Rep1) : (x ∈ qL false ∨ x ∈ qL true) ∧ ∀ y ∈ NativeSporadic.M12,
      y * y = m12Rep1 → x * y ≠ y * x →
        (x ∈ qL false ∧ y ∈ qL false) ∨ (x ∈ qL true ∧ y ∈ qL true) := by
  have hR : ∀ y ∈ NativeSporadic.M12, y * y = m12Rep1 → y ∈ m12SqRoots1 := fun y hy hy2 =>
    List.mem_filter.2 ⟨mem_enum1_iff.2 ⟨hy, by rw [← hy2, mul_assoc]⟩, by simpa using hy2⟩
  have h := Certificates.certificate55112.2.2.1
  simp only [chkRoots, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h x (hR x hx hx2)
  refine ⟨h1, fun y hy hy2 hxy => ?_⟩
  rcases h2 y (hR y hy hy2) with (h3 | h3) | h3
  · exact absurd h3 hxy
  · exact Or.inl h3
  · exact Or.inr h3

theorem qL_root {x : Equiv.Perm (Fin 12)} (hx : x ∈ NativeSporadic.M12)
    (hx2 : x * x = m12Rep1) : ∃ b, x ∈ qL b := by
  rcases (roots_spec hx hx2).1 with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

theorem qL_same {x y : Equiv.Perm (Fin 12)} (hx : x ∈ NativeSporadic.M12)
    (hx2 : x * x = m12Rep1) (hy : y ∈ NativeSporadic.M12) (hy2 : y * y = m12Rep1)
    (hxy : x * y ≠ y * x) : ∃ b, x ∈ qL b ∧ y ∈ qL b := by
  rcases (roots_spec hx hx2).2 y hy hy2 hxy with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

end Checks

theorem wit_spec : ∃ g ∈ NativeSporadic.M12, ∃ x ∈ qL true, ∃ y ∈ qL true,
    g * x * g⁻¹ ≠ 1 ∧ g * x * g⁻¹ * (g * x * g⁻¹) ≠ 1 ∧
      (∀ a ∈ qL false, g * x * g⁻¹ * a * (g * x * g⁻¹)⁻¹ ∈ qL false) ∧
        ¬ ∀ a ∈ qL false, g * y * g⁻¹ * a * (g * y * g⁻¹)⁻¹ ∈ qL false := by
  have h := Certificates.certificate55112.2.2.2.2.2.1
  simp only [chkWit, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨_, evalCodes_mem _ gens_mem wG, (quatL1 ()).getD 7 1, ?_, (quatL1 ()).getD 6 1, ?_,
    h1, h2, fun a ha => of_decide_eq_true (List.all_eq_true.1 h3 a ha), fun h5 => ?_⟩
  · simp [qL, quatL1, q8List]
  · simp [qL, quatL1, q8List]
  · have h6 : ((quatL0 ()).all fun a => decide (witV () * a * (witV ())⁻¹ ∈ quatL0 ())) = true :=
      List.all_eq_true.2 fun a ha => decide_eq_true (h5 a ha)
    rw [h6] at h4
    exact Bool.noConfusion h4

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.M12
