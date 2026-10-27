module

public import Certificates.Certificate9415

public section

open CFSG.Quasithin CFSG.Open

namespace CFSG.AGLEmbedding.D4Two

theorem bfsElems_forall {P : Array GF8 → Prop} {A B : Array GF8} (hone : P oneArr)
    (hA : ∀ x, P x → P (mulArr x A)) (hB : ∀ x, P x → P (mulArr x B))
    (par : List (ℕ × Bool)) : ∀ x ∈ bfsElems A B par, P x := by
  unfold bfsElems
  suffices h : ∀ (par : List (ℕ × Bool)) (acc : List (Array GF8)), (∀ x ∈ acc, P x) →
      ∀ x ∈ par.foldl (bfsStep A B) acc, P x from h par [oneArr] (by simpa using hone)
  intro par
  induction par with
  | nil => intro acc hacc; simpa using hacc
  | cons p par ih =>
    intro acc hacc
    refine ih _ ?_
    intro x hx
    simp only [bfsStep, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hacc x hx
    · have h1 : P (acc.getD p.1 oneArr) := by
        by_cases hi : p.1 < acc.length
        · rw [List.getD_eq_getElem _ _ hi]; exact hacc _ (List.getElem_mem hi)
        · rw [List.getD_eq_default _ _ (by omega)]; exact hone
      cases hp : p.2
      · simpa using hB _ h1
      · simpa using hA _ h1

theorem oneArr_mem_bfsElems (A B : Array GF8) (par : List (ℕ × Bool)) :
    oneArr ∈ bfsElems A B par := by
  unfold bfsElems
  suffices h : ∀ (par : List (ℕ × Bool)) (acc : List (Array GF8)), oneArr ∈ acc →
      oneArr ∈ par.foldl (bfsStep A B) acc from h par [oneArr] (by simp)
  intro par
  induction par with
  | nil => intro acc h; simpa using h
  | cons p par ih =>
    intro acc h
    exact ih _ (by simp [bfsStep, h])

theorem size_of_mem_bfsElems (A B : Array GF8) (par : List (ℕ × Bool)) :
    ∀ x ∈ bfsElems A B par, x.size = 64 :=
  bfsElems_forall (P := fun x => x.size = 64) size_oneArr (fun _ _ => size_mulArr _ _)
    (fun _ _ => size_mulArr _ _) par

theorem size_sylowElems : ∀ x ∈ sylowElems, x.size = 64 :=
  size_of_mem_bfsElems genA genB bfsPar

theorem sylowGroup_le : sylowGroup ≤ trialityGroup8 := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro g (rfl | rfl)
  · exact wordGL_mem _
  · exact wordGL_mem _

theorem coe_wordGL_A : ((wordGL wordA : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
    toMat genA := coe_wordGL wordA

theorem coe_wordGL_B : ((wordGL wordB : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
    toMat genB := coe_wordGL wordB

theorem exists_mem_of_mem_sylowElems : ∀ x ∈ sylowElems, ∃ g ∈ sylowGroup,
    ((g : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat x := by
  refine bfsElems_forall (P := fun x => ∃ g ∈ sylowGroup,
    ((g : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat x) ?_ ?_ ?_ bfsPar
  · exact ⟨1, one_mem _, by rw [oneArr, toMat_ofMat]; rfl⟩
  · rintro x ⟨g, hg, hgx⟩
    refine ⟨g * wordGL wordA, mul_mem hg (Subgroup.subset_closure (by simp)), ?_⟩
    rw [Units.val_mul, hgx, coe_wordGL_A, toMat_mulArr]
  · rintro x ⟨g, hg, hgx⟩
    refine ⟨g * wordGL wordB, mul_mem hg (Subgroup.subset_closure (by simp)), ?_⟩
    rw [Units.val_mul, hgx, coe_wordGL_B, toMat_mulArr]

theorem cube1_of {a : Array GF8} (g : GL (Fin 8) GF8)
    (hga : (g : Matrix (Fin 8) (Fin 8) GF8) = toMat a) (h3 : g ^ 3 = 1) : cube1 a = true := by
  unfold cube1
  rw [beq_iff_eq]
  apply eq_of_toMat_eq (size_mulArr _ _) size_oneArr
  rw [toMat_mulArr, toMat_mulArr, oneArr, toMat_ofMat, ← hga, ← mul_assoc]
  have := congrArg (fun g : GL (Fin 8) GF8 => (g : Matrix (Fin 8) (Fin 8) GF8)) h3
  simpa [pow_three'] using this

theorem commutes_of {a b : Array GF8} (g h : GL (Fin 8) GF8)
    (hga : (g : Matrix (Fin 8) (Fin 8) GF8) = toMat a)
    (hhb : (h : Matrix (Fin 8) (Fin 8) GF8) = toMat b) (hgh : g * h = h * g) :
    commutes a b = true := by
  unfold commutes
  rw [beq_iff_eq]
  apply eq_of_toMat_eq (size_mulArr _ _) (size_mulArr _ _)
  rw [toMat_mulArr, toMat_mulArr, ← hga, ← hhb, ← Units.val_mul, ← Units.val_mul, hgh]

theorem toMat_mem_pows {a : Array GF8} {g : GL (Fin 8) GF8}
    (hga : (g : Matrix (Fin 8) (Fin 8) GF8) = toMat a) :
    ∀ u ∈ [oneArr, a, mulArr a a], ∃ i : Fin 3,
      toMat u = ((g ^ (i : ℕ) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) := by
  intro u hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact ⟨0, by rw [oneArr, toMat_ofMat]; simp⟩
  · exact ⟨1, by simp [hga]⟩
  · exact ⟨2, by rw [toMat_mulArr, ← hga]; simp [pow_two]⟩

theorem sylowGroup_facts :
    sylowGroup ≤ trialityGroup8 ∧ Nat.card sylowGroup = 3 ^ 4 ∧
      ∀ E : Subgroup (GL (Fin 8) GF8), E ≤ sylowGroup → IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2 :=
  ⟨sylowGroup_le, by rw [Certificates.certificate9415.1]; norm_num,
    fun E hE hEA => Certificates.certificate9415.2.1 E hE hEA⟩

theorem exists_sylowElems_eq (g : GL (Fin 8) GF8)
    (hg : g ∈ sylowGroup) :
    ∃ x ∈ sylowElems, ((g : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat x :=
  Certificates.certificate9415.2.2 g hg

end CFSG.AGLEmbedding.D4Two
