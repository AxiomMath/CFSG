module

public import Certificates.Certificate101707
public import CFSG.Sporadic.Co2I301.Spec
public import CFSG.Sporadic.Co2I301.SpecSixAux

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H301B.Co2Six

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert
  CFSG.Sporadic.Co2Schreier CFSG.Certificates.Native CFSG.HardMathSupport.Dickson.I271
  CFSG.Sporadic.Co2I301 CFSG.LocalAnalysis.GLTheoremA.H301B.Co2RowNative

section Image


theorem toPerm63_sixAction_mem_closure (c : locC) :
    toPerm63 (sixAction c) ∈ Subgroup.closure {π | ∃ i < 2, sixPi i = π} := by
  have h : sixAction c ∈ sixAction.range := ⟨c, rfl⟩
  rw [sixAction_range] at h
  have h2 := Subgroup.mem_map_of_mem toPerm63 h
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
  exact ⟨i, hi, (toPerm63_sixAction_cGen hi).symm⟩

end Image

section Search


private def sixBaseFin : List (Fin 63) := [0, 1, 3, 7, 15, 31]

private theorem sixRec_baseArr : sixRec.baseArr = (sixBaseFin.map Fin.val).toArray := by
  rw [baseArr_eq]
  change witRec.wLocal.sixActionChain.base.toArray = _
  rw [sixChain_shape.base_eq]
  rfl

theorem six_x0_facts (c₁ c₂ c₃ : locC) (h₁ : (c₁ : Equiv.Perm (Fin 2300)) = k1P)
    (h₂ : (c₂ : Equiv.Perm (Fin 2300)) = k2P)
    (h₃ : (c₃ : Equiv.Perm (Fin 2300)) = CFSG.Sporadic.Co2I301.dP) :
    (c₁ * c₂) ^ 5 = 1 ∧ ∀ c : locC, c ^ 3 = 1 → toPerm63 (sixAction c) ≠ 1 →
      Commute (toPerm63 (sixAction c)) (toPerm63 (sixAction (c₁ * c₂))) →
      toPerm63 (sixAction c) = toPerm63 (sixAction c₃) ∨
        toPerm63 (sixAction c) = toPerm63 (sixAction c₃) ^ 2 := by
  obtain ⟨r₁, r₂, r₃, s₁, s₂, s₃⟩ := smallCheck_six_cols
  have r₁' : Rep 2300 i301K1 (c₁ : Equiv.Perm (Fin 2300)) := by rw [h₁]; exact r₁
  have r₂' : Rep 2300 i301K2 (c₂ : Equiv.Perm (Fin 2300)) := by rw [h₂]; exact r₂
  have r₃' : Rep 2300 i301D (c₃ : Equiv.Perm (Fin 2300)) := by rw [h₃]; exact r₃
  have h := Certificates.certificate101707
  simp only [co2RowCheck, sixX0Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hpow, hchain⟩, hcn⟩, -⟩ := h
  rw [sixRec_baseArr] at hchain hcn
  obtain ⟨A, hA⟩ : ∃ A, A = toPerm63 (sixAction c₁) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = toPerm63 (sixAction c₂) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = toPerm63 (sixAction c₃) := ⟨_, rfl⟩
  have rA : Rep 63 (perm63Of i301K1) A := hA ▸ rep_perm63Of c₁ r₁' s₁
  have rB : Rep 63 (perm63Of i301K2) B := hB ▸ rep_perm63Of c₂ r₂' s₂
  have rD : Rep 63 (perm63Of i301D) D := hD ▸ rep_perm63Of c₃ r₃' s₃
  have hk : 2 ≤ sixRec.strongArrs.size := by
    change 2 ≤ witRec.wLocal.sixActionChain.strongArrs.size
    rw [sixChain_shape.strongArrs_size]
    norm_num
  have hT : ∀ {t : Array ℕ} {G : Equiv.Perm (Fin 63)}, Rep 63 t G →
      leafD3 (perm63Of i301D) t = true → (G * G * G = 1 → G ≠ 1 → G = D ∨ G = D * D) := by
    intro t G hG hleaf hG3 hG1
    have e0 : G * (G * G) = 1 := by rw [← mul_assoc]; exact hG3
    simp only [leafD3, Bool.or_eq_true, Bool.not_eq_true'] at hleaf
    rcases hleaf with ((h1 | h1) | h1) | h1
    · exfalso
      have h2 : eqA 63 (compA 63 t (compA 63 t t)) (idA 63) = true :=
        (eqA_iff (rep_compA hG (rep_compA hG hG)) rep_idA).2 e0
      rw [h2] at h1
      exact absurd h1 (by decide)
    · exact absurd ((eqA_iff hG rep_idA).1 h1) hG1
    · exact Or.inl ((eqA_iff hG rD).1 h1)
    · exact Or.inr ((eqA_iff hG (rep_compA rD rD)).1 h1)
  obtain ⟨-, -, hall⟩ := case_centNormMem2P (p := 5) (n := 63) (S := sixRec.strongArrs)
    (by norm_num) hk (bs := sixBaseFin) (by decide) (rep_sixPi (i := 0) (by norm_num))
    (rep_sixPi (i := 1) (by norm_num)) hchain (rep_compA rA rB) (Sg := ⊤)
    (Pr := fun G => G * G * G = 1 → G ≠ 1 → G = D ∨ G = D * D) (fun _ _ => Subgroup.mem_top _) hT
    hcn
  have hset : {π | ∃ i < 2, sixPi i = π} = ({sixPi 0, sixPi 1} : Set (Equiv.Perm (Fin 63))) := by
    ext π
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      interval_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, rfl⟩
      · exact ⟨1, by norm_num, rfl⟩
  refine ⟨?_, fun c hc3 hc1 hcomm => ?_⟩
  · have hx : Rep 2300 (compA 2300 i301K1 i301K2) ((c₁ * c₂ : locC) : Equiv.Perm (Fin 2300)) := by
      rw [Subgroup.coe_mul]
      exact rep_compA r₁' r₂'
    have h5 := (eqA_iff (rep_powArr hx 5) rep_idA).1 hpow
    exact Subtype.ext (by simpa using h5)
  · have hg : toPerm63 (sixAction c) ∈
        Subgroup.centralizer {A * B} ⊓ Subgroup.closure {sixPi 0, sixPi 1} := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
      · have hAB : A * B = toPerm63 (sixAction (c₁ * c₂)) := by
          rw [hA, hB, map_mul, map_mul]
        rw [hAB]
        exact hcomm.eq
      · rw [← hset]
        exact toPerm63_sixAction_mem_closure c
    have hc3' : toPerm63 (sixAction c) * toPerm63 (sixAction c) * toPerm63 (sixAction c) = 1 := by
      rw [← pow_three', ← map_pow, ← map_pow, hc3, map_one, map_one]
    rw [← hD]
    exact (hall _ hg).2 (fun l hl => absurd hl (by simp)) hc3' hc1

end Search

end CFSG.LocalAnalysis.GLTheoremA.H301B.Co2Six

end
