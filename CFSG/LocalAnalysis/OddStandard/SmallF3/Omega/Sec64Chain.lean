module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63Chain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63Om5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec64_mem_conjugate {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ha
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem sec64_plain_of_chain [Finite G] (h63 : Asc82Lemma63) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) (hHyp : Asc82Hyp62 G) {X Y : Subgroup G} (hXF : InFStar X)
    (hch : WalterChain X Y) : PlainChain X Y := by
  have hmain : ∀ {A B : Subgroup G}, InFStar A → WalterChain A B →
      PlainChain A B ∧ InFStar B := by
    intro A B hAF hch
    revert hAF
    unfold WalterChain at hch
    induction hch with
    | refl =>
        intro hAF
        exact ⟨Relation.ReflTransGen.refl, hAF⟩
    | @tail Z W _ hbc ih =>
        intro hAF
        obtain ⟨hPZ, hZF⟩ := ih hAF
        rcases hbc with hstep | hstep
        · exact ⟨hPZ.tail hstep, inFStar_of_walterArrow hS.a2 hstep hZF⟩
        · exfalso
          have hWF : InFStar W := inFStar_of_walterArrowDiag hS.a2 hstep hZF
          unfold WalterArrowDiag at hstep
          obtain ⟨x, y, -, hy, hxy, -, hWc, -, hne⟩ := hstep
          have hxCy : x ∈ centralizer ({y} : Set G) :=
            Subgroup.mem_centralizer_singleton_iff.mpr hxy
          have hne' : W ≠ CFSG.conjugate W x := by
            intro heq
            exact hne (by rw [heq.symm, sup_idem])
          exact hne' (h63 G t L hS hHyp y hy W (CFSG.conjugate W x) hWc hWF
            (hWc.conjugate hxCy) (hWF.conjugate x))
  exact (hmain hXF hch).1

theorem sec64_mem_normalizer [Finite G] (h63 : Asc82Lemma63) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) (hHyp : Asc82Hyp62 G) {y r : G} {Y : Subgroup G}
    (hy : orderOf y = 2) (hYc : IsComponentIn Y (centralizer ({y} : Set G))) (hYF : InFStar Y)
    (hr : r ∈ centralizer ({y} : Set G)) : r ∈ normalizer (Y : Set G) := by
  have hYeq : Y = CFSG.conjugate Y r :=
    h63 G t L hS hHyp y hy Y (CFSG.conjugate Y r) hYc hYF (hYc.conjugate hr) (hYF.conjugate r)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [hYeq] at hh
    exact sec64_mem_conjugate.mp hh
  · intro hh
    rw [hYeq]
    exact sec64_mem_conjugate.mpr hh

theorem sec64_step [Finite G] (hsh : Asc82Shapes) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {A B : Subgroup G} (h : WalterArrow A B) (hAF : InFStar A) :
    InFStar B ∧ (LieModel (A ⧸ oddCore A) .PSL 3 3 1 → IsOmega6Plus B) ∧
      (IsU33 A → IsOmega6Minus B) := by
  have hBF : InFStar B := inFStar_of_walterArrow hS.a2 h hAF
  obtain ⟨hdvd, hne⟩ := ctrQ_dvd_of_walterArrow h
  obtain ⟨x, y, -, hy, -, hAc, hBc, -, -⟩ := h
  have hAq := hAc.isQuasisimple
  have hBq := hBc.isQuasisimple
  have hBsh := sec65_shape hsh hS ⟨y, hy, hBc⟩ hBF
  refine ⟨hBF, ?_, ?_⟩
  · intro hA33
    rw [ctrQ_of_l33 hAq hA33] at hdvd hne
    rcases hBsh with hB | hB | hB | hB | hB | hB
    · rw [ctrQ_of_l29 hBq hB] at hdvd
      omega
    · rw [ctrQ_of_l281 hBq hB] at hdvd
      omega
    · rcases hB with hB | hB
      · rw [ctrQ_of_l33 hBq hB] at hne
        exact absurd rfl hne
      · rw [ctrQ_of_u33 hBq hB] at hdvd
        omega
    · rw [ctrQ_of_psp4 hBq hB] at hdvd
      omega
    · exact hB
    · rw [ctrQ_of_u43 hBq hB] at hdvd
      omega
  · intro hA33
    rw [ctrQ_of_u33 hAq hA33] at hdvd hne
    rcases hBsh with hB | hB | hB | hB | hB | hB
    · rw [ctrQ_of_l29 hBq hB] at hdvd
      omega
    · rw [ctrQ_of_l281 hBq hB] at hdvd
      omega
    · rcases hB with hB | hB
      · rw [ctrQ_of_l33 hBq hB] at hdvd
        omega
      · rw [ctrQ_of_u33 hBq hB] at hne
        exact absurd rfl hne
    · rw [ctrQ_of_psp4 hBq hB] at hdvd
      omega
    · rw [ctrQ_of_l43 hBq hB] at hdvd
      omega
    · exact hB

theorem sec64_plain_chain [Finite G] (hsh : Asc82Shapes) (hP : Asc82Tab6P) {t : G}
    {L : Subgroup G} (hS : Sec3SettingLB G t L) (hHyp : Asc82Hyp62 G) {X Y : Subgroup G}
    (hXC : InC X) (hXF : InFStar X) (hch : PlainChain X Y) :
    X = Y ∨
      (WalterArrow X Y ∧
        ((IsL29 X ∧ (IsL281 Y ∨ IsOmega5 Y ∨ IsOmega6Plus Y ∨ IsOmega6Minus Y)) ∨
          (IsOmega5 X ∧ (IsOmega6Plus Y ∨ IsOmega6Minus Y)) ∨
          (LieModel (X ⧸ oddCore X) .PSL 3 3 1 ∧ IsOmega6Plus Y) ∨
          (IsU33 X ∧ IsOmega6Minus Y))) ∨
      (IsL29 X ∧ ∃ Z : Subgroup G, WalterArrow X Z ∧ IsOmega5 Z ∧ WalterArrow Z Y ∧
        IsOmega6Minus Y) := by
  have hch' : Relation.ReflTransGen WalterArrow X Y := hch
  rcases hch'.cases_head with hXY | ⟨B, hXB, hBY⟩
  · exact Or.inl hXY
  · rcases sec65_shape hsh hS hXC hXF with h29 | h281 | h3eps | h5 | h6p | h6m
    · rcases sec63_plain_chain hsh hS hXF (Or.inl h29) hch with hXY | h2 | h3
      · exact Or.inl hXY
      · obtain ⟨hX29, hXY', hYsh⟩ := h2
        exact Or.inr (Or.inl ⟨hXY', Or.inl ⟨hX29, hYsh⟩⟩)
      · obtain ⟨hX29, Z, hXZ, hZ5, hZY, hYsh⟩ := h3
        rcases hYsh with h6p' | h6m'
        · exact absurd h6p' (sec63_no_om5_om6p hP hHyp hZY hZ5)
        · exact Or.inr (Or.inr ⟨hX29, Z, hXZ, hZ5, hZY, h6m'⟩)
    · exfalso
      obtain ⟨-, -, -, hs3⟩ := sec63_step hsh hS hXB hXF
      exact hs3 (Or.inl h281)
    · have h64 := sec64_step hsh hS hXB hXF
      rcases h3eps with h33 | hU33
      · have hB6p : IsOmega6Plus B := h64.2.1 h33
        rcases hBY.cases_head with hBeq | ⟨C, hBC, -⟩
        · rw [← hBeq]
          exact Or.inr (Or.inl ⟨hXB, Or.inr (Or.inr (Or.inl ⟨h33, hB6p⟩))⟩)
        · exfalso
          have hBF := inFStar_of_walterArrow hS.a2 hXB hXF
          obtain ⟨-, -, -, hs3'⟩ := sec63_step hsh hS hBC hBF
          exact hs3' (Or.inr (Or.inl hB6p))
      · have hB6m : IsOmega6Minus B := h64.2.2 hU33
        rcases hBY.cases_head with hBeq | ⟨C, hBC, -⟩
        · rw [← hBeq]
          exact Or.inr (Or.inl ⟨hXB, Or.inr (Or.inr (Or.inr ⟨hU33, hB6m⟩))⟩)
        · exfalso
          have hBF := inFStar_of_walterArrow hS.a2 hXB hXF
          obtain ⟨-, -, -, hs3'⟩ := sec63_step hsh hS hBC hBF
          exact hs3' (Or.inr (Or.inr hB6m))
    · obtain ⟨-, -, hs2, -⟩ := sec63_step hsh hS hXB hXF
      have hBsh : IsOmega6Plus B ∨ IsOmega6Minus B := hs2 h5
      rcases hBY.cases_head with hBeq | ⟨C, hBC, -⟩
      · rw [← hBeq]
        exact Or.inr (Or.inl ⟨hXB, Or.inr (Or.inl ⟨h5, hBsh⟩)⟩)
      · exfalso
        have hBF := inFStar_of_walterArrow hS.a2 hXB hXF
        obtain ⟨-, -, -, hs3'⟩ := sec63_step hsh hS hBC hBF
        rcases hBsh with h6p' | h6m'
        · exact hs3' (Or.inr (Or.inl h6p'))
        · exact hs3' (Or.inr (Or.inr h6m'))
    · exfalso
      obtain ⟨-, -, -, hs3⟩ := sec63_step hsh hS hXB hXF
      exact hs3 (Or.inr (Or.inl h6p))
    · exfalso
      obtain ⟨-, -, -, hs3⟩ := sec63_step hsh hS hXB hXF
      exact hs3 (Or.inr (Or.inr h6m))

end CFSG.OddStandard.SmallF3.Omega
