module

public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4ElementCentralizerTorus
public import CFSG.RankThree.PartOne.KLR.A1Pair
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4PlaneCentralizer

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KF4
  CFSG.HardMathSupport.Malle.LocalAction

section A1

variable {L : Type} [Field L] {i j : Fin ReeTag.F4.tag.rank}

theorem cartan_f4_zero_symm : ∀ i j : Fin 4, Tag.F4.cartan i j = 0 → Tag.F4.cartan j i = 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem cartan_f4_two : ∀ k : Fin 4, Tag.F4.cartan k k = 2 := by
  intro k
  fin_cases k <;> decide

omit [Field L] in
theorem a1Pair_cartan_symm (h : A1Pair i j) : Tag.F4.cartan j i = 0 :=
  cartan_f4_zero_symm i j h.cartan

omit [Field L] in
theorem cartan_f4_diag (k : Fin ReeTag.F4.tag.rank) : Tag.F4.cartan k k = 2 :=
  cartan_f4_two k

theorem mem_charKer_a1 (h : A1Pair i j) {c : Fin ReeTag.F4.tag.rank → Lˣ} :
    c ∈ charKer (L := L) (parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) ↔
      c i = 1 ∧ c j = 1 := by
  constructor
  · intro hc
    have h1 := hc (Pi.single i 1) ⟨isRoot_single _ _, fun k hk => Pi.single_eq_of_ne
      (fun e => hk (by simp [e])) _⟩
    have h2 := hc (Pi.single j 1) ⟨isRoot_single _ _, fun k hk => Pi.single_eq_of_ne
      (fun e => hk (by simp [e])) _⟩
    exact ⟨(CTTorus.rootChar_single c _).symm.trans h1, (CTTorus.rootChar_single c _).symm.trans h2⟩
  · rintro ⟨h1, h2⟩ α ⟨-, hα⟩
    unfold rootChar
    refine Finset.prod_eq_one fun k _ => ?_
    by_cases hk : k = i
    · rw [hk, h1, one_zpow]
    · by_cases hk' : k = j
      · rw [hk', h2, one_zpow]
      · rw [hα k (by simp [hk, hk']), zpow_zero]

theorem torus2Elt_eq_rootDiagUnit_a1 (s₁ s₂ : Lˣ) :
    torus2Elt i j s₁ s₂ = rootDiagUnit ReeTag.F4.tag
      (fun l => s₁ ^ Tag.F4.cartan i l * s₂ ^ Tag.F4.cartan j l) := by
  rw [torus2Elt, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  rfl

theorem a1_split [IsAlgClosed L] (h : A1Pair i j)
    (c : Fin ReeTag.F4.tag.rank → Lˣ) :
    ∃ z ∈ ZGrp (L := L) (parabolicRoots ReeTag.F4.tag
        (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))),
      ∃ q ∈ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
        (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))),
        rootDiagUnit ReeTag.F4.tag c = z * q := by
  obtain ⟨s₁, hs₁⟩ := exists_unit_sq (c i)
  obtain ⟨s₂, hs₂⟩ := exists_unit_sq (c j)
  set t : Fin ReeTag.F4.tag.rank → Lˣ :=
    fun l => s₁ ^ Tag.F4.cartan i l * s₂ ^ Tag.F4.cartan j l with ht
  have hji := a1Pair_cartan_symm h
  have hii := cartan_f4_diag i
  have hjj := cartan_f4_diag j
  have hij := h.cartan
  refine ⟨rootDiagUnit ReeTag.F4.tag (c * t⁻¹), ?_, torus2Elt i j s₁ s₂, ?_, ?_⟩
  · refine mem_ZGrp.2 ⟨c * t⁻¹, (mem_charKer_a1 h).2 ⟨?_, ?_⟩, rfl⟩
    · show c i * (s₁ ^ Tag.F4.cartan i i * s₂ ^ Tag.F4.cartan j i)⁻¹ = 1
      rw [hii, hji, zpow_zero, mul_one, ← hs₁]
      simp [sq]
    · show c j * (s₁ ^ Tag.F4.cartan i j * s₂ ^ Tag.F4.cartan j j)⁻¹ = 1
      rw [hij, hjj, zpow_zero, one_mul, ← hs₂]
      simp [sq]
  · have hmem : torus2Elt i j s₁ s₂ ∈ subsystemTorus ReeTag.F4.tag L ({i, j} : Set (Fin ReeTag.F4.tag.rank)) :=
      (mem_subsystemTorus_pair i j).2 ⟨s₁, s₂, rfl⟩
    have h1 : torus2Elt i j s₁ s₂ ∈ subsystemGroup ReeTag.F4.tag L ({i, j} : Set (Fin ReeTag.F4.tag.rank)) :=
      subsystemTorus_le_subsystemGroup hmem
    rw [subsystemGroup_eq_rootSpan] at h1
    simpa only [Finset.coe_pair] using h1
  · have e := torus2Elt_eq_rootDiagUnit_a1 (L := L) (i := i) (j := j) s₁ s₂
    calc rootDiagUnit ReeTag.F4.tag c =
        rootDiagUnit ReeTag.F4.tag (c * t⁻¹) * rootDiagUnit ReeTag.F4.tag t := by
          rw [← rootDiagUnit_mul]
          congr 1
          funext l
          simp
      _ = _ := congrArg _ e.symm

theorem a1_inf [CharP L 2] [IsAlgClosed L] (h : A1Pair i j) :
    ZGrp (L := L) (parabolicRoots ReeTag.F4.tag
        (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) ⊓
      rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
        (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) = ⊥ := by
  have hji := a1Pair_cartan_symm h
  have hii := cartan_f4_diag i
  have hjj := cartan_f4_diag j
  have hij := h.cartan
  rw [eq_bot_iff]
  rintro _ ⟨hz, hq⟩
  obtain ⟨e, he, rfl⟩ := mem_ZGrp.1 hz
  obtain ⟨he1, he2⟩ := (mem_charKer_a1 h).1 he
  have hH : rootDiagUnit ReeTag.F4.tag e ∈ torusGroup ReeTag.F4.tag L :=
    rootDiagUnit_mem_torusGroup e
  have hq0 : rootDiagUnit ReeTag.F4.tag e ∈ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) := hq
  have hq' : rootDiagUnit ReeTag.F4.tag e ∈
      subsystemGroup ReeTag.F4.tag L ({i, j} : Set (Fin ReeTag.F4.tag.rank)) := by
    rw [subsystemGroup_eq_rootSpan]
    simpa only [Finset.coe_pair] using hq0
  have hT : rootDiagUnit ReeTag.F4.tag e ∈
      subsystemTorus ReeTag.F4.tag L ({i, j} : Set (Fin ReeTag.F4.tag.rank)) := by
    have hinf := subsystemGroup_inf_torusGroup (τ := ReeTag.F4.tag) (K := L)
      (A := ({i, j} : Set (Fin ReeTag.F4.tag.rank)))
    have hmem : rootDiagUnit ReeTag.F4.tag e ∈
        subsystemGroup ReeTag.F4.tag L ({i, j} : Set (Fin ReeTag.F4.tag.rank)) ⊓
          torusGroup ReeTag.F4.tag L := ⟨hq', hH⟩
    rwa [hinf] at hmem
  obtain ⟨s₁, s₂, hs⟩ := (mem_subsystemTorus_pair i j).1 hT
  have hcart : e = fun l => s₁ ^ Tag.F4.cartan i l * s₂ ^ Tag.F4.cartan j l :=
    rootDiagUnit_injective (τ := ReeTag.F4.tag) (K := L)
      (hs.trans (torus2Elt_eq_rootDiagUnit_a1 s₁ s₂))
  have e1 : e i = s₁ ^ 2 := by
    rw [hcart]
    show s₁ ^ Tag.F4.cartan i i * s₂ ^ Tag.F4.cartan j i = _
    rw [hii, hji]
    simp
  have e2 : e j = s₂ ^ 2 := by
    rw [hcart]
    show s₁ ^ Tag.F4.cartan i j * s₂ ^ Tag.F4.cartan j j = _
    rw [hij, hjj]
    simp
  have hs1 : s₁ = 1 := unit_sq_eq_one_charTwo (by rw [← e1, he1])
  have hs2 : s₂ = 1 := unit_sq_eq_one_charTwo (by rw [← e2, he2])
  show rootDiagUnit ReeTag.F4.tag e = 1
  rw [hs, hs1, hs2]
  exact torus2Elt_one i j

end A1

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big
