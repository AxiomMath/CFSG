module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionFacts
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotClassesC3Levi

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LieType.Ree (ReeTag)

variable {K : Type} [Field K]

namespace ClassReps

section Reps


variable (K) in
@[expose] noncomputable def frameT : adjointGroup .F4 K :=
  ⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩

variable (K) in
@[expose] noncomputable def frameU : adjointGroup .F4 K :=
  ⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩

variable (K) in
@[expose] noncomputable def frameTU : adjointGroup .F4 K :=
  ⟨f4x K 47 1 * f4x K 44 1, mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)⟩

variable (K) in
@[expose] noncomputable def frameV : adjointGroup .F4 K :=
  ⟨f4x K 41 1 * f4x K 45 1, mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)⟩

variable (K) in
@[expose] noncomputable def frameReps : Set (adjointGroup .F4 K) :=
  {frameT K, frameU K, frameTU K, frameV K}

theorem frameTU_eq : frameTU K = frameT K * frameU K := rfl

theorem frameV_eq : frameV K = (⟨f4x K 41 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) *
    ⟨f4x K 45 1, pinnedX_mem_adjointGroup _ _⟩ := rfl

end Reps

theorem orbitCertRoot_32_31_28 :
    orbitCertRoot .F4 32 = root0122 ∧ orbitCertRoot .F4 31 = root0121 ∧
      orbitCertRoot .F4 28 = root0110 :=
  ⟨List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel),
    List.ofFn_injective (by decide +kernel)⟩

theorem orbitCertRoot_mem_C3Set : orbitCertRoot .F4 32 ∈ C3Set ∧ orbitCertRoot .F4 31 ∈ C3Set ∧
    orbitCertRoot .F4 28 ∈ C3Set := by
  refine ⟨?_, ?_, ?_⟩ <;> (show _ ∈ C3Roots; decide +kernel)

@[expose] def weylWordT : List ℕ := [0, 1, 2, 3, 1, 2, 0]

@[expose] def weylWordV : List ℕ := [0, 1, 2, 3, 1, 2, 1]

theorem weylWord_perm :
    f4CollWeylPerm weylWordT 47 = 32 ∧ f4CollWeylPerm weylWordT 44 = 31 ∧
      f4CollWeylPerm weylWordV 41 = 28 ∧ f4CollWeylPerm weylWordV 45 = 32 := by
  decide

theorem weylWord_lt_four : (∀ j ∈ weylWordT, j < 4) ∧ ∀ j ∈ weylWordV, j < 4 := by
  decide

section Coe


theorem coe_yRep_t : ((yRep K .t : adjointGroup .F4 K) : ModGL .F4 K) = f4x K 32 1 := by
  show pinnedX .F4 K root0122 1 = pinnedX .F4 K (orbitCertRoot .F4 32) 1
  rw [orbitCertRoot_32_31_28.1]

theorem coe_yRep_u : ((yRep K .u : adjointGroup .F4 K) : ModGL .F4 K) = f4x K 31 1 := by
  show pinnedX .F4 K root0121 1 = pinnedX .F4 K (orbitCertRoot .F4 31) 1
  rw [orbitCertRoot_32_31_28.2.1]

theorem coe_yRep_tu :
    ((yRep K .tu : adjointGroup .F4 K) : ModGL .F4 K) = f4x K 32 1 * f4x K 31 1 := by
  show pinnedX .F4 K root0122 1 * pinnedX .F4 K root0121 1 =
    pinnedX .F4 K (orbitCertRoot .F4 32) 1 * pinnedX .F4 K (orbitCertRoot .F4 31) 1
  rw [orbitCertRoot_32_31_28.1, orbitCertRoot_32_31_28.2.1]

theorem coe_yV : ((yV K : adjointGroup .F4 K) : ModGL .F4 K) = f4x K 28 1 * f4x K 32 1 := by
  show pinnedX .F4 K root0110 1 * pinnedX .F4 K root0122 1 =
    pinnedX .F4 K (orbitCertRoot .F4 28) 1 * pinnedX .F4 K (orbitCertRoot .F4 32) 1
  rw [orbitCertRoot_32_31_28.1, orbitCertRoot_32_31_28.2.2]

theorem mem_C3Levi_yRep (κ : TwoCentral) : yRep K κ ∈ C3Levi K := by
  obtain ⟨h32, h31, -⟩ := orbitCertRoot_mem_C3Set
  have e32 : f4x K 32 1 ∈ rootSpan .F4 K C3Set := pinnedX_mem_rootSpan h32 1
  have e31 : f4x K 31 1 ∈ rootSpan .F4 K C3Set := pinnedX_mem_rootSpan h31 1
  rw [C3Levi_eq_subgroupOf_rootSpan_C3Set, Subgroup.mem_subgroupOf]
  cases κ
  · rw [coe_yRep_t]; exact e32
  · rw [coe_yRep_u]; exact e31
  · rw [coe_yRep_tu]; exact mul_mem e32 e31

theorem mem_C3Levi_yV : yV K ∈ C3Levi K := by
  obtain ⟨h32, -, h28⟩ := orbitCertRoot_mem_C3Set
  rw [C3Levi_eq_subgroupOf_rootSpan_C3Set, Subgroup.mem_subgroupOf, coe_yV]
  exact mul_mem (pinnedX_mem_rootSpan h28 1) (pinnedX_mem_rootSpan h32 1)

end Coe

section Weyl


variable (K) in
@[expose] noncomputable def weylEltC (ω : List ℕ) : adjointGroup .F4 K :=
  ⟨f4CollWeylElt K ω, f4CollWeylElt_mem ω⟩

theorem weylEltC_conj_frame [CharP K 2] :
    weylEltC K weylWordT * frameT K * (weylEltC K weylWordT)⁻¹ = yRep K .t ∧
      weylEltC K weylWordT * frameU K * (weylEltC K weylWordT)⁻¹ = yRep K .u ∧
      weylEltC K weylWordT * frameTU K * (weylEltC K weylWordT)⁻¹ = yRep K .tu ∧
      weylEltC K weylWordV * frameV K * (weylEltC K weylWordV)⁻¹ = yV K := by
  obtain ⟨hT, hV⟩ := weylWord_lt_four
  obtain ⟨p47, p44, p41, p45⟩ := weylWord_perm
  have c47 := (f4CollWeylElt_conj (K := K) weylWordT hT (p := 47) (by norm_num) 1).1
  have c44 := (f4CollWeylElt_conj (K := K) weylWordT hT (p := 44) (by norm_num) 1).1
  have c41 := (f4CollWeylElt_conj (K := K) weylWordV hV (p := 41) (by norm_num) 1).1
  have c45 := (f4CollWeylElt_conj (K := K) weylWordV hV (p := 45) (by norm_num) 1).1
  rw [p47] at c47
  rw [p44] at c44
  rw [p41] at c41
  rw [p45] at c45
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [coe_yRep_t, ← c47]
    rfl
  · rw [coe_yRep_u, ← c44]
    rfl
  · rw [coe_yRep_tu, ← c47, ← c44]
    simp only [weylEltC, frameTU, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  · rw [coe_yV, ← c41, ← c45]
    simp only [weylEltC, frameV, Subgroup.coe_mul, Subgroup.coe_inv]
    group

end Weyl

section ClassList


theorem exists_mulAut_eq_frameRep [Finite K] [CharP K 2] {y : adjointGroup .F4 K}
    (hy : y ^ 2 = 1) (hy1 : y ≠ 1) :
    ∃ β : MulAut (adjointGroup .F4 K), β y = frameT K ∨ β y = frameTU K ∨ β y = frameV K := by
  obtain ⟨ψ, L, hL, he⟩ := exists_mulAut_eq_f4DescProd hy hy1
  have hL' : L ∈ f4FrameCandidates := hL
  obtain ⟨g, hg, hgL⟩ := exists_conj_of_mem_f4FrameCandidates (K := K) hL'
  set g' : adjointGroup .F4 K := ⟨g, hg⟩ with hg'
  have hβ : (((MulAut.conj g' * ψ) y : adjointGroup .F4 K) : ModGL .F4 K) =
      g * f4CollProd K L * g⁻¹ := by
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, he]
    rfl
  refine ⟨MulAut.conj g' * ψ, ?_⟩
  rcases hgL with h | h | h
  · exact Or.inl (Subtype.ext (hβ.trans h))
  · exact Or.inr (Or.inl (Subtype.ext (hβ.trans h)))
  · exact Or.inr (Or.inr (Subtype.ext (hβ.trans h)))

theorem frameU_mul_frameT [CharP K 2] : frameU K * frameT K = frameT K * frameU K :=
  Subtype.ext (f4x_central (Or.inr rfl) 1 (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ 1))

theorem f4x_45_mul_f4x_41 [CharP K 2] :
    f4x K 45 1 * f4x K 41 1 = f4x K 41 1 * f4x K 45 1 :=
  (f4x_commute_of_lookup ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    (fun _ => by decide +kernel) (1 : K) 1).symm

theorem phi_mem_frameReps [Finite K] [CharP K 2] {w : adjointGroup .F4 K}
    (hw : w ∈ frameReps K) : f4DescPhi K w ∈ frameReps K := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨h47, h44⟩ := f4Phi_f4x_47_44 (K := K)
  have hT : f4DescPhi K (frameT K) = frameU K := h47
  have hU : f4DescPhi K (frameU K) = frameT K := h44
  obtain ⟨hl, hs, hd45, hd41⟩ := f4Pair_roots 9
  have e45 : f4PairLong 9 = 45 := rfl
  have e41 : f4PairShort 9 = 41 := rfl
  rw [e45] at hl
  rw [e41] at hs
  rw [e45, e41] at hd45 hd41
  have h41 : f4DescPhi K ⟨f4x K 41 1, pinnedX_mem_adjointGroup _ _⟩ =
      ⟨f4x K 45 1, pinnedX_mem_adjointGroup _ _⟩ := by
    have h := finiteExceptionalAut_pinnedX_short (K := K) hs 1
    rw [hd41, one_pow] at h
    exact h
  have h45 : f4DescPhi K ⟨f4x K 45 1, pinnedX_mem_adjointGroup _ _⟩ =
      ⟨f4x K 41 1, pinnedX_mem_adjointGroup _ _⟩ := by
    have h := finiteExceptionalAut_pinnedX_long (K := K) hl 1
    rw [hd45] at h
    exact h
  have hTU : f4DescPhi K (frameTU K) = frameTU K := by
    rw [frameTU_eq, map_mul, hT, hU, frameU_mul_frameT]
  have hV : f4DescPhi K (frameV K) = frameV K := by
    rw [frameV_eq, map_mul, h41, h45]
    exact Subtype.ext f4x_45_mul_f4x_41
  simp only [frameReps, Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
  rcases hw with rfl | rfl | rfl | rfl
  · rw [hT]; exact Or.inr (Or.inl rfl)
  · rw [hU]; exact Or.inl rfl
  · rw [hTU]; exact Or.inr (Or.inr (Or.inl rfl))
  · rw [hV]; exact Or.inr (Or.inr (Or.inr rfl))

theorem phi_pow_mem_frameReps [Finite K] [CharP K 2] (k : ℕ) {w : adjointGroup .F4 K}
    (hw : w ∈ frameReps K) : ((f4DescPhi K) ^ k) w ∈ frameReps K := by
  induction k with
  | zero => simpa using hw
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply]
    exact phi_mem_frameReps ih

theorem exists_conj_mem_frameReps [Finite K] [CharP K 2] {y : adjointGroup .F4 K}
    (hy : orderOf y = 2) : ∃ g : adjointGroup .F4 K, g * y * g⁻¹ ∈ frameReps K := by
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy
    exact absurd hy (by decide)
  obtain ⟨β, hβ⟩ := exists_mulAut_eq_frameRep hy2 hy1
  have hβR : β y ∈ frameReps K := by
    simp only [frameReps, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hβ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨-, hnf, -⟩ := even_F4_exact_automorphism_normal_form n.pos K hK
  obtain ⟨⟨h₀, k⟩, hhk₀, -⟩ := hnf β⁻¹
  set h : adjointGroup .F4 K := h₀
  have hhk : β⁻¹ = MulAut.conj h * (f4DescPhi K) ^ (k : ℕ) := hhk₀
  clear_value h
  clear hhk₀
  have hy' : y = h * ((f4DescPhi K) ^ (k : ℕ)) (β y) * h⁻¹ := by
    have e : β⁻¹ (β y) = y := by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    rw [← MulAut.conj_apply, ← MulAut.mul_apply, ← hhk, e]
  have hw := phi_pow_mem_frameReps k hβR
  obtain ⟨w, hw'⟩ : ∃ w, ((f4DescPhi K) ^ (k : ℕ)) (β y) = w := ⟨_, rfl⟩
  rw [hw'] at hy' hw
  refine ⟨h⁻¹, ?_⟩
  have e : h⁻¹ * y * h⁻¹⁻¹ = w := by
    rw [hy']
    group
  rw [e]
  exact hw

theorem not_conj_frameT_frameU [CharP K 2] (g : adjointGroup .F4 K) :
    g * frameT K * g⁻¹ ≠ frameU K := fun h =>
  conj_f4x_47_ne_f4x_44 g.2 (by
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h'
    exact h')

theorem not_conj_yRep_t_u [CharP K 2] (g : adjointGroup .F4 K) :
    g * yRep K .t * g⁻¹ ≠ yRep K .u := by
  intro h
  obtain ⟨hT, hU, -, -⟩ := weylEltC_conj_frame (K := K)
  set n := weylEltC K weylWordT
  apply not_conj_frameT_frameU (n⁻¹ * g * n)
  rw [← hT, ← hU] at h
  calc n⁻¹ * g * n * frameT K * (n⁻¹ * g * n)⁻¹ = n⁻¹ * (g * (n * frameT K * n⁻¹) * g⁻¹) * n := by
        group
    _ = n⁻¹ * (n * frameU K * n⁻¹) * n := by rw [h]
    _ = frameU K := by group

end ClassList

end ClassReps

section FactF1


open ClassReps

theorem factF1 [Finite K] [CharP K 2] : FactF1 K := by
  intro y hy
  obtain ⟨g, hg⟩ := exists_conj_mem_frameReps hy
  obtain ⟨hT, hU, hTU, hV⟩ := weylEltC_conj_frame (K := K)
  have key : ∀ {n w y' : adjointGroup .F4 K}, g * y * g⁻¹ = w → n * w * n⁻¹ = y' →
      (n * g) * y * (n * g)⁻¹ = y' := by
    intro n w y' h1 h2
    rw [← h2, ← h1]
    group
  simp only [frameReps, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with h | h | h | h
  · exact ⟨_, Or.inl (key h hT)⟩
  · exact ⟨_, Or.inr (Or.inl (key h hU))⟩
  · exact ⟨_, Or.inr (Or.inr (Or.inl (key h hTU)))⟩
  · exact ⟨_, Or.inr (Or.inr (Or.inr (key h hV)))⟩

end FactF1

end CFSG.SeitzReduction.F4Pilot
