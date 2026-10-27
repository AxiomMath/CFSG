module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL3
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.BorelOvergroups

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even
open scoped Pointwise


variable {K : Type} [Field K] [Finite K]

section Roots

theorem d4_posRoot_check : ∀ l ∈ Tag.D4.artifactRoots, 0 < l.sum →
    (l.getD 2 0 = 0 → l = [1, 0, 0, 0] ∨ l = [0, 1, 0, 0] ∨ l = [0, 0, 0, 1]) ∧
    (l.getD 0 0 = 0 → l.getD 1 0 = 0 → l.getD 3 0 = 0 → l = [0, 0, 1, 0]) := by
  decide

theorem posRoot_simple {J : Set (Fin Tag.D4.rank)}
    (hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank))) {β : Fin Tag.D4.rank → ℤ}
    (hβ : β ∈ parabolicPosRoots Tag.D4 J) : ∃ k ∈ J, β = Pi.single k 1 := by
  obtain ⟨⟨hroot, hsupp⟩, -, hpos⟩ := hβ
  have hl := (isRoot_iff_mem_artifactRoots (τ := Tag.D4)).1 hroot
  have hpos' : 0 < (List.ofFn β).sum := by rw [List.sum_ofFn]; exact hpos
  have hlist : List.ofFn β = [β 0, β 1, β 2, β 3] := rfl
  have e0 : (List.ofFn β).getD 0 0 = β 0 := by rw [hlist]; rfl
  have e1 : (List.ofFn β).getD 1 0 = β 1 := by rw [hlist]; rfl
  have e2 : (List.ofFn β).getD 2 0 = β 2 := by rw [hlist]; rfl
  have e3 : (List.ofFn β).getD 3 0 = β 3 := by rw [hlist]; rfl
  obtain ⟨h1, h2⟩ := d4_posRoot_check _ hl hpos'
  have key : ∀ a b c d : ℤ, [β 0, β 1, β 2, β 3] = [a, b, c, d] →
      β 0 = a ∧ β 1 = b ∧ β 2 = c ∧ β 3 = d := by
    intro a b c d h
    simpa using h
  have hi4 : ∀ i : Fin Tag.D4.rank, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  rcases hJ with rfl | rfl
  · have hb0 : β 0 = 0 := hsupp 0 (by simp)
    have hb1 : β 1 = 0 := hsupp 1 (by simp)
    have hb3 : β 3 = 0 := hsupp 3 (by simp)
    have := h2 (by rw [e0]; exact hb0) (by rw [e1]; exact hb1) (by rw [e3]; exact hb3)
    rw [hlist] at this
    obtain ⟨c0, c1, c2, c3⟩ := key _ _ _ _ this
    refine ⟨2, Set.mem_singleton _, funext fun i => ?_⟩
    rcases hi4 i with rfl | rfl | rfl | rfl <;> simp [Pi.single_apply, c0, c1, c2, c3]
  · have hb2 : β 2 = 0 := hsupp 2 (by simp)
    have := h1 (by rw [e2]; exact hb2)
    rw [hlist] at this
    rcases this with h | h | h
    · obtain ⟨c0, c1, c2, c3⟩ := key _ _ _ _ h
      refine ⟨0, mem_outer0, funext fun i => ?_⟩
      rcases hi4 i with rfl | rfl | rfl | rfl <;> simp [Pi.single_apply, c0, c1, c2, c3]
    · obtain ⟨c0, c1, c2, c3⟩ := key _ _ _ _ h
      refine ⟨1, mem_outer1, funext fun i => ?_⟩
      rcases hi4 i with rfl | rfl | rfl | rfl <;> simp [Pi.single_apply, c0, c1, c2, c3]
    · obtain ⟨c0, c1, c2, c3⟩ := key _ _ _ _ h
      refine ⟨3, mem_outer3, funext fun i => ?_⟩
      rcases hi4 i with rfl | rfl | rfl | rfl <;> simp [Pi.single_apply, c0, c1, c2, c3]

theorem leviUnip_le {J : Set (Fin Tag.D4.rank)}
    (hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank))) :
    parabolicLeviUnipotent Tag.D4 K J ≤
      Subgroup.closure {x | ∃ k ∈ J, ∃ c : K, x = xUnit Tag.D4 K k c} := by
  unfold parabolicLeviUnipotent rootSpan
  refine iSup₂_le fun β hβ => ?_
  obtain ⟨k, hk, rfl⟩ := posRoot_simple hJ hβ
  unfold rootSubgroup
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  rw [pinnedX_single]
  exact Subgroup.subset_closure ⟨k, hk, c, rfl⟩

end Roots

section Semi

theorem semiDirect_levi (J : Set (Fin Tag.D4.rank)) :
    IsSemiDirect (parabolicSubgroup Tag.D4 K J) (parabolicRadical Tag.D4 K J)
      (parabolicLevi Tag.D4 K J) := by
  obtain ⟨hQP, -, -, hMP, hinf, hsup, -⟩ := parabolic_root_radical_Levi_factors (τ := Tag.D4) (K := K) J
  have hnorm : parabolicSubgroup Tag.D4 K J ≤
      Subgroup.normalizer (parabolicRadical Tag.D4 K J : Set (ModGL Tag.D4 K)) :=
    parabolicSubgroup_le_normalizer_parabolicRadical J
  have hMN : parabolicLevi Tag.D4 K J ≤
      Subgroup.normalizer (parabolicRadical Tag.D4 K J : Set (ModGL Tag.D4 K)) :=
    le_trans hMP hnorm
  have hprod : (parabolicSubgroup Tag.D4 K J : Set (ModGL Tag.D4 K)) =
      (parabolicRadical Tag.D4 K J : Set (ModGL Tag.D4 K)) * (parabolicLevi Tag.D4 K J : Set (ModGL Tag.D4 K)) := by
    rw [← hsup, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hMN]
  refine ⟨hQP, hMP, fun x hx q hq => ?_, fun x hxQ hxM => ?_, fun x hx => ?_⟩
  · exact ((Subgroup.mem_normalizer_iff.1 (hnorm hx) q).1 hq)
  · have : x ∈ parabolicRadical Tag.D4 K J ⊓ parabolicLevi Tag.D4 K J := ⟨hxQ, hxM⟩
    rw [hinf] at this
    exact this
  · have hx' : x ∈ (parabolicRadical Tag.D4 K J : Set (ModGL Tag.D4 K)) *
        (parabolicLevi Tag.D4 K J : Set (ModGL Tag.D4 K)) := by
      rw [← hprod]; exact hx
    obtain ⟨q, hq, m, hm, rfl⟩ := hx'
    exact ⟨q, hq, m, hm, rfl⟩

end Semi

section Phi

@[expose] def phiG (g : ModGL Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) :
    ModGL Tag.D4 K →* ModGL Tag.D4 K :=
  (MulAut.conj g).toMonoidHom.comp (d4F K a σ ε)

theorem phiG_apply (g : ModGL Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ)
    (x : ModGL Tag.D4 K) : phiG g a σ ε x = g * d4F K a σ ε x * g⁻¹ := rfl

theorem height_permLattice_d4 (π : Equiv.Perm (Fin Tag.D4.rank)) (v : Fin Tag.D4.rank → ℤ) :
    height (permLattice π v) = height v := by
  unfold height permLattice
  exact Equiv.sum_comp π.symm v

theorem permLattice_radical {J : Set (Fin Tag.D4.rank)} {ε : ℕ}
    (hJρ : ∀ i, i ∈ J ↔ (d4Rho ^ ε) i ∈ J) {β : Fin Tag.D4.rank → ℤ}
    (hβ : β ∈ parabolicRadicalRoots Tag.D4 J) :
    permLattice (d4Rho ^ ε) β ∈ parabolicRadicalRoots Tag.D4 J := by
  obtain ⟨hroot, hpos, i, hi, hβi⟩ := mem_parabolicRadicalRoots_iff.1 hβ
  refine mem_parabolicRadicalRoots_iff.2 ⟨isRoot_permLattice_d4Rho_pow hroot ε, ?_,
    (d4Rho ^ ε) i, fun h => hi ((hJρ i).2 h), ?_⟩
  · rw [height_permLattice_d4]; exact hpos
  · simpa [permLattice] using hβi

theorem phi_radical_le {J : Set (Fin Tag.D4.rank)} {g : ModGL Tag.D4 K} (hg : g ∈ borelGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) {ε : ℕ} (hJρ : ∀ i, i ∈ J ↔ (d4Rho ^ ε) i ∈ J) :
    ∀ q ∈ parabolicRadical Tag.D4 K J, phiG g a σ ε q ∈ parabolicRadical Tag.D4 K J := by
  have hgN : g ∈ Subgroup.normalizer (parabolicRadical Tag.D4 K J : Set (ModGL Tag.D4 K)) :=
    borelGroup_le_normalizer_parabolicRadical J hg
  have hle : parabolicRadical Tag.D4 K J ≤
      (parabolicRadical Tag.D4 K J).comap (phiG g a σ ε) := by
    unfold parabolicRadical rootSpan
    refine iSup₂_le fun β hβ => ?_
    unfold rootSubgroup
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    obtain ⟨e, he⟩ := exists_d4F_pinnedX (K := K) a σ ε
    have hroot := (mem_parabolicRadicalRoots_iff.1 hβ).1
    show phiG g a σ ε (pinnedX Tag.D4 K β c) ∈ rootSpan Tag.D4 K (parabolicRadicalRoots Tag.D4 J)
    rw [phiG_apply, he β hroot c]
    have hmem : pinnedX Tag.D4 K (permLattice (d4Rho ^ ε) β) (e β * σ c) ∈
        rootSpan Tag.D4 K (parabolicRadicalRoots Tag.D4 J) :=
      Subgroup.mem_iSup_of_mem (permLattice (d4Rho ^ ε) β) (Subgroup.mem_iSup_of_mem
        (permLattice_radical hJρ hβ) (Subgroup.subset_closure ⟨_, rfl⟩))
    exact (Subgroup.mem_normalizer_iff.1 hgN _).1 hmem
  exact fun q hq => hle hq

end Phi

end CFSG.LocalAnalysis.GLTheoremA
