module

public import CFSG.Certificates.Kernel.E8PlaneSound
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest6
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KilledPlaneTransport
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KilledPlaneCubeRoot
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8KilledPlaneWords
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8KilledPlaneBlocksGeo
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralD4Triples

public section

namespace CFSG.KC.E8Plane

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest6.Aux
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral.E8Plane


private theorem triPairing_comb (c₀ c₁ : ZMod 3) (b₀ b₁ : Fin Tag.E8.rank → ZMod 3)
    (v : Fin Tag.E8.rank → ℤ) :
    triPairing (c₀ • b₀ + c₁ • b₁) v = c₀ * triPairing b₀ v + c₁ * triPairing b₁ v := by
  simp only [triPairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

private theorem exists_triPairing_conj (g : WeylGroup Tag.E8) (b : Fin Tag.E8.rank → ZMod 3) :
    ∃ b' : Fin Tag.E8.rank → ZMod 3, ∀ x, triPairing b' x = triPairing b (g⁻¹ • x) := by
  let f : (Fin Tag.E8.rank → ℤ) →+ (Fin Tag.E8.rank → ℤ) :=
    AddMonoidHom.mk' (fun x => g⁻¹ • x) (smul_add g⁻¹)
  let φ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Z3 :=
    (triChar b).comp (AddMonoidHom.toMultiplicative f)
  refine ⟨fun j => Z3.toAdd (φ (Multiplicative.ofAdd (Pi.single j 1))), fun x => ?_⟩
  have h := congrArg (fun χ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Z3 =>
    χ (Multiplicative.ofAdd x)) (eq_triChar φ)
  have h2 : φ (Multiplicative.ofAdd x) = Z3.ofAdd (triPairing b (g⁻¹ • x)) := rfl
  simp only [triChar_apply, h2, Z3.ofAdd_eq_ofAdd_iff] at h
  exact h.symm

theorem planeOK_conj {t v : WeylGroup Tag.E8} {b b' : Fin 2 → Fin Tag.E8.rank → ZMod 3}
    (hb : ∀ s x, triPairing (b' s) x = triPairing (b s) (t • x)) (h : E8PlaneOK v b') :
    E8PlaneOK (t * v * t⁻¹) b := by
  have hS : ∀ α, α ∈ planeKer b ↔ t⁻¹ • α ∈ planeKer b' := by
    intro α
    rw [mem_planeKer, mem_planeKer, isRoot_smul_iff, hb, hb, smul_inv_smul]
  have hS' : ∀ α ∈ planeKer b', IsRoot Tag.E8 α := fun α h => (mem_planeKer.1 h).1
  rcases h with h | h | ⟨h78, h⟩
  · left
    rw [closure_rootReflection_eq_map hS' hS]
    exact ⟨v, h, rfl⟩
  · right; left
    exact exists_kernelBlocks_conj hS' hS h
  · right; right
    refine ⟨fun c hc => ?_, ?_⟩
    · rw [ncard_eq_of_mem_iff_inv_smul (t := t)
        (S' := {α | IsRoot Tag.E8 α ∧ triPairing (c 0 • b' 0 + c 1 • b' 1) α = 0}) ?_]
      · exact h78 c hc
      · intro α
        simp only [Set.mem_setOf_eq, isRoot_smul_iff, triPairing_comb, hb, smul_inv_smul]
    · rcases h with ⟨h24, hfix, htr, horb⟩ | htri
      · left
        obtain ⟨h1, h2⟩ := orthOrbit_conj hS hfix horb
        exact ⟨by rw [ncard_eq_of_mem_iff_inv_smul hS, h24], h1,
          tripleRefl_transitive_conj hS htr, h2⟩
      · right
        exact e8D4Triangles_conj htri

section Field

variable {L : Type} [Field L] {a : Fin 2 → Fin Tag.E8.rank → Lˣ}
  {k : Fin 2 → Fin Tag.E8.rank → ZMod 3}

private theorem rootChar_eq_one_iff_of_comb
    (hk : ∀ (c : Fin 2 → ZMod 3) (v : Fin Tag.E8.rank → ℤ),
      rootChar (fun i => a 0 i ^ (c 0).val * a 1 i ^ (c 1).val) v = 1 ↔
        triPairing (c 0 • k 0 + c 1 • k 1) v = 0) (s : Fin 2) (v : Fin Tag.E8.rank → ℤ) :
    rootChar (a s) v = 1 ↔ triPairing (k s) v = 0 := by
  have h1 : (1 : ZMod 3).val = 1 := rfl
  have h0 : (0 : ZMod 3).val = 0 := rfl
  fin_cases s
  · simpa [h0, h1] using hk ![1, 0] v
  · simpa [h0, h1] using hk ![0, 1] v

private theorem familyKernel_eq_planeKer
    (hk : ∀ (c : Fin 2 → ZMod 3) (v : Fin Tag.E8.rank → ℤ),
      rootChar (fun i => a 0 i ^ (c 0).val * a 1 i ^ (c 1).val) v = 1 ↔
        triPairing (c 0 • k 0 + c 1 • k 1) v = 0) :
    familyKernel a = planeKer k := by
  ext α
  rw [mem_planeKer, familyKernel, Set.mem_setOf_eq, Fin.forall_fin_two,
    rootChar_eq_one_iff_of_comb hk 0, rootChar_eq_one_iff_of_comb hk 1]

private theorem triPairing_smul_of_mem_rootCharStabilizer
    (hk : ∀ (c : Fin 2 → ZMod 3) (v : Fin Tag.E8.rank → ℤ),
      rootChar (fun i => a 0 i ^ (c 0).val * a 1 i ^ (c 1).val) v = 1 ↔
        triPairing (c 0 • k 0 + c 1 • k 1) v = 0)
    {s : Fin 2} {w : WeylGroup Tag.E8} (hw : w ∈ rootCharStabilizer (a s))
    (x : Fin Tag.E8.rank → ℤ) :
    triPairing (k s) (w • x) = triPairing (k s) x := by
  have h1 : rootChar (a s) (w • x - x) = 1 := by
    have h := hw x
    rw [← sub_add_cancel (w • x) x, rootChar_add] at h
    exact mul_right_cancel (h.trans (one_mul _).symm)
  have h2 := (rootChar_eq_one_iff_of_comb hk s _).1 h1
  rw [← sub_add_cancel (w • x) x, triPairing_add, h2, zero_add]

end Field

theorem e8ThreeKilledPlaneBlocks_of_QE8
    (hQ : ∀ e : Fin 5 → Fin 3, nfE8 e ^ 3 = 1 → ∀ b : Fin 2 → Fin Tag.E8.rank → ZMod 3,
      (∀ s x, triPairing (b s) (nfE8 e • x) = triPairing (b s) x) → E8PlaneOK (nfE8 e) b) :
    E8ThreeKilledPlaneBlocks := by
  intro L _ a h3 _ w hw3 hstab
  obtain ⟨k, hk⟩ := exists_triPairing_of_pow_three a h3
  have hfam := familyKernel_eq_planeKer hk
  have hwk : ∀ s x, triPairing (k s) (w • x) = triPairing (k s) x :=
    fun s x => triPairing_smul_of_mem_rootCharStabilizer hk (hstab s) x
  obtain ⟨g, hg⟩ := exists_conj_mem_QE8 w ⟨1, by simpa using hw3⟩
  obtain ⟨e, he⟩ := exists_nfE8_of_mem hg
  choose b hb using fun s => exists_triPairing_conj g (k s)
  have hwv : g⁻¹ * nfE8 e * g⁻¹⁻¹ = w := by rw [he]; group
  have hv3 : nfE8 e ^ 3 = 1 := by rw [he, conj_pow, hw3, mul_one, mul_inv_cancel]
  have hvb : ∀ s x, triPairing (b s) (nfE8 e • x) = triPairing (b s) x := by
    intro s x
    rw [hb, hb, he, mul_smul, mul_smul, inv_smul_smul, hwk]
  have hS : ∀ α, α ∈ planeKer k ↔ g⁻¹⁻¹ • α ∈ planeKer b := by
    intro α
    rw [inv_inv, mem_planeKer, mem_planeKer, isRoot_smul_iff, hb, hb, inv_smul_smul]
  have hS' : ∀ α ∈ planeKer b, IsRoot Tag.E8 α := fun α h => (mem_planeKer.1 h).1
  rcases hQ e hv3 b hvb with h | h | ⟨h78, h⟩
  · left
    rw [kernelWeylGroup_eq_closure, kernelRoots_familyChar, hfam,
      closure_rootReflection_eq_map hS' hS, ← hwv]
    exact ⟨nfE8 e, h, rfl⟩
  · right; left
    rw [hfam, ← hwv]
    exact exists_kernelBlocks_conj hS' hS h
  · right; right
    refine ⟨?_, ?_⟩
    · unfold E8KillsSeventyEight
      intro c hc
      have hset : {α : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 α ∧
          rootChar (fun i => a 0 i ^ (c 0).val * a 1 i ^ (c 1).val) α = 1} =
          {α | IsRoot Tag.E8 α ∧ triPairing (c 0 • k 0 + c 1 • k 1) α = 0} := by
        ext α
        simp only [Set.mem_setOf_eq, hk c α]
      rw [hset, ncard_eq_of_mem_iff_inv_smul (t := g⁻¹)
        (S' := {α | IsRoot Tag.E8 α ∧ triPairing (c 0 • b 0 + c 1 • b 1) α = 0}) ?_]
      · exact h78 c hc
      · intro α
        simp only [Set.mem_setOf_eq, inv_inv, isRoot_smul_iff, triPairing_comb, hb,
          inv_smul_smul]
    · rcases h with ⟨h24, hfix, htr, horb⟩ | htri
      · left
        obtain ⟨h1, h2⟩ := orthOrbit_conj hS hfix horb
        change OrthBody (familyKernel a) w
        rw [hfam, ← hwv]
        exact ⟨by rw [ncard_eq_of_mem_iff_inv_smul hS, h24], h1,
          tripleRefl_transitive_conj hS htr, h2⟩
      · right
        unfold E8D4Triangles at htri ⊢
        refine ⟨fun α hα hfixα => htri.1 (g • α) (IsRoot.smul hα g) ?_, ?_⟩
        · rw [he, mul_smul, mul_smul, inv_smul_smul, hfixα]
        · rw [← hwv, trace_conj]
          exact htri.2

theorem e8ThreeKilledPlaneBlocks_of_reps {rt : Array ℕ} (hrt : ReflTable rt)
    {RW : List (List ℕ)} (hRW : ∀ i, ∀ l ∈ RW.getD i [], l < 8)
    (hq : ∀ c < 243, c = 0 ∨
      (∃ x < 8, e8PlanePermOf rt (e8PlaneWord c) (e8PlanePermOf rt (e8PlaneWord c)
        (e8PlanePermOf rt (e8PlaneWord c) x)) ≠ x) ∨
      ∃ i g, (∀ l ∈ g, l < 8) ∧ ∀ j < 8,
        e8PlanePermOf rt (e8PlaneWord c) (e8PlanePermOf rt g j) =
          e8PlanePermOf rt g (e8PlanePermOf rt (RW.getD i []) j))
    (hrep : ∀ i (b : Fin 2 → Fin Tag.E8.rank → ZMod 3),
      (∀ s x, triPairing (b s) (wordR (RW.getD i []) • x) = triPairing (b s) x) →
        E8PlaneOK (wordR (RW.getD i [])) b) :
    E8ThreeKilledPlaneBlocks := by
  refine e8ThreeKilledPlaneBlocks_of_QE8 fun e hv3 b hvb => ?_
  have hc : (e 0 : ℕ) + 3 * (e 1 : ℕ) + 9 * (e 2 : ℕ) + 27 * (e 3 : ℕ) + 81 * (e 4 : ℕ) < 243 := by
    have := (e 0).isLt
    have := (e 1).isLt
    have := (e 2).isLt
    have := (e 3).isLt
    have := (e 4).isLt
    omega
  have hv := e8PlaneWord_prod e
  generalize (e 0 : ℕ) + 3 * (e 1 : ℕ) + 9 * (e 2 : ℕ) + 27 * (e 3 : ℕ) + 81 * (e 4 : ℕ) = c
    at hc hv
  have hw8 : ∀ l ∈ e8PlaneWord c, l < 240 := fun l hl => by
    have := e8PlaneWord_lt c l hl
    omega
  rcases hq c hc with h0 | ⟨x, hx, hne⟩ | ⟨i, g, hg, hcomm⟩
  · have h00 : e8PlaneWord 0 = [] := by decide
    rw [h0, h00, List.map_nil, List.prod_nil] at hv
    rw [← hv]
    exact Or.inl (one_mem _)
  · exfalso
    apply hne
    obtain ⟨h1, e1⟩ := e8PlanePermOf_spec hrt hw8 (x := x) (by omega)
    obtain ⟨h2, e2⟩ := e8PlanePermOf_spec hrt hw8 h1
    obtain ⟨h3, e3⟩ := e8PlanePermOf_spec hrt hw8 h2
    refine e8Certificate_root_inj h3 (by omega) ?_
    rw [e3, e2, e1, hv, smul_smul, smul_smul, ← pow_three', hv3, one_smul]
  · have hg240 : ∀ l ∈ g, l < 240 := fun l hl => by
      have := hg l hl
      omega
    have hr240 : ∀ l ∈ RW.getD i [], l < 240 := fun l hl => by
      have := hRW i l hl
      omega
    have hmul : nfE8 e * wordR g = wordR g * wordR (RW.getD i []) := ext_single fun j => by
      have hj : (j : ℕ) < 8 := j.2
      obtain ⟨a1, ea1⟩ := e8PlanePermOf_spec hrt hg240 (x := j) (by omega)
      obtain ⟨a2, ea2⟩ := e8PlanePermOf_spec hrt hw8 a1
      obtain ⟨b1, eb1⟩ := e8PlanePermOf_spec hrt hr240 (x := j) (by omega)
      obtain ⟨b2, eb2⟩ := e8PlanePermOf_spec hrt hg240 b1
      have hh := congrArg e8Certificate.root (hcomm j hj)
      rw [ea2, ea1, eb2, eb1, e8Certificate_root_single, hv] at hh
      rw [mul_smul, mul_smul]
      exact hh
    have hconj : nfE8 e = wordR g * wordR (RW.getD i []) * (wordR g)⁻¹ := by
      rw [← hmul, mul_inv_cancel_right]
    choose b' hb' using fun s => exists_triPairing_conj (wordR g)⁻¹ (b s)
    have hb'' : ∀ s x, triPairing (b' s) x = triPairing (b s) (wordR g • x) := fun s x => by
      rw [hb', inv_inv]
    have hfix : ∀ s x, triPairing (b' s) (wordR (RW.getD i []) • x) = triPairing (b' s) x := by
      intro s x
      rw [hb'', hb'', ← mul_smul, ← hmul, mul_smul, hvb]
    rw [hconj]
    exact planeOK_conj hb'' (hrep i b' hfix)

end CFSG.KC.E8Plane
