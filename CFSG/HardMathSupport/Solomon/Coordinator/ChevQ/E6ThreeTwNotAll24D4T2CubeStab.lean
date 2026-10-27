module

public import Certificates.Certificate214103
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Lattice
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.Blueprint.Chevalley.RootCertificate CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LieType.AlgebraicGroups


theorem twD4T2StabCheck_spec {k : ℕ} (hk : k < 3 ^ Tag.E6.rank)
    {e : ℕ × ℕ × ℕ} (he : e ∈ twD4T2Elems)
    (hfix : twD4T2Fixes (vec3OfIndex (τ := .E6) k) (decodeT Tag.E6.rank e.1) = true)
    (hpos : twD4T2PosOK (vec3OfIndex (τ := .E6) k) (twD4T2Sig ()) (decodeT Tag.E6.rank e.1) =
      true) :
    decodeT Tag.E6.rank e.1 = List.range Tag.E6.rank := by
  have h := Certificates.certificate214103
  unfold twD4T2StabCheck at h
  simp only [List.all_eq_true, List.mem_range] at h
  have h1 := h k hk e he
  rw [hfix, hpos, Bool.and_self, Bool.not_true, Bool.false_or, beq_iff_eq] at h1
  exact h1

theorem twMem_kernelRoots_prod {f c : Fin Tag.E6.rank → ZMod 3} {α : Fin Tag.E6.rank → ℤ} :
    α ∈ kernelRoots ((triChar f).prod (triChar c)) ↔
      IsRoot .E6 α ∧ triPairing f α = 0 ∧ triPairing c α = 0 := by
  refine Iff.trans Iff.rfl (and_congr_right fun _ => ?_)
  rw [MonoidHom.prod_apply, Prod.mk_eq_one, triChar_apply, triChar_apply, Z3.ofAdd_eq_one,
    Z3.ofAdd_eq_one]

theorem twMem_charStabilizer_prod {f c : Fin Tag.E6.rank → ZMod 3} {w : WeylGroup .E6} :
    w ∈ charStabilizer ((triChar f).prod (triChar c)) ↔
      w ∈ charStabilizer (triChar f) ∧ w ∈ charStabilizer (triChar c) := by
  simp only [mem_charStabilizer, MonoidHom.prod_apply, Prod.mk.injEq, forall_and]

theorem twKernelWeylGroup_prod_le {f c : Fin Tag.E6.rank → ZMod 3} :
    kernelWeylGroup ((triChar f).prod (triChar c)) ≤ kernelWeylGroup (triChar f) := by
  unfold kernelWeylGroup
  refine Subgroup.closure_mono ?_
  rintro _ ⟨w, i, hα, rfl⟩
  obtain ⟨h1, h2, -⟩ := twMem_kernelRoots_prod.1 hα
  exact ⟨w, i, mem_kernelRoots_triChar.2 ⟨h1, h2⟩, rfl⟩

theorem twD4T2Fixes_of_mem_charStabilizer {c : Fin Tag.E6.rank → ZMod 3} {t : List ℕ}
    {w : WeylGroup .E6} (hrep : e6Certificate.Represents t w)
    (hw : w ∈ charStabilizer (triChar c)) : twD4T2Fixes c t = true := by
  simp only [twD4T2Fixes, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]
  intro j
  have h := hw (Pi.single j 1 : Fin Tag.E6.rank → ℤ)
  rw [triChar_apply, triChar_apply] at h
  rw [(hrep.2 j).2, Z3.ofAdd_eq_ofAdd_iff.1 h, twTriPairing_single]

theorem twD4T2_stab_f0
    {c : Fin Tag.E6.rank → ZMod 3} {u : WeylGroup .E6}
    (hu : u ∈ kernelWeylGroup (triChar (vec3 (τ := .E6) twD4T2F0)))
    (hc : u ∈ charStabilizer (triChar c)) :
    u ∈ kernelWeylGroup ((triChar (vec3 (τ := .E6) twD4T2F0)).prod (triChar c)) := by
  obtain ⟨k, hk, rfl⟩ := exists_vec3OfIndex (τ := .E6) c
  set χ := (triChar (vec3 (τ := .E6) twD4T2F0)).prod (triChar (vec3OfIndex (τ := .E6) k))
    with hχ
  obtain ⟨v, hv, hω⟩ := exists_mul_mem_kernelPosStabilizer
    (twMem_charStabilizer_prod.2 ⟨kernelWeylGroup_le hu, hc⟩ : u ∈ charStabilizer χ)
  obtain ⟨e, he, hrep⟩ := twD4T2_exists_elem (mul_mem hu (twKernelWeylGroup_prod_le hv))
  have hfix := twD4T2Fixes_of_mem_charStabilizer hrep (twMem_charStabilizer_prod.1 hω.1).2
  have hpos : twD4T2PosOK (vec3OfIndex (τ := .E6) k) (twD4T2Sig ())
      (decodeT Tag.E6.rank e.1) = true := by
    simp only [twD4T2PosOK, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq]
    intro p hp
    by_cases h0 : triPairing (vec3OfIndex (τ := .E6) k) (e6Certificate.root p) = 0 ∧
        0 < height (e6Certificate.root p)
    · right
      have hp' := hp
      unfold twD4T2Sig at hp'
      obtain ⟨hp1, hp2⟩ := List.mem_filter.1 hp'
      have hβ : e6Certificate.root p ∈ posRoots (kernelRoots χ) :=
        ⟨twMem_kernelRoots_prod.2 ⟨isRoot_root e6Certificate_check p (List.mem_range.1 hp1),
          of_decide_eq_true hp2, h0.1⟩, h0.2⟩
      have himg : (u * v) • e6Certificate.root p ∈ posRoots (kernelRoots χ) := by
        rw [← hω.2]
        exact ⟨_, hβ, rfl⟩
      rw [tupleVec_eq hrep]
      exact himg.2
    · left
      by_cases h1 : triPairing (vec3OfIndex (τ := .E6) k) (e6Certificate.root p) = 0
      · exact Or.inr fun h2 => h0 ⟨h1, h2⟩
      · exact Or.inl h1
  have hid := twD4T2StabCheck_spec hk he hfix hpos
  rw [hid] at hrep
  have h1 : u * v = 1 := represents_unique hrep (represents_one e6Certificate_check)
  rw [eq_inv_of_mul_eq_one_left h1]
  exact inv_mem hv

theorem twD4T2_stab
    {f c : Fin Tag.E6.rank → ZMod 3}
    (h24 : {α | IsRoot .E6 α ∧ triPairing f α = 0}.ncard = 24) {u : WeylGroup .E6}
    (hu : u ∈ kernelWeylGroup (triChar f)) (hc : u ∈ charStabilizer (triChar c)) :
    u ∈ kernelWeylGroup ((triChar f).prod (triChar c)) := by
  obtain ⟨ρ, hρ, t, ht⟩ := exists_isCharConj_of_orbitCheck3 e6ThreeScCheck_spec.1 (triChar f)
  have hpair : ∀ v, triPairing f v =
      triPairing (vec3 (τ := .E6) (e6ThreeReps.getD ρ [])) (t⁻¹ • v) := fun v => by
    have h := ht v
    rw [triChar_apply, triChar_apply] at h
    exact Z3.ofAdd_eq_ofAdd_iff.1 h
  obtain rfl : ρ = 6 := twD4T2_rep_eq_six hρ (by rw [← twNcard_kernel_conj hpair]; exact h24)
  have hrep : e6ThreeReps.getD 6 [] = twD4T2F0 := rfl
  rw [hrep] at ht
  obtain ⟨c', hc'⟩ := twExists_triPairing_comp c t
  have hcc : IsCharConj (triChar c') (triChar c) t := fun v => by
    rw [triChar_apply, triChar_apply, hc', smul_inv_smul]
  have hk : t⁻¹ * u * t ∈ kernelWeylGroup (triChar (vec3 (τ := .E6) twD4T2F0)) := by
    rw [kernelWeylGroup_eq_map ht, Subgroup.mem_map] at hu
    obtain ⟨y, hy, hyu⟩ := hu
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyu
    rw [← hyu]
    simpa [mul_assoc] using hy
  have h0 := twD4T2_stab_f0 hk ((charStabilizer_iff_of_isCharConj hcc).1 hc)
  have hprod : IsCharConj ((triChar (vec3 (τ := .E6) twD4T2F0)).prod (triChar c'))
      ((triChar f).prod (triChar c)) t := fun v => by
    rw [MonoidHom.prod_apply, MonoidHom.prod_apply, ht v, hcc v]
  rw [kernelWeylGroup_eq_map hprod, Subgroup.mem_map]
  exact ⟨_, h0, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

theorem d4t2_stab_mem_kernelWeylGroup
    {L : Type} [Field L]
    {a b : Fin Tag.E6.rank → Lˣ} (ha : ∀ i, a i ^ 3 = 1) (hb : ∀ i, b i ^ 3 = 1)
    (h24 : (kernelRoots (rootCharHom a)).ncard = 24) {w : WeylGroup .E6}
    (hwa : w ∈ kernelReflectionGroup a) (hwb : w ∈ rootCharStabilizer b) :
    w ∈ kernelWeylGroup (familyChar ![a, b]) := by
  obtain ⟨χa, hχa⟩ := exists_triChar_ker_eq (rootCharHom3 a) (rootCharHom3_pow_three a ha)
  obtain ⟨χb, hχb⟩ := exists_triChar_ker_eq (rootCharHom3 b) (rootCharHom3_pow_three b hb)
  obtain ⟨fa, rfl⟩ : ∃ fa, χa = triChar fa := ⟨_, eq_triChar χa⟩
  obtain ⟨fb, rfl⟩ : ∃ fb, χb = triChar fb := ⟨_, eq_triChar χb⟩
  have hwa' : w ∈ kernelWeylGroup (triChar fa) := by
    rw [← kernelWeylGroup_congr_ker hχa]
    exact hwa
  have hwb' : w ∈ charStabilizer (triChar fb) := by
    rw [← charStabilizer_congr_ker hχb]
    exact hwb
  have h24' : {α | IsRoot .E6 α ∧ triPairing fa α = 0}.ncard = 24 := by
    have hk : kernelRoots (rootCharHom a) = {α | IsRoot .E6 α ∧ triPairing fa α = 0} := by
      ext α
      rw [Set.mem_setOf_eq, ← mem_kernelRoots_triChar, ← kernelRoots_congr_ker hχa]
      exact Iff.rfl
    rw [← hk]
    exact h24
  have h := twD4T2_stab h24' hwa' hwb'
  rwa [kernelWeylGroup_congr_ker (χ' := familyChar ![a, b]) fun x => ?_] at h
  rw [MonoidHom.prod_apply, Prod.mk_eq_one, ← hχa, ← hχb]
  constructor
  · rintro ⟨h1, h2⟩
    funext i
    fin_cases i
    · exact h1
    · exact h2
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
