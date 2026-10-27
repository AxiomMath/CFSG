module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.WeylCharStab
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.F4ThreeLangInner

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem ennola_stab_of_frobRoot
    {τ : Tag} {L : Type} [Field L] {D : LangDatum τ L}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρ : FrobRootMap D ρ) {p : ℕ} (hpq : p ∣ D.q + 1)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ D.torus) (ha : ∀ i, a i ^ p = 1)
    {w : WeylGroup τ} (hw : ∀ γ, IsRoot τ γ → ρ γ = -(w • γ)) :
    w ∈ rootCharStabilizerSubgroup a := by
  have hneg : ∀ x : Fin τ.rank → ℤ, rootChar a (-x) = (rootChar a x)⁻¹ := fun x => by
    rw [eq_inv_iff_mul_eq_one, ← rootChar_add, neg_add_cancel, rootChar_zero]
  have hqa : ∀ i, a i ^ (D.q + 1) = 1 := fun i => by
    obtain ⟨m, hm⟩ := hpq
    rw [hm, pow_mul, ha i, one_pow]
  have hone : ∀ x : Fin τ.rank → ℤ, rootChar a x ^ (D.q + 1) = 1 := fun x => by
    have h : rootChar a x ^ (D.q + 1) = ∏ i, (a i ^ (D.q + 1)) ^ x i := by
      simp only [rootChar, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    rw [h]
    exact Finset.prod_eq_one fun i _ => by rw [hqa i, one_zpow]
  refine (mem_rootCharStabilizerSubgroup).2 fun v =>
    rootChar_smul_eq_of_forall_isRoot (fun α hα => ?_) v
  have h1 := hρ.rootChar_eq a hT α hα
  rw [hw α hα, hneg] at h1
  have h2 : rootChar a (w • α) = (rootChar a α ^ D.q)⁻¹ := by rw [← h1, inv_inv]
  rw [h2, inv_eq_iff_mul_eq_one, ← pow_succ]
  exact hone α

theorem kernelReflectionGroup_smul_componentRoots
    {τ : Tag} {L : Type} [Field L]
    {a : Fin τ.rank → Lˣ} {u : WeylGroup τ} (hu : u ∈ kernelReflectionGroup a)
    (i : KernelComponent (rootCharHom a)) :
    (fun γ => u • γ) '' componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i := by
  have key : ∀ {v : WeylGroup τ}, v ∈ kernelReflectionGroup a →
      ∀ γ ∈ componentRoots (rootCharHom a) i, v • γ ∈ componentRoots (rootCharHom a) i := by
    intro v hv γ hγ
    obtain ⟨u', hu'C, hu'⟩ := f4Three_exists_restrict i hv
    rw [hu' γ hγ]
    exact (f4Three_smul_mem_component_iff i hu'C γ).2 hγ
  ext γ
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    exact key hu δ hδ
  · intro hγ
    refine ⟨u⁻¹ • γ, key (inv_mem hu) γ hγ, ?_⟩
    simp

theorem exists_pow_mem_kernelReflectionGroup
    {τ : Tag} {L : Type} [Field L] {p : ℕ} (hp : p.Prime)
    {a : Fin τ.rank → Lˣ} (ha : ∀ i, a i ^ p = 1) {w : WeylGroup τ}
    (hw : w ∈ rootCharStabilizerSubgroup a) : ∃ k : ℕ, w ^ (p ^ k) ∈ kernelReflectionGroup a := by
  obtain ⟨k, hk⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isPGroup_quotient hp ha
    (QuotientGroup.mk (⟨w, hw⟩ : ↥(rootCharStabilizerSubgroup a)))
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hk
  simpa using hk

private lemma ennola_iterate {τ : Tag} {w : WeylGroup τ}
    {ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)}
    (hw : ∀ γ, IsRoot τ γ → ρ γ = -(w • γ)) (m : ℕ) :
    ∀ γ, IsRoot τ γ → ρ^[m] γ = (-1 : ℤ) ^ m • (w ^ m • γ) := by
  induction m with
  | zero => intro γ _; simp
  | succ m ih =>
    intro γ hγ
    have hneg : IsRoot τ (-(w • γ)) := IsRoot.neg (IsRoot.smul hγ w)
    rw [Function.iterate_succ_apply, hw γ hγ, ih (-(w • γ)) hneg]
    simp only [smul_neg, pow_succ, mul_smul, neg_one_smul]

private lemma ennola_iterate_odd {τ : Tag} {w : WeylGroup τ}
    {ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)}
    (hw : ∀ γ, IsRoot τ γ → ρ γ = -(w • γ)) {N : ℕ} (hN : Odd N) :
    ∀ γ, IsRoot τ γ → ρ^[N] γ = -(w ^ N • γ) := by
  intro γ hγ
  rw [ennola_iterate hw N γ hγ, hN.neg_one_pow, neg_one_smul]

private lemma ennola_neg_mem
    {τ : Tag} {L : Type} [Field L] {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ componentRoots (rootCharHom a) i) :
    -γ ∈ componentRoots (rootCharHom a) i := by
  have hr : rootReflection γ ∈ Subgroup.closure {s : WeylGroup τ |
      ∃ δ ∈ componentRoots (rootCharHom a) i, s = rootReflection δ} :=
    Subgroup.subset_closure ⟨γ, hγ, rfl⟩
  have h := (f4Three_smul_mem_component_iff i hr γ).2 hγ
  rwa [rootReflection_smul_self (isRoot_of_mem_componentRoots hγ)] at h

private lemma ennola_image_eq_of_period
    {τ : Tag} {L : Type} [Field L]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {u : WeylGroup τ}
    (hu : (fun γ => u • γ) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (huinv : (fun γ => u⁻¹ • γ) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i) {N : ℕ}
    (hper : ∀ γ ∈ componentRoots (rootCharHom a) i,
      (ρ : (Fin τ.rank → ℤ) → _)^[N] γ = -(u • γ)) :
    (ρ : (Fin τ.rank → ℤ) → _)^[N] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i := by
  ext δ
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    rw [hper γ hγ]
    exact ennola_neg_mem i (hu ▸ ⟨γ, hγ, rfl⟩)
  · intro hδ
    have hmem : u⁻¹ • δ ∈ componentRoots (rootCharHom a) i :=
      huinv ▸ ⟨δ, hδ, rfl⟩
    have hγ : -(u⁻¹ • δ) ∈ componentRoots (rootCharHom a) i := ennola_neg_mem i hmem
    refine ⟨-(u⁻¹ • δ), hγ, ?_⟩
    rw [hper _ hγ]
    simp only [smul_neg, smul_inv_smul, neg_neg]

private lemma ennola_dvd_of_period {α : Type*} (f : α → α) {Ψ : Set α} {N : ℕ}
    (hN : 0 < N) (hper : f^[N] '' Ψ = Ψ) :
    sInf {s : ℕ | 0 < s ∧ f^[s] '' Ψ = Ψ} ∣ N := by
  set P : Set ℕ := {s : ℕ | 0 < s ∧ f^[s] '' Ψ = Ψ} with hPdef
  have hne : P.Nonempty := ⟨N, hN, hper⟩
  have hs : sInf P ∈ P := Nat.sInf_mem hne
  have hperiod : ∀ t : ℕ, f^[sInf P * t] '' Ψ = Ψ := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Nat.mul_succ, Function.iterate_add, Set.image_comp, hs.2, ih]
  by_contra hnd
  have hmod : N % sInf P ≠ 0 := fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)
  have hlt : N % sInf P < sInf P := Nat.mod_lt _ hs.1
  have hmem : N % sInf P ∈ P := by
    refine ⟨Nat.pos_of_ne_zero hmod, ?_⟩
    calc f^[N % sInf P] '' Ψ
        = f^[N % sInf P] '' (f^[sInf P * (N / sInf P)] '' Ψ) := by
            rw [hperiod (N / sInf P)]
      _ = f^[N % sInf P + sInf P * (N / sInf P)] '' Ψ := by
            rw [Function.iterate_add, Set.image_comp]
      _ = f^[N] '' Ψ := by rw [Nat.mod_add_div]
      _ = Ψ := hper
  have hle : sInf P ≤ N % sInf P := Nat.sInf_le hmem
  omega

theorem ennola_orbit_odd
    {τ : Tag} {L : Type} [Field L] {D : LangDatum τ L}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρ : FrobRootMap D ρ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ D.q + 1) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ D.torus)
    (ha : ∀ i, a i ^ p = 1) {w : WeylGroup τ} (hw : ∀ γ, IsRoot τ γ → ρ γ = -(w • γ))
    (i : KernelComponent (rootCharHom a)) :
    Odd (componentOrbitLength ρ (componentRoots (rootCharHom a) i)) := by
  have hwa : w ∈ rootCharStabilizerSubgroup a :=
    ennola_stab_of_frobRoot hρ hpq hT ha hw
  obtain ⟨k, hk⟩ := exists_pow_mem_kernelReflectionGroup hp ha hwa
  set N : ℕ := p ^ k with hNdef
  have hNpos : 0 < N := by rw [hNdef]; exact pow_pos hp.pos k
  have hNodd : Odd N := by
    rw [hNdef]
    exact (hp.odd_of_ne_two hp2).pow
  set u : WeylGroup τ := w ^ N with hudef
  have hu : u ∈ kernelReflectionGroup a := by rw [hudef, hNdef]; exact hk
  have hwcm : (fun γ => u • γ) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i :=
    kernelReflectionGroup_smul_componentRoots hu i
  have hwcm_inv : (fun γ => u⁻¹ • γ) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i :=
    kernelReflectionGroup_smul_componentRoots (inv_mem hu) i
  have hper : ∀ γ ∈ componentRoots (rootCharHom a) i,
      (ρ : (Fin τ.rank → ℤ) → _)^[N] γ = -(u • γ) := by
    intro γ hγ
    have h := ennola_iterate_odd (τ := τ) hw hNodd γ (isRoot_of_mem_componentRoots hγ)
    rw [h, hudef]
  have himg : (ρ : (Fin τ.rank → ℤ) → _)^[N] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i :=
    ennola_image_eq_of_period i hwcm hwcm_inv hper
  rw [componentOrbitLength]
  exact Odd.of_dvd_nat hNodd
    (ennola_dvd_of_period (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) hNpos himg)

end CFSG.HardMathSupport.Timmesfeld.LangTorus

end
