module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootGroup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus Matrix

set_option linter.unusedSectionVars false

section Pure

variable {τ : Tag}

theorem kc_perm_apply_inv {α : Type*} (f : Equiv.Perm α) (x : α) : f (f⁻¹ x) = x :=
  Equiv.apply_symm_apply f x

theorem kc_perm_inv_apply {α : Type*} (f : Equiv.Perm α) (x : α) : f⁻¹ (f x) = x :=
  Equiv.symm_apply_apply f x

theorem kc_stab_pow {S : Set (Fin τ.rank → ℤ)} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (h1 : ∀ a ∈ S, ρ a ∈ S) (h2 : ∀ a ∈ S, ρ⁻¹ a ∈ S) (i : ℕ) :
    (∀ a ∈ S, (ρ ^ i) a ∈ S) ∧ (∀ a ∈ S, (ρ ^ i)⁻¹ a ∈ S) := by
  induction i with
  | zero =>
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · rw [pow_zero, Equiv.Perm.one_apply]
      exact ha
    · rw [pow_zero, inv_one, Equiv.Perm.one_apply]
      exact ha
  | succ i ih =>
    obtain ⟨hi1, hi2⟩ := ih
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · rw [pow_succ, Equiv.Perm.mul_apply]
      exact hi1 _ (h1 a ha)
    · rw [pow_succ, _root_.mul_inv_rev, Equiv.Perm.mul_apply]
      exact h2 _ (hi2 a ha)

theorem kc_iform_pow {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hiso : ∀ a b, iform (ρ a) (ρ b) = iform a b) (i : ℕ) (a b : Fin τ.rank → ℤ) :
    iform ((ρ ^ i) a) ((ρ ^ i) b) = iform a b := by
  induction i with
  | zero => rw [pow_zero, Equiv.Perm.one_apply, Equiv.Perm.one_apply]
  | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hiso, ih]

theorem kc_iform_pow_inv {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hiso : ∀ a b, iform (ρ a) (ρ b) = iform a b) (i : ℕ) (a b : Fin τ.rank → ℤ) :
    iform ((ρ ^ i)⁻¹ a) ((ρ ^ i)⁻¹ b) = iform a b := by
  have h := kc_iform_pow hiso i ((ρ ^ i)⁻¹ a) ((ρ ^ i)⁻¹ b)
  rw [kc_perm_apply_inv, kc_perm_apply_inv] at h
  exact h.symm

def kcSeq {L : Type} [Field L] (s : ℕ → L) (q : ℕ) (t₀ : L) : ℕ → L
  | 0 => t₀
  | k + 1 => s k * (kcSeq s q t₀ k) ^ q

theorem kc_kcSeq_affine {L : Type} [Field L] (s : ℕ → L) (hs : ∀ k, s k ≠ 0) (q : ℕ) :
    ∀ n : ℕ, ∃ S : L, S ≠ 0 ∧ ∀ t₀ : L, kcSeq s q t₀ n = S * t₀ ^ (q ^ n)
  | 0 => ⟨1, one_ne_zero, fun t₀ => by simp [kcSeq]⟩
  | n + 1 => by
    obtain ⟨S, hS, hf⟩ := kc_kcSeq_affine s hs q n
    refine ⟨s n * S ^ q, mul_ne_zero (hs n) (pow_ne_zero _ hS), fun t₀ => ?_⟩
    simp only [kcSeq]
    rw [hf, mul_pow, ← pow_mul, pow_succ]
    ring

theorem kc_exists_kcSeq_fixed {L : Type} [Field L] [IsAlgClosed L] (s : ℕ → L)
    (hs : ∀ k, s k ≠ 0) {q n : ℕ} (hq : 2 ≤ q) (hn : 0 < n) :
    ∃ t₀ : L, t₀ ≠ 0 ∧ kcSeq s q t₀ n = t₀ := by
  obtain ⟨S, hS, hf⟩ := kc_kcSeq_affine s hs q n
  have hqn : 2 ≤ q ^ n := le_trans hq (Nat.le_self_pow hn.ne' q)
  obtain ⟨t₀, ht₀⟩ := IsAlgClosed.exists_pow_nat_eq S⁻¹ (show 0 < q ^ n - 1 by omega)
  have ht0 : t₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at ht₀
    exact inv_ne_zero hS ht₀.symm
  refine ⟨t₀, ht0, ?_⟩
  rw [hf, show q ^ n = (q ^ n - 1) + 1 by omega, pow_succ, ht₀, ← mul_assoc,
    mul_inv_cancel₀ hS, one_mul]

end Pure

section Cycle


variable {τ : Tag}

theorem kc_mk_map {M : Type*} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (σ : Equiv.Perm (Fin τ.rank → ℤ)) (hσ : ∀ a ∈ kernelRoots χ, σ a ∈ kernelRoots χ)
    (hiso : ∀ a b, iform (σ a) (σ b) = iform a b)
    {a b : Fin τ.rank → ℤ} (ha : a ∈ kernelRoots χ) (hb : b ∈ kernelRoots χ)
    (h : (⟦⟨a, ha⟩⟧ : KernelComponent χ) = ⟦⟨b, hb⟩⟧) :
    (⟦⟨σ a, hσ a ha⟩⟧ : KernelComponent χ) = ⟦⟨σ b, hσ b hb⟩⟧ := by
  let g : kernelRoots χ → kernelRoots χ := fun c => ⟨σ (c : Fin τ.rank → ℤ), hσ c c.2⟩
  have hrel : ∀ c d : kernelRoots χ,
      (c : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (d : Fin τ.rank → ℤ)) ≠ 0 →
        (g c : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (g d : Fin τ.rank → ℤ)) ≠ 0 := by
    intro c d hcd
    rw [dotProduct_mulVec_eq_iform] at hcd ⊢
    show iform (σ (c : Fin τ.rank → ℤ)) (σ (d : Fin τ.rank → ℤ)) ≠ 0
    rw [hiso]
    exact hcd
  have key : Relation.EqvGen (fun c d : kernelRoots χ =>
      (c : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (d : Fin τ.rank → ℤ)) ≠ 0)
      ⟨a, ha⟩ ⟨b, hb⟩ :=
    Quotient.exact h
  exact Quotient.sound (kr_eqvGen_map hrel key)

theorem kc_exists_kill_root_cycle (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {M : Type*} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ1 : ∀ a ∈ kernelRoots χ, ρ a ∈ kernelRoots χ)
    (hρ2 : ∀ a ∈ kernelRoots χ, ρ⁻¹ a ∈ kernelRoots χ)
    (hiso : ∀ a b, iform (ρ a) (ρ b) = iform a b)
    {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots χ) :
    ∃ x ∈ Subgroup.closure (rootReflection '' kernelRoots χ), ∃ (n : ℕ) (hn : 0 < n),
      ∃ β : Fin n → Fin τ.rank → ℤ, β ⟨0, hn⟩ = α ∧ (∀ k, β k ∈ kernelRoots χ) ∧
        (∀ i j, i ≠ j → iform (β i) (β j) = 0 ∧ β i ≠ β j ∧ β i ≠ -β j ∧
          ∀ a b : ℕ, 0 < a → 0 < b → ¬ IsRoot τ (a • β i + b • β j)) ∧
        ∀ k : Fin n, x • ρ (β k) = β ⟨((k : ℕ) + 1) % n, Nat.mod_lt _ hn⟩ := by
  classical
  have hP := kc_stab_pow hρ1 hρ2
  have hr : ∀ m : ℕ, (ρ ^ m) α ∈ kernelRoots χ := fun m => (hP m).1 α hα
  obtain ⟨cl, hcl⟩ : ∃ cl : ℕ → KernelComponent χ,
      ∀ m, cl m = ⟦⟨(ρ ^ m) α, hr m⟩⟧ := ⟨_, fun m => rfl⟩
  have hfinS : (kernelRoots χ).Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1
  haveI : Finite (kernelRoots χ) := hfinS.to_subtype
  obtain ⟨i₀, j₀, hij₀, hfij⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun m : ℕ => (⟨(ρ ^ m) α, hr m⟩ : kernelRoots χ))
  have hper : ∀ i j : ℕ, i < j → (ρ ^ i) α = (ρ ^ j) α → (ρ ^ (j - i)) α = α := by
    intro i j hij h
    have e : ρ ^ j = ρ ^ i * ρ ^ (j - i) := by
      rw [← pow_add]
      congr 1
      omega
    rw [e, Equiv.Perm.mul_apply] at h
    exact ((ρ ^ i).injective h).symm
  obtain ⟨N, hNpos, hNeq⟩ : ∃ N, 0 < N ∧ (ρ ^ N) α = α := by
    have h' : (ρ ^ i₀) α = (ρ ^ j₀) α := congrArg Subtype.val hfij
    rcases Nat.lt_or_gt_of_ne hij₀ with h | h
    · exact ⟨j₀ - i₀, by omega, hper i₀ j₀ h h'⟩
    · exact ⟨i₀ - j₀, by omega, hper j₀ i₀ h h'.symm⟩
  have hex : ∃ m, 0 < m ∧ cl m = ⟦⟨α, hα⟩⟧ :=
    ⟨N, hNpos, (hcl N).trans (kr_mk_of_eq (hr N) hα hNeq)⟩
  obtain ⟨n, hn0, hncl, hmin⟩ : ∃ n, 0 < n ∧ cl n = ⟦⟨α, hα⟩⟧ ∧
      ∀ m, 0 < m → m < n → cl m ≠ ⟦⟨α, hα⟩⟧ :=
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      fun m hm0 hmn hc => Nat.find_min hex hmn ⟨hm0, hc⟩⟩
  have hdist : ∀ i j : ℕ, i < j → j < n → cl i ≠ cl j := by
    intro i j hij hjn heq
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij.le
    have hd : 0 < d := by omega
    have hdn : d < n := by omega
    have c1 : (⟦⟨α, hα⟩⟧ : KernelComponent χ) =
        ⟦⟨(ρ ^ i)⁻¹ ((ρ ^ i) α), (hP i).2 _ (hr i)⟩⟧ :=
      kr_mk_of_eq hα ((hP i).2 _ (hr i)) (kc_perm_inv_apply (ρ ^ i) α).symm
    have c2 : (⟦⟨(ρ ^ i)⁻¹ ((ρ ^ i) α), (hP i).2 _ (hr i)⟩⟧ : KernelComponent χ) =
        ⟦⟨(ρ ^ i)⁻¹ ((ρ ^ (i + d)) α), (hP i).2 _ (hr (i + d))⟩⟧ :=
      kc_mk_map χ ((ρ ^ i)⁻¹) (hP i).2 (kc_iform_pow_inv hiso i) (hr i) (hr (i + d))
        ((hcl i).symm.trans (heq.trans (hcl (i + d))))
    have c3 : (⟦⟨(ρ ^ i)⁻¹ ((ρ ^ (i + d)) α), (hP i).2 _ (hr (i + d))⟩⟧ :
        KernelComponent χ) = ⟦⟨(ρ ^ d) α, hr d⟩⟧ :=
      kr_mk_of_eq ((hP i).2 _ (hr (i + d))) (hr d)
        (by rw [pow_add, Equiv.Perm.mul_apply, kc_perm_inv_apply])
    exact hmin d hd hdn ((hcl d).trans (c1.trans (c2.trans c3)).symm)
  have hdistc : ∀ i j : ℕ, i < n → j < n → i ≠ j →
      (⟦⟨(ρ ^ i) α, hr i⟩⟧ : KernelComponent χ) ≠ ⟦⟨(ρ ^ j) α, hr j⟩⟧ := by
    intro i j hi hj hij heq
    have hcl_eq : cl i = cl j := (hcl i).trans (heq.trans (hcl j).symm)
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact hdist i j h hj hcl_eq
    · exact hdist j i h hi hcl_eq.symm
  have hαΨ : α ∈ componentRoots χ ⟦⟨α, hα⟩⟧ := ⟨hα, rfl⟩
  have hρnΨ : (ρ ^ n) α ∈ componentRoots χ ⟦⟨α, hα⟩⟧ :=
    ⟨hr n, (hcl n).symm.trans hncl⟩
  obtain ⟨x0, hx0, hx0α⟩ :=
    kr_smul_of_mem_component hτ (isRootComponent_componentRoots (χ := χ) ⟦⟨α, hα⟩⟧) hρnΨ hαΨ
  have hfix : ∀ m : ℕ, 0 < m → m < n → x0 • ((ρ ^ m) α) = (ρ ^ m) α := by
    intro m hm0 hmn
    refine kr_fix_of_orth hx0 (fun γ hγ => ?_)
    obtain ⟨hγk, hγc⟩ := hγ
    refine iform_eq_zero_of_mk_ne (α := ⟨γ, hγk⟩) (β := ⟨(ρ ^ m) α, hr m⟩) ?_
    intro hne
    exact hmin m hm0 hmn ((hcl m).trans (hne.symm.trans hγc))
  refine ⟨x0, kr_componentWeylGroup_le _ hx0, n, hn0, fun k => (ρ ^ (k : ℕ)) α, ?_,
    fun k => hr k, ?_, ?_⟩
  · show (ρ ^ 0) α = α
    rw [pow_zero, Equiv.Perm.one_apply]
  · intro i j hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun e => hij (Fin.ext e)
    have hc := hdistc (i : ℕ) (j : ℕ) i.2 j.2 hne
    have h0 : iform ((ρ ^ (i : ℕ)) α) ((ρ ^ (j : ℕ)) α) = 0 :=
      iform_eq_zero_of_mk_ne (α := ⟨(ρ ^ (i : ℕ)) α, hr i⟩) (β := ⟨(ρ ^ (j : ℕ)) α, hr j⟩) hc
    refine ⟨h0, fun h => hc (kr_mk_of_eq (hr i) (hr j) h), ?_,
      fun a b ha hb => not_isRoot_of_mk_ne hc ha hb⟩
    intro h
    have h' : (ρ ^ (i : ℕ)) α = -((ρ ^ (j : ℕ)) α) := h
    have hv := kr_iform_self hτ (hr j).1
    have hneg := iform_smul_left (-1 : ℤ) ((ρ ^ (j : ℕ)) α) ((ρ ^ (j : ℕ)) α)
    rw [neg_one_smul, hv] at hneg
    rw [h'] at h0
    linarith
  · intro k
    show x0 • ρ ((ρ ^ (k : ℕ)) α) = (ρ ^ (((k : ℕ) + 1) % n)) α
    have e1 : ρ ((ρ ^ (k : ℕ)) α) = (ρ ^ ((k : ℕ) + 1)) α := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    rw [e1]
    by_cases hkn : (k : ℕ) + 1 < n
    · rw [Nat.mod_eq_of_lt hkn]
      exact hfix _ (by omega) hkn
    · have hk : (k : ℕ) + 1 = n := by omega
      rw [hk, Nat.mod_self, pow_zero, Equiv.Perm.one_apply]
      exact hx0α

theorem kc_kill_cycle_periodic {L : Type} [Field L] {ι : Type}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (a : ι → Fin τ.rank → Lˣ)
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (h1 : ∀ δ ∈ familyKernel a, ρ δ ∈ familyKernel a)
    (h2 : ∀ δ ∈ familyKernel a, ρ⁻¹ δ ∈ familyKernel a)
    (hiso : ∀ δ ε, iform (ρ δ) (ρ ε) = iform δ ε)
    {α : Fin τ.rank → ℤ} (hα : α ∈ familyKernel a) :
    ∃ x ∈ Subgroup.closure (rootReflection '' familyKernel a), ∃ (n : ℕ)
      (β : ℕ → Fin τ.rank → ℤ), 0 < n ∧ (∀ k, β (k + n) = β k) ∧
      (∀ k, β k ∈ familyKernel a) ∧
      (∀ k l, k < n → l < n → k ≠ l →
        iform (β k) (β l) = 0 ∧ β k ≠ β l ∧ ¬ IsRoot τ (β k + β l)) ∧
      ∀ k, x • ρ (β k) = β (k + 1) := by
  have hker := kernelRoots_familyChar a
  obtain ⟨x, hx, n, hn, β, -, hβS, horth, hgβ⟩ := kc_exists_kill_root_cycle hτ (familyChar a) ρ
    (fun δ hδ => by rw [hker] at hδ ⊢; exact h1 δ hδ)
    (fun δ hδ => by rw [hker] at hδ ⊢; exact h2 δ hδ) hiso (by rw [hker]; exact hα)
  rw [hker] at hx hβS
  refine ⟨x, hx, n, fun k => β ⟨k % n, Nat.mod_lt _ hn⟩, hn, ?_, ?_, ?_, ?_⟩
  · intro k
    show β ⟨(k + n) % n, Nat.mod_lt _ hn⟩ = β ⟨k % n, Nat.mod_lt _ hn⟩
    congr 1
    exact Fin.ext (Nat.add_mod_right k n)
  · intro k
    exact hβS _
  · intro k l hk hl hkl
    have hkl' : (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n) ≠ ⟨l % n, Nat.mod_lt _ hn⟩ := by
      intro h
      apply hkl
      have h' := congrArg Fin.val h
      simp only [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hl] at h'
      exact h'
    have h := horth ⟨k % n, Nat.mod_lt _ hn⟩ ⟨l % n, Nat.mod_lt _ hn⟩ hkl'
    refine ⟨h.1, h.2.1, ?_⟩
    have h11 := h.2.2.2 1 1 one_pos one_pos
    simpa using h11
  · intro k
    show x • ρ (β ⟨k % n, Nat.mod_lt _ hn⟩) = β ⟨(k + 1) % n, Nat.mod_lt _ hn⟩
    refine (hgβ ⟨k % n, Nat.mod_lt _ hn⟩).trans ?_
    congr 1
    exact Fin.ext (Nat.mod_add_mod k n 1)

end Cycle

section Element


variable {τ : Tag}

theorem kc_exists_cycle_element {L : Type} [Field L] [IsAlgClosed L] (r : ℕ) [Fact r.Prime]
    [CharP L r] {q : ℕ} (hq : 2 ≤ q) (F : ModGL τ L →* ModGL τ L) (n : ℕ) (hn : 0 < n)
    (β : ℕ → Fin τ.rank → ℤ) (hper : ∀ k, β (k + n) = β k) (hroot : ∀ k, IsRoot τ (β k))
    (horth : ∀ k l, k < n → l < n → k ≠ l →
      iform (β k) (β l) = 0 ∧ β k ≠ β l ∧ ¬ IsRoot τ (β k + β l))
    (m : ℕ → L) (hm0 : ∀ k, m k ≠ 0)
    (hF : ∀ k (c : L), F (pinnedX τ L (β k) c) = pinnedX τ L (β (k + 1)) (m k * c ^ q))
    (S : Set (Fin τ.rank → ℤ)) (hS : ∀ k, β k ∈ S) :
    ∃ v : ModGL τ L, v ∈ rootSpan τ L S ∧ F v = v ∧ v ≠ 1 ∧ v ^ r = 1 := by
  obtain ⟨t₀, ht₀, hfix⟩ := kc_exists_kcSeq_fixed m hm0 hq hn
  obtain ⟨t, ht⟩ : ∃ t : ℕ → L, t = kcSeq m q t₀ := ⟨_, rfl⟩
  have ht0 : t 0 = t₀ := by rw [ht]; rfl
  have htsucc : ∀ k, t (k + 1) = m k * (t k) ^ q := fun k => by rw [ht]; rfl
  have htn : t n = t₀ := by rw [ht]; exact hfix
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ModGL τ L, ∀ k, f k = pinnedX τ L (β k) (t k) :=
    ⟨_, fun k => rfl⟩
  have hG : ∀ k, F (f k) = f (k + 1) := by
    intro k
    rw [hf, hF, hf, htsucc k]
  have hGv : F (((List.range n).map f).prod) =
      ((List.range n).map (fun k => f (k + 1))).prod := by
    rw [map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hG k
  have hcomm : ∀ i j, i < n → j < n → i ≠ j → Commute (f i) (f j) := by
    intro i j hi hj hij
    rw [hf, hf]
    exact pinnedX_commute_of_iform_eq_zero L (hroot i) (hroot j) (horth i j hi hj hij).1
      (horth i j hi hj hij).2.2 (t i) (t j)
  have hcomm0 : ∀ k, k < n → Commute (f 0) (f k) := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      exact Commute.refl _
    · exact hcomm 0 k (by omega) hk (Ne.symm hk0)
  have hPcomm : Commute (f 0) ((List.range n).map f).prod := by
    apply Commute.list_prod_right
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact hcomm0 k (List.mem_range.1 hk)
  have hL1 : ((List.range (n + 1)).map f).prod =
      f 0 * ((List.range n).map (fun k => f (k + 1))).prod := by
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
    rfl
  have hL2 : ((List.range (n + 1)).map f).prod = ((List.range n).map f).prod * f n := by
    rw [List.range_succ, List.map_append, List.prod_append]
    simp
  have hfn : f n = f 0 := by
    rw [hf, hf]
    have hβn : β n = β 0 := by simpa using hper 0
    have htn' : t n = t 0 := by rw [htn, ht0]
    rw [hβn, htn']
  have hP' : ((List.range n).map (fun k => f (k + 1))).prod = ((List.range n).map f).prod := by
    have key : f 0 * ((List.range n).map (fun k => f (k + 1))).prod =
        f 0 * ((List.range n).map f).prod := by
      rw [← hL1, hL2, hfn, hPcomm.eq]
    exact mul_left_cancel key
  have hmem : ((List.range n).map f).prod ∈ rootSpan τ L S := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    rw [hf]
    have hle : rootSubgroup τ L (β k) ≤ rootSpan τ L S :=
      le_iSup₂_of_le (f := fun α (_ : α ∈ S) => rootSubgroup τ L α) (β k) (hS k) le_rfl
    exact hle (Subgroup.subset_closure ⟨t k, rfl⟩)
  have hconv : ∀ g' : ℕ → ModGL τ L,
      (List.range n).map g' = List.ofFn (fun i : Fin n => g' i.val) := by
    intro g'
    apply List.ext_getElem <;> simp
  have hv_eq : ((List.range n).map f).prod =
      (List.ofFn fun i : Fin n => pinnedX τ L (β i.val) (t i.val)).prod := by
    rw [hconv f]
    simp only [hf]
  have hv_ne : ((List.range n).map f).prod ≠ 1 := by
    intro hv1
    have hcard : (Finset.univ.filter fun i : Fin n => height (β i.val) < 0).card ≤ n :=
      le_trans (Finset.card_filter_le _ _) (by simp)
    have hinj : Function.Injective (fun i : Fin n => β i.val) := by
      intro i j hij
      by_contra hne
      exact (horth i.val j.val i.2 j.2 (fun h => hne (Fin.ext h))).2.1 hij
    have hne := prod_ne_one_aux n n (fun i : Fin n => β i.val) (fun i : Fin n => t i.val) ⟨0, hn⟩
      (fun i => hroot i.val) hinj
      (fun i k hik => (horth i.val k.val i.2 k.2 (fun h => hik (Fin.ext h))).1) hcard
      (show t 0 ≠ 0 by rw [ht0]; exact ht₀)
    have hP : (List.ofFn fun i : Fin n => pinnedX τ L (β i.val) (t i.val)).prod = 1 := by
      rw [← hv_eq]
      exact hv1
    exact hne hP
  have hvp : ((List.range n).map f).prod ^ r = 1 :=
    pow_prod_range_eq_one r f n hcomm (fun i _ => by rw [hf]; exact pinnedX_pow_char r _ _)
  refine ⟨((List.range n).map f).prod, hmem, ?_, hv_ne, hvp⟩
  rw [hGv, hP']

theorem exists_unip_centralizing_familyKernel (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) {l : ℕ} [Fact l.Prime]
    [CharP L l] {f : ℕ} (hqf : S.D.q = l ^ f) {ι : Type} (b : ι → Fin τ.rank → Lˣ)
    (hb : ∀ i, rootDiagUnit τ (b i) ∈ S.D.torus) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ familyKernel b) :
    ∃ u ∈ S.D.model, u ≠ 1 ∧ u ^ l = 1 ∧
      ∀ i, u * rootDiagUnit τ (b i) = rootDiagUnit τ (b i) * u := by
  classical
  have hK1 : ∀ δ ∈ familyKernel b, S.ρ δ ∈ familyKernel b := by
    intro δ hδ
    refine ⟨(S.frob.isRoot_iff δ).2 hδ.1, fun i => ?_⟩
    rw [S.frob.rootChar_eq (b i) (hb i) δ hδ.1, hδ.2 i, one_pow]
  have hK2 : ∀ δ ∈ familyKernel b, S.ρ⁻¹ δ ∈ familyKernel b := by
    intro δ hδ
    have hδ' : S.ρ (S.ρ⁻¹ δ) = δ := kc_perm_apply_inv S.ρ δ
    have hroot : IsRoot τ (S.ρ⁻¹ δ) := (S.frob.isRoot_iff _).1 (by rw [hδ']; exact hδ.1)
    refine ⟨hroot, fun i => ?_⟩
    have h := S.frob.rootChar_eq (b i) (hb i) _ hroot
    rw [hδ', hδ.2 i, hqf] at h
    exact units_eq_one_of_pow_char _ h.symm
  obtain ⟨x, hx, n, β, hn, hper, hβS, horth, hxβ⟩ :=
    kc_kill_cycle_periodic hτ b S.ρ hK1 hK2 S.frob.iform_eq hγ
  have hroot : ∀ k, IsRoot τ (β k) := fun k => (hβS k).1
  have hμex : ∀ δ : Fin τ.rank → ℤ, ∃ μ : L, IsRoot τ δ → μ ≠ 0 ∧
      ∀ c : L, S.D.step (pinnedX τ L δ c) = pinnedX τ L (S.ρ δ) (μ * c ^ S.D.q) := by
    intro δ
    by_cases hδ : IsRoot τ δ
    · obtain ⟨μ, hμ0, hμ⟩ := step_pinnedX S hδ
      exact ⟨μ, fun _ => ⟨hμ0, hμ⟩⟩
    · exact ⟨1, fun h => absurd h hδ⟩
  choose μ hμ using hμex
  obtain ⟨s, hs⟩ := exists_sign_family (L := L) (τ := τ) x
  obtain ⟨nx, hnx⟩ : ∃ nx : ModGL τ L, nx = canonicalRep (coxeterSystem τ) L x := ⟨_, rfl⟩
  obtain ⟨F', hF'⟩ : ∃ F' : ModGL τ L →* ModGL τ L, ∀ g, F' g = nx * S.D.step g * nx⁻¹ :=
    ⟨(MulAut.conj nx).toMonoidHom.comp S.D.step, fun g => rfl⟩
  have hρr : ∀ k, IsRoot τ (S.ρ (β k)) := fun k => (S.frob.isRoot_iff _).2 (hroot k)
  have hm : ∀ k (c : L), F' (pinnedX τ L (β k) c) =
      pinnedX τ L (β (k + 1)) ((s (S.ρ (β k)) * μ (β k)) * c ^ S.D.q) := by
    intro k c
    rw [hF', (hμ (β k) (hroot k)).2 c, hnx, (hs (S.ρ (β k)) (hρr k)).2, hxβ k, mul_assoc]
  have hm0 : ∀ k, s (S.ρ (β k)) * μ (β k) ≠ 0 := by
    intro k
    refine mul_ne_zero ?_ (hμ (β k) (hroot k)).1
    intro h0
    have h1 := (hs (S.ρ (β k)) (hρr k)).1
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  obtain ⟨v, hvR, hvF, hv1, hvl⟩ := kc_exists_cycle_element (L := L) l S.hqpow.1.two_le F' n hn
    β hper hroot horth (fun k => s (S.ρ (β k)) * μ (β k)) hm0 hm (familyKernel b) hβS
  have hkerb := kernelRoots_familyChar b
  have hnxM : nx ∈ familyGroup (K := L) b := by
    rw [hnx]
    exact canonicalRep_closure_mem_familyGroup b hx
  obtain ⟨z, hzZ, hz⟩ := exists_lang_torus_sup_kernelRoots S (χ := familyChar b) one_pos
    (fun δ hδ => by
      rw [Function.iterate_one]
      rw [hkerb] at hδ ⊢
      exact hK1 δ hδ)
    (y := nx) (by rw [hkerb]; exact hnxM)
  rw [hkerb] at hzZ
  rw [iterHom_eq_iterate, Function.iterate_one] at hz
  have hzM : z ∈ familyGroup (K := L) b := hzZ
  have hvM : v ∈ familyGroup (K := L) b := rootSpan_le_familyGroup b hvR
  have hstepv : S.D.step v = nx⁻¹ * v * nx := by
    have h := hvF
    rw [hF'] at h
    calc S.D.step v = nx⁻¹ * (nx * S.D.step v * nx⁻¹) * nx := by group
      _ = nx⁻¹ * v * nx := by rw [h]
  have hzA := familyGroup_le_adjoint b hzM
  have hvA := familyGroup_le_adjoint b hvM
  refine ⟨z * v * z⁻¹, ?_, ?_, ?_, fun i => ?_⟩
  · refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hzA hvA) (inv_mem hzA), ?_⟩
    change S.D.step (z * v * z⁻¹) = z * v * z⁻¹
    rw [map_mul, map_mul, map_inv, hz, hstepv]
    group
  · intro h
    apply hv1
    calc v = z⁻¹ * (z * v * z⁻¹) * z := by group
      _ = 1 := by rw [h]; group
  · rw [conj_pow, hvl]
    group
  · have hzd : Commute z (rootDiagUnit τ (b i)) := familyGroup_comm b i hzM
    have hvd : Commute v (rootDiagUnit τ (b i)) := familyGroup_comm b i hvM
    exact ((hzd.mul_left hvd).mul_left hzd.inv_left).eq

end Element

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
