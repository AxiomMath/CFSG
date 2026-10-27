module

public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix


theorem kr_symmetrizer {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (j : Fin τ.rank) :
    τ.symmetrizer j j = 1 := by
  rcases hτ with rfl | rfl | rfl | rfl <;> simp [Tag.symmetrizer]

theorem kr_iform_self {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : iform γ γ = 2 := by
  induction hγ with
  | basis j => rw [iform_single_single, kr_symmetrizer hτ j, mul_one]
  | reflect i _ ih => rw [iform_reflect, ih]

theorem kr_corootPair {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (v : Fin τ.rank → ℤ) :
    corootPair δ v = iform δ v := by
  unfold corootPair
  rw [kr_iform_self hτ hδ]
  omega

theorem kr_rootReflection_smul {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (v : Fin τ.rank → ℤ) :
    rootReflection δ • v = v - iform δ v • δ := by
  rw [rootReflection_smul hδ, kr_corootPair hτ hδ]

theorem kr_iform_add_add {τ : Tag} (δ ε : Fin τ.rank → ℤ) :
    iform (δ + ε) (δ + ε) = iform δ δ + 2 * iform δ ε + iform ε ε := by
  simp only [iform_add_left, iform_add_right, iform_comm ε δ]
  ring

theorem kr_smul_of_simpleAdj {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) {δ ε : Fin τ.rank → ℤ}
    (hδ : δ ∈ simpleRoots Ψ) (hε : ε ∈ simpleRoots Ψ) (hne : iform δ ε ≠ 0) :
    ∃ x ∈ componentWeylGroup Ψ, x • δ = ε := by
  by_cases he : δ = ε
  · exact ⟨1, one_mem _, by rw [he, one_smul]⟩
  have hδr := simpleRoots_isRoot hδ
  have hεr := simpleRoots_isRoot hε
  have hle : iform δ ε ≤ 0 := iform_simpleRoots_nonpos hΨ hδ hε he
  have hδδ := kr_iform_self hτ hδr
  have hεε := kr_iform_self hτ hεr
  have hge : -1 ≤ iform δ ε := by
    by_contra! hlt
    have hv : δ + ε ≠ 0 := by
      intro h0
      have hδ' : δ = -ε := add_eq_zero_iff_eq_neg.1 h0
      have h1 := simpleRoots_height_pos hδ
      have h2 := simpleRoots_height_pos hε
      rw [hδ', height_neg] at h1
      omega
    have hpos := iform_self_pos hv
    rw [kr_iform_add_add, hδδ, hεε] at hpos
    omega
  have h1 : iform δ ε = -1 := by omega
  have hrε : rootReflection ε • δ = δ + ε := by
    rw [kr_rootReflection_smul hτ hεr, iform_comm, h1, neg_one_smul, sub_neg_eq_add]
  have hrδ : rootReflection δ • (δ + ε) = ε := by
    rw [kr_rootReflection_smul hτ hδr, iform_add_right, hδδ, h1]
    norm_num
  exact ⟨rootReflection δ * rootReflection ε,
    mul_mem (rootReflection_mem_componentWeylGroup hδ) (rootReflection_mem_componentWeylGroup hε),
    by rw [mul_smul, hrε, hrδ]⟩

theorem kr_smul_of_reflTransGen {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) {β c : Fin τ.rank → ℤ}
    (h : Relation.ReflTransGen (SimpleAdj Ψ) β c) : ∃ x ∈ componentWeylGroup Ψ, x • β = c := by
  induction h with
  | refl => exact ⟨1, one_mem _, one_smul _ _⟩
  | tail _ hbc ih =>
    obtain ⟨x, hx, hxβ⟩ := ih
    obtain ⟨hb, hc, hne⟩ := hbc
    obtain ⟨y, hy, hyb⟩ := kr_smul_of_simpleAdj hτ hΨ hb hc hne
    exact ⟨y * x, mul_mem hy hx, by rw [mul_smul, hxβ, hyb]⟩

theorem kr_smul_of_mem_component {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) {α β : Fin τ.rank → ℤ}
    (hα : α ∈ Ψ) (hβ : β ∈ Ψ) : ∃ x ∈ componentWeylGroup Ψ, x • α = β := by
  obtain ⟨u, hu, δ, hδ, rfl⟩ := exists_smul_simpleRoot hΨ hα
  obtain ⟨v, hv, ε, hε, rfl⟩ := exists_smul_simpleRoot hΨ hβ
  obtain ⟨y, hy, hyδ⟩ := kr_smul_of_reflTransGen hτ hΨ (simpleRoots_connected hΨ hδ hε)
  exact ⟨v * y * u⁻¹, mul_mem (mul_mem hv hy) (inv_mem hu),
    by rw [mul_smul, mul_smul, inv_smul_smul, hyδ]⟩

theorem kr_fix_of_orth {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} {w : WeylGroup τ}
    (hw : w ∈ componentWeylGroup Ψ) {v : Fin τ.rank → ℤ} (hv : ∀ γ ∈ Ψ, iform γ v = 0) :
    w • v = v := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨δ, hδ, rfl⟩ := hx
    exact rootReflection_smul_of_iform_eq_zero (simpleRoots_isRoot hδ)
      (hv δ (simpleRoots_subset hδ))
  | one => rw [one_smul]
  | mul x y _ _ hx hy => rw [mul_smul, hy, hx]
  | inv x _ hx =>
    calc x⁻¹ • v = x⁻¹ • x • v := by rw [hx]
      _ = v := inv_smul_smul x v

theorem kr_eqvGen_map {α : Type*} {r : α → α → Prop} {g : α → α}
    (hg : ∀ a b, r a b → r (g a) (g b)) {a b : α} (h : Relation.EqvGen r a b) :
    Relation.EqvGen r (g a) (g b) := by
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (hg x y hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem kr_mk_of_eq {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {a b : Fin τ.rank → ℤ} (ha : a ∈ kernelRoots χ) (hb : b ∈ kernelRoots χ) (h : a = b) :
    (⟦⟨a, ha⟩⟧ : KernelComponent χ) = ⟦⟨b, hb⟩⟧ := by
  subst h
  rfl

theorem kr_mk_map {τ : Tag} {M : Type*} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (x : WeylGroup τ) (hx : ∀ a ∈ kernelRoots χ, x • a ∈ kernelRoots χ)
    {a b : Fin τ.rank → ℤ} (ha : a ∈ kernelRoots χ) (hb : b ∈ kernelRoots χ)
    (h : (⟦⟨a, ha⟩⟧ : KernelComponent χ) = ⟦⟨b, hb⟩⟧) :
    (⟦⟨x • a, hx a ha⟩⟧ : KernelComponent χ) = ⟦⟨x • b, hx b hb⟩⟧ := by
  let g : kernelRoots χ → kernelRoots χ := fun c => ⟨x • (c : Fin τ.rank → ℤ), hx c c.2⟩
  have hrel : ∀ c d : kernelRoots χ,
      (c : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (d : Fin τ.rank → ℤ)) ≠ 0 →
        (g c : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (g d : Fin τ.rank → ℤ)) ≠ 0 := by
    intro c d hcd
    rw [dotProduct_mulVec_eq_iform] at hcd ⊢
    show iform (x • (c : Fin τ.rank → ℤ)) (x • (d : Fin τ.rank → ℤ)) ≠ 0
    rwa [iform_smul]
  have key : Relation.EqvGen (fun c d : kernelRoots χ =>
      (c : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (d : Fin τ.rank → ℤ)) ≠ 0)
      ⟨a, ha⟩ ⟨b, hb⟩ :=
    Quotient.exact h
  exact Quotient.sound (kr_eqvGen_map hrel key)

theorem kr_componentRoots_subset {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ) :
    componentRoots χ i ⊆ kernelRoots χ :=
  fun _ ⟨h, _⟩ => h

theorem kr_componentWeylGroup_le {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ) :
    componentWeylGroup (componentRoots χ i) ≤
      Subgroup.closure (rootReflection '' kernelRoots χ) := by
  unfold componentWeylGroup
  exact Subgroup.closure_mono
    (Set.image_mono fun δ hδ => kr_componentRoots_subset i (simpleRoots_subset hδ))

theorem kr_stab_pow {τ : Tag} {S : Set (Fin τ.rank → ℤ)} {w : WeylGroup τ}
    (h1 : ∀ a ∈ S, w • a ∈ S) (h2 : ∀ a ∈ S, w⁻¹ • a ∈ S) (i : ℕ) :
    (∀ a ∈ S, (w ^ i) • a ∈ S) ∧ (∀ a ∈ S, (w ^ i)⁻¹ • a ∈ S) := by
  induction i with
  | zero =>
    exact ⟨fun a ha => by rwa [pow_zero, one_smul],
      fun a ha => by rwa [pow_zero, inv_one, one_smul]⟩
  | succ i ih =>
    obtain ⟨hi1, hi2⟩ := ih
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · rw [pow_succ, mul_smul]
      exact hi1 _ (h1 a ha)
    · rw [pow_succ, _root_.mul_inv_rev, mul_smul]
      exact h2 _ (hi2 a ha)

theorem exists_kill_root_cycle {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {M : Type*} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (w : WeylGroup τ)
    (hw : (fun α => w • α) '' kernelRoots χ = kernelRoots χ)
    {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots χ) :
    ∃ x ∈ Subgroup.closure (rootReflection '' kernelRoots χ), ∃ (n : ℕ) (hn : 0 < n),
      ∃ β : Fin n → Fin τ.rank → ℤ, β ⟨0, hn⟩ = α ∧ (∀ k, β k ∈ kernelRoots χ) ∧
        (∀ i j, i ≠ j → iform (β i) (β j) = 0 ∧ β i ≠ β j ∧ β i ≠ -β j ∧
          ∀ a b : ℕ, 0 < a → 0 < b → ¬ IsRoot τ (a • β i + b • β j)) ∧
        ∀ k : Fin n, (x * w) • β k = β ⟨((k : ℕ) + 1) % n, Nat.mod_lt _ hn⟩ := by
  classical
  have hw1 : ∀ a ∈ kernelRoots χ, w • a ∈ kernelRoots χ := by
    intro a ha
    have h : w • a ∈ (fun γ => w • γ) '' kernelRoots χ := ⟨a, ha, rfl⟩
    rwa [hw] at h
  have hw2 : ∀ a ∈ kernelRoots χ, w⁻¹ • a ∈ kernelRoots χ := by
    intro a ha
    have h : a ∈ (fun γ => w • γ) '' kernelRoots χ := by rwa [hw]
    obtain ⟨b, hb, hba⟩ := h
    dsimp only at hba
    rw [← hba, inv_smul_smul]
    exact hb
  have hP := kr_stab_pow hw1 hw2
  have hr : ∀ m : ℕ, (w ^ m) • α ∈ kernelRoots χ := fun m => (hP m).1 α hα
  obtain ⟨cl, hcl⟩ : ∃ cl : ℕ → KernelComponent χ,
      ∀ m, cl m = ⟦⟨(w ^ m) • α, hr m⟩⟧ := ⟨_, fun m => rfl⟩
  obtain ⟨N, hNpos, hNeq⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite w)
  have hex : ∃ m, 0 < m ∧ cl m = ⟦⟨α, hα⟩⟧ :=
    ⟨N, hNpos, (hcl N).trans (kr_mk_of_eq (hr N) hα (by rw [hNeq, one_smul]))⟩
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
        ⟦⟨(w ^ i)⁻¹ • ((w ^ i) • α), (hP i).2 _ (hr i)⟩⟧ :=
      kr_mk_of_eq hα ((hP i).2 _ (hr i)) (inv_smul_smul (w ^ i) α).symm
    have c2 : (⟦⟨(w ^ i)⁻¹ • ((w ^ i) • α), (hP i).2 _ (hr i)⟩⟧ : KernelComponent χ) =
        ⟦⟨(w ^ i)⁻¹ • ((w ^ (i + d)) • α), (hP i).2 _ (hr (i + d))⟩⟧ :=
      kr_mk_map χ ((w ^ i)⁻¹) (hP i).2 (hr i) (hr (i + d))
        ((hcl i).symm.trans (heq.trans (hcl (i + d))))
    have c3 : (⟦⟨(w ^ i)⁻¹ • ((w ^ (i + d)) • α), (hP i).2 _ (hr (i + d))⟩⟧ :
        KernelComponent χ) = ⟦⟨(w ^ d) • α, hr d⟩⟧ :=
      kr_mk_of_eq ((hP i).2 _ (hr (i + d))) (hr d)
        (by rw [pow_add, mul_smul, inv_smul_smul])
    exact hmin d hd hdn ((hcl d).trans (c1.trans (c2.trans c3)).symm)
  have hdistc : ∀ i j : ℕ, i < n → j < n → i ≠ j →
      (⟦⟨(w ^ i) • α, hr i⟩⟧ : KernelComponent χ) ≠ ⟦⟨(w ^ j) • α, hr j⟩⟧ := by
    intro i j hi hj hij heq
    have hcl_eq : cl i = cl j := (hcl i).trans (heq.trans (hcl j).symm)
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact hdist i j h hj hcl_eq
    · exact hdist j i h hi hcl_eq.symm
  have hαΨ : α ∈ componentRoots χ ⟦⟨α, hα⟩⟧ := ⟨hα, rfl⟩
  have hwnΨ : (w ^ n) • α ∈ componentRoots χ ⟦⟨α, hα⟩⟧ :=
    ⟨hr n, (hcl n).symm.trans hncl⟩
  obtain ⟨x0, hx0, hx0α⟩ :=
    kr_smul_of_mem_component hτ (isRootComponent_componentRoots (χ := χ) ⟦⟨α, hα⟩⟧) hwnΨ hαΨ
  have hfix : ∀ m : ℕ, 0 < m → m < n → x0 • ((w ^ m) • α) = (w ^ m) • α := by
    intro m hm0 hmn
    refine kr_fix_of_orth hx0 (fun γ hγ => ?_)
    obtain ⟨hγk, hγc⟩ := hγ
    refine iform_eq_zero_of_mk_ne (α := ⟨γ, hγk⟩) (β := ⟨(w ^ m) • α, hr m⟩) ?_
    intro hne
    exact hmin m hm0 hmn ((hcl m).trans (hne.symm.trans hγc))
  refine ⟨x0, kr_componentWeylGroup_le _ hx0, n, hn0, fun k => (w ^ (k : ℕ)) • α, ?_,
    fun k => hr k, ?_, ?_⟩
  · simp
  · intro i j hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun e => hij (Fin.ext e)
    have hc := hdistc (i : ℕ) (j : ℕ) i.2 j.2 hne
    have h0 : iform ((w ^ (i : ℕ)) • α) ((w ^ (j : ℕ)) • α) = 0 :=
      iform_eq_zero_of_mk_ne (α := ⟨(w ^ (i : ℕ)) • α, hr i⟩) (β := ⟨(w ^ (j : ℕ)) • α, hr j⟩) hc
    refine ⟨h0, fun h => hc (kr_mk_of_eq (hr i) (hr j) h), ?_,
      fun a b ha hb => not_isRoot_of_mk_ne hc ha hb⟩
    intro h
    have h' : (w ^ (i : ℕ)) • α = -((w ^ (j : ℕ)) • α) := h
    have hv := kr_iform_self hτ (IsRoot.smul hα.1 (w ^ (j : ℕ)))
    have hneg := iform_smul_left (-1 : ℤ) ((w ^ (j : ℕ)) • α) ((w ^ (j : ℕ)) • α)
    rw [neg_one_smul, hv] at hneg
    rw [h'] at h0
    linarith
  · intro k
    show (x0 * w) • ((w ^ (k : ℕ)) • α) = (w ^ (((k : ℕ) + 1) % n)) • α
    rw [mul_smul, ← mul_smul w, ← pow_succ']
    by_cases hkn : (k : ℕ) + 1 < n
    · rw [Nat.mod_eq_of_lt hkn]
      exact hfix _ (by omega) hkn
    · have hk : (k : ℕ) + 1 = n := by omega
      rw [hk, Nat.mod_self, pow_zero, one_smul]
      exact hx0α

end CFSG.LieType.SeitzGeneration.ExcHighThree
