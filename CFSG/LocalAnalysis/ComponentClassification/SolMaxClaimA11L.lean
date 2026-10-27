module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA11S

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem permCongr_apply_eq_of_ofSubtype {α β : Type*} {p : α → Prop} [DecidablePred p]
    (π : Subtype p ≃ β) (u : Perm (Subtype p)) {q : Perm α} (hu : Perm.ofSubtype u = q)
    {b : β} (hb : q (π.symm b) = π.symm b) : π.permCongr u b = b := by
  have h1 : u (π.symm b) = π.symm b := by
    apply Subtype.ext
    rw [← Perm.ofSubtype_apply_coe, hu]
    exact hb
  rw [Equiv.permCongr_apply, h1, Equiv.apply_symm_apply]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem exists_fixed_layer_pair' {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M) {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin (n + 2))}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin (n + 2))} (hρ : IsPermAction θ ρ)
    (htM : t ∈ normalizer (M : Set X)) {e₀ e₁ : X} (he₀E : e₀ ∈ E) (he₁E : e₁ ∈ E)
    (he₀1 : e₀ ≠ 1) (he₁1 : e₁ ≠ 1) (h01 : e₀ ≠ e₁) :
    ∃ (L₀ F : Subgroup X) (χ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* alternatingGroup (Fin (n - 2)))
      (DY : Finset (Fin (n - 2))), L₀ ≤ M ∧
      L₀ ≤ centralizer ({e₁} : Set X) ⊓ centralizer ({e₀} : Set X) ∧
      IsPComponent 2 (L₀.subgroupOf (centralizer ({e₁} : Set X) ⊓ centralizer ({e₀} : Set X))) ∧
      F ≤ L₀ ∧ F ≤ J ∧ Nat.card F = 4 ∧ (∀ x ∈ F, x * x = 1) ∧
      (∃ DF : Finset (Fin n), DF.card = 4 ∧ ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
        ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω) ∧
      DY.card = 4 ∧
      ∀ x : ↥L₀, (x : X) ∈ F → ∀ y ∉ DY,
        ((χ (x : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) : alternatingGroup (Fin (n - 2))) :
          Perm (Fin (n - 2))) y = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := S.nine_le
  have he₀J : e₀ ∈ J := S.le he₀E
  have he₁J : e₁ ∈ J := S.le he₁E
  have he₀M : e₀ ∈ M := hJM he₀J
  have he₁M : e₁ ∈ M := hJM he₁J
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have he₁2 : e₁ * e₁ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₁ he₁E
  have h10 : e₁ * e₀ = e₀ * e₁ := congrArg Subtype.val
    ((isElementaryAbelian_of_klein S.klein).toIsMulCommutative.is_comm.comm ⟨e₁, he₁E⟩
      ⟨e₀, he₀E⟩)
  obtain ⟨ι, hι⟩ := S.exists_embedding_of_le htM hJM (by omega) (by omega) hρ
  have hρM : ∀ (x : X) (hx : x ∈ M), ρ ⟨x, le_normalizer hx⟩ = coreImage θ hx :=
    fun x hx => hρ.apply_of_mem (by omega) ⟨x, hx⟩
  have hsuppJ : ∀ (x : X) (hxJ : x ∈ J) (hxM : x ∈ M),
      (coreImage θ hxM).support = (coreImage e hxJ).support.map ι := fun x hxJ hxM => by
    rw [← hρM x hxM]
    exact hι x hxJ
  have hτ₀s : (coreImage θ he₀M).support = D.map ι := by
    rw [hsuppJ e₀ he₀J he₀M, S.support_coreImage_E he₀E he₀1]
  have hc₁s : (coreImage θ he₁M).support = D.map ι := by
    rw [hsuppJ e₁ he₁J he₁M, S.support_coreImage_E he₁E he₁1]
  have hτ₀4 : (coreImage θ he₀M).support.card = 4 := by rw [hτ₀s, Finset.card_map, S.card]
  have hcomm₁ : ∀ p : Perm (Fin (n + 2)), p.support ⊆ (coreImage θ he₀M).supportᶜ →
      coreImage θ he₁M * p = p * coreImage θ he₁M := by
    intro p hp
    have hd : (coreImage θ he₁M).Disjoint p := by
      rw [Perm.disjoint_iff_disjoint_support, hc₁s, ← hτ₀s]
      exact Finset.disjoint_of_subset_right hp disjoint_compl_right
    exact hd.commute.eq
  have h5 : 5 ≤ (n + 2) - (coreImage θ he₀M).support.card := by rw [hτ₀4]; omega
  obtain ⟨L₁, hL₁, hL₁pc, hinv₁, hsub₁, χ₁, hχ₁⟩ :=
    exists_fixed_component_of_acts hMH hMpc θ (le_normalizer he₀M) he₀2 he₀M
      (by rw [mul_inv_cancel]; exact one_mem _) h5
  have hL₁M : L₁ ≤ M := hL₁.trans inf_le_left
  have hL₁C₀ : L₁ ≤ centralizer ({e₀} : Set X) := hL₁.trans inf_le_right
  have hL₁HC : L₁ ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      centralizer ({e₀} : Set X) := le_inf (hL₁M.trans hMH) hL₁C₀
  have he₁L₁ : e₁ ∈ normalizer (L₁ : Set X) := by
    refine mem_normalizer_of_fixed_component θ hL₁C₀
      (primeResidual_eq_top_of_isPComponent hL₁HC hL₁pc) hinv₁ hsub₁ (le_normalizer he₁M) h10
      fun x hx hxs => ?_
    rw [coreImage_conj_of_mem θ he₁M hx, hcomm₁ _ hxs, mul_inv_cancel_right]
    exact hxs
  have he₁K : e₁ ∈ UnbalancedLayer.coreActionKernel L₁ := by
    refine UnbalancedLayer.mem_coreActionKernel.mpr ⟨he₁L₁, fun x hx => ?_⟩
    have he₁inv : e₁⁻¹ = e₁ := inv_eq_of_mul_eq_one_right he₁2
    have hy : e₁ * x * e₁⁻¹ ∈ L₁ := (mem_normalizer_iff.mp he₁L₁ x).mp hx
    obtain ⟨hxM, hxs⟩ := hsub₁ x hx
    have himg : coreImage θ (hL₁M hy) = coreImage θ hxM := by
      rw [coreImage_conj_of_mem θ he₁M hxM, hcomm₁ _ hxs, mul_inv_cancel_right]
    have hq : ((⟨e₁ * x * e₁⁻¹, hy⟩ : ↥L₁) : ↥L₁ ⧸ pPrimeCore 2 ↥L₁) =
        ((⟨x, hx⟩ : ↥L₁) : ↥L₁ ⧸ pPrimeCore 2 ↥L₁) := by
      apply χ₁.injective
      apply Subtype.ext
      apply Perm.ofSubtype_injective
      rw [hχ₁ ⟨_, hy⟩ (hL₁M hy), hχ₁ ⟨x, hx⟩ hxM]
      exact himg
    refine ⟨_, QuotientGroup.eq.mp hq.symm, ?_⟩
    change x⁻¹ * (e₁ * x * e₁⁻¹) = x⁻¹ * e₁⁻¹ * x * e₁
    rw [he₁inv]
    group
  have hβ₁ : Fintype.card ↥((coreImage θ he₀M).supportᶜ : Finset (Fin (n + 2))) = n - 2 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hτ₀4]
    omega
  set π₁ := Fintype.equivFinOfCardEq hβ₁ with hπ₁def
  set eL₁ : ↥L₁ ⧸ pPrimeCore 2 ↥L₁ ≃* alternatingGroup (Fin (n - 2)) :=
    χ₁.trans π₁.altCongrHom with heL₁def
  have h1L₁ : (1 : X) ∈ L₁ := one_mem _
  have h5' : 5 ≤ (n - 2) - (coreImage eL₁ h1L₁).support.card := by
    rw [coreImage_one, Perm.support_one, Finset.card_empty]
    omega
  obtain ⟨L₀, hL₀, hL₀pc, hinv₂, -, χ₂, hχ₂⟩ :=
    exists_fixed_component_of_acts hL₁HC hL₁pc eL₁ he₁L₁ he₁2 h1L₁
      (by rw [inv_one, mul_one]; exact he₁K) h5'
  have hL₀L₁ : L₀ ≤ L₁ := hL₀.trans inf_le_left
  have hCC : (normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      centralizer ({e₀} : Set X)) ⊓ centralizer ({e₁} : Set X) =
      centralizer ({e₁} : Set X) ⊓ centralizer ({e₀} : Set X) := by
    rw [inf_assoc, inf_of_le_right (S.inf_centralizer_le he₀E he₁E he₀1 he₁1 h01), inf_comm]
  rw [hCC] at hL₀pc
  have hL₀C : L₀ ≤ centralizer ({e₁} : Set X) ⊓ centralizer ({e₀} : Set X) :=
    le_inf (hL₀.trans inf_le_right) (hL₀L₁.trans hL₁C₀)
  obtain ⟨F, DF, hFJ, hF4, hFsq, hDF, hdisj, hFs, hFE⟩ :=
    exists_commuting_four_subgroup S.nine_le e S.le S.isPGroup S.card S.supp
  have hFsupp : ∀ (x : X) (hxF : x ∈ F) (hxM : x ∈ M), ∀ ω ∉ DF.map ι,
      coreImage θ hxM ω = ω := by
    intro x hxF hxM ω hω
    rw [← Perm.notMem_support, hsuppJ x (hFJ hxF) hxM]
    intro hω'
    apply hω
    refine Finset.map_subset_map.mpr (fun z hz => ?_) hω'
    by_contra hzF
    exact (Perm.mem_support.mp hz) (hFs ⟨x, hFJ hxF⟩ hxF z hzF)
  have hDMτ : ∀ (x : X) (hxF : x ∈ F) (hxM : x ∈ M),
      (coreImage θ hxM).support ⊆ (coreImage θ he₀M).supportᶜ := by
    intro x hxF hxM ω hω
    rw [Finset.mem_compl, hτ₀s]
    intro hωD
    have hωF : ω ∈ DF.map ι := by
      by_contra h
      exact (Perm.mem_support.mp hω) (hFsupp x hxF hxM ω h)
    exact Finset.disjoint_left.mp ((Finset.disjoint_map ι).mpr hdisj) hωD hωF
  have hF2k : ∀ x ∈ F, ∃ k : ℕ, x ^ 2 ^ k = 1 := fun x hx =>
    ⟨1, by rw [pow_one, sq]; exact hFsq x hx⟩
  have hFe : ∀ x ∈ F, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    (mem_centralizer_iff.mp (hFE hx) y hy).symm
  have hFL₁ : F ≤ L₁ := fun x hx =>
    hinv₁ x (hJM (hFJ hx)) (hFe x hx e₀ he₀E) (hF2k x hx) (hDMτ x hx _)
  have hFL₀ : F ≤ L₀ := fun x hx => hinv₂ x (hFL₁ hx) (hFe x hx e₁ he₁E) (hF2k x hx) (by
    rw [coreImage_one, Perm.support_one, Finset.compl_empty]
    exact Finset.subset_univ _)
  have hβ₂ : Fintype.card ↥((coreImage eL₁ h1L₁).supportᶜ : Finset (Fin (n - 2))) = n - 2 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, coreImage_one, Perm.support_one,
      Finset.card_empty, Nat.sub_zero]
  set π₂ := Fintype.equivFinOfCardEq hβ₂ with hπ₂def
  set χ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* alternatingGroup (Fin (n - 2)) :=
    χ₂.trans π₂.altCongrHom with hχdef
  obtain ⟨κ, hκdef⟩ : ∃ κ : Fin (n - 2) → Fin (n + 2), ∀ i, κ i =
      ((π₁.symm (π₂.symm i : Fin (n - 2)) : ↥((coreImage θ he₀M).supportᶜ :
        Finset (Fin (n + 2)))) : Fin (n + 2)) := ⟨_, fun _ => rfl⟩
  have hκ : Function.Injective κ := by
    intro i j hij
    rw [hκdef, hκdef] at hij
    exact π₂.symm.injective (Subtype.ext (π₁.symm.injective (Subtype.ext hij)))
  set DY₀ := Finset.univ.filter (fun i : Fin (n - 2) => κ i ∈ DF.map ι) with hDY₀def
  have hDY₀ : DY₀.card ≤ 4 := by
    have h1 : DY₀.card ≤ (DF.map ι).card := Finset.card_le_card_of_injOn κ
      (fun i hi => (Finset.mem_filter.mp hi).2) (hκ.injOn)
    rwa [Finset.card_map, hDF] at h1
  obtain ⟨DY, hDY₀Y, -, hDY4⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ DY₀) hDY₀
    (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  have hB : ∀ (x : X) (hxL₁ : x ∈ L₁), (∀ ω ∉ DF.map ι, coreImage θ (hL₁M hxL₁) ω = ω) →
      ∀ i : Fin (n - 2), ((π₁.symm i : ↥((coreImage θ he₀M).supportᶜ :
        Finset (Fin (n + 2)))) : Fin (n + 2)) ∉ DF.map ι → coreImage eL₁ hxL₁ i = i := by
    intro x hxL₁ hA i hi
    have h1 : coreImage eL₁ hxL₁ = π₁.permCongr ((χ₁ ((⟨x, hxL₁⟩ : ↥L₁) :
        ↥L₁ ⧸ pPrimeCore 2 ↥L₁) : alternatingGroup _) : Perm _) := rfl
    rw [h1]
    exact permCongr_apply_eq_of_ofSubtype π₁ _ (hχ₁ ⟨x, hxL₁⟩ (hL₁M hxL₁)) (hA _ hi)
  refine ⟨L₀, F, χ, DY, hL₀L₁.trans hL₁M, hL₀C, hL₀pc, hFL₀, hFJ, hF4, hFsq, ⟨DF, hDF, hFs⟩,
    hDY4, ?_⟩
  intro x hxF y hy
  have hxL₁ : (x : X) ∈ L₁ := hL₀L₁ x.2
  have h1 : ((χ (x : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) : alternatingGroup (Fin (n - 2))) :
      Perm (Fin (n - 2))) = π₂.permCongr ((χ₂ (x : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) :
        alternatingGroup _) : Perm _) := rfl
  rw [h1]
  refine permCongr_apply_eq_of_ofSubtype π₂ _ (hχ₂ x hxL₁) ?_
  refine hB x hxL₁ (hFsupp x hxF _) _ fun hκy => hy (hDY₀Y ?_)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hκdef]; exact hκy⟩

theorem exists_fixed_layer_pair (_hn : 11 ≤ n) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M) {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin (n + 2))}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin (n + 2))} (hρ : IsPermAction θ ρ)
    (htM : t ∈ normalizer (M : Set X)) {e₀ e₁ : X} (he₀E : e₀ ∈ E) (he₁E : e₁ ∈ E)
    (he₀1 : e₀ ≠ 1) (he₁1 : e₁ ≠ 1) (h01 : e₀ ≠ e₁) :
    ∃ (L₀ F : Subgroup X) (χ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* alternatingGroup (Fin (n - 2)))
      (DY : Finset (Fin (n - 2))),
      L₀ ≤ centralizer ({e₁} : Set X) ⊓ centralizer ({e₀} : Set X) ∧
      IsPComponent 2 (L₀.subgroupOf (centralizer ({e₁} : Set X) ⊓ centralizer ({e₀} : Set X))) ∧
      F ≤ L₀ ∧ F ≤ J ∧ Nat.card F = 4 ∧ (∀ x ∈ F, x * x = 1) ∧
      (∃ DF : Finset (Fin n), DF.card = 4 ∧ ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
        ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω) ∧
      DY.card = 4 ∧
      ∀ x : ↥L₀, (x : X) ∈ F → ∀ y ∉ DY,
        ((χ (x : ↥L₀ ⧸ pPrimeCore 2 ↥L₀) : alternatingGroup (Fin (n - 2))) :
          Perm (Fin (n - 2))) y = y :=
  let ⟨L₀, F, χ, DY, _, h⟩ := S.exists_fixed_layer_pair' hMH hMpc hJM hρ htM he₀E he₁E he₀1 he₁1 h01
  ⟨L₀, F, χ, DY, h⟩

end Sig36

end CFSG.ComponentClassification.SolMax
