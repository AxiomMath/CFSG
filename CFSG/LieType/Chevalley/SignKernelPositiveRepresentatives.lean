module

public import CFSG.LieType.Chevalley.SignStabilizerQuotients
import CFSG.GroupTheory.ElementaryAbelianTransport

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem kernelWeylGroup_eq_closure :
    kernelWeylGroup χ = Subgroup.closure (rootReflection '' kernelRoots χ) := by
  rw [kernelWeylGroup]
  congr 1
  ext r
  constructor
  · rintro ⟨w, i, hα, rfl⟩
    exact ⟨_, hα, (conj_simple_eq_rootReflection w i).symm⟩
  · rintro ⟨α, hα, rfl⟩
    obtain ⟨w, i, rfl⟩ := isRoot_iff_exists_smul_single.1 hα.1
    exact ⟨w, i, hα, (conj_simple_eq_rootReflection w i).symm⟩

theorem componentWeylGroup_le_kernelWeylGroup
    (i : KernelComponent χ) :
    componentWeylGroup (componentRoots χ i) ≤ kernelWeylGroup χ := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨β, hβ, rfl⟩
  obtain ⟨hβk, -⟩ := simpleRoots_subset hβ
  exact rootReflection_mem_kernelWeylGroup hβk

theorem kernelWeylGroup_le_iSup :
    kernelWeylGroup χ ≤ ⨆ i : KernelComponent χ, componentWeylGroup (componentRoots χ i) := by
  rw [kernelWeylGroup_eq_closure, Subgroup.closure_le]
  rintro _ ⟨α, hα, rfl⟩
  have hΨ := isRootComponent_componentRoots (χ := χ) ⟦⟨α, hα⟩⟧
  obtain ⟨w, hw, β, hβ, e⟩ := exists_smul_simpleRoot hΨ (α := α) ⟨hα, rfl⟩
  rw [SetLike.mem_coe, e, rootReflection_smul_root _ (simpleRoots_isRoot hβ)]
  exact Subgroup.mem_iSup_of_mem _ (mul_mem (mul_mem hw
    (rootReflection_mem_componentWeylGroup hβ)) (inv_mem hw))

theorem rootReflection_commute
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (h : iform β γ = 0) : Commute (rootReflection β) (rootReflection γ) := by
  have e := rootReflection_smul_root (rootReflection β) hγ
  rw [rootReflection_smul_of_iform_eq_zero hβ h, rootReflection_inv hβ] at e
  calc rootReflection β * rootReflection γ =
      rootReflection β * rootReflection γ * rootReflection β * rootReflection β := by
        rw [mul_assoc _ (rootReflection β), rootReflection_mul_self hβ, mul_one]
    _ = rootReflection γ * rootReflection β := by rw [← e]

theorem iform_eq_zero_of_ne_class {i j : KernelComponent χ} (hij : i ≠ j) {β γ : Fin τ.rank → ℤ}
    (hβ : β ∈ componentRoots χ i) (hγ : γ ∈ componentRoots χ j) : iform β γ = 0 := by
  obtain ⟨hβk, hβi⟩ := hβ
  obtain ⟨hγk, hγj⟩ := hγ
  exact iform_eq_zero_of_mk_ne (α := ⟨β, hβk⟩) (β := ⟨γ, hγk⟩) (by rw [hβi, hγj]; exact hij)

theorem commute_of_mem_componentWeylGroup
    {i j : KernelComponent χ} (hij : i ≠ j)
    {x y : WeylGroup τ} (hx : x ∈ componentWeylGroup (componentRoots χ i))
    (hy : y ∈ componentWeylGroup (componentRoots χ j)) : Commute x y := by
  have hle : componentWeylGroup (componentRoots χ i) ≤
      Subgroup.centralizer (rootReflection '' (simpleRoots (componentRoots χ j) :
        Set (Fin τ.rank → ℤ))) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβ, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ ⟨γ, hγ, rfl⟩
    exact (rootReflection_commute (simpleRoots_isRoot hβ) (simpleRoots_isRoot hγ)
      (iform_eq_zero_of_ne_class hij (simpleRoots_subset hβ) (simpleRoots_subset hγ))).eq.symm
  have hx' := hle hx
  rw [← Subgroup.centralizer_closure] at hx'
  exact ((Subgroup.mem_centralizer_iff.1 hx') y hy).symm

theorem smul_eq_of_mem_componentWeylGroup
    {i j : KernelComponent χ} (hij : i ≠ j)
    {x : WeylGroup τ} (hx : x ∈ componentWeylGroup (componentRoots χ j)) {α : Fin τ.rank → ℤ}
    (hα : α ∈ componentRoots χ i) : x • α = α := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, rfl⟩ := hx
    refine rootReflection_smul_of_iform_eq_zero (simpleRoots_isRoot hγ) ?_
    rw [iform_comm]
    exact iform_eq_zero_of_ne_class hij hα (simpleRoots_subset hγ)
  | one => exact one_smul _ _
  | mul x y _ _ hx hy => rw [mul_smul, hy, hx]
  | inv x _ hx => rw [inv_smul_eq_iff, hx]

theorem smul_eq_of_mem_iSup_ne
    {i : KernelComponent χ} {x : WeylGroup τ}
    (hx : x ∈ ⨆ j : {j : KernelComponent χ // j ≠ i},
      componentWeylGroup (componentRoots χ (j : KernelComponent χ)))
    {α : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i) : x • α = α :=
  Subgroup.iSup_induction (C := fun x => x • α = α) _ hx
    (fun j _ hy => smul_eq_of_mem_componentWeylGroup j.2.symm hy hα) (one_smul _ _)
    (fun x y hx hy => by rw [mul_smul, hy, hx])

theorem eq_one_of_mem_kernelWeylGroup
    {u : WeylGroup τ} (hu : u ∈ kernelWeylGroup χ)
    (hpos : ∀ α ∈ posRoots (kernelRoots χ), u • α ∈ posRoots (kernelRoots χ)) : u = 1 := by
  classical
  have : Finite (kernelRoots χ) := ((finite_setOf_isRoot τ).subset fun α h => h.1).to_subtype
  have : Fintype (KernelComponent χ) := Fintype.ofFinite _
  have hcomm : Pairwise fun i j : KernelComponent χ => ∀ x y : WeylGroup τ,
      x ∈ componentWeylGroup (componentRoots χ i) →
        y ∈ componentWeylGroup (componentRoots χ j) → Commute x y :=
    fun i j hij x y hx hy => commute_of_mem_componentWeylGroup hij hx hy
  obtain ⟨s, rfl⟩ : ∃ s, Subgroup.noncommPiCoprod
      (H := fun i => componentWeylGroup (componentRoots χ i)) hcomm s = u := by
    rw [← MonoidHom.mem_range, Subgroup.noncommPiCoprod_range]
    exact kernelWeylGroup_le_iSup hu
  have hfac : ∀ i, (s i : WeylGroup τ) = 1 := by
    intro i
    have hΨ := isRootComponent_componentRoots (χ := χ) i
    have hcomm' : ((Finset.univ.erase i : Finset (KernelComponent χ)) :
        Set (KernelComponent χ)).Pairwise (Function.onFun Commute fun j => (s j : WeylGroup τ)) :=
      fun j _ k _ h => hcomm h _ _ (s j).2 (s k).2
    have hsplit : Subgroup.noncommPiCoprod (H := fun i => componentWeylGroup (componentRoots χ i))
        hcomm s = (s i : WeylGroup τ) *
          (Finset.univ.erase i).noncommProd (fun j => (s j : WeylGroup τ)) hcomm' := by
      rw [Subgroup.noncommPiCoprod_apply]
      exact (Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ i)
        (fun j => (s j : WeylGroup τ)) _).symm
    have hPmem : (Finset.univ.erase i).noncommProd (fun j => (s j : WeylGroup τ)) hcomm' ∈
        ⨆ j : {j : KernelComponent χ // j ≠ i},
          componentWeylGroup (componentRoots χ (j : KernelComponent χ)) :=
      Subgroup.noncommProd_mem _ _ fun j hj =>
        Subgroup.mem_iSup_of_mem (⟨j, Finset.ne_of_mem_erase hj⟩ : {j // j ≠ i}) (s j).2
    by_contra hne
    obtain ⟨β, hβ, hneg⟩ := exists_smul_mem_negRoots hΨ (s i).2 hne
    have hβΨ := simpleRoots_subset hβ
    obtain ⟨hβk, -⟩ := simpleRoots_subset hβ
    have h1 := hpos β ⟨hβk, simpleRoots_height_pos hβ⟩
    rw [hsplit, mul_smul, smul_eq_of_mem_iSup_ne hPmem hβΨ] at h1
    have h2 := h1.2
    have h3 := hneg.2
    rw [height_neg] at h3
    omega
  have hs : s = 1 := funext fun i => Subtype.ext (hfac i)
  rw [hs, map_one]

theorem kernelWeylGroup_inf_kernelPosStabilizer :
    kernelWeylGroup χ ⊓ kernelPosStabilizer χ = ⊥ := by
  refine eq_bot_iff.2 fun u hu => ?_
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 hu
  refine Subgroup.mem_bot.2 (eq_one_of_mem_kernelWeylGroup hu1 fun α hα => ?_)
  rw [← hu2.2]
  exact ⟨α, hα, rfl⟩

@[expose] def kernelPosStabilizerMulEquiv :
    kernelPosStabilizer χ ≃* CharQuotient χ :=
  MulEquiv.ofBijective ((QuotientGroup.mk' _).comp (Subgroup.inclusion kernelPosStabilizer_le))
    ⟨(MonoidHom.ker_eq_bot_iff _).1 <| eq_bot_iff.2 fun ω hω => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] at hω
      have h : (ω : WeylGroup τ) ∈ kernelWeylGroup χ ⊓ kernelPosStabilizer χ :=
        Subgroup.mem_inf.2 ⟨hω, ω.2⟩
      rw [kernelWeylGroup_inf_kernelPosStabilizer, Subgroup.mem_bot] at h
      exact Subgroup.mem_bot.2 (Subtype.ext h),
    fun q => by
      obtain ⟨ω, hω⟩ := surjective_kernelPosStabilizer (χ := χ) q
      exact ⟨ω, hω⟩⟩

theorem kernelPosStabilizerMulEquiv_apply
    (ω : kernelPosStabilizer χ) :
    kernelPosStabilizerMulEquiv ω =
      (QuotientGroup.mk (⟨ω, kernelPosStabilizer_le ω.2⟩ : charStabilizer χ) : CharQuotient χ) :=
  rfl

theorem existsUnique_mul_of_mem_charStabilizer
    {w : WeylGroup τ} (hw : w ∈ charStabilizer χ) :
    ∃! p : WeylGroup τ × WeylGroup τ, p.1 ∈ kernelWeylGroup χ ∧
      p.2 ∈ kernelPosStabilizer χ ∧ w = p.1 * p.2 := by
  obtain ⟨u, hu, hwu⟩ := exists_mul_mem_kernelPosStabilizer hw
  refine ⟨(w * u⁻¹ * w⁻¹, w * u), ⟨conj_mem_kernelWeylGroup hw (inv_mem hu), hwu, by group⟩, ?_⟩
  rintro p ⟨hu', hω', e⟩
  have hmem : p.2 * (w * u)⁻¹ ∈ kernelWeylGroup χ ⊓ kernelPosStabilizer χ := by
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem hω' (inv_mem hwu)⟩
    have h : p.2 * (w * u)⁻¹ = p.1⁻¹ * (w * u⁻¹ * w⁻¹) := by
      rw [e]
      group
    rw [h]
    exact mul_mem (inv_mem hu') (conj_mem_kernelWeylGroup hw (inv_mem hu))
  rw [kernelWeylGroup_inf_kernelPosStabilizer, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  refine Prod.ext ?_ hmem
  have h : p.1 = w * p.2⁻¹ := by
    rw [e]
    group
  change p.1 = w * u⁻¹ * w⁻¹
  rw [h, hmem]
  group

theorem isElementaryAbelian_of_mulEquiv {p : ℕ} {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : CFSG.IsElementaryAbelian p H) : CFSG.IsElementaryAbelian p G :=
  CFSG.IsElementaryAbelian.of_mulEquiv e.symm h

theorem sign_kernel_positive_Weyl_component_representatives
    (τ : Tag)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) :
    kernelWeylGroup χ = Subgroup.closure (rootReflection '' kernelRoots χ) ∧
    kernelPosStabilizer χ ≤ charStabilizer χ ∧ kernelWeylGroup χ ≤ charStabilizer χ ∧
    ((kernelWeylGroup χ).subgroupOf (charStabilizer χ)).Normal ∧
    (∀ w ∈ charStabilizer χ, ∃! p : WeylGroup τ × WeylGroup τ, p.1 ∈ kernelWeylGroup χ ∧
      p.2 ∈ kernelPosStabilizer χ ∧ w = p.1 * p.2) ∧
    (∃ e : kernelPosStabilizer χ ≃* CharQuotient χ, ∀ ω : kernelPosStabilizer χ,
      e ω = (QuotientGroup.mk (⟨ω, kernelPosStabilizer_le ω.2⟩ : charStabilizer χ) :
        CharQuotient χ)) ∧
    ((τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) → Nat.card (kernelPosStabilizer χ) = 1) ∧
    (τ = .E7 → Nat.card (kernelPosStabilizer χ) ∣ 2) ∧
    (τ = .D4 → Nat.card (kernelPosStabilizer χ) ∣ 4 ∧
      CFSG.IsElementaryAbelian 2 (kernelPosStabilizer χ)) := by
  obtain ⟨-, -, hGFE, hE7, hD4⟩ := sign_character_Weyl_stabilizer_quotients τ χ
  have hcard : Nat.card (kernelPosStabilizer χ) = Nat.card (CharQuotient χ) :=
    Nat.card_congr kernelPosStabilizerMulEquiv.toEquiv
  refine ⟨kernelWeylGroup_eq_closure, kernelPosStabilizer_le, kernelWeylGroup_le, inferInstance,
    fun w hw => existsUnique_mul_of_mem_charStabilizer hw,
    ⟨kernelPosStabilizerMulEquiv, kernelPosStabilizerMulEquiv_apply⟩, fun h => ?_,
    fun h => by rw [hcard]; exact hE7 h, fun h => ?_⟩
  ·
    rw [hcard]
    exact Subgroup.index_eq_one.2 (Subgroup.subgroupOf_eq_top.2 (hGFE h).le)
  · obtain ⟨h1, h2⟩ := hD4 h
    exact ⟨by rw [hcard]; exact h1, isElementaryAbelian_of_mulEquiv kernelPosStabilizerMulEquiv h2⟩

end CFSG.LieType.Chevalley
