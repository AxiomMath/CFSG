module

public import CFSG.Holt.H78.Sec4Prop43R
import CFSG.Holt.H78.Sec4Box
import CFSG.Holt.H78.Sec4Prop43W
public import CFSG.Holt.H78.Sec4Prop43B6

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

section KleinPerm

variable {Ψ : Type*} [DecidableEq Ψ]

theorem mul_swap_mul_swap_mem_longInvAt {x : Equiv.Perm Ψ} {p : Ψ}
    (hx : x ∈ longInvAt (Equiv.Perm Ψ) Ψ p) {a b c d : Ψ} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hxa : x a = b) (hxc : x c = d) :
    x * Equiv.swap a d * Equiv.swap b c ∈ longInvAt (Equiv.Perm Ψ) Ψ p ∧
      (x * Equiv.swap a d * Equiv.swap b c) a = c ∧
      x * (x * Equiv.swap a d * Equiv.swap b c) = x * Equiv.swap a d * Equiv.swap b c * x ∧
      (x * (x * Equiv.swap a d * Equiv.swap b c)) c = b ∧
      ∀ π : Equiv.Perm Ψ, π a = a → π b = b → π c = c → π d = d → π * x = x * π →
        π * (x * Equiv.swap a d * Equiv.swap b c) = x * Equiv.swap a d * Equiv.swap b c * π := by
  have hxx := CCL.apply_apply_of_mem_longInv hx.1
  have hxb : x b = a := by rw [← hxa, hxx]
  have hxd : x d = c := by rw [← hxc, hxx]
  have hxp : x p = p := hx.2
  have hpa : p ≠ a := fun h => hab (by rw [← hxa, ← h, hxp, h])
  have hpb : p ≠ b := fun h => hab (by rw [← hxb, ← h, hxp, h])
  have hpc : p ≠ c := fun h => hcd (by rw [← hxc, ← h, hxp, h])
  have hpd : p ≠ d := fun h => hcd (by rw [← hxd, ← h, hxp, h])
  set σ := Equiv.swap a d * Equiv.swap b c with hσ
  have hnd : [a, d, b, c].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false,
      not_or]
    exact ⟨⟨had, hab, hac⟩, ⟨hbd.symm, hcd.symm⟩, hbc, not_false, trivial⟩
  have hcomm : Equiv.swap a d * Equiv.swap b c = Equiv.swap b c * Equiv.swap a d :=
    (Equiv.Perm.disjoint_swap_swap hnd).commute.eq
  have hσx : x * σ = σ * x := by
    have h1 : x * Equiv.swap a d * x⁻¹ = Equiv.swap b c := by
      rw [← Equiv.swap_apply_apply, hxa, hxd]
    have h2 : x * Equiv.swap b c * x⁻¹ = Equiv.swap a d := by
      rw [← Equiv.swap_apply_apply, hxb, hxc]
    have h3 : x * σ * x⁻¹ = σ := by
      rw [hσ, show x * (Equiv.swap a d * Equiv.swap b c) * x⁻¹ =
        (x * Equiv.swap a d * x⁻¹) * (x * Equiv.swap b c * x⁻¹) by group, h1, h2, hcomm]
    calc x * σ = x * σ * x⁻¹ * x := by group
      _ = σ * x := by rw [h3]
  have hσσ : σ * σ = 1 := by
    rw [hσ, show Equiv.swap a d * Equiv.swap b c * (Equiv.swap a d * Equiv.swap b c) =
      Equiv.swap a d * (Equiv.swap b c * Equiv.swap a d) * Equiv.swap b c by group, ← hcomm,
      show Equiv.swap a d * (Equiv.swap a d * Equiv.swap b c) * Equiv.swap b c =
        (Equiv.swap a d * Equiv.swap a d) * (Equiv.swap b c * Equiv.swap b c) by group,
      Equiv.swap_mul_self, Equiv.swap_mul_self, one_mul]
  have hx2 : x * x = 1 := Equiv.ext fun z => hxx z
  have hσa : σ a = d := by simp [hσ, Equiv.swap_apply_of_ne_of_ne hab hac]
  have hσb : σ b = c := by simp [hσ, Equiv.swap_apply_of_ne_of_ne hac.symm hcd]
  have hσc : σ c = b := by simp [hσ, Equiv.swap_apply_of_ne_of_ne hab.symm hbd]
  have hσd : σ d = a := by simp [hσ, Equiv.swap_apply_of_ne_of_ne hbd.symm hcd.symm]
  have hσz : ∀ z, z ≠ a → z ≠ b → z ≠ c → z ≠ d → σ z = z := fun z h1 h2 h3 h4 => by
    simp [hσ, Equiv.swap_apply_of_ne_of_ne h1 h4, Equiv.swap_apply_of_ne_of_ne h2 h3]
  have hy : x * σ = x * Equiv.swap a d * Equiv.swap b c := by rw [hσ, mul_assoc]
  rw [← hy]
  have hya : (x * σ) a = c := by rw [Equiv.Perm.mul_apply, hσa, hxd]
  refine ⟨⟨⟨orderOf_eq_prime (by
      rw [sq, show x * σ * (x * σ) = x * (σ * x) * σ by group, ← hσx,
        show x * (x * σ) * σ = x * x * (σ * σ) by group, hx2, hσσ, one_mul])
      fun h => hac (by rw [← hya, h]; rfl), p, ?_, ?_⟩, ?_⟩,
    hya, by rw [← mul_assoc, hx2, one_mul, mul_assoc, ← hσx, ← mul_assoc, hx2, one_mul], ?_,
    fun π ha hb hc hd hπx => ?_⟩
  · change x (σ p) = p
    rw [hσz p hpa hpb hpc hpd, hxp]
  · intro z hz
    change x (σ z) = z at hz
    by_cases h1 : z = a
    · rw [h1, hσa, hxd] at hz; exact absurd hz.symm hac
    by_cases h2 : z = b
    · rw [h2, hσb, hxc] at hz; exact absurd hz.symm hbd
    by_cases h3 : z = c
    · rw [h3, hσc, hxb] at hz; exact absurd hz hac
    by_cases h4 : z = d
    · rw [h4, hσd, hxa] at hz; exact absurd hz hbd
    rw [hσz z h1 h2 h3 h4] at hz
    exact (hx.1.2.unique hz hxp)
  · change x (σ p) = p
    rw [hσz p hpa hpb hpc hpd, hxp]
  · rw [← mul_assoc, hx2, one_mul, hσc]
  · have h1 : π * Equiv.swap a d * π⁻¹ = Equiv.swap a d := by rw [← Equiv.swap_apply_apply, ha, hd]
    have h2 : π * Equiv.swap b c * π⁻¹ = Equiv.swap b c := by rw [← Equiv.swap_apply_apply, hb, hc]
    have h3 : π * σ = σ * π := by
      have : π * σ * π⁻¹ = σ := by
        rw [hσ, show π * (Equiv.swap a d * Equiv.swap b c) * π⁻¹ =
          (π * Equiv.swap a d * π⁻¹) * (π * Equiv.swap b c * π⁻¹) by group, h1, h2]
      calc π * σ = π * σ * π⁻¹ * π := by group
        _ = σ * π := by rw [this]
    calc π * (x * σ) = π * x * σ := by group
      _ = x * π * σ := by rw [hπx]
      _ = x * (π * σ) := by group
      _ = x * (σ * π) := by rw [h3]
      _ = x * σ * π := by group

end KleinPerm

namespace AltConfig

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} (C : AltConfig G Ω α β)

@[expose] def line : Set Ω :=
  (↑) '' {δ : holtDelta G Ω α β | ∀ i, i ≠ C.i₁ → C.D.coord δ i = C.D.coord C.γ i}

@[expose] def lineKer : Subgroup G := C.calP ⊓ fixingSubgroup G C.line

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_line_iff (δ : holtDelta G Ω α β) :
    (δ : Ω) ∈ C.line ↔ ∀ i, i ≠ C.i₁ → C.D.coord δ i = C.D.coord C.γ i :=
  ⟨fun ⟨δ', hδ', h⟩ => (Subtype.ext h : δ' = δ) ▸ hδ', fun h => ⟨δ, h, rfl⟩⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem line_subset_holtDelta : C.line ⊆ holtDelta G Ω α β := by
  rintro _ ⟨δ, -, rfl⟩
  exact δ.2

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem γ_mem_line : (C.γ : Ω) ∈ C.line := (C.mem_line_iff C.γ).mpr fun _ _ => rfl

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem linePoint_mem (c : C.D.Ψc C.i₁) :
    ((C.coordEquiv.symm (Function.update (C.D.coord C.γ) C.i₁ c) : holtDelta G Ω α β) : Ω) ∈
      C.line :=
  (C.mem_line_iff _).mpr fun i hi => by rw [C.coord_coordEquiv_symm, Function.update_of_ne hi]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem lineKer_le_calP : C.lineKer ≤ C.calP := inf_le_left

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem isPGroup_lineKer : IsPGroup 2 C.lineKer :=
  C.sylow.2.1.to_le (C.lineKer_le_calP.trans inf_le_left)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem lineKer_le_inf : C.lineKer ≤ stabilizer G α ⊓ stabilizer G β :=
  C.lineKer_le_calP.trans (C.calP_le_calG.trans C.calG_le_inf)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem kerC_inf_le_lineKer {j : C.D.ι} (hj : j ≠ C.i₁) : C.calP ⊓ C.kerC j ≤ C.lineKer := by
  rintro q ⟨hqP, hqK⟩
  refine ⟨hqP, (mem_fixingSubgroup_iff G).mpr ?_⟩
  rintro _ ⟨δ, hδ, rfl⟩
  exact C.smul_eq_of_mem_kerC hqK (hδ j hj)

omit [FaithfulSMul G Ω] in
theorem exists_mem_Qimg_apply_ne (hS : Sec4Setting G Ω) (hP : fusionIsSylowIn 2 C.calP C.calG)
    {j : C.D.ι} {c : C.D.Ψc j} (hc : c ≠ C.D.coord C.γ j) :
    ∃ u ∈ C.Qimg j, u c ≠ c := by
  classical
  have hU := C.fusionIsSylowIn_Qimg_inf hS hP j
  rw [← fixingSubgroup_singleton_perm] at hU
  have hcard : Nat.card ↥(({C.D.coord C.γ j} : Set (C.D.Ψc j))ᶜ) =
      Fintype.card (C.D.Ψc j) - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_compl_set]
    simp
  have hfix := fixSet_eq_of_fusionIsSylowIn_alternatingGroup_inf_fixingSubgroup (by
      rw [hcard]
      obtain ⟨k, hk⟩ := C.D.odd_card_Ψc j
      exact ⟨k, by omega⟩)
    (by rw [hcard]; have := C.D.five_le_card j; omega) hU
  have hcf : c ∉ fixSet (C.D.Ψc j) (C.Qimg j ⊓ alternatingGroup (C.D.Ψc j)) := by
    rw [hfix]
    exact hc
  simp only [fixSet, Set.mem_ofPred_eq, not_forall] at hcf
  obtain ⟨u, hu, huc⟩ := hcf
  exact ⟨u, (Subgroup.mem_inf.mp hu).1, huc⟩

omit [FaithfulSMul G Ω] in
theorem mem_fixSet_lineKer_iff (hS : Sec4Setting G Ω) (hP : fusionIsSylowIn 2 C.calP C.calG)
    (δ : holtDelta G Ω α β) : (δ : Ω) ∈ fixSet Ω C.lineKer ↔ (δ : Ω) ∈ C.line := by
  refine ⟨fun h => ?_, fun h x hx => (mem_fixingSubgroup_iff G).mp hx.2 _ h⟩
  rw [C.mem_line_iff]
  intro j hj
  by_contra hne
  obtain ⟨u, hu, huδ⟩ := C.exists_mem_Qimg_apply_ne hS hP hne
  obtain ⟨q, hqP, rfl⟩ := C.exists_of_mem_Qimg hu
  exact C.smul_ne_of_kerCHom_ne q huδ (h q (C.kerC_inf_le_lineKer hj ⟨hqP, q.2⟩))

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem smul_mem_line {g : G} (hg : g ∈ C.calG) {ω : Ω} (hω : ω ∈ C.line) :
    g • ω ∈ C.line := by
  obtain ⟨δ, hδ, rfl⟩ := hω
  have hgS := C.calG_le_stabilizer_pair hg
  have hgγ : g • (C.γ : Ω) = C.γ := C.calG_le_stabilizer_γ hg
  obtain ⟨σ, hσ⟩ := C.exists_mapsDir hgS
  have hσ₁ : σ C.i₁ = C.i₁ := MapsDir.eq C hgS (hσ C.i₁) (C.mapsDir_i₁ (Subgroup.mem_inf.mp hg).2)
  refine (C.mem_line_iff (twoPointElt hgS • δ)).mpr fun m hm => ?_
  have hl : σ.symm m ≠ C.i₁ := fun h => hm (by
    have h' := hσ₁
    rw [← h, Equiv.apply_symm_apply] at h'
    exact h'.trans h)
  have h := hσ (σ.symm m) δ C.γ (twoPointElt hgS • δ) C.γ rfl hgγ.symm
  rw [Equiv.apply_symm_apply] at h
  exact h.mpr (hδ _ hl)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_calG_of_mem_fixingSubgroup_line {g : G}
    (hg : g ∈ stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G C.line) : g ∈ C.calG := by
  obtain ⟨hgαβ, hgL⟩ := Subgroup.mem_inf.mp hg
  have hgS := stabilizer_inf_le_stabilizer_pair α β hgαβ
  have hfix : ∀ ω ∈ C.line, g • ω = ω := (mem_fixingSubgroup_iff G).mp hgL
  obtain ⟨σ, hσ⟩ := C.exists_mapsDir hgS
  have hσ₁ : σ C.i₁ = C.i₁ := by
    by_contra hk
    have := C.nontrivial_Ψc C.i₁
    obtain ⟨c, hc⟩ := exists_ne (C.D.coord C.γ C.i₁)
    set δ := C.coordEquiv.symm (Function.update (C.D.coord C.γ) C.i₁ c)
    have hδ : C.D.coord δ = Function.update (C.D.coord C.γ) C.i₁ c := C.coord_coordEquiv_symm _
    have h := (hσ C.i₁ δ C.γ δ C.γ (hfix _ (C.linePoint_mem c)).symm
      (hfix _ C.γ_mem_line).symm).mp (by rw [hδ, Function.update_of_ne hk])
    rw [hδ, Function.update_self] at h
    exact hc h
  have hN := C.mem_twoPointNormalizer_of_mapsDir hgS (hσ₁ ▸ hσ C.i₁)
  exact ⟨⟨hgαβ, hfix _ C.γ_mem_line⟩, hN⟩

omit [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem fusionIsSylowIn_lineKer (hP : fusionIsSylowIn 2 C.calP C.calG) :
    fusionIsSylowIn 2 C.lineKer (stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G C.line) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := fusionIsSylowIn_inf_of_conj_mem' hP
    (fun g hg => C.mem_calG_of_mem_fixingSubgroup_line hg) (by
      intro h hh n hn
      obtain ⟨hnαβ, hnL⟩ := Subgroup.mem_inf.mp hn
      obtain ⟨hnα, hnβ⟩ := Subgroup.mem_inf.mp hnαβ
      obtain ⟨hhα, hhβ⟩ := Subgroup.mem_inf.mp (C.calG_le_inf hh)
      rw [mem_stabilizer_iff] at hnα hnβ hhα hhβ
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩,
        (mem_fixingSubgroup_iff G).mpr fun ω hω => ?_⟩
      · rw [mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff.mpr hhα.symm, hnα, hhα]
      · rw [mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff.mpr hhβ.symm, hnβ, hhβ]
      · have h1 := C.smul_mem_line (inv_mem hh) hω
        rw [mul_smul, mul_smul, (mem_fixingSubgroup_iff G).mp hnL _ h1, smul_inv_smul])
  have he : C.calP ⊓ (stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G C.line) = C.lineKer := by
    rw [← inf_assoc, inf_eq_left.mpr (C.calP_le_calG.trans C.calG_le_inf)]
    rfl
  rwa [he] at h

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem ncard_line : C.line.ncard = Fintype.card (C.D.Ψc C.i₁) := by
  set φ : C.D.Ψc C.i₁ → Ω := fun c =>
    ((C.coordEquiv.symm (Function.update (C.D.coord C.γ) C.i₁ c) : holtDelta G Ω α β) : Ω)
  have hφ : Function.Injective φ := by
    intro c c' h
    have h1 := congrArg (fun δ => C.D.coord δ C.i₁) (Subtype.ext h :
      C.coordEquiv.symm (Function.update (C.D.coord C.γ) C.i₁ c) =
        C.coordEquiv.symm (Function.update (C.D.coord C.γ) C.i₁ c'))
    simpa using h1
  have hr : Set.range φ = C.line := by
    refine Set.Subset.antisymm (by rintro _ ⟨c, rfl⟩; exact C.linePoint_mem c) ?_
    rintro _ ⟨δ, hδ, rfl⟩
    refine ⟨C.D.coord δ C.i₁, congrArg Subtype.val (C.eq_of_coord_eq ?_)⟩
    rw [C.coord_coordEquiv_symm]
    funext i
    by_cases hi : i = C.i₁
    · subst hi
      rw [Function.update_self]
    · rw [Function.update_of_ne hi, hδ i hi]
  rw [← hr, Set.ncard_range_of_injective hφ, Nat.card_eq_fintype_card]

omit [FaithfulSMul G Ω] in
theorem lineKer_ne_bot (hS : Sec4Setting G Ω) (hP : fusionIsSylowIn 2 C.calP C.calG)
    (hr : ∃ j, j ≠ C.i₁) : C.lineKer ≠ ⊥ := by
  intro h
  obtain ⟨j, hj⟩ := hr
  have := C.nontrivial_Ψc j
  obtain ⟨c, hc⟩ := exists_ne (C.D.coord C.γ j)
  set δ := C.coordEquiv.symm (Function.update (C.D.coord C.γ) j c)
  have hδ : (δ : Ω) ∈ fixSet Ω C.lineKer := by
    rw [h]
    intro g hg
    rw [Subgroup.mem_bot.mp hg, one_smul]
  have h1 := (C.mem_line_iff δ).mp ((C.mem_fixSet_lineKer_iff hS hP δ).mp hδ) j hj
  rw [C.coord_coordEquiv_symm, Function.update_self] at h1
  exact hc h1

theorem exists_holtData_lineKer (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hP : fusionIsSylowIn 2 C.calP C.calG) (hr : ∃ j, j ≠ C.i₁) :
    ∃ (D : HoltData (centralizerImage Ω C.lineKer) (fixSet Ω C.lineKer)) (k : D.ι),
      (∀ k', k' = k) ∧ factorImage _ _ (D.L k) (D.ρ k) = alternatingGroup (D.Ψc k) ∧
      Fintype.card (D.Ψc k) = Fintype.card (C.D.Ψc C.i₁) + 2 ∧
      ∀ x y : fixSet Ω C.lineKer, ((x : Ω) = α ∨ (x : Ω) = β ∨ (x : Ω) ∈ C.line) →
        ((y : Ω) = α ∨ (y : Ω) = β ∨ (y : Ω) ∈ C.line) → D.coord x k = D.coord y k → x = y := by
  classical
  have hX := C.isPGroup_lineKer
  have hXαβ := C.lineKer_le_inf
  have hX1 := C.lineKer_ne_bot hS hP hr
  set a : fixSet Ω C.lineKer := ⟨α, mem_fixSet_iff_le_stabilizer.mpr (hXαβ.trans inf_le_left)⟩
  set b : fixSet Ω C.lineKer := ⟨β, mem_fixSet_iff_le_stabilizer.mpr (hXαβ.trans inf_le_right)⟩
  have hab : a ≠ b := fun h => hαβ (congrArg Subtype.val h)
  have h3 := hS.three_le_card_fixSet_of_ne hX hab
  set Λc : ∀ i, Set (C.D.Ψc i) := fun i =>
    (fun δ : holtDelta G Ω α β => C.D.coord δ i) '' (Subtype.val ⁻¹' C.line) with hΛc
  have hbox : ∀ δ : holtDelta G Ω α β,
      (δ : Ω) ∈ fixSet Ω C.lineKer ↔ ∀ i, C.D.coord δ i ∈ Λc i := by
    intro δ
    rw [C.mem_fixSet_lineKer_iff hS hP δ]
    refine ⟨fun h i => ⟨δ, h, rfl⟩, fun h => (C.mem_line_iff δ).mpr fun i hi => ?_⟩
    obtain ⟨δ', hδ', he⟩ := h i
    rw [← he]
    exact (C.mem_line_iff δ').mp hδ' i hi
  have hΛ₁ : Λc C.i₁ = Set.univ := Set.eq_univ_of_forall fun c =>
    ⟨_, C.linePoint_mem c, by simp⟩
  have hΛj : ∀ j, ¬ j = C.i₁ → (Λc j).Subsingleton := by
    rintro j hj _ ⟨δ, hδ, rfl⟩ _ ⟨δ', hδ', rfl⟩
    change C.D.coord δ j = C.D.coord δ' j
    rw [(C.mem_line_iff δ).mp hδ j hj, (C.mem_line_iff δ').mp hδ' j hj]
  have hnt : (Λc C.i₁).Nontrivial := by
    rw [hΛ₁]
    have := C.nontrivial_Ψc C.i₁
    exact Set.nontrivial_univ
  obtain ⟨e, he, hcoord, hreal⟩ := hS.exists_boxEquiv_ccl hαβ C.D C.oddCore_eq_bot C.alt hX
    (a := a) (b := b) rfl rfl Λc hbox (p := fun i => i = C.i₁) (fun i h => h ▸ hnt) hΛj
  obtain ⟨DK⟩ := hS.holtData_centralizerImage hX hX1 h3
  have hcard₁ : Fintype.card ↥(Λc C.i₁) = Fintype.card (C.D.Ψc C.i₁) := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hΛ₁, Set.ncard_univ,
      Nat.card_eq_fintype_card]
  have h5' : ∀ j : {i // i = C.i₁}, 5 ≤ Fintype.card (Λc j) := by
    rintro ⟨j, rfl⟩
    rw [hcard₁]
    exact C.D.five_le_card _
  have hodd := hS.odd_card_inf_fixingSubgroup_centralizerImage hαβ hX C.line_subset_holtDelta
    (C.fusionIsSylowIn_lineKer hP) (a := a) (b := b) rfl rfl
  obtain ⟨c, -, hca, -, hcd⟩ := DK.ccl (hS.star_centralizerImage hX h3)
    (hS.holtTheorem1Below_centralizerImage hX hX1 h3) hab e h5' hcoord hreal
  set i₁' : {i // i = C.i₁} := ⟨C.i₁, rfl⟩
  have hi₁' : ∀ j : {i // i = C.i₁}, j = i₁' := fun j => Subtype.ext j.2
  obtain ⟨hA, hcard, habk, hδk⟩ := hca i₁'
  refine ⟨DK, c i₁', fun k' => ?_, hA, ?_, ?_⟩
  · obtain ⟨j, rfl⟩ : k' ∈ Set.range c := (hcd hodd).symm ▸ Set.mem_univ k'
    rw [hi₁' j]
  · rw [hcard]
    exact congrArg (· + 2) hcard₁
  · have hK : ∀ x : fixSet Ω C.lineKer, (x : Ω) ∈ C.line →
        x ∈ holtDelta (centralizerImage Ω C.lineKer) (fixSet Ω C.lineKer) a b := fun x hx =>
      (hS.mem_holtDelta_centralizerImage_iff hX h3 hab).mpr (C.line_subset_holtDelta hx)
    have hxa : ∀ x : fixSet Ω C.lineKer, (x : Ω) = α → x = a := fun x hx => Subtype.ext hx
    have hxb : ∀ x : fixSet Ω C.lineKer, (x : Ω) = β → x = b := fun x hx => Subtype.ext hx
    intro x y hx hy hxy
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
    · exact (hxa x hx).trans (hxa y hy).symm
    · rw [hxa x hx, hxb y hy] at hxy
      exact absurd hxy habk
    · rw [hxa x hx] at hxy
      exact absurd hxy.symm (hδk ⟨y, hK y hy⟩ ⟨y, hK y hy⟩).2.1
    · rw [hxb x hx, hxa y hy] at hxy
      exact absurd hxy.symm habk
    · exact (hxb x hx).trans (hxb y hy).symm
    · rw [hxb x hx] at hxy
      exact absurd hxy.symm (hδk ⟨y, hK y hy⟩ ⟨y, hK y hy⟩).2.2
    · rw [hxa y hy] at hxy
      exact absurd hxy (hδk ⟨x, hK x hx⟩ ⟨x, hK x hx⟩).2.1
    · rw [hxb y hy] at hxy
      exact absurd hxy (hδk ⟨x, hK x hx⟩ ⟨x, hK x hx⟩).2.2
    · have h1 := ((hδk ⟨x, hK x hx⟩ ⟨y, hK y hy⟩).1).mp hxy
      have h2 : e ⟨x, hK x hx⟩ = e ⟨y, hK y hy⟩ := funext fun j => by rw [hi₁' j]; exact h1
      exact congrArg Subtype.val (e.injective h2)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem smul_linePoint_eq (q : C.kerC C.i₁) {c : C.D.Ψc C.i₁} (hq : C.kerCHom C.i₁ q c = c) :
    (q : G) • ((C.coordEquiv.symm (Function.update (C.D.coord C.γ) C.i₁ c) :
      holtDelta G Ω α β) : Ω) = C.coordEquiv.symm (Function.update (C.D.coord C.γ) C.i₁ c) := by
  refine C.smul_eq_of_kerCHom_fix q (Λc := Function.update (fun _ => Set.univ) C.i₁ {c})
    (fun x hx => ?_) _ fun j => ?_
  · rw [Function.update_self, Set.mem_singleton_iff] at hx
    rw [hx]
    exact hq
  · by_cases hj : j = C.i₁
    · subst hj
      rw [Function.update_self, C.coord_coordEquiv_symm, Function.update_self]
      exact rfl
    · rw [Function.update_of_ne hj]
      exact Set.mem_univ _

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem eq_one_of_mem_lineKer_of_mem_kerC (hT : Odd (Nat.card (twoPointKernel G Ω α β)))
    {g : G} (hgX : g ∈ C.lineKer) (hgK : g ∈ C.kerC C.i₁) : g = 1 := by
  refine C.eq_one_of_kerCHom_eq_one hT (q := ⟨g, hgK⟩) (C.lineKer_le_calP hgX)
    (Equiv.ext fun c => ?_)
  set δ := C.coordEquiv.symm (Function.update (C.D.coord C.γ) C.i₁ c)
  have h := C.coord_smul_eq_kerCHom ⟨g, hgK⟩ (δ := δ) (δ' := δ)
    ((mem_fixingSubgroup_iff G).mp hgX.2 _ (C.linePoint_mem c)).symm
  rw [C.coord_coordEquiv_symm, Function.update_self] at h
  exact h.symm

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem conj_mem_lineKer {p : G} (hp : p ∈ C.calP) {x : G} (hx : x ∈ C.lineKer) :
    p * x * p⁻¹ ∈ C.lineKer := by
  refine ⟨C.calP.mul_mem (C.calP.mul_mem hp hx.1) (C.calP.inv_mem hp),
    (mem_fixingSubgroup_iff G).mpr fun ω hω => ?_⟩
  have h1 := C.smul_mem_line (C.calG.inv_mem (C.calP_le_calG hp)) hω
  rw [mul_smul, mul_smul, (mem_fixingSubgroup_iff G).mp hx.2 _ h1, smul_inv_smul]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem commute_of_mem_kerC_of_mem_lineKer (hT : Odd (Nat.card (twoPointKernel G Ω α β)))
    {v : G} (hvP : v ∈ C.calP) (hvK : v ∈ C.kerC C.i₁) {x : G} (hx : x ∈ C.lineKer) :
    v * x = x * v := by
  have h1 : v * x * v⁻¹ * x⁻¹ ∈ C.lineKer :=
    C.lineKer.mul_mem (C.conj_mem_lineKer hvP hx) (C.lineKer.inv_mem hx)
  have h2 : v * x * v⁻¹ * x⁻¹ ∈ C.kerC C.i₁ := by
    rw [show v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) by group]
    exact (C.kerC C.i₁).mul_mem hvK
      (C.conj_mem_kerC_i₁ (C.calP_le_calG hx.1) ((C.kerC C.i₁).inv_mem hvK))
  have h3 := C.eq_one_of_mem_lineKer_of_mem_kerC hT h1 h2
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  exact h3

theorem notMem_orbit_jOddCore_linePoint (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hT : Odd (Nat.card (twoPointKernel G Ω α β))) (hP : fusionIsSylowIn 2 C.calP C.calG)
    (hr : ∃ j, j ≠ C.i₁) {V : Subgroup G} (hVQ : V ≤ C.calP ⊓ C.kerC C.i₁)
    {c₁ c₂ : C.D.Ψc C.i₁} (hc₁ : c₁ ≠ C.D.coord C.γ C.i₁) (hc₂ : c₂ ≠ C.D.coord C.γ C.i₁)
    (hc₁₂ : c₁ ≠ c₂)
    (hfix : ∀ v : C.kerC C.i₁, (v : G) ∈ V →
      C.kerCHom C.i₁ v c₁ = c₁ ∧ C.kerCHom C.i₁ v c₂ = c₂)
    (γV γ'V : fixSet Ω V) (hγV : (γV : Ω) = C.γ)
    (hγ'V : (γ'V : Ω) = C.coordEquiv.symm (Function.update (C.D.coord C.γ) C.i₁ c₁)) :
    γ'V ∉ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) γV := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set δ₁ := C.coordEquiv.symm (Function.update (C.D.coord C.γ) C.i₁ c₁) with hδ₁
  set δ₂ := C.coordEquiv.symm (Function.update (C.D.coord C.γ) C.i₁ c₂) with hδ₂
  have hcδ₁ : C.D.coord δ₁ = Function.update (C.D.coord C.γ) C.i₁ c₁ := C.coord_coordEquiv_symm _
  have hcδ₂ : C.D.coord δ₂ = Function.update (C.D.coord C.γ) C.i₁ c₂ := C.coord_coordEquiv_symm _
  have hne : ∀ δ δ' : holtDelta G Ω α β, C.D.coord δ C.i₁ ≠ C.D.coord δ' C.i₁ →
      (δ : Ω) ≠ δ' := fun δ δ' h h' => h (by rw [(Subtype.ext h' : δ = δ')])
  have hγδ₁ : (C.γ : Ω) ≠ δ₁ := hne _ _ (by rw [hcδ₁, Function.update_self]; exact hc₁.symm)
  have hγδ₂ : (C.γ : Ω) ≠ δ₂ := hne _ _ (by rw [hcδ₂, Function.update_self]; exact hc₂.symm)
  have hδ₁δ₂ : (δ₁ : Ω) ≠ δ₂ := hne _ _ (by
    rw [hcδ₁, hcδ₂, Function.update_self, Function.update_self]
    exact hc₁₂)
  have hαΔ : ∀ δ : holtDelta G Ω α β, (δ : Ω) ≠ α := fun δ h =>
    left_notMem_holtDelta (G := G) hαβ (by have := δ.2; rwa [h] at this)
  have hβΔ : ∀ δ : holtDelta G Ω α β, (δ : Ω) ≠ β := fun δ h =>
    right_notMem_holtDelta (G := G) hαβ (by have := δ.2; rwa [h] at this)
  have hVα : ∀ v ∈ V, v • α = α := fun v hv =>
    mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (C.kerC_le_inf _ (hVQ hv).2)).1
  have hVβ : ∀ v ∈ V, v • β = β := fun v hv =>
    mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (C.kerC_le_inf _ (hVQ hv).2)).2
  have hVγ : ∀ v ∈ V, v • (C.γ : Ω) = C.γ := fun v hv => C.smul_eq_of_mem_kerC (hVQ hv).2 rfl
  have hVδ₁ : ∀ v ∈ V, v • (δ₁ : Ω) = δ₁ := fun v hv =>
    C.smul_linePoint_eq ⟨v, (hVQ hv).2⟩ (hfix _ hv).1
  have hVδ₂ : ∀ v ∈ V, v • (δ₂ : Ω) = δ₂ := fun v hv =>
    C.smul_linePoint_eq ⟨v, (hVQ hv).2⟩ (hfix _ hv).2
  set X := C.lineKer with hXdef
  have hX := C.isPGroup_lineKer
  have hXαβ := C.lineKer_le_inf
  have hXfix : ∀ ω ∈ C.line, ∀ x ∈ X, x • ω = ω := fun ω hω x hx =>
    (mem_fixingSubgroup_iff G).mp hx.2 ω hω
  have hXV : X ≤ Subgroup.centralizer (V : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      C.commute_of_mem_kerC_of_mem_lineKer hT (hVQ hv).1 (hVQ hv).2 hx
  have hVX : V ≤ Subgroup.centralizer (X : Set G) := Subgroup.le_centralizer_iff.mp hXV
  set W := V ⊔ X with hWdef
  have hW : IsPGroup 2 W := C.sylow.2.1.to_le (sup_le (hVQ.trans (inf_le_left.trans inf_le_left))
    (C.lineKer_le_calP.trans inf_le_left))
  have hWαβ : W ≤ stabilizer G α ⊓ stabilizer G β :=
    sup_le (fun v hv => ⟨hVα v hv, hVβ v hv⟩) hXαβ
  have hWfix : ∀ ω, (∀ v ∈ V, v • ω = ω) → (∀ x ∈ X, x • ω = ω) → ω ∈ fixSet Ω W :=
    fun ω h1 h2 => mem_fixSet_iff_le_stabilizer.mpr (sup_le (fun v hv => h1 v hv)
      fun x hx => h2 x hx)
  have hγW := hWfix _ hVγ (hXfix _ C.γ_mem_line)
  have hδ₁W := hWfix _ hVδ₁ (hXfix _ (C.linePoint_mem c₁))
  have hδ₂W := hWfix _ hVδ₂ (hXfix _ (C.linePoint_mem c₂))
  have h3i : ∀ j, 3 ≤ Fintype.card (C.D.Ψc j) := fun j => by have := C.D.five_le_card j; omega
  obtain ⟨t₀, ht₀⟩ := exists_mem_longInvAt_perm (C.D.odd_card_Ψc C.i₁) (h3i C.i₁)
    (C.D.coord C.γ C.i₁)
  obtain ⟨t, ht, htc⟩ := exists_mem_longInvAt_perm_apply_eq ht₀ hc₁ hc₂ (Ne.symm hc₁₂)
  have htc' : t c₂ = c₁ := by rw [← htc, CCL.apply_apply_of_mem_longInv ht.1]
  obtain ⟨z, hz⟩ := CCL.exists_forall_mem_longInvAt (fun j => C.D.odd_card_Ψc j) h3i
    (C.D.coord C.γ)
  have hyt := CCL.update_mem_longInvAt hz ht
  obtain ⟨u, hu, hucoord⟩ := hS.exists_mem_longInvSwap_coord_smul hαβ C.D C.alt
    (Function.update z C.i₁ t) fun j => (hyt j).1
  have humem : ∀ δ : holtDelta G Ω α β, u • (δ : Ω) ∈ holtDelta G Ω α β := fun δ => by
    have h := mem_stabilizer_iff.mp (mem_stabilizer_holtDelta_of_mem_longInvSwap hu)
    have h1 : u • (δ : Ω) ∈ u • holtDelta G Ω α β := Set.smul_mem_smul_set δ.2
    rwa [h] at h1
  have hu_eq : ∀ δ δ' : holtDelta G Ω α β,
      C.D.coord δ' = (fun j => Function.update z C.i₁ t j (C.D.coord δ j)) →
        u • (δ : Ω) = δ' := fun δ δ' h => by
    have h1 := hucoord δ ⟨_, humem δ⟩ rfl
    exact congrArg Subtype.val (C.eq_of_coord_eq (h1.trans h.symm))
  have huγ : u • (C.γ : Ω) = C.γ := hu_eq _ _ (funext fun j => ((hyt j).2).symm)
  have huδ₁ : u • (δ₁ : Ω) = δ₂ := hu_eq _ _ (funext fun j => by
    rw [hcδ₁, hcδ₂]
    by_cases hj : j = C.i₁
    · subst hj
      rw [Function.update_self, Function.update_self, Function.update_self, htc]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj, Function.update_of_ne hj]
      exact ((hz j).2).symm)
  have huδ₂ : u • (δ₂ : Ω) = δ₁ := hu_eq _ _ (funext fun j => by
    rw [hcδ₁, hcδ₂]
    by_cases hj : j = C.i₁
    · subst hj
      rw [Function.update_self, Function.update_self, Function.update_self, htc']
    · rw [Function.update_of_ne hj, Function.update_of_ne hj, Function.update_of_ne hj]
      exact ((hz j).2).symm)
  have huu : ∀ ω : Ω, u • u • ω = ω := fun ω => by
    rw [← mul_smul, mul_self_eq_one_of_mem_longInv hu.1, one_smul]
  set Λ : Set Ω := {(C.γ : Ω), (δ₁ : Ω), (δ₂ : Ω)} with hΛ
  have huΛ' : ∀ ω ∈ Λ, u • ω ∈ Λ := by
    rintro ω (rfl | rfl | rfl)
    · rw [huγ]; exact Or.inl rfl
    · rw [huδ₁]; exact Or.inr (Or.inr rfl)
    · rw [huδ₂]; exact Or.inr (Or.inl rfl)
  have huΛ : u ∈ stabilizer G Λ := mem_stabilizer_set.mpr fun ω =>
    ⟨fun h => by rw [← huu ω]; exact huΛ' _ h, huΛ' ω⟩
  have hΛW : Λ ⊆ fixSet Ω W := by
    rintro ω (rfl | rfl | rfl)
    exacts [hγW, hδ₁W, hδ₂W]
  obtain ⟨cx, hcx, hcxW, hcxΛ⟩ := hS.exists_mem_longInvSwap_centralizer_eqOn hαβ hW hWαβ
    ⟨C.γ, Or.inl rfl⟩ hΛW hu huΛ
  have hcxγ : cx • (C.γ : Ω) = C.γ := (hcxΛ _ (Or.inl rfl)).trans huγ
  have hcxδ₁ : cx • (δ₁ : Ω) = δ₂ := (hcxΛ _ (Or.inr (Or.inl rfl))).trans huδ₁
  have hcxδ₂ : cx • (δ₂ : Ω) = δ₁ := (hcxΛ _ (Or.inr (Or.inr rfl))).trans huδ₂
  have hcxα : cx • α = β := hcx.2
  have hcxβ : cx • β = α := by rw [← hcxα, ← mul_smul, mul_self_eq_one_of_mem_longInv hcx.1,
    one_smul]
  have hCX : Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (X : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right)
  have hCV : Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left)
  have hcxX : cx ∈ Subgroup.centralizer (X : Set G) := hCX hcxW
  have hcxV : cx ∈ Subgroup.centralizer (V : Set G) := hCV hcxW
  obtain ⟨DX, k, hι, hAX, -, hinj⟩ := C.exists_holtData_lineKer hS hαβ hP hr
  have hXF : ∀ ω ∈ C.line, ω ∈ fixSet Ω X := fun ω hω x hx => hXfix ω hω x hx
  have hαX : α ∈ fixSet Ω X := fun x hx => mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (hXαβ hx)).1
  have hβX : β ∈ fixSet Ω X := fun x hx => mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (hXαβ hx)).2
  set aX : fixSet Ω X := ⟨α, hαX⟩
  set bX : fixSet Ω X := ⟨β, hβX⟩
  set gX : fixSet Ω X := ⟨C.γ, hXF _ C.γ_mem_line⟩
  set d₁X : fixSet Ω X := ⟨δ₁, hXF _ (C.linePoint_mem c₁)⟩
  set d₂X : fixSet Ω X := ⟨δ₂, hXF _ (C.linePoint_mem c₂)⟩
  have hab : aX ≠ bX := fun h => hαβ (congrArg Subtype.val h)
  have h3X := hS.three_le_card_fixSet_of_ne hX hab
  have hK := hS.star_centralizerImage hX h3X
  set ρ := DX.extRho hι
  have hcne : ∀ x y : fixSet Ω X, ((x : Ω) = α ∨ (x : Ω) = β ∨ (x : Ω) ∈ C.line) →
      ((y : Ω) = α ∨ (y : Ω) = β ∨ (y : Ω) ∈ C.line) → (x : Ω) ≠ y →
        DX.coord x k ≠ DX.coord y k := fun x y hx hy hxy h =>
    hxy (congrArg Subtype.val (hinj x y hx hy h))
  have hLα : (α : Ω) = α ∨ (α : Ω) = β ∨ (α : Ω) ∈ C.line := Or.inl rfl
  have hLβ : (β : Ω) = α ∨ (β : Ω) = β ∨ (β : Ω) ∈ C.line := Or.inr (Or.inl rfl)
  have hLγ : (C.γ : Ω) = α ∨ (C.γ : Ω) = β ∨ (C.γ : Ω) ∈ C.line :=
    Or.inr (Or.inr C.γ_mem_line)
  have hLδ₁ : (δ₁ : Ω) = α ∨ (δ₁ : Ω) = β ∨ (δ₁ : Ω) ∈ C.line :=
    Or.inr (Or.inr (C.linePoint_mem c₁))
  have hLδ₂ : (δ₂ : Ω) = α ∨ (δ₂ : Ω) = β ∨ (δ₂ : Ω) ∈ C.line :=
    Or.inr (Or.inr (C.linePoint_mem c₂))
  have hab' := hcne aX bX hLα hLβ hαβ
  have had₂ := hcne aX d₂X hLα hLδ₂ (hαΔ δ₂).symm
  have had₁ := hcne aX d₁X hLα hLδ₁ (hαΔ δ₁).symm
  have hbd₁ := hcne bX d₁X hLβ hLδ₁ (hβΔ δ₁).symm
  have hbd₂ := hcne bX d₂X hLβ hLδ₂ (hβΔ δ₂).symm
  have hd₁d₂ := hcne d₁X d₂X hLδ₁ hLδ₂ hδ₁δ₂
  set u₁ : centralizerImage Ω X := centralizerImageElt (Ω := Ω) hcxX
  have hu₁ : u₁ ∈ longInvAt (centralizerImage Ω X) (fixSet Ω X) gX :=
    ⟨(hS.mem_longInv_centralizerImage_iff hX h3X u₁).mpr ⟨cx, hcx.1, hcxX, fun ω => rfl⟩,
      Subtype.ext hcxγ⟩
  have hρu₁ : ρ u₁ ∈ longInvAt (Equiv.Perm (DX.Ψc k)) (DX.Ψc k) (DX.coord gX k) := by
    rw [DX.extRho_eq_rho hι ⟨u₁, mem_jHull_of_mem_longInv hu₁.1⟩]
    exact DX.rho_mem_longInvAt hu₁ k
  have hu₁a : ρ u₁ (DX.coord aX k) = DX.coord bX k := by
    rw [DX.extRho_coord hι]
    exact congrArg (DX.coord · k) (Subtype.ext hcxα : u₁ • aX = bX)
  have hu₁d : ρ u₁ (DX.coord d₁X k) = DX.coord d₂X k := by
    rw [DX.extRho_coord hι]
    exact congrArg (DX.coord · k) (Subtype.ext hcxδ₁ : u₁ • d₁X = d₂X)
  obtain ⟨hyJ, hya', hxy, hxyc, hcommπ⟩ := mul_swap_mul_swap_mem_longInvAt hρu₁ hab' had₁ had₂
    hbd₁ hbd₂ hd₁d₂ hu₁a hu₁d
  set yb := ρ u₁ * Equiv.swap (DX.coord aX k) (DX.coord d₂X k) *
    Equiv.swap (DX.coord bX k) (DX.coord d₁X k) with hybdef
  have hAle : alternatingGroup (DX.Ψc k) ≤ (DX.ρ k).range := by
    rw [← hAX]
    exact Subgroup.map_le_range _ _
  have hyR : yb ∈ (DX.ρ k).range := longInv_perm_subset_of_alternatingGroup_le hAle
    ⟨DX.tHull, rfl⟩ (DX.rho_mem_longInv DX.t_mem k) hyJ.1
  set y' : ∀ i, Equiv.Perm (DX.Ψc i) := Function.update (fun _ => 1) k yb with hy'
  obtain ⟨u₂, hu₂, hρu₂⟩ := DX.exists_mem_longInvSwap_rho_eq (α := aX) (β := d₁X) y'
    (fun i => by
      by_cases hi : i = k
      · subst hi; rw [hy', Function.update_self]; exact hyR
      · exact absurd (hι i) hi)
    (fun i => by
      by_cases hi : i = k
      · subst hi; rw [hy', Function.update_self]; exact hyJ.1
      · exact absurd (hι i) hi)
    (fun i => by
      by_cases hi : i = k
      · subst hi; rw [hy', Function.update_self]; exact hya'
      · exact absurd (hι i) hi)
  have hρu₂' : ρ u₂ = yb := by
    rw [DX.extRho_eq_rho hι u₂, hρu₂ k, hy', Function.update_self]
  let fX : Subgroup.centralizer (X : Set G) →* centralizerImage Ω X :=
    (MulAction.toPermHom (Subgroup.centralizer (X : Set G)) (fixSet Ω X)).rangeRestrict
  set Z : Subgroup (centralizerImage Ω X) :=
    (V.subgroupOf (Subgroup.centralizer (X : Set G))).map fX with hZdef
  have hV2 : IsPGroup 2 V := C.sylow.2.1.to_le (hVQ.trans (inf_le_left.trans inf_le_left))
  have hZ : IsPGroup 2 Z :=
    (hV2.comap_of_injective _ (Subgroup.centralizer (X : Set G)).subtype_injective).map fX
  have hZsmul : ∀ z ∈ Z, ∃ v ∈ V, ∀ ω : fixSet Ω X, ((z • ω : fixSet Ω X) : Ω) = v • (ω : Ω) := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, hv, fun ω => rfl⟩
  have hZcomm : ∀ z ∈ Z, z * u₁ = u₁ * z := by
    intro z hz
    obtain ⟨v, hv, hvω⟩ := hZsmul z hz
    refine Subtype.ext (Equiv.ext fun ω => Subtype.ext ?_)
    change ((z • u₁ • ω : fixSet Ω X) : Ω) = ((u₁ • z • ω : fixSet Ω X) : Ω)
    rw [hvω]
    change v • cx • (ω : Ω) = cx • ((z • ω : fixSet Ω X) : Ω)
    rw [hvω, ← mul_smul, ← mul_smul, (Subgroup.mem_centralizer_iff.mp hcxV v hv)]
  have hZfix : ∀ z ∈ Z, ∀ ω : fixSet Ω X, (∀ v ∈ V, v • (ω : Ω) = ω) → z • ω = ω := by
    intro z hz ω hω
    obtain ⟨v, hv, hvω⟩ := hZsmul z hz
    exact Subtype.ext ((hvω ω).trans (hω v hv))
  have hρZ : ∀ z ∈ Z, ∀ ω : fixSet Ω X, (∀ v ∈ V, v • (ω : Ω) = ω) →
      ρ z (DX.coord ω k) = DX.coord ω k := fun z hz ω hω => by
    rw [DX.extRho_coord hι, hZfix z hz ω hω]
  obtain ⟨x₁, x₂, hx₁, hx₂, hx₁₂, hx₁Z, hx₂Z, hρx₁, hρx₂⟩ := DX.exists_commute_lifts hι hK hZ
    hu₁.1 hu₂.1 (by rw [hρu₂']; exact hxy)
    (fun z hz => by rw [← map_mul, ← map_mul, hZcomm z hz])
    (fun z hz => by
      rw [hρu₂']
      exact hcommπ (ρ z) (hρZ z hz aX hVα) (hρZ z hz bX hVβ) (hρZ z hz d₁X hVδ₁)
        (hρZ z hz d₂X hVδ₂) (by rw [← map_mul, ← map_mul, hZcomm z hz]))
    (fun z hz => hZfix z hz gX hVγ) (by rw [hρu₂']; exact hyJ.2)
  set Γ : Set Ω := fixSet Ω V ∩ fixSet Ω X with hΓ
  have hγΓ : (C.γ : Ω) ∈ Γ := ⟨fun v hv => hVγ v hv, hXF _ C.γ_mem_line⟩
  have hδ₁Γ : (δ₁ : Ω) ∈ Γ := ⟨fun v hv => hVδ₁ v hv, hXF _ (C.linePoint_mem c₁)⟩
  have h3Γ : 3 ≤ Nat.card Γ := by
    rw [Nat.card_coe_set_eq, ← C.ncard_triple hαβ]
    refine Set.ncard_le_ncard ?_ (Set.toFinite Γ)
    rintro ω (rfl | rfl | rfl)
    exacts [⟨fun v hv => hVα v hv, hαX⟩, ⟨fun v hv => hVβ v hv, hβX⟩, hγΓ]
  have hWΓ : W ≤ fixingSubgroup G Γ := sup_le
    (fun v hv => (mem_fixingSubgroup_iff G).mpr fun ω hω => hω.1 v hv)
    (fun x hx => (mem_fixingSubgroup_iff G).mpr fun ω hω => hω.2 x hx)
  have hlift : ∀ x : centralizerImage Ω X, x ∈ longInvAt (centralizerImage Ω X) (fixSet Ω X) gX →
      x ∈ Subgroup.centralizer (Z : Set (centralizerImage Ω X)) →
        ∃ e ∈ longInvAt G Ω C.γ, e ∈ Subgroup.centralizer (W : Set G) ∧
          ∀ ω (hω : ω ∈ Γ), e • ω = ((x : Equiv.Perm (fixSet Ω X)) ⟨ω, hω.2⟩ : Ω) := by
    intro x hx hxZ
    obtain ⟨e', he'J, he'X, he'π⟩ := (hS.mem_longInv_centralizerImage_iff hX h3X x).mp hx.1
    have hΓ' : ∀ ω (hω : ω ∈ Γ), e' • ω ∈ Γ := by
      intro ω hω
      refine ⟨fun v hv => ?_, by
        rw [← he'π ⟨ω, hω.2⟩]
        exact ((x : Equiv.Perm (fixSet Ω X)) ⟨ω, hω.2⟩).2⟩
      have hzc := (Subgroup.mem_centralizer_iff.mp hxZ) (fX ⟨v, hVX hv⟩) ⟨⟨v, hVX hv⟩, hv, rfl⟩
      have h1 := congrArg (fun π : centralizerImage Ω X =>
        ((π : Equiv.Perm (fixSet Ω X)) ⟨ω, hω.2⟩ : Ω)) hzc
      have h2 : (fX ⟨v, hVX hv⟩ : Equiv.Perm (fixSet Ω X)) ⟨ω, hω.2⟩ = ⟨ω, hω.2⟩ :=
        Subtype.ext (hω.1 v hv)
      simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply, h2] at h1
      rw [← he'π ⟨ω, hω.2⟩]
      exact h1
    have he'Γ : e' ∈ stabilizer G Γ := mem_stabilizer_set.mpr fun ω =>
      ⟨fun h => by
        have h' := hΓ' _ h
        rwa [← mul_smul, mul_self_eq_one_of_mem_longInv he'J, one_smul] at h',
        hΓ' ω⟩
    obtain ⟨e, heJ, heW, heΓ⟩ := hS.frattini h3Γ hW hWΓ he'J he'Γ
    refine ⟨e, ⟨heJ, ?_⟩, heW, fun ω hω => (heΓ ω hω).trans (he'π ⟨ω, hω.2⟩).symm⟩
    rw [heΓ _ hγΓ, ← he'π gX]
    exact congrArg Subtype.val hx.2
  obtain ⟨e₁, he₁, he₁W, he₁Γ⟩ := hlift x₁ hx₁ hx₁Z
  obtain ⟨e₂, he₂, he₂W, he₂Γ⟩ := hlift x₂ hx₂ hx₂Z
  have hstab : ∀ e ∈ Subgroup.centralizer (W : Set G), ∀ ω ∈ Γ, e • ω ∈ Γ := fun e he ω hω =>
    ⟨smul_mem_fixSet_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ (hCV he)) hω.1,
      smul_mem_fixSet_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ (hCX he)) hω.2⟩
  have hcomp : ∀ {e e' : G} {x x' : centralizerImage Ω X}, e' ∈ Subgroup.centralizer (W : Set G) →
      (∀ ω (hω : ω ∈ Γ), e • ω = ((x : Equiv.Perm (fixSet Ω X)) ⟨ω, hω.2⟩ : Ω)) →
      (∀ ω (hω : ω ∈ Γ), e' • ω = ((x' : Equiv.Perm (fixSet Ω X)) ⟨ω, hω.2⟩ : Ω)) →
        ∀ ω (hω : ω ∈ Γ), e • e' • ω =
          (((x * x' : centralizerImage Ω X) : Equiv.Perm (fixSet Ω X)) ⟨ω, hω.2⟩ : Ω) := by
    intro e e' x x' he' hx hx' ω hω
    have h1 := hstab e' he' ω hω
    have h2 : (x' : Equiv.Perm (fixSet Ω X)) ⟨ω, hω.2⟩ = ⟨e' • ω, h1.2⟩ :=
      Subtype.ext (hx' ω hω).symm
    rw [hx (e' • ω) h1, Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply, h2]
  have hγV' : (γV : Ω) ∈ fixSet Ω X := by rw [hγV]; exact hXF _ C.γ_mem_line
  have hγ'V' : (γ'V : Ω) ∈ fixSet Ω X := by rw [hγ'V]; exact hXF _ (C.linePoint_mem c₁)
  refine notMem_orbit_jOddCore_of_separation hXV hX hγV' hγ'V' (by rw [hγV]; exact he₁)
    (by rw [hγV]; exact he₂) (hCV he₁W) (hCV he₂W) (hCX he₁W) (hCX he₂W) ?_ ?_
  · intro ω hωX hωV
    rw [hcomp he₂W he₁Γ he₂Γ ω ⟨hωV, hωX⟩, hcomp he₁W he₂Γ he₁Γ ω ⟨hωV, hωX⟩, hx₁₂]
  · rw [hγ'V, hcomp he₂W he₁Γ he₂Γ _ hδ₁Γ]
    intro h
    have h1 : (x₁ * x₂ : centralizerImage Ω X) • d₁X = d₁X := Subtype.ext h
    have h2 := DX.extRho_coord hι (x₁ * x₂) d₁X
    rw [h1, map_mul, hρx₁, hρx₂, hρu₂', hxyc] at h2
    exact hbd₁ h2

end AltConfig

end CFSG.Holt.H78
