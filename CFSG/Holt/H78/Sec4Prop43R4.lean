module

public import CFSG.Holt.H78.Sec4Prop43R3
import CFSG.Holt.H78.Sec4Box
import CFSG.Holt.H78.Sec4Prop43W
public import CFSG.Holt.H78.Sec4Prop43B7

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

namespace AltConfig

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} (C : AltConfig G Ω α β)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_kerC_of_coordwise (s : Finset C.D.ι) :
    ∀ {p : G}, p ∈ C.calP → ∀ τ : ∀ j, Equiv.Perm (C.D.Ψc j),
      (∀ δ δ' : holtDelta G Ω α β, (δ' : Ω) = p • (δ : Ω) →
        ∀ j, C.D.coord δ' j = τ j (C.D.coord δ j)) →
      (∀ j, j ≠ C.i₁ → j ∉ s → τ j = 1) → (∀ j ∈ s, j ≠ C.i₁ ∧ τ j ∈ C.Qimg j) →
        ∃ q : C.kerC C.i₁, (q : G) ∈ C.calP ∧ C.kerCHom C.i₁ q = τ C.i₁ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro p hp τ hτ h1 _
    have hpS := C.mem_stabilizer_pair_of_mem_calP hp
    have hpmem : ∀ δ : holtDelta G Ω α β, p • (δ : Ω) ∈ holtDelta G Ω α β := fun δ =>
      (twoPointElt hpS • δ).2
    have hτγ : τ C.i₁ (C.D.coord C.γ C.i₁) = C.D.coord C.γ C.i₁ := by
      have h := hτ C.γ C.γ (C.smul_γ_of_mem_calP hp).symm C.i₁
      exact h.symm
    have hpK : p ∈ C.kerC C.i₁ := by
      refine ⟨C.calG_le_inf (C.calP_le_calG hp), (mem_fixingSubgroup_iff G).mpr ?_⟩
      rintro _ ⟨δ, rfl, hδ⟩
      have h := hτ δ ⟨_, hpmem δ⟩ rfl
      refine congrArg Subtype.val (C.eq_of_coord_eq (funext fun j => ?_) :
        (⟨_, hpmem δ⟩ : holtDelta G Ω α β) = δ)
      rw [h j]
      by_cases hj : j = C.i₁
      · subst hj
        rw [hδ, hτγ]
      · rw [h1 j hj (Finset.notMem_empty j), Equiv.Perm.one_apply]
    refine ⟨⟨p, hpK⟩, hp, Equiv.ext fun c => ?_⟩
    set δ := C.coordEquiv.symm (Function.update (C.D.coord C.γ) C.i₁ c)
    have hδ : C.D.coord δ C.i₁ = c := by rw [C.coord_coordEquiv_symm, Function.update_self]
    have h2 := C.coord_smul_eq_kerCHom ⟨p, hpK⟩ (δ := δ) (δ' := ⟨_, hpmem δ⟩) rfl
    rw [hτ δ ⟨_, hpmem δ⟩ rfl C.i₁, hδ] at h2
    exact h2.symm
  | insert j₀ s hj₀ ih =>
    intro p hp τ hτ h1 h2
    obtain ⟨hj₀i, hj₀Q⟩ := h2 j₀ (Finset.mem_insert_self j₀ s)
    obtain ⟨q₀, hq₀P, hq₀⟩ := C.exists_of_mem_Qimg hj₀Q
    have hp' : (q₀ : G)⁻¹ * p ∈ C.calP := C.calP.mul_mem (C.calP.inv_mem hq₀P) hp
    refine ih hp' (Function.update τ j₀ 1) (fun δ δ' e j => ?_) (fun j hj hjs => ?_)
      (fun j hjs => ?_) |>.imp fun q hq => ⟨hq.1, by rw [hq.2, Function.update_of_ne
        (Ne.symm hj₀i)]⟩
    · have hpS := C.mem_stabilizer_pair_of_mem_calP hp
      set η : holtDelta G Ω α β := twoPointElt hpS • δ
      have hη : (η : Ω) = p • (δ : Ω) := rfl
      have he' : (δ' : Ω) = ((q₀⁻¹ : C.kerC j₀) : G) • (η : Ω) := by
        rw [e, hη, mul_smul]
        rfl
      by_cases hj : j = j₀
      · subst hj
        rw [Function.update_self, Equiv.Perm.one_apply, C.coord_smul_eq_kerCHom (q₀⁻¹) he',
          hτ δ η hη, map_inv, hq₀, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
      · rw [Function.update_of_ne hj, C.coord_smul_of_mem_kerC (q₀⁻¹).2 he' hj, hτ δ η hη]
    · by_cases hjj : j = j₀
      · subst hjj
        rw [Function.update_self]
      · rw [Function.update_of_ne hjj]
        exact h1 j hj (by simp [hjj, hjs])
    · have hjj : j ≠ j₀ := fun h => hj₀ (h ▸ hjs)
      rw [Function.update_of_ne hjj]
      exact h2 j (Finset.mem_insert_of_mem hjs)

omit [FaithfulSMul G Ω] in
theorem mapsDir_self_of_commute (hS : Sec4Setting G Ω) (hP : fusionIsSylowIn 2 C.calP C.calG)
    {g : G} (hgS : g ∈ stabilizer G ({α, β} : Set Ω)) (hgγ : g • (C.γ : Ω) = C.γ) {j : C.D.ι}
    (hcomm : ∀ q ∈ C.calP ⊓ C.kerC j, g * q = q * g) : C.MapsDir g j j := by
  obtain ⟨σ, hσ⟩ := C.exists_mapsDir hgS
  suffices h : σ j = j by
    have := hσ j
    rwa [h] at this
  by_contra hm
  have := C.nontrivial_Ψc j
  obtain ⟨c, hc⟩ := exists_ne (C.D.coord C.γ j)
  obtain ⟨u, hu, huc⟩ := C.exists_mem_Qimg_apply_ne hS hP hc
  obtain ⟨q, hqP, rfl⟩ := C.exists_of_mem_Qimg hu
  set δ := C.coordEquiv.symm (Function.update (C.D.coord C.γ) j c) with hδ
  have hcδ : C.D.coord δ = Function.update (C.D.coord C.γ) j c := C.coord_coordEquiv_symm _
  have hqδ : (q : G) • (δ : Ω) ≠ δ := C.smul_ne_of_kerCHom_ne q (by
    rw [hcδ, Function.update_self]
    exact huc)
  set η : holtDelta G Ω α β := twoPointElt (inv_mem hgS) • δ
  have hgγ' : g⁻¹ • (C.γ : Ω) = C.γ := by rw [inv_smul_eq_iff, hgγ]
  have hη : C.D.coord η j = C.D.coord C.γ j := by
    have h := MapsDir.inv C (hσ j) δ C.γ η C.γ rfl hgγ'.symm
    exact h.mpr (by rw [hcδ, Function.update_of_ne hm])
  have hqη : (q : G) • (η : Ω) = η := C.smul_eq_of_mem_kerC q.2 hη
  apply hqδ
  have hδη : (δ : Ω) = g • (η : Ω) := by
    change (δ : Ω) = g • g⁻¹ • (δ : Ω)
    rw [smul_inv_smul]
  rw [hδη, ← mul_smul, ← hcomm q ⟨hqP, q.2⟩, mul_smul, hqη]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_calG_of_smul_mem_line {g : G} (hgαβ : g ∈ stabilizer G α ⊓ stabilizer G β)
    (hgγ : g • (C.γ : Ω) = C.γ) (hgL : ∀ ω ∈ C.line, g • ω ∈ C.line) : g ∈ C.calG := by
  have hgS := stabilizer_inf_le_stabilizer_pair α β hgαβ
  obtain ⟨σ, hσ⟩ := C.exists_mapsDir hgS
  have hσ₁ : σ C.i₁ = C.i₁ := by
    by_contra hk
    have := C.nontrivial_Ψc C.i₁
    obtain ⟨c, hc⟩ := exists_ne (C.D.coord C.γ C.i₁)
    set δ := C.coordEquiv.symm (Function.update (C.D.coord C.γ) C.i₁ c)
    have hcδ : C.D.coord δ = Function.update (C.D.coord C.γ) C.i₁ c :=
      C.coord_coordEquiv_symm _
    set η : holtDelta G Ω α β := twoPointElt hgS • δ
    have hηL : (η : Ω) ∈ C.line := hgL _ (C.linePoint_mem c)
    have h := (hσ C.i₁ δ C.γ η C.γ rfl hgγ.symm).mp ((C.mem_line_iff η).mp hηL _ hk)
    rw [hcδ, Function.update_self] at h
    exact hc h
  have h1 := hσ C.i₁
  rw [hσ₁] at h1
  exact ⟨⟨hgαβ, hgγ⟩, C.mem_twoPointNormalizer_of_mapsDir hgS h1⟩

theorem not_Qimg_le_alternatingGroup_of_five (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hT : Odd (Nat.card (twoPointKernel G Ω α β))) (hP : fusionIsSylowIn 2 C.calP C.calG)
    (hr : ∃ j, j ≠ C.i₁) (hcard : Fintype.card (C.D.Ψc C.i₁) = 5)
    (h5 : ∀ j, j ≠ C.i₁ → Fintype.card (C.D.Ψc j) = 5) :
    ¬ C.Qimg C.i₁ ≤ alternatingGroup (C.D.Ψc C.i₁) := by
  intro heven
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := C.lineKer with hXdef
  obtain ⟨DX, k, hι, hAX, hcardX, hinj⟩ := C.exists_holtData_lineKer hS hαβ hP hr
  rw [hcard] at hcardX
  have hX := C.isPGroup_lineKer
  have hXαβ := C.lineKer_le_inf
  have hXF : ∀ ω ∈ C.line, ω ∈ fixSet Ω X := fun ω hω x hx =>
    (mem_fixingSubgroup_iff G).mp hx.2 ω hω
  have hαX : α ∈ fixSet Ω X := fun x hx => mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (hXαβ hx)).1
  have hβX : β ∈ fixSet Ω X := fun x hx => mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (hXαβ hx)).2
  set aX : fixSet Ω X := ⟨α, hαX⟩
  set bX : fixSet Ω X := ⟨β, hβX⟩
  set gX : fixSet Ω X := ⟨C.γ, hXF _ C.γ_mem_line⟩
  have hab : aX ≠ bX := fun h => hαβ (congrArg Subtype.val h)
  have h3X := hS.three_le_card_fixSet_of_ne hX hab
  set ρ := DX.extRho hι
  set Φ₀ : Set (fixSet Ω X) := {x | (x : Ω) = α ∨ (x : Ω) = β ∨ (x : Ω) ∈ C.line} with hΦ₀
  have hαL : α ∉ C.line := fun h => left_notMem_holtDelta (G := G) hαβ (C.line_subset_holtDelta h)
  have hβL : β ∉ C.line := fun h => right_notMem_holtDelta (G := G) hαβ (C.line_subset_holtDelta h)
  have hΦ₀card : Φ₀.ncard = 7 := by
    have h1 : Subtype.val '' Φ₀ = insert α (insert β C.line) := by
      ext ω
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases hx with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (rfl | rfl | h)
        · exact ⟨aX, Or.inl rfl, rfl⟩
        · exact ⟨bX, Or.inr (Or.inl rfl), rfl⟩
        · exact ⟨⟨ω, hXF ω h⟩, Or.inr (Or.inr h), rfl⟩
    rw [← Set.ncard_image_of_injective Φ₀ Subtype.val_injective, h1,
      Set.ncard_insert_of_notMem (by rintro (h | h); exacts [hαβ h, hαL h]) (Set.toFinite _),
      Set.ncard_insert_of_notMem hβL (Set.toFinite _), C.ncard_line, hcard]
  have hinjOn : Set.InjOn (fun x : fixSet Ω X => DX.coord x k) Φ₀ := fun x hx y hy h =>
    hinj x y hx hy h
  have hsurj : ∀ c : DX.Ψc k, ∃ x ∈ Φ₀, DX.coord x k = c := by
    have himg : (fun x => DX.coord x k) '' Φ₀ = Set.univ := by
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcardX,
        hinjOn.ncard_image, hΦ₀card]
    intro c
    obtain ⟨x, hx, rfl⟩ := himg.symm ▸ Set.mem_univ c
    exact ⟨x, hx, rfl⟩
  set a := DX.coord aX k
  set b := DX.coord bX k
  set cγ := DX.coord gX k
  have hmore : ∀ S : Set (DX.Ψc k), S.ncard ≤ 4 → ∃ z, z ∉ S := by
    intro S hS
    by_contra h
    push Not at h
    have h1 : (Set.univ : Set (DX.Ψc k)).ncard ≤ S.ncard :=
      Set.ncard_le_ncard (fun z _ => h z) (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcardX] at h1
    omega
  obtain ⟨x, hx⟩ := hmore {a, b, cγ} (by
    have h1 := Set.ncard_insert_le a ({b, cγ} : Set (DX.Ψc k))
    have h2 := Set.ncard_insert_le b ({cγ} : Set (DX.Ψc k))
    rw [Set.ncard_singleton] at h2
    omega)
  obtain ⟨y, hy⟩ := hmore {a, b, cγ, x} (by
    have h1 := Set.ncard_insert_le a ({b, cγ, x} : Set (DX.Ψc k))
    have h2 := Set.ncard_insert_le b ({cγ, x} : Set (DX.Ψc k))
    have h3 := Set.ncard_insert_le cγ ({x} : Set (DX.Ψc k))
    rw [Set.ncard_singleton] at h3
    omega)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx hy
  set π := Equiv.swap x y with hπ
  have hπ2 : π * π = 1 := Equiv.swap_mul_self x y
  have hπ1 : π ≠ 1 := fun h => by
    have h1 := congrArg (fun σ : Equiv.Perm (DX.Ψc k) => σ x) h
    simp only [hπ, Equiv.swap_apply_left, Equiv.Perm.one_apply] at h1
    exact hy.2.2.2 h1
  have hout : IsOuterFactor (DX.M k) := ⟨hAX, by rw [hcardX]⟩
  have htA : DX.ρ k DX.tHull ∉ alternatingGroup (DX.Ψc k) :=
    (notMem_alternatingGroup_iff_of_mem_longInv_perm (DX.rho_mem_longInv DX.t_mem k)).mpr
      (by rw [hcardX])
  have hπR : π ∈ (DX.ρ k).range := by
    have hAle : alternatingGroup (DX.Ψc k) ≤ (DX.ρ k).range := by
      rw [← hAX]
      exact Subgroup.map_le_range _ _
    have h1 : (DX.ρ k DX.tHull)⁻¹ * π ∈ alternatingGroup (DX.Ψc k) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hπ,
        Equiv.Perm.sign_swap (Ne.symm hy.2.2.2)]
      rw [Equiv.Perm.mem_alternatingGroup] at htA
      rcases Int.units_eq_one_or (Equiv.Perm.sign (DX.ρ k DX.tHull)) with h | h
      · exact absurd h htA
      · rw [h]
        decide
    have h2 := (DX.ρ k).range.mul_mem ⟨DX.tHull, rfl⟩ (hAle h1)
    rwa [mul_inv_cancel_left] at h2
  obtain ⟨h, hh⟩ := hπR
  have hker : ∀ k' : jHull (centralizerImage Ω X) (fixSet Ω X), DX.ρ k k' = 1 →
      Odd (orderOf k') := by
    intro k' hk'
    have hK : (k' : centralizerImage Ω X) ∈ jOrbitKernel (centralizerImage Ω X) (fixSet Ω X) :=
      (DX.mem_jOrbitKernel_iff_rho (h := k')).mpr fun i => by rw [hι i]; exact hk'
    rw [DX.ker_outer ⟨k, hout⟩] at hK
    rw [← Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat odd_card_jOddCore (Subgroup.orderOf_dvd_natCard _ hK)
  obtain ⟨û, -, hûρ, hû2⟩ := exists_mem_zpowers_orderOf_eq_two (DX.ρ k) (h := h)
    (by rw [hh]; exact hπ2) (by rw [hh]; exact hπ1) hker
  rw [hh] at hûρ
  have hûu : ((û : centralizerImage Ω X) : Equiv.Perm (fixSet Ω X)) *
      ((û : centralizerImage Ω X) : Equiv.Perm (fixSet Ω X)) = 1 := by
    have h1 : û * û = 1 := by rw [← sq, ← hû2, pow_orderOf_eq_one]
    have h2 := congrArg (fun z : jHull (centralizerImage Ω X) (fixSet Ω X) =>
      ((z : centralizerImage Ω X) : Equiv.Perm (fixSet Ω X))) h1
    simpa using h2
  obtain ⟨g, hgX, hg2, hgû⟩ := exists_isPGroup_zpowers_of_mem_centralizerImage
    (û : centralizerImage Ω X).2 hûu
  have hcoordK' : ∀ y z : fixSet Ω X, DX.coord y = DX.coord z ↔ DX.coord y k = DX.coord z k :=
    fun y z => ⟨fun h => congrFun h k, fun h => funext fun k' => by rw [hι k']; exact h⟩
  have hblock : ∀ n (hn : n ∈ Subgroup.normalizer (X : Set G)) (y z : fixSet Ω X),
      DX.coord y k = DX.coord z k ↔
        DX.coord ((⟨n, hn⟩ : Subgroup.normalizer (X : Set G)) • y) k =
          DX.coord ((⟨n, hn⟩ : Subgroup.normalizer (X : Set G)) • z) k := by
    intro n hn y z
    obtain ⟨σ, hσ⟩ := DX.exists_equiv_coord_eq_iff_of_mem_normalizer
      (toPermHom_mem_normalizer_centralizerImage (Ω := Ω) ⟨n, hn⟩)
    have h := hσ k y z
    rw [hι (σ k)] at h
    exact h
  set Bf : fixSet Ω X → Set Ω := fun y₀ =>
    {ω | ∃ h : ω ∈ fixSet Ω X, DX.coord ⟨ω, h⟩ k = DX.coord y₀ k} with hBf
  have hBstab : ∀ n (hn : n ∈ Subgroup.normalizer (X : Set G)) (y₀ : fixSet Ω X),
      DX.coord ((⟨n, hn⟩ : Subgroup.normalizer (X : Set G)) • y₀) k = DX.coord y₀ k →
        n ∈ stabilizer G (Bf y₀) := by
    intro n hn y₀ hy₀
    rw [mem_stabilizer_set]
    intro ω
    constructor
    · rintro ⟨h, hω⟩
      have hω' : ω ∈ fixSet Ω X := by
        have h' := smul_mem_fixSet_of_mem_normalizer (inv_mem hn) h
        rwa [inv_smul_smul] at h'
      refine ⟨hω', (hblock n hn _ _).mpr ?_⟩
      rw [hy₀]
      exact hω
    · rintro ⟨h, hω⟩
      refine ⟨smul_mem_fixSet_of_mem_normalizer hn h, ?_⟩
      have h' := (hblock n hn _ _).mp hω
      rw [hy₀] at h'
      exact h'
  set 𝔑 := Subgroup.normalizer (X : Set G) ⊓ stabilizer G (Bf aX) ⊓ stabilizer G (Bf bX) ⊓
    stabilizer G (Bf gX) with h𝔑
  have hmem𝔑 : ∀ n (hn : n ∈ Subgroup.normalizer (X : Set G)),
      DX.coord ((⟨n, hn⟩ : Subgroup.normalizer (X : Set G)) • aX) k = a →
      DX.coord ((⟨n, hn⟩ : Subgroup.normalizer (X : Set G)) • bX) k = b →
      DX.coord ((⟨n, hn⟩ : Subgroup.normalizer (X : Set G)) • gX) k = cγ → n ∈ 𝔑 :=
    fun n hn ha' hb' hc' => ⟨⟨⟨hn, hBstab n hn aX ha'⟩, hBstab n hn bX hb'⟩, hBstab n hn gX hc'⟩
  have hPN : C.calP ≤ Subgroup.normalizer (X : Set G) := fun p hp =>
    mem_normalizer_of_forall_conj_mem (fun x hx => C.conj_mem_lineKer hp hx) fun x hx => by
      have h := C.conj_mem_lineKer (C.calP.inv_mem hp) hx
      rwa [inv_inv] at h
  have hP𝔑 : C.calP ≤ 𝔑 := by
    intro p hp
    have hpG := C.calP_le_calG hp
    refine hmem𝔑 p (hPN hp) ?_ ?_ ?_
    · rw [show (⟨p, hPN hp⟩ : Subgroup.normalizer (X : Set G)) • aX = aX from
        Subtype.ext (mem_stabilizer_iff.mp (C.calG_le_inf hpG).1)]
    · rw [show (⟨p, hPN hp⟩ : Subgroup.normalizer (X : Set G)) • bX = bX from
        Subtype.ext (mem_stabilizer_iff.mp (C.calG_le_inf hpG).2)]
    · rw [show (⟨p, hPN hp⟩ : Subgroup.normalizer (X : Set G)) • gX = gX from
        Subtype.ext (C.calG_le_stabilizer_γ hpG)]
  have hP2 : IsPGroup 2 C.calP := C.sylow.2.1.to_le inf_le_left
  obtain ⟨Y, hPY, hY⟩ := exists_fusionIsSylowIn_ge hP2 hP𝔑
  have hFP : fixSet Ω C.calP = {α, β, (C.γ : Ω)} :=
    C.fixSet_eq_of_le hαβ le_rfl (C.calP_le_calG.trans inf_le_left)
  have hYfix : ∀ y₀ : fixSet Ω X, (y₀ : Ω) ∈ ({α, β, (C.γ : Ω)} : Set Ω) →
      (∀ z ∈ ({α, β, (C.γ : Ω)} : Set Ω), ∀ hz : z ∈ fixSet Ω X,
        DX.coord ⟨z, hz⟩ k = DX.coord y₀ k → z = y₀) →
      Y ≤ stabilizer G (Bf y₀) → (y₀ : Ω) ∈ fixSet Ω Y := by
    intro y₀ _ huniq hYB
    have hBorb : Bf y₀ =
        Subtype.val '' orbit (jOddCore (centralizerImage Ω X) (fixSet Ω X)) y₀ := by
      ext ω
      constructor
      · rintro ⟨h, hω⟩
        exact ⟨⟨ω, h⟩, (DX.coord_eq_iff y₀ ⟨ω, h⟩).mp ((hcoordK' _ _).mpr hω.symm), rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, (congrFun ((DX.coord_eq_iff y₀ y).mpr hy) k).symm⟩
    have hBodd : Odd (Nat.card (Bf y₀)) := by
      rw [hBorb, Nat.card_image_of_injective Subtype.val_injective]
      exact odd_card_orbit_jOddCore y₀
    have hFB : Odd (Nat.card ↥(fixSet Ω Y ∩ Bf y₀)) := by
      rw [Nat.odd_iff] at hBodd ⊢
      rw [← card_modEq_card_fixSet_inter_of_le_stabilizer hY.2.1 hYB, hBodd]
    obtain ⟨ω₀, hω₀Y, hω₀X, hω₀⟩ : (fixSet Ω Y ∩ Bf y₀).Nonempty := by
      have h := hFB.pos
      rw [Nat.card_pos_iff] at h
      exact Set.nonempty_coe_sort.mp h.1
    have hω₀P : ω₀ ∈ fixSet Ω C.calP := fun p hp => hω₀Y p (hPY hp)
    rw [hFP] at hω₀P
    rw [← huniq ω₀ hω₀P hω₀X hω₀]
    exact hω₀Y
  have hΦα : ∀ z ∈ ({α, β, (C.γ : Ω)} : Set Ω), ∀ hz : z ∈ fixSet Ω X,
      (⟨z, hz⟩ : fixSet Ω X) ∈ Φ₀ := by
    rintro z (rfl | rfl | rfl) hz
    exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr C.γ_mem_line)]
  have huniq : ∀ y₀ : fixSet Ω X, y₀ ∈ Φ₀ → ∀ z ∈ ({α, β, (C.γ : Ω)} : Set Ω),
      ∀ hz : z ∈ fixSet Ω X, DX.coord ⟨z, hz⟩ k = DX.coord y₀ k → z = y₀ :=
    fun y₀ hy₀ z hz hzX h => congrArg Subtype.val (hinj _ y₀ (hΦα z hz hzX) hy₀ h)
  have hYα : α ∈ fixSet Ω Y := hYfix aX (Or.inl rfl) (huniq aX (Or.inl rfl))
    (hY.1.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
  have hYβ : β ∈ fixSet Ω Y := hYfix bX (Or.inr (Or.inl rfl)) (huniq bX (Or.inr (Or.inl rfl)))
    (hY.1.trans (inf_le_left.trans inf_le_right))
  have hYγ : (C.γ : Ω) ∈ fixSet Ω Y := hYfix gX (Or.inr (Or.inr rfl))
    (huniq gX (Or.inr (Or.inr C.γ_mem_line))) (hY.1.trans inf_le_right)
  set E := 𝔑 ⊓ Subgroup.centralizer (X : Set G) with hE
  have hEN : ∀ h ∈ 𝔑, ∀ n ∈ E, h * n * h⁻¹ ∈ E := by
    intro h hh n hn
    refine ⟨𝔑.mul_mem (𝔑.mul_mem hh hn.1) (𝔑.inv_mem hh), Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro x hx
    have hhN := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hh).1).1).1
    have hx' : h⁻¹ * x * h ∈ X :=
      (Subgroup.mem_normalizer_iff.mp hhN (h⁻¹ * x * h)).mpr (by simpa [mul_assoc] using hx)
    have hc := Subgroup.mem_centralizer_iff.mp hn.2 _ hx'
    calc x * (h * n * h⁻¹) = h * (h⁻¹ * x * h * n) * h⁻¹ := by group
      _ = h * (n * (h⁻¹ * x * h)) * h⁻¹ := by rw [hc]
      _ = h * n * h⁻¹ * x := by group
  have hEX : E ≤ Subgroup.centralizer (X : Set G) := inf_le_right
  let fX : Subgroup.centralizer (X : Set G) →* centralizerImage Ω X :=
    (MulAction.toPermHom (Subgroup.centralizer (X : Set G)) (fixSet Ω X)).rangeRestrict
  let bE : E →* Equiv.Perm (DX.Ψc k) := ρ.comp (fX.comp (Subgroup.inclusion hEX))
  have hbE : ∀ (e : E) (ω : fixSet Ω X), bE e (DX.coord ω k) =
      DX.coord (fX (Subgroup.inclusion hEX e) • ω) k := fun e ω => DX.extRho_coord hι _ ω
  have hfXsmul : ∀ (c : Subgroup.centralizer (X : Set G)) (ω : fixSet Ω X),
      ((fX c • ω : fixSet Ω X) : Ω) = (c : G) • (ω : Ω) := fun _ _ => rfl
  have hgN : g ∈ Subgroup.normalizer (X : Set G) := Subgroup.centralizer_le_normalizer _ hgX
  have hgsmul : ∀ ω : fixSet Ω X, (⟨g, hgN⟩ : Subgroup.normalizer (X : Set G)) • ω =
      (û : centralizerImage Ω X) • ω := fun ω => Subtype.ext (hgû ω).symm
  have hπfix : ∀ z, z ≠ x → z ≠ y → π z = z := fun z h1 h2 =>
    Equiv.swap_apply_of_ne_of_ne h1 h2
  have hgcoord : ∀ ω : fixSet Ω X,
      DX.coord ((⟨g, hgN⟩ : Subgroup.normalizer (X : Set G)) • ω) k = π (DX.coord ω k) :=
    fun ω => by rw [hgsmul, DX.coord_smul û ω k, hûρ]
  have hg𝔑 : g ∈ 𝔑 := hmem𝔑 g hgN
    (by rw [hgcoord]; exact hπfix a (fun h => hx.1 h.symm) fun h => hy.1 h.symm)
    (by rw [hgcoord]; exact hπfix b (fun h => hx.2.1 h.symm) fun h => hy.2.1 h.symm)
    (by rw [hgcoord]; exact hπfix cγ (fun h => hx.2.2 h.symm) fun h => hy.2.2.1 h.symm)
  have hgE : g ∈ E := ⟨hg𝔑, hgX⟩
  have hbEg : bE ⟨g, hgE⟩ = π := by
    have h1 : fX (Subgroup.inclusion hEX ⟨g, hgE⟩) = (û : centralizerImage Ω X) :=
      Subtype.ext (Equiv.ext fun ω => Subtype.ext (hgû ω).symm)
    change ρ (fX (Subgroup.inclusion hEX ⟨g, hgE⟩)) = π
    rw [h1, DX.extRho_eq_rho hι, hûρ]
  have hYE : fusionIsSylowIn 2 (Y ⊓ E) E := fusionIsSylowIn_inf_of_conj_mem' hY inf_le_left hEN
  have hT := fusionIsSylowIn_map bE (fusionIsSylowIn_subgroupOf_top hYE)
  have hπE : π ∈ (⊤ : Subgroup E).map bE := ⟨⟨g, hgE⟩, trivial, hbEg⟩
  have hπ2' : IsPGroup 2 (Subgroup.zpowers π) := by
    have ho : orderOf π = 2 := orderOf_eq_prime (by rw [sq]; exact hπ2) hπ1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho, pow_one])
  obtain ⟨T', hπT', hT'⟩ := exists_fusionIsSylowIn_ge hπ2' (Subgroup.zpowers_le.mpr hπE)
  obtain ⟨c, hc, hcT⟩ := exists_mem_conj_of_fusionIsSylowIn hT hT'
  obtain ⟨e', he'YE, he'c⟩ := (hcT π).mp (hπT' (Subgroup.mem_zpowers π))
  obtain ⟨e₀, -, rfl⟩ := hc
  have hbfix : ∀ (e : E) (y₀ : fixSet Ω X), (∀ n ∈ 𝔑, n ∈ stabilizer G (Bf y₀)) →
      bE e (DX.coord y₀ k) = DX.coord y₀ k := by
    intro e y₀ hy₀
    rw [hbE]
    have h1 : (e : G) • (y₀ : Ω) ∈ Bf y₀ := by
      have h2 := (mem_stabilizer_set.mp (hy₀ e e.2.1) (y₀ : Ω)).mpr ⟨y₀.2, rfl⟩
      exact h2
    obtain ⟨h3, h4⟩ := h1
    exact h4
  have hc_a := hbfix e₀ aX fun n hn => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp
    (Subgroup.mem_inf.mp hn).1).1).2
  have hc_b := hbfix e₀ bX fun n hn => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hn).1).2
  have hc_c := hbfix e₀ gX fun n hn => (Subgroup.mem_inf.mp hn).2
  set cc := bE e₀ with hcc
  have he'swap : bE e' = Equiv.swap (cc⁻¹ x) (cc⁻¹ y) := by
    rw [he'c, Equiv.swap_apply_apply, inv_inv]
  set e : G := (e' : G) with he
  have heYE : e ∈ Y ⊓ E := he'YE
  have heX : e ∈ Subgroup.centralizer (X : Set G) := heYE.2.2
  have heα : e • α = α := hYα e heYE.1
  have heβ : e • β = β := hYβ e heYE.1
  have heγ : e • (C.γ : Ω) = C.γ := hYγ e heYE.1
  have heαβ : e ∈ stabilizer G α ⊓ stabilizer G β := ⟨heα, heβ⟩
  have heΔ : ∀ δ : holtDelta G Ω α β, e • (δ : Ω) ∈ holtDelta G Ω α β := fun δ =>
    (twoPointElt (stabilizer_inf_le_stabilizer_pair α β heαβ) • δ).2
  have heL : ∀ ω ∈ C.line, e • ω ∈ C.line := by
    intro ω hω
    obtain ⟨δ, hδ, rfl⟩ := hω
    refine (C.mem_fixSet_lineKer_iff hS hP ⟨_, heΔ δ⟩).mp ?_
    exact smul_mem_fixSet_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ heX)
      ((C.mem_fixSet_lineKer_iff hS hP δ).mpr ⟨δ, hδ, rfl⟩)
  have heG : e ∈ C.calG := C.mem_calG_of_smul_mem_line heαβ heγ heL
  have heP : e ∈ C.calP := by
    have h := hP.2.2 (Y ⊓ C.calG) inf_le_right (hY.2.1.to_le inf_le_left)
      (le_inf hPY C.calP_le_calG)
    rw [← h]
    exact ⟨heYE.1, heG⟩
  have heS := C.mem_stabilizer_pair_of_mem_calP heP
  have hcommQ : ∀ j, j ≠ C.i₁ → ∀ q ∈ C.calP ⊓ C.kerC j, e * q = q * e := fun j hj q hq =>
    (Subgroup.mem_centralizer_iff.mp heX q (C.kerC_inf_le_lineKer hj hq)).symm
  have hdir : ∀ j, C.MapsDir e j j := by
    intro j
    by_cases hj : j = C.i₁
    · subst hj
      exact C.mapsDir_i₁ (Subgroup.mem_inf.mp heP).2
    · exact C.mapsDir_self_of_commute hS hP heS heγ (hcommQ j hj)
  have hej : ∀ j, e ∈ C.calG ⊓ twoPointNormalizer G Ω α β (C.D.L j) := fun j =>
    ⟨heG, C.mem_twoPointNormalizer_of_mapsDir heS (hdir j)⟩
  set τ : ∀ j, Equiv.Perm (C.D.Ψc j) := fun j => C.normHom j ⟨e, hej j⟩ with hτdef
  have hτ : ∀ δ δ' : holtDelta G Ω α β, (δ' : Ω) = e • (δ : Ω) →
      ∀ j, C.D.coord δ' j = τ j (C.D.coord δ j) := fun δ δ' h j =>
    C.coord_smul_eq_normHom ⟨e, hej j⟩ h
  have hτQ : ∀ j, j ≠ C.i₁ → τ j ∈ C.Qimg j := by
    intro j hj
    have hU := C.fusionIsSylowIn_Qimg_inf hS hP j
    rw [← fixingSubgroup_singleton_perm] at hU
    have h4 : 4 ∣ Nat.card ↥(({C.D.coord C.γ j} : Set (C.D.Ψc j))ᶜ) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_compl_set]
      simp [h5 j hj]
    have hτγ : τ j ∈ fixingSubgroup (Equiv.Perm (C.D.Ψc j)) {C.D.coord C.γ j} := by
      rw [fixingSubgroup_singleton_perm, mem_stabilizer_iff]
      exact (hτ C.γ C.γ heγ.symm j).symm
    refine (Subgroup.mem_inf.mp
      (mem_of_commute_of_fusionIsSylowIn_alternatingGroup_inf_fixingSubgroup h4 hU hτγ
        fun v hv => ?_)).1
    obtain ⟨q, hqP, rfl⟩ := C.exists_of_mem_Qimg (Subgroup.mem_inf.mp hv).1
    have hc : (⟨e, hej j⟩ : ↥(C.calG ⊓ twoPointNormalizer G Ω α β (C.D.L j))) *
        ⟨q, C.kerC_le_calG_inf j q.2⟩ = ⟨q, C.kerC_le_calG_inf j q.2⟩ * ⟨e, hej j⟩ :=
      Subtype.ext (hcommQ j hj q ⟨hqP, q.2⟩)
    have h := congrArg (C.normHom j) hc
    rw [map_mul, map_mul, ← C.kerCHom_eq_normHom] at h
    exact h
  set L : C.D.Ψc C.i₁ → holtDelta G Ω α β := fun c =>
    C.coordEquiv.symm (Function.update (C.D.coord C.γ) C.i₁ c) with hL
  have hLc : ∀ c, C.D.coord (L c) C.i₁ = c := fun c => by
    rw [hL, C.coord_coordEquiv_symm, Function.update_self]
  set Lp : C.D.Ψc C.i₁ → fixSet Ω X := fun c => ⟨(L c : Ω), hXF _ (C.linePoint_mem c)⟩ with hLp
  have hLpΦ : ∀ c, Lp c ∈ Φ₀ := fun c => Or.inr (Or.inr (C.linePoint_mem c))
  set θ : C.D.Ψc C.i₁ → DX.Ψc k := fun c => DX.coord (Lp c) k with hθ
  have hθinj : Function.Injective θ := fun c c' h => by
    have h1 := congrArg Subtype.val (hinj _ _ (hLpΦ c) (hLpΦ c') h)
    rw [← hLc c, ← hLc c', (Subtype.ext h1 : L c = L c')]
  have hLpline : ∀ (ω : fixSet Ω X) (hω : (ω : Ω) ∈ C.line), ω = Lp (C.D.coord
      (⟨ω, C.line_subset_holtDelta hω⟩ : holtDelta G Ω α β) C.i₁) := by
    intro ω hω
    have h1 : (⟨ω, C.line_subset_holtDelta hω⟩ : holtDelta G Ω α β) =
        L (C.D.coord (⟨ω, C.line_subset_holtDelta hω⟩ : holtDelta G Ω α β) C.i₁) := by
      refine C.eq_of_coord_eq (funext fun j => ?_)
      rw [hL, C.coord_coordEquiv_symm]
      by_cases hj : j = C.i₁
      · subst hj
        rw [Function.update_self]
      · rw [Function.update_of_ne hj]
        exact (C.mem_line_iff _).mp hω j hj
    apply Subtype.ext
    exact congrArg (fun δ : holtDelta G Ω α β => (δ : Ω)) h1
  have heLp : ∀ c, fX (Subgroup.inclusion hEX e') • Lp c = Lp (τ C.i₁ c) := by
    intro c
    have hmem : e • ((L c : holtDelta G Ω α β) : Ω) ∈ C.line := heL _ (C.linePoint_mem c)
    have h1 := hLpline (fX (Subgroup.inclusion hEX e') • Lp c) hmem
    rw [h1]
    congr 1
    have h2 := hτ (L c) ⟨_, heΔ (L c)⟩ rfl C.i₁
    rw [hLc] at h2
    exact h2
  have hθτ : ∀ c, θ (τ C.i₁ c) = Equiv.swap (cc⁻¹ x) (cc⁻¹ y) (θ c) := by
    intro c
    change DX.coord (Lp (τ C.i₁ c)) k = _
    rw [← heLp c, ← hbE, he'swap]
  have hrange : ∀ z, z ≠ a → z ≠ b → ∃ c, θ c = z := by
    intro z hza hzb
    obtain ⟨φ, hφ, hφz⟩ := hsurj z
    rcases hφ with h | h | h
    · exact absurd (by rw [← hφz, show φ = aX from Subtype.ext h]) hza
    · exact absurd (by rw [← hφz, show φ = bX from Subtype.ext h]) hzb
    · refine ⟨C.D.coord (⟨φ, C.line_subset_holtDelta h⟩ : holtDelta G Ω α β) C.i₁, ?_⟩
      change DX.coord (Lp _) k = z
      rw [← hLpline φ h]
      exact hφz
  have hca : cc a = a := hc_a
  have hcb : cc b = b := hc_b
  have hinvapp : ∀ z, cc (cc⁻¹ z) = z := fun z => by simp
  have hx'a : cc⁻¹ x ≠ a := fun h => hx.1 (by rw [← hinvapp x, h, hca])
  have hx'b : cc⁻¹ x ≠ b := fun h => hx.2.1 (by rw [← hinvapp x, h, hcb])
  have hy'a : cc⁻¹ y ≠ a := fun h => hy.1 (by rw [← hinvapp y, h, hca])
  have hy'b : cc⁻¹ y ≠ b := fun h => hy.2.1 (by rw [← hinvapp y, h, hcb])
  obtain ⟨c₁, hc₁⟩ := hrange _ hx'a hx'b
  obtain ⟨c₂, hc₂⟩ := hrange _ hy'a hy'b
  have hxy' : cc⁻¹ x ≠ cc⁻¹ y := fun h => hy.2.2.2 (cc⁻¹.injective h).symm
  have hc₁₂ : c₁ ≠ c₂ := fun h => hxy' (by rw [← hc₁, ← hc₂, h])
  have hτswap : τ C.i₁ = Equiv.swap c₁ c₂ := by
    refine Equiv.ext fun c => hθinj ?_
    rw [hθτ]
    by_cases h1 : c = c₁
    · subst h1
      rw [hc₁, Equiv.swap_apply_left, Equiv.swap_apply_left, hc₂]
    by_cases h2 : c = c₂
    · subst h2
      rw [hc₂, Equiv.swap_apply_right, Equiv.swap_apply_right, hc₁]
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne
      (fun h => h1 (hθinj (h.trans hc₁.symm))) fun h => h2 (hθinj (h.trans hc₂.symm))]
  obtain ⟨q, hqP, hq⟩ := C.exists_kerC_of_coordwise (Finset.univ.filter (· ≠ C.i₁)) heP τ hτ
    (fun j hj hjs => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩) hjs)
    (fun j hjs => ⟨(Finset.mem_filter.mp hjs).2, hτQ j (Finset.mem_filter.mp hjs).2⟩)
  have hqA := heven ⟨q, ⟨hqP, q.2⟩, rfl⟩
  rw [hq, hτswap, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap hc₁₂] at hqA
  exact absurd hqA (by decide)

theorem false_of_isRStar (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hT : Odd (Nat.card (twoPointKernel G Ω α β))) (h : C.IsRStar) : False := by
  obtain ⟨hP, hr, -, h5, hcases⟩ := h
  rcases hcases with h1 | ⟨a, ha, hcard, -⟩
  · by_cases heven : C.Qimg C.i₁ ≤ alternatingGroup (C.D.Ψc C.i₁)
    · exact C.not_Qimg_le_alternatingGroup_of_five hS hαβ hT hP hr h1 h5 heven
    · exact C.false_of_rStar_five_of_not_le hS hαβ hT hP hr h1 heven
  · exact C.false_of_rStar_two_pow_add_three hS hαβ hT hP hr ha hcard

theorem false_of_odd_of_two_le (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hT : Odd (Nat.card (twoPointKernel G Ω α β))) (hr : 2 ≤ Fintype.card C.D.ι) : False :=
  C.false_of_odd_of_two_le_of_isRStar hS hαβ hT hr fun C' _ h => C'.false_of_isRStar hS hαβ hT h

end AltConfig

end CFSG.Holt.H78
