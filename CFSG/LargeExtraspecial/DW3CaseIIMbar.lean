module

public import CFSG.LargeExtraspecial.DW3CaseI
public import CFSG.LargeExtraspecial.DWCaseIIBAxis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.GroupTheory.GLnTwoSplitting
  CFSG.RankThree.Literature.FSmith

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}
  [IsElementaryAbelian 2 A]

@[expose] noncomputable def stabMbar (S : Setting G) (x : S.Qt) : Subgroup S.Mbar :=
  MulAction.stabilizer S.Mbar x

@[simp]
theorem mem_stabMbar {S : Setting G} {x : S.Qt} {p : S.Mbar} :
    p ∈ stabMbar S x ↔ ((p : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x = x := by
  rw [stabMbar, MulAction.mem_stabilizer_iff]
  rfl

namespace MaxEA

theorem resAt_surjective_of_axisA_eq (hA : MaxEA S A)
    (hM : S.M ≤ normalizer (A : Set G))
    (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A)
    (hD : spanD S = S.clSub A)
    (hsl : ∀ g : G, g * S.z * g⁻¹ ∈ A → g * S.z * g⁻¹ ≠ S.z →
      axisA S A g = ZMod 2 ∙ S.cl (g * S.z * g⁻¹)) :
    Function.Surjective (resAt S A hM) := by
  have : FiniteDimensional (ZMod 2) (S.clSub A) := Module.Finite.of_finite
  rw [← MonoidHom.range_eq_top]
  refine eq_top_of_transvections (resAt S A hM).range
    {v : S.clSub A | ∃ g : G, g * S.z * g⁻¹ ∈ A ∧ g * S.z * g⁻¹ ≠ S.z ∧
      (v : S.Qt) = S.cl (g * S.z * g⁻¹)} ?_ ?_
  · intro U hU
    have hspan : spanD S ≤ U.map (S.clSub A).subtype := by
      rw [spanD, Submodule.span_le]
      rintro w ⟨h, hhQ, rfl⟩
      have hxA : h * S.z * h⁻¹ ∈ A := hII h hhQ
      by_cases hz : h * S.z * h⁻¹ = S.z
      · rw [hz, S.cl_z]
        exact Submodule.zero_mem _
      · exact Submodule.mem_map.mpr
          ⟨⟨S.cl (h * S.z * h⁻¹), S.cl_mem_clSub hxA (hA.le_QG hxA)⟩,
            hU ⟨h, hxA, hz, rfl⟩, rfl⟩
    apply eq_top_iff.mpr
    intro v _
    have hvD : (v : S.Qt) ∈ spanD S := by
      rw [hD]
      exact v.2
    have hv : (v : S.Qt) ∈ U.map (S.clSub A).subtype := hspan hvD
    obtain ⟨w, hwU, hwv⟩ := Submodule.mem_map.mp hv
    have hwv' : w = v := Subtype.ext hwv
    simpa [hwv'] using hwU
  · rintro d ⟨g, hgA, hgz, hgd⟩ f hfd
    have hxgQ : g * S.z * g⁻¹ ∈ S.QG := hA.le_QG hgA
    have hφ : ∀ w : S.clSub A, (w : S.Qt) ∈ axisA S A g → f w = 0 := by
      intro w hw
      rw [hsl g hgA hgz] at hw
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
      have hw' : w = c • d := by
        apply Subtype.ext
        rw [Submodule.coe_smul, hgd]
        exact hc.symm
      rw [hw', map_smul, hfd, smul_zero]
    obtain ⟨t, htAbar, ht⟩ := hA.exists_Abar_eq hM hII hgA hgz f hφ
    let p : S.Mbar := ⟨t, Abar_le_Mbar A g htAbar⟩
    refine ⟨resAt S A hM p, ⟨p, rfl⟩, fun w => ?_⟩
    apply Subtype.ext
    change (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (w : S.Qt) =
      (w : S.Qt) + f w • (d : S.Qt)
    rw [ht w, hgd]

theorem exists_apply_eq_of_surjective (hA : MaxEA S A)
    (hM : S.M ≤ normalizer (A : Set G))
    (hsurj : Function.Surjective (resAt S A hM))
    {u v : S.Qt} (hu : u ∈ S.clSub A) (hv : v ∈ S.clSub A) (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    ∃ p : S.Mbar, ((p : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = v := by
  by_cases huv : u = v
  · exact ⟨1, by rw [huv]; rfl⟩
  let U : S.clSub A := ⟨u, hu⟩
  let V : S.clSub A := ⟨v, hv⟩
  have hU0 : U ≠ 0 := fun h => hu0 (congrArg Subtype.val h)
  have hV0 : V ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have hmem : U ∉ (ZMod 2) ∙ (U + V) := by
    rw [mem_span_singleton_iff_two]
    rintro (h | h)
    · exact hU0 h
    · exact hV0 (by
        have h' : U + 0 = U + V := by rw [add_zero]; exact h
        exact (add_left_cancel h').symm)
  obtain ⟨f, hfker, hfU⟩ :=
    exists_dual_eq_one_of_notMem (S := (ZMod 2) ∙ (U + V)) (w := U) hmem
  have hfsum : f (U + V) = 0 :=
    hfker (U + V) (Submodule.mem_span_singleton_self (U + V))
  let e : S.clSub A ≃ₗ[ZMod 2] S.clSub A := LinearEquiv.transvection hfsum
  have heU : e U = V := by
    rw [transvection_apply, hfU, one_smul, ← add_assoc, two_add_self, zero_add]
  obtain ⟨p, hp⟩ := hsurj e
  refine ⟨p, ?_⟩
  have hres : resAt S A hM p U = V := by
    rw [hp]
    exact heU
  have hcoe : ((resAt S A hM p U : S.clSub A) : S.Qt) = ((V : S.clSub A) : S.Qt) :=
    congrArg Subtype.val hres
  rw [coe_resAt_apply] at hcoe
  simpa [U, V] using hcoe

theorem exists_conj_eq_of_surjective (hA : MaxEA S A)
    (hM : S.M ≤ normalizer (A : Set G))
    (hsurj : Function.Surjective (resAt S A hM))
    {g₀ : G} (hg₀A : g₀ * S.z * g₀⁻¹ ∈ A) (hg₀z : g₀ * S.z * g₀⁻¹ ≠ S.z)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) : ∃ g : G, g * S.z * g⁻¹ = a := by
  by_cases haz : a = S.z
  · exact ⟨1, by rw [haz]; group⟩
  have hxQ : g₀ * S.z * g₀⁻¹ ∈ S.QG := hA.le_QG hg₀A
  have haQ : a ∈ S.QG := hA.le_QG ha
  have hx0 : S.cl (g₀ * S.z * g₀⁻¹) ≠ 0 := fun h =>
    hg₀z ((S.cl_eq_zero_iff hxQ).mp h |>.resolve_left (S.s12_conj_z_ne_one g₀))
  have ha0 : S.cl a ≠ 0 := fun h => by
    rcases (S.cl_eq_zero_iff haQ).mp h with h1 | h1
    · exact ha1 h1
    · exact haz h1
  obtain ⟨p, hp⟩ := exists_apply_eq_of_surjective hA hM hsurj
    (S.cl_mem_clSub hg₀A hxQ) (S.cl_mem_clSub ha haQ) hx0 ha0
  obtain ⟨m, hm⟩ := S.ρM_surjective p
  have hρ : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl (g₀ * S.z * g₀⁻¹)) = S.cl a := by
    rw [← hm] at hp
    simpa [S.coe_ρM m] using hp
  have hcl : S.cl (m * (g₀ * S.z * g₀⁻¹) * m⁻¹) = S.cl a := by
    calc S.cl (m * (g₀ * S.z * g₀⁻¹) * m⁻¹)
        = ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g₀ * S.z * g₀⁻¹)) := by
          simpa using (S.ρ_cl m hxQ).symm
      _ = S.cl a := hρ
  have hyQ : m * (g₀ * S.z * g₀⁻¹) * m⁻¹ ∈ S.QG := S.conj_mem_QG m.2 hxQ
  have hzz : ∀ x : G, x * S.z * S.z = x := by
    intro x
    rw [mul_assoc, S.z_mul_z, mul_one]
  rcases (S.cl_eq_cl_iff hyQ haQ).mp hcl with h | h
  · refine ⟨m * g₀, ?_⟩
    rw [h]
    simp only [Subgroup.coe_inv]
    group
  · have hyt : m * (g₀ * S.z * g₀⁻¹) * m⁻¹ = a * S.z := by
      rw [h]
      exact (hzz _).symm
    have htQ : a * S.z ∈ S.QG := S.QG.mul_mem haQ S.z_mem_QG
    have ht1 : a * S.z ≠ 1 := by
      intro h1
      apply haz
      calc a = a * S.z * S.z := by rw [mul_assoc, S.z_mul_z, mul_one]
        _ = 1 * S.z := by rw [h1]
        _ = S.z := one_mul _
    have htz : a * S.z ≠ S.z := by
      intro h1
      apply ha1
      calc a = a * S.z * S.z := by rw [mul_assoc, S.z_mul_z, mul_one]
        _ = S.z * S.z := by rw [h1]
        _ = 1 := S.z_mul_z
    obtain ⟨u, -, hu⟩ := S.exists_conj_eq_mul_z htQ ht1 htz
    have hut : u * (a * S.z) * u⁻¹ = a := by
      rw [hu, mul_assoc, S.z_mul_z, mul_one]
    refine ⟨u * m * g₀, ?_⟩
    have hconj : (u * m * g₀) * S.z * (u * m * g₀)⁻¹ =
        u * (m * (g₀ * S.z * g₀⁻¹) * m⁻¹) * u⁻¹ := by
      simp only [Subgroup.coe_inv]
      group
    rw [hconj, hyt]
    exact hut

theorem nonempty_Mbar_mulEquiv_of_surjective (hA : MaxEA S A)
    (hM : S.M ≤ normalizer (A : Set G))
    (hsurj : Function.Surjective (resAt S A hM)) :
    Nonempty (S.Mbar ≃* GL (Fin S.width) (ZMod 2)) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_mulEquiv_GL (E := S.clSub A) hA.finrank_clSub
  exact ⟨(MulEquiv.ofBijective (resAt S A hM) ⟨hA.resAt_injective hM, hsurj⟩).trans e⟩

theorem card_stabilizer_eq (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
    (hw : S.width = 3) (hsurj : Function.Surjective (resAt S A hM))
    {x : S.Qt} (hx : x ∈ S.clSub A) (hx0 : x ≠ 0) :
    Nat.card (stabMbar S x) = 24 := by
  classical
  change Nat.card (MulAction.stabilizer S.Mbar x) = 24
  haveI : Fintype (S.clSub A) := Fintype.ofFinite _
  haveI : Fintype {v : S.clSub A // v ≠ 0} := Fintype.ofFinite _
  have hset : (MulAction.orbit S.Mbar x : Set S.Qt) = {v | v ∈ S.clSub A ∧ v ≠ 0} := by
    ext v
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨apply_mem_clSub hM p.2 hx, ?_⟩
      intro h0
      change (((p : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x = 0 at h0
      exact hx0 ((((p : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).map_eq_zero_iff.mp h0)
    · rintro ⟨hvA, hv0⟩
      obtain ⟨p, hp⟩ := exists_apply_eq_of_surjective hA hM hsurj hx hvA hx0 hv0
      exact MulAction.mem_orbit_iff.mpr ⟨p, hp⟩
  have hcardA : Nat.card (S.clSub A) = 8 := by
    rw [S.card_submodule, hA.finrank_clSub, hw]
    norm_num
  have hcardne : Nat.card {v : S.clSub A // v ≠ 0} = 7 := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (fun v : S.clSub A => v = 0),
      Fintype.card_subtype_eq (0 : S.clSub A), ← Nat.card_eq_fintype_card, hcardA]
  have horbit : Nat.card (MulAction.orbit S.Mbar x) = 7 := by
    rw [hset]
    change Nat.card {v : S.Qt // v ∈ S.clSub A ∧ v ≠ 0} = 7
    let e : {v : S.Qt // v ∈ S.clSub A ∧ v ≠ 0} ≃ {v : S.clSub A // v ≠ 0} :=
      { toFun := fun v => ⟨⟨v.1, v.2.1⟩, by simpa using v.2.2⟩
        invFun := fun v => ⟨v.1.1, v.1.2, by simpa using v.2⟩
        left_inv := fun v => by ext <;> rfl
        right_inv := fun v => by ext <;> rfl }
    rw [Nat.card_congr e]
    exact hcardne
  have hcardMbar : Nat.card S.Mbar = 168 := by
    obtain ⟨e⟩ := nonempty_Mbar_mulEquiv_of_surjective hA hM hsurj
    rw [hw] at e
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.H13.L619.card_GL32]
  have hindex : (MulAction.stabilizer S.Mbar x).index = 7 := by
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, horbit]
  have hmul : Nat.card (MulAction.stabilizer S.Mbar x) * 7 = 168 := by
    rw [← hindex, ← hcardMbar]
    exact (MulAction.stabilizer S.Mbar x).card_mul_index
  have h24 : Nat.card (MulAction.stabilizer S.Mbar x) = 24 := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 7)
    rw [hmul]
  exact h24

theorem map_ne_of_noInvariantCompl (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
    (hw : S.width = 3) (hsurj : Function.Surjective (resAt S A hM))
    (hNS : ∀ B : Submodule (ZMod 2) S.Qt, IsMbarInvariant S B → (∀ b ∈ B, S.q b = 0) →
      ¬ IsCompl (S.clSub A) B)
    {t : S.Mbar} (ht1 : t ≠ 1) (ht2 : t * t = 1) {B : Submodule (ZMod 2) S.Qt}
    (hB : B ∈ tsCompl S.q (S.clSub A)) :
    B.map (((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) ≠ B := by
  intro heq
  letI : MulAction S.Mbar (tsCompl S.q (S.clSub A)) := tsComplAction (S := S) (A := A) hM
  let x₀ : tsCompl S.q (S.clSub A) := ⟨B, hB⟩
  have hstab : t ∈ MulAction.stabilizer S.Mbar x₀ := by
    rw [MulAction.mem_stabilizer_iff]
    change (tsComplAction (S := S) (A := A) hM).smul t x₀ = x₀
    apply Subtype.ext
    exact heq
  have h2dvd : 2 ∣ Nat.card (MulAction.stabilizer S.Mbar x₀) := by
    let g : MulAction.stabilizer S.Mbar x₀ := ⟨t, hstab⟩
    have hg : orderOf g = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by simpa [pow_two] using ht2) ht1
    have hdiv : orderOf g ∣ Nat.card (MulAction.stabilizer S.Mbar x₀) :=
      orderOf_dvd_natCard g
    rwa [hg] at hdiv
  obtain ⟨e⟩ := nonempty_Mbar_mulEquiv_of_surjective hA hM hsurj
  rw [hw] at e
  haveI : IsSimpleGroup (GL (Fin 3) (ZMod 2)) :=
    CFSG.Quasithin.H13.L619.isSimpleGroup_GL_zmod_two (by norm_num)
  haveI : IsSimpleGroup S.Mbar := MulEquiv.isSimpleGroup e
  have hcardMbar : Nat.card S.Mbar = 168 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.H13.L619.card_GL32]
  have hXcard : Nat.card (tsCompl S.q (S.clSub A)) = 8 := by
    refine card_tsCompl_eq_eight S.q_nondegenerate hB.1 (fun u hu => q_clSub hu)
      (fun b hb => hB.2 b hb) ?_
    rw [hA.finrank_clSub, hw]
  obtain ⟨W₂, hW₂fix⟩ :=
    CFSG.GroupTheory.exists_fixed_of_card_eq_168 hcardMbar hXcard x₀ h2dvd
  have hinv : IsMbarInvariant S W₂.1 := by
    intro m w hw
    have hsmul : W₂.1.map
        (↑(((S.ρM m : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :
          S.Qt →ₗ[ZMod 2] S.Qt) = W₂.1 :=
      congrArg Subtype.val (hW₂fix (S.ρM m))
    have hmem : (((S.ρM m : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W₂.1 := by
      rw [← hsmul]
      exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩
    simpa [S.coe_ρM m] using hmem
  exact hNS W₂.1 hinv W₂.2.2 W₂.2.1

end MaxEA

end CFSG.LargeExtraspecial.DW
