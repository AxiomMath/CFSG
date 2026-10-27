module

public import CFSG.GroupTheory.SubnormalFamilyMaximalOvergroup

public section

namespace CFSG.GroupTheory

open Subgroup

universe u

variable {G : Type u} [Group G]

theorem isSubnormal_subgroupOf_subgroupOf_iff {B L K : Subgroup G} (hLK : L ≤ K) :
    ((B.subgroupOf K).subgroupOf (L.subgroupOf K)).IsSubnormal ↔
      (B.subgroupOf L).IsSubnormal := by
  let e : L.subgroupOf K ≃* L := Subgroup.subgroupOfEquivOfLe hLK
  constructor
  · intro h
    have h' := h.comap e.symm.toMonoidHom
    convert h' using 1
    ext z
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    rfl
  · intro h
    have h' := h.comap e.toMonoidHom
    convert h' using 1
    ext z
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    rfl

theorem isSubnormal_subgroupOf_of_le {B L K : Subgroup G} (hLK : L ≤ K)
    (h : (B.subgroupOf K).IsSubnormal) : (B.subgroupOf L).IsSubnormal :=
  (isSubnormal_subgroupOf_subgroupOf_iff (B := B) hLK).mp (h.subgroupOf)

theorem isSubnormal_subgroupOf_trans {B L K : Subgroup G} (hBL : B ≤ L) (hLK : L ≤ K)
    (hB : (B.subgroupOf L).IsSubnormal) (hL : (L.subgroupOf K).IsSubnormal) :
    (B.subgroupOf K).IsSubnormal :=
  Subgroup.IsSubnormal.trans (fun _ hz => hBL hz)
    ((isSubnormal_subgroupOf_subgroupOf_iff (B := B) hLK).mpr hB) hL

theorem isSubnormal_subgroupOf_conjugate {B K : Subgroup G} (x : G)
    (h : (B.subgroupOf K).IsSubnormal) :
    ((CFSG.conjugate B x).subgroupOf (CFSG.conjugate K x)).IsSubnormal := by
  have hmem : ∀ g : CFSG.conjugate K x, x * (g : G) * x⁻¹ ∈ K := by
    rintro ⟨g, k, hk, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hk
  let ψ : CFSG.conjugate K x →* K :=
    ((MulAut.conj x).toMonoidHom.comp (CFSG.conjugate K x).subtype).codRestrict K
      (fun g => by simpa [MulAut.conj_apply] using hmem g)
  have h' := h.comap ψ
  convert h' using 1
  ext g
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  change (g : G) ∈ CFSG.conjugate B x ↔ x * (g : G) * x⁻¹ ∈ B
  constructor
  · rintro ⟨b, hb, hbg⟩
    rw [← hbg]
    simpa [MulAut.conj_apply, mul_assoc] using hb
  · intro hg
    refine ⟨x * (g : G) * x⁻¹, hg, ?_⟩
    simp [mul_assoc]

theorem conjugate_conjugate (A : Subgroup G) (x y : G) :
    CFSG.conjugate (CFSG.conjugate A x) y = CFSG.conjugate A (x * y) := by
  ext g
  simp only [CFSG.conjugate, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, by group⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨x⁻¹ * a * x⁻¹⁻¹, ⟨a, ha, rfl⟩, by group⟩

theorem conjugate_mono {A B : Subgroup G} (x : G) (h : A ≤ B) :
    CFSG.conjugate A x ≤ CFSG.conjugate B x :=
  Subgroup.map_mono h

theorem conjugate_le_of_mem {B U : Subgroup G} {g : G} (hB : B ≤ U) (hg : g ∈ U) :
    CFSG.conjugate B g ≤ U := by
  rintro _ ⟨b, hb, rfl⟩
  change g⁻¹ * b * g⁻¹⁻¹ ∈ U
  exact U.mul_mem (U.mul_mem (U.inv_mem hg) (hB hb)) (U.inv_mem (U.inv_mem hg))

theorem conjugate_subgroupOf {B U : Subgroup G} (u : U) :
    CFSG.conjugate (B.subgroupOf U) u = (CFSG.conjugate B u).subgroupOf U := by
  ext g
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨(b : G), hb, by simp⟩
  · rintro ⟨b, hb, hbg⟩
    have hgb : (g : G) = (u : G)⁻¹ * b * u := by
      rw [← hbg]
      simp
    refine ⟨u * g * u⁻¹, ?_, ?_⟩
    · change ((u * g * u⁻¹ : U) : G) ∈ B
      have heq : ((u * g * u⁻¹ : U) : G) = b := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hgb]
        group
      rw [heq]
      exact hb
    · apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        inv_inv]
      group

variable [Finite G]

theorem conjugate_pair_subnormality (A : Subgroup G)
    (h : ∀ g : G, (A.subgroupOf (A ⊔ CFSG.conjugate A g)).IsSubnormal) : A.IsSubnormal := by
  classical
  induction hcard : Nat.card G using Nat.strong_induction_on generalizing G with
  | _ N ih =>
  by_contra hA
  have hconjhyp : ∀ x u : G, ((CFSG.conjugate A x).subgroupOf
      (CFSG.conjugate A x ⊔ CFSG.conjugate (CFSG.conjugate A x) u)).IsSubnormal := by
    intro x u
    have h1 := isSubnormal_subgroupOf_conjugate x (h (x * u * x⁻¹))
    have hsup : CFSG.conjugate (A ⊔ CFSG.conjugate A (x * u * x⁻¹)) x =
        CFSG.conjugate A x ⊔ CFSG.conjugate (CFSG.conjugate A x) u := by
      rw [CFSG.conjugate, Subgroup.map_sup]
      congr 1
      change CFSG.conjugate (CFSG.conjugate A (x * u * x⁻¹)) x = _
      rw [conjugate_conjugate, conjugate_conjugate]
      congr 1
      group
    rwa [hsup] at h1
  have hproper : ∀ U : Subgroup G, U ≠ ⊤ → ∀ x : G, CFSG.conjugate A x ≤ U →
      ((CFSG.conjugate A x).subgroupOf U).IsSubnormal := by
    intro U hU x hle
    have hlt : Nat.card U < N := by
      rw [← hcard]
      have h' := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hU)
      rwa [Subgroup.card_top] at h'
    refine ih (Nat.card U) hlt ((CFSG.conjugate A x).subgroupOf U) ?_ rfl
    intro u
    have hBu : CFSG.conjugate (CFSG.conjugate A x) (u : G) ≤ U := conjugate_le_of_mem hle u.2
    have hsupU : (CFSG.conjugate A x).subgroupOf U ⊔
        CFSG.conjugate ((CFSG.conjugate A x).subgroupOf U) u =
        (CFSG.conjugate A x ⊔ CFSG.conjugate (CFSG.conjugate A x) u).subgroupOf U := by
      rw [conjugate_subgroupOf, Subgroup.subgroupOf_sup hle hBu]
    rw [hsupU, isSubnormal_subgroupOf_subgroupOf_iff (sup_le hle hBu)]
    exact hconjhyp x u
  have hAtop : A ≠ ⊤ := fun hA' => hA (hA' ▸ Subgroup.normal_top.isSubnormal)
  have hconj1 : CFSG.conjugate A 1 = A := by
    ext g
    simp [CFSG.conjugate]
  set 𝒰 : Set (Subgroup G) := {U | U ≠ ⊤ ∧ A ≤ U} with h𝒰
  set Sig : Subgroup G → Set (Subgroup G) :=
    fun U => {B | (∃ x : G, B = CFSG.conjugate A x) ∧ B ≤ U} with hSig
  have hmax := subnormal_family_normalizer_unique_maximal_overgroup 𝒰 ⟨A, hAtop, le_rfl⟩ Sig
    (fun U _ B hB => hB.2)
    (fun U hU B hB => by
      obtain ⟨⟨x, rfl⟩, hle⟩ := hB
      exact hproper U hU.1 x hle)
    (fun U _ B hB g hg => by
      obtain ⟨⟨x, rfl⟩, hle⟩ := hB
      exact ⟨⟨x * g, conjugate_conjugate A x g⟩, conjugate_le_of_mem hle hg⟩)
    (fun U _ V _ B hB hBU => ⟨hB.1, hBU⟩)
    (by
      intro U hU V hV
      set L := Subgroup.closure (⋃ B ∈ Sig U ∩ Sig V, (B : Set G)) with hL
      have hAmem : A ∈ Sig U ∩ Sig V :=
        ⟨⟨⟨1, hconj1.symm⟩, hU.2⟩, ⟨⟨1, hconj1.symm⟩, hV.2⟩⟩
      have hAL : A ≤ L := by
        intro a ha
        apply Subgroup.subset_closure
        simp only [Set.mem_iUnion]
        exact ⟨A, hAmem, ha⟩
      have hLU : L ≤ U := by
        rw [hL, Subgroup.closure_le]
        intro g hg
        simp only [Set.mem_iUnion] at hg
        obtain ⟨B, hB, hgB⟩ := hg
        exact hB.1.2 hgB
      refine ⟨Subgroup.normalizer (L : Set G), ⟨?_, le_trans hAL Subgroup.le_normalizer⟩, le_rfl⟩
      intro hNtop
      have hLnormal : L.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
      have hAU : (A.subgroupOf U).IsSubnormal := by
        have := hproper U hU.1 1 (by rw [hconj1]; exact hU.2)
        rwa [hconj1] at this
      have hAL' : (A.subgroupOf L).IsSubnormal := isSubnormal_subgroupOf_of_le hLU hAU
      exact hA (Subgroup.IsSubnormal.trans hAL (hAL') hLnormal.isSubnormal))
  obtain ⟨⟨M, hM𝒰, -, -, hall⟩, -⟩ := hmax
  have hpair : ∀ g : G, CFSG.conjugate A g ≤ M := by
    intro g
    have hne : A ⊔ CFSG.conjugate A g ≠ ⊤ := by
      intro htop
      apply hA
      have h1 := h g
      rw [htop] at h1
      have h2 : (A.subgroupOf ⊤).IsSubnormal → A.IsSubnormal := by
        intro h3
        have h4 := h3.map (f := (⊤ : Subgroup G).subtype) (fun z => ⟨⟨z, trivial⟩, rfl⟩)
        convert h4 using 1
        ext z
        simp
      exact h2 h1
    exact le_trans le_sup_right (hall _ ⟨hne, le_sup_left⟩)
  set K := Subgroup.normalClosure (A : Set G) with hK
  have hKM : K ≤ M := by
    rw [hK, Subgroup.normalClosure, Subgroup.closure_le]
    intro c hc
    obtain ⟨a, ha, hac⟩ := Group.mem_conjugatesOfSet_iff.mp hc
    obtain ⟨g, rfl⟩ := isConj_iff.mp hac
    apply hpair g⁻¹
    refine ⟨a, ha, ?_⟩
    simp [MulAut.conj_apply]
  have hAK : A ≤ K := Subgroup.subset_normalClosure
  have hAM : (A.subgroupOf M).IsSubnormal := by
    have := hproper M hM𝒰.1 1 (by rw [hconj1]; exact hM𝒰.2)
    rwa [hconj1] at this
  have hAK' : (A.subgroupOf K).IsSubnormal := isSubnormal_subgroupOf_of_le hKM hAM
  exact hA (Subgroup.IsSubnormal.trans hAK hAK' (Subgroup.normalClosure_normal).isSubnormal)

end CFSG.GroupTheory
