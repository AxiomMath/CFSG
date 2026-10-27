module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallQuot
public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallPsu3
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitF5B4Four

public section

namespace CFSG.ComponentClassification.Foote5.HallD8

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.Asc76X DihedralGroup

variable {G : Type} [Group G] {D : Subgroup G} (e : D ≃* DihedralGroup 4)

@[expose] noncomputable def Mq : Subgroup G :=
  ((normalClosure (Dq e : Set (Hz e ⧸ Zq e))).comap (πq e)).map (Hz e).subtype

theorem le_Mq : D ≤ Mq e := fun d hd =>
  ⟨⟨d, le_Hz_of_D e hd⟩, subset_normalClosure ⟨_, mem_subgroupOf.mpr hd, rfl⟩, rfl⟩

theorem conj_mem_Mq {h x : G} (hh : h ∈ Hz e) (hx : x ∈ Mq e) : h⁻¹ * x * h ∈ Mq e := by
  obtain ⟨m, hm, rfl⟩ := hx
  have hm' : πq e m ∈ normalClosure (Dq e : Set (Hz e ⧸ Zq e)) := hm
  refine ⟨⟨h, hh⟩⁻¹ * m * ⟨h, hh⟩, ?_, rfl⟩
  show πq e (⟨h, hh⟩⁻¹ * m * ⟨h, hh⟩) ∈ normalClosure (Dq e : Set (Hz e ⧸ Zq e))
  rw [map_mul, map_mul, map_inv]
  have := (normalClosure_normal (s := (Dq e : Set (Hz e ⧸ Zq e)))).conj_mem _ hm'
    (πq e ⟨h, hh⟩)⁻¹
  rwa [inv_inv] at this

theorem e_symm (x : DihedralGroup 4) : e ⟨(e.symm x : G), (e.symm x).2⟩ = x :=
  e.apply_symm_apply x

theorem rot_ne_one : rot e ≠ 1 := fun h => by
  have h1 := rot_mul_rot e
  rw [h, one_mul] at h1
  exact cen_ne_one e h1.symm

theorem rot_ne_cen : rot e ≠ cen e := fun h => by
  have h1 := rot_mul_rot e
  rw [h, cen_mul_cen] at h1
  exact cen_ne_one e h1.symm

theorem rot_not_mem : rot e ∉ zpowers (cen e) := by
  rw [mem_zpowers_cen_iff]
  rintro (h | h)
  · exact rot_ne_one e h
  · exact rot_ne_cen e h

@[expose] def refl : G := (e.symm (sr 0) : G)

theorem refl_mem : refl e ∈ D := (e.symm (sr 0)).2

theorem refl_not_mem : refl e ∉ zpowers (cen e) := by
  rw [mem_zpowers_cen_iff]
  rintro (h | h)
  · have h1 : e ⟨refl e, refl_mem e⟩ = sr 0 := e_symm e (sr 0)
    have h2 : e ⟨refl e, refl_mem e⟩ = e ⟨1, one_mem D⟩ := by
      congr 1
      exact Subtype.ext h
    rw [h2, e_one] at h1
    exact absurd h1 (by decide)
  · have h1 : e ⟨refl e, refl_mem e⟩ = sr 0 := e_symm e (sr 0)
    have h2 : e ⟨refl e, refl_mem e⟩ = e ⟨cen e, cen_mem e⟩ := by
      congr 1
      exact Subtype.ext h
    rw [h2, e_cen] at h1
    exact absurd h1 (by decide)

theorem inv_rot_mul_refl_not_mem : (rot e)⁻¹ * refl e ∉ zpowers (cen e) := by
  rw [mem_zpowers_cen_iff]
  have hm : (rot e)⁻¹ * refl e ∈ D := mul_mem (inv_mem (rot_mem e)) (refl_mem e)
  have he : e ⟨(rot e)⁻¹ * refl e, hm⟩ = (r 1)⁻¹ * sr 0 := by
    rw [e_mul e (inv_mem (rot_mem e)) (refl_mem e), e_inv e (rot_mem e), e_rot]
    congr 1
    exact e_symm e (sr 0)
  rintro (h | h)
  · have h2 : e ⟨(rot e)⁻¹ * refl e, hm⟩ = e ⟨1, one_mem D⟩ := by
      congr 1
      exact Subtype.ext h
    rw [he, e_one] at h2
    exact absurd h2 (by decide)
  · have h2 : e ⟨(rot e)⁻¹ * refl e, hm⟩ = e ⟨cen e, cen_mem e⟩ := by
      congr 1
      exact Subtype.ext h
    rw [he, e_cen] at h2
    exact absurd h2 (by decide)

variable [Finite G]
  (hcl : ∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
    ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d)

include hcl in
theorem hall_cases
    {T : Subgroup G} (hT : IsSylowOf 2 T ⊤) (hDT : D ≤ T) :
    (∀ x ∈ T ⊓ Mq e, x * x ∈ zpowers (cen e) → x ∈ D) ∨
      (Nat.card ↥(T ⊓ Mq e) = 16 ∧ ∃ y ∈ T ⊓ Mq e, y * y ∈ D ∧ y * y ∉ zpowers (cen e)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH := le_Hz e hcl hT.isPGroup hDT
  have hzT : cen e ∈ T := hDT (cen_mem e)
  set Mb := normalClosure (Dq e : Set (Hz e ⧸ Zq e)) with hMb
  have hTq := isSylowOf_Tq e hcl hT hDT
  have hPb : IsSylowOf 2 (Tq e T ⊓ Mb) Mb :=
    hTq.inf_of_le_normalizer le_top (normalizer_eq_top (H := Mb)).ge
  have hDP : Dq e ≤ Tq e T ⊓ Mb := le_inf (Dq_le_Tq e hDT) subset_normalClosure
  have hmapP : ∀ x (hx : x ∈ T ⊓ Mq e), πq e ⟨x, hTH (mem_inf.mp hx).1⟩ ∈ Tq e T ⊓ Mb := by
    intro x hx
    obtain ⟨hxT, m, hm, hmx⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨⟨_, mem_subgroupOf.mpr hxT, rfl⟩, ?_⟩
    have : m = ⟨x, hTH hxT⟩ := Subtype.ext hmx
    rw [← this]
    exact hm
  rcases hallFusionThm32 (Hz e ⧸ Zq e) (Tq e T) (Dq e) hTq (Dq_le_Tq e hDT) (card_Dq e)
    (FooteLit.F5.isElemAbelian_of_mul_self fun x hx => Dq_sq e hx)
    (rightConjugate_Dq e hcl hT.isPGroup hDT) with h1 | h2 | h3
  ·
    left
    have heq : Tq e T ⊓ Mb = Dq e := h1.eq_of_le hDP inf_le_right hPb.isPGroup
    intro x hx _
    have h := hmapP x hx
    rw [heq] at h
    exact mem_of_πq_mem_Dq e h
  ·
    left
    obtain ⟨e₂⟩ := h2
    intro x hx hx2
    obtain ⟨Q, hQ⟩ := hPb.exists_sylow_eq_subgroupOf
    have hxP := hmapP x hx
    have hxM : πq e ⟨x, hTH (mem_inf.mp hx).1⟩ ∈ Mb := (mem_inf.mp hxP).2
    have hmem : (⟨_, hxM⟩ : Mb) ∈ (Q : Subgroup Mb) := by
      rw [hQ, mem_subgroupOf]
      exact hxP
    have hDQ : (Dq e).subgroupOf Mb ≤ Q := by
      rw [hQ]
      exact subgroupOf_mono _ hDP
    have hD4 : Nat.card ((Dq e).subgroupOf Mb) = 4 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe (hDP.trans inf_le_right)).toEquiv, card_Dq]
    have hDsq : ∀ w ∈ (Dq e).subgroupOf Mb, w * w = 1 := fun w hw =>
      Subtype.ext (Dq_sq e (mem_subgroupOf.mp hw))
    have hsq : (⟨_, hxM⟩ : Mb) * ⟨_, hxM⟩ = 1 := by
      apply Subtype.ext
      change πq e ⟨x, _⟩ * πq e ⟨x, _⟩ = 1
      rw [← map_mul, πq_eq_one_iff]
      exact hx2
    have hres := mem_of_sq_eq_one_of_psu3 e₂ Q hDQ hD4 hDsq hmem hsq
    exact mem_of_πq_mem_Dq e (mem_subgroupOf.mp hres)
  ·
    right
    obtain ⟨eP⟩ := h3 _ hPb
    set Pb := Tq e T ⊓ Mb with hPbdef
    have hPb8 : Nat.card Pb = 8 := by
      rw [Nat.card_congr eP.toEquiv, DihedralGroup.nat_card]
    set yb : Hz e ⧸ Zq e := (eP.symm (r 1) : Hz e ⧸ Zq e) with hyb
    have hybP : yb ∈ Pb := (eP.symm (r 1)).2
    have hyb2 : yb * yb = (eP.symm (r 2) : Hz e ⧸ Zq e) := by
      rw [hyb, ← coe_mul, ← map_mul, r_mul_r]
      rfl
    have hyb1 : yb * yb ≠ 1 := by
      rw [hyb2]
      intro h
      have h' : eP.symm (r 2) = 1 := Subtype.ext h
      rw [MulEquiv.symm_apply_eq, map_one] at h'
      exact absurd h' (by decide)
    have hybD : yb * yb ∈ Dq e := by
      set ab := πq e ⟨rot e, le_Hz_of_D e (rot_mem e)⟩ with hab
      set bb := πq e ⟨refl e, le_Hz_of_D e (refl_mem e)⟩ with hbb
      have habD : ab ∈ Dq e := ⟨_, mem_subgroupOf.mpr (rot_mem e), rfl⟩
      have hbbD : bb ∈ Dq e := ⟨_, mem_subgroupOf.mpr (refl_mem e), rfl⟩
      have habP : ab ∈ Pb := hDP habD
      have hbbP : bb ∈ Pb := hDP hbbD
      have hab1 : ab ≠ 1 := by
        rw [hab, Ne, πq_eq_one_iff]
        exact rot_not_mem e
      have hbb1 : bb ≠ 1 := by
        rw [hbb, Ne, πq_eq_one_iff]
        exact refl_not_mem e
      have habb : ab ≠ bb := by
        rw [hab, hbb, Ne, πq_eq_iff]
        exact inv_rot_mul_refl_not_mem e
      set a' := eP ⟨ab, habP⟩
      set b' := eP ⟨bb, hbbP⟩
      have ha' : a' * a' = 1 := by
        rw [← map_mul, ← map_one eP]
        congr 1
        exact Subtype.ext (Dq_sq e habD)
      have hb' : b' * b' = 1 := by
        rw [← map_mul, ← map_one eP]
        congr 1
        exact Subtype.ext (Dq_sq e hbbD)
      have ha'1 : a' ≠ 1 := fun h => hab1 (by
        rw [← map_one eP] at h
        exact congrArg Subtype.val (eP.injective h))
      have hb'1 : b' ≠ 1 := fun h => hbb1 (by
        rw [← map_one eP] at h
        exact congrArg Subtype.val (eP.injective h))
      have hab' : a' ≠ b' := fun h => habb (congrArg Subtype.val (eP.injective h))
      have habab : (a' * b') * (a' * b') = 1 := by
        rw [← map_mul, ← map_mul, ← map_one eP]
        congr 1
        exact Subtype.ext (Dq_sq e (mul_mem habD hbbD))
      have hr2 : eP.symm (r 2) = ⟨ab, habP⟩ ∨ eP.symm (r 2) = ⟨bb, hbbP⟩ ∨
          eP.symm (r 2) = ⟨ab, habP⟩ * ⟨bb, hbbP⟩ := by
        rcases d8_four a' b' ha' hb' ha'1 hb'1 hab' habab with h | h | h
        · left
          rw [h, MulEquiv.symm_apply_apply]
        · right; left
          rw [h, MulEquiv.symm_apply_apply]
        · right; right
          rw [h, ← map_mul, MulEquiv.symm_apply_apply]
      rw [hyb2]
      rcases hr2 with h | h | h <;> rw [h]
      · exact habD
      · exact hbbD
      · exact mul_mem habD hbbD
    obtain ⟨t, ht, hty⟩ := (mem_inf.mp hybP).1
    have htM : t ∈ Mb.comap (πq e) := by
      rw [mem_comap, hty]
      exact (mem_inf.mp hybP).2
    have htT : (t : G) ∈ T := mem_subgroupOf.mp ht
    have htTM : (t : G) ∈ T ⊓ Mq e := mem_inf.mpr ⟨htT, ⟨t, htM, rfl⟩⟩
    set K₁ := T.subgroupOf (Hz e) ⊓ Mb.comap (πq e) with hK₁
    have hZK : Zq e ≤ K₁ := by
      rw [Zq, zpowers_le]
      refine mem_inf.mpr ⟨mem_subgroupOf.mpr hzT, ?_⟩
      rw [mem_comap, (πq_eq_one_iff e).mpr (mem_zpowers _)]
      exact one_mem _
    have hK₁P : K₁.map (πq e) = Pb := by
      ext p
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact mem_inf.mpr ⟨⟨k, (mem_inf.mp hk).1, rfl⟩, (mem_inf.mp hk).2⟩
      · intro hp
        obtain ⟨k, hk, rfl⟩ := (mem_inf.mp hp).1
        exact ⟨k, mem_inf.mpr ⟨hk, (mem_inf.mp hp).2⟩, rfl⟩
    have hTM : T ⊓ Mq e = K₁.map (Hz e).subtype := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxT, m, hm, rfl⟩ := mem_inf.mp hx
        exact ⟨m, mem_inf.mpr ⟨mem_subgroupOf.mpr hxT, hm⟩, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact mem_inf.mpr ⟨mem_subgroupOf.mp (mem_inf.mp hk).1, ⟨k, (mem_inf.mp hk).2, rfl⟩⟩
    refine ⟨?_, (t : G), htTM, ?_, ?_⟩
    · have h := card_map_πq_mul e hZK
      rw [hK₁P, hPb8] at h
      rw [hTM, card_map_of_injective (Hz e).subtype_injective]
      omega
    · have h : πq e (t * t) ∈ Dq e := by
        rw [map_mul, hty]
        exact hybD
      exact mem_of_πq_mem_Dq e h
    · intro h
      apply hyb1
      rw [← hty, ← map_mul, πq_eq_one_iff]
      exact h

end CFSG.ComponentClassification.Foote5.HallD8
