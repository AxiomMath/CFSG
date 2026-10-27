module

public import CFSG.ClassicalInvolution.Q3.Q3NMClass
public import CFSG.ClassicalInvolution.Q3.Q3NMTwin
public import CFSG.ClassicalInvolution.Q3.Q3OTKlein
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerAbs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3.Q3NM

section Inn

variable {H : Type} [Group H]

@[expose] noncomputable def innL (L : Subgroup H) : ↥L →* ↥(inducedAutOn L) :=
  (toInducedAutOn L).comp (Subgroup.inclusion (Subgroup.le_normalizer (H := L)))

theorem innL_coe (L : Subgroup H) (t : ↥L) :
    ((innL L t : ↥(inducedAutOn L)) : MulAut ↥L) = MulAut.conj t := by
  ext y
  rfl

theorem conj_eq_one_iff_mem_center {X : Type} [Group X] (t : X) :
    MulAut.conj t = 1 ↔ t ∈ Subgroup.center X := by
  constructor
  · intro h
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut X => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * t = (t * g * t⁻¹) * t := by rw [this]
      _ = t * g := by group
  · intro h
    ext g
    have := Subgroup.mem_center_iff.mp h g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    calc t * g * t⁻¹ = g * t * t⁻¹ := by rw [this]
      _ = g := by group

theorem innL_eq_one_iff (L : Subgroup H) (t : ↥L) :
    innL L t = 1 ↔ t ∈ Subgroup.center ↥L := by
  rw [Subtype.ext_iff, innL_coe, Subgroup.coe_one, conj_eq_one_iff_mem_center]

@[expose] noncomputable def innHom (L : Subgroup H) :
    (↥L ⧸ Subgroup.center ↥L) →* ↥(inducedAutOn L) :=
  QuotientGroup.lift (Subgroup.center ↥L) (innL L) fun t ht => (innL_eq_one_iff L t).mpr ht

theorem innHom_mk (L : Subgroup H) (t : ↥L) :
    innHom L (QuotientGroup.mk t) = innL L t := rfl

theorem innHom_injective (L : Subgroup H) : Function.Injective (innHom L) := by
  rw [injective_iff_map_eq_one]
  intro tb h
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective tb
  rw [innHom_mk, innL_eq_one_iff] at h
  exact (QuotientGroup.eq_one_iff t).mpr h

theorem conj_eq_conj_iff_mk {X : Type} [Group X] (u t : X) :
    MulAut.conj u = MulAut.conj t ↔
      (QuotientGroup.mk u : X ⧸ Subgroup.center X) = QuotientGroup.mk t := by
  rw [QuotientGroup.eq]
  constructor
  · intro h
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut X => φ g) h
    simp only [MulAut.conj_apply] at this
    calc g * (u⁻¹ * t) = u⁻¹ * (u * g * u⁻¹) * t := by group
      _ = u⁻¹ * (t * g * t⁻¹) * t := by rw [this]
      _ = (u⁻¹ * t) * g := by group
  · intro h
    ext g
    have h1 := Subgroup.mem_center_iff.mp h g
    simp only [MulAut.conj_apply]
    calc u * g * u⁻¹ = u * (g * (u⁻¹ * t)) * t⁻¹ := by group
      _ = u * ((u⁻¹ * t) * g) * t⁻¹ := by rw [h1]
      _ = t * g * t⁻¹ := by group

theorem mem_fixed_iff_commutes (L : Subgroup H) (a : ↥(inducedAutOn L)) (t : ↥L) :
    (QuotientGroup.mk t : ↥L ⧸ Subgroup.center ↥L) ∈
        fixedSubgroup (autToCentralQuotient ↥L (a : MulAut ↥L)) ↔
      innL L t ∈ Subgroup.centralizer ({a} : Set ↥(inducedAutOn L)) := by
  rw [mem_fixedSubgroup_iff, autToCentralQuotient_mk, Subgroup.mem_centralizer_singleton_iff,
    ← conj_eq_conj_iff_mk, Subtype.ext_iff]
  simp only [Subgroup.coe_mul, innL_coe]
  have h1 : (a : MulAut ↥L) * MulAut.conj t * (a : MulAut ↥L)⁻¹ =
      MulAut.conj ((a : MulAut ↥L) t) := mul_conj_mul_inv _ _
  rw [← h1, mul_inv_eq_iff_eq_mul]
  first | exact Iff.rfl | exact eq_comm

theorem oddCoreIn_centralizer_inf_inn_eq_bot (L : Subgroup H) (a : ↥(inducedAutOn L))
    (h : oddCoreIn (fixedSubgroup (autToCentralQuotient ↥L (a : MulAut ↥L))) = ⊥) :
    oddCoreIn (Subgroup.centralizer ({a} : Set ↥(inducedAutOn L)) ⊓
      (innSubgroup ↥L).subgroupOf (inducedAutOn L)) = ⊥ := by
  have hmap : (fixedSubgroup (autToCentralQuotient ↥L (a : MulAut ↥L))).map (innHom L) =
      Subgroup.centralizer ({a} : Set ↥(inducedAutOn L)) ⊓
        (innSubgroup ↥L).subgroupOf (inducedAutOn L) := by
    ext g
    constructor
    · rintro ⟨tb, htb, rfl⟩
      obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective tb
      refine ⟨(mem_fixed_iff_commutes L a t).mp htb, ?_⟩
      show innL L t ∈ (innSubgroup ↥L).subgroupOf (inducedAutOn L)
      rw [Subgroup.mem_subgroupOf, innL_coe]
      exact ⟨t, rfl⟩
    · rintro ⟨hg1, hg2⟩
      obtain ⟨t, ht⟩ := Subgroup.mem_subgroupOf.mp hg2
      have hgt : g = innL L t := Subtype.ext (by rw [innL_coe, ht])
      refine ⟨QuotientGroup.mk t, ?_, by rw [innHom_mk, hgt]⟩
      show (QuotientGroup.mk t : ↥L ⧸ Subgroup.center ↥L) ∈
        fixedSubgroup (autToCentralQuotient ↥L (a : MulAut ↥L))
      rw [mem_fixed_iff_commutes, ← hgt]
      exact hg1
  rw [← hmap]
  exact oddCoreIn_map_eq_bot (innHom L) (innHom_injective L) h

end Inn

section Quot

theorem autOddFreeInnerOn_of_centralQuotient {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    (P : (X ⧸ Subgroup.center X) → Prop) (h : AutOddFreeInnerOn (X ⧸ Subgroup.center X) P) :
    AutOddFreeInnerOn X (fun s => P (QuotientGroup.mk s)) := by
  intro 𝒳 hinn f s hs hPs hf
  have hΦ := autToCentralQuotient_injective (X := X)
  set 𝒳' := 𝒳.map (autToCentralQuotient X) with h𝒳'
  have hinn' : innSubgroup (X ⧸ Subgroup.center X) ≤ 𝒳' := by
    rintro _ ⟨s', rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s'
    refine ⟨MulAut.conj x, hinn ⟨x, rfl⟩, ?_⟩
    ext y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rfl
  let ε : ↥𝒳 ≃* ↥𝒳' := 𝒳.equivMapOfInjective (autToCentralQuotient X) hΦ
  have hf' : orderOf (ε f) = 2 := by rw [MulEquiv.orderOf_eq]; exact hf
  have hs' : MulAut.conj (QuotientGroup.mk s : X ⧸ Subgroup.center X) =
      ((ε f : ↥𝒳') : MulAut (X ⧸ Subgroup.center X)) := by
    show MulAut.conj (QuotientGroup.mk s) = autToCentralQuotient X (f : MulAut X)
    rw [← hs]
    ext y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rfl
  exact oddCoreIn_centralizer_eq_bot_of_mulEquiv ε f
    (h 𝒳' hinn' (ε f) (QuotientGroup.mk s) hs' hPs hf')

end Quot

section KleinInner

variable {H : Type} [Group H] [Finite H]

theorem alphaOf_klein_inner_good3 (L : Subgroup H) {a b : ↥(inducedAutOn L)} (ha2 : a * a = 1)
    (hb2 : b * b = 1) (hab : a * b = b * a) (hb1 : b ≠ 1)
    (ha : (a : MulAut ↥L) ∈ innSubgroup ↥L) (hb : (b : MulAut ↥L) ∈ innSubgroup ↥L)
    (hfix : ∀ ℓ : ↥L, MulAut.conj ℓ ≠ 1 → MulAut.conj ℓ * MulAut.conj ℓ = 1 →
      oddCoreIn (fixedSubgroup (autToCentralQuotient ↥L (MulAut.conj ℓ))) = ⊥)
    (hb0 : CFSG.Assembly.Dichotomy.involutionOddCore b = ⊥) :
    alphaOf (Subgroup.closure ({b, a} : Set ↥(inducedAutOn L))) = ⊥ := by
  set B : Subgroup ↥(inducedAutOn L) := Subgroup.closure ({b, a} : Set ↥(inducedAutOn L))
    with hBdef
  have hBinv : ∀ g ∈ B, g * g = 1 := mul_self_eq_one_of_mem_closure_pair hb2 ha2 hab.symm
  have hBI : B ≤ (innSubgroup ↥L).subgroupOf (inducedAutOn L) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro y hy
    rcases hy with rfl | hy
    · exact Subgroup.mem_subgroupOf.mpr hb
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Subgroup.mem_subgroupOf.mpr ha
  have hBinn : ∀ g ∈ B, (g : MulAut ↥L) ∈ innSubgroup ↥L := fun g hg =>
    Subgroup.mem_subgroupOf.mp (hBI hg)
  have hO : ∀ a₁ ∈ B, a₁ ≠ 1 → oddCoreIn (Subgroup.centralizer ({a₁} : Set ↥(inducedAutOn L)) ⊓
      (innSubgroup ↥L).subgroupOf (inducedAutOn L)) = ⊥ := by
    intro a₁ ha₁ ha₁1
    obtain ⟨ℓ, hℓ⟩ := hBinn a₁ ha₁
    have hℓ1 : MulAut.conj ℓ ≠ 1 := by
      rw [hℓ]
      intro h
      exact ha₁1 (Subtype.ext h)
    have hℓ2 : MulAut.conj ℓ * MulAut.conj ℓ = 1 := by
      rw [hℓ, ← Subgroup.coe_mul, hBinv a₁ ha₁]
      rfl
    refine oddCoreIn_centralizer_inf_inn_eq_bot L a₁ ?_
    rw [← hℓ]
    exact hfix ℓ hℓ1 hℓ2
  exact alphaOf_eq_bot_of_inner_good _ hBI (closure_pair_commute hab.symm) hO
    (a₀ := b) (Subgroup.subset_closure (Set.mem_insert _ _)) hb1 hb0

end KleinInner

section KleinOuter

variable {H : Type} [Group H] [Finite H]

theorem alphaOf_klein_outer_good3 (L : Subgroup H) {y b : ↥(inducedAutOn L)} (hy2 : y * y = 1)
    (hb2 : b * b = 1) (hyb : y * b = b * y) (hb1 : b ≠ 1)
    (hb : (b : MulAut ↥L) ∈ innSubgroup ↥L)
    (hfy : oddCoreIn (fixedSubgroup (autToCentralQuotient ↥L (y : MulAut ↥L))) = ⊥)
    (hfyb : oddCoreIn (fixedSubgroup (autToCentralQuotient ↥L ((y * b : ↥(inducedAutOn L)) :
      MulAut ↥L))) = ⊥)
    (hb0 : CFSG.Assembly.Dichotomy.involutionOddCore b = ⊥) :
    alphaOf (Subgroup.closure ({y, b} : Set ↥(inducedAutOn L))) = ⊥ := by
  set B : Subgroup ↥(inducedAutOn L) := Subgroup.closure ({y, b} : Set ↥(inducedAutOn L))
    with hBdef
  set I : Subgroup ↥(inducedAutOn L) := (innSubgroup ↥L).subgroupOf (inducedAutOn L) with hIdef
  have hbI : b ∈ I := Subgroup.mem_subgroupOf.mpr hb
  have hbB : b ∈ B := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hyB : y ∈ B := Subgroup.subset_closure (Set.mem_insert _ _)
  have hbC : ∀ a : ↥(inducedAutOn L), a * b = b * a →
      b ∈ Subgroup.centralizer ({a} : Set ↥(inducedAutOn L)) ⊓ I := fun a hab =>
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hab.symm, hbI⟩
  refine alphaOf_eq_bot_of_cover I (a₀ := b) ?_ hbB hb1 hb0
  intro a ha ha1
  rcases CFSG.ClassicalInvolution.ModelFacts.Orth15.klein_mem_closure hy2 hb2 hyb ha with
    h | h | h | h
  · exact absurd h ha1
  · rw [h]
    right
    refine ⟨oddCoreIn_centralizer_inf_inn_eq_bot L _ hfy, ?_⟩
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    rcases hg with hg | hg
    · rw [hg]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact Subgroup.mem_sup_right (hbC _ hyb)
  · rw [h]
    left
    exact hb0
  · rw [h]
    right
    refine ⟨oddCoreIn_centralizer_inf_inn_eq_bot L _ hfyb, ?_⟩
    have hyb' : y * b * b = b * (y * b) := by
      calc y * b * b = y := by rw [mul_assoc, hb2, mul_one]
        _ = b * (y * b) := by rw [← mul_assoc, ← hyb, mul_assoc, hb2, mul_one]
    have hC := hbC (y * b) hyb'
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    rcases hg with hg | hg
    · rw [hg]
      have hyy : y = (y * b) * b⁻¹ := by group
      have hmem : (y * b) * b⁻¹ ∈ Subgroup.zpowers (y * b) ⊔
          (Subgroup.centralizer ({y * b} : Set ↥(inducedAutOn L)) ⊓ I) :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
          (Subgroup.mem_sup_right ((Subgroup.centralizer ({y * b} : Set ↥(inducedAutOn L)) ⊓
            I).inv_mem hC))
      rwa [← hyy] at hmem
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact Subgroup.mem_sup_right hC

end KleinOuter

end CFSG.ClassicalInvolution.Q3.Q3OT
