module

public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutLift
public import CFSG.ClassicalInvolution.Asc77.WP3Hyp51

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S3A

open CFSG.ClassicalInvolution.Asc77

section Quot

variable {H : Type} [Group H] (L N : Subgroup H) [N.Normal]

theorem comap_map_quotient (hNL : N ≤ L) :
    (L.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = L :=
  Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hNL)

theorem mk_mem_map_iff (hNL : N ≤ L) (x : H) :
    QuotientGroup.mk' N x ∈ L.map (QuotientGroup.mk' N) ↔ x ∈ L := by
  rw [← Subgroup.mem_comap, comap_map_quotient L N hNL]

theorem mem_normalizer_map (hNL : N ≤ L) {n : H} (hn : n ∈ Subgroup.normalizer (L : Set H)) :
    QuotientGroup.mk' N n ∈
      Subgroup.normalizer ((L.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N y
  have e : QuotientGroup.mk' N n * QuotientGroup.mk' N h * (QuotientGroup.mk' N n)⁻¹ =
      QuotientGroup.mk' N (n * h * n⁻¹) := by simp
  rw [e, mk_mem_map_iff L N hNL, mk_mem_map_iff L N hNL]
  exact Subgroup.mem_normalizer_iff.mp hn h

@[expose] noncomputable def normalizerQuotHom (hNL : N ≤ L) :
    ↥(Subgroup.normalizer (L : Set H)) →*
      ↥(inducedAutOn (L.map (QuotientGroup.mk' N))) :=
  (toInducedAutOn (L.map (QuotientGroup.mk' N))).comp
    (((QuotientGroup.mk' N).comp (Subgroup.normalizer (L : Set H)).subtype).codRestrict _
      (fun n => mem_normalizer_map L N hNL n.2))

theorem normalizerQuotHom_apply (hNL : N ≤ L) (n : H) (hn : n ∈ Subgroup.normalizer (L : Set H)) :
    normalizerQuotHom L N hNL ⟨n, hn⟩ =
      toInducedAutOn (L.map (QuotientGroup.mk' N))
        ⟨QuotientGroup.mk' N n, mem_normalizer_map L N hNL hn⟩ := rfl

variable {L N}

theorem quotHom_eq_one_iff (hNL : N ≤ L) {n : H} (hn : n ∈ Subgroup.normalizer (L : Set H)) :
    normalizerQuotHom L N hNL ⟨n, hn⟩ = 1 ↔
      ∀ l ∈ L, QuotientGroup.mk' N (n * l * n⁻¹) = QuotientGroup.mk' N l := by
  rw [normalizerQuotHom_apply]
  constructor
  · intro h l hl
    have h1 : QuotientGroup.mk' N n * QuotientGroup.mk' N l * (QuotientGroup.mk' N n)⁻¹ =
        QuotientGroup.mk' N l :=
      congrArg (fun τ : ↥(inducedAutOn (L.map (QuotientGroup.mk' N))) =>
        (((τ : MulAut ↥(L.map (QuotientGroup.mk' N)))
          ⟨QuotientGroup.mk' N l, Subgroup.mem_map_of_mem _ hl⟩ :
            ↥(L.map (QuotientGroup.mk' N))) : H ⧸ N)) h
    simpa using h1
  · intro h
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    obtain ⟨l, hl, hly⟩ := Subgroup.mem_map.mp y.2
    apply Subtype.ext
    show QuotientGroup.mk' N n * (y : H ⧸ N) * (QuotientGroup.mk' N n)⁻¹ = (y : H ⧸ N)
    rw [← hly]
    simpa using h l hl

theorem ker_toInducedAutOn_le (hNL : N ≤ L) :
    (toInducedAutOn L).ker ≤ (normalizerQuotHom L N hNL).ker := by
  rintro ⟨n, hn⟩ h
  rw [MonoidHom.mem_ker] at h ⊢
  rw [quotHom_eq_one_iff hNL hn]
  intro l hl
  have h1 : n * l * n⁻¹ = l :=
    congrArg (fun τ : ↥(inducedAutOn L) => (((τ : MulAut ↥L) ⟨l, hl⟩ : ↥L) : H)) h
  rw [h1]

@[expose] noncomputable def inducedAutQuotHom (hNL : N ≤ L) :
    ↥(inducedAutOn L) →* ↥(inducedAutOn (L.map (QuotientGroup.mk' N))) :=
  MonoidHom.liftOfSurjective (toInducedAutOn L) (MonoidHom.rangeRestrict_surjective _)
    ⟨normalizerQuotHom L N hNL, ker_toInducedAutOn_le hNL⟩

theorem inducedAutQuotHom_apply (hNL : N ≤ L) (n : H) (hn : n ∈ Subgroup.normalizer (L : Set H)) :
    inducedAutQuotHom hNL (toInducedAutOn L ⟨n, hn⟩) =
      toInducedAutOn (L.map (QuotientGroup.mk' N))
        ⟨QuotientGroup.mk' N n, mem_normalizer_map L N hNL hn⟩ := by
  have hsurj := MonoidHom.rangeRestrict_surjective (conjOnNormalizer L)
  exact MonoidHom.liftOfRightInverse_comp_apply (toInducedAutOn L) (Function.surjInv hsurj)
    (Function.rightInverse_surjInv hsurj)
    ⟨normalizerQuotHom L N hNL, ker_toInducedAutOn_le hNL⟩ ⟨n, hn⟩

theorem inducedAutQuotHom_injective (hNL : N ≤ L) (hNc : N ≤ Subgroup.center H)
    [Group.IsPerfect ↥L] : Function.Injective (inducedAutQuotHom hNL) := by
  rw [injective_iff_map_eq_one]
  intro τ hτ
  obtain ⟨⟨n, hn⟩, rfl⟩ := (MonoidHom.rangeRestrict_surjective (conjOnNormalizer L)) τ
  have h1 : normalizerQuotHom L N hNL ⟨n, hn⟩ = 1 := by
    have := inducedAutQuotHom_apply hNL n hn
    rw [normalizerQuotHom_apply]
    exact this.symm.trans hτ
  rw [quotHom_eq_one_iff hNL hn] at h1
  have hker : (((QuotientGroup.mk' N).comp L.subtype : ↥L →* H ⧸ N)).ker ≤
      Subgroup.center ↥L := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hNc hx) y
  have hab : (conjOnNormalizer L ⟨n, hn⟩).toMonoidHom = MonoidHom.id ↥L := by
    refine CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.hom_eq_of_central_ker_perfect hker _ _
      (fun x => ?_)
    show QuotientGroup.mk' N (n * (x : H) * n⁻¹) = QuotientGroup.mk' N (x : H)
    exact h1 (x : H) x.2
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  exact DFunLike.congr_fun hab x

theorem inducedAutQuotHom_surjective (hNL : N ≤ L) :
    Function.Surjective (inducedAutQuotHom hNL) := by
  intro τ'
  obtain ⟨⟨h', hh'⟩, rfl⟩ := (MonoidHom.rangeRestrict_surjective (conjOnNormalizer
    (L.map (QuotientGroup.mk' N)))) τ'
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N h'
  have hh : h ∈ Subgroup.normalizer (L : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h2 := Subgroup.mem_normalizer_iff.mp hh' (QuotientGroup.mk' N x)
    rw [mk_mem_map_iff L N hNL] at h2
    have e : QuotientGroup.mk' N h * QuotientGroup.mk' N x * (QuotientGroup.mk' N h)⁻¹ =
        QuotientGroup.mk' N (h * x * h⁻¹) := by simp
    rw [e, mk_mem_map_iff L N hNL] at h2
    exact h2
  exact ⟨toInducedAutOn L ⟨h, hh⟩, inducedAutQuotHom_apply hNL h hh⟩

@[expose] noncomputable def inducedAutQuotEquiv (hNL : N ≤ L) (hNc : N ≤ Subgroup.center H)
    [Group.IsPerfect ↥L] :
    ↥(inducedAutOn L) ≃* ↥(inducedAutOn (L.map (QuotientGroup.mk' N))) :=
  MulEquiv.ofBijective (inducedAutQuotHom hNL)
    ⟨inducedAutQuotHom_injective hNL hNc, inducedAutQuotHom_surjective hNL⟩

theorem inducedAutQuotEquiv_apply (hNL : N ≤ L) (hNc : N ≤ Subgroup.center H) [Group.IsPerfect ↥L]
    (n : H) (hn : n ∈ Subgroup.normalizer (L : Set H)) :
    inducedAutQuotEquiv hNL hNc (toInducedAutOn L ⟨n, hn⟩) =
      toInducedAutOn (L.map (QuotientGroup.mk' N))
        ⟨QuotientGroup.mk' N n, mem_normalizer_map L N hNL hn⟩ :=
  inducedAutQuotHom_apply hNL n hn

end Quot

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S3A
