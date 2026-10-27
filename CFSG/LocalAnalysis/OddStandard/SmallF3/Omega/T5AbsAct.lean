module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G G' : Type} [Group G] [Group G'] {L : Subgroup G} {L' : Subgroup G'}

structure IsActQuot (f : ↥L →* ↥L') (s : G) (s' : G') : Prop where
  surjective : Function.Surjective f
  ker_le_center : f.ker ≤ Subgroup.center ↥L
  center_of_map : ∀ l : ↥L, f l ∈ Subgroup.center ↥L' → l ∈ Subgroup.center ↥L
  mem_normalizer : s ∈ Subgroup.normalizer (L : Set G)
  mem_normalizer' : s' ∈ Subgroup.normalizer (L' : Set G')
  conj : ∀ l l' : ↥L, (l' : G) = s * l * s⁻¹ →
    ((f l' : ↥L') : G') = s' * ((f l : ↥L') : G') * s'⁻¹

@[expose] def ActQuot (L : Subgroup G) (L' : Subgroup G') (s : G) (s' : G') : Prop :=
  ∃ f : ↥L →* ↥L', IsActQuot f s s'

private theorem ker_mk_comp_eq_center {f : ↥L →* ↥L'} {s : G} {s' : G'} (hf : IsActQuot f s s') :
    Subgroup.center ↥L = ((QuotientGroup.mk' (Subgroup.center ↥L')).comp f).ker := by
  ext l
  constructor
  · intro hl
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_center_iff]
    intro y
    obtain ⟨l₂, rfl⟩ := hf.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hl l₂]
  · intro hl
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hl
    exact hf.center_of_map l hl

noncomputable def IsActQuot.quotEquiv {f : ↥L →* ↥L'} {s : G} {s' : G'} (hf : IsActQuot f s s') :
    ↥L ⧸ Subgroup.center ↥L ≃* ↥L' ⧸ Subgroup.center ↥L' :=
  (QuotientGroup.quotientMulEquivOfEq (ker_mk_comp_eq_center hf)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk'_surjective _).comp hf.surjective))

theorem IsActQuot.quotEquiv_mk {f : ↥L →* ↥L'} {s : G} {s' : G'} (hf : IsActQuot f s s')
    (l : ↥L) :
    hf.quotEquiv (QuotientGroup.mk l) = QuotientGroup.mk (f l) := by
  unfold IsActQuot.quotEquiv
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem IsActQuot.inducesViaP_iff {f : ↥L →* ↥L'} {s : G} {s' : G'} (hf : IsActQuot f s s')
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} (hQ : Q.Nondegenerate)
    (e : ↥L' ⧸ Subgroup.center ↥L' ≃* omegaProj hQ) (x : ProjSim Q) :
    InducesViaP L' (Subgroup.center ↥L') hQ e s' x ↔
      InducesViaP L (Subgroup.center ↥L) hQ (hf.quotEquiv.trans e) s x := by
  constructor
  · rintro ⟨hs', H'⟩
    refine ⟨hf.mem_normalizer, ?_⟩
    intro l l' hl
    have hconj : ((f l' : ↥L') : G') = s' * ((f l : ↥L') : G') * s'⁻¹ := hf.conj l l' hl
    have h := H' (f l) (f l') hconj
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hf.quotEquiv_mk, hf.quotEquiv_mk]
    exact h
  · rintro ⟨hs, H⟩
    refine ⟨hf.mem_normalizer', ?_⟩
    intro l₁ l₁' hl₁
    obtain ⟨l, rfl⟩ := hf.surjective l₁
    have hmem : s * (l : G) * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hs l).mp l.2
    let l₂ : ↥L := ⟨s * (l : G) * s⁻¹, hmem⟩
    have hl₂ : (l₂ : G) = s * l * s⁻¹ := rfl
    have hconj : ((f l₂ : ↥L') : G') = s' * ((f l : ↥L') : G') * s'⁻¹ := hf.conj l l₂ hl₂
    have hfl₂ : f l₂ = l₁' := Subtype.ext (hconj.trans hl₁.symm)
    have h := H l l₂ hl₂
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hf.quotEquiv_mk, hf.quotEquiv_mk, hfl₂] at h
    exact h

private theorem transfer_aux {f : ↥L →* ↥L'} {s : G} {s' : G'} (hf : IsActQuot f s s')
    (n : ℕ) (ε : ℤˣ)
    (P : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
      {Q : QuadraticForm (ZMod 3) V}, ProjSim Q → Prop) :
    (∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V)
      (_ : FiniteDimensional (ZMod 3) V) (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate)
      (e : ↥L' ⧸ Subgroup.center ↥L' ≃* omegaProj hQ) (x : ProjSim Q),
      Module.finrank (ZMod 3) V = n ∧ quadSign Q = ε ∧
        InducesViaP L' (Subgroup.center ↥L') hQ e s' x ∧ P x) ↔
    (∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V)
      (_ : FiniteDimensional (ZMod 3) V) (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate)
      (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (x : ProjSim Q),
      Module.finrank (ZMod 3) V = n ∧ quadSign Q = ε ∧
        InducesViaP L (Subgroup.center ↥L) hQ e s x ∧ P x) := by
  constructor
  · rintro ⟨V, i1, i2, i3, Q, hQ, e, x, hdim, hsgn, hind, hty⟩
    letI := i1; letI := i2; letI := i3
    exact ⟨V, i1, i2, i3, Q, hQ, hf.quotEquiv.trans e, x, hdim, hsgn,
      (hf.inducesViaP_iff hQ e x).mp hind, hty⟩
  · rintro ⟨V, i1, i2, i3, Q, hQ, e, x, hdim, hsgn, hind, hty⟩
    letI := i1; letI := i2; letI := i3
    refine ⟨V, i1, i2, i3, Q, hQ, hf.quotEquiv.symm.trans e, x, hdim, hsgn, ?_, hty⟩
    have he : hf.quotEquiv.trans (hf.quotEquiv.symm.trans e) = e := by
      ext a; simp [MulEquiv.trans_apply]
    rw [(hf.inducesViaP_iff hQ (hf.quotEquiv.symm.trans e) x), he]
    exact hind

theorem inducesTypeSome_transfer {s : G} {s' : G'} (h : ActQuot L L' s s') (n : ℕ) (ε : ℤˣ)
    (r : ℕ) (α : ℤˣ) : InducesTypeSome L' s' n ε r α ↔ InducesTypeSome L s n ε r α := by
  obtain ⟨f, hf⟩ := h
  exact transfer_aux hf n ε (fun x => SimHasType x r α)

theorem inducesProjective_transfer {s : G} {s' : G'} (h : ActQuot L L' s s') (n : ℕ) (ε : ℤˣ) :
    InducesProjective L' n ε s' ↔ InducesProjective L n ε s := by
  obtain ⟨f, hf⟩ := h
  exact transfer_aux hf n ε (fun x => SimIsProjective x)

theorem inducesOutsideGStar_transfer {s : G} {s' : G'} (h : ActQuot L L' s s') (n : ℕ) (ε : ℤˣ) :
    InducesOutsideGStar L' n ε s' ↔ InducesOutsideGStar L n ε s := by
  obtain ⟨f, hf⟩ := h
  exact transfer_aux hf n ε (fun x => x * x = 1 ∧ ¬ SimInGStar x)

end CFSG.OddStandard.SmallF3.Omega
