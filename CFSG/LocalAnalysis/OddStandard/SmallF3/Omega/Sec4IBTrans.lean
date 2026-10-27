module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBSyl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def Sec4IFrame.map (g : OGroup Q) (fr : Sec4IFrame Q) : Sec4IFrame Q where
  b := fr.b.map (g : V ≃ₗ[ZMod 3] V)
  neg i := by
    rw [Module.Basis.map_apply]
    exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.2 _).trans (fr.neg i)
  orth i j hij := by
    have h := fr.orth i j hij
    rw [Module.Basis.map_apply, Module.Basis.map_apply]
    simp only [QuadraticMap.polar] at h ⊢
    rw [← map_add]
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.2,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.2,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.2]
    exact h

theorem sec4IT_map (g : OGroup Q) (fr : Sec4IFrame Q) (v : Fin 7 → ZMod 2) :
    sec4IT (fr.map g) v = g * sec4IT fr v * g⁻¹ := by
  apply sec4I_ogroup_ext (fr.map g)
  intro i
  have hR : ((g * sec4IT fr v * g⁻¹ : OGroup Q) : V ≃ₗ[ZMod 3] V)
        ((g : V ≃ₗ[ZMod 3] V) (fr.b i)) =
      ((sec4ISgn (v i) : (ZMod 3)ˣ) : ZMod 3) • (g : V ≃ₗ[ZMod 3] V) (fr.b i) := by
    have hcoe : ((g * sec4IT fr v * g⁻¹ : OGroup Q) : V ≃ₗ[ZMod 3] V) =
        (g : V ≃ₗ[ZMod 3] V) * (sec4IT fr v : V ≃ₗ[ZMod 3] V) *
          (g : V ≃ₗ[ZMod 3] V)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    simp only [hcoe, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply, sec4IT_apply_basis, map_smul]
  have hb : (Sec4IFrame.map g fr).b i = (g : V ≃ₗ[ZMod 3] V) (fr.b i) := by
    rw [show (Sec4IFrame.map g fr).b = fr.b.map (g : V ≃ₗ[ZMod 3] V) from rfl,
      Module.Basis.map_apply]
  rw [sec4IT_apply_basis, hb]
  exact hR.symm

theorem mem_sec4IB0_map (g : OGroup Q) (fr : Sec4IFrame Q) (x : ProjOrth Q) :
    x ∈ sec4IB0 (fr.map g) ↔ (toProj Q g)⁻¹ * x * toProj Q g ∈ sec4IB0 fr := by
  rw [mem_sec4IB0_iff, mem_sec4IB0_iff]
  have hpsi : ∀ v : Fin 7 → ZMod 2, sec4IPsi (fr.map g) v =
      (toProj Q g) * sec4IPsi fr v * (toProj Q g)⁻¹ := by
    intro v
    change toProj Q (sec4IT (fr.map g) v) =
      toProj Q g * toProj Q (sec4IT fr v) * (toProj Q g)⁻¹
    rw [sec4IT_map, map_mul, map_mul, map_inv]
  constructor
  · rintro ⟨v, hv, hx⟩
    refine ⟨v, hv, ?_⟩
    rw [← hx, hpsi]
    group
  · rintro ⟨v, hv, hx⟩
    refine ⟨v, hv, ?_⟩
    rw [hpsi, hx]
    group

theorem sec4IGood_map {fr : Sec4IFrame Sec4IQ} {R : Subgroup (ProjOrth Sec4IQ)}
    (h : Sec4IGood fr R) {g : OGroup Sec4IQ} (hg : toProj Sec4IQ g ∈ Sec4IOmega)
    {R' : Subgroup (ProjOrth Sec4IQ)}
    (hR' : ∀ x, x ∈ R' ↔ (toProj Sec4IQ g)⁻¹ * x * toProj Sec4IQ g ∈ R) :
    Sec4IGood (fr.map g) R' := by
  classical
  let a : ProjOrth Sec4IQ := toProj Sec4IQ g
  let φ : ProjOrth Sec4IQ →* ProjOrth Sec4IQ := (MulAut.conj a).toMonoidHom
  have hφinj : Function.Injective φ := (MulAut.conj a).injective
  have hφsurj : Function.Surjective φ := (MulAut.conj a).surjective
  have hR'map : R' = R.map φ := by
    ext x
    rw [hR']
    constructor
    · intro hx
      refine ⟨a⁻¹ * x * a, hx, ?_⟩
      change (MulAut.conj a) (a⁻¹ * x * a) = x
      rw [MulAut.conj_apply]
      group
    · rintro ⟨r, hr, rfl⟩
      change a⁻¹ * (MulAut.conj a) r * a ∈ R
      rw [MulAut.conj_apply]
      have hconj : a⁻¹ * (a * r * a⁻¹) * a = r := by group
      rwa [hconj]
  have hOmegaMap : Sec4IOmega.map φ = Sec4IOmega := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact Sec4IOmega.mul_mem (Sec4IOmega.mul_mem hg hy) (Sec4IOmega.inv_mem hg)
    · intro x hx
      refine ⟨a⁻¹ * x * a,
        Sec4IOmega.mul_mem (Sec4IOmega.mul_mem (Sec4IOmega.inv_mem hg) hx) hg, ?_⟩
      change (MulAut.conj a) (a⁻¹ * x * a) = x
      rw [MulAut.conj_apply]
      group
  have hR'le : R' ≤ Sec4IOmega := by
    intro x hx
    have hxR : a⁻¹ * x * a ∈ Sec4IOmega := h.sylow.1 ((hR' x).mp hx)
    have hxa : a * (a⁻¹ * x * a) * a⁻¹ = x := by group
    rw [← hxa]
    exact Sec4IOmega.mul_mem (Sec4IOmega.mul_mem hg hxR) (Sec4IOmega.inv_mem hg)
  have hR'pg : IsPGroup 2 R' := by
    rw [hR'map]
    exact h.sylow.2.1.map φ
  have hrel : R'.relIndex Sec4IOmega = R.relIndex Sec4IOmega := by
    rw [hR'map]
    have hh := Subgroup.relIndex_map_map_of_injective (f := φ) R Sec4IOmega hφinj
    rw [hOmegaMap] at hh
    exact hh
  have hR'syl : IsSylow2Of R' Sec4IOmega :=
    ⟨hR'le, hR'pg, by rw [hrel]; exact h.sylow.2.2⟩
  refine ⟨hR'syl, ?_, ?_, ?_⟩
  · intro x hx
    rw [hR']
    exact h.le ((mem_sec4IB0_map g fr x).mp hx)
  · intro F hFR hF
    have hF''R : F.comap φ ≤ R := by
      intro x hx
      change φ x ∈ F at hx
      have hx'' : a⁻¹ * φ x * a ∈ R := (hR' (φ x)).mp (hFR hx)
      have hx3 : a⁻¹ * φ x * a = x := by
        change a⁻¹ * (MulAut.conj a) x * a = x
        rw [MulAut.conj_apply]
        group
      rwa [hx3] at hx''
    have hF'' : CFSG.Open.IsElemAbelian 2 (F.comap φ) := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · apply Subtype.ext
        apply hφinj
        simp only [Subgroup.coe_mul]
        rw [map_mul, map_mul]
        exact congrArg Subtype.val
          (hF.1.is_comm.comm ⟨φ ↑a, a.2⟩ ⟨φ ↑b, b.2⟩)
      · apply hφinj
        rw [map_pow, map_one, hF.2 (φ x) hx]
    have hcardF'' : Nat.card (F.comap φ) = Nat.card F := by
      rw [← Subgroup.card_map_of_injective (K := F.comap φ) (f := φ) hφinj,
        Subgroup.map_comap_eq_self_of_surjective (f := φ) hφsurj F]
    have hle := h.card_le (F.comap φ) hF''R hF''
    rwa [hcardF''] at hle
  · intro F hFR hF hcard
    have hF''R : F.comap φ ≤ R := by
      intro x hx
      change φ x ∈ F at hx
      have hx'' : a⁻¹ * φ x * a ∈ R := (hR' (φ x)).mp (hFR hx)
      have hx3 : a⁻¹ * φ x * a = x := by
        change a⁻¹ * (MulAut.conj a) x * a = x
        rw [MulAut.conj_apply]
        group
      rwa [hx3] at hx''
    have hF'' : CFSG.Open.IsElemAbelian 2 (F.comap φ) := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · apply Subtype.ext
        apply hφinj
        simp only [Subgroup.coe_mul]
        rw [map_mul, map_mul]
        exact congrArg Subtype.val
          (hF.1.is_comm.comm ⟨φ ↑a, a.2⟩ ⟨φ ↑b, b.2⟩)
      · apply hφinj
        rw [map_pow, map_one, hF.2 (φ x) hx]
    have hcardF'' : Nat.card (F.comap φ) = Nat.card F := by
      rw [← Subgroup.card_map_of_injective (K := F.comap φ) (f := φ) hφinj,
        Subgroup.map_comap_eq_self_of_surjective (f := φ) hφsurj F]
    have hFB0 : F.comap φ = sec4IB0 fr :=
      h.eq_B0 (F.comap φ) hF''R hF'' (by rw [hcardF'']; exact hcard)
    have hmapB0 : (sec4IB0 fr).map φ = sec4IB0 (fr.map g) := by
      ext x
      rw [mem_sec4IB0_map g fr x]
      constructor
      · rintro ⟨y, hy, hxy⟩
        rw [← hxy]
        change a⁻¹ * (MulAut.conj a) y * a ∈ sec4IB0 fr
        rw [MulAut.conj_apply]
        have hconj : a⁻¹ * (a * y * a⁻¹) * a = y := by group
        rwa [hconj]
      · intro hx
        refine ⟨a⁻¹ * x * a, hx, ?_⟩
        change (MulAut.conj a) (a⁻¹ * x * a) = x
        rw [MulAut.conj_apply]
        group
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := φ) hφsurj F, hFB0, hmapB0]

theorem sec4I_exists_frame_good {R : Subgroup (ProjOrth Sec4IQ)}
    (hR : IsSylow2Of R Sec4IOmega) : ∃ fr : Sec4IFrame Sec4IQ, Sec4IGood fr R := by
  obtain ⟨fr0⟩ := sec4I_exists_frame
  obtain ⟨R0, hR0⟩ := sec4I_exists_good fr0
  obtain ⟨a, ha, hconj⟩ := IsSylow2Of.exists_conj_mem hR0.sylow hR
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (piGroup Sec4IQ) a
  have hgmem : toProj Sec4IQ g ∈ Sec4IOmega := by rw [hg]; exact ha
  refine ⟨fr0.map g, sec4IGood_map hR0 hgmem ?_⟩
  intro x
  rw [hg]
  exact hconj x

end CFSG.OddStandard.SmallF3.Omega
