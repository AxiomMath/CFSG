module

public import CFSG.HardMathSupport.Timmesfeld.Balance.Reduction
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I194Orbit

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.Balance

section Transport

variable {M M' : Type} [Group M] [Group M']

theorem centralizer_map_mulEquiv (φ : M ≃* M') (D : Subgroup M) :
    (Subgroup.centralizer (D : Set M)).map φ.toMonoidHom =
      Subgroup.centralizer ((D.map φ.toMonoidHom : Subgroup M') : Set M') := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    intro z hz
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hz
    have h1 := Subgroup.mem_centralizer_iff.1 hx d hd
    show φ d * φ x = φ x * φ d
    rw [← map_mul, ← map_mul, h1]
  · intro h
    refine ⟨φ.symm y, ?_, by simp⟩
    intro d hd
    apply φ.injective
    have h1 := Subgroup.mem_centralizer_iff.1 h (φ d) (Subgroup.mem_map.2 ⟨d, hd, rfl⟩)
    rw [map_mul, map_mul]
    simpa using h1

theorem isCoreFree_map_congr {K K' : Type} [Group K] [Group K'] (p : ℕ) (θ : K ≃* K')
    {A : Subgroup (MulAut K)} (h : IsCoreFreeLocalType p A) :
    IsCoreFreeLocalType p (A.map (MulAut.congr θ).toMonoidHom) := by
  intro D' hD' H' hH' hDH'
  set φ := MulAut.congr θ with hφ
  have hD : D'.map φ.symm.toMonoidHom ≤ A := by
    have := Subgroup.map_mono (f := φ.symm.toMonoidHom) hD'
    rwa [map_map_symm_mulEquiv] at this
  have hH : innerAut K ≤ H'.map φ.symm.toMonoidHom := by
    rintro _ ⟨k, rfl⟩
    rw [Subgroup.mem_map_equiv]
    have h1 := hH' ⟨θ k, rfl⟩
    have e : φ (MulAut.conj k) = MulAut.conj (θ k) := congr_conj_apply θ k
    show φ (MulAut.conj k) ∈ H'
    rw [e]
    exact h1
  have hDH : D'.map φ.symm.toMonoidHom ≤
      Subgroup.normalizer ((H'.map φ.symm.toMonoidHom : Subgroup _) : Set _) := by
    rintro _ ⟨d', hd', rfl⟩
    exact mem_normalizer_map_symm φ (hDH' hd')
  have key := h _ hD _ hH hDH
  have e : H' ⊓ Subgroup.centralizer ((D' : Subgroup (MulAut K')) : Set (MulAut K')) =
      (H'.map φ.symm.toMonoidHom ⊓
        Subgroup.centralizer ((D'.map φ.symm.toMonoidHom : Subgroup (MulAut K)) : Set (MulAut K))).map
        φ.toMonoidHom := by
    rw [Subgroup.map_inf_eq _ _ φ.toMonoidHom φ.injective, centralizer_map_mulEquiv,
      map_symm_map_mulEquiv, map_symm_map_mulEquiv]
  rw [e, gLAPPrimeCoreOf_map_mulEquiv, key, Subgroup.map_bot]

theorem isCoreFree_mono {K : Type} [Group K] (p : ℕ) {A A' : Subgroup (MulAut K)} (hA : A' ≤ A)
    (h : IsCoreFreeLocalType p A) : IsCoreFreeLocalType p A' :=
  fun D hD H hH hDH => h D (hD.trans hA) H hH hDH

end Transport

section BarX

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem isSubnormal_barX_top {X J : Subgroup G} (hsn : IsSubnormal J X) :
    IsSubnormal (barX p X J) ⊤ := by
  have h := isSubnormal_barX p (C := X) hsn
  rwa [barX_self] at h

theorem glaPPrimeCore_barX_eq_bot (hp : p.Prime) {X J : Subgroup G} (hsn : IsSubnormal J X) :
    GLAPPrimeCore p ↥(barX p X J) = ⊥ :=
  glaPPrimeCore_eq_bot_of_subnormal hp (glaPPrimeCore_quotient_eq_bot hp)
    (isSubnormal_barX_top hsn)

noncomputable def barOfIso (hp : p.Prime) {X J : Subgroup G} (hJX : J ≤ X)
    (hsn : IsSubnormal J X) : barOf p J ≃* barOf p (barX p X J) :=
  (barIso hp hJX hsn).trans
    (((QuotientGroup.quotientMulEquivOfEq (glaPPrimeCore_barX_eq_bot hp hsn)).trans
      QuotientGroup.quotientBot).symm)

theorem barOfIso_mk (hp : p.Prime) {X J : Subgroup G} (hJX : J ≤ X) (hsn : IsSubnormal J X)
    (x : ↥J) : barOfIso hp hJX hsn (QuotientGroup.mk x) =
      QuotientGroup.mk (barHom p hJX x) := by
  unfold barOfIso
  rw [MulEquiv.trans_apply, barIso_mk]
  rw [MulEquiv.symm_apply_eq]
  rfl

theorem congr_apply_apply {K K' : Type} [Group K] [Group K'] (θ : K ≃* K') (f : MulAut K)
    (z : K) : MulAut.congr θ f (θ z) = θ (f z) := by
  simp [MulAut.congr_apply]

theorem autBar_barX_le (hp : p.Prime) {X B J : Subgroup G} (hJX : J ≤ X)
    (hsn : IsSubnormal J X) (hJ : GLAPComponent p X J) :
    autBar p (barX p X B) (barX p X J) ≤
      (autBar p B J).map (MulAut.congr (barOfIso hp hJX hsn)).toMonoidHom := by
  rintro _ ⟨γ, hγ, rfl⟩
  have hγ' := Subgroup.mem_subgroupOf.1 hγ
  obtain ⟨hγB, hγN⟩ := Subgroup.mem_inf.1 hγ'
  obtain ⟨x, hxB, hxγ⟩ := (mem_barX_iff p X B _).1 hγB
  have hxN : (x : G) ∈ Subgroup.normalizer (J : Set G) :=
    mem_normalizer_of_barX_normalizer hJ x.2 (by rw [hxγ]; exact hγN)
  set δ : ↥(Subgroup.normalizer (J : Set G)) := ⟨(x : G), hxN⟩ with hδ
  have hδmem : δ ∈ ((B ⊓ Subgroup.normalizer (J : Set G)).subgroupOf
      (Subgroup.normalizer (J : Set G))) :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hxB, hxN⟩)
  refine Subgroup.mem_map.2 ⟨barAut p J δ, Subgroup.mem_map.2 ⟨δ, hδmem, rfl⟩, ?_⟩
  apply MulEquiv.ext
  intro z
  obtain ⟨w, rfl⟩ := (barOfIso hp hJX hsn).surjective z
  induction w using QuotientGroup.induction_on with
  | _ y =>
    rw [MulEquiv.coe_toMonoidHom, congr_apply_apply, barAut_mk, barOfIso_mk, barOfIso_mk,
      barAut_mk]
    congr 1
    apply Subtype.ext
    simp only [coe_barHom, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [← hxγ]
    rfl

theorem isCompCoreFree_barX (hp : p.Prime) {X B J : Subgroup G} (hJ : GLAPComponent p X J)
    (hcf : IsCompCoreFreeLocalType p B J) :
    IsCompCoreFreeLocalType p (barX p X B) (barX p X J) := by
  have hJ' := hJ
  obtain ⟨hJX, hsn, -, -⟩ := hJ'
  unfold IsCompCoreFreeLocalType at hcf ⊢
  exact isCoreFree_mono p (autBar_barX_le hp hJX hsn hJ)
    (isCoreFree_map_congr p (barOfIso hp hJX hsn) hcf)

end BarX

end CFSG.LocalAnalysis.GLTheoremA
