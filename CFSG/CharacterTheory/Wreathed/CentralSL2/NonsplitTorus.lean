module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.NonsplitElements

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section Torus

variable (F : Type) [Field F] [Fintype F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (E : Type) [Field E] [Algebra F E] (basis : Module.Basis (Fin 2) F E)

@[expose] noncomputable def projectiveTorus : Subgroup (ProjGenLinGroup (Fin 2) F) :=
  (ProjGenLinGroup.mk.comp (mulGL F E basis)).range

@[expose] noncomputable def nonsplitTorus : Subgroup (CentralExtension F b m hm heven) :=
  (projectiveTorus F E basis).comap (projectiveMap F b m hm heven)

variable {F b m hm heven E basis}

omit [Fintype F] in
theorem mem_nonsplitTorus_iff (g : CentralExtension F b m hm heven) :
    g ∈ nonsplitTorus F b m hm heven E basis ↔
      ∃ s : Eˣ, ProjGenLinGroup.mk (mulGL F E basis s) = projectiveMap F b m hm heven g := by
  rw [nonsplitTorus, Subgroup.mem_comap, projectiveTorus, MonoidHom.mem_range]
  rfl

theorem nonsplitDiag_mem (t : normOne F E) :
    nonsplitDiag F b m hm heven E basis t ∈ nonsplitTorus F b m hm heven E basis :=
  (mem_nonsplitTorus_iff _).mpr ⟨t, (projectiveMap_nonsplitDiag t).symm⟩

variable (z : Eˣ) (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b)

theorem nonsplitGenerator_mem :
    nonsplitGenerator F b m hm heven E basis z hz ∈ nonsplitTorus F b m hm heven E basis :=
  (mem_nonsplitTorus_iff _).mpr ⟨z, (projectiveMap_nonsplitGenerator z hz).symm⟩

omit [Fintype F] in
theorem cyclicGenerator_sq_mem_nonsplitTorus (hb : ¬ IsSquare b) :
    cyclicGenerator F b m hm heven ^ 2 ∈ nonsplitTorus F b m hm heven E basis := by
  rw [mem_nonsplitTorus_iff]
  refine ⟨1, ?_⟩
  rw [map_one, map_one]
  have h := (projectiveMap_ker F b m hm heven hb).ge
    (Subgroup.mem_zpowers (cyclicGenerator F b m hm heven ^ 2))
  exact (MonoidHom.mem_ker.mp h).symm

omit [Fintype F] in
theorem zpowers_le_nonsplitTorus (hb : ¬ IsSquare b) :
    Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) ≤
      nonsplitTorus F b m hm heven E basis := by
  rw [Subgroup.zpowers_le]
  exact cyclicGenerator_sq_mem_nonsplitTorus hb

theorem nonsplitTorus_normalForm (g : CentralExtension F b m hm heven)
    (hg : g ∈ nonsplitTorus F b m hm heven E basis) :
    ∃ t : normOne F E, ∃ k : Fin m, g = nonsplitDiag F b m hm heven E basis t *
      nonsplitGenerator F b m hm heven E basis z hz ^ (k : ℕ) := by
  have : NeZero m := ⟨hm.ne'⟩
  set k : Fin m := ⟨(baseResidue F b m hm heven g).toAdd.val, ZMod.val_lt _⟩ with hk
  have hres : baseResidue F b m hm heven
      (g * (nonsplitGenerator F b m hm heven E basis z hz ^ (k : ℕ))⁻¹) = 1 := by
    rw [map_mul, map_inv, baseResidue_nonsplitGenerator_pow, hk]
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
    rw [ofAdd_toAdd, mul_inv_cancel]
  have hmem : g * (nonsplitGenerator F b m hm heven E basis z hz ^ (k : ℕ))⁻¹ ∈
      (specialInclusion F b m hm heven).range := by
    rw [← baseResidue_ker, MonoidHom.mem_ker]
    exact hres
  obtain ⟨X, hX⟩ := hmem
  have hXT : specialInclusion F b m hm heven X ∈ nonsplitTorus F b m hm heven E basis := by
    rw [hX]
    exact (nonsplitTorus F b m hm heven E basis).mul_mem hg
      ((nonsplitTorus F b m hm heven E basis).inv_mem
        ((nonsplitTorus F b m hm heven E basis).pow_mem (nonsplitGenerator_mem z hz) _))
  obtain ⟨s, hs⟩ := (mem_nonsplitTorus_iff _).mp hXT
  rw [projectiveMap_specialInclusion, ProjGenLinGroup.mk_eq_mk_iff] at hs
  obtain ⟨c, hc⟩ := hs
  have hX' : SpecialLinearGroup.toGL X = mulGL F E basis (s * unitE F E c) := by
    rw [map_mul, mulGL_unitE, hc]
  have hmemN : s * unitE F E c ∈ normOne F E := by
    rw [mem_normOne_iff]
    have hdet : (mulMatrix F E basis ((s * unitE F E c : Eˣ) : E)).det = 1 := by
      rw [← mulGL_val, ← hX']
      exact X.2
    rw [← algebraMap_det_mulMatrix F E basis, hdet, map_one]
  refine ⟨⟨s * unitE F E c, hmemN⟩, k, ?_⟩
  have hXeq : X = mulSL F E basis ⟨s * unitE F E c, hmemN⟩ :=
    SpecialLinearGroup.toGL_injective (by rw [hX', toGL_mulSL])
  rw [nonsplitDiag, MonoidHom.comp_apply, ← hXeq, hX, inv_mul_cancel_right]

theorem nonsplitDiag_injective : Function.Injective (nonsplitDiag F b m hm heven E basis) :=
  (specialInclusion_injective F b m hm heven).comp (mulSL_injective F E basis)

theorem nonsplitTorus_normalForm_unique {t t' : normOne F E} {k k' : Fin m}
    (h : nonsplitDiag F b m hm heven E basis t *
        nonsplitGenerator F b m hm heven E basis z hz ^ (k : ℕ) =
      nonsplitDiag F b m hm heven E basis t' *
        nonsplitGenerator F b m hm heven E basis z hz ^ (k' : ℕ)) :
    t = t' ∧ k = k' := by
  have : NeZero m := ⟨hm.ne'⟩
  have hres := congrArg (baseResidue F b m hm heven) h
  rw [map_mul, map_mul, baseResidue_nonsplitDiag, baseResidue_nonsplitDiag, one_mul, one_mul,
    baseResidue_nonsplitGenerator_pow, baseResidue_nonsplitGenerator_pow] at hres
  have hkk : k = k' := by
    have := congrArg ZMod.val (congrArg Multiplicative.toAdd hres)
    simp only [toAdd_ofAdd, ZMod.val_natCast, Nat.mod_eq_of_lt k.2, Nat.mod_eq_of_lt k'.2] at this
    exact Fin.ext this
  subst hkk
  exact ⟨nonsplitDiag_injective (mul_right_cancel h), rfl⟩

include z hz in
theorem card_nonsplitTorus :
    Nat.card (nonsplitTorus F b m hm heven E basis) = m * (Nat.card F + 1) := by
  let e : normOne F E × Fin m → nonsplitTorus F b m hm heven E basis := fun p =>
    ⟨nonsplitDiag F b m hm heven E basis p.1 *
        nonsplitGenerator F b m hm heven E basis z hz ^ (p.2 : ℕ),
      (nonsplitTorus F b m hm heven E basis).mul_mem (nonsplitDiag_mem _)
        ((nonsplitTorus F b m hm heven E basis).pow_mem (nonsplitGenerator_mem z hz) _)⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨t, k⟩ ⟨t', k'⟩ h
      obtain ⟨h1, h2⟩ := nonsplitTorus_normalForm_unique z hz (congrArg Subtype.val h)
      exact Prod.ext h1 h2
    · rintro ⟨g, hg⟩
      obtain ⟨t, k, rfl⟩ := nonsplitTorus_normalForm z hz g hg
      exact ⟨(t, k), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective e he), Nat.card_prod, card_normOne F E basis,
    Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin, mul_comm]

include z hz in
theorem nonsplitTorus_mul_comm {g g' : CentralExtension F b m hm heven}
    (hg : g ∈ nonsplitTorus F b m hm heven E basis)
    (hg' : g' ∈ nonsplitTorus F b m hm heven E basis) : g * g' = g' * g := by
  obtain ⟨t, k, rfl⟩ := nonsplitTorus_normalForm z hz g hg
  obtain ⟨t', k', rfl⟩ := nonsplitTorus_normalForm z hz g' hg'
  have hcomm : ∀ (s : normOne F E) (n : ℕ),
      Commute (nonsplitGenerator F b m hm heven E basis z hz ^ n)
        (nonsplitDiag F b m hm heven E basis s) := fun s n =>
    Commute.pow_left (nonsplitGenerator_mul_nonsplitDiag z hz s) n
  have hdd : ∀ s s' : normOne F E, Commute (nonsplitDiag F b m hm heven E basis s)
      (nonsplitDiag F b m hm heven E basis s') := fun s s' => by
    change _ * _ = _ * _
    rw [← map_mul, ← map_mul, mul_comm s s']
  calc nonsplitDiag F b m hm heven E basis t *
        nonsplitGenerator F b m hm heven E basis z hz ^ (k : ℕ) *
        (nonsplitDiag F b m hm heven E basis t' *
          nonsplitGenerator F b m hm heven E basis z hz ^ (k' : ℕ))
      = nonsplitDiag F b m hm heven E basis t * nonsplitDiag F b m hm heven E basis t' *
          (nonsplitGenerator F b m hm heven E basis z hz ^ (k : ℕ) *
            nonsplitGenerator F b m hm heven E basis z hz ^ (k' : ℕ)) := by
        rw [mul_assoc, ← mul_assoc (nonsplitGenerator F b m hm heven E basis z hz ^ (k : ℕ)),
          (hcomm t' k).eq, mul_assoc, mul_assoc]
    _ = nonsplitDiag F b m hm heven E basis t' * nonsplitDiag F b m hm heven E basis t *
          (nonsplitGenerator F b m hm heven E basis z hz ^ (k' : ℕ) *
            nonsplitGenerator F b m hm heven E basis z hz ^ (k : ℕ)) := by
        rw [(hdd t t').eq, ← pow_add, ← pow_add, add_comm]
    _ = _ := by
        rw [mul_assoc, ← mul_assoc (nonsplitDiag F b m hm heven E basis t),
          ← (hcomm t k').eq, mul_assoc, mul_assoc]

theorem nonsplitTorus_eq_closure :
    nonsplitTorus F b m hm heven E basis = Subgroup.closure
      (Set.range (nonsplitDiag F b m hm heven E basis) ∪
        {nonsplitGenerator F b m hm heven E basis z hz}) := by
  set S := Set.range (nonsplitDiag F b m hm heven E basis) ∪
    {nonsplitGenerator F b m hm heven E basis z hz} with hS
  apply le_antisymm
  · intro g hg
    obtain ⟨t, k, rfl⟩ := nonsplitTorus_normalForm z hz g hg
    have h1 : nonsplitDiag F b m hm heven E basis t ∈ Subgroup.closure S :=
      Subgroup.subset_closure (Or.inl ⟨t, rfl⟩)
    have h2 : nonsplitGenerator F b m hm heven E basis z hz ∈ Subgroup.closure S :=
      Subgroup.subset_closure (Or.inr rfl)
    exact (Subgroup.closure S).mul_mem h1 ((Subgroup.closure S).pow_mem h2 _)
  · rw [Subgroup.closure_le]
    rintro _ (⟨t, rfl⟩ | h)
    · exact nonsplitDiag_mem t
    · rw [Set.mem_singleton_iff] at h
      rw [h]
      exact nonsplitGenerator_mem z hz

end Torus

section Presentation

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {E : Type} [Field E] [Algebra F E] {basis : Module.Basis (Fin 2) F E}
  (z : Eˣ) (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b) (h2 : (2 : F) ≠ 0)

@[expose] noncomputable def nonsplitTorusCover :
    normOne F E × Multiplicative ℤ →* nonsplitTorus F b m hm heven E basis where
  toFun p := ⟨nonsplitDiag F b m hm heven E basis p.1 *
      nonsplitGenerator F b m hm heven E basis z hz ^ p.2.toAdd,
    (nonsplitTorus F b m hm heven E basis).mul_mem (nonsplitDiag_mem _)
      ((nonsplitTorus F b m hm heven E basis).zpow_mem (nonsplitGenerator_mem z hz) _)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' p q := by
    apply Subtype.ext
    have hcomm : Commute (nonsplitGenerator F b m hm heven E basis z hz ^ p.2.toAdd)
        (nonsplitDiag F b m hm heven E basis q.1) :=
      Commute.zpow_left (nonsplitGenerator_mul_nonsplitDiag z hz q.1) _
    simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, Subgroup.coe_mul, map_mul,
      _root_.zpow_add]
    rw [mul_assoc (nonsplitDiag F b m hm heven E basis p.1)
        (nonsplitGenerator F b m hm heven E basis z hz ^ p.2.toAdd),
      ← mul_assoc (nonsplitGenerator F b m hm heven E basis z hz ^ p.2.toAdd), hcomm.eq]
    simp only [mul_assoc]

theorem nonsplitTorusCover_apply (p : normOne F E × Multiplicative ℤ) :
    ((nonsplitTorusCover (hm := hm) (heven := heven) (basis := basis) z hz p :
      nonsplitTorus F b m hm heven E basis) : CentralExtension F b m hm heven) =
      nonsplitDiag F b m hm heven E basis p.1 *
        nonsplitGenerator F b m hm heven E basis z hz ^ p.2.toAdd := rfl

theorem nonsplitTorusCover_surjective :
    Function.Surjective (nonsplitTorusCover (hm := hm) (heven := heven) (basis := basis) z hz) := by
  rintro ⟨g, hg⟩
  obtain ⟨t, k, rfl⟩ := nonsplitTorus_normalForm z hz g hg
  refine ⟨(t, Multiplicative.ofAdd (k : ℤ)), Subtype.ext ?_⟩
  rw [nonsplitTorusCover_apply, toAdd_ofAdd, zpow_natCast]

theorem nonsplitTorusCover_ker_le {p : normOne F E × Multiplicative ℤ}
    (hp : p ∈ (nonsplitTorusCover (hm := hm) (heven := heven) (basis := basis) z hz).ker) :
    ∃ l : ℤ, p = ((cMinus F E b m h2 z hz) ^ (-l), Multiplicative.ofAdd ((m : ℤ) * l)) := by
  have : NeZero m := ⟨hm.ne'⟩
  rw [MonoidHom.mem_ker] at hp
  have hp' := congrArg Subtype.val hp
  rw [nonsplitTorusCover_apply, Subgroup.coe_one] at hp'
  have hres := congrArg (baseResidue F b m hm heven) hp'
  have hv : baseResidue F b m hm heven
      (nonsplitGenerator F b m hm heven E basis z hz ^ p.2.toAdd) =
        Multiplicative.ofAdd ((p.2.toAdd : ℤ) : ZMod m) := by
    rw [map_zpow, baseResidue_nonsplitGenerator, ← ofAdd_zsmul, zsmul_one]
  rw [map_mul, baseResidue_nonsplitDiag, one_mul, hv, map_one] at hres
  have hdvd : (m : ℤ) ∣ p.2.toAdd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp
    (congrArg Multiplicative.toAdd hres)
  obtain ⟨l, hl⟩ := hdvd
  refine ⟨l, ?_⟩
  have hv' : nonsplitGenerator F b m hm heven E basis z hz ^ p.2.toAdd =
      nonsplitDiag F b m hm heven E basis (cMinus F E b m h2 z hz) ^ l := by
    rw [hl, _root_.zpow_mul, zpow_natCast, nonsplitGenerator_pow_m z hz h2]
  rw [hv', ← map_zpow, ← map_mul] at hp'
  have hc : p.1 * cMinus F E b m h2 z hz ^ l = 1 :=
    nonsplitDiag_injective (hp'.trans (map_one _).symm)
  apply Prod.ext
  · rw [_root_.zpow_neg, eq_inv_iff_mul_eq_one]
    exact hc
  · rw [← hl]
    rfl

theorem nonsplitTorus_lift {K : Type*} [Group K] (η : normOne F E →* K) (ζ : K)
    (hcomm : ∀ t, ζ * η t = η t * ζ) (hζ : ζ ^ m = η (cMinus F E b m h2 z hz)) :
    ∃! φ : nonsplitTorus F b m hm heven E basis →* K,
      (∀ t, φ ⟨nonsplitDiag F b m hm heven E basis t, nonsplitDiag_mem t⟩ = η t) ∧
      φ ⟨nonsplitGenerator F b m hm heven E basis z hz, nonsplitGenerator_mem z hz⟩ = ζ := by
  let ψ : normOne F E × Multiplicative ℤ →* K :=
    { toFun := fun p => η p.1 * ζ ^ p.2.toAdd
      map_one' := by simp
      map_mul' := fun p q => by
        have hc : Commute (ζ ^ p.2.toAdd) (η q.1) := Commute.zpow_left (hcomm q.1) _
        simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, map_mul, _root_.zpow_add]
        rw [mul_assoc (η p.1) (ζ ^ p.2.toAdd), ← mul_assoc (ζ ^ p.2.toAdd), hc.eq]
        simp only [mul_assoc] }
  have hle : (nonsplitTorusCover (hm := hm) (heven := heven) (basis := basis) z hz).ker ≤
      ψ.ker := by
    intro p hp
    obtain ⟨l, rfl⟩ := nonsplitTorusCover_ker_le z hz h2 hp
    rw [MonoidHom.mem_ker]
    change η (cMinus F E b m h2 z hz ^ (-l)) *
      ζ ^ (Multiplicative.ofAdd ((m : ℤ) * l)).toAdd = 1
    rw [toAdd_ofAdd, _root_.zpow_mul, zpow_natCast, hζ, map_zpow, _root_.zpow_neg,
      inv_mul_cancel]
  let e := QuotientGroup.quotientKerEquivOfSurjective _
    (nonsplitTorusCover_surjective (hm := hm) (heven := heven) (basis := basis) z hz)
  let φ : nonsplitTorus F b m hm heven E basis →* K :=
    (QuotientGroup.lift _ ψ hle).comp e.symm.toMonoidHom
  have hφ : ∀ p, φ (nonsplitTorusCover z hz p) = ψ p := by
    intro p
    change QuotientGroup.lift _ ψ hle (e.symm (nonsplitTorusCover z hz p)) = ψ p
    have he : e.symm (nonsplitTorusCover z hz p) = QuotientGroup.mk p := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [he, QuotientGroup.lift_mk]
  have hdiag : ∀ t, (⟨nonsplitDiag F b m hm heven E basis t, nonsplitDiag_mem t⟩ :
      nonsplitTorus F b m hm heven E basis) = nonsplitTorusCover z hz (t, 1) := by
    intro t
    apply Subtype.ext
    rw [nonsplitTorusCover_apply]
    simp
  have hgen : (⟨nonsplitGenerator F b m hm heven E basis z hz, nonsplitGenerator_mem z hz⟩ :
      nonsplitTorus F b m hm heven E basis) =
        nonsplitTorusCover z hz (1, Multiplicative.ofAdd 1) := by
    apply Subtype.ext
    rw [nonsplitTorusCover_apply]
    simp
  refine ⟨φ, ⟨fun t => ?_, ?_⟩, ?_⟩
  · rw [hdiag, hφ]
    simp [ψ]
  · rw [hgen, hφ]
    simp [ψ]
  · rintro φ' ⟨h1, h2'⟩
    apply MonoidHom.ext
    intro g
    obtain ⟨p, rfl⟩ := nonsplitTorusCover_surjective z hz g
    rw [hφ]
    have hp : (nonsplitTorusCover z hz p : nonsplitTorus F b m hm heven E basis) =
        nonsplitTorusCover z hz (p.1, 1) *
          nonsplitTorusCover z hz (1, Multiplicative.ofAdd 1) ^ p.2.toAdd := by
      rw [← map_zpow, ← map_mul]
      congr 1
      ext
      · simp
      · simp [← ofAdd_zsmul]
    rw [hp, map_mul, map_zpow, ← hdiag, ← hgen, h1, h2']
    rfl

end Presentation

section Weyl

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {E : Type} [Field E] [Algebra F E] {basis : Module.Basis (Fin 2) F E}
  (z : Eˣ) (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b)
  (y : Eˣ) (hy : (y : E) * (y : E) ^ Nat.card F = -1) (h2 : (2 : F) ≠ 0)

theorem nonsplitWeyl_conj_normalForm (t : normOne F E) (k : ℕ) :
    nonsplitWeyl F b m hm heven E basis h2 y hy *
        (nonsplitDiag F b m hm heven E basis t *
          nonsplitGenerator F b m hm heven E basis z hz ^ k) *
        (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ =
      nonsplitDiag F b m hm heven E basis (t⁻¹ * βE F E basis z ^ k) *
        nonsplitGenerator F b m hm heven E basis z hz ^ k := by
  have hconj : nonsplitWeyl F b m hm heven E basis h2 y hy *
      (nonsplitDiag F b m hm heven E basis t *
        nonsplitGenerator F b m hm heven E basis z hz ^ k) *
      (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ =
      (nonsplitWeyl F b m hm heven E basis h2 y hy * nonsplitDiag F b m hm heven E basis t *
        (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹) *
      (nonsplitWeyl F b m hm heven E basis h2 y hy *
        nonsplitGenerator F b m hm heven E basis z hz *
          (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹) ^ k := by
    rw [conj_pow]
    group
  have hc : Commute (nonsplitDiag F b m hm heven E basis (βE F E basis z))
      (nonsplitGenerator F b m hm heven E basis z hz) :=
    (nonsplitGenerator_mul_nonsplitDiag z hz _).symm
  rw [hconj, nonsplitWeyl_conj_nonsplitDiag y hy h2,
    nonsplitWeyl_conj_nonsplitGenerator' z hz y hy h2,
    hc.mul_pow, ← mul_assoc, ← map_pow, ← map_mul]

include z hz in
theorem nonsplitWeyl_conj_mem {g : CentralExtension F b m hm heven}
    (hg : g ∈ nonsplitTorus F b m hm heven E basis) :
    nonsplitWeyl F b m hm heven E basis h2 y hy * g *
        (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ ∈ nonsplitTorus F b m hm heven E basis := by
  obtain ⟨t, k, rfl⟩ := nonsplitTorus_normalForm z hz g hg
  rw [nonsplitWeyl_conj_normalForm z hz y hy h2]
  exact (nonsplitTorus F b m hm heven E basis).mul_mem (nonsplitDiag_mem _)
    ((nonsplitTorus F b m hm heven E basis).pow_mem (nonsplitGenerator_mem z hz) _)

include z hz in
theorem nonsplitWeyl_inv_conj_mem {g : CentralExtension F b m hm heven}
    (hg : g ∈ nonsplitTorus F b m hm heven E basis) :
    (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ * g *
        nonsplitWeyl F b m hm heven E basis h2 y hy ∈ nonsplitTorus F b m hm heven E basis := by
  rw [nonsplitWeyl_inv_conj y hy h2]
  exact nonsplitWeyl_conj_mem z hz y hy h2 hg

end Weyl

end CFSG.Wreathed.CentralSL2
