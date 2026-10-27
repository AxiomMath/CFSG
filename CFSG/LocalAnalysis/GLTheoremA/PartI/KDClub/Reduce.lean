module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1411
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510
public import CFSG.LocalAnalysis.GLTheoremA.Pump

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns

@[expose] def KDClubAt (S : Type) [Group S] : Prop :=
  ∀ α : MulAut S, α ≠ 1 → α ^ 3 = 1 → ∀ J : Subgroup S, GLAPComponent 3 (fixSub α) J →
    Nat.card (Subgroup.center (PQuot 3 J)) = 1 ∧ catalogIs (PSimple 3 J) clubIndex

private noncomputable def kdrQuotEquiv {S S' : Type} [Group S] [Group S'] (p : ℕ) (e : S ≃* S')
    (X : Subgroup S) :
    (↥X ⧸ GLAPPrimeCore p ↥X) ≃*
      (↥(X.map e.toMonoidHom) ⧸ GLAPPrimeCore p ↥(X.map e.toMonoidHom)) :=
  QuotientGroup.congr _ _ (X.equivMapOfInjective e.toMonoidHom e.injective)
    (glaPPrimeCore_map_iso p (X.equivMapOfInjective e.toMonoidHom e.injective))

private theorem kdr_map_subgroupOf {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (X K : Subgroup S) :
    (K.subgroupOf X).map (X.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom =
      (K.map e.toMonoidHom).subgroupOf (X.map e.toMonoidHom) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact ⟨x.1, Subgroup.mem_subgroupOf.1 hx, rfl⟩
  · intro hy
    rw [Subgroup.mem_subgroupOf] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    obtain ⟨w, hwX, hwy⟩ := y.2
    have hzw : z = w := e.injective (hzy.trans hwy.symm)
    have hzX : z ∈ X := by
      rw [hzw]
      exact hwX
    exact ⟨⟨z, hzX⟩, Subgroup.mem_subgroupOf.2 hz, Subtype.ext hzy⟩

private theorem kdr_barX_quotEquiv {S S' : Type} [Group S] [Group S'] (p : ℕ) (e : S ≃* S')
    (X K : Subgroup S) :
    ((K.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).map
        (kdrQuotEquiv p e X).toMonoidHom =
      ((K.map e.toMonoidHom).subgroupOf (X.map e.toMonoidHom)).map
        (QuotientGroup.mk' (GLAPPrimeCore p ↥(X.map e.toMonoidHom))) := by
  have hcomm : (kdrQuotEquiv p e X).toMonoidHom.comp (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) =
      (QuotientGroup.mk' (GLAPPrimeCore p ↥(X.map e.toMonoidHom))).comp
        (X.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    rfl
  rw [Subgroup.map_map, hcomm, ← Subgroup.map_map, kdr_map_subgroupOf]

private theorem kdr_map_map_symm {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (K : Subgroup S) : (K.map e.toMonoidHom).map e.symm.toMonoidHom = K := by
  rw [Subgroup.map_map]
  have h : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id S := by
    ext x
    simp
  rw [h, Subgroup.map_id]

private theorem kdr_map_symm_map {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (K : Subgroup S') : (K.map e.symm.toMonoidHom).map e.toMonoidHom = K := by
  rw [Subgroup.map_map]
  have h : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id S' := by
    ext x
    simp
  rw [h, Subgroup.map_id]

private theorem kdr_glaPComponent_map {S S' : Type} [Group S] [Group S'] {p : ℕ} (e : S ≃* S')
    {X L : Subgroup S} (h : GLAPComponent p X L) :
    GLAPComponent p (X.map e.toMonoidHom) (L.map e.toMonoidHom) := by
  obtain ⟨hLX, hsn, hcomp, hmin⟩ := h
  refine ⟨Subgroup.map_mono hLX, CFSG.SignalizerFunctorTheorem.TransportA.isSubnormal_map e hsn,
    ?_, ?_⟩
  · have h1 : IsComponentOf
        (((L.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).map
          (kdrQuotEquiv p e X).toMonoidHom)
        ((⊤ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)).map (kdrQuotEquiv p e X).toMonoidHom) :=
      CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map (kdrQuotEquiv p e X) hcomp
    have htop : Subgroup.map (kdrQuotEquiv p e X).toMonoidHom
        (⊤ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) = ⊤ :=
      Subgroup.map_top_of_surjective _ (kdrQuotEquiv p e X).surjective
    rw [htop, kdr_barX_quotEquiv] at h1
    exact h1
  · intro J' hJ' hJ'sn heq
    have hJe : (J'.map e.symm.toMonoidHom).map e.toMonoidHom = J' := kdr_map_symm_map e J'
    have hJL : J'.map e.symm.toMonoidHom < L := by
      refine lt_of_le_of_ne ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        obtain ⟨l, hl, hly⟩ := hJ'.le hy
        rw [← hly]
        simpa using hl
      · intro hEq
        apply hJ'.ne
        rw [← hJe, hEq]
    have hJsn : IsSubnormal (J'.map e.symm.toMonoidHom) X := by
      have h2 : IsSubnormal (J'.map e.symm.toMonoidHom)
          ((X.map e.toMonoidHom).map e.symm.toMonoidHom) :=
        CFSG.SignalizerFunctorTheorem.TransportA.isSubnormal_map e.symm hJ'sn
      rwa [kdr_map_map_symm e X] at h2
    refine hmin _ hJL hJsn ?_
    apply Subgroup.map_injective (f := (kdrQuotEquiv p e X).toMonoidHom)
      (kdrQuotEquiv p e X).injective
    rw [kdr_barX_quotEquiv, kdr_barX_quotEquiv, hJe]
    exact heq

theorem kdClubAt_congr {S S' : Type} [Group S] [Group S'] (e : S ≃* S') (h : KDClubAt S) :
    KDClubAt S' := by
  intro α' hα'1 hα'3 J' hJ'
  have hα1 : MulAut.congr e.symm α' ≠ 1 := by
    intro h1
    apply hα'1
    apply (MulAut.congr e.symm).injective
    exact h1.trans (map_one _).symm
  have hα3 : (MulAut.congr e.symm α') ^ 3 = 1 := by
    have h3 := map_pow (MulAut.congr e.symm) α' 3
    rw [hα'3, map_one] at h3
    exact h3.symm
  have hfix : fixSub (MulAut.congr e.symm α') = (fixSub α').map e.symm.toMonoidHom := by
    ext x
    rw [mem_fixSub, Subgroup.mem_map]
    constructor
    · intro hx
      have hx' : e.symm (α' (e x)) = x := hx
      have hfixed : α' (e x) = e x := by
        have h4 := congrArg e hx'
        simpa using h4
      exact ⟨e x, mem_fixSub.2 hfixed, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      rw [mem_fixSub] at hy
      show e.symm (α' (e (e.symm y))) = e.symm y
      simp [hy]
  have hJ : GLAPComponent 3 (fixSub (MulAut.congr e.symm α')) (J'.map e.symm.toMonoidHom) := by
    rw [hfix]
    exact kdr_glaPComponent_map e.symm hJ'
  obtain ⟨c, cat⟩ := h (MulAut.congr e.symm α') hα1 hα3 _ hJ
  exact (clubData_congr (kdrQuotEquiv 3 e.symm J').symm).1 ⟨c, cat⟩

theorem kdClub_of_at (h : ∀ i : TauCeti.CFSGIndex, clubIndex i → KDClubAt i.Group) : KDClub := by
  intro Y _ _ K hK y hyN hy3 hnC J hJ
  obtain ⟨i, hi, ⟨eK⟩⟩ := hK
  have hKat : KDClubAt ↥K := kdClubAt_congr eK.symm (h i hi)
  have hJX : J ≤ K ⊓ Subgroup.centralizer ({y} : Set Y) := hJ.1
  have hJK : J ≤ K := hJX.trans inf_le_left
  obtain ⟨β, hβdef⟩ : ∃ β : MulAut ↥K, β = Subgroup.normalizerMonoidHom K ⟨y, hyN⟩ :=
    ⟨_, rfl⟩
  have hβapp : ∀ k : ↥K, ((β k : ↥K) : Y) = y * (k : Y) * y⁻¹ := by
    intro k
    rw [hβdef]
    rfl
  have hβ3 : β ^ 3 = 1 := by
    have h3 : (⟨y, hyN⟩ : Subgroup.normalizer (K : Set Y)) ^ 3 = 1 := Subtype.ext hy3
    rw [hβdef, ← map_pow, h3, map_one]
  have hβ1 : β ≠ 1 := by
    intro h1
    apply hnC
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk' : y * k * y⁻¹ = k := by
      have h2 := hβapp ⟨k, hk⟩
      rw [h1, MulAut.one_apply] at h2
      exact h2.symm
    exact (mul_inv_eq_iff_eq_mul.1 hk').symm
  have hfix : fixSub β = (K ⊓ Subgroup.centralizer ({y} : Set Y)).subgroupOf K := by
    ext k
    rw [mem_fixSub, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hk
      have h1 : ((β k : ↥K) : Y) = (k : Y) := congrArg Subtype.val hk
      rw [hβapp] at h1
      exact ⟨k.2, (mul_inv_eq_iff_eq_mul.1 h1).symm⟩
    · rintro ⟨-, hk⟩
      apply Subtype.ext
      rw [hβapp]
      exact mul_inv_eq_iff_eq_mul.2 hk.symm
  have hJ' : GLAPComponent 3 (fixSub β) (J.subgroupOf K) := by
    rw [hfix]
    exact glaPComponent_subgroupOf Nat.prime_three inf_le_left hJ
  obtain ⟨c, cat⟩ := hKat β hβ1 hβ3 (J.subgroupOf K) hJ'
  obtain ⟨eJ⟩ := nonempty_pQuot_equiv_subgroupOf 3 hJK
  exact (clubData_congr eJ).1 ⟨c, cat⟩

theorem kdClubAt_of_solvable {S : Type} [Group S] [Finite S]
    (h : ∀ α : MulAut S, α ≠ 1 → α ^ 3 = 1 → IsSolvable ↥(fixSub α)) : KDClubAt S := by
  intro α hα1 hα3 J hJ
  exfalso
  have hsolv : Group.IsSolvable ↥(fixSub α) := h α hα1 hα3
  have hJX : J ≤ fixSub α := hJ.1
  have hperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have hne : J ≠ ⊥ := glaPComponent_ne_bot' hJ
  have hJ'ne : J.subgroupOf (fixSub α) ≠ ⊥ := by
    intro h0
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hJX, h0, Subgroup.map_bot]
  have hlt : ⁅J.subgroupOf (fixSub α), J.subgroupOf (fixSub α)⁆ < J.subgroupOf (fixSub α) :=
    Group.IsSolvable.commutator_lt_of_ne_bot hJ'ne
  have heq : ⁅J.subgroupOf (fixSub α), J.subgroupOf (fixSub α)⁆ = J.subgroupOf (fixSub α) := by
    apply Subgroup.map_injective (f := (fixSub α).subtype) (fixSub α).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJX]
    exact hperf
  rw [heq] at hlt
  exact lt_irrefl _ hlt

end CFSG.LocalAnalysis.GLTheoremA
