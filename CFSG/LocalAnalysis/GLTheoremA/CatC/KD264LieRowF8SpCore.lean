module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1SpGroup
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8LnModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Sp

open CFSG.Open Module CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Ln

theorem alt6_facts : CFSG.Open.IsQuasisimple (alternatingGroup (Fin 6)) ∧
    3 ∣ Nat.card (alternatingGroup (Fin 6) ⧸ Subgroup.center (alternatingGroup (Fin 6))) := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hcen : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hperf : commutator (alternatingGroup (Fin 6)) = ⊤ :=
    commutator_alternatingGroup_eq_top (by simp)
  refine ⟨⟨hperf, ?_⟩, ?_⟩
  · exact ((QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientBot (G := alternatingGroup (Fin 6)))).isSimpleGroup
  · rw [hcen]
    have h1 : Nat.card (alternatingGroup (Fin 6) ⧸ (⊥ : Subgroup (alternatingGroup (Fin 6)))) =
        Nat.card (alternatingGroup (Fin 6)) :=
      Nat.card_congr (QuotientGroup.quotientBot (G := alternatingGroup (Fin 6))).toEquiv
    rw [h1, nat_card_alternatingGroup]
    simp [Nat.card_eq_fintype_card, Nat.factorial]

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem sp_core_c (f : LinearMap.BilinForm (ZMod 2) W) (hfalt : f.IsAlt)
    (hfnd : f.Nondegenerate) (hdim : Module.finrank (ZMod 2) W = 2 * 3)
    (E' : Subgroup ↥(TauCeti.BilinForm.isometryGroup f)) [Fintype E']
    (hE' : IsElemAbelian 3 E') (hcard : 3 ^ 3 ≤ Fintype.card E') :
    ∃ c ∈ E', c ≠ 1 ∧ ∃ L' : Subgroup ↥(TauCeti.BilinForm.isometryGroup f),
      L' ≤ Subgroup.centralizer ({c} : Set ↥(TauCeti.BilinForm.isometryGroup f)) ∧
      CFSG.Open.IsSubnormal L'
        (Subgroup.centralizer ({c} : Set ↥(TauCeti.BilinForm.isometryGroup f))) ∧
      CFSG.Open.IsQuasisimple ↥L' ∧ 3 ∣ Nat.card (↥L' ⧸ Subgroup.center ↥L') := by
  classical
  let EΓ : Subgroup (W ≃ₗ[ZMod 2] W) := E'.map (TauCeti.BilinForm.isometryGroup f).subtype
  haveI : Fintype EΓ := Fintype.ofFinite _
  have hEΓ : IsElemAbelian 3 EΓ :=
    X1Sp.isElemAbelian_map_hom 3 (TauCeti.BilinForm.isometryGroup f).subtype hE'
  have hcardΓ' : Fintype.card EΓ = Fintype.card E' :=
    (Fintype.card_congr (Subgroup.equivMapOfInjective E'
      (TauCeti.BilinForm.isometryGroup f).subtype Subtype.val_injective).toEquiv).symm
  have hle : Fintype.card EΓ ≤ 3 ^ 3 := by
    have := card_le_three_pow_half EΓ hEΓ
    rw [hdim] at this
    simpa using this
  have hcardΓ : Fintype.card EΓ = 3 ^ 3 := le_antisymm hle (hcardΓ' ▸ hcard)
  have hGmem : ∀ g ∈ EΓ, g ∈ TauCeti.BilinForm.isometryGroup f := by
    intro g hg
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hg
    exact y.2
  have hEf : ∀ g ∈ EΓ, ∀ x y, f (g x) (g y) = f x y := by
    intro g hg x y
    exact (TauCeti.BilinForm.mem_isometryGroup_iff.1 (hGmem g hg)) x y
  obtain ⟨X, ρ, hdim2, hind, hsup, hinv, hmem, hcyc, hfix, hpow, hsep⟩ :=
    sp_struct EΓ hEΓ 3 hdim hcardΓ
  choose e heE hact using hsep
  let D : PlaneData EΓ 3 :=
    { X := X, ρ := ρ, e := e, dim2 := hdim2, indep := hind, sup_eq := hsup, inv := hinv,
      memE := hmem, cyc := hcyc, fixfree := hfix, pow := hpow, emem := heE, eact := hact }
  have hn2 : 2 ≤ 3 := by norm_num
  have hSub : CFSG.Open.IsSubnormal (D.Lg f hn2) (D.Cg f) :=
    D.isSubnormal_Lg_Cg f hEf hfalt hfnd hEΓ hn2
  have hIso := D.Lg_iso_alt f hEf hfalt hfnd hn2
  have hCG : D.Cg f ≤ TauCeti.BilinForm.isometryGroup f := inf_le_right
  have hLG : D.Lg f hn2 ≤ TauCeti.BilinForm.isometryGroup f :=
    le_trans (le_trans (Subgroup.map_le_range _ _) (D.Hg_le_Cg f hEf hfalt hn2)) hCG
  let i2 : Fin 3 := ⟨2, by norm_num⟩
  have hi2 : 2 ≤ i2.val := le_rfl
  let c : ↥(TauCeti.BilinForm.isometryGroup f) := ⟨e i2, hGmem _ (heE i2)⟩
  have hcE : c ∈ E' := by
    have hmemΓ : e i2 ∈ EΓ := heE i2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hmemΓ
    have : y = c := Subtype.ext hyx
    rw [← this]
    exact hy
  have hc1 : c ≠ 1 := by
    intro h1
    have h2 : D.e i2 = 1 := congrArg Subtype.val h1
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := D.X i2) (by
      intro h0
      have := D.dim2 i2
      rw [h0, finrank_bot] at this
      omega)
    have h3 : D.e i2 x = D.ρ i2 x := by
      rw [D.eact i2 i2 x hx, if_pos rfl]
    rw [h2] at h3
    exact hx0 (D.fixfree i2 x hx (by rw [← h3]; rfl))
  have hfixU : ∀ h ∈ D.fixU, ∃ k : ℕ, h = D.e i2 ^ k := by
    intro h hh
    obtain ⟨k, hk⟩ := D.pow i2 h hh.1
    refine ⟨(k : ℕ), LinearEquiv.ext fun v => ?_⟩
    have hv : v ∈ ⨆ i, D.X i := by rw [D.sup_eq]; trivial
    refine Submodule.iSup_induction D.X (motive := fun v => h v = (D.e i2 ^ (k : ℕ)) v) hv ?_ ?_ ?_
    · intro j x hx
      by_cases hj : j = i2
      · rw [hj] at hx
        rw [hk x hx, D.ea_pow_plane i2 (k : ℕ) x hx]
      · have hjlo : j ∈ idxLo 3 := by
          show j.val < 2
          have hj3 := j.isLt
          have : j.val ≠ 2 := fun h' => hj (Fin.ext h')
          omega
        have hxU : x ∈ D.piecesOf (idxLo 3) := le_biSup D.X hjlo hx
        rw [hh.2 x hxU, D.ea_trivial j i2 hj (k : ℕ) x hx]
    · simp
    · intro x y hx hy
      rw [map_add, map_add, hx, hy]
  have hcent : Subgroup.centralizer ({c} : Set ↥(TauCeti.BilinForm.isometryGroup f)) =
      (D.Cg f).subgroupOf (TauCeti.BilinForm.isometryGroup f) := by
    ext x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hxe : e i2 * (x : W ≃ₗ[ZMod 2] W) = (x : W ≃ₗ[ZMod 2] W) * e i2 :=
        congrArg Subtype.val (hx c (Set.mem_singleton _))
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 (fun h hh => ?_), x.2⟩
      obtain ⟨k, rfl⟩ := hfixU h hh
      exact (Commute.pow_left (hxe : Commute (e i2) (x : W ≃ₗ[ZMod 2] W)) k).eq
    · intro hx y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      apply Subtype.ext
      have := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).1) (e i2) (D.e_mem_fixU i2 hi2)
      exact this
  have hSub' := X1Sp.Gen.isSubnormal_subgroupOf (TauCeti.BilinForm.isometryGroup f) hSub hCG
  rw [← hcent] at hSub'
  obtain ⟨ι⟩ := hIso
  obtain ⟨hq6, hd6⟩ := alt6_facts
  have hLiso : ↥((D.Lg f hn2).subgroupOf (TauCeti.BilinForm.isometryGroup f)) ≃*
      alternatingGroup (Fin 6) := (Subgroup.subgroupOfEquivOfLe hLG).trans ι
  refine ⟨c, hcE, hc1, (D.Lg f hn2).subgroupOf (TauCeti.BilinForm.isometryGroup f), ?_, hSub',
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv hLiso.symm hq6, ?_⟩
  ·
    exact X1Sp.Gen.isSubnormal_le hSub'
  · rw [card_quotient_center_of_equiv hLiso]
    exact hd6

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Sp

end
