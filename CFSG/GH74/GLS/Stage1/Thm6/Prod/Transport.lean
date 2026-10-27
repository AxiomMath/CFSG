module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid
public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

section Transport

theorem pPrimeCore_map_normal {C : Type*} [Group C] (Y : Subgroup C) [Y.Normal] (p : ℕ) :
    ((pPrimeCore p ↥Y).map Y.subtype).Normal := by
  constructor
  rintro _ ⟨k, hk, rfl⟩ c
  refine ⟨(MulAut.conjNormal c : MulAut ↥Y) k, ?_, by simp [MulAut.conjNormal_apply]⟩
  have h : (MulAut.conjNormal c : MulAut ↥Y) k ∈
      (pPrimeCore p ↥Y).map (MulAut.conjNormal c : MulAut ↥Y).toMonoidHom := ⟨k, hk, rfl⟩
  rwa [pPrimeCore_map_iso] at h

theorem fstar_solvable_of_pcore {Γ : Type*} [Group Γ] [Finite Γ] {R : Subgroup Γ}
    (hF : generalizedFitting Γ = R)
    (hR : (pCore 2 ↥(oResidual 2 Γ)).map (oResidual 2 Γ).subtype = R) :
    Group.IsSolvable ↥(generalizedFitting Γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥R := by
    rw [← hR]
    exact (pCore_isPGroup (p := 2) (G := ↥(oResidual 2 Γ))).map _
  rw [hF]
  have := hp.isNilpotent
  infer_instance

variable {G : Type} [Group G] (z : G)

theorem toBar_surj : Function.Surjective (toBar z) := QuotientGroup.mk'_surjective _

variable [Finite G]

omit [Finite G] in
theorem LC_subgroupOf :
    (LC z).subgroupOf (Cen z) = oPrimePResidual 2 ↥(Cen z) ⊓ (InnerE z).comap (toBar z) :=
  Subgroup.comap_map_eq_self_of_injective (Cen z).subtype_injective _

omit [Finite G] in
theorem mem_LC_iff (c : ↥(Cen z)) :
    (c : G) ∈ LC z ↔ c ∈ oPrimePResidual 2 ↥(Cen z) ∧ toBar z c ∈ InnerE z := by
  have h : c ∈ (LC z).subgroupOf (Cen z) ↔ (c : G) ∈ LC z := Subgroup.mem_subgroupOf
  rw [← h, LC_subgroupOf]
  exact Iff.rfl

omit [Finite G] in
theorem LC_subgroupOf_le : (LC z).subgroupOf (Cen z) ≤ oPrimePResidual 2 ↥(Cen z) := by
  rw [LC_subgroupOf]; exact inf_le_left

omit [Finite G] in
theorem innerE_normal : (InnerE z).Normal := by
  have : (layer (CentralizerBar z)).Characteristic := CFSG.LocalCores.layer_characteristic
  have h1 : (layer (CentralizerBar z)).Normal := Subgroup.normal_of_characteristic _
  unfold InnerE
  exact Subgroup.sup_normal _ _

omit [Finite G] in
theorem layer_le_innerE : layer (CentralizerBar z) ≤ InnerE z := le_sup_left

omit [Finite G] in
theorem mem_LC_of_mem_layer {c : ↥(Cen z)} (h1 : c ∈ oPrimePResidual 2 ↥(Cen z))
    (h2 : toBar z c ∈ layer (CentralizerBar z)) : (c : G) ∈ LC z :=
  (mem_LC_iff z c).2 ⟨h1, layer_le_innerE z h2⟩

omit [Finite G] in
theorem innerE_eq_top_of_quasisimple (hq : IsQuasisimple (CentralizerBar z)) : InnerE z = ⊤ := by
  have hc : IsComponent (⊤ : Subgroup (CentralizerBar z)) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq,
      Subgroup.IsSubnormal.top⟩
  exact eq_top_iff.2 ((CFSG.LocalCores.component_le_layer hc).trans le_sup_left)

omit [Finite G] in
theorem innerE_eq_top_of_layer_eq_bot (h : layer (CentralizerBar z) = ⊥) : InnerE z = ⊤ := by
  unfold InnerE
  rw [h]
  simp

omit [Finite G] in
theorem innerE_eq_top_of_solvable (hs : Group.IsSolvable (CentralizerBar z)) : InnerE z = ⊤ := by
  refine innerE_eq_top_of_layer_eq_bot z (eq_bot_iff.2 (sSup_le fun K hK => ?_))
  by_contra hne
  have hKs : Group.IsSolvable ↥K := Group.isSolvable_of_isSolvable_injective K.subtype_injective
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  have : Group.IsPerfect ↥K := hK.1.1
  exact Group.IsPerfect.not_isSolvable ↥K hKs

omit [Finite G] in
theorem innerE_eq_top_of_fstar_solvable
    (hs : Group.IsSolvable ↥(generalizedFitting (CentralizerBar z))) : InnerE z = ⊤ := by
  refine innerE_eq_top_of_layer_eq_bot z (eq_bot_iff.2 (sSup_le fun K hK => ?_))
  by_contra hne
  have hKF : K ≤ generalizedFitting (CentralizerBar z) :=
    (CFSG.LocalCores.component_le_layer hK).trans le_sup_right
  have hKs : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKF)
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  have : Group.IsPerfect ↥K := hK.1.1
  exact Group.IsPerfect.not_isSolvable ↥K hKs

theorem LBar_eq : LBar z = oPrimePResidual 2 (CentralizerBar z) ⊓ InnerE z := by
  have hO := map_oPrimePResidual (toBar z) (toBar_surj z) Nat.prime_two
  apply le_antisymm
  · unfold LBar barOf
    rw [LC_subgroupOf, Subgroup.map_le_iff_le_comap]
    intro c hc
    refine Subgroup.mem_inf.2 ⟨?_, hc.2⟩
    rw [← hO]
    exact ⟨c, hc.1, rfl⟩
  · rintro y ⟨hy1, hy2⟩
    rw [← hO] at hy1
    obtain ⟨c, hc, rfl⟩ := hy1
    unfold LBar barOf
    rw [LC_subgroupOf]
    exact ⟨c, ⟨hc, hy2⟩, rfl⟩

theorem LBar_eq_of_le (hI : oPrimePResidual 2 (CentralizerBar z) ≤ InnerE z) :
    LBar z = oPrimePResidual 2 (CentralizerBar z) := by
  rw [LBar_eq, inf_eq_left.2 hI]

theorem LBar_eq_oResidual (h : oPrimeResidual 2 (CentralizerBar z) = ⊤)
    (hI : oPrimePResidual 2 (CentralizerBar z) ≤ InnerE z) :
    LBar z = oResidual 2 (CentralizerBar z) := by
  rw [LBar_eq_of_le z hI]; exact oPrimePResidual_eq_oResidual Nat.prime_two h

theorem LC_normal : ((LC z).subgroupOf (Cen z)).Normal := by
  have h1 : (oPrimePResidual 2 ↥(Cen z)).Normal := oPrimePResidual_normal Nat.prime_two _
  have h2 : ((InnerE z).comap (toBar z)).Normal := (innerE_normal z).comap _
  rw [LC_subgroupOf]
  exact Subgroup.normal_inf_normal _ _

theorem LBar_isNormal : (LBar z).Normal := by
  have := LC_normal z
  unfold LBar barOf
  exact Subgroup.Normal.map inferInstance (toBar z) (toBar_surj z)

theorem mem_LC_iff_of_pElt (g : ↥(Cen z)) {k : ℕ} (hg : g ^ (2 ^ k) = 1) :
    (g : G) ∈ LC z ↔ toBar z g ∈ LBar z := by
  have hLn : (oPrimePResidual 2 ↥(Cen z)).Normal := oPrimePResidual_normal Nat.prime_two _
  have hO := map_oPrimePResidual (toBar z) (toBar_surj z) Nat.prime_two
  rw [mem_LC_iff, LBar_eq, Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [← hO]
    exact ⟨g, h1, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← hO] at h1
    exact ⟨two_elt_mem_of_map_mem (pPrimeCore 2 ↥(Cen z)) (oPrimePResidual 2 ↥(Cen z))
      pPrimeCore_coprime_card hg h1, h2⟩

@[expose] noncomputable def psiZ :
    ↥(oResidual 2 ↥(Cen z)) →* ↥(oResidual 2 (CentralizerBar z)) :=
  ((toBar z).comp (oResidual 2 ↥(Cen z)).subtype).codRestrict (oResidual 2 (CentralizerBar z))
    (fun y => by
      rw [← map_oResidual (toBar z) (toBar_surj z) Nat.prime_two]
      exact ⟨y, y.2, rfl⟩)

theorem psiZ_coe (y : ↥(oResidual 2 ↥(Cen z))) :
    ((psiZ z y : ↥(oResidual 2 (CentralizerBar z))) : CentralizerBar z) = toBar z (y : ↥(Cen z)) :=
  rfl

theorem psiZ_surj : Function.Surjective (psiZ z) := by
  rintro ⟨yb, hyb⟩
  rw [← map_oResidual (toBar z) (toBar_surj z) Nat.prime_two] at hyb
  obtain ⟨y, hy, rfl⟩ := hyb
  exact ⟨⟨y, hy⟩, rfl⟩

theorem psiZ_eq_one (y : ↥(oResidual 2 ↥(Cen z))) :
    psiZ z y = 1 ↔ (y : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) := by
  constructor
  · intro h
    have : toBar z (y : ↥(Cen z)) = 1 := congrArg Subtype.val h
    exact (QuotientGroup.eq_one_iff _).1 this
  · intro h
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).2 h

theorem oddCore_le_oResidual : pPrimeCore 2 ↥(Cen z) ≤ oResidual 2 ↥(Cen z) := by
  intro n hn
  apply Subgroup.subset_closure
  show Nat.Coprime (orderOf n) 2
  have h1 := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 ↥(Cen z)) hn
  have : orderOf n ∣ Nat.card (pPrimeCore 2 ↥(Cen z)) := by simpa [Subgroup.orderOf_coe] using h1
  exact Nat.Coprime.coprime_dvd_left this (pPrimeCore_coprime_card).symm

theorem psiZ_ker : (psiZ z).ker = pPrimeCore 2 ↥(oResidual 2 ↥(Cen z)) := by
  have : (oResidual 2 ↥(Cen z)).Normal := oResidual_normal 2 _
  apply le_antisymm
  · apply le_sSup
    refine ⟨inferInstance, ?_⟩
    let f : (psiZ z).ker →* ↥(pPrimeCore 2 ↥(Cen z)) :=
      ((oResidual 2 ↥(Cen z)).subtype.comp (psiZ z).ker.subtype).codRestrict
        (pPrimeCore 2 ↥(Cen z)) (fun y => (psiZ_eq_one z y.1).1 y.2)
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun t => ((t : ↥(pPrimeCore 2 ↥(Cen z))) : ↥(Cen z))) hab
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_injective f hf)
      pPrimeCore_coprime_card
  · intro y hy
    have hK : (pPrimeCore 2 ↥(oResidual 2 ↥(Cen z))).map (oResidual 2 ↥(Cen z)).subtype ≤
        pPrimeCore 2 ↥(Cen z) := by
      apply le_sSup
      refine ⟨pPrimeCore_map_normal (oResidual 2 ↥(Cen z)) 2, ?_⟩
      rw [Subgroup.card_map_of_injective (oResidual 2 ↥(Cen z)).subtype_injective]
      exact pPrimeCore_coprime_card
    exact (psiZ_eq_one z y).2 (hK ⟨y, hy, rfl⟩)

theorem pPrimePCore_eq_comap :
    pPrimePCore 2 ↥(oResidual 2 ↥(Cen z)) =
      (pCore 2 ↥(oResidual 2 (CentralizerBar z))).comap (psiZ z) := by
  let Y : Subgroup ↥(Cen z) := oResidual 2 ↥(Cen z)
  let Yb : Subgroup (CentralizerBar z) := oResidual 2 (CentralizerBar z)
  have hker := psiZ_ker z
  let e : (↥Y ⧸ pPrimeCore 2 ↥Y) ≃* ↥Yb :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (psiZ z) (psiZ_surj z))
  have hcore := pCore_map_iso 2 e
  have hψe : psiZ z = e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥Y)) := by
    ext y; rfl
  unfold pPrimePCore
  rw [hψe, ← Subgroup.comap_comap, ← hcore, Subgroup.comap_map_eq_self_of_injective e.injective]

theorem WBar_eq :
    WBar z = (pCore 2 ↥(oResidual 2 (CentralizerBar z))).map
      (oResidual 2 (CentralizerBar z)).subtype := by
  have hsub : (WC z).subgroupOf (Cen z) =
      (pPrimePCore 2 ↥(oResidual 2 ↥(Cen z))).map (oResidual 2 ↥(Cen z)).subtype :=
    Subgroup.comap_map_eq_self_of_injective (Cen z).subtype_injective _
  have hW0 : (pPrimePCore 2 ↥(oResidual 2 ↥(Cen z))).map (psiZ z) =
      pCore 2 ↥(oResidual 2 (CentralizerBar z)) := by
    rw [pPrimePCore_eq_comap, Subgroup.map_comap_eq_self_of_surjective (psiZ_surj z)]
  unfold WBar barOf
  rw [hsub, Subgroup.map_map]
  have hcomm : (toBar z).comp (oResidual 2 ↥(Cen z)).subtype =
      (oResidual 2 (CentralizerBar z)).subtype.comp (psiZ z) := by ext y; rfl
  rw [hcomm, ← Subgroup.map_map, hW0]

theorem oddCore_le_WC : pPrimeCore 2 ↥(Cen z) ≤ (WC z).subgroupOf (Cen z) := by
  intro n hn
  have hY := oddCore_le_oResidual z hn
  have : (⟨n, hY⟩ : ↥(oResidual 2 ↥(Cen z))) ∈ pPrimePCore 2 ↥(oResidual 2 ↥(Cen z)) := by
    rw [pPrimePCore_eq_comap]
    show psiZ z ⟨n, hY⟩ ∈ pCore 2 ↥(oResidual 2 (CentralizerBar z))
    rw [(psiZ_eq_one z _).2 hn]
    exact Subgroup.one_mem _
  have hsub : (WC z).subgroupOf (Cen z) =
      (pPrimePCore 2 ↥(oResidual 2 ↥(Cen z))).map (oResidual 2 ↥(Cen z)).subtype :=
    Subgroup.comap_map_eq_self_of_injective (Cen z).subtype_injective _
  rw [hsub]
  exact ⟨_, this, rfl⟩

theorem mem_WC_iff (g : ↥(Cen z)) : (g : G) ∈ WC z ↔ toBar z g ∈ WBar z := by
  have hmem : (g : G) ∈ WC z ↔ g ∈ (WC z).subgroupOf (Cen z) := Iff.rfl
  rw [hmem]
  constructor
  · intro h
    exact ⟨g, h, rfl⟩
  · intro h
    obtain ⟨w, hw, hwg⟩ := h
    have hn : w⁻¹ * g ∈ pPrimeCore 2 ↥(Cen z) := by
      apply (QuotientGroup.eq_one_iff _).1
      show toBar z (w⁻¹ * g) = 1
      rw [map_mul, map_inv, hwg, inv_mul_cancel]
    have : g = w * (w⁻¹ * g) := by group
    rw [this]
    exact Subgroup.mul_mem _ hw (oddCore_le_WC z hn)

end Transport

end CFSG.GH74.GLS.Stage1.Thm6.Prod
