module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Simple
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParDef
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SLChev
public import CFSG.Quasithin.Vol2.KGFactC31RuConcl
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertU33

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.Open CFSG.AGLEmbedding CFSG.LieType.BorelTits CFSG.Quasithin.SmithC27

theorem exists_sylow_of_isSylowTwoOf'' {X : Type} [Group X] {S : Subgroup X}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ P : Sylow 2 X, (P : Subgroup X) = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hi : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  exact ⟨hS.2.1.toSylow hi, rfl⟩

theorem simpleStmt_of_overgroups {Y : Type} [Group Y] [Finite Y] (hq : CFSG.IsQuasisimple Y)
    (hZ : Subgroup.center Y = ⊥) (hcl : IsClassicalTwoOrG2 Y)
    (hrad : IsRadicalParabolic (⊤ : Subgroup Y)) (T₀ : Sylow 2 Y)
    (hov : ∀ J : Subgroup Y, (T₀ : Subgroup Y) ≤ J →
      J = ⊤ ∨ (CFSG.QuasithinUnique.CharTwo J ∧ Group.IsSolvable ↥J)) : SimpleStmt Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro R hR
  by_cases hne : (⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y) = ⊤
  · exact ⟨leviStructure_improper hq hZ hcl hR hne, fun h => absurd hne h⟩
  have hR2 : IsPGroup 2 R := by rw [hR]; exact pCoreOf_isPGroup 2 _
  have hRbot : R ≠ ⊥ := by
    rintro rfl
    apply hne
    rw [eq_top_iff]
    intro x _
    exact ⟨trivial, Subgroup.mem_normalizer_iff.mpr fun y => by simp⟩
  obtain ⟨-, S, hS, hSN⟩ := hrad R le_top hRbot hR2 hR.symm
  obtain ⟨T, hT⟩ := exists_sylow_of_isSylowTwoOf'' hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y T T₀
  set φ : Y →* Y := (MulAut.conj g).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj g).injective
  set J : Subgroup Y := (⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y) with hJ
  have hTJ : (T : Subgroup Y) ≤ J := by
    have h1 : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J := by
      rw [hT]; simpa using hSN
    exact Subgroup.le_normalizer.trans h1
  have hT0 : (T₀ : Subgroup Y) ≤ J.map φ := by
    have : (T₀ : Subgroup Y) = (T : Subgroup Y).map φ := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    rw [this]
    exact Subgroup.map_mono hTJ
  rcases hov (J.map φ) hT0 with h1 | ⟨h1, h2⟩
  · exfalso
    apply hne
    have : J = ⊤ := by
      have h3 := congrArg (Subgroup.map (MulAut.conj g).symm.toMonoidHom) h1
      rw [Subgroup.map_map] at h3
      have h4 : ((MulAut.conj g).symm.toMonoidHom.comp φ) = MonoidHom.id Y := by
        ext x; simp [hφ]
      rw [h4, Subgroup.map_id] at h3
      rw [h3]
      exact Subgroup.map_top_of_surjective _ (MulAut.conj g).symm.surjective
    exact this
  · let e : ↥J ≃* ↥(J.map φ) := Subgroup.equivMapOfInjective J φ hφinj
    have hsolvJ : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    have hcharJ : CFSG.QuasithinUnique.CharTwo J :=
      CFSG.Quasithin.Rk2.charTwo_of_equiv e.symm h1
    have hRJ : pCoreOf 2 J = R := hR.symm
    refine ⟨⟨0, fun _ => ⊥, J, ?_, le_rfl, hsolvJ, fun i => i.elim0, fun i => i.elim0, ?_⟩, ?_⟩
    · rw [← hRJ]; exact pCoreOf_le 2 J
    · rw [iSup_of_empty, sup_bot_eq]
    · intro _ x hx
      have hxc : x ∈ Subgroup.centralizer (R : Set Y) := by
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        exact (hx g hg).symm
      have hxJ : x ∈ J := ⟨trivial, (Subgroup.centralizer_le_normalizer (R : Set Y)) hxc⟩
      have hxc' : x ∈ Subgroup.centralizer ((pCoreOf 2 J : Subgroup Y) : Set Y) := by
        rw [hRJ]; exact hxc
      have := hcharJ ⟨hxJ, hxc'⟩
      rwa [hRJ] at this

@[expose] def SylowOver (Y : Type) [Group Y] (T₀ : Subgroup Y) : Prop :=
  CFSG.QuasithinUnique.IsSylowTwoOf T₀ ⊤ ∧ ∀ J : Subgroup Y, T₀ ≤ J →
    J = ⊤ ∨ (CFSG.QuasithinUnique.CharTwo J ∧ Group.IsSolvable ↥J)

theorem simpleStmt_of_sylowOver {Y : Type} [Group Y] [Finite Y] (hq : CFSG.IsQuasisimple Y)
    (hZ : Subgroup.center Y = ⊥) (hcl : IsClassicalTwoOrG2 Y)
    (hrad : IsRadicalParabolic (⊤ : Subgroup Y)) {T₀ : Subgroup Y} (h : SylowOver Y T₀) :
    SimpleStmt Y := by
  obtain ⟨P, hP⟩ := exists_sylow_of_isSylowTwoOf'' h.1
  exact simpleStmt_of_overgroups hq hZ hcl hrad P (by rw [hP]; exact h.2)

theorem sylowOver_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    {T₀ : Subgroup S} (h : SylowOver S T₀) : SylowOver S' (T₀.map e.toMonoidHom) := by
  have hid : ∀ A : Subgroup S', (A.map e.symm.toMonoidHom).map e.toMonoidHom = A := fun A => by
    rw [Subgroup.map_map, show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id S' by
      ext y; simp, Subgroup.map_id]
  refine ⟨?_, ?_⟩
  · have := (CFSG.QuasithinUnique.Setup.Layer.isSylowTwoOf_map_mulEquiv e (X := T₀) (Y := ⊤)).2
      h.1
    rwa [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at this
  · intro J' hJ'
    have hJ : T₀ ≤ J'.map e.symm.toMonoidHom := by
      intro x hx
      exact ⟨e x, hJ' (Subgroup.mem_map_of_mem e.toMonoidHom hx), by simp⟩
    rcases h.2 _ hJ with h1 | ⟨h1, h2⟩
    · left
      have := congrArg (Subgroup.map e.toMonoidHom) h1
      rwa [hid, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at this
    · right
      let f : ↥(J'.map e.symm.toMonoidHom) ≃* ↥J' :=
        (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
          (MulEquiv.subgroupCongr (hid J'))
      exact ⟨CFSG.Quasithin.Rk2.charTwo_of_equiv f h1,
        Group.isSolvable_of_isSolvable_injective (f := f.symm.toMonoidHom) f.symm.injective⟩

open Equiv CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.L246C127 CFSG.QuasithinUnique.Bridge.Over CFSG.QuasithinUnique.Unc25K1.Six

theorem solvable_overgroups_of_latCert {n : ℕ} {A : Subgroup (Perm (Fin n))}
    (c : LatCert (Perm (Fin n))) (hM : Subgroup.closure {g | g ∈ c.mGens} = A)
    (hTA : Subgroup.closure {g | g ∈ c.tGens} ≤ A) (hc : c.check RN.enc = true)
    (hsz : ∀ s ∈ c.sizes, s = c.sizes.headD 0 ∨ s = 3 * c.sizes.headD 0 ∨ s = c.msize)
    (hT₀ : IsPGroup 2 ((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A))
    (J : Subgroup ↥A) (hTJ : (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A ≤ J) :
    J = ⊤ ∨ Group.IsSolvable ↥J := by
  subst hM
  set T₀ := (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf
    (Subgroup.closure {g | g ∈ c.mGens}) with hT₀def
  have hcl := c.closedOK_of_check hc
  have hszOK := c.sizesOK_of_check hc
  have hcardT : Nat.card T₀ = c.sizes.headD 0 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTA).toEquiv,
      c.card_t (rawIsEnc n) hcl hszOK]
  have hcardA : Nat.card ↥(Subgroup.closure {g | g ∈ c.mGens}) = c.msize :=
    c.card_m (rawIsEnc n) hcl hszOK
  have hmem : Nat.card J ∈ c.sizes := by
    obtain ⟨L, -, hLM, hYL, hL⟩ := c.overgroup_cases (rawIsEnc n) hc J hTJ
    rw [hYL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv]
    exact hL
  obtain ⟨k, hk⟩ := hT₀.exists_card_eq
  rw [hcardT] at hk
  rcases hsz _ hmem with hJ | hJ | hJ
  · right
    have : IsPGroup 2 J := IsPGroup.of_card (by rw [hJ, hk])
    have := this.isNilpotent
    infer_instance
  · right
    have : Fintype ↥J := Fintype.ofFinite _
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      Nat.prime_two Nat.prime_three (by norm_num) (a := k) (b := 1)
      (by rw [← Nat.card_eq_fintype_card, hJ, hk]; ring)
  · left
    exact Subgroup.eq_top_of_card_eq J (by rw [hJ, hcardA])

theorem sylowOver_alt_six :
    SylowOver ↥(alternatingGroup (Fin 6))
      (Even6.D.subgroupOf (alternatingGroup (Fin 6))) := by
  refine ⟨Even6.isSylow_D, fun J hJ => ?_⟩
  have hT₀ : IsPGroup 2 (Even6.D.subgroupOf (alternatingGroup (Fin 6))) :=
    Even6.isSylow_D.2.1
  rcases solvable_overgroups_of_latCert Even6.cert Even6.closure_mGens Even6.D_le
    Even6.cert_check (by decide) hT₀ J hJ with h | h
  · exact Or.inl h
  · rcases Even6.overgroups J hJ with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h', h⟩

theorem sylowOver_u33 :
    SylowOver ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup
      (CertU33.D.subgroupOf CFSG.GH74.KGroups.U33.QP.originalSubgroup) := by
  refine ⟨CertU33.isSylow_D, fun J hJ => ?_⟩
  have hT₀ : IsPGroup 2 (CertU33.D.subgroupOf CFSG.GH74.KGroups.U33.QP.originalSubgroup) :=
    CertU33.isSylow_D.2.1
  rcases solvable_overgroups_of_latCert CertU33.cert CertU33.closure_mGens CertU33.D_le
    CertU33.cert_check (by decide) hT₀ J hJ with h | h
  · exact Or.inl h
  · rcases overgroups_charTwo CertU33.cert CertU33.cts CertU33.closure_mGens CertU33.D_le
      CertU33.cert_check CertU33.members_ok J hJ with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h', h⟩

section Small


theorem simpleStmt_of_equiv_sylowOver {Y S : Type} [Group Y] [Finite Y] [Group S]
    (hcl : IsClassicalTwoOrG2 Y) (e : Y ≃* S) (hs : IsSimpleGroup S) (hq : CFSG.IsQuasisimple S)
    {T₀ : Subgroup S} (hT : SylowOver S T₀) : SimpleStmt Y := by
  have hsY : IsSimpleGroup Y := e.isSimpleGroup
  have hqY : CFSG.IsQuasisimple Y := isQuasisimple_of_mulEquiv e.symm hq
  have hZ : Subgroup.center Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hqY.2.2
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      have ha' : a' ∈ Subgroup.center Y := by rw [h1]; trivial
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp ha' b']
  have hX := CFSG.HardMathSupport.Cooperstein.StructureLie.evenLieType_or_alt_six_or_psu_of_isClassicalTwoOrG2
    hcl
  have hrad : IsRadicalParabolic (⊤ : Subgroup Y) :=
    CFSG.Quasithin.C22Pf.isRadicalParabolic_c224_holds Y hX
  exact simpleStmt_of_sylowOver hqY hZ hcl hrad (sylowOver_of_mulEquiv e.symm hT)

theorem simpleStmt_of_alt_six {Y : Type} [Group Y] [Finite Y]
    (hcl : IsClassicalTwoOrG2 Y) (h : CFSG.Quasithin.IsAlt 6 Y) : SimpleStmt Y := by
  obtain ⟨e⟩ := h
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hnc : ∃ a b : ↥(alternatingGroup (Fin 6)), a * b ≠ b * a := by
    by_contra hall
    push Not at hall
    let _ : CommGroup ↥(alternatingGroup (Fin 6)) := { (inferInstance : Group _) with mul_comm := hall }
    have hp := IsSimpleGroup.prime_card (α := ↥(alternatingGroup (Fin 6)))
    rw [Even6.card_alt] at hp
    norm_num at hp
  exact simpleStmt_of_equiv_sylowOver hcl e hs (isQuasisimple_of_simple hs hnc) sylowOver_alt_six

theorem simpleStmt_of_psu_three_three {Y : Type} [Group Y] [Finite Y]
    (hcl : IsClassicalTwoOrG2 Y) (h : CFSG.Quasithin.IsPSU 3 3 1 Y) : SimpleStmt Y := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (Or.inl ⟨by decide, h⟩)
  have hs : IsSimpleGroup Y := CFSG.Quasithin.SBc11.isSimpleGroup_of_list (Or.inr (Or.inr h))
  have hs' : IsSimpleGroup ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup := e.symm.isSimpleGroup
  have hq : CFSG.IsQuasisimple Y := CFSG.Quasithin.KGC31.isQuasisimple_of_isPSU33 h
  exact simpleStmt_of_equiv_sylowOver hcl e hs' (isQuasisimple_of_mulEquiv e hq) sylowOver_u33

end Small

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
