module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeReeF4LargeRFInner
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitBasic
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcLiftY

public section

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Open

namespace CFSG.LocalAnalysis.GLTheoremA.F151


theorem isComponentOf_of_glaPComponent_reeF4 (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (x : S) (hx : orderOf x = p) {J : Subgroup S}
    (hJ : GLAPComponent p (Subgroup.centralizer ({x} : Set S)) J) :
    CFSG.Open.IsComponentOf J (Subgroup.centralizer ({x} : Set S)) := by
  have hfix := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.fixSubgroup_conj_eq x
  have hβp : (MulAut.conj x) ^ p = 1 := by
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hβ1 : MulAut.conj x ≠ 1 := by
    intro h
    have hxc : x ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : x * g * x⁻¹ = g := by
        have := congrArg (fun φ : MulAut S => φ g) h
        simpa [MulAut.conj_apply] using this
      calc g * x = x * g * x⁻¹ * x := by rw [h1]
        _ = x * g := by group
    rcases (Subgroup.center S).normal_of_characteristic.eq_bot_or_eq_top with hb | ht
    · rw [hb, Subgroup.mem_bot] at hxc
      rw [hxc, orderOf_one] at hx
      exact hp.one_lt.ne hx
    · obtain ⟨a, b, hab⟩ := hnc
      have ha : a ∈ Subgroup.center S := ht ▸ Subgroup.mem_top a
      exact hab ((Subgroup.mem_center_iff.1 ha b).symm)
  have hPL := CFSG.HardMathSupport.Dickson.SuzukiReeB.perfectInLayer_reeF4 m hv hnc ⟨eS⟩ hp hp2
    hβp hβ1
  rw [← hfix] at hJ
  have hperf := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.glaPComponent_perfect hJ
  have hle := hPL J hJ.1 hperf
  have hcomp :=
    (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJ hle).1
  rwa [hfix] at hcomp

theorem inner_of_glaPComponent_reeF4_of_three_lt (m : ℕ)
    (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (x : S) (hx : orderOf x = p) {J : Subgroup S}
    (hJ : GLAPComponent p (Subgroup.centralizer ({x} : Set S)) J)
    (c : S) (hc : c ∈ Subgroup.centralizer ({x} : Set S)) :
    ∃ n ∈ J, ∀ y ∈ J, c * y * c⁻¹ = n * y * n⁻¹ := by
  have hD0 := isComponentOf_of_glaPComponent_reeF4 m hv hnc eS hp (by omega) x hx hJ
  have hD : CFSG.RankThree.PartOne.IsComponentOf (Subgroup.centralizer ({x} : Set S)) J :=
    ⟨hD0.1, CFSG.HardMathSupport.Solomon.Coordinator.i183v_isQuasisimple hD0.2.2,
      (CFSG.Open.IsSubnormal.iff_subgroupOf hD0.1).1 hD0.2.1⟩
  have hm1 : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hR := CFSG.LieType.SeitzGeneration.reeTitsModel_cat_reeF4 hv
  obtain ⟨K, hfield, hfinite, hchar, hKcard, ⟨eK⟩⟩ :=
    CFSG.LieType.ChevTwo.Semi.exists_mulEquiv_reeGamma hm1 hR
  letI := hfield
  letI := hfinite
  haveI : CharP K ReeTag.F4.prime := hchar
  let e : S ≃* ↥(ReeTag.F4.reeGamma K m) := eS.trans eK
  letI : Finite ↥(ReeTag.F4.reeGamma K m) := Subtype.finite
  have hX : orderOf (e x) = p :=
    (orderOf_injective e.toMonoidHom e.injective x).trans hx
  obtain ⟨N, hNle, -, huniq, hNcomp⟩ :=
    CFSG.RankThree.PartOne.TCF.largeRee_component_data hm1 hKcard hp hp3 (e x) hX
  have hD' : CFSG.RankThree.PartOne.IsComponentOf
      (Subgroup.centralizer ({e x} : Set ↥(ReeTag.F4.reeGamma K m))) (J.map e.toMonoidHom) := by
    have h := CFSG.RankThree.PartOne.isComponentOf_map_mulEquiv e hD
    rwa [CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e x] at h
  have hJN : J.map e.toMonoidHom = N := huniq _ hD'
  have hc' : e c ∈ Subgroup.centralizer ({e x} : Set ↥(ReeTag.F4.reeGamma K m)) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    simpa using congrArg e hc
  obtain ⟨n', hn', hact⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.inner_of_reeGamma hm1 hKcard hp hp3 (e x) hX N hNle
      huniq hNcomp (e c) hc'
  rw [← hJN] at hn' hact
  obtain ⟨n, hn, hne⟩ := Subgroup.mem_map.mp hn'
  refine ⟨n, hn, fun y hy => ?_⟩
  apply e.injective
  have h := hact (e y) (Subgroup.mem_map_of_mem _ hy)
  rw [← hne] at h
  simpa using h

theorem inner_of_glaPComponent_reeF4_three (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group)
    (x : S) (hx : orderOf x = 3) {J : Subgroup S}
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({x} : Set S)) J)
    (c : S) (hc : c ∈ Subgroup.centralizer ({x} : Set S)) :
    ∃ n ∈ J, ∀ y ∈ J, c * y * c⁻¹ = n * y * n⁻¹ := by
  have hD0 := isComponentOf_of_glaPComponent_reeF4 m hv hnc eS Nat.prime_three (by omega) x hx hJ
  have hm1 : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hR := CFSG.LieType.SeitzGeneration.reeTitsModel_cat_reeF4 hv
  obtain ⟨K, hfield, hfinite, hchar, hKcard, ⟨eK⟩⟩ :=
    CFSG.LieType.ChevTwo.Semi.exists_mulEquiv_reeGamma hm1 hR
  letI := hfield
  letI := hfinite
  haveI : CharP K ReeTag.F4.prime := hchar
  let e : S ≃* ↥(ReeTag.F4.reeGamma K m) := eS.trans eK
  have hX : orderOf (e x) = 3 :=
    (orderOf_injective e.toMonoidHom e.injective x).trans hx
  obtain ⟨eU⟩ := CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU
    m K hKcard (e x) hX
  have hK' : Nat.card (GaloisField 2 (2 * (2 * m + 1))) = (2 ^ (2 * m + 1)) ^ 2 := by
    rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]
  have hq := (CFSG.RankThree.PartTwo.Sec8.Item87Proof.isQuasisimple_statedSU_three
    (F := GaloisField 2 (2 * (2 * m + 1))) (f := 2 * m + 1) hK' (by omega)).1
  have hmap := CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e x
  let eC : Subgroup.centralizer ({x} : Set S) ≃*
      Subgroup.centralizer ({e x} : Set ↥(ReeTag.F4.reeGamma K m)) :=
    (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hmap)
  have hqC : CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({x} : Set S)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_open
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv (eC.trans eU).symm hq)
  have hsub := CFSG.StandardType.ggRCS_isComponentOf_subgroupOf hD0 hD0.1 le_rfl
  have htop :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1313.eq_top_of_isComponentOf_quasisimple
      hqC hsub
  have hJC : J = Subgroup.centralizer ({x} : Set S) :=
    le_antisymm hD0.1 (Subgroup.subgroupOf_eq_top.1 htop)
  exact ⟨c, hJC ▸ hc, fun _ _ => rfl⟩

end CFSG.LocalAnalysis.GLTheoremA.F151

end
