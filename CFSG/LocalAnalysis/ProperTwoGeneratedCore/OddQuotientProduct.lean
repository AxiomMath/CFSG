module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GammaBasic
public import CFSG.LocalAnalysis.SolvableSignalizer.CoprimeAction
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWCore
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitElemAb
public import CFSG.GroupTheory.ConjTransport
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpLift
public import CFSG.Quasithin.Vol2.Ch11SecO5E
public import CFSG.GroupTheory.NormalizerQuotientProduct
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddKernelSylowEquiv

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG Open Subgroup

variable {Y A B : Type*} [Group Y] [Finite Y] [Group A] [Group B]

theorem properTwoGenCoreGamma_eq_top_of_oddKer_prod
    (f : Y →* A × B) (hf : Function.Surjective f)
    (hker : Odd (Nat.card f.ker))
    {VA : Subgroup A} (hVA : IsKleinFour VA)
    {VB : Subgroup B} (hVB : IsKleinFour VB)
    (T : Sylow 2 Y) :
    CFSG.Open.properTwoGenCoreGamma (T : Subgroup Y) 2 = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsKleinFour VA := hVA
  have : IsKleinFour VB := hVB
  have : IsMulCommutative VA := IsKleinFour.isMulCommutative
  have : IsMulCommutative VB := IsKleinFour.isMulCommutative
  let : CommGroup VA := IsMulCommutative.instCommGroup
  let : CommGroup VB := IsMulCommutative.instCommGroup
  have hodd : ¬ 2 ∣ Nat.card f.ker := fun h =>
    (Nat.not_even_iff_odd.mpr hker) (even_iff_two_dvd.mpr h)
  let C : Subgroup (A × B) := VA.prod VB
  let CA : Subgroup (A × B) := VA.prod (⊥ : Subgroup B)
  let CB : Subgroup (A × B) := (⊥ : Subgroup A).prod VB
  have hCcard : Nat.card C = 16 := by
    rw [show Nat.card C = Nat.card (↥VA × ↥VB) from
      Nat.card_congr (Subgroup.prodEquiv VA VB).toEquiv]
    rw [Nat.card_prod, hVA.card_four, hVB.card_four]
  have hCpow : ∀ z ∈ C, z ^ 2 = 1 := by
    rintro ⟨a, b⟩ hz
    rw [Subgroup.mem_prod] at hz
    ext
    · have h := IsKleinFour.mul_self (⟨a, hz.1⟩ : VA)
      simpa [sq] using congrArg Subtype.val h
    · have h := IsKleinFour.mul_self (⟨b, hz.2⟩ : VB)
      simpa [sq] using congrArg Subtype.val h
  have hCcomm : ∀ z ∈ C, ∀ w ∈ C, z * w = w * z := by
    rintro ⟨a, b⟩ hz ⟨c, d⟩ hw
    rw [Subgroup.mem_prod] at hz hw
    ext
    · simpa using congrArg Subtype.val (mul_comm (⟨a, hz.1⟩ : VA) (⟨c, hw.1⟩ : VA))
    · simpa using congrArg Subtype.val (mul_comm (⟨b, hz.2⟩ : VB) (⟨d, hw.2⟩ : VB))
  have hC2 : IsPGroup 2 C := IsPGroup.of_card (n := 4) (by rw [hCcard]; norm_num)
  have hCAcard : Nat.card CA = 4 := by
    rw [show Nat.card CA = Nat.card (↥VA × ↥(⊥ : Subgroup B)) from
      Nat.card_congr (Subgroup.prodEquiv VA (⊥ : Subgroup B)).toEquiv]
    rw [Nat.card_prod, hVA.card_four]
    simp
  have hCBcard : Nat.card CB = 4 := by
    rw [show Nat.card CB = Nat.card (↥(⊥ : Subgroup A) × ↥VB) from
      Nat.card_congr (Subgroup.prodEquiv (⊥ : Subgroup A) VB).toEquiv]
    rw [Nat.card_prod, hVB.card_four]
    simp
  let H : Subgroup Y := C.comap f
  obtain ⟨P⟩ : Nonempty (Sylow 2 H) := inferInstance
  let E0 : Subgroup Y := (P : Subgroup H).map H.subtype
  have hE0p : IsPGroup 2 E0 := P.isPGroup'.map H.subtype
  have hE0map : E0.map f = C := by
    have h := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.map_sylow_comap_eq f hf C hC2 P
    simpa [E0, H] using h
  have hE0cop : Nat.Coprime (Nat.card E0) (Nat.card f.ker) := by
    obtain ⟨n, hn⟩ := hE0p.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hker)
  have hE0ker : E0 ⊓ f.ker = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hE0cop)
  let fE0 : E0 →* A × B := f.comp E0.subtype
  have hfE0inj : Function.Injective fE0 := by
    intro x y hxy
    have hmem : ((x : E0) : Y) * ((y : E0) : Y)⁻¹ ∈ E0 ⊓ f.ker := by
      refine ⟨E0.mul_mem x.2 (E0.inv_mem y.2), ?_⟩
      have hfg : f ((x : E0) : Y) = f ((y : E0) : Y) := by simpa [fE0] using hxy
      have hgoal : f (((x : E0) : Y) * ((y : E0) : Y)⁻¹) = 1 := by
        rw [map_mul, map_inv, hfg, mul_inv_cancel]
      simpa [MonoidHom.ker_toSubmonoid, MonoidHom.mem_mker] using hgoal
    have h1 : ((x : E0) : Y) * ((y : E0) : Y)⁻¹ = 1 := by
      simpa [hE0ker] using hmem
    exact Subtype.ext (mul_inv_eq_one.mp h1)
  have hfE0range : fE0.range = C := by
    change (f.comp E0.subtype).range = C
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hE0map
  have hE0card : Nat.card E0 = 16 := by
    calc Nat.card E0 = Nat.card fE0.range :=
          Nat.card_congr (MonoidHom.ofInjective hfE0inj).toEquiv
      _ = Nat.card C := by rw [hfE0range]
      _ = 16 := hCcard
  have hE0pow : ∀ x ∈ E0, x ^ 2 = 1 := by
    intro x hx
    have hxr : fE0 ⟨x, hx⟩ ∈ C := by
      rw [← hfE0range]
      exact ⟨⟨x, hx⟩, rfl⟩
    have hsq : (⟨x, hx⟩ : E0) ^ 2 = 1 := by
      apply hfE0inj
      rw [map_pow, map_one]
      exact hCpow _ hxr
    simpa using congrArg Subtype.val hsq
  have hE0comm : ∀ x ∈ E0, ∀ y ∈ E0, x * y = y * x := by
    intro x hx y hy
    have hxr : fE0 ⟨x, hx⟩ ∈ C := by
      rw [← hfE0range]
      exact ⟨⟨x, hx⟩, rfl⟩
    have hyr : fE0 ⟨y, hy⟩ ∈ C := by
      rw [← hfE0range]
      exact ⟨⟨y, hy⟩, rfl⟩
    have hcomm : (⟨x, hx⟩ : E0) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
      apply hfE0inj
      rw [map_mul, map_mul]
      exact hCcomm _ hxr _ hyr
    simpa using congrArg Subtype.val hcomm
  obtain ⟨g, hg⟩ := CFSG.GroupTheory.exists_map_conj_le_sylow T hE0p
  let E : Subgroup Y := E0.map (MulAut.conj g).toMonoidHom
  have hET : E ≤ T := hg
  have hEcard : Nat.card E = 16 := by
    change Nat.card (E0.map (MulAut.conj g).toMonoidHom) = 16
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE0card]
  have hEp : IsPGroup 2 E := by
    change IsPGroup 2 (E0.map (MulAut.conj g).toMonoidHom)
    exact hE0p.map _
  have hEpow : ∀ x ∈ E, x ^ 2 = 1 := by
    rintro x ⟨y, hy, rfl⟩
    rw [← map_pow, hE0pow y hy, map_one]
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro x ⟨y, hy, rfl⟩ z ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, hE0comm y hy w hw]
  have hEel : CFSG.Open.IsElemAbelian 2 E :=
    ⟨⟨⟨fun x y => Subtype.ext (hEcomm (x : Y) x.2 (y : Y) y.2)⟩⟩, hEpow⟩
  let EA0e : Subgroup E0 := CA.comap fE0
  let EA0 : Subgroup Y := EA0e.map E0.subtype
  have hEA0emap : EA0e.map fE0 = CA := by
    apply le_antisymm (Subgroup.map_comap_le fE0 CA)
    intro z hz
    have hzC : z ∈ C := Subgroup.prod_mono le_rfl bot_le hz
    have hzrange : z ∈ fE0.range := by rw [hfE0range]; exact hzC
    obtain ⟨e, he⟩ := hzrange
    rw [← he]
    exact Subgroup.mem_map_of_mem fE0 (by rw [Subgroup.mem_comap, he]; exact hz)
  have hEA0ecard : Nat.card EA0e = 4 := by
    rw [← Subgroup.card_map_of_injective (K := EA0e) (f := fE0) hfE0inj,
      hEA0emap, hCAcard]
  have hEA0card : Nat.card EA0 = 4 := by
    change Nat.card (EA0e.map E0.subtype) = 4
    rw [Subgroup.card_subtype, hEA0ecard]
  have hEA0pow : ∀ x ∈ EA0, x ^ 2 = 1 := by
    rintro x ⟨e, he, rfl⟩
    have hfe : fE0 e ∈ CA := by
      rw [← hEA0emap]
      exact Subgroup.mem_map_of_mem fE0 he
    have hfeC : fE0 e ∈ C := Subgroup.prod_mono le_rfl bot_le hfe
    have hsq : (e : E0) ^ 2 = 1 := by
      apply hfE0inj
      rw [map_pow, map_one]
      exact hCpow _ hfeC
    simpa using congrArg Subtype.val hsq
  have hEA0 : IsKleinFour EA0 :=
    CFSG.ComponentClassification.FooteLit.isKleinFour_of_card_eq_four hEA0card hEA0pow
  let EA : Subgroup Y := EA0.map (MulAut.conj g).toMonoidHom
  have hEAcard : Nat.card EA = 4 := by
    change Nat.card (EA0.map (MulAut.conj g).toMonoidHom) = 4
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hEA0card]
  have hEApow : ∀ x ∈ EA, x ^ 2 = 1 := by
    rintro x ⟨y, hy, rfl⟩
    rw [← map_pow, hEA0pow y hy, map_one]
  have hEA : IsKleinFour EA :=
    CFSG.ComponentClassification.FooteLit.isKleinFour_of_card_eq_four hEAcard hEApow
  have hEA0E0 : EA0 ≤ E0 := Subgroup.map_subtype_le EA0e
  have hEAT : EA ≤ T := (Subgroup.map_mono hEA0E0).trans hET
  let EZ0e : Subgroup E0 := CB.comap fE0
  let EZ0 : Subgroup Y := EZ0e.map E0.subtype
  have hEZ0emap : EZ0e.map fE0 = CB := by
    apply le_antisymm (Subgroup.map_comap_le fE0 CB)
    intro z hz
    have hzC : z ∈ C := Subgroup.prod_mono bot_le le_rfl hz
    have hzrange : z ∈ fE0.range := by rw [hfE0range]; exact hzC
    obtain ⟨e, he⟩ := hzrange
    rw [← he]
    exact Subgroup.mem_map_of_mem fE0 (by rw [Subgroup.mem_comap, he]; exact hz)
  have hEZ0ecard : Nat.card EZ0e = 4 := by
    rw [← Subgroup.card_map_of_injective (K := EZ0e) (f := fE0) hfE0inj,
      hEZ0emap, hCBcard]
  have hEZ0card : Nat.card EZ0 = 4 := by
    change Nat.card (EZ0e.map E0.subtype) = 4
    rw [Subgroup.card_subtype, hEZ0ecard]
  have hEZ0pow : ∀ x ∈ EZ0, x ^ 2 = 1 := by
    rintro x ⟨e, he, rfl⟩
    have hfe : fE0 e ∈ CB := by
      rw [← hEZ0emap]
      exact Subgroup.mem_map_of_mem fE0 he
    have hfeC : fE0 e ∈ C := Subgroup.prod_mono bot_le le_rfl hfe
    have hsq : (e : E0) ^ 2 = 1 := by
      apply hfE0inj
      rw [map_pow, map_one]
      exact hCpow _ hfeC
    simpa using congrArg Subtype.val hsq
  have hEZ0 : IsKleinFour EZ0 :=
    CFSG.ComponentClassification.FooteLit.isKleinFour_of_card_eq_four hEZ0card hEZ0pow
  let EZ : Subgroup Y := EZ0.map (MulAut.conj g).toMonoidHom
  have hEZcard : Nat.card EZ = 4 := by
    change Nat.card (EZ0.map (MulAut.conj g).toMonoidHom) = 4
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hEZ0card]
  have hEZpow : ∀ x ∈ EZ, x ^ 2 = 1 := by
    rintro x ⟨y, hy, rfl⟩
    rw [← map_pow, hEZ0pow y hy, map_one]
  have hEZ : IsKleinFour EZ :=
    CFSG.ComponentClassification.FooteLit.isKleinFour_of_card_eq_four hEZcard hEZpow
  have hEZ0E0 : EZ0 ≤ E0 := Subgroup.map_subtype_le EZ0e
  have hEZT : EZ ≤ T := (Subgroup.map_mono hEZ0E0).trans hET
  have hEAp : IsPGroup 2 EA := IsPGroup.of_card (n := 2) (by rw [hEAcard]; norm_num)
  have hEZp : IsPGroup 2 EZ := IsPGroup.of_card (n := 2) (by rw [hEZcard]; norm_num)
  have hEAimage : EA.map f ≤ (⊤ : Subgroup A).prod (⊥ : Subgroup B) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨e0, he0, rfl⟩ := Subgroup.mem_map.mp he
    have hfe : fE0 e0 ∈ CA := by
      rw [← hEA0emap]
      exact Subgroup.mem_map_of_mem fE0 he0
    have hfe2 : (f (e0 : E0)).2 = 1 := by
      simpa [fE0] using (Subgroup.mem_prod.mp hfe).2
    rw [Subgroup.mem_prod]
    refine ⟨trivial, ?_⟩
    change (f ((MulAut.conj g) (e0 : E0))).2 = 1
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, Prod.snd_mul, Prod.snd_mul,
      Prod.snd_inv, hfe2, mul_one, mul_inv_cancel]
  have hEZimage : EZ.map f ≤ (⊥ : Subgroup A).prod (⊤ : Subgroup B) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨e0, he0, rfl⟩ := Subgroup.mem_map.mp he
    have hfe : fE0 e0 ∈ CB := by
      rw [← hEZ0emap]
      exact Subgroup.mem_map_of_mem fE0 he0
    have hfe1 : (f (e0 : E0)).1 = 1 := by
      simpa [fE0] using (Subgroup.mem_prod.mp hfe).1
    rw [Subgroup.mem_prod]
    refine ⟨?_, trivial⟩
    change (f ((MulAut.conj g) (e0 : E0))).1 = 1
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul,
      Prod.fst_inv, hfe1, mul_one, mul_inv_cancel]
  have hrank_of_klein : ∀ {U : Subgroup Y}, IsKleinFour U → 2 ≤ CFSG.Open.pRank 2 U := by
    intro U hU
    let : IsKleinFour U := hU
    have hUel : CFSG.Open.IsElemAbelian 2 U := by
      refine ⟨IsKleinFour.isMulCommutative, fun x hx => ?_⟩
      have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : U)
      rw [hU.exponent_two] at h
      exact congrArg Subtype.val h
    exact CFSG.SectionRank.le_pRank (by norm_num) le_rfl hUel
      (by rw [hU.card_four]; norm_num)
  let Γ : Subgroup Y := CFSG.Open.properTwoGenCoreGamma (T : Subgroup Y) 2
  have hΓEA : Subgroup.centralizer (EA : Set Y) ≤ Γ :=
    (Subgroup.centralizer_le_normalizer (EA : Set Y)).trans
      (CFSG.OddStandard.Solomon75.AhatData.normalizer_le_gamma hEAT (hrank_of_klein hEA))
  have hΓEZ : Subgroup.centralizer (EZ : Set Y) ≤ Γ :=
    (Subgroup.centralizer_le_normalizer (EZ : Set Y)).trans
      (CFSG.OddStandard.Solomon75.AhatData.normalizer_le_gamma hEZT (hrank_of_klein hEZ))
  have hcenEA : (Subgroup.centralizer (EA : Set Y)).map f =
      Subgroup.centralizer ((EA.map f : Subgroup (A × B)) : Set (A × B)) :=
    CFSG.ComponentClassification.GrSLit.map_centralizer_eq_of_odd_ker f hf hodd hEAp
  have hcenEZ : (Subgroup.centralizer (EZ : Set Y)).map f =
      Subgroup.centralizer ((EZ.map f : Subgroup (A × B)) : Set (A × B)) :=
    CFSG.ComponentClassification.GrSLit.map_centralizer_eq_of_odd_ker f hf hodd hEZp
  have hBcen : (⊥ : Subgroup A).prod (⊤ : Subgroup B) ≤
      Subgroup.centralizer ((EA.map f : Subgroup (A × B)) : Set (A × B)) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hz1 : z.1 = 1 := (Subgroup.mem_prod.mp hz).1
    have hw2 : w.2 = 1 := (Subgroup.mem_prod.mp (hEAimage hw)).2
    ext <;> simp [hz1, hw2]
  have hAcen : (⊤ : Subgroup A).prod (⊥ : Subgroup B) ≤
      Subgroup.centralizer ((EZ.map f : Subgroup (A × B)) : Set (A × B)) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hz2 : z.2 = 1 := (Subgroup.mem_prod.mp hz).2
    have hw1 : w.1 = 1 := (Subgroup.mem_prod.mp (hEZimage hw)).1
    ext <;> simp [hz2, hw1]
  have h1 : (⊥ : Subgroup A).prod (⊤ : Subgroup B) ≤ Γ.map f :=
    calc (⊥ : Subgroup A).prod (⊤ : Subgroup B)
        ≤ Subgroup.centralizer ((EA.map f : Subgroup (A × B)) : Set (A × B)) := hBcen
      _ = (Subgroup.centralizer (EA : Set Y)).map f := hcenEA.symm
      _ ≤ Γ.map f := Subgroup.map_mono hΓEA
  have h2 : (⊤ : Subgroup A).prod (⊥ : Subgroup B) ≤ Γ.map f :=
    calc (⊤ : Subgroup A).prod (⊥ : Subgroup B)
        ≤ Subgroup.centralizer ((EZ.map f : Subgroup (A × B)) : Set (A × B)) := hAcen
      _ = (Subgroup.centralizer (EZ : Set Y)).map f := hcenEZ.symm
      _ ≤ Γ.map f := Subgroup.map_mono hΓEZ
  have hsup : ((⊥ : Subgroup A).prod (⊤ : Subgroup B)) ⊔
      ((⊤ : Subgroup A).prod (⊥ : Subgroup B)) = (⊤ : Subgroup (A × B)) := by
    apply eq_top_iff.mpr
    rintro ⟨a, b⟩ -
    have h1 : (1, b) ∈ (⊥ : Subgroup A).prod (⊤ : Subgroup B) :=
      Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top _⟩
    have h2 : (a, 1) ∈ (⊤ : Subgroup A).prod (⊥ : Subgroup B) :=
      Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩
    have hmul := Subgroup.mul_mem
      ((⊥ : Subgroup A).prod (⊤ : Subgroup B) ⊔ (⊤ : Subgroup A).prod (⊥ : Subgroup B))
      (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
    simpa using hmul
  have hΓmap : Γ.map f = ⊤ := by
    apply top_le_iff.mp
    rw [← hsup]
    exact sup_le h1 h2
  let R : Subgroup Y := f.ker
  have : R.Normal := f.normal_ker
  have : IsMulCommutative E := hEel.1
  let : CommGroup E := IsMulCommutative.instCommGroup
  let α : E →* MulAut R := (MulAut.conjNormal : Y →* MulAut R).comp E.subtype
  have : CFSG.IsElementaryAbelian 2 E :=
    { toIsMulCommutative := hEel.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hEel.2 x x.2) }
  have : Nontrivial E :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hEcard]; norm_num)
  have hgen := CFSG.SolvableSignalizer.iSup_fixedBySubgroup_index_eq_top
    2 Nat.prime_two (A := E) (G := R) α hodd
  have hgenle : (⨆ (U : Subgroup E) (_ : U.index = 2),
      CFSG.SolvableSignalizer.fixedBySubgroup α U).map R.subtype ≤ Γ := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun U => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hU => ?_
    have hUcard : Nat.card U = 8 := by
      have h1 := Subgroup.card_mul_index U
      rw [hU, hEcard] at h1
      omega
    obtain ⟨W, hWU, hWcard⟩ :=
      Sylow.exists_subgroup_le_card_pow_prime_of_le_card (n := 2) (p := 2)
        Nat.prime_two hEp (by rw [hUcard]; norm_num)
    let UU : Subgroup Y := W.map E.subtype
    have hUUcard : Nat.card UU = 4 := by
      change Nat.card (W.map E.subtype) = 4
      rw [Subgroup.card_subtype, hWcard]
      norm_num
    have hUUpow : ∀ x ∈ UU, x ^ 2 = 1 := by
      rintro x ⟨w, hw, rfl⟩
      exact hEpow (w : Y) w.2
    have hUUk : IsKleinFour UU :=
      CFSG.ComponentClassification.FooteLit.isKleinFour_of_card_eq_four hUUcard hUUpow
    have hUUT : UU ≤ T := (Subgroup.map_subtype_le W).trans hET
    have hUUnorm : Subgroup.normalizer (UU : Set Y) ≤ Γ :=
      CFSG.OddStandard.Solomon75.AhatData.normalizer_le_gamma hUUT (hrank_of_klein hUUk)
    have hfixle : (CFSG.SolvableSignalizer.fixedBySubgroup α U).map R.subtype ≤
        Subgroup.centralizer (UU : Set Y) := by
      rintro _ ⟨r, hr, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro y ⟨w, hw, rfl⟩
      have hwU : w ∈ U := hWU hw
      have hfix := (CFSG.SolvableSignalizer.mem_fixedBySubgroup α U r).mp hr w hwU
      have hval := congrArg Subtype.val hfix
      change ((MulAut.conjNormal (E.subtype w) r : R) : Y) = (r : Y) at hval
      rw [MulAut.conjNormal_apply] at hval
      change (w : Y) * (r : Y) * (w : Y)⁻¹ = (r : Y) at hval
      have hcomm : (w : Y) * (r : Y) = (r : Y) * (w : Y) := by
        calc (w : Y) * (r : Y) = (w : Y) * (r : Y) * (w : Y)⁻¹ * (w : Y) := by group
          _ = (r : Y) * (w : Y) := by rw [hval]
      exact hcomm
    exact (hfixle.trans (Subgroup.centralizer_le_normalizer (UU : Set Y))).trans hUUnorm
  have hRle : R ≤ Γ := by
    have h := hgenle
    rw [hgen, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    exact h
  have hcomap := Subgroup.comap_map_eq f Γ
  rw [hΓmap, Subgroup.comap_top, sup_eq_left.mpr hRle] at hcomap
  exact hcomap.symm


section AltFiveProd

variable {Y Z : Type*} [Group Y] [Finite Y] [Group Z]

theorem exists_central_isKleinFour_of_oddKer_alt5_prod
    (f : Y →* alternatingGroup (Fin 5) × Z)
    (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker))
    (T : Sylow 2 Y) :
    ∃ V : Subgroup Y, IsKleinFour V ∧ V ≤ (T : Subgroup Y) ∧
      V ≤ Subgroup.centralizer ((T : Subgroup Y) : Set Y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (alternatingGroup (Fin 5) × Z) := Finite.of_surjective f hf
  have : Finite Z := Finite.of_surjective
    (MonoidHom.snd (alternatingGroup (Fin 5)) Z) Prod.snd_surjective
  let SX : Sylow 2 (alternatingGroup (Fin 5) × Z) := T.mapSurjective hf
  let SA : Sylow 2 (alternatingGroup (Fin 5)) :=
    SX.mapSurjective (f := MonoidHom.fst (alternatingGroup (Fin 5)) Z) Prod.fst_surjective
  let SB : Sylow 2 Z :=
    SX.mapSurjective (f := MonoidHom.snd (alternatingGroup (Fin 5)) Z) Prod.snd_surjective
  have hSAcoe : (SA : Subgroup (alternatingGroup (Fin 5))) =
      (SX : Subgroup (alternatingGroup (Fin 5) × Z)).map
        (MonoidHom.fst (alternatingGroup (Fin 5)) Z) :=
    Sylow.coe_mapSurjective (f := MonoidHom.fst (alternatingGroup (Fin 5)) Z)
      Prod.fst_surjective SX
  have hSBcoe : (SB : Subgroup Z) =
      (SX : Subgroup (alternatingGroup (Fin 5) × Z)).map
        (MonoidHom.snd (alternatingGroup (Fin 5)) Z) :=
    Sylow.coe_mapSurjective (f := MonoidHom.snd (alternatingGroup (Fin 5)) Z)
      Prod.snd_surjective SX
  have hSAk : IsKleinFour (SA : Subgroup (alternatingGroup (Fin 5))) :=
    CFSG.Quasithin.Vol2.Ch11.O5.isKleinFour_sylow_two_alt5 SA
  have hSXtop : CFSG.QuasithinUnique.IsSylowTwoOf
      (SX : Subgroup (alternatingGroup (Fin 5) × Z)) ⊤ := by
    refine ⟨le_top, SX.isPGroup', ?_⟩
    rw [show ((SX : Subgroup (alternatingGroup (Fin 5) × Z)).subgroupOf ⊤).index =
        (SX : Subgroup (alternatingGroup (Fin 5) × Z)).index from
      Subgroup.relIndex_top_right (SX : Subgroup (alternatingGroup (Fin 5) × Z))]
    exact SX.not_dvd_index
  have hSAtop : CFSG.QuasithinUnique.IsSylowTwoOf
      (SA : Subgroup (alternatingGroup (Fin 5))) ⊤ := by
    refine ⟨le_top, SA.isPGroup', ?_⟩
    rw [show ((SA : Subgroup (alternatingGroup (Fin 5))).subgroupOf ⊤).index =
        (SA : Subgroup (alternatingGroup (Fin 5))).index from
      Subgroup.relIndex_top_right (SA : Subgroup (alternatingGroup (Fin 5)))]
    exact SA.not_dvd_index
  have hSBtop : CFSG.QuasithinUnique.IsSylowTwoOf (SB : Subgroup Z) ⊤ := by
    refine ⟨le_top, SB.isPGroup', ?_⟩
    rw [show ((SB : Subgroup Z).subgroupOf ⊤).index = (SB : Subgroup Z).index from
      Subgroup.relIndex_top_right (SB : Subgroup Z)]
    exact SB.not_dvd_index
  have hprodSylow : CFSG.QuasithinUnique.IsSylowTwoOf
      ((SA : Subgroup (alternatingGroup (Fin 5))).prod (SB : Subgroup Z)) ⊤ :=
    CFSG.GroupTheory.isSylowTwoOf_prod hSAtop hSBtop
  have hSle : (SX : Subgroup (alternatingGroup (Fin 5) × Z)) ≤
      (SA : Subgroup (alternatingGroup (Fin 5))).prod (SB : Subgroup Z) := by
    intro x hx
    rw [Subgroup.mem_prod]
    exact ⟨by rw [hSAcoe]; exact Subgroup.mem_map_of_mem _ hx,
      by rw [hSBcoe]; exact Subgroup.mem_map_of_mem _ hx⟩
  have hEq : (SA : Subgroup (alternatingGroup (Fin 5))).prod (SB : Subgroup Z) =
      (SX : Subgroup (alternatingGroup (Fin 5) × Z)) :=
    CFSG.QuasithinUnique.IsSylowTwoOf.eq_of_le hSXtop hSle le_top hprodSylow.2.1
  let P : Subgroup (alternatingGroup (Fin 5) × Z) :=
    (SA : Subgroup (alternatingGroup (Fin 5))).prod (⊥ : Subgroup Z)
  have hPS : P ≤ (SX : Subgroup (alternatingGroup (Fin 5) × Z)) := by
    rw [← hEq]
    exact Subgroup.prod_mono le_rfl bot_le
  have hPcard : Nat.card P = 4 := by
    rw [show Nat.card P = Nat.card
        (↥(SA : Subgroup (alternatingGroup (Fin 5))) × ↥(⊥ : Subgroup Z)) from
      Nat.card_congr (Subgroup.prodEquiv
        (SA : Subgroup (alternatingGroup (Fin 5))) (⊥ : Subgroup Z)).toEquiv]
    rw [Nat.card_prod, hSAk.card_four]
    simp
  have hPpow : ∀ x ∈ P, x ^ 2 = 1 := by
    rintro ⟨a, z⟩ hx
    rw [Subgroup.mem_prod] at hx
    have ha : a * a = 1 := by
      have : IsKleinFour (SA : Subgroup (alternatingGroup (Fin 5))) := hSAk
      exact congrArg Subtype.val (IsKleinFour.mul_self (⟨a, hx.1⟩ : SA))
    have hz : z = 1 := Subgroup.mem_bot.mp hx.2
    ext <;> simp [sq, ha, hz]
  let Psub : Subgroup (SX : Subgroup (alternatingGroup (Fin 5) × Z)) :=
    P.subgroupOf (SX : Subgroup (alternatingGroup (Fin 5) × Z))
  have hPsubcard : Nat.card Psub = 4 := by
    rw [show Nat.card Psub = Nat.card P from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv]
    exact hPcard
  have hPsubpow : ∀ x ∈ Psub, x ^ 2 = 1 := by
    intro x hx
    apply Subtype.ext
    have hxP : (x : alternatingGroup (Fin 5) × Z) ∈ P := Subgroup.mem_subgroupOf.mp hx
    simpa using hPpow (x : alternatingGroup (Fin 5) × Z) hxP
  have hPsub : IsKleinFour Psub :=
    CFSG.ComponentClassification.FooteLit.isKleinFour_of_card_eq_four hPsubcard hPsubpow
  have hPcentral : P ≤ Subgroup.centralizer
      ((SX : Subgroup (alternatingGroup (Fin 5) × Z)) :
        Set (alternatingGroup (Fin 5) × Z)) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hp' : p.1 ∈ (SA : Subgroup (alternatingGroup (Fin 5))) ∧
        p.2 ∈ (⊥ : Subgroup Z) := Subgroup.mem_prod.mp hp
    have hqP : q ∈ (SA : Subgroup (alternatingGroup (Fin 5))).prod (SB : Subgroup Z) := by
      rw [← hEq] at hq
      exact hq
    have hq' : q.1 ∈ (SA : Subgroup (alternatingGroup (Fin 5))) ∧
        q.2 ∈ (SB : Subgroup Z) := Subgroup.mem_prod.mp hqP
    have hp2 : p.2 = 1 := Subgroup.mem_bot.mp hp'.2
    have : IsKleinFour (SA : Subgroup (alternatingGroup (Fin 5))) := hSAk
    have : IsMulCommutative (SA : Subgroup (alternatingGroup (Fin 5))) :=
      IsKleinFour.isMulCommutative
    let : CommGroup (SA : Subgroup (alternatingGroup (Fin 5))) :=
      IsMulCommutative.instCommGroup
    apply Prod.ext
    · simpa using congrArg Subtype.val
        (mul_comm (⟨q.1, hq'.1⟩ : SA) (⟨p.1, hp'.1⟩ : SA))
    · simp [hp2]
  obtain ⟨e⟩ : Nonempty ((T : Subgroup Y) ≃*
      (SX : Subgroup (alternatingGroup (Fin 5) × Z))) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.odd_kernel_sylow_equiv f hf hker T
  let Vsub : Subgroup (T : Subgroup Y) := Psub.map e.symm.toMonoidHom
  have hVsubcard : Nat.card Vsub = 4 := by
    change Nat.card (Psub.map e.symm.toMonoidHom) = 4
    rw [Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective,
      hPsubcard]
  have hVsubpow : ∀ x ∈ Vsub, x ^ 2 = 1 := by
    rintro x ⟨y, hy, rfl⟩
    rw [← map_pow, hPsubpow y hy, map_one]
  have hVsub : IsKleinFour Vsub :=
    CFSG.ComponentClassification.FooteLit.isKleinFour_of_card_eq_four hVsubcard hVsubpow
  let V : Subgroup Y := Vsub.map (T : Subgroup Y).subtype
  have hVcard : Nat.card V = 4 := by
    change Nat.card (Vsub.map (T : Subgroup Y).subtype) = 4
    rw [Subgroup.card_subtype, hVsubcard]
  have hVpow : ∀ x ∈ V, x ^ 2 = 1 := by
    rintro x ⟨y, hy, rfl⟩
    simpa using congrArg Subtype.val (hVsubpow y hy)
  have hV : IsKleinFour V :=
    CFSG.ComponentClassification.FooteLit.isKleinFour_of_card_eq_four hVcard hVpow
  refine ⟨V, hV, Subgroup.map_subtype_le Vsub, ?_⟩
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  obtain ⟨y, hy, rfl⟩ := hv
  obtain ⟨p, hp, rfl⟩ := hy
  have hpP : (p : alternatingGroup (Fin 5) × Z) ∈ P := Subgroup.mem_subgroupOf.mp hp
  have hpCen := hPcentral hpP
  rw [Subgroup.mem_centralizer_iff] at hpCen
  let t' : (T : Subgroup Y) := ⟨t, ht⟩
  have hcommSX : (e t') * p = p * (e t') := by
    apply Subtype.ext
    exact hpCen (e t') (e t').2
  have hcommT : t' * (e.symm p) = (e.symm p) * t' := by
    apply e.injective
    simpa [map_mul, MulEquiv.apply_symm_apply] using hcommSX
  simpa [t'] using congrArg Subtype.val hcommT

end AltFiveProd

end CFSG.ProperTwoGeneratedCore
