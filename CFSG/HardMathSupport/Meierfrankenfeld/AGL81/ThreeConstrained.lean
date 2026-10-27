module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.TransvectionBasic
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.TransvectionSolvable
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.ComponentExclusion
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.OffenderClosure
public import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.FStar
public import CFSG.Quasithin.H13.NQCatSubnormalCore

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

theorem pCore_two_eq_bot_of_normal_two [Finite W] {X : Subgroup (MulAut W)}
    (hO2 : ∀ Q : Subgroup (MulAut W), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥) :
    CFSG.pCore 2 ↥X = ⊥ := by
  refine B1.pCore_eq_bot_of_normal_two_trivial fun Q hQ hQp => ?_
  have hQ' : Q.map X.subtype = ⊥ := by
    refine hO2 _ (Subgroup.map_subtype_le Q) ?_ (hQp.map X.subtype)
    have hsub : (Q.map X.subtype).subgroupOf X = Q :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective Q
    rw [hsub]
    exact hQ
  exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).1 hQ'

theorem closure_transvectionsIn_subgroupOf_normal (X : Subgroup (MulAut W)) :
    ((Subgroup.closure (transvectionsIn X)).subgroupOf X).Normal :=
  ⟨fun d hd x => by
    rw [Subgroup.mem_subgroupOf] at hd ⊢
    simpa using B1.closure_transvectionsIn_normal x.1 x.2 d.1 hd⟩

@[expose] noncomputable def threeCoreOfClosure (X : Subgroup (MulAut W)) :
    Subgroup (MulAut W) :=
  ((CFSG.pCore 3 ↥((Subgroup.closure (transvectionsIn X)).subgroupOf X)).map
    ((Subgroup.closure (transvectionsIn X)).subgroupOf X).subtype).map X.subtype

theorem threeCoreOfClosure_le (X : Subgroup (MulAut W)) :
    threeCoreOfClosure X ≤ Subgroup.closure (transvectionsIn X) := by
  rintro _ ⟨y, ⟨z, -, rfl⟩, rfl⟩
  exact z.2

theorem isPGroup_threeCoreOfClosure (X : Subgroup (MulAut W)) :
    IsPGroup 3 (threeCoreOfClosure X) :=
  ((show IsPGroup 3 (CFSG.pCore 3 ↥((Subgroup.closure (transvectionsIn X)).subgroupOf X)) from
    CFSG.pCore_isPGroup).map _).map _

theorem conj_mem_threeCoreOfClosure (X : Subgroup (MulAut W)) {d q : MulAut W}
    (hd : d ∈ Subgroup.closure (transvectionsIn X)) (hq : q ∈ threeCoreOfClosure X) :
    d * q * d⁻¹ ∈ threeCoreOfClosure X := by
  obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hq
  have hdX : d ∈ X := B1.closure_transvectionsIn_le X hd
  have hdD : (⟨d, hdX⟩ : ↥X) ∈ (Subgroup.closure (transvectionsIn X)).subgroupOf X := by
    rw [Subgroup.mem_subgroupOf]
    exact hd
  have hz' := (inferInstance : (CFSG.pCore 3
    ↥((Subgroup.closure (transvectionsIn X)).subgroupOf X)).Normal).conj_mem z hz ⟨⟨d, hdX⟩, hdD⟩
  refine ⟨_, ⟨_, hz', rfl⟩, ?_⟩
  simp

theorem exists_not_commute_pCore_three
    [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {X : Subgroup (MulAut W)} (hKX : CFSG.Open.IsKGroup ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut W), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥)
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥X) :
    ∀ t ∈ transvectionsIn (Subgroup.closure (transvectionsIn X)),
      ∃ q ∈ threeCoreOfClosure X, t * q ≠ q * t := by
  classical
  intro t ht
  have hO2' : CFSG.pCore 2 ↥X = ⊥ := pCore_two_eq_bot_of_normal_two hO2
  have hDX : Subgroup.closure (transvectionsIn X) ≤ X := B1.closure_transvectionsIn_le X
  have htX : t ∈ X := hDX ht.1
  obtain ⟨ht1, w, htw⟩ := ht.2
  have htt : t * t = 1 := B1.tv_sq hW htw ht1
  by_contra hno
  push Not at hno
  let Dt : Subgroup ↥X := (Subgroup.closure (transvectionsIn X)).subgroupOf X
  have hDtn : Dt.Normal := closure_transvectionsIn_subgroupOf_normal X
  let tX : ↥X := ⟨t, htX⟩
  have htD : tX ∈ Dt := by
    show (tX : MulAut W) ∈ Subgroup.closure (transvectionsIn X)
    exact ht.1
  have hcomm : ∀ y : ↥X, t * (y : MulAut W) = (y : MulAut W) * t → y * tX = tX * y :=
    fun y h => Subtype.ext h.symm
  have hA₀ : Subgroup.zpowers tX ≤ Subgroup.centralizer
      (((CFSG.generalizedFitting ↥Dt).map Dt.subtype : Subgroup ↥X) : Set ↥X) := by
    by_contra hF
    rcases Coordinator.exists_pCore_or_component_of_not_le_centralizer hF with
      ⟨p, hp, hpA⟩ | ⟨K, hK, hKA⟩
    · apply hpA
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      by_cases hp2 : p = 2
      · subst hp2
        have hle := CFSG.Quasithin.H13.NQCat.map_pCore_le_pCore_of_isSubnormal' (p := 2)
          (Subgroup.Normal.isSubnormal hDtn)
        rw [hO2'] at hle
        have hy1 : y = 1 := by simpa using hle hy
        rw [hy1, one_mul, mul_one]
      by_cases hp3 : p = 3
      · subst hp3
        exact hcomm y (hno _ ⟨y, hy, rfl⟩)
      · apply hcomm
        have hRp : IsPGroup p (((CFSG.pCore p ↥Dt).map Dt.subtype).map X.subtype) :=
          ((show IsPGroup p (CFSG.pCore p ↥Dt) from CFSG.pCore_isPGroup).map _).map _
        have htR : ∀ y ∈ ((CFSG.pCore p ↥Dt).map Dt.subtype).map X.subtype,
            t * y * t⁻¹ ∈ ((CFSG.pCore p ↥Dt).map Dt.subtype).map X.subtype := by
          rintro _ ⟨y, ⟨z, hz, rfl⟩, rfl⟩
          have hz' := (inferInstance : (CFSG.pCore p ↥Dt).Normal).conj_mem z hz ⟨tX, htD⟩
          exact ⟨_, ⟨_, hz', rfl⟩, by simp [tX]⟩
        exact commute_of_isPGroup_of_transvection hW ⟨ht1, w, htw⟩ hp hp2 hp3 hRp htR _
          ⟨y, hy, rfl⟩
    · apply hKA
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      apply hcomm
      have eK' : ↥K ≃* ↥(K.map Dt.subtype) :=
        Subgroup.equivMapOfInjective K Dt.subtype Dt.subtype_injective
      have hK'c : CFSG.IsComponent (K.map Dt.subtype) :=
        ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eK' hK.1,
          Subgroup.IsSubnormal.trans' hK.2 (Subgroup.Normal.isSubnormal hDtn)⟩
      have hK3 := not_three_dvd_card_of_isComponent hcon hK'c
      have hoff := isFFStarOffender_zpowers_of_transvection hW htX ⟨ht1, w, htw⟩
      exact commute_of_isFFStarOffender_of_isComponent hW hKX hO2' hoff hK'c hK3 t
        (Subgroup.mem_zpowers t) y hy
  have htX2 : tX ^ 2 = 1 := Subtype.ext (by simp [pow_two, tX, htt])
  have ha2 : ∀ a ∈ Subgroup.zpowers tX, a ^ 2 = 1 := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, htX2, one_zpow]
  have hcent := Coordinator.le_centralizer_of_le_centralizer_genFitting hO2' ha2 hA₀
  have hmem : tX ∈ Coordinator.centerInvolutions Dt := by
    refine ⟨htD, fun x hx => ?_, htX2⟩
    exact (Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_zpowers tX)) x hx).symm
  rw [Coordinator.centerInvolutions_eq_bot hO2' Dt, Subgroup.mem_bot] at hmem
  exact ht1 (congrArg Subtype.val hmem)

theorem isSolvable_closure_transvectionsIn
    [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {X : Subgroup (MulAut W)} (hKX : CFSG.Open.IsKGroup ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut W), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥)
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥X) :
    Group.IsSolvable ↥(Subgroup.closure (transvectionsIn X)) := by
  have hcl : Subgroup.closure (transvectionsIn (Subgroup.closure (transvectionsIn X))) =
      Subgroup.closure (transvectionsIn X) := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).2 fun t ht => ht.1
    · exact Subgroup.closure_mono fun t ht => ⟨Subgroup.subset_closure ht, ht.2⟩
  exact isSolvable_of_transvections_move hW hcl (threeCoreOfClosure_le X)
    (isPGroup_threeCoreOfClosure X) (fun d hd q hq => conj_mem_threeCoreOfClosure X hd hq)
    (exists_not_commute_pCore_three hW hKX hO2 hcon)

theorem le_centralizer_layer_of_forall_component {Γ : Type*} [Group Γ] {S : Subgroup Γ}
    (h : ∀ K : Subgroup Γ, CFSG.IsComponent K → ∀ s ∈ S, ∀ k ∈ K, k * s = s * k) :
    S ≤ Subgroup.centralizer (CFSG.layer Γ : Set Γ) := by
  rw [Subgroup.le_centralizer_iff]
  refine sSup_le fun K hK k hk => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  exact (h K hK s hs k hk).symm

theorem eq_one_of_isPGroup_two_of_odd {Γ : Type*} [Group Γ] {Q F : Subgroup Γ}
    (hQ : IsPGroup 2 Q) (hF : Odd (Nat.card F)) {c : Γ} (hcQ : c ∈ Q) (hcF : c ∈ F) : c = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨c, hcQ⟩
  have h1 : c ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h2 : orderOf c ∣ Nat.card F := by
    have := orderOf_dvd_natCard (⟨c, hcF⟩ : F)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card F) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hF)
  exact orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1)) h2)

theorem exists_solvable_le_of_isFFStarOffender
    [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {X : Subgroup (MulAut W)} (hKX : CFSG.Open.IsKGroup ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut W), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥)
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥X) {A : Subgroup (MulAut W)}
    (hA : IsFFStarOffender X A) :
    ∃ Y : Subgroup (MulAut W), Y ≤ X ∧ A ≤ Y ∧ Subgroup.closure (transvectionsIn X) ≤ Y ∧
      Group.IsSolvable ↥Y ∧
      ∀ Q : Subgroup (MulAut W), Q ≤ Y → (Q.subgroupOf Y).Normal → IsPGroup 2 Q → Q = ⊥ := by
  classical
  have hO2' : CFSG.pCore 2 ↥X = ⊥ := pCore_two_eq_bot_of_normal_two hO2
  have hDX : Subgroup.closure (transvectionsIn X) ≤ X := B1.closure_transvectionsIn_le X
  have hAX : A ≤ X := hA.1
  let Dt : Subgroup ↥X := (Subgroup.closure (transvectionsIn X)).subgroupOf X
  have hDtn : Dt.Normal := closure_transvectionsIn_subgroupOf_normal X
  let Ft : Subgroup ↥X := CFSG.fittingSubgroup ↥X
  let At : Subgroup ↥X := A.subgroupOf X
  have hcF : Ft ≤ Subgroup.centralizer (CFSG.layer ↥X : Set ↥X) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp CFSG.LocalCores.fitting_layer_commute
  have hcD : Dt ≤ Subgroup.centralizer (CFSG.layer ↥X : Set ↥X) := by
    refine le_centralizer_layer_of_forall_component fun K hK => ?_
    have hK3 := not_three_dvd_card_of_isComponent hcon hK
    have hle : Subgroup.closure (transvectionsIn X) ≤
        (Subgroup.centralizer (K : Set ↥X)).map X.subtype := by
      refine (Subgroup.closure_le _).2 fun t ht => ?_
      have hoff := isFFStarOffender_zpowers_of_transvection hW ht.1 ht.2
      refine ⟨⟨t, ht.1⟩, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_, rfl⟩
      exact Subtype.ext (commute_of_isFFStarOffender_of_isComponent hW hKX hO2' hoff hK hK3 t
        (Subgroup.mem_zpowers t) k hk).symm
    intro d hd k hk
    obtain ⟨d', hd', hdd'⟩ := hle (Subgroup.mem_subgroupOf.mp hd)
    have hd'd : d' = d := Subtype.ext hdd'
    rw [← hd'd]
    exact Subgroup.mem_centralizer_iff.mp hd' k hk
  have hcA : At ≤ Subgroup.centralizer (CFSG.layer ↥X : Set ↥X) := by
    refine le_centralizer_layer_of_forall_component fun K hK a ha k hk => ?_
    have hK3 := not_three_dvd_card_of_isComponent hcon hK
    exact Subtype.ext (commute_of_isFFStarOffender_of_isComponent hW hKX hO2' hA hK hK3 a
      (Subgroup.mem_subgroupOf.mp ha) k hk).symm
  have hDsolv : Group.IsSolvable ↥(Subgroup.closure (transvectionsIn X)) :=
    isSolvable_closure_transvectionsIn hW hKX hO2 hcon
  have hDtsolv : Group.IsSolvable ↥Dt :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hDX).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hDX).injective
  have hFtsolv : Group.IsSolvable ↥Ft := by
    have := (CFSG.LocalCores.fitting_nilpotent (G := ↥X)).1
    infer_instance
  have hFDsolv : Group.IsSolvable ↥(Ft ⊔ Dt) := CFSG.ABGLocalTools.isSolvable_sup_of_normal Ft Dt
  have hFDn : (Ft ⊔ Dt).Normal := inferInstance
  have hYtsolv : Group.IsSolvable ↥((Ft ⊔ Dt) ⊔ At) :=
    CFSG.Quasithin.B19Aux.isSolvable_sup_of_le_normalizer
      Subgroup.le_normalizer_of_normal
      (fun a ha b hb => Subtype.ext (hA.2.2.1.1 _ ha _ hb))
  let Y : Subgroup (MulAut W) := ((Ft ⊔ Dt) ⊔ At).map X.subtype
  have hYX : Y ≤ X := Subgroup.map_subtype_le _
  have hAY : A ≤ Y := fun a ha =>
    ⟨⟨a, hAX ha⟩, le_sup_right (a := Ft ⊔ Dt) (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  have hYsolv : Group.IsSolvable ↥Y :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective ((Ft ⊔ Dt) ⊔ At) X.subtype
        X.subtype_injective).symm.toMonoidHom)
      (Subgroup.equivMapOfInjective _ X.subtype X.subtype_injective).symm.injective
  have hFodd : Odd (Nat.card Ft) := B1.fitting_card_odd hO2'
  have hFstarN : (CFSG.generalizedFitting ↥X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := ↥X)).2
  have hO2Y : ∀ Q : Subgroup (MulAut W), Q ≤ Y → (Q.subgroupOf Y).Normal → IsPGroup 2 Q →
      Q = ⊥ := by
    intro Q hQY hQn hQ2
    have hQX : Q ≤ X := hQY.trans hYX
    have hQconj : ∀ y ∈ Y, ∀ q ∈ Q, y * q * y⁻¹ ∈ Q := by
      intro y hy q hq
      have h := hQn.conj_mem ⟨q, hQY hq⟩ (Subgroup.mem_subgroupOf.mpr hq) ⟨y, hy⟩
      simpa using Subgroup.mem_subgroupOf.mp h
    have hcent : ∀ q (hq : q ∈ Q), (⟨q, hQX hq⟩ : ↥X) ∈
        Subgroup.centralizer (CFSG.generalizedFitting ↥X : Set ↥X) := by
      intro q hq
      have hqY : (⟨q, hQX hq⟩ : ↥X) ∈ (Ft ⊔ Dt) ⊔ At := by
        obtain ⟨y, hy, hyq⟩ := hQY hq
        have : y = ⟨q, hQX hq⟩ := Subtype.ext hyq
        rw [← this]
        exact hy
      have hqF : (⟨q, hQX hq⟩ : ↥X) ∈ Subgroup.centralizer (Ft : Set ↥X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro f hf
        set qX : ↥X := ⟨q, hQX hq⟩
        have hcF' : qX * f * qX⁻¹ * f⁻¹ ∈ Ft :=
          Ft.mul_mem ((inferInstance : Ft.Normal).conj_mem f hf qX) (Ft.inv_mem hf)
        have hfY : (f : MulAut W) ∈ Y := ⟨f, le_sup_left (a := Ft ⊔ Dt)
          (le_sup_left (a := Ft) hf), rfl⟩
        have hcQ : ((qX * f * qX⁻¹ * f⁻¹ : ↥X) : MulAut W) ∈ Q := by
          have h1 : (f : MulAut W) * q⁻¹ * (f : MulAut W)⁻¹ ∈ Q :=
            hQconj _ hfY _ (Q.inv_mem hq)
          have h2 : ((qX * f * qX⁻¹ * f⁻¹ : ↥X) : MulAut W) =
              q * ((f : MulAut W) * q⁻¹ * (f : MulAut W)⁻¹) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, qX]
            group
          rw [h2]
          exact Q.mul_mem hq h1
        have hc1 : (qX * f * qX⁻¹ * f⁻¹ : ↥X) = 1 := by
          have hFodd' : Odd (Nat.card (Ft.map X.subtype)) := by
            rwa [Subgroup.card_map_of_injective X.subtype_injective]
          exact Subtype.ext (eq_one_of_isPGroup_two_of_odd hQ2 hFodd' hcQ ⟨_, hcF', rfl⟩)
        have : qX * f * qX⁻¹ = f := by
          calc qX * f * qX⁻¹ = qX * f * qX⁻¹ * f⁻¹ * f := by group
            _ = f := by rw [hc1, one_mul]
        calc f * qX = qX * f * qX⁻¹ * qX := by rw [this]
          _ = qX * f := by group
      have hqE : (⟨q, hQX hq⟩ : ↥X) ∈ Subgroup.centralizer (CFSG.layer ↥X : Set ↥X) :=
        (sup_le (sup_le hcF hcD) hcA) hqY
      have hz : Subgroup.zpowers (⟨q, hQX hq⟩ : ↥X) ≤
          Subgroup.centralizer (CFSG.generalizedFitting ↥X : Set ↥X) := by
        rw [Subgroup.le_centralizer_iff, CFSG.generalizedFitting, sup_le_iff]
        constructor
        · rw [← Subgroup.le_centralizer_iff, Subgroup.zpowers_le]; exact hqF
        · rw [← Subgroup.le_centralizer_iff, Subgroup.zpowers_le]; exact hqE
      exact hz (Subgroup.mem_zpowers _)
    by_contra hne
    have hQ2' : IsPGroup 2 ↥Q := hQ2
    obtain ⟨n, hn⟩ := hQ2'.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.eq_bot_of_card_eq Q (by simpa using hn))
    have h2 : 2 ∣ Nat.card Q := by
      rw [hn]
      exact dvd_pow_self 2 hn0
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) 2 h2
    have hx1 : (x : MulAut W) ≠ 1 := by
      intro h
      have : x = 1 := Subtype.ext h
      rw [this, orderOf_one] at hx
      omega
    have hxF : (⟨x, hQX x.2⟩ : ↥X) ∈ CFSG.generalizedFitting ↥X :=
      CFSG.centralizer_generalizedFitting_le ↥X (hcent x x.2)
    have hx2 : (⟨x, hQX x.2⟩ : ↥X) ^ 2 = 1 := by
      apply Subtype.ext
      have := pow_orderOf_eq_one x
      rw [hx] at this
      simpa using congrArg Subtype.val this
    have hmem : (⟨x, hQX x.2⟩ : ↥X) ∈ Coordinator.centerInvolutions (CFSG.generalizedFitting ↥X) :=
      ⟨hxF, fun y hy => (Subgroup.mem_centralizer_iff.mp (hcent x x.2) y hy).symm, hx2⟩
    rw [Coordinator.centerInvolutions_eq_bot hO2', Subgroup.mem_bot] at hmem
    exact hx1 (congrArg Subtype.val hmem)
  have hDY : Subgroup.closure (transvectionsIn X) ≤ Y := fun d hd =>
    ⟨⟨d, hDX hd⟩, le_sup_left (a := Ft ⊔ Dt) (le_sup_right (a := Ft)
      (Subgroup.mem_subgroupOf.mpr hd)), rfl⟩
  exact ⟨Y, hYX, hAY, hDY, hYsolv, hO2Y⟩

theorem le_closure_transvectionsIn_of_isFFStarOffender
    [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {X : Subgroup (MulAut W)} (hKX : CFSG.Open.IsKGroup ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut W), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥)
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥X) {A : Subgroup (MulAut W)}
    (hA : IsFFStarOffender X A) : A ≤ Subgroup.closure (transvectionsIn X) := by
  obtain ⟨Y, hYX, hAY, -, hYsolv, hO2Y⟩ := exists_solvable_le_of_isFFStarOffender hW hKX hO2 hcon hA
  exact le_closure_transvectionsIn_of_le_solvable hW hYX hAY hYsolv hO2Y hA

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81
