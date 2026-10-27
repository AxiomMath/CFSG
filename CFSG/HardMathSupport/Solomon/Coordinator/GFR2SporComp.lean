module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporHat

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open scoped commutatorElement

theorem false_of_perfect_of_central_mem_abelian {J : Type*} [Group J] [Finite J]
    (hperf : commutator J = ⊤) {P : Subgroup J} (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) {z : J}
    (hz : z ∈ Subgroup.center J) (hzP : z ∈ P) (hcop : Nat.Coprime P.index (orderOf z)) :
    z = 1 := by
  letI : CommGroup ↥P := { (inferInstance : Group ↥P) with
    mul_comm := fun a b => Subtype.ext (hP a a.2 b b.2) }
  haveI : P.FiniteIndex := Subgroup.finiteIndex_of_finite
  let ϕ : ↥P →* ↥P := MonoidHom.id ↥P
  have key : ∀ (k : ℕ) (g₀ : J), g₀⁻¹ * z ^ k * g₀ ∈ P → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk : z ^ k ∈ Subgroup.center J := Subgroup.pow_mem _ hz k
    rw [Subgroup.mem_center_iff] at hzk
    rw [mul_assoc, ← hzk g₀]
    group
  have h1 := MonoidHom.transfer_eq_pow ϕ z key
  have h2 : (MonoidHom.transfer ϕ) z = 1 := by
    have := Abelianization.commutator_subset_ker (MonoidHom.transfer ϕ)
    rw [hperf] at this
    exact this (Subgroup.mem_top z)
  rw [h2] at h1
  have h3 : z ^ P.index = 1 := by
    have := congrArg (fun w : ↥P => (w : J)) h1
    simpa [ϕ] using this.symm
  have h4 : orderOf z ∣ P.index := orderOf_dvd_of_pow_eq_one h3
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop.symm h4)

private theorem exists_conj_projOf (hOut : SporadicOuterLeTwo) {name : TauCeti.SporadicName}
    {Y : Type} [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y)
    (e : (Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.sporadic name).Group)
    {x : MulAut Y} (hxo : orderOf x = 3) :
    ∃ t : (TauCeti.CFSGIndex.sporadic name).Group, orderOf t = 3 ∧
      ∀ y : Y, projOf e (x y) = t * projOf e y * t⁻¹ := by
  have hx3 : x ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hperf : commutator Y = ⊤ := hq.1
  have hnab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hq
  have hs := hq.2
  have hcen : Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (Outer (Y ⧸ Subgroup.center Y)) ≤ 2 := hOut _ hs hnab name ⟨e⟩
  have hβ3 : (autCenterQuot Y x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  obtain ⟨s, hsβ, hs3⟩ := exists_conj_of_pow Nat.prime_three (by norm_num) hcen hout
    (autCenterQuot Y x) hβ3
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, map_one] at hsβ
    have h2 : x = 1 := autCenterQuot_injective_of_perfect hperf (by rw [← hsβ, map_one])
    rw [h2, orderOf_one] at hxo
    omega
  have hso : orderOf (e s) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hs3 hs1
  refine ⟨e s, hso, fun y => ?_⟩
  have h1 : (autCenterQuot Y x) (y : Y ⧸ Subgroup.center Y) = (x y : Y ⧸ Subgroup.center Y) := by
    rw [autCenterQuot_mk]
  rw [← hsβ, MulAut.conj_apply] at h1
  show e (QuotientGroup.mk (x y)) = e s * e (QuotientGroup.mk y) * (e s)⁻¹
  rw [← h1, map_mul, map_mul, map_inv]

private theorem fixSubgroup_conj_eq {Q : Type*} [Group Q] (t : Q) :
    fixSubgroup (MulAut.conj t) = Subgroup.centralizer ({t} : Set Q) := by
  ext y
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc y * t = (t * y * t⁻¹) * t := by rw [h]
      _ = t * y := by group
  · intro h
    rw [← h]; group

private theorem isComponentOf_of_glaPComponent {G : Type*} [Group G] {p : ℕ} {X L : Subgroup G}
    (hX : GLAPPrimeCoreOf p X = ⊥) (hL : GLAPComponent p X L) : IsComponentOf L X := by
  have hcore : GLAPPrimeCore p ↥X = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).1 hX
  refine ⟨hL.1, hL.2.1, ?_⟩
  have hq := hL.2.2.1.2.2
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcore]
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
    ((Subgroup.equivMapOfInjective (L.subgroupOf X) _ hinj).symm.trans
      (Subgroup.subgroupOfEquivOfLe hL.1)) hq

private theorem image_isComponentOf (hSpM : SporadicMultipliers) (hOut : SporadicOuterLeTwo)
    {name : TauCeti.SporadicName}
    (hO : OPrimeCoreTrivialAt 3 (TauCeti.CFSGIndex.sporadic name).Group)
    {Y : Type} [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y) (hcore : GLAPPrimeCore 3 Y = ⊥)
    (e : (Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.sporadic name).Group)
    {x : MulAut Y} (hxo : orderOf x = 3) {J₁ : Subgroup Y}
    (hJ₁ : GLAPComponent 3 (Lemma510Ns.fixSub x) J₁) :
    ∃ t : (TauCeti.CFSGIndex.sporadic name).Group, orderOf t = 3 ∧
      IsComponentOf (J₁.map (projOf e)) (Subgroup.centralizer ({t} : Set _)) ∧
      GLAPPrimeCore 3 ↥J₁ = ⊥ := by
  haveI : Finite (TauCeti.CFSGIndex.sporadic name).Group := Finite.of_equiv _ e.toEquiv
  obtain ⟨t, ht, hrel⟩ := exists_conj_projOf hOut hq e hxo
  refine ⟨t, ht, ?_⟩
  have hker : (projOf e).ker ≤ Subgroup.center Y := (ker_projOf e).le
  have hαβ : ∀ k, projOf e (x k) = (MulAut.conj t) (projOf e k) := fun k => by
    rw [hrel k, MulAut.conj_apply]
  have hI : GLAPComponent 3 (fixSubgroup (MulAut.conj t)) (J₁.map (projOf e)) :=
    glaPComponent_map_fixSubgroup (projOf e) hker x (MulAut.conj t) hαβ (projOf_surjective e)
      Nat.prime_three hJ₁
  rw [fixSubgroup_conj_eq] at hI
  have hOt := hO t ht
  have hIc : IsComponentOf (J₁.map (projOf e)) (Subgroup.centralizer ({t} : Set _)) :=
    isComponentOf_of_glaPComponent hOt hI
  refine ⟨hIc, ?_⟩
  set N : Subgroup Y := GLAPPrimeCoreOf 3 J₁ with hNdef
  have hNJ : N ≤ J₁ := Subgroup.map_subtype_le _
  have hZcard : Nat.card (Subgroup.center Y) ∣ 3 := card_center_le_three hSpM hq hcore e
  have hM : N.map (projOf e) ≤ GLAPPrimeCoreOf 3 (J₁.map (projOf e)) := by
    refine CFSG.HardMathSupport.Timmesfeld.Proving.le_GLAPPrimeCoreOf_of_normal
      (Subgroup.map_mono hNJ) ?_ ?_
    · rintro _ ⟨j, hj, rfl⟩ _ ⟨n, hn, rfl⟩
      exact ⟨j * n * j⁻¹, CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_conj_mem j hj n hn,
        by simp⟩
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd N (projOf e))
        (CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf Nat.prime_three J₁)
  have hIO : GLAPPrimeCoreOf 3 (J₁.map (projOf e)) ≤
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({t} : Set _)) :=
    LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal 3 hIc.2.1
  have hM0 : N.map (projOf e) = ⊥ := le_bot_iff.1 (hM.trans (hIO.trans hOt.le))
  have hNZ : N ≤ Subgroup.center Y := by
    intro n hn
    rw [← ker_projOf e, MonoidHom.mem_ker]
    have h1 : projOf e n ∈ N.map (projOf e) := ⟨n, hn, rfl⟩
    rw [hM0] at h1
    simpa using h1
  have h1 : Nat.card N ∣ 3 := (Subgroup.card_dvd_of_le hNZ).trans hZcard
  have h2 : Nat.Coprime 3 (Nat.card N) :=
    CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf Nat.prime_three J₁
  have hN1 : Nat.card N = 1 := Nat.Coprime.eq_one_of_dvd h2.symm h1
  have hNbot : N = ⊥ := Subgroup.eq_bot_of_card_eq _ hN1
  exact (Subgroup.map_eq_bot_iff_of_injective _ J₁.subtype_injective).1 hNbot

private theorem commutator_eq_top_of_mulEquiv {X X' : Type*} [Group X] [Group X'] (f : X ≃* X')
    (h : commutator X = ⊤) : commutator X' = ⊤ := by
  rw [commutator_def] at h ⊢
  have h1 := Subgroup.map_commutator (⊤ : Subgroup X) ⊤ f.toMonoidHom
  rw [h, Subgroup.map_top_of_surjective _ f.surjective] at h1
  exact h1.symm

private theorem map_center_mulEquiv {X X' : Type*} [Group X] [Group X'] (f : X ≃* X') :
    (Subgroup.center X).map f.toMonoidHom = Subgroup.center X' := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩ g
    obtain ⟨g', rfl⟩ := f.surjective g
    show f g' * f x = f x * f g'
    rw [← map_mul, ← map_mul, hx g']
  · intro h
    refine ⟨f.symm y, fun g => ?_, by simp⟩
    apply f.injective
    simp [h (f g)]

private theorem hat_of_mulEquiv {X X' Q : Type*} [Group X] [Group X'] [Group Q] (f : X ≃* X')
    (h : commutator X = ⊤ ∧ Nat.card (Subgroup.center X) = 3 ∧
      Nonempty ((X ⧸ Subgroup.center X) ≃* Q)) :
    commutator X' = ⊤ ∧ Nat.card (Subgroup.center X') = 3 ∧
      Nonempty ((X' ⧸ Subgroup.center X') ≃* Q) := by
  obtain ⟨hc, hz, ⟨g⟩⟩ := h
  refine ⟨commutator_eq_top_of_mulEquiv f hc, ?_,
    ⟨(QuotientGroup.congr (Subgroup.center X) (Subgroup.center X') f
      (map_center_mulEquiv f)).symm.trans g⟩⟩
  rw [← map_center_mulEquiv f, Subgroup.card_map_of_injective f.injective, hz]

private theorem isHatSix_of_mulEquiv {X X' : Type*} [Group X] [Group X'] (f : X ≃* X')
    (h : IsHatSix X) : IsHatSix X' := hat_of_mulEquiv f h

private theorem isHatON_of_mulEquiv {X X' : Type*} [Group X] [Group X'] (f : X ≃* X')
    (h : IsHatON X) : IsHatON X' := hat_of_mulEquiv f h

private noncomputable def restrictProj {Y S : Type*} [Group Y] [Group S] (π : Y →* S)
    (J : Subgroup Y) : ↥J →* ↥(J.map π) :=
  (π.domRestrict J).codRestrict (J.map π) (fun j => ⟨j, j.2, rfl⟩)

private theorem restrictProj_coe {Y S : Type*} [Group Y] [Group S] (π : Y →* S) (J : Subgroup Y)
    (j : ↥J) : ((restrictProj π J j : ↥(J.map π)) : S) = π j := rfl

private theorem restrictProj_surjective {Y S : Type*} [Group Y] [Group S] (π : Y →* S)
    (J : Subgroup Y) : Function.Surjective (restrictProj π J) := by
  rintro ⟨_, j, hj, rfl⟩
  exact ⟨⟨j, hj⟩, Subtype.ext rfl⟩

private theorem mem_ker_restrictProj {Y S : Type*} [Group Y] [Group S] (π : Y →* S)
    (J : Subgroup Y) (j : ↥J) : j ∈ (restrictProj π J).ker ↔ (j : Y) ∈ π.ker := by
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro h
    have := congrArg Subtype.val h
    simpa [restrictProj_coe] using this
  · intro h
    exact Subtype.ext (by simpa [restrictProj_coe] using h)

private theorem ker_restrictProj_projOf {Y S : Type*} [Group Y] [Group S]
    (e : (Y ⧸ Subgroup.center Y) ≃* S) (J : Subgroup Y) :
    (restrictProj (projOf e) J).ker = (Subgroup.center Y).subgroupOf J := by
  ext j
  rw [mem_ker_restrictProj, ker_projOf, Subgroup.mem_subgroupOf]

private theorem nonempty_mulEquiv_map_of_inf_eq_bot {Y S : Type*} [Group Y] [Group S]
    (e : (Y ⧸ Subgroup.center Y) ≃* S) {J : Subgroup Y} (h : J ⊓ Subgroup.center Y = ⊥) :
    Nonempty (↥J ≃* ↥(J.map (projOf e))) := by
  refine ⟨MulEquiv.ofBijective (restrictProj (projOf e) J)
    ⟨?_, restrictProj_surjective _ _⟩⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro j hj
  rw [ker_restrictProj_projOf, Subgroup.mem_subgroupOf] at hj
  have h1 : (j : Y) ∈ J ⊓ Subgroup.center Y := ⟨j.2, hj⟩
  rw [h, Subgroup.mem_bot] at h1
  exact (Subgroup.mem_bot).2 (Subtype.ext h1)

private theorem nonempty_mulEquiv_alt_of_isHatSix {Y S : Type*} [Group Y] [Group S] [Finite Y]
    (e : (Y ⧸ Subgroup.center Y) ≃* S) {J : Subgroup Y} (hZJ : Subgroup.center Y ≤ J)
    (hZ : Nat.card (Subgroup.center Y) = 3) (hJ : IsHatSix ↥J) :
    Nonempty (↥(J.map (projOf e)) ≃* ↥(alternatingGroup (Fin 6))) := by
  obtain ⟨-, hz, ⟨g⟩⟩ := hJ
  have hker := ker_restrictProj_projOf e J
  have hcard1 : Nat.card ↥((Subgroup.center Y).subgroupOf J) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZJ).toEquiv]; exact hZ
  have hle : (restrictProj (projOf e) J).ker ≤ Subgroup.center ↥J := by
    rw [hker]
    intro j hj
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (Subgroup.mem_center_iff.1 (Subgroup.mem_subgroupOf.1 hj) (k : Y))
  have heq : (restrictProj (projOf e) J).ker = Subgroup.center ↥J :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hz, hker, hcard1])
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective (restrictProj (projOf e) J)
    (restrictProj_surjective _ _)).symm.trans ((QuotientGroup.quotientMulEquivOfEq heq).trans g)⟩

private theorem nonempty_mulEquiv_barOf {G : Type*} [Group G] {J : Subgroup G}
    (h : GLAPPrimeCore 3 ↥J = ⊥) : Nonempty (↥J ≃* barOf 3 J) :=
  ⟨(QuotientGroup.quotientBot (G := ↥J)).symm.trans (QuotientGroup.quotientMulEquivOfEq h.symm)⟩

private theorem nine_dvd_card_closure {S : Type*} [Group S] {a b : S} (hab : a * b = b * a)
    (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) (hba : b ∉ Subgroup.zpowers a) [Finite S] :
    9 ∣ Nat.card ↥(Subgroup.closure ({a, b} : Set S)) := by
  set E : Subgroup S := Subgroup.closure ({a, b} : Set S) with hE
  haveI : IsMulCommutative ↥E := by
    refine Subgroup.isMulCommutative_closure ?_
    intro u hu v hv _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact Commute.refl _
    · exact hab
    · exact hab.symm
    · exact Commute.refl _
  have haE : a ∈ E := Subgroup.subset_closure (by simp)
  have hbE : b ∈ E := Subgroup.subset_closure (by simp)
  set H : Subgroup ↥E := (Subgroup.zpowers a).subgroupOf E with hH
  have hle : Subgroup.zpowers a ≤ E := (Subgroup.zpowers_le).2 haE
  have hHcard : Nat.card H = 3 := by
    rw [hH, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, ha3]
  have hq3 : orderOf (QuotientGroup.mk (⟨b, hbE⟩ : ↥E) : ↥E ⧸ H) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow]
      have : (⟨b, hbE⟩ : ↥E) ^ 3 = 1 := Subtype.ext (by simpa [hb3] using pow_orderOf_eq_one b)
      rw [this]; exact QuotientGroup.mk_one _
    · intro h
      rw [QuotientGroup.eq_one_iff] at h
      exact hba (Subgroup.mem_subgroupOf.1 h)
  have h3 : 3 ∣ Nat.card (↥E ⧸ H) := hq3 ▸ orderOf_dvd_natCard _
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup H, hHcard]
  have h9 := Nat.mul_dvd_mul_right h3 3
  simpa using h9

private theorem false_of_commuting_lifts {Y S : Type*} [Group Y] [Group S] [Finite Y]
    (e : (Y ⧸ Subgroup.center Y) ≃* S) (hZ : Nat.card (Subgroup.center Y) = 3)
    {J : Subgroup Y} (hperf : commutator ↥J = ⊤) (hcard : Nat.card ↥J = 1080)
    (hZJ : Subgroup.center Y ≤ J) {a b g : S} (ha : a ∈ J.map (projOf e))
    (hb : b ∈ J.map (projOf e)) (hab : a * b = b * a) (ha3 : orderOf a = 3) (hb3 : orderOf b = 3)
    (hba : b ∉ Subgroup.zpowers a) (hga : g * a * g⁻¹ = a) (hgb : g * b * g⁻¹ = b⁻¹) : False := by
  obtain ⟨a₁, ha₁, rfl⟩ := ha
  obtain ⟨b₁, hb₁, rfl⟩ := hb
  obtain ⟨g₁, rfl⟩ := projOf_surjective e g
  have hker := ker_projOf e
  have hcen : ∀ w ∈ Subgroup.center Y, ∀ y : Y, w * y = y * w := fun w hw y =>
    (Subgroup.mem_center_iff.1 hw y).symm
  have hc : ⁅a₁, b₁⁆ ∈ Subgroup.center Y := by
    rw [← hker, MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hab
  set c : Y := ⁅a₁, b₁⁆ with hcdef
  have hcc : ∀ y : Y, c * y = y * c := hcen c hc
  have hz1 : a₁⁻¹ * (g₁ * a₁ * g₁⁻¹) ∈ Subgroup.center Y := by
    rw [← hker, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hga]
    group
  have hz2 : b₁ * (g₁ * b₁ * g₁⁻¹) ∈ Subgroup.center Y := by
    rw [← hker, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hgb]
    group
  set z₁ : Y := a₁⁻¹ * (g₁ * a₁ * g₁⁻¹) with hz₁
  set z₂ : Y := b₁ * (g₁ * b₁ * g₁⁻¹) with hz₂
  have e1 : g₁ * a₁ * g₁⁻¹ = a₁ * z₁ := by rw [hz₁]; group
  have e2 : g₁ * b₁ * g₁⁻¹ = b₁⁻¹ * z₂ := by rw [hz₂]; group
  have hconj : g₁ * c * g₁⁻¹ = ⁅a₁ * z₁, b₁⁻¹ * z₂⁆ := by
    have : g₁ * c * g₁⁻¹ = ⁅g₁ * a₁ * g₁⁻¹, g₁ * b₁ * g₁⁻¹⁆ := by
      simp only [hcdef, commutatorElement_def]; group
    rw [this, e1, e2]
  have hcomm1 : ⁅a₁ * z₁, b₁⁻¹ * z₂⁆ = ⁅a₁, b₁⁻¹⁆ :=
    commutatorElement_mul_mul' (hcen z₁ hz1 _) (hcen z₁ hz1 z₂) (hcen z₂ hz2 a₁)
  have hinv : ⁅a₁, b₁⁻¹⁆ = c⁻¹ := by
    have h1 : a₁ * b₁⁻¹ * a₁⁻¹ = b₁⁻¹ * c⁻¹ := by
      rw [hcdef, commutatorElement_def]; group
    have h2 : ⁅a₁, b₁⁻¹⁆ = a₁ * b₁⁻¹ * a₁⁻¹ * b₁ := by
      rw [commutatorElement_def, inv_inv]
    rw [h2, h1]
    have h3 := hcen c⁻¹ (Subgroup.inv_mem _ hc) b₁
    calc b₁⁻¹ * c⁻¹ * b₁ = b₁⁻¹ * (c⁻¹ * b₁) := by group
      _ = b₁⁻¹ * (b₁ * c⁻¹) := by rw [h3]
      _ = c⁻¹ := by group
  have hgc : g₁ * c * g₁⁻¹ = c := by rw [← hcc g₁]; group
  have hcc2 : c = c⁻¹ := by
    calc c = g₁ * c * g₁⁻¹ := hgc.symm
      _ = ⁅a₁ * z₁, b₁⁻¹ * z₂⁆ := hconj
      _ = ⁅a₁, b₁⁻¹⁆ := hcomm1
      _ = c⁻¹ := hinv
  have hc3 : c ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥(Subgroup.center Y)) (x := ⟨c, hc⟩)
    rw [hZ] at h
    exact congrArg Subtype.val h
  have hc1 : c = 1 := by
    have h2 : c * c = 1 := by
      calc c * c = c * c⁻¹ := by rw [← hcc2]
        _ = 1 := mul_inv_cancel c
    calc c = c ^ 3 * (c * c)⁻¹ := by group
      _ = 1 := by rw [hc3, h2]; simp
  have hab1 : a₁ * b₁ = b₁ * a₁ := commutatorElement_eq_one_iff_mul_comm.1 (hcdef ▸ hc1)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨zz, hzzord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center Y)) 3
    (by rw [hZ])
  set z : Y := (zz : Y) with hzdef
  have hzc : z ∈ Subgroup.center Y := zz.2
  have hzord : orderOf z = 3 := by rw [hzdef, Subgroup.orderOf_coe]; exact hzzord
  have hzJ : z ∈ J := hZJ hzc
  set P₀ : Subgroup Y := Subgroup.closure ({a₁, b₁, z} : Set Y) with hP₀
  haveI : IsMulCommutative ↥P₀ := by
    refine Subgroup.isMulCommutative_closure ?_
    intro u hu v hv _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact Commute.refl _
    · exact hab1
    · exact (hcen z hzc _).symm
    · exact hab1.symm
    · exact Commute.refl _
    · exact (hcen z hzc _).symm
    · exact hcen z hzc _
    · exact hcen z hzc _
    · exact Commute.refl _
  have ha₁P : a₁ ∈ P₀ := Subgroup.subset_closure (by simp)
  have hb₁P : b₁ ∈ P₀ := Subgroup.subset_closure (by simp)
  have hzP : z ∈ P₀ := Subgroup.subset_closure (by simp)
  have hP₀J : P₀ ≤ J := by
    rw [hP₀, Subgroup.closure_le]
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact ha₁
    · exact hb₁
    · exact hzJ
  have hPZ : Nat.card ↥(P₀ ⊓ Subgroup.center Y) = 3 := by
    have h1 : Subgroup.zpowers z ≤ P₀ ⊓ Subgroup.center Y :=
      (Subgroup.zpowers_le).2 ⟨hzP, hzc⟩
    have h2 : 3 ∣ Nat.card ↥(P₀ ⊓ Subgroup.center Y) := by
      have := Subgroup.card_dvd_of_le h1
      rwa [Nat.card_zpowers, hzord] at this
    have h3 : Nat.card ↥(P₀ ⊓ Subgroup.center Y) ∣ 3 :=
      hZ ▸ Subgroup.card_dvd_of_le inf_le_right
    exact Nat.dvd_antisymm h3 h2
  have hmap9 : 9 ∣ Nat.card ↥(P₀.map (projOf e)) := by
    have hE : Subgroup.closure ({projOf e a₁, projOf e b₁} : Set S) ≤ P₀.map (projOf e) := by
      rw [Subgroup.closure_le]
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl
      · exact ⟨a₁, ha₁P, rfl⟩
      · exact ⟨b₁, hb₁P, rfl⟩
    haveI : Finite S := Finite.of_surjective (projOf e) (projOf_surjective e)
    exact (nine_dvd_card_closure hab ha3 hb3 hba).trans (Subgroup.card_dvd_of_le hE)
  have h27 : 27 ∣ Nat.card ↥P₀ := by
    have := card_map_projOf_mul e P₀
    rw [hPZ] at this
    rw [← this]
    exact Nat.mul_dvd_mul hmap9 (dvd_refl 3) |> fun h => by simpa using h
  set P : Subgroup ↥J := P₀.subgroupOf J with hPdef
  have hPcard : Nat.card P = Nat.card P₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀J).toEquiv
  obtain ⟨m, hm⟩ := h27
  have hidx : P.index * Nat.card P = Nat.card ↥J := Subgroup.index_mul_card P
  have hidx40 : P.index ∣ 40 := by
    rw [hPcard, hm, hcard] at hidx
    have h1 : 27 * (P.index * m) = 27 * 40 := by
      calc 27 * (P.index * m) = P.index * (27 * m) := by ring
        _ = 1080 := hidx
        _ = 27 * 40 := by norm_num
    exact Dvd.intro m (Nat.eq_of_mul_eq_mul_left (by norm_num) h1)
  have hzorder : orderOf (⟨z, hzJ⟩ : ↥J) = 3 := by
    rw [← hzord]; exact Subgroup.orderOf_mk z hzJ
  have hcop : Nat.Coprime P.index (orderOf (⟨z, hzJ⟩ : ↥J)) := by
    rw [hzorder]
    exact Nat.Coprime.coprime_dvd_left hidx40 (by norm_num)
  have hP : ∀ u ∈ P, ∀ v ∈ P, u * v = v * u := by
    intro u hu v hv
    have hu' : (u : Y) ∈ P₀ := Subgroup.mem_subgroupOf.1 hu
    have hv' : (v : Y) ∈ P₀ := Subgroup.mem_subgroupOf.1 hv
    have h := congrArg Subtype.val
      (IsMulCommutative.is_comm.comm (⟨(u : Y), hu'⟩ : ↥P₀) ⟨(v : Y), hv'⟩)
    exact Subtype.ext h
  have hzcent : (⟨z, hzJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcen z hzc g).symm
  have hz1 := false_of_perfect_of_central_mem_abelian hperf hP hzcent
    (Subgroup.mem_subgroupOf.2 hzP) hcop
  have hz1' : z = 1 := congrArg Subtype.val hz1
  rw [hz1', orderOf_one] at hzord
  omega

private theorem card_center_eq_three {Y : Type*} [Group Y] [Finite Y] {J : Subgroup Y}
    (h3 : Nat.card (Subgroup.center Y) ∣ 3) (hne : J ⊓ Subgroup.center Y ≠ ⊥) :
    Nat.card (Subgroup.center Y) = 3 := by
  have h1 : Nat.card ↥(J ⊓ Subgroup.center Y) ∣ Nat.card (Subgroup.center Y) :=
    Subgroup.card_dvd_of_le inf_le_right
  have h2 : Nat.card ↥(J ⊓ Subgroup.center Y) ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq _ h)
  rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
  · exfalso
    apply h2
    rw [h] at h1
    exact Nat.dvd_one.1 h1
  · exact h

private theorem center_le_of_inf_ne_bot {Y : Type*} [Group Y] [Finite Y] {J : Subgroup Y}
    (hZ : Nat.card (Subgroup.center Y) = 3) (hne : J ⊓ Subgroup.center Y ≠ ⊥) :
    Subgroup.center Y ≤ J := by
  have h1 : Nat.card ↥(J ⊓ Subgroup.center Y) ∣ 3 := by
    rw [← hZ]; exact Subgroup.card_dvd_of_le inf_le_right
  have h2 : Nat.card ↥(J ⊓ Subgroup.center Y) ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq _ h)
  have h3 : Nat.card ↥(J ⊓ Subgroup.center Y) = 3 :=
    ((Nat.dvd_prime Nat.prime_three).1 h1).resolve_left h2
  have h4 : J ⊓ Subgroup.center Y = Subgroup.center Y :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hZ])
  exact inf_eq_right.1 h4

private theorem centralizer_ne_top {Y S : Type*} [Group Y] [Group S]
    (hq : CFSG.Open.IsQuasisimple Y) (e : (Y ⧸ Subgroup.center Y) ≃* S) {t : S} (ht : t ≠ 1) :
    Subgroup.centralizer ({t} : Set S) ≠ ⊤ := by
  intro htop
  haveI := hq.2
  have hnab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hq
  have hcen : Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hmem : e.symm t ∈ Subgroup.center (Y ⧸ Subgroup.center Y) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    have h1 : e g ∈ Subgroup.centralizer ({t} : Set S) := htop ▸ Subgroup.mem_top _
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    simpa using h1
  rw [hcen, Subgroup.mem_bot] at hmem
  exact ht (by simpa using congrArg e hmem)

private theorem inf_center_eq_bot_of_reflections (hSpM : SporadicMultipliers)
    (hOut : SporadicOuterLeTwo) {name : TauCeti.SporadicName}
    (hO : OPrimeCoreTrivialAt 3 (TauCeti.CFSGIndex.sporadic name).Group)
    (hB : 3 ∣ sporadicMultiplierOrder name →
      ∀ s : (TauCeti.CFSGIndex.sporadic name).Group, orderOf s = 3 →
      ∀ K : Subgroup (TauCeti.CFSGIndex.sporadic name).Group,
        CFSG.Open.IsComponentOf K (Subgroup.centralizer ({s} : Set _)) →
        Nonempty (↥K ≃* alternatingGroup (Fin 6)) →
        ∃ a ∈ K, ∃ b ∈ K, ∃ g : (TauCeti.CFSGIndex.sporadic name).Group,
          a * b = b * a ∧ orderOf a = 3 ∧ orderOf b = 3 ∧ b ∉ Subgroup.zpowers a ∧
          g * a * g⁻¹ = a ∧ g * b * g⁻¹ = b⁻¹)
    (Y : Type) [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y)
    (hcore : GLAPPrimeCore 3 Y = ⊥) (hZ : Nat.card (Subgroup.center Y) = 3)
    (e : (Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.sporadic name).Group)
    (x : MulAut Y) (hxo : orderOf x = 3) (J₁ : Subgroup Y)
    (hJ₁ : GLAPComponent 3 (Lemma510Ns.fixSub x) J₁) (hSix : IsHatSix (barOf 3 J₁)) :
    J₁ ⊓ Subgroup.center Y = ⊥ := by
  by_contra hne
  obtain ⟨t, ht, hIc, hN⟩ := image_isComponentOf hSpM hOut hO hq hcore e hxo hJ₁
  obtain ⟨ψ⟩ := nonempty_mulEquiv_barOf hN
  have hSix' : IsHatSix ↥J₁ := isHatSix_of_mulEquiv ψ.symm hSix
  have hZJ : Subgroup.center Y ≤ J₁ := center_le_of_inf_ne_bot hZ hne
  have hm : 3 ∣ sporadicMultiplierOrder name := by
    have := card_center_dvd_mult hSpM hq name e
    rwa [hZ] at this
  obtain ⟨a, ha, b, hb, g, hab, ha3, hb3, hba, hga, hgb⟩ :=
    hB hm t ht _ hIc (nonempty_mulEquiv_alt_of_isHatSix e hZJ hZ hSix')
  exact false_of_commuting_lifts e hZ hSix'.1 (gfr2_card_isHatSix hSix') hZJ ha hb hab ha3 hb3 hba
    hga hgb

theorem sporNoPumpup_of_components_cover (hSpM : SporadicMultipliers)
    (hOG : UniquenessMaximal.InputONGroup) (hOut : SporadicOuterLeTwo)
    {name : TauCeti.SporadicName}
    (hOrd : Nat.card (TauCeti.CFSGIndex.sporadic name).Group = sporOrd name)
    (hO : OPrimeCoreTrivialAt 3 (TauCeti.CFSGIndex.sporadic name).Group)
    (hA : ∀ s : (TauCeti.CFSGIndex.sporadic name).Group, orderOf s = 3 →
      ∀ K : Subgroup (TauCeti.CFSGIndex.sporadic name).Group,
        CFSG.Open.IsComponentOf K (Subgroup.centralizer ({s} : Set _)) →
        IsHatSix ↥K ∨ (name = .M ∧ IsHatON ↥K) → False)
    (hB : ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
      GLAPPrimeCore 3 Y = ⊥ → Nat.card (Subgroup.center Y) = 3 →
      Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
      ∀ x : MulAut Y, orderOf x = 3 → ∀ J₁ : Subgroup Y,
        GLAPComponent 3 (Lemma510Ns.fixSub x) J₁ → IsHatSix (barOf 3 J₁) →
        J₁ ⊓ Subgroup.center Y = ⊥) :
    SporNoPumpup name := by
  intro Y _ _ hq _ hcore ⟨e⟩ x hxo J₁ hJ₁ hty
  haveI : Finite (TauCeti.CFSGIndex.sporadic name).Group := Finite.of_equiv _ e.toEquiv
  obtain ⟨t, ht, hIc, hN⟩ := image_isComponentOf hSpM hOut hO hq hcore e hxo hJ₁
  obtain ⟨ψ⟩ := nonempty_mulEquiv_barOf hN
  have hZ3 : Nat.card (Subgroup.center Y) ∣ 3 := card_center_le_three hSpM hq hcore e
  rcases hty with hON | hSix
  ·
    have hON' : IsHatON ↥J₁ := isHatON_of_mulEquiv ψ.symm hON
    have hJcard : Nat.card ↥J₁ = 3 * orderON := by
      have h1 := (UniquenessMaximal.isSimple_card_of_isHatON hOG hON').2
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J₁), h1, hON'.2.1,
        mul_comm]
    have hz13 : Nat.card (Subgroup.center Y) = 1 ∨ Nat.card (Subgroup.center Y) = 3 :=
      (Nat.dvd_prime Nat.prime_three).1 hZ3
    have hzd := card_center_dvd_mult hSpM hq name e
    have hcardY : Nat.card Y = Nat.card (Subgroup.center Y) * sporOrd name := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y)
      rw [Nat.card_congr e.toEquiv, hOrd] at h1
      rw [h1, mul_comm]
    have hdvd : 3 * orderON ∣ Nat.card (Subgroup.center Y) * sporOrd name := by
      rw [← hcardY, ← hJcard]
      exact Subgroup.card_subgroup_dvd_card J₁
    rcases (spor_arith name _ hz13 hzd).1 hdvd with ⟨hname, hz3⟩ | ⟨hname, hz1⟩
    ·
      exfalso
      have hSON : Nat.card (TauCeti.CFSGIndex.sporadic name).Group = orderON := by
        rw [hname]; exact hOG.2
      have hlt : Nat.card ↥(Subgroup.centralizer ({t} : Set _)) <
          Nat.card (TauCeti.CFSGIndex.sporadic name).Group :=
        lt_of_le_of_ne (Subgroup.card_le_card_group _) fun h =>
          centralizer_ne_top hq e (fun h1 => by rw [h1, orderOf_one] at ht; omega)
            (Subgroup.eq_top_of_card_eq _ h)
      have hIle : Nat.card ↥(J₁.map (projOf e)) ≤
          Nat.card ↥(Subgroup.centralizer ({t} : Set _)) := Subgroup.card_le_of_le hIc.1
      have hk : Nat.card ↥(J₁ ⊓ Subgroup.center Y) ≤ 3 := by
        have := Subgroup.card_le_of_le (inf_le_right : J₁ ⊓ Subgroup.center Y ≤ Subgroup.center Y)
        omega
      have hmul := card_map_projOf_mul e J₁
      have hmul2 : Nat.card ↥(J₁.map (projOf e)) * Nat.card ↥(J₁ ⊓ Subgroup.center Y) ≤
          Nat.card ↥(J₁.map (projOf e)) * 3 := Nat.mul_le_mul_left _ hk
      omega
    ·
      have hbot : Subgroup.center Y = ⊥ := Subgroup.eq_bot_of_card_eq _ hz1
      obtain ⟨ρ⟩ := nonempty_mulEquiv_map_of_inf_eq_bot e (J := J₁)
        (by rw [hbot]; exact inf_bot_eq _)
      exact hA t ht _ hIc (Or.inr ⟨hname, isHatON_of_mulEquiv ρ hON'⟩)
  ·
    have hSix' : IsHatSix ↥J₁ := isHatSix_of_mulEquiv ψ.symm hSix
    by_cases hJZ : J₁ ⊓ Subgroup.center Y = ⊥
    · obtain ⟨ρ⟩ := nonempty_mulEquiv_map_of_inf_eq_bot e hJZ
      exact hA t ht _ hIc (Or.inl (isHatSix_of_mulEquiv ρ hSix'))
    · exact hJZ (hB Y hq hcore (card_center_eq_three hZ3 hJZ) ⟨e⟩ x hxo J₁ hJ₁ hSix)

theorem sporNoPumpup_of_components (hSpM : SporadicMultipliers)
    (hOG : UniquenessMaximal.InputONGroup) (hOut : SporadicOuterLeTwo)
    {name : TauCeti.SporadicName}
    (hOrd : Nat.card (TauCeti.CFSGIndex.sporadic name).Group = sporOrd name)
    (hO : OPrimeCoreTrivialAt 3 (TauCeti.CFSGIndex.sporadic name).Group)
    (hA : ∀ s : (TauCeti.CFSGIndex.sporadic name).Group, orderOf s = 3 →
      ∀ K : Subgroup (TauCeti.CFSGIndex.sporadic name).Group,
        CFSG.Open.IsComponentOf K (Subgroup.centralizer ({s} : Set _)) →
        IsHatSix ↥K ∨ (name = .M ∧ IsHatON ↥K) → False)
    (hB : 3 ∣ sporadicMultiplierOrder name →
      ∀ s : (TauCeti.CFSGIndex.sporadic name).Group, orderOf s = 3 →
      ∀ K : Subgroup (TauCeti.CFSGIndex.sporadic name).Group,
        CFSG.Open.IsComponentOf K (Subgroup.centralizer ({s} : Set _)) →
        Nonempty (↥K ≃* alternatingGroup (Fin 6)) →
        ∃ a ∈ K, ∃ b ∈ K, ∃ g : (TauCeti.CFSGIndex.sporadic name).Group,
          a * b = b * a ∧ orderOf a = 3 ∧ orderOf b = 3 ∧ b ∉ Subgroup.zpowers a ∧
          g * a * g⁻¹ = a ∧ g * b * g⁻¹ = b⁻¹) :
    SporNoPumpup name :=
  sporNoPumpup_of_components_cover hSpM hOG hOut hOrd hO hA
    (fun Y _ _ hq hcore hZ ⟨e⟩ x hxo J₁ hJ₁ hSix =>
      inf_center_eq_bot_of_reflections hSpM hOut hO hB Y hq hcore hZ e x hxo J₁ hJ₁ hSix)

end CFSG.HardMathSupport.Solomon.Coordinator
