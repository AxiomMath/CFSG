module

public import CFSG.ClassicalInvolution.Q3.TL4S289Lnk
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExact
public import CFSG.ClassicalInvolution.Q3.TL4VtxFam

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

@[expose] def LinkDichSyl {Y : Type} [Group Y] (R : Subgroup Y) (t : Y) : Prop :=
  ∀ M ∈ restrictFamily (coreLinkFam R t) (linkGrp R t), ∀ a : ↥(linkGrp R t),
    IsUniqueInvolution M a → ∀ P : Subgroup ↥(linkGrp R t), IsSylow2In P M →
      ∀ β : MulAut ↥(linkGrp R t), β * β = 1 → (∀ x ∈ P, β x = x) →
        β = 1 ∨ β = MulAut.conj a

namespace S289

section Coprime

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_oddCoreOf {J : Subgroup G} {c : G} (hc : c ∈ Subgroup.normalizer (J : Set G))
    {o : G} (ho : o ∈ oddCoreOf J) : c * o * c⁻¹ ∈ oddCoreOf J := by
  have h1 := Vtx.oddCoreOf_map_of_inj (MulAut.conj c).toMonoidHom (MulAut.conj c).injective J
  have h2 : J.map (MulAut.conj c).toMonoidHom = J := mem_normalizer_iff_conjSub_eq.mp hc
  rw [h2] at h1
  rw [h1]
  exact ⟨o, ho, rfl⟩

theorem commutator_mem_oddCoreOf_of_sylow {J T : Subgroup G}
    (h2 : IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J)) (hT : IsSylow2In T J) {c : G}
    (hcJ : c ∈ Subgroup.normalizer (J : Set G)) (hcT : T ≤ Subgroup.centralizer ({c} : Set G))
    {x : G} (hx : x ∈ J) : ⁅c, x⁆ ∈ oddCoreOf J := by
  obtain ⟨r, hr, o, ho, rfl⟩ := Q3.PhilipHall.Frame.TwinExact.mem_mul_oddCore_of_sylow h2 hT x hx
  have hrc : r * c = c * r := Subgroup.mem_centralizer_singleton_iff.mp (hcT hr)
  have h1 : c * o * c⁻¹ * o⁻¹ ∈ oddCoreOf J :=
    (oddCoreOf J).mul_mem (conj_mem_oddCoreOf hcJ ho) ((oddCoreOf J).inv_mem ho)
  have h3 := conj_mem_oddCoreOf (Subgroup.le_normalizer (hT.1 hr)) h1
  have e : ⁅c, r * o⁆ = r * (c * o * c⁻¹ * o⁻¹) * r⁻¹ := by
    rw [commutatorElement_def]
    calc c * (r * o) * c⁻¹ * (r * o)⁻¹ = (c * r) * o * c⁻¹ * o⁻¹ * r⁻¹ := by group
      _ = (r * c) * o * c⁻¹ * o⁻¹ * r⁻¹ := by rw [hrc]
      _ = r * (c * o * c⁻¹ * o⁻¹) * r⁻¹ := by group
  rw [e]
  exact h3

theorem exists_sylow_le_centralizer_pair {J Ta Tb : Subgroup G}
    (h2 : IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J)) (hTa : IsSylow2In Ta J)
    (hTb : IsSylow2In Tb J) {a b : G} (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a)
    (haJ : a ∈ Subgroup.normalizer (J : Set G)) (hbJ : b ∈ Subgroup.normalizer (J : Set G))
    (haT : Ta ≤ Subgroup.centralizer ({a} : Set G))
    (hbT : Tb ≤ Subgroup.centralizer ({b} : Set G)) :
    ∃ P : Subgroup G, IsSylow2In P J ∧ P ≤ Subgroup.centralizer ({a} : Set G) ∧
      P ≤ Subgroup.centralizer ({b} : Set G) := by
  have hle : Subgroup.closure ({a, b} : Set G) ≤ Bootstrap.trivialOnQuot J := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact ⟨haJ, fun x hx => commutator_mem_oddCoreOf_of_sylow h2 hTa haJ haT hx⟩
    · exact ⟨hbJ, fun x hx => commutator_mem_oddCoreOf_of_sylow h2 hTb hbJ hbT hx⟩
  have hAJ : ⁅Subgroup.closure ({a, b} : Set G), J⁆ ≤ oddCoreOf J :=
    Subgroup.commutator_le.mpr fun y hy x hx => (hle hy).2 x hx
  obtain ⟨P, hP, hPc⟩ := AscE184Sect.exists_isSylow2In_centralizer
    (T8.isPGroup_closure_pair ha2 hb2 hab) hAJ
  refine ⟨P, hP, ?_, ?_⟩
  · refine hPc.trans (Subgroup.centralizer_le fun x hx => Subgroup.subset_closure ?_)
    rw [Set.mem_singleton_iff.mp hx]
    exact Set.mem_insert _ _
  · refine hPc.trans (Subgroup.centralizer_le fun x hx => Subgroup.subset_closure ?_)
    rw [Set.mem_singleton_iff.mp hx]
    exact Set.mem_insert_of_mem _ rfl

theorem natCard_map_of_inf_ker {A B : Type} [Group A] [Group B] (f : A →* B) {H : Subgroup A}
    (h : ∀ x ∈ H, f x = 1 → x = 1) : Nat.card ↥(H.map f) = Nat.card ↥H := by
  have hinj : Function.Injective (f.comp H.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    exact Subtype.ext (h x x.2 hx)
  rw [show H.map f = (f.comp H.subtype).range by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).symm.toEquiv

omit [Finite G] in
theorem eq_one_of_two_of_odd {H N : Subgroup G} (h2 : IsPGroup 2 ↥H) (hN : Odd (Nat.card ↥N))
    {x : G} (hxH : x ∈ H) (hxN : x ∈ N) : x = 1 := by
  obtain ⟨k, hk⟩ := h2 ⟨x, hxH⟩
  have hk' : x ^ 2 ^ k = 1 := by
    have h1 := congrArg Subtype.val hk
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h1
  have hm : x ^ Nat.card ↥N = 1 := by
    have h1 := congrArg Subtype.val (pow_card_eq_one' (G := ↥N) (x := ⟨x, hxN⟩))
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h1
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥N) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN)
  have h3 := pow_gcd_eq_one.mpr ⟨hk', hm⟩
  rwa [hcop.gcd_eq_one, pow_one] at h3

theorem isSylow2In_of_card_ge {Pb M : Subgroup G} (hPM : Pb ≤ M) (h2 : IsPGroup 2 ↥Pb)
    (hcard : ∀ S : Subgroup G, IsSylow2In S M → Nat.card ↥S ≤ Nat.card ↥Pb) :
    IsSylow2In Pb M := by
  refine ⟨hPM, h2, fun V hVM hV2 hPV => ?_⟩
  obtain ⟨Q, hQ⟩ := (hV2.comap_subtype (K := M)).exists_le_sylow
  have hVS : V ≤ (Q : Subgroup ↥M).map M.subtype := fun v hv =>
    ⟨⟨v, hVM hv⟩, hQ (Subgroup.mem_subgroupOf.mpr hv), rfl⟩
  exact (Subgroup.eq_of_le_of_card_ge hPV
    ((Subgroup.card_le_of_le hVS).trans (hcard _ (isSylow2In_map_subtype M Q)))).symm

end Coprime

section Conj

variable {Q Z : Type} [Group Q] [Group Z] {N : Subgroup Q} [N.Normal]

@[expose] def conjAut (e : ↥N ≃* Z) (w : Q) : MulAut Z :=
  e.symm.trans ((MulAut.conjNormal w).trans e)

theorem conjAut_apply (e : ↥N ≃* Z) (w : Q) {y : Q} (hy : y ∈ N) :
    conjAut e w (e ⟨y, hy⟩) = e ⟨w * y * w⁻¹, Subgroup.Normal.conj_mem inferInstance y hy w⟩ := by
  show e (MulAut.conjNormal w (e.symm (e ⟨y, hy⟩))) = _
  rw [MulEquiv.symm_apply_apply]
  congr 1

theorem conjAut_mul_self (e : ↥N ≃* Z) {w : Q} (hw : w * w = 1) :
    conjAut e w * conjAut e w = 1 := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨⟨y, hy⟩, rfl⟩ := e.surjective x
  rw [MulAut.mul_apply, conjAut_apply, conjAut_apply, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  show w * (w * y * w⁻¹) * w⁻¹ = y
  calc w * (w * y * w⁻¹) * w⁻¹ = (w * w) * y * (w * w)⁻¹ := by group
    _ = y := by rw [hw, one_mul, inv_one, mul_one]

theorem conjAut_apply_of_commute (e : ↥N ≃* Z) {w y : Q} (hy : y ∈ N) (hc : w * y = y * w) :
    conjAut e w (e ⟨y, hy⟩) = e ⟨y, hy⟩ := by
  rw [conjAut_apply]
  congr 1
  apply Subtype.ext
  show w * y * w⁻¹ = y
  rw [hc, mul_inv_cancel_right]

theorem commute_of_conjAut_eq_one (e : ↥N ≃* Z) {w : Q} (h : conjAut e w = 1) {y : Q}
    (hy : y ∈ N) : w * y = y * w := by
  have h1 : conjAut e w (e ⟨y, hy⟩) = e ⟨y, hy⟩ := by rw [h]; rfl
  rw [conjAut_apply] at h1
  have h2 := congrArg Subtype.val (e.injective h1)
  calc w * y = w * y * w⁻¹ * w := by group
    _ = y * w := by rw [show w * y * w⁻¹ = y from h2]

theorem commute_of_conjAut_eq_conj (e : ↥N ≃* Z) {w a : Q} (ha : a ∈ N) (ha2 : a * a = 1)
    (h : conjAut e w = MulAut.conj (e ⟨a, ha⟩)) {y : Q} (hy : y ∈ N) :
    a * w * y = y * (a * w) := by
  have h1 : conjAut e w (e ⟨y, hy⟩) = e (⟨a, ha⟩ * ⟨y, hy⟩ * ⟨a, ha⟩⁻¹) := by
    rw [h, MulAut.conj_apply, map_mul, map_mul, map_inv]
  rw [conjAut_apply] at h1
  have h2 : w * y * w⁻¹ = a * y * a⁻¹ := congrArg Subtype.val (e.injective h1)
  calc a * w * y = a * (w * y * w⁻¹) * w := by group
    _ = a * (a * y * a⁻¹) * w := by rw [h2]
    _ = (a * a) * y * a⁻¹ * w := by group
    _ = y * (a * w) := by rw [ha2, one_mul, inv_eq_of_mul_eq_one_right ha2, mul_assoc]

end Conj

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem linkVtxEquiv_eq (hL : TightLargeHypR r n Y R S t) {y : Y} (hy : y ∈ linkLayer R t) :
    linkVtxEquiv hL ⟨oddQuotMk t ⟨y, linkLayerAt_le_centralizer hy⟩,
      oddQuotMk_mem_modOdd hy (linkLayerAt_le_centralizer hy)⟩ = linkLayerHom' hL ⟨y, hy⟩ :=
  Subtype.ext (linkVtxEquiv_mk hL hy)

theorem isUniqueInvolution_link_of (hL : TightLargeHypR r n Y R S t) {J' : Subgroup Y} {t' : Y}
    (hJ' : J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (ht' : IsUniqueInvolution J' t') (ht'Λ : t' ∈ linkLayer R t) :
    IsUniqueInvolution
      ((secImg (CoreAssembly.conjClass (tightCore R)) t J').subgroupOf (linkGrp R t))
      (linkVtxEquiv hL ⟨oddQuotMk t ⟨t', linkLayerAt_le_centralizer ht'Λ⟩,
        oddQuotMk_mem_modOdd ht'Λ (linkLayerAt_le_centralizer ht'Λ)⟩) := by
  have h := isUniqueInvolution_subgroupOf (isUniqueInvolution_secImg
    (TightLargeHypR.typeRFam hL) (xMem_of_mem_omegaNbr_core hL hJ') ht')
    (le_linkGrp (t := t) hJ')
  convert h using 1
  exact Subtype.ext (linkVtxEquiv_mk hL ht'Λ)

theorem coe_linkLayerHom' (hL : TightLargeHypR r n Y R S t) (y : ↥(linkLayer R t)) :
    ((linkLayerHom' hL y : ↥(linkGrp R t)) : SecQuot (CoreAssembly.conjClass (tightCore R)) t) =
      linkLayerHom hL y :=
  rfl

theorem linkLayerHom_mem_secImg (hL : TightLargeHypR r n Y R S t) {J' : Subgroup Y} {p : Y}
    (hp : p ∈ linkLayer R t) (hpc : p ∈ coreAt t J') :
    linkLayerHom hL ⟨p, hp⟩ ∈ secImg (CoreAssembly.conjClass (tightCore R)) t J' := by
  rw [linkLayerHom_apply]
  exact ⟨⟨p, linkLayer_le_layerY hL hp⟩, Subgroup.mem_subgroupOf.mpr hpc, rfl⟩

theorem map_le_member (hL : TightLargeHypR r n Y R S t) {J' P : Subgroup Y}
    (hPc : P ≤ coreAt t J') :
    (P.subgroupOf (linkLayer R t)).map (linkLayerHom' hL) ≤
      (secImg (CoreAssembly.conjClass (tightCore R)) t J').subgroupOf (linkGrp R t) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [Subgroup.mem_subgroupOf, coe_linkLayerHom']
  exact linkLayerHom_mem_secImg hL y.2 (hPc (Subgroup.mem_subgroupOf.mp hy))

theorem natCard_map_linkLayerHom' (hL : TightLargeHypR r n Y R S t) {P : Subgroup Y}
    (hPΛ : P ≤ linkLayer R t) (hP2 : IsPGroup 2 ↥P) :
    Nat.card ↥((P.subgroupOf (linkLayer R t)).map (linkLayerHom' hL)) = Nat.card ↥P := by
  rw [natCard_map_of_inf_ker _ fun x hx h1 => ?_]
  · exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPΛ).toEquiv
  · have hxk : x ∈ (linkLayerHom' hL).ker := h1
    rw [ker_linkLayerHom hL] at hxk
    exact eq_one_of_two_of_odd hP2.comap_subtype
      (CFSG.ComponentClassification.OddCore.odd_card _) hx hxk

theorem exists_sylow_coreAt (hL : TightLargeHypR r n Y R S t) {J' K''' : Subgroup Y} {t' w' : Y}
    (hJ' : J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (ht' : IsUniqueInvolution J' t')
    (hK : K''' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J')
    (hw : IsUniqueInvolution K''' w') (hwt : w' ∈ Subgroup.centralizer ({t} : Set Y)) :
    ∃ P : Subgroup Y, IsSylow2In P J' ∧ P ≤ coreAt t J' ∧
      P ≤ Subgroup.centralizer ({w'} : Set Y) := by
  have h := TightLargeHypR.typeRFam hL
  have hΩ := hL.datum.hypOmegaGen
  have ht := hL.datum.isUniqueInvolution_core
  have hJ'Φ := hJ'.1
  have htt' : t * t' = t' * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ' ht'
  obtain ⟨-, -, T₁, hT₁R, hT₁J, hT₁N⟩ := id hJ'
  have hT₁ : IsSylow2In T₁ J' := Q3CL.Sec7.isSylow2In_of_mem_RSet_of_le hΩ hT₁R hJ'Φ hT₁J
  have hT₁t : T₁ ≤ Subgroup.centralizer ({t} : Set Y) := fun x hx =>
    S1916.normalizer_le_centralizer_of_isUniqueInvolution ht (hT₁N hx)
  obtain ⟨-, -, T₂, hT₂R, hT₂J, hT₂N⟩ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ'Φ hK.1 hK
  have hT₂ : IsSylow2In T₂ J' := Q3CL.Sec7.isSylow2In_of_mem_RSet_of_le hΩ hT₂R hJ'Φ hT₂J
  have hT₂w : T₂ ≤ Subgroup.centralizer ({w'} : Set Y) := fun x hx =>
    S1916.normalizer_le_centralizer_of_isUniqueInvolution hw (hT₂N hx)
  have ht'w : t' * w' = w' * t' := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht' hK hw
  have htN : t ∈ Subgroup.normalizer (J' : Set Y) :=
    h.tight J' hJ'Φ t' ht' (Subgroup.mem_centralizer_singleton_iff.mpr htt')
  have hwN : w' ∈ Subgroup.normalizer (J' : Set Y) :=
    h.tight J' hJ'Φ t' ht' (Subgroup.mem_centralizer_singleton_iff.mpr ht'w.symm)
  obtain ⟨P, hP, hPt, hPw⟩ := exists_sylow_le_centralizer_pair (h.twoGroup J' hJ'Φ) hT₁ hT₂
    ht.sq hw.sq (Subgroup.mem_centralizer_singleton_iff.mp hwt).symm htN hwN hT₁t hT₂w
  exact ⟨P, hP, le_coreAt t hP.2.1 hP.1 hPt, hPw⟩

theorem isSylow2In_map_member (hL : TightLargeHypR r n Y R S t) {J' P : Subgroup Y}
    (hJ' : J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hP : IsSylow2In P J') (hPc : P ≤ coreAt t J') :
    IsSylow2In ((P.subgroupOf (linkLayer R t)).map (linkLayerHom' hL))
      ((secImg (CoreAssembly.conjClass (tightCore R)) t J').subgroupOf (linkGrp R t)) := by
  have hPΛ : P ≤ linkLayer R t := hPc.trans (coreAt_le_linkLayerAt hJ')
  obtain ⟨eP⟩ := (TightLargeHypR.typeRFam hL).quat _ hJ'.1 P hP
  refine isSylow2In_of_card_ge (map_le_member hL hPc) (hP.2.1.comap_subtype.map _)
    fun S' hS' => ?_
  obtain ⟨eS⟩ := ((typeRFam_coreLinkFam hL).restrict (linkGrp R t)).quat _
    (subgroupOf_mem_linkRestrict (t := t) hJ') S' hS'
  rw [natCard_map_linkLayerHom' hL hPΛ hP.2.1, Nat.card_congr eP.toEquiv,
    Nat.card_congr eS.toEquiv]

theorem false_of_linkDich (hL : TightLargeHypR r n Y R S t) (hD : LinkDichSyl R t)
    {J' K''' : Subgroup Y} {t' w' : Y}
    (hJ' : J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (ht' : IsUniqueInvolution J' t')
    (hK : K''' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J')
    (hw : IsUniqueInvolution K''' w') (ht'C : t' ∈ Subgroup.centralizer ({t} : Set Y))
    (hwt : w' ∈ Subgroup.centralizer ({t} : Set Y)) {L : Subgroup (OddQuot t)}
    (hLc : IsComponent L)
    (hmt : ∃ y ∈ L, oddQuotMk t ⟨t', ht'C⟩ * y ≠ y * oddQuotMk t ⟨t', ht'C⟩)
    (hmw : ∃ y ∈ L, oddQuotMk t ⟨w', hwt⟩ * y ≠ y * oddQuotMk t ⟨w', hwt⟩)
    (hmtw : ∃ y ∈ L, oddQuotMk t ⟨t', ht'C⟩ * oddQuotMk t ⟨w', hwt⟩ * y ≠
      y * (oddQuotMk t ⟨t', ht'C⟩ * oddQuotMk t ⟨w', hwt⟩)) : False := by
  have ht := hL.datum.isUniqueInvolution_core
  have htt' : t * t' = t' * t :=
    Q3CL.T8.mul_comm_of_mem_omegaNbr hL.datum.hypOmegaGen ht hJ' ht'
  have ht'Λ : t' ∈ linkLayer R t := coreAt_le_linkLayerAt hJ' (mem_coreAt_of_sq_sq ht'.mem
    (by rw [ht'.sq, one_mul]) htt'.symm)
  have hNor : (modOdd t (linkLayer R t)).Normal :=
    modOdd_normal fun _ hc _ hy => conj_mem_linkLayer hL hc hy
  have hLN : L ≤ modOdd t (linkLayer R t) :=
    le_of_moved hNor hLc (oddQuotMk_mem_modOdd ht'Λ ht'C) hmt
  obtain ⟨P, hP, hPc, hPw⟩ := exists_sylow_coreAt hL hJ' ht' hK hw hwt
  have hwb2 : oddQuotMk t ⟨w', hwt⟩ * oddQuotMk t ⟨w', hwt⟩ = 1 := by
    rw [← map_mul, show (⟨w', hwt⟩ : ↥(Subgroup.centralizer ({t} : Set Y))) * ⟨w', hwt⟩ = 1
      from Subtype.ext hw.sq, map_one]
  have ht'b2 : oddQuotMk t ⟨t', ht'C⟩ * oddQuotMk t ⟨t', ht'C⟩ = 1 := by
    rw [← map_mul, show (⟨t', ht'C⟩ : ↥(Subgroup.centralizer ({t} : Set Y))) * ⟨t', ht'C⟩ = 1
      from Subtype.ext ht'.sq, map_one]
  have hβP : ∀ x ∈ (P.subgroupOf (linkLayer R t)).map (linkLayerHom' hL),
      conjAut (linkVtxEquiv hL) (oddQuotMk t ⟨w', hwt⟩) x = x := by
    rintro _ ⟨⟨p, hpΛ⟩, hp, rfl⟩
    rw [← linkVtxEquiv_eq hL hpΛ]
    refine conjAut_apply_of_commute _ _ ?_
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (hPw (Subgroup.mem_subgroupOf.mp hp))).symm)
  rcases hD _ (subgroupOf_mem_linkRestrict (t := t) hJ') _
    (isUniqueInvolution_link_of hL hJ' ht' ht'Λ) _ (isSylow2In_map_member hL hJ' hP hPc) _
    (conjAut_mul_self _ hwb2) hβP with h1 | h1
  · obtain ⟨y, hy, hne⟩ := hmw
    exact hne (commute_of_conjAut_eq_one _ h1 (hLN hy))
  · obtain ⟨y, hy, hne⟩ := hmtw
    exact hne (commute_of_conjAut_eq_conj _ (oddQuotMk_mem_modOdd ht'Λ ht'C) ht'b2 h1 (hLN hy))

end Cit3

end S289

end CFSG.ClassicalInvolution.Q3.TL4
