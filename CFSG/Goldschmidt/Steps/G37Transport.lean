module

public import CFSG.Goldschmidt.BasicG
public import CFSG.Walter.Bender1970.S2.Transport
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Adapters.GeneralizedFittingTop

public section

namespace CFSG.Goldschmidt.SStarTransport

open CFSG.Open
open scoped Pointwise

universe u

section Iso

theorem omega1_map_of_injective {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) (T : Subgroup G) : (Omega1 T).map f = Omega1 (T.map f) := by
  rw [Omega1, Omega1, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxT, hx2⟩, rfl⟩
    exact ⟨⟨x, hxT, rfl⟩, by rw [← map_pow, hx2, map_one]⟩
  · rintro ⟨⟨x, hxT, rfl⟩, hy2⟩
    refine ⟨x, ⟨hxT, ?_⟩, rfl⟩
    apply hf
    rw [map_pow, hy2, map_one]

theorem pCore_map_mulEquiv {Q Q' : Type*} [Group Q] [Group Q'] (p : ℕ) (e : Q ≃* Q') :
    (CFSG.Open.pCore p Q).map e.toMonoidHom = CFSG.Open.pCore p Q' := by
  exact CFSG.pCore_map_iso p e

theorem goldschmidtLayer_eq_componentLayerOf (Q : Type*) [Group Q] :
    goldschmidtLayer Q = GorensteinWalter.componentLayerOf (⊤ : Subgroup Q) :=
  (CFSG.Adapters.componentLayerOf_top_eq_componentClassification Q).symm

theorem goldschmidtLayer_map_mulEquiv' {Q Q' : Type u} [Group Q] [Group Q'] (e : Q ≃* Q') :
    (goldschmidtLayer Q).map e.toMonoidHom = goldschmidtLayer Q' := by
  rw [goldschmidtLayer_eq_componentLayerOf, goldschmidtLayer_eq_componentLayerOf]
  exact CFSG.Walter.componentLayerOf_top_map_of_mulEquiv' e

theorem isComponentOf_top_map_mulEquiv {Q Q' : Type u} [Group Q] [Group Q'] (e : Q ≃* Q')
    {L : Subgroup Q} (hL : IsComponentOf L ⊤) : IsComponentOf (L.map e.toMonoidHom) ⊤ := by
  rw [CFSG.Adapters.isComponentOf_top_iff] at hL ⊢
  exact CFSG.Walter.isComponentOf_top_map_of_mulEquiv e hL

@[expose] noncomputable def quotientCenterEquiv {L L' : Type*} [Group L] [Group L'] (e : L ≃* L') :
    L ⧸ Subgroup.center L ≃* L' ⧸ Subgroup.center L' :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem isGoldTypeI_of_mulEquiv {L L' : Type*} [Group L] [Group L'] (e : L ≃* L')
    (h : IsGoldTypeI L) : IsGoldTypeI L' := by
  rcases h with ⟨n, hn, ⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩
  · exact Or.inl ⟨n, hn, ⟨(quotientCenterEquiv e).symm.trans φ⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨(quotientCenterEquiv e).symm.trans φ⟩⟩)
  · exact Or.inr (Or.inr ⟨n, hn, ⟨(quotientCenterEquiv e).symm.trans φ⟩⟩)

theorem isGoldL2_of_mulEquiv {L L' : Type*} [Group L] [Group L'] (e : L ≃* L')
    (h : IsGoldL2 L) : IsGoldL2 L' := by
  obtain ⟨p, f, hp, hpodd, hf, h5, h8, ⟨φ⟩⟩ := h
  exact ⟨p, f, hp, hpodd, hf, h5, h8, ⟨(quotientCenterEquiv e).symm.trans φ⟩⟩

theorem isGoldJR_of_mulEquiv {L L' : Type*} [Group L] [Group L'] [Finite L] (e : L ≃* L')
    (h : IsGoldJR L) : IsGoldJR L' :=
  CFSG.Walter.IsTypeJR.of_mulEquiv (quotientCenterEquiv e) h

theorem isGoldTypeII_of_mulEquiv {L L' : Type*} [Group L] [Group L'] [Finite L] (e : L ≃* L')
    (h : IsGoldTypeII L) : IsGoldTypeII L' := by
  obtain ⟨hodd, h2⟩ := h
  refine ⟨?_, h2.imp (isGoldL2_of_mulEquiv e) (isGoldJR_of_mulEquiv e)⟩
  have hc : Nat.card (Subgroup.center L') = Nat.card (Subgroup.center L) := by
    rw [← Subgroup.map_center_eq e]
    exact Subgroup.card_map_of_injective e.injective
  rw [hc]
  exact hodd

theorem sstarConditions_map {Q Q' : Type u} [Group Q] [Group Q'] [Finite Q] (e : Q ≃* Q')
    {A T : Subgroup Q}
    (h : CFSG.Open.pCore 2 Q ⊔ goldschmidtLayer Q = ⊤ ∧
      CFSG.Open.pCore 2 Q ≤ Subgroup.center Q ∧
      A = CFSG.Open.pCore 2 Q ⊔ Omega1 (T ⊓ goldschmidtLayer Q) ∧
      ∀ L : Subgroup Q, IsComponentOf L ⊤ → IsGoldTypeI L ∨ IsGoldTypeII L) :
    CFSG.Open.pCore 2 Q' ⊔ goldschmidtLayer Q' = ⊤ ∧
      CFSG.Open.pCore 2 Q' ≤ Subgroup.center Q' ∧
      A.map e.toMonoidHom = CFSG.Open.pCore 2 Q' ⊔
        Omega1 (T.map e.toMonoidHom ⊓ goldschmidtLayer Q') ∧
      ∀ L : Subgroup Q', IsComponentOf L ⊤ → IsGoldTypeI L ∨ IsGoldTypeII L := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hP := pCore_map_mulEquiv 2 e
  have hE := goldschmidtLayer_map_mulEquiv' e
  have hZ : (Subgroup.center Q).map e.toMonoidHom = Subgroup.center Q' :=
    Subgroup.map_center_eq e
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hP, ← hE, ← Subgroup.map_sup, h1, Subgroup.map_top_of_surjective _ e.surjective]
  · rw [← hP, ← hZ]
    exact Subgroup.map_mono h2
  · rw [h3, Subgroup.map_sup, hP, omega1_map_of_injective _ e.injective,
      Subgroup.map_inf_eq _ _ _ e.injective, hE]
  · intro L hL
    have hL' := isComponentOf_top_map_mulEquiv e.symm hL
    have hmap : (L.map e.symm.toMonoidHom).map e.toMonoidHom = L := by
      rw [Subgroup.map_map]
      have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Q' := by
        ext x
        exact e.apply_symm_apply x
      rw [hid, Subgroup.map_id]
    let φ : ↥(L.map e.symm.toMonoidHom) ≃* ↥L :=
      (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hmap)
    rcases h4 _ hL' with hI | hII
    · exact Or.inl (isGoldTypeI_of_mulEquiv φ hI)
    · exact Or.inr (isGoldTypeII_of_mulEquiv φ hII)

end Iso

section OddCore

variable {P P' : Type*} [Group P] [Group P'] [Finite P] [Finite P']

theorem odd_card_goldschmidtOddCore (Q : Type*) [Group Q] [Finite Q] :
    Odd (Nat.card (goldschmidtOddCore Q)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [goldschmidtOddCore_eq_pPrimeCore]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem comap_goldschmidtOddCore_eq (φ : P →* P') (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker)) :
    (goldschmidtOddCore P').comap φ = goldschmidtOddCore P := by
  apply le_antisymm
  · have hn : ((goldschmidtOddCore P').comap φ).Normal :=
      (goldschmidtOddCore_normal P').comap φ
    let g := φ.domRestrict ((goldschmidtOddCore P').comap φ)
    have hcard := Subgroup.card_ker_mul_card_range g
    have hrange : Nat.card g.range ∣ Nat.card (goldschmidtOddCore P') := by
      apply Subgroup.card_dvd_of_le
      rintro _ ⟨v, rfl⟩
      exact v.2
    have hkerdvd : Nat.card g.ker ∣ Nat.card φ.ker := by
      have hsub : g.ker.map ((goldschmidtOddCore P').comap φ).subtype ≤ φ.ker := by
        rintro _ ⟨v, hv, rfl⟩
        exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hv)
      rw [← Subgroup.card_map_of_injective (K := g.ker)
        ((goldschmidtOddCore P').comap φ).subtype_injective]
      exact Subgroup.card_dvd_of_le hsub
    have hodd : Odd (Nat.card ((goldschmidtOddCore P').comap φ)) := by
      rw [← hcard]
      exact (hker.of_dvd_nat hkerdvd).mul
        ((odd_card_goldschmidtOddCore P').of_dvd_nat hrange)
    exact le_sSup ⟨hn, hodd⟩
  · rw [← Subgroup.map_le_iff_le_comap]
    have hn : ((goldschmidtOddCore P).map φ).Normal := (goldschmidtOddCore_normal P).map φ hφ
    have hodd : Odd (Nat.card ((goldschmidtOddCore P).map φ)) :=
      (odd_card_goldschmidtOddCore P).of_dvd_nat (Subgroup.card_map_dvd _ φ)
    exact le_sSup ⟨hn, hodd⟩

@[expose] noncomputable def oddCoreQuotientEquiv (φ : P →* P') (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker)) :
    P ⧸ goldschmidtOddCore P ≃* P' ⧸ goldschmidtOddCore P' :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      exact (comap_goldschmidtOddCore_eq φ hφ hker).symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      ((QuotientGroup.mk' (goldschmidtOddCore P')).comp φ)
      ((QuotientGroup.mk'_surjective _).comp hφ))

theorem oddCoreQuotientEquiv_mk (φ : P →* P') (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker)) (x : P) :
    oddCoreQuotientEquiv φ hφ hker (QuotientGroup.mk x) =
      (QuotientGroup.mk (φ x) : P' ⧸ goldschmidtOddCore P') :=
  rfl

theorem map_oddCoreQuotientEquiv (φ : P →* P') (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker)) (B : Subgroup P) :
    (B.map (QuotientGroup.mk' (goldschmidtOddCore P))).map
        (oddCoreQuotientEquiv φ hφ hker).toMonoidHom =
      (B.map φ).map (QuotientGroup.mk' (goldschmidtOddCore P')) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

end OddCore


section Sylow

variable {G : Type*} [Group G]

theorem exists_sylow_of_isSylowIn {p : ℕ} {T X : Subgroup G} (h : fusionIsSylowIn p T X) :
    ∃ P : Sylow p X, (P : Subgroup X) = T.subgroupOf X := by
  obtain ⟨hTX, hT, hmax⟩ := h
  refine ⟨⟨T.subgroupOf X, hT.comap_subtype, fun {Q} hQ hTQ => ?_⟩, rfl⟩
  have h1 := hmax (Q.map X.subtype) (Subgroup.map_subtype_le Q) (hQ.map X.subtype) fun s hs =>
    ⟨⟨s, hTX hs⟩, hTQ (show (⟨s, hTX hs⟩ : X) ∈ T.subgroupOf X from hs), rfl⟩
  rw [← h1]
  exact (Subgroup.comap_map_eq_self_of_injective X.subtype_injective Q).symm

theorem isSylowIn_of_sylow {p : ℕ} {T X : Subgroup G} (hTX : T ≤ X) (P : Sylow p X)
    (hP : (P : Subgroup X) = T.subgroupOf X) : fusionIsSylowIn p T X := by
  have hT : IsPGroup p T := by
    have h1 := P.isPGroup'.map X.subtype
    rwa [hP, Subgroup.map_subgroupOf_eq_of_le hTX] at h1
  refine ⟨hTX, hT, fun Q hQX hQ hTQ => ?_⟩
  have h1 := P.is_maximal' (Q := Q.subgroupOf X) hQ.comap_subtype (by
    rw [hP]
    exact fun x hx => hTQ hx)
  rw [hP] at h1
  have h2 := congrArg (Subgroup.map X.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hQX, Subgroup.map_subgroupOf_eq_of_le hTX] at h2

theorem exists_sylow_subgroupOf_of_normal [Finite G] {p : ℕ} [Fact p.Prime] {T H K : Subgroup G}
    (hT : fusionIsSylowIn p T H) (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal) :
    ∃ P : Sylow p K, (P : Subgroup K) = T.subgroupOf K := by
  obtain ⟨PT, hPT⟩ := exists_sylow_of_isSylowIn hT
  obtain ⟨P₁, hP₁⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal PT hKn.isSubnormal
  let e : ↥(K.subgroupOf H) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKH
  have he : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨P₁.mapSurjective he, ?_⟩
  rw [Sylow.coe_mapSurjective]
  ext k
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (x : H) ∈ (P₁ : Subgroup (K.subgroupOf H)).map (K.subgroupOf H).subtype :=
      ⟨x, hx, rfl⟩
    rw [hP₁, hPT] at hx'
    exact hx'.1
  · intro hk
    set x : ↥(K.subgroupOf H) := e.symm k with hxdef
    have hxk : e x = k := e.apply_symm_apply k
    have hxT : (x : H) ∈ (PT : Subgroup H) ⊓ K.subgroupOf H := by
      refine ⟨?_, x.2⟩
      rw [hPT]
      show ((x : H) : G) ∈ T
      have : ((x : H) : G) = (k : G) := congrArg Subtype.val hxk
      rw [this]
      exact hk
    rw [← hP₁] at hxT
    obtain ⟨x', hx', hx'x⟩ := hxT
    have : x' = x := Subtype.ext hx'x
    exact ⟨x, this ▸ hx', hxk⟩

end Sylow

section Main

variable {G G' : Type u} [Group G] [Group G'] [Finite G] [Finite G']

theorem isSStarIn_of_surjective {H A : Subgroup G} {H' A' : Subgroup G'} (hS : IsSStarIn H A)
    (f : ↥H →* ↥H') (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker))
    (hA'H' : A' ≤ H') (hAA' : (A.subgroupOf H).map f = A'.subgroupOf H') :
    IsSStarIn H' A' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAH, hAc, T, hT, hAT, hcl, hK1, hK2, hK3, hK4⟩ := hS
  have hTH : T ≤ H := hT.1
  set A₀ : Subgroup H := A.subgroupOf H with hA₀
  set T₀ : Subgroup H := T.subgroupOf H with hT₀
  set T' : Subgroup G' := (T₀.map f).map H'.subtype with hT'
  have hT'H' : T' ≤ H' := Subgroup.map_subtype_le _
  have hT'sub : T'.subgroupOf H' = T₀.map f :=
    Subgroup.comap_map_eq_self_of_injective H'.subtype_injective _
  obtain ⟨PT, hPT⟩ := exists_sylow_of_isSylowIn hT
  have hmemA' : ∀ x (hx : x ∈ A'), ∃ a ∈ A₀, f a = ⟨x, hA'H' hx⟩ := by
    intro x hx
    have hx' : (⟨x, hA'H' hx⟩ : H') ∈ A'.subgroupOf H' := hx
    rw [← hAA'] at hx'
    exact hx'
  have hmemA'' : ∀ a ∈ A₀, ((f a : H') : G') ∈ A' := by
    intro a ha
    have : f a ∈ A'.subgroupOf H' := hAA' ▸ ⟨a, ha, rfl⟩
    exact this
  have hA'c : IsMulCommutative A' := by
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    obtain ⟨a, ha, hax⟩ := hmemA' x x.2
    obtain ⟨b, hb, hby⟩ := hmemA' y y.2
    have hab : a * b = b * a := by
      have h1 := hAc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
      have h2 : (a : G) * b = b * a := congrArg Subtype.val h1
      exact Subtype.ext h2
    have e1 : ((f a : H') : G') = x := congrArg Subtype.val hax
    have e2 : ((f b : H') : G') = y := congrArg Subtype.val hby
    show (x : G') * y = y * x
    rw [← e1, ← e2, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hab]
  have hT'syl : fusionIsSylowIn 2 T' H' := by
    refine isSylowIn_of_sylow hT'H' (PT.mapSurjective hf) ?_
    rw [Sylow.coe_mapSurjective, hPT, hT'sub]
  have hA'T' : A' ≤ T' := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := hmemA' x hx
    exact ⟨f a, ⟨a, hAT ha, rfl⟩, congrArg Subtype.val hax⟩
  have hAnT : ∀ t ∈ T, ∀ a ∈ A, t * a * t⁻¹ ∈ A := by
    intro t ht a ha
    have h1 := hcl a ha t⁻¹ (H.inv_mem (hTH ht)) (by
      rw [inv_inv]
      exact T.mul_mem (T.mul_mem ht (hAT ha)) (T.inv_mem ht))
    rwa [inv_inv] at h1
  have hA'nT' : ∀ τ ∈ T₀.map f, ∀ α ∈ A₀.map f, τ * α * τ⁻¹ ∈ A₀.map f := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨a, ha, rfl⟩
    refine ⟨t * a * t⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact hAnT (t : G) ht (a : G) ha
  have hcl' : IsStronglyClosedIn A' T' H' := by
    intro x hx y hy hxy
    obtain ⟨a, ha, hax⟩ := hmemA' x hx
    obtain ⟨h, hhy⟩ := hf ⟨y, hy⟩
    set b : H := h⁻¹ * a * h with hb
    have hfb : ((f b : H') : G') = y⁻¹ * x * y := by
      rw [hb, map_mul, map_mul, map_inv, hhy, hax]
      rfl
    have hfbT : f b ∈ T₀.map f := by
      rw [← hT'sub]
      show ((f b : H') : G') ∈ T'
      rw [hfb]
      exact hxy
    obtain ⟨t, ht, hft⟩ := hfbT
    set R : Subgroup H := T₀ ⊔ f.ker with hR
    have hbR : b ∈ R := by
      have hb' : b = t * (t⁻¹ * b) := by group
      rw [hb']
      refine Subgroup.mul_mem_sup ht ?_
      rw [MonoidHom.mem_ker, map_mul, map_inv, hft, inv_mul_cancel]
    have hbp : IsPGroup 2 (Subgroup.zpowers b) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (hT.2.1.comap_subtype (K := H)))
        ⟨a, hAT ha⟩
      have hak : a ^ 2 ^ k = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one]
        have : orderOf (⟨a, hAT ha⟩ : ↥(T.comap H.subtype)) = orderOf a :=
          Subgroup.orderOf_mk a (hAT ha)
        rw [← this, hk]
      have hbk : b ^ 2 ^ k = 1 := by
        have h1 := conj_pow (a := h⁻¹) (b := a) (i := 2 ^ k)
        rw [inv_inv] at h1
        rw [hb, h1, hak, mul_one, inv_mul_cancel]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hbk)
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have hPTR : (PT : Subgroup H) ≤ R := by
      rw [hPT]
      exact le_sup_left
    let PR : Sylow 2 R := PT.subtype hPTR
    obtain ⟨Q, hQ⟩ := (hbp.comap_subtype (K := R)).exists_le_sylow
    obtain ⟨r, hr⟩ := MulAction.exists_smul_eq R PR Q
    have hbQ : (⟨b, hbR⟩ : R) ∈ (Q : Subgroup R) :=
      hQ (show (⟨b, hbR⟩ : R) ∈ (Subgroup.zpowers b).comap R.subtype from
        Subgroup.mem_zpowers b)
    have hQ' : (Q : Subgroup R) = MulAut.conj r • (PR : Subgroup R) := by
      rw [← hr]
      exact Sylow.coe_subgroup_smul
    rw [hQ', Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hbQ
    have hc : ((r : H)⁻¹ * b * r) ∈ T₀ := by
      have h1 : ((MulAut.conj r)⁻¹ • (⟨b, hbR⟩ : R)) ∈ (PR : Subgroup R) := hbQ
      rw [Sylow.coe_subtype, hPT] at h1
      have h2 : (MulAut.conj r)⁻¹ • (⟨b, hbR⟩ : R) = r⁻¹ * ⟨b, hbR⟩ * r := by
        rw [MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply]
      rw [h2] at h1
      exact h1
    have hcA : ((r : H)⁻¹ * b * r) ∈ A₀ := by
      have h1 := hcl (a : G) ha ((h * r : H) : G) (h * r).2 (by
        have : ((h * r : H) : G)⁻¹ * a * ((h * r : H) : G) = (((r : H)⁻¹ * b * r : H) : G) := by
          rw [hb]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [this]
        exact hc)
      have : ((h * r : H) : G)⁻¹ * a * ((h * r : H) : G) = (((r : H)⁻¹ * b * r : H) : G) := by
        rw [hb]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [this] at h1
      exact h1
    have hfr : f r ∈ T₀.map f := by
      have hr2 : (r : H) ∈ T₀ ⊔ f.ker := r.2
      obtain ⟨t', ht', n, hn, htn⟩ := Subgroup.mem_sup_of_normal_right.mp hr2
      refine ⟨t', ht', ?_⟩
      rw [← htn, map_mul, MonoidHom.mem_ker.mp hn, mul_one]
    have hfb' : f b = f r * f ((r : H)⁻¹ * b * r) * (f r)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      group
    have hfbA : f b ∈ A'.subgroupOf H' := by
      rw [← hAA', hfb']
      exact hA'nT' _ hfr _ ⟨_, hcA, rfl⟩
    have : ((f b : H') : G') ∈ A' := hfbA
    rwa [hfb] at this
  refine ⟨hA'H', hA'c, T', hT'syl, hA'T', hcl', ?_⟩
  set N₀ : Subgroup H := Subgroup.normalClosure (A₀ : Set H) with hN₀
  set N₀' : Subgroup H' := Subgroup.normalClosure ((A'.subgroupOf H') : Set H') with hN₀'
  have hNN : N₀.map f = N₀' := by
    rw [hN₀, hN₀', Subgroup.map_normalClosure _ f hf, ← hAA', Subgroup.coe_map]
  set K : Subgroup G := normalClosureIn H A with hK
  set K' : Subgroup G' := normalClosureIn H' A' with hK'
  have hKdef : K = N₀.map H.subtype := rfl
  have hK'def : K' = N₀'.map H'.subtype := rfl
  have hKH : K ≤ H := Subgroup.map_subtype_le _
  have hK'H' : K' ≤ H' := Subgroup.map_subtype_le _
  have hKsub : K.subgroupOf H = N₀ :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hmemK : ∀ k : K, Subgroup.inclusion hKH k ∈ N₀ := by
    intro k
    have h1 : Subgroup.inclusion hKH k ∈ K.subgroupOf H := k.2
    rwa [hKsub] at h1
  have hmemK' : ∀ k : K, ((f (Subgroup.inclusion hKH k) : H') : G') ∈ K' := by
    intro k
    rw [hK'def]
    exact ⟨_, hNN ▸ ⟨_, hmemK k, rfl⟩, rfl⟩
  let φ : ↥K →* ↥K' :=
    (H'.subtype.comp (f.comp (Subgroup.inclusion hKH))).codRestrict K' hmemK'
  have hφapply : ∀ k : K, ((φ k : K') : G') = ((f (Subgroup.inclusion hKH k) : H') : G') :=
    fun _ => rfl
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [hK'def] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    rw [← hNN] at hy₀
    obtain ⟨x₀, hx₀, rfl⟩ := hy₀
    refine ⟨⟨(x₀ : G), ⟨x₀, hx₀, rfl⟩⟩, Subtype.ext ?_⟩
    rfl
  have hφker : Odd (Nat.card φ.ker) := by
    have hle : φ.ker.map (Subgroup.inclusion hKH) ≤ f.ker := by
      rintro _ ⟨k, hk, rfl⟩
      rw [MonoidHom.mem_ker]
      have h1 := congrArg (fun z : K' => (z : G')) (MonoidHom.mem_ker.mp hk)
      simp only [hφapply, OneMemClass.coe_one] at h1
      exact Subtype.ext h1
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hKH)] at hdvd
    exact hker.of_dvd_nat hdvd
  let ψ := oddCoreQuotientEquiv φ hφ hφker
  have hbarA : (barOf K A).map ψ.toMonoidHom = barOf K' A' := by
    rw [barOf, barOf, map_oddCoreQuotientEquiv]
    congr 1
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      show ((φ k : K') : G') ∈ A'
      rw [hφapply]
      exact hmemA'' _ hk
    · intro hy
      obtain ⟨a, ha, hay⟩ := hmemA' (y : G') hy
      have haN : a ∈ N₀ := Subgroup.subset_normalClosure ha
      refine ⟨⟨(a : G), ⟨a, haN, rfl⟩⟩, ha, Subtype.ext ?_⟩
      rw [hφapply]
      exact congrArg Subtype.val hay
  have hbarT : (barOf K T).map ψ.toMonoidHom = barOf K' T' := by
    rw [barOf, barOf, map_oddCoreQuotientEquiv]
    congr 1
    have hKn : (K.subgroupOf H).Normal := by
      rw [hKsub]
      exact Subgroup.normalClosure_normal
    obtain ⟨PK, hPK⟩ := exists_sylow_subgroupOf_of_normal hT hKH hKn
    have hle : (T.subgroupOf K).map φ ≤ T'.subgroupOf K' := by
      rintro _ ⟨k, hk, rfl⟩
      show ((φ k : K') : G') ∈ T'
      rw [hφapply]
      exact ⟨_, ⟨_, hk, rfl⟩, rfl⟩
    have hT'p : IsPGroup 2 (T'.subgroupOf K') :=
      ((hT.2.1.comap_subtype (K := H)).map f |>.map H'.subtype).comap_subtype
    have h1 := (PK.mapSurjective hφ).is_maximal' hT'p (by
      rw [Sylow.coe_mapSurjective, hPK]
      exact hle)
    rw [h1, Sylow.coe_mapSurjective, hPK]
  have hconds := sstarConditions_map ψ (A := barOf K A) (T := barOf K T) ⟨hK1, hK2, hK3, hK4⟩
  rw [hbarA, hbarT] at hconds
  exact hconds

theorem isSStarIn_quotient {H A : Subgroup G} (hS : IsSStarIn H A) (N : Subgroup H) [N.Normal]
    (hN : Odd (Nat.card N)) :
    IsSStarIn (⊤ : Subgroup (H ⧸ N)) ((A.subgroupOf H).map (QuotientGroup.mk' N)) := by
  let f : ↥H →* ↥(⊤ : Subgroup (H ⧸ N)) :=
    (QuotientGroup.mk' N).codRestrict ⊤ (fun _ => Subgroup.mem_top _)
  have hf : Function.Surjective f := by
    rintro ⟨y, -⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨x, rfl⟩
  have hker : f.ker = N := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff x).mp h1
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff x).mpr h)
  refine isSStarIn_of_surjective hS f hf (by rw [hker]; exact hN) le_top ?_
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, hay⟩
    exact ⟨a, ha, Subtype.ext hay⟩

omit [Finite G'] in
theorem isSStarIn_barOf {H A : Subgroup G} (hS : IsSStarIn H A) :
    IsSStarIn (⊤ : Subgroup (H ⧸ goldschmidtOddCore H)) (barOf H A) :=
  isSStarIn_quotient hS _ (odd_card_goldschmidtOddCore H)

theorem isSStarIn_map_of_injective {H A : Subgroup G} (hS : IsSStarIn H A) (φ : G →* G')
    (hφ : Function.Injective φ) : IsSStarIn (H.map φ) (A.map φ) := by
  have hker : (φ.subgroupMap H).ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : φ (x : G) = φ 1 := by
      rw [map_one]
      exact congrArg Subtype.val hx
    exact Subtype.ext (hφ h1)
  refine isSStarIn_of_surjective hS (φ.subgroupMap H) (φ.subgroupMap_surjective H)
    (by rw [hker, Subgroup.card_bot]; exact odd_one) (Subgroup.map_mono hS.1) ?_
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨a, ha, hay⟩
    have : φ (a : G) = y := congrArg Subtype.val hay
    exact ⟨a, ha, this⟩
  · rintro ⟨a, ha, hay⟩
    exact ⟨⟨a, hS.1 ha⟩, ha, Subtype.ext hay⟩

omit [Finite G'] in
theorem isSStarIn_subgroupOf {H A X : Subgroup G} (hS : IsSStarIn H A) (hHX : H ≤ X) :
    IsSStarIn (H.subgroupOf X) (A.subgroupOf X) := by
  let e : ↥H ≃* ↥(H.subgroupOf X) := (Subgroup.subgroupOfEquivOfLe hHX).symm
  refine isSStarIn_of_surjective hS e.toMonoidHom e.surjective (by
    have : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
    rw [this, Subgroup.card_bot]
    exact odd_one) (fun x hx => hS.1 hx) ?_
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨a, ha, hay⟩
    have : ((e a : H.subgroupOf X) : X) = y := congrArg Subtype.val hay
    have h2 : ((a : G)) = ((y : X) : G) := congrArg Subtype.val this
    show (y : G) ∈ A
    rw [← h2]
    exact ha
  · intro ha
    refine ⟨(⟨(y : G), hy⟩ : H), ha, ?_⟩
    rfl

end Main

theorem isElemAbelian_map {G G' : Type*} [Group G] [Group G'] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) (f : G →* G') : IsElemAbelian p (E.map f) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem isElemAbelian_subgroupOf {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) (X : Subgroup G) : IsElemAbelian p (E.subgroupOf X) :=
  CFSG.Open.IsElemAbelian.subgroupOf hE X

end CFSG.Goldschmidt.SStarTransport
