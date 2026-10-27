module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Order
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticIsotropy
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents

public section

namespace CFSG.ComponentClassification.GSThmB.X10Orth

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer

namespace E8Triple

variable {G H : Type*} [Group G] [Group H] {u v w : G}

theorem comap {φ : G →* H} (hφ : Function.Injective φ) (h : E8Triple (φ u) (φ v) (φ w)) :
    E8Triple u v w where
  sq_u := hφ (by rw [map_mul, h.sq_u, map_one])
  sq_v := hφ (by rw [map_mul, h.sq_v, map_one])
  sq_w := hφ (by rw [map_mul, h.sq_w, map_one])
  comm_uv := hφ (by rw [map_mul, map_mul, h.comm_uv])
  comm_uw := hφ (by rw [map_mul, map_mul, h.comm_uw])
  comm_vw := hφ (by rw [map_mul, map_mul, h.comm_vw])
  ne_u := fun h1 => h.ne_u (by rw [h1, map_one])
  ne_v := fun h1 => h.ne_v (by rw [h1, map_one])
  ne_w := fun h1 => h.ne_w (by rw [h1, map_one])
  ne_uv := fun h1 => h.ne_uv (by rw [← map_mul, h1, map_one])
  ne_uw := fun h1 => h.ne_uw (by rw [← map_mul, h1, map_one])
  ne_vw := fun h1 => h.ne_vw (by rw [← map_mul, h1, map_one])
  ne_uvw := fun h1 => h.ne_uvw (by rw [← map_mul, ← map_mul, h1, map_one])

end E8Triple

theorem mul_self_eq_one_of_mem_closure {G : Type*} [Group G] {u v w : G}
    (h : E8Triple u v w) {g : G} (hg : g ∈ closure ({u, v, w} : Set G)) : g * g = 1 := by
  set S : Set G := {u, v, w} with hS
  have hSc : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    intro s hs t ht
    simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with hs | hs | hs <;> rcases ht with ht | ht | ht <;> rw [hs, ht]
    · exact h.comm_uv
    · exact h.comm_uw
    · exact h.comm_uv.symm
    · exact h.comm_vw
    · exact h.comm_uw.symm
    · exact h.comm_vw.symm
  have hcent : closure S ≤ centralizer S := by
    rw [closure_le]
    intro s hs
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro t ht
    exact hSc t ht s hs
  have hcomm : ∀ x ∈ closure S, ∀ y ∈ closure S, x * y = y * x := by
    intro x hx y hy
    have hle : closure S ≤ centralizer ({y} : Set G) := by
      rw [closure_le]
      intro s hs
      rw [SetLike.mem_coe, mem_centralizer_iff]
      intro t ht
      rw [Set.mem_singleton_iff] at ht
      subst ht
      exact (mem_centralizer_iff.mp (hcent hy) s hs).symm
    exact (mem_centralizer_iff.mp (hle hx) y (Set.mem_singleton y)).symm
  induction hg using closure_induction with
  | mem x hx =>
    simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact h.sq_u
    · exact h.sq_v
    · exact h.sq_w
  | one => exact one_mul 1
  | mul x y hx hy ihx ihy =>
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hcomm y hy x hx]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ihx => rw [← mul_inv_rev, ihx, inv_one]

theorem false_of_sylow {G : Type*} [Group G] [Finite G] {H P₀ : Subgroup G}
    (hR : ∃ R : Sylow 2 H, (R : Subgroup H) = P₀.subgroupOf H)
    (hy : ∃ y ∈ P₀, Nat.card P₀ = 2 * orderOf y) {u v w : G} (hu : u ∈ H) (hv : v ∈ H)
    (hw : w ∈ H) (h : E8Triple u v w) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := hR
  obtain ⟨y, hyP, hcard⟩ := hy
  set U : H := ⟨u, hu⟩
  set V : H := ⟨v, hv⟩
  set W : H := ⟨w, hw⟩
  have hT : E8Triple U V W := E8Triple.comap (φ := H.subtype) H.subtype_injective h
  set E : Subgroup H := closure ({U, V, W} : Set H)
  have hE : IsPGroup 2 E := fun g =>
    ⟨1, by rw [pow_one, sq]; exact Subtype.ext (mul_self_eq_one_of_mem_closure hT g.2)⟩
  obtain ⟨S, hES⟩ := hE.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq H R S
  have hconj : ∀ X ∈ ({U, V, W} : Set H), ((k⁻¹ * X * k : H) : G) ∈ P₀ := by
    intro X hX
    have hXS : X ∈ (S : Subgroup H) := hES (subset_closure hX)
    rw [← hk, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hXS
    have e : (MulAut.conj k)⁻¹ • X = k⁻¹ * X * k := by
      rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
    rw [e, hR, mem_subgroupOf] at hXS
    exact hXS
  have hT' := (hT.map_injective (MulAut.conj k⁻¹).toMonoidHom
    (MulAut.conj k⁻¹).injective).map_injective H.subtype H.subtype_injective
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, coe_subtype] at hT'
  have : Finite P₀ := inferInstance
  exact false_of_cyclic_index_two hyP hcard (hconj U (by simp)) (hconj V (by simp))
    (hconj W (by simp)) hT'

structure X10Hyp {P : Type*} [Group P] (s : MulAut P) (J : Subgroup P) (Q : ℕ) : Prop where
  noE8 : ∀ u ∈ J, ∀ v ∈ J, ∀ w ∈ J, ¬ E8Triple u v w
  noE4 : ∀ x y : P, s x = x → s y = y → (∀ j ∈ J, x * j = j * x) → (∀ j ∈ J, y * j = j * y) →
    x * x = 1 → y * y = 1 → x * y = y * x → x ≠ 1 → y ≠ 1 → x * y ≠ 1 →
    MulAut.conj x ≠ s → MulAut.conj y ≠ s → MulAut.conj (x * y) ≠ s → False
  card : Nat.card J = Nat.card (pPrimeCore 2 J) * (Q * (Q ^ 2 - 1) / 2)

theorem congr_conj {P P' : Type*} [Group P] [Group P'] (e : P ≃* P') (g : P) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  change e (g * e.symm x * g⁻¹) = e g * x * (e g)⁻¹
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem X10Hyp.map {P P' : Type*} [Group P] [Group P'] {s : MulAut P} {J : Subgroup P} {Q : ℕ}
    (h : X10Hyp s J Q) (e : P ≃* P') :
    X10Hyp (MulAut.congr e s) (J.map e.toMonoidHom) Q where
  noE8 := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ hT
    exact h.noE8 u hu v hv w hw (E8Triple.comap (φ := e.toMonoidHom) e.injective hT)
  noE4 := by
    intro x y hx hy hxJ hyJ hxx hyy hxy hx1 hy1 hxy1 hcx hcy hcxy
    have hs : ∀ z, MulAut.congr e s z = e (s (e.symm z)) := fun z => rfl
    have hfix : ∀ z, MulAut.congr e s z = z → s (e.symm z) = e.symm z := fun z hz => by
      rw [hs] at hz
      have := congrArg e.symm hz
      rwa [MulEquiv.symm_apply_apply] at this
    have hcen : ∀ z, (∀ j ∈ J.map e.toMonoidHom, z * j = j * z) →
        ∀ j ∈ J, e.symm z * j = j * e.symm z := fun z hz j hj => by
      have := hz (e j) ⟨j, hj, rfl⟩
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, this]
    have hconj : ∀ z, MulAut.conj z ≠ MulAut.congr e s → MulAut.conj (e.symm z) ≠ s :=
      fun z hz hc => hz (by rw [← hc, congr_conj, MulEquiv.apply_symm_apply])
    have hsq : ∀ z, z * z = 1 → e.symm z * e.symm z = 1 := fun z hz => by
      rw [← map_mul, hz, map_one]
    have hne : ∀ z, z ≠ 1 → e.symm z ≠ 1 := fun z hz h1 => hz (by
      rw [← MulEquiv.apply_symm_apply e z, h1, map_one])
    refine h.noE4 (e.symm x) (e.symm y) (hfix x hx) (hfix y hy) (hcen x hxJ) (hcen y hyJ)
      (hsq x hxx) (hsq y hyy) (by rw [← map_mul, hxy, map_mul]) (hne x hx1) (hne y hy1)
      (by rw [← map_mul]; exact hne _ hxy1) (hconj x hcx) (hconj y hcy) ?_
    rw [← map_mul]
    exact hconj _ hcxy
  card := by
    have eJ : ↥J ≃* ↥(J.map e.toMonoidHom) := J.equivMapOfInjective e.toMonoidHom e.injective
    rw [← Nat.card_congr eJ.toEquiv, ← pPrimeCore_map_iso 2 eJ, h.card]
    congr 1
    exact Nat.card_congr ((pPrimeCore 2 ↥J).equivMapOfInjective _ eJ.injective).toEquiv

theorem conjNormal_coe {G : Type*} [Group G] {N : Subgroup G} [N.Normal] (x : N) :
    (MulAut.conjNormal (x : G) : MulAut N) = MulAut.conj x := by
  ext y
  simp only [MulAut.conjNormal_apply, MulAut.conj_apply, coe_mul, coe_inv]

theorem x10Hyp_of_conf {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal] {p f : ℕ}
    (hp2 : p ≠ 2) {a : G} {J P₀ : Subgroup G} (ha : orderOf a = 2) (hJN : J ≤ N)
    (hJC : J ≤ centralizer ({a} : Set G))
    (hJm : Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p (2 * f))
    (hR : ∃ R : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ coreActionKernel J),
      (R : Subgroup _) = P₀.subgroupOf (centralizer ({a} : Set G) ⊓ coreActionKernel J))
    (hy : ∃ y ∈ P₀, Nat.card P₀ = 2 * orderOf y) {P : Type*} [Group P] (θ : ↥N ≃* P) :
    X10Hyp (MulAut.congr θ (MulAut.conjNormal a)) ((J.subgroupOf N).map θ.toMonoidHom)
      ((p ^ f) ^ 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ha; exact absurd ha (by norm_num)
  set s := MulAut.congr θ (MulAut.conjNormal a : MulAut N) with hsdef
  have hs : ∀ z, s z = θ (MulAut.conjNormal a (θ.symm z)) := fun z => rfl
  have hfix : ∀ z, s z = z → a * (θ.symm z : G) = (θ.symm z : G) * a := fun z hz => by
    rw [hs] at hz
    have e : MulAut.conjNormal a (θ.symm z) = θ.symm z := by
      rw [← θ.symm_apply_apply (MulAut.conjNormal a (θ.symm z)), hz]
    have e' := congrArg Subtype.val e
    rw [MulAut.conjNormal_apply] at e'
    calc a * (θ.symm z : G) = a * (θ.symm z : G) * a⁻¹ * a := by group
      _ = (θ.symm z : G) * a := by rw [e']
  have hmemJ : ∀ j (hj : j ∈ J), (⟨j, hJN hj⟩ : N) ∈ J.subgroupOf N := fun j hj => by
    rw [mem_subgroupOf]
    exact hj
  have hcen : ∀ z, (∀ j ∈ (J.subgroupOf N).map θ.toMonoidHom, z * j = j * z) →
      ∀ j ∈ J, (θ.symm z : G) * j = j * (θ.symm z : G) := fun z hz j hj => by
    have := hz (θ ⟨j, hJN hj⟩) ⟨_, hmemJ j hj, rfl⟩
    have e := congrArg (fun t => ((θ.symm t : N) : G)) this
    simp only [map_mul, MulEquiv.symm_apply_apply, coe_mul] at e
    exact e
  have hcoreJ : ∀ g : G, (∀ j ∈ J, g * j = j * g) → g ∈ coreActionKernel J := fun g hg => by
    refine mem_coreActionKernel.mpr ⟨?_, fun j hj => ?_⟩
    · rw [mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have e : g * h * g⁻¹ = h := by rw [hg h hh, mul_inv_cancel_right]
        rw [e]
        exact hh
      · intro hh
        have hc := hg _ hh
        have e : h = g * h * g⁻¹ := by
          calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
            _ = g⁻¹ * (g * (g * h * g⁻¹)) := by rw [mul_assoc g⁻¹, ← hc]
            _ = g * h * g⁻¹ := by group
        rw [e]
        exact hh
    · have e : j⁻¹ * g⁻¹ * j * g = 1 := by
        calc j⁻¹ * g⁻¹ * j * g = j⁻¹ * g⁻¹ * (j * g) := by group
          _ = j⁻¹ * g⁻¹ * (g * j) := by rw [hg j hj]
          _ = 1 := by group
      rw [e]
      exact one_mem _
  obtain ⟨hp, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data hJm
  refine ⟨?_, ?_, ?_⟩
  ·
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ hT
    have hT1 : E8Triple u v w := E8Triple.comap (φ := θ.toMonoidHom) θ.injective hT
    have hT2 : E8Triple (u : G) v w := hT1.map_injective N.subtype N.subtype_injective
    have hT3 : E8Triple (⟨u, mem_subgroupOf.mp hu⟩ : J) ⟨v, mem_subgroupOf.mp hv⟩
        ⟨w, mem_subgroupOf.mp hw⟩ := E8Triple.comap (φ := J.subtype) J.subtype_injective hT2
    have hodd : Odd (Nat.card F) := by
      rw [hF]
      exact (hp.odd_of_ne_two hp2).pow
    have h2 : (2 : F) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
    refine false_of_statedProjSL h2 (hT3.map (e.toMonoidHom.comp
      (QuotientGroup.mk' (pPrimeCore 2 ↥J))) fun g hg h1 => ?_)
    have h1' : QuotientGroup.mk' (pPrimeCore 2 ↥J) g = 1 :=
      e.injective (by rw [map_one]; exact h1)
    have hgO : g ∈ pPrimeCore 2 ↥J := (QuotientGroup.eq_one_iff g).mp h1'
    have hd2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hg)
    have hdO : orderOf g ∣ Nat.card (pPrimeCore 2 ↥J) := by
      have := orderOf_dvd_natCard (⟨g, hgO⟩ : pPrimeCore 2 ↥J)
      rwa [Subgroup.orderOf_mk] at this
    have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥J)
    have h1g : orderOf g = 1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hdO
    exact orderOf_eq_one_iff.mp h1g
  ·
    intro x y hx hy' hxJ hyJ hxx hyy hxy hx1 hy1 hxy1 hcx hcy hcxy
    have hsq : ∀ z, z * z = 1 → ((θ.symm z : N) : G) * (θ.symm z : N) = 1 := fun z hz => by
      rw [← coe_mul, ← map_mul, hz, map_one, coe_one]
    have hne : ∀ z, z ≠ 1 → ((θ.symm z : N) : G) ≠ 1 := fun z hz h1 => hz (by
      have h1' : θ.symm z = 1 := Subtype.ext h1
      rw [← MulEquiv.apply_symm_apply θ z, h1', map_one])
    have hna : ∀ z, MulAut.conj z ≠ s → ((θ.symm z : N) : G) ≠ a := fun z hz h1 => hz (by
      rw [hsdef, ← h1, conjNormal_coe, congr_conj, MulEquiv.apply_symm_apply])
    have hinv : ∀ g : G, a * g = 1 → g = a := fun g hg => by
      calc g = a⁻¹ * (a * g) := by group
        _ = a := by rw [hg, mul_one, inv_eq_of_mul_eq_one_right haa]
    have hT : E8Triple a ((θ.symm x : N) : G) (θ.symm y : N) :=
      { sq_u := haa
        sq_v := hsq x hxx
        sq_w := hsq y hyy
        comm_uv := hfix x hx
        comm_uw := hfix y hy'
        comm_vw := by rw [← coe_mul, ← coe_mul, ← map_mul, hxy, map_mul]
        ne_u := ha1
        ne_v := hne x hx1
        ne_w := hne y hy1
        ne_uv := fun h1 => hna x hcx (hinv _ h1)
        ne_uw := fun h1 => hna y hcy (hinv _ h1)
        ne_vw := by rw [← coe_mul, ← map_mul]; exact hne _ hxy1
        ne_uvw := fun h1 => hna (x * y) hcxy (by
          rw [map_mul, coe_mul]
          exact hinv _ (by rw [← mul_assoc]; exact h1)) }
    have hmemC : ∀ g : G, a * g = g * a → g ∈ centralizer ({a} : Set G) := fun g hg => by
      rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hg
    have haJ : ∀ j ∈ J, a * j = j * a := fun j hj =>
      (mem_centralizer_iff.mp (hJC hj) a (Set.mem_singleton a))
    exact false_of_sylow hR hy ⟨hmemC a rfl, hcoreJ a haJ⟩
      ⟨hmemC _ (hfix x hx), hcoreJ _ (hcen x hxJ)⟩ ⟨hmemC _ (hfix y hy'), hcoreJ _ (hcen y hyJ)⟩
      hT
  ·
    have eJ : ↥J ≃* ↥((J.subgroupOf N).map θ.toMonoidHom) :=
      (subgroupOfEquivOfLe hJN).symm.trans
        ((J.subgroupOf N).equivMapOfInjective θ.toMonoidHom θ.injective)
    rw [← Nat.card_congr eJ.toEquiv, ← pPrimeCore_map_iso 2 eJ,
      Nat.card_congr ((pPrimeCore 2 ↥J).equivMapOfInjective _ eJ.injective).toEquiv.symm,
      (pPrimeCore 2 ↥J).card_eq_card_quotient_mul_card_subgroup,
      CatFactsSp4.card_of_lieModel_psl_sq hp2 hJm,
      mul_comm]

end CFSG.ComponentClassification.GSThmB.X10Orth
