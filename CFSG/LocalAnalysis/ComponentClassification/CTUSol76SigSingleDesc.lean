module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleSimple
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleFam

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {Q : Type} [Group Q] [Finite Q]

theorem exists_orderOf_eq_two_pow_of_mem_center (hO : pPrimeCore 2 Q = ⊥) {z : Q}
    (hz : z ∈ center Q) : ∃ k : ℕ, orderOf z = 2 ^ k := by
  obtain ⟨a, m, hm, hzm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  refine ⟨a, ?_⟩
  have hwo : orderOf (z ^ (2 ^ a)) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hzm⟩, hzm,
      Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
  have hwZ : z ^ (2 ^ a) ∈ center Q := pow_mem hz _
  have hnorm : (zpowers (z ^ (2 ^ a))).Normal := by
    constructor
    intro k hk g
    have hkZ : k ∈ center Q := (zpowers_le.mpr hwZ) hk
    rw [mem_center_iff.mp hkZ g, mul_inv_cancel_right]
    exact hk
  have hle : zpowers (z ^ (2 ^ a)) ≤ pPrimeCore 2 Q := le_sSup ⟨hnorm, by
    rw [Nat.card_zpowers, hwo]
    exact Nat.coprime_two_left.mpr hm⟩
  rw [hO, le_bot_iff, zpowers_eq_bot] at hle
  rw [hle, orderOf_one] at hwo
  rw [hzm, ← hwo, mul_one]

theorem inf_center_eq_bot_of_forall (hO : pPrimeCore 2 Q = ⊥) {X : Subgroup Q}
    (hX : ∀ x ∈ X, orderOf x = 2 → x ∈ center Q → False) : X ⊓ center Q = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzX, hzZ⟩
  obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow_of_mem_center hO hzZ
  rcases k with _ | k
  · rw [pow_zero, orderOf_eq_one_iff] at hk
    exact (mem_bot).mpr hk
  · exfalso
    have hw2 : orderOf (z ^ (2 ^ k)) = 2 := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨2, by rw [hk, pow_succ]⟩, hk,
        pow_succ, Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
    exact hX _ (pow_mem hzX _) hw2 (pow_mem hzZ _)

theorem inf_center_eq_bot_left (hQ : IsQuasisimple Q) (hO : pPrimeCore 2 Q = ⊥)
    {X Y : Subgroup Q} (hXp : ⁅X, X⁆ = X) (hXq : IsQuasisimple (↥X ⧸ pPrimeCore 2 ↥X))
    (hcomm : ⁅X, Y⁆ ≤ oddCoreIn X ⊓ oddCoreIn Y)
    (hP : ∀ x ∈ X, orderOf x = 2 → ∃ P : Subgroup Q,
      IsTwoComponentIn P (centralizer ({x} : Set Q)) ∧
      P ⊔ oddCoreIn (centralizer ({x} : Set Q)) =
        twoLayerIn (Y ⊓ centralizer ({x} : Set Q)) ⊔ oddCoreIn (centralizer ({x} : Set Q))) :
    X ⊓ center Q = ⊥ :=
  inf_center_eq_bot_of_forall hO fun _ hx hx2 hxZ =>
    false_of_center_mem_left hQ hO hXp hXq hcomm hP hx hx2 hxZ

theorem inf_center_eq_bot_right (hQ : IsQuasisimple Q) (hO : pPrimeCore 2 Q = ⊥)
    {X Y : Subgroup Q} (hYp : ⁅Y, Y⁆ = Y) (hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y))
    (hcomm : ⁅X, Y⁆ ≤ oddCoreIn X ⊓ oddCoreIn Y)
    (hP : ∀ y ∈ Y, orderOf y = 2 → ∃ P : Subgroup Q,
      IsTwoComponentIn P (centralizer ({y} : Set Q)) ∧
      P ⊔ oddCoreIn (centralizer ({y} : Set Q)) =
        twoLayerIn (X ⊓ centralizer ({y} : Set Q)) ⊔ oddCoreIn (centralizer ({y} : Set Q))) :
    Y ⊓ center Q = ⊥ :=
  inf_center_eq_bot_of_forall hO fun _ hy hy2 hyZ =>
    false_of_center_mem_right hQ hO hYp hYq hcomm hP hy hy2 hyZ

omit [Finite Q] in
theorem orderOf_eq_two_of_mk {X : Subgroup Q} (hXZ : X ⊓ center Q = ⊥) {x : Q} (hxX : x ∈ X)
    (hx2 : orderOf (QuotientGroup.mk' (center Q) x) = 2) : orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : x ^ 2 ∈ X ⊓ center Q := by
    refine ⟨pow_mem hxX 2, ?_⟩
    have h1 := pow_orderOf_eq_one (QuotientGroup.mk' (center Q) x)
    rw [hx2, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  rw [hXZ, mem_bot] at hsq
  refine orderOf_eq_prime hsq fun h1 => ?_
  rw [h1, map_one, orderOf_one] at hx2
  exact absurd hx2 (by norm_num)

omit [Finite Q] in
theorem map_centralizer_le_centralizer_mk (x : Q) :
    (centralizer ({x} : Set Q)).map (QuotientGroup.mk' (center Q)) ≤
      centralizer ({QuotientGroup.mk' (center Q) x} : Set (Q ⧸ center Q)) := by
  rintro _ ⟨c, hc, rfl⟩
  have hc' := mem_centralizer_singleton_iff.mp hc
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hc']

omit [Finite Q] in
theorem mem_normalizer_centralizer_of_mk {x q : Q}
    (hq : QuotientGroup.mk' (center Q) q ∈
      centralizer ({QuotientGroup.mk' (center Q) x} : Set (Q ⧸ center Q))) :
    q ∈ normalizer (centralizer ({x} : Set Q) : Set Q) := by
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, QuotientGroup.mk'_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq] at hq
  obtain ⟨c, hc⟩ : ∃ c : Q, c = (q * x)⁻¹ * (x * q) := ⟨_, rfl⟩
  have hc' : ∀ g : Q, g * c = c * g := mem_center_iff.mp (hc ▸ hq)
  have hconj : q⁻¹ * x * q = x * c := by rw [hc]; group
  have key : ∀ y : Q, y * x = x * y ↔ q * y * q⁻¹ * x = x * (q * y * q⁻¹) := by
    intro y
    have e1 : q * y * q⁻¹ * x = x * (q * y * q⁻¹) ↔
        y * (q⁻¹ * x * q) = (q⁻¹ * x * q) * y := by
      constructor
      · intro h
        calc y * (q⁻¹ * x * q) = q⁻¹ * (q * y * q⁻¹ * x) * q := by group
          _ = q⁻¹ * (x * (q * y * q⁻¹)) * q := by rw [h]
          _ = (q⁻¹ * x * q) * y := by group
      · intro h
        calc q * y * q⁻¹ * x = q * (y * (q⁻¹ * x * q)) * q⁻¹ := by group
          _ = q * ((q⁻¹ * x * q) * y) * q⁻¹ := by rw [h]
          _ = x * (q * y * q⁻¹) := by group
    have e2 : y * (x * c) = (x * c) * y ↔ y * x = x * y := by
      rw [← mul_assoc, mul_assoc x c y, ← hc' y, ← mul_assoc]
      exact mul_left_inj c
    rw [e1, hconj, e2]
  rw [mem_normalizer_iff]
  intro y
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  exact key y

omit [Finite Q] in
theorem map_subgroupOf_normal {x : Q} {S : Subgroup Q}
    (hSn : normalizer (centralizer ({x} : Set Q) : Set Q) ≤ normalizer (S : Set Q)) :
    ((S.map (QuotientGroup.mk' (center Q))).subgroupOf
      (centralizer ({QuotientGroup.mk' (center Q) x} : Set (Q ⧸ center Q)))).Normal := by
  constructor
  rintro ⟨s, hsD⟩ hs ⟨g, hg⟩
  rw [mem_subgroupOf] at hs ⊢
  obtain ⟨s', hs', rfl⟩ := hs
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (center Q) g
  have hqN := hSn (mem_normalizer_centralizer_of_mk hg)
  refine ⟨q * s' * q⁻¹, (mem_normalizer_iff.mp hqN s').mp hs', ?_⟩
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

omit [Finite Q] in
theorem isSubnormal_subgroupOf_of_normal {G : Type*} [Group G] {L C₀ D : Subgroup G}
    (hLC : L ≤ C₀) (hCD : C₀ ≤ D) (hL : (L.subgroupOf C₀).IsSubnormal)
    (hN : (C₀.subgroupOf D).Normal) : (L.subgroupOf D).IsSubnormal := by
  have hLD : L.subgroupOf D ≤ C₀.subgroupOf D := fun _ hx => hLC hx
  refine Subgroup.IsSubnormal.trans hLD ?_ hN.isSubnormal
  have h2 := hL.map (f := (subgroupOfEquivOfLe hCD).symm.toMonoidHom)
    (subgroupOfEquivOfLe hCD).symm.surjective
  convert h2 using 1
  ext ⟨⟨y, hyD⟩, hyC⟩
  constructor
  · intro hy
    refine ⟨⟨y, hyC⟩, ?_, ?_⟩
    · simpa [mem_subgroupOf] using hy
    · rfl
  · rintro ⟨z, hz, hzy⟩
    have hzy' : (z : G) = y := by
      have := congrArg (fun w : ↥(C₀.subgroupOf D) => ((w : ↥D) : G)) hzy
      simpa using this
    simp only [mem_subgroupOf] at hz ⊢
    rw [← hzy']
    exact hz

theorem isTwoComponentIn_map_center (hO : pPrimeCore 2 Q = ⊥) {x : Q} {P : Subgroup Q}
    (hP : IsTwoComponentIn P (centralizer ({x} : Set Q))) :
    IsTwoComponentIn (P.map (QuotientGroup.mk' (center Q)))
      (centralizer ({QuotientGroup.mk' (center Q) x} : Set (Q ⧸ center Q))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC₀D := map_centralizer_le_centralizer_mk x
  have hPC₀ : P.map (QuotientGroup.mk' (center Q)) ≤
      (centralizer ({x} : Set Q)).map (QuotientGroup.mk' (center Q)) := map_mono hP.1
  set ψ := (QuotientGroup.mk' (center Q)).subgroupMap (centralizer ({x} : Set Q)) with hψ
  have hker : ∀ c ∈ ψ.ker, (c : Q) ∈ center Q := by
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have h1 := congrArg Subtype.val hc
    simp only [hψ, MonoidHom.subgroupMap_apply_coe, OneMemClass.coe_one] at h1
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hkerZ : ψ.ker ≤ center ↥(centralizer ({x} : Set Q)) := by
    intro c hc
    rw [mem_center_iff]
    intro d
    exact Subtype.ext (mem_center_iff.mp (hker c hc) d)
  have hker2 : IsPGroup 2 ψ.ker := by
    refine IsPGroup.iff_orderOf.mpr fun k => ?_
    obtain ⟨j, hj⟩ := exists_orderOf_eq_two_pow_of_mem_center hO (hker k k.2)
    exact ⟨j, by rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]; exact hj⟩
  have himg := CentralTwoKernelComponents.image ψ
    ((QuotientGroup.mk' (center Q)).subgroupMap_surjective _) hkerZ hker2
    (P.subgroupOf (centralizer ({x} : Set Q)))
    ((CatalogueBAlternating.pComponent_two_iff _).mp hP.2)
  have hC₀pc : IsPComponent 2 ((P.map (QuotientGroup.mk' (center Q))).subgroupOf
      ((centralizer ({x} : Set Q)).map (QuotientGroup.mk' (center Q)))) := by
    rw [subgroupOf_map_eq_map_subgroupMap _ hP.1]
    exact (CatalogueBAlternating.pComponent_two_iff _).mpr himg
  obtain ⟨hsub, hres, hqs⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 _ _ hPC₀).mp hC₀pc
  have hN := map_subgroupOf_normal (x := x) (S := centralizer ({x} : Set Q)) le_rfl
  refine ⟨hPC₀.trans hC₀D, (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 _ _
    (hPC₀.trans hC₀D)).mpr ⟨isSubnormal_subgroupOf_of_normal hPC₀ hC₀D hsub hN, hres, hqs⟩⟩

omit [Finite Q] in
theorem commutator_twoLayerIn_self (S : Subgroup Q) :
    ⁅twoLayerIn S, twoLayerIn S⁆ = twoLayerIn S := by
  rw [twoLayerIn, ← Subgroup.map_commutator, UnbalancedCorr.pLayer_two_isPerfect]

theorem oddCoverAt_map (hO : pPrimeCore 2 Q = ⊥) {X Y : Subgroup Q} (hXZ : X ⊓ center Q = ⊥)
    (hP : ∀ x ∈ X, orderOf x = 2 → ∃ P : Subgroup Q,
      IsTwoComponentIn P (centralizer ({x} : Set Q)) ∧
      P ⊔ oddCoreIn (centralizer ({x} : Set Q)) =
        twoLayerIn (Y ⊓ centralizer ({x} : Set Q)) ⊔ oddCoreIn (centralizer ({x} : Set Q)))
    {t : Q ⧸ center Q} (ht : t ∈ X.map (QuotientGroup.mk' (center Q))) (ht2 : orderOf t = 2) :
    OddCoverAt (Y.map (QuotientGroup.mk' (center Q))) t := by
  obtain ⟨x, hxX, rfl⟩ := ht
  obtain ⟨P, hPC, heq⟩ := hP x hxX (orderOf_eq_two_of_mk hXZ hxX ht2)
  have hOC : oddCoreIn (centralizer ({x} : Set Q)) ≤ centralizer ({x} : Set Q) :=
    map_subtype_le _
  have hLC : twoLayerIn (Y ⊓ centralizer ({x} : Set Q)) ≤ Y ⊓ centralizer ({x} : Set Q) :=
    map_subtype_le _
  refine ⟨P.map (QuotientGroup.mk' (center Q)),
    (oddCoreIn (centralizer ({x} : Set Q))).map (QuotientGroup.mk' (center Q)),
    (twoLayerIn (Y ⊓ centralizer ({x} : Set Q))).map (QuotientGroup.mk' (center Q)),
    isTwoComponentIn_map_center hO hPC,
    (map_mono hOC).trans (map_centralizer_le_centralizer_mk x),
    map_subgroupOf_normal fun q hq => mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn hq),
    ?_, le_inf (map_mono (hLC.trans inf_le_left))
      ((map_mono (hLC.trans inf_le_right)).trans (map_centralizer_le_centralizer_mk x)),
    by rw [← Subgroup.map_commutator, commutator_twoLayerIn_self],
    (map_mono (le_sup_left.trans heq.le)).trans (Subgroup.map_sup _ _ _).le,
    (map_mono (le_sup_left.trans heq.ge)).trans (Subgroup.map_sup _ _ _).le⟩
  exact Odd.of_dvd_nat (Nat.coprime_two_left.mp (coprime_card_oddCoreIn _))
    (Subgroup.card_map_dvd _ _)

omit [Finite Q] in
theorem injective_subgroupMap_mk {X : Subgroup Q} (hXZ : X ⊓ center Q = ⊥) :
    Function.Injective ((QuotientGroup.mk' (center Q)).subgroupMap X) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : QuotientGroup.mk' (center Q) (a : Q) = 1 := congrArg Subtype.val ha
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have ha' : (a : Q) ∈ X ⊓ center Q := ⟨a.2, h1⟩
  rw [hXZ, mem_bot] at ha'
  exact Subtype.ext ha'

omit [Finite Q] in
theorem isQuasisimple_map_mk {X : Subgroup Q} (hXZ : X ⊓ center Q = ⊥)
    (hXq : IsQuasisimple (↥X ⧸ pPrimeCore 2 ↥X)) :
    IsQuasisimple (↥(X.map (QuotientGroup.mk' (center Q))) ⧸
      pPrimeCore 2 ↥(X.map (QuotientGroup.mk' (center Q)))) := by
  let e : ↥X ≃* ↥(X.map (QuotientGroup.mk' (center Q))) :=
    MulEquiv.ofBijective _ ⟨injective_subgroupMap_mk hXZ,
      (QuotientGroup.mk' (center Q)).subgroupMap_surjective X⟩
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv (QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)).symm
      (CatalogueBAlternating.quasisimple_iff_native.mp hXq))

theorem pRank_le_pRank_map_mk {X : Subgroup Q} (hXZ : X ⊓ center Q = ⊥) :
    CFSG.Open.pRank 2 X ≤ CFSG.Open.pRank 2 (X.map (QuotientGroup.mk' (center Q))) := by
  obtain ⟨E, hEX, hE, hcard⟩ := SectionRank.exists_pRank (by norm_num : 1 < 2) X
  refine SectionRank.le_pRank (by norm_num) (map_mono hEX)
    (SectionRank.isElemAbelian_map hE _) ?_
  rw [← hcard]
  have hinj := injective_subgroupMap_mk (eq_bot_iff.mpr ((inf_le_inf_right _ hEX).trans hXZ.le))
  exact (Nat.card_congr (Equiv.ofBijective _
    ⟨hinj, (QuotientGroup.mk' (center Q)).subgroupMap_surjective E⟩)).symm

theorem map_oddCoreIn_le_oddCoreIn_map (X : Subgroup Q) :
    (oddCoreIn X).map (QuotientGroup.mk' (center Q)) ≤
      oddCoreIn (X.map (QuotientGroup.mk' (center Q))) := by
  calc (oddCoreIn X).map (QuotientGroup.mk' (center Q))
      = ((pPrimeCore 2 ↥X).map ((QuotientGroup.mk' (center Q)).subgroupMap X)).map
          (X.map (QuotientGroup.mk' (center Q))).subtype := by
        rw [oddCoreIn, Subgroup.map_map, Subgroup.map_map]
        rfl
    _ ≤ oddCoreIn (X.map (QuotientGroup.mk' (center Q))) :=
        map_mono (map_pPrimeCore_le _ ((QuotientGroup.mk' (center Q)).subgroupMap_surjective X))

theorem singleComponentQuasisimpleAt_of_simpleAt {P : (S : Type) → [Group S] → Prop}
    (h : SingleComponentSimpleAt P) : SingleComponentQuasisimpleAt P := by
  intro Q _ _ hQ hO hPQ X Y hXp hYp hXq hYq hXr hYr hcomm hP₁ hP₂
  have hXZ := inf_center_eq_bot_left hQ hO hXp hXq hcomm hP₁
  have hYZ := inf_center_eq_bot_right hQ hO hYp hYq hcomm hP₂
  have : IsSimpleGroup (Q ⧸ center Q) := hQ.2.1
  refine h (Q ⧸ center Q) this hPQ (X.map (QuotientGroup.mk' (center Q)))
    (Y.map (QuotientGroup.mk' (center Q))) (by rw [← Subgroup.map_commutator, hXp])
    (by rw [← Subgroup.map_commutator, hYp]) (isQuasisimple_map_mk hXZ hXq)
    (isQuasisimple_map_mk hYZ hYq) (hXr.trans (pRank_le_pRank_map_mk hXZ))
    (hYr.trans (pRank_le_pRank_map_mk hYZ)) ?_
    (fun t ht ht2 => oddCoverAt_map hO hXZ hP₁ ht ht2)
    (fun t ht ht2 => oddCoverAt_map hO hYZ hP₂ ht ht2)
  rw [← Subgroup.map_commutator]
  exact (map_mono hcomm).trans (le_inf
    ((map_mono inf_le_left).trans (map_oddCoreIn_le_oddCoreIn_map X))
    ((map_mono inf_le_right).trans (map_oddCoreIn_le_oddCoreIn_map Y)))

end CFSG.ComponentClassification.Sol76.Sig
