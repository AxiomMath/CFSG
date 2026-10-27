module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1111b
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Fi22
public import CFSG.GH74.GLS.LU.Local.FiveCbarF
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7TrSub

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut Fi22Facts IsFiTwentyTwo)

section PGroup

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_omegaOne_centerOf {p : ℕ} [Fact p.Prime] {R W : Subgroup G} (hR : IsPGroup p R)
    (hWR : W ≤ R) (hWn : (W.subgroupOf R).Normal) (hW : W ≠ ⊥) :
    ∃ z ∈ W, z ∈ omegaOne p (centerOf R) ∧ z ≠ 1 := by
  haveI : Group.IsNilpotent ↥R := hR.isNilpotent
  have hW' : W.subgroupOf R ≠ ⊥ := by
    intro hb
    apply hW
    rw [eq_bot_iff]
    intro w hw
    have : (⟨w, hWR hw⟩ : ↥R) ∈ W.subgroupOf R := hw
    rw [hb, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hW'
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  obtain ⟨k, hk⟩ := hR z
  have hk' : (z : G) ^ (p ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hz1' : (z : G) ≠ 1 := fun h1 => hz1 (Subtype.ext (Subtype.ext h1))
  obtain ⟨j, hj5, hj1⟩ := exists_pow_of_order_p hk' hz1'
  have hzW : (z : G) ^ j ∈ W :=
    Subgroup.pow_mem _ (Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hz).1) j
  have hzc : (z : G) ∈ centerOf R := Subgroup.mem_map.2 ⟨z, (Subgroup.mem_inf.1 hz).2, rfl⟩
  exact ⟨_, hzW, Subgroup.subset_closure ⟨Subgroup.pow_mem _ hzc j, hj5⟩, hj1⟩

theorem card_le_of_isCyclic_of_pow {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {T : Subgroup X} (hT : IsCyclic ↥T) (hexp : ∀ t ∈ T, t ^ p = 1) : Nat.card ↥T ≤ p := by
  have h1 : Monoid.exponent ↥T ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one
    (fun t => Subtype.ext (by simpa using hexp t t.2))
  rw [IsCyclic.exponent_eq_card] at h1
  exact Nat.le_of_dvd (Fact.out : p.Prime).pos h1

theorem map_mem_of_mem_sup₂ {H : Type*} [Group H] {R W V : Subgroup G} (f : ↥R →* H)
    (S : Subgroup H) (hWR : W ≤ R) (hVR : V ≤ R) (hW : ∀ w (hw : w ∈ W), f ⟨w, hWR hw⟩ ∈ S)
    (hV : ∀ v (hv : v ∈ V), f ⟨v, hVR hv⟩ ∈ S) {x : G} (hxR : x ∈ R) (hx : x ∈ W ⊔ V) :
    f ⟨x, hxR⟩ ∈ S := by
  have hle : W ⊔ V ≤ (S.comap f).map R.subtype := by
    refine sup_le ?_ ?_
    · intro w hw
      exact ⟨⟨w, hWR hw⟩, hW w hw, rfl⟩
    · intro v hv
      exact ⟨⟨v, hVR hv⟩, hV v hv, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hle hx
  have : y = ⟨x, hxR⟩ := Subtype.ext hyx
  rw [← this]
  exact hy

theorem card_le_mul_card_inf_of_le_sup {p : ℕ} [Fact p.Prime] {R W V F : Subgroup G}
    (hWR : W ≤ R) (hVR : V ≤ R) (hVn : (V.subgroupOf R).Normal) (hWc : IsCyclic ↥W)
    (hFR : F ≤ R) (hF : IsElemAbelian p F) (hFWV : F ≤ W ⊔ V) :
    Nat.card ↥F ≤ p * Nat.card ↥(F ⊓ V) := by
  set V' : Subgroup ↥R := V.subgroupOf R with hV'
  set θ : ↥R →* ↥R ⧸ V' := QuotientGroup.mk' V' with hθ
  set F' : Subgroup ↥R := F.subgroupOf R with hF'
  set W' : Subgroup ↥R := W.subgroupOf R with hW'
  haveI hW'c : IsCyclic ↥W' := (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hWR)).2 hWc
  haveI hWimc : IsCyclic ↥(W'.map θ) := isCyclic_of_surjective (θ.subgroupMap W')
    (θ.subgroupMap_surjective W')
  set θF : ↥F' →* ↥R ⧸ V' := θ.comp F'.subtype with hθF
  have hrange : θF.range ≤ W'.map θ := by
    rintro _ ⟨⟨⟨x, hxR⟩, hxF⟩, rfl⟩
    exact map_mem_of_mem_sup₂ θ (W'.map θ) hWR hVR
      (fun w hw => ⟨⟨w, hWR hw⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩)
      (fun v hv => by
        rw [show θ ⟨v, hVR hv⟩ = 1 from (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hv)]
        exact Subgroup.one_mem _)
      hxR (hFWV (Subgroup.mem_subgroupOf.1 hxF))
  have hrc : Nat.card ↥θF.range ≤ p := by
    refine card_le_of_isCyclic_of_pow (Subgroup.isCyclic_of_le hrange) ?_
    rintro _ ⟨⟨⟨x, hxR⟩, hxF⟩, rfl⟩
    show θ ⟨x, hxR⟩ ^ p = 1
    rw [← map_pow]
    have : (⟨x, hxR⟩ : ↥R) ^ p = 1 :=
      Subtype.ext (by simpa using hF.2 x (Subgroup.mem_subgroupOf.1 hxF))
    rw [this, map_one]
  have hkc : Nat.card ↥θF.ker ≤ Nat.card ↥(F ⊓ V) := by
    refine Nat.card_le_card_of_injective (fun k => ⟨(((k : ↥F') : ↥R) : G), ?_⟩) ?_
    · have hk : θ (k : ↥F') = 1 := MonoidHom.mem_ker.1 k.2
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 (k : ↥F').2,
        Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hk)⟩
    · intro k₁ k₂ h
      have h' : (((k₁ : ↥F') : ↥R) : G) = (((k₂ : ↥F') : ↥R) : G) :=
        congrArg (fun z : ↥(F ⊓ V) => (z : G)) h
      exact Subtype.ext (Subtype.ext (Subtype.ext h'))
  have hF'c : Nat.card ↥F' = Nat.card ↥F := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFR).toEquiv
  have h1 : Nat.card ↥θF.ker * Nat.card ↥θF.range = Nat.card ↥F' := by
    rw [← Subgroup.index_ker θF]
    exact Subgroup.card_mul_index _
  rw [← hF'c, ← h1, mul_comm]
  exact Nat.mul_le_mul hrc hkc

theorem exists_sup_zpowers_of_rank_le_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {R X₀ : Subgroup G}
    (hR : IsPGroup p ↥R) (hX₀R : X₀ ≤ R) (hX₀n : (X₀.subgroupOf R).Normal)
    (hrank : ∀ X : Subgroup G, X₀ ≤ X → X ≤ R → (∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ X₀) →
      (∀ x ∈ X, x ^ p ∈ X₀) → Nat.card ↥X ≤ p * Nat.card ↥X₀) :
    ∃ r ∈ R, R ≤ X₀ ⊔ Subgroup.zpowers r := by
  set X₀' : Subgroup ↥R := X₀.subgroupOf R with hX₀'
  set φ : ↥R →* ↥R ⧸ X₀' := QuotientGroup.mk' X₀' with hφ
  have hQp : IsPGroup p (↥R ⧸ X₀') := hR.to_quotient X₀'
  have hcyc : IsCyclic (↥R ⧸ X₀') := by
    by_contra hnc
    haveI : Fact (IsPGroup p (↥R ⧸ X₀')) := ⟨hQp⟩
    obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hp2 hnc
    set X : Subgroup G := (S.comap φ).map R.subtype with hX
    have hXR : X ≤ R := Subgroup.map_subtype_le _
    have hmemX : ∀ x (hx : x ∈ X), φ ⟨x, hXR hx⟩ ∈ S := by
      rintro _ ⟨y, hy, rfl⟩
      exact hy
    have hX₀X : X₀ ≤ X := by
      intro x hx
      refine ⟨⟨x, hX₀R hx⟩, ?_, rfl⟩
      show φ ⟨x, hX₀R hx⟩ ∈ S
      rw [show φ ⟨x, hX₀R hx⟩ = 1 from (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hx)]
      exact S.one_mem
    have hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hSel.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hSp : ∀ a ∈ S, a ^ p = 1 := fun a ha => CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
    have hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ X₀ := by
      intro x hx y hy
      have h1 := hSc _ (hmemX x hx) _ (hmemX y hy)
      have h2 : φ (⟨x, hXR hx⟩ * ⟨y, hXR hy⟩ * ⟨x, hXR hx⟩⁻¹ * ⟨y, hXR hy⟩⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
        group
      exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h2)
    have hpow : ∀ x ∈ X, x ^ p ∈ X₀ := by
      intro x hx
      have h2 : φ (⟨x, hXR hx⟩ ^ p) = 1 := by
        rw [map_pow]
        exact hSp _ (hmemX x hx)
      exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h2)
    have hcard : Nat.card ↥X = p ^ 2 * Nat.card ↥X₀ := by
      rw [hX, Subgroup.card_map_of_injective R.subtype_injective]
      have h1 : Nat.card ↥(S.comap φ) = Nat.card ↥X₀' * Nat.card ↥S :=
        QuotientGroup.card_preimage_mk X₀' (S : Set (↥R ⧸ X₀'))
      rw [h1, hScard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₀R).toEquiv, mul_comm]
    have h := hrank X hX₀X hXR hcomm hpow
    rw [hcard] at h
    have hpos : 0 < Nat.card ↥X₀ := Nat.card_pos
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    have h3 : p * (p * Nat.card ↥X₀) ≤ 1 * (p * Nat.card ↥X₀) := by nlinarith
    have h4 := Nat.le_of_mul_le_mul_right h3 (Nat.mul_pos (by omega) hpos)
    omega
  obtain ⟨q, hq⟩ := isCyclic_iff_exists_zpowers_eq_top.1 hcyc
  obtain ⟨⟨r, hrR⟩, rfl⟩ := QuotientGroup.mk'_surjective X₀' q
  refine ⟨r, hrR, fun x hxR => ?_⟩
  have hx : φ ⟨x, hxR⟩ ∈ Subgroup.zpowers (φ ⟨r, hrR⟩) := hq ▸ Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← map_zpow] at hk
  have h1 : ((⟨r, hrR⟩ : ↥R) ^ k)⁻¹ * ⟨x, hxR⟩ ∈ X₀' := QuotientGroup.eq.1 hk
  have h2 : (r ^ k)⁻¹ * x ∈ X₀ := by
    have := Subgroup.mem_subgroupOf.1 h1
    simpa using this
  have : x = r ^ k * ((r ^ k)⁻¹ * x) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers r k))
    (Subgroup.mem_sup_left h2)

end PGroup

@[expose] def ReIRCClaim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G},
    Cex117 G m p B M E A a K → Type117b p K →
    ∀ R : Subgroup G, IsSylowIn 5 M R → E ⊔ A ≤ R →
    ∀ e ∈ omegaOne 5 (centerOf R), e ≠ 1 →
      ∃ W V : Subgroup G, W ≤ R ∧ V ≤ R ∧ (W.subgroupOf R).Normal ∧ (V.subgroupOf R).Normal ∧
        W ≠ ⊥ ∧ e ∉ W ∧ W ⊓ V = ⊥ ∧
        (IsCyclic ↥W → ∀ F : Subgroup G, F ≤ R → IsElemAbelian 5 F →
          Nat.card ↥F ≤ 5 * Nat.card ↥(F ⊓ (W ⊔ V)))

section Step12

variable {G : Type} [Group G] [Finite G]

theorem exists_normal_plane_le {R Q : Subgroup G} (hR : IsPGroup 5 ↥R) (hQR : Q ≤ R)
    (hQn : (Q.subgroupOf R).Normal) (hQc : ¬ IsCyclic ↥Q) :
    ∃ U : Subgroup G, U ≤ Q ∧ IsEkIn 5 2 R U ∧ (U.subgroupOf R).Normal := by
  obtain ⟨U, hUQ, hUp, hRU⟩ :=
    Claims1111b.input31_5_holds G 5 (by norm_num) (by norm_num) R Q hR hQR hQn hQc
  exact ⟨U, hUQ, ⟨hUQ.trans hQR, hUp.1, hUp.2⟩,
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hUQ.trans hQR)).2 hRU⟩

theorem step12Claim_of_reIRC (h119 : Lemma119Statement) (hRC : ReIRCClaim) :
    Claims1110.Step12Claim := by
  intro G _ _ m p B M E A a K h hb R hR hEAR
  obtain ⟨rfl, hfi⟩ := hb
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hsc := lemma104_ii_holds hS h.pair
  obtain ⟨hrk, -, -, -⟩ := h119 h
  have hRp : IsPGroup 5 ↥R := hR.2.1
  have hZle : omegaOne 5 (centerOf R) ≤ E ⊓ A :=
    le_inf (l1110_omegaOne_centerOf_le hsc.1 (le_sup_left.trans hEAR))
      (l1110_omegaOne_centerOf_le hsc.2 (le_sup_right.trans hEAR))
  have hA0el : IsElemAbelian 5 (E ⊓ A) := l1110_isElemAbelian_of_le hsc.1.2.1 inf_le_left
  have hA0c : Nat.card ↥(E ⊓ A) = 5 ^ 2 := by rw [l1110_card_eq_pow_pRank hA0el, hrk]
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hle : E ⊓ A ≤ ⊥ := hbot ▸ (inf_le_left.trans (le_sup_left.trans hEAR))
    rw [le_bot_iff] at hle
    rw [hle, Subgroup.card_bot] at hA0c
    norm_num at hA0c
  have hRn : ((R : Subgroup G).subgroupOf R).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  obtain ⟨e, -, heZ, he1⟩ := exists_mem_omegaOne_centerOf hRp le_rfl hRn hRne
  obtain ⟨W, V, hWR, hVR, hWn, hVn, hW1, heW, hWV, hrank⟩ := hRC h ⟨rfl, hfi⟩ R hR hEAR e heZ he1
  obtain ⟨z, hzW, hzZ, hz1⟩ := exists_mem_omegaOne_centerOf hRp hWR hWn hW1
  have hcyc : IsCyclic ↥W → ¬ IsCyclic ↥V := by
    intro hWc hVc
    have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS.standing hS.bOne hS.pre
    have hBel : IsElemAbelian 5 B := hS.bOne.1.1
    obtain ⟨y, -, T, hTp, hTM, hRT, hBT⟩ :=
      exists_conj_le_pGroup' hR.1 hR.2.1 hBM (isPGroup_of_elemAb hBel)
    have hTR : T = R := hR.2.2 T hTM hTp hRT
    rw [hTR] at hBT
    have hF₀el : IsElemAbelian 5 (GLBConj y B) := isElemAbelian_conj y hBel
    have hF₀c : 5 ^ 4 ≤ Nat.card ↥(GLBConj y B) := by
      rw [card_conj, hS.standing.card_eq hS.bOne]
      exact Nat.pow_le_pow_right (by norm_num) hS.standing.four_le
    have h1 := hrank hWc (GLBConj y B) hBT hF₀el
    have hF₁el : IsElemAbelian 5 (GLBConj y B ⊓ (W ⊔ V)) :=
      l1110_isElemAbelian_of_le hF₀el inf_le_left
    have h2 := card_le_mul_card_inf_of_le_sup hWR hVR hVn hWc (inf_le_left.trans hBT) hF₁el
      inf_le_right
    have h3 : Nat.card ↥((GLBConj y B ⊓ (W ⊔ V)) ⊓ V) ≤ 5 :=
      card_le_of_isCyclic_of_pow (Subgroup.isCyclic_of_le inf_le_right)
        (fun t ht => hF₁el.2 t (Subgroup.mem_inf.1 ht).1)
    norm_num at hF₀c
    omega
  have he5 : e ^ 5 = 1 := hA0el.2 e (hZle heZ)
  have hz5 : z ^ 5 = 1 := hA0el.2 z (hZle hzZ)
  have heo : orderOf e = 5 := orderOf_eq_of_pow he5 he1
  have hze : z ∉ Subgroup.zpowers e := by
    intro hz
    have hzz := zpowers_eq_of_mem hz hz5 hz1 heo
    have : e ∈ Subgroup.zpowers z := hzz ▸ Subgroup.mem_zpowers e
    exact heW (((Subgroup.zpowers_le).2 hzW) this)
  have hcomm : ∀ x ∈ Subgroup.zpowers e, x * z = z * x := by
    intro x hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hc : Commute e z := elemAbelian_comm hA0el (hZle heZ) (hZle hzZ)
    exact (hc.zpow_left j).eq
  have hcard := card_sup_zpowers hze hz5 hcomm
  rw [Nat.card_zpowers, heo] at hcard
  have hle : Subgroup.zpowers e ⊔ Subgroup.zpowers z ≤ omegaOne 5 (centerOf R) :=
    sup_le ((Subgroup.zpowers_le).2 heZ) ((Subgroup.zpowers_le).2 hzZ)
  have hZeq : omegaOne 5 (centerOf R) = E ⊓ A := by
    refine Subgroup.eq_of_le_of_card_ge hZle ?_
    rw [hA0c]
    calc 5 ^ 2 = Nat.card ↥(Subgroup.zpowers e ⊔ Subgroup.zpowers z) := by rw [hcard]; norm_num
      _ ≤ Nat.card ↥(omegaOne 5 (centerOf R)) := Subgroup.card_le_of_le hle
  refine ⟨hZeq, ?_⟩
  by_cases hWc : IsCyclic ↥W
  · obtain ⟨U, hUV, hU, hUn⟩ := exists_normal_plane_le hRp hVR hVn (hcyc hWc)
    refine ⟨U, hU, hUn, fun hUZ => hz1 ?_⟩
    have hzU : z ∈ U := hUZ ▸ hzZ
    have : z ∈ W ⊓ V := Subgroup.mem_inf.2 ⟨hzW, hUV hzU⟩
    rw [hWV, Subgroup.mem_bot] at this
    exact this
  · obtain ⟨U, hUW, hU, hUn⟩ := exists_normal_plane_le hRp hWR hWn hWc
    exact ⟨U, hU, hUn, fun hUZ => heW (hUW (hUZ ▸ heZ))⟩

end Step12

@[expose] def ReIMetaClaim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G},
    Cex117 G m p B M E A a K → Type117b p K →
    ∀ R : Subgroup G, IsSylowIn 5 M R → E ⊔ A ≤ R → IsSylowIn 5 ⊤ R →
      omegaOne 5 (centerOf R) = E ⊓ A → A = (E ⊓ A) ⊔ Subgroup.zpowers a → E ⊓ A = A ⊓ K →
      IsSylowIn 5 (Cg a) A → Cg a ≤ Subgroup.normalizer (K : Set G) →
      ∀ e ∈ E ⊓ A, e ≠ 1 → ¬ GLAPLayer 5 (K ⊓ Cg e) ≤ M →
        ∃ W V : Subgroup G, W ≤ R ∧ V ≤ R ∧ (W.subgroupOf R).Normal ∧ (V.subgroupOf R).Normal ∧
          e ∉ W ∧ IsCyclic ↥V ∧
          ∀ X : Subgroup G, W ⊔ V ≤ X → X ≤ R → (∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ W ⊔ V) →
            (∀ x ∈ X, x ^ 5 ∈ W ⊔ V) → Nat.card ↥X ≤ 5 * Nat.card ↥(W ⊔ V)

section Step4

variable {G : Type} [Group G] [Finite G]

theorem comm_of_isMetacyclic {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hQ : IsPGroup p Q) (hmeta : CFSG.IsMetacyclic Q) {x y : Q} (hx : x ^ p = 1) (hy : y ^ p = 1) :
    x * y = y * x := by
  by_cases hcyc : IsCyclic Q
  · exact IsCyclic.commGroup.mul_comm x y
  · haveI : Fact (IsPGroup p Q) := ⟨hQ⟩
    obtain ⟨-, hel⟩ := CFSG.lemma_4_10 hp2 hmeta hcyc
    have hxo : x ∈ CFSG.omega₁ (G := Q) (p := p) := Subgroup.subset_closure (by simpa using hx)
    have hyo : y ∈ CFSG.omega₁ (G := Q) (p := p) := Subgroup.subset_closure (by simpa using hy)
    exact congrArg Subtype.val (hel.toIsMulCommutative.is_comm.comm ⟨x, hxo⟩ ⟨y, hyo⟩)

theorem map_mem_of_mem_sup {H : Type*} [Group H] {R W : Subgroup G} (f : ↥R →* H) (S : Subgroup H)
    (hWR : W ≤ R) (hW : ∀ w (hw : w ∈ W), f ⟨w, hWR hw⟩ ∈ S) {g : G} (hgR : g ∈ R)
    (hg : f ⟨g, hgR⟩ ∈ S) {x : G} (hxR : x ∈ R) (hx : x ∈ W ⊔ Subgroup.zpowers g) :
    f ⟨x, hxR⟩ ∈ S := by
  have hle : W ⊔ Subgroup.zpowers g ≤ (S.comap f).map R.subtype := by
    refine sup_le ?_ ?_
    · intro w hw
      exact ⟨⟨w, hWR hw⟩, hW w hw, rfl⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨g, hgR⟩, hg, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hle hx
  have : y = ⟨x, hxR⟩ := Subtype.ext hyx
  rw [← this]
  exact hy

theorem commutator_omegaOne_le {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {R W C : Subgroup G}
    (hR : IsPGroup p ↥R) (hWC : W ≤ C) (hCR : C ≤ R) (hWn : (W.subgroupOf R).Normal)
    (hCn : (C.subgroupOf R).Normal) {c : G} (hcC : c ∈ C) (hC : C ≤ W ⊔ Subgroup.zpowers c)
    {r : G} (hrR : r ∈ R) (hRC : R ≤ C ⊔ Subgroup.zpowers r) :
    ⁅omegaOne p R, omegaOne p R⁆ ≤ W := by
  have hWR : W ≤ R := hWC.trans hCR
  set W' : Subgroup ↥R := W.subgroupOf R with hW'
  set φ : ↥R →* ↥R ⧸ W' := QuotientGroup.mk' W' with hφ
  have hφW : ∀ w (hw : w ∈ W), φ ⟨w, hWR hw⟩ = 1 := fun w hw =>
    (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hw)
  set CQ : Subgroup (↥R ⧸ W') := (C.subgroupOf R).map φ with hCQ
  haveI hCQn : CQ.Normal := Subgroup.Normal.map hCn φ (QuotientGroup.mk'_surjective W')
  have hmeta : CFSG.IsMetacyclic (↥R ⧸ W') := by
    refine ⟨CQ, hCQn, ?_, ?_⟩
    · have hle : CQ ≤ Subgroup.zpowers (φ ⟨c, hCR hcC⟩) := by
        rintro _ ⟨⟨x, hxR⟩, hxC, rfl⟩
        exact map_mem_of_mem_sup φ _ hWR (fun w hw => by rw [hφW w hw]; exact Subgroup.one_mem _)
          (hCR hcC) (Subgroup.mem_zpowers _) hxR (hC (Subgroup.mem_subgroupOf.1 hxC))
      exact Subgroup.isCyclic_of_le hle
    · set ψ : ↥R →* (↥R ⧸ W') ⧸ CQ := (QuotientGroup.mk' CQ).comp φ with hψ
      have hψs : Function.Surjective ψ :=
        (QuotientGroup.mk'_surjective CQ).comp (QuotientGroup.mk'_surjective W')
      have hψC : ∀ w (hw : w ∈ C), ψ ⟨w, hCR hw⟩ = 1 := by
        intro w hw
        rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact ⟨⟨w, hCR hw⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩
      refine isCyclic_iff_exists_zpowers_eq_top.2 ⟨ψ ⟨r, hrR⟩, eq_top_iff.2 fun q _ => ?_⟩
      obtain ⟨⟨x, hxR⟩, rfl⟩ := hψs q
      exact map_mem_of_mem_sup ψ _ hCR (fun w hw => by rw [hψC w hw]; exact Subgroup.one_mem _)
        hrR (Subgroup.mem_zpowers _) hxR (hRC hxR)
  have hQp : IsPGroup p (↥R ⧸ W') := hR.to_quotient W'
  set T : Set (↥R ⧸ W') := {q | q ^ p = 1} with hT
  have hTel : IsElemAbelian p (Subgroup.closure T) :=
    IsElemAbelian.closure_of_commute (fun a ha b hb => comm_of_isMetacyclic hp2 hQp hmeta ha hb)
      (fun a ha => ha)
  have hOR : omegaOne p R ≤ R := omegaOne_le' p R
  have hOle : omegaOne p R ≤ ((Subgroup.closure T).comap φ).map R.subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨hyR, hyp⟩
    refine ⟨⟨y, hyR⟩, Subgroup.subset_closure ?_, rfl⟩
    show (φ ⟨y, hyR⟩) ^ p = 1
    rw [← map_pow]
    have : (⟨y, hyR⟩ : ↥R) ^ p = 1 := Subtype.ext (by simpa using hyp)
    rw [this, map_one]
  set O' : Subgroup ↥R := (omegaOne p R).subgroupOf R with hO'
  have hO'map : O'.map φ ≤ Subgroup.closure T := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hOle (Subgroup.mem_subgroupOf.1 hx)
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hcomm' : ⁅O'.map φ, O'.map φ⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact elemAbelian_comm hTel (hO'map hb) (hO'map ha)
  have hker : ⁅O', O'⁆ ≤ W' := by
    have h1 : ⁅O', O'⁆.map φ = ⊥ := by rw [Subgroup.map_commutator, hcomm']
    intro x hx
    have hx1 : φ x = 1 := by
      have := Subgroup.mem_map_of_mem φ hx
      rw [h1, Subgroup.mem_bot] at this
      exact this
    exact (QuotientGroup.eq_one_iff x).1 hx1
  have hmap : ⁅O', O'⁆.map R.subtype = ⁅omegaOne p R, omegaOne p R⁆ := by
    rw [Subgroup.map_commutator, hO', Subgroup.subgroupOf_map_subtype, inf_of_le_left hOR]
  intro g hg
  rw [← hmap] at hg
  obtain ⟨y, hy, rfl⟩ := hg
  exact Subgroup.mem_subgroupOf.1 (hker hy)

theorem step4Claim_of_reIMeta (hMeta : ReIMetaClaim) : Claims1110.Step4Claim := by
  intro G _ _ m p B M E A a K h hb R hR hEAR hRG hZ hAeq hA2 hASyl hCaN e he he1 hKe
  obtain ⟨W, V, hWR, hVR, hWn, hVn, heW, hVc, hrank⟩ :=
    hMeta h hb R hR hEAR hRG hZ hAeq hA2 hASyl hCaN e he he1 hKe
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hCR : W ⊔ V ≤ R := sup_le hWR hVR
  have hCn : ((W ⊔ V).subgroupOf R).Normal := by
    rw [Subgroup.subgroupOf_sup hWR hVR]
    infer_instance
  obtain ⟨c, hc⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top V).1 hVc
  have hcC : c ∈ W ⊔ V := Subgroup.mem_sup_right (hc ▸ Subgroup.mem_zpowers c)
  have hC : W ⊔ V ≤ W ⊔ Subgroup.zpowers c := by rw [hc]
  obtain ⟨r, hrR, hRC⟩ := exists_sup_zpowers_of_rank_le_one (by norm_num) hR.2.1 hCR hCn hrank
  exact fun heO => heW
    (commutator_omegaOne_le (by norm_num) hR.2.1 le_sup_left hCR hWn hCn hcC hC hrR hRC heO)

end Step4

section Cover

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns (conj_mem_gLAPPrimeCoreOf gLAPPrimeCoreOf_le)

@[expose] def IeOf (K : Subgroup G) (e : G) : Subgroup G :=
  ⨆ g ∈ GLAPLayer 5 (Cg e), GLBConj g (GLAPLayer 5 (K ⊓ Cg e))

theorem glaPLayer_le'' (p : ℕ) (X : Subgroup G) : GLAPLayer p X ≤ X :=
  sSup_le fun _ h => h.1

theorem ke_le_ieOf (K : Subgroup G) (e : G) : GLAPLayer 5 (K ⊓ Cg e) ≤ IeOf K e := by
  intro x hx
  have h1 : x ∈ GLBConj 1 (GLAPLayer 5 (K ⊓ Cg e)) := by
    rw [mem_gLBConj]
    simpa using hx
  exact (le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 5 (Cg e)) => GLBConj g (GLAPLayer 5 (K ⊓ Cg e)))
    1 (Subgroup.one_mem _)) h1

theorem ieOf_le_cg (K : Subgroup G) (e : G) : IeOf K e ≤ Cg e := by
  refine iSup₂_le fun g hg => ?_
  intro x hx
  rw [mem_gLBConj] at hx
  have hgC : g ∈ Cg e := glaPLayer_le'' 5 _ hg
  have hxC : g * x * g⁻¹ ∈ Cg e := (glaPLayer_le'' 5 _).trans inf_le_right hx
  have := (Cg e).mul_mem ((Cg e).mul_mem ((Cg e).inv_mem hgC) hxC) hgC
  simpa [mul_assoc] using this

@[expose] def CRIe (R K : Subgroup G) (e : G) : Subgroup G where
  carrier := {x | x ∈ R ∧ x ∈ Cg e ∧ ∀ y ∈ IeOf K e, x * y * x⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf 5 (Cg e)}
  mul_mem' := by
    rintro x x' ⟨hxR, hxC, hx⟩ ⟨hx'R, hx'C, hx'⟩
    refine ⟨R.mul_mem hxR hx'R, (Cg e).mul_mem hxC hx'C, fun y hy => ?_⟩
    have h1 := conj_mem_gLAPPrimeCoreOf 5 (Cg e) hxC (hx' y hy)
    have hm := (GLAPPrimeCoreOf 5 (Cg e)).mul_mem h1 (hx y hy)
    have e' : x * x' * y * (x * x')⁻¹ * y⁻¹ =
        x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by group
    rw [e']
    exact hm
  one_mem' := ⟨R.one_mem, (Cg e).one_mem, fun y _ => by simp⟩
  inv_mem' := by
    rintro x ⟨hxR, hxC, hx⟩
    refine ⟨R.inv_mem hxR, (Cg e).inv_mem hxC, fun y hy => ?_⟩
    have h1 := conj_mem_gLAPPrimeCoreOf 5 (Cg e) ((Cg e).inv_mem hxC)
      ((GLAPPrimeCoreOf 5 (Cg e)).inv_mem (hx y hy))
    have e' : x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ = x⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e']
    exact h1

theorem mem_cRIe {R K : Subgroup G} {e x : G} :
    x ∈ CRIe R K e ↔ x ∈ R ∧ x ∈ Cg e ∧
      ∀ y ∈ IeOf K e, x * y * x⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf 5 (Cg e) := Iff.rfl

theorem cRIe_le (R K : Subgroup G) (e : G) : CRIe R K e ≤ R := fun _ hx => hx.1

@[expose] def IeLayerClaim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G},
    Cex117 G m p B M E A a K → Type117b p K →
    ∀ R : Subgroup G, IsSylowIn 5 M R → E ⊔ A ≤ R →
    ∀ e ∈ omegaOne 5 (centerOf R), e ≠ 1 →
      ∃ 𝓛 : Set (Subgroup G), (∀ L ∈ 𝓛, GLAPComponent 5 (Cg e) L) ∧ IeOf K e = sSup 𝓛

theorem mem_normalizer_sSup {X : Set (Subgroup G)} {b : G}
    (hb : ∀ L ∈ X, b ∈ Subgroup.normalizer (L : Set G)) :
    b ∈ Subgroup.normalizer ((sSup X : Subgroup G) : Set G) := by
  have hle : ∀ b' : G, (∀ L ∈ X, b' ∈ Subgroup.normalizer (L : Set G)) →
      ∀ x ∈ sSup X, b' * x * b'⁻¹ ∈ sSup X := by
    intro b' hb' x hx
    have h1 : sSup X ≤ ((sSup X).comap (MulAut.conj b').toMonoidHom) := by
      refine sSup_le fun L hL => ?_
      intro y hy
      exact le_sSup hL ((Subgroup.mem_normalizer_iff.1 (hb' L hL) y).1 hy)
    exact h1 hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hle b hb x
  · intro hx
    have := hle b⁻¹ (fun L hL => Subgroup.inv_mem _ (hb L hL)) _ hx
    simpa [mul_assoc] using this

theorem exists_fixed_mul {p : ℕ} [Fact p.Prime] {X V O : Subgroup G} (hV : IsPGroup p ↥V)
    (hVX : V ≤ X) (hOX : X ≤ Subgroup.normalizer (O : Set G)) (hO : Nat.Coprime p (Nat.card ↥O))
    {z : G} (hzX : z ∈ X) (hz : ∀ v ∈ V, v * z * v⁻¹ * z⁻¹ ∈ O) :
    ∃ c ∈ Subgroup.centralizer (V : Set G), ∃ o ∈ O, z = c * o := by
  classical
  set S : Set G := {s | z⁻¹ * s ∈ O} with hSdef
  have hVS : ∀ v ∈ V, ∀ s ∈ S, v * s * v⁻¹ ∈ S := by
    intro v hv s hs
    have h1 : z⁻¹ * (v * z * v⁻¹ * z⁻¹) * z ∈ O := by
      have := (Subgroup.mem_normalizer_iff.1 (hOX ((X.inv_mem hzX))) _).1 (hz v hv)
      simpa [mul_assoc] using this
    have h2 : v * (z⁻¹ * s) * v⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hOX (hVX hv)) _).1 hs
    have h3 := O.mul_mem h1 h2
    show z⁻¹ * (v * s * v⁻¹) ∈ O
    have e' : z⁻¹ * (v * s * v⁻¹) = z⁻¹ * (v * z * v⁻¹ * z⁻¹) * z * (v * (z⁻¹ * s) * v⁻¹) := by group
    rw [e']
    exact h3
  letI := Claims1110.conjActSet V S hVS
  have hcard : Nat.card ↥S = Nat.card ↥O := by
    refine Nat.card_congr
      { toFun := fun s => ⟨z⁻¹ * s, s.2⟩
        invFun := fun o => ⟨z * o, by show z⁻¹ * (z * o) ∈ O; simpa using o.2⟩
        left_inv := fun s => by apply Subtype.ext; simp
        right_inv := fun o => by apply Subtype.ext; simp }
  have hmod := hV.card_modEq_card_fixedPoints ↥S
  have hne : (MulAction.fixedPoints ↥V ↥S).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h0 : Nat.card ↥(MulAction.fixedPoints ↥V ↥S) = 0 := by
      rw [hemp]
      simp
    rw [h0, hcard] at hmod
    have hdvd : p ∣ Nat.card ↥O := (Nat.modEq_zero_iff_dvd).1 hmod
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).1 hO hdvd
  obtain ⟨⟨s, hsS⟩, hsfix⟩ := hne
  refine ⟨s, ?_, (z⁻¹ * s)⁻¹, O.inv_mem hsS, by group⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 : v * s * v⁻¹ = s := congrArg Subtype.val (hsfix ⟨v, hv⟩)
  calc v * s = (v * s * v⁻¹) * v := by group
    _ = s * v := by rw [h1]

theorem ieOf_le_M_of_not_isCyclic (h119 : Lemma119Statement) (h111 : Prop111Statement)
    (h112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2) (hLay : IeLayerClaim)
    {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m 5 B M E A a K)
    (hb : Type117b 5 K) {R : Subgroup G} (hR : IsSylowIn 5 M R) (hEAR : E ⊔ A ≤ R) {e : G}
    (heZ : e ∈ omegaOne 5 (centerOf R)) (he1 : e ≠ 1) (hnc : ¬ IsCyclic ↥(CRIe R K e)) :
    IeOf K e ≤ M := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hsc := lemma104_ii_holds hS h.pair
  obtain ⟨hrk, -, -, -⟩ := h119 h
  have hZle : omegaOne 5 (centerOf R) ≤ E ⊓ A :=
    le_inf (l1110_omegaOne_centerOf_le hsc.1 (le_sup_left.trans hEAR))
      (l1110_omegaOne_centerOf_le hsc.2 (le_sup_right.trans hEAR))
  have heA : e ∈ A := (Subgroup.mem_inf.1 (hZle heZ)).2
  have hRC : R ≤ Cg e := fun r hr => Subgroup.mem_centralizer_singleton_iff.2
    (comm_of_mem_centerOf (omegaOne_le' 5 _ heZ) hr)
  set O := GLAPPrimeCoreOf 5 (Cg e) with hO
  have hOM : O ≤ M := h111 h.toCex117Base.toSec11 heA he1
  have hOcop : Nat.Coprime 5 (Nat.card ↥O) := by
    have h1 : Nat.card ↥O = Nat.card ↥(GLAPPrimeCore 5 ↥(Cg e)) :=
      Subgroup.card_map_of_injective (Cg e).subtype_injective
    rw [h1]
    exact CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 5 ↥(Cg e)
  have hCeO : Cg e ≤ Subgroup.normalizer (O : Set G) := fun x hx =>
    Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => conj_mem_gLAPPrimeCoreOf 5 (Cg e) hx hy,
      fun hy => by
        have := conj_mem_gLAPPrimeCoreOf 5 (Cg e) ((Cg e).inv_mem hx) hy
        simpa [mul_assoc] using this⟩
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS.standing hS.bOne hS.pre
  have hBel : IsElemAbelian 5 B := hS.bOne.1.1
  obtain ⟨y, hyM, T, hTp, hTM, hRT, hBT⟩ :=
    exists_conj_le_pGroup' hR.1 hR.2.1 hBM (isPGroup_of_elemAb hBel)
  have hTR : T = R := hR.2.2 T hTM hTp hRT
  rw [hTR] at hBT
  set B₁ := GLBConj y B with hB₁
  have hB₁D : inD 5 M B₁ := (lemma101_i_holds hS hyM (lemma101_ii_holds hS) h.pair.1.2.1).1
  have hB₁el : IsElemAbelian 5 B₁ := isElemAbelian_conj y hBel
  have hB₁c : Nat.card ↥B₁ = 5 ^ m := by rw [hB₁, card_conj, hS.standing.card_eq hS.bOne]
  have hm4 : 4 ≤ m := hS.standing.four_le
  have hB₁C : B₁ ≤ Cg e := hBT.trans hRC
  have hB₁rk : CFSG.Open.pRank 5 B₁ = m := by
    have h1 := l1110_card_eq_pow_pRank hB₁el
    rw [hB₁c] at h1
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 5) h1).symm
  have hB₁rank : GLATwoLocalRank 5 ↥(Cg e) ≤ CFSG.Open.pRank 5 B₁ := by
    rw [hB₁rk]
    exact (CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le hp _).trans
      hS.standing.rank_eq.le
  obtain ⟨𝓛, h𝓛, hIe⟩ := hLay h hb R hR hEAR e heZ he1
  have hB₁N : B₁ ≤ Subgroup.normalizer ((IeOf K e : Subgroup G) : Set G) := by
    intro b hbB
    rw [hIe]
    refine mem_normalizer_sSup fun L hL => ?_
    by_contra hn
    have := (h112 G m 5 hS.standing (Cg e) B₁ L hB₁el hB₁C hB₁rank (h𝓛 L hL)
      (fun hle => hn (hle hbB))).1
    norm_num at this
  have hB₁NC : B₁ ≤ Subgroup.normalizer ((CRIe R K e : Subgroup G) : Set G) := by
    have key : ∀ b ∈ B₁, ∀ x ∈ CRIe R K e, b * x * b⁻¹ ∈ CRIe R K e := by
      intro b hbB x hx
      obtain ⟨hxR, hxC, hxI⟩ := (mem_cRIe).1 hx
      have hbR : b ∈ R := hBT hbB
      have hbC : b ∈ Cg e := hB₁C hbB
      refine (mem_cRIe).2 ⟨R.mul_mem (R.mul_mem hbR hxR) (R.inv_mem hbR),
        (Cg e).mul_mem ((Cg e).mul_mem hbC hxC) ((Cg e).inv_mem hbC), fun z hz => ?_⟩
      have hz' : b⁻¹ * z * b ∈ IeOf K e := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hB₁N hbB)) z).1 hz
        simpa using this
      have h1 := conj_mem_gLAPPrimeCoreOf 5 (Cg e) hbC (hxI _ hz')
      have e' : b * x * b⁻¹ * z * (b * x * b⁻¹)⁻¹ * z⁻¹ =
          b * (x * (b⁻¹ * z * b) * x⁻¹ * (b⁻¹ * z * b)⁻¹) * b⁻¹ := by group
      rw [e']
      exact h1
    intro b hbB
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact key b hbB x
    · intro hx
      have := key b⁻¹ (B₁.inv_mem hbB) _ hx
      simpa [mul_assoc] using this
  set R' : Subgroup G := CRIe R K e ⊔ B₁ with hR'
  have hR'R : R' ≤ R := sup_le (cRIe_le R K e) hBT
  have hR'p : IsPGroup 5 ↥R' := hR.2.1.to_le hR'R
  have hCn : ((CRIe R K e).subgroupOf R').Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le (Subgroup.le_normalizer) hB₁NC
  obtain ⟨V, hVC, hVp, hR'V⟩ := Claims1111b.input31_5_holds G 5 hp (by norm_num) R' (CRIe R K e)
    hR'p le_sup_left hCn hnc
  have hB₁V : B₁ ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hR'V
  have hlines := card_le_mul_inf_centralizer (isPGroup_of_elemAb hB₁el) hVp.2 hB₁V
  set Cb := B₁ ⊓ Subgroup.centralizer (V : Set G) with hCb
  have hCb3 : 5 ^ 3 ≤ Nat.card ↥Cb := by
    rw [hB₁c] at hlines
    have h5 : 5 ^ 4 ≤ 5 ^ m := Nat.pow_le_pow_right (by norm_num) hm4
    have : 5 * 5 ^ 3 ≤ 5 * Nat.card ↥Cb := by
      calc 5 * 5 ^ 3 = 5 ^ 4 := by norm_num
        _ ≤ 5 ^ m := h5
        _ ≤ 5 * Nat.card ↥Cb := hlines
    omega
  have hCbel : IsElemAbelian 5 Cb := l1110_isElemAbelian_of_le hB₁el inf_le_left
  have hVCb : V ≤ Subgroup.centralizer (Cb : Set G) := Subgroup.le_centralizer_iff.1 inf_le_right
  have hVCel : IsElemAbelian 5 (V ⊔ Cb) := isElemAbelian_sup_of_commute hVp.1 hCbel hVCb
  obtain ⟨A₁, hA₁sc, hA₁⟩ := exists_isSCp_top_above' hVCel
  obtain ⟨U₃, hU₃, hU₃Cb⟩ := exists_isEkIn_le (X := ⊤) le_top hCbel hCb3
  have hU₃A₁ : U₃ ≤ A₁ := hU₃Cb.trans (le_sup_right.trans hA₁)
  have hU₃B₁ : U₃ ≤ B₁ := hU₃Cb.trans inf_le_left
  have hconn : IsKConnectedIn 5 (CFSG.Open.pRank 5 (E ⊓ A) + 1) ⊤ A₁ B₁ := by
    rw [hrk]
    refine ⟨le_top, hA₁sc.2.1, ?_, le_top, hB₁el, ?_, Or.inr ⟨U₃, U₃, hU₃, hU₃,
      le_centralizer_of_le hA₁sc.2.1 le_rfl hU₃A₁, Relation.ReflTransGen.refl,
      le_centralizer_of_le hB₁el hU₃B₁ le_rfl⟩⟩
    · calc 5 ^ 3 = Nat.card ↥U₃ := hU₃.2.2.symm
        _ ≤ Nat.card ↥A₁ := Subgroup.card_le_of_le hU₃A₁
    · rw [hB₁c]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA₁D : inD 5 M A₁ := lemma104_iii_holds hS h.pair hA₁sc hB₁D hconn
  have hVrk : 2 ≤ CFSG.Open.pRank 5 V := by
    have h1 : CFSG.Open.pRank 5 V = 2 := Nat.pow_right_injective (by norm_num : 2 ≤ 5)
      ((l1110_card_eq_pow_pRank hVp.1).symm.trans hVp.2)
    omega
  have hVM : Subgroup.normalizer (V : Set G) ≤ M :=
    (l1110_normalizer_le_glbCore (le_sup_left.trans hA₁) hVrk).trans hA₁D.2.clause_d
  intro z hz
  have hzC : z ∈ Cg e := ieOf_le_cg K e hz
  have hVR : V ≤ R := hVC.trans (cRIe_le R K e)
  obtain ⟨c, hc, o, ho, rfl⟩ := exists_fixed_mul (hR.2.1.to_le hVR) (hVR.trans hRC) hCeO hOcop hzC
    (fun v hv => ((mem_cRIe).1 (hVC hv)).2.2 z hz)
  exact M.mul_mem (hVM (Subgroup.centralizer_le_normalizer _ hc)) (hOM ho)

end Cover

section Step5

@[expose] def gammaK0 {X : Type*} [Group X] (P : Subgroup X) : Subgroup X :=
  Subgroup.normalizer (P : Set X) ⊔
    ⨆ (x : X) (_ : x ∈ P) (_ : x ≠ 1), GLAPLayer 5 (Subgroup.centralizer ({x} : Set X))

@[expose] def Input24_2K0 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsFiTwentyTwo X → ∀ P : Subgroup X, IsPGroup 5 ↥P →
    Nat.card ↥P = 5 ^ 2 → ∀ Y : Subgroup X, gammaK0 P ≤ Y → Y = gammaK0 P ∨ Y = ⊤

@[expose] def Step6Claim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G},
    Cex117 G m p B M E A a K → Type117b p K →
    ∀ R : Subgroup G, IsSylowIn 5 M R → E ⊔ A ≤ R → IsSylowIn 5 ⊤ R →
      omegaOne 5 (centerOf R) = E ⊓ A → A = (E ⊓ A) ⊔ Subgroup.zpowers a → E ⊓ A = A ⊓ K →
      IsSylowIn 5 (Cg a) A → Cg a ≤ Subgroup.normalizer (K : Set G) →
      Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M →
      (∀ e ∈ E ⊓ A, e ≠ 1 → GLAPLayer 5 (K ⊓ Cg e) ≤ M) → GLAPPrimeCoreOf 5 K ≤ M →
      ((K ⊓ M).subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore 5 ↥K)) =
        gammaK0 (((E ⊓ A).subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore 5 ↥K))) → False

variable {G : Type} [Group G] [Finite G]

theorem step5 (h119 : Lemma119Statement) (h111 : Prop111Statement) (hK0 : Input24_2K0)
    {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m 5 B M E A a K)
    (hfi : IsSporType .Fi22 (barOf 5 K)) (hA2 : E ⊓ A = A ⊓ K)
    (hN0 : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M)
    (hKe : ∀ e ∈ E ⊓ A, e ≠ 1 → GLAPLayer 5 (K ⊓ Cg e) ≤ M) :
    GLAPPrimeCoreOf 5 K ≤ M ∧
      ((K ⊓ M).subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore 5 ↥K)) =
        gammaK0 (((E ⊓ A).subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore 5 ↥K))) := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hsc := lemma104_ii_holds hS h.pair
  obtain ⟨hrk, -, -, -⟩ := h119 h
  have hA0el : IsElemAbelian 5 (E ⊓ A) := l1110_isElemAbelian_of_le hsc.1.2.1 inf_le_left
  have hA0c : Nat.card ↥(E ⊓ A) = 5 ^ 2 := by rw [l1110_card_eq_pow_pRank hA0el, hrk]
  have hA0K : E ⊓ A ≤ K := by rw [hA2]; exact inf_le_right
  have hOK : GLAPPrimeCoreOf 5 K ≤ M :=
    (CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal 5 h.hK.2.1).trans
      (h111 h.toCex117Base.toSec11 h.ha.1 h.ha.2)
  refine ⟨hOK, ?_⟩
  set O' : Subgroup ↥K := GLAPPrimeCore 5 ↥K with hO'
  set π : ↥K →* ↥K ⧸ O' := QuotientGroup.mk' O' with hπ
  set A₀' : Subgroup ↥K := (E ⊓ A).subgroupOf K with hA₀'
  set Y : Subgroup (↥K ⧸ O') := ((K ⊓ M).subgroupOf K).map π with hY
  have hOcop : Nat.Coprime 5 (Nat.card ↥O') :=
    CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 5 ↥K
  have hA₀'c : Nat.card ↥A₀' = 5 ^ 2 := by
    rw [hA₀', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA0K).toEquiv, hA0c]
  have hA₀'p : IsPGroup 5 ↥A₀' := IsPGroup.of_card hA₀'c
  have hA0O : ∀ x : ↥K, x ∈ A₀' → x ∈ O' → x = 1 := by
    intro x hxA hxO
    have hx5 : x ^ 5 = 1 :=
      Subtype.ext (by simpa using hA0el.2 _ (Subgroup.mem_subgroupOf.1 hxA))
    exact eq_one_of_dvd_coprime hOcop (orderOf_dvd_of_pow_eq_one hx5)
      (Subgroup.orderOf_dvd_natCard _ hxO)
  have hA0bc : Nat.card ↥(A₀'.map π) = 5 ^ 2 := by
    have hinj : Function.Injective (π.comp A₀'.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      exact Subgroup.mem_bot.2 (Subtype.ext (hA0O _ x.2 hx))
    have h1 : (π.comp A₀'.subtype).range = A₀'.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hA₀'c]
  have hA0bp : IsPGroup 5 ↥(A₀'.map π) := hA₀'p.map π
  have hN : Subgroup.normalizer ((A₀'.map π : Subgroup (↥K ⧸ O')) : Set (↥K ⧸ O')) ≤ Y := by
    intro nb hnb
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective O' nb
    set H : Subgroup ↥K := (A₀'.map π).comap π with hH
    have hA0H : A₀' ≤ H := fun x hx => ⟨x, hx, rfl⟩
    have hnH : GLBConj n⁻¹ A₀' ≤ H := by
      intro y hy
      rw [mem_gLBConj, inv_inv] at hy
      have h1 : π (n⁻¹ * y * n) ∈ A₀'.map π := ⟨_, hy, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.1 hnb _).1 h1
      show π y ∈ A₀'.map π
      have e' : π y = π n * π (n⁻¹ * y * n) * (π n)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
        group
      rw [e']
      exact h2
    have hHcard : Nat.card ↥H = Nat.card ↥O' * Nat.card ↥(A₀'.map π) :=
      QuotientGroup.card_preimage_mk O' ((A₀'.map π : Subgroup (↥K ⧸ O')) : Set (↥K ⧸ O'))
    have hHc : (Nat.card ↥H).factorization 5 = 2 := by
      rw [hHcard, hA0bc, Nat.factorization_mul Nat.card_pos.ne' (by norm_num), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).1 hOcop),
        Nat.Prime.factorization_pow hp]
      simp
    have hc1 : Nat.card ↥A₀' = 5 ^ (Nat.card ↥H).factorization 5 := by rw [hHc, hA₀'c]
    have hc2 : Nat.card ↥(GLBConj n⁻¹ A₀') = 5 ^ (Nat.card ↥H).factorization 5 := by
      rw [card_conj, hc1]
    obtain ⟨x, hxH, hx⟩ :=
      exists_conj_eq_of_card hA0H hnH hA₀'p (isPGroup_conj n⁻¹ hA₀'p) hc1 hc2
    rw [gLBConj_gLBConj] at hx
    have hnx : n⁻¹ * x ∈ Subgroup.normalizer (A₀' : Set ↥K) := mem_normalizer_iff_gLBConj_eq.2 hx
    obtain ⟨a', ha', hax⟩ := hxH
    set c : ↥K := a' * (n⁻¹ * x)⁻¹ with hc
    have hcN : c ∈ Subgroup.normalizer (A₀' : Set ↥K) :=
      Subgroup.mul_mem _ (Subgroup.le_normalizer ha') (Subgroup.inv_mem _ hnx)
    have hπc : π c = π n := by
      rw [hc, map_mul, map_inv, map_mul, map_inv, hax]
      group
    have hcG : (c : G) ∈ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) :=
      mem_normalizer_of_subgroupOf' hA0K hcN
    exact ⟨c, Subgroup.mem_subgroupOf.2 ⟨c.2, hN0 hcG⟩, hπc⟩
  have hL : ∀ xb ∈ A₀'.map π, xb ≠ 1 →
      GLAPLayer 5 (Subgroup.centralizer ({xb} : Set (↥K ⧸ O'))) ≤ Y := by
    rintro _ ⟨e', he'A, rfl⟩ he1
    have heA : (e' : G) ∈ E ⊓ A := Subgroup.mem_subgroupOf.1 he'A
    have he'1 : e' ≠ 1 := fun h1 => he1 (by rw [h1, map_one])
    have he1' : (e' : G) ≠ 1 := fun h1 => he'1 (Subtype.ext h1)
    have he'5 : e' ^ 5 = 1 := Subtype.ext (by simpa using hA0el.2 _ heA)
    have he'o : orderOf e' = 5 := orderOf_eq_of_pow he'5 he'1
    have he'p : IsPGroup 5 ↥(Subgroup.zpowers e') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, he'o, pow_one])
    set C : Subgroup ↥K := Subgroup.centralizer ({e'} : Set ↥K) with hC
    have hCmap : C.map π = Subgroup.centralizer ({π e'} : Set (↥K ⧸ O')) := by
      apply le_antisymm
      · rintro _ ⟨c, hc, rfl⟩
        have hc' : c * e' = e' * c := Subgroup.mem_centralizer_singleton_iff.1 hc
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hc']
      · intro yb hyb
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O' yb
        have hyb' : π e' * π y = π y * π e' :=
          (Subgroup.mem_centralizer_singleton_iff.1 hyb).symm
        have hcomm : ∀ v ∈ Subgroup.zpowers e', v * y * v⁻¹ * y⁻¹ ∈ O' := by
          intro v hv
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
          have h1 : π (e' ^ j) * π y = π y * π (e' ^ j) := by
            rw [map_zpow]
            exact ((Commute.zpow_left (show Commute (π e') (π y) from hyb') j)).eq
          have h2 : π (e' ^ j * y * (e' ^ j)⁻¹ * y⁻¹) = 1 := by
            rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
            group
          exact (QuotientGroup.eq_one_iff _).1 h2
        have hOX : (⊤ : Subgroup ↥K) ≤ Subgroup.normalizer (O' : Set ↥K) :=
          (Subgroup.normalizer_eq_top_iff.2 inferInstance).ge
        obtain ⟨c, hc, o, ho, hyco⟩ := exists_fixed_mul he'p le_top hOX hOcop (Subgroup.mem_top y) hcomm
        refine ⟨c, ?_, ?_⟩
        · exact Subgroup.mem_centralizer_singleton_iff.2
            ((Subgroup.mem_centralizer_iff.1 hc e' (Subgroup.mem_zpowers e')).symm)
        · rw [hyco, map_mul, show π o = 1 from (QuotientGroup.eq_one_iff o).2 ho, mul_one]
    have hker1 : Nat.Coprime 5 (Nat.card ↥(C ⊓ π.ker)) := by
      refine Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) ?_
      rw [hπ, QuotientGroup.ker_mk']
      exact hOcop
    have h1 := CFSG.HardMathSupport.Solomon.Coordinator.i227m_glaPLayer_map hp π hker1
    have hker2 : Nat.Coprime 5 (Nat.card ↥(C ⊓ (K.subtype).ker)) := by
      rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
      exact Nat.coprime_one_right 5
    have h2 := CFSG.HardMathSupport.Solomon.Coordinator.i227m_glaPLayer_map hp K.subtype hker2
    have hCK : C.map K.subtype = K ⊓ Cg (e' : G) := by
      apply le_antisymm
      · rintro _ ⟨c, hc, rfl⟩
        refine Subgroup.mem_inf.2 ⟨c.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hc)
      · intro x hx
        obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.1 hx
        refine ⟨⟨x, hxK⟩, Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_), rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.1 hxC
    rw [hCK] at h2
    have hKeM := hKe _ heA he1'
    rw [← hCmap, h1]
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z, Subgroup.mem_subgroupOf.2 ⟨z.2, ?_⟩, rfl⟩
    exact hKeM (h2 ▸ ⟨z, hz, rfl⟩)
  have hle : gammaK0 (A₀'.map π) ≤ Y :=
    sup_le hN (iSup_le fun x => iSup_le fun hx => iSup_le fun hx1 => hL x hx hx1)
  rcases hK0 (↥K ⧸ O') hfi (A₀'.map π) hA0bp hA0bc Y hle with hY | hY
  · exact hY
  · exfalso
    apply h.notM
    intro k hk
    have hmem : π ⟨k, hk⟩ ∈ Y := hY ▸ Subgroup.mem_top _
    obtain ⟨c, hcKM, hcπ⟩ := hmem
    have h1 : c⁻¹ * ⟨k, hk⟩ ∈ O' := QuotientGroup.eq.1 hcπ
    have h2 : (c : G)⁻¹ * k ∈ GLAPPrimeCoreOf 5 K := ⟨_, h1, rfl⟩
    have hcM : (c : G) ∈ M := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hcKM)).2
    have : k = (c : G) * ((c : G)⁻¹ * k) := by group
    rw [this]
    exact M.mul_mem hcM (hOK h2)

theorem step56Claim_of_step6 (h119 : Lemma119Statement) (h111 : Prop111Statement)
    (hK0 : Input24_2K0) (h6 : Step6Claim) : Claims1110.Step56Claim := by
  intro G _ _ m p B M E A a K h hb R hR hEAR hRG hZ hAeq hA2 hASyl hCaN hN0 hKe
  obtain ⟨rfl, hfi⟩ := hb
  obtain ⟨hOK, hY⟩ := step5 h119 h111 hK0 h hfi hA2 hN0 hKe
  exact h6 h ⟨rfl, hfi⟩ R hR hEAR hRG hZ hAeq hA2 hASyl hCaN hN0 hKe hOK hY

end Step5

section Fi22Class

open CFSG.RankThree.Native CFSG.Monster.B.Fischer

theorem conj_mem_commutator_self {X : Type*} [Group X] {C : Subgroup X} {g : X} (hg : g ∈ C) {y : X}
    (hy : y ∈ ⁅C, C⁆) : g * y * g⁻¹ ∈ ⁅C, C⁆ := by
  have hle : C.map (MulAut.conj g).toMonoidHom ≤ C := by
    rintro _ ⟨c, hc, rfl⟩
    exact C.mul_mem (C.mul_mem hg hc) (C.inv_mem hg)
  have h1 : ⁅C, C⁆.map (MulAut.conj g).toMonoidHom ≤ ⁅C, C⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hle hle
  exact h1 ⟨y, hy, rfl⟩

theorem fi22_le_normalizer_D :
    fi22FiveC 0 ≤ Subgroup.normalizer (fi22FiveD 0 : Set (Equiv.Perm (Fin 3510))) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact conj_mem_commutator_self hh
  · intro hx
    have := conj_mem_commutator_self ((fi22FiveC 0).inv_mem hh) hx
    have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
    rw [e] at this
    exact this

theorem fi22_mem_zpowers_of_comm_D
    {g : Equiv.Perm (Fin 3510)} (hgC : g ∈ fi22FiveC 0)
    (hgP : g ∈ fi22P) (hg : ∀ d ∈ fi22FiveD 0, g * d = d * g) :
    g ∈ Subgroup.zpowers (fi22FiveLine 0) := by
  have hmem : g ∈ Subgroup.centralizer (fi22FiveD 0 : Set (Equiv.Perm (Fin 3510))) ⊓ fi22FiveC 0 :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 (fun d hd => (hg d hd).symm), hgC⟩
  obtain ⟨e, -, f, hf, rfl⟩ := (mem_centralizer_fi22FiveD_iff 0 g).1 hmem
  interval_cases f
  · simpa using Subgroup.npow_mem_zpowers (fi22FiveLine 0) e
  · exfalso
    apply fi22FiveW_not_mem_P
    have h1 : (fi22FiveLine 0 ^ e)⁻¹ * (fi22FiveLine 0 ^ e * fi22FiveW ^ 1) ∈ fi22P :=
      fi22P.mul_mem (fi22P.inv_mem (fi22P.pow_mem (fi22FiveLine_mem_P 0) e)) hgP
    simpa using h1

theorem fi22_exists_conj_sq :
    ∃ t ∈ fi22P, t * fi22FiveLine 0 * t⁻¹ = fi22FiveLine 0 ^ 2 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set D := fi22FiveD 0 with hD
  set H : Subgroup (Equiv.Perm (Fin 3510)) := fi22FiveC 0 ⊓ fi22P with hH
  haveI : IsSimpleGroup ↥D := fi22FiveD_isSimpleGroup 0
  obtain ⟨ψ⟩ := CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (card_fi22FiveD 0)
  have hHN : H ≤ Subgroup.normalizer (D : Set (Equiv.Perm (Fin 3510))) :=
    inf_le_left.trans fi22_le_normalizer_D
  set Φ : ↥H →* MulAut ↥D := D.normalizerMonoidHom.comp (Subgroup.inclusion hHN) with hΦ
  have hΦapp : ∀ (h : ↥H) (d : ↥D), ((Φ h d : ↥D) : Equiv.Perm (Fin 3510)) =
      (h : Equiv.Perm (Fin 3510)) * d * (h : Equiv.Perm (Fin 3510))⁻¹ := fun h d => rfl
  have hkerz : ∀ k : ↥H, Φ k = 1 → (k : Equiv.Perm (Fin 3510)) ∈ Subgroup.zpowers (fi22FiveLine 0) := by
    intro k hk
    refine fi22_mem_zpowers_of_comm_D (Subgroup.mem_inf.1 k.2).1 (Subgroup.mem_inf.1 k.2).2 ?_
    intro d hd
    have h1 := congrArg (fun φ : MulAut ↥D => ((φ ⟨d, hd⟩ : ↥D) : Equiv.Perm (Fin 3510))) hk
    simp only [MulAut.one_apply] at h1
    rw [hΦapp] at h1
    calc (k : Equiv.Perm (Fin 3510)) * d = ((k : Equiv.Perm (Fin 3510)) * d * (k : Equiv.Perm (Fin 3510))⁻¹) *
          (k : Equiv.Perm (Fin 3510)) := by group
      _ = d * k := by rw [h1]
  have hker : Nat.card ↥Φ.ker ≤ 5 := by
    have h1 : Nat.card ↥Φ.ker ≤ Nat.card ↥(Subgroup.zpowers (fi22FiveLine 0)) := by
      refine Nat.card_le_card_of_injective
        (fun k => ⟨((k : ↥H) : Equiv.Perm (Fin 3510)), hkerz k k.2⟩) ?_
      intro k₁ k₂ h
      have h' : ((k₁ : ↥H) : Equiv.Perm (Fin 3510)) = ((k₂ : ↥H) : Equiv.Perm (Fin 3510)) :=
        congrArg (fun z : ↥(Subgroup.zpowers (fi22FiveLine 0)) => (z : Equiv.Perm (Fin 3510))) h
      exact Subtype.ext (Subtype.ext h')
    rwa [Nat.card_zpowers, orderOf_fi22FiveLine] at h1
  have hcardH : Nat.card ↥H = 600 := card_fi22FiveC_inf_P 0
  have hcardAut : Nat.card (MulAut ↥D) = 120 := by
    rw [CFSG.LargeExtraspecial.S12Tri.card_mulAut_congr ψ]
    exact CFSG.GH74.GLS.LU.Local.Five.nat_card_mulAut_alternatingGroup_five
  have hrange : Φ.range = ⊤ := by
    have h1 : Nat.card ↥Φ.ker * Nat.card ↥Φ.range = 600 := by
      rw [← hcardH, ← Subgroup.index_ker Φ]
      exact Subgroup.card_mul_index _
    have h2 : Nat.card ↥Φ.range ≤ 120 := hcardAut ▸ Subgroup.card_le_card_group _
    have h3 : 0 < Nat.card ↥Φ.ker := Nat.card_pos
    apply Subgroup.eq_top_of_card_eq
    rw [hcardAut]
    nlinarith
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 5 (by rw [card_fi22FiveD 0]; norm_num)
  set σ : ↥(alternatingGroup (Fin 5)) := ψ y with hσ
  have hσo : orderOf (σ : Equiv.Perm (Fin 5)) = 5 := by
    rw [Subgroup.orderOf_coe, hσ, MulEquiv.orderOf_eq, hy]
  have hσ2o : orderOf ((σ : Equiv.Perm (Fin 5)) ^ 2) = 5 := by
    rw [Nat.Coprime.orderOf_pow (by rw [hσo]; norm_num), hσo]
  have hct : ∀ τ : Equiv.Perm (Fin 5), orderOf τ = 5 → τ.cycleType = {5} := by
    intro τ hτ
    obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (by rw [hτ]; norm_num : (orderOf τ).Prime)
    have hle := τ.sum_cycleType_le
    rw [hn, hτ, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hle
    have hn0 : n = 0 := by omega
    rw [hn, hn0, hτ]
    rfl
  have hconj : IsConj (σ : Equiv.Perm (Fin 5)) ((σ : Equiv.Perm (Fin 5)) ^ 2) := by
    rw [Equiv.Perm.isConj_iff_cycleType_eq, hct _ hσo, hct _ hσ2o]
  obtain ⟨π, hπ⟩ := isConj_iff.1 hconj
  set α : MulAut ↥D := (MulAut.congr ψ).symm (MulAut.conjNormal π) with hα
  have hαy : α y = y ^ 2 := by
    have h1 : (MulAut.conjNormal π σ : ↥(alternatingGroup (Fin 5))) = σ ^ 2 := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, hπ]
      rfl
    show ψ.symm (MulAut.conjNormal π (ψ y)) = y ^ 2
    rw [← hσ, h1, hσ, ← map_pow, MulEquiv.symm_apply_apply]
  obtain ⟨s, hs⟩ : α ∈ Φ.range := hrange ▸ Subgroup.mem_top α
  have hsy : (s : Equiv.Perm (Fin 3510)) * (y : Equiv.Perm (Fin 3510)) * (s : Equiv.Perm (Fin 3510))⁻¹ =
      (y : Equiv.Perm (Fin 3510)) ^ 2 := by
    have h1 := congrArg (fun φ : MulAut ↥D => ((φ y : ↥D) : Equiv.Perm (Fin 3510))) hs
    rw [hΦapp, hαy] at h1
    rw [h1]
    rfl
  have hyP : (y : Equiv.Perm (Fin 3510)) ∈ fi22P := fi22FiveD_le_P 0 y.2
  have hyo : orderOf (y : Equiv.Perm (Fin 3510)) = 5 := by rw [Subgroup.orderOf_coe, hy]
  obtain ⟨g, hgP, hgz⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.YS08.Fi22Copy.exists_conj_zpowers_x0 hyP hyo
  set u := g * (y : Equiv.Perm (Fin 3510)) * g⁻¹ with hu
  have hx₀u : fi22FiveLine 0 ∈ Subgroup.zpowers u := hgz ▸ Subgroup.mem_zpowers _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hx₀u
  have hsP : (s : Equiv.Perm (Fin 3510)) ∈ fi22P := (Subgroup.mem_inf.1 s.2).2
  refine ⟨g * s * g⁻¹, fi22P.mul_mem (fi22P.mul_mem hgP hsP) (fi22P.inv_mem hgP), ?_⟩
  have htu : (g * s * g⁻¹) * u * (g * s * g⁻¹)⁻¹ = u ^ 2 := by
    rw [hu]
    calc (g * s * g⁻¹) * (g * (y : Equiv.Perm (Fin 3510)) * g⁻¹) * (g * s * g⁻¹)⁻¹ =
          g * ((s : Equiv.Perm (Fin 3510)) * y * (s : Equiv.Perm (Fin 3510))⁻¹) * g⁻¹ := by group
      _ = g * (y : Equiv.Perm (Fin 3510)) ^ 2 * g⁻¹ := by rw [hsy]
      _ = (g * (y : Equiv.Perm (Fin 3510)) * g⁻¹) ^ 2 := by rw [conj_pow]
  calc (g * s * g⁻¹) * fi22FiveLine 0 * (g * s * g⁻¹)⁻¹ =
        ((g * s * g⁻¹) * u * (g * s * g⁻¹)⁻¹) ^ j := by rw [conj_zpow, hj]
    _ = (u ^ 2) ^ j := by rw [htu]
    _ = (u ^ j) ^ 2 := by group
    _ = fi22FiveLine 0 ^ 2 := by rw [hj]

theorem fi22P_exists_conj_x0
    {y : Equiv.Perm (Fin 3510)} (hyP : y ∈ fi22P) (hy : orderOf y = 5) :
    ∃ g ∈ fi22P, g * y * g⁻¹ = fi22FiveLine 0 := by
  obtain ⟨t, htP, ht⟩ := fi22_exists_conj_sq
  obtain ⟨g, hgP, hgz⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.YS08.Fi22Copy.exists_conj_zpowers_x0 hyP hy
  have hmem : g * y * g⁻¹ ∈ Subgroup.zpowers (fi22FiveLine 0) := hgz ▸ Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hord : orderOf (fi22FiveLine 0) = 5 := orderOf_fi22FiveLine 0
  have hti : ∀ i : ℕ, t ^ i * fi22FiveLine 0 * (t ^ i)⁻¹ = fi22FiveLine 0 ^ (2 ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc t ^ (i + 1) * fi22FiveLine 0 * (t ^ (i + 1))⁻¹ =
            t * (t ^ i * fi22FiveLine 0 * (t ^ i)⁻¹) * t⁻¹ := by group
        _ = (t * fi22FiveLine 0 * t⁻¹) ^ (2 ^ i) := by rw [ih, conj_pow]
        _ = fi22FiveLine 0 ^ (2 ^ (i + 1)) := by rw [ht, ← pow_mul, pow_succ']
  obtain ⟨n, hn, hnk⟩ : ∃ n : ℕ, n < 5 ∧ (n : ℤ) = k % 5 := ⟨(k % 5).toNat, by omega, by omega⟩
  have hkn : fi22FiveLine 0 ^ k = fi22FiveLine 0 ^ n := by
    rw [← zpow_mod_orderOf, hord, ← zpow_natCast, hnk]
    norm_num
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [hkn, pow_zero] at hk
    have hy1 : y = 1 := by
      have := congrArg (fun z => g⁻¹ * z * g) hk
      simpa [mul_assoc] using this.symm
    rw [hy1, orderOf_one] at hy
    norm_num at hy
  obtain ⟨i, hi⟩ : ∃ i : ℕ, fi22FiveLine 0 ^ n = fi22FiveLine 0 ^ (2 ^ i) := by
    have h5 : fi22FiveLine 0 ^ 5 = 1 := by
      have := pow_orderOf_eq_one (fi22FiveLine 0)
      rwa [hord] at this
    interval_cases n
    · exact absurd rfl hn0
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩
    · refine ⟨3, ?_⟩
      rw [show 2 ^ 3 = 5 + 3 by norm_num, pow_add, h5, one_mul]
    · exact ⟨2, by norm_num⟩
  have key : g * y * g⁻¹ = t ^ i * fi22FiveLine 0 * (t ^ i)⁻¹ := by
    rw [← hk, hkn, hi, hti]
  refine ⟨(t ^ i)⁻¹ * g, fi22P.mul_mem (fi22P.inv_mem (fi22P.pow_mem htP i)) hgP, ?_⟩
  calc (t ^ i)⁻¹ * g * y * ((t ^ i)⁻¹ * g)⁻¹ = (t ^ i)⁻¹ * (g * y * g⁻¹) * t ^ i := by group
    _ = (t ^ i)⁻¹ * (t ^ i * fi22FiveLine 0 * (t ^ i)⁻¹) * t ^ i := by rw [key]
    _ = fi22FiveLine 0 := by group

theorem inputFi22OneClassFive_holds :
    Claims1110.InputFi22OneClassFive := by
  intro X _ _ hX x y hx hy
  obtain ⟨e⟩ := hX
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have β' : CFSG.Blueprint.NativeSporadic.Fi22 ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group := β
  let θ : X ≃* ↥fi22P := (e.trans β'.symm).trans fi22PermEquiv
  have hxo : orderOf ((θ x : ↥fi22P) : Equiv.Perm (Fin 3510)) = 5 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx]
  have hyo : orderOf ((θ y : ↥fi22P) : Equiv.Perm (Fin 3510)) = 5 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy]
  obtain ⟨g₁, hg₁P, hg₁⟩ := fi22P_exists_conj_x0 (θ x).2 hxo
  obtain ⟨g₂, hg₂P, hg₂⟩ := fi22P_exists_conj_x0 (θ y).2 hyo
  let c : ↥fi22P := ⟨g₂⁻¹ * g₁, fi22P.mul_mem (fi22P.inv_mem hg₂P) hg₁P⟩
  have hc : c * θ x * c⁻¹ = θ y := by
    apply Subtype.ext
    show (g₂⁻¹ * g₁) * ((θ x : ↥fi22P) : Equiv.Perm (Fin 3510)) * (g₂⁻¹ * g₁)⁻¹ = θ y
    calc (g₂⁻¹ * g₁) * ((θ x : ↥fi22P) : Equiv.Perm (Fin 3510)) * (g₂⁻¹ * g₁)⁻¹ =
          g₂⁻¹ * (g₁ * ((θ x : ↥fi22P) : Equiv.Perm (Fin 3510)) * g₁⁻¹) * g₂ := by group
      _ = g₂⁻¹ * (g₂ * ((θ y : ↥fi22P) : Equiv.Perm (Fin 3510)) * g₂⁻¹) * g₂ := by rw [hg₁, hg₂]
      _ = θ y := by group
  refine ⟨θ.symm c, θ.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc]

end Fi22Class

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110b
