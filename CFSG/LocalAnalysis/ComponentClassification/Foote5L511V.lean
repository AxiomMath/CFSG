module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511T
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SmallIndexBasic

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem card_lt_card_inf_mul_card_centralizer_L511V {P X : Subgroup G} {z : G} (hzP : z ∈ P)
    (hzX : z ∈ X) (hz1 : z ≠ 1) (hPX : ∀ g ∈ P, ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    Nat.card P < Nat.card ↥(P ⊓ X) * Nat.card ↥(P ⊓ centralizer ({z} : Set G)) := by
  classical
  set z' : ↥P := ⟨z, hzP⟩ with hz'
  set O := MulAction.orbit (ConjAct ↥P) z' with hO
  set St := MulAction.stabilizer (ConjAct ↥P) z' with hSt
  have h1 : Nat.card O * Nat.card St = Nat.card P := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct ↥P) z')).trans
      (Nat.card_congr ConjAct.ofConjAct.toEquiv)
  have hst : ∀ c : ConjAct ↥P, c ∈ St ↔
      ((ConjAct.ofConjAct c : ↥P) : G) * z = z * ((ConjAct.ofConjAct c : ↥P) : G) := by
    intro c
    rw [hSt, MulAction.mem_stabilizer_iff, ConjAct.smul_def]
    constructor
    · intro h2
      have h3 : ((ConjAct.ofConjAct c : ↥P) : G) * z * ((ConjAct.ofConjAct c : ↥P) : G)⁻¹ = z :=
        congrArg Subtype.val h2
      calc ((ConjAct.ofConjAct c : ↥P) : G) * z
          = ((ConjAct.ofConjAct c : ↥P) : G) * z * ((ConjAct.ofConjAct c : ↥P) : G)⁻¹ *
            ((ConjAct.ofConjAct c : ↥P) : G) := by group
        _ = z * ((ConjAct.ofConjAct c : ↥P) : G) := by rw [h3]
    · intro h2
      apply Subtype.ext
      change ((ConjAct.ofConjAct c : ↥P) : G) * z * ((ConjAct.ofConjAct c : ↥P) : G)⁻¹ = z
      rw [h2, mul_inv_cancel_right]
  have h2 : Nat.card St = Nat.card ↥(P ⊓ centralizer ({z} : Set G)) := by
    refine Nat.card_congr
      { toFun := fun c => ⟨((ConjAct.ofConjAct (c : ConjAct ↥P) : ↥P) : G),
          mem_inf.mpr ⟨(ConjAct.ofConjAct (c : ConjAct ↥P)).2,
            mem_centralizer_singleton_iff.mpr ((hst c).mp c.2)⟩⟩
        invFun := fun x => ⟨ConjAct.toConjAct (⟨x, (mem_inf.mp x.2).1⟩ : ↥P),
          (hst _).mpr (mem_centralizer_singleton_iff.mp (mem_inf.mp x.2).2)⟩
        left_inv := fun c => rfl
        right_inv := fun x => rfl }
  have hOX : ∀ y ∈ O, ((y : ↥P) : G) ∈ X := by
    rintro y ⟨c, rfl⟩
    change ((ConjAct.ofConjAct c : ↥P) : G) * z * ((ConjAct.ofConjAct c : ↥P) : G)⁻¹ ∈ X
    exact hPX _ (ConjAct.ofConjAct c).2 z hzX
  have hO1 : (1 : ↥P) ∉ O := by
    rintro ⟨c, hc⟩
    apply hz1
    have h4 : ((ConjAct.ofConjAct c : ↥P) : G) * z * ((ConjAct.ofConjAct c : ↥P) : G)⁻¹ = 1 :=
      congrArg Subtype.val hc
    calc z = ((ConjAct.ofConjAct c : ↥P) : G)⁻¹ * (((ConjAct.ofConjAct c : ↥P) : G) * z *
          ((ConjAct.ofConjAct c : ↥P) : G)⁻¹) * ((ConjAct.ofConjAct c : ↥P) : G) := by group
      _ = 1 := by rw [h4]; group
  have h3 : Nat.card O < Nat.card ↥(P ⊓ X) := by
    have := Fintype.ofFinite O
    have := Fintype.ofFinite ↥(P ⊓ X)
    let f : O → ↥(P ⊓ X) := fun y => ⟨((y : ↥P) : G), mem_inf.mpr ⟨(y : ↥P).2, hOX y y.2⟩⟩
    have hf : Function.Injective f := fun a b hab => by
      have h7 : ((f a : ↥(P ⊓ X)) : G) = ((f b : ↥(P ⊓ X)) : G) := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h7)
    have hnot : (1 : ↥(P ⊓ X)) ∉ Set.range f := by
      rintro ⟨y, hy⟩
      apply hO1
      have h7 : ((f y : ↥(P ⊓ X)) : G) = ((1 : ↥(P ⊓ X)) : G) := congrArg Subtype.val hy
      have h5 : (y : ↥P) = 1 := Subtype.ext h7
      rw [← h5]
      exact y.2
    have h6 := Fintype.card_lt_of_injective_of_notMem f hf hnot
    rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h6
  rw [← h1, h2]
  exact Nat.mul_lt_mul_of_pos_right h3 Nat.card_pos

variable {𝕊 : Type} [Group 𝕊]

theorem card_actImage_le_of_isSylowOf_L511V [Finite 𝕊] {A K S P : Subgroup G}
    (ε : A ⧸ pPrimeCore 2 A ≃* 𝕊) (hKN : K ≤ normalizer (A : Set G)) (hS : IsSylowOf 2 S K)
    (hPK : P ≤ K) (hP : IsPGroup 2 P) :
    Nat.card (actImage A ε P) ≤ Nat.card (actImage A ε S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hkK, hk⟩ := exists_conj_le_of_isSylowOf hS hPK hP
  have hkN := hKN hkK
  set γ : MulAut 𝕊 := (actG A ε k)⁻¹ with hγ
  have hle : (actImage A ε P).map (MulAut.conj γ).toMonoidHom ≤ actImage A ε S := by
    rintro _ ⟨α, hα, rfl⟩
    obtain ⟨p, hp, rfl⟩ := (mem_actImage ε (hPK.trans hKN)).mp hα
    have hpN := hKN (hPK hp)
    rw [mem_actImage ε (hS.le.trans hKN)]
    refine ⟨k⁻¹ * p * k, hk p hp, ?_⟩
    rw [actG_mul ε (mul_mem (inv_mem hkN) hpN) hkN, actG_mul ε (inv_mem hkN) hpN, actG_inv ε hkN,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hγ, inv_inv]
  calc Nat.card (actImage A ε P)
      = Nat.card ((actImage A ε P).map (MulAut.conj γ).toMonoidHom) :=
        (card_map_of_injective (f := (MulAut.conj γ).toMonoidHom) (MulAut.conj γ).injective).symm
    _ ≤ Nat.card (actImage A ε S) := card_le_of_le hle

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊) {Lin : Subgroup (MulAut 𝕊)}
include h

include ε in
theorem exists_sylow_centralizer_diag_L511V (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) (hT2 : Nat.card T = 2 * Nat.card S)
    {s : G} (hsT : s ∈ T) (hsS : s ∉ S) (hz : z = s⁻¹ * t * s) {r : G}
    (hr : r ∈ conjugate (S ⊓ L) s) (hr2 : r * r = 1) (hrt : r * t ∈ Q) :
    r * t * (r * t) = 1 ∧ r * t ≠ 1 ∧ r * t ≠ z ∧ ∃ T' : Subgroup G, IsPGroup 2 T' ∧
      T' ≤ centralizer ({r * t} : Set G) ∧ Nat.card T' = 2 * Nat.card S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 := h.t_mul_self
  have hsN := mem_normalizer_of_card_eq_two_mul h.ST hT2 hsT
  have hss : s * s ∈ S := mul_mem_of_card_eq_two_mul h.ST hT2 hsT hsT hsS hsS
  have hst : s * t * s⁻¹ ≠ t := by rw [h.conj_t_eq_z hss hz]; exact h.z_ne_t
  have hRs := h.inf_conjugate_R_eq_bot hna hsN hst
  have hRRs : ∀ x : G, x ∈ S ⊓ L → x ∈ conjugate (S ⊓ L) s → x = 1 := fun x hx hx' => by
    have h1 : x ∈ S ⊓ L ⊓ conjugate (S ⊓ L) s := mem_inf.mpr ⟨hx, hx'⟩
    rwa [hRs, mem_bot] at h1
  have hrS : r ∈ S := conjugate_le_of_mem_normalizer hsN inf_le_left hr
  have hr1 : r ≠ 1 := fun h1 => h.t_not_mem_Q (by rwa [h1, one_mul] at hrt)
  have hrtc : r * t = t * r := h.tZ r hrS
  have hrR : ∀ ρ ∈ S ⊓ L, r * ρ = ρ * r := fun ρ hρ =>
    h.commute_of_inf_conjugate_eq_bot hsN hRs hρ hr
  have hrt' : r ≠ t := fun h1 => h.t_ne_one (hRRs t h.tR (h1 ▸ hr))
  have hzr : IsConj z r := by
    have hsr : s * r * s⁻¹ ∈ S ⊓ L := mem_conjugate_iff.mp hr
    have hsr2 : (s * r * s⁻¹) ^ 2 = 1 := by
      rw [sq, show s * r * s⁻¹ * (s * r * s⁻¹) = s * (r * r) * s⁻¹ by group, hr2]
      group
    have hsr1 : s * r * s⁻¹ ≠ 1 := fun h1 => hr1 (by
      calc r = s⁻¹ * (s * r * s⁻¹) * s := by group
        _ = 1 := by rw [h1]; group)
    obtain ⟨k, -, hk⟩ := h.exists_conj_t hsr (orderOf_eq_prime hsr2 hsr1)
    refine isConj_iff.mpr ⟨s⁻¹ * k * s, ?_⟩
    calc s⁻¹ * k * s * z * (s⁻¹ * k * s)⁻¹ = s⁻¹ * (k * t * k⁻¹) * s := by rw [hz]; group
      _ = s⁻¹ * (s * r * s⁻¹) * s := by rw [← hk]; group
      _ = r := by group
  obtain ⟨g', hg'z, hg't⟩ := h.exists_conj_mem_centralizer_t_L511T ε hD hna hT2 hsT hsS hz hzr
    hrR hrt'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show r * t * (r * t) = r * (t * r) * t by group, ← hrtc,
      show r * (r * t) * t = (r * r) * (t * t) by group, hr2, ht2, one_mul]
  · intro h1
    exact hrt' (by rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_left ht2])
  · have hzRs : z ∈ conjugate (S ⊓ L) s := by
      rw [mem_conjugate_iff, hz, show s * (s⁻¹ * t * s) * s⁻¹ = t by group]
      exact h.tR
    intro h1
    refine h.t_ne_one (hRRs t h.tR ?_)
    have h2 : t = r⁻¹ * z := by rw [← h1]; group
    rw [h2]
    exact mul_mem (inv_mem hr) hzRs
  · have hzt : g' * (z * t) * g'⁻¹ = r * t := by
      rw [← hg'z, show g' * (z * t) * g'⁻¹ = g' * z * g'⁻¹ * (g' * t * g'⁻¹) by group,
        hg't, mul_inv_cancel_right]
    refine ⟨conjugate T g'⁻¹, ?_, ?_, by rw [card_conjugate_eq_card, hT2]⟩
    · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.sylT.isPGroup
      exact IsPGroup.of_card (n := k) (by rw [card_conjugate_eq_card, hk])
    · intro x hx
      rw [mem_conjugate_iff, inv_inv] at hx
      have h1 := h.zt_commute_T hT2 hsT hsS hz hx
      refine mem_centralizer_singleton_iff.mpr ?_
      rw [← hzt]
      calc x * (g' * (z * t) * g'⁻¹) = g' * ((g'⁻¹ * x * g') * (z * t)) * g'⁻¹ := by group
        _ = g' * ((z * t) * (g'⁻¹ * x * g')) * g'⁻¹ := by rw [h1]
        _ = g' * (z * t) * g'⁻¹ * x := by group

theorem two_mul_twoPart_le_L511V {b : G} (hbQ : b ∈ Q) (hb2 : b * b = 1) (hb1 : b ≠ 1)
    (hbz : b ≠ z) {T' : Subgroup G} (hT'2 : IsPGroup 2 T') (hT'C : T' ≤ centralizer ({b} : Set G))
    (hT'S : Nat.card S < Nat.card T') :
    2 * twoPart (coreActionKernel (footeF L₀ b)) ≤ Nat.card Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 := h.sec4
  have hbS := h.QS hbQ
  have hb2' : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb2) hb1
  have hbC : b ∈ coreActionKernel L := h.Q_le hbQ
  obtain ⟨-, hLb, hLbF⟩ := footeFixed_eq_footeF h4.hLB h4.hGA h4.hGC h4.hSA
    h4.footeFamilyType h4.huniq h4.hrank2 h.pmax h.memF hb2' hbC
  have hCbN := le_normalizer_of_mem_footeFamilyOf h4.huniq hLb hLbF
  have hzb : z * b = b * z := (h.zS b hbS).symm
  have hzC : z ∈ coreActionKernel (footeF L₀ b) :=
    (h.mem_coreActionKernel_footeF_iff hbC hb2' (h.S_le (h.QS h.zQ))
      (mem_centralizer_singleton_iff.mpr hzb)).mpr (h.Q_le h.zQ)
  have hbC' : b ∈ coreActionKernel (footeF L₀ b) :=
    (h.mem_coreActionKernel_footeF_iff hbC hb2' (h.S_le hbS)
      (mem_centralizer_singleton_iff.mpr rfl)).mpr hbC
  have hz1 : z ≠ 1 := fun h1 => by
    have h2 := h.z2
    rw [h1, orderOf_one] at h2
    omega
  have hrank : CFSG.pRank 2 ↥(coreActionKernel (footeF L₀ b)) = 2 := by
    refine le_antisymm (h.rankC _ hLbF) ?_
    rw [(SectionRank.pRank_eq_open_pRank_top 2 _).trans
      (SectionRank.pRank_eq_pRank_top_subgroup _).symm]
    exact AschbacherTheorem3.two_le_pRank_of_involutions hzC hbC' (by rw [sq]; exact h.z_mul_self)
      (by rw [sq]; exact hb2) hz1 hb1 hbz.symm hzb
  have hle := h.maxQ _ hLbF hrank
  have hne : twoPart (coreActionKernel (footeF L₀ b)) ≠ Nat.card Q := fun heq => by
    have hmax := h.maxS _ hLbF hrank heq
    have hT'le := card_le_twoPart hT'2 (hT'C.trans hCbN)
    omega
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_Q
  rw [twoPart, hk] at hle hne ⊢
  have hlt : (Nat.card ↥(coreActionKernel (footeF L₀ b))).factorization 2 < k := by
    by_contra hge
    push Not at hge
    exact hne (le_antisymm hle (Nat.pow_le_pow_right (by norm_num) hge))
  calc 2 * 2 ^ (Nat.card ↥(coreActionKernel (footeF L₀ b))).factorization 2
      = 2 ^ ((Nat.card ↥(coreActionKernel (footeF L₀ b))).factorization 2 + 1) := by ring
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hlt

end Sec5

end CFSG.ComponentClassification.Foote5
