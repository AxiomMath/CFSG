module

public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Defs

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open scoped Pointwise

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {z y : G} (hz : orderOf z = 2)
    (hy : y ∈ zpowers z) : y = 1 ∨ y = z := by
  obtain ⟨k, rfl⟩ := hy
  show z ^ k = 1 ∨ z ^ k = z
  rw [← zpow_mod_orderOf, hz]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    simp only [Nat.cast_ofNat, h, zpow_zero]
  · right
    simp only [Nat.cast_ofNat, h, zpow_one]

theorem mem_centerIn {G : Type} [Group G] {H : Subgroup G} {x : G} :
    x ∈ centerIn H ↔ x ∈ H ∧ x ∈ centralizer (H : Set G) :=
  Iff.rfl

namespace Sec4Q

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F S₁ Q : Subgroup G}
  {z : G}

theorem z_mem_centerIn_Q (hQ : Sec4Q G A R g E F S₁ Q z) : z ∈ centerIn Q := by
  rw [hQ.center_Q]
  exact mem_zpowers z

theorem z_mem_Q (hQ : Sec4Q G A R g E F S₁ Q z) : z ∈ Q :=
  hQ.z_mem_centerIn_Q.1

theorem le_centralizer (hQ : Sec4Q G A R g E F S₁ Q z) : S₁ ≤ centralizer ({z} : Set G) := by
  intro s hs
  have hz : z ∈ centerIn S₁ := by rw [hQ.center_S₁]; exact mem_zpowers z
  rw [mem_centralizer_singleton_iff]
  exact (mem_centralizer_iff.mp hz.2) s hs

theorem Q_le_centralizer (hQ : Sec4Q G A R g E F S₁ Q z) : Q ≤ centralizer ({z} : Set G) :=
  hQ.le.trans hQ.le_centralizer

theorem z_ne_one (hQ : Sec4Q G A R g E F S₁ Q z) : z ≠ 1 := by
  intro h
  have := hQ.order_z
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem normalizer_le_centralizer (hQ : Sec4Q G A R g E F S₁ Q z) :
    normalizer (Q : Set G) ≤ centralizer ({z} : Set G) := by
  intro n hn
  have hzc : z ∈ centralizer (Q : Set G) := hQ.z_mem_centerIn_Q.2
  have h1 : n * z * n⁻¹ ∈ centerIn Q := by
    refine mem_centerIn.mpr ⟨(mem_normalizer_iff.mp hn z).mp hQ.z_mem_Q, ?_⟩
    rw [mem_centralizer_iff]
    intro q hq
    have hq' : n⁻¹ * q * n ∈ Q := by
      have := (mem_normalizer_iff.mp (inv_mem hn) q).mp hq
      simpa using this
    have hc := mem_centralizer_iff.mp hzc _ hq'
    calc q * (n * z * n⁻¹) = n * ((n⁻¹ * q * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * q * n)) * n⁻¹ := by rw [hc]
      _ = n * z * n⁻¹ * q := by group
  rw [hQ.center_Q] at h1
  rw [mem_centralizer_singleton_iff]
  rcases eq_one_or_eq_of_mem_zpowers hQ.order_z h1 with h | h
  · refine absurd ?_ hQ.z_ne_one
    calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  · calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [h]

theorem commutator_mem (hQ : Sec4Q G A R g E F S₁ Q z) {q v : G} (hq : q ∈ Q) (hv : v ∈ Q) :
    q * v * q⁻¹ * v⁻¹ ∈ zpowers z := by
  rw [← hQ.center_Q]
  have h1 : (⟨q, hq⟩ : Q) * ⟨v, hv⟩ * (⟨q, hq⟩ : Q)⁻¹ * (⟨v, hv⟩ : Q)⁻¹ ∈ center Q := by
    rw [← hQ.extraspecial.2.1]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  refine mem_centerIn.mpr
    ⟨Q.mul_mem (Q.mul_mem (Q.mul_mem hq hv) (Q.inv_mem hq)) (Q.inv_mem hv), ?_⟩
  rw [mem_centralizer_iff]
  intro w hw
  exact congrArg Subtype.val ((mem_center_iff.mp h1) ⟨w, hw⟩)

theorem z_mem_E (h46 : Step46) (hQ : Sec4Q G A R g E F S₁ Q z) : z ∈ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hX, -⟩ := h46 G A R g E F S₁ Q z hQ
  obtain ⟨-, -, -, hcard⟩ := hX E (by simp)
  have : Group.IsNilpotent Q := hQ.extraspecial.1.isNilpotent
  have hN : (E.subgroupOf Q).Normal := by
    constructor
    intro x hx q
    rw [mem_subgroupOf] at hx ⊢
    simp only [coe_mul, coe_inv]
    exact (mem_normalizer_iff.mp (hQ.normE q.2) x).mp hx
  have hne : E.subgroupOf Q ≠ ⊥ := by
    intro h
    have h1 : Nat.card (E.subgroupOf Q) = 16 := by
      rw [← hcard, inf_comm, ← inf_subgroupOf_right E Q]
      exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [h, card_bot] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyE : ((y : Q) : G) ∈ E := mem_subgroupOf.mp (mem_inf.mp y.2).1
  have hyZ : ((y : Q) : G) ∈ centerIn Q := by
    refine mem_centerIn.mpr ⟨(y : Q).2, mem_centralizer_iff.mpr fun w hw => ?_⟩
    exact congrArg Subtype.val ((mem_center_iff.mp (mem_inf.mp y.2).2) ⟨w, hw⟩)
  rw [hQ.center_Q] at hyZ
  rcases eq_one_or_eq_of_mem_zpowers hQ.order_z hyZ with h | h
  · exact absurd (Subtype.ext (Subtype.ext h)) hy1
  · rwa [← h]

end Sec4Q

theorem card_rankTwoQuot_of_typeL34 {G : Type} [Group G] {A : Subgroup G}
    (hL : TypeL34 (rankTwoQuot A)) : Nat.card (rankTwoQuot A) = 20160 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK]
  decide

theorem le_center_or_eq_top_of_isQuasisimple {H : Type*} [Group H] (hH : Open.IsQuasisimple H)
    {N : Subgroup H} (hN : N.Normal) : N ≤ center H ∨ N = ⊤ := by
  obtain ⟨hp, hs⟩ := hH
  have := hN.map (QuotientGroup.mk' (center H)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (center H))) with
    h | h
  · left
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · right
    have hsup : N ⊔ center H = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (center H)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hZ : ⁅center H, center H⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hmap : (⊤ : Subgroup H).map (QuotientGroup.mk' N) =
        (center H).map (QuotientGroup.mk' N) := by
      rw [← hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    have hcomm : commutator H ≤ N := by
      rw [_root_.commutator_def, ← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
        Subgroup.map_commutator, hmap, ← Subgroup.map_commutator, hZ, Subgroup.map_bot]
    exact eq_top_iff.mpr (hp ▸ hcomm)

theorem le_center_or_eq_of_isQuasisimple {G : Type*} [Group G] {A N : Subgroup G}
    (hA : Open.IsQuasisimple A) (hNA : N ≤ A) (hAN : A ≤ normalizer (N : Set G)) :
    N ≤ (center A).map A.subtype ∨ N = A := by
  have hn : (N.subgroupOf A).Normal := (normal_subgroupOf_iff_le_normalizer hNA).mpr hAN
  rcases le_center_or_eq_top_of_isQuasisimple hA hn with h | h
  · left
    intro x hx
    exact ⟨⟨x, hNA hx⟩, h hx, rfl⟩
  · right
    refine le_antisymm hNA fun x hx => ?_
    have : (⟨x, hx⟩ : A) ∈ N.subgroupOf A := h ▸ mem_top _
    exact this

theorem exists_isSylowOf_ge_of_le {G : Type*} [Group G] [Finite G] {T C : Subgroup G}
    (hTC : T ≤ C) (hT : IsPGroup 2 T) : ∃ P : Subgroup G, T ≤ P ∧ IsSylowOf 2 P C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsPGroup 2 (T.subgroupOf C) := hT.comap_subtype
  obtain ⟨S, hS⟩ := hT'.exists_le_sylow
  refine ⟨(S : Subgroup C).map C.subtype, fun t ht => ?_, S, rfl⟩
  exact ⟨⟨t, hTC ht⟩, hS (show (⟨t, hTC ht⟩ : C) ∈ T.subgroupOf C from ht), rfl⟩

theorem le_normalizer_inf {G : Type*} [Group G] {A C M : Subgroup G} (hAC : A ≤ C)
    (hCM : C ≤ normalizer (M : Set G)) : A ≤ normalizer ((A ⊓ M : Subgroup G) : Set G) := by
  intro a ha
  rw [mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨hy1, hy2⟩
    exact ⟨A.mul_mem (A.mul_mem ha hy1) (A.inv_mem ha),
      (mem_normalizer_iff.mp (hCM (hAC ha)) y).mp hy2⟩
  · rintro ⟨hy1, hy2⟩
    refine ⟨?_, (mem_normalizer_iff.mp (hCM (hAC ha)) y).mpr hy2⟩
    have := A.mul_mem (A.mul_mem (A.inv_mem ha) hy1) ha
    simpa [mul_assoc] using this

theorem false_of_quasisimple_le {G : Type*} [Group G] [Finite G] {A Z T C M O Q : Subgroup G}
    (hA : ∀ N : Subgroup G, N ≤ A → A ≤ normalizer (N : Set G) → N ≤ Z ∨ N = A)
    (hZ : 2 ^ 7 < Z.relIndex A)
    (hTA : T ≤ A) (hT : IsPGroup 2 T) (hT7 : 2 ^ 7 ≤ Nat.card T)
    (hTZ : Nat.card (T ⊓ Z : Subgroup G) ≤ 4)
    (hAC : A ≤ C) (hMC : M ≤ C) (hCM : C ≤ normalizer (M : Set G))
    (hOM : O ≤ M) (hCO : C ≤ normalizer (O : Set G)) (hO : Odd (Nat.card O))
    (hQM : Q ≤ M) (hM : M ≤ O ⊔ Q) (hQ : Nat.card Q = 2 ^ 7)
    (hC : ∀ P : Subgroup G, IsSylowOf 2 P C → Nat.card P ≤ 2 ^ 11) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hA (A ⊓ M) inf_le_left (le_normalizer_inf hAC hCM) with hZ' | hAM
  ·
    obtain ⟨P, hTP, hP⟩ := exists_isSylowOf_ge_of_le (hTA.trans hAC) hT
    have hK : IsSylowOf 2 (P ⊓ M) M := hP.inf_of_le_normalizer hMC hCM
    have hK7 : 2 ^ 7 ≤ Nat.card (P ⊓ M : Subgroup G) := by
      rw [hK.card_eq]
      have hdvd : 2 ^ 7 ∣ Nat.card M := hQ ▸ Subgroup.card_dvd_of_le hQM
      have := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
      exact Nat.pow_le_pow_right (by norm_num) this
    have hTK : Nat.card (P ⊓ M ⊓ T : Subgroup G) ≤ 4 := by
      refine le_trans (Subgroup.card_le_of_le ?_) hTZ
      intro t ht
      exact ⟨ht.2, hZ' ⟨hTA ht.2, ht.1.2⟩⟩
    have h1 := Subgroup.relIndex_mul_card (P ⊓ M) T
    have h2 := Subgroup.relIndex_mul_card (P ⊓ M) P
    rw [inf_eq_left.mpr (inf_le_left : P ⊓ M ≤ P)] at h2
    have hP0 : (P ⊓ M).relIndex P ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h2
      exact Nat.card_pos.ne' h2.symm
    have h3 : (P ⊓ M).relIndex T ≤ (P ⊓ M).relIndex P :=
      Subgroup.relIndex_le_of_le_right hTP hP0
    have hP11 := hC P hP
    have ha : 32 ≤ (P ⊓ M).relIndex T := by nlinarith
    have hb : (P ⊓ M).relIndex P ≤ 16 := by nlinarith
    omega
  ·
    have hAM' : A ≤ M := hAM ▸ inf_le_right
    rcases hA (A ⊓ O) inf_le_left (le_normalizer_inf hAC hCO) with hZO | hAO
    · have hO0 : O.relIndex M ≠ 0 := by
        intro h0
        have := Subgroup.relIndex_mul_card O M
        rw [h0, zero_mul] at this
        exact Nat.card_pos.ne' this.symm
      have h1 : O.relIndex A ≤ O.relIndex M := Subgroup.relIndex_le_of_le_right hAM' hO0
      have h2 : Z.relIndex A ∣ O.relIndex A := by
        rw [← Subgroup.inf_relIndex_right O A]
        exact Subgroup.relIndex_dvd_of_le_left A fun x hx => hZO ⟨hx.2, hx.1⟩
      have hOQ : ((O ⊔ Q : Subgroup G) : Set G) = (O : Set G) * (Q : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left O Q ((hQM.trans hMC).trans hCO)
      have hcardM : Nat.card M ≤ Nat.card O * Nat.card Q := by
        calc Nat.card M ≤ Nat.card (O ⊔ Q : Subgroup G) := Subgroup.card_le_of_le hM
          _ = Nat.card ((O : Set G) * (Q : Set G)) := by rw [← hOQ]; rfl
          _ ≤ Nat.card O * Nat.card Q := Set.natCard_mul_le
      have h3 := Subgroup.relIndex_mul_card O M
      rw [inf_eq_left.mpr hOM] at h3
      have hO' := (Nat.card_pos (α := O))
      have h4 : O.relIndex M ≤ 2 ^ 7 := by
        rw [hQ] at hcardM
        nlinarith
      have h5 : 0 < O.relIndex A := by
        refine Nat.pos_of_ne_zero fun h0 => ?_
        have := Subgroup.relIndex_mul_card O A
        rw [h0, zero_mul] at this
        exact Nat.card_pos.ne' this.symm
      have := Nat.le_of_dvd h5 h2
      omega
    · have hTO : T ≤ O := hTA.trans (hAO ▸ inf_le_right)
      have hodd := hO.of_dvd_nat (Subgroup.card_dvd_of_le hTO)
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT
      rcases n with _ | n
      · rw [hn] at hT7
        norm_num at hT7
      · rw [hn, pow_succ] at hodd
        exact absurd hodd (by simp [Nat.not_odd_iff_even, parity_simps])

theorem map_conj_centralizer {G : Type*} [Group G] (x z : G) :
    (centralizer ({z} : Set G)).map (MulAut.conj x).toMonoidHom =
      centralizer ({x * z * x⁻¹} : Set G) := by
  ext y
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
    MulAut.conj_symm_apply]
  constructor
  · intro h
    calc y * (x * z * x⁻¹) = x * ((x⁻¹ * y * x) * z) * x⁻¹ := by group
      _ = x * (z * (x⁻¹ * y * x)) * x⁻¹ := by rw [h]
      _ = x * z * x⁻¹ * y := by group
  · intro h
    calc x⁻¹ * y * x * z = x⁻¹ * (y * (x * z * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * z * x⁻¹) * y) * x := by rw [h]
      _ = z * (x⁻¹ * y * x) := by group

namespace Sec4Q

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F S₁ Q : Subgroup G}
  {z : G}

theorem two_pow_seven_le_card_sup (hQ : Sec4Q G A R g E F S₁ Q z) :
    2 ^ 7 ≤ Nat.card (E ⊔ F : Subgroup G) := by
  have hF := hQ.setting.frame
  have hT := hF.sylow.isPGroup
  have hlt : E < E ⊔ F := by
    refine lt_of_le_of_ne le_sup_left fun h => hF.ne ?_
    have hFE : F ≤ E := h ▸ le_sup_right
    exact (Subgroup.eq_of_le_of_card_ge hFE (by rw [hF.cardE, hF.cardF])).symm
  have h1 := Subgroup.card_lt_of_lt hlt
  have h2 : 64 ∣ Nat.card (E ⊔ F : Subgroup G) := hF.cardE ▸ Subgroup.card_dvd_of_le le_sup_left
  rw [hF.cardE] at h1
  omega

theorem not_mem_rightConjugate (h16 : Step16) (h44 : Step44ii) (hQ : Sec4Q G A R g E F S₁ Q z)
    (hM : centralizer ({z} : Set G) ≤
      normalizer ((Q ⊔ AS76b.oddCoreIn (centralizer ({z} : Set G)) : Subgroup G) : Set G))
    (x : G) : z ∉ rightConjugate R x := by
  intro hzx
  rw [mem_rightConjugate_iff] at hzx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := hQ.setting.frame
  have hRA : R ≤ A := (h16 G A R g E F hF hQ.setting.even).1
  have hAR : A ⊔ R = A := sup_eq_left.mpr hRA
  obtain ⟨O, hO⟩ : ∃ O, O = AS76b.oddCoreIn (centralizer ({z} : Set G)) := ⟨_, rfl⟩
  rw [← hO] at hM
  have hC := map_conj_centralizer x z
  have hOC : O ≤ centralizer ({z} : Set G) := hO ▸ AS76b.oddCoreIn_le _
  have hMC : Q ⊔ O ≤ centralizer ({z} : Set G) := sup_le hQ.Q_le_centralizer hOC
  have hCO : centralizer ({z} : Set G) ≤ normalizer (O : Set G) :=
    hO ▸ AS76b.le_normalizer_oddCoreIn _
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = (center A).map A.subtype := ⟨_, rfl⟩
  have hRZ : R ≤ Z := by
    intro r hr
    rw [hZ]
    exact ⟨⟨r, hRA hr⟩, mem_center_iff.mpr fun a =>
      Subtype.ext ((mem_centralizer_iff.mp (hF.sylowR.le hr)) a a.2), rfl⟩
  have hZC : Z ≤ centralizer (A : Set G) := by
    rw [hZ]
    rintro _ ⟨y, hy, rfl⟩
    exact mem_centralizer_iff.mpr fun a ha => congrArg Subtype.val ((mem_center_iff.mp hy) ⟨a, ha⟩)
  have hEA : E ≤ A := hAR ▸ hF.E_le
  have hFA : F ≤ A := hAR ▸ hF.F_le
  have hT := hF.sylow.isPGroup
  have hTZ : (E ⊔ F) ⊓ Z = R :=
    hF.sylowR.eq_of_le (le_inf (hF.R_le_E.trans le_sup_left) hRZ) (inf_le_right.trans hZC)
      (hT.to_le inf_le_left)
  have hZA : Z.relIndex A = 20160 := by
    rw [Subgroup.relIndex, hZ, show ((center A).map A.subtype).subgroupOf A = center A from
      comap_map_eq_self_of_injective A.subtype_injective _, index_eq_card]
    exact card_rankTwoQuot_of_typeL34 hQ.setting.type
  refine false_of_quasisimple_le (A := A) (Z := Z) (T := E ⊔ F)
    (C := centralizer ({x * z * x⁻¹} : Set G)) (M := (Q ⊔ O).map (MulAut.conj x).toMonoidHom)
    (O := O.map (MulAut.conj x).toMonoidHom) (Q := Q.map (MulAut.conj x).toMonoidHom)
    (fun N hNA hAN => hZ ▸ le_center_or_eq_of_isQuasisimple hF.quasisimple hNA hAN)
    (by rw [hZA]; norm_num) (sup_le hEA hFA) hT hQ.two_pow_seven_le_card_sup
    (by rw [hTZ, hF.cardR]) ?_ ?_ ?_ (map_mono le_sup_right) ?_ ?_ (map_mono le_sup_left) ?_ ?_ ?_
  ·
    intro a ha
    exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hF.sylowR.le hzx)) a ha)
  · rw [← hC]
    exact map_mono hMC
  · rw [← hC, ← map_equiv_normalizer_eq]
    exact map_mono hM
  · rw [← hC, ← map_equiv_normalizer_eq]
    exact map_mono hCO
  · rw [card_map_of_injective (MulAut.conj x).injective, hO]
    exact AS76b.odd_card_oddCoreIn _
  · rw [Subgroup.map_sup, sup_comm]
  · rw [card_map_of_injective (MulAut.conj x).injective, hQ.card]
  · intro P hP
    have hS := (hQ.sylow.of_le hQ.le_centralizer le_top).card_eq
    rw [hP.card_eq, ← hC, card_map_of_injective (MulAut.conj x).injective, ← hS]
    rcases h44 G A R g E F hQ.setting S₁ hQ.sylowN with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    norm_num

end Sec4Q

end CFSG.ComponentClassification.AS81
