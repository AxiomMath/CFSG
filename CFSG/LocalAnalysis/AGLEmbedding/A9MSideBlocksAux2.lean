module

import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeConfig
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualToolsAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Inner

variable {G : Type} [Group G] [Finite G]

theorem D1PhaseThree.mk_mem_barM_of_mul_inv_mem {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R) (h84 : Asc81bEightFour) (h86 : Asc81bEightSix)
    (hD2 : D1NoXBlock) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {x l : M}
    (hxK : (x : G) ∈ H ⊓ M) (hlL : (l : G) ∈ L)
    (hxl : QuotientGroup.mk' (CFSG.pCore 2 ↥M) x * (QuotientGroup.mk' (CFSG.pCore 2 ↥M) l)⁻¹ ∈
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) l ∈
      barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) := by
  have hKeq := h.inf_eq_inf_normalizer_twoCore
  set S := pCoreOf 2 H with hSdef
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLbdef
  have hxS : (x : G) ∈ Subgroup.normalizer (S : Set G) := (hKeq ▸ hxK).2
  have hlb : mk l ∈ Lb := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hlL)
  have hSL : barM M S ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    h86 G M S h.isKGroup.1 h.asc81bHyp _ hL.component
  have act : ∀ y ∈ Lb, mk x * y * (mk x)⁻¹ = mk l * y * (mk l)⁻¹ := by
    intro y hy
    have hly : mk l * y * (mk l)⁻¹ ∈ Lb := Lb.mul_mem (Lb.mul_mem hlb hy) (Lb.inv_mem hlb)
    have hz := Subgroup.mem_centralizer_iff.mp hxl _ hly
    calc mk x * y * (mk x)⁻¹
        = (mk x * (mk l)⁻¹) * (mk l * y * (mk l)⁻¹) * (mk x * (mk l)⁻¹)⁻¹ := by group
      _ = (mk l * y * (mk l)⁻¹) * (mk x * (mk l)⁻¹) * (mk x * (mk l)⁻¹)⁻¹ := by rw [← hz]
      _ = mk l * y * (mk l)⁻¹ := by group
  refine stmtBlockInnerNormalizer_of h h84 h86 hD2 hL _ hlb fun s hs => ?_
  obtain ⟨σ, hσ, rfl⟩ := hs
  have hσS : (σ : G) ∈ S := Subgroup.mem_subgroupOf.mp hσ
  have hσ' : (x : G) * σ * (x : G)⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hxS σ).mp hσS
  refine ⟨mk x * mk σ * (mk x)⁻¹, ⟨x * σ * x⁻¹, Subgroup.mem_subgroupOf.mpr hσ', by
    simp only [map_mul, map_inv]; rfl⟩, fun y hy => ?_⟩
  have hsb : mk σ ∈ barM M S := Subgroup.mem_map_of_mem _ hσ
  have hy1 : (mk l)⁻¹ * y * mk l ∈ Lb := Lb.mul_mem (Lb.mul_mem (Lb.inv_mem hlb) hy) hlb
  have hy2 : mk σ * ((mk l)⁻¹ * y * mk l) * (mk σ)⁻¹ ∈ Lb :=
    (Subgroup.mem_normalizer_iff.mp (hSL hsb) _).mp hy1
  have hy3 : (mk x)⁻¹ * y * mk x = (mk l)⁻¹ * y * mk l := by
    calc (mk x)⁻¹ * y * mk x = (mk x)⁻¹ * (mk l * ((mk l)⁻¹ * y * mk l) * (mk l)⁻¹) * mk x := by
          group
      _ = (mk x)⁻¹ * (mk x * ((mk l)⁻¹ * y * mk l) * (mk x)⁻¹) * mk x := by rw [act _ hy1]
      _ = (mk l)⁻¹ * y * mk l := by group
  calc mk l * mk σ * (mk l)⁻¹ * y * (mk l * mk σ * (mk l)⁻¹)⁻¹
      = mk l * (mk σ * ((mk l)⁻¹ * y * mk l) * (mk σ)⁻¹) * (mk l)⁻¹ := by group
    _ = mk x * (mk σ * ((mk l)⁻¹ * y * mk l) * (mk σ)⁻¹) * (mk x)⁻¹ := (act _ hy2).symm
    _ = mk x * (mk σ * ((mk x)⁻¹ * y * mk x) * (mk σ)⁻¹) * (mk x)⁻¹ := by rw [hy3]
    _ = mk x * mk σ * (mk x)⁻¹ * y * (mk x * mk σ * (mk x)⁻¹)⁻¹ := by group

end Inner

section Centre

variable {Y : Type*} [Group Y] [Finite Y]

theorem coprime_three_card_inf_centralizer (hY : CFSG.pCore 3 Y = ⊥) {K : Subgroup Y}
    (hK : IsSubnormal K ⊤) :
    Nat.Coprime 3 (Nat.card (K ⊓ Subgroup.centralizer (K : Set Y) : Subgroup Y)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro hdvd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hzo : orderOf (z : Y) = 3 := by rw [Subgroup.orderOf_coe, hz]
  have hW : IsSubnormal (Subgroup.zpowers (z : Y)) ⊤ :=
    isSubnormal_of_le_inf_centralizer hK ((Subgroup.zpowers_le).mpr z.2)
  have h3 : IsPGroup 3 (Subgroup.zpowers (z : Y)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hzo, pow_one]
  have h1 := cfsg_subnormal_pCoreOf_le 3 hW
  rw [pCoreOf_top_eq_pCore, hY] at h1
  have h4 : Subgroup.zpowers (z : Y) ≤ pCoreOf 3 (Subgroup.zpowers (z : Y)) :=
    normal_pGroup_le_pCoreOf 3 _ _ le_rfl (by rw [Subgroup.subgroupOf_self]; infer_instance) h3
  have hbot := le_bot_iff.mp (h4.trans h1)
  have hz1 : (z : Y) = 1 := by
    have : (z : Y) ∈ Subgroup.zpowers (z : Y) := Subgroup.mem_zpowers _
    rwa [hbot, Subgroup.mem_bot] at this
  rw [hz1, orderOf_one] at hzo
  exact absurd hzo (by norm_num)

theorem coprime_three_card_center (hY : CFSG.pCore 3 Y = ⊥) {K : Subgroup Y}
    (hK : IsSubnormal K ⊤) : Nat.Coprime 3 (Nat.card (Subgroup.center K)) := by
  have he : (Subgroup.center K).map K.subtype = K ⊓ Subgroup.centralizer (K : Set Y) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun w hw =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨w, hw⟩)⟩
    · rintro ⟨hx, hxc⟩
      exact ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun w =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc (w : Y) w.2), rfl⟩
  rw [← Subgroup.card_map_of_injective K.subtype_injective, he]
  exact coprime_three_card_inf_centralizer hY hK

omit [Finite Y] in
private theorem card_sup_mul_card_inf {A B : Subgroup Y}
    (hB : B ≤ Subgroup.normalizer (A : Set Y)) :
    Nat.card (A ⊔ B : Subgroup Y) * Nat.card (A ⊓ B : Subgroup Y) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set Y)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hc : ∀ X : Subgroup Y, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have h1 := Subgroup.relIndex_mul_card (H := A.subgroupOf N)
    (K := B.subgroupOf N ⊔ A.subgroupOf N)
  have h2 := Subgroup.relIndex_mul_card (H := A.subgroupOf N) (K := B.subgroupOf N)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : A.subgroupOf N ≤ _)] at h1
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hc _ (sup_le hAN hB), hc A hAN] at h1
  rw [hinf, hc _ (inf_le_left.trans hAN), hc B hB] at h2
  rw [← h1, ← h2]
  ring

end Centre

section Embedding

variable {G : Type} [Group G] [Finite G]

theorem nonempty_mulEquiv_barM {M Q : Subgroup G} (hQM : Q ≤ M) (hQ3 : IsPGroup 3 Q) :
    Nonempty (↥(barM M Q) ≃* ↥Q) := by
  set f : ↥Q →* ↥M ⧸ CFSG.pCore 2 ↥M :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hQM) with hf
  have hQO : Q ⊓ pCoreOf 2 M = ⊥ := inf_eq_bot_of_isPGroup Nat.prime_three hQ3 (by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num))
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have h1 : (q : G) ∈ Q ⊓ pCoreOf 2 M :=
      ⟨q.2, coe_mem_pCoreOf_two_of_mk_eq_one (Subgroup.inclusion hQM q) hq⟩
    rw [hQO, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hrange : f.range = barM M Q := by
    rw [hf, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinj).symm⟩

theorem D1PhaseThree.exists_mulEquiv_le_barM {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R) (h84 : Asc81bEightFour) (h86 : Asc81bEightSix)
    (hD2 : D1NoXBlock) (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {Q : Subgroup G} (hQ3 : IsPGroup 3 Q)
    (hQK : Q ≤ H ⊓ M) (hQL : Q ≤ L ⊔ blockCentralizer M L)
    (hQC : Q ⊓ blockCentralizer M L = ⊥) :
    ∃ U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      U ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ∧ Nonempty (↥U ≃* ↥Q) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLb
  set C := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hC
  set Qb := barM M Q with hQb
  have hQM : Q ≤ M := hQK.trans inf_le_right
  have hLM : L ≤ M := hL.le
  have hNC : Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      Subgroup.normalizer (C : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have hLbC : Lb ≤ Subgroup.normalizer (C : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.le_normalizer.trans hNC
  have hbarC : barM M (blockCentralizer M L) ≤ C := by
    rintro _ ⟨⟨c, hcM⟩, hc, rfl⟩
    exact (mem_blockCentralizer_iff ⟨c, hcM⟩).mp (Subgroup.mem_subgroupOf.mp hc)
  have hQbLC : Qb ≤ Lb ⊔ C := by
    refine (barM_mono hQL).trans ?_
    change ((L ⊔ blockCentralizer M L).subgroupOf M).map mk ≤ _
    rw [Subgroup.subgroupOf_sup hLM (blockCentralizer_le M L), Subgroup.map_sup]
    exact sup_le_sup le_rfl hbarC
  have hQbN : Qb ≤ Subgroup.normalizer (C : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    hQbLC.trans (sup_le hLbC Subgroup.le_normalizer)
  have hQbC : Qb ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨m, hm, rfl⟩, hmC⟩
    have h1 : (m : G) ∈ Q ⊓ blockCentralizer M L :=
      ⟨Subgroup.mem_subgroupOf.mp hm, (mem_blockCentralizer_iff m).mpr hmC⟩
    rw [hQC, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot, show m = 1 from Subtype.ext h1, map_one]
  set W := Qb ⊔ C with hW
  set V := W ⊓ Lb with hV
  have hVN : V ≤ Subgroup.normalizer (C : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := inf_le_right.trans hLbC
  have hWN : W ≤ Subgroup.normalizer (C : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    sup_le hQbN Subgroup.le_normalizer
  have hVC : C ⊔ V = W := by
    refine le_antisymm (sup_le le_sup_right inf_le_left) (sup_le (fun q hq => ?_) le_sup_left)
    have hq' : q ∈ ((Lb ⊔ C : Subgroup _) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := hQbLC hq
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Lb C hLbC] at hq'
    obtain ⟨l, hl, c, hc, rfl⟩ := hq'
    have hlW : l ∈ W := by
      have := W.mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right (C.inv_mem hc))
      rwa [mul_inv_cancel_right] at this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨hlW, hl⟩) (Subgroup.mem_sup_left hc)
  have hVP : V ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) := by
    rintro v ⟨hvW, hvL⟩
    have hv' : v ∈ ((Qb ⊔ C : Subgroup _) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := hvW
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Qb C hQbN] at hv'
    obtain ⟨_, ⟨x, hx, rfl⟩, c, hc, hqc⟩ := hv'
    obtain ⟨l, hl, rfl⟩ := hvL
    have hxl : mk x * (mk l)⁻¹ ∈ C := by
      rw [← hqc, mul_inv_rev, ← mul_assoc]
      exact (Subgroup.mem_normalizer_iff.mp (hQbN ⟨x, hx, rfl⟩) _).mp (C.inv_mem hc)
    exact h.mk_mem_barM_of_mul_inv_mem h84 h86 hD2 hL (hQK (Subgroup.mem_subgroupOf.mp hx))
      (Subgroup.mem_subgroupOf.mp hl) hxl
  have hWcard : Nat.card W = Nat.card Qb * Nat.card C := by
    have h1 := card_sup_mul_card_inf hQbN
    rw [inf_comm, hQbC, Subgroup.card_bot, mul_one, sup_comm] at h1
    rw [h1, mul_comm]
  have hVcard : Nat.card V = Nat.card Qb * Nat.card (C ⊓ V : Subgroup _) := by
    have h1 := card_sup_mul_card_inf hVN
    rw [hVC, hWcard] at h1
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := C)) ?_
    rw [← h1]
    ring
  have hCV : Nat.Coprime 3 (Nat.card (C ⊓ V : Subgroup _)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le
      (le_inf (inf_le_right.trans inf_le_right) inf_le_left))
      (coprime_three_card_inf_centralizer hO hL.component.2.1)
  obtain ⟨T⟩ : Nonempty (Sylow 3 ↥V) := inferInstance
  set U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := (T : Subgroup ↥V).map V.subtype with hU
  have hUV : U ≤ V := Subgroup.map_subtype_le _
  have hU3 : IsPGroup 3 U := T.isPGroup'.map _
  have hQb3 : IsPGroup 3 Qb := (hQ3.comap_subtype (K := M)).map mk
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hQb3
  have hUcard : Nat.card U = Nat.card Qb := by
    have hfac : (Nat.card V).factorization 3 = a := by
      rw [hVcard, ha, Nat.factorization_mul (pow_ne_zero _ (by norm_num)) Nat.card_pos.ne',
        Finsupp.add_apply, Nat.prime_three.factorization_pow, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hCV), add_zero]
    rw [hU, Subgroup.card_map_of_injective V.subtype_injective, Sylow.card_eq_multiplicity, hfac,
      ha]
  have hUC : U ⊓ C = ⊥ := by
    have h1 := inf_eq_bot_of_isPGroup Nat.prime_three hU3 hCV
    rw [eq_bot_iff]
    intro u hu
    have hu' : u ∈ U ⊓ (C ⊓ V) := ⟨hu.1, hu.2, hUV hu.1⟩
    rwa [h1] at hu'
  have hCW : C ≤ W := le_sup_right
  have : (C.subgroupOf W).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hCW).mpr hWN
  have hinj : ∀ {A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hAW : A ≤ W), A ⊓ C = ⊥ →
      Function.Injective ((QuotientGroup.mk' (C.subgroupOf W)).comp (Subgroup.inclusion hAW)) := by
    intro A hAW hAC
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : Subgroup.inclusion hAW a ∈ C.subgroupOf W := (QuotientGroup.eq_one_iff _).mp ha
    have h2 : (a : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ A ⊓ C := ⟨a.2, h1⟩
    rw [hAC, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hcardQ : Nat.card (↥W ⧸ C.subgroupOf W) = Nat.card Qb := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (C.subgroupOf W)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCW).toEquiv, hWcard] at h1
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).symm
  have hbU := (hinj (hUV.trans inf_le_left) hUC).bijective_of_nat_card_le (by rw [hcardQ, hUcard])
  have hbQ := (hinj (le_sup_left : Qb ≤ W) hQbC).bijective_of_nat_card_le hcardQ.le
  exact ⟨U, hUV.trans hVP, ⟨((MulEquiv.ofBijective _ hbU).trans
    (MulEquiv.ofBijective _ hbQ).symm).trans (nonempty_mulEquiv_barM hQM hQ3).some⟩⟩

theorem D1PhaseThree.exists_isElemAbelian_le_barM {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R) (h84 : Asc81bEightFour) (h86 : Asc81bEightSix)
    (hD2 : D1NoXBlock) (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {Q : Subgroup G} (hQ : IsElemAbelian 3 Q)
    (hQK : Q ≤ H ⊓ M) (hQL : Q ≤ L ⊔ blockCentralizer M L)
    (hQC : Q ⊓ blockCentralizer M L = ⊥) :
    ∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      E ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ∧ IsElemAbelian 3 E ∧
        Nat.card E = Nat.card Q := by
  have hQ3 : IsPGroup 3 Q := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hQ.2 x x.2)⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := h.exists_mulEquiv_le_barM h84 h86 hD2 hO hL hQ3 hQK hQL hQC
  refine ⟨E, hE, ⟨isMulCommutative_iff.mpr fun a b => e.injective ?_, fun x hx => ?_⟩,
    Nat.card_congr e.toEquiv⟩
  · rw [map_mul, map_mul]
    exact (isMulCommutative_iff.mp hQ.1) _ _
  · have h1 : e ⟨x, hx⟩ ^ 3 = 1 := Subtype.ext (hQ.2 _ (e ⟨x, hx⟩).2)
    rw [← map_pow, ← e.map_one] at h1
    exact congrArg Subtype.val (e.injective h1)

end Embedding

end CFSG.AGLEmbedding
