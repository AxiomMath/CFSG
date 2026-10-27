module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseL
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLCore
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiPartnerM1

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore perfectCore_mono le_perfectCore_of_perfect perfectCore_le
  perfectCore_perfect map_perfectCore)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)

local instance f4PilotXiCaseLProofNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

section Torus


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {kL : Type} [Field kL] [Finite kL]
  [CharP kL 2]

theorem exists_torus_rootSL2_of_conj (hq : 4 ≤ Nat.card kL) (e : L ≃* adjointGroup .F4 kL)
    {w : G} (hwL : w ∈ L) (c : adjointGroup .F4 kL) (i : Fin (Tag.rank .F4)) {a : kL}
    (ha : a ≠ 0)
    (hcw : ((c * e ⟨w, hwL⟩ * c⁻¹ : adjointGroup .F4 kL) : ModGL .F4 kL) =
      pinnedX .F4 kL (Pi.single i 1) a) :
    ∃ T J' : Subgroup G, T ≤ L ∧ T ≤ centralizer ({w} : Set G) ∧
      Nat.card T = (Nat.card kL - 1) ^ 3 ∧
      (∀ y ∈ T, ∃ d : adjointGroup .F4 kL, (d : ModGL .F4 kL) ∈ leviTorus kL {i} ∧
        y = ((e.symm (c⁻¹ * d * c) : L) : G)) ∧
      J' ≤ L ∧ w ∈ J' ∧ (∃ y ∈ J', y * w ≠ w * y) ∧ Nat.card J' = Nat.card (SL2 kL) ∧
      J' ≤ centralizerPerfectCore T ∧
      centralizerPerfectCore T =
        (pieceCore e {i}).map (MulAut.conj ((e.symm c⁻¹ : L) : G)).toMonoidHom := by
  have h2 : (2 : kL) = 0 := CharP.cast_eq_zero kL 2
  have : Finite (ModGL .F4 kL) := finite_modGL
  set l : G := ((e.symm c⁻¹ : L) : G) with hl
  set T₀ : Subgroup G := modelToG e (leviTorus kL {i}) with hT₀
  set R : Subgroup (ModGL .F4 kL) := rootSpan .F4 kL (amalgamRoots {i}) with hR
  have hRcore := perfectCore_inf_centralizer_leviTorus hq (J := {i}) (by simp)
  have hRle : R ≤ adjointGroup .F4 kL ⊓ centralizer (leviTorus kL {i} : Set (ModGL .F4 kL)) := by
    rw [hR, ← hRcore]
    exact perfectCore_le _
  have hRperf : ⁅R, R⁆ = R := by
    rw [hR, ← hRcore]
    exact perfectCore_perfect _
  have hRsing : R = rootSubgroup .F4 kL (Pi.single i 1) ⊔ rootSubgroup .F4 kL (-Pi.single i 1) :=
    rootSpan_amalgamRoots_singleton_F4 i
  set J₀ : Subgroup G := modelToG e R with hJ₀
  have hlL : l ∈ L := (e.symm c⁻¹).2
  have hew : e ⟨w, hwL⟩ = c⁻¹ * ⟨pinnedX .F4 kL (Pi.single i 1) a,
      pinnedX_mem_adjointGroup _ _⟩ * c := by
    have h1 : c * e ⟨w, hwL⟩ * c⁻¹ = ⟨pinnedX .F4 kL (Pi.single i 1) a,
        pinnedX_mem_adjointGroup _ _⟩ := Subtype.ext hcw
    rw [← h1]
    group
  have hconj : ∀ y : adjointGroup .F4 kL, l * ((e.symm y : L) : G) * l⁻¹ =
      ((e.symm (c⁻¹ * y * c) : L) : G) := by
    intro y
    have h1 : e.symm c⁻¹ * e.symm y * (e.symm c⁻¹)⁻¹ = e.symm (c⁻¹ * y * c) := by
      rw [← map_inv, inv_inv, ← map_mul, ← map_mul]
    rw [← h1, L.coe_mul, L.coe_mul, L.coe_inv]
  have hmemT₀ : ∀ y, y ∈ T₀.map (MulAut.conj l).toMonoidHom ↔ ∃ d : adjointGroup .F4 kL,
      (d : ModGL .F4 kL) ∈ leviTorus kL {i} ∧ y = ((e.symm (c⁻¹ * d * c) : L) : G) := by
    intro y
    simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨_, hz, rfl⟩
      obtain ⟨d, hd, rfl⟩ := (mem_modelToG e).1 hz
      exact ⟨d, hd, hconj d⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨_, symm_mem_modelToG e hd, hconj d⟩
  have hmemJ₀ : ∀ y : adjointGroup .F4 kL, (y : ModGL .F4 kL) ∈ R →
      ((e.symm (c⁻¹ * y * c) : L) : G) ∈ J₀.map (MulAut.conj l).toMonoidHom := by
    intro y hy
    exact ⟨_, symm_mem_modelToG e hy, hconj y⟩
  refine ⟨T₀.map (MulAut.conj l).toMonoidHom, J₀.map (MulAut.conj l).toMonoidHom, ?_, ?_, ?_,
    fun y hy => (hmemT₀ y).1 hy, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨z, hz, rfl⟩
    exact mul_mem (mul_mem hlL (modelToG_le e _ hz)) (inv_mem hlL)
  ·
    intro y hy
    obtain ⟨d, hd, rfl⟩ := (hmemT₀ y).1 hy
    obtain ⟨b, hb, hbd⟩ := mem_leviTorus.1 hd
    rw [mem_centralizer_singleton_iff]
    have hdx : d * ⟨pinnedX .F4 kL (Pi.single i 1) a, pinnedX_mem_adjointGroup _ _⟩ =
        ⟨pinnedX .F4 kL (Pi.single i 1) a, pinnedX_mem_adjointGroup _ _⟩ * d := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hbd]
      have h1 := rootDiagUnit_conj_pinnedX b (isRoot_single .F4 i) a
      rw [rootChar_single_one, hb i (Finset.mem_singleton_self i), Units.val_one, one_mul] at h1
      calc rootDiagUnit .F4 b * pinnedX .F4 kL (Pi.single i 1) a =
          rootDiagUnit .F4 b * pinnedX .F4 kL (Pi.single i 1) a * (rootDiagUnit .F4 b)⁻¹ *
            rootDiagUnit .F4 b := by group
        _ = pinnedX .F4 kL (Pi.single i 1) a * rootDiagUnit .F4 b := by rw [h1]
    have hw' : w = ((e.symm (e ⟨w, hwL⟩) : L) : G) := by rw [MulEquiv.symm_apply_apply]
    conv_rhs => rw [hw']
    conv_lhs => rw [hw']
    rw [← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul, hew]
    congr 2
    calc c⁻¹ * d * c * (c⁻¹ * ⟨pinnedX .F4 kL (Pi.single i 1) a, pinnedX_mem_adjointGroup _ _⟩ * c) =
        c⁻¹ * (d * ⟨pinnedX .F4 kL (Pi.single i 1) a, pinnedX_mem_adjointGroup _ _⟩) * c := by group
      _ = c⁻¹ * (⟨pinnedX .F4 kL (Pi.single i 1) a, pinnedX_mem_adjointGroup _ _⟩ * d) * c := by
          rw [hdx]
      _ = c⁻¹ * ⟨pinnedX .F4 kL (Pi.single i 1) a, pinnedX_mem_adjointGroup _ _⟩ * c *
          (c⁻¹ * d * c) := by group
  ·
    rw [card_map_of_injective (MulAut.conj l).injective, hT₀, modelToG,
      card_map_of_injective L.subtype_injective, card_map_of_injective e.symm.injective,
      card_subgroupOf_of_le (leviTorus_le_adjointGroup _), natCard_leviTorus_singleton]
  ·
    rintro _ ⟨z, hz, rfl⟩
    exact mul_mem (mul_mem hlL (modelToG_le e _ hz)) (inv_mem hlL)
  ·
    have hx : pinnedX .F4 kL (Pi.single i 1) a ∈ R := by
      rw [hRsing]
      exact mem_sup_left (Subgroup.subset_closure ⟨a, rfl⟩)
    have h1 := hmemJ₀ ⟨_, pinnedX_mem_adjointGroup _ _⟩ hx
    rw [← hew, MulEquiv.symm_apply_apply] at h1
    exact h1
  ·
    have hy : pinnedX .F4 kL (-Pi.single i 1) 1 ∈ R := by
      rw [hRsing]
      exact mem_sup_right (Subgroup.subset_closure ⟨1, rfl⟩)
    refine ⟨_, hmemJ₀ ⟨_, pinnedX_mem_adjointGroup _ _⟩ hy, fun h => ?_⟩
    have hw' : w = ((e.symm (e ⟨w, hwL⟩) : L) : G) := by rw [MulEquiv.symm_apply_apply]
    rw [hw', ← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul, hew] at h
    have h1 := e.symm.injective (Subtype.ext h)
    have h2 : (⟨pinnedX .F4 kL (-Pi.single i 1) 1, pinnedX_mem_adjointGroup _ _⟩ :
        adjointGroup .F4 kL) * ⟨pinnedX .F4 kL (Pi.single i 1) a, pinnedX_mem_adjointGroup _ _⟩ =
        ⟨pinnedX .F4 kL (Pi.single i 1) a, pinnedX_mem_adjointGroup _ _⟩ *
          ⟨pinnedX .F4 kL (-Pi.single i 1) 1, pinnedX_mem_adjointGroup _ _⟩ := by
      have h3 : c * (c⁻¹ * ⟨pinnedX .F4 kL (-Pi.single i 1) 1, pinnedX_mem_adjointGroup _ _⟩ * c *
          (c⁻¹ * ⟨pinnedX .F4 kL (Pi.single i 1) a, pinnedX_mem_adjointGroup _ _⟩ * c)) * c⁻¹ =
          c * (c⁻¹ * ⟨pinnedX .F4 kL (Pi.single i 1) a, pinnedX_mem_adjointGroup _ _⟩ * c *
          (c⁻¹ * ⟨pinnedX .F4 kL (-Pi.single i 1) 1, pinnedX_mem_adjointGroup _ _⟩ * c)) * c⁻¹ := by
        rw [h1]
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using h3
    exact pinnedX_mul_pinnedX_neg_ne (isRoot_single .F4 i) ha
      (congrArg Subtype.val h2).symm
  ·
    rw [card_map_of_injective (MulAut.conj l).injective, hJ₀, modelToG,
      card_map_of_injective L.subtype_injective, card_map_of_injective e.symm.injective,
      card_subgroupOf_of_le (fun x hx => (hRle hx).1), hRsing,
      natCard_rootSubgroup_sup_neg (isRoot_single .F4 i), natCard_SL2_eq]
  ·
    refine le_centralizerPerfectCore ?_ ?_
    · rw [← map_commutator, hJ₀, ← modelToG_commutator e (fun x hx => (hRle hx).1)
        (fun x hx => (hRle hx).1), hRperf]
    · have hc0 : J₀ ≤ centralizer (T₀ : Set G) :=
        modelToG_le_centralizer e (fun x hx => (hRle hx).2)
      rw [← map_centralizer_mulEquiv]
      exact map_mono hc0
  ·
    rw [← map_centralizerPerfectCore]
    rfl

end Torus

section Helpers

variable {G : Type*} [Group G] [Finite G]

theorem exists_le_natCard_eq_two_pow {Λ L : Subgroup G} (hΛL : Λ ≤ L) {n R : ℕ} (hR : Odd R)
    (hL : Nat.card L = 2 ^ n * R) (hΛ : 2 ^ n ∣ Nat.card Λ) :
    ∃ U : Subgroup G, U ≤ Λ ∧ Nat.card U = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 Λ) := inferInstance
  refine ⟨(P : Subgroup Λ).map Λ.subtype, map_subtype_le _, ?_⟩
  rw [card_map_of_injective Λ.subtype_injective]
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).1 P.isPGroup'
  have h1 : 2 ^ n ∣ 2 ^ m := hm ▸ P.pow_dvd_card_of_pow_dvd_card hΛ
  have h2 : 2 ^ m ∣ 2 ^ n * R := by
    rw [← hm, ← hL, ← card_map_of_injective Λ.subtype_injective]
    exact Subgroup.card_dvd_of_le ((map_subtype_le _).trans hΛL)
  have hc : Nat.Coprime (2 ^ m) R := Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hR)
  have h3 := hc.dvd_of_dvd_mul_right h2
  rw [hm, le_antisymm ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h3)
    ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1)]

omit [Finite G] in
theorem natCard_map_of_forall_eq_one {Y : Type*} [Group Y] (ε : G →* Y) {H : Subgroup G}
    (h : ∀ a ∈ H, ε a = 1 → a = 1) : Nat.card (H.map ε) = Nat.card H := by
  have hinj : Function.Injective (ε.comp H.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (h a a.2 ha)
  have e : H.map ε = (ε.comp H.subtype).range := by
    rw [← MonoidHom.map_range, Subgroup.range_subtype]
  rw [e]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

theorem map_subtype_perfectCore_centralizer_subgroupOf {G₀ T : Subgroup G} (hT : T ≤ G₀)
    (hE : centralizerPerfectCore T ≤ G₀) :
    (perfectCore (centralizer ((T.subgroupOf G₀ : Subgroup G₀) : Set G₀))).map G₀.subtype =
      centralizerPerfectCore T := by
  apply le_antisymm
  · refine le_centralizerPerfectCore ?_ ?_
    · rw [← map_commutator, perfectCore_perfect]
    · rintro _ ⟨y, hy, rfl⟩
      rw [mem_centralizer_iff]
      intro s hs
      have h1 := mem_centralizer_iff.1 (perfectCore_le _ hy) ⟨s, hT hs⟩ hs
      exact congrArg Subtype.val h1
  · intro g hg
    have hsub : (centralizerPerfectCore T).subgroupOf G₀ ≤
        perfectCore (centralizer ((T.subgroupOf G₀ : Subgroup G₀) : Set G₀)) := by
      refine le_perfectCore_of_perfect ?_
        (commutator_subgroupOf_eq hE (perfectCore_perfect _))
      intro y hy
      rw [mem_centralizer_iff]
      intro s hs
      apply Subtype.ext
      have h1 := mem_centralizer_iff.1 (centralizerPerfectCore_le_centralizer T
        (mem_subgroupOf.1 hy)) s (mem_subgroupOf.1 hs)
      exact h1
    exact ⟨⟨g, hE hg⟩, hsub (mem_subgroupOf.2 hg), rfl⟩

omit [Finite G] in
theorem coe_symm_mem_normalizer_of_mem_normalizer_map {L : Subgroup G} {X : Type*} [Group X]
    (e : L ≃* X) {U : Subgroup G} (hUL : U ≤ L) {n : X}
    (hn : n ∈ normalizer (((U.subgroupOf L).map e.toMonoidHom : Subgroup X) : Set X)) :
    ((e.symm n : L) : G) ∈ normalizer (U : Set G) := by
  have key : ∀ g : L, (g : G) ∈ U ↔ e g ∈ (U.subgroupOf L).map e.toMonoidHom := fun g => by
    constructor
    · intro hg
      exact ⟨g, mem_subgroupOf.2 hg, rfl⟩
    · rintro ⟨g', hg', hgg'⟩
      have : g' = g := e.injective hgg'
      rw [← this]
      exact mem_subgroupOf.1 hg'
  have hnL : ((e.symm n : L) : G) ∈ L := (e.symm n).2
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have hgL : g ∈ L := hUL hg
    have h1 := (key ⟨g, hgL⟩).1 hg
    have h2 := (mem_normalizer_iff.1 hn _).1 h1
    have h3 : n * e ⟨g, hgL⟩ * n⁻¹ = e (e.symm n * ⟨g, hgL⟩ * (e.symm n)⁻¹) := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [h3] at h2
    have h4 := (key _).2 h2
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h4
  · intro hg
    have hgL : g ∈ L := by
      have hC := hUL hg
      have e1 : g = ((e.symm n : L) : G)⁻¹ * (((e.symm n : L) : G) * g * ((e.symm n : L) : G)⁻¹) *
          ((e.symm n : L) : G) := by group
      rw [e1]
      exact mul_mem (mul_mem (inv_mem hnL) hC) hnL
    have h1 : (((e.symm n * ⟨g, hgL⟩ * (e.symm n)⁻¹ : L)) : G) ∈ U := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hg
    have h2 := (key _).1 h1
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
    have h3 := (mem_normalizer_iff.1 hn _).2 h2
    exact (key _).2 h3

end Helpers

section Core


theorem centralizerPerfectCore_le_of_caseL_model {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (e : L ≃* adjointGroup .F4 K) (hZL : center L = ⊥) {t : G}
    (htC : t ∈ centralizer (L : Set G))
    {KC : Type} [Field KC] [Finite KC] {C J : Subgroup (ModGL TwistTag.E6.tag KC)}
    {η : MulAut C} {k : Type} [Field k] [Finite k] [CharP k 2] (hk : Nat.card k = 2 ^ f)
    {eJ : J ≃* adjointGroup .F4 k} {A : Subgroup KCˣ} {x : C}
    (hmod : XiCaseLModel C J η eJ A x)
    (e₀ : pieceSpan e ⧸ center (pieceSpan e) ≃* C)
    (htN : t ∈ normalizer (pieceSpan e : Set G)) {ψ : MulAut C}
    (hψ : ψ * normalizerQuotMulAut e₀ ⟨t, htN⟩ * ψ⁻¹ = η)
    {w : G} (hwL : w ∈ L) (hw1 : w ≠ 1)
    (htwN : t * w ∈ normalizer (pieceSpan e : Set G)) {φ' : MulAut C}
    (hφ' : φ' * normalizerQuotMulAut e₀ ⟨t * w, htwN⟩ * φ'⁻¹ = MulAut.conj x * η)
    {U Λ T Jw : Subgroup G} (hUL' : U ≤ L) (hUcard : Nat.card U = 2 ^ (24 * f))
    (hwU : U ≤ centralizer ({w} : Set G)) (hΛL : Λ ≤ L) (hΛw : Λ ≤ centralizer ({w} : Set G))
    (hN₃Λ : (2 ^ f) ^ 24 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1)) ∣
      Nat.card Λ)
    (hTL : T ≤ L) (hTU : T ≤ normalizer (U : Set G)) (hTw : T ≤ centralizer ({w} : Set G))
    (hTcard : Nat.card T = (Nat.card K - 1) ^ 3) (hJwL : Jw ≤ L)
    (hJwcard : Nat.card Jw = Nat.card (SL2 K)) (hJwE : Jw ≤ centralizerPerfectCore T)
    (hETG₀ : centralizerPerfectCore T ≤ pieceSpan e) :
    centralizerPerfectCore T ≤ Jw := by
  have hf1 : 1 ≤ f := by omega
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hqk : 4 ≤ Nat.card k := by rw [hk, ← hK]; exact hq
  have : Finite (ModGL TwistTag.E6.tag KC) := finite_modGL
  have : Finite C := Finite.of_injective _ Subtype.val_injective
  have hLG₀ : L ≤ pieceSpan e := le_pieceSpan hq e
  have hTodd : Odd (Nat.card T) := by
    rw [hTcard, hK]
    have h1 := odd_two_pow_pow_sub_one hf1 (j := 1) le_rfl
    rw [pow_one] at h1
    exact h1.pow
  set wL : L := ⟨w, hwL⟩ with hwLdef
  have hwL1 : wL ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
  set UL : Subgroup L := U.subgroupOf L with hULdef
  have hUL : Nat.card UL = 2 ^ (24 * f) := by
    rw [hULdef, card_subgroupOf_of_le hUL', hUcard]
  have hwUL : wL ∈ centralizer (UL : Set L) := by
    rw [mem_centralizer_iff]
    intro u hu
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hwU (mem_subgroupOf.1 hu)))
  set ΛL : Subgroup L := Λ.subgroupOf L with hΛLdef
  have hΛLw : ΛL ≤ centralizer ({wL} : Set L) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hΛw (mem_subgroupOf.1 hy)))
  have hdivL : (2 ^ f) ^ 24 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1)) ∣
      Nat.card ΛL := by
    rw [hΛLdef, card_subgroupOf_of_le hΛL]
    exact hN₃Λ

  set ε : pieceSpan e →* ModGL TwistTag.E6.tag KC := quotMap e₀ ψ with hεdef
  have hεcoe : ∀ y : pieceSpan e, (⟨ε y, quotMap_mem e₀ ψ y⟩ : C) =
      ψ (e₀ (QuotientGroup.mk' (center (pieceSpan e)) y)) := fun y => rfl
  have hεker : ∀ y : pieceSpan e, ε y = 1 → y ∈ center (pieceSpan e) := by
    intro y hy
    have h1 : ψ (e₀ (QuotientGroup.mk' (center (pieceSpan e)) y)) = 1 := by
      rw [← hεcoe]
      exact Subtype.ext hy
    rw [← map_one ψ, ← map_one e₀] at h1
    exact (QuotientGroup.eq_one_iff y).1 (e₀.injective (ψ.injective h1))
  have hLZ : ∀ l : L, (⟨l, hLG₀ l.2⟩ : pieceSpan e) ∈ center (pieceSpan e) → l = 1 := by
    intro l hz
    have h1 : l ∈ center L := mem_center_iff.2 fun m => by
      have h2 := congrArg Subtype.val (mem_center_iff.1 hz ⟨m, hLG₀ m.2⟩)
      exact Subtype.ext h2
    rw [hZL, mem_bot] at h1
    exact h1
  have hεJ : ∀ l : L, ε ⟨l, hLG₀ l.2⟩ ∈ J := by
    intro l
    have hfix : η ⟨ε ⟨l, hLG₀ l.2⟩, quotMap_mem e₀ ψ _⟩ = ⟨ε ⟨l, hLG₀ l.2⟩, quotMap_mem e₀ ψ _⟩ := by
      rw [hεcoe, ← hψ]
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
      rw [normalizerQuotMulAut_apply]
      congr 3
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      change t * l * t⁻¹ = l
      rw [(mem_centralizer_iff.1 htC l l.2).symm, mul_inv_cancel_right]
    exact (hmod.eta_eq_iff _).1 hfix
  set β₀ : L →* adjointGroup .F4 k := eJ.toMonoidHom.comp
    ((ε.comp (Subgroup.inclusion hLG₀)).codRestrict J fun l => hεJ l) with hβ₀def
  have hβ₀ : ∀ l : L, (β₀ l : adjointGroup .F4 k) = eJ ⟨ε ⟨l, hLG₀ l.2⟩, hεJ l⟩ := fun l => rfl
  have hβ₀inj : Function.Injective β₀ := by
    rw [injective_iff_map_eq_one]
    intro l hl
    rw [hβ₀] at hl
    have h1 : (⟨ε ⟨l, hLG₀ l.2⟩, hεJ l⟩ : J) = 1 := eJ.injective (hl.trans (map_one eJ).symm)
    exact hLZ l (hεker _ (congrArg Subtype.val h1))
  set TL : Subgroup L := T.subgroupOf L with hTLdef
  have hTLU : TL ≤ normalizer (UL : Set L) := by
    intro y hy
    rw [mem_normalizer_iff]
    intro u
    rw [hULdef, mem_subgroupOf, mem_subgroupOf]
    have h1 := mem_normalizer_iff.1 (hTU (mem_subgroupOf.1 hy)) (u : G)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1
  have hTLw : TL ≤ centralizer ({wL} : Set L) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hTw (mem_subgroupOf.1 hy)))
  have hTLodd : Odd (Nat.card TL) := by
    rw [hTLdef, card_subgroupOf_of_le hTL]
    exact hTodd
  obtain ⟨c', i', a', hi', ha', hcw', hcS', -⟩ := exists_conj_leviTorus_of_injective hf1 hk
    hβ₀inj hUL hwUL hwL1 hΛLw hdivL hTLU hTLw hTLodd
  have hsurj : ∀ d : adjointGroup .F4 k, (d : ModGL .F4 k) ∈ leviTorus k {i'} →
      ∃ s ∈ TL, c' * β₀ s * c'⁻¹ = d := by
    set θ : TL →* adjointGroup .F4 k := (MulAut.conj c').toMonoidHom.comp (β₀.comp TL.subtype)
      with hθ
    have hθinj : Function.Injective θ := fun a b hab =>
      Subtype.ext (hβ₀inj ((MulAut.conj c').injective hab))
    have hθle : θ.range ≤ (leviTorus k {i'}).subgroupOf (adjointGroup .F4 k) := by
      rintro _ ⟨s, rfl⟩
      rw [mem_subgroupOf]
      exact hcS' s s.2
    have hθcard : Nat.card θ.range = Nat.card ((leviTorus k {i'}).subgroupOf
        (adjointGroup .F4 k)) := by
      rw [Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv.symm, hTLdef,
        card_subgroupOf_of_le hTL, hTcard, card_subgroupOf_of_le (leviTorus_le_adjointGroup _),
        natCard_leviTorus_singleton, hK, hk]
    have hθeq := Subgroup.eq_of_le_of_card_ge hθle hθcard.ge
    intro d hd
    have hd' : d ∈ θ.range := by
      rw [hθeq, mem_subgroupOf]
      exact hd
    obtain ⟨s, hs⟩ := hd'
    exact ⟨s, s.2, hs⟩
  rcases hi' with rfl | rfl
  ·
    have hfixP : ∀ g ∈ C, diagramMap TwistTag.E6 KC * g * (diagramMap TwistTag.E6 KC)⁻¹ = g →
        g ∈ J := fun g hg hPg =>
      (hmod.eta_eq_iff ⟨g, hg⟩).1 (Subtype.ext ((hmod.eta_apply ⟨g, hg⟩).trans hPg))
    set T₀ : Subgroup (pieceSpan e) := T.subgroupOf (pieceSpan e) with hT₀
    set S : Subgroup (ModGL TwistTag.E6.tag KC) := T₀.map ε with hSdef
    have hSJ : S ≤ J := by
      rintro _ ⟨y, hy, rfl⟩
      exact hεJ ⟨y, hTL (mem_subgroupOf.1 hy)⟩
    have hS : ∀ d : adjointGroup .F4 k, (d : ModGL .F4 k) ∈ leviTorus k {1} →
        ∃ (s : ModGL TwistTag.E6.tag KC) (hs : s ∈ S), c' * eJ ⟨s, hSJ hs⟩ * c'⁻¹ = d := by
      intro d hd
      obtain ⟨s₀, hs₀, hcs⟩ := hsurj d hd
      exact ⟨ε ⟨s₀, hLG₀ s₀.2⟩, ⟨⟨s₀, hLG₀ s₀.2⟩, mem_subgroupOf.2 (mem_subgroupOf.1 hs₀), rfl⟩,
        by rw [← hcs, hβ₀]⟩
    have hup := natCard_perfectCore_le_natCard_SL2 hqk hmod.le hmod.le_adjointGroup
      hmod.two_eq_zero hfixP eJ hmod.three_le_card hmod.coroot hSJ c' hS
    rw [hSdef, ← map_perfectCore_centralizer_quotMap e₀ ψ T₀] at hup
    set E' := perfectCore (centralizer (T₀ : Set (pieceSpan e))) with hE'
    have hE'map : E'.map (pieceSpan e).subtype = centralizerPerfectCore T :=
      map_subtype_perfectCore_centralizer_subgroupOf (hTL.trans hLG₀) hETG₀
    set Jw₀ : Subgroup (pieceSpan e) := Jw.subgroupOf (pieceSpan e) with hJw₀
    have hJw₀E' : Jw₀ ≤ E' := by
      intro y hy
      have h1 : (y : G) ∈ E'.map (pieceSpan e).subtype := by
        rw [hE'map]
        exact hJwE (mem_subgroupOf.1 hy)
      obtain ⟨y', hy', hyy'⟩ := h1
      rw [← Subtype.ext hyy']
      exact hy'
    have hJw₀card : Nat.card (Jw₀.map ε) = Nat.card (SL2 k) := by
      rw [natCard_map_of_forall_eq_one ε (fun y hy hy1 => by
        have h5 := congrArg Subtype.val (hLZ ⟨y, hJwL (mem_subgroupOf.1 hy)⟩ (hεker y hy1))
        exact Subtype.ext h5), hJw₀,
        card_subgroupOf_of_le (hJwL.trans hLG₀), hJwcard, natCard_SL2_eq, natCard_SL2_eq,
        hK, hk]
    have hmapeq : Jw₀.map ε = E'.map ε := Subgroup.eq_of_le_of_card_ge (map_mono hJw₀E')
      (by rw [hJw₀card]; exact hup)
    have hE'le : E' ≤ Jw₀ ⊔ center (pieceSpan e) := by
      intro y hy
      have h1 : ε y ∈ Jw₀.map ε := by
        rw [hmapeq]
        exact ⟨y, hy, rfl⟩
      obtain ⟨j₁, hj₁, hj₁y⟩ := h1
      have h2 : j₁⁻¹ * y ∈ center (pieceSpan e) := hεker _ (by
        rw [map_mul, map_inv, hj₁y, inv_mul_cancel])
      have h3 : y = j₁ * (j₁⁻¹ * y) := by group
      rw [h3]
      exact mul_mem (mem_sup_left hj₁) (mem_sup_right h2)
    have hE'Jw : E' ≤ Jw₀ := le_of_le_sup_center_of_perfect le_rfl hE'le (perfectCore_perfect _)
    rw [← hE'map]
    rintro _ ⟨y, hy, rfl⟩
    exact mem_subgroupOf.1 (hE'Jw hy)
  ·
    exfalso
    obtain ⟨z, hz, g₀, hg₀⟩ := hmod.short a' ha'
    have h1 : c' * β₀ wL * c'⁻¹ = eJ z := Subtype.ext (hcw'.trans hz.symm)
    set j : J := eJ.symm c'⁻¹ with hj
    have h2 : (⟨ε ⟨w, hLG₀ hwL⟩, hεJ wL⟩ : J) = j * z * j⁻¹ := by
      apply eJ.injective
      have h3 : eJ ⟨ε ⟨w, hLG₀ hwL⟩, hεJ wL⟩ = β₀ wL := (hβ₀ wL).symm
      rw [h3, map_mul, map_mul, map_inv, hj, MulEquiv.apply_symm_apply, ← h1]
      group
    have hwG₀ : w ∈ pieceSpan e := hLG₀ hwL
    have hsplit : (⟨t * w, htwN⟩ : normalizer (pieceSpan e : Set G)) =
        ⟨t, htN⟩ * ⟨w, le_normalizer hwG₀⟩ := rfl
    have hA : normalizerQuotMulAut e₀ ⟨t * w, htwN⟩ = normalizerQuotMulAut e₀ ⟨t, htN⟩ *
        MulAut.conj (e₀ (QuotientGroup.mk' (center (pieceSpan e)) ⟨w, hwG₀⟩)) := by
      rw [hsplit, map_mul, EPilot.normalizerQuotMulAut_of_mem e₀ hwG₀]
    set wC : C := ⟨ε ⟨w, hwG₀⟩, quotMap_mem e₀ ψ _⟩ with hwC
    have hwCψ : wC = ψ (e₀ (QuotientGroup.mk' (center (pieceSpan e)) ⟨w, hwG₀⟩)) := rfl
    have hηwC : η wC = wC := (hmod.eta_eq_iff wC).2 (hεJ wL)
    have hB : ψ * normalizerQuotMulAut e₀ ⟨t * w, htwN⟩ * ψ⁻¹ = MulAut.conj wC * η := by
      rw [hA]
      calc ψ * (normalizerQuotMulAut e₀ ⟨t, htN⟩ *
            MulAut.conj (e₀ (QuotientGroup.mk' (center (pieceSpan e)) ⟨w, hwG₀⟩))) * ψ⁻¹ =
          (ψ * normalizerQuotMulAut e₀ ⟨t, htN⟩ * ψ⁻¹) * (ψ *
            MulAut.conj (e₀ (QuotientGroup.mk' (center (pieceSpan e)) ⟨w, hwG₀⟩)) * ψ⁻¹) := by
            group
        _ = η * MulAut.conj wC := by rw [hψ, mulAut_conj_conj_eq, ← hwCψ]
        _ = MulAut.conj wC * η := mulAut_mul_conj_of_apply_eq hηwC
    set jC : C := ⟨j, hmod.le j.2⟩ with hjC
    set zC : C := ⟨z, hmod.le z.2⟩ with hzC
    have hwCeq : wC = jC * zC * jC⁻¹ := by
      have h3 : ε ⟨w, hLG₀ hwL⟩ = (j : ModGL TwistTag.E6.tag KC) * z *
          (j : ModGL TwistTag.E6.tag KC)⁻¹ := congrArg Subtype.val h2
      exact Subtype.ext h3
    have hηj : η jC = jC := (hmod.eta_eq_iff jC).2 j.2
    have h3 : MulAut.conj wC * η = (MulAut.conj jC * MulAut.conj g₀) * η *
        (MulAut.conj jC * MulAut.conj g₀)⁻¹ := by
      rw [hwCeq, conj_conj_mul_eta hηj, ← hg₀]
      group
    apply hmod.not_conj (φ' * ψ⁻¹ * (MulAut.conj jC * MulAut.conj g₀))
    rw [← hφ']
    have h4 : normalizerQuotMulAut e₀ ⟨t * w, htwN⟩ = ψ⁻¹ * (MulAut.conj wC * η) * ψ := by
      rw [← hB]
      group
    rw [h4, h3]
    group

theorem le_of_caseL_model_M {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) {t : G} (ht : orderOf t = 2)
    {KC : Type} [Field KC] [Finite KC] {C J : Subgroup (ModGL TwistTag.E6.tag KC)}
    {η : MulAut C} {k : Type} [Field k] [Finite k] [CharP k 2] (hk : Nat.card k = 2 ^ f)
    {eJ : J ≃* adjointGroup .F4 k} {A : Subgroup KCˣ} {x : C}
    (hmod : XiCaseLModel C J η eJ A x)
    {M : Subgroup G} (hZM : Odd (Nat.card (center M))) (eM : M ⧸ center M ≃* C)
    (htM : t ∈ normalizer (M : Set G)) {φ : MulAut C}
    (hφ : φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = MulAut.conj x * η)
    {w : G} (hwM : w ∈ M) (hwx : eM (QuotientGroup.mk' (center M) ⟨w, hwM⟩) = φ⁻¹ x)
    (hΛcard : Nat.card (perfectCore (M ⊓ centralizer ({t} : Set G))) =
      (2 ^ f) ^ 24 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1)))
    (hΛw : perfectCore (M ⊓ centralizer ({t} : Set G)) ≤ centralizer ({w} : Set G))
    (hwΛ : w ∈ perfectCore (M ⊓ centralizer ({t} : Set G)))
    {U T Jw : Subgroup G} (hUΛ : U ≤ perfectCore (M ⊓ centralizer ({t} : Set G)))
    (hUcard : Nat.card U = 2 ^ (24 * f))
    (hTΛ : T ≤ perfectCore (M ⊓ centralizer ({t} : Set G)))
    (hTU : T ≤ normalizer (U : Set G)) (hTodd : Odd (Nat.card T))
    (hETJ : centralizerPerfectCore T ≤ Jw) (hJwcard : Nat.card Jw = Nat.card (SL2 K)) :
    Jw ≤ M := by
  have hf1 : 1 ≤ f := by omega
  have hq : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Finite (ModGL TwistTag.E6.tag KC) := finite_modGL
  have : Finite C := Finite.of_injective _ Subtype.val_injective
  set Λ := perfectCore (M ⊓ centralizer ({t} : Set G)) with hΛdef
  have hΛM : Λ ≤ M := (perfectCore_le _).trans inf_le_left
  set ΛM : Subgroup M := perfectCore ((centralizer ({t} : Set G)).subgroupOf M) with hΛMdef
  have hΛsub : ΛM.map M.subtype = Λ := map_subtype_perfectCore_subgroupOf M t
  set π : M →* C := eM.toMonoidHom.comp (QuotientGroup.mk' (center M)) with hπ
  have hperfA := fixSubgroup_perfect_of_conj hφ hmod.fix_perfect
  have hmapΛ : ΛM.map π = E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩) :=
    map_perfectCore_subgroupOf_centralizer_eq hZM eM ht htM hperfA
  have hfixmap := map_eqLocus_eq_of_conj hφ
  have hfixA : Nat.card (E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩)) =
      Nat.card (perfectCore (M ⊓ centralizer ({t} : Set G))) := by
    rw [hΛcard, ← card_map_of_injective (f := φ.toMonoidHom) φ.injective]
    change Nat.card (((normalizerQuotMulAut eM ⟨t, htM⟩).toMonoidHom.eqLocus
      (MonoidHom.id C)).map φ.toMonoidHom) = _
    rw [hfixmap]
    change Nat.card (E6Pilot.fixSubgroup (MulAut.conj x * η)) = _
    rw [hmod.card_fix, natCard_centralizer_yRep_of_ne_tu hf1 hk (by decide)]
  have hΛMcard : Nat.card ΛM = Nat.card Λ := by
    rw [← hΛsub, card_map_of_injective M.subtype_injective]
  have hπinj : Function.Injective (π.comp ΛM.subtype) := by
    refine injective_of_natCard_range _ ?_
    rw [← MonoidHom.map_range, Subgroup.range_subtype, hmapΛ, hfixA, hΛMcard]
  have hΛΛM : ∀ y : Λ, (⟨y, hΛM y.2⟩ : M) ∈ ΛM := by
    intro y
    have h1 : (y : G) ∈ ΛM.map M.subtype := by rw [hΛsub]; exact y.2
    obtain ⟨y', hy', hyy'⟩ := h1
    have h2 : y' = ⟨y, hΛM y.2⟩ := Subtype.ext hyy'
    rw [← h2]
    exact hy'
  set ι : M →* ModGL TwistTag.E6.tag KC := quotMap eM φ with hιdef
  have hιJ : ∀ y : Λ, ι ⟨y, hΛM y.2⟩ ∈ J := by
    intro y
    have h1 : π ⟨y, hΛM y.2⟩ ∈ E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩) := by
      rw [← hmapΛ]
      exact ⟨_, hΛΛM y, rfl⟩
    have h2 : φ (π ⟨y, hΛM y.2⟩) ∈ E6Pilot.fixSubgroup (MulAut.conj x * η) := by
      change φ (π ⟨y, hΛM y.2⟩) ∈ ((MulAut.conj x * η).toMonoidHom.eqLocus (MonoidHom.id C))
      rw [← hfixmap]
      exact ⟨_, h1, rfl⟩
    exact hmod.fix_le _ h2
  set β₁ : Λ →* adjointGroup .F4 k := eJ.toMonoidHom.comp
    ((ι.comp (Subgroup.inclusion hΛM)).codRestrict J fun y => hιJ y) with hβ₁def
  have hβ₁ : ∀ y : Λ, β₁ y = eJ ⟨ι ⟨y, hΛM y.2⟩, hιJ y⟩ := fun y => rfl
  have hβ₁inj : Function.Injective β₁ := by
    intro y y' h
    rw [hβ₁, hβ₁] at h
    have h1 := congrArg Subtype.val (eJ.injective h)
    have h2 : φ (π ⟨y, hΛM y.2⟩) = φ (π ⟨y', hΛM y'.2⟩) := Subtype.ext h1
    have h3 := hπinj (a₁ := ⟨_, hΛΛM y⟩) (a₂ := ⟨_, hΛΛM y'⟩) (φ.injective h2)
    exact Subtype.ext (congrArg (fun z : ΛM => ((z : M) : G)) h3)
  have hw1 : (⟨w, hwΛ⟩ : Λ) ≠ 1 := by
    intro h
    have hw : w = 1 := congrArg Subtype.val h
    subst hw
    apply hmod.not_conj 1
    have h1 : eM (QuotientGroup.mk' (center M) (1 : M)) = φ⁻¹ x := hwx
    rw [map_one, map_one] at h1
    have h2 := congrArg φ h1
    rw [map_one, MulAut.inv_apply, MulEquiv.apply_symm_apply] at h2
    rw [← h2, map_one, one_mul]
    group
  set UΛ : Subgroup Λ := U.subgroupOf Λ with hUΛdef
  have hUΛcard : Nat.card UΛ = 2 ^ (24 * f) := by
    rw [hUΛdef, card_subgroupOf_of_le hUΛ, hUcard]
  have hwUΛ : (⟨w, hwΛ⟩ : Λ) ∈ centralizer (UΛ : Set Λ) := by
    rw [mem_centralizer_iff]
    intro u hu
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hΛw (hUΛ (mem_subgroupOf.1 hu))))
  have htop : (⊤ : Subgroup Λ) ≤ centralizer ({(⟨w, hwΛ⟩ : Λ)} : Set Λ) := by
    intro y _
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hΛw y.2))
  have hdiv : (2 ^ f) ^ 24 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1)) ∣
      Nat.card (⊤ : Subgroup Λ) := by
    rw [Subgroup.card_top, ← hΛcard]
  set TΛ : Subgroup Λ := T.subgroupOf Λ with hTΛdef
  have hTΛU : TΛ ≤ normalizer (UΛ : Set Λ) := by
    intro y hy
    rw [mem_normalizer_iff]
    intro u
    rw [hUΛdef, mem_subgroupOf, mem_subgroupOf]
    have h1 := mem_normalizer_iff.1 (hTU (mem_subgroupOf.1 hy)) (u : G)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1
  have hTΛw : TΛ ≤ centralizer ({(⟨w, hwΛ⟩ : Λ)} : Set Λ) := fun y _ => htop (mem_top y)
  have hTΛodd : Odd (Nat.card TΛ) := by
    rw [hTΛdef, card_subgroupOf_of_le hTΛ]
    exact hTodd
  obtain ⟨c'', i'', -, -, -, -, hcS'', -⟩ := exists_conj_leviTorus_of_injective hf1 hk hβ₁inj
    hUΛcard hwUΛ hw1 htop hdiv hTΛU hTΛw hTΛodd
  set TM : Subgroup M := T.subgroupOf M with hTMdef
  set S : Subgroup (ModGL TwistTag.E6.tag KC) := TM.map ι with hSdef
  have hSJ : S ≤ J := by
    rintro _ ⟨y, hy, rfl⟩
    exact hιJ ⟨y, hTΛ (mem_subgroupOf.1 hy)⟩
  have hS : ∀ (s : ModGL TwistTag.E6.tag KC) (hs : s ∈ S),
      ((c'' * eJ ⟨s, hSJ hs⟩ * c''⁻¹ : adjointGroup .F4 k) : ModGL .F4 k) ∈ leviTorus k {i''} := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hcS'' ⟨y, hTΛ (mem_subgroupOf.1 hy)⟩ (mem_subgroupOf.2 (mem_subgroupOf.1 hy))
    rw [hβ₁] at h1
    exact h1
  have hlow := natCard_SL2_le_perfectCore_of_le_leviTorus hq hmod.le eJ hSJ c'' i'' hS
  rw [hSdef, ← map_perfectCore_centralizer_quotMap eM φ TM] at hlow
  have hlow' := hlow.trans (Nat.le_of_dvd Nat.card_pos (natCard_map_dvd _ _))
  set F : Subgroup G := (perfectCore (centralizer (TM : Set M))).map M.subtype with hFdef
  have hFE : F ≤ centralizerPerfectCore T := by
    refine le_centralizerPerfectCore ?_ ?_
    · rw [hFdef, ← map_commutator, perfectCore_perfect]
    · rintro _ ⟨y, hy, rfl⟩
      rw [mem_centralizer_iff]
      intro s hs
      have h1 := mem_centralizer_iff.1 (perfectCore_le _ hy) ⟨s, hΛM (hTΛ hs)⟩ hs
      exact congrArg Subtype.val h1
  have hFJ : F ≤ Jw := hFE.trans hETJ
  have hFcard : Nat.card Jw ≤ Nat.card F := by
    have e1 : Nat.card F = Nat.card (perfectCore (centralizer (TM : Set M))) := by
      rw [hFdef, card_map_of_injective M.subtype_injective]
    have e2 : Nat.card Jw = Nat.card (SL2 k) := by
      rw [hJwcard, natCard_SL2_eq, natCard_SL2_eq, hK, hk]
    rw [e1, e2]
    exact hlow'
  have hFeq : F = Jw := Subgroup.eq_of_le_of_card_ge hFJ hFcard
  rw [← hFeq]
  exact map_subtype_le _

theorem false_of_caseL_model {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type}
    [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (e : L ≃* adjointGroup .F4 K) (hZL : center L = ⊥) {t : G} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (L : Set G))
    {KC : Type} [Field KC] [Finite KC] {C J : Subgroup (ModGL TwistTag.E6.tag KC)}
    {η : MulAut C} {k : Type} [Field k] [Finite k] [CharP k 2] (hk : Nat.card k = 2 ^ f)
    {eJ : J ≃* adjointGroup .F4 k} {A : Subgroup KCˣ} {x : C}
    (hmod : XiCaseLModel C J η eJ A x)
    (e₀ : pieceSpan e ⧸ center (pieceSpan e) ≃* C)
    (htN : t ∈ normalizer (pieceSpan e : Set G)) {ψ : MulAut C}
    (hψ : ψ * normalizerQuotMulAut e₀ ⟨t, htN⟩ * ψ⁻¹ = η)
    {M : Subgroup G} (hZM : Odd (Nat.card (center M))) (eM : M ⧸ center M ≃* C)
    (htM : t ∈ normalizer (M : Set G)) {φ : MulAut C}
    (hφ : φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = MulAut.conj x * η)
    (hΛL : perfectCore (M ⊓ centralizer ({t} : Set G)) ≤ L)
    {w : G} (hwM : w ∈ M) (hwL : w ∈ L)
    (hwx : eM (QuotientGroup.mk' (center M) ⟨w, hwM⟩) = φ⁻¹ x)
    (hwΛ : w ∈ perfectCore (M ⊓ centralizer ({t} : Set G)))
    (hwc : ∀ c ∈ M ⊓ centralizer ({t} : Set G), c * w = w * c)
    (htwN : t * w ∈ normalizer (pieceSpan e : Set G)) {φ' : MulAut C}
    (hφ' : φ' * normalizerQuotMulAut e₀ ⟨t * w, htwN⟩ * φ'⁻¹ = MulAut.conj x * η) :
    False := by
  have hf1 : 1 ≤ f := by omega
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hqk : 4 ≤ Nat.card k := by rw [hk, ← hK]; exact hq
  have : Finite (ModGL TwistTag.E6.tag KC) := finite_modGL
  have : Finite C := Finite.of_injective _ Subtype.val_injective
  have hLG₀ : L ≤ pieceSpan e := le_pieceSpan hq e
  set P3 := ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1) with hP3
  set P3' := (2 ^ f) ^ 24 * P3 with hP3'
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hmod.not_conj 1 (by rw [map_one, one_mul]; group)
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hx1
    have h1 : eM (QuotientGroup.mk' (center M) (1 : M)) = φ⁻¹ x := hwx
    rw [map_one, map_one] at h1
    have h2 := congrArg φ h1
    rw [map_one, MulAut.inv_apply, MulEquiv.apply_symm_apply] at h2
    exact h2.symm
  set Λ := perfectCore (M ⊓ centralizer ({t} : Set G)) with hΛdef
  have hperfA := fixSubgroup_perfect_of_conj hφ hmod.fix_perfect
  have hmapΛ := map_perfectCore_subgroupOf_centralizer_eq hZM eM ht htM hperfA
  have hfixmap := map_eqLocus_eq_of_conj hφ
  have hfixA : Nat.card (E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩)) = P3' := by
    rw [← card_map_of_injective (f := φ.toMonoidHom) φ.injective]
    change Nat.card (((normalizerQuotMulAut eM ⟨t, htM⟩).toMonoidHom.eqLocus
      (MonoidHom.id C)).map φ.toMonoidHom) = _
    rw [hfixmap]
    change Nat.card (E6Pilot.fixSubgroup (MulAut.conj x * η)) = _
    rw [hmod.card_fix, natCard_centralizer_yRep_of_ne_tu hf1 hk (by decide)]
  have hΛsub := map_subtype_perfectCore_subgroupOf M t
  have hΛcard : Nat.card Λ =
      Nat.card (perfectCore ((centralizer ({t} : Set G)).subgroupOf M)) := by
    rw [hΛdef, ← hΛsub, card_map_of_injective M.subtype_injective]
  have hN₃Λ : P3' ∣ Nat.card Λ := by
    rw [hΛcard, ← hfixA, ← hmapΛ]
    exact natCard_map_dvd _ _
  have hΛw : Λ ≤ centralizer ({w} : Set G) := fun c hc =>
    mem_centralizer_singleton_iff.2 (hwc c (perfectCore_le _ hc))
  have hΛM : Λ ≤ M := (perfectCore_le _).trans inf_le_left
  have hLcard : Nat.card L = 2 ^ (24 * f) *
      (((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 8 - 1) * ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) := by
    rw [Nat.card_congr e.toEquiv, natCard_adjointGroup_F4_eq hK]
  have h2dvd : 2 ^ (24 * f) ∣ Nat.card Λ := by
    refine (Dvd.intro P3 ?_).trans hN₃Λ
    rw [hP3', ← pow_mul, mul_comm f 24]
  obtain ⟨U, hUΛ, hUcard⟩ :=
    exists_le_natCard_eq_two_pow (hΛL) (odd_ordF4_oddPart hf1) hLcard h2dvd
  set wL : L := ⟨w, hwL⟩ with hwLdef
  have hwL1 : wL ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
  set UL : Subgroup L := U.subgroupOf L with hULdef
  have hUL : Nat.card UL = 2 ^ (24 * f) := by
    rw [hULdef, card_subgroupOf_of_le (hUΛ.trans hΛL), hUcard]
  have hwUL : wL ∈ centralizer (UL : Set L) := by
    rw [mem_centralizer_iff]
    intro u hu
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hΛw (hUΛ (mem_subgroupOf.1 hu))))
  set ΛL : Subgroup L := Λ.subgroupOf L with hΛLdef
  have hΛLw : ΛL ≤ centralizer ({wL} : Set L) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hΛw (mem_subgroupOf.1 hy)))
  have hdivL : P3' ∣ Nat.card ΛL := by
    rw [hΛLdef, card_subgroupOf_of_le hΛL]
    exact hN₃Λ
  obtain ⟨c, i, a, -, ha, hcw, -, hcN⟩ := exists_conj_leviTorus_of_injective hf1 hK
    (β := e.toMonoidHom) e.injective hUL hwUL hwL1 hΛLw hdivL (T := ⊥) bot_le bot_le
    (by rw [Subgroup.card_bot]; exact odd_one)
  have hcardCL : Nat.card (L ⊓ centralizer ({w} : Set G) : Subgroup G) =
      Nat.card (centralizer ({e wL} : Set (adjointGroup .F4 K))) := by
    have h1 : (L ⊓ centralizer ({w} : Set G) : Subgroup G) =
        ((centralizer ({wL} : Set L)).map e.toMonoidHom).map (L.subtype.comp
          e.symm.toMonoidHom) := by
      rw [map_map]
      ext g
      simp only [mem_inf, mem_map, mem_centralizer_singleton_iff, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, coe_subtype]
      constructor
      · rintro ⟨hgL, hgw⟩
        refine ⟨⟨g, hgL⟩, Subtype.ext hgw, ?_⟩
        rw [MulEquiv.symm_apply_apply]
      · rintro ⟨y, hy, rfl⟩
        rw [MulEquiv.symm_apply_apply]
        exact ⟨y.2, congrArg Subtype.val hy⟩
    have h2 : (centralizer ({wL} : Set L)).map e.toMonoidHom =
        centralizer ({e wL} : Set (adjointGroup .F4 K)) := by
      ext y
      simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [← map_mul, ← map_mul, hz]
      · intro hy
        exact ⟨e.symm y, e.injective (by rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]),
          MulEquiv.apply_symm_apply e y⟩
    have hinj : Function.Injective (L.subtype.comp e.symm.toMonoidHom) := fun a b hab =>
      e.symm.injective (L.subtype_injective hab)
    rw [h1, card_map_of_injective hinj, h2]
  have hUe : Nat.card (UL.map e.toMonoidHom) = 2 ^ (24 * f) := by
    rw [card_map_of_injective e.injective, hUL]
  have hxP : e wL ∈ centralizer (((sylowOfCardF4 hf1 hK (UL.map e.toMonoidHom) hUe :
      Sylow 2 (adjointGroup .F4 K)) : Subgroup (adjointGroup .F4 K)) :
        Set (adjointGroup .F4 K)) := by
    rw [coe_sylowOfCardF4, mem_centralizer_iff]
    rintro _ ⟨u, hu, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, mem_centralizer_iff.1 hwUL u hu]
  obtain ⟨κ, c₁, hc₁⟩ := factF2 _ (e wL) hxP (fun h => hwL1 (e.injective (h.trans (map_one e).symm)))
  have hdivCL : P3' ∣ Nat.card (L ⊓ centralizer ({w} : Set G) : Subgroup G) :=
    hN₃Λ.trans (Subgroup.card_dvd_of_le (le_inf hΛL hΛw))
  have hκ : κ ≠ .tu := by
    rintro rfl
    apply not_dvd_natCard_centralizer_yRep_tu hf1 hk hK (κ := .t) (by decide)
    rw [natCard_centralizer_yRep_of_ne_tu hf1 hk (by decide), ← hc₁, natCard_centralizer_conj,
      ← hcardCL]
    exact hdivCL
  have hCL : Nat.card (L ⊓ centralizer ({w} : Set G) : Subgroup G) = P3' := by
    rw [hcardCL, ← natCard_centralizer_conj c₁, hc₁, natCard_centralizer_yRep_of_ne_tu hf1 hK hκ]
  have hΛeq : Λ = L ⊓ centralizer ({w} : Set G) :=
    Subgroup.eq_of_le_of_card_ge (le_inf hΛL hΛw) (by
      rw [hCL]
      exact Nat.le_of_dvd Nat.card_pos hN₃Λ)
  obtain ⟨T, Jw, hTL, hTw, hTcard, hTform, hJwL, hwJw, ⟨y₀, hy₀J, hy₀⟩, hJwcard, hJwE, hE⟩ :=
    exists_torus_rootSL2_of_conj hq e hwL c i ha hcw
  have hTΛ : T ≤ Λ := by
    rw [hΛeq]
    exact le_inf hTL hTw
  have hTM : T ≤ M := hTΛ.trans hΛM
  have hTodd : Odd (Nat.card T) := by
    rw [hTcard, hK]
    have h1 := odd_two_pow_pow_sub_one hf1 (j := 1) le_rfl
    rw [pow_one] at h1
    exact h1.pow
  have hTU : T ≤ normalizer (U : Set G) := by
    intro y hy
    obtain ⟨d, hd, rfl⟩ := hTform y hy
    exact coe_symm_mem_normalizer_of_mem_normalizer_map e (hUΛ.trans hΛL) (hcN d hd)
  have hETG₀ : centralizerPerfectCore T ≤ pieceSpan e := by
    rw [hE]
    have hl : ((e.symm c⁻¹ : L) : G) ∈ pieceSpan e := hLG₀ (e.symm c⁻¹).2
    have h1 : pieceCore e {i} ≤ pieceSpan e :=
      le_iSup_of_le (f := fun J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2} =>
        pieceCore e J.1) ⟨{i}, by simp⟩ le_rfl
    calc (pieceCore e {i}).map (MulAut.conj ((e.symm c⁻¹ : L) : G)).toMonoidHom
        ≤ (pieceSpan e).map (MulAut.conj ((e.symm c⁻¹ : L) : G)).toMonoidHom := map_mono h1
      _ = pieceSpan e := map_conj_eq_self_of_mem_kerTorus_aux hl
  have hwU : U ≤ centralizer ({w} : Set G) := hUΛ.trans hΛw
  have hETJ : centralizerPerfectCore T ≤ Jw :=
    centralizerPerfectCore_le_of_caseL_model hf hK e hZL htC hk hmod e₀ htN hψ hwL hw1 htwN hφ'
      (hUΛ.trans hΛL) hUcard hwU hΛL hΛw hN₃Λ hTL hTU hTw hTcard hJwL hJwcard hJwE hETG₀
  have hΛcard' : Nat.card Λ = P3' := by rw [hΛeq, hCL]
  have hJwM : Jw ≤ M :=
    le_of_caseL_model_M hf hK ht hk hmod hZM eM htM hφ hwM hwx hΛcard' hΛw hwΛ hUΛ hUcard hTΛ hTU
      hTodd hETJ hJwcard
  have hy₀M : y₀ ∈ M ⊓ centralizer ({t} : Set G) := by
    refine ⟨hJwM hy₀J, mem_centralizer_singleton_iff.2 ?_⟩
    exact (mem_centralizer_iff.1 htC y₀ (hJwL hy₀J))
  exact hy₀ (hwc y₀ hy₀M)

end Core

end CFSG.SeitzReduction.F4Pilot
