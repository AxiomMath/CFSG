module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.LevelOne
public import CFSG.LocalAnalysis.EvenBN.TwoF4.SuzukiSylow

public section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup CFSG.Open
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff isSylowOf_of_card)
open scoped commutatorElement

section Generic

variable {X : Type*} [Group X]

theorem mem_normalizer_commutator {M : Subgroup X} {g : X} (hg : g ∈ normalizer (M : Set X)) :
    g ∈ normalizer ((⁅M, M⁆ : Subgroup X) : Set X) := by
  have hM : M.map (MulAut.conj g).toMonoidHom = M := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.1 hg y).1 hy
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := (mem_normalizer_iff.1 (inv_mem hg) x).1 hx
      rwa [inv_inv] at this
  have hC : ⁅M, M⁆.map (MulAut.conj g).toMonoidHom = ⁅M, M⁆ := by
    rw [map_commutator, hM]
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hC]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hC] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have e : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      exact mul_left_cancel (mul_right_cancel e)
    rwa [← this]

theorem card_le_of_isSylowOf [Finite X] {p : ℕ} [Fact p.Prime] {P K Q : Subgroup X}
    (hP : IsSylowOf p P K) (hQK : Q ≤ K) (hQ : IsPGroup p Q) : Nat.card Q ≤ Nat.card P := by
  have hQ' : IsPGroup p (Q.subgroupOf K) := hQ.comap_subtype
  obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
  have h1 : Nat.card (Q.subgroupOf K) ≤ Nat.card S := Subgroup.card_le_of_le hS
  rw [Nat.card_congr (subgroupOfEquivOfLe hQK).toEquiv, Sylow.card_eq_multiplicity] at h1
  rw [hP.card_eq]
  exact h1

theorem isSylowOf_of_forall_card_le [Finite X] {p : ℕ} [Fact p.Prime] {P K : Subgroup X}
    (hPK : P ≤ K) (hP : IsPGroup p P)
    (h : ∀ Q : Subgroup X, Q ≤ K → IsPGroup p Q → Nat.card Q ≤ Nat.card P) : IsSylowOf p P K := by
  have hP' : IsPGroup p (P.subgroupOf K) := hP.comap_subtype
  obtain ⟨S, hS⟩ := hP'.exists_le_sylow
  set S' : Subgroup X := (S : Subgroup K).map K.subtype with hS'
  have hPS : P ≤ S' := by
    intro x hx
    exact ⟨⟨x, hPK hx⟩, hS hx, rfl⟩
  have hSK : S' ≤ K := map_subtype_le _
  have hcard : Nat.card S' ≤ Nat.card P := h S' hSK (S.isPGroup'.map K.subtype)
  have heq : P = S' := Subgroup.eq_of_le_of_card_ge hPS hcard
  exact ⟨S, heq.symm⟩

theorem isSylowOf_map_of_injective [Finite X] {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] {P K : Subgroup X} (hP : IsSylowOf p P K) {φ : X →* Y}
    (hφ : Function.Injective φ) : IsSylowOf p (P.map φ) (K.map φ) := by
  rw [isSylowOf_iff] at hP ⊢
  obtain ⟨hle, hp, hdvd⟩ := hP
  refine ⟨map_mono hle, hp.map φ, ?_⟩
  rw [Subgroup.relIndex_map_map, (MonoidHom.ker_eq_bot_iff φ).2 hφ, sup_bot_eq, sup_bot_eq]
  exact hdvd

end Generic

namespace Setup

variable {G : Type} [Group G] [Finite G]
  (h : Setup G)

theorem pull_centralizer_subgroup {M : Subgroup (ModGL F4.tag h.K)}
    (hM : M ≤ F4.reeGamma h.K h.a) :
    h.pull (centralizer (M : Set (ModGL F4.tag h.K))) =
      h.L ⊓ centralizer (h.pull M : Set G) := by
  refine le_antisymm (le_inf (h.pull_le_L _) (h.pull_le_centralizer le_rfl)) ?_
  rintro x ⟨hxL, hxc⟩
  rw [← h.range_emb] at hxL
  obtain ⟨y, rfl⟩ := hxL
  refine h.emb_mem_pull.2 (mem_centralizer_iff.2 fun m hm => ?_)
  have h1 := mem_centralizer_iff.1 hxc (h.emb ⟨m, hM hm⟩) (h.emb_mem_pull.2 hm)
  rw [← map_mul, ← map_mul] at h1
  exact congrArg Subtype.val (h.emb_injective h1)

theorem levi_core_G {i : Idx} (hi : i.isCenter = false) :
    h.L ⊓ centralizer (h.Ht i : Set G) = h.Ht i ⊔ h.N i ∧
      h.N i ≤ centralizer (h.Ht i : Set G) ∧ h.Ht i ⊓ h.N i = ⊥ := by
  obtain ⟨h1, h2, h3, -⟩ := miyamoto_2_2 h.one_le_a h.card_K hi
  have hHΓ : torusHi h.K h.a i ≤ F4.reeGamma h.K h.a :=
    (torusHi_le_torusH i).trans (torusH_le_reeGamma h.card_K)
  refine ⟨?_, h.pull_le_centralizer h2, ?_⟩
  · have := congrArg h.pull h1
    rw [h.pull_inf, h.pull_reeGamma, h.pull_centralizer_subgroup hHΓ, ← inf_assoc, inf_idem,
      h.pull_sup hHΓ (leviN_le_reeGamma h.card_K i)] at this
    exact this
  · have := congrArg h.pull h3
    rwa [h.pull_inf, h.pull_bot] at this

theorem Ht_le_centralizer_Ht (i : Idx) : h.Ht i ≤ centralizer (h.Ht i : Set G) :=
  h.pull_le_centralizer ((torusHi_le_torusH i).trans (torusH_le_centralizer_torusHi i))

theorem commutator_N (i : Idx) : ⁅h.N i, h.N i⁆ = h.N i :=
  commutator_eq_self_of_isSimpleGroup (h.isSimpleGroup_N i).1 (h.isSimpleGroup_N i).2

theorem eq_one_of_mem_N_of_commute (i : Idx) {m : G} (hm : m ∈ h.N i)
    (hc : ∀ m' ∈ h.N i, m * m' = m' * m) : m = 1 :=
  eq_one_of_forall_commute_of_isSimpleGroup (h.isSimpleGroup_N i).1 (h.isSimpleGroup_N i).2 hm hc

theorem L_inf_centralizer_Ht_le {i : Idx} (hi : i.isCenter = false) {x : G}
    (hx : x ∈ h.L ⊓ centralizer (h.Ht i : Set G)) (hxN : ∀ n ∈ h.N i, x * n = n * x) :
    x ∈ h.Ht i := by
  obtain ⟨hcore, hNH, -⟩ := h.levi_core_G hi
  have hle : h.N i ≤ normalizer (h.Ht i : Set G) := fun n hn =>
    Subgroup.centralizer_le_normalizer _ (hNH hn)
  rw [hcore, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left (h.Ht i) (h.N i) hle] at hx
  obtain ⟨y, hy, n, hn, rfl⟩ := hx
  beta_reduce at hxN ⊢
  have hn1 : n = 1 := by
    refine h.eq_one_of_mem_N_of_commute i hn fun m hm => ?_
    have h1 := hxN m hm
    have hym : y * m = m * y := mem_centralizer_iff.1 (hNH hm) y hy
    calc n * m = y⁻¹ * (y * n * m) := by group
      _ = y⁻¹ * (m * (y * n)) := by rw [h1]
      _ = y⁻¹ * (m * y) * n := by group
      _ = y⁻¹ * (y * m) * n := by rw [hym]
      _ = m * n := by group
  rw [hn1, mul_one]
  exact hy

theorem C_inf_centralizer_Ht_le_normalizer_N {i : Idx} (hi : i.isCenter = false) :
    h.C ⊓ centralizer (h.Ht i : Set G) ≤ normalizer (h.N i : Set G) := by
  obtain ⟨hcore, hNH, -⟩ := h.levi_core_G hi
  have hcomm : ⁅h.L ⊓ centralizer (h.Ht i : Set G), h.L ⊓ centralizer (h.Ht i : Set G)⁆ =
      h.N i := by
    rw [hcore]
    refine le_antisymm ((commutator_sup_le_of_central fun z hz y hy => ?_).trans
      (h.commutator_N i).le) ?_
    · have hyc : y ∈ centralizer (h.Ht i : Set G) :=
        (sup_le (h.Ht_le_centralizer_Ht i) hNH) hy
      exact mem_centralizer_iff.1 hyc z hz
    · conv_lhs => rw [← h.commutator_N i]
      exact commutator_mono le_sup_right le_sup_right
  intro x hx
  obtain ⟨hxC, hxH⟩ := mem_inf.1 hx
  rw [← hcomm]
  refine mem_normalizer_commutator (mem_normalizer_iff.2 fun y => ?_)
  have hxL := mem_normalizer_iff.1 (h.centralizer_le_normalizer hxC) y
  have hxH' := mem_normalizer_iff.1 (Subgroup.le_normalizer hxH) y
  simp only [mem_inf]
  exact ⟨fun ⟨h1, h2⟩ => ⟨hxL.1 h1, hxH'.1 h2⟩, fun ⟨h1, h2⟩ => ⟨hxL.2 h1, hxH'.2 h2⟩⟩

theorem mem_Ht_sup_of_commute_N {i : Idx} (hi : i.isCenter = false)
    (hσ : ∀ x : h.C, (∀ n ∈ h.N i, (x : G) * n = n * x) → h.fieldFactor x = 1) {x : G}
    (hxC : x ∈ h.C) (hxH : x ∈ centralizer (h.Ht i : Set G))
    (hxN : ∀ n ∈ h.N i, x * n = n * x) : x ∈ h.Ht i ⊔ zpowers h.t := by
  obtain ⟨l, hl, c, hc, hxlc⟩ := (h.fieldFactor_eq_one_iff ⟨x, hxC⟩).1 (hσ ⟨x, hxC⟩ hxN)
  change x = l * c at hxlc
  have hcL : ∀ y ∈ h.L, c * y = y * c := fun y hy => (mem_centralizer_iff.1 hc.1 y hy).symm
  have hlx : l = x * c⁻¹ := by rw [hxlc]; group
  have hlH : l ∈ h.L ⊓ centralizer (h.Ht i : Set G) := by
    refine mem_inf.2 ⟨hl, mem_centralizer_iff.2 fun y hy => ?_⟩
    have hyL : y ∈ h.L := h.pull_le_L _ hy
    have h1 := mem_centralizer_iff.1 hxH y hy
    rw [hlx]
    calc y * (x * c⁻¹) = x * y * c⁻¹ := by rw [← mul_assoc, h1]
      _ = x * (c⁻¹ * y) := by
        rw [mul_assoc, (Commute.inv_left (show Commute c y from hcL y hyL)).eq]
      _ = x * c⁻¹ * y := by group
  have hlN : ∀ n ∈ h.N i, l * n = n * l := by
    intro n hn
    have hnL : n ∈ h.L := h.N_le_L i hn
    rw [hlx]
    calc x * c⁻¹ * n = x * n * c⁻¹ := by
          rw [mul_assoc, (Commute.inv_left (show Commute c n from hcL n hnL)).eq, ← mul_assoc]
      _ = n * x * c⁻¹ := by rw [hxN n hn]
      _ = n * (x * c⁻¹) := by group
  have hlHt := h.L_inf_centralizer_Ht_le hi hlH hlN
  have hcT : c ∈ zpowers h.t := by
    rw [← h.sec3_1.1]
    exact hc
  rw [hxlc]
  exact mul_mem (mem_sup_left hlHt) (mem_sup_right hcT)

theorem fieldFactor_eq_one_of_commute_N5 (x : h.C) (hx : ∀ n ∈ h.N .i5, (x : G) * n = n * x) :
    h.fieldFactor x = 1 :=
  h.fieldFactor_eq_one_of_commute_V12 x fun v hv =>
    hx v (h.V_le_N .i5 (h.V_center_le .i5 hv))

theorem isSylowOf_V_N {i : Idx} (hi : i.isCenter = false) : IsSylowOf 2 (h.V i) (h.N i) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.finite_reeGamma
  have hsyl := isSylowOf_rootV_leviN h.one_le_a h.card_K hi
  have hV : ((rootV h.K h.a i).subgroupOf (F4.reeGamma h.K h.a)).map
      (F4.reeGamma h.K h.a).subtype = rootV h.K h.a i := by
    rw [subgroupOf_map_subtype, inf_eq_left.2 (rootV_le_reeGamma h.card_K i)]
  have hN : ((leviN h.K h.a i).subgroupOf (F4.reeGamma h.K h.a)).map
      (F4.reeGamma h.K h.a).subtype = leviN h.K h.a i := by
    rw [subgroupOf_map_subtype, inf_eq_left.2 (leviN_le_reeGamma h.card_K i)]
  rw [← hV, ← hN, CFSG.ABGLocalTools.isSylowOf_map_subtype_iff] at hsyl
  exact isSylowOf_map_of_injective hsyl h.emb_injective

theorem card_Ht (i : Idx) : Nat.card (h.Ht i) = 2 ^ (2 * h.a + 1) - 1 := by
  rw [Ht, h.card_pull ((torusHi_le_torusH i).trans (torusH_le_reeGamma h.card_K)),
    card_torusHi h.card_K i]

theorem isSylowOf_V_Ht_sup_N {i : Idx} (hi : i.isCenter = false) :
    IsSylowOf 2 (h.V i) (h.Ht i ⊔ h.N i) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hNH, hHN⟩ := h.levi_core_G hi
  have hVN := h.isSylowOf_V_N hi
  rw [isSylowOf_iff] at hVN ⊢
  obtain ⟨hle, hp, hdvd⟩ := hVN
  refine ⟨hle.trans le_sup_right, hp, ?_⟩
  rw [← relIndex_mul_relIndex _ _ _ hle le_sup_right]
  have hcard : Nat.card (h.Ht i ⊔ h.N i : Subgroup G) = Nat.card (h.Ht i) * Nat.card (h.N i) := by
    have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (h.Ht i) (h.N i)
      fun x hx y hy => mem_centralizer_iff.1 (hNH hy) x hx).1
    rwa [hHN, Subgroup.card_bot, mul_one] at this
  have hrel : (h.N i).relIndex (h.Ht i ⊔ h.N i) = Nat.card (h.Ht i) := by
    have e := relIndex_mul_card (h.N i) (h.Ht i ⊔ h.N i)
    rw [inf_of_le_left le_sup_right, hcard] at e
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos e
  have hodd : Odd (Nat.card (h.Ht i)) := by
    rw [h.card_Ht]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  rw [hrel]
  intro h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h3 | h3
  · exact hdvd h3
  · exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h3)

theorem V_le_centralizer_Ht {i : Idx} (hi : i.isCenter = false) :
    h.V i ≤ centralizer (h.Ht i : Set G) :=
  (h.V_le_N i).trans (h.levi_core_G hi).2.1

theorem t_commute_L {l : G} (hl : l ∈ h.L) : h.t * l = l * h.t :=
  (mem_centralizer_iff.1 h.htL l hl).symm

theorem card_le_of_isPGroup_C_inf {i : Idx} (hi : i.isCenter = false) {Q : Subgroup G}
    (hQ : Q ≤ h.C ⊓ centralizer (h.Ht i : Set G)) (hQ2 : IsPGroup 2 Q) :
    Nat.card Q ≤ 2 * Nat.card (h.V i) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcore, -, -⟩ := h.levi_core_G hi
  have hT := h.sec3_1.1
  have hQLT : Q ≤ h.L ⊔ zpowers h.t := by
    have := h.le_sup_of_isPGroup (hQ.trans inf_le_left) hQ2
    rwa [← Tsyl, hT] at this
  have hLT : h.L ⊓ zpowers h.t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxL, hxt⟩ := mem_inf.1 hx
    rcases eq_one_or_eq_of_mem_zpowers h.t_mul_t hxt with h1 | h1
    · rw [h1]; exact one_mem _
    · exact absurd (h1 ▸ hxL) h.t_not_mem_L
  have hcardLT : Nat.card (h.L ⊔ zpowers h.t : Subgroup G) = Nat.card h.L * 2 := by
    have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute h.L (zpowers h.t)
      fun x hx y hy => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
        exact ((Commute.zpow_left (show Commute h.t x from h.t_commute_L hx) k)).symm.eq).1
    rwa [hLT, Subgroup.card_bot, mul_one, h.card_zpowers_t] at this
  have hrelLT : h.L.relIndex (h.L ⊔ zpowers h.t) = 2 := by
    have e := relIndex_mul_card h.L (h.L ⊔ zpowers h.t)
    rw [inf_of_le_left le_sup_left, hcardLT, mul_comm] at e
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos e
  have hrel : h.L.relIndex Q ≤ 2 := by
    rw [← hrelLT]
    exact Subgroup.relIndex_le_of_le_right hQLT (by rw [hrelLT]; norm_num)
  have hQL : Nat.card (Q ⊓ h.L : Subgroup G) ≤ Nat.card (h.V i) := by
    refine card_le_of_isSylowOf (h.isSylowOf_V_Ht_sup_N hi) ?_ (hQ2.to_le inf_le_left)
    rw [← hcore]
    exact le_inf inf_le_right ((inf_le_left.trans hQ).trans inf_le_right)
  have e := relIndex_mul_card (Q ⊓ h.L) Q
  rw [inf_of_le_left inf_le_left, inf_relIndex_left] at e
  rw [← e]
  calc h.L.relIndex Q * Nat.card (Q ⊓ h.L : Subgroup G) ≤ 2 * Nat.card (h.V i) :=
    Nat.mul_le_mul hrel hQL

theorem card_V_sup_t (i : Idx) : Nat.card (h.V i ⊔ zpowers h.t : Subgroup G) =
    2 * Nat.card (h.V i) := by
  have hVt : h.V i ⊓ zpowers h.t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxV, hxt⟩ := mem_inf.1 hx
    rcases eq_one_or_eq_of_mem_zpowers h.t_mul_t hxt with h1 | h1
    · rw [h1]; exact one_mem _
    · exact absurd (h1 ▸ (h.pull_le_L _ hxV)) h.t_not_mem_L
  have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (h.V i) (zpowers h.t)
    fun x hx y hy => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      exact ((Commute.zpow_left (show Commute h.t x from h.t_commute_L (h.pull_le_L _ hx))
        k)).symm.eq).1
  rw [hVt, Subgroup.card_bot, mul_one, h.card_zpowers_t] at this
  rw [this, mul_comm]

theorem suzukiSylowFacts_V {i : Idx} (hi : i.isSz = true) : SuzukiSylowFacts (h.V i) := by
  have h1 := suzukiSylowFacts_rootV h.one_le_a h.card_K hi
  have hV : ((rootV h.K h.a i).subgroupOf (F4.reeGamma h.K h.a)).map
      (F4.reeGamma h.K h.a).subtype = rootV h.K h.a i := by
    rw [subgroupOf_map_subtype, inf_eq_left.2 (rootV_le_reeGamma h.card_K i)]
  rw [← hV] at h1
  exact (h1.of_map (F4.reeGamma h.K h.a).subtype_injective).map h.emb_injective

end Setup

end CFSG.LocalAnalysis.EvenBN.TwoF4
