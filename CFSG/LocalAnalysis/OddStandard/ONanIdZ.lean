module

public import CFSG.LocalAnalysis.OddStandard.ONanIdC
public import CFSG.LocalAnalysis.ZStar
public import CFSG.GroupTheory.PCore.PrimeCoreImages
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris

theorem isPGroup_closure_pair_sq {K : Type*} [Group K] {a b : K} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) : IsPGroup 2 (closure ({a, b} : Set K)) := by
  have hC : closure ({a, b} : Set K) ≤ centralizer ({a, b} : Set K) := by
    rw [closure_le]
    intro g hg
    rw [SetLike.mem_coe, mem_centralizer_iff]
    rcases hg with rfl | rfl <;> rintro h (rfl | rfl)
    · rfl
    · exact hab.symm
    · exact hab
    · rfl
  have hcomm : ∀ g ∈ closure ({a, b} : Set K), ∀ h ∈ closure ({a, b} : Set K),
      g * h = h * g := by
    intro g hg h hh
    have hg' := mem_centralizer_iff.1 (hC hg)
    have hle : closure ({a, b} : Set K) ≤ centralizer ({g} : Set K) := by
      rw [closure_le]
      intro y hy
      exact mem_centralizer_singleton_iff.2 (hg' y hy)
    exact (mem_centralizer_singleton_iff.1 (hle hh)).symm
  have hsq : ∀ g ∈ closure ({a, b} : Set K), g * g = 1 := by
    intro g hg
    induction hg using closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact ha
      · exact hb
    | one => exact mul_one 1
    | mul y y' hy hy' ih ih' =>
      calc y * y' * (y * y') = y * (y' * y) * y' := by group
        _ = y * (y * y') * y' := by rw [hcomm y' hy' y hy]
        _ = y * y * (y' * y') := by group
        _ = 1 := by rw [ih, ih', one_mul]
    | inv y hy ih => rw [← mul_inv_rev, ih, inv_one]
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, OneMemClass.coe_one, pow_two]
  exact hsq g g.2

theorem exists_isPGroup_of_quot {K : Type*} [Group K] {C : Subgroup K} {Z : Subgroup C}
    [Z.Normal] (hZ : IsPGroup 2 Z) {u v : C} (hu : u * u ∈ Z) (hv : v * v ∈ Z)
    (huv : (u * v)⁻¹ * (v * u) ∈ Z) :
    ∃ M : Subgroup K, IsPGroup 2 M ∧ M ≤ C ∧ (u : K) ∈ M ∧ (v : K) ∈ M := by
  have haa : QuotientGroup.mk' Z u * QuotientGroup.mk' Z u = 1 := by
    rw [← map_mul, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).2 hu
  have hbb : QuotientGroup.mk' Z v * QuotientGroup.mk' Z v = 1 := by
    rw [← map_mul, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).2 hv
  have hab : QuotientGroup.mk' Z u * QuotientGroup.mk' Z v =
      QuotientGroup.mk' Z v * QuotientGroup.mk' Z u := by
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact QuotientGroup.eq.2 huv
  have hker : IsPGroup 2 (QuotientGroup.mk' Z).ker := by
    rw [QuotientGroup.ker_mk']
    exact hZ
  refine ⟨((closure ({QuotientGroup.mk' Z u, QuotientGroup.mk' Z v} :
    Set (C ⧸ Z))).comap (QuotientGroup.mk' Z)).map C.subtype,
    ((isPGroup_closure_pair_sq haa hbb hab).comap_of_ker_isPGroup _ hker).map _, ?_,
    ⟨u, subset_closure (Set.mem_insert _ _), rfl⟩,
    ⟨v, subset_closure (Set.mem_insert_of_mem _ rfl), rfl⟩⟩
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem oddCore_eq_pPrimeCore_two' (X : Type*) [Group X] : CFSG.oddCore X = pPrimeCore 2 X := by
  unfold CFSG.oddCore pPrimeCore
  congr 1
  ext K
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem eq_bot_of_odd_normal_quot {H : Type*} [Group H] [Finite H] {Z : Subgroup H} [Z.Normal]
    (hZc : Z ≤ center H) (hZ2 : IsPGroup 2 Z) (hO : CFSG.oddCore H = ⊥)
    {N : Subgroup (H ⧸ Z)} (hN : N.Normal) (hNo : Odd (Nat.card N)) : N = ⊥ := by
  have h1 := CFSG.central_p_subgroup_prime_core_quotient Z hZc hZ2
  rw [← oddCore_eq_pPrimeCore_two' H, hO, Subgroup.map_bot] at h1
  have hle : N ≤ pPrimeCore 2 (H ⧸ Z) := le_sSup ⟨hN, Nat.coprime_two_left.2 hNo⟩
  rw [h1] at hle
  exact le_bot_iff.1 hle

theorem stE_inv_xE : gen 3 * gen 4 * xE * (gen 3 * gen 4)⁻¹ = xE⁻¹ := by decide

theorem stE_inv_y0E : gen 3 * gen 4 * y0E * (gen 3 * gen 4)⁻¹ = y0E⁻¹ := by decide

theorem xE_ne : xE ≠ 1 ∧ xE ≠ zc ∧ xE ≠ xE⁻¹ := by decide

theorem xE_inv_eq : xE⁻¹ = xE * zc := by decide

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

local notation "𝔵" => xel v1 v2 v3
local notation "𝔷" => invRep v1 v2 v3 s t 0

theorem mem_zpowers_z {g : G} : g ∈ zpowers 𝔷 ↔ g = 1 ∨ g = 𝔷 := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 h
    rw [← zpow_mod_orderOf, D.orderOf_rep 0]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [Nat.cast_ofNat, h, zpow_zero]
    · right
      rw [Nat.cast_ofNat, h, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem x_sq_mem_zpowers : 𝔵 * 𝔵 ∈ zpowers 𝔷 := by
  rw [D.xel_sq]
  exact mem_zpowers _

theorem x_comm_z : 𝔵 * 𝔷 = 𝔷 * 𝔵 := by
  rw [← D.xel_sq]
  group

theorem x_mem_Cz : 𝔵 ∈ centralizer ({𝔷} : Set G) :=
  mem_centralizer_singleton_iff.2 D.x_comm_z

theorem x_inv_eq : 𝔵⁻¹ = 𝔵 * 𝔷 := by
  rw [D.x_eq, D.z_eq, ← map_inv, ← map_mul, xE_inv_eq]

theorem x_ne_inv : 𝔵 ≠ 𝔵⁻¹ := by
  rw [D.x_eq, ← map_inv]
  exact fun h => xE_ne.2.2 (D.E.inj h)

theorem x_notMem_zpowers_z : 𝔵 ∉ zpowers 𝔷 := by
  rw [D.mem_zpowers_z, D.x_eq, D.z_eq]
  rintro (h | h)
  · exact xE_ne.1 (D.E.inj (by rw [h, map_one]))
  · exact xE_ne.2.1 (D.E.inj h)

theorem st_inv_x : s * t * 𝔵 * (s * t)⁻¹ = 𝔵⁻¹ := by
  have h := congrArg D.E.φ stE_inv_xE
  simp only [map_mul, map_inv, AlpEmb.φ_s, AlpEmb.φ_t] at h
  rw [D.x_eq]
  exact h

theorem st_inv_y0 : s * t * (v1 * v3) * (s * t)⁻¹ = (v1 * v3)⁻¹ := by
  have h := congrArg D.E.φ stE_inv_y0E
  simp only [map_mul, map_inv, AlpEmb.φ_s, AlpEmb.φ_t] at h
  rw [D.y0_eq]
  exact h

theorem P_le_Cz : alpP v1 v2 v3 s t ≤ centralizer ({𝔷} : Set G) :=
  fun p hp => mem_centralizer_singleton_iff.2
    ((AlpEmb.centre_alpP D.E D.hF D.z_mem_P).2 (Or.inr rfl) p hp)

theorem st_mem_Cz : s * t ∈ centralizer ({𝔷} : Set G) :=
  D.P_le_Cz (mul_mem s_mem_P t_mem_P)

theorem isPGroup_zpowers_zIn_z : IsPGroup 2 (zpowers (zIn 𝔷)) := by
  refine IsPGroup.of_card (n := 1) ?_
  rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
  exact D.orderOf_rep 0

theorem conj_eq_or_inv_of_sq {g₁ g₂ : G} (h₁ : g₁ * 𝔵 * g₁⁻¹ ∈ alpV v1 v2 v3)
    (h₂ : g₂ * 𝔵 * g₂⁻¹ ∈ alpV v1 v2 v3)
    (hsq : g₁ * 𝔵 * g₁⁻¹ * (g₁ * 𝔵 * g₁⁻¹) = g₂ * 𝔵 * g₂⁻¹ * (g₂ * 𝔵 * g₂⁻¹)) :
    g₂ * 𝔵 * g₂⁻¹ = g₁ * 𝔵 * g₁⁻¹ ∨ g₂ * 𝔵 * g₂⁻¹ = (g₁ * 𝔵 * g₁⁻¹)⁻¹ := by
  obtain ⟨n, hn, hnx⟩ := D.fuse_V (D.V_le_centralizer_V D.x_mem_V) (D.V_le_centralizer_V h₁)
    ⟨g₁, rfl⟩
  have hb' : n * (g₂ * 𝔵 * g₂⁻¹) * n⁻¹ ∈ alpV v1 v2 v3 := conj_mem_V hn h₂
  have hsq' : n * (g₂ * 𝔵 * g₂⁻¹) * n⁻¹ * (n * (g₂ * 𝔵 * g₂⁻¹) * n⁻¹) = 𝔵 * 𝔵 := by
    calc n * (g₂ * 𝔵 * g₂⁻¹) * n⁻¹ * (n * (g₂ * 𝔵 * g₂⁻¹) * n⁻¹)
        = n * (g₂ * 𝔵 * g₂⁻¹ * (g₂ * 𝔵 * g₂⁻¹)) * n⁻¹ := by group
      _ = n * (g₁ * 𝔵 * g₁⁻¹ * (g₁ * 𝔵 * g₁⁻¹)) * n⁻¹ := by rw [hsq]
      _ = n * (n⁻¹ * 𝔵 * n * (n⁻¹ * 𝔵 * n)) * n⁻¹ := by rw [hnx]
      _ = 𝔵 * 𝔵 := by group
  have hW : 𝔵⁻¹ * (n * g₂ * 𝔵 * (n * g₂)⁻¹) ∈ alpW v1 v2 v3 := by
    rw [show n * g₂ * 𝔵 * (n * g₂)⁻¹ = n * (g₂ * 𝔵 * g₂⁻¹) * n⁻¹ by group]
    refine (D.mem_W_iff).2 ⟨mul_mem (inv_mem D.x_mem_V) hb', ?_⟩
    have hc := D.comm_V (inv_mem D.x_mem_V) hb'
    calc 𝔵⁻¹ * (n * (g₂ * 𝔵 * g₂⁻¹) * n⁻¹) * (𝔵⁻¹ * (n * (g₂ * 𝔵 * g₂⁻¹) * n⁻¹))
        = 𝔵⁻¹ * ((n * (g₂ * 𝔵 * g₂⁻¹) * n⁻¹) * 𝔵⁻¹) * (n * (g₂ * 𝔵 * g₂⁻¹) * n⁻¹) := by
          group
      _ = 𝔵⁻¹ * (𝔵⁻¹ * (n * (g₂ * 𝔵 * g₂⁻¹) * n⁻¹)) * (n * (g₂ * 𝔵 * g₂⁻¹) * n⁻¹) := by
          rw [hc]
      _ = (𝔵 * 𝔵)⁻¹ * (n * (g₂ * 𝔵 * g₂⁻¹) * n⁻¹ * (n * (g₂ * 𝔵 * g₂⁻¹) * n⁻¹)) := by group
      _ = 1 := by rw [hsq', inv_mul_cancel]
  have e : g₂ * 𝔵 * g₂⁻¹ = n⁻¹ * (n * g₂ * 𝔵 * (n * g₂)⁻¹) * n := by group
  rcases D.conj_x_of_mem hW with h | h
  · left
    rw [e, h, hnx]
  · right
    rw [e, h, ← hnx]
    group

theorem conj_x_of_comm_mod (hone : OneClass G) {g : G} (hg : g ∈ centralizer ({𝔷} : Set G))
    (hc : (g * 𝔵 * g⁻¹ * 𝔵)⁻¹ * (𝔵 * (g * 𝔵 * g⁻¹)) ∈ zpowers 𝔷) :
    g * 𝔵 * g⁻¹ = 𝔵 ∨ g * 𝔵 * g⁻¹ = 𝔵⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgz : g * 𝔷 * g⁻¹ = 𝔷 := by rw [mem_centralizer_singleton_iff.1 hg, mul_inv_cancel_right]
  have hx1 : g * 𝔵 * g⁻¹ ∈ centralizer ({𝔷} : Set G) :=
    mul_mem (mul_mem hg D.x_mem_Cz) (inv_mem hg)
  have hsq1 : g * 𝔵 * g⁻¹ * (g * 𝔵 * g⁻¹) ∈ zpowers 𝔷 := by
    rw [show g * 𝔵 * g⁻¹ * (g * 𝔵 * g⁻¹) = g * (𝔵 * 𝔵) * g⁻¹ by group, D.xel_sq, hgz]
    exact mem_zpowers _
  obtain ⟨M, hMp, hMC, hxM, hx1M⟩ := exists_isPGroup_of_quot D.isPGroup_zpowers_zIn_z
    (u := ⟨𝔵, D.x_mem_Cz⟩) (v := ⟨g * 𝔵 * g⁻¹, hx1⟩)
    ((mem_zpowers_zIn_iff _).2 D.x_sq_mem_zpowers) ((mem_zpowers_zIn_iff _).2 hsq1)
    ((mem_zpowers_zIn_iff _).2 (by
      have e : (𝔵 * (g * 𝔵 * g⁻¹))⁻¹ * (g * 𝔵 * g⁻¹ * 𝔵) =
          ((g * 𝔵 * g⁻¹ * 𝔵)⁻¹ * (𝔵 * (g * 𝔵 * g⁻¹)))⁻¹ := by group
      show (𝔵 * (g * 𝔵 * g⁻¹))⁻¹ * (g * 𝔵 * g⁻¹ * 𝔵) ∈ zpowers 𝔷
      rw [e]
      exact inv_mem hc))
  obtain ⟨c, hc', hcM⟩ := exists_conj_le_of_isSylowOf D.isSylowOf_P_centralizer_z hMC hMp
  have hcz : c * 𝔷 * c⁻¹ = 𝔷 := by
    rw [mem_centralizer_singleton_iff.1 hc', mul_inv_cancel_right]
  have hV₁ : c * 𝔵 * c⁻¹ ∈ alpV v1 v2 v3 := D.conj_x_mem_V hone (hcM _ hxM)
  have hV₂ : c * g * 𝔵 * (c * g)⁻¹ ∈ alpV v1 v2 v3 := by
    refine D.conj_x_mem_V hone ?_
    rw [show c * g * 𝔵 * (c * g)⁻¹ = c * (g * 𝔵 * g⁻¹) * c⁻¹ by group]
    exact hcM _ hx1M
  have hsq : c * 𝔵 * c⁻¹ * (c * 𝔵 * c⁻¹) = c * g * 𝔵 * (c * g)⁻¹ * (c * g * 𝔵 * (c * g)⁻¹) := by
    calc c * 𝔵 * c⁻¹ * (c * 𝔵 * c⁻¹) = c * (𝔵 * 𝔵) * c⁻¹ := by group
      _ = c * (g * (𝔵 * 𝔵) * g⁻¹) * c⁻¹ := by rw [D.xel_sq, hgz]
      _ = c * g * 𝔵 * (c * g)⁻¹ * (c * g * 𝔵 * (c * g)⁻¹) := by group
  rcases D.conj_eq_or_inv_of_sq hV₁ hV₂ hsq with h | h
  · left
    calc g * 𝔵 * g⁻¹ = c⁻¹ * (c * g * 𝔵 * (c * g)⁻¹) * c := by group
      _ = c⁻¹ * (c * 𝔵 * c⁻¹) * c := by rw [h]
      _ = 𝔵 := by group
  · right
    calc g * 𝔵 * g⁻¹ = c⁻¹ * (c * g * 𝔵 * (c * g)⁻¹) * c := by group
      _ = c⁻¹ * (c * 𝔵 * c⁻¹)⁻¹ * c := by rw [h]
      _ = 𝔵⁻¹ := by group

theorem conj_x_of_mem_centralizer_z (hone : OneClass G) (hbal : Balanced G) {g : G}
    (hg : g ∈ centralizer ({𝔷} : Set G)) : g * 𝔵 * g⁻¹ = 𝔵 ∨ g * 𝔵 * g⁻¹ = 𝔵⁻¹ := by
  classical
  have : Fintype (KQ 𝔷) := Fintype.ofFinite _
  have hτ1 : πQ 𝔷 ⟨𝔵, D.x_mem_Cz⟩ ≠ 1 := by
    rw [Ne, πQ_eq_one_iff]
    exact D.x_notMem_zpowers_z
  have hττ : πQ 𝔷 ⟨𝔵, D.x_mem_Cz⟩ * πQ 𝔷 ⟨𝔵, D.x_mem_Cz⟩ = 1 := by
    rw [← map_mul, πQ_eq_one_iff]
    exact D.x_sq_mem_zpowers
  have hconj : ∀ k : centralizer ({𝔷} : Set G),
      πQ 𝔷 k * πQ 𝔷 ⟨𝔵, D.x_mem_Cz⟩ * (πQ 𝔷 k)⁻¹ =
        πQ 𝔷 ⟨(k : G) * 𝔵 * (k : G)⁻¹, mul_mem (mul_mem k.2 D.x_mem_Cz) (inv_mem k.2)⟩ := by
    intro k
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hiso : ∀ h : KQ 𝔷, h * πQ 𝔷 ⟨𝔵, D.x_mem_Cz⟩ * h⁻¹ * πQ 𝔷 ⟨𝔵, D.x_mem_Cz⟩ =
      πQ 𝔷 ⟨𝔵, D.x_mem_Cz⟩ * (h * πQ 𝔷 ⟨𝔵, D.x_mem_Cz⟩ * h⁻¹) →
      h * πQ 𝔷 ⟨𝔵, D.x_mem_Cz⟩ * h⁻¹ = πQ 𝔷 ⟨𝔵, D.x_mem_Cz⟩ := by
    intro h hh
    obtain ⟨k, rfl⟩ := πQ_surjective 𝔷 h
    rw [hconj k] at hh ⊢
    rw [← map_mul, ← map_mul] at hh
    have hc := (πQ_eq_iff _ _).1 hh
    rw [πQ_eq_iff]
    rcases D.conj_x_of_comm_mod hone k.2 hc with h1 | h1
    · show ((k : G) * 𝔵 * (k : G)⁻¹)⁻¹ * 𝔵 ∈ zpowers 𝔷
      rw [h1, inv_mul_cancel]
      exact one_mem _
    · show ((k : G) * 𝔵 * (k : G)⁻¹)⁻¹ * 𝔵 ∈ zpowers 𝔷
      rw [h1, inv_inv]
      exact D.x_sq_mem_zpowers
  obtain ⟨N, hNn, hNo, hN⟩ := CFSG.ZStar.glauberman_zStar (KQ 𝔷) _ hτ1 hττ hiso
  have hcen : zpowers (zIn 𝔷) ≤ center (centralizer ({𝔷} : Set G)) :=
    zpowers_le.2 (Subgroup.mem_center_iff.2 fun y =>
      Subtype.ext (mem_centralizer_singleton_iff.1 y.2))
  have hN1 : N = ⊥ :=
    eq_bot_of_odd_normal_quot hcen D.isPGroup_zpowers_zIn_z (hbal _ (D.orderOf_rep 0)) hNn hNo
  have hk := hN (πQ 𝔷 ⟨g, hg⟩)
  rw [hN1, mem_bot, mul_inv_eq_one, hconj, πQ_eq_iff] at hk
  have hk' : 𝔵⁻¹ * (g * 𝔵 * g⁻¹) ∈ zpowers 𝔷 := by
    have := inv_mem hk
    rw [mul_inv_rev, inv_inv] at this
    exact this
  rcases D.mem_zpowers_z.1 hk' with h1 | h1
  · left
    calc g * 𝔵 * g⁻¹ = 𝔵 * (𝔵⁻¹ * (g * 𝔵 * g⁻¹)) := by group
      _ = 𝔵 := by rw [h1, mul_one]
  · right
    calc g * 𝔵 * g⁻¹ = 𝔵 * (𝔵⁻¹ * (g * 𝔵 * g⁻¹)) := by group
      _ = 𝔵 * 𝔷 := by rw [h1]
      _ = 𝔵⁻¹ := D.x_inv_eq.symm

omit [Finite G] D in
theorem mem_centralizer_x_iff {k : G} : k ∈ centralizer ({𝔵} : Set G) ↔ k * 𝔵 * k⁻¹ = 𝔵 := by
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [h, mul_inv_cancel_right]
  · intro h
    calc k * 𝔵 = k * 𝔵 * k⁻¹ * k := by group
      _ = 𝔵 * k := by rw [h]

theorem index_centralizer_x (hone : OneClass G) (hbal : Balanced G) :
    ((centralizer ({𝔵} : Set G)).subgroupOf (centralizer ({𝔷} : Set G))).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨s * t, D.st_mem_Cz⟩, fun b => ?_⟩
  rw [mem_subgroupOf, mem_subgroupOf, Subgroup.coe_mul, mem_centralizer_x_iff,
    mem_centralizer_x_iff]
  have e : (b : G) * (s * t) * 𝔵 * ((b : G) * (s * t))⁻¹ = ((b : G) * 𝔵 * (b : G)⁻¹)⁻¹ := by
    calc (b : G) * (s * t) * 𝔵 * ((b : G) * (s * t))⁻¹
        = (b : G) * (s * t * 𝔵 * (s * t)⁻¹) * (b : G)⁻¹ := by group
      _ = (b : G) * 𝔵⁻¹ * (b : G)⁻¹ := by rw [D.st_inv_x]
      _ = ((b : G) * 𝔵 * (b : G)⁻¹)⁻¹ := by group
  show Xor ((b : G) * (s * t) * 𝔵 * ((b : G) * (s * t))⁻¹ = 𝔵) ((b : G) * 𝔵 * (b : G)⁻¹ = 𝔵)
  rw [e]
  have hne := D.x_ne_inv
  rcases D.conj_x_of_mem_centralizer_z hone hbal b.2 with h | h
  · rw [h]
    exact Or.inr ⟨rfl, fun h' => hne h'.symm⟩
  · rw [h, inv_inv]
    exact Or.inl ⟨rfl, fun h' => hne h'.symm⟩

end FusCtx

end CFSG.OddStandard.ONanRec
