module

public import CFSG.LocalAnalysis.OddStandard.ONanFusInvert
public import CFSG.LocalAnalysis.OddStandard.ONanFusLocModel
public import CFSG.LocalAnalysis.OddStandard.ONanFusFinal
public import CFSG.LocalAnalysis.OddStandard.ONanFusClasses
public import CFSG.LocalAnalysis.OddStandard.ONanSylowTransfer2

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

@[expose] def fG (i : Fin 2) : G := D.E.φ (fE i)

theorem fG_mem_V (i : Fin 2) : D.fG i ∈ alpV v1 v2 v3 := by
  rw [AlpEmb.alpV_eq_map D.E]
  exact Subgroup.mem_map_of_mem _ (mem_Vsub.2 (fE_d i))

theorem st_eq : s * t = D.E.φ stE := (AlpEmb.φ_stE D.E).symm

theorem st_mem_P : s * t ∈ alpP v1 v2 v3 s t := by
  rw [D.st_eq]
  exact AlpEmb.φ_mem D.E _

theorem st_sq : s * t * (s * t) = 1 := by
  rw [D.st_eq, ← map_mul, stE_sq, map_one]

theorem st_not_mem_V : s * t ∉ alpV v1 v2 v3 := by
  rw [D.st_eq, AlpEmb.alpV_eq_map D.E, Subgroup.mem_map_iff_mem D.E.inj, mem_Vsub, stE_d]
  decide

theorem st_mem_K (i : Fin 2) : s * t ∈ centralizer ({D.fG i} : Set G) := by
  rw [mem_centralizer_singleton_iff, D.st_eq, fG, ← map_mul, ← map_mul, fE_st i]

theorem fG_sq (i : Fin 2) : D.fG i * D.fG i = v1 ^ 2 * v2 ^ 2 := by
  rw [fG, ← map_mul, fE_sq i, map_mul, map_pow, map_pow, AlpEmb.φ_v1 D.E, AlpEmb.φ_v2 D.E]

theorem orderOf_fG (i : Fin 2) : orderOf (D.fG i) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [fG, orderOf_injective D.E.φ D.E.inj]
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using fE_sq_ne_one i)
    (by simpa using fE_pow_four i)

theorem V_le_K (i : Fin 2) : alpV v1 v2 v3 ≤ centralizer ({D.fG i} : Set G) := fun _ hv =>
  mem_centralizer_singleton_iff.2
    (mem_centralizer_iff.1 (D.V_le_centralizer_V hv) _ (D.fG_mem_V i)).symm

theorem mem_zpowers_fG_iff (i : Fin 2) {x : G} :
    x ∈ zpowers (D.fG i) ↔ ∃ k : Fin 4, D.fG i ^ (k : ℕ) = x := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, D.orderOf_fG i, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, Finset.mem_range.1 hk⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, Finset.mem_range.2 k.2, rfl⟩

@[expose] def A0G (i : Fin 2) : Subgroup G := (A0E i).map D.E.φ

theorem A0G_le_V (i : Fin 2) : D.A0G i ≤ alpV v1 v2 v3 := by
  rw [A0G, AlpEmb.alpV_eq_map D.E]
  exact Subgroup.map_mono fun y hy => mem_Vsub.2 hy.1

theorem card_A0G (i : Fin 2) : Nat.card (D.A0G i) = 16 := by
  rw [A0G, AlpEmb.card_map D.E, card_A0E]

theorem mem_A0G_iff (i : Fin 2) {v : G} (hv : v ∈ alpV v1 v2 v3) :
    v ∈ D.A0G i ↔ v * v ∈ zpowers (D.fG i) := by
  rw [AlpEmb.alpV_eq_map D.E] at hv
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hv
  rw [A0G, Subgroup.mem_map_iff_mem D.E.inj, mem_A0E, InA0, D.mem_zpowers_fG_iff i]
  have hyd : y.d = 0 := hy
  simp only [hyd, true_and, fG, ← map_mul, ← map_pow, D.E.inj.eq_iff]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

theorem zpowers_le_A0G (i : Fin 2) : zpowers (D.fG i) ≤ D.A0G i := by
  intro x hx
  have hxV : x ∈ alpV v1 v2 v3 := (zpowers_le.2 (D.fG_mem_V i)) hx
  rw [D.mem_A0G_iff i hxV]
  exact mul_mem hx hx

abbrev KG (i : Fin 2) : Subgroup G := centralizer ({D.fG i} : Set G)

abbrev ZG (i : Fin 2) : Subgroup (D.KG i) := zpowers (zIn (D.fG i))

abbrev πG (i : Fin 2) : D.KG i →* D.KG i ⧸ D.ZG i := QuotientGroup.mk' (D.ZG i)

abbrev barG (i : Fin 2) (H : Subgroup G) : Subgroup (D.KG i ⧸ D.ZG i) :=
  (H.subgroupOf (D.KG i)).map (D.πG i)

theorem mem_ZG_iff {i : Fin 2} (x : D.KG i) : x ∈ D.ZG i ↔ (x : G) ∈ zpowers (D.fG i) := by
  rw [ZG, mem_zpowers_iff, mem_zpowers_iff]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m, by simp [zIn]⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, Subtype.ext (by simpa [zIn] using hm)⟩

theorem πG_eq_one_iff {i : Fin 2} (x : D.KG i) :
    D.πG i x = 1 ↔ (x : G) ∈ zpowers (D.fG i) := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, D.mem_ZG_iff]

theorem mem_barG {i : Fin 2} {H : Subgroup G} {q : D.KG i ⧸ D.ZG i} :
    q ∈ D.barG i H ↔ ∃ x : D.KG i, (x : G) ∈ H ∧ D.πG i x = q := by
  simp only [barG, Subgroup.mem_map, mem_subgroupOf]

theorem mem_barG_of {i : Fin 2} {H : Subgroup G} {x : D.KG i} (hx : (x : G) ∈ H) :
    D.πG i x ∈ D.barG i H := D.mem_barG.2 ⟨x, hx, rfl⟩

abbrev jG (i : Fin 2) : D.KG i ⧸ D.ZG i := D.πG i ⟨s * t, D.st_mem_K i⟩

theorem mem_V_or_of_mem_K {i : Fin 2} {x : G} (hxP : x ∈ alpP v1 v2 v3 s t)
    (hxK : x ∈ centralizer ({D.fG i} : Set G)) :
    x ∈ alpV v1 v2 v3 ∨ x * (s * t) ∈ alpV v1 v2 v3 := by
  obtain ⟨y, rfl⟩ := (AlpEmb.mem_alpP_iff D.E).1 hxP
  rw [mem_centralizer_singleton_iff, fG, ← map_mul, ← map_mul, D.E.inj.eq_iff,
    mul_comm_iff_of_d_zero _ _ (fE_d i), fE_cent_d] at hxK
  rw [D.st_eq, ← map_mul, AlpEmb.alpV_eq_map D.E, Subgroup.mem_map_iff_mem D.E.inj,
    Subgroup.mem_map_iff_mem D.E.inj, mem_Vsub, mem_Vsub, mul_d, stE_d]
  rcases hxK with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [h]; rfl)

theorem exists_model_V {v : G} (hv : v ∈ alpV v1 v2 v3) :
    ∃ a b c : ZMod 4, D.E.φ ⟨0, a, b, c⟩ = v := by
  rw [AlpEmb.alpV_eq_map D.E] at hv
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hv
  exact ⟨y.v0, y.v1, y.v2, by rw [← eta_of_d_zero (mem_Vsub.1 hy)]⟩

theorem invSetting_fG (i : Fin 2) :
    InvSetting (D.barG i (alpP v1 v2 v3 s t ⊓ centralizer ({D.fG i} : Set G)))
      (D.barG i (alpV v1 v2 v3)) (D.barG i (D.A0G i)) (D.jG i) where
  CS := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := D.mem_barG.1 hq
    exact D.mem_barG_of ⟨D.V_le_P hx, x.2⟩
  S_cov := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := D.mem_barG.1 hq
    rcases D.mem_V_or_of_mem_K hx.1 x.2 with h | h
    · exact Or.inl (D.mem_barG_of h)
    · right
      rw [← map_mul]
      exact D.mem_barG_of h
  C_comm := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := D.mem_barG.1 ha
    obtain ⟨y, hy, rfl⟩ := D.mem_barG.1 hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((mem_centralizer_iff.1 (D.V_le_centralizer_V hy) _ hx))
  AC := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := D.mem_barG.1 hq
    exact D.mem_barG_of (D.A0G_le_V i hx)
  A_of := by
    intro q hq hqq
    obtain ⟨x, hx, rfl⟩ := D.mem_barG.1 hq
    rw [← map_mul, D.πG_eq_one_iff] at hqq
    exact D.mem_barG_of ((D.mem_A0G_iff i hx).2 hqq)
  A_sq := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := D.mem_barG.1 hq
    rw [← map_mul, D.πG_eq_one_iff]
    exact (D.mem_A0G_iff i (D.A0G_le_V i hx)).1 hx
  S_sq := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := D.mem_barG.1 hq
    rw [← map_mul]
    refine D.mem_barG_of ?_
    obtain ⟨y, hy⟩ := (AlpEmb.mem_alpP_iff D.E).1 hx.1
    have hxK := x.2
    rcases D.mem_V_or_of_mem_K hx.1 hxK with hV | hV
    · have hxxV : (x : G) * x ∈ alpV v1 v2 v3 := mul_mem hV hV
      rw [show ((x * x : D.KG i) : G) = (x : G) * x from rfl, D.mem_A0G_iff i hxxV]
      have h4 : (x : G) * x * ((x : G) * x) = 1 := by
        rw [← hy, ← map_mul, ← map_mul, ← map_one D.E.φ]
        congr 1
        have hyd : y.d = 0 := by
          rw [← hy, AlpEmb.alpV_eq_map D.E, Subgroup.mem_map_iff_mem D.E.inj] at hV
          exact hV
        have := pow_four_of_mem_V D.hF hyd
        rw [← this]
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [h4]
      exact one_mem _
    · have hyd : y.d = 5 := by
        rw [← hy, D.st_eq, ← map_mul, AlpEmb.alpV_eq_map D.E,
          Subgroup.mem_map_iff_mem D.E.inj, mem_Vsub, mul_d, stE_d] at hV
        revert hV
        generalize y.d = d
        decide +revert
      have hy' : y = ⟨5, y.v0, y.v1, y.v2⟩ := by ext <;> simp [hyd]
      have hA : InA0 i (y * y) := by rw [hy']; exact fE_sq_st i _ _ _
      show (x : G) * x ∈ D.A0G i
      rw [← hy, ← map_mul]
      exact Subgroup.mem_map_of_mem _ hA
  jS := D.mem_barG_of ⟨D.st_mem_P, D.st_mem_K i⟩
  jC := by
    intro hj
    obtain ⟨x, hx, hxj⟩ := D.mem_barG.1 hj
    have hxj' : (QuotientGroup.mk x : D.KG i ⧸ D.ZG i) =
        QuotientGroup.mk (⟨s * t, D.st_mem_K i⟩ : D.KG i) := hxj
    have hxj'' := (D.mem_ZG_iff _).1 (QuotientGroup.eq.1 hxj')
    have h1 : (x : G)⁻¹ * (s * t) ∈ alpV v1 v2 v3 :=
      (zpowers_le.2 (D.fG_mem_V i)) hxj''
    have h2 := mul_mem hx h1
    rw [mul_inv_cancel_left] at h2
    exact D.st_not_mem_V h2
  j2 := by
    rw [← map_mul, D.πG_eq_one_iff]
    exact (show ((⟨s * t, D.st_mem_K i⟩ * ⟨s * t, D.st_mem_K i⟩ : D.KG i) : G) = 1 from
      D.st_sq) ▸ one_mem _
  jN := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := D.mem_barG.1 hq
    rw [← map_mul, ← map_mul]
    refine D.mem_barG_of ?_
    have h := AlpEmb.alpV_normal D.E D.st_mem_P hx
    have hinv : (s * t)⁻¹ = s * t := inv_eq_of_mul_eq_one_right D.st_sq
    rw [hinv] at h
    exact h
  jA := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := D.mem_barG.1 hq
    obtain ⟨a, b, c, habc⟩ := D.exists_model_V (D.A0G_le_V i hx)
    have hA : InA0 i ⟨0, a, b, c⟩ := by
      rw [A0G, ← habc, Subgroup.mem_map_iff_mem D.E.inj] at hx
      exact hx
    obtain ⟨k, hk⟩ := fE_st_A0 i a b c hA
    have hG : s * t * (x : G) * (s * t) * (x : G)⁻¹ = D.fG i ^ (k : ℕ) := by
      rw [D.st_eq, ← habc, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hk, map_pow]
      rfl
    have h1 : D.πG i (⟨s * t, D.st_mem_K i⟩ * x * ⟨s * t, D.st_mem_K i⟩ * x⁻¹) = 1 := by
      rw [D.πG_eq_one_iff]
      refine (D.mem_zpowers_fG_iff i).2 ⟨k, ?_⟩
      rw [← hG]
      simp
    rw [map_mul, map_mul, map_mul, map_inv, mul_inv_eq_one] at h1
    have hj2 : D.jG i * D.jG i = 1 := by
      rw [← map_mul, D.πG_eq_one_iff]
      exact (show ((⟨s * t, D.st_mem_K i⟩ * ⟨s * t, D.st_mem_K i⟩ : D.KG i) : G) = 1 from
        D.st_sq) ▸ one_mem _
    calc D.πG i x * D.jG i = D.jG i * (D.jG i * D.πG i x * D.jG i) := by
          rw [← mul_assoc, ← mul_assoc, hj2, one_mul]
      _ = D.jG i * D.πG i x := by rw [h1]
  comm_mem := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := D.mem_barG.1 hq
    obtain ⟨a, b, c, habc⟩ := D.exists_model_V hx
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    refine D.mem_barG_of ?_
    show (x : G) * (s * t) * (x : G)⁻¹ * (s * t) ∈ D.A0G i
    rw [D.st_eq, ← habc, ← map_inv, ← map_mul, ← map_mul, ← map_mul, A0G]
    exact Subgroup.mem_map_of_mem _ (fE_comm_mem i a b c)
  comm_surj := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := D.mem_barG.1 hq
    obtain ⟨a, b, c, habc⟩ := D.exists_model_V (D.A0G_le_V i hx)
    have hA : InA0 i ⟨0, a, b, c⟩ := by
      rw [A0G, ← habc, Subgroup.mem_map_iff_mem D.E.inj] at hx
      exact hx
    obtain ⟨a', b', c', k, hk⟩ := fE_comm_surj i a b c hA
    set v' : G := D.E.φ ⟨0, a', b', c'⟩ with hv'
    have hv'V : v' ∈ alpV v1 v2 v3 := by
      rw [AlpEmb.alpV_eq_map D.E]
      exact Subgroup.mem_map_of_mem _ (mem_Vsub.2 rfl)
    refine ⟨D.πG i ⟨v', D.V_le_K i hv'V⟩, D.mem_barG_of hv'V, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq, D.mem_ZG_iff]
    have hG : v' * (s * t) * v'⁻¹ * (s * t) = (x : G) * D.fG i ^ (k : ℕ) := by
      rw [hv', D.st_eq, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hk, map_mul, habc, fG,
        map_pow]
    refine ⟨-(k : ℤ), ?_⟩
    show D.fG i ^ (-(k : ℤ)) = ((⟨v', D.V_le_K i hv'V⟩ * ⟨s * t, D.st_mem_K i⟩ *
      ⟨v', D.V_le_K i hv'V⟩⁻¹ * ⟨s * t, D.st_mem_K i⟩ : D.KG i)⁻¹ * x : D.KG i)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hG]
    group

theorem card_P_inf_K (i : Fin 2) :
    Nat.card (alpP v1 v2 v3 s t ⊓ centralizer ({D.fG i} : Set G) : Subgroup G) = 128 := by
  rw [fG, AlpEmb.inf_centralizer_eq_map D.E, AlpEmb.card_map D.E, card_centralizer_fE]

theorem isSylowOf_centralizer_fG (hAB : ¬ D.Fus 0 1) (i : Fin 2) :
    IsSylowOf 2 (alpP v1 v2 v3 s t ⊓ centralizer ({D.fG i} : Set G))
      (centralizer ({D.fG i} : Set G)) := by
  refine isSylowOf_of_card_le D.isSylowOf_P (D.V_le_P (D.fG_mem_V i)) fun g hg => ?_
  rw [D.card_P_inf_K i]
  obtain ⟨y, hy⟩ := (AlpEmb.mem_alpP_iff D.E).1 hg
  rw [← hy, AlpEmb.inf_centralizer_eq_map D.E, AlpEmb.card_map D.E]
  have hsq : D.E.φ (y * y) = g⁻¹ * invRep v1 v2 v3 s t 1 * g := by
    rw [map_mul, hy, show invRep v1 v2 v3 s t 1 = D.fG i * D.fG i by rw [D.fG_sq i]; rfl]
    group
  by_cases hyd : y.d = 0
  · refine card_centralizer_le_128 hyd (fun h1 => D.rep_ne_one 1 ?_) (fun hz => hAB ?_)
    · rw [h1, map_one] at hsq
      calc invRep v1 v2 v3 s t 1 = g * (g⁻¹ * invRep v1 v2 v3 s t 1 * g) * g⁻¹ := by group
        _ = 1 := by rw [← hsq]; group
    · rw [hz, AlpEmb.φ_zc D.E] at hsq
      exact Fus.symm D ⟨g, hsq.symm⟩
  · exact (card_centralizer_le D.hF hyd).trans (by norm_num)

theorem isSylowOf_bar (hAB : ¬ D.Fus 0 1) (i : Fin 2) :
    IsSylowOf 2 (D.barG i (alpP v1 v2 v3 s t ⊓ centralizer ({D.fG i} : Set G))) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := D.isSylowOf_centralizer_fG hAB i
  have hT' : (T : Subgroup (D.KG i)) =
      (alpP v1 v2 v3 s t ⊓ centralizer ({D.fG i} : Set G)).subgroupOf (D.KG i) := by
    rw [← hT]
    exact (Subgroup.comap_map_eq_self_of_injective (D.KG i).subtype_injective _).symm
  have h := isSylowOf_top (T.mapSurjective (QuotientGroup.mk'_surjective (D.ZG i)))
  rwa [Sylow.coe_mapSurjective, hT'] at h

theorem card_barA0 (i : Fin 2) : Nat.card (D.barG i (D.A0G i)) = 4 := by
  have h1 := relIndex_ker ((D.A0G i).subgroupOf (D.KG i)) (D.πG i)
  rw [QuotientGroup.ker_mk'] at h1
  rw [barG, ← h1]
  have h2 := relIndex_mul_card (H := D.ZG i) (K := (D.A0G i).subgroupOf (D.KG i))
  have hle : D.ZG i ≤ (D.A0G i).subgroupOf (D.KG i) := by
    intro x hx
    rw [mem_subgroupOf]
    exact D.zpowers_le_A0G i ((D.mem_ZG_iff x).1 hx)
  rw [inf_of_le_left hle] at h2
  have hZ : Nat.card (D.ZG i) = 4 := by
    rw [ZG, Nat.card_zpowers, ← orderOf_coe, ← D.orderOf_fG i]
    rfl
  have hA : Nat.card ((D.A0G i).subgroupOf (D.KG i)) = 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe ((D.A0G_le_V i).trans (D.V_le_K i))).toEquiv,
      D.card_A0G i]
  rw [hZ, hA] at h2
  omega

theorem conj_st_not_mem_V (hAB : ¬ D.Fus 0 1) (i : Fin 2) {k : G}
    (hk : k ∈ centralizer ({D.fG i} : Set G)) : k⁻¹ * (s * t) * k ∉ alpV v1 v2 v3 := by
  intro hV
  apply (D.invSetting_fG i).not_conj_mem (D.isSylowOf_bar hAB i) (D.card_barA0 i)
    (D.πG i ⟨k, hk⟩)
  rw [← map_inv, ← map_mul, ← map_mul]
  exact D.mem_barG_of hV

end FusCtx

end CFSG.OddStandard.ONanRec
