module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Finite.Perm
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ReeL28

open Subgroup

theorem index_modEq_one {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (P : Sylow p G) {H : Subgroup G}
    (hH : normalizer ((P : Subgroup G) : Set G) ≤ H) : H.index ≡ 1 [MOD p] := by
  have hPH : (P : Subgroup G) ≤ H := le_normalizer.trans hH
  let P' : Sylow p H := P.subtype hPH
  have hG : Nat.card (Sylow p G) = (normalizer ((P : Subgroup G) : Set G)).index :=
    P.card_eq_index_normalizer
  have hH' : Nat.card (Sylow p H) = (normalizer ((P' : Subgroup H) : Set H)).index :=
    P'.card_eq_index_normalizer
  have hN : normalizer ((P' : Subgroup H) : Set H) =
      (normalizer ((P : Subgroup G) : Set G)).subgroupOf H :=
    (Subgroup.subgroupOf_normalizer_eq hPH).symm
  have hrel := Subgroup.relIndex_mul_index hH
  have h1 : Nat.card (Sylow p G) = Nat.card (Sylow p H) * H.index := by
    rw [hG, hH', hN]
    exact hrel.symm
  have hm1 : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
  have hm2 : Nat.card (Sylow p H) ≡ 1 [MOD p] := card_sylow_modEq_one p H
  have h3 : Nat.card (Sylow p H) * H.index ≡ 1 * H.index [MOD p] := hm2.mul_right _
  rw [one_mul, ← h1] at h3
  exact h3.symm.trans hm1

theorem eq_sup_of_card_504 {G : Type*} [Group G] [Finite G] {H T : Subgroup G} {z : G}
    (hH : Nat.card H = 504) (hTH : T ≤ H) (hT : Nat.card T = 8) (hz : z ∈ H)
    (hz7 : orderOf z = 7) : H = (normalizer (zpowers z : Set G) ⊓ H) ⊔ T := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set J : Subgroup G := (normalizer (zpowers z : Set G) ⊓ H) ⊔ T with hJ
  have hJH : J ≤ H := sup_le inf_le_right hTH
  have hzH : zpowers z ≤ H := Subgroup.zpowers_le.mpr hz
  let P0 : Subgroup ↥H := (zpowers z).subgroupOf H
  have hP0card : Nat.card P0 = 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzH).toEquiv, Nat.card_zpowers, hz7]
  have hP0p : IsPGroup 7 P0 := IsPGroup.of_card (n := 1) (by rw [hP0card]; norm_num)
  have hP0idx : ¬ 7 ∣ P0.index := by
    have h := Subgroup.card_mul_index P0
    rw [hP0card, hH] at h
    have : P0.index = 72 := by omega
    rw [this]
    norm_num
  let P : Sylow 7 ↥H := hP0p.toSylow hP0idx
  have hNJ : normalizer ((P : Subgroup ↥H) : Set ↥H) ≤ J.subgroupOf H := by
    have hN : normalizer ((P : Subgroup ↥H) : Set ↥H) =
        (normalizer (zpowers z : Set G)).subgroupOf H :=
      (Subgroup.subgroupOf_normalizer_eq hzH).symm
    rw [hN]
    intro g hg
    exact (le_sup_left : normalizer (zpowers z : Set G) ⊓ H ≤ J) ⟨hg, g.2⟩
  have hmod : (J.subgroupOf H).index ≡ 1 [MOD 7] := index_modEq_one P hNJ
  have h8 : 8 ∣ Nat.card J := hT ▸ Subgroup.card_dvd_of_le (le_sup_right : T ≤ J)
  have h7 : 7 ∣ Nat.card J := by
    have hzJ : z ∈ J := (le_sup_left : normalizer (zpowers z : Set G) ⊓ H ≤ J)
      ⟨Subgroup.le_normalizer (Subgroup.mem_zpowers z), hz⟩
    exact hz7 ▸ Subgroup.orderOf_dvd_natCard J hzJ
  have hrel : (J.subgroupOf H).index * Nat.card J = 504 := by
    have := Subgroup.relIndex_mul_card J H
    rw [inf_eq_left.mpr hJH, hH] at this
    exact this
  obtain ⟨c, hc⟩ : 8 * 7 ∣ Nat.card J :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h8 h7
  rw [hc] at hrel
  have hidx9 : (J.subgroupOf H).index * c = 9 := by nlinarith
  have hle : (J.subgroupOf H).index ≤ 9 := Nat.le_of_dvd (by norm_num) ⟨c, hidx9.symm⟩
  have hidx : (J.subgroupOf H).index = 1 := by
    generalize (J.subgroupOf H).index = i at hmod hidx9 hle
    unfold Nat.ModEq at hmod
    interval_cases i <;> omega
  have hHJ : H ≤ J := Subgroup.relIndex_eq_one.mp hidx
  exact le_antisymm hHJ hJH

theorem not_dvd_card_normalizer {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    (hS8 : Nat.card S = 8) (hC : ∀ x : G, (∀ s ∈ S, x * s = s * x) → x ∈ S) :
    ¬ 49 ∣ Nat.card (normalizer (S : Set G)) := by
  classical
  set N : Subgroup G := normalizer (S : Set G) with hN
  let φ : ↥N →* Equiv.Perm ↥S := (MulAut.toPerm ↥S).comp S.normalizerMonoidHom
  have hφ : ∀ (n : ↥N) (s : ↥S), ((φ n s : ↥S) : G) = (n : G) * s * (n : G)⁻¹ := fun n s => rfl
  have hker : φ.ker ≤ S.subgroupOf N := by
    intro n hn
    rw [Subgroup.mem_subgroupOf]
    apply hC
    intro s hs
    have h := congrArg (fun f : Equiv.Perm ↥S => ((f ⟨s, hs⟩ : ↥S) : G))
      (MonoidHom.mem_ker.mp hn)
    simp only [Equiv.Perm.coe_one, id_eq] at h
    rw [hφ] at h
    calc (n : G) * s = ((n : G) * s * (n : G)⁻¹) * n := by group
      _ = s * n := by rw [h]
  have hcard : Nat.card φ.ker * Nat.card φ.range = Nat.card N := by
    have := Subgroup.card_mul_index φ.ker
    rwa [Subgroup.index_ker] at this
  have hkerdvd : Nat.card φ.ker ∣ 8 := by
    have h1 : Nat.card φ.ker ∣ Nat.card (S.subgroupOf N) := Subgroup.card_dvd_of_le hker
    have h2 : Nat.card (S.subgroupOf N) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv, hS8]
    rwa [h2] at h1
  have hrangedvd : Nat.card φ.range ∣ 40320 := by
    have h1 : Nat.card φ.range ∣ Nat.card (Equiv.Perm ↥S) := Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_perm, hS8] at h1
    exact h1
  intro h49
  have hdvd : Nat.card N ∣ 8 * 40320 := hcard ▸ Nat.mul_dvd_mul hkerdvd hrangedvd
  have := h49.trans hdvd
  norm_num at this

theorem exists_conj_mem_zpowers {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    (hS8 : Nat.card S = 8) (hC : ∀ x : G, (∀ s ∈ S, x * s = s * x) → x ∈ S)
    {z g : G} (hz : z ∈ normalizer (S : Set G)) (hz7 : orderOf z = 7)
    (hg : g ∈ normalizer (S : Set G)) (hg7 : orderOf g = 7) :
    ∃ y ∈ normalizer (S : Set G), y⁻¹ * z * y ∈ zpowers g := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set N : Subgroup G := normalizer (S : Set G) with hN
  have h49 := not_dvd_card_normalizer hS8 hC
  have hsyl : ∀ x : G, x ∈ N → orderOf x = 7 → ∃ P : Sylow 7 ↥N,
      (P : Subgroup ↥N) = (zpowers x).subgroupOf N := by
    intro x hx hx7
    have hxN : zpowers x ≤ N := Subgroup.zpowers_le.mpr hx
    let P0 : Subgroup ↥N := (zpowers x).subgroupOf N
    have hP0card : Nat.card P0 = 7 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hxN).toEquiv, Nat.card_zpowers, hx7]
    have hP0p : IsPGroup 7 P0 := IsPGroup.of_card (n := 1) (by rw [hP0card]; norm_num)
    have hP0idx : ¬ 7 ∣ P0.index := by
      intro h7
      apply h49
      have h := Subgroup.card_mul_index P0
      rw [hP0card] at h
      obtain ⟨m, hm⟩ := h7
      rw [← h, hm]
      exact ⟨m, by ring⟩
    exact ⟨hP0p.toSylow hP0idx, rfl⟩
  obtain ⟨Pz, hPz⟩ := hsyl z hz hz7
  obtain ⟨Pg, hPg⟩ := hsyl g hg hg7
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq (↥N) Pg Pz
  refine ⟨(n : G), n.2, ?_⟩
  have hzPz : (⟨z, hz⟩ : ↥N) ∈ (Pz : Subgroup ↥N) := by
    rw [hPz]
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers z)
  rw [← hn, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hPg,
    Subgroup.mem_subgroupOf] at hzPz
  exact hzPz

@[expose] def ReeL28Data (G : Type) [Group G] : Prop :=
  (∀ (S : Sylow 2 G) (x : G), (∀ s ∈ (S : Subgroup G), x * s = s * x) → x ∈ (S : Subgroup G)) ∧
  (∀ S : Sylow 2 G, Nat.card (S : Subgroup G) = 8) ∧
  ∃ (D : Subgroup G) (S : Sylow 2 G) (g : G), IsSimpleGroup D ∧ Nat.card D = 504 ∧
    (S : Subgroup G) ≤ D ∧ g ∈ D ∧ orderOf g = 7 ∧ g ∈ normalizer ((S : Subgroup G) : Set G)

theorem ReeL28Data.of_mulEquiv {G G' : Type} [Group G] [Group G'] [Finite G] (e : G ≃* G')
    (h : ReeL28Data G) : ReeL28Data G' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite G' := Finite.of_equiv G e.toEquiv
  obtain ⟨hC, h8, D, S, g, hD, hD504, hSD, hgD, hg7, hgS⟩ := h
  have hmapS : ∀ S' : Sylow 2 G', ((S'.mapSurjective (f := e.symm.toMonoidHom)
      e.symm.surjective : Sylow 2 G) : Subgroup G) = (S' : Subgroup G').map e.symm.toMonoidHom :=
    fun S' => Sylow.coe_mapSurjective _ S'
  have hmapS' : ((S.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 2 G') :
      Subgroup G') = (S : Subgroup G).map e.toMonoidHom := Sylow.coe_mapSurjective _ S
  refine ⟨?_, ?_, D.map e.toMonoidHom, S.mapSurjective (f := e.toMonoidHom) e.surjective, e g,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S' x' hx'
    have hx := hC (S'.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective) (e.symm x') (by
      intro s hs
      rw [hmapS] at hs
      obtain ⟨s', hs', rfl⟩ := hs
      have := hx' s' hs'
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, this])
    rw [hmapS] at hx
    obtain ⟨s', hs', hs'x⟩ := hx
    have : s' = x' := e.symm.injective hs'x
    rwa [← this]
  · intro S'
    have := h8 (S'.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective)
    rwa [hmapS, Subgroup.card_map_of_injective e.symm.injective] at this
  · exact (D.equivMapOfInjective e.toMonoidHom e.injective).isSimpleGroup_congr.mp hD
  · rw [Subgroup.card_map_of_injective e.injective, hD504]
  · rw [hmapS']
    exact Subgroup.map_mono hSD
  · exact Subgroup.mem_map_of_mem _ hgD
  · rw [MulEquiv.orderOf_eq e g]
    exact hg7
  · show e g ∈ normalizer (((S.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 2 G') :
      Subgroup G') : Set G')
    rw [hmapS', Subgroup.mem_normalizer_iff]
    intro y'
    obtain ⟨y, rfl⟩ := e.surjective y'
    have hn := Subgroup.mem_normalizer_iff.mp hgS y
    rw [Subgroup.mem_map_equiv, ← map_mul, ← map_inv, ← map_mul, Subgroup.mem_map_equiv]
    simpa using hn

theorem exists_sub504 {G : Type} [Group G] [Finite G] (h : ReeL28Data G) (S : Sylow 2 G) {z : G}
    (hz : z ∈ normalizer ((S : Subgroup G) : Set G)) (hz7 : orderOf z = 7) :
    ∃ H : Subgroup G, IsSimpleGroup H ∧ Nat.card H = 504 ∧ (S : Subgroup G) ≤ H ∧ z ∈ H ∧
      H = (normalizer (zpowers z : Set G) ⊓ H) ⊔ (S : Subgroup G) := by
  obtain ⟨hC, h8, D, S₀, g, hD, hD504, hSD, hgD, hg7, hgS⟩ := h
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G S₀ S
  have hSx : ∀ s : G, s ∈ (S : Subgroup G) ↔ x⁻¹ * s * x ∈ (S₀ : Subgroup G) := by
    intro s
    rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  have hg₁ : x * g * x⁻¹ ∈ normalizer ((S : Subgroup G) : Set G) := by
    refine Sylow.smul_eq_iff_mem_normalizer.mp ?_
    have hgS' : g • S₀ = S₀ := Sylow.smul_eq_iff_mem_normalizer.mpr hgS
    have hxg : x * g * x⁻¹ * x = x * g := by group
    calc (x * g * x⁻¹) • S = (x * g * x⁻¹) • (x • S₀) := by rw [hx]
      _ = x • (g • S₀) := by rw [← mul_smul, hxg, mul_smul]
      _ = S := by rw [hgS', hx]
  have hg₁7 : orderOf (x * g * x⁻¹) = 7 := by
    have := MulEquiv.orderOf_eq (MulAut.conj x) g
    rwa [MulAut.conj_apply, hg7] at this
  obtain ⟨y, hy, hyz⟩ := exists_conj_mem_zpowers (h8 S) (hC S) hz hz7 hg₁ hg₁7
  set w : G := y * x with hw
  set H : Subgroup G := D.map (MulAut.conj w).toMonoidHom with hH
  have hmem : ∀ u : G, u ∈ H ↔ w⁻¹ * u * w ∈ D := by
    intro u
    rw [hH, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hHcard : Nat.card H = 504 := by
    rw [hH, Subgroup.card_map_of_injective (MulAut.conj w).injective, hD504]
  have hHsimple : IsSimpleGroup H :=
    (D.equivMapOfInjective (MulAut.conj w).toMonoidHom (MulAut.conj w).injective
      ).isSimpleGroup_congr.mp hD
  have hSH : (S : Subgroup G) ≤ H := by
    intro s hs
    rw [hmem]
    have hsy : y⁻¹ * s * y ∈ (S : Subgroup G) := by
      have := (Subgroup.mem_normalizer_iff.mp ((normalizer ((S : Subgroup G) : Set G)).inv_mem hy)
        s).mp hs
      simpa using this
    have := hSD ((hSx _).mp hsy)
    have e : w⁻¹ * s * w = x⁻¹ * (y⁻¹ * s * y) * x := by rw [hw]; group
    rwa [e]
  have hzH : z ∈ H := by
    rw [hmem]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyz
    have e : w⁻¹ * z * w = g ^ k := by
      have h1 : (x * g * x⁻¹) ^ k = x * g ^ k * x⁻¹ := conj_zpow
      have h2 : z = y * (x * g ^ k * x⁻¹) * y⁻¹ := by
        rw [← h1, hk]; group
      rw [hw, h2]
      group
    rw [e]
    exact Subgroup.zpow_mem D hgD k
  exact ⟨H, hHsimple, hHcard, hSH, hzH, eq_sup_of_card_504 hHcard hSH (h8 S) hzH hz7⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ReeL28
