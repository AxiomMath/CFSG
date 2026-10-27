module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH4Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Input
public import CFSG.Adapters.GeneralizedFitting
import CFSG.Walter.Cited.OddQuotient

public section

namespace CFSG.EvenSporadicStandard.M24Std.CU43

open Subgroup CFSG.Open

theorem arith_two_pow (b m : ℕ) (h : 2 ^ b = m ∨ 2 ^ b = 3 * m)
    (hm : m = 1 ∨ m = 2 ∨ m = 360 ∨ m = 720 ∨ m = 1440) : 2 ^ b ≤ 2 := by
  have h3 : ¬ 3 ∣ 2 ^ b := fun h' => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h'
    omega
  rcases h with h | h
  · rcases hm with rfl | rfl | rfl | rfl | rfl
    · omega
    · omega
    all_goals exact absurd (by rw [h]; norm_num) h3
  · exact absurd (by rw [h]; exact Dvd.intro _ rfl) h3

variable {Y : Type} [Group Y] [Finite Y] (O : Subgroup Y) [O.Normal]

theorem normal_twoGroup_eq_bot (hO : Odd (Nat.card O)) {z : Y} (hz : z * z = 1) (hz1 : z ≠ 1)
    (φ : centralizer ({z} : Set Y) →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6))
    (hφ : Function.Surjective φ) (hk : Nat.card φ.ker = 3)
    (hP : Nat.card (centralizer ({z} : Set Y)) = 4320)
    (E : Subgroup (Y ⧸ O)) [E.Normal] (hEs : IsSimpleGroup E) (hEcard : Nat.card E = 3265920)
    (W : Subgroup (Y ⧸ O)) [W.Normal] (hW2 : IsPGroup 2 W) : W = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ζ : Y ⧸ O := QuotientGroup.mk' O z with hζdef
  have hζ2 : ζ * ζ = 1 := by rw [hζdef, ← map_mul, hz, map_one]
  have hζ1 : ζ ≠ 1 := fun h =>
    hz1 (eq_one_of_sq_of_mem_odd hO hz ((QuotientGroup.eq_one_iff z).1 h))
  have hcop : centralizer ({ζ} : Set (Y ⧸ O)) ≤
      (centralizer ({z} : Set Y)).map (QuotientGroup.mk' O) :=
    CFSG.Walter.Suzuki.centralizer_mk_le_map O hO hz
  let ρ : centralizer ({z} : Set Y) →* Y ⧸ O :=
    (QuotientGroup.mk' O).comp (centralizer ({z} : Set Y)).subtype
  have hρ : ∀ p, ρ p = QuotientGroup.mk' O (p : Y) := fun p => rfl
  have hrange : ρ.range = centralizer ({ζ} : Set (Y ⧸ O)) := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      rw [hρ, mem_centralizer_singleton_iff]
      have := mem_centralizer_singleton_iff.1 p.2
      rw [hζdef, ← map_mul, ← map_mul, this]
    · intro ω hω
      obtain ⟨p, hp, rfl⟩ := hcop hω
      exact ⟨⟨p, hp⟩, hρ ⟨p, hp⟩⟩
  have hodd : Odd (Nat.card (QuotientGroup.mk' O).ker) := by
    rw [QuotientGroup.ker_mk']
    exact hO
  have hρker : ρ.ker ≤ φ.ker := fun p hp =>
    CResH4.map_eq_one_of_odd_ker (QuotientGroup.mk' O) hodd φ hφ p (by rwa [← hρ])
  have hρcard : Nat.card ρ.range ≤ 4320 :=
    (Nat.le_of_dvd (by norm_num) (hP ▸ Subgroup.card_range_dvd ρ))
  by_contra hWne
  have hWE : Disjoint W E := by
    rw [disjoint_iff]
    have hn : ((W ⊓ E).subgroupOf E).Normal := Subgroup.Normal.subgroupOf inferInstance E
    rcases hEs.eq_bot_or_eq_top_of_normal ((W ⊓ E).subgroupOf E) with h | h
    · rw [eq_bot_iff]
      intro x hx
      rw [mem_bot]
      have hxE := (mem_inf.1 hx).2
      have : (⟨x, hxE⟩ : E) ∈ (W ⊓ E).subgroupOf E := mem_subgroupOf.2 hx
      rw [h, mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      have hEW : E ≤ W := fun x hx => (mem_inf.1 (by
        have : (⟨x, hx⟩ : E) ∈ (W ⊓ E).subgroupOf E := by rw [h]; exact mem_top _
        exact mem_subgroupOf.1 this)).1
      obtain ⟨n, hn'⟩ := IsPGroup.iff_card.1 (hW2.to_le hEW)
      rw [hEcard] at hn'
      have h3 : 3 ∣ 2 ^ n := hn' ▸ (by norm_num : 3 ∣ 3265920)
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
  have hcommWE : ∀ w ∈ W, ∀ e ∈ E, w * e = e * w := fun w hw e he =>
    (Subgroup.commute_of_normal_of_disjoint W E inferInstance inferInstance hWE w e hw he).eq
  have hζp : IsPGroup 2 (zpowers ζ) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, orderOf_eq_prime (by rwa [sq]) hζ1]
    norm_num
  obtain ⟨S, hS⟩ := hζp.exists_le_sylow
  have hWS : W ≤ (S : Subgroup (Y ⧸ O)) := hW2.le_sylow_of_normal S
  have hζS : ζ ∈ (S : Subgroup (Y ⧸ O)) := hS (mem_zpowers ζ)
  have hSnil : Group.IsNilpotent (S : Subgroup (Y ⧸ O)) := S.isPGroup'.isNilpotent
  have hW'ne : W.subgroupOf (S : Subgroup (Y ⧸ O)) ≠ ⊥ := by
    intro h
    apply hWne
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    have : (⟨x, hWS hx⟩ : (S : Subgroup (Y ⧸ O))) ∈ W.subgroupOf (S : Subgroup (Y ⧸ O)) :=
      mem_subgroupOf.2 hx
    rw [h, mem_bot] at this
    exact congrArg Subtype.val this
  have hW'n : (W.subgroupOf (S : Subgroup (Y ⧸ O))).Normal :=
    Subgroup.Normal.subgroupOf inferInstance _
  obtain ⟨⟨⟨w, hwS⟩, hwmem⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hW'ne))
  have hwW : w ∈ W := mem_subgroupOf.1 (mem_inf.1 hwmem).1
  have hwc : w * ζ = ζ * w := by
    have := mem_center_iff.1 (mem_inf.1 hwmem).2 ⟨ζ, hζS⟩
    have h2 := congrArg Subtype.val this
    exact h2.symm
  have hw1' : w ≠ 1 := fun h1 => hw1 (Subtype.ext (Subtype.ext h1))
  set Cζ := centralizer ({ζ} : Set (Y ⧸ O)) with hCζ
  set U : Subgroup (Y ⧸ O) := W ⊓ Cζ with hU
  have hwU : w ∈ U := mem_inf.2 ⟨hwW, mem_centralizer_singleton_iff.2 hwc⟩
  set V : Subgroup (Y ⧸ O) := U ⊔ zpowers ζ with hV
  have hζC : ζ ∈ Cζ := mem_centralizer_singleton_iff.2 rfl
  have hVC : V ≤ Cζ := sup_le inf_le_right (zpowers_le.2 hζC)
  have hVS : V ≤ (S : Subgroup (Y ⧸ O)) := sup_le (inf_le_left.trans hWS) hS
  have hVp : IsPGroup 2 V := S.isPGroup'.to_le hVS
  have hVn : ∀ ω ∈ ρ.range, ∀ n ∈ V, ω * n * ω⁻¹ ∈ V := by
    intro ω hω n hn
    have hωC : ω ∈ Cζ := hrange ▸ hω
    have h1 : V.map (MulAut.conj ω).toMonoidHom ≤ V := by
      rw [hV, Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨m, hm, rfl⟩
        refine mem_inf.2 ⟨Normal.conj_mem inferInstance m (mem_inf.1 hm).1 ω,
          mul_mem (mul_mem hωC (mem_inf.1 hm).2) (inv_mem hωC)⟩
      · rw [MonoidHom.map_zpowers, zpowers_le]
        have : (MulAut.conj ω).toMonoidHom ζ = ζ := by
          show ω * ζ * ω⁻¹ = ζ
          rw [mul_inv_eq_iff_eq_mul]
          exact mem_centralizer_singleton_iff.1 hωC
        rw [this]
        exact mem_zpowers ζ
    exact h1 ⟨n, hn, rfl⟩
  have hVr : V ≤ ρ.range := hrange ▸ hVC
  have hVcn : (V.comap ρ).Normal := CResH4.normal_comap_of_normalized ρ V hVn
  have hMn : ((V.comap ρ).map φ).Normal := hVcn.map φ hφ
  have h1 := CResH4.card_eq_or_card_eq_three_mul_card_map_comap ρ φ hρker hk V hVr
  have h2 := CResH4.card_normal_z2s6 _ hMn
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hVp
  have hV2 : Nat.card V ≤ 2 := by
    rw [hb] at h1 ⊢
    exact arith_two_pow b _ h1 h2
  have hζV : ζ ∈ V := mem_sup_right (mem_zpowers ζ)
  have hzp2 : Nat.card (zpowers ζ) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rwa [sq]) hζ1]
  have hVeq : V = zpowers ζ :=
    (eq_of_le_of_card_ge (zpowers_le.2 hζV) (by rw [hzp2]; exact hV2)).symm
  have hwV : w ∈ zpowers ζ := hVeq ▸ mem_sup_left hwU
  have hwζ : w = ζ := by
    rcases CResH4.eq_one_or_eq_of_mem_zpowers hζ2 hζ1 hwV with h | h
    · exact absurd h hw1'
    · exact h
  have hζW : ζ ∈ W := hwζ ▸ hwW
  have hEC : E ≤ ρ.range := by
    intro e he
    rw [hrange]
    exact mem_centralizer_singleton_iff.2 (hcommWE ζ hζW e he).symm
  have := Subgroup.card_le_of_le hEC
  omega

theorem centralizer_layer_eq_bot (hO : Odd (Nat.card O))
    (hX : ∀ N : Subgroup (Y ⧸ O), N.Normal → Odd (Nat.card N) → N = ⊥) {z : Y} (hz : z * z = 1)
    (hz1 : z ≠ 1)
    (φ : centralizer ({z} : Set Y) →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6))
    (hφ : Function.Surjective φ) (hk : Nat.card φ.ker = 3)
    (hP : Nat.card (centralizer ({z} : Set Y)) = 4320)
    (E : Subgroup (Y ⧸ O)) [E.Normal] (hlayer : egaLayer (Y ⧸ O) = E) (hEs : IsSimpleGroup E)
    (hEcard : Nat.card E = 3265920) : centralizer (E : Set (Y ⧸ O)) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpp : CFSG.pPrimeCore 2 (Y ⧸ O) = ⊥ := by
    apply le_bot_iff.1
    refine sSup_le fun K ⟨hKn, hKc⟩ => ?_
    exact (hX K hKn (Nat.coprime_two_left.1 hKc)).le
  have hF : genFittingFitting (Y ⧸ O) = ⊥ := by
    apply le_bot_iff.1
    refine sSup_le fun N ⟨hNn, hNnil⟩ => ?_
    have := hNn
    have hN2 : IsPGroup 2 N := CFSG.isPGroup_of_nilpotent_normal N hNn hNnil hpp
    exact (normal_twoGroup_eq_bot O hO hz hz1 φ hφ hk hP E hEs hEcard N hN2).le
  have hlay : genFittingLayer (Y ⧸ O) = E := by
    rw [← hlayer, egaLayer, genFittingLayer, sSup_eq_iSup]
    rfl
  have hFstar : genFittingFStar (Y ⧸ O) = E := by
    rw [genFittingFStar, hF, hlay, bot_sup_eq]
  have hself := CFSG.Adapters.generalized_fitting_self_centralizing (Y ⧸ O)
  rw [hFstar] at hself
  have hcenter : center E = ⊥ := by
    rcases hEs.eq_bot_or_eq_top_of_normal (center E) with h | h
    · exact h
    · have hc : IsMulCommutative E := Subgroup.center_eq_top_iff.1 h
      have hp := Group.is_simple_iff_prime_card.1 hEs
      rw [hEcard] at hp
      norm_num at hp
  rw [eq_bot_iff]
  intro x hx
  have hxE : x ∈ E := hself hx
  have hmem : (⟨x, hxE⟩ : E) ∈ center E := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 hx g g.2)
  rw [hcenter, mem_bot] at hmem
  rw [mem_bot]
  exact congrArg Subtype.val hmem

end CFSG.EvenSporadicStandard.M24Std.CU43
