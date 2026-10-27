module

public import CFSG.LieType.BorelTits.Basic
import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphismsSupport
import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.LocalAnalysis.AGLEmbeddingD2.Reduced

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open

attribute [local instance] CFSG.LieType.BorelTits.pCore_normal

section Perm

variable {Γ : Type*} [Group Γ]

theorem nonempty_quotient_pCore_perm_three [Finite Γ] {T : Subgroup Γ} (hT : IsPGroup 2 T)
    (h3 : T.index = 3) (hn : ¬ T.Normal) :
    Nonempty (Γ ⧸ CFSG.Open.pCore 2 Γ ≃* Equiv.Perm (Fin 3)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : Γ →* Equiv.Perm (Γ ⧸ T) := MulAction.toPermHom Γ (Γ ⧸ T) with hf
  have hcard : Nat.card (Γ ⧸ T) = 3 := h3
  have hker : f.ker = T.normalCore := (Subgroup.normalCore_eq_ker T).symm
  have hkerT : f.ker ≤ T := hker ▸ T.normalCore_le
  have hker2 : IsPGroup 2 f.ker := hT.to_le hkerT
  have hrange : Nat.card f.range ∣ 6 := by
    have h := Subgroup.card_subgroup_dvd_card f.range
    rwa [Nat.card_perm, hcard, show Nat.factorial 3 = 6 by decide] at h
  have hidx : Nat.card f.range = f.ker.relIndex T * 3 := by
    rw [← Subgroup.index_ker, ← h3]
    exact (Subgroup.relIndex_mul_index hkerT).symm
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have hrel : f.ker.relIndex T = 2 := by
    rw [hidx] at hrange hpos
    have h2 : f.ker.relIndex T ∣ 2 := by
      have : f.ker.relIndex T * 3 ∣ 2 * 3 := hrange
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exfalso
      apply hn
      have hTk : T ≤ f.ker := Subgroup.relIndex_eq_one.mp h
      have : f.ker = T := le_antisymm hkerT hTk
      rw [← this]
      exact MonoidHom.normal_ker f
    · exact h
  have hrange6 : Nat.card f.range = Nat.card (Equiv.Perm (Γ ⧸ T)) := by
    rw [hidx, hrel, Nat.card_perm, hcard]
    decide
  have hsurj : Function.Surjective f :=
    MonoidHom.range_eq_top.mp ((Subgroup.card_eq_iff_eq_top _).mp hrange6)
  set ψ : Equiv.Perm (Γ ⧸ T) ≃* Equiv.Perm (Fin 3) :=
    (Finite.equivFinOfCardEq hcard).permCongrHom with hψ
  have hpc : CFSG.Open.pCore 2 Γ = f.ker := by
    refine le_antisymm ?_
      (CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker f) hker2)
    have hN : ((CFSG.Open.pCore 2 Γ).map f).Normal :=
      (CFSG.LieType.BorelTits.pCore_normal 2).map f hsurj
    have hbot : (CFSG.Open.pCore 2 Γ).map f = ⊥ :=
      CFSG.Semidihedral.Local.normal_isPGroup_two_eq_bot ψ _ hN
        ((CFSG.LieType.BorelTits.pCore_isPGroup 2).map f)
    exact (Subgroup.map_eq_bot_iff _).mp hbot
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hpc).trans
    ((QuotientGroup.quotientKerEquivOfSurjective f hsurj).trans ψ)⟩

theorem nonempty_quotient_pCore_perm_three_map {G : Type*} [Group G] (f : Γ →* G)
    (hf : Function.Injective f) (I : Subgroup Γ)
    (h : Nonempty (↥I ⧸ CFSG.Open.pCore 2 ↥I ≃* Equiv.Perm (Fin 3))) :
    Nonempty (↥(I.map f) ⧸ CFSG.Open.pCore 2 ↥(I.map f) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := h
  let σ : ↥I ≃* ↥(I.map f) := I.equivMapOfInjective f hf
  have hσ := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 σ
  exact ⟨(QuotientGroup.congr _ _ σ hσ).symm.trans e⟩

end Perm

section Invariant

variable {Γ X : Type*} [Group Γ] [Group X]

theorem exists_subgroup_card_three_invariant [Finite Γ] (φ : Γ →* X) (L : Subgroup Γ) [L.Normal]
    {y₀ : X} (hy₀ : orderOf y₀ = 3) (hmem : y₀ ∈ L.map φ)
    (hcent : ∀ l ∈ L, φ l = 1 → ∀ m ∈ L, l * m = m * l)
    (hcop : ∀ l ∈ L, φ l = 1 → Nat.Coprime 3 (orderOf l)) :
    ∃ Y : Subgroup Γ, Y ≤ L ∧ Nat.card Y = 3 ∧ y₀ ∈ Y.map φ ∧
      ∀ g : Γ, φ g ∈ Subgroup.normalizer ((Subgroup.zpowers y₀ : Subgroup X) : Set X) →
        g ∈ Subgroup.normalizer (Y : Set Γ) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxL, hxy⟩ := hmem
  set Z : Subgroup Γ := L ⊓ φ.ker with hZ
  set t := Nat.card Z with ht
  have hy₀3 : y₀ ^ 3 = 1 := by rw [← hy₀]; exact pow_orderOf_eq_one y₀
  have h3t : ¬ 3 ∣ t := by
    intro h3
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have h1 := hcop (z : Γ) z.2.1 z.2.2
    rw [Subgroup.orderOf_coe, hz] at h1
    exact absurd h1 (by norm_num)
  have hyt : y₀ ^ t ≠ 1 := fun h => h3t (hy₀ ▸ orderOf_dvd_of_pow_eq_one h)
  set y : Γ := x ^ t with hy
  have hyL : y ∈ L := L.pow_mem hxL t
  have hφy : φ y = y₀ ^ t := by rw [hy, map_pow, hxy]
  have hy3 : y ^ 3 = 1 := by
    have hx3mem : x ^ 3 ∈ Z := Subgroup.mem_inf.mpr
      ⟨L.pow_mem hxL 3, MonoidHom.mem_ker.mpr (by rw [map_pow, hxy, hy₀3])⟩
    have hx3 : (⟨x ^ 3, hx3mem⟩ : Z) ^ t = 1 := pow_card_eq_one'
    have h := congrArg Subtype.val hx3
    simpa [hy, ← pow_mul, mul_comm] using h
  have hyne : y ≠ 1 := fun h => hyt (by rw [← hφy, h, map_one])
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hyne
  have hYcard : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hord]
  have hc1 : Nat.card (Subgroup.zpowers y₀) = 3 := by rw [Nat.card_zpowers, hy₀]
  have : Finite (Subgroup.zpowers y₀) := Nat.finite_of_card_ne_zero (by rw [hc1]; norm_num)
  have hzp : Subgroup.zpowers (φ y) = Subgroup.zpowers y₀ := by
    have hle : Subgroup.zpowers (φ y) ≤ Subgroup.zpowers y₀ := by
      rw [Subgroup.zpowers_le, hφy]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers y₀) t
    have hc2 : Nat.card (Subgroup.zpowers (φ y)) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [← map_pow, hy3, map_one]) (by rw [hφy]; exact hyt)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc1, hc2])
  have hmapY : (Subgroup.zpowers y).map φ = Subgroup.zpowers y₀ := by
    rw [MonoidHom.map_zpowers, hzp]
  refine ⟨Subgroup.zpowers y, Subgroup.zpowers_le.mpr hyL, hYcard,
    hmapY ▸ Subgroup.mem_zpowers y₀, fun g hg => ?_⟩
  have hcL : g * y * g⁻¹ ∈ L := Subgroup.Normal.conj_mem inferInstance y hyL g
  have hc3 : (g * y * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hy3, mul_one, mul_inv_cancel]
  have hφc : φ (g * y * g⁻¹) ∈ Subgroup.zpowers (φ y) := by
    have h1 := (Subgroup.mem_normalizer_iff.mp hg (y₀ ^ t)).mp
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers y₀) t)
    rw [hzp, map_mul, map_mul, map_inv, hφy]
    exact h1
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hφc
  set c := g * y * g⁻¹ with hcdef
  obtain ⟨w, hwdef⟩ : ∃ w : Γ, w = c * y ^ (-i) := ⟨_, rfl⟩
  have hwker : w ∈ φ.ker := by
    rw [hwdef, MonoidHom.mem_ker, map_mul, map_zpow, ← hi, zpow_neg, mul_inv_cancel]
  have hwL : w ∈ L := hwdef ▸ L.mul_mem hcL (L.zpow_mem hyL _)
  have hwc := hcent w hwL hwker
  have hcw : c = w * y ^ i := by rw [hwdef]; group
  have hwy : w * y = y * w := hwc y hyL
  have hcy : Commute c y := by
    show c * y = y * c
    rw [hcw]
    calc w * y ^ i * y = w * (y ^ i * y) := by rw [mul_assoc]
      _ = w * (y * y ^ i) := by rw [(Commute.self_zpow y i).eq]
      _ = (w * y) * y ^ i := by rw [mul_assoc]
      _ = (y * w) * y ^ i := by rw [hwy]
      _ = y * (w * y ^ i) := by rw [mul_assoc]
  have hw3 : w ^ 3 = 1 := by
    rw [hwdef, (hcy.zpow_right (-i)).mul_pow, hc3, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hy3, one_zpow]
  have hw1 : w = 1 := by
    have h1 := hcop w hwL hwker
    have h2 : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h1.symm h2)
  have hcY : c ∈ Subgroup.zpowers y := by
    rw [hcw, hw1, one_mul]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) i
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ hcY j

end Invariant

section Lift

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem exists_card_three_of_normalizing_quotient (S : Subgroup Γ) [S.Normal] (hS : IsPGroup 2 S)
    {U : Subgroup Γ} (hSU : S ≤ U) (hU : IsPGroup 2 U) {Y : Subgroup (Γ ⧸ S)}
    (hY : Nat.card Y = 3)
    (hUY : U.map (QuotientGroup.mk' S) ≤ Subgroup.normalizer (Y : Set (Γ ⧸ S)))
    (hact : ∃ u ∈ U, ∃ y ∈ Y, QuotientGroup.mk' S u * y * (QuotientGroup.mk' S u)⁻¹ ≠ y) :
    ∃ W : Subgroup Γ, Nat.card W = 3 ∧ W.map (QuotientGroup.mk' S) = Y ∧
      U.relIndex (U ⊔ W) = 3 ∧ ¬ (U.subgroupOf (U ⊔ W)).Normal := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := QuotientGroup.mk' S with hf
  have hY3 : IsPGroup 3 Y := IsPGroup.of_card (n := 1) (by rw [hY, pow_one])
  obtain ⟨W, hW3, hWY⟩ := exists_isPGroup_map_mk_eq_of_isPGroup (p := 3) S hY3
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hScop : Nat.Coprime 3 (Nat.card S) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hWcard : Nat.card W = 3 := by
    rw [← CFSG.AGLEmbedding.card_map_mk_of_isPGroup Nat.prime_three S hScop hW3, hWY, hY]
  set N : Subgroup Γ := Y.comap f with hN
  have hWN : W ≤ N := fun w hw => by
    rw [hN, Subgroup.mem_comap, ← hWY]
    exact Subgroup.mem_map_of_mem f hw
  have hSN : S ≤ N := fun s hs => by
    have h1 : f s = 1 := (QuotientGroup.eq_one_iff s).mpr hs
    rw [hN, Subgroup.mem_comap, h1]
    exact Y.one_mem
  have hNcard : Nat.card N = Nat.card S * 3 := by
    have h1 := Subgroup.card_mul_index (Y.comap f)
    rw [Subgroup.index_comap_of_surjective Y (QuotientGroup.mk'_surjective S)] at h1
    have h2 := Subgroup.card_mul_index Y
    have h3 := Subgroup.card_mul_index S
    have hY0 : Y.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hY0)
    rw [hN, h1, ← h3, Subgroup.index_eq_card, ← h2, hY]
    ring
  have hUN : U ≤ Subgroup.normalizer (N : Set Γ) := fun u hu =>
    Subgroup.mem_normalizer_iff.mpr fun n => by
      have h := Subgroup.mem_normalizer_iff.mp (hUY (Subgroup.mem_map_of_mem f hu)) (f n)
      simp only [hN, Subgroup.mem_comap, map_mul, map_inv]
      exact h
  have hUNS : U ⊓ N = S := by
    refine le_antisymm (fun u hu => ?_) (le_inf hSU hSN)
    obtain ⟨n, hn⟩ := hU ⟨u, hu.1⟩
    have hn' : u ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have hfu : f u ∈ Y := hu.2
    have h3 : (f u) ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := Y) (x := (⟨f u, hfu⟩ : Y))
      rw [hY] at h
      exact congrArg Subtype.val h
    have h2 : (f u) ^ 2 ^ n = 1 := by rw [← map_pow, hn', map_one]
    have hord : orderOf (f u) ∣ Nat.gcd (2 ^ n) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left n (by norm_num))] at hord
    exact (QuotientGroup.eq_one_iff u).mp (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord))
  have hcardP : Nat.card (N ⊔ U : Subgroup Γ) = 3 * Nat.card U := by
    have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hUN
    rw [inf_comm, hUNS, hNcard] at h
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := S))
    rw [h]
    ring
  have hrelP : U.relIndex (N ⊔ U) = 3 := by
    have h := Subgroup.relIndex_mul_card U (N ⊔ U)
    rw [inf_eq_left.mpr le_sup_right, hcardP] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := U)) (by rw [h, mul_comm])
  have hWU : ¬ W ≤ U := by
    intro h
    obtain ⟨m, hm⟩ := (hU.to_le h).exists_card_eq
    rw [hWcard] at hm
    have h3 : 3 ∣ 2 ^ m := by rw [← hm]
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hle : U ⊔ W ≤ N ⊔ U := sup_le le_sup_right (hWN.trans le_sup_left)
  have hmul := Subgroup.relIndex_mul_relIndex U (U ⊔ W) (N ⊔ U) le_sup_left hle
  rw [hrelP] at hmul
  have hrelUW : U.relIndex (U ⊔ W) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro _ hmul) with h1 | h1
    · exfalso
      exact hWU (le_sup_right.trans (Subgroup.relIndex_eq_one.mp h1))
    · exact h1
  refine ⟨W, hWcard, hWY, hrelUW, fun hnorm => ?_⟩
  obtain ⟨u, hu, y, hy, hne⟩ := hact
  obtain ⟨w, hw, rfl⟩ : ∃ w ∈ W, f w = y := by
    rw [← hWY] at hy
    exact hy
  have hwP : w ∈ U ⊔ W := Subgroup.mem_sup_right hw
  have huP : u ∈ U ⊔ W := Subgroup.mem_sup_left hu
  have h1 := hnorm.conj_mem ⟨u, huP⟩ (Subgroup.mem_subgroupOf.mpr hu) ⟨w, hwP⟩
  have h2 : w * u * w⁻¹ ∈ U := h1
  have hc1 : w * u * w⁻¹ * u⁻¹ ∈ U := U.mul_mem h2 (U.inv_mem hu)
  have hc2 : w * u * w⁻¹ * u⁻¹ ∈ N := by
    have h3 : u * w⁻¹ * u⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hUN hu) w⁻¹).mp (N.inv_mem (hWN hw))
    simpa [mul_assoc] using N.mul_mem (hWN hw) h3
  have hcS : w * u * w⁻¹ * u⁻¹ ∈ S := by
    rw [← hUNS]
    exact ⟨hc1, hc2⟩
  have h3 : f (w * u * w⁻¹ * u⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hcS
  simp only [map_mul, map_inv] at h3
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  apply hne
  rw [← h3, mul_inv_cancel_right]

end Lift

end CFSG.AGLEmbeddingD2
