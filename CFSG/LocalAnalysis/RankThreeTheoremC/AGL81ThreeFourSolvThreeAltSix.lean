module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeTargets
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNormalizesNoSU
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel
import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionDatum
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltSix

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

theorem perm_three_eq_or_eq_sq : ∀ a b : Equiv.Perm (Fin 3), a ^ 3 = 1 → b ^ 3 = 1 → a ≠ 1 →
    b ≠ 1 → b = a ∨ b = a ^ 2 := by decide

theorem perm_three_exists_inv : ∀ a : Equiv.Perm (Fin 3), a ^ 3 = 1 →
    ∃ τ : Equiv.Perm (Fin 3), τ * a * τ⁻¹ = a⁻¹ := by decide

section Generic

variable {Y : Type} [Group Y] [Finite Y]

theorem commute_of_pow_three_of_pRank_le_one {C Q : Subgroup Y} (hQC : Q ≤ C)
    (hrk : CFSG.Open.pRank 3 C ≤ 1) (hQ3 : ∀ x ∈ Q, x ^ 3 = 1) :
    ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hQ : Q = ⊥
  · intro x hx y hy
    rw [hQ, Subgroup.mem_bot] at hx hy
    rw [hx, hy]
  have hQp : IsPGroup 3 Q := fun x => ⟨1, Subtype.ext (by simpa using hQ3 x x.2)⟩
  haveI : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ
  haveI := hQp.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center Q)
  set z' : Y := ((z : Q) : Y) with hz'
  have hz'Q : z' ∈ Q := (z : Q).2
  have hz'1 : z' ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  have hz'3 : z' ^ 3 = 1 := hQ3 z' hz'Q
  have hz'c : ∀ w ∈ Q, w * z' = z' * w := fun w hw =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨w, hw⟩)
  have hall : ∀ w ∈ Q, w ∈ zpowers z' := by
    intro w hw
    by_contra hwz
    have hcomm : ∀ a ∈ zpowers z', ∀ b ∈ zpowers w, a * b = b * a := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow (show Commute z' w from (hz'c w hw).symm) i j).eq
    have hel := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.sup
      (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers hz'3)
      (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers (hQ3 w hw)) hcomm
    obtain ⟨k, hk⟩ := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card Nat.prime_three hel
    have hlt : zpowers z' < zpowers z' ⊔ zpowers w := by
      refine lt_of_le_of_ne le_sup_left fun h => hwz ?_
      rw [h]
      exact mem_sup_right (mem_zpowers w)
    have hcard := CFSG.GH74.Uniqueness.SU.SU1.card_lt_of_lt hlt
    rw [Nat.card_zpowers, orderOf_eq_prime hz'3 hz'1, hk] at hcard
    have hk2 : 2 ≤ k := by
      have h1 : 3 ^ 1 < 3 ^ k := by simpa using hcard
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp h1
      omega
    have hle : k ≤ CFSG.Open.pRank 3 C :=
      CFSG.GH74.Uniqueness.SU.SU1.le_pRank (by norm_num)
        (sup_le (zpowers_le.mpr (hQC hz'Q)) (zpowers_le.mpr (hQC hw))) hel hk
    omega
  intro x hx y hy
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (hall x hx)
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp (hall y hy)
  exact (Commute.zpow_zpow_self z' i j).eq

theorem commute_of_le_of_not_dvd {K Q : Subgroup Y} (hQK : Q ≤ K) (hK : ¬ 27 ∣ Nat.card K)
    (hQ3 : ∀ x ∈ Q, x ^ 3 = 1) : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQp : IsPGroup 3 Q := fun x => ⟨1, Subtype.ext (by simpa using hQ3 x x.2)⟩
  obtain ⟨n, hn⟩ := hQp.exists_card_eq
  have hdvd : 3 ^ n ∣ Nat.card K := hn ▸ Subgroup.card_dvd_of_le hQK
  have hn2 : n ≤ 2 := by
    by_contra h
    exact hK ((pow_dvd_pow 3 (by omega : 3 ≤ n)).trans hdvd)
  intro x hx y hy
  interval_cases n
  · have hbot : Q = ⊥ := Subgroup.eq_bot_of_card_eq Q (by simpa using hn)
    rw [hbot, Subgroup.mem_bot] at hx hy
    rw [hx, hy]
  · haveI : IsCyclic Q := isCyclic_of_prime_card (p := 3) (by simpa using hn)
    exact congrArg Subtype.val
      ((IsCyclic.isMulCommutative (α := Q)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  · exact congrArg Subtype.val (IsPGroup.commutative_of_card_eq_prime_sq hn ⟨x, hx⟩ ⟨y, hy⟩)

theorem commute_of_le_sup_centralizer {K P : Subgroup Y} [K.Normal]
    (hKC : K ⊓ centralizer (K : Set Y) = ⊥)
    (hK : ∀ Q : Subgroup Y, Q ≤ K → Q ≤ P ⊔ centralizer (K : Set Y) → (∀ x ∈ Q, x ^ 3 = 1) →
      ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hrkC : CFSG.Open.pRank 3 (centralizer (K : Set Y)) ≤ 1)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1) (hPKC : P ≤ K ⊔ centralizer (K : Set Y)) :
    ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  set C := centralizer (K : Set Y) with hCdef
  haveI : C.Normal := by rw [hCdef]; infer_instance
  have hcube : ∀ k ∈ K, ∀ c ∈ C, (k * c) ^ 3 = 1 → k ^ 3 = 1 ∧ c ^ 3 = 1 := by
    intro k hk c hc h
    have hkc : k * c = c * k := Subgroup.mem_centralizer_iff.mp hc k hk
    have h1 : k ^ 3 * c ^ 3 = 1 := by rw [← Commute.mul_pow hkc 3]; exact h
    have h2 : c ^ 3 ∈ K ⊓ C := by
      refine ⟨?_, Subgroup.pow_mem _ hc 3⟩
      rw [eq_inv_of_mul_eq_one_right h1]
      exact K.inv_mem (K.pow_mem hk 3)
    rw [hKC, Subgroup.mem_bot] at h2
    exact ⟨by rw [h2, mul_one] at h1; exact h1, h2⟩
  set PK : Subgroup Y := (P ⊔ C) ⊓ K with hPK
  set PC : Subgroup Y := (P ⊔ K) ⊓ C with hPC
  have hPK3 : ∀ z ∈ PK, z ^ 3 = 1 := by
    intro z hz
    obtain ⟨hzPC, hzK⟩ := Subgroup.mem_inf.mp hz
    rw [← SetLike.mem_coe, Subgroup.mul_normal P C] at hzPC
    obtain ⟨p, hp, c, hc, rfl⟩ := Set.mem_mul.mp hzPC
    have hpK : p = (p * c) * c⁻¹ := by group
    have hp3 := hP3 p hp
    rw [hpK] at hp3
    exact (hcube _ hzK _ (C.inv_mem hc) hp3).1
  have hPC3 : ∀ w ∈ PC, w ^ 3 = 1 := by
    intro w hw
    obtain ⟨hwPK, hwC⟩ := Subgroup.mem_inf.mp hw
    rw [sup_comm, ← SetLike.mem_coe, Subgroup.normal_mul K P] at hwPK
    obtain ⟨k, hk, p, hp, rfl⟩ := Set.mem_mul.mp hwPK
    have hpe : p = k⁻¹ * (k * p) := by group
    have hp3 := hP3 p hp
    rw [hpe] at hp3
    exact (hcube _ (K.inv_mem hk) _ hwC hp3).2
  have hPKc := hK PK inf_le_right inf_le_left hPK3
  have hPCc := commute_of_pow_three_of_pRank_le_one inf_le_right hrkC hPC3
  have hdec : ∀ x ∈ P, ∃ k ∈ PK, ∃ c ∈ PC, x = k * c ∧ ∀ k' ∈ K, c * k' = k' * c := by
    intro x hx
    have hx' := hPKC hx
    rw [← SetLike.mem_coe, Subgroup.normal_mul K C] at hx'
    obtain ⟨k, hk, c, hc, rfl⟩ := Set.mem_mul.mp hx'
    refine ⟨k, ⟨?_, hk⟩, c, ⟨?_, hc⟩, rfl, fun k' hk' =>
      (Subgroup.mem_centralizer_iff.mp hc k' hk').symm⟩
    · have : k = (k * c) * c⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (mem_sup_left hx) (mem_sup_right (C.inv_mem hc))
    · have : c = k⁻¹ * (k * c) := by group
      rw [this]
      exact Subgroup.mul_mem _ (mem_sup_right (K.inv_mem hk)) (mem_sup_left hx)
  intro x hx y hy
  obtain ⟨k₁, hk₁, c₁, hc₁, rfl, hc₁K⟩ := hdec x hx
  obtain ⟨k₂, hk₂, c₂, hc₂, rfl, hc₂K⟩ := hdec y hy
  have e1 := hPKc k₁ hk₁ k₂ hk₂
  have e2 := hPCc c₁ hc₁ c₂ hc₂
  have e3 := hc₁K k₂ hk₂.2
  have e4 := hc₂K k₁ hk₁.2
  calc k₁ * c₁ * (k₂ * c₂) = k₁ * (c₁ * k₂) * c₂ := by group
    _ = k₁ * (k₂ * c₁) * c₂ := by rw [e3]
    _ = (k₁ * k₂) * (c₁ * c₂) := by group
    _ = (k₂ * k₁) * (c₂ * c₁) := by rw [e1, e2]
    _ = k₂ * (k₁ * c₂) * c₁ := by group
    _ = k₂ * (c₂ * k₁) * c₁ := by rw [e4]
    _ = k₂ * c₂ * (k₁ * c₁) := by group

end Generic

section Solvable

variable {Y I₀ : Type} [Group Y] [Finite Y] [Group I₀] [Finite I₀]

theorem exists_oUpperTwo_of_odd (σ : I₀ →* Y) {y : Y} (hy : y ∈ σ.range)
    (hodd : Odd (orderOf y)) :
    ∃ g ∈ CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀), σ g = y := by
  have hyJ : y ∈ CFSG.ComponentClassification.AS76b.oUpperTwo σ.range :=
    Subgroup.subset_closure ⟨hy, hodd⟩
  rw [MonoidHom.range_eq_map, ← SUPair.map_oUpperTwo] at hyJ
  obtain ⟨g, hg, rfl⟩ := hyJ
  exact ⟨g, hg, rfl⟩

theorem eq_one_of_mem_map_pCore_of_odd (σ : I₀ →* Y) {y : Y}
    (hy : y ∈ (CFSG.pCore 2 I₀).map σ) (hodd : Odd (orderOf y)) : y = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 ((CFSG.pCore 2 I₀).map σ) := CFSG.pCore_isPGroup.map σ
  obtain ⟨n, hn⟩ := h2 ⟨y, hy⟩
  have hn' : y ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hcop : Nat.Coprime (orderOf y) (2 ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hodd)
  have hdvd : orderOf y ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one hcop]
    exact Nat.dvd_gcd dvd_rfl (orderOf_dvd_of_pow_eq_one hn')
  rwa [Nat.dvd_one, orderOf_eq_one_iff] at hdvd

theorem mem_of_odd_of_symThree (σ : I₀ →* Y) (f : I₀ ⧸ CFSG.pCore 2 I₀ ≃* Equiv.Perm (Fin 3))
    {C : Subgroup Y} (hσC : (CFSG.pCore 2 I₀).map σ ≤ C) {y₀ : Y} (hy₀ : y₀ ∈ σ.range)
    (hy₀o : Odd (orderOf y₀)) (hy₀C : y₀ ∈ C) (hy₀1 : y₀ ≠ 1) {y : Y} (hy : y ∈ σ.range)
    (hyo : Odd (orderOf y)) : y ∈ C := by
  have hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀) := Or.inl ⟨f⟩
  obtain ⟨g₀, hg₀, rfl⟩ := exists_oUpperTwo_of_odd σ hy₀ hy₀o
  obtain ⟨g, hg, rfl⟩ := exists_oUpperTwo_of_odd σ hy hyo
  have hcube : ∀ x ∈ CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀),
      f (x : I₀ ⧸ CFSG.pCore 2 I₀) ^ 3 = 1 := by
    intro x hx
    rw [← map_pow, ← QuotientGroup.mk_pow,
      (QuotientGroup.eq_one_iff _).mpr (cube_mem_pCore_two hb x hx), map_one]
  have hn0 : f (g₀ : I₀ ⧸ CFSG.pCore 2 I₀) ≠ 1 := by
    intro h
    have h1 : (g₀ : I₀ ⧸ CFSG.pCore 2 I₀) = 1 := f.injective (by rw [h, map_one])
    exact hy₀1 (eq_one_of_mem_map_pCore_of_odd σ
      (Subgroup.mem_map_of_mem σ ((QuotientGroup.eq_one_iff _).mp h1)) hy₀o)
  by_cases hn : f (g : I₀ ⧸ CFSG.pCore 2 I₀) = 1
  · have h1 : (g : I₀ ⧸ CFSG.pCore 2 I₀) = 1 := f.injective (by rw [hn, map_one])
    exact hσC (Subgroup.mem_map_of_mem σ ((QuotientGroup.eq_one_iff _).mp h1))
  rcases perm_three_eq_or_eq_sq _ _ (hcube g₀ hg₀) (hcube g hg) hn0 hn with h | h
  · have h' : (g₀ : I₀ ⧸ CFSG.pCore 2 I₀) = g := (f.injective h).symm
    have hm : g₀⁻¹ * g ∈ CFSG.pCore 2 I₀ := QuotientGroup.eq.mp h'
    have he : σ g = σ g₀ * σ (g₀⁻¹ * g) := by rw [← map_mul, mul_inv_cancel_left]
    rw [he]
    exact C.mul_mem hy₀C (hσC (Subgroup.mem_map_of_mem σ hm))
  · have h' : ((g₀ ^ 2 : I₀) : I₀ ⧸ CFSG.pCore 2 I₀) = g := by
      apply f.injective
      rw [h, QuotientGroup.mk_pow, map_pow]
    have hm : (g₀ ^ 2)⁻¹ * g ∈ CFSG.pCore 2 I₀ := QuotientGroup.eq.mp h'
    have he : σ g = σ g₀ ^ 2 * σ ((g₀ ^ 2)⁻¹ * g) := by
      rw [← map_pow, ← map_mul, mul_inv_cancel_left]
    rw [he]
    exact C.mul_mem (C.pow_mem hy₀C 2) (hσC (Subgroup.mem_map_of_mem σ hm))

end Solvable

theorem threeFourSolvThreeLeAt_altSix (h : 5 ≤ 6) :
    ThreeFourSolvThreeLeAt (TauCeti.CFSGIndex.alternating 6 h).Group := by
  intro Y _ _ K Y₀ E R I₀ _ _ σ hK hKX hZ hrk hrkC hC _ _ _ _ _ hO2 hker hσY hσs hb _ _ hJ
  haveI := hK
  obtain ⟨e⟩ := hKX
  set C := centralizer (K : Set Y) with hCdef
  haveI : C.Normal := by rw [hCdef]; infer_instance
  have hKC := CFSG.QuasithinUnique.RankOneRecog.inf_centralizer_eq_bot_of_center_eq_bot hZ
  have hinner := exists_conj_of_pow_three_of_mulEquiv e
    (fun _ hα => CFSG.RankThree.PartTwo.Sec4.Item434Alt.mem_range_conj_of_pow_three hα)
  have hσC : (CFSG.pCore 2 I₀).map σ ≤ C := (map_pCore_two_le_pCoreOf σ hσs).trans hO2
  have hrkC' : CFSG.Open.pRank 3 C ≤ 1 := by
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at hrkC
  have hdec : ∀ y ∈ σ.range, Odd (orderOf y) →
      ∃ k ∈ K, ∃ c ∈ C, y = k * c ∧ k ^ 3 = 1 ∧ c ^ 3 = 1 := by
    intro y hy hodd
    have hy3 := pow_three_eq_one_of_mem_range_of_odd σ hb hy hodd
    obtain ⟨k, hk, c, hc, rfl⟩ := exists_mul_of_pow_three hinner hy3
    have hkc : k * c = c * k := Subgroup.mem_centralizer_iff.mp hc k hk
    have h1 : k ^ 3 * c ^ 3 = 1 := by rw [← Commute.mul_pow hkc 3]; exact hy3
    have hc3 : c ^ 3 = 1 := by
      have h2 : c ^ 3 ∈ K ⊓ C := by
        refine ⟨?_, Subgroup.pow_mem _ hc 3⟩
        rw [eq_inv_of_mul_eq_one_right h1]
        exact K.inv_mem (K.pow_mem hk 3)
      rwa [hKC, Subgroup.mem_bot] at h2
    refine ⟨k, hk, c, hc, rfl, ?_, hc3⟩
    rw [hc3, mul_one] at h1
    exact h1
  have hodd_of : ∀ u : I₀, (∃ m : ℕ, u ^ 3 ^ m = 1) → Odd (orderOf (σ u)) := by
    rintro u ⟨m, hm⟩
    have : (σ u) ^ 3 ^ m = 1 := by rw [← map_pow, hm, map_one]
    exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one this)
  by_cases hs3 : Nonempty (I₀ ⧸ CFSG.pCore 2 I₀ ≃* Equiv.Perm (Fin 3))
  · obtain ⟨f⟩ := hs3
    have hnoC : ∀ y₀ ∈ σ.range, Odd (orderOf y₀) → y₀ ∈ C → y₀ = 1 := by
      intro y₀ hy₀ hy₀o hy₀C
      by_contra hy₀1
      exact hJ (oUpperTwo_map_le_of_odd σ fun y' hy' hy'o =>
        mem_of_odd_of_symThree σ f hσC hy₀ hy₀o hy₀C hy₀1 hy' hy'o)
    refine oUpperTwo_map_le_of_odd σ fun y hy hodd => ?_
    obtain ⟨k, hk, c, hc, rfl, hk3, hc3⟩ := hdec y hy hodd
    obtain ⟨g, hg, hgy⟩ := exists_oUpperTwo_of_odd σ hy hodd
    have ha3 : f (g : I₀ ⧸ CFSG.pCore 2 I₀) ^ 3 = 1 := by
      rw [← map_pow, ← QuotientGroup.mk_pow,
        (QuotientGroup.eq_one_iff _).mpr (cube_mem_pCore_two (Or.inl ⟨f⟩) g hg), map_one]
    obtain ⟨τ, hτ⟩ := perm_three_exists_inv _ ha3
    obtain ⟨q, hq⟩ := f.surjective τ
    obtain ⟨t₀, rfl⟩ := QuotientGroup.mk_surjective q
    have hw : t₀ * g * t₀⁻¹ * g ∈ CFSG.pCore 2 I₀ := by
      rw [← QuotientGroup.eq_one_iff]
      apply f.injective
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        map_mul, map_mul, map_mul, map_inv, hq, hτ, map_one, inv_mul_cancel]
    set t : Y := σ t₀ with ht
    have htS : t ∈ σ.range := ⟨t₀, rfl⟩
    have htw : t * (k * c) * t⁻¹ * (k * c) ∈ C := by
      have h1 := hσC (Subgroup.mem_map_of_mem σ hw)
      rwa [map_mul, map_mul, map_mul, map_inv, hgy] at h1
    have htk : t * k * t⁻¹ = k⁻¹ := by
      have hcC : t * c * t⁻¹ ∈ C := (inferInstance : C.Normal).conj_mem c hc t
      have hkK : t * k * t⁻¹ * k ∈ K := K.mul_mem (hK.conj_mem k hk t) hk
      have hcomm : (t * c * t⁻¹) * k = k * (t * c * t⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hcC k hk).symm
      have hprod : t * (k * c) * t⁻¹ * (k * c) =
          (t * k * t⁻¹ * k) * (t * c * t⁻¹ * c) := by
        calc t * (k * c) * t⁻¹ * (k * c) = (t * k * t⁻¹) * ((t * c * t⁻¹) * k) * c := by group
          _ = (t * k * t⁻¹) * (k * (t * c * t⁻¹)) * c := by rw [hcomm]
          _ = (t * k * t⁻¹ * k) * (t * c * t⁻¹ * c) := by group
      have hkC : t * k * t⁻¹ * k ∈ C := by
        have h1 := C.mul_mem htw (C.inv_mem (C.mul_mem hcC hc))
        rwa [hprod, mul_inv_cancel_right] at h1
      have h1 : t * k * t⁻¹ * k ∈ K ⊓ C := ⟨hkK, hkC⟩
      rw [hKC, Subgroup.mem_bot] at h1
      exact eq_inv_of_mul_eq_one_left h1
    have hkY : k ∈ Y₀ := by
      have hke : k = (k * c) * c⁻¹ := by group
      rw [hke]
      exact Y₀.mul_mem (hσY hy) (Y₀.inv_mem (hC hc))
    obtain ⟨d, hd⟩ := exists_iterate_commutator_le_of_isSubnormal hσs (zpowers_le.mpr hkY)
    have hck : ⁅k, t⁆ = k⁻¹ := by
      rw [commutatorElement_def]
      calc k * t * k⁻¹ * t⁻¹ = k * (t * k * t⁻¹)⁻¹ := by group
        _ = k * k := by rw [htk, inv_inv]
        _ = k ^ 3 * k⁻¹ := by rw [pow_succ, pow_two, mul_inv_cancel_right]
        _ = k⁻¹ := by rw [hk3, one_mul]
    have hiter : ∀ n : ℕ, zpowers k ≤ (fun X : Subgroup Y => ⁅X, σ.range⁆)^[n] (zpowers k) := by
      intro n
      induction n with
      | zero => exact le_rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        refine zpowers_le.mpr ?_
        have hm : ⁅k, t⁆ ∈ ⁅(fun X : Subgroup Y => ⁅X, σ.range⁆)^[n] (zpowers k), σ.range⁆ :=
          Subgroup.commutator_mem_commutator (ih (mem_zpowers k)) htS
        rw [hck] at hm
        simpa using Subgroup.inv_mem _ hm
    have hkS : k ∈ σ.range := hd (hiter d (mem_zpowers k))
    have hcS : c ∈ σ.range := by
      have hce : c = k⁻¹ * (k * c) := by group
      rw [hce]
      exact σ.range.mul_mem (σ.range.inv_mem hkS) hy
    have hco : Odd (orderOf c) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hc3)
    rw [hnoC c hcS hco hc, mul_one]
    exact hk
  ·
    exfalso
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨a, b, ha, hb3, hab⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNoSU.exists_cube_not_comm hb
        (not_nonempty_iff.mp hs3)
    have hH : IsPGroup 3
        (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup (I₀ ⧸ CFSG.pCore 2 I₀))) := by
      intro x
      exact ⟨1, Subtype.ext (by
        simpa using IsSymThreeOrSUThreeTwo.cube kFactSUThreeTwoShape_holds hb x x.2)⟩
    have hmemH : ∀ z : I₀ ⧸ CFSG.pCore 2 I₀, z ^ 3 = 1 →
        z ∈ CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup (I₀ ⧸ CFSG.pCore 2 I₀)) :=
      fun z hz => Subgroup.subset_closure
        ⟨Subgroup.mem_top z, Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hz)⟩
    obtain ⟨P₀⟩ : Nonempty (Sylow 3 I₀) := inferInstance
    set Pbar := P₀.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 I₀)) with hPbar
    have hHP : CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup (I₀ ⧸ CFSG.pCore 2 I₀)) ≤
        (Pbar : Subgroup (I₀ ⧸ CFSG.pCore 2 I₀)) := by
      haveI := (normal_oUpperTwo_top :
        (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup (I₀ ⧸ CFSG.pCore 2 I₀))).Normal)
      have hsup := hH.to_sup_of_normal_left Pbar.isPGroup'
      have := Pbar.is_maximal' hsup le_sup_right
      rw [← this]
      exact le_sup_left
    have hlift : ∀ z : I₀ ⧸ CFSG.pCore 2 I₀, z ^ 3 = 1 →
        ∃ x ∈ (P₀ : Subgroup I₀), QuotientGroup.mk' (CFSG.pCore 2 I₀) x = z := by
      intro z hz
      have h1 := hHP (hmemH z hz)
      rw [hPbar, Sylow.coe_mapSurjective] at h1
      obtain ⟨x, hx, hxz⟩ := h1
      exact ⟨x, hx, hxz⟩
    obtain ⟨x, hx, hxa⟩ := hlift a ha
    obtain ⟨y, hy, hyb⟩ := hlift b hb3
    have hP3 : ∀ u ∈ (P₀ : Subgroup I₀).map σ, u ^ 3 = 1 := by
      rintro _ ⟨u, hu, rfl⟩
      exact pow_three_eq_one_of_mem_range_of_odd σ hb ⟨u, rfl⟩
        (hodd_of u (by
          obtain ⟨m, hm⟩ := P₀.isPGroup' ⟨u, hu⟩
          exact ⟨m, by simpa using congrArg Subtype.val hm⟩))
    have hPKC : (P₀ : Subgroup I₀).map σ ≤ K ⊔ C := by
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨m, hm⟩ := P₀.isPGroup' ⟨u, hu⟩
      obtain ⟨k, hk, c, hc, he, -, -⟩ :=
        hdec (σ u) ⟨u, rfl⟩ (hodd_of u ⟨m, by simpa using congrArg Subtype.val hm⟩)
      rw [he]
      exact mul_mem_sup hk hc
    have hK27 : ¬ 27 ∣ Nat.card K := by
      rw [Nat.card_congr e.toEquiv]
      change ¬ 27 ∣ Nat.card (alternatingGroup (Fin 6))
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    have hcomm := commute_of_le_sup_centralizer hKC
      (fun Q hQ _ h3 => commute_of_le_of_not_dvd hQ hK27 h3) hrkC' hP3 hPKC
      (σ x) (Subgroup.mem_map_of_mem σ hx) (σ y) (Subgroup.mem_map_of_mem σ hy)
    set z := x * y * x⁻¹ * y⁻¹ with hz
    have hzP : z ∈ (P₀ : Subgroup I₀) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) (Subgroup.inv_mem _ hx))
        (Subgroup.inv_mem _ hy)
    have hzk : z ∈ σ.ker := by
      rw [MonoidHom.mem_ker, hz, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have hz1 : z = 1 := by
      obtain ⟨m, hm⟩ := P₀.isPGroup' ⟨z, hzP⟩
      have hm' : z ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
      have h1 : orderOf z ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hm'
      have h2 : orderOf z ∣ Nat.card σ.ker := by
        have := orderOf_dvd_natCard (⟨z, hzk⟩ : σ.ker)
        rwa [Subgroup.orderOf_mk] at this
      have hcop : Nat.Coprime (3 ^ m) (Nat.card σ.ker) := Nat.Coprime.pow_left m hker
      have h3 : orderOf z ∣ 1 := by
        rw [← Nat.Coprime.gcd_eq_one hcop]
        exact Nat.dvd_gcd h1 h2
      rwa [Nat.dvd_one, orderOf_eq_one_iff] at h3
    apply hab
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    congr 1
    calc x * y = z * (y * x) := by rw [hz]; group
      _ = y * x := by rw [hz1, one_mul]

theorem threeFourSolvThreeTargets_holds : ThreeFourSolvThreeTargets :=
  threeFourSolvThreeTargets_of_altSix threeFourSolvThreeLeAt_altSix

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
