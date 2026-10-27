module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PI
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517Defs
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520B0
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512B
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PG
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PM
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PK
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open KFactsSmall

theorem mem_uniqueSet_of_order_three_aux_outTwo (hKOut : KOut) {S : Type} [Group S] [Finite S]
    (hq : CFSG.Open.IsQuasisimple S) (hlist : IsOutTwoGroupList (S ⧸ Subgroup.center S)) :
    OutTwoGroup S := by
  haveI : Group.IsPerfect S := ⟨hq.1⟩
  intro φ
  set π := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom S with hπ
  obtain ⟨k, y, hy⟩ := hKOut (S ⧸ Subgroup.center S) hlist (π φ)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have hconj : π (MulAut.conj g) = MulAut.conj (QuotientGroup.mk g : S ⧸ Subgroup.center S) := by
    ext z
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
    have h1 := CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk
      (MulAut.conj g) z
    simp only [QuotientGroup.mk'_apply] at h1
    simp [hπ, CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom, h1,
      MulAut.conj_apply]
  refine ⟨k, g, ?_⟩
  apply CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective S
  rw [← hπ, hconj, map_pow]
  exact hy

theorem mem_uniqueSet_of_order_three_aux_big {S : Type} [Group S] (h : Big1525 S) :
    IsOutTwoGroupList S := by
  rcases h with h | h | ⟨Q, hp, hc, d, hd, e⟩ | ⟨d, ⟨q, hq, hd⟩, e⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨d, Or.inl ⟨Q, hc, hd⟩, e⟩)
  · exact Or.inr (Or.inr ⟨d, Or.inr (Or.inl ⟨q, hq, hd⟩), e⟩)

theorem mem_uniqueSet_of_order_three_aux_bigEquiv {S S' : Type} [Group S] [Group S']
    (e : S ≃* S') (h : Big1525 S) : Big1525 S' := by
  rcases h with ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩ | ⟨Q, hp, hc, d, hd, ⟨e'⟩⟩ | ⟨d, hd, ⟨e'⟩⟩
  · exact Or.inl ⟨e.symm.trans e'⟩
  · exact Or.inr (Or.inl ⟨e.symm.trans e'⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨Q, hp, hc, d, hd, ⟨e.symm.trans e'⟩⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨d, hd, ⟨e.symm.trans e'⟩⟩))

theorem mem_uniqueSet_of_order_three_aux_barO2_gen {X : Type} [Group X] [Finite X]
    {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X}
    (hl : LiftCtxGen X T T₁ T₂ Ls L) (hbig : Big1525 ↥Ls) :
    Big1525 (↥(barO2 L) ⧸ Subgroup.center ↥(barO2 L)) := by
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift hl.gn hl.comp.1 hl.lift
  have hSmall : Small1522 ↥Ls := by
    rcases hbig with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have hZ : Subgroup.center ↥Ls = ⊥ := (small1522_simple_center hSmall).2
  have e1 : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* ↥Ls :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact mem_uniqueSet_of_order_three_aux_bigEquiv (eQ.trans e1).symm hbig

theorem mem_uniqueSet_of_order_three_aux_lift3 {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hLn : L.Normal) (hOut : OutTwoGroup ↥(barO2 L)) {b : X} (hb : b ^ 3 = 1) :
    ∃ l ∈ L, (∃ j : ℕ, orderOf l = 3 ^ j) ∧ l⁻¹ * b ∈ cMHat L := by
  set π : X →* X ⧸ CFSG.pCore 2 X := QuotientGroup.mk' (CFSG.pCore 2 X) with hπ
  haveI hbn : (barO2 L).Normal := Subgroup.Normal.map hLn _ (QuotientGroup.mk'_surjective _)
  have hbN : π b ∈ Subgroup.normalizer (barO2 L : Set (X ⧸ CFSG.pCore 2 X)) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  have hb3 : (π b) ^ 3 = 1 := by rw [← map_pow, hb, map_one]
  have hodd : Odd (orderOf (π b)) :=
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hb3)
  have hmem := mem_sup_centralizer_of_outTwo hOut hbN hodd
  have hle : Subgroup.centralizer (barO2 L : Set (X ⧸ CFSG.pCore 2 X)) ≤
      Subgroup.normalizer (barO2 L : Set (X ⧸ CFSG.pCore 2 X)) :=
    Subgroup.centralizer_le_normalizer _
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle] at hmem
  obtain ⟨x, hx, y, hy, hxy⟩ := hmem
  obtain ⟨l₀, hl₀, hl₀x⟩ := hx
  have hcomm : x * y = y * x := (Subgroup.mem_centralizer_iff.1 hy) x ⟨l₀, hl₀, hl₀x⟩
  have hn : orderOf l₀ ≠ 0 := (orderOf_pos l₀).ne'
  obtain ⟨a, m, hm3, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 3 (by norm_num)
  have hk1 : (m * m) % 3 = 1 := by
    have : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  have hpow3 : ∀ z : X ⧸ CFSG.pCore 2 X, z ^ 3 = 1 → z ^ (m * m) = z := by
    intro z hz
    obtain ⟨q, hq⟩ : ∃ q, m * m = 3 * q + 1 := ⟨(m * m) / 3, by omega⟩
    rw [hq, pow_succ, pow_mul, hz, one_pow, one_mul]
  refine ⟨l₀ ^ (m * m), L.pow_mem hl₀ _, ?_, ?_⟩
  · have h1 : (l₀ ^ (m * m)) ^ (3 ^ a) = 1 := by
      have : m * m * 3 ^ a = orderOf l₀ * m := by rw [hnm]; ring
      rw [← pow_mul, this, pow_mul, pow_orderOf_eq_one, one_pow]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨j, hj⟩
  · have key : π ((l₀ ^ (m * m))⁻¹ * b) = y ^ (m * m) := by
      have h1 : π b = x * y := hxy.symm
      have h2 : (x * y) ^ (m * m) = x * y := hpow3 _ (by rw [← h1]; exact hb3)
      have h3 : (x * y) ^ (m * m) = x ^ (m * m) * y ^ (m * m) := (Commute.mul_pow hcomm (m * m))
      rw [map_mul, map_inv, map_pow, hl₀x, h1, ← h2, h3, inv_mul_cancel_left]
    show π ((l₀ ^ (m * m))⁻¹ * b) ∈ cMBar L
    rw [key]
    exact pow_mem hy _

theorem mem_uniqueSet_of_order_three_aux_cl {X : Type} [Group X] [Finite X] {N E : Subgroup X}
    [hNn : N.Normal] (hN2 : IsPGroup 2 N) (hE : IsPGroup 3 E) {b : X}
    (hB : IsPGroup 3 (Subgroup.zpowers b)) (hc : ∀ e ∈ E, b * e * b⁻¹ * e⁻¹ ∈ N) :
    ∃ x ∈ N, ∀ e ∈ E, b * (x * e * x⁻¹) = (x * e * x⁻¹) * b := by
  have hNF : N ≤ N ⊔ E := le_sup_left
  have hEF : E ≤ N ⊔ E := le_sup_right
  have hFN : N ⊔ E ≤ Subgroup.normalizer (N : Set X) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  set π : X →* X ⧸ N := QuotientGroup.mk' N with hπ
  have hcE : ∀ e ∈ E, π b * π e = π e * π b := by
    intro e he
    have h1 : π (b * e * b⁻¹ * e⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 (hc e he)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
  have hF' : ∀ f ∈ N ⊔ E, π b * π f = π f * π b := by
    have hle : N ⊔ E ≤ (Subgroup.centralizer ({π b} : Set (X ⧸ N))).comap π := by
      refine sup_le (fun n hn => ?_) (fun e he => ?_)
      · show π n ∈ Subgroup.centralizer ({π b} : Set (X ⧸ N))
        have : π n = 1 := (QuotientGroup.eq_one_iff n).2 hn
        rw [this]
        exact Subgroup.one_mem _
      · show π e ∈ Subgroup.centralizer ({π b} : Set (X ⧸ N))
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact hcE e he
    intro f hf
    have := Subgroup.mem_centralizer_iff.1 (hle hf) (π b) rfl
    exact this
  have hy : ∀ y ∈ Subgroup.zpowers b, ∀ f ∈ N ⊔ E, y * f * y⁻¹ * f⁻¹ ∈ N := by
    intro y hy f hf
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hcomm : Commute (π b ^ j) (π f) := Commute.zpow_left (hF' f hf) j
    have h2 : π (b ^ j * f * (b ^ j)⁻¹ * f⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_zpow]
      rw [hcomm.eq]
      group
    exact (QuotientGroup.eq_one_iff _).1 h2
  obtain ⟨x, hxN, hx⟩ := exists_conj_centralized_aux_main Nat.prime_three (by norm_num)
    Nat.prime_three (by norm_num) hN2 hNF hFN hE hEF hB hy
  exact ⟨x, hxN, fun e he => hx e he b (Subgroup.mem_zpowers b)⟩

theorem mem_uniqueSet_of_order_three_aux_cube {X : Type} [Group X] [Finite X] {l : X} {j : ℕ}
    (hj : orderOf l = 3 ^ j) (h : (QuotientGroup.mk' (CFSG.pCore 2 X) l) ^ 3 = 1) : l ^ 3 = 1 := by
  have h3 : QuotientGroup.mk' (CFSG.pCore 2 X) (l ^ 3) = 1 := by rw [map_pow]; exact h
  have hmemN : l ^ 3 ∈ CFSG.pCore 2 X := (QuotientGroup.eq_one_iff _).1 h3
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (CFSG.pCore_isPGroup (p := 2) (G := X))) ⟨l ^ 3, hmemN⟩
  have hk' : orderOf (l ^ 3) = 2 ^ k := by
    rw [← Subgroup.orderOf_mk (l ^ 3) hmemN]
    exact hk
  have hdvd : orderOf (l ^ 3) ∣ 3 ^ j := by
    rw [← hj]
    exact orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow])
  have hcop : Nat.Coprime (orderOf (l ^ 3)) (3 ^ j) := by
    rw [hk']
    exact Nat.Coprime.pow _ _ (by norm_num)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem mem_uniqueSet_of_order_three_aux_exists {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hLn : L.Normal) (hOut : OutTwoGroup ↥(barO2 L))
    (hE9 : ∀ A : Subgroup X, A ≤ L → Nat.card A = 3 →
      ∃ E : Subgroup X, A ≤ E ∧ E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 9)
    (hexp : ∀ l ∈ L, (∃ j : ℕ, orderOf l = 3 ^ j) → l ^ 3 ∈ cMHat L → l ^ 3 = 1)
    {A₀ : Subgroup X} (hA₀L : A₀ ≤ L) (hA₀ : Nat.card A₀ = 3) {b : X} (hb : b ^ 3 = 1) :
    ∃ E : Subgroup X, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ ∀ e ∈ E, b * e = e * b := by
  obtain ⟨l, hlL, ⟨j, hj⟩, hlb⟩ := mem_uniqueSet_of_order_three_aux_lift3 hLn hOut hb
  have hl3c : l ^ 3 ∈ cMHat L := by
    set π : X →* X ⧸ CFSG.pCore 2 X := QuotientGroup.mk' (CFSG.pCore 2 X) with hπ
    have hmem : π l ∈ barO2 L := ⟨l, hlL, rfl⟩
    have hd : π (l⁻¹ * b) ∈ Subgroup.centralizer (barO2 L : Set (X ⧸ CFSG.pCore 2 X)) := hlb
    have hπb : π b = π l * π (l⁻¹ * b) := by
      rw [← map_mul]
      congr 1
      group
    have hc : Commute (π l) (π (l⁻¹ * b)) := (Subgroup.mem_centralizer_iff.1 hd) (π l) hmem
    have h1 : (π b) ^ 3 = 1 := by rw [← map_pow, hb, map_one]
    rw [hπb, hc.mul_pow] at h1
    show π (l ^ 3) ∈ cMBar L
    rw [map_pow, eq_inv_of_mul_eq_one_left h1]
    exact inv_mem (pow_mem hd 3)
  have hl3 : l ^ 3 = 1 := hexp l hlL ⟨j, hj⟩ hl3c
  obtain ⟨E, hEL, hEa, hEc, hlE⟩ : ∃ E : Subgroup X, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      ∀ e ∈ E, l * e = e * l := by
    by_cases hl1 : l = 1
    · obtain ⟨E, -, hEL, hEa, hEc⟩ := hE9 A₀ hA₀L hA₀
      exact ⟨E, hEL, hEa, hEc, fun e _ => by rw [hl1, one_mul, mul_one]⟩
    · have hord : orderOf l = 3 := by
        have h1 : orderOf l ∣ 3 := orderOf_dvd_of_pow_eq_one hl3
        rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
        · exact absurd (orderOf_eq_one_iff.1 h) hl1
        · exact h
      have hcard : Nat.card (Subgroup.zpowers l) = 3 := by rw [Nat.card_zpowers, hord]
      obtain ⟨E, hzE, hEL, hEa, hEc⟩ := hE9 (Subgroup.zpowers l) (Subgroup.zpowers_le.2 hlL) hcard
      refine ⟨E, hEL, hEa, hEc, fun e he => ?_⟩
      exact hEa.comm (hzE (Subgroup.mem_zpowers l)) he
  haveI hNn : (O2In L).Normal := by
    haveI := hLn
    unfold O2In
    infer_instance
  have hc : ∀ e ∈ E, b * e * b⁻¹ * e⁻¹ ∈ O2In L := by
    intro e he
    have heL : e ∈ L := hEL he
    have hbd : b = l * (l⁻¹ * b) := by group
    have hu1 : (l⁻¹ * b) * e * (l⁻¹ * b)⁻¹ * e⁻¹ ∈ CFSG.pCore 2 X :=
      exists_conj_centralized_aux_commutator hlb heL
    have hu2 : (l⁻¹ * b) * e * (l⁻¹ * b)⁻¹ * e⁻¹ ∈ L :=
      L.mul_mem (by simpa using hLn.conj_mem e heL (l⁻¹ * b)) (L.inv_mem heL)
    have hu : (l⁻¹ * b) * e * (l⁻¹ * b)⁻¹ * e⁻¹ ∈ O2In L := ⟨hu2, hu1⟩
    have hc2 : Commute l e := hlE e he
    have : b * e * b⁻¹ * e⁻¹ = l * ((l⁻¹ * b) * e * (l⁻¹ * b)⁻¹ * e⁻¹) * l⁻¹ := by
      calc b * e * b⁻¹ * e⁻¹ = l * (l⁻¹ * b) * e * (l * (l⁻¹ * b))⁻¹ * e⁻¹ := by rw [← hbd]
        _ = l * (l⁻¹ * b) * e * (l⁻¹ * b)⁻¹ * (l⁻¹ * e⁻¹) := by group
        _ = l * (l⁻¹ * b) * e * (l⁻¹ * b)⁻¹ * (e⁻¹ * l⁻¹) := by rw [hc2.inv_inv.eq]
        _ = l * ((l⁻¹ * b) * e * (l⁻¹ * b)⁻¹ * e⁻¹) * l⁻¹ := by group
    rw [this]
    exact hNn.conj_mem _ hu l
  have hN2 : IsPGroup 2 (O2In L) := (CFSG.pCore_isPGroup (p := 2) (G := X)).to_le inf_le_right
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hEc]; norm_num)
  have hB : IsPGroup 3 (Subgroup.zpowers b) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (show orderOf b ∣ 3 ^ 1 by simpa using orderOf_dvd_of_pow_eq_one hb)
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨x, hxN, hx⟩ := mem_uniqueSet_of_order_three_aux_cl hN2 hEp hB hc
  have hxL : x ∈ L := hxN.1
  refine ⟨E.map (MulAut.conj x).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    exact L.mul_mem (L.mul_mem hxL (hEL he)) (L.inv_mem hxL)
  · exact CFSG.SectionRank.isElemAbelian_map hEa _
  · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hEc]
  · rintro _ ⟨e, he, rfl⟩
    exact hx e he

theorem mem_uniqueSet_of_order_three_aux_main_gen {G : Type} [Group G] [Finite G]
    {M T : Subgroup G}
    (hO1217 : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O1217At G M)
    (hO991 : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O991At G M)
    {T₁ T₂ : Subgroup ↥M}
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    (h11 : Row1511 G M T T₁ T₂) (h20 : Row1520 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hLn : L.Normal) (hOut : OutTwoGroup ↥(barO2 L))
    (hE9 : ∀ A : Subgroup ↥M, A ≤ L → Nat.card A = 3 →
      ∃ E : Subgroup ↥M, A ≤ E ∧ E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 9)
    (hexp : ∀ l ∈ L, (∃ j : ℕ, orderOf l = 3 ^ j) → l ^ 3 ∈ cMHat L → l ^ 3 = 1)
    {A : Subgroup ↥M} (hAL : A ≤ L) (hA : Nat.card A = 3) :
    A.map M.subtype ∈ uniqueSet M := by
  have hmem : ∀ E : Subgroup ↥M, E ≤ L → IsElemAbelian 3 E → Nat.card E = 9 →
      E.map M.subtype ∈ uniqueSet M := by
    intro E hEL hEa hEc
    have hΓ := gamma_le_of_le_lift_gen hO1217 ctx h11 h20 hLs hL Nat.prime_three (by norm_num)
      hEL hEa hEc
    exact hO991 h11 (E.map M.subtype) (Subgroup.map_subtype_le E)
      (CFSG.SectionRank.isElemAbelian_map hEa M.subtype)
      (by rw [Subgroup.card_map_of_injective M.subtype_injective, hEc]) hΓ
  obtain ⟨E₀, hAE₀, hE₀L, hE₀a, hE₀c⟩ := hE9 A hAL hA
  have hΓ₀ := gamma_le_of_le_lift_gen hO1217 ctx h11 h20 hLs hL Nat.prime_three (by norm_num)
    hE₀L hE₀a hE₀c
  have hAa : IsElemAbelian 3 A := hE₀a.mono hAE₀
  have hAmap : IsElemAbelian 3 (A.map M.subtype) :=
    CFSG.SectionRank.isElemAbelian_map hAa M.subtype
  have hAc : Nat.card (A.map M.subtype) = 3 ^ 1 := by
    rw [Subgroup.card_map_of_injective M.subtype_injective, hA]
    norm_num
  have hk : 1 ≤ CFSG.Open.pRank 3 (A.map M.subtype) :=
    CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_rfl hAmap hAc
  have hN0 : Subgroup.normalizer ((A.map M.subtype : Subgroup G) : Set G) ≤
      rankThreeGamma 1 3 (E₀.map M.subtype) :=
    CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore (Subgroup.map_mono hAE₀) hk
  have hN : Subgroup.normalizer ((A.map M.subtype : Subgroup G) : Set G) ≤ M := hN0.trans hΓ₀
  refine ⟨Subgroup.map_subtype_le A, fun g hg => ?_⟩
  obtain ⟨a₀, ha₀A, ha₀1⟩ : ∃ a ∈ A, a ≠ 1 := by
    have hne : A ≠ ⊥ := by
      intro h0
      rw [h0] at hA
      simp at hA
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  have ha₀3 : a₀ ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (G := ↥A) (x := (⟨a₀, ha₀A⟩ : ↥A))
    rw [hA] at h1
    simpa using congrArg Subtype.val h1
  have hAzp : Subgroup.zpowers a₀ = A := by
    have h1 : Subgroup.zpowers a₀ ≤ A := (Subgroup.zpowers_le).2 ha₀A
    have hord : orderOf a₀ = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one ha₀3) with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) ha₀1
      · exact h
    have h2 : Nat.card (Subgroup.zpowers a₀) = 3 := by rw [Nat.card_zpowers, hord]
    exact Subgroup.eq_of_le_of_card_ge h1 (by rw [h2, hA])
  set aG : G := (a₀ : G) with haG
  have hAG : A.map M.subtype = Subgroup.zpowers aG := by
    rw [← hAzp, MonoidHom.map_zpowers]
    rfl
  have haM : g⁻¹ * aG * g ∈ M :=
    (gamma_le_of_le_lift_aux_mem_map_conj M g aG).1 (hg ⟨a₀, ha₀A, rfl⟩)
  let b : ↥M := ⟨g⁻¹ * aG * g, haM⟩
  have hb3 : b ^ 3 = 1 := by
    apply Subtype.ext
    have h1 : aG ^ 3 = 1 := by simpa using congrArg Subtype.val ha₀3
    show (g⁻¹ * aG * g) ^ 3 = 1
    calc (g⁻¹ * aG * g) ^ 3 = (g⁻¹ * aG * g⁻¹⁻¹) ^ 3 := by rw [inv_inv]
      _ = g⁻¹ * aG ^ 3 * g⁻¹⁻¹ := conj_pow
      _ = 1 := by rw [h1]; group
  obtain ⟨E, hEL, hEa, hEc, hEcomm⟩ :=
    mem_uniqueSet_of_order_three_aux_exists hLn hOut hE9 hexp hAL hA hb3
  have hEU := hmem E hEL hEa hEc
  have hle : E.map M.subtype ≤ M.map (MulAut.conj g⁻¹).toMonoidHom := by
    rintro _ ⟨e, he, rfl⟩
    rw [gamma_le_of_le_lift_aux_mem_map_conj]
    have hcomm : (b : G) * (e : G) = (e : G) * (b : G) := congrArg Subtype.val (hEcomm e he)
    have hbG : (b : G) = g⁻¹ * aG * g := rfl
    have hct : g * (e : G) * g⁻¹ * aG = aG * (g * (e : G) * g⁻¹) := by
      have h1 : aG = g * (b : G) * g⁻¹ := by rw [hbG]; group
      rw [h1]
      calc g * (e : G) * g⁻¹ * (g * (b : G) * g⁻¹) = g * ((e : G) * (b : G)) * g⁻¹ := by group
        _ = g * ((b : G) * (e : G)) * g⁻¹ := by rw [hcomm]
        _ = g * (b : G) * g⁻¹ * (g * (e : G) * g⁻¹) := by group
    have ht : g * (e : G) * g⁻¹ ∈ Subgroup.centralizer ((A.map M.subtype : Subgroup G) : Set G) := by
      rw [hAG, Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact (Commute.zpow_left (show Commute aG (g * (e : G) * g⁻¹) from hct.symm) j).eq
    have htN : g * (e : G) * g⁻¹ ∈ M := hN ((Subgroup.centralizer_le_normalizer _) ht)
    simpa using htN
  have hEq : M.map (MulAut.conj g⁻¹).toMonoidHom = M := hEU.2 g⁻¹ hle
  have key : ∀ y : G, g * y * g⁻¹ ∈ M ↔ y ∈ M := by
    intro y
    have h2 : y ∈ M.map (MulAut.conj g⁻¹).toMonoidHom ↔ y ∈ M := by rw [hEq]
    rw [gamma_le_of_le_lift_aux_mem_map_conj, inv_inv] at h2
    exact h2
  ext x
  rw [gamma_le_of_le_lift_aux_mem_map_conj]
  have h3 := key (g⁻¹ * x * g)
  have h4 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rw [h4] at h3
  exact h3.symm

theorem mem_uniqueSet_of_order_three_aux_cover3 (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd) {S : Type}
    [Group S] [Finite S] (hq : CFSG.Open.IsQuasisimple S) (hodd : Odd (Nat.card (Subgroup.center S)))
    (h3 : 3 ∣ Nat.card (Subgroup.center S)) (hbig : Big1525 (S ⧸ Subgroup.center S)) :
    IsAltSixCoverThree S := by
  rcases hbig with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨Q, hQ2, hQc, d, hd, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · obtain ⟨h67, -⟩ := hKSMAlt S hq 6 ⟨e⟩ hodd
    exact ⟨hq, Nat.dvd_antisymm (h67 (Or.inl rfl)) h3, ⟨e⟩⟩
  · obtain ⟨-, h8⟩ := hKSMAlt S hq 8 ⟨e⟩ hodd
    rw [h8 le_rfl] at h3
    omega
  · exfalso
    have hin : In1512 d.1 := by rw [hd]; exact hQc
    have h1 := (hKSMOdd.1 S hq d hin (fun Q' h => by rw [hd] at h; cases h)
      (fun Q' h => by rw [hd] at h; cases h) ⟨e⟩ hodd).2 (fun Q' h => by rw [hd] at h; cases h)
    rw [h1] at h3
    omega
  · exfalso
    have h1 := hKSMOdd.2 S hq d hd ⟨e⟩ hodd
    rw [h1] at h3
    omega

theorem mem_uniqueSet_of_order_three_aux_hexp_gen (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd)
    {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hl : LiftCtxGen X T T₁ T₂ Ls L) (hbig : Big1525 ↥Ls) :
    ∀ l ∈ L, (∃ j : ℕ, orderOf l = 3 ^ j) → l ^ 3 ∈ cMHat L → l ^ 3 = 1 := by
  rintro l hlL ⟨j, hj⟩ hlc
  set π : X →* X ⧸ CFSG.pCore 2 X := QuotientGroup.mk' (CFSG.pCore 2 X) with hπ
  have hmem : π l ∈ barO2 L := ⟨l, hlL, rfl⟩
  have hx3 : ∃ i : ℕ, orderOf (⟨π l, hmem⟩ : ↥(barO2 L)) = 3 ^ i := by
    have h1 : orderOf (⟨π l, hmem⟩ : ↥(barO2 L)) ∣ 3 ^ j := by
      rw [Subgroup.orderOf_mk, ← hj]
      exact orderOf_map_dvd π l
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
    exact ⟨i, hi⟩
  have hcube : (π l) ^ 3 ∈ Subgroup.centralizer (barO2 L : Set (X ⧸ CFSG.pCore 2 X)) := by
    have : π (l ^ 3) ∈ cMBar L := hlc
    rwa [map_pow] at this
  have hxc : (⟨π l, hmem⟩ : ↥(barO2 L)) ^ 3 ∈ Subgroup.center ↥(barO2 L) := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hcube) y y.2)
  have hq : CFSG.Open.IsQuasisimple ↥(barO2 L) := hl.lift.1.component.2.2
  have hx1 : (⟨π l, hmem⟩ : ↥(barO2 L)) ^ 3 = 1 := by
    obtain ⟨i, hi⟩ := hx3
    by_cases h3 : 3 ∣ Nat.card (Subgroup.center ↥(barO2 L))
    · exact exponent_three_of_isAltSixCoverThree
        (mem_uniqueSet_of_order_three_aux_cover3 hKSMAlt hKSMOdd hq (centre_barO2_odd hl.lift.1) h3
          (mem_uniqueSet_of_order_three_aux_barO2_gen hl hbig)) (k := i)
        (by rw [← hi]; exact pow_orderOf_eq_one _)
    · have h1 : orderOf ((⟨π l, hmem⟩ : ↥(barO2 L)) ^ 3) ∣ 3 ^ i := by
        rw [← hi]
        exact orderOf_dvd_of_pow_eq_one
          (by rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow])
      have h2 : orderOf ((⟨π l, hmem⟩ : ↥(barO2 L)) ^ 3) ∣
          Nat.card (Subgroup.center ↥(barO2 L)) :=
        Subgroup.orderOf_dvd_natCard (Subgroup.center ↥(barO2 L)) hxc
      have hcop : Nat.Coprime (3 ^ i) (Nat.card (Subgroup.center ↥(barO2 L))) :=
        Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hx1' : (π l) ^ 3 = 1 := by
    have := congrArg (fun z : ↥(barO2 L) => (z : X ⧸ CFSG.pCore 2 X)) hx1
    simpa using this
  exact mem_uniqueSet_of_order_three_aux_cube hj hx1'

theorem mem_uniqueSet_of_order_three_of_ksm_gen (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd)
    (kOut : KOut) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    (hO1217 : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O1217At G M)
    (hO991 : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O991At G M)
    {T₁ T₂ : Subgroup ↥M}
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    (hR : LiftRankBound G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hLn : L.Normal) (hbig : Big1525 ↥Ls) {A : Subgroup ↥M} (hAL : A ≤ L) (hA : Nat.card A = 3) :
    A.map M.subtype ∈ uniqueSet M := by
  have hl := hR.liftCtxGen ctx.gn ctx.good hLs hL
  have hq : CFSG.Open.IsQuasisimple ↥(barO2 L) := hl.lift.1.component.2.2
  exact mem_uniqueSet_of_order_three_aux_main_gen hO1217 hO991 ctx h11 h20 hLs hL hLn
    (mem_uniqueSet_of_order_three_aux_outTwo kOut hq
      (mem_uniqueSet_of_order_three_aux_big (mem_uniqueSet_of_order_three_aux_barO2_gen hl hbig)))
    (fun A' hA'L hA' => exists_E9_of_order_three_gen hl hbig hA'L hA')
    (mem_uniqueSet_of_order_three_aux_hexp_gen hKSMAlt hKSMOdd hl hbig) hAL hA

end CFSG.LocalAnalysis.RankThreeUC.S15
