module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTwoGroupCases
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveMain
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34LocalGroup
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallM11Local
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
public import Certificates.Data.ONanSmallM11
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TwoSignalizer

open CFSG.Open Subgroup
open scoped commutatorElement

section Inner

variable {X : Type} [Group X] [Finite X]

theorem commutator_eq_bot_of_inner {K B T : Subgroup X} [K.Normal] (hBK : B ≤ K)
    (hBT : B ≤ normalizer (T : Set X))
    (hin : ∀ U : Subgroup X, U ≤ K → U ≤ T → B ≤ normalizer (U : Set X) → U = ⊥) :
    ⁅B, T⁆ = ⊥ := by
  have hU : T ⊓ K = ⊥ := by
    refine hin _ inf_le_right inf_le_left fun b hb => ?_
    refine mem_normalizer_fintype fun u hu => ?_
    obtain ⟨huT, huK⟩ := Subgroup.mem_inf.1 hu
    exact Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (hBT hb) u).1 huT,
      ‹K.Normal›.conj_mem u huK b⟩
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro b hb t ht
  have h1 : ⁅b, t⁆ ∈ T := by
    have h3 : b * t * b⁻¹ ∈ T := (mem_normalizer_iff.1 (hBT hb) t).1 ht
    simpa [commutatorElement_def] using T.mul_mem h3 (T.inv_mem ht)
  have h2 : ⁅b, t⁆ ∈ K := by
    have h3 : t * b⁻¹ * t⁻¹ ∈ K := ‹K.Normal›.conj_mem b⁻¹ (K.inv_mem (hBK hb)) t
    simpa [commutatorElement_def, mul_assoc] using K.mul_mem (hBK hb) h3
  have h4 : ⁅b, t⁆ ∈ T ⊓ K := Subgroup.mem_inf.2 ⟨h1, h2⟩
  rw [hU] at h4
  exact h4

theorem commutator_eq_bot_of_noTwo {K B T : Subgroup X} [K.Normal] (hBK : B ≤ K)
    (hT : IsPGroup 2 T) (hBT : B ≤ normalizer (T : Set X))
    (hno : ∀ U : Subgroup ↥K, IsPGroup 2 U → B.subgroupOf K ≤ normalizer (U : Set ↥K) →
      U = ⊥) :
    ⁅B, T⁆ = ⊥ := by
  refine commutator_eq_bot_of_inner hBK hBT fun U hUK hUT hBU => ?_
  have hU2 : IsPGroup 2 (U.subgroupOf K) := (hT.to_le hUT).comap_subtype
  have hbot : U.subgroupOf K = ⊥ := by
    refine hno _ hU2 fun b hb => ?_
    refine mem_normalizer_fintype fun n hn => ?_
    exact (mem_normalizer_iff.1 (hBU hb) (n : X)).1 hn
  rw [eq_bot_iff]
  intro u hu
  have h1 : (⟨u, hUK hu⟩ : ↥K) ∈ U.subgroupOf K := hu
  rw [hbot, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)

end Inner

section Fi22

theorem twoSignalizerFi22_holds :
    TwoSignalizerOn 5 fun _ _ K B =>
      Nonempty (↥K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group) ∧ B ≤ K := by
  intro X _ _ K hKn _hs _hnab B _hB hBc _hBC hcase T hT hBT
  obtain ⟨hK, hBK⟩ := hcase
  obtain ⟨φ⟩ := hK
  haveI : K.Normal := hKn
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have hcardK : Nat.card K = 64561751654400 := by
    rw [Nat.card_congr (φ.trans β.symm).toEquiv]
    exact CFSG.Sporadic.Fi22.card_Fi22
  have hfac : (Nat.card K).factorization 5 = 2 := by
    rw [hcardK, show (64561751654400 : ℕ) = 5 ^ 2 * 2582470066176 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hcardB : Nat.card (B.subgroupOf K) = 5 ^ (Nat.card K).factorization 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv, hBc, hfac]
  refine le_of_eq_of_le (commutator_eq_bot_of_noTwo hBK hT hBT fun U hU hBU => ?_) bot_le
  exact CFSG.AGLEmbedding.kFactFi22NoTwo ↥K ⟨φ⟩ (Sylow.ofCard (B.subgroupOf K) hcardB) U hU hBU

end Fi22

section M11

open Certificates.ONanSmallM11 CFSG.AGLEmbedding.KFactProofs.SmallIdent CFSG.Blueprint

private theorem fix_of_mem_m11E {q : Equiv.Perm (Fin 11)} (hq : q ∈ m11E) (hq1 : q ≠ 1) :
    q 0 = 0 ∧ q 1 = 1 ∧ ∀ a : Fin 11, q a = a → a = 0 ∨ a = 1 := by
  simp only [m11E, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq1
  all_goals exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

private theorem cube_of_mem_m11E {q : Equiv.Perm (Fin 11)} (hq : q ∈ m11E) : q ^ 3 = 1 := by
  simp only [m11E, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_pow 3
  all_goals decide +kernel

private theorem noTwo_map {G M : Type} [Group G] [Group M] (Φ : M ≃* G) {R : Subgroup M}
    (h : ∀ U : Subgroup M, IsPGroup 2 U → R ≤ normalizer (U : Set M) → U = ⊥)
    (U : Subgroup G) (hU : IsPGroup 2 U) (hRU : R.map Φ.toMonoidHom ≤ normalizer (U : Set G)) :
    U = ⊥ := by
  have hU' : IsPGroup 2 (U.comap Φ.toMonoidHom) :=
    hU.comap_of_injective Φ.toMonoidHom Φ.injective
  have hbot : U.comap Φ.toMonoidHom = ⊥ := by
    refine h _ hU' fun r hr => ?_
    rw [mem_normalizer_iff]
    intro x
    simpa using mem_normalizer_iff.1 (hRU ⟨r, hr, rfl⟩) (Φ x)
  rw [eq_bot_iff]
  intro u hu
  have h1 : Φ.symm u ∈ U.comap Φ.toMonoidHom := by simpa using hu
  rw [hbot, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  simpa using congrArg Φ h1


private theorem glbCore_m11T0_le :
    GLBCore 3 1 m11T0 ≤ normalizer ((m11T0 : Subgroup ↥NativeSporadic.M11) :
      Set ↥NativeSporadic.M11) := by
  refine sSup_le ?_
  rintro N ⟨Q, hQT, hQ, rfl⟩
  have hQ' : Q ≠ ⊥ :=
    CFSG.AGLEmbedding.KFactProofs.L34Local.LocalData.ne_bot_of_one_le_pRank (by norm_num) hQ
  obtain ⟨q, hq⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQ'
  intro g hg
  have hr : g * (q : ↥NativeSporadic.M11) * g⁻¹ ∈ Q := (mem_normalizer_iff.1 hg q).1 q.2
  have hqE := mem_m11T0_iff_mem_m11E.1 (hQT q.2)
  have hrE := mem_m11T0_iff_mem_m11E.1 (hQT hr)
  set gp : Equiv.Perm (Fin 11) := (g : Equiv.Perm (Fin 11)) with hgp
  set qp : Equiv.Perm (Fin 11) := ((q : ↥NativeSporadic.M11) : Equiv.Perm (Fin 11)) with hqp
  have hq1 : qp ≠ 1 := fun h => hq (Subtype.ext (Subtype.ext h))
  have hr1 : gp * qp * gp⁻¹ ≠ 1 := by
    intro h
    apply hq1
    calc qp = gp⁻¹ * (gp * qp * gp⁻¹) * gp := by group
      _ = 1 := by rw [h]; group
  obtain ⟨hq0, hq1', -⟩ := fix_of_mem_m11E hqE hq1
  obtain ⟨-, -, hrfix⟩ := fix_of_mem_m11E hrE hr1
  have hmap : ∀ a : Fin 11, qp a = a → gp a = 0 ∨ gp a = 1 := by
    intro a ha
    apply hrfix
    change (gp * qp * gp⁻¹) (gp a) = gp a
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
      Equiv.symm_apply_apply, ha]
  have h0 := hmap 0 hq0
  have h1 := hmap 1 hq1'
  have hne : gp 0 ≠ gp 1 := fun h => absurd (gp.injective h) (by decide)
  rw [normalizer_m11T0, mem_stabilizer_duad_iff g (by decide)]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact absurd (h0.trans h1.symm) hne
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h0, h1⟩
  · exact absurd (h0.trans h1.symm) hne

private theorem noTwo_m11T0 (U : Subgroup ↥NativeSporadic.M11)
    (hU : IsPGroup 2 U)
    (hEU : m11T0 ≤ normalizer (U : Set ↥NativeSporadic.M11)) : U = ⊥ := by
  obtain ⟨S, hS⟩ := exists_sylow_m11T0
  have hcard : Nat.card (S : Subgroup ↥NativeSporadic.M11) = 9 := by rw [hS]; exact card_m11T0
  have hdvd : 3 ^ 2 ∣ Nat.card S := by
    rw [show Nat.card S = Nat.card (S : Subgroup ↥NativeSporadic.M11) from rfl, hcard]
    norm_num
  refine noTwo_of_gamma_le_normalizer Nat.prime_three (by norm_num) S hdvd
    (fun s hs => ?_) (hS ▸ glbCore_m11T0_le) (fun g hg => ?_) U hU (hS ▸ hEU)
  · have hs' : (s : Equiv.Perm (Fin 11)) ∈ m11E := mem_m11T0_iff_mem_m11E.1 (hS ▸ hs)
    exact Subtype.ext (cube_of_mem_m11E hs')
  · exact hS ▸ centralizer_le_m11T0 g (fun t ht => hg t (hS ▸ ht))

end M11

section M11Main

open CFSG.AGLEmbedding.KFactProofs.SmallIdent CFSG.Blueprint

theorem twoSignalizerM11_holds :
    TwoSignalizerM11 := by
  intro X _ _ K hKn _hs _hnab B _hB hBc _hBC hcase T hT hBT
  obtain ⟨hK, hBK⟩ := hcase
  obtain ⟨φ⟩ := hK
  haveI : K.Normal := hKn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  let e : ↥K ≃* ↥NativeSporadic.M11 := φ.trans β.symm
  have hcardK : Nat.card K = 7920 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M11
  have hfac : (Nat.card K).factorization 3 = 2 := by
    rw [hcardK, show (7920 : ℕ) = 3 ^ 2 * 880 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hcardB : Nat.card (B.subgroupOf K) = 3 ^ (Nat.card K).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv, hBc, hfac]
  obtain ⟨T₀, hT₀⟩ := exists_sylow_m11T0
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow e (R := m11T0)
    (by rw [← hT₀]; exact T₀.isPGroup') (by rw [← hT₀]; exact T₀.not_dvd_index)
    (Sylow.ofCard (B.subgroupOf K) hcardB)
  have hΦ' : B.subgroupOf K = m11T0.map Φ.toMonoidHom := hΦ
  refine le_of_eq_of_le (commutator_eq_bot_of_noTwo hBK hT hBT fun U hU hBU => ?_) bot_le
  exact noTwo_map Φ (fun V hV hEV => noTwo_m11T0 V hV hEV) U hU (hΦ' ▸ hBU)

end M11Main

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TwoSignalizer
