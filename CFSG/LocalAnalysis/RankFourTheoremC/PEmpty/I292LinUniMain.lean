module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292LinUniCent
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62Lift
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294Lemmas
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.GLTheoremB.Input20_1Proof
import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292LinUniDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (IsMaxTwoInvariantIn)
open CFSG.LocalAnalysis.GLTheoremB (IsSCp centralizes_pCore_of_isSCp input20_1_proved
  isSCp_subgroupOf)

namespace I292

variable {Y : Type} [Group Y]

theorem conj_mem_omegaOneTwo {T L : Subgroup Y} [L.Normal] {g : Y}
    (hg : g ∈ normalizer (T : Set Y)) {h : Y} (hh : h ∈ omegaOneTwo T L) :
    g * h * g⁻¹ ∈ omegaOneTwo T L := by
  have hsub : (omegaOneTwo T L).map (MulAut.conj g).toMonoidHom ≤ omegaOneTwo T L := by
    unfold omegaOneTwo
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨s, ⟨hsTL, hs2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 hg s).1 (Subgroup.mem_inf.1 hsTL).1
      · exact ‹L.Normal›.conj_mem s (Subgroup.mem_inf.1 hsTL).2 g
    · show ((MulAut.conj g).toMonoidHom s) ^ 2 = 1
      rw [← map_pow, hs2, map_one]
  exact hsub ⟨h, hh, rfl⟩

theorem mem_normalizer_omegaOneTwo {T L : Subgroup Y} [L.Normal] {g : Y}
    (hg : g ∈ normalizer (T : Set Y)) : g ∈ normalizer (omegaOneTwo T L : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_omegaOneTwo hg hh, fun hh => ?_⟩
  have := conj_mem_omegaOneTwo (Subgroup.inv_mem _ hg) hh
  simpa [mul_assoc] using this

theorem le_normalizer_map_subtype {N : Subgroup Y} (O : Subgroup ↥N) [O.Normal] :
    N ≤ normalizer ((O.map N.subtype : Subgroup Y) : Set Y) := by
  have key : ∀ n : ↥N, ∀ y ∈ O.map N.subtype, (n : Y) * y * (n : Y)⁻¹ ∈ O.map N.subtype := by
    rintro n _ ⟨o, ho, rfl⟩
    exact ⟨n * o * n⁻¹, ‹O.Normal›.conj_mem o ho n, by simp⟩
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key ⟨n, hn⟩ y, fun hy => ?_⟩
  have := key ⟨n, hn⟩⁻¹ _ hy
  simpa [mul_assoc] using this

theorem mem_map_conj_iff' {T : Subgroup Y} {c y : Y} :
    y ∈ T.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * y * c ∈ T := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ht
  · intro h
    exact ⟨c⁻¹ * y * c, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem exists_conj_normalizes [Finite Y] {p : ℕ} (hp : p.Prime) {K T Q : Subgroup Y}
    (hK : ¬ p ∣ Nat.card K) (hT : fusionIsSylowIn 2 T K) (hQp : IsPGroup p Q)
    (hQK : Q ≤ normalizer (K : Set Y)) :
    ∃ c ∈ K, ∀ q ∈ Q, c⁻¹ * q * c ∈ normalizer (T : Set Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hbotp : IsPGroup p (⊥ : Subgroup Y) := IsPGroup.of_bot
  obtain ⟨S, hS, -, hQS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing hp
    Nat.prime_two hQp hK hQK (bot_le : (⊥ : Subgroup Y) ≤ K) IsPGroup.of_bot
    (fun g _ => by rw [Subgroup.normalizer_eq_top]; trivial)
  obtain ⟨c, hcK, hc⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows hp Nat.prime_two
    (A := ⊥) (M := K) (S := T) (S' := S) hbotp hK bot_le hT hS bot_le bot_le
  refine ⟨c, (Subgroup.mem_inf.1 hcK).1, fun q hq => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro t
  have hmem : ∀ y, y ∈ S ↔ c⁻¹ * y * c ∈ T := fun y => by rw [hc]; exact mem_map_conj_iff'
  have h1 := Subgroup.mem_normalizer_iff.1 (hQS hq) (c * t * c⁻¹)
  rw [hmem, hmem] at h1
  have e1 : c⁻¹ * (c * t * c⁻¹) * c = t := by group
  have e2 : c⁻¹ * (q * (c * t * c⁻¹) * q⁻¹) * c = (c⁻¹ * q * c) * t * (c⁻¹ * q * c)⁻¹ := by
    group
  rw [e1, e2] at h1
  exact h1

theorem exists_sylow_le_of_conj {p : ℕ} (Q : Sylow p Y) (c : Y) {M : Subgroup Y}
    (h : ∀ q ∈ (Q : Subgroup Y), c⁻¹ * q * c ∈ M) :
    ∃ Q' : Sylow p Y, (Q' : Subgroup Y) ≤ M := by
  refine ⟨c⁻¹ • Q, fun y hy => ?_⟩
  have hy' : y ∈ (Q : Subgroup Y).map (MulAut.conj c⁻¹).toMonoidHom := hy
  obtain ⟨q, hq, rfl⟩ := hy'
  have := h q hq
  simpa [MulAut.conj_apply] using this

theorem isSCp_plane [Finite Y] {p : ℕ} [Fact p.Prime] {P : Subgroup Y} {x z : Y}
    (hYD : YData p Y P x z) : IsSCp p ⊤ (zpowers x ⊔ zpowers z) := by
  have hcfg := hYD.cfg
  have hXe : IsElemAbelian p (zpowers x) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1
      (CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hcfg.x_pow)
  have hZe : IsElemAbelian p (zpowers z) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1
      (CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hcfg.z_pow)
  have hBe : IsElemAbelian p (zpowers x ⊔ zpowers z) :=
    K62B.isElemAbelian_sup hXe hZe
      (fun a ha b hb => hcfg.zpowers_central hb (zpowers_le.2 hcfg.x_mem ha))
  refine ⟨le_top, hBe, fun E _ hE hBE => ?_⟩
  refine le_antisymm (fun y hy => ?_) hBE
  have hyc : y ∈ centralizer ((zpowers x ⊔ zpowers z : Subgroup Y) : Set Y) := by
    rw [mem_centralizer_iff]
    intro b hb
    exact CFSG.Open.IsElemAbelian.comm hE (hBE hb) hy
  exact hYD.sc y hyc (hE.2 y hy)

end I292

theorem kd292LinUni_of_kdata (h0 : KD291LinUniZero) (hM : KD291LinUniModel)
    (hAL : KD292CaseALin) (hAU : KD292CaseAUni) (hBS : KD292CaseBSylow)
    (hBC : KD292CaseBConstr) : KD292LinUni := by
  intro p Y _ _ P x z hYD L hL hLu hlu T hT
  have hcfg : LinUniCfg p P x z L := ⟨hYD, hL, hLu, hlu⟩
  have hshape : LinUniShape p x L := ⟨h0 p Y P x z L hcfg, hM p Y P x z L hcfg⟩
  have hY := hYD.cfg
  have hp : p.Prime := hY.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by have := hY.five_le; omega
  haveI hLn : L.Normal := I291.normal_of_unique hL hLu
  set B : Subgroup Y := zpowers x ⊔ zpowers z with hBdef
  have hSC : IsSCp p ⊤ B := I292.isSCp_plane hYD
  have hBp : IsPGroup p B := IsPGroup.of_card (n := 2) hYD.plane_card
  have hT2 : IsPGroup 2 T := hT.1.2.1
  have hBT : B ≤ normalizer (T : Set Y) := hT.1.2.2
  have hxT : x ∈ normalizer (T : Set Y) := hBT (Subgroup.mem_sup_left (mem_zpowers x))
  have hTP : T ≤ centralizer (CFSG.pCore p Y : Set Y) :=
    centralizes_pCore_of_isSCp input20_1_proved hp hp2 hSC hT2 hBT
  have hCeq : centralizer (L : Set Y) = CFSG.pCore p Y :=
    I292.centralizer_eq_pCore hY.core hL hLu hshape.zero.pCore_cyclic hshape.zero.omega_le
  have hTC : ∀ t ∈ T, ∀ r ∈ centralizer (L : Set Y), t * r = r * t := by
    intro t ht r hr
    rw [hCeq] at hr
    exact ((Subgroup.mem_centralizer_iff.1 (hTP ht)) r hr).symm
  by_cases hTL : T ⊓ L = ⊥
  ·
    rcases hshape.model with hlin | huni
    · obtain ⟨Q, hQ⟩ := hAL p Y P x z L hcfg hshape.zero hlin T hT2 hxT hTC hTL
      exact ⟨Q, fun g hg => Subgroup.centralizer_le_normalizer _ (hQ hg)⟩
    · have hT1 : T = ⊥ := hAU p Y P x z L hcfg hshape.zero huni T hT2 hxT hTC hTL
      obtain ⟨Q⟩ : Nonempty (Sylow p Y) := inferInstance
      refine ⟨Q, fun g _ => ?_⟩
      rw [hT1, Subgroup.normalizer_eq_top]
      trivial
  ·
    have hlay := hBC p Y P x z L hcfg hshape T hT2 hxT hTC hTL
    obtain ⟨Q, hQN⟩ := hBS p Y P x z L hcfg hshape T hT2 hxT hTC hTL
    set N : Subgroup Y := normalizer (omegaOneTwo T L : Set Y) with hNdef
    have hTN : T ≤ N := fun t ht => I292.mem_normalizer_omegaOneTwo (Subgroup.le_normalizer ht)
    have hBN : B ≤ N := fun b hb => I292.mem_normalizer_omegaOneTwo (hBT hb)
    have hlayer : GLAPLayer p (⊤ : Subgroup ↥N) = ⊥ :=
      CFSG.LocalAnalysis.RankFourTheoremC.glaPLayer_top_eq_bot_of_subgroup hp N hlay
    have hSC' : IsSCp p ⊤ (B.subgroupOf N) := isSCp_subgroupOf hSC hBN
    have key := GL83.I_20_1_proved ↥N p hp hp2 hlayer (B.subgroupOf N) hSC'.2.1
      (fun E hE hBE => hSC'.2.2 E le_top hE hBE)
    have hT'cop : Nat.Coprime p (Nat.card (T.subgroupOf N)) := by
      obtain ⟨k, hk⟩ := hT2.exists_card_eq
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv, hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have hT'norm : B.subgroupOf N ≤ normalizer ((T.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
      intro b hb
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have := Subgroup.mem_normalizer_iff.1 (hBT ((Subgroup.mem_subgroupOf).1 hb)) (y : Y)
      simpa [Subgroup.mem_subgroupOf] using this
    have hT'O : T.subgroupOf N ≤ GLAPPrimeCoreOf p (⊤ : Subgroup ↥N) := by
      rw [← key]
      exact le_iSup_of_le _ (le_iSup_of_le hT'cop (le_iSup_of_le hT'norm le_rfl))
    rw [GL83.glaPPrimeCoreOf_top_eq] at hT'O
    set O : Subgroup ↥N := primeComplementCore (G := ↥N) p with hO
    haveI hOn : O.Normal := inferInstance
    set K : Subgroup Y := O.map N.subtype with hK
    have hTK : T ≤ K := fun t ht => ⟨⟨t, hTN ht⟩, hT'O (Subgroup.mem_subgroupOf.2 ht), rfl⟩
    have hKcop : ¬ p ∣ Nat.card K := by
      rw [hK, Subgroup.card_map_of_injective N.subtype_injective]
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 (primeComplementCore_coprime p)
    have hNK : N ≤ normalizer (K : Set Y) := I292.le_normalizer_map_subtype O
    have hKfus : fusionIsSylowIn 2 T K :=
      K62.fusionIsSylowIn_of_isMax hp hBp hT hTK hKcop (hBN.trans hNK)
    obtain ⟨c, -, hc⟩ := I292.exists_conj_normalizes hp hKcop hKfus Q.isPGroup' (hQN.trans hNK)
    exact I292.exists_sylow_le_of_conj Q c hc

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
