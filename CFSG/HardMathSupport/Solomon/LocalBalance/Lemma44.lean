module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec2Statements
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.TwoLocalTools
public import CFSG.HardMathSupport.Solomon.Proving.Transport
public import CFSG.HardMathSupport.Solomon.LocalBalance.GlueTools
public import CFSG.LocalAnalysis.GL83PartI.I_33

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def Lemma44 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p → p = 5 → ¬ GLCaseOne G p →
    ∀ B : Subgroup G, IsBOneMax p B → ∃ b ∈ B, b ≠ 1 ∧ ∃ L : Subgroup G,
      GLAPComponent 5 (Subgroup.centralizer ({b} : Set G)) L ∧ IsFiTwentyTwo (barOf 5 L)

theorem card_le_of_isCyclic_of_isElemAbelian {G : Type*} [Group G] [Finite G] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) (hp : 0 < p) (hc : IsCyclic E) : Nat.card E ≤ p := by
  have h1 : Monoid.exponent ↥E = Nat.card E := IsCyclic.exponent_eq_card
  have h2 : Monoid.exponent ↥E ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by simpa using hE.2 x x.2)
  rw [← h1]
  exact Nat.le_of_dvd hp h2

theorem eq_bot_of_isPGroup_two_of_odd {G : Type*} [Group G] [Finite G] {H T : Subgroup G}
    (hT : IsPGroup 2 T) (hle : T ≤ H) (hodd : Odd (Nat.card H)) : T = ⊥ := by
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  have hdvd : Nat.card T ∣ Nat.card H := Subgroup.card_dvd_of_le hle
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hne
    have h2 : 2 ∣ Nat.card H := (dvd_pow_self 2 hne).trans hdvd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq T hk

theorem even_card_of_isPGroup_two {G : Type*} [Group G] [Finite G] {Y S : Subgroup G}
    (hS : IsPGroup 2 S) (hne : S ≠ ⊥) (hle : S ≤ Y) : Even (Nat.card Y) := by
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, pow_zero] at hk
    exact hne (Subgroup.eq_bot_of_card_eq S hk)
  have : 2 ∣ Nat.card S := hk ▸ dvd_pow_self 2 hk0
  exact even_iff_two_dvd.2 (this.trans (Subgroup.card_dvd_of_le hle))

theorem false_of_exceptional_five {G : Type} [Group G] [Finite G] {m : ℕ} (hS : GLStanding G m 5)
    {B : Subgroup G} (hB1 : IsBOneMax 5 B) (hweak : IsWeaklyBalancedWrt 5 2 B) {b : G} (hb : b ∈ B)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (B : Set G))))
    {B₀ : Subgroup G} (hB₀B : B₀ ≤ B) (hidx : (B₀.subgroupOf B).index = 25)
    (hrk : CFSG.Open.pRank 5 B <
      CFSG.Open.pRank 5 (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (B₀ : Set G))) :
    False := by
  have hp : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  have hsimple := hS.simple
  have hBel : IsElemAbelian 5 B := hB1.1.1
  have hcardB : Nat.card B = 5 ^ m := hS.card_eq hB1
  have hm4 : 4 ≤ m := hS.four_le
  have hmrank : GLATwoLocalRank 5 G = m := hS.rank_eq
  have hpB : CFSG.Open.pRank 5 B = m := pRank_eq_of_card hp hBel hcardB
  have hB₀card : Nat.card B₀ = 5 ^ (m - 2) := by
    have h1 := Subgroup.card_mul_index (B₀.subgroupOf B)
    rw [hidx] at h1
    have h2 : Nat.card (B₀.subgroupOf B) = Nat.card B₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₀B).toEquiv
    rw [h2, hcardB] at h1
    have h3 : (5 : ℕ) ^ m = 5 ^ (m - 2) * 25 := by
      rw [show (25 : ℕ) = 5 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    rw [h3] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have hB₀el : IsElemAbelian 5 B₀ := isElemAbelian_mono hBel hB₀B
  have hB₀ne : B₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hB₀card
    have : 5 ^ 1 ≤ 5 ^ (m - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hB₀nc : ¬ IsCyclic B₀ := fun hc => by
    have := card_le_of_isCyclic_of_isElemAbelian hB₀el (by norm_num) hc
    rw [hB₀card] at this
    have h25 : 5 ^ 2 ≤ 5 ^ (m - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨E, hEle, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
    (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (B₀ : Set G))
  have hEgt : m < CFSG.Open.pRank 5 E := by
    rw [pRank_eq_of_card hp hEel hEcard]; rw [hpB] at hrk; exact hrk
  have hEB₀ : ∀ x ∈ B₀, E ≤ Subgroup.centralizer ({x} : Set G) := by
    intro x hx e he
    have h2 : e ∈ Subgroup.centralizer (B₀ : Set G) := (hEle he).2
    rw [Subgroup.mem_centralizer_iff] at h2 ⊢
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact h2 x hx
  have hodd5 : ∀ x ∈ B₀, x ≠ 1 →
      Odd (Nat.card (GLAPPrimeCoreOf 5 (Subgroup.centralizer ({x} : Set G)))) := by
    intro x hx hx1
    by_contra hev
    have hev' : Even (Nat.card (GLAPPrimeCoreOf 5 (Subgroup.centralizer ({x} : Set G)))) :=
      Nat.not_odd_iff_even.1 hev
    obtain ⟨T, hT, -, hT2, hET⟩ := exists_twoGroup_normalized_of_coprime_even hp (by norm_num)
      (GL83.isPGroup_of_isElemAbelian hEel)
      ((hEB₀ x hx).trans (le_normalizer_glaPPrimeCoreOf 5 _)) (not_dvd_card_glaPPrimeCoreOf hp _)
      hev'
    have := pRank_le_glaTwoLocalRank_of_normalizes (G := G) hp hT hT2 hET
    omega
  obtain ⟨-, D, hDB, hDpl, hDeven⟩ := hB1
  have hD1 : D ≠ ⊥ := by
    intro h
    have h1 := hDpl.2
    rw [h, Subgroup.card_bot] at h1
    have : 1 < 5 ^ 2 := by norm_num
    omega
  have hBD : B ≤ Subgroup.normalizer (D : Set G) := by
    refine le_trans (fun e he => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (elemAbelian_comm hBel he (hDB hy)).symm
  have hBΔ : B ≤ Subgroup.normalizer (GLADelta 5 D : Set G) :=
    hBD.trans (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_normalizer_glaDelta 5 D)
  obtain ⟨T, hT, hTΔ, hT2, hBT⟩ := exists_twoGroup_normalized_of_coprime_even hp (by norm_num)
    (GL83.isPGroup_of_isElemAbelian hBel) hBΔ
    (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLADelta hp hD1 |>
      (hp.coprime_iff_not_dvd).1) hDeven
  have hgen := GL83.le_iSup_hyperplane hp (by norm_num) hB₀ne hB₀el hT2 (hB₀B.trans hBT)
  have hex : ∃ A : Subgroup G, A ≤ B₀ ∧ (A.subgroupOf B₀).index = 5 ∧
      T ⊓ Subgroup.centralizer (A : Set G) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hT
    refine le_bot_iff.1 (hgen.trans (iSup₂_le fun A hA => ?_))
    exact le_bot_iff.2 (hcon A hA.1 hA.2)
  obtain ⟨A, hAB₀, hAidx, hAT⟩ := hex
  have hAcard : Nat.card A = 5 ^ (m - 3) :=
    card_eq_of_index_eq hp hAB₀ hAidx (by rw [show m - 3 + 1 = m - 2 by omega]; exact hB₀card)
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hAcard
    have : 5 ^ 1 ≤ 5 ^ (m - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨⟨x, hxA⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hAne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxB₀ : x ∈ B₀ := hAB₀ hxA
  have hxB : x ∈ B := hB₀B hxB₀
  have hDek : IsEkIn 5 2 B D := ⟨hDB, hDpl.1, hDpl.2⟩
  have hw := hweak D hDek x hxB hx1'
  set T₁ : Subgroup G := T ⊓ Subgroup.centralizer ({x} : Set G) with hT₁
  have hT₁ne : T₁ ≠ ⊥ := by
    intro h
    apply hAT
    refine le_bot_iff.1 (h ▸ ?_)
    exact inf_le_inf_left T (Subgroup.centralizer_le (by simpa using hxA))
  have hT₁sub : T₁ ≤ GLADelta 5 D ⊓ Subgroup.centralizer ({x} : Set G) :=
    le_inf (inf_le_left.trans hTΔ) inf_le_right
  have hT₁2 : IsPGroup 2 T₁ := hT2.to_le inf_le_left
  have hTB : ⁅T, B⁆ ≤ T := GL83.commutator_le_of_le_normalizer hBT
  have hcomm_le : ⁅T₁, B⁆ ≤ GLAPPrimeCoreOf 5 (Subgroup.centralizer ({x} : Set G)) :=
    (Subgroup.commutator_mono hT₁sub le_rfl).trans hw
  have hcomm_ne : ⁅T₁, B⁆ ≠ ⊥ := by
    intro h
    have hc : T₁ ≤ Subgroup.centralizer (B : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    have hcb : T₁ ≤ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (B : Set G) :=
      le_inf (hc.trans (Subgroup.centralizer_le (by simpa using hb))) hc
    exact hT₁ne (eq_bot_of_isPGroup_two_of_odd hT₁2 hcb hodd)
  have h2g : IsPGroup 2 (⁅T₁, B⁆ : Subgroup G) :=
    hT2.to_le ((Subgroup.commutator_mono inf_le_left le_rfl).trans hTB)
  have hev := even_card_of_isPGroup_two h2g hcomm_ne hcomm_le
  exact (Nat.not_even_iff_odd.2 (hodd5 x hxB₀ hx1')) hev

theorem lemma44_of_inputs (h31 : Lemma31) (h24 : Lemma24) (i22 : Input19_2_2)
    (i1910 : Input19_10) : Lemma44 := by
  intro G _ _ m p hS hp5 hnc B hB1
  subst hp5
  have hp : Nat.Prime 5 := by norm_num
  have hsimple := hS.simple
  have hBmax : GLAIsBmax 5 B := hB1.1
  have hBel : IsElemAbelian 5 B := hBmax.1
  obtain ⟨D₀, hD₀B, hD₀pl, hD₀ev⟩ := hB1.2
  have hB0 : IsBZeroMax 5 B :=
    ⟨hBmax, D₀, hD₀B, hD₀pl, fun _ => hD₀ev, fun h => absurd h (by norm_num)⟩
  have hsc : IsSCp 5 ⊤ B := lemma23_proved G m 5 hS B hB1
  have hpB : CFSG.Open.pRank 5 B = m := pRank_eq_of_card hp hBel (hS.card_eq hB1)
  have hm4 : 4 ≤ m := hS.four_le
  by_contra hno
  push Not at hno
  have hweak : IsWeaklyBalancedWrt 5 2 B := by
    by_contra hnot
    have hex : ∃ D : Subgroup G, IsEkIn 5 2 B D ∧ ∃ b ∈ B, b ≠ 1 ∧
        ¬ delta2At 5 B D b ≤ GLAPPrimeCoreOf 5 (Subgroup.centralizer ({b} : Set G)) := by
      by_contra hcon
      push Not at hcon
      exact hnot fun D hD b hb hb1 => hcon D hD b hb hb1
    obtain ⟨D, hD, b, hb, hb1, hX⟩ := hex
    exact absurd (h24 G m 5 hS B hB1 hnot D hD b hb hb1 hX).1 (by norm_num)
  have hEq : lambdaStarGroup 5 B = psiStarGroup 5 B := by
    refine lambdaStarGroup_eq_psiStarGroup_of_forall fun b hb hb1 => ?_
    have hM : lambdaMOf 5 B b = ⊥ := le_bot_iff.1 (sSup_le fun L hL =>
      absurd hL.2.2.2.2 (hno b hb hb1 L hL.1))
    rw [lambdaOf_eq_psiOf_sup_lambdaMOf_of_five h31 hS hBmax hsc hb hb1, hM, sup_bot_eq]
  have hbal : IsBalancedWrt 5 2 B := by
    refine i22 G hS.nonabelian hS.kProper 5 hp (by norm_num) B hBel 2 (by norm_num) fun b hb hb1 J hJ => ?_
    have hCbne : Subgroup.centralizer ({b} : Set G) ≠ ⊤ :=
      centralizer_ne_top_of_simple hS.nonabelian hb1
    have hBCb : B ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.2 (elemAbelian_comm hBel hx hb)
    have hrank : GLATwoLocalRank 5 ↥(Subgroup.centralizer ({b} : Set G)) ≤
        CFSG.Open.pRank 5 B := by
      rw [hpB, ← hS.rank_eq]
      exact glaTwoLocalRank_subgroup_le hp _
    obtain ⟨-, -, h3⟩ := i1910 G hS.nonabelian hS.kProper 5 hp (by norm_num)
      (Subgroup.centralizer ({b} : Set G)) hCbne B hBCb hBel hrank J hJ
    rcases h3 (by omega) with hloc | ⟨-, hM⟩ | ⟨h53, -⟩ | ⟨-, -, hodd, B₀, hB₀B, hidx, hrk⟩
    · exact hloc
    · exact absurd hM (hno b hb hb1 J hJ)
    · exact absurd h53 (by norm_num)
    · exact (false_of_exceptional_five hS hB1 hweak hb hodd hB₀B hidx hrk).elim
  exact hnc ⟨B, hB1, hbal, hEq⟩

end CFSG.HardMathSupport.Solomon.LocalBalance
