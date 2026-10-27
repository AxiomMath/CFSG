module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L76B
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L76C
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Triple
public import CFSG.HardMathSupport.Solomon.Proving.CoprimeSylow

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_card_of_isPGroup_two {T : Subgroup G} (hT : IsPGroup 2 T) :
    ¬ 3 ∣ Nat.card T := by
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  rw [hk]
  intro h3
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)


open scoped commutatorElement

theorem lemma76_of_lemma75 (i116 : Input11_6) (hS : GLStanding G 4 3) {B : Subgroup G}
    (hB : IsBOneMax 3 B) (h68 : Prop68Out B) (h75 : Lemma75Stmt B) : Lemma76Stmt B := by
  intro K hK N hNtop hKM I hI hbar
  have hf := h68 K hK
  have hB3 : IsElemAbelian 3 B := hB.1.1
  have hBM2 : B ≤ gammaOneThree B := le_gammaOneThree_self hS hB
  have hKN : K ≤ N := le_sup_left.trans hKM
  have hM2N : gammaOneThree B ≤ N := le_sup_right.trans hKM
  have hBN : B ≤ N := hBM2.trans hM2N
  obtain ⟨⟨x, hxB, hx1, hxK⟩, -, -⟩ := id hK
  have hKK : GLAPComponent 3 K K := glaPComponent_of_le Nat.prime_three hxK le_rfl hxK.1
  have hlayer : GLAPLayer 3 K = K := le_antisymm (glaPLayer_le 3 K) (le_sSup hKK)
  have hcomp : IsComponentOf (barX 3 N K) ⊤ := by
    have := h75 K hK N hNtop hBN (le_sup_of_le_left (le_inf hKN le_rfl))
    rwa [inf_eq_left.2 hKN, hlayer] at this
  have hOKN : GLAPPrimeCoreOf 3 K ≤ GLAPPrimeCoreOf 3 N :=
    glaPPrimeCoreOf_le_of_barX_component Nat.prime_three hKN hcomp
  have hL34 : IsLThreeFour ↥(barX 3 N K) := isLThreeFour_barX hKN hOKN hf.lThreeFour
  have hsimp := (isSimpleGroup_of_isLThreeFour hL34).1
  have hcard : Nat.card (barX 3 N K) = 20160 := card_eq_of_isLThreeFour hL34
  have hnot2 : ¬ IsPGroup 2 (barX 3 N K) := by
    intro h2
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rw [hcard] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 20160)
    exact absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)) (by norm_num)
  have hBI : B ≤ Subgroup.normalizer (I : Set G) :=
    le_normalizer_of_barX_eq hBN hKN hf.normalizes hI hbar
  obtain ⟨U, hU1, hU2, hBU⟩ := hB.1.2.2
  obtain ⟨T, hTmax, hUT⟩ := Sec7.exists_isMaxBInvariantTwo B U hU2 hBU
  have hT1 : T ≠ ⊥ := fun h => hU1 (le_bot_iff.1 (h ▸ hUT))
  have hCT : B ⊓ Subgroup.centralizer (T : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_isMaxBInvariantTwo hS.charTwo hB3 hTmax hT1
  have hT2 : IsPGroup 2 T := hTmax.1
  have hT3 : ¬ 3 ∣ Nat.card T := not_three_dvd_card_of_isPGroup_two hT2
  have hTM2 : T ≤ gammaOneThree B := le_gammaOneThree_of_normalized hS hB hTmax.2.1 hT3
  have hTN : T ≤ N := hTM2.trans hM2N
  have hTI : T ≤ Subgroup.normalizer (I : Set G) :=
    le_normalizer_component_of_input11_6 i116 hS hB hNtop hBN hTN hTmax.2.1 hT3 hI

  have hII : I ≤ N := hI.1
  have hB1 : B ≠ ⊥ := by
    intro h
    have h1 := card_eq_81 hS hB
    rw [h, Subgroup.card_bot] at h1
    omega
  have hFN : B ⊓ K ≤ N := inf_le_left.trans hBN
  have hFel : IsElemAbelian 3 (barX 3 N (B ⊓ K)) :=
    elemAbelian_barX Nat.prime_three hFN (isElemAbelian_mono hB3 inf_le_left)
  have hFcard : Nat.card (barX 3 N (B ⊓ K)) = 9 := by
    rw [card_barX_of_isPGroup Nat.prime_three hFN
      (isPGroup_of_isElemAbelian' (isElemAbelian_mono hB3 inf_le_left))]
    have := hf.fK.2.2
    norm_num at this
    exact this
  have hTb : IsPGroup 2 (barX 3 N T) := isPGroup_barX hT2
  have hTbK : barX 3 N T ≤ Subgroup.normalizer (barX 3 N K : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) := by
    have := barX_le_normalizer (p := 3) (C := N) hTI
    rwa [hbar] at this
  have hBbT : barX 3 N B ≤
      Subgroup.normalizer (barX 3 N T : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) :=
    barX_le_normalizer hTmax.2.1
  have hFbK : barX 3 N (B ⊓ K) ≤ barX 3 N K := barX_mono 3 inf_le_right
  have hFbT : barX 3 N (B ⊓ K) ≤
      Subgroup.normalizer (barX 3 N T : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) :=
    (barX_mono 3 inf_le_left).trans hBbT
  have hcomm1 := commutator_le_inf_of_normalizes hFbT hTbK hFbK
  have hbot : ⁅barX 3 N (B ⊓ K), barX 3 N T⁆ = ⊥ :=
    eq_bot_of_two_group_normalized_by_nine_ambient hL34 hFbK (hcomm1.trans inf_le_left) hFel hFcard
      (hTb.to_le (hcomm1.trans inf_le_right))
      (le_normalizer_commutator Subgroup.le_normalizer hFbT)
  have hFT : ∀ f ∈ barX 3 N (B ⊓ K), ∀ t ∈ barX 3 N T, f * t = t * f := by
    intro f hfm t ht
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot hfm
    exact (Subgroup.mem_centralizer_iff.1 h1 t ht).symm
  obtain ⟨y, ⟨hyT, hyP⟩, hy1⟩ := exists_ne_one_mem_preCentralizer hB3 hBN hTN hTmax.2.1 hCT hB1
    hf.normalizes hKN hOKN hf.sup_eq hFT hTbK
  set S : Subgroup G := T ⊓ preCentralizer N K with hSdef
  have hS1 : S ≠ ⊥ := by
    intro h
    have : y ∈ S := ⟨hyT, hyP⟩
    rw [h] at this
    exact hy1 (Subgroup.mem_bot.1 this)
  have hS2 : IsPGroup 2 S := hT2.to_le inf_le_left
  have hBS : B ≤ Subgroup.normalizer (S : Set G) := fun b hb =>
    Sec7.inf_normalizer_le_normalizer_inf T (preCentralizer N K)
      ⟨hTmax.2.1 hb, le_normalizer_preCentralizer hBN hf.normalizes hb⟩
  have hSI : S ≤ Subgroup.normalizer (I : Set G) := inf_le_left.trans hTI
  set O := GLAPPrimeCoreOf 3 N with hOdef
  set W := I ⊓ O with hWdef
  have hNO : N ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf 3 N
  have hSW : S ≤ Subgroup.normalizer (W : Set G) := fun s hs =>
    Sec7.inf_normalizer_le_normalizer_inf I O
      ⟨hSI hs, hNO ((inf_le_left.trans hTN) hs)⟩
  have hWI : W ≤ I := inf_le_left
  have hWO : W ≤ O := inf_le_right
  have hH1I : S ⊔ W ≤ Subgroup.normalizer (I : Set G) :=
    sup_le hSI (hWI.trans Subgroup.le_normalizer)
  have hBH1 : B ≤ Subgroup.normalizer ((S ⊔ W : Subgroup G) : Set G) := by
    intro b hb
    have hbW : b ∈ Subgroup.normalizer (W : Set G) :=
      Sec7.inf_normalizer_le_normalizer_inf I O ⟨hBI hb, hNO (hBN hb)⟩
    exact Subgroup.inf_normalizer_le_normalizer_sup S W ⟨hBS hb, hbW⟩
  have hW3 : ¬ 3 ∣ Nat.card W := fun h =>
    not_dvd_card_glaPPrimeCoreOf Nat.prime_three N (h.trans (Subgroup.card_dvd_of_le hWO))
  have hH1_3 : ¬ 3 ∣ Nat.card (S ⊔ W : Subgroup G) :=
    not_dvd_card_sup_of_coprime hSW (not_three_dvd_card_of_isPGroup_two hS2) hW3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS'2, hS'H1, hS'max, hBS'⟩ :=
    Proving.exists_normalized_sylow_of_coprime (Y := S ⊔ W) (p := 3) (q := 2)
      (isPGroup_of_isElemAbelian' hB3) hBH1 hH1_3
  have hS'1 : S' ≠ ⊥ := by
    intro h
    have := hS'max S (h ▸ bot_le) le_sup_left hS2
    exact hS1 (this.trans h)
  have hH1P : S ⊔ W ≤ preCentralizer N K :=
    sup_le inf_le_right (hWO.trans (glaPPrimeCoreOf_le_preCentralizer N K))
  have hcomm : ∀ s ∈ S', ∀ g ∈ I, s * g * s⁻¹ * g⁻¹ ∈ W := by
    intro s hs g hg
    have hsH := hS'H1 hs
    refine ⟨?_, commutator_mem_of_mem_preCentralizer hII (le_of_eq hbar) (hH1P hsH) hg⟩
    exact I.mul_mem ((Subgroup.mem_normalizer_iff.1 (hH1I hsH) g).1 hg) (I.inv_mem hg)
  have hS'W : S' ≤ Subgroup.normalizer (W : Set G) := fun s hs =>
    (sup_le hSW (Subgroup.le_normalizer : W ≤ Subgroup.normalizer (W : Set G))) (hS'H1 hs)
  have hmaxS' : ∀ Q : Subgroup G, IsPGroup 2 Q → S' ≤ Q → Q ≤ S' ⊔ W → Q = S' :=
    fun Q h2 h1 h3 => hS'max Q h1 (h3.trans (sup_le hS'H1 le_sup_right)) h2
  have hfrat := frattini_two hS'2 hmaxS' hS'W hWI hcomm
  set IN : Subgroup G := I ⊓ Subgroup.normalizer (S' : Set G) with hINdef
  have hINN : IN ≤ N := inf_le_left.trans hII
  have hbarIN : barX 3 N I ≤ barX 3 N IN := by
    refine barX_le_of_forall hINN fun g hg => ?_
    obtain ⟨j, hj, w, hw, rfl⟩ := hfrat g hg
    exact ⟨j, hj, by simpa using hWO hw⟩
  have hbarIN' : barX 3 N IN = barX 3 N K :=
    le_antisymm (hbar ▸ barX_mono 3 inf_le_left) (hbar ▸ hbarIN)
  set I0 : Subgroup G := Subgroup.closure {g : G | g ∈ IN ∧ IsPGroup 3 (Subgroup.zpowers g)}
    with hI0def
  have hI0IN : I0 ≤ IN := (Subgroup.closure_le IN).2 fun g hg => hg.1
  have hI0I : I0 ≤ I := hI0IN.trans inf_le_left
  have hbarI0 : barX 3 N I0 = barX 3 N K := by
    have h := barX_closure_three_eq (N := N) (Y := IN) hINN (by rw [hbarIN']; exact hsimp)
      (by rw [hbarIN', hcard]; norm_num)
    exact h.trans hbarIN'
  have hgen : I0 = Subgroup.closure {c : G | c ∈ I0 ∧ IsPGroup 3 (Subgroup.zpowers c)} :=
    le_antisymm (Subgroup.closure_mono fun g hg => ⟨Subgroup.subset_closure hg, hg.2⟩)
      ((Subgroup.closure_le I0).2 fun c hc => hc.1)
  have hloc : IsTwoLocal (Subgroup.normalizer (S' : Set G)) := ⟨S', hS'1, hS'2, rfl⟩
  have hCH := hS.charTwo _ hloc
  set P2 := pCoreOf 2 (Subgroup.normalizer (S' : Set G)) with hP2def
  have hI0H : I0 ≤ Subgroup.normalizer (S' : Set G) := hI0IN.trans inf_le_right
  have hBH : B ≤ Subgroup.normalizer (S' : Set G) := hBS'
  have hP2 : IsPGroup 2 P2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hHP : Subgroup.normalizer (S' : Set G) ≤ Subgroup.normalizer (P2 : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  set R : Subgroup G := ⁅P2, I0⁆ with hRdef
  have hI0P : I0 ≤ Subgroup.normalizer (P2 : Set G) := hI0H.trans hHP
  have hRP : R ≤ P2 := commutator_le_left hI0P
  have hR2 : IsPGroup 2 R := hP2.to_le hRP
  have hR1 : R ≠ ⊥ := by
    intro hR
    have hc : I0 ≤ Subgroup.centralizer (P2 : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hR
    have h1 : I0 ≤ P2 := fun g hg => hCH ⟨hI0H hg, hc hg⟩
    have := isPGroup_barX (p := 3) (N := N) (hP2.to_le h1)
    rw [hbarI0] at this
    exact hnot2 this
  have hRR : ⁅R, I0⁆ = R :=
    commutator_commutator_eq (not_three_dvd_card_of_isPGroup_two hP2) hI0P hgen
  have hBI0 : B ≤ Subgroup.normalizer (I0 : Set G) :=
    le_normalizer_closure_three (fun b hb =>
      Sec7.inf_normalizer_le_normalizer_inf I (Subgroup.normalizer (S' : Set G))
        ⟨hBI hb, Subgroup.le_normalizer (hBS' hb)⟩)
  have hP2M2 : P2 ≤ gammaOneThree B :=
    le_gammaOneThree_of_normalized hS hB (hBH.trans hHP) (not_three_dvd_card_of_isPGroup_two hP2)
  have hP2N : P2 ≤ N := hP2M2.trans hM2N
  have hRN : R ≤ N := hRP.trans hP2N
  have hBR : B ≤ Subgroup.normalizer (R : Set G) :=
    le_normalizer_commutator (hBH.trans hHP) hBI0
  have hRI : R ≤ Subgroup.normalizer (I : Set G) :=
    le_normalizer_component_of_input11_6 i116 hS hB hNtop hBN hRN hBR
      (not_three_dvd_card_of_isPGroup_two hR2) hI
  have hRIsub : R ≤ I := by
    calc R = ⁅R, I0⁆ := hRR.symm
      _ ≤ I := by
        refine Subgroup.commutator_le.2 fun r hr g hg => ?_
        have h1 := (Subgroup.mem_normalizer_iff.1 (hRI hr) g).1 (hI0I hg)
        exact I.mul_mem h1 (I.inv_mem (hI0I hg))
  have hRbar : barX 3 N R = ⊥ := by
    have hI0R : I0 ≤ Subgroup.normalizer (R : Set G) :=
      le_normalizer_commutator hI0P Subgroup.le_normalizer
    have hnorm : barX 3 N I0 ≤
        Subgroup.normalizer (barX 3 N R : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) :=
      barX_le_normalizer hI0R
    rw [hbarI0] at hnorm
    have hRK : barX 3 N R ≤ barX 3 N K := hbar ▸ barX_mono 3 hRIsub
    have hn : ((barX 3 N R).subgroupOf (barX 3 N K)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hRK).2 hnorm
    rcases hsimp.eq_bot_or_eq_top_of_normal ((barX 3 N R).subgroupOf (barX 3 N K)) with h | h
    · exact (Subgroup.subgroupOf_eq_bot.1 h).eq_bot_of_le hRK
    · exfalso
      have hKR : barX 3 N K ≤ barX 3 N R := Subgroup.subgroupOf_eq_top.1 h
      exact hnot2 ((isPGroup_barX (p := 3) (N := N) hR2).to_le hKR)
  have hRO : R ≤ O := Sec7.le_glaPPrimeCoreOf_of_barX_eq_bot hRN hRbar
  have hRle : R ≤ ⁅I, GLAPPrimeCoreOf 3 N⁆ := by
    calc R = ⁅R, I0⁆ := hRR.symm
      _ ≤ ⁅O, I⁆ := Subgroup.commutator_mono hRO hI0I
      _ = ⁅I, O⁆ := Subgroup.commutator_comm _ _
  have h2dvd : 2 ∣ Nat.card R := by
    obtain ⟨k, hk⟩ := hR2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hR1 (Subgroup.eq_bot_of_card_eq R (by rw [hk]; rfl))
    rw [hk]
    exact dvd_pow_self 2 hk0
  exact even_iff_two_dvd.2 (h2dvd.trans (Subgroup.card_dvd_of_le hRle))

theorem lemma76_of_inputs (i116 : Input11_6) (i183 : Input18_3_4) (i25 : Input2_5)
    (i145 : Input14_5) (i252 : Input25_2) (hS : GLStanding G 4 3) {B : Subgroup G}
    (hB : IsBOneMax 3 B) (h68 : Prop68Out B) : Lemma76Stmt B :=
  lemma76_of_lemma75 i116 hS hB h68 (lemma75_of_inputs i183 i25 i145 i252 hS hB h68)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
