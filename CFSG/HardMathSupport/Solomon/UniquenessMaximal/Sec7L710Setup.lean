module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710Defs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710SetupA
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L76A
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L76B

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_card_of_isPGroup_two' {T : Subgroup G} (hT : IsPGroup 2 T) :
    ¬ 3 ∣ Nat.card T := by
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  rw [hk]
  intro h3
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem glaPPrimeCoreOf_le_normalizer_component {N I : Subgroup G} (hI : GLAPComponent 3 N I) :
    GLAPPrimeCoreOf 3 N ≤ Subgroup.normalizer (I : Set G) := by
  have hIP : I ≤ preimBarX 3 N I := le_preimBarX 3 hI.1
  have hP : preimBarX 3 N I ≤ Subgroup.normalizer (I : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIP).1 (glaPComponent_normal_preimBarX hI)
  intro o ho
  refine hP ?_
  obtain ⟨o', ho', rfl⟩ := ho
  refine ⟨o', ?_, rfl⟩
  have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) o' = 1 := (QuotientGroup.eq_one_iff o').2 ho'
  show QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) o' ∈ barX 3 N I
  rw [h1]
  exact one_mem _

theorem commutator_le_of_component {N I : Subgroup G} (hI : GLAPComponent 3 N I)
    (hgen : Subgroup.closure {x : G | x ∈ I ∧ ∃ n : ℕ, x ^ (3 ^ n) = 1} = I) :
    ⁅I, GLAPPrimeCoreOf 3 N⁆ ≤ ⁅I, GLAPPrimeCoreOf 3 I⁆ := by
  set O := GLAPPrimeCoreOf 3 N with hO
  have hJ : GLAPPrimeCoreOf 3 I = I ⊓ O :=
    (glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three hI.2.1).symm
  have hIO : I ≤ Subgroup.normalizer (O : Set G) :=
    hI.1.trans (le_normalizer_glaPPrimeCoreOf 3 N)
  have hOI : O ≤ Subgroup.normalizer (I : Set G) := glaPPrimeCoreOf_le_normalizer_component hI
  have hcomm : ⁅O, I⁆ ≤ I ⊓ O := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_inf_of_normalizes hIO hOI le_rfl
  have hgen' : I = Subgroup.closure {c : G | c ∈ I ∧ IsPGroup 3 (Subgroup.zpowers c)} := by
    have hset : {c : G | c ∈ I ∧ IsPGroup 3 (Subgroup.zpowers c)} =
        {x : G | x ∈ I ∧ ∃ n : ℕ, x ^ (3 ^ n) = 1} :=
      Set.ext fun x => and_congr_right fun _ => isPGroup_three_zpowers_iff
    rw [hset, hgen]
  have hcc : ⁅⁅O, I⁆, I⁆ = ⁅O, I⁆ :=
    commutator_commutator_eq (not_dvd_card_glaPPrimeCoreOf Nat.prime_three N) hIO hgen'
  rw [hJ, Subgroup.commutator_comm I O, ← hcc, Subgroup.commutator_comm I (I ⊓ O)]
  exact Subgroup.commutator_mono hcomm le_rfl

omit [Finite G] in
theorem preimBarX_eq_of_barX_eq {N I K : Subgroup G} (hbar : barX 3 N I = barX 3 N K) :
    preimBarX 3 N I = preimBarX 3 N K := by
  unfold preimBarX
  rw [hbar]

theorem setup710_exists (hS : GLStanding G 4 3) {B M₀ : Subgroup G} (hB : IsBOneMax 3 B)
    (h63 : Prop63Out B M₀) (h68 : Prop68Out B) (hU : UniqComp B) (h75 : Lemma75Stmt B)
    (h76 : Lemma76Stmt B) (i11 : Input11_6) (l23 : Lemma23) (i18 : Input18_10)
    {T K : Subgroup G} (hT : IsMaxBInvariantTwo B T) (hK : IsHSet B K) :
    ∃ I : Subgroup G, Setup710 B T I ∧ K ≤ I ∧ I ≤ K ⊔ GLAPPrimeCoreOf 3 I ∧
      yOf B T I ≠ ⊤ := by
  have _hl23 := l23
  have hB3 : IsElemAbelian 3 B := hB.1.1
  have hf := h68 K hK
  obtain ⟨-, hNtop⟩ := permutable_gammaOneThree hS hB h63 h68 hU hK
  set N : Subgroup G := K ⊔ gammaOneThree B with hNdef
  have hBM2 : B ≤ gammaOneThree B := le_gammaOneThree_self hS hB
  have hBN : B ≤ N := hBM2.trans le_sup_right
  have hKN : K ≤ N := le_sup_left
  have hT2 : IsPGroup 2 T := hT.1
  have hT3 : ¬ 3 ∣ Nat.card T := not_three_dvd_card_of_isPGroup_two' hT2
  have hTN : T ≤ N := (le_gammaOneThree_of_normalized hS hB hT.2.1 hT3).trans le_sup_right
  have hT1 : T ≠ ⊥ := by
    obtain ⟨U, hU1, hU2, hBU⟩ := hB.1.2.2
    intro h
    exact hU1 (by rw [hT.2.2 U hU2 hBU (h ▸ bot_le), h])
  obtain ⟨⟨x0, hx0B, hx01, hx0K⟩, -, -⟩ := id hK
  have hKK : GLAPComponent 3 K K := glaPComponent_of_le Nat.prime_three hx0K le_rfl hx0K.1
  have hlayer : GLAPLayer 3 K = K := le_antisymm (glaPLayer_le 3 K) (le_sSup hKK)
  have hcomp : IsComponentOf (barX 3 N K) ⊤ := by
    have := h75 K hK N hNtop hBN (le_sup_of_le_left (le_inf hKN le_rfl))
    rwa [inf_eq_left.2 hKN, hlayer] at this
  have hOKN : GLAPPrimeCoreOf 3 K ≤ GLAPPrimeCoreOf 3 N :=
    glaPPrimeCoreOf_le_of_barX_component Nat.prime_three hKN hcomp
  have hL34K : IsLThreeFour ↥(barX 3 N K) := isLThreeFour_barX hKN hOKN hf.lThreeFour
  obtain ⟨I, hI, hbar⟩ := exists_glaPComponent_barX_eq (p := 3) N hcomp
  have hIN : I ≤ N := hI.1
  have hINtop : I ≠ ⊤ := fun h => hNtop (top_le_iff.1 (h ▸ hIN))
  have hPeq := preimBarX_eq_of_barX_eq hbar
  have hKI : K ≤ I := by
    have hgenK := closure_three_eq_of_component hx0K hf.lThreeFour
    rw [← hgenK]
    refine (Subgroup.closure_le I).2 fun x hx => ?_
    obtain ⟨hxK, n, hn⟩ := hx
    refine mem_of_mem_preimBarX_of_three hI ?_ hn
    rw [hPeq]
    exact le_preimBarX 3 hKN hxK
  have hIK : I ≤ K ⊔ GLAPPrimeCoreOf 3 I := by
    intro i hi
    have hiP : i ∈ preimBarX 3 N K := hPeq ▸ le_preimBarX 3 hIN hi
    obtain ⟨k, hk, hko⟩ := exists_mul_of_mem_preimBarX 3 hiP
    have hkI : k ∈ I := hKI hk
    have hoI : k⁻¹ * i ∈ GLAPPrimeCoreOf 3 I := by
      rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three hI.2.1]
      exact ⟨I.mul_mem (I.inv_mem hkI) hi, hko⟩
    have : i = k * (k⁻¹ * i) := by simp
    rw [this]
    exact Subgroup.mul_mem_sup hk hoI
  have hlthree : IsLThreeFour (↥I ⧸ GLAPPrimeCore 3 ↥I) :=
    IsLThreeFour.of_mulEquiv
      (((quotEquivBarX Nat.prime_three hIN hI.2.1).trans (MulEquiv.subgroupCongr hbar)).symm)
      hL34K
  have hgen3 := closure_three_eq_of_component hI hlthree
  have hBI : B ≤ Subgroup.normalizer (I : Set G) :=
    le_normalizer_of_barX_eq hBN hKN hf.normalizes hI hbar
  have hTI : T ≤ Subgroup.normalizer (I : Set G) :=
    le_normalizer_component_of_input11_6 i11 hS hB hNtop hBN hTN hT.2.1 hT3 hI
  have hCT : B ⊓ Subgroup.centralizer (T : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_isMaxBInvariantTwo hS.charTwo hB3 hT hT1
  have hBI9 : Nat.card ↥(B ⊓ I) = 9 := by
    refine le_antisymm (card_le_nine_of_isLThreeFour hlthree inf_le_right
      (isPGroup_of_isElemAbelian' (isElemAbelian_mono hB3 inf_le_left))) ?_
    have h1 := Subgroup.card_le_of_le (inf_le_inf_left B hKI : B ⊓ K ≤ B ⊓ I)
    have h2 := hf.fK.2.2
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num] at h2
    omega
  have hc18 : ∀ Q : Subgroup G, Q ≤ ⁅I, GLAPPrimeCoreOf 3 I⁆ → IsPGroup 2 ↥Q →
      ¬ 2 ∣ Q.relIndex ⁅I, GLAPPrimeCoreOf 3 I⁆ →
        I ⊓ Subgroup.centralizer (Q : Set G) ≤ GLAPPrimeCoreOf 3 I := by
    intro Q hQV hQ2 hQidx
    have hev := h76 K hK N hNtop le_rfl I hI hbar
    have hdvd : 2 ∣ Nat.card ↥(⁅I, GLAPPrimeCoreOf 3 I⁆) :=
      (even_iff_two_dvd.1 hev).trans
        (Subgroup.card_dvd_of_le (commutator_le_of_component hI hgen3))
    have hIcomp : GLAPComponent 3 I I := glaPComponent_of_le Nat.prime_three hI le_rfl hIN
    exact (i18 G I (isKGroup_of_isKProper hS.kProper hINtop) 3 Nat.prime_three hIcomp 2
      Nat.prime_two Q hdvd hQV hQ2 hQidx).trans (oPrimeP_le_of_isLThreeFour hlthree)
  refine ⟨I, ⟨hB3, card_eq_81 hS hB, hT2, hT.2.1, hT.2.2, fun b hb hbt => ?_, hBI, hTI,
    glaPComponent_perfect hI, hgen3, hlthree,
    fun R hRI hR => card_le_nine_of_isLThreeFour hlthree hRI hR, hBI9, hc18⟩, hKI, hIK, ?_⟩
  · have : b ∈ B ⊓ Subgroup.centralizer (T : Set G) :=
      ⟨hb, Subgroup.mem_centralizer_iff.2 fun t ht => (hbt t ht).symm⟩
    rw [hCT] at this
    exact Subgroup.mem_bot.1 this
  · intro h
    exact hNtop (top_le_iff.1 (h ▸ sup_le (sup_le hIN hTN) hBN))

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710
