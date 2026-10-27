module

public import CFSG.CGT.PushingUpLit.T2K.SixC
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKBender
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightTypes
public import CFSG.Walter.W67.Section5.Lemma57
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974 odd_card_goldschmidtOddCore)
open CFSG.QuasithinUnique.Lin2
  (exists_fusionBenderBorel_of_fusionIsBenderGroup false_of_benderBorel)
open scoped commutatorElement MatrixGroups

theorem goldschmidtSimpleType_congr {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : goldschmidtSimpleType L') : goldschmidtSimpleType L := by
  unfold goldschmidtSimpleType at h ⊢
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ |
      ⟨p, f, hp, hodd, hf, h5, h8, ⟨e'⟩⟩ | ⟨k, hk, hcard⟩ | ⟨⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hodd, hf, h5, h8, ⟨e.trans e'⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨k, hk, (Nat.card_congr e.toEquiv).trans hcard⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans e'⟩))))

theorem center_bot_of_nonabelian_simple {B : Type*} [Group B] [IsSimpleGroup B]
    (hna : ∃ a b : B, a * b ≠ b * a) : Subgroup.center B = ⊥ := by
  obtain ⟨a, b, hab⟩ := hna
  rcases (Subgroup.center B).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    apply hab
    have hb : b ∈ Subgroup.center B := h ▸ Subgroup.mem_top b
    exact Subgroup.mem_center_iff.mp hb a

theorem quasisimple_of_nonabelian_simple {B : Type*} [Group B] [hs : IsSimpleGroup B]
    (hna : ∃ a b : B, a * b ≠ b * a) : CFSG.Open.IsQuasisimple B := by
  have hcen := center_bot_of_nonabelian_simple hna
  obtain ⟨a, b, hab⟩ := hna
  have hperf : commutator B = ⊤ := by
    rcases (Subgroup.commutator_normal (⊤ : Subgroup B) ⊤).eq_bot_or_eq_top with h | h
    · exfalso
      apply hab
      have h1 : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup B), ⊤⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    · rw [commutator_def]
      exact h
  have e : B ⧸ Subgroup.center B ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  exact ⟨hperf, e.isSimpleGroup_congr.mpr hs⟩

theorem nonabelian_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ a b : B, a * b ≠ b * a) : ∃ a b : A, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨e.symm a, e.symm b, fun h1 => hab ?_⟩
  apply e.symm.injective
  rw [map_mul, map_mul, h1]

theorem goldschmidtSimpleType_of_simple (hGold : Goldschmidt1974) {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) (S : Sylow 2 X) {A : Subgroup X}
    (hAS : A ≤ (S : Subgroup X)) (hAab : IsMulCommutative A)
    (hcl : ∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A)
    (hA1 : A ≠ ⊥) : goldschmidtSimpleType X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hc⟩ := hGold X S A hAS hAab hcl
  set M : Subgroup X := Subgroup.normalClosure (A : Set X) with hMdef
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hAM : A ≤ M := Subgroup.le_normalClosure
  have hMtop : M = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h0 | h0
    · exact absurd (le_bot_iff.1 (h0 ▸ hAM)) hA1
    · exact h0
  let eM : ↥M ≃* X := (MulEquiv.subgroupCongr hMtop).trans Subgroup.topEquiv
  have : IsSimpleGroup ↥M := eM.isSimpleGroup
  have hcardM : Nat.card ↥M = Nat.card X := Nat.card_congr eM.toEquiv
  have hO : goldschmidtOddCore ↥M = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (goldschmidtOddCore ↥M) with h0 | h0
    · exact h0
    · exfalso
      have hodd := odd_card_goldschmidtOddCore ↥M
      rw [h0, Subgroup.card_top, hcardM] at hodd
      have hAp : IsPGroup 2 ↥A := S.isPGroup'.to_le hAS
      have hne : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA1
      obtain ⟨m, hm, hcard⟩ := hAp.nontrivial_iff_card.mp hne
      have h2 : 2 ∣ Nat.card X :=
        (dvd_pow_self 2 hm.ne').trans (hcard ▸ Subgroup.card_subgroup_dvd_card A)
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  let eH : (↥M ⧸ goldschmidtOddCore ↥M) ≃* X :=
    ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans eM
  let eT : ↥(⊤ : Subgroup (↥M ⧸ goldschmidtOddCore ↥M)) ≃* X := Subgroup.topEquiv.trans eH
  have : IsSimpleGroup ↥(⊤ : Subgroup (↥M ⧸ goldschmidtOddCore ↥M)) := eT.isSimpleGroup
  have hnabT := nonabelian_of_mulEquiv eT hnab
  have hcomp : CFSG.Open.IsComponentOf (⊤ : Subgroup (↥M ⧸ goldschmidtOddCore ↥M)) ⊤ :=
    ⟨le_rfl, CFSG.Open.IsSubnormal.refl _, quasisimple_of_nonabelian_simple hnabT⟩
  have hty := hc ⊤ hcomp
  have hZ := center_bot_of_nonabelian_simple hnabT
  let eZ : (↥(⊤ : Subgroup (↥M ⧸ goldschmidtOddCore ↥M)) ⧸
      Subgroup.center ↥(⊤ : Subgroup (↥M ⧸ goldschmidtOddCore ↥M))) ≃* X :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eT
  exact goldschmidtSimpleType_congr eZ.symm hty

namespace NatBlock

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ}

theorem not_isSolvable (h : NatBlock L n) : ¬ Group.IsSolvable ↥L := by
  intro hL
  have hn : 2 ≤ n := h.two_le
  have hS : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    Group.isSolvable_of_surjective h.natData.φ_surj
  have hP : Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))))
  have hq : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine CFSG.Walter.W67.Sec57.not_isSolvable_psl2 (F := GaloisField 2 n) ?_ hP
  rw [GaloisField.card 2 n (by omega)]
  omega

end NatBlock

namespace T2Hyp

variable {G : Type} [Group G] [Finite G] {L M : Subgroup G} {n : ℕ}

theorem sixteen_dvd_card (h : T2Hyp G L M n) : 16 ∣ Nat.card G := by
  have hcard := h.natBlock.card_blockU
  have h1 : (2 ^ n) ^ 2 ∣ Nat.card ↥(blockU L) := ⟨_, hcard⟩
  have h2 : Nat.card ↥(blockU L) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
  have h3 : 16 ∣ (2 ^ n) ^ 2 := by
    have h4 : 4 ≤ n * 2 := by have := h.two_le; omega
    have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [h16, ← pow_mul]
    exact pow_dvd_pow 2 h4
  exact h3.trans (h1.trans h2)

theorem false_of_goldschmidtSimpleType (h : T2Hyp G L M n) (hG : goldschmidtSimpleType G) :
    False := by
  have h16 := h.sixteen_dvd_card
  obtain ⟨P, hP1, hP2, hMP⟩ := h.maxLocal.1
  have hLP : L ≤ Subgroup.normalizer (P : Set G) := hMP ▸ h.le
  have hLns := h.natBlock.not_isSolvable
  have hbender : fusionIsBenderGroup G → False := fun hB => by
    obtain ⟨q, k, hq⟩ := exists_fusionBenderBorel_of_fusionIsBenderGroup hB
    exact false_of_benderBorel hq hP1 hP2 hLP hLns
  unfold goldschmidtSimpleType at hG
  rcases hG with ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ |
      ⟨p, f, hp, hodd, hf, -, h8, ⟨e⟩⟩ | ⟨m, -, hcard⟩ | ⟨⟨e⟩⟩
  · exact hbender (Or.inl ⟨f, by omega, ⟨e⟩⟩)
  · exact hbender (Or.inr (Or.inr ⟨a, ha, ⟨e⟩⟩))
  · exact hbender (Or.inr (Or.inl ⟨f, hf, ⟨e⟩⟩))
  · have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) even_two
    obtain ⟨k, hk, hkeq⟩ :=
      CFSG.ComponentClassification.AschbacherTheorem3.FourEight.psl2_card_two_part h8
    have h1 := CFSG.Glauberman.Dickson.MaxUp.card_psl2_galoisField (p := p) (m := f) hp2
      (by omega)
    have hcardG : Nat.card G = 4 * k := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField p f)) = _
      rw [h1, mul_comm 2 f, pow_mul, hkeq]
    have hk2 := Nat.odd_iff.mp hk
    omega
  · obtain ⟨k, hk, hkeq⟩ :=
      CFSG.ComponentClassification.AschbacherTheorem3.FourEight.ordRee_two_part m
    have hk2 := Nat.odd_iff.mp hk
    rw [hcard, hkeq] at h16
    omega
  · rw [Nat.card_congr e.toEquiv,
      CFSG.ComponentClassification.AschbacherTheorem3.FourEight.card_goldschmidtJ1] at h16
    omega

end T2Hyp

theorem print64D1_of_goldschmidt (hGold : Goldschmidt1974) : Print64D1 := by
  intro G _ _ L M T n D hs hD hD1
  subst hD1
  by_contra hcon
  have h := hs.sec4.hyp
  have hQg : ∀ g : G, g ∉ M → (QOf L M).map (MulAut.conj g).toMonoidHom ⊓ M = ⊥ := by
    intro g hg
    by_contra hne
    refine hcon ⟨g, ?_, hg, bot_lt_iff_ne_bot.2 hne⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hx
    rw [hx, one_mul, mul_one]
  have hQab : IsElemAbelian 2 (QOf L M) := hs.Q_abelian
  have hQp : IsPGroup 2 ↥(QOf L M) := fun x => ⟨1, Subtype.ext (by simpa using hQab.2 x x.2)⟩
  have hQ1 : QOf L M ≠ ⊥ := bot_lt_iff_ne_bot.1 (hD.lt_Q hs)
  obtain ⟨S, hQS⟩ := hQp.exists_le_sylow
  have hSM : (S : Subgroup G) ≤ M := T2Hyp.two_le_M hs S.isPGroup' hQS
  have hAab : IsMulCommutative (QOf L M) :=
    ⟨⟨fun a b => Subtype.ext (isElemAbelian_comm' hQab a.2 b.2)⟩⟩
  have hcl : ∀ a ∈ QOf L M, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) →
      g⁻¹ * a * g ∈ QOf L M := by
    intro a ha g hg
    have hbM : g⁻¹ * a * g ∈ M := hSM hg
    by_cases hgM : g⁻¹ ∈ M
    · have hn : g⁻¹ ∈ Subgroup.normalizer ((QOf L M : Subgroup G) : Set G) := by
        rw [hs.N_Q]
        exact hgM
      have := (Subgroup.mem_normalizer_iff.1 hn a).1 ha
      simpa using this
    · have hmem : g⁻¹ * a * g ∈ (QOf L M).map (MulAut.conj g⁻¹).toMonoidHom ⊓ M :=
        ⟨⟨a, ha, by simp⟩, hbM⟩
      rw [hQg _ hgM, Subgroup.mem_bot] at hmem
      rw [hmem]
      exact Subgroup.one_mem _
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    obtain ⟨P, hP1, -, hMP⟩ := h.maxLocal.1
    have hMn : M.Normal := ⟨fun x hx g => by
      have e : g * x * g⁻¹ = x := by rw [hcomm g x, mul_assoc, mul_inv_cancel, mul_one]
      rw [e]
      exact hx⟩
    rcases h.simple.eq_bot_or_eq_top_of_normal M with h0 | h0
    · apply hP1
      have : P ≤ M := hMP ▸ Subgroup.le_normalizer
      exact le_bot_iff.1 (h0 ▸ this)
    · exact h.M_ne_top h0
  have := h.simple
  exact h.false_of_goldschmidtSimpleType
    (goldschmidtSimpleType_of_simple hGold hnab S hQS hAab hcl hQ1)

theorem print64_of_goldschmidt (hGold : Goldschmidt1974) : Print64 :=
  print64_of hGold (print64D1_of_goldschmidt hGold)

end CFSG.CGT.PushingUpLit.T2K
