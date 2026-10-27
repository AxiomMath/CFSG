module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveOverlap
public import CFSG.Walter.PSL2Facts.Even

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open scoped MatrixGroups

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace SectionSix

namespace Linear

variable {X : Type} [Group X]

theorem oTwoPrime_le (Q : Subgroup X) : AschbacherTheorem3.oTwoPrime Q ≤ Q := by
  rw [AschbacherTheorem3.oTwoPrime, Subgroup.closure_le]
  exact fun x hx => hx.1

theorem le_oTwoPrime {Q P : Subgroup X} (hPQ : P ≤ Q) (hP : IsPGroup 2 P) :
    P ≤ AschbacherTheorem3.oTwoPrime Q := by
  intro x hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  exact Subgroup.subset_closure ⟨hPQ hx, k, congrArg Subtype.val hk⟩

theorem oTwoPrime_normal [Finite X] (Q : Subgroup X) :
    Q ≤ Subgroup.normalizer (AschbacherTheorem3.oTwoPrime Q : Set X) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rw [AschbacherTheorem3.oTwoPrime, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, ⟨hxQ, k, hk⟩, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨Q.mul_mem (Q.mul_mem hq hxQ) (Q.inv_mem hq), k, ?_⟩
    change (q * x * q⁻¹) ^ 2 ^ k = 1
    rw [conj_pow, hk]
    group
  · rw [Subgroup.card_map_of_injective (MulAut.conj q).injective]

theorem oTwoPrime_eq_of_quasisimple [Finite X] {A : Subgroup X}
    (hAq : CFSG.Open.IsQuasisimple A) : AschbacherTheorem3.oTwoPrime A = A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := oTwoPrime_le A
  have hn : ((AschbacherTheorem3.oTwoPrime A).subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr (oTwoPrime_normal A)
  rcases Quasisimple.normal_le_center_or_eq_top hAq
    ((AschbacherTheorem3.oTwoPrime A).subgroupOf A) with hc | htop
  · exfalso
    obtain ⟨P, hP⟩ := exists_isSylowOf 2 A
    have hAne : A ≠ ⊥ := A.nontrivial_iff_ne_bot.mp (Quasisimple.nontrivial hAq)
    apply sylow_not_le_centralizer_of_perfect ⟨hAq.1⟩ hAne hP
    intro x hx
    have hxN : x ∈ AschbacherTheorem3.oTwoPrime A := le_oTwoPrime hP.le hP.isPGroup hx
    have hxc : (⟨x, hP.le hx⟩ : A) ∈ Subgroup.center A := hc hxN
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hxc) ⟨y, hy⟩)
  · apply le_antisymm hle
    intro x hx
    have : (⟨x, hx⟩ : A) ∈ (AschbacherTheorem3.oTwoPrime A).subgroupOf A :=
      htop ▸ Subgroup.mem_top _
    exact this

theorem psl_sylow_card [Finite X] {A P : Subgroup X} {n : ℕ} (hn : 2 ≤ n)
    (e : A ≃* PSL(2, GaloisField 2 n)) (hP : IsSylowOf 2 P A) : Nat.card P = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U⟩ := (inferInstance : Nonempty (Sylow 2 PSL(2, GaloisField 2 n)))
  obtain ⟨-, hUcard⟩ := CFSG.Walter.psl2_even_sylow_two hn U
  rw [hP.card_eq, Nat.card_congr e.toEquiv, ← hUcard, Sylow.card_eq_multiplicity]

theorem exists_sylow_image [Finite X] {A P : Subgroup X} {n : ℕ} (hn : 2 ≤ n)
    (e : A ≃* PSL(2, GaloisField 2 n)) (hP : IsSylowOf 2 P A) :
    ∃ U : Sylow 2 PSL(2, GaloisField 2 n),
      (U : Subgroup PSL(2, GaloisField 2 n)) = (P.subgroupOf A).map e.toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U⟩ := (inferInstance : Nonempty (Sylow 2 PSL(2, GaloisField 2 n)))
  obtain ⟨-, hUcard⟩ := CFSG.Walter.psl2_even_sylow_two hn U
  have hcard : Nat.card ((P.subgroupOf A).map e.toMonoidHom) =
      2 ^ (Nat.card PSL(2, GaloisField 2 n)).factorization 2 := by
    rw [Subgroup.card_map_of_injective e.injective, card_subgroupOf, inf_eq_left.mpr hP.le,
      psl_sylow_card hn e hP, ← hUcard, Sylow.card_eq_multiplicity]
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

theorem psl_sylow_structure [Finite X] {A P : Subgroup X} {n : ℕ} (hn : 2 ≤ n)
    (e : A ≃* PSL(2, GaloisField 2 n)) (hP : IsSylowOf 2 P A) :
    IsElemAbelian 2 P ∧
      (∀ p ∈ P, ∀ q ∈ P, p ≠ 1 → q ≠ 1 →
        ∃ y ∈ A ⊓ Subgroup.normalizer (P : Set X), y * p * y⁻¹ = q) ∧
      A ⊓ Subgroup.centralizer (P : Set X) ≤ P := by
  obtain ⟨U, hU⟩ := exists_sylow_image hn e hP
  obtain ⟨hUel, -⟩ := CFSG.Walter.psl2_even_sylow_two hn U
  have hPA := hP.le
  have hmem : ∀ x : A, (x : X) ∈ P ↔ e x ∈ (U : Subgroup PSL(2, GaloisField 2 n)) := by
    intro x
    rw [hU, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    rfl
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_, ?_⟩
  · have ha : e ⟨a, hPA a.2⟩ ∈ (U : Subgroup _) := (hmem ⟨a, hPA a.2⟩).mp a.2
    have hb : e ⟨b, hPA b.2⟩ ∈ (U : Subgroup _) := (hmem ⟨b, hPA b.2⟩).mp b.2
    have hcomm := congrArg Subtype.val (hUel.toIsMulCommutative.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
    change e ⟨a, _⟩ * e ⟨b, _⟩ = e ⟨b, _⟩ * e ⟨a, _⟩ at hcomm
    rw [← map_mul, ← map_mul] at hcomm
    have h := congrArg (fun z : A => (z : X)) (e.injective hcomm)
    exact Subtype.ext h
  · have hx' : e ⟨x, hPA hx⟩ ∈ (U : Subgroup _) := (hmem ⟨x, hPA hx⟩).mp hx
    have h2 := elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (A := (U : Subgroup PSL(2, GaloisField 2 n))) _ hx'
    rw [← map_pow] at h2
    have h3 : (⟨x, hPA hx⟩ : A) ^ 2 = 1 := e.injective (by rw [h2, map_one])
    exact congrArg Subtype.val h3
  · intro p hp q hq hp1 hq1
    have hpU := (hmem ⟨p, hPA hp⟩).mp hp
    have hqU := (hmem ⟨q, hPA hq⟩).mp hq
    have hpU1 : e ⟨p, hPA hp⟩ ≠ 1 := fun h => hp1 (congrArg Subtype.val (e.injective
      (h.trans (map_one e).symm)))
    have hqU1 : e ⟨q, hPA hq⟩ ≠ 1 := fun h => hq1 (congrArg Subtype.val (e.injective
      (h.trans (map_one e).symm)))
    obtain ⟨Dg, -, -, -, hsup, htrans⟩ := CFSG.Walter.psl2_even_normalizer_sylow_two hn U
    obtain ⟨d, hd, -⟩ := htrans _ hpU hpU1 _ hqU hqU1
    have hdN : (d : PSL(2, GaloisField 2 n)) ∈
        Subgroup.normalizer ((U : Subgroup PSL(2, GaloisField 2 n)) : Set _) :=
      hsup ▸ (le_sup_right : Dg ≤ _) d.2
    set y : A := e.symm d
    refine ⟨y, ⟨y.2, AschbacherToolkit.mem_normalizer_of_conj_le (V := P) (g := (y : X))
      (fun v hv => ?_)⟩, ?_⟩
    · have hvU := (hmem ⟨v, hPA hv⟩).mp hv
      have h1 : e (y * ⟨v, hPA hv⟩ * y⁻¹) ∈ (U : Subgroup _) := by
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
        exact (Subgroup.mem_normalizer_iff.mp hdN _).mp hvU
      exact (hmem (y * ⟨v, hPA hv⟩ * y⁻¹)).mpr h1
    · have h1 : e (y * ⟨p, hPA hp⟩ * y⁻¹) = e ⟨q, hPA hq⟩ := by
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
        exact hd
      exact congrArg Subtype.val (e.injective h1)
  · intro x hx
    obtain ⟨hxA, hxC⟩ := hx
    obtain ⟨⟨u, hu⟩, hu1⟩ := ((U : Subgroup PSL(2, GaloisField 2 n)).ne_bot_iff_exists_ne_one).mp
      (by
        intro hbot
        obtain ⟨-, hUcard⟩ := CFSG.Walter.psl2_even_sylow_two hn U
        rw [hbot, Subgroup.card_bot] at hUcard
        have : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
        omega)
    have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
    have hC := CFSG.Walter.psl2_even_centralizer_involution hn U hu hu1'
    set w : A := e.symm u
    have hwP : (w : X) ∈ P := (hmem w).mpr (by rw [MulEquiv.apply_symm_apply]; exact hu)
    have hxw : (x : X) * w = w * x := ((Subgroup.mem_centralizer_iff.mp hxC) w hwP).symm
    have hexw : e ⟨x, hxA⟩ ∈ Subgroup.centralizer ({u} : Set PSL(2, GaloisField 2 n)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : (⟨x, hxA⟩ : A) * w = w * ⟨x, hxA⟩ := Subtype.ext hxw
      have h2 := congrArg e h1
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2
    rw [hC] at hexw
    exact (hmem ⟨x, hxA⟩).mpr hexw

theorem le_normalizer_pCoreOf (p : ℕ) (K : Subgroup X) :
    K ≤ Subgroup.normalizer (pCoreOf p K : Set X) := by
  have hn := CFSG.LieType.BorelTits.pCore_normal (G := K) p
  have h := Subgroup.le_normalizer_map (f := K.subtype) (H := CFSG.Open.pCore p K)
  rw [Subgroup.normalizer_eq_top_iff.mpr hn, Subgroup.map_top, Subgroup.range_subtype] at h
  exact h

theorem decode_altThree [Finite X] {A T : Subgroup X} (hAq : CFSG.Open.IsQuasisimple A)
    (hTA : T ≤ Subgroup.normalizer (A : Set X)) (hT2 : IsPGroup 2 T)
    (hTAbot : T ⊓ A = ⊥) (hTC : T ⊓ Subgroup.centralizer (A : Set X) = ⊥)
    (h : Thm3AltThree A T) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (A ≃* PSL(2, GaloisField 2 n)) ∧ ∃ O P : Subgroup X,
      IsElemAbelian 2 O ∧ Nat.card O = 2 ^ n ∧ O ≤ Subgroup.centralizer (A : Set X) ∧
      O ⊓ A = ⊥ ∧ P = (O ⊔ T) ⊓ A ∧ IsSylowOf 2 P A ∧ Nat.card P = 2 ^ n ∧ T ≤ O ⊔ P ∧
      Nat.card T = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, h1, h2, h3, h4, h5, ⟨e⟩⟩ := h
  have hN := oTwoPrime_eq_of_quasisimple hAq
  rw [hN] at h1 h2 h3
  have e' : A ≃* PSL(2, GaloisField 2 n) := (MulEquiv.subgroupCongr hN.symm).trans e
  set O := pCoreOf 2 (A ⊔ T) with hOdef
  have hOn : A ⊔ T ≤ Subgroup.normalizer (O : Set X) := le_normalizer_pCoreOf 2 (A ⊔ T)
  have hOle : O ≤ A ⊔ T := Subgroup.map_subtype_le _
  have hOC : O ≤ Subgroup.centralizer (A : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  have hAO : A ≤ Subgroup.normalizer (O : Set X) := le_sup_left.trans hOn
  have hTN : T ≤ Subgroup.normalizer (O : Set X) := le_sup_right.trans hOn
  have hTOA : T ≤ O ⊔ A := (le_oTwoPrime (le_sup_right : T ≤ A ⊔ T) hT2).trans h1.le
  have hTO : O ⊓ T = ⊥ :=
    le_bot_iff.mp (by rw [inf_comm]; exact (inf_le_inf_left T hOC).trans hTC.le)
  have hTOcard : Nat.card (O ⊔ T : Subgroup X) = Nat.card O * Nat.card T :=
    AschbacherTheorem3.card_sup_of_le_normalizer hTN hTO
  set P := (O ⊔ T) ⊓ A with hPdef
  have hdec : O ⊔ T ≤ O ⊔ P := by
    intro x hx
    have hxOA : x ∈ ((O ⊔ A : Subgroup X) : Set X) := (sup_le le_sup_left hTOA) hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left O A hAO] at hxOA
    obtain ⟨o, ho, a, ha, rfl⟩ := Set.mem_mul.mp hxOA
    have haOT : a ∈ O ⊔ T := by
      have := (O ⊔ T).mul_mem ((O ⊔ T).inv_mem ((le_sup_left : O ≤ O ⊔ T) ho)) hx
      simpa using this
    exact Subgroup.mul_mem_sup ho ⟨haOT, ha⟩
  have hOTeq : O ⊔ T = O ⊔ P := le_antisymm hdec (sup_le le_sup_left inf_le_left)
  have hOPbot : O ⊓ P = ⊥ := le_bot_iff.mp ((inf_le_inf_left O inf_le_right).trans h2.le)
  have hOPcard : Nat.card (O ⊔ P : Subgroup X) = Nat.card O * Nat.card P :=
    AschbacherTheorem3.card_sup_of_le_normalizer (inf_le_right.trans hAO) hOPbot
  have hPT : Nat.card P = Nat.card T := by
    have h6 : Nat.card O * Nat.card P = Nat.card O * Nat.card T := by
      rw [← hOPcard, ← hTOcard, hOTeq]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h6
  have hOT : Nat.card O ≤ Nat.card T := by
    have hOAcard : Nat.card (O ⊔ A : Subgroup X) = Nat.card O * Nat.card A :=
      AschbacherTheorem3.card_sup_of_le_normalizer hAO h2
    have hATcard : Nat.card (A ⊔ T : Subgroup X) = Nat.card A * Nat.card T :=
      AschbacherTheorem3.card_sup_of_le_normalizer hTA (by rw [inf_comm]; exact hTAbot)
    have hle := Subgroup.card_le_of_le (sup_le hOle (le_sup_left : A ≤ A ⊔ T))
    rw [hOAcard, hATcard, mul_comm (Nat.card A)] at hle
    exact Nat.le_of_mul_le_mul_right hle Nat.card_pos
  have hOT2 : IsPGroup 2 (O ⊔ T : Subgroup X) :=
    IsPGroup.to_sup_of_normal_left' (IsPGroup.of_card h5) hT2 hTN
  have hP2 : IsPGroup 2 P := hOT2.to_le inf_le_left
  obtain ⟨PA, hPA⟩ := exists_isSylowOf 2 A
  have hPle : Nat.card P ≤ 2 ^ n :=
    (AschbacherTheorem3.card_le_of_isSylowOf hPA hP2 inf_le_right).trans
      (psl_sylow_card hn e' hPA).le
  have hT : Nat.card T = 2 ^ n := le_antisymm (hPT ▸ hPle) (h5 ▸ hOT)
  have hPsyl : IsSylowOf 2 P A :=
    isSylowOf_of_card inf_le_right (by rw [hPT, hT, ← psl_sylow_card hn e' hPA, hPA.card_eq])
  exact ⟨n, hn, ⟨e'⟩, O, P, h4, h5, hOC, h2, rfl, hPsyl, hPT.trans hT,
    le_sup_right.trans hOTeq.le, hT⟩

end Linear

end SectionSix

end CFSG.ComponentClassification.AschbacherTheorem5
