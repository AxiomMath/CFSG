module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Lin2S
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61Base
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245NaturalMain

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin Subgroup
open scoped commutatorElement

namespace C56

section Generic

variable {G : Type} [Group G]

theorem comm_of_mem_conjSubgroup {A : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (x : G) :
    ∀ a ∈ conjSubgroup A x, ∀ b ∈ conjSubgroup A x, a * b = b * a := by
  intro a ha b hb
  rw [mem_conjSubgroup_iff] at ha hb
  have := hA _ ha _ hb
  have h2 : x * (a * b) * x⁻¹ = x * (b * a) * x⁻¹ := by
    calc x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      _ = (x * b * x⁻¹) * (x * a * x⁻¹) := this
      _ = x * (b * a) * x⁻¹ := by group
  simpa using h2

variable [Finite G]

omit [Finite G] in
theorem rank1_W_le_inf {B Q U W : Subgroup G} {q : ℕ} (h : C5.Rank1 B Q U W q) {x : G}
    (hx : x ∈ normalizer (B : Set G)) (hx1 : ¬ conjSubgroup U x ≤ Q) :
    W ≤ Q ⊓ conjSubgroup Q x := by
  intro w hw
  have h1 : w ∈ U ⊓ centralizer ((conjSubgroup U x : Subgroup G) : Set G) := by
    rw [h.inf_centralizer_conj hx hx1]
    exact hw
  refine ⟨h.U_le_Q (h.W_le_U hw), ?_⟩
  rw [h.conj_Q_eq hx]
  exact ⟨h.U_le_B h1.1, h1.2⟩

theorem invol_mem_inf_conj {B Q U W : Subgroup G} {q : ℕ} (h : C5.Rank1 B Q U W q) {x : G}
    (hx : x ∈ normalizer (B : Set G)) (hxx : x * x = 1) (hx1 : ¬ conjSubgroup U x ≤ Q)
    (hQ : C5.ElemAb2 Q) {t : G} (htB : t ∈ B) (ht2 : t * t = 1) (htx : x * t = t * x) :
    t ∈ Q ⊓ conjSubgroup Q x := by
  have hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q := by
    rw [inv_eq_of_mul_eq_one_right hxx]
    exact hx1
  have hBeq : conjSubgroup U x ⊔ Q = B := h.sup_Q_conj hx hx2
  obtain ⟨-, hNU⟩ := h.relIndex_inf_conj hx hx1
  have hUxB : conjSubgroup U x ≤ B := h.conj_le_B hx
  have hUxN : conjSubgroup U x ≤ normalizer (Q : Set G) := hUxB.trans h.B_le_normQ
  have hUN : U ≤ normalizer ((Q ⊓ conjSubgroup Q x : Subgroup G) : Set G) := fun g hg =>
    C5.mem_normalizer_inf (h.B_le_normQ (h.U_le_B hg)) (h.B_le_normQ_conj hx (h.U_le_B hg))
  have hWN := rank1_W_le_inf h hx hx1
  have hxt : x * t * x⁻¹ = t := by rw [htx]; group
  have hQ2 : ∀ c ∈ Q, c * c = 1 := fun c hc => by
    have := hQ.2 c hc
    rwa [pow_two] at this
  suffices htQ : t ∈ Q from
    ⟨htQ, mem_conjSubgroup_iff.mpr (by rw [hxt]; exact htQ)⟩
  obtain ⟨v, hv, c, hc, rfl⟩ := C5.mem_sup_of_le_normalizer hUxN
    (show t ∈ conjSubgroup U x ⊔ Q by rw [hBeq]; exact htB)
  have hvQx : v ∈ conjSubgroup Q x := C5.conjSubgroup_mono h.U_le_Q x hv
  have hv2 : v * v = 1 := by
    have hv' := (mem_conjSubgroup_iff).mp hv
    have h1 := hQ2 _ (h.U_le_Q hv')
    calc v * v = x⁻¹ * (x * v * x⁻¹ * (x * v * x⁻¹)) * x := by group
      _ = 1 := by rw [h1]; group
  have hcv : c * v = v * c := by
    have h1 : (v * c)⁻¹ = v * c := inv_eq_of_mul_eq_one_right ht2
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hQ2 c hc),
      inv_eq_of_mul_eq_one_right hv2] at h1
    exact h1
  obtain ⟨u, hu, n, hn, hcun⟩ : ∃ u ∈ U, ∃ n ∈ Q ⊓ conjSubgroup Q x, c = u * n :=
    C5.mem_sup_of_le_normalizer hUN (show c ∈ U ⊔ (Q ⊓ conjSubgroup Q x) by rw [hNU]; exact hc)
  have hnv : n * v = v * n :=
    comm_of_mem_conjSubgroup hQ.1 x n hn.2 v hvQx
  have huv : u * v = v * u := by
    have h1 : Commute (u * n) v := by rw [← hcun]; exact hcv
    have h2 : Commute n⁻¹ v := (show Commute n v from hnv).inv_left
    have h3 : Commute (u * n * n⁻¹) v := h1.mul_left h2
    rw [mul_inv_cancel_right] at h3
    exact h3
  by_cases hvQ : v ∈ Q
  · exact mul_mem hvQ hc
  · have hvB : v ∈ B := hUxB hv
    have huW : u ∈ W := (h.cent_y v hvB hvQ u hu).mpr huv
    have hcN : c ∈ Q ⊓ conjSubgroup Q x := by
      rw [hcun]
      exact mul_mem (hWN huW) hn
    have htQx : v * c ∈ conjSubgroup Q x := mul_mem hvQx hcN.2
    have := (mem_conjSubgroup_iff).mp htQx
    rwa [hxt] at this

end Generic

section Normalizer

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_not_mem_of_lt {P K : Subgroup G} (hP : IsPGroup 2 P) (hKP : K < P) :
    ∃ y ∈ P, y ∈ Subgroup.normalizer (K : Set G) ∧ y ∉ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let KP : Subgroup P := K.subgroupOf P
  have hne : KP ≠ ⊤ := by
    intro htop
    obtain ⟨z, hzP, hzK⟩ := IsConcreteLE.exists_of_lt hKP
    have : (⟨z, hzP⟩ : P) ∈ KP := by rw [htop]; trivial
    exact hzK (Subgroup.mem_subgroupOf.mp this)
  have hlt : KP < ⊤ := lt_top_iff_ne_top.2 hne
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnc : NormalizerCondition P := Group.normalizerCondition_of_isNilpotent (G := P)
  have hlt' : KP < Subgroup.normalizer (KP : Set P) := hnc KP hlt
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt hlt'
  refine ⟨x, x.2, ?_, fun h => hxnot (Subgroup.mem_subgroupOf.mpr h)⟩
  have hxsub : x ∈ (Subgroup.normalizer (K : Set G)).subgroupOf P := by
    rw [Subgroup.subgroupOf_normalizer_eq (show K ≤ P from hKP.le)]
    exact hxN
  exact Subgroup.mem_subgroupOf.mp hxsub

omit [Finite G] in
theorem lin2_not_alt {L : Subgroup G} {n : ℕ} (hn : 1 < n) (hlin : IsLin2Type L n) :
    ¬ IsAltType L 3 := by
  rintro ⟨α', hα's, hα'k, -⟩
  obtain ⟨F, hFfield, hFfin, hcard, α, hαs, hαk, -⟩ := hlin
  have hk : α.ker = α'.ker := hαk.trans hα'k.symm
  have e1 := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv
  have e2 := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α' hα's).toEquiv
  rw [hk] at e1
  have h3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Fintype.card_fin, Nat.factorial]
  have hFq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
  have h4 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFq]
  have h5 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h6 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 3 := by
    rw [← e1, e2, h3]
  rw [h4] at h6
  have h7 : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
  have h8 : 15 ≤ (2 ^ n) ^ 2 - 1 := by omega
  nlinarith

end Normalizer

section Main

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem lin2_rank1 (hN : NaturalModuleStructure)
    (hcs : ConstrainedSetting G T M H S L) (hj : conjJoin S L = L) {n : ℕ} (hn : 1 < n)
    (hlin : IsLin2Type L n) {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T)
    (h2 : S.relIndex M₀ = 2) :
    ∃ (q : ℕ) (W : Subgroup G), q = 2 ^ n ∧
      C5.Rank1 (baum S) (baum S ⊓ centralizer (blockU L : Set G)) (blockU L) W q ∧
      (∀ x ∈ M₀, x ∉ S →
        SingleRank1Concl S H L (baum S ⊓ centralizer (blockU L : Set G)) q x) := by
  obtain ⟨q, W, hq2, hidxQ, hidxW, hZ, hcent, hcomm, hmain, -⟩ :=
    single_rank1 hN hcs hj (Or.inl ⟨n, hn, hlin⟩) hSM hMT h2
  have hq : q = 2 ^ n := by
    have h1 := relIndex_blockZ_isLin2Type (G := G) (L := L) hlin
    exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hZ.symm.trans h1 :
      (fun m : ℕ => m ^ 2) q = (fun m : ℕ => m ^ 2) (2 ^ n))
  have hLsh := isShort hcs
  have hBS : baum S ≤ S := inf_le_left
  have hBU : baum S ≤ normalizer (blockU L : Set G) := hBS.trans (S_le_normalizer_blockU hj)
  have hne : S ≠ M₀ := by
    intro h
    rw [← h] at h2
    simp at h2
  obtain ⟨x₀, hx₀, hx₀S⟩ : ∃ x ∈ M₀, x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hSM hcon)
  obtain ⟨-, -, -, -, o5, -, -, -, -, -, -, -⟩ := hmain x₀ hx₀ hx₀S
  have hWU : W ≤ blockU L := by
    rw [← hcomm, Subgroup.commutator_le]
    intro u hu b hb
    have h1 : b * u⁻¹ * b⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (hBU hb) _).mp (inv_mem hu)
    have := mul_mem hu h1
    rw [commutatorElement_def]
    simpa [mul_assoc] using this
  refine ⟨q, W, hq, ?_, hmain⟩
  exact
    { U_le_Q := by rw [← o5]; exact blockU_le_pCoreOf hcs hj
      Q_le_B := inf_le_left
      B_le_normQ := fun _ hb => C5.mem_normalizer_inf (Subgroup.le_normalizer hb)
        (C5.mem_normalizer_centralizer (hBU hb))
      B_le_normU := hBU
      Q_eq := rfl
      W_le_U := hWU
      idx_Q := hidxQ
      idx_W := hidxW
      q_ne_zero := by omega
      cent_y := hcent
      comm_UB := hcomm
      U_comm := (C1.elemAb2_blockU hLsh).1 }

theorem lin2_star
    (hcs : ConstrainedSetting G T M H S L) (hj : conjJoin S L = L) {n : ℕ} (hn : 1 < n)
    (hlin : IsLin2Type L n) {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T)
    (h2 : S.relIndex M₀ = 2) {A : Subgroup G} (hAM : A ≤ M₀) (hA : IsElemAbelian 2 A)
    (hQA : Nat.card (pCoreOf 2 H) ≤ Nat.card A) : A ≤ S := by
  by_contra hAS
  obtain ⟨x, hxA, hxS⟩ := IsConcreteLE.not_le_iff_exists.mp hAS
  have hLsh := isShort hcs
  have hxM : x ∈ M₀ := hAM hxA
  have hA' := C5.isElemAbelian_two_iff.mp hA
  have hsq : ∀ e ∈ A, e * e = 1 := fun e he => by
    have := hA'.2 e he
    rwa [pow_two] at this
  have hxx : x * x = 1 := hsq x hxA
  obtain ⟨q, W, hq, hR1, hmain⟩ := lin2_rank1 naturalModuleStructure hcs hj hn hlin hSM hMT h2
  obtain ⟨o1, -, -, -, o5, o6, -, -, -, -, -, -⟩ := hmain x hxM hxS
  have hSL := S_le_normalizer hj
  have hS2 := isPGroup_S hcs
  set B := baum S with hBdef
  set U := blockU L with hUdef
  set Q := B ⊓ centralizer (U : Set G) with hQdef
  have hBS : B ≤ S := inf_le_left
  have hxB : x ∈ normalizer (B : Set G) :=
    normalizer_le_normalizer_baum S (normalizer_of_relIndex_two hSM h2 hxM)
  have hx1 : ¬ conjSubgroup U x ≤ Q := by
    rw [← o5]
    exact not_conj_le_of_mem_diff hcs hSM hMT h2 hxM hxS
  obtain ⟨hBN, hBsyl⟩ := baumann_single hcs.minParabolic hcs.block (Or.inl ⟨n, hn, hlin⟩)
    hcs.thompson (H_eq hcs hj) (S_le_normalizer hj)
  have hLX : L ≤ L ⊔ B := le_sup_left
  have hXN : L ⊔ B ≤ normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBN
  have hTsyl : IsSylowTwoOf (B ⊓ L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hBsyl hLX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLX).mpr hXN).isSubnormal
  have hTS : B ⊓ L ≤ S := inf_le_left.trans hBS
  have hTn : ∀ s ∈ S, ∀ t ∈ B ⊓ L, s * t * s⁻¹ ∈ B ⊓ L := by
    intro s hs t ht
    have hsB : s ∈ normalizer (B : Set G) :=
      normalizer_le_normalizer_baum S (Subgroup.le_normalizer hs)
    exact ⟨(Subgroup.mem_normalizer_iff.mp hsB t).mp ht.1,
      (Subgroup.mem_normalizer_iff.mp (hSL hs) t).mp ht.2⟩
  obtain ⟨hG1, hG2⟩ := lin2_S_facts hLsh (by omega) hlin hTsyl hS2 hSL hTS hTn
  have hKB : (B ⊓ L) ⊔ (S ⊓ centralizer (U : Set G)) ≤ B := by
    refine sup_le inf_le_left ?_
    intro g hg
    have : g ∈ H ⊓ centralizer (U : Set G) := ⟨hcs.sylow.le hg.1, hg.2⟩
    rw [inf_centralizer_eq hcs hj, o5] at this
    exact this.1
  have hG1' : ∀ E : Subgroup G, E ≤ S → (∀ e ∈ E, e * e = 1) →
      Nat.card E ≤ 2 * Nat.card ↥(E ⊓ B) := fun E hES hE2 =>
    (hG1 E hES hE2).trans
      (Nat.mul_le_mul_left 2 (Subgroup.card_le_of_le (inf_le_inf_left E hKB)))
  have hG2' : ∀ s ∈ S, (∀ w ∈ W, s * w = w * s) → s ∈ B := by
    intro s hs hsW
    refine hKB (hG2 s hs fun w hw => hsW w ?_)
    rw [← hR1.comm_UB]
    exact Subgroup.commutator_mono le_rfl inf_le_left hw
  set N := Q ⊓ conjSubgroup Q x with hNdef
  have hQcard : Nat.card Q = Nat.card N * q := by
    have := C5.card_eq_card_mul_relIndex (inf_le_left : N ≤ Q)
    rwa [o1] at this
  have hq4 : 4 ≤ q := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hνpos : 0 < Nat.card N := Nat.card_pos
  have hQA' : Nat.card Q ≤ Nat.card A := by rwa [o5] at hQA
  have hAE : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ S) := by
    have h1 := C5.card_eq_card_mul_relIndex (inf_le_left : A ⊓ S ≤ A)
    have h2' : (A ⊓ S).relIndex A ≤ 2 := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
      calc S.relIndex A ≤ S.relIndex M₀ :=
            Subgroup.relIndex_le_of_le_right hAM (by rw [h2]; norm_num)
        _ = 2 := h2
    rw [h1]
    calc Nat.card ↥(A ⊓ S) * (A ⊓ S).relIndex A ≤ Nat.card ↥(A ⊓ S) * 2 :=
          Nat.mul_le_mul_left _ h2'
      _ = 2 * Nat.card ↥(A ⊓ S) := mul_comm _ _
  have hEE : Nat.card ↥(A ⊓ S) ≤ 2 * Nat.card ↥((A ⊓ S) ⊓ B) :=
    hG1' (A ⊓ S) inf_le_right fun e he => hsq e he.1
  have hE0N : (A ⊓ S) ⊓ B ≤ N := by
    intro t ht
    have htA : t ∈ A := ht.1.1
    exact invol_mem_inf_conj hR1 hxB hxx hx1 o6 ht.2 (hsq t htA) (hA'.1 x hxA t htA)
  have hE0 : Nat.card ↥((A ⊓ S) ⊓ B) ≤ Nat.card N := Subgroup.card_le_of_le hE0N
  have hlow : Nat.card N * q ≤ 4 * Nat.card N := by
    calc Nat.card N * q = Nat.card Q := hQcard.symm
      _ ≤ Nat.card A := hQA'
      _ ≤ 2 * Nat.card ↥(A ⊓ S) := hAE
      _ ≤ 2 * (2 * Nat.card ↥((A ⊓ S) ⊓ B)) := Nat.mul_le_mul_left 2 hEE
      _ ≤ 2 * (2 * Nat.card N) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 hE0)
      _ = 4 * Nat.card N := by ring
  have hq_le : q ≤ 4 := by
    by_contra hlt
    push Not at hlt
    nlinarith
  have hq4' : q = 4 := le_antisymm hq_le hq4
  rw [hq4'] at hQcard
  have heq1 : Nat.card ↥((A ⊓ S) ⊓ B) = Nat.card N := by omega
  have heq2 : Nat.card ↥(A ⊓ S) = 2 * Nat.card ↥((A ⊓ S) ⊓ B) := by omega
  have hEN : (A ⊓ S) ⊓ B = N :=
    Subgroup.eq_of_le_of_card_ge hE0N (by rw [heq1])
  have hex : ∃ t ∈ A ⊓ S, t ∉ B := by
    by_contra hcon
    push Not at hcon
    have hEB : A ⊓ S ≤ (A ⊓ S) ⊓ B := fun t ht => ⟨ht, hcon t ht⟩
    have := Subgroup.card_le_of_le hEB
    have hpos : 0 < Nat.card ↥((A ⊓ S) ⊓ B) := Nat.card_pos
    omega
  obtain ⟨t, htE, htB⟩ := hex
  have hNE : N ≤ A ⊓ S := by
    rw [← hEN]
    exact inf_le_left
  apply htB
  refine hG2' t htE.2 fun w hw => ?_
  have hwN : w ∈ N := rank1_W_le_inf hR1 hxB hx1 hw
  exact hA'.1 t htE.1 w (hNE hwN).1

theorem lin2_isMaxElemAbelian_iff
    (hcs : ConstrainedSetting G T M H S L) (hj : conjJoin S L = L) {n : ℕ} (hn : 1 < n)
    (hlin : IsLin2Type L n) {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T)
    (h2 : S.relIndex M₀ = 2) (A : Subgroup G) :
    IsMaxElemAbelian M₀ A ↔ IsMaxElemAbelian S A := by
  have hne : S ≠ M₀ := by
    intro h
    rw [← h] at h2
    simp at h2
  obtain ⟨x₀, hx₀, hx₀S⟩ : ∃ x ∈ M₀, x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hSM hcon)
  obtain ⟨q, W, hq, hR1, hmain⟩ := lin2_rank1 naturalModuleStructure hcs hj hn hlin hSM hMT h2
  obtain ⟨-, -, -, -, o5, -, o7, -, -, -, -, -⟩ := hmain x₀ hx₀ hx₀S
  have hQS : IsMaxElemAbelian S (pCoreOf 2 H) := by rw [o5]; exact o7
  constructor
  · rintro ⟨hAM, hAe, hmax⟩
    have hQA : Nat.card (pCoreOf 2 H) ≤ Nat.card A :=
      hmax _ (hQS.1.trans hSM) hQS.2.1
    have hAS : A ≤ S := lin2_star hcs hj hn hlin hSM hMT h2 hAM hAe hQA
    exact ⟨hAS, hAe, fun B hBS hBe => hmax B (hBS.trans hSM) hBe⟩
  · rintro ⟨hAS, hAe, hmax⟩
    refine ⟨hAS.trans hSM, hAe, fun B hBM hBe => ?_⟩
    by_contra hlt
    push Not at hlt
    have hQA : Nat.card (pCoreOf 2 H) ≤ Nat.card A := hmax _ hQS.1 hQS.2.1
    have hBS : B ≤ S :=
      lin2_star hcs hj hn hlin hSM hMT h2 hBM hBe (hQA.trans hlt.le)
    exact absurd (hmax B hBS hBe) (not_le.mpr hlt)

theorem normalizer_le_of_isMaxElemAbelian (hcs : ConstrainedSetting G T M H S L) {M₀ : Subgroup G}
    (hSM : S ≤ M₀) (hMT : M₀ ≤ T) {x : G} (hx : x ∈ M₀)
    (hA : ∀ A : Subgroup G, IsMaxElemAbelian M₀ A ↔
      A = pCoreOf 2 H ∨ A = conjR (pCoreOf 2 H) x) :
    T ⊓ normalizer (M₀ : Set G) ≤ M₀ := by
  have hHP : H ≤ normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have h244 : ∀ y, y ∈ T → y ∈ normalizer (pCoreOf 2 H : Set G) → y ∈ S := fun y hyT hyN => by
    have e := lemma244 G T M H S L hcs (pCoreOf 2 H) (pCoreOf_ne_bot hcs) (pCoreOf_le_S hcs) hHP
    have : y ∈ T ⊓ normalizer (pCoreOf 2 H : Set G) := ⟨hyT, hyN⟩
    rwa [e] at this
  intro σ hσ
  have hσT : σ ∈ T := hσ.1
  have hσN : σ ∈ normalizer (M₀ : Set G) := hσ.2
  have hP : IsMaxElemAbelian M₀ (pCoreOf 2 H) := (hA _).mpr (Or.inl rfl)
  have hP' := isMaxElemAbelian_conjSubgroup hP hσN
  rcases (hA _).mp hP' with h | h
  · exact hSM (h244 σ hσT (conjSubgroup_eq_iff_mem_normalizer.mp h))
  · rw [conjR_eq] at h
    have h' : conjSubgroup (pCoreOf 2 H) (σ * x⁻¹) = pCoreOf 2 H := by
      rw [← conjSubgroup_conjSubgroup, h, conjSubgroup_conjSubgroup, mul_inv_cancel,
        conjSubgroup_one]
    have hσx : σ * x⁻¹ ∈ S :=
      h244 _ (mul_mem hσT (inv_mem (hMT hx))) (conjSubgroup_eq_iff_mem_normalizer.mp h')
    have e : σ = (σ * x⁻¹) * x := by group
    rw [e]
    exact mul_mem (hSM hσx) hx

end Main

end C56

theorem c61Lin2Alternatives : C61Lin2Alternatives := by
  intro G _ _ T M H S L hcs hj ⟨n, hn, hlin⟩
  obtain ⟨M₀, hSM, hMT, h2⟩ := C56.exists_index_two hcs
  have hne : S ≠ M₀ := by
    intro h
    rw [← h] at h2
    simp at h2
  obtain ⟨x₀, hx₀, hx₀S⟩ : ∃ x ∈ M₀, x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hSM hcon)
  obtain ⟨q, W, hq, hR1, hmain⟩ :=
    C56.lin2_rank1 naturalModuleStructure hcs hj hn hlin hSM hMT h2
  obtain ⟨-, -, -, -, o5, -, -, o8, -, -, -, -⟩ := hmain x₀ hx₀ hx₀S
  have hiff := C56.lin2_isMaxElemAbelian_iff hcs hj hn hlin hSM hMT h2
  have hAM : ∀ A : Subgroup G, IsMaxElemAbelian M₀ A ↔
      A = pCoreOf 2 H ∨ A = conjR (pCoreOf 2 H) x₀ := by
    intro A
    have h8 := o8 A
    rw [← o5] at h8
    exact (hiff A).trans h8
  have hJ : thompsonJ M₀ = thompsonJ S := by
    unfold thompsonJ
    refine iSup_congr fun A => ?_
    exact iSup_congr_Prop (hiff A) fun _ => rfl
  have hNle := C56.normalizer_le_of_isMaxElemAbelian hcs hSM hMT hx₀ hAM
  have hMeq : M₀ = T := by
    by_contra hne'
    have hlt : M₀ < T := lt_of_le_of_ne hMT hne'
    obtain ⟨y, hyT, hyN, hyM⟩ :=
      C56.exists_mem_normalizer_not_mem_of_lt hcs.setting.sylow.isPGroup hlt
    exact hyM (hNle ⟨hyT, hyN⟩)
  subst hMeq
  exact Or.inl ⟨h2, hJ.symm, fun h3 _ => absurd h3 (C56.lin2_not_alt hn hlin)⟩

end CFSG.QuasithinUnique
