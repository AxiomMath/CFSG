module

public import CFSG.HardMathSupport.Lang.AnisoF4.Closing
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4FrameB4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLeviFrame
public import CFSG.Timmesfeld.ARS.LinearLevis

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoF4

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

set_option linter.unusedSectionVars false


theorem dvd_card_SL4_of_dvd {p q : ℕ} (hq : 1 ≤ q) (hp : p ∣ q ^ 2 + 1) :
    p ∣ q ^ (4 * (4 - 1) / 2) * ∏ j ∈ Finset.Icc 2 4, (q ^ j - 1) := by
  have h4 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    zify [h1, Nat.one_le_pow 4 q hq]
    ring
  have hmem : (4 : ℕ) ∈ Finset.Icc 2 4 := by decide
  refine Dvd.dvd.mul_left ?_ _
  exact (h4 ▸ Dvd.dvd.mul_left hp _).trans (Finset.dvd_prod_of_mem _ hmem)

theorem f4Delta_chain_facts :
    b4Root ≠ f4Delta ∧ b4Root ≠ -f4Delta ∧ iform b4Root f4Delta = 0 ∧
      ¬ IsRoot .F4 (b4Root + f4Delta) ∧ ¬ IsRoot .F4 (b4Root + -f4Delta) ∧
    Pi.single (f4Node 0) 1 ≠ f4Delta ∧ Pi.single (f4Node 0) 1 ≠ -f4Delta ∧
      iform (Pi.single (f4Node 0) 1) f4Delta = 0 ∧
      ¬ IsRoot .F4 (Pi.single (f4Node 0) 1 + f4Delta) ∧
      ¬ IsRoot .F4 (Pi.single (f4Node 0) 1 + -f4Delta) ∧
    Pi.single (f4Node 1) 1 ≠ f4Delta ∧ Pi.single (f4Node 1) 1 ≠ -f4Delta ∧
      iform (Pi.single (f4Node 1) 1) f4Delta = 0 ∧
      ¬ IsRoot .F4 (Pi.single (f4Node 1) 1 + f4Delta) ∧
      ¬ IsRoot .F4 (Pi.single (f4Node 1) 1 + -f4Delta) := by
  simp only [RootCertificate.isRoot_iff (Tag.rootCertificate_check .F4)]
  decide +kernel

variable {K : Type} [Field K]

theorem commutes_b4Chain_rootPairF4_delta (k : Fin 4) (hk : k ≠ 3) :
    Commutes (b4Chain K k) (rootPairF4 K f4Delta) := by
  obtain ⟨n0, n0', i0, s0, s0', n1, n1', i1, s1, s1', n2, n2', i2, s2, s2'⟩ := f4Delta_chain_facts
  fin_cases k
  · exact commutes_rootPair_F4 isRoot_b4Root isRoot_f4Delta n0 n0' i0 s0 s0'
  · exact commutes_rootPair_F4 (isRoot_single _ _) isRoot_f4Delta n1 n1' i1 s1 s1'
  · exact commutes_rootPair_F4 (isRoot_single _ _) isRoot_f4Delta n2 n2' i2 s2 s2'
  · exact absurd rfl hk

theorem commutes_b4Chain_zero_two : Commutes (b4Chain K 0) (b4Chain K 2) :=
  commutes_rootPair_F4 isRoot_b4Root (isRoot_single _ _) b4_root_ne.1 b4_root_ne.2.1
    iform_b4Root_one not_isRoot_b4_sums.1 not_isRoot_b4_sums.2.1

theorem exists_sl4_b4Chain [Finite K] :
    ∃ Ψ : SL(3 + 1, K) →* adjointGroup .F4 K, Ψ.ker ≤ Subgroup.center SL(3 + 1, K) ∧
      Ψ.range = ⨆ k : Fin 3, (![b4Chain K 0, b4Chain K 1, b4Chain K 2] :
        Fin 3 → Subgroup (adjointGroup .F4 K)) k := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n', hℓ, hcardK⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n' : ℕ) := by rw [Nat.card_eq_fintype_card, hcardK]
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL (3 + 1) (ringChar K) n' :=
    ⟨hℓ, n'.pos, by norm_num, by simp, by simp⟩
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
    (Dv := (f4Datum K).divisible) rfl
  obtain ⟨C, -, hC⟩ := f4_commutatorFormula K O
  have hE := f4_chevalleyExtras K O C hC
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  set n : adjointGroup .F4 K :=
    Chevalley.weylElement .F4 K (f4Node 3) * Chevalley.weylElement .F4 K (f4Node 2) with hn
  set ρ : Fin 3 → SL(2, K) →* adjointGroup .F4 K :=
    ![(MulAut.conj n).toMonoidHom.comp (ρF (f4Node 1)), ρF (f4Node 0), ρF (f4Node 1)] with hρ
  have hρ0 : ((MulAut.conj n).toMonoidHom.comp (ρF (f4Node 1))).range = b4Chain K 0 := by
    rw [MonoidHom.range_comp, hρFr, hn, conj_mul_toMonoidHom, ← Subgroup.map_map]
    change (((f4Datum K).rootGroup (Pi.single (f4Node 1) 1) ⊔
      (f4Datum K).rootGroup (-Pi.single (f4Node 1) 1)).map _).map _ = _
    rw [map_conj_weylElement_rootPair_F4 _ (isRoot_single _ _),
      map_conj_weylElement_rootPair_F4 _ (IsRoot.reflect _ (isRoot_single _ _)),
      reflect_three_two_single_one]
    rfl
  have hc02 := commutes_b4Chain_zero_two (K := K)
  obtain ⟨Ψ, hker, hrange, -, -, -⟩ := weakCT_of_frame_subgroup (RingEquiv.refl K)
    (CurtisTits.curtisTitsConclusion_specialLinear hadm hK (by norm_num))
    (CFSG.Timmesfeld.leviConePresented_specialLinear 3 K)
    (CFSG.Timmesfeld.ARS.simplyLacedLevis_specialLinear (m := 3) (F := K)) (⟨0, by norm_num⟩ : Fin 3)
    (U := ![b4Chain K 0, b4Chain K 1, b4Chain K 2])
    (fun i j hij h1 h2 u hu v hv => by
      fin_cases i <;> fin_cases j <;> simp at hij h1 h2
      · exact hc02 u hu v hv
      · exact (hc02 v hv u hu).symm)
    (ρ := ρ)
    (fun k => by
      fin_cases k
      · exact ⟨(MulAut.conj n).injective.comp (hρFi _), hρ0⟩
      · exact ⟨hρFi _, hρFr _⟩
      · exact ⟨hρFi _, hρFr _⟩)
    (fun i j hij => by
      fin_cases i <;> fin_cases j <;> simp at hij
      ·
        obtain ⟨emb, -, -, hv⟩ := ClassicalInvolution.WeakCT.exists_sl3Levi hE rfl
          (i := f4Node 1) (j := f4Node 0) (k := f4Node 2) f4Node_zero_ne_one.symm f4_cartan_10
          f4_cartan_01 f4_sl3_witness_10
        obtain ⟨h0, h1⟩ := sl3_comp_blk hv (hρFv (f4Node 1)) (hρFv (f4Node 0))
        refine ⟨(MulAut.conj n).toMonoidHom.comp emb, ?_, ?_⟩
        · rw [MonoidHom.comp_assoc, h0]
          rfl
        · rw [MonoidHom.comp_assoc, h1]
          refine MonoidHom.ext fun A => ?_
          have hA : ρF (f4Node 0) A ∈ rankOne (f4Datum K).rootGroup (f4Node 0) := by
            rw [← hρFr]
            exact ⟨A, rfl⟩
          rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            (commute_weylElement_three_two hA).eq, mul_inv_cancel_right]
          rfl
      ·
        obtain ⟨emb, -, -, hv⟩ := ClassicalInvolution.WeakCT.exists_sl3Levi hE rfl
          (i := f4Node 0) (j := f4Node 1) (k := f4Node 2) f4Node_zero_ne_one f4_cartan_01
          f4_cartan_10 f4_sl3_witness_01
        exact ⟨emb, sl3_comp_blk hv (hρFv (f4Node 0)) (hρFv (f4Node 1))⟩)
  exact ⟨Ψ, hker, hrange⟩

theorem exists_e1_F4_four [Finite K] {p : ℕ} [hpF : Fact p.Prime] (hp2 : p ≠ 2)
    (hp : p ∣ Nat.card K ^ 2 + 1) :
    ∃ e ∈ b4Chain K 0 ⊔ b4Chain K 1 ⊔ b4Chain K 2, orderOf e = p ∧
      ∀ y ∈ rootPairF4 K f4Delta, Commute e y := by
  classical
  obtain ⟨Ψ, hker, hrange⟩ := exists_sl4_b4Chain (K := K)
  set A : Subgroup (adjointGroup .F4 K) := b4Chain K 0 ⊔ b4Chain K 1 ⊔ b4Chain K 2 with hA
  have hAr : Ψ.range = A := by
    rw [hrange, hA]
    apply le_antisymm
    · refine iSup_le fun k => ?_
      fin_cases k
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    · refine sup_le (sup_le ?_ ?_) ?_
      · exact le_iSup (fun k : Fin 3 => (![b4Chain K 0, b4Chain K 1, b4Chain K 2] :
          Fin 3 → Subgroup (adjointGroup .F4 K)) k) 0
      · exact le_iSup (fun k : Fin 3 => (![b4Chain K 0, b4Chain K 1, b4Chain K 2] :
          Fin 3 → Subgroup (adjointGroup .F4 K)) k) 1
      · exact le_iSup (fun k : Fin 3 => (![b4Chain K 0, b4Chain K 1, b4Chain K 2] :
          Fin 3 → Subgroup (adjointGroup .F4 K)) k) 2
  have hcard : p ∣ Nat.card (SL(3 + 1, K)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num)]
    exact dvd_card_SL4_of_dvd Nat.card_pos hp
  obtain ⟨A₀, hA₀⟩ := exists_prime_orderOf_dvd_card' p hcard
  have hmem : Ψ A₀ ∈ A := hAr ▸ ⟨A₀, rfl⟩
  refine ⟨Ψ A₀, hmem, ?_, ?_⟩
  ·
    have hdvd : orderOf (Ψ A₀) ∣ p := hA₀ ▸ orderOf_map_dvd Ψ A₀
    rcases (Nat.dvd_prime hpF.out).1 hdvd with h1 | h1
    · exfalso
      rw [orderOf_eq_one_iff] at h1
      have hc : A₀ ∈ Subgroup.center SL(3 + 1, K) := hker h1
      obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
      have h4 : A₀ ^ 4 = 1 := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_pow, ← hrA, Matrix.SpecialLinearGroup.coe_one]
        rw [show (Matrix.scalar (Fin (3 + 1)) r) ^ 4 = Matrix.scalar (Fin (3 + 1)) (r ^ 4) by
          rw [map_pow]]
        simp [Fintype.card_fin] at hr
        rw [hr, map_one]
      have hp4 : p ∣ 4 := hA₀ ▸ orderOf_dvd_of_pow_eq_one h4
      have hp2' : p ∣ 2 ^ 2 := by norm_num; exact hp4
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hpF.out Nat.prime_two).1
        (hpF.out.dvd_of_dvd_pow hp2'))
    · exact h1
  ·
    intro y hy
    have hcent : A ≤ Subgroup.centralizer (rootPairF4 K f4Delta : Set (adjointGroup .F4 K)) := by
      refine sup_le (sup_le ?_ ?_) ?_ <;> intro x hx <;> rw [Subgroup.mem_centralizer_iff] <;>
        intro z hz
      · exact ((commutes_b4Chain_rootPairF4_delta 0 (by decide)) x hx z hz).symm
      · exact ((commutes_b4Chain_rootPairF4_delta 1 (by decide)) x hx z hz).symm
      · exact ((commutes_b4Chain_rootPairF4_delta 2 (by decide)) x hx z hz).symm
    exact (Subgroup.mem_centralizer_iff.1 (hcent hmem) y hy).symm

end CFSG.HardMathSupport.Lang.AnisoF4
