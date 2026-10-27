module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Two

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open scoped MatrixGroups commutatorElement
open CFSG.ComponentClassification
open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.CurtisTits
  CFSG.ComponentClassification.CatLeafProof CFSG.TauCetiBridge TauCeti CFSG.Open
  CFSG.HardMathSupport.Lang.AnisoE8 CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Timmesfeld
  CFSG.StandardType.TableBExcTwo

section PerfectFrame

theorem mem_center_of_commutator_mem_center_of_perfect {L : Type*} [Group L]
    (hperf : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤) {x : L}
    (hx : ∀ y : L, ⁅x, y⁆ ∈ Subgroup.center L) : x ∈ Subgroup.center L := by
  rw [Subgroup.mem_center_iff]
  intro y
  have hle : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ ≤ Subgroup.centralizer {x} := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_centralizer_singleton_iff]
    have ha : x * a * x⁻¹ = a * ⁅x, a⁆ := by
      calc x * a * x⁻¹ = ⁅x, a⁆ * a := by simp only [commutatorElement_def]; group
        _ = a * ⁅x, a⁆ := (Subgroup.mem_center_iff.mp (hx a) a).symm
    have hb : x * b * x⁻¹ = b * ⁅x, b⁆ := by
      calc x * b * x⁻¹ = ⁅x, b⁆ * b := by simp only [commutatorElement_def]; group
        _ = b * ⁅x, b⁆ := (Subgroup.mem_center_iff.mp (hx b) b).symm
    have h1 : x * ⁅a, b⁆ * x⁻¹ = ⁅a, b⁆ := by
      calc x * ⁅a, b⁆ * x⁻¹ = ⁅x * a * x⁻¹, x * b * x⁻¹⁆ := by
            simp only [commutatorElement_def]; group
        _ = ⁅a * ⁅x, a⁆, b * ⁅x, b⁆⁆ := by rw [ha, hb]
        _ = ⁅a, b⁆ := commutator_mul_central _ _ _ _ (Subgroup.mem_center_iff.mp (hx a))
              (Subgroup.mem_center_iff.mp (hx b))
    calc ⁅a, b⁆ * x = x * ⁅a, b⁆ * x⁻¹ * x := by rw [h1]
      _ = x * ⁅a, b⁆ := by group
  rw [hperf] at hle
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top y))

variable {G L : Type*} [Group G] [Group L]

theorem exists_conj_le_frame_sylow_of_perfect [Finite G] [Finite L] {k : ℕ}
    (ρ : Fin k → L →* G) (hρk : ∀ i, (ρ i).ker ≤ Subgroup.center L)
    (hρc : Pairwise fun i j => ∀ x y : L, Commute (ρ i x) (ρ j y))
    (hperf : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤)
    {p : ℕ} [hpF : Fact p.Prime] (hZ : ¬ p ∣ Nat.card (Subgroup.center L))
    (hord : (Nat.card G).factorization p ≤ k * (Nat.card L).factorization p) :
    ∃ Q : Subgroup (Fin k → L),
      Disjoint Q (MonoidHom.noncommPiCoprod ρ hρc).ker ∧
      ∀ E : Subgroup G, (∀ x ∈ E, x ^ p = 1) →
        ∃ g : G, E.map (MulAut.conj g).toMonoidHom ≤ Q.map (MonoidHom.noncommPiCoprod ρ hρc) := by
  classical
  set μ := MonoidHom.noncommPiCoprod ρ hρc with hμ
  obtain ⟨Q⟩ : Nonempty (Sylow p (Fin k → L)) := inferInstance
  have hdisj : Disjoint (Q : Subgroup (Fin k → L)) μ.ker := by
    rw [Subgroup.disjoint_def]
    intro x hxQ hxk
    have hx1 : μ x = 1 := hxk
    have hcent : ∀ i, ∀ y : L, ⁅x i, y⁆ ∈ Subgroup.center L := by
      intro i y
      set x' : Fin k → L := Function.update x i 1 with hx'
      have hsplit : x = Pi.mulSingle i (x i) * x' := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [hx']
        · simp [hx', hj]
      have hcomm' : Commute (μ x') (ρ i y) := by
        rw [hμ, MonoidHom.noncommPiCoprod_apply]
        refine (Finset.noncommProd_commute _ _ _ (ρ i y) fun j _ => ?_).symm
        by_cases hj : j = i
        · subst hj
          simp [hx']
        · exact (hρc (Ne.symm hj) _ _)
      have h1 : ρ i (x i) * μ x' = 1 := by
        have := hx1
        rw [hsplit, map_mul, hμ, MonoidHom.noncommPiCoprod_mulSingle] at this
        exact this
      have h2 : ρ i (x i) = (μ x')⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h3 : Commute (ρ i (x i)) (ρ i y) := by
        rw [h2]
        exact (hcomm'.inv_left).symm.symm
      apply hρk i
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr h3.eq
    have hcenter : ∀ i, x i ∈ Subgroup.center L := fun i =>
      mem_center_of_commutator_mem_center_of_perfect hperf (hcent i)
    obtain ⟨m, hm⟩ := Q.isPGroup' ⟨x, hxQ⟩
    have hm' : x ^ (p ^ m) = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have hcop : Nat.Coprime (p ^ m) (Nat.card (Subgroup.center L)) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hpF.out).2 hZ)
    funext i
    have hi : x i ^ (p ^ m) = 1 := by
      have := congrFun hm' i
      simpa using this
    have hd1 : orderOf (x i) ∣ p ^ m := orderOf_dvd_of_pow_eq_one hi
    have hd2 : orderOf (x i) ∣ Nat.card (Subgroup.center L) := by
      have h := orderOf_dvd_natCard (⟨x i, hcenter i⟩ : Subgroup.center L)
      rwa [Subgroup.orderOf_mk] at h
    have hd : orderOf (x i) ∣ Nat.gcd (p ^ m) (Nat.card (Subgroup.center L)) :=
      Nat.dvd_gcd hd1 hd2
    rw [hcop] at hd
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
  refine ⟨Q, hdisj, fun E hEp => ?_⟩
  have hcard : (Nat.card G).factorization p =
      (Nat.card ((Q : Subgroup _).map μ)).factorization p := by
    have h1 : Nat.card ((Q : Subgroup _).map μ) = Nat.card Q := by
      have hinj : Function.Injective (μ.comp (Q : Subgroup _).subtype) := by
        rw [injective_iff_map_eq_one]
        intro x hx
        exact Subtype.ext (Subgroup.disjoint_def.mp hdisj x.2 hx)
      have hrange : (μ.comp (Q : Subgroup _).subtype).range = (Q : Subgroup _).map μ := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [← hrange]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    have h2 : (Nat.card ((Q : Subgroup _).map μ)).factorization p =
        k * (Nat.card L).factorization p := by
      rw [h1, Sylow.card_eq_multiplicity Q, Nat.Prime.factorization_pow hpF.out,
        Finsupp.single_eq_same, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    have h3 : (Nat.card ((Q : Subgroup _).map μ)).factorization p ≤
        (Nat.card G).factorization p :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
        (Subgroup.card_subgroup_dvd_card _) p
    omega
  obtain ⟨g, -, hg⟩ := CFSG.RankThree.PartOne.K133H.exists_conj_le_of_sylow (p := p) (Y := ⊤)
    (H := (Q : Subgroup _).map μ) (A := E) le_top le_top hEp
    (by rw [Subgroup.card_top]; exact hcard)
  exact ⟨g, hg⟩

theorem map_noncommPiCoprod_le_iSup_range {k : ℕ} (ρ : Fin k → L →* G)
    (hρc : Pairwise fun i j => ∀ x y : L, Commute (ρ i x) (ρ j y))
    (Q : Subgroup (Fin k → L)) :
    Q.map (MonoidHom.noncommPiCoprod ρ hρc) ≤ ⨆ i, (ρ i).range := by
  refine le_trans (fun x hx => ?_) (MonoidHom.noncommPiCoprod_range (hcomm := hρc) ρ).le
  rcases hx with ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩

end PerfectFrame

theorem mul_comm_of_mem_iSup_iSup {X : Type*} [Group X] {ι κ : Type*} (A : ι → Subgroup X)
    (B : κ → Subgroup X) (h : ∀ i j, ∀ x ∈ A i, ∀ y ∈ B j, x * y = y * x) :
    ∀ x ∈ ⨆ i, A i, ∀ y ∈ ⨆ j, B j, x * y = y * x := by
  have h1 : ∀ i, ∀ x ∈ A i, ∀ y ∈ ⨆ j, B j, x * y = y * x := by
    intro i x hx y hy
    have : (⨆ j, B j) ≤ Subgroup.centralizer {x} := iSup_le fun j z hz =>
      Subgroup.mem_centralizer_singleton_iff.mpr (h i j x hx z hz).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (this hy)).symm
  intro x hx y hy
  have : (⨆ i, A i) ≤ Subgroup.centralizer {y} := iSup_le fun i z hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h1 i z hz y hy)
  exact Subgroup.mem_centralizer_singleton_iff.mp (this hx)

section Roots

@[expose] def e8D4Root : Fin 8 → (Fin (Tag.rank .E8) → ℤ) :=
  ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0], ![2, 2, 3, 4, 3, 2, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 1, 1, 2, 2, 2, 1, 0]]

@[expose] def e8D4Perm : Fin 8 → Fin 8 := ![3, 1, 2, 0, 7, 5, 6, 4]

@[expose] def e8D4Word : List (Fin (Tag.rank .E8)) :=
  e8w [5, 6, 7, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 3, 4, 2, 3, 0, 2,
    1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 2, 0]

theorem e8D4Perm_swap (i : Fin 8) : e8D4Perm (e8D4Perm i) = i := by
  revert i
  decide

theorem wordReflect_e8Word_e8D4Root : ∀ i : Fin 8,
    CatLeafProof.wordReflect .E8 e8Word (e8D4Root i) = e8D4Root (e8D4Perm i) := by decide

theorem wordReflect_e8D4Word_e8D4Root : ∀ j : Fin 4,
    CatLeafProof.wordReflect .E8 e8D4Word (e8D4Root (Fin.castAdd 4 j)) =
      e8D4Root (Fin.natAdd 4 j) := by
  decide +kernel

theorem e8D8Node_e8D4Root : ∀ j : Fin 4,
    Pi.single (e8D8Node (Fin.natAdd 4 j)) 1 = e8D4Root (Fin.castAdd 4 j) := by decide


theorem e8D4Root_isRoot : ∀ i, IsRoot .E8 (e8D4Root i) := by
  intro i
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E8)]
  revert i
  decide +kernel

theorem e8D4Root_facts : ∀ i j : Fin 4, e8D4Root (Fin.castAdd 4 i) ≠ e8D4Root (Fin.natAdd 4 j) ∧
    e8D4Root (Fin.castAdd 4 i) ≠ -e8D4Root (Fin.natAdd 4 j) ∧
    iform (e8D4Root (Fin.castAdd 4 i)) (e8D4Root (Fin.natAdd 4 j)) = 0 ∧
      ¬ IsRoot .E8 (e8D4Root (Fin.castAdd 4 i) + e8D4Root (Fin.natAdd 4 j)) ∧
        ¬ IsRoot .E8 (e8D4Root (Fin.castAdd 4 i) + -e8D4Root (Fin.natAdd 4 j)) := by
  simp only [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E8)]
  decide +kernel

end Roots

section Arith

theorem not_dvd_of_orderOf_eq_four {p q : ℕ} (hp : p.Prime) (he : orderOf (q : ZMod p) = 4) :
    ¬ p ∣ q := by
  have : Fact p.Prime := ⟨hp⟩
  intro h
  have h0 : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).2 h
  rw [h0, orderOf_zero] at he
  omega

theorem not_dvd_pred_of_orderOf_eq_four {p q : ℕ} (hp : p.Prime) (hq : 1 ≤ q)
    (he : orderOf (q : ZMod p) = 4) : ¬ p ∣ q - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  intro h
  have h1 : (q : ZMod p) = 1 := by
    have := (ZMod.natCast_eq_zero_iff (q - 1) p).2 h
    rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at this
    exact this
  rw [h1, orderOf_one] at he
  omega

@[expose] def ordPOmegaPlus4 (q : ℕ) : ℕ :=
  q ^ (4 * (4 - 1)) * (q ^ 4 - 1) * ∏ i ∈ Finset.Icc 1 (4 - 1), (q ^ (2 * i) - 1)

theorem ordPOmegaPlus4_eq (q : ℕ) : ordPOmegaPlus4 q = q ^ 12 * (q ^ 4 - 1) *
    ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) := by
  simp [ordPOmegaPlus4, Finset.prod_Icc_succ_top]

theorem cast_ordPOmegaPlus4 {q : ℕ} (hq : 1 ≤ q) : (ordPOmegaPlus4 q : ℤ) =
    (q : ℤ) ^ (4 * (4 - 1)) * ((q : ℤ) ^ 4 - 1) *
      ∏ i ∈ Finset.Icc 1 (4 - 1), ((q : ℤ) ^ (2 * i) - 1) := by
  simp only [ordPOmegaPlus4, Nat.cast_mul, Nat.cast_pow, Nat.cast_prod]
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq),
    Finset.prod_congr rfl fun i _ => Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  push_cast
  rfl

theorem factorization_ordPOmegaPlus4_eq {p q : ℕ} (hp : p.Prime) (hq : 2 ≤ q)
    (he : orderOf (q : ZMod p) = 4) :
    (ordPOmegaPlus4 q).factorization p = 2 * (q ^ 4 - 1).factorization p := by
  have hq1 : 1 ≤ q := by omega
  have hnd : ∀ k, ¬ 4 ∣ k → ¬ p ∣ q ^ k - 1 := fun k hk h =>
    hk ((dvd_pow_sub_one_iff_orderOf hq1 he).1 h)
  have hne : ∀ k, 0 < k → q ^ k - 1 ≠ 0 := fun k hk => by
    have := Nat.one_lt_pow hk.ne' (show 1 < q by omega)
    omega
  have hpq : ¬ p ∣ q := not_dvd_of_orderOf_eq_four hp he
  have e : ordPOmegaPlus4 q =
      ((q ^ 4 - 1) * (q ^ 4 - 1)) * (q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1)) := by
    rw [ordPOmegaPlus4_eq]
    ring
  have hR : ¬ p ∣ q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) := by
    simp only [hp.dvd_mul, not_or]
    exact ⟨⟨fun h => hpq (hp.dvd_of_dvd_pow h), hnd 2 (by norm_num)⟩, hnd 6 (by norm_num)⟩
  have h4 := hne 4 (by norm_num)
  rw [e, factorization_mul_eq_left (mul_ne_zero h4 h4) hR, Nat.factorization_mul h4 h4,
    Finsupp.add_apply]
  ring

section SpinFour

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.ModelFacts.OrthAut

theorem factorization_ordPOmegaPlus4_le_card_proj {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (h7 : 7 ≤ p) (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 4) :
    (ordPOmegaPlus4 (Nat.card K)).factorization p ≤
      (Nat.card (StatedProj (StatedOmega (StatedQuadPlus 4 K)))).factorization p := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  by_cases h2 : ringChar K = 2
  · have : CharP K 2 := h2 ▸ ringChar.charP K
    have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus (K := K)
      (n := 4) (by norm_num)
    rw [← cast_ordPOmegaPlus4 Nat.card_pos] at h
    have h' : Nat.card (StatedProj (StatedOmega (StatedQuadPlus 4 K))) =
        ordPOmegaPlus4 (Nat.card K) := by
      exact_mod_cast h
    rw [h']
  · have h := CFSG.ClassicalInvolution.card_statedProj_statedOmega_quadPlus_eq_ordD hℓ h2 hK
      (n := 4) (by norm_num)
    rw [h, ← hK]
    set q := Nat.card K with hq
    have hdef : CFSG.Open.ordD 4 q = ordPOmegaPlus4 q / Nat.gcd 4 (q ^ 4 - 1) := rfl
    have hg : Nat.gcd 4 (q ^ 4 - 1) ∣ ordPOmegaPlus4 q := by
      refine (Nat.gcd_dvd_right _ _).trans ?_
      rw [ordPOmegaPlus4]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left dvd_rfl _) _
    have hgf : (Nat.gcd 4 (q ^ 4 - 1)).factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hdv
      have := Nat.le_of_dvd (by norm_num) (hdv.trans (Nat.gcd_dvd_left 4 _))
      omega
    rw [hdef, Nat.factorization_div hg, Finsupp.coe_tsub, Pi.sub_apply, hgf, Nat.sub_zero]

theorem finite_spinGroup_quadPlus_four (K : Type) [Field K] [Finite K] :
    Finite (spinGroup (Spin.quadPlus 4 K)) := by
  have : Nonempty (Fin 4 ⊕ Fin 4) := ⟨Sum.inl 0⟩
  exact CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _
    coe_ker_spinMatrix_quadPlus

end SpinFour

end Arith

section Groups


theorem factorization_card_E8_of_orderOf_eq_four {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (h7 : 7 ≤ p) (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 4) :
    (Nat.card (adjointGroup .E8 K)).factorization p = 4 * (Nat.card K ^ 4 - 1).factorization p := by
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hq2 : 2 ≤ Nat.card K :=
    Nat.succ_le_of_lt (Finite.one_lt_card_iff_nontrivial.2 inferInstance)
  have hpK := not_dvd_of_orderOf_eq_four hp he
  have h1 := ordProj_card_adjointGroup_E (τ := .E8) (Or.inr (Or.inr rfl)) (K := K) hp (by omega)
    hpK
  have h2 := prod_ordProj_pow_sub_one hp (by omega) hpK hq2 he (degreesE .E8) (by
    intro d hd hde
    refine ⟨?_, ?_⟩
    · rintro rfl
      simp [degreesE] at hd
    · simp only [degreesE, List.mem_cons, List.not_mem_nil, or_false] at hd
      intro hdv
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | omega
          | (have := Nat.le_of_dvd (by norm_num) hdv; omega))
  rw [h2] at h1
  have h3 : (degreesE .E8).filter (fun d => 4 ∣ d) = [8, 12, 20, 24] := by
    simp [degreesE]
  rw [h3] at h1
  have h4 : ([8, 12, 20, 24] : List ℕ).length = 4 := rfl
  rw [h4, ← pow_mul] at h1
  exact (Nat.pow_right_injective hp.two_le h1).trans (mul_comm _ _)

variable {K : Type} [Field K]

@[expose] noncomputable def e8D4Group (K : Type) [Field K] : Subgroup (adjointGroup .E8 K) :=
  ⨆ i, rootPairE8 K (e8D4Root i)

theorem rootPairE8_e8D4Root_le_d8 (i : Fin 8) :
    rootPairE8 K (e8D4Root i) ≤ ⨆ k, e8D8Chain K k := by
  fin_cases i
  · have e : e8D4Root 0 = Pi.single (e8Node 4) 1 := by decide
    show rootPairE8 K (e8D4Root 0) ≤ _
    rw [e]
    exact rootPairE8_simple_le_d8 4 (by decide)
  · have e : e8D4Root 1 = Pi.single (e8Node 3) 1 := by decide
    show rootPairE8 K (e8D4Root 1) ≤ _
    rw [e]
    exact rootPairE8_simple_le_d8 3 (by decide)
  · have e : e8D4Root 2 = Pi.single (e8Node 2) 1 := by decide
    show rootPairE8 K (e8D4Root 2) ≤ _
    rw [e]
    exact rootPairE8_simple_le_d8 2 (by decide)
  · have e : e8D4Root 3 = Pi.single (e8Node 1) 1 := by decide
    show rootPairE8 K (e8D4Root 3) ≤ _
    rw [e]
    exact rootPairE8_simple_le_d8 1 (by decide)
  · have e : e8D4Root 4 = e8D8Root := by decide
    show rootPairE8 K (e8D4Root 4) ≤ _
    rw [e]
    exact rootPairE8_theta_le_d8
  · have e : e8D4Root 5 = Pi.single (e8Node 7) 1 := by decide
    show rootPairE8 K (e8D4Root 5) ≤ _
    rw [e]
    exact rootPairE8_simple_le_d8 7 (by decide)
  · have e : e8D4Root 6 = Pi.single (e8Node 6) 1 := by decide
    show rootPairE8 K (e8D4Root 6) ≤ _
    rw [e]
    exact rootPairE8_simple_le_d8 6 (by decide)
  · have e : e8D4Root 7 = frameE8Root 2 := by decide
    show rootPairE8 K (e8D4Root 7) ≤ _
    rw [e]
    exact rootPairE8_frame_le_d8 2

theorem e8D4Group_le_d8 : e8D4Group K ≤ ⨆ k, e8D8Chain K k :=
  iSup_le fun i => rootPairE8_e8D4Root_le_d8 i

theorem e8D4Group_le_conj_d8 : e8D4Group K ≤
    (⨆ k, e8D8Chain K k).map (MulAut.conj (weylWordElt .E8 K e8Word)).toMonoidHom := by
  refine iSup_le fun i => ?_
  have h := map_conj_weylWordElt_rootPair (K := K) e8Word (e8D4Root_isRoot (e8D4Perm i))
  rw [wordReflect_e8Word_e8D4Root, e8D4Perm_swap] at h
  change (e8Datum K).rootGroup (e8D4Root i) ⊔ (e8Datum K).rootGroup (-e8D4Root i) ≤ _
  rw [← h]
  exact Subgroup.map_mono (rootPairE8_e8D4Root_le_d8 _)

@[expose] noncomputable def e8D4Levi (K : Type) [Field K] : Subgroup (adjointGroup .E8 K) :=
  ⨆ j : Fin 4, e8D8Chain K (Fin.natAdd 4 j)

theorem e8D8Chain_natAdd (j : Fin 4) :
    e8D8Chain K (Fin.natAdd 4 j) = rootPairE8 K (e8D4Root (Fin.castAdd 4 j)) := by
  have hk : Fin.natAdd 4 j ≠ (0 : Fin 8) := by
    revert j
    decide
  have hU : e8D8Chain K (Fin.natAdd 4 j) =
      rankOne (e8Datum K).rootGroup (e8D8Node (Fin.natAdd 4 j)) := by
    unfold e8D8Chain
    rw [ite_eq_right_iff.2 (fun h => absurd h hk)]
  rw [hU, ← e8D8Node_e8D4Root j]
  rfl

theorem e8D4Levi_eq : e8D4Levi K = ⨆ j : Fin 4, rootPairE8 K (e8D4Root (Fin.castAdd 4 j)) := by
  unfold e8D4Levi
  congr 1
  funext j
  exact e8D8Chain_natAdd j

@[expose] noncomputable def e8D4Perp (K : Type) [Field K] : Subgroup (adjointGroup .E8 K) :=
  (e8D4Levi K).map (MulAut.conj (weylWordElt .E8 K e8D4Word)).toMonoidHom

theorem e8D4Perp_eq : e8D4Perp K = ⨆ j : Fin 4, rootPairE8 K (e8D4Root (Fin.natAdd 4 j)) := by
  unfold e8D4Perp
  rw [e8D4Levi_eq, Subgroup.map_iSup]
  congr 1
  funext j
  have h := map_conj_weylWordElt_rootPair (K := K) e8D4Word (e8D4Root_isRoot (Fin.castAdd 4 j))
  rw [wordReflect_e8D4Word_e8D4Root] at h
  exact h

theorem e8D4Levi_sup_perp_le : e8D4Levi K ⊔ e8D4Perp K ≤ e8D4Group K := by
  refine sup_le ?_ ?_
  · rw [e8D4Levi_eq]
    exact iSup_le fun j => le_iSup (fun i => rootPairE8 K (e8D4Root i)) (Fin.castAdd 4 j)
  · rw [e8D4Perp_eq]
    exact iSup_le fun j => le_iSup (fun i => rootPairE8 K (e8D4Root i)) (Fin.natAdd 4 j)

theorem e8D4Levi_commute_perp : ∀ x ∈ e8D4Levi K, ∀ y ∈ e8D4Perp K, x * y = y * x := by
  rw [e8D4Levi_eq, e8D4Perp_eq]
  refine mul_comm_of_mem_iSup_iSup _ _ fun i j x hx y hy => ?_
  obtain ⟨h1, h2, h3, h4, h5⟩ := e8D4Root_facts i j
  exact commutes_rootPair_of_noG2 (K := K) noG2_E8 (e8D4Root_isRoot _) (e8D4Root_isRoot _)
    h1 h2 h3 h4 h5 x hx y hy

theorem exists_psi_D4_E8 (K : Type) [Field K] [Finite K] :
    ∃ Ψ : spinGroup (Spin.quadPlus 4 K) →* adjointGroup .E8 K,
      Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus 4 K)) ∧ Ψ.range = e8D4Levi K := by
  obtain ⟨ρ, hρ', hcomm, hψ⟩ := exists_e8D8_family K
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .POmegaPlus 4 (ringChar K) n :=
    ⟨hℓ, n.pos, by norm_num⟩
  have hedge : ∀ i j : Fin 4, edgeD 4 i j ↔ edgeD 8 (Fin.natAdd 4 i) (Fin.natAdd 4 j) := by
    decide
  obtain ⟨Ψ, h1, h2, -, -⟩ := spinPlus_frame_subgroup (n := 4)
    (U := fun j => e8D8Chain K (Fin.natAdd 4 j)) (ρ := fun j => ρ (Fin.natAdd 4 j)) hadm
    (by norm_num) hK
    (fun i j hij hi hj u hu v hv => hcomm (Fin.natAdd 4 i) (Fin.natAdd 4 j)
      (fun h => hij (by simpa [Fin.ext_iff] using h)) (fun h => hi ((hedge i j).2 h))
      (fun h => hj ((hedge j i).2 h)) u hu v hv)
    (fun k => hρ' _)
    (fun i j hij => hψ (Fin.natAdd 4 i) (Fin.natAdd 4 j) ((hedge i j).1 hij))
  exact ⟨Ψ, h1, h2⟩

section SylowD4

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.ModelFacts.OrthAut

theorem e8FourSylow :
    ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime], 7 ≤ p →
      orderOf ((Nat.card K : ℕ) : ZMod p) = 4 →
      ∀ E₀ : Subgroup (adjointGroup .E8 K), (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 →
        ∃ g : adjointGroup .E8 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e8D4Group K := by
  intro K _ _ p hpF h7 he E₀ hE₀p hE₀c
  have hn3 : 3 ≤ 4 := by norm_num
  have : Nonempty (Fin 4 ⊕ Fin 4) := ⟨Sum.inl 0⟩
  have : Finite (spinGroup (quadPlus 4 K)) := finite_spinGroup_quadPlus_four K
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hq2 : 2 ≤ Nat.card K :=
    Nat.succ_le_of_lt (Finite.one_lt_card_iff_nontrivial.2 inferInstance)
  have hp2 : p ≠ 2 := by omega
  have hpq1 : ¬ p ∣ Nat.card K - 1 := not_dvd_pred_of_orderOf_eq_four hpF.out hq1 he
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D4_E8 K
  set w := weylWordElt .E8 K e8D4Word with hw
  set Ψ' : spinGroup (quadPlus 4 K) →* adjointGroup .E8 K :=
    (MulAut.conj w).toMonoidHom.comp Ψ with hΨ'
  have hΨ'range : Ψ'.range = e8D4Perp K := by
    rw [hΨ', MonoidHom.range_comp, hrange]
    rfl
  let ρ : Fin 2 → spinGroup (quadPlus 4 K) →* adjointGroup .E8 K := ![Ψ, Ψ']
  have hρk : ∀ i, (ρ i).ker ≤ Subgroup.center (spinGroup (quadPlus 4 K)) := by
    intro i
    fin_cases i
    · exact hker
    · intro x hx
      apply hker
      have h1 : (MulAut.conj w).toMonoidHom (Ψ x) = 1 := hx
      exact (MulAut.conj w).injective (h1.trans (map_one (MulAut.conj w)).symm)
  have hmemL : ∀ x, Ψ x ∈ e8D4Levi K := fun x => hrange ▸ ⟨x, rfl⟩
  have hmemP : ∀ x, Ψ' x ∈ e8D4Perp K := fun x => hΨ'range ▸ ⟨x, rfl⟩
  have hρc : Pairwise fun i j => ∀ x y, Commute (ρ i x) (ρ j y) := by
    intro i j hij x y
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact e8D4Levi_commute_perp _ (hmemL x) _ (hmemP y)
    · exact (e8D4Levi_commute_perp _ (hmemL y) _ (hmemP x)).symm
    · exact absurd rfl hij
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := 4) (K := K) hn3
  set π := spinToStatedProj (quadPlus 4 K) (range_spinMatrix_quadPlus hn3) with hπdef
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 4 K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadPlus 4 K) (range_spinMatrix_quadPlus hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2 hpq1
  have hperf : ⁅(⊤ : Subgroup (spinGroup (quadPlus 4 K))), ⊤⁆ = ⊤ :=
    (isPerfect_spinGroup_quadPlus hn3).commutator_eq_top
  have hcard : Nat.card (spinGroup (quadPlus 4 K)) =
      Nat.card (StatedProj (StatedOmega (StatedQuadPlus 4 K))) *
        Nat.card (Subgroup.center (spinGroup (quadPlus 4 K))) := by
    have e := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπsurj).toEquiv
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    rw [e, hZ] at h
    exact h
  have hord : (Nat.card (adjointGroup .E8 K)).factorization p ≤
      2 * (Nat.card (spinGroup (quadPlus 4 K))).factorization p := by
    rw [factorization_card_E8_of_orderOf_eq_four hpF.out h7 he]
    have h1 := factorization_ordPOmegaPlus4_eq hpF.out hq2 he
    have h2 := factorization_ordPOmegaPlus4_le_card_proj (K := K) hpF.out h7 he
    have h3 : (Nat.card (StatedProj (StatedOmega (StatedQuadPlus 4 K)))).factorization p ≤
        (Nat.card (spinGroup (quadPlus 4 K))).factorization p :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
        (Dvd.intro _ hcard.symm) p
    omega
  obtain ⟨Q, -, hQ⟩ := exists_conj_le_frame_sylow_of_perfect ρ hρk hρc hperf hcen hord
  obtain ⟨g, hg⟩ := hQ E₀ hE₀p
  refine ⟨g, hg.trans ((map_noncommPiCoprod_le_iSup_range ρ hρc Q).trans ?_)⟩
  refine iSup_le fun i => ?_
  fin_cases i
  · exact (hrange.le.trans le_sup_left).trans e8D4Levi_sup_perp_le
  · exact (hΨ'range.le.trans le_sup_right).trans e8D4Levi_sup_perp_le

end SylowD4

section ClassicalD8

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.ModelFacts.OrthAut

theorem iSup_d8Chain_le_closure_centralizers_of_ne {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) (hpq1 : ¬ p ∣ Nat.card K - 1)
    (Ψ : spinGroup (Spin.quadPlus 8 K) →* adjointGroup .E8 K)
    (hker : Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus 8 K)))
    (hrange : Ψ.range = ⨆ k, e8D8Chain K k)
    (E : Subgroup (adjointGroup .E8 K)) (hE : E ≤ ⨆ k, e8D8Chain K k)
    (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    ⨆ k, e8D8Chain K k ≤ Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x} := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hn3 : 3 ≤ 8 := by norm_num
  have : Nonempty (Fin 8 ⊕ Fin 8) := ⟨Sum.inl 0⟩
  have : Finite (spinGroup (quadPlus 8 K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := 8) (K := K) hn3
  set π := spinToStatedProj (quadPlus 8 K) (range_spinMatrix_quadPlus hn3) with hπdef
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 8 K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadPlus 8 K) (range_spinMatrix_quadPlus hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2 hpq1
  have hπcop : ¬ p ∣ Nat.card π.ker := by
    intro hd
    apply hcen
    have : Nat.card π.ker ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 8 K))) := by
      rw [hZ]
    exact hd.trans this
  have hΨcop : ¬ p ∣ Nat.card Ψ.ker := by
    intro hd
    apply hcen
    exact hd.trans (Subgroup.card_dvd_of_le hker)
  have hperf : ⁅(⊤ : Subgroup (spinGroup (quadPlus 8 K))), ⊤⁆ = ⊤ :=
    (isPerfect_spinGroup_quadPlus hn3).commutator_eq_top
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup E := IsPGroup.commGroupOfCardEqPrimeSq hEc
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hE_le : E ≤ Ψ.range := hrange ▸ hE
  set Ψ' : spinGroup (quadPlus 8 K) →* Ψ.range := Ψ.rangeRestrict with hΨ'
  have hΨ'surj : Function.Surjective Ψ' := Ψ.rangeRestrict_surjective
  have hΨ'ker : Ψ'.ker = Ψ.ker := Ψ.ker_rangeRestrict
  set E1 : Subgroup Ψ.range := E.subgroupOf Ψ.range with hE1def
  have hE1 : IsElemAbelian p E1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hEp x hx)⟩
  obtain ⟨E', hmapE', hdisE', hE'ea⟩ :=
    exists_lift_elemAbelian_of_coprime_ker Ψ' hΨ'surj (hΨ'ker ▸ hΨcop) hE1
  have hcardE1 : Nat.card E1 = p ^ 2 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le).toEquiv
  have hcardE' : Nat.card E' = p ^ 2 := by
    rw [← card_map_eq_of_disjoint_ker Ψ' hdisE', hmapE', hcardE1]
  set Ebar : Subgroup _ := E'.map π with hEbar
  have hEbarea : IsElemAbelian p Ebar :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE'ea π
  have hcardEbar : Nat.card Ebar = p ^ 2 := by
    rw [hEbar, card_map_eq_of_disjoint_ker π (disjoint_ker_of_exponent π hπcop hE'ea.2), hcardE']
  have hmodel := orthogonalPlusPlanes 8 p K (by norm_num) hp hp5 hpK Ebar hEbarea hcardEbar
  have hG := closure_centralizers_of_quotient π hπsurj hZ.le hπcop hperf E' hE'ea.2 hmodel
  have hdisΨ : Disjoint E' Ψ.ker := hΨ'ker ▸ hdisE'
  rw [← hrange, MonoidHom.range_eq_map, ← hG, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨g, ⟨x, hx, hx1, hg⟩, rfl⟩
  refine ⟨Ψ x, ?_, ?_, ?_⟩
  · have : Ψ' x ∈ E1 := hmapE' ▸ ⟨x, hx, rfl⟩
    exact this
  · intro h1
    exact hx1 (Subgroup.disjoint_def.mp hdisΨ hx (MonoidHom.mem_ker.mpr h1))
  · show Ψ g * Ψ x = Ψ x * Ψ g
    rw [← map_mul, ← map_mul]
    exact congrArg Ψ hg

end ClassicalD8

@[expose] def E8FourD8 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime], 7 ≤ p →
    orderOf ((Nat.card K : ℕ) : ZMod p) = 4 →
    ∀ E : Subgroup (adjointGroup .E8 K), E ≤ ⨆ k, e8D8Chain K k → (∀ x ∈ E, x ^ p = 1) →
      Nat.card E = p ^ 2 →
        ⨆ k, e8D8Chain K k ≤ Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x}

@[expose] def E8FourNative : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime], 7 ≤ p →
    orderOf ((Nat.card K : ℕ) : ZMod p) = 4 →
    ∀ E₀ : Subgroup (adjointGroup .E8 K), (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 →
      Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤

theorem e8FourNative_of_interfaces (h2 : E8FourD8) : E8FourNative := by
  have h1 := e8FourSylow
  intro K _ _ p hpF h7 he E₀ hE₀p hE₀c
  obtain ⟨g, hg⟩ := h1 K p h7 he E₀ hE₀p hE₀c
  exact closure_centralizers_eq_top_of_two_conj (p := p) (⨆ k, e8D8Chain K k) (e8D4Group K)
    (weylWordElt .E8 K e8Word) e8D4Group_le_d8 e8D4Group_le_conj_d8
    (fun M hX hn => eq_top_of_e8D8Chain_le_of_conj_le M hX hn)
    (fun E hE hEp hEc => h2 K p h7 he E hE hEp hEc) E₀ hE₀p hE₀c ⟨g, hg⟩

theorem e8FourD8 : E8FourD8 := by
  intro K _ _ p hpF h7 he E hE hEp hEc
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family (exists_e8D8_family K)
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  exact iSup_d8Chain_le_closure_centralizers_of_ne hpF.out (by omega)
    (not_dvd_of_orderOf_eq_four hpF.out he) (not_dvd_pred_of_orderOf_eq_four hpF.out hq1 he)
    Ψ hker hrange E hE hEp hEc

theorem e8FourNative : E8FourNative := e8FourNative_of_interfaces e8FourD8

section Glue


@[expose] def SeitzExcHighE8FourGeSeven : Prop :=
  SeitzExcHighForAt IsE8Index fun d p => 7 ≤ p ∧ ClassRange LieTypeIndex.E8 (fun _ => True) 4 d p

theorem seitzExcHighE8Four_of_native (h : E8FourNative) : SeitzExcHighE8FourGeSeven := by
  intro d p hp _ _ _ E hE hcard hS
  obtain ⟨hin, -, ⟨hp7, -, q, hdq, -, hord⟩, -, -⟩ := hS
  obtain ⟨d₁, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨K, _, _, hKq, hchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have : Fact p.Prime := ⟨hp⟩
  have hord' : orderOf ((Nat.card K : ℕ) : ZMod p) = 4 := by
    rw [hKq]
    exact hord
  exact CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.planeGen_of_native_closure e
    center_adjointGroup_eq_bot (fun E₀ hE₀p hE₀c => h K p hp7 hord' E₀ hE₀p hE₀c) hE hcard hin

theorem seitzExcHighE8Four_of_ge_seven : SeitzExcHighE8FourGeSeven :=
  seitzExcHighE8Four_of_native e8FourNative

@[expose] def SeitzExcHighE8FourLtSeven : Prop :=
  SeitzExcHighForAt IsE8Index fun d p => p < 7 ∧ ClassRange LieTypeIndex.E8 (fun _ => True) 4 d p

theorem seitzExcHighE8Four_of_ge_seven_of_lt
    (h : SeitzExcHighE8FourLtSeven) : SeitzExcHighE8Four :=
  SeitzExcHighForAt.union (fun d p _ _ hQ => (Nat.lt_or_ge p 7).elim
    (fun h' => Or.inr ⟨h', hQ⟩) (fun h' => Or.inl ⟨h', hQ⟩))
    seitzExcHighE8Four_of_ge_seven h

end Glue

end Groups

end CFSG.LieType.SeitzGeneration.ExcHigh
