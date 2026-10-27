module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Eng
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3TwoL

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H]

theorem fiVariantThreeNM_of_rowInputs (I : FiV3RowInputs) : FiVariantThreeNM := by
  classical
  intro lit H _ _ ih N hN hidx hkp hN22 hN23 hN24 hnb ⟨L₀, hL₀std, hL₀cov⟩
    ⟨P, hPinL, hPcq, hPnm⟩
  have pf := I.basic.pinned
  have hpin : FiV3Pinned := I.basic.toPinned I.rows
  have hrow := hyp31Row_fi23 pf
  obtain ⟨hcore, h4a⟩ := fiHyp31V3L_of_rowFacts pf I.rows I.lx lit hrow H ih N hN hidx hkp hN24
  have hyp : Hyp31NS H N IsKFi23 (IsLS [.Fi24Prime]) := { hrow, hcore with }
  have hcq := cqEq_isKFi23
  have spec := canLocSpec_v3 pf I.rows H
  have hPq : CFSG.IsQuasisimple ↥P := hPinL.isQuasisimple
  have hPK : IsKFi23 ↥P := ⟨inferInstance, hPq, hPcq⟩
  obtain ⟨T₀, hT₀, hT₀2, hPc⟩ := id hPinL
  have hexc := hyp.K_not_exc _ hPK
  obtain ⟨n₀, Lc, Tc, sc, hch₀, hL₀0⟩ :=
    lit.cor23 H ih.uHered hkp N hN (perfect_subgroups_le_of_index_le_two hN.normal hidx)
      T₀ P hT₀2 hPc hexc.1 hexc.2
  have hKch₀ : IsKChain IsKFi23 N n₀ := ⟨Lc, Tc, sc, hch₀, by rw [hL₀0]; exact hPK⟩
  have hn₀ : 1 ≤ n₀ := by
    by_contra hn0
    have hn0' : n₀ = 0 := by omega
    have hKN : P = N := by rw [← hL₀0, ← hch₀.last, hn0']
    have hcomp : IsCompIn N (centralizer (T₀ : Set H)) := by rw [← hKN]; exact hPc
    exact hT₀ (hN.eq_bot_of_isCompIn hcomp)
  have hn₀2 : 2 ≤ n₀ := by
    by_contra hlt
    have h1 : n₀ = 1 := by omega
    subst h1
    refine not_klike_last_ns hyp hch₀ le_rfl ?_ fun _ hstd => ?_
    · have : (1 : ℕ) - 1 = 0 := rfl
      rw [this, hL₀0]
      exact KLike.of_isK hPK
    · have : (1 : ℕ) - 1 = 0 := rfl
      rw [this, hL₀0] at hstd
      exact hPnm (maximal_of_stdBare hPinL hstd)
  obtain ⟨n, hmax⟩ := exists_isMaxKChain hKch₀
  obtain ⟨L₁, T₁, s₁, hch, hL1⟩ := hmax.1
  have hn : n₀ ≤ n := hmax.2 n₀ hKch₀
  have hn2 : 2 ≤ n := by omega
  obtain ⟨hL, hK, hle, hlt, hmaxL, hstdL, hlink, hT1, hcyc⟩ :=
    lemma33_pair_ns hyp hcq (lit.thm22 H ih.uHered) hkp hch hL1 hn2
  obtain ⟨s', hs', hqs, hodd, hspor⟩ := id hL
  obtain rfl : s' = .Fi24Prime := List.mem_singleton.1 hs'
  have hcov : OddCover .Fi24Prime (L₁ (n - 1)) := ⟨hqs, hodd, hspor⟩
  have hinLK : InL (L₁ (n - 2)) := hch.inL hN (by omega)
  have hinLL : InL (L₁ (n - 1)) := hch.inL hN (by omega)
  have hKq : CFSG.IsQuasisimple ↥(L₁ (n - 2)) := hinLK.isQuasisimple
  have hKcq := isSporadic_cq_of_isKFi23 hKq hK
  have hKz : center ↥(L₁ (n - 2)) = ⊥ := pf.mult23 _ hKq hKcq
  have hKcard := card_le_of_isKFi23 I.basic.order23 hK
  have hne : L₁ (n - 2) ≠ L₁ (n - 1) := fun h =>
    absurd (hch.inj (n - 2) (by omega) (n - 1) (by omega) h) (by omega)
  have hcent := I.basic.selfCent H (L₁ (n - 1)) (L₁ (n - 2)) hcov hle hKq hKcq
  have hSol : SolStd (L₁ (n - 1)) := solStd_of_inL_stdBare hinLL hstdL
  obtain ⟨huN0, hunot0, hKu0⟩ := link5b_outer hlink hKq hle hne hcent
  obtain ⟨u, t, hu2, ht2, htL, hut, huN, hunot, hKu⟩ := exists_outer_pair hlink hT1 huN0 hunot0 hKu0
    (I.outerInv lit H ih N hN hidx hkp hN22 hN23 hN24 hnb ⟨L₀, hL₀std, hL₀cov⟩ (L₁ (n - 2))
      (L₁ (n - 1)) (T₁ (n - 1)) (s₁ (n - 1)) hle hne hKq hKcq hcov hSol hlink hT1 hunot0 hKu0)
  have hΛs : Group.IsSolvable ↥(lam (L₁ (n - 1)) (L₁ (n - 2))) :=
    lam_isSolvable (cyclic_sylow_all_of_exists hcyc) (hpin.autSolv H _ _ hcov hle hKq hKcq)
  obtain ⟨N₀, hcan⟩ := spec.exists_loc (L₁ (n - 2)) hKq hK
  have h4 := h4a.four_a (L₁ (n - 2)) (L₁ (n - 1)) hinLK hmaxL hL hlt hle hK N₀ hcan
  have hperf : Group.IsPerfect ↥(L₁ (n - 2)) := hKq.1
  have hemb0 := h4.2 ↥(L₁ (n - 2)) hperf ⟨MulEquiv.refl _⟩
  have hemb : NoFixedEmbeds ↥(L₁ (n - 2)) ↥(lam (L₁ (n - 1)) (L₁ (n - 2))) :=
    noFixedEmbeds_of_le
      (inf_le_inf_left _ (Subgroup.centralizer_le fun x hx => spec.le _ _ hcan hx)) hemb0
  have h33 : ∀ M : Subgroup H, InL M → Lt (L₁ (n - 2)) M → M ≠ L₁ (n - 2) →
      IsLS [.Fi24Prime] ↥M := fun M hM hlt' hne' =>
    lemma33_twoL IsKFi23 (IsLS [.Fi24Prime]) H CanLocV3 hcq spec lit ih.uHered hkp N n L₁ T₁ s₁
      hyp h4a hch hL1 hn2 hmax.2 M hM hlt' hne'
  have hty : ∀ M : Subgroup H, InL M → IsLS [.Fi24Prime] ↥M → SolStd M ∧
      (∃ S : Sylow 2 (centralizer (M : Set H)), IsCyclic ↥S) ∧
        ∀ y : H, 3 ≤ CFSG.pRank 2 ↥(M.map (MulAut.conj y).toMonoidHom) :=
    fun M hM hLS => typeL_facts lit ih.uHered hkp hN hyp hM hLS
  have hKs : IsSporadic ↥(L₁ (n - 2)) .Fi23 := isSporadic_of_center_eq_bot hKz hKcq
  have hunique : ∀ K' : Subgroup H, K' ≤ L₁ (n - 1) → K' ≤ centralizer ({u} : Set H) →
      IsSporadic ↥K' .Fi23 → K' = L₁ (n - 2) := by
    intro K' hK'L hK'C hK's
    obtain ⟨e'⟩ := hK's
    obtain ⟨e⟩ := hKs
    exact eq_of_equiv_of_outer hpin.outerFixed hcov.1 hcov.2.1 hcov.2.2 huN hu2 hunot hle hKq
      hKu hKcard hK'L (fun k hk => mem_centralizer_singleton_iff.1 (hK'C hk)) (e'.trans e.symm)
  have hu1 : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two hu2
  have ht1 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht2
  have hutt : u * t * (u * t) = 1 := by
    calc u * t * (u * t) = u * (t * u) * t := by group
      _ = u * (u * t) * t := by rw [← hut]
      _ = (u * u) * (t * t) := by group
      _ = 1 := by rw [hu1, ht1]; group
  have hut1 : u * t ≠ 1 := by
    intro h
    apply hunot
    have : u = t⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact Subgroup.mem_sup_right (Subgroup.inv_mem _ htL)
  have hut2 : orderOf (u * t) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hutt) hut1
  have hutN : u * t ∈ normalizer (L₁ (n - 1) : Set H) :=
    Subgroup.mul_mem _ huN ((Subgroup.centralizer_le_normalizer (L₁ (n - 1) : Set H)) htL)
  have hutnot : u * t ∉ L₁ (n - 1) ⊔ centralizer (L₁ (n - 1) : Set H) := by
    intro h
    apply hunot
    have h2 := Subgroup.mul_mem _ h
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right htL : t ∈ L₁ (n - 1) ⊔ centralizer _))
    simpa [mul_assoc] using h2
  have hKut : ∀ k ∈ L₁ (n - 2), k * (u * t) = (u * t) * k := by
    intro k hk
    have hkt : k * t = t * k := mem_centralizer_iff.1 htL k (hle hk)
    calc k * (u * t) = (k * u) * t := by rw [mul_assoc]
      _ = (u * k) * t := by rw [hKu k hk]
      _ = u * (k * t) := by rw [mul_assoc]
      _ = u * (t * k) := by rw [hkt]
      _ = (u * t) * k := by rw [mul_assoc]
  have hutt' : u * t * t = t * (u * t) := by
    calc u * t * t = (t * u) * t := by rw [← hut]
      _ = t * (u * t) := by group
  have alt_u := outer_dichotomy lit ih.uHered hpin hN hkp hcov hSol ht2 htL hle hKq hKcard hu2
    huN hunot hKu hut hΛs hemb h33 hty
  have alt_ut := outer_dichotomy lit ih.uHered hpin hN hkp hcov hSol ht2 htL hle hKq hKcard
    hut2 hutN hutnot hKut hutt' hΛs hemb h33 hty
  have hfi : ∀ w : H, L₁ (n - 2) = componentProduct (L₁ (n - 2)) w → orderOf w = 2 →
      w ∈ normalizer (L₁ (n - 1) : Set H) → w ∉ L₁ (n - 1) ⊔ centralizer (L₁ (n - 1) : Set H) →
      (∀ k ∈ L₁ (n - 2), k * w = w * k) → w * t = t * w →
      FiOut H N (L₁ (n - 1)) .Fi24Prime := by
    intro w hw hw2 hwN hwnot hKw hwt
    exact Or.inl ⟨L₁ (n - 2), t, w, ⟨hSol, hcyc, ht2, htL, hwt, hw⟩,
      Or.inr ⟨hwN, hwnot, hw2, hle, hKw, hKq, hKcard, hnb⟩⟩
  refine ⟨.Fi24Prime, L₁ (n - 1), by simp [fiTypes], hcov, ?_⟩
  rcases alt_u with hu35 | ⟨Mu, hMu⟩
  · exact hfi _ hu35 hu2 huN hunot hKu hut
  · rcases alt_ut with hut35 | ⟨Mut, hMut⟩
    · exact hfi _ hut35 hut2 hutN hutnot hKut hutt'
    · refine Or.inr ⟨rfl, t, u, ?_⟩
      exact
        { fstar := hN
          index_le_two := hidx
          standardL := hSol
          cyclicSylow := hcyc
          t_order := ht2
          t_mem := htL
          u_order := hu2
          u_comm_t := hut
          u_mem := huN
          u_not_mem := hunot
          exists_data := ⟨L₁ (n - 2), Mu, Mut,
            { le_L := hle
              le_C := fun k hk => mem_centralizer_singleton_iff.2 (hKu k hk)
              isSporadic := hKs
              unique := hunique
              Lu_comp := hMu.comp
              Lu_cover := hMu.cover
              Lu_std := hMu.std
              le_Lu := hMu.le
              Lut_comp := hMut.comp
              Lut_cover := hMut.cover
              Lut_std := hMut.std
              le_Lut := hMut.le }⟩ }

theorem fiVariantThree_of_rowInputs (I : FiV3RowInputs) : FiVariantThree :=
  fiVariantThree_of_nm I.basic.pinned (fiVariantThreeNM_of_rowInputs I)

theorem fiCoexist_of_rowInputs (I : FiV3RowInputs) (hmax : FiCoexistMax) : FiCoexist :=
  fiCoexist_of_nm (fiVariantThreeNM_of_rowInputs I) hmax

end CFSG.EvenSporadicStandard.Induction.Fi.V3
