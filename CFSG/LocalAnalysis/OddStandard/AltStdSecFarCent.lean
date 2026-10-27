module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarStd
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarAlt
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarMain
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarSecWreath
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.Asc75.Helpers
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoMain

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.RankTwoStandard
  CFSG.OddStandard.AltStdBal

section Bound

variable {X : Type} [Group X] [Finite X]

theorem card_le_of_le_normalizer {A : Subgroup X} {n : ℕ} (e : A ≃* alternatingGroup (Fin n))
    (hn : 8 ≤ n) {H : Subgroup X} (hH : H ≤ normalizer (A : Set X)) :
    Nat.card H ≤ Nat.card ↥(H ⊓ centralizer (A : Set X)) * n.factorial := by
  set f : ↥H →* Perm (Fin n) := (AltStdBal.rho e hn).comp (Subgroup.inclusion hH) with hf
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at h1
  have h2 : Nat.card f.range ≤ n.factorial := by
    calc Nat.card f.range ≤ Nat.card (Perm (Fin n)) := Subgroup.card_le_card_group _
      _ = n.factorial := by rw [Nat.card_perm, Nat.card_fin]
  have h3 : Nat.card f.ker ≤ Nat.card ↥(H ⊓ centralizer (A : Set X)) := by
    refine Nat.card_le_card_of_injective (fun k => ⟨((k : H) : X), Subgroup.mem_inf.2 ⟨(k : H).2,
      (AltStdBal.rho_eq_one_iff e hn _).1 (MonoidHom.mem_ker.1 k.2)⟩⟩) ?_
    intro a b hab
    have := congrArg Subtype.val hab
    simp only at this
    exact Subtype.ext (Subtype.ext this)
  calc Nat.card H = Nat.card f.ker * Nat.card f.range := h1.symm
    _ ≤ Nat.card ↥(H ⊓ centralizer (A : Set X)) * n.factorial := Nat.mul_le_mul h3 h2

end Bound

section Final

variable {G : Type} [Group G] [Finite G] {z : G} {m : ℕ} (O : OverData G z m) (h4 : 4 ≤ m + 3)

omit [Finite G] in
theorem centralizer_ebar_le_normalizer :
    centralizer ({ebar O h4} : Set (Cbar O h4)) ≤ normalizer (L0bar O h4 : Set (Cbar O h4)) := by
  intro q hq
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
  exact comm_ebar_mem_normalizer O h4 (mem_centralizer_singleton_iff.1 hq)

theorem card_centralizer_ebar_le (hm : 9 ≤ m) :
    Nat.card (centralizer ({ebar O h4} : Set (Cbar O h4))) ≤ 4 * (m - 1).factorial := by
  have h1 := card_le_of_le_normalizer (L0barEquiv O h4 (by omega)) (by omega)
    (centralizer_ebar_le_normalizer O h4)
  have h2 : Nat.card ↥(centralizer ({ebar O h4} : Set (Cbar O h4)) ⊓
      centralizer (L0bar O h4 : Set (Cbar O h4))) ≤ Nat.card (kbar O h4) :=
    Subgroup.card_le_of_le (fun q hq => mem_kbar_of_comm_ebar O h4 (by omega)
      (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hq).1) (Subgroup.mem_inf.1 hq).2)
  have h3 := card_kbar_le O h4
  calc Nat.card (centralizer ({ebar O h4} : Set (Cbar O h4))) ≤
      Nat.card ↥(centralizer ({ebar O h4} : Set (Cbar O h4)) ⊓
        centralizer (L0bar O h4 : Set (Cbar O h4))) * (m - 1).factorial := h1
    _ ≤ 4 * (m - 1).factorial := Nat.mul_le_mul_right _ (h2.trans h3)

omit [Finite G] in
theorem ebar_mul_fbar : ebar O h4 * fbar O h4 = fbar O h4 * ebar O h4 := by
  rw [← map_mul, ← map_mul]
  rw [psi4_congr O h4 (x := swap 0 1 * (swap 0 2 * swap 1 3)) (mem_dEight_iff.2 (by decide)) rfl,
    psi4_congr O h4 (d := ⟨swap 0 2 * swap 1 3, _⟩ * ⟨swap 0 1, _⟩)
      (x := swap 0 1 * (swap 0 2 * swap 1 3) * kA4) (mem_dEight_iff.2 (by decide)) (by decide),
    psi4_mul_kA4]

omit [Finite G] in
theorem ebar_ne_fbar : ebar O h4 ≠ fbar O h4 := by
  intro h
  have h1 : psi4 O h4 ⟨(swap 0 1)⁻¹ * (swap 0 2 * swap 1 3), mem_dEight_iff.2 (by decide)⟩ = 1 := by
    have : (⟨(swap 0 1)⁻¹ * (swap 0 2 * swap 1 3), mem_dEight_iff.2 (by decide)⟩ : dEight) =
        (⟨swap 0 1, mem_dEight_iff.2 (by decide)⟩ : dEight)⁻¹ *
          ⟨swap 0 2 * swap 1 3, mem_dEight_iff.2 (by decide)⟩ := rfl
    rw [this, map_mul, map_inv]
    change (ebar O h4)⁻¹ * fbar O h4 = 1
    rw [h, inv_mul_cancel]
  exact psi4_ne_one O h4 _ (by decide) (by decide) h1

theorem normal_L0bar (hR2 : RankTwoAlternatingStandard) (hNE : L0Normal O (kleinR h4))
    (hNy : L0Normal O (cycR h4))
    (hKC : CFSG.SectionRank.IsKGroupCat (Cbar O h4)) (hO : CFSG.oddCore (Cbar O h4) = ⊥)
    (hm : 10 ≤ m) : (L0bar O h4).Normal := by
  by_contra hnn
  have heK : ebar O h4 ∈ kbar O h4 := ⟨_, rfl⟩
  have hfK : fbar O h4 ∈ kbar O h4 := ⟨_, rfl⟩
  have he2 := mul_self_of_mem_kbar O h4 heK
  have hrank : 2 ≤ CFSG.Open.pRank 2 (centralizer (L0bar O h4 : Set (Cbar O h4))) :=
    CFSG.Asc75.two_le_pRank_of_pair he2 (mul_self_of_mem_kbar O h4 hfK) (ebar_mul_fbar O h4)
      (psi4_ne_one O h4 _ (by decide) (by decide)) (psi4_ne_one O h4 _ (by decide) (by decide))
      (ebar_ne_fbar O h4) (kbar_le_centralizer O h4 heK) (kbar_le_centralizer O h4 hfK)
  have hyp : RankTwoHyp (Cbar O h4) (L0bar O h4) :=
    ⟨fun K L _ _ _ hs _ => hKC K _ hs, isStandard_L0bar O h4 hNE hNy (by omega), hnn, hrank⟩
  have hc : center ↥(L0bar O h4) = ⊥ := center_eq_bot_of_alt (by omega) (L0barEquiv O h4 (by omega))
  have eq : rankTwoQuot (L0bar O h4) ≃* alternatingGroup (Fin (m - 1)) :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans
      (L0barEquiv O h4 (by omega))
  rcases hR2 _ _ hyp hO (m - 1) (by omega) ⟨eq⟩ with hψ | ⟨h5, -⟩ | ⟨h5, -, -⟩
  · obtain ⟨ψ⟩ := hψ
    have hLt : L0bar O h4 ≤ centralizer ({ebar O h4} : Set (Cbar O h4)) := by
      intro l hl
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.1 (kbar_le_centralizer O h4 heK) l hl)
    have hCt : Nat.card (centralizer ({ebar O h4} : Set (Cbar O h4))) ≤
        4 * (m - 1 + 4 - 4).factorial := by
      rw [show m - 1 + 4 - 4 = m - 1 by omega]
      exact card_centralizer_ebar_le O h4 (by omega)
    refine false_of_alt (N := m - 1 + 4) (by omega) (X := rankTwoX (L0bar O h4)) ψ he2
      Subgroup.le_normalClosure hLt ((L0barEquiv O h4 (by omega)).trans
        (Equiv.altCongrHom (finCongr (by omega)))) hCt ?_
    intro u v hu1 hu2 hv1 hv2 huv
    exact eq_of_isConj_of_mem_kbar O h4 (by omega) (mem_kbar_of_comm_ebar O h4 (by omega) hu1 hu2)
      (mem_kbar_of_comm_ebar O h4 (by omega) hv1 hv2) huv
  · omega
  · omega

theorem card_Jbar_le (hm : 10 ≤ m) (hN : (L0bar O h4).Normal) (hO : CFSG.oddCore (Cbar O h4) = ⊥) :
    Nat.card (Jbar O h4) ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hKP⟩ := (isPGroup_kbarJ O h4).exists_le_sylow
  have hPK := sylow_le_kbar O h4 hm P hKP
  have hP : normalizer (P : Set (Jbar O h4)) ≤ centralizer (P : Set (Jbar O h4)) := by
    intro n hn
    rw [mem_centralizer_iff]
    intro p hp
    have h1 : n * p * n⁻¹ ∈ (P : Subgroup (Jbar O h4)) := (mem_normalizer_iff.1 hn p).1 hp
    have h2 : (((n * p * n⁻¹ : Jbar O h4) : Cbar O h4)) ∈ kbar O h4 := hPK h1
    have h3 : ((p : Jbar O h4) : Cbar O h4) ∈ kbar O h4 := hPK hp
    have h4' := eq_of_isConj_of_mem_kbar O h4 hm h3 h2 (isConj_iff.2 ⟨(n : Cbar O h4), rfl⟩)
    apply Subtype.ext
    change (p : Cbar O h4) * n = n * p
    calc (p : Cbar O h4) * n = ((n * p * n⁻¹ : Jbar O h4) : Cbar O h4) * n := by rw [← h4']
      _ = n * p := by simp
  set f := MonoidHom.transferSylow P hP with hf
  have hodd_ker : ∀ k : Jbar O h4, Odd (orderOf k) → f k = 1 := by
    intro k hk
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 P.isPGroup') (f k)
    have h1 : orderOf (f k) ∣ orderOf k := orderOf_map_dvd f k
    rw [hj] at h1
    have h2 : j = 0 := by
      by_contra hj0
      have : 2 ∣ orderOf k := (dvd_pow_self 2 hj0).trans h1
      exact (Nat.not_even_iff_odd.2 hk) (even_iff_two_dvd.2 this)
    rw [h2, pow_zero] at hj
    exact orderOf_eq_one_iff.1 hj
  have hkodd : Odd (Nat.card f.ker) := by
    have := MonoidHom.not_dvd_card_ker_transferSylow P hP
    rwa [← even_iff_two_dvd, Nat.not_even_iff_odd] at this
  set K' : Subgroup (Cbar O h4) := f.ker.map (Jbar O h4).subtype with hK'
  have hJN : ∀ g : Cbar O h4, ∀ x ∈ Jbar O h4, g * x * g⁻¹ ∈ Jbar O h4 := by
    intro g x hx
    have hg : g ∈ normalizer (L0bar O h4 : Set (Cbar O h4)) := by
      rw [normalizer_eq_top_iff.2 hN]; exact mem_top g
    exact (mem_normalizer_iff.1 (normalizer_le_normalizer_centralizer' _ hg) x).1 hx
  have hK'n : K'.Normal := by
    constructor
    rintro _ ⟨k, hk, rfl⟩ g
    refine ⟨⟨g * k * g⁻¹, hJN g k k.2⟩, ?_, rfl⟩
    apply hodd_ker
    have h1 : orderOf (⟨g * k * g⁻¹, hJN g k k.2⟩ : Jbar O h4) = orderOf k := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe k]
      exact orderOf_conj' g (k : Cbar O h4)
    rw [h1]
    exact (hkodd).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hk)
  have hK'odd : Odd (Nat.card K') := by
    rw [hK', Subgroup.card_map_of_injective (Jbar O h4).subtype_injective]
    exact hkodd
  have hK'bot : K' = ⊥ := by
    rw [eq_bot_iff, ← hO]
    exact le_sSup ⟨hK'n, hK'odd⟩
  have hker : f.ker = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    have : (k : Cbar O h4) ∈ K' := ⟨k, hk, rfl⟩
    rw [hK'bot, mem_bot] at this
    exact Subtype.ext this
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 hker
  have h1 : Nat.card (Jbar O h4) ≤ Nat.card (P : Subgroup (Jbar O h4)) :=
    Nat.card_le_card_of_injective f hinj
  have h2 : Nat.card (P : Subgroup (Jbar O h4)) ≤
      Nat.card ((kbar O h4).subgroupOf (Jbar O h4)) := Subgroup.card_le_of_le hPK
  have h3 : Nat.card ((kbar O h4).subgroupOf (Jbar O h4)) = Nat.card (kbar O h4) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (kbar_le_centralizer O h4)).toEquiv
  have h4' := card_kbar_le O h4
  omega

theorem card_centralizer_wA_le (hR2 : RankTwoAlternatingStandard) (hNE : L0Normal O (kleinR h4))
    (hNy : L0Normal O (cycR h4))
    (hKC : CFSG.SectionRank.IsKGroupCat (Cbar O h4)) (hO : CFSG.oddCore (Cbar O h4) = ⊥)
    (hm : 10 ≤ m) :
    Nat.card (centralizer ({wA O h4} : Set G)) ≤ 8 * (m - 1).factorial := by
  have hN := normal_L0bar O h4 hR2 hNE hNy hKC hO hm
  have hJ := card_Jbar_le O h4 (by omega) hN hO
  have h1 := card_le_of_le_normalizer (L0barEquiv O h4 (by omega)) (by omega)
    (H := (⊤ : Subgroup (Cbar O h4))) (by rw [normalizer_eq_top_iff.2 hN])
  have h2 : Nat.card ↥((⊤ : Subgroup (Cbar O h4)) ⊓ centralizer (L0bar O h4 : Set (Cbar O h4))) =
      Nat.card (Jbar O h4) := by rw [top_inf_eq]
  rw [h2, Subgroup.card_top] at h1
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (zpowers (selfC (wA O h4)))
  have h4' : Nat.card (zpowers (selfC (wA O h4))) = 2 := by
    rw [Nat.card_zpowers]
    unfold selfC
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact wA_mul_self O h4) (wA_ne_one O h4)
  rw [h4'] at h3
  have h5 : Nat.card (Cbar O h4) ≤ 4 * (m - 1).factorial :=
    h1.trans (Nat.mul_le_mul_right _ hJ)
  change Nat.card (centralizer ({wA O h4} : Set G)) =
    Nat.card (Cbar O h4) * 2 at h3
  omega

end Final

section Main

theorem centDoubleAt_of_l0 (hR2 : RankTwoAlternatingStandard) {m : ℕ} (hm : 10 ≤ m)
    (hL0 : ∀ (G : Type) [Group G] [Finite G] (z : G) (O : OverData G z m) (h4 : 4 ≤ m + 3),
      (∀ H : Subgroup G, H ≠ ⊤ → CFSG.SectionRank.IsKGroupCat H) →
      (∀ x : G, x ≠ 1 → centralizer ({x} : Set G) ≠ ⊤) →
      L0Normal O (kleinR h4) ∧ L0Normal O (cycR h4)) :
    ShapeTwoCentDoubleAt (m + 1) := by
  intro G _ _ L Q z u h d T e S₀ hS₀ hkn hII w hw hct
  classical
  obtain ⟨u₀, T₀, htw⟩ := exists_untwisted h d T e hS₀ hkn hII
  set D := nearData_of_untwisted h d T₀ e hS₀ hkn hII htw with hD
  obtain ⟨M, eM, hC, hz, hcompat, hconj⟩ := exists_symmetric_overgroup_near (by omega : 10 ≤ m) D
  set O : OverData G z m := ⟨D, M, eM, hC, hz, hcompat, hconj⟩ with hO
  have h4 : 4 ≤ m + 3 := by omega
  set σ : Perm (Fin (m + 1)) := ((e ⟨w, hw⟩ : alternatingGroup (Fin (m + 1))) : Perm (Fin (m + 1)))
    with hσ
  have hσA : σ ∈ alternatingGroup (Fin (m + 1)) := (e ⟨w, hw⟩).2
  obtain ⟨hw', hew⟩ := swapIota_mem_of_even h d T₀ e hσA
  have hwι : (swapIota h d T₀ e σ : G) = w := by
    have h1 : e ⟨swapIota h d T₀ e σ, hw'⟩ = e ⟨w, hw⟩ := Subtype.ext hew
    exact congrArg Subtype.val (e.injective h1)
  have hwφ : O.φ (inclPerm m σ) = w := by
    rw [OverData.φ_apply]
    change (eM (inclPerm m σ) : G) = w
    rw [hcompat]
    exact hwι
  have hct1 : (inclPerm m σ).cycleType = {2, 2} := by
    rw [inclPerm, Perm.extendDomainHom_apply, Perm.cycleType_extendDomain]
    exact hct
  have hct2 : (emb4 h4 kA4).cycleType = {2, 2} := by
    rw [emb4, Perm.extendDomainHom_apply, Perm.cycleType_extendDomain]
    exact cycleType_mul_swap ⟨0, 1, by decide, rfl⟩ ⟨2, 3, by decide, rfl⟩ (by decide) (by decide)
  obtain ⟨γ, hγ⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 (hct2.trans hct1.symm))
  have hw0 : w = O.φ γ * wA O h4 * (O.φ γ)⁻¹ := by
    rw [← hwφ, ← hγ, map_mul, map_mul, map_inv]
    rfl
  rw [hw0, nat_card_centralizer_conj]
  have hw1 : wA O h4 ≠ 1 := wA_ne_one O h4
  have hw2 : orderOf (wA O h4) = 2 := orderOf_eq_prime (by rw [pow_two]; exact wA_mul_self O h4) hw1
  obtain ⟨hNE, hNy⟩ := hL0 G z O h4 (isKGroupCat_of_kProper h.std.kProper)
    (fun x hx => centralizer_singleton_ne_top h hx)
  have := card_centralizer_wA_le O h4 hR2 hNE hNy (isKGroupCat_twoSec h hw1)
    (oddCore_twoSec_eq_bot h hw2) hm
  rwa [show m + 1 - 2 = m - 1 by omega]

theorem isKGroupCat_secP {G : Type} [Group G] [Finite G] {z : G} {m : ℕ} (O : OverData G z m)
    (h4 : 4 ≤ m + 3) (hK : ∀ H : Subgroup G, H ≠ ⊤ → CFSG.SectionRank.IsKGroupCat H)
    (hne : ∀ x : G, x ≠ 1 → centralizer ({x} : Set G) ≠ ⊤) :
    CFSG.SectionRank.IsKGroupCat ↥(centralizer (secP O (kleinR h4) : Set G)) ∧
      CFSG.SectionRank.IsKGroupCat ↥(centralizer (secP O (cycR h4) : Set G)) := by
  have hne' := hne _ (wA_ne_one O h4)
  refine ⟨hK _ (fun htop => hne' ?_), hK _ (fun htop => hne' ?_)⟩
  · rw [eq_top_iff, ← htop]
    exact centralizer_le (Set.singleton_subset_iff.2 ⟨kleinA h4, kleinA_mem_kleinR h4, rfl⟩)
  · rw [eq_top_iff, ← htop]
    exact centralizer_le (Set.singleton_subset_iff.2 ⟨kleinA h4, kleinA_mem_cycR h4, rfl⟩)

theorem shapeTwoCentDoubleAt_of_ne (htri : ExactShapeTrichotomy) (hR2 : RankTwoAlternatingStandard)
    {n : ℕ} (hn : 13 ≤ n) (h14 : n ≠ 14) : ShapeTwoCentDoubleAt n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine centDoubleAt_of_l0 hR2 (by omega) ?_
  intro G _ _ z O h4 hK hne
  obtain ⟨hKE, hKy⟩ := isKGroupCat_secP O h4 hK hne
  exact ⟨l0Normal_of_not_hn O (secR_klein (by omega)) htri hKE (by omega) (fun h => by omega),
    l0Normal_of_not_hn O (secR_cyc (by omega)) htri hKy (by omega) (fun h => by omega)⟩

theorem shapeTwoCaseIIClassification_of_rankTwo (htri : ExactShapeTrichotomy)
    (hR2 : RankTwoAlternatingStandard) (h14 : ShapeTwoCentDoubleAt 14) :
    ShapeTwoCaseIIClassification := by
  intro G _ _ L Q n z u h d T e hn S₀ hS₀ hII
  have h47 : ShapeTwoCentDoubleAt n := by
    rcases eq_or_ne n 14 with rfl | hne
    · exact h14
    · exact shapeTwoCentDoubleAt_of_ne htri hR2 (by omega) hne
  exact caseII_of_centDoubleAt h47 h d T e (by omega) (Or.inl hS₀) (by omega) hII

end Main

end CFSG.OddStandard.AltStdSec
