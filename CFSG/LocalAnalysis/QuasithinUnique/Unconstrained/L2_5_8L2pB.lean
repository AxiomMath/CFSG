module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L2p
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Sylow
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFacts

public section

namespace CFSG.QuasithinUnique.Unc25Small

open CFSG.Open CFSG.Quasithin CFSG.GorensteinWalter
open scoped MatrixGroups

section PSL2

variable {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]

theorem psl2_four_fixes (H : L2pHyp K p) :
    ∀ P : Subgroup PSL(2, K), IsSylowTwoOf P ⊤ → ∀ F : Subgroup PSL(2, K), F ≤ P →
      IsFourSubgroup F → ∀ φ : MulAut PSL(2, K), (∀ f ∈ F, φ f = f) →
        ∀ y : PSL(2, K), φ y ∈ P ↔ y ∈ P := by
  intro P hP F hFP hF φ hφ y
  obtain ⟨g0, hg0F, hg0⟩ := psl2_aut_fix_four H (isKleinFour_of_isFourSubgroup hF) hφ
  have hg0P : g0 ∈ P := hFP hg0F
  rw [hg0]
  simp only [MulAut.conj_apply]
  constructor
  · intro h
    have := P.mul_mem (P.mul_mem (P.inv_mem hg0P) h) hg0P
    simpa [mul_assoc] using this
  · intro h
    exact P.mul_mem (P.mul_mem hg0P h) (P.inv_mem hg0P)

theorem psl2_fixPointwiseInner
    (H : L2pHyp K p) : FixPointwiseInner PSL(2, K) := by
  intro P hP α hα
  obtain ⟨S, hSP⟩ := Unc25K1.exists_sylow_of_isSylowTwoOf_top hP
  obtain ⟨t, s, htS, hsS, ht2, hs2, ht1, hs1, hts, hcomm⟩ :=
    Unc25K1.exists_commuting_involutions_of_sylow H.odd S
  rw [hSP] at htS hsS
  have hc : Commute t s := hcomm
  have hV : IsKleinFour (kleinFourOfCommutingInvolutions t s ht2 hs2 hc) :=
    isKleinFour_kleinFourOfCommutingInvolutions t s ht2 hs2 ht1 hs1 hts hc
  have hVfix : ∀ v ∈ kleinFourOfCommutingInvolutions t s ht2 hs2 hc, α v = v := by
    intro v hv
    apply hα
    rcases (Unc25K1.mem_kleinFourOfCommutingInvolutions_iff ht2 hs2 hc v).mp hv with
      rfl | rfl | rfl | rfl
    · exact P.mul_mem htS hsS
    · exact htS
    · exact hsS
    · exact P.one_mem
  obtain ⟨g0, -, hg0⟩ := psl2_aut_fix_four H hV hVfix
  exact ⟨g0, hg0.symm⟩

theorem eight_dvd_normalizer (H : L2pHyp K p) {F : Subgroup PSL(2, K)} (hF : IsFourSubgroup F) :
    8 ∣ Nat.card (Subgroup.normalizer (F : Set PSL(2, K))) := by
  refine eight_dvd_normalizer_of_sylow (fun P hP => ?_) hF
  obtain ⟨m, hm2, ⟨eP⟩⟩ := psl2_sylow_dihedral H P hP
  rw [Nat.card_congr eP.toEquiv, DihedralGroup.nat_card]
  have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  omega

theorem three_dvd_normalizer (H : L2pHyp K p) {F : Subgroup PSL(2, K)} (hF : IsFourSubgroup F) :
    3 ∣ Nat.card (Subgroup.normalizer (F : Set PSL(2, K))) := by
  obtain ⟨t, s, ht, hs, hc, ht1, hs1, hts, hFeq⟩ := exists_kleinFour_gens hF
  have h2 : (2 : K) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K
      (by rw [H.hK]; exact (Fact.out : p.Prime).odd_of_ne_two (by have := H.hp7; omega))
  obtain ⟨w, hw1, hw2⟩ := Unc25K1.exists_psl2_cycle h2 ht1 hs1 hts ht hs hc
  obtain ⟨hwN, hw3⟩ := Unc25K1.three_dvd_orderOf_of_cycle ht hs hc hts hw1 hw2
  rw [← hFeq] at hwN
  have h := orderOf_dvd_natCard (⟨w, hwN⟩ : Subgroup.normalizer (F : Set PSL(2, K)))
  rw [Subgroup.orderOf_mk] at h
  exact hw3.trans h

theorem psl2_four_normalizer
    (H : L2pHyp K p) :
    ∀ F : Subgroup PSL(2, K), IsFourSubgroup F →
      Nonempty (↥(Subgroup.normalizer (F : Set PSL(2, K))) ≃* Equiv.Perm (Fin 4)) := fun _ hF =>
  four_normalizer_of_centralizer hF (psl2_centralizer_kleinFour H (isKleinFour_of_isFourSubgroup hF))
    (three_dvd_normalizer H hF) (eight_dvd_normalizer H hF)

theorem psl2_sylow_normalizer (H : L2pHyp K p) :
    ∀ P : Subgroup PSL(2, K), IsSylowTwoOf P ⊤ →
      Subgroup.normalizer (P : Set PSL(2, K)) ≤ P := by
  intro P hP
  obtain ⟨m, hm2, ⟨eP⟩⟩ := psl2_sylow_dihedral H P hP
  have hm4 : 4 ≤ 2 ^ m :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have hZ : Nat.card (Subgroup.center ↥P) = 2 :=
    (Nat.card_congr (Subgroup.centerCongr eP).toEquiv).trans (card_center_dihedral _ hm4 ⟨m, rfl⟩)
  obtain ⟨y, hy1, hyu⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center ↥P)).mp hZ
  set u : PSL(2, K) := (((y : ↥P)) : PSL(2, K)) with hu
  have hu1 : u ≠ 1 := fun h => hy1 (Subtype.ext (Subtype.ext h))
  have huP : u ∈ P := (y : ↥P).2
  have hucomm : ∀ q ∈ P, q * u = u * q := by
    intro q hq
    have := Subgroup.mem_center_iff.mp y.2 ⟨q, hq⟩
    exact congrArg Subtype.val this
  have hu2 : u * u = 1 := by
    by_contra hne
    have hyy : y * y ≠ 1 := fun h => hne (congrArg (fun z : ↥(Subgroup.center ↥P) =>
      ((z : ↥P) : PSL(2, K))) h)
    have h1 : y * y = y := hyu _ hyy
    apply hy1
    exact mul_left_cancel (h1.trans (mul_one y).symm)
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  have hC2 : IsPGroup 2 (Subgroup.centralizer ({u} : Set PSL(2, K))) :=
    Unc25K1.psl2_cent_two H.hp7 H.hK H.hpow u hord
  have hPC : P ≤ Subgroup.centralizer ({u} : Set PSL(2, K)) := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hucomm q hq)
  obtain ⟨P'', hCP'', hP''⟩ := exists_isSylowTwoOf_of_le (le_top) hC2
  have hcard : Nat.card (Subgroup.centralizer ({u} : Set PSL(2, K))) ≤ Nat.card P := by
    calc Nat.card (Subgroup.centralizer ({u} : Set PSL(2, K))) ≤ Nat.card P'' :=
          Subgroup.card_le_of_le hCP''
      _ = Nat.card P := hP''.card_eq.trans hP.card_eq.symm
  have hPeq : P = Subgroup.centralizer ({u} : Set PSL(2, K)) :=
    Subgroup.eq_of_le_of_card_ge hPC hcard
  intro n hn
  have hn' := Subgroup.mem_normalizer_iff.mp hn
  have hv : n * u * n⁻¹ ∈ P := (hn' u).mp huP
  have hconj : ∀ q ∈ P, n⁻¹ * q * n ∈ P := fun q hq =>
    (hn' (n⁻¹ * q * n)).mpr (by simpa [mul_assoc] using hq)
  have hvc : ∀ q ∈ P, q * (n * u * n⁻¹) = (n * u * n⁻¹) * q := by
    intro q hq
    have h1 := hucomm _ (hconj q hq)
    calc q * (n * u * n⁻¹) = n * ((n⁻¹ * q * n) * u) * n⁻¹ := by group
      _ = n * (u * (n⁻¹ * q * n)) * n⁻¹ := by rw [h1]
      _ = (n * u * n⁻¹) * q := by group
  let c : ↥(Subgroup.center ↥P) :=
    ⟨⟨n * u * n⁻¹, hv⟩, Subgroup.mem_center_iff.mpr fun q => Subtype.ext (hvc q q.2)⟩
  have hc1 : c ≠ 1 := by
    intro h
    have h1 := congrArg (fun z : ↥(Subgroup.center ↥P) => ((z : ↥P) : PSL(2, K))) h
    apply hu1
    have h2 : n * u * n⁻¹ = 1 := h1
    calc u = n⁻¹ * (n * u * n⁻¹) * n := by group
      _ = 1 := by rw [h2]; group
  have hcy : c = y := hyu c hc1
  have hvu : n * u * n⁻¹ = u := congrArg (fun z : ↥(Subgroup.center ↥P) =>
    ((z : ↥P) : PSL(2, K))) hcy
  have hnC : n ∈ Subgroup.centralizer ({u} : Set PSL(2, K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc n * u = n * u * n⁻¹ * n := by group
      _ = u * n := by rw [hvu]
  rw [hPeq]
  exact hnC

theorem psl2_smallListFacts
    (H : L2pHyp K p) : SmallListFacts PSL(2, K) :=
  { simple := Unc25K1.psl2_simple H.hp7 H.hK
    out_two := psl2_out_two H
    sylow_shape := psl2_sylow_shape H
    sylow_normalizer := psl2_sylow_normalizer H
    four_normalizer := psl2_four_normalizer H
    four_fixes := psl2_four_fixes H }

end PSL2

theorem l2p_facts
    {p : ℕ} (hFM : IsFermatOrMersenne p) (h7 : 7 < p) (X : Type) [Group X]
    [Finite X] (hmodel : StatedClassicalModel X .PSL 2 p 1) :
    SmallListFacts X ∧ FixPointwiseInner X := by
  have hp : p.Prime := hFM.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, _, e, hcard, -, -⟩ := CFSG.QuasithinUnique.K1.psl2_model_data (by omega) hmodel
  have hK : Nat.card K = p := by rw [Nat.card_eq_fintype_card, hcard, pow_one]
  have H : L2pHyp K p := ⟨by omega, hK, Unc25K1.fermat_or_mersenne_pow hFM h7⟩
  exact ⟨SmallListFacts.of_mulEquiv e (psl2_smallListFacts H),
    FixPointwiseInner.of_mulEquiv e (psl2_fixPointwiseInner H)⟩

theorem l32_facts
    (X : Type) [Group X] [Finite X] (h : StatedClassicalModel X .PSL 3 2 1) :
    SmallListFacts X ∧ FixPointwiseInner X := by
  obtain ⟨F, _, _, _, e, hq7, -, -⟩ := Unc25K1.exists_psl2_seven h
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hK : Nat.card F = 7 := by rw [Nat.card_eq_fintype_card, hq7]
  have H : L2pHyp F 7 := ⟨le_rfl, hK, Or.inr ⟨by norm_num, 3, by norm_num⟩⟩
  exact ⟨SmallListFacts.of_mulEquiv e (psl2_smallListFacts H),
    FixPointwiseInner.of_mulEquiv e (psl2_fixPointwiseInner H)⟩

end CFSG.QuasithinUnique.Unc25Small
