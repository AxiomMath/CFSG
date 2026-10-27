module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.QuasithinUnique.Ch1
open Equiv Equiv.Perm

section Tools

theorem commutator_le_of_card_eq_two_mul {G : Type} [Group G] [Finite G] {K R : Subgroup G}
    (hKR : K ≤ R) (h : Nat.card R = 2 * Nat.card K) : ⁅R, R⁆ ≤ K := by
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hidx : (K.subgroupOf R).index = 2 := by
    have := Subgroup.card_mul_index (K.subgroupOf R)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKR).toEquiv, h] at this
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [this, mul_comm])
  have := Subgroup.normal_of_index_eq_two hidx
  have hcard2 : Nat.card (↥R ⧸ K.subgroupOf R) = 2 := hidx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (↥R ⧸ K.subgroupOf R) := isCyclic_of_prime_card hcard2
  let : CommGroup (↥R ⧸ K.subgroupOf R) := IsCyclic.commGroup
  have hle : commutator ↥R ≤ K.subgroupOf R := by
    have := Abelianization.commutator_subset_ker (QuotientGroup.mk' (K.subgroupOf R))
    rwa [QuotientGroup.ker_mk'] at this
  have h1 : ⁅R, R⁆ = (commutator ↥R).map R.subtype := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [h1]
  calc (commutator ↥R).map R.subtype ≤ (K.subgroupOf R).map R.subtype := Subgroup.map_mono hle
    _ = K := Subgroup.map_subgroupOf_eq_of_le hKR

theorem isA6_of_card_dvd {G : Type} [Group G] {K : Subgroup G} (hK : IsKType K) {N : ℕ}
    (hN : 0 < N) (hdvd : Nat.card ↥K ∣ N) (hlt : N < 2448) (h168 : ¬ 168 ∣ N) : IsA6 K := by
  rcases hK with hK | hK | hK
  · exfalso
    have := hK.card_ge
    have := Nat.le_of_dvd hN hdvd
    omega
  · exfalso
    rw [hK.card_eq] at hdvd
    exact h168 hdvd
  · exact hK

end Tools

section L4Two

open Ident

variable {G : Type} [Group G] [Finite G]

theorem tabIdentFor_l4Two
    : TabIdentFor @FamL4Two := by
  intro G _ _ X K t hs hX
  obtain ⟨hsimple, hmodel⟩ := hX
  obtain ⟨φ0⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff
    ↥X).mp (Or.inl ⟨by decide, hmodel⟩)
  have hc : Subgroup.center ↥X = ⊥ := hs.center_eq_bot_of_simple hsimple
  let φ : (↥X ⧸ Subgroup.center ↥X) ≃* alternatingGroup (Fin 8) :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans φ0
  have hφ : ∀ y : ↥X, φ (QuotientGroup.mk y) = φ0 y := fun y => rfl
  obtain ⟨σ, hσ⟩ := hs.exists_perm (n := 8) (Or.inr (by norm_num)) φ
  have hsq : σ * σ = 1 := hs.perm_sq (by norm_num) φ hσ
  have hne : σ ≠ 1 := hs.perm_ne_one φ hσ
  obtain ⟨k, hk1, hcyc⟩ := involution_cycleType hsq hne
  have hk4 : k ≤ 4 := by
    have := two_mul_le_of_cycleType hcyc
    omega
  have hcard := card_centralizer_involution hk1 hcyc
  have hKt : K ≤ Subgroup.centralizer ({t} : Set G) := hs.K_le_cent
  have hdvd := hs.card_dvd_cent φ hσ hs.K_le hKt (hs.psiOf_injective_K hs.ktype φ)
  have hN : (k = 1 ∧ Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 8)))) = 1440) ∨
      (k = 2 ∧ Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 8)))) = 192) ∨
      (k = 3 ∧ Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 8)))) = 96) ∨
      (k = 4 ∧ Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 8)))) = 384) := by
    interval_cases k <;> simp [hcard, Nat.factorial]
  have hA6 : IsA6 K := isA6_of_card_dvd hs.ktype Nat.card_pos hdvd (by omega) (by omega)
  have h360 : 360 ∣ Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 8)))) := by
    rw [← hA6.card_eq]
    exact hdvd
  have hk : k = 1 := by omega
  subst hk
  have hC : Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 8)))) = 1440 := by omega
  have hodd : σ ∉ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup, sign_involution hcyc]
    decide
  have hsw : σ.IsSwap := Equiv.Perm.isSwap_iff_cycleType.mpr (by simpa using hcyc)
  obtain ⟨a, b, hab, hσab⟩ := hsw
  have hKeq : K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)) := by
    set C := X ⊓ Subgroup.centralizer ({t} : Set G) with hCdef
    set R := CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf C with hRdef
    have hKR : K ≤ R := le_perfectResidualOf hs.perfect_K hs.comp.1
    have hRC : R ≤ C := perfectResidualOf_le C
    have hRperf : ⁅R, R⁆ = R := perfectResidualOf_perfect C
    have hRX : R ≤ X := hRC.trans inf_le_left
    have hRt : R ≤ Subgroup.centralizer ({t} : Set G) := hRC.trans inf_le_right
    have hR720 := hs.two_mul_card_le φ hσ hodd hRX hRt
      (psiOf_injective_of_center_eq_bot hc φ hRX)
    rw [hC] at hR720
    have hK360 : Nat.card ↥K = 360 := hA6.card_eq
    have hdvdR : Nat.card ↥K ∣ Nat.card ↥R := Subgroup.card_dvd_of_le hKR
    obtain ⟨m, hm⟩ := hdvdR
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · exfalso
        have : 0 < Nat.card ↥R := Nat.card_pos
        rw [hm, h0, mul_zero] at this
        exact lt_irrefl _ this
      · exact h0
    have hm2 : m ≤ 2 := by
      rw [hK360] at hm
      omega
    have hm1 : m = 1 := by
      by_contra hne1
      have hm2' : m = 2 := by omega
      subst hm2'
      have hRcard : Nat.card ↥R = 2 * Nat.card ↥K := by rw [hm, hK360]
      have hle := commutator_le_of_card_eq_two_mul hKR hRcard
      rw [hRperf] at hle
      have : Nat.card ↥R ≤ Nat.card ↥K := Subgroup.card_le_of_le hle
      rw [hRcard] at this
      omega
    subst hm1
    refine Subgroup.eq_of_le_of_card_ge hKR ?_
    rw [hm, mul_one]
  have hind : InducesAut t X φ0 (MulAut.conjNormal (Equiv.swap a b)) := by
    refine ⟨hs.tN, fun y y' hy' => ?_⟩
    have hy'eq : y' = hs.conjAut y := Subtype.ext hy'
    apply Subtype.ext
    have h1 := hσ y
    rw [hφ, hφ] at h1
    rw [hy'eq, h1, hσab]
    simp [MulAut.conjNormal_apply]
  refine ⟨?_, hKeq, fun hbig => ?_, fun hl => ?_, fun _ => ?_⟩
  · rw [hc]
    exact (by simp [IsPGroup] : IsPGroup 2 (⊥ : Subgroup ↥X))
  · have h1 := hbig.card_ge
    rw [hA6.card_eq] at h1
    omega
  · have h1 := hl.card_eq
    rw [hA6.card_eq] at h1
    omega
  · exact Or.inr (Or.inr (Or.inr ⟨hA6, φ0, a, b, hab, hind⟩))

end L4Two

end CFSG.QuasithinUnique.Id2519
