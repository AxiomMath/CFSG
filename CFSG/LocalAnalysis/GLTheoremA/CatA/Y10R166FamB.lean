module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Cases
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SpBlocks2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Mult
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2EUp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TablesHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Build

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.SeitzReduction.SymplecticPilot CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped MatrixGroups

theorem hasLabel_statedSp_symplectic {F : Type} [Field F] [Finite F] [CharP F 2]
    (N n : ℕ) (hcard : Nat.card F = 2 ^ n) (hN : 2 ≤ N) (hn : 2 ≤ n) :
    HasLabel (StatedSp N F) (· = ⟨.B, N, n⟩) := by
  have hF4 : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hQ : CFSG.IsQuasisimple (StatedSp N F) :=
    CFSG.LieType.Universal.Symplectic.isQuasisimple N F (by omega) (Or.inl (Or.inr hF4))
  have hbot : (StatedScalars (Fin N ⊕ Fin N) F).subgroupOf (StatedSp N F) = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot
  have hZ : Subgroup.center (StatedSp N F) = ⊥ := center_statedSp_eq_bot N
  have hbase : StatedClassicalModel (StatedProj (StatedSp N F)) .PSp N 2 n :=
    CFSG.StandardType.statedClassicalModel_symplectic N n hcard
      ⟨Nat.prime_two, by omega, hN, by
        rintro h
        have h2 : 2 ^ n = 2 := (Prod.ext_iff.1 h).2
        have h4 : 4 ≤ 2 ^ n := hcard ▸ hF4
        omega⟩
  have hquot : StatedClassicalModel
      (StatedSp N F ⧸ Subgroup.center (StatedSp N F)) .PSp N 2 n :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (hbot.trans hZ.symm)) hbase
  exact hasLabel_of_statedClassicalModel_PSp hQ hquot

theorem hasLabel_complSp_symplectic {F : Type} [Field F] [Finite F] [CharP F 2]
    {m n : ℕ} (hcard : Nat.card F = 2 ^ n) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (k : Fin (m + 1)) :
    HasLabel (complSp F k) (· = ⟨.B, m, n⟩) :=
  (hasLabel_congr (complSpEquiv (K := F) k) (fun l => l = ⟨.B, m, n⟩)).1
    (hasLabel_statedSp_symplectic m n hcard hm hn)


section Certs


theorem evenRank_statedSp_symplectic {F : Type} [Field F] [Finite F] [CharP F 2]
    (N n : ℕ) (hcard : Nat.card F = 2 ^ n) (hN : 2 ≤ N) (hn : 2 ≤ n) :
    evenRank (StatedSp N F) = N := by
  have hlab := hasLabel_statedSp_symplectic N n hcard hN hn
  have hK : Rk2IsLabel (StatedSp N F) ⟨.B, N, n⟩ := hlab
  have hlow : N ≤ evenRank (StatedSp N F) :=
    (rk2Lower_holds (StatedSp N F) ⟨.B, N, n⟩ hK).bcd_ge (Or.inl rfl) hn
  have hup : evenRank (StatedSp N F) ≤ N :=
    (rk2_eUpAt_of_tables rk2KRank rk2Upper_holds (K := StatedSp N F)
      (lab := ⟨.B, N, n⟩) hK).bd (Or.inl rfl) hn
  exact le_antisymm hup hlow

end Certs


section Certs2



theorem concl166S_statedSp {F : Type} [Field F] [Finite F] [CharP F 2]
    {p m n q : ℕ} {ζ : Fˣ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m) (hn : 2 ≤ n)
    (hcard : Nat.card F = 2 ^ n) (hpvd : p ∣ 2 ^ n + 1)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqdvd : q ∣ Nat.card F - 1) (hζ : orderOf ζ = q) :
    ∃ (B' : Subgroup (StatedSp (m + 1) F)) (x' : StatedSp (m + 1) F)
      (J : Subgroup (StatedSp (m + 1) F)), Concl166S (StatedSp (m + 1) F) p q B' x' J := by
  classical
  have hF4 : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have heven : evenRank (StatedSp (m + 1) F) = m + 1 :=
    evenRank_statedSp_symplectic (m + 1) n hcard (by omega) hn
  obtain ⟨E, hEB, hE, hEcard, hxE, he3layer⟩ :=
    exists_e3_statedSp (F := F) (m := m) (n := n) (q := q) (ζ := ζ)
      hm hn hcard hq hq2 hqdvd hζ
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζ
    exact hq.ne_one hζ.symm
  have hζ2 : ζ * ζ ≠ 1 := by
    intro h
    have h2 : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    have hpq : q ∣ 2 := hζ ▸ h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hpq)
  have hx1 : rootTorusHom F (m + 1) 0 ζ ≠ 1 := fun h =>
    hζ1 (rootTorusHom_injective 0 (by rw [h, map_one]))
  have hxmem : rootTorusHom F (m + 1) 0 ζ ∈ symplecticQTorus (F := F) (ℓ := m + 1) q := by
    refine (mem_symplecticQTorus (F := F) (ℓ := m + 1)).2
      ⟨Pi.mulSingle 0 ζ, ?_, rootTorusHom_apply ..⟩
    intro i
    by_cases hi : i = 0
    · subst hi
      rw [Pi.mulSingle_eq_same, ← hζ]
      exact pow_orderOf_eq_one ζ
    · rw [Pi.mulSingle_eq_of_ne hi]
      simp
  have hrankB : Nat.card (symplecticQTorus (F := F) (ℓ := m + 1) q) =
      q ^ evenRank (StatedSp (m + 1) F) := by
    rw [card_symplecticQTorus hq hqdvd, heven]
  have hJlab : HasLabel ↥(complSp F (0 : Fin (m + 1))) (· = ⟨.B, m, n⟩) :=
    hasLabel_complSp_symplectic hcard (by omega) hn 0
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hsymp := symplectic_mult (J := ↥(complSp F (0 : Fin (m + 1))))
    (m := m) (n := n) (by omega) hn hJlab hGA
  have hmul_arith : m + 1 + 2 ≤ n * (m * (m + 1) / 2) := by
    have h1 : m + 1 ≤ m * (m + 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      nlinarith
    have h2 : 2 * (m + 1) ≤ n * (m * (m + 1) / 2) :=
      (Nat.mul_le_mul_left 2 h1).trans (Nat.mul_le_mul_right _ hn)
    omega
  have hm2 : evenRank (StatedSp (m + 1) F) + 2 ≤ twoRank ↥(complSp F (0 : Fin (m + 1))) := by
    rw [heven]
    exact hmul_arith.trans hsymp.2.2.1
  have hshape : ∀ lab : GLALabel, HasLabel (StatedSp (m + 1) F) (fun l : GLALabel => l = lab) →
      JShape lab (3 ∣ Nat.card (Subgroup.center (StatedSp (m + 1) F))) ⟨.B, m, n⟩ := by
    intro lab hlab
    have hlabK : HasLabel (StatedSp (m + 1) F) (· = ⟨.B, m + 1, n⟩) :=
      hasLabel_statedSp_symplectic (m + 1) n hcard (by omega) hn
    have h4 : 4 ≤ evenRank (StatedSp (m + 1) F) := by rw [heven]; omega
    rcases label_eq_or_BC h4 hlab hlabK with heq | ⟨ht1, -, hr, hnn⟩
    · subst heq
      exact ⟨rfl, Or.inl ⟨Or.inl rfl, rfl, rfl⟩⟩
    · refine ⟨hnn.symm, Or.inl ⟨ht1, rfl, hr.symm⟩⟩
  have hpdvd : p ∣ 2 ^ (2 * n) - 1 := by
    have hfac : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      rw [show 2 * n = n * 2 by omega, pow_mul, show (1 : ℕ) = 1 ^ 2 by norm_num,
        Nat.sq_sub_sq]
      ring
    rw [hfac]
    exact dvd_mul_of_dvd_left hpvd _
  have hqdvd2 : q ∣ 2 ^ (2 * n) - 1 := by
    have hq' : q ∣ 2 ^ n - 1 := by rwa [hcard] at hqdvd
    have hfac : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      rw [show 2 * n = n * 2 by omega, pow_mul, show (1 : ℕ) = 1 ^ 2 by norm_num,
        Nat.sq_sub_sq]
      ring
    rw [hfac]
    exact dvd_mul_of_dvd_right hq' _
  have hpq : p ≠ q := by
    intro hpq
    have hq' : q ∣ 2 ^ n - 1 := by rwa [hcard] at hqdvd
    have hp' : q ∣ 2 ^ n + 1 := hpq ▸ hpvd
    have hsub : q ∣ (2 ^ n + 1) - (2 ^ n - 1) :=
      Nat.dvd_sub hp' hq'
    have h2 : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by omega
    rw [h2] at hsub
    exact hp2 (hpq ▸ (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hsub)
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hdvd : p * q ∣ Nat.card
      (↥(complSp F (0 : Fin (m + 1))) ⧸ Subgroup.center ↥(complSp F (0 : Fin (m + 1)))) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop
      (hsymp.2.2.2 p hp hp2 hpdvd) (hsymp.2.2.2 q hq hq2 hqdvd2)
  have hJx : complSp F (0 : Fin (m + 1)) ≤
      Subgroup.centralizer ({rootTorusHom F (m + 1) 0 ζ} : Set (StatedSp (m + 1) F)) :=
    fun y hy => Subgroup.mem_centralizer_singleton_iff.2
      ((Subgroup.mem_centralizer_iff.1 (complSp_le_centralizer_rootTorusSp 0 hy)
        (rootTorusHom F (m + 1) 0 ζ) (rootTorusHom_mem_rootTorusSp 0 ζ)).symm)
  have hcomm : ∀ g ∈ Subgroup.centralizer
      ({rootTorusHom F (m + 1) 0 ζ} : Set (StatedSp (m + 1) F)),
      ∀ h ∈ Subgroup.centralizer ({rootTorusHom F (m + 1) 0 ζ} : Set (StatedSp (m + 1) F)),
      g * h * g⁻¹ * h⁻¹ ∈ complSp F (0 : Fin (m + 1)) := fun g hg h hh =>
    commutator_mem_complSp_of_centralizer_rootTorusHom (k := 0) hζ2 hg hh
  have hsu : 3 ∣ Nat.card (Subgroup.center (StatedSp (m + 1) F)) →
      (∃ lab : GLALabel, HasLabel (StatedSp (m + 1) F) (fun l : GLALabel => l = lab) ∧
        ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)) →
      complSp F (0 : Fin (m + 1)) = ⊤ ∧ q = 3 ∧
        ∀ k : StatedSp (m + 1) F, k * rootTorusHom F (m + 1) 0 ζ =
          rootTorusHom F (m + 1) 0 ζ * k := by
    intro h3
    rw [center_statedSp_eq_bot (m + 1)] at h3
    simp at h3
  have hBJS : symplecticQTorus (F := F) (ℓ := m + 1) q ⊓ complSp F (0 : Fin (m + 1)) ⊓
      Subgroup.centralizer (complSpSiegel (F := F) m : Set _) ≤
        Subgroup.zpowers (rootTorusHom F (m + 1) 0 ζ) := by
    intro y hy
    have heq := symplecticQTorus_inf_centralizer_complSpSiegel (F := F) (m := m)
      hq hq2 hqdvd hζ
    exact heq ▸ ⟨hy.1.1, hy.2⟩
  have hrankinf : evenRank (StatedSp (m + 1) F) ≤
      CFSG.Open.pRank q (symplecticQTorus (F := F) (ℓ := m + 1) q ⊓
        complSp F (0 : Fin (m + 1))) + 2 := by
    rw [heven]
    exact evenRank_le_pRank_symplecticQTorus_inf (F := F) (m := m) hq hq2 hqdvd (by omega)
  refine ⟨symplecticQTorus (F := F) (ℓ := m + 1) q,
    rootTorusHom F (m + 1) 0 ζ, complSp F (0 : Fin (m + 1)), ?_⟩
  exact concl166S_of_witness (K := StatedSp (m + 1) F) (p := p) (q := q)
    (B := symplecticQTorus (F := F) (ℓ := m + 1) q)
    (x := rootTorusHom F (m + 1) 0 ζ) (J := complSp F (0 : Fin (m + 1)))
    hq hq2 (isElemAbelian_symplecticQTorus (F := F) (ℓ := m + 1) hq) hxmem hx1 hrankB
    (by rw [heven]; omega)
    hJx (isQuasisimple_complSp hF4 (by omega) 0) hcomm
    ⟨.B, m, n⟩ hJlab hshape hm2 hsymp.2.1 hdvd (Or.inl hsymp.1)
    E hEB hE hEcard hxE he3layer
    (symplecticQTorus_le_sup_complSp_zpowers (F := F) (m := m) hq hqdvd hζ)
    hrankinf
    (complSpSiegel (F := F) m) (complSpSiegel_le_complSp (F := F) (m := m))
    (isPGroup_complSpSiegel (F := F) (m := m))
    (symplecticQTorus_le_normalizer_complSpSiegel (F := F) (m := m) q) hBJS hsu

theorem exists_concl166S_statedSp {F : Type} [Field F] [Finite F] [CharP F 2]
    {p m n q : ℕ} {ζ : Fˣ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m) (hn : 2 ≤ n)
    (hcard : Nat.card F = 2 ^ n) (hpvd : p ∣ 2 ^ n + 1)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqdvd : q ∣ Nat.card F - 1) (hζ : orderOf ζ = q) :
    ∃ (q' : ℕ) (B' : Subgroup (StatedSp (m + 1) F)) (x' : StatedSp (m + 1) F)
      (J : Subgroup (StatedSp (m + 1) F)), Concl166S (StatedSp (m + 1) F) p q' B' x' J := by
  obtain ⟨B', x', J, h⟩ := concl166S_statedSp hp hp2 hm hn hcard hpvd hq hq2 hqdvd hζ
  exact ⟨q, B', x', J, h⟩

end Certs2



section LabelToModel


theorem exists_mulEquiv_statedSp_of_isLabel {K : Type} [Group K] [Finite K] {N n : ℕ}
    (hK : HasLabel K (· = ⟨.B, N, n⟩)) (hZ : Subgroup.center K = ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ n ∧ Nonempty (K ≃* StatedSp N F) := by
  obtain ⟨-, -, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSp N 2 n := hM
  obtain ⟨-, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
  letI : Field F := hfield
  letI : Finite F := hfinite
  haveI : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = 2 ^ n := by rwa [← Nat.card_eq_fintype_card]
  have hchar : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  letI : CharP F 2 := hchar
  have hbot : (StatedScalars (Fin N ⊕ Fin N) F).subgroupOf (StatedSp N F) = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot
  let eZ : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  let eS : StatedProj (StatedSp N F) ≃* StatedSp N F :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact ⟨F, hfield, hfinite, hchar, hcard, ⟨eZ.trans (e.trans eS)⟩⟩

end LabelToModel

section Family


theorem i166On_famB_of_transport
    (htr : ∀ {K R : Type} [Group K] [Finite K] [Group R] [Finite R], (K ≃* R) → ∀ {p : ℕ},
      (∃ (q : ℕ) (B' : Subgroup R) (x' : R) (J : Subgroup R), Concl166S R p q B' x' J) →
      ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J) :
    I166On i166FamB := by
  intro K _ _ lab p hlab hfam hp hp2 hns he hr
  obtain ⟨htag, hn, hpvd⟩ := hfam
  have hlow : lab.rank ≤ evenRank K :=
    (rk2Lower_holds K lab hlab).bcd_ge (Or.inl htag) hn
  have hup : evenRank K ≤ lab.rank :=
    (rk2_eUpAt_of_tables rk2KRank rk2Upper_holds (K := K) (lab := lab) hlab).bd
      (Or.inl htag) hn
  have hN : 4 ≤ lab.rank := le_trans he hup
  have heven : evenRank K = lab.rank := le_antisymm hup hlow
  have hZ : Subgroup.center K = ⊥ := rk2_center_eq_bot_of_large hlab (Or.inl htag) hn
  obtain ⟨m, hm⟩ : ∃ m, lab.rank = m + 1 := ⟨lab.rank - 1, by omega⟩
  have hm3 : 3 ≤ m := by omega
  have hlab_eq : lab = (⟨.B, m + 1, lab.n⟩ : GLALabel) := by
    rcases lab with ⟨t, r, s⟩
    simp only at htag hm
    subst htag
    simp [hm]
  rw [hlab_eq] at hlab
  obtain ⟨F, hfield, hfinite, hchar, hcard, ⟨e⟩⟩ :=
    exists_mulEquiv_statedSp_of_isLabel (N := m + 1) (n := lab.n) hlab hZ
  letI : Field F := hfield
  letI : Finite F := hfinite
  letI : CharP F 2 := hchar
  have hF4 : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card F - 1) (by omega)
  have hoddF : Odd (Nat.card F - 1) := by
    rw [hcard]
    have h2 : Even (2 ^ lab.n) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
    have hpos : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
    exact Nat.Even.sub_odd hpos h2 odd_one
  have hq2 : q ≠ 2 := by
    intro h
    subst h
    exact (Nat.not_even_iff_odd.mpr hoddF) (even_iff_two_dvd.mpr hqdvd)
  haveI : Fact q.Prime := ⟨hq⟩
  have hqdvd' : q ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) q hqdvd'
  exact htr e (exists_concl166S_statedSp (F := F) (p := p) (m := m) (n := lab.n)
    (q := q) (ζ := ζ) hp hp2 hm3 hn hcard hpvd hq hq2 hqdvd hζ)

end Family


end CFSG.LocalAnalysis.GLTheoremA.Y10F
