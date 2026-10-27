module

public import CFSG.ClassicalInvolution.AschTight.S19LField
public import CFSG.ClassicalInvolution.AschTight.S19LSL2
public import CFSG.ClassicalInvolution.AschTight.S1911F0c
public import CFSG.ClassicalInvolution.AschTight.S1911FusD

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19L

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

omit [IsSimpleGroup G] in
theorem three_lt_card {Y : Subgroup G} {F : Type} [Field F] [Finite F]
    (eY : ↥Y ⧸ classicalInvolutionOddCore ↥Y ≃* SL(2, F)) (h3 : 3 ≤ Nat.card F)
    (h16 : 16 ≤ Nat.card ↥((S : Subgroup G) ⊓ Y)) : 3 < Nat.card F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (S.isPGroup'.to_le inf_le_left :
    IsPGroup 2 ↥((S : Subgroup G) ⊓ Y)).exists_card_eq
  have hk4 : 4 ≤ k := by
    by_contra h
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h16d : 16 ∣ Nat.card ↥Y := by
    have h1 : 2 ^ 4 ∣ 2 ^ k := Nat.pow_dvd_pow 2 hk4
    rw [← hk] at h1
    exact h1.trans (Subgroup.card_dvd_of_le inf_le_right)
  have hY := Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore ↥Y)
  have hO : Odd (Nat.card (classicalInvolutionOddCore ↥Y)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥Y
  rw [hY, Nat.card_congr eY.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    at h16d
  have hco : Nat.Coprime 16 (Nat.card (classicalInvolutionOddCore ↥Y)) :=
    Nat.Coprime.pow_left 4 (Nat.coprime_two_left.mpr hO)
  have h16' := hco.dvd_of_dvd_mul_right h16d
  by_contra hle
  have h3' : Nat.card F = 3 := by omega
  rw [h3'] at h16'
  exact absurd h16' (by decide)

@[expose] noncomputable def fixMap {Y : Subgroup G} {F : Type} [Field F]
    (e : Y ⧸ classicalInvolutionOddCore Y ≃* SL(2, F)) {a : G}
    (haN : a ∈ Subgroup.normalizer (Y : Set G)) :
    ↥(Y ⊓ Subgroup.centralizer ({a} : Set G)) →* ↥(S1911.slFix e ⟨a, haN⟩) :=
  ((S1911.slProj Y e).comp (Subgroup.inclusion inf_le_left)).codRestrict _ fun c => by
    change S1911.slAut Y e ⟨a, haN⟩ (S1911.slProj Y e (Subgroup.inclusion inf_le_left c)) =
      S1911.slProj Y e (Subgroup.inclusion inf_le_left c)
    rw [S1911.slAut_slProj]
    congr 1
    apply Subtype.ext
    rw [normalizerConj_apply_coe]
    have hc := Subgroup.mem_centralizer_singleton_iff.mp c.2.2
    change a * c * a⁻¹ = c
    rw [← hc]
    group

omit [Finite G] [IsSimpleGroup G] in
theorem coe_fixMap {Y : Subgroup G} {F : Type} [Field F]
    (e : Y ⧸ classicalInvolutionOddCore Y ≃* SL(2, F)) {a : G}
    (haN : a ∈ Subgroup.normalizer (Y : Set G)) (c : ↥(Y ⊓ Subgroup.centralizer ({a} : Set G))) :
    ((fixMap e haN c : ↥(S1911.slFix e ⟨a, haN⟩)) : SL(2, F)) =
      S1911.slProj Y e (Subgroup.inclusion inf_le_left c) := rfl

omit [IsSimpleGroup G] in
theorem fixMap_surjective {Y : Subgroup G} {F : Type} [Field F]
    (e : Y ⧸ classicalInvolutionOddCore Y ≃* SL(2, F)) {a : G}
    (haN : a ∈ Subgroup.normalizer (Y : Set G)) (ha2 : a * a = 1) :
    Function.Surjective (fixMap e haN) := by
  rintro ⟨b, hb⟩
  obtain ⟨c, hca, hcb⟩ := S1911.exists_mem_centralizer_of_slAut_eq e haN ha2 hb
  exact ⟨⟨c, c.2, hca⟩, Subtype.ext hcb⟩

theorem exists_mem_derived (hd : Sec19DataT p f K z S W L t V) {a : G}
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (haX : a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G)) {m' : ℕ} (hY2 : IsSL2ModOdd (sec19Y K z) m')
    (h16 : 16 ≤ Nat.card ↥((S : Subgroup G) ⊓ sec19Y K z)) :
    ∃ (H : Subgroup ↥(Subgroup.centralizer ({a} : Set G)))
      (y : ↥(Subgroup.centralizer ({a} : Set G))),
      (∀ h ∈ H, (h : G) * z = z * (h : G) ∧ (h : G) ∈ centralizerModOdd ⊤ K) ∧
        y ∈ ⁅⁅H, H⁆, ⁅H, H⁆⁆ ∧
        Odd (orderOf ((⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G)))⁻¹ * y)) := by
  have hd0 := hd.toSec19Data
  have hNY := S1916.sd_centralizer_le_normalizer_Y hd0
  have hzZ := S1916.isUniqueInvolution_W_inf hd
  have haN := hNY (hd0.hSz haS)
  obtain ⟨p', e', hfact, hp'2, he', -, ⟨eY⟩⟩ := hY2
  have hFcard : Nat.card (GaloisField p' e') = p' ^ e' := GaloisField.card p' e' he'.ne'
  have hp'3 : 3 ≤ p' := by have := hfact.out.two_le; omega
  have hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p' e')) :=
    ⟨p', e', hfact.out, hfact.out.odd_of_ne_two hp'2, he', hFcard⟩
  have h3 : 3 < Nat.card (GaloisField p' e') := three_lt_card eY
    (by rw [hFcard]; exact hp'3.trans (Nat.le_self_pow he'.ne' p')) h16
  set Ψ := normalizerToPGammaL2Mod eY hFcard hF h3 with hΨ
  have hσ1 := fieldPart_ne_one hd haS ha2 haX hp'2 eY hFcard hF h3 haN
  have hσ2 : (Ψ ⟨a, haN⟩).right * (Ψ ⟨a, haN⟩).right = 1 := by
    have haa : (⟨a, haN⟩ : Subgroup.normalizer ((sec19Y K z : Subgroup G) : Set G)) *
        ⟨a, haN⟩ = 1 := Subtype.ext ha2
    have h1 : Ψ ⟨a, haN⟩ * Ψ ⟨a, haN⟩ = 1 := by rw [← map_mul, haa, map_one]
    have h2 := congrArg SemidirectProduct.right h1
    simpa using h2
  obtain ⟨e₂, rfl⟩ := S1911.two_dvd_of_ringEquiv he'.ne' hσ1 hσ2
  have he₂ : 0 < e₂ := by omega
  obtain ⟨g, hg⟩ := S1911.exists_semilinHom_of_mem eY hFcard hF h3 ⟨a, haN⟩
  have hinv : ∀ b, semilinHom g (Ψ ⟨a, haN⟩).right (semilinHom g (Ψ ⟨a, haN⟩).right b) = b := by
    intro b
    rw [← hg, ← hg]
    exact S1911.slAut_slAut_of_mul_self eY ⟨a, haN⟩ ha2 b
  obtain ⟨φ⟩ := S1911.factF0 p' e₂ hp'2 he₂ _ hσ1 hσ2 g hinv
  have hfix : S1911.slFix eY ⟨a, haN⟩ = MonoidHom.eqLocus
      (semilinHom g (Ψ ⟨a, haN⟩).right) (MonoidHom.id SL(2, GaloisField p' (2 * e₂))) := by
    ext b
    change S1911.slAut _ eY ⟨a, haN⟩ b = b ↔ _ = b
    rw [hg]
  let φ' : ↥(S1911.slFix eY ⟨a, haN⟩) ≃* SL(2, GaloisField p' e₂) :=
    (MulEquiv.subgroupCongr hfix).trans φ
  have h2 : (2 : GaloisField p' e₂) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p' e₂) p']; exact hp'2)
  have h2' : (2 : GaloisField p' (2 * e₂)) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p' (2 * e₂)) p']; exact hp'2)
  set T₁ := (⊤ : Subgroup ↥(S1911.slFix eY ⟨a, haN⟩)) with hT₁
  set T₂ := (⊤ : Subgroup SL(2, GaloisField p' e₂)) with hT₂
  set T₃ := (⊤ : Subgroup ↥(sec19Y K z ⊓ Subgroup.centralizer ({a} : Set G))) with hT₃
  set n := φ'.symm (-1) with hn
  have hn2 : ⁅⁅T₁, T₁⁆, ⁅T₁, T₁⁆⁆ = (⁅⁅T₂, T₂⁆, ⁅T₂, T₂⁆⁆).map φ'.symm.toMonoidHom := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hT₂,
      Subgroup.map_top_of_surjective _ φ'.symm.surjective]
  have hnD : n ∈ ⁅⁅T₁, T₁⁆, ⁅T₁, T₁⁆⁆ := by
    rw [hn2]
    exact ⟨-1, neg_one_mem_derived h2, rfl⟩
  set π := fixMap eY haN with hπ
  have hπs := fixMap_surjective eY haN ha2
  have hD : (⁅⁅T₃, T₃⁆, ⁅T₃, T₃⁆⁆).map π = ⁅⁅T₁, T₁⁆, ⁅T₁, T₁⁆⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hT₃,
      Subgroup.map_top_of_surjective _ hπs]
  obtain ⟨y', hy'D, hy'n⟩ : n ∈ (⁅⁅T₃, T₃⁆, ⁅T₃, T₃⁆⁆).map π := hD ▸ hnD
  set zYa : ↥(sec19Y K z ⊓ Subgroup.centralizer ({a} : Set G)) := ⟨z, hzZ.mem.2, hzA⟩ with hzYa
  have hbot : W ⊓ sec19Y K z ⊓ oddCoreOf (sec19Y K z) = ⊥ :=
    S1916.inf_oddCoreOf_eq_bot (S.isPGroup'.to_le (inf_le_left.trans hd.hWS)) _
  have hπz : (((π zYa : ↥(S1911.slFix eY ⟨a, haN⟩)) : SL(2, GaloisField p' (2 * e₂))) :
      Matrix (Fin 2) (Fin 2) (GaloisField p' (2 * e₂))) = -1 := by
    refine CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2' _ ?_ ?_
    · rw [← Subgroup.coe_pow, ← map_pow, sq, show zYa * zYa = 1 from Subtype.ext hzZ.sq, map_one,
        Subgroup.coe_one]
    · intro h
      have h1 : S1911.slProj (sec19Y K z) eY ⟨z, hzZ.mem.2⟩ = 1 := by
        rw [← h, hπ, coe_fixMap]
        rfl
      rw [S1911.slProj_eq_one_iff] at h1
      have hmem : z ∈ W ⊓ sec19Y K z ⊓ oddCoreOf (sec19Y K z) := ⟨hzZ.mem, h1⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hzZ.ne_one hmem
  have hnn : (((n : ↥(S1911.slFix eY ⟨a, haN⟩)) : SL(2, GaloisField p' (2 * e₂))) :
      Matrix (Fin 2) (Fin 2) (GaloisField p' (2 * e₂))) = -1 := by
    refine CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2' _ ?_ ?_
    · rw [← Subgroup.coe_pow, hn, ← map_pow, neg_one_sq, map_one, Subgroup.coe_one]
    · intro h
      have h1 : n = 1 := Subtype.ext h
      rw [hn, MulEquiv.map_eq_one_iff] at h1
      have := congrArg (fun A : SL(2, GaloisField p' e₂) =>
        (A : Matrix (Fin 2) (Fin 2) (GaloisField p' e₂)) 0 0) h1
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
        Matrix.neg_apply, Matrix.one_apply_eq] at this
      apply h2
      linear_combination -this
  have hzn : π zYa = n := Subtype.ext (Subtype.ext (hπz.trans hnn.symm))
  have hker : (((zYa⁻¹ * y' : ↥(sec19Y K z ⊓ Subgroup.centralizer ({a} : Set G))) : G)) ∈
      oddCoreOf (sec19Y K z) := by
    have h1 : π (zYa⁻¹ * y') = 1 := by rw [map_mul, map_inv, hzn, hy'n, inv_mul_cancel]
    have h2 : S1911.slProj (sec19Y K z) eY
        (Subgroup.inclusion inf_le_left (zYa⁻¹ * y')) = 1 := by
      rw [← coe_fixMap eY haN, ← hπ, h1]
      rfl
    exact (S1911.slProj_eq_one_iff eY _).mp h2
  set ι : ↥(sec19Y K z ⊓ Subgroup.centralizer ({a} : Set G)) →*
    ↥(Subgroup.centralizer ({a} : Set G)) := Subgroup.inclusion inf_le_right with hι
  refine ⟨ι.range, ι y', ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    have hxY : (x : G) ∈ sec19Y K z := x.2.1
    exact ⟨(Subgroup.mem_centralizer_singleton_iff.mp (S1916.sd_le_centralizer_Y hd0 hxY)),
      ⟨Subgroup.mem_top _, hxY.2.1, hxY.2.2.1, hxY.2.2.2⟩⟩
  · have hmap : (⁅⁅T₃, T₃⁆, ⁅T₃, T₃⁆⁆).map ι = ⁅⁅ι.range, ι.range⁆, ⁅ι.range, ι.range⁆⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_commutator, hT₃, ← MonoidHom.range_eq_map]
    rw [← hmap]
    exact ⟨y', hy'D, rfl⟩
  · have e : (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G)))⁻¹ * ι y' = ι (zYa⁻¹ * y') := by
      rw [map_mul, map_inv]
      rfl
    rw [e, ← Subgroup.orderOf_coe]
    exact (oddCoreOf_odd_natCard (sec19Y K z)).of_dvd_nat
      (Subgroup.orderOf_dvd_natCard _ hker)

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19L
