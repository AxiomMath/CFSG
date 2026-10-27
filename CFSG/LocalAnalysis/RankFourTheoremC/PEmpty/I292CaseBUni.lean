module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBGen
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBOmega
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBUniClif
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBUniCard
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseAUni
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALinAut
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseAIdx

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB

open Matrix Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {r f p : ℕ} {K : Type} [Field K]

section Basic

variable (h : UnitaryFieldData r f K)

theorem conjHom_eq_one_iff {n : ℕ} (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ r ^ f = 2))
    (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    primeFormConjHom h _ A = 1 ↔ ∃ c : Kˣ, h.norm (c : K) = 1 ∧
      (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c := by
  classical
  haveI := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, hker1, -⟩ := unitary_prime_form_full_semilinear_realization h hC hn hq
  have e := hker1 ⟨A, 1⟩
  rw [primeFormPsi_apply, map_one, mul_one] at e
  rw [e]
  exact ⟨fun h' => h'.2, fun h' => ⟨rfl, h'⟩⟩

theorem conjHom_not_mem_inner {n : ℕ} (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ r ^ f = 2))
    (y : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hdet : ∀ b : K, b ^ n ≠ ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det) :
    primeFormConjHom h _ y ∉
      inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  intro hin
  classical
  haveI := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, -, -, -, hinn, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  obtain ⟨s, hs⟩ := (hinn _).1 hin
  have h1 : primeFormConjHom h _
      (y * (⟨s, s.2.1⟩ : primeFormUnitary h ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K))⁻¹) = 1 := by
    rw [map_mul, map_inv, ← hs, mul_inv_cancel]
  obtain ⟨c, -, hc⟩ := (conjHom_eq_one_iff h hn hq _).1 h1
  have hy : (y : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c * s := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc
    rw [← hc]
    group
  apply hdet (c : K)
  rw [hy, Units.val_mul, Matrix.det_mul, s.2.2, mul_one, det_scalar_eq]

theorem diagGL_mem_primeFormUnitary (d : Fin p → Kˣ) (hd : ∀ i, h.norm (d i : K) = 1) :
    diagGL p K d ∈ primeFormUnitary h ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) := by
  rw [mem_primeFormUnitary, diagGL_val, Units.val_one, Matrix.mul_one,
    Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have := hd i
  simpa [UnitaryFieldData.norm, mul_comm] using this

theorem rotGL_mem_primeFormUnitary :
    rotGL p K ∈ primeFormUnitary h ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) := by
  rw [mem_primeFormUnitary, rotGL_val, Units.val_one, Matrix.mul_one]
  have h1 : (((finRotate p)⁻¹).permMatrix K).map h.bar = ((finRotate p)⁻¹).permMatrix K := by
    ext i j
    simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply]
    split_ifs <;> simp
  rw [h1, Matrix.transpose_permMatrix, inv_inv, ← Matrix.permMatrix_mul, inv_mul_cancel,
    Matrix.permMatrix_one]

end Basic


section Model

variable (h : UnitaryFieldData r f K)

@[expose] noncomputable def uniModel (hn : 3 ≤ p) (hq : ¬(p = 3 ∧ r ^ f = 2)) :
    MatModel p K (primeFormP h ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)) where
  H := gramSU h ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)
  𝔾 := primeFormUnitary h ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)
  norm_mem := fun g hg A hA => conj_mem_gramSU h _ hg hA
  ι := QuotientGroup.mk' (normOneScalars h
    (gramSU h ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)) p)
  c := primeFormConjHom h _
  det_one := fun A hA => hA.2
  ι_surj := QuotientGroup.mk'_surjective _
  ι_eq_one := fun A => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_normOneScalars]
    constructor
    · rintro ⟨c, -, -, hc⟩
      exact ⟨c, hc⟩
    · rintro ⟨z, hz⟩
      have hAU : (A : GL (Fin p) K) ∈
          primeFormUnitary h ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) := A.2.1
      have hdet : ((A : GL (Fin p) K) : Matrix (Fin p) (Fin p) K).det = 1 := A.2.2
      rw [hz] at hAU hdet
      have hN := norm_eq_one_of_scalar_mem_primeFormUnitary h (by omega) 1 hAU
      refine ⟨z, hN, ?_, hz⟩
      rw [det_scalar_eq] at hdet
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hdet)
  c_ι := fun g A => primeFormConjHom_mk h _ g A
  c_eq_one := fun g hg => by
    obtain ⟨c, -, hc⟩ := (conjHom_eq_one_iff h hn hq g).1 hg
    exact ⟨c, hc⟩

theorem uniModelHyps [Finite K] (hp : p.Prime) (hn : 3 ≤ p) (hq : ¬(p = 3 ∧ r ^ f = 2))
    (hpq : p ∣ r ^ f + 1) {ŷ : GL (Fin p) K}
    (hŷU : ŷ ∈ primeFormUnitary h ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)) {ω : K}
    (hωN : h.bar ω * ω = 1) (hy : (ŷ : Matrix (Fin p) (Fin p) K) ^ p = Matrix.scalar (Fin p) ω)
    (hω : ∀ b : K, b ^ p ≠ ω) : ModelHyps (uniModel h hn hq) ŷ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hK1card : Nat.card (Units.map h.normHom).ker = r ^ f + 1 := (unitary_field_norm h).2.2.1
  refine ⟨hŷU, ?_, ?_, ?_⟩
  · intro Th hTh hT2 hTne hyN
    have hdet : ∀ g ∈ Th, (g : Matrix (Fin p) (Fin p) K).det = 1 := fun g hg => (hTh hg).2
    obtain ⟨B, δ, hrot, hδ, hdiag, hsep⟩ := exists_diag_basis hp hp2 hT2 hTne hdet hy hω hyN
    exact exists_unitary_diag_basis h hp hp2 (fun g hg => (hTh hg).1) hŷU hωN hrot hδ hdiag hsep
  · intro Th B hBU hB hyN hdvd
    set U := primeFormUnitary h ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) with hUdef
    set K1 : Subgroup Kˣ := (Units.map h.normHom).ker with hK1
    obtain ⟨S⟩ : Nonempty (Sylow p K1) := inferInstance
    set Q : Subgroup Kˣ := (S : Subgroup K1).map K1.subtype with hQ
    have hQp : IsPGroup p Q := S.isPGroup'.map K1.subtype
    have hQcard : Nat.card Q = p ^ (r ^ f + 1).factorization p := by
      rw [hQ, Subgroup.card_map_of_injective K1.subtype_injective, Sylow.card_eq_multiplicity,
        hK1card]
    have hQK1 : Q ≤ K1 := Subgroup.map_subtype_le _
    have hmono : monoQ (p := p) (K := K) Q ≤ U := by
      rw [monoQ]
      refine sup_le ?_ ?_
      · rintro _ ⟨c, rfl⟩
        exact diagGL_mem_primeFormUnitary h (fun i => (c i : Kˣ))
          (fun i => (h.mem_ker_normUnits).1 (hQK1 (c i).2))
      · rw [Subgroup.zpowers_le]
        exact rotGL_mem_primeFormUnitary h
    set Mm := (monoQ (p := p) (K := K) Q).map (MulAut.conj B).toMonoidHom with hMm
    have hMmN : Mm ≤ normalizer (Th : Set (GL (Fin p) K)) :=
      map_monoQ_le_normalizer hB.sep hB.diag hB.rot hyN Q
    have hMmU : Mm ≤ U := by
      rintro _ ⟨m, hm, rfl⟩
      exact mul_mem (mul_mem hBU (hmono hm)) (inv_mem hBU)
    set Mu : Subgroup ↥U := Mm.subgroupOf U with hMu
    have hle : Mu ≤ (normalizer (Th : Set (GL (Fin p) K))).comap U.subtype :=
      fun x hx => hMmN hx
    have hdvd' : p ∣ Mu.index := hdvd.trans (Subgroup.index_dvd_of_le hle)
    have hMucard : Nat.card Mu = Nat.card (monoQ (p := p) (K := K) Q) := by
      rw [hMu, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMmU).toEquiv, hMm,
        Subgroup.card_map_of_injective (MulAut.conj B).injective]
    have hMp : IsPGroup p (monoQ (p := p) (K := K) Q) := isPGroup_monoQ hp.two_le hQp
    obtain ⟨m, hm⟩ := hMp.exists_card_eq
    have hge := card_monoQ_ge (K := K) hp.two_le hQp
    rw [hQcard, hm, ← pow_mul, ← pow_succ] at hge
    have hmge : (r ^ f + 1).factorization p * p + 1 ≤ m :=
      (Nat.pow_le_pow_iff_right hp.one_lt).1 hge
    have hcard := Subgroup.card_mul_index Mu
    have hfac := factorization_card_primeFormUnitary hp hp2 h hpq
    have hidx0 : Mu.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    have hpos : 0 < Mu.index.factorization p := Nat.Prime.factorization_pos_of_dvd hp hidx0 hdvd'
    rw [← hcard, hMucard, hm, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hidx0,
      Finsupp.add_apply, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same] at hfac
    nlinarith
  · have hpK1 : p ∣ Nat.card (Units.map h.normHom).ker := by
      rw [hK1card]
      exact hpq
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hpK1
    have hζp : (ζ : Kˣ) ^ p = 1 := by
      have := pow_orderOf_eq_one ζ
      rw [hζ] at this
      simpa using congrArg Subtype.val this
    refine ⟨(ζ : Kˣ), hζp, ?_, ?_, fun j => ?_⟩
    · intro h1
      have h2 : ζ = 1 := Subtype.ext h1
      rw [h2, orderOf_one] at hζ
      exact hp.one_lt.ne hζ
    · intro h2
      have h3 : ζ ^ 2 = 1 := Subtype.ext (by simpa using h2)
      have h4 : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one h3
      rw [hζ] at h4
      have := Nat.le_of_dvd (by norm_num) h4
      omega
    · refine diagGL_mem_primeFormUnitary h _ fun i => ?_
      by_cases hi : i = j
      · subst hi
        rw [Pi.mulSingle_eq_same]
        exact (h.mem_ker_normUnits).1 ζ.2
      · rw [Pi.mulSingle_eq_of_ne hi]
        simp [UnitaryFieldData.norm]

end Model


section Aut

variable (h : UnitaryFieldData r f K)

theorem uniAutHyps [Finite K] (hp : p.Prime) (hn : 3 ≤ p) (hq : ¬(p = 3 ∧ r ^ f = 2))
    {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal]
    (eP : (↥L ⧸ center ↥L) ≃* primeFormP h ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K))
    (hperf : ∀ (N : Subgroup Y) [N.Normal], IsPGroup p (Y ⧸ N) → N = ⊤)
    {ŷ : GL (Fin p) K}
    (hŷU : ŷ ∈ primeFormUnitary h ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K))
    (hdet : ∀ b : K, b ^ p ≠ (ŷ : Matrix (Fin p) (Fin p) K).det) {x : Y}
    (hx : thetaP L eP x = primeFormConjHom h _ ⟨ŷ, hŷU⟩) :
    AutHyps (thetaP L eP) (uniModel h hn hq) := by
  classical
  have hC : IsPrimeFormGram (1 : GL (Fin p) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, -, hFker, hDn, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order h hn hq
  set I := inner (primeFormP h ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)) with hI
  set D := primeFormD h ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) with hD
  haveI : D.Normal := hDn
  have hIle : I ≤ (thetaP L eP).range := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨u, rfl⟩ := eP.surjective w
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective u
    exact ⟨(l : Y), thetaP_of_mem L eP l⟩
  have hdvd : I.relIndex D ∣ p := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, hcard]
    exact Nat.gcd_dvd_left _ _
  have hDS : D ≤ (thetaP L eP).range :=
    le_of_relIndex_dvd_prime hp hIle hdvd (d := primeFormConjHom h _ ⟨ŷ, hŷU⟩) ⟨_, rfl⟩
      ⟨x, hx⟩ (conjHom_not_mem_inner h hn hq ⟨ŷ, hŷU⟩ hdet)
  have hab : ∀ a b : MulAut (primeFormP h ((1 : GL (Fin p) K) :
      Matrix (Fin p) (Fin p) K)), a * b * a⁻¹ * b⁻¹ ∈ D := by
    obtain ⟨-, hcyc⟩ := card_ringAut_and_isCyclic h.prime K (n := 2 * f) h.card
    haveI : IsCyclic (K ≃+* K) := hcyc
    letI : CommGroup (K ≃+* K) := IsCyclic.commGroup
    intro a b
    rw [← hFker, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [mul_comm (primeFormFieldFactor h hC hn hq a) (primeFormFieldFactor h hC hn hq b)]
    group
  exact ⟨hDS, not_dvd_index_comap_of_commutator hp (thetaP L eP) D hab hperf,
    fun φ hφ ψ => hDn.conj_mem φ hφ ψ, hab⟩

end Aut


section Cfg

theorem uniHyps_of_cfg {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x z : Y}
    {L : Subgroup Y} [L.Normal] [Group.IsPerfect ↥L] (hcfg : LinUniCfg p P x z L) [Finite K]
    (hU : UnitaryFieldData r f K) (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 3 ≤ p)
    (hq : ¬(p = 3 ∧ r ^ f = 2)) (hK : Nat.card K = (r ^ f) ^ 2) (hpq : p ∣ r ^ f + 1)
    (e : (↥L ⧸ center ↥L) ≃* StatedProj (StatedSU p (r ^ f) K)) (ŷ : GL (Fin p) K) (ω : Kˣ)
    (hŷu : ((ŷ : Matrix (Fin p) (Fin p) K).map (· ^ (r ^ f)))ᵀ *
      (ŷ : Matrix (Fin p) (Fin p) K) = 1)
    (hŷp : ŷ ^ p = GeneralLinearGroup.scalar (Fin p) ω)
    (hω : orderOf ω = p ^ (r ^ f + 1).factorization p)
    (hact : ∀ (g h : ↥L) (A B : ↥(StatedSU p (r ^ f) K)), x * (g : Y) * x⁻¹ = (h : Y) →
      e (QuotientGroup.mk g) = QuotientGroup.mk A →
      (B : GL (Fin p) K) = ŷ * (A : GL (Fin p) K) * ŷ⁻¹ →
      e (QuotientGroup.mk h) = QuotientGroup.mk B) :
    ∃ hM : ModelHyps (uniModel hU hn hq) ŷ,
      AutHyps (thetaP L (e.trans (statedEquiv hU (by omega : 1 ≤ p)))) (uniModel hU hn hq) ∧
      thetaP L (e.trans (statedEquiv hU (by omega : 1 ≤ p))) x =
        (uniModel hU hn hq).c ⟨ŷ, hM.ŷ_mem⟩ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hn1 : 1 ≤ p := by omega
  have hŷ : ŷ ∈ primeFormUnitary hU ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) := by
    rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one]
    exact hŷu
  have hŷp' : ((ŷ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) ^ p =
      Matrix.scalar (Fin p) (ω : K) := by
    rw [← Units.val_pow_eq_pow_val, hŷp, GeneralLinearGroup.coe_scalar]
  have hωnp : ∀ b : K, b ^ p ≠ (ω : K) := not_pow_omega hp hp2 hpq hK hω
  have hdet := not_pow_det hp hp2 hŷp' hωnp
  have hωN : hU.bar (ω : K) * (ω : K) = 1 := by
    have h1 : (ω : Kˣ) ^ (r ^ f + 1) = 1 := by
      have h2 : orderOf ω ∣ r ^ f + 1 := by
        rw [hω]
        exact Nat.ordProj_dvd _ _
      exact orderOf_dvd_iff_pow_eq_one.1 h2
    have h3 := congrArg Units.val h1
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h3
    rw [hU.bar_apply, ← pow_succ]
    exact h3
  have hM := uniModelHyps hU hp hn hq hpq hŷ hωN hŷp' hωnp
  have hx : thetaP L (e.trans (statedEquiv hU hn1)) x = primeFormConjHom hU _ ⟨ŷ, hŷ⟩ :=
    thetaP_eq_conjHom hU hn1 e ŷ hŷ hact
  exact ⟨hM, uniAutHyps hU hp hn hq (e.trans (statedEquiv hU hn1)) hcfg.data.perf hŷ hdet hx, hx⟩

theorem kd292CaseBSylow_uni (p : ℕ) (Y : Type) [Group Y] [Finite Y] (P : Subgroup Y) (x z : Y)
    (L : Subgroup Y) (hcfg : LinUniCfg p P x z L) (hzero : LinUniZero p L)
    (hmodel : LinUniModelUni p x L) (T : Subgroup Y) (hT2 : IsPGroup 2 T)
    (hxN : x ∈ normalizer (T : Set Y)) (hTL : T ⊓ L ≠ ⊥) :
    ∃ Q : Sylow p Y, (Q : Subgroup Y) ≤ normalizer (omegaOneTwo T L : Set Y) := by
  have hY := hcfg.data.cfg
  have hp : p.Prime := hY.prime
  have hp5 : 5 ≤ p := hY.five_le
  have hp2 : p ≠ 2 := by omega
  have hL := hcfg.comp
  have hLu := hcfg.uniq
  haveI hLn : L.Normal := I291.normal_of_unique hL hLu
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hperf : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  have hCp : IsPGroup p (centralizer (L : Set Y)) :=
    I292.centralizer_isPGroup hY.core hL hLu hzero.pCore_cyclic hzero.omega_le
  obtain ⟨q, K, instF, instFin, e, ŷ, ω, hK, hpq, hŷu, hŷp, hω, hact⟩ := hmodel
  have hq2 : 2 ≤ q := by
    have := Nat.le_of_dvd (by omega) hpq
    omega
  obtain ⟨r, f, rfl, ⟨hU⟩⟩ := exists_unitaryFieldData hK hq2
  have hn3 : 3 ≤ p := by omega
  have hq : ¬(p = 3 ∧ r ^ f = 2) := fun ⟨h3, _⟩ => by omega
  obtain ⟨hM, hAut, hx⟩ := uniHyps_of_cfg hcfg hU hp hp5 hn3 hq hK hpq e ŷ ω hŷu hŷp hω hact
  exact exists_sylow_normalizer hp hp2 hCp (e.trans (statedEquiv hU (by omega)))
    (uniModel hU hn3 hq) hM hAut omegaOneTwo_le_left (isPGroup_omegaOneTwo hT2)
    (omegaOneTwo_ne_bot hT2 hTL) (mem_normalizer_omegaOneTwo' hxN) hx

theorem kd292CaseBConstr_uni (p : ℕ) (Y : Type) [Group Y] [Finite Y] (P : Subgroup Y) (x z : Y)
    (L : Subgroup Y) (hcfg : LinUniCfg p P x z L) (hzero : LinUniZero p L)
    (hmodel : LinUniModelUni p x L) (T : Subgroup Y) (hT2 : IsPGroup 2 T)
    (hxN : x ∈ normalizer (T : Set Y)) (hTL : T ⊓ L ≠ ⊥) :
    GLAPLayer p (normalizer (omegaOneTwo T L : Set Y)) = ⊥ := by
  have hY := hcfg.data.cfg
  have hp : p.Prime := hY.prime
  have hp5 : 5 ≤ p := hY.five_le
  have hp2 : p ≠ 2 := by omega
  have hL := hcfg.comp
  have hLu := hcfg.uniq
  haveI hLn : L.Normal := I291.normal_of_unique hL hLu
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hperf : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  have hCp : IsPGroup p (centralizer (L : Set Y)) :=
    I292.centralizer_isPGroup hY.core hL hLu hzero.pCore_cyclic hzero.omega_le
  obtain ⟨q, K, instF, instFin, e, ŷ, ω, hK, hpq, hŷu, hŷp, hω, hact⟩ := hmodel
  have hq2 : 2 ≤ q := by
    have := Nat.le_of_dvd (by omega) hpq
    omega
  obtain ⟨r, f, rfl, ⟨hU⟩⟩ := exists_unitaryFieldData hK hq2
  have hn3 : 3 ≤ p := by omega
  have hq : ¬(p = 3 ∧ r ^ f = 2) := fun ⟨h3, _⟩ => by omega
  obtain ⟨hM, hAut, hx⟩ := uniHyps_of_cfg hcfg hU hp hp5 hn3 hq hK hpq e ŷ ω hŷu hŷp hω hact
  exact glaPLayer_normalizer hp hp2 hCp (e.trans (statedEquiv hU (by omega)))
    (uniModel hU hn3 hq) hM hAut omegaOneTwo_le_left (isPGroup_omegaOneTwo hT2)
    (omegaOneTwo_ne_bot hT2 hTL) (mem_normalizer_omegaOneTwo' hxN) hx

end Cfg

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB
