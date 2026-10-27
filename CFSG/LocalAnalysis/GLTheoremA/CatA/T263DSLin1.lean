module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DSGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
public import CFSG.Assembly.GL83StatedBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.Y10F
open scoped MatrixGroups

section MatConj

theorem t263_matConj_inner {K : Type} [Field K] [Finite K] (h2 : (2 : K) = 0) (A : GL (Fin 2) K)
    (φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 2) K)))
    (hφ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K))
      (fun h h' => (h' : GL (Fin 2) K) = A * (h : GL (Fin 2) K) * A⁻¹) φ) :
    ∃ r : LargeEvenProj (LargeEvenSLGroup (Fin 2) K), φ = MulAut.conj r := by
  classical
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two (F := K) (ringChar.eq K 2) (Matrix.GeneralLinearGroup.det A : Kˣ)
  have hl0 : l ≠ 0 := by
    rintro rfl
    have := (Matrix.GeneralLinearGroup.det A).ne_zero
    simp [hl] at this
  let lu : Kˣ := Units.mk0 l hl0
  let Sc : GL (Fin 2) K := Matrix.GeneralLinearGroup.scalar (Fin 2) lu
  have hSc : (Sc : Matrix (Fin 2) (Fin 2) K) = l • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    simp [Sc, lu, Matrix.GeneralLinearGroup.scalar, Matrix.one_apply, Matrix.diagonal_apply]
  have hdetSc : (Sc : Matrix (Fin 2) (Fin 2) K).det = l * l := by
    rw [hSc, Matrix.det_smul]
    simp [sq]
  have hScc : ∀ g : GL (Fin 2) K, g * Sc = Sc * g := by
    intro g
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hSc, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]
  have hdetA' : ((A * Sc⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det Sc = Matrix.GeneralLinearGroup.det A := by
      apply Units.ext
      rw [hl]
      simpa using hdetSc
    have h2 : Matrix.GeneralLinearGroup.det (A * Sc⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have := congrArg (fun u : Kˣ => (u : K)) h2
    simpa using this
  have hmem : (A * Sc⁻¹ : GL (Fin 2) K) ∈ LargeEvenSLGroup (Fin 2) K := by
    rw [largeEvenSLGroup_eq_statedSL, CFSG.Open.StatedAPI.mem_statedSL_iff]
    exact hdetA'
  have hSLdet : ∀ g : GL (Fin 2) K, g ∈ LargeEvenSLGroup (Fin 2) K ↔ Matrix.GeneralLinearGroup.det g = 1 := by
    intro g
    rw [largeEvenSLGroup_eq_statedSL, CFSG.Open.StatedAPI.statedSL_eq_ker_det, MonoidHom.mem_ker]
  have hN : ∀ (g : GL (Fin 2) K) (h : ↥(LargeEvenSLGroup (Fin 2) K)),
      g * (h : GL (Fin 2) K) * g⁻¹ ∈ LargeEvenSLGroup (Fin 2) K := by
    intro g h
    have hh := (hSLdet _).1 h.2
    rw [hSLdet, map_mul, map_mul, hh, map_inv]
    simp
  have hconjSc : ∀ g : GL (Fin 2) K, Sc⁻¹ * g * Sc = g := by
    intro g
    rw [mul_assoc, hScc g, inv_mul_cancel_left]
  clear_value Sc
  refine ⟨LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K) ⟨A * Sc⁻¹, hmem⟩, ?_⟩
  ext q
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  have e1 : φ (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K) h) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K) ⟨A * (h : GL (Fin 2) K) * A⁻¹, hN A h⟩ :=
    hφ h ⟨A * (h : GL (Fin 2) K) * A⁻¹, hN A h⟩ rfl
  have e2 : (MulAut.conj (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K) ⟨A * Sc⁻¹, hmem⟩))
        (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K) h) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K) ⟨A * (h : GL (Fin 2) K) * A⁻¹, hN A h⟩ := by
    rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show A * Sc⁻¹ * (h : GL (Fin 2) K) * (A * Sc⁻¹)⁻¹ = A * (h : GL (Fin 2) K) * A⁻¹
    calc A * Sc⁻¹ * (h : GL (Fin 2) K) * (A * Sc⁻¹)⁻¹
        = A * (Sc⁻¹ * (h : GL (Fin 2) K) * Sc) * A⁻¹ := by group
      _ = A * (h : GL (Fin 2) K) * A⁻¹ := by rw [hconjSc]
  exact e1.trans e2.symm

end MatConj

section Families

@[expose] def t263GLinRk1 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .A 1 q => q.p = 2 | _ => False

@[expose] def t263GLinHi : TauCeti.CFSGIndex → Prop :=
  onLie fun | .A r q => q.p = 2 ∧ 2 ≤ r | _ => False

theorem t263GLin_cover (i : TauCeti.CFSGIndex) (h : t263GLin i) : t263GLinRk1 i ∨ t263GLinHi i := by
  obtain ⟨h1, -⟩ := h
  cases i with
  | cyclic p hp => simp [t263GLinAll, onLie] at h1
  | alternating n hn => simp [t263GLinAll, onLie] at h1
  | sporadic s => simp [t263GLinAll, onLie] at h1
  | lie d =>
    obtain ⟨t, hv⟩ := d
    cases t with
    | A r q =>
      have hq : q.p = 2 := by simpa [t263GLinAll, onLie] using h1
      have hr : 1 ≤ r :=
        ((TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
      rcases Nat.lt_or_ge r 2 with hr2 | hr2
      · have : r = 1 := by omega
        subst this
        exact Or.inl (by simpa [t263GLinRk1, onLie] using hq)
      · exact Or.inr (by simpa [t263GLinHi, onLie] using ⟨hq, hr2⟩)
    | _ => simp [t263GLinAll, onLie] at h1

theorem t263_recipe_rank_one {lab : LargeEvenLabel} {m : ℕ} (hc : canonLabel lab = ⟨.A, 1, m⟩) :
    ∃ m₀ : ℕ, ∀ Q : LargeEvenRawCont, LargeEvenRawDatum lab Q ↔ LargeEvenRecipeLinear 2 (2 ^ m₀) Q := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag
  case A =>
    simp [canonLabel] at hc
    obtain ⟨rfl, -⟩ := hc
    exact ⟨n, fun Q => Iff.rfl⟩
  case twD =>
    by_cases h3 : rank = 3
    · simp [canonLabel, h3] at hc
    · by_cases h2 : rank = 2
      · exact ⟨n * 2, fun Q => by simp [LargeEvenRawDatum, h2, pow_mul]⟩
      · simp [canonLabel, h3, h2] at hc
  case D =>
    by_cases h3 : rank = 3
    · simp [canonLabel, h3] at hc
    · simp [canonLabel, h3] at hc
  all_goals simp [canonLabel] at hc

end Families

section Inner

private theorem t263_charP_two {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])

theorem t263_exists_psl2_of_linRk1 {T : Type} [Group T] (h : catalogIs T t263GLinRk1) :
    ∃ (m : ℕ) (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = 2 ^ m ∧
      Nonempty (T ≃* StatedProj (StatedSL 2 E)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [t263GLinRk1, onLie] at hi
  | alternating n hn => simp [t263GLinRk1, onLie] at hi
  | sporadic s => simp [t263GLinRk1, onLie] at hi
  | lie d =>
    obtain ⟨t, hv⟩ := d
    cases t with
    | A r q =>
      rcases r with _ | _ | r
      · simp [t263GLinRk1, onLie] at hi
      · have hq : q.p = 2 := by simpa [t263GLinRk1, onLie] using hi
        haveI : Fact q.p.Prime := ⟨q.prime_p⟩
        haveI : NeZero q.exponent := ⟨Nat.pos_iff_ne_zero.1 q.exponent_pos⟩
        refine ⟨q.exponent, GaloisField q.p q.exponent, inferInstance, inferInstance, ?_,
          ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)).trans
            (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (1 + 1)
              (GaloisField q.p q.exponent))⟩⟩
        rw [GaloisField.card q.p q.exponent (Nat.pos_iff_ne_zero.1 q.exponent_pos), hq]
      · simp [t263GLinRk1, onLie] at hi
    | _ => simp [t263GLinRk1, onLie] at hi

theorem t263_lin1_inner (hLD : Y10GInnLin.LinLabelDict) {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω}
    {x : Ω} (hQ : catalogIs (PSimple p S) t263GLinRk1) (hxN : x ∈ Subgroup.normalizer (S : Set Ω))
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) :
    ∃ s : PSimple p S, MI.indAut p S x hxN = MulAut.conj s := by
  have hdiag : CFSG.Assembly.LargeEvenMarking (PQuot p S)
      fun _ _ _ I _ θ => ∃ φ ∈ I, CFSG.Assembly.LargeEvenInduces θ (indRel p S x) φ :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh x (Subgroup.mem_zpowers x)) hInn.2
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hdiag
  have hlab : HasLabel (PQuot p S) (fun l : GLALabel => l = lab) :=
    ⟨hperf, lab, hΛ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨m, E, hEf, hEfin, hE, ⟨e⟩⟩ := t263_exists_psl2_of_linRk1 hQ
  have hcanon := hLD (PQuot p S) lab 2 m E le_rfl hE hlab ⟨e⟩
  obtain ⟨m₀, hiff⟩ := t263_recipe_rank_one hcanon
  obtain ⟨K, instF, instFin, hK, hs, hna, θ, φ, hφ, hind⟩ := (hiff _).1 hraw
  haveI : CharP K 2 := t263_charP_two hK
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  obtain ⟨A, -, hA⟩ := hφ
  obtain ⟨r, hr⟩ := t263_matConj_inner h2 A φ hA
  have e1 : φ = MulAut.congr θ (MI.indAut p S x hxN) := (MI.induces_indRel_iff hxN θ).1 hind
  refine ⟨θ.symm r, ?_⟩
  have e2 : MulAut.congr θ.symm (MulAut.conj r) = MulAut.conj (θ.symm r) :=
    CFSG.ComponentClassification.OuterAutomorphisms.congr_conj θ.symm r
  have e3 : MulAut.congr θ.symm (MulAut.congr θ (MI.indAut p S x hxN)) = MI.indAut p S x hxN := by
    ext y
    simp [MulAut.congr_apply]
  rw [← e2, ← hr, e1, e3]

end Inner

section Cent

theorem t263_psl2_no_odd_comm_invol {T : Type} [Group T] (hT : catalogIs T t263GLinRk1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (s t : T) (hs : s ^ p = 1) (hs1 : s ≠ 1) (ht : orderOf t = 2) (hts : t * s = s * t) : False := by
  classical
  obtain ⟨m, E, hEf, hEfin, hE, ⟨e⟩⟩ := t263_exists_psl2_of_linRk1 hT
  haveI : CharP E 2 := t263_charP_two hE
  let e' : T ≃* PSL(2, E) :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 E).symm
  have hto : orderOf (e' t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  have hcent := CFSG.Walter.psl2_centralizer_isPGroup_of_charTwo (K := E) hto
  have hmem : e' s ∈ Subgroup.centralizer ({e' t} : Set PSL(2, E)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hts]
  obtain ⟨k, hk⟩ := hcent ⟨e' s, hmem⟩
  have hdvd : orderOf (e' s) ∣ 2 ^ k := by
    have h1 : orderOf (⟨e' s, hmem⟩ : Subgroup.centralizer ({e' t} : Set PSL(2, E))) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one hk
    rwa [Subgroup.orderOf_mk] at h1
  have hdvdp : orderOf (e' s) ∣ p := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hs, map_one])
  have h1 : orderOf (e' s) = 1 := by
    have h2 : orderOf (e' s) ∣ Nat.gcd (2 ^ k) p := Nat.dvd_gcd hdvd hdvdp
    have h3 : Nat.Coprime (2 ^ k) p :=
      Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
    rwa [h3, Nat.dvd_one] at h2
  exact hs1 (e'.injective (by rw [orderOf_eq_one_iff.1 h1, map_one]))

end Cent

section Certs


theorem t263Desc_linRk1 : T263Desc t263GLinRk1 := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hQ hF2 hSB hΩ hB h4 hT hC B₀ hB₀ hdich hcase T' hT'ne hT'2 hT'S
    hBT' hker x hxB₀ hxC hxcomm
  exfalso
  have hBel : CFSG.Open.IsElemAbelian p B := hB.1
  have hxB : x ∈ B := hB₀.1 hxB₀
  have hxp : x ^ p = 1 := hBel.2 x hxB
  have hcat : catalogIs (PSimple p S) t263GLinRk1 := by
    obtain ⟨i, hi, ⟨e⟩⟩ := hQ
    exact ⟨i, hi, ⟨(pSimpleEquiv hSp).trans e⟩⟩
  have hInn : InnDiagOn p (Subgroup.zpowers x) S :=
    S10.innDiagOn_mono hB₀.2.1 (Subgroup.zpowers_le.2 hxB₀)
  obtain ⟨w, hwT', hw2, hwx⟩ := t263_exists_invol_of_comm hT'2 hxcomm
  exact t263_false_of_inner_comm_invol hp hp2 hSn hSq hSp hxp hxC (hT'S hwT') hw2 hwx
    (t263_lin1_inner Y10GInnLin.linLabelDict_holds hcat (t263_normalizer_of_normal hSn) hInn)
    (fun s t hs hs1 ht hts => t263_psl2_no_odd_comm_invol hcat hp hp2 s t hs hs1 ht hts)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.T263

end
