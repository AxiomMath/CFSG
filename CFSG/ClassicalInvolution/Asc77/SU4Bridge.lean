module

public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusBridge
public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthLayerD

public section

namespace CFSG.ClassicalInvolution.RouteD.SU4Pattern

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Models.TwistedPairs
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.WeakCT.SU4 CFSG.Timmesfeld
open scoped Matrix MatrixGroups

@[expose] def levi4 {K : Type} [Field K] : Matrix (Fin 4) (Fin 4) K :=
  Matrix.diagonal ![1, 1, -1, -1]

theorem levi4_mul_self {K : Type} [Field K] : (levi4 : Matrix (Fin 4) (Fin 4) K) * levi4 = 1 := by
  rw [levi4, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

@[expose] def leviGL (K : Type) [Field K] : GL (Fin 4) K :=
  ⟨levi4, levi4, levi4_mul_self, levi4_mul_self⟩

theorem coe_leviGL {K : Type} [Field K] :
    ((leviGL K : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = levi4 := rfl

theorem rootMatrix_zero_one_comm {K : Type} [Field K] (σ : K ≃+* K) (x : K) :
    rootMatrix σ (0 : Fin 4) 1 x * levi4 = levi4 * rootMatrix σ (0 : Fin 4) 1 x := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rootMatrix, levi4, Matrix.mul_apply, Matrix.single_apply, Matrix.diagonal_apply,
      Fin.rev]

theorem rootMatrix_one_zero_comm {K : Type} [Field K] (σ : K ≃+* K) (x : K) :
    rootMatrix σ (1 : Fin 4) 0 x * levi4 = levi4 * rootMatrix σ (1 : Fin 4) 0 x := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rootMatrix, levi4, Matrix.mul_apply, Matrix.single_apply, Matrix.diagonal_apply,
      Fin.rev]

section Levi

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F] {σ₀ : K ≃+* K} {b c : F}
  [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]

theorem phiGL_short_mem_centralizer (D : KleinData F K σ₀ b c)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (B : SL(2, ShortField b c)) :
    D.PhiGL (shortBlock hirr 3 finOne B) ∈
      Subgroup.centralizer ({leviGL K} : Set (GL (Fin 4) K)) := by
  refine sl2_mem_of_tv (D.PhiGL.comp (shortBlock hirr 3 finOne))
    (H := Subgroup.centralizer ({leviGL K} : Set (GL (Fin 4) K))) (fun t => ?_) (fun t => ?_) B
  · show D.PhiGL (shortBlock hirr 3 finOne (tv 0 1 t)) ∈ _
    rw [shortBlock_tv01]
    change D.PhiGL (twShortRoot 3 hirr iO true (.ofAdd (fieldCoord t))) ∈ _
    rw [D.PhiGL_eq_of_coe (g := suroot σ₀ D.σσ 0 1 (by decide) (by decide) (by decide)
        (-(D.δ * (algebraMap F K (fieldCoord t 0) - algebraMap F K (fieldCoord t 1) * D.ω))))
        (D.PhiMon_short_e1 hirr (fieldCoord t)), Subgroup.mem_centralizer_singleton_iff]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_leviGL]
    exact rootMatrix_zero_one_comm σ₀ _
  · show D.PhiGL (shortBlock hirr 3 finOne (tv 1 0 t)) ∈ _
    rw [shortBlock_tv10]
    change D.PhiGL (twShortRoot 3 hirr iO false (.ofAdd (starCoord t))) ∈ _
    rw [D.PhiGL_eq_of_coe (g := suroot σ₀ D.σσ 1 0 (by decide) (by decide) (by decide)
        (D.ε * (algebraMap F K (starCoord t 0) + algebraMap F K (starCoord t 1) *
          algebraMap F K b + algebraMap F K (starCoord t 1) * D.ω)))
        (D.PhiMon_short_f1 hirr (starCoord t)), Subgroup.mem_centralizer_singleton_iff]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_leviGL]
    exact rootMatrix_one_zero_comm σ₀ _

end Levi

section RankOne

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem map_rankOne_eq_rootSU2 (hF : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (Q : GL (Fin 4) K)
    (hQ : conjTr (unitaryInvolution K p f) (Q : Matrix (Fin 4) (Fin 4) K) *
      (Q : Matrix (Fin 4) (Fin 4) K) = antidiag 4)
    (hsupp : ∀ r : Fin 4, r = 0 ∨ r = 1 →
      (Q : Matrix (Fin 4) (Fin 4) K) r 0 = 0 ∧ (Q : Matrix (Fin 4) (Fin 4) K) r 3 = 0) :
    (rootGroup (unitaryInvolution K p f) (unitaryInvolution_involutive hF) 4
        (Pi.single (1 : Fin (4 / 2)) 1) ⊔
      rootGroup (unitaryInvolution K p f) (unitaryInvolution_involutive hF) 4
        (-Pi.single (1 : Fin (4 / 2)) 1)).map (conjEquiv Q hQ).toMonoidHom =
      rootSU2 K p f (by norm_num : 2 ≤ 4) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have hγ : toStd 4 (Pi.single (1 : Fin (4 / 2)) 1) =
      2 • weight 4 (lowIdx (1 : Fin (4 / 2))) := by decide
  have hγ' : toStd 4 (-Pi.single (1 : Fin (4 / 2)) 1) =
      2 • weight 4 (Fin.rev (lowIdx (1 : Fin (4 / 2)))) := by decide
  obtain ⟨i, hi⟩ := exists_isLongRootSU2_map_rankOne hF hp2 (by norm_num : 2 ≤ 4) hγ hγ' Q hQ
  have hmem : rootInvSU K p f (by norm_num : 2 ≤ 4) ∈
      (rootGroup (unitaryInvolution K p f) (unitaryInvolution_involutive hF) 4
        (Pi.single (1 : Fin (4 / 2)) 1) ⊔
      rootGroup (unitaryInvolution K p f) (unitaryInvolution_involutive hF) 4
        (-Pi.single (1 : Fin (4 / 2)) 1)).map (conjEquiv Q hQ).toMonoidHom := by
    rw [rankOne_eq_fixCols hF hγ hγ', mem_map_fixCols_iff Q hQ]
    intro w hw
    obtain ⟨u, rfl⟩ : ∃ u, w = (Q : Matrix (Fin 4) (Fin 4) K) *ᵥ u :=
      ⟨((Q⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ w, by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]⟩
    have hu := (mem_perp_colPlane_iff hQ (i := lowIdx (1 : Fin (4 / 2))) u).mp hw
    have hu1 : u 1 = 0 := hu.2
    have hu2 : u 2 = 0 := hu.1
    have w0 : ((Q : Matrix (Fin 4) (Fin 4) K) *ᵥ u) 0 = 0 := by
      obtain ⟨h0, h3⟩ := hsupp 0 (Or.inl rfl)
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, h0, h3, hu1, hu2]
    have w1 : ((Q : Matrix (Fin 4) (Fin 4) K) *ᵥ u) 1 = 0 := by
      obtain ⟨h0, h3⟩ := hsupp 1 (Or.inr rfl)
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, h0, h3, hu1, hu2]
    show suMat (rootInvSU K p f (by norm_num : 2 ≤ 4)) *ᵥ ((Q : Matrix (Fin 4) (Fin 4) K) *ᵥ u) =
      (Q : Matrix (Fin 4) (Fin 4) K) *ᵥ u
    rw [suMat_rootInvSU, negBlock_eq_diagonal]
    funext a
    fin_cases a <;> simp [Matrix.mulVec_diagonal, w0, w1]
  have hord : orderOf (rootInvSU K p f (by norm_num : 2 ≤ 4)) = 2 :=
    (isClassicalSL2_rootSU2 hF hp2 (by norm_num : 2 ≤ 4)).orderOf_eq_two
  have hii : rootInvSU K p f (by norm_num : 2 ≤ 4) = i :=
    hi.eq_of_orderOf_eq_two hF hp2 hmem hord
  rw [hi.eq_longRootGroupSU h2, ← hii, suMat_rootInvSU,
    ← rootSU2_eq_longRootGroupSU h2 (by norm_num : 2 ≤ 4)]

end RankOne

section Bridge

variable {p f : ℕ} [Fact p.Prime]

theorem exists_phiSU_bridge (hp2 : p ≠ 2) (hf : f ≠ 0) {b c : GaloisField p f}
    [Fact (∀ r : GaloisField p f, r ^ 2 ≠ -c + b * r)]
    (hirr : ∀ s : GaloisField p f, s ^ 2 + b * s + c ≠ 0) :
    ∃ Φ : spinGroup (Spin.quadMinus 3 (GaloisField p f) b c) ≃*
        SU (unitaryInvolution (GaloisField p (2 * f)) p f) 4,
      (∀ x ∈ (spinMinusModel hirr).sb.range,
        (((Φ x : SU (unitaryInvolution (GaloisField p (2 * f)) p f) 4) :
          GL (Fin 4) (GaloisField p (2 * f))) : Matrix (Fin 4) (Fin 4) (GaloisField p (2 * f))) *
            levi4 = levi4 * (((Φ x : SU (unitaryInvolution (GaloisField p (2 * f)) p f) 4) :
          GL (Fin 4) (GaloisField p (2 * f))) :
            Matrix (Fin 4) (Fin 4) (GaloisField p (2 * f)))) ∧
      ∀ (Q : GL (Fin 4) (GaloisField p (2 * f)))
        (hQ : conjTr (unitaryInvolution (GaloisField p (2 * f)) p f)
          (Q : Matrix (Fin 4) (Fin 4) (GaloisField p (2 * f))) *
            (Q : Matrix (Fin 4) (Fin 4) (GaloisField p (2 * f))) = antidiag 4),
        (∀ r : Fin 4, r = 0 ∨ r = 1 →
          (Q : Matrix (Fin 4) (Fin 4) (GaloisField p (2 * f))) r 0 = 0 ∧
            (Q : Matrix (Fin 4) (Fin 4) (GaloisField p (2 * f))) r 3 = 0) →
        (spinMinusModel hirr).lb.range.map (Φ.trans (conjEquiv Q hQ)).toMonoidHom =
          rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4) := by
  have : NeZero f := ⟨hf⟩
  have : NeZero (2 * f) := ⟨by omega⟩
  obtain ⟨inst, ⟨D⟩⟩ := exists_kleinData hp2 hf hirr
  let _ := inst
  have hF : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    card_galoisField_two_mul p f (Nat.one_le_iff_ne_zero.mpr hf)
  have h2 : (2 : GaloisField p f) ≠ 0 := ModelFacts.two_ne_zero_galoisField f hp2
  let ePhi : spinGroup (Spin.quadMinus 3 (GaloisField p f) b c) ≃*
      SU (unitaryInvolution (GaloisField p (2 * f)) p f) 4 :=
    MulEquiv.ofBijective (D.PhiSU hirr h2)
      ⟨D.PhiSU_injective hirr h2, fun g => by
        have h := D.range_PhiSU_eq_top hF hirr h2
        have hg : g ∈ (D.PhiSU hirr h2).range := by rw [h]; exact Subgroup.mem_top g
        exact hg⟩
  refine ⟨ePhi, ?_, ?_⟩
  · rintro _ ⟨B, rfl⟩
    have h1 := phiGL_short_mem_centralizer D hirr B
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    have h' := congrArg Units.val h1
    rw [Units.val_mul, Units.val_mul, coe_leviGL] at h'
    exact h'
  · intro Q hQ hsupp
    have hmap : (spinMinusModel hirr).lb.range.map (ePhi.trans (conjEquiv Q hQ)).toMonoidHom =
        ((minusLongBlock b c).range.map (D.PhiSU hirr h2)).map (conjEquiv Q hQ).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [hmap, D.map_minusLongBlock_eq hF hirr h2]
    exact map_rankOne_eq_rootSU2 hF hp2 Q hQ hsupp

end Bridge

section Pair

variable {p f : ℕ} [Fact p.Prime]

theorem twistedPair_of_equiv (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {b c : GaloisField p f}
    [Fact (∀ r : GaloisField p f, r ^ 2 ≠ -c + b * r)]
    {hirr : ∀ s : GaloisField p f, s ^ 2 + b * s + c ≠ 0} (hg6 : SpinMinus6Generated hirr)
    (e : spinGroup (Spin.quadMinus 3 (GaloisField p f) b c) ≃*
      Su (GaloisField p (2 * f)) p f 4)
    {R : Subgroup (Su (GaloisField p (2 * f)) p f 4)}
    (hR : R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) (by norm_num : 2 ≤ 4))
    (hlb : (spinMinusModel hirr).lb.range.map e.toMonoidHom = R) {X : Type} [Group X]
    (ψ : Su (GaloisField p (2 * f)) p f 4 →* X)
    (hker : ψ.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f 4)) :
    TwistedB2BlockPair hirr (ψ.comp e.toMonoidHom).range (R.map ψ)
        (((spinMinusModel hirr).sb.range.map e.toMonoidHom).map ψ) ∧
      R ⊔ (spinMinusModel hirr).sb.range.map e.toMonoidHom = ⊤ := by
  have hF := typeU_card_field (p := p) (f := f) hq
  have h2 : (2 : GaloisField p f) ≠ 0 := ModelFacts.two_ne_zero_galoisField f hp2
  obtain ⟨i, hi⟩ := hR
  refine ⟨⟨ψ.comp e.toMonoidHom, rfl, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro y hy
    have hy1 : e y ∈ ψ.ker := hy
    have hc := hker hy1
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro w
    apply e.injective
    rw [map_mul, map_mul]
    exact hc (e w)
  · intro a b hab
    apply injective_minusLongBlock hirr h2
    apply e.injective
    have hab' : ψ (e ((spinMinusModel hirr).lb a)) = ψ (e ((spinMinusModel hirr).lb b)) := hab
    have ha : e ((spinMinusModel hirr).lb a) ∈ R := by
      rw [← hlb]
      exact ⟨_, ⟨a, rfl⟩, rfl⟩
    have hb : e ((spinMinusModel hirr).lb b) ∈ R := by
      rw [← hlb]
      exact ⟨_, ⟨b, rfl⟩, rfl⟩
    have hw : (e ((spinMinusModel hirr).lb a))⁻¹ * e ((spinMinusModel hirr).lb b) ∈ R :=
      R.mul_mem (R.inv_mem ha) hb
    have hwk : (e ((spinMinusModel hirr).lb a))⁻¹ * e ((spinMinusModel hirr).lb b) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab', inv_mul_cancel]
    exact inv_mul_eq_one.mp (Transfer.eq_one_of_mem_ker_of_isLongRootSU2 hF hp2 hq
      (by norm_num : 3 ≤ 4) hi hker _ hw hwk)
  · rw [← Subgroup.map_map, hlb]
  · exact (Subgroup.map_map _ _ _).symm
  · rw [← hlb, ← Subgroup.map_sup, hg6, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr e.surjective

end Pair

end CFSG.ClassicalInvolution.RouteD.SU4Pattern
