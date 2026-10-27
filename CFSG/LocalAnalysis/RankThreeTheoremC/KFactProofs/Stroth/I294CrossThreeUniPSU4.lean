module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeUniSpec
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeModelDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeProj
public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

namespace CrossUni

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.Open
open CFSG.LocalAnalysis.RankFourTheoremC.TorusU

section Torus

variable {K : Type} [Field K] {σ : K ≃+* K} {ζ : K} {p : ℕ}

theorem exists_torusHom_four (hσ : IsUnitaryInvolution σ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : IsPrimitiveRoot ζ p) (hσζ : σ ζ = ζ⁻¹) (s : GL (Fin 4) K)
    (hsiso : conjTr σ (s : Matrix (Fin 4) (Fin 4) K) * (s : Matrix (Fin 4) (Fin 4) K) = 1)
    (hs : s ^ p = 1) :
    ∃ F : (Fin 3 → Multiplicative (ZMod p)) →* SUid σ 4,
      Function.Injective F ∧
      (∀ x, s * ((F x : SUid σ 4) : GL (Fin 4) K) = ((F x : SUid σ 4) : GL (Fin 4) K) * s) ∧
      ∀ x, ((F x : SUid σ 4) : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K → F x = 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : (p : K) ≠ 0 := (hζ.neZero').out
  set sM : Matrix (Fin 4) (Fin 4) K := ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hsM
  have hspow : sM ^ p = 1 := by
    have := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) hs
    simpa [hsM] using this
  have hSp : (Matrix.toLin' sM) ^ p = 1 := by
    rw [← Matrix.toLin'_pow, hspow, Matrix.toLin'_one]
    rfl
  have hS : ∀ x y, herm σ (Matrix.toLin' sM x) (Matrix.toLin' sM y) = herm σ x y := by
    intro x y
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, herm_mulVec, hsiso, Matrix.one_mulVec]
  obtain ⟨b, u, hb, hu⟩ := exists_orthonormal_eigenbasis hσ hζ hp.pos hp0 hσζ hSp hS
  have hu' : ∀ i, sM *ᵥ b i = u i • b i := fun i => by
    rw [← Matrix.toLin'_apply]
    exact hu i
  have hP : conjTr σ (colMatrix b) * colMatrix b = 1 := conjTr_colMatrix_mul_self hb
  have hsP : sM * colMatrix b = colMatrix b * diagonal u := mul_colMatrix hu'
  set T := torusHom (charHom hζ) (0 : Fin 4) 1 2 3
  have hTx : ∀ x j, T x j = (Pi.mulSingle (0 : Fin 4) (charHom hζ (x 0)) : Fin 4 → K) j *
      (Pi.mulSingle (1 : Fin 4) (charHom hζ (x 1)) : Fin 4 → K) j *
        (Pi.mulSingle (2 : Fin 4) (charHom hζ (x 2)) : Fin 4 → K) j *
          (Pi.mulSingle (3 : Fin 4) (charHom hζ (x 0 * x 1 * x 2)⁻¹) : Fin 4 → K) j :=
    fun x j => rfl
  have hms : ∀ (i j : Fin 4) (a : K), σ a * a = 1 →
      σ ((Pi.mulSingle i a : Fin 4 → K) j) * (Pi.mulSingle i a : Fin 4 → K) j = 1 := by
    intro i j a ha
    by_cases h : j = i
    · subst h
      simpa using ha
    · simp [Pi.mulSingle_eq_of_ne h]
  have hmul : ∀ a b : K, σ a * a = 1 → σ b * b = 1 → σ (a * b) * (a * b) = 1 := by
    intro a b ha hb
    rw [map_mul]
    calc σ a * σ b * (a * b) = (σ a * a) * (σ b * b) := by ring
      _ = 1 := by rw [ha, hb, one_mul]
  have hT : ∀ x j, σ (T x j) * T x j = 1 := by
    intro x j
    rw [hTx]
    exact hmul _ _ (hmul _ _ (hmul _ _ (hms _ _ _ (norm_charHom hζ hσζ _))
      (hms _ _ _ (norm_charHom hζ hσζ _))) (hms _ _ _ (norm_charHom hζ hσζ _)))
      (hms _ _ _ (norm_charHom hζ hσζ _))
  have hdet : ∀ x, ∏ j, T x j = 1 := by
    intro x
    simp only [hTx, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.mem_univ, if_true]
    rw [← map_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one]
  obtain ⟨F, hF⟩ := exists_hom_conjDiag hσ.invol hP T hT hdet
  have hone : ∀ (i j : Fin 4) (a : K), j ≠ i → (Pi.mulSingle i a : Fin 4 → K) j = 1 :=
    fun i j a h => by simp [Pi.mulSingle_apply, h]
  have hT0 : ∀ x, T x 0 = charHom hζ (x 0) := by
    intro x
    rw [hTx, Pi.mulSingle_eq_same, hone 1 0 _ (by decide), hone 2 0 _ (by decide),
      hone 3 0 _ (by decide)]
    simp
  have hT1 : ∀ x, T x 1 = charHom hζ (x 1) := by
    intro x
    rw [hTx, Pi.mulSingle_eq_same, hone 0 1 _ (by decide), hone 2 1 _ (by decide),
      hone 3 1 _ (by decide)]
    simp
  have hT2 : ∀ x, T x 2 = charHom hζ (x 2) := by
    intro x
    rw [hTx, Pi.mulSingle_eq_same, hone 0 2 _ (by decide), hone 1 2 _ (by decide),
      hone 3 2 _ (by decide)]
    simp
  have hT3 : ∀ x, T x 3 = charHom hζ (x 0 * x 1 * x 2)⁻¹ := by
    intro x
    rw [hTx, Pi.mulSingle_eq_same, hone 0 3 _ (by decide), hone 1 3 _ (by decide),
      hone 2 3 _ (by decide)]
    simp
  refine ⟨F, (injective_iff_map_eq_one F).mpr fun x hx => ?_, fun x => ?_, fun x hx => ?_⟩
  · have h1 : conjDiag σ (colMatrix b) (T x) = 1 := by
      rw [← hF x, hx]
      rfl
    have h2 := eq_one_of_conjDiag_eq_one hP h1
    have e0 : x 0 = 1 := eq_one_of_charHom_eq_one hζ (by rw [← hT0 x]; exact h2 0)
    have e1 : x 1 = 1 := eq_one_of_charHom_eq_one hζ (by rw [← hT1 x]; exact h2 1)
    have e2 : x 2 = 1 := eq_one_of_charHom_eq_one hζ (by rw [← hT2 x]; exact h2 2)
    funext k
    fin_cases k
    exacts [e0, e1, e2]
  · apply Units.ext
    simp only [Units.val_mul]
    rw [hF x]
    exact commute_conjDiag hP hsP _
  · obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hx
    have h1 : Matrix.scalar (Fin 4) (c : K) = conjDiag σ (colMatrix b) (T x) := by
      have := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) hc
      simpa [hF x] using this
    have h2 : diagonal (T x) = diagonal fun _ => (c : K) := by
      rw [diagonal_eq_conjDiag hP, ← h1, Matrix.scalar_apply, ← smul_one_eq_diagonal,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hP]
    have h3 : ∀ j, T x j = c := fun j => by
      have := congrFun (congrFun h2 j) j
      simpa using this
    have e0 : charHom hζ (x 0) = c := (hT0 x).symm.trans (h3 0)
    have e1 : charHom hζ (x 1) = c := (hT1 x).symm.trans (h3 1)
    have e2 : charHom hζ (x 2) = c := (hT2 x).symm.trans (h3 2)
    have e3 : charHom hζ (x 0 * x 1 * x 2)⁻¹ = c := (hT3 x).symm.trans (h3 3)
    have hcp : (c : K) ^ p = 1 := by
      rw [← e0, ← map_pow, pow_prime_eq_one_zmod, map_one]
    have hc4 : (c : K) ^ 4 = 1 := by
      have h0 : ((c : K) * c * c) ≠ 0 :=
        mul_ne_zero (mul_ne_zero c.ne_zero c.ne_zero) c.ne_zero
      have h2 := e3
      rw [map_inv, map_mul, map_mul, e0, e1, e2] at h2
      calc (c : K) ^ 4 = (c : K) * ((c : K) * c * c) := by ring
        _ = ((c : K) * c * c)⁻¹ * ((c : K) * c * c) := by rw [h2]
        _ = 1 := inv_mul_cancel₀ h0
    have hcop : Nat.Coprime p 4 := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
        (hp.dvd_of_dvd_pow (n := 2) (by simpa using h)))
    have hc1 : c = 1 := Units.ext (by
      have := pow_gcd_eq_one.2 ⟨hcp, hc4⟩
      rwa [hcop.gcd_eq_one, pow_one] at this)
    apply Subtype.ext
    apply Units.ext
    show (((F x : SUid σ 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1
    rw [hF x, ← h1, hc1]
    simp

end Torus

section Main

open CFSG.LieType.BorelTits CFSG.LinearGroups

theorem statedSU_scalar_pow {K : Type} [Field K] {r f n : ℕ} (hr : r.Prime)
    (hK : Nat.card K = (r ^ f) ^ 2) (hn : 1 ≤ n)
    (z : StatedSU n (r ^ f) K) (hz : z ∈ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (r ^ f) K)) :
    z ^ n = 1 ∧ z ^ (r ^ f + 1) = 1 := by
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hz
  have hmem : GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n (r ^ f) K := by
    rw [hc]
    exact z.2
  obtain ⟨hcn, hcq⟩ := (scalar_mem_statedSU_iff hr hK hn c).1 hmem
  refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [Subgroup.coe_pow, ← hc, ← map_pow, hcn, map_one]
    rfl
  · rw [Subgroup.coe_pow, ← hc, ← map_pow, hcq, map_one]
    rfl

end Main

end CrossUni

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits

theorem i294CrossModelPSU4_holds : I294CrossModelPSU4 := by
  intro q K _ _ hK h3 x hx
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  obtain ⟨r, f, hr, hchar, rfl⟩ := CrossUni.exists_prime_pow_of_card_sq hK
  haveI : Fact r.Prime := ⟨hr⟩
  haveI := hchar
  obtain ⟨g, hg3, rfl⟩ := exists_lift_pow_three (H := StatedSU 4 (r ^ f) K) (N := 4)
    (by norm_num) (fun z hz => (CrossUni.statedSU_scalar_pow hr hK (by norm_num) z hz).1)
    hx3
  have hσ : IsUnitaryInvolution (unitaryInvolution K r f) :=
    isUnitaryInvolution_unitaryInvolution hK
  have hq : 1 < r ^ f := one_lt_pow_of_card hK
  have hcard : 3 ∣ Nat.card Kˣ := by
    rw [card_units_of_card hK, sq_sub_one_eq _ hq.le]
    exact Dvd.dvd.mul_right h3 _
  obtain ⟨ζ, hζ⟩ := CrossUni.exists_isPrimitiveRoot_three hcard
  have hσζ : unitaryInvolution K r f ζ = ζ⁻¹ := by
    rw [unitaryInvolution_apply]
    have h1 : ζ ^ (r ^ f + 1) = 1 := (hζ.pow_eq_one_iff_dvd _).2 h3
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h1)
  have hgS : (g : GL (Fin 4) K) ∈ SUid (unitaryInvolution K r f) 4 := by
    rw [SUid_eq_statedSU hK 4]
    exact g.2
  have hsiso := (mem_SUid.1 hgS).2
  have hs : (g : GL (Fin 4) K) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hg3
  obtain ⟨F, hFi, hFc, hFs⟩ := CrossUni.exists_torusHom_four hσ Nat.prime_three (by norm_num)
    hζ hσζ (g : GL (Fin 4) K) hsiso hs
  have hA : Nat.card (Fin 3 → Multiplicative (ZMod 3)) = 3 ^ 3 := by
    simp [Nat.card_eq_fintype_card]
  have := le_pRank_centralizer_statedProj (H := StatedSU 4 (r ^ f) K)
    (A := Fin 3 → Multiplicative (ZMod 3)) (k := 3) (fun a b => mul_comm a b)
    (fun a => funext fun i => CrossUni.pow_prime_eq_one_zmod (a i)) hA
    ((SUid (unitaryInvolution K r f) 4).subtype.comp F)
    ((SUid (unitaryInvolution K r f) 4).subtype_injective.comp hFi)
    (fun a => by
      rw [← SUid_eq_statedSU hK 4]
      exact (F a).2)
    (fun a ha => hFi (by rw [hFs a ha, map_one])) g
    (fun a => hFc a)
  exact this

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
