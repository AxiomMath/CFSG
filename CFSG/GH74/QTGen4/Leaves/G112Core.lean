module

public import CFSG.GH74.QTGen4.Leaves.G112Basis
public import CFSG.GH74.QTGen4.Ch6.G112A2

public section

namespace CFSG.GH74.QTGen4.Leaves.G112

section Assembly

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem encC_lt4 : ∀ c : Fin 4 → ZMod 2, encC c < 4 ↔ (c 2 = 0 ∧ c 3 = 0) := by
  decide

theorem wit_spec (b : Basis (Fin 4) (ZMod 2) V) (N : V →ₗ[ZMod 2] V)
    (hU : ∀ u, u ∈ LinearMap.range N ↔ b.equivFun u 2 = 0 ∧ b.equivFun u 3 = 0)
    (γ : V ≃ₗ[ZMod 2] V) (hw : Wit (mat b γ.toLinearMap) = true) :
    (∀ w ∈ LinearMap.range N, γ w ∈ LinearMap.range N) ∧ γ (b 0) ≠ b 0 := by
  have hlt : ∀ u, u ∈ LinearMap.range N ↔ enc b u < 4 := fun u => by
    rw [hU u, enc]; exact (encC_lt4 _).symm
  simp only [Wit, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hw
  refine ⟨fun w hw => ?_, fun heq => h4 ?_⟩
  · rw [hlt] at hw ⊢
    have e := ap_enc b γ.toLinearMap w
    have e' : enc b (γ w) = ap (mat b γ.toLinearMap) (enc b w) := e.symm
    rw [e']
    obtain hk | hk | hk | hk : enc b w = 0 ∨ enc b w = 1 ∨ enc b w = 2 ∨ enc b w = 3 := by omega
    · rw [hk]; exact h0
    · rw [hk]; exact h1
    · rw [hk]; exact h2
    · rw [hk]; exact h3
  · have e := ap_enc b γ.toLinearMap (b 0)
    have hg : γ.toLinearMap (b 0) = b 0 := heq
    rw [hg, enc_basis] at e
    simpa using e

theorem finite_aut [Finite V] : Finite (V ≃ₗ[ZMod 2] V) :=
  Finite.of_injective (fun γ : V ≃ₗ[ZMod 2] V => (γ : V → V)) DFunLike.coe_injective

theorem finCore [Finite V] (B : LinearMap.BilinForm (ZMod 2) V)
    (hd : Module.finrank (ZMod 2) V = 4) (halt : ∀ v, B v v = 0)
    (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (hΓ : ∀ γ ∈ Γ, ∀ v w, B (γ v) (γ w) = B v w)
    (t : V ≃ₗ[ZMod 2] V) (htΓ : t ∈ Γ) (ht2 : t * t = 1)
    (hrk : Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2)
    (hBt : ∀ v, B v (t v) = 0) (v₁ : V) (hv₁ : v₁ ≠ 0)
    (hv₁U : v₁ ∈ LinearMap.range (t.toLinearMap - LinearMap.id))
    (hcard : 10 ∣ Nat.card Γ ∨ 18 ∣ Nat.card Γ) :
    ∃ γ ∈ Γ, (∀ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id),
        γ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) ∧ γ v₁ ≠ v₁ := by
  classical
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_aut
  have htiso : ∀ v w, B (t v) (t w) = B v w := hΓ t htΓ
  obtain ⟨b, hb0, hGram, htb0, htb1, htb2, htb3, hU⟩ :=
    exists_adapted_basis B hd halt hnd t htiso ht2 hrk hBt v₁ hv₁ hv₁U
  have hmt : mat b t.toLinearMap = tL := by
    show (⟨enc b (t (b 0)), enc b (t (b 1)), enc b (t (b 2)), enc b (t (b 3))⟩ : Lin) =
      ⟨1, 2, 5, 10⟩
    rw [htb0, htb1, htb2, htb3, enc_add, enc_add, enc_basis, enc_basis, enc_basis, enc_basis]
    rfl
  have hisoCols : ∀ γ ∈ Γ, IsoCols (mat b γ.toLinearMap) := by
    intro γ hγ
    have hbf : ∀ i j, bf (enc b (γ (b i))) (enc b (γ (b j))) = decide (Jm i j = 1) := by
      intro i j
      rw [bf_enc b B hGram, hΓ γ hγ, hGram]
    refine ⟨enc_lt b _, enc_lt b _, enc_lt b _, enc_lt b _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h := hbf 0 1
      have hJ : decide (Jm 0 1 = 1) = false := by decide
      rw [hJ] at h; exact h
    · have h := hbf 0 2
      have hJ : decide (Jm 0 2 = 1) = false := by decide
      rw [hJ] at h; exact h
    · have h := hbf 1 2
      have hJ : decide (Jm 1 2 = 1) = true := by decide
      rw [hJ] at h; exact h
    · have h := hbf 0 3
      have hJ : decide (Jm 0 3 = 1) = true := by decide
      rw [hJ] at h; exact h
    · have h := hbf 1 3
      have hJ : decide (Jm 1 3 = 1) = false := by decide
      rw [hJ] at h; exact h
    · have h := hbf 2 3
      have hJ : decide (Jm 2 3 = 1) = false := by decide
      rw [hJ] at h; exact h
  have fin : ∀ γ ∈ Γ, Wit (mat b γ.toLinearMap) = true →
      ∃ γ ∈ Γ, (∀ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id),
        γ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) ∧ γ v₁ ≠ v₁ := by
    intro γ hγ hw
    obtain ⟨h1, h2⟩ := wit_spec b (t.toLinearMap - LinearMap.id) hU γ hw
    exact ⟨γ, hγ, h1, by rw [hb0] at h2; exact h2⟩
  have hmatpow : ∀ σ : V ≃ₗ[ZMod 2] V, mat b (σ * σ).toLinearMap = pw2 (mat b σ.toLinearMap) :=
    fun σ => mat_mul b σ σ
  have hmatcube : ∀ σ : V ≃ₗ[ZMod 2] V,
      mat b (σ * (σ * σ)).toLinearMap = cube (mat b σ.toLinearMap) := fun σ => by
    rw [mat_mul, mat_mul]; rfl
  rcases hcard with h10 | h18
  ·
    have h5 : 5 ∣ Nat.card Γ := Dvd.dvd.trans (by norm_num) h10
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 5 h5
    have hg5 : orderOf (g : V ≃ₗ[ZMod 2] V) = 5 := by rw [Subgroup.orderOf_coe]; exact hg
    have hgΓ : (g : V ≃ₗ[ZMod 2] V) ∈ Γ := g.2
    set g' : V ≃ₗ[ZMod 2] V := (g : V ≃ₗ[ZMod 2] V) with hg'
    have hpow : (g' * g') * (g' * (g' * g')) = 1 := by
      have h := pow_orderOf_eq_one g'
      rw [hg5] at h
      calc (g' * g') * (g' * (g' * g')) = g' ^ 5 := by simp [pow_succ, mul_assoc]
        _ = 1 := h
    have h5eq : eqL (comp (pw2 (mat b g'.toLinearMap)) (cube (mat b g'.toLinearMap))) idL = true := by
      have e : mat b ((g' * g') * (g' * (g' * g'))).toLinearMap =
          comp (pw2 (mat b g'.toLinearMap)) (cube (mat b g'.toLinearMap)) := by
        rw [mat_mul, hmatpow, hmatcube]
      rw [← e, hpow, mat_one]
      exact eqL_self _
    have hne : eqL (mat b g'.toLinearMap) idL = false := by
      by_contra hcon
      have htrue : eqL (mat b g'.toLinearMap) idL = true := by simpa using hcon
      have h1 : g' = 1 := mat_inj b ((eqL_eq htrue).trans (mat_one b).symm)
      rw [h1, orderOf_one] at hg5
      omega
    rcases witness5 (hisoCols g' hgΓ) h5eq hne with hw | hw
    · refine fin (g' * (t * (((g' * g') * (g' * g')) * (t * g')))) ?_ ?_
      · exact Γ.mul_mem hgΓ (Γ.mul_mem htΓ (Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hgΓ hgΓ)
          (Γ.mul_mem hgΓ hgΓ)) (Γ.mul_mem htΓ hgΓ)))
      · have e : mat b (g' * (t * (((g' * g') * (g' * g')) * (t * g')))).toLinearMap =
            w5a (mat b g'.toLinearMap) := by
          simp only [mat_mul, hmt, w5a, pw2]
        rw [e]; exact hw
    · refine fin ((g' * g') * (t * ((g' * (g' * g')) * (t * (g' * g'))))) ?_ ?_
      · exact Γ.mul_mem (Γ.mul_mem hgΓ hgΓ) (Γ.mul_mem htΓ (Γ.mul_mem (Γ.mul_mem hgΓ
          (Γ.mul_mem hgΓ hgΓ)) (Γ.mul_mem htΓ (Γ.mul_mem hgΓ hgΓ))))
      · have e : mat b ((g' * g') * (t * ((g' * (g' * g')) * (t * (g' * g'))))).toLinearMap =
            w5b (mat b g'.toLinearMap) := by
          simp only [mat_mul, hmt, w5b, pw2, cube]
        rw [e]; exact hw
  ·
    have h9 : 3 ^ 2 ∣ Nat.card Γ := Dvd.dvd.trans (by norm_num) h18
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := Γ) 3 h9
    have hcomm : ∀ x y : P, x * y = y * x :=
      fun x y => (IsPGroup.isMulCommutative_of_card_eq_prime_sq hP).is_comm.comm x y
    obtain ⟨a₀, ha₀⟩ : ∃ a : P, a ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : Subsingleton P := ⟨fun x y => (hcon x).trans (hcon y).symm⟩
      have h1 : Nat.card P = 1 := Nat.card_of_subsingleton 1
      rw [hP] at h1
      norm_num at h1
    have hcube : ∀ x : P, ((x : Γ) : V ≃ₗ[ZMod 2] V) * (((x : Γ) : V ≃ₗ[ZMod 2] V) *
        ((x : Γ) : V ≃ₗ[ZMod 2] V)) = 1 := by
      intro x
      set X : V ≃ₗ[ZMod 2] V := ((x : Γ) : V ≃ₗ[ZMod 2] V) with hX
      have hXΓ : X ∈ Γ := (x : Γ).2
      have h9' : X ^ 9 = 1 := by
        have h1 : x ^ Nat.card P = 1 := pow_card_eq_one'
        rw [hP] at h1
        have h2 := congrArg (fun y : P => ((y : Γ) : V ≃ₗ[ZMod 2] V)) h1
        simpa using h2
      have h9eq : (X * (X * X)) * ((X * (X * X)) * (X * (X * X))) = 1 := by
        rw [← h9']
        simp [pow_succ, mul_assoc]
      have hm : eqL (cube (cube (mat b X.toLinearMap))) idL = true := by
        have e : mat b ((X * (X * X)) * ((X * (X * X)) * (X * (X * X)))).toLinearMap =
            cube (cube (mat b X.toLinearMap)) := by
          rw [← hmatcube X, ← hmatcube (X * (X * X))]
        rw [← e, h9eq, mat_one]
        exact eqL_self _
      have h3 := no_order_nine (hisoCols X hXΓ) hm
      rw [← hmatcube X] at h3
      exact mat_inj b ((eqL_eq h3).trans (mat_one b).symm)
    have hneq : ∀ X Y : V ≃ₗ[ZMod 2] V, X ≠ Y →
        eqL (mat b X.toLinearMap) (mat b Y.toLinearMap) = false := by
      intro X Y hXY
      by_contra hcon
      have htrue : eqL (mat b X.toLinearMap) (mat b Y.toLinearMap) = true := by simpa using hcon
      exact hXY (mat_inj b (eqL_eq htrue))
    have hP3 : ∀ x : P, orderOf x ∣ 3 := by
      intro x
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext; apply Subtype.ext
      simpa [pow_succ, mul_assoc] using hcube x
    have hz : Nat.card (Subgroup.zpowers a₀) ≤ 3 := by
      rw [Nat.card_zpowers]; exact Nat.le_of_dvd (by norm_num) (hP3 a₀)
    obtain ⟨b₀, hb₀⟩ : ∃ b₀ : P, b₀ ∉ Subgroup.zpowers a₀ := by
      by_contra hcon
      push Not at hcon
      have hinj : Function.Injective (fun x : P => (⟨x, hcon x⟩ : Subgroup.zpowers a₀)) :=
        fun x y hxy => by simpa using hxy
      have := Nat.card_le_card_of_injective _ hinj
      rw [hP] at this
      omega
    set A : V ≃ₗ[ZMod 2] V := ((a₀ : Γ) : V ≃ₗ[ZMod 2] V) with hA
    set Bv : V ≃ₗ[ZMod 2] V := ((b₀ : Γ) : V ≃ₗ[ZMod 2] V) with hBv
    have hAΓ : A ∈ Γ := (a₀ : Γ).2
    have hBΓ : Bv ∈ Γ := (b₀ : Γ).2
    have hA1 : A ≠ 1 := fun h => ha₀ (Subtype.ext (Subtype.ext h))
    have hB1 : Bv ≠ 1 := fun h => hb₀ (by
      have : b₀ = 1 := Subtype.ext (Subtype.ext h)
      exact this ▸ Subgroup.one_mem _)
    have hBA : Bv ≠ A := fun h => hb₀ (by
      have : b₀ = a₀ := Subtype.ext (Subtype.ext h)
      exact this ▸ Subgroup.mem_zpowers _)
    have hBA2 : Bv ≠ A * A := fun h => hb₀ (by
      have : b₀ = a₀ * a₀ := Subtype.ext (Subtype.ext h)
      exact this ▸ Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _))
    have hAB : A * Bv = Bv * A := by
      have := hcomm a₀ b₀
      have h2 := congrArg (fun y : P => ((y : Γ) : V ≃ₗ[ZMod 2] V)) this
      simpa using h2
    have hma3 : eqL (cube (mat b A.toLinearMap)) idL = true := by
      rw [← hmatcube, hcube a₀, mat_one]; exact eqL_self _
    have hmb3 : eqL (cube (mat b Bv.toLinearMap)) idL = true := by
      rw [← hmatcube, hcube b₀, mat_one]; exact eqL_self _
    have hma1 : eqL (mat b A.toLinearMap) idL = false := by
      rw [← mat_one b]; exact hneq _ _ hA1
    have hmb1 : eqL (mat b Bv.toLinearMap) idL = false := by
      rw [← mat_one b]; exact hneq _ _ hB1
    have hmab : eqL (comp (mat b A.toLinearMap) (mat b Bv.toLinearMap))
        (comp (mat b Bv.toLinearMap) (mat b A.toLinearMap)) = true := by
      rw [← mat_mul, ← mat_mul, hAB]; exact eqL_self _
    have hmba : eqL (mat b Bv.toLinearMap) (mat b A.toLinearMap) = false := hneq _ _ hBA
    have hmba2 : eqL (mat b Bv.toLinearMap) (pw2 (mat b A.toLinearMap)) = false := by
      rw [← hmatpow]; exact hneq _ _ hBA2
    have hW := witness9 (hisoCols A hAΓ) (hisoCols Bv hBΓ) hma3 hma1 hmb3 hmb1 hmab hmba hmba2
    simp only [W9, Bool.or_eq_true] at hW
    have hAB' : A * Bv ∈ Γ := Γ.mul_mem hAΓ hBΓ
    rcases hW with ((((hw | hw) | hw) | hw) | hw)
    · refine fin (A * (t * ((A * A) * (t * A)))) ?_ ?_
      · exact Γ.mul_mem hAΓ (Γ.mul_mem htΓ (Γ.mul_mem (Γ.mul_mem hAΓ hAΓ) (Γ.mul_mem htΓ hAΓ)))
      · simpa only [mat_mul, hmt, pw2] using hw
    · refine fin (Bv * (t * (Bv * (t * ((Bv * Bv) * (t * (Bv * Bv))))))) ?_ ?_
      · exact Γ.mul_mem hBΓ (Γ.mul_mem htΓ (Γ.mul_mem hBΓ (Γ.mul_mem htΓ (Γ.mul_mem
          (Γ.mul_mem hBΓ hBΓ) (Γ.mul_mem htΓ (Γ.mul_mem hBΓ hBΓ))))))
      · simpa only [mat_mul, hmt, pw2] using hw
    · refine fin ((A * Bv) * (t * (((A * Bv) * (A * Bv)) * (t * (A * Bv))))) ?_ ?_
      · exact Γ.mul_mem hAB' (Γ.mul_mem htΓ (Γ.mul_mem (Γ.mul_mem hAB' hAB')
          (Γ.mul_mem htΓ hAB')))
      · simpa only [mat_mul, hmt, pw2] using hw
    · refine fin (A * (t * (A * A))) ?_ ?_
      · exact Γ.mul_mem hAΓ (Γ.mul_mem htΓ (Γ.mul_mem hAΓ hAΓ))
      · simpa only [mat_mul, hmt, pw2] using hw
    · refine fin ((A * Bv) * (t * ((A * Bv) * (A * Bv)))) ?_ ?_
      · exact Γ.mul_mem hAB' (Γ.mul_mem htΓ (Γ.mul_mem hAB' hAB'))
      · simpa only [mat_mul, hmt, pw2] using hw

end Assembly

theorem g112ConclA2_d4_holds : CFSG.GH74.QTGen4.G112ConclA2_d4 := by
  intro V _ _ _ B Γ v₁ W X X₀ hhyp hc2 t ht hrk hv₁ ha2
  obtain ⟨hd, hcard⟩ := hc2
  have h101 := hhyp.toG101Hyp
  exact finCore B hd h101.alt h101.nondegenerate Γ h101.isometry t (h101.X_le ht)
    (h101.X_sq t ht) hrk ha2 v₁ h101.point hv₁ hcard

theorem g112ConclA2_le4_holds : CFSG.GH74.QTGen4.G112ConclA2_le4 :=
  CFSG.GH74.QTGen4.g112ConclA2_le4_of_d4 g112ConclA2_d4_holds

end CFSG.GH74.QTGen4.Leaves.G112
