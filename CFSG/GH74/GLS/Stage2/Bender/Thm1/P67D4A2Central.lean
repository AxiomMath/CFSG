module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2TorusCoord
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Core

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

omit [Finite K]
  in
theorem a2_weyl_conj (i : Fin d4.rank) {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ u : K,
      CFSG.LieType.Chevalley.weylElement d4 K i * xPar (rootOperatorFamily d4) β u *
          (CFSG.LieType.Chevalley.weylElement d4 K i)⁻¹ =
        xPar (rootOperatorFamily d4) (reflect d4 i β) ((ε : K) * u) := by
  obtain ⟨ε, hε, h⟩ := weylElement_xPar_conj (F := rootOperatorFamily d4) (K := K) i hβ
  refine ⟨ε, hε, fun u => ?_⟩
  have h1 := h 1 u
  rw [weylElement_xPar, torusElement_one_eq, one_mul] at h1
  rw [h1]
  have hrefl : CFSG.LieType.RootSystem.reflection d4.cartan i β = reflect d4 i β := by
    rw [CFSG.LieType.RootSystem.reflection_apply]
    rfl
  rw [hrefl]
  simp

@[expose] def weylWord (K : Type) [Field K] (L : List (Fin d4.rank)) : adjointGroup d4 K :=
  (L.map (CFSG.LieType.Chevalley.weylElement d4 K)).prod

@[expose] def reflWord (L : List (Fin d4.rank)) (β : Fin d4.rank → ℤ) : Fin d4.rank → ℤ :=
  L.foldr (fun i v => reflect d4 i v) β

theorem isRoot_reflWord (L : List (Fin d4.rank)) {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β) :
    IsRoot d4 (reflWord L β) := by
  induction L with
  | nil => exact hβ
  | cons i L ih => exact IsRoot.reflect i ih

omit [Finite K]
  in
theorem weylWord_conj_xPar (L : List (Fin d4.rank)) {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ u : K,
      weylWord K L * xPar (rootOperatorFamily d4) β u * (weylWord K L)⁻¹ =
        xPar (rootOperatorFamily d4) (reflWord L β) ((ε : K) * u) := by
  induction L with
  | nil => exact ⟨1, Or.inl rfl, fun u => by simp [weylWord, reflWord]⟩
  | cons i L ih =>
    obtain ⟨ε₁, hε₁, h₁⟩ := ih
    obtain ⟨ε₂, hε₂, h₂⟩ := a2_weyl_conj (K := K) i (isRoot_reflWord L hβ)
    refine ⟨ε₂ * ε₁, ?_, fun u => ?_⟩
    · rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl <;> simp
    · have e : weylWord K (i :: L) * xPar (rootOperatorFamily d4) β u * (weylWord K (i :: L))⁻¹ =
          CFSG.LieType.Chevalley.weylElement d4 K i *
            (weylWord K L * xPar (rootOperatorFamily d4) β u * (weylWord K L)⁻¹) *
              (CFSG.LieType.Chevalley.weylElement d4 K i)⁻¹ := by
        simp only [weylWord, List.map_cons, List.prod_cons]
        group
      rw [e, h₁, h₂]
      simp only [reflWord, List.foldr_cons, Int.cast_mul, mul_assoc]

@[expose] def centralWord : List (Fin d4.rank) :=
  [nd 0, nd 1, nd 3, nd 2, nd 0, nd 1, nd 3, nd 2, nd 0, nd 1, nd 3, nd 2]

theorem reflWord_central :
    reflWord centralWord (Pi.single (nd 2) 1) = -Pi.single (nd 2) 1 := by
  decide

omit [Finite K]
  in
theorem a2_rootChar_single (c : Fin d4.rank → Kˣ) (j : Fin d4.rank) :
    rootChar (τ := TwistTag.D4.tag) c (Pi.single j 1) = c j := by
  unfold rootChar
  rw [Finset.prod_eq_single j (fun i _ hij => by simp [hij]) (fun h => absurd (Finset.mem_univ j) h)]
  simp

omit [Finite K]
  in
theorem a2_torus_conj_xPar {g : adjointGroup d4 K} {c : Fin d4.rank → Kˣ}
    (hg : (g : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag c)
    {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β) (u : K) :
    g * xPar (rootOperatorFamily d4) β u * g⁻¹ =
      xPar (rootOperatorFamily d4) β (((rootChar (τ := TwistTag.D4.tag) c β : Kˣ) : K) * u) := by
  apply Subtype.ext
  change (g : ModGL TwistTag.D4.tag K) * ((xPar (rootOperatorFamily d4) β u : adjointGroup d4 K) :
      ModGL TwistTag.D4.tag K) * (g : ModGL TwistTag.D4.tag K)⁻¹ = _
  rw [coe_xPar_a2 hβ, coe_xPar_a2 hβ, hg]
  have := rootDiagUnit_conj_pinnedX (τ := TwistTag.D4.tag) c hβ (a2Sign K β * u)
  rw [this]
  congr 1
  ring

theorem A2Core.a2_central_weyl (h : A2Core σ d q) {g : adjointGroup d4 K}
    (hg : g ∈ ⨆ i, hHatE σ.toRingHom i) :
    a2Conj σ d ((((nHatE K (ng 1) * nHatE K (ng 0)) ^ 3 * g : adjointGroup d4 K)) :
        ModGL TwistTag.D4.tag K) ≠
      (((nHatE K (ng 1) * nHatE K (ng 0)) ^ 3 * g : adjointGroup d4 K) :
        ModGL TwistTag.D4.tag K) := by
  intro hfix
  obtain ⟨c, hc, -, -, -, hc2⟩ := a2_torus_coord h hg
  set β : Fin d4.rank → ℤ := Pi.single (nd 2) 1 with hβdef
  have hβ : IsRoot d4 β := isRoot_single d4 (nd 2)
  have hβ' : IsRoot d4 (-β) := IsRoot.neg hβ
  obtain ⟨ε, hε, hρ⟩ := weylWord_conj_xPar (K := K) centralWord hβ
  rw [reflWord_central] at hρ
  set W : adjointGroup d4 K := weylWord K centralWord with hW
  have hρ3 : (nHatE K (ng 1) * nHatE K (ng 0)) ^ 3 = W := by
    simp only [hW, weylWord, centralWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, nHatE_one, nHatE_zero, pow_succ, pow_zero, one_mul, mul_one, mul_assoc]
  rw [hρ3] at hfix
  set m : adjointGroup d4 K := W * g with hm
  have hc2' : σ ((c (nd 2) : Kˣ) : K) = ((c (nd 2) : Kˣ) : K) := by
    have := congrArg (fun u : Kˣ => (u : K)) hc2
    exact this
  have hchar : (((rootChar (τ := TwistTag.D4.tag) c β : Kˣ) : K)) = ((c (nd 2) : Kˣ) : K) := by
    rw [hβdef, a2_rootChar_single]
  have hconj : ∀ u : K, m * xPar (rootOperatorFamily d4) β u * m⁻¹ =
      xPar (rootOperatorFamily d4) (-β) ((ε : K) * ((c (nd 2) : Kˣ) : K) * u) := by
    intro u
    have e : m * xPar (rootOperatorFamily d4) β u * m⁻¹ =
        W * (g * xPar (rootOperatorFamily d4) β u * g⁻¹) * W⁻¹ := by
      rw [hm]; group
    rw [e, a2_torus_conj_xPar hc hβ, hchar, hρ]
    congr 1
    ring
  have hA : a2Conj σ d ((m * xPar (rootOperatorFamily d4) β 1 * m⁻¹ : adjointGroup d4 K) :
      ModGL TwistTag.D4.tag K) =
      ((xPar (rootOperatorFamily d4) (-β) ((ε : K) * ((c (nd 2) : Kˣ) : K) * a2Char d β) :
        adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
    have h1 : ((m * xPar (rootOperatorFamily d4) β 1 * m⁻¹ : adjointGroup d4 K) :
        ModGL TwistTag.D4.tag K) = (m : ModGL TwistTag.D4.tag K) *
        ((xPar (rootOperatorFamily d4) β 1 : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) *
          (m : ModGL TwistTag.D4.tag K)⁻¹ := rfl
    rw [h1, a2Conj_mul, a2Conj_mul, a2Conj_inv, hfix, a2Conj_xPar h hβ, map_one, mul_one]
    have := congrArg (fun x : adjointGroup d4 K => (x : ModGL TwistTag.D4.tag K))
      (hconj (a2Char d β))
    simpa using this
  have hB : a2Conj σ d ((m * xPar (rootOperatorFamily d4) β 1 * m⁻¹ : adjointGroup d4 K) :
      ModGL TwistTag.D4.tag K) =
      ((xPar (rootOperatorFamily d4) (-β) (a2Char d (-β) * σ ((ε : K) * ((c (nd 2) : Kˣ) : K))) :
        adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
    rw [hconj 1, mul_one, a2Conj_xPar h hβ']
  rw [hA] at hB
  have hinj := xPar_injective (F := rootOperatorFamily d4) (K := K) hβ'
  have h2 := hinj (Subtype.ext hB)
  have hεK : (ε : K) ≠ 0 := by
    rcases hε with rfl | rfl <;> simp
  have hc2K : ((c (nd 2) : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hσε : σ (ε : K) = (ε : K) := map_intCast σ ε
  have hχβ : a2Char d β = (d : K) := by
    simp [a2Char, hβdef]
  have hχβ' : a2Char d (-β) = ((d : K))⁻¹ := by
    simp [a2Char, hβdef]
  rw [hχβ, hχβ', map_mul, hσε, hc2'] at h2
  have hdK : (d : K) ≠ 0 := Units.ne_zero d
  have h3 : (d : K) * (d : K) = 1 := by
    have h4 : (ε : K) * ((c (nd 2) : Kˣ) : K) * (d : K) * (d : K) =
        (ε : K) * ((c (nd 2) : Kˣ) : K) * 1 := by
      calc (ε : K) * ((c (nd 2) : Kˣ) : K) * (d : K) * (d : K)
          = ((d : K))⁻¹ * ((ε : K) * ((c (nd 2) : Kˣ) : K)) * (d : K) := by rw [h2]
        _ = (ε : K) * ((c (nd 2) : Kˣ) : K) * 1 := by field_simp
    exact mul_left_cancel₀ (mul_ne_zero hεK hc2K) (by simpa [mul_assoc] using h4)
  have h5 : d ^ 2 = 1 := by
    apply Units.ext
    simpa [pow_two] using h3
  apply h.ne_one
  calc d = d ^ 3 * (d ^ 2)⁻¹ := by group
    _ = 1 := by rw [h.cube, h5]; simp

end CFSG.GH74.GLS.Stage2.Bender.Thm1
