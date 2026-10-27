module

public import CFSG.ClassicalInvolution.ModelFacts.TwistedE6PairClass

public section

namespace CFSG.ClassicalInvolution.ModelFacts.LeviE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional

section Generic

variable {τ : Tag} {K : Type} [Field K]

theorem commute_pinnedX_pm {γ : Fin τ.rank → ℤ} {y : ModGL τ K} {s t : K} (hs : s * s = 1)
    (ht : t * t = 1) (h : y * pinnedX τ K γ s = pinnedX τ K γ s * y) :
    y * pinnedX τ K γ t = pinnedX τ K γ t * y := by
  have hinv : ∀ {a : K}, y * pinnedX τ K γ a = pinnedX τ K γ a * y →
      y * pinnedX τ K γ (-a) = pinnedX τ K γ (-a) * y := fun {a} ha => by
    rw [← pinnedX_neg]
    exact (Commute.inv_right (show Commute y (pinnedX τ K γ a) from ha)).eq
  rcases mul_self_eq_one_iff.1 hs with rfl | rfl <;> rcases mul_self_eq_one_iff.1 ht with rfl | rfl
  · exact h
  · exact hinv h
  · have := hinv h
    rwa [neg_neg] at this
  · exact h

theorem map_comm_of_comm {G H : Type*} [Group G] [Group H] (f : G →* H) {a b : G}
    (h : a * b = b * a) : f a * f b = f b * f a :=
  (f.map_mul a b).symm.trans ((congrArg f h).trans (f.map_mul b a))

end Generic

section Phi

variable (p : ℕ) [Fact p.Prime] (e : ℕ)

abbrev E6Closure : Type := AlgebraicClosure (GaloisField p (2 * e))

theorem isAlgebraic_zmod_E6Closure [Finite (GaloisField p (2 * e))] [CharP (E6Closure p e) p] :
    letI := ZMod.algebra (E6Closure p e) p
    Algebra.IsAlgebraic (ZMod p) (E6Closure p e) := by
  let _ : Algebra (ZMod p) (E6Closure p e) := ZMod.algebra (E6Closure p e) p
  refine ⟨fun y => ?_⟩
  obtain ⟨E, hEf, hyE, -⟩ := exists_finite_subfield_of_finset (K := GaloisField p (2 * e))
    ({y} : Finset (E6Closure p e))
  have hy : y ∈ E := hyE (Finset.mem_coe.2 (Finset.mem_singleton_self y))
  have : Fintype E := Fintype.ofFinite E
  have hpow : y ^ Fintype.card E = y :=
    congrArg Subtype.val (FiniteField.pow_card (⟨y, hy⟩ : E))
  refine ⟨Polynomial.X ^ Fintype.card E - Polynomial.X,
    FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) Fintype.one_lt_card, ?_⟩
  rw [map_sub, map_pow, Polynomial.aeval_X, hpow, sub_self]

noncomputable abbrev phiE6 : twistedE6Group p e →* ModGL .E6 (E6Closure p e) :=
  twistedE6Phi p e (E6Closure p e)

noncomputable abbrev frobE6 : ModGL .E6 (E6Closure p e) →* ModGL .E6 (E6Closure p e) :=
  frobTwistGL TwistTag.E6.tag (E6Closure p e) p e (diagramMap TwistTag.E6 (E6Closure p e))

noncomputable abbrev twistedE6SignGroup' : Subgroup (twistedE6Group p e) :=
  (e6SignDiagonalGroup (E6Closure p e)).comap (phiE6 p e)

noncomputable abbrev stdRankE6 : Subgroup (twistedE6Group p e) :=
  twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (proj thetaE6) ⊔
    twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-proj thetaE6)

theorem rho_thetaE6 : rho thetaE6 = thetaE6 := perm_thetaE6

theorem rho_neg_thetaE6 : rho (-thetaE6) = -thetaE6 :=
  List.ofFn_injective (by decide : List.ofFn (permLattice TwistTag.E6.perm (-thetaE6)) =
    List.ofFn (-thetaE6))

theorem e6Sign_thetaE6_mul_self {F : Type} [Field F] : (e6Sign thetaE6 : F) * e6Sign thetaE6 = 1 :=
  e6Sign_mul_self thetaE6

theorem phiE6_xFixed_thetaE6_one :
    phiE6 p e (xFixed (frobQ p e) isRoot_thetaE6 rho_thetaE6 (1 : GaloisField p (2 * e))
      (map_one _)) = pinnedX .E6 (E6Closure p e) thetaE6 (e6Sign thetaE6 : E6Closure p e) := by
  have h := twistedE6Phi_xFixed p e (E6Closure p e) isRoot_thetaE6
    rho_thetaE6 (1 : GaloisField p (2 * e)) (map_one _)
  rw [map_one, mul_one] at h
  exact h

theorem phiE6_xFixed_neg_thetaE6_one :
    phiE6 p e (xFixed (frobQ p e) (IsRoot.neg isRoot_thetaE6) rho_neg_thetaE6
      (1 : GaloisField p (2 * e)) (map_one _)) =
      pinnedX .E6 (E6Closure p e) (-thetaE6) (e6Sign (-thetaE6) : E6Closure p e) := by
  have h := twistedE6Phi_xFixed p e (E6Closure p e)
    (IsRoot.neg isRoot_thetaE6) rho_neg_thetaE6 (1 : GaloisField p (2 * e)) (map_one _)
  rw [map_one, mul_one] at h
  exact h

theorem xFixed_thetaE6_mem_stdRankE6 :
    xFixed (frobQ p e) isRoot_thetaE6 rho_thetaE6 (1 : GaloisField p (2 * e)) (map_one _) ∈
      stdRankE6 p e :=
  Subgroup.mem_sup_left (xFixed_mem (frobQ p e) isRoot_thetaE6 rho_thetaE6 _ _)

theorem xFixed_neg_thetaE6_mem_stdRankE6 :
    xFixed (frobQ p e) (IsRoot.neg isRoot_thetaE6) rho_neg_thetaE6 (1 : GaloisField p (2 * e))
      (map_one _) ∈ stdRankE6 p e := by
  refine Subgroup.mem_sup_right ?_
  rw [← map_neg proj thetaE6]
  exact xFixed_mem (frobQ p e) (IsRoot.neg isRoot_thetaE6) rho_neg_thetaE6 _ _

variable {p e}

theorem commute_rootSL2_of_commute_phi_xFixed {y : ModGL .E6 (E6Closure p e)}
    (hu : y * phiE6 p e (xFixed (frobQ p e) isRoot_thetaE6 rho_thetaE6
      (1 : GaloisField p (2 * e)) (map_one _)) =
      phiE6 p e (xFixed (frobQ p e) isRoot_thetaE6 rho_thetaE6 (1 : GaloisField p (2 * e))
        (map_one _)) * y)
    (hv : y * phiE6 p e (xFixed (frobQ p e) (IsRoot.neg isRoot_thetaE6) rho_neg_thetaE6
      (1 : GaloisField p (2 * e)) (map_one _)) =
      phiE6 p e (xFixed (frobQ p e) (IsRoot.neg isRoot_thetaE6) rho_neg_thetaE6
        (1 : GaloisField p (2 * e)) (map_one _)) * y) :
    y * rootSL2 .E6 (E6Closure p e) thetaE6 (uSL 1) =
        rootSL2 .E6 (E6Closure p e) thetaE6 (uSL 1) * y ∧
      y * rootSL2 .E6 (E6Closure p e) thetaE6 (vSL 1) =
        rootSL2 .E6 (E6Closure p e) thetaE6 (vSL 1) * y := by
  rw [phiE6_xFixed_thetaE6_one] at hu
  rw [phiE6_xFixed_neg_thetaE6_one] at hv
  obtain ⟨η, hη, hηv⟩ := exists_rootSL2_vSL_eq (τ := .E6) (K := E6Closure p e)
    (β := thetaE6) isRoot_thetaE6
  have hε : ((pinnedData .E6 thetaE6).2.2 • (1 : E6Closure p e)) *
      ((pinnedData .E6 thetaE6).2.2 • (1 : E6Closure p e)) = 1 := by
    rcases pinnedSign_eq .E6 thetaE6 with h | h <;> rw [h] <;> simp
  refine ⟨?_, ?_⟩
  · rw [rootSL2_uSL_eq]
    exact commute_pinnedX_pm e6Sign_thetaE6_mul_self hε hu
  · rw [hηv 1]
    exact commute_pinnedX_pm (e6Sign_mul_self (-thetaE6)) (by rw [mul_one]; exact hη) hv

theorem phiE6_center_stdRankE6 (hp2 : p ≠ 2) (he : 1 ≤ e) {z : twistedE6Group p e}
    (hz : z ∈ stdRankE6 p e) (hzc : ∀ r ∈ stdRankE6 p e, z * r = r * z) :
    phiE6 p e z = 1 ∨
      phiE6 p e z = rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : (E6Closure p e)ˣ)) := by
  classical
  have hk : ringChar (E6Closure p e) ≠ 2 := by rw [ringChar.eq (E6Closure p e) p]; exact hp2
  have hmem : phiE6 p e z ∈ rootRankOneGroup .E6 (E6Closure p e) thetaE6 := by
    rw [(exceptional_Lang_root_rank_one_torus_transport .E6 (E6Closure p e)
      isRoot_thetaE6).1]
    have h1 : ∀ x ∈ twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (proj thetaE6),
        phiE6 p e x ∈ rootSubgroup .E6 (E6Closure p e) thetaE6 := fun x hx =>
      ((map_twistedRootGroup_fixed p e hp2 he isRoot_thetaE6 rho_thetaE6).le
        (Subgroup.mem_map_of_mem _ hx)).1
    have h2 : ∀ x ∈ twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-proj thetaE6),
        phiE6 p e x ∈ rootSubgroup .E6 (E6Closure p e) (-thetaE6) := fun x hx => by
      have hx' : x ∈ twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (proj (-thetaE6)) := by
        rw [map_neg]
        exact hx
      exact ((map_twistedRootGroup_fixed p e hp2 he (IsRoot.neg isRoot_thetaE6)
        rho_neg_thetaE6).le (Subgroup.mem_map_of_mem _ hx')).1
    have hle : (stdRankE6 p e).map (phiE6 p e) ≤
        rootSubgroup .E6 (E6Closure p e) thetaE6 ⊔ rootSubgroup .E6 (E6Closure p e) (-thetaE6) := by
      rw [Subgroup.map_sup]
      exact sup_le_sup (by rintro _ ⟨x, hx, rfl⟩; exact h1 x hx)
        (by rintro _ ⟨x, hx, rfl⟩; exact h2 x hx)
    exact hle (Subgroup.mem_map_of_mem _ hz)
  obtain ⟨A, hA⟩ := hmem
  have hinj : Function.Injective (rootSL2 .E6 (E6Closure p e) thetaE6) :=
    ((exceptional_Lang_root_rank_one_data .E6 (E6Closure p e) thetaE6).2.2.2.2.2.2.2.1 hk).1
  have hu' := map_comm_of_comm (phiE6 p e) (hzc _ (xFixed_thetaE6_mem_stdRankE6 p e))
  have hv' := map_comm_of_comm (phiE6 p e) (hzc _ (xFixed_neg_thetaE6_mem_stdRankE6 p e))
  obtain ⟨hcu, hcv⟩ := commute_rootSL2_of_commute_phi_xFixed hu' hv'
  rw [← hA] at hcu hcv
  have hAu : A * uSL 1 = uSL 1 * A := hinj (by rw [map_mul, map_mul]; exact hcu)
  have hAv : A * vSL 1 = vSL 1 * A := hinj (by rw [map_mul, map_mul]; exact hcv)
  rcases eq_one_or_HSL_neg_one_of_commute_uSL_vSL one_ne_zero one_ne_zero hAu hAv with h | h
  · left
    rw [← hA, h, map_one]
  · right
    rw [← hA, h]
    exact rootTorusSL2_thetaE6 (-1)

theorem exists_phi_conj_sign_E6 (hp2 : p ≠ 2) (he : 1 ≤ e) {y g : ModGL .E6 (E6Closure p e)}
    (hyR : y ∈ fixedPointsIn (adjointGroup .E6 (E6Closure p e)) (frobE6 p e)) (hy2 : y ^ 2 = 1)
    (hg : g ∈ adjointGroup .E6 (E6Closure p e))
    (hgy : g * rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : (E6Closure p e)ˣ)) * g⁻¹ = y)
    (hyU : y * rootSL2 .E6 (E6Closure p e) thetaE6 (uSL 1) =
      rootSL2 .E6 (E6Closure p e) thetaE6 (uSL 1) * y)
    (hyV : y * rootSL2 .E6 (E6Closure p e) thetaE6 (vSL 1) =
      rootSL2 .E6 (E6Closure p e) thetaE6 (vSL 1) * y) :
    ∃ x : twistedE6Group p e,
      phiE6 p e x * rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : (E6Closure p e)ˣ)) =
        rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : (E6Closure p e)ˣ)) * phiE6 p e x ∧
      phiE6 p e x * y * (phiE6 p e x)⁻¹ ∈ e6SignDiagonalGroup (E6Closure p e) := by
  classical
  have hfin : Finite (GaloisField p (2 * e)) := Nat.finite_of_card_ne_zero (by
    rw [card_galoisField_two_mul' p e he]
    exact (pow_pos (pow_pos (Fact.out : p.Prime).pos e) _).ne')
  have hk : ringChar (E6Closure p e) ≠ 2 := by rw [ringChar.eq (E6Closure p e) p]; exact hp2
  have halg := isAlgebraic_zmod_E6Closure (p := p) (e := e)
  obtain ⟨hyG, hFy⟩ := mem_fixedPointsIn.1 hyR
  have hyL : y ∈ parabolicLevi .E6 (E6Closure p e) JE6 :=
    mem_parabolicLevi_of_commute_rootSL2_E6 hk hyG hyU hyV
  rcases exists_levi_fixed_conj_or_eq_thetaDiag_E6 halg hp2 he hyL hy2 hFy hg hgy hyU with
    hyd | ⟨h, hhL, hFh, hhy⟩
  · refine ⟨1, by simp, ?_⟩
    rw [map_one, one_mul, inv_one, mul_one, hyd]
    exact rootDiagUnit_thetaDiag_thetaE6_mem_sign
  · have hhG : h ∈ adjointGroup .E6 (E6Closure p e) :=
      parabolicSubgroup_le_adjointGroup _ _ _ (parabolicLevi_le_parabolicSubgroup JE6 hhL)
    obtain ⟨u, huT, x, hx⟩ : ∃ u : ModGL .E6 (E6Closure p e), u ∈ torusGroup .E6 (E6Closure p e) ∧
        ∃ x : twistedE6Group p e, h = u * phiE6 p e x := by
      obtain ⟨u, huT, -, x, hx⟩ := exists_torus_mul_of_mem_fixedPointsIn p e hp2 he
        (mem_fixedPointsIn.2 ⟨hhG, hFh⟩)
      exact ⟨u, huT, x, hx⟩
    have hΦx : phiE6 p e x = u⁻¹ * h := eq_inv_mul_of_mul_eq hx.symm
    refine ⟨x, ?_, ?_⟩
    · rw [hΦx]
      have h1 := rootDiagUnit_thetaDiag_comm_levi' (τ := .E6) (k := E6Closure p e) thetaE6
        (-1 : (E6Closure p e)ˣ) (J := JE6) (fun j hj => iform_single_thetaE6_of_mem hj) hhL
      have h2 := rootDiagUnit_mul_comm_of_mem_torusGroup (τ := .E6)
        (thetaDiag thetaE6 (-1 : (E6Closure p e)ˣ)) (inv_mem huT)
      calc u⁻¹ * h * rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : (E6Closure p e)ˣ)) =
          u⁻¹ * (h * rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : (E6Closure p e)ˣ))) := by group
        _ = u⁻¹ * (rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : (E6Closure p e)ˣ)) * h) := by
          rw [h1]
        _ = (u⁻¹ * rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : (E6Closure p e)ˣ))) * h := by group
        _ = (rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : (E6Closure p e)ˣ)) * u⁻¹) * h := by
          rw [h2]
        _ = _ := by group
    · rw [hΦx]
      have h3 := rootDiagUnit_mul_comm_of_mem_torusGroup (τ := .E6)
        (thetaDiag alpha4E6 (-1 : (E6Closure p e)ˣ)) (inv_mem huT)
      have h4 : u⁻¹ * h * y * (u⁻¹ * h)⁻¹ =
          rootDiagUnit .E6 (thetaDiag alpha4E6 (-1 : (E6Closure p e)ˣ)) := by
        calc u⁻¹ * h * y * (u⁻¹ * h)⁻¹ = u⁻¹ * (h * y * h⁻¹) * u := by group
          _ = u⁻¹ * rootDiagUnit .E6 (thetaDiag alpha4E6 (-1 : (E6Closure p e)ˣ)) * u := by
            rw [hhy]
          _ = (rootDiagUnit .E6 (thetaDiag alpha4E6 (-1 : (E6Closure p e)ˣ)) * u⁻¹) * u := by
            rw [h3]
          _ = _ := by group
      rw [h4]
      exact rootDiagUnit_thetaDiag_alpha4E6_mem_sign

theorem rootDiagUnit_thetaDiag_thetaE6_mul_self :
    rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : (E6Closure p e)ˣ)) *
      rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : (E6Closure p e)ˣ)) = 1 := by
  obtain ⟨b, hb, hbd⟩ := rootDiagUnit_thetaDiag_thetaE6_mem_sign (k := E6Closure p e)
  rw [show rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : (E6Closure p e)ˣ)) =
    rootDiagUnit TwistTag.E6.tag (fun l => b (CFSG.LieType.Steinberg.TwistedE6.orbitMap l)) from
    hbd]
  exact rootDiagUnit_mul_self_of_sign (E6Closure p e) hb

theorem twistedE6_hbase (hp2 : p ≠ 2) (he : 1 ≤ e) {c₁ c₂ : twistedE6Group p e}
    (hc₁ : c₁ ∈ stdRankE6 p e) (hc₁c : ∀ r ∈ stdRankE6 p e, c₁ * r = r * c₁)
    (hc₂c : ∀ r ∈ stdRankE6 p e, c₂ * r = r * c₂)
    (hconj : ∃ g z : twistedE6Group p e, z ∈ stdRankE6 p e ∧
      (∀ r ∈ stdRankE6 p e, z * r = r * z) ∧ c₂ = g * z * g⁻¹) :
    ∃ x : twistedE6Group p e, x * c₁ * x⁻¹ ∈ twistedE6SignGroup' p e ∧
      x * c₂ * x⁻¹ ∈ twistedE6SignGroup' p e := by
  classical
  obtain ⟨g, z, hz, hzc, hc₂⟩ := hconj
  have hΦ1 : phiE6 p e c₁ ∈ e6SignDiagonalGroup (E6Closure p e) := by
    rcases phiE6_center_stdRankE6 hp2 he hc₁ hc₁c with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact rootDiagUnit_thetaDiag_thetaE6_mem_sign
  rcases phiE6_center_stdRankE6 hp2 he hz hzc with h1 | h1
  ·
    have hzcen : z ∈ Subgroup.center (twistedE6Group p e) :=
      ker_twistedE6Phi_le_center p e (E6Closure p e) (by rw [MonoidHom.mem_ker]; exact h1)
    have hc₂z : c₂ = z := by
      rw [hc₂]
      calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [Subgroup.mem_center_iff.1 hzcen g]
        _ = z := by group
    refine ⟨1, ?_, ?_⟩
    · show phiE6 p e (1 * c₁ * 1⁻¹) ∈ e6SignDiagonalGroup (E6Closure p e)
      simpa using hΦ1
    · show phiE6 p e (1 * c₂ * 1⁻¹) ∈ e6SignDiagonalGroup (E6Closure p e)
      rw [hc₂z]
      simp only [one_mul, inv_one, mul_one, h1]
      exact one_mem _
  ·
    have hyR : phiE6 p e c₂ ∈ fixedPointsIn (adjointGroup .E6 (E6Closure p e)) (frobE6 p e) :=
      twistedE6Phi_mem_fixedPointsIn p e hp2 he c₂
    have hgR : phiE6 p e g ∈ adjointGroup .E6 (E6Closure p e) :=
      (mem_fixedPointsIn.1 (twistedE6Phi_mem_fixedPointsIn p e hp2 he g)).1
    have hgy : phiE6 p e g * rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : (E6Closure p e)ˣ)) *
        (phiE6 p e g)⁻¹ = phiE6 p e c₂ := by
      rw [hc₂, map_mul, map_mul, map_inv, h1]
    have hy2 : phiE6 p e c₂ ^ 2 = 1 := by
      rw [sq, ← hgy]
      calc phiE6 p e g * rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : (E6Closure p e)ˣ)) *
            (phiE6 p e g)⁻¹ * (phiE6 p e g * rootDiagUnit .E6 (thetaDiag thetaE6
              (-1 : (E6Closure p e)ˣ)) * (phiE6 p e g)⁻¹) =
          phiE6 p e g * (rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : (E6Closure p e)ˣ)) *
            rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : (E6Closure p e)ˣ))) *
              (phiE6 p e g)⁻¹ := by group
        _ = 1 := by rw [rootDiagUnit_thetaDiag_thetaE6_mul_self]; group
    have hyU := map_comm_of_comm (phiE6 p e) (hc₂c _ (xFixed_thetaE6_mem_stdRankE6 p e))
    have hyV := map_comm_of_comm (phiE6 p e) (hc₂c _ (xFixed_neg_thetaE6_mem_stdRankE6 p e))
    obtain ⟨hyU', hyV'⟩ := commute_rootSL2_of_commute_phi_xFixed hyU hyV
    obtain ⟨x, hxd, hxs⟩ := exists_phi_conj_sign_E6 hp2 he hyR hy2 hgR hgy hyU' hyV'
    refine ⟨x, ?_, ?_⟩
    · show phiE6 p e (x * c₁ * x⁻¹) ∈ e6SignDiagonalGroup (E6Closure p e)
      rw [map_mul, map_mul, map_inv]
      rcases phiE6_center_stdRankE6 hp2 he hc₁ hc₁c with h | h
      · rw [h, mul_one, mul_inv_cancel]
        exact one_mem _
      · rw [h, hxd, mul_assoc, mul_inv_cancel, mul_one]
        exact rootDiagUnit_thetaDiag_thetaE6_mem_sign
    · show phiE6 p e (x * c₂ * x⁻¹) ∈ e6SignDiagonalGroup (E6Closure p e)
      rw [map_mul, map_mul, map_inv]
      exact hxs

end Phi

end CFSG.ClassicalInvolution.ModelFacts.LeviE6
