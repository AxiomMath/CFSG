module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Small
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3Aut
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3U3
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U3Frame
public import CFSG.ClassicalInvolution.Q3.TA3SmallModels

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2
open CFSG.ClassicalInvolution.Q3.TA3.Q5L3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix QuaternionGroup
open scoped MatrixGroups commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem tightEdgeless_of_sq_R (hD : TightDatum R S t) {N J : Subgroup Y} [N.Normal]
    (htN : t ∈ N) (hRJ : R ≤ Subgroup.centralizer (J : Set Y))
    {s : Y} (hsR : s ∈ R) (hsN : s ∈ N) (hs4 : orderOf s = 4)
    (hinv : ∀ v ∈ N, v ∈ Subgroup.centralizer ({t} : Set Y) →
      v ∈ Subgroup.centralizer (J : Set Y) → v * v = 1 → v = 1 ∨ v = t)
    (hsq : ∀ y ∈ N, y ∈ Subgroup.centralizer ({t} : Set Y) → y * y = t →
      y ∉ Subgroup.centralizer (J : Set Y) → y ∈ J) : TightEdgeless R := by
  obtain ⟨k, hk, ⟨eS⟩⟩ := hD.quat
  have : NeZero (2 ^ (k - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hev : Even (2 ^ (k - 2)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  set S₀ := (S : Subgroup R).map R.subtype with hS₀
  have ht1 : t ≠ 1 := fun h => by
    have := hD.order
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have htt : t * t = 1 := by rw [← pow_two, ← hD.order, pow_orderOf_eq_one]
  obtain ⟨r, hrR, hrs⟩ := TightDatum.exists_conj_mem_of_pow S hsR (k := 2)
    (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hs4, pow_orderOf_eq_one])
  set s' := r * s * r⁻¹ with hs'
  have hs'R : s' ∈ R := R.mul_mem (R.mul_mem hrR hsR) (R.inv_mem hrR)
  have hs'N : s' ∈ N := (inferInstance : N.Normal).conj_mem s hsN r
  have hs'4 : orderOf s' = 4 := by
    rw [hs', ← MulAut.conj_apply, MulEquiv.orderOf_eq, hs4]
  have hs'2 := TightDatum.sq_eq_of_orderOf_eq_four hD hs'R hs'4
  let eS₀ : S₀ ≃* QuaternionGroup (2 ^ (k - 2)) :=
    (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans eS
  obtain ⟨h, hh⟩ := quaternionGroup_exists_conj_eq_inv hev (eS₀ ⟨s', hrs⟩)
  set j : Y := ((eS₀.symm h : S₀) : Y) with hj
  have hjS : j ∈ S₀ := (eS₀.symm h).2
  have hjs : j * s' * j⁻¹ = s'⁻¹ := by
    have h1 : eS₀.symm h * ⟨s', hrs⟩ * (eS₀.symm h)⁻¹ = (⟨s', hrs⟩ : S₀)⁻¹ :=
      eS₀.injective (by simpa using hh)
    simpa [hj] using congrArg Subtype.val h1
  refine TightDatum.edgeless_of_forall hD fun P hP hPC => ?_
  obtain ⟨x, rfl⟩ := TightDatum.exists_eq_conjSub_of_mem_RSet hD hP
  set v := x⁻¹ * t * x with hv
  have hSv : ∀ g ∈ S₀, g * v = v * g := fun g hg => by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hPC (conj_mem_conjSub (n := x) hg))
    calc g * v = x⁻¹ * ((x * g * x⁻¹) * t) * x := by rw [hv]; group
      _ = x⁻¹ * (t * (x * g * x⁻¹)) * x := by rw [h1]
      _ = v * g := by rw [hv]; group
  have hvt : v = t := by
    by_contra hne
    have hvN : v ∈ N := by
      have := (inferInstance : N.Normal).conj_mem t htN x⁻¹
      rwa [inv_inv] at this
    have hv2 : v * v = 1 := by
      calc v * v = x⁻¹ * (t * t) * x := by rw [hv]; group
        _ = 1 := by rw [htt]; group
    have hvC : v ∈ Subgroup.centralizer ({t} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hSv t hD.mem).symm
    have hs'v : s' * v = v * s' := hSv s' hrs
    have hs'C : s' ∈ Subgroup.centralizer ({t} : Set Y) := hD.cent hs'R
    have hs'J : s' ∈ Subgroup.centralizer (J : Set Y) := hRJ hs'R
    have hyN : s' * v ∈ N := N.mul_mem hs'N hvN
    have hyC : s' * v ∈ Subgroup.centralizer ({t} : Set Y) := Subgroup.mul_mem _ hs'C hvC
    have hy2 : s' * v * (s' * v) = t := by
      calc s' * v * (s' * v) = s' * (v * s') * v := by group
        _ = s' * (s' * v) * v := by rw [hs'v]
        _ = s' * s' * (v * v) := by group
        _ = t := by rw [hs'2, hv2, mul_one]
    by_cases hyJ : s' * v ∈ Subgroup.centralizer (J : Set Y)
    · have hvJ : v ∈ Subgroup.centralizer (J : Set Y) := by
        have e : v = s'⁻¹ * (s' * v) := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hs'J) hyJ
      rcases hinv v hvN hvC hvJ hv2 with h1 | h1
      · apply ht1
        have e : t = x * v * x⁻¹ := by rw [hv]; group
        rw [e, h1]
        group
      · exact hne h1
    · have hyJ' := hsq _ hyN hyC hy2 hyJ
      have hjR : j ∈ R := Subgroup.map_subtype_le _ hjS
      have hjy : (s' * v) * j = j * (s' * v) :=
        Subgroup.mem_centralizer_iff.mp (hRJ hjR) _ hyJ'
      have hjv : j * v = v * j := hSv j hjS
      have e1 : s' * v = s'⁻¹ * v := by
        calc s' * v = j * (s' * v) * j⁻¹ := by rw [← hjy]; group
          _ = (j * s' * j⁻¹) * (j * v * j⁻¹) := by group
          _ = s'⁻¹ * v := by rw [hjs, hjv]; group
      have e2 : s' * s' = 1 := by
        have := mul_right_cancel e1
        calc s' * s' = s' * s'⁻¹ := by rw [← this]
          _ = 1 := mul_inv_cancel s'
      exact ht1 (hs'2.symm.trans e2)
  rw [mem_conjSub_iff, ← hv, hvt]
  exact hD.mem

variable {F : Type} [Field F] {H : Subgroup (GL (Fin 2) F)}

theorem tightEdgeless_of_gl2_R (hD : TightDatum R S t)
    {N : Subgroup Y} [N.Normal] {π : H →* Y}
    (hrange : π.range = N ⊓ Subgroup.centralizer ({t} : Set Y)) (hk : CubeKer π)
    (hcs : SLCentScalar H) {N1 : H} (hN1 : (N1 : GL (Fin 2) F) = -1) (hπ1 : π N1 = t)
    {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Odd (Nat.card F₀)) (h4 : 4 ≤ Nat.card F₀)
    (eJ : slPart H ≃* SL(2, F₀)) {s : Y} (hsR : s ∈ R) (hsN : s ∈ N) (hs4 : orderOf s = 4) :
    TightEdgeless R := by
  have hRJ := TightDatum.le_centralizer_of_gl2 hD hrange hk hF₀ h4 eJ
  have hval : ∀ y ∈ N, y ∈ Subgroup.centralizer ({t} : Set Y) → ∃ A : H, π A = y :=
    fun y hyN hyt => by
      have : y ∈ π.range := hrange ▸ ⟨hyN, hyt⟩
      exact this
  have htN : t ∈ N := by
    have : π N1 ∈ N ⊓ Subgroup.centralizer ({t} : Set Y) := hrange ▸ ⟨N1, rfl⟩
    rw [← hπ1]
    exact this.1
  have hscal : ∀ A : H, π A ∈ Subgroup.centralizer (((slPart H).map π : Subgroup Y) : Set Y) →
      ∃ c : Fˣ, (A : GL (Fin 2) F) = GeneralLinearGroup.scalar (Fin 2) c := fun A hA =>
    exists_scalar_of_commute hk hcs fun B hB =>
      (Subgroup.mem_centralizer_iff.mp hA (π B) ⟨B, hB, rfl⟩).symm
  have hcomm : ∀ A B : H, (∃ c : Fˣ, (A : GL (Fin 2) F) = GeneralLinearGroup.scalar (Fin 2) c) →
      π A * π B = π B * π A := by
    rintro A B ⟨c, hcA⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hcA, scalar_mul_comm]
  have hinv : ∀ v ∈ N, v ∈ Subgroup.centralizer ({t} : Set Y) →
      v ∈ Subgroup.centralizer (((slPart H).map π : Subgroup Y) : Set Y) → v * v = 1 →
        v = 1 ∨ v = t := by
    intro v hvN hvt hvJ hv2
    obtain ⟨A, rfl⟩ := hval v hvN hvt
    obtain ⟨c, hcA⟩ := hscal A hvJ
    rw [← hπ1]
    exact eq_or_of_scalar_sq hk hN1 hcA hv2
  have hsq : ∀ y ∈ N, y ∈ Subgroup.centralizer ({t} : Set Y) → y * y = t →
      y ∉ Subgroup.centralizer (((slPart H).map π : Subgroup Y) : Set Y) →
        y ∈ (slPart H).map π := by
    intro y hyN hyt hy2 hyJ
    obtain ⟨A, rfl⟩ := hval y hyN hyt
    refine mem_map_slPart_of_sq hk hN1 (by rw [hπ1]; exact hy2) fun c hcA => hyJ ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨B, -, rfl⟩
    exact (hcomm A B ⟨c, hcA⟩).symm
  exact tightEdgeless_of_sq_R hD htN hRJ hsR hsN hs4 hinv hsq

theorem smallLeafR_l3Ne3 (r : ℕ) : SmallLeafR r SmallL3Ne3 := by
  intro Y _ _ _ hnab _ hPF R S t hD _ _
  obtain ⟨p, f, hp, hp2, hf, h3, hm⟩ := hPF
  have : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot hnab
  set N := genFittingFStar Y with hN
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hm
  let e : ↥N ≃* projectiveSL 3 K :=
    (e₀.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    obtain ⟨k, hk⟩ := hodd
    omega
  have hoddK : Odd (Nat.card K) := hK ▸ hodd
  have h5K : 5 ≤ Nat.card K := hK ▸ h5
  let ι : Y →* MulAut (projectiveSL 3 K) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : Y →* MulAut ↥N)
  have hιapp : ∀ (y : Y) (n : ↥N), ι y (e n) = e (MulAut.conjNormal y n) := fun y n => by
    show e ((MulAut.conjNormal y) (e.symm (e n))) = _
    rw [MulEquiv.symm_apply_apply]
  have hιN : ∀ y : Y,
      ι y ∈ ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 K) → y ∈ N := by
    rintro y ⟨m, hm⟩
    have key : ∀ x : ↥N, (e.symm m : ↥N) * x * (e.symm m)⁻¹ = MulAut.conjNormal y x := by
      intro x
      apply e.injective
      have h1 := DFunLike.congr_fun hm (e x)
      rw [hιapp] at h1
      rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulAut.conj_apply]
    have hcen : ((e.symm m : ↥N) : Y)⁻¹ * y ∈ Subgroup.centralizer (N : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h2 := congrArg Subtype.val (key ⟨x, hx⟩)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply] at h2
      calc x * (((e.symm m : ↥N) : Y)⁻¹ * y) =
          ((e.symm m : ↥N) : Y)⁻¹ * (((e.symm m : ↥N) : Y) * x * ((e.symm m : ↥N) : Y)⁻¹) * y := by
            group
        _ = ((e.symm m : ↥N) : Y)⁻¹ * (y * x * y⁻¹) * y := by rw [h2]
        _ = ((e.symm m : ↥N) : Y)⁻¹ * y * x := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcen
    rw [← hcen]
    exact (e.symm m).2
  obtain ⟨φ, hφi, hφR, hφt⟩ := datum_exists_q8 hD
  have hq4 : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by decide
  have htN : t ∈ N := by
    have hq : (a 1 : QuaternionGroup 2) * xa 0 * (a 1)⁻¹ * (xa 0)⁻¹ = a 1 ^ 2 := by decide
    have ht' : t = φ (a 1) * φ (xa 0) * (φ (a 1))⁻¹ * (φ (xa 0))⁻¹ := by
      rw [← hφt, ← map_pow, ← hq, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hD' : ι t ∈ linearAutGroup 3 K := by
      rw [ht', map_mul ι, map_mul ι, map_mul ι, map_inv ι, map_inv ι]
      exact commutator_mem_linearAutGroup le_rfl _ _
    have ht2 : t ^ 2 = 1 := by rw [← hD.order, pow_orderOf_eq_one]
    have h2 : ι t ^ 2 ^ 1 = 1 := by rw [← map_pow, pow_one, ht2, map_one]
    exact hιN t (mem_inner_of_pow hD' h2)
  obtain ⟨Q, π, hrange, hk, hπ1, hπ⟩ := exists_frame hoddK e htN hD.order
  have hRJ := TightDatum.le_centralizer_of_gl2 hD hrange hk hoddK (by omega) slPartTopEquiv
  have hfix : ∀ g ∈ R, ∀ B : SL(2, K),
      ι g (proj 3 K ((blkP Q).comp SpecialLinearGroup.toGL B)) =
        proj 3 K ((blkP Q).comp SpecialLinearGroup.toGL B) := by
    intro g hg B
    let x : ↥N := e.symm (proj 3 K (blkP Q (SpecialLinearGroup.toGL B)))
    have hxJ : (x : Y) ∈ (slPart (⊤ : Subgroup (GL (Fin 2) K))).map π :=
      ⟨⟨SpecialLinearGroup.toGL B, Subgroup.mem_top _⟩,
        mem_slPart.mpr (SpecialLinearGroup.coeToGL_det B), hπ _⟩
    have hgx : (x : Y) * g = g * x := Subgroup.mem_centralizer_iff.mp (hRJ hg) _ hxJ
    have hconj : MulAut.conjNormal g x = x := Subtype.ext (by
      rw [MulAut.conjNormal_apply, ← hgx, mul_inv_cancel_right])
    have hex : proj 3 K (blkP Q (SpecialLinearGroup.toGL B)) = e x :=
      (MulEquiv.apply_symm_apply e _).symm
    show ι g (proj 3 K (blkP Q (SpecialLinearGroup.toGL B))) =
      proj 3 K (blkP Q (SpecialLinearGroup.toGL B))
    rw [hex, hιapp, hconj]
  have hs : ∃ s ∈ R, s ∈ N ∧ orderOf s = 4 := by
    have hE : ∃ q : QuaternionGroup 2, ¬ q ^ 2 ^ 1 = 1 ∧ ι (φ q) ∈ semilinearAutGroup 3 K := by
      by_cases ha : ι (φ (a 1)) ∈ semilinearAutGroup 3 K
      · exact ⟨a 1, by decide, ha⟩
      by_cases hb : ι (φ (xa 0)) ∈ semilinearAutGroup 3 K
      · exact ⟨xa 0, by decide, hb⟩
      refine ⟨a 1 * xa 0, by decide, ?_⟩
      rw [map_mul φ, map_mul ι]
      exact mul_mem_semilinearAutGroup ha hb
    obtain ⟨q, hq2, hqE⟩ := hE
    have hqD := mem_linearAutGroup_of_fix (by omega) ((blkP Q).comp SpecialLinearGroup.toGL)
      (trace_blkP Q) hqE (hfix _ (hφR q))
    have hq4' : ι (φ q) ^ 2 ^ 2 = 1 := by
      rw [← map_pow, ← map_pow, show (2 : ℕ) ^ 2 = 4 by norm_num, hq4, map_one, map_one]
    have hqN := hιN _ (mem_inner_of_pow hqD hq4')
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨φ q, hφR q, hqN, ?_⟩
    rw [orderOf_injective φ hφi q]
    exact orderOf_eq_prime_pow hq2 (by rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]; exact hq4 q)
  obtain ⟨s, hsR, hsN, hs4⟩ := hs
  exact tightEdgeless_of_gl2_R hD hrange hk slCentScalar_top (N1 := ⟨-1, _⟩) rfl
    hπ1 hoddK (by omega) slPartTopEquiv hsR hsN hs4

theorem smallLeafR_u3Ne3 (r : ℕ) : SmallLeafR r SmallU3Ne3 := by
  intro Y _ _ _ hnab _ hPF R S t hD _ _
  obtain ⟨p, f, hp, hp2, hf, h3, hm⟩ := hPF
  have : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot hnab
  have hg : Odd (Nat.gcd 3 (p ^ f + 1)) :=
    (by decide : Odd 3).of_dvd_nat (Nat.gcd_dvd_left 3 _)
  obtain ⟨htN, s, hsR, hsN, hs4⟩ :=
    TightDatum.exists_cyclic4_of_outTwoCyclic hD hC (outTwoCyclic_PSU hm hg)
  obtain ⟨⟨hℓ, hm1, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have h : UnitaryFieldData p f K := ⟨hℓ, hm1, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := h.charP
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    obtain ⟨k, hk⟩ := hodd
    omega
  have hq := LieType.Steinberg.card_fixedSubfield h.card_eq_sq
  obtain ⟨π, hrange, hk, hπ1⟩ := Q5U3.exists_frame h hp2 e htN hD.order
  obtain ⟨eJ⟩ := Q5U3.nonempty_slPart_equiv h
  exact tightEdgeless_of_gl2_R hD hrange hk (Q5U3.slCentScalar_GU2 h)
    (N1 := ⟨-1, Q5U3.neg_one_mem_GU2 h⟩) rfl hπ1 (by rw [hq]; exact hodd) (by rw [hq]; omega)
    eJ hsR hsN hs4

end CFSG.CGT.PushingUpLit.SolKNA.R4
