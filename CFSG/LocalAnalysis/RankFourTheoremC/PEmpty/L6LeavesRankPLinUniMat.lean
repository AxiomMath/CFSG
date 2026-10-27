module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPLinUniMon
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMonEmb
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreUnits

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP.LU

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore CFSG.SectionRank.OddCover Equiv Subgroup
open scoped commutatorElement

variable {F : Type} [Field F]

theorem det_eq_one_iff {n : ℕ} (x : GL (Fin n) F) :
    Matrix.GeneralLinearGroup.det x = 1 ↔ (x : Matrix (Fin n) (Fin n) F).det = 1 := by
  rw [Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]

theorem mul_scalar_comm {n : ℕ} (c : Fˣ) (g : GL (Fin n) F) :
    g * Matrix.GeneralLinearGroup.scalar (Fin n) c =
      Matrix.GeneralLinearGroup.scalar (Fin n) c * g := by
  have hc : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ Subgroup.center (GL (Fin n) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  exact Subgroup.mem_center_iff.1 hc g

theorem conj_scalar {n : ℕ} (c : Fˣ) (g : GL (Fin n) F) :
    g * Matrix.GeneralLinearGroup.scalar (Fin n) c * g⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  rw [mul_scalar_comm, mul_assoc, mul_inv_cancel, mul_one]

theorem exists_monScalar_of_emb_eq_scalar {C : Type} [CommGroup C] {n : ℕ} (hn : 1 ≤ n)
    {e : C →* Fˣ} (he : Function.Injective e) {y : Mon C n} {c : Fˣ}
    (h : monEmb e n y = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    ∃ z : C, y = monScalar C n z := by
  have hent : ∀ i j : Fin n, (if y.right⁻¹ i = j then (e (y.left i) : F) else 0) =
      if i = j then (c : F) else 0 := by
    intro i j
    rw [← coe_monEmb_apply, h, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply]
  have hσ : ∀ i, y.right⁻¹ i = i := by
    intro i
    have h1 := hent i (y.right⁻¹ i)
    rw [if_pos rfl] at h1
    by_contra hne
    rw [if_neg (Ne.symm hne)] at h1
    exact (e (y.left i)).ne_zero h1
  have hr : y.right = 1 := inv_eq_one.mp (Equiv.ext hσ)
  have hl : ∀ i, e (y.left i) = c := by
    intro i
    have h1 := hent i i
    rw [if_pos (hσ i), if_pos rfl] at h1
    exact Units.ext h1
  refine ⟨y.left ⟨0, hn⟩, ?_⟩
  rw [eq_monT_of_right_eq_one hr, monScalar_apply]
  congr 1
  funext i
  exact he ((hl i).trans (hl ⟨0, hn⟩).symm)

theorem exists_pGroup_ker_det [Finite F] {f n a m : ℕ} [Fact f.Prime]
    (hCa : Nat.card (unitsPPart F f) = f ^ a) (Γ : Subgroup (GL (Fin n) F))
    (hΓ : (Nat.card Γ).factorization f = m) :
    ∃ H : Subgroup (GL (Fin n) F), H ≤ Γ ∧ (∀ x ∈ H, Matrix.GeneralLinearGroup.det x = 1) ∧
      IsPGroup f H ∧ f ^ (m - a) ≤ Nat.card H := by
  classical
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow f Γ))
  let ι : (Q : Subgroup Γ) →* GL (Fin n) F := Γ.subtype.comp (Q : Subgroup Γ).subtype
  have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  let δ : (Q : Subgroup Γ) →* Fˣ := Matrix.GeneralLinearGroup.det.comp ι
  have hcard := Subgroup.card_ker_mul_card_range δ
  have hQcard : Nat.card (Q : Subgroup Γ) = f ^ m := by
    rw [Q.card_eq_multiplicity, hΓ]
  have hrange : Nat.card δ.range ≤ f ^ a := by
    rw [← hCa]
    apply Subgroup.card_le_of_le
    rintro _ ⟨x, rfl⟩
    obtain ⟨k, hk⟩ := Q.isPGroup' x
    refine ⟨k, ?_⟩
    rw [← map_pow, hk, map_one]
  have hker : f ^ (m - a) ≤ Nat.card δ.ker := by
    by_cases ham : a ≤ m
    · have hfa : 0 < f ^ a := pow_pos (Fact.out : f.Prime).pos _
      refine Nat.le_of_mul_le_mul_right ?_ hfa
      calc f ^ (m - a) * f ^ a = f ^ m := by rw [← pow_add, Nat.sub_add_cancel ham]
        _ = Nat.card δ.ker * Nat.card δ.range := by rw [← hQcard, hcard]
        _ ≤ Nat.card δ.ker * f ^ a := Nat.mul_le_mul_left _ hrange
    · rw [Nat.sub_eq_zero_of_le (by omega), pow_zero]
      exact Nat.card_pos
  refine ⟨δ.ker.map ι, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.1.2
  · rintro _ ⟨x, hx, rfl⟩
    exact hx
  · exact (Q.isPGroup'.to_subgroup δ.ker).map ι
  · rw [Subgroup.card_map_of_injective hι]
    exact hker

theorem exists_lift_of_monomial [Finite F] {f n a : ℕ} [Fact f.Prime] (hf2 : f ≠ 2) (hfn : f ∣ n)
    (hn : 4 ≤ n) (hCa : Nat.card (unitsPPart F f) = f ^ a) (ha : 1 ≤ a)
    (G : Subgroup (GL (Fin n) F)) (hGdet : ∀ x ∈ G, Matrix.GeneralLinearGroup.det x = 1)
    (hdiag : ∀ t : Fin n → unitsPPart F f, ∏ i, t i = 1 →
      diagHom n (fun i => ((t i : unitsPPart F f) : Fˣ)) ∈ G)
    (hconj : ∀ H : Subgroup (GL (Fin n) F), H ≤ G → IsPGroup f H →
      ∃ g : GL (Fin n) F, (∀ x ∈ H, g * x * g⁻¹ ∈ G) ∧
        ∀ x ∈ H, g * x * g⁻¹ ∈ (monEmb (unitsPPart F f).subtype n).range)
    {P₁ : Subgroup (GL (Fin n) F)} (hP₁G : P₁ ≤ G) (hP₁p : IsPGroup f P₁)
    (hP₁c : f ^ (a * (n - 1) + padicValNat f n.factorial) ≤ Nat.card P₁)
    {A₀ : GL (Fin n) F} (hA₀ : A₀ ∈ P₁)
    (hcomm : ∀ u ∈ P₁, ∃ c : Fˣ, ⁅A₀, u⁆ = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (hpow : ∃ c : Fˣ, A₀ ^ f = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    ∃ A ∈ G, A ^ f = 1 ∧ ∃ c : Fˣ, A = Matrix.GeneralLinearGroup.scalar (Fin n) c * A₀ := by
  classical
  have hCp : IsPGroup f (unitsPPart F f) := unitsPPart_isPGroup F f
  haveI : Nontrivial (unitsPPart F f) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hCa]
    exact Nat.one_lt_pow (by omega) (Fact.out : f.Prime).one_lt
  haveI : IsCyclic (unitsPPart F f) := unitsPPart_isCyclic F f
  let e : unitsPPart F f →* Fˣ := (unitsPPart F f).subtype
  have he : Function.Injective e := Subtype.val_injective
  let E := monEmb e n
  have hE : Function.Injective E := monEmb_injective he n
  obtain ⟨g, hgG, hgE⟩ := hconj P₁ hP₁G hP₁p
  let cg : GL (Fin n) F →* GL (Fin n) F := (MulAut.conj g).toMonoidHom
  have hcg : ∀ x, cg x = g * x * g⁻¹ := fun x => rfl
  let Q : Subgroup (GL (Fin n) F) := P₁.map cg
  have hcginj : Function.Injective cg := (MulAut.conj g).injective
  have hQmem : ∀ x ∈ Q, ∃ x' ∈ P₁, x = g * x' * g⁻¹ := by
    rintro _ ⟨x', hx', rfl⟩
    exact ⟨x', hx', rfl⟩
  have hQG : Q ≤ G := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := hQmem x hx
    exact hgG x' hx'
  have hQE : Q ≤ E.range := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := hQmem x hx
    exact hgE x' hx'
  have hQp : IsPGroup f Q := hP₁p.map cg
  have hQcard : Nat.card Q = Nat.card P₁ := Subgroup.card_map_of_injective hcginj
  let P : Subgroup (Mon (unitsPPart F f) n) := Q.comap E
  have hPmap : P.map E = Q := Subgroup.map_comap_eq_self hQE
  have hPp : IsPGroup f P := hQp.comap_of_injective E hE
  have hPcard : Nat.card P = Nat.card P₁ := by
    rw [← hQcard, ← hPmap, Subgroup.card_map_of_injective hE]
  have hodd : ∀ x ∈ P, Odd (orderOf x) := by
    intro x hx
    obtain ⟨k, hk⟩ := hPp ⟨x, hx⟩
    have h1 : x ^ (f ^ k) = 1 := by simpa using congrArg Subtype.val hk
    exact Odd.of_dvd_nat (((Fact.out : f.Prime).odd_of_ne_two hf2).pow)
      (orderOf_dvd_of_pow_eq_one h1)
  have hPdet : ∀ x ∈ P, monDet x = 1 := by
    intro x hx
    have h1 := monEmb_det_of_odd e x (hodd x hx)
    have h2 : Matrix.GeneralLinearGroup.det (E x) = 1 := hGdet _ (hQG hx)
    exact he (by rw [← h1]; exact h2.trans (map_one e).symm)
  have hgA₀Q : g * A₀ * g⁻¹ ∈ Q := ⟨A₀, hA₀, rfl⟩
  obtain ⟨x₀, hx₀E⟩ := hQE hgA₀Q
  have hx₀P : x₀ ∈ P := by
    show E x₀ ∈ Q
    rw [hx₀E]
    exact hgA₀Q
  have hcommMon : ∀ u ∈ P, ∃ z : unitsPPart F f, ⁅x₀, u⁆ = monScalar _ n z := by
    intro u hu
    obtain ⟨u', hu', hu'E⟩ := hQmem (E u) hu
    obtain ⟨c, hc⟩ := hcomm u' hu'
    have h1 : E ⁅x₀, u⁆ = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
      rw [map_commutatorElement, hx₀E, hu'E]
      have h2 : ⁅g * A₀ * g⁻¹, g * u' * g⁻¹⁆ = g * ⁅A₀, u'⁆ * g⁻¹ :=
        (map_commutatorElement cg A₀ u').symm
      rw [h2, hc, conj_scalar]
    obtain ⟨z, hz⟩ := exists_monScalar_of_emb_eq_scalar (by omega) he h1
    exact ⟨z, hz⟩
  have hpowMon : ∃ z : unitsPPart F f, x₀ ^ f = monScalar _ n z := by
    obtain ⟨c, hc⟩ := hpow
    have h1 : E (x₀ ^ f) = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
      rw [map_pow, hx₀E]
      have h2 : (g * A₀ * g⁻¹) ^ f = g * A₀ ^ f * g⁻¹ := (map_pow cg A₀ f).symm
      rw [h2, hc, conj_scalar]
    exact exists_monScalar_of_emb_eq_scalar (by omega) he h1
  have hcardMon : Nat.card (unitsPPart F f) ^ (n - 1) * f ^ padicValNat f n.factorial ≤
      Nat.card P := by
    rw [hCa, ← pow_mul, ← pow_add, hPcard]
    exact hP₁c
  obtain ⟨t, s, hxt, htf, htp⟩ := exists_diag_lift hf2 hCp hfn hn hPp hPdet hcardMon hx₀P
    hcommMon hpowMon
  let Â : GL (Fin n) F := diagHom n (fun i => ((t i : unitsPPart F f) : Fˣ))
  have hÂG : Â ∈ G := hdiag t htp
  have hET : E (monT t) = Â := monEmb_monT e t
  have hÂf : Â ^ f = 1 := by
    rw [← hET, ← map_pow]
    have h1 : (monT t) ^ f = 1 := by
      rw [← monT_pow]
      have : t ^ f = 1 := funext htf
      rw [this]
      exact map_one (SemidirectProduct.inl : (Fin n → unitsPPart F f) →* _)
    rw [h1, map_one]
  obtain ⟨sc, hsc⟩ : ∃ sc : GL (Fin n) F,
      sc = Matrix.GeneralLinearGroup.scalar (Fin n) (e s) := ⟨_, rfl⟩
  have hscomm : ∀ h : GL (Fin n) F, h * sc = sc * h := fun h => by
    rw [hsc]
    exact mul_scalar_comm _ h
  have hxE : g * A₀ * g⁻¹ = Â * sc := by
    rw [← hx₀E, hxt, map_mul, hET, monEmb_monScalar, hsc]
  have hscG : sc ∈ G := by
    have h1 : sc = Â⁻¹ * (g * A₀ * g⁻¹) := by
      rw [hxE, inv_mul_cancel_left]
    rw [h1]
    exact G.mul_mem (G.inv_mem hÂG) (hgG A₀ hA₀)
  have hAeq : sc⁻¹ * A₀ = g⁻¹ * Â * g := by
    calc sc⁻¹ * A₀ = sc⁻¹ * (g⁻¹ * (g * A₀ * g⁻¹) * g) := by group
      _ = sc⁻¹ * (g⁻¹ * (Â * sc) * g) := by rw [hxE]
      _ = sc⁻¹ * ((g⁻¹ * Â * g) * sc) := by
          rw [mul_assoc g⁻¹ (Â * sc) g, mul_assoc Â sc g, ← hscomm g]
          group
      _ = sc⁻¹ * (sc * (g⁻¹ * Â * g)) := by rw [hscomm]
      _ = g⁻¹ * Â * g := inv_mul_cancel_left sc _
  refine ⟨sc⁻¹ * A₀, G.mul_mem (G.inv_mem hscG) (hP₁G hA₀), ?_, (e s)⁻¹, ?_⟩
  · rw [hAeq]
    have h1 : (g⁻¹ * Â * g) ^ f = g⁻¹ * Â ^ f * g := by
      have := (map_pow (MulAut.conj g⁻¹).toMonoidHom Â f).symm
      simpa [MulAut.conj_apply] using this
    rw [h1, hÂf]
    group
  · rw [hsc, map_inv]

theorem exists_lift_of_cover {K' Ĝ : Type} [Group K'] [Group Ĝ] [Finite Ĝ] [Finite F]
    {f n a : ℕ} [Fact f.Prime] (hf2 : f ≠ 2) (hfn : f ∣ n) (hn : 4 ≤ n)
    (hCa : Nat.card (unitsPPart F f) = f ^ a) (ha : 1 ≤ a)
    (ι : Ĝ →* GL (Fin n) F) (hι : Function.Injective ι)
    (hGdet : ∀ x ∈ ι.range, Matrix.GeneralLinearGroup.det x = 1)
    (hdiag : ∀ t : Fin n → unitsPPart F f, ∏ i, t i = 1 →
      diagHom n (fun i => ((t i : unitsPPart F f) : Fˣ)) ∈ ι.range)
    (hconj : ∀ H : Subgroup (GL (Fin n) F), H ≤ ι.range → IsPGroup f H →
      ∃ g : GL (Fin n) F, (∀ x ∈ H, g * x * g⁻¹ ∈ ι.range) ∧
        ∀ x ∈ H, g * x * g⁻¹ ∈ (monEmb (unitsPPart F f).subtype n).range)
    (hSyl : ∃ H : Subgroup (GL (Fin n) F), H ≤ ι.range ∧ IsPGroup f H ∧
      f ^ (a * (n - 1) + padicValNat f n.factorial) ≤ Nat.card H)
    (ψ : Ĝ →* K') (hψ : Function.Surjective ψ)
    (hker : ∀ s, ψ s = 1 ↔ ∃ c : Fˣ, ι s = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    {z : K'} (hz : orderOf z = f) (S : Sylow f K') (hzS : z ∈ (S : Subgroup K'))
    (hcen : ∀ s ∈ (S : Subgroup K'), z * s = s * z) :
    ∃ A : Ĝ, A ^ f = 1 ∧ ψ A = z := by
  classical
  obtain ⟨P, hPS⟩ := Sylow.mapSurjective_surjective hψ f S
  have hPmap : (P : Subgroup Ĝ).map ψ = (S : Subgroup K') := by
    rw [← hPS, Sylow.coe_mapSurjective]
  obtain ⟨H, hHle, hHp, hHc⟩ := hSyl
  have hPc : f ^ (a * (n - 1) + padicValNat f n.factorial) ≤ Nat.card (P : Subgroup Ĝ) := by
    refine hHc.trans ?_
    have hHmap : (H.comap ι).map ι = H := Subgroup.map_comap_eq_self hHle
    have hH'p : IsPGroup f (H.comap ι) := hHp.comap_of_injective ι hι
    obtain ⟨Q, hQ⟩ := hH'p.exists_le_sylow
    have hcardH : Nat.card H = Nat.card (H.comap ι) := by
      have h1 := Subgroup.card_map_of_injective hι (K := H.comap ι)
      rwa [hHmap] at h1
    calc Nat.card H = Nat.card (H.comap ι) := hcardH
      _ ≤ Nat.card (Q : Subgroup Ĝ) := Subgroup.card_le_of_le hQ
      _ = Nat.card (P : Subgroup Ĝ) := by rw [Q.card_eq_multiplicity, P.card_eq_multiplicity]
  obtain ⟨A₀, hA₀P, hA₀z⟩ : ∃ A₀ ∈ (P : Subgroup Ĝ), ψ A₀ = z := by
    have := hzS
    rw [← hPmap] at this
    exact Subgroup.mem_map.1 this
  have hz1 : z ^ f = 1 := hz ▸ pow_orderOf_eq_one z
  have hP₁p : IsPGroup f ((P : Subgroup Ĝ).map ι) := P.isPGroup'.map ι
  have hP₁c : Nat.card ((P : Subgroup Ĝ).map ι) = Nat.card (P : Subgroup Ĝ) :=
    Subgroup.card_map_of_injective hι
  obtain ⟨Â, hÂG, hÂf, c, hÂc⟩ := exists_lift_of_monomial hf2 hfn hn hCa ha ι.range hGdet hdiag
    hconj (P₁ := (P : Subgroup Ĝ).map ι) (Subgroup.map_le_range ι _) hP₁p (hP₁c ▸ hPc)
    (A₀ := ι A₀) (Subgroup.mem_map_of_mem ι hA₀P)
    (fun u hu => by
      obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
      have h1 : ψ ⁅A₀, u'⁆ = 1 := by
        rw [map_commutatorElement, hA₀z, commutatorElement_eq_one_iff_mul_comm]
        exact hcen _ (hPmap ▸ Subgroup.mem_map_of_mem ψ hu')
      obtain ⟨c, hc⟩ := (hker _).1 h1
      exact ⟨c, by rw [← map_commutatorElement, hc]⟩)
    (by
      have h1 : ψ (A₀ ^ f) = 1 := by rw [map_pow, hA₀z, hz1]
      obtain ⟨c, hc⟩ := (hker _).1 h1
      exact ⟨c, by rw [← map_pow, hc]⟩)
  obtain ⟨A, rfl⟩ := hÂG
  refine ⟨A, hι (by rw [map_pow, hÂf, map_one]), ?_⟩
  have h1 : ψ (A₀⁻¹ * A) = 1 := by
    rw [hker]
    refine ⟨c, ?_⟩
    rw [map_mul, map_inv, hÂc, ← mul_assoc, mul_scalar_comm c (ι A₀)⁻¹, mul_assoc, inv_mul_cancel,
      mul_one]
  rw [map_mul, map_inv, hA₀z, inv_mul_eq_one] at h1
  exact h1.symm

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP.LU
