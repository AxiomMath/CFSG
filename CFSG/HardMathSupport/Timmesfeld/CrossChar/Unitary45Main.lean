module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary45Mono
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary45Chars
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary32Main

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.HardMathSupport.Timmesfeld.Balance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.RankThree.PartOne.KCUnitaryOne

private theorem isElemAbelian_comap' {M N : Type*} [Group M] [Group N] (φ : M →* N)
    (hφ : Function.Injective φ) {p : ℕ} {E : Subgroup N} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap φ) := CFSG.Open.IsElemAbelian.comap hE hφ

section Delta

variable {M : Type*} [Group M] {p : ℕ}

theorem conj_mem_localDeltaIn {H D : Subgroup M} {u c : M} (hu : u ∈ localDeltaIn p H D)
    (hcH : c ∈ H) (hcD : ∀ d ∈ D, c * d = d * c) : c * u * c⁻¹ ∈ localDeltaIn p H D := by
  unfold localDeltaIn
  simp only [Subgroup.mem_iInf]
  intro d hd hd1
  have h1 := le_core_of_mem_localDeltaIn hu hd hd1
  refine GLAPPrimeCoreOf_conj_mem c ?_ u h1
  refine Subgroup.mem_inf.2 ⟨hcH, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hcD d hd

end Delta

section Helpers

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem idForm_mulVec_of_mem (A : primeFormUnitary h (idGram K n)) (v w : Fin n → K) :
    idForm h n (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)
      (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) = idForm h n v w :=
  (mem_sesqUnitaryGroup.mp (toLinU_mem A)) v w

@[expose] noncomputable def torusSU {b₁ b₂ : Fin n → K} (hb : IsONPair h b₁ b₂) (c : Kˣ)
    (hc : h.norm (c : K) = 1) : gramSU h (idGram K n) :=
  ⟨(torusUnitary h hb c hc : primeFormUnitary h (idGram K n)),
    (mem_gramSU_iff_unitary h).2 ⟨(torusUnitary h hb c hc).2, det_torusUnitary h hb c hc⟩⟩

theorem coe_torusSU {b₁ b₂ : Fin n → K} (hb : IsONPair h b₁ b₂) (c : Kˣ)
    (hc : h.norm (c : K) = 1) :
    (((torusSU hb c hc : gramSU h (idGram K n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      torusMat h b₁ b₂ c := rfl

theorem eigen_cube_eq_one (hq : ℓ ^ f = 2) (A : primeFormUnitary h (idGram K n))
    {v : Fin n → K} (hv : idForm h n v v = 1) {a : K}
    (hA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = a • v) : a ^ 3 = 1 := by
  have h1 := idForm_mulVec_of_mem A v v
  rw [hA, hv] at h1
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hv] at h1
  have h3 : h.norm a = 1 := by
    rw [UnitaryFieldData.norm]
    simpa using h1
  rwa [norm_eq_cube h hq] at h3

theorem pow_three_eq_one_of_eigen (b : Module.Basis (Fin n) K (Fin n → K)) (A : GL (Fin n) K)
    (hA : ∀ l, ∃ a : K, a ^ 3 = 1 ∧ ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b l =
      a • b l) : A ^ 3 = 1 := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply b.ext
  intro k
  obtain ⟨a, ha3, hk⟩ := hA k
  have key : ∀ v : Fin n → K, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = a • v →
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)) = a ^ 3 • v := by
    intro v hv
    simp only [hv, Matrix.mulVec_smul, smul_smul]
    congr 1
    ring
  have e2 := key _ hk
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Units.val_pow_eq_pow_val, pow_three',
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e2, ha3, one_smul]
  simp

structure EigData (h : UnitaryFieldData ℓ f K) (n : ℕ)
    (Dh : Subgroup (gramSU h (idGram K n))) where
  b : Module.Basis (Fin n) K (Fin n → K)
  hb : IsOrthonormalFamily h b
  c : Fin n → ↥Dh →* Kˣ
  hc : ∀ (k : Fin n) (x : ↥Dh),
    (((x : gramSU h (idGram K n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b k =
      (c k x : K) • b k
  hcls : ∀ i j l : Fin n, i ≠ j → i ≠ l → j ≠ l → ¬ (c i = c j ∧ c i = c l)

theorem torusSU_comm {Dh : Subgroup (gramSU h (idGram K n))} (E : EigData h n Dh)
    {i j : Fin n} (hij : i ≠ j) (c : Kˣ) (hc : h.norm (c : K) = 1)
    (x : ↥Dh) :
    torusSU (E.hb.pair hij) c hc * (x : gramSU h (idGram K n)) =
      (x : gramSU h (idGram K n)) * torusSU (E.hb.pair hij) c hc := by
  apply Subtype.ext
  apply Units.ext
  change torusMat h (E.b i) (E.b j) c *
    (((x : gramSU h (idGram K n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
    (((x : gramSU h (idGram K n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      torusMat h (E.b i) (E.b j) c
  apply Matrix.toLin'.injective
  apply E.b.ext
  intro k
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    E.hc, torusMat_mulVec_basis h E.hb hij, Matrix.mulVec_smul, Matrix.mulVec_smul,
    torusMat_mulVec_basis h E.hb hij, E.hc, smul_smul, smul_smul, mul_comm]

theorem eq_one_of_innerLift_mem_localDeltaIn (hq : ℓ ^ f = 2) (hn2 : 2 ≤ n)
    {Dh : Subgroup (gramSU h (idGram K n))} (E : EigData h n Dh)
    {D H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hmap : Dh.map (innerLift h n) = D)
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H)
    (hinj : Function.Injective (innerLift h n)) (hDne : ∃ d ∈ D, d ≠ 1)
    {s : gramSU h (idGram K n)} (hs : innerLift h n s ∈ localDeltaIn 3 H D) : s = 1 := by
  classical
  have := h.finite
  have : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have hscomm : ∀ x : ↥Dh, s * (x : gramSU h (idGram K n)) = (x : gramSU h (idGram K n)) * s := by
    intro x
    have := commute_of_mem_localDeltaIn hs (d := innerLift h n x)
      (by rw [← hmap]; exact Subgroup.mem_map_of_mem _ x.2)
    apply hinj
    rw [map_mul, map_mul]
    exact this
  have hcops : Nat.Coprime 3 (orderOf s) := by
    obtain ⟨d, hd, hd1⟩ := hDne
    have := coprime_orderOf_of_mem_localDeltaIn Nat.prime_three hs hd hd1
    rwa [orderOf_injective (innerLift h n) hinj s] at this
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root h hq
  have hωn : h.norm (ω : K) = 1 := by
    rw [norm_eq_cube h hq, ← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hcop : ∀ (i j : Fin n) (hij : i ≠ j),
      Nat.Coprime 3 (orderOf ((((s : gramSU h (idGram K n)) : GL (Fin n) K)) *
        torusGL h (E.hb.pair hij) ω * (((s : gramSU h (idGram K n)) : GL (Fin n) K))⁻¹ *
        (torusGL h (E.hb.pair hij) ω)⁻¹)) := by
    intro i j hij
    set T : gramSU h (idGram K n) := torusSU (E.hb.pair hij) ω hωn with hT
    have hTH : innerLift h n T ∈ H := by
      apply hH
      rw [← range_innerLift_eq]
      exact ⟨T, rfl⟩
    have hTD : ∀ d ∈ D, innerLift h n T * d = d * innerLift h n T := by
      intro d hd
      rw [← hmap] at hd
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hd
      rw [← map_mul, ← map_mul]
      exact congrArg _ (torusSU_comm E hij ω hωn ⟨x, hx⟩)
    have h1 := conj_mem_localDeltaIn (inv_mem hs) hTH hTD
    have h2 : innerLift h n (s * T * s⁻¹ * T⁻¹) ∈ localDeltaIn 3 H D := by
      have : innerLift h n (s * T * s⁻¹ * T⁻¹) = innerLift h n s *
          (innerLift h n T * (innerLift h n s)⁻¹ * (innerLift h n T)⁻¹) := by
        simp only [map_mul, map_inv]
        group
      rw [this]
      exact mul_mem hs h1
    obtain ⟨d, hd, hd1⟩ := hDne
    have h3 := coprime_orderOf_of_mem_localDeltaIn Nat.prime_three h2 hd hd1
    rw [orderOf_injective (innerLift h n) hinj] at h3
    have h4 := Subgroup.orderOf_coe (s * T * s⁻¹ * T⁻¹)
    rw [← h4] at h3
    simpa [hT, torusSU, torusUnitary] using h3
  have hcls : ∀ i j l : Fin n, i ≠ j → i ≠ l → j ≠ l →
      ¬ ∀ g : ↥Dh, (E.c i g : K) = (E.c j g : K) ∧ (E.c i g : K) = (E.c l g : K) := by
    intro i j l hij hil hjl hall
    refine E.hcls i j l hij hil hjl ⟨?_, ?_⟩
    · ext g; exact (hall g).1
    · ext g; exact (hall g).2
  have hdiag := fun l => diag_of_coprime_commutators h hq hn2 E.hb
    (fun x : ↥Dh => (((x : gramSU h (idGram K n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (fun (x : ↥Dh) k => (E.c k x : K)) (fun x k => E.hc k x) hcls
    ((s : gramSU h (idGram K n)) : GL (Fin n) K)
    (idForm_mulVec_of_mem (liftUnitary s))
    (fun x => by
      have := congrArg (fun z : gramSU h (idGram K n) =>
        ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (hscomm x).symm
      simpa using this)
    ω hω3 hω1 hcop l
  have hs3 : ((s : gramSU h (idGram K n)) : GL (Fin n) K) ^ 3 = 1 := by
    refine pow_three_eq_one_of_eigen E.b _ fun l => ?_
    obtain ⟨a, ha⟩ := hdiag l
    exact ⟨a, eigen_cube_eq_one hq (liftUnitary s) (by rw [E.hb l l, ite_eq_left rfl]) ha, ha⟩
  have hs3' : s ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hs3
  have h1 : orderOf s ∣ 3 := orderOf_dvd_of_pow_eq_one hs3'
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcops.symm h1)

end Helpers

section Main

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem localDeltaIn_eq_bot_three_two_small (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2)
    (hn : n = 4 ∨ n = 5)
    (D : Subgroup (MulAut (primeFormP h (idGram K n)))) (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 27)
    (hDinn : D ≤ (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range)
    {H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H) :
    localDeltaIn 3 H D = ⊥ := by
  classical
  have := h.finite
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hn3 : 3 ≤ n := by omega
  have hne : ¬(n = 3 ∧ ℓ ^ f = 2) := fun h' => by omega
  have h3n : ¬ 3 ∣ n := by omega
  have hℓ : ℓ = 2 := by
    have : ℓ ∣ 2 := hq ▸ dvd_pow_self ℓ (by have := h.one_le; omega)
    exact (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this
  have hpℓ : 3 ≠ ℓ := by omega
  have hpq : 3 ∣ ℓ ^ f + 1 := by rw [hq]
  have hZp := noTorsion_of_not_dvd hp3 h3n h
  have hinj := innerLift_injective_three_two h hn3 hne hq h3n
  set Dh : Subgroup (gramSU h (idGram K n)) := D.comap (innerLift h n) with hDh
  have hDrange : D ≤ (innerLift h n).range := by rw [range_innerLift_eq]; exact hDinn
  have hmap : Dh.map (innerLift h n) = D := Subgroup.map_comap_eq_self hDrange
  have hDhel : IsElemAbelian 3 Dh := isElemAbelian_comap' _ hinj hD
  have hDhc : Nat.card Dh = 27 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hcard]
  have : IsElementaryAbelian 3 Dh :=
    { toIsMulCommutative := hDhel.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (hDhel.2 x x.2) }
  have : Finite Dh := Nat.finite_of_card_ne_zero (by rw [hDhc]; norm_num)
  obtain ⟨b, hbON, hbeig⟩ := exists_orthonormal_eigenbasis_of_elem hp3 hpq Dh
  have hb0 : ∀ i, b i ≠ 0 := fun i => b.ne_zero i
  have hchar : ∀ i : Fin n, ∃ χ : ↥Dh →* Kˣ, ∀ x : ↥Dh,
      xlin h n x.1 (b i) = (χ x : K) • b i := fun i =>
    exists_charHom (planeRep h n Dh) (hb0 i) (fun x => hbeig x.1 x.2 i)
  choose c hc using hchar
  have hc3 : ∀ i (x : ↥Dh), c i x ^ 3 = 1 := fun i x => by
    have hx : x ^ 3 = 1 := Subtype.ext (hDhel.2 x.1 x.2)
    rw [← map_pow, hx, map_one]
  have : Fintype ↥Dh := Fintype.ofFinite _
  have hX : ∀ (k : Fin n) (x : ↥Dh),
      (((x : gramSU h (idGram K n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b k =
        (c k x : K) • b k := fun k x => hc k x
  have hfaith : ∀ x : ↥Dh, (∀ k, c k x = 1) → x = 1 := by
    intro x hx
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    apply Matrix.toLin'.injective
    apply b.ext
    intro k
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hX k x, hx k]
    simp
  have hdet : ∀ x : ↥Dh, ∏ k, c k x = 1 := by
    intro x
    have h1 : (((x : gramSU h (idGram K n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 :=
      x.1.2.2
    have h2 : LinearMap.toMatrix b b (Matrix.toLin'
        (((x : gramSU h (idGram K n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
          Matrix.diagonal (fun k => (c k x : K)) := by
      ext i j
      rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, hX j x, map_smul, Module.Basis.repr_self,
        Finsupp.smul_apply, Finsupp.single_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij, Ne.symm hij]
    have h3 := LinearMap.det_toMatrix b (Matrix.toLin'
        (((x : gramSU h (idGram K n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    rw [h2, Matrix.det_diagonal, LinearMap.det_toLin', h1] at h3
    apply Units.ext
    rw [Units.coe_prod, h3, Units.val_one]
  have hcls : ∀ i j l : Fin n, i ≠ j → i ≠ l → j ≠ l → ¬ (c i = c j ∧ c i = c l) :=
    fun i j l hij hil hjl => no_three_equal_chars hDhc hn c hc3 hfaith hdet hij hil hjl
  let E : EigData h n Dh := ⟨b, hbON, c, hX, hcls⟩
  have hDne : ∃ d ∈ D, d ≠ 1 := by
    have : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
    obtain ⟨d, hd⟩ := exists_ne (1 : D)
    exact ⟨d, d.2, fun h1 => hd (Subtype.ext h1)⟩
  have hstep2 : ∀ s : gramSU h (idGram K n), innerLift h n s ∈ localDeltaIn 3 H D → s = 1 :=
    fun s hs => eq_one_of_innerLift_mem_localDeltaIn hq (by omega) E hmap hH hinj hDne hs
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root h hq
  have hωn : h.norm (ω : K) = 1 := by
    rw [norm_eq_cube h hq, ← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  obtain ⟨⟨M, τ⟩, hgM⟩ := surjective_primeFormPsi_of_ne (h := h) (n := n) hn3 hne g
  have hcent : ∀ x ∈ Dh, g * primeFormConjHom h (idGram K n) (liftUnitary x) =
      primeFormConjHom h (idGram K n) (liftUnitary x) * g := by
    intro x hx
    refine commute_of_mem_localDeltaIn hg ?_
    rw [← hmap, primeFormConjHom_liftUnitary]
    exact ⟨x, hx, (innerLift_apply x)⟩
  have hact : ∀ Y : Matrix (Fin n) (Fin n) K, idAct' h n hn3 hne g Y =
      ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Y.map τ *
        (((M : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    intro Y
    rw [← hgM, idAct'_primeFormPsi, idMatAction_mk]
  have hMM : (((M : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have htor : ∀ (i j : Fin n) (hij : i ≠ j) (c : Kˣ) (hc : h.norm (c : K) = 1),
      ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (torusMat h (b i) (b j) c).map τ =
        torusMat h (b i) (b j) c * ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    intro i j hij c hc
    set T : gramSU h (idGram K n) := torusSU (hbON.pair hij) c hc with hT
    set y : primeFormUnitary h (idGram K n) := idActU' h n hn3 hne g (liftUnitary T) with hy
    have hymat : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        idAct' h n hn3 hne g ((T : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
      coe_idActU' hn3 hne g _
    have hdety : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
      rw [hymat]
      exact det_idAct' hn3 hne g T.2.2
    have hdetTi : ((((liftUnitary T : primeFormUnitary h (idGram K n)) : GL (Fin n) K)⁻¹ :
        GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
      have h1 : ((((liftUnitary T : primeFormUnitary h (idGram K n)) : GL (Fin n) K)⁻¹ :
          GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det *
          (((liftUnitary T : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K).det = 1 := by
        rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
      have h2 : (((liftUnitary T : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K).det = 1 := T.2.2
      rwa [h2, mul_one] at h1
    set W : primeFormUnitary h (idGram K n) := y * (liftUnitary T)⁻¹ with hW
    have hdetW : ((W : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
      rw [hW, Subgroup.coe_mul, Units.val_mul, Matrix.det_mul, hdety, one_mul]
      exact hdetTi
    let Ws : gramSU h (idGram K n) := ⟨W, (mem_gramSU_iff_unitary h).2 ⟨W.2, hdetW⟩⟩
    have hρT : primeFormConjHom h (idGram K n) (liftUnitary T) = innerLift h n T := by
      rw [primeFormConjHom_liftUnitary, innerLift_apply]
    have hWi : innerLift h n Ws = g * innerLift h n T * g⁻¹ * (innerLift h n T)⁻¹ := by
      have h1 : innerLift h n Ws = primeFormConjHom h (idGram K n) W := by
        rw [innerLift_apply, ← primeFormConjHom_liftUnitary]
        rfl
      rw [h1, hW, map_mul, map_inv, ← hρT, conj_primeFormConjHom' hn3 hne g (liftUnitary T)]
    have hTH : innerLift h n T ∈ H := by
      apply hH
      rw [← range_innerLift_eq]
      exact ⟨T, rfl⟩
    have hTD : ∀ d ∈ D, innerLift h n T * d = d * innerLift h n T := by
      intro d hd
      rw [← hmap] at hd
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hd
      rw [← map_mul, ← map_mul]
      exact congrArg _ (torusSU_comm E hij c hc ⟨x, hx⟩)
    have hWΔ : innerLift h n Ws ∈ localDeltaIn 3 H D := by
      rw [hWi]
      have h1 := conj_mem_localDeltaIn (inv_mem hg) hTH hTD
      have : g * innerLift h n T * g⁻¹ * (innerLift h n T)⁻¹ =
          g * (innerLift h n T * g⁻¹ * (innerLift h n T)⁻¹) := by group
      rw [this]
      exact mul_mem hg h1
    have hW1 := hstep2 Ws hWΔ
    have hy1 : y = liftUnitary T := by
      have h1 : W = 1 :=
        Subtype.ext (congrArg (fun z : gramSU h (idGram K n) => (z : GL (Fin n) K)) hW1)
      rw [hW, mul_inv_eq_one] at h1
      exact h1
    have h2 : idAct' h n hn3 hne g ((T : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((T : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← hymat, hy1]
      rfl
    rw [hact] at h2
    have hTm : ((T : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = torusMat h (b i) (b j) c :=
      coe_torusSU (hbON.pair hij) c hc
    rw [hTm] at h2
    calc ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (torusMat h (b i) (b j) c).map τ
        = (((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (torusMat h (b i) (b j) c).map τ *
          (((M : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
          ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          simp only [Matrix.mul_assoc, hMM, Matrix.mul_one]
      _ = torusMat h (b i) (b j) c * ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [h2]
  have hτ : τ = RingEquiv.refl K := by
    let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    let i2 : Fin n := ⟨2, by omega⟩
    have h01 : i0 ≠ i1 := fun h' => by simpa [i0, i1] using congrArg Fin.val h'
    have h02 : i0 ≠ i2 := fun h' => by simpa [i0, i2] using congrArg Fin.val h'
    have h12 : i1 ≠ i2 := fun h' => by simpa [i1, i2] using congrArg Fin.val h'
    exact tau_eq_one_of_torus (h := h) (M := ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (M : GL (Fin n) K).isUnit (hbON.pair h01) (hbON.pair h02)
      (hbON.linearIndependent_triple h01 h02 h12) (fun c hc => htor i0 i1 h01 c hc)
      (fun c hc => htor i0 i2 h02 c hc)
  subst hτ
  have hmat1 : ∀ Y : Matrix (Fin n) (Fin n) K, Y.map (RingEquiv.refl K) = Y := fun Y => by
    ext
    rfl
  have hMx : ∀ x : gramSU h (idGram K n), x ∈ Dh →
      ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    intro x hx
    have hxp : x ^ 3 = 1 := hDhel.2 x hx
    let L : PlaneData h n 3 x := ⟨hn3, hne, hp3, hpℓ, hZp, hxp⟩
    have hα : g * primeFormConjHom h (idGram K n) (liftUnitary x) * g⁻¹ =
        primeFormConjHom h (idGram K n) (liftUnitary x) := by
      rw [hcent x hx, mul_inv_cancel_right]
    have h1 := L.idAct'_eq_of_conj_eq g hα
    rw [hact, hmat1] at h1
    calc ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        = (((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (((M : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
          ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          simp only [Matrix.mul_assoc, hMM, Matrix.mul_one]
      _ = ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [h1]
  have hcls' : ∀ i j l : Fin n, i ≠ j → i ≠ l → j ≠ l →
      ¬ ∀ x : ↥Dh, (c i x : K) = (c j x : K) ∧ (c i x : K) = (c l x : K) := by
    intro i j l hij hil hjl hall
    refine hcls i j l hij hil hjl ⟨?_, ?_⟩
    · ext x; exact (hall x).1
    · ext x; exact (hall x).2
  have hcop : ∀ (i j : Fin n) (hij : i ≠ j),
      Nat.Coprime 3 (orderOf ((M : GL (Fin n) K) * torusGL h (hbON.pair hij) ω *
        (M : GL (Fin n) K)⁻¹ * (torusGL h (hbON.pair hij) ω)⁻¹)) := by
    intro i j hij
    have hMT : (M : GL (Fin n) K) * torusGL h (hbON.pair hij) ω =
        torusGL h (hbON.pair hij) ω * (M : GL (Fin n) K) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      have := htor i j hij ω hωn
      rw [hmat1] at this
      exact this
    rw [hMT]
    have : torusGL h (hbON.pair hij) ω * (M : GL (Fin n) K) * (M : GL (Fin n) K)⁻¹ *
        (torusGL h (hbON.pair hij) ω)⁻¹ = 1 := by group
    rw [this, orderOf_one]
    exact Nat.coprime_one_right _
  have hdiag := fun l => diag_of_coprime_commutators h hq (by omega : 2 ≤ n) hbON
    (fun x : ↥Dh => ((x : gramSU h (idGram K n)) : GL (Fin n) K).val)
    (fun (x : ↥Dh) k => (c k x : K)) (fun x k => hX k x) hcls' (M : GL (Fin n) K)
    (idForm_mulVec_of_mem M) (fun x => (hMx x x.2).symm) ω hω3 hω1 hcop l
  have hM3 : (M : GL (Fin n) K) ^ 3 = 1 := by
    refine pow_three_eq_one_of_eigen b _ fun l => ?_
    obtain ⟨a, ha⟩ := hdiag l
    exact ⟨a, eigen_cube_eq_one hq M (by rw [hbON l l, ite_eq_left rfl]) ha, ha⟩
  have hM3' : M ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hM3
  have hg3 : g ^ 3 = 1 := by
    have hgρ : g = primeFormConjHom h (idGram K n) M := by
      rw [primeFormConjHom_eq_primeFormPsi]
      exact hgM.symm
    rw [hgρ, ← map_pow, hM3', map_one]
  obtain ⟨d, hd, hd1⟩ := hDne
  have hcopg := coprime_orderOf_of_mem_localDeltaIn Nat.prime_three hg hd hd1
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcopg.symm (orderOf_dvd_of_pow_eq_one hg3))
