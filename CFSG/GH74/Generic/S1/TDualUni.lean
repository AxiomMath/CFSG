module

public import CFSG.GH74.Generic.S1.TDualLin
public import CFSG.GH74.Generic.S1.TExoticUni

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic Matrix
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.GH74.Generic.S1.SymBlocksUni
open scoped MatrixGroups

section UniExotic

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem no_exotic_of_fixed_q8_uni (hF : Nat.card F = (p ^ f) ^ 2) (hq : 2 ≤ p ^ f) (h2 : (2 : F) ≠ 0)
    (β : MulAut ↥(StatedSU 4 (p ^ f) F)) (Φ : QuaternionGroup 2 →* ↥(StatedSU 4 (p ^ f) F))
    (hΦ : Function.Injective Φ) (hfix : ∀ g, β (Φ g) = Φ g) :
    ¬ IsExoticUni (StatedSU 4 (p ^ f) F) (p ^ f) β := by
  rintro ⟨bar, g, hbar, hgu, hgs, hgd, hβ⟩
  have hbarσ : ∀ x : F, bar x = unitaryInvolution F p f x := fun x => by
    rw [hbar, unitaryInvolution_apply]
  have hunit : ∀ s : QuaternionGroup 2,
      (((Φ s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map bar)ᵀ *
        ((Φ s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    intro s
    have h := (unitary_of_mem_statedSU hF (Φ s)).2
    have hm : ((Φ s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map bar =
        ((Φ s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map (unitaryInvolution F p f) := by
      ext i j
      simp only [Matrix.map_apply, hbarσ]
    rw [hm]
    exact h
  have hcom : ∀ s : QuaternionGroup 2,
      ((Φ s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) =
        (g : Matrix (Fin 4) (Fin 4) F) *
          ((Φ s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map bar := by
    intro s
    have h1 := hβ (Φ s)
    rw [hfix s] at h1
    have h2' : (Φ s : GL (Fin 4) F) * g = g * Matrix.GeneralLinearGroup.map bar (Φ s : GL (Fin 4) F) := by
      have := congrArg (fun m => m * g) h1
      simpa [mul_assoc] using this
    have h3 := congrArg (fun m : GL (Fin 4) F => (m : Matrix (Fin 4) (Fin 4) F)) h2'
    simpa [Units.val_mul, Matrix.GeneralLinearGroup.map_apply] using h3
  have hiso : ∀ s : QuaternionGroup 2,
      ((Φ s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
        ((Φ s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = (g : Matrix (Fin 4) (Fin 4) F) := by
    intro s
    have h1 := congrArg Matrix.transpose (hunit s)
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h1
    have hMM : ((Φ s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map bar *
        ((Φ s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := mul_eq_one_comm.1 h1
    calc ((Φ s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          ((Φ s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ
        = (g : Matrix (Fin 4) (Fin 4) F) * ((Φ s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map bar *
          ((Φ s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := by rw [hcom s]
      _ = (g : Matrix (Fin 4) (Fin 4) F) := by rw [Matrix.mul_assoc, hMM, Matrix.mul_one]
  have hσ : ∀ s : QuaternionGroup 2,
      (g : Matrix (Fin 4) (Fin 4) F) * ((Φ s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ =
        (((Φ s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ).map bar * (g : Matrix (Fin 4) (Fin 4) F) := by
    intro s
    have h1 := congrArg Matrix.transpose (hcom s)
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hgs, ← Matrix.transpose_map] at h1
    exact h1
  set I : Matrix (Fin 4) (Fin 4) F := ((Φ (QuaternionGroup.a 1) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hI
  set J : Matrix (Fin 4) (Fin 4) F := ((Φ (QuaternionGroup.xa 0) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hJ
  set Z : Matrix (Fin 4) (Fin 4) F := ((Φ (QuaternionGroup.a 2) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hZ
  have cm : ∀ s t : ↥(StatedSU 4 (p ^ f) F), s = t → ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := fun s t h => by rw [h]
  have rII : I * I = Z := by
    have h := cm (Φ (QuaternionGroup.a 1) * Φ (QuaternionGroup.a 1)) (Φ (QuaternionGroup.a 2))
      (by rw [← map_mul, q8_rel1])
    rw [mat_mul_coe] at h
    exact h
  have rJJ : J * J = Z := by
    have h := cm (Φ (QuaternionGroup.xa 0) * Φ (QuaternionGroup.xa 0)) (Φ (QuaternionGroup.a 2))
      (by rw [← map_mul, q8_rel2])
    rw [mat_mul_coe] at h
    exact h
  have rZZ : Z * Z = 1 := by
    have h := cm (Φ (QuaternionGroup.a 2) * Φ (QuaternionGroup.a 2)) 1
      (by rw [← map_mul, q8_rel3, map_one])
    rw [mat_mul_coe] at h
    exact h
  have rJI : J * I = Z * (I * J) := by
    have h := cm (Φ (QuaternionGroup.xa 0) * Φ (QuaternionGroup.a 1))
      (Φ (QuaternionGroup.a 2) * (Φ (QuaternionGroup.a 1) * Φ (QuaternionGroup.xa 0)))
      (by rw [← map_mul, ← map_mul, ← map_mul, q8_rel4])
    rw [mat_mul_coe, mat_mul_coe, mat_mul_coe] at h
    exact h
  have rZ1 : Z ≠ 1 := by
    intro h
    apply q8_ne
    apply hΦ
    rw [map_one]
    apply Subtype.ext
    apply Units.ext
    exact h
  have hZI : Z * I = I * Z := by rw [← rII, Matrix.mul_assoc]
  have hZJ : Z * J = J * Z := by rw [← rJJ, Matrix.mul_assoc]
  refine no_q8_isometry_uni hF hq h2 bar hbar (G := (g : Matrix (Fin 4) (Fin 4) F)) (a := Iᵀ)
    (b := Jᵀ) (z := Zᵀ) hgs hgu hgd ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using hiso (QuaternionGroup.a 1)
  · simpa using hiso (QuaternionGroup.xa 0)
  · exact hσ (QuaternionGroup.a 1)
  · exact hσ (QuaternionGroup.xa 0)
  · rw [← Matrix.transpose_mul, rII]
  · rw [← Matrix.transpose_mul, rJJ]
  · rw [← Matrix.transpose_mul, rZZ, Matrix.transpose_one]
  · intro h
    apply rZ1
    have := congrArg Matrix.transpose h
    simpa using this
  · have hc : Z * (I * J) = (I * J) * Z := by
      rw [← Matrix.mul_assoc, hZI, Matrix.mul_assoc, hZJ, ← Matrix.mul_assoc]
    calc Iᵀ * Jᵀ = (J * I)ᵀ := by rw [Matrix.transpose_mul]
      _ = (Z * (I * J))ᵀ := by rw [rJI]
      _ = ((I * J) * Z)ᵀ := by rw [hc]
      _ = Zᵀ * (Jᵀ * Iᵀ) := by rw [Matrix.transpose_mul, Matrix.transpose_mul]


theorem exists_q8_uniBlk (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) {c d : Fin 4} (hcd : c ≠ d) :
    ∃ q8 : QuaternionGroup 2 →* ↥(StatedSU 4 (p ^ f) F), Function.Injective q8 ∧
      ∀ g, q8 g ∈ uniBlk F (p ^ f) c d := by
  obtain ⟨e1⟩ := CFSG.ClassicalInvolution.Models.nonempty_sl2_mulEquiv_su_two (K := F) (p := p)
    (f := f) hF
  obtain ⟨e2⟩ := nonempty_equiv_uniBlk hF hcd
  have hodd : Odd (Nat.card ↥(CFSG.LieType.Steinberg.fixedSubfield F p f)) :=
    CFSG.ClassicalInvolution.Models.odd_natCard_fixedSubfield hF hp2
  have h2 : (2 : ↥(CFSG.LieType.Steinberg.fixedSubfield F p f)) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hK2 : ringChar ↥(CFSG.LieType.Steinberg.fixedSubfield F p f) ≠ 2 :=
    ringChar_ne_two_of_two_ne_zero h2
  obtain ⟨a, b, hab⟩ := (CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.odd_field_two_dimensional_quaternion_matrices
    hK2).1
  let qh : QuaternionGroup 2 →* SL(2, ↥(CFSG.LieType.Steinberg.fixedSubfield F p f)) :=
    CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.quatHom hab
  have hqh : Function.Injective qh :=
    CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.quatHom_injective hK2 hab
  refine ⟨(uniBlk F (p ^ f) c d).subtype.comp (e2.toMonoidHom.comp (e1.toMonoidHom.comp qh)), ?_,
    fun g => (e2 (e1 (qh g))).2⟩
  exact (uniBlk F (p ^ f) c d).subtype_injective.comp (e2.injective.comp (e1.injective.comp hqh))

end UniExotic


section UniPair

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem not_exotic_uni_of_frame (hExact : S1LiftExactProp) {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S1Setup G x K) (hfront : S1Front G x K) {u : Fin 4 → G}
    {hu : ∀ k, u k ∈ centralizer ({x} : Set G)} (hF : Nat.card F = (p ^ f) ^ 2) (hq : (p ^ f) % 4 = 1)
    (hp2 : p ≠ 2) (e : ↥K ≃* ↥(StatedSU 4 (p ^ f) F))
    (hact : ∀ k, ActsAsReflOn e (barOf (hu k)) (reflDiag F k))
    (i j : Fin 5) {K' : Subgroup (CentralizerBar (symX x u i))} [K'.Normal]
    (hfront' : S1Front G (symX x u i) K')
    (hv : symX x u j ∈ centralizer ({symX x u i} : Set G)) (e' : ↥K' ≃* ↥(StatedSU 4 (p ^ f) F)) :
    ¬ IsExoticUni (StatedSU 4 (p ^ f) F) (p ^ f)
      (MulAut.congr e' (MulAut.conjNormal (barOf hv) : MulAut ↥K')) := by
  classical
  have hq1 : 1 < p ^ f := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF] at h1
    by_contra hle
    have hle' : p ^ f ≤ 1 := by omega
    interval_cases hpf : p ^ f <;> simp at h1
  have hq5 : 5 ≤ p ^ f := by omega
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (Nat.odd_iff.2 (by omega : p ^ f % 2 = 1)).pow
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  obtain ⟨c, d, hcd, hci, hcj, hdi, hdj⟩ := choose_coords i j
  set D := layerDataOf hExact hset hfront e with hD
  have hactD : ∀ k, ActsAsReflOn D.iso (barOf (hu k)) (reflDiag F k) := hact
  obtain ⟨q8, hq8, hq8blk⟩ := exists_q8_uniBlk hF hp2 hcd
  have hgood : ⁅uniBlk F (p ^ f) c d, uniBlk F (p ^ f) c d⁆ = uniBlk F (p ^ f) c d ∨
      (OddGenerated (uniBlk F (p ^ f) c d) ∧ ThreeModel ↥K') :=
    Or.inl (uniBlk_perfect hF hq5 hcd)
  have hcomm : ∀ s ∈ uniBlk F (p ^ f) c d, ∀ k, k ≠ c → k ≠ d →
      (s : GL (Fin 4) F) * reflDiag F k = reflDiag F k * (s : GL (Fin 4) F) :=
    fun s hs k hkc hkd => uniBlk_comm_refl hkc hkd hs
  have hy : ∀ s ∈ uniBlk F (p ^ f) c d, D.ι s * symX x u i = symX x u i * D.ι s :=
    fun s hs => ι_comm_symX D hu hactD (uniBlk F (p ^ f) c d) hcomm hci hdi hs
  have hvc : ∀ s ∈ uniBlk F (p ^ f) c d, D.ι s * symX x u j = symX x u j * D.ι s :=
    fun s hs => ι_comm_symX D hu hactD (uniBlk F (p ^ f) c d) hcomm hcj hdj hs
  obtain ⟨Φ, hΦ, hfix⟩ :=
    exists_fixed_q8 D (uniBlk F (p ^ f) c d) hfront' hgood q8 hq8 hq8blk hy hv hvc e'
  exact no_exotic_of_fixed_q8_uni hF (by omega) h2 _ Φ hΦ hfix

end UniPair


section UniSym

variable {G : Type} [Group G] [Finite G]

theorem outer_reflection_uni_of_noExotic {y : G} {K : Subgroup (CentralizerBar y)} [K.Normal]
    (hset : S1Setup G y K) (hfront : S1Front G y K) {v : G} (hv : v ∈ centralizer ({y} : Set G))
    (hconj : IsConj y v) (hvy : v ≠ y) (hv2 : v * v = 1) (hvK : barOf hv ∉ K) {q : ℕ} {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1) (e : ↥K ≃* ↥(StatedSU 4 q F))
    (hNoExo : ¬ IsExoticUni (StatedSU 4 q F) q (MulAut.congr e (MulAut.conjNormal (barOf hv) : MulAut ↥K))) :
    IsReflection (StatedSU 4 q F) (MulAut.congr e (MulAut.conjNormal (barOf hv) : MulAut ↥K)) := by
  have hxK : xbar y ∈ K := hset.shape.2
  have hcentle : Subgroup.centralizer (K : Set (CentralizerBar y)) ≤ K := by
    rw [hfront.cent_eq]
    exact (Subgroup.zpowers_le).2 hxK
  obtain ⟨hα2, hout⟩ := conjNormal_involutory hcentle hv hv2 hvK
  have hnotA := not_goodFixed_conjNormal hset.inv hxK hfront hv hconj hvy hv2
  have hback : ∀ (hA : GoodFixedCentral False
      (MulAut.congr e (MulAut.conjNormal (barOf hv) : MulAut ↥K))), False := fun hA => by
    apply hnotA
    have h1 := (hA.of_mulEquiv e.symm).mono (T' := ThreeModel ↥K) (fun h => h.elim)
    rwa [congr_symm_congr] at h1
  rcases uniClassify F q hF hq (MulAut.congr e (MulAut.conjNormal (barOf hv) : MulAut ↥K))
    (congr_mul_self_eq_one e hα2) (congr_not_inner e hout) with hA | hR | hG
  · exact (hback hA).elim
  · exact hR
  · rcases graphUniRefine F q hF hq (MulAut.congr e (MulAut.conjNormal (barOf hv) : MulAut ↥K))
      (congr_mul_self_eq_one e hα2) hG with hA | hE
    · exact (hback hA).elim
    · exact (hNoExo hE).elim

theorem s1_symFrame_uni_dual (hExact : S1LiftExactProp) {x : G} {K : Subgroup (CentralizerBar x)}
    [K.Normal] (hset : S1Setup G x K) (hfront : S1Front G x K) {u : Fin 4 → G}
    {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu)
    {q : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1)
    (e : ↥K ≃* ↥(StatedSU 4 q F)) (hact : ∀ k, ActsAsReflOn e (barOf (hu k)) (reflDiag F k)) :
    S1SymFrameUni x u q F := by
  obtain ⟨p, f, hud, hqpf, hp2⟩ := FrameUni.exists_unitaryFieldData hF hq
  have : Fact p.Prime := ⟨hud.prime⟩
  have : CharP F p := hud.charP
  subst hqpf
  intro i
  obtain ⟨hy, hw, hw2, hwc, hwconj, hwne, hind2, hind3, hprod⟩ :=
    sym_hyps hset.shape.2 hset.inv hf i
  obtain ⟨K', hset', hfront', h1, h2', h3, h4, e'', he''⟩ :=
    sym_at_dual hset hfront (uniOps hF hq) e
      (fun y v => ∃ m n : Fin 5, m ≠ n ∧ y = symX x u m ∧ v = symX x u n)
      (fun y K' _ hs hfr e' v hv hgd hc hvy hv2 hvK => by
        obtain ⟨m, n, hmn, rfl, rfl⟩ := hgd
        exact outer_reflection_uni_of_noExotic hs hfr hv hc hvy hv2 hvK hF hq e'
          (not_exotic_uni_of_frame hExact hset hfront hF hq hp2 e hact m n hfr hv e'))
      hy (fun j => symX x u (i.succAbove j)) hw
      (fun j => ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm, rfl, rfl⟩) hw2 hwc hwconj hwne hind2
      hind3 hprod
  exact ⟨K', hw, hset', hfront', ⟨h1, h2', h3, h4, Or.inr ⟨p ^ f, F, inferInstance, inferInstance,
    e'', hF, hq, he''⟩⟩, e'', he''⟩

end UniSym

end CFSG.GH74.Generic.S1
