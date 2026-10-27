module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3ModelB
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofD4
import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofPairingU3Zs
import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarD4Cent
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuter
import CFSG.HardMathSupport.Dickson.I271.Support.EngineKL
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Types
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Conj
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingFusionCorrBridge
import CFSG.CGT.T75P.SylowSplit
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

section Restrict

variable {G : Type*} [Group G]

@[expose] noncomputable def triD4_restrictAut (ψ : MulAut G) (H : Subgroup G)
    (hH : H.map ψ.toMonoidHom = H) : MulAut ↥H :=
  (ψ.subgroupMap H).trans (MulEquiv.subgroupCongr hH)

theorem triD4_restrictAut_apply (ψ : MulAut G) (H : Subgroup G)
    (hH : H.map ψ.toMonoidHom = H) (x : ↥H) : ((triD4_restrictAut ψ H hH x : ↥H) : G) = ψ x :=
  rfl

theorem triD4_restrictAut_pow (ψ : MulAut G) (H : Subgroup G)
    (hH : H.map ψ.toMonoidHom = H) (n : ℕ) (x : ↥H) :
    (((triD4_restrictAut ψ H hH ^ n) x : ↥H) : G) = (ψ ^ n) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, triD4_restrictAut_apply, pow_succ, MulAut.mul_apply]

theorem triD4_map_eq_of_le [Finite G] (ψ : MulAut G) {H : Subgroup G}
    (hH : ∀ x ∈ H, ψ x ∈ H) : H.map ψ.toMonoidHom = H := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    exact hH x hx
  · rw [Subgroup.card_map_of_injective ψ.injective]

theorem triD4_map_centralizer_le (ψ : MulAut G) {H : Subgroup G}
    (hH : H.map ψ.toMonoidHom = H) {x : G} (hx : x ∈ Subgroup.centralizer (H : Set G)) :
    ψ x ∈ Subgroup.centralizer (H : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro h hh
  have hh' : h ∈ H.map ψ.toMonoidHom := hH.symm ▸ hh
  obtain ⟨h₀, hh₀, rfl⟩ := hh'
  change ψ h₀ * ψ x = ψ x * ψ h₀
  rw [← map_mul, ← map_mul, hx h₀ hh₀]

theorem triD4_fix_of_perfect {H : Subgroup G} (hperf : commutator ↥H = ⊤) {β : MulAut G}
    (hβH : ∀ j ∈ H, β j ∈ H)
    (hc : ∀ j ∈ H, ∀ h ∈ H, (j * (β j)⁻¹) * h = h * (j * (β j)⁻¹)) :
    ∀ j ∈ H, β j = j := by
  have hcH : ∀ j ∈ H, j * (β j)⁻¹ ∈ H := fun j hj => H.mul_mem hj (H.inv_mem (hβH j hj))
  let f : ↥H →* ↥(Subgroup.center ↥H) :=
    { toFun := fun j => ⟨⟨(j : G) * (β j)⁻¹, hcH j j.2⟩, Subgroup.mem_center_iff.2 fun h =>
        Subtype.ext (hc j j.2 h h.2).symm⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        apply Subtype.ext
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        have h1 := hc y y.2 (β x)⁻¹ (H.inv_mem (hβH x x.2))
        calc (x : G) * y * ((β y)⁻¹ * (β x)⁻¹) = x * ((y * (β y)⁻¹) * (β x)⁻¹) := by group
          _ = x * ((β x)⁻¹ * (y * (β y)⁻¹)) := by rw [h1]
          _ = x * (β x)⁻¹ * (y * (β y)⁻¹) := by group }
  have hker : commutator ↥H ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (Subgroup.mem_center_iff.1 (f y).2 (f x : ↥H))
  intro j hj
  have h1 : (⟨j, hj⟩ : ↥H) ∈ f.ker := hker (hperf ▸ Subgroup.mem_top _)
  have h2 : (j : G) * (β j)⁻¹ = 1 := by
    have h3 := congrArg (fun z : ↥(Subgroup.center ↥H) => ((z : ↥H) : G)) (MonoidHom.mem_ker.1 h1)
    exact h3
  exact (mul_inv_eq_one.1 h2).symm

end Restrict

section Model

theorem triD4_modelB_of {K : Type} [Field K] [Finite K] {Q : ℕ} {σ δ : K ≃+* K}
    (hK : Nat.card K = Q ^ 3) (hσ : ∀ c, σ c = c ^ Q) (hQ2 : ¬ 2 ∣ Q) (hQ3 : ¬ 3 ∣ Q)
    (hδ3 : δ ^ 3 = 1) (hδ1 : δ ≠ 1)
    (hmem : ∀ x ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom,
      fieldActor σ δ x ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom)
    (hinv : ∃ t ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom,
      t ≠ 1 ∧ t ^ 2 = 1 ∧
      (∀ x ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom,
        x * t = t * x) ∧ fieldActor σ δ t = t)
    (hlay : GLAPLayer 3 (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom ⊓
      fixSubgroup (fieldActor σ δ)) ≠ ⊥) :
    ModelB (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (fieldActor σ δ) := by
  classical
  set C₀ := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC₀
  set J := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom with hJdef
  set ψ : MulAut C₀ := fieldActor σ δ with hψdef
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ℓ, f, hℓ, hf, hQℓ⟩ :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.exists_prime_pow_of_card_eq_cube hK
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hf0 : f ≠ 0 := by omega
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    exact hQ2 (hQℓ ▸ dvd_pow_self 2 hf0)
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    exact hQ3 (hQℓ ▸ dvd_pow_self 3 hf0)
  have hKℓ : Nat.card K = (ℓ ^ f) ^ 3 := hQℓ ▸ hK
  have hσℓ : ∀ c, σ c = c ^ (ℓ ^ f) := fun c => hQℓ ▸ hσ c
  have hσ3 : σ ^ 3 = 1 := by
    apply RingEquiv.ext
    intro c
    have : Fintype K := Fintype.ofFinite K
    change σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    have h1 : Q * (Q * Q) = Fintype.card K := by
      rw [← Nat.card_eq_fintype_card, hK]
      ring
    rw [h1, FiniteField.pow_card]
  have hQ1 : 1 < Q := by
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    rw [hK] at h2
    by_contra h
    have hQ : Q ≤ 1 := by omega
    have : Q ^ 3 ≤ 1 := by
      calc Q ^ 3 ≤ 1 ^ 3 := Nat.pow_le_pow_left hQ 3
        _ = 1 := by norm_num
    omega
  have hQ5 : 5 ≤ Q := by
    by_contra h
    interval_cases Q <;> omega
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ Q := by omega
      _ ≤ Q ^ 3 := Nat.le_self_pow (by norm_num) Q
  have hψ3 : ψ ^ 3 = 1 := by
    change (fieldActorHom (t := TwistTag.D4) σ δ) ^ 3 = 1
    rw [← map_pow, hδ3, map_one]
  obtain ⟨-, -, ⟨Θ, hΘ, -, -, -⟩, -⟩ :=
    CFSG.LieType.Chevalley.odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf K hKℓ σ hσℓ
  have hψout : ψ ∉ (MulAut.conj : C₀ →* MulAut C₀).range := by
    rintro ⟨g, hg⟩
    have h1 : Θ ψ = 1 := hΘ ψ g 1 (by rw [← hg, fieldActor_one, mul_one])
    have h2 : Θ ψ = δ := hΘ ψ 1 δ (by rw [map_one, one_mul])
    exact hδ1 (h2.symm.trans h1)
  have hψk : ∀ k : ℕ, k < 3 → k ≠ 0 → ψ ^ k ∉ (MulAut.conj : C₀ →* MulAut C₀).range := by
    intro k hk hk0 hmemk
    interval_cases k
    · exact hk0 rfl
    · rw [pow_one] at hmemk
      exact hψout hmemk
    · apply hψout
      have h2 : ψ = (ψ ^ 2)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ']
        exact hψ3
      rw [h2]
      exact Subgroup.inv_mem _ hmemk
  have hJmap : J.map ψ.toMonoidHom = J := triD4_map_eq_of_le ψ hmem
  set M := Subgroup.centralizer (J : Set C₀) with hMdef
  have hMmap : M.map ψ.toMonoidHom = M :=
    triD4_map_eq_of_le ψ fun x hx => triD4_map_centralizer_le ψ hJmap hx
  have hJq : CFSG.Open.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.UnbalancingLocal.isQuasisimple_open_iff _).2
      (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.isQuasisimple_d4ShortSL2 hσ3 hK4)
  have h3Q : 3 ∣ Q ^ 2 - 1 := by
    have h := Nat.pow_mod Q 2 3
    have hr : Q % 3 = 1 ∨ Q % 3 = 2 := by omega
    have h1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
    rcases hr with hr | hr <;> rw [hr] at h <;> omega
  have hJ3 : 3 ∣ Nat.card J := by
    rw [hJdef, CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.card_d4ShortSL2 hσ3, hK]
    apply Dvd.dvd.mul_left
    have : (Q ^ 3) ^ 2 - 1 = (Q ^ 2 - 1) * (Q ^ 4 + Q ^ 2 + 1) := by
      have h1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [h1, Nat.one_le_pow 2 (Q ^ 3) (by positivity)]
      ring
    rw [this]
    exact Dvd.dvd.mul_right h3Q _
  have hM3 : 3 ∣ Nat.card M := by
    obtain ⟨F, _, _, -, hF, ⟨eM⟩⟩ :=
      CFSG.RankThree.PartTwo.Sec11.Item1120V0Bar.nonempty_mulEquiv_centralizer_d4ShortSL2
        (ℓ := ℓ) (f := f) hf hℓ3 hKℓ hσℓ
    rw [hMdef, ← Nat.card_congr eM.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      hF, ← hQℓ]
    exact Dvd.dvd.mul_left h3Q _
  obtain ⟨r', hr'fix, hr'ord⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_orderOf_eq_prime_mem_fixSubgroup
    Nat.prime_three (triD4_restrictAut ψ M hMmap)
    (MulEquiv.ext fun x => Subtype.ext (by rw [triD4_restrictAut_pow, hψ3]; rfl)) hM3
  obtain ⟨q', hq'fix, hq'ord⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_orderOf_eq_prime_mem_fixSubgroup
    Nat.prime_three (triD4_restrictAut ψ J hJmap)
    (MulEquiv.ext fun x => Subtype.ext (by rw [triD4_restrictAut_pow, hψ3]; rfl)) hJ3
  set r : C₀ := (r' : C₀) with hrdef
  set qb : C₀ := (q' : C₀) with hqbdef
  have hrM : r ∈ M := r'.2
  have hqJ : qb ∈ J := q'.2
  have hψr : ψ r = r := congrArg Subtype.val hr'fix
  have hψq : ψ qb = qb := congrArg Subtype.val hq'fix
  have hr3 : orderOf r = 3 := by rw [hrdef, Subgroup.orderOf_coe, hr'ord]
  have hq3 : orderOf qb = 3 := by rw [hqbdef, Subgroup.orderOf_coe, hq'ord]
  have hrJ : ∀ j ∈ J, j * r = r * j := fun j hj =>
    (Subgroup.mem_centralizer_iff.1 hrM j hj)
  have hZJ3 : ∀ y ∈ J, y ∈ M → y ^ 3 = 1 → y = 1 := fun y hy hyM hy3 =>
    CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofU3Zs.d4ShortSL2_central_eq_one hσ3 hy hyM hy3
  set A₁ := Subgroup.zpowers r with hA₁
  set A := A₁ ⊔ Subgroup.zpowers qb with hA
  have hcommrq : ∀ x ∈ A₁, ∀ y ∈ Subgroup.zpowers qb, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow ((hrJ qb hqJ).symm) m n).eq
  have hzel : ∀ x : C₀, orderOf x = 3 → IsElemAbelian 3 (Subgroup.zpowers x) := by
    intro x hx
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
      simp only [Subgroup.coe_mul]
      rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx, pow_orderOf_eq_one,
        one_zpow]
  have hAel : IsElemAbelian 3 A := (hzel r hr3).sup_of_commute (hzel qb hq3) hcommrq
  have hAinf : A₁ ⊓ Subgroup.zpowers qb = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy₁, hy₂⟩
    rw [Subgroup.mem_bot]
    have hyM : y ∈ M := (Subgroup.zpowers_le.2 hrM) hy₁
    have hyJ : y ∈ J := (Subgroup.zpowers_le.2 hqJ) hy₂
    refine hZJ3 y hyJ hyM ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy₁
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hr3, pow_orderOf_eq_one,
      one_zpow]
  have hAc : Nat.card A = 3 ^ 2 := by
    rw [hA, CFSG.CGT.T75P.card_sup_of_commute hcommrq hAinf, Nat.card_zpowers, Nat.card_zpowers,
      hr3, hq3]; norm_num
  have hA₁c : Nat.card A₁ = 3 := by rw [hA₁, Nat.card_zpowers, hr3]
  have hψA : ∀ a ∈ A, ψ a = a := by
    have hle : A ≤ fixSubgroup ψ := sup_le (Subgroup.zpowers_le.2 hψr) (Subgroup.zpowers_le.2 hψq)
    exact fun a ha => hle ha
  have hJr : J ≤ Subgroup.centralizer ({r} : Set C₀) := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.2 (hrJ j hj)
  have hcentA₁ : Subgroup.centralizer (A₁ : Set C₀) = Subgroup.centralizer ({r} : Set C₀) := by
    rw [hA₁, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hrne : r ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hr3
    exact absurd hr3 (by norm_num)
  have hr3' : r ^ 3 = 1 := by rw [← hr3]; exact pow_orderOf_eq_one r
  obtain ⟨hcomm, -⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.d4ThreeBCent_holds K Q σ hK hσ hQ3
    r hrM hr3' hrne
  have hJn : (J.subgroupOf (Subgroup.centralizer ({r} : Set C₀))).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have h := hcomm (g : C₀) g.2 (x : C₀) (hJr hx)
    have e : ((g * x * g⁻¹ : ↥(Subgroup.centralizer ({r} : Set C₀))) : C₀) =
        ((g : C₀) * x * (g : C₀)⁻¹ * (x : C₀)⁻¹) * x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact J.mul_mem h hx
  have hJcomp : GLAPComponent 3 (Subgroup.centralizer (A₁ : Set C₀)) J := by
    rw [hcentA₁]
    exact CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal Nat.prime_three hJq hJ3 hJr hJn
  have hAN : A ≤ Subgroup.normalizer (J : Set C₀) := by
    refine sup_le (Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _ hrM))
      (Subgroup.zpowers_le.2 (Subgroup.le_normalizer hqJ))
  have hJperf : commutator ↥J = ⊤ := hJq.1
  have hO : ∀ y ∈ GLAPPrimeCoreOf 3 J, ∀ h ∈ J, y * h = h * y := by
    intro y hy h hh
    obtain ⟨y', hy', rfl⟩ := (CFSG.LocalAnalysis.GLTheoremA.H81.mem_glaPPrimeCoreOf_iff').1 hy
    have hc := CFSG.LocalAnalysis.GLTheoremA.H81Orth.glaPPrimeCore_le_center_of_dvd_card
      Nat.prime_three hJq hJ3 hy'
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨h, hh⟩).symm
  have hψkJ : ∀ k : ℕ, ∀ j ∈ J, (ψ ^ k) j ∈ J := by
    intro k
    induction k with
    | zero => intro j hj; exact hj
    | succ k ih => intro j hj; rw [pow_succ, MulAut.mul_apply]; exact ih _ (hmem _ hj)
  have hψkA : ∀ k : ℕ, ∀ a ∈ A, (ψ ^ k) a = a := by
    intro k a ha
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, MulAut.mul_apply, hψA a ha, ih]
  have hcentmod : ∀ a ∈ A, ∀ k : ℕ, k < 3 →
      (∀ j ∈ J, j * (a * (ψ ^ k) j * a⁻¹)⁻¹ ∈ GLAPPrimeCoreOf 3 J) → k = 0 ∧ a ∈ A₁ := by
    intro a ha k hk hj
    set β : MulAut C₀ := MulAut.conj a * ψ ^ k with hβ
    have hβapp : ∀ x, β x = a * (ψ ^ k) x * a⁻¹ := fun x => rfl
    have haJ : ∀ j ∈ J, a * j * a⁻¹ ∈ J := fun j hj =>
      (Subgroup.mem_normalizer_iff.1 (hAN ha) j).1 hj
    have hβJ : ∀ j ∈ J, β j ∈ J := fun j hj => by
      rw [hβapp]
      exact haJ _ (hψkJ k j hj)
    have hβfix : ∀ j ∈ J, β j = j := by
      have h := triD4_fix_of_perfect (H := J) hJperf hβJ fun j' hj' h hh => by
        rw [hβapp]
        exact hO _ (hj j' hj') h hh
      exact h
    have hcommψ : MulAut.conj a * ψ ^ k = ψ ^ k * MulAut.conj a := by
      ext x
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hψkA k a ha]
    have hβ3 : β ^ 3 = 1 := by
      rw [hβ, (Commute.mul_pow hcommψ 3), ← map_pow, ← pow_mul, mul_comm, pow_mul, hψ3, one_pow,
        mul_one, (hAel.2 a ha), map_one]
    have hinn := CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.d4ShortOut_holds K Q σ hK hσ hQ3 β
      ⟨1, by rw [pow_one, hβ3]⟩ hβfix
    obtain ⟨g, hg⟩ := hinn
    have hk0 : k = 0 := by
      by_contra hk0
      apply hψk k hk hk0
      refine ⟨a⁻¹ * g, ?_⟩
      rw [map_mul, hg, hβ, map_inv, ← mul_assoc, inv_mul_cancel, one_mul]
    subst hk0
    refine ⟨rfl, ?_⟩
    have haM : a ∈ M := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have h := hβfix j hj
      rw [hβapp, pow_zero, MulAut.one_apply] at h
      calc j * a = a * j * a⁻¹ * a := by rw [h]
        _ = a * j := by group
    obtain ⟨x, hx, y, hy, rfl⟩ := CFSG.GH74.Uniqueness.SU.SU1.mem_sup_of_commute hcommrq ha
    have hyM : y ∈ M := by
      have : y = x⁻¹ * (x * y) := by group
      rw [this]
      exact M.mul_mem (M.inv_mem ((Subgroup.zpowers_le.2 hrM) hx)) haM
    have hyJ : y ∈ J := (Subgroup.zpowers_le.2 hqJ) hy
    have hy3 : y ^ 3 = 1 := (hzel qb hq3).2 y hy
    rw [hZJ3 y hyJ hyM hy3, mul_one]
    exact hx
  obtain ⟨t, htJ, ht1, ht2, htc, hψt⟩ := hinv
  refine ⟨hψ3, hψout, A, A₁, J, t, hAel, hAc, hψA, le_sup_left, hA₁c, hJcomp, hAN, hJmap,
    hcentmod, hlay, ht1, ht2, fun j hj => Subgroup.mem_centralizer_singleton_iff.2 (htc j hj), ?_,
    hψt⟩
  refine sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 ?_))
    (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (htc qb hqJ)))
  exact (hrJ t htJ).symm

end Model

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end

