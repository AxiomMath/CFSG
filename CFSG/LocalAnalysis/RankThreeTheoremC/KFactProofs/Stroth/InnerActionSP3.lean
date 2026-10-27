module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionLie
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionN1Common

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Abstract

private theorem exists_noncomm_three {A : Type*} [Group A] [Finite A] {x u y : A}
    (hx : x ^ 3 = 1) (hu : u ^ 3 = 1) (hy : y ^ 3 = 1) (hxu : x * u = u * x)
    (huy : u * y = y * u) (hyx : y * x * y⁻¹ = x * u ^ 2) (hu1 : u ≠ 1) :
    ∃ V : Subgroup A, IsPGroup 3 V ∧ ∃ a ∈ V, ∃ b ∈ V, a * b ≠ b * a := by
  have hp : ∀ g : A, g ^ 3 = 1 → IsPGroup 3 (Subgroup.zpowers g) := fun g hg => by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hg
  set T : Subgroup A := Subgroup.zpowers x ⊔ Subgroup.zpowers u
  have hTp : IsPGroup 3 T := by
    refine (hp x hx).to_sup_of_normal_right' (hp u hu) ?_
    rw [Subgroup.zpowers_le]
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have : Commute x (u ^ m) := Commute.zpow_right (show Commute x u from hxu) m
    rw [this.eq, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers_iff.2 ⟨m, rfl⟩
  have hmap : T.map (MulAut.conj y).toMonoidHom ≤ T := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      show y * x * y⁻¹ ∈ T
      rw [hyx]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
        (pow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers u)) 2)
    · rw [Subgroup.zpowers_le]
      show y * u * y⁻¹ ∈ T
      rw [← huy, mul_inv_cancel_right]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hyT : y ∈ Subgroup.normalizer (T : Set A) :=
    Subgroup.mem_normalizer_fintype fun t ht => hmap ⟨t, ht, rfl⟩
  refine ⟨T ⊔ Subgroup.zpowers y, hTp.to_sup_of_normal_left' (hp y hy) ?_,
    x, Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers x)),
    y, Subgroup.mem_sup_right (Subgroup.mem_zpowers y), fun hcomm => hu1 ?_⟩
  · rw [Subgroup.zpowers_le]
    exact hyT
  · have h1 : x = x * u ^ 2 := by
      rw [← hyx, ← hcomm, mul_inv_cancel_right]
    have h2 : u ^ 2 = 1 := mul_left_cancel (a := x) (h1.symm.trans (mul_one x).symm)
    calc u = u * u ^ 2 := by rw [h2, mul_one]
      _ = u ^ 3 := by group
      _ = 1 := hu

private theorem mem_inner_of_nonabelian_three {K : Type} [Group K] [Finite K]
    (hout : ¬ 9 ∣ Nat.card (Outer K))
    (hnab : ∃ V : Subgroup (MulAut K), IsPGroup 3 V ∧ ∃ a ∈ V, ∃ b ∈ V, a * b ≠ b * a)
    {S : Subgroup K} (hS : IsPGroup 3 S) (hSi : ¬ 3 ∣ S.index) (hab : IsMulCommutative S)
    {α : MulAut K} (hα : α ^ 3 = 1) (hαS : ∀ s ∈ S, α s = s) : α ∈ inner K := by
  by_contra hαI
  change ¬ 9 ∣ (inner K).index at hout
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut K) := Finite.of_injective (fun f : MulAut K => (f : K → K))
    (fun f g h => MulEquiv.ext (congrFun h))
  obtain ⟨V, hVp, a, ha, b, hb, hne⟩ := hnab
  let c : K →* MulAut K := MulAut.conj
  set U : Subgroup (MulAut K) := S.map c with hU
  have hUI : U ≤ inner K := Subgroup.map_le_range c S
  have hUp : IsPGroup 3 U := hS.map c
  haveI : IsMulCommutative U := Subgroup.map_isMulCommutative S c
  have hαU : ∀ u ∈ U, α * u = u * α := by
    rintro _ ⟨s, hs, rfl⟩
    ext x
    simp [c, MulAut.conj_apply, hαS s hs]
  have hαnU : α ∉ U := fun h => hαI (hUI h)
  have hUidx : ¬ 3 ∣ U.relIndex (inner K) := by
    have h1 : U.relIndex (inner K) ∣ S.index := by
      have e : inner K = (⊤ : Subgroup K).map c := MonoidHom.range_eq_map c
      rw [e, hU, Subgroup.relIndex_map_map, top_sup_eq, Subgroup.relIndex_top_right]
      exact Subgroup.index_dvd_of_le le_sup_left
    exact fun h => hSi (h.trans h1)
  have hZp : IsPGroup 3 (Subgroup.zpowers α) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hα
  have hnorm : U ≤ Subgroup.normalizer (Subgroup.zpowers α : Set (MulAut K)) := by
    intro u hu
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have : Commute u (α ^ m) := Commute.zpow_right (show Commute u α from (hαU u hu).symm) m
    rw [this.eq, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers_iff.2 ⟨m, rfl⟩
  set H : Subgroup (MulAut K) := U ⊔ Subgroup.zpowers α
  have hHp : IsPGroup 3 H := hUp.to_sup_of_normal_right' hZp hnorm
  have hHab : IsMulCommutative H := by
    have e : H = Subgroup.closure ((U : Set (MulAut K)) ∪ {α}) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure]
    rw [e]
    refine Subgroup.isMulCommutative_closure ?_
    intro x hx y hy _
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact setLike_mul_comm hx hy
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (hαU x hx).symm
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hαU y hy
    · rw [Set.mem_singleton_iff] at hx hy
      subst hx
      subst hy
      exact rfl
  have hHidx : ¬ 3 ∣ H.index := by
    intro h3
    have hUH : U ≤ H := le_sup_left
    have e1 := Subgroup.relIndex_mul_index hUH
    have e2 := Subgroup.relIndex_mul_index hUI
    have hrel : 3 ∣ U.relIndex H := by
      obtain ⟨k, hk⟩ := IsPGroup.index (G := H) hHp (U.subgroupOf H)
      have hk' : U.relIndex H = 3 ^ k := hk
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · exfalso
        rw [pow_zero, Subgroup.relIndex_eq_one] at hk'
        exact hαnU (hk' (Subgroup.mem_sup_right (Subgroup.mem_zpowers α)))
      · rw [hk']
        exact dvd_pow_self 3 hkpos.ne'
    have h9 : 3 * 3 ∣ U.relIndex (inner K) * (inner K).index := by
      rw [e2, ← e1]
      exact Nat.mul_dvd_mul hrel h3
    have hcop : Nat.Coprime (3 * 3) (U.relIndex (inner K)) := by
      have : Nat.Coprime 3 (U.relIndex (inner K)) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hUidx
      exact Nat.Coprime.mul_left this this
    have h9' : 9 ∣ (inner K).index := by simpa using hcop.dvd_of_dvd_mul_left h9
    exact hout h9'
  exact not_isMulCommutative_of_noncomm_pSubgroup hVp ha hb hne hHp hHidx hHab

end Abstract

section Rels

private theorem exists_noncomm_of_rels {G A : Type*} [Group G] [Group A] [Finite A] (c : G →* A)
    {D D' E S₁ S₂ : G} (hS₁ : c S₁ = 1) (hS₂ : c S₂ = 1)
    (hD : D ^ 3 = 1) (hD' : D' ^ 3 = 1) (hE : E ^ 3 = 1)
    (h1 : D * D' = D' * D) (h2 : D' * E = S₁ * (E * D')) (h3 : E * D = D * D' ^ 2 * S₂ * E)
    (hne : c D' ≠ 1) :
    ∃ V : Subgroup A, IsPGroup 3 V ∧ ∃ a ∈ V, ∃ b ∈ V, a * b ≠ b * a := by
  refine exists_noncomm_three (x := c D) (u := c D') (y := c E) ?_ ?_ ?_ ?_ ?_ ?_ hne
  · rw [← map_pow, hD, map_one]
  · rw [← map_pow, hD', map_one]
  · rw [← map_pow, hE, map_one]
  · rw [← map_mul, ← map_mul, h1]
  · rw [← map_mul, h2, map_mul, hS₁, one_mul, map_mul]
  · have := congrArg c h3
    rw [map_mul, map_mul, map_mul, map_mul, map_pow, hS₂, mul_one] at this
    rw [this, mul_inv_cancel_right]

private theorem transport_data {K P : Type} [Group K] [Group P] (e : K ≃* P)
    (hout : ¬ 9 ∣ Nat.card (Outer P))
    (hnab : ∃ V : Subgroup (MulAut P), IsPGroup 3 V ∧ ∃ a ∈ V, ∃ b ∈ V, a * b ≠ b * a) :
    ¬ 9 ∣ Nat.card (Outer K) ∧
      ∃ V : Subgroup (MulAut K), IsPGroup 3 V ∧ ∃ a ∈ V, ∃ b ∈ V, a * b ≠ b * a := by
  refine ⟨?_, ?_⟩
  · rwa [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  · obtain ⟨V, hV, a, ha, b, hb, hne⟩ := hnab
    refine ⟨V.map (MulAut.congr e.symm).toMonoidHom, hV.map _, _, ⟨a, ha, rfl⟩, _,
      ⟨b, hb, rfl⟩, fun h => hne ((MulAut.congr e.symm).injective ?_)⟩
    rw [map_mul, map_mul]
    exact h

end Rels

section Arith

private theorem cube_mod_nine (r : ℕ) : r ^ 3 % 9 = 0 ∨ r ^ 3 % 9 = 1 ∨ r ^ 3 % 9 = 8 := by
  have h : r ^ 3 % 9 = (r % 9) ^ 3 % 9 := Nat.pow_mod r 3 9
  have hlt : r % 9 < 9 := Nat.mod_lt _ (by norm_num)
  rw [h]
  generalize r % 9 = s at hlt ⊢
  interval_cases s <;> simp

private theorem not_three_dvd_of_sub {ℓ f : ℕ} (h3 : 3 ∣ ℓ ^ f - 1) (h9 : ¬ 9 ∣ ℓ ^ f - 1)
    (hℓ : 0 < ℓ) : ¬ 3 ∣ f := by
  rintro ⟨g, rfl⟩
  have hq : ℓ ^ (3 * g) = (ℓ ^ g) ^ 3 := by rw [pow_mul']
  have hpos : 0 < (ℓ ^ g) ^ 3 := by positivity
  rw [hq] at h3 h9
  have := cube_mod_nine (ℓ ^ g)
  generalize (ℓ ^ g) ^ 3 = s at *
  omega

private theorem not_three_dvd_of_add {ℓ f : ℕ} (h3 : 3 ∣ ℓ ^ f + 1) (h9 : ¬ 9 ∣ ℓ ^ f + 1) :
    ¬ 3 ∣ f := by
  rintro ⟨g, rfl⟩
  have hq : ℓ ^ (3 * g) = (ℓ ^ g) ^ 3 := by rw [pow_mul']
  rw [hq] at h3 h9
  have := cube_mod_nine (ℓ ^ g)
  generalize (ℓ ^ g) ^ 3 = s at *
  omega

private theorem not_nine_dvd_of_dvd {N f : ℕ} (hN : N ∣ 2 * f * 3) (hf : ¬ 3 ∣ f) : ¬ 9 ∣ N :=
  fun h => hf (by have := h.trans hN; omega)

end Arith

section Matrices

open CFSG.LocalAnalysis.RankThreeTheoremC.NineSubgroup

variable {F : Type} [Field F]

private theorem scalar_eq_dglHom (u : Fˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) u = (dglHom 3 (fun _ => u) : GL (Fin 3) F) := by
  refine Units.ext ?_
  simp only [Matrix.GeneralLinearGroup.coe_scalar, coe_dglHom, Matrix.scalar_apply]

private theorem cyc_mul_dglHom (d : Fin 3 → Fˣ) :
    cycGL F * dglHom 3 d = dglHom 3 ![d 2, d 0, d 1] * cycGL F := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_cycGL, coe_dglHom]
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp

private def dz (z : Fˣ) : Fin 3 → Fˣ := ![z, 1, 1]

private def dw (z : Fˣ) : Fin 3 → Fˣ := ![1, z, z ^ 2]

private theorem dz_pow_three {z : Fˣ} (hz : z ^ 3 = 1) : dz z ^ 3 = 1 := by
  funext i
  fin_cases i <;> simp [dz, hz]

private theorem dw_pow_three {z : Fˣ} (hz : z ^ 3 = 1) : dw z ^ 3 = 1 := by
  funext i
  fin_cases i
  · simp [dw]
  · simpa [dw] using hz
  · simp [dw]
    rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]

private theorem dw_perm {z : Fˣ} (hz : z ^ 3 = 1) :
    dw z = (fun _ => z) * ![dw z 2, dw z 0, dw z 1] := by
  funext i
  fin_cases i
  · simp [dw]
    rw [← pow_succ']
    exact hz.symm
  · simp [dw]
  · simp [dw]
    rw [pow_two]

private theorem dz_perm {z : Fˣ} (hz : z ^ 3 = 1) :
    ![dz z 2, dz z 0, dz z 1] = dz z * dw z ^ 2 * (fun _ => z ^ 2) := by
  funext i
  fin_cases i
  · simp [dz, dw]
    rw [← pow_succ']
    exact hz.symm
  · simp [dz, dw]
    calc z = z * z ^ 3 := by rw [hz, mul_one]
      _ = z ^ 2 * z ^ 2 := by group
  · simp [dz, dw]
    calc (1 : Fˣ) = (z ^ 3) ^ 2 := by rw [hz, one_pow]
      _ = (z ^ 2) ^ 2 * z ^ 2 := by group

private theorem dw_mul_cyc {z : Fˣ} (hz : z ^ 3 = 1) :
    (dglHom 3 (dw z) : GL (Fin 3) F) * cycGL F =
      Matrix.GeneralLinearGroup.scalar (Fin 3) z * (cycGL F * dglHom 3 (dw z)) := by
  rw [scalar_eq_dglHom, cyc_mul_dglHom, ← mul_assoc, ← map_mul, ← dw_perm hz]

private theorem cyc_mul_dz {z : Fˣ} (hz : z ^ 3 = 1) :
    cycGL F * (dglHom 3 (dz z) : GL (Fin 3) F) =
      dglHom 3 (dz z) * dglHom 3 (dw z) ^ 2 *
        Matrix.GeneralLinearGroup.scalar (Fin 3) (z ^ 2) * cycGL F := by
  rw [scalar_eq_dglHom, cyc_mul_dglHom, ← map_pow, ← map_mul, ← map_mul, dz_perm hz]

end Matrices

section PSL

open CFSG.Open (StatedClassicalModel StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL conjAut conjAut_scalar
  eq_one_of_conjAut_mul_fieldAut_eq_one)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound)
open CFSG.LocalAnalysis.ComponentInitial.LinearCover (projectiveSpecialLinearEquivProjectiveSL)
open CFSG.Assembly.LowTwoRank (projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.LocalAnalysis.RankThreeTheoremC.NineSubgroup

private theorem psl_data {K : Type} [Group K] [Finite K] {ℓ f : ℕ}
    (hK : StatedClassicalModel K .PSL 3 ℓ f) (h3q : 3 ∣ ℓ ^ f - 1) (h9q : ¬ 9 ∣ ℓ ^ f - 1) :
    ¬ 9 ∣ Nat.card (Outer K) ∧
      ∃ V : Subgroup (MulAut K), IsPGroup 3 V ∧ ∃ a ∈ V, ∃ b ∈ V, a * b ≠ b * a := by
  obtain ⟨⟨hℓ, hf, -, -⟩, F, instF, instFin, hF, ⟨e⟩⟩ := hK
  have hf3 : ¬ 3 ∣ f := not_three_dvd_of_sub h3q h9q hℓ.pos
  let eK : K ≃* projectiveSL 3 F :=
    e.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
      (projectiveSpecialLinearEquivProjectiveSL 3 F))
  haveI : Finite (projectiveSL 3 F) := Finite.of_equiv K eK.toEquiv
  haveI : Finite (MulAut (projectiveSL 3 F)) :=
    Finite.of_injective (fun α : MulAut (projectiveSL 3 F) => (α : projectiveSL 3 F → _))
      fun _ _ hαβ => MulEquiv.ext (congrFun hαβ)
  refine transport_data eK ?_ ?_
  · have hb := higher_linear_outer_order_divides_field_gcd_bound hℓ hf le_rfl hF
    rw [Nat.gcd_eq_left h3q] at hb
    exact not_nine_dvd_of_dvd hb hf3
  · have hcardU : 3 ∣ Nat.card Fˣ := by rw [Nat.card_units, hF]; exact h3q
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hcardU
    have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have hz1 : z ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hz
      omega
    refine exists_noncomm_of_rels (conjAut 3 F) (D := dglHom 3 (dz z)) (D' := dglHom 3 (dw z))
      (E := cycGL F) (S₁ := Matrix.GeneralLinearGroup.scalar (Fin 3) z)
      (S₂ := Matrix.GeneralLinearGroup.scalar (Fin 3) (z ^ 2)) (conjAut_scalar z)
      (conjAut_scalar _) ?_ ?_ cycGL_pow_three ?_ (dw_mul_cyc hz3) (cyc_mul_dz hz3) ?_
    · rw [← map_pow, dz_pow_three hz3, map_one]
    · rw [← map_pow, dw_pow_three hz3, map_one]
    · rw [← map_mul, ← map_mul, mul_comm]
    · intro h
      obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) (dglHom 3 (dw z)) 1
        (by rw [map_one, mul_one]; exact h)
      have hmem : (dglHom 3 (dw z) : GL (Fin 3) F) ∈ StatedScalars (Fin 3) F := ⟨c, hc⟩
      obtain ⟨c', hc'⟩ := (dglHom_mem_scalars_iff _).1 hmem
      have h0 := hc' 0
      have h1 := hc' 1
      simp [dw] at h0 h1
      exact hz1 (h1.trans h0.symm)

end PSL

section PSU

open CFSG.Open (StatedClassicalModel StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSUEquiv)
open CFSG.LocalAnalysis.RankThreeTheoremC.NineSubgroup

private theorem psu_data {K : Type} [Group K] [Finite K] {ℓ f : ℕ}
    (hK : StatedClassicalModel K .PSU 3 ℓ f) (h3q : 3 ∣ ℓ ^ f + 1) (h9q : ¬ 9 ∣ ℓ ^ f + 1) :
    ¬ 9 ∣ Nat.card (Outer K) ∧
      ∃ V : Subgroup (MulAut K), IsPGroup 3 V ∧ ∃ a ∈ V, ∃ b ∈ V, a * b ≠ b * a := by
  obtain ⟨⟨hℓ, hf, -, hq⟩, F, instF, instFin, hF, ⟨eT⟩⟩ := hK
  have hf3 : ¬ 3 ∣ f := not_three_dvd_of_add h3q h9q
  have h : UnitaryFieldData ℓ f F := ⟨hℓ, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hq' : ¬(3 = 3 ∧ ℓ ^ f = 2) := fun ⟨h1, h2⟩ => hq (by rw [h2])
  have hC : IsPrimeFormGram (1 : GL (Fin 3) F) := isPrimeFormGram_one
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h hC
  let e' : K ≃* primeFormP h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  haveI : Finite (primeFormP h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :=
    Finite.of_equiv K e'.toEquiv
  haveI : Finite (MulAut (primeFormP h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))) :=
    Finite.of_injective (fun α : MulAut (primeFormP h ((1 : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F)) => (α : _ → _)) fun _ _ hαβ => MulEquiv.ext (congrFun hαβ)
  refine transport_data e' ?_ ?_
  · obtain ⟨-, -, -, hout, -⟩ := unitary_full_diagonal_outer_order h le_rfl hq'
    rw [hout, Nat.gcd_eq_left h3q]
    exact not_nine_dvd_of_dvd (dvd_refl _) hf3
  · have hcardU : 3 ∣ Nat.card Fˣ := by
      rw [Nat.card_units, hF]
      have := Nat.sq_sub_sq (ℓ ^ f) 1
      rw [one_pow] at this
      rw [this]
      exact Dvd.dvd.mul_right h3q _
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hcardU
    have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have hz1 : z ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hz
      omega
    have hzq : (z : F) ^ (ℓ ^ f + 1) = 1 := by
      have := pow_eq_one_of_dvd_three hz3 h3q
      simpa using congrArg Units.val this
    have hq0 : ℓ ^ f ≠ 0 := (pow_pos hℓ.pos f).ne'
    obtain ⟨-, -, hker1, -⟩ := unitary_prime_form_full_semilinear_realization h hC
      (n := 3) le_rfl hq'
    set U := primeFormUnitary h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hU
    have hconj1 : ∀ A : U, primeFormConjHom h _ A = 1 ↔ ∃ c : Fˣ, h.norm (c : F) = 1 ∧
        (A : GL (Fin 3) F) = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
      intro A
      have e := hker1 ⟨A, 1⟩
      rw [primeFormPsi_apply, map_one, mul_one] at e
      rw [e]
      exact ⟨fun h' => h'.2, fun h' => ⟨rfl, h'⟩⟩
    have hbar : (⇑h.bar : F → F) = fun x => x ^ ℓ ^ f := funext h.bar_apply
    have hmem : ∀ d : Fin 3 → Fˣ, (∀ i, (d i : F) ^ (ℓ ^ f + 1) = 1) → dglHom 3 d ∈ U := by
      intro d hd
      rw [hU, mem_primeFormUnitary, Units.val_one, Matrix.mul_one, hbar]
      exact dglHom_unitary hq0 d hd
    have hEU : cycGL F ∈ U := by
      rw [hU, mem_primeFormUnitary, Units.val_one, Matrix.mul_one, hbar]
      exact cycGL_unitary hq0
    have hzq2 : ((z ^ 2 : Fˣ) : F) ^ (ℓ ^ f + 1) = 1 := by
      rw [Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hzq, one_pow]
    have hnorm : ∀ w : Fˣ, (w : F) ^ (ℓ ^ f + 1) = 1 → h.norm (w : F) = 1 := by
      intro w hw
      rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← pow_succ']
      exact hw
    have hDU : dglHom 3 (dz z) ∈ U := hmem _ (by
      intro i
      fin_cases i <;> simp [dz, hzq])
    have hD'U : dglHom 3 (dw z) ∈ U := hmem _ (by
      intro i
      fin_cases i
      · simp [dw]
      · simpa [dw] using hzq
      · simpa [dw] using hzq2)
    refine exists_noncomm_of_rels (primeFormConjHom h _) (D := (⟨_, hDU⟩ : U))
      (D' := (⟨_, hD'U⟩ : U)) (E := (⟨_, hEU⟩ : U))
      (S₁ := (⟨_, scalar_mem_primeFormUnitary_one h (hnorm z hzq)⟩ : U))
      (S₂ := (⟨_, scalar_mem_primeFormUnitary_one h (hnorm (z ^ 2) hzq2)⟩ : U))
      ((hconj1 _).2 ⟨z, hnorm z hzq, rfl⟩) ((hconj1 _).2 ⟨z ^ 2, hnorm _ hzq2, rfl⟩)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · refine Subtype.ext ?_
      rw [Subgroup.coe_pow, ← map_pow, dz_pow_three hz3, map_one]
      rfl
    · refine Subtype.ext ?_
      rw [Subgroup.coe_pow, ← map_pow, dw_pow_three hz3, map_one]
      rfl
    · refine Subtype.ext ?_
      rw [Subgroup.coe_pow]
      exact cycGL_pow_three
    · refine Subtype.ext ?_
      simp only [Subgroup.coe_mul]
      rw [← map_mul, ← map_mul, mul_comm]
    · exact Subtype.ext (dw_mul_cyc hz3)
    · refine Subtype.ext ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_pow]
      exact cyc_mul_dz hz3
    · intro hc
      obtain ⟨c, -, hc⟩ := (hconj1 _).1 hc
      have hmem' : (dglHom 3 (dw z) : GL (Fin 3) F) ∈ StatedScalars (Fin 3) F := ⟨c, hc.symm⟩
      obtain ⟨c', hc'⟩ := (dglHom_mem_scalars_iff _).1 hmem'
      have h0 := hc' 0
      have h1 := hc' 1
      simp [dw] at h0 h1
      exact hz1 (h1.trans h0.symm)

end PSU

theorem sp3PSL_holds : SP3PSL := by
  intro K _ _ ℓ f hK h3q h9q S hS hSi hab α hα hαS
  obtain ⟨hout, hnab⟩ := psl_data hK h3q h9q
  exact mem_inner_of_nonabelian_three hout hnab hS hSi hab hα hαS

theorem sp3PSU_holds : SP3PSU := by
  intro K _ _ ℓ f hK h3q h9q S hS hSi hab α hα hαS
  obtain ⟨hout, hnab⟩ := psu_data hK h3q h9q
  exact mem_inner_of_nonabelian_three hout hnab hS hSi hab hα hαS

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction
