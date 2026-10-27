module

public import CFSG.GH74.GLS.C3.Layer1.St1P89AutStmt
public import CFSG.GH74.GLS.C3.Layer1.Back113A
public import CFSG.GH74.GLS.C3.Layer1.Thm1Transport
public import CFSG.GH74.KGroups.A6
public import CFSG.GH74.GLS.IVK.Proofs2.C3PglK
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSylowTools
public import Certificates.Certificate5146

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.KGroups CFSG.GH74.KGroups.A6 CFSG.Sporadic.Schreier CFSG.Certificates
  CFSG.GH74.Uniqueness.SU.SU1 CFSG.GH74.GLS CFSG.GH74.GLS.IVK

structure Conc89 (P B' E' : Subgroup G10) (x r s f k₁ k₂ : G10) : Prop where
  r_mem : r ∈ B' ⊓ P
  s_mem : s ∈ B' ⊓ P
  r4 : r ^ 4 = 1
  s2 : s ^ 2 = 1
  srs : s * r * s⁻¹ = r⁻¹
  r2_ne : r ^ 2 ≠ 1
  P_gen : ∀ p ∈ B' ⊓ P, ∃ i j : ℕ, p = r ^ i * s ^ j
  x_r : x * r * x⁻¹ = r⁻¹
  x_s : x * s * x⁻¹ = r * s ∨ x * s * x⁻¹ = r ^ 3 * s
  f_mem : f ∈ E'
  f2 : f ^ 2 = 1
  f_cent : ∀ p ∈ B' ⊓ P, f * p = p * f
  f_ne_one : f ≠ 1
  f_ne_z : f ≠ r ^ 2
  B_gen : ∀ b ∈ B', ∃ p ∈ B' ⊓ P, ∃ i j : ℕ, b = p * f ^ i * x ^ j
  C_P : ∀ b ∈ B', (∀ p ∈ B' ⊓ P, b * p = p * b) → ∃ i j : ℕ, b = r ^ (2 * i) * f ^ j
  Z_B : ∀ b ∈ B', (∀ b' ∈ B', b * b' = b' * b) → b = 1 ∨ b = r ^ 2
  xf : x * f * x⁻¹ = r ^ 2 * f
  s_E : s ∈ E'
  z_E : r ^ 2 ∈ E'
  k1_P : k₁ ∈ P
  k2_P : k₂ ∈ P
  k1_z : k₁ * r ^ 2 * k₁⁻¹ = s
  k1_s : k₁ * s * k₁⁻¹ = r ^ 2
  k1_f : f * k₁ = k₁ * f
  k2_z : k₂ * r ^ 2 * k₂⁻¹ = r ^ 2
  k2_s : k₂ * s * k₂⁻¹ = r ^ 2 * s
  k2_f : f * k₂ = k₂ * f

section FinMain

theorem mem_of_subset_card {S : Set G10} {l : List G10} (hl : l.Nodup) (hsub : ∀ g ∈ S, g ∈ l)
    (hcard : Nat.card ↥S = l.length) : ∀ g ∈ l, g ∈ S := by
  classical
  let f : ↥S → {g // g ∈ l} := fun g => ⟨g.1, hsub g.1 g.2⟩
  have hinj : Function.Injective f := fun a b h => by
    have h1 := congrArg Subtype.val h
    exact Subtype.ext (by simpa [f] using h1)
  have hcard' : Nat.card {g // g ∈ l} = l.length := by
    rw [Nat.card_eq_fintype_card, ← List.toFinset_card_of_nodup hl, ← Fintype.card_coe]
    simp
  have hbij : Function.Bijective f := by
    refine (Nat.bijective_iff_injective_and_card f).2 ⟨hinj, ?_⟩
    rw [hcard, hcard']
  intro g hg
  obtain ⟨a, ha⟩ := hbij.2 ⟨g, hg⟩
  have := congrArg Subtype.val ha
  simp only [f] at this
  rw [← this]
  exact a.2

theorem fin_main (hF : P89Facts) {B' E' : Subgroup G10} (hB' : ∀ b ∈ B', b ∈ Bl)
    (hBP : Nat.card ↥(B' ⊓ QP.originalSubgroup) = 8) {x : G10} (hxB : x ∈ B') (hx2 : x ^ 2 = 1)
    (hxP : x ∉ QP.originalSubgroup)
    (hx3 : ∀ c ∈ QP.originalSubgroup, orderOf c = 3 → x * c ≠ c * x) (hEB : E' ≤ B')
    (hEel : Open.IsElemAbelian 2 E') (hE8 : 8 ≤ Nat.card ↥E') :
    ∃ r s f k₁ k₂ : G10, Conc89 QP.originalSubgroup B' E' x r s f k₁ k₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨⟨hBnd, hBlen, hB1, hBmul, hBinv⟩, hBsift⟩, ⟨hPnd, hPlen, hPB, hPsift⟩, ⟨hP3, hX⟩, hE, hW⟩ :=
    hF
  have hQP : ValidSchreier QP := QP_ok
  have hPmem : ∀ g : G10, g ∈ QP.originalSubgroup ↔ QP.sift g 0 = true := fun g =>
    mem_iff_sift QP hQP g
  have hP0sub : ∀ g ∈ B' ⊓ QP.originalSubgroup, g ∈ Pl := by
    intro g hg
    exact (hPsift g (hB' g hg.1)).2 ((hPmem g).1 hg.2)
  have hP0 : ∀ g ∈ Pl, g ∈ B' ⊓ QP.originalSubgroup :=
    mem_of_subset_card (S := ((B' ⊓ QP.originalSubgroup : Subgroup G10) : Set G10)) hPnd hP0sub
      (by rw [hPlen]; exact hBP)
  have hxBl : x ∈ Bl := hB' x hxB
  have hxPl : x ∉ Pl := fun h => hxP ((hPmem x).2 ((hPsift x hxBl).1 h))
  have hx3' : ∀ c ∈ P3, x * c ≠ c * x := by
    intro c hc
    obtain ⟨hc3, hc1, hcs⟩ := hP3 c hc
    exact hx3 c ((hPmem c).2 hcs) (orderOf_eq_prime hc3 hc1)
  have hxX : x ∈ Xl := hX x hxBl hx2 hxPl hx3'
  have hEcomm := (isElemAbelian_iff.mp hEel).1
  have hEsq := (isElemAbelian_iff.mp hEel).2
  obtain ⟨a, haE, b, hbE, ha1, hb⟩ := exists_two_independent E' (by omega)
  obtain ⟨c, hcE, hc⟩ := exists_mem_notMem_list E' [1, a, b, a * b] (by simp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
  have hindep : P89Indep a b c :=
    ⟨hEsq a haE, hEsq b hbE, hEsq c hcE, hEcomm a haE b hbE, hEcomm a haE c hcE,
      hEcomm b hbE c hcE, ha1, hb.1, hb.2.1, hc⟩
  have hspan := hE a (hB' a (hEB haE)) b (hB' b (hEB hbE)) c (hB' c (hEB hcE)) hindep
  have hprod : ∀ y ∈ [1, a, b, c, a * b, a * c, b * c, a * b * c], y ∈ E' := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with h | h | h | h | h | h | h | h <;> rw [h]
    · exact E'.one_mem
    · exact haE
    · exact hbE
    · exact hcE
    · exact E'.mul_mem haE hbE
    · exact E'.mul_mem haE hcE
    · exact E'.mul_mem hbE hcE
    · exact E'.mul_mem (E'.mul_mem haE hbE) hcE
  obtain ⟨Ei, hEi, hEsub⟩ : ∃ i ∈ List.range 2, ∀ y ∈ (if i = 0 then E1 else E2), y ∈ E' := by
    rcases hspan with h | h
    · exact ⟨0, by simp, fun y hy => hprod y (h y (by simpa using hy))⟩
    · exact ⟨1, by simp, fun y hy => hprod y (h y (by simpa using hy))⟩
  obtain ⟨w, hwW, hw1, hw2, hcond⟩ := hW x hxX Ei hEi
  obtain ⟨x', i', r, s, f, k₁, k₂⟩ := w
  dsimp only at hw1 hw2 hcond
  subst hw1
  subst hw2
  obtain ⟨⟨hrPl, hsPl, hr4, hs2, hsrs, hr2, hPgen⟩, ⟨hxr, hxs⟩, ⟨hfE, hf2, hfcent, hf1, hfz, hxf, hsE, hzE⟩,
    ⟨hBgen, hCPf, hZB⟩, ⟨hk1, hk2, hk1z, hk1s, hk1f, hk2z, hk2s, hk2f⟩⟩ := hcond
  have hBsup : ∀ g ∈ Bl, g ∈ B' := by
    intro g hg
    obtain ⟨p, hp, i, hi, j, hj, h⟩ := hBgen g hg
    rw [h]
    exact B'.mul_mem (B'.mul_mem (hP0 p hp).1 (B'.pow_mem (hEB (hEsub f hfE)) i))
      (B'.pow_mem hxB j)
  refine ⟨r, s, f, k₁, k₂, ⟨hP0 r hrPl, hP0 s hsPl, hr4, hs2, hsrs, hr2, ?_, hxr, hxs,
    hEsub f hfE, hf2, ?_, hf1, hfz, ?_, ?_, ?_, hxf, hEsub s hsE, hEsub _ hzE,
    (hPmem k₁).2 hk1, (hPmem k₂).2 hk2, hk1z, hk1s, hk1f, hk2z, hk2s, hk2f⟩⟩
  · intro p hp
    obtain ⟨i, hi, j, hj, hpij⟩ := hPgen p (hP0sub p hp)
    exact ⟨i, j, hpij⟩
  · intro p hp
    exact hfcent p (hP0sub p hp)
  · intro b hb
    obtain ⟨p, hp, i, hi, j, hj, h⟩ := hBgen b (hB' b hb)
    exact ⟨p, hP0 p hp, i, j, h⟩
  · intro b hb hcomm
    obtain ⟨i, hi, j, hj, h⟩ := hCPf b (hB' b hb) (fun p hp => hcomm p (hP0 p hp))
    exact ⟨i, j, h⟩
  · intro b hb hcomm
    exact hZB b (hB' b hb) (fun b' hb' => hcomm b' (hBsup b' hb'))

end FinMain

private theorem mulConjMulInvAut {H : Type} [Group H] (γ : MulAut H) (g : H) :
    γ * MulAut.conj g * γ⁻¹ = MulAut.conj (γ g) := by
  ext y
  simp [MulAut.conj_apply, MulAut.mul_apply]

section Model

variable {Kb : Type} [Group Kb]

theorem pa_mem_A : pa ∈ QA.originalSubgroup := by
  rw [QA, certificate_originalSubgroup]
  exact Subgroup.subset_closure (by simp)

theorem pb_mem_A : pb ∈ QA.originalSubgroup := by
  rw [QA, certificate_originalSubgroup]
  exact Subgroup.subset_closure (by simp)

theorem P_le_A : QP.originalSubgroup ≤ QA.originalSubgroup := by
  rw [QP_closure, Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | hg
  · exact pa_mem_A
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    exact pb_mem_A

theorem centA : ∀ σ ∈ QA.originalSubgroup, (∀ x ∈ QP.originalSubgroup, σ * x = x * σ) → σ = 1 := by
  intro σ hσ hc
  by_contra hne
  have h1 := List.all_eq_true.1 cent_ok σ ((mem_elemsT QA QA_ok σ).2 hσ)
  have hpa : pa ∈ QP.originalSubgroup := by
    rw [QP_closure]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hpb : pb ∈ QP.originalSubgroup := by
    rw [QP_closure]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hA' : σ * pa = pa * σ := hc pa hpa
  have hB' : σ * pb = pb * σ := hc pb hpb
  simp [hA', hB', hne] at h1

variable (M : AutModel Kb G10) (hP : M.P = QP.originalSubgroup) (hA : M.A = QA.originalSubgroup)

include hP hA in
theorem ι_conj (k : Kb) : M.ι (MulAut.conj k) = ((M.e k : M.P) : G10) := by
  set a : G10 := M.ι (MulAut.conj k) with ha
  set b : G10 := ((M.e k : M.P) : G10) with hb
  have haA : a ∈ QA.originalSubgroup := hA ▸ M.ι_mem _
  have hbP : b ∈ QP.originalSubgroup := hP ▸ (M.e k).2
  have hbA : b ∈ QA.originalSubgroup := P_le_A hbP
  have hcomm : ∀ x : Kb, (a⁻¹ * b) * ((M.e x : M.P) : G10) = ((M.e x : M.P) : G10) * (a⁻¹ * b) := by
    intro x
    have h1 := M.spec (MulAut.conj k) x
    have h2 : ((M.e ((MulAut.conj k) x) : M.P) : G10) = b * ((M.e x : M.P) : G10) * b⁻¹ := by
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
      simp [hb]
    rw [h2] at h1
    have h3 : (M.Φ (MulAut.conj k) : G10) = a := rfl
    rw [h3] at h1
    calc a⁻¹ * b * (M.e x : G10) = a⁻¹ * (b * (M.e x : G10) * b⁻¹) * b := by group
      _ = a⁻¹ * (a * (M.e x : G10) * a⁻¹) * b := by rw [h1]
      _ = (M.e x : G10) * (a⁻¹ * b) := by group
  have hσ : a⁻¹ * b ∈ QA.originalSubgroup := QA.originalSubgroup.mul_mem (QA.originalSubgroup.inv_mem haA) hbA
  have h1 : a⁻¹ * b = 1 := by
    apply centA _ hσ
    intro y hy
    rw [← hP] at hy
    obtain ⟨x, hx⟩ := M.e.surjective ⟨y, hy⟩
    have := hcomm x
    rw [hx] at this
    exact this
  exact (inv_mul_eq_one.1 h1)

include hP hA in
theorem mem_innAut_iff (φ : MulAut Kb) : φ ∈ innAut Kb ↔ M.ι φ ∈ QP.originalSubgroup := by
  constructor
  · rintro ⟨k, rfl⟩
    rw [ι_conj M hP hA k]
    exact hP ▸ (M.e k).2
  · intro h
    obtain ⟨k, hk⟩ := M.inner_of_mem φ (hP ▸ h)
    exact ⟨k, MulEquiv.ext fun x => (hk x).symm⟩

include hP hA in
theorem exists_conj_of_mem_P {y : G10} (hy : y ∈ QP.originalSubgroup) :
    ∃ k : Kb, M.ι (MulAut.conj k) = y := by
  rw [← hP] at hy
  obtain ⟨k, hk⟩ := M.e.surjective ⟨y, hy⟩
  exact ⟨k, by rw [ι_conj M hP hA k, hk]⟩

include hA in
theorem exists_ι_of_mem_A {g : G10} (hg : g ∈ QA.originalSubgroup) : ∃ φ : MulAut Kb, M.ι φ = g := by
  rw [← hA] at hg
  obtain ⟨φ, hφ⟩ := M.Φ.surjective ⟨g, hg⟩
  exact ⟨φ, congrArg Subtype.val hφ⟩

include hP hA in
theorem A_normalizes_P {g : G10} (hg : g ∈ QA.originalSubgroup) {y : G10}
    (hy : y ∈ QP.originalSubgroup) : g * y * g⁻¹ ∈ QP.originalSubgroup := by
  obtain ⟨φ, rfl⟩ := exists_ι_of_mem_A M hA hg
  obtain ⟨k, rfl⟩ := exists_conj_of_mem_P M hP hA hy
  have : M.ι φ * M.ι (MulAut.conj k) * (M.ι φ)⁻¹ = M.ι (MulAut.conj (φ k)) := by
    rw [← map_inv, ← map_mul, ← map_mul, mulConjMulInvAut]
  rw [this]
  exact (mem_innAut_iff M hP hA _).1 ⟨φ k, rfl⟩

end Model

@[expose] def B0sub (hF : P89Facts) : Subgroup G10 where
  carrier := {g | g ∈ Bl}
  one_mem' := by
    obtain ⟨⟨⟨_, _, h1, _, _⟩, _⟩, _⟩ := hF
    exact h1
  mul_mem' := by
    intro a b ha hb
    obtain ⟨⟨⟨_, _, _, hmul, _⟩, _⟩, _⟩ := hF
    exact hmul a ha b hb
  inv_mem' := by
    intro a ha
    obtain ⟨⟨⟨_, _, _, _, hinv⟩, _⟩, _⟩ := hF
    exact hinv a ha

theorem card_subtype_mem {l : List G10} (hl : l.Nodup) : Nat.card {g // g ∈ l} = l.length := by
  classical
  rw [Nat.card_eq_fintype_card, ← List.toFinset_card_of_nodup hl, ← Fintype.card_coe]
  simp

theorem B0sub_card (hF : P89Facts) : Nat.card ↥(B0sub hF) = 32 := by
  obtain ⟨⟨⟨hnd, hlen, _⟩, _⟩, _⟩ := id hF
  have : Nat.card ↥(B0sub hF) = Nat.card {g // g ∈ Bl} := Nat.card_congr (Equiv.refl _)
  rw [this, card_subtype_mem hnd, hlen]

theorem B0sub_le_A (hF : P89Facts) :
    B0sub hF ≤ QA.originalSubgroup := by
  intro g hg
  obtain ⟨⟨_, hsift⟩, _⟩ := id hF
  exact (mem_iff_sift QA QA_ok g).2 (hsift g hg)

theorem B0sub_sylow (hF : P89Facts) :
    IsSylowOf 2 (B0sub hF) QA.originalSubgroup := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_of_card (B0sub_le_A hF) ?_
  rw [B0sub_card hF, card_group QA QA_ok, QA_valid.2]
  have hfac : (1440 : ℕ).factorization 2 = 5 := by
    rw [show (1440 : ℕ) = 2 ^ 5 * 45 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.add_apply, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [hfac]
  norm_num

theorem card_P_two_part :
    2 ^ (Nat.card ↥QP.originalSubgroup).factorization 2 = 8 := by
  rw [card_group QP QP_ok, QP_valid.2]
  have hfac : (360 : ℕ).factorization 2 = 3 := by
    rw [show (360 : ℕ) = 2 ^ 3 * 45 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.add_apply, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [hfac]
  norm_num

section PGL

variable {Kb : Type} [Group Kb]

theorem pgl_no_commute (hcen : Function.Injective (MulAut.conj : Kb →* MulAut Kb)) {xb : MulAut Kb}
    (hx2 : xb ^ 2 = 1) (hxn : xb ∉ innAut Kb)
    (hP : IsPGL2 ↥(innAut Kb ⊔ zpowers xb) (fun q => q = 9)) (k : Kb) (hk : orderOf k = 3) :
    xb * MulAut.conj k ≠ MulAut.conj k * xb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hc
  obtain ⟨F₀, _, _, hF₀, ⟨ψ⟩⟩ := hP
  have hF₀9 : Nat.card F₀ = 9 := hF₀
  let tX : ↥(innAut Kb ⊔ zpowers xb) := ⟨xb, Subgroup.mem_sup_right (Subgroup.mem_zpowers xb)⟩
  let uX : ↥(innAut Kb ⊔ zpowers xb) := ⟨MulAut.conj k, Subgroup.mem_sup_left ⟨k, rfl⟩⟩
  have hxne : xb ≠ 1 := fun h => hxn (by rw [h]; exact one_mem _)
  have htX : orderOf tX = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime hx2 hxne
  have huX : orderOf uX = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact (orderOf_injective _ hcen k).trans hk
  have hcomm : tX * uX = uX * tX := Subtype.ext hc
  refine IVK.Proofs2.pgl2_nine_no_order_six hF₀9 (t := ψ tX) (u := ψ uX) ?_ ?_ ?_
  · rw [MulEquiv.orderOf_eq]
    exact htX
  · rw [MulEquiv.orderOf_eq]
    exact huX
  · rw [← map_mul, ← map_mul, hcomm]

end PGL

section Pull

variable {Kb : Type} [Group Kb]

theorem autData_of_conc (ψ : MulAut Kb →* G10) (hinj : Function.Injective ψ)
    (hinn : ∀ φ : MulAut Kb, φ ∈ innAut Kb ↔ ψ φ ∈ QP.originalSubgroup)
    (hsurj : ∀ y ∈ QP.originalSubgroup, ∃ φ : MulAut Kb, ψ φ = y) {B Eb : Subgroup (MulAut Kb)}
    {xb : MulAut Kb} {r s f k₁ k₂ : G10}
    (conc : Conc89 QP.originalSubgroup (B.map ψ) (Eb.map ψ) (ψ xb) r s f k₁ k₂) :
    ∃ (rb sb fb : MulAut Kb) (κ₁ κ₂ : Kb), AutData89 B Eb xb rb sb fb κ₁ κ₂ := by
  obtain ⟨⟨rb, hrB, hrb⟩, hrP⟩ := conc.r_mem
  obtain ⟨⟨sb, hsB, hsb⟩, hsP⟩ := conc.s_mem
  obtain ⟨fb, hfE, hfb⟩ := conc.f_mem
  obtain ⟨φ₁, hφ₁⟩ := hsurj _ conc.k1_P
  obtain ⟨φ₂, hφ₂⟩ := hsurj _ conc.k2_P
  obtain ⟨κ₁, hκ₁⟩ := (hinn φ₁).2 (hφ₁ ▸ conc.k1_P)
  obtain ⟨κ₂, hκ₂⟩ := (hinn φ₂).2 (hφ₂ ▸ conc.k2_P)
  have hk1 : ψ (MulAut.conj κ₁) = k₁ := by
    have : (MulAut.conj : Kb →* MulAut Kb) κ₁ = φ₁ := hκ₁
    rw [this, hφ₁]
  have hk2 : ψ (MulAut.conj κ₂) = k₂ := by
    have : (MulAut.conj : Kb →* MulAut Kb) κ₂ = φ₂ := hκ₂
    rw [this, hφ₂]
  have hrP' : ψ rb ∈ QP.originalSubgroup := by rw [hrb]; exact hrP
  have hsP' : ψ sb ∈ QP.originalSubgroup := by rw [hsb]; exact hsP
  subst hrb hsb hfb hk1 hk2
  have hPP : ∀ p ∈ B ⊓ innAut Kb, ψ p ∈ (B.map ψ) ⊓ QP.originalSubgroup := fun p hp =>
    ⟨⟨p, hp.1, rfl⟩, (hinn p).1 hp.2⟩
  have hPP' : ∀ y ∈ (B.map ψ) ⊓ QP.originalSubgroup, ∃ p ∈ B ⊓ innAut Kb, ψ p = y := by
    rintro y ⟨⟨p, hpB, rfl⟩, hyP⟩
    exact ⟨p, ⟨hpB, (hinn p).2 hyP⟩, rfl⟩
  refine ⟨rb, sb, fb, κ₁, κ₂, ?_⟩
  refine
    { r_mem := ⟨hrB, (hinn rb).2 hrP'⟩
      s_mem := ⟨hsB, (hinn sb).2 hsP'⟩
      r4 := hinj (by simpa [map_pow] using conc.r4)
      s2 := hinj (by simpa [map_pow] using conc.s2)
      srs := hinj (by simpa [map_mul, map_inv] using conc.srs)
      r2_ne := fun h => conc.r2_ne (by simpa [map_pow] using congrArg ψ h)
      P_gen := ?_
      x_r := hinj (by simpa [map_mul, map_inv] using conc.x_r)
      x_s := ?_
      f_mem := hfE
      f2 := hinj (by simpa [map_pow] using conc.f2)
      f_cent := ?_
      f_ne_one := fun h => conc.f_ne_one (by simpa using congrArg ψ h)
      f_ne_z := fun h => conc.f_ne_z (by simpa [map_pow] using congrArg ψ h)
      B_gen := ?_
      C_P := ?_
      Z_B := ?_
      xf := hinj (by simpa [map_mul, map_inv, map_pow] using conc.xf)
      s_E := ?_
      z_E := ?_
      k1_z := hinj (by simpa [map_mul, map_inv, map_pow] using conc.k1_z)
      k1_s := hinj (by simpa [map_mul, map_inv, map_pow] using conc.k1_s)
      k1_f := hinj (by simpa [map_mul] using conc.k1_f)
      k2_z := hinj (by simpa [map_mul, map_inv, map_pow] using conc.k2_z)
      k2_s := hinj (by simpa [map_mul, map_inv, map_pow] using conc.k2_s)
      k2_f := hinj (by simpa [map_mul] using conc.k2_f) }
  · intro p hp
    obtain ⟨i, j, h⟩ := conc.P_gen (ψ p) (hPP p hp)
    exact ⟨i, j, hinj (by simpa [map_mul, map_pow] using h)⟩
  · rcases conc.x_s with h | h
    · exact Or.inl (hinj (by simpa [map_mul, map_inv] using h))
    · exact Or.inr (hinj (by simpa [map_mul, map_inv, map_pow] using h))
  · intro p hp
    exact hinj (by simpa [map_mul] using conc.f_cent (ψ p) (hPP p hp))
  · intro b hb
    obtain ⟨p', hp', i, j, h⟩ := conc.B_gen (ψ b) ⟨b, hb, rfl⟩
    obtain ⟨p, hp, rfl⟩ := hPP' p' hp'
    exact ⟨p, hp, i, j, hinj (by simpa [map_mul, map_pow] using h)⟩
  · intro b hb hcomm
    obtain ⟨i, j, h⟩ := conc.C_P (ψ b) ⟨b, hb, rfl⟩ (fun p' hp' => by
      obtain ⟨p, hp, rfl⟩ := hPP' p' hp'
      simpa [map_mul] using congrArg ψ (hcomm p hp))
    exact ⟨i, j, hinj (by simpa [map_mul, map_pow] using h)⟩
  · intro b hb hcomm
    rcases conc.Z_B (ψ b) ⟨b, hb, rfl⟩ (fun b' hb' => by
      obtain ⟨b'', hb'', rfl⟩ := hb'
      simpa [map_mul] using congrArg ψ (hcomm b'' hb'')) with h | h
    · exact Or.inl (hinj (by simpa using h))
    · exact Or.inr (hinj (by simpa [map_pow] using h))
  · exact (Subgroup.mem_map_iff_mem hinj).1 conc.s_E
  · have := conc.z_E
    rw [← map_pow] at this
    exact (Subgroup.mem_map_iff_mem hinj).1 this

end Pull

theorem b_prop89_autlevel_of_facts (hF : P89Facts) :
    B_prop89_autlevel := by
  intro Kb _ _ hL2 B hB2 hSyl xb hxB hx2 hxn hpgl Eb hEB hEel hE8
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e0⟩ := Back.nonempty_alt6_of_hasL2Model9 hL2
  obtain ⟨e⟩ := equiv_of_alt6 ⟨e0⟩
  obtain ⟨M, hP, hA⟩ := autModel e
  have hfinMA : Finite (MulAut Kb) := Finite.of_equiv ↥M.A M.Φ.symm.toEquiv
  have hcen : Function.Injective (MulAut.conj : Kb →* MulAut Kb) := by
    intro k₁ k₂ h
    have h' : M.ι (MulAut.conj k₁) = M.ι (MulAut.conj k₂) := by rw [h]
    rw [ι_conj M hP hA k₁, ι_conj M hP hA k₂] at h'
    exact M.e.injective (Subtype.ext h')
  have hBA : B.map M.ι ≤ QA.originalSubgroup := by
    rintro _ ⟨b, -, rfl⟩
    exact hA ▸ M.ι_mem b
  have hB2' : IsPGroup 2 ↥(B.map M.ι) :=
    hB2.of_surjective (M.ι.subgroupMap B) (M.ι.subgroupMap_surjective B)
  obtain ⟨g, hgA, hg⟩ := CFSG.ComponentClassification.FooteLit.exists_conj_le_of_isSylowOf
    (B0sub_sylow hF) hBA hB2'
  let ψ : MulAut Kb →* G10 := (MulAut.conj g⁻¹).toMonoidHom.comp M.ι
  have hψ : ∀ φ, ψ φ = g⁻¹ * M.ι φ * g := fun φ => by simp [ψ]
  have hinj : Function.Injective ψ := by
    intro a b h
    apply M.ι_injective
    exact (MulAut.conj g⁻¹).injective h
  have hgP : ∀ y ∈ QP.originalSubgroup, g⁻¹ * y * g ∈ QP.originalSubgroup := by
    intro y hy
    have := A_normalizes_P M hP hA ((QA.originalSubgroup).inv_mem hgA) hy
    simpa using this
  have hgP' : ∀ y ∈ QP.originalSubgroup, g * y * g⁻¹ ∈ QP.originalSubgroup := fun y hy =>
    A_normalizes_P M hP hA hgA hy
  have hinn : ∀ φ : MulAut Kb, φ ∈ innAut Kb ↔ ψ φ ∈ QP.originalSubgroup := by
    intro φ
    rw [mem_innAut_iff M hP hA, hψ]
    constructor
    · intro h
      exact hgP _ h
    · intro h
      have := hgP' _ h
      have e : g * (g⁻¹ * M.ι φ * g) * g⁻¹ = M.ι φ := by group
      rwa [e] at this
  have hsurj : ∀ y ∈ QP.originalSubgroup, ∃ φ : MulAut Kb, ψ φ = y := by
    intro y hy
    obtain ⟨φ, hφ⟩ := exists_ι_of_mem_A M hA (P_le_A (hgP' y hy))
    refine ⟨φ, ?_⟩
    rw [hψ, hφ]
    group
  have hB' : ∀ b ∈ B.map ψ, b ∈ Bl := by
    rintro _ ⟨b₀, hb₀, rfl⟩
    rw [hψ]
    exact hg _ ⟨b₀, hb₀, rfl⟩
  have hBP : Nat.card ↥(B.map ψ ⊓ QP.originalSubgroup) = 8 := by
    have h1 := CFSG.GH74.GLS.C3.Layer1.Thm1.isSylowOf_map_hom ψ hSyl
    have hmapInn : (innAut Kb).map ψ = QP.originalSubgroup := by
      ext y
      constructor
      · rintro ⟨φ, hφ, rfl⟩
        exact (hinn φ).1 hφ
      · intro hy
        obtain ⟨φ, hφ⟩ := hsurj y hy
        exact ⟨φ, (hinn φ).2 (hφ ▸ hy), hφ⟩
    have hmapB : (B ⊓ innAut Kb).map ψ = B.map ψ ⊓ QP.originalSubgroup := by
      rw [Subgroup.map_inf_eq B (innAut Kb) ψ hinj, hmapInn]
    rw [hmapInn, hmapB] at h1
    rw [h1.card_eq, card_P_two_part]
  have hx'B : ψ xb ∈ B.map ψ := ⟨xb, hxB, rfl⟩
  have hx'2 : ψ xb ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
  have hx'P : ψ xb ∉ QP.originalSubgroup := fun h => hxn ((hinn xb).2 h)
  have hx3 : ∀ c ∈ QP.originalSubgroup, orderOf c = 3 → ψ xb * c ≠ c * ψ xb := by
    intro c hc hc3 hcomm
    obtain ⟨φ, rfl⟩ := hsurj c hc
    obtain ⟨κ, hκ⟩ := (hinn φ).2 hc
    have hφ : φ = MulAut.conj κ := hκ.symm
    subst hφ
    have h1 : orderOf (MulAut.conj κ) = 3 := by
      rw [← orderOf_injective ψ hinj]
      exact hc3
    have hκ3 : orderOf κ = 3 := by
      rw [← orderOf_injective (MulAut.conj : Kb →* MulAut Kb) hcen κ]
      exact h1
    apply pgl_no_commute hcen hx2 hxn hpgl κ hκ3
    apply hinj
    rw [map_mul, map_mul]
    exact hcomm
  have hE'B : Eb.map ψ ≤ B.map ψ := Subgroup.map_mono hEB
  have hE'el : Open.IsElemAbelian 2 (Eb.map ψ) := by
    have hcomm := (isElemAbelian_iff.mp hEel).1
    have hsq := (isElemAbelian_iff.mp hEel).2
    refine isElemAbelian_iff.2 ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hcomm a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hsq a ha, map_one]
  have hE'8 : 8 ≤ Nat.card ↥(Eb.map ψ) := by
    rw [Subgroup.card_map_of_injective hinj]
    exact hE8
  obtain ⟨r, s, f, k₁, k₂, conc⟩ := fin_main hF hB' hBP hx'B hx'2 hx'P hx3 hE'B hE'el hE'8
  exact autData_of_conc ψ hinj hinn hsurj conc

theorem b_prop89_autlevel_proved :
    B_prop89_autlevel :=
  b_prop89_autlevel_of_facts Certificates.certificate5146

end CFSG.GH74.GLS.C3.Layer1.P89
