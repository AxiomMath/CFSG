module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Data
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitElem
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitInputs

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem gen4_of_harada (hH : HaradaInput) (S : Sylow 2 X) {E : Subgroup X}
    (hES : E ≤ S) (hE : ElemAbelianTwo E) (hcard : Nat.card E = 8)
    (hC : ∀ x ∈ (S : Subgroup X), (∀ e ∈ E, x * e = e * x) → x ∈ E)
    (P : Subgroup X) (hP : IsPGroup 2 P) :
    ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P := by
  classical
  set E' : Subgroup S := E.subgroupOf S with hE'
  have hEl : IsElementaryAbelian 2 E' :=
    { is_comm := ⟨fun a b => Subtype.ext (Subtype.ext (hE.comm _ a.2 _ b.2))⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (Subtype.ext (by simpa using hE.sq_eq_one _ a.2)) }
  have hcard' : Nat.card E' = 8 := by
    rw [hE', Nat.card_congr (subgroupOfEquivOfLe hES).toEquiv, hcard]
  have hcent : centralizer (E' : Set S) = E' := by
    apply le_antisymm
    · intro x hx
      refine hC x x.2 fun e he => ?_
      have := (mem_centralizer_iff.mp hx) ⟨e, hES he⟩ he
      exact (congrArg Subtype.val this).symm
    · intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (hE.comm _ hy _ hx)
  have hgen := hH.1 S S.isPGroup' E' hEl hcard' hcent
  refine exists_finset_closure_eq_of_sylow S (fun U hU => ?_) P hP
  obtain ⟨s, hs, hsU⟩ := hgen (U.subgroupOf S)
  refine ⟨s.image (S : Subgroup X).subtype, Finset.card_image_le.trans hs, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hsU, subgroupOf_map_subtype,
    inf_of_le_left hU]

theorem gen4_of_harada_of_maximal (hH : HaradaInput) {E : Subgroup X} (hE : ElemAbelianTwo E)
    (hcard : Nat.card E = 8)
    (hmax : ∀ P : Subgroup X, IsPGroup 2 P → E ≤ P → P ≤ centralizer (E : Set X) → P = E)
    (P : Subgroup X) (hP : IsPGroup 2 P) :
    ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  obtain ⟨S, hS⟩ := hE2.exists_le_sylow
  refine gen4_of_harada hH S hS hE hcard (fun x hx hxE => ?_) P hP
  have hEC : E ≤ (S : Subgroup X) ⊓ centralizer (E : Set X) :=
    le_inf hS fun a ha => mem_centralizer_iff.mpr fun b hb => hE.comm _ hb _ ha
  have hP' : IsPGroup 2 ((S : Subgroup X) ⊓ centralizer (E : Set X) : Subgroup X) :=
    S.isPGroup'.to_le inf_le_left
  have h := hmax _ hP' hEC inf_le_right
  rw [← h]
  exact ⟨hx, mem_centralizer_iff.mpr fun e he => (hxE e he).symm⟩

namespace A7Data

variable {t : X} {L : Subgroup X} (A : A7Data t L)

omit [Finite X] in
theorem card_T_eq : Nat.card A.T = Nat.card A.ψ.range * Nat.card A.K := by
  have hker : A.ψ.ker = A.K.subgroupOf A.T := by
    ext g
    rw [MonoidHom.mem_ker, A.ψ_eq_one_iff, mem_subgroupOf]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  rw [← Subgroup.card_mul_index A.ψ.ker, Subgroup.index_ker, hker,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : A.K ≤ A.T)).toEquiv, mul_comm]

omit [Finite X] in
theorem R0_le_range : R0 ≤ A.ψ.range := by
  intro σ hσ
  obtain ⟨g, -, hg⟩ := A.exists_ψ_eq σ hσ
  exact ⟨g, hg⟩

theorem exists_conj_le_T {P : Subgroup X} (hP : IsPGroup 2 P)
    (hPt : P ≤ centralizer ({t} : Set X)) :
    ∃ h ∈ centralizer ({t} : Set X), P.map (MulAut.conj h).toMonoidHom ≤ A.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf (centralizer ({t} : Set X))) :=
    hP.comap_of_injective _ (subtype_injective _)
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (centralizer ({t} : Set X)) Q A.syl
  refine ⟨h, h.2, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have hpC : p ∈ centralizer ({t} : Set X) := hPt hp
  have hpQ : (⟨p, hpC⟩ : centralizer ({t} : Set X)) ∈ (Q : Subgroup _) := hQ hp
  have : h * (⟨p, hpC⟩ : centralizer ({t} : Set X)) * h⁻¹ ∈ (A.syl : Subgroup _) := by
    rw [← hh, Sylow.coe_subgroup_smul]
    exact ⟨_, hpQ, rfl⟩
  exact ⟨_, this, rfl⟩

omit [Finite X] in
theorem exists_not_commute_R : ∃ r₁ ∈ A.R, ∃ r₂ ∈ A.R, r₁ * r₂ ≠ r₂ * r₁ := by
  obtain ⟨r₁, hr₁, hψ₁⟩ := A.exists_mem_R_ψ_eq a0_b0_mem_R0
  obtain ⟨r₂, hr₂, hψ₂⟩ := A.exists_mem_R_ψ_eq c0_b0_mem_R0
  refine ⟨r₁, hr₁, r₂, hr₂, fun h => a0_b0_c0_b0_ne ?_⟩
  rw [← hψ₁, ← hψ₂, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext h

theorem sq_eq_one_of_mem_R {r : X} (hr : r ∈ A.R) (h : A.ψ ⟨r, hr.1⟩ ^ 2 = 1) : r ^ 2 = 1 := by
  have hm : r ^ 2 ∈ A.R := pow_mem hr 2
  refine A.eq_of_ψ_eq hm (one_mem _) ?_
  have : (⟨r ^ 2, hm.1⟩ : A.T) = (⟨r, hr.1⟩ : A.T) ^ 2 := rfl
  rw [this, map_pow, h]
  exact (map_one A.ψ).symm

theorem le_of_le_centralizer_of_card_T (hT : Nat.card A.T = 16) {E P : Subgroup X}
    (hEP : E ≤ P) (hPT : P ≤ A.T) (hPE : P ≤ centralizer (E : Set X)) (hE : Nat.card E = 8) :
    P = E := by
  by_contra hne
  have hlt : E < P := lt_of_le_of_ne hEP (Ne.symm hne)
  have h8 : 8 < Nat.card P := by
    rw [← hE]
    exact Subgroup.card_lt_of_lt hlt
  have hPeq : P = A.T := Subgroup.eq_of_le_of_card_ge hPT (by
    have hdvd : Nat.card P ∣ 16 := hT ▸ Subgroup.card_dvd_of_le hPT
    have hmem : Nat.card P ∈ Nat.divisors 16 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    rw [show Nat.divisors 16 = {1, 2, 4, 8, 16} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega)
  have hET : E ≤ A.T := hEP.trans hPT
  have hidx : (E.subgroupOf A.T).index = 2 := by
    have h := Subgroup.card_mul_index (E.subgroupOf A.T)
    rw [Nat.card_congr (subgroupOfEquivOfLe hET).toEquiv, hE, hT] at h
    omega
  have hcen : E.subgroupOf A.T ≤ center A.T := by
    intro e he
    rw [mem_center_iff]
    intro g
    have hg : (g : X) ∈ centralizer (E : Set X) := hPE (hPeq ▸ g.2)
    exact Subtype.ext ((mem_centralizer_iff.mp hg) e he).symm
  obtain ⟨r₁, hr₁, r₂, hr₂, hne'⟩ := A.exists_not_commute_R
  have := commute_of_index_eq_two hidx hcen ⟨r₁, hr₁.1⟩ ⟨r₂, hr₂.1⟩
  exact hne' (congrArg Subtype.val this)

theorem gen4_of_range_le (hH : HaradaInput) (hK : Nat.card A.K = 2) (hψ : ∀ g, A.ψ g ∈ R0)
    (P : Subgroup X) (hP : IsPGroup 2 P) :
    ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrange : A.ψ.range = R0 := le_antisymm (by rintro _ ⟨g, rfl⟩; exact hψ g) A.R0_le_range
  have hT : Nat.card A.T = 16 := by rw [A.card_T_eq, hrange, card_R0, hK]
  obtain ⟨z, hz, hψz⟩ := A.exists_mem_R_ψ_eq a0_sq_mem_R0
  obtain ⟨r, hr, hψr⟩ := A.exists_mem_R_ψ_eq a0_b0_mem_R0
  have hz2 : z ^ 2 = 1 := A.sq_eq_one_of_mem_R hz (by rw [hψz]; decide)
  have hr2 : r ^ 2 = 1 := A.sq_eq_one_of_mem_R hr (by rw [hψr]; decide)
  have hz1 : z ≠ 1 := by
    rintro rfl
    have : A.ψ ⟨1, hz.1⟩ = 1 := map_one A.ψ
    rw [hψz] at this
    exact absurd this (by decide)
  have hzr : z * r = r * z := by
    have hm1 : z * r ∈ A.R := mul_mem hz hr
    have hm2 : r * z ∈ A.R := mul_mem hr hz
    refine A.eq_of_ψ_eq hm1 hm2 ?_
    have e1 : (⟨z * r, hm1.1⟩ : A.T) = ⟨z, hz.1⟩ * ⟨r, hr.1⟩ := rfl
    have e2 : (⟨r * z, hm2.1⟩ : A.T) = ⟨r, hr.1⟩ * ⟨z, hz.1⟩ := rfl
    rw [e1, e2, map_mul, map_mul, hψz, hψr]
    decide
  have hrz : r ≠ z := by
    intro h
    have h' : A.ψ ⟨r, hr.1⟩ = A.ψ ⟨z, hz.1⟩ := by congr 1; exact Subtype.ext h
    rw [hψr, hψz] at h'
    exact absurd h' (by decide)
  have hr1 : r ≠ 1 := by
    rintro rfl
    have : A.ψ ⟨1, hr.1⟩ = 1 := map_one A.ψ
    rw [hψr] at this
    exact absurd this (by decide)
  obtain ⟨hV1, hV1m, hV1c⟩ := ElemAbelianTwo.bot.sup_zpowers hz2
    (fun h => hz1 (mem_bot.mp h)) (fun a ha => by rw [mem_bot.mp ha, one_mul, mul_one])
  have hrV1 : r ∉ (⊥ ⊔ zpowers z : Subgroup X) := by
    intro h
    rcases hV1m r h with h' | h'
    · exact hr1 (mem_bot.mp h')
    · have h1 : r * z = 1 := mem_bot.mp h'
      have h2 : r = z := by
        calc r = r * z * z := by rw [mul_assoc, ← pow_two, hz2, mul_one]
          _ = z := by rw [h1, one_mul]
      exact hrz h2
  have hrc1 : ∀ a ∈ (⊥ ⊔ zpowers z : Subgroup X), r * a = a * r := by
    intro a ha
    rcases hV1m a ha with h' | h'
    · rw [mem_bot.mp h', mul_one, one_mul]
    · have h1 : a * z = 1 := mem_bot.mp h'
      have h2 : a = z := by
        calc a = a * z * z := by rw [mul_assoc, ← pow_two, hz2, mul_one]
          _ = z := by rw [h1, one_mul]
      rw [h2, hzr]
  obtain ⟨hV2, -, hV2c⟩ := hV1.sup_zpowers hr2 hrV1 hrc1
  have hV2L : (⊥ ⊔ zpowers z ⊔ zpowers r : Subgroup X) ≤ L :=
    sup_le (sup_le bot_le (zpowers_le.mpr hz.2)) (zpowers_le.mpr hr.2)
  have hV2T : (⊥ ⊔ zpowers z ⊔ zpowers r : Subgroup X) ≤ A.T :=
    sup_le (sup_le bot_le (zpowers_le.mpr hz.1)) (zpowers_le.mpr hr.1)
  have ht2 : t ^ 2 = 1 := by rw [← A.orderOf_t, pow_orderOf_eq_one]
  obtain ⟨hE, -, hEc⟩ := hV2.sup_zpowers ht2 (fun h => A.t_not_mem_L (hV2L h))
    (fun a ha => (A.commute_t (hV2T ha)).symm)
  set E : Subgroup X := ⊥ ⊔ zpowers z ⊔ zpowers r ⊔ zpowers t with hEdef
  have hcardE : Nat.card E = 8 := by
    rw [hEc, hV2c, hV1c, Subgroup.card_bot]
  have hET : E ≤ A.T := sup_le hV2T (zpowers_le.mpr A.t_mem_T)
  have htE : t ∈ E := le_sup_right (a := (⊥ ⊔ zpowers z ⊔ zpowers r : Subgroup X)) (mem_zpowers t)
  refine gen4_of_harada_of_maximal hH hE hcardE (fun Q hQ hEQ hQE => ?_) P hP
  have hQt : Q ≤ centralizer ({t} : Set X) := by
    intro q hq
    rw [mem_centralizer_singleton_iff]
    exact ((mem_centralizer_iff.mp (hQE hq)) t htE).symm
  obtain ⟨h, -, hhQ⟩ := A.exists_conj_le_T hQ hQt
  have hcen : Q.map (MulAut.conj h).toMonoidHom ≤
      centralizer ((E.map (MulAut.conj h).toMonoidHom : Subgroup X) : Set X) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨e, he, rfl⟩
    have hqe := (mem_centralizer_iff.mp (hQE hq)) e he
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hqe]
  have hcardE' : Nat.card (E.map (MulAut.conj h).toMonoidHom) = 8 := by
    rw [card_map_of_injective (MulAut.conj h).injective, hcardE]
  have heq := A.le_of_le_centralizer_of_card_T hT (map_mono hEQ) hhQ hcen hcardE'
  have hc : Nat.card Q = Nat.card E := by
    have h1 : Nat.card (Q.map (MulAut.conj h).toMonoidHom) = Nat.card Q :=
      card_map_of_injective (MulAut.conj h).injective
    have h2 : Nat.card (E.map (MulAut.conj h).toMonoidHom) = Nat.card E :=
      card_map_of_injective (MulAut.conj h).injective
    rw [← h1, ← h2, heq]
  exact (Subgroup.eq_of_le_of_card_ge hEQ hc.le).symm

end A7Data

end CFSG.ComponentClassification.HSFLit
