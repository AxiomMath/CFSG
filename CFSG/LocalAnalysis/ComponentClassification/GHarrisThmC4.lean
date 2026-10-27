module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisThmC3
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisThmC1
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion

public noncomputable section

namespace CFSG.ComponentClassification.GHarris.ThmC

open CFSG Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23 CFSG.RankTwoShapes
open CFSG.SectionRank.Ccomm GL42
open scoped Matrix Pointwise

@[expose] def eEquiv : Eu ≃* Multiplicative (Fin 4 → ZMod 2) where
  toFun u := Multiplicative.ofAdd ![(u : UT3 F4c).a.a, (u : UT3 F4c).a.b, (u : UT3 F4c).c.a,
    (u : UT3 F4c).c.b]
  invFun v := ⟨⟨⟨Multiplicative.toAdd v 0, Multiplicative.toAdd v 1⟩, 0,
    ⟨Multiplicative.toAdd v 2, Multiplicative.toAdd v 3⟩⟩, rfl⟩
  left_inv u := by
    obtain ⟨⟨a, b, c⟩, hu⟩ := u
    change b = 0 at hu
    subst hu
    rfl
  right_inv v := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl
  map_mul' u w := by
    obtain ⟨⟨ua, ub, uc⟩, hu⟩ := u
    obtain ⟨⟨wa, wb, wc⟩, hw⟩ := w
    change ub = 0 at hu
    change wb = 0 at hw
    subst hu hw
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · rfl
    · rfl
    · show (uc + wc + ua * 0).a = uc.a + wc.a
      rw [mul_zero, add_zero]
      rfl
    · show (uc + wc + ua * 0).b = uc.b + wc.b
      rw [mul_zero, add_zero]
      rfl

theorem conj_coords (u : UT3 F4c) (x c : F4c) :
    (⟨(u * ⟨x, 0, c⟩ * u⁻¹).a.a, (u * ⟨x, 0, c⟩ * u⁻¹).a.b, (u * ⟨x, 0, c⟩ * u⁻¹).c.a,
      (u * ⟨x, 0, c⟩ * u⁻¹).c.b⟩ : V4c) = (e0 u.b.a u.b.b).mulVec ⟨x.a, x.b, c.a, c.b⟩ := by
  rw [ut_conj]
  show (⟨x.a, x.b, (c + u.a * 0 + x * u.b).a, (c + u.a * 0 + x * u.b).b⟩ : V4c) = _
  rw [mul_zero, add_zero]
  show (⟨x.a, x.b, c.a + (x.a * u.b.a + x.b * u.b.b),
      c.b + (x.a * u.b.b + x.b * u.b.a + x.b * u.b.b)⟩ : V4c) =
    ⟨1 * x.a + 0 * x.b + 0 * c.a + 0 * c.b, 0 * x.a + 1 * x.b + 0 * c.a + 0 * c.b,
      u.b.a * x.a + u.b.b * x.b + 1 * c.a + 0 * c.b,
      u.b.b * x.a + (u.b.a + u.b.b) * x.b + 0 * c.a + 1 * c.b⟩
  congr 1 <;> ring

theorem exists_e0 : ∀ e ∈ e0c, ∃ p q : ZMod 2, e = e0 p q := by decide

theorem e0_mem : ∀ p q : ZMod 2, e0 p q ∈ e0c := by decide

namespace UTSylow

variable {X : Type} [Group X] (D : UTSylow X)

@[expose] def eE : D.E ≃* Multiplicative (Fin 4 → ZMod 2) :=
  (Eu.equivMapOfInjective D.toX D.toX_injective).symm.trans eEquiv

theorem eE_toX {u : UT3 F4c} (hu : u.b = 0) :
    D.eE ⟨D.toX u, D.toX_mem_E_iff.mpr hu⟩ =
      Multiplicative.ofAdd ![u.a.a, u.a.b, u.c.a, u.c.b] := by
  have h : (Eu.equivMapOfInjective D.toX D.toX_injective).symm ⟨D.toX u, D.toX_mem_E_iff.mpr hu⟩ =
      ⟨u, hu⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [eE, MulEquiv.trans_apply, h]
  rfl

@[expose] def psi : normalizer (D.E : Set X) →* GL4 :=
  (elemAutEquivGL D.eE).toMonoidHom.comp D.E.normalizerMonoidHom

theorem psi_mulVec (n : normalizer (D.E : Set X)) (w : D.E) :
    ((D.psi n : GL4) : M4) *ᵥ Multiplicative.toAdd (D.eE w) =
      Multiplicative.toAdd (D.eE (D.E.normalizerMonoidHom n w)) :=
  elemAutEquivGL_mulVec D.eE _ w

theorem coe_normalizerMonoidHom (n : normalizer (D.E : Set X)) (w : D.E) :
    ((D.E.normalizerMonoidHom n w : D.E) : X) = n * w * n⁻¹ := rfl

theorem psi_eq_one_iff (n : normalizer (D.E : Set X)) :
    D.psi n = 1 ↔ (n : X) ∈ centralizer (D.E : Set X) := by
  rw [psi, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    ← MonoidHom.mem_ker, normalizerMonoidHom_ker, mem_subgroupOf]

theorem E_le_centralizer : D.E ≤ centralizer (D.E : Set X) := by
  rintro _ ⟨u, hu, rfl⟩
  refine mem_centralizer_iff.mpr ?_
  rintro _ ⟨w, hw, rfl⟩
  rw [← map_mul, ← map_mul, (ut_mul_comm_iff w u).mpr (by
    rw [mem_Eu.mp hu, mem_Eu.mp hw, mul_zero, mul_zero])]

theorem conj_mem_centralizer {n c : X} (hn : n ∈ normalizer (D.E : Set X))
    (hc : c ∈ centralizer (D.E : Set X)) : n * c * n⁻¹ ∈ centralizer (D.E : Set X) := by
  refine mem_centralizer_iff.mpr fun e he => ?_
  have he' : n⁻¹ * e * n⁻¹⁻¹ ∈ D.E := (mem_normalizer_iff.mp (inv_mem hn) e).mp he
  have h := mem_centralizer_iff.mp hc _ he'
  calc e * (n * c * n⁻¹) = n * ((n⁻¹ * e * n⁻¹⁻¹) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * e * n⁻¹⁻¹)) * n⁻¹ := by rw [h]
    _ = n * c * n⁻¹ * e := by group

variable [Finite X]

theorem T_le_normalizer : (D.T : Subgroup X) ≤ normalizer (D.E : Set X) := by
  intro t ht
  obtain ⟨u, rfl⟩ := D.exists_toX ht
  refine mem_normalizer_fintype fun w hw => ?_
  obtain ⟨w', hw', rfl⟩ := hw
  rw [← map_inv, ← map_mul, ← map_mul, ut_conj]
  exact D.toX_mem_E_iff.mpr (mem_Eu.mp hw')

theorem psi_toX (u : UT3 F4c) :
    ((D.psi ⟨D.toX u, D.T_le_normalizer (D.toX_mem u)⟩ : GL4) : M4) =
      (e0 u.b.a u.b.b).toMat := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  have hv : Multiplicative.toAdd (D.eE ⟨D.toX ⟨⟨v 0, v 1⟩, 0, ⟨v 2, v 3⟩⟩,
      D.toX_mem_E_iff.mpr rfl⟩) = v := by
    rw [D.eE_toX rfl]
    funext i
    fin_cases i <;> rfl
  have h1 : D.E.normalizerMonoidHom ⟨D.toX u, D.T_le_normalizer (D.toX_mem u)⟩
      ⟨D.toX ⟨⟨v 0, v 1⟩, 0, ⟨v 2, v 3⟩⟩, D.toX_mem_E_iff.mpr rfl⟩ =
      ⟨D.toX (u * ⟨⟨v 0, v 1⟩, 0, ⟨v 2, v 3⟩⟩ * u⁻¹),
        D.toX_mem_E_iff.mpr (by rw [ut_conj])⟩ := by
    apply Subtype.ext
    rw [coe_normalizerMonoidHom]
    change D.toX u * D.toX _ * (D.toX u)⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul]
  rw [← hv, D.psi_mulVec, h1, D.eE_toX (u := u * ⟨⟨v 0, v 1⟩, 0, ⟨v 2, v 3⟩⟩ * u⁻¹)
    (by rw [ut_conj]), D.eE_toX (u := ⟨⟨v 0, v 1⟩, 0, ⟨v 2, v 3⟩⟩) rfl]
  have h2 := congrArg V4c.toVec (conj_coords u ⟨v 0, v 1⟩ ⟨v 2, v 3⟩)
  rw [M4c.toVec_mulVec] at h2
  exact h2

theorem T_le_normalizer_centralizer :
    (D.T : Subgroup X) ≤ normalizer (centralizer (D.E : Set X) : Set X) := fun _ ht =>
  mem_normalizer_fintype fun _ hc => D.conj_mem_centralizer (D.T_le_normalizer ht) hc

theorem coe_T_sup_centralizer : (((D.T : Subgroup X) ⊔ centralizer (D.E : Set X) : Subgroup X) :
    Set X) = (D.T : Set X) * (centralizer (D.E : Set X) : Set X) :=
  coe_mul_of_left_le_normalizer_right _ _ D.T_le_normalizer_centralizer

theorem exists_conj_not_mem_of_isAlperin (hE : IsAlperinSubgroup 2 (D.T : Subgroup X) D.E) :
    ∃ n ∈ normalizer (D.E : Set X), ∃ t ∈ (D.T : Subgroup X),
      n * t * n⁻¹ ∉ (D.T : Subgroup X) ⊔ centralizer (D.E : Set X) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, -, -, hrad⟩ := hE
  have hTN := D.T_le_normalizer
  set R : Subgroup X := (D.T : Subgroup X) ⊔ centralizer (D.E : Set X) with hR
  have hRmul : (R : Set X) = (D.T : Set X) * (centralizer (D.E : Set X) : Set X) :=
    D.coe_T_sup_centralizer
  have hEC : D.E ⊔ centralizer (D.E : Set X) = centralizer (D.E : Set X) :=
    sup_eq_right.mpr D.E_le_centralizer
  have hQC : D.E ⊔ centralizer (D.E : Set X) ≤ R := by
    rw [hEC]
    exact le_sup_right
  have hRN : R ≤ normalizer (D.E : Set X) := sup_le hTN (centralizer_le_normalizer D.E)
  have hRnorm : normalizer (D.E : Set X) ≤ normalizer (R : Set X) := by
    intro n hn
    refine mem_normalizer_fintype fun r hr => ?_
    have hr' : r ∈ (D.T : Set X) * (centralizer (D.E : Set X) : Set X) := hRmul ▸ hr
    obtain ⟨t, ht, c, hc, rfl⟩ := hr'
    rw [show n * (t * c) * n⁻¹ = (n * t * n⁻¹) * (n * c * n⁻¹) by group]
    exact mul_mem (hcon n hn t ht)
      (le_sup_right (a := (D.T : Subgroup X)) (D.conj_mem_centralizer hn hc))
  have hidx : ∃ k : ℕ, ((D.E ⊔ centralizer (D.E : Set X)).subgroupOf R).index = 2 ^ k := by
    rw [hEC]
    have hTR : (D.T : Subgroup X) ≤ R := le_sup_left
    have : ((centralizer (D.E : Set X)).subgroupOf R).Normal :=
      ⟨fun x hx g => mem_subgroupOf.mpr (D.conj_mem_centralizer (hRN g.2) (mem_subgroupOf.mp hx))⟩
    let f : (D.T : Subgroup X) →* R ⧸ (centralizer (D.E : Set X)).subgroupOf R :=
      (QuotientGroup.mk' _).comp (inclusion hTR)
    have hf : Function.Surjective f := by
      intro q
      obtain ⟨⟨r, hr⟩, rfl⟩ := QuotientGroup.mk_surjective q
      have hr' : r ∈ (D.T : Set X) * (centralizer (D.E : Set X) : Set X) := hRmul ▸ hr
      obtain ⟨t, ht, c, hc, rfl⟩ := hr'
      refine ⟨⟨t, ht⟩, ?_⟩
      change (QuotientGroup.mk (inclusion hTR ⟨t, ht⟩) : R ⧸ _) = QuotientGroup.mk _
      rw [QuotientGroup.eq, mem_subgroupOf]
      change t⁻¹ * (t * c) ∈ _
      rw [inv_mul_cancel_left]
      exact hc
    have hP : IsPGroup 2 (R ⧸ (centralizer (D.E : Set X)).subgroupOf R) :=
      D.T.isPGroup'.of_surjective f hf
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
    exact ⟨k, by rw [index_eq_card, hk]⟩
  have hReq := hrad R hQC hRN hRnorm hidx
  have hT : D.toX ⟨0, 1, 0⟩ ∈ centralizer (D.E : Set X) := by
    rw [← hEC, ← hReq]
    exact le_sup_left (a := (D.T : Subgroup X)) (D.toX_mem _)
  have h1 := mem_centralizer_iff.mp hT (D.toX ⟨1, 0, 0⟩) (D.toX_mem_E_iff.mpr rfl)
  rw [← map_mul, ← map_mul] at h1
  have h2 := (ut_mul_comm_iff _ _).mp (D.toX_injective h1)
  exact absurd h2 (by decide)

theorem exists_conj_eq_of_not_mem
    (hn : ∃ n ∈ normalizer (D.E : Set X), ∃ t ∈ (D.T : Subgroup X),
      n * t * n⁻¹ ∉ (D.T : Subgroup X) ⊔ centralizer (D.E : Set X))
    {e : X} (he : e ∈ D.E) (he1 : e ≠ 1) :
    ∃ n ∈ normalizer (D.E : Set X), n * D.toX ⟨0, 0, 1⟩ * n⁻¹ = e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN := D.T_le_normalizer
  let Tn : Sylow 2 (normalizer (D.E : Set X)) := D.T.subtype hTN
  let S : Sylow 2 D.psi.range := Tn.mapSurjective D.psi.rangeRestrict_surjective
  have hmemTn : ∀ t : normalizer (D.E : Set X), t ∈ Tn ↔ (t : X) ∈ (D.T : Subgroup X) := by
    intro t
    change t ∈ (Tn : Subgroup _) ↔ _
    rw [Sylow.coe_subtype, mem_subgroupOf]
  have hmemS : ∀ x : D.psi.range, x ∈ S ↔ ∃ t ∈ Tn, D.psi.rangeRestrict t = x := by
    intro x
    change x ∈ (S : Subgroup _) ↔ _
    rw [Sylow.coe_mapSurjective, mem_map]
    rfl
  have hS : ∀ y : M4, (∃ x ∈ S, ((D.psi.range.subtype x : GL4) : M4) = y) ↔ y ∈ listSet e0c := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨t, ht, rfl⟩ := (hmemS x).mp hx
      obtain ⟨u, hu⟩ := D.exists_toX ((hmemTn t).mp ht)
      have htu : t = ⟨D.toX u, D.T_le_normalizer (D.toX_mem u)⟩ := Subtype.ext hu.symm
      subst htu
      exact ⟨e0 u.b.a u.b.b, e0_mem _ _, (D.psi_toX u).symm⟩
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨p, q, rfl⟩ := exists_e0 c hc
      refine ⟨D.psi.rangeRestrict ⟨D.toX ⟨0, ⟨p, q⟩, 0⟩, D.T_le_normalizer (D.toX_mem _)⟩,
        (hmemS _).mpr ⟨_, (hmemTn _).mpr (D.toX_mem _), rfl⟩, ?_⟩
      exact D.psi_toX ⟨0, ⟨p, q⟩, 0⟩
  have hn' : ∃ h : D.psi.range, ∃ x ∈ S, h * x * h⁻¹ ∉ S := by
    obtain ⟨n, hn, t, ht, hnt⟩ := hn
    refine ⟨D.psi.rangeRestrict ⟨n, hn⟩, D.psi.rangeRestrict ⟨t, hTN ht⟩,
      (hmemS _).mpr ⟨_, (hmemTn _).mpr ht, rfl⟩, fun hmem => hnt ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul] at hmem
    obtain ⟨t', ht', heq⟩ := (hmemS _).mp hmem
    have heq' : D.psi t' = D.psi (⟨n, hn⟩ * ⟨t, hTN ht⟩ * ⟨n, hn⟩⁻¹) := by
      have h3 := congrArg Subtype.val heq
      simpa only [MonoidHom.coe_rangeRestrict] using h3
    have h2 : D.psi (t'⁻¹ * (⟨n, hn⟩ * ⟨t, hTN ht⟩ * ⟨n, hn⟩⁻¹)) = 1 := by
      rw [map_mul, map_inv, heq', inv_mul_cancel]
    have hc := (D.psi_eq_one_iff _).mp h2
    have hmem' : n * t * n⁻¹ = (t' : X) * ((t' : X)⁻¹ * (n * t * n⁻¹)) := by group
    rw [hmem']
    exact mul_mem (le_sup_left (a := (D.T : Subgroup X)) ((hmemTn t').mp ht'))
      (le_sup_right (a := (D.T : Subgroup X)) hc)
  have hv : Multiplicative.toAdd (D.eE ⟨e, he⟩) ≠ 0 := fun h => he1 (by
    have h' : D.eE ⟨e, he⟩ = 1 := Multiplicative.toAdd.injective h
    rw [MulEquiv.map_eq_one_iff] at h'
    exact congrArg Subtype.val h')
  obtain ⟨g, hg⟩ := transitive_of_sylow D.psi.range.subtype D.psi.range.subtype_injective S hS
    hn' hv
  obtain ⟨n, hng⟩ := g.2
  refine ⟨n, n.2, ?_⟩
  have hz : V4c.v0.toVec =
      Multiplicative.toAdd (D.eE ⟨D.toX ⟨0, 0, 1⟩, D.toX_mem_E_iff.mpr rfl⟩) := by
    rw [D.eE_toX rfl]
    funext i
    fin_cases i <;> rfl
  rw [hz, subtype_apply, ← hng, D.psi_mulVec] at hg
  have h3 := D.eE.injective (Multiplicative.toAdd.injective hg)
  exact congrArg Subtype.val h3

theorem exists_conj_eq_of_isAlperin
    (hE : IsAlperinSubgroup 2 (D.T : Subgroup X) D.E) {e : X} (he : e ∈ D.E) (he1 : e ≠ 1) :
    ∃ n ∈ normalizer (D.E : Set X), n * D.toX ⟨0, 0, 1⟩ * n⁻¹ = e :=
  D.exists_conj_eq_of_not_mem (D.exists_conj_not_mem_of_isAlperin hE) he he1

end UTSylow

end CFSG.ComponentClassification.GHarris.ThmC
