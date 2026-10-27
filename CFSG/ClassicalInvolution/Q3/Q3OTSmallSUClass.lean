module

public import CFSG.ClassicalInvolution.Q3.Q3OTSmallSUEq
public import CFSG.ClassicalInvolution.Q3.Q3OTSmallSUKlein
public import CFSG.ClassicalInvolution.Q3.Q3OTSmallLift
public import CFSG.ClassicalInvolution.Q3.Q3OTSmallSU
public import CFSG.ClassicalInvolution.Q3.Q3OTSmallExc
public import CFSG.ClassicalInvolution.Q3.Q3NMRows
import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
public import CFSG.ClassicalInvolution.Asc77.AscT7MW
public import CFSG.ClassicalInvolution.Asc77.SU4Model
public import CFSG.ClassicalInvolution.Q3.Q3NMOrth
public import CFSG.ClassicalInvolution.Q3.Q3P21S4
public import CFSG.ClassicalInvolution.Q3.Q3TIRed
public import CFSG.ClassicalInvolution.Q3.Q3TY32
public import CFSG.ClassicalInvolution.Q3.Q3URDict
public import CFSG.ClassicalInvolution.Q3.Q3URStd

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.ModelFacts.Orth15.SqU4
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits


section Transport

variable {E : Type} [Field E] [Finite E] [Fact (Nat.Prime 3)] [CharP E 3]

theorem exists_transport (Pm : GL (Fin 4) E)
    (hPm : conjTr (unitaryInvolution E 3 1) (Pm : Matrix (Fin 4) (Fin 4) E) *
      (Pm : Matrix (Fin 4) (Fin 4) E) = antidiag 4)
    (Dm : Matrix (Fin 4) (Fin 4) E) (hDD : Dm * Dm = 1)
    (hDu : conjTr (unitaryInvolution E 3 1) Dm * Dm = 1) :
    ∃ (D : GL (Fin 4) E)
      (hDg : cT (unitaryInvolution E 3 1) (D : Matrix (Fin 4) (Fin 4) E) * antidiag 4 *
        (D : Matrix (Fin 4) (Fin 4) E) = antidiag 4),
      D * D = 1 ∧ ∀ s : SU (unitaryInvolution E 3 1) 4,
        suMat (Unitary.conjEquiv Pm hPm (Q3NM.conjAut (SU (unitaryInvolution E 3 1) 4) D
          (Q3NM.mem_normalizer_SU hDg) s)) =
          Dm * suMat (Unitary.conjEquiv Pm hPm s) * Dm := by
  have hPP : (Pm : Matrix (Fin 4) (Fin 4) E) *
      ((Pm⁻¹ : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨Dg, hDg⟩ : ∃ Dg : GL (Fin 4) E, (Dg : Matrix (Fin 4) (Fin 4) E) = Dm :=
    ⟨⟨Dm, Dm, hDD, hDD⟩, rfl⟩
  have hDgDg : Dg * Dg = 1 := Units.ext (by rw [Units.val_mul, hDg, hDD, Units.val_one])
  obtain ⟨D, hDdef⟩ : ∃ D : GL (Fin 4) E, D = Pm⁻¹ * Dg * Pm := ⟨_, rfl⟩
  have hDD' : D * D = 1 := by
    calc D * D = Pm⁻¹ * (Dg * Dg) * Pm := by
          rw [hDdef]
          group
      _ = 1 := by
          rw [hDgDg]
          group
  have hDi : D⁻¹ = D := inv_eq_of_mul_eq_one_right hDD'
  have hDmat : (D : Matrix (Fin 4) (Fin 4) E) =
      ((Pm⁻¹ : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) * Dm *
        (Pm : Matrix (Fin 4) (Fin 4) E) := by
    rw [hDdef, Units.val_mul, Units.val_mul, hDg]
  have hDg2 : cT (unitaryInvolution E 3 1) (D : Matrix (Fin 4) (Fin 4) E) * antidiag 4 *
      (D : Matrix (Fin 4) (Fin 4) E) = antidiag 4 := by
    rw [hDmat]
    show conjTr (unitaryInvolution E 3 1) (((Pm⁻¹ : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) *
        Dm * (Pm : Matrix (Fin 4) (Fin 4) E)) * antidiag 4 *
          (((Pm⁻¹ : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) * Dm *
            (Pm : Matrix (Fin 4) (Fin 4) E)) = antidiag 4
    have h1 : conjTr (unitaryInvolution E 3 1) ((Pm⁻¹ : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) *
        conjTr (unitaryInvolution E 3 1) (Pm : Matrix (Fin 4) (Fin 4) E) = 1 := by
      rw [← conjTr_mul, hPP, conjTr_one]
    calc conjTr (unitaryInvolution E 3 1) (((Pm⁻¹ : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) *
          Dm * (Pm : Matrix (Fin 4) (Fin 4) E)) * antidiag 4 *
          (((Pm⁻¹ : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) * Dm *
            (Pm : Matrix (Fin 4) (Fin 4) E))
        = conjTr (unitaryInvolution E 3 1) (Pm : Matrix (Fin 4) (Fin 4) E) *
          (conjTr (unitaryInvolution E 3 1) Dm *
            (conjTr (unitaryInvolution E 3 1) ((Pm⁻¹ : GL (Fin 4) E) :
              Matrix (Fin 4) (Fin 4) E) * conjTr (unitaryInvolution E 3 1)
                (Pm : Matrix (Fin 4) (Fin 4) E)) *
            ((Pm : Matrix (Fin 4) (Fin 4) E) *
              ((Pm⁻¹ : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E)) * Dm) *
          (Pm : Matrix (Fin 4) (Fin 4) E) := by
          rw [conjTr_mul, conjTr_mul, ← hPm]
          simp only [Matrix.mul_assoc]
      _ = antidiag 4 := by
          simp only [h1, hPP, Matrix.mul_one, hDu]
          exact hPm
  refine ⟨D, hDg2, hDD', fun s => ?_⟩
  have hA : ∀ t : SU (unitaryInvolution E 3 1) 4, suMat (Unitary.conjEquiv Pm hPm t) =
      ((Pm * (t : GL (Fin 4) E) * Pm⁻¹ : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) :=
    fun t => rfl
  have h2 : ((Q3NM.conjAut (SU (unitaryInvolution E 3 1) 4) D (Q3NM.mem_normalizer_SU hDg2) s :
      SU (unitaryInvolution E 3 1) 4) : GL (Fin 4) E) = D * (s : GL (Fin 4) E) * D⁻¹ :=
    Q3NM.conjAut_apply _ _ _ _
  have h3 : Pm * (D * (s : GL (Fin 4) E) * D⁻¹) * Pm⁻¹ =
      Dg * (Pm * (s : GL (Fin 4) E) * Pm⁻¹) * Dg := by
    rw [hDi, hDdef]
    group
  rw [hA, hA, h2, h3]
  simp only [Units.val_mul, hDg]

end Transport

local notation "𝔽₉" => GaloisField 3 (2 * 1)
local notation "SU₄" => SU (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) 4

section Klein

theorem klein_class3 {H : Type} [Group H] (hperf : Group.IsPerfect SU₄)
    (Pm : GL (Fin 4) 𝔽₉)
    (hPm : conjTr (unitaryInvolution 𝔽₉ 3 1) (Pm : Matrix (Fin 4) (Fin 4) 𝔽₉) *
      (Pm : Matrix (Fin 4) (Fin 4) 𝔽₉) = antidiag 4)
    (ψ : SU₄ →* H) (hker : ψ.ker ≤ Subgroup.center SU₄) {R R' : Subgroup SU₄}
    (hR : R.map (Unitary.conjEquiv Pm hPm).toMonoidHom ∈
      longRootSetU (K := 𝔽₉) (p := 3) (f := 1) (show 2 ≤ 4 by norm_num))
    (hR' : R'.map (Unitary.conjEquiv Pm hPm).toMonoidHom ∈
      longRootSetU (K := 𝔽₉) (p := 3) (f := 1) (show 2 ≤ 4 by norm_num))
    (hne : R ≠ R') {x x' : SU₄} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1) (hsame : ψ x = ψ x')
    {k : SU₄} (hkR : k ∈ R) (hkk : ψ k * ψ k = ψ x) (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvv : v * v = FrameVertex.innerHom ψ x) :
    ∃ (D : GL (Fin 4) 𝔽₉)
      (hDg : cT (unitaryInvolution 𝔽₉ 3 1) (D : Matrix (Fin 4) (Fin 4) 𝔽₉) * antidiag 4 *
        (D : Matrix (Fin 4) (Fin 4) 𝔽₉) = antidiag 4),
      D * D = 1 ∧ ∀ s : SU₄,
        ((FrameVertex.innerHom ψ k * v : ↥(inducedAutOn ψ.range)) :
          MulAut ↥ψ.range) (ψ.rangeRestrict s) =
          ψ.rangeRestrict (Q3NM.conjAut SU₄ D (Q3NM.mem_normalizer_SU hDg) s) := by
  have : Group.IsPerfect SU₄ := hperf
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hK : Nat.card 𝔽₉ = (3 ^ 1) ^ 2 := card_galoisField_two_mul 3 1 le_rfl
  set e := Unitary.conjEquiv Pm hPm with he
  set π : SU₄ →* PU 𝔽₉ 3 1 :=
    (QuotientGroup.mk' (Subgroup.center (Su 𝔽₉ 3 1 4))).comp e.toMonoidHom with hπdef
  have hπk : π.ker = Subgroup.center SU₄ := by
    ext s
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (e s) : Su 𝔽₉ 3 1 4 ⧸ _) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact mulEquiv_mem_center_iff e s
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp e.surjective
  have hfix : ∀ r : SU₄, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v →
      outerAction ψ hker π hπ hπk v (π r) = π r := by
    intro r hr
    apply (outerEquiv ψ hker π hπ hπk).injective
    apply Subtype.ext
    rw [outerAction_apply, outerEquiv_apply, hr]
    group
  have hφ2 : outerAction ψ hker π hπ hπk v * outerAction ψ hker π hπ hπk v =
      MulAut.conj (π x) := by
    rw [← map_mul, hvv, outerAction_innerHom]
  have hkk' : π k * π k = π x := by
    have h1 : k * k * x⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hkk, mul_inv_cancel]
    have h3 : k * k * x⁻¹ ∈ π.ker := by
      rw [hπk]
      exact hker h1
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv] at h3
    exact mul_inv_eq_one.mp h3
  have hc : x' * x⁻¹ ∈ Subgroup.center SU₄ := by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hsame, mul_inv_cancel]
  have hne' : R.map e.toMonoidHom ≠ R'.map e.toMonoidHom := fun h =>
    hne (Subgroup.map_injective e.injective h)
  have hc' : e x' * (e x)⁻¹ ∈ Subgroup.center (Su 𝔽₉ 3 1 4) := by
    have := (mulEquiv_mem_center_iff e (x' * x⁻¹)).mpr hc
    rwa [map_mul, map_inv] at this
  obtain ⟨Dm, hDD, hDu, hact⟩ := su4_klein_matrix3 (K := 𝔽₉) (p := 3) (f := 1) hK hp2 le_rfl
    (fun z hz => Q3.Q3P21.cop_center_su4_three z hz) pow3_su_two hR hR' hne'
    (x := e x) (x' := e x') ⟨x, hxR, rfl⟩ (by rw [← map_mul, hx2, map_one])
    (fun h => hx1 (e.injective (h.trans (map_one e).symm))) ⟨x', hx'R', rfl⟩
    (by rw [← map_mul, hx'2, map_one])
    (fun h => hx'1 (e.injective (h.trans (map_one e).symm))) hc' (k := e k) ⟨k, hkR, rfl⟩ hkk'
    (φ := outerAction ψ hker π hπ hπk v)
    (by
      rintro _ ⟨r, hr, rfl⟩
      exact hfix r (hvR r hr))
    (by
      rintro _ ⟨r, hr, rfl⟩
      exact hfix r (hvR' r hr)) hφ2
  obtain ⟨D, hDg, hDD', hDmat⟩ := exists_transport Pm hPm Dm hDD hDu
  refine ⟨D, hDg, hDD', fun s => ?_⟩
  refine apply_rangeRestrict_eq ψ (FrameVertex.innerHom ψ k * v)
    (Q3NM.conjAut SU₄ D (Q3NM.mem_normalizer_SU hDg)) (fun s' => ?_) s
  refine conj_innerHom_of_outerAction ψ hker π hπ hπk (FrameVertex.innerHom ψ k * v) ?_
  have hy : outerAction ψ hker π hπ hπk (FrameVertex.innerHom ψ k * v) =
      MulAut.conj (QuotientGroup.mk (e k) : PU 𝔽₉ 3 1) * outerAction ψ hker π hπ hπk v := by
    rw [map_mul, outerAction_innerHom]
    rfl
  rw [hy]
  obtain ⟨h', hh', hmat⟩ := hact.2.2 (e s')
  have hh'e : h' = e (Q3NM.conjAut SU₄ D (Q3NM.mem_normalizer_SU hDg) s') :=
    suMat_injective (hmat.trans (hDmat s').symm)
  rw [hh'e] at hh'
  exact hh'

end Klein

section Rows

theorem twinSqAlpha3_psu (hadm : StatedLieAdmissible .PSU 4 3 1) : TwinSqAlpha 3 1 .PSU 4 := by
  obtain ⟨Pm, hPm, hφP⟩ := psu_model_equiv_P hadm
  have hperf : Group.IsPerfect (modelUniv .PSU 4 3 1 Fact.out).K :=
    Group.isPerfect_def.2
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .PSU 4 3 1 Fact.out trivial hadm).1.1
  have hnc := fund_noncentral_modelUniv (t := .PSU) (n := 4) trivial hadm (by simp)
  intro H _ _ ψ R R' x x' hpair k hkR hkk v hvR hvR' hvv
  have hodd := Q3NM.autOddFreeOn_PSU (n := 4) (by norm_num) ψ.rangeRestrict
    ψ.rangeRestrict_surjective ((MonoidHom.ker_rangeRestrict ψ).le.trans hpair.ker)
  have hxx : ψ x * ψ x = 1 := by rw [← map_mul, hpair.hx2, map_one]
  have hxx' : FrameVertex.innerHom ψ x * FrameVertex.innerHom ψ x = 1 := by
    rw [← map_mul, hpair.hx2, map_one]
  have hik : FrameVertex.innerHom ψ k * FrameVertex.innerHom ψ k = FrameVertex.innerHom ψ x := by
    rw [← map_mul]
    exact innerHom_congr ψ (by rw [map_mul]; exact hkk)
  have hvk : v * FrameVertex.innerHom ψ k = FrameVertex.innerHom ψ k * v := hvR k hkR
  have hvx : v * FrameVertex.innerHom ψ x = FrameVertex.innerHom ψ x * v :=
    hvR x hpair.hx
  have hy2 : (FrameVertex.innerHom ψ k * v) * (FrameVertex.innerHom ψ k * v) = 1 := by
    calc FrameVertex.innerHom ψ k * v * (FrameVertex.innerHom ψ k * v)
        = FrameVertex.innerHom ψ k * (v * FrameVertex.innerHom ψ k) * v := by
          simp only [mul_assoc]
      _ = FrameVertex.innerHom ψ k * (FrameVertex.innerHom ψ k * v) * v := by rw [hvk]
      _ = (FrameVertex.innerHom ψ k * FrameVertex.innerHom ψ k) * (v * v) := by
          simp only [mul_assoc]
      _ = 1 := by rw [hik, hvv, hxx']
  have hik' : FrameVertex.innerHom ψ k * FrameVertex.innerHom ψ x =
      FrameVertex.innerHom ψ x * FrameVertex.innerHom ψ k := by
    rw [← hik]
    exact (mul_assoc _ _ _).symm
  have hyz : (FrameVertex.innerHom ψ k * v) * FrameVertex.innerHom ψ x =
      FrameVertex.innerHom ψ x * (FrameVertex.innerHom ψ k * v) := by
    calc FrameVertex.innerHom ψ k * v * FrameVertex.innerHom ψ x
        = FrameVertex.innerHom ψ k * (v * FrameVertex.innerHom ψ x) := by rw [mul_assoc]
      _ = FrameVertex.innerHom ψ k * (FrameVertex.innerHom ψ x * v) := by rw [hvx]
      _ = (FrameVertex.innerHom ψ k * FrameVertex.innerHom ψ x) * v := by rw [mul_assoc]
      _ = (FrameVertex.innerHom ψ x * FrameVertex.innerHom ψ k) * v := by rw [hik']
      _ = FrameVertex.innerHom ψ x * (FrameVertex.innerHom ψ k * v) := by rw [mul_assoc]
  have hz1 : FrameVertex.innerHom ψ x ≠ 1 := by
    intro h
    exact hpair.hx1 (hnc R hpair.mem x hpair.hx
      ((FrameVertex.innerHom_spec ψ hpair.ker).1 x h))
  have hkR' : k⁻¹ ∈ R := R.inv_mem hkR
  have hkk' : ψ k⁻¹ * ψ k⁻¹ = ψ x := by
    rw [map_inv, ← _root_.mul_inv_rev, hkk]
    exact inv_eq_of_mul_eq_one_right hxx
  have hψkx : ψ (k * x) = ψ k⁻¹ := by
    rw [map_mul, map_inv, ← hkk]
    have h4 : ψ k * (ψ k * (ψ k * ψ k)) = 1 := by
      have : ψ k * ψ k * (ψ k * ψ k) = 1 := by
        rw [hkk]
        exact hxx
      simpa only [mul_assoc] using this
    exact (inv_eq_of_mul_eq_one_right h4).symm
  have hyz' : (FrameVertex.innerHom ψ k * v) * FrameVertex.innerHom ψ x =
      FrameVertex.innerHom ψ k⁻¹ * v := by
    calc FrameVertex.innerHom ψ k * v * FrameVertex.innerHom ψ x
        = FrameVertex.innerHom ψ k * (v * FrameVertex.innerHom ψ x) := by rw [mul_assoc]
      _ = FrameVertex.innerHom ψ k * (FrameVertex.innerHom ψ x * v) := by rw [hvx]
      _ = (FrameVertex.innerHom ψ k * FrameVertex.innerHom ψ x) * v := by rw [mul_assoc]
      _ = FrameVertex.innerHom ψ (k * x) * v := by rw [map_mul]
      _ = FrameVertex.innerHom ψ k⁻¹ * v := by rw [innerHom_congr ψ hψkx]
  have hP1 := klein_class3 hperf Pm hPm ψ hpair.ker ((hφP R).mp hpair.mem)
    ((hφP R').mp hpair.mem') hpair.ne hpair.hx hpair.hx2 hpair.hx1 hpair.hx' hpair.hx'2
    hpair.hx'1 hpair.same hkR hkk v hvR hvR' hvv
  have hP2 := klein_class3 hperf Pm hPm ψ hpair.ker ((hφP R).mp hpair.mem)
    ((hφP R').mp hpair.mem') hpair.ne hpair.hx hpair.hx2 hpair.hx1 hpair.hx' hpair.hx'2
    hpair.hx'1 hpair.same hkR' hkk' v hvR hvR' hvv
  refine Q3NM.alphaOf_eq_bot_of_on ψ.range _ hodd _
    (Q3NM.mul_self_eq_one_of_mem_closure_pair hy2 hxx' hyz)
    ⟨FrameVertex.innerHom ψ x, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), hz1⟩ ?_
  intro g hg hg1
  rcases mem_closure_pair_cases hy2 hxx' hyz g hg with rfl | rfl | rfl | rfl
  · exact absurd rfl hg1
  · obtain ⟨D, hDg, hDD, hlift⟩ := hP1
    exact Or.inr ⟨D, hDg, hDD, hlift⟩
  · exact Or.inl (innerHom_mem_innSubgroup ψ x)
  · obtain ⟨D, hDg, hDD, hlift⟩ := hP2
    rw [hyz']
    exact Or.inr ⟨D, hDg, hDD, hlift⟩

end Rows

end CFSG.ClassicalInvolution.Q3.Q3OT
