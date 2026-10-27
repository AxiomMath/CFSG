module

public import CFSG.GH74.Generic.BProg.B3.S3T2L291D
public import CFSG.GH74.Generic.BProg.B3.S3T2L291F
public import CFSG.GH74.Generic.BProg.B3.SolvAssembly
public import CFSG.GH74.Generic.BProg.B3.S3T2L291B
public import CFSG.GH74.Generic.BProg.B3.S3T2L291C

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg
  Subgroup CFSG.GH74.Generic.BProg.B1.PilotS3
open scoped commutatorElement

namespace S3T2L291

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizer_bar_of_mul {x e : G} (he : e ∈ centralizer ({x} : Set G))
    {c : CentralizerBar x} (hc : c ∈ centralizer ({bar x (e * x)} : Set (CentralizerBar x))) :
    c ∈ centralizer ({bar x e} : Set (CentralizerBar x)) := by
  have hxx : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hex : e * x ∈ centralizer ({x} : Set G) := mul_mem he hxx
  have hsurj : Function.Surjective (proj x) := QuotientGroup.mk'_surjective _
  obtain ⟨c', rfl⟩ := hsurj c
  have hxc : proj x c' * proj x ⟨x, hxx⟩ = proj x ⟨x, hxx⟩ * proj x c' := by
    rw [← map_mul, ← map_mul]
    exact congrArg (proj x) (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c'.2))
  have e1 : bar x (e * x) = proj x ⟨e, he⟩ * proj x ⟨x, hxx⟩ := by
    rw [bar_of_mem hex, ← map_mul]
    rfl
  rw [Subgroup.mem_centralizer_singleton_iff, e1] at hc
  rw [Subgroup.mem_centralizer_singleton_iff, bar_of_mem he]
  set a := proj x c'
  set u := proj x ⟨e, he⟩
  set v := proj x ⟨x, hxx⟩
  have h : a * u * v = u * a * v := by
    calc a * u * v = a * (u * v) := by group
      _ = u * v * a := hc
      _ = u * (v * a) := by group
      _ = u * (a * v) := by rw [hxc]
      _ = u * a * v := by group
  exact mul_right_cancel h

theorem nbhdSemisimple_of_solvAdm (h101 : Prop10_1Stmt) (hyp : Hyp2 G) {F : Type} [Field F]
    [Finite F] {x y : G} {K A E E₀ : Subgroup G} {Lb Ib : Subgroup (CentralizerBar x)}
    (hx : orderOf x = 2) (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hY : Split3Like F (imgBar x K)) (hEK : E ≤ K) (hAE : A = E ⊔ zpowers x)
    (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hE₀A : E₀ ≤ A) (hsol : SolvAdm x y K E₀ Lb Ib)
    (hall : ∀ e ∈ E, e ≠ 1 → NbhdSemisimple x e (Lbar x e K)) : NbhdSemisimple x y Lb := by
  obtain ⟨I0, I1, hSL, hI1Ib⟩ := exists_solvLift_mem hK hsol
  have hS := hsol.setup
  set D : Subgroup G := closure ({x, y} : Set G) with hD
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 hS.y_mem).symm
  have hDel : CFSG.IsElementaryAbelian 2 ↥D := B1.isElementaryAbelian_closure_pair hxy
    (by rw [← hx]; exact pow_orderOf_eq_one x) (by rw [← hS.y_ord]; exact pow_orderOf_eq_one y)
  have hI0I1 : I0 ≤ I1 := by
    rw [← hSL.res_I1]
    exact Balance.oPrimeResidualOf_le_self _
  have hI0Y : I0 ≤ centralizer ((D ⊔ E₀ : Subgroup G) : Set G) := hI0I1.trans hSL.le_cent
  have hIc : ∀ g ∈ D ⊔ E₀, I0 ≤ centralizer ({g} : Set G) := fun g hg i hi =>
    Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 (hI0Y hi) g hg).symm)
  have hIx : I0 ≤ centralizer ({x} : Set G) := hIc x (mem_sup_left (subset_closure (by simp)))
  set E₁ : Subgroup G := E₀ ⊓ centralizer (D : Set G) with hE₁
  have hE₁el : CFSG.IsElementaryAbelian 2 ↥E₁ :=
    Th2Sig6.isElementaryAbelian_of_le hS.E_ea inf_le_left
  have hIE₁ : I0 ≤ centralizer (E₁ : Set G) :=
    hI0Y.trans (centralizer_le ((inf_le_left.trans le_sup_right : E₁ ≤ D ⊔ E₀) : _))
  set S : Subgroup (CentralizerBar x) :=
    centralizer ((imgBar x E₀ : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)) with hSd
  have hX₀le : extLayer2 (S ⊓ Lb) ≤ S ⊓ Lb := SolvLiftBasic.extLayer2_le _
  have hLbK : Lb ≤ imgBar x K :=
    (exists_noncomm_two_elements_of_isQuasi2CompIn hsol.quasiL).1.trans inf_le_right
  have hbS : ∀ g ∈ E₀, ∀ hg : g ∈ centralizer ({x} : Set G), ∀ c ∈ S,
      c ∈ centralizer ({bar x g} : Set (CentralizerBar x)) := fun g hg hgC c hc =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hc _
      (mem_imgBar.2 ⟨⟨g, hgC⟩, hg, (bar_of_mem hgC).symm⟩)).symm
  have hlift : ∀ e ∈ E, e ≠ 1 → (e ∈ E₁ ∨ e * x ∈ E₁) → I0 ≤ centralizer ({e} : Set G) →
      I0 ≤ liftAt x e (Lbar x e K) := by
    intro e he he1 heE₁ hIe
    have heC : e ∈ centralizer ({x} : Set G) := hK.1 (hEK he)
    have hSe := isSplit3_Lbar hK.1 hY (hEK he) (orderOf_eq_two_of_mem hEel he he1)
    have hX₀e : extLayer2 (S ⊓ Lb) ≤ centralizer ({bar x e} : Set (CentralizerBar x)) ⊓
        imgBar x K := by
      refine le_inf (fun c hc => ?_) (hX₀le.trans (inf_le_right.trans hLbK))
      have hcS := (Subgroup.mem_inf.1 (hX₀le hc)).1
      rcases heE₁ with h1 | h1
      · exact hbS e (Subgroup.mem_inf.1 h1).1 heC c hcS
      · exact mem_centralizer_bar_of_mul heC
          (hbS (e * x) (Subgroup.mem_inf.1 h1).1 (hS.E_le (Subgroup.mem_inf.1 h1).1) c hcS)
    refine (le_of_eq hSL.res.symm).trans (oPrimeResidualOf_le_liftAt (le_inf hIx hIe)
      fun g hg h2 hgx => mem_of_isSolv2CompIn hSe hX₀e hsol.solvI (hI1Ib g hgx (hI0I1 hg)) ?_)
    obtain ⟨k, hk⟩ := h2
    refine ⟨k, ?_⟩
    have h3 : (⟨g, hgx⟩ : ↥(centralizer ({x} : Set G))) ^ (2 ^ k) = 1 :=
      Subtype.ext (by simpa using hk)
    rw [← map_pow, h3, map_one]
  have hB := comm_of_semisimple hx hK.1 hEK hAE (inf_le_left.trans hE₀A) hE₁el hS.E_rank hIx hIE₁
    hlift hall
  refine nbhdSemisimple_of_centralizes hx hK hsol hSL fun d hd hd1 => ?_
  refine comm_eq_bot_of_hyperplanes hSL.res hE₁el hS.E_rank (fun b hb => ?_)
    (hIc d (mem_sup_left hd)) hIE₁ (fun b hb hb1 => ?_) hB
  · exact Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hb).2 d hd).symm
  · exact h101 G hyp x y K E₀ Lb Ib I0 I1 hx hK hsol hSL d hd hd1 b (Subgroup.mem_inf.1 hb).1 hb1

end S3T2L291

end CFSG.GH74.Generic.BProg.B3
