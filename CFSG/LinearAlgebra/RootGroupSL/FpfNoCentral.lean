module

public import CFSG.LinearAlgebra.RootGroupSL.Fpf
public import CFSG.LinearAlgebra.RootGroupSL.NormalizerX
import CFSG.LocalAnalysis.SteinbergCESolvableCoprimeLifting
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.LinearAlgebra.RootGroupSL

open CFSG.Open
open CFSG.Semidihedral.Principal.CoprimeFixedPoint
open scoped commutatorElement

variable {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]
  [Finite k] [Finite E] [Module.Finite k X] [CharP k 2]

private lemma finite_specialLinearGroup_dspace :
    Finite (SpecialLinearGroup k (DSpace E X)) := by
  haveI : Finite X := Module.finite_of_finite k
  haveI : Finite (DSpace E X) := inferInstance
  haveI : Finite (DSpace E X ≃ₗ[k] DSpace E X) :=
    Finite.of_injective (fun e : DSpace E X ≃ₗ[k] DSpace E X => e.toEquiv.toFun)
      (fun e f h => LinearEquiv.ext (fun x => congrFun h x))
  infer_instance

theorem rootNoCentral_rootSL (hdX : Module.finrank k E ≤ Module.finrank k X)
    (hstar : 2 ≤ Module.finrank k E ∨
      (Module.finrank k E = 1 ∧ 4 ≤ Nat.card k ∧ 2 ≤ Module.finrank k X))
    (A B' : Subgroup (SpecialLinearGroup k (DSpace E X)))
    (hRA : rootSL k E X ≤ A) (hAB : A ≤ B')
    (hB : B' ≤ pCoreOf 2
      (Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X)))))
    (hNA : Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))) ≤
      Subgroup.normalizer (A : Set (SpecialLinearGroup k (DSpace E X))))
    (hNB : Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))) ≤
      Subgroup.normalizer (B' : Set (SpecialLinearGroup k (DSpace E X))))
    (hc : ⁅B', Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X)))⁆ ≤
      A) : B' ≤ A := by
  have hX : 0 < Module.finrank k X :=
    lt_of_lt_of_le (Module.finrank_pos (R := k) (M := E)) hdX
  haveI : Finite (SpecialLinearGroup k (DSpace E X)) :=
    finite_specialLinearGroup_dspace (k := k) (E := E) (X := X)
  have hBQ : B' ≤ QK k E X :=
    hB.trans (le_of_eq (pCoreOf_normalizer_rootSL (k := k) (E := E) (X := X) hX))
  obtain ⟨h, hhN, hodd, hcent⟩ := exists_fpf (k := k) (E := E) (X := X) hstar
  let Nrm : Subgroup (SpecialLinearGroup k (DSpace E X)) :=
    Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X)))
  have hBN : B' ≤ Nrm :=
    hBQ.trans (QK_le_centralizer_rootSL.trans (Subgroup.centralizer_le_normalizer _))
  have hBA : ⁅B', B'⁆ ≤ A :=
    (Subgroup.commutator_mono le_rfl hBN).trans hc
  have hN_normal : (A.subgroupOf B').Normal := by
    rw [Subgroup.normal_subgroupOf_iff hAB]
    intro a b ha hb
    have hcomm : ⁅b, a⁆ ∈ A := hBA (Subgroup.commutator_mem_commutator hb (hAB ha))
    have hsplit : b * a * b⁻¹ = ⁅b, a⁆ * a := by
      rw [commutatorElement_def]
      group
    rw [hsplit]
    exact A.mul_mem hcomm ha
  haveI : (A.subgroupOf B').Normal := hN_normal
  let H : Subgroup (SpecialLinearGroup k (DSpace E X)) := Subgroup.zpowers h
  let hH : H := ⟨h, Subgroup.mem_zpowers h⟩
  have hle : H ≤ Subgroup.normalizer (B' : Set (SpecialLinearGroup k (DSpace E X))) :=
    Subgroup.zpowers_le.mpr (hNB hhN)
  let α : H →* MulAut ↥B' :=
    (Subgroup.normalizerMonoidHom (H := B')).comp (Subgroup.inclusion hle)
  have hαval : ∀ (a : H) (x : ↥B'),
      ((α a x : ↥B') : SpecialLinearGroup k (DSpace E X)) =
        (a : SpecialLinearGroup k (DSpace E X)) * (x : SpecialLinearGroup k (DSpace E X)) *
          (a : SpecialLinearGroup k (DSpace E X))⁻¹ := fun a x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe B' (Subgroup.inclusion hle a) x
  have hN_inv : ∀ a : H, ∀ n ∈ (A.subgroupOf B'), α a n ∈ (A.subgroupOf B') := by
    intro a n hn
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have haN : (a : SpecialLinearGroup k (DSpace E X)) ∈ Nrm :=
      Subgroup.zpowers_le.mpr hhN a.2
    rw [hαval a n]
    exact (Subgroup.mem_normalizer_iff.mp (hNA haN)
      (n : SpecialLinearGroup k (DSpace E X))).mp hn
  have hBp : IsPGroup 2 ↥B' :=
    (isPGroup_QK (k := k) (E := E) (X := X)).to_le hBQ
  have hcop : Nat.Coprime (Nat.card H) (Nat.card (A.subgroupOf B')) := by
    have hcardH : Nat.card H = orderOf h := Nat.card_zpowers h
    rw [hcardH]
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥B')).mp hBp
    have hdvd : Nat.card (A.subgroupOf B') ∣ 2 ^ n := by
      rw [← hn]
      exact Subgroup.card_subgroup_dvd_card _
    exact (hodd.coprime_two_right.pow_right n).coprime_dvd_right hdvd
  have hsolvH : Group.IsSolvable H := inferInstance
  have hlift :=
    CFSG.LocalAnalysis.solvable_coprime_fixed_point_lifting (A := H) (G := ↥B') hsolvH α
      (A.subgroupOf B') hN_inv hcop
  intro b hb
  let b' : ↥B' := ⟨b, hb⟩
  let q : (↥B') ⧸ (A.subgroupOf B') := b'
  have hfix_h : quotientAction α (A.subgroupOf B') hN_inv hH q = q := by
    rw [quotientAction_mk]
    change ((α hH b' : ↥B') : (↥B') ⧸ (A.subgroupOf B')) =
      (b' : (↥B') ⧸ (A.subgroupOf B'))
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    have hcomm : ⁅h, b⁆ ∈ A := by
      have h1 : ⁅h, b⁆ ∈ ⁅B', Nrm⁆ := by
        have h2 : ⁅h, b⁆ ∈ ⁅Nrm, B'⁆ := Subgroup.commutator_mem_commutator hhN hb
        rwa [← Subgroup.commutator_comm] at h2
      exact hc h1
    have hval : (((α hH b' : ↥B') / b' : ↥B') : SpecialLinearGroup k (DSpace E X)) =
        ⁅h, b⁆ := by
      rw [Subgroup.coe_div, hαval hH b', commutatorElement_def]
      rfl
    rw [hval]
    exact hcomm
  have hfix_all : ∀ a : H, quotientAction α (A.subgroupOf B') hN_inv a q = q := by
    let K : Subgroup H :=
      { carrier := {a | quotientAction α (A.subgroupOf B') hN_inv a q = q}
        one_mem' := by simp
        mul_mem' := by
          intro a c ha hc
          change quotientAction α (A.subgroupOf B') hN_inv (a * c) q = q
          rw [map_mul, MulAut.mul_apply, hc, ha]
        inv_mem' := by
          intro a ha
          change quotientAction α (A.subgroupOf B') hN_inv a⁻¹ q = q
          conv_lhs => rw [← ha]
          rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] }
    have hKtop : K = ⊤ := by
      rw [eq_top_iff]
      have htop : (⊤ : Subgroup H) = Subgroup.zpowers hH := by
        refine le_antisymm (fun a _ => ?_) le_top
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp a.2
        exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by
          rw [Subgroup.coe_zpow]
          exact hn)⟩
      rw [htop, Subgroup.zpowers_le]
      exact hfix_h
    intro a
    have ha : a ∈ K := by rw [hKtop]; exact Subgroup.mem_top a
    exact ha
  have hb_fixed : q ∈ {q : (↥B') ⧸ (A.subgroupOf B') |
      ∀ a : H, quotientAction α (A.subgroupOf B') hN_inv a q = q} := hfix_all
  have hb_mem : q ∈ QuotientGroup.mk' (A.subgroupOf B') ''
      {c : ↥B' | ∀ a : H, α a c = c} := by
    rw [← hlift]
    exact hb_fixed
  obtain ⟨b₁, hb₁fix, hb₁eq⟩ := hb_mem
  have hb₁comm : h * (b₁ : SpecialLinearGroup k (DSpace E X)) =
      (b₁ : SpecialLinearGroup k (DSpace E X)) * h := by
    have h1 : ((α hH b₁ : ↥B') : SpecialLinearGroup k (DSpace E X)) =
        (b₁ : SpecialLinearGroup k (DSpace E X)) := congrArg Subtype.val (hb₁fix hH)
    rw [hαval hH b₁] at h1
    calc h * (b₁ : SpecialLinearGroup k (DSpace E X)) =
          (h * (b₁ : SpecialLinearGroup k (DSpace E X)) * h⁻¹) * h := by group
      _ = (b₁ : SpecialLinearGroup k (DSpace E X)) * h := by rw [h1]
  have hb₁cent : (b₁ : SpecialLinearGroup k (DSpace E X)) ∈
      Subgroup.centralizer ({h} : Set (SpecialLinearGroup k (DSpace E X))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hb₁comm
  have hb₁R : (b₁ : SpecialLinearGroup k (DSpace E X)) ∈ rootSL k E X := by
    have hb₁Q : (b₁ : SpecialLinearGroup k (DSpace E X)) ∈ QK k E X := hBQ b₁.2
    have hmem : (b₁ : SpecialLinearGroup k (DSpace E X)) ∈
        Subgroup.centralizer ({h} : Set (SpecialLinearGroup k (DSpace E X))) ⊓ QK k E X :=
      ⟨hb₁cent, hb₁Q⟩
    rwa [hcent] at hmem
  have hb₁memA : (b₁ : SpecialLinearGroup k (DSpace E X)) ∈ A := hRA hb₁R
  have hdiv : (b₁ : (↥B') ⧸ (A.subgroupOf B')) = (b' : (↥B') ⧸ (A.subgroupOf B')) := hb₁eq
  have hprodA : (((b₁ / b' : ↥B')) : SpecialLinearGroup k (DSpace E X)) ∈ A :=
    Subgroup.mem_subgroupOf.mp (QuotientGroup.eq_iff_div_mem.mp hdiv)
  have hbdecomp : b = (((b₁ / b' : ↥B')) : SpecialLinearGroup k (DSpace E X))⁻¹ *
      (b₁ : SpecialLinearGroup k (DSpace E X)) := by
    have hcoe : (((b₁ / b' : ↥B')) : SpecialLinearGroup k (DSpace E X)) = b₁ * b⁻¹ := by
      simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
    rw [hcoe]
    group
  rw [hbdecomp]
  exact A.mul_mem (A.inv_mem hprodA) hb₁memA

end CFSG.LinearAlgebra.RootGroupSL
