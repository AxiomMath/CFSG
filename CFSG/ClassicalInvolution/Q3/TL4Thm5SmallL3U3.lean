module

public import CFSG.ClassicalInvolution.Q3.TL4Thm5Small
public import CFSG.ClassicalInvolution.Q3.TL4MF165A
public import CFSG.ClassicalInvolution.Q3.TL4E3S3GenL3
public import CFSG.ClassicalInvolution.Q3.TL4E3S3GenU3

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace Small

section Transport

variable {X : Type} [Group X] [Finite X]

theorem alphaOf_eq_bot_of_autAlphaPairs (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a)
    (hA : AutAlphaPairs ↥(genFittingFStar X)) {z t : X} (hzF : z ∈ genFittingFStar X)
    (htF : t ∈ genFittingFStar X) (hz2 : z * z = 1) (hz1 : z ≠ 1) (htz : t ≠ z)
    (hzt : z * t = t * z) (hc : ∃ c ∈ genFittingFStar X, c * z * c⁻¹ = t) :
    alphaOf (Subgroup.closure ({z, t} : Set X)) = ⊥ := by
  set F := genFittingFStar X with hF
  have : F.Normal := genFittingFStar_normal X
  set φ : X →* MulAut ↥F := MulAut.conjNormal with hφ
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxc : x ∈ Subgroup.centralizer (F : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := DFunLike.congr_fun (MonoidHom.mem_ker.mp hx) ⟨y, hy⟩
      have h2 : x * y * x⁻¹ = y := congrArg Subtype.val h1
      calc y * x = x * y * x⁻¹ * x := by rw [h2]
        _ = x * y := by group
    rw [centralizer_genFittingFStar_eq_bot hnab] at hxc
    exact hxc
  set θ : X ≃* ↥φ.range := MonoidHom.ofInjective hφinj with hθ
  have hφF : ∀ (g : X) (hg : g ∈ F), φ g = MulAut.conj (⟨g, hg⟩ : ↥F) := fun g hg => by
    ext n
    rfl
  have hinn : ∀ g : ↥F, MulAut.conj g ∈ φ.range := fun g => ⟨g, hφF g g.2⟩
  have hθF : ∀ (g : X) (hg : g ∈ F), θ g = ⟨MulAut.conj (⟨g, hg⟩ : ↥F), hinn ⟨g, hg⟩⟩ :=
    fun g hg => Subtype.ext (hφF g hg)
  obtain ⟨c, hcF, hcz⟩ := hc
  have hA' := hA φ.range hinn ⟨z, hzF⟩ ⟨t, htF⟩ (Subtype.ext hz2)
    (fun h => hz1 (congrArg Subtype.val h)) (fun h => htz (congrArg Subtype.val h))
    (Subtype.ext hzt) ⟨⟨c, hcF⟩, Subtype.ext hcz⟩
  rw [← hθF z hzF, ← hθF t htF] at hA'
  have hmap : (Subgroup.closure ({z, t} : Set X)).map θ.toMonoidHom =
      Subgroup.closure ({θ z, θ t} : Set ↥φ.range) := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  have h1 := ExactLayer.alphaOf_map_equiv θ (Subgroup.closure ({z, t} : Set X))
  rw [hmap, hA'] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ θ.injective).mp h1.symm

end Transport

theorem leaf_u3Ne3 : Thm5SmallLeaf TA3.SmallU3Ne3 := by
  intro X _ _ _ Φ hΦ hO hs hnab htr hgen _ hPF K hK J hJ z t hz ht
  obtain ⟨htz, hzt⟩ := Outer.ne_and_commute_of_mem_omegaNbr hΦ hK hz hJ ht
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥K))
  obtain ⟨hd, -, -, -⟩ := tightCls_of_gen hΦ hO htr hgen hK hz S
  have := genFittingFStar_normal X
  obtain ⟨p, f, hp, hp2, hf, -, hm⟩ := hPF
  have hg : Odd (Nat.gcd 3 (p ^ f + 1)) :=
    (by decide : Odd 3).of_dvd_nat (Nat.gcd_dvd_left 3 _)
  obtain ⟨hzF, -⟩ := TA3.TightDatum.exists_cyclic4_of_outTwoCyclic hd
    (Nobq.centralizer_genFittingFStar_eq_bot hnab) (TA3.outTwoCyclic_PSU hm hg)
  obtain ⟨g, hg'⟩ := Outer.exists_conj_of_trans htr hK hz hJ.1 ht
  have htF : t ∈ genFittingFStar X := hg' ▸ (genFittingFStar_normal X).conj_mem z hzF g
  have hAP : AutAlphaPairs ↥(genFittingFStar X) :=
    autAlphaPairs_of_lieModel _ p f hp hp2 (Or.inr (Or.inl ⟨by decide, hm⟩))
  obtain ⟨⟨hℓ, hm1, -, -⟩, Kf, _, _, hK', ⟨e⟩⟩ := hm
  have h : UnitaryFieldData p f Kf := ⟨hℓ, hm1, by rw [hK', ← pow_mul, mul_comm]⟩
  have ho : ∀ (y : X) (hy : y ∈ genFittingFStar X), y * y = 1 → y ≠ 1 →
      orderOf (e ⟨y, hy⟩) = 2 := fun y hy hy2 hy1 => by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  obtain ⟨c, hc⟩ := E3S3Gen.exists_conj_psu3 h hp2 (ho z hzF hz.sq hz.ne_one)
    (ho t htF ht.sq ht.ne_one)
  refine alphaOf_eq_bot_of_autAlphaPairs hs hnab hAP hzF htF hz.sq hz.ne_one htz hzt
    ⟨e.symm c, (e.symm c).2, ?_⟩
  have h1 := congrArg (fun y => ((e.symm y : ↥(genFittingFStar X)) : X)) hc
  simpa using h1

theorem mem_fstar_of_psl3 {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R}
    {z : X} (hD : TightDatum R S z) (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a)
    [IsSimpleGroup ↥(genFittingFStar X)] {Kf : Type} [Field Kf] [Finite Kf]
    (e : ↥(genFittingFStar X) ≃* projectiveSL 3 Kf) : z ∈ genFittingFStar X := by
  have : (genFittingFStar X).Normal := genFittingFStar_normal X
  have hC : Subgroup.centralizer ((genFittingFStar X : Subgroup X) : Set X) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot hnab
  set N := genFittingFStar X with hN
  let ι : X →* MulAut (projectiveSL 3 Kf) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : X →* MulAut ↥N)
  have hιapp : ∀ (y : X) (n : ↥N), ι y (e n) = e (MulAut.conjNormal y n) := fun y n => by
    show e ((MulAut.conjNormal y) (e.symm (e n))) = _
    rw [MulEquiv.symm_apply_apply]
  have hιN : ∀ y : X, ι y ∈ inner (projectiveSL 3 Kf) → y ∈ N := by
    rintro y ⟨m, hm⟩
    have key : ∀ x : ↥N, (e.symm m : ↥N) * x * (e.symm m)⁻¹ = MulAut.conjNormal y x := by
      intro x
      apply e.injective
      have h1 := DFunLike.congr_fun hm (e x)
      rw [hιapp] at h1
      rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulAut.conj_apply]
    have hcen : ((e.symm m : ↥N) : X)⁻¹ * y ∈ Subgroup.centralizer (N : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h2 := congrArg Subtype.val (key ⟨x, hx⟩)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply] at h2
      calc x * (((e.symm m : ↥N) : X)⁻¹ * y) =
          ((e.symm m : ↥N) : X)⁻¹ * (((e.symm m : ↥N) : X) * x * ((e.symm m : ↥N) : X)⁻¹) * y := by
            group
        _ = ((e.symm m : ↥N) : X)⁻¹ * (y * x * y⁻¹) * y := by rw [h2]
        _ = ((e.symm m : ↥N) : X)⁻¹ * y * x := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcen
    rw [← hcen]
    exact (e.symm m).2
  obtain ⟨φ, -, -, hφt⟩ := TA3.datum_exists_q8 hD
  have hq : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 *
      (QuaternionGroup.a 1)⁻¹ * (QuaternionGroup.xa 0)⁻¹ = QuaternionGroup.a 1 ^ 2 := by decide
  have ht' : z = φ (QuaternionGroup.a 1) * φ (QuaternionGroup.xa 0) *
      (φ (QuaternionGroup.a 1))⁻¹ * (φ (QuaternionGroup.xa 0))⁻¹ := by
    rw [← hφt, ← map_pow, ← hq, map_mul, map_mul, map_mul, map_inv, map_inv]
  have hD' : ι z ∈ linearAutGroup 3 Kf := by
    rw [ht', map_mul ι, map_mul ι, map_mul ι, map_inv ι, map_inv ι]
    exact TA3.Q5L3.commutator_mem_linearAutGroup le_rfl _ _
  have ht2 : z ^ 2 = 1 := by rw [← hD.order, pow_orderOf_eq_one]
  have h2 : ι z ^ 2 ^ 1 = 1 := by rw [← map_pow, pow_one, ht2, map_one]
  exact hιN z (TA3.Q5L3.mem_inner_of_pow hD' h2)

theorem leaf_l3Ne3 : Thm5SmallLeaf TA3.SmallL3Ne3 := by
  intro X _ _ _ Φ hΦ hO hs hnab htr hgen _ hPF K hK J hJ z t hz ht
  obtain ⟨htz, hzt⟩ := Outer.ne_and_commute_of_mem_omegaNbr hΦ hK hz hJ ht
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥K))
  obtain ⟨hd, -, -, -⟩ := tightCls_of_gen hΦ hO htr hgen hK hz S
  have := genFittingFStar_normal X
  obtain ⟨p, f, hp, hp2, hf, -, hm⟩ := hPF
  have hAP : AutAlphaPairs ↥(genFittingFStar X) :=
    autAlphaPairs_of_lieModel _ p f hp hp2 (Or.inl (Or.inl ⟨by decide, hm⟩))
  obtain ⟨-, Kf, _, _, hK', ⟨e₀⟩⟩ := hm
  let e : ↥(genFittingFStar X) ≃* projectiveSL 3 Kf :=
    (e₀.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 Kf).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 Kf)
  have hzF := mem_fstar_of_psl3 hd hnab e
  obtain ⟨g, hg'⟩ := Outer.exists_conj_of_trans htr hK hz hJ.1 ht
  have htF : t ∈ genFittingFStar X := hg' ▸ (genFittingFStar_normal X).conj_mem z hzF g
  have hodd : Odd (Nat.card Kf) := hK' ▸ (hp.odd_of_ne_two hp2).pow
  have ho : ∀ (y : X) (hy : y ∈ genFittingFStar X), y * y = 1 → y ≠ 1 →
      orderOf (e ⟨y, hy⟩) = 2 := fun y hy hy2 hy1 => by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  obtain ⟨c, hc⟩ := E3S3Gen.exists_conj_psl3 hodd (ho z hzF hz.sq hz.ne_one)
    (ho t htF ht.sq ht.ne_one)
  refine alphaOf_eq_bot_of_autAlphaPairs hs hnab hAP hzF htF hz.sq hz.ne_one htz hzt
    ⟨e.symm c, (e.symm c).2, ?_⟩
  have h1 := congrArg (fun y => ((e.symm y : ↥(genFittingFStar X)) : X)) hc
  simpa using h1

end Small

end CFSG.ClassicalInvolution.Q3.TL4
