module

public import CFSG.GH74.Generic.S1.KL3G2Shape
public import CFSG.GH74.Generic.S1.KL3SurvDef
public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.GH74.Orders.LieType
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4E8
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Edge
public import CFSG.GH74.GLS.IVK.L2.Torus
public import CFSG.GH74.GLS.IVK.L2.TorusGeneral
public import CFSG.GH74.GLS.Stage4.RestP93
public import CFSG.GH74.GLS.Stage4.RestSetup
public import CFSG.GH74.Generic.BarSubnormal
public import CFSG.GH74.Generic.S1.DecompCore
public import CFSG.GH74.Generic.S1.TFrame
public import CFSG.GH74.Generic.S1.TLeafA
public import CFSG.GH74.Generic.S1.TLeafBar
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.GH74.GLS.IVK.GHInv CFSG.GH74
open scoped MatrixGroups

namespace CFSG.GH74.Generic.S1

theorem kl3_g2_odd_aut_inner {S : Type} [Group S] (hM : LieModel S .G2 0 3 1)
    (α : MulAut S) (hα : Odd (orderOf α)) : ∃ g : S, α = MulAut.conj g := by
  have hm : UntwistedChevalleyModel S .G2 (3 ^ 1) :=
    (CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hM).2
  obtain ⟨K, hK, hKfin, hKc, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm
  have hK3 : Nat.card K = 3 := by simpa using hKc
  let e' : S ≃* ↥(adjointGroup ReeTag.G2.tag K) := e
  have hchar3 : CharP K 3 := by
    have : Fintype K := Fintype.ofFinite K
    have hdvd : ringChar K ∣ Nat.card K :=
      ringChar.dvd (by rw [Nat.card_eq_fintype_card]; exact FiniteField.cast_card_eq_zero K)
    rw [hK3] at hdvd
    have h3 : ringChar K = 3 :=
      ((Nat.dvd_prime Nat.prime_three).1 hdvd).resolve_left CharP.ringChar_ne_one
    have := ringChar.charP K
    rwa [h3] at this
  have hchar : CharP K ReeTag.G2.prime := hchar3
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ :=
    G2_three_exact_automorphism_normal_form (f := 1) le_rfl K (by simpa using hK3)
  set α' : MulAut ↥(adjointGroup ReeTag.G2.tag K) := MulAut.congr e' α with hα'
  have hodd' : Odd (orderOf α') := by rwa [hα', MulEquiv.orderOf_eq]
  have hΘ : Θ α' = 1 := by
    have h2 : ∀ x : Multiplicative (ZMod (2 * 1)), x ^ 2 = 1 := by decide
    obtain ⟨m, hm⟩ := hodd'
    have h1 : Θ α' ^ orderOf α' = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    rw [hm, pow_succ, pow_mul, h2, one_pow, one_mul] at h1
    exact h1
  have hmem : α' ∈ Θ.ker := hΘ
  rw [hker] at hmem
  obtain ⟨ĝ, hĝ⟩ := hmem
  refine ⟨e'.symm ĝ, ?_⟩
  have h1 : α = (MulAut.congr e').symm α' := by rw [hα', MulEquiv.symm_apply_apply]
  rw [h1, ← hĝ]
  ext x
  simp [MulAut.congr, MulAut.conj_apply]


theorem kl3_g2_center_bot {S : Type} [Group S] (hM : LieModel S .G2 0 3 1) :
    Subgroup.center S = ⊥ := by
  have hm : UntwistedChevalleyModel S .G2 (3 ^ 1) :=
    (CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hM).2
  obtain ⟨K, hK, hKfin, hKc, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm
  have hZ := center_adjointGroup_eq_bot (τ := Tag.G2) (K := K)
  rw [eq_bot_iff]
  intro x hx
  have hex : e x ∈ Subgroup.center ↥(adjointGroup Tag.G2 K) := by
    have h1 : e x ∈ (Subgroup.center S).map e.toMonoidHom := ⟨x, hx, rfl⟩
    rwa [show (Subgroup.center S).map e.toMonoidHom = Subgroup.center _ from
      Subgroup.map_center_eq e] at h1
  rw [hZ, Subgroup.mem_bot] at hex
  exact (Subgroup.mem_bot).2 (e.injective (by rw [hex, map_one]))

theorem kl3SurvG2 : KL3SurvG2 := by
  intro S _ _ hM F _ _ hF3 Pb hPb
  obtain ⟨e⟩ := hPb
  let z : S := ((e.symm (KL3G2.z0 F) : ↥Pb) : S)
  let d : S := ((e.symm (KL3G2.d0 F) : ↥Pb) : S)
  have hzP : z ∈ Pb := (e.symm (KL3G2.z0 F)).2
  have hdP : d ∈ Pb := (e.symm (KL3G2.d0 F)).2
  have hz2 : orderOf z = 2 := by
    show orderOf (((e.symm (KL3G2.z0 F)) : ↥Pb) : S) = 2
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact KL3G2.orderOf_z0 hF3
  have hd8 : orderOf d = 8 := by
    show orderOf (((e.symm (KL3G2.d0 F)) : ↥Pb) : S) = 8
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact KL3G2.orderOf_d0 hF3
  have hzd : z * d = d * z := by
    have h := congrArg (fun x : SL(3, F) => ((e.symm x : ↥Pb) : S)) (KL3G2.z0_d0_comm hF3)
    simpa using h
  obtain ⟨F₀, hF₀, hFin₀, Sh, hcard₀, hSz⟩ :=
    exists_shape_G2 (p := 3) (f := 1) Nat.prime_three (by norm_num) hM z hz2
  have hF₀3 : Nat.card F₀ = 3 := by simpa using hcard₀
  refine ⟨?_, ?_⟩
  · intro α hαodd hfix
    obtain ⟨g, rfl⟩ := kl3_g2_odd_aut_inner hM α hαodd
    have hcomm : ∀ p ∈ Pb, g * p = p * g := by
      intro p hp
      have h := hfix p hp
      rw [MulAut.conj_apply] at h
      calc g * p = (g * p * g⁻¹) * g := by group
        _ = p * g := by rw [h]
    have hconj_inj : Function.Injective (MulAut.conj : S →* MulAut S) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hx' : x ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro y
        have := congrArg (fun a : MulAut S => a y) hx
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc y * x = (x * y * x⁻¹) * x := by rw [this]
          _ = x * y := by group
      rw [kl3_g2_center_bot hM, Subgroup.mem_bot] at hx'
      exact hx'
    have hgodd : Odd (orderOf g) := by
      rwa [← orderOf_injective _ hconj_inj g]
    have hgz : g ∈ centralizer ({z} : Set S) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm z hzP
    have hdz : d ∈ centralizer ({z} : Set S) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hzd.symm
    let g' : ↥(centralizer ({z} : Set S)) := ⟨g, hgz⟩
    let d' : ↥(centralizer ({z} : Set S)) := ⟨d, hdz⟩
    have hg1 : g' = 1 :=
      KL3G2.shape_odd_eq_one hF₀3 hF₀3 Sh (g := g') (d := d')
        (by simpa [d', Subgroup.orderOf_mk] using hd8)
        (by simpa [g', Subgroup.orderOf_mk] using hgodd)
        (Subtype.ext (hcomm d hdP))
    have : g = 1 := congrArg Subtype.val hg1
    rw [this, map_one]
  · obtain ⟨E, -, hEc, hE2, hE8⟩ := Sh.exists_elementary_eight (by rw [hF₀3]; decide)
      (by rw [hF₀3]; decide)
    refine ⟨E.map (centralizer ({z} : Set S)).subtype, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
    · obtain ⟨a, a', ha, rfl⟩ := a
      obtain ⟨b, b', hb, rfl⟩ := b
      exact Subtype.ext (by exact congrArg (fun t : ↥(centralizer ({z} : Set S)) => (t : S)) (hEc a' ha b' hb))
    · rintro _ ⟨y, hy, rfl⟩
      have := hE2 y hy
      exact congrArg Subtype.val this
    · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hE8]
      norm_num

end CFSG.GH74.Generic.S1
