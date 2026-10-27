module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25V4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25V0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25V2

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Q3.AE (AEQ mkQ memBar Wr)
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan)
open CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL (layerX_le_centralizer conjSub_layerX_of_mem le_layerX)
open Certificates.AE5X (memL zW)
open scoped commutatorElement


section Basic

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ c : G}

namespace AE5Layer

variable (A : AE5Layer Ω z c)

theorem one : A.ε 1 = 1 := by
  have h := A.mul 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
  rw [mul_one] at h
  exact left_eq_mul.mp h

theorem inv {y : G} (hy : y ∈ layerX Ω c) : A.ε y⁻¹ = (A.ε y)⁻¹ := by
  have h := A.mul y hy y⁻¹ ((layerX Ω c).inv_mem hy)
  rw [mul_inv_cancel, A.one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem conj_mem {g y : G} (hΩ : HypOmegaGen Ω) (hg : g ∈ Subgroup.centralizer ({c} : Set G))
    (hy : y ∈ layerX Ω c) : g * y * g⁻¹ ∈ layerX Ω c := by
  have h := Generic.conj_mem_conjSub (n := g) hy
  rwa [conjSub_layerX_of_mem hΩ hg] at h

theorem eps_conj {n y : G} (hn : n ∈ layerX Ω c) (hy : y ∈ layerX Ω c) :
    A.ε (n * y * n⁻¹) = A.ε n * A.ε y * (A.ε n)⁻¹ := by
  rw [A.mul _ ((layerX Ω c).mul_mem hn hy) _ ((layerX Ω c).inv_mem hn), A.mul _ hn _ hy, A.inv hn]

end AE5Layer

namespace Lay

variable (Λ : Lay Ω K K' W S R R' z t u₁ u₂ c)
include Λ

theorem P_le : R ⊔ R' ≤ layerX Ω c := sup_le Λ.R_le Λ.R'_le

theorem P_two : IsPGroup 2 ↥(R ⊔ R') :=
  S.isPGroup'.to_le (sup_le Λ.hyp.hR.2.2 Λ.hyp.hR'.2.2)

theorem RR'_comm : Commutes R R' := by
  obtain ⟨t', h⟩ := T7T.exists_hyp25T Λ.hyp
  exact h.hcomm

theorem z_mem_R : z ∈ R := by
  have hz : IsUniqueInvolution K z := Λ.hyp.std.setting.hz
  have hΩ : HypOmegaMod Ω := Λ.hyp.std.setting.stand.hyp
  have hKΩ : K ∈ Ω := Λ.hyp.std.1.stand.mem
  have hRK : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hKΩ Λ.hyp.hR.1 Λ.hyp.hR.2.1
  have := layer_sq_of_order_four hz (hRK.1 Λ.hyp.hu₁.1) Λ.hyp.hu₁.2.1
  rw [← this]
  exact R.mul_mem Λ.hyp.hu₁.1 Λ.hyp.hu₁.1

theorem z_mem_R' : z ∈ R' := by
  have hz : IsUniqueInvolution K z := Λ.hyp.std.setting.hz
  have hz' : IsUniqueInvolution K' z := by
    obtain ⟨-, z', hz'K, hz'J⟩ := Λ.hyp.std.1.hK'
    rwa [hz.eq hz'K]
  have hΩ : HypOmegaMod Ω := Λ.hyp.std.setting.stand.hyp
  have hK'Ω : K' ∈ Ω := Λ.hyp.std.1.hK'.1
  have hR'K' : IsSylow2In R' K' :=
    Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK'Ω Λ.hyp.hR'.1 Λ.hyp.hR'.2.1
  have := layer_sq_of_order_four hz' (hR'K'.1 Λ.hyp.hu₂.1) Λ.hyp.hu₂.2.1
  rw [← this]
  exact R'.mul_mem Λ.hyp.hu₂.1 Λ.hyp.hu₂.1

theorem hz2 : z * z = 1 := Λ.hyp.std.setting.hz.sq

end Lay

namespace AE5Layer

variable (A : AE5Layer Ω z c) (Λ : Lay Ω K K' W S R R' z t u₁ u₂ c)
include Λ

theorem inj_P {y : G} (hy : y ∈ R ⊔ R') (h : A.ε y = 1) : y = 1 :=
  eq_one_of_isPGroup_of_odd Λ.P_two (odd_card_oddCoreIn _) hy ((A.ker y (Λ.P_le hy)).1 h)

theorem inj_P2 {y₁ y₂ : G} (h₁ : y₁ ∈ R ⊔ R') (h₂ : y₂ ∈ R ⊔ R') (h : A.ε y₁ = A.ε y₂) : y₁ = y₂ := by
  have e : A.ε (y₁⁻¹ * y₂) = 1 := by
    rw [A.mul _ (Λ.P_le ((R ⊔ R').inv_mem h₁)) _ (Λ.P_le h₂), A.inv (Λ.P_le h₁), h,
      inv_mul_cancel]
  exact inv_mul_eq_one.mp (A.inj_P Λ ((R ⊔ R').mul_mem ((R ⊔ R').inv_mem h₁) h₂) e)

end AE5Layer

structure TwinLab (A : AE5Layer Ω z c) (R R' : Subgroup G) (α α' : Finset (Fin 5)) (h : α.card = 4)
    (h' : α'.card = 4) (b b' : Bool) : Prop where
  R_mem : ∀ y ∈ R, A.ε y ∈ memBar α h b
  R_surj : ∀ w ∈ memBar α h b, ∃ y ∈ R, A.ε y = w
  R'_mem : ∀ y ∈ R', A.ε y ∈ memBar α' h' b'
  R'_surj : ∀ w ∈ memBar α' h' b', ∃ y ∈ R', A.ε y = w

namespace AE5Layer

variable (A : AE5Layer Ω z c) (Λ : Lay Ω K K' W S R R' z t u₁ u₂ c)
include Λ

theorem exists_label_side {J RR : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) (hRJ : IsSylow2In RR J)
    (hRc : RR ≤ Subgroup.centralizer ({c} : Set G)) (hRX : RR ≤ layerX Ω c)
    (hRP : RR ≤ R ⊔ R') (h8 : 8 ≤ Nat.card RR) :
    ∃ (α : Finset (Fin 5)) (h : α.card = 4) (b : Bool), (∀ y ∈ RR, A.ε y ∈ memBar α h b) ∧
      ∀ w ∈ memBar α h b, ∃ y ∈ RR, A.ε y = w := by
  obtain ⟨α, h, b, h1, h2⟩ := A.lab J hJ
  have hcore : RR ≤ TwinADescent.coreAt c J :=
    le_tightCore_of_isPGroup (le_inf hRJ.1 hRc) hRJ.2.1
  refine ⟨α, h, b, fun y hy => h1 y (hRX hy) (hcore hy), ?_⟩
  let f : ↥RR → ↥(memBar α h b) := fun y => ⟨A.ε y, h1 y (hRX y.2) (hcore y.2)⟩
  have hf : Function.Injective f := by
    intro y₁ y₂ he
    apply Subtype.ext
    exact A.inj_P2 Λ (hRP y₁.2) (hRP y₂.2) (congrArg Subtype.val he)
  have hcard : Nat.card ↥(memBar α h b) ≤ Nat.card ↥RR := by
    rw [AE.natCard_memBar le_rfl α h b]
    exact h8
  have hbij := hf.bijective_of_nat_card_le hcard
  intro w hw
  obtain ⟨y, hy⟩ := hbij.2 ⟨w, hw⟩
  exact ⟨y, y.2, congrArg Subtype.val hy⟩

theorem exists_labels : ∃ (α α' : Finset (Fin 5)) (h : α.card = 4) (h' : α'.card = 4) (b b' : Bool),
    TwinLab A R R' α α' h h' b b' := by
  obtain ⟨hKtq, hK'tq, -, -, -, -⟩ := layer_twins_tq Λ.hyp Λ.hcA
  have hΩ' : HypOmegaMod Ω := Λ.hyp.std.setting.stand.hyp
  have hKΩ : K ∈ Ω := Λ.hyp.std.1.stand.mem
  have hK'Ω : K' ∈ Ω := Λ.hyp.std.1.hK'.1
  have hRK : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ' hKΩ Λ.hyp.hR.1 Λ.hyp.hR.2.1
  have hR'K' : IsSylow2In R' K' :=
    Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ' hK'Ω Λ.hyp.hR'.1 Λ.hyp.hR'.2.1
  have hRc : R ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Λ.hcR x hx).symm
  have hR'c : R' ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Λ.hcR' x hx).symm
  obtain ⟨α, h, b, h1, h2⟩ := A.exists_label_side Λ hKtq hRK hRc Λ.R_le le_sup_left
    (hΩ'.isQuatSub_of_mem_RSet Λ.hyp.hR.1).eight_le
  obtain ⟨α', h', b', h1', h2'⟩ := A.exists_label_side Λ hK'tq hR'K' hR'c Λ.R'_le le_sup_right
    (hΩ'.isQuatSub_of_mem_RSet Λ.hyp.hR'.1).eight_le
  exact ⟨α, α', h, h', b, b', ⟨h1, h2, h1', h2'⟩⟩

end AE5Layer

namespace TwinLab

variable {A : AE5Layer Ω z c} {α α' : Finset (Fin 5)} {h : α.card = 4} {h' : α'.card = 4} {b b' : Bool}
  (T : TwinLab A R R' α α' h h' b b') (Λ : Lay Ω K K' W S R R' z t u₁ u₂ c)
include T Λ

theorem comm : ∀ x ∈ memBar α h b, ∀ y ∈ memBar α' h' b', x * y = y * x := by
  intro x hx y hy
  obtain ⟨r, hr, rfl⟩ := T.R_surj x hx
  obtain ⟨r', hr', rfl⟩ := T.R'_surj y hy
  rw [← A.mul r (Λ.R_le hr) r' (Λ.R'_le hr'), ← A.mul r' (Λ.R'_le hr') r (Λ.R_le hr),
    Λ.RR'_comm r hr r' hr']

theorem eps_z : A.ε z = mkQ 5 (zW (α, b)) := by
  have hz1 : z ≠ 1 := Λ.hyp.std.setting.hz.ne_one
  have hzR := Λ.z_mem_R
  have hx : A.ε z ∈ memBar α h b := T.R_mem z hzR
  have hx1 : A.ε z ≠ 1 := fun h1 => hz1 (A.inj_P Λ (Subgroup.mem_sup_left hzR) h1)
  have hx2 : A.ε z * A.ε z = 1 := by
    rw [← A.mul z (Λ.R_le hzR) z (Λ.R_le hzR), Λ.hz2, A.one]
  exact spec_inv h b hx hx1 hx2

theorem mem_P {y : G} (hy : y ∈ R ⊔ R') :
    ∃ m ∈ memL (α, b), ∃ m' ∈ memL (α', b'), A.ε y = mkQ 5 (m * m') := by
  obtain ⟨r, hr, r', hr', rfl⟩ := mem_sup_comm Λ.RR'_comm hy
  obtain ⟨m, hm, hm'⟩ := (TL4.Mdl117.mem_memBar_iff α h b _).1 (T.R_mem r hr)
  obtain ⟨m', hm2, hm2'⟩ := (TL4.Mdl117.mem_memBar_iff α' h' b' _).1 (T.R'_mem r' hr')
  refine ⟨m, hm, m', hm2, ?_⟩
  rw [A.mul r (Λ.R_le hr) r' (Λ.R'_le hr'), map_mul, hm', hm2']

theorem P_surj {m m' : Wr 5} (hm : m ∈ memL (α, b)) (hm' : m' ∈ memL (α', b')) :
    ∃ y ∈ R ⊔ R', A.ε y = mkQ 5 (m * m') := by
  obtain ⟨r, hr, hre⟩ := T.R_surj (mkQ 5 m) ((TL4.Mdl117.mem_memBar_iff α h b _).2 ⟨m, hm, rfl⟩)
  obtain ⟨r', hr', hre'⟩ := T.R'_surj (mkQ 5 m') ((TL4.Mdl117.mem_memBar_iff α' h' b' _).2 ⟨m', hm', rfl⟩)
  exact ⟨r * r', Subgroup.mul_mem_sup hr hr', by rw [A.mul r (Λ.R_le hr) r' (Λ.R'_le hr'), hre, hre', map_mul]⟩

theorem inv18_iff {y : G} (hy : y ∈ R ⊔ R') :
    (y * y = 1 ∧ y ≠ 1 ∧ y ≠ z) ↔ IsI18 (α, b) (α', b') (A.ε y) := by
  have hε₁ : A.ε (y * y) = A.ε y * A.ε y := A.mul y (Λ.P_le hy) y (Λ.P_le hy)
  have hz : A.ε z = mkQ 5 (zW (α, b)) := T.eps_z Λ
  constructor
  · rintro ⟨h2, h1, hz'⟩
    obtain ⟨m₀, hm₀, m₀', hm₀', hmm₀⟩ := T.mem_P Λ hy
    refine ⟨⟨m₀, hm₀, m₀', hm₀', hmm₀.symm⟩, ?_, ?_, ?_⟩
    · intro he
      exact h1 (A.inj_P Λ hy he)
    · rw [← hε₁, h2, A.one]
    · intro he
      rw [← hz] at he
      exact hz' (A.inj_P2 Λ hy (Subgroup.mem_sup_left Λ.z_mem_R) he)
  · rintro ⟨-, h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · apply A.inj_P Λ ((R ⊔ R').mul_mem hy hy)
      rw [hε₁]
      exact h2
    · intro he
      apply h1
      rw [he, A.one]
    · intro he
      apply h3
      rw [he, hz]

theorem exists_inv18 {x : AEQ 5} (hx : IsI18 (α, b) (α', b') x) :
    ∃ y ∈ R ⊔ R', y * y = 1 ∧ y ≠ 1 ∧ y ≠ z ∧ A.ε y = x := by
  obtain ⟨m, hm, m', hm', hmm⟩ := hx.1
  obtain ⟨y, hy, hye⟩ := T.P_surj Λ hm hm'
  have hI : IsI18 (α, b) (α', b') (A.ε y) := by
    rw [hye, hmm]
    exact hx
  obtain ⟨h2, h1, hz⟩ := (T.inv18_iff Λ hy).2 hI
  exact ⟨y, hy, h2, h1, hz, by rw [hye, hmm]⟩

theorem norm_P {u : AEQ 5}
    (hconj : ∀ x ∈ memBar α h b ⊔ memBar α' h' b', u * x * u⁻¹ ∈ memBar α h b ⊔ memBar α' h' b') :
    ∀ y ∈ R ⊔ R', ∃ y' ∈ R ⊔ R', A.ε y' = u * A.ε y * u⁻¹ := by
  intro y hy
  obtain ⟨r, hr, r', hr', rfl⟩ := mem_sup_comm Λ.RR'_comm hy
  have hmem : A.ε (r * r') ∈ memBar α h b ⊔ memBar α' h' b' := by
    rw [A.mul r (Λ.R_le hr) r' (Λ.R'_le hr')]
    exact Subgroup.mul_mem_sup (T.R_mem r hr) (T.R'_mem r' hr')
  have h1 := hconj _ hmem
  obtain ⟨x₁, hx₁, x₂, hx₂, he⟩ := mem_sup_comm (T.comm Λ) h1
  obtain ⟨y₁, hy₁, rfl⟩ := T.R_surj x₁ hx₁
  obtain ⟨y₂, hy₂, rfl⟩ := T.R'_surj x₂ hx₂
  exact ⟨y₁ * y₂, Subgroup.mul_mem_sup hy₁ hy₂, by
    rw [A.mul y₁ (Λ.R_le hy₁) y₂ (Λ.R'_le hy₂), he]⟩

theorem lift_norm {u : AEQ 5} (hu : u ∈ TL4.aeModel 5) (hN : NormGen (α, b) (α', b') u)
    (hz : u * mkQ 5 (zW (α, b)) * u⁻¹ = mkQ 5 (zW (α, b))) :
    ∃ n ∈ layerX Ω c, A.ε n = u ∧ (∀ y ∈ R ⊔ R', n * y * n⁻¹ ∈ R ⊔ R') ∧ n * z * n⁻¹ = z := by
  obtain ⟨x₀, hx₀, hx₀u⟩ := A.surj u hu
  have hnorm := T.norm_P Λ (NormGen.mem_sup hN)
  have hxP : ∀ y ∈ R ⊔ R', ∃ y' ∈ R ⊔ R', ∃ n ∈ oddCoreIn (layerX Ω c), x₀ * y * x₀⁻¹ = y' * n := by
    intro y hy
    obtain ⟨y', hy', hye⟩ := hnorm y hy
    refine ⟨y', hy', y'⁻¹ * (x₀ * y * x₀⁻¹), ?_, by group⟩
    have hX : x₀ * y * x₀⁻¹ ∈ layerX Ω c :=
      (layerX Ω c).mul_mem ((layerX Ω c).mul_mem hx₀ (Λ.P_le hy)) ((layerX Ω c).inv_mem hx₀)
    have hy'X := Λ.P_le hy'
    have hm : y'⁻¹ * (x₀ * y * x₀⁻¹) ∈ layerX Ω c := (layerX Ω c).mul_mem ((layerX Ω c).inv_mem hy'X) hX
    rw [← A.ker _ hm, A.mul _ ((layerX Ω c).inv_mem hy'X) _ hX, A.inv hy'X, A.eps_conj hx₀ (Λ.P_le hy),
      hx₀u, hye]
    group
  obtain ⟨o, ho, hon⟩ := frattini_G (X := layerX Ω c) (N := oddCoreIn (layerX Ω c)) (P := R ⊔ R')
    (oddCoreIn_le _) Λ.P_le (fun x hx n hn => conj_mem_oddCoreIn hx hn) (odd_card_oddCoreIn _) Λ.P_two
    hx₀ hxP
  have hoX := oddCoreIn_le _ ho
  have hnX : o⁻¹ * x₀ ∈ layerX Ω c := (layerX Ω c).mul_mem ((layerX Ω c).inv_mem hoX) hx₀
  have hεn : A.ε (o⁻¹ * x₀) = u := by
    rw [A.mul _ ((layerX Ω c).inv_mem hoX) _ hx₀, A.inv hoX, (A.ker o hoX).2 ho, inv_one, one_mul, hx₀u]
  refine ⟨o⁻¹ * x₀, hnX, hεn, hon, ?_⟩
  have hzP : z ∈ R ⊔ R' := Subgroup.mem_sup_left Λ.z_mem_R
  apply A.inj_P2 Λ (hon z hzP) hzP
  rw [A.eps_conj hnX (Λ.P_le hzP), hεn, T.eps_z Λ, hz]

theorem lift_inv {m : G} (hm : m ∈ layerX Ω c)
    (hnorm : ∀ y ∈ R ⊔ R', ∃ y' ∈ R ⊔ R',
      A.ε y' = A.ε (m * z * m⁻¹) * A.ε y * (A.ε (m * z * m⁻¹))⁻¹) :
    ∃ m' ∈ layerX Ω c, A.ε (m' * z * m'⁻¹) = A.ε (m * z * m⁻¹) ∧
      ∀ y ∈ R ⊔ R', (m' * z * m'⁻¹) * y * (m' * z * m'⁻¹)⁻¹ ∈ R ⊔ R' := by
  have hzX : z ∈ layerX Ω c := Λ.P_le (Subgroup.mem_sup_left Λ.z_mem_R)
  have hτX : m * z * m⁻¹ ∈ layerX Ω c :=
    (layerX Ω c).mul_mem ((layerX Ω c).mul_mem hm hzX) ((layerX Ω c).inv_mem hm)
  have hτ2 : (m * z * m⁻¹) * (m * z * m⁻¹) = 1 := by
    calc (m * z * m⁻¹) * (m * z * m⁻¹) = m * (z * z) * m⁻¹ := by group
      _ = 1 := by rw [Λ.hz2]; group
  have hτP : ∀ y ∈ R ⊔ R', ∃ y' ∈ R ⊔ R', ∃ n ∈ oddCoreIn (layerX Ω c),
      (m * z * m⁻¹) * y * (m * z * m⁻¹)⁻¹ = y' * n := by
    intro y hy
    obtain ⟨y', hy', hye⟩ := hnorm y hy
    refine ⟨y', hy', y'⁻¹ * ((m * z * m⁻¹) * y * (m * z * m⁻¹)⁻¹), ?_, by group⟩
    have hX : (m * z * m⁻¹) * y * (m * z * m⁻¹)⁻¹ ∈ layerX Ω c :=
      (layerX Ω c).mul_mem ((layerX Ω c).mul_mem hτX (Λ.P_le hy)) ((layerX Ω c).inv_mem hτX)
    have hy'X := Λ.P_le hy'
    have hmm : y'⁻¹ * ((m * z * m⁻¹) * y * (m * z * m⁻¹)⁻¹) ∈ layerX Ω c :=
      (layerX Ω c).mul_mem ((layerX Ω c).inv_mem hy'X) hX
    rw [← A.ker _ hmm, A.mul _ ((layerX Ω c).inv_mem hy'X) _ hX, A.inv hy'X,
      A.eps_conj hτX (Λ.P_le hy), hye]
    group
  obtain ⟨ν, hν, hνn⟩ := involution_G (X := layerX Ω c) (N := oddCoreIn (layerX Ω c)) (P := R ⊔ R')
    (oddCoreIn_le _) Λ.P_le (fun x hx n hn => conj_mem_oddCoreIn hx hn) (odd_card_oddCoreIn _) Λ.P_two
    hτX hτ2 hτP
  have hνX := oddCoreIn_le _ hν
  have e : (ν * m) * z * (ν * m)⁻¹ = ν * (m * z * m⁻¹) * ν⁻¹ := by group
  refine ⟨ν * m, (layerX Ω c).mul_mem hνX hm, ?_, ?_⟩
  · rw [e, A.eps_conj hνX hτX, (A.ker ν hνX).2 hν, one_mul, inv_one, mul_one]
  · intro y hy
    rw [e]
    exact hνn y hy

end TwinLab

end Basic

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X
