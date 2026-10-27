module

public import CFSG.LargeExtraspecial.AS35VMain
public import CFSG.LargeExtraspecial.AS35JFiveNineTwo
public import CFSG.LargeExtraspecial.AS35QThDefs
public import CFSG.LargeExtraspecial.AS35QThXa
public import CFSG.LargeExtraspecial.AS35QThFpf
public import CFSG.LargeExtraspecial.AS35QThGU
public import CFSG.LargeExtraspecial.AS35QThCoordB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QTh

open Subgroup QuadraticMap CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

variable {G : Type} [Group G] [Finite G]

structure ThSetup (S : Setting G) where
  g : G
  hgD : g * S.z * g⁻¹ ∈ S.DSet
  hgM : g * S.z * g⁻¹ ∈ S.M
  hswap : g * (g * S.z * g⁻¹) * g⁻¹ = S.z
  hw : S.width = 3
  X : Subgroup S.O
  hXM : X ≤ S.Mbar
  hXn : ∀ m ∈ S.Mbar, ∀ x ∈ X, m * x * m⁻¹ ∈ X
  hX27 : Nat.card X = 27
  ζ : S.O
  hζX : ζ ∈ X
  hζ3 : ζ ^ 3 = 1
  hCt : ∀ x ∈ X, x * S.ρ ⟨_, hgM⟩ = S.ρ ⟨_, hgM⟩ * x → x ∈ zpowers ζ
  hζM : ∀ m ∈ S.Mbar, m * ζ = ζ * m
  l : (Fin 3 → K) → S.Qt
  hl : HermCoords S.q (ζ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap l

theorem finite_O (S : Setting G) : Finite S.O :=
  Finite.of_injective (fun s : S.O => ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt → S.Qt))
    (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))

theorem apply_mul {S : Setting G} (s s' : S.O) (v : S.Qt) :
    ((s * s' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s' : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := rfl

theorem apply_pow_three {S : Setting G} (s : S.O) (v : S.Qt) :
    ((s ^ 3 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = (s : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) := by
  rw [pow_succ, pow_succ, pow_one, apply_mul, apply_mul]

theorem q_apply {S : Setting G} (s : S.O) (v : S.Qt) :
    S.q ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = S.q v :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp s.2 v

theorem exists_setup (hP : S14.Asc512PbarStmt) (h58 : S14.Asc512FiveEightStmt)
    (h2 : S14.Asc512ThomasIndexTwoStmt) {S : Setting G} (hS : S.SixHyp)
    (hth : S.Asc512Thomas) : Nonempty (ThSetup S) := by
  classical
  have := finite_O S
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨hw, X, hXM, hXn, hX3, t, htD, htM, x, hx, hne⟩ := hth
  have hth : S.Asc512Thomas := ⟨hw, X, hXM, hXn, hX3, t, htD, htM, x, hx, hne⟩
  obtain ⟨h, hh⟩ := S.exists_conj_of_mem_DSet htD
  obtain ⟨g, hgz, hgt⟩ := S.exists_swap_J hS htD hh
  subst hgz
  have hPX : ∀ p ∈ S.PbarAsc g, ∀ x ∈ X, p * x * p⁻¹ ∈ X :=
    fun p hp x hx => hXn p (Subgroup.map_le_range _ _ hp) x hx
  obtain ⟨-, h27, hnab, hC⟩ := S.fiveEleven_one hP h58 hS htD htM hXM hX3 hPX ⟨x, hx, hne⟩
  have hZ := h2 G S hS hth X hXM hXn hX3
  set tb := S.ρ ⟨_, htM⟩ with htb
  have htbM : tb ∈ S.Mbar := ⟨_, rfl⟩
  have htt : tb * tb = 1 := by
    rw [htb, ← map_mul]
    have e : (⟨_, htM⟩ : S.M) * ⟨_, htM⟩ = 1 :=
      Subtype.ext (S.mul_self_of_isConj (S.isConj_of_mem_ESet htD.1))
    rw [e, map_one]
  obtain ⟨a, b, ζ, ha, hb, hζX, hζc, hζ1, hζ3, hab, ha3, hb3, hCt, hcen⟩ :=
    exists_heisenberg_basis h27 hnab htt (fun x hx => hXn _ htbM x hx) hC
      (fun c hc hcc => (hZ c hc hcc tb htbM).symm)
  have hζM : ∀ m ∈ S.Mbar, m * ζ = ζ * m := fun m hm => hZ ζ hζX hζc m hm
  have hdim : Module.finrank (ZMod 2) S.Qt = 6 := by rw [S.finrank_Qt_eq_two_mul_width, hw]
  have hfpf : ∀ v, (ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) +
      (ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v + v = 0 := by
    refine zeta_sq_add_of_card (X.map S.O.subtype) hdim ?_ ?_ ?_ ?_ ?_
    · rw [Subgroup.card_map_of_injective S.O.subtype_injective]
      exact h27
    · intro h1
      exact hζ1 (Subtype.ext h1)
    · have := congrArg Subtype.val hζ3
      simpa using this
    · rintro _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hζc y hy)
    · rintro _ ⟨c, hc, rfl⟩ hcc
      have hc' : ∀ y ∈ X, c * y = y * c := fun y hy => Subtype.ext (hcc _ ⟨y, hy, rfl⟩)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcen c hc hc')
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← hk]; simp⟩
  have hCH : CoordHyp S.q (a : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap
      (b : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap (ζ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap :=
    { qζ := fun v => q_apply ζ v
      qa := fun v => q_apply a v
      ζa := fun v => by
        have := congrArg (fun s : S.O => (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v) (hζc a ha)
        exact this
      ζb := fun v => by
        have := congrArg (fun s : S.O => (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v) (hζc b hb)
        exact this
      ab := fun v => congrArg (fun s : S.O => (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v) hab
      a3 := fun v => by
        have := congrArg (fun s : S.O => (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v) ha3
        simp only [apply_pow_three] at this
        exact this
      b3 := fun v => by
        have := congrArg (fun s : S.O => (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v) hb3
        simp only [apply_pow_three] at this
        exact this
      ζ2 := hfpf
      nd := fun v hv => S.q_nondegenerate.1 v fun w => by
        rw [QuadraticMap.polarBilin_apply_apply]
        exact hv w }
  have hcard : Nat.card S.Qt = 64 := by
    rw [S.card_Qt, hdim]
    norm_num
  obtain ⟨l, hadd, hbij, hom, hpol⟩ := hCH.exists_coords hcard
  exact ⟨{
    g := g
    hgD := htD
    hgM := htM
    hswap := hgt
    hw := hw
    X := X
    hXM := hXM
    hXn := hXn
    hX27 := h27
    ζ := ζ
    hζX := hζX
    hζ3 := hζ3
    hCt := hCt
    hζM := hζM
    l := l
    hl := ⟨hadd, hbij, hom, hpol⟩ }⟩

end CFSG.LargeExtraspecial.AS35QTh
