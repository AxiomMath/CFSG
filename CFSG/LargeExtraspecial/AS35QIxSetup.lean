module

public import CFSG.LargeExtraspecial.AS35QIxCoord
public import CFSG.LargeExtraspecial.AS35QThXb
public import CFSG.LargeExtraspecial.AS35TMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Subgroup QuadraticMap CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.RankThree.OrthogonalInvolutions
open CFSG.Blueprint.Fischer (K)

variable {G : Type} [Group G] [Finite G]

structure IxSetup (S : Setting G) where
  g : G
  hgD : g * S.z * g⁻¹ ∈ S.DSet
  hgM : g * S.z * g⁻¹ ∈ S.M
  hswap : g * (g * S.z * g⁻¹) * g⁻¹ = S.z
  hw : S.width = 3
  X : Subgroup S.O
  hXM : X ≤ S.Mbar
  hXn : ∀ m ∈ S.Mbar, ∀ x ∈ X, m * x * m⁻¹ ∈ X
  hX27 : Nat.card X = 27
  α : S.O
  β : S.O
  ζ : S.O
  hαX : α ∈ X
  hβX : β ∈ X
  hζX : ζ ∈ X
  hζc : ∀ x ∈ X, ζ * x = x * ζ
  hζ1 : ζ ≠ 1
  hζ3 : ζ ^ 3 = 1
  hαβ : α * β = ζ * (β * α)
  hα3 : α ^ 3 = 1
  hβ3 : β ^ 3 = 1
  htα : S.ρ ⟨_, hgM⟩ * α * (S.ρ ⟨_, hgM⟩)⁻¹ = α⁻¹
  htβ : S.ρ ⟨_, hgM⟩ * β * (S.ρ ⟨_, hgM⟩)⁻¹ = β⁻¹
  hCt : ∀ x ∈ X, x * S.ρ ⟨_, hgM⟩ = S.ρ ⟨_, hgM⟩ * x → x ∈ zpowers ζ
  hcen : ∀ c ∈ X, (∀ x ∈ X, c * x = x * c) → c ∈ zpowers ζ
  hζt : ζ * S.ρ ⟨_, hgM⟩ = S.ρ ⟨_, hgM⟩ * ζ
  hζ2 : ∀ v, (ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) +
    (ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v + v = 0
  l : (Fin 3 → K) → S.Qt
  hl : AS35QTh.HermCoords S.q (ζ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap l
  hlα : ∀ x, (α : S.Qt ≃ₗ[ZMod 2] S.Qt) (l x) = l ![x 0, ω * x 1, frob ω * x 2]
  hlβ : ∀ x, (β : S.Qt ≃ₗ[ZMod 2] S.Qt) (l x) = l ![x 2, x 0, x 1]

theorem mem_zpowers_of_central {H : Type*} [Group H] [Finite H] {X : Subgroup H}
    (hcard : Nat.card X = 27) (hnab : ∃ a ∈ X, ∃ b ∈ X, a * b ≠ b * a) {ζ₀ : H}
    (hζ₀X : ζ₀ ∈ X) (hζ₀1 : ζ₀ ≠ 1) (hζ₀3 : ζ₀ ^ 3 = 1) (hζ₀c : ∀ x ∈ X, ζ₀ * x = x * ζ₀)
    {c : H} (hcX : c ∈ X) (hc : ∀ x ∈ X, c * x = x * c) : c ∈ zpowers ζ₀ := by
  have hncX : ∃ a b : X, a * b ≠ b * a := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnab
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
  set Z : Subgroup H := (Subgroup.center X).map X.subtype with hZ
  have hZcard : Nat.card Z = 3 := by
    rw [hZ, Subgroup.card_map_of_injective X.subtype_injective]
    exact AS35QTh.card_center_eq_three hcard hncX
  have hmemZ : ∀ w : H, w ∈ X → (∀ x ∈ X, w * x = x * w) → w ∈ Z := by
    intro w hwX hw
    refine ⟨⟨w, hwX⟩, Subgroup.mem_center_iff.mpr fun x => ?_, rfl⟩
    exact Subtype.ext (hw x x.2).symm
  have hle : zpowers ζ₀ ≤ Z := (zpowers_le).mpr (hmemZ ζ₀ hζ₀X hζ₀c)
  have heq : zpowers ζ₀ = Z := Subgroup.eq_of_le_of_card_ge hle (by
    rw [hZcard, Nat.card_zpowers, AS35V.orderOf_eq_three_of_pow hζ₀3 hζ₀1])
  rw [heq]
  exact hmemZ c hcX hc

theorem rho_t_mul_self (S : Setting G) {g : G} (htD : g * S.z * g⁻¹ ∈ S.DSet)
    (htM : g * S.z * g⁻¹ ∈ S.M) : S.ρ ⟨_, htM⟩ * S.ρ ⟨_, htM⟩ = 1 := by
  rw [← map_mul]
  have e : (⟨_, htM⟩ : S.M) * ⟨_, htM⟩ = 1 :=
    Subtype.ext (S.mul_self_of_isConj (S.isConj_of_mem_ESet htD.1))
  rw [e, map_one]

theorem exists_ixSetup {S : Setting G} (hS : S.SixHyp) (hth : S.Asc512Thomas) :
    Nonempty (IxSetup S) := by
  classical
  have := AS35QTh.finite_O S
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨hw, X, hXM, hXn, hX3, t, htD, htM, x, hx, hne⟩ := hth
  obtain ⟨h, hh⟩ := S.exists_conj_of_mem_DSet htD
  obtain ⟨g, hgz, hgt⟩ := S.exists_swap_J hS htD hh
  subst hgz
  have hPX : ∀ p ∈ S.PbarAsc g, ∀ x ∈ X, p * x * p⁻¹ ∈ X :=
    fun p hp x hx => hXn p (Subgroup.map_le_range _ _ hp) x hx
  obtain ⟨-, h27, hnab, hC⟩ := S.fiveEleven_one S14.asc512PbarStmt S14.asc512FiveEightStmt hS
    htD htM hXM hX3 hPX ⟨x, hx, hne⟩
  set tb := S.ρ ⟨_, htM⟩ with htb
  have htbM : tb ∈ S.Mbar := ⟨_, rfl⟩
  have htt : tb * tb = 1 := rho_t_mul_self S htD htM
  have hPf := AS35V.pbarFacts_of_asc512 S14.asc512PbarStmt hS htD htM
  obtain ⟨ζ₀, hζ₀X, hζ₀1, hζ₀3, hζ₀t, -, hζ₀c⟩ :=
    hPf.exists_zeta (S14.asc512FiveEightStmt G S hS g htD htM) hXM hX3 hPX ⟨x, hx, hne⟩
  have hZt : ∀ c ∈ X, (∀ x ∈ X, c * x = x * c) → c * tb = tb * c := by
    intro c hcX hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp
      (mem_zpowers_of_central h27 hnab hζ₀X hζ₀1 hζ₀3 hζ₀c hcX hc)
    exact (Commute.zpow_left hζ₀t k).eq
  obtain ⟨a, b, ζ, ha, hb, hζX, hζc, hζ1, hζ3, hab, ha3, hb3, hta, htb', hCt, hcen⟩ :=
    exists_heisenberg_basis_inv h27 hnab htt (fun x hx => hXn _ htbM x hx) hC hZt
  have hdim : Module.finrank (ZMod 2) S.Qt = 6 := by rw [S.finrank_Qt_eq_two_mul_width, hw]
  have hfpf : ∀ v, (ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) +
      (ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v + v = 0 := by
    refine AS35QTh.zeta_sq_add_of_card (X.map S.O.subtype) hdim ?_ ?_ ?_ ?_ ?_
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
  have hCH : AS35QTh.CoordHyp S.q (a : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap
      (b : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap (ζ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap :=
    { qζ := fun v => AS35QTh.q_apply ζ v
      qa := fun v => AS35QTh.q_apply a v
      ζa := fun v => by
        have := congrArg (fun s : S.O => (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v) (hζc a ha)
        exact this
      ζb := fun v => by
        have := congrArg (fun s : S.O => (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v) (hζc b hb)
        exact this
      ab := fun v => congrArg (fun s : S.O => (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v) hab
      a3 := fun v => by
        have := congrArg (fun s : S.O => (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v) ha3
        simp only [AS35QTh.apply_pow_three] at this
        exact this
      b3 := fun v => by
        have := congrArg (fun s : S.O => (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v) hb3
        simp only [AS35QTh.apply_pow_three] at this
        exact this
      ζ2 := hfpf
      nd := fun v hv => S.q_nondegenerate.1 v fun w => by
        rw [QuadraticMap.polarBilin_apply_apply]
        exact hv w }
  have hcard : Nat.card S.Qt = 64 := by
    rw [S.card_Qt, hdim]
    norm_num
  obtain ⟨l, hadd, hbij, hom, hpol, hla, hlb⟩ := exists_coords_mono hCH hcard
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
    α := a
    β := b
    ζ := ζ
    hαX := ha
    hβX := hb
    hζX := hζX
    hζc := hζc
    hζ1 := hζ1
    hζ3 := hζ3
    hαβ := hab
    hα3 := ha3
    hβ3 := hb3
    htα := hta
    htβ := htb'
    hCt := hCt
    hcen := hcen
    hζt := hZt ζ hζX hζc
    hζ2 := hfpf
    l := l
    hl := ⟨hadd, hbij, hom, hpol⟩
    hlα := hla
    hlβ := hlb }⟩

end CFSG.LargeExtraspecial.AS35QIx
