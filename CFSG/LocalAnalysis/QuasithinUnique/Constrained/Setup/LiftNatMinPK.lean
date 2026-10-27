module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNatData

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

section Group

variable {Γ : Type} [Group Γ]

theorem pow_mul_eq_mem_mul_pow {L : Subgroup Γ} {l d : Γ} (hl : l ∈ L)
    (hd : d ∈ Subgroup.normalizer (L : Set Γ)) (n : ℕ) :
    ∃ l' ∈ L, (l * d) ^ n = l' * d ^ n := by
  induction n with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨l', hl', h⟩ := ih
    have hdn : d ^ n ∈ Subgroup.normalizer (L : Set Γ) := Subgroup.pow_mem _ hd n
    have h1 : d ^ n * l * (d ^ n)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hdn l).1 hl
    refine ⟨l' * (d ^ n * l * (d ^ n)⁻¹), L.mul_mem hl' h1, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem oddOrderSubgroup_sup_eq [Finite Γ] {L D : Subgroup Γ} (hperf : Group.IsPerfect ↥L)
    (hD : IsPGroup 2 D) (hDn : D ≤ Subgroup.normalizer (L : Set Γ)) :
    oddOrderSubgroup (L ⊔ D) = L := by
  apply le_antisymm
  · refine oddOrderSubgroup_le_of_pow_mem fun h hh => ?_
    have hh' : h ∈ ((L ⊔ D : Subgroup Γ) : Set Γ) := hh
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L D hDn] at hh'
    obtain ⟨l, hl, d, hdD, rfl⟩ := hh'
    obtain ⟨k, hk⟩ := hD ⟨d, hdD⟩
    have hk' : d ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    obtain ⟨l', hl', h1⟩ := pow_mul_eq_mem_mul_pow hl (hDn hdD) (2 ^ k)
    refine ⟨k, ?_⟩
    rw [h1, hk', mul_one]
    exact hl'
  · calc L = oddOrderSubgroup L := (oddOrderSubgroup_eq_of_perfect hperf).symm
      _ ≤ oddOrderSubgroup (L ⊔ D) := oddOrderSubgroup_mono le_sup_left

end Group

section Rho

variable {G : Type} [Group G]

theorem inf_centralizer_eq_of_autOn_eq {V X X' : Subgroup G} [V.Normal]
    (h : autOn X V = autOn X' V) :
    V ⊓ Subgroup.centralizer (X : Set G) = V ⊓ Subgroup.centralizer (X' : Set G) := by
  have key : ∀ {Y Y' : Subgroup G}, autOn Y' V ≤ autOn Y V →
      V ⊓ Subgroup.centralizer (Y : Set G) ≤ V ⊓ Subgroup.centralizer (Y' : Set G) := by
    intro Y Y' hle v hv
    refine ⟨hv.1, Subgroup.mem_centralizer_iff.2 fun x' hx' => ?_⟩
    have hρ : MulAut.conjNormal (H := V) x' ∈ autOn Y V := by
      apply hle
      rw [autOn_eq_map_conjNormal]
      exact Subgroup.mem_map_of_mem _ hx'
    rw [autOn_eq_map_conjNormal] at hρ
    obtain ⟨x, hx, hxx'⟩ := hρ
    have h1 : x * v = v * x := Subgroup.mem_centralizer_iff.1 hv.2 x hx
    have h2 := congrArg (fun ξ : MulAut V => ((ξ ⟨v, hv.1⟩ : V) : G)) hxx'
    simp only [MulAut.conjNormal_apply] at h2
    have h3 : x * v * x⁻¹ = v := by rw [h1, mul_inv_cancel_right]
    rw [h3] at h2
    calc x' * v = (x' * v * x'⁻¹) * x' := by group
      _ = v * x' := by rw [← h2]
  exact le_antisymm (key h.ge) (key h.le)

end Rho

section Main

variable {G : Type} [Group G] [Finite G]

theorem natMinPKProp
    : NatMinPKProp := by
  intro G _ _ R M V n F _ r Lc ctx i P hbase hY hmin hbasic hI
  have hS := ctx.setting
  have hX := ctx.hX
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have hnormV : ∀ A : Subgroup G, A ≤ Subgroup.normalizer (V : Set G) := fun A x _ => hX
      (Subgroup.mem_top x)
  have hdata := nat_family_data hS ctx.comps ctx.natural
  have hfin : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) DFunLike.coe_injective
  have hperf : Group.IsPerfect ↥(Lc i) := ⟨(ctx.comps.isComp i).2.2.1⟩
  have hDp : IsPGroup 2 (autOn (baum R) V) := by
    rw [autOn_eq_map_conjNormal V]
    exact (hS.sylow.2.1.to_le (inf_le_left : baum R ≤ R)).map _
  have himage : autOn (oddOrderSubgroup P) V = Lc i := by
    rw [autOn_oddOrderSubgroup (hnormV P), hI.image]
    exact oddOrderSubgroup_sup_eq hperf hDp (hdata.normS i)
  have hDle : Lc i ≤ autOn (⊤ : Subgroup G) V := (ctx.comps.isComp i).1
  refine ⟨himage, ?_⟩
  have hfull : autOn (oddOrderSubgroup P) V = autOn (rhoPreimage V ⊤ hX (Lc i)) V := by
    rw [himage, autOn_rhoPreimage_of_le hX hDle]
  have hIV : modComm V (Lc i) ≤ V := modComm_le V (Lc i)
  have h1 := inf_centralizer_eq_of_autOn_eq hfull
  calc modComm V (Lc i) ⊓ Subgroup.centralizer (oddOrderSubgroup P : Set G)
      = modComm V (Lc i) ⊓ (V ⊓ Subgroup.centralizer (oddOrderSubgroup P : Set G)) := by
        rw [← inf_assoc, inf_eq_left.2 hIV]
    _ = modComm V (Lc i) ⊓ (V ⊓ Subgroup.centralizer
          (rhoPreimage V ⊤ hX (Lc i) : Set G)) := by rw [h1]
    _ = modComm V (Lc i) ⊓ Subgroup.centralizer (rhoPreimage V ⊤ hX (Lc i) : Set G) := by
        rw [← inf_assoc, inf_eq_left.2 hIV]

end Main

end CFSG.QuasithinUnique.Setup.Lift
