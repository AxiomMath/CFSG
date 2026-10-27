module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapesAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTrans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128ClPerf

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84t_not_mem_of_char {B : Type} [Group B] (E : Subgroup B) [Group.IsPerfect ↥E]
    (ε : B →* (ZMod 3)ˣ) {u : B} (hu : ε u ≠ 1) : u ∉ E := by
  have hle : E ≤ ε.ker :=
    sec128_perfect_le_ker (fun a b : (ZMod 3)ˣ => mul_comm a b) E
      (Subgroup.commutator_eq_self (H := E)) ε
  intro huE
  exact hu (MonoidHom.mem_ker.mp (hle huE))

private lemma sec8t84t_aux_map_bot_false {G : Type} [Group G] {C : Subgroup G}
    {B : Type} [Group B] {ρ : ↥C →* B} (hρ : OddCentralCover ρ) {E : Subgroup B}
    {A : Subgroup G} (hNE : (A.subgroupOf C).map ρ ≤ E)
    (hbot : ((A.subgroupOf C).map ρ).subgroupOf E = ⊥)
    (hqs : CFSG.IsQuasisimple ↥(A.subgroupOf C)) : False := by
  have hmapbot : (A.subgroupOf C).map ρ = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxE : x ∈ E := hNE hx
    have hx' : (⟨x, hxE⟩ : ↥E) ∈ ((A.subgroupOf C).map ρ).subgroupOf E :=
      (Subgroup.mem_subgroupOf).mpr hx
    rw [hbot, Subgroup.mem_bot] at hx'
    exact congrArg Subtype.val hx'
  have hmap1 : ∀ x : ↥(A.subgroupOf C), ρ (x : ↥C) = 1 := by
    intro x
    have hx : ρ (x : ↥C) ∈ (A.subgroupOf C).map ρ := Subgroup.mem_map_of_mem ρ x.2
    rw [hmapbot] at hx
    exact Subgroup.mem_bot.mp hx
  have hcen : ∀ x : ↥(A.subgroupOf C), (x : ↥C) ∈ Subgroup.center ↥C :=
    fun x => hρ.ker_le_center (MonoidHom.mem_ker.mpr (hmap1 x))
  have hcomm : ∀ x y : ↥(A.subgroupOf C), x * y = y * x := by
    intro x y
    apply Subtype.ext
    show (x : ↥C) * (y : ↥C) = (y : ↥C) * (x : ↥C)
    exact (Subgroup.mem_center_iff.mp (hcen x) (y : ↥C)).symm
  obtain ⟨a, b, hab⟩ := hqs.2.2
  let q : ↥(A.subgroupOf C) →* ↥(A.subgroupOf C) ⧸ Subgroup.center ↥(A.subgroupOf C) :=
    QuotientGroup.mk' _
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  refine hab ?_
  calc q x * q y = q (x * y) := (map_mul q x y).symm
    _ = q (y * x) := by rw [hcomm x y]
    _ = q y * q x := map_mul q y x

theorem sec8t84t_cover_image_eq {G : Type} [Group G] {C : Subgroup G} {B : Type} [Group B]
    [Finite B] {ρ : ↥C →* B} (hρ : OddCentralCover ρ) (E : Subgroup B) [E.Normal]
    (hE : IsSimpleGroup ↥E) (h2 : IsPGroup 2 (B ⧸ E)) {A : Subgroup G}
    (hA : IsComponentIn A C) : (A.subgroupOf C).map ρ = E := by
  let A' : Subgroup ↥C := A.subgroupOf C
  have hqs : CFSG.IsQuasisimple ↥A' := hA.2.1
  have hsub : A'.IsSubnormal := hA.2.2
  haveI hperf : Group.IsPerfect ↥A' := hqs.1
  have hNperf : Group.IsPerfect ↥(A'.map ρ) := Group.IsPerfect.map (f := ρ)
  have hNE : A'.map ρ ≤ E := ff_perfect_le_of_quot_two E h2 (A'.map ρ) hNperf
  have hNsub : (A'.map ρ).IsSubnormal := hsub.map hρ.surjective
  have hNsubE : ((A'.map ρ).subgroupOf E).IsSubnormal := hNsub.subgroupOf
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hE hNsubE with hbot | htop
  · exact (sec8t84t_aux_map_bot_false hρ hNE hbot hqs).elim
  · exact le_antisymm hNE (Subgroup.subgroupOf_eq_top.mp htop)

theorem sec8t84t_outer_of_cover {G : Type} [Group G] {C : Subgroup G} {B : Type} [Group B]
    [Finite B] {ρ : ↥C →* B} (hρ : OddCentralCover ρ) (E : Subgroup B) [E.Normal]
    (hE : IsSimpleGroup ↥E) (h2 : IsPGroup 2 (B ⧸ E))
    (hcent : ∀ c : B, (∀ e ∈ E, c * e = e * c) → c = 1) {u : B} (hu : u * u = 1)
    (huE : u ∉ E) {A : Subgroup G} (hA : IsComponentIn A C) :
    ∃ v ∈ C, orderOf v = 2 ∧ ¬ InnerOn A v := by
  have hN : (A.subgroupOf C).map ρ = E := sec8t84t_cover_image_eq hρ E hE h2 hA
  obtain ⟨a, ha⟩ := hρ.surjective u
  have hpow := hρ.pow_card_ker (a := a) (by rw [ha]; exact hu)
  let a₀ : ↥C := a ^ Nat.card ρ.ker
  refine ⟨(a₀ : G), a₀.2, ?_, ?_⟩
  · have hvv : (a₀ : G) * (a₀ : G) = 1 := by
      have h := congrArg (fun z : ↥C => (z : G)) (show a₀ * a₀ = 1 from hpow.1)
      simpa using h
    have hv1 : (a₀ : G) ≠ 1 := by
      intro h
      have hsub : a₀ = 1 := Subtype.ext (by simpa using h)
      have hρ1 : ρ a₀ = 1 := by rw [hsub, map_one]
      have hu1 : u = 1 := by rw [← ha, ← hpow.2, hρ1]
      exact huE (by simpa [hu1] using E.one_mem)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hvv) hv1
  · intro hInner
    obtain ⟨l, hlA, c, hc, hvlc⟩ := ff_innerOn_decompose hInner
    have hlC : l ∈ C := hA.1 hlA
    have hvC : (a₀ : G) ∈ C := a₀.2
    have hcC : c ∈ C := by
      have hc_eq : l⁻¹ * (a₀ : G) = c := by rw [hvlc]; group
      rw [← hc_eq]
      exact C.mul_mem (C.inv_mem hlC) hvC
    let l' : ↥C := ⟨l, hlC⟩
    let c' : ↥C := ⟨c, hcC⟩
    have hl'A : l' ∈ A.subgroupOf C := (Subgroup.mem_subgroupOf).mpr hlA
    have ha₀ : a₀ = l' * c' := by
      apply Subtype.ext
      show (a₀ : G) = l * c
      exact hvlc
    have hxc : ∀ x : ↥C, x ∈ A.subgroupOf C → x * c' = c' * x := by
      intro x hx
      have hxA : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp hx
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hc (x : G) hxA
    have hρc_comm : ∀ e ∈ E, ρ c' * e = e * ρ c' := by
      intro e he
      have he' : e ∈ (A.subgroupOf C).map ρ := by rw [hN]; exact he
      obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp he'
      calc ρ c' * e = ρ c' * ρ x := by rw [← hxe]
        _ = ρ (c' * x) := (map_mul ρ c' x).symm
        _ = ρ (x * c') := by rw [← hxc x hx]
        _ = ρ x * ρ c' := map_mul ρ x c'
        _ = e * ρ c' := by rw [hxe]
    have hρc1 : ρ c' = 1 := hcent (ρ c') hρc_comm
    have hρlE : ρ l' ∈ E := by
      rw [← hN]
      exact Subgroup.mem_map_of_mem ρ hl'A
    have hu_eq : u = ρ l' := by
      calc u = ρ a := ha.symm
        _ = ρ a₀ := hpow.2.symm
        _ = ρ (l' * c') := by rw [ha₀]
        _ = ρ l' * ρ c' := map_mul ρ l' c'
        _ = ρ l' := by rw [hρc1, mul_one]
    exact huE (by simpa [hu_eq] using hρlE)

end CFSG.OddStandard.SmallF3.Omega
