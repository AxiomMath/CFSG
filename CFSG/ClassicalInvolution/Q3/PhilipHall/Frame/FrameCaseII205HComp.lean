module

public import CFSG.ClassicalInvolution.Q3.Q3NMClass

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

section Generic

theorem center_eq_bot_of_nonabelian' {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hnab : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center Q := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem component_nontrivial {H : Type} [Group H] [Finite H] {L : Subgroup H}
    (hL : CFSG.IsComponent L) : Nontrivial L := by
  obtain ⟨⟨-, -, a, b, hab⟩, -⟩ := hL
  have hne : a ≠ b := fun h => hab (h ▸ rfl)
  have hnt : Nontrivial (L ⧸ Subgroup.center L) := ⟨⟨a, b, hne⟩⟩
  by_contra hnot
  rw [not_nontrivial_iff_subsingleton] at hnot
  have hsub : Subsingleton (L ⧸ Subgroup.center L) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) x
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) y
    rw [Subsingleton.elim u v]
  exact (not_nontrivial_iff_subsingleton.mpr hsub) hnt

theorem component_not_le_of_odd {H : Type} [Group H] [Finite H] {L K : Subgroup H}
    (hL : CFSG.IsComponent L) (hK : Odd (Nat.card K)) : ¬ L ≤ K := by
  intro hLK
  have hodd : Odd (Nat.card L) := Odd.of_dvd_nat hK (Subgroup.card_dvd_of_le hLK)
  have hsolv : Group.IsSolvable L := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  haveI := component_nontrivial hL
  haveI : Group.IsPerfect L := hL.1.1
  exact Group.IsPerfect.not_isSolvable L hsolv

theorem exists_mem_component_map_ne_one {H S : Type} [Group H] [Finite H] [Group S]
    (F : H →* S) {L : Subgroup H} (hL : CFSG.IsComponent L) (hK : Odd (Nat.card F.ker)) :
    ∃ x ∈ L, F x ≠ 1 := by
  by_contra h
  push Not at h
  exact component_not_le_of_odd hL hK fun x hx => MonoidHom.mem_ker.mpr (h x hx)

theorem isPerfect_map {H S : Type} [Group H] [Group S] (F : H →* S) {L : Subgroup H}
    [Group.IsPerfect L] [Finite L] : Group.IsPerfect (L.map F) := by
  let ψ : L →* L.map F :=
    (F.comp L.subtype).codRestrict (L.map F) (fun x => Subgroup.mem_map_of_mem F x.2)
  refine Q3NM.isPerfect_of_surjective ψ ?_
  intro y
  obtain ⟨x, hx, hxy⟩ := y.2
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem not_le_of_isPGroup {S : Type} [Group S] [Finite S] {E : Subgroup S}
    (hE : IsPGroup 2 E) {P : Subgroup S} [Group.IsPerfect P] (hPne : P ≠ ⊥) : ¬ P ≤ E := by
  intro hPE
  haveI : Finite E := inferInstance
  haveI : Group.IsNilpotent E := IsPGroup.isNilpotent hE
  have hsolvE : Group.IsSolvable E := inferInstance
  have hsub : Group.IsSolvable (P.subgroupOf E) := inferInstance
  have hPiso : Group.IsSolvable P :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hPE).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPE).surjective
  haveI : Nontrivial P := by
    by_contra hnot
    rw [not_nontrivial_iff_subsingleton] at hnot
    exact hPne (Subgroup.eq_bot_of_subsingleton P)
  exact Group.IsPerfect.not_isSolvable P hPiso

theorem le_of_perfect_of_solvable_quot {S : Type} [Group S] [Finite S] (N : Subgroup S)
    [N.Normal] [Group.IsSolvable (S ⧸ N)] {P : Subgroup S} (hP : Group.IsPerfect P) :
    P ≤ N := by
  by_contra hPN
  obtain ⟨x, hxP, hxN⟩ := Set.not_subset.mp hPN
  haveI := hP
  haveI : Group.IsPerfect (P.map (QuotientGroup.mk' N)) := isPerfect_map _
  haveI : Group.IsSolvable (P.map (QuotientGroup.mk' N)) := inferInstance
  have hx1 : QuotientGroup.mk' N x ≠ 1 := fun h => hxN ((QuotientGroup.eq_one_iff x).mp h)
  haveI : Nontrivial (P.map (QuotientGroup.mk' N)) :=
    nontrivial_of_ne ⟨QuotientGroup.mk' N x, Subgroup.mem_map_of_mem _ hxP⟩ 1
      (fun h => hx1 (congrArg Subtype.val h))
  exact Group.IsPerfect.not_isSolvable (P.map (QuotientGroup.mk' N)) inferInstance

theorem component_map_le {H S : Type} [Group H] [Finite H] [Group S] [Finite S] (F : H →* S)
    {L : Subgroup H} (hL : CFSG.IsComponent L) {N : Subgroup S} [N.Normal]
    [Group.IsSolvable (S ⧸ N)] : L.map F ≤ N := by
  haveI : Group.IsPerfect L := hL.1.1
  exact le_of_perfect_of_solvable_quot N (isPerfect_map F)

theorem component_map_ne_bot {H S : Type} [Group H] [Finite H] [Group S] (F : H →* S)
    {L : Subgroup H} (hL : CFSG.IsComponent L) (hK : Odd (Nat.card F.ker)) :
    L.map F ≠ ⊥ := by
  obtain ⟨x, hx, hFx⟩ := exists_mem_component_map_ne_one F hL hK
  intro h
  apply hFx
  have hmem : F x ∈ L.map F := Subgroup.mem_map_of_mem F hx
  rw [h] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem component_map_eq {H S : Type} [Group H] [Finite H] [Group S] [Finite S] (F : H →* S)
    (hF : Function.Surjective F) {L : Subgroup H} (hL : CFSG.IsComponent L)
    (hK : Odd (Nat.card F.ker)) {N : Subgroup S} [N.Normal] [IsSimpleGroup N]
    [Group.IsSolvable (S ⧸ N)] : L.map F = N := by
  have hle : L.map F ≤ N := component_map_le F hL
  have hsn : (L.map F).IsSubnormal := hL.2.map hF
  have hsub : ((L.map F).subgroupOf N).IsSubnormal := hsn.subgroupOf
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance hsub with h | h
  · exfalso
    have h2 := Subgroup.map_subgroupOf_eq_of_le hle
    rw [h, Subgroup.map_bot] at h2
    exact component_map_ne_bot F hL hK h2.symm
  · have h2 := Subgroup.map_subgroupOf_eq_of_le hle
    rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
    exact h2.symm

theorem autOddFree_of_surj_simple {L Q : Type} [Group L] [Finite L] [Group Q] [Finite Q]
    [IsSimpleGroup Q] (hLq : CFSG.IsQuasisimple L) (ψ : L →* Q)
    (hψ : Function.Surjective ψ) (hnab : ∃ a b : Q, a * b ≠ b * a)
    (hAO : Q3NM.AutOddFree Q) : Q3NM.AutOddFree L := by
  have hker_ne : ψ.ker ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := hnab
    obtain ⟨x, rfl⟩ := hψ a
    obtain ⟨y, rfl⟩ := hψ b
    have hx : x ∈ ψ.ker := htop ▸ Subgroup.mem_top x
    have hy : y ∈ ψ.ker := htop ▸ Subgroup.mem_top y
    exact hab (by rw [MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp hy])
  have hker_le : ψ.ker ≤ Subgroup.center L :=
    (CFSG.LocalCores.quasisimple_normal_subgroups hLq ψ.normal_ker).resolve_left hker_ne
  have hcen : Subgroup.center L ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzQ : ψ z ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨y, rfl⟩ := hψ q
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
    have hc : Subgroup.center Q = ⊥ := center_eq_bot_of_nonabelian' hnab
    rw [hc, Subgroup.mem_bot] at hzQ
    exact hzQ
  have hkereq : ψ.ker = Subgroup.center L := le_antisymm hker_le hcen
  let e : L ⧸ Subgroup.center L ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hkereq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  haveI : Group.IsPerfect L := hLq.1
  have hQ' : Q3NM.AutOddFree (L ⧸ Subgroup.center L) := Q3NM.AutOddFree.of_mulEquiv e.symm hAO
  exact Q3NM.autOddFree_of_centralQuotient hQ'

theorem component_eq_and_autOddFree {H S : Type} [Group H] [Finite H] [Group S] [Finite S]
    (F : H →* S) (hF : Function.Surjective F) (hK : Odd (Nat.card F.ker))
    {N : Subgroup S} [N.Normal] [IsSimpleGroup N] [Finite N] [Group.IsSolvable (S ⧸ N)]
    (hnab : ∃ a b : N, a * b ≠ b * a) (hAO : Q3NM.AutOddFree N) :
    (∀ L₁ L₂ : Subgroup H, CFSG.IsComponent L₁ → CFSG.IsComponent L₂ → L₁ = L₂) ∧
      ∀ L : Subgroup H, CFSG.IsComponent L → Q3NM.AutOddFree L := by
  refine ⟨fun L₁ L₂ h₁ h₂ => ?_, fun L hL => ?_⟩
  · rcases CFSG.LocalCores.distinct_components_commute h₁ h₂ with h | hc
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have e1 := component_map_eq F hF h₁ hK (N := N)
      have e2 := component_map_eq F hF h₂ hK (N := N)
      have ha : (a : S) ∈ L₁.map F := by rw [e1]; exact a.2
      have hb : (b : S) ∈ L₂.map F := by rw [e2]; exact b.2
      obtain ⟨x, hx, hxa⟩ := ha
      obtain ⟨y, hy, hyb⟩ := hb
      have hc' : ⁅x, y⁆ ∈ ⁅L₁, L₂⁆ := Subgroup.commutator_mem_commutator hx hy
      rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc'
      apply hab
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hxa, ← hyb, ← map_mul, ← map_mul, hc']
  · have hLN : L.map F = N := component_map_eq F hF hL hK (N := N)
    let ψ : L →* N := (F.comp L.subtype).codRestrict N (fun x => by
      rw [← hLN]; exact Subgroup.mem_map_of_mem F x.2)
    have hψ : Function.Surjective ψ := by
      intro n
      have hn : (n : S) ∈ L.map F := by rw [hLN]; exact n.2
      obtain ⟨x, hx, hxn⟩ := hn
      exact ⟨⟨x, hx⟩, Subtype.ext hxn⟩
    exact autOddFree_of_surj_simple hL.1 ψ hψ hnab hAO

theorem centralizes_of_preimage {H S : Type} [Group H] [Finite H] [Group S] [Finite S]
    (F : H →* S) (hF : Function.Surjective F) (hK : Odd (Nat.card F.ker))
    {E : Subgroup S} [E.Normal] (hE : IsPGroup 2 E) {L : Subgroup H}
    (hL : CFSG.IsComponent L) {h : H} (hh : F h ∈ E) {x : H} (hx : x ∈ L) :
    h * x = x * h := by
  haveI : E.Normal := inferInstance
  have hN : (E.comap F).Normal := inferInstance
  rcases CFSG.LocalCores.component_subnormal_subgroup hL hN.isSubnormal with hLN | hc
  · exfalso
    have hPE : L.map F ≤ E := Subgroup.map_le_iff_le_comap.mpr hLN
    haveI : Group.IsPerfect L := hL.1.1
    haveI : Group.IsPerfect (L.map F) := isPerfect_map F
    exact not_le_of_isPGroup hE (component_map_ne_bot F hL hK) hPE
  · have hxh : ⁅x, h⁆ ∈ ⁅L, E.comap F⁆ :=
      Subgroup.commutator_mem_commutator hx (Subgroup.mem_comap.mpr hh)
    rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hxh
    exact hxh.symm

theorem no_component_of_pgroup {H S : Type} [Group H] [Finite H] [Group S] [Finite S]
    (F : H →* S) (hK : Odd (Nat.card F.ker)) {W : Subgroup S} [W.Normal] (hW : IsPGroup 2 W)
    [Group.IsSolvable (S ⧸ W)] {L : Subgroup H} (hL : CFSG.IsComponent L) : False := by
  haveI : Group.IsPerfect L := hL.1.1
  haveI : Group.IsPerfect (L.map F) := isPerfect_map F
  exact not_le_of_isPGroup hW (component_map_ne_bot F hL hK) (component_map_le F hL)

end Generic

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
