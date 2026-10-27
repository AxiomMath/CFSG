module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chains
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Standard

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Relation CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H]

@[expose] noncomputable def cqOrd (X : Subgroup H) : ℕ := Nat.card (↥X ⧸ center ↥X)

theorem cqOrd_le_card_range {A B : Subgroup H} (h : A ≤ B) :
    cqOrd A ≤ Nat.card ((QuotientGroup.mk' (center ↥B)).comp (Subgroup.inclusion h)).range := by
  set φ : ↥A →* ↥B ⧸ center ↥B := (QuotientGroup.mk' (center ↥B)).comp (Subgroup.inclusion h)
    with hφ
  have hker : φ.ker ≤ center ↥A := by
    intro x hx
    have hxc : (Subgroup.inclusion h x : ↥B) ∈ center ↥B := by
      simpa [φ, QuotientGroup.eq_one_iff] using hx
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_center_iff.1 hxc (Subgroup.inclusion h g)
    exact Subtype.ext (by simpa using congrArg (fun z : ↥B => (z : H)) this)
  let ψ : ↥A ⧸ φ.ker →* ↥A ⧸ center ↥A := QuotientGroup.map φ.ker (center ↥A) (MonoidHom.id _) hker
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk a, rfl⟩
  have h1 : Nat.card (↥A ⧸ center ↥A) ≤ Nat.card (↥A ⧸ φ.ker) := Nat.card_le_card_of_surjective ψ hψ
  have h2 : Nat.card (↥A ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  exact h2 ▸ h1

theorem cqOrd_le_of_le {A B : Subgroup H} (h : A ≤ B) : cqOrd A ≤ cqOrd B :=
  (cqOrd_le_card_range h).trans (Subgroup.card_le_card_group _)

theorem eq_of_le_of_cqOrd_eq {L L' : Subgroup H} (hle : L ≤ L') (hLq : CFSG.IsQuasisimple ↥L)
    (hL'q : CFSG.IsQuasisimple ↥L') (hcard : cqOrd L = cqOrd L') : L = L' := by
  let φ : ↥L →* ↥L' ⧸ center ↥L' :=
    (QuotientGroup.mk' (center ↥L')).comp (Subgroup.inclusion hle)
  have hker : φ.ker ≤ center ↥L := by
    intro x hx
    have hxc : (Subgroup.inclusion hle x : ↥L') ∈ center ↥L' := by
      simpa [φ, QuotientGroup.eq_one_iff] using hx
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_center_iff.1 hxc (Subgroup.inclusion hle g)
    exact Subtype.ext (by simpa using congrArg (fun z : ↥L' => (z : H)) this)
  have hkerle : Nat.card φ.ker ≤ Nat.card (center ↥L) := Subgroup.card_le_of_le hker
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card ↥L := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card (↥L ⧸ center ↥L) * Nat.card (center ↥L) = Nat.card ↥L :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L)).symm
  have h3 : Nat.card (↥L ⧸ center ↥L) = Nat.card (↥L' ⧸ center ↥L') := hcard
  have hpos : 0 < Nat.card (center ↥L) := Nat.card_pos
  have hrange : Nat.card (↥L' ⧸ center ↥L') ≤ Nat.card φ.range := by
    by_contra hlt
    push Not at hlt
    have : Nat.card φ.ker * Nat.card φ.range < Nat.card (center ↥L) *
        Nat.card (↥L ⧸ center ↥L) := by
      calc Nat.card φ.ker * Nat.card φ.range ≤ Nat.card (center ↥L) * Nat.card φ.range :=
            Nat.mul_le_mul_right _ hkerle
        _ < Nat.card (center ↥L) * Nat.card (↥L ⧸ center ↥L) :=
            Nat.mul_lt_mul_of_pos_left (h3 ▸ hlt) hpos
    have h2' : Nat.card (center ↥L) * Nat.card (↥L ⧸ center ↥L) = Nat.card ↥L := by
      rw [mul_comm]
      exact h2
    omega
  have hrt : φ.range = ⊤ := Subgroup.eq_top_of_le_card _ hrange
  have hx : ∀ x : ↥L', ∃ a : ↥L, ∃ z ∈ center ↥L', x = Subgroup.inclusion hle a * z := by
    intro x
    have hmem : QuotientGroup.mk x ∈ φ.range := hrt ▸ Subgroup.mem_top _
    obtain ⟨a, ha⟩ := hmem
    refine ⟨a, (Subgroup.inclusion hle a)⁻¹ * x, QuotientGroup.eq.1 ha, by group⟩
  have hAn : (L.subgroupOf L').Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨a, z, hz, rfl⟩ := hx g
    have hzn : z * n * z⁻¹ = n := by
      calc z * n * z⁻¹ = (n * z) * z⁻¹ := by rw [(Subgroup.mem_center_iff.1 hz n).symm]
        _ = n := by group
    have ha' : Subgroup.inclusion hle a ∈ L.subgroupOf L' := a.2
    have hconj : Subgroup.inclusion hle a * z * n * (Subgroup.inclusion hle a * z)⁻¹ =
        Subgroup.inclusion hle a * n * (Subgroup.inclusion hle a)⁻¹ := by
      calc Subgroup.inclusion hle a * z * n * (Subgroup.inclusion hle a * z)⁻¹
          = Subgroup.inclusion hle a * (z * n * z⁻¹) * (Subgroup.inclusion hle a)⁻¹ := by group
        _ = _ := by rw [hzn]
    rw [hconj]
    exact (L.subgroupOf L').mul_mem ((L.subgroupOf L').mul_mem ha' hn)
      ((L.subgroupOf L').inv_mem ha')
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hL'q hAn with htop | hcent
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.1 htop)
  · exfalso
    refine not_forall_commute_of_isQuasisimple hLq fun a ha b hb => ?_
    have h1 : (⟨a, hle ha⟩ : ↥L') ∈ L.subgroupOf L' := ha
    have := Subgroup.mem_center_iff.1 (hcent h1) ⟨b, hle hb⟩
    exact congrArg Subtype.val this.symm

omit [Finite H] in
theorem le_of_link5b {Li Lp : Subgroup H} {s : H} (h : Sol78Link5b Li Lp s)
    (hincl : Lp ≤ Li ⊔ Li.map (MulAut.conj s).toMonoidHom) : Lp ≤ Li := by
  have h1 := h.1
  rw [← h1, sup_idem] at hincl
  exact hincl

theorem link_cqOrd_le {Li Lp : Subgroup H} {s : H}
    (hincl : Lp ≤ Li ⊔ Li.map (MulAut.conj s).toMonoidHom)
    (h : Sol78Link5a Li Lp s ∨ Sol78Link5b Li Lp s) : cqOrd Lp ≤ cqOrd Li := by
  rcases h with h5a | h5b
  · obtain ⟨e⟩ := h5a.2
    exact (Nat.card_congr e.toEquiv).symm.le
  · exact cqOrd_le_of_le (le_of_link5b h5b hincl)

theorem link5a_of_cqOrd_eq {Li Lp : Subgroup H} {s : H} (hLpq : CFSG.IsQuasisimple ↥Lp)
    (hLiq : CFSG.IsQuasisimple ↥Li) (hincl : Lp ≤ Li ⊔ Li.map (MulAut.conj s).toMonoidHom)
    (h : Sol78Link5a Li Lp s ∨ Sol78Link5b Li Lp s) (heq : cqOrd Lp = cqOrd Li) (hne : Lp ≠ Li) :
    Sol78Link5a Li Lp s := by
  rcases h with h5a | h5b
  · exact h5a
  · exact absurd (eq_of_le_of_cqOrd_eq (le_of_link5b h5b hincl) hLpq hLiq heq) hne

end CFSG.EvenSporadicStandard.Induction
