module

public import CFSG.CGT.Timmesfeld75.Sec5Four

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

theorem isBenderGroup_of_oddClass {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) (hnab : ∃ a b : G, a * b ≠ b * a)
    {H : Subgroup G} (hH : H ≠ ⊤) {t₀ : G} (ht₀ : t₀ ≠ 1) (ht₀H : t₀ ∈ H)
    (hord : ∀ d : G, IsConj t₀ d → d * d = 1)
    (hcases : ∀ d e : G, IsConj t₀ d → IsConj t₀ e →
      orderOf (d * e) ∣ 2 ∨ Odd (orderOf (d * e)))
    (hcl : ∀ u : G, IsConj t₀ u → u ∈ H → ∀ v : G, IsConj t₀ v → Commute u v → v ∈ H) :
    CFSG.BenderSuzuki.IsBenderGroup G := by
  set E : Set G := {x | IsConj t₀ x} with hEdef
  have ht₀E : t₀ ∈ E := IsConj.refl t₀
  have hne1 : ∀ d ∈ E, d ≠ 1 := by
    intro d hd h1
    apply ht₀
    have hd' : IsConj t₀ 1 := h1 ▸ hd
    exact isConj_one_left.1 hd'
  have hordE : ∀ d ∈ E, orderOf d = 2 := fun d hd =>
    orderOf_eq_prime (by simpa [pow_two] using hord d hd) (hne1 d hd)
  have hconj : ∀ a ∈ E, ∀ c : G, c * a * c⁻¹ ∈ E := fun a ha c =>
    ha.trans (isConj_iff.2 ⟨c, rfl⟩)
  have hclos : Subgroup.closure E = ⊤ := by
    have hnc : Subgroup.normalClosure E = Subgroup.closure E := by
      refine le_antisymm (Subgroup.closure_mono fun x hx => ?_)
        (Subgroup.closure_le _ |>.2 Subgroup.subset_normalClosure)
      obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.1 hx
      obtain ⟨c, hc⟩ := isConj_iff.1 hax
      rw [← hc]
      exact hconj a ha c
    have hPn : (Subgroup.closure E).Normal := hnc ▸ Subgroup.normalClosure_normal
    have := hPn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.closure E) with h | h
    · exfalso
      have : t₀ ∈ Subgroup.closure E := Subgroup.subset_closure ht₀E
      rw [h, Subgroup.mem_bot] at this
      exact ht₀ this
    · exact h
  have hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥ := by
    intro N hN hsolv
    have := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      subst h
      have : Group.IsSolvable G :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.topEquiv.symm.toMonoidHom)
          (MulEquiv.injective _)
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (IsSimpleGroup.comm_iff_isSolvable.2 this a b)
  rcases hTO G E ⟨t₀, rfl⟩ hordE (fun d hd e he => hcases d e hd he) hclos hrad
    ⟨H, hH, ⟨t₀, ht₀E, ht₀H⟩, fun u hu huH v hv hc => hcl u hu huH v hv hc⟩ with
    hB | ⟨f, n, -, hn, ⟨e⟩⟩ | hAlm
  · exact hB
  · exfalso
    have hsW := e.symm.isSimpleGroup
    exact not_isSimpleGroup_wreath (by omega) hsW
  · exfalso
    obtain ⟨M, hMn, hMmin, -, -, -, h2, -, -⟩ := hAlm
    have := hMn
    have hM := (IsSimpleGroup.eq_bot_or_eq_top_of_normal M).resolve_left hMmin.2.1
    rw [hM, Subgroup.index_top] at h2
    omega

theorem false_of_oddClass {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) (hBW : BenderWCInput)
    (hnab : ∃ a b : G, a * b ≠ b * a) {T : Subgroup G} (hT : IsWC T) (hTbot : T ≠ ⊥) {x : G}
    (hne : conjSubgroup x T ≠ T) (hL : normIn T (conjSubgroup x T) ≠ ⊥)
    {H : Subgroup G} (hH : H ≠ ⊤) {t₀ : G} (ht₀ : t₀ ≠ 1) (ht₀H : t₀ ∈ H)
    (hord : ∀ d : G, IsConj t₀ d → d * d = 1)
    (hcases : ∀ d e : G, IsConj t₀ d → IsConj t₀ e →
      orderOf (d * e) ∣ 2 ∨ Odd (orderOf (d * e)))
    (hcl : ∀ u : G, IsConj t₀ u → u ∈ H → ∀ v : G, IsConj t₀ v → Commute u v → v ∈ H) :
    False :=
  hL (hBW G (isBenderGroup_of_oddClass hTO hnab hH ht₀ ht₀H hord hcases hcl) T hT hTbot x hne)

end CFSG.CGT.Timmesfeld75
