module

public import CFSG.CGT.PushingUpLit.BHS.SymNatMaxSwap
public import CFSG.CGT.PushingUpLit.BHS.SymNatOrbitsCount

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm

theorem isSimpleGroup_altOn {d : ℕ} {B : Finset (Fin d)} (h5 : 5 ≤ B.card) :
    IsSimpleGroup ↥(altOn B) := by
  classical
  have hA : IsSimpleGroup ↥(alternatingGroup ↥B) :=
    alternatingGroup.isSimpleGroup (by simpa using h5)
  exact (MulEquiv.isSimpleGroup_congr (Subgroup.equivMapOfInjective (alternatingGroup ↥B)
    (Perm.ofSubtype : Perm ↥B →* Perm (Fin d)) Perm.ofSubtype_injective)).1 hA

theorem le_of_index_three {H : Type*} [Group H] [Finite H] {Q : Subgroup H} [Q.Normal]
    (hQ : IsPGroup 2 Q) {N : Subgroup H} (hN : N.index = 3) : Q ≤ N := by
  classical
  have hcard : Nat.card (H ⧸ N) = 3 := hN
  have hmod := hQ.card_modEq_card_fixedPoints (H ⧸ N)
  rw [hcard] at hmod
  have hpos : 0 < Nat.card (MulAction.fixedPoints ↥Q (H ⧸ N)) := by
    rcases Nat.eq_zero_or_pos (Nat.card (MulAction.fixedPoints ↥Q (H ⧸ N))) with h | h
    · rw [h] at hmod
      exact absurd (Nat.ModEq.symm hmod) (by decide)
    · exact h
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_pos_iff.1 hpos).1
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  intro q hq
  have hq' : h * q⁻¹ * h⁻¹ ∈ Q := Subgroup.Normal.conj_mem inferInstance q⁻¹ (Q.inv_mem hq) h
  have h1 := hx ⟨h * q⁻¹ * h⁻¹, hq'⟩
  have h2 : (QuotientGroup.mk ((h * q⁻¹ * h⁻¹) * h) : H ⧸ N) = QuotientGroup.mk h := h1
  rw [QuotientGroup.eq] at h2
  have h3 : ((h * q⁻¹ * h⁻¹) * h)⁻¹ * h = q := by group
  rwa [h3] at h2

theorem no_index_three {d : ℕ} {H : Type*} [Group H] [Finite H] {Q : Subgroup H} [Q.Normal]
    (hQ : IsPGroup 2 Q) (ψ : H →* Perm (Fin d)) (hker : ψ.ker ≤ Q) {B : Finset (Fin d)}
    (hB : 5 ≤ B.card) (hd : B.card + 1 = d) (hrange : ψ.range ≤ setStab B)
    (halt : altOn B ≤ ψ.range) {N : Subgroup H} (hN : N.index = 3) : False := by
  classical
  have hQN : Q ≤ N := le_of_index_three hQ hN
  set F : Subgroup (Perm (Fin d)) := ψ.range with hF
  set ψ' : H →* ↥F := ψ.rangeRestrict with hψ'
  have hsurj : Function.Surjective ψ' := ψ.rangeRestrict_surjective
  have hkerψ' : ψ'.ker ≤ N := by
    rw [hψ', MonoidHom.ker_rangeRestrict]
    exact hker.trans hQN
  have hF1 : (N.map ψ').index = 3 := by
    rw [Subgroup.index_map_eq N hsurj hkerψ']
    exact hN
  set F₁ : Subgroup ↥F := N.map ψ' with hF₁
  set A : Subgroup ↥F := (altOn B).subgroupOf F with hA
  have hsimpleA : IsSimpleGroup ↥A :=
    (MulEquiv.isSimpleGroup_congr (Subgroup.subgroupOfEquivOfLe halt)).2 (isSimpleGroup_altOn hB)
  have hAF1 : A ≤ F₁ := by
    let ρ : ↥F →* Perm (↥F ⧸ F₁) := MulAction.toPermHom ↥F (↥F ⧸ F₁)
    let ρA : ↥A →* Perm (↥F ⧸ F₁) := ρ.comp A.subtype
    rcases hsimpleA.eq_bot_or_eq_top_of_normal ρA.ker with hbot | htop
    · exfalso
      have hinj : Function.Injective ρA := (MonoidHom.ker_eq_bot_iff ρA).1 hbot
      have h1 := Nat.card_le_card_of_injective ρA hinj
      have h2 : Nat.card (Perm (↥F ⧸ F₁)) = 6 := by
        rw [Nat.card_perm]
        have : Nat.card (↥F ⧸ F₁) = 3 := hF1
        rw [this]
        rfl
      have h3 : Nat.card ↥A = B.card.factorial / 2 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe halt).toEquiv]
        exact card_altOn (by omega)
      have h4 : Nat.factorial 5 ≤ B.card.factorial := Nat.factorial_le hB
      rw [h2, h3] at h1
      have h5 : Nat.factorial 5 = 120 := by decide
      omega
    · intro a ha
      have hker1 : ρ a = 1 := by
        have : (⟨a, ha⟩ : ↥A) ∈ ρA.ker := by rw [htop]; trivial
        exact this
      have : a ∈ F₁.normalCore := by
        rw [Subgroup.normalCore_eq_ker]
        exact hker1
      exact Subgroup.normalCore_le F₁ this
  have h3 : 3 ∣ A.index := by
    rw [← hF1]
    exact Subgroup.index_dvd_of_le hAF1
  have hA2 : A.index ≤ 2 := by
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, Bᶜ = {c₀} := Finset.card_eq_one.1 (by
      rw [Finset.card_compl, Fintype.card_fin]
      omega)
    have hle : (alternatingGroup (Fin d)).subgroupOf F ≤ A := by
      intro f hf
      have hfalt : (f : Perm (Fin d)) ∈ alternatingGroup (Fin d) := hf
      have hfst : (f : Perm (Fin d)) ∈ setStab B := hrange f.2
      show (f : Perm (Fin d)) ∈ altOn B
      rw [mem_altOn]
      refine ⟨fun x hx => ?_, Equiv.Perm.mem_alternatingGroup.1 hfalt⟩
      have hxc : x ∈ Bᶜ := Finset.mem_compl.2 hx
      have hfx : (f : Perm (Fin d)) x ∉ B := fun h => hx ((mem_setStab.1 hfst x).1 h)
      have hfc : (f : Perm (Fin d)) x ∈ Bᶜ := Finset.mem_compl.2 hfx
      rw [hc₀, Finset.mem_singleton] at hxc hfc
      rw [hfc, hxc]
    have hdvd : A.index ∣ ((alternatingGroup (Fin d)).subgroupOf F).index :=
      Subgroup.index_dvd_of_le hle
    have hdvd2 : ((alternatingGroup (Fin d)).subgroupOf F).index ∣
        (alternatingGroup (Fin d)).index := by
      have := Subgroup.relIndex_dvd_index_of_normal (H := alternatingGroup (Fin d)) F
      exact this
    have hnt : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 (by omega)
    have h2 : (alternatingGroup (Fin d)).index = 2 := alternatingGroup.index_eq_two
    rw [h2] at hdvd2
    exact Nat.le_of_dvd (by norm_num) (hdvd.trans hdvd2)
  have hpos : A.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  omega

end CFSG.CGT.PushingUpLit.SolK
