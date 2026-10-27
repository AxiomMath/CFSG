module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporWit

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.RuPairs

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

section Canonical

variable {Γ : Type*} [Group Γ]

theorem map_conj_eq_of_mem {K : Subgroup Γ} {g : Γ} (hg : g ∈ K) :
    K.map (MulAut.conj g).toMonoidHom = K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact K.mul_mem (K.mul_mem hg hy) (K.inv_mem hg)
  · intro hx
    refine ⟨g⁻¹ * x * g, K.mul_mem (K.mul_mem (K.inv_mem hg) hx) hg, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group

theorem invariant_of_selfNormalizing {S K : Subgroup Γ} (hSK : S ≤ K)
    (hinner : ∀ α : MulAut Γ, ∃ g : Γ, α = MulAut.conj g)
    (hself : ∀ g : Γ, S.map (MulAut.conj g).toMonoidHom = S → g ∈ S) :
    ∀ α : MulAut Γ, S.map α.toMonoidHom = S → K.map α.toMonoidHom = K := by
  intro α hα
  obtain ⟨g, rfl⟩ := hinner α
  exact map_conj_eq_of_mem (hSK (hself g hα))

theorem mem_of_map_conj_eq {S : Subgroup Γ} {g : Γ} (h : S.map (MulAut.conj g).toMonoidHom = S) :
    (∀ s ∈ S, g * s * g⁻¹ ∈ S) ∧ (∀ s ∈ S, g⁻¹ * s * g ∈ S) := by
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · have hmem : (MulAut.conj g).toMonoidHom s ∈ S.map (MulAut.conj g).toMonoidHom :=
      ⟨s, hs, rfl⟩
    rw [h] at hmem
    exact hmem
  · rw [← h] at hs
    obtain ⟨y, hy, rfl⟩ := hs
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    show g⁻¹ * (g * y * g⁻¹) * g ∈ S
    rw [e]
    exact hy

end Canonical

section Good

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem goodLocal_subgroupOf {P Y Q : Subgroup Γ} (hYP : Y ≤ P) (hQY : Q ≤ Y)
    (hQn : (Q.subgroupOf Y).Normal) (hQ2 : IsPGroup 2 Q) {a p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hcard : Nat.card Y = 2 ^ a * 3 * p) {b c u w : Γ} (hbY : b ∈ Y) (hb : orderOf b = 3)
    (hcY : c ∈ Y) (hc : orderOf c = p) (hu : u ∈ Q) (hw : w ∈ Q)
    (h3 : ⁅u, b⁆ * ⁅u, b⁆ ≠ 1) (hnc : w * c ≠ c * w) : GoodLocal (Y.subgroupOf P) := by
  have hQP : Q ≤ P := hQY.trans hYP
  set Y' : Subgroup ↥P := Y.subgroupOf P with hY'
  set Q' : Subgroup ↥P := Q.subgroupOf P with hQ'
  have hQ'Y' : Q' ≤ Y' := Subgroup.subgroupOf_mono P hQY
  have hnorm : (Q'.subgroupOf Y').Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQ'Y']
    intro h k hh hk
    exact (Subgroup.normal_subgroupOf_iff hQY).1 hQn (h : Γ) (k : Γ) hh hk
  have hN2 : IsPGroup 2 (Q'.subgroupOf Y') := by
    intro g
    obtain ⟨k, hk⟩ := hQ2 ⟨(((g : ↥Y') : ↥P) : Γ), g.2⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg (fun z : ↥Q => (z : Γ)) hk
    simpa using this
  have hQ'le : Q' ≤ pCoreOf 2 Y' := by
    intro x hx
    have hxY' : x ∈ Y' := hQ'Y' hx
    refine ⟨⟨x, hxY'⟩, ?_, rfl⟩
    exact le_pCore_of_normal hN2 hx
  have hcard' : Nat.card ↥Y' = 2 ^ a * 3 * p := by
    rw [hY', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYP).toEquiv]
    exact hcard
  refine goodLocal_of_witnesses Y' hp h5 hcard' ?_ ?_
  · refine ⟨⟨b, hYP hbY⟩, hbY, ?_, ⁅(⟨u, hQP hu⟩ : ↥P), (⟨b, hYP hbY⟩ : ↥P)⁆,
      Subgroup.commutator_mem_commutator (hQ'le hu) (Subgroup.mem_zpowers _),
      ⁅(⟨u, hQP hu⟩ : ↥P), (⟨b, hYP hbY⟩ : ↥P)⁆,
      Subgroup.commutator_mem_commutator (hQ'le hu) (Subgroup.mem_zpowers _), Or.inr ?_⟩
    · rw [← hb]
      exact Subgroup.orderOf_mk _ _
    · intro h
      apply h3
      have := congrArg Subtype.val h
      simpa [commutatorElement_def] using this
  · refine ⟨⟨c, hYP hcY⟩, hcY, ?_, ⟨w, hQP hw⟩, hQ'le hw, fun h => hnc (congrArg Subtype.val h)⟩
    rw [← hc]
    exact Subgroup.orderOf_mk _ _

end Good

end CFSG.QuasithinUnique.Vol2Native.L239.RuPairs
