module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Amb

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

section Hyp

variable {G : Type} [Group G] [Finite G]

theorem mem_centModSubgroup_of_subgroupOf {p : ℕ} {H L : Subgroup G} (hLH : L ≤ H)
    (hHN : H ≤ Subgroup.normalizer (L : Set G)) {g : ↥H}
    (hg : g ∈ centModSubgroup p (L.subgroupOf H)) : (g : G) ∈ centModSubgroup p L := by
  refine ⟨hHN g.2, fun l hl => ?_⟩
  have hl' : (⟨l, hLH hl⟩ : ↥H) ∈ L.subgroupOf H := hl
  have := hg.2 _ hl'
  rw [← map_subtype_glaPPrimeCoreOf_subgroupOf p hLH]
  exact ⟨_, this, rfl⟩

theorem cycModSylow_quot {p : ℕ} (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H)
    (hHN : H ≤ Subgroup.normalizer (L : Set G)) (N₀ : Subgroup ↥H) [N₀.Normal]
    (hN₀ : N₀ = GLAPPrimeCoreOf p (L.subgroupOf H)) (hcyc : CycModSylow p L) :
    CycModSylow p ((L.subgroupOf H).map (QuotientGroup.mk' N₀)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hker : ¬ p ∣ Nat.card (QuotientGroup.mk' N₀).ker := by
    rw [QuotientGroup.ker_mk', hN₀]; exact not_dvd_card_glaPPrimeCoreOf hp _
  intro E hE hEp
  obtain ⟨Et, hEtp, hEtmap, -⟩ := CFSG.HardMathSupport.Solomon.Coordinator.i1020_frattini_lift
    (QuotientGroup.mk' N₀) (QuotientGroup.mk'_surjective N₀) hEp
  have hcyc' : IsCyclic ((Et.map H.subtype : Subgroup G)) := by
    refine hcyc _ (fun g hg => ?_) (hEtp.map _)
    obtain ⟨g₀, hg₀, rfl⟩ := hg
    have hgE : QuotientGroup.mk' N₀ g₀ ∈ E := by rw [← hEtmap]; exact ⟨g₀, hg₀, rfl⟩
    have hK₀n : (L.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 hHN
    have h1 := hE _ hgE
    rw [centMod_iff] at h1 ⊢
    have h2 : g₀ ∈ centModSubgroup p (L.subgroupOf H) := by
      rw [mem_centModSubgroup_map_iff hp (QuotientGroup.mk' N₀) hker (by
        rw [Subgroup.normalizer_eq_top_iff.2 hK₀n]; exact Subgroup.mem_top _)]
      exact h1
    exact mem_centModSubgroup_of_subgroupOf hLH hHN h2
  have hcyc'' : IsCyclic Et :=
    isCyclic_of_surjective (Et.equivMapOfInjective H.subtype H.subtype_injective).symm.toMonoidHom
      (Et.equivMapOfInjective H.subtype H.subtype_injective).symm.surjective
  let f : ↥Et →* ↥E := ((QuotientGroup.mk' N₀).comp Et.subtype).codRestrict E (fun x => by
    rw [← hEtmap]; exact ⟨x, x.2, rfl⟩)
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : ↥H ⧸ N₀) ∈ Et.map (QuotientGroup.mk' N₀) := by rw [hEtmap]; exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact isCyclic_of_surjective f hsurj

end Hyp

section Main

theorem i268At_of_facts (hZ1 : S267FactZ1) (hZ3 : S267FactZ3) (G : Type) [Group G] [Finite G]
    (p : ℕ) : I268At G p := by
  classical
  intro hp hp2 q hq hq2 hqp X L hX hL hLayer hlie hcyc _hz hA
  obtain ⟨Q, hQq, hQ⟩ := hlie
  obtain ⟨A, hAX, hAel, hAc⟩ := hA
  haveI : Fact p.Prime := ⟨hp⟩
  have hQ2 : Q.p ≠ 2 := by rw [hQq]; exact hq2
  have hQp : Q.p ≠ p := by rw [hQq]; exact hqp
  have hLX : L ≤ X := hL.1
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := by
    have := P65.le_normalizer_glaPLayer (p := p) (X := X) (B := X) Subgroup.le_normalizer
    rwa [hLayer] at this
  set H : Subgroup G := L ⊔ A with hH
  have hLH : L ≤ H := le_sup_left
  have hAH : A ≤ H := le_sup_right
  have hHX : H ≤ X := sup_le hLX hAX
  have hHN : H ≤ Subgroup.normalizer (L : Set G) := hHX.trans hXL
  set K₀ : Subgroup ↥H := L.subgroupOf H with hK₀
  haveI hK₀n : K₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 hHN
  set N₀ : Subgroup ↥H := GLAPPrimeCoreOf p K₀ with hN₀def
  haveI hN₀n : N₀.Normal := by
    have h := normalizer_le_normalizer_glaPPrimeCoreOf p K₀
    rw [Subgroup.normalizer_eq_top_iff.2 hK₀n, top_le_iff] at h
    exact Subgroup.normalizer_eq_top_iff.1 h
  have hN : ¬ p ∣ Nat.card N₀ := not_dvd_card_glaPPrimeCoreOf hp K₀
  have hNK : N₀ ≤ K₀ := Subgroup.map_subtype_le _
  set π : ↥H →* ↥H ⧸ N₀ := QuotientGroup.mk' N₀ with hπ
  have hker : ¬ p ∣ Nat.card π.ker := by rw [hπ, QuotientGroup.ker_mk']; exact hN
  set S : Subgroup (↥H ⧸ N₀) := K₀.map π with hS
  set Ab : Subgroup (↥H ⧸ N₀) := (A.subgroupOf H).map π with hAb
  have hSn : S.Normal := hK₀n.map π (QuotientGroup.mk'_surjective N₀)
  have hq1 : CFSG.Open.IsQuasisimple (PQuot p L) := isQuasisimple_pQuot_of_glaPComponent hp hL
  obtain ⟨e₂⟩ := nonempty_pQuot_equiv_subgroupOf p hLH
  obtain ⟨e₃⟩ := nonempty_pQuot_equiv_map_self (p := p) (ψ := π) (K := K₀)
    (by rw [hπ, QuotientGroup.ker_mk', inf_eq_left.2 hNK])
  let e₁ : PQuot p L ≃* ↥S := e₂.symm.trans e₃
  have hSq : CFSG.Open.IsQuasisimple ↥S := hq1.of_mulEquiv e₁.symm
  have hSp : GLAPPrimeCore p ↥S = ⊥ := by
    have h1 := map_glaPPrimeCoreOf hp π hker K₀
    have h2 : GLAPPrimeCoreOf p S = ⊥ := by
      rw [← h1]
      exact (Subgroup.map_eq_bot_iff _).2 (by rw [hπ, QuotientGroup.ker_mk'])
    exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1 h2
  have hAel' : IsElemAbelian p (A.subgroupOf H) := isElemAbelian_subgroupOf hAel H
  have hAbel : IsElemAbelian p Ab := CFSG.SectionRank.isElemAbelian_map hAel' π
  have hAbc : Nat.card Ab = p ^ 4 := by
    rw [hAb, card_map_of_isPGroup hp π hker (isPGroup_of_isElemAbelian hAel'),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, hAc]
  have hcycS : CycModSylow p S := cycModSylow_quot hp hLH hHN N₀ hN₀def hcyc
  have hfin : ∀ hConc : S267Conc268 p S, S267Conc268X p L X := by
    intro hConc
    have hCov := conc268cov_of_quot hp hp2 N₀ hN K₀ hNK hK₀n hConc
    have hfinal := conc268X_of_Cov hp H hHX K₀ hCov
    rwa [show K₀.map H.subtype = L from Subgroup.map_subgroupOf_eq_of_le hLH] at hfinal
  by_cases hcen : Subgroup.center (PQuot p L) = ⊥
  · have hSc : Subgroup.center ↥S = ⊥ := by
      have := Subgroup.map_center_eq e₁
      rw [hcen, Subgroup.map_bot] at this; exact this.symm
    have e₅ : PSimple p L ≃* ↥S :=
      ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).trans e₁
    have hcatS : catalogIs ↥S (onLie fun d => d = .A 2 Q) ∨
        catalogIs ↥S (onLie fun d => d = .twistedA 2 Q) := by
      rcases hQ with h | h
      · exact Or.inl ((catalogIs_congr e₅).1 h)
      · exact Or.inr ((catalogIs_congr e₅).1 h)
    exact hfin (conc268_of_Z1 hZ1 hp hp2 Q hQ2 hQp S Ab hSn hSq hSc hcatS hAbel hAbc hcycS)
  · have hSc : Subgroup.center ↥S ≠ ⊥ := fun h =>
      hcen ((Subgroup.map_eq_bot_iff_of_injective _ e₁.injective).1
        (by rw [Subgroup.map_center_eq e₁]; exact h))
    have e₆ : PSimple p L ≃* ↥S ⧸ Subgroup.center ↥S :=
      QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)
    have hcatS : catalogIs (↥S ⧸ Subgroup.center ↥S) (onLie fun d => d = .A 2 Q) ∨
        catalogIs (↥S ⧸ Subgroup.center ↥S) (onLie fun d => d = .twistedA 2 Q) := by
      rcases hQ with h | h
      · exact Or.inl ((catalogIs_congr e₆).1 h)
      · exact Or.inr ((catalogIs_congr e₆).1 h)
    exact hfin (conc268_of_Z3 hZ3 hp hp2 Q hQ2 hQp S Ab hSn hSq hSp hSc hcatS hAbel hAbc hcycS)

end Main

end CFSG.LocalAnalysis.GLTheoremA.S267

end
