module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATFrob

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns

section Equiv

variable {A B C : Type*} [Group A] [Group B] [Group C]

theorem exists_equiv_of_surjective_ker (f : A →* C) (g : B →* C) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (hkf : f.ker = Subgroup.center A)
    (hkg : g.ker = Subgroup.center B) :
    ∃ E : (A ⧸ Subgroup.center A) ≃* (B ⧸ Subgroup.center B),
      ∀ (a : A) (b : B), E (QuotientGroup.mk a) = QuotientGroup.mk b ↔ f a = g b := by
  let Ef := QuotientGroup.quotientKerEquivOfSurjective f hf
  let Eg := QuotientGroup.quotientKerEquivOfSurjective g hg
  let E : (A ⧸ Subgroup.center A) ≃* (B ⧸ Subgroup.center B) :=
    (QuotientGroup.quotientMulEquivOfEq hkf.symm).trans
      (Ef.trans (Eg.symm.trans (QuotientGroup.quotientMulEquivOfEq hkg)))
  refine ⟨E, fun a b => ?_⟩
  have h1 : E (QuotientGroup.mk a) =
      QuotientGroup.quotientMulEquivOfEq hkg (Eg.symm (f a)) := by
    simp only [E, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have h2 : (QuotientGroup.mk b : B ⧸ Subgroup.center B) =
      QuotientGroup.quotientMulEquivOfEq hkg (QuotientGroup.mk b) :=
    (QuotientGroup.quotientMulEquivOfEq_mk hkg b).symm
  rw [h1, h2, (QuotientGroup.quotientMulEquivOfEq hkg).injective.eq_iff, MulEquiv.symm_apply_eq]
  exact Iff.rfl

end Equiv

section Perfect

theorem range_le_commutator {H G' : Type*} [Group H] [Group G'] (θ : H →* G')
    (h : commutator H = ⊤) : θ.range ≤ ⁅θ.range, θ.range⁆ := by
  have : (commutator H).map θ = ⁅θ.range, θ.range⁆ := by
    change (⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆).map θ = _
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map]
  rw [← this, h, Subgroup.map_top]

theorem map_le_commutator {Y G' : Type*} [Group Y] [Group G'] (φ : Y →* G') {S : Subgroup Y}
    (h : commutator ↥S = ⊤) : S.map φ ≤ ⁅S.map φ, S.map φ⁆ := by
  have := range_le_commutator (φ.comp S.subtype) h
  rwa [MonoidHom.range_comp, Subgroup.range_subtype] at this

end Perfect

section Restrict

variable {π : Bool} {p f : ℕ} {F : Type} [Field F]

theorem isFieldAutThree_restrict {Y : Type} [Group Y] [Finite Y] {hK : PiField π p f F}
    (hq : ModThree π (p ^ f)) (h8 : π = false → p ^ f ≠ 8)
    (e : (Y ⧸ Subgroup.center Y) ≃*
      (↥(slPi π 3 (p ^ f) F) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) F)))
    {α ε : MulAut Y} {ρ τ : F ≃+* F} (hρ : orderOf ρ = 3) (hτρ : τ * ρ = ρ * τ)
    (hτodd : π = false → Odd (orderOf τ))
    (hα : MulAut.congr e (centerDescend Y α) = centerDescend _ (frobSL hK ρ))
    (hε : MulAut.congr e (centerDescend Y ε) = centerDescend _ (frobSL hK τ))
    {S : Subgroup Y} (hSq : CFSG.Open.IsQuasisimple ↥S) (hSfix : S = fixSub α)
    (hZS : ∀ z : ↥S, z ∈ Subgroup.center ↥S → (z : Y) ∈ Subgroup.center Y) (ρS : MulAut ↥S)
    (hρS : ∀ s : ↥S, ((ρS s : ↥S) : Y) = ε (s : Y)) : IsFieldAutThree ρS := by
  have := hK.finite
  obtain ⟨d⟩ := exists_frobData hK hρ
  have hq₀ := d.modThree hq
  have hne : π = false → p ^ d.f₀ ≠ 2 := fun h h2 => h8 h (by rw [d.pow_eq, h2]; norm_num)
  have hq₀2 : π = false → 2 < p ^ d.f₀ := fun h => by
    have h1 : p ≤ p ^ d.f₀ := Nat.le_self_pow (by have := d.hP.one_le; omega) p
    have h2 := hK.prime.two_le
    have := hne h
    omega
  have hcom : ∀ c, c ∈ d.K₀ ↔ τ c ∈ d.K₀ := by
    intro c
    rw [d.hKσ c, d.hKσ (τ c)]
    have h1 : ρ (τ c) = τ (ρ c) := by
      have := congrArg (fun x : F ≃+* F => x c) hτρ
      simp only [RingAut.mul_apply] at this
      exact this.symm
    rw [h1]
    exact ⟨fun h => by rw [h], fun h => τ.injective h⟩
  obtain ⟨τ₀, hτ₀⟩ := exists_restrict hcom
  have hτ₀odd : π = false → Odd (orderOf τ₀) := fun h =>
    (hτodd h).of_dvd_nat (orderOf_restrict_dvd hτ₀)
  set G := ↥(slPi π 3 (p ^ f) F) with hG
  set G₀ := ↥(slPi π 3 (p ^ d.f₀) d.K₀) with hG₀
  let pm : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' _
  have hsurj : Function.Surjective pm := QuotientGroup.mk'_surjective _
  have hker : ∀ c, pm c = 1 → c ∈ Subgroup.center G := fun c h => (QuotientGroup.eq_one_iff c).1 h
  have hc : ∀ x, pm (frobSL hK ρ x) = centerDescend G (frobSL hK ρ) (pm x) := fun x => rfl
  set φ : Y →* (G ⧸ Subgroup.center G) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y)) with hφ
  have hφsurj : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφker : ∀ c, φ c = 1 → c ∈ Subgroup.center Y := by
    intro c h
    apply (QuotientGroup.eq_one_iff c).1
    apply e.injective
    rw [map_one]
    exact h
  have hφα : ∀ y, φ (α y) = centerDescend G (frobSL hK ρ) (φ y) := fun y => by
    have := descend_apply_mk e α y
    rw [hα] at this
    exact this.symm
  have hφε : ∀ y, φ (ε y) = centerDescend G (frobSL hK τ) (φ y) := fun y => by
    have := descend_apply_mk e ε y
    rw [hε] at this
    exact this.symm
  let θ : G₀ →* G ⧸ Subgroup.center G := pm.comp d.incl
  set Ŝ : Subgroup (G ⧸ Subgroup.center G) := (fixSub (frobSL hK ρ)).map pm with hŜ
  have hrange : θ.range = Ŝ := by
    rw [MonoidHom.range_comp, ← d.fixSub_eq]
  have hker' : θ.ker = Subgroup.center G₀ := by
    ext s0
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : d.incl s0 ∈ Subgroup.center G := hker _ h
      rw [← d.map_center_incl hq] at h1
      obtain ⟨z, hz, hzs⟩ := h1
      rwa [← d.incl_injective hzs]
    · intro h
      apply (QuotientGroup.eq_one_iff _).2
      rw [← d.map_center_incl hq]
      exact ⟨s0, h, rfl⟩
  have hS₀q : CFSG.Open.IsQuasisimple G₀ := isQuasisimple_slPi d.hP hne
  set C := fixSub (centerDescend G (frobSL hK ρ)) with hC
  have hŜC : Ŝ ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_fixSub, ← hc, mem_fixSub.1 hx]
  have hcommC : ⁅C, C⁆ ≤ Ŝ := fixSub_commutator_le_map hsurj hker hc
  have hcommC' : ⁅C, C⁆ ≤ S.map φ := by
    have := fixSub_commutator_le_map hφsurj hφker hφα
    rw [hSfix]
    exact this
  have hSC : S.map φ ≤ C := by
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_fixSub, ← hφα]
    have : α s = s := mem_fixSub.1 (hSfix ▸ hs)
    rw [this]
  have hSŜ : S.map φ = Ŝ := by
    refine le_antisymm ?_ ?_
    · exact (map_le_commutator φ hSq.1).trans ((Subgroup.commutator_mono hSC hSC).trans hcommC)
    · rw [← hrange]
      exact (range_le_commutator θ hS₀q.1).trans (by
        rw [hrange]; exact (Subgroup.commutator_mono hŜC hŜC).trans hcommC')
  let fS : ↥S →* ↥Ŝ := (φ.comp S.subtype).codRestrict Ŝ (fun s => by
    rw [← hSŜ]; exact ⟨s, s.2, rfl⟩)
  let gS : G₀ →* ↥Ŝ := θ.codRestrict Ŝ (fun t => by rw [← hrange]; exact ⟨t, rfl⟩)
  have hfS : Function.Surjective fS := by
    rintro ⟨x, hx⟩
    rw [← hSŜ] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    exact ⟨⟨s, hs⟩, rfl⟩
  have hgS : Function.Surjective gS := by
    rintro ⟨x, hx⟩
    rw [← hrange] at hx
    obtain ⟨t, rfl⟩ := hx
    exact ⟨t, rfl⟩
  have hkS : fS.ker = Subgroup.center ↥S := by
    ext s
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : φ (s : Y) = 1 := congrArg Subtype.val h
      have h2 := hφker _ h1
      rw [Subgroup.mem_center_iff] at h2 ⊢
      intro g
      exact Subtype.ext (h2 (g : Y))
    · intro h
      apply Subtype.ext
      show φ (s : Y) = 1
      have h1 := hZS s h
      show e (QuotientGroup.mk (s : Y)) = 1
      rw [(QuotientGroup.eq_one_iff _).2 h1, map_one]
  have hkg : gS.ker = Subgroup.center G₀ := by
    rw [← hker']
    ext t
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  obtain ⟨E, hE⟩ := exists_equiv_of_surjective_ker fS gS hfS hgS hkS hkg
  refine isFieldAutThree_of_frob' d.hP hq₀2 E hτ₀odd ?_
  ext x
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (E.symm (QuotientGroup.mk t))
  have hst : E (QuotientGroup.mk s) = QuotientGroup.mk t := by
    rw [hs, MulEquiv.apply_symm_apply]
  have h1 := (hE s t).1 hst
  have h2 : φ (s : Y) = θ t := congrArg Subtype.val h1
  have key : E (QuotientGroup.mk (ρS s)) = QuotientGroup.mk (frobSL d.hP τ₀ t) := by
    refine (hE (ρS s) (frobSL d.hP τ₀ t)).2 (Subtype.ext ?_)
    show φ ((ρS s : ↥S) : Y) = θ (frobSL d.hP τ₀ t)
    rw [hρS, hφε, h2]
    show _ = pm (d.incl (frobSL d.hP τ₀ t))
    rw [← frobSL_incl d hτ₀ t]
    rfl
  have h3 := descend_apply_mk E ρS s
  rw [hst, key] at h3
  rw [h3, centerDescend_mk]

end Restrict

end CFSG.HardMathSupport.Solomon.Coordinator
