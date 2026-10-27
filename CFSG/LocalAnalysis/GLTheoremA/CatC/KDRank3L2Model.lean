module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3L2
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSL

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

namespace KDRank3L2

open CFSG.Open (StatedClassicalModel StatedLieTag StatedProj StatedSL)

theorem center_eq_bot_of_simple {G : Type*} [Group G] (hs : IsSimpleGroup G)
    (hna : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hna
    exact absurd ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a)) b).symm hab

theorem two_le_of_dvd_numerator {p g : ℕ} (hp : p.Prime) (hg : 1 ≤ g)
    (h : p ^ 2 ∣ p ^ g * ((p ^ g) ^ 2 - 1)) : 2 ≤ g := by
  by_contra hlt
  have hg1 : g = 1 := by omega
  subst hg1
  simp only [pow_one] at h
  have h1 : p * p ∣ p * (p ^ 2 - 1) := by rwa [← sq]
  have h2 : p ∣ p ^ 2 - 1 := Nat.dvd_of_mul_dvd_mul_left hp.pos h1
  have h3 : p ∣ p ^ 2 - 1 + 1 := by
    rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)]
    exact dvd_pow_self p two_ne_zero
  have := (Nat.dvd_add_right h2).1 h3
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

theorem exists_numerator_dvd {p ℓ f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (hm : StatedClassicalModel S .PSL 2 ℓ f) {E : Subgroup (MulAut S)} (hE : IsElemAbelian p E)
    (hnot : ¬ E ≤ inner S) (hE0 : Nat.card ↥(E ⊓ inner S) = p ^ 2) :
    ∃ f₀ : ℕ, f = p * f₀ ∧
      p ^ 2 ∣ CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 2 (ℓ ^ f₀) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple hs hna
  have hconj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    conj_injective_of_center_eq_bot hZ
  obtain ⟨x, hxE, hxI⟩ := Set.not_subset.1 hnot
  have hxp : x ^ p = 1 := hE.2 x hxE
  obtain ⟨f₀, hff₀, hdvd⟩ :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrder_PSL_two hm hp hp2 x hxp hxI
  set E₀ : Subgroup (MulAut S) := E ⊓ inner S with hE₀def
  set A : Subgroup S := E₀.comap MulAut.conj with hAdef
  have hAmap : A.map MulAut.conj = E₀ := Subgroup.map_comap_eq_self inf_le_right
  have hAcard : Nat.card A = p ^ 2 := by
    rw [← hE0, ← hAmap, Subgroup.card_map_of_injective hconj]
  have hAfix : A ≤ CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup x := by
    intro u hu
    have huE : (MulAut.conj u : MulAut S) ∈ E := (show (MulAut.conj u : MulAut S) ∈ E₀ from hu).1
    have hcomm := isElemAbelian_commute hE hxE huE
    have h1 : x * MulAut.conj u * x⁻¹ = MulAut.conj (x u) := by
      ext y
      simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]
    have h2 : (MulAut.conj (x u) : MulAut S) = MulAut.conj u := by
      rw [← h1, hcomm]; group
    exact hconj h2
  have hp2dvd : p ^ 2 ∣ Nat.card (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup x) :=
    hAcard ▸ Subgroup.card_dvd_of_le hAfix
  exact ⟨f₀, hff₀, hp2dvd.trans hdvd⟩

theorem rank3Concl_linTwo {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (hm : StatedClassicalModel S .PSL 2 p f) {E : Subgroup (MulAut S)} (hE : IsElemAbelian p E)
    (hnot : ¬ E ≤ inner S) (hE0 : Nat.card ↥(E ⊓ inner S) = p ^ 2) : Rank3Concl p S E := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple hs hna
  have hm' := hm
  obtain ⟨⟨-, hf1, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hm'
  obtain ⟨f₀, hff₀, hnum⟩ := exists_numerator_dvd hp hp2 hs hna hm hE hnot hE0
  have hf₀1 : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h | h
    · rw [h] at hff₀; omega
    · exact h
  have hnum' : p ^ 2 ∣ p ^ f₀ * ((p ^ f₀) ^ 2 - 1) := by
    simpa [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator] using hnum
  have hf₀2 : 2 ≤ f₀ := two_le_of_dvd_numerator hp hf₀1 hnum'
  have hf6 : 6 ≤ f := by
    have : 3 ≤ p := by have := hp.two_le; omega
    rw [hff₀]; nlinarith
  let e' : S ≃* CFSG.GorensteinWalter.PSL2 F :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  refine KDRank3Aux.rank3Concl_of_mulEquiv e' ?_
  set φ : MulAut S →* MulAut (CFSG.GorensteinWalter.PSL2 F) := (MulAut.congr e').toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.congr e').injective
  have hZ' : Subgroup.center (CFSG.GorensteinWalter.PSL2 F) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e'.symm z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      have := hz (e' g)
      have h2 := congrArg e'.symm this
      simpa using h2
    rw [hZ] at hz'
    have h3 : e'.symm z = 1 := Subgroup.mem_bot.1 hz'
    have h4 : z = 1 := by simpa using congrArg e' h3
    simp [h4]
  have hinn : (inner S).map φ = inner (CFSG.GorensteinWalter.PSL2 F) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i196_map_innerAut_congr e'
  have hE0' : Nat.card ↥(E.map φ ⊓ inner (CFSG.GorensteinWalter.PSL2 F)) = p ^ 2 := by
    rw [← hinn, ← Subgroup.map_inf E (inner S) φ hφinj, Subgroup.card_map_of_injective hφinj]
    exact hE0
  exact rank3Concl_psl2 hp hp2 hFcard hf6 hZ' (CFSG.Open.IsElemAbelian.map hE φ) hE0'

end KDRank3L2

end CFSG.LocalAnalysis.GLTheoremA
