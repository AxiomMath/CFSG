module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentSplit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentExcl
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentOne
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentPair

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S172X CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem modelExist_orthDerived_of_type (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hn5 : n = 4 ∨ 6 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (htype : IsPlusType Q ↔ Odd n)
    (hb : CatDistinct.OrderBridge) {Q₁ : TauCeti.CFSGIndex → Prop}
    (hQ₁ : ∀ W : Submodule F V, (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate →
      Module.finrank F W = 2 → ¬ IsPlusType (Q.comp W.subtype) →
      catalogIs (PSimple p (⊤ : Subgroup ↥(orthDerived (Q.comp (polarPerp Q W).subtype)))) Q₁)
    (hexcl : ∀ (S : Type) [Group S] [Finite S],
      catalogIs S (isUnA (n - 1) (Nat.card F)) → catalogIs S Q₁ → False) :
    ModelExist p ↥(orthDerived Q) (n - 1) (isUnA (n - 1) (Nat.card F)) Q₁
      (isUnA (n - 2) (Nat.card F)) := by
  intro Bb hBb hcard d hd hLd hcd
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨f, hf1, hf⟩ := Cent.exists_natCard_eq_two_pow F
  obtain ⟨U, e, hF⟩ := exists_planeFrame hQ hdim hp hp2 hpq htype hBb hcard
  have hQ₁' : ∀ j, catalogIs (PSimple p (⊤ : Subgroup
      ↥(orthDerived (Q.comp (polarPerp Q (U j)).subtype)))) Q₁ := fun j =>
    hQ₁ (U j) (hF.nondeg j) (hF.finrank_eq j) (hF.not_isPlusType j)
  obtain ⟨h, hh, hh1, hU⟩ := exists_primary_of_layerIs hQ hdim hn hf hf1 hp hp2 hpq hb hF hQ₁'
    hexcl hd hLd hcd
  have hm4 : 4 ≤ n - 2 ∨ ((n - 2 = 2 ∨ n - 2 = 3) ∧ 4 ≤ Nat.card F) := by
    rcases hn5 with rfl | h6
    · right
      refine ⟨Or.inl rfl, ?_⟩
      have hLd2 : catalogIs (PSimple p (GLALayer (Subgroup.centralizer {d})))
          (isUnA (4 - 1) (2 ^ f)) := by
        rw [← hf]
        exact hLd.2
      obtain ⟨-, h2, -⟩ := S172.v2_isUnA hb hf1 hLd2
      have hf2 : 2 ≤ f := h2 (by norm_num)
      rw [hf]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    · left
      omega
  let j₀ : Fin (n - 1) := ⟨0, by omega⟩
  let j₁ : Fin (n - 1) := ⟨1, by omega⟩
  obtain ⟨hL1, hc1⟩ := layerIs_centralizer_rot hQ hdim hn hp hp2 hpq htype hF j₀ (hQ₁' j₀)
  refine ⟨e j₀, hF.mem j₀, ?_, hL1, hc1,
    layerIs_centralizer_pair hQ hdim hn hp hp2 hpq hF hd hh hh1 hU j₀ hm4⟩
  intro hy
  have hfix := hF.apply_eq_of_mem_zpowers hp hd hy j₁ (by simp [j₀, j₁, Fin.ext_iff])
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U j₁) (hF.finrank_eq j₁)
  exact hv0 (eq_zero_of_mem_primaryComponent_of_apply_eq hh hh1 (hU j₁ hv) (hfix v hv))

theorem modelExist_orthDerived_minus (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (_hbound : ∀ E : Subgroup ↥(orthDerived Q), IsElemAbelian p E → Nat.card E ≤ p ^ (n - 1))
    (hminus : ¬ IsPlusType Q) (hn : 4 ≤ n) (heven : Even n) (hb : CatDistinct.OrderBridge) :
    ModelExist p ↥(orthDerived Q) (n - 1) (isUnA (n - 1) (Nat.card F))
      (isOmPA (n - 1) (Nat.card F)) (isUnA (n - 2) (Nat.card F)) := by
  obtain ⟨f, hf1, hf⟩ := Cent.exists_natCard_eq_two_pow F
  have htype : IsPlusType Q ↔ Odd n :=
    ⟨fun h => absurd h hminus, fun h => absurd heven (Nat.not_even_iff_odd.2 h)⟩
  refine modelExist_orthDerived_of_type hQ hdim hn (by obtain ⟨k, hk⟩ := heven; omega) hp hp2 hpq
    htype hb (fun W hW hW2 hWm => ?_) (fun S _ _ h1 h2 => ?_)
  · have hdimW : Module.finrank F (polarPerp Q W) = 2 * (n - 1) := by
      rw [finrank_polarPerp hQ W, hdim, hW2]
      omega
    exact Cent.catalogIs_pSimple_top_orthDerived_plus (Cent.nondeg_comp_polarPerp hQ hW) (m := n - 1)
      (by omega) hdimW
      ((Cent.isPlusType_comp_polarPerp_iff hQ hdim (by omega) hW hW2 hWm).2 hminus) hp hp2 hpq
  · rw [hf] at h1 h2
    exact Cent.false_of_catalogIs_isUnA_isOmPA hb hf1 h1 h2

end CFSG.LocalAnalysis.GLTheoremA.S172C

end
