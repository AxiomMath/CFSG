module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cIface

public section

namespace CFSG.GH74.GLS.Stage4.Rest

namespace Mix11cN

section Trivial

variable {k G W : Type*} [Field k] [Monoid G] [AddCommGroup W] [Module k W]

theorem smul_mem_of_trivial (σ : Representation k G W) (htriv : ∀ g, σ g = 1)
    (S : Submodule k σ.asModule) (r : MonoidAlgebra k G) {x : σ.asModule} (hx : x ∈ S) :
    r • x ∈ S := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    have h : (MonoidAlgebra.of k G g) • x = x := by
      show σ.asAlgebraHom (MonoidAlgebra.of k G g) x = x
      rw [Representation.asAlgebraHom_of, htriv g]
      rfl
    rw [h]
    exact hx
  | add f g hf hg =>
    rw [add_smul]
    exact S.add_mem hf hg
  | smul a f hf =>
    rw [smul_assoc]
    exact S.smul_mem a hf

theorem finrank_le_one_of_trivial [Module.Finite k W] (σ : Representation k G W)
    (hs : IsSimpleModule (MonoidAlgebra k G) σ.asModule) (htriv : ∀ g, σ g = 1) :
    Module.finrank k W ≤ 1 := by
  have := hs
  by_contra hlt
  have h2 : 1 < Module.finrank k W := not_le.1 hlt
  obtain ⟨w, hw⟩ : ∃ w : σ.asModule, w ≠ 0 := by
    have : 0 < Module.finrank k W := by omega
    obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.1 this
    exact ⟨w, hw⟩
  let S : Submodule k σ.asModule := Submodule.span k {w}
  let N : Submodule (MonoidAlgebra k G) σ.asModule :=
    { toAddSubmonoid := S.toAddSubmonoid
      smul_mem' := fun r x hx => smul_mem_of_trivial σ htriv S r hx }
  have hwN : w ∈ N := Submodule.mem_span_singleton_self w
  rcases eq_bot_or_eq_top N with h | h
  · rw [h] at hwN
    exact hw ((Submodule.mem_bot _).1 hwN)
  · have hall : ∀ x : σ.asModule, ∃ c : k, c • w = x := by
      intro x
      have hx : x ∈ N := by rw [h]; exact Submodule.mem_top
      exact Submodule.mem_span_singleton.1 hx
    have hall' : ∀ x : W, ∃ c : k, c • (w : W) = x := fun x => hall x
    have h3 : Module.finrank k W ≤ 1 := finrank_le_one_iff.2 ⟨(w : W), hall'⟩
    omega

end Trivial

theorem charP_of_card {p n : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ n) : CharP F p := by
  have := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (f := n) (by rw [← hF, Nat.card_eq_fintype_card])

end Mix11cN

open Mix11cN

theorem mix11c_sl2class (hD : Mix11cDescent) (hN : Mix11cNumerics) : Mix11cSL2Class := by
  intro p n hp hp2 hn F _ _ hF
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card hF
  let _ : Algebra (ZMod p) F := ZMod.algebra F p
  obtain ⟨hD1, hD2⟩ := hD p n hp2 hn F hF
  obtain ⟨hN1, hN2, hN3⟩ := hN
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hnt : ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
      (σ : Representation (ZMod p) (SLm F) W),
      IsSimpleModule (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule →
      2 * n < Module.finrank (ZMod p) W → ∃ g, σ g ≠ 1 := by
    intro W _ _ _ σ hs hd
    by_contra h
    have h' : ∀ g, σ g = 1 := fun g => by
      by_contra hne
      exact h ⟨g, hne⟩
    have := finrank_le_one_of_trivial σ hs h'
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro W _ _ _ σ hs hne
    obtain ⟨A, c, hA, hA0, hc, -, hdim, -, -⟩ := hD1 W σ hs hne
    rw [hdim]
    exact (hN1 p n hp hp2 hn A hA hA0 c hc).1
  · intro W _ _ _ σ hs h1 h2
    obtain ⟨A, c, hA, hA0, hc, -, hdim, hneg, hend⟩ := hD1 W σ hs (hnt W σ hs h1)
    rw [hdim] at h1 h2
    obtain ⟨hc1, hshape⟩ := (hN1 p n hp hp2 hn A hA hA0 c hc).2 h2 h1
    subst hc1
    rcases hshape with ⟨hr, he, j, hj, hAj⟩ | ⟨hr, he, j, hj, hAj⟩
    · right
      refine ⟨?_, ?_, ?_⟩
      · intro w
        have hev : Even A := ⟨p ^ j, by rw [hAj]; ring⟩
        have h1 : (-1 : ZMod p) ^ A = 1 := Even.neg_one_pow hev
        rw [hneg w, h1, one_smul]
      · rw [hdim, hr, he]
        ring
      · rw [hend rfl, hr]
    · left
      refine ⟨?_, ?_⟩
      · intro w
        have hodd' : Odd A := by
          rw [hAj]
          exact (((odd_one.add_odd (hodd.pow)).add_odd hodd.pow)).mul hodd.pow
        have h1 : (-1 : ZMod p) ^ A = -1 := Odd.neg_one_pow hodd'
        rw [hneg w, h1]
        exact neg_one_smul (ZMod p) w
      · rw [hdim, he]
        omega
  · intro W W' _ _ _ _ _ _ σ σ' hs hs' h1 h2 hdd
    obtain ⟨A, c, hA, hA0, hc, hconst, hdim, -, -⟩ := hD1 W σ hs (hnt W σ hs h1)
    have h1' : 2 * n < Module.finrank (ZMod p) W' := by rw [hdd]; exact h1
    have h2' : Module.finrank (ZMod p) W' < 4 * n := by rw [hdd]; exact h2
    obtain ⟨A', c', hA', hA0', hc', hconst', hdim', -, -⟩ := hD1 W' σ' hs' (hnt W' σ' hs' h1')
    have hlt : c * rotPeriod p n A * digitProd p n A < 4 * n := by rw [← hdim]; exact h2
    have hgt : 2 * n < c * rotPeriod p n A * digitProd p n A := by rw [← hdim]; exact h1
    have hlt' : c' * rotPeriod p n A' * digitProd p n A' < 4 * n := by rw [← hdim']; exact h2'
    have hgt' : 2 * n < c' * rotPeriod p n A' * digitProd p n A' := by rw [← hdim']; exact h1'
    obtain ⟨hc1, hshape⟩ := (hN1 p n hp hp2 hn A hA hA0 c hc).2 hlt hgt
    obtain ⟨hc1', hshape'⟩ := (hN1 p n hp hp2 hn A' hA' hA0' c' hc').2 hlt' hgt'
    subst hc1 hc1'
    have hrel : ∃ s : ℕ, A' = (rot p n)^[s] A := by
      rcases hshape with ⟨hr, he, j, hj, hAj⟩ | ⟨hr, he, j, hj, hAj⟩ <;>
        rcases hshape' with ⟨hr', he', j', hj', hAj'⟩ | ⟨hr', he', j', hj', hAj'⟩
      · obtain ⟨s, hs⟩ := hN2 p n hp3 j j' hj hj'
        exact ⟨s, by rw [hAj', hAj, hs]⟩
      · exfalso
        rw [hr, he] at hdim
        rw [he'] at hdim'
        omega
      · exfalso
        rw [he] at hdim
        rw [hr', he'] at hdim'
        omega
      · obtain ⟨s, hs⟩ := hN3 p n hp3 ⟨rotPeriod p n A, hr.symm⟩ j j' hj hj'
        exact ⟨s, by rw [hAj', hAj, hs]⟩
    exact hD2 W W' σ σ' hs hs' A A' hconst hconst' hrel hdd.symm

end CFSG.GH74.GLS.Stage4.Rest
