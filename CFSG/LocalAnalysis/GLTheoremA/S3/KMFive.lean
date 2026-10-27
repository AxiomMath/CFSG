module

public import CFSG.LocalAnalysis.GLTheoremA.S3.KMExtra
public import CFSG.LocalAnalysis.GLTheoremA.S3.KMMin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S3.KM

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec3 (squares)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A T : Subgroup G}

theorem Ctx.centralizes_of_five (c : Ctx p A T) (hp5 : 5 ≤ p) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hVT : V ≤ T) (hVn : A ≤ normalizer (V : Set G)) :
    ∀ x ∈ V, ∀ a ∈ A, a * x = x * a := by
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => c.comm ha hb
  have hVle : V ≤ centralizer (A : Set G) := by
    refine le_of_forall_isHyp c.prime c.elem c.ne_bot hVn (c.not_dvd_card (c.two.to_le hVT)) ?_
    intro H hH
    set X := V ⊓ centralizer (H : Set G) with hX
    obtain ⟨α, hα, hαH⟩ := hH.exists_not_mem c.prime
    have hsup := hH.sup_zpowers c.prime hα hαH
    have hXe : IsElemAbelian 2 X := isElemAbelian_mono hV inf_le_left
    have hXT : X ≤ T ⊓ centralizer (H : Set G) := le_inf (inf_le_left.trans hVT) inf_le_right
    have hX4 : Nat.card X ≤ 4 := c.rank1 hH hXT hXe
    have hXn : A ≤ normalizer (X : Set G) := le_normalizer_inf_centralizer hAc hH.1 hVn
    have hXα : X ≤ centralizer ({α} : Set G) :=
      le_centralizer_of_card_lt c.prime (c.pow_p hα) (hXn hα) (by omega)
    intro x hx
    rw [mem_centralizer_iff]
    intro a ha
    exact commute_of_sup_zpowers hsup (fun h hh => (mem_centralizer_iff.1 (mem_inf.1 hx).2 h hh))
      (mem_centralizer_singleton_iff.1 (hXα hx)).symm a ha
  intro x hx a ha
  exact mem_centralizer_iff.1 (hVle hx) a ha

section AtomFive

variable {W S H : Subgroup G} {b : G}

theorem Atom.extra5 (c : Ctx p A T) (hp5 : 5 ≤ p) (hWT : W ≤ T) (a : Atom p A W b S H) :
    ∃ z : G, Extra S z ∧ (∀ x ∈ A, x * z = z * x) ∧ Nat.card S = 32 ∧
      (∀ u ∈ S, b * u = u * b → u = 1 ∨ u = z) ∧ (∀ f ∈ squares S, f = 1 ∨ f = z) := by
  have hsup : H ⊔ zpowers b = A := a.hyp.sup_zpowers c.prime a.hb a.not_mem
  have hST : S ≤ T := a.le.trans hWT
  have hnc : ∃ s ∈ S, ∃ t ∈ S, s * t ≠ t * s := by
    by_contra hcon
    push Not at hcon
    have hSe : IsElemAbelian 2 S :=
      ⟨⟨⟨fun x y => Subtype.ext (hcon x x.2 y y.2)⟩⟩, fun x hx => a.sq_eq_one_of_comm hcon hx⟩
    have hcen := c.centralizes_of_five hp5 hSe hST a.inv
    apply a.ne
    have h1 : ⁅S, zpowers b⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer]
      intro s hs
      rw [mem_centralizer_iff]
      intro x hx
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
      exact (Commute.zpow_left (hcen s hs b a.hb : Commute b s) i).eq
    rw [← a.perf]
    exact h1
  have hnc' : ¬ ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro hall
    obtain ⟨s, hs, t, ht, hst⟩ := hnc
    exact hst (hall s hs t ht)
  have hF1 : squares S ≠ ⊥ := by
    intro h
    apply hnc'
    have h1 := a.commutator_eq_squares
    rw [h] at h1
    intro x hx y hy
    have := commutator_eq_bot_iff_le_centralizer.1 h1 hx
    exact (mem_centralizer_iff.1 this y hy).symm
  have hFA : ∀ f ∈ squares S, ∀ x ∈ A, x * f = f * x := fun f hf =>
    commute_of_sup_zpowers hsup (fun h hh => a.cent f (a.squares_le hf) h hh) (a.squares_b hf)
  have hFe : IsElemAbelian 2 (squares S) :=
    ⟨⟨⟨fun x y => Subtype.ext (a.squares_central x.2 (a.squares_le y.2))⟩⟩,
      fun x hx => a.sq_squares hx⟩
  have hFle : squares S ≤ T ⊓ centralizer (A : Set G) :=
    le_inf ((a.squares_le).trans hST) (fun f hf => mem_centralizer_iff.2 (fun x hx => hFA f hf x hx))
  have hF2 : Nat.card (squares S) ≤ 2 := c.rank0 hFle hFe
  obtain ⟨z, hzF, hz1⟩ := exists_mem_ne_one hF1
  have hFz : ∀ f ∈ squares S, f = 1 ∨ f = z := by
    intro f hf
    by_cases hf1 : f = 1
    · exact Or.inl hf1
    · exact Or.inr (eq_of_card_le_two hF2 hf hzF hf1 hz1)
  have hzS : z ∈ S := a.squares_le hzF
  have hextra : Extra S z :=
    { two := a.isPGroup_S
      zS := hzS
      z1 := hz1
      z2 := a.sq_squares hzF
      center := by
        intro s hs
        constructor
        · intro hc
          exact hFz s (a.center_le_squares hnc' hs hc)
        · intro hs1
          have hsF : s ∈ squares S := by
            rcases hs1 with rfl | rfl
            · exact one_mem _
            · exact hzF
          intro t ht
          exact a.squares_central hsF ht
      comm_mem := by
        intro s hs t ht
        have : ⁅s, t⁆ ∈ squares S := by
          rw [← a.commutator_eq_squares]
          exact commutator_mem_commutator hs ht
        exact hFz _ this
      sq_mem := fun s hs => hFz _ (CFSG.RankThree.PartTwo.Sec3.sq_mem_squares hs)
      nonab := hnc }
  refine ⟨z, hextra, hFA z hzF, ?_, fun u hu hbu => hFz u (a.mem_squares_of_comm hu hbu), hFz⟩
  have hrank : ∀ V : Subgroup G, V ≤ S → IsElemAbelian 2 V → Nat.card V ≤ 4 := fun V hVS hVe =>
    c.rank1 a.hyp (le_inf (hVS.trans hST) (fun x hx => mem_centralizer_iff.2
      (fun h hh => a.cent x (hVS hx) h hh))) hVe
  have hcard := hextra.card_S_of_rank hrank
  have hFcard : Nat.card (squares S) = 2 := by
    have hnt : Nontrivial (squares S) := ⟨⟨⟨z, hzF⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
    have : 1 < Nat.card (squares S) := Finite.one_lt_card_iff_nontrivial.2 hnt
    omega
  have hCF : S ⊓ centralizer ({b} : Set G) = squares S := by
    apply le_antisymm
    · intro u hu
      obtain ⟨huS, huC⟩ := mem_inf.1 hu
      exact a.mem_squares_of_comm huS (mem_centralizer_singleton_iff.1 huC).symm
    · intro f hf
      exact mem_inf.2 ⟨a.squares_le hf, mem_centralizer_singleton_iff.2 (a.squares_b hf).symm⟩
  haveI : Fact p.Prime := ⟨c.prime⟩
  have hmod : Nat.card S ≡ Nat.card (squares S) [MOD p] := by
    have := card_modEq_card_inf_centralizer (c.pow_p a.hb) (a.inv a.hb)
    rwa [hCF] at this
  rw [hFcard] at hmod
  rcases hcard with h8 | h32
  · exfalso
    rw [h8] at hmod
    have h6 := (Nat.modEq_iff_dvd' (by norm_num : 2 ≤ 8)).1 hmod.symm
    have hdvd : p ∣ 2 * 3 := by simpa using h6
    rcases (Nat.Prime.dvd_mul c.prime).1 hdvd with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) h2
      omega
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
  · exact h32

end AtomFive

end CFSG.LocalAnalysis.GLTheoremA.S3.KM
