module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LDefs
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LHomB
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LHomC

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

namespace Hom

open Module

universe u

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

theorem comm_comp_subtype {G : Type u} [Group G] (ρ : G →* (V ≃ₗ[ZMod 2] V)) (M : Subgroup G) :
    comm (ρ.comp M.subtype) ⊤ = comm ρ M := by
  ext z
  rw [mem_comm, mem_comm]
  constructor
  · intro h m hm
    exact h ⟨m, hm⟩ trivial
  · intro h m _
    exact h m m.2

theorem cz_comp_subtype {G : Type u} [Group G] (ρ : G →* (V ≃ₗ[ZMod 2] V)) (M : Subgroup G) :
    cz (ρ.comp M.subtype) ⊤ = cz ρ M := by
  unfold cz
  rw [comm_comp_subtype]

theorem simple_comp_subtype {G : Type u} [Group G] (ρ : G →* (V ≃ₗ[ZMod 2] V)) (M : Subgroup G)
    (h : Simple ρ M) : Simple (ρ.comp M.subtype) ⊤ := by
  intro z hz
  rw [cz_comp_subtype] at hz
  exact h z hz

theorem cyclic_of_simple_odd {j : ℕ} (hdim : finrank (ZMod 2) V = 2 ^ j) :
    ∀ (n : ℕ) (G : Type u) [Group G] [Finite G] (ρ : G →* (V ≃ₗ[ZMod 2] V)),
      Nat.card G = n → Odd n → Function.Injective ρ → Simple ρ ⊤ → IsCyclic G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ ρ hn hodd hinj hs
    haveI : Nontrivial V := Module.finrank_pos_iff.mp (by rw [hdim]; positivity)
    rcases subsingleton_or_nontrivial G with hG | hG
    · exact isCyclic_of_subsingleton
    haveI : Group.IsSolvable G := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (hn ▸ hodd)
    obtain ⟨M, hMnorm, q, hq, hMq⟩ := exists_normal_prime_index G
    have hqn : q ∣ n := by
      rw [← hn, ← hMq]; exact Subgroup.index_dvd_card M
    have hq2 : ¬ q ∣ finrank (ZMod 2) V := by
      intro hd
      rw [hdim] at hd
      have h2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hd)
      subst h2
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hqn)
    have hsM : Simple ρ M := simple_of_prime_index ρ M hq hMq hq2 hs
    have hcard : Nat.card M * q = n := by rw [← hn, ← hMq]; exact Subgroup.card_mul_index M
    have hMpos : 0 < Nat.card M := Nat.card_pos
    have hoddM : Odd (Nat.card M) := Odd.of_dvd_nat hodd (Dvd.intro _ hcard)
    have hMlt : Nat.card M < n := by
      have := hq.two_le
      nlinarith
    have hcycM : IsCyclic M :=
      ih (Nat.card M) hMlt M (ρ.comp M.subtype) rfl hoddM (hinj.comp Subtype.val_injective)
        (simple_comp_subtype ρ M hsM)
    have hMab : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a := by
      intro a ha b hb
      letI := IsCyclic.commGroup (α := M)
      exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : M) ⟨b, hb⟩)
    have hinjZ : InjZ ρ M := injZ_of_simple ρ M hoddM hsM
    have hK : IsField (cz ρ M) := isField_cz ρ M hinjZ
    have hKd : finrank (ZMod 2) (cz ρ M) ∣ finrank (ZMod 2) V := by
      letI : Field (cz ρ M) := hK.toField
      exact Dvd.intro _ (Module.finrank_mul_finrank (ZMod 2) (cz ρ M) V)
    obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hdim ▸ hKd)
    have hcen : ∀ (x : G) (z : Module.End (ZMod 2) V), z ∈ cz ρ M → cj ρ x z = z := by
      intro x z hz
      have hoddx : Odd (orderOf (ρ x)) :=
        Odd.of_dvd_nat (hn ▸ hodd) ((orderOf_map_dvd ρ x).trans (orderOf_dvd_natCard x))
      exact centralize_of_odd (cz ρ M) hK t ht (ρ x) hoddx
        (fun z hz => cj_mem_cz ρ M x hz) z hz
    have hcentral : ∀ m ∈ M, ∀ x : G, x * m * x⁻¹ = m := by
      intro m hm x
      have h1 := hcen x _ (er_mem_cz ρ M hMab hm)
      rw [cj_er] at h1
      apply hinj
      apply LinearEquiv.ext
      intro v
      exact congrArg (fun y => y v) h1
    have hMc : M ≤ Subgroup.center G := by
      intro m hm
      rw [Subgroup.mem_center_iff]
      intro g
      have := hcentral m hm g
      calc g * m = g * m * g⁻¹ * g := by group
        _ = m * g := by rw [this]
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : IsCyclic (G ⧸ M) := isCyclic_of_prime_card (p := q) (by rw [← hMq]; rfl)
    have hab : ∀ a b : G, a * b = b * a := fun a b =>
      commutative_of_cyclic_center_quotient (QuotientGroup.mk' M) (by simpa using hMc) a b
    have hoddT : Odd (Nat.card (⊤ : Subgroup G)) := by rw [Subgroup.card_top]; exact hn ▸ hodd
    exact isCyclic_of_injZ ρ (injZ_of_simple ρ ⊤ hoddT hs) hinj hab

end Hom

theorem isCyclic_of_irreducible_odd {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (O : Subgroup (V ≃ₗ[ZMod 2] V)) (hodd : Odd (Nat.card O))
    {j : ℕ} (hdim : Module.finrank (ZMod 2) V = 2 ^ j)
    (hirr : ∀ U : Submodule (ZMod 2) V, (∀ g ∈ O, Stable g U) → U = ⊥ ∨ U = ⊤) : IsCyclic O := by
  haveI : Finite O := Nat.finite_of_card_ne_zero (by
    intro h; rw [h] at hodd; exact absurd hodd (by decide))
  refine Hom.cyclic_of_simple_odd hdim (Nat.card O) O O.subtype rfl hodd Subtype.val_injective
    (Hom.simple_of_irreducible O.subtype fun U hU => hirr U fun g hg u hu => hU ⟨g, hg⟩ u hu)

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
