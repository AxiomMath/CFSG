module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Pull4
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Pull3

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut)

variable {G : Type} [Group G] {L : Subgroup G} {z t : G} {T : Subgroup G}
  {EY : Subgroup (MulAut (↥L ⧸ center ↥L))}

open Classical in
@[expose] noncomputable def nuExt (L : Subgroup G) (e : G) : MulAut (↥L ⧸ center ↥L) :=
  if hl : e ∈ L then nuL L ⟨e, hl⟩ else 1

theorem nuExt_of_mem {e : G} (hl : e ∈ L) : nuExt L e = nuL L ⟨e, hl⟩ := by
  simp [nuExt, hl]

namespace PullHyp

variable (h : PullHyp G L z t T EY)

include h in
theorem pullE_roots_image :
    nuExt L '' {e | e ∈ pullE L EY ∧ e * e = t} =
      {ε | ε ∈ EY ∧
        ε * ε = MulAut.conj (((⟨t, h.cfg.t_mem_A⟩ : ↥L)) : ↥L ⧸ center ↥L)} := by
  ext ε
  constructor
  · rintro ⟨e, ⟨he, he2⟩, rfl⟩
    obtain ⟨hl, hν⟩ := mem_pullE.1 he
    rw [nuExt_of_mem hl]
    refine ⟨hν, ?_⟩
    have : nuL L ⟨e, hl⟩ * nuL L ⟨e, hl⟩ = nuL L ⟨t, h.cfg.t_mem_A⟩ := by
      rw [← map_mul]
      exact congrArg (nuL L) (Subtype.ext he2)
    exact this
  · rintro ⟨hε, hε2⟩
    obtain ⟨e, he, hl, hνe⟩ := h.exists_mem_pullE hε
    refine ⟨e, ⟨he, ?_⟩, by rw [nuExt_of_mem hl, hνe]⟩
    have : nuL L (⟨e, hl⟩ * ⟨e, hl⟩) = nuL L ⟨t, h.cfg.t_mem_A⟩ := by
      rw [map_mul, hνe]
      exact hε2
    exact congrArg Subtype.val (h.nuL_inj this)

include h in
theorem pullE_roots_injOn :
    Set.InjOn (nuExt L) {e | e ∈ pullE L EY ∧ e * e = t} := by
  rintro e ⟨he, -⟩ e' ⟨he', -⟩ hee
  obtain ⟨hl, -⟩ := mem_pullE.1 he
  obtain ⟨hl', -⟩ := mem_pullE.1 he'
  rw [nuExt_of_mem hl, nuExt_of_mem hl'] at hee
  exact congrArg Subtype.val (h.nuL_inj hee)

include h in
theorem pullE_roots_ge : 20 ≤ Set.ncard {e : G | e ∈ pullE L EY ∧ e * e = t} := by
  have h1 := h.facts.E_roots_ge
  rw [← h.pullE_roots_image, h.pullE_roots_injOn.ncard_image] at h1
  exact h1

include h in
theorem pullE_eq_closure_roots :
    pullE L EY = closure {e : G | e ∈ pullE L EY ∧ e * e = t} := by
  apply le_antisymm
  · intro e he
    obtain ⟨hl, hν⟩ := mem_pullE.1 he
    have hEYc : ∀ x, x ∈ closure {ε | ε ∈ EY ∧
        ε * ε = MulAut.conj (((⟨t, h.cfg.t_mem_A⟩ : ↥L)) : ↥L ⧸ center ↥L)} → x ∈ EY := by
      intro x hx
      rw [h.facts.E_roots]
      exact hx
    have key : ∀ ε, ε ∈ closure {ε | ε ∈ EY ∧
        ε * ε = MulAut.conj (((⟨t, h.cfg.t_mem_A⟩ : ↥L)) : ↥L ⧸ center ↥L)} →
        ∀ l : ↥L, nuL L l = ε → (l : G) ∈ closure {e : G | e ∈ pullE L EY ∧ e * e = t} := by
      intro ε hε
      induction hε using Subgroup.closure_induction with
      | mem x hx =>
        intro l hl
        refine subset_closure ⟨(nuL_mem_iff l).2 (hl ▸ hx.1), ?_⟩
        have : nuL L (l * l) = nuL L ⟨t, h.cfg.t_mem_A⟩ := by
          rw [map_mul, hl]
          exact hx.2
        exact congrArg Subtype.val (h.nuL_inj this)
      | one =>
        intro l hl
        have : l = 1 := h.nuL_inj (hl.trans (map_one _).symm)
        rw [this]
        exact one_mem _
      | mul x y hx hy ihx ihy =>
        intro l hl
        obtain ⟨lx, hlx⟩ := h.exists_nuL_of_mem (hEYc x hx)
        obtain ⟨ly, hly⟩ := h.exists_nuL_of_mem (hEYc y hy)
        have : l = lx * ly := h.nuL_inj (by rw [hl, map_mul, hlx, hly])
        rw [this]
        exact mul_mem (ihx lx hlx) (ihy ly hly)
      | inv x hx ihx =>
        intro l hl
        obtain ⟨lx, hlx⟩ := h.exists_nuL_of_mem (hEYc x hx)
        have : l = lx⁻¹ := h.nuL_inj (by rw [hl, map_inv, hlx])
        rw [this]
        exact inv_mem (ihx lx hlx)
    exact key _ (by rw [← h.facts.E_roots]; exact hν) ⟨e, hl⟩ rfl
  · rw [closure_le]
    exact fun e he => he.1

end PullHyp

variable [Finite G]

theorem exists_outerE_roots (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hZ : center ↥L = ⊥)
    (hcZ : center (↥L ⧸ center ↥L) = ⊥) (hOE : OuterEData (↥L ⧸ center ↥L))
    (hout : (innAut (↥L ⧸ center ↥L)).index ∣ 2)
    (hidx : (L ⊔ centralizer (L : Set G)).relIndex (normalizer (L : Set G)) = 2)
    (cfg : OuterConfig G L z t T) :
    ∃ E : Subgroup G, OuterE G L z t T E ∧ Nat.card (MulAut ↥E) = 1920 ∧ Nat.card ↥T = 512 ∧
      E = closure {e | e ∈ E ∧ e * e = t} ∧ 20 ≤ Set.ncard {e | e ∈ E ∧ e * e = t} := by
  obtain ⟨EY, hP⟩ := exists_pullHyp h hS hZ hcZ hOE hout hidx cfg
  exact ⟨_, hP.outerE, hP.card_aut_pullE, hP.card_T, hP.pullE_eq_closure_roots,
    hP.pullE_roots_ge⟩

end CFSG.EvenSporadicStandard.Fin76b
