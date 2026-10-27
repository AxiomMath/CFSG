module

public import CFSG.ClassicalInvolution.Orders.Classical
public import CFSG.ClassicalInvolution.Orders.Twisted
public import CFSG.ClassicalInvolution.Orders.Ree

public section

namespace CFSG.ClassicalInvolution

open CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank

theorem ordA_mem_lieOrdersOver {n q : ℕ} (hn : 1 ≤ n) : ordA n q ∈ lieOrdersOver q :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨n, hn, rfl⟩))))

theorem ordTwistedA_mem_lieOrdersOver {n q : ℕ} (hn : 2 ≤ n) :
    ordTwistedA n q ∈ lieOrdersOver q :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨n, hn, rfl⟩))))

theorem ordBC_mem_lieOrdersOver {n q : ℕ} (hn : 2 ≤ n) : ordBC n q ∈ lieOrdersOver q :=
  Or.inl (Or.inl (Or.inl (Or.inr ⟨n, hn, rfl⟩)))

theorem ordD_mem_lieOrdersOver {n q : ℕ} (hn : 4 ≤ n) : ordD n q ∈ lieOrdersOver q :=
  Or.inl (Or.inl (Or.inr ⟨n, hn, rfl⟩))

theorem ordTwistedD_mem_lieOrdersOver {n q : ℕ} (hn : 4 ≤ n) :
    ordTwistedD n q ∈ lieOrdersOver q :=
  Or.inl (Or.inr ⟨n, hn, rfl⟩)

theorem mem_lieOrdersChar_of_mem_lieOrdersOver {p f m : ℕ} (hf : 1 ≤ f)
    (h : m ∈ lieOrdersOver (p ^ f)) : m ∈ lieOrdersChar p :=
  Or.inl (Or.inl (Or.inl ⟨f, hf, h⟩))

theorem card_mem_lieOrdersChar_of_oddLieType {X : Type} [Group X] (h : OddLieType X) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card X ∈ lieOrdersChar p := by
  obtain ⟨t, n, p, f, hp, hp2, hadm, hmodel⟩ := h
  refine ⟨p, hp, hp2, ?_⟩
  have hf : 1 ≤ f := hadm.2.1
  rcases hmodel with ⟨-, hc⟩ | ⟨-, ht, he⟩ | ⟨-, ht, hr⟩ | ⟨-, rfl, -⟩
  ·
    have hcard := card_statedClassicalModel_of_ne_two hp2 hc
    apply mem_lieOrdersChar_of_mem_lieOrdersOver hf
    cases t
    case PSL =>
      obtain ⟨⟨-, -, hn, -, -⟩, -⟩ := hc
      rw [hcard.1 rfl]
      exact ordA_mem_lieOrdersOver (by omega)
    case PSU =>
      obtain ⟨⟨-, -, hn, -⟩, -⟩ := hc
      rw [hcard.2.1 rfl]
      exact ordTwistedA_mem_lieOrdersOver (by omega)
    case PSp =>
      obtain ⟨⟨-, -, hn, -⟩, -⟩ := hc
      rw [hcard.2.2.1 rfl]
      exact ordBC_mem_lieOrdersOver hn
    case POmegaOdd =>
      obtain ⟨⟨-, -, hn, -⟩, -⟩ := hc
      rw [hcard.2.2.2.1 rfl]
      exact ordBC_mem_lieOrdersOver (by omega)
    case POmegaPlus =>
      obtain ⟨⟨-, -, hn⟩, -⟩ := hc
      rw [hcard.2.2.2.2.1 rfl]
      exact ordD_mem_lieOrdersOver hn
    case POmegaMinus =>
      obtain ⟨⟨-, -, hn⟩, -⟩ := hc
      rw [hcard.2.2.2.2.2 rfl]
      exact ordTwistedD_mem_lieOrdersOver hn
    all_goals exact (hc.2 : False).elim
  ·
    have hcard := card_chevalleyExceptionalModel_of_ne_two hp2 he
    apply mem_lieOrdersChar_of_mem_lieOrdersOver hf
    cases t
    case G2 =>
      rw [hcard]
      simp [lieOrdersOver]
    case F4 =>
      rw [hcard]
      simp [lieOrdersOver]
    case E6 =>
      rw [hcard]
      simp [lieOrdersOver]
    case E7 =>
      rw [hcard]
      simp [lieOrdersOver]
    case E8 =>
      rw [hcard]
      simp [lieOrdersOver]
    case twistedE6 =>
      rw [hcard]
      simp [lieOrdersOver]
    case trialityD4 =>
      rw [hcard]
      simp [lieOrdersOver]
    all_goals exact absurd ht (by decide)
  ·
    cases t
    case twistedG2 =>
      obtain ⟨hp3, a, ha, hfa, hcard⟩ := card_of_reeTitsModel_twistedG2 hr
      subst hp3
      exact Or.inl (Or.inr ⟨rfl, a, ha, by rw [hcard, hfa]⟩)
    case twistedF4 => exact absurd hadm.2.2.2.1 hp2
    case Tits => exact absurd hadm.2.2.2.1 hp2
    all_goals exact absurd ht (by decide)
  ·
    exact absurd hadm.2.2.2.1 hp2

end CFSG.ClassicalInvolution
