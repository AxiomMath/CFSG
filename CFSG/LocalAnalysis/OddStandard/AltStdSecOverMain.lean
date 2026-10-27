module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecOverSwap
public import CFSG.LocalAnalysis.OddStandard.AltStdSecOverBase
public import CFSG.LocalAnalysis.OddStandard.AltStdSecOverCent
public import CFSG.LocalAnalysis.OddStandard.AltStdSecSwapAssembly

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem centralizer_le_subStab_of_unique (hU : WreathPairUniqueAt n)
    (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) (hn : 11 ≤ n)
    {H : Subgroup G} (hH : WreathPair L z n H) :
    centralizer ({z} : Set G) ≤ subStab ({H, cjSub z H} : Set (Subgroup G)) := by
  intro x hx
  have hz2 := d.mul_self
  have hxz : x * z = z * x := mem_centralizer_singleton_iff.1 hx
  have hxL : cjSub x L = L :=
    cjSub_eq_of_mem_normalizer (AltStdBal.centralizer_le_normalizer h d hx)
  have hzx : x * z * x⁻¹ = z := by rw [hxz]; group
  have hH₂ : WreathPair L z n (cjSub x H) := by
    have := hH.conjugate x⁻¹
    simp only [inv_inv] at this
    have e1 : CFSG.conjugate L x⁻¹ = cjSub x L := by simp [CFSG.conjugate, cjSub]
    have e2 : CFSG.conjugate H x⁻¹ = cjSub x H := by simp [CFSG.conjugate, cjSub]
    rw [e1, e2, hzx, hxL] at this
    exact this
  have hne : H ≠ cjSub z H := hH.ne_cjSub (by omega)
  have hu := hU G L Q z h d hQ2 H _ hH hH₂
  rw [mem_subStab_pair_iff hne]
  have hxz' : cjSub x (cjSub z H) = cjSub z (cjSub x H) := by
    rw [← cjSub_mul, ← cjSub_mul, hxz]
  rcases hu with h1 | h1
  · left
    refine ⟨h1, ?_⟩
    rw [hxz', h1]
  · right
    have h1' : cjSub x H = cjSub z H := h1
    refine ⟨h1', ?_⟩
    rw [hxz', h1', ← cjSub_mul, hz2, cjSub_one]

theorem not_conj_of_pairChar_eq_one (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hn : 11 ≤ n) {H : Subgroup G} (hH : WreathPair L z n H)
    (hCz : Nat.card (centralizer ({z} : Set G)) = 2 * n.factorial)
    (w : subStab ({H, cjSub z H} : Set (Subgroup G)))
    (hw : pairChar H (cjSub z H) (hH.ne_cjSub (by omega)) w = 1) :
    ¬ ∃ g : G, g⁻¹ * z * g = (w : G) := by
  rintro ⟨g, hg⟩
  have hne : H ≠ cjSub z H := hH.ne_cjSub (by omega)
  have h1 : cjSub (w : G) H = H := (pairChar_eq_one_iff hne).1 hw
  have h2 : cjSub (w : G) (cjSub z H) = cjSub z H := by
    rcases (mem_subStab_pair_iff hne).1 w.2 with ⟨-, h2⟩ | ⟨h2, -⟩
    · exact h2
    · exact absurd (h1.symm.trans h2) hne
  rw [← hg] at h1 h2
  exact false_of_conj_fixes h d hQ2 hn hH g hCz h1 h2

theorem wreathOvergroup_of_unique (hU : WreathPairUniqueAt n)
    (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) (hn : 11 ≤ n) {u : G}
    (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q) (hu2 : u ^ 2 = 1)
    (e : L ≃* alternatingGroup (Fin n)) :
    ∀ H : Subgroup G, WreathPair L z n H →
      ∃ (M : Subgroup G) (hC : centralizer ({z} : Set G) ≤ M) (χ : M →* Multiplicative (ZMod 2)),
        (∀ g : G, g⁻¹ * z * g ∈ M → ∃ m ∈ M, g⁻¹ * z * g = m⁻¹ * z * m) ∧
          χ ⟨z, hC (mem_centralizer_singleton_iff.2 rfl)⟩ ≠ 1 := by
  intro H hH
  have hne : H ≠ cjSub z H := hH.ne_cjSub (by omega)
  have hCz := card_centralizer_eq_two_mul_factorial h d hQ2 hu huL hu2 e
  have hC := centralizer_le_subStab_of_unique hU h d hQ2 hn hH
  refine ⟨subStab ({H, cjSub z H} : Set (Subgroup G)), hC, pairChar H (cjSub z H) hne, ?_, ?_⟩
  · intro g hg
    have hg' := (mem_subStab_pair_iff hne).1 hg
    rcases hg' with ⟨hg1, hg2⟩ | ⟨hg1, hg2⟩
    · exact (false_of_conj_fixes h d hQ2 hn hH g hCz hg1 hg2).elim
    · exact ⟨g, mem_subStab_of_swap_of_unique hU h d hQ2 hn hH hg1 hg2, rfl⟩
  · intro h1
    have h2 := (pairChar_eq_one_iff hne).1 h1
    exact hH.cjSub_ne (by omega) h2

theorem wreathOvergroup (htri : ExactShapeTrichotomy)
    (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) (hn : 12 ≤ n) {u : G}
    (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q) (hu2 : u ^ 2 = 1)
    (e : L ≃* alternatingGroup (Fin n)) :
    ∀ H : Subgroup G, WreathPair L z n H →
      ∃ (M : Subgroup G) (hC : centralizer ({z} : Set G) ≤ M) (χ : M →* Multiplicative (ZMod 2)),
        (∀ g : G, g⁻¹ * z * g ∈ M → ∃ m ∈ M, g⁻¹ * z * g = m⁻¹ * z * m) ∧
          χ ⟨z, hC (mem_centralizer_singleton_iff.2 rfl)⟩ ≠ 1 :=
  wreathOvergroup_of_unique (wreathPairUniqueAt_of_tri htri hn) h d hQ2 (by omega) hu huL hu2 e

theorem false_of_shapeTwo_of_dichotomy_of_unique (hU : WreathPairUniqueAt n)
    (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) (hn : 11 ≤ n) {u : G}
    (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q) (hu2 : u ^ 2 = 1)
    (e : L ≃* alternatingGroup (Fin n))
    (hdich : CaseII e h.hn (L ⊔ zpowers u) z ∨ CaseII e h.hn (L ⊔ zpowers (u * z)) z ∨
      ∃ H : Subgroup G, WreathPair L z n H) : False :=
  false_of_shapeTwo_of_wreath h d hQ2 hu huL hu2 e hdich
    (wreathOvergroup_of_unique hU h d hQ2 hn hu huL hu2 e)

theorem false_of_shapeTwo_of_dichotomy (htri : ExactShapeTrichotomy)
    (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) (hn : 12 ≤ n) {u : G}
    (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q) (hu2 : u ^ 2 = 1)
    (e : L ≃* alternatingGroup (Fin n))
    (hdich : CaseII e h.hn (L ⊔ zpowers u) z ∨ CaseII e h.hn (L ⊔ zpowers (u * z)) z ∨
      ∃ H : Subgroup G, WreathPair L z n H) : False :=
  false_of_shapeTwo_of_wreath h d hQ2 hu huL hu2 e hdich
    (wreathOvergroup htri h d hQ2 hn hu huL hu2 e)

end CFSG.OddStandard.AltStdSec
