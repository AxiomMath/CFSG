module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixDefs

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.SignalizerFunctor.Helpers
open CFSG.Open
open scoped Pointwise commutatorElement

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem commutator_le_of_le_normalizer {T L : Subgroup X}
    (hTL : T ≤ Subgroup.normalizer (L : Set X)) : ⁅T, L⁆ ≤ L := by
  rw [Subgroup.commutator_le]
  intro t ht l hl
  rw [commutatorElement_def]
  exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTL ht) l).mp hl) (L.inv_mem hl)

omit [Finite X] in
theorem inf_le_commutator_of_mem {G T L : Subgroup X} (hF : Frame G T) {n : X} (hn : n ∈ L)
    (hLG : L ≤ G) (hTL : T ≤ Subgroup.normalizer (L : Set X))
    (hN : rightConjugate T n ≤ Subgroup.normalizer (T : Set X)) :
    (T ⊔ rightConjugate T n) ⊓ G ≤ ⁅T, L⁆ := by
  rintro w ⟨hw, hwG⟩
  have hwm : w ∈ (T : Set X) * (rightConjugate T n : Set X) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left T _ hN]
    exact hw
  obtain ⟨t, ht, k, hk, rfl⟩ := Set.mem_mul.mp hwm
  have hk' : n * k * n⁻¹ ∈ T := (mem_rightConjugate_iff T n k).mp hk
  set t' := n * k * n⁻¹ with ht'
  have hcomm : t'⁻¹ * n⁻¹ * t' * n ∈ ⁅T, L⁆ := by
    have := Subgroup.commutator_mem_commutator (T.inv_mem hk') (L.inv_mem hn)
    simpa [commutatorElement_def] using this
  have hTLG : ⁅T, L⁆ ≤ G := (commutator_le_of_le_normalizer hTL).trans hLG
  have hkeq : k = t' * (t'⁻¹ * n⁻¹ * t' * n) := by rw [ht']; group
  have htt : t * t' ∈ T ⊓ G := by
    refine ⟨T.mul_mem ht hk', ?_⟩
    have h1 : t * k ∈ G := hwG
    rw [hkeq, ← mul_assoc] at h1
    have h2 := G.mul_mem h1 (G.inv_mem (hTLG hcomm))
    rwa [mul_inv_cancel_right] at h2
  rw [hF.inf_eq_bot, Subgroup.mem_bot] at htt
  rw [hkeq, ← mul_assoc, htt, one_mul]
  exact hcomm

namespace Conf46

variable {G T S Q H : Subgroup X} {g : X}

theorem hyp43_sub (c : Conf46 G T S Q H g) {L : Subgroup X} (hLG : L ≤ G) :
    Hyp43 L T (Q ⊓ (L ⊔ T)) (H ⊓ (L ⊔ T)) where
  le := inf_le_inf_right _ c.hyp43.le
  le_normalizer := fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨c.hyp43.le_normalizer hx.1, Subgroup.le_normalizer hx.2⟩
  le_sup := inf_le_right
  sylow := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact c.hyp43.sylow.of_le (le_inf c.hyp43.le_Q le_sup_right) inf_le_left
  inf_eq_bot := fun n hn hnH => by
    have hnH' : n ∉ H := fun h => hnH ⟨h, Subgroup.mem_sup_left hn⟩
    exact c.hyp43.inf_eq_bot n (hLG hn) hnH'

theorem exists_conf_T (c : Conf46 G T S Q H g) {L S₀ : Subgroup X}
    (hLG : L ≤ G) (hTN : T ≤ Subgroup.normalizer (L : Set X))
    (hS₀ : IsSylowOf 2 S₀ (L ⊔ T)) (hS₀S : S₀ ≤ S) :
    ∃ S₁ : Subgroup X, SylowFrame L T S₁ ∧ ∃ y ∈ L ⊔ T, ∃ n ∈ L,
      relativeWeakClosure L T S₁ = T ⊔ rightConjugate T n ∧
      rightConjugate T n ≤ Subgroup.normalizer (T : Set X) ∧
      (relativeWeakClosure L T S₁ = T ∨
        relativeWeakClosure L T S₁ = rightConjugate (T ⊔ rightConjugate T g) y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := T ⊔ rightConjugate T g with hWdef
  have hWab : IsMulCommutative W := c.isMulCommutative_W
  have hWS : relativeWeakClosure G T S = W := c.weakClosure
  have hF₁ : Frame L T := ⟨hTN, by
    rw [eq_bot_iff, ← c.frame.inf_eq_bot]; exact inf_le_inf_left T hLG,
    c.frame.isPGroup⟩
  obtain ⟨S₁, hS₁⟩ := hF₁.exists_sylowFrame
  have hTS₁ : T ≤ S₁ := hS₁.le
  obtain ⟨y, hyL, hy⟩ := exists_rightConjugate_eq_of_isSylowOf hS₁.sylow hS₀
  refine ⟨S₁, hS₁, y, hyL, ?_⟩
  have hkey : ∀ x ∈ L ⊔ T, rightConjugate T x ≤ S₁ →
      rightConjugate T x ≤ rightConjugate W y := by
    intro x hx hle
    have hxy : x * y⁻¹ ∈ L ⊔ T := (L ⊔ T).mul_mem hx ((L ⊔ T).inv_mem hyL)
    obtain ⟨t, ht, h, hh, -, hrc⟩ := hF₁.exists_rightConjugate_eq hxy
    have hS₀eq : rightConjugate S₁ y⁻¹ = S₀ := by
      rw [← hy, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
    have h1 : rightConjugate T (x * y⁻¹) ≤ S₀ := by
      rw [← rightConjugate_mul, ← hS₀eq]
      exact rightConjugate_le_rightConjugate hle y⁻¹
    rw [hrc] at h1
    have h3 : rightConjugate T h ≤ W := by
      rw [← hWS]
      exact rightConjugate_le_relativeWeakClosure (hLG hh) (h1.trans hS₀S)
    rw [← hrc] at h3
    have h4 := rightConjugate_le_rightConjugate h3 y
    rwa [rightConjugate_mul, inv_mul_cancel_right] at h4
  have hW₁W : relativeWeakClosure L T S₁ ≤ rightConjugate W y := by
    rw [relativeWeakClosure_le_iff]
    exact fun x hx hle => hkey x (Subgroup.mem_sup_left hx) hle
  by_cases hall : ∀ n ∈ L, rightConjugate T n ≤ S₁ → rightConjugate T n = T
  · have hW₁ : relativeWeakClosure L T S₁ = T := by
      apply le_antisymm _ (subgroup_le_relative_weak_closure _ _ _ hTS₁)
      rw [relativeWeakClosure_le_iff]
      exact fun x hx hle => (hall x hx hle).le
    refine ⟨1, L.one_mem, ?_, ?_, Or.inl hW₁⟩
    · rw [rightConjugate_one, sup_idem, hW₁]
    · rw [rightConjugate_one]
      exact Subgroup.le_normalizer
  · push Not at hall
    obtain ⟨n, hn, hle, hne⟩ := hall
    have hTW : T ≤ rightConjugate W y := hkey 1 (Subgroup.one_mem _) (by
      rw [rightConjugate_one]; exact hTS₁) |>.trans' (by rw [rightConjugate_one])
    have hTnW : rightConjugate T n ≤ rightConjugate W y := hkey n (Subgroup.mem_sup_left hn) hle
    have hWyab : IsMulCommutative (rightConjugate W y) := isMulCommutative_rightConjugate hWab y
    have hTnN : rightConjugate T n ≤ Subgroup.normalizer (T : Set X) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro x hx
      exact Subgroup.mem_centralizer_iff.mpr fun t ht => congrArg Subtype.val
        (hWyab.is_comm.comm ⟨t, hTW ht⟩ ⟨x, hTnW hx⟩)
    have hinf : T ⊓ rightConjugate T n = ⊥ := by
      by_contra hne'
      have hnH : n ∈ H := c.hyp43.mem_of_inf_ne_bot (hLG hn) hne'
      have hle₂ : T ⊔ rightConjugate T n ≤ Q := by
        refine sup_le c.hyp43.le_Q ?_
        have h1 := rightConjugate_le_rightConjugate c.hyp43.le_Q n
        rwa [(rightConjugate_eq_self_iff Q n).mpr (c.hyp43.le_normalizer hnH)] at h1
      have h2 : IsPGroup 2 (T ⊔ rightConjugate T n : Subgroup X) :=
        c.frame.isPGroup.to_sup_of_normal_left' (isPGroup_rightConjugate c.frame.isPGroup n)
          hTnN
      have hcard := card_le_of_isSylowOf c.hyp43.sylow h2 hle₂
      have heq : T ⊔ rightConjugate T n = rightConjugate T n :=
        (Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [rightConjugate_card]; exact hcard)).symm
      apply hne
      exact (Subgroup.eq_of_le_of_card_ge (heq ▸ le_sup_left) (by rw [rightConjugate_card])).symm
    have hcardTT : Nat.card (T ⊔ rightConjugate T n : Subgroup X) = Nat.card T * Nat.card T := by
      rw [card_sup_of_le_normalizer hTnN hinf, rightConjugate_card]
    have hWy : rightConjugate W y = T ⊔ rightConjugate T n := by
      refine (Subgroup.eq_of_le_of_card_ge (sup_le hTW hTnW) ?_).symm
      rw [rightConjugate_card, hcardTT, c.hyp45.card_W]
    have hW₁ : relativeWeakClosure L T S₁ = rightConjugate W y := by
      apply le_antisymm hW₁W
      rw [hWy]
      exact sup_le (subgroup_le_relative_weak_closure _ _ _ hTS₁)
        (rightConjugate_le_relativeWeakClosure hn hle)
    refine ⟨n, hn, ?_, hTnN, Or.inr hW₁⟩
    rw [hW₁, hWy]

theorem sub_T (c : Conf46 G T S Q H g) (IH : IH46 (Nat.card (G ⊔ T : Subgroup X)))
    {L S₀ : Subgroup X} (hLG : L ≤ G) (hTN : T ≤ Subgroup.normalizer (L : Set X))
    (hS₀ : IsSylowOf 2 S₀ (L ⊔ T)) (hS₀S : S₀ ≤ S)
    (hcard : Nat.card (L ⊔ T : Subgroup X) < Nat.card (G ⊔ T : Subgroup X))
    (hOL : CFSG.oddCore L = ⊥) :
    ⁅L, T⁆ = ⊥ ∨
    (∃ y ∈ L ⊔ T, L ≤ Subgroup.normalizer
        (rightConjugate (T ⊔ rightConjugate T g) y : Set X) ∧
      rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) y ≤ L) ∨
    (∃ y ∈ L ⊔ T, ∃ S₁ : Subgroup X, Bender46 L T S₁ ∧
      relativeWeakClosure L T S₁ = rightConjugate (T ⊔ rightConjugate T g) y ∧
      rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) y ≤ ⁅T, L⁆) := by
  obtain ⟨S₁, hS₁, y, hyL, n, hn, hW₁eq, hnN, hcases⟩ := c.exists_conf_T hLG hTN hS₀ hS₀S
  have h43₁ := c.hyp43_sub hLG
  rcases hcases with hW₁T | hW₁W
  ·
    left
    have h := lemma_4_2_oddCore ⟨hS₁.toFrame, hS₁.sylow, hS₁.le, fun x hx hle =>
      Subgroup.eq_of_le_of_card_ge
        ((rightConjugate_le_relativeWeakClosure hx hle).trans hW₁T.le)
        (by rw [rightConjugate_card])⟩
    rwa [hOL, Subgroup.map_bot, le_bot_iff] at h
  ·
    have hGy : rightConjugate G y = G := (rightConjugate_eq_self_iff G y).mpr
      ((sup_le Subgroup.le_normalizer c.frame.le_normalizer) (sup_le_sup_right hLG T hyL))
    have hZy : rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) y ≤ ⁅T, L⁆ := by
      rw [rightConjugate_inf, hGy, ← hW₁W, hW₁eq]
      exact inf_le_commutator_of_mem c.frame hn hLG hTN hnN
    rcases IH X L T S₁ _ _ n hcard hS₁ h43₁ c.ne_bot hOL hn hW₁eq hnN with hm | hN | hB
    · exfalso
      have := c.pRank_lt
      omega
    · right; left
      refine ⟨y, hyL, ?_, hZy.trans (commutator_le_of_le_normalizer hTN)⟩
      rw [← hW₁W]
      exact le_sup_left.trans hN
    · right; right
      exact ⟨y, hyL, S₁, hB, hW₁W, hZy⟩

end Conf46

end CFSG.ComponentClassification.AschbacherTheorem3
