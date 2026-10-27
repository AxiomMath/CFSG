module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Lemma36Top
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.LitCompBInner
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.LayerBalanceAt

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction

section Trichotomy

variable {G : Type} [Group G] [Finite G] {n : ℕ} {U T : ℕ → Subgroup G} {s : ℕ → G} {u x : G}

theorem oddCore_eq_bot_of_isSimpleGroup (hs : IsSimpleGroup G) {t : G} (ht : orderOf t = 2) :
    CFSG.oddCore G = ⊥ := by
  haveI : (CFSG.oddCore G).Normal := inferInstance
  rcases hs.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with h | h
  · exact h
  · exfalso
    have hodd := odd_card_oddCore' G
    rw [h, Subgroup.card_top] at hodd
    have h2 : 2 ∣ Nat.card G := ht ▸ orderOf_dvd_natCard t
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

theorem TopData.trichotomy_of_layerBalance (hLB : Induction.Junction.LayerBalanceKAt G)
    (hD : TopData G n U T s u x) :
    IsCompIn (U (n - 2)) (centralizer ((zpowers x : Subgroup G) : Set G)) ∨
    (∃ K₀, IsCompIn K₀ (centralizer ((zpowers x : Subgroup G) : Set G)) ∧ K₀ ≠ U (n - 2) ∧
      K₀ = K₀.map (MulAut.conj u).toMonoidHom ∧ U (n - 2) ≤ K₀ ∧
      K₀ = conjClosure (U (n - 2)) (layerIn (centralizer ((zpowers x : Subgroup G) : Set G)))) ∨
    (∃ I, IsCompIn I (centralizer ((zpowers x : Subgroup G) : Set G)) ∧
      Sol78Link5a I (U (n - 2)) u ∧ U (n - 2) ≤ I ⊔ I.map (MulAut.conj u).toMonoidHom ∧
      I ⊔ I.map (MulAut.conj u).toMonoidHom =
        conjClosure (U (n - 2)) (layerIn (centralizer ((zpowers x : Subgroup G) : Set G)))) := by
  have hOu := hD.out
  have hxt : x ∈ centralizer ({u} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hOu.mem x hD.xmem)
  have hzx : centralizer ((zpowers x : Subgroup G) : Set G) = centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hux' : u ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hxt).symm
  have hux : u ∈ normalizer ((zpowers x : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ (by rw [hzx]; exact hux')
  have hu2 : u ^ 2 ∈ zpowers x := by
    rw [sq_eq_one_of_orderOf_eq_two hOu.inv]
    exact one_mem _
  have hKc : IsCompIn (U (n - 2)) (centralizer ((zpowers x ⊔ zpowers u : Subgroup G) : Set G)) := by
    rw [sup_comm, hD.jstar]
    exact isCompIn_jOf hD.facts hxt hD.xinv
  have hS2 : IsPGroup 2 ↥(zpowers x ⊔ zpowers u) :=
    isPGroup_sup_zpowers (isPGroup_zpowers_of_orderOf_eq_two hD.xinv) hux hu2
  have hSle : zpowers x ⊔ zpowers u ≤ centralizer ({x} : Set G) :=
    sup_le (Subgroup.zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
      (Subgroup.zpowers_le.2 hux')
  have hKL : U (n - 2) ≤ layerIn (centralizer ((zpowers x : Subgroup G) : Set G)) :=
    hLB hOu.std.kProper (oddCore_eq_bot_of_isSimpleGroup hOu.std.simple hOu.inv)
      (zpowers x ⊔ zpowers u) x hS2 hD.xinv
      ((le_sup_left : zpowers x ≤ zpowers x ⊔ zpowers u) (Subgroup.mem_zpowers x))
      (fun y hy => mem_centralizer_singleton_iff.1 (hSle hy)) (U (n - 2)) hKc
  rcases pumpUp_trichotomy hux hu2 hKc hKL with hK | ⟨M, hM, hMK, hlink, hle, hcl⟩
  · exact Or.inl hK
  · rcases hlink with hMu | h5a
    · refine Or.inr (Or.inl ⟨M, hM, hMK, hMu, ?_, ?_⟩)
      · rwa [← hMu, sup_idem] at hle
      · rwa [← hMu, sup_idem] at hcl
    · exact Or.inr (Or.inr ⟨M, hM, h5a, hle, hcl⟩)

end Trichotomy

section TrichotomyUgt


variable {G : Type} [Group G] [Finite G] {n : ℕ} {U T : ℕ → Subgroup G} {s : ℕ → G} {u x : G}

theorem TopData.trichotomy (hUG : Induction.Balance.UHered G)
    (hD : TopData G n U T s u x) :
    IsCompIn (U (n - 2)) (centralizer ((zpowers x : Subgroup G) : Set G)) ∨
    (∃ K₀, IsCompIn K₀ (centralizer ((zpowers x : Subgroup G) : Set G)) ∧ K₀ ≠ U (n - 2) ∧
      K₀ = K₀.map (MulAut.conj u).toMonoidHom ∧ U (n - 2) ≤ K₀ ∧
      K₀ = conjClosure (U (n - 2)) (layerIn (centralizer ((zpowers x : Subgroup G) : Set G)))) ∨
    (∃ I, IsCompIn I (centralizer ((zpowers x : Subgroup G) : Set G)) ∧
      Sol78Link5a I (U (n - 2)) u ∧ U (n - 2) ≤ I ⊔ I.map (MulAut.conj u).toMonoidHom ∧
      I ⊔ I.map (MulAut.conj u).toMonoidHom =
        conjClosure (U (n - 2)) (layerIn (centralizer ((zpowers x : Subgroup G) : Set G)))) :=
  hD.trichotomy_of_layerBalance
    (Induction.Junction.layerBalanceKAt_of_lemma15At (Induction.fs79Lemma15At_of_uhered G hUG))

end TrichotomyUgt

end CFSG.EvenSporadicStandard.M12Std.Rbc
