module

public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving

variable {G : Type*} [Group G]

theorem list_complete [Finite G] {C : Subgroup G} {n : ℕ} (f : ℕ → G) (hfC : ∀ i < n, f i ∈ C)
    (hinj : ∀ i < n, ∀ j < i, f i ≠ f j) (hcard : Nat.card C ≤ n) :
    (∀ c ∈ C, ∃ i < n, f i = c) ∧ Nat.card C = n := by
  set F : Fin n → C := fun i => ⟨f i, hfC i i.2⟩ with hF
  have hFinj : Function.Injective F := by
    intro i j hij
    have hij' : f i = f j := congrArg Subtype.val hij
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact hinj j j.2 i h hij'.symm
    · exact hinj i i.2 j h hij'
  have hFbij : Function.Bijective F :=
    hFinj.bijective_of_nat_card_le (by rw [Nat.card_fin]; exact hcard)
  refine ⟨fun c hc => ?_, by rw [← Nat.card_eq_of_bijective F hFbij, Nat.card_fin]⟩
  obtain ⟨i, hi⟩ := hFbij.2 ⟨c, hc⟩
  exact ⟨i, i.2, congrArg Subtype.val hi⟩

theorem gLAPPrimeCoreOf_eq_bot_of_list [Finite G] {p : ℕ} (hp : p.Prime) {C : Subgroup G}
    {n m k : ℕ} (hn : n = p ^ k * m) (f : ℕ → G) (hfC : ∀ i < n, f i ∈ C)
    (hinj : ∀ i < n, ∀ j < i, f i ≠ f j) (hcard : Nat.card C ≤ n) (w : ℕ → List ℕ)
    (hwn : ∀ i < n, ∀ j ∈ w i, j < n)
    (hw : ∀ i < n, f i ≠ 1 → (f i * ((w i).map fun j => f j * f i * (f j)⁻¹).prod) ^ m ≠ 1) :
    GLAPPrimeCoreOf p C = ⊥ := by
  set N := GLAPPrimeCoreOf p C with hNdef
  set F : Fin n → C := fun i => ⟨f i, hfC i i.2⟩ with hF
  have hFinj : Function.Injective F := by
    intro i j hij
    have hij' : f i = f j := congrArg Subtype.val hij
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact hinj j j.2 i h hij'.symm
    · exact hinj i i.2 j h hij'
  have hFbij : Function.Bijective F :=
    hFinj.bijective_of_nat_card_le (by rw [Nat.card_fin]; exact hcard)
  have hcardC : Nat.card C = n := by
    rw [← Nat.card_eq_of_bijective F hFbij, Nat.card_fin]
  have hpow : ∀ y ∈ N, y ^ m = 1 := by
    intro y hy
    have h1 : orderOf y ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hy
    have h2 : Nat.card N ∣ p ^ k * m := hn ▸ hcardC ▸ Subgroup.card_dvd_of_le (GLAPPrimeCoreOf_le C)
    have h3 : Nat.Coprime (Nat.card N) (p ^ k) :=
      Nat.Coprime.pow_right k (coprime_card_GLAPPrimeCoreOf hp C).symm
    exact orderOf_dvd_iff_pow_eq_one.1 (h1.trans (h3.dvd_of_dvd_mul_left h2))
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  obtain ⟨i, hi⟩ := hFbij.2 ⟨y, GLAPPrimeCoreOf_le C hy⟩
  have hyi : f i = y := congrArg Subtype.val hi
  by_contra hne
  rw [← hyi] at hy hne
  apply hw i i.2 hne
  refine hpow _ (N.mul_mem hy (N.list_prod_mem fun x hx => ?_))
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  exact GLAPPrimeCoreOf_conj_mem (f j) (hfC j (hwn i i.2 j hj)) (f i) hy

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
