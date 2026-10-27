module

public import CFSG.ClassicalInvolution.Phan.Coherent
public import CFSG.Timmesfeld.RankTwo.LevisSpin

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg
open CFSG.Timmesfeld (edgeD)

theorem edgeD_iff_of_four_le {n : ℕ} (hn : 4 ≤ n) (i j : Fin n) :
    edgeD n i j ↔
      (i.val + 1 = j.val ∧ j.val + 1 < n) ∨ (i.val = n - 3 ∧ j.val = n - 1) := by
  unfold edgeD
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega⟩

theorem edgeD_lt {n : ℕ} (hn : 4 ≤ n) {i j : Fin n} (h : edgeD n i j) : i < j := by
  rcases (edgeD_iff_of_four_le hn i j).1 h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact Fin.lt_def.2 (by omega)
  · exact Fin.lt_def.2 (by omega)

theorem edgeD_irrefl (n : ℕ) (i : Fin n) : ¬ edgeD n i i := by
  unfold edgeD
  omega

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

variable (K p f) in
structure PhanFamilyD (n : ℕ) (Y : Type) [Group Y] where
  ι : Fin n → (Su K p f 2 →* Y)
  θ : ∀ i j : Fin n, edgeD n i j → (Su K p f 3 →* Y)
  left : ∀ (i j : Fin n) (h : edgeD n i j),
    (θ i j h).comp (embSUid (unitaryInvolution K p f) 2) = ι i
  right : ∀ (i j : Fin n) (h : edgeD n i j),
    (θ i j h).comp (embSUid (unitaryInvolution K p f) 0) = ι j
  comm : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
    ∀ a b, ι i a * ι j b = ι j b * ι i a

theorem exists_family {n : ℕ} (hn : 4 ≤ n) (hK : Nat.card K = (p ^ f) ^ 2) {X : Type}
    [Group X] (U : Fin n → Subgroup X) (W : Fin n → Fin n → Subgroup X)
    (hcomm : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, edgeD n i j →
      UnitaryBlockStandardPair K p f (W i j) (U i) (U j)) :
    ∃ F : PhanFamilyD K p f n X, (∀ i, (F.ι i).range = U i) ∧
      (∀ i, Function.Injective (F.ι i)) ∧
      (∀ i j (h : edgeD n i j), (F.θ i j h).ker ≤ Subgroup.center (Su K p f 3)) ∧
      ∀ i j (h : edgeD n i j), (F.θ i j h).range = W i j := by
  classical
  let u : ℕ → Subgroup X := fun i => if h : i < n then U ⟨i, h⟩ else ⊥
  have hu : ∀ (i : ℕ) (h : i < n), u i = U ⟨i, h⟩ := fun i h => dif_pos h
  let Wf : (i : ℕ) → i + 2 < n → Subgroup X := fun i h =>
    W ⟨i, by omega⟩ ⟨i + 1, by omega⟩
  let w : ℕ → Subgroup X := fun i => if h : i + 2 < n then Wf i h else ⊥
  have hw : ∀ (i : ℕ) (h : i + 2 < n), w i = Wf i h := fun i h => dif_pos h
  have hWf : ∀ (i : ℕ) (h : i + 2 < n),
      UnitaryBlockStandardPair K p f (Wf i h) (u i) (u (i + 1)) := by
    intro i h
    have h1 : i < n := by omega
    have h2 : i + 1 < n := by omega
    rw [hu i h1, hu (i + 1) h2]
    exact hpair ⟨i, by omega⟩ ⟨i + 1, by omega⟩ (by
      unfold edgeD
      left
      constructor
      · rfl
      · dsimp only
        omega)
  obtain ⟨θc, hθc⟩ := coherent_chain hK (autExtends hK) u w (n - 2)
    (fun i hi => by
      have h0 : i + 2 < n := by omega
      rw [hw i h0]
      exact hWf i h0)
    (fun i hi => by
      have h1 : i < n := by omega
      have h2 : i + 2 < n := by omega
      rw [hu i h1, hu (i + 2) h2]
      exact hcomm ⟨i, by omega⟩ ⟨i + 2, by omega⟩
        (by
          intro e
          have h := congrArg Fin.val e
          dsimp only at h
          omega)
        (by
          unfold edgeD
          dsimp only
          omega)
        (by
          unfold edgeD
          dsimp only
          omega))
  let Wlast : Subgroup X := W ⟨n - 3, by omega⟩ ⟨n - 1, by omega⟩
  have hWlast : UnitaryBlockStandardPair K p f Wlast (u (n - 3)) (u (n - 1)) := by
    rw [hu (n - 3) (by omega), hu (n - 1) (by omega)]
    exact hpair ⟨n - 3, by omega⟩ ⟨n - 1, by omega⟩ (by
      unfold edgeD
      right
      constructor
      · dsimp only
        omega
      · dsimp only
        omega)
  obtain ⟨θ', hr', hk', h12', h23'⟩ := pair_normalize hWlast
  obtain ⟨hk₄, -, h12₄, h23₄, hcomp₄⟩ := hθc (n - 4) (by omega)
  have h23₄' : (B23 K p f).map (θc (n - 4)) = u (n - 3) := by
    rw [h23₄, show n - 4 + 1 = n - 3 from by omega]
  have hglue : (B23 K p f).map (θc (n - 4)) = (B12 K p f).map θ' :=
    h23₄'.trans h12'.symm
  have hcomm_last : ∀ x ∈ (B12 K p f).map (θc (n - 4)), ∀ y ∈ (B23 K p f).map θ',
      x * y = y * x := by
    intro x hx y hy
    rw [h12₄] at hx
    rw [hu (n - 4) (by omega)] at hx
    rw [h23'] at hy
    rw [hu (n - 1) (by omega)] at hy
    exact hcomm ⟨n - 4, by omega⟩ ⟨n - 1, by omega⟩
      (by
        intro e
        have h := congrArg Fin.val e
        dsimp only at h
        omega)
      (by
        unfold edgeD
        dsimp only
        omega)
      (by
        unfold edgeD
        dsimp only
        omega) x hx y hy
  obtain ⟨θ₂, hk₂, hr₂, hb12₂, hb23₂, hcomp₂⟩ :=
    exists_glue hK (autExtends hK) hk₄ hk' hglue hcomm_last
  have hWlast_range : θ₂.range = Wlast := hr₂.trans hr'
  let iota : Fin n → (Su K p f 2 →* X) := fun i =>
    if h : i.val + 2 < n then (θc i.val).comp (embSUid (unitaryInvolution K p f) 2)
    else if hi : i.val = n - 2 then (θc (n - 3)).comp (embSUid (unitaryInvolution K p f) 0)
    else θ₂.comp (embSUid (unitaryInvolution K p f) 0)
  have hiota_chain : ∀ i : Fin n, i.val + 2 < n →
      iota i = (θc i.val).comp (embSUid (unitaryInvolution K p f) 2) := by
    intro i h
    simp only [iota, dif_pos h]
  have hiota_penult : ∀ i : Fin n, ¬ i.val + 2 < n → i.val = n - 2 →
      iota i = (θc (n - 3)).comp (embSUid (unitaryInvolution K p f) 0) := by
    intro i h hi
    simp only [iota, dif_neg h, dif_pos hi]
  have hiota_last : ∀ i : Fin n, ¬ i.val + 2 < n → i.val ≠ n - 2 →
      iota i = θ₂.comp (embSUid (unitaryInvolution K p f) 0) := by
    intro i h hi
    simp only [iota, dif_neg h, dif_neg hi]
  have hrange : ∀ i : Fin n, (iota i).range = U i := by
    intro i
    by_cases h : i.val + 2 < n
    · have hiN : i.val < n - 2 := by omega
      obtain ⟨hk, -, h12, h23, -⟩ := hθc i.val hiN
      obtain ⟨-, hr, -, -⟩ := pair_block_inj hK hk h12 h23
      rw [hiota_chain i h, hr, hu i.val i.isLt]
    · by_cases hi : i.val = n - 2
      · have hN : n - 3 < n - 2 := by omega
        obtain ⟨hk, -, h12, h23, -⟩ := hθc (n - 3) hN
        obtain ⟨-, -, -, hr⟩ := pair_block_inj hK hk h12 h23
        rw [hiota_penult i h hi, hr, show n - 3 + 1 = n - 2 from by omega,
          show n - 2 = i.val from hi.symm, hu i.val i.isLt]
      · have hi' : i.val = n - 1 := by omega
        obtain ⟨-, -, -, hr⟩ := pair_block_inj hK hk₂ hb12₂ hb23₂
        rw [hiota_last i h (by omega), hr, h23', show n - 1 = i.val from hi'.symm,
          hu i.val i.isLt]
  have hinj : ∀ i : Fin n, Function.Injective (iota i) := by
    intro i
    by_cases h : i.val + 2 < n
    · have hiN : i.val < n - 2 := by omega
      obtain ⟨hk, -, h12, h23, -⟩ := hθc i.val hiN
      obtain ⟨hin, -, -, -⟩ := pair_block_inj hK hk h12 h23
      rw [hiota_chain i h]
      exact hin
    · by_cases hi : i.val = n - 2
      · have hN : n - 3 < n - 2 := by omega
        obtain ⟨hk, -, h12, h23, -⟩ := hθc (n - 3) hN
        obtain ⟨-, -, hin, -⟩ := pair_block_inj hK hk h12 h23
        rw [hiota_penult i h hi]
        exact hin
      · obtain ⟨-, -, hin, -⟩ := pair_block_inj hK hk₂ hb12₂ hb23₂
        rw [hiota_last i h (by omega)]
        exact hin
  let theta : ∀ i j : Fin n, edgeD n i j → (Su K p f 3 →* X) := fun i j _ =>
    if hc : i.val + 1 = j.val ∧ j.val + 1 < n then θc i.val else θ₂
  have htheta_chain : ∀ (i j : Fin n) (h : edgeD n i j),
      i.val + 1 = j.val → j.val + 1 < n → theta i j h = θc i.val := by
    intro i j h h1 h2
    simp only [theta, dif_pos (show i.val + 1 = j.val ∧ j.val + 1 < n from ⟨h1, h2⟩)]
  have htheta_fork : ∀ (i j : Fin n) (h : edgeD n i j),
      ¬ (i.val + 1 = j.val ∧ j.val + 1 < n) → theta i j h = θ₂ := by
    intro i j h hc
    simp only [theta, dif_neg hc]
  have hleft : ∀ (i j : Fin n) (h : edgeD n i j),
      (theta i j h).comp (embSUid (unitaryInvolution K p f) 2) = iota i := by
    intro i j h
    rcases h with hc | ⟨h1, h2⟩
    · have hci : iota i = (θc i.val).comp (embSUid (unitaryInvolution K p f) 2) :=
        hiota_chain i (by omega)
      rw [htheta_chain i j (Or.inl hc) hc.1 hc.2, hci]
    · have hcf : ¬ (i.val + 1 = j.val ∧ j.val + 1 < n) := by
        rintro ⟨e1, e2⟩
        omega
      have hi : i.val = n - 3 := by omega
      have hci : iota i = (θc (n - 3)).comp (embSUid (unitaryInvolution K p f) 2) := by
        rw [hiota_chain i (by omega)]
        rw [hi]
      rw [htheta_fork i j (Or.inr ⟨h1, h2⟩) hcf, hci, hcomp₂]
      have hc4 := hcomp₄ (show n - 4 + 1 < n - 2 by omega)
      rw [show n - 4 + 1 = n - 3 from by omega] at hc4
      exact hc4.symm
  have hright : ∀ (i j : Fin n) (h : edgeD n i j),
      (theta i j h).comp (embSUid (unitaryInvolution K p f) 0) = iota j := by
    intro i j h
    rcases h with hc | ⟨h1, h2⟩
    · have hiN : i.val < n - 2 := by omega
      have hth : theta i j (Or.inl hc) = θc i.val := htheta_chain i j (Or.inl hc) hc.1 hc.2
      have hj : j.val = i.val + 1 := hc.1.symm
      by_cases hj2 : j.val + 2 < n
      · have hcj : iota j = (θc j.val).comp (embSUid (unitaryInvolution K p f) 2) :=
          hiota_chain j hj2
        have hcomp := (hθc i.val hiN).2.2.2.2 (show i.val + 1 < n - 2 by omega)
        rw [hth, hcj, show j.val = i.val + 1 from hj]
        exact hcomp.symm
      · have hje : j.val = n - 2 := by omega
        have hcj : iota j = (θc (n - 3)).comp (embSUid (unitaryInvolution K p f) 0) :=
          hiota_penult j (by omega) hje
        rw [hth, hcj]
        rw [show i.val = n - 3 from by omega]
    · have hcf : ¬ (i.val + 1 = j.val ∧ j.val + 1 < n) := by
        rintro ⟨e1, e2⟩
        omega
      have hcj : iota j = θ₂.comp (embSUid (unitaryInvolution K p f) 0) :=
        hiota_last j (by omega) (by omega)
      rw [htheta_fork i j (Or.inr ⟨h1, h2⟩) hcf, hcj]
  have hker : ∀ (i j : Fin n) (h : edgeD n i j),
      (theta i j h).ker ≤ Subgroup.center (Su K p f 3) := by
    intro i j h
    rcases h with hc | ⟨h1, h2⟩
    · rw [htheta_chain i j (Or.inl hc) hc.1 hc.2]
      exact (hθc i.val (by omega)).1
    · have hcf : ¬ (i.val + 1 = j.val ∧ j.val + 1 < n) := by
        rintro ⟨e1, e2⟩
        omega
      rw [htheta_fork i j (Or.inr ⟨h1, h2⟩) hcf]
      exact hk₂
  have hrangeθ : ∀ (i j : Fin n) (h : edgeD n i j), (theta i j h).range = W i j := by
    intro i j h
    rcases h with hc | ⟨h1, h2⟩
    · have h0 : i.val + 2 < n := by omega
      have hi : (⟨i.val, by omega⟩ : Fin n) = i := Fin.ext rfl
      have hj : (⟨i.val + 1, by omega⟩ : Fin n) = j := Fin.ext hc.1
      rw [htheta_chain i j (Or.inl hc) hc.1 hc.2, (hθc i.val (by omega)).2.1, hw i.val h0]
      exact congrArg₂ W hi hj
    · have hcf : ¬ (i.val + 1 = j.val ∧ j.val + 1 < n) := by
        rintro ⟨e1, e2⟩
        omega
      have hi : (⟨n - 3, by omega⟩ : Fin n) = i :=
        Fin.ext (show n - 3 = i.val by omega)
      have hj : (⟨n - 1, by omega⟩ : Fin n) = j :=
        Fin.ext (show n - 1 = j.val by omega)
      rw [htheta_fork i j (Or.inr ⟨h1, h2⟩) hcf, hWlast_range]
      exact congrArg₂ W hi hj
  have hmem : ∀ (i : Fin n) (a : Su K p f 2), iota i a ∈ U i := by
    intro i a
    rw [← hrange i]
    exact ⟨a, rfl⟩
  have hcommF : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      ∀ a b, iota i a * iota j b = iota j b * iota i a :=
    fun i j hij h1 h2 a b => hcomm i j hij h1 h2 (iota i a) (hmem i a) (iota j b) (hmem j b)
  refine ⟨⟨iota, theta, hleft, hright, hcommF⟩, hrange, hinj, hker, hrangeθ⟩

end CFSG.ClassicalInvolution.PhanDn
