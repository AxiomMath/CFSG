module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseFarDef
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseModelB
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseModelA

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG.OddStandard.AltStdSec.SylowSn

def farModel (l : List ℕ) (c : ℕ) : Set (Gam l) :=
  {γ | sgG l γ = 1 ∧ (γ = 1 ∨ (γ * γ = 1 ∧ γ ≠ 1 ∧ c + fixG l γ ≤ 3))}

theorem model_mem_farSet_iff {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {l : List ℕ} {c : ℕ}
    (ι : Gam l →* Equiv.Perm (Fin n)) (hι : Function.Injective ι)
    (hsg : ∀ γ, Equiv.Perm.sign (ι γ) = sgG l γ)
    (hfix : ∀ γ, Nat.card (Function.fixedPoints (ι γ)) = c + fixG l γ)
    (hP : ∀ x, x ∈ P ↔ ∃ γ, sgG l γ = 1 ∧ ι γ = x) (γ : Gam l) :
    ι γ ∈ farSet n P ↔ γ ∈ farModel l c := by
  have hι1 : ι γ = 1 ↔ γ = 1 := by
    rw [← map_one ι]
    exact hι.eq_iff
  have hsq : ι γ * ι γ = 1 ↔ γ * γ = 1 := by
    rw [← map_mul, ← map_one ι]
    exact hι.eq_iff
  constructor
  · rintro (h | ⟨-, h2, h1, h3, h4⟩)
    · have h' : γ = 1 := hι1.1 (Set.mem_singleton_iff.1 h)
      subst h'
      exact ⟨map_one _, Or.inl rfl⟩
    · have h5 : sgG l γ = 1 := (hsg γ).symm.trans h4
      have h6 := hfix γ
      exact ⟨h5, Or.inr ⟨hsq.1 h2, fun h => h1 (hι1.2 h), by omega⟩⟩
  · rintro ⟨h5, h | ⟨h2, h1, h3⟩⟩
    · exact Or.inl (Set.mem_singleton_iff.2 (hι1.2 h))
    · have h6 := hfix γ
      exact Or.inr ⟨(hP _).2 ⟨γ, h5, rfl⟩, hsq.2 h2, fun h => h1 (hι1.1 h), by omega,
        (hsg γ).trans h5⟩

theorem farTriple_model {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {l : List ℕ} {c : ℕ}
    (ι : Gam l →* Equiv.Perm (Fin n)) (hι : Function.Injective ι)
    (hsg : ∀ γ, Equiv.Perm.sign (ι γ) = sgG l γ)
    (hfix : ∀ γ, Nat.card (Function.fixedPoints (ι γ)) = c + fixG l γ)
    (hP : ∀ x, x ∈ P ↔ ∃ γ, sgG l γ = 1 ∧ ι γ = x) (γ : Gam l) :
    farTriple n P (ι γ) = prodCnt (farModel l c) γ := by
  unfold farTriple
  refine prodCnt_inj ι hι (fun h => model_mem_farSet_iff ι hι hsg hfix hP h) (fun x hx => ?_) γ
  rcases hx with hx | hx
  · exact ⟨1, by rw [map_one]; exact (Set.mem_singleton_iff.1 hx).symm⟩
  · obtain ⟨δ, -, hδ⟩ := (hP x).1 hx.1
    exact ⟨δ, hδ⟩

theorem farModel_eq {l₂ : List ℕ} {k c : ℕ} (hc : c ≤ 1) (hk : 1 ≤ k) (hpts : ptsG l₂ = 4 * k)
    (hl₂ : ∀ a ∈ l₂, 2 ≤ a) (hne : l₂ ≠ []) : farModel l₂ c = insert 1 (Fl l₂) := by
  have hl1 : ∀ a ∈ l₂, 1 ≤ a := fun a ha => by have := hl₂ a ha; omega
  ext γ
  constructor
  · rintro ⟨hsg, h1 | ⟨h2, h1, hf⟩⟩
    · exact Or.inl h1
    · refine Or.inr ((mem_Fl_iff l₂ γ).2 ⟨h2, ?_⟩)
      obtain ⟨m, hm⟩ := fixG_even l₂ hl1 γ
      have hs := sgG_invol l₂ γ h2
      rw [hsg, hpts] at hs
      by_contra hne0
      have hm2 : fixG l₂ γ = 2 := by omega
      rw [hm2] at hs
      have hodd : Odd ((4 * k - 2) / 2) := ⟨k - 1, by omega⟩
      rw [hodd.neg_one_pow] at hs
      exact absurd hs (by decide)
  · rintro (h1 | h)
    · subst h1
      exact ⟨map_one _, Or.inl rfl⟩
    · obtain ⟨h2, hf⟩ := (mem_Fl_iff l₂ γ).1 h
      refine ⟨?_, Or.inr ⟨h2, ?_, by omega⟩⟩
      · rw [sgG_invol l₂ γ h2, hf, hpts]
        have heven : Even ((4 * k - 0) / 2) := ⟨k, by omega⟩
        exact heven.neg_one_pow
      · intro h1
        subst h1
        exact one_notMem_Fl l₂ hne h

theorem farCount_model {n : ℕ} (P : Subgroup (Equiv.Perm (Fin n))) {l₂ : List ℕ} {k c : ℕ}
    (hc : c ≤ 1) (hk : 1 ≤ k) (hpts : ptsG l₂ = 4 * k) (hl₂ : ∀ a ∈ l₂, 2 ≤ a)
    (hbig : (∃ a ∈ l₂, 4 ≤ a) ∨ l₂ = [2, 3])
    (ι : Gam l₂ →* Equiv.Perm (Fin n)) (hι : Function.Injective ι)
    (hsg : ∀ γ, Equiv.Perm.sign (ι γ) = sgG l₂ γ)
    (hfix : ∀ γ, Nat.card (Function.fixedPoints (ι γ)) = c + fixG l₂ γ)
    (hP : ∀ x, x ∈ P ↔ ∃ γ, sgG l₂ γ = 1 ∧ ι γ = x)
    (y : Equiv.Perm (Fin n)) (hyP : y ∈ P) (hyF : y ∈ farSet n P) (hy1 : y ≠ 1)
    (hyc : ∀ p ∈ P, p * y = y * p) : farTriple n P 1 ≠ farTriple n P y := by
  have hne : l₂ ≠ [] := by
    rcases hbig with ⟨a, ha, -⟩ | h
    · exact List.ne_nil_of_mem ha
    · rw [h]
      exact List.cons_ne_nil _ _
  have hbig1 : 2 ≤ l₂.length ∨ ∃ a ∈ l₂, 3 ≤ a := by
    rcases hbig with ⟨a, ha, h4⟩ | h
    · exact Or.inr ⟨a, ha, by omega⟩
    · rw [h]
      exact Or.inl (by simp)
  have hΩ : farModel l₂ c = insert 1 (Fl l₂) := farModel_eq hc hk hpts hl₂ hne
  have hT : ∀ γ, farTriple n P (ι γ) = prodCnt (insert (1 : Gam l₂) (Fl l₂)) γ := fun γ => by
    rw [farTriple_model ι hι hsg hfix hP γ, hΩ]
  obtain ⟨γc, hγc1, rfl⟩ := (hP y).1 hyP
  have hγcΩ : γc ∈ insert (1 : Gam l₂) (Fl l₂) := by
    rw [← hΩ, ← model_mem_farSet_iff ι hι hsg hfix hP]
    exact hyF
  have hγc_ne : γc ≠ 1 := by
    rintro rfl
    exact hy1 (map_one ι)
  have hγcFl : γc ∈ Fl l₂ := by
    rcases hγcΩ with h | h
    · exact absurd h hγc_ne
    · exact h
  have hcent : ∀ δ : Gam l₂, sgG l₂ δ = 1 → δ * γc = γc * δ := by
    intro δ hδ
    apply hι
    rw [map_mul, map_mul]
    exact hyc (ι δ) ((hP _).2 ⟨δ, hδ, rfl⟩)
  obtain ⟨h2, hf0⟩ := (mem_Fl_iff l₂ γc).1 hγcFl
  have hcL : γc = cL l₂ := central_far l₂ hl₂ hbig1 γc hγc1 hcent h2 (by omega)
  subst hcL
  have h1 : farTriple n P 1 = prodCnt (insert (1 : Gam l₂) (Fl l₂)) 1 := by
    rw [← hT 1, map_one]
  rw [h1, hT (cL l₂)]
  exact (modelFar l₂ hl₂ hbig).ne

theorem farCount_case1 {n : ℕ} (P : Subgroup (Equiv.Perm (Fin n))) {l₂ : List ℕ} {k : ℕ}
    (hk : 1 ≤ k) (hpts : ptsG l₂ = 4 * k) (hl₂ : ∀ a ∈ l₂, 2 ≤ a)
    (hbig : (∃ a ∈ l₂, 4 ≤ a) ∨ l₂ = [2, 3]) {l : List ℕ} (hl : l = 0 :: l₂)
    (ι : Gam l →* Equiv.Perm (Fin n)) (hι : Function.Injective ι)
    (hsg : ∀ γ, Equiv.Perm.sign (ι γ) = sgG l γ)
    (hfix : ∀ γ, Nat.card (Function.fixedPoints (ι γ)) = fixG l γ)
    (hP : ∀ x, x ∈ P ↔ ∃ γ, sgG l γ = 1 ∧ ι γ = x)
    (y : Equiv.Perm (Fin n)) (hyP : y ∈ P) (hyF : y ∈ farSet n P) (hy1 : y ≠ 1)
    (hyc : ∀ p ∈ P, p * y = y * p) : farTriple n P 1 ≠ farTriple n P y := by
  subst hl
  let j : Gam l₂ →* Gam (0 :: l₂) := MonoidHom.inr (W 0) (Gam l₂)
  have hjsg : ∀ γ, sgG (0 :: l₂) (j γ) = sgG l₂ γ := fun γ => by
    show sgG (0 :: l₂) (Gam.cons 1 γ) = _
    rw [sgG_cons, map_one, one_mul]
  have hjfix : ∀ γ, fixG (0 :: l₂) (j γ) = 1 + fixG l₂ γ := fun γ => by
    show fixW 0 1 + fixG l₂ γ = _
    rw [fixW_zero]
  have hjsurj : ∀ δ : Gam (0 :: l₂), ∃ γ, j γ = δ := by
    rintro ⟨w, γ⟩
    exact ⟨γ, Prod.ext (Subsingleton.elim _ _) rfl⟩
  refine farCount_model P (c := 1) le_rfl hk hpts hl₂ hbig (ι.comp j) ?_ ?_ ?_ ?_ y hyP hyF hy1 hyc
  · exact hι.comp (fun a b h => (Prod.ext_iff.1 h).2)
  · intro γ
    exact (hsg (j γ)).trans (hjsg γ)
  · intro γ
    exact (hfix (j γ)).trans (hjfix γ)
  · intro x
    rw [hP x]
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      obtain ⟨γ, rfl⟩ := hjsurj δ
      exact ⟨γ, (hjsg γ).symm.trans hδ, rfl⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨j γ, (hjsg γ).trans hγ, rfl⟩

theorem bitIndices_four_mul (k : ℕ) : (4 * k).bitIndices = k.bitIndices.map (· + 2) := by
  have h : 4 * k = 2 * (2 * k) := by omega
  rw [h, Nat.bitIndices_two_mul, Nat.bitIndices_two_mul, List.map_map]
  rfl

theorem bitIndices_four_mul_add_one (k : ℕ) :
    (4 * k + 1).bitIndices = 0 :: (4 * k).bitIndices := by
  have h : 4 * k = 2 * (2 * k) := by omega
  rw [h, Nat.bitIndices_two_mul_add_one, Nat.bitIndices_two_mul (2 * k)]

theorem two_le_of_mem_bitIndices_four_mul (k a : ℕ) (ha : a ∈ (4 * k).bitIndices) : 2 ≤ a := by
  rw [bitIndices_four_mul] at ha
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
  omega

theorem exists_bitIndex_ge (m n : ℕ) (hn : 2 ^ m ≤ n) : ∃ a ∈ n.bitIndices, m ≤ a := by
  by_contra h
  push Not at h
  have : n < 2 ^ m := Nat.lt_pow_two_of_testBit n (fun i hi => by
    by_contra hb
    have hb' : n.testBit i = true := by simpa using hb
    have := h i (Nat.mem_bitIndices.2 hb')
    omega)
  omega

theorem bitIndices_big (k : ℕ) (hk : 3 ≤ k) :
    (∃ a ∈ (4 * k).bitIndices, 4 ≤ a) ∨ (4 * k).bitIndices = [2, 3] := by
  rcases Nat.eq_or_lt_of_le hk with h | h
  · right
    subst h
    decide
  · left
    exact exists_bitIndex_ge 4 (4 * k) (by omega)

theorem farCount_mod01 (n : ℕ) (hn : 12 ≤ n) (h : n % 4 = 0 ∨ n % 4 = 1) : FarCount n := by
  intro P hP hp hmax y hyP hyF hy1 hyc
  obtain ⟨ι, hι, hsg, hfix, hPm⟩ := exists_model n P hP hp hmax
  obtain ⟨k, hk3, hkn⟩ : ∃ k, 3 ≤ k ∧ (n = 4 * k ∨ n = 4 * k + 1) :=
    ⟨n / 4, by omega, by omega⟩
  have hpts : ptsG (4 * k).bitIndices = 4 * k := Nat.sum_map_two_pow_bitIndices (4 * k)
  have hl₂ : ∀ a ∈ (4 * k).bitIndices, 2 ≤ a := fun a ha =>
    two_le_of_mem_bitIndices_four_mul k a ha
  have hbig := bitIndices_big k hk3
  rcases hkn with rfl | rfl
  · exact farCount_model P (c := 0) (Nat.zero_le _) (by omega) hpts hl₂ hbig ι hι hsg
      (fun γ => by rw [zero_add]; exact hfix γ) hPm y hyP hyF hy1 hyc
  · exact farCount_case1 P (by omega) hpts hl₂ hbig (bitIndices_four_mul_add_one k) ι hι hsg hfix
      hPm y hyP hyF hy1 hyc

end CFSG.OddStandard.AltStdSec
