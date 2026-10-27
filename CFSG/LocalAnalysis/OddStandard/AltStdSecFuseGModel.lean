module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseGTab
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseModel

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG.OddStandard.AltStdSec.SylowSn

theorem bitIndices_four_mul_add_two (k : ℕ) :
    (4 * k + 2).bitIndices = 1 :: (4 * k).bitIndices := by
  have h : 4 * k + 2 = 2 * (2 * k + 1) := by omega
  have h' : 4 * k = 2 * (2 * k) := by omega
  rw [h, Nat.bitIndices_two_mul, Nat.bitIndices_two_mul_add_one, h', Nat.bitIndices_two_mul]
  simp

theorem bitIndices_four_mul_add_three (k : ℕ) :
    (4 * k + 3).bitIndices = 0 :: 1 :: (4 * k).bitIndices := by
  have h : 4 * k + 3 = 2 * (2 * k + 1) + 1 := by omega
  have h2 : 2 * (2 * k + 1) = 4 * k + 2 := by omega
  rw [h, Nat.bitIndices_two_mul_add_one, ← Nat.bitIndices_two_mul, h2,
    bitIndices_four_mul_add_two]

theorem W_one_eq (w : W 1) : w = 1 ∨ w = cc 1 :=
  eq_one_or_cc 1 le_rfl w (fun a => W_one_comm a w) (W_one_sq w)

@[expose] noncomputable def sgSecFun (ε : ℤˣ) : W 1 := if ε = 1 then 1 else cc 1

theorem sgSecFun_one : sgSecFun 1 = 1 := by
  unfold sgSecFun
  exact ite_eq_left rfl

theorem sgSecFun_neg_one : sgSecFun (-1) = cc 1 := by
  have h1 : (-1 : ℤˣ) ≠ 1 := by decide
  unfold sgSecFun
  exact ite_eq_right h1

theorem sgSecFun_mul (ε₁ ε₂ : ℤˣ) : sgSecFun (ε₁ * ε₂) = sgSecFun ε₁ * sgSecFun ε₂ := by
  rcases Int.units_eq_one_or ε₁ with rfl | rfl <;>
    rcases Int.units_eq_one_or ε₂ with rfl | rfl
  · rw [one_mul (1 : ℤˣ), sgSecFun_one, one_mul (1 : W 1)]
  · rw [one_mul (-1 : ℤˣ), sgSecFun_one, one_mul (sgSecFun (-1))]
  · rw [mul_one (-1 : ℤˣ), sgSecFun_one, mul_one (sgSecFun (-1))]
  · have h : ((-1 : ℤˣ) * -1) = 1 := by decide
    rw [h, sgSecFun_one, sgSecFun_neg_one, W_one_sq]

@[expose] noncomputable def sgSec : ℤˣ →* W 1 where
  toFun := sgSecFun
  map_one' := sgSecFun_one
  map_mul' := sgSecFun_mul

theorem sgSec_apply (ε : ℤˣ) : sgSec ε = sgSecFun ε := rfl

theorem sgW_one_sgSec (ε : ℤˣ) : sgW 1 (sgSec ε) = ε := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · rw [sgSec_apply, sgSecFun_one, map_one]
  · rw [sgSec_apply, sgSecFun_neg_one, sgW_cc_one]

theorem fixW_one_sgSec (ε : ℤˣ) : fixW 1 (sgSec ε) = if ε = 1 then 2 else 0 := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · rw [sgSec_apply, sgSecFun_one, fixW_one, ite_eq_left rfl]
    rfl
  · have h1 : (-1 : ℤˣ) ≠ 1 := by decide
    rw [sgSec_apply, sgSecFun_neg_one, ite_eq_right h1]
    exact (cc_mem_Fb 1 le_rfl).2

theorem sgSec_sgW_one (w : W 1) : sgSec (sgW 1 w) = w := by
  rcases W_one_eq w with rfl | rfl
  · rw [map_one, map_one]
  · rw [sgW_cc_one, sgSec_apply, sgSecFun_neg_one]

@[expose] noncomputable def psiSec (l₂ : List ℕ) : Gam l₂ →* Gam (1 :: l₂) :=
  (sgSec.comp (sgG l₂)).prod (MonoidHom.id (Gam l₂))

theorem psiSec_apply (l₂ : List ℕ) (γ : Gam l₂) :
    psiSec l₂ γ = Gam.cons (sgSec (sgG l₂ γ)) γ := rfl

theorem psiSec_injective (l₂ : List ℕ) : Function.Injective (psiSec l₂) :=
  fun _ _ h => (Prod.ext_iff.1 h).2

theorem sgG_psiSec (l₂ : List ℕ) (γ : Gam l₂) : sgG (1 :: l₂) (psiSec l₂ γ) = 1 := by
  rw [psiSec_apply, sgG_cons, sgW_one_sgSec]
  exact Int.units_mul_self _

theorem fixG_psiSec (l₂ : List ℕ) (γ : Gam l₂) :
    fixG (1 :: l₂) (psiSec l₂ γ) = (if sgG l₂ γ = 1 then 2 else 0) + fixG l₂ γ := by
  rw [psiSec_apply, fixG_cons, fixW_one_sgSec]

theorem exists_psiSec (l₂ : List ℕ) (δ : Gam (1 :: l₂)) (hδ : sgG (1 :: l₂) δ = 1) :
    ∃ γ, psiSec l₂ γ = δ := by
  obtain ⟨w, γ⟩ := δ
  refine ⟨γ, ?_⟩
  rw [sgG_cons] at hδ
  have hw : sgW 1 w = sgG l₂ γ := by
    have h := Int.units_mul_self (sgG l₂ γ)
    calc sgW 1 w = sgW 1 w * (sgG l₂ γ * sgG l₂ γ) := by rw [h, mul_one]
      _ = (sgW 1 w * sgG l₂ γ) * sgG l₂ γ := by rw [mul_assoc]
      _ = sgG l₂ γ := by rw [hδ, one_mul]
  rw [psiSec_apply, ← hw, sgSec_sgW_one]

theorem model2_mem_farSet_iff {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {l₂ : List ℕ}
    {k c : ℕ} (hc : c ≤ 1) (hk : 1 ≤ k) (hpts : ptsG l₂ = 4 * k) (hl₂ : ∀ a ∈ l₂, 2 ≤ a)
    (ι : Gam l₂ →* Equiv.Perm (Fin n)) (hι : Function.Injective ι)
    (hsg : ∀ γ, Equiv.Perm.sign (ι γ) = 1)
    (hfix : ∀ γ, Nat.card (Function.fixedPoints (ι γ)) =
      c + (if sgG l₂ γ = 1 then 2 else 0) + fixG l₂ γ)
    (hP : ∀ x, x ∈ P ↔ ∃ γ, ι γ = x) (γ : Gam l₂) :
    ι γ ∈ farSet n P ↔ γ ∈ insert (1 : Gam l₂) (Fl l₂ ∪ Gl l₂) := by
  have hl1 : ∀ a ∈ l₂, 1 ≤ a := fun a ha => by have := hl₂ a ha; omega
  have hne : l₂ ≠ [] := by
    rintro rfl
    have h0 : ptsG ([] : List ℕ) = 0 := rfl
    omega
  have hι1 : ι γ = 1 ↔ γ = 1 := by
    rw [← map_one ι]
    exact hι.eq_iff
  have hsq : ι γ * ι γ = 1 ↔ γ * γ = 1 := by
    rw [← map_mul, ← map_one ι]
    exact hι.eq_iff
  have h6 := hfix γ
  obtain ⟨m, hm⟩ := fixG_even l₂ hl1 γ
  constructor
  · rintro (h | ⟨-, h2, h1, h3, -⟩)
    · exact Or.inl (hι1.1 (Set.mem_singleton_iff.1 h))
    · have hγ2 : γ * γ = 1 := hsq.1 h2
      have hs := sgG_invol l₂ γ hγ2
      rw [hpts] at hs
      by_cases hs1 : sgG l₂ γ = 1
      · rw [ite_eq_left hs1] at h6
        exact Or.inr (Or.inl ((mem_Fl_iff l₂ γ).2 ⟨hγ2, by omega⟩))
      · rw [ite_eq_right hs1] at h6
        refine Or.inr (Or.inr ((mem_Gl_iff l₂ hl1 γ).2 ⟨hγ2, ?_⟩))
        by_contra hne2
        have h0 : fixG l₂ γ = 0 := by omega
        rw [h0] at hs
        have heven : Even ((4 * k - 0) / 2) := ⟨k, by omega⟩
        exact hs1 (hs.trans heven.neg_one_pow)
  · rintro (h | h | h)
    · exact Or.inl (Set.mem_singleton_iff.2 (hι1.2 h))
    · obtain ⟨hγ2, hf0⟩ := (mem_Fl_iff l₂ γ).1 h
      have hs : sgG l₂ γ = 1 := by
        rw [sgG_invol l₂ γ hγ2, hf0, hpts]
        have heven : Even ((4 * k - 0) / 2) := ⟨k, by omega⟩
        exact heven.neg_one_pow
      rw [ite_eq_left hs] at h6
      refine Or.inr ⟨(hP _).2 ⟨γ, rfl⟩, hsq.2 hγ2, fun h1 => ?_, by omega, hsg γ⟩
      exact one_notMem_Fl l₂ hne (hι1.1 h1 ▸ h)
    · obtain ⟨hγ2, hf2⟩ := (mem_Gl_iff l₂ hl1 γ).1 h
      have hs : sgG l₂ γ ≠ 1 := by
        rw [sgG_invol l₂ γ hγ2, hf2, hpts]
        have hodd : Odd ((4 * k - 2) / 2) := ⟨k - 1, by omega⟩
        rw [hodd.neg_one_pow]
        decide
      rw [ite_eq_right hs] at h6
      refine Or.inr ⟨(hP _).2 ⟨γ, rfl⟩, hsq.2 hγ2, fun h1 => ?_, by omega, hsg γ⟩
      have h7 : fixG l₂ (1 : Gam l₂) = 4 * k := hpts ▸ fixG_one l₂
      have h8 : γ = 1 := hι1.1 h1
      subst h8
      omega

theorem farTriple_model2 {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {l₂ : List ℕ}
    {k c : ℕ} (hc : c ≤ 1) (hk : 1 ≤ k) (hpts : ptsG l₂ = 4 * k) (hl₂ : ∀ a ∈ l₂, 2 ≤ a)
    (ι : Gam l₂ →* Equiv.Perm (Fin n)) (hι : Function.Injective ι)
    (hsg : ∀ γ, Equiv.Perm.sign (ι γ) = 1)
    (hfix : ∀ γ, Nat.card (Function.fixedPoints (ι γ)) =
      c + (if sgG l₂ γ = 1 then 2 else 0) + fixG l₂ γ)
    (hP : ∀ x, x ∈ P ↔ ∃ γ, ι γ = x) (γ : Gam l₂) :
    farTriple n P (ι γ) = prodCnt (insert (1 : Gam l₂) (Fl l₂ ∪ Gl l₂)) γ := by
  unfold farTriple
  refine prodCnt_inj ι hι (fun h => model2_mem_farSet_iff hc hk hpts hl₂ ι hι hsg hfix hP h)
    (fun x hx => ?_) γ
  rcases hx with hx | hx
  · exact ⟨1, by rw [map_one]; exact (Set.mem_singleton_iff.1 hx).symm⟩
  · exact (hP x).1 hx.1

theorem farCount_model2 {n : ℕ} (P : Subgroup (Equiv.Perm (Fin n))) {l₂ : List ℕ} {k c : ℕ}
    (hc : c ≤ 1) (hk : 1 ≤ k) (hpts : ptsG l₂ = 4 * k) (hl₂ : ∀ a ∈ l₂, 2 ≤ a)
    (hbig : (∃ a ∈ l₂, 4 ≤ a) ∨ l₂ = [2, 3])
    (ι : Gam l₂ →* Equiv.Perm (Fin n)) (hι : Function.Injective ι)
    (hsg : ∀ γ, Equiv.Perm.sign (ι γ) = 1)
    (hfix : ∀ γ, Nat.card (Function.fixedPoints (ι γ)) =
      c + (if sgG l₂ γ = 1 then 2 else 0) + fixG l₂ γ)
    (hP : ∀ x, x ∈ P ↔ ∃ γ, ι γ = x)
    (y : Equiv.Perm (Fin n)) (hyP : y ∈ P) (hyF : y ∈ farSet n P) (hy1 : y ≠ 1)
    (hyc : ∀ p ∈ P, p * y = y * p) : farTriple n P 1 ≠ farTriple n P y := by
  have hl1 : ∀ a ∈ l₂, 1 ≤ a := fun a ha => by have := hl₂ a ha; omega
  have hT : ∀ γ, farTriple n P (ι γ) = prodCnt (insert (1 : Gam l₂) (Fl l₂ ∪ Gl l₂)) γ :=
    fun γ => farTriple_model2 hc hk hpts hl₂ ι hι hsg hfix hP γ
  obtain ⟨γc, rfl⟩ := (hP y).1 hyP
  have hγcΩ : γc ∈ insert (1 : Gam l₂) (Fl l₂ ∪ Gl l₂) :=
    (model2_mem_farSet_iff hc hk hpts hl₂ ι hι hsg hfix hP γc).1 hyF
  have hγc_ne : γc ≠ 1 := by
    rintro rfl
    exact hy1 (map_one ι)
  have hγcFG : γc ∈ Fl l₂ ∪ Gl l₂ := by
    rcases hγcΩ with h | h
    · exact absurd h hγc_ne
    · exact h
  have hcent : ∀ δ : Gam l₂, δ * γc = γc * δ := by
    intro δ
    apply hι
    rw [map_mul, map_mul]
    exact hyc (ι δ) ((hP _).2 ⟨δ, rfl⟩)
  have hsq : γc * γc = 1 ∧ fixG l₂ γc ≤ 3 := by
    rcases hγcFG with h | h
    · obtain ⟨h2, hf⟩ := (mem_Fl_iff l₂ γc).1 h
      exact ⟨h2, by omega⟩
    · obtain ⟨h2, hf⟩ := (mem_Gl_iff l₂ hl1 γc).1 h
      exact ⟨h2, by omega⟩
  have hcL : γc = cL l₂ := eq_cL_of_central l₂ hl₂ γc hcent hsq.1 hsq.2
  subst hcL
  have h1 : farTriple n P 1 = prodCnt (insert (1 : Gam l₂) (Fl l₂ ∪ Gl l₂)) 1 := by
    rw [← hT 1, map_one]
  rw [h1, hT (cL l₂)]
  exact (modelFarG l₂ hl₂ hbig).ne

theorem farCount_case2 {n : ℕ} (P : Subgroup (Equiv.Perm (Fin n))) {l₂ : List ℕ} {k c : ℕ}
    (hc : c ≤ 1) (hk : 1 ≤ k) (hpts : ptsG l₂ = 4 * k) (hl₂ : ∀ a ∈ l₂, 2 ≤ a)
    (hbig : (∃ a ∈ l₂, 4 ≤ a) ∨ l₂ = [2, 3]) {l : List ℕ} (hl : l = 1 :: l₂)
    (ι : Gam l →* Equiv.Perm (Fin n)) (hι : Function.Injective ι)
    (hsg : ∀ γ, Equiv.Perm.sign (ι γ) = sgG l γ)
    (hfix : ∀ γ, Nat.card (Function.fixedPoints (ι γ)) = c + fixG l γ)
    (hP : ∀ x, x ∈ P ↔ ∃ γ, sgG l γ = 1 ∧ ι γ = x)
    (y : Equiv.Perm (Fin n)) (hyP : y ∈ P) (hyF : y ∈ farSet n P) (hy1 : y ≠ 1)
    (hyc : ∀ p ∈ P, p * y = y * p) : farTriple n P 1 ≠ farTriple n P y := by
  subst hl
  refine farCount_model2 P hc hk hpts hl₂ hbig (ι.comp (psiSec l₂)) ?_ ?_ ?_ ?_ y hyP hyF hy1 hyc
  · exact hι.comp (psiSec_injective l₂)
  · intro γ
    exact (hsg (psiSec l₂ γ)).trans (sgG_psiSec l₂ γ)
  · intro γ
    show Nat.card (Function.fixedPoints (ι (psiSec l₂ γ))) = _
    rw [hfix, fixG_psiSec, add_assoc]
  · intro x
    rw [hP x]
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      obtain ⟨γ, rfl⟩ := exists_psiSec l₂ δ hδ
      exact ⟨γ, rfl⟩
    · rintro ⟨γ, rfl⟩
      exact ⟨psiSec l₂ γ, sgG_psiSec l₂ γ, rfl⟩

theorem farCount_case3 {n : ℕ} (P : Subgroup (Equiv.Perm (Fin n))) {l₂ : List ℕ} {k : ℕ}
    (hk : 1 ≤ k) (hpts : ptsG l₂ = 4 * k) (hl₂ : ∀ a ∈ l₂, 2 ≤ a)
    (hbig : (∃ a ∈ l₂, 4 ≤ a) ∨ l₂ = [2, 3]) {l : List ℕ} (hl : l = 0 :: 1 :: l₂)
    (ι : Gam l →* Equiv.Perm (Fin n)) (hι : Function.Injective ι)
    (hsg : ∀ γ, Equiv.Perm.sign (ι γ) = sgG l γ)
    (hfix : ∀ γ, Nat.card (Function.fixedPoints (ι γ)) = fixG l γ)
    (hP : ∀ x, x ∈ P ↔ ∃ γ, sgG l γ = 1 ∧ ι γ = x)
    (y : Equiv.Perm (Fin n)) (hyP : y ∈ P) (hyF : y ∈ farSet n P) (hy1 : y ≠ 1)
    (hyc : ∀ p ∈ P, p * y = y * p) : farTriple n P 1 ≠ farTriple n P y := by
  subst hl
  let j : Gam (1 :: l₂) →* Gam (0 :: 1 :: l₂) := MonoidHom.inr (W 0) (Gam (1 :: l₂))
  have hjsg : ∀ γ, sgG (0 :: 1 :: l₂) (j γ) = sgG (1 :: l₂) γ := fun γ => by
    show sgG (0 :: 1 :: l₂) (Gam.cons 1 γ) = _
    rw [sgG_cons, map_one, one_mul]
  have hjfix : ∀ γ, fixG (0 :: 1 :: l₂) (j γ) = 1 + fixG (1 :: l₂) γ := fun γ => by
    show fixW 0 1 + fixG (1 :: l₂) γ = _
    rw [fixW_zero]
  have hjsurj : ∀ δ : Gam (0 :: 1 :: l₂), ∃ γ, j γ = δ := by
    rintro ⟨w, γ⟩
    exact ⟨γ, Prod.ext (Subsingleton.elim _ _) rfl⟩
  refine farCount_case2 P (c := 1) le_rfl hk hpts hl₂ hbig (l := 1 :: l₂) rfl (ι.comp j) ?_ ?_ ?_
    ?_ y hyP hyF hy1 hyc
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

theorem farCount_mod23 (n : ℕ) (hn : 14 ≤ n) (h : n % 4 = 2 ∨ n % 4 = 3) : FarCount n := by
  intro P hP hp hmax y hyP hyF hy1 hyc
  obtain ⟨ι, hι, hsg, hfix, hPm⟩ := exists_model n P hP hp hmax
  obtain ⟨k, hk3, hkn⟩ : ∃ k, 3 ≤ k ∧ (n = 4 * k + 2 ∨ n = 4 * k + 3) :=
    ⟨n / 4, by omega, by omega⟩
  have hpts : ptsG (4 * k).bitIndices = 4 * k := Nat.sum_map_two_pow_bitIndices (4 * k)
  have hl₂ : ∀ a ∈ (4 * k).bitIndices, 2 ≤ a := fun a ha =>
    two_le_of_mem_bitIndices_four_mul k a ha
  have hbig := bitIndices_big k hk3
  rcases hkn with rfl | rfl
  · exact farCount_case2 P (c := 0) (Nat.zero_le _) (by omega) hpts hl₂ hbig
      (bitIndices_four_mul_add_two k) ι hι hsg (fun γ => by rw [zero_add]; exact hfix γ) hPm y
      hyP hyF hy1 hyc
  · exact farCount_case3 P (by omega) hpts hl₂ hbig (bitIndices_four_mul_add_three k) ι hι hsg
      hfix hPm y hyP hyF hy1 hyc

end CFSG.OddStandard.AltStdSec
