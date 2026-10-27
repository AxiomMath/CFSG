module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOneBaseInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOneClosures
public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.EvenSporadicStandard.TwoRu.HypOne

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.M12Cover CFSG.Sporadic.SmallOddCore

theorem commute_of_card_isConj_le {G : Type*} [Group G] [Finite G] {x h : G} {p : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p) (hh : h ^ p = 1) (hx : Nat.card {y // IsConj x y} ≤ 4) :
    h * x = x * h := by
  by_contra hne
  have key : ∀ d, 0 < d → d < p → h ^ d * x ≠ x * h ^ d := by
    intro d hd hdp hc
    apply hne
    have hcop : Nat.Coprime d p :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hd hdp))
    obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    have e : h = (h ^ d) ^ a := by
      rw [← pow_mul, ← Nat.div_add_mod (d * a) p, pow_add, pow_mul, hh, one_pow, one_mul, ha,
        pow_one]
    rw [e]
    exact (Commute.pow_left hc a).eq
  have aux : ∀ i j : ℕ, i < j → j < p →
      h ^ i * x * (h ^ i)⁻¹ ≠ h ^ j * x * (h ^ j)⁻¹ := by
    intro i j hij hj e
    obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    apply key d (by omega) (by omega)
    rw [pow_add] at e
    have e2 := congrArg (fun y => (h ^ i)⁻¹ * y * h ^ i) e
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at e2
    calc h ^ d * x = h ^ d * (x * (h ^ d)⁻¹) * h ^ d := by group
      _ = x * h ^ d := by rw [← e2]
  let f : Fin p → {y // IsConj x y} := fun k =>
    ⟨h ^ (k : ℕ) * x * (h ^ (k : ℕ))⁻¹, isConj_iff.2 ⟨h ^ (k : ℕ), rfl⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    have e : h ^ (i : ℕ) * x * (h ^ (i : ℕ))⁻¹ = h ^ (j : ℕ) * x * (h ^ (j : ℕ))⁻¹ :=
      congrArg Subtype.val hij
    by_contra hne'
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne') with hlt | hlt
    · exact aux _ _ hlt j.2 e
    · exact aux _ _ hlt i.2 e.symm
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

theorem rep_tblOfArr {t : Array ℕ} {g : Equiv.Perm (Fin 4060)}
    (h : CFSG.Monster.B.Co2.Rep 4060 t g) : CFSG.Sporadic.Th.Rep 4060 (tblOfArr t) g := by
  intro i hi
  rw [CFSG.Sporadic.Th.idx_of_lt _ hi]
  have hti := h ⟨i, hi⟩
  have hlt : t[i]! < 2 ^ 32 := by
    rw [hti]
    exact (g ⟨i, hi⟩).isLt.trans (by norm_num)
  have hget : (tblOfArr t)[i]! = UInt32.ofNat t[i]! := by
    by_cases hs : i < t.size
    · rw [getElem!_pos (tblOfArr t) i (by simpa [tblOfArr] using hs), getElem!_pos t i hs]
      simp [tblOfArr]
    · rw [getElem!_neg (tblOfArr t) i (by simpa [tblOfArr] using hs), getElem!_neg t i hs]
      rfl
  rw [ap, hget, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt, hti]
  rfl

variable {n : ℕ}

theorem rep_apply {T : Table} {g : Equiv.Perm (Fin n)} (h : Rep n T g) {i : ℕ} (hi : i < n) :
    ap T i = (g ⟨i, hi⟩ : ℕ) := by
  rw [h i hi, idx_of_lt _ hi]
  rfl

theorem lettersOK_spec {k : ℕ} {w : List ℤ} (h : lettersOK k w = true) :
    ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ k := by
  intro z hz
  have := List.all_eq_true.1 h z hz
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
  exact this

theorem sq_fix_of_basePtOK (hn : n < 2 ^ 32) {hT hTi : Array Table} {hh : ℕ → Equiv.Perm (Fin n)}
    {X : Equiv.Perm (Fin n)}
    (hg : ∀ l < hT.size, Rep n hT[l]! (hh l) ∧ Rep n hTi[l]! (hh l)⁻¹ ∧
      hh l ∈ Subgroup.centralizer {X})
    {q : ℕ × List (List ℤ) × List (ℕ × List ℤ)} (hq : basePtOK n hT hTi q = true)
    (hb : q.1 < n) : X (X ⟨q.1, hb⟩) = ⟨q.1, hb⟩ := by
  simp only [basePtOK, Bool.and_eq_true, List.all_eq_true, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, beq_iff_eq] at hq
  obtain ⟨⟨⟨⟨⟨-, hsl⟩, hfl⟩, hs⟩, hall⟩, hf⟩ := hq
  have hcomm : ∀ {g : Equiv.Perm (Fin n)}, g ∈ Subgroup.centralizer {X} → ∀ y, g (X y) = X (g y) :=
    fun hgc y => by
      have := Subgroup.mem_centralizer_singleton_iff.1 hgc
      rw [← Equiv.Perm.mul_apply, this, Equiv.Perm.mul_apply]
  set c := X ⟨q.1, hb⟩ with hc
  have hsc : ∀ s ∈ q.2.1, ap (wordT n (letterTab hT hTi) s) c = c := by
    intro s hsm
    obtain ⟨S, hSK, hSR⟩ := rep_wordTables hn _ hg (lettersOK_spec (hsl s hsm))
    have h1 : S ⟨q.1, hb⟩ = ⟨q.1, hb⟩ := Fin.ext (by rw [← rep_apply hSR hb]; exact hs s hsm)
    rw [rep_apply hSR c.2]
    change ((S (X ⟨q.1, hb⟩)) : ℕ) = (X ⟨q.1, hb⟩ : ℕ)
    rw [hcomm hSK, h1]
  have hany := allIn_eq_true.1 hall c (Nat.zero_le _) c.2
  have hsall : ((q.2.1.map (wordT n (letterTab hT hTi))).all fun s => ap s c == c) = true := by
    simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, beq_iff_eq]
    exact hsc
  rw [hsall, Bool.not_true, Bool.false_or, List.any_eq_true] at hany
  obtain ⟨f, hfm, hfc⟩ := hany
  rw [beq_iff_eq] at hfc
  obtain ⟨T, hTK, hTR⟩ := rep_wordTables hn _ hg (lettersOK_spec (hfl f hfm))
  obtain ⟨h1, h2⟩ := hf f hfm
  have hTb : T ⟨q.1, hb⟩ = c := Fin.ext (by rw [← rep_apply hTR hb, h1, hfc])
  have hTc : T c = ⟨q.1, hb⟩ := Fin.ext (by
    rw [← rep_apply hTR c.2]
    change ap _ (c : ℕ) = q.1
    rw [← hfc]
    exact h2)
  calc X c = X (T ⟨q.1, hb⟩) := by rw [hTb]
    _ = T (X ⟨q.1, hb⟩) := (hcomm hTK _).symm
    _ = ⟨q.1, hb⟩ := hTc

theorem fourClassesLarge_of_baseOK (hn : n < 2 ^ 32) (K : Subgroup (Equiv.Perm (Fin n)))
    {gens : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ gg l ∈ K)
    {hw : List (List ℤ)} {p : ℕ} {pts : List (ℕ × List (List ℤ) × List (ℕ × List ℤ))}
    (hp : p.Prime) (h5 : 5 ≤ p) (hok : fourBaseOK n gens hw p pts = true)
    (hfix : ∀ g ∈ K, (∀ q ∈ pts, ∀ hq : q.1 < n, g ⟨q.1, hq⟩ = ⟨q.1, hq⟩) → g = 1) :
    FourClassesLarge K := by
  classical
  intro x _ hx2
  by_contra hlt
  have hle : Nat.card {y : K // IsConj x y} ≤ 4 := by omega
  simp only [fourBaseOK, Bool.and_eq_true, List.all_eq_true, Array.all_eq_true,
    List.mem_range] at hok
  obtain ⟨⟨⟨hgi, hhw⟩, hH⟩, hpts⟩ := hok
  set gi := gens.map (invT n) with hgi_def
  set hT := (hw.map (wordT n (letterTab gens gi))).toArray with hT_def
  set hTi := hT.map (invT n) with hTi_def
  have hg' : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gi[l]! (gg l)⁻¹ ∧ gg l ∈ K := by
    intro l hl
    refine ⟨(hg l hl).1, ?_, (hg l hl).2⟩
    have e : gi[l]! = invT n gens[l]! := by
      rw [getElem!_pos gi l (by simpa [gi] using hl), getElem!_pos gens l hl, Array.getElem_map]
    rw [e]
    refine Rep.inv_of_invOK (hg l hl).1 ?_
    rw [getElem!_pos gens l hl]
    exact hgi l hl
  have hsz : hT.size = hw.length := by simp [hT]
  have hex : ∀ i, ∃ g : Equiv.Perm (Fin n), i < hT.size → g ∈ K ∧ Rep n hT[i]! g := by
    intro i
    by_cases hi : i < hT.size
    · have e : hT[i]! = wordT n (letterTab gens gi) hw[i]! := by
        rw [getElem!_pos hT i hi]
        simp [hT, getElem!_pos hw i (by omega)]
      obtain ⟨g, hgK, hgR⟩ := rep_wordTables hn K hg'
        (lettersOK_spec (hhw hw[i]! (by
          rw [getElem!_pos hw i (by omega)]
          exact List.getElem_mem _)))
      exact ⟨g, fun _ => ⟨hgK, e ▸ hgR⟩⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose hh hhs using hex
  have hHi : ∀ i < hT.size, Rep n hTi[i]! (hh i)⁻¹ := by
    intro i hi
    exact Rep.inv_of_invOK (hhs i hi).2 (hH i hi).1
  have hpow : ∀ i < hT.size, hh i ^ p = 1 := by
    intro i hi
    have hl : ∀ l ∈ List.replicate p ((i : ℤ) + 1),
        Rep n (letterTab hT hTi l) (letterG hh l) := by
      intro l hlm
      rw [List.eq_of_mem_replicate hlm]
      have h0 : (0 : ℤ) < (i : ℤ) + 1 := by omega
      have h1 : ((i : ℤ) + 1).toNat - 1 = i := by omega
      simp only [letterTab, letterG, h0, ite_true, h1]
      exact (hhs i hi).2
    have hR := Rep.wordT hn _ hl
    rw [wordG, List.map_replicate, List.prod_replicate] at hR
    have h0 : (0 : ℤ) < (i : ℤ) + 1 := by omega
    have h1 : ((i : ℤ) + 1).toNat - 1 = i := by omega
    simp only [letterG, h0, ite_true, h1] at hR
    exact (tblEq_idT_iff hn hR).1 (hH i hi).2
  have hcomm : ∀ i < hT.size, hh i * (x : Equiv.Perm (Fin n)) = x * hh i := by
    intro i hi
    have := commute_of_card_isConj_le (x := x) (h := ⟨hh i, (hhs i hi).1⟩) hp h5
      (Subtype.ext (by simpa using hpow i hi)) hle
    exact congrArg Subtype.val this
  have hg'' : ∀ l < hT.size, Rep n hT[l]! (hh l) ∧ Rep n hTi[l]! (hh l)⁻¹ ∧
      hh l ∈ Subgroup.centralizer {(x : Equiv.Perm (Fin n))} :=
    fun l hl => ⟨(hhs l hl).2, hHi l hl, Subgroup.mem_centralizer_singleton_iff.2 (hcomm l hl)⟩
  have hx1 : (x : Equiv.Perm (Fin n)) ^ 2 = 1 := by
    refine hfix _ (K.pow_mem x.2 2) fun q hq hb => ?_
    rw [pow_two, Equiv.Perm.mul_apply]
    exact sq_fix_of_basePtOK hn hg'' (hpts q hq) hb
  exact hx2 (Subtype.ext (by simpa using hx1))

end CFSG.EvenSporadicStandard.TwoRu.HypOne
