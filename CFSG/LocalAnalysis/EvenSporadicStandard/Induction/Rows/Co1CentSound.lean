module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundSpin
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundSmall
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundLetters
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1PairK
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCRow
public import Certificates.Certificate27207
public import Certificates.Certificate27208

public noncomputable section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Co1Cent

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2
  CFSG.EvenSporadicStandard.Co1Pair

section Elts

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native
  CFSG.EvenSporadicStandard.Induction.AutBound.Spin


theorem centOK_parts (h : centOK = true) :
    sWords.length = 6 ∧ mul cpX (inv cpX) = one ∧ mul cpY (inv cpY) = one ∧
      spinOK centData = true := by
  unfold centOK at h
  obtain ⟨h, c4⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, c3⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨c1, c2⟩ := Eq.mp (Bool.and_eq_true _ _) h
  exact ⟨beq_iff_eq.1 c1, beq_iff_eq.1 c2, beq_iff_eq.1 c3, c4⟩

@[expose] noncomputable def sElt (j : ℕ) : C₁ := wordM [px', py] (sWords.getD j [])

theorem sElt_mem_K₁ (j : ℕ) : sElt j ∈ K₁ := by
  refine wordM_mem K₁ _ ?_ _
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem rep_sElt (hx : mul cpX (inv cpX) = one) (hy : mul cpY (inv cpY) = one)
    (hw : sWords.length = 6) {j : ℕ} (hj : j < 6) :
    MRep (sRows.getD j #[]) (ιC (sElt j)) := by
  have hl : ListRep [cpX, cpY] [inv cpX, inv cpY] [ιC px', ιC py] :=
    ⟨List.Forall₂.cons rep_px' (List.Forall₂.cons rep_py List.Forall₂.nil),
      List.Forall₂.cons (MRep.inv rep_px' hx)
        (List.Forall₂.cons (MRep.inv rep_py hy) List.Forall₂.nil)⟩
  have h1 := MRep.word hl (sWords.getD j [])
  have h2 : ιC (sElt j) = wordG [ιC px', ιC py] (sWords.getD j []) :=
    map_wordM ιC [px', py] _
  have hj' : j < sWords.length := by rw [hw]; exact hj
  have h3 : sRows.getD j #[] = word [cpX, cpY] [inv cpX, inv cpY] (sWords.getD j []) := by
    unfold sRows
    simp [List.getD_eq_getElem?_getD, hj']
  rw [h3, h2]
  exact h1

theorem cent_spin {g : GL24}
    (hg : ∀ j < 6, g * ιC (sElt j) = ιC (sElt j) * g) :
    ∃ x < 2 ^ centData.wcols.length,
      (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) = rowsMatrix 24 (cx x) := by
  obtain ⟨hw, hx, hy, hspin⟩ := centOK_parts Certificates.certificate27207
  have hlen : centData.rs.length = 6 := by
    show sRows.length = 6
    simp [sRows, hw]
  refine CFSG.EvenSporadicStandard.Induction.AutBound.Spin.spin_sound' centData hspin
    (n := 24) rfl (g := (g : Matrix (Fin 24) (Fin 24) (ZMod 2))) ?_
  intro k hk
  rw [hlen] at hk
  have hrep := rep_sElt hx hy hw hk
  have hg' := congrArg Units.val (hg k hk)
  rw [Units.val_mul, Units.val_mul] at hg'
  show _ * rowsMatrix 24 (sRows.getD k #[]) = rowsMatrix 24 (sRows.getD k #[]) * _
  rw [hrep]
  exact hg'

end Elts


section Class

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native
  CFSG.EvenSporadicStandard.Induction.AutBound.Spin

theorem classOK_parts (h : classOK = true) :
    centData.wcols.length = 6 ∧ gdX.length = 12 ∧ (∀ x ∈ gdX, x < 64) ∧
    (∀ G ∈ gdRows, validR 24 G = true ∧ validR 24 (inv G) = true) ∧
    (∀ G ∈ gdRows, mul G (inv G) = one) ∧
    (∀ G ∈ gdRows, mul G G = one ∨ mul (mul G G) G = one) ∧
    (∀ G ∈ gdRows, ∀ H ∈ gdRows, mul G G = one → mul H H = one → mul G H = mul H G) ∧
    (gdRows.filter fun G => mul G G == one).length ≤ 4 ∧
    (∀ G ∈ gdRows, ∀ H ∈ gdRows,
      mul (mul (mul (mul G H) (inv G)) (inv H)) (mul (mul (mul G H) (inv G)) (inv H)) = one) ∧
    ∀ x < 64, x ∈ gdX ∨ (∃ r ∈ singRecs, r.1 = x ∧ singOK x r.2 = true) ∨
      ∃ r ∈ exclRecs, r.1 = x ∧ exclOK x r.2.1 r.2.2 = true := by
  unfold classOK at h
  obtain ⟨h, c10⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, c9⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, c8⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, c7⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, c6⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, c5⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, c4⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, c3⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨c1, c2⟩ := Eq.mp (Bool.and_eq_true _ _) h
  refine ⟨beq_iff_eq.1 c1, beq_iff_eq.1 c2, fun x hx => ?_, fun G hG => ?_, fun G hG => ?_,
    fun G hG => ?_, fun G hG H hH hGG hHH => ?_, of_decide_eq_true c8, fun G hG H hH => ?_,
    fun x hx => ?_⟩
  · exact of_decide_eq_true (List.all_eq_true.1 c3 x hx)
  · exact Eq.mp (Bool.and_eq_true _ _) (List.all_eq_true.1 c4 G hG)
  · exact beq_iff_eq.1 (List.all_eq_true.1 c5 G hG)
  · rcases Eq.mp (Bool.or_eq_true _ _) (List.all_eq_true.1 c6 G hG) with h | h
    · exact Or.inl (beq_iff_eq.1 h)
    · exact Or.inr (beq_iff_eq.1 h)
  · have := List.all_eq_true.1 (List.all_eq_true.1 c7 G hG) H hH
    have hGG' : (mul G G == one) = true := beq_iff_eq.2 hGG
    have hHH' : (mul H H == one) = true := beq_iff_eq.2 hHH
    rcases Eq.mp (Bool.or_eq_true _ _) this with h | h
    · rw [hGG', hHH'] at h
      exact absurd h (by decide)
    · exact beq_iff_eq.1 h
  · exact beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 c9 G hG) H hH)
  · have hx' : x ∈ List.range 64 := List.mem_range.2 hx
    have := List.all_eq_true.1 c10 x hx'
    rcases Eq.mp (Bool.or_eq_true _ _) this with h | h
    · rcases Eq.mp (Bool.or_eq_true _ _) h with h1 | h2
      · exact Or.inl (by simpa using h1)
      · obtain ⟨r, hr, hr'⟩ := List.any_eq_true.1 h2
        obtain ⟨hr1, hr2⟩ := Eq.mp (Bool.and_eq_true _ _) hr'
        exact Or.inr (Or.inl ⟨r, hr, beq_iff_eq.1 hr1, hr2⟩)
    · obtain ⟨r, hr, hr'⟩ := List.any_eq_true.1 h
      obtain ⟨hr1, hr2⟩ := Eq.mp (Bool.and_eq_true _ _) hr'
      exact Or.inr (Or.inr ⟨r, hr, beq_iff_eq.1 hr1, hr2⟩)

end Class


section Excl

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native
  CFSG.EvenSporadicStandard.Induction.AutBound.Spin

theorem isPerfect_of_comm_eq {G : Type*} [Group G] {K : Subgroup G} (h : ⁅K, K⁆ = K) :
    Group.IsPerfect ↥K := by
  refine Group.isPerfect_def.2 (Subgroup.map_injective K.subtype_injective ?_)
  rw [Subgroup.map_subtype_commutator, h, Subgroup.map_top, Subgroup.range_subtype]

theorem singOK_parts {x u : ℕ} (h : singOK x u = true) :
    u ≠ 0 ∧ u < 2 ^ 24 ∧ act (cx x) u = 0 := by
  unfold singOK at h
  obtain ⟨h, c3⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨c1, c2⟩ := Eq.mp (Bool.and_eq_true _ _) h
  exact ⟨of_decide_eq_true c1, of_decide_eq_true c2, beq_iff_eq.1 c3⟩

theorem exclOK_parts {x e u : ℕ} (h : exclOK x e u = true) :
    mul (pow (cx x) e) aR = mul aR (pow (cx x) e) ∧
      triTrivial (transposeRows 24 (pow (cx x) e)) = true ∧
      act cpX (act (pow (cx x) e) u) < 2 ^ 24 ∧ act (pow (cx x) e) (act cpX u) < 2 ^ 24 ∧
      act cpX (act (pow (cx x) e) u) ≠ act (pow (cx x) e) (act cpX u) := by
  unfold exclOK at h
  dsimp only at h
  obtain ⟨h, c5⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, c4⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, c3⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨c1, c2⟩ := Eq.mp (Bool.and_eq_true _ _) h
  exact ⟨beq_iff_eq.1 c1, c2, of_decide_eq_true c3, of_decide_eq_true c4, bne_iff_ne.1 c5⟩

theorem triTrivial_spec {Ct : Array ℕ} (h : triTrivial Ct = true) :
    ∀ p ∈ twoBTris, vecMulN 24 Ct p.1 = p.1 ∨ vecMulN 24 Ct p.1 = p.2 ∨
      vecMulN 24 Ct p.1 = (p.1 ^^^ p.2) := by
  intro p hp
  have := List.all_eq_true.1 h p hp
  rcases Eq.mp (Bool.or_eq_true _ _) this with h1 | h3
  · rcases Eq.mp (Bool.or_eq_true _ _) h1 with h1 | h2
    · exact Or.inl (beq_iff_eq.1 h1)
    · exact Or.inr (Or.inl (beq_iff_eq.1 h2))
  · exact Or.inr (Or.inr (beq_iff_eq.1 h3))

end Excl


section Main

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native
  CFSG.EvenSporadicStandard.Induction.AutBound.Spin


theorem K₁_facts :
    Group.IsPerfect ↥K₁ ∧ Nat.card ↥K₁ = Nat.card twoBD := by
  have : IsSimpleGroup ↥twoBD := isSimpleGroup_twoBD
  have hD : ⁅twoBD, twoBD⁆ = twoBD := by
    have hc : commutator ↥twoBD = ⊤ :=
      commutator_eq_top_of_simple (D := ↥twoBD) (hna := ⟨xD, yD, xD_yD_ne⟩)
    rw [← Subgroup.map_subtype_commutator, hc, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨h1, h2⟩ := perfect_of_map_eq triHom K₁ twoBD map_K₁ hD card_K₁_le
  exact ⟨isPerfect_of_comm_eq h1, h2⟩

theorem ker_comm_px' {c : C₁} (hc : c ∈ (triHom : C₁ →* _).ker) :
    ιC px' * ιC c = ιC c * ιC px' := by
  obtain ⟨hp, hcard⟩ := K₁_facts
  have h := CFSG.EvenSporadicStandard.Solomon78.co1_quot2Data.comm_ker hp hcard
    (Subgroup.subset_closure (Set.mem_insert _ _) : px' ∈ K₁) hc
  rw [← map_mul, ← map_mul, h]

end Main


section Class2

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native
  CFSG.EvenSporadicStandard.Induction.AutBound.Spin


theorem cent_class
    {g : GL24} (hgA : g ∈ GA)
    (hg : ∀ j < 6, g * ιC (sElt j) = ιC (sElt j) * g) :
    ∃ k < 12, (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
      rowsMatrix 24 (gdRows.getD k #[]) := by
  obtain ⟨x, hxlt, hx⟩ := cent_spin hg
  obtain ⟨hw, hlen, hbd, hval, hinv, hF1, hF2, hcnt, hF3, hcov⟩ :=
    classOK_parts Certificates.certificate27208
  have hx64 : x < 64 := by
    have : x < 2 ^ 6 := by rwa [hw] at hxlt
    simpa using this
  have hrep : MRep (cx x) g := hx.symm
  rcases hcov x hx64 with hgd | ⟨r, hr, hr1, hr2⟩ | ⟨r, hr, hr1, hr2⟩
  · obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.1 hgd
    refine ⟨k, by rw [← hlen]; exact hk, ?_⟩
    have : gdRows.getD k #[] = cx x := by
      simp [gdRows, List.getD_eq_getElem?_getD, hk, hkx]
    rw [this, hx]
  · exfalso
    obtain ⟨hu0, hu24, hact⟩ := singOK_parts hr2
    have hmv := MRep.mulVec hrep r.2
    rw [hact, toVecD_zero] at hmv
    have h1 : toVecD 24 r.2 = 0 := by
      have := congrArg (fun v => ((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)).mulVec v) hmv
      simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this
    exact hu0 (toVecD_injective hu24 (by norm_num) (h1.trans (toVecD_zero 24).symm))
  · exfalso
    obtain ⟨x', e, u⟩ := r
    simp only at hr1 hr2
    subst hr1
    obtain ⟨hA, hB, hlt1, hlt2, hne⟩ := exclOK_parts hr2
    have hrepc : MRep (pow (cx x') e) (g ^ e) := MRep.pow hrep e
    have hĝA : g ^ e ∈ GA := pow_mem hgA e
    have hAcomm : g ^ e * A₁ = A₁ * g ^ e :=
      MRep.eq (hrepc.mul rep_A₁) (by rw [hA]; exact rep_A₁.mul hrepc)
    have hmem : g ^ e ∈ Subgroup.centralizer ({A₁} : Set GL24) :=
      Subgroup.mem_centralizer_singleton_iff.2 hAcomm
    have hcent : (⟨g ^ e, hĝA⟩ : GA) ∈ C₁ := mem_C₁_of hmem
    let cC : C₁ := ⟨⟨g ^ e, hĝA⟩, hcent⟩
    have htri : triHom cC = 1 := by
      refine Equiv.ext fun k => ?_
      rw [triHom_apply, Equiv.Perm.one_apply]
      refine triAct_eq ?_
      have hk : (k : ℕ) < 1365 := k.2
      have hp := triTrivial_spec hB (triP k) (triP_mem hk)
      refine ⟨act (pow (cx x') e) (triP k).1, ?_, ?_⟩
      · rw [inTriN_iff]
        exact hp
      · exact MRep.mulVec hrepc (triP k).1
    have hker : cC ∈ (triHom : C₁ →* Equiv.Perm (Fin 1365)).ker := MonoidHom.mem_ker.2 htri
    have hcomm := ker_comm_px' hker
    have hcc : (ιC cC : GL24) = g ^ e := rfl
    rw [hcc] at hcomm
    have hmat := congrArg Units.val hcomm
    rw [Units.val_mul, Units.val_mul] at hmat
    have v1 : (((ιC px' : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
        ((g ^ e : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2))).mulVec (toVecD 24 u) =
        toVecD 24 (act cpX (act (pow (cx x') e) u)) := by
      rw [← Matrix.mulVec_mulVec, MRep.mulVec hrepc, MRep.mulVec rep_px']
    have v2 : (((g ^ e : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
        ((ιC px' : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2))).mulVec (toVecD 24 u) =
        toVecD 24 (act (pow (cx x') e) (act cpX u)) := by
      rw [← Matrix.mulVec_mulVec, MRep.mulVec rep_px', MRep.mulVec hrepc]
    rw [hmat] at v1
    exact hne (toVecD_injective hlt1 hlt2 (v1.symm.trans v2))

end Class2


section Small

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native
  CFSG.EvenSporadicStandard.Induction.AutBound.Spin

@[expose] def GdSet : Set GL24 :=
  {g | ∃ k < 12, (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) = rowsMatrix 24 (gdRows.getD k #[])}

theorem gdRows_length : gdRows.length = gdX.length := by simp [gdRows]

theorem gdSet_small :
    (∀ g ∈ GdSet, g * g = 1 ∨ g * g * g = 1) ∧
    (∀ a ∈ GdSet, ∀ b ∈ GdSet, a * a = 1 → b * b = 1 → a * b = b * a) ∧
    (∀ a ∈ GdSet, ∀ b ∈ GdSet, (a * b * a⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹) = 1) ∧
    {g ∈ GdSet | g * g = 1}.Finite ∧ {g ∈ GdSet | g * g = 1}.ncard ≤ 4 := by
  classical
  obtain ⟨hw, hlen, hbd, hval, hinv, hF1, hF2, hcnt, hF3, hcov⟩ :=
    classOK_parts Certificates.certificate27208
  have hlen' : gdRows.length = 12 := by rw [gdRows_length, hlen]
  have hex : ∀ g ∈ GdSet, ∃ G ∈ gdRows, MRep G g := by
    rintro g ⟨k, hk, hkg⟩
    refine ⟨gdRows.getD k #[], ?_, hkg.symm⟩
    have : k < gdRows.length := by rw [hlen']; exact hk
    simp [List.getD_eq_getElem?_getD, this]
  have hone : ∀ {G : Array ℕ}, G ∈ gdRows → validR 24 G = true := fun {G} hG => (hval G hG).1
  have hsq : ∀ {G : Array ℕ} {a : GL24}, G ∈ gdRows → MRep G a → a * a = 1 → mul G G = one := by
    intro G a hG hrep ha
    have h1 := hrep.mul hrep
    rw [ha] at h1
    exact rowsMatrix_inj_of_valid (d := 24) (validR_mulRows (hone hG) (hone hG)) validR_idRows
      (h1.trans MRep.one.symm)
  have H1 : ∀ g ∈ GdSet, g * g = 1 ∨ g * g * g = 1 := by
    intro g hg
    obtain ⟨G, hG, hrep⟩ := hex g hg
    rcases hF1 G hG with h | h
    · left
      have := hrep.mul hrep
      rw [h] at this
      exact MRep.eq this MRep.one
    · right
      have := (hrep.mul hrep).mul hrep
      rw [h] at this
      exact MRep.eq this MRep.one
  have H2 : ∀ a ∈ GdSet, ∀ b ∈ GdSet, a * a = 1 → b * b = 1 → a * b = b * a := by
    intro a ha b hb haa hbb
    obtain ⟨G, hG, hra⟩ := hex a ha
    obtain ⟨H, hH, hrb⟩ := hex b hb
    have h := hF2 G hG H hH (hsq hG hra haa) (hsq hH hrb hbb)
    exact MRep.eq (hra.mul hrb) (by rw [h]; exact hrb.mul hra)
  have H3 : ∀ a ∈ GdSet, ∀ b ∈ GdSet, (a * b * a⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹) = 1 := by
    intro a ha b hb
    obtain ⟨G, hG, hra⟩ := hex a ha
    obtain ⟨H, hH, hrb⟩ := hex b hb
    have hGi := MRep.inv hra (hinv G hG)
    have hHi := MRep.inv hrb (hinv H hH)
    have hc := ((hra.mul hrb).mul hGi).mul hHi
    have := hc.mul hc
    rw [hF3 G hG H hH] at this
    exact MRep.eq this MRep.one
  refine ⟨H1, H2, H3, ?_⟩
  set Gq : List (Array ℕ) := gdRows.filter (fun G => mul G G == one) with hGq
  have hmem : ∀ g ∈ {g ∈ GdSet | g * g = 1},
      ∃ i : Fin Gq.length, (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) = rowsMatrix 24 (Gq.get i) := by
    rintro g ⟨hg, hgg⟩
    obtain ⟨G, hG, hrep⟩ := hex g hg
    have hGG := hsq hG hrep hgg
    have hmemq : G ∈ Gq := List.mem_filter.2 ⟨hG, by simpa using hGG⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 hmemq
    exact ⟨i, by rw [hi]; exact hrep.symm⟩
  let f : ↥{g ∈ GdSet | g * g = 1} → Fin Gq.length := fun g => (hmem g.1 g.2).choose
  have hf : Function.Injective f := by
    intro g g' h
    have h1 := (hmem g.1 g.2).choose_spec
    have h2 := (hmem g'.1 g'.2).choose_spec
    have h3 : (g.1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = g'.1 := by
      rw [h1, h2]
      show rowsMatrix 24 (Gq.get (f g)) = rowsMatrix 24 (Gq.get (f g'))
      rw [h]
    exact Subtype.ext (Units.ext h3)
  have hfin : Finite ↥{g ∈ GdSet | g * g = 1} := Finite.of_injective f hf
  refine ⟨Set.finite_coe_iff.1 hfin, ?_⟩
  rw [← Nat.card_coe_set_eq]
  calc Nat.card ↥{g ∈ GdSet | g * g = 1} ≤ Nat.card (Fin Gq.length) :=
        Nat.card_le_card_of_injective f hf
    _ = Gq.length := Nat.card_eq_fintype_card.trans (Fintype.card_fin _)
    _ ≤ 4 := hcnt

end Small


section Structure

open CFSG.Sporadic.Co1Schreier.Native CFSG.EvenSporadicStandard.Induction.AutBound


theorem cent_structure
    {X : Type*} [Group X] [Finite X] (Θ : X →* GL24)
    (hΘ : Function.Injective Θ) (hGA : ∀ x, Θ x ∈ GA)
    (hc : ∀ x, ∀ j < 6, Θ x * ιC (sElt j) = ιC (sElt j) * Θ x) :
    Group.IsSolvable X ∧ (Nat.card X).factorization 2 ≤ 2 ∧
      ∀ E : Subgroup X, (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 4 := by
  obtain ⟨H1, H2, H3, hfin, hcard⟩ := gdSet_small
  have hX : ∀ x, Θ x ∈ GdSet := fun x => cent_class (hGA x) (hc x)
  have hSq : ∀ g ∈ GdSet, g * g = 1 → g ∈ {g ∈ GdSet | g * g = 1} := fun g hg hgg => ⟨hg, hgg⟩
  refine ⟨smallSub_isSolvable Θ GdSet H2 H3 hΘ hX,
    smallSub_twoAdic_le Θ GdSet _ hSq hfin H1 hΘ hX (n := 2) (by simpa using hcard),
    fun E hE => ?_⟩
  exact (smallSub_elemBound Θ GdSet _ hSq hfin hΘ hX E hE).trans hcard

end Structure

end CFSG.EvenSporadicStandard.Co1Cent
