module

public import CFSG.GF2Type.SmithTypeE.L6.ModConj
public import CFSG.GF2Type.SmithTypeE.L6Ident.StabOrbit
public import CFSG.LargeExtraspecial.S14SMGCert
public import Certificates.Certificate38652

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open CFSG.SmithL6 CFSG.GF2Type.SmithTypeE.LMod
open CFSG.SmithE (applyCols SpanData spanData gensOf)
open CFSG.LargeExtraspecial.SMod20 (V decode decode_xor decode_zero eq_of_decode_eq
  linearEquiv_ext_single)
open CFSG.LargeExtraspecial.S14.SMG (applyCols_lt code_lt comm_eq_basis' syn_comm' syn_basis'
  gensOf_get)

theorem pair0Check_holds : mfChkPair0 = true :=
  Certificates.certificate38652.1

theorem span6Check_holds : mfChkSpan = true :=
  Certificates.certificate38652.2.1

theorem int0Check_holds : mfChkInt0 = true :=
  Certificates.certificate38652.2.2

section Trans


theorem exists_T6_zero (k : Fin 1953) : ∃ g : T6, (g : Equiv.Perm (Fin 1953)) 0 = k := by
  obtain ⟨g, hg, hgk⟩ := L6Ident.exists_mem_T6_apply_zero_eq k
  exact ⟨⟨g, hg⟩, hgk⟩

end Trans

section BaseRel


theorem relC_of_commuteB {k l : Nat} (hk : k < 1953) (hl : l < 1953)
    (h : mfCommuteB (tvCols k) (tvCols l) = true) : RelC (tvEquiv k) (tvEquiv l) := by
  apply linearEquiv_ext_single
  intro m
  have h' := (List.all_eq_true.mp h) m.val (List.mem_range.mpr m.2)
  simp only [LinearEquiv.mul_apply, tvEquiv_single hk, tvEquiv_single hl, tvEquiv_decode hk,
    tvEquiv_decode hl]
  exact congrArg decode (beq_iff_eq.mp h')

theorem relB_of_braidB {k l : Nat} (hk : k < 1953) (hl : l < 1953)
    (h : mfBraidB (tvCols k) (tvCols l) = true) : RelB (tvEquiv k) (tvEquiv l) := by
  apply linearEquiv_ext_single
  intro m
  have h' := (List.all_eq_true.mp h) m.val (List.mem_range.mpr m.2)
  simp only [LinearEquiv.mul_apply, tvEquiv_single hk, tvEquiv_single hl, tvEquiv_decode hk,
    tvEquiv_decode hl]
  exact congrArg decode (beq_iff_eq.mp h')

theorem relD_of_dihB {k l : Nat} (hk : k < 1953) (hl : l < 1953)
    (h : mfDihB (tvCols k) (tvCols l) = true) : RelD (tvEquiv k) (tvEquiv l) := by
  apply linearEquiv_ext_single
  intro m
  have h' := (List.all_eq_true.mp h) m.val (List.mem_range.mpr m.2)
  simp only [LinearEquiv.mul_apply, tvEquiv_single hk, tvEquiv_single hl, tvEquiv_decode hk,
    tvEquiv_decode hl]
  exact congrArg decode (beq_iff_eq.mp h')

end BaseRel

theorem mfPairKind_cases (k l : Nat) :
    mfPairKind k l = 0 ∨ mfPairKind k l = 1 ∨ mfPairKind k l = 2 := by
  simp only [mfPairKind]
  split_ifs <;> simp

section Pair


theorem pair0_kind (l : Fin 1953) :
    (mfPairKind 0 l.val = 0 → RelC (tvE 0) (tvE l)) ∧
      (mfPairKind 0 l.val = 1 → RelB (tvE 0) (tvE l)) ∧
      (mfPairKind 0 l.val = 2 → RelD (tvE 0) (tvE l)) := by
  have h := pair0Check_holds
  simp only [mfChkPair0, List.all_eq_true, List.mem_range] at h
  have hl := h l.val l.2
  have h0 : (0 : Nat) < 1953 := by norm_num
  refine ⟨fun hk => ?_, fun hk => ?_, fun hk => ?_⟩
  · rw [hk] at hl
    rw [tvArr_get h0, tvArr_get l.2] at hl
    exact relC_of_commuteB h0 l.2 hl
  · rw [hk] at hl
    rw [tvArr_get h0, tvArr_get l.2] at hl
    exact relB_of_braidB h0 l.2 hl
  · rw [hk] at hl
    rw [tvArr_get h0, tvArr_get l.2] at hl
    exact relD_of_dihB h0 l.2 hl

theorem pair_kind_conj (g : T6) (l : Fin 1953) :
    (mfPairKind 0 l.val = 0 →
      RelC (tvE ((g : Equiv.Perm (Fin 1953)) 0)) (tvE ((g : Equiv.Perm (Fin 1953)) l))) ∧
    (mfPairKind 0 l.val = 1 →
      RelB (tvE ((g : Equiv.Perm (Fin 1953)) 0)) (tvE ((g : Equiv.Perm (Fin 1953)) l))) ∧
    (mfPairKind 0 l.val = 2 →
      RelD (tvE ((g : Equiv.Perm (Fin 1953)) 0)) (tvE ((g : Equiv.Perm (Fin 1953)) l))) := by
  obtain ⟨h0, h1, h2⟩ := pair0_kind l
  exact ⟨fun h => relC_tvE g (h0 h), fun h => relB_tvE g (h1 h), fun h => relD_tvE g (h2 h)⟩

end Pair

section General


theorem pair_general (k l : Fin 1953) :
    RelC (tvE k) (tvE l) ∨ RelB (tvE k) (tvE l) ∨ RelD (tvE k) (tvE l) := by
  obtain ⟨g, hg⟩ := exists_T6_zero k
  obtain ⟨l', hl'⟩ : ∃ l' : Fin 1953, (g : Equiv.Perm (Fin 1953)) l' = l :=
    ⟨(g : Equiv.Perm (Fin 1953))⁻¹ l, by simp⟩
  subst hg hl'
  obtain ⟨h0, h1, h2⟩ := pair_kind_conj g l'
  rcases mfPairKind_cases 0 l'.val with h | h | h
  · exact Or.inl (h0 h)
  · exact Or.inr (Or.inl (h1 h))
  · exact Or.inr (Or.inr (h2 h))

theorem kind_two_of_not (g : T6) (l' : Fin 1953)
    (hC : ¬ RelC (tvE ((g : Equiv.Perm (Fin 1953)) 0)) (tvE ((g : Equiv.Perm (Fin 1953)) l')))
    (hB : ¬ RelB (tvE ((g : Equiv.Perm (Fin 1953)) 0)) (tvE ((g : Equiv.Perm (Fin 1953)) l'))) :
    mfPairKind 0 l'.val = 2 := by
  obtain ⟨h0, h1, -⟩ := pair_kind_conj g l'
  rcases mfPairKind_cases 0 l'.val with h | h | h
  · exact absurd (h0 h) hC
  · exact absurd (h1 h) hB
  · exact h

end General

theorem mfSpanArr_get {k : Nat} (hk : k < 1953) : mfSpanArr[k]! = spanData (tvCols k) := by
  simp [mfSpanArr, getElem!_pos, hk, tvArr]

theorem mfIsWt_spec {v : Nat} (h : mfIsWt v = true) : ∃ j < 1395, wt j = v := by
  simp only [mfIsWt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨_, h.1, by rw [← wtArr_get h.1]; exact h.2⟩

section Span


theorem span6_parts {k : Nat} (hk : k < 1953) :
    (spanData (tvCols k)).basis.size = 6 ∧ (spanData (tvCols k)).coef.size = 20 ∧
    ∀ m < 20, (spanData (tvCols k)).coef[m]! < 64 ∧
      applyCols (spanData (tvCols k)).basis (spanData (tvCols k)).coef[m]! =
        (tvCols k)[m]! ^^^ 2 ^ m ∧
      applyCols (spanData (tvCols k)).syn ((tvCols k)[m]! ^^^ 2 ^ m) = 0 := by
  have hS := span6Check_holds
  simp only [mfChkSpan, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hS
  obtain ⟨⟨h1, h2⟩, h3⟩ := hS k hk
  rw [mfSpanArr_get hk] at h1 h2 h3
  rw [tvArr_get hk] at h3
  refine ⟨h1, h2, fun m hm => ?_⟩
  obtain ⟨⟨h4, h5⟩, h6⟩ := h3 m hm
  rw [gensOf_get _ hm] at h5 h6
  exact ⟨h4, h5, h6⟩

theorem int0_code {l : Nat} (hl : l < 1953) (hl0 : l ≠ 0) {c c' : Nat} (hc : c < 2 ^ 20)
    (hc' : c' < 2 ^ 20) (h : applyCols (tvCols 0) c ^^^ c = applyCols (tvCols l) c' ^^^ c') :
    applyCols (tvCols 0) c ^^^ c = 0 ∨
      (mfPairKind 0 l = 0 ∧ ∃ j < 1395, wt j = applyCols (tvCols 0) c ^^^ c) := by
  have h0 : (0 : Nat) < 1953 := by norm_num
  obtain ⟨hbk, hck, hk3⟩ := span6_parts h0
  obtain ⟨-, -, hl3⟩ := span6_parts hl
  set Dk := spanData (tvCols 0)
  set Dl := spanData (tvCols l)
  set d := applyCols Dk.coef c
  have hd64 : d < 2 ^ 6 := applyCols_lt (fun m hm => (hk3 m (by omega)).1) c
  have hv : applyCols (tvCols 0) c ^^^ c = applyCols Dk.basis d :=
    comm_eq_basis' (size_tvCols 0) hck (fun m hm => (hk3 m hm).2.1) hc
  have hsyn : applyCols Dl.syn (applyCols Dk.basis d) = 0 := by
    rw [← hv, h]
    exact syn_comm' (size_tvCols l) (fun m hm => (hl3 m hm).2.2) hc'
  have hI := int0Check_holds
  simp only [mfChkInt0, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    bne_iff_ne, ne_eq, beq_iff_eq, Bool.and_eq_true] at hI
  rcases hI l hl with h1 | h1
  · exact absurd h1 hl0
  rw [mfSpanArr_get h0, mfSpanArr_get hl] at h1
  have hSd := syn_basis' (E := Dl) hbk hd64
  rcases h1 d hd64 with h2 | h2
  · exact absurd (hSd.trans hsyn) h2
  · rw [hv]
    rcases h2 with h3 | ⟨h3, h4⟩
    · exact Or.inl h3
    · exact Or.inr ⟨h3, mfIsWt_spec h4⟩

end Span

@[expose] def IntV (a b : V ≃ₗ[ZMod 2] V) : Prop :=
  ∀ u : V, InEV a u → InEV b u → u = 0 ∨ (RelC a b ∧ ∃ j : Fin 1395, u = wtV j.val)

section Int


theorem intV_base (l : Fin 1953) (hl : l ≠ 0) : IntV (tvE 0) (tvE l) := by
  rintro u ⟨x, hx⟩ ⟨y, hy⟩
  have h0 : (0 : Nat) < 1953 := by norm_num
  have hl0 : l.val ≠ 0 := fun h => hl (Fin.ext h)
  have hxc : decode (CFSG.LargeExtraspecial.S14.SMG.code x) = x := decode_code x
  have hyc : decode (CFSG.LargeExtraspecial.S14.SMG.code y) = y := decode_code y
  set c := CFSG.LargeExtraspecial.S14.SMG.code x with hc
  set c' := CFSG.LargeExtraspecial.S14.SMG.code y with hc'
  have hc20 : c < 2 ^ 20 := code_lt x
  have hc20' : c' < 2 ^ 20 := code_lt y
  have e1 : decode (applyCols (tvCols 0) c ^^^ c) = u := by
    rw [decode_xor, ← tvEquiv_decode h0 c, hxc, hx]
    rfl
  have e2 : decode (applyCols (tvCols l.val) c' ^^^ c') = u := by
    rw [decode_xor, ← tvEquiv_decode l.2 c', hyc, hy]
    rfl
  have hbd1 : applyCols (tvCols 0) c ^^^ c < 2 ^ 20 :=
    Nat.xor_lt_two_pow (n := 20) (applyCols_tv_lt h0 c) hc20
  have hbd2 : applyCols (tvCols l.val) c' ^^^ c' < 2 ^ 20 :=
    Nat.xor_lt_two_pow (n := 20) (applyCols_tv_lt l.2 c') hc20'
  have heq := eq_of_decode_eq hbd1 hbd2 (e1.trans e2.symm)
  rcases int0_code l.2 hl0 hc20 hc20' heq with hz | ⟨hk, j, hj, hjw⟩
  · left
    rw [← e1, hz, decode_zero]
  · right
    refine ⟨(pair0_kind l).1 hk, ⟨j, hj⟩, ?_⟩
    rw [← e1, ← hjw]
    rfl

theorem intV_smul (g : T6) {k l : Fin 1953} (h : IntV (tvE k) (tvE l)) :
    IntV (tvE ((g : Equiv.Perm (Fin 1953)) k)) (tvE ((g : Equiv.Perm (Fin 1953)) l)) := by
  intro u hu hu'
  have hu_eq : u = rhoMod g ((rhoMod g).symm u) := ((rhoMod g).apply_symm_apply u).symm
  rw [hu_eq] at hu hu' ⊢
  have h1 := (inEV_tvE_smul g k _).mp hu
  have h2 := (inEV_tvE_smul g l _).mp hu'
  rcases h _ h1 h2 with h0 | ⟨hc, j, hj⟩
  · left
    rw [h0, map_zero]
  · right
    refine ⟨relC_tvE g hc, g • j, ?_⟩
    rw [hj, rhoMod_wtV]

theorem intV_general (k l : Fin 1953) (hkl : k ≠ l) : IntV (tvE k) (tvE l) := by
  obtain ⟨g, hg⟩ := exists_T6_zero k
  obtain ⟨l', hl'⟩ : ∃ l' : Fin 1953, (g : Equiv.Perm (Fin 1953)) l' = l :=
    ⟨(g : Equiv.Perm (Fin 1953))⁻¹ l, by simp⟩
  subst hg hl'
  have hl0 : l' ≠ 0 := fun h => hkl (by rw [h])
  exact intV_smul g (intV_base l' hl0)

end Int

end CFSG.GF2Type.SmithTypeE.L6
