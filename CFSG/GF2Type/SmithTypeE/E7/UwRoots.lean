module

public import CFSG.GF2Type.SmithTypeE.E7.UwOrb
public import Certificates.Certificate38821

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 CFSG.GF2Type.SmithTypeE.DMod

attribute [local irreducible] planeImg planeImgM tvCols tvLin

section Cert

theorem uwE0Check_holds : uw7ChkE0 () = true := Certificates.certificate38821.1

theorem uwLeviCheck_holds : uw7ChkLevi () = true := Certificates.certificate38821.2.1

theorem uwBClsCheck_holds : uw7ChkBCls () = true := Certificates.certificate38821.2.2.1

theorem uwBCheck_holds : ∀ v < 75735, uw7InB (uw7E0 ()) v = true → Relation.ReflTransGen
    (fun a b => ∃ g < 30, uw7InB (uw7E0 ()) a = true ∧ uw7InB (uw7E0 ()) b = true ∧
      uw7BCls (uw7E0 ()) a = uw7BCls (uw7E0 ()) b ∧ planeImg (uw7LLines ())[g]! a = b)
    ((uw7BReps ())[uw7BCls (uw7E0 ()) v - 1]!) v :=
  Certificates.certificate38821.2.2.2.1

theorem uwWitCheck_holds : ∀ v < 75735, uw7InB (uw7E0 ()) v = true → uw7BCls (uw7E0 ()) v = 1 →
    ∃ k < 365211, (linePair k).1 &&& 63 = 0 ∧ (linePair k).2 &&& 63 = 0 ∧
      planeImgM (tvCols k) (uw7E0 ()) = v :=
  Certificates.certificate38821.2.2.2.2

theorem e0_unpack : uw7E0 () < 75735 ∧ fB (wt 0) (wt (uw7E0 ())) = true ∧
    ∀ i < 6, memR pbArr[uw7E0 ()]! ppArr[uw7E0 ()]! (eV i) = true := by
  have h := uwE0Check_holds
  simp only [uw7ChkE0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem levi_unpack : (uw7LLines ()).size = 30 ∧ ∀ g < 30, (uw7LLines ())[g]! < 365211 ∧
    planeImg (uw7LLines ())[g]! 0 = 0 ∧ planeImg (uw7LLines ())[g]! (uw7E0 ()) = uw7E0 () := by
  have h := uwLeviCheck_holds
  simp only [uw7ChkLevi, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun g hg => ?_⟩
  have hg' : g < (uw7LLines ()).size := by omega
  have := Array.all_eq_true'.mp h2 (uw7LLines ())[g] (Array.getElem_mem hg')
  rw [getElem!_pos (uw7LLines ()) g hg']
  simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] using this

theorem bcls_unpack :
    (∀ c < 3, (uw7BReps ())[c]! < 75735 ∧ uw7InB (uw7E0 ()) (uw7BReps ())[c]! = true ∧
      uw7BCls (uw7E0 ()) (uw7BReps ())[c]! = c + 1) ∧
    ∀ c < 3, ((List.range 75735).filter fun j => uw7InB (uw7E0 ()) j && uw7BCls (uw7E0 ()) j == c + 1).length =
      uw7BSizes[c]! := by
  have h := uwBClsCheck_holds
  simp only [uw7ChkBCls, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨-, h2⟩, h3⟩ := h
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · have := List.all_eq_true.mp h2 c (List.mem_range.mpr hc)
    simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] using this
  · have := List.all_eq_true.mp h3 c (List.mem_range.mpr hc)
    simpa only [beq_iff_eq] using this

end Cert

section E0

theorem snd_dec12_eq_zero_iff (c : ℕ) : (dec12 c).2 = 0 ↔ ∀ i < 6, c.testBit (6 + i) = false := by
  constructor
  · intro h i hi
    have h' := congrFun h ⟨i, hi⟩
    simp only [dec12, Pi.zero_apply] at h'
    by_contra hb
    rw [Bool.not_eq_false] at hb
    simp [hb] at h'
  · intro h
    funext j
    simp only [dec12, Pi.zero_apply]
    rw [h j.val j.isLt]
    simp

theorem enc12_lt_64 {x : V12} (hx : x.2 = 0) : enc12 x < 64 := by
  have hc0 : (dec12 (enc12 x)).2 = 0 := by
    rw [dec12_enc12]
    exact hx
  have hbits := (snd_dec12_eq_zero_iff _).1 hc0
  apply Nat.lt_pow_two_of_testBit (n := 6)
  intro i hi
  by_cases hi' : i < 12
  · have := hbits (i - 6) (by omega)
    rwa [show 6 + (i - 6) = i by omega] at this
  · have h12 : (4096 : ℕ) ≤ 2 ^ i := by
      calc (4096 : ℕ) = 2 ^ 12 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (enc12_lt x) h12)

def eBasis : Array ℕ := #[1, 2, 4, 8, 16, 32]

theorem xorComb_eBasis (d : ℕ) (hd : d < 64) : xorComb eBasis d = d := by
  have key : ∀ e : Fin 64, xorComb eBasis e.val = e.val := by decide
  exact key ⟨d, hd⟩

theorem mem_planeSpan_of_snd_zero {B P : Array ℕ} (hB : ∀ i < 6, memR B P (eV i) = true)
    {x : V12} (hx : x.2 = 0) : x ∈ planeSpan B := by
  have hlt := enc12_lt_64 hx
  have hmem : x ∈ planeSpan eBasis := by
    rw [mem_planeSpan_iff]
    exact ⟨enc12 x, hlt, by rw [xorComb_eBasis _ hlt, dec12_enc12]⟩
  have hle : planeSpan eBasis ≤ planeSpan B := by
    unfold planeSpan
    rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    have h1 : eBasis[m.val]! = eV m.val := by
      have key : ∀ m : Fin 6, eBasis[m.val]! = eV m.val := by decide
      exact key m
    show dec12 eBasis[m.val]! ∈ planeSpan B
    rw [h1]
    exact dec12_mem_planeSpan_of_memR (hB m.val m.isLt)
  exact hle hmem

@[expose] noncomputable def E0 : Fin 75735 := ⟨uw7E0 (), e0_unpack.1⟩

theorem opp_zero_E0 : Opp 0 E0.val :=
  (opp_iff_fB (by norm_num) E0.2).2 e0_unpack.2.1

theorem mem_planeSub_E0 {x : V12} (hx : x.2 = 0) : x ∈ planeSub E0.val :=
  mem_planeSpan_of_snd_zero e0_unpack.2.2 hx

theorem K0_eq_one_of_smul_E0 {u : TD6} (hu : u ∈ K0) (h : u • E0 = E0) : u = 1 := by
  have hF := fixesF_of_mem_K0 hu
  have hσ := iso_symm u
  have hm := map_planeSub_smul u E0
  rw [h] at hm
  have hfix : ∀ a b : Fin 6 → ZMod 2, (omegaTD6.symm u).1 (a, b) = (a, b) := by
    intro a b
    rw [fix_apply hσ hF]
    have h1 : ((a, 0) : V12) ∈ planeSub E0.val := mem_planeSub_E0 rfl
    have h2 : (omegaTD6.symm u).1 (a, 0) ∈ planeSub E0.val := by
      rw [← hm]
      exact ⟨(a, 0), h1, rfl⟩
    have h3 : (omegaTD6.symm u).1 (a, 0) - (a, 0) ∈ planeSub E0.val := Submodule.sub_mem _ h2 h1
    have h4 : (omegaTD6.symm u).1 (a, 0) - (a, 0) =
        ((0 : Fin 6 → ZMod 2), ((omegaTD6.symm u).1 (a, 0)).2) := by
      rw [fix_apply hσ hF a 0]
      refine Prod.ext ?_ ?_
      · simp
      · simp
    rw [h4] at h3
    have h5 : ((0 : Fin 6 → ZMod 2), ((omegaTD6.symm u).1 (a, 0)).2) ∈ planeSub 0 :=
      mem_F_iff.mpr rfl
    have h6 := (Submodule.disjoint_def.1 opp_zero_E0) _ h5 h3
    have h7 : ((omegaTD6.symm u).1 (a, 0)).2 = 0 := congrArg Prod.snd h6
    rw [h7, add_zero]
  apply omegaTD6.symm.injective
  rw [map_one]
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  exact hfix x.1 x.2

theorem inB_smul_E0 {u : TD6} (hu : u ∈ K0) (hu1 : u ≠ 1) :
    uw7InB (uw7E0 ()) ((u • E0 : Fin 75735) : ℕ) = true := by
  have hstab : u • (0 : Fin 75735) = 0 := MulAction.mem_stabilizer_iff.1 (K0_le_stab hu)
  have hopp : Opp 0 ((u • E0 : Fin 75735) : ℕ) := by
    have := (opp_smul u 0 E0).2 opp_zero_E0
    rwa [hstab] at this
  have hfB := (opp_iff_fB (by norm_num) (u • E0).2).1 hopp
  have hne : ((u • E0 : Fin 75735) : ℕ) ≠ uw7E0 () := fun h =>
    hu1 (K0_eq_one_of_smul_E0 hu (Fin.ext h))
  simp [uw7InB, hfB, hne]

end E0

section Main

theorem tvP_smul_E0 {k : Fin 365211} (hkE : planeImg k.val (uw7E0 ()) = uw7E0 ()) :
    (⟨tvP k, tvP_mem k⟩ : TD6) • E0 = E0 := by
  rw [tvP_smul]
  exact Fin.ext hkE

theorem planeImg_planeImg (k : Fin 365211) {n : ℕ} (hn : n < 75735) :
    planeImg k.val (planeImg k.val n) = n := by
  have h : (⟨tvP k, tvP_mem k⟩ : TD6) * ⟨tvP k, tvP_mem k⟩ = 1 :=
    Subtype.ext (tvP_mul_self k)
  have h2 : (⟨tvP k, tvP_mem k⟩ : TD6) • ((⟨tvP k, tvP_mem k⟩ : TD6) • (⟨n, hn⟩ : Fin 75735)) =
      ⟨n, hn⟩ := by
    rw [← mul_smul, h, one_smul]
  have := congrArg Fin.val h2
  rwa [tvP_smul, tvP_smul] at this

def Th (O : Set TD6) : Set ℕ := {n | ∃ u ∈ O, ((u • E0 : Fin 75735) : ℕ) = n}

theorem Th_closed {O : Set TD6} (hinv : ∀ g ∈ Stab0, ∀ u ∈ O, g * u * g⁻¹ ∈ O) {k : Fin 365211}
    (hk0 : planeImg k.val 0 = 0) (hkE : planeImg k.val (uw7E0 ()) = uw7E0 ()) {n : ℕ}
    (hn : n ∈ Th O) : planeImg k.val n ∈ Th O := by
  obtain ⟨u, hu, rfl⟩ := hn
  obtain ⟨τ, hτ⟩ : ∃ τ : TD6, τ = ⟨tvP k, tvP_mem k⟩ := ⟨_, rfl⟩
  have hτs : τ ∈ Stab0 := by
    rw [hτ]
    exact tvP_mem_Stab0 hk0
  have hτE : τ • E0 = E0 := by
    rw [hτ]
    exact tvP_smul_E0 hkE
  refine ⟨τ * u * τ⁻¹, hinv τ hτs u hu, ?_⟩
  have h1 : τ⁻¹ • E0 = E0 := by
    rw [inv_smul_eq_iff]
    exact hτE.symm
  rw [mul_smul, mul_smul, h1, hτ, tvP_smul]

theorem levi_line {g : ℕ} (hg : g < 30) : ∃ k : Fin 365211, k.val = (uw7LLines ())[g]! ∧
    planeImg k.val 0 = 0 ∧ planeImg k.val (uw7E0 ()) = uw7E0 () := by
  obtain ⟨-, hlevi⟩ := levi_unpack
  obtain ⟨hgl, hg0, hgE⟩ := hlevi g hg
  exact ⟨⟨_, hgl⟩, rfl, hg0, hgE⟩

theorem Th_forest {O : Set TD6} (hinv : ∀ g ∈ Stab0, ∀ u ∈ O, g * u * g⁻¹ ∈ O) :
    ∀ v < 75735, uw7InB (uw7E0 ()) v = true →
      (v ∈ Th O ↔ (uw7BReps ())[uw7BCls (uw7E0 ()) v - 1]! ∈ Th O) := by
  obtain ⟨hreps, -⟩ := bcls_unpack
  have key : ∀ a b : ℕ, Relation.ReflTransGen
      (fun a b => ∃ g < 30, uw7InB (uw7E0 ()) a = true ∧ uw7InB (uw7E0 ()) b = true ∧
        uw7BCls (uw7E0 ()) a = uw7BCls (uw7E0 ()) b ∧ planeImg (uw7LLines ())[g]! a = b) a b →
      a < 75735 → b < 75735 ∧ (a ∈ Th O ↔ b ∈ Th O) := by
    intro a b h ha
    induction h with
    | refl => exact ⟨ha, Iff.rfl⟩
    | tail _ hbc ih =>
      obtain ⟨hb, hab⟩ := ih
      obtain ⟨g, hg, -, -, -, hgv⟩ := hbc
      obtain ⟨k, hk, hk0, hkE⟩ := levi_line hg
      rw [← hk] at hgv
      subst hgv
      refine ⟨(tvEquiv_wtV k.2 hb).1, hab.trans ⟨fun h => Th_closed hinv hk0 hkE h, fun h => ?_⟩⟩
      have := Th_closed hinv hk0 hkE h
      rwa [planeImg_planeImg k hb] at this
  intro v hv hin
  have hc : uw7BCls (uw7E0 ()) v - 1 < 3 := by
    unfold uw7BCls
    split_ifs <;> omega
  exact (key _ _ (uwBCheck_holds v hv hin) (hreps _ hc).1).2.symm

theorem card_filter_fin (p : ℕ → Bool) :
    (Finset.univ.filter fun j : Fin 75735 => p j.val = true).card =
      ((List.range 75735).filter p).length := by
  have e : (Finset.univ.filter fun j : Fin 75735 => p j.val = true).map Fin.valEmbedding =
      (Finset.range 75735).filter fun j => p j = true := by
    ext a
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    exact ⟨fun ⟨b, hb, hba⟩ => hba ▸ ⟨b.2, hb⟩, fun ⟨ha, hc⟩ => ⟨⟨a, ha⟩, hc, rfl⟩⟩
  rw [← Finset.card_map Fin.valEmbedding, e]
  simp only [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]
  apply congrArg List.length
  apply List.filter_congr
  intro x _
  simp

def Cset (c : ℕ) : Set (Fin 75735) :=
  {j | uw7InB (uw7E0 ()) j.val = true ∧ uw7BCls (uw7E0 ()) j.val = c}

theorem ncard_Cset {c : ℕ} (hc : c < 3) : (Cset (c + 1)).ncard = uw7BSizes[c]! := by
  obtain ⟨-, h⟩ := bcls_unpack
  have e : Cset (c + 1) = ↑(Finset.univ.filter fun j : Fin 75735 =>
      (uw7InB (uw7E0 ()) j.val && uw7BCls (uw7E0 ()) j.val == c + 1) = true) := by
    ext j
    simp [Cset]
  rw [e, Set.ncard_coe_finset,
    card_filter_fin (fun n => uw7InB (uw7E0 ()) n && uw7BCls (uw7E0 ()) n == c + 1), h c hc]

theorem uw7BCls_cases (e0 j : ℕ) : uw7BCls e0 j = 1 ∨ uw7BCls e0 j = 2 ∨ uw7BCls e0 j = 3 := by
  unfold uw7BCls
  split_ifs <;> simp

theorem dec12_mem_F' {c : ℕ} (hc : c &&& 63 = 0) : dec12 c ∈ planeSub 0 := by
  rw [mem_F_iff, fst_dec12_eq_zero_iff]
  intro i hi
  have h := testBit_and_63 c i
  rw [hc, Nat.zero_testBit] at h
  simpa [hi] using h.symm

theorem wit_line {v : ℕ} (hv : v < 75735) (hin : uw7InB (uw7E0 ()) v = true)
    (hc : uw7BCls (uw7E0 ()) v = 1) :
    ∃ P : Fin 365211, (∀ x ∈ lineSet P.val, x ∈ planeSub 0) ∧
      ((⟨tvP P, tvP_mem P⟩ : TD6) • E0 : Fin 75735).val = v := by
  obtain ⟨w, h1, h2, h3, h4⟩ := uwWitCheck_holds v hv hin hc
  refine ⟨⟨w, h1⟩, ?_, ?_⟩
  · intro x hx
    rw [lineSet_eq] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact dec12_mem_F' h2
    · exact dec12_mem_F' h3
    · rw [dec12_xor]
      exact Submodule.add_mem _ (dec12_mem_F' h2) (dec12_mem_F' h3)
  · rw [tvP_smul]
    change planeImg w (uw7E0 ()) = v
    rw [planeImg_eq_planeImgM]
    exact h4

theorem orbit_roots (O : Set TD6) (hne : O.Nonempty) (hK : ∀ u ∈ O, u ∈ K0) (h1 : (1 : TD6) ∉ O)
    (hinv : ∀ g ∈ Stab0, ∀ u ∈ O, g * u * g⁻¹ ∈ O) (hdvd : O.ncard ∣ 41664)
    (hts : ∀ u ∈ O, ∀ E : Fin 75735, ¬ Opp E.val (u • E).val) :
    ∀ u ∈ O, ∃ p : Fin 365211, (∀ x ∈ lineSet p.val, x ∈ planeSub 0) ∧
      u = ⟨tvP p, tvP_mem p⟩ := by
  have hu1 : ∀ u ∈ O, u ≠ 1 := fun u hu h => h1 (h ▸ hu)
  have hinB : ∀ u ∈ O, uw7InB (uw7E0 ()) ((u • E0 : Fin 75735) : ℕ) = true := fun u hu =>
    inB_smul_E0 (hK u hu) (hu1 u hu)
  have hcls3 : ∀ u ∈ O, uw7BCls (uw7E0 ()) ((u • E0 : Fin 75735) : ℕ) ≠ 3 := by
    intro u hu h3
    have hfB : fB (wt (uw7E0 ())) (wt ((u • E0 : Fin 75735) : ℕ)) = true := by
      by_contra hf
      unfold uw7BCls at h3
      rw [if_neg hf] at h3
      split_ifs at h3 <;> omega
    exact hts u hu E0 ((opp_iff_fB E0.2 (u • E0).2).2 hfB)
  have hinj : Set.InjOn (fun u : TD6 => u • E0) O := by
    intro u hu u' hu' h
    have h' : u • E0 = u' • E0 := h
    have hk : u⁻¹ * u' ∈ K0 := K0.mul_mem (K0.inv_mem (hK u hu)) (hK u' hu')
    have h2 : (u⁻¹ * u') • E0 = E0 := by rw [mul_smul, ← h', inv_smul_smul]
    exact inv_mul_eq_one.1 (K0_eq_one_of_smul_E0 hk h2)
  have hcard : ((fun u : TD6 => u • E0) '' O).ncard = O.ncard := hinj.ncard_image
  have hsub : (fun u : TD6 => u • E0) '' O ⊆ Cset 1 ∪ Cset 2 := by
    rintro _ ⟨u, hu, rfl⟩
    rcases uw7BCls_cases (uw7E0 ()) ((u • E0 : Fin 75735) : ℕ) with h | h | h
    · exact Or.inl ⟨hinB u hu, h⟩
    · exact Or.inr ⟨hinB u hu, h⟩
    · exact absurd h (hcls3 u hu)
  by_cases hr2 : (uw7BReps ())[1]! ∈ Th O
  · exfalso
    have hsub2 : Cset 2 ⊆ (fun u : TD6 => u • E0) '' O := by
      intro j hj
      obtain ⟨hin, hc⟩ := hj
      have := (Th_forest hinv j.val j.2 hin).2
      rw [hc] at this
      obtain ⟨u, hu, hj'⟩ := this hr2
      exact ⟨u, hu, Fin.ext hj'⟩
    have hlo : (Cset 2).ncard ≤ O.ncard := by
      rw [← hcard]
      exact Set.ncard_le_ncard hsub2 (Set.toFinite _)
    have hhi : O.ncard ≤ (Cset 1).ncard + (Cset 2).ncard := by
      rw [← hcard]
      exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le _ _)
    have c1 : (Cset 1).ncard = 651 := (ncard_Cset (c := 0) (by norm_num)).trans (by decide)
    have c2 : (Cset 2).ncard = 18228 := (ncard_Cset (c := 1) (by norm_num)).trans (by decide)
    obtain ⟨k, hk⟩ := hdvd
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega
    rcases hk3 with rfl | rfl | rfl | hk3
    · omega
    · omega
    · omega
    · have : O.ncard * 3 ≤ O.ncard * k := Nat.mul_le_mul_left _ hk3
      omega
  · intro u hu
    have hc1 : uw7BCls (uw7E0 ()) ((u • E0 : Fin 75735) : ℕ) = 1 := by
      rcases uw7BCls_cases (uw7E0 ()) ((u • E0 : Fin 75735) : ℕ) with h | h | h
      · exact h
      · exfalso
        apply hr2
        have := (Th_forest hinv _ (u • E0).2 (hinB u hu)).1 ⟨u, hu, rfl⟩
        rwa [h] at this
      · exact absurd h (hcls3 u hu)
    obtain ⟨P, hP, hPv⟩ := wit_line (u • E0).2 (hinB u hu) hc1
    refine ⟨P, hP, ?_⟩
    have hPK : (⟨tvP P, tvP_mem P⟩ : TD6) ∈ K0 := tvP_mem_K0 hP
    have h2 : ((⟨tvP P, tvP_mem P⟩ : TD6)⁻¹ * u) • E0 = E0 := by
      rw [mul_smul, inv_smul_eq_iff]
      exact (Fin.ext hPv).symm
    have h3 := K0_eq_one_of_smul_E0 (K0.mul_mem (K0.inv_mem hPK) (hK u hu)) h2
    exact (inv_mul_eq_one.1 h3).symm

end Main

end CFSG.GF2Type.SmithTypeE.E7
