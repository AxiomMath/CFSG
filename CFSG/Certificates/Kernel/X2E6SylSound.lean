module

public import Certificates.Data.Kernel.X2E6Syl
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6Rank0
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.KC.X2E6Syl

open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6 CFSG.Open

abbrev GL6 : Type := Matrix.GeneralLinearGroup (Fin 6) (ZMod 3)

@[expose] def dec (A : List (List ℕ)) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  Matrix.of fun i j => ((ent A i j : ℕ) : ZMod 3)

theorem ent_mk6 (f : ℕ → ℕ → ℕ) (i j : Fin 6) : ent (mk6 f) i j = f i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem dec_mk6 (f : ℕ → ℕ → ℕ) (i j : Fin 6) : dec (mk6 f) i j = ((f i j : ℕ) : ZMod 3) := by
  rw [dec, Matrix.of_apply, ent_mk6]

theorem dec_apply (A : List (List ℕ)) (i j : Fin 6) : dec A i j = ((ent A i j : ℕ) : ZMod 3) := rfl

theorem dec_mulL (A B : List (List ℕ)) : dec (mulL A B) = dec A * dec B := by
  ext i j
  rw [mulL, dec_mk6, Matrix.mul_apply, Fin.sum_univ_six, ZMod.natCast_mod]
  simp only [dec_apply, Nat.cast_add, Nat.cast_mul]
  rfl

theorem dec_addL (A B : List (List ℕ)) : dec (addL A B) = dec A + dec B := by
  ext i j
  rw [addL, dec_mk6, Matrix.add_apply, ZMod.natCast_mod]
  simp only [dec_apply, Nat.cast_add]

theorem dec_subL (A B : List (List ℕ)) : dec (subL A B) = dec A - dec B := by
  ext i j
  rw [subL, dec_mk6, Matrix.sub_apply, ZMod.natCast_mod]
  have h2 : ((2 : ℕ) : ZMod 3) = -1 := by decide
  simp only [dec_apply, Nat.cast_add, Nat.cast_mul, h2]
  ring

theorem dec_idL : dec idL = 1 := by
  ext i j
  rw [idL, dec_mk6, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    simp [h, h']

theorem dec_zeroL : dec zeroL = 0 := by
  ext i j
  rw [zeroL, dec_mk6]
  simp

theorem dec_pwL (A : List (List ℕ)) (e : ℕ) : dec (pwL A e) = dec A ^ e := by
  induction e with
  | zero => rw [pwL, dec_idL, pow_zero]
  | succ e ih => rw [pwL, dec_mulL, ih, pow_succ]

def Canon (A : List (List ℕ)) : Prop :=
  ∃ f : ℕ → ℕ → ℕ, A = mk6 f ∧ ∀ i < 6, ∀ j < 6, f i j < 3

theorem canon_mulL (A B : List (List ℕ)) : Canon (mulL A B) :=
  ⟨_, rfl, fun _ _ _ _ => Nat.mod_lt _ (by norm_num)⟩

theorem canon_idL : Canon idL :=
  ⟨_, rfl, fun i _ j _ => by split <;> norm_num⟩

theorem mk6_congr {f g : ℕ → ℕ → ℕ} (h : ∀ i < 6, ∀ j < 6, f i j = g i j) : mk6 f = mk6 g := by
  simp only [mk6, mkV]
  simp (disch := norm_num) only [h]

theorem dec_inj {A B : List (List ℕ)} (hA : Canon A) (hB : Canon B) (h : dec A = dec B) :
    A = B := by
  obtain ⟨f, rfl, hf⟩ := hA
  obtain ⟨g, rfl, hg⟩ := hB
  refine mk6_congr fun i hi j hj => ?_
  have e := congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩
  rw [dec_mk6, dec_mk6, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hf i hi j hj),
    Nat.mod_eq_of_lt (hg i hi j hj)] at e
  exact e

@[expose] noncomputable def refl' (i : ℕ) : GL6 := if h : i < 6 then reflGL ⟨i, h⟩ else 1

theorem ent_reflL_fin : ∀ i j k : Fin 6, ent (reflL i) j k = (reflMat i j k).val := by
  decide +kernel

theorem dec_reflL_fin (i j k : Fin 6) : dec (reflL i) j k = reflMat i j k := by
  rw [dec_apply, ent_reflL_fin, ZMod.natCast_zmod_val]

theorem dec_reflL (i : ℕ) : dec (reflL i) = ((refl' i : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) := by
  unfold refl'
  split_ifs with h
  · ext j k
    exact dec_reflL_fin ⟨i, h⟩ j k
  · ext j k
    rw [reflL, dec_mk6, Units.val_one, Matrix.one_apply]
    have hk : (k : ℕ) ≠ i := fun e => h (e ▸ k.isLt)
    by_cases hjk : j = k
    · subst hjk
      simp [hk]
    · have h' : (j : ℕ) ≠ k := fun e => hjk (Fin.ext e)
      simp [hjk, h', hk]

theorem refl'_mem (i : ℕ) : refl' i ∈ W3 := by
  unfold refl'
  split_ifs with h
  · exact Subgroup.subset_closure ⟨⟨i, h⟩, rfl⟩
  · exact W3.one_mem

@[expose] noncomputable def wordGL (w : List ℕ) : GL6 := (w.map refl').prod

theorem dec_wordL (w : List ℕ) :
    dec (wordL w) = ((wordGL w : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) := by
  induction w with
  | nil => rw [wordL, List.foldr_nil, dec_idL, wordGL, List.map_nil, List.prod_nil, Units.val_one]
  | cons i w ih =>
    have e : wordL (i :: w) = mulL (reflL i) (wordL w) := rfl
    rw [e, dec_mulL, ih, dec_reflL]
    simp [wordGL]

theorem wordGL_mem (w : List ℕ) : wordGL w ∈ W3 :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact refl'_mem i

@[expose] noncomputable def qGen (gw : List (List ℕ)) (k : ℕ) : GL6 := wordGL (gw.getD k [])

@[expose] noncomputable def qSub (gw : List (List ℕ)) : Subgroup GL6 :=
  Subgroup.closure (Set.range fun k : Fin 4 => qGen gw k)

theorem qSub_le (gw : List (List ℕ)) : qSub gw ≤ W3 :=
  (Subgroup.closure_le _).2 (by rintro _ ⟨k, rfl⟩; exact wordGL_mem _)

def QS (gw : List (List ℕ)) : Set (Matrix (Fin 6) (Fin 6) (ZMod 3)) :=
  {M | ∃ A ∈ qEls gw, dec A = M}

def Mat (R : Subgroup GL6) : Set (Matrix (Fin 6) (Fin 6) (ZMod 3)) :=
  (fun g : GL6 => (g : Matrix (Fin 6) (Fin 6) (ZMod 3))) '' (R : Set GL6)

theorem canon_of_mem_qEls {gw : List (List ℕ)} {A : List (List ℕ)} (hA : A ∈ qEls gw) :
    Canon A := by
  simp only [qEls, List.mem_flatMap, List.mem_map] at hA
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hA
  exact canon_mulL _ _

theorem idL_mem_qEls (gw : List (List ℕ)) : idL ∈ qEls gw := by
  have e : mulL (mulL (mulL idL idL) idL) idL = idL := by decide +kernel
  simp only [qEls, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨0, by norm_num, 0, by norm_num, 0, by norm_num, 0, by norm_num, e⟩

theorem mem_qSub_of_mem_qEls {gw : List (List ℕ)} {A : List (List ℕ)} (hA : A ∈ qEls gw) :
    ∃ g ∈ qSub gw, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) = dec A := by
  simp only [qEls, List.mem_flatMap, List.mem_map] at hA
  obtain ⟨a, -, b, -, c, -, d, -, rfl⟩ := hA
  have hg : ∀ k : Fin 4, qGen gw k ∈ qSub gw := fun k => Subgroup.subset_closure ⟨k, rfl⟩
  refine ⟨qGen gw 0 ^ a * qGen gw 1 ^ b * qGen gw 2 ^ c * qGen gw 3 ^ d,
    mul_mem (mul_mem (mul_mem (pow_mem (hg 0) _) (pow_mem (hg 1) _)) (pow_mem (hg 2) _))
      (pow_mem (hg 3) _), ?_⟩
  simp only [dec_mulL, dec_pwL, dec_wordL, Units.val_mul, Units.val_pow_eq_pow_val, qGen]

theorem qOK_props {gw : List (List ℕ)} (h : qOK gw = true) :
    gw.length = 4 ∧ (∀ w ∈ gw, pwL (wordL w) 3 = idL) ∧ (qEls gw).length = 81 ∧
      (qEls gw).Nodup ∧ ∀ A ∈ qEls gw, ∀ w ∈ gw, mulL A (wordL w) ∈ qEls gw := by
  simp only [qOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.contains_iff] at h
  obtain ⟨⟨⟨⟨⟨h1, -⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h3, h4, h5, h6⟩

theorem qGen_cube {gw : List (List ℕ)} (h : qOK gw = true) (k : Fin 4) : qGen gw k ^ 3 = 1 := by
  obtain ⟨h1, h3, -⟩ := qOK_props h
  have hk : gw.getD k [] ∈ gw := by
    rw [List.getD_eq_getElem _ _ (by rw [h1]; exact k.isLt)]
    exact List.getElem_mem _
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, qGen, ← dec_wordL, ← dec_pwL, h3 _ hk, dec_idL, Units.val_one]

theorem QS_mul_qGen {gw : List (List ℕ)} (h : qOK gw = true) {M : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (hM : M ∈ QS gw) (k : Fin 4) : M * (qGen gw k : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ QS gw := by
  obtain ⟨h1, -, -, -, h6⟩ := qOK_props h
  obtain ⟨A, hA, rfl⟩ := hM
  have hk : gw.getD k [] ∈ gw := by
    rw [List.getD_eq_getElem _ _ (by rw [h1]; exact k.isLt)]
    exact List.getElem_mem _
  exact ⟨_, h6 A hA _ hk, by rw [dec_mulL, dec_wordL]; rfl⟩

theorem mat_qSub {gw : List (List ℕ)} (h : qOK gw = true) : Mat (qSub gw) = QS gw := by
  have key : ∀ g ∈ qSub gw, (∀ M ∈ QS gw, M * (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ QS gw) ∧
      (∀ M ∈ QS gw, M * ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ QS gw) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      have hinv : (qGen gw k)⁻¹ = qGen gw k * qGen gw k := by
        refine inv_eq_of_mul_eq_one_right ?_
        rw [← qGen_cube h k, pow_three]
      refine ⟨fun M hM => QS_mul_qGen h hM k, fun M hM => ?_⟩
      rw [hinv, Units.val_mul, ← Matrix.mul_assoc]
      exact QS_mul_qGen h (QS_mul_qGen h hM k) k
    | one => exact ⟨fun M hM => by simpa using hM, fun M hM => by simpa using hM⟩
    | mul x y _ _ hx hy =>
      refine ⟨fun M hM => ?_, fun M hM => ?_⟩
      · rw [Units.val_mul, ← Matrix.mul_assoc]
        exact hy.1 _ (hx.1 M hM)
      · rw [mul_inv_rev, Units.val_mul, ← Matrix.mul_assoc]
        exact hx.2 _ (hy.2 M hM)
    | inv x _ hx =>
      refine ⟨fun M hM => hx.2 M hM, fun M hM => ?_⟩
      rw [inv_inv]
      exact hx.1 M hM
  have h1 : (1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ QS gw := ⟨idL, idL_mem_qEls gw, dec_idL⟩
  ext M
  constructor
  · rintro ⟨g, hg, rfl⟩
    simpa using (key g hg).1 1 h1
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨g, hg, e⟩ := mem_qSub_of_mem_qEls hA
    exact ⟨g, hg, e⟩

theorem ncard_mat (R : Subgroup GL6) : (Mat R).ncard = Nat.card R := by
  rw [Mat, Set.ncard_image_of_injective _ (fun g h hgh => Units.ext hgh), ← Nat.card_coe_set_eq]
  rfl

theorem ncard_dec {L : List (List (List ℕ))} (hc : ∀ A ∈ L, Canon A) (hn : L.Nodup) :
    {M | ∃ A ∈ L, dec A = M}.ncard = L.length := by
  have himg : {M | ∃ A ∈ L, dec A = M} = dec '' ((L.toFinset : Finset _) : Set (List (List ℕ))) := by
    ext M
    simp
  have hinj : Set.InjOn dec ((L.toFinset : Finset _) : Set (List (List ℕ))) := by
    intro A hA B hB hAB
    simp only [Finset.mem_coe, List.mem_toFinset] at hA hB
    exact dec_inj (hc A hA) (hc B hB) hAB
  rw [himg, hinj.ncard_image, Set.ncard_coe_finset, List.toFinset_card_of_nodup hn]

theorem card_qSub {gw : List (List ℕ)} (h : qOK gw = true) : Nat.card (qSub gw) = 81 := by
  obtain ⟨-, -, h4, h5, -⟩ := qOK_props h
  rw [← ncard_mat, mat_qSub h, QS, ncard_dec (fun A hA => canon_of_mem_qEls hA) h5, h4]

def FamSet (H : List (List (List ℕ))) : Set (Matrix (Fin 6) (Fin 6) (ZMod 3)) :=
  {M | ∃ A ∈ H, dec A = M}

theorem getD_mem_qEls (gw : List (List ℕ)) (i : ℕ) : (qEls gw).getD i idL ∈ qEls gw := by
  rw [List.getD_eq_getElem?_getD]
  cases hget : (qEls gw)[i]? with
  | none => exact idL_mem_qEls gw
  | some A => exact List.mem_of_getElem? hget

theorem mem_qEls_of_mem_famM {gw : List (List ℕ)} {m : List ℕ} {A : List (List ℕ)}
    (hA : A ∈ famM (qEls gw) m) : A ∈ qEls gw := by
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hA
  exact getD_mem_qEls gw i

theorem famOK_props {gw : List (List ℕ)} {mel : List (List ℕ)} (hf : famOK gw mel = true) :
    [idL] ∈ mel.map (famM (qEls gw)) ∧ (∀ H ∈ mel.map (famM (qEls gw)), H.Nodup) ∧
    ∀ H ∈ mel.map (famM (qEls gw)), ∀ x ∈ tEls (qEls gw), x ∉ H →
      (∀ h ∈ H, mulL x h = mulL h x) →
        ∃ K ∈ mel.map (famM (qEls gw)), K.length = 3 * H.length ∧
          (∀ A ∈ K, A ∈ extL H x) ∧ ∀ A ∈ extL H x, A ∈ K := by
  simp only [famOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, List.any_eq_true, Bool.not_eq_true', List.contains_iff, sameSet] at hf
  obtain ⟨⟨h0, hnod⟩, hcl⟩ := hf
  refine ⟨List.mem_of_mem_head? (by rw [h0]; rfl), hnod, fun H hH x hx hxH hc => ?_⟩
  rcases hcl H hH x hx with (h1 | h2) | h3
  · exact absurd h1 hxH
  · exfalso
    rw [List.all_eq_false] at h2
    obtain ⟨h, hh, hne⟩ := h2
    exact absurd (hc h hh) (by simpa using hne)
  · obtain ⟨K, hK, hlen, hKe, heK⟩ := h3
    exact ⟨K, hK, hlen, fun A hA => hKe A hA, fun A hA => heK A hA⟩

theorem sq_not_mem' {K : Subgroup GL6} {x : GL6} (hxK : x ∉ K) (hx3 : x ^ 3 = 1) : x ^ 2 ∉ K := by
  intro h2
  apply hxK
  have h4 : x ^ 4 = x := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hx3, one_mul]
  have : x = (x ^ 2) ^ 2 := by rw [← pow_mul, h4]
  rw [this]
  exact K.pow_mem h2 2

theorem exists_decomp' {R K : Subgroup GL6} {x : GL6} (hA : IsElemAbelian 3 R) (hKR : K ≤ R)
    (hxR : x ∈ R) (hxK : x ∉ K) (hcard : Nat.card R = 3 * Nat.card K) (g : GL6) (hg : g ∈ R) :
    ∃ k ∈ K, ∃ i : ℕ, i < 3 ∧ g = k * x ^ i := by
  have hx3 : x ^ 3 = 1 := hA.2 x hxR
  have hx2K := sq_not_mem' hxK hx3
  let φ : K × Fin 3 → R := fun p => ⟨p.1.1 * x ^ p.2.val, mul_mem (hKR p.1.2) (pow_mem hxR _)⟩
  have hinj : Function.Injective φ := by
    rintro ⟨⟨k, hk⟩, i⟩ ⟨⟨k', hk'⟩, j⟩ hφ
    have h' : k * x ^ i.val = k' * x ^ j.val := congrArg Subtype.val hφ
    have hu : k'⁻¹ * k = x ^ j.val * (x ^ i.val)⁻¹ := by
      rw [eq_mul_inv_of_mul_eq h'.symm]
      group
    have hmem : x ^ j.val * (x ^ i.val)⁻¹ ∈ K := hu ▸ K.mul_mem (K.inv_mem hk') hk
    have hij : i = j := by
      have hxinv : x⁻¹ = x ^ 2 := inv_eq_of_mul_eq_one_right ((pow_succ' x 2).symm.trans hx3)
      have hx2inv : (x ^ 2)⁻¹ = x := inv_eq_of_mul_eq_one_right ((pow_succ x 2).symm.trans hx3)
      fin_cases i <;> fin_cases j
      · rfl
      · have e : x ^ 1 * (x ^ 0)⁻¹ = x := by simp
        exact absurd (e ▸ hmem) hxK
      · have e : x ^ 2 * (x ^ 0)⁻¹ = x ^ 2 := by simp
        exact absurd (e ▸ hmem) hx2K
      · have e : x ^ 0 * (x ^ 1)⁻¹ = x ^ 2 := by simp [hxinv]
        exact absurd (e ▸ hmem) hx2K
      · rfl
      · have e : x ^ 2 * (x ^ 1)⁻¹ = x := by rw [pow_one, mul_inv_eq_iff_eq_mul, pow_two]
        exact absurd (e ▸ hmem) hxK
      · have e : x ^ 0 * (x ^ 2)⁻¹ = x := by rw [pow_zero, one_mul, hx2inv]
        exact absurd (e ▸ hmem) hxK
      · have e : x ^ 1 * (x ^ 2)⁻¹ = x ^ 2 := by rw [pow_one, hx2inv, pow_two]
        exact absurd (e ▸ hmem) hx2K
      · rfl
    subst hij
    have hkk : k = k' := by
      have : k'⁻¹ * k = 1 := by rw [hu, mul_inv_cancel]
      exact (inv_mul_eq_one.1 this).symm
    subst hkk
    rfl
  have hcardle : Nat.card R ≤ Nat.card (K × Fin 3) := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin, hcard, Nat.mul_comm]
  obtain ⟨p, hp⟩ := (hinj.bijective_of_nat_card_le hcardle).2 ⟨g, hg⟩
  exact ⟨p.1.1, p.1.2, p.2.val, p.2.isLt, by
    have := congrArg Subtype.val hp
    simpa [φ] using this.symm⟩

theorem mat_bot' : Mat (⊥ : Subgroup GL6) = {1} := by
  ext M
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [Subgroup.mem_bot.1 hg]
    simp
  · rintro rfl
    exact ⟨1, Subgroup.one_mem _, by simp⟩

theorem exists_fam {gw : List (List ℕ)} {mel : List (List ℕ)} (hq : qOK gw = true)
    (hf : famOK gw mel = true) :
    ∀ (n : ℕ) (R : Subgroup GL6), R ≤ qSub gw → IsElemAbelian 3 R → Nat.card R = 3 ^ n →
      ∃ H ∈ mel.map (famM (qEls gw)), Mat R = FamSet H := by
  obtain ⟨hone, -, hcl⟩ := famOK_props hf
  have hQ := mat_qSub hq
  intro n
  induction n with
  | zero =>
    intro R _ _ hcard
    have hbot : R = ⊥ := Subgroup.eq_bot_of_card_eq R (by simpa using hcard)
    refine ⟨[idL], hone, ?_⟩
    rw [hbot, mat_bot']
    ext M
    simp [FamSet, dec_idL, eq_comm]
  | succ n ih =>
    intro R hRQ hA hcard
    have hdvd : 3 ^ n ∣ Nat.card R := by
      rw [hcard]
      exact pow_dvd_pow 3 (Nat.le_succ n)
    obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
    set K : Subgroup GL6 := K'.map R.subtype with hKdef
    have hKR : K ≤ R := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    have hKcard : Nat.card K = 3 ^ n := by
      rw [hKdef, Subgroup.card_map_of_injective Subtype.val_injective]
      exact hK'
    obtain ⟨H, hH, hMK⟩ := ih K (hKR.trans hRQ) (isElemAbelian_mono hA hKR) hKcard
    have hcardK : Nat.card R = 3 * Nat.card K := by
      rw [hcard, hKcard, pow_succ, Nat.mul_comm]
    have hKlt : Nat.card K < Nat.card R := by
      have : 0 < 3 ^ n := by positivity
      omega
    obtain ⟨x, hxR, hxK⟩ : ∃ x ∈ R, x ∉ K := SetLike.not_le_iff_exists.1 fun hRK =>
      lt_irrefl _ (hKlt.trans_le (Subgroup.card_le_of_le hRK))
    have hHQ : ∀ B ∈ H, B ∈ qEls gw := by
      obtain ⟨m, -, rfl⟩ := List.mem_map.1 hH
      exact fun B hB => mem_qEls_of_mem_famM hB
    have hmatK : ∀ B ∈ H, ∃ g ∈ K, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) = dec B := by
      intro B hB
      have hmem : dec B ∈ FamSet H := ⟨B, hB, rfl⟩
      rw [← hMK] at hmem
      obtain ⟨g, hg, e⟩ := hmem
      exact ⟨g, hg, e⟩
    obtain ⟨A, hAQ, hAx⟩ : ∃ A ∈ qEls gw, dec A = (x : Matrix (Fin 6) (Fin 6) (ZMod 3)) := by
      have : (x : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ Mat (qSub gw) := ⟨x, hRQ hxR, rfl⟩
      rw [hQ] at this
      exact this
    have hAc := canon_of_mem_qEls hAQ
    have hx3 : x ^ 3 = 1 := hA.2 x hxR
    have hA1 : A ≠ idL := by
      intro hA1
      apply hxK
      have hx1 : x = 1 := Units.ext (by rw [← hAx, hA1, dec_idL]; rfl)
      rw [hx1]
      exact K.one_mem
    have hA3 : mulL A (mulL A A) = idL := by
      apply dec_inj (canon_mulL _ _) canon_idL
      rw [dec_mulL, dec_mulL, hAx, dec_idL]
      have h3 := congrArg Units.val hx3
      simpa [Units.val_mul, pow_three, Units.val_one] using h3
    have hAT : A ∈ tEls (qEls gw) := by
      unfold tEls
      rw [List.mem_filter]
      refine ⟨hAQ, ?_⟩
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
      exact ⟨hA1, hA3⟩
    have hAH : A ∉ H := by
      intro hAH
      obtain ⟨g, hgK, hg⟩ := hmatK A hAH
      have hgx : g = x := Units.ext (by rw [hg, hAx])
      exact hxK (hgx ▸ hgK)
    have hcomm : ∀ B ∈ H, mulL A B = mulL B A := by
      intro B hB
      obtain ⟨g, hgK, hg⟩ := hmatK B hB
      have hc : x * g = g * x := isElemAbelian_commute hA hxR (hKR hgK)
      apply dec_inj (canon_mulL _ _) (canon_mulL _ _)
      rw [dec_mulL, dec_mulL, hAx, ← hg]
      have h2 := congrArg Units.val hc
      simpa [Units.val_mul] using h2
    obtain ⟨H'', hH'', -, hKe, heK⟩ := hcl H hH A hAT hAH hcomm
    have hset : FamSet H'' = FamSet (extL H A) := by
      ext M
      constructor
      · rintro ⟨B, hB, rfl⟩
        exact ⟨B, hKe B hB, rfl⟩
      · rintro ⟨B, hB, rfl⟩
        exact ⟨B, heK B hB, rfl⟩
    refine ⟨H'', hH'', ?_⟩
    rw [hset]
    ext M
    simp only [FamSet, extL, List.mem_append, List.mem_map, Set.mem_setOf_eq]
    constructor
    · rintro ⟨g, hgR, rfl⟩
      obtain ⟨k, hkK, i, hi, rfl⟩ := exists_decomp' hA hKR hxR hxK hcardK g hgR
      have hkM : (k : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ Mat K := ⟨k, hkK, rfl⟩
      rw [hMK] at hkM
      obtain ⟨B₀, hB₀H, hB₀⟩ := hkM
      interval_cases i
      · exact ⟨B₀, Or.inl (Or.inl hB₀H), by simp [hB₀]⟩
      · exact ⟨mulL B₀ A, Or.inl (Or.inr ⟨B₀, hB₀H, rfl⟩), by rw [dec_mulL, hB₀, hAx]; simp⟩
      · exact ⟨mulL B₀ (mulL A A), Or.inr ⟨B₀, hB₀H, rfl⟩, by
          rw [dec_mulL, dec_mulL, hB₀, hAx]; simp [pow_two]⟩
    · rintro ⟨B, hB, rfl⟩
      rcases hB with (hBH | ⟨h', hh', rfl⟩) | ⟨h', hh', rfl⟩
      · obtain ⟨g, hgK, hg⟩ := hmatK B hBH
        exact ⟨g, hKR hgK, hg⟩
      · obtain ⟨g, hgK, hg⟩ := hmatK h' hh'
        refine ⟨g * x, mul_mem (hKR hgK) hxR, ?_⟩
        dsimp only
        rw [Units.val_mul, dec_mulL, hAx, ← hg]
      · obtain ⟨g, hgK, hg⟩ := hmatK h' hh'
        refine ⟨g * (x * x), mul_mem (hKR hgK) (mul_mem hxR hxR), ?_⟩
        dsimp only
        rw [Units.val_mul, Units.val_mul, dec_mulL, dec_mulL, hAx, ← hg]

theorem card_eq_length {gw : List (List ℕ)} {mel : List (List ℕ)} (hf : famOK gw mel = true)
    {R : Subgroup GL6} {H : List (List (List ℕ))} (hH : H ∈ mel.map (famM (qEls gw)))
    (hMat : Mat R = FamSet H) : Nat.card R = H.length := by
  obtain ⟨-, hnod, -⟩ := famOK_props hf
  have hc : ∀ A ∈ H, Canon A := by
    obtain ⟨m, -, rfl⟩ := List.mem_map.1 hH
    exact fun A hA => canon_of_mem_qEls (mem_qEls_of_mem_famM hA)
  rw [← ncard_mat, hMat, FamSet, ncard_dec hc (hnod H hH)]

theorem foldr_mulVec (f : ℕ → List (List ℕ)) (Ys : List (ℕ × List (List ℕ)))
    (v : Fin 6 → ZMod 3) (hv : ∀ p ∈ Ys, Matrix.mulVec (dec (f p.1)) v = v) :
    Matrix.mulVec (dec (Ys.foldr (fun p acc => addL (mulL p.2 (subL (f p.1) idL)) acc) zeroL)) v =
      0 := by
  induction Ys with
  | nil => simp [dec_zeroL]
  | cons p Ys ih =>
    rw [List.foldr_cons, dec_addL, Matrix.add_mulVec, dec_mulL, dec_subL, dec_idL,
      ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hv p (List.mem_cons_self ..),
      sub_self, Matrix.mulVec_zero, ih fun q hq => hv q (List.mem_cons_of_mem _ hq), add_zero]

theorem card_fixVec_le {R : Subgroup GL6} {H : List (List (List ℕ))} (hMat : Mat R = FamSet H)
    (f : ℕ → List (List ℕ)) {S : List ℕ} {E : List (List ℕ)} {Ys : List (ℕ × List (List ℕ))}
    (hY : ∀ p ∈ Ys, f p.1 ∈ H)
    (hEq : subL idL E = Ys.foldr (fun p acc => addL (mulL p.2 (subL (f p.1) idL)) acc) zeroL)
    (hS : ∀ j ∈ S, j < 6) (hcol : ∀ i j : Fin 6, (j : ℕ) ∉ S → ent E i j = 0) :
    Nat.card (fixVec R) ≤ 3 ^ S.length := by
  have hfix : ∀ v ∈ fixVec R, Matrix.mulVec (dec E) v = v := by
    intro v hv
    have hv' : ∀ p ∈ Ys, Matrix.mulVec (dec (f p.1)) v = v := by
      intro p hp
      have hmem : dec (f p.1) ∈ Mat R := by rw [hMat]; exact ⟨_, hY p hp, rfl⟩
      obtain ⟨g, hg, e⟩ := hmem
      rw [← e]
      exact hv g hg
    have h0 := foldr_mulVec f Ys v hv'
    rw [← hEq, dec_subL, dec_idL, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    exact h0.symm
  have hzero : ∀ u : Fin 6 → ZMod 3, Matrix.mulVec (dec E) u = u →
      (∀ j : Fin 6, (j : ℕ) ∈ S → u j = 0) → u = 0 := by
    intro u hu hS0
    funext i
    rw [← hu]
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : (j : ℕ) ∈ S
    · rw [hS0 j hj, mul_zero]
    · rw [dec_apply, hcol i j hj, Nat.cast_zero, zero_mul]
  let φ : fixVec R → (Fin S.length → ZMod 3) := fun v t => v.1 ⟨S.get t, hS _ (List.get_mem _ _)⟩
  have hinj : Function.Injective φ := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
    have hd : v - w ∈ fixVec R := by
      intro g hg
      rw [Matrix.mulVec_sub, hv g hg, hw g hg]
    have h0 := hzero (v - w) (hfix _ hd) (fun j hj => by
      obtain ⟨t, ht⟩ := List.mem_iff_get.1 hj
      have := congrFun hvw t
      simp only [φ, ht] at this
      simp [this])
    exact Subtype.ext (sub_eq_zero.1 h0)
  calc Nat.card (fixVec R) ≤ Nat.card (Fin S.length → ZMod 3) :=
        Nat.card_le_card_of_injective φ hinj
    _ = 3 ^ S.length := by simp [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]

@[expose] def vecF (f : List ℕ) : Fin 6 → ZMod 3 := fun i => ((f.getD i 0 : ℕ) : ZMod 3)

@[expose] def rootF (a : List ℤ) : Fin 6 → ℤ := fun i => a.getD i 0

theorem getD_mkV {α : Type} (g : ℕ → α) (d : α) (i : Fin 6) : (mkV g).getD i d = g i := by
  fin_cases i <;> rfl

theorem cz_eq (i j : Fin 6) : cz i j = cartanE6 i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem sum6_eq (g : ℕ → ℤ) : sum6 g = ∑ i : Fin 6, g i := by
  rw [Fin.sum_univ_six]
  rfl

theorem rootF_rootReflL (i : Fin 6) (a : List ℤ) :
    rootF (rootReflL i a) = rootRefl i (rootF a) := by
  funext j
  simp only [rootF, rootReflL, getD_mkV, rootRefl, sum6_eq]
  by_cases h : j = i
  · subst h
    simp [cz_eq]
  · have h' : (j : ℕ) ≠ i := fun e => h (Fin.ext e)
    simp [h, h']

theorem rootF_rootW_mem {j : ℕ} (hj : j < 6) {w : List ℕ} (hw : ∀ i ∈ w, i < 6) :
    rootF (rootW j w) ∈ rootsE6 := by
  induction w with
  | nil =>
    have e : rootF (rootW j []) = Pi.single (⟨j, hj⟩ : Fin 6) 1 := by
      funext t
      simp only [rootF, rootW, List.foldr_nil, getD_mkV, Pi.single_apply, Fin.ext_iff]
    rw [e]
    exact rootsE6_simple _
  | cons i w ih =>
    have hi : i < 6 := hw i (List.mem_cons_self ..)
    have e : rootW j (i :: w) = rootReflL i (rootW j w) := rfl
    rw [e, show i = ((⟨i, hi⟩ : Fin 6) : ℕ) from rfl, rootF_rootReflL]
    exact rootsE6_closed (ih fun t ht => hw t (List.mem_cons_of_mem _ ht)) _

theorem pair_eq_zero {a : List ℤ} {f : List ℕ} (h : pairI a f % 3 = 0) :
    ∑ i, ((rootF a i : ℤ) : ZMod 3) * vecF f i = 0 := by
  have e : ((pairI a f : ℤ) : ZMod 3) = ∑ i, ((rootF a i : ℤ) : ZMod 3) * vecF f i := by
    rw [pairI, sum6_eq]
    push_cast
    rfl
  rw [← e, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Int.dvd_of_emod_eq_zero h

theorem cformL_eq (a b : List ℤ) : cformL a b = cartanForm (rootF a) (rootF b) := by
  simp only [cformL, cartanForm, sum6_eq, rootF, cz_eq]

theorem linearIndependent_of_det' {x y z : Fin 6 → ℚ} (c1 c2 c3 : Fin 6)
    (hdet : (!![x c1, y c1, z c1; x c2, y c2, z c2; x c3, y c3, z c3] :
      Matrix (Fin 3) (Fin 3) ℚ).det ≠ 0) :
    LinearIndependent ℚ ![x, y, z] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have e1 := congrFun hg c1
  have e2 := congrFun hg c2
  have e3 := congrFun hg c3
  simp [Fin.sum_univ_three] at e1 e2 e3
  have hsum : Matrix.mulVec (!![x c1, y c1, z c1; x c2, y c2, z c2; x c3, y c3, z c3] :
      Matrix (Fin 3) (Fin 3) ℚ) g = 0 := by
    funext r
    fin_cases r
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      linear_combination e1
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      linear_combination e2
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      linear_combination e3
  have hg0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hsum
  intro k
  exact congrFun hg0 k

theorem three_le_rootRankQ' (C : Set (Fin 6 → ℤ)) {x y z : Fin 6 → ℤ} (hx : x ∈ C) (hy : y ∈ C)
    (hz : z ∈ C) (c1 c2 c3 : Fin 6)
    (hdet : x c1 * (y c2 * z c3 - y c3 * z c2) - x c2 * (y c1 * z c3 - y c3 * z c1) +
      x c3 * (y c1 * z c2 - y c2 * z c1) ≠ 0) : 3 ≤ rootRankQ C := by
  let φ : (Fin 6 → ℤ) → (Fin 6 → ℚ) := fun α i => ((α i : ℤ) : ℚ)
  have hmat : (!![φ x c1, φ y c1, φ z c1; φ x c2, φ y c2, φ z c2; φ x c3, φ y c3, φ z c3] :
      Matrix (Fin 3) (Fin 3) ℚ).det ≠ 0 := by
    rw [Matrix.det_fin_three]
    simp only [φ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const]
    intro h0
    apply hdet
    have : ((x c1 * (y c2 * z c3 - y c3 * z c2) - x c2 * (y c1 * z c3 - y c3 * z c1) +
      x c3 * (y c1 * z c2 - y c2 * z c1) : ℤ) : ℚ) = 0 := by
      push_cast
      linear_combination h0
    exact_mod_cast this
  have hli := linearIndependent_of_det' (x := φ x) (y := φ y) (z := φ z) c1 c2 c3 hmat
  have hfin : Module.finrank ℚ (Submodule.span ℚ (Set.range ![φ x, φ y, φ z])) = 3 := by
    rw [finrank_span_eq_card hli]
    simp
  unfold rootRankQ
  rw [← hfin]
  apply Submodule.finrank_mono
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  fin_cases k
  · exact Submodule.subset_span ⟨x, hx, rfl⟩
  · exact Submodule.subset_span ⟨y, hy, rfl⟩
  · exact Submodule.subset_span ⟨z, hz, rfl⟩

def compC' (F : Set (Fin 6 → ZMod 3)) (a0 : Fin 6 → ℤ) : Set (Fin 6 → ℤ) :=
  {β | Relation.ReflTransGen (fun a b => (a ∈ rootsE6 ∧ ∀ f ∈ F, ∑ i, ((a i : ℤ) : ZMod 3) * f i = 0) ∧
    (b ∈ rootsE6 ∧ ∀ f ∈ F, ∑ i, ((b i : ℤ) : ZMod 3) * f i = 0) ∧ cartanForm a b ≠ 0) a0 β}

theorem rootGood_of_three (F : Set (Fin 6 → ZMod 3)) {a0 b2 b3 : Fin 6 → ℤ}
    (ha0 : a0 ∈ rootsE6 ∧ ∀ f ∈ F, ∑ i, ((a0 i : ℤ) : ZMod 3) * f i = 0)
    (hb2 : b2 ∈ rootsE6 ∧ ∀ f ∈ F, ∑ i, ((b2 i : ℤ) : ZMod 3) * f i = 0)
    (hb3 : b3 ∈ rootsE6 ∧ ∀ f ∈ F, ∑ i, ((b3 i : ℤ) : ZMod 3) * f i = 0)
    (hadj2 : b2 = a0 ∨ cartanForm a0 b2 ≠ 0) (hadj3 : b3 = a0 ∨ cartanForm a0 b3 ≠ 0)
    (c1 c2 c3 : Fin 6)
    (hdet : a0 c1 * (b2 c2 * b3 c3 - b2 c3 * b3 c2) - a0 c2 * (b2 c1 * b3 c3 - b2 c3 * b3 c1) +
      a0 c3 * (b2 c1 * b3 c2 - b2 c2 * b3 c1) ≠ 0) : RootGood F := by
  set r := fun a b : Fin 6 → ℤ => (a ∈ rootsE6 ∧ ∀ f ∈ F, ∑ i, ((a i : ℤ) : ZMod 3) * f i = 0) ∧
    (b ∈ rootsE6 ∧ ∀ f ∈ F, ∑ i, ((b i : ℤ) : ZMod 3) * f i = 0) ∧ cartanForm a b ≠ 0 with hr
  have hC : ∀ β ∈ compC' F a0, β ∈ rootsE6 ∧ ∀ f ∈ F, ∑ i, ((β i : ℤ) : ZMod 3) * f i = 0 := by
    intro β hβ
    induction hβ with
    | refl => exact ha0
    | tail _ hbc _ => exact hbc.2.1
  have hchain : ∀ β, Relation.ReflTransGen r a0 β →
      Relation.ReflTransGen (fun a b => a ∈ compC' F a0 ∧ b ∈ compC' F a0 ∧ cartanForm a b ≠ 0)
        a0 β := by
    intro β hβ
    induction hβ with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hab hbc ih =>
      exact Relation.ReflTransGen.tail ih ⟨hab, Relation.ReflTransGen.tail hab hbc, hbc.2.2⟩
  have hconn : IsRootConnected (compC' F a0) := by
    intro x hx y hy
    have hsymm : Symmetric (fun a b => a ∈ compC' F a0 ∧ b ∈ compC' F a0 ∧ cartanForm a b ≠ 0) :=
      fun a b hab => ⟨hab.2.1, hab.1, by rw [cartanForm_comm]; exact hab.2.2⟩
    haveI : Std.Symm (fun a b => a ∈ compC' F a0 ∧ b ∈ compC' F a0 ∧ cartanForm a b ≠ 0) :=
      ⟨hsymm⟩
    have hx' := (Relation.ReflTransGen.symmetric (r := fun a b => a ∈ compC' F a0 ∧
      b ∈ compC' F a0 ∧ cartanForm a b ≠ 0)).symm _ _ (hchain x hx)
    exact hx'.trans (hchain y hy)
  have hmem : ∀ b, b ∈ rootsE6 ∧ (∀ f ∈ F, ∑ i, ((b i : ℤ) : ZMod 3) * f i = 0) →
      (b = a0 ∨ cartanForm a0 b ≠ 0) → b ∈ compC' F a0 := by
    intro b hb hadj
    rcases hadj with h | h
    · rw [h]; exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨ha0, hb, h⟩
  refine ⟨compC' F a0, fun β hβ => (hC β hβ).1, hconn, ?_, fun α hα f hf => (hC α hα).2 f hf⟩
  exact three_le_rootRankQ' _ Relation.ReflTransGen.refl (hmem b2 hb2 hadj2) (hmem b3 hb3 hadj3)
    c1 c2 c3 hdet

theorem rootOK_spec {fs : List (List ℕ)} {r : ℕ × List ℕ} (h : rootOK fs r = true) :
    rootF (rootW r.1 r.2) ∈ rootsE6 ∧
      ∀ f ∈ fs, ∑ i, ((rootF (rootW r.1 r.2) i : ℤ) : ZMod 3) * vecF f i = 0 := by
  simp only [rootOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  exact ⟨rootF_rootW_mem h.1.1 h.1.2, fun f hf => pair_eq_zero (h.2 f hf)⟩

theorem getD_lt {l : List ℤ} {c : ℕ} (hc : c < 6) : l.getD c 0 = rootF l ⟨c, hc⟩ := rfl

theorem rootGood_of_witOK1 {w : Wit} (h : witOK1 w = true) :
    RootGood (vecF '' {f | f ∈ w.2.1}) := by
  obtain ⟨m, fs, rs, cs⟩ := w
  unfold witOK1 at h
  split at h
  next r₀ r₂ r₃ c₁ c₂ c₃ _ _ =>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Bool.or_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, h0⟩, h2⟩, h3⟩, ha2⟩, ha3⟩, hc1⟩, hc2⟩, hc3⟩, hdet⟩ := h
    have conv : ∀ r : ℕ × List ℕ, rootOK fs r = true →
        rootF (rootW r.1 r.2) ∈ rootsE6 ∧ ∀ f ∈ vecF '' {f | f ∈ fs},
          ∑ i, ((rootF (rootW r.1 r.2) i : ℤ) : ZMod 3) * f i = 0 := by
      intro r hr
      obtain ⟨hr1, hr2⟩ := rootOK_spec hr
      exact ⟨hr1, by rintro _ ⟨f, hf, rfl⟩; exact hr2 f hf⟩
    have adj : ∀ a b : List ℤ, (b = a ∨ cformL a b ≠ 0) → (rootF b = rootF a ∨
        cartanForm (rootF a) (rootF b) ≠ 0) := by
      intro a b hab
      rcases hab with e | e
      · exact Or.inl (by rw [e])
      · exact Or.inr (by rwa [← cformL_eq])
    refine rootGood_of_three _ (conv r₀ h0) (conv r₂ h2) (conv r₃ h3) (adj _ _ ha2) (adj _ _ ha3)
      ⟨c₁, hc1⟩ ⟨c₂, hc2⟩ ⟨c₃, hc3⟩ ?_
    simpa only [det3L, getD_lt hc1, getD_lt hc2, getD_lt hc3] using hdet
  next => exact absurd h (by simp)

theorem vecF_mvL (A : List (List ℕ)) (f : List ℕ) :
    vecF (mvL A f) = Matrix.mulVec (dec A) (vecF f) := by
  funext i
  rw [vecF, mvL, getD_mkV, ZMod.natCast_mod]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_six, dec_apply, vecF, Nat.cast_add,
    Nat.cast_mul]
  rfl

theorem vecF_addV (a b : List ℕ) : vecF (addV a b) = vecF a + vecF b := by
  funext i
  rw [vecF, addV, getD_mkV, ZMod.natCast_mod]
  simp [vecF]

theorem vecF_negV (a : List ℕ) : vecF (negV a) = -vecF a := by
  funext i
  rw [vecF, negV, getD_mkV, ZMod.natCast_mod]
  have h2 : (2 : ZMod 3) = -1 := by decide
  simp [vecF, h2]

theorem vecF_zero : vecF (mkV fun _ => 0) = 0 := by
  funext i
  rw [vecF, getD_mkV]
  simp

theorem vecF_inj {a b : List ℕ} (ha : wfV a = true) (hb : wfV b = true) (e : vecF a = vecF b) :
    a = b := by
  simp only [wfV, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at ha hb
  refine List.ext_getElem (ha.1.trans hb.1.symm) fun i h1 h2 => ?_
  have hi : i < 6 := ha.1 ▸ h1
  have := congrFun e ⟨i, hi⟩
  simp only [vecF, List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (ha.2 _ (List.getElem_mem h1)),
    Nat.mod_eq_of_lt (hb.2 _ (List.getElem_mem h2))] at this
  exact this

def addSubOf' (fs : List (List ℕ)) (h : fsOK fs = true) : AddSubgroup (Fin 6 → ZMod 3) where
  carrier := vecF '' {f | f ∈ fs}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    simp only [fsOK, Bool.and_eq_true, List.all_eq_true, List.contains_iff] at h
    exact ⟨addV a b, h.1.2 a ha b hb, vecF_addV a b⟩
  zero_mem' := by
    simp only [fsOK, Bool.and_eq_true, List.contains_iff] at h
    exact ⟨_, h.1.1.2, vecF_zero⟩
  neg_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [fsOK, Bool.and_eq_true, List.all_eq_true, List.contains_iff] at h
    exact ⟨negV a, h.2 a ha, vecF_negV a⟩

theorem card_addSubOf' (fs : List (List ℕ)) (h : fsOK fs = true) :
    Nat.card (addSubOf' fs h) = 9 := by
  have h' := h
  simp only [fsOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨hlen, hnod⟩, hwf⟩, -⟩, -⟩, -⟩ := h'
  have hinj : Set.InjOn vecF ((fs.toFinset : Finset (List ℕ)) : Set (List ℕ)) := by
    intro a ha b hb e
    simp only [Finset.mem_coe, List.mem_toFinset] at ha hb
    exact vecF_inj (hwf a ha) (hwf b hb) e
  have hset : ((addSubOf' fs h : AddSubgroup (Fin 6 → ZMod 3)) : Set (Fin 6 → ZMod 3)) =
      vecF '' ((fs.toFinset : Finset (List ℕ)) : Set (List ℕ)) := by
    ext v
    change v ∈ vecF '' {f | f ∈ fs} ↔ v ∈ vecF '' ((fs.toFinset : Finset (List ℕ)) : Set (List ℕ))
    simp
  change Nat.card ((addSubOf' fs h : AddSubgroup (Fin 6 → ZMod 3)) : Set (Fin 6 → ZMod 3)) = 9
  rw [Nat.card_coe_set_eq, hset, hinj.ncard_image, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnod, hlen]

theorem fixOK_props {gw : List (List ℕ)} {mel fixS : List (List ℕ)}
    {fixE : List (List (List ℕ))} {fixY : List (List (ℕ × List (List ℕ)))} {wit : List Wit}
    (h : fixOK gw mel fixS fixE fixY wit = true) {H : List (List (List ℕ))}
    (hH : H ∈ mel.map (famM (qEls gw))) :
    ∃ (S : List ℕ) (E : List (List ℕ)) (Ys : List (ℕ × List (List ℕ))),
      (∀ p ∈ Ys, (qEls gw).getD p.1 idL ∈ H) ∧
      subL idL E = Ys.foldr (fun p acc => addL (mulL p.2 (subL ((qEls gw).getD p.1 idL) idL))
        acc) zeroL ∧
      (∀ j ∈ S, j < 6) ∧ (∀ i j : Fin 6, (j : ℕ) ∉ S → ent E i j = 0) ∧
      H.length ≤ 27 ∧ (H.length = 9 → S.length ≤ 2) ∧ (H.length = 27 → S.length ≤ 1) ∧
      (H.length = 3 → S.length ≤ 4) ∧
      (H.length = 3 → S.length = 4 → ∃ w ∈ wit, witOK1 w = true ∧
        ∀ A ∈ H, ∀ f ∈ w.2.1, mvL A f = f) := by
  obtain ⟨mm, hmm, rfl⟩ := List.mem_map.1 hH
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hmm
  unfold fixOK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have hm' := h.2 m (List.mem_range.2 hm)
  dsimp only at hm'
  rw [List.getD_eq_getElem _ _ hm] at hm'
  simp only [Bool.and_eq_true] at hm'
  obtain ⟨⟨⟨⟨⟨hY, hEq⟩, hS⟩, hcol⟩, hb⟩, hw⟩ := hm'
  simp only [List.all_eq_true, List.contains_iff] at hY
  rw [beq_iff_eq] at hEq
  simp only [List.all_eq_true, decide_eq_true_eq] at hS
  refine ⟨fixS.getD m [], fixE.getD m [], fixY.getD m [], hY, hEq, hS, ?_, ?_⟩
  · intro i j hj
    simp only [colsZero, List.all_eq_true, List.mem_range, Bool.or_eq_true, List.contains_iff,
      beq_iff_eq] at hcol
    exact (hcol i i.isLt j j.isLt).resolve_left hj
  · simp only [boundOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne,
      ne_eq] at hb
    obtain ⟨⟨⟨h27, h9⟩, h27'⟩, h3⟩ := hb
    refine ⟨h27, fun e => h9.resolve_left (not_not.2 e), fun e => h27'.resolve_left (not_not.2 e),
      fun e => h3.resolve_left (not_not.2 e), fun e3 e4 => ?_⟩
    rw [Bool.or_eq_true] at hw
    rcases hw with hw | hw
    · rw [e3, e4] at hw
      exact absurd hw (by decide)
    · obtain ⟨w, hw, hwm⟩ := List.any_eq_true.1 hw
      rw [Bool.and_eq_true, Bool.and_eq_true] at hwm
      refine ⟨w, hw, hwm.1.2, fun A hA f hf => ?_⟩
      have h1 := List.all_eq_true.1 hwm.2 A hA
      exact beq_iff_eq.1 (List.all_eq_true.1 h1 f hf)

theorem claims_qSub {gw : List (List ℕ)} {mel fixS : List (List ℕ)}
    {fixE : List (List (List ℕ))} {fixY : List (List (ℕ × List (List ℕ)))} {wit : List Wit}
    (hq : qOK gw = true) (hf : famOK gw mel = true) (hx : fixOK gw mel fixS fixE fixY wit = true)
    {R : Subgroup GL6} (hRQ : R ≤ qSub gw) (hA : IsElemAbelian 3 R) {r : ℕ}
    (hr : Nat.card R = 3 ^ r) :
    r ≤ 3 ∧ (2 ≤ r → Nat.card (fixVec R) ≤ 3 ^ (4 - r)) ∧
      (r = 1 → Nat.card (fixVec R) ≤ 81 ∧ (81 ≤ Nat.card (fixVec R) →
        ∃ F : AddSubgroup (Fin 6 → ZMod 3), (F : Set (Fin 6 → ZMod 3)) ⊆ fixVec R ∧
          Nat.card F = 9 ∧ RootGood (F : Set (Fin 6 → ZMod 3)))) := by
  obtain ⟨H, hH, hMat⟩ := exists_fam hq hf r R hRQ hA hr
  have hlen : H.length = 3 ^ r := by rw [← card_eq_length hf hH hMat, hr]
  obtain ⟨S, E, Ys, hY, hEq, hS, hcol, h27, h9, h27', h3, hw⟩ := fixOK_props hx hH
  have hfix := card_fixVec_le hMat (fun i => (qEls gw).getD i idL) hY hEq hS hcol
  clear hY hEq hcol
  have h27r : 3 ^ r ≤ 3 ^ 3 := by rw [← hlen]; exact h27
  have hr3 : r ≤ 3 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h27r
  refine ⟨hr3, fun h2 => ?_, fun h1 => ?_⟩
  · have hr23 : r = 2 ∨ r = 3 := by omega
    rcases hr23 with rfl | rfl
    · exact hfix.trans (Nat.pow_le_pow_right (by norm_num) (h9 (by rw [hlen]; norm_num)))
    · exact hfix.trans (Nat.pow_le_pow_right (by norm_num) (h27' (by rw [hlen]; norm_num)))
  · subst h1
    have hl3 : H.length = 3 := by rw [hlen]; norm_num
    have hk := h3 hl3
    refine ⟨hfix.trans (by simpa using Nat.pow_le_pow_right (n := 3) (by norm_num) hk),
      fun h81 => ?_⟩
    have hk4 : S.length = 4 := by
      have : 3 ^ 4 ≤ 3 ^ S.length := by simpa using h81.trans hfix
      have := (Nat.pow_le_pow_iff_right (by norm_num)).1 this
      omega
    obtain ⟨w, -, hwOK, hcov⟩ := hw hl3 hk4
    have hfs : fsOK w.2.1 = true := by
      unfold witOK1 at hwOK
      split at hwOK
      · simp only [Bool.and_eq_true] at hwOK
        exact hwOK.1.1.1.1.1.1.1.1.1
      · exact absurd hwOK (by simp)
    refine ⟨addSubOf' w.2.1 hfs, ?_, card_addSubOf' _ _, rootGood_of_witOK1 hwOK⟩
    rintro _ ⟨f, hf, rfl⟩ g hg
    have hmem : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ Mat R := ⟨g, hg, rfl⟩
    rw [hMat] at hmem
    obtain ⟨A, hA', e⟩ := hmem
    rw [← e, ← vecF_mvL, hcov A hA' f hf]

end CFSG.KC.X2E6Syl

end
