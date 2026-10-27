module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W1
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4CheckC
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeClasses
public import Certificates.Certificate416101

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.Blueprint

namespace O8Pi

open CFSG.EvenSmallLie.OmegaEight CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover
open CFSG.ClassicalInvolution.Q3.TL4.E4C

theorem piGens_size : (piGens ()).size = 4 := by
  simp [piGens, piIdx]

theorem piS_size : (piS ()).size = 6 := by
  rw [piS, size_pushWords, piGens_size]
  rfl

@[expose] noncomputable def piQ : RawSchreierDatum 360 :=
  RawSchreierDatum.ofArrays 360 (by norm_num) (piS ()) 4 (by rw [piS_size]; norm_num) piBase
    (by decide) (wordsOf 4 piWords)

@[expose] noncomputable def piT : Subgroup (Equiv.Perm (Fin 360)) := piQ.originalSubgroup

theorem piS_getElem! {i : ℕ} (hi : i < 4) : (piS ())[i]! = genArrs[piIdx.getD i 0]! := by
  rw [piS, pushWords_getElem! _ _ (by rw [piGens_size]; exact hi), piGens,
    getElem!_pos _ i (by simpa [piIdx] using hi), Array.getElem_map]
  congr 1
  interval_cases i <;> rfl

theorem piT_le_omegaT : piT ≤ omegaT := by
  rw [piT, piQ, ofArrays_originalSubgroup, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  rw [piS_getElem! hi]
  exact gen_mem_omegaT (by interval_cases i <;> decide)

theorem check_parts (h : check () = true) :
    piChainCheck (piS ()) = true ∧
      ((testA (piS ())).all fun c => isInvA 360 c (invCand 360 c)) = true ∧
      q8Check (piS ()) = true := by
  simp only [check, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem chain_ok (h : check () = true) :
    rawChainOK 360 ((piS ()).extract 0 4) (piS ()) (piBase.map Fin.val).toArray
        (wordsOf 4 piWords) 4 = true ∧
      rawOrbitSizes 360 (piS ()) (piBase.map Fin.val).toArray = [64, 4, 4, 4] := by
  have h1 := (check_parts h).1
  simp only [piChainCheck, Bool.and_eq_true, beq_iff_eq] at h1
  exact h1

theorem card_piT (h : check () = true) : Nat.card piT = 4096 := by
  rw [piT, piQ, ofArrays_card (by norm_num) (chain_ok h).1, (chain_ok h).2]
  rfl

theorem piQ_valid (h : check () = true) : ValidSchreier piQ :=
  ofArrays_valid (by norm_num) (chain_ok h).1

@[expose] noncomputable def cOne : Equiv.Perm (Fin 360) :=
  permOfArr 360 (wordA 360 (piS ()) (rawInvs 360 (piS ())) [1, 2])

@[expose] noncomputable def cTwo : Equiv.Perm (Fin 360) :=
  permOfArr 360 (wordA 360 (piS ()) (rawInvs 360 (piS ())) [3, 6])

theorem cOne_spec (h : check () = true) :
    CFSG.Monster.B.Co2.Rep 360 (wordA 360 (piS ()) (rawInvs 360 (piS ())) [1, 2]) cOne ∧
      cOne ∈ piT :=
  chain_word_mem (chain_ok h).1 [1, 2] (by rw [piS_size]; rfl)

theorem cTwo_spec (h : check () = true) :
    CFSG.Monster.B.Co2.Rep 360 (wordA 360 (piS ()) (rawInvs 360 (piS ())) [3, 6]) cTwo ∧
      cTwo ∈ piT :=
  chain_word_mem (chain_ok h).1 [3, 6] (by rw [piS_size]; rfl)

theorem testT_spec (h : check () = true) :
    ∀ c ∈ [cOne, cTwo, cOne⁻¹ * cTwo], ∃ cT dT : Table, (cT, dT) ∈ testT (piS ()) ∧
      CFSG.Sporadic.Th.Rep 360 cT c ∧ CFSG.Sporadic.Th.Rep 360 dT c⁻¹ := by
  have hn : (360 : ℕ) < 2 ^ 32 := by norm_num
  have hinv := (check_parts h).2.1
  simp only [testA, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hinv
  obtain ⟨h1, h2, h3⟩ := hinv
  have r1 := (cOne_spec h).1
  have r2 := (cTwo_spec h).1
  have r1i := rep_inv_of_isInvA r1 h1
  have r3 := rep_compA r1i r2
  have r3i := rep_inv_of_isInvA r3 h3
  have e : testT (piS ()) =
      [(arrTable 360 (wordA 360 (piS ()) (rawInvs 360 (piS ())) [1, 2]),
          arrTable 360 (invCand 360 (wordA 360 (piS ()) (rawInvs 360 (piS ())) [1, 2]))),
        (arrTable 360 (wordA 360 (piS ()) (rawInvs 360 (piS ())) [3, 6]),
          arrTable 360 (invCand 360 (wordA 360 (piS ()) (rawInvs 360 (piS ())) [3, 6]))),
        (arrTable 360 (compA 360 (invCand 360 (wordA 360 (piS ()) (rawInvs 360 (piS ())) [1, 2]))
            (wordA 360 (piS ()) (rawInvs 360 (piS ())) [3, 6])),
          arrTable 360 (invCand 360 (compA 360
            (invCand 360 (wordA 360 (piS ()) (rawInvs 360 (piS ())) [1, 2]))
            (wordA 360 (piS ()) (rawInvs 360 (piS ())) [3, 6]))))] := rfl
  intro c hc
  rw [e]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ⟨_, _, List.mem_cons_self, rep_arrTable hn r1, rep_arrTable hn r1i⟩
  · exact ⟨_, _, List.mem_cons_of_mem _ List.mem_cons_self, rep_arrTable hn r2,
      rep_arrTable hn (rep_inv_of_isInvA r2 h2)⟩
  · exact ⟨_, _, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      rep_arrTable hn r3, rep_arrTable hn r3i⟩

@[expose] def bimg (g : Equiv.Perm (Fin 360)) : List ℕ := baseN.map (idx 360 g)

@[expose] def PtRep (f : ℕ → ℕ) (g : Equiv.Perm (Fin 360)) : Prop :=
  ∀ i < 360, f i = idx 360 g i

theorem lt_of_mem_baseN {b : ℕ} (hb : b ∈ baseN) : b < 360 := by
  simp only [baseN, List.mem_cons, List.not_mem_nil, or_false] at hb
  omega

theorem ptRep_id : PtRep id 1 := fun i _ => (idx_one i).symm

theorem ptRep_comp {T : Table} {g h : Equiv.Perm (Fin 360)} {f : ℕ → ℕ}
    (hT : CFSG.Sporadic.Th.Rep 360 T g) (hf : PtRep f h) : PtRep (fun i => ap T (f i)) (g * h) := by
  intro i hi
  show ap T (f i) = _
  rw [hf i hi, hT _ (idx_lt h hi), idx_mul]

theorem imgs_eq {f : ℕ → ℕ} {g : Equiv.Perm (Fin 360)} (hf : PtRep f g) : imgs f = bimg g :=
  List.map_congr_left fun b hb => hf b (lt_of_mem_baseN hb)

theorem q8Imgs_eq {x y : Table} {X Y : Equiv.Perm (Fin 360)} (hx : CFSG.Sporadic.Th.Rep 360 x X)
    (hy : CFSG.Sporadic.Th.Rep 360 y Y) : q8Imgs x y = (q8Elems (X * X) X Y).map bimg := by
  have hX : PtRep (ap x) X := hx
  have hY : PtRep (ap y) Y := hy
  have e1 : imgs id = bimg 1 := imgs_eq ptRep_id
  have e2 : imgs (fun b => ap x (ap x b)) = bimg (X * X) := imgs_eq (ptRep_comp hx hX)
  have e3 : imgs (ap x) = bimg X := imgs_eq hX
  have e4 : imgs (fun b => ap x (ap x (ap x b))) = bimg (X * (X * X)) :=
    imgs_eq (ptRep_comp hx (ptRep_comp hx hX))
  have e5 : imgs (ap y) = bimg Y := imgs_eq hY
  have e6 : imgs (fun b => ap y (ap x (ap x b))) = bimg (Y * (X * X)) :=
    imgs_eq (ptRep_comp hy (ptRep_comp hx hX))
  have e7 : imgs (fun b => ap x (ap y b)) = bimg (X * Y) := imgs_eq (ptRep_comp hx hY)
  have e8 : imgs (fun b => ap x (ap y (ap x (ap x b)))) = bimg (X * Y * (X * X)) := by
    rw [mul_assoc]
    exact imgs_eq (ptRep_comp hx (ptRep_comp hy (ptRep_comp hx hX)))
  simp only [q8Imgs, q8Elems, List.map_cons, List.map_nil, e1, e2, e3, e4, e5, e6, e7, e8]

theorem conjImg_eq {cT dT : Table} {c : Equiv.Perm (Fin 360)}
    (hc : CFSG.Sporadic.Th.Rep 360 cT c) (hd : CFSG.Sporadic.Th.Rep 360 dT c⁻¹) {x : Table}
    {X : Equiv.Perm (Fin 360)} (hx : CFSG.Sporadic.Th.Rep 360 x X) :
    conjImg (cT, dT) x = bimg (c * X * c⁻¹) := by
  rw [mul_assoc]
  exact imgs_eq (ptRep_comp hc (ptRep_comp hx hd))

theorem presB_of {x y : Table} {X Y : Equiv.Perm (Fin 360)} (hx : CFSG.Sporadic.Th.Rep 360 x X)
    (hy : CFSG.Sporadic.Th.Rep 360 y Y) (h : Y * X = X * X * X * Y) : presB x y = true := by
  have hX : PtRep (ap x) X := hx
  have hY : PtRep (ap y) Y := hy
  have e1 : PtRep (fun b => ap y (ap x b)) (Y * X) := ptRep_comp hy hX
  have e2 : PtRep (fun b => ap x (ap x (ap x (ap y b)))) (X * (X * (X * Y))) :=
    ptRep_comp hx (ptRep_comp hx (ptRep_comp hx hY))
  unfold presB
  rw [List.all_eq_true]
  intro b hb
  have hb' := lt_of_mem_baseN hb
  have e1' : ap y (ap x b) = idx 360 (Y * X) b := e1 b hb'
  have e2' : ap x (ap x (ap x (ap y b))) = idx 360 (X * (X * (X * Y))) b := e2 b hb'
  rw [beq_iff_eq, e1', e2', h]
  simp only [mul_assoc]

theorem sqMoves_of {T : Table} {g : Equiv.Perm (Fin 360)} (hT : CFSG.Sporadic.Th.Rep 360 T g)
    (h : g * g ≠ 1) : sqMoves T = true := by
  have e : PtRep (fun i => ap T (ap T i)) (g * g) := ptRep_comp hT hT
  unfold sqMoves
  rw [List.any_eq_true]
  by_contra hno
  apply h
  ext i
  have hi := List.mem_range.2 i.2
  have h1 : ¬ (ap T (ap T i.val) != i.val) = true := fun h' => hno ⟨i.val, hi, h'⟩
  have ei : ap T (ap T i.val) = idx 360 (g * g) i.val := e i.val i.2
  rw [bne_iff_ne, not_not, ei, idx_of_lt _ i.2] at h1
  simpa using congrArg Fin.val (show ((g * g) • i) = i from Fin.ext h1)

theorem sqMoves_iff {T : Table} {g : Equiv.Perm (Fin 360)} (hT : CFSG.Sporadic.Th.Rep 360 T g) :
    sqMoves T = true ↔ g * g ≠ 1 := by
  refine ⟨fun hs h1 => ?_, sqMoves_of hT⟩
  have e : PtRep (fun i => ap T (ap T i)) (g * g) := ptRep_comp hT hT
  unfold sqMoves at hs
  obtain ⟨i, hi, hne⟩ := List.any_eq_true.1 hs
  rw [List.mem_range] at hi
  have ei : ap T (ap T i) = idx 360 (g * g) i := e i hi
  rw [bne_iff_ne, ei, h1, idx_one] at hne
  exact hne rfl

theorem sqKey_eq {T : Table} {g : Equiv.Perm (Fin 360)} (hT : CFSG.Sporadic.Th.Rep 360 T g) :
    sqKey T = bimg (g * g) :=
  imgs_eq (ptRep_comp hT hT)

theorem mem_sqList (h : check () = true) {x : Equiv.Perm (Fin 360)} (hx : x ∈ piT)
    (hx2 : x * x ≠ 1) :
    ∃ T, CFSG.Sporadic.Th.Rep 360 T x ∧ (T, sqKey T) ∈ sqList (piS ()) := by
  classical
  have hn : (360 : ℕ) < 2 ^ 32 := by norm_num
  have hQv := piQ_valid h
  have hlev : levelTables piQ = chainTables 360 (piS ()) (piBase.map Fin.val).toArray :=
    ofArrays_levelTables (chain_ok h).1
  have hs := filterProducts_spec (P := fun g : Equiv.Perm (Fin 360) => g * g ≠ 1)
    (f := sqMoves) (fun T g hT => sqMoves_iff hT) (forall₂_levelTables hn piQ)
    (CFSG.Sporadic.Th.Rep.idT hn) (acc := []) (accG := []) List.Forall₂.nil
  simp only [List.append_nil] at hs
  have hmem : x ∈ (((enumeration piQ).map (1 * ·)).filter fun g =>
      decide (g * g ≠ 1)).reverse := by
    rw [List.mem_reverse, List.mem_filter, List.mem_map]
    exact ⟨⟨x, (mem_enumeration_iff piQ hQv x).2 hx, one_mul x⟩, by simpa using hx2⟩
  obtain ⟨T, hT, hTx⟩ := EvenSmallLie.OmegaEight.exists_of_forall₂_mem_right hs hmem
  rw [hlev] at hT
  exact ⟨T, hTx, List.mem_map_of_mem hT⟩

theorem q8_spec (h : check () = true) {x y : Equiv.Perm (Fin 360)} (hx : x ∈ piT) (hy : y ∈ piT)
    (hx2 : x * x ≠ 1) (hyy : y * y = x * x) (hyx : y * x = x * x * x * y) :
    ∀ c ∈ [cOne, cTwo, cOne⁻¹ * cTwo],
      ¬ (c * x * c⁻¹ ∈ q8Elems (x * x) x y ∧ c * y * c⁻¹ ∈ q8Elems (x * x) x y) := by
  obtain ⟨Tx, hTx, hPx⟩ := mem_sqList h hx hx2
  obtain ⟨Ty, hTy, hPy⟩ := mem_sqList h hy (hyy ▸ hx2)
  have hkey : sqKey Ty = sqKey Tx := by rw [sqKey_eq hTx, sqKey_eq hTy, hyy]
  have hq := (check_parts h).2.2
  simp only [q8Check, List.all_eq_true] at hq
  have hk : sqKey Tx ∈ ((sqList (piS ())).map Prod.snd).dedup :=
    List.mem_dedup.2 (List.mem_map.2 ⟨_, hPx, rfl⟩)
  have hxB : Tx ∈ ((sqList (piS ())).filter fun p => p.2 == sqKey Tx).map Prod.fst :=
    List.mem_map.2 ⟨_, List.mem_filter.2 ⟨hPx, by simp⟩, rfl⟩
  have hyB : Ty ∈ ((sqList (piS ())).filter fun p => p.2 == sqKey Tx).map Prod.fst :=
    List.mem_map.2 ⟨_, List.mem_filter.2 ⟨hPy, by simp [hkey]⟩, rfl⟩
  have hpair := hq _ hk Tx hxB Ty hyB
  unfold pairB at hpair
  rw [presB_of hTx hTy hyx, Bool.not_true, Bool.false_or, List.all_eq_true] at hpair
  intro c hc ⟨h1, h2⟩
  obtain ⟨cT, dT, hp, hcT, hdT⟩ := testT_spec h c hc
  have hm := hpair _ hp
  unfold movesB at hm
  rw [q8Imgs_eq hTx hTy, conjImg_eq hcT hdT hTx, conjImg_eq hcT hdT hTy] at hm
  have hm1 : (List.map bimg (q8Elems (x * x) x y)).contains (bimg (c * x * c⁻¹)) = true :=
    List.elem_iff.2 (List.mem_map_of_mem h1)
  have hm2 : (List.map bimg (q8Elems (x * x) x y)).contains (bimg (c * y * c⁻¹)) = true :=
    List.elem_iff.2 (List.mem_map_of_mem h2)
  rw [hm1, hm2] at hm
  exact absurd hm (by decide)

section Cert


theorem conjSub_ne {B : Subgroup (Equiv.Perm (Fin 360))} (hB : B ≤ piT)
    (e : ↥B ≃* QuaternionGroup 2) : ∀ c ∈ [cOne, cTwo, cOne⁻¹ * cTwo], conjSub c B ≠ B := by
  have h := Certificates.certificate416101
  set ρ : Equiv.Perm (Fin 360) := ((e.symm (QuaternionGroup.a 1) : ↥B) : Equiv.Perm (Fin 360))
  have hρB : ρ ∈ B := (e.symm (QuaternionGroup.a 1)).2
  have hρ2 : ρ * ρ ≠ 1 := by
    intro h1
    have h2 : e.symm (QuaternionGroup.a 1 * QuaternionGroup.a 1) = 1 := by
      rw [map_mul]
      exact Subtype.ext h1
    have h3 := congrArg e h2
    rw [MulEquiv.apply_symm_apply, map_one] at h3
    exact absurd h3 (by decide)
  obtain ⟨j, hjB, hjj, hjρ, hiff⟩ := exists_q8_gen e hρB hρ2
  have h4 : ρ * ρ * (ρ * ρ) = 1 := by
    have e1 : j * (ρ * ρ) * j⁻¹ = (j * ρ * j⁻¹) * (j * ρ * j⁻¹) := by group
    have e2 : j * (ρ * ρ) * j⁻¹ = ρ * ρ := by
      rw [← hjj]
      group
    rw [e2, hjρ] at e1
    calc ρ * ρ * (ρ * ρ) = ρ⁻¹ * ρ⁻¹ * (ρ * ρ) := by rw [← e1]
      _ = 1 := by group
  have hjx : j * ρ = ρ * ρ * ρ * j := by
    have hinv : ρ⁻¹ = ρ * ρ * ρ := by
      rw [inv_eq_iff_mul_eq_one]
      rw [← h4]
      group
    calc j * ρ = (j * ρ * j⁻¹) * j := by group
      _ = ρ * ρ * ρ * j := by rw [hjρ, hinv]
  intro c hc heq
  apply q8_spec h (hB hρB) (hB hjB) hρ2 hjj hjx c hc
  constructor
  · rw [← hiff, ← heq]
    exact Generic.conj_mem_conjSub hρB
  · rw [← hiff, ← heq]
    exact Generic.conj_mem_conjSub hjB

theorem exists_three {B : Subgroup (Equiv.Perm (Fin 360))} (hB : B ≤ piT)
    (e : ↥B ≃* QuaternionGroup 2) :
    cOne ∈ piT ∧ cTwo ∈ piT ∧ conjSub cOne B ≠ B ∧ conjSub cTwo B ≠ B ∧
      conjSub cOne B ≠ conjSub cTwo B := by
  have h := Certificates.certificate416101
  have hn := conjSub_ne hB e
  refine ⟨(cOne_spec h).2, (cTwo_spec h).2, hn _ List.mem_cons_self,
    hn _ (List.mem_cons_of_mem _ List.mem_cons_self), fun h12 => ?_⟩
  apply hn _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  rw [conjSub_mul, ← h12, conjSub_inv_conjSub]

theorem isSylow2In_piT : IsSylow2In piT omegaT := by
  have h := Certificates.certificate416101
  have hcard := card_piT h
  refine ⟨piT_le_omegaT, IsPGroup.of_card (n := 12) (by rw [hcard]; norm_num),
    fun V hVle hV2 hle => ?_⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hV2
  have hdvd : 2 ^ m ∣ 174182400 := by
    rw [← hm, ← card_omegaT]
    exact Subgroup.card_dvd_of_le hVle
  have hm12 : m ≤ 12 := by
    by_contra hlt
    rw [not_le] at hlt
    have h13 : 2 ^ 13 ∣ 174182400 := (Nat.pow_dvd_pow 2 hlt).trans hdvd
    norm_num at h13
  have hVcard : Nat.card V ≤ Nat.card piT := by
    rw [hm, hcard]
    calc 2 ^ m ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hm12
      _ = 4096 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge hle hVcard).symm

theorem exists_conj_le_piT {A : Subgroup (Equiv.Perm (Fin 360))} (hA : IsPGroup 2 A)
    (hAle : A ≤ omegaT) : ∃ x ∈ omegaT, conjSub x A ≤ piT := by
  obtain ⟨V, hV, hAV⟩ := IsSylow2In.exists_ge hA hAle
  obtain ⟨x, hx, hxV⟩ := exists_conjSub_eq_of_isSylow2In hV isSylow2In_piT
  exact ⟨x, hx, hxV ▸ conjSub_mono hAV⟩

end Cert

section Lift

variable {W : Type} [Group W] [Finite W]

theorem conjSub_eq_of_isSylow2In {K P P₂ : Subgroup W} (hP : IsSylow2In P K)
    (h2 : IsPGroup 2 P₂) {w w' : W} (hw : conjSub w P ≤ P₂) (hw' : conjSub w' P ≤ P₂)
    (hK : conjSub w K = conjSub w' K) : conjSub w P = conjSub w' P := by
  have h1 := hP.conj w
  have h1' := hP.conj w'
  rw [← hK] at h1'
  have hT : IsPGroup 2 ↥(P₂ ⊓ conjSub w K) := h2.to_le inf_le_left
  have e1 := h1.eq_of_le hT inf_le_right (le_inf hw h1.1)
  have e2 := h1'.eq_of_le hT inf_le_right (le_inf hw' h1'.1)
  rw [← e1, ← e2]

theorem eq_one_of_map_eq_one {Q : Type} [Group Q] {f : W →* Q} (hker : IsPGroup 2 ↥f.ker)
    {K P : Subgroup W} {k : W} (hk : IsUniqueInvolution K k)
    (hO2 : ¬ ∃ P : Subgroup W, P.Normal ∧ IsPGroup 2 ↥P ∧ k ∈ P) (hPK : P ≤ K)
    (hP2 : IsPGroup 2 ↥P) {p : W} (hp : p ∈ P) (hfp : f p = 1) : p = 1 := by
  by_contra hp1
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hP2) ⟨p, hp⟩
  rw [Subgroup.orderOf_mk] at hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hm
    exact hp1 hm
  set q := p ^ 2 ^ (m - 1) with hq
  have hqq : q * q = 1 := by
    rw [hq, ← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0), ← hm,
      pow_orderOf_eq_one]
  have hq1 : q ≠ 1 := pow_ne_one_of_lt_orderOf (by positivity)
    (by rw [hm]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hqk : q = k := (hk.unique q (K.pow_mem (hPK hp) _) hqq).resolve_left hq1
  have hfq : f k = 1 := by rw [← hqk, hq, map_pow, hfp, one_pow]
  exact hO2 ⟨f.ker, f.normal_ker, hker, hfq⟩

end Lift

end O8Pi

open CFSG.EvenSmallLie.OmegaEight O8Pi in
theorem gapTwinE4O8p2_of_certs :
    GapTwinE4O8p2 := by
  intro W _ _ Φ K K' k k' h Q _ f hf hker hQ
  classical
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hQ
  set φ : W →* Equiv.Perm (Fin 360) := omegaT.subtype.comp (e.toMonoidHom.comp f)
  have hφapp : ∀ w, φ w = ((e (f w) : ↥omegaT) : Equiv.Perm (Fin 360)) := fun w => rfl
  have hφ1 : ∀ w, φ w = 1 → f w = 1 := by
    intro w hw
    rw [hφapp] at hw
    have : e (f w) = 1 := Subtype.ext hw
    rwa [MulEquiv.map_eq_one_iff] at this
  have hφker : φ.ker = f.ker := by
    ext w
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    refine ⟨hφ1 w, fun hw => ?_⟩
    rw [hφapp, hw, map_one]
    rfl
  have hlift : ∀ g ∈ omegaT, ∃ w : W, φ w = g := by
    intro g hg
    obtain ⟨w, hw⟩ := hf (e.symm ⟨g, hg⟩)
    exact ⟨w, by rw [hφapp, hw, MulEquiv.apply_symm_apply]⟩
  obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (P := K) (T := ⊥) IsPGroup.of_bot bot_le
  obtain ⟨eP⟩ := h.fam.quat K h.memK P hP
  have hPcard : Nat.card ↥P = 8 := by
    rw [Nat.card_congr eP.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rfl
  have hinj : Function.Injective (φ.domRestrict P) := by
    rw [injective_iff_map_eq_one]
    intro p hp
    exact Subtype.ext (eq_one_of_map_eq_one hker h.invK h.notO2 hP.1 hP.2.1 p.2
      (hφ1 _ hp))
  set A : Subgroup (Equiv.Perm (Fin 360)) := P.map φ
  have eA : ↥P ≃* ↥A :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range P φ))
  have hAle : A ≤ omegaT := by
    rintro _ ⟨p, -, rfl⟩
    rw [hφapp]
    exact (e (f p)).2
  obtain ⟨x, hxΩ, hxA⟩ := exists_conj_le_piT (hP.2.1.map φ) hAle
  have eB : ↥(conjSub x A) ≃* QuaternionGroup 2 :=
    ((A.equivMapOfInjective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective).symm.trans
      eA.symm).trans eP
  obtain ⟨hc1, hc2, hn1, hn2, hn12⟩ := exists_three hxA eB
  obtain ⟨w₀, hw₀⟩ := hlift x hxΩ
  obtain ⟨w₁, hw₁⟩ := hlift (cOne * x) (omegaT.mul_mem (piT_le_omegaT hc1) hxΩ)
  obtain ⟨w₂, hw₂⟩ := hlift (cTwo * x) (omegaT.mul_mem (piT_le_omegaT hc2) hxΩ)
  have hmap : ∀ w : W, (conjSub w P).map φ = conjSub (φ w) A := fun w =>
    (conjSub_map φ w P).symm
  have hB₀ : (conjSub w₀ P).map φ = conjSub x A := by rw [hmap, hw₀]
  have hB₁ : (conjSub w₁ P).map φ = conjSub cOne (conjSub x A) := by
    rw [hmap, hw₁, conjSub_mul]
  have hB₂ : (conjSub w₂ P).map φ = conjSub cTwo (conjSub x A) := by
    rw [hmap, hw₂, conjSub_mul]
  have hpi : ∀ c ∈ piT, conjSub c (conjSub x A) ≤ piT := fun c hc => by
    have := conjSub_mono (n := c) hxA
    rwa [conjSub_eq_self_of_mem hc] at this
  set P₂ : Subgroup W := piT.comap φ
  have hP₂2 : IsPGroup 2 ↥P₂ := by
    have hpi2 : IsPGroup 2 ↥piT :=
      IsPGroup.of_card (n := 12) (by rw [card_piT Certificates.certificate416101]; norm_num)
    exact hpi2.comap_of_ker_isPGroup φ (hφker ▸ hker)
  have hle : ∀ w : W, (conjSub w P).map φ ≤ piT → conjSub w P ≤ P₂ := fun w hw =>
    Subgroup.map_le_iff_le_comap.mp hw
  have hle₀ := hle w₀ (hB₀ ▸ hxA)
  have hle₁ := hle w₁ (hB₁ ▸ hpi cOne hc1)
  have hle₂ := hle w₂ (hB₂ ▸ hpi cTwo hc2)
  have hcard : ∀ w : W, conjSub w P ≤ P₂ → 2 < Nat.card ↥(conjSub w K ⊓ P₂) := by
    intro w hw
    have h8 : Nat.card ↥(conjSub w P) = 8 := by rw [natCard_conjSub, hPcard]
    have := Subgroup.card_le_of_le (le_inf (conjSub_mono (n := w) hP.1) hw)
    omega
  have hne : ∀ {w w' : W}, conjSub w P ≤ P₂ → conjSub w' P ≤ P₂ →
      (conjSub w P).map φ ≠ (conjSub w' P).map φ → conjSub w K ≠ conjSub w' K :=
    fun hw hw' hne hK => hne (by rw [conjSub_eq_of_isSylow2In hP hP₂2 hw hw' hK])
  refine ⟨P₂, conjSub w₀ K, conjSub w₁ K, conjSub w₂ K, hP₂2,
    h.fam.hyp.conjInvariant w₀ K h.memK, h.fam.hyp.conjInvariant w₁ K h.memK,
    h.fam.hyp.conjInvariant w₂ K h.memK, ?_, ?_, ?_, hcard w₀ hle₀, hcard w₁ hle₁,
    hcard w₂ hle₂⟩
  · exact hne hle₀ hle₁ (by rw [hB₀, hB₁]; exact fun h' => hn1 h'.symm)
  · exact hne hle₀ hle₂ (by rw [hB₀, hB₂]; exact fun h' => hn2 h'.symm)
  · exact hne hle₁ hle₂ (by rw [hB₁, hB₂]; exact hn12)

end CFSG.ClassicalInvolution.Q3.TL4.Z2W
