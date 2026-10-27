module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5CntSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSInvolutions
public import CFSG.RankThree.PartOne.KS.OrbitCert
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.RankThree.PartOne.FIS.SymBuild

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Certificates.Native CFSG.RankThree.Native CFSG.EvenSporadicStandard.HSStd
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus CFSG.Permutation.SymmetricCoxeter
  CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

noncomputable abbrev Yp : Equiv.Perm (Fin 100) := permOfArr 100 y0

noncomputable abbrev Zp : Equiv.Perm (Fin 100) := permOfArr 100 z0

noncomputable abbrev Up : Equiv.Perm (Fin 100) := permOfArr 100 u0

noncomputable abbrev Xp (i : ℕ) : Equiv.Perm (Fin 100) := permOfArr 100 xGens[i]!

noncomputable abbrev Rp (i : ℕ) : Equiv.Perm (Fin 100) := permOfArr 100 rGens[i]!

noncomputable abbrev Pe : Equiv.Perm (Fin 100) := permOfArr 100 pEl

theorem keys_lt : ∀ p ∈ keys, p < 100 := by
  intro p hp
  simp only [keys, List.mem_cons, List.not_mem_nil, or_false] at hp
  omega

theorem rep_pw {x : Array ℕ} {X : Equiv.Perm (Fin 100)} (h : Rep 100 x X) :
    ∀ k, Rep 100 (pw x k) (X ^ k)
  | 0 => by
    rw [pow_zero]
    exact rep_idA
  | k + 1 => by
    rw [pw, pow_succ']
    exact rep_compA h (rep_pw h k)

theorem forall_closure {gs : Array (Array ℕ)} {c : ArrCert} (h : enumOK 100 gs keys c = true)
    {p : Array ℕ → Bool} (hall : c.pts.toList.all p = true)
    {x : Equiv.Perm (Fin 100)} (hx : x ∈ Subgroup.closure (permsA 100 gs)) :
    ∃ a ∈ c.pts.toList, Rep 100 a x ∧ p a = true := by
  obtain ⟨hmem, -, hval⟩ := enumOK_spec keys_lt h
  obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
  have hmemL : c.pts[i]! ∈ c.pts.toList := by
    rw [getElem!_pos _ i hi]
    exact Array.mem_toList_iff.2 (Array.getElem_mem hi)
  exact ⟨_, hmemL, rep_of_validA (hval i hi), List.all_eq_true.1 hall _ hmemL⟩

theorem valid_of_mem {gs : Array (Array ℕ)} {c : ArrCert} (h : enumOK 100 gs keys c = true)
    {a : Array ℕ} (ha : a ∈ c.pts.toList) : validA 100 a = true := by
  obtain ⟨-, -, hval⟩ := enumOK_spec keys_lt h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hi' : i < c.pts.size := by simpa using hi
  rw [Array.getElem_toList, ← getElem!_pos c.pts i hi']
  exact hval i hi'

theorem mem_closure_of_any {gs : Array (Array ℕ)} {c : ArrCert} (h : enumOK 100 gs keys c = true)
    {t : Array ℕ} {x : Equiv.Perm (Fin 100)} (ht : Rep 100 t x)
    (hany : c.pts.toList.any (eqA 100 t) = true) : x ∈ Subgroup.closure (permsA 100 gs) :=
  enumOK_mem_of_any keys_lt h ht hany

theorem mem_closure_iff_any {gs : Array (Array ℕ)} {c : ArrCert} (h : enumOK 100 gs keys c = true)
    {t : Array ℕ} {x : Equiv.Perm (Fin 100)} (ht : Rep 100 t x) :
    x ∈ Subgroup.closure (permsA 100 gs) ↔ c.pts.toList.any (eqA 100 t) = true := by
  constructor
  · intro hx
    obtain ⟨a, ha, hra, -⟩ := forall_closure h (p := fun _ => true) (by simp) hx
    rw [List.any_eq_true]
    exact ⟨a, ha, (eqA_iff ht hra).2 rfl⟩
  · exact mem_closure_of_any h ht

theorem gens_mem_closure {gs : Array (Array ℕ)} {k : ℕ} (hk : k < gs.size) :
    permOfArr 100 gs[k]! ∈ Subgroup.closure (permsA 100 gs) :=
  Subgroup.subset_closure (mem_permsA hk)

theorem card_closure_of_enum {gs : Array (Array ℕ)} {c : ArrCert} {N : ℕ}
    (h : enumOK 100 gs keys c = true) (hN : c.pts.size = N) :
    Nat.card (Subgroup.closure (permsA 100 gs)) = N := by
  rw [(enumOK_spec keys_lt h).2.1, hN]

set_option linter.unusedSectionVars false

section Certified

theorem closure_pGens_aux : permsA 100 pGens = {hs100A, hs100B} := by
  ext g
  simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk2 : k < 2 := by simpa [pGens] using hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by simp [pGens], rfl⟩
    · exact ⟨1, by simp [pGens], rfl⟩

theorem closure_pGens : Subgroup.closure (permsA 100 pGens) = hs100P := by
  rw [closure_pGens_aux]
  rfl

theorem card_P : Nat.card hs100P = 44352000 := card_hs100P

theorem card_cent_of_classOK {x : Array ℕ} {c : ArrCert} {N : ℕ}
    (hgs : ∀ k < pGens.size, validA 100 pGens[k]! = true)
    (hc : classOK x c N = true) :
    Nat.card hs100P = N * Nat.card ↥(hs100P ⊓ centralizer ({permOfArr 100 x} :
      Set (Equiv.Perm (Fin 100)))) := by
  simp only [classOK, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨hc, hN⟩ := hc
  obtain ⟨-, hcard⟩ := CFSG.RankThree.PartOne.card_closure_eq_card_mul_card_centralizer
    (n := 100) (gs := pGens) (ps := keys) keys_lt hgs hc
  rw [closure_pGens, hN] at hcard
  exact hcard

theorem s0_parts (h : s0OK = true) : basicOK = true ∧ classesOK = true ∧ yOK = true ∧
    kOK = true ∧ aOK = true ∧ tableOK = true := by
  simp only [s0OK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem basic_spec (hb : basicOK = true) :
    (∀ k < pGens.size, validA 100 pGens[k]! = true) ∧
    validA 100 z0 = true ∧ Zp ∈ hs100P ∧ Zp * Zp = 1 ∧ Zp ≠ 1 ∧
    validA 100 y0 = true ∧ Yp ∈ hs100P ∧ Up ≠ 1 ∧
    (∀ k < 4, validA 100 xGens[k]! = true ∧ Xp k ∈ hs100P) ∧
    (∀ k < 5, validA 100 rGens[k]! = true ∧ Rp k ∈ hs100P) ∧
    validA 100 pEl = true ∧ Pe ∈ hs100P := by
  simp only [basicOK, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at hb
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hb
  have hrz : Rep 100 z0 Zp := rep_of_validA h2
  refine ⟨allLt_iff.1 h1, h2, (s5InP_iff h2).1 h3, (eqA_iff (rep_compA hrz hrz) rep_idA).1 h4, ?_, h6,
    (s5InP_iff h6).1 h7, ?_, ?_, ?_, h11, (s5InP_iff h11).1 h12⟩
  · intro h0
    have := (eqA_iff hrz rep_idA).2 h0
    rw [this] at h5
    exact absurd h5 (by simp)
  · intro h0
    have hu : validA 100 u0 = true := by
      have := allLt_spec h9 (by decide : 0 < xGens.size)
      simpa [u0, xGens, tab] using (Bool.and_eq_true_iff.1 this).1
    have := (eqA_iff (rep_of_validA hu) rep_idA).2 h0
    rw [this] at h8
    exact absurd h8 (by simp)
  · intro k hk
    have := allLt_spec h9 (show k < xGens.size by simpa [xGens] using hk)
    rw [Bool.and_eq_true] at this
    exact ⟨this.1, (s5InP_iff this.1).1 this.2⟩
  · intro k hk
    have := allLt_spec h10 (show k < rGens.size by simpa [rGens] using hk)
    rw [Bool.and_eq_true] at this
    exact ⟨this.1, (s5InP_iff this.1).1 this.2⟩

theorem u0_eq : u0 = xGens[0]! := rfl

theorem valid_u0 (hb : basicOK = true) : validA 100 u0 = true := by
  have := (basic_spec hb).2.2.2.2.2.2.2.2.1 0 (by norm_num)
  rw [u0_eq]
  exact this.1

noncomputable def fixN (g : Equiv.Perm (Fin 100)) : ℕ := Nat.card {i : Fin 100 // g i = i}

theorem fixCnt_eq {a : Array ℕ} {g : Equiv.Perm (Fin 100)} (hr : Rep 100 a g) :
    fixCnt a = fixN g := by
  unfold fixCnt fixN
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hr i, Fin.ext_iff]

theorem fixN_conj (c g : Equiv.Perm (Fin 100)) : fixN (c * g * c⁻¹) = fixN g := by
  unfold fixN
  refine Nat.card_congr (Equiv.subtypeEquiv c.symm fun i => ?_)
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
  constructor
  · intro h
    have := congrArg c.symm h
    simpa using this
  · intro h
    simp [h]

theorem s0_card_cent_subtype {M : Type*} [Group M] (P : Subgroup M) (x : ↥P) :
    Nat.card ↥(centralizer ({x} : Set ↥P)) =
      Nat.card ↥(P ⊓ centralizer ({(x : M)} : Set M)) := by
  have h : (centralizer ({x} : Set ↥P)).map P.subtype =
      P ⊓ centralizer ({(x : M)} : Set M) := by
    ext z
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, Subgroup.coe_subtype]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.2, ?_⟩
      have := congrArg Subtype.val ha
      simpa using this
    · rintro ⟨hz, h⟩
      refine ⟨⟨z, hz⟩, ?_, rfl⟩
      exact Subtype.ext h
  rw [← h]
  exact (Subgroup.card_map_of_injective P.subtype_injective).symm

theorem classes_spec (hb : basicOK = true) (hc : classesOK = true) :
    Nat.card ↥(hs100P ⊓ centralizer ({Zp} : Set (Equiv.Perm (Fin 100)))) = 7680 ∧
    Nat.card ↥(hs100P ⊓ centralizer ({Up} : Set (Equiv.Perm (Fin 100)))) = 2880 ∧
    Nat.card ↥(hs100P ⊓ centralizer ({Yp} : Set (Equiv.Perm (Fin 100)))) = 360 ∧
    fixN Zp = 20 ∧ fixN Up = 0 := by
  obtain ⟨hgs, hvz, -, -, -, hvy, -, -, -, -, -, -⟩ := basic_spec hb
  have hvu := valid_u0 hb
  simp only [classesOK, Bool.and_eq_true, beq_iff_eq, and_assoc] at hc
  obtain ⟨hz, hu, hy, hfz, hfu⟩ := hc
  have c1 : 44352000 = 5775 * Nat.card ↥(hs100P ⊓ centralizer ({Zp} :
      Set (Equiv.Perm (Fin 100)))) := by
    have := card_cent_of_classOK hgs hz
    rwa [card_P] at this
  have c2 : 44352000 = 15400 * Nat.card ↥(hs100P ⊓ centralizer ({Up} :
      Set (Equiv.Perm (Fin 100)))) := by
    have := card_cent_of_classOK hgs hu
    rwa [card_P] at this
  have c3 : 44352000 = 123200 * Nat.card ↥(hs100P ⊓ centralizer ({Yp} :
      Set (Equiv.Perm (Fin 100)))) := by
    have := card_cent_of_classOK hgs hy
    rwa [card_P] at this
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · rw [← fixCnt_eq (rep_of_validA hvz)]; exact hfz
  · rw [← fixCnt_eq (rep_of_validA hvu)]; exact hfu

theorem coxOK_spec {s : Array (Array ℕ)} {m : ℕ} (hv : ∀ k < m, validA 100 s[k]! = true)
    (h : coxOK s m = true) : IsCoxeterA m (fun i => permOfArr 100 s[i]!) := by
  simp only [coxOK, Bool.and_eq_true] at h
  obtain ⟨⟨hc1, hc2⟩, hc3⟩ := h
  have hrx : ∀ i < m, Rep 100 s[i]! (permOfArr 100 s[i]!) := fun i hi => rep_of_validA (hv i hi)
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i j hij hj => ?_⟩
  · exact (eqA_iff (rep_compA (hrx i hi) (hrx i hi)) rep_idA).1 (allLt_spec hc1 hi)
  · have hi3 : i < m - 1 := by omega
    exact (eqA_iff (rep_compA (rep_compA (hrx i (by omega)) (hrx (i + 1) hi)) (hrx i (by omega)))
      (rep_compA (rep_compA (hrx (i + 1) hi) (hrx i (by omega))) (hrx (i + 1) hi))).1
      (allLt_spec hc2 hi3)
  · have h1 := allLt_spec (allLt_spec hc3 (by omega : i < m)) hj
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
    rcases h1 with h1 | h1
    · omega
    · exact (eqA_iff (rep_compA (hrx i (by omega)) (hrx j hj))
        (rep_compA (hrx j hj) (hrx i (by omega)))).1 h1

theorem mem_normalizer_of_conj_le {H : Subgroup (Equiv.Perm (Fin 100))} {g : Equiv.Perm (Fin 100)}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set (Equiv.Perm (Fin 100))) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let f : H → H := fun a => ⟨g * a * g⁻¹, h a a.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.1 hf) ⟨g * x * g⁻¹, hx⟩
  have := congrArg Subtype.val ha
  simp only [f, mul_left_inj, mul_right_inj] at this
  rw [← this]
  exact a.2

theorem mem_normalizer_closure {gs : Array (Array ℕ)} {g : Equiv.Perm (Fin 100)}
    (h : ∀ k < gs.size, g * permOfArr 100 gs[k]! * g⁻¹ ∈ Subgroup.closure (permsA 100 gs)) :
    g ∈ normalizer (Subgroup.closure (permsA 100 gs) : Set (Equiv.Perm (Fin 100))) := by
  apply mem_normalizer_of_conj_le
  have : Subgroup.closure (permsA 100 gs) ≤
      (Subgroup.closure (permsA 100 gs)).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  intro x hx
  exact this hx

theorem cent_fix
    (hZc : Nat.card ↥(hs100P ⊓ centralizer ({Zp} : Set (Equiv.Perm (Fin 100)))) = 7680)
    (hUc : Nat.card ↥(hs100P ⊓ centralizer ({Up} : Set (Equiv.Perm (Fin 100)))) = 2880)
    (hZP : Zp ∈ hs100P) (hUP : Up ∈ hs100P) (hZ2 : orderOf Zp = 2) (hU2 : orderOf Up = 2)
    (hfz : fixN Zp = 20) (hfu : fixN Up = 0)
    {w : Equiv.Perm (Fin 100)} (hw : w ∈ hs100P) (hw2 : orderOf w = 2) :
    (fixN w = 20 → Nat.card ↥(hs100P ⊓ centralizer ({w} : Set (Equiv.Perm (Fin 100)))) = 7680) ∧
    (fixN w = 0 → Nat.card ↥(hs100P ⊓ centralizer ({w} : Set (Equiv.Perm (Fin 100)))) = 2880) := by
  have hY : IsSporadic ↥hs100P .HS := ⟨hs100Equiv.symm⟩
  set W' : ↥hs100P := ⟨w, hw⟩
  set Z' : ↥hs100P := ⟨Zp, hZP⟩
  set U' : ↥hs100P := ⟨Up, hUP⟩
  have hW2 : orderOf W' = 2 := by rw [← Subgroup.orderOf_coe]; exact hw2
  have hZ2' : orderOf Z' = 2 := by rw [← Subgroup.orderOf_coe]; exact hZ2
  have hU2' : orderOf U' = 2 := by rw [← Subgroup.orderOf_coe]; exact hU2
  have cW := s0_card_cent_subtype hs100P W'
  have cZ := s0_card_cent_subtype hs100P Z'
  have cU := s0_card_cent_subtype hs100P U'
  have key : ∀ V' : ↥hs100P, orderOf V' = 2 →
      Nat.card ↥(centralizer ({W'} : Set ↥hs100P)) = Nat.card ↥(centralizer ({V'} : Set ↥hs100P)) →
      fixN w = fixN (V' : Equiv.Perm (Fin 100)) := by
    intro V' hV2 hc
    obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_of_card_centralizer_eq_hs hY W' V' hW2 hV2 hc)
    have := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [← this, fixN_conj]
  have hdisj := card_centralizer_of_involution_hs hY W' hW2
  rw [cW] at hdisj
  constructor
  · intro hf
    rcases hdisj with h | h
    · exact h
    · exfalso
      have := key U' hU2' (by rw [cW, cU, h, hUc])
      rw [hf, hfu] at this
      omega
  · intro hf
    rcases hdisj with h | h
    · exfalso
      have := key Z' hZ2' (by rw [cW, cZ, h, hZc])
      rw [hf, hfz] at this
      omega
    · exact h

noncomputable abbrev E0 : Subgroup (Equiv.Perm (Fin 100)) :=
  Subgroup.closure (permsA 100 zasE0Gens)

theorem y_spec (hy : yOK = true) (hvy : validA 100 y0 = true) (hvz : validA 100 z0 = true) :
    Yp ^ 3 = 1 ∧ Yp ≠ 1 ∧ Yp * Zp = Zp * Yp ∧ Yp ∈ normalizer (E0 : Set (Equiv.Perm (Fin 100))) ∧
      Zp ∈ E0 ∧ Nat.card ↥(E0 ⊓ centralizer ({Yp} : Set (Equiv.Perm (Fin 100)))) = 4 := by
  classical
  simp only [yOK, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at hy
  obtain ⟨h3, hne, hcomm, henum, hsz, hnorm, hz, hcount⟩ := hy
  replace hcount : eCommCount = 4 := beq_iff_eq.1 hcount
  have hry : Rep 100 y0 Yp := rep_of_validA hvy
  have hrz : Rep 100 z0 Zp := rep_of_validA hvz
  have hpsE : ∀ p ∈ zasEKeys, p < 100 := fun p hp => List.mem_range.1 hp
  have hY3 : Yp ^ 3 = 1 := (eqA_iff (rep_pw hry 3) rep_idA).1 h3
  have hY1 : Yp ≠ 1 := fun h1 => by
    have := (eqA_iff hry rep_idA).2 h1
    rw [this] at hne
    exact absurd hne (by simp)
  refine ⟨hY3, hY1, (commA_iff hry hrz).1 hcomm, ?_, enumOK_mem_of_any hpsE henum hrz hz, ?_⟩
  · apply mem_normalizer_closure
    intro k hk
    have hv := enumOK_gens_valid henum hk
    have := allLt_spec hnorm hk
    exact enumOK_mem_of_any hpsE henum (rep_conjA hvy (rep_of_validA hv)) this
  · obtain ⟨hmem, hcardE, hval⟩ := enumOK_spec hpsE henum
    have hcs := card_subtype_enum E0 (fun i => permOfArr 100 zasE0Cert.pts[i]!) (fun x => by
      rw [hmem x]) hcardE (fun y => y ∈ centralizer ({Yp} : Set (Equiv.Perm (Fin 100))))
    have h1 : Nat.card ↥(E0 ⊓ centralizer ({Yp} : Set (Equiv.Perm (Fin 100)))) =
        Nat.card {y : E0 // y.1 ∈ centralizer ({Yp} : Set (Equiv.Perm (Fin 100)))} :=
      Nat.card_congr
        { toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
          invFun := fun y => ⟨y.1.1, y.1.2, y.2⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
    rw [h1, hcs, Nat.card_eq_fintype_card, Fintype.card_subtype, ← hcount, eCommCount]
    congr 1
    refine Finset.filter_congr fun i _ => ?_
    have hrk := rep_of_validA (hval i.1 i.2)
    rw [mem_centralizer_singleton_iff, commA_iff hry hrk]
    exact eq_comm

theorem disjoint_zpowers_of_prime {M : Type*} [Group M] {g : M} {p : ℕ} [Fact p.Prime]
    (hg : orderOf g = p) {K : Subgroup M} (hgK : g ∉ K) : Disjoint (zpowers g) K := by
  rw [Subgroup.disjoint_def]
  intro x hx hxK
  by_contra hx1
  have hfin : Finite ↥(zpowers g) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hg]; exact (Fact.out : p.Prime).ne_zero)
  have hle : zpowers g ⊓ K ≤ zpowers g := inf_le_left
  have hcard : Nat.card ↥(zpowers g ⊓ K) ∣ p := by
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, hg] at this
  rcases (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : p.Prime) _ hcard) with h1 | h1
  · have : zpowers g ⊓ K = ⊥ := Subgroup.card_eq_one.1 h1
    have hmem : x ∈ zpowers g ⊓ K := ⟨hx, hxK⟩
    rw [this] at hmem
    exact hx1 (Subgroup.mem_bot.1 hmem)
  · have heq : zpowers g ⊓ K = zpowers g :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [h1, Nat.card_zpowers, hg])
    apply hgK
    have : g ∈ zpowers g ⊓ K := by rw [heq]; exact mem_zpowers g
    exact this.2

theorem cyGens_zero : cyGens[0]! = y0 := rfl

theorem cyGens_succ {k : ℕ} (hk : k < 4) : cyGens[k + 1]! = xGens[k]! := by
  interval_cases k <;> simp [cyGens, xGens]

theorem cuGens_zero : cuGens[0]! = u0 := rfl

theorem cuGens_succ {k : ℕ} (hk : k < 6) : cuGens[k + 1]! = aGens[k]! := by
  interval_cases k <;> simp [cuGens, aGens]

theorem forall_cy {H : Subgroup (Equiv.Perm (Fin 100))} (h0 : permOfArr 100 y0 ∈ H)
    (hs : ∀ k < xGens.size, permOfArr 100 xGens[k]! ∈ H) :
    ∀ k < cyGens.size, permOfArr 100 cyGens[k]! ∈ H := by
  intro k hk
  have hk5 : k < 5 := by simpa [cyGens] using hk
  rcases k with _ | k
  · rw [cyGens_zero]; exact h0
  · rw [cyGens_succ (by omega)]
    exact hs k (by simp [xGens]; omega)

theorem forall_cu {H : Subgroup (Equiv.Perm (Fin 100))} (h0 : permOfArr 100 u0 ∈ H)
    (hs : ∀ k < aGens.size, permOfArr 100 aGens[k]! ∈ H) :
    ∀ k < cuGens.size, permOfArr 100 cuGens[k]! ∈ H := by
  intro k hk
  have hk7 : k < 7 := by simpa [cuGens] using hk
  rcases k with _ | k
  · rw [cuGens_zero]; exact h0
  · rw [cuGens_succ (by omega)]
    exact hs k (by simp [aGens]; omega)

noncomputable abbrev K0 : Subgroup (Equiv.Perm (Fin 100)) :=
  Subgroup.closure (permsA 100 xGens)

noncomputable abbrev Cy : Subgroup (Equiv.Perm (Fin 100)) :=
  Subgroup.closure (permsA 100 cyGens)

theorem Xp_mem_K0 {i : ℕ} (hi : i < 4) : Xp i ∈ K0 := gens_mem_closure (by simpa [xGens] using hi)

theorem k_spec (hb : basicOK = true) (hk : kOK = true) (hcl : classesOK = true)
    (hYo : orderOf Yp = 3) :
    Nat.card K0 = 120 ∧ K0 ≤ hs100P ⊓ centralizer ({Yp} : Set (Equiv.Perm (Fin 100))) ∧
    hs100P ⊓ centralizer ({Yp} : Set (Equiv.Perm (Fin 100))) = zpowers Yp ⊔ K0 ∧
    Disjoint (zpowers Yp) K0 ∧ Up ∈ K0 ∧
    (∃ e : ↥K0 ≃* Equiv.Perm (Fin 5), ∀ h : Up ∈ K0, (e ⟨Up, h⟩).IsSwap) ∧
    enumOK 100 cyGens keys cyCert = true ∧
    hs100P ⊓ centralizer ({Yp} : Set (Equiv.Perm (Fin 100))) = Cy := by
  obtain ⟨hgs, hvz, -, -, -, hvy, hYP, hU1, hX, -, -, -⟩ := basic_spec hb
  obtain ⟨-, -, hc3, -, -⟩ := classes_spec hb hcl
  have hvy' := hvy
  simp only [kOK, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at hk
  obtain ⟨hcox, hne, henum, hsz, hcomm, hcyenum, hcysz, hYK⟩ := hk
  replace hsz : kCert.pts.size = 120 := beq_iff_eq.1 hsz
  replace hcysz : cyCert.pts.size = 360 := beq_iff_eq.1 hcysz
  have hxv : ∀ k < 4, validA 100 xGens[k]! = true := fun k hk => (hX k hk).1
  have hK0card : Nat.card K0 = 120 := card_closure_of_enum henum hsz
  have hCox := coxOK_spec (s := xGens) (m := 4) hxv hcox
  obtain ⟨ψ, hψ⟩ := exists_hom_perm 4 (fun i => permOfArr 100 xGens[i]!) hCox
  have hinj : Function.Injective ψ := by
    refine CFSG.RankThree.PartOne.FIS.injective_of_ne_one (m := 2) le_rfl ψ ?_
    have e0 := hψ 0 (by norm_num)
    have e1 := hψ 1 (by norm_num)
    show ψ (adjSwap 4 0) * ψ (adjSwap 4 1) ≠ 1
    rw [e0, e1]
    intro h1
    have hr0 : Rep 100 xGens[0]! (Xp 0) := rep_of_validA (hxv 0 (by norm_num))
    have hr1 : Rep 100 xGens[1]! (Xp 1) := rep_of_validA (hxv 1 (by norm_num))
    have := (eqA_iff (rep_compA hr0 hr1) rep_idA).2 h1
    rw [this] at hne
    exact absurd hne (by simp)
  have hrange_le : ψ.range ≤ K0 := by
    rintro _ ⟨σ, rfl⟩
    have : (⊤ : Subgroup (Equiv.Perm (Fin 5))) ≤ K0.comap ψ := by
      rw [← closure_adjSwap 4, Subgroup.closure_le]
      rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, hψ i hi]
      exact Xp_mem_K0 hi
    exact this (mem_top σ)
  have hrange_card : Nat.card ψ.range = 120 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
  have hrange : ψ.range = K0 :=
    Subgroup.eq_of_le_of_card_ge hrange_le (by rw [hK0card, hrange_card])
  have hKP : K0 ≤ hs100P ⊓ centralizer ({Yp} : Set (Equiv.Perm (Fin 100))) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk4 : k < 4 := by simpa [xGens] using hk
    exact Subgroup.mem_inf.2 ⟨(hX k hk4).2, mem_centralizer_singleton_iff.2
      ((commA_iff (rep_of_validA hvy) (rep_of_validA (hxv k hk4))).1
        (allLt_spec hcomm hk)).symm⟩
  have hCyle : Cy ≤ hs100P ⊓ centralizer ({Yp} : Set (Equiv.Perm (Fin 100))) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact forall_cy (Subgroup.mem_inf.2 ⟨hYP, mem_centralizer_singleton_iff.2 rfl⟩)
      (fun k hk => hKP (gens_mem_closure (by simpa [xGens] using hk))) k hk
  have hCyeq : Cy = hs100P ⊓ centralizer ({Yp} : Set (Equiv.Perm (Fin 100))) :=
    Subgroup.eq_of_le_of_card_ge hCyle (by
      rw [card_closure_of_enum hcyenum hcysz, hc3])
  have hCysup : Cy = zpowers Yp ⊔ K0 := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      exact forall_cy (Subgroup.mem_sup_left (mem_zpowers _))
        (fun k hk => Subgroup.mem_sup_right (gens_mem_closure (by simpa [xGens] using hk))) k hk
    · refine sup_le (Subgroup.zpowers_le.2 ?_) ?_
      · have := gens_mem_closure (gs := cyGens) (k := 0) (by simp [cyGens])
        rwa [cyGens_zero] at this
      · rw [Subgroup.closure_le]
        rintro _ ⟨k, hk, rfl⟩
        have hk4 : k < 4 := by simpa [xGens] using hk
        have := gens_mem_closure (gs := cyGens) (k := k + 1) (by simp [cyGens]; omega)
        rwa [cyGens_succ hk4] at this
  refine ⟨hK0card, hKP, hCyeq ▸ hCysup, ?_, Xp_mem_K0 (i := 0) (by norm_num), ?_, hcyenum,
    hCyeq.symm⟩
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine disjoint_zpowers_of_prime hYo fun hYin => ?_
    have := (mem_closure_iff_any henum (rep_of_validA hvy)).1 hYin
    rw [this] at hYK
    exact absurd hYK (by simp)
  · let e0 : Equiv.Perm (Fin 5) ≃* ↥K0 :=
      (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
    refine ⟨e0.symm, fun h => ?_⟩
    have : e0.symm ⟨Up, h⟩ = adjSwap 4 0 := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      show Up = ψ (adjSwap 4 0)
      rw [hψ 0 (by norm_num)]
      rfl
    rw [this, adjSwap_of_lt (by norm_num)]
    exact ⟨_, _, by simp, rfl⟩

theorem u_order (hb : basicOK = true) (hk : kOK = true) : orderOf Up = 2 := by
  obtain ⟨-, -, -, -, -, -, -, hU1, hX, -, -, -⟩ := basic_spec hb
  simp only [kOK, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at hk
  obtain ⟨hcox, -⟩ := hk
  have hCox := coxOK_spec (s := xGens) (m := 4) (fun k hk => (hX k hk).1) hcox
  have hsq : Up * Up = 1 := hCox.sq 0 (by norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact hsq) hU1

noncomputable abbrev Ab : Subgroup (Equiv.Perm (Fin 100)) := Subgroup.closure (permsA 100 aGens)

noncomputable abbrev Jm : Subgroup (Equiv.Perm (Fin 100)) := Subgroup.closure (permsA 100 jGens)

noncomputable abbrev Cu : Subgroup (Equiv.Perm (Fin 100)) := Subgroup.closure (permsA 100 cuGens)

theorem aGens_get_r {k : ℕ} (hk : k < 5) : aGens[k]! = rGens[k]! := by
  interval_cases k <;> simp [aGens, rGens]

theorem jGens_get {k : ℕ} (hk : k < 4) : jGens[k]! = compA 100 rGens[k]! rGens[k + 1]! := by
  interval_cases k <;> simp [jGens, rGens]

theorem rep_jGen {k : ℕ} (hk : k < 4) (hrv : ∀ k < 5, validA 100 rGens[k]! = true) :
    permOfArr 100 jGens[k]! = Rp k * Rp (k + 1) := by
  rw [jGens_get hk]
  exact permOfArr_eq_of_rep (rep_compA (rep_of_validA (hrv k (by omega)))
    (rep_of_validA (hrv (k + 1) (by omega))))

theorem Rp_eq_aGens {k : ℕ} (hk : k < 5) : permOfArr 100 aGens[k]! = Rp k := by
  rw [aGens_get_r hk]

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem mul_eq_commutator_of_braid {M : Type*} [Group M] {g h : M} (hg : g * g = 1)
    (hh : h * h = 1) (hb : g * h * g = h * g * h) : g * h = ⁅h, g⁆ := by
  have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have hh' : h⁻¹ = h := inv_eq_of_mul_eq_one_right hh
  rw [commutatorElement_def, hg', hh']
  calc g * h = (g * h * g) * g := by rw [mul_assoc (g * h) g g, hg, mul_one]
    _ = (h * g * h) * g := by rw [hb]
    _ = h * g * h * g := rfl

theorem a_spec (hb : basicOK = true) (hcl : classesOK = true)
    (hk : kOK = true) (ha : aOK = true)
    (hcyenum : enumOK 100 cyGens keys cyCert = true)
    (hCy : hs100P ⊓ centralizer ({Yp} : Set (Equiv.Perm (Fin 100))) = Cy) :
    Nat.card Ab = 1440 ∧ Ab ≤ hs100P ⊓ centralizer ({Up} : Set (Equiv.Perm (Fin 100))) ∧
    hs100P ⊓ centralizer ({Up} : Set (Equiv.Perm (Fin 100))) = zpowers Up ⊔ Ab ∧
    Disjoint (zpowers Up) Ab ∧ Jm ≤ Ab ∧ Yp ∈ Jm ∧ Nat.card Jm = 360 ∧
    (∀ a ∈ Ab, ∀ j ∈ Jm, a * j * a⁻¹ ∈ Jm) ∧
    hs100P ⊓ centralizer (Jm : Set (Equiv.Perm (Fin 100))) = zpowers Up ∧
    Jm ≤ derivedIn Ab ∧ Nonempty (alternatingGroup (Fin 6) ≃* ↥Jm) := by
  obtain ⟨hgs, hvz, hZP, -, -, hvy, hYP, hU1, hX, hR, hvp, hPP⟩ := basic_spec hb
  have hvu := valid_u0 hb
  obtain ⟨-, hc2, -, -, -⟩ := classes_spec hb hcl
  have hU2 := u_order hb hk
  have hUP : Up ∈ hs100P := (hX 0 (by norm_num)).2
  have hru : Rep 100 u0 Up := rep_of_validA hvu
  have hry : Rep 100 y0 Yp := rep_of_validA hvy
  simp only [aOK, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at ha
  obtain ⟨hcox, hne, hcomm, haenum, hasz, hUnA, hcuenum, hcusz, hjenum, hjsz, hYJ, hnormJ,
    hcyall⟩ := ha
  replace hasz : aCert.pts.size = 1440 := beq_iff_eq.1 hasz
  replace hcusz : cuCert.pts.size = 2880 := beq_iff_eq.1 hcusz
  replace hjsz : jCert.pts.size = 360 := beq_iff_eq.1 hjsz
  have hrv : ∀ k < 5, validA 100 rGens[k]! = true := fun k hk => (hR k hk).1
  have haP : ∀ k < aGens.size, permOfArr 100 aGens[k]! ∈ hs100P := by
    intro k hk
    have hk6 : k < 6 := by simpa [aGens] using hk
    by_cases hk5 : k < 5
    · rw [aGens_get_r hk5]; exact (hR k hk5).2
    · have : k = 5 := by omega
      subst this
      exact hPP
  have haC : ∀ k < aGens.size, permOfArr 100 aGens[k]! * Up = Up * permOfArr 100 aGens[k]! := by
    intro k hk
    have hv := enumOK_gens_valid haenum hk
    exact ((commA_iff hru (rep_of_validA hv)).1 (allLt_spec hcomm hk)).symm
  have hAcard : Nat.card Ab = 1440 := card_closure_of_enum haenum hasz
  have hAle : Ab ≤ hs100P ⊓ centralizer ({Up} : Set (Equiv.Perm (Fin 100))) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact Subgroup.mem_inf.2 ⟨haP k hk, mem_centralizer_singleton_iff.2 (haC k hk)⟩
  have hUA : Up ∉ Ab := fun hmem => by
    have := (mem_closure_iff_any haenum hru).1 hmem
    rw [this] at hUnA
    exact absurd hUnA (by simp)
  have hCule : Cu ≤ hs100P ⊓ centralizer ({Up} : Set (Equiv.Perm (Fin 100))) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact forall_cu (Subgroup.mem_inf.2 ⟨hUP, mem_centralizer_singleton_iff.2 rfl⟩)
      (fun k hk => hAle (gens_mem_closure hk)) k hk
  have hCueq : Cu = hs100P ⊓ centralizer ({Up} : Set (Equiv.Perm (Fin 100))) :=
    Subgroup.eq_of_le_of_card_ge hCule (by rw [card_closure_of_enum hcuenum hcusz, hc2])
  have hCusup : hs100P ⊓ centralizer ({Up} : Set (Equiv.Perm (Fin 100))) = zpowers Up ⊔ Ab := by
    rw [← hCueq]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      exact forall_cu (Subgroup.mem_sup_left (mem_zpowers _))
        (fun k hk => Subgroup.mem_sup_right (gens_mem_closure hk)) k hk
    · refine sup_le (Subgroup.zpowers_le.2 ?_) ?_
      · have := gens_mem_closure (gs := cuGens) (k := 0) (by simp [cuGens])
        rwa [cuGens_zero] at this
      · rw [Subgroup.closure_le]
        rintro _ ⟨k, hk, rfl⟩
        have hk6 : k < 6 := by simpa [aGens] using hk
        have := gens_mem_closure (gs := cuGens) (k := k + 1) (by simp [cuGens]; omega)
        rwa [cuGens_succ hk6] at this
  have hdisj : Disjoint (zpowers Up) Ab := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact disjoint_zpowers_of_prime hU2 hUA
  have hJA : Jm ≤ Ab := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk4 : k < 4 := by simpa [jGens] using hk
    show permOfArr 100 jGens[k]! ∈ Ab
    rw [rep_jGen hk4 hrv, ← Rp_eq_aGens (k := k) (by omega),
      ← Rp_eq_aGens (k := k + 1) (by omega)]
    exact Ab.mul_mem (gens_mem_closure (by simp [aGens]; omega))
      (gens_mem_closure (by simp [aGens]; omega))
  have hYJm : Yp ∈ Jm := mem_closure_of_any hjenum hry hYJ
  have hJcard : Nat.card Jm = 360 := card_closure_of_enum hjenum hjsz
  have hnormal : ∀ a ∈ Ab, ∀ j ∈ Jm, a * j * a⁻¹ ∈ Jm := by
    have hle : Ab ≤ normalizer (Jm : Set (Equiv.Perm (Fin 100))) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨g, hg, rfl⟩
      apply mem_normalizer_closure
      intro k hk
      have hvg := enumOK_gens_valid haenum hg
      exact mem_closure_of_any hjenum (rep_conjA hvg (rep_of_validA (enumOK_gens_valid hjenum hk)))
        (allLt_spec (allLt_spec hnormJ hg) hk)
    intro a ha j hj
    exact (mem_normalizer_iff.1 (hle ha) j).1 hj
  have hrJ : ∀ k < jGens.size, Rep 100 jGens[k]! (permOfArr 100 jGens[k]!) :=
    fun k hk => rep_of_validA (enumOK_gens_valid hjenum hk)
  have hCJ : hs100P ⊓ centralizer (Jm : Set (Equiv.Perm (Fin 100))) = zpowers Up := by
    apply le_antisymm
    · rintro g ⟨hgP, hgC⟩
      have hgY : g ∈ hs100P ⊓ centralizer ({Yp} : Set (Equiv.Perm (Fin 100))) :=
        Subgroup.mem_inf.2 ⟨hgP, mem_centralizer_singleton_iff.2
          (mem_centralizer_iff.1 hgC Yp hYJm).symm⟩
      rw [hCy] at hgY
      obtain ⟨a, -, hra, hp⟩ := forall_closure hcyenum
        (p := fun c => (!allLt jGens.size (fun k => commA 100 c jGens[k]!)) ||
          eqA 100 c (idA 100) || eqA 100 c u0) hcyall hgY
      have hall : allLt jGens.size (fun k => commA 100 a jGens[k]!) = true := by
        refine allLt_iff.2 fun k hk => (commA_iff hra (hrJ k hk)).2 ?_
        exact (mem_centralizer_iff.1 hgC _ (gens_mem_closure hk)).symm
      simp only [Bool.or_eq_true, Bool.not_eq_true', hall] at hp
      rcases hp with (hp | hp) | hp
      · exact absurd hp (by simp)
      · rw [(eqA_iff hra rep_idA).1 hp]; exact one_mem _
      · rw [(eqA_iff hra hru).1 hp]; exact mem_zpowers _
    · refine Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨hUP, mem_centralizer_iff.2 fun j hj => ?_⟩)
      exact mem_centralizer_singleton_iff.1 (hAle (hJA hj)).2
  have hCox := coxOK_spec (s := rGens) (m := 5) hrv hcox
  have hder : Jm ≤ derivedIn Ab := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    show permOfArr 100 jGens[k]! ∈ derivedIn Ab
    have hk4 : k < 4 := by simpa [jGens] using hk
    rw [rep_jGen hk4 hrv, mul_eq_commutator_of_braid (hCox.sq k (by omega))
      (hCox.sq (k + 1) (by omega)) (hCox.braid k (by omega))]
    have hA0 : Rp k ∈ Ab := by
      have := gens_mem_closure (gs := aGens) (k := k) (by simp [aGens]; omega)
      rwa [Rp_eq_aGens (by omega)] at this
    have hA1 : Rp (k + 1) ∈ Ab := by
      have := gens_mem_closure (gs := aGens) (k := k + 1) (by simp [aGens]; omega)
      rwa [Rp_eq_aGens (by omega)] at this
    have hmem : ⁅(⟨Rp (k + 1), hA1⟩ : ↥Ab), (⟨Rp k, hA0⟩ : ↥Ab)⁆ ∈ commutator ↥Ab := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    exact Subgroup.mem_map.2 ⟨_, hmem, by simp [commutatorElement_def]⟩
  obtain ⟨ψ, hψ⟩ := exists_hom_perm 5 (fun i => permOfArr 100 rGens[i]!) hCox
  have hinj : Function.Injective ψ := by
    refine CFSG.RankThree.PartOne.FIS.injective_of_ne_one (m := 3) (by norm_num) ψ ?_
    show ψ (adjSwap 5 0) * ψ (adjSwap 5 1) ≠ 1
    rw [hψ 0 (by norm_num), hψ 1 (by norm_num)]
    intro h1
    have hr0 : Rep 100 rGens[0]! (Rp 0) := rep_of_validA (hrv 0 (by norm_num))
    have hr1 : Rep 100 rGens[1]! (Rp 1) := rep_of_validA (hrv 1 (by norm_num))
    have := (eqA_iff (rep_compA hr0 hr1) rep_idA).2 h1
    rw [this] at hne
    exact absurd hne (by simp)
  have hJle : Jm ≤ (alternatingGroup (Fin 6)).map ψ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    show permOfArr 100 jGens[k]! ∈ (alternatingGroup (Fin 6)).map ψ
    have hk4 : k < 4 := by simpa [jGens] using hk
    rw [rep_jGen hk4 hrv]
    refine ⟨adjSwap 5 k * adjSwap 5 (k + 1), ?_, ?_⟩
    · refine Equiv.Perm.mem_alternatingGroup.2 ?_
      rw [adjSwap_of_lt (by omega : k < 5),
        adjSwap_of_lt (by omega : k + 1 < 5), Equiv.Perm.sign_mul,
        Equiv.Perm.sign_swap (by simp [Fin.ext_iff]), Equiv.Perm.sign_swap (by simp [Fin.ext_iff])]
      norm_num
    · rw [map_mul, hψ k (by omega), hψ (k + 1) (by omega)]
  have hJcard' : Nat.card ((alternatingGroup (Fin 6)).map ψ) = 360 := by
    rw [Subgroup.card_map_of_injective hinj]
    exact card_alt_six
  have hJeq : Jm = (alternatingGroup (Fin 6)).map ψ :=
    Subgroup.eq_of_le_of_card_ge hJle (by rw [hJcard, hJcard'])
  exact ⟨hAcard, hAle, hCusup, hdisj, hJA, hYJm, hJcard, hnormal, hCJ, hder,
    ⟨(Subgroup.equivMapOfInjective _ ψ hinj).trans (MulEquiv.subgroupCongr hJeq.symm)⟩⟩

section Recognition

variable {G : Type*} [Group G]

noncomputable def actAut {Ab J : Subgroup G} (hn : ∀ a ∈ Ab, ∀ j ∈ J, a * j * a⁻¹ ∈ J)
    (e : alternatingGroup (Fin 6) ≃* ↥J) (a : ↥Ab) : MulAut (alternatingGroup (Fin 6)) where
  toFun x := e.symm ⟨(a : G) * (e x : G) * (a : G)⁻¹, hn a a.2 _ (e x).2⟩
  invFun x := e.symm ⟨(a : G)⁻¹ * (e x : G) * (a : G), by
    simpa using hn (a : G)⁻¹ (Ab.inv_mem a.2) _ (e x).2⟩
  left_inv x := by
    apply e.injective
    simp only [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply e.injective
    simp only [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' x y := by
    apply e.injective
    simp only [MulEquiv.apply_symm_apply, map_mul]
    apply Subtype.ext
    simp [mul_assoc]

theorem coe_actAut {Ab J : Subgroup G} (hn : ∀ a ∈ Ab, ∀ j ∈ J, a * j * a⁻¹ ∈ J)
    (e : alternatingGroup (Fin 6) ≃* ↥J) (a : ↥Ab) (x : alternatingGroup (Fin 6)) :
    ((e (actAut hn e a x) : ↥J) : G) = (a : G) * (e x : G) * (a : G)⁻¹ := by
  show ((e (e.symm _) : ↥J) : G) = _
  rw [MulEquiv.apply_symm_apply]

theorem exists_eAbar {Ab J : Subgroup G} (hn : ∀ a ∈ Ab, ∀ j ∈ J, a * j * a⁻¹ ∈ J)
    (e : alternatingGroup (Fin 6) ≃* ↥J) (hcard : Nat.card Ab = 1440)
    (hC : ∀ a ∈ Ab, (∀ j ∈ J, a * j = j * a) → a = 1) :
    ∃ f : ↥Ab ≃* MulAut (alternatingGroup (Fin 6)),
      ∀ (a : ↥Ab) (x : alternatingGroup (Fin 6)),
        ((e (f a x) : ↥J) : G) = (a : G) * (e x : G) * (a : G)⁻¹ := by
  let θ : ↥Ab →* MulAut (alternatingGroup (Fin 6)) :=
    { toFun := actAut hn e
      map_one' := by
        refine MulEquiv.ext fun x => ?_
        apply e.injective
        apply Subtype.ext
        rw [coe_actAut]
        simp
      map_mul' := fun a b => by
        refine MulEquiv.ext fun x => ?_
        apply e.injective
        apply Subtype.ext
        rw [coe_actAut]
        show _ = ((e (actAut hn e a (actAut hn e b x)) : ↥J) : G)
        rw [coe_actAut, coe_actAut]
        simp [mul_assoc] }
  have hθ : ∀ a x, ((e (θ a x) : ↥J) : G) = (a : G) * (e x : G) * (a : G)⁻¹ :=
    fun a x => coe_actAut hn e a x
  have hinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    refine hC a a.2 fun j hj => ?_
    have := hθ a (e.symm ⟨j, hj⟩)
    rw [ha, MulAut.one_apply, MulEquiv.apply_symm_apply] at this
    have h2 : (a : G) * j * (a : G)⁻¹ = j := this.symm
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have hbij : Function.Bijective θ := by
    refine (Nat.bijective_iff_injective_and_card θ).2 ⟨hinj, ?_⟩
    rw [hcard, CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6]
  exact ⟨MulEquiv.ofBijective θ hbij, hθ⟩

variable {Ab J : Subgroup G} (hn : ∀ a ∈ Ab, ∀ j ∈ J, a * j * a⁻¹ ∈ J)
  (e : alternatingGroup (Fin 6) ≃* ↥J)
  (hC : ∀ a ∈ Ab, (∀ j ∈ J, a * j = j * a) → a = 1) (hJA : J ≤ Ab)
  (f : ↥Ab ≃* MulAut (alternatingGroup (Fin 6)))
  (hf : ∀ (a : ↥Ab) (x : alternatingGroup (Fin 6)),
    ((e (f a x) : ↥J) : G) = (a : G) * (e x : G) * (a : G)⁻¹)

include hC hJA hf in
theorem eAbar_inner_iff (a : ↥Ab) :
    f a ∈ (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range ↔
      (a : G) ∈ J := by
  constructor
  · rintro ⟨b, hb⟩
    have h1 : ∀ x, (a : G) * (e x : G) * (a : G)⁻¹ =
        (e b : G) * (e x : G) * (e b : G)⁻¹ := by
      intro x
      rw [← hf a x, ← hb]
      show ((e (b * x * b⁻¹) : ↥J) : G) = _
      simp
    have h2 : ((e b : ↥J) : G)⁻¹ * (a : G) = 1 := by
      refine hC _ (Ab.mul_mem (Ab.inv_mem (hJA (e b).2)) a.2) fun j hj => ?_
      have := h1 (e.symm ⟨j, hj⟩)
      rw [MulEquiv.apply_symm_apply] at this
      simp only at this
      rw [mul_inv_eq_iff_eq_mul] at this
      calc ((e b : ↥J) : G)⁻¹ * (a : G) * j = ((e b : ↥J) : G)⁻¹ * ((a : G) * j) := by
            rw [mul_assoc]
        _ = j * (((e b : ↥J) : G)⁻¹ * (a : G)) := by rw [this]; group
    have h3 : ((e b : ↥J) : G) = (a : G) := inv_mul_eq_one.1 h2
    rw [← h3]
    exact (e b).2
  · intro ha
    refine ⟨e.symm ⟨a, ha⟩, ?_⟩
    refine MulEquiv.ext fun x => ?_
    apply e.injective
    apply Subtype.ext
    rw [hf]
    rw [MulAut.conj_apply]
    simp

include hf in
theorem eAbar_fix_iff (a : ↥Ab) :
    (∃ b : alternatingGroup (Fin 6), orderOf b = 3 ∧ f a b = b) ↔
      ∃ j ∈ J, orderOf j = 3 ∧ (a : G) * j = j * (a : G) := by
  constructor
  · rintro ⟨b, hb3, hfb⟩
    refine ⟨(e b : ↥J), (e b).2, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hb3]
    · have := hf a b
      rw [hfb, eq_mul_inv_iff_mul_eq] at this
      exact this.symm
  · rintro ⟨j, hj, hj3, hcomm⟩
    refine ⟨e.symm ⟨j, hj⟩, ?_, ?_⟩
    · rw [MulEquiv.orderOf_eq]
      rw [← hj3, ← Subgroup.orderOf_coe]
    · apply e.injective
      apply Subtype.ext
      rw [hf, MulEquiv.apply_symm_apply, mul_inv_eq_iff_eq_mul]
      exact hcomm

end Recognition

theorem a_enums (ha : aOK = true) :
    enumOK 100 aGens keys aCert = true ∧ enumOK 100 jGens keys jCert = true := by
  simp only [aOK, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at ha
  obtain ⟨-, -, -, haenum, -, -, -, -, hjenum, -⟩ := ha
  exact ⟨haenum, hjenum⟩

theorem table_spec
    (hb : basicOK = true) (hcl : classesOK = true)
    (hk : kOK = true) (ha : aOK = true) (ht : tableOK = true)
    (hAle : Ab ≤ hs100P ⊓ centralizer ({Up} : Set (Equiv.Perm (Fin 100))))
    (hdisj : Disjoint (zpowers Up) Ab) :
    ∀ x ∈ Ab, x * x = 1 → x ≠ 1 →
      (x ∈ Jm →
        Nat.card ↥(hs100P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 100)))) = 7680 ∧
        Nat.card ↥(hs100P ⊓ centralizer ({Up * x} : Set (Equiv.Perm (Fin 100)))) = 2880) ∧
      (x ∉ Jm → (∃ j ∈ Jm, orderOf j = 3 ∧ x * j = j * x) →
        (Nat.card ↥(hs100P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 100)))) = 7680 ∧
          Nat.card ↥(hs100P ⊓ centralizer ({Up * x} : Set (Equiv.Perm (Fin 100)))) = 2880) ∨
        (Nat.card ↥(hs100P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 100)))) = 2880 ∧
          Nat.card ↥(hs100P ⊓ centralizer ({Up * x} : Set (Equiv.Perm (Fin 100)))) = 7680)) ∧
      (x ∉ Jm → (∀ j ∈ Jm, orderOf j = 3 → x * j ≠ j * x) →
        Nat.card ↥(hs100P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 100)))) = 2880 ∧
        Nat.card ↥(hs100P ⊓ centralizer ({Up * x} : Set (Equiv.Perm (Fin 100)))) = 2880) := by
  obtain ⟨hgs, hvz, hZP, hZ2', hZ1, hvy, hYP, hU1, hX, hR, hvp, hPP⟩ := basic_spec hb
  have hvu := valid_u0 hb
  obtain ⟨hcZ, hcU, -, hfZ, hfU⟩ := classes_spec hb hcl
  have hU2 := u_order hb hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ2 : orderOf Zp = 2 := orderOf_eq_prime (by rw [pow_two]; exact hZ2') hZ1
  have hUP : Up ∈ hs100P := (hX 0 (by norm_num)).2
  have hru : Rep 100 u0 Up := rep_of_validA hvu
  obtain ⟨haenum, hjenum⟩ := a_enums ha
  have hUsq : Up * Up = 1 := by
    have := pow_orderOf_eq_one Up
    rwa [hU2, pow_two] at this
  intro x hx hx2 hx1
  obtain ⟨a, -, hra, hone⟩ := forall_closure haenum (p := tableOne) ht hx
  have hxa : (eqA 100 (compA 100 a a) (idA 100) && !eqA 100 a (idA 100)) = true := by
    rw [Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨(eqA_iff (rep_compA hra hra) rep_idA).2 hx2,
      Bool.eq_false_iff.2 fun h => hx1 ((eqA_iff hra rep_idA).1 h)⟩
  unfold tableOne at hone
  rw [hxa] at hone
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hone
  obtain ⟨⟨h1, h2⟩, h3⟩ := hone
  have hxP : x ∈ hs100P := (hAle hx).1
  have hxU : x * Up = Up * x := mem_centralizer_singleton_iff.1 (hAle hx).2
  have hX2 : orderOf x = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hrux : Rep 100 (compA 100 u0 a) (Up * x) := rep_compA hru hra
  have hUx2 : orderOf (Up * x) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · have hc : Commute Up x := hxU.symm
      rw [hc.mul_pow, pow_two, pow_two, hUsq, hx2, one_mul]
    · intro h
      have : x = Up⁻¹ := eq_inv_of_mul_eq_one_right h
      have hxz : x ∈ zpowers Up := by
        rw [this, inv_eq_of_mul_eq_one_right hUsq]
        exact mem_zpowers _
      exact hx1 (Subgroup.disjoint_def.1 hdisj hxz hx)
  have cx := cent_fix hcZ hcU hZP hUP hZ2 hU2 hfZ hfU hxP hX2
  have cux := cent_fix hcZ hcU hZP hUP hZ2 hU2 hfZ hfU (hs100P.mul_mem hUP hxP) hUx2
  have hfx : fixCnt a = fixN x := fixCnt_eq hra
  have hfux : fixCnt (compA 100 u0 a) = fixN (Up * x) := fixCnt_eq hrux
  have hI : x ∈ Jm ↔ jCert.pts.toList.any (eqA 100 a) = true :=
    mem_closure_iff_any hjenum hra
  have hF : (∃ j ∈ Jm, orderOf j = 3 ∧ x * j = j * x) ↔
      ord3J.any (fun b => commA 100 a b) = true := by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨j, hj, hj3, hcomm⟩
      obtain ⟨b, hb, hrb, -⟩ := forall_closure hjenum (p := fun _ => true) (by simp) hj
      refine ⟨b, ?_, (commA_iff hra hrb).2 hcomm⟩
      simp only [ord3J, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨hb, ?_, ?_⟩
      · rw [eqA_iff (rep_pw hrb 3) rep_idA, ← hj3]
        exact pow_orderOf_eq_one j
      · refine Bool.eq_false_iff.2 fun h => ?_
        have := (eqA_iff hrb rep_idA).1 h
        rw [this, orderOf_one] at hj3
        omega
    · rintro ⟨b, hbm, hcb⟩
      simp only [ord3J, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hbm
      obtain ⟨hbJ, hb3, hb1⟩ := hbm
      have hvb := valid_of_mem hjenum hbJ
      have hrb := rep_of_validA hvb
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hb3' : permOfArr 100 b ^ 3 = 1 := (eqA_iff (rep_pw hrb 3) rep_idA).1 hb3
      have hb1' : permOfArr 100 b ≠ 1 := fun h => by
        have := (eqA_iff hrb rep_idA).2 h
        rw [this] at hb1
        exact absurd hb1 (by simp)
      exact ⟨permOfArr 100 b, enumOK_mem_of_mem keys_lt hjenum hrb hbJ, orderOf_eq_prime hb3' hb1',
        (commA_iff hra hrb).1 hcb⟩
  refine ⟨fun hxJ => ?_, fun hxJ hf3 => ?_, fun hxJ hf3 => ?_⟩
  · have hIt := hI.1 hxJ
    simp only [hIt, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h1
    rw [hfx, hfux] at h1
    exact ⟨cx.1 h1.1, cux.2 h1.2⟩
  · have hIf : jCert.pts.toList.any (eqA 100 a) = false :=
      Bool.eq_false_iff.2 fun h => hxJ (hI.2 h)
    have hFt := hF.1 hf3
    simp only [hIf, hFt, Bool.false_or, Bool.not_true, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq] at h2
    rw [hfx, hfux] at h2
    rcases h2 with h2 | h2
    · exact Or.inl ⟨cx.1 h2.1, cux.2 h2.2⟩
    · exact Or.inr ⟨cx.2 h2.1, cux.1 h2.2⟩
  · have hIf : jCert.pts.toList.any (eqA 100 a) = false :=
      Bool.eq_false_iff.2 fun h => hxJ (hI.2 h)
    have hFf : ord3J.any (fun b => commA 100 a b) = false :=
      Bool.eq_false_iff.2 fun h => by
        obtain ⟨j, hj, hj3, hcomm⟩ := hF.2 h
        exact hf3 j hj hj3 hcomm
    simp only [hIf, hFf, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h3
    rw [hfx, hfux] at h3
    exact ⟨cx.2 h3.1, cux.2 h3.2⟩

end Certified

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0
