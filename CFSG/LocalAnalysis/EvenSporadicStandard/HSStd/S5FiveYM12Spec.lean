module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYGrp
public import CFSG.RankThree.PartOne.KS.OrbitCert
public import Certificates.Certificate27262

public section

namespace CFSG.EvenSporadicStandard.HSStd.FiveY

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.RankThree.Native CFSG.Blueprint

theorem exists_conj_of_mem_class {n : ℕ} {gs : Array (Array ℕ)} {ps : List ℕ}
    (hgs : ∀ k < gs.size, validA n gs[k]! = true) {x : Array ℕ} {c : ArrCert}
    (hc : arrCertOK (fun k a => conjA n gs[k]! a) gs.size (validA n) (keyA n ps) x c = true)
    {i : ℕ} (hi : i < c.pts.size) :
    ∃ g ∈ Subgroup.closure (permsA n gs),
      permOfArr n c.pts[i]! = g * permOfArr n x * g⁻¹ := by
  classical
  let gens' : ℕ → ConjAct (Equiv.Perm (Fin n)) := fun k =>
    ConjAct.toConjAct (permOfArr n gs[k]!)
  have hact : ∀ k < gs.size, ∀ a, validA n a = true →
      permOfArr n (conjA n gs[k]! a) = gens' k • permOfArr n a := by
    intro k hk a ha
    rw [ConjAct.smul_def]
    exact permOfArr_eq_of_rep (rep_conjA (hgs k hk) (rep_of_validA ha))
  have hroot : c.pts[0]! = x := arrCertOK_root hc
  obtain ⟨hτ, hτmem⟩ := arrCertOK_treeWord (G := ConjAct (Equiv.Perm (Fin n)))
    (X := Equiv.Perm (Fin n)) (dec := permOfArr n) («gens» := gens') hc hact hi
  set R := Subgroup.closure (permsA n gs) with hR
  set H : Subgroup (ConjAct (Equiv.Perm (Fin n))) :=
    Subgroup.closure (gens' '' {k | k < gs.size}) with hH
  have hHR : H = R.map (ConjAct.toConjAct : Equiv.Perm (Fin n) ≃* _).toMonoidHom := by
    rw [hH, hR, MonoidHom.map_closure]
    congr 1
    ext g
    simp only [Set.mem_image, permsA, Set.mem_ofPred_eq, gens']
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨permOfArr n gs[k]!, ⟨k, hk, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, rfl⟩
  have hHmem : ∀ g : ConjAct (Equiv.Perm (Fin n)), g ∈ H ↔ ConjAct.ofConjAct g ∈ R := by
    intro g
    rw [hHR, Subgroup.mem_map_equiv]
    rfl
  refine ⟨ConjAct.ofConjAct (CFSG.Perm.treeWord (fun i => c.par[i]!) (fun i => c.lab[i]!) gens' i),
    (hHmem _).1 hτmem, ?_⟩
  rw [hroot] at hτ
  rw [← hτ, ConjAct.smul_def]

abbrev m12gA : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]

abbrev m12gB : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
    List.formPerm [5, 9, 6]

theorem rep_m12A : CFSG.Monster.B.Co2.Rep 12 m12A m12gA := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem rep_m12B : CFSG.Monster.B.Co2.Rep 12 m12B m12gB := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem permsA_m12 : permsA 12 m12Gens = {m12gA, m12gB} := by
  ext g
  simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have : k < 2 := by simpa [m12Gens] using hk
    interval_cases k
    · exact Or.inl (permOfArr_eq_of_rep rep_m12A)
    · exact Or.inr (permOfArr_eq_of_rep rep_m12B)
  · rintro (rfl | rfl)
    · exact ⟨0, by simp [m12Gens], permOfArr_eq_of_rep rep_m12A⟩
    · exact ⟨1, by simp [m12Gens], permOfArr_eq_of_rep rep_m12B⟩

theorem closure_permsA_m12 : Subgroup.closure (permsA 12 m12Gens) = NativeSporadic.M12 := by
  rw [permsA_m12]
  rfl

structure M12Facts : Prop where
  enumM : enumOKL 12 m12Gens m12Keys m12Cert = true
  sizeM : m12Cert.pts.size = 95040
  inv0 : isInvol12 m12Inv0 = true
  inv1 : isInvol12 m12Inv1 = true
  cls0 : arrCertOKL m12Act m12Gens.size (validA 12) (keyA 12 m12Keys) m12Inv0 m12Cls0 = true
  size0 : m12Cls0.pts.size = 396
  cls1 : arrCertOKL m12Act m12Gens.size (validA 12) (keyA 12 m12Keys) m12Inv1 m12Cls1 = true
  size1 : m12Cls1.pts.size = 495
  cover : m12Pts.all (fun x => !eqA 12 (compA 12 x x) (idA 12) || eqA 12 x (idA 12) ||
      m12Pts0.any (eqA 12 x) || m12Pts1.any (eqA 12 x)) = true
  enumC : enumOKL 12 m12CGens m12Keys m12CCert = true
  sizeC : m12CCert.pts.size = 240
  gensC : allLt m12CGens.size (fun k => eqA 12 (compA 12 m12Inv0 m12CGens[k]!)
      (compA 12 m12CGens[k]! m12Inv0) && m12Pts.any (eqA 12 m12CGens[k]!)) = true
  enumD : enumOKL 12 m12DGens m12Keys m12DCert = true
  sizeD : m12DCert.pts.size = 60
  comm : m12CPts.all (fun x => m12CPts.all (fun y =>
      m12DPts.any (eqA 12 (commutatorA 12 x y)))) = true
  invD : m12DPts.all (fun d => !eqA 12 (compA 12 d d) (idA 12) ||
      m12Pts0.any (eqA 12 (compA 12 m12Inv0 d))) = true

theorem m12Facts_of_check (h : m12OK = true) : M12Facts := by
  simp only [m12OK, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

noncomputable abbrev A0 : Equiv.Perm (Fin 12) := permOfArr 12 m12Inv0

noncomputable abbrev A1 : Equiv.Perm (Fin 12) := permOfArr 12 m12Inv1

theorem keys_lt : ∀ p ∈ m12Keys, p < 12 := by
  intro p hp
  simp only [m12Keys, List.mem_cons, List.not_mem_nil, or_false] at hp
  omega

theorem exists_index_of_mem {l : Array (Array ℕ)} {y : Array ℕ} (hy : y ∈ l.toList) :
    ∃ j < l.size, l[j]! = y := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  have hj' : j < l.size := by simpa using hj
  exact ⟨j, hj', by rw [getElem!_pos l j hj']; simp⟩

theorem mem_toList_of_lt {l : Array (Array ℕ)} {i : ℕ} (hi : i < l.size) :
    l[i]! ∈ l.toList := by
  rw [getElem!_pos _ i hi]
  exact Array.mem_toList_iff.2 (Array.getElem_mem hi)

theorem perm_eq_of_eqA {n : ℕ} {x y : Array ℕ} (hx : validA n x = true) (hy : validA n y = true)
    (h : eqA n x y = true) : permOfArr n x = permOfArr n y :=
  (eqA_iff (rep_of_validA hx) (rep_of_validA hy)).1 h

section Consequences

variable (f : M12Facts)

include f

theorem M12Facts.gens_valid : ∀ k < m12Gens.size, validA 12 m12Gens[k]! = true :=
  fun _ hk => enumOK_gens_valid (enumOK_of_enumOKL f.enumM) hk

theorem M12Facts.spec_M :
    (∀ x, x ∈ NativeSporadic.M12 ↔ ∃ i < m12Cert.pts.size, permOfArr 12 m12Cert.pts[i]! = x) ∧
      Nat.card NativeSporadic.M12 = 95040 ∧
      ∀ i < m12Cert.pts.size, validA 12 m12Cert.pts[i]! = true := by
  obtain ⟨h1, h2, h3⟩ := enumOK_spec keys_lt (enumOK_of_enumOKL f.enumM)
  rw [closure_permsA_m12] at h1 h2
  exact ⟨h1, h2.trans f.sizeM, h3⟩

theorem M12Facts.class_data {x : Array ℕ} {c : ArrCert}
    (hc : arrCertOKL m12Act m12Gens.size (validA 12) (keyA 12 m12Keys) x c = true) :
    (∀ i < c.pts.size, ∃ g ∈ NativeSporadic.M12,
        permOfArr 12 c.pts[i]! = g * permOfArr 12 x * g⁻¹) ∧
      Nat.card NativeSporadic.M12 = c.pts.size * Nat.card ↥(NativeSporadic.M12 ⊓
        centralizer ({permOfArr 12 x} : Set (Equiv.Perm (Fin 12)))) := by
  have hc' : arrCertOK (fun k a => conjA 12 m12Gens[k]! a) m12Gens.size (validA 12)
      (keyA 12 m12Keys) x c = true := arrCertOK_of_arrCertOKL hc
  refine ⟨fun i hi => ?_, ?_⟩
  · obtain ⟨g, hg, h⟩ := exists_conj_of_mem_class f.gens_valid hc' hi
    rw [closure_permsA_m12] at hg
    exact ⟨g, hg, h⟩
  · have := (CFSG.RankThree.PartOne.card_closure_eq_card_mul_card_centralizer keys_lt
      f.gens_valid hc').2
    rw [closure_permsA_m12] at this
    exact this

theorem M12Facts.cent0 :
    Nat.card ↥(NativeSporadic.M12 ⊓ centralizer ({A0} : Set (Equiv.Perm (Fin 12)))) = 240 := by
  have h : 95040 = 396 * Nat.card ↥(NativeSporadic.M12 ⊓
      centralizer ({A0} : Set (Equiv.Perm (Fin 12)))) := by
    have := (f.class_data f.cls0).2
    rwa [f.spec_M.2.1, f.size0] at this
  omega

theorem M12Facts.cent1 :
    Nat.card ↥(NativeSporadic.M12 ⊓ centralizer ({A1} : Set (Equiv.Perm (Fin 12)))) = 192 := by
  have h : 95040 = 495 * Nat.card ↥(NativeSporadic.M12 ⊓
      centralizer ({A1} : Set (Equiv.Perm (Fin 12)))) := by
    have := (f.class_data f.cls1).2
    rwa [f.spec_M.2.1, f.size1] at this
  omega

theorem M12Facts.cover_involutions {a : Equiv.Perm (Fin 12)} (ha : a ∈ NativeSporadic.M12)
    (ha2 : a * a = 1) (ha1 : a ≠ 1) :
    (∃ g ∈ NativeSporadic.M12, a = g * A0 * g⁻¹) ∨
      ∃ g ∈ NativeSporadic.M12, a = g * A1 * g⁻¹ := by
  obtain ⟨i, hi, rfl⟩ := (f.spec_M.1 a).1 ha
  set x := m12Cert.pts[i]! with hx
  have hvx := f.spec_M.2.2 i hi
  have hrx := rep_of_validA hvx
  have hmem : x ∈ m12Pts := mem_toList_of_lt hi
  have hc := List.all_eq_true.1 f.cover x hmem
  have hsq : eqA 12 (compA 12 x x) (idA 12) = true :=
    (eqA_iff (rep_compA hrx hrx) rep_idA).2 ha2
  have hne : eqA 12 x (idA 12) = false := by
    by_contra h
    exact ha1 ((eqA_iff hrx rep_idA).1 (by simpa using h))
  simp only [hsq, hne, Bool.not_true, Bool.false_or, Bool.or_eq_true, List.any_eq_true] at hc
  rcases hc with ⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩
  · left
    obtain ⟨j, hj, rfl⟩ := exists_index_of_mem hy
    obtain ⟨g, hg, h⟩ := (f.class_data f.cls0).1 j hj
    exact ⟨g, hg, (perm_eq_of_eqA hvx (by
      exact arrCertOK_valid (arrCertOK_of_arrCertOKL f.cls0) hj) hxy).trans h⟩
  · right
    obtain ⟨j, hj, rfl⟩ := exists_index_of_mem hy
    obtain ⟨g, hg, h⟩ := (f.class_data f.cls1).1 j hj
    exact ⟨g, hg, (perm_eq_of_eqA hvx (by
      exact arrCertOK_valid (arrCertOK_of_arrCertOKL f.cls1) hj) hxy).trans h⟩

theorem M12Facts.inv0_spec : validA 12 m12Inv0 = true ∧ A0 * A0 = 1 ∧ A0 ≠ 1 := by
  have h := f.inv0
  simp only [isInvol12, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hv, hsq⟩, hne⟩ := h
  have hr := rep_of_validA hv
  refine ⟨hv, (eqA_iff (rep_compA hr hr) rep_idA).1 hsq, fun h1 => ?_⟩
  have := (eqA_iff hr rep_idA).2 h1
  rw [hne] at this
  exact absurd this (by simp)

theorem M12Facts.closure_C : Subgroup.closure (permsA 12 m12CGens) =
    NativeSporadic.M12 ⊓ centralizer ({A0} : Set (Equiv.Perm (Fin 12))) := by
  obtain ⟨-, hcardC, -⟩ := enumOK_spec keys_lt (enumOK_of_enumOKL f.enumC)
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < m12CGens.size := hk
    have hv : validA 12 m12CGens[k]! = true :=
      enumOK_gens_valid (enumOK_of_enumOKL f.enumC) hk'
    have := allLt_spec f.gensC hk'
    simp only [Bool.and_eq_true] at this
    obtain ⟨hcomm, hmem⟩ := this
    refine ⟨?_, ?_⟩
    · rw [← closure_permsA_m12]
      exact enumOK_mem_of_any keys_lt (enumOK_of_enumOKL f.enumM) (rep_of_validA hv) hmem
    · have hr0 := rep_of_validA f.inv0_spec.1
      have hrk := rep_of_validA hv
      have := (eqA_iff (rep_compA hr0 hrk) (rep_compA hrk hr0)).1 hcomm
      exact mem_centralizer_singleton_iff.2 this.symm
  · rw [f.cent0, hcardC, f.sizeC]

theorem M12Facts.fusion_perm {b : Equiv.Perm (Fin 12)}
    (hb : b ∈ ⁅NativeSporadic.M12 ⊓ centralizer ({A0} : Set (Equiv.Perm (Fin 12))),
      NativeSporadic.M12 ⊓ centralizer ({A0} : Set (Equiv.Perm (Fin 12)))⁆)
    (hbb : b * b = 1) : ∃ g ∈ NativeSporadic.M12, g * A0 * g⁻¹ = A0 * b := by
  obtain ⟨hmemC, -, hvalC⟩ := enumOK_spec keys_lt (enumOK_of_enumOKL f.enumC)
  obtain ⟨hmemD, -, hvalD⟩ := enumOK_spec keys_lt (enumOK_of_enumOKL f.enumD)
  have hD : ⁅NativeSporadic.M12 ⊓ centralizer ({A0} : Set (Equiv.Perm (Fin 12))),
      NativeSporadic.M12 ⊓ centralizer ({A0} : Set (Equiv.Perm (Fin 12)))⁆ ≤
        Subgroup.closure (permsA 12 m12DGens) := by
    rw [← f.closure_C, Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨i, hi, rfl⟩ := (hmemC g₁).1 hg₁
    obtain ⟨j, hj, rfl⟩ := (hmemC g₂).1 hg₂
    have hi' : m12CCert.pts[i]! ∈ m12CPts := mem_toList_of_lt hi
    have hj' : m12CCert.pts[j]! ∈ m12CPts := mem_toList_of_lt hj
    have h1 := List.all_eq_true.1 f.comm _ hi'
    have h2 := List.all_eq_true.1 h1 _ hj'
    exact enumOK_mem_of_any keys_lt (enumOK_of_enumOKL f.enumD)
      (rep_commutatorA (hvalC i hi) (hvalC j hj)) h2
  obtain ⟨j, hj, rfl⟩ := (hmemD b).1 (hD hb)
  have hvd := hvalD j hj
  have hrd := rep_of_validA hvd
  have hd := List.all_eq_true.1 f.invD _ (mem_toList_of_lt hj)
  have hsq : eqA 12 (compA 12 m12DCert.pts[j]! m12DCert.pts[j]!) (idA 12) = true :=
    (eqA_iff (rep_compA hrd hrd) rep_idA).2 hbb
  simp only [hsq, Bool.not_true, Bool.false_or, List.any_eq_true] at hd
  obtain ⟨y, hy, hxy⟩ := hd
  obtain ⟨j', hj', rfl⟩ := exists_index_of_mem hy
  obtain ⟨g, hg, h⟩ := (f.class_data f.cls0).1 j' hj'
  have hr0 := rep_of_validA f.inv0_spec.1
  have hvy := arrCertOK_valid (arrCertOK_of_arrCertOKL f.cls0) hj'
  have heq := (eqA_iff (rep_compA hr0 hrd) (rep_of_validA hvy)).1 hxy
  exact ⟨g, hg, by rw [← h, ← heq]⟩

end Consequences

theorem m12_fusion {a b : ↥NativeSporadic.M12} (ha : a * a = 1)
    (ha1 : a ≠ 1) (hC : Nat.card ↥(centralizer ({a} : Set ↥NativeSporadic.M12)) = 240)
    (hb : b ∈ ⁅centralizer ({a} : Set ↥NativeSporadic.M12),
      centralizer ({a} : Set ↥NativeSporadic.M12)⁆) (hbb : b * b = 1) : IsConj (a * b) a := by
  have f := m12Facts_of_check Certificates.certificate27262
  have haP : (a : Equiv.Perm (Fin 12)) * (a : Equiv.Perm (Fin 12)) = 1 := congrArg Subtype.val ha
  have ha1P : (a : Equiv.Perm (Fin 12)) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hbbP : (b : Equiv.Perm (Fin 12)) * (b : Equiv.Perm (Fin 12)) = 1 := congrArg Subtype.val hbb
  have hcentP : Nat.card ↥(NativeSporadic.M12 ⊓
      centralizer ({(a : Equiv.Perm (Fin 12))} : Set (Equiv.Perm (Fin 12)))) = 240 := by
    rw [← card_centralizer_subtype NativeSporadic.M12 a]
    exact hC
  rcases f.cover_involutions a.2 haP ha1P with ⟨g, hg, hga⟩ | ⟨g, hg, hga⟩
  · have hbP : (b : Equiv.Perm (Fin 12)) ∈
        ⁅NativeSporadic.M12 ⊓ centralizer ({(a : Equiv.Perm (Fin 12))} :
          Set (Equiv.Perm (Fin 12))),
          NativeSporadic.M12 ⊓ centralizer ({(a : Equiv.Perm (Fin 12))} :
          Set (Equiv.Perm (Fin 12)))⁆ := by
      have := Subgroup.mem_map_of_mem NativeSporadic.M12.subtype hb
      rwa [Subgroup.map_commutator, map_subtype_centralizer] at this
    have hb' : g⁻¹ * (b : Equiv.Perm (Fin 12)) * g ∈
        ⁅NativeSporadic.M12 ⊓ centralizer ({A0} : Set (Equiv.Perm (Fin 12))),
          NativeSporadic.M12 ⊓ centralizer ({A0} : Set (Equiv.Perm (Fin 12)))⁆ := by
      have := Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hbP
      rw [Subgroup.map_commutator] at this
      rw [hga, map_conj_inf_centralizer NativeSporadic.M12 hg] at this
      simpa [MulAut.conj_apply] using this
    have hb2 : g⁻¹ * (b : Equiv.Perm (Fin 12)) * g * (g⁻¹ * (b : Equiv.Perm (Fin 12)) * g) = 1 := by
      calc g⁻¹ * (b : Equiv.Perm (Fin 12)) * g * (g⁻¹ * (b : Equiv.Perm (Fin 12)) * g) =
          g⁻¹ * ((b : Equiv.Perm (Fin 12)) * (b : Equiv.Perm (Fin 12))) * g := by group
        _ = 1 := by rw [hbbP]; group
    obtain ⟨h, hh, hfus⟩ := f.fusion_perm hb' hb2
    refine isConj_iff.2 ⟨⟨g * h⁻¹ * g⁻¹, NativeSporadic.M12.mul_mem
      (NativeSporadic.M12.mul_mem hg (NativeSporadic.M12.inv_mem hh))
      (NativeSporadic.M12.inv_mem hg)⟩, Subtype.ext ?_⟩
    have e1 : (a : Equiv.Perm (Fin 12)) * (b : Equiv.Perm (Fin 12)) =
        g * (h * A0 * h⁻¹) * g⁻¹ := by
      rw [hfus, hga]
      group
    show g * h⁻¹ * g⁻¹ * ((a : Equiv.Perm (Fin 12)) * (b : Equiv.Perm (Fin 12))) *
      (g * h⁻¹ * g⁻¹)⁻¹ = (a : Equiv.Perm (Fin 12))
    rw [e1, hga]
    group
  · exfalso
    have : Nat.card ↥(NativeSporadic.M12 ⊓
        centralizer ({(a : Equiv.Perm (Fin 12))} : Set (Equiv.Perm (Fin 12)))) = 192 := by
      rw [hga, card_inf_centralizer_conj NativeSporadic.M12 hg]
      exact f.cent1
    omega

end CFSG.EvenSporadicStandard.HSStd.FiveY
