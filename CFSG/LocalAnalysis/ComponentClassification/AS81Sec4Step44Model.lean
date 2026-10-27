module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step44Tests
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaModel

public section

namespace CFSG.ComponentClassification.AS81.Hexa

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow

structure V0Parts : Prop where
  len : hexaV0.length = 4
  zero : eqA 64 (v0A 0) (idA 64) = true
  ne : (List.range 4).all (fun i => i == 0 || !(eqA 64 (v0A i) (idA 64))) = true
  mul : (List.range 4).all (fun i => (List.range 4).all fun j =>
    eqA 64 (mulN 64 (v0A i) (v0A j)) (v0A (i ^^^ j))) = true
  mem : (List.range 4).all (fun i => validA 64 (v0A i) && inLN 64 (eltsN 64 hexaMGens) (v0A i) &&
    fix16A (v0A i)) = true
  all : (eltsN 64 hexaMGens).all (fun m => !(fix16A m) || inV0A m) = true
  omValid : validA 64 hexaOmega = true
  omMem : inLN 64 (eltsN 64 hexaMGens) hexaOmega = true
  omFix : (List.range 64).all (fun v => v == 0 || hexaOmega[v]! != v) = true
  omPow : eqA 64 (powN 64 hexaOmega 3) (idA 64) = true
  omComm : (List.range 4).all (fun i => commN 64 hexaOmega (v0A i)) = true
  muValid : validA 64 hexaMu = true
  muMem : inLN 64 (eltsN 64 hexaMGens) hexaMu = true
  muPow : eqA 64 (powN 64 hexaMu 3) (idA 64) = true
  muComm : commN 64 hexaMu hexaOmega = true
  piSize : hexaMuPi.size = 4
  muConj : (List.range 4).all (fun i => decide (hexaMuPi[i]! < 4) &&
    eqA 64 (conjA 64 hexaMu (v0A i)) (v0A hexaMuPi[i]!)) = true
  k36 : enumCheckN 64 k36Gens 36 = true
  om9 : enumCheckN 64 [hexaOmega, hexaMu] 9 = true
  k36Mul : (eltsN 64 k36Gens).all (fun k => (List.range 4).any fun i =>
    inLN 64 (eltsN 64 [hexaOmega, hexaMu]) (mulN 64 (v0A i) k)) = true
  k36Pow : (eltsN 64 k36Gens).all (fun k => inV0A (powN 64 k 9)) = true
  k36Of : (eltsN 64 hexaMGens).all (fun m => !(normV0A m && inV0A (powN 64 m 9)) ||
    inLN 64 (eltsN 64 k36Gens) m) = true
  card144 : ((eltsN 64 hexaMGens).filter normV0A).length = 144
  norm144 : enumCheckN 64 hexaNormGens 144 = true
  normGens : hexaNormGens.all (fun m => inLN 64 (eltsN 64 hexaMGens) m && normV0A m) = true
  lt16 : (eltsN 64 hexaMGens).all (fun m => !(normV0A m) ||
    (List.range 16).all fun v => decide (m[v]! < 16)) = true
  six : (eltsN 64 hexaMGens).all (fun m => !(normV0A m && sixTrivA m) || inV0A m) = true

theorem v0Check_parts (h : v0Check = true) : V0Parts := by
  simp only [v0Check, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27⟩

structure SMParts : Prop where
  tauMul : f3Pairs.all (fun c => f3Pairs.all fun c' => (List.range 256).all fun i =>
    smTau c.1 c.2 (smTau c'.1 c'.2 i) == smTau (c.1 + c'.1) (c.2 + c'.2) i) = true
  tauNe : f3Pairs.all (fun c => c == (0, 0) || (List.range 256).any fun i => smTau c.1 c.2 i != i) =
    true
  g0 : smTau 1 0 64 = 64
  g1 : smTau 0 1 30 = 30
  g2 : smTau 1 1 4 = 4
  g3 : smTau 1 2 1 = 1
  nf : eqA 256 (smCand (1, 0) (0, 1) 64 30 4 1) (idA 256) = true
  n72 : enumCheckN 256 hexaNGens 72 = true
  nHom : hexaNGens.all smHomA = true
  aut : smAutN (eltsN 256 hexaNGens) = true
  ne36 : enumCheckN 256 hexaNEGens 36 = true
  neN : hexaNEGens.all (inLN 256 (eltsN 256 hexaNGens)) = true
  nE : (eltsN 256 hexaNGens).all (fun f => !(presTA f) || inLN 256 (eltsN 256 hexaNEGens) f) =
    true
  p8 : enumCheckN 256 hexaPGens 8 = true
  pN : hexaPGens.all (inLN 256 (eltsN 256 hexaNGens)) = true
  pe4 : enumCheckN 256 hexaPEGens 4 = true
  peNE : hexaPEGens.all (inLN 256 (eltsN 256 hexaNEGens)) = true
  lam : enumCheckN 256 smLamGens 256 = true
  ab : enumCheckN 256 (smLamGens ++ hexaPGens) 2048 = true
  abGraph : enumCheckN 288 (List.zipWith (pairA 256) (smLamGens ++ hexaPGens) hexaAbImgs) 2048 =
    true
  abLen : hexaAbImgs.length = 10
  abSize : (smLamGens ++ hexaPGens).all (·.size == 256) = true
  abImgSize : hexaAbImgs.all (·.size == 32) = true
  abY : enumCheckN 32 hexaAbImgs 2048 = true
  y32 : enumCheckN 32 GrSLit.HeldFix.hfT0Tabs32.toList 2048 = true
  abGens : GrSLit.HeldFix.hfT0Tabs32.toList.all (inLN 32 (eltsN 32 hexaAbImgs)) = true
  aa : enumCheckN 256 (smLamGens ++ hexaPEGens) 1024 = true
  aaGraph : enumCheckN 272 (List.zipWith (pairA 256) (smLamGens ++ hexaPEGens) hexaAaImgs) 1024 =
    true
  aaLen : hexaAaImgs.length = 10
  aaSize : (smLamGens ++ hexaPEGens).all (·.size == 256) = true
  aaImgSize : hexaAaImgs.all (·.size == 16) = true
  aaX : enumCheckN 16 hexaAaImgs 1024 = true
  x16 : enumCheckN 16 heSyl16 1024 = true
  aaGens : heSyl16.all (inLN 16 (eltsN 16 hexaAaImgs)) = true

theorem smCheck_parts (h : smCheck = true) : SMParts := by
  simp only [smCheck, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34⟩

theorem step44Check_parts (h : step44Check = true) : v0Check = true ∧ smCheck = true := by
  simp only [step44Check, Bool.and_eq_true] at h
  exact h

theorem rep_of_inLN {n : ℕ} {gs : List (Array ℕ)} {m : ℕ} (hg : enumCheckN n gs m = true)
    {t : Array ℕ} (h : inLN n (eltsN n gs) t = true) :
    Rep n t (permOfArr n t) ∧ permOfArr n t ∈ grpN n gs := by
  rw [inLN, List.any_eq_true] at h
  obtain ⟨u, hu, he⟩ := h
  have hru := rep_of_validA (validA_of_mem_elts hg hu)
  have hrt : Rep n t (permOfArr n u) := fun x => by
    have := allLt_spec he x.2
    rw [beq_iff_eq] at this
    rw [this]
    exact hru x
  rw [permOfArr_eq_of_rep hrt]
  exact ⟨hrt, (mem_grpN_iff hg).2 ⟨u, hu, hru⟩⟩

noncomputable abbrev v0P (i : ℕ) : Equiv.Perm (Fin 64) := permOfArr 64 (v0A i)

noncomputable abbrev omegaP : Equiv.Perm (Fin 64) := permOfArr 64 hexaOmega

noncomputable abbrev muP : Equiv.Perm (Fin 64) := permOfArr 64 hexaMu

noncomputable abbrev k36 : Subgroup (Equiv.Perm (Fin 64)) := grpN 64 k36Gens

noncomputable abbrev v0Grp : Subgroup (Equiv.Perm (Fin 64)) := grpN 64 hexaV0

noncomputable abbrev om9 : Subgroup (Equiv.Perm (Fin 64)) := grpN 64 [hexaOmega, hexaMu]

section V0

variable (hc : hexaCheck = true) (h : step44Check = true)

include h in
theorem v0Parts : V0Parts := v0Check_parts (step44Check_parts h).1

include h in
theorem smParts : SMParts := smCheck_parts (step44Check_parts h).2

include hc h

theorem rep_v0A {i : ℕ} (hi : i < 4) :
    validA 64 (v0A i) = true ∧ Rep 64 (v0A i) (v0P i) ∧ v0P i ∈ hexaM := by
  obtain ⟨-, hM, -⟩ := hexaCheck_parts hc
  have h5 := List.all_eq_true.1 (v0Parts h).mem i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true] at h5
  exact ⟨h5.1.1, rep_of_inLN hM h5.1.2⟩

theorem rep_omega : Rep 64 hexaOmega omegaP ∧ omegaP ∈ hexaM := by
  obtain ⟨-, hM, -⟩ := hexaCheck_parts hc
  exact rep_of_inLN hM (v0Parts h).omMem

theorem rep_mu : Rep 64 hexaMu muP ∧ muP ∈ hexaM := by
  obtain ⟨-, hM, -⟩ := hexaCheck_parts hc
  exact rep_of_inLN hM (v0Parts h).muMem

theorem v0P_zero : v0P 0 = 1 :=
  eq_of_eqA (rep_v0A hc h (by norm_num)).2.1 rep_idA (v0Parts h).zero

theorem v0P_ne_one {i : ℕ} (hi : i < 4) (hi0 : i ≠ 0) : v0P i ≠ 1 := by
  have h3 := List.all_eq_true.1 (v0Parts h).ne i (List.mem_range.2 hi)
  intro he
  have := (eqA_iff (rep_v0A hc h hi).2.1 rep_idA).2 he
  simp [hi0, this] at h3

theorem v0P_mul {i j : ℕ} (hi : i < 4) (hj : j < 4) : v0P i * v0P j = v0P (i ^^^ j) := by
  have h4 := List.all_eq_true.1 (List.all_eq_true.1 (v0Parts h).mul i (List.mem_range.2 hi)) j
    (List.mem_range.2 hj)
  have hij : i ^^^ j < 4 := Nat.xor_lt_two_pow (n := 2) hi hj
  exact eq_of_eqA (rep_mulN (rep_v0A hc h hi).2.1 (rep_v0A hc h hj).2.1) (rep_v0A hc h hij).2.1 h4

theorem exists_v0P_of_fix {m : Equiv.Perm (Fin 64)} (hm : m ∈ hexaM)
    (hfix : ∀ v : Fin 64, v.val < 16 → m v = v) : ∃ i < 4, m = v0P i := by
  obtain ⟨-, hM, -⟩ := hexaCheck_parts hc
  obtain ⟨t, ht, hrt⟩ := (mem_grpN_iff hM).1 hm
  have h6 := List.all_eq_true.1 (v0Parts h).all t ht
  have hf : fix16A t = true := List.all_eq_true.2 fun v hv => by
    have hv' := List.mem_range.1 hv
    rw [beq_iff_eq, hrt.apply (by omega : v < 64), hfix ⟨v, by omega⟩ hv']
  rw [hf, Bool.not_true, Bool.false_or, inV0A, List.any_eq_true] at h6
  obtain ⟨i, hi, he⟩ := h6
  have hi' := List.mem_range.1 hi
  exact ⟨i, hi', eq_of_eqA hrt (rep_v0A hc h hi').2.1 he⟩

theorem eq_zero_of_omegaP_fix {v : Fin 64} (hv : omegaP v = v) : v = 0 := by
  have h8 := List.all_eq_true.1 (v0Parts h).omFix v.val (List.mem_range.2 v.2)
  have hv' : hexaOmega[v.val]! = v.val := by
    rw [(rep_omega hc h).1 v, hv]
  by_contra hne
  have hne' : v.val ≠ 0 := fun h0 => hne (Fin.ext h0)
  simp [hne', hv'] at h8

theorem omegaP_pow_three : omegaP ^ 3 = 1 :=
  eq_of_eqA (rep_powN (rep_omega hc h).1 3) rep_idA (v0Parts h).omPow

theorem omegaP_comm_v0P {i : ℕ} (hi : i < 4) : omegaP * v0P i = v0P i * omegaP :=
  (commN_iff (rep_omega hc h).1 (rep_v0A hc h hi).2.1).1
    (List.all_eq_true.1 (v0Parts h).omComm i (List.mem_range.2 hi))

theorem muP_pow_three : muP ^ 3 = 1 :=
  eq_of_eqA (rep_powN (rep_mu hc h).1 3) rep_idA (v0Parts h).muPow

theorem muP_comm_omegaP : muP * omegaP = omegaP * muP :=
  (commN_iff (rep_mu hc h).1 (rep_omega hc h).1).1 (v0Parts h).muComm

omit hc in
theorem muPi_lt {i : ℕ} (hi : i < 4) : hexaMuPi[i]! < 4 := by
  have h15 := List.all_eq_true.1 (v0Parts h).muConj i (List.mem_range.2 hi)
  rw [Bool.and_eq_true, decide_eq_true_eq] at h15
  exact h15.1

theorem muP_conj_v0P {i : ℕ} (hi : i < 4) : muP * v0P i * muP⁻¹ = v0P hexaMuPi[i]! := by
  have h15 := List.all_eq_true.1 (v0Parts h).muConj i (List.mem_range.2 hi)
  rw [Bool.and_eq_true] at h15
  have hr := rep_conjA (v0Parts h).muValid (rep_v0A hc h hi).2.1
  exact eq_of_eqA hr (rep_v0A hc h (muPi_lt h hi)).2.1 h15.2

theorem v0P_mul_self {i : ℕ} (hi : i < 4) : v0P i * v0P i = 1 := by
  rw [v0P_mul hc h hi hi, Nat.xor_self, v0P_zero hc h]

theorem mem_v0Grp_iff {x : Equiv.Perm (Fin 64)} : x ∈ v0Grp ↔ ∃ i < 4, x = v0P i := by
  have hlen := (v0Parts h).len
  constructor
  · intro hx
    let V : Subgroup (Equiv.Perm (Fin 64)) :=
      { carrier := {x | ∃ i < 4, x = v0P i}
        mul_mem' := by
          rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
          exact ⟨i ^^^ j, Nat.xor_lt_two_pow (n := 2) hi hj, v0P_mul hc h hi hj⟩
        one_mem' := ⟨0, by norm_num, (v0P_zero hc h).symm⟩
        inv_mem' := by
          rintro _ ⟨i, hi, rfl⟩
          exact ⟨i, hi, inv_eq_of_mul_eq_one_left (v0P_mul_self hc h hi)⟩ }
    have hle : v0Grp ≤ V := grpN_le fun a ha => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      have hi4 : i < 4 := hlen ▸ hi
      have e : v0A i = hexaV0[i] := getElem!_pos hexaV0 i hi
      exact ⟨i, hi4, congrArg (permOfArr 64) e.symm⟩
    exact hle hx
  · rintro ⟨i, hi, rfl⟩
    have hm : hexaV0[i]! ∈ hexaV0 := by
      rw [getElem!_pos hexaV0 i (by rw [hlen]; exact hi)]
      exact List.getElem_mem _
    exact gen_mem_grpN hm

theorem v0Grp_le_hexaM : v0Grp ≤ hexaM := fun x hx => by
  obtain ⟨i, hi, rfl⟩ := (mem_v0Grp_iff hc h).1 hx
  exact (rep_v0A hc h hi).2.2

theorem normV0A_iff {t : Array ℕ} (hv : validA 64 t = true) :
    normV0A t = true ↔ permOfArr 64 t ∈ normalizer (v0Grp : Set (Equiv.Perm (Fin 64))) := by
  have hrt := rep_of_validA hv
  have key : ∀ i < 4, inV0A (conjA 64 t (v0A i)) = true ↔
      permOfArr 64 t * v0P i * (permOfArr 64 t)⁻¹ ∈ v0Grp := by
    intro i hi
    have hr := rep_conjA hv (rep_v0A hc h hi).2.1
    rw [inV0A, List.any_eq_true, mem_v0Grp_iff hc h]
    constructor
    · rintro ⟨j, hj, he⟩
      have hj' := List.mem_range.1 hj
      exact ⟨j, hj', eq_of_eqA hr (rep_v0A hc h hj').2.1 he⟩
    · rintro ⟨j, hj, he⟩
      exact ⟨j, List.mem_range.2 hj, (eqA_iff hr (rep_v0A hc h hj).2.1).2 he⟩
  rw [normV0A, List.all_eq_true]
  constructor
  · intro hall
    refine mem_normalizer_of_map_conj_le' ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi, rfl⟩ := (mem_v0Grp_iff hc h).1 hx
    exact (key i hi).1 (hall i (List.mem_range.2 hi))
  · intro hn i hi
    have hi' := List.mem_range.1 hi
    refine (key i hi').2 ?_
    exact (mem_normalizer_iff.mp hn _).mp ((mem_v0Grp_iff hc h).2 ⟨i, hi', rfl⟩)

theorem k36_le_hexaM : k36 ≤ hexaM := by
  refine grpN_le fun a ha => ?_
  simp only [k36Gens, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with ha | rfl | rfl
  · exact v0Grp_le_hexaM hc h (gen_mem_grpN ha)
  · exact (rep_omega hc h).2
  · exact (rep_mu hc h).2

omit hc h in
theorem v0Grp_le_k36 : v0Grp ≤ k36 :=
  grpN_le fun _ ha => gen_mem_grpN (List.mem_append_left _ ha)

omit hc h in
theorem omegaP_mem_k36 : omegaP ∈ k36 :=
  gen_mem_grpN (List.mem_append_right _ List.mem_cons_self)

omit hc h in
theorem muP_mem_k36 : muP ∈ k36 :=
  gen_mem_grpN (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))

omit hc h in
theorem omegaP_mem_om9 : omegaP ∈ om9 := gen_mem_grpN List.mem_cons_self

omit hc h in
theorem muP_mem_om9 : muP ∈ om9 := gen_mem_grpN (List.mem_cons_of_mem _ List.mem_cons_self)

omit hc h in
theorem om9_le_k36 : om9 ≤ k36 := by
  refine grpN_le fun a ha => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact omegaP_mem_k36
  · exact muP_mem_k36

omit hc in
theorem card_k36 : Nat.card k36 = 36 := card_grpN (v0Parts h).k36

omit hc in
theorem card_om9 : Nat.card om9 = 9 := card_grpN (v0Parts h).om9

theorem exists_eq_of_mem_om9 {x : Equiv.Perm (Fin 64)} (hx : x ∈ om9) :
    ∃ a b : ℕ, x = omegaP ^ a * muP ^ b := by
  have hcomm := muP_comm_omegaP hc h
  have hcomm' : ∀ a b : ℕ, muP ^ b * omegaP ^ a = omegaP ^ a * muP ^ b := fun a b =>
    ((Commute.pow_pow (show Commute muP omegaP from hcomm) b a).eq)
  let X : Subgroup (Equiv.Perm (Fin 64)) :=
    { carrier := {x | ∃ a b : ℕ, x = omegaP ^ a * muP ^ b}
      mul_mem' := by
        rintro _ _ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
        refine ⟨a + a', b + b', ?_⟩
        rw [pow_add, pow_add, mul_assoc, ← mul_assoc (muP ^ b), hcomm' a' b]
        group
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, b, rfl⟩
        refine ⟨2 * a, 2 * b, ?_⟩
        have h3 : ∀ y : Equiv.Perm (Fin 64), y ^ 3 = 1 → ∀ k : ℕ, (y ^ k)⁻¹ = y ^ (2 * k) := by
          intro y hy k
          rw [← mul_eq_one_iff_inv_eq, ← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, hy,
            one_pow]
        rw [mul_inv_rev, h3 _ (muP_pow_three hc h), h3 _ (omegaP_pow_three hc h), hcomm'] }
  have hle : om9 ≤ X := by
    refine grpN_le fun a ha => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  exact hle hx

theorem exists_v0P_mul_mem_om9 {k : Equiv.Perm (Fin 64)} (hk : k ∈ k36) :
    ∃ i < 4, v0P i * k ∈ om9 := by
  obtain ⟨t, ht, hrt⟩ := (mem_grpN_iff (v0Parts h).k36).1 hk
  have h18 := List.all_eq_true.1 (v0Parts h).k36Mul t ht
  rw [List.any_eq_true] at h18
  obtain ⟨i, hi, hin⟩ := h18
  have hi' := List.mem_range.1 hi
  exact ⟨i, hi', mem_of_inLN (v0Parts h).om9 hin (rep_mulN (rep_v0A hc h hi').2.1 hrt)⟩

theorem pow_nine_mem_v0Grp {k : Equiv.Perm (Fin 64)} (hk : k ∈ k36) : k ^ 9 ∈ v0Grp := by
  obtain ⟨t, ht, hrt⟩ := (mem_grpN_iff (v0Parts h).k36).1 hk
  have h19 := List.all_eq_true.1 (v0Parts h).k36Pow t ht
  rw [inV0A, List.any_eq_true] at h19
  obtain ⟨i, hi, he⟩ := h19
  have hi' := List.mem_range.1 hi
  exact (mem_v0Grp_iff hc h).2 ⟨i, hi', eq_of_eqA (rep_powN hrt 9) (rep_v0A hc h hi').2.1 he⟩

theorem mem_k36_of {m : Equiv.Perm (Fin 64)} (hm : m ∈ hexaM)
    (hn : m ∈ normalizer (v0Grp : Set (Equiv.Perm (Fin 64)))) (h9 : m ^ 9 ∈ v0Grp) : m ∈ k36 := by
  obtain ⟨-, hM, -⟩ := hexaCheck_parts hc
  obtain ⟨t, ht, hrt⟩ := (mem_grpN_iff hM).1 hm
  have hv := validA_of_mem_elts hM ht
  have h20 := List.all_eq_true.1 (v0Parts h).k36Of t ht
  have hn' : normV0A t = true := (normV0A_iff hc h hv).2 (permOfArr_eq_of_rep hrt ▸ hn)
  have h9' : inV0A (powN 64 t 9) = true := by
    obtain ⟨i, hi, he⟩ := (mem_v0Grp_iff hc h).1 h9
    rw [inV0A, List.any_eq_true]
    exact ⟨i, List.mem_range.2 hi, (eqA_iff (rep_powN hrt 9) (rep_v0A hc h hi).2.1).2 he⟩
  rw [hn', h9', Bool.and_true, Bool.not_true, Bool.false_or] at h20
  exact mem_of_inLN (v0Parts h).k36 h20 hrt

theorem k36_le_normalizer : k36 ≤ normalizer (v0Grp : Set (Equiv.Perm (Fin 64))) := by
  refine grpN_le fun a ha => ?_
  simp only [k36Gens, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  have hsub : ∀ {x : Equiv.Perm (Fin 64)}, (∀ i < 4, x * v0P i * x⁻¹ ∈ v0Grp) →
      x ∈ normalizer (v0Grp : Set (Equiv.Perm (Fin 64))) := fun {x} hx =>
    mem_normalizer_of_map_conj_le' (by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨i, hi, rfl⟩ := (mem_v0Grp_iff hc h).1 hy
      exact hx i hi)
  rcases ha with ha | rfl | rfl
  · have hx : permOfArr 64 a ∈ v0Grp := gen_mem_grpN ha
    exact Subgroup.le_normalizer hx
  · refine hsub fun i hi => ?_
    show omegaP * v0P i * omegaP⁻¹ ∈ v0Grp
    rw [omegaP_comm_v0P hc h hi, mul_inv_cancel_right]
    exact (mem_v0Grp_iff hc h).2 ⟨i, hi, rfl⟩
  · refine hsub fun i hi => ?_
    show muP * v0P i * muP⁻¹ ∈ v0Grp
    rw [muP_conj_v0P hc h hi]
    exact (mem_v0Grp_iff hc h).2 ⟨_, muPi_lt h hi, rfl⟩

end V0

theorem v0A_get_lt : ∀ m < 4, ∀ k < 64, (v0A m)[k]! < 64 := by decide +kernel

theorem omuA_get_lt' : ∀ a < 3, ∀ b < 3, ∀ k < 64, (omuA a b)[k]! < 64 := by decide +kernel

theorem muPiN_lt : ∀ b < 3, ∀ m < 4, muPiN b m < 4 := by decide +kernel

theorem exists_ker : ∀ s1 ∈ f3Pairs, ∀ s2 ∈ f3Pairs, (s1.1 * s2.2 + 2 * (s1.2 * s2.1)) % 3 = 0 →
    ∃ c ∈ f3Pairs, c ≠ (0, 0) ∧ sigN s1 s2 c = (0, 0) := by decide +kernel

theorem omuA_mod (a b : ℕ) : omuA a b = omuA (a % 3) (b % 3) := by
  simp only [omuA, Nat.mod_mod]

theorem omuA_get_lt (a b : ℕ) {k : ℕ} (hk : k < 64) : (omuA a b)[k]! < 64 := by
  rw [omuA_mod]
  exact omuA_get_lt' _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num)) k hk

theorem smTau_mod (a b i : ℕ) : smTau a b i = smTau (a % 3) (b % 3) i := by
  simp only [smTau, Nat.mod_mod, ← omuA_mod]

theorem smStar_lt {i j : ℕ} (hi : i < 256) (hj : j < 256) : smStar i j < 256 := by
  have h1 : (v0A (i / 64))[j % 64]! < 64 := v0A_get_lt _ (by omega) _ (Nat.mod_lt _ (by norm_num))
  have h2 : (i % 64) ^^^ (v0A (i / 64))[j % 64]! < 64 :=
    Nat.xor_lt_two_pow (n := 6) (Nat.mod_lt _ (by norm_num)) h1
  have h3 : (i / 64) ^^^ (j / 64) < 4 := Nat.xor_lt_two_pow (n := 2) (by omega) (by omega)
  unfold smStar
  omega

theorem smTau_lt (a b : ℕ) {i : ℕ} (hi : i < 256) : smTau a b i < 256 := by
  have h1 := omuA_get_lt a b (Nat.mod_lt i (by norm_num : 0 < 64))
  have h2 : muPiN (b % 3) (i / 64) < 4 := muPiN_lt _ (Nat.mod_lt _ (by norm_num)) _ (by omega)
  unfold smTau
  omega

@[expose] def smStarF (i j : Fin 256) : Fin 256 := ⟨smStar i j, smStar_lt i.2 j.2⟩

@[expose] def smTauF (a b : ℕ) (i : Fin 256) : Fin 256 := ⟨smTau a b i, smTau_lt a b i.2⟩

theorem smComp_lt {s1 s2 d : ℕ × ℕ} {y : ℕ} (hy : y < 256) (code : ℕ) :
    smComp s1 s2 d y code < 256 := by
  unfold smComp
  split_ifs
  · norm_num
  · exact smTau_lt _ _ hy

section SM

variable (h : step44Check = true)
include h

theorem smTau_mul {c c' : ℕ × ℕ} (hc : c ∈ f3Pairs) (hc' : c' ∈ f3Pairs) {i : ℕ} (hi : i < 256) :
    smTau c.1 c.2 (smTau c'.1 c'.2 i) = smTau (c.1 + c'.1) (c.2 + c'.2) i := by
  have := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 (smParts h).tauMul c hc) c'
    hc') i (List.mem_range.2 hi)
  rwa [beq_iff_eq] at this

omit h in
theorem mem_f3Pairs {a b : ℕ} (ha : a < 3) (hb : b < 3) : (a, b) ∈ f3Pairs := by
  unfold f3Pairs
  simp only [List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨a, ha, b, hb, rfl⟩

theorem smTau_comp (a b a' b' : ℕ) {i : ℕ} (hi : i < 256) :
    smTau a b (smTau a' b' i) = smTau (a + a') (b + b') i := by
  rw [smTau_mod a b, smTau_mod a' b',
    smTau_mul h (c := (a % 3, b % 3)) (c' := (a' % 3, b' % 3))
      (mem_f3Pairs (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)))
      (mem_f3Pairs (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))) hi,
    smTau_mod (a + a'), smTau_mod (a % 3 + a' % 3)]
  congr 1
  · omega
  · omega

omit h in
theorem smTau_zero (i : ℕ) : smTau 0 0 i = i := by
  have h1 : (omuA 0 0)[i % 64]! = i % 64 := by
    have hk : i % 64 < 64 := Nat.mod_lt _ (by norm_num)
    simp only [omuA, powN, mulN]
    rw [compA_get hk, idA_get hk, idA_get hk]
  unfold smTau
  rw [h1]
  simp only [muPiN]
  omega

theorem aut_tau {φ : Fin 256 → Fin 256} {s1 s2 : ℕ × ℕ}
    (hτ1 : ∀ i, φ (smTauF 1 0 i) = smTauF s1.1 s1.2 (φ i))
    (hτ2 : ∀ i, φ (smTauF 0 1 i) = smTauF s2.1 s2.2 (φ i)) (a b : ℕ) (i : Fin 256) :
    φ (smTauF a b i) = smTauF (sigN s1 s2 (a, b)).1 (sigN s1 s2 (a, b)).2 (φ i) := by
  have hF : ∀ (x y x' y' : ℕ) (j : Fin 256),
      smTauF x y (smTauF x' y' j) = smTauF (x + x') (y + y') j := fun x y x' y' j =>
    Fin.ext (smTau_comp h x y x' y' j.2)
  have key : ∀ (x y x' y' : ℕ) (j : Fin 256), x % 3 = x' % 3 → y % 3 = y' % 3 →
      smTauF x y j = smTauF x' y' j := fun x y x' y' j hx hy =>
    Fin.ext (show smTau x y j = smTau x' y' j by rw [smTau_mod x, smTau_mod x', hx, hy])
  have h0 : ∀ j : Fin 256, smTauF 0 0 j = j := fun j => Fin.ext (smTau_zero j)
  induction a with
  | zero =>
    induction b with
    | zero =>
      rw [h0, show sigN s1 s2 (0, 0) = (0, 0) by simp [sigN], h0]
    | succ b ih =>
      have e : smTauF 0 (b + 1) i = smTauF 0 1 (smTauF 0 b i) := by
        rw [hF]
        exact key _ _ _ _ _ rfl (by omega)
      rw [e, hτ2, ih, hF]
      refine key _ _ _ _ _ ?_ ?_
      · simp only [sigN]
        rw [show 0 * s1.1 + (b + 1) * s2.1 = (0 * s1.1 + b * s2.1) + s2.1 by ring]
        omega
      · simp only [sigN]
        rw [show 0 * s1.2 + (b + 1) * s2.2 = (0 * s1.2 + b * s2.2) + s2.2 by ring]
        omega
  | succ a ih =>
    have e : smTauF (a + 1) b i = smTauF 1 0 (smTauF a b i) := by
      rw [hF]
      exact key _ _ _ _ _ (by omega) (by omega)
    rw [e, hτ1, ih, hF]
    refine key _ _ _ _ _ ?_ ?_
    · simp only [sigN]
      rw [show (a + 1) * s1.1 + b * s2.1 = (a * s1.1 + b * s2.1) + s1.1 by ring]
      omega
    · simp only [sigN]
      rw [show (a + 1) * s1.2 + b * s2.2 = (a * s1.2 + b * s2.2) + s1.2 by ring]
      omega

omit h in
theorem smStar_zero : smStar 0 0 = 0 := by decide

omit h in
theorem eq_zero_of_smStar_self : ∀ x < 256, smStar x x = x → x = 0 := by decide +kernel

omit h in
theorem sigN_mod (s1 s2 : ℕ × ℕ) (a b : ℕ) : sigN s1 s2 (a % 3, b % 3) = sigN s1 s2 (a, b) := by
  simp only [sigN, Prod.mk.injEq]
  constructor
  · simp [Nat.add_mod, Nat.mul_mod]
  · simp [Nat.add_mod, Nat.mul_mod]

omit h in
theorem sigN_one_zero (c : ℕ × ℕ) : sigN (1, 0) (0, 1) c = (c.1 % 3, c.2 % 3) := by
  simp [sigN]

theorem mem_hexaN_of_aut {φ : Equiv.Perm (Fin 256)}
    (hmul : ∀ i j, φ (smStarF i j) = smStarF (φ i) (φ j)) {s1 s2 : ℕ × ℕ}
    (hτ1 : ∀ i, φ (smTauF 1 0 i) = smTauF s1.1 s1.2 (φ i))
    (hτ2 : ∀ i, φ (smTauF 0 1 i) = smTauF s2.1 s2.2 (φ i)) : φ ∈ grpN 256 hexaNGens := by
  set r1 : ℕ × ℕ := (s1.1 % 3, s1.2 % 3) with hr1d
  set r2 : ℕ × ℕ := (s2.1 % 3, s2.2 % 3) with hr2d
  have hτ1' : ∀ i, φ (smTauF 1 0 i) = smTauF r1.1 r1.2 (φ i) := fun i => by
    rw [hτ1]
    exact Fin.ext (smTau_mod _ _ _)
  have hτ2' : ∀ i, φ (smTauF 0 1 i) = smTauF r2.1 r2.2 (φ i) := fun i => by
    rw [hτ2]
    exact Fin.ext (smTau_mod _ _ _)
  have hr1 : r1 ∈ f3Pairs := mem_f3Pairs (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
  have hr2 : r2 ∈ f3Pairs := mem_f3Pairs (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
  have hσ := aut_tau h hτ1' hτ2'
  have hφ0 : φ 0 = 0 := by
    have h1 := hmul 0 0
    have h00 : smStarF 0 0 = 0 := Fin.ext smStar_zero
    rw [h00] at h1
    exact Fin.ext (eq_zero_of_smStar_self _ (φ 0).2 (congrArg Fin.val h1).symm)
  have hdet : (r1.1 * r2.2 + 2 * (r1.2 * r2.1)) % 3 ≠ 0 := by
    intro hd
    obtain ⟨c, hc, hc0, hck⟩ := exists_ker r1 hr1 r2 hr2 hd
    have hfix : ∀ i : Fin 256, smTauF c.1 c.2 i = i := fun i => φ.injective (by
      rw [hσ, hck]
      exact Fin.ext (smTau_zero _))
    have hne := List.all_eq_true.1 (smParts h).tauNe c hc
    rw [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hne
    rcases hne with hne | ⟨i, hi, hne⟩
    · exact hc0 hne
    · have hi' := List.mem_range.1 hi
      rw [bne_iff_ne] at hne
      exact hne (congrArg Fin.val (hfix ⟨i, hi'⟩))
  have hsig : (r1, r2) ∈ smSigmas := by
    unfold smSigmas
    rw [List.mem_flatMap]
    refine ⟨r1, hr1, ?_⟩
    rw [List.mem_filterMap]
    refine ⟨r2, hr2, ?_⟩
    have : ((r1.1 * r2.2 + 2 * (r1.2 * r2.1)) % 3 == 0) = false := by
      rw [beq_eq_false_iff_ne]
      exact hdet
    rw [this]
    rfl
  have hfixed : ∀ (k : ℕ × ℕ) (g : Fin 256), g ≠ 0 → smTau k.1 k.2 g = g →
      (φ g).val ∈ smFix r1 r2 k := by
    intro k g hg0 hgk
    refine List.mem_filter.2 ⟨List.mem_range.2 (φ g).2, ?_⟩
    rw [Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
    refine ⟨fun h0 => hg0 (φ.injective (Fin.ext (by rw [h0, hφ0]; rfl))), ?_⟩
    have := hσ k.1 k.2 g
    rw [show smTauF k.1 k.2 g = g from Fin.ext hgk] at this
    exact (congrArg Fin.val this).symm
  have hy0 := hfixed (1, 0) 64 (by decide) (smParts h).g0
  have hy1 := hfixed (0, 1) 30 (by decide) (smParts h).g1
  have hy2 := hfixed (1, 1) 4 (by decide) (smParts h).g2
  have hy3 := hfixed (1, 2) 1 (by decide) (smParts h).g3
  let φN : ℕ → ℕ := fun i => if hi : i < 256 then (φ ⟨i, hi⟩).val else 0
  have hφN : ∀ x : Fin 256, φN x.val = (φ x).val := fun x => by simp [φN, x.2]
  have hmulN : ∀ {i j : ℕ}, i < 256 → j < 256 → φN (smStar i j) = smStar (φN i) (φN j) := by
    intro i j hi hj
    have e := congrArg Fin.val (hmul ⟨i, hi⟩ ⟨j, hj⟩)
    simp only [smStarF] at e
    simp only [φN, hi, hj, smStar_lt hi hj, ↓reduceDIte]
    exact e
  have hcompN : ∀ (d : ℕ × ℕ) {g : ℕ}, g < 256 → ∀ code : ℕ,
      φN (smComp (1, 0) (0, 1) d g code) = smComp r1 r2 d (φN g) code := by
    intro d g hg code
    by_cases hc0 : code = 0
    · simp only [smComp, hc0, ite_true]
      rw [show φN 0 = 0 from (hφN 0).trans (congrArg Fin.val hφ0)]
    · have e : smComp (1, 0) (0, 1) d g code =
          smTau (((code - 1) * d.1) % 3) (((code - 1) * d.2) % 3) g := by
        simp only [smComp, hc0, ite_false, sigN_one_zero]
      have e2 := congrArg Fin.val (hσ (((code - 1) * d.1) % 3) (((code - 1) * d.2) % 3) ⟨g, hg⟩)
      simp only [smTauF] at e2
      rw [e, hφN ⟨_, smTau_lt _ _ hg⟩, e2, sigN_mod, ← hφN ⟨g, hg⟩]
      simp only [smComp, hc0, ite_false]
  have hnf := (smParts h).nf
  have hrep : Rep 256 (smCand r1 r2 (φN 64) (φN 30) (φN 4) (φN 1)) φ := fun x => by
    have hx := allLt_spec hnf x.2
    rw [beq_iff_eq, idA_get x.2, smCand, getElem!_ofFn_nat _ x.2] at hx
    rw [smCand, getElem!_ofFn_nat _ x.2, ← hφN x]
    change smCandAt (1, 0) (0, 1) 64 30 4 1 x.val = x.val at hx
    change smCandAt r1 r2 (φN 64) (φN 30) (φN 4) (φN 1) x.val = φN x.val
    conv_rhs => rw [← hx]
    unfold smCandAt
    have l0 := smComp_lt (s1 := (1, 0)) (s2 := (0, 1)) (d := (0, 1)) (y := 64) (by norm_num)
      hexaNF[4 * x.val]!
    have l1 := smComp_lt (s1 := (1, 0)) (s2 := (0, 1)) (d := (1, 0)) (y := 30) (by norm_num)
      hexaNF[4 * x.val + 1]!
    have l2 := smComp_lt (s1 := (1, 0)) (s2 := (0, 1)) (d := (0, 1)) (y := 4) (by norm_num)
      hexaNF[4 * x.val + 2]!
    have l3 := smComp_lt (s1 := (1, 0)) (s2 := (0, 1)) (d := (0, 1)) (y := 1) (by norm_num)
      hexaNF[4 * x.val + 3]!
    rw [hmulN (smStar_lt (smStar_lt l0 l1) l2) l3, hmulN (smStar_lt l0 l1) l2, hmulN l0 l1,
      hcompN _ (by norm_num), hcompN _ (by norm_num), hcompN _ (by norm_num),
      hcompN _ (by norm_num)]
  have hy0 : φN 64 ∈ smFix r1 r2 (1, 0) := hφN 64 ▸ hy0
  have hy1 : φN 30 ∈ smFix r1 r2 (0, 1) := hφN 30 ▸ hy1
  have hy2 : φN 4 ∈ smFix r1 r2 (1, 1) := hφN 4 ▸ hy2
  have hy3 : φN 1 ∈ smFix r1 r2 (1, 2) := hφN 1 ▸ hy3
  have hhom : smHomA (smCand r1 r2 (φN 64) (φN 30) (φN 4) (φN 1)) = true := by
    unfold smHomA
    refine List.all_eq_true.2 fun i hi => List.all_eq_true.2 fun j hj => ?_
    have hi' := List.mem_range.1 hi
    have hj' := List.mem_range.1 hj
    rw [beq_iff_eq, hrep.apply (smStar_lt hi' hj'), hrep.apply hi', hrep.apply hj']
    exact congrArg Fin.val (hmul ⟨i, hi'⟩ ⟨j, hj'⟩)
  have hall := (smParts h).aut
  unfold smAutN at hall
  have h1 := List.all_eq_true.1 hall (r1, r2) hsig
  have h2 := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1
    (List.all_eq_true.1 h1 _ hy0) _ hy1) _ hy2) _ hy3
  rw [hhom, Bool.not_true, Bool.false_or] at h2
  exact mem_of_inLN (smParts h).n72 h2 hrep

end SM

section Graph

open CFSG.Sporadic.HeldB
open scoped Pointwise

theorem injective_of_card_range' {G K : Type*} [Group G] [Group K] [Finite G] (f : G →* K)
    (h : Nat.card f.range = Nat.card G) : Function.Injective f := by
  have hk := Subgroup.card_ker_mul_card_range f
  rw [h] at hk
  have hpos : 0 < Nat.card G := Nat.card_pos
  have h1 : Nat.card f.ker = 1 := by
    have : Nat.card f.ker * Nat.card G = 1 * Nat.card G := by rw [hk, one_mul]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Subgroup.card_eq_one.1 h1

theorem pairA_get_left {n₁ : ℕ} {a b : Array ℕ} (ha : a.size = n₁) {x : ℕ} (hx : x < n₁) :
    (pairA n₁ a b)[x]! = a[x]! := by
  unfold pairA
  have hx' : x < (a ++ b.map (· + n₁)).size := by simp; omega
  rw [getElem!_pos _ x hx', getElem!_pos a x (by omega), Array.getElem_append_left]

theorem pairA_get_right {n₁ n₂ : ℕ} {a b : Array ℕ} (ha : a.size = n₁) (hb : b.size = n₂) {y : ℕ}
    (hy : y < n₂) : (pairA n₁ a b)[n₁ + y]! = b[y]! + n₁ := by
  unfold pairA
  have hy' : n₁ + y < (a ++ b.map (· + n₁)).size := by simp; omega
  rw [getElem!_pos _ (n₁ + y) hy', getElem!_pos b y (by omega),
    Array.getElem_append_right (by omega)]
  simp [ha]

theorem nonempty_mulEquiv_of_graph {n₁ n₂ N : ℕ} {gs₁ gs₂ : List (Array ℕ)}
    (h1 : enumCheckN n₁ gs₁ N = true) (h2 : enumCheckN n₂ gs₂ N = true)
    (hlen : gs₁.length = gs₂.length) (hs1 : gs₁.all (·.size == n₁) = true)
    (hs2 : gs₂.all (·.size == n₂) = true)
    (hg : enumCheckN (n₁ + n₂) (List.zipWith (pairA n₁) gs₁ gs₂) N = true) :
    Nonempty (↥(grpN n₁ gs₁) ≃* ↥(grpN n₂ gs₂)) := by
  classical
  set ps := List.zipWith (pairA n₁) gs₁ gs₂ with hps
  have hlenps : ps.length = gs₁.length := by rw [hps, List.length_zipWith, ← hlen, min_self]
  let δ₁ : Fin n₁ → Fin (n₁ + n₂) := Fin.castAdd n₂
  let δ₂ : Fin n₂ → Fin (n₁ + n₂) := Fin.natAdd n₁
  have hδ₁ : Function.Injective δ₁ := Fin.castAdd_injective n₁ n₂
  have hδ₂ : Function.Injective δ₂ := Fin.natAdd_injective n₂ n₁
  have hgen : ∀ k (hk : k < gs₁.length),
      (∀ x : Fin n₁, permOfArr (n₁ + n₂) (ps[k]'(hlenps ▸ hk)) (δ₁ x) =
        δ₁ (permOfArr n₁ gs₁[k] x)) ∧
      ∀ y : Fin n₂, permOfArr (n₁ + n₂) (ps[k]'(hlenps ▸ hk)) (δ₂ y) =
        δ₂ (permOfArr n₂ (gs₂[k]'(hlen ▸ hk)) y) := by
    intro k hk
    have hk2 : k < gs₂.length := hlen ▸ hk
    have hpk : ps[k]'(hlenps ▸ hk) = pairA n₁ gs₁[k] gs₂[k] := List.getElem_zipWith ..
    have hv := validA_of_mem hg (List.getElem_mem (hlenps ▸ hk))
    have hr := rep_of_validA hv
    have hra := rep_of_validA (validA_of_mem h1 (List.getElem_mem hk))
    have hrb := rep_of_validA (validA_of_mem h2 (List.getElem_mem hk2))
    have hsa : gs₁[k].size = n₁ := by
      have := List.all_eq_true.1 hs1 _ (List.getElem_mem hk)
      simpa using this
    have hsb : gs₂[k].size = n₂ := by
      have := List.all_eq_true.1 hs2 _ (List.getElem_mem hk2)
      simpa using this
    constructor
    · intro x
      apply Fin.ext
      have e1 := hr (δ₁ x)
      rw [hpk] at e1 ⊢
      simp only [δ₁, Fin.val_castAdd] at e1 ⊢
      rw [← e1, pairA_get_left hsa x.2, hra x]
    · intro y
      apply Fin.ext
      have e2 := hr (δ₂ y)
      rw [hpk] at e2 ⊢
      simp only [δ₂, Fin.val_natAdd] at e2 ⊢
      rw [← e2, pairA_get_right hsa hsb y.2, hrb y]
      omega
  have hΓ₁ : grpN (n₁ + n₂) ps ≤ MulAction.stabilizer (Equiv.Perm (Fin (n₁ + n₂))) (Set.range δ₁) :=
    grpN_le fun a ha => by
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
      exact mem_stabilizer_of_agree (hgen k (hlenps ▸ hk)).1
  have hΓ₂ : grpN (n₁ + n₂) ps ≤ MulAction.stabilizer (Equiv.Perm (Fin (n₁ + n₂))) (Set.range δ₂) :=
    grpN_le fun a ha => by
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
      exact mem_stabilizer_of_agree (hgen k (hlenps ▸ hk)).2
  let π₁ := restrictHom hδ₁ (grpN (n₁ + n₂) ps) hΓ₁
  let π₂ := restrictHom hδ₂ (grpN (n₁ + n₂) ps) hΓ₂
  have hle₁ : grpN n₁ gs₁ ≤ π₁.range := grpN_le fun a ha => by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
    exact ⟨⟨_, gen_mem_grpN (List.getElem_mem (hlenps ▸ hk))⟩,
      restrictHom_eq_of_agree hδ₁ hΓ₁ _ (hgen k hk).1⟩
  have hle₂ : grpN n₂ gs₂ ≤ π₂.range := grpN_le fun a ha => by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
    have hk1 : k < gs₁.length := hlen ▸ hk
    exact ⟨⟨_, gen_mem_grpN (List.getElem_mem (hlenps ▸ hk1))⟩,
      restrictHom_eq_of_agree hδ₂ hΓ₂ _ (hgen k hk1).2⟩
  have hcΓ := card_grpN hg
  have hc₁ : Nat.card π₁.range = N := le_antisymm
    (hcΓ ▸ Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective π₁))
    (card_grpN h1 ▸ Subgroup.card_le_of_le hle₁)
  have hc₂ : Nat.card π₂.range = N := le_antisymm
    (hcΓ ▸ Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective π₂))
    (card_grpN h2 ▸ Subgroup.card_le_of_le hle₂)
  have hinj₁ := injective_of_card_range' π₁ (by rw [hc₁, hcΓ])
  have hinj₂ := injective_of_card_range' π₂ (by rw [hc₂, hcΓ])
  have heq₁ : grpN n₁ gs₁ = π₁.range :=
    Subgroup.eq_of_le_of_card_ge hle₁ (by rw [hc₁, card_grpN h1])
  have heq₂ : grpN n₂ gs₂ = π₂.range :=
    Subgroup.eq_of_le_of_card_ge hle₂ (by rw [hc₂, card_grpN h2])
  exact ⟨(MulEquiv.subgroupCongr heq₁).trans ((MonoidHom.ofInjective hinj₁).symm.trans
    ((MonoidHom.ofInjective hinj₂).trans (MulEquiv.subgroupCongr heq₂.symm)))⟩

end Graph

noncomputable abbrev hexaN : Subgroup (Equiv.Perm (Fin 256)) := grpN 256 hexaNGens

noncomputable abbrev hexaNE : Subgroup (Equiv.Perm (Fin 256)) := grpN 256 hexaNEGens

noncomputable abbrev hexaP : Subgroup (Equiv.Perm (Fin 256)) := grpN 256 hexaPGens

noncomputable abbrev hexaPE : Subgroup (Equiv.Perm (Fin 256)) := grpN 256 hexaPEGens

noncomputable abbrev smLamGrp : Subgroup (Equiv.Perm (Fin 256)) := grpN 256 smLamGens

noncomputable abbrev hexaAb : Subgroup (Equiv.Perm (Fin 256)) := grpN 256 (smLamGens ++ hexaPGens)

noncomputable abbrev hexaAa : Subgroup (Equiv.Perm (Fin 256)) := grpN 256 (smLamGens ++ hexaPEGens)

@[expose] def smAut : Subgroup (Equiv.Perm (Fin 256)) where
  carrier := {φ | ∀ i j, φ (smStarF i j) = smStarF (φ i) (φ j)}
  mul_mem' {φ ψ} hφ hψ i j := by
    simp only [Set.mem_ofPred_eq, Equiv.Perm.mul_apply] at hφ hψ ⊢
    rw [hψ, hφ]
  one_mem' i j := rfl
  inv_mem' {φ} hφ i j := by
    simp only [Set.mem_ofPred_eq] at hφ ⊢
    apply φ.injective
    rw [hφ]
    show φ (φ.symm (smStarF i j)) = smStarF (φ (φ.symm i)) (φ (φ.symm j))
    simp only [Equiv.apply_symm_apply]

theorem grpN_append {n : ℕ} (A B : List (Array ℕ)) : grpN n (A ++ B) = grpN n A ⊔ grpN n B := by
  apply le_antisymm
  · refine grpN_le fun a ha => ?_
    rcases List.mem_append.1 ha with ha | ha
    · exact mem_sup_left (gen_mem_grpN ha)
    · exact mem_sup_right (gen_mem_grpN ha)
  · exact sup_le (grpN_le fun a ha => gen_mem_grpN (List.mem_append_left _ ha))
      (grpN_le fun a ha => gen_mem_grpN (List.mem_append_right _ ha))

section Groups

variable (h : step44Check = true)
include h

theorem card_hexaN : Nat.card hexaN = 72 := card_grpN (smParts h).n72

theorem card_hexaNE : Nat.card hexaNE = 36 := card_grpN (smParts h).ne36

theorem card_hexaP : Nat.card hexaP = 8 := card_grpN (smParts h).p8

theorem card_hexaPE : Nat.card hexaPE = 4 := card_grpN (smParts h).pe4

theorem card_smLamGrp : Nat.card smLamGrp = 256 := card_grpN (smParts h).lam

omit h in
theorem mem_smAut_of {gs : List (Array ℕ)} {N : ℕ} (hg : enumCheckN 256 gs N = true)
    {a : Array ℕ} (ha : a ∈ gs) (hh : smHomA a = true) : permOfArr 256 a ∈ smAut := by
  have hr := rep_of_validA (validA_of_mem hg ha)
  intro i j
  apply Fin.ext
  have := List.all_eq_true.1 (List.all_eq_true.1 hh i.val (List.mem_range.2 i.2)) j.val
    (List.mem_range.2 j.2)
  rw [beq_iff_eq] at this
  have e1 := hr (smStarF i j)
  have e2 := hr i
  have e3 := hr j
  simp only [smStarF] at e1 ⊢
  rw [← e1, this, e2, e3]

theorem hexaN_le_smAut : hexaN ≤ smAut :=
  grpN_le fun a ha => mem_smAut_of (smParts h).n72 ha
    (List.all_eq_true.1 (smParts h).nHom a ha)

theorem hexaNE_le_hexaN : hexaNE ≤ hexaN :=
  grpN_le_of_all (smParts h).n72 (smParts h).ne36 (smParts h).neN

theorem hexaP_le_hexaN : hexaP ≤ hexaN :=
  grpN_le_of_all (smParts h).n72 (smParts h).p8 (smParts h).pN

theorem hexaPE_le_hexaNE : hexaPE ≤ hexaNE :=
  grpN_le_of_all (smParts h).ne36 (smParts h).pe4 (smParts h).peNE

theorem mem_hexaNE_of {β : Equiv.Perm (Fin 256)} (hβ : β ∈ hexaN)
    (hT : ∀ i : Fin 256, i.val < 64 → (β i).val < 64) : β ∈ hexaNE := by
  obtain ⟨t, ht, hrt⟩ := (mem_grpN_iff (smParts h).n72).1 hβ
  have hc := List.all_eq_true.1 (smParts h).nE t ht
  have hp : presTA t = true := List.all_eq_true.2 fun i hi => by
    have hi' := List.mem_range.1 hi
    rw [decide_eq_true_eq, hrt.apply (by omega : i < 256)]
    exact hT ⟨i, by omega⟩ hi'
  rw [hp, Bool.not_true, Bool.false_or] at hc
  exact mem_of_inLN (smParts h).ne36 hc hrt

omit h in
theorem hexaAb_eq : hexaAb = smLamGrp ⊔ hexaP := grpN_append _ _

omit h in
theorem hexaAa_eq : hexaAa = smLamGrp ⊔ hexaPE := grpN_append _ _

theorem smLamGens_get {a : Array ℕ} (ha : a ∈ smLamGens) :
    ∃ x < 256, ∀ i : Fin 256, (permOfArr 256 a i).val = smStar x i.val := by
  have hr := rep_of_validA (validA_of_mem (smParts h).lam ha)
  unfold smLamGens at ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  refine ⟨x, ?_, fun i => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    omega
  · rw [← hr.apply i.2, smLamA, getElem!_ofFn_nat _ i.2]

theorem hexaAbImgs_eq_Y32 : grpN 32 hexaAbImgs = Y32 := by
  have hle : Y32 ≤ grpN 32 hexaAbImgs := grpN_le fun a ha =>
    mem_of_inLN (smParts h).abY (List.all_eq_true.1 (smParts h).abGens a ha)
      (rep_of_validA (validA_of_mem (smParts h).y32 ha))
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_grpN (smParts h).abY,
    card_grpN (smParts h).y32])).symm

theorem hexaAaImgs_eq_X16 : grpN 16 hexaAaImgs = X16 := by
  have hle : X16 ≤ grpN 16 hexaAaImgs := grpN_le fun a ha =>
    mem_of_inLN (smParts h).aaX (List.all_eq_true.1 (smParts h).aaGens a ha)
      (rep_of_validA (validA_of_mem (smParts h).x16 ha))
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_grpN (smParts h).aaX,
    card_grpN (smParts h).x16])).symm

theorem nonempty_hexaAb_equiv : Nonempty (↥hexaAb ≃* ↥Y32) := by
  have hlen : (smLamGens ++ hexaPGens).length = hexaAbImgs.length := by
    rw [(smParts h).abLen]
    rfl
  obtain ⟨e⟩ := nonempty_mulEquiv_of_graph (smParts h).ab (smParts h).abY hlen (smParts h).abSize
    (smParts h).abImgSize (smParts h).abGraph
  exact ⟨e.trans (MulEquiv.subgroupCongr (hexaAbImgs_eq_Y32 h))⟩

theorem nonempty_hexaAa_equiv : Nonempty (↥hexaAa ≃* ↥X16) := by
  have hlen : (smLamGens ++ hexaPEGens).length = hexaAaImgs.length := by
    rw [(smParts h).aaLen]
    rfl
  obtain ⟨e⟩ := nonempty_mulEquiv_of_graph (smParts h).aa (smParts h).aaX hlen (smParts h).aaSize
    (smParts h).aaImgSize (smParts h).aaGraph
  exact ⟨e.trans (MulEquiv.subgroupCongr (hexaAaImgs_eq_X16 h))⟩

end Groups

end CFSG.ComponentClassification.AS81.Hexa
