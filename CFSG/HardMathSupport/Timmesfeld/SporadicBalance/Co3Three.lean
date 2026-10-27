module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.AbelianSylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OuterTrivial
public import Certificates.Certificate13635

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.Sporadic.Schreier.Co3 CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
  CFSG.Sporadic.Schreier.Co3.Native

section Checks

theorem qCheck_eq : qCheck () = true := Certificates.certificate13635.1

theorem dCheck_eq : dCheck () = true := Certificates.certificate13635.2.1

theorem hypCheck_eq : hypCheck () = true := Certificates.certificate13635.2.2.1

theorem fusCheck_eq : fusCheck () = true := Certificates.certificate13635.2.2.2.1

theorem transCheck_eq : transCheck () = true := Certificates.certificate13635.2.2.2.2.1

theorem cCheck_eq : cCheck () = true := Certificates.certificate13635.2.2.2.2.2.1

theorem classCheck_eq : classCheck () = true := Certificates.certificate13635.2.2.2.2.2.2

end Checks

theorem co3Chain_base_toList :
    co3Chain.base.toList = co3FinList 276 (by decide) co3ChainBase := by
  simp [co3Chain, RawSchreierDatum.ofArrays]

section Chain

theorem mem_co3P_of_inP {g : Array ℕ} {G : Equiv.Perm (Fin 276)} (hG : Rep 276 g G)
    (h : inP (levels ()) g = true) : G ∈ co3P :=
  (siftA_iff_mem_originalSubgroup co3ChainArrays (by norm_num) co3Order_check.1 hG).1 h

theorem eq_one_of_fixes_base {c : Equiv.Perm (Fin 276)} (hc : c ∈ co3P)
    (hfix : ∀ l : Fin 276, (l : ℕ) < 7 → c l = l) : c = 1 := by
  have hQ := co3Chain_valid.1
  have hmem : c ∈ co3Chain.levelSubgroup co3Chain.baseCount := by
    rw [co3Chain.mem_levelSubgroup_iff hQ _ le_rfl]
    refine ⟨hc, fun b hb => hfix b ?_⟩
    have hb' : b ∈ co3Chain.base.toList := List.mem_of_mem_take hb
    rw [co3Chain_base_toList] at hb'
    simp only [co3FinList, co3ChainBase, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rw [co3Chain.levelSubgroup_terminal_eq_bot hQ] at hmem
  exact Subgroup.mem_bot.1 hmem

end Chain

theorem keys_lt : ∀ q ∈ keys, q < 276 := by decide

@[expose] noncomputable def Qg : Subgroup (Equiv.Perm (Fin 276)) :=
  Subgroup.closure (permsA 276 (qGens ()))

theorem qGens_size : (qGens ()).size = 4 := by simp [qGens]

section Q

theorem qCheck_parts : enumOK 276 (qGens ()) keys (qCert ()) = true ∧
    (qCert ()).pts.size = 2187 ∧ ∀ k < 4, inP (levels ()) (qGens ())[k]! = true := by
  have h := qCheck_eq
  simp only [qCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, fun k hk => allLt_spec h3 hk⟩

theorem card_Qg : Nat.card Qg = 2187 :=
  (enumOK_spec keys_lt qCheck_parts.1).2.1.trans qCheck_parts.2.1

theorem Qg_le : Qg ≤ co3P := by
  rw [Qg, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact mem_co3P_of_inP (rep_of_validA (enumOK_gens_valid qCheck_parts.1 hk))
    (qCheck_parts.2.2 k (qGens_size ▸ hk))

end Q

theorem factorization_card_co3P_three :
    (Nat.card co3P).factorization 3 = 7 := by
  rw [card_co3P, show (495766656000 : ℕ) = 3 ^ 7 * 226688000 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

@[expose] def vec (k : ℕ) : Fin 5 → ZMod 3 := fun i => (digit3 k i : ZMod 3)

theorem vec_val (k : ℕ) (i : Fin 5) : (vec k i).val = digit3 k i := by
  rw [vec, ZMod.val_natCast]
  unfold digit3
  exact Nat.mod_mod _ _

@[expose] def idx (a : Fin 5 → ZMod 3) : ℕ :=
  (a 0).val + 3 * (a 1).val + 9 * (a 2).val + 27 * (a 3).val + 81 * (a 4).val

theorem idx_lt (a : Fin 5 → ZMod 3) : idx a < 243 := by
  have h0 := ZMod.val_lt (a 0)
  have h1 := ZMod.val_lt (a 1)
  have h2 := ZMod.val_lt (a 2)
  have h3 := ZMod.val_lt (a 3)
  have h4 := ZMod.val_lt (a 4)
  unfold idx
  omega

theorem digit3_idx (a : Fin 5 → ZMod 3) (i : Fin 5) : digit3 (idx a) i = (a i).val := by
  have h0 := ZMod.val_lt (a 0)
  have h1 := ZMod.val_lt (a 1)
  have h2 := ZMod.val_lt (a 2)
  have h3 := ZMod.val_lt (a 3)
  have h4 := ZMod.val_lt (a 4)
  fin_cases i <;> simp only [digit3, idx, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    pow_zero, pow_one, Nat.reducePow, Nat.div_one] <;> omega

theorem vec_idx (a : Fin 5 → ZMod 3) : vec (idx a) = a := by
  funext i
  rw [vec, digit3_idx, ZMod.natCast_zmod_val]

theorem idx_eq_zero_iff (a : Fin 5 → ZMod 3) : idx a = 0 ↔ a = 0 := by
  constructor
  · intro h
    rw [← vec_idx a, h]
    funext i
    simp [vec, digit3]
  · rintro rfl
    simp [idx]

@[expose] noncomputable def dPerm (i : Fin 5) : Equiv.Perm (Fin 276) :=
  permOfArr 276 (dGens ())[(i : ℕ)]!

section D

theorem dCheck_parts :
    (∀ i < 5, validA 276 (dGens ())[i]! = true ∧ inP (levels ()) (dGens ())[i]! = true ∧
      eqA 276 (powArr 276 (dGens ())[i]! 3) (idA 276) = true) ∧
    (∀ i < 5, ∀ j < 5, CFSG.RankThree.Native.commA 276 (dGens ())[i]! (dGens ())[j]! = true) ∧
    (∀ k < 243, ∀ k' < 243, k = k' ∨ eqA 276 (dElts ())[k]! (dElts ())[k']! = false) := by
  have h := dCheck_eq
  simp only [dCheck, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun i hi => ?_, fun i hi j hj => allLt_spec (allLt_spec h2 hi) hj,
    fun k hk k' hk' => ?_⟩
  · have := allLt_spec h1 hi
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have := allLt_spec (allLt_spec h3 hk) hk'
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
    exact this

theorem rep_dGen {i : ℕ} (hi : i < 5) : Rep 276 (dGens ())[i]! (dPerm ⟨i, hi⟩) :=
  rep_of_validA (dCheck_parts.1 i hi).1

theorem dPerm_pow (i : Fin 5) : dPerm i ^ 3 = 1 :=
  (eqA_iff (rep_powArr (rep_dGen i.2) 3) rep_idA).1 (dCheck_parts.1 i i.2).2.2

theorem dPerm_comm (i j : Fin 5) : Commute (dPerm i) (dPerm j) :=
  (CFSG.RankThree.Native.commA_iff (rep_dGen i.2) (rep_dGen j.2)).1
    (dCheck_parts.2.1 i i.2 j j.2)

theorem dPerm_mem (i : Fin 5) :
    dPerm i ∈ co3P :=
  mem_co3P_of_inP (rep_dGen i.2) (dCheck_parts.1 i i.2).2.1

@[expose] noncomputable def φ : Multiplicative (Fin 5 → ZMod 3) →* Equiv.Perm (Fin 276) :=
  vecProdHom dPerm dPerm_comm dPerm_pow

theorem φ_apply (a : Fin 5 → ZMod 3) : φ (Multiplicative.ofAdd a) = vecProd dPerm a := rfl

theorem vecProd_eq (a : Fin 5 → ZMod 3) : vecProd dPerm a =
    dPerm 0 ^ (a 0).val * (dPerm 1 ^ (a 1).val * (dPerm 2 ^ (a 2).val *
      (dPerm 3 ^ (a 3).val * dPerm 4 ^ (a 4).val))) := by
  simp [vecProd, List.finRange_succ]

theorem rep_dElts {k : ℕ} (hk : k < 243) :
    Rep 276 (dElts ())[k]! (φ (Multiplicative.ofAdd (vec k))) := by
  rw [φ_apply, vecProd_eq]
  have he : (dElts ())[k]! = dProd (dGens ()) k := by
    rw [dElts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  rw [he, dProd]
  simp only [vec_val]
  exact rep_compA (rep_powArr (rep_dGen (by norm_num)) _) (rep_compA (rep_powArr
    (rep_dGen (by norm_num)) _) (rep_compA (rep_powArr (rep_dGen (by norm_num)) _)
      (rep_compA (rep_powArr (rep_dGen (by norm_num)) _) (rep_powArr (rep_dGen (by norm_num)) _))))

theorem φ_injective : Function.Injective φ := by
  intro a b hab
  have ha := rep_dElts (idx_lt a.toAdd)
  have hb := rep_dElts (idx_lt b.toAdd)
  rw [vec_idx, ofAdd_toAdd] at ha hb
  have heq : eqA 276 (dElts ())[idx a.toAdd]! (dElts ())[idx b.toAdd]! = true :=
    (eqA_iff ha hb).2 hab
  rcases dCheck_parts.2.2 (idx a.toAdd) (idx_lt _) (idx b.toAdd) (idx_lt _) with h | h
  · have := congrArg vec h
    rw [vec_idx, vec_idx] at this
    exact Multiplicative.toAdd.injective this
  · rw [h] at heq
    exact absurd heq Bool.false_ne_true

@[expose] noncomputable def Dg : Subgroup (Equiv.Perm (Fin 276)) := φ.range

theorem card_Dg : Nat.card Dg = 243 := by
  rw [Dg, MonoidHom.range_eq_map, Subgroup.card_map_of_injective φ_injective, Subgroup.card_top,
    card_vec]
  norm_num

theorem Dg_comm : ∀ x ∈ Dg, ∀ y ∈ Dg, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem Dg_pow_three : ∀ x ∈ Dg, x ^ 3 = 1 := by
  rintro _ ⟨a, rfl⟩
  rw [← map_pow]
  have : a ^ 3 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, show ((3 : ℕ) : ZMod 3) = 0 from rfl,
      zero_mul]
  rw [this, map_one]

theorem Dg_le : Dg ≤ co3P := by
  rintro _ ⟨a, rfl⟩
  change vecProd dPerm a.toAdd ∈ co3P
  rw [vecProd_eq]
  have h := dPerm_mem
  exact co3P.mul_mem (co3P.pow_mem (h 0) _) (co3P.mul_mem (co3P.pow_mem (h 1) _)
    (co3P.mul_mem (co3P.pow_mem (h 2) _) (co3P.mul_mem (co3P.pow_mem (h 3) _)
      (co3P.pow_mem (h 4) _))))

end D

theorem anyLt_true {n : ℕ} {p : ℕ → Bool} (h : anyLt n p = true) : ∃ i < n, p i = true := by
  unfold anyLt at h
  rw [Nat.any_eq_finRange_any, List.any_eq_true] at h
  obtain ⟨⟨i, hi⟩, -, h⟩ := h
  exact ⟨i, hi, h⟩

@[expose] def hypG : Array (Array Nat) := hypTuples.map (rebuild (levels ()))

@[expose] def hypC : Array (Array Nat) :=
  hypG.map fun g => Array.ofFn (n := 7) fun l => coordOf (dElts ()) g l.val

theorem dot3_eq_zero_iff (a : Fin 5 → ZMod 3) (k : ℕ) :
    dot3 (idx a) k = 0 ↔ ∑ i, a i * vec k i = 0 := by
  have hc : ∀ i : Fin 5, ((digit3 (idx a) i * digit3 k i : ℕ) : ZMod 3) = a i * vec k i := by
    intro i
    rw [Nat.cast_mul, digit3_idx, ZMod.natCast_zmod_val]
    rfl
  rw [Fin.sum_univ_five, ← hc 0, ← hc 1, ← hc 2, ← hc 3, ← hc 4]
  simp only [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
  unfold dot3
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  exact Nat.dvd_iff_mod_eq_zero.symm

section Hyp

theorem hypCheck_parts : hypG.size = 121 ∧
    (∀ j < 121, validA 276 hypG[j]! = true ∧ inP (levels ()) hypG[j]! = true ∧
      ∀ l < 7, (hypC[j]!)[l]! < 243 ∧
        ((dElts ())[(hypC[j]!)[l]!]!)[(hypG[j]!)[0]!]! = (hypG[j]!)[l]!) ∧
    (∀ m < 243, m = 0 ∨ ∃ j < 121, ∀ l < 7, dot3 m (hypC[j]!)[l]! = 0) := by
  have h : hypCheck () = true := hypCheck_eq
  unfold hypCheck at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨beq_iff_eq.1 h1, fun j hj => ?_, fun m hm => ?_⟩
  · have h4 := allLt_spec h2 hj
    rw [Bool.and_eq_true, Bool.and_eq_true] at h4
    refine ⟨h4.1.1, h4.1.2, fun l hl => ?_⟩
    have h5 := allLt_spec h4.2 hl
    rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h5
    exact h5
  · have h4 := allLt_spec h3 hm
    rw [Bool.or_eq_true, beq_iff_eq] at h4
    rcases h4 with h0 | h0
    · exact Or.inl h0
    · right
      obtain ⟨j, hj, hjl⟩ := anyLt_true h0
      refine ⟨j, hj, fun l hl => ?_⟩
      have h5 := allLt_spec hjl hl
      rw [beq_iff_eq] at h5
      exact h5

theorem centralizer_inf_eq_Dg {B : Subgroup (Equiv.Perm (Fin 276))} (hBD : B ≤ Dg)
    (hB : Nat.card B * 3 = 243) :
    Subgroup.centralizer (B : Set (Equiv.Perm (Fin 276))) ⊓ co3P = Dg := by
  obtain ⟨f, hf0, hf⟩ := exists_dot_eq_zero_imp_mem φ φ_injective hBD (by rw [hB]; norm_num)
  have hm0 : idx f ≠ 0 := fun h => hf0 ((idx_eq_zero_iff f).1 h)
  obtain ⟨-, hgj, hcov⟩ := hypCheck_parts
  obtain ⟨j, hj, hjl⟩ := (hcov (idx f) (idx_lt f)).resolve_left hm0
  obtain ⟨hgv, hgP, hgl⟩ := hgj j hj
  set g := permOfArr 276 hypG[j]! with hgdef
  have hg : Rep 276 hypG[j]! g := rep_of_validA hgv
  have hgmem : g ∈ co3P := mem_co3P_of_inP hg hgP
  have hy : ∀ l : Fin 276, (l : ℕ) < 7 → ∃ y ∈ B, y (g 0) = g l := by
    intro l hl
    obtain ⟨hk, hkeq⟩ := hgl l hl
    set k := (hypC[j]!)[(l : ℕ)]! with hkdef
    refine ⟨φ (Multiplicative.ofAdd (vec k)), hf _ ((dot3_eq_zero_iff f k).1 (hjl l hl)), ?_⟩
    have hrep := rep_dElts hk
    have hg0 : (hypG[j]!)[0]! = (g 0 : ℕ) := hg 0
    apply Fin.ext
    rw [← hrep (g 0), ← hg0, hkeq, hg l]
  have hinj : Function.Injective fun c : ↥(Subgroup.centralizer (B : Set (Equiv.Perm (Fin 276))) ⊓
      co3P) => (c : Equiv.Perm (Fin 276)) (g 0) := by
    intro c₁ c₂ hc
    have hc' : (c₁ : Equiv.Perm (Fin 276)) (g 0) = (c₂ : Equiv.Perm (Fin 276)) (g 0) := hc
    obtain ⟨hc₁B, hc₁P⟩ := Subgroup.mem_inf.1 c₁.2
    obtain ⟨hc₂B, hc₂P⟩ := Subgroup.mem_inf.1 c₂.2
    set e := g⁻¹ * (c₁ : Equiv.Perm (Fin 276))⁻¹ * c₂ * g with he
    have heP : e ∈ co3P :=
      co3P.mul_mem (co3P.mul_mem (co3P.mul_mem (co3P.inv_mem hgmem) (co3P.inv_mem hc₁P)) hc₂P)
        hgmem
    have hfix : ∀ l : Fin 276, (l : ℕ) < 7 → e l = l := by
      intro l hl
      obtain ⟨y, hyB, hyl⟩ := hy l hl
      have hcy₁ : (c₁ : Equiv.Perm (Fin 276)) * y = y * c₁ :=
        (Subgroup.mem_centralizer_iff.1 hc₁B y hyB).symm
      have hcy₂ : (c₂ : Equiv.Perm (Fin 276)) * y = y * c₂ :=
        (Subgroup.mem_centralizer_iff.1 hc₂B y hyB).symm
      have h1 : (c₂ : Equiv.Perm (Fin 276)) (g l) = (c₁ : Equiv.Perm (Fin 276)) (g l) := by
        rw [← hyl]
        have e1 := congrArg (fun σ : Equiv.Perm (Fin 276) => σ (g 0)) hcy₁
        have e2 := congrArg (fun σ : Equiv.Perm (Fin 276) => σ (g 0)) hcy₂
        simp only [Equiv.Perm.mul_apply] at e1 e2
        rw [e1, e2, hc']
      rw [he]
      simp only [Equiv.Perm.mul_apply, h1]
      simp
    have he1 := eq_one_of_fixes_base heP hfix
    apply Subtype.ext
    rw [he] at he1
    have : (c₁ : Equiv.Perm (Fin 276))⁻¹ * c₂ = 1 := by
      have h2 : g * (g⁻¹ * (c₁ : Equiv.Perm (Fin 276))⁻¹ * c₂ * g) * g⁻¹ = 1 := by
        rw [he1, mul_one, mul_inv_cancel]
      simpa [mul_assoc] using h2
    exact (inv_mul_eq_one.1 this)
  have hle : Nat.card ↥(Subgroup.centralizer (B : Set (Equiv.Perm (Fin 276))) ⊓ co3P) ≤ 276 := by
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_fin] at this
  have hDle : Dg ≤ Subgroup.centralizer (B : Set (Equiv.Perm (Fin 276))) ⊓ co3P := by
    intro x hx
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun b hb => ?_, Dg_le hx⟩
    exact Dg_comm b (hBD hb) x hx
  have hdvd := Subgroup.card_dvd_of_le hDle
  rw [card_Dg] at hdvd
  obtain ⟨t, ht⟩ := hdvd
  have hpos : 0 < Nat.card ↥(Subgroup.centralizer (B : Set (Equiv.Perm (Fin 276))) ⊓ co3P) :=
    Nat.card_pos
  have ht1 : t = 1 := by
    rw [ht] at hle hpos
    rcases t with _ | _ | t
    · omega
    · rfl
    · omega
  rw [ht1, mul_one] at ht
  exact (Subgroup.eq_of_le_of_card_ge hDle (by rw [ht, card_Dg])).symm

end Hyp

section DCore

theorem isPGroup_Dg : IsPGroup 3 ↥Dg := IsPGroup.of_card (n := 5) (by rw [card_Dg]; norm_num)

theorem isPGroup_centralizer_Dg :
    IsPGroup 3 ↥(Subgroup.centralizer (Dg : Set (Equiv.Perm (Fin 276))) ⊓ co3P) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nontrivial ↥Dg := Finite.one_lt_card_iff_nontrivial.1 (by rw [card_Dg]; norm_num)
  obtain ⟨B1, hB1⟩ := CFSG.SolvableHall.exists_index_eq_prime (p := 3) (A := ↥Dg) isPGroup_Dg
  set B' := B1.map Dg.subtype
  have hB'D : B' ≤ Dg := Subgroup.map_subtype_le B1
  have hcard : Nat.card B' * 3 = 243 := by
    rw [Subgroup.card_map_of_injective Dg.subtype_injective, ← hB1, B1.card_mul_index, card_Dg]
  have hC := centralizer_inf_eq_Dg hB'D hcard
  have hP : IsPGroup 3 ↥(Subgroup.centralizer (B' : Set (Equiv.Perm (Fin 276))) ⊓ co3P) := by
    rw [hC]
    exact isPGroup_Dg
  exact hP.to_le (inf_le_inf_right _ (Subgroup.centralizer_le hB'D))

@[expose] noncomputable def Tg : Subgroup ↥co3P := Dg.subgroupOf co3P

theorem card_Tg : Nat.card Tg = 243 := by
  rw [Tg, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Dg_le).toEquiv, card_Dg]

theorem Tg_elemAbelian : IsElemAbelian 3 Tg := by
  refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    exact Dg_comm _ (Subgroup.mem_subgroupOf.1 a.2) _ (Subgroup.mem_subgroupOf.1 b.2)
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact Dg_pow_three _ (Subgroup.mem_subgroupOf.1 hx)

theorem isPGroup_of_map_le {K : Subgroup ↥co3P} {X : Subgroup (Equiv.Perm (Fin 276))}
    (hX : IsPGroup 3 ↥X) (hK : ∀ c ∈ K, (c : Equiv.Perm (Fin 276)) ∈ X) : IsPGroup 3 ↥K :=
  (hX.comap_of_injective co3P.subtype co3P.subtype_injective).to_le fun c hc => hK c hc

theorem isPGroup_centralizer_of_index {B : Subgroup ↥co3P} (hBT : B ≤ Tg)
    (hidx : B.relIndex Tg = 3) : IsPGroup 3 ↥(Subgroup.centralizer (B : Set ↥co3P)) := by
  set B' := B.map co3P.subtype with hB'
  have hB'D : B' ≤ Dg := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hBT hx)
  have hcard : Nat.card B' * 3 = 243 := by
    rw [Subgroup.card_map_of_injective co3P.subtype_injective]
    have h := Subgroup.relIndex_mul_card B Tg
    rw [inf_eq_left.2 hBT, hidx, card_Tg] at h
    omega
  have hC := centralizer_inf_eq_Dg hB'D hcard
  have hP : IsPGroup 3 ↥(Subgroup.centralizer (B' : Set (Equiv.Perm (Fin 276))) ⊓ co3P) := by
    rw [hC]
    exact isPGroup_Dg
  refine isPGroup_of_map_le hP fun c hc => Subgroup.mem_inf.2 ⟨?_, c.2⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hc b hb)

theorem gLAPPrimeCoreOf_eq_bot_of_mem_Dg {s : ↥co3P} (hs : orderOf s = 3)
    (hsD : (s : Equiv.Perm (Fin 276)) ∈ Dg) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set ↥co3P)) = ⊥ := by
  refine gLAPPrimeCoreOf_eq_bot_of_elemAbelian Nat.prime_three Tg_elemAbelian
    (Subgroup.mem_subgroupOf.2 hsD) hs (fun B hBT hidx => gLAPPrimeCoreOf_eq_bot_of_isPGroup
      Nat.prime_three (isPGroup_centralizer_of_index hBT hidx)) ?_
  refine gLAPPrimeCoreOf_eq_bot_of_isPGroup Nat.prime_three
    (isPGroup_of_map_le isPGroup_centralizer_Dg fun c hc => Subgroup.mem_inf.2 ⟨?_, c.2⟩)
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hc ⟨d, Dg_le hd⟩
    (Subgroup.mem_subgroupOf.2 hd))

end DCore

@[expose] noncomputable def yPerm : Equiv.Perm (Fin 276) := permOfArr 276 (yArr ())

section Cy

theorem cCheck_parts : validA 276 (yArr ()) = true ∧ inP (levels ()) (yArr ()) = true ∧
    eqA 276 (powArr 276 (yArr ()) 3) (idA 276) = true ∧ eqA 276 (yArr ()) (idA 276) = false ∧
    centOKP 3 276 co3ChainArrs co3ChainBaseArr (yArr ()) yRels (cGens ()) keys (cCert ()) 4536 =
      true := by
  have h : cCheck () = true := cCheck_eq
  unfold cCheck at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem rep_y : Rep 276 (yArr ()) yPerm := rep_of_validA cCheck_parts.1

theorem yPerm_pow : yPerm ^ 3 = 1 :=
  (eqA_iff (rep_powArr rep_y 3) rep_idA).1 cCheck_parts.2.2.1

theorem yPerm_ne_one : yPerm ≠ 1 := fun h => by
  have := (eqA_iff rep_y rep_idA).2 h
  rw [cCheck_parts.2.2.2.1] at this
  exact Bool.false_ne_true this

theorem cEnum : enumOK 276 (cGens ()) keys (cCert ()) = true := centOKP_enum cCheck_parts.2.2.2.2

theorem classCheck_parts : ∀ i < (cCert ()).pts.size,
    eqA 276 (cCert ()).pts[i]! (idA 276) = true ∨
      (eqA 276 (powArr 276 (cCert ()).pts[i]! 2) (idA 276) = false ∧
        eqA 276 (powArr 276 (cCert ()).pts[i]! 7) (idA 276) = false) ∨
      commCount (cCert ()).pts (cCert ()).pts[i]! < 81 := by
  intro i hi
  have h : classCheck () = true := classCheck_eq
  unfold classCheck at h
  have h1 := allLt_spec h hi
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_true_eq] at h1
  rcases h1 with (h1 | h1) | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

theorem centralizer_y_sq : Subgroup.centralizer ({yPerm ^ 2} : Set (Equiv.Perm (Fin 276))) =
    Subgroup.centralizer {yPerm} := by
  apply le_antisymm
  · intro z hz
    have hz' : z * yPerm ^ 2 = yPerm ^ 2 * z := Subgroup.mem_centralizer_singleton_iff.1 hz
    have hy4 : yPerm = (yPerm ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, yPerm_pow, one_mul, pow_one]
    rw [Subgroup.mem_centralizer_singleton_iff, hy4]
    exact Commute.pow_right hz' 2
  · intro z hz
    have hz' : z * yPerm = yPerm * z := Subgroup.mem_centralizer_singleton_iff.1 hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Commute.pow_right hz' 2

theorem yPerm_mem : yPerm ∈ co3P := mem_co3P_of_inP rep_y cCheck_parts.2.1

theorem Cy_eq : Subgroup.closure (permsA 276 (cGens ())) = Subgroup.centralizer {yPerm} ⊓ co3P ∧
    Nat.card (Subgroup.closure (permsA 276 (cGens ()))) = 4536 :=
  centralizer_eq_of_centOKP co3ChainArrays (by norm_num) co3Order_check.1 rep_y keys_lt
    cCheck_parts.2.2.2.2

theorem gLAPPrimeCoreOf_Cy :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({yPerm} : Set (Equiv.Perm (Fin 276))) ⊓ co3P) = ⊥ := by
  obtain ⟨hCeq, hCcard⟩ := Cy_eq
  rw [← hCeq]
  refine gLAPPrimeCoreOf_eq_bot_of_classSize Nat.prime_three (a := 4) (r := 56)
    (by rw [hCcard]; norm_num) (by norm_num) ?_
  intro w hw hwp hwr
  rw [hCcard]
  obtain ⟨i, hi, hrep⟩ := enumOK_exists_rep keys_lt cEnum hw
  have hw1 : w ≠ 1 := fun h => by
    rw [h, orderOf_one] at hwp
    exact Nat.not_prime_one hwp
  have hw27 : w ^ 2 = 1 ∨ w ^ 7 = 1 := by
    have h56 : orderOf w ∣ 2 ^ 3 * 7 := hwr
    rcases (Nat.Prime.dvd_mul hwp).1 h56 with h | h
    · left
      rw [← (Nat.prime_dvd_prime_iff_eq hwp Nat.prime_two).1 (hwp.dvd_of_dvd_pow h)]
      exact pow_orderOf_eq_one w
    · right
      rw [← (Nat.prime_dvd_prime_iff_eq hwp (by norm_num)).1 h]
      exact pow_orderOf_eq_one w
  rcases classCheck_parts i hi with h | ⟨h2, h7⟩ | h
  · exact absurd ((eqA_iff hrep rep_idA).1 h) hw1
  · exfalso
    rcases hw27 with h' | h'
    · rw [(eqA_iff (rep_powArr hrep 2) rep_idA).2 h'] at h2
      exact absurd h2 (by decide)
    · rw [(eqA_iff (rep_powArr hrep 7) rep_idA).2 h'] at h7
      exact absurd h7 (by decide)
  · have hle := card_closure_inf_centralizer_le keys_lt cEnum hrep
    unfold commCount at h
    omega

theorem gLAPPrimeCoreOf_eq_bot_of_y {s : ↥co3P}
    (hs : (s : Equiv.Perm (Fin 276)) = yPerm ∨ (s : Equiv.Perm (Fin 276)) = yPerm ^ 2) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set ↥co3P)) = ⊥ := by
  have hcs : Subgroup.centralizer ({(s : Equiv.Perm (Fin 276))} : Set (Equiv.Perm (Fin 276))) =
      Subgroup.centralizer {yPerm} := by
    rcases hs with h | h
    · rw [h]
    · rw [h]
      exact centralizer_y_sq
  have hmap := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective 3
    co3P.subtype co3P.subtype_injective (Subgroup.centralizer ({s} : Set ↥co3P))
  have hc := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_inf_centralizer_of_injective
    co3P.subtype co3P.subtype_injective ⊤ s
  rw [top_inf_eq, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hc
  have hsub : co3P.subtype s = (s : Equiv.Perm (Fin 276)) := rfl
  rw [hc, hsub, hcs, inf_comm, gLAPPrimeCoreOf_Cy] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ co3P.subtype_injective).1 hmap

end Cy

theorem getElem!_lines {j : ℕ} (hj : j < 12) :
    (Array.ofFn (n := 12) fun j => lineArr j.val)[j]! = lineArr j := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem getElem!_lines2 {j : ℕ} (hj : j < 12) :
    ((Array.ofFn (n := 12) fun j => lineArr j.val).map fun x => compA 276 x x)[j]! =
      compA 276 (lineArr j) (lineArr j) := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, Array.getElem_ofFn]

section Fusion

theorem fusCheck_parts : ∀ k < 2187,
    eqA 276 (powArr 276 (qCert ()).pts[k]! 3) (idA 276) = false ∨
      eqA 276 (qCert ()).pts[k]! (idA 276) = true ∨ inD (dElts ()) (qCert ()).pts[k]! = true ∨
      ∃ u < 2187, ∃ j < 12,
        eqA 276 (conjA 276 (qCert ()).pts[u]! (qCert ()).pts[k]!) (lineArr j) = true ∨
        eqA 276 (conjA 276 (qCert ()).pts[u]! (qCert ()).pts[k]!)
          (compA 276 (lineArr j) (lineArr j)) = true := by
  intro k hk
  have h : fusCheck () = true := fusCheck_eq
  unfold fusCheck at h
  rw [Bool.and_eq_true] at h
  have h1 := allLt_spec h.2 hk
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1
  rcases h1 with ((h1 | h1) | h1) | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · right; right; right
    obtain ⟨u, hu, hj⟩ := anyLt_true h1
    obtain ⟨j, hj', hjj⟩ := anyLt_true hj
    rw [Bool.or_eq_true, getElem!_lines hj', getElem!_lines2 hj'] at hjj
    exact ⟨u, hu, j, hj', hjj⟩

theorem transCheck_parts : ∀ j < 12, validA 276 (transArr j) = true ∧
    validA 276 (lineArr j) = true ∧ inP (levels ()) (transArr j) = true ∧
    (inD (dElts ()) (conjA 276 (transArr j) (lineArr j)) = true ∨
      eqA 276 (conjA 276 (transArr j) (lineArr j)) (yArr ()) = true ∨
      eqA 276 (conjA 276 (transArr j) (lineArr j)) (compA 276 (yArr ()) (yArr ())) = true) := by
  intro j hj
  have h : transCheck () = true := transCheck_eq
  unfold transCheck at h
  have h1 := allLt_spec h hj
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h1
  obtain ⟨⟨⟨h2, h3⟩, h4⟩, h5⟩ := h1
  refine ⟨h2, h3, h4, ?_⟩
  split_ifs at h5
  · exact Or.inl h5
  · rw [Bool.or_eq_true] at h5
    exact Or.inr h5

theorem mem_Dg_of_inD {a : Array ℕ} {A : Equiv.Perm (Fin 276)} (ha : Rep 276 a A)
    (h : inD (dElts ()) a = true) : A ∈ Dg := by
  unfold inD at h
  obtain ⟨i, hi, hai⟩ := anyLt_true h
  rw [(eqA_iff ha (rep_dElts hi)).1 hai]
  exact ⟨_, rfl⟩

theorem exists_conj_D_or_y {x : Equiv.Perm (Fin 276)} (hx : x ∈ co3P) (hxo : orderOf x = 3) :
    ∃ h ∈ co3P, h * x * h⁻¹ ∈ Dg ∨ h * x * h⁻¹ = yPerm ∨ h * x * h⁻¹ = yPerm ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hgP, hgQ⟩ := exists_conj_mem_of_full Qg_le
    (by rw [card_Qg, factorization_card_co3P_three]; norm_num) hx hxo
  set t := g⁻¹ * x * g with htdef
  have hto : orderOf t = 3 := by
    have := (MulAut.conj g⁻¹ : Equiv.Perm (Fin 276) ≃* Equiv.Perm (Fin 276)).orderOf_eq x
    simpa [MulAut.conj_apply, htdef, hxo] using this
  have ht3 : t ^ 3 = 1 := hto ▸ pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at hto; omega
  obtain ⟨k, hk, hrep⟩ := enumOK_exists_rep keys_lt qCheck_parts.1 hgQ
  have hk' : k < 2187 := qCheck_parts.2.1 ▸ hk
  rcases fusCheck_parts k hk' with h | h | h | ⟨u, hu, j, hj, h⟩
  · rw [(eqA_iff (rep_powArr hrep 3) rep_idA).2 ht3] at h
    exact absurd h (by decide)
  · exact absurd ((eqA_iff hrep rep_idA).1 h) ht1
  · refine ⟨g⁻¹, co3P.inv_mem hgP, Or.inl ?_⟩
    rw [inv_inv]
    exact mem_Dg_of_inD hrep h
  · have hu' : u < (qCert ()).pts.size := qCheck_parts.2.1.symm ▸ hu
    have hUv := (enumOK_spec keys_lt qCheck_parts.1).2.2 u hu'
    set U := permOfArr 276 (qCert ()).pts[u]! with hUdef
    have hUP : U ∈ co3P := Qg_le (enumOK_mem keys_lt qCheck_parts.1 hu' (rep_of_validA hUv))
    have hconj := rep_conjA hUv hrep
    obtain ⟨hHv, hLv, hHP, hz⟩ := transCheck_parts j hj
    set H := permOfArr 276 (transArr j) with hHdef
    set L := permOfArr 276 (lineArr j) with hLdef
    have hLrep : Rep 276 (lineArr j) L := rep_of_validA hLv
    have hHmem : H ∈ co3P := mem_co3P_of_inP (rep_of_validA hHv) hHP
    have hUtL : U * t * U⁻¹ = L ∨ U * t * U⁻¹ = L ^ 2 := by
      rcases h with h | h
      · exact Or.inl ((eqA_iff hconj hLrep).1 h)
      · right
        rw [pow_two]
        exact (eqA_iff hconj (rep_compA hLrep hLrep)).1 h
    have hzrep := rep_conjA hHv hLrep
    have hzcase : H * L * H⁻¹ ∈ Dg ∨ H * L * H⁻¹ = yPerm ∨ H * L * H⁻¹ = yPerm ^ 2 := by
      rcases hz with hz | hz | hz
      · exact Or.inl (mem_Dg_of_inD hzrep hz)
      · exact Or.inr (Or.inl ((eqA_iff hzrep rep_y).1 hz))
      · right; right
        rw [pow_two]
        exact (eqA_iff hzrep (rep_compA rep_y rep_y)).1 hz
    refine ⟨H * U * g⁻¹, co3P.mul_mem (co3P.mul_mem hHmem hUP) (co3P.inv_mem hgP), ?_⟩
    have hkey : H * U * g⁻¹ * x * (H * U * g⁻¹)⁻¹ = H * (U * t * U⁻¹) * H⁻¹ := by
      rw [htdef]
      group
    rw [hkey]
    rcases hUtL with he | he
    · rw [he]
      exact hzcase
    · rw [he, ← conj_pow]
      rcases hzcase with hD | hy | hy
      · exact Or.inl (Dg.pow_mem hD 2)
      · rw [hy]
        exact Or.inr (Or.inr rfl)
      · rw [hy, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, yPerm_pow, one_mul,
          pow_one]
        exact Or.inr (Or.inl rfl)

end Fusion

theorem oPrimeCoreTrivialAt_co3P : OPrimeCoreTrivialAt 3 ↥co3P := by
  intro s hs
  have hso : orderOf (s : Equiv.Perm (Fin 276)) = 3 := by rw [Subgroup.orderOf_coe]; exact hs
  obtain ⟨h, hhP, hcase⟩ := exists_conj_D_or_y s.2 hso
  set h' : ↥co3P := ⟨h, hhP⟩ with hh'
  have hval : ((h' * s * h'⁻¹ : ↥co3P) : Equiv.Perm (Fin 276)) = h * (s : Equiv.Perm (Fin 276)) *
      h⁻¹ := rfl
  have ho : orderOf (h' * s * h'⁻¹) = 3 := by
    have := (MulAut.conj h' : ↥co3P ≃* ↥co3P).orderOf_eq s
    simpa [MulAut.conj_apply, hs] using this
  refine (gLAPPrimeCoreOf_centralizer_conj h' s).1 ?_
  rcases hcase with hD | hy | hy2
  · exact gLAPPrimeCoreOf_eq_bot_of_mem_Dg ho (hval ▸ hD)
  · exact gLAPPrimeCoreOf_eq_bot_of_y (Or.inl (hval.trans hy))
  · exact gLAPPrimeCoreOf_eq_bot_of_y (Or.inr (hval.trans hy2))

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint CFSG.Sporadic.Schreier.Co3

theorem sporadicOPrimeHolds_Co3_three :
    SporadicOPrimeHolds .Co3 3 := by
  intro S _ _ _ ⟨e⟩
  have e0 : S ≃* NativeSporadic.Co3 := e
  exact OPrimeCoreTrivialAt.of_mulEquiv (e0.trans co3PermEquiv) Co3T.oPrimeCoreTrivialAt_co3P

theorem sporadicOnePairHolds_Co3_three :
    SporadicOnePairHolds .Co3 3 :=
  ⟨sporadicOPrimeHolds_Co3_three, sporadicOuterHolds_Co3 3⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
