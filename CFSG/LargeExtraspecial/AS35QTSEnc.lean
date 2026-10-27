module

public import CFSG.LargeExtraspecial.AS35QTSCode
public import CFSG.LargeExtraspecial.AS35QThGamBij

public section

namespace CFSG.LargeExtraspecial.AS35QTS

open Matrix CFSG.Fischer CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LargeExtraspecial.AS35QTh
open CFSG.Blueprint.Fischer (K)

noncomputable abbrev ef (c : K) : F4 := eF4.symm c

theorem ef_add (a b : K) : ef (a + b) = ef a + ef b := map_add eF4.symm a b

theorem ef_mul (a b : K) : ef (a * b) = ef a * ef b := map_mul eF4.symm a b

theorem ef_zero : ef 0 = 0 := map_zero eF4.symm

theorem ef_one : ef 1 = 1 := map_one eF4.symm

theorem ef_frob (c : K) : ef (frob c) = fr (ef c) := by
  rw [frob_apply, pow_two, ef_mul]
  rfl

theorem ef_omega : ef ω = F4.ω := by
  rw [omega_eq]
  exact eF4.symm_apply_apply F4.ω

@[expose] noncomputable def encV (a : Fin 3 → K) : V3 := ⟨ef (a 0), ef (a 1), ef (a 2)⟩

@[expose] noncomputable def encM (A : Matrix (Fin 3) (Fin 3) K) : M3 :=
  ⟨⟨ef (A 0 0), ef (A 0 1), ef (A 0 2)⟩, ⟨ef (A 1 0), ef (A 1 1), ef (A 1 2)⟩,
    ⟨ef (A 2 0), ef (A 2 1), ef (A 2 2)⟩⟩

theorem encV_injective : Function.Injective encV := by
  intro a b h
  simp only [encV, V3.mk.injEq] at h
  obtain ⟨h0, h1, h2⟩ := h
  funext i
  fin_cases i
  · exact eF4.symm.injective h0
  · exact eF4.symm.injective h1
  · exact eF4.symm.injective h2

theorem encM_injective : Function.Injective encM := by
  intro A B h
  simp only [encM, M3.mk.injEq, V3.mk.injEq] at h
  obtain ⟨⟨h00, h01, h02⟩, ⟨h10, h11, h12⟩, ⟨h20, h21, h22⟩⟩ := h
  ext i j
  fin_cases i <;> fin_cases j <;> apply eF4.symm.injective <;> assumption

theorem encV_add (a b : Fin 3 → K) : encV (a + b) = vadd (encV a) (encV b) := by
  simp only [encV, vadd, Pi.add_apply, ef_add]

theorem encV_mulVec (A : Matrix (Fin 3) (Fin 3) K) (v : Fin 3 → K) :
    encV (A *ᵥ v) = mv (encM A) (encV v) := by
  simp only [encV, encM, mv, dot, mulVec, dotProduct, Fin.sum_univ_three, ef_add, ef_mul]

theorem encM_mul (A B : Matrix (Fin 3) (Fin 3) K) :
    encM (A * B) = mm (encM A) (encM B) := by
  simp only [encM, mm, rowMul, dot, col0, col1, col2, mul_apply, Fin.sum_univ_three, ef_add,
    ef_mul]

theorem ef_herm (a b : Fin 3 → K) : ef (herm frob a b) = hermC (encV a) (encV b) := by
  rw [herm_def, Fin.sum_univ_three, ef_add, ef_add, ef_mul, ef_mul, ef_mul, ef_frob, ef_frob,
    ef_frob]
  rfl

theorem tr2_eq (c : K) : tr2 c = tr2C (ef c) := by
  classical
  unfold tr2 tr2C
  have e : (c + frob c = 0) ↔ (ef c + fr (ef c) = 0) := by
    rw [← ef_frob, ← ef_add, ← ef_zero]
    exact eF4.symm.injective.eq_iff.symm
  by_cases h : c + frob c = 0
  · simp only [h, e.mp h, ite_true]
  · have h' : ¬ (ef c + fr (ef c) = 0) := fun h' => h (e.mpr h')
    simp only [h, h', ite_false]

theorem beta_eq (a b : Fin 3 → K) : beta a b = betaC (encV a) (encV b) := by
  rw [beta, betaC, tr2_eq, ef_mul, ef_omega, ef_herm]

@[expose] noncomputable def enc (x : Model) : Cd := ⟨x.1, encV x.2.1, encM (gm x.2.2)⟩

theorem enc_mulM (x y : Model) : enc (mulM x y) = mulC (enc x) (enc y) := by
  obtain ⟨ε, a, A⟩ := x
  obtain ⟨ε', a', A'⟩ := y
  simp only [enc, mulM, mulC, gv, Cd.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [beta_eq, encV_mulVec]
  · rw [encV_add, encV_mulVec]
  · rw [show gm (A * A') = gm A * gm A' from rfl, encM_mul]

theorem enc_injective : Function.Injective enc := by
  rintro ⟨ε, a, A⟩ ⟨ε', a', A'⟩ h
  simp only [enc, Cd.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [h1, encV_injective h2, gm_injective (encM_injective h3)]

@[expose] def colOf (B : M3) : Fin 3 → V3 := ![col0 B, col1 B, col2 B]

theorem herm_colOf_encM (A : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    hermC (colOf (encM A) i) (colOf (encM A) j) = ef ((conjTr frob A * A) i j) := by
  have e : (conjTr frob A * A) i j =
      frob (A 0 i) * A 0 j + frob (A 1 i) * A 1 j + frob (A 2 i) * A 2 j := by
    simp only [conjTr, mul_apply, Fin.sum_univ_three, transpose_apply, map_apply]
  rw [e, ef_add, ef_add, ef_mul, ef_mul, ef_mul, ef_frob, ef_frob, ef_frob]
  fin_cases i <;> fin_cases j <;> rfl

theorem unitB_iff (B : M3) : unitB B = true ↔
    ∀ i j : Fin 3, hermC (colOf B i) (colOf B j) = if i = j then 1 else 0 := by
  constructor
  · intro h i j
    simp only [unitB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h00, h01⟩, h02⟩, h10⟩, h11⟩, h12⟩, h20⟩, h21⟩, h22⟩ := h
    fin_cases i <;> fin_cases j <;> simpa [colOf]
  · intro h
    have h00 := h 0 0
    have h01 := h 0 1
    have h02 := h 0 2
    have h10 := h 1 0
    have h11 := h 1 1
    have h12 := h 1 2
    have h20 := h 2 0
    have h21 := h 2 1
    have h22 := h 2 2
    simp only [colOf] at h00 h01 h02 h10 h11 h12 h20 h21 h22
    simp only [unitB, Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> simpa

theorem unitB_encM {A : Matrix (Fin 3) (Fin 3) K} (hA : conjTr frob A * A = 1) :
    unitB (encM A) = true := by
  rw [unitB_iff]
  intro i j
  rw [herm_colOf_encM, hA, one_apply]
  split_ifs <;> simp

@[expose] def compOf (v : V3) : Fin 3 → F4 := ![v.x0, v.x1, v.x2]

@[expose] def rowOf (B : M3) : Fin 3 → V3 := ![B.r0, B.r1, B.r2]

@[expose] noncomputable def decM (B : M3) : Matrix (Fin 3) (Fin 3) K :=
  fun i j => eF4 (compOf (rowOf B i) j)

theorem encM_decM (B : M3) : encM (decM B) = B := by
  obtain ⟨⟨a, b, c⟩, ⟨d, e, f⟩, ⟨g, h, i⟩⟩ := B
  simp [encM, decM, ef, compOf, rowOf]

theorem conjTr_decM {B : M3} (hB : unitB B = true) : conjTr frob (decM B) * decM B = 1 := by
  rw [unitB_iff] at hB
  ext i j
  apply eF4.symm.injective
  have := hB i j
  rw [← encM_decM B, herm_colOf_encM] at this
  change ef _ = ef _
  rw [this, one_apply]
  split_ifs
  · exact ef_one.symm
  · exact ef_zero.symm

@[expose] noncomputable def decGU {B : M3} (hB : unitB B = true) : GU3 :=
  ⟨⟨decM B, conjTr frob (decM B), mul_eq_one_comm.mp (conjTr_decM hB), conjTr_decM hB⟩,
    conjTr_decM hB⟩

theorem encM_decGU {B : M3} (hB : unitB B = true) : encM (gm (decGU hB)) = B := encM_decM B

theorem mem_f4s (x : F4) : x ∈ f4s := by
  obtain ⟨k⟩ := x
  fin_cases k <;> simp [f4s]

theorem mem_v3s (v : V3) : v ∈ v3s := by
  obtain ⟨a, b, c⟩ := v
  simp only [v3s, List.mem_flatMap, List.mem_map]
  exact ⟨a, mem_f4s a, b, mem_f4s b, c, mem_f4s c, rfl⟩

theorem mem_gu3s {B : M3} : B ∈ gu3s ↔ unitB B = true := by
  obtain ⟨r0, r1, r2⟩ := B
  simp only [gu3s, List.mem_filter, List.mem_flatMap, List.mem_map]
  exact ⟨fun h => h.2, fun h => ⟨⟨r0, mem_v3s r0, r1, mem_v3s r1, r2, mem_v3s r2, rfl⟩, h⟩⟩

theorem mem_codes {c : Cd} : c ∈ codes ↔ unitB c.m = true := by
  obtain ⟨e, a, m⟩ := c
  simp only [codes, List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨e', -, a', -, m', hm', h⟩
    simp only [Cd.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact mem_gu3s.mp hm'
  · intro h
    refine ⟨e, ?_, a, mem_v3s a, m, mem_gu3s.mpr h, rfl⟩
    revert e
    decide

theorem enc_mem_codes (x : Model) : enc x ∈ codes :=
  mem_codes.mpr (unitB_encM (mem_GU3.mp x.2.2.2))

theorem exists_enc_eq {c : Cd} (hc : c ∈ codes) : ∃ x : Model, enc x = c := by
  obtain ⟨e, a, m⟩ := c
  have hm := mem_codes.mp hc
  refine ⟨(e, fun i => eF4 (compOf a i), decGU hm), ?_⟩
  have h1 : encV (fun i => eF4 (compOf a i)) = a := by
    obtain ⟨a0, a1, a2⟩ := a
    simp only [encV, ef, compOf, RingEquiv.symm_apply_apply]
    rfl
  change (⟨e, encV _, encM (gm (decGU hm))⟩ : Cd) = ⟨e, a, m⟩
  rw [h1, encM_decGU hm]

abbrev CC : Type := Subgroup.centralizer ({tq (v₀ 3)} : Set (PG 5))

@[expose] noncomputable def psiEquiv : Model ≃ CC := Equiv.ofBijective psiC psiC_bijective

@[expose] noncomputable def psiCode (x : CC) : Cd := enc (psiEquiv.symm x)

theorem psiCode_mul (x y : CC) : psiCode (x * y) = mulC (psiCode x) (psiCode y) := by
  obtain ⟨a, rfl⟩ := psiEquiv.surjective x
  obtain ⟨b, rfl⟩ := psiEquiv.surjective y
  have e : psiEquiv a * psiEquiv b = psiEquiv (mulM a b) := (psiC_mul a b).symm
  rw [e, psiCode, psiCode, psiCode, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, enc_mulM]

theorem psiCode_injective : Function.Injective psiCode :=
  enc_injective.comp psiEquiv.symm.injective

theorem psiCode_mem (x : CC) : psiCode x ∈ codes := enc_mem_codes _

theorem exists_psiCode_eq {c : Cd} (hc : c ∈ codes) : ∃ x : CC, psiCode x = c := by
  obtain ⟨y, rfl⟩ := exists_enc_eq hc
  exact ⟨psiEquiv y, by rw [psiCode, Equiv.symm_apply_apply]⟩

theorem natCard_GU3 : Nat.card GU3 = gu3s.toFinset.card := by
  classical
  have hinj : Function.Injective fun A : GU3 => encM (gm A) :=
    fun A B h => gm_injective (encM_injective h)
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.ofBijective (fun A => ⟨encM (gm A), ?_⟩) ⟨?_, ?_⟩)
  · exact List.mem_toFinset.mpr (mem_gu3s.mpr (unitB_encM (mem_GU3.mp A.2)))
  · intro A B h
    exact hinj (congrArg Subtype.val h)
  · rintro ⟨B, hB⟩
    have hB' := mem_gu3s.mp (List.mem_toFinset.mp hB)
    exact ⟨decGU hB', Subtype.ext (encM_decGU hB')⟩

theorem natCard_CC : Nat.card CC = 2 * 64 * gu3s.toFinset.card := by
  rw [← Nat.card_congr psiEquiv, Nat.card_prod, Nat.card_prod, natCard_GU3, Nat.card_zmod,
    Nat.card_fun, card_K, Nat.card_fin]
  ring

end CFSG.LargeExtraspecial.AS35QTS
