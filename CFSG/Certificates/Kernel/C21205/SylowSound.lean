module

public import Certificates.Data.Kernel.C21205.Sylow
public import CFSG.Certificates.Kernel.Misc.Spec.F2Mat
public import CFSG.Certificates.Kernel.Spor.PK.MiscBase
public import CFSG.LargeExtraspecial.AS35QCoSp6Spec
public import CFSG.Sporadic.Co2Smith.Timmesfeld
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Utils
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import Certificates.Data.Kernel.Misc.T46

public section

namespace CFSG.KC.C21205

open CFSG.LargeExtraspecial.AS35QCo CFSG.LargeExtraspecial.AS35QCo.Native CFSG.KS.PK
  CFSG.KC.Misc.Spec CFSG.Sporadic.Co2Smith CFSG.KC.Ord CFSG.KC.LQT.P
open scoped Pointwise Matrix

theorem fld_eq (Q w i : ℕ) : fld Q w i = (Q >>> (w * i)) &&& (2 ^ w - 1) := by
  unfold fld
  rw [shl1_eq]
  rfl

theorem fld_lt (Q w i : ℕ) : fld Q w i < 2 ^ w := by
  rw [fld_eq]
  exact Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos w) Nat.one_pos)

theorem decode_eq_pkMat (c : ℕ) :
    decode c = (pkMat 6 c).submatrix finSumFinEquiv finSumFinEquiv := by
  ext x y
  rfl

theorem decode_mulK (c d : ℕ) : decode (mulK c d) = decode c * decode d := by
  simp only [decode_eq_pkMat, mulK, pkMat_mulF2, Matrix.submatrix_mul_equiv]

theorem rep_mulK {c d : ℕ} {g h : Sp62} (hg : LargeExtraspecial.AS35QCo.Rep c g)
    (hh : LargeExtraspecial.AS35QCo.Rep d h) :
    LargeExtraspecial.AS35QCo.Rep (mulK c d) (g * h) := by
  unfold LargeExtraspecial.AS35QCo.Rep at *
  rw [decode_mulK, ← hg, ← hh]
  rfl

theorem stepF2_lt (A B k : ℕ) : stepF2 6 A B k < 2 ^ 36 := by
  unfold stepF2
  apply Nat.and_lt_two_pow
  have hV : (B >>> (6 * k)) &&& (2 ^ 6 - 1) ≤ 2 ^ 6 - 1 := Nat.and_le_right
  have hm := repu_mul 6 6
  calc ((B >>> (6 * k)) &&& (2 ^ 6 - 1)) * repu 6 6 ≤ (2 ^ 6 - 1) * repu 6 6 :=
        Nat.mul_le_mul_right _ hV
    _ < 2 ^ 36 := by
        have e : (2 : ℕ) ^ (6 * 6) = 2 ^ 36 := rfl
        omega

theorem foldF2_lt (A B : ℕ) : ∀ m, foldF2 6 A B m < 2 ^ 36
  | 0 => by simp [foldF2]
  | m + 1 => Nat.xor_lt_two_pow (foldF2_lt A B m) (stepF2_lt A B m)

theorem mulK_lt (c d : ℕ) : mulK c d < 2 ^ 36 := by
  rw [mulK, mulF2_eq_fold (by norm_num)]
  exact foldF2_lt c d 6

theorem mulK_eq (c d : ℕ) : mulK c d = mulc c d :=
  decode_injective (mulK_lt c d) (mulc_lt c d) (by rw [decode_mulK, decode_mulc])

@[expose] noncomputable def transLoop (c : ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p acc => Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight c
      (Nat.add (Nat.mul 6 (Nat.mod p 6)) (Nat.div p 6))) 1) p)) n

theorem transLoop_succ (c n : ℕ) :
    transLoop c (n + 1) = transLoop c n ||| (((c >>> (6 * (n % 6) + n / 6)) &&& 1) <<< n) := rfl

theorem testBit_transLoop (c q : ℕ) :
    ∀ n, (transLoop c n).testBit q = (decide (q < n) && c.testBit (6 * (q % 6) + q / 6))
  | 0 => by simp [transLoop]
  | n + 1 => by
    rw [transLoop_succ, Nat.testBit_or, testBit_transLoop c q n, Nat.testBit_shiftLeft]
    rcases lt_trichotomy q n with h | rfl | h
    · have h1 : ¬ q ≥ n := by omega
      simp [h, h1, show q < n + 1 by omega]
    · simp [Nat.testBit_and, Nat.testBit_shiftRight]
    · have h1 : ¬ q < n := by omega
      have h2 : ¬ q < n + 1 := by omega
      have h3 : (1 : ℕ).testBit (q - n) = false :=
        Bool.eq_false_iff.mpr (Nat.testBit_one_eq_true_iff_self_eq_zero.not.mpr (by omega))
      rw [Nat.testBit_and, h3]
      simp [h1, h2]

theorem testBit_transK (c q : ℕ) :
    (transK c).testBit q = (decide (q < 36) && c.testBit (6 * (q % 6) + q / 6)) :=
  testBit_transLoop c q 36

theorem transK_lt (c : ℕ) : transK c < 2 ^ 36 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_transK]
  simp [show ¬ i < 36 by omega]

theorem decode_transK (c : ℕ) : decode (transK c) = (decode c)ᵀ := by
  ext x y
  rw [Matrix.transpose_apply, decode_apply, decode_apply, testBit_transK]
  have hx := ix_lt x
  have hy := ix_lt y
  have h1 : (6 * ix x + ix y) % 6 = ix y := by omega
  have h2 : (6 * ix x + ix y) / 6 = ix x := by omega
  rw [h1, h2, decide_eq_true (by omega : 6 * ix x + ix y < 36), Bool.true_and]

theorem transK_eq (c : ℕ) : transK c = transc c :=
  decode_injective (transK_lt c) (transc_lt c) (by rw [decode_transK, decode_transc])

theorem isSpK_eq (c : ℕ) : isSpK c = isSp c := by
  unfold isSpK isSp
  rw [mulK_eq, mulK_eq, transK_eq]
  rfl

theorem exists_rep_of_pairK {c ci : ℕ} (h : pairK c ci = true) :
    ∃ g : Sp62, Rep c g ∧ Rep ci g⁻¹ := by
  simp only [pairK, andB_eq, Bool.and_eq_true, Nat.beq_eq, isSpK_eq, mulK_eq] at h
  exact exists_rep h.2.1 h.2.2 h.1

section Census

variable {PQ i0 ng G R PD CJ : ℕ}

local notation "X" i => fld PQ 36 i

local notation "Gc" j => fld (fld G 72 j) 36 0

theorem finite_sp62 : Finite Sp62 :=
  Nat.finite_of_card_ne_zero (by rw [natCard_sp62]; norm_num)

theorem lt_of_chain {f : ℕ → ℕ} (h : ∀ i < 511, f i < f (i + 1)) :
    ∀ j, j < 512 → ∀ i < j, f i < f j := by
  intro j
  induction j with
  | zero => intro _ i hi; omega
  | succ j ih =>
    intro hj i hi
    rcases (show i < j ∨ i = j by omega) with h' | rfl
    · exact (ih (by omega) i h').trans (h j (by omega))
    · exact h i (by omega)

theorem exists_conj_rep_of_sylowK (h : sylowK PQ i0 ng G R PD CJ = true) (τ : Sp62)
    (h2 : τ * τ = 1) (h1 : τ ≠ 1) :
    ∃ k < 4, ∃ ρ : Sp62, LargeExtraspecial.AS35QCo.Rep (repc k) ρ ∧
      ∃ m : Sp62, τ = m * ρ * m⁻¹ := by
  have hfin := finite_sp62
  simp only [sylowK, andB_eq, orB_eq, notB_eq, impB_eq, letB_eq, Bool.and_eq_true,
    Bool.or_eq_true, allN_lqt_iff, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hi0, hid, hsort, hreps, hgens, hcl, htree, hinv⟩ := h
  have hgen : ∀ j < ng, ∃ g : Sp62, LargeExtraspecial.AS35QCo.Rep (Gc j) g := fun j hj => by
    obtain ⟨g, hg, -⟩ := exists_rep_of_pairK (hgens j hj)
    exact ⟨g, hg⟩
  set gens : Set Sp62 := {g | ∃ j < ng, LargeExtraspecial.AS35QCo.Rep (Gc j) g} with hgensdef
  set M := Submonoid.closure gens with hM
  have htreeM : ∀ d, ∀ i < 512, Nat.shiftRight (fld PD 24 i) 13 = d →
      ∃ g ∈ M, LargeExtraspecial.AS35QCo.Rep (X i) g := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i hi hd
      rcases htree i hi with e | ⟨hj, hdep, hx⟩
      · subst e
        exact ⟨1, M.one_mem, hid ▸ Rep.one⟩
      · obtain ⟨g, hgM, hg⟩ := ih (Nat.shiftRight (fld PD 24 (fld (fld PD 24 i) 9 0)) 13)
          (by rw [← hd, hdep]; exact Nat.lt_succ_self _) (fld (fld PD 24 i) 9 0) (fld_lt _ 9 0) rfl
        obtain ⟨u, hu⟩ := hgen _ hj
        exact ⟨g * u, M.mul_mem hgM (Submonoid.subset_closure ⟨_, hj, hu⟩), hx ▸ rep_mulK hg hu⟩
  have hSM : ∀ i < 512, ∃ g ∈ M, LargeExtraspecial.AS35QCo.Rep (X i) g := fun i hi => htreeM _ i hi rfl
  have hMS : ∀ g ∈ M, ∃ i < 512, LargeExtraspecial.AS35QCo.Rep (X i) g := by
    intro g hg
    induction hg using Submonoid.closure_induction_right with
    | one => exact ⟨i0, hi0, hid ▸ Rep.one⟩
    | mul_right x _ y hy ih =>
      obtain ⟨i, hi, hx⟩ := ih
      obtain ⟨j, hj, hyj⟩ := hy
      refine ⟨fld R 9 (Nat.add (Nat.mul ng i) j), fld_lt _ 9 _, ?_⟩
      rw [hcl i hi j hj]
      exact rep_mulK hx hyj
  set P := Subgroup.closure gens with hP
  have hPM : ∀ g, g ∈ P ↔ g ∈ M := fun g => by
    rw [hP, ← Subgroup.mem_toSubmonoid, Subgroup.closure_toSubmonoid_of_finite]
  have hinj : ∀ i < 512, ∀ j < 512, (X i) = (X j) → i = j := by
    intro i hi j hj e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · exact absurd e (lt_of_chain hsort j hj i h').ne
    · exact absurd e (lt_of_chain hsort i hi j h').ne'
  have hcard : Nat.card P = 512 := by
    have hel : ∀ i : Fin 512, ∃ g : P, LargeExtraspecial.AS35QCo.Rep (X i.val) g := fun i => by
      obtain ⟨g, hgM, hg⟩ := hSM i.val i.isLt
      exact ⟨⟨g, (hPM g).mpr hgM⟩, hg⟩
    choose f hf using hel
    rw [← Nat.card_eq_of_bijective f ⟨?_, ?_⟩, Nat.card_eq_fintype_card, Fintype.card_fin]
    · intro a b e
      apply Fin.ext
      apply hinj a.val a.isLt b.val b.isLt
      exact Rep.code_eq (hf a) (e ▸ hf b) (fld_lt _ _ _) (fld_lt _ _ _)
    · intro g
      obtain ⟨i, hi, hg⟩ := hMS g.1 ((hPM g.1).mp g.2)
      exact ⟨⟨i, hi⟩, Subtype.ext (Rep.unique (hf ⟨i, hi⟩) hg)⟩
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPp : IsPGroup 2 P := IsPGroup.of_card (n := 9) (by rw [hcard]; norm_num)
  have hidx : ¬ 2 ∣ P.index := by
    have hm := P.card_mul_index
    rw [hcard, natCard_sp62] at hm
    have : P.index = 2835 := by omega
    rw [this]
    norm_num
  set S := hPp.toSylow hidx
  have hτp : IsPGroup 2 (Subgroup.zpowers τ) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [sq]; exact h2) h1)
  obtain ⟨Q, hQ⟩ := hτp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Sp62 S Q
  have hτQ : τ ∈ (Q : Subgroup Sp62) := hQ (Subgroup.mem_zpowers τ)
  rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hτQ
  set y := g⁻¹ * τ * g with hy
  have hyP : y ∈ P := by
    have hS : (S : Subgroup Sp62) = P := hPp.toSylow_coe hidx
    rw [hS] at hτQ
    simpa [MulAut.smul_def, MulAut.conj_apply] using hτQ
  obtain ⟨i, hi, hyi⟩ := hMS y ((hPM y).mp hyP)
  have hy2 : y * y = 1 := by
    calc y * y = g⁻¹ * (τ * τ) * g := by rw [hy]; group
      _ = 1 := by rw [h2]; group
  have hy1 : y ≠ 1 := fun e => h1 (by
    calc τ = g * y * g⁻¹ := by rw [hy]; group
      _ = 1 := by rw [e]; group)
  have hsq : mulK (X i) (X i) = idc :=
    Rep.code_eq (hy2 ▸ rep_mulK hyi hyi) Rep.one (mulK_lt _ _) (by decide)
  have hne : (X i) ≠ idc := fun e => hy1 (Rep.unique hyi (e ▸ Rep.one))
  have hc : conjK (X i) (fld CJ 74 i) = true := by
    rcases hinv i hi with h' | h'
    · rw [hsq, Nat.beq_refl] at h'
      simp only [Bool.true_and, Bool.not_not] at h'
      exact absurd (Nat.eq_of_beq_eq_true h') hne
    · exact h'
  simp only [conjK, letB_eq, andB_eq, Bool.and_eq_true, Nat.beq_eq] at hc
  obtain ⟨hpair, hconj⟩ := hc
  obtain ⟨μ, hμ, -⟩ := exists_rep_of_pairK hpair
  set k := fld (fld CJ 74 i) 2 0
  have hk : k < 4 := fld_lt _ 2 0
  have hr := hreps k hk
  simp only [Bool.and_eq_true, Nat.beq_eq, isSpK_eq, mulK_eq] at hr
  obtain ⟨ρ, hρ, -⟩ := exists_rep hr.2 hr.2 hr.1
  have e : y * μ = μ * ρ := Rep.unique (rep_mulK hyi hμ) (hconj ▸ rep_mulK hμ hρ)
  refine ⟨k, hk, ρ, hρ, g * μ, ?_⟩
  have hyμ : y = μ * ρ * μ⁻¹ := by
    calc y = y * μ * μ⁻¹ := by group
      _ = μ * ρ * μ⁻¹ := by rw [e]
  calc τ = g * y * g⁻¹ := by rw [hy]; group
    _ = g * μ * ρ * (g * μ)⁻¹ := by rw [hyμ]; group

end Census

end CFSG.KC.C21205

end
