module

public import CFSG.GH74.Generic.S1.SymBlocksUniCore
public import CFSG.GH74.L5U5.ModelsPairsUnitary
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2

public section

namespace CFSG.GH74.Generic.S1.SymBlocksUni

open Matrix CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

section PF

open CFSG.ClassicalInvolution CFSG.GH74.L5U5 CFSG.LieType.BorelTits

variable [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2)

include hF in
theorem unitary_of_mem_statedSU (g : ↥(StatedSU 4 (p ^ f) F)) :
    ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 ∧
      conjTr (unitaryInvolution F p f) ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
  have hg : (g : GL (Fin 4) F) ∈ SUid (unitaryInvolution F p f) 4 := by
    rw [SUid_eq_statedSU hF]
    exact g.2
  exact hg

include hF in
theorem mem_uniBlk_iff {a b : Fin 4} {g : ↥(StatedSU 4 (p ^ f) F)} :
    g ∈ uniBlk F (p ^ f) a b ↔ IdOut a b ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  obtain ⟨-, hU⟩ := unitary_of_mem_statedSU hF g
  have hinv : (((g : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      conjTr (unitaryInvolution F p f) ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) :=
    Units.inv_eq_of_mul_eq_one_left hU
  rw [hinv]
  exact h.conjTr

@[expose] noncomputable def uniEmb {a b : Fin 4} (hab : a ≠ b) :
    Phan.Su F p f 2 →* ↥(StatedSU 4 (p ^ f) F) :=
  (suEquiv hF 4).toMonoidHom.comp (blkEmb (unitaryInvolution F p f) (pairIdx_injective hab))

theorem coe_coe_uniEmb {a b : Fin 4} (hab : a ≠ b) (A : Phan.Su F p f 2) :
    (((uniEmb hF hab A : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      blkMat (pairIdx a b) (((A : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem uniEmb_injective {a b : Fin 4} (hab : a ≠ b) : Function.Injective (uniEmb hF hab) :=
  (suEquiv hF 4).injective.comp (blkEmb_injective _ (pairIdx_injective hab))

theorem range_uniEmb {a b : Fin 4} (hab : a ≠ b) :
    (uniEmb hF hab).range = uniBlk F (p ^ f) a b := by
  ext g
  constructor
  · rintro ⟨A, rfl⟩
    rw [mem_uniBlk_iff hF, coe_coe_uniEmb]
    exact idOut_blkMat _
  · intro hg
    rw [mem_uniBlk_iff hF] at hg
    obtain ⟨hdet, hU⟩ := unitary_of_mem_statedSU hF g
    have hι := pairIdx_injective hab
    set M : Matrix (Fin 4) (Fin 4) F := ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hM
    set Am : Matrix (Fin 2) (Fin 2) F :=
      Matrix.of fun x y => M (pairIdx a b x) (pairIdx a b y) with hAm
    have hMA : M = blkMat (pairIdx a b) Am := eq_blkMat_of_idOut hab hg
    have hdetA : Am.det = 1 := by
      rw [← det_blkMat hι, ← hMA]
      exact hdet
    have hUA : conjTr (unitaryInvolution F p f) Am * Am = 1 := by
      apply blkMat_injective hι
      rw [blkMat_mul hι, ← conjTr_blkMat, ← hMA, blkMat_one]
      exact hU
    let Agl : GL (Fin 2) F :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero Am (by rw [hdetA]; exact one_ne_zero)
    have hA : Agl ∈ SUid (unitaryInvolution F p f) 2 := ⟨hdetA, hUA⟩
    refine ⟨⟨Agl, hA⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact hMA.symm

include hF in
theorem nonempty_equiv_uniBlk {a b : Fin 4} (hab : a ≠ b) :
    Nonempty (Phan.Su F p f 2 ≃* ↥(uniBlk F (p ^ f) a b)) :=
  ⟨(MonoidHom.ofInjective (uniEmb_injective hF hab)).trans
    (MulEquiv.subgroupCongr (range_uniEmb hF hab))⟩

include hF in
theorem uniBlk_perfect (hq5 : 5 ≤ p ^ f) {a b : Fin 4} (hab : a ≠ b) :
    ⁅uniBlk F (p ^ f) a b, uniBlk F (p ^ f) a b⁆ = uniBlk F (p ^ f) a b := by
  have hperf : Group.IsPerfect (Phan.Su F p f 2) := by
    obtain ⟨e⟩ := CFSG.ClassicalInvolution.Models.nonempty_sl2_mulEquiv_su_two (K := F) (p := p)
      (f := f) hF
    refine CFSG.ClassicalInvolution.isPerfect_of_equiv_sl2 ?_ e.symm
    rw [CFSG.LieType.Steinberg.card_fixedSubfield hF]
    omega
  obtain ⟨e⟩ := nonempty_equiv_uniBlk hF hab
  have : Group.IsPerfect ↥(uniBlk F (p ^ f) a b) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact Subgroup.isPerfect_iff.1 this

end PF

section PerfectLe

theorem entries_of_comm_refl (h2 : (2 : F) ≠ 0) {M : Matrix (Fin 4) (Fin 4) F} {c : Fin 4}
    (hM : M * reflDiagMat F c = reflDiagMat F c * M) {j : Fin 4} (hj : j ≠ c) :
    M c j = 0 ∧ M j c = 0 := by
  unfold reflDiagMat at hM
  have h1 := congrFun (congrFun hM c) j
  have h3 := congrFun (congrFun hM j) c
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1 h3
  simp only [hj, ↓reduceIte] at h1 h3
  constructor
  · have : (2 : F) * M c j = 0 := by linear_combination h1
    exact (mul_eq_zero.1 this).resolve_left h2
  · have : (2 : F) * M j c = 0 := by linear_combination -h3
    exact (mul_eq_zero.1 this).resolve_left h2

theorem mul_apply_self_of_row {M N : Matrix (Fin 4) (Fin 4) F} {c : Fin 4}
    (hM : ∀ k, k ≠ c → M c k = 0) : (M * N) c c = M c c * N c c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single c]
  · intro k _ hk
    rw [hM k hk, zero_mul]
  · simp

theorem fin4_cases : ∀ a b c d : Fin 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ∀ k, k = a ∨ k = b ∨ k = c ∨ k = d := by decide

end PerfectLe

section PerfectLePF

open CFSG.GH74.L5U5 CFSG.LieType.BorelTits

variable [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2)

include hF in
theorem uniBlk_perfect_le (hp2 : p ≠ 2) {a b c d : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (P : Subgroup ↥(StatedSU 4 (p ^ f) F))
    (hP : ∀ g ∈ P, (g : GL (Fin 4) F) * reflDiag F c = reflDiag F c * (g : GL (Fin 4) F) ∧
      (g : GL (Fin 4) F) * reflDiag F d = reflDiag F d * (g : GL (Fin 4) F))
    (hperf : ⁅P, P⁆ = P) : P ≤ uniBlk F (p ^ f) a b := by
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
  have hcommM : ∀ g : ↥P,
      (((g : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          reflDiagMat F c = reflDiagMat F c *
          (((g : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ∧
      (((g : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          reflDiagMat F d = reflDiagMat F d *
          (((g : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    intro g
    obtain ⟨h1, h3⟩ := hP g g.2
    have e1 := congrArg Units.val h1
    have e2 := congrArg Units.val h3
    rw [Units.val_mul, Units.val_mul] at e1 e2
    exact ⟨e1, e2⟩
  let φ0 : ↥P →* F × F :=
    { toFun := fun g => ((((g : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) :
          Matrix (Fin 4) (Fin 4) F) c c,
        (((g : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) d d)
      map_one' := by
        refine Prod.ext ?_ ?_ <;> simp
      map_mul' := fun g g' => by
        refine Prod.ext ?_ ?_
        · exact mul_apply_self_of_row fun k hk => (entries_of_comm_refl h2 (hcommM g).1 hk).1
        · exact mul_apply_self_of_row fun k hk => (entries_of_comm_refl h2 (hcommM g).2 hk).1 }
  have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hperf
  have hker : ∀ g : ↥P, φ0.toHomUnits g = 1 := by
    have := Abelianization.commutator_subset_ker φ0.toHomUnits
    rw [Group.IsPerfect.commutator_eq_top] at this
    intro g
    exact MonoidHom.mem_ker.1 (this (Subgroup.mem_top g))
  have hcc : ∀ g : ↥P, (((g : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) c c = 1 ∧
      (((g : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) d d = 1 := by
    intro g
    have := congrArg Units.val (hker g)
    rw [MonoidHom.coe_toHomUnits, Units.val_one] at this
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  intro g hg
  rw [mem_uniBlk_iff hF]
  intro i j hij
  obtain ⟨hcc1, hdd1⟩ := hcc ⟨g, hg⟩
  have hall := fin4_cases a b c d hab hac had hbc hbd hcd
  set M : Matrix (Fin 4) (Fin 4) F := ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hM
  have hMc : M * reflDiagMat F c = reflDiagMat F c * M := (hcommM ⟨g, hg⟩).1
  have hMd : M * reflDiagMat F d = reflDiagMat F d * M := (hcommM ⟨g, hg⟩).2
  have hkey : i = c ∨ i = d ∨ j = c ∨ j = d := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hic, hid, hjc, hjd⟩ := hcon
    apply hij
    refine ⟨?_, ?_⟩
    · rcases hall i with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hic
      · exact absurd h hid
    · rcases hall j with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hjc
      · exact absurd h hjd
  rcases hkey with h | h | h | h
  · subst h
    by_cases hj : j = i
    · subst hj; rw [hcc1]; simp
    · rw [(entries_of_comm_refl h2 hMc hj).1]; simp [Ne.symm hj]
  · subst h
    by_cases hj : j = i
    · subst hj; rw [hdd1]; simp
    · rw [(entries_of_comm_refl h2 hMd hj).1]; simp [Ne.symm hj]
  · subst h
    by_cases hi : i = j
    · subst hi; rw [hcc1]; simp
    · rw [(entries_of_comm_refl h2 hMc hi).2]; simp [hi]
  · subst h
    by_cases hi : i = j
    · subst hi; rw [hdd1]; simp
    · rw [(entries_of_comm_refl h2 hMd hi).2]; simp [hi]

end PerfectLePF

section Standard

open CFSG.ClassicalInvolution CFSG.GH74.L5U5 CFSG.LieType.BorelTits

theorem selL_blockIdx {m k i : ℕ} (h : i + k ≤ m) :
    selL F (Phan.blockIdx i h) = Phan.blockSel F m k i := by
  ext x j
  rw [selL_apply, Phan.blockSel_apply]
  simp only [Fin.ext_iff, Phan.blockIdx_val]

theorem blockMat_eq_blkMat {m k i : ℕ} (h : i + k ≤ m) (A : Matrix (Fin k) (Fin k) F) :
    Phan.blockMat m i A = blkMat (Phan.blockIdx i h) A := by
  unfold Phan.blockMat blkMat
  rw [selL_blockIdx]

theorem blockIdx_comp_pairIdx_zero {a b c : Fin 4} :
    (![a, b, c] : Fin 3 → Fin 4) ∘ Phan.blockIdx 0 (by omega : 0 + 2 ≤ 3) = pairIdx a b := by
  funext x
  fin_cases x <;> rfl

theorem blockIdx_comp_pairIdx_one {a b c : Fin 4} :
    (![a, b, c] : Fin 3 → Fin 4) ∘ Phan.blockIdx 1 (by omega : 1 + 2 ≤ 3) = pairIdx b c := by
  funext x
  fin_cases x <;> rfl

theorem blockIdx_eq_pairIdx (i : Fin 3) (h : (i : ℕ) + 2 ≤ 4) :
    Phan.blockIdx (i : ℕ) h = pairIdx (Fin.castSucc i) (Fin.succ i) := by
  funext x
  fin_cases x <;> (apply Fin.ext; simp [Phan.blockIdx, pairIdx])

theorem pairIdx_three_injective {a b c : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (![a, b, c] : Fin 3 → Fin 4) := by
  intro x y hxy
  fin_cases x <;> fin_cases y
  · rfl
  · exact absurd hxy hab
  · exact absurd hxy hac
  · exact absurd hxy.symm hab
  · rfl
  · exact absurd hxy hbc
  · exact absurd hxy.symm hac
  · exact absurd hxy.symm hbc
  · rfl

variable [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2)

include hF in
theorem uni_std_pf {a b c : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ W : Subgroup ↥(StatedSU 4 (p ^ f) F), Phan.UnitaryBlockStandardPair F p f W
      (uniBlk F (p ^ f) a b) (uniBlk F (p ^ f) b c) := by
  have hι3 := pairIdx_three_injective hab hac hbc
  let θ : Phan.Su F p f 3 →* ↥(StatedSU 4 (p ^ f) F) :=
    (suEquiv hF 4).toMonoidHom.comp (blkEmb (unitaryInvolution F p f) hι3)
  have hθinj : Function.Injective θ :=
    (suEquiv hF 4).injective.comp (blkEmb_injective _ hι3)
  have hB12 : (Phan.B12 F p f).map θ = uniBlk F (p ^ f) a b := by
    rw [Phan.B12, ← MonoidHom.range_comp, ← range_uniEmb hF hab]
    congr 1
    apply MonoidHom.ext
    intro A
    apply Subtype.ext
    apply Units.ext
    change blkMat ![a, b, c] (CFSG.LieType.Steinberg.embPair 2
      ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) = blkMat (pairIdx a b) _
    rw [Phan.embPair_two_eq_blockMat, blockMat_eq_blkMat (by omega : 0 + 2 ≤ 3), blkMat_blkMat,
      blockIdx_comp_pairIdx_zero]
    rfl
  have hB23 : (Phan.B23 F p f).map θ = uniBlk F (p ^ f) b c := by
    rw [Phan.B23, ← MonoidHom.range_comp, ← range_uniEmb hF hbc]
    congr 1
    apply MonoidHom.ext
    intro A
    apply Subtype.ext
    apply Units.ext
    change blkMat ![a, b, c] (CFSG.LieType.Steinberg.embPair 0
      ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) = blkMat (pairIdx b c) _
    rw [Phan.embPair_zero_eq_blockMat, blockMat_eq_blkMat (by omega : 1 + 2 ≤ 3), blkMat_blkMat,
      blockIdx_comp_pairIdx_one]
    rfl
  have hc : ∀ H : Subgroup (Phan.Su F p f 3),
      H.map (MulAut.conj (1 : Phan.Su F p f 3)⁻¹).toMonoidHom = H := fun H => by
    ext x
    simp
  refine ⟨θ.range, θ, 1, rfl, ?_, Or.inl ⟨?_, ?_⟩⟩
  · rw [(MonoidHom.ker_eq_bot_iff _).mpr hθinj]
    exact bot_le
  · rw [hc, hB12]
  · rw [hc, hB23]

include hF in
theorem uni_chain_pf (hq2 : p ^ f ≠ 2) :
    ∃ W : Fin 3 → Fin 3 → Subgroup ↥(StatedSU 4 (p ^ f) F), Phan.WeakPhanA F p f 3
      (fun i : Fin 3 => uniBlk F (p ^ f) (Fin.castSucc i) (Fin.succ i)) W := by
  have hsys := weakPhanA_map_equiv (Phan.weakPhanA_standard hF hq2 3) (suEquiv hF 4)
  have hU : ∀ i : Fin 3, (Phan.standardU F p f 3 i).map (suEquiv hF 4).toMonoidHom =
      uniBlk F (p ^ f) (Fin.castSucc i) (Fin.succ i) := by
    intro i
    have hne : Fin.castSucc i ≠ Fin.succ i := Fin.castSucc_lt_succ.ne
    rw [← range_uniEmb hF hne, Phan.standardU, ← MonoidHom.range_comp]
    congr 1
    apply MonoidHom.ext
    intro A
    apply Subtype.ext
    apply Units.ext
    change Phan.blockMat 4 (i : ℕ) _ = blkMat (pairIdx (Fin.castSucc i) (Fin.succ i)) _
    rw [blockMat_eq_blkMat (by omega), blockIdx_eq_pairIdx]
  refine ⟨fun i j => (Phan.standardW F p f 3 i j).map (suEquiv hF 4).toMonoidHom, ?_⟩
  have : (fun i : Fin 3 => uniBlk F (p ^ f) (Fin.castSucc i) (Fin.succ i)) =
      fun i => (Phan.standardU F p f 3 i).map (suEquiv hF 4).toMonoidHom :=
    funext fun i => (hU i).symm
  rw [this]
  exact hsys

end Standard
end CFSG.GH74.Generic.S1.SymBlocksUni
