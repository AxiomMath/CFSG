module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameModelPSL
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalUnitary

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.ModelFacts CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_mul blockMat_one Su blockEmb)
open scoped MatrixGroups

section Basic

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {m : ℕ}

theorem monoSU_conj_zEltU (hn : 0 < m + 1) (σ : Equiv.Perm (Fin (m + 1))) (T T' : Pair (m + 1))
    (hT : T'.1 = T.1.map σ.toEmbedding) :
    monoSU K p f hn σ * zEltU K p f T * (monoSU K p f hn σ)⁻¹ = zEltU K p f T' := by
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_zEltU, suMat_zEltU]
  have hg : IsMonomialFor (suMat (monoSU K p f hn σ)) σ := isMonomialFor_monoMat σ
  rw [hg.mul_zMat_mul_inv (suMat_mul_suMat_inv _), hT]

theorem zEltU_not_central (h2 : (2 : K) ≠ 0) (hn : 0 < m + 1) (T : Pair (m + 1))
    {x y : Fin (m + 1)} (hx : x ∈ T.1) (hy : y ∉ T.1) :
    zEltU K p f T ∉ Subgroup.center (Su K p f (m + 1)) := by
  intro hc
  set T' : Pair (m + 1) := ⟨T.1.map (Equiv.swap x y).toEmbedding, by rw [Finset.card_map, T.2]⟩
    with hT'
  have hconj := monoSU_conj_zEltU (K := K) (p := p) (f := f) hn (Equiv.swap x y) T T' rfl
  have hcen := Subgroup.mem_center_iff.mp hc (monoSU K p f hn (Equiv.swap x y))
  have h1 : zEltU K p f T' = zEltU K p f T := by
    rw [← hconj, hcen]
    group
  have h2' : T'.1 = T.1 := zMat_inj h2 (by
    have := congrArg suMat h1
    rwa [suMat_zEltU, suMat_zEltU] at this)
  have hyT' : y ∈ T'.1 := by
    show y ∈ T.1.map (Equiv.swap x y).toEmbedding
    rw [Finset.mem_map_equiv]
    simpa using hx
  exact hy (h2' ▸ hyT')

end Basic

section Block

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

variable (K p f) in
@[expose] noncomputable def wSU : Su K p f 2 :=
  mkSU K p f !![0, 1; -1, 0] (by simp [Matrix.det_fin_two]) (by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two])

theorem suMat_wSU : suMat (wSU K p f) = !![0, 1; -1, 0] := rfl

theorem wSU_mul_self : suMat (wSU K p f) * suMat (wSU K p f) = -1 := by
  rw [suMat_wSU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem commutator_blockEmb_eq (hn : 2 ≤ n) {e : Su K p f n}
    (he : e ∈ signGroupU K p f n) (hne : entU e ⟨0, by omega⟩ ≠ entU e ⟨1, by omega⟩) :
    e * blockEmb K p f n 2 0 (by omega) (wSU K p f) * e⁻¹ *
        (blockEmb K p f n 2 0 (by omega) (wSU K p f))⁻¹ =
      zEltU K p f (⟨{⟨0, by omega⟩, ⟨1, by omega⟩}, Finset.card_pair (by
        intro h; simpa using congrArg Fin.val h)⟩ : Pair n) := by
  have ha := entU_cases he ⟨0, by omega⟩
  have hb := entU_cases he ⟨1, by omega⟩
  have hab : entU e ⟨0, by omega⟩ * entU e ⟨1, by omega⟩ = -1 := by
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp_all
  have h1 : e * blockEmb K p f n 2 0 (by omega) (wSU K p f) * e⁻¹ *
      blockEmb K p f n 2 0 (by omega) (wSU K p f) = 1 := by
    apply suMat_injective
    rw [suMat_mul, suMat_conj_blockEmb hn he, suMat_blockEmb, ← blockMat_mul (by omega),
      suMat_one, ← blockMat_one (m := n) (i := 0) (k := 2) (F := K)]
    congr 1
    rw [suMat_wSU]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hab]
    all_goals linear_combination (-1 : K) * hab
  have h2r : blockEmb K p f n 2 0 (by omega) (wSU K p f) *
      blockEmb K p f n 2 0 (by omega) (wSU K p f) =
      zEltU K p f (⟨{⟨0, by omega⟩, ⟨1, by omega⟩}, Finset.card_pair (by
        intro h; simpa using congrArg Fin.val h)⟩ : Pair n) := by
    apply suMat_injective
    rw [suMat_mul, suMat_blockEmb, ← blockMat_mul (by omega), wSU_mul_self, suMat_zEltU]
    exact negBlock_eq_zMat (by omega : 0 + 2 ≤ n)
  rw [eq_inv_of_mul_eq_one_left h1, ← _root_.mul_inv_rev, h2r]
  exact inv_eq_of_mul_eq_one_right (zEltU_mul_self _)

end Block

section Chain

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {m : ℕ}

theorem chainPair_suModel (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hm : 2 ≤ m) :
    ∃ (R₁ R₂ : Subgroup (Su K p f (m + 1))) (τ₁ τ₂ ν₁ ν₂ : Su K p f (m + 1)),
      R₁ ∈ longRootSetU (K := K) (p := p) (f := f) (by omega : 2 ≤ m + 1) ∧
      R₂ ∈ longRootSetU (K := K) (p := p) (f := f) (by omega : 2 ≤ m + 1) ∧
      ChainPairData (longRootSetU (K := K) (p := p) (f := f) (by omega : 2 ≤ m + 1)) R₁ R₂ τ₁ τ₂
        ν₁ ν₂ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have h2F : (2 : CFSG.LieType.Steinberg.fixedSubfield K p f) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card _ (odd_natCard_fixedSubfield hK hp)
  have hn : 2 ≤ m + 1 := by omega
  have hn0 : 0 < m + 1 := by omega
  set a₀ : Fin (m + 1) := ⟨0, by omega⟩ with ha₀
  set a₁ : Fin (m + 1) := ⟨1, by omega⟩ with ha₁
  set a₂ : Fin (m + 1) := ⟨2, by omega⟩ with ha₂
  have h01 : a₀ ≠ a₁ := fun h => by simpa [ha₀, ha₁] using congrArg Fin.val h
  have h12 : a₁ ≠ a₂ := fun h => by simpa [ha₁, ha₂] using congrArg Fin.val h
  have h02 : a₀ ≠ a₂ := fun h => by simpa [ha₀, ha₂] using congrArg Fin.val h
  let T₂ : Pair (m + 1) := ⟨{a₀, a₁}, Finset.card_pair h01⟩
  let T₁ : Pair (m + 1) := ⟨{a₁, a₂}, Finset.card_pair h12⟩
  let T₃ : Pair (m + 1) := ⟨{a₀, a₂}, Finset.card_pair h02⟩
  have hR₁ : LcU K p f T₁ ∈ longRootSetU (K := K) (p := p) (f := f) hn :=
    LcU_mem_longRootSetU h2 hn T₁
  have hR₂ : LcU K p f T₂ ∈ longRootSetU (K := K) (p := p) (f := f) hn :=
    LcU_mem_longRootSetU h2 hn T₂
  have hcenter : ∀ (T : Pair (m + 1)) (c : Su K p f (m + 1)), c ∈ LcU K p f T →
      (∀ r ∈ LcU K p f T, c * r = r * c) → c = 1 ∨ c = zEltU K p f T := fun T c hc hcc =>
    eq_one_or_eq_of_isClassicalSL2_center h2F
      ((isLongRootSU2_LcU (p := p) (f := f) h2 hn T).isClassicalSL2 hK hp) hc hcc
  have hU₁ := isUniqueInvolution_LcU hK hp hn T₁
  have hU₂ := isUniqueInvolution_LcU hK hp hn T₂
  have hcomm : zEltU K p f T₁ * zEltU K p f T₂ = zEltU K p f T₂ * zEltU K p f T₁ :=
    signGroupU_comm (zEltU_mem_signGroupU T₁) (zEltU_mem_signGroupU T₂)
  have hprod : zEltU K p f T₁ * zEltU K p f T₂ = zEltU K p f T₃ := by
    rw [hcomm]
    apply suMat_injective
    rw [suMat_mul, suMat_zEltU, suMat_zEltU, suMat_zEltU]
    exact zMat_pair_mul h01 h12 h02
  have hsq₁ := zEltU_mul_self (K := K) (p := p) (f := f) T₁
  have hsq₂ := zEltU_mul_self (K := K) (p := p) (f := f) T₂
  refine ⟨LcU K p f T₁, LcU K p f T₂, zEltU K p f T₁, zEltU K p f T₂,
    monoSU K p f hn0 (Equiv.swap a₀ a₂), monoSU K p f hn0 (Equiv.swap a₀ a₁), hR₁, hR₂, ?_⟩
  have hLc₂ : LcU K p f T₂ = (blockEmb K p f (m + 1) 2 0 (by omega)).range := by
    unfold LcU
    rw [range_blockEmb_eq_longRootGroupSU h2 (by omega : 0 + 2 ≤ m + 1),
      negBlock_eq_zMat (by omega : 0 + 2 ≤ m + 1)]
  have hr : blockEmb K p f (m + 1) 2 0 (by omega) (wSU K p f) ∈ LcU K p f T₂ := by
    rw [hLc₂]
    exact ⟨_, rfl⟩
  have hent₁ : entU (zEltU K p f T₁) a₀ ≠ entU (zEltU K p f T₁) a₁ := by
    rw [zEltU_entU, zEltU_entU]
    simp only [T₁, Finset.mem_insert, Finset.mem_singleton, h01, h02, or_self, ite_false,
      true_or, ite_true]
    intro h
    exact h2 (by linear_combination h)
  have hT1 : T₂.1 = T₁.1.map (Equiv.swap a₀ a₂).toEmbedding := by
    show ({a₀, a₁} : Finset (Fin (m + 1))) =
      Finset.map (Equiv.swap a₀ a₂).toEmbedding {a₁, a₂}
    rw [Finset.map_insert, Finset.map_singleton]
    simp only [Equiv.coe_toEmbedding, Equiv.swap_apply_of_ne_of_ne h01.symm h12,
      Equiv.swap_apply_right]
    exact Finset.pair_comm _ _
  have hT1' : T₁.1 = T₂.1.map (Equiv.swap a₀ a₂).toEmbedding := by
    show ({a₁, a₂} : Finset (Fin (m + 1))) =
      Finset.map (Equiv.swap a₀ a₂).toEmbedding {a₀, a₁}
    rw [Finset.map_insert, Finset.map_singleton]
    simp only [Equiv.coe_toEmbedding, Equiv.swap_apply_of_ne_of_ne h01.symm h12,
      Equiv.swap_apply_left]
    exact Finset.pair_comm _ _
  have hT2 : T₃.1 = T₁.1.map (Equiv.swap a₀ a₁).toEmbedding := by
    show ({a₀, a₂} : Finset (Fin (m + 1))) =
      Finset.map (Equiv.swap a₀ a₁).toEmbedding {a₁, a₂}
    rw [Finset.map_insert, Finset.map_singleton]
    simp only [Equiv.coe_toEmbedding, Equiv.swap_apply_of_ne_of_ne h02.symm h12.symm,
      Equiv.swap_apply_right]
  have hT2' : T₂.1 = T₂.1.map (Equiv.swap a₀ a₁).toEmbedding := by
    show ({a₀, a₁} : Finset (Fin (m + 1))) =
      Finset.map (Equiv.swap a₀ a₁).toEmbedding {a₀, a₁}
    rw [Finset.map_insert, Finset.map_singleton]
    simp only [Equiv.coe_toEmbedding, Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact Finset.pair_comm _ _
  exact
    { mem₁ := hU₁.mem
      mem₂ := hU₂.mem
      center₁ := hcenter T₁
      center₂ := hcenter T₂
      sq₁ := hsq₁
      sq₂ := hsq₂
      comm := hcomm
      prod_not_central := by
        rw [hprod]
        exact zEltU_not_central h2 hn0 T₃ (x := a₂) (y := a₁) (by simp [T₃]) (by
          simp [T₃, h01.symm, h12])
      not_central := ⟨_, hr, by
        rw [commutator_blockEmb_eq hn (zEltU_mem_signGroupU T₁) hent₁]
        exact zEltU_not_central h2 hn0 T₂ (x := a₁) (y := a₂) (by simp [T₂]) (by
          simp [T₂, h02.symm, h12.symm])⟩
      swap₁ := monoSU_conj_zEltU hn0 _ T₁ T₂ hT1
      swap₁' := monoSU_conj_zEltU hn0 _ T₂ T₁ hT1'
      swap₂ := (monoSU_conj_zEltU hn0 _ T₁ T₃ hT2).trans hprod.symm
      swap₂' := monoSU_conj_zEltU hn0 _ T₂ T₂ hT2'
      gen := iSup_longRootSetU_centralizing hK hp (m := m) (by omega) hsq₁ hsq₂ hcomm }

end Chain

section PSU

variable {p : ℕ} [Fact p.Prime]

theorem chainPair_psu (hp2 : p ≠ 2) {n e : ℕ} (hadm : StatedLieAdmissible .PSU n p e) :
    ChainPair (Generic.fundamentalSubgroups .PSU (Generic.modelUniv .PSU n p e Fact.out).D) := by
  have hf : 1 ≤ e := hadm.2.1
  have hn3 : 3 ≤ n := hadm.2.2.1
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  have : NeZero (2 * e) := ⟨by omega⟩
  have hK := CFSG.LieType.Universal.card_galoisField_two_mul p e hf
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨R₁, R₂, τ₁, τ₂, ν₁, ν₂, hR₁, hR₂, hd⟩ :=
    chainPair_suModel (K := GaloisField p (2 * e)) (p := p) (f := e) hK hp2 (by omega : 2 ≤ m)
  have hCP : ChainPair (longRootSetU (K := GaloisField p (2 * e)) (p := p) (f := e)
      (by omega : 2 ≤ m + 1)) := ⟨R₁, hR₁, R₂, hR₂, τ₁, τ₂, ν₁, ν₂, hd⟩
  refine ChainPair.of_mulEquiv φ.symm (fun R => ?_) hCP
  rw [hφ]
  have hRR : (R.map φ.symm.toMonoidHom).map φ.toMonoidHom = R := by
    rw [Subgroup.map_map]
    ext x
    simp
  rw [hRR]

theorem chainPair_model (hp2 : p ≠ 2) (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n e : ℕ)
    (ht : t = .PSL ∨ t = .PSU) (hn : 3 ≤ n) (hadm : StatedLieAdmissible t n p e) :
    ChainPair (Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D) := by
  rcases ht with rfl | rfl
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact chainPair_psl hp2 (by omega : 2 ≤ m)
  · exact chainPair_psu hp2 hadm

end PSU

end CFSG.ClassicalInvolution.Asc77
