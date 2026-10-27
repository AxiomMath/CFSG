module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81EightThirteenKnownCore
import CFSG.ClassicalInvolution.Phan.Standard
import CFSG.RankThree.PartTwo.KFacts.KS21FusionU58
import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Extra
public import CFSG.ClassicalGroups.Unitary.Generation

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

section Planes

variable {M : Type*} [Group M]

private theorem uni_mem_normalizer_of_commute {g a b : M} (ha : g * a = a * g)
    (hb : g * b = b * g) :
    g ∈ Subgroup.normalizer (Subgroup.closure ({a, b} : Set M) : Set M) := by
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro x (rfl | rfl)
  · exact ha.symm
  · exact hb.symm

private theorem uni_mem_normalizer_of_conj [Finite M] {g a b : M}
    (ha : g * a * g⁻¹ ∈ Subgroup.closure ({a, b} : Set M))
    (hb : g * b * g⁻¹ ∈ Subgroup.closure ({a, b} : Set M)) :
    g ∈ Subgroup.normalizer (Subgroup.closure ({a, b} : Set M) : Set M) := by
  set X := Subgroup.closure ({a, b} : Set M)
  have hle : X.map (MulAut.conj g).toMonoidHom ≤ X := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, (rfl | rfl), rfl⟩
    · exact ha
    · exact hb
  have heq : X.map (MulAut.conj g).toMonoidHom = X :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨fun hs => hle ⟨s, hs, rfl⟩, fun hs => ?_⟩
  rw [← heq] at hs
  obtain ⟨t, ht, hts⟩ := hs
  have : t = s := by simpa [MulAut.conj_apply] using hts
  rwa [← this]

private theorem uni_not_mem_zpowers {x y h : M} (hx : h * x = x * h) (hy : h * y ≠ y * h) :
    y ∉ Subgroup.zpowers x := by
  intro hm
  have hle : Subgroup.zpowers x ≤ Subgroup.centralizer ({h} : Set M) :=
    (Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 hx.symm)
  exact hy (Subgroup.mem_centralizer_singleton_iff.1 (hle hm)).symm

private theorem uni_not_mem_closure {a b x h : M} (ha : h * a = a * h) (hb : h * b = b * h)
    (hx : h * x ≠ x * h) : x ∉ Subgroup.closure ({a, b} : Set M) := by
  intro hm
  have hle : Subgroup.closure ({a, b} : Set M) ≤ Subgroup.centralizer ({h} : Set M) := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 ha.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 hb.symm
  exact hx (Subgroup.mem_centralizer_singleton_iff.1 (hle hm)).symm

private theorem uni_threePlaneGen [Finite M] {a₁ b₁ a₂ b₂ : M}
    (hc : ∀ x ∈ ({a₁, b₁, a₂, b₂} : Set M), ∀ y ∈ ({a₁, b₁, a₂, b₂} : Set M), x * y = y * x)
    (h3 : ∀ x ∈ ({a₁, b₁, a₂, b₂} : Set M), x ^ 3 = 1)
    (ha₁ : a₁ ≠ 1) (hb₁ : b₁ ∉ Subgroup.zpowers a₁) (ha₂ : a₂ ≠ 1)
    (hb₂ : b₂ ∉ Subgroup.zpowers a₂) (hsep : a₂ ∉ Subgroup.closure ({a₁, b₁} : Set M))
    (hgen : Subgroup.normalizer (Subgroup.closure ({a₁, b₁} : Set M) : Set M) ⊔
      Subgroup.normalizer (Subgroup.closure ({a₂, b₂} : Set M) : Set M) = ⊤) :
    ThreePlaneGen M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X₁ := Subgroup.closure ({a₁, b₁} : Set M) with hX₁
  set X₂ := Subgroup.closure ({a₂, b₂} : Set M) with hX₂
  have hE : X₁ ⊔ X₂ = Subgroup.closure ({a₁, b₁, a₂, b₂} : Set M) := by
    rw [hX₁, hX₂, ← Subgroup.closure_union]
    congr 1
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hEl : IsElemAbelian 3 (X₁ ⊔ X₂) := by
    rw [hE]
    exact IsElemAbelian.closure_of_commute hc h3
  have h1 : Nat.card X₁ = 3 ^ 2 :=
    CFSG.HardMathSupport.Dickson.I271.card_closure_pair_sq (hc a₁ (by simp) b₁ (by simp))
      (h3 a₁ (by simp)) (h3 b₁ (by simp)) ha₁ hb₁
  have h2 : Nat.card X₂ = 3 ^ 2 :=
    CFSG.HardMathSupport.Dickson.I271.card_closure_pair_sq (hc a₂ (by simp) b₂ (by simp))
      (h3 a₂ (by simp)) (h3 b₂ (by simp)) ha₂ hb₂
  have hp : IsPGroup 3 ↥(X₁ ⊔ X₂) := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact hEl.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hdvd : 3 ^ 2 ∣ 3 ^ k := by
    rw [← h1, ← hk]
    exact Subgroup.card_dvd_of_le le_sup_left
  have hk2 : 2 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  have hk3 : k ≠ 2 := by
    rintro rfl
    apply hsep
    have heq : X₁ = X₁ ⊔ X₂ := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hk, h1])
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  exact ⟨X₁ ⊔ X₂, X₁, X₂, k, hEl, by omega, hk, le_sup_left, h1, le_sup_right, h2, hgen⟩

end Planes

section Monomial

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

private noncomputable def uniDiag (σ : F ≃+* F) (δ : Fin n → F) (hu : ∀ i, σ (δ i) * δ i = 1)
    (h1 : ∏ i, δ i = 1) : SUid σ n :=
  mkSU σ (diagonal δ) (by rw [det_diagonal, h1]) fun x y => by
    rw [herm_def, herm_def]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mulVec_diagonal, mulVec_diagonal, map_mul]
    linear_combination (σ (x i) * y i) * hu i

private theorem uniDiag_smul {δ : Fin n → F} {hu : ∀ i, σ (δ i) * δ i = 1}
    {h1 : ∏ i, δ i = 1} (v : Fin n → F) : uniDiag σ δ hu h1 • v = δ * v := by
  funext i
  exact mulVec_diagonal δ v i

private theorem uniDiag_mul_comm {δ δ' : Fin n → F} {hu : ∀ i, σ (δ i) * δ i = 1}
    {h1 : ∏ i, δ i = 1} {hu' : ∀ i, σ (δ' i) * δ' i = 1} {h1' : ∏ i, δ' i = 1} :
    uniDiag σ δ hu h1 * uniDiag σ δ' hu' h1' = uniDiag σ δ' hu' h1' * uniDiag σ δ hu h1 :=
  ext_smul _ fun v => by
    rw [mul_smul, mul_smul, uniDiag_smul, uniDiag_smul, uniDiag_smul, uniDiag_smul]
    ring

private theorem uniDiag_pow_three {δ : Fin n → F} {hu : ∀ i, σ (δ i) * δ i = 1}
    {h1 : ∏ i, δ i = 1} (h : ∀ i, δ i ^ 3 = 1) : uniDiag σ δ hu h1 ^ 3 = 1 :=
  ext_smul _ fun v => by
    rw [pow_three, mul_smul, mul_smul, uniDiag_smul, uniDiag_smul, uniDiag_smul, one_smul]
    funext i
    simp only [Pi.mul_apply]
    linear_combination v i * h i

private theorem uni_commute_diag {g : SUid σ n} {δ : Fin n → F} {hu : ∀ i, σ (δ i) * δ i = 1}
    {h1 : ∏ i, δ i = 1}
    (h : ∀ a b, a ≠ b → ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a b ≠ 0 → δ a = δ b) :
    g * uniDiag σ δ hu h1 = uniDiag σ δ hu h1 * g := by
  apply Subtype.ext
  apply Units.ext
  change ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * diagonal δ =
    diagonal δ * ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  ext a b
  rw [mul_diagonal, diagonal_mul]
  by_cases hab : a = b
  · subst hab
    exact mul_comm _ _
  · by_cases h0 : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a b = 0
    · rw [h0, zero_mul, mul_zero]
    · rw [h a b hab h0, mul_comm]

private theorem uni_det_perm (h2 : (2 : F) = 0) (π : Equiv.Perm (Fin n)) :
    (π.permMatrix F).det = 1 := by
  rw [det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> rw [h]
  · simp
  · have : (-1 : F) = 1 := by linear_combination -h2
    simpa using this

private noncomputable def uniPerm (σ : F ≃+* F) (h2 : (2 : F) = 0) (π : Equiv.Perm (Fin n)) :
    SUid σ n :=
  mkSU σ (π.permMatrix F) (uni_det_perm h2 π) fun x y => by
    rw [permMatrix_mulVec, permMatrix_mulVec, herm_def, herm_def]
    exact Equiv.sum_comp π (fun i => σ (x i) * y i)

private theorem uniPerm_smul {h2 : (2 : F) = 0} {π : Equiv.Perm (Fin n)} (v : Fin n → F) :
    uniPerm σ h2 π • v = v ∘ π :=
  permMatrix_mulVec π

private theorem uniPerm_mul {h2 : (2 : F) = 0} (π ρ : Equiv.Perm (Fin n)) :
    uniPerm σ h2 (π * ρ) = uniPerm σ h2 ρ * uniPerm σ h2 π :=
  ext_smul _ fun v => by
    rw [mul_smul, uniPerm_smul, uniPerm_smul, uniPerm_smul]
    rfl

private theorem uni_perm_apply_ne_zero {π : Equiv.Perm (Fin n)} {a b : Fin n}
    (h : (π.permMatrix F) a b ≠ 0) : π a = b := by
  by_contra hne
  exact h (by simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hne])

private theorem uni_commute_swap {h2 : (2 : F) = 0} {i j : Fin n} {δ : Fin n → F}
    {hu : ∀ i, σ (δ i) * δ i = 1} {h1 : ∏ i, δ i = 1} (h : δ i = δ j) :
    uniPerm σ h2 (Equiv.swap i j) * uniDiag σ δ hu h1 =
      uniDiag σ δ hu h1 * uniPerm σ h2 (Equiv.swap i j) := by
  refine uni_commute_diag fun a b _ hab => ?_
  rw [← uni_perm_apply_ne_zero hab]
  rcases eq_or_ne a i with rfl | hai
  · rw [Equiv.swap_apply_left, h]
  · rcases eq_or_ne a j with rfl | haj
    · rw [Equiv.swap_apply_right, h]
    · rw [Equiv.swap_apply_of_ne_of_ne hai haj]

private theorem uniPerm_one {h2 : (2 : F) = 0} : uniPerm σ h2 (1 : Equiv.Perm (Fin n)) = 1 :=
  ext_smul _ fun v => by rw [uniPerm_smul, one_smul]; rfl

private theorem uni_perm_conj_smul {h2 : (2 : F) = 0} (π : Equiv.Perm (Fin n)) {δ : Fin n → F}
    {hu : ∀ i, σ (δ i) * δ i = 1} {h1 : ∏ i, δ i = 1} (v : Fin n → F) :
    (uniPerm σ h2 π * uniDiag σ δ hu h1 * (uniPerm σ h2 π)⁻¹) • v = (δ ∘ π) * v := by
  have hinv : (uniPerm σ h2 π)⁻¹ • v = v ∘ π.symm := by
    rw [inv_smul_eq_iff, uniPerm_smul]
    funext k
    simp
  rw [mul_smul, mul_smul, hinv, uniDiag_smul, uniPerm_smul]
  funext k
  simp

private theorem uni_swap_scalar {h2 : (2 : F) = 0} {p q : Fin n} {δ : Fin n → F}
    {hu : ∀ i, σ (δ i) * δ i = 1} {h1 : ∏ i, δ i = 1} {c : F}
    (h : ∀ v : Fin n → F, (uniDiag σ δ hu h1 * uniPerm σ h2 (Equiv.swap p q)) • v =
      c • ((uniPerm σ h2 (Equiv.swap p q) * uniDiag σ δ hu h1) • v)) (k : Fin n) :
    δ (Equiv.swap p q k) = c * δ k := by
  have e := congrFun (h (Pi.single k 1)) (Equiv.swap p q k)
  simpa [mul_smul, uniDiag_smul, uniPerm_smul, Pi.single_apply] using e

private theorem uni_swap_ne {h2 : (2 : F) = 0} {p q r : Fin n} {δ : Fin n → F}
    {hu : ∀ i, σ (δ i) * δ i = 1} {h1 : ∏ i, δ i = 1} (hrp : r ≠ p) (hrq : r ≠ q)
    (hne : δ p ≠ δ q) (hr : δ r ≠ 0) {c : F}
    (h : ∀ v : Fin n → F, (uniDiag σ δ hu h1 * uniPerm σ h2 (Equiv.swap p q)) • v =
      c • ((uniPerm σ h2 (Equiv.swap p q) * uniDiag σ δ hu h1) • v)) : False := by
  have e1 := uni_swap_scalar h r
  rw [Equiv.swap_apply_of_ne_of_ne hrp hrq] at e1
  have hc : c = 1 := by
    have : (c - 1) * δ r = 0 := by linear_combination -e1
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hr)
  have e2 := uni_swap_scalar h p
  rw [Equiv.swap_apply_left, hc, one_mul] at e2
  exact hne e2.symm

private theorem uni_swap_not_comm {h2 : (2 : F) = 0} {p q r : Fin n} {δ : Fin n → F}
    {hu : ∀ i, σ (δ i) * δ i = 1} {h1 : ∏ i, δ i = 1} (hrp : r ≠ p) (hrq : r ≠ q)
    (hne : δ p ≠ δ q) (hr : δ r ≠ 0) :
    uniPerm σ h2 (Equiv.swap p q) * uniDiag σ δ hu h1 ≠
      uniDiag σ δ hu h1 * uniPerm σ h2 (Equiv.swap p q) := fun h =>
  uni_swap_ne hrp hrq hne hr (c := 1) fun v => by rw [one_smul, h]

private theorem uniDiag_ne_one {δ : Fin n → F} {hu : ∀ i, σ (δ i) * δ i = 1}
    {h1 : ∏ i, δ i = 1} {p : Fin n} (hp : δ p ≠ 1) : uniDiag σ δ hu h1 ≠ 1 := fun h => by
  have e := congrFun (uniDiag_smul (hu := hu) (h1 := h1) (Pi.single p 1)) p
  rw [h, one_smul] at e
  simp at e
  exact hp e.symm

end Monomial

section Two

open CFSG.Fischer.Classification.Unitary
open CFSG.Blueprint.Fischer (K)
open CFSG.ClassicalInvolution.Phan (blockGL blockGL_mem_SUid blockMat blockMat_apply
  blockMat_mulVec_blockIdx blockMat_mulVec_of_not_mem blockIdx)
open CFSG.RankThree.PartTwo.KFacts.KS21.DFT (dftMat dftInvMat dftGL coe_dftGL det_dftMat
  dftInvMat_mul_dftMat)

variable {n : ℕ}

private theorem uni_cube {c : K} (hc : c ≠ 0) : c ^ 3 = 1 := by
  have h := frob_mul_self hc
  rw [frob_apply] at h
  linear_combination h

private theorem uni_omega_sq : ω ^ 2 + ω + 1 = 0 := by
  have h := frob_omega
  rw [frob_apply] at h
  rw [h]
  linear_combination (ω + 1) * two_eq_zero

private theorem uni_omega_sq_ne : ω ^ 2 ≠ ω := by
  intro h
  apply omega_ne_one
  have h' : ω * (ω - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h' with h0 | h0
  · exact absurd h0 omega_ne_zero
  · exact sub_eq_zero.1 h0

private theorem uni_omega_sq_ne_zero : ω ^ 2 ≠ 0 := pow_ne_zero 2 omega_ne_zero

private theorem uni_conjTr_dft : conjTr frob (dftMat ω) = dftInvMat ω := by
  have h3 : ω ^ 3 = 1 := uni_cube omega_ne_zero
  have h4 : ω ^ 4 = ω := by rw [show 4 = 3 + 1 by rfl, pow_succ, h3, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, dftMat, dftInvMat, frobenius_def, ← pow_mul, h4]

private abbrev uniIdx (h : 3 ≤ n) (x : Fin 3) : Fin n := blockIdx 0 (show 0 + 3 ≤ n by omega) x

private noncomputable def uniF3 : SUid frob 3 :=
  ⟨dftGL two_eq_zero uni_omega_sq, det_dftMat two_eq_zero uni_omega_sq, by
    rw [coe_dftGL, uni_conjTr_dft]
    exact dftInvMat_mul_dftMat two_eq_zero uni_omega_sq⟩

private noncomputable def uniFourier (n : ℕ) (h : 3 ≤ n) : SUid frob n :=
  ⟨blockGL n 0 (by omega) (uniF3 : GL (Fin 3) K), blockGL_mem_SUid frob (by omega) uniF3.2⟩

private theorem coe_uniFourier (h : 3 ≤ n) :
    (((uniFourier n h : SUid frob n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      blockMat n 0 (dftMat ω) :=
  rfl

private theorem uniFourier_smul_block (h : 3 ≤ n) (c : Fin n → K)
    (hc : ∀ x : Fin 3, c (uniIdx h x) = 1) (x : Fin 3) :
    (uniFourier n h • c) (uniIdx h x) = if x = 0 then 1 else 0 := by
  rw [smul_def, coe_uniFourier, uniIdx, blockMat_mulVec_blockIdx]
  have : (fun y => c (blockIdx 0 (show 0 + 3 ≤ n by omega) y)) = fun _ => (1 : K) := funext hc
  rw [this]
  have h3 : (1 : K) + 1 + 1 = 1 := by linear_combination two_eq_zero
  have h1 : (1 : K) + ω + ω ^ 2 = 0 := by linear_combination uni_omega_sq
  have h2 : (1 : K) + ω ^ 2 + ω = 0 := by linear_combination uni_omega_sq
  fin_cases x <;> simp [dftMat, mulVec, dotProduct, Fin.sum_univ_three, h1, h2, h3]

private theorem uniFourier_smul_of_le (h : 3 ≤ n) (c : Fin n → K) {k : Fin n}
    (hk : 3 ≤ k.val) : (uniFourier n h • c) k = c k := by
  rw [smul_def, coe_uniFourier]
  exact blockMat_mulVec_of_not_mem _ c (by omega)

private theorem uniFourier_entry {h : 3 ≤ n} {a b : Fin n} (hab : a ≠ b)
    (h0 : (((uniFourier n h : SUid frob n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ≠ 0) :
    a.val < 3 ∧ b.val < 3 := by
  rw [coe_uniFourier, blockMat_apply] at h0
  split_ifs at h0 with hblk
  · omega
  · exact absurd (one_apply_ne hab) h0

private theorem uni_commute_tvU {v : Fin n → K} (hv : herm frob v v = 0) {δ : Fin n → K}
    {hu : ∀ i, frob (δ i) * δ i = 1} {h1 : ∏ i, δ i = 1} {c : K}
    (hc : ∀ i, v i ≠ 0 → δ i = c) :
    tvU v * uniDiag frob δ hu h1 = uniDiag frob δ hu h1 * tvU v := by
  refine ext_smul _ fun x => ?_
  rw [mul_smul, mul_smul, uniDiag_smul, uniDiag_smul, tvU_smul hv, tvU_smul hv]
  have hh : herm frob v (δ * x) = c * herm frob v x := by
    rw [herm_def, herm_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : v i = 0
    · simp [h]
    · simp only [Pi.mul_apply]
      rw [hc i h]
      ring
  rw [hh]
  funext i
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : v i = 0
  · simp [h]
  · rw [hc i h]
    ring

private theorem uni_tvU_move {H : Subgroup (SUid frob n)} {g : SUid frob n} (hg : g ∈ H)
    {a : Fin n → K} (ha : herm frob a a = 0) (h : tvU (g • a) ∈ H) : tvU a ∈ H := by
  have e := conj_tvU g ha
  have : tvU a = g⁻¹ * tvU (g • a) * g := by rw [← e]; group
  rw [this]
  exact H.mul_mem (H.mul_mem (H.inv_mem hg) h) hg

private theorem uni_inj2 {α : Type*} {i j : α} (hij : i ≠ j) : Function.Injective ![i, j] := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all [eq_comm]

private theorem uni_inj3 {α : Type*} {i j l : α} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    Function.Injective ![i, j, l] := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all [eq_comm]

section Supp

open Classical

private noncomputable def uniSupp (a : Fin n → K) : ℕ :=
  (Finset.univ.filter fun i => a i ≠ 0).card

private theorem uniSupp_def (a : Fin n → K) :
    uniSupp a = (Finset.univ.filter fun i => a i ≠ 0).card :=
  rfl

private theorem uniSupp_comp (π : Equiv.Perm (Fin n)) (a : Fin n → K) :
    uniSupp (a ∘ π) = uniSupp a := by
  rw [uniSupp_def, uniSupp_def, Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp π (fun k => if a k ≠ 0 then 1 else 0)

private theorem uniSupp_mul {δ : Fin n → K} (hδ : ∀ i, δ i ≠ 0) (b : Fin n → K) :
    uniSupp (δ * b) = uniSupp b := by
  rw [uniSupp_def, uniSupp_def]
  congr 1
  exact Finset.filter_congr fun i _ => by simp [hδ i]

private theorem uniSupp_eq_zero {a : Fin n → K} (h : uniSupp a = 0) : a = 0 := by
  funext i
  by_contra hi
  rw [uniSupp_def, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  exact h (Finset.mem_univ i) hi

private theorem uniSupp_ne_one {a : Fin n → K} (ha : herm frob a a = 0) : uniSupp a ≠ 1 := by
  intro h
  rw [uniSupp_def, Finset.card_eq_one] at h
  obtain ⟨i, hi⟩ := h
  have hmem : ∀ j, a j ≠ 0 ↔ j = i := fun j => by
    have := congrArg (j ∈ ·) hi
    simpa using this
  have hz : ∀ j, j ≠ i → a j = 0 := fun j hj => by_contra fun h => hj ((hmem j).1 h)
  have hai : a i ≠ 0 := (hmem i).2 rfl
  have : herm frob a a = frob (a i) * a i := by
    rw [herm_def, Finset.sum_eq_single i (fun j _ hj => by rw [hz j hj, mul_zero]) (by simp)]
  rw [this, frob_mul_self hai] at ha
  exact one_ne_zero ha

private theorem uniSupp_eq_two {a : Fin n → K} (h : uniSupp a = 2) :
    ∃ i j, i ≠ j ∧ ∀ k, a k ≠ 0 → k = i ∨ k = j := by
  rw [uniSupp_def, Finset.card_eq_two] at h
  obtain ⟨i, j, hij, hs⟩ := h
  refine ⟨i, j, hij, fun k hk => ?_⟩
  have : k ∈ Finset.univ.filter fun i => a i ≠ 0 := by simp [hk]
  rw [hs] at this
  simpa using this

private theorem uniSupp_three {a : Fin n → K} (h : 3 ≤ uniSupp a) :
    ∃ i j l, a i ≠ 0 ∧ a j ≠ 0 ∧ a l ≠ 0 ∧ i ≠ j ∧ i ≠ l ∧ j ≠ l := by
  rw [uniSupp_def] at h
  obtain ⟨i, j, l, hi, hj, hl, hij, hil, hjl⟩ := Finset.two_lt_card_iff.1
    (by omega : 2 < (Finset.univ.filter fun i => a i ≠ 0).card)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj hl
  exact ⟨i, j, l, hi, hj, hl, hij, hil, hjl⟩

private theorem uniIdx_val (h : 3 ≤ n) (x : Fin 3) : (uniIdx h x).val = x.val := by
  simp [uniIdx, blockIdx]

private theorem uniIdx_injective (h : 3 ≤ n) : Function.Injective (uniIdx h) :=
  CFSG.ClassicalInvolution.Phan.blockIdx_injective _

private theorem uniSupp_fourier (h : 3 ≤ n) {c : Fin n → K} (hc : ∀ x : Fin 3, c (uniIdx h x) = 1) :
    uniSupp (uniFourier n h • c) + 2 = uniSupp c := by
  have h12 : uniIdx h 1 ≠ uniIdx h 2 := (uniIdx_injective h).ne (by decide)
  have hd : (Finset.univ.filter fun i => (uniFourier n h • c) i ≠ 0) =
      ((Finset.univ.filter fun i => c i ≠ 0).erase (uniIdx h 1)).erase (uniIdx h 2) := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hk : 3 ≤ k.val
    · have h1 : k ≠ uniIdx h 1 := fun e => by rw [e, uniIdx_val] at hk; simp at hk
      have h2 : k ≠ uniIdx h 2 := fun e => by rw [e, uniIdx_val] at hk; simp at hk
      rw [uniFourier_smul_of_le h c hk]
      tauto
    · obtain ⟨x, rfl⟩ : ∃ x : Fin 3, uniIdx h x = k :=
        ⟨⟨k.val, by omega⟩, Fin.ext (by rw [uniIdx_val])⟩
      rw [uniFourier_smul_block h c hc x, hc x]
      fin_cases x <;> simp [(uniIdx_injective h).eq_iff]
  have hm1 : uniIdx h 1 ∈ Finset.univ.filter fun i => c i ≠ 0 := by simp [hc 1]
  have hm2 : uniIdx h 2 ∈ (Finset.univ.filter fun i => c i ≠ 0).erase (uniIdx h 1) := by
    simp [hc 2, h12.symm]
  have hpos := Finset.card_pos.2 ⟨_, hm2⟩
  rw [Finset.card_erase_of_mem hm1] at hpos
  rw [uniSupp_def, uniSupp_def, hd, Finset.card_erase_of_mem hm2, Finset.card_erase_of_mem hm1]
  omega

end Supp

private theorem uni_exists_diag (hn : 4 ≤ n) (b : Fin n → K)
    (hb : ∀ x : Fin 3, b (uniIdx (by omega) x) ≠ 0) :
    ∃ (δ : Fin n → K) (hu : ∀ i, frob (δ i) * δ i = 1) (_ : ∏ i, δ i = 1),
      (∀ i, δ i ≠ 0) ∧ ∀ x : Fin 3, (δ * b) (uniIdx (by omega) x) = 1 := by
  have h3 : 3 ≤ n := by omega
  set i₀ := uniIdx h3 0
  set i₁ := uniIdx h3 1
  set i₂ := uniIdx h3 2
  set i₃ : Fin n := ⟨3, by omega⟩
  have v₀ : i₀.val = 0 := uniIdx_val h3 0
  have v₁ : i₁.val = 1 := uniIdx_val h3 1
  have v₂ : i₂.val = 2 := uniIdx_val h3 2
  have h01 : i₀ ≠ i₁ := fun e => by rw [Fin.ext_iff, v₀, v₁] at e; simp at e
  have h02 : i₀ ≠ i₂ := fun e => by rw [Fin.ext_iff, v₀, v₂] at e; simp at e
  have h03 : i₀ ≠ i₃ := fun e => by rw [Fin.ext_iff, v₀] at e; simp [i₃] at e
  have h12 : i₁ ≠ i₂ := fun e => by rw [Fin.ext_iff, v₁, v₂] at e; simp at e
  have h13 : i₁ ≠ i₃ := fun e => by rw [Fin.ext_iff, v₁] at e; simp [i₃] at e
  have h23 : i₂ ≠ i₃ := fun e => by rw [Fin.ext_iff, v₂] at e; simp [i₃] at e
  have hb0 : b i₀ ≠ 0 := hb 0
  have hb1 : b i₁ ≠ 0 := hb 1
  have hb2 : b i₂ ≠ 0 := hb 2
  set δ : Fin n → K := Pi.mulSingle i₀ (b i₀)⁻¹ * Pi.mulSingle i₁ (b i₁)⁻¹ *
    Pi.mulSingle i₂ (b i₂)⁻¹ * Pi.mulSingle i₃ (b i₀ * b i₁ * b i₂) with hδ
  have hne : ∀ i, δ i ≠ 0 := by
    intro i
    simp only [hδ, Pi.mul_apply, Pi.mulSingle_apply]
    have : b i₀ * b i₁ * b i₂ ≠ 0 := mul_ne_zero (mul_ne_zero hb0 hb1) hb2
    split_ifs <;> simp_all
  refine ⟨δ, fun i => frob_mul_self (hne i), ?_, hne, fun x => ?_⟩
  · simp only [hδ, Pi.mul_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Fintype.prod_pi_mulSingle', Fintype.prod_pi_mulSingle', Fintype.prod_pi_mulSingle',
      Fintype.prod_pi_mulSingle']
    field_simp
  · fin_cases x
    · show δ i₀ * b i₀ = 1
      simp only [hδ, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h01,
        Pi.mulSingle_eq_of_ne h02, Pi.mulSingle_eq_of_ne h03, mul_one]
      exact inv_mul_cancel₀ hb0
    · show δ i₁ * b i₁ = 1
      simp only [hδ, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h01.symm,
        Pi.mulSingle_eq_of_ne h12, Pi.mulSingle_eq_of_ne h13, mul_one, one_mul]
      exact inv_mul_cancel₀ hb1
    · show δ i₂ * b i₂ = 1
      simp only [hδ, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h02.symm,
        Pi.mulSingle_eq_of_ne h12.symm, Pi.mulSingle_eq_of_ne h23, mul_one, one_mul]
      exact inv_mul_cancel₀ hb2

private theorem uni_eq_top (hn : 4 ≤ n) {H : Subgroup (SUid frob n)}
    (hD : ∀ (δ : Fin n → K) (hu : ∀ i, frob (δ i) * δ i = 1) (h1 : ∏ i, δ i = 1),
      uniDiag frob δ hu h1 ∈ H)
    (hP : ∀ π : Equiv.Perm (Fin n), uniPerm frob two_eq_zero π ∈ H)
    (hF : uniFourier n (by omega) ∈ H)
    (hT : ∀ v : Fin n → K, herm frob v v = 0 → (∀ k : Fin n, 2 ≤ k.val → v k = 0) →
      tvU v ∈ H) :
    H = ⊤ := by
  have h3 : 3 ≤ n := by omega
  have key : ∀ m, ∀ a : Fin n → K, herm frob a a = 0 → uniSupp a = m → tvU a ∈ H := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro a ha hm
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ 3 ≤ m) with rfl | rfl | rfl | hm3
    · rw [uniSupp_eq_zero hm, tvU_zero]
      exact H.one_mem
    · exact absurd hm (uniSupp_ne_one ha)
    · obtain ⟨i, j, hij, hs⟩ := uniSupp_eq_two hm
      obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair
        (![⟨0, by omega⟩, ⟨1, by omega⟩] : Fin 2 → Fin n) ![i, j]
        (uni_inj2 (by simp [Fin.ext_iff])) (uni_inj2 hij)
      refine uni_tvU_move (hP π) ha (hT _ (by rw [herm_smul_smul]; exact ha) fun k hk => ?_)
      rw [uniPerm_smul, Function.comp_apply]
      by_contra hne
      have h0 : π ⟨0, by omega⟩ = i := hπ 0
      have h1 : π ⟨1, by omega⟩ = j := hπ 1
      rcases hs _ hne with h | h
      · have := π.injective (h.trans h0.symm)
        rw [this] at hk
        simp at hk
      · have := π.injective (h.trans h1.symm)
        rw [this] at hk
        simp at hk
    · obtain ⟨i, j, l, hi, hj, hl, hij, hil, hjl⟩ := uniSupp_three (a := a) (by omega)
      obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair (uniIdx h3) ![i, j, l]
        (uniIdx_injective h3) (uni_inj3 hij hil hjl)
      have hbx : ∀ x : Fin 3, (uniPerm frob two_eq_zero π • a) (uniIdx h3 x) ≠ 0 := by
        intro x
        rw [uniPerm_smul, Function.comp_apply, hπ x]
        fin_cases x
        · exact hi
        · exact hj
        · exact hl
      obtain ⟨δ, hu, h1, hδ0, hδb⟩ := uni_exists_diag hn _ hbx
      have hc : ∀ x : Fin 3,
          (uniDiag frob δ hu h1 • uniPerm frob two_eq_zero π • a) (uniIdx h3 x) = 1 := by
        intro x
        rw [uniDiag_smul]
        exact hδb x
      have hcard := uniSupp_fourier h3 hc
      have e1 : uniSupp (uniDiag frob δ hu h1 • uniPerm frob two_eq_zero π • a) = m := by
        rw [uniDiag_smul, uniSupp_mul hδ0, uniPerm_smul, uniSupp_comp, hm]
      have hiso : ∀ (g : SUid frob n) (v : Fin n → K), herm frob v v = 0 →
          herm frob (g • v) (g • v) = 0 := fun g v hv => by
        rw [herm_smul_smul]
        exact hv
      have hPa := hiso (uniPerm frob two_eq_zero π) a ha
      have hDPa := hiso (uniDiag frob δ hu h1) _ hPa
      have hd := ih _ (by omega) _ (hiso (uniFourier n h3) _ hDPa) rfl
      exact uni_tvU_move (hP π) ha (uni_tvU_move (hD δ hu h1) hPa (uni_tvU_move hF hDPa hd))
  have hT' := T_eq_top isUnitaryInvolution_frob (n := n) (by omega) (fun h => by omega)
  rw [T_eq_closure_tvU] at hT'
  rw [eq_top_iff, ← hT', Subgroup.closure_le]
  rintro _ ⟨v, -, hv, rfl⟩
  exact key _ v hv rfl

end Two

section TwoModel

open CFSG.Fischer.Classification.Unitary
open CFSG.Blueprint.Fischer (K)

variable {n : ℕ}

private abbrev UniP (n : ℕ) : Type := StatedProj (StatedSU n (2 ^ 1) (GaloisField 2 (2 * 1)))

private noncomputable def uniπ (n : ℕ) : SUid frob n →* UniP n :=
  (QuotientGroup.mk' _).comp (MulEquiv.subgroupCongr (SUid_eq_statedSU card_K n)).toMonoidHom

private theorem uniπ_surjective (n : ℕ) : Function.Surjective (uniπ n) :=
  (QuotientGroup.mk'_surjective _).comp (MulEquiv.surjective _)

private theorem uni_finite (n : ℕ) : Finite (UniP n) := by
  have : Finite (GL (Fin n) K) := Finite.of_injective _ Units.val_injective
  exact Finite.of_surjective (uniπ n) (uniπ_surjective n)

private theorem uni_exists_scalar {g g' : SUid frob n} (h : uniπ n g = uniπ n g') :
    ∃ c : K, ∀ v : Fin n → K, g' • v = c • (g • v) := by
  have h' : (MulEquiv.subgroupCongr (SUid_eq_statedSU card_K n) g)⁻¹ *
      MulEquiv.subgroupCongr (SUid_eq_statedSU card_K n) g' ∈
      (StatedScalars (Fin n) (GaloisField 2 (2 * 1))).subgroupOf
        (StatedSU n (2 ^ 1) (GaloisField 2 (2 * 1))) := QuotientGroup.eq.1 h
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 h'
  refine ⟨(c : K), fun v => ?_⟩
  have hg' : ((g' : SUid frob n) : GL (Fin n) K) =
      (g : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) c := by
    rw [hc]
    change (g' : GL (Fin n) K) =
      (g : GL (Fin n) K) * ((g : GL (Fin n) K)⁻¹ * (g' : GL (Fin n) K))
    group
  rw [smul_def, smul_def, hg', Units.val_mul, ← mulVec_mulVec, GeneralLinearGroup.coe_scalar,
    scalar_apply]
  have : diagonal (fun _ => (c : K)) *ᵥ v = (c : K) • v := by
    funext i
    rw [mulVec_diagonal]
    rfl
  rw [this, mulVec_smul]

private theorem uniπ_diag_ne_one {δ : Fin n → K} {hu : ∀ i, frob (δ i) * δ i = 1}
    {h1 : ∏ i, δ i = 1} {p q : Fin n} (hpq : δ p ≠ δ q) :
    uniπ n (uniDiag frob δ hu h1) ≠ 1 := by
  intro h
  rw [← map_one (uniπ n)] at h
  obtain ⟨c, hc⟩ := uni_exists_scalar h
  have hp := congrFun (hc (Pi.single p 1)) p
  have hq := congrFun (hc (Pi.single q 1)) q
  simp only [one_smul, uniDiag_smul, Pi.smul_apply, Pi.mul_apply, Pi.single_eq_same, mul_one,
    smul_eq_mul] at hp hq
  apply hpq
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hp
  exact mul_left_cancel₀ hc0 (hp.symm.trans hq)

private theorem uniπ_swap_not_comm {δ : Fin n → K} {hu : ∀ i, frob (δ i) * δ i = 1}
    {h1 : ∏ i, δ i = 1} {p q r : Fin n} (hrp : r ≠ p) (hrq : r ≠ q) (hne : δ p ≠ δ q)
    (hr : δ r ≠ 0) :
    uniπ n (uniPerm frob two_eq_zero (Equiv.swap p q)) * uniπ n (uniDiag frob δ hu h1) ≠
      uniπ n (uniDiag frob δ hu h1) * uniπ n (uniPerm frob two_eq_zero (Equiv.swap p q)) := by
  intro h
  rw [← map_mul, ← map_mul] at h
  obtain ⟨c, hc⟩ := uni_exists_scalar h
  exact uni_swap_ne hrp hrq hne hr hc

private noncomputable def uniX₁ (n : ℕ) : Fin n → K := fun k => if k.val < 3 then ω else 1

private noncomputable def uniY₁ (n : ℕ) : Fin n → K := fun k =>
  if k.val = n - 2 then ω else if k.val = n - 1 then ω ^ 2 else 1

private noncomputable def uniX₂ (n : ℕ) : Fin n → K := fun k =>
  if 2 ≤ k.val ∧ k.val < 5 then ω else 1

private noncomputable def uniY₂ (n : ℕ) : Fin n → K := fun k =>
  if k.val = 0 then ω else if k.val = 1 then ω ^ 2 else 1

private theorem uniX₁_ne (k : Fin n) : uniX₁ n k ≠ 0 := by
  unfold uniX₁
  split_ifs
  exacts [omega_ne_zero, one_ne_zero]

private theorem uniY₁_ne (k : Fin n) : uniY₁ n k ≠ 0 := by
  unfold uniY₁
  split_ifs
  exacts [omega_ne_zero, uni_omega_sq_ne_zero, one_ne_zero]

private theorem uniX₂_ne (k : Fin n) : uniX₂ n k ≠ 0 := by
  unfold uniX₂
  split_ifs
  exacts [omega_ne_zero, one_ne_zero]

private theorem uniY₂_ne (k : Fin n) : uniY₂ n k ≠ 0 := by
  unfold uniY₂
  split_ifs
  exacts [omega_ne_zero, uni_omega_sq_ne_zero, one_ne_zero]

private theorem uni_prod (hn : 5 ≤ n) (hn' : n ≤ 6) :
    (∏ i, uniX₁ n i = 1) ∧ (∏ i, uniY₁ n i = 1) ∧ (∏ i, uniX₂ n i = 1) ∧
      (∏ i, uniY₂ n i = 1) := by
  have h3 : ω ^ 3 = 1 := uni_cube omega_ne_zero
  have h3' : ω * ω ^ 2 = 1 := by rw [← pow_succ']; exact h3
  have h3'' : ω * ω * ω = 1 := by rw [← pow_two, ← pow_succ]; exact h3
  interval_cases n <;>
    simp [Fin.prod_univ_five, Fin.prod_univ_six, uniX₁, uniY₁, uniX₂, uniY₂, h3', h3'']

private theorem uni_two_threePlaneGen (hn : 5 ≤ n) (hn' : n ≤ 6) : ThreePlaneGen (UniP n) := by
  haveI := uni_finite n
  obtain ⟨pX₁, pY₁, pX₂, pY₂⟩ := uni_prod hn hn'
  have hω1 : ω ≠ 1 := omega_ne_one
  have hω2 : ω ^ 2 ≠ ω := uni_omega_sq_ne
  have hω4 : ω ^ 2 * ω ^ 2 = ω := by
    rw [← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_succ, uni_cube omega_ne_zero, one_mul]
  set x₁ := uniDiag frob (uniX₁ n) (fun i => frob_mul_self (uniX₁_ne i)) pX₁
  set y₁ := uniDiag frob (uniY₁ n) (fun i => frob_mul_self (uniY₁_ne i)) pY₁
  set x₂ := uniDiag frob (uniX₂ n) (fun i => frob_mul_self (uniX₂_ne i)) pX₂
  set y₂ := uniDiag frob (uniY₂ n) (fun i => frob_mul_self (uniY₂_ne i)) pY₂
  set π := uniπ n
  set i₀ : Fin n := ⟨0, by omega⟩
  set i₁ : Fin n := ⟨1, by omega⟩
  set i₂ : Fin n := ⟨2, by omega⟩
  set p : Fin n := ⟨n - 2, by omega⟩
  set q : Fin n := ⟨n - 1, by omega⟩
  have h0p : i₀ ≠ p := fun e => by simp [i₀, p, Fin.ext_iff] at e; omega
  have h0q : i₀ ≠ q := fun e => by simp [i₀, q, Fin.ext_iff] at e; omega
  have h01 : i₀ ≠ i₁ := fun e => by simp [i₀, i₁, Fin.ext_iff] at e
  have h02 : i₀ ≠ i₂ := fun e => by simp [i₀, i₂, Fin.ext_iff] at e
  have h21 : i₂ ≠ i₁ := fun e => by simp [i₂, i₁, Fin.ext_iff] at e
  have vX₁ : ∀ k : Fin n, k.val < 3 → uniX₁ n k = ω := fun k hk => by simp [uniX₁, hk]
  have vX₁' : ∀ k : Fin n, 3 ≤ k.val → uniX₁ n k = 1 := fun k hk => by
    simp [uniX₁]; omega
  have vY₁ : ∀ k : Fin n, k.val < 3 → uniY₁ n k = 1 := fun k hk => by
    simp only [uniY₁]
    rw [if_neg (by omega), if_neg (by omega)]
  have vY₁p : uniY₁ n p = ω := by simp [uniY₁, p]
  have vY₁q : uniY₁ n q = ω ^ 2 := by simp [uniY₁, q]; omega
  have vY₁r : ∀ k : Fin n, k ≠ p → k ≠ q → uniY₁ n k = 1 := fun k hkp hkq => by
    simp only [uniY₁]
    rw [if_neg fun e => hkp (Fin.ext e), if_neg fun e => hkq (Fin.ext e)]
  have vX₂ : ∀ k : Fin n, 2 ≤ k.val → k.val < 5 → uniX₂ n k = ω := fun k hk hk' => by
    simp [uniX₂, hk, hk']
  have vX₂' : ∀ k : Fin n, k.val < 2 → uniX₂ n k = 1 := fun k hk => by
    simp [uniX₂]; omega
  have vY₂ : ∀ k : Fin n, 2 ≤ k.val → uniY₂ n k = 1 := fun k hk => by
    simp only [uniY₂]
    rw [if_neg (by omega), if_neg (by omega)]
  have vY₂0 : uniY₂ n i₀ = ω := by simp [uniY₂, i₀]
  have vY₂1 : uniY₂ n i₁ = ω ^ 2 := by simp [uniY₂, i₁]
  have hcomm : ∀ {g d : SUid frob n}, g * d = d * g → π g * π d = π d * π g := fun h => by
    rw [← map_mul, ← map_mul, h]
  have hdd : ∀ (δ : Fin n → K) (hu : ∀ i, frob (δ i) * δ i = 1) (h1 : ∏ i, δ i = 1)
      (δ' : Fin n → K) (hu' : ∀ i, frob (δ' i) * δ' i = 1) (h1' : ∏ i, δ' i = 1),
      π (uniDiag frob δ hu h1) * π (uniDiag frob δ' hu' h1') =
        π (uniDiag frob δ' hu' h1') * π (uniDiag frob δ hu h1) :=
    fun _ _ _ _ _ _ => hcomm uniDiag_mul_comm
  have hswap : ∀ {a b : Fin n} {δ : Fin n → K} {hu : ∀ i, frob (δ i) * δ i = 1}
      {h1 : ∏ i, δ i = 1}, δ a = δ b →
      π (uniPerm frob two_eq_zero (Equiv.swap a b)) * π (uniDiag frob δ hu h1) =
        π (uniDiag frob δ hu h1) * π (uniPerm frob two_eq_zero (Equiv.swap a b)) :=
    fun h => hcomm (uni_commute_swap h)
  set X₁ := Subgroup.closure ({π x₁, π y₁} : Set (UniP n))
  set X₂ := Subgroup.closure ({π x₂, π y₂} : Set (UniP n))
  have hsN : π (uniPerm frob two_eq_zero (Equiv.swap p q)) ∈
      Subgroup.normalizer (X₁ : Set (UniP n)) := by
    refine uni_mem_normalizer_of_conj ?_ ?_
    · have e : π (uniPerm frob two_eq_zero (Equiv.swap p q)) * π x₁ =
          π x₁ * π (uniPerm frob two_eq_zero (Equiv.swap p q)) :=
        hswap (by rw [vX₁' p (by simp [p]; omega), vX₁' q (by simp [q]; omega)])
      rw [e, mul_inv_cancel_right]
      exact Subgroup.subset_closure (by simp)
    · have e : uniPerm frob two_eq_zero (Equiv.swap p q) * y₁ *
          (uniPerm frob two_eq_zero (Equiv.swap p q))⁻¹ = y₁ * y₁ := by
        refine ext_smul _ fun v => ?_
        rw [uni_perm_conj_smul, mul_smul, uniDiag_smul, uniDiag_smul]
        funext k
        simp only [Pi.mul_apply, Function.comp_apply]
        rcases eq_or_ne k p with rfl | hkp
        · rw [Equiv.swap_apply_left, vY₁p, vY₁q]
          ring
        · rcases eq_or_ne k q with rfl | hkq
          · rw [Equiv.swap_apply_right, vY₁p, vY₁q, ← mul_assoc, hω4]
          · rw [Equiv.swap_apply_of_ne_of_ne hkp hkq, vY₁r k hkp hkq]
            ring
      rw [← map_inv, ← map_mul, ← map_mul, e, map_mul]
      exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hgen : Subgroup.normalizer (X₁ : Set (UniP n)) ⊔ Subgroup.normalizer (X₂ : Set (UniP n)) =
      ⊤ := by
    set N := Subgroup.normalizer (X₁ : Set (UniP n)) ⊔ Subgroup.normalizer (X₂ : Set (UniP n))
    have hN₁ : ∀ {g : SUid frob n}, g * x₁ = x₁ * g → g * y₁ = y₁ * g → π g ∈ N :=
      fun h1 h2 => Subgroup.mem_sup_left (uni_mem_normalizer_of_commute (hcomm h1) (hcomm h2))
    have hN₂ : ∀ {g : SUid frob n}, g * x₂ = x₂ * g → g * y₂ = y₂ * g → π g ∈ N :=
      fun h1 h2 => Subgroup.mem_sup_right (uni_mem_normalizer_of_commute (hcomm h1) (hcomm h2))
    have hsw : ∀ a : Fin n, π (uniPerm frob two_eq_zero (Equiv.swap a i₂)) ∈ N := by
      intro a
      by_cases ha3 : a.val < 3
      · exact hN₁ (uni_commute_swap (by rw [vX₁ a ha3, vX₁ i₂ (by simp [i₂])]))
          (uni_commute_swap (by rw [vY₁ a ha3, vY₁ i₂ (by simp [i₂])]))
      · by_cases ha5 : a.val < 5
        · exact hN₂ (uni_commute_swap (by rw [vX₂ a (by omega) ha5, vX₂ i₂ (by simp [i₂])
              (by simp [i₂])]))
            (uni_commute_swap (by rw [vY₂ a (by omega), vY₂ i₂ (by simp [i₂])]))
        · have hap : a = q := Fin.ext (by simp [q]; omega)
          have h2p : i₂ ≠ p := fun e => by simp [i₂, p, Fin.ext_iff] at e; omega
          have h2q : i₂ ≠ q := fun e => by simp [i₂, q, Fin.ext_iff] at e; omega
          have e : Equiv.swap a i₂ = Equiv.swap p q * Equiv.swap i₂ p * Equiv.swap p q := by
            rw [Equiv.swap_mul_swap_mul_swap h2p h2q, hap]
          rw [e, uniPerm_mul, uniPerm_mul, map_mul, map_mul]
          have hp5 : p.val < 5 := by simp [p]; omega
          have hp2 : 2 ≤ p.val := by simp [p]; omega
          have h24 : π (uniPerm frob two_eq_zero (Equiv.swap i₂ p)) ∈ N :=
            hN₂ (uni_commute_swap (by rw [vX₂ i₂ (by simp [i₂]) (by simp [i₂]), vX₂ p hp2 hp5]))
              (uni_commute_swap (by rw [vY₂ i₂ (by simp [i₂]), vY₂ p hp2]))
          exact mul_mem (Subgroup.mem_sup_left hsN)
            (mul_mem h24 (Subgroup.mem_sup_left hsN))
    have hall : ∀ a b : Fin n, π (uniPerm frob two_eq_zero (Equiv.swap a b)) ∈ N := by
      intro a b
      by_cases hab : a = b
      · rw [hab, Equiv.swap_self]
        change π (uniPerm frob two_eq_zero 1) ∈ N
        rw [uniPerm_one, map_one]
        exact one_mem _
      · by_cases ha2 : a = i₂
        · rw [ha2, Equiv.swap_comm]
          exact hsw b
        · have e : Equiv.swap a b = Equiv.swap i₂ b * Equiv.swap a i₂ * Equiv.swap i₂ b := by
            rw [Equiv.swap_mul_swap_mul_swap ha2 hab, Equiv.swap_comm]
          have hb := hsw b
          rw [Equiv.swap_comm] at hb
          rw [e, uniPerm_mul, uniPerm_mul, map_mul, map_mul]
          exact mul_mem hb (mul_mem (hsw a) hb)
    have hH : N.comap π = ⊤ := by
      refine uni_eq_top (by omega) (fun δ hu h1 => ?_) (fun σ' => ?_) ?_ (fun v hv hsupp => ?_)
      · exact hN₁ uniDiag_mul_comm uniDiag_mul_comm
      · show π (uniPerm frob two_eq_zero σ') ∈ N
        induction σ' using Equiv.Perm.swap_induction_on with
        | one =>
          rw [uniPerm_one, map_one]
          exact one_mem _
        | swap_mul f a b _ ih =>
          rw [uniPerm_mul, map_mul]
          exact mul_mem ih (hall a b)
      · refine hN₁ (uni_commute_diag fun a b hab h0 => ?_) (uni_commute_diag fun a b hab h0 => ?_)
        · obtain ⟨ha, hb⟩ := uniFourier_entry hab h0
          rw [vX₁ a ha, vX₁ b hb]
        · obtain ⟨ha, hb⟩ := uniFourier_entry hab h0
          rw [vY₁ a ha, vY₁ b hb]
      · have hlt : ∀ i : Fin n, v i ≠ 0 → i.val < 2 := fun i hi => by
          by_contra h
          exact hi (hsupp i (by omega))
        exact hN₁ (uni_commute_tvU hv fun i hi => vX₁ i (by have := hlt i hi; omega))
          (uni_commute_tvU hv fun i hi => vY₁ i (by have := hlt i hi; omega))
    rw [eq_top_iff]
    intro m _
    obtain ⟨g, rfl⟩ := uniπ_surjective n m
    have : g ∈ N.comap π := by rw [hH]; trivial
    exact this
  refine uni_threePlaneGen (a₁ := π x₁) (b₁ := π y₁) (a₂ := π x₂) (b₂ := π y₂) ?_ ?_ ?_ ?_ ?_ ?_
    ?_ hgen
  · rintro x (rfl | rfl | rfl | rfl) y (rfl | rfl | rfl | rfl) <;> exact hdd _ _ _ _ _ _
  · rintro x (rfl | rfl | rfl | rfl) <;>
      exact by rw [← map_pow, uniDiag_pow_three fun i => uni_cube (by
        first | exact uniX₁_ne i | exact uniY₁_ne i | exact uniX₂_ne i | exact uniY₂_ne i),
        map_one]
  · exact uniπ_diag_ne_one (p := i₀) (q := q)
      (by rw [vX₁ i₀ (by simp [i₀]), vX₁' q (by simp [q]; omega)]; exact hω1)
  · exact uni_not_mem_zpowers
      (hswap (by rw [vX₁' p (by simp [p]; omega), vX₁' q (by simp [q]; omega)]))
      (uniπ_swap_not_comm h0p h0q (by rw [vY₁p, vY₁q]; exact hω2.symm) (uniY₁_ne _))
  · exact uniπ_diag_ne_one (p := i₀) (q := i₂)
      (by rw [vX₂' i₀ (by simp [i₀]), vX₂ i₂ (by simp [i₂]) (by simp [i₂])]; exact hω1.symm)
  · have h20 : i₂ ≠ i₀ := h02.symm
    exact uni_not_mem_zpowers
      (hswap (by rw [vX₂' i₀ (by simp [i₀]), vX₂' i₁ (by simp [i₁])]))
      (uniπ_swap_not_comm h20 h21 (by rw [vY₂0, vY₂1]; exact hω2.symm) (uniY₂_ne _))
  · exact uni_not_mem_closure
      (hswap (by rw [vX₁ i₁ (by simp [i₁]), vX₁ i₂ (by simp [i₂])]))
      (hswap (by rw [vY₁ i₁ (by simp [i₁]), vY₁ i₂ (by simp [i₂])]))
      (uniπ_swap_not_comm h01 h02
        (by rw [vX₂' i₁ (by simp [i₁]), vX₂ i₂ (by simp [i₂]) (by simp [i₂])]; exact hω1.symm)
        (uniX₂_ne _))

end TwoModel

section Eight

open CFSG.ClassicalInvolution.Phan (Su blockEmb2 blockEmb coe_coe_blockEmb blockMat_apply
  iSup_range_blockEmb2)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)

private abbrev UniK8 : Type := GaloisField 2 (2 * 3)

private noncomputable def uniE8 : Su UniK8 2 3 5 ≃* CFSG.Assembly.RankThreeEven.projSU 5 2 3 :=
  (MulEquiv.subgroupCongr
    (SUid_eq_statedSU CFSG.RankThree.PartTwo.KFacts.KS21.U58.card_K 5)).trans
    CFSG.RankThree.PartTwo.KFacts.KS21.U58.equivSUI.symm

private theorem uni_block_commute {i : Fin 4} (A : Su UniK8 2 3 2) {δ : Fin 5 → UniK8}
    {hu : ∀ j, unitaryInvolution UniK8 2 3 (δ j) * δ j = 1} {h1 : ∏ j, δ j = 1}
    (h : δ ⟨i, by omega⟩ = δ ⟨i + 1, by omega⟩) :
    blockEmb2 UniK8 2 3 4 i A * uniDiag (unitaryInvolution UniK8 2 3) δ hu h1 =
      uniDiag (unitaryInvolution UniK8 2 3) δ hu h1 * blockEmb2 UniK8 2 3 4 i A := by
  refine uni_commute_diag fun a b hab h0 => ?_
  rw [blockEmb2, coe_coe_blockEmb, blockMat_apply] at h0
  split_ifs at h0 with hblk
  · have key : ∀ c : Fin 5, (i : ℕ) ≤ c.val → c.val < i + 2 → δ c = δ ⟨i, by omega⟩ := by
      intro c hc hc'
      rcases (by omega : c.val = i ∨ c.val = i + 1) with e | e
      · rw [show c = ⟨i, by omega⟩ from Fin.ext e]
      · rw [show c = ⟨i + 1, by omega⟩ from Fin.ext e, h]
    rw [key a hblk.1.1 hblk.1.2, key b hblk.2.1 hblk.2.2]
  · exact absurd (one_apply_ne hab) h0

private theorem uni_eight_threePlaneGen : ThreePlaneGen (Su UniK8 2 3 5) := by
  haveI : Finite (Su UniK8 2 3 5) := by
    have : Finite (GL (Fin 5) UniK8) := Finite.of_injective _ Units.val_injective
    infer_instance
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : (2 : UniK8) = 0 := CharTwo.two_eq_zero
  obtain ⟨u, hu⟩ : ∃ u : UniK8ˣ, orderOf u = 3 := exists_prime_orderOf_dvd_card' 3
    (by rw [CFSG.RankThree.PartTwo.KFacts.KS21.U58.card_units_K]; norm_num)
  set ω : UniK8 := (u : UniK8) with hωdef
  have hu3 : u ^ 3 = 1 := by
    have h := pow_orderOf_eq_one u
    rwa [hu] at h
  have hω3 : ω ^ 3 = 1 := by
    rw [hωdef, ← Units.val_pow_eq_pow_val, hu3, Units.val_one]
  have hω1 : ω ≠ 1 := fun h => by
    have : u = 1 := Units.ext h
    rw [this, orderOf_one] at hu
    norm_num at hu
  have hω0 : ω ≠ 0 := u.ne_zero
  have hω2 : ω ^ 2 ≠ ω := fun h => by
    apply hω1
    have h' : ω * (ω - 1) = 0 := by linear_combination h
    exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_left hω0)
  have hω6 : ω ^ 6 = 1 := by
    calc ω ^ 6 = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω3, one_pow]
  have hσ : ∀ c : UniK8, c ^ 3 = 1 → unitaryInvolution UniK8 2 3 c * c = 1 := fun c hc => by
    rw [unitaryInvolution_apply]
    calc c ^ 2 ^ 3 * c = (c ^ 3) ^ 3 := by ring
      _ = 1 := by rw [hc, one_pow]
  have c2 : (ω ^ 2) ^ 3 = 1 := by
    calc (ω ^ 2) ^ 3 = ω ^ 6 := by ring
      _ = 1 := hω6
  set dX₁ : Fin 5 → UniK8 := ![ω, ω, ω, ω, ω ^ 2] with hdX₁
  set dY₁ : Fin 5 → UniK8 := ![ω, ω, 1, 1, ω] with hdY₁
  set dX₂ : Fin 5 → UniK8 := ![ω ^ 2, ω, ω, ω, ω] with hdX₂
  set dY₂ : Fin 5 → UniK8 := ![ω, ω, ω, 1, 1] with hdY₂
  have kX₁ : ∀ i, dX₁ i ^ 3 = 1 := fun i => by fin_cases i <;> simp [hdX₁, hω3, c2]
  have kY₁ : ∀ i, dY₁ i ^ 3 = 1 := fun i => by fin_cases i <;> simp [hdY₁, hω3]
  have kX₂ : ∀ i, dX₂ i ^ 3 = 1 := fun i => by fin_cases i <;> simp [hdX₂, hω3, c2]
  have kY₂ : ∀ i, dY₂ i ^ 3 = 1 := fun i => by fin_cases i <;> simp [hdY₂, hω3]
  have pX₁ : ∏ i, dX₁ i = 1 := by
    simp only [hdX₁, Fin.prod_univ_five]
    simp
    linear_combination hω6
  have pY₁ : ∏ i, dY₁ i = 1 := by
    simp only [hdY₁, Fin.prod_univ_five]
    simp
    linear_combination hω3
  have pX₂ : ∏ i, dX₂ i = 1 := by
    simp only [hdX₂, Fin.prod_univ_five]
    simp
    linear_combination hω6
  have pY₂ : ∏ i, dY₂ i = 1 := by
    simp only [hdY₂, Fin.prod_univ_five]
    simp
    linear_combination hω3
  set σ := unitaryInvolution UniK8 2 3
  set x₁ := uniDiag σ dX₁ (fun i => hσ _ (kX₁ i)) pX₁
  set y₁ := uniDiag σ dY₁ (fun i => hσ _ (kY₁ i)) pY₁
  set x₂ := uniDiag σ dX₂ (fun i => hσ _ (kX₂ i)) pX₂
  set y₂ := uniDiag σ dY₂ (fun i => hσ _ (kY₂ i)) pY₂
  set X₁ := Subgroup.closure ({x₁, y₁} : Set (Su UniK8 2 3 5))
  set X₂ := Subgroup.closure ({x₂, y₂} : Set (Su UniK8 2 3 5))
  have hgen : Subgroup.normalizer (X₁ : Set (Su UniK8 2 3 5)) ⊔
      Subgroup.normalizer (X₂ : Set (Su UniK8 2 3 5)) = ⊤ := by
    rw [eq_top_iff, ← iSup_range_blockEmb2 CFSG.RankThree.PartTwo.KFacts.KS21.U58.card_K
      (by norm_num) 4]
    refine iSup_le fun i => ?_
    rintro _ ⟨A, rfl⟩
    fin_cases i
    · exact Subgroup.mem_sup_left (uni_mem_normalizer_of_commute
        (uni_block_commute A (by simp [hdX₁])) (uni_block_commute A (by simp [hdY₁])))
    · exact Subgroup.mem_sup_right (uni_mem_normalizer_of_commute
        (uni_block_commute A (by simp [hdX₂])) (uni_block_commute A (by simp [hdY₂])))
    · exact Subgroup.mem_sup_left (uni_mem_normalizer_of_commute
        (uni_block_commute A (by simp [hdX₁])) (uni_block_commute A (by simp [hdY₁])))
    · exact Subgroup.mem_sup_right (uni_mem_normalizer_of_commute
        (uni_block_commute A (by simp [hdX₂])) (uni_block_commute A (by simp [hdY₂])))
  refine uni_threePlaneGen (a₁ := x₁) (b₁ := y₁) (a₂ := x₂) (b₂ := y₂) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hgen
  · rintro x (rfl | rfl | rfl | rfl) y (rfl | rfl | rfl | rfl) <;> exact uniDiag_mul_comm
  · rintro x (rfl | rfl | rfl | rfl)
    exacts [uniDiag_pow_three kX₁, uniDiag_pow_three kY₁, uniDiag_pow_three kX₂,
      uniDiag_pow_three kY₂]
  · exact uniDiag_ne_one (p := 0) (by simpa [hdX₁] using hω1)
  · exact uni_not_mem_zpowers (uni_commute_swap (h2 := h2) (i := 1) (j := 2) (by simp [hdX₁]))
      (uni_swap_not_comm (h2 := h2) (p := 1) (q := 2) (r := 0) (by decide) (by decide)
        (by simpa [hdY₁] using hω1) (by simpa [hdY₁] using hω0))
  · exact uniDiag_ne_one (p := 1) (by simpa [hdX₂] using hω1)
  · exact uni_not_mem_zpowers (uni_commute_swap (h2 := h2) (i := 2) (j := 3) (by simp [hdX₂]))
      (uni_swap_not_comm (h2 := h2) (p := 2) (q := 3) (r := 0) (by decide) (by decide)
        (by simpa [hdY₂] using hω1) (by simpa [hdY₂] using hω0))
  · exact uni_not_mem_closure (uni_commute_swap (h2 := h2) (i := 0) (j := 1) (by simp [hdX₁]))
      (uni_commute_swap (h2 := h2) (i := 0) (j := 1) (by simp [hdY₁]))
      (uni_swap_not_comm (h2 := h2) (p := 0) (q := 1) (r := 2) (by decide) (by decide)
        (by simpa [hdX₂] using hω2) (by simpa [hdX₂] using hω0))

end Eight

theorem threeCoreAt_U52 : ThreeCoreAt (CFSG.Assembly.RankThreeEven.projSU 5 2 1) :=
  threeCoreAt_of_threePlaneGen (CFSG.PGLModel.projSUEquivStatedProj 5 2 1).symm
    (uni_two_threePlaneGen (by norm_num) (by norm_num))

theorem threeCoreAt_U62 : ThreeCoreAt (CFSG.Assembly.RankThreeEven.projSU 6 2 1) :=
  threeCoreAt_of_threePlaneGen (CFSG.PGLModel.projSUEquivStatedProj 6 2 1).symm
    (uni_two_threePlaneGen (by norm_num) (by norm_num))

theorem threeCoreAt_U58 : ThreeCoreAt (CFSG.Assembly.RankThreeEven.projSU 5 2 3) :=
  threeCoreAt_of_threePlaneGen uniE8 uni_eight_threePlaneGen

end CFSG.LocalAnalysis.RankThreeTheoremC
