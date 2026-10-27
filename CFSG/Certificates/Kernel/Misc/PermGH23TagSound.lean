module

public import Certificates.Data.Kernel.Misc.PermGH23Tag
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23AltGen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Z3Gen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Hom
public import Mathlib.Data.List.GetD
import CFSG.Certificates.Kernel.LocalQTPermSound
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.Certificates.Kernel.Misc.PermGH23Sound
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Clos
public import Certificates.Data.GH23Tags

public section

namespace CFSG.KC.Misc.GH23

open Equiv CFSG.KC.Misc.Clos CFSG.KC.LQT CFSG.OddStandard.SmallF3.HarrisU33.GH23Data
  CFSG.OddStandard.SmallF3.HarrisU33.Outside CFSG.Permutation.SymmetricCoxeter

theorem memAt_sound {H : Subgroup (Perm (Fin 8))} {N : ℕ} {E : ℕ → ℕ}
    (hE : ExactList gh23Code H N E) {c t : ℕ} (h : memAt E N c t = true) :
    ∃ σ ∈ H, gh23Code σ = c := by
  obtain ⟨h1, h2⟩ := P.andB_iff.1 h
  obtain ⟨σ, hσ, hc⟩ := hE.1 t (Nat.blt_eq.mp h1)
  exact ⟨σ, hσ, hc.trans (Nat.eq_of_beq_eq_true h2)⟩

theorem comm_le_of_commAt {A B : Subgroup (Perm (Fin 8))} {nA nB o : ℕ} {EA EB W : ℕ → ℕ}
    (hA : ExactList gh23Code A nA EA) (hB : ExactList gh23Code B nB EB)
    (h : ∀ i < nA * nA, commAt EA nA EB nB W o i = true) : ⁅A, A⁆ ≤ B := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a, ha, hxa⟩ := hA.2.1 x hx
  obtain ⟨b, hb, hyb⟩ := hA.2.1 y hy
  have hpos : 0 < nA := by omega
  have hi : a * nA + b < nA * nA := by nlinarith
  have hdiv : (a * nA + b) / nA = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hb, Nat.zero_add]
  have hmod : (a * nA + b) % nA = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  have h' := h _ hi
  unfold commAt at h'
  rw [P.letB_eq, P.letB_eq, P.letB_eq] at h'
  obtain ⟨ht, heq⟩ := P.andB_iff.1 h'
  have heq' := Nat.eq_of_beq_eq_true heq
  have hdiv' : Nat.div (a * nA + b) nA = a := hdiv
  have hmod' : Nat.mod (a * nA + b) nA = b := hmod
  rw [hdiv', hmod', ← hxa, ← hyb] at heq'
  obtain ⟨τ, hτ, hτc⟩ := hB.1 _ (Nat.blt_eq.mp ht)
  rw [← hτc, mul8_eq, mul8_eq, mul8_eq, gh23_mulC_code, gh23_mulC_code, gh23_mulC_code] at heq'
  have hτ' : τ * (y * x) = x * y := gh23_code_injective heq'
  have hc : x * y * x⁻¹ * y⁻¹ = τ := by
    rw [← hτ']
    group
  rw [commutatorElement_def, hc]
  exact hτ

theorem gh23Sub_nil : gh23Sub [] = ⊥ := by
  unfold gh23Sub
  simp

theorem gh23Sub_le_of_codes {A : List ℕ} {H : Subgroup (Perm (Fin 8))}
    (h : ∀ c ∈ A, ∃ σ ∈ H, gh23Code σ = c) : gh23Sub A ≤ H := by
  unfold gh23Sub
  rw [Subgroup.closure_le]
  intro τ hτ
  obtain ⟨σ, hσ, hσc⟩ := h _ hτ
  rwa [gh23_code_injective hσc] at hσ

theorem gh23_two_exact {Pg ngens : List ℕ} {NN : ℕ} {EN : ℕ → ℕ}
    (hN : ExactList gh23Code (gh23Sub ngens) NN EN)
    (hmem : ∀ c ∈ ngens, ∃ σ ∈ gh23Sub Pg, gh23Code σ = c) (hne : ∃ c ∈ ngens, c ≠ oneC)
    (hsq : ∀ k < NN, mulC (EN k) (EN k) = oneC)
    (hconj : ∀ σ : Perm (Fin 8), gh23Code σ ∈ Pg → ∀ ν : Perm (Fin 8), gh23Code ν ∈ ngens →
      σ * ν * σ⁻¹ ∈ gh23Sub ngens ∧ σ⁻¹ * ν * σ ∈ gh23Sub ngens) :
    ¬ NoNormalTwo (gh23Sub Pg) := by
  obtain ⟨n, hn, hne'⟩ := hne
  obtain ⟨σ0, -, hσ0⟩ := hmem n hn
  have hσ0N : σ0 ∈ gh23Sub ngens := Subgroup.subset_closure (by simpa [hσ0] using hn)
  have hσ0ne : σ0 ≠ 1 := by
    intro h1
    exact hne' (by rw [← hσ0, h1, gh23_oneC])
  have hN0 : gh23Sub ngens ≠ ⊥ := by
    intro hbot
    exact hσ0ne (by simpa [hbot] using hσ0N)
  have hle : gh23Sub ngens ≤ gh23Sub Pg := gh23Sub_le_of_codes hmem
  have hp : IsPGroup 2 (gh23Sub ngens) := by
    intro g
    refine ⟨1, ?_⟩
    change g ^ 2 = 1
    apply Subtype.ext
    obtain ⟨k, hk, hkc⟩ := hN.2.1 _ g.2
    have hs := hsq k hk
    rw [← hkc, gh23_mulC_code, gh23_oneC] at hs
    simpa [pow_two] using gh23_code_injective hs
  have hnorm : gh23Sub Pg ≤ Subgroup.normalizer (gh23Sub ngens : Set (Perm (Fin 8))) := by
    change Subgroup.closure {σ : Perm (Fin 8) | gh23Code σ ∈ Pg} ≤
      Subgroup.normalizer (gh23Sub ngens : Set (Perm (Fin 8)))
    rw [Subgroup.closure_le]
    intro σ hσ
    have hconj' : ∀ τ : Perm (Fin 8), τ ∈ gh23Sub ngens →
        MulAut.conj σ τ ∈ gh23Sub ngens ∧ (MulAut.conj σ)⁻¹ τ ∈ gh23Sub ngens := by
      intro τ hτ
      refine Subgroup.closure_induction (p := fun τ _ =>
        MulAut.conj σ τ ∈ gh23Sub ngens ∧ (MulAut.conj σ)⁻¹ τ ∈ gh23Sub ngens)
        ?_ ?_ ?_ ?_ hτ
      · intro ν hν
        rw [MulAut.conj_apply, MulAut.conj_inv_apply]
        exact hconj σ hσ ν hν
      · constructor <;> simp
      · intro x y _ _ hx' hy'
        refine ⟨?_, ?_⟩
        · simpa only [map_mul] using mul_mem hx'.1 hy'.1
        · simpa only [map_mul] using mul_mem hx'.2 hy'.2
      · intro x _ hx'
        refine ⟨?_, ?_⟩
        · simpa only [map_inv] using inv_mem hx'.1
        · simpa only [map_inv] using inv_mem hx'.2
    refine (Subgroup.mem_normalizer_iff (H := gh23Sub ngens)).mpr ?_
    intro τ
    constructor
    · intro hτ
      exact (hconj' τ hτ).1
    · intro hτ
      have h2 := (hconj' (MulAut.conj σ τ) hτ).2
      rwa [MulAut.inv_apply_self] at h2
  intro hno
  exact hN0 (hno (gh23Sub ngens) hle hnorm hp)

theorem fact_eq_factorial' : ∀ n, fact n = n.factorial
  | 0 => rfl
  | n + 1 => by
    change (n + 1) * fact n = (n + 1).factorial
    rw [fact_eq_factorial' n, Nat.factorial_succ]

theorem gh23_imgs_common {Pg imgs : List ℕ} (hsub : gh23Sub Pg = gh23Sub imgs)
    (himgs : ∀ c ∈ imgs, ∃ σ ∈ gh23Sub Pg, gh23Code σ = c) :
    ∃ (σ : ℕ → Perm (Fin 8)) (y : ℕ → ↥(gh23Sub Pg)),
      (∀ i, i < imgs.length → gh23Code (σ i) = imgs.getD i 0) ∧
      (∀ i, i < imgs.length → ((y i : ↥(gh23Sub Pg)) : Perm (Fin 8)) = σ i) ∧
      Subgroup.closure {h | ∃ i, i < imgs.length ∧ y i = h} = ⊤ := by
  have hex : ∀ i, i < imgs.length → ∃ σ : Perm (Fin 8),
      σ ∈ gh23Sub Pg ∧ gh23Code σ = imgs.getD i 0 := by
    intro i hi
    have hmem : imgs.getD i 0 ∈ imgs := by
      rw [List.getD_eq_getElem (l := imgs) (d := 0) hi]
      exact List.getElem_mem hi
    obtain ⟨σ, hσmem, hσc⟩ := himgs _ hmem
    exact ⟨σ, hσmem, hσc⟩
  let σ : ℕ → Perm (Fin 8) := fun i =>
    if hi : i < imgs.length then Classical.choose (hex i hi) else 1
  have hσmem : ∀ i (hi : i < imgs.length), σ i ∈ gh23Sub Pg := by
    intro i hi
    change (if h : i < imgs.length then Classical.choose (hex i h) else 1) ∈ gh23Sub Pg
    simp only [dif_pos hi]
    exact (Classical.choose_spec (hex i hi)).1
  have hσcode : ∀ i (hi : i < imgs.length), gh23Code (σ i) = imgs.getD i 0 := by
    intro i hi
    change gh23Code (if h : i < imgs.length then Classical.choose (hex i h) else 1) =
      imgs.getD i 0
    simp only [dif_pos hi]
    exact (Classical.choose_spec (hex i hi)).2
  let y : ℕ → ↥(gh23Sub Pg) := fun i =>
    if hi : i < imgs.length then ⟨σ i, hσmem i hi⟩ else 1
  have hy_coe : ∀ i (hi : i < imgs.length), ((y i : ↥(gh23Sub Pg)) : Perm (Fin 8)) = σ i := by
    intro i hi
    have hy : y i = ⟨σ i, hσmem i hi⟩ := by
      dsimp only [y]
      rw [dif_pos hi]
    exact congrArg Subtype.val hy
  have hgen : Subgroup.closure {h | ∃ i, i < imgs.length ∧ y i = h} = ⊤ := by
    set s : Set (Perm (Fin 8)) := {τ | gh23Code τ ∈ imgs} with hs
    have hclos : Subgroup.closure s = gh23Sub Pg := by
      rw [hs]
      exact hsub.symm
    have hpre := Subgroup.closure_preimage_eq_top (s := s)
    rw [hclos] at hpre
    have hset : {h : ↥(gh23Sub Pg) | ∃ i, i < imgs.length ∧ y i = h} =
        (gh23Sub Pg).subtype ⁻¹' s := by
      ext h
      constructor
      · rintro ⟨i, hi, rfl⟩
        change gh23Code ((y i : ↥(gh23Sub Pg)) : Perm (Fin 8)) ∈ imgs
        rw [hy_coe i hi, hσcode i hi, List.getD_eq_getElem (l := imgs) (d := 0) hi]
        exact List.getElem_mem hi
      · intro hh
        change gh23Code ((h : ↥(gh23Sub Pg)) : Perm (Fin 8)) ∈ imgs at hh
        obtain ⟨k, hk, hkcode⟩ := List.mem_iff_getElem.mp hh
        refine ⟨k, hk, ?_⟩
        apply Subtype.ext
        rw [hy_coe k hk]
        apply gh23_code_injective
        rw [hσcode k hk, List.getD_eq_getElem (l := imgs) (d := 0) hk, hkcode]
    rw [hset]
    exact hpre
  exact ⟨σ, y, hσcode, hy_coe, hgen⟩

theorem gh23_alt_exact {Pg imgs : List ℕ} {n : ℕ}
    (himgs : ∀ c ∈ imgs, ∃ σ ∈ gh23Sub Pg, gh23Code σ = c)
    (hPg : ∀ c ∈ Pg, ∃ σ ∈ gh23Sub imgs, gh23Code σ = c)
    (hcard : Nat.card (gh23Sub imgs) = fact n / 2) (h3n : 3 ≤ n) (hlen : imgs.length + 2 = n)
    (hcarm : carmRels imgs = true) :
    Nonempty (↥(gh23Sub Pg) ≃* alternatingGroup (Fin n)) := by
  have hsub : gh23Sub Pg = gh23Sub imgs :=
    le_antisymm (gh23Sub_le_of_codes hPg) (gh23Sub_le_of_codes himgs)
  obtain ⟨σ, y, hσcode, hy_coe, hgen⟩ := gh23_imgs_common hsub himgs
  unfold carmRels at hcarm
  rw [List.all_eq_true] at hcarm
  have hcubeσ : ∀ i, i < imgs.length → σ i ^ 3 = 1 := by
    intro i hi
    have h := hcarm i (List.mem_range.mpr hi)
    rw [Bool.and_eq_true] at h
    have h3 := beq_iff_eq.mp h.1
    rw [← hσcode i hi] at h3
    simp only [gh23_mulC_code, gh23_oneC] at h3
    simpa only [pow_three'] using gh23_code_injective h3
  have hsqσ : ∀ i j, i < imgs.length → j < imgs.length → i ≠ j → (σ i * σ j) ^ 2 = 1 := by
    intro i j hi hj hij
    have h := hcarm i (List.mem_range.mpr hi)
    rw [Bool.and_eq_true] at h
    have h2 := List.all_eq_true.mp h.2 j (List.mem_range.mpr hj)
    rw [Bool.or_eq_true] at h2
    rcases h2 with h2 | h2
    · exact absurd (beq_iff_eq.mp h2) hij
    · have h2' := beq_iff_eq.mp h2
      rw [← hσcode i hi, ← hσcode j hj] at h2'
      simp only [gh23_mulC_code, gh23_oneC] at h2'
      simpa only [pow_two] using gh23_code_injective h2'
  have h3y : ∀ i, i < n - 2 → y i ^ 3 = 1 := by
    intro i hi
    have hi' : i < imgs.length := by omega
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, hy_coe i hi']
    exact hcubeσ i hi'
  have h2y : ∀ i j, i < n - 2 → j < n - 2 → i ≠ j → (y i * y j) ^ 2 = 1 := by
    intro i j hi hj hij
    have hi' : i < imgs.length := by omega
    have hj' : j < imgs.length := by omega
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one, hy_coe i hi', hy_coe j hj']
    exact hsqσ i j hi' hj' hij
  have hgen' : Subgroup.closure {h | ∃ i, i < n - 2 ∧ y i = h} = ⊤ := by
    have : n - 2 = imgs.length := by omega
    rw [this]
    exact hgen
  have hcardP : Nat.card ↥(gh23Sub Pg) = n.factorial / 2 := by
    rw [hsub, hcard, fact_eq_factorial' n]
  exact gh23_alt_equiv_of_rels h3n y h3y h2y hgen' hcardP

theorem gh23_sym_exact {Pg imgs : List ℕ} {n : ℕ}
    (himgs : ∀ c ∈ imgs, ∃ σ ∈ gh23Sub Pg, gh23Code σ = c)
    (hPg : ∀ c ∈ Pg, ∃ σ ∈ gh23Sub imgs, gh23Code σ = c)
    (hcard : Nat.card (gh23Sub imgs) = fact n) (hlen : imgs.length + 1 = n)
    (hcox : coxRels imgs = true) :
    Nonempty (↥(gh23Sub Pg) ≃* Equiv.Perm (Fin n)) := by
  have hsub : gh23Sub Pg = gh23Sub imgs :=
    le_antisymm (gh23Sub_le_of_codes hPg) (gh23Sub_le_of_codes himgs)
  obtain ⟨σ, y, hσcode, hy_coe, hgen⟩ := gh23_imgs_common hsub himgs
  unfold coxRels at hcox
  rw [Bool.and_eq_true, Bool.and_eq_true] at hcox
  obtain ⟨⟨hcox1, hcox2⟩, hcox3⟩ := hcox
  rw [List.all_eq_true] at hcox1 hcox2 hcox3
  have hsqσ : ∀ i, i < imgs.length → σ i * σ i = 1 := by
    intro i hi
    have h := beq_iff_eq.mp (hcox1 i (List.mem_range.mpr hi))
    rw [← hσcode i hi, gh23_mulC_code, gh23_oneC] at h
    exact gh23_code_injective h
  have hbraidσ : ∀ i, i + 1 < imgs.length →
      σ i * σ (i + 1) * σ i = σ (i + 1) * σ i * σ (i + 1) := by
    intro i hi
    have hi' : i < imgs.length := by omega
    have h := hcox2 i (List.mem_range.mpr hi')
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [decide_eq_true_iff] at h
      omega
    · have h' := beq_iff_eq.mp h
      rw [← hσcode i hi', ← hσcode (i + 1) hi] at h'
      apply gh23_code_injective
      simpa only [← gh23_mulC_code] using h'
  have hcommσ : ∀ i j, i + 2 ≤ j → j < imgs.length → σ i * σ j = σ j * σ i := by
    intro i j hij hj
    have hi : i < imgs.length := by omega
    have h := List.all_eq_true.mp (hcox3 i (List.mem_range.mpr hi)) j (List.mem_range.mpr hj)
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [decide_eq_true_iff] at h
      omega
    · have h' := beq_iff_eq.mp h
      rw [← hσcode i hi, ← hσcode j hj] at h'
      apply gh23_code_injective
      simpa only [← gh23_mulC_code] using h'
  have hcoxy : IsCoxeterA imgs.length y := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_one, hy_coe i hi]
      exact hsqσ i hi
    · intro i hi
      have hi' : i < imgs.length := by omega
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hy_coe i hi', hy_coe (i + 1) hi]
      exact hbraidσ i hi
    · intro i j hij hj
      have hi : i < imgs.length := by omega
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hy_coe i hi, hy_coe j hj]
      exact hcommσ i j hij hj
  have hcardP : Nat.card ↥(gh23Sub Pg) = (imgs.length + 1).factorial := by
    rw [hsub, hcard, ← hlen, fact_eq_factorial']
  subst hlen
  exact gh23_sym_equiv_of_rels (n := imgs.length) y hcoxy hgen hcardP

theorem gh23_z3a5_exact {Pg imgs : List ℕ} {z : ℕ}
    (himgs : ∀ c ∈ imgs ++ [z], ∃ σ ∈ gh23Sub Pg, gh23Code σ = c)
    (hPg : ∀ c ∈ Pg, ∃ σ ∈ gh23Sub (imgs ++ [z]), gh23Code σ = c)
    (hcard : Nat.card (gh23Sub (imgs ++ [z])) = 180) (hlen : imgs.length = 3)
    (hcarm : carmRels imgs = true) (hz3 : mulC (mulC z z) z = oneC)
    (hcomm : ∀ x ∈ imgs, mulC z x = mulC x z) :
    Nonempty (↥(gh23Sub Pg) ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 5)) := by
  have hsub : gh23Sub Pg = gh23Sub (imgs ++ [z]) :=
    le_antisymm (gh23Sub_le_of_codes hPg) (gh23Sub_le_of_codes himgs)
  obtain ⟨σ, y, hσcode, hy_coe, hgen⟩ := gh23_imgs_common hsub himgs
  have hl : (imgs ++ [z]).length = 4 := by simp [hlen]
  have hget : ∀ i, i < 3 → (imgs ++ [z]).getD i 0 = imgs.getD i 0 := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega),
      List.getElem_append_left]
  have hget3 : (imgs ++ [z]).getD 3 0 = z := by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by omega)]
    simp [hlen]
  unfold carmRels at hcarm
  rw [List.all_eq_true] at hcarm
  have hc3 : ∀ i, i < 3 → gh23Code (σ i) = imgs.getD i 0 := fun i hi => by
    rw [hσcode i (by omega), hget i hi]
  have hz : gh23Code (σ 3) = z := by rw [hσcode 3 (by omega), hget3]
  have h3 : ∀ i, i < 3 → y i ^ 3 = 1 := by
    intro i hi
    have h := hcarm i (List.mem_range.mpr (by omega))
    rw [Bool.and_eq_true] at h
    have h3 := beq_iff_eq.mp h.1
    rw [← hc3 i hi] at h3
    simp only [gh23_mulC_code, gh23_oneC] at h3
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, hy_coe i (by omega)]
    simpa only [pow_three'] using gh23_code_injective h3
  have h2 : ∀ i j, i < 3 → j < 3 → i ≠ j → (y i * y j) ^ 2 = 1 := by
    intro i j hi hj hij
    have h := hcarm i (List.mem_range.mpr (by omega))
    rw [Bool.and_eq_true] at h
    have h2 := List.all_eq_true.mp h.2 j (List.mem_range.mpr (by omega))
    rw [Bool.or_eq_true] at h2
    rcases h2 with h2 | h2
    · exact absurd (beq_iff_eq.mp h2) hij
    · have h2' := beq_iff_eq.mp h2
      rw [← hc3 i hi, ← hc3 j hj] at h2'
      simp only [gh23_mulC_code, gh23_oneC] at h2'
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one, hy_coe i (by omega),
        hy_coe j (by omega)]
      simpa only [pow_two] using gh23_code_injective h2'
  have hzz : y 3 ^ 3 = 1 := by
    have h := hz3
    rw [← hz] at h
    simp only [gh23_mulC_code, gh23_oneC] at h
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, hy_coe 3 (by omega)]
    simpa only [pow_three'] using gh23_code_injective h
  have hc : ∀ i, i < 3 → y 3 * y i = y i * y 3 := by
    intro i hi
    have hmem : imgs.getD i 0 ∈ imgs := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    have h := hcomm _ hmem
    rw [← hz, ← hc3 i hi, gh23_mulC_code, gh23_mulC_code] at h
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hy_coe 3 (by omega), hy_coe i (by omega)]
    exact gh23_code_injective h
  have hgen' : Subgroup.closure ({y 3} ∪ {h | ∃ i, i < 3 ∧ y i = h}) = ⊤ := by
    rw [← hgen, hl]
    congr 1
    ext h
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨3, by omega, rfl⟩
      · exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.lt_or_ge i 3 with h | h
      · exact Or.inr ⟨i, h, rfl⟩
      · obtain rfl : i = 3 := by omega
        exact Or.inl rfl
  have hcardP : Nat.card ↥(gh23Sub Pg) = 180 := by rw [hsub, hcard]
  exact gh23_z3a5_equiv_of_rels y (y 3) h3 h2 hzz hc hgen' hcardP

theorem gh23_idx2_exact {Pg Lg : List ℕ} (hle : ∀ c ∈ Lg, ∃ σ ∈ gh23Sub Pg, gh23Code σ = c)
    (hcard : Nat.card (gh23Sub Pg) = 2 * Nat.card (gh23Sub Lg))
    (hz : Nonempty (↥(gh23Sub Lg) ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 5))) :
    ∃ K : Subgroup ↥(gh23Sub Pg), K.index = 2 ∧
      Nonempty (↥K ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 5)) := by
  have hle' : gh23Sub Lg ≤ gh23Sub Pg := gh23Sub_le_of_codes hle
  refine ⟨(gh23Sub Lg).subgroupOf (gh23Sub Pg), ?_, ?_⟩
  · have hKcard : Nat.card ((gh23Sub Lg).subgroupOf (gh23Sub Pg)) = Nat.card (gh23Sub Lg) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle').toEquiv
    have hci := Subgroup.card_mul_index ((gh23Sub Lg).subgroupOf (gh23Sub Pg))
    rw [hKcard, hcard, Nat.mul_comm 2] at hci
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hci
  · obtain ⟨f⟩ := hz
    exact ⟨(Subgroup.subgroupOfEquivOfLe hle').trans f⟩

theorem gh23_gl_exact {nG NP NQ : ℕ} {G EP EQ CT φ ψ : ℕ → ℕ} {Pg Qg : List ℕ}
    (hPg : Pg = (List.range nG).map G)
    (hP : ExactList gh23Code (gh23Sub Pg) NP EP) (hQ : ExactList gh23Code (gh23Sub Qg) NQ EQ)
    (hcP : Nat.card (gh23Sub Pg) = NP) (hcQ : Nat.card (gh23Sub Qg) = NQ) (hNPQ : NP = NQ)
    (hCT : ∀ k < NP, ∀ j < nG, CT (k * nG + j) < NP ∧ EP (CT (k * nG + j)) = mulC (EP k) (G j))
    (h1P : EP 0 = oneC) (h1Q : EQ (φ 0) = oneC) (hφ : ∀ k < NP, φ k < NQ)
    (hψ : ∀ k < NP, ψ (φ k) = k)
    (hmul : ∀ k < NP, ∀ j < nG, EQ (φ (CT (k * nG + j))) = mulC (EQ (φ k)) (EQ (φ (CT j)))) :
    Nonempty (↥(gh23Sub Pg) ≃* ↥(gh23Sub Qg)) := by
  classical
  have hNP : 0 < NP := by
    rw [← hcP]
    exact Nat.card_pos
  have hidx : ∀ σ : ↥(gh23Sub Pg), ∃ k < NP, gh23Code (σ : Perm (Fin 8)) = EP k :=
    fun σ => hP.2.1 _ σ.2
  choose idx hidx_lt hidx_code using hidx
  have huniq : ∀ (σ : ↥(gh23Sub Pg)) (k : ℕ), k < NP → EP k = gh23Code (σ : Perm (Fin 8)) →
      idx σ = k := fun σ k hk h =>
    hP.2.2 _ (hidx_lt σ) _ hk ((hidx_code σ).symm.trans h.symm)
  have hex : ∀ σ : ↥(gh23Sub Pg), ∃ τ : ↥(gh23Sub Qg),
      gh23Code (τ : Perm (Fin 8)) = EQ (φ (idx σ)) := by
    intro σ
    obtain ⟨τ, hτ, hτc⟩ := hQ.1 _ (hφ _ (hidx_lt σ))
    exact ⟨⟨τ, hτ⟩, hτc⟩
  choose f hf using hex
  have hidx1 : idx 1 = 0 := huniq 1 0 hNP (by rw [h1P, gh23_oneC]; rfl)
  have h1 : f 1 = 1 := by
    apply Subtype.ext
    apply gh23_code_injective
    rw [hf, hidx1, h1Q, gh23_oneC]
    rfl
  let gens : Set ↥(gh23Sub Pg) := {σ | gh23Code (σ : Perm (Fin 8)) ∈ Pg}
  have hgen : Subgroup.closure gens = ⊤ := by
    change Subgroup.closure
      (((↑) : ↥(gh23Sub Pg) → Perm (Fin 8)) ⁻¹' {σ : Perm (Fin 8) | gh23Code σ ∈ Pg}) = ⊤
    exact Subgroup.closure_closure_coe_preimage
  have hmulf : ∀ x : ↥(gh23Sub Pg), ∀ g ∈ gens, f (x * g) = f x * f g := by
    intro x g hg
    change gh23Code (g : Perm (Fin 8)) ∈ Pg at hg
    have hg2 : gh23Code (g : Perm (Fin 8)) ∈ (List.range nG).map G := by
      rw [← hPg]
      exact hg
    obtain ⟨j, hj, hgj⟩ := List.mem_map.mp hg2
    rw [List.mem_range] at hj
    have hk := hidx_lt x
    obtain ⟨ht, hte⟩ := hCT (idx x) hk j hj
    obtain ⟨h0t, h0e⟩ := hCT 0 hNP j hj
    rw [Nat.zero_mul, Nat.zero_add] at h0t h0e
    have hxg : idx (x * g) = CT (idx x * nG + j) := by
      refine huniq _ _ ht ?_
      rw [hte, ← hidx_code x, hgj, gh23_mulC_code]
      rfl
    have hg' : idx g = CT j := by
      refine huniq _ _ h0t ?_
      rw [h0e, h1P, hgj, gh23_oneC, gh23_mulC_code, one_mul]
    apply Subtype.ext
    apply gh23_code_injective
    rw [hf, hxg, hmul _ hk j hj, ← hg', ← hf, ← hf, gh23_mulC_code]
    rfl
  have hinj : Function.Injective f := by
    intro σ τ hστ
    have hc := congrArg (fun z : ↥(gh23Sub Qg) => gh23Code (z : Perm (Fin 8))) hστ
    simp only [hf] at hc
    have hφe : φ (idx σ) = φ (idx τ) :=
      hQ.2.2 _ (hφ _ (hidx_lt σ)) _ (hφ _ (hidx_lt τ)) hc
    have hi : idx σ = idx τ := by
      rw [← hψ _ (hidx_lt σ), ← hψ _ (hidx_lt τ), hφe]
    apply Subtype.ext
    apply gh23_code_injective
    rw [hidx_code σ, hidx_code τ, hi]
  have hle : Nat.card ↥(gh23Sub Qg) ≤ Nat.card ↥(gh23Sub Pg) := by
    rw [hcP, hcQ, hNPQ]
  exact gh23_mulEquiv_of_gens gens hgen f f h1 hmulf hinj hle

end CFSG.KC.Misc.GH23

end
