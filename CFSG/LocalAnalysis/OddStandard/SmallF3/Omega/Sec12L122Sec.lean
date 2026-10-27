module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L107bAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private def A5fin : Finset (Equiv.Perm (Fin 5)) :=
  Finset.univ.filter (fun σ => Equiv.Perm.sign σ = 1)

private theorem mem_A5fin {σ : Equiv.Perm (Fin 5)} :
    σ ∈ A5fin ↔ σ ∈ alternatingGroup (Fin 5) := by
  simp [A5fin, Equiv.Perm.mem_alternatingGroup]

private def wpair : Fin 5 → ZMod 2 := fun j => if j = 0 ∨ j = 4 then 1 else 0

private theorem wpair_even : IsEvenVec wpair := by
  unfold IsEvenVec wpair
  decide +kernel

private theorem count_id (n : Fin 5 → ZMod 2) (hn : IsEvenVec n) :
    ∑ σ ∈ A5fin, (n (σ 0)).val • permVec σ wpair = n := by
  revert n
  unfold IsEvenVec wpair permVec A5fin
  decide +kernel

private theorem isEvenVec_smul {n : ℕ} (k : ℕ) {v : Fin n → ZMod 2} (hv : IsEvenVec v) :
    IsEvenVec (k • v) := by
  unfold IsEvenVec at *
  simp only [Pi.smul_apply]
  rw [Finset.sum_nsmul, hv, nsmul_zero]

private theorem isEvenVec_sum {ι : Type} (T : Finset ι) (a : ι → Fin 5 → ZMod 2) (k : ι → ℕ)
    (ha : ∀ i ∈ T, IsEvenVec (a i)) : IsEvenVec (∑ i ∈ T, k i • a i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [IsEvenVec]
  | insert x s hx ih =>
    rw [Finset.sum_insert hx]
    exact isEvenVec_add (isEvenVec_smul (k x) (ha x (Finset.mem_insert_self x s)))
      (ih (fun i hi => ha i (Finset.mem_insert_of_mem hi)))

private theorem pow_val_add {V : Subgroup G} (hsq : ∀ v ∈ V, v * v = 1) (x : ↥V)
    (a b : ZMod 2) : x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  have hxx : x * x = 1 := Subtype.ext (hsq x x.2)
  have h00 : ((0 : ZMod 2) + 0).val = 0 := by decide
  have h01 : ((0 : ZMod 2) + 1).val = 1 := by decide
  have h10 : ((1 : ZMod 2) + 0).val = 1 := by decide
  have h11 : ((1 : ZMod 2) + 1).val = 0 := by decide
  have ha : a = 0 ∨ a = 1 := by revert a; decide +kernel
  have hb : b = 0 ∨ b = 1 := by revert b; decide +kernel
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · simp only [h00, ZMod.val_zero, pow_zero, one_mul]
  · simp only [h01, ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, one_mul]
  · simp only [h10, ZMod.val_one, ZMod.val_zero, pow_zero, pow_one, mul_one]
  · simp only [h11, ZMod.val_one, pow_zero, pow_one, hxx]

private theorem phi_nsmul {φ : (Fin 5 → ZMod 2) → G} {B Y : Subgroup G}
    (hperm : IsPermModuleVia IsEvenVec φ B Y (alternatingGroup (Fin 5)))
    (hφ0 : φ 0 = 1) (k : ℕ) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    φ (k • v) = (φ v) ^ k := by
  induction k with
  | zero => simpa using hφ0
  | succ k ih =>
    rw [show (k + 1) • v = k • v + v from succ_nsmul _ _,
      hperm.1 (k • v) v (isEvenVec_smul k hv) hv, ih, pow_succ]

theorem sec122_section {V B Y : Subgroup G} {φ : (Fin 5 → ZMod 2) → G} {f : G → G}
    (hcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hsq : ∀ v ∈ V, v * v = 1)
    (hperm : IsPermModuleVia IsEvenVec φ B Y (alternatingGroup (Fin 5)))
    (hYV : ∀ y ∈ Y, ∀ v ∈ V, y * v * y⁻¹ ∈ V)
    (htriv : ∀ y ∈ Y, (∀ v, IsEvenVec v → y * φ v * y⁻¹ = φ v) → ∀ x ∈ V, y * x * y⁻¹ = x)
    (hfB : ∀ v ∈ V, f v ∈ B) (hfmul : ∀ v ∈ V, ∀ w ∈ V, f (v * w) = f v * f w)
    (hfconj : ∀ y ∈ Y, ∀ v ∈ V, f (y * v * y⁻¹) = y * f v * y⁻¹)
    (hfsurj : ∀ b ∈ B, ∃ v ∈ V, f v = b) :
    ∃ s : (Fin 5 → ZMod 2) → G,
      (∀ n, IsEvenVec n → s n ∈ V) ∧
      (∀ n m, IsEvenVec n → IsEvenVec m → s (n + m) = s n * s m) ∧
      (∀ n, IsEvenVec n → f (s n) = φ n) ∧
      ∀ y ∈ Y, ∀ σ : Equiv.Perm (Fin 5),
        (∀ v, IsEvenVec v → y * φ v * y⁻¹ = φ (permVec σ v)) →
          ∀ n, IsEvenVec n → y * s n * y⁻¹ = s (permVec σ n) := by
  classical
  have hφ0 : φ 0 = 1 := by
    have h : φ 0 = φ 0 * φ 0 := by
      simpa using hperm.1 0 0 (by simp [IsEvenVec]) (by simp [IsEvenVec])
    exact mul_eq_left.1 h.symm
  have hφB : ∀ v, IsEvenVec v → φ v ∈ B :=
    fun v hv => (hperm.2.2.1 (φ v)).2 ⟨v, hv, rfl⟩
  have hf1 : f 1 = 1 := by
    have h : f 1 = f 1 * f 1 := by simpa using hfmul 1 V.one_mem 1 V.one_mem
    exact mul_eq_left.1 h.symm
  have hBcomm : ∀ a b : ↥B, a * b = b * a := by
    intro a b
    obtain ⟨v, hv, hvx⟩ := (hperm.2.2.1 (a : G)).1 a.2
    obtain ⟨w, hw, hwy⟩ := (hperm.2.2.1 (b : G)).1 b.2
    apply Subtype.ext
    show (a : G) * b = b * a
    rw [← hvx, ← hwy, ← hperm.1 v w hv hw, ← hperm.1 w v hw hv]
    exact congrArg φ (add_comm v w)
  letI : CommGroup ↥V :=
    { (inferInstance : Group ↥V) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  letI : CommGroup ↥B :=
    { (inferInstance : Group ↥B) with mul_comm := hBcomm }
  let φB : (Fin 5 → ZMod 2) → ↥B := fun v =>
    if hv : IsEvenVec v then ⟨φ v, hφB v hv⟩ else 1
  have hφBv : ∀ v, IsEvenVec v → (φB v : G) = φ v := by
    intro v hv
    dsimp only [φB]
    rw [dif_pos hv]
  have hex : ∀ σ : Equiv.Perm (Fin 5), ∃ y ∈ Y, σ ∈ alternatingGroup (Fin 5) →
      ∀ v, IsEvenVec v → y * φ v * y⁻¹ = φ (permVec σ v) := by
    intro σ
    by_cases hσ : σ ∈ alternatingGroup (Fin 5)
    · obtain ⟨y, hy, hy'⟩ := hperm.2.2.2.2 σ hσ
      exact ⟨y, hy, fun _ => hy'⟩
    · exact ⟨1, Y.one_mem, fun h => absurd h hσ⟩
  choose yσ hyY hyσ using hex
  obtain ⟨u, huV, hfu⟩ := hfsurj (φ wpair) (hφB wpair wpair_even)
  let uV : Equiv.Perm (Fin 5) → ↥V := fun σ =>
    ⟨yσ σ * u * (yσ σ)⁻¹, hYV (yσ σ) (hyY σ) u huV⟩
  let s : (Fin 5 → ZMod 2) → G := fun n =>
    ((∏ σ ∈ A5fin, (uV σ) ^ (n (σ 0)).val : ↥V) : G)
  have f_pow : ∀ (x : ↥V) (k : ℕ), f ((x ^ k : ↥V) : G) = f (x : G) ^ k := by
    intro x k
    induction k with
    | zero => simp [hf1]
    | succ k ih =>
      rw [pow_succ, pow_succ]
      rw [show (((x ^ k) * x : ↥V) : G) = ((x ^ k : ↥V) : G) * (x : G) from rfl]
      rw [hfmul ((x ^ k : ↥V) : G) (x ^ k).2 (x : G) x.2, ih]
  have f_prod : ∀ {ι : Type} (T : Finset ι) (g : ι → ↥V),
      f ((∏ i ∈ T, g i : ↥V) : G)
        = ((∏ i ∈ T, (⟨f (g i), hfB (g i) (g i).2⟩ : ↥B) : ↥B) : G) := by
    intro ι T
    refine Finset.induction_on T ?_ ?_
    · intro g
      simp [hf1]
    · intro a t ha ih g
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      rw [show ((g a * ∏ i ∈ t, g i : ↥V) : G)
            = (g a : G) * ((∏ i ∈ t, g i : ↥V) : G) from rfl]
      rw [hfmul (g a : G) (g a).2 ((∏ i ∈ t, g i : ↥V) : G) (Subtype.mem _)]
      rw [show ((⟨f (g a), hfB (g a) (g a).2⟩
              * ∏ i ∈ t, (⟨f (g i), hfB (g i) (g i).2⟩ : ↥B) : ↥B) : G)
            = f (g a) * ((∏ i ∈ t, (⟨f (g i), hfB (g i) (g i).2⟩ : ↥B) : ↥B) : G)
          from rfl]
      rw [ih g]
  have phi_prod : ∀ {ι : Type} (T : Finset ι) (a : ι → (Fin 5 → ZMod 2)) (k : ι → ℕ),
      (∀ i ∈ T, IsEvenVec (a i)) →
      ((∏ i ∈ T, (φB (a i)) ^ k i : ↥B) : G) = φ (∑ i ∈ T, k i • a i) := by
    intro ι T
    refine Finset.induction_on T ?_ ?_
    · intro a k ha
      simp only [Finset.prod_empty, Finset.sum_empty]
      rw [show ((1 : ↥B) : G) = 1 from rfl, hφ0]
    · intro x t hx ih a k ha
      rw [Finset.prod_insert hx, Finset.sum_insert hx]
      have hmemx : IsEvenVec (a x) := ha x (Finset.mem_insert_self x t)
      have hsum : IsEvenVec (∑ i ∈ t, k i • a i) :=
        isEvenVec_sum t a k (fun i hi => ha i (Finset.mem_insert_of_mem hi))
      rw [show (((φB (a x)) ^ k x * ∏ i ∈ t, (φB (a i)) ^ k i : ↥B) : G)
            = ((φB (a x)) ^ k x : G) * ((∏ i ∈ t, (φB (a i)) ^ k i : ↥B) : G)
          from rfl]
      rw [show ((φB (a x)) ^ k x : G) = (φ (a x)) ^ k x from by
        rw [show ((φB (a x)) ^ k x : G) = ((φB (a x) : ↥B) : G) ^ k x from rfl,
          hφBv (a x) hmemx]]
      rw [← phi_nsmul hperm hφ0 (k x) hmemx]
      rw [hperm.1 (k x • a x) (∑ i ∈ t, k i • a i) (isEvenVec_smul (k x) hmemx) hsum]
      rw [ih a k (fun i hi => ha i (Finset.mem_insert_of_mem hi))]
  have hf_uV : ∀ σ, σ ∈ alternatingGroup (Fin 5) →
      f (uV σ : G) = φ (permVec σ wpair) := by
    intro σ hσ
    show f (yσ σ * u * (yσ σ)⁻¹) = φ (permVec σ wpair)
    rw [hfconj (yσ σ) (hyY σ) u huV, hfu, hyσ σ hσ wpair wpair_even]
  have hsV : ∀ n, IsEvenVec n → s n ∈ V := by
    intro n _
    show ((∏ σ ∈ A5fin, (uV σ) ^ (n (σ 0)).val : ↥V) : G) ∈ V
    exact (∏ σ ∈ A5fin, (uV σ) ^ (n (σ 0)).val : ↥V).2
  have hsadd : ∀ n m, IsEvenVec n → IsEvenVec m → s (n + m) = s n * s m := by
    intro n m hn hm
    show ((∏ σ ∈ A5fin, (uV σ) ^ ((n + m) (σ 0)).val : ↥V) : G)
        = ((∏ σ ∈ A5fin, (uV σ) ^ (n (σ 0)).val : ↥V) : G)
          * ((∏ σ ∈ A5fin, (uV σ) ^ (m (σ 0)).val : ↥V) : G)
    rw [show (∏ σ ∈ A5fin, (uV σ) ^ ((n + m) (σ 0)).val : ↥V)
          = (∏ σ ∈ A5fin, (uV σ) ^ (n (σ 0)).val * (uV σ) ^ (m (σ 0)).val : ↥V) from by
        apply Finset.prod_congr rfl
        intro σ _
        rw [show (n + m) (σ 0) = n (σ 0) + m (σ 0) from rfl, pow_val_add hsq]]
    rw [Finset.prod_mul_distrib, Subgroup.coe_mul]
  have hfs : ∀ n, IsEvenVec n → f (s n) = φ n := by
    intro n hn
    show f ((∏ σ ∈ A5fin, (uV σ) ^ (n (σ 0)).val : ↥V) : G) = φ n
    rw [f_prod]
    rw [show (∏ σ ∈ A5fin, (⟨f (((uV σ) ^ (n (σ 0)).val : ↥V) : G),
              hfB _ ((uV σ) ^ (n (σ 0)).val).2⟩ : ↥B) : ↥B)
          = ∏ σ ∈ A5fin, (φB (permVec σ wpair)) ^ (n (σ 0)).val from by
        apply Finset.prod_congr rfl
        intro σ hσ
        apply Subtype.ext
        show f (((uV σ) ^ (n (σ 0)).val : ↥V) : G)
            = (((φB (permVec σ wpair)) ^ (n (σ 0)).val : ↥B) : G)
        rw [f_pow, hf_uV σ (mem_A5fin.1 hσ)]
        rw [show (((φB (permVec σ wpair)) ^ (n (σ 0)).val : ↥B) : G)
              = ((φB (permVec σ wpair) : ↥B) : G) ^ (n (σ 0)).val from rfl,
            hφBv (permVec σ wpair) (isEvenVec_permVec σ wpair_even)]]
    rw [phi_prod A5fin (fun σ => permVec σ wpair) (fun σ => (n (σ 0)).val)
          (fun σ _ => isEvenVec_permVec σ wpair_even)]
    rw [count_id n hn]
  refine ⟨s, hsV, hsadd, hfs, ?_⟩
  intro y hy σ₀ hσ₀ n hn
  have htriv' : ∀ {y y' : G}, y ∈ Y → y' ∈ Y → ∀ σ : Equiv.Perm (Fin 5),
      (∀ v, IsEvenVec v → y * φ v * y⁻¹ = φ (permVec σ v)) →
      (∀ v, IsEvenVec v → y' * φ v * y'⁻¹ = φ (permVec σ v)) →
      ∀ x ∈ V, y * x * y⁻¹ = y' * x * y'⁻¹ := by
    intro y y' hy hy' σ hσ hσ' x hx
    have hc : y'⁻¹ * y ∈ Y := Y.mul_mem (Y.inv_mem hy') hy
    have hfix : ∀ v, IsEvenVec v → (y'⁻¹ * y) * φ v * (y'⁻¹ * y)⁻¹ = φ v := by
      intro v hv
      have h1 : y'⁻¹ * (y * φ v * y⁻¹) * y' = φ v := by
        rw [hσ v hv, ← hσ' v hv]
        group
      calc (y'⁻¹ * y) * φ v * (y'⁻¹ * y)⁻¹
          = y'⁻¹ * (y * φ v * y⁻¹) * y' := by group
        _ = φ v := h1
    have hx' := htriv (y'⁻¹ * y) hc hfix x hx
    calc y * x * y⁻¹ = y' * ((y'⁻¹ * y) * x * (y'⁻¹ * y)⁻¹) * y'⁻¹ := by group
      _ = y' * x * y'⁻¹ := by rw [hx']
  have hσ₀alt : σ₀ ∈ alternatingGroup (Fin 5) := by
    obtain ⟨σ', hσ'alt, hσ'⟩ := hperm.2.2.2.1 y hy
    have heq : ∀ v, IsEvenVec v → permVec σ₀ v = permVec σ' v := by
      intro v hv
      exact hperm.2.1 (permVec σ₀ v) (permVec σ' v) (isEvenVec_permVec σ₀ hv)
        (isEvenVec_permVec σ' hv) (by rw [← hσ₀ v hv, hσ' v hv])
    have hEq : σ₀ = σ' := permVec_injective_five heq
    rw [hEq]
    exact hσ'alt
  let conjV : ↥V →* ↥V :=
    { toFun := fun x => ⟨y * (x : G) * y⁻¹, hYV y hy x x.2⟩
      map_one' := by
        apply Subtype.ext
        show y * ((1 : ↥V) : G) * y⁻¹ = 1
        rw [show ((1 : ↥V) : G) = 1 from rfl]
        group
      map_mul' := by
        intro a b
        apply Subtype.ext
        show y * ((a * b : ↥V) : G) * y⁻¹ = (y * (a : G) * y⁻¹) * (y * (b : G) * y⁻¹)
        rw [Subgroup.coe_mul]
        group }
  have hconj_uV : ∀ σ ∈ alternatingGroup (Fin 5), conjV (uV σ) = uV (σ₀ * σ) := by
    intro σ hσ
    apply Subtype.ext
    show y * (yσ σ * u * (yσ σ)⁻¹) * y⁻¹
        = yσ (σ₀ * σ) * u * (yσ (σ₀ * σ))⁻¹
    have hσ₀σ : σ₀ * σ ∈ alternatingGroup (Fin 5) :=
      (alternatingGroup (Fin 5)).mul_mem hσ₀alt hσ
    have hact1 : ∀ v, IsEvenVec v →
        (y * yσ σ) * φ v * (y * yσ σ)⁻¹ = φ (permVec (σ₀ * σ) v) := by
      intro v hv
      calc (y * yσ σ) * φ v * (y * yσ σ)⁻¹
          = y * (yσ σ * φ v * (yσ σ)⁻¹) * y⁻¹ := by group
        _ = y * φ (permVec σ v) * y⁻¹ := by rw [hyσ σ hσ v hv]
        _ = φ (permVec σ₀ (permVec σ v)) := hσ₀ (permVec σ v) (isEvenVec_permVec σ hv)
        _ = φ (permVec (σ₀ * σ) v) := by rw [permVec_mul]
    have hact2 : ∀ v, IsEvenVec v →
        yσ (σ₀ * σ) * φ v * (yσ (σ₀ * σ))⁻¹ = φ (permVec (σ₀ * σ) v) :=
      fun v hv => hyσ (σ₀ * σ) hσ₀σ v hv
    have hxu := htriv' (Y.mul_mem hy (hyY σ)) (hyY (σ₀ * σ)) (σ₀ * σ) hact1 hact2 u huV
    calc y * (yσ σ * u * (yσ σ)⁻¹) * y⁻¹
        = (y * yσ σ) * u * (y * yσ σ)⁻¹ := by group
      _ = yσ (σ₀ * σ) * u * (yσ (σ₀ * σ))⁻¹ := hxu
  have hreindex : (∏ σ ∈ A5fin, (uV (σ₀ * σ)) ^ (n (σ 0)).val : ↥V)
      = ∏ σ' ∈ A5fin, (uV σ') ^ (n ((σ₀⁻¹ * σ') 0)).val := by
    refine Finset.prod_nbij' (fun σ => σ₀ * σ) (fun σ => σ₀⁻¹ * σ) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      exact mem_A5fin.2 ((alternatingGroup (Fin 5)).mul_mem hσ₀alt (mem_A5fin.1 ha))
    · intro a ha
      exact mem_A5fin.2 ((alternatingGroup (Fin 5)).mul_mem
        ((alternatingGroup (Fin 5)).inv_mem hσ₀alt) (mem_A5fin.1 ha))
    · intro a _
      show σ₀⁻¹ * (σ₀ * a) = a
      group
    · intro a _
      show σ₀ * (σ₀⁻¹ * a) = a
      group
    · intro a _
      rw [show σ₀⁻¹ * (σ₀ * a) = a from by group]
  show y * ((∏ σ ∈ A5fin, (uV σ) ^ (n (σ 0)).val : ↥V) : G) * y⁻¹
      = ((∏ σ' ∈ A5fin, (uV σ') ^ ((permVec σ₀ n) (σ' 0)).val : ↥V) : G)
  rw [show y * ((∏ σ ∈ A5fin, (uV σ) ^ (n (σ 0)).val : ↥V) : G) * y⁻¹
        = (conjV (∏ σ ∈ A5fin, (uV σ) ^ (n (σ 0)).val) : G) from rfl]
  rw [map_prod]
  rw [show (∏ σ ∈ A5fin, conjV ((uV σ) ^ (n (σ 0)).val) : ↥V)
        = ∏ σ ∈ A5fin, (uV (σ₀ * σ)) ^ (n (σ 0)).val from by
      apply Finset.prod_congr rfl
      intro σ hσ
      rw [map_pow, hconj_uV σ (mem_A5fin.1 hσ)]]
  rw [hreindex]
  rfl

end CFSG.OddStandard.SmallF3.Omega
