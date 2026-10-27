module

public import Certificates.Data.GMS78RuCzPres

public section

namespace CFSG.ComponentClassification.GMS78.RuCz

open Equiv Subgroup CFSG.CosetTable
open scoped Pointwise

@[expose] def czSigma0 (i : Fin 9) : Perm (Fin 5) :=
  if i.val < 6 then 1 else if i.val = 6 then c[2, 3, 4] else if i.val = 7 then swap 2 3
  else swap 1 2

namespace CzSigma

section Words

variable {G : Type*} [Group G]

@[expose] def evalW (g : ℕ → G) : List ℕ → G
  | [] => 1
  | c :: w => (if c % 2 = 0 then g (c / 2) else (g (c / 2))⁻¹) * evalW g w

theorem wordOfCodes_single : ∀ c (hc : c < 18),
    wordOfCodes 9 [c] = [(⟨c / 2, by omega⟩, c % 2 == 0)] := by
  decide

theorem ofNat_eq_mk {n : ℕ} (h : n < 9) : Fin.ofNat 9 n = ⟨n, h⟩ :=
  Fin.ext (by rw [Fin.val_ofNat, Nat.mod_eq_of_lt h])

theorem lift_mk_wordOfCodes (x : Fin 9 → G) {w : List ℕ} (hw : ∀ c ∈ w, c < 18) :
    FreeGroup.lift x (FreeGroup.mk (wordOfCodes 9 w)) = evalW (fun i => x (Fin.ofNat 9 i)) w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    have hc : c < 18 := hw c List.mem_cons_self
    have hw' : ∀ c ∈ w, c < 18 := fun c' h => hw c' (List.mem_cons_of_mem _ h)
    have e : wordOfCodes 9 (c :: w) = wordOfCodes 9 [c] ++ wordOfCodes 9 w := by
      simp only [wordOfCodes, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [e, ← FreeGroup.mul_mk, map_mul, ih hw', wordOfCodes_single c hc, evalW,
      ofNat_eq_mk (show c / 2 < 9 by omega)]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one c with h2 | h2
    · simp only [h2, ↓reduceIte]
      exact FreeGroup.lift_apply_of
    · simp only [h2, one_ne_zero, ↓reduceIte]
      change FreeGroup.lift x (FreeGroup.of _)⁻¹ = _
      rw [map_inv, FreeGroup.lift_apply_of]

theorem map_evalW {G' : Type*} [Group G'] (f : G →* G') (g : ℕ → G) (w : List ℕ) :
    f (evalW g w) = evalW (fun i => f (g i)) w := by
  induction w with
  | nil => exact map_one f
  | cons c w ih =>
    simp only [evalW, map_mul, ih]
    split_ifs <;> simp

end Words

theorem codes_lt : ∀ r ∈ czP12Codes, ∀ c ∈ r, c < 18 := by decide +kernel

theorem fin9_cases {p : Fin 9 → Prop} (h0 : ∀ i : Fin 9, i.val < 6 → p i) (h6 : p 6) (h7 : p 7)
    (h8 : p 8) (i : Fin 9) : p i := by
  rcases i with ⟨i, hi⟩
  by_cases h : i < 6
  · exact h0 ⟨i, hi⟩ h
  · obtain rfl | rfl | rfl : i = 6 ∨ i = 7 ∨ i = 8 := by omega
    exacts [h6, h7, h8]

@[expose] def czA0 : Perm (Fin 5) := swap 2 3 * swap 3 4

theorem czA0_eq : czA0 = c[2, 3, 4] := by decide

@[expose] def czB6 : List (Perm (Fin 5)) := [swap 2 3, swap 2 4, swap 3 4, swap 2 3 * swap 0 1,
  swap 2 4 * swap 0 1, swap 3 4 * swap 0 1]

@[expose] def czInv5 : List (Perm (Fin 5)) := [1, swap 0 1, swap 0 2, swap 0 3, swap 0 4,
  swap 1 2, swap 1 3, swap 1 4, swap 2 3, swap 2 4, swap 3 4, swap 0 1 * swap 2 3,
  swap 0 1 * swap 2 4, swap 0 1 * swap 3 4, swap 0 2 * swap 1 3, swap 0 2 * swap 1 4,
  swap 0 2 * swap 3 4, swap 0 3 * swap 1 2, swap 0 3 * swap 1 4, swap 0 3 * swap 2 4,
  swap 0 4 * swap 1 2, swap 0 4 * swap 1 3, swap 0 4 * swap 2 3, swap 1 2 * swap 3 4,
  swap 1 3 * swap 2 4, swap 1 4 * swap 2 3]

@[expose] def czCen6 : List (Perm (Fin 5)) :=
  [1, czA0, czA0 * czA0, swap 0 1, swap 0 1 * czA0, swap 0 1 * czA0 * czA0]

set_option maxRecDepth 100000 in
theorem conj_czA0 : ∀ a : Perm (Fin 5), a * a * a = 1 → a ≠ 1 →
    ∃ π : Perm (Fin 5), π * a * π⁻¹ = czA0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mem_czB6 : ∀ b : Perm (Fin 5), b * b = 1 → czA0⁻¹ * b * czA0 * b * czA0⁻¹ = 1 →
    b ∈ czB6 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mem_czInv5 : ∀ c : Perm (Fin 5), c * c = 1 → c ∈ czInv5 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem classify : ∀ b ∈ czB6, ∀ c ∈ czInv5, b * c * czA0 * c⁻¹ * czA0⁻¹ * c⁻¹ = 1 →
    (∃ π ∈ czCen6, π * b * π⁻¹ = swap 2 3 ∧ π * c * π⁻¹ = swap 1 2) ∨
      (c * czA0 * c⁻¹ = czA0 ∨ c * czA0 * c⁻¹ = czA0⁻¹) := by
  decide +kernel

theorem cen6_comm : ∀ π ∈ czCen6, π * czA0 * π⁻¹ = czA0 := by decide +kernel

theorem czB6_inv : ∀ b ∈ czB6, b * czA0 * b⁻¹ = czA0⁻¹ := by decide +kernel

@[expose] def czN12 : Subgroup (Perm (Fin 5)) where
  carrier := {g | g * czA0 * g⁻¹ = czA0 ∨ g * czA0 * g⁻¹ = czA0⁻¹}
  mul_mem' := fun {g h} hg hh => by
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [show g * h * czA0 * (g * h)⁻¹ = g * (h * czA0 * h⁻¹) * g⁻¹ by group]
    rcases hh with hh | hh <;> rw [hh]
    · exact hg
    · rw [show g * czA0⁻¹ * g⁻¹ = (g * czA0 * g⁻¹)⁻¹ by group]
      rcases hg with hg | hg <;> rw [hg]
      · exact Or.inr rfl
      · exact Or.inl (inv_inv _)
  one_mem' := Or.inl (by group)
  inv_mem' := fun {g} hg => by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    rcases hg with hg | hg
    · left
      calc g⁻¹ * czA0 * g⁻¹⁻¹ = g⁻¹ * (g * czA0 * g⁻¹) * g := by rw [hg]; group
        _ = czA0 := by group
    · right
      calc g⁻¹ * czA0 * g⁻¹⁻¹ = g⁻¹ * (g * czA0 * g⁻¹)⁻¹ * g := by rw [hg]; group
        _ = czA0⁻¹ := by group

theorem mem_czN12 {g : Perm (Fin 5)} :
    g ∈ czN12 ↔ g * czA0 * g⁻¹ = czA0 ∨ g * czA0 * g⁻¹ = czA0⁻¹ :=
  Iff.rfl

instance : DecidablePred (· ∈ czN12) := fun _ => decidable_of_iff _ mem_czN12.symm

theorem card_czN12 : Nat.card czN12 = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

section Letters

variable {H : Type*} [Group H]

theorem rels (τ : H →* Perm (Fin 5)) (x : Fin 9 → H)
    (hP12 : ∀ r ∈ czP12Codes, FreeGroup.lift x (FreeGroup.mk (wordOfCodes 9 r)) = 1)
    (hx : ∀ i : Fin 9, i.val < 6 → τ (x i) = 1) :
    τ (x 6) * τ (x 6) * τ (x 6) = 1 ∧ τ (x 7) * τ (x 7) = 1 ∧ τ (x 8) * τ (x 8) = 1 ∧
      (τ (x 6))⁻¹ * τ (x 7) * τ (x 6) * τ (x 7) * (τ (x 6))⁻¹ = 1 ∧
      τ (x 7) * τ (x 8) * τ (x 6) * (τ (x 8))⁻¹ * (τ (x 6))⁻¹ * (τ (x 8))⁻¹ = 1 := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ → Perm (Fin 5), s = fun i => τ (x (Fin.ofNat 9 i)) := ⟨_, rfl⟩
  have hrel : ∀ r ∈ czP12Codes, evalW s r = 1 := fun r hr => by
    rw [hs, ← map_evalW τ (fun i => x (Fin.ofNat 9 i)), ← lift_mk_wordOfCodes x (codes_lt r hr),
      hP12 r hr, map_one]
  have hs1 : ∀ i < 6, s i = 1 := fun i hi => by
    rw [hs]
    exact (congrArg τ (congrArg x (ofNat_eq_mk (by omega)))).trans (hx ⟨i, by omega⟩ hi)
  have h6 : s 6 = τ (x 6) := by rw [hs]; rfl
  have h7 : s 7 = τ (x 7) := by rw [hs]; rfl
  have h8 : s 8 = τ (x 8) := by rw [hs]; rfl
  have R1 := hrel [12, 12, 12] (by decide +kernel)
  have R2 := hrel [14, 14] (by decide +kernel)
  have R3 := hrel [3, 4, 3, 4, 16, 0, 16] (by decide +kernel)
  have R4 := hrel [1, 13, 14, 12, 14, 13, 6, 10, 0, 6] (by decide +kernel)
  have R5 := hrel [14, 16, 12, 17, 13, 3, 17, 10] (by decide +kernel)
  change s 6 * (s 6 * (s 6 * 1)) = 1 at R1
  change s 7 * (s 7 * 1) = 1 at R2
  change (s 1)⁻¹ * (s 2 * ((s 1)⁻¹ * (s 2 * (s 8 * (s 0 * (s 8 * 1)))))) = 1 at R3
  change (s 0)⁻¹ * ((s 6)⁻¹ * (s 7 * (s 6 * (s 7 * ((s 6)⁻¹ * (s 3 * (s 5 * (s 0 *
    (s 3 * 1))))))))) = 1 at R4
  change s 7 * (s 8 * (s 6 * ((s 8)⁻¹ * ((s 6)⁻¹ * ((s 1)⁻¹ * ((s 8)⁻¹ * (s 5 * 1))))))) = 1
    at R5
  simp only [hs1 0 (by norm_num), hs1 1 (by norm_num), hs1 2 (by norm_num),
    hs1 3 (by norm_num), hs1 5 (by norm_num), h6, h7, h8, inv_one, one_mul, mul_one]
    at R1 R2 R3 R4 R5
  refine ⟨?_, R2, R3, ?_, ?_⟩
  · simpa only [mul_assoc] using R1
  · simpa only [mul_assoc] using R4
  · simpa only [mul_assoc] using R5

theorem le_card [Finite H] {Q : Subgroup H} (τ : H →* Perm (Fin 5)) (hker : τ.ker = Q)
    (x : Fin 9 → H) (hcard : Nat.card (closure (Set.range x)) = 24 * Nat.card Q)
    {T : Subgroup (Perm (Fin 5))} (hT : ∀ i, τ (x i) ∈ T) : 24 ≤ Nat.card T := by
  have h1 := Subgroup.relIndex_mul_card τ.ker (closure (Set.range x))
  rw [Subgroup.relIndex_ker] at h1
  have h2 : Nat.card (τ.ker ⊓ closure (Set.range x) : Subgroup H) ≤ Nat.card Q := by
    rw [← hker]; exact Subgroup.card_le_of_le inf_le_left
  have h3 : (closure (Set.range x)).map τ ≤ T := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hT i
  have h5 : 24 * Nat.card Q ≤ Nat.card ((closure (Set.range x)).map τ) * Nat.card Q := by
    rw [← hcard, ← h1]; exact Nat.mul_le_mul_left _ h2
  exact (Nat.le_of_mul_le_mul_right h5 Nat.card_pos).trans (Subgroup.card_le_of_le h3)

theorem conj_comp {Q : Subgroup H} {σ : H →* Perm (Fin 5)} (hσ : Function.Surjective σ)
    (hker : σ.ker = Q) (π : Perm (Fin 5)) :
    Function.Surjective ((MulAut.conj π).toMonoidHom.comp σ) ∧
      ((MulAut.conj π).toMonoidHom.comp σ).ker = Q ∧
      ∀ h, (MulAut.conj π).toMonoidHom.comp σ h = π * σ h * π⁻¹ :=
  ⟨(MulAut.conj π).surjective.comp hσ, by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj π).injective, hker], fun _ => rfl⟩

end Letters

end CzSigma

open CzSigma

theorem exists_sigma0 {H : Type*} [Group H] [Finite H] {Q : Subgroup H}
    (σ : H →* Equiv.Perm (Fin 5)) (hσ : Function.Surjective σ) (hker : σ.ker = Q)
    (x : Fin 9 → H)
    (hP12 : ∀ r ∈ czP12Codes, FreeGroup.lift x (FreeGroup.mk (wordOfCodes 9 r)) = 1)
    (hxQ : ∀ i : Fin 9, i.val < 6 → x i ∈ Q)
    (hcard : Nat.card (Subgroup.closure (Set.range x)) = 24 * Nat.card Q) :
    ∃ σ' : H →* Equiv.Perm (Fin 5), Function.Surjective σ' ∧ σ'.ker = Q ∧
      ∀ i : Fin 9, σ' (x i) = czSigma0 i := by
  have hσ1 : ∀ i : Fin 9, i.val < 6 → σ (x i) = 1 := fun i hi =>
    MonoidHom.mem_ker.mp (by rw [hker]; exact hxQ i hi)
  obtain ⟨R1, R2, -, -, R5⟩ := rels σ x hP12 hσ1
  by_cases ha : σ (x 6) = 1
  ·
    exfalso
    rw [ha] at R5
    simp only [mul_one, inv_one, mul_inv_cancel_right] at R5
    have hbc : σ (x 8) = σ (x 7) := (mul_inv_eq_one.mp R5).symm
    have h24 := le_card σ hker x hcard (T := zpowers (σ (x 7)))
      (fin9_cases (fun i hi => by rw [hσ1 i hi]; exact one_mem _) (by rw [ha]; exact one_mem _)
        (mem_zpowers _) (by rw [hbc]; exact mem_zpowers _))
    rw [Nat.card_zpowers] at h24
    have := orderOf_le_of_pow_eq_one (x := σ (x 7)) (by norm_num : 0 < 2)
      (by rw [pow_two]; exact R2)
    omega
  · obtain ⟨π, hπ⟩ := conj_czA0 (σ (x 6)) R1 ha
    obtain ⟨hτs, hτk, hτa⟩ := conj_comp hσ hker π
    generalize (MulAut.conj π).toMonoidHom.comp σ = τ at hτs hτk hτa
    have hτ6 : τ (x 6) = czA0 := (hτa _).trans hπ
    have hτ1 : ∀ i : Fin 9, i.val < 6 → τ (x i) = 1 := fun i hi => by
      rw [hτa, hσ1 i hi, mul_one, mul_inv_cancel]
    obtain ⟨-, S2, S3, S4, S5⟩ := rels τ x hP12 hτ1
    rw [hτ6] at S4 S5
    have hb := mem_czB6 _ S2 S4
    rcases classify _ hb _ (mem_czInv5 _ S3) S5 with ⟨π', hπ', h7, h8⟩ | hN
    · obtain ⟨hs', hk', ha'⟩ := conj_comp hτs hτk π'
      refine ⟨_, hs', hk', fin9_cases (fun i hi => ?_) ?_ ?_ ?_⟩
      · rw [ha', hτ1 i hi, mul_one, mul_inv_cancel, czSigma0, ite_eq_left hi]
      · rw [ha', hτ6, cen6_comm π' hπ', czA0_eq]; rfl
      · rw [ha', h7]; rfl
      · rw [ha', h8]; rfl
    ·
      exfalso
      have h24 := le_card τ hτk x hcard (T := czN12)
        (fin9_cases (fun i hi => by rw [hτ1 i hi]; exact one_mem _)
          (mem_czN12.mpr (by rw [hτ6]; exact Or.inl (by group)))
          (mem_czN12.mpr (Or.inr (czB6_inv _ hb))) (mem_czN12.mpr hN))
      rw [card_czN12] at h24
      omega

theorem exists_comm_swap {H : Type*} [Group H] [Finite H] {Q : Subgroup H}
    (σ : H →* Equiv.Perm (Fin 5)) (hσ : Function.Surjective σ) (hker : σ.ker = Q)
    (hQ : IsPGroup 2 Q) {y : H} (hy : σ y = c[2, 3, 4]) (hy3 : y ^ 3 = 1) :
    ∃ h : H, h * y = y * h ∧ σ h = Equiv.swap 0 1 := by
  rw [← czA0_eq] at hy
  obtain ⟨n₀, hn₀⟩ := hσ (swap 0 1)
  obtain ⟨P, hP⟩ : ∃ P : Subgroup H, P = (zpowers czA0).comap σ := ⟨_, rfl⟩
  have hyP : y ∈ P := by rw [hP, mem_comap, hy]; exact mem_zpowers _
  have hσy' : σ (n₀ * y * n₀⁻¹) = czA0 := by
    rw [map_mul, map_mul, map_inv, hn₀, hy]; decide
  have hy'P : n₀ * y * n₀⁻¹ ∈ P := by rw [hP, mem_comap, hσy']; exact mem_zpowers _
  have hA3 : orderOf czA0 = 3 := orderOf_eq_prime (by decide) (by decide)
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 fun h => by
    rw [h, map_one] at hy; exact absurd hy (by decide)
  have hy'o : orderOf (n₀ * y * n₀⁻¹) = 3 := orderOf_eq_prime
    (by rw [conj_pow, hy3, mul_one, mul_inv_cancel]) fun h => by
      rw [h, map_one] at hσy'; exact absurd hσy' (by decide)
  have hPcard : Nat.card P = 3 * Nat.card Q := by
    have h1 := Subgroup.relIndex_mul_card σ.ker P
    rw [Subgroup.relIndex_ker, hP, Subgroup.map_comap_eq_self_of_surjective hσ, Nat.card_zpowers,
      hA3, inf_eq_left.mpr (MonoidHom.ker_le_comap σ _), hker] at h1
    rw [hP]; exact h1.symm
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  have hsyl : ∀ u ∈ P, orderOf u = 3 →
      ∃ T : Sylow 3 P, ∀ g : P, g ∈ T ↔ (g : H) ∈ zpowers u := by
    intro u hu hou
    have hle : zpowers u ≤ P := zpowers_le.mpr hu
    have hc : Nat.card ((zpowers u).subgroupOf P) = 3 ^ 1 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, hou, pow_one]
    have hi : ¬ 3 ∣ ((zpowers u).subgroupOf P).index := by
      have h1 := Subgroup.relIndex_mul_card (zpowers u) P
      rw [inf_eq_left.mpr hle, Nat.card_zpowers, hou, hPcard, hn] at h1
      have h2 : (zpowers u).relIndex P = 2 ^ n :=
        Nat.eq_of_mul_eq_mul_right (by norm_num) (h1.trans (mul_comm _ _))
      change ¬ 3 ∣ (zpowers u).relIndex P
      rw [h2]
      intro h
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    exact ⟨(IsPGroup.of_card hc).toSylow hi, fun g => by
      rw [IsPGroup.mem_toSylow, mem_subgroupOf]⟩
  obtain ⟨T, hT⟩ := hsyl y hyP hyo
  obtain ⟨T', hT'⟩ := hsyl _ hy'P hy'o
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P T T'
  have hmem : (⟨n₀ * y * n₀⁻¹, hy'P⟩ : P) ∈ MulAut.conj g • (T : Subgroup P) := by
    rw [← Sylow.coe_subgroup_smul, hg]
    exact (hT' _).mpr (mem_zpowers _)
  obtain ⟨s, hs, hgs⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hmem
  rw [MulAut.smul_def, MulAut.conj_apply] at hgs
  have hgs' : (g : H) * s * (g : H)⁻¹ = n₀ * y * n₀⁻¹ := by
    have := congrArg Subtype.val hgs
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  obtain ⟨k, hks⟩ := mem_zpowers_iff.mp ((hT s).mp hs)
  rw [← hks] at hgs'
  have hσP : ∀ u ∈ P, σ u ∈ zpowers czA0 := fun u hu => by rw [hP, mem_comap] at hu; exact hu
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hσP _ g.2)
  have hmk : n₀⁻¹ * g * y ^ k * (n₀⁻¹ * g)⁻¹ = y := by
    calc n₀⁻¹ * g * y ^ k * (n₀⁻¹ * g)⁻¹ = n₀⁻¹ * ((g : H) * y ^ k * (g : H)⁻¹) * n₀ := by group
      _ = y := by rw [hgs']; group
  have hcomm : Commute (swap 0 1 : Perm (Fin 5))⁻¹ czA0 := by
    change (swap 0 1 : Perm (Fin 5))⁻¹ * czA0 = czA0 * (swap 0 1)⁻¹
    decide
  have hk1 : czA0 ^ k = czA0 := by
    have e := congrArg σ hmk
    rw [map_mul, map_mul, map_inv, map_zpow, hy, map_mul, map_inv, hn₀, ← hj] at e
    have hwk : (swap 0 1 : Perm (Fin 5))⁻¹ * czA0 ^ k = czA0 ^ k * (swap 0 1)⁻¹ :=
      (hcomm.zpow_right k).eq
    calc czA0 ^ k = (swap 0 1 : Perm (Fin 5))⁻¹ * czA0 ^ k * (swap 0 1)⁻¹⁻¹ := by
          rw [hwk]; group
      _ = (swap 0 1)⁻¹ * czA0 ^ j * czA0 ^ k * ((swap 0 1)⁻¹ * czA0 ^ j)⁻¹ := by group
      _ = czA0 := e
  have hyk : y ^ k = y := by
    have h1 : czA0 ^ (k - 1) = 1 := by rw [zpow_sub_one, hk1, mul_inv_cancel]
    have h2 : ((orderOf y : ℕ) : ℤ) ∣ k - 1 := by
      rw [hyo, ← hA3]; exact orderOf_dvd_iff_zpow_eq_one.mpr h1
    have h3 := orderOf_dvd_iff_zpow_eq_one.mp h2
    rwa [zpow_sub_one, mul_inv_eq_one] at h3
  rw [hyk] at hmk
  have hm : n₀⁻¹ * g * y = y * (n₀⁻¹ * g) := mul_inv_eq_iff_eq_mul.mp hmk
  refine ⟨n₀⁻¹ * g * y ^ (-j), ?_, ?_⟩
  · calc n₀⁻¹ * g * y ^ (-j) * y = n₀⁻¹ * g * y * y ^ (-j) := by group
      _ = y * (n₀⁻¹ * g) * y ^ (-j) := by rw [hm]
      _ = y * (n₀⁻¹ * g * y ^ (-j)) := by group
  · rw [map_mul, map_mul, map_inv, hn₀, map_zpow, hy, ← hj, mul_assoc, ← zpow_add, add_neg_cancel,
      zpow_zero, mul_one, swap_inv]

end CFSG.ComponentClassification.GMS78.RuCz
