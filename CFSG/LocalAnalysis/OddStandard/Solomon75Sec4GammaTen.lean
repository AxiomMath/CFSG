module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GammaSmall
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GammaPairs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Order

public section

namespace CFSG.OddStandard.Solomon75.AhatData

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG CFSG.GH74.GLS

section Ten

abbrev embTen : Fin 8 ↪ Fin 10 := Fin.castLEEmb (by norm_num)

noncomputable def vExt : Perm (Fin 8) →* Perm (Fin 10) := Perm.viaEmbeddingHom embTen

theorem vExt_apply_ge (q : Perm (Fin 8)) (x : Fin 10) (hx : 8 ≤ x.val) : vExt q x = x := by
  rw [vExt, Perm.viaEmbeddingHom_apply]
  apply Perm.viaEmbedding_apply_of_notMem
  rintro ⟨i, rfl⟩
  have := i.2
  simp [Fin.castLEEmb] at hx
  omega

theorem vExt_apply_lt (q : Perm (Fin 8)) (i : Fin 8) : vExt q (embTen i) = embTen (q i) := by
  rw [vExt, Perm.viaEmbeddingHom_apply]
  exact Perm.viaEmbedding_apply q embTen i

theorem sign_vExt (q : Perm (Fin 8)) : sign (vExt q) = sign q := by
  rw [vExt, Perm.viaEmbeddingHom_apply, Perm.viaEmbedding, Perm.sign_extendDomain]

theorem vExt_injective : Function.Injective vExt := Perm.viaEmbeddingHom_injective embTen

def invEight : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 5

def invTen : Perm (Fin 10) := swap 0 1 * swap 2 3 * swap 4 5

theorem vExt_invEight : vExt invEight = invTen := by
  ext x
  by_cases hx : x.val < 8
  · have : x = embTen ⟨x.val, hx⟩ := by ext; simp [Fin.castLEEmb]
    rw [this, vExt_apply_lt]
    generalize (⟨x.val, hx⟩ : Fin 8) = i
    revert i
    decide
  · have h8 : 8 ≤ x.val := by omega
    rw [vExt_apply_ge _ _ h8]
    have h8' : x = 8 ∨ x = 9 := by
      have := x.2
      omega
    rcases h8' with rfl | rfl <;> decide

theorem swap89_mul_vExt (q : Perm (Fin 8)) : swap (8 : Fin 10) 9 * vExt q = vExt q * swap 8 9 :=
  swap_mul_comm_of_fix (vExt_apply_ge q 8 (by simp)) (vExt_apply_ge q 9 (by simp))

noncomputable def twist10 : Perm (Fin 8) →* Perm (Fin 10) where
  toFun q := vExt q * (if sign q = 1 then 1 else swap 8 9)
  map_one' := by simp
  map_mul' q r := by
    have hs2 : swap (8 : Fin 10) 9 * swap 8 9 = 1 := swap_mul_self _ _
    have hq := Int.units_eq_one_or (sign q)
    have hr := Int.units_eq_one_or (sign r)
    rcases hq with hq | hq <;> rcases hr with hr | hr
    · have hqr : sign (q * r) = 1 := by rw [Perm.sign_mul, hq, hr]; rfl
      simp [hq, hr, hqr, map_mul]
    · have hqr : sign (q * r) = -1 := by rw [Perm.sign_mul, hq, hr]; rfl
      have h1 : ¬ (sign (q * r) = 1) := by rw [hqr]; decide
      have h2 : ¬ (sign r = 1) := by rw [hr]; decide
      simp [hq, h2, map_mul, mul_assoc]
    · have hqr : sign (q * r) = -1 := by rw [Perm.sign_mul, hq, hr]; rfl
      have h1 : ¬ (sign (q * r) = 1) := by rw [hqr]; decide
      have h2 : ¬ (sign q = 1) := by rw [hq]; decide
      simp only [hr, h2, map_mul, ite_true, ite_false, mul_one]
      rw [mul_assoc, mul_assoc, swap89_mul_vExt]
    · have hqr : sign (q * r) = 1 := by rw [Perm.sign_mul, hq, hr]; rfl
      have h1 : ¬ (sign q = 1) := by rw [hq]; decide
      have h2 : ¬ (sign r = 1) := by rw [hr]; decide
      simp only [hqr, h1, h2, map_mul, ite_true, ite_false, mul_one]
      calc vExt q * vExt r = vExt q * (swap 8 9 * swap 8 9) * vExt r := by rw [hs2]; group
        _ = vExt q * swap 8 9 * (swap 8 9 * vExt r) := by group
        _ = vExt q * swap 8 9 * (vExt r * swap 8 9) := by rw [swap89_mul_vExt]

theorem twist10_of_even {q : Perm (Fin 8)} (hq : sign q = 1) : twist10 q = vExt q := by
  simp [twist10, hq]

theorem twist10_of_odd {q : Perm (Fin 8)} (hq : sign q = -1) :
    twist10 q = vExt q * swap 8 9 := by
  have : ¬ (sign q = 1) := by rw [hq]; decide
  simp [twist10, this]

theorem sign_twist10 (q : Perm (Fin 8)) : sign (twist10 q) = 1 := by
  rcases Int.units_eq_one_or (sign q) with hq | hq
  · rw [twist10_of_even hq, sign_vExt, hq]
  · rw [twist10_of_odd hq, Perm.sign_mul, sign_vExt, hq, Perm.sign_swap (by decide)]
    rfl

end Ten

section TenMain

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem isPGroup_ker_rho {n : ℕ} (C : CoverSetup n K) : IsPGroup 2 C.ρ.ker := by
  refine IsPGroup.of_card (n := 1) ?_
  have : C.ρ.ker = center K := by
    ext x
    rw [MonoidHom.mem_ker, C.ρ_eq_one_iff]
  rw [this, C.center_card, pow_one]

theorem map_vExt_inf_le (Q : Subgroup (Perm (Fin 8))) :
    (Q ⊓ alternatingGroup (Fin 8)).map vExt ≤
      Q.map twist10 ⊓ altEmb embTen := by
  rintro _ ⟨q, ⟨hqQ, hqA⟩, rfl⟩
  have hq : sign q = 1 := Perm.mem_alternatingGroup.1 hqA
  refine ⟨⟨q, hqQ, twist10_of_even hq⟩, fun x hx => ?_, by rw [sign_vExt, hq]⟩
  have : 8 ≤ x.val := by
    by_contra h
    exact hx ⟨⟨x.val, by omega⟩, by ext; simp [Fin.castLEEmb]⟩
  exact vExt_apply_ge q x this

theorem exists_sylow_gamma_eq_top_ten
    (C : CoverSetup 10 K) : ∃ S : Sylow 2 K, properTwoGenCoreGamma (S : Subgroup K) 2 = ⊤ := by
  have hu8sq : invEight * invEight = 1 := by decide
  have hu8odd : sign invEight = -1 := by decide
  have hu81 : invEight ≠ 1 := by decide
  have hpg : IsPGroup 2 (Subgroup.zpowers invEight) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hu8sq) hu81]
    simp
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  have hu8Q : invEight ∈ (Q : Subgroup (Perm (Fin 8))) := hQ (Subgroup.mem_zpowers invEight)
  set R : Subgroup (Perm (Fin 10)) := (Q : Subgroup (Perm (Fin 8))).map twist10 with hR
  have hRp : IsPGroup 2 R := Q.isPGroup'.map twist10
  have hRA : R ≤ alternatingGroup (Fin 10) := by
    rintro _ ⟨q, -, rfl⟩
    exact Perm.mem_alternatingGroup.2 (sign_twist10 q)
  set W : Subgroup K := R.comap C.ρ with hW
  have hWp : IsPGroup 2 W := hRp.comap_of_ker_isPGroup C.ρ (isPGroup_ker_rho C)
  obtain ⟨S, hWS⟩ := hWp.exists_le_sylow
  obtain ⟨L, hL, hmap, hcen⟩ :=
    exists_doubleCover_altEmb (n := 10) (m := 8) (by norm_num) (by norm_num) C embTen
  have hLeq : L = (altEmb embTen).comap C.ρ := eq_comap_altEmb hmap hcen
  have hLcard : Nat.card ↥L = Nat.factorial 8 := card_K_eq (by norm_num) hL
  have hB₀p : IsPGroup 2 (W.subgroupOf L) := hWp.comap_subtype
  obtain ⟨B, hB⟩ := hB₀p.exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup (Perm (Fin 8))) = 2 ^ 7 := by
    rw [Q.card_eq_multiplicity, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin,
      factorization_two_factorial_eight]
  have hQA : Nat.card ↥((Q : Subgroup (Perm (Fin 8))) ⊓ alternatingGroup (Fin 8)) * 2 =
      Nat.card (Q : Subgroup (Perm (Fin 8))) :=
    card_inf_alternating_mul_two hu8Q hu8odd
  have hRinf : 2 ^ 6 ≤ Nat.card ↥(R ⊓ altEmb embTen) := by
    have hsub : ((Q : Subgroup (Perm (Fin 8))) ⊓ alternatingGroup (Fin 8)).map vExt ≤
        R ⊓ altEmb embTen := map_vExt_inf_le (Q : Subgroup (Perm (Fin 8)))
    have h1 := Subgroup.card_le_of_le hsub
    rw [Subgroup.card_map_of_injective vExt_injective] at h1
    omega
  have hWL : 2 ^ 7 ≤ Nat.card ↥(W.subgroupOf L) := by
    have h1 : (W.subgroupOf L).map L.subtype = W ⊓ L := by
      rw [Subgroup.subgroupOf_map_subtype, inf_comm]
    have h2 : Nat.card (W.subgroupOf L) = Nat.card ↥(W ⊓ L) := by
      rw [← h1, Subgroup.card_map_of_injective L.subtype_injective]
    have h3 : W ⊓ L = (R ⊓ altEmb embTen).comap C.ρ := by
      rw [hLeq, hW, Subgroup.comap_inf]
    rw [h2, h3, C.card_comap ((inf_le_right).trans (altEmb_le_alternatingGroup embTen))]
    omega
  have hBcard : Nat.card (B : Subgroup ↥L) = 2 ^ 7 := by
    rw [B.card_eq_multiplicity, hLcard, factorization_two_factorial_eight]
  have hBeq : W.subgroupOf L = (B : Subgroup ↥L) :=
    Subgroup.eq_of_le_of_card_ge hB (by rw [hBcard]; exact hWL)
  have hBS : (B : Subgroup ↥L).map L.subtype ≤ (S : Subgroup K) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← hBeq] at hb
    exact hWS (Subgroup.mem_subgroupOf.1 hb)
  have hLΓ : L ≤ properTwoGenCoreGamma (S : Subgroup K) 2 := le_gamma_of_sylow_subcover hL B hBS
  refine ⟨S, ?_⟩
  set H := (properTwoGenCoreGamma (S : Subgroup K) 2).map C.ρ with hH
  have hAltH : altEmb embTen ≤ H := by rw [← hmap]; exact Subgroup.map_mono hLΓ
  set a' : Perm (Fin 10) := invTen * swap 8 9 with ha'
  have ha'R : a' ∈ R := ⟨invEight, hu8Q, by rw [twist10_of_odd hu8odd, vExt_invEight]⟩
  have ha'2 : a' * a' = 1 := by decide
  have ha'1 : a' ≠ 1 := by decide
  have ha's : sign a' = 1 := by decide
  have ha'8 : 8 ∣ a'.support.card := by
    have : a'.support.card = 8 := by decide
    rw [this]
  have hE : ((pairSub a' ha'2).comap C.ρ : Subgroup K) ≤ (S : Subgroup K) :=
    (Subgroup.comap_mono (pairSub_le_of_mem ha'2 ha'R)).trans hWS
  have hr := C.two_le_pRank_comap_pairSub (by norm_num : 8 ≤ 10) ha'2 ha'1 ha's ha'8
  set g : Perm (Fin 10) := swap 0 8 * swap 1 9 with hg
  have hgs : sign g = 1 := by decide
  have hga : g * a' = a' * g := by decide
  have hgH : g ∈ H := by
    obtain ⟨y, hy⟩ := C.exists_ρ_eq hgs
    have hyN := C.mem_normalizer_comap_pairSub ha'2 (x := y) (by rw [hy]; exact hga)
    exact ⟨y, normalizer_le_gamma hE hr hyN, hy⟩
  let FA : Finset (Fin 10) := Finset.univ.filter (fun x : Fin 10 => x.val < 8)
  let FB : Finset (Fin 10) := Finset.univ.filter (fun x : Fin 10 => 2 ≤ x.val)
  let F : Fin 2 → Finset (Fin 10) := fun i => if i = 0 then FA else FB
  have hFA : ∀ x : Fin 10, x ∈ FA ↔ x.val < 8 := fun x => by simp [FA]
  have hFB : ∀ x : Fin 10, x ∈ FB ↔ 2 ≤ x.val := fun x => by simp [FB]
  have h3 : ∀ i, 3 ≤ (F i).card := by
    intro i
    by_cases hi : i = 0
    · simp only [F, hi, ite_true]
      decide
    · simp only [F, hi, ite_false]
      decide
  have hF0 : ∀ a b c : Fin 10, a ∈ FA → b ∈ FA → c ∈ FA → a ≠ b → a ≠ c → b ≠ c →
      swap a b * swap a c ∈ H := by
    intro a b c ha hb hc hab hac hbc
    rw [hFA] at ha hb hc
    refine hAltH ⟨fun x hx => ?_, ?_⟩
    · have hx8 : 8 ≤ x.val := by
        by_contra h
        exact hx ⟨⟨x.val, by omega⟩, by ext; simp [Fin.castLEEmb]⟩
      have h1 : x ≠ a := fun h => by rw [h] at hx8; omega
      have h2 : x ≠ b := fun h => by rw [h] at hx8; omega
      have h3 : x ≠ c := fun h => by rw [h] at hx8; omega
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne h1 h3, swap_apply_of_ne_of_ne h1 h2]
    · rw [Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hac]
      rfl
  have hgdec : ∀ x : Fin 10, 2 ≤ x.val → (g x).val < 8 := by decide
  have hF1 : ∀ a b c : Fin 10, a ∈ FB → b ∈ FB → c ∈ FB → a ≠ b → a ≠ c → b ≠ c →
      swap a b * swap a c ∈ H := by
    intro a b c ha hb hc hab hac hbc
    rw [hFB] at ha hb hc
    have key := hF0 (g a) (g b) (g c) ((hFA _).2 (hgdec a ha)) ((hFA _).2 (hgdec b hb))
      ((hFA _).2 (hgdec c hc)) (g.injective.ne hab) (g.injective.ne hac) (g.injective.ne hbc)
    have e1 : swap (g a) (g b) * swap (g a) (g c) = g * (swap a b * swap a c) * g⁻¹ := by
      rw [swap_apply_apply g a b, swap_apply_apply g a c]
      group
    rw [e1] at key
    have e2 : swap a b * swap a c = g⁻¹ * (g * (swap a b * swap a c) * g⁻¹) * g := by group
    rw [e2]
    exact H.mul_mem (H.mul_mem (H.inv_mem hgH) key) hgH
  have hFH : ∀ (i : Fin 2) (a b c : Fin 10), a ∈ F i → b ∈ F i → c ∈ F i → a ≠ b → a ≠ c →
      b ≠ c → swap a b * swap a c ∈ H := by
    intro i
    by_cases hi : i = 0
    · simp only [F, hi, ite_true]
      exact hF0
    · simp only [F, hi, ite_false]
      exact hF1
  have hstar : ∀ x : Fin 10, ∃ i, x ∈ F i ∧ (2 : Fin 10) ∈ F i := by
    intro x
    by_cases hx : x.val < 8
    · exact ⟨0, by simp only [F, ite_true]; exact (hFA x).2 hx, by
        simp only [F, ite_true]; exact (hFA 2).2 (by decide)⟩
    · exact ⟨1, by simp only [F]; simp; exact (hFB x).2 (by omega), by
        simp only [F]; simp; exact (hFB 2).2 (by decide)⟩
  have hAlt := alt_le_of_star H 2 F h3 hFH hstar
  have hcen' : center K ≤ properTwoGenCoreGamma (S : Subgroup K) 2 :=
    center_le_gamma hE hr
  rw [eq_top_iff]
  intro k _
  obtain ⟨γ, hγ, hγk⟩ := hAlt (Perm.mem_alternatingGroup.2 (C.sign_ρ k))
  have hkγ : k * γ⁻¹ ∈ center K := by
    rw [← C.ρ_eq_one_iff, map_mul, map_inv, hγk, mul_inv_cancel]
  have : k = (k * γ⁻¹) * γ := by group
  rw [this]
  exact Subgroup.mul_mem _ (hcen' hkγ) hγ

end TenMain

end CFSG.OddStandard.Solomon75.AhatData
