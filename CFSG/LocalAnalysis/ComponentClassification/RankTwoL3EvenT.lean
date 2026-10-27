module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3EvenFrame
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma38Core
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3EvenLift

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoL3Even

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial LinearFlag
  FieldFourCover CFSG.LieType.Chevalley
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2]
  {A : Subgroup G} {ψ : normalizer (A : Set G) →* MulAut (projectiveSL 3 F)}

omit [Finite G] [Finite F] [CharP F 2] in
theorem exists_psi_eq_of_mem_sup
    (hψ : IsActionHom A (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ψ)
    {t : G} (htN : t ∈ normalizer (A : Set G))
    (ht : t ∈ A ⊔ centralizer (A : Set G)) :
    ∃ a : G, ∃ ha : a ∈ A, a⁻¹ * t ∈ centralizer (A : Set G) ∧
      ψ ⟨t, htN⟩ = ψ ⟨a, le_normalizer ha⟩ := by
  have hKN : centralizer (A : Set G) ≤ normalizer (A : Set G) :=
    Subgroup.centralizer_le_normalizer (A : Set G)
  obtain ⟨a, ha, k, hk, hak⟩ := AS76b.exists_mul_of_mem_sup_of_le_normalizer hKN ht
  subst hak
  have hkN : k ∈ normalizer (A : Set G) := hKN hk
  refine ⟨a, ha, by rw [inv_mul_cancel_left]; exact hk, ?_⟩
  rw [psi_mul (le_normalizer ha) hkN, (hψ.eq_one_iff ⟨k, hkN⟩).2 hk, mul_one]

omit [Finite G] [Finite F] [CharP F 2] in
theorem commute_of_mem_sup {t : G} (ht : t ∈ A ⊔ centralizer (A : Set G)) :
    ∀ z ∈ A ⊓ centralizer (A : Set G), t * z = z * t := by
  have hKN : centralizer (A : Set G) ≤ normalizer (A : Set G) :=
    Subgroup.centralizer_le_normalizer (A : Set G)
  obtain ⟨a, ha, k, hk, hak⟩ := AS76b.exists_mul_of_mem_sup_of_le_normalizer hKN ht
  subst hak
  intro z hz
  have h1 : a * z = z * a := mem_centralizer_iff.1 hz.2 a ha
  have h2 : z * k = k * z := mem_centralizer_iff.1 hk z hz.1
  calc a * k * z = a * (z * k) := by rw [mul_assoc, h2]
    _ = z * (a * k) := by rw [← mul_assoc, h1, mul_assoc]

omit [Finite G] [Finite F] [CharP F 2] in
theorem not_mem_centralizer_of_mem_rightConjugate (hA : standardComponentIsStandard A) {g : G}
    (hg : g ∉ normalizer (A : Set G)) {t : G}
    (htK : t ∈ rightConjugate (centralizer (A : Set G)) g) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    t ∉ centralizer (A : Set G) := by
  intro htC
  have hg' : g ∉ normalizer (centralizer (A : Set G) : Set G) := by
    rwa [AS76b.normalizer_centralizer_eq hA]
  have hodd := (AS76b.tightlyEmbedded_centralizer hA).2 g hg'
  have hmem : t ∈ centralizer (A : Set G) ⊓ rightConjugate (centralizer (A : Set G)) g :=
    ⟨htC, htK⟩
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [sq, ht2]) ht1
  have h2 := hodd.of_dvd_nat (hto ▸ Subgroup.orderOf_dvd_natCard _ hmem)
  exact (Nat.not_odd_iff_even.2 even_two) h2

omit [Finite F] [CharP F 2] in
theorem torusSL_mul (l l' : Fˣ) : torusSL l * torusSL l' = torusSL (l * l') := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_torusSL, coe_torusSL, coe_torusSL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  ring

omit [Finite F] [CharP F 2] in
theorem torusSL_one : torusSL (1 : Fˣ) = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [coe_torusSL]
  fin_cases i <;> fin_cases j <;> simp

omit [Finite F] [CharP F 2] in
theorem torusSL_pow (l : Fˣ) (n : ℕ) : torusSL l ^ n = torusSL (l ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, torusSL_one]
  | succ n ih => rw [pow_succ, ih, torusSL_mul, pow_succ]

omit [Finite F] [CharP F 2] in
theorem projTorus_pow_card_sub_one (l : Fˣ) : projTorus F l ^ (Nat.card F - 1) = 1 := by
  have hl : l ^ (Nat.card F - 1) = 1 := by
    rw [← Nat.card_units]
    exact pow_card_eq_one'
  rw [projTorus, ← map_pow, torusSL_pow, hl, torusSL_one, map_one]

theorem exists_pow_eq_one_of_isPGroup {M : Type*} [Group M] {H : Subgroup M} (hH : IsPGroup 2 H)
    {x : M} (hx : x ∈ H) : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hH ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem exists_frame (hA : standardComponentIsStandard A)
    (hψ : IsActionHom A (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ψ)
    (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)))
    {m : ℕ} (hm : 3 ≤ m) (hF : Nat.card F = 2 ^ m)
    (hKey : ∀ c : G, Odd (Nat.card (A ⊓ rightConjugate (centralizer (A : Set G)) c :
      Subgroup G)))
    {g : G} (hg : g ∉ normalizer (A : Set G)) {T : Subgroup G}
    (hTK : T ≤ rightConjugate (centralizer (A : Set G)) g) (hTN : T ≤ normalizer (A : Set G))
    (hTAK : T ≤ A ⊔ centralizer (A : Set G)) (hTe : IsElemAbelian 2 T)
    {t₀ : G} (ht₀ : t₀ ∈ T) (ht₀1 : t₀ ≠ 1) :
    ∃ (γ : MulAut (projectiveSL 3 F)) (l : Fˣ) (w : G) (hwA : w ∈ A),
      (l : F) ^ 3 ≠ 1 ∧ ψ ⟨t₀, hTN ht₀⟩ = γ * MulAut.conj (x0 F) * γ⁻¹ ∧
      ψ ⟨w, le_normalizer hwA⟩ = γ * MulAut.conj (projTorus F l) * γ⁻¹ ∧
      Odd (orderOf w) ∧ w * t₀ = t₀ * w ∧ ∀ s : G, ∀ hs : s ∈ T, ψ ⟨s, hTN hs⟩ ∈ centerA γ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h8 : 8 ≤ Nat.card F := by
    rw [hF]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hTsq : ∀ s ∈ T, s * s = 1 := fun s hs => by rw [← sq]; exact hTe.2 s hs
  have hTcomm : ∀ s ∈ T, ∀ s' ∈ T, s * s' = s' * s := fun s hs s' hs' =>
    congrArg Subtype.val (hTe.1.is_comm.comm ⟨s, hs⟩ ⟨s', hs'⟩)
  have hTX : ∀ s : G, ∀ hs : s ∈ T, ψ ⟨s, hTN hs⟩ ∈
      (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range := by
    intro s hs
    obtain ⟨a, ha, -, h⟩ := exists_psi_eq_of_mem_sup hψ (hTN hs) (hTAK hs)
    rw [h]
    exact hψ.map_mem a ha
  have hTsqψ : ∀ s : G, ∀ hs : s ∈ T, ψ ⟨s, hTN hs⟩ * ψ ⟨s, hTN hs⟩ = 1 := by
    intro s hs
    rw [← psi_mul (hTN hs) (hTN hs)]
    have h1 : (⟨s * s, mul_mem (hTN hs) (hTN hs)⟩ : normalizer (A : Set G)) = 1 :=
      Subtype.ext (hTsq s hs)
    rw [h1, map_one]
  have hτ1 : ψ ⟨t₀, hTN ht₀⟩ ≠ 1 := fun h =>
    not_mem_centralizer_of_mem_rightConjugate hA hg (hTK ht₀) (hTsq t₀ ht₀) ht₀1
      ((hψ.eq_one_iff _).1 h)
  obtain ⟨γ, hγ⟩ := exists_eq_conj_x0 (hTX t₀ ht₀) (hTsqψ t₀ ht₀) hτ1
  obtain ⟨lu, hlu⟩ := LinearCover.exists_units_pow_three_ne_one (K := F) h8
  have hl : (lu : F) ^ 3 ≠ 1 := fun h => hlu (Units.ext (by
    rw [Units.val_pow_eq_pow_val, h, Units.val_one]))
  obtain ⟨w, hwA, hwψ⟩ := hψ.exists_eq _ (conj_mem_innerP γ (projTorus F lu))
  have ht₀Z := commute_of_mem_sup (hTAK ht₀)
  have hcx0 : MulAut.conj (projTorus F lu) * MulAut.conj (x0 F) =
      MulAut.conj (x0 F) * MulAut.conj (projTorus F lu) := by
    rw [← map_mul, ← map_mul, projTorus_mul_comm_of_mem_projCenterW lu x0_mem_projCenterW]
  have hwt₀ : w * t₀ = t₀ * w := by
    refine commute_of_psi_commute hψ hZ (hTN ht₀) (hTsq t₀ ht₀) ht₀Z hwA ?_
    rw [hwψ, hγ]
    calc γ * MulAut.conj (projTorus F lu) * γ⁻¹ * (γ * MulAut.conj (x0 F) * γ⁻¹)
        = γ * (MulAut.conj (projTorus F lu) * MulAut.conj (x0 F)) * γ⁻¹ := by group
      _ = γ * (MulAut.conj (x0 F) * MulAut.conj (projTorus F lu)) * γ⁻¹ := by rw [hcx0]
      _ = γ * MulAut.conj (x0 F) * γ⁻¹ * (γ * MulAut.conj (projTorus F lu) * γ⁻¹) := by group
  have hwodd : Odd (orderOf w) := by
    set q := Nat.card F - 1 with hq
    have hqodd : Odd q := by
      rw [hq, hF]
      exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
    have hz : w ^ q ∈ A ⊓ centralizer (A : Set G) := by
      refine ⟨pow_mem hwA q, (hψ.eq_one_iff ⟨w ^ q, le_normalizer (pow_mem hwA q)⟩).1 ?_⟩
      rw [psi_pow (le_normalizer hwA), hwψ, conj_pow, ← map_pow, projTorus_pow_card_sub_one,
        map_one, mul_one, mul_inv_cancel]
    have hzo := odd_orderOf_of_mem hZ hz
    have hdvd : orderOf w ∣ q * orderOf (w ^ q) := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [pow_mul, pow_orderOf_eq_one]
    exact (hqodd.mul hzo).of_dvd_nat hdvd
  refine ⟨γ, lu, w, hwA, hl, hγ, hwψ, hwodd, hwt₀, fun s hs => ?_⟩
  have hsU : ψ ⟨s, hTN hs⟩ ∈ unipA γ := by
    have h1 : γ⁻¹ * ψ ⟨s, hTN hs⟩ * γ ∈
        (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range := by
      have h2 := conj_mem_innerP γ⁻¹ (Classical.choose (hTX s hs))
      rw [Classical.choose_spec (hTX s hs), inv_inv] at h2
      exact h2
    have h2 : γ⁻¹ * ψ ⟨s, hTN hs⟩ * γ * MulAut.conj (x0 F) =
        MulAut.conj (x0 F) * (γ⁻¹ * ψ ⟨s, hTN hs⟩ * γ) := by
      refine (commute_conj_iff γ _ _).1 ?_
      rw [← hγ, ← psi_mul (hTN hs) (hTN ht₀), ← psi_mul (hTN ht₀) (hTN hs)]
      congr 1
      exact Subtype.ext (hTcomm s hs t₀ ht₀)
    have h3 : (γ⁻¹ * ψ ⟨s, hTN hs⟩ * γ) ^ 2 ^ 1 = 1 := by
      rw [conj_inv_pow, pow_one, sq, hTsqψ s hs, mul_one, inv_mul_cancel]
    obtain ⟨u, hu, hu'⟩ := mem_map_projUnip_of_commute h1 h2 h3
    refine mem_unipA.2 ⟨u, hu, ?_⟩
    rw [hu']
    group
  have key : ∀ a b c : F, a * b = 0 →
      ψ ⟨s, hTN hs⟩ * (γ * MulAut.conj (proj 3 F (unipU F a b c)) * γ⁻¹) =
        γ * MulAut.conj (proj 3 F (unipU F a b c)) * γ⁻¹ * ψ ⟨s, hTN hs⟩ := by
    intro a b c hab
    set cb := γ * MulAut.conj (proj 3 F (unipU F a b c)) * γ⁻¹ with hcb
    have hcbU : cb ∈ unipA γ := mem_unipA.2 ⟨_, mem_projUnip.2 ⟨a, b, c, rfl⟩, rfl⟩
    have hcb2 : cb ^ 2 ^ 2 = 1 := by
      rw [hcb, conj_pow, ← map_pow, ← map_pow]
      have h1 : unipU F a b c ^ 2 ^ 2 = 1 := by
        rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, sq (unipU F a b c), unipU_mul_self,
          hab, sq, unipU_mul_self, mul_zero, unipU_zero]
      rw [h1, map_one, map_one, mul_one, mul_inv_cancel]
    obtain ⟨cc, hccA, -, hccψ⟩ := exists_two_lift hψ (conj_mem_innerP γ _) hcb2
    have hcct : cc * t₀ = t₀ * cc := by
      refine commute_of_psi_commute hψ hZ (hTN ht₀) (hTsq t₀ ht₀) ht₀Z hccA ?_
      rw [hccψ, hγ]
      exact (commute_centerA_unipA (mem_centerA.2 ⟨x0 F, x0_mem_projCenterW, rfl⟩) hcbU).symm
    have htight := AS76b.tightlyEmbedded_rightConjugate (AS76b.tightlyEmbedded_centralizer hA) g
    have hccN : cc ∈ normalizer (rightConjugate (centralizer (A : Set G)) g : Set G) :=
      mem_normalizer_of_commute_of_mem htight (hTK ht₀) ht₀1 (hTsq t₀ ht₀) hcct
    have hmemA : ⁅cc, s⁆ ∈ A := by
      rw [commutatorElement_def]
      have h1 : s * cc⁻¹ * s⁻¹ ∈ A := (mem_normalizer_iff.1 (hTN hs) cc⁻¹).1 (inv_mem hccA)
      have h2 := mul_mem hccA h1
      simpa [mul_assoc] using h2
    have hmemK : ⁅cc, s⁆ ∈ rightConjugate (centralizer (A : Set G)) g := by
      rw [commutatorElement_def]
      have h1 : cc * s * cc⁻¹ ∈ rightConjugate (centralizer (A : Set G)) g :=
        (mem_normalizer_iff.1 hccN s).1 (hTK hs)
      exact mul_mem h1 (inv_mem (hTK hs))
    have hodd := odd_orderOf_of_mem (hKey g) ⟨hmemA, hmemK⟩
    have hψc : ψ ⟨⁅cc, s⁆, le_normalizer hmemA⟩ = ⁅cb, ψ ⟨s, hTN hs⟩⁆ := by
      rw [hcb, ← hccψ]
      exact psi_commutatorElement (le_normalizer hccA) (hTN hs)
    have hU : ⁅cb, ψ ⟨s, hTN hs⟩⁆ ∈ unipA γ := commutatorElement_mem' hcbU hsU
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup (isPGroup_unipA hF γ) hU
    have hodd' : Odd (orderOf ⁅cb, ψ ⟨s, hTN hs⟩⁆) := by
      rw [← hψc]
      refine hodd.of_dvd_nat ?_
      refine (orderOf_map_dvd ψ _).trans ?_
      rw [Subgroup.orderOf_mk]
    have h1 := eq_one_of_odd_of_pow_two hodd' hk
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  exact mem_centerA_of_commute hsU (key 1 0 0 (by ring)) (key 0 1 0 (by ring))

omit [Finite F] [CharP F 2] in
theorem exists_mul_ne_mul_SL2 : ∃ a b : SL2 F, a * b ≠ b * a := by
  refine ⟨uSL 1, vSL 1, fun h => ?_⟩
  have h00 := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  change ((uSL 1 : SL2 F) * (vSL 1 : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
    ((vSL 1 : SL2 F) * (uSL 1 : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 at h00
  simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] at h00

omit [CharP F 2] in
theorem isPerfect_SL2 (h4 : 4 ≤ Nat.card F) : Group.IsPerfect (SL2 F) := by
  have := Fintype.ofFinite F
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
    (show 4 ≤ (Finset.univ : Finset F).card by
      rwa [Finset.card_univ, ← Nat.card_eq_fintype_card])
  exact CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨s, hs⟩

theorem mem_normalizer_of_mem_normalizer_sylow {K R : Subgroup G} (hK : TightlyEmbedded K)
    (hR : IsSylowOf 2 R K) (hR1 : R ≠ ⊥) {y : G} (hy : y ∈ normalizer (R : Set G)) :
    y ∈ normalizer (K : Set G) := by
  by_contra hyK
  have hodd := hK.2 y hyK
  have hle : R ≤ K ⊓ rightConjugate K y := by
    refine le_inf hR.le fun r hr => ?_
    rw [mem_rightConjugate_iff]
    exact hR.le ((mem_normalizer_iff.1 hy r).1 hr)
  exact hR1 (two_subgroup_of_odd_eq_bot R _ hR.isPGroup hodd hle)

omit [Finite G] in
theorem mem_centralizer_zpowers_iff {w x : G} :
    x ∈ centralizer (zpowers w : Set G) ↔ w * x = x * w := by
  rw [zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff, eq_comm]

omit [Finite F] [CharP F 2] in
theorem inv_pow_three_ne_one {l : Fˣ} (hl : (l : F) ^ 3 ≠ 1) : l⁻¹ ^ 3 ≠ 1 := by
  intro h
  apply hl
  have h1 := congrArg (fun u : Fˣ => (u : F)) h
  simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_one, inv_pow,
    inv_eq_one] at h1
  exact h1

section Levi

variable (hψ : IsActionHom A
    (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ψ)
  {γ : MulAut (projectiveSL 3 F)} {l : Fˣ} {w : G} (hwA : w ∈ A)
  (hwψ : ψ ⟨w, le_normalizer hwA⟩ = γ * MulAut.conj (projTorus F l) * γ⁻¹)
include hψ hwψ

omit hψ [Finite G] [Finite F] [CharP F 2] in
theorem psi_w_eq : ψ ⟨w, le_normalizer hwA⟩ = γ * conjAut 3 F (torusGL (l⁻¹ ^ 3)) * γ⁻¹ := by
  rw [hwψ, conj_projTorus]

omit [Finite G] [Finite F] [CharP F 2] in
theorem leviLift_le_inf_centralizer :
    leviLift ψ (leviA γ) ≤ A ⊓ centralizer (zpowers w : Set G) := by
  refine le_inf leviLift_le fun x hx => ?_
  have h := leviLift_le_centralizer hψ (le_normalizer hwA) (fun s hs => ?_) hx
  · rw [mem_centralizer_zpowers_iff]
    exact (mem_centralizer_singleton_iff.1 h).symm
  · rw [psi_w_eq hwA hwψ]
    exact commute_torus_leviA _ γ hs

omit hψ [Finite G] [Finite F] [CharP F 2] in
theorem normalizer_inf_centralizer_le [Group.IsPerfect (SL2 F)] (hl : (l : F) ^ 3 ≠ 1) :
    normalizer (A : Set G) ⊓ centralizer (zpowers w : Set G) ≤
      normalizer (leviLift ψ (leviA γ) : Set G) := by
  intro y hy
  obtain ⟨hyN, hyW⟩ := mem_inf.1 hy
  refine mem_normalizer_leviLift hyN (mem_normalizer_leviA (inv_pow_three_ne_one hl) ?_)
  rw [← psi_w_eq hwA hwψ, ← psi_mul hyN (le_normalizer hwA), ← psi_mul (le_normalizer hwA) hyN]
  congr 1
  exact Subtype.ext ((mem_centralizer_zpowers_iff.1 hyW).symm)

theorem isSylowOf_inf_centralizer [Group.IsPerfect (SL2 F)] (hl : (l : F) ^ 3 ≠ 1)
    (hA : standardComponentIsStandard A) {R : Subgroup G}
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hR1 : R ≠ ⊥) :
    IsSylowOf 2 R (centralizer (zpowers w : Set G) ⊓
      centralizer (leviLift ψ (leviA γ) : Set G) ⊓ normalizer (R : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKW : centralizer (A : Set G) ≤ centralizer (zpowers w : Set G) :=
    centralizer_le ((zpowers_le).2 hwA)
  have hKL : centralizer (A : Set G) ≤ centralizer (leviLift ψ (leviA γ) : Set G) :=
    centralizer_le leviLift_le
  have hRle : R ≤ centralizer (zpowers w : Set G) ⊓
      centralizer (leviLift ψ (leviA γ) : Set G) ⊓ normalizer (R : Set G) :=
    le_inf (le_inf (hR.le.trans hKW) (hR.le.trans hKL)) le_normalizer
  obtain ⟨S, hS, hRS⟩ := AS76b.exists_isSylowOf_le hRle hR.isPGroup
  have hSK : S ≤ centralizer (A : Set G) := by
    intro y hy
    obtain ⟨⟨hyW, hyL⟩, hyR⟩ := hS.le hy
    have hyNK := mem_normalizer_of_mem_normalizer_sylow (AS76b.tightlyEmbedded_centralizer hA)
      hR hR1 hyR
    have hyN : y ∈ normalizer (A : Set G) := by rwa [← AS76b.normalizer_centralizer_eq hA]
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup hS.isPGroup hy
    have hψk : (ψ ⟨y, hyN⟩) ^ 2 ^ k = 1 := by
      rw [← psi_pow hyN]
      have h1 : (⟨y ^ 2 ^ k, pow_mem hyN _⟩ : normalizer (A : Set G)) = 1 := Subtype.ext hk
      rw [h1, map_one]
    have hc : ψ ⟨y, hyN⟩ * (γ * conjAut 3 F (torusGL (l⁻¹ ^ 3)) * γ⁻¹) =
        γ * conjAut 3 F (torusGL (l⁻¹ ^ 3)) * γ⁻¹ * ψ ⟨y, hyN⟩ := by
      rw [← psi_w_eq hwA hwψ, ← psi_mul hyN (le_normalizer hwA),
        ← psi_mul (le_normalizer hwA) hyN]
      congr 1
      exact Subtype.ext (mem_centralizer_zpowers_iff.1 hyW).symm
    have hL : ∀ s ∈ leviA γ, ψ ⟨y, hyN⟩ * s = s * ψ ⟨y, hyN⟩ := by
      intro s hs
      obtain ⟨x, hx, hxs⟩ := exists_mem_leviLift hψ (leviA_le_innerP γ) (commutator_leviA γ) hs
      rw [← hxs, ← psi_mul hyN (le_normalizer (leviLift_le hx)),
        ← psi_mul (le_normalizer (leviLift_le hx)) hyN]
      congr 1
      exact Subtype.ext (mem_centralizer_iff.1 hyL x hx).symm
    exact (hψ.eq_one_iff ⟨y, hyN⟩).1
      (eq_one_of_commute_leviA (inv_pow_three_ne_one hl) hψk hc hL)
  have hSR : S = R := hR.eq_of_le hRS hSK hS.isPGroup
  rw [hSR] at hS
  exact hS

omit hwψ [Finite F] [CharP F 2] in
theorem le_sup_leviLift [Group.IsPerfect (SL2 F)]
    (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G))) {T R : Subgroup G}
    (hTN : T ≤ normalizer (A : Set G)) (hTAK : T ≤ A ⊔ centralizer (A : Set G))
    (hTe : IsElemAbelian 2 T) (hTR : ⁅T, R⁆ = ⊥) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hT : ∀ s : G, ∀ hs : s ∈ T, ψ ⟨s, hTN hs⟩ ∈ centerA γ) :
    T ≤ R ⊔ leviLift ψ (leviA γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro s hs
  obtain ⟨a, ha, hak, hψa⟩ := exists_psi_eq_of_mem_sup hψ (hTN hs) (hTAK hs)
  obtain ⟨e, -, he2, he3, -⟩ := exists_twoPartExp G
  have hcomm : Commute a (a⁻¹ * s) := mem_centralizer_iff.1 hak a ha
  have hs2 : s ^ 2 ^ 1 = 1 := by rw [pow_one]; exact hTe.2 s hs
  have hse : s = a ^ e * (a⁻¹ * s) ^ e := by
    calc s = s ^ e := (he3 s 1 hs2).symm
      _ = (a * (a⁻¹ * s)) ^ e := by rw [mul_inv_cancel_left]
      _ = a ^ e * (a⁻¹ * s) ^ e := hcomm.mul_pow e
  have haS : a ∈ liftIn ψ (leviA γ) :=
    mem_liftIn.2 ⟨ha, by rw [← hψa]; exact centerA_le_leviA γ (hT s hs)⟩
  have hae : a ^ e ∈ leviLift ψ (leviA γ) :=
    mem_leviLift_of_pow hψ (leviA_le_innerP γ) (commutator_leviA γ) hZ (pow_mem haS e) (he2 a)
  have hsR : ∀ r ∈ R, s * r = r * s := by
    have h1 := (commutator_eq_bot_iff_le_centralizer.1 hTR) hs
    intro r hr
    exact (mem_centralizer_iff.1 h1 r hr).symm
  have hkC : (a⁻¹ * s) ^ e ∈ centralizer (A : Set G) := pow_mem hak e
  have hkR : ∀ r ∈ R, (a⁻¹ * s) ^ e * r = r * (a⁻¹ * s) ^ e := by
    intro r hr
    have hrA : r ∈ centralizer (A : Set G) := hR.le hr
    have har : a ^ e * r = r * a ^ e := mem_centralizer_iff.1 hrA _ (pow_mem ha e)
    have hk : (a⁻¹ * s) ^ e = (a ^ e)⁻¹ * s := by
      calc (a⁻¹ * s) ^ e = (a ^ e)⁻¹ * (a ^ e * (a⁻¹ * s) ^ e) := by group
        _ = (a ^ e)⁻¹ * s := by rw [← hse]
    rw [hk]
    calc (a ^ e)⁻¹ * s * r = (a ^ e)⁻¹ * (r * s) := by rw [mul_assoc, hsR r hr]
      _ = (a ^ e)⁻¹ * r * (a ^ e) * ((a ^ e)⁻¹ * s) := by group
      _ = r * ((a ^ e)⁻¹ * s) := by
        rw [show (a ^ e)⁻¹ * r * a ^ e = r by rw [mul_assoc, ← har, ← mul_assoc, inv_mul_cancel,
          one_mul]]
  have hkmem : (a⁻¹ * s) ^ e ∈ R := by
    have hP : IsPGroup 2 (zpowers ((a⁻¹ * s) ^ e) ⊔ R : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow_two (he2 _)) hR.isPGroup
        ((zpowers_le).2 (Subgroup.centralizer_le_normalizer (R : Set G)
          (mem_centralizer_iff.2 fun r hr => (hkR r hr).symm)))
    have heq : zpowers ((a⁻¹ * s) ^ e) ⊔ R = R :=
      hR.eq_of_le le_sup_right (sup_le ((zpowers_le).2 hkC) hR.le) hP
    exact heq ▸ mem_sup_left (mem_zpowers _)
  rw [hse]
  exact mul_mem (mem_sup_right hae) (mem_sup_left hkmem)

end Levi

end CFSG.ComponentClassification.RankTwoL3Even

