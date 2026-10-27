module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcCentTwNFix
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNGenTorus
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Two

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.SeitzGeneration (e6TwoWord e6Two_pow)
open CFSG.Timmesfeld.ExceptionalOrders (zpowMatrix zpowMatrix_apply)
open CFSG.HardMathSupport.Curtis.UnitaryLevi (Smat wordW)
open scoped Matrix

section Data

@[expose] def E6A : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  !![1, 1, 2, 2, 1, 0; 0, -1, 0, 0, 0, 0; 0, 0, -1, 0, 0, 0; 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, -1, 0;
    0, 1, 1, 2, 2, 1]

@[expose] def E6B : Matrix (Fin Tag.E6.rank) (Fin 4) ℤ :=
  !![1, 0, 0, 0; 2, -2, -3, -4; -2, 0, 1, 2; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def E6Bp : Matrix (Fin 4) (Fin Tag.E6.rank) ℤ :=
  !![1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]

theorem E6A_sq : E6A * E6A = 1 := by decide +kernel

theorem E6A_mul_B : E6A * E6B = -E6B := by decide +kernel

theorem E6Bp_mul_B : E6Bp * E6B = 1 := by decide +kernel

theorem E6A_add_one_mul_one_sub : (E6A + 1) * (1 - E6A) = 0 := by decide +kernel

theorem E6_kernel_eq (x : Fin Tag.E6.rank → ℤ) (hx : (E6A + 1) *ᵥ x = 0) :
    x = E6B *ᵥ (E6Bp *ᵥ x) := by
  have key : ∀ (A : Matrix (Fin 6) (Fin 6) ℤ) (B : Matrix (Fin 6) (Fin 4) ℤ)
      (Bp : Matrix (Fin 4) (Fin 6) ℤ),
      A = !![1, 1, 2, 2, 1, 0; 0, -1, 0, 0, 0, 0; 0, 0, -1, 0, 0, 0; 0, 0, 0, -1, 0, 0;
        0, 0, 0, 0, -1, 0; 0, 1, 1, 2, 2, 1] →
      B = !![1, 0, 0, 0; 2, -2, -3, -4; -2, 0, 1, 2; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] →
      Bp = !![1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1] →
      ∀ y : Fin 6 → ℤ, (A + 1) *ᵥ y = 0 → y = B *ᵥ (Bp *ᵥ y) := by
    rintro A B Bp rfl rfl rfl y hy
    have h2 := congrFun hy 0
    have h6 := congrFun hy 5
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply] at h2 h6
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> omega
  exact key E6A E6B E6Bp rfl rfl rfl x hx

end Data

section Ract

variable {C : Type} [CommGroup C] {m n p : ℕ}

@[expose] def ract (M : Matrix (Fin m) (Fin n) ℤ) (t : Fin n → C) : Fin m → C :=
  fun k => ∏ j, t j ^ M k j

theorem mactC_eq_ract {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ) (t : Fin r → C) :
    mactC M t = ract M t := rfl

theorem ract_mul (M : Matrix (Fin m) (Fin n) ℤ) (N : Matrix (Fin n) (Fin p) ℤ) (t : Fin p → C) :
    ract (M * N) t = ract M (ract N t) := by
  ext1 k
  simp only [ract, Matrix.mul_apply, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← prod_zpow_sum_ab]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem ract_one {r : ℕ} (t : Fin r → C) : ract (1 : Matrix (Fin r) (Fin r) ℤ) t = t :=
  mactC_one t

theorem ract_mul_apply (M : Matrix (Fin m) (Fin n) ℤ) (s t : Fin n → C) :
    ract M (s * t) = ract M s * ract M t := by
  ext1 k
  simp [ract, mul_zpow, Finset.prod_mul_distrib]

theorem ract_one_vec (M : Matrix (Fin m) (Fin n) ℤ) : ract M (1 : Fin n → C) = 1 := by
  ext1 k
  simp [ract]

theorem ract_neg (M : Matrix (Fin m) (Fin n) ℤ) (t : Fin n → C) :
    ract (-M) t = (ract M t)⁻¹ := by
  ext1 k
  simp [ract, Finset.prod_inv_distrib]

theorem ract_inv (M : Matrix (Fin m) (Fin n) ℤ) (t : Fin n → C) :
    ract M t⁻¹ = (ract M t)⁻¹ := by
  ext1 k
  simp only [ract, Pi.inv_apply, Pi.inv_apply, Finset.prod_inv_distrib, inv_zpow]

theorem ract_pow (M : Matrix (Fin m) (Fin n) ℤ) (t : Fin n → C) (k : ℕ) :
    ract M (t ^ k) = (ract M t) ^ k := by
  ext1 i
  simp only [ract, Pi.pow_apply, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← zpow_natCast (t j) k, ← zpow_natCast (t j ^ M i j) k, ← zpow_mul, ← zpow_mul, mul_comm]

theorem ract_vecTC (M : Matrix (Fin m) (Fin n) ℤ) (w : Fin n → ℤ) (g : C) :
    ract M (vecTC w g) = vecTC (M.mulVec w) g := by
  ext1 k
  simp only [ract, vecTC, ← zpow_mul, Matrix.mulVec, dotProduct]
  rw [← prod_zpow_sum_ab]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem vecTC_eq_of_dvd_gen {r : ℕ} (w w' : Fin r → ℤ) (g : C) (N : ℕ) (hg : orderOf g = N)
    (h : ∀ i, (N : ℤ) ∣ w i - w' i) : vecTC w g = vecTC w' g := by
  ext1 k
  simp only [vecTC]
  rw [zpow_eq_zpow_iff_modEq, hg]
  exact (Int.modEq_iff_dvd.2 (by simpa using (h k))).symm

end Ract

section Torus

variable
  {F L : Type} [Field F] [Finite F] [Field L] [Algebra F L] [IsAlgClosure F L]
  (Fr : L →+* L)

abbrev wE6W : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd e6TwoWord

theorem Atw_wE6 : Atw wE6W = E6A := by
  show Atw (wordW Tag.E6 e6TwoWord) = E6A
  rw [Atw_wordW]
  decide +kernel

theorem weylTuple_eq_mactC {τ : Tag} (w : WeylGroup τ) {L : Type} [Field L]
    (a : Fin τ.rank → Lˣ) : weylTuple w a = mactC (Atw w) a := by
  funext i
  rw [weylTuple_eq_zpowMatrix, zpowMatrix_apply]
  simp [mactC, Atw]

abbrev TE6 (Fr : L →+* L) : Subgroup (ModGL Tag.E6 L) :=
  twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) L wE6W) (Units.map (entrywiseHom Fr))

variable {Fr}

theorem rootDiagUnit_mem_TE6_iff (hFr : ∀ c, Fr c = c ^ Nat.card F) (a : Fin Tag.E6.rank → Lˣ) :
    rootDiagUnit Tag.E6 a ∈ TE6 Fr ↔ mactC E6A (a ^ Nat.card F) = a := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  rw [mem_twistedTorusOf_iff_negPhi, negPhi_rootDiagUnit_gen_pow Fr wE6W hFr, weylTuple_eq_mactC,
    Atw_wE6]
  constructor
  · rintro ⟨-, h⟩
    exact rootDiagUnit_injective h
  · intro h
    exact ⟨rootDiagUnit_mem_torusGroup a, congrArg _ h⟩

theorem mem_TE6_iff (hFr : ∀ c, Fr c = c ^ Nat.card F) (t : ModGL Tag.E6 L) :
    t ∈ TE6 Fr ↔ ∃ a : Fin Tag.E6.rank → Lˣ, t = rootDiagUnit Tag.E6 a ∧ mactC E6A (a ^ Nat.card F) = a := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  constructor
  · intro ht
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht.1
    exact ⟨a, rfl, (rootDiagUnit_mem_TE6_iff hFr a).1 ht⟩
  · rintro ⟨a, rfl, ha⟩
    exact (rootDiagUnit_mem_TE6_iff hFr a).2 ha

theorem TE6_pow_sq (hFr : ∀ c, Fr c = c ^ Nat.card F) {t : ModGL Tag.E6 L} (ht : t ∈ TE6 Fr) :
    t ^ (Nat.card F ^ 2 - 1) = 1 := by
  obtain ⟨a, rfl, ha⟩ := (mem_TE6_iff hFr t).1 ht
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have h1 : a ^ Nat.card F = mactC E6A a := by
    have := congrArg (mactC E6A) ha
    rwa [← mactC_mul, E6A_sq, mactC_one] at this
  have h2 : a ^ (Nat.card F ^ 2) = a := by
    calc a ^ (Nat.card F ^ 2) = (a ^ Nat.card F) ^ Nat.card F := by rw [← pow_mul, sq]
      _ = (mactC E6A a) ^ Nat.card F := by rw [← h1]
      _ = mactC E6A (a ^ Nat.card F) := (ract_pow E6A a _).symm
      _ = a := ha
  have h3 : a ^ (Nat.card F ^ 2 - 1) = 1 := by
    have h4 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ (by omega)
    have : a ^ (Nat.card F ^ 2 - 1) * a = 1 * a := by
      rw [← pow_succ, Nat.sub_add_cancel h4, h2, one_mul]
    exact mul_right_cancel this
  have := map_pow (rootDiagUnitHom Tag.E6 L) a (Nat.card F ^ 2 - 1)
  rw [h3, map_one] at this
  exact this.symm

end Torus

section Iota

@[expose] def μ3 (F L : Type) [Field L] : Subgroup Lˣ :=
  rootsOfUnity (3 ^ padicValNat 3 (Nat.card F + 1)) L

theorem mem_μ3 {F L : Type} [Field L] {ζ : Lˣ} :
    ζ ∈ μ3 F L ↔ ζ ^ (3 ^ padicValNat 3 (Nat.card F + 1)) = 1 := mem_rootsOfUnity _ _

theorem three_pow_dvd_card_succ (F : Type) :
    3 ^ padicValNat 3 (Nat.card F + 1) ∣ Nat.card F + 1 := pow_padicValNat_dvd

instance isCyclic_μ3 {F L : Type} [Field L] : IsCyclic (μ3 F L) :=
  inferInstanceAs (IsCyclic (rootsOfUnity _ L))

theorem natCard_μ3 {F L : Type} [Field F] [Finite F] [Field L] [Algebra F L] [IsAlgClosure F L]
    (h3 : 3 ∣ Nat.card F + 1) :
    Nat.card (μ3 F L) = 3 ^ padicValNat 3 (Nat.card F + 1) := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  have hne : NeZero (((3 ^ padicValNat 3 (Nat.card F + 1) : ℕ)) : L) := by
    obtain ⟨ℓ, hℓ, hcharL, hℓq⟩ := exists_char_dvd_card F L
    refine ⟨fun h => ?_⟩
    have h1 : ℓ ∣ 3 ^ padicValNat 3 (Nat.card F + 1) := (CharP.cast_eq_zero_iff L ℓ _).1 h
    have h2 : ℓ ∣ 3 := hℓ.dvd_of_dvd_pow h1
    have h5 : ℓ = 3 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h2
    have h4 : 3 ∣ 1 := (Nat.dvd_add_right (h5 ▸ hℓq)).1 h3
    omega
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (3 ^ padicValNat 3 (Nat.card F + 1))
  exact hζ.card_rootsOfUnity

@[expose] def ι3 (F L : Type) [Field L] : (Fin 4 → μ3 F L) →* ModGL Tag.E6 L where
  toFun b := rootDiagUnit Tag.E6 (ract E6B fun k => (b k : Lˣ))
  map_one' := by
    show rootDiagUnit Tag.E6 (ract E6B fun _ => ((1 : μ3 F L) : Lˣ)) = 1
    rw [show (fun _ => ((1 : μ3 F L) : Lˣ)) = (1 : Fin 4 → Lˣ) from rfl, ract_one_vec,
      rootDiagUnit_one]
  map_mul' b b' := by
    show rootDiagUnit Tag.E6 (ract E6B fun k => ((b k * b' k : μ3 F L) : Lˣ)) =
      rootDiagUnit Tag.E6 (ract E6B fun k => (b k : Lˣ)) *
        rootDiagUnit Tag.E6 (ract E6B fun k => (b' k : Lˣ))
    rw [show (fun k => ((b k * b' k : μ3 F L) : Lˣ)) =
      (fun k => (b k : Lˣ)) * (fun k => (b' k : Lˣ)) from rfl, ract_mul_apply, rootDiagUnit_mul]

theorem ι3_apply {F L : Type} [Field L] (b : Fin 4 → μ3 F L) :
    ι3 F L b = rootDiagUnit Tag.E6 (ract E6B fun k => (b k : Lˣ)) := rfl

variable {F L : Type} [Field F] [Finite F] [Field L] [Algebra F L] [IsAlgClosure F L]
  {Fr : L →+* L}

theorem ι3_mem_T (hFr : ∀ c, Fr c = c ^ Nat.card F) (b : Fin 4 → μ3 F L) :
    ι3 F L b ∈ TE6 Fr := by
  rw [ι3_apply, rootDiagUnit_mem_TE6_iff hFr]
  set u : Fin 4 → Lˣ := fun k => (b k : Lˣ) with hu0
  have hu : u ^ Nat.card F = u⁻¹ := by
    funext k
    have h1 : (u k) ^ (Nat.card F + 1) = 1 := by
      obtain ⟨c, hc⟩ := three_pow_dvd_card_succ F
      rw [hc, pow_mul, mem_μ3.1 (b k).2, one_pow]
    simp only [Pi.pow_apply, Pi.inv_apply]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h1)
  rw [mactC_eq_ract, ← ract_pow, hu, ract_inv, ract_inv, ← ract_mul, E6A_mul_B, ract_neg, inv_inv]

theorem ι3_injective : Function.Injective (ι3 F L) := by
  intro b b' h
  have h1 := rootDiagUnit_injective
    (show rootDiagUnit Tag.E6 (ract E6B fun k => (b k : Lˣ)) =
      rootDiagUnit Tag.E6 (ract E6B fun k => (b' k : Lˣ)) from h)
  have h2 : (fun k => (b k : Lˣ)) = fun k => (b' k : Lˣ) := by
    have := congrArg (ract E6Bp) h1
    rwa [← ract_mul, ← ract_mul, E6Bp_mul_B, ract_one, ract_one] at this
  funext k
  exact Subtype.ext (congrFun h2 k)

theorem ι3_pow (b : Fin 4 → μ3 F L) :
    ι3 F L b ^ (3 ^ padicValNat 3 (Nat.card F + 1)) = 1 := by
  rw [ι3_apply]
  have h : (ract E6B fun k => (b k : Lˣ)) ^ (3 ^ padicValNat 3 (Nat.card F + 1)) = 1 := by
    rw [← ract_pow, show ((fun k => (b k : Lˣ)) ^ (3 ^ padicValNat 3 (Nat.card F + 1))) = 1 from
      funext fun k => mem_μ3.1 (b k).2, ract_one_vec]
  have := map_pow (rootDiagUnitHom Tag.E6 L) (ract E6B fun k => (b k : Lˣ))
    (3 ^ padicValNat 3 (Nat.card F + 1))
  rw [h, map_one] at this
  exact this.symm

theorem T3_le_range (hFr : ∀ c, Fr c = c ^ Nat.card F) (h3 : 3 ∣ Nat.card F + 1)
    {t : ModGL Tag.E6 L} (ht : t ∈ TE6 Fr) (ht3 : t ^ (3 ^ padicValNat 3 (Nat.card F + 1)) = 1) :
    t ∈ (ι3 F L).range := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  obtain ⟨a, rfl, ha⟩ := (mem_TE6_iff hFr t).1 ht
  have ha3 : a ^ (3 ^ padicValNat 3 (Nat.card F + 1)) = 1 := by
    have h1 : rootDiagUnit Tag.E6 (a ^ (3 ^ padicValNat 3 (Nat.card F + 1))) =
        rootDiagUnit Tag.E6 (1 : Fin Tag.E6.rank → Lˣ) := by
      rw [rootDiagUnit_one]
      exact (map_pow (rootDiagUnitHom Tag.E6 L) a (3 ^ padicValNat 3 (Nat.card F + 1))).trans ht3
    exact rootDiagUnit_injective h1
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := μ3 F L)
  have hord : orderOf (g : Lˣ) = 3 ^ padicValNat 3 (Nat.card F + 1) := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, natCard_μ3 h3]
  have he : ∀ i, ∃ m : ℤ, (g : Lˣ) ^ m = a i := fun i => by
    have hai : a i ∈ μ3 F L := mem_μ3.2 (by simpa using congrFun ha3 i)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨a i, hai⟩)
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  choose e he using he
  have hae : a = vecTC e (g : Lˣ) := funext fun i => (he i).symm
  have haq : a ^ Nat.card F = a⁻¹ := by
    funext i
    have h1 : a i ^ (Nat.card F + 1) = 1 := by
      obtain ⟨c, hc⟩ := three_pow_dvd_card_succ F
      have h2 : a i ^ (3 ^ padicValNat 3 (Nat.card F + 1)) = 1 := by simpa using congrFun ha3 i
      rw [hc, pow_mul, h2, one_pow]
    simp only [Pi.pow_apply, Pi.inv_apply]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h1)
  have hfix : (vecTC (E6A *ᵥ e) (g : Lˣ))⁻¹ = vecTC e (g : Lˣ) := by
    have := ha
    rw [haq, mactC_eq_ract, ract_inv, hae, ract_vecTC] at this
    exact this
  have hdiv : ∀ i, ((3 ^ padicValNat 3 (Nat.card F + 1) : ℕ) : ℤ) ∣ e i + (E6A *ᵥ e) i := by
    intro i
    have h1 := congrFun hfix i
    simp only [vecTC, Pi.inv_apply] at h1
    have h2 : (g : Lˣ) ^ (e i + (E6A *ᵥ e) i) = 1 := by
      rw [zpow_add, ← h1, inv_mul_cancel]
    have h3' := orderOf_dvd_iff_zpow_eq_one.2 h2
    rwa [hord] at h3'
  obtain ⟨k, hk⟩ : Odd (3 ^ padicValNat 3 (Nat.card F + 1) : ℕ) := Odd.pow (by decide)
  have hNk : ((3 ^ padicValNat 3 (Nat.card F + 1) : ℕ) : ℤ) = 2 * (k : ℤ) + 1 := by
    exact_mod_cast hk
  set x : Fin Tag.E6.rank → ℤ := (1 - E6A) *ᵥ e with hx
  have hxi : ∀ i, x i = e i - (E6A *ᵥ e) i := fun i => by simp [hx, Matrix.sub_mulVec]
  have hx0 : (E6A + 1) *ᵥ x = 0 := by
    rw [hx, Matrix.mulVec_mulVec, E6A_add_one_mul_one_sub, Matrix.zero_mulVec]
  have hxB := E6_kernel_eq x hx0
  set b₀ : Fin 4 → ℤ := ((k : ℤ) + 1) • (E6Bp *ᵥ x) with hb₀
  have hBb : E6B *ᵥ b₀ = ((k : ℤ) + 1) • x := by
    rw [hb₀, Matrix.mulVec_smul, ← hxB]
  refine ⟨fun j => g ^ b₀ j, ?_⟩
  rw [ι3_apply]
  have hcoe : (fun j => ((g ^ b₀ j : μ3 F L) : Lˣ)) = vecTC b₀ (g : Lˣ) := by
    funext j
    simp [vecTC]
  rw [hcoe, ract_vecTC]
  congr 1
  rw [hae]
  refine vecTC_eq_of_dvd_gen _ _ (g : Lˣ) _ hord fun i => ?_
  obtain ⟨m, hm⟩ := hdiv i
  have hBi := congrFun hBb i
  simp only [Pi.smul_apply, smul_eq_mul] at hBi
  have hAe : (E6A *ᵥ e) i = ((3 ^ padicValNat 3 (Nat.card F + 1) : ℕ) : ℤ) * m - e i := by
    linarith
  refine ⟨e i - ((k : ℤ) + 1) * m, ?_⟩
  rw [hBi, hxi, hAe]
  linear_combination (-(e i)) * hNk

end Iota

section Prime

variable
  {F L : Type} [Field F] [Finite F] [Field L] [IsAlgClosed L] {Fr : L →+* L}

@[expose] def TpowE6 (Fr : L →+* L) (k : ℕ) : Subgroup (ModGL Tag.E6 L) where
  carrier := {t | t ∈ TE6 Fr ∧ t ^ k = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
    refine ⟨mul_mem ha hb, ?_⟩
    rw [(show Commute a b from torusGroup_mul_comm ha.1 hb.1).mul_pow, ha1, hb1, one_mul]
  one_mem' := ⟨one_mem _, one_pow _⟩
  inv_mem' := by
    rintro a ⟨ha, ha1⟩
    exact ⟨inv_mem ha, by rw [inv_pow, ha1, inv_one]⟩

theorem TpowE6_le (k : ℕ) : TpowE6 Fr k ≤ TE6 Fr := fun _ h => h.1

@[expose] def E6M (F : Type) : ℕ :=
  (Nat.card F ^ 2 - 1) / 3 ^ padicValNat 3 (Nat.card F + 1)

@[expose] def T'E6 (F : Type) (Fr : L →+* L) : Subgroup (ModGL Tag.E6 L) :=
  TpowE6 Fr (E6M F)

@[expose] def T3E6 (F : Type) (Fr : L →+* L) : Subgroup (ModGL Tag.E6 L) :=
  TpowE6 Fr (3 ^ padicValNat 3 (Nat.card F + 1))

theorem T'E6_le : T'E6 F Fr ≤ TE6 Fr := TpowE6_le _

theorem T'E6_comm : ∀ t ∈ T'E6 F Fr, ∀ u ∈ T'E6 F Fr, t * u = u * t :=
  fun _ ht _ hu => torusGroup_mul_comm ht.1.1 hu.1.1

theorem sq_sub_one_eq' {q : ℕ} (hq : 1 < q) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h1, hq.le]
  ring

theorem padicValNat_sq_sub_one' {q : ℕ} (hq : 1 < q) (h3 : 3 ∣ q + 1) :
    padicValNat 3 (q ^ 2 - 1) = padicValNat 3 (q + 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [sq_sub_one_eq' hq, padicValNat.mul (by omega) (by omega),
    padicValNat.eq_zero_of_not_dvd (p := 3) (n := q - 1) (by omega), zero_add]

theorem E6M_mul (F : Type) [Field F] [Finite F] :
    E6M F * 3 ^ padicValNat 3 (Nat.card F + 1) = Nat.card F ^ 2 - 1 := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  refine Nat.div_mul_cancel ?_
  rw [sq_sub_one_eq' hq]
  exact Dvd.dvd.mul_left pow_padicValNat_dvd _

theorem not_three_dvd_E6M (F : Type) [Field F] [Finite F] (h3 : 3 ∣ Nat.card F + 1) : ¬ 3 ∣ E6M F := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hM := E6M_mul F
  have hpos : 0 < Nat.card F ^ 2 - 1 := by
    have : 1 < Nat.card F ^ 2 := Nat.one_lt_pow (by norm_num) hq
    omega
  have hM0 : E6M F ≠ 0 := by
    intro h
    rw [h, zero_mul] at hM
    omega
  have h1 := congrArg (padicValNat 3) hM
  rw [padicValNat.mul hM0 (pow_ne_zero _ (by norm_num)), padicValNat.prime_pow,
    padicValNat_sq_sub_one' hq h3] at h1
  intro hd
  have := one_le_padicValNat_of_dvd hM0 hd
  omega

theorem coprime_three_pow_E6M (F : Type) [Field F] [Finite F] (h3 : 3 ∣ Nat.card F + 1) :
    Nat.Coprime (3 ^ padicValNat 3 (Nat.card F + 1)) (E6M F) :=
  Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
    (not_three_dvd_E6M F h3))

theorem T3E6_inf_T'E6 (h3 : 3 ∣ Nat.card F + 1) : T3E6 F Fr ⊓ T'E6 F Fr = ⊥ := by
  rw [eq_bot_iff]
  rintro t ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [(coprime_three_pow_E6M F h3).gcd_eq_one] at h
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h)

end Prime

theorem ι3_range_le_T3 {F L : Type} [Field F] [Finite F] [Field L] [Algebra F L] [IsAlgClosure F L]
    [IsAlgClosed L] {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ Nat.card F) : (ι3 F L).range ≤ T3E6 F Fr := by
  rintro _ ⟨b, rfl⟩
  exact ⟨ι3_mem_T hFr b, ι3_pow b⟩

theorem T'E6_inter_range {F L : Type} [Field F] [Finite F] [Field L] [Algebra F L]
    [IsAlgClosure F L] [IsAlgClosed L] {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ Nat.card F) (h3 : 3 ∣ Nat.card F + 1)
    {t : ModGL Tag.E6 L} (ht : t ∈ T'E6 F Fr) (hr : t ∈ (ι3 F L).range) : t = 1 := by
  have : t ∈ T3E6 F Fr ⊓ T'E6 F Fr := ⟨ι3_range_le_T3 hFr hr, ht⟩
  rwa [T3E6_inf_T'E6 h3, Subgroup.mem_bot] at this

section Final

variable {F L : Type} [Field F] [Finite F] [Field L] [Algebra F L] [IsAlgClosure F L]
  [IsAlgClosed L] {Fr : L →+* L}

theorem T'E6_decomp (hFr : ∀ c, Fr c = c ^ Nat.card F) (h3 : 3 ∣ Nat.card F + 1)
    {t : ModGL Tag.E6 L} (ht : t ∈ TE6 Fr) :
    ∃ t₃ t' : ModGL Tag.E6 L, t₃ ∈ TE6 Fr ∧ t₃ ^ (3 ^ padicValNat 3 (Nat.card F + 1)) = 1 ∧
      t' ∈ T'E6 F Fr ∧ t = t₃ * t' := by
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 (coprime_three_pow_E6M F h3)
  have hMul : ((E6M F : ℕ) : ℤ) * ((3 ^ padicValNat 3 (Nat.card F + 1) : ℕ) : ℤ) =
      ((Nat.card F ^ 2 - 1 : ℕ) : ℤ) := by exact_mod_cast E6M_mul F
  have hone : ∀ c : ℤ, t ^ (c * ((Nat.card F ^ 2 - 1 : ℕ) : ℤ)) = 1 := fun c => by
    rw [zpow_mul', zpow_natCast, TE6_pow_sq hFr ht, one_zpow]
  have hsplit : t = t ^ (y * ((E6M F : ℕ) : ℤ)) *
      t ^ (x * ((3 ^ padicValNat 3 (Nat.card F + 1) : ℕ) : ℤ)) := by
    rw [← zpow_add, show y * ((E6M F : ℕ) : ℤ) + x * ((3 ^ padicValNat 3 (Nat.card F + 1) : ℕ) : ℤ)
      = 1 by linarith, zpow_one]
  refine ⟨t ^ (y * ((E6M F : ℕ) : ℤ)), t ^ (x * ((3 ^ padicValNat 3 (Nat.card F + 1) : ℕ) : ℤ)),
    zpow_mem ht _, ?_, ⟨zpow_mem ht _, ?_⟩, hsplit⟩
  · rw [← zpow_natCast (t ^ (y * ((E6M F : ℕ) : ℤ))) (3 ^ padicValNat 3 (Nat.card F + 1)),
      ← zpow_mul, mul_assoc, hMul]
    exact hone y
  · rw [← zpow_natCast (t ^ (x * ((3 ^ padicValNat 3 (Nat.card F + 1) : ℕ) : ℤ))) (E6M F),
      ← zpow_mul, mul_assoc, mul_comm _ ((E6M F : ℕ) : ℤ), hMul]
    exact hone x

theorem finite_TE6 (hFr : ∀ c, Fr c = c ^ Nat.card F) : Finite (TE6 Fr) :=
  finite_twistedTorusOf_gen Fr _ (wordProd_smul_eq_wordMat_mulVec Tag.E6 e6TwoWord) hFr (e := 2)
    two_ne_zero e6Two_pow

theorem coprime_card_T'E6 (hFr : ∀ c, Fr c = c ^ Nat.card F) (h3 : 3 ∣ Nat.card F + 1) :
    Nat.Coprime 3 (Nat.card (T'E6 F Fr)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := finite_TE6 hFr
  have hfin : Finite (T'E6 F Fr) := Finite.of_injective _ (Subgroup.inclusion_injective T'E6_le)
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
  have hxM : x ^ E6M F = 1 := Subtype.ext x.2.2
  have h1 := orderOf_dvd_of_pow_eq_one hxM
  rw [hx] at h1
  exact not_three_dvd_E6M F h3 h1

@[expose] def T'NFix (F : Type) (Fr : L →+* L) :
    Subgroup (NFix (canonicalRep (coxeterSystem Tag.E6) L wE6W) Fr) :=
  (T'E6 F Fr).subgroupOf (NFix (canonicalRep (coxeterSystem Tag.E6) L wE6W) Fr)

theorem T'E6_le_NFix : T'E6 F Fr ≤ NFix (canonicalRep (coxeterSystem Tag.E6) L wE6W) Fr :=
  T'E6_le.trans (twistedTorusOf_le_NFix _ _)

theorem mem_T'NFix {x : NFix (canonicalRep (coxeterSystem Tag.E6) L wE6W) Fr} :
    x ∈ T'NFix F Fr ↔ (x : ModGL Tag.E6 L) ∈ T'E6 F Fr := Iff.rfl

instance T'NFix_normal : (T'NFix F Fr).Normal :=
  ⟨fun x hx y => by
    have hx' : (x : ModGL Tag.E6 L) ∈ T'E6 F Fr := hx
    show ((y : ModGL Tag.E6 L) * (x : ModGL Tag.E6 L) * (y : ModGL Tag.E6 L)⁻¹) ∈ T'E6 F Fr
    refine ⟨NFix_conj_mem_twistedTorusOf y.2 hx'.1, ?_⟩
    rw [conj_pow, hx'.2, mul_one, mul_inv_cancel]⟩

theorem T'NFix_comm : ∀ x ∈ T'NFix F Fr, ∀ y ∈ T'NFix F Fr, x * y = y * x :=
  fun _ hx _ hy => Subtype.ext (T'E6_comm _ hx _ hy)

instance T'NFix_isMulCommutative : IsMulCommutative (T'NFix F Fr) :=
  ⟨⟨fun a b => Subtype.ext (T'NFix_comm a.1 a.2 b.1 b.2)⟩⟩

theorem natCard_T'NFix :
    Nat.card (T'NFix F Fr) = Nat.card (T'E6 F Fr) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe T'E6_le_NFix).toEquiv

theorem coprime_card_T'NFix (hFr : ∀ c, Fr c = c ^ Nat.card F) (h3 : 3 ∣ Nat.card F + 1) :
    Nat.Coprime 3 (Nat.card (T'NFix F Fr)) := by
  rw [natCard_T'NFix]
  exact coprime_card_T'E6 hFr h3

end Final

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

end
