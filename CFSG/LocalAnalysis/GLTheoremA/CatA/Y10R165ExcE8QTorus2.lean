module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8QTorus
public import CFSG.RankThree.PartOne.KE6.E6LStd

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open CFSG CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KD4T

open scoped Pointwise

variable {L : Type} [Field L]

theorem torusRootChar_pow
    {τ : Tag} {g : ModGL τ L} (hg : g ∈ diagonalGroup) (α : Fin τ.rank → ℤ) (n : ℕ) :
    torusRootChar (g ^ n) α = (torusRootChar g α) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, torusRootChar_one]
  | succ n ih =>
    rw [pow_succ, torusRootChar_mul (Subgroup.pow_mem _ hg n) hg, ih, pow_succ]

theorem torusElt_pow
    {τ : Tag} {R : Type} [CommRing R] (i : Fin τ.rank) (t : Rˣ) (n : ℕ) :
    torusElt τ R i (t ^ n) = torusElt τ R i t ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, torusElt_one]
  | succ n ih => rw [pow_succ, pow_succ, torusElt_mul, ih]

theorem units_map_entrywiseHom_torusElt
    {τ : Tag} (σ : L →+* L) (i : Fin τ.rank) (t : Lˣ) :
    Units.map (entrywiseHom σ) (torusElt τ L i t) =
      torusElt τ L i (Units.map σ.toMonoidHom t) := by
  have h2 : (fun j => Units.map σ.toMonoidHom (t ^ (Tag.cartan τ i j))) =
      (fun j => Units.map σ.toMonoidHom t ^ (Tag.cartan τ i j)) := by
    funext j
    rw [map_zpow]
  calc Units.map (entrywiseHom σ) (torusElt τ L i t)
      = Units.map (entrywiseHom σ) (rootDiagUnit τ (fun j => t ^ (Tag.cartan τ i j))) := by
        rw [torusElt_eq_rootDiagUnit]
    _ = rootDiagUnit τ (fun j => Units.map σ.toMonoidHom (t ^ (Tag.cartan τ i j))) :=
        Units.ext (entrywise_rootDiag σ _)
    _ = rootDiagUnit τ (fun j => Units.map σ.toMonoidHom t ^ (Tag.cartan τ i j)) := by rw [h2]
    _ = torusElt τ L i (Units.map σ.toMonoidHom t) := by rw [torusElt_eq_rootDiagUnit]

theorem torusRootChar_torusElt_single
    {τ : Tag} (i k : Fin τ.rank) (t : Lˣ) :
    torusRootChar (torusElt τ L i t) (Pi.single k 1) = ((t ^ Tag.cartan τ i k : Lˣ) : L) := by
  rw [torusRootChar_torusElt _ _ (isRoot_single _ _),
    show (∑ j, Tag.cartan τ i j * (Pi.single k 1 : Fin τ.rank → ℤ) j) = Tag.cartan τ i k from by
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · intro hk; exact absurd (Finset.mem_univ k) hk]

lemma torusRootChar_torusElt_self
    (i : Fin Tag.E8.rank) (t : Lˣ) :
    torusRootChar (torusElt Tag.E8 L i t) (Pi.single i 1) = (t : L) ^ 2 := by
  rw [torusRootChar_torusElt_single, Tag.cartan_self, zpow_ofNat,
    Units.val_pow_eq_pow_val]

lemma torusRootChar_torusElt_eq_one
    {i k : Fin Tag.E8.rank} (t : Lˣ)
    (h : Tag.cartan Tag.E8 i k = 0) :
    torusRootChar (torusElt Tag.E8 L i t) (Pi.single k 1) = 1 := by
  rw [torusRootChar_torusElt_single, h, zpow_zero, Units.val_one]

section StdLayer


variable {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)

theorem torusRootChar_mul_pow_three {τ : Tag}
    {a b c : ModGL τ L} (ha : a ∈ diagonalGroup)
    (hb : b ∈ diagonalGroup) (hc : c ∈ diagonalGroup) (m n k : ℕ)
    (α : Fin τ.rank → ℤ) :
    torusRootChar (a ^ m * b ^ n * c ^ k) α =
      (torusRootChar a α) ^ m * ((torusRootChar b α) ^ n * (torusRootChar c α) ^ k) := by
  have hm := Subgroup.pow_mem _ ha m
  have hn := Subgroup.pow_mem _ hb n
  have hk := Subgroup.pow_mem _ hc k
  rw [show a ^ m * b ^ n * c ^ k = a ^ m * (b ^ n * c ^ k) from by group]
  rw [torusRootChar_mul hm (mul_mem hn hk), torusRootChar_mul hn hk, torusRootChar_pow ha α m,
    torusRootChar_pow hb α n, torusRootChar_pow hc α k]

theorem conj_torusElt_of_hgen {τ : Tag} [E6Sub τ]
    {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    (hgen : ∀ j ∈ e6Set τ, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
      n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c)
    {j : Fin τ.rank} (hj : j ∈ e6Set τ) (t : Lˣ) :
    n₁ * torusElt τ L j t * n₁⁻¹ = torusElt τ L (π j) t := by
  have hw : ∀ s : Lˣ, n₁ * weylElt τ L j s * n₁⁻¹ = weylElt τ L (π j) s := by
    intro s
    rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul,
      CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
    rw [show n₁ * (xUnit τ L j (s : L) * yUnit τ L j (-(((s⁻¹ : Lˣ) : L))) *
          xUnit τ L j (s : L)) * n₁⁻¹ =
        (n₁ * xUnit τ L j (s : L) * n₁⁻¹) * (n₁ * yUnit τ L j (-(((s⁻¹ : Lˣ) : L))) *
          n₁⁻¹) * (n₁ * xUnit τ L j (s : L) * n₁⁻¹) from by group]
    rw [(hgen j hj (s : L)).1, (hgen j hj (-(((s⁻¹ : Lˣ) : L)))).2]
  rw [torusElt, torusElt]
  rw [show n₁ * (weylElt τ L j t * weylElt τ L j (-1)) * n₁⁻¹ =
      (n₁ * weylElt τ L j t * n₁⁻¹) * (n₁ * weylElt τ L j (-1) * n₁⁻¹) from by group]
  rw [hw, hw]



private lemma torusElt_mem_stdLayer_of_fixed {n₁ : ModGL Tag.E8 L} {ω : Lˣ}
    (hstd : StdTwist6 n₁ (1 : Equiv.Perm (Fin Tag.E8.rank)))
    (hωfix : Units.map (iterateFrobenius L ℓ f).toMonoidHom ω = ω)
    {i : Fin Tag.E8.rank} (hi : i ∈ e6Set Tag.E8) :
    torusElt Tag.E8 L i ω ∈ stdLayer Tag.E8 ℓ f n₁ := by
  have hQ : torusElt Tag.E8 L i ω ∈ subsystemGroup Tag.E8 L (e6Set Tag.E8) :=
    subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hi ω)
  refine mem_stdLayer.2 ⟨hQ, ?_⟩
  rw [units_map_entrywiseHom_torusElt, hωfix]
  exact StdTwist6.commute_of_one hstd rfl hQ

lemma orderOf_torusElt_of_pow {ω : Lˣ} {q : ℕ} (hωq : ω ^ q = 1)
    (hωdvd : ∀ k : ℕ, ω ^ k = 1 → q ∣ k) (hq : q.Prime) (hq2 : q ≠ 2)
    {i : Fin Tag.E8.rank} :
    orderOf (torusElt Tag.E8 L i ω) = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hpow : torusElt Tag.E8 L i ω ^ q = 1 := by
    rw [← torusElt_pow, hωq, torusElt_one]
  have hne : torusElt Tag.E8 L i ω ≠ 1 := by
    intro h1
    have h2 := congrArg (fun g => torusRootChar g (Pi.single i 1)) h1
    rw [torusRootChar_one, torusRootChar_torusElt_self] at h2
    have h3 : ω ^ 2 = 1 := by
      ext
      rwa [Units.val_pow_eq_pow_val, Units.val_one]
    have h4 : q ∣ 2 := hωdvd 2 h3
    rcases (Nat.dvd_prime Nat.prime_two).1 h4 with h | h
    · exact hq.ne_one h
    · exact hq2 h
  exact orderOf_eq_prime hpow hne

private lemma dvd_of_two_mul_pow_eq_one {ω : Lˣ} {q : ℕ} (hq : q.Prime)
    (hωdvd : ∀ k : ℕ, ω ^ k = 1 → q ∣ k) (htwo : (2 : ZMod q) ≠ 0) {m : ℕ}
    (hm : (ω : L) ^ (2 * m) = 1) : q ∣ m := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hm1 : ω ^ (2 * m) = 1 := by
    ext
    rwa [Units.val_pow_eq_pow_val, Units.val_one]
  have hm2 : q ∣ 2 * m := hωdvd (2 * m) hm1
  have hmz : (m : ZMod q) = 0 := by
    have e : (2 : ZMod q) * (m : ZMod q) = 0 := by
      have h' : ((2 * m : ℕ) : ZMod q) = 0 := by
        have h2' : ((2 * (m : ℤ) : ℤ) : ZMod q) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * (m : ℤ)) q).2 (by exact_mod_cast hm2)
        simpa using h2'
      simpa using h'
    exact mul_left_cancel₀ htwo (e.trans (mul_zero 2).symm)
  have hm' : ((m : ℤ) : ZMod q) = 0 := by push_cast; exact hmz
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (m : ℤ) q).1 hm'

private lemma independent_powers_torusElt_zero_one_four {ω : Lˣ} {q : ℕ} (hq : q.Prime)
    (hωdvd : ∀ k : ℕ, ω ^ k = 1 → q ∣ k) (htwo : (2 : ZMod q) ≠ 0) :
    ∀ m n k : ℕ, torusElt Tag.E8 L 0 ω ^ m * torusElt Tag.E8 L 1 ω ^ n *
        torusElt Tag.E8 L 4 ω ^ k = 1 → q ∣ m ∧ q ∣ n ∧ q ∣ k := by
  intro m n k h1
  have hdiag : ∀ i : Fin Tag.E8.rank, torusElt Tag.E8 L i ω ∈ diagonalGroup := fun i =>
    torusGroup_le_diagonalGroup (torusElt_mem_torusGroup i ω)
  have hchar : ∀ r : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 r →
      torusRootChar (torusElt Tag.E8 L 0 ω ^ m * torusElt Tag.E8 L 1 ω ^ n *
        torusElt Tag.E8 L 4 ω ^ k) r = 1 := by
    intro r hr
    rw [h1, torusRootChar_one]
  have h0 : (ω : L) ^ (2 * m) = 1 := by
    have h := hchar (Pi.single 0 1) (isRoot_single _ _)
    rw [torusRootChar_mul_pow_three (hdiag 0) (hdiag 1) (hdiag 4) m n k,
      torusRootChar_torusElt_self, torusRootChar_torusElt_eq_one ω (by decide),
      torusRootChar_torusElt_eq_one ω (by decide)] at h
    simpa [pow_mul] using h
  have h1' : (ω : L) ^ (2 * n) = 1 := by
    have h := hchar (Pi.single 1 1) (isRoot_single _ _)
    rw [torusRootChar_mul_pow_three (hdiag 0) (hdiag 1) (hdiag 4) m n k,
      torusRootChar_torusElt_eq_one ω (by decide), torusRootChar_torusElt_self,
      torusRootChar_torusElt_eq_one ω (by decide)] at h
    simpa [pow_mul] using h
  have h4 : (ω : L) ^ (2 * k) = 1 := by
    have h := hchar (Pi.single 4 1) (isRoot_single _ _)
    rw [torusRootChar_mul_pow_three (hdiag 0) (hdiag 1) (hdiag 4) m n k,
      torusRootChar_torusElt_eq_one ω (by decide),
      torusRootChar_torusElt_eq_one ω (by decide), torusRootChar_torusElt_self] at h
    simpa [pow_mul] using h
  exact ⟨dvd_of_two_mul_pow_eq_one hq hωdvd htwo h0,
    dvd_of_two_mul_pow_eq_one hq hωdvd htwo h1',
    dvd_of_two_mul_pow_eq_one hq hωdvd htwo h4⟩

theorem exists_three_qTorus_stdLayer_one {K : Type} [Field K] [Algebra K L] {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ q)
    (hFr : ∀ x : K, (algebraMap K L x) ^ (ℓ ^ f) = algebraMap K L x)
    {n₁ : ModGL Tag.E8 L} (hstd : StdTwist6 n₁ (1 : Equiv.Perm (Fin Tag.E8.rank))) :
    ∃ T : Subgroup (ModGL Tag.E8 L), T ≤ stdLayer Tag.E8 ℓ f n₁ ∧
      IsElemAbelian q T ∧ Nat.card T = q ^ 3 := by
  classical
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (1 < q) := ⟨hq.one_lt⟩
  set ζu : Kˣ := Units.mk0 ζ (hζ.ne_zero hq.ne_zero) with hζudef
  have hζu : IsPrimitiveRoot ζu q := (IsPrimitiveRoot.coe_units_iff).mp hζ
  set ω : Lˣ := Units.map (algebraMap K L).toMonoidHom ζu with hωdef
  have hωval : (ω : L) = algebraMap K L (ζu : K) := by rw [hωdef, Units.coe_map]; rfl
  have hωL : IsPrimitiveRoot (ω : L) q := by
    have h : (ω : L) = algebraMap K L ζ := by rw [hωval]; rfl
    rw [h]
    exact IsPrimitiveRoot.map_of_injective hζ (algebraMap K L).injective
  have hωfix : Units.map (iterateFrobenius L ℓ f).toMonoidHom ω = ω := by
    apply Units.ext
    rw [Units.coe_map, hωval]
    change (iterateFrobenius L ℓ f) (algebraMap K L (ζu : K)) = algebraMap K L (ζu : K)
    rw [iterateFrobenius_def]
    exact hFr (ζu : K)
  have hωq : ω ^ q = 1 := by
    rw [hωdef, ← map_pow, hζu.pow_eq_one, map_one]
  have hωdvd : ∀ k : ℕ, ω ^ k = 1 → q ∣ k := by
    intro k hk
    have h : (ω : L) ^ k = 1 := by rw [← Units.val_pow_eq_pow_val, hk, Units.val_one]
    exact (hωL.pow_eq_one_iff_dvd k).1 h
  have hmem0 : (0 : Fin Tag.E8.rank) ∈ e6Set Tag.E8 := by
    change (0 : Fin Tag.E8.rank).val < Tag.E6.rank; decide
  have hmem1 : (1 : Fin Tag.E8.rank) ∈ e6Set Tag.E8 := by
    change (1 : Fin Tag.E8.rank).val < Tag.E6.rank; decide
  have hmem4 : (4 : Fin Tag.E8.rank) ∈ e6Set Tag.E8 := by
    change (4 : Fin Tag.E8.rank).val < Tag.E6.rank; decide
  have hmem : ∀ i : Fin Tag.E8.rank, i ∈ e6Set Tag.E8 →
      torusElt Tag.E8 L i ω ∈ stdLayer Tag.E8 ℓ f n₁ :=
    fun i hi => torusElt_mem_stdLayer_of_fixed hstd hωfix hi
  have hord : ∀ i : Fin Tag.E8.rank, i ∈ e6Set Tag.E8 →
      orderOf (torusElt Tag.E8 L i ω) = q :=
    fun i _ => orderOf_torusElt_of_pow hωq hωdvd hq hq2
  have hcomm : ∀ i j : Fin Tag.E8.rank,
      Commute (torusElt Tag.E8 L i ω) (torusElt Tag.E8 L j ω) := fun i j =>
    torusElt_mul_comm i j ω ω
  have htwo : (2 : ZMod q) ≠ 0 := by
    intro h
    have h2 : q ∣ 2 := by
      have h' : ((2 : ℤ) : ZMod q) = 0 := by push_cast; exact h
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd 2 q).1 h'
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact hq.ne_one h
    · exact hq2 h
  have hind := independent_powers_torusElt_zero_one_four (L := L) hq hωdvd htwo
  exact exists_elemAbelian_three_of_commute (hord 0 hmem0) (hord 1 hmem1) (hord 4 hmem4)
    (hcomm 0 1) (hcomm 0 4) (hcomm 1 4) hind (hmem 0 hmem0) (hmem 1 hmem1) (hmem 4 hmem4)

end StdLayer

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three
