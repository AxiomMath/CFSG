module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.ExtStructure
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.ElemModule
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.General

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628

section
theorem sevenLin_two_eq_zero {V : Type} [AddCommGroup V] [Module (ZMod 2) V] :
    (2 : Module.End (ZMod 2) V) = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  calc (2 : Module.End (ZMod 2) V)
      = algebraMap (ZMod 2) (Module.End (ZMod 2) V) 2 := (map_ofNat _ 2).symm
    _ = 0 := by rw [h, map_zero]

theorem sevenLin_mul_eq {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ζ : Module.End (ZMod 2) V) :
    (ζ ^ 3 + ζ + 1) * (ζ ^ 3 + ζ ^ 2 + 1) = ∑ i ∈ Finset.range 7, ζ ^ i := by
  have h2 := sevenLin_two_eq_zero (V := V)
  have h : (ζ ^ 3 + ζ + 1) * (ζ ^ 3 + ζ ^ 2 + 1) =
      ∑ i ∈ Finset.range 7, ζ ^ i + 2 * ζ ^ 3 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    noncomm_ring
  rw [h, h2]
  simp

theorem exists_invariant_subspace_seven {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] [Nontrivial V] (ζ : Module.End (ZMod 2) V) (h7 : ζ ^ 7 = 1)
    (hfix : ∀ v, ζ v = v → v = 0) :
    ∃ U : Submodule (ZMod 2) V, U ≠ ⊥ ∧ (∀ u ∈ U, ζ u ∈ U) ∧ Module.finrank (ZMod 2) U ≤ 3 := by
  classical
  have hS : ∀ v, (∑ i ∈ Finset.range 7, ζ ^ i) v = 0 := by
    intro v
    apply hfix
    have h := mul_geom_sum ζ 7
    rw [h7, sub_self] at h
    have h' := congrArg (fun f : Module.End (ZMod 2) V => f v) h
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.zero_apply] at h'
    exact sub_eq_zero.mp h'
  have hg : ∀ v, (ζ ^ 3 + ζ + 1 : Module.End (ZMod 2) V)
      ((ζ ^ 3 + ζ ^ 2 + 1 : Module.End (ZMod 2) V) v) = 0 := by
    intro v
    have h := hS v
    rw [← sevenLin_mul_eq ζ] at h
    simpa only [Module.End.mul_apply] using h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨u, hu0, hu⟩ : ∃ u : V, u ≠ 0 ∧
      ((ζ ^ 3 + ζ + 1 : Module.End (ZMod 2) V) u = 0 ∨
        (ζ ^ 3 + ζ ^ 2 + 1 : Module.End (ZMod 2) V) u = 0) := by
    by_cases h2 : (ζ ^ 3 + ζ ^ 2 + 1 : Module.End (ZMod 2) V) v = 0
    · exact ⟨v, hv, Or.inr h2⟩
    · exact ⟨_, h2, Or.inl (hg v)⟩
  have hrel : ζ (ζ (ζ u)) + ζ u + u = 0 ∨ ζ (ζ (ζ u)) + ζ (ζ u) + u = 0 := by
    rcases hu with h | h
    · left
      simpa [pow_succ] using h
    · right
      simpa [pow_succ] using h
  obtain ⟨U, hU⟩ : ∃ U : Submodule (ZMod 2) V,
      U = Submodule.span (ZMod 2) (↑({u, ζ u, ζ (ζ u)} : Finset V) : Set V) := ⟨_, rfl⟩
  have h1 : u ∈ U := hU ▸ Submodule.subset_span (by simp)
  have h2 : ζ u ∈ U := hU ▸ Submodule.subset_span (by simp)
  have h3 : ζ (ζ u) ∈ U := hU ▸ Submodule.subset_span (by simp)
  have h4 : ζ (ζ (ζ u)) ∈ U := by
    rcases hrel with h | h
    · have e : ζ (ζ (ζ u)) = -(ζ u + u) := by
        rw [eq_neg_iff_add_eq_zero, ← add_assoc]
        exact h
      rw [e]
      exact U.neg_mem (U.add_mem h2 h1)
    · have e : ζ (ζ (ζ u)) = -(ζ (ζ u) + u) := by
        rw [eq_neg_iff_add_eq_zero, ← add_assoc]
        exact h
      rw [e]
      exact U.neg_mem (U.add_mem h3 h1)
  have hmap : U.map ζ ≤ U := by
    rw [hU, Submodule.map_span, Submodule.span_le, ← hU]
    rintro _ ⟨x, hx, rfl⟩
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact h2
    · exact h3
    · exact h4
  refine ⟨U, ?_, fun w hw => hmap (Submodule.mem_map_of_mem hw), ?_⟩
  · intro hbot
    rw [hbot] at h1
    exact hu0 (by simpa using h1)
  · rw [hU]
    exact (finrank_span_finset_le_card _).trans Finset.card_le_three
end

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem sevenFalse_conj_zpowers {x t m : K} (hxt : x * t = t * x) (hm : m ∈ zpowers t) :
    x * m * x⁻¹ = m := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hm
  have h : Commute x t := hxt
  have := (h.zpow_right n).eq
  rw [mul_inv_eq_iff_eq_mul]
  exact this

theorem sevenFalse_mem_normalizer_zpowers {g t : K} (h : g * t = t * g) :
    g ∈ normalizer (zpowers t : Set K) := by
  rw [mem_normalizer_iff]
  intro m
  constructor
  · intro hm
    rw [sevenFalse_conj_zpowers h hm]
    exact hm
  · intro hm
    have h' : g⁻¹ * t = t * g⁻¹ := (Commute.inv_left (show Commute g t from h)).eq
    have h2 := sevenFalse_conj_zpowers h' hm
    have e : g⁻¹ * (g * m * g⁻¹) * g⁻¹⁻¹ = m := by group
    rw [e] at h2
    rw [h2]
    exact hm

theorem sevenFalse_isPGroup_seven {z : K} (hz : z ^ 7 = 1) : IsPGroup 7 (zpowers z) := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp g.2
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm,
    zpow_mul, zpow_natCast, hz, one_zpow]

theorem sevenFalse_module {R : Subgroup K} {t z : K} (hR : IsExt2 R t) (hz : z ^ 7 = 1)
    (hzR : z ∈ normalizer (R : Set K)) (hzt : z * t = t * z)
    (hfix : ∀ r ∈ R, z * r = r * z → r ∈ zpowers t) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Module.Finite (ZMod 2) W)
      (π : K → W) (ζ : Module.End (ZMod 2) W),
      (∀ x ∈ R, ∀ y ∈ R, π (x * y) = π x + π y) ∧ (∀ x ∈ R, π x = 0 ↔ x ∈ zpowers t) ∧
      (∀ w : W, ∃ x ∈ R, π x = w) ∧ (∀ x ∈ R, ζ (π x) = π (z * x * z⁻¹)) ∧ ζ ^ 7 = 1 ∧
      (∀ w, ζ w = w → w = 0) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzt_le : zpowers t ≤ R := zpowers_le.mpr hR.t_mem
  have hzpR : zpowers z ≤ normalizer (R : Set K) := zpowers_le.mpr hzR
  obtain ⟨W, iW, mW, fW, π, ρ, hadd, hzero, hsurj, hρ⟩ :=
    exists_elemSection (f := 2) (Y := R) (M := zpowers t) (G := zpowers z) hzt_le
      (fun x hx m hm => by rw [sevenFalse_conj_zpowers (hR.t_comm x hx) hm]; exact hm)
      (fun x hx y hy => by
        have := hR.comm_mem x hx y hy
        rwa [commutatorElement_def] at this)
      (fun x hx => hR.sq_mem x hx) hzpR (zpowers_le.mpr (sevenFalse_mem_normalizer_zpowers hzt))
  have hρz : ∀ x ∈ R, ρ ⟨z, mem_zpowers z⟩ (π x) = π (z * x * z⁻¹) :=
    fun x hx => hρ ⟨z, mem_zpowers z⟩ x hx
  refine ⟨W, iW, mW, fW, π, ρ ⟨z, mem_zpowers z⟩, hadd, hzero, hsurj, hρz, ?_, ?_⟩
  · rw [← map_pow]
    have : (⟨z, mem_zpowers z⟩ : ↥(zpowers z)) ^ 7 = 1 := Subtype.ext (by simpa using hz)
    rw [this, map_one]
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := hsurj w
    have hfixn : ∀ m : ℕ, (ρ ⟨z, mem_zpowers z⟩ ^ m) (π x) = π x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, Module.End.mul_apply, hw, ih]
    have hpow : ∀ g ∈ zpowers z, π (g * x * g⁻¹) = π x := by
      intro g hg
      obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hg)
      have hrep : ρ ⟨z ^ n, hg⟩ = (ρ ⟨z, mem_zpowers z⟩) ^ n := by
        rw [← map_pow]; rfl
      have h1 : ρ ⟨z ^ n, hg⟩ (π x) = π (z ^ n * x * (z ^ n)⁻¹) := hρ ⟨z ^ n, hg⟩ x hx
      rw [← h1, hrep, hfixn]
    have hxM : ∀ g ∈ zpowers z, x⁻¹ * (g * x * g⁻¹) ∈ zpowers t := by
      intro g hg
      have hgx : g * x * g⁻¹ ∈ R := (mem_normalizer_iff.mp (hzpR hg) x).mp hx
      refine (hzero _ (R.mul_mem (R.inv_mem hx) hgx)).mp ?_
      rw [hadd _ (R.inv_mem hx) _ hgx, hpow g hg, ← hadd _ (R.inv_mem hx) _ hx, inv_mul_cancel]
      exact (hzero 1 R.one_mem).mpr (one_mem _)
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hTM : zpowers z ≤ normalizer (zpowers t : Set K) :=
      zpowers_le.mpr (sevenFalse_mem_normalizer_zpowers hzt)
    have hq : ¬ 7 ∣ Nat.card (zpowers t) := by
      rw [Nat.card_zpowers, orderOf_eq_prime hR.t_sq hR.t_ne]
      norm_num
    obtain ⟨m, hm, hmfix⟩ := exists_fixed_in_coset (sevenFalse_isPGroup_seven hz) hTM hq hxM
    have hxm : x * m ∈ R := R.mul_mem hx (hzt_le hm)
    have hxmz : z * (x * m) = (x * m) * z := by
      have := hmfix z (mem_zpowers z)
      rwa [mul_inv_eq_iff_eq_mul] at this
    have hxmt := hfix _ hxm hxmz
    have hxt : x ∈ zpowers t := by
      have := (zpowers t).mul_mem hxmt ((zpowers t).inv_mem hm)
      simpa using this
    exact (hzero x hx).mpr hxt

theorem sevenFalse_exists_sub {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {R : Subgroup K}
    {π : K → W} (hπ : ∀ x ∈ R, ∀ y ∈ R, π (x * y) = π x + π y) (U : Submodule (ZMod 2) W) :
    ∃ A : Subgroup K, A ≤ R ∧ ∀ x, x ∈ A ↔ x ∈ R ∧ π x ∈ U := by
  have h1 : π 1 = 0 := by
    have := hπ 1 R.one_mem 1 R.one_mem
    simpa using this
  have hinv : ∀ x ∈ R, π x⁻¹ = - π x := by
    intro x hx
    have := hπ x⁻¹ (R.inv_mem hx) x hx
    rw [inv_mul_cancel, h1] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  refine ⟨{ carrier := {x | x ∈ R ∧ π x ∈ U}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, ?_, ?_⟩
  · rintro a b ⟨haR, haU⟩ ⟨hbR, hbU⟩
    refine ⟨R.mul_mem haR hbR, ?_⟩
    rw [hπ a haR b hbR]
    exact U.add_mem haU hbU
  · exact ⟨R.one_mem, by rw [h1]; exact U.zero_mem⟩
  · rintro a ⟨haR, haU⟩
    refine ⟨R.inv_mem haR, ?_⟩
    rw [hinv a haR]
    exact U.neg_mem haU
  · intro x hx
    exact hx.1
  · intro x
    rfl

theorem sevenFalse_card_sub {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] {R A : Subgroup K} {t : K} {π : K → W}
    (hπ : ∀ x ∈ R, ∀ y ∈ R, π (x * y) = π x + π y)
    (hzero : ∀ x ∈ R, π x = 0 ↔ x ∈ zpowers t) (hsurj : ∀ w : W, ∃ x ∈ R, π x = w)
    (U : Submodule (ZMod 2) W) (hA : ∀ x, x ∈ A ↔ x ∈ R ∧ π x ∈ U) (htR : t ∈ R)
    (ht2 : Nat.card (zpowers t) = 2) :
    Nat.card A = 2 * 2 ^ Module.finrank (ZMod 2) U := by
  have h1 : π 1 = 0 := by
    have := hπ 1 R.one_mem 1 R.one_mem
    simpa using this
  have hzR : zpowers t ≤ R := zpowers_le.mpr htR
  have hzA : zpowers t ≤ A := by
    intro x hx
    rw [hA]
    refine ⟨hzR hx, ?_⟩
    rw [(hzero x (hzR hx)).mpr hx]
    exact U.zero_mem
  let φ : ↥A →* Multiplicative U :=
    MonoidHom.mk' (fun x => Multiplicative.ofAdd (⟨π x, ((hA x).mp x.2).2⟩ : U)) (by
      intro a b
      exact congrArg Multiplicative.ofAdd
        (Subtype.ext (hπ a ((hA a).mp a.2).1 b ((hA b).mp b.2).1)))
  have hφsurj : Function.Surjective φ := by
    intro u
    obtain ⟨x, hxR, hx⟩ := hsurj (Multiplicative.toAdd u : U)
    have hxA : x ∈ A := (hA x).mpr ⟨hxR, by rw [hx]; exact (Multiplicative.toAdd u).2⟩
    refine ⟨⟨x, hxA⟩, ?_⟩
    exact congrArg Multiplicative.ofAdd (Subtype.ext hx)
  have hker : φ.ker = (zpowers t).subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have hxR : (x : K) ∈ R := ((hA x).mp x.2).1
    rw [← hzero _ hxR]
    constructor
    · intro h
      have := congrArg Multiplicative.toAdd h
      exact congrArg Subtype.val this
    · intro h
      exact congrArg Multiplicative.ofAdd (Subtype.ext h)
  have hcard := Subgroup.card_ker_mul_card_of_surjective hφsurj
  have hk : Nat.card φ.ker = 2 := by
    rw [hker, ← ht2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzA).toEquiv
  have hU : Nat.card (Multiplicative U) = 2 ^ Module.finrank (ZMod 2) U := by
    rw [Nat.card_congr Multiplicative.toAdd, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod]
  rw [← hcard, hk, hU]

theorem sevenFalse_normalizer_sub {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {R A : Subgroup K}
    {z : K} {π : K → W} {ζ : Module.End (ZMod 2) W} (hzR : z ∈ normalizer (R : Set K))
    (hζπ : ∀ x ∈ R, ζ (π x) = π (z * x * z⁻¹)) (h7 : ζ ^ 7 = 1) (U : Submodule (ZMod 2) W)
    (hU : ∀ u ∈ U, ζ u ∈ U) (hA : ∀ x, x ∈ A ↔ x ∈ R ∧ π x ∈ U) :
    z ∈ normalizer (A : Set K) := by
  have hpow : ∀ n : ℕ, ∀ u ∈ U, (ζ ^ n) u ∈ U := by
    intro n
    induction n with
    | zero => intro u hu; simpa using hu
    | succ n ih => intro u hu; rw [pow_succ, Module.End.mul_apply]; exact ih _ (hU u hu)
  rw [mem_normalizer_iff]
  intro x
  rw [hA, hA]
  constructor
  · rintro ⟨hxR, hxU⟩
    refine ⟨(mem_normalizer_iff.mp hzR x).mp hxR, ?_⟩
    rw [← hζπ x hxR]
    exact hU _ hxU
  · rintro ⟨hxR, hxU⟩
    have hxR' : x ∈ R := (mem_normalizer_iff.mp hzR x).mpr hxR
    refine ⟨hxR', ?_⟩
    have e : (ζ ^ 6) * ζ = 1 := by rw [← pow_succ]; exact h7
    have hx : π x = (ζ ^ 6) (ζ (π x)) := by
      rw [← Module.End.mul_apply, e]; simp
    rw [hx, hζπ x hxR']
    exact hpow 6 _ hxU

theorem sevenFalse_normalizer_center {A : Subgroup K} {z : K} (hzA : z ∈ normalizer (A : Set K)) :
    z ∈ normalizer ((A ⊓ centralizer (A : Set K) : Subgroup K) : Set K) := by
  have hz' : ∀ x, x ∈ A ↔ z * x * z⁻¹ ∈ A := fun x => mem_normalizer_iff.mp hzA x
  rw [mem_normalizer_iff]
  intro x
  rw [mem_inf, mem_inf, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · rintro ⟨hxA, hxc⟩
    refine ⟨(hz' x).mp hxA, ?_⟩
    intro h hh
    have hh' : z⁻¹ * h * z ∈ A := by
      rw [hz' (z⁻¹ * h * z)]
      have : z * (z⁻¹ * h * z) * z⁻¹ = h := by group
      rw [this]; exact hh
    have := hxc _ hh'
    calc h * (z * x * z⁻¹) = z * ((z⁻¹ * h * z) * x) * z⁻¹ := by group
      _ = z * (x * (z⁻¹ * h * z)) * z⁻¹ := by rw [this]
      _ = (z * x * z⁻¹) * h := by group
  · rintro ⟨hxA, hxc⟩
    refine ⟨(hz' x).mpr hxA, ?_⟩
    intro h hh
    have hh' : z * h * z⁻¹ ∈ A := (hz' h).mp hh
    have := hxc _ hh'
    calc h * x = z⁻¹ * ((z * h * z⁻¹) * (z * x * z⁻¹)) * z := by group
      _ = z⁻¹ * ((z * x * z⁻¹) * (z * h * z⁻¹)) * z := by rw [this]
      _ = x * h := by group

theorem seven_false {R : Subgroup K} {t z : K} (hR : IsExt2 R t) (hz : z ^ 7 = 1)
    (hzR : z ∈ normalizer (R : Set K)) (hzt : z * t = t * z)
    (hfix : ∀ r ∈ R, z * r = r * z → r ∈ zpowers t)
    (hstar : ∀ A : Subgroup K, A ≤ R → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      z ∈ normalizer (A : Set K) → ∀ a ∈ A, z * a = a * z)
    (hcard : Nat.card R = 2 ^ 7) : False := by
  obtain ⟨W, iW, mW, fW, π, ζ, hadd, hzero, hsurj, hζ, h7, hnofix⟩ :=
    sevenFalse_module hR hz hzR hzt hfix
  have ht2 : Nat.card (zpowers t) = 2 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime hR.t_sq hR.t_ne
  have hzt_le : zpowers t ≤ R := zpowers_le.mpr hR.t_mem
  haveI : Nontrivial W := by
    obtain ⟨x, hxR, hxt⟩ : ∃ x ∈ R, x ∉ zpowers t := by
      by_contra hcon
      push Not at hcon
      have hle : R ≤ zpowers t := fun x hx => hcon x hx
      have := Subgroup.card_le_of_le hle
      rw [hcard, ht2] at this
      norm_num at this
    exact ⟨⟨π x, 0, fun h => hxt ((hzero x hxR).mp h)⟩⟩
  obtain ⟨U, hU0, hUζ, hdim⟩ := exists_invariant_subspace_seven ζ h7 hnofix
  obtain ⟨A, hAR, hA⟩ := sevenFalse_exists_sub hadd U
  have hcardA := sevenFalse_card_sub hadd hzero hsurj U hA hR.t_mem ht2
  have hzA := sevenFalse_normalizer_sub hzR hζ h7 U hUζ hA
  have htA : zpowers t ≤ A := by
    intro x hx
    rw [hA]
    refine ⟨hzt_le hx, ?_⟩
    rw [(hzero x (hzt_le hx)).mpr hx]
    exact U.zero_mem
  have hAC : A ⊓ centralizer ({z} : Set K) = zpowers t := by
    apply le_antisymm
    · intro x hx
      rw [mem_inf, mem_centralizer_iff] at hx
      obtain ⟨hxA, hxc⟩ := hx
      exact hfix x (hAR hxA) (hxc z (Set.mem_singleton z))
    · intro x hx
      rw [mem_inf, mem_centralizer_iff]
      refine ⟨htA hx, ?_⟩
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
      exact ((show Commute h t from hzt).zpow_right n).eq
  have hmod := card_modEq_card_inf_centralizer (V := A) (z := z) (p := 7) (by norm_num) hz hzA
  rw [hAC, ht2, hcardA] at hmod
  have hd1 : 1 ≤ Module.finrank (ZMod 2) U :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hU0)
  have hd : Module.finrank (ZMod 2) U = 3 := by
    generalize Module.finrank (ZMod 2) U = d at hd1 hdim hmod
    interval_cases d
    · exact absurd hmod (by decide)
    · exact absurd hmod (by decide)
    · rfl
  have hExtA : IsExt2 A t := by
    refine ⟨htA (mem_zpowers t), hR.t_sq, hR.t_ne, fun r hr => hR.t_comm r (hAR hr), ?_,
      fun r hr => hR.sq_mem r (hAR hr),
      fun r hr s hs => hR.comm_mem r (hAR hr) s (hAR hs)⟩
    intro y hyA hy
    have hZcR : A ⊓ centralizer (A : Set K) ≤ R := inf_le_left.trans hAR
    have hZcab : ∀ a ∈ A ⊓ centralizer (A : Set K), ∀ b ∈ A ⊓ centralizer (A : Set K),
        a * b = b * a := by
      intro a ha b hb
      rw [mem_inf] at ha hb
      exact (mem_centralizer_iff.mp ha.2 b hb.1).symm
    have hyZc : y ∈ A ⊓ centralizer (A : Set K) :=
      mem_inf.mpr ⟨hyA, mem_centralizer_iff.mpr (fun h hh => (hy h hh).symm)⟩
    exact hfix y (hAR hyA)
      (hstar (A ⊓ centralizer (A : Set K)) hZcR hZcab (sevenFalse_normalizer_center hzA) y hyZc)
  obtain ⟨k, hk⟩ := hExtA.card_eq
  rw [hcardA, hd] at hk
  have h4 : (2 : ℕ) ^ 4 = 2 ^ (1 + 2 * k) := by rw [← hk]; norm_num
  have := Nat.pow_right_injective (le_refl 2) h4
  omega
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628
