module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeTIFacts.Matrix
public import CFSG.Adapters.FrobeniusKernel

public section

namespace CFSG.Semidihedral.AllPrime.QDTI

noncomputable section

open Matrix CFSG.Semidihedral CFSG.Semidihedral.MatrixCoverData CFSG.Semidihedral.MatrixTorus
open scoped Pointwise

theorem frobenius_kernel_subgroup {G₀ : Type} [Group G₀] [Finite G₀] {R W : Subgroup G₀}
    (hWR : W ≤ R) (hW1 : W ≠ ⊥) (hRW : ¬ R ≤ W)
    (hfrob : ∀ g ∈ R, g ∉ W → ∀ x ∈ W, g⁻¹ * x * g ∈ W → x = 1) :
    ∃ K : Subgroup G₀, K ≤ R ∧ (∀ g ∈ R, ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧ K ⊓ W = ⊥ ∧
      (∀ x ∈ R, ∃ k ∈ K, ∃ w ∈ W, x = k * w) ∧
      (∀ x ∈ R, x ∈ K ↔ (x = 1 ∨ ∀ g ∈ R, g⁻¹ * x * g ∉ W)) := by
  set H : Subgroup R := W.subgroupOf R with hHdef
  have hconj : ∀ a g : R, g ∈ MulAut.conj a • H ↔ a⁻¹ * g * a ∈ H := by
    intro a g
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, ← map_inv,
      MulAut.conj_apply, inv_inv]
  have hH1 : H ≠ ⊥ := by
    obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW1
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨⟨w, hWR hw⟩, hw⟩, fun h => hw1 (Subtype.ext ?_)⟩
    exact congrArg (fun y : R => (y : G₀)) (congrArg Subtype.val h)
  have hHtop : H ≠ ⊤ := by
    rw [hHdef, Ne, Subgroup.subgroupOf_eq_top]
    exact hRW
  have hfrob' : ∀ g : R, g ∉ H → H ⊓ (MulAut.conj g • H) = ⊥ := by
    intro g hg
    rw [eq_bot_iff]
    intro x hx
    have hxH : x ∈ H := hx.1
    have hxc : x ∈ MulAut.conj g • H := hx.2
    rw [Subgroup.mem_bot]
    rw [hconj] at hxc
    apply Subtype.ext
    exact hfrob g g.2 hg x hxH hxc
  obtain ⟨K₀, hKset, hKn, hdecomp, hKH, -⟩ := CFSG.Adapters.frobenius_kernel H hH1 hHtop hfrob'
  have hmemK : ∀ x : R, x ∈ K₀ ↔ x = 1 ∨ ∀ g : R, g⁻¹ * x * g ∉ H := by
    intro x
    rw [← SetLike.mem_coe, hKset]
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_univ, true_and,
      Set.mem_iUnion, SetLike.mem_coe, hconj, not_exists]
  refine ⟨K₀.map R.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · rintro g hg _ ⟨k, hk, rfl⟩
    exact ⟨⟨g, hg⟩ * k * ⟨g, hg⟩⁻¹, hKn.conj_mem k hk ⟨g, hg⟩, rfl⟩
  · rw [eq_bot_iff]
    rintro _ ⟨⟨k, hk, rfl⟩, hkW⟩
    have : k ∈ K₀ ⊓ H := ⟨hk, hkW⟩
    rw [hKH, Subgroup.mem_bot] at this
    rw [this]
    exact Subgroup.one_mem _
  · intro x hx
    obtain ⟨k, hk, h, hh, hkh⟩ := hdecomp ⟨x, hx⟩
    exact ⟨k, ⟨k, hk, rfl⟩, h, hh, congrArg Subtype.val hkh⟩
  · intro x hx
    constructor
    · rintro ⟨k, hk, rfl⟩
      rcases (hmemK k).mp hk with h1 | h
      · left
        rw [h1]
        rfl
      · right
        intro g hg hgW
        exact h ⟨g, hg⟩ hgW
    · rintro (h1 | h)
      · rw [h1]
        exact Subgroup.one_mem _
      · refine ⟨⟨x, hx⟩, (hmemK _).mpr (Or.inr fun g hg => h g g.2 hg), rfl⟩

variable {F : Type} [Field F]

@[expose] def Wsl (a : Fˣ) : Subgroup (SL F) := (W F a).map (Torus F a).subtype

theorem Wsl_le_torus (a : Fˣ) : Wsl a ≤ Torus F a := Subgroup.map_subtype_le _

theorem mem_Wsl_iff [Finite F] (hodd : Odd (Nat.card F)) (a : Fˣ) (ha : ¬IsSquare a)
    (x : SL F) : x ∈ Wsl a ↔ x ∈ Torus F a ∧ Odd (orderOf x) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
    exact (mem_W_iff_odd_order F a hodd ha y).mp hy
  · rintro ⟨hx, hxo⟩
    refine ⟨⟨x, hx⟩, (mem_W_iff_odd_order F a hodd ha _).mpr ?_, rfl⟩
    rwa [Subgroup.orderOf_mk]

theorem card_Wsl [Finite F] (hodd : Odd (Nat.card F)) (a : Fˣ) (ha : ¬IsSquare a) :
    Nat.card (Wsl a) = torusSize (Nat.card F) / 2 := by
  rw [Wsl, Subgroup.card_map_of_injective (Torus F a).subtype_injective, W_card F a hodd ha]

theorem torus_entries_ne_zero_of_odd (a : Fˣ) {w : SL F} (hw : w ∈ Torus F a)
    (hwo : Odd (orderOf w)) (hw1 : w ≠ 1) : w.1 0 0 * w.1 1 0 ≠ 0 := by
  intro h
  have h4 := torus_pow_four a hw h
  have hdvd : orderOf w ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have h1 : orderOf w = 1 := by
    have hc : Nat.Coprime (orderOf w) 4 :=
      Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hwo)
    exact Nat.Coprime.eq_one_of_dvd hc hdvd
  exact hw1 (orderOf_eq_one_iff.mp h1)

theorem not_odd_orderOf_of_sq_eq_neg_one (h2 : (2 : F) ≠ 0) {g : SL F}
    (hg : g ^ 2 = OddFieldSL2.minusIdentity F) : ¬ Odd (orderOf g) := by
  intro hodd
  have h4 : g ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hg, OddFieldSL2.minusIdentity_square]
  have hdvd : orderOf g ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hc : Nat.Coprime (orderOf g) 4 := Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hodd)
  have h1 : orderOf g = 1 := Nat.Coprime.eq_one_of_dvd hc hdvd
  rw [orderOf_eq_one_iff.mp h1, one_pow] at hg
  exact OddFieldSL2.minusIdentity_ne_one F h2 hg.symm

theorem beta_beta (a : Fˣ) (x : SL F) : beta F a (beta F a x) = x := by
  have h := congrArg (fun φ : MulAut (SL F) => φ x) (beta_square F a)
  simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h

theorem torusSize_half_ge_three {q : ℕ} (hq : 7 ≤ q) : 3 ≤ torusSize q / 2 := by
  unfold torusSize
  split_ifs <;> omega

theorem odd_subgroup_structure [Finite F] (hodd : Odd (Nat.card F)) (a : Fˣ)
    (ha : ¬IsSquare a) (hq : 7 ≤ Nat.card F) {R : Subgroup (SL F)} (hRodd : Odd (Nat.card R))
    (hWR : Wsl a ≤ R) (hβ : ∀ x ∈ R, beta F a x ∈ R) :
    R ≤ Wsl a ∨ ∃ l : F, l ^ 2 = -(a : F) ∧ R ≤ Wsl a ⊔ rootGroup l := by
  have h2 := OddFieldSL2.two_ne_zero_of_odd_card F hodd
  by_cases hRW : R ≤ Wsl a
  · exact Or.inl hRW
  right
  have hRo : ∀ x ∈ R, Odd (orderOf x) := by
    intro x hx
    have h := orderOf_dvd_natCard (⟨x, hx⟩ : R)
    rw [Subgroup.orderOf_mk] at h
    exact hRodd.of_dvd_nat h
  have hWcard : 3 ≤ Nat.card (Wsl a) := by
    rw [card_Wsl hodd a ha]
    exact torusSize_half_ge_three hq
  have hW1 : Wsl a ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hWcard
    omega
  obtain ⟨⟨w₀, hw₀⟩, hw₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW1
  have hw₀1 : w₀ ≠ 1 := fun h => hw₀ne (Subtype.ext h)
  obtain ⟨hw₀T, hw₀o⟩ := (mem_Wsl_iff hodd a ha w₀).mp hw₀
  have hw₀xy := torus_entries_ne_zero_of_odd a hw₀T hw₀o hw₀1
  have hfrob : ∀ g ∈ R, g ∉ Wsl a → ∀ x ∈ Wsl a, g⁻¹ * x * g ∈ Wsl a → x = 1 := by
    intro g hg hgW x hx hgx
    by_contra hx1
    obtain ⟨hxT, hxo⟩ := (mem_Wsl_iff hodd a ha x).mp hx
    have hx10 : x.1 1 0 ≠ 0 := fun h =>
      torus_entries_ne_zero_of_odd a hxT hxo hx1 (by rw [h, mul_zero])
    obtain ⟨hgxT, -⟩ := (mem_Wsl_iff hodd a ha _).mp hgx
    have hcomm : g * (g⁻¹ * x * g) = x * g := by group
    rcases torus_or_anticomm_of_conj a h2 hxT hgxT hx10 hcomm with hgT | hgA
    · exact hgW ((mem_Wsl_iff hodd a ha g).mpr ⟨hgT, hRo g hg⟩)
    · exact not_odd_orderOf_of_sq_eq_neg_one h2 (sq_eq_neg_one_of_anticomm a hgA) (hRo g hg)
  obtain ⟨K, hKR, hKn, hKW, hdec, hKmem⟩ := frobenius_kernel_subgroup hWR hW1 hRW hfrob
  have hβW : ∀ w ∈ Wsl a, beta F a w = w := fun w hw =>
    (beta_fixed_iff F a w).mpr (Wsl_le_torus a hw)
  have hKβ : ∀ k ∈ K, beta F a k ∈ K := by
    intro k hk
    have hkR := hKR hk
    rw [hKmem _ (hβ k hkR)]
    rcases (hKmem k hkR).mp hk with h1 | h
    · left
      rw [h1, map_one]
    · right
      intro g hg hgW
      apply h (beta F a g) (hβ g hg)
      have : beta F a (g⁻¹ * beta F a k * g) = (beta F a g)⁻¹ * k * beta F a g := by
        simp only [map_mul, map_inv, beta_beta]
      rw [← this, hβW _ hgW]
      exact hgW
  have hKfix : ∀ k ∈ K, beta F a k = k → k = 1 := by
    intro k hk hfix
    have hkW : k ∈ Wsl a :=
      (mem_Wsl_iff hodd a ha k).mpr ⟨(beta_fixed_iff F a k).mp hfix, hRo k (hKR hk)⟩
    have : k ∈ K ⊓ Wsl a := ⟨hk, hkW⟩
    rwa [hKW, Subgroup.mem_bot] at this
  let βK : K →* K :=
    { toFun := fun k => ⟨beta F a k, hKβ k k.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _) }
  have hfree : MonoidHom.FixedPointFree βK := by
    intro k hk
    exact Subtype.ext (hKfix k k.2 (congrArg Subtype.val hk))
  have hinvol : Function.Involutive βK := fun k => Subtype.ext (beta_beta a k)
  have hinvK : ∀ k ∈ K, beta F a k = k⁻¹ := by
    intro k hk
    have h := congrFun (hfree.coe_eq_inv_of_involutive hinvol) ⟨k, hk⟩
    exact congrArg Subtype.val h
  have hcommK : ∀ k ∈ K, ∀ k' ∈ K, k * k' = k' * k := by
    intro k hk k' hk'
    have h := hfree.commute_all_of_involutive hinvol ⟨k, hk⟩ ⟨k', hk'⟩
    exact congrArg Subtype.val h.eq
  have hroot : ∀ k ∈ K, k ≠ 1 → ∃ l : F, l ^ 2 = -(a : F) ∧ k ∈ rootGroup l := by
    intro k hk hk1
    have hk' := hKn w₀ (hWR hw₀) k hk
    exact inverted_odd_mem_rootGroup a h2 (hinvK k hk) hk1 (hRo k (hKR hk)) hw₀T hw₀xy
      (hcommK k hk _ hk')
  have hK1 : ∃ k ∈ K, k ≠ 1 := by
    by_contra hcon
    apply hRW
    intro x hx
    obtain ⟨k, hk, w, hw, rfl⟩ := hdec x hx
    have hk1 : k = 1 := by
      by_contra hk1
      exact hcon ⟨k, hk, hk1⟩
    rw [hk1, one_mul]
    exact hw
  obtain ⟨k₀, hk₀, hk₀1⟩ := hK1
  obtain ⟨b, hb, -⟩ := hroot k₀ hk₀ hk₀1
  have hor : ∀ k ∈ K, k ∈ rootGroup b ∨ k ∈ rootGroup (-b) := by
    intro k hk
    by_cases hk1 : k = 1
    · left
      rw [hk1]
      exact Subgroup.one_mem _
    obtain ⟨l, hl, hkl⟩ := hroot k hk hk1
    have : (l - b) * (l + b) = 0 := by linear_combination hl - hb
    rcases mul_eq_zero.mp this with h | h
    · left
      rwa [show l = b by linear_combination h] at hkl
    · right
      rwa [show l = -b by linear_combination h] at hkl
  have hfin : ∀ l : F, K ≤ rootGroup l → R ≤ Wsl a ⊔ rootGroup l := by
    intro l hKl x hx
    obtain ⟨k, hk, w, hw, rfl⟩ := hdec x hx
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hKl hk)) (Subgroup.mem_sup_left hw)
  rcases le_or_le_of_forall_mem_or_mem hor with hKb | hKb
  · exact ⟨b, hb, hfin b hKb⟩
  · exact ⟨-b, by rw [neg_sq]; exact hb, hfin (-b) hKb⟩

theorem not_odd_orderOf_neg (h2 : (2 : F) ≠ 0) {r : SL F} (hr : Odd (orderOf r)) :
    ¬ Odd (orderOf (OddFieldSL2.minusIdentity F * r)) := by
  have hc : Commute (OddFieldSL2.minusIdentity F) r :=
    (Subgroup.mem_center_iff.mp (OddFieldSL2.minusIdentity_mem_center F) r).symm
  rw [hc.orderOf_mul_eq_mul_orderOf_of_coprime (by
    rw [OddFieldSL2.minusIdentity_orderOf F h2]
    exact Nat.coprime_two_left.mpr hr), OddFieldSL2.minusIdentity_orderOf F h2]
  rw [Nat.odd_mul]
  intro h
  exact absurd h.1 (by decide)

theorem torus_overgroup_structure [Finite F] (hodd : Odd (Nat.card F)) (a : Fˣ)
    (ha : ¬IsSquare a) (hq : 7 ≤ Nat.card F) {R₀ : Subgroup (SL F)} (hTR : Torus F a ≤ R₀)
    (hidx : Odd ((Torus F a).relIndex R₀)) (hβ : ∀ x ∈ R₀, beta F a x ∈ R₀) :
    R₀ ≤ Torus F a ∨ ∃ l : F, l ^ 2 = -(a : F) ∧ R₀ ≤ Torus F a ⊔ rootGroup l := by
  classical
  have h2 := OddFieldSL2.two_ne_zero_of_odd_card F hodd
  set m := OddFieldSL2.minusIdentity F with hm
  have hm2 : orderOf m = 2 := OddFieldSL2.minusIdentity_orderOf F h2
  have hmT : m ∈ Torus F a := (MatrixTorus.z F a).2
  have hmR : m ∈ R₀ := hTR hmT
  set Z : Subgroup R₀ := Subgroup.zpowers ⟨m, hmR⟩ with hZ
  have hZn : Z.Normal := by
    apply Subgroup.normal_of_le_center
    rw [hZ, Subgroup.zpowers_le]
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (OddFieldSL2.minusIdentity_mem_center F) g
  have hZcard : Nat.card Z = 2 := by
    rw [hZ, Nat.card_zpowers, Subgroup.orderOf_mk, hm2]
  have hR₀card : Nat.card R₀ = torusSize (Nat.card F) * (Torus F a).relIndex R₀ := by
    rw [← torus_card F a hodd ha, ← Subgroup.relIndex_mul_card (H := Torus F a) (K := R₀),
      inf_of_le_left hTR, mul_comm]
  have hTodd : Odd (torusSize (Nat.card F) / 2) := torusSize_half_odd hodd
  have hTeq : torusSize (Nat.card F) = 2 * (torusSize (Nat.card F) / 2) :=
    torusSize_two_mul_half hodd
  have hZindex : Z.index = torusSize (Nat.card F) / 2 * (Torus F a).relIndex R₀ := by
    have h := Z.card_mul_index
    rw [hZcard, hR₀card, hTeq, mul_assoc] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hcop : Nat.Coprime (Nat.card Z) Z.index := by
    rw [hZcard, hZindex]
    exact Nat.coprime_two_left.mpr (hTodd.mul hidx)
  obtain ⟨R', hR'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hR'card : Nat.card R' = torusSize (Nat.card F) / 2 * (Torus F a).relIndex R₀ := by
    have h := hR'.card_mul_card
    rw [hZcard, hR₀card, hTeq, mul_assoc] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hR'odd : Odd (Nat.card R') := by rw [hR'card]; exact hTodd.mul hidx
  set R'' : Subgroup (SL F) := R'.map R₀.subtype with hR''
  have hR''card : Nat.card R'' = Nat.card R' := by
    rw [hR'', Subgroup.card_map_of_injective R₀.subtype_injective]
  have hmemZ : ∀ z : R₀, z ∈ Z → (z : SL F) = 1 ∨ (z : SL F) = m := by
    intro z hz
    rw [hZ, mem_zpowers_iff_mem_range_orderOf, Subgroup.orderOf_mk, hm2] at hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
    have hn' : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · left
      simp
    · right
      simp
  have hdecomp : ∀ x ∈ R₀, ∃ z : R₀, z ∈ Z ∧ ∃ r ∈ R'', x = z * r := by
    intro x hx
    obtain ⟨⟨z, r⟩, hzr, -⟩ := (Subgroup.isComplement'_def.mp hR').existsUnique ⟨x, hx⟩
    exact ⟨z, z.2, r, ⟨r, r.2, rfl⟩, (congrArg Subtype.val hzr).symm⟩
  have hR''odd : ∀ r ∈ R'', Odd (orderOf r) := by
    rintro _ ⟨r, hr, rfl⟩
    have h := orderOf_dvd_natCard (⟨r, hr⟩ : R')
    rw [Subgroup.orderOf_mk] at h
    rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
    exact hR'odd.of_dvd_nat h
  have hodd_mem : ∀ x ∈ R₀, Odd (orderOf x) → x ∈ R'' := by
    intro x hx hxo
    obtain ⟨z, hz, r, hr, rfl⟩ := hdecomp x hx
    rcases hmemZ z hz with h1 | hzm
    · rw [h1, one_mul]
      exact hr
    · rw [hzm] at hxo
      exact absurd hxo (not_odd_orderOf_neg h2 (hR''odd r hr))
  have hWR'' : Wsl a ≤ R'' := by
    intro w hw
    obtain ⟨hwT, hwo⟩ := (mem_Wsl_iff hodd a ha w).mp hw
    exact hodd_mem w (hTR hwT) hwo
  have hβR'' : ∀ x ∈ R'', beta F a x ∈ R'' := by
    intro x hx
    have hxR : x ∈ R₀ := by
      obtain ⟨r, -, rfl⟩ := hx
      exact r.2
    apply hodd_mem _ (hβ x hxR)
    rw [MulEquiv.orderOf_eq]
    exact hR''odd x hx
  have hfin : ∀ X : Subgroup (SL F), R'' ≤ X → Torus F a ≤ X → R₀ ≤ X := by
    intro X hR''X hTX x hx
    obtain ⟨z, hz, r, hr, rfl⟩ := hdecomp x hx
    refine X.mul_mem ?_ (hR''X hr)
    rcases hmemZ z hz with h1 | hzm
    · rw [h1]
      exact X.one_mem
    · rw [hzm]
      exact hTX hmT
  rcases odd_subgroup_structure hodd a ha hq (hR''card ▸ hR'odd) hWR'' hβR'' with h | ⟨l, hl, h⟩
  · left
    exact hfin _ (h.trans (Wsl_le_torus a)) le_rfl
  · right
    refine ⟨l, hl, hfin _ (h.trans (sup_le_sup_right (Wsl_le_torus a) _)) le_sup_left⟩

section Permutable

variable {G₀ : Type} [Group G₀]

@[expose] def permProd (U C : Subgroup G₀) (hUC : (U : Set G₀) * C = C * U) : Subgroup G₀ where
  carrier := (U : Set G₀) * C
  mul_mem' {x y} hx hy := by
    obtain ⟨u₁, hu₁, c₁, hc₁, rfl⟩ := hx
    obtain ⟨u₂, hu₂, c₂, hc₂, rfl⟩ := hy
    have hcu : c₁ * u₂ ∈ (U : Set G₀) * C := by
      rw [hUC]
      exact Set.mul_mem_mul hc₁ hu₂
    obtain ⟨u₃, hu₃, c₃, hc₃, h⟩ := hcu
    refine ⟨u₁ * u₃, U.mul_mem hu₁ hu₃, c₃ * c₂, C.mul_mem hc₃ hc₂, ?_⟩
    change u₁ * u₃ * (c₃ * c₂) = u₁ * c₁ * (u₂ * c₂)
    rw [show u₁ * c₁ * (u₂ * c₂) = u₁ * (c₁ * u₂) * c₂ by group, ← h]
    group
  one_mem' := ⟨1, U.one_mem, 1, C.one_mem, mul_one 1⟩
  inv_mem' {x} hx := by
    obtain ⟨u, hu, c, hc, rfl⟩ := hx
    have : (u * c)⁻¹ ∈ (C : Set G₀) * U := by
      rw [_root_.mul_inv_rev]
      exact Set.mul_mem_mul (C.inv_mem hc) (U.inv_mem hu)
    rwa [← hUC] at this

theorem sup_eq_permProd (U C : Subgroup G₀) (hUC : (U : Set G₀) * C = C * U) :
    U ⊔ C = permProd U C hUC := by
  apply le_antisymm
  · apply sup_le
    · intro u hu
      exact ⟨u, hu, 1, C.one_mem, mul_one u⟩
    · intro c hc
      exact ⟨1, U.one_mem, c, hc, one_mul c⟩
  · rintro _ ⟨u, hu, c, hc, rfl⟩
    exact Subgroup.mul_mem_sup hu hc

theorem mem_sup_iff_of_permute {U C : Subgroup G₀} (hUC : (U : Set G₀) * C = C * U) (x : G₀) :
    x ∈ U ⊔ C ↔ ∃ u ∈ U, ∃ c ∈ C, x = u * c := by
  rw [sup_eq_permProd U C hUC]
  constructor
  · rintro ⟨u, hu, c, hc, h⟩
    exact ⟨u, hu, c, hc, h.symm⟩
  · rintro ⟨u, hu, c, hc, rfl⟩
    exact ⟨u, hu, c, hc, rfl⟩

theorem relIndex_sup_dvd_card_of_permute [Finite G₀] {U C : Subgroup G₀}
    (hUC : (U : Set G₀) * C = C * U) : C.relIndex (U ⊔ C) ∣ Nat.card U := by
  set K := U ⊔ C with hK
  let ι : U →* K := Subgroup.inclusion le_sup_left
  let : MulAction U (K ⧸ C.subgroupOf K) := MulAction.compHom _ ι
  have hsmul : ∀ (g : U) (x : K), g • (x : K ⧸ C.subgroupOf K) = ((ι g * x : K) :
      K ⧸ C.subgroupOf K) := fun g x => rfl
  have hbase : ∀ x : K ⧸ C.subgroupOf K, ∃ g : U, g • ((1 : K) : K ⧸ C.subgroupOf K) = x := by
    intro x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨u, hu, c, hc, hkuc⟩ := (mem_sup_iff_of_permute hUC k).mp k.2
    refine ⟨⟨u, hu⟩, ?_⟩
    rw [hsmul, mul_one, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    change (ι ⟨u, hu⟩ : G₀)⁻¹ * k ∈ C
    change u⁻¹ * (k : G₀) ∈ C
    rw [hkuc, inv_mul_cancel_left]
    exact hc
  have : MulAction.IsPretransitive U (K ⧸ C.subgroupOf K) := by
    constructor
    intro x y
    obtain ⟨g₁, rfl⟩ := hbase x
    obtain ⟨g₂, rfl⟩ := hbase y
    exact ⟨g₂ * g₁⁻¹, by rw [mul_smul, inv_smul_smul]⟩
  have h := MulAction.index_stabilizer_of_transitive U ((1 : K) : K ⧸ C.subgroupOf K)
  change Nat.card (K ⧸ C.subgroupOf K) ∣ Nat.card U
  rw [← h]
  exact Subgroup.index_dvd_card _

end Permutable

end

end CFSG.Semidihedral.AllPrime.QDTI
