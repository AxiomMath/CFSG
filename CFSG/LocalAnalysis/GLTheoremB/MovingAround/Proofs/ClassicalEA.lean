module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Leaves
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.OmegaFacts2
public import CFSG.RankThree.OrthogonalInvolutions.Witt
public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualModel
public import CFSG.RankThree.Classical.SteinbergR3EHigherSymplecticOuterOrder

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.ClassicalEA

open Module CFSG.Open

section Basic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def fixSp (g : V →ₗ[K] V) : Submodule K V := LinearMap.ker (g - LinearMap.id)

theorem mem_fixSp {g : V →ₗ[K] V} {v : V} : v ∈ fixSp g ↔ g v = v := by
  simp [fixSp, sub_eq_zero]

@[expose] def ptw (S : Submodule K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ x ∈ S, g x = x}
  mul_mem' := fun {a b} ha hb x hx => by rw [LinearEquiv.mul_apply, hb x hx, ha x hx]
  one_mem' := fun _ _ => rfl
  inv_mem' := fun {a} ha x hx => by
    have h1 : (a⁻¹ * a) x = x := by rw [inv_mul_cancel]; rfl
    rw [LinearEquiv.mul_apply, ha x hx] at h1
    exact h1

theorem mem_ptw {S : Submodule K V} {g : V ≃ₗ[K] V} : g ∈ ptw S ↔ ∀ x ∈ S, g x = x := Iff.rfl

theorem inv_apply_eq_of_apply_eq {g : V ≃ₗ[K] V} {x y : V} (h : g x = y) : g⁻¹ y = x := by
  rw [← h]
  have h1 : (g⁻¹ * g) x = x := by rw [inv_mul_cancel]; rfl
  exact h1

theorem apply_inv_apply (g : V ≃ₗ[K] V) (y : V) : g (g⁻¹ y) = y := by
  have h1 : (g * g⁻¹) y = y := by rw [mul_inv_cancel]; rfl
  exact h1

@[expose] noncomputable def glue {W W' : Submodule K V} (hc : IsCompl W W') (g : V →ₗ[K] V) :
    V →ₗ[K] V :=
  LinearMap.ofIsCompl hc (g ∘ₗ W.subtype) W'.subtype

theorem glue_left {W W' : Submodule K V} (hc : IsCompl W W') (g : V →ₗ[K] V) {w : V}
    (hw : w ∈ W) : glue hc g w = g w :=
  LinearMap.ofIsCompl_apply_left hc (u := ⟨w, hw⟩)

theorem glue_right {W W' : Submodule K V} (hc : IsCompl W W') (g : V →ₗ[K] V) {x : V}
    (hx : x ∈ W') : glue hc g x = x :=
  LinearMap.ofIsCompl_apply_right hc (v := ⟨x, hx⟩)

theorem exists_add_of_isCompl {W W' : Submodule K V} (hc : IsCompl W W') (v : V) :
    ∃ w ∈ W, ∃ x ∈ W', v = w + x := by
  have hv : v ∈ W ⊔ W' := by rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨w, hw, x, hx, h⟩ := Submodule.mem_sup.1 hv
  exact ⟨w, hw, x, hx, h.symm⟩

theorem linearMap_ext_of_isCompl {W W' : Submodule K V} (hc : IsCompl W W')
    {f g : V →ₗ[K] V} (h1 : ∀ w ∈ W, f w = g w) (h2 : ∀ x ∈ W', f x = g x) : f = g := by
  ext v
  obtain ⟨w, hw, x, hx, rfl⟩ := exists_add_of_isCompl hc v
  rw [map_add, map_add, h1 w hw, h2 x hx]

theorem linearEquiv_ext_of_isCompl {W W' : Submodule K V} (hc : IsCompl W W')
    {f g : V ≃ₗ[K] V} (h1 : ∀ w ∈ W, f w = g w) (h2 : ∀ x ∈ W', f x = g x) : f = g :=
  LinearEquiv.toLinearMap_injective (linearMap_ext_of_isCompl hc h1 h2)

theorem glue_injective {W W' : Submodule K V} (hc : IsCompl W W') (g : V ≃ₗ[K] V)
    (hg : ∀ w ∈ W, g w ∈ W) : Function.Injective (glue hc g.toLinearMap) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  obtain ⟨w, hw, x, hx, rfl⟩ := exists_add_of_isCompl hc v
  rw [map_add, glue_left hc _ hw, glue_right hc _ hx] at hv
  have hgw : g w ∈ W := hg w hw
  have h1 : g w = -x := eq_neg_of_add_eq_zero_left hv
  have hxW : g w ∈ W' := h1 ▸ W'.neg_mem hx
  have h0 : g w = 0 := (Submodule.disjoint_def.1 hc.disjoint) _ hgw hxW
  have hw0 : w = 0 := g.injective (by rw [h0, map_zero])
  subst hw0
  rw [map_zero, zero_add] at hv
  rw [zero_add]
  exact hv

variable [FiniteDimensional K V]

@[expose] noncomputable def glueE {W W' : Submodule K V} (hc : IsCompl W W') (g : V ≃ₗ[K] V)
    (hg : ∀ w ∈ W, g w ∈ W) : V ≃ₗ[K] V :=
  LinearEquiv.ofInjectiveEndo _ (glue_injective hc g hg)

theorem glueE_left {W W' : Submodule K V} (hc : IsCompl W W') (g : V ≃ₗ[K] V)
    (hg : ∀ w ∈ W, g w ∈ W) {w : V} (hw : w ∈ W) : glueE hc g hg w = g w :=
  glue_left hc _ hw

theorem glueE_right {W W' : Submodule K V} (hc : IsCompl W W') (g : V ≃ₗ[K] V)
    (hg : ∀ w ∈ W, g w ∈ W) {x : V} (hx : x ∈ W') : glueE hc g hg x = x :=
  glue_right hc _ hx

end Basic

section Bilin

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def Nondeg (B : LinearMap.BilinForm (ZMod 2) V) (W : Submodule (ZMod 2) V) : Prop :=
  Disjoint W (B.orthogonal W)

variable {B : LinearMap.BilinForm (ZMod 2) V}

theorem nondeg_iff {W : Submodule (ZMod 2) V} :
    Nondeg B W ↔ ∀ w ∈ W, (∀ u ∈ W, B u w = 0) → w = 0 := by
  unfold Nondeg
  rw [Submodule.disjoint_def]
  exact ⟨fun h w hw hu => h w hw hu, fun h w hw hu => h w hw hu⟩

theorem nsmul_odd {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {p : ℕ} (hp : Odd p) (c : M) :
    p • c = c := by
  obtain ⟨k, rfl⟩ := hp
  have h2 : (2 : ℕ) • c = 0 := by
    rw [two_nsmul, ← two_smul (ZMod 2) c]
    have : (2 : ZMod 2) = 0 := rfl
    rw [this, zero_smul]
  rw [add_nsmul, one_nsmul, mul_nsmul, h2, nsmul_zero, zero_add]

theorem sum_range_odd {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {p : ℕ} (hp : Odd p)
    (c : M) : ∑ _i ∈ Finset.range p, c = c := by
  rw [Finset.sum_const, Finset.card_range, nsmul_odd hp]

variable (hBs : ∀ x y, B x y = B y x)
include hBs

theorem isRefl_of_symm : B.IsRefl := fun x y h => by rw [hBs]; exact h

variable [FiniteDimensional (ZMod 2) V]

theorem isCompl_of_nondeg {W : Submodule (ZMod 2) V} (hW : Nondeg B W) :
    IsCompl W (B.orthogonal W) :=
  (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint (isRefl_of_symm hBs)).2 hW

variable (hB : B.Nondegenerate)
include hB

theorem orth_orth (W : Submodule (ZMod 2) V) : B.orthogonal (B.orthogonal W) = W :=
  LinearMap.BilinForm.orthogonal_orthogonal hB (isRefl_of_symm hBs) W

theorem nondeg_orth {W : Submodule (ZMod 2) V} (hW : Nondeg B W) : Nondeg B (B.orthogonal W) := by
  unfold Nondeg
  rw [orth_orth hBs hB]
  exact hW.symm

theorem nondeg_top : Nondeg B ⊤ := by
  rw [nondeg_iff]
  intro w _ hw
  exact hB.2 w fun u => hw u Submodule.mem_top

end Bilin

section OddOrder

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {B : LinearMap.BilinForm (ZMod 2) V}

@[expose] def IsIsom (B : LinearMap.BilinForm (ZMod 2) V) (g : V ≃ₗ[ZMod 2] V) : Prop :=
  ∀ x y, B (g x) (g y) = B x y

theorem IsIsom.pow {g : V ≃ₗ[ZMod 2] V} (hg : IsIsom B g) (n : ℕ) : IsIsom B (g ^ n) := by
  induction n with
  | zero => intro x y; rfl
  | succ n ih =>
    intro x y
    rw [pow_succ, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ih, hg]

theorem IsIsom.inv {g : V ≃ₗ[ZMod 2] V} (hg : IsIsom B g) : IsIsom B g⁻¹ := by
  intro x y
  rw [← hg (g⁻¹ x) (g⁻¹ y), apply_inv_apply, apply_inv_apply]

theorem apply_orbitSum {g : V ≃ₗ[ZMod 2] V} {p : ℕ} (hgp : g ^ p = 1) (v : V) :
    g (∑ i ∈ Finset.range p, (g ^ i) v) = ∑ i ∈ Finset.range p, (g ^ i) v := by
  rw [map_sum]
  have h1 : ∀ i ∈ Finset.range p, g ((g ^ i) v) = (g ^ (i + 1)) v := fun i _ => by
    rw [pow_succ', LinearEquiv.mul_apply]
  rw [Finset.sum_congr rfl h1]
  rcases Nat.eq_zero_or_pos p with h0 | hpos
  · subst h0
    simp
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun i => (g ^ i) v), hgp, pow_zero]

theorem nondeg_inf_fixSp (hBs : ∀ x y, B x y = B y x) {y : V ≃ₗ[ZMod 2] V} (hy : IsIsom B y)
    {p : ℕ} (hp : Odd p) (hyp : y ^ p = 1) {W : Submodule (ZMod 2) V} (hW : Nondeg B W)
    (hyW : ∀ w ∈ W, y w ∈ W) : Nondeg B (W ⊓ fixSp y.toLinearMap) := by
  rw [nondeg_iff] at hW ⊢
  intro w hw hperp
  obtain ⟨hwW, hwy⟩ := Submodule.mem_inf.1 hw
  have hwy' : y w = w := mem_fixSp.1 hwy
  refine hW w hwW fun u hu => ?_
  have hpowW : ∀ i : ℕ, (y ^ i) u ∈ W := by
    intro i
    induction i with
    | zero => simpa using hu
    | succ i ih =>
      rw [pow_succ', LinearEquiv.mul_apply]
      exact hyW _ ih
  have hwi : ∀ i : ℕ, (y ^ i) w = w := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', LinearEquiv.mul_apply, ih, hwy']
  set s := ∑ i ∈ Finset.range p, (y ^ i) u with hs
  have hsW : s ∈ W := Submodule.sum_mem _ fun i _ => hpowW i
  have hsy : s ∈ fixSp y.toLinearMap := mem_fixSp.2 (apply_orbitSum hyp u)
  have h1 : B s w = 0 := hperp s (Submodule.mem_inf.2 ⟨hsW, hsy⟩)
  have h2 : B s w = B u w := by
    rw [hs, map_sum, LinearMap.sum_apply]
    have : ∀ i ∈ Finset.range p, B ((y ^ i) u) w = B u w := fun i _ => by
      conv_lhs => rw [← hwi i]
      exact (hy.pow i) u w
    rw [Finset.sum_congr rfl this, sum_range_odd hp]
  rw [← h2, h1]

theorem pow_apply_eq_self {g : V ≃ₗ[ZMod 2] V} {w : V} (h : g w = w) (n : ℕ) : (g ^ n) w = w := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', LinearEquiv.mul_apply, ih, h]

theorem pow_apply_mem {g : V ≃ₗ[ZMod 2] V} {W : Submodule (ZMod 2) V} (hgW : ∀ w ∈ W, g w ∈ W)
    (n : ℕ) {w : V} (hw : w ∈ W) : (g ^ n) w ∈ W := by
  induction n with
  | zero => simpa using hw
  | succ n ih => rw [pow_succ', LinearEquiv.mul_apply]; exact hgW _ ih

theorem pow_eq_pow_mod {G : Type*} [Monoid G] {c : G} {p : ℕ} (hc : c ^ p = 1) (n : ℕ) :
    c ^ n = c ^ (n % p) := by
  conv_lhs => rw [← Nat.div_add_mod n p, pow_add, pow_mul, hc, one_pow, one_mul]

theorem orbitSum_eq_zero {g : V ≃ₗ[ZMod 2] V} {p : ℕ} (hgp : g ^ p = 1)
    {W : Submodule (ZMod 2) V} (hgW : ∀ w ∈ W, g w ∈ W) (hf : ∀ w ∈ W, g w = w → w = 0)
    {w : V} (hw : w ∈ W) : ∑ i ∈ Finset.range p, (g ^ i) w = 0 :=
  hf _ (Submodule.sum_mem _ fun i _ => pow_apply_mem hgW i hw) (apply_orbitSum hgp w)

theorem fpf_pow {c : V ≃ₗ[ZMod 2] V} {p : ℕ} (hp : p.Prime) (hc : c ^ p = 1)
    {W : Submodule (ZMod 2) V} (hcf : ∀ w ∈ W, c w = w → w = 0) {i : ℕ} (hi : ¬ p ∣ i) :
    ∀ w ∈ W, (c ^ i) w = w → w = 0 := by
  intro w hw hwi
  have hcop : Nat.Coprime i p := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hi)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  apply hcf w hw
  have h1 := pow_apply_eq_self hwi m
  rw [← pow_mul, pow_eq_pow_mod hc, hm, pow_one] at h1
  exact h1

theorem eq_bot_of_fpf_pair {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a c : V ≃ₗ[ZMod 2] V}
    (hac : a * c = c * a) (ha : a ^ p = 1) (hc : c ^ p = 1) {W : Submodule (ZMod 2) V}
    (haW : ∀ w ∈ W, a w ∈ W) (hcW : ∀ w ∈ W, c w ∈ W) (hcf : ∀ w ∈ W, c w = w → w = 0)
    (hacf : ∀ k : ℕ, ∀ w ∈ W, (a * c ^ k) w = w → w = 0) : W = ⊥ := by
  have hpo : Odd p := hp.odd_of_ne_two hp2
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  have hcomm : ∀ k : ℕ, Commute a (c ^ k) := fun k => (Commute.pow_right hac k)
  have hpowk : ∀ k : ℕ, (a * c ^ k) ^ p = 1 := fun k => by
    rw [(hcomm k).mul_pow, ha, ← pow_mul, mul_comm, pow_mul, hc, one_pow, one_mul]
  have hinvk : ∀ k : ℕ, ∀ v ∈ W, (a * c ^ k) v ∈ W := fun k v hv => by
    rw [LinearEquiv.mul_apply]
    exact haW _ (pow_apply_mem hcW k hv)
  have h1 : ∀ k : ℕ, ∑ i ∈ Finset.range p, ((a * c ^ k) ^ i) w = 0 := fun k =>
    orbitSum_eq_zero (hpowk k) (hinvk k) (hacf k) hw
  have h2 : ∀ i ∈ Finset.range p, i ≠ 0 → ∑ k ∈ Finset.range p, (c ^ (k * i)) w = 0 := by
    intro i hi hi0
    have hpi : ¬ p ∣ i := fun h => hi0 (Nat.eq_zero_of_dvd_of_lt h (Finset.mem_range.1 hi))
    have hci : (c ^ i) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hc, one_pow]
    have := orbitSum_eq_zero hci (fun v hv => pow_apply_mem hcW i hv)
      (fpf_pow hp hc hcf hpi) hw
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← pow_mul, mul_comm]
  have h3 : ∑ k ∈ Finset.range p, ∑ i ∈ Finset.range p, ((a * c ^ k) ^ i) w = w := by
    have e1 : ∀ k i : ℕ, ((a * c ^ k) ^ i) w = (a ^ i) ((c ^ (k * i)) w) := fun k i => by
      rw [(hcomm k).mul_pow, ← pow_mul, LinearEquiv.mul_apply]
    simp_rw [e1]
    rw [Finset.sum_comm]
    have e2 : ∀ i ∈ Finset.range p,
        ∑ k ∈ Finset.range p, (a ^ i) ((c ^ (k * i)) w) = if i = 0 then w else 0 := by
      intro i hi
      rw [← map_sum]
      by_cases hi0 : i = 0
      · subst hi0
        simp only [mul_zero, pow_zero, if_true]
        rw [sum_range_odd hpo]
        rfl
      · rw [if_neg hi0, h2 i hi hi0, map_zero]
    rw [Finset.sum_congr rfl e2, Finset.sum_ite_eq' (Finset.range p) 0 (fun _ => w),
      if_pos (Finset.mem_range.2 hp.pos)]
  rw [← h3]
  exact Finset.sum_eq_zero fun k _ => h1 k

@[expose] def commSp (e : V ≃ₗ[ZMod 2] V) : Submodule (ZMod 2) V :=
  LinearMap.range (e.toLinearMap - LinearMap.id)

theorem mem_commSp_iff {e : V ≃ₗ[ZMod 2] V} {w : V} : w ∈ commSp e ↔ ∃ v, e v - v = w := by
  simp [commSp]

theorem pow_sub_mem_commSp (e : V ≃ₗ[ZMod 2] V) (x : V) (i : ℕ) : (e ^ i) x - x ∈ commSp e := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h : (e ^ (i + 1)) x - x = (e ((e ^ i) x) - (e ^ i) x) + ((e ^ i) x - x) := by
      rw [pow_succ', LinearEquiv.mul_apply]
      abel
    rw [h]
    exact Submodule.add_mem _ (mem_commSp_iff.2 ⟨_, rfl⟩) ih

theorem commSp_fpf {e : V ≃ₗ[ZMod 2] V} {p : ℕ} (hp : Odd p) (hep : e ^ p = 1) {w : V}
    (hw : w ∈ commSp e) (hew : e w = w) : w = 0 := by
  obtain ⟨v, rfl⟩ := mem_commSp_iff.1 hw
  have h1 : ∑ i ∈ Finset.range p, (e ^ i) (e v - v) = e v - v := by
    rw [Finset.sum_congr rfl (fun i _ => pow_apply_eq_self hew i), sum_range_odd hp]
  have h2 : ∑ i ∈ Finset.range p, (e ^ i) (e v - v) = 0 := by
    have : ∀ i ∈ Finset.range p, (e ^ i) (e v - v) = (e ^ (i + 1)) v - (e ^ i) v := fun i _ => by
      rw [map_sub, pow_succ, LinearEquiv.mul_apply]
    rw [Finset.sum_congr rfl this, Finset.sum_range_sub (fun i => (e ^ i) v), hep]
    simp
  rw [← h1, h2]

theorem commSp_invariant {e g : V ≃ₗ[ZMod 2] V} (hge : g * e = e * g) {w : V}
    (hw : w ∈ commSp e) : g w ∈ commSp e := by
  obtain ⟨v, rfl⟩ := mem_commSp_iff.1 hw
  refine mem_commSp_iff.2 ⟨g v, ?_⟩
  rw [map_sub, ← LinearEquiv.mul_apply, ← hge, LinearEquiv.mul_apply]

theorem commSp_ne_bot {e : V ≃ₗ[ZMod 2] V} (he : e ≠ 1) : commSp e ≠ ⊥ := by
  intro h
  apply he
  ext v
  have hv : e v - v ∈ commSp e := mem_commSp_iff.2 ⟨v, rfl⟩
  rw [h, Submodule.mem_bot, sub_eq_zero] at hv
  exact hv

theorem nondeg_commSp (hBs : ∀ x y, B x y = B y x) (hB : B.Nondegenerate)
    {e : V ≃ₗ[ZMod 2] V} (he : IsIsom B e) {p : ℕ} (hp : Odd p) (hep : e ^ p = 1) :
    Nondeg B (commSp e) := by
  rw [nondeg_iff]
  intro w hw hperp
  obtain ⟨v, rfl⟩ := mem_commSp_iff.1 hw
  refine hB.2 _ fun x => ?_
  set s := ∑ i ∈ Finset.range p, (e ^ i) x with hs
  have hxs : x - s ∈ commSp e := by
    have : x - s = -∑ i ∈ Finset.range p, ((e ^ i) x - x) := by
      rw [Finset.sum_sub_distrib, sum_range_odd hp x, hs]
      abel
    rw [this]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => pow_sub_mem_commSp e x i)
  have hes : e s = s := apply_orbitSum hep x
  have h1 : B (x - s) (e v - v) = 0 := hperp _ hxs
  have h2 : B s (e v - v) = 0 := by
    rw [map_sub, ← hes, he s v, hes, sub_self]
  have : x = (x - s) + s := by abel
  rw [this, map_add, LinearMap.add_apply, h1, h2, add_zero]

end OddOrder

section Groups

variable {G : Type*} [Group G]

theorem card_sup_of_inf_eq_bot [Finite G] {A C : Subgroup G} (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (hd : A ⊓ C = ⊥) : Nat.card ↥(A ⊔ C) = Nat.card A * Nat.card C := by
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A C hAC).1
  rw [hd, Subgroup.card_bot, mul_one] at h
  exact h

theorem mem_sup_iff_of_commute [Finite G] {A C : Subgroup G}
    (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) {x : G} :
    x ∈ A ⊔ C ↔ ∃ a ∈ A, ∃ c ∈ C, a * c = x := by
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A C hAC).2
  rw [← SetLike.mem_coe, h, Set.mem_mul]
  simp only [SetLike.mem_coe]

theorem card_zpowers_of_prime {g : G} {p : ℕ} (hp : p.Prime) (hg : g ^ p = 1) (hg1 : g ≠ 1) :
    Nat.card (Subgroup.zpowers g) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.card_zpowers, orderOf_eq_prime hg hg1]

theorem zpowers_inf_eq_bot {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {b : G}
    (hbp : b ^ p = 1) {H : Subgroup G} (hb : b ∉ H) : Subgroup.zpowers b ⊓ H = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxb, hxH⟩ := Subgroup.mem_inf.1 hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hb1 : b ≠ 1 := fun h => hb (h ▸ one_mem _)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxb
  have hxp : (b ^ j) ^ p = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hbp, one_zpow]
  have heq : Subgroup.zpowers (b ^ j) = Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxb) (by
      rw [card_zpowers_of_prime hp hbp hb1, card_zpowers_of_prime hp hxp hx1])
  apply hb
  have hbm : b ∈ Subgroup.zpowers (b ^ j) := heq ▸ Subgroup.mem_zpowers b
  exact (Subgroup.zpowers_le.2 hxH) hbm

end Groups

section Structure

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {B : LinearMap.BilinForm (ZMod 2) V}

@[expose] def IsRestrClosed (B : LinearMap.BilinForm (ZMod 2) V)
    (G : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  (∀ g ∈ G, IsIsom B g) ∧
    ∀ g ∈ G, ∀ W : Submodule (ZMod 2) V, Nondeg B W → (∀ w ∈ W, g w ∈ W) →
      ∀ g' : V ≃ₗ[ZMod 2] V, (∀ w ∈ W, g' w = g w) → (∀ x ∈ B.orthogonal W, g' x = x) → g' ∈ G

@[expose] def IsBlock (B : LinearMap.BilinForm (ZMod 2) V) (b : V ≃ₗ[ZMod 2] V)
    (W : Submodule (ZMod 2) V) : Prop :=
  Nondeg B W ∧ W ≠ ⊥ ∧ (∀ w ∈ W, b w ∈ W) ∧ (∀ x ∈ B.orthogonal W, b x = x) ∧
    (∀ w ∈ W, b w = w → w = 0) ∧
    ∀ W' : Submodule (ZMod 2) V, W' ≤ W → W' ≠ ⊥ → Nondeg B W' → (∀ w ∈ W', b w ∈ W') → W' = W

@[expose] def HasBlocks (B : LinearMap.BilinForm (ZMod 2) V) (U : Submodule (ZMod 2) V)
    (E : Subgroup (V ≃ₗ[ZMod 2] V)) (p : ℕ) : Prop :=
  ∃ (r : ℕ) (b : Fin r → V ≃ₗ[ZMod 2] V) (W : Fin r → Submodule (ZMod 2) V),
    (∀ i, b i ∈ E) ∧ (∀ i, IsBlock B (b i) (W i)) ∧ (∀ i, W i ≤ U) ∧
    (∀ i j, i ≠ j → W i ≤ B.orthogonal (W j)) ∧ E = Subgroup.closure (Set.range b) ∧
    Nat.card E = p ^ r

theorem finite_linearEquiv : Finite (V ≃ₗ[ZMod 2] V) := by
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  exact Finite.of_injective (fun g : V ≃ₗ[ZMod 2] V => (g : V → V)) DFunLike.coe_injective

theorem mem_fixSp_equiv {g : V ≃ₗ[ZMod 2] V} {v : V} : v ∈ fixSp g.toLinearMap ↔ g v = v := by
  rw [mem_fixSp]
  rfl

theorem mem_orth_sup_iff {A C : Submodule (ZMod 2) V} {x : V} :
    x ∈ B.orthogonal (A ⊔ C) ↔ x ∈ B.orthogonal A ∧ x ∈ B.orthogonal C := by
  constructor
  · intro h
    exact ⟨fun a ha => h a (Submodule.mem_sup_left ha), fun c hc => h c (Submodule.mem_sup_right hc)⟩
  · rintro ⟨h1, h2⟩ n hn
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hn
    show B (a + c) x = 0
    rw [map_add, LinearMap.add_apply, h1 a ha, h2 c hc, add_zero]

variable (hBs : ∀ x y, B x y = B y x) (hB : B.Nondegenerate)
include hBs hB

theorem orth_inf_orth (U W : Submodule (ZMod 2) V) :
    B.orthogonal (U ⊓ B.orthogonal W) = B.orthogonal U ⊔ W := by
  have : U ⊓ B.orthogonal W = B.orthogonal (B.orthogonal U ⊔ W) := by
    ext x
    rw [Submodule.mem_inf, mem_orth_sup_iff, orth_orth hBs hB]
  rw [this, orth_orth hBs hB]

theorem apply_mem_of_ptw {g : V ≃ₗ[ZMod 2] V} (hg : IsIsom B g) {U : Submodule (ZMod 2) V}
    (hgU : ∀ x ∈ B.orthogonal U, g x = x) {u : V} (hu : u ∈ U) : g u ∈ U := by
  rw [← orth_orth hBs hB U]
  intro x hx
  show B x (g u) = 0
  rw [← hgU x hx, hg x u, hBs]
  exact hx u hu

omit hB in
theorem apply_mem_orth_of_invariant {g : V ≃ₗ[ZMod 2] V} (hg : IsIsom B g)
    {W : Submodule (ZMod 2) V} (hgW : ∀ w ∈ W, g w ∈ W) {x : V} (hx : x ∈ B.orthogonal W) :
    g x ∈ B.orthogonal W := by
  intro w hw
  have hinj : Function.Injective (g.toLinearMap.restrict hgW) := fun a b h =>
    Subtype.ext (g.injective (congrArg Subtype.val h))
  obtain ⟨w', hw'⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨w, hw⟩
  have h1 : g w' = w := congrArg Subtype.val hw'
  show B w (g x) = 0
  rw [← h1, hg]
  exact hx w' w'.2

omit hB in
theorem apply_mem_orth_of_ptw {g : V ≃ₗ[ZMod 2] V} (hg : IsIsom B g)
    {W : Submodule (ZMod 2) V} (hgW : ∀ w ∈ W, g w = w) {x : V} (hx : x ∈ B.orthogonal W) :
    g x ∈ B.orthogonal W :=
  apply_mem_orth_of_invariant hBs hg (fun w hw => (hgW w hw).symm ▸ hw) hx

omit hBs hB in
theorem glueE_pow {W W' : Submodule (ZMod 2) V} (hc : IsCompl W W') (g : V ≃ₗ[ZMod 2] V)
    (hg : ∀ w ∈ W, g w ∈ W) (n : ℕ) :
    (glueE hc g hg ^ n) = glueE hc (g ^ n) (fun w hw => pow_apply_mem hg n hw) := by
  refine linearEquiv_ext_of_isCompl hc (fun w hw => ?_) (fun x hx => ?_)
  · rw [glueE_left hc _ _ hw]
    induction n generalizing w with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, LinearEquiv.mul_apply, glueE_left hc _ _ hw, ih _ (hg w hw), pow_succ,
        LinearEquiv.mul_apply]
  · rw [glueE_right hc _ _ hx]
    exact pow_apply_eq_self (glueE_right hc _ _ hx) n

omit hBs hB in
theorem zpowers_inf_ptw_eq_bot {p : ℕ} (hp : p.Prime) {b : V ≃ₗ[ZMod 2] V} (hbp : b ^ p = 1)
    {W : Submodule (ZMod 2) V} (hb : b ∉ ptw W) : Subgroup.zpowers b ⊓ ptw W = ⊥ :=
  haveI : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  zpowers_inf_eq_bot hp hbp hb

theorem exists_block_step {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hG : IsRestrClosed B G) {U : Submodule (ZMod 2) V} (hU : Nondeg B U)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hEU : E ≤ G ⊓ ptw (B.orthogonal U))
    (hE : IsElemAbelian p E)
    (hmax : ∀ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ G ⊓ ptw (B.orthogonal U) →
      IsElemAbelian p F → Nat.card F ≤ Nat.card E) (hne : E ≠ ⊥) :
    ∃ (b : V ≃ₗ[ZMod 2] V) (W : Submodule (ZMod 2) V), b ∈ E ∧ IsBlock B b W ∧ W ≤ U ∧
      Nondeg B (U ⊓ B.orthogonal W) ∧
      finrank (ZMod 2) ↥(U ⊓ B.orthogonal W) < finrank (ZMod 2) ↥U ∧
      E ⊓ ptw W ≤ G ⊓ ptw (B.orthogonal (U ⊓ B.orthogonal W)) ∧
      (∀ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ G ⊓ ptw (B.orthogonal (U ⊓ B.orthogonal W)) →
        IsElemAbelian p F → Nat.card F ≤ Nat.card ↥(E ⊓ ptw W)) ∧
      E = (E ⊓ ptw W) ⊔ Subgroup.zpowers b ∧ Nat.card E = p * Nat.card ↥(E ⊓ ptw W) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hkey : ∀ k : ℕ, k + k * (p - 1) = p * k := fun k => by
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
    rw [hq, Nat.add_sub_cancel]
    ring
  have hEG : ∀ g ∈ E, g ∈ G := fun g hg => (hEU hg).1
  have hEiso : ∀ g ∈ E, IsIsom B g := fun g hg => hG.1 g (hEG g hg)
  have hEfix : ∀ g ∈ E, ∀ x ∈ B.orthogonal U, g x = x := fun g hg => (hEU hg).2
  have hEp : ∀ g ∈ E, g ^ p = 1 := fun g hg => hE.2 g hg
  have hEc : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g := fun g hg h hh => hE.comm hg hh
  have hEU' : ∀ g ∈ E, ∀ u ∈ U, g u ∈ U := fun g hg u hu =>
    apply_mem_of_ptw hBs hB (hEiso g hg) (hEfix g hg) hu
  have hUc : IsCompl U (B.orthogonal U) := isCompl_of_nondeg hBs hU
  let InS : Submodule (ZMod 2) V → Prop := fun W => W ≤ U ∧ W ≠ ⊥ ∧ Nondeg B W ∧
    (∀ g ∈ E, ∀ w ∈ W, g w ∈ W) ∧ ∀ w ∈ W, (∀ g ∈ E, g w = w) → w = 0
  obtain ⟨e, heE, he1⟩ := (E.bot_or_exists_ne_one).resolve_left hne
  have hS0 : InS (commSp e) := by
    refine ⟨fun w hw => ?_, commSp_ne_bot he1,
      nondeg_commSp hBs hB (hEiso e heE) hpo (hEp e heE),
      fun g hg w hw => commSp_invariant (hEc g hg e heE) hw,
      fun w hw hfix => commSp_fpf hpo (hEp e heE) hw (hfix e heE)⟩
    obtain ⟨v, rfl⟩ := mem_commSp_iff.1 hw
    obtain ⟨u, hu, x, hx, rfl⟩ := exists_add_of_isCompl hUc v
    have : e (u + x) - (u + x) = e u - u := by rw [map_add, hEfix e heE x hx]; abel
    rw [this]
    exact U.sub_mem (hEU' e heE u hu) hu
  have hex : ∃ d, ∃ W, InS W ∧ finrank (ZMod 2) W = d := ⟨_, _, hS0, rfl⟩
  obtain ⟨W, hWS, hWd⟩ := Nat.find_spec hex
  have hmin : ∀ W', InS W' → W' ≤ W → W' = W := fun W' hW' hle =>
    Submodule.eq_of_le_of_finrank_le hle (hWd ▸ Nat.find_min' hex ⟨W', hW', rfl⟩)
  obtain ⟨hWU, hW0, hWnd, hWE, hWC⟩ := hWS
  have hWc : IsCompl W (B.orthogonal W) := isCompl_of_nondeg hBs hWnd
  have hWperpE : ∀ g ∈ E, ∀ x ∈ B.orthogonal W, g x ∈ B.orthogonal W := fun g hg x hx =>
    apply_mem_orth_of_invariant hBs (hEiso g hg) (hWE g hg) hx
  have hA : ∀ g ∈ E, (∃ w ∈ W, g w ≠ w) → ∀ w ∈ W, g w = w → w = 0 := by
    intro g hg hmov
    by_cases h : W ⊓ fixSp g.toLinearMap = ⊥
    · intro w hw hgw
      have hw' : w ∈ W ⊓ fixSp g.toLinearMap := Submodule.mem_inf.2 ⟨hw, mem_fixSp_equiv.2 hgw⟩
      rw [h] at hw'
      exact (Submodule.mem_bot _).1 hw'
    · exfalso
      have hS : InS (W ⊓ fixSp g.toLinearMap) := by
        refine ⟨inf_le_left.trans hWU, h,
          nondeg_inf_fixSp hBs (hEiso g hg) hpo (hEp g hg) hWnd (hWE g hg), ?_, ?_⟩
        · intro g' hg' w hw
          obtain ⟨hwW, hwg⟩ := Submodule.mem_inf.1 hw
          refine Submodule.mem_inf.2 ⟨hWE g' hg' w hwW, mem_fixSp_equiv.2 ?_⟩
          have : g (g' w) = g' (g w) := by
            rw [← LinearEquiv.mul_apply, hEc g hg g' hg', LinearEquiv.mul_apply]
          rw [this, mem_fixSp_equiv.1 hwg]
        · intro w hw hfix
          exact hWC w (Submodule.mem_inf.1 hw).1 hfix
      have heq := hmin _ hS inf_le_left
      obtain ⟨w, hw, hgw⟩ := hmov
      apply hgw
      have hw' : w ∈ W ⊓ fixSp g.toLinearMap := heq.symm ▸ hw
      exact mem_fixSp_equiv.1 (Submodule.mem_inf.1 hw').2
  have hmove : ∃ e₀ ∈ E, ∃ w ∈ W, e₀ w ≠ w := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    exact hw0 (hWC w hw fun g hg => hcon g hg w hw)
  have hB' : ∀ e₁ ∈ E, (∃ w ∈ W, e₁ w ≠ w) → ∀ g ∈ E, ∃ k : ℕ, ∀ w ∈ W, g w = (e₁ ^ k) w := by
    intro e₁ he₁ hmov₁ g hg
    by_contra hcon
    push Not at hcon
    apply hW0
    refine eq_bot_of_fpf_pair hp hp2 (hEc g hg e₁ he₁) (hEp g hg) (hEp e₁ he₁) (hWE g hg)
      (hWE e₁ he₁) (hA e₁ he₁ hmov₁) fun k => ?_
    have hgk : g * e₁ ^ k ∈ E := mul_mem hg (pow_mem he₁ k)
    refine hA _ hgk ?_
    by_contra hcon'
    push Not at hcon'
    obtain ⟨w, hw, hne⟩ := hcon (k * (p - 1))
    apply hne
    have h1 : (e₁ ^ k) ((e₁ ^ (k * (p - 1))) w) = w := by
      rw [← LinearEquiv.mul_apply, ← pow_add, hkey k, pow_mul, hEp e₁ he₁, one_pow]
      rfl
    have h2 := hcon' ((e₁ ^ (k * (p - 1))) w) (pow_apply_mem (hWE e₁ he₁) (k * (p - 1)) hw)
    rw [LinearEquiv.mul_apply, h1] at h2
    exact h2
  set K := E ⊓ ptw W with hK
  have hKE : K ≤ E := inf_le_left
  have hdecomp : ∀ e₁ ∈ E, (∃ w ∈ W, e₁ w ≠ w) →
      E = K ⊔ Subgroup.zpowers e₁ ∧ Nat.card E = p * Nat.card K := by
    intro e₁ he₁ hmov₁
    have he₁W : e₁ ∉ ptw W := fun h => by
      obtain ⟨w, hw, hne⟩ := hmov₁
      exact hne (h w hw)
    have he₁1 : e₁ ≠ 1 := fun h => he₁W (h ▸ one_mem _)
    have hEq : E = K ⊔ Subgroup.zpowers e₁ := by
      refine le_antisymm (fun g hg => ?_) (sup_le hKE (Subgroup.zpowers_le.2 he₁))
      obtain ⟨k, hk⟩ := hB' e₁ he₁ hmov₁ g hg
      have hgK : g * e₁ ^ (k * (p - 1)) ∈ K := by
        refine Subgroup.mem_inf.2 ⟨mul_mem hg (pow_mem he₁ _), fun w hw => ?_⟩
        rw [LinearEquiv.mul_apply, hk _ (pow_apply_mem (hWE e₁ he₁) _ hw),
          ← LinearEquiv.mul_apply, ← pow_add, hkey k, pow_mul, hEp e₁ he₁, one_pow]
        rfl
      have : g = g * e₁ ^ (k * (p - 1)) * e₁ ^ k := by
        rw [mul_assoc, ← pow_add, add_comm, hkey k, pow_mul, hEp e₁ he₁, one_pow, mul_one]
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left hgK)
        (Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers e₁) k))
    refine ⟨hEq, ?_⟩
    have hcomm : ∀ a ∈ K, ∀ c ∈ Subgroup.zpowers e₁, a * c = c * a := fun a ha c hc =>
      hEc a (hKE ha) c (Subgroup.zpowers_le.2 he₁ hc)
    have hinf : K ⊓ Subgroup.zpowers e₁ = ⊥ := by
      rw [eq_bot_iff, ← zpowers_inf_ptw_eq_bot hp (hEp e₁ he₁) he₁W]
      intro x hx
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2,
        (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2⟩
    conv_lhs => rw [hEq]
    rw [card_sup_of_inf_eq_bot hcomm hinf, card_zpowers_of_prime hp (hEp e₁ he₁) he₁1, mul_comm]
  obtain ⟨e₀, he₀E, hmov₀⟩ := hmove
  have he₀W : e₀ ∉ ptw W := fun h => by
    obtain ⟨w, hw, hne⟩ := hmov₀
    exact hne (h w hw)
  have hcardE : Nat.card E = p * Nat.card K := (hdecomp e₀ he₀E hmov₀).2
  have hD : ∃ b ∈ E, b ≠ 1 ∧ ∀ x ∈ B.orthogonal W, b x = x := by
    by_contra hcon
    push Not at hcon
    let ρ : ↥E →* (V ≃ₗ[ZMod 2] V) :=
      { toFun := fun g => glueE hWc.symm g.1 (hWperpE g.1 g.2)
        map_one' := by
          refine linearEquiv_ext_of_isCompl hWc (fun w hw => ?_) (fun x hx => ?_)
          · rw [glueE_right hWc.symm _ _ hw]; rfl
          · rw [glueE_left hWc.symm _ _ hx]; rfl
        map_mul' := fun g h => by
          refine linearEquiv_ext_of_isCompl hWc (fun w hw => ?_) (fun x hx => ?_)
          · rw [LinearEquiv.mul_apply, glueE_right hWc.symm _ _ hw, glueE_right hWc.symm _ _ hw,
              glueE_right hWc.symm _ _ hw]
          · rw [LinearEquiv.mul_apply, glueE_left hWc.symm (h : V ≃ₗ[ZMod 2] V) _ hx,
              glueE_left hWc.symm (g : V ≃ₗ[ZMod 2] V) _ (hWperpE h.1 h.2 x hx),
              glueE_left hWc.symm _ (hWperpE (g * h).1 (g * h).2) hx]
            rfl }
    have hρapp : ∀ (g : ↥E) (x : V), x ∈ B.orthogonal W → ρ g x = g.1 x := fun g x hx =>
      glueE_left hWc.symm g.1 (hWperpE g.1 g.2) hx
    have hρappW : ∀ (g : ↥E) (w : V), w ∈ W → ρ g w = w := fun g w hw =>
      glueE_right hWc.symm g.1 (hWperpE g.1 g.2) hw
    have hρinj : Function.Injective ρ := by
      rw [injective_iff_map_eq_one]
      intro g hg
      by_contra hg1
      have hg1' : (g : V ≃ₗ[ZMod 2] V) ≠ 1 := fun h => hg1 (Subtype.ext h)
      obtain ⟨x, hx, hne⟩ := hcon g.1 g.2 hg1'
      apply hne
      rw [← hρapp g x hx, hg]
      rfl
    set c := glueE hWc e₀ (hWE e₀ he₀E) with hc
    have hcW : ∀ w ∈ W, c w = e₀ w := fun w hw => glueE_left hWc _ _ hw
    have hcW' : ∀ x ∈ B.orthogonal W, c x = x := fun x hx => glueE_right hWc _ _ hx
    have hcp : c ^ p = 1 := by
      rw [hc, glueE_pow]
      refine linearEquiv_ext_of_isCompl hWc (fun w hw => ?_) (fun x hx => ?_)
      · rw [glueE_left hWc _ _ hw, hEp e₀ he₀E]
      · rw [glueE_right hWc _ _ hx]; rfl
    have hcptw : c ∉ ptw W := fun h => by
      obtain ⟨w, hw, hne⟩ := hmov₀
      exact hne ((hcW w hw).symm.trans (h w hw))
    have hc1 : c ≠ 1 := fun h => hcptw (h ▸ one_mem _)
    have hUW : B.orthogonal U ≤ B.orthogonal W :=
      LinearMap.BilinForm.orthogonal_le hWU
    have hρG : ρ.range ≤ G ⊓ ptw (B.orthogonal U) := by
      rintro _ ⟨g, rfl⟩
      refine Subgroup.mem_inf.2 ⟨?_, fun x hx => ?_⟩
      · refine hG.2 g.1 (hEG _ g.2) (B.orthogonal W) (nondeg_orth hBs hB hWnd)
          (hWperpE g.1 g.2) (ρ g) (fun x hx => hρapp g x hx) (fun w hw => ?_)
        rw [orth_orth hBs hB] at hw
        exact hρappW g w hw
      · rw [hρapp g x (hUW hx)]
        exact hEfix _ g.2 x hx
    have hcG : c ∈ G ⊓ ptw (B.orthogonal U) := by
      refine Subgroup.mem_inf.2 ⟨hG.2 e₀ (hEG e₀ he₀E) W hWnd (hWE e₀ he₀E) c hcW hcW',
        fun x hx => hcW' x (hUW hx)⟩
    have hcomm : ∀ a ∈ ρ.range, ∀ d ∈ Subgroup.zpowers c, a * d = d * a := by
      rintro _ ⟨g, rfl⟩ d hd
      have h1 : ρ g * c = c * ρ g := by
        refine linearEquiv_ext_of_isCompl hWc (fun w hw => ?_) (fun x hx => ?_)
        · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hcW w hw,
            hρappW g _ (hWE e₀ he₀E w hw), hρappW g w hw, hcW w hw]
        · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hcW' x hx, hρapp g x hx,
            hcW' _ (hWperpE g.1 g.2 x hx)]
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
      exact ((Commute.zpow_right h1) j).eq
    have hrangeEA : IsElemAbelian p ρ.range := by
      refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
      · obtain ⟨g, hg⟩ := x.2
        obtain ⟨h, hh⟩ := y.2
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hg, ← hh, ← map_mul, ← map_mul]
        exact congrArg ρ (Subtype.ext (hEc _ g.2 _ h.2))
      · obtain ⟨g, rfl⟩ := hx
        rw [← map_pow]
        have : g ^ p = 1 := Subtype.ext (hEp _ g.2)
        rw [this, map_one]
    have hFEA : IsElemAbelian p (ρ.range ⊔ Subgroup.zpowers c) :=
      IsElemAbelian.sup_of_commute hrangeEA (isElemAbelian_zpowers hcp) hcomm
    have hFG : ρ.range ⊔ Subgroup.zpowers c ≤ G ⊓ ptw (B.orthogonal U) :=
      sup_le hρG (Subgroup.zpowers_le.2 hcG)
    have hinf : ρ.range ⊓ Subgroup.zpowers c = ⊥ := by
      rw [eq_bot_iff, ← zpowers_inf_ptw_eq_bot hp hcp hcptw]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨g, rfl⟩ := hx1
      exact Subgroup.mem_inf.2 ⟨hx2, fun w hw => hρappW g w hw⟩
    have hcardF : Nat.card ↥(ρ.range ⊔ Subgroup.zpowers c) = Nat.card E * p := by
      rw [card_sup_of_inf_eq_bot hcomm hinf, card_zpowers_of_prime hp hcp hc1,
        ← Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv]
    have h1 := hmax _ hFG hFEA
    rw [hcardF] at h1
    have h2 : 0 < Nat.card E := Nat.card_pos
    have h3 := hp.two_le
    nlinarith
  obtain ⟨b, hbE, hb1, hbW⟩ := hD
  have hbmov : ∃ w ∈ W, b w ≠ w := by
    by_contra hcon
    push Not at hcon
    exact hb1 (linearEquiv_ext_of_isCompl hWc (fun w hw => hcon w hw) (fun x hx => hbW x hx))
  have hbfpf := hA b hbE hbmov
  obtain ⟨hEeq, hcardE'⟩ := hdecomp b hbE hbmov
  have hbW' : b ∉ ptw W := fun h => by
    obtain ⟨w, hw, hne⟩ := hbmov
    exact hne (h w hw)
  have hblock : IsBlock B b W := by
    refine ⟨hWnd, hW0, hWE b hbE, hbW, hbfpf, fun W' hle hW'0 hW'nd hW'b => ?_⟩
    refine hmin W' ⟨hle.trans hWU, hW'0, hW'nd, fun g hg w hw => ?_,
      fun w hw hfix => hWC w (hle hw) hfix⟩ hle
    obtain ⟨k, hk⟩ := hB' b hbE hbmov g hg
    rw [hk w (hle hw)]
    exact pow_apply_mem hW'b k hw
  have hU'nd : Nondeg B (U ⊓ B.orthogonal W) := by
    rw [nondeg_iff]
    intro x hx hperp
    have hx' : x ∈ B.orthogonal (U ⊓ B.orthogonal W) := hperp
    rw [orth_inf_orth hBs hB] at hx'
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
    obtain ⟨hxU, hxW⟩ := Submodule.mem_inf.1 hx
    have hyU : y ∈ U := by
      have := U.sub_mem hxU (hWU hw)
      simpa using this
    have hy0 : y = 0 := (Submodule.disjoint_def.1 hU) y hyU hy
    subst hy0
    rw [zero_add] at hxW ⊢
    exact (Submodule.disjoint_def.1 hWnd) w hw hxW
  have hU'lt : finrank (ZMod 2) ↥(U ⊓ B.orthogonal W) < finrank (ZMod 2) ↥U := by
    refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left fun h => hW0 ?_)
    rw [eq_bot_iff]
    intro w hw
    have hwU' : w ∈ U ⊓ B.orthogonal W := by rw [h]; exact hWU hw
    exact (Submodule.disjoint_def.1 hWnd) w hw (Submodule.mem_inf.1 hwU').2
  have hU'perp := orth_inf_orth hBs hB U W
  have hKsupp : K ≤ G ⊓ ptw (B.orthogonal (U ⊓ B.orthogonal W)) := by
    intro g hg
    obtain ⟨hgE, hgW⟩ := Subgroup.mem_inf.1 hg
    refine Subgroup.mem_inf.2 ⟨hEG g hgE, fun x hx => ?_⟩
    rw [hU'perp] at hx
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, hEfix g hgE y hy, hgW w hw]
  have hKmax : ∀ F : Subgroup (V ≃ₗ[ZMod 2] V),
      F ≤ G ⊓ ptw (B.orthogonal (U ⊓ B.orthogonal W)) → IsElemAbelian p F →
        Nat.card F ≤ Nat.card ↥K := by
    intro F hF hFea
    have hFW : ∀ f ∈ F, ∀ w ∈ W, f w = w := fun f hf w hw =>
      (hF hf).2 w (hU'perp ▸ Submodule.mem_sup_right hw)
    have hFU : ∀ f ∈ F, ∀ x ∈ B.orthogonal U, f x = x := fun f hf x hx =>
      (hF hf).2 x (hU'perp ▸ Submodule.mem_sup_left hx)
    have hcomm : ∀ f ∈ F, ∀ d ∈ Subgroup.zpowers b, f * d = d * f := by
      intro f hf d hd
      have hfiso : IsIsom B f := hG.1 f (hF hf).1
      have h1 : f * b = b * f := by
        refine linearEquiv_ext_of_isCompl hWc (fun w hw => ?_) (fun x hx => ?_)
        · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hFW f hf _ (hWE b hbE w hw),
            hFW f hf w hw]
        · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hbW x hx,
            hbW _ (apply_mem_orth_of_ptw hBs hfiso (hFW f hf) hx)]
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
      exact ((Commute.zpow_right h1) j).eq
    have hinf : F ⊓ Subgroup.zpowers b = ⊥ := by
      rw [eq_bot_iff, ← zpowers_inf_ptw_eq_bot hp (hEp b hbE) hbW']
      intro x hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
      exact Subgroup.mem_inf.2 ⟨hx2, hFW x hx1⟩
    have hle : F ⊔ Subgroup.zpowers b ≤ G ⊓ ptw (B.orthogonal U) :=
      sup_le (fun f hf => Subgroup.mem_inf.2 ⟨(hF hf).1, hFU f hf⟩)
        (Subgroup.zpowers_le.2 (hEU hbE))
    have hea := IsElemAbelian.sup_of_commute hFea (isElemAbelian_zpowers (hEp b hbE)) hcomm
    have h1 := hmax _ hle hea
    rw [card_sup_of_inf_eq_bot hcomm hinf, card_zpowers_of_prime hp (hEp b hbE) hb1,
      hcardE] at h1
    rw [mul_comm] at h1
    exact Nat.le_of_mul_le_mul_left h1 hp.pos
  exact ⟨b, W, hbE, hblock, hWU, hU'nd, hU'lt, hKsupp, hKmax, hEeq, hcardE'⟩

theorem hasBlocks_of_max {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hG : IsRestrClosed B G) :
    ∀ (n : ℕ) (U : Submodule (ZMod 2) V), finrank (ZMod 2) U = n → Nondeg B U →
      ∀ E : Subgroup (V ≃ₗ[ZMod 2] V), E ≤ G ⊓ ptw (B.orthogonal U) → IsElemAbelian p E →
      (∀ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ G ⊓ ptw (B.orthogonal U) → IsElemAbelian p F →
        Nat.card F ≤ Nat.card E) →
      HasBlocks B U E p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U hn hU E hEU hE hmax
  by_cases hne : E = ⊥
  · refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, ?_, ?_⟩
    · rw [hne, Set.range_eq_empty, Subgroup.closure_empty]
    · rw [hne, Subgroup.card_bot, pow_zero]
  obtain ⟨b, W, hbE, hblock, hWU, hU'nd, hU'lt, hKsupp, hKmax, hEeq, hcard⟩ :=
    exists_block_step hBs hB hp hp2 hG hU hEU hE hmax hne
  obtain ⟨r, b', W', hb'K, hblocks', hW'U', horth', hKcl, hKcard⟩ :=
    ih _ (hn ▸ hU'lt) _ rfl hU'nd _ hKsupp (hE.mono inf_le_left) hKmax
  refine ⟨r + 1, (Fin.cons b b' : Fin (r + 1) → V ≃ₗ[ZMod 2] V),
    (Fin.cons W W' : Fin (r + 1) → Submodule (ZMod 2) V), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hbE
    · exact (Subgroup.mem_inf.1 (hb'K i)).1
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hblock
    · exact hblocks' i
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hWU
    · exact (hW'U' i).trans inf_le_left
  · have h0j : ∀ j, W ≤ B.orthogonal (W' j) := fun j w hw x hx => by
      rw [hBs]
      exact (inf_le_right : U ⊓ B.orthogonal W ≤ B.orthogonal W) (hW'U' j hx) w hw
    have hi0 : ∀ i, W' i ≤ B.orthogonal W := fun i => (hW'U' i).trans inf_le_right
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ j => exact h0j j
    | succ i =>
      induction j using Fin.cases with
      | zero => exact hi0 i
      | succ j => exact horth' i j fun h => hij (by rw [h])
  · rw [Fin.range_cons, Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← hKcl, sup_comm]
    exact hEeq
  · rw [hcard, hKcard, pow_succ']

omit hBs hB in
theorem linearIndependent_sigma_of_orth {r : ℕ} {W : Fin r → Submodule (ZMod 2) V}
    (hWnd : ∀ i, Nondeg B (W i)) (horth : ∀ i j, i ≠ j → W i ≤ B.orthogonal (W j))
    {d : Fin r → ℕ} {u : ∀ i, Fin (d i) → V} (hu : ∀ i, LinearIndependent (ZMod 2) (u i))
    (hmem : ∀ i j, u i j ∈ W i) :
    LinearIndependent (ZMod 2) (fun x : (Σ i, Fin (d i)) => u x.1 x.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc x
  rw [Fintype.sum_sigma] at hc
  have hsmem : ∀ i, ∑ j, c ⟨i, j⟩ • u i j ∈ W i := fun i =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmem i j)
  have hs : ∀ i₀, ∑ j, c ⟨i₀, j⟩ • u i₀ j = 0 := by
    intro i₀
    refine (Submodule.disjoint_def.1 (hWnd i₀)) _ (hsmem i₀) ?_
    intro w hw
    have h0 : B w (∑ i, ∑ j, c ⟨i, j⟩ • u i j) = 0 := by rw [hc, map_zero]
    rw [map_sum, Finset.sum_eq_single i₀] at h0
    · exact h0
    · intro i _ hi
      exact horth i i₀ hi (hsmem i) w hw
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  obtain ⟨i, j⟩ := x
  exact (Fintype.linearIndependent_iff.1 (hu i)) (fun j => c ⟨i, j⟩) (hs i) j

end Structure

section Poly

open Polynomial

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem aeval_apply_of_fixed {y : V ≃ₗ[ZMod 2] V} {x : V} (hx : y x = x) (f : (ZMod 2)[X]) :
    aeval y.toLinearMap f x = f.eval 1 • x := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add, LinearMap.add_apply, hf, hg, eval_add, add_smul]
  | monomial n c =>
    rw [aeval_monomial, eval_monomial, one_pow, mul_one, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.End.pow_apply]
    congr 1
    exact Function.iterate_fixed hx n

theorem aeval_mem_of_invariant {y : V →ₗ[ZMod 2] V} {W : Submodule (ZMod 2) V}
    (hW : ∀ w ∈ W, y w ∈ W) (f : (ZMod 2)[X]) {w : V} (hw : w ∈ W) : aeval y f w ∈ W := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add, LinearMap.add_apply]; exact W.add_mem hf hg
  | monomial n c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Module.End.pow_apply]
    refine W.smul_mem c ?_
    induction n with
    | zero => simpa using hw
    | succ n ih => rw [Function.iterate_succ_apply']; exact hW _ ih

theorem mem_of_aeval_eq_zero {W W' : Submodule (ZMod 2) V} (hc : IsCompl W W')
    {y : V ≃ₗ[ZMod 2] V} (hyW : ∀ w ∈ W, y w ∈ W) (hyW' : ∀ x ∈ W', y x = x)
    {f : (ZMod 2)[X]} (hf : f.eval 1 ≠ 0) {v : V} (hv : aeval y.toLinearMap f v = 0) : v ∈ W := by
  obtain ⟨w, hw, x, hx, rfl⟩ := exists_add_of_isCompl hc v
  rw [map_add, aeval_apply_of_fixed (hyW' x hx)] at hv
  have h1 : f.eval 1 • x = -aeval y.toLinearMap f w := eq_neg_of_add_eq_zero_right hv
  have h2 : f.eval 1 • x ∈ W := h1 ▸ W.neg_mem (aeval_mem_of_invariant hyW f hw)
  have h3 : f.eval 1 • x = 0 := (Submodule.disjoint_def.1 hc.disjoint) _ h2 (W'.smul_mem _ hx)
  rw [smul_eq_zero] at h3
  rcases h3 with h3 | h3
  · exact absurd h3 hf
  · rw [h3, add_zero]; exact hw

theorem eval_one_ne_zero {h : (ZMod 2)[X]} (hirr : Irreducible h) (hmon : h.Monic)
    (hne : h ≠ X - 1) : h.eval 1 ≠ 0 := by
  intro h1
  have hdvd : X - C 1 ∣ h := Polynomial.dvd_iff_isRoot.2 h1
  have := eq_of_monic_of_associated (monic_X_sub_C 1) hmon
    ((Polynomial.irreducible_X_sub_C (1 : ZMod 2)).associated_of_dvd hirr hdvd)
  apply hne
  rw [← this, map_one]

theorem symm_mem_of_invariant [FiniteDimensional (ZMod 2) V] {y : V ≃ₗ[ZMod 2] V}
    {W : Submodule (ZMod 2) V} (hyW : ∀ w ∈ W, y w ∈ W) {w : V} (hw : w ∈ W) : y.symm w ∈ W := by
  have hinj : Function.Injective (y.toLinearMap.restrict hyW) := fun a b h =>
    Subtype.ext (y.injective (congrArg Subtype.val h))
  obtain ⟨w', hw'⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨w, hw⟩
  have h1 : y w' = w := congrArg Subtype.val hw'
  rw [← h1, LinearEquiv.symm_apply_apply]
  exact w'.2

end Poly

section Orth

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem polarBilin_symm (Q : QuadraticForm (ZMod 2) V) :
    ∀ x y, polarBilin Q x y = polarBilin Q y x := fun x y => polar_comm Q x y

theorem isIsom_of_mem {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    IsIsom (polarBilin Q) g := fun x y =>
  TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg x y

theorem isRestrClosed_orthogonalGroup (Q : QuadraticForm (ZMod 2) V) :
    IsRestrClosed (polarBilin Q) (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  refine ⟨fun g hg => isIsom_of_mem hg, fun g hg W hW hgW g' h1 h2 => ?_⟩
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  obtain ⟨w, hw, x, hx, rfl⟩ := exists_add_of_isCompl (isCompl_of_nondeg (polarBilin_symm Q) hW) v
  have e1 : polar Q (g w) x = 0 := hx (g w) (hgW w hw)
  have e2 : polar Q w x = 0 := hx w hw
  rw [map_add, h1 w hw, h2 x hx, QuadraticMap.map_add Q, QuadraticMap.map_add Q,
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg, e1, e2]

theorem natCast_odd_ne_zero {p : ℕ} (hp : Odd p) : (p : ZMod 2) ≠ 0 := by
  obtain ⟨k, rfl⟩ := hp
  have h2 : (2 : ZMod 2) = 0 := rfl
  push_cast
  rw [h2, zero_mul, zero_add]
  exact one_ne_zero

theorem oddOrderIsometry_of (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : Odd p)
    {b : V ≃ₗ[ZMod 2] V} (hb : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hbp : b ^ p = 1) :
    OddOrderIsometry Q p b :=
  ⟨hb, hbp, natCast_odd_ne_zero hp, fun v hv => hQ.1 v fun w => hv w⟩

theorem exists_factor_of_block (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : Odd p)
    {b : V ≃ₗ[ZMod 2] V} (hb : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hbp : b ^ p = 1)
    {W : Submodule (ZMod 2) V} (hW : IsBlock (polarBilin Q) b W) :
    ∃ h ∈ primaryFactors b.toLinearMap, h ≠ X - 1 ∧ orbitSpace b.toLinearMap h = W := by
  classical
  have hx := oddOrderIsometry_of hQ hp hb hbp
  obtain ⟨hWnd, hW0, hbW, hbW', hbf, hmin⟩ := hW
  have hWc := isCompl_of_nondeg (polarBilin_symm Q) hWnd
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hsum := congrArg (fun f : Module.End (ZMod 2) V => f w)
    (sum_primaryProjection (x := b.toLinearMap) hx.squarefree_minpoly)
  simp only [LinearMap.sum_apply, Module.End.one_apply] at hsum
  obtain ⟨h, hh, hπ⟩ : ∃ h ∈ primaryFactors b.toLinearMap,
      primaryProjection b.toLinearMap h w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Finset.sum_eq_zero hcon] at hsum
    exact hw0 hsum.symm
  have hπW : primaryProjection b.toLinearMap h w ∈ W :=
    aeval_mem_of_invariant (fun v hv => hbW v hv) _ hw
  have hπh := primaryProjection_mem hx.squarefree_minpoly hh w
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  have hne1 : h ≠ X - 1 := by
    rintro rfl
    apply hπ
    refine hbf _ hπW ?_
    have := mem_primaryComponent.1 hπh
    rw [map_sub, aeval_X, map_one, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have h0 := hx.coeff_zero_ne hh
  have hle1 : primaryComponent b.toLinearMap h ≤ W := fun v hv =>
    mem_of_aeval_eq_zero hWc (fun u hu => hbW u hu) hbW' (eval_one_ne_zero hirr hmon hne1)
      (mem_primaryComponent.1 hv)
  have hle2 : primaryComponent b.toLinearMap (reciprocalPolynomial h) ≤ W := fun v hv =>
    mem_of_aeval_eq_zero hWc (fun u hu => symm_mem_of_invariant hbW hu)
      (fun x hx' => by rw [← hbW' x hx', LinearEquiv.symm_apply_apply, hbW' x hx'])
      (eval_one_ne_zero hirr hmon hne1) ((mem_primaryComponent_reciprocalPolynomial h0).1 hv)
  refine ⟨h, hh, hne1, hmin _ (sup_le hle1 hle2) ?_ ?_ ?_⟩
  · intro hbot
    apply primaryComponent_ne_bot hx.squarefree_minpoly hh
    exact eq_bot_iff.2 (hbot ▸ le_sup_left)
  · rw [nondeg_iff]
    intro u hu hperp
    exact hx.eq_zero_of_polar_orbit hh hu fun v hv => by rw [polar_comm]; exact hperp v hv
  · intro u hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.1 hu
    rw [map_add]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (apply_mem_primaryComponent (Commute.refl _) hu₁))
      (Submodule.mem_sup_right (apply_mem_primaryComponent (Commute.refl _) hu₂))

theorem mem_primaryFactors_of_ne_bot' {x : Module.End (ZMod 2) V} {h : (ZMod 2)[X]}
    (hirr : Irreducible h) (hmon : h.Monic) (hne : primaryComponent x h ≠ ⊥) :
    h ∈ primaryFactors x := by
  rw [mem_primaryFactors]
  refine ⟨hirr, hmon, ?_⟩
  by_contra hdvd
  have hcop : IsCoprime h (minpoly (ZMod 2) x) := (Irreducible.coprime_iff_not_dvd hirr).mpr hdvd
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : aeval x u * aeval x h = 1 := by
    have := congrArg (aeval x) huv
    simpa [minpoly.aeval] using this
  apply hne
  rw [eq_bot_iff]
  intro w hw
  rw [mem_primaryComponent] at hw
  rw [Submodule.mem_bot]
  have h2 : (aeval x u * aeval x h) w = w := by rw [h1]; rfl
  rw [Module.End.mul_apply, hw, map_zero] at h2
  exact h2.symm

theorem aeval_pow_eq_zero {y : Module.End (ZMod 2) V} {h₁ h₂ : (ZMod 2)[X]} {k : ℕ}
    (hdvd : h₂ ∣ h₁.comp (X ^ k)) {v : V} (hv : aeval y h₂ v = 0) : aeval (y ^ k) h₁ v = 0 := by
  obtain ⟨q, hq⟩ := hdvd
  have : aeval (y ^ k) h₁ = aeval y (h₁.comp (X ^ k)) := by
    rw [Polynomial.aeval_comp, map_pow, aeval_X]
  rw [this, hq, mul_comm, map_mul, Module.End.mul_apply, hv, map_zero]

theorem symm_pow (b : V ≃ₗ[ZMod 2] V) (k : ℕ) : (b ^ k).symm = b.symm ^ k := by
  show (b ^ k)⁻¹ = b⁻¹ ^ k
  exact (inv_pow b k).symm

theorem isBlock_pow {B : LinearMap.BilinForm (ZMod 2) V} {p : ℕ} (hp : p.Prime)
    {b : V ≃ₗ[ZMod 2] V} (hbp : b ^ p = 1) {W : Submodule (ZMod 2) V} (hW : IsBlock B b W)
    {k : ℕ} (hk : ¬ p ∣ k) : IsBlock B (b ^ k) W := by
  obtain ⟨hWnd, hW0, hbW, hbW', hbf, hmin⟩ := hW
  have hcop : Nat.Coprime k p := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hk)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hb : b = (b ^ k) ^ m := by
    rw [← pow_mul, pow_eq_pow_mod hbp (k * m), hm, pow_one]
  refine ⟨hWnd, hW0, fun w hw => pow_apply_mem hbW k hw,
    fun x hx => pow_apply_eq_self (hbW' x hx) k, fpf_pow hp hbp hbf hk,
    fun W' hle hW'0 hW'nd hW'b => hmin W' hle hW'0 hW'nd fun w hw => ?_⟩
  rw [hb]
  exact pow_apply_mem hW'b m hw

theorem exists_pow_factor (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {b₁ b₂ : V ≃ₗ[ZMod 2] V} (hb₁ : b₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hb₁p : b₁ ^ p = 1) (hb₂ : b₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hb₂p : b₂ ^ p = 1)
    {h₁ h₂ : (ZMod 2)[X]} (hh₁ : h₁ ∈ primaryFactors b₁.toLinearMap) (hne₁ : h₁ ≠ X - 1)
    (hh₂ : h₂ ∈ primaryFactors b₂.toLinearMap) (hne₂ : h₂ ≠ X - 1)
    {W₂ : Submodule (ZMod 2) V} (hW₂ : IsBlock (polarBilin Q) b₂ W₂)
    (hO₂ : orbitSpace b₂.toLinearMap h₂ = W₂) :
    ∃ k : ℕ, 0 < k ∧ k < p ∧ h₁ ∈ primaryFactors (b₂ ^ k).toLinearMap ∧
      orbitSpace (b₂ ^ k).toLinearMap h₁ = W₂ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpo := hp.odd_of_ne_two hp2
  have hx₁ := oddOrderIsometry_of hQ hpo hb₁ hb₁p
  have hx₂ := oddOrderIsometry_of hQ hpo hb₂ hb₂p
  have hirr₁ := irreducible_of_mem_primaryFactors hh₁
  have hirr₂ := irreducible_of_mem_primaryFactors hh₂
  have hmon₁ := monic_of_mem_primaryFactors hh₁
  have hmon₂ := monic_of_mem_primaryFactors hh₂
  haveI : Fact (Irreducible h₂) := ⟨hirr₂⟩
  set lam := AdjoinRoot.root h₂ with hlam
  have hlp : lam ^ p = 1 := root_pow_eq_one (hx₂.dvd_X_pow_sub_one hh₂)
  have hl1 : lam ≠ 1 := root_ne_one hmon₂ hne₂
  have hprim : IsPrimitiveRoot lam p := IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime hlp hl1)
  have hdvd₁ : h₁ ∣ (X ^ p - 1 : (ZMod 2)[X]) := hx₁.dvd_X_pow_sub_one hh₁
  set f := algebraMap (ZMod 2) (AdjoinRoot h₂) with hf
  have hsplit : (h₁.map f).Splits := by
    refine (X_pow_sub_one_splits hprim).of_dvd (X_pow_sub_C_ne_zero hp.pos 1) ?_
    have := Polynomial.map_dvd f hdvd₁
    simpa using this
  have hdeg : (h₁.map f).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    exact (Polynomial.degree_pos_of_irreducible hirr₁).ne'
  obtain ⟨ρ, hρ⟩ := hsplit.exists_eval_eq_zero hdeg
  have hρ' : aeval ρ h₁ = 0 := by rw [aeval_def, ← eval_map]; exact hρ
  have hρp : ρ ^ p = 1 := by
    obtain ⟨q, hq⟩ := hdvd₁
    have := congrArg (aeval ρ) hq
    rw [map_mul, hρ', zero_mul, map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at this
    exact this
  obtain ⟨k, hkp, hk⟩ := hprim.eq_pow_of_pow_eq_one hρp
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    apply eval_one_ne_zero hirr₁ hmon₁ hne₁
    have h1 : f (h₁.eval 1) = 0 := by
      rw [← Polynomial.eval₂_at_one, ← eval_map, hk]
      exact hρ
    exact (map_eq_zero_iff f f.injective).1 h1
  have hcomp : aeval lam (h₁.comp (X ^ k)) = 0 := by
    rw [Polynomial.aeval_comp, map_pow, aeval_X, hk]
    exact hρ'
  have hdvd : h₂ ∣ h₁.comp (X ^ k) := by
    rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
    exact hcomp
  set c := b₂ ^ k with hc
  have hcl : c.toLinearMap = b₂.toLinearMap ^ k := toLinearMap_pow b₂ k
  have hcsl : c.symm.toLinearMap = b₂.symm.toLinearMap ^ k := by
    rw [hc, symm_pow, toLinearMap_pow]
  have h0₁ := hx₁.coeff_zero_ne hh₁
  have h0₂ := hx₂.coeff_zero_ne hh₂
  have hle1 : primaryComponent b₂.toLinearMap h₂ ≤ primaryComponent c.toLinearMap h₁ :=
    fun v hv => by
      rw [mem_primaryComponent, hcl]
      exact aeval_pow_eq_zero hdvd (mem_primaryComponent.1 hv)
  have hle2 : primaryComponent b₂.toLinearMap (reciprocalPolynomial h₂) ≤
      primaryComponent c.toLinearMap (reciprocalPolynomial h₁) := fun v hv => by
    rw [mem_primaryComponent_reciprocalPolynomial h0₁, hcsl]
    exact aeval_pow_eq_zero hdvd ((mem_primaryComponent_reciprocalPolynomial h0₂).1 hv)
  obtain ⟨hWnd, -, hbW, hbW', -, -⟩ := hW₂
  have hWc := isCompl_of_nondeg (polarBilin_symm Q) hWnd
  have hcW : ∀ w ∈ W₂, c w ∈ W₂ := fun w hw => pow_apply_mem hbW k hw
  have hcW' : ∀ x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W₂, c x = x := fun x hx =>
    pow_apply_eq_self (hbW' x hx) k
  have hle3 : orbitSpace c.toLinearMap h₁ ≤ W₂ := by
    refine sup_le (fun v hv => ?_) (fun v hv => ?_)
    · exact mem_of_aeval_eq_zero hWc hcW hcW' (eval_one_ne_zero hirr₁ hmon₁ hne₁)
        (mem_primaryComponent.1 hv)
    · exact mem_of_aeval_eq_zero hWc (fun u hu => symm_mem_of_invariant hcW hu)
        (fun x hx => by rw [← hcW' x hx, LinearEquiv.symm_apply_apply, hcW' x hx])
        (eval_one_ne_zero hirr₁ hmon₁ hne₁)
        ((mem_primaryComponent_reciprocalPolynomial h0₁).1 hv)
  have heq : orbitSpace c.toLinearMap h₁ = W₂ :=
    le_antisymm hle3 (hO₂ ▸ sup_le_sup hle1 hle2)
  refine ⟨k, Nat.pos_of_ne_zero hk0, hkp, mem_primaryFactors_of_ne_bot' hirr₁ hmon₁ ?_, heq⟩
  intro hbot
  apply primaryComponent_ne_bot hx₂.squarefree_minpoly hh₂
  exact eq_bot_iff.2 (hbot ▸ hle1)

theorem mult_eq_one_of_block {M₀ : Type*} [AddCommGroup M₀] [Module (ZMod 2) M₀] [Nontrivial M₀]
    {m : ℕ} {b : V ≃ₗ[ZMod 2] V} {W : Submodule (ZMod 2) V} (hW : IsBlock (polarBilin Q) b W)
    (ι : (Fin m → M₀) →ₗ[ZMod 2] V) (hι : Function.Injective ι) (hr : LinearMap.range ι = W)
    (T : M₀ →ₗ[ZMod 2] M₀) (hT : ∀ a, b (ι a) = ι (fun i => T (a i)))
    (horth : ∀ (i : Fin m) (z : M₀) (a : Fin m → M₀), a i = 0 →
      polar Q (ι (Pi.single i z)) (ι a) = 0) : m = 1 := by
  classical
  obtain ⟨hWnd, hW0, -, -, -, hmin⟩ := hW
  obtain ⟨z, hz⟩ := exists_ne (0 : M₀)
  rcases Nat.lt_or_ge m 2 with hm | hm
  · rcases (show m = 0 ∨ m = 1 by omega) with h0 | h1
    · exfalso
      subst h0
      apply hW0
      rw [← hr, eq_bot_iff]
      rintro _ ⟨a, rfl⟩
      have : a = 0 := funext fun i => i.elim0
      rw [this, map_zero]
      exact Submodule.zero_mem _
    · exact h1
  · exfalso
    let i₀ : Fin m := ⟨0, by omega⟩
    let i₁ : Fin m := ⟨1, by omega⟩
    have hi : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
    let S := LinearMap.range (ι ∘ₗ LinearMap.single (ZMod 2) (fun _ : Fin m => M₀) i₀)
    have hSmem : ∀ y, ι (Pi.single i₀ y) ∈ S := fun y => ⟨y, rfl⟩
    have hSmem' : ∀ s ∈ S, ∃ y, s = ι (Pi.single i₀ y) := by
      rintro _ ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    have hSW : S ≤ W := by
      intro s hs
      obtain ⟨y, rfl⟩ := hSmem' s hs
      rw [← hr]
      exact ⟨_, rfl⟩
    have hS0 : S ≠ ⊥ := by
      intro h
      have h1 : ι (Pi.single i₀ z) ∈ S := hSmem z
      rw [h, Submodule.mem_bot] at h1
      have h2 : Pi.single i₀ z = 0 := hι (by rw [h1, map_zero])
      have h3 := congrFun h2 i₀
      simp only [Pi.single_eq_same, Pi.zero_apply] at h3
      exact hz h3
    have hSb : ∀ s ∈ S, b s ∈ S := by
      intro s hs
      obtain ⟨y, rfl⟩ := hSmem' s hs
      rw [hT]
      have : (fun i => T ((Pi.single i₀ y : Fin m → M₀) i)) = (Pi.single i₀ (T y) : Fin m → M₀) := by
        funext i
        by_cases hii : i = i₀
        · subst hii
          simp
        · simp [Pi.single_apply, hii]
      rw [this]
      exact hSmem _
    have hSnd : Nondeg (polarBilin Q) S := by
      rw [nondeg_iff]
      intro s hs hperp
      obtain ⟨y, rfl⟩ := hSmem' s hs
      rw [nondeg_iff] at hWnd
      refine hWnd _ (hSW (hSmem y)) fun w hw => ?_
      rw [← hr] at hw
      obtain ⟨a, rfl⟩ := hw
      set a₀ : Fin m → M₀ := Pi.single i₀ (a i₀) with ha₀
      set a' : Fin m → M₀ := a - a₀ with ha'
      have ha'0 : a' i₀ = 0 := by simp [ha', ha₀]
      have hsplit : a = a₀ + a' := by rw [ha']; abel
      have e1 : polar Q (ι a₀) (ι (Pi.single i₀ y)) = 0 := hperp _ (hSmem _)
      have e2 : polar Q (ι a') (ι (Pi.single i₀ y)) = 0 := by
        rw [polar_comm]
        exact horth i₀ y _ ha'0
      show polar Q (ι a) (ι (Pi.single i₀ y)) = 0
      rw [hsplit, map_add, polar_add_left, e1, e2, add_zero]
    have hSne : S ≠ W := by
      intro h
      have hmem : ι (Pi.single i₁ z) ∈ S := by rw [h, ← hr]; exact ⟨_, rfl⟩
      obtain ⟨y, hy⟩ := hSmem' _ hmem
      have h2 : Pi.single i₁ z = Pi.single i₀ y := hι hy
      have h3 := congrFun h2 i₁
      simp only [Pi.single_eq_same] at h3
      rw [Pi.single_eq_of_ne hi] at h3
      exact hz h3
    exact hSne (hmin S hSW hS0 hSnd hSb)

@[expose] def piProdEquiv (R ι' M M' : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid M'] [Module R M'] : (ι' → M × M') ≃ₗ[R] (ι' → M) × (ι' → M') where
  toFun a := (fun i => (a i).1, fun i => (a i).2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := fun i => (x.1 i, x.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

theorem fin_one_eq {m : ℕ} (hm : m = 1) (i : Fin m) : i = ⟨0, by omega⟩ :=
  Fin.ext (by have := i.2; omega)

theorem normalize_selfDual {h : (ZMod 2)[X]} [Fact (Irreducible h)] {d m : ℕ}
    {b : V ≃ₗ[ZMod 2] V} {W : Submodule (ZMod 2) V} (hW : IsBlock (polarBilin Q) b W)
    (ι : (Fin m → AdjoinRoot h) →ₗ[ZMod 2] V) (hι : Function.Injective ι)
    (hr : LinearMap.range ι = W)
    (hQι : ∀ a : Fin m → AdjoinRoot h, ∃ hmem : (∑ i, a i * a i ^ (Nat.card (ZMod 2) ^ d)) ∈
        fixedSubfield (ZMod 2) (AdjoinRoot h) d,
      Q (ι a) = Algebra.trace (ZMod 2) (fixedSubfield (ZMod 2) (AdjoinRoot h) d) ⟨_, hmem⟩)
    (hbι : ∀ a, b (ι a) = ι (AdjoinRoot.root h • a)) :
    ∃ ι' : AdjoinRoot h →ₗ[ZMod 2] V, Function.Injective ι' ∧ LinearMap.range ι' = W ∧
      (∀ z : AdjoinRoot h, ∃ hmem : z * z ^ (Nat.card (ZMod 2) ^ d) ∈
          fixedSubfield (ZMod 2) (AdjoinRoot h) d,
        Q (ι' z) = Algebra.trace (ZMod 2) (fixedSubfield (ZMod 2) (AdjoinRoot h) d) ⟨_, hmem⟩) ∧
      ∀ z, b (ι' z) = ι' (AdjoinRoot.root h * z) := by
  classical
  have hN : Nat.card (ZMod 2) ^ d ≠ 0 := pow_ne_zero _ (by rw [Nat.card_zmod]; norm_num)
  have horth : ∀ (i : Fin m) (z : AdjoinRoot h) (a : Fin m → AdjoinRoot h), a i = 0 →
      polar Q (ι (Pi.single i z)) (ι a) = 0 := by
    intro i z a hai
    obtain ⟨h1, e1⟩ := hQι (Pi.single i z + a)
    obtain ⟨h2, e2⟩ := hQι (Pi.single i z)
    obtain ⟨h3, e3⟩ := hQι a
    have hsum : (∑ j, ((Pi.single i z : Fin m → AdjoinRoot h) + a) j *
          ((Pi.single i z : Fin m → AdjoinRoot h) + a) j ^ (Nat.card (ZMod 2) ^ d)) =
        (∑ j, (Pi.single i z : Fin m → AdjoinRoot h) j *
          (Pi.single i z : Fin m → AdjoinRoot h) j ^ (Nat.card (ZMod 2) ^ d)) +
        ∑ j, a j * a j ^ (Nat.card (ZMod 2) ^ d) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hji : j = i
      · subst hji
        simp [hai, zero_pow hN]
      · simp [Pi.single_apply, hji, zero_pow hN]
    have hadd : (⟨_, h1⟩ : ↥(fixedSubfield (ZMod 2) (AdjoinRoot h) d)) = ⟨_, h2⟩ + ⟨_, h3⟩ :=
      Subtype.ext hsum
    show Q (ι (Pi.single i z) + ι a) - Q (ι (Pi.single i z)) - Q (ι a) = 0
    rw [← map_add, e1, e2, e3, hadd, map_add]
    ring
  have hm : m = 1 := mult_eq_one_of_block hW ι hι hr
    (LinearMap.mulLeft (ZMod 2) (AdjoinRoot.root h)) (fun a => by rw [hbι]; rfl) horth
  let i₀ : Fin m := ⟨0, by omega⟩
  let diag : AdjoinRoot h →ₗ[ZMod 2] (Fin m → AdjoinRoot h) := LinearMap.pi fun _ => LinearMap.id
  have hdiag : ∀ z, diag z = fun _ => z := fun z => rfl
  refine ⟨ι ∘ₗ diag, ?_, ?_, fun z => ?_, fun z => ?_⟩
  · intro z z' hzz
    have := congrFun (hι hzz) i₀
    simpa [hdiag] using this
  · refine le_antisymm ((LinearMap.range_comp_le_range _ _).trans hr.le) ?_
    rw [← hr]
    rintro _ ⟨a, rfl⟩
    refine ⟨a i₀, ?_⟩
    rw [LinearMap.comp_apply, hdiag]
    congr 1
    funext i
    rw [fin_one_eq hm i]
  · obtain ⟨hmem, e⟩ := hQι (diag z)
    have hs : (∑ i : Fin m, diag z i * diag z i ^ (Nat.card (ZMod 2) ^ d)) =
        z * z ^ (Nat.card (ZMod 2) ^ d) := by
      show (∑ _i : Fin m, z * z ^ (Nat.card (ZMod 2) ^ d)) = _
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hm, one_smul]
    refine ⟨hs ▸ hmem, ?_⟩
    rw [LinearMap.comp_apply, e]
    congr 1
    exact Subtype.ext hs
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, hbι]
    rfl

theorem normModel_selfDual (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {b : V ≃ₗ[ZMod 2] V} (hb : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hbp : b ^ p = 1) {W : Submodule (ZMod 2) V} (hW : IsBlock (polarBilin Q) b W)
    {h : (ZMod 2)[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors b.toLinearMap)
    (hne1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h)
    (hO : orbitSpace b.toLinearMap h = W) :
    ∃ d : ℕ, h.natDegree = 2 * d ∧ ∃ ι : AdjoinRoot h →ₗ[ZMod 2] V, Function.Injective ι ∧
      LinearMap.range ι = W ∧
      (∀ z : AdjoinRoot h, ∃ hmem : z * z ^ (Nat.card (ZMod 2) ^ d) ∈
          fixedSubfield (ZMod 2) (AdjoinRoot h) d,
        Q (ι z) = Algebra.trace (ZMod 2) (fixedSubfield (ZMod 2) (AdjoinRoot h) d) ⟨_, hmem⟩) ∧
      ∀ z, b (ι z) = ι (AdjoinRoot.root h * z) := by
  have hpo := hp.odd_of_ne_two hp2
  have hx := oddOrderIsometry_of hQ hpo hb hbp
  obtain ⟨d, hd, -, -, -, -, -, ι, hι, hr, hQι, hbι⟩ := hx.selfDualModel hpo hh hne1 hself
  have hVh : primaryComponent b.toLinearMap h = W := by
    rw [← hO, orbitSpace, ← hself, sup_idem]
  exact ⟨d, hd, normalize_selfDual hW ι hι (hr.trans hVh) hQι hbι⟩

theorem normalize_paired {h : (ZMod 2)[X]} [Fact (Irreducible h)] {m : ℕ}
    {b : V ≃ₗ[ZMod 2] V} {W : Submodule (ZMod 2) V} (hW : IsBlock (polarBilin Q) b W)
    (ι : (Fin m → AdjoinRoot h) × (Fin m → AdjoinRoot h) →ₗ[ZMod 2] V)
    (hι : Function.Injective ι) (hr : LinearMap.range ι = W)
    (hQι : ∀ a c, Q (ι (a, c)) = Algebra.trace (ZMod 2) (AdjoinRoot h) (∑ i, a i * c i))
    (hbι : ∀ a c, b (ι (a, c)) = ι (AdjoinRoot.root h • a, (AdjoinRoot.root h)⁻¹ • c)) :
    ∃ ι' : AdjoinRoot h × AdjoinRoot h →ₗ[ZMod 2] V, Function.Injective ι' ∧
      LinearMap.range ι' = W ∧
      (∀ z z' : AdjoinRoot h, Q (ι' (z, z')) = Algebra.trace (ZMod 2) (AdjoinRoot h) (z * z')) ∧
      ∀ z z', b (ι' (z, z')) = ι' (AdjoinRoot.root h * z, (AdjoinRoot.root h)⁻¹ * z') := by
  classical
  let e := piProdEquiv (ZMod 2) (Fin m) (AdjoinRoot h) (AdjoinRoot h)
  have he : ∀ a, e a = (fun i => (a i).1, fun i => (a i).2) := fun a => rfl
  have horth : ∀ (i : Fin m) (z : AdjoinRoot h × AdjoinRoot h)
      (a : Fin m → AdjoinRoot h × AdjoinRoot h), a i = 0 →
      polar Q ((ι ∘ₗ e.toLinearMap) (Pi.single i z)) ((ι ∘ₗ e.toLinearMap) a) = 0 := by
    intro i z a hai
    show Q (ι (e (Pi.single i z)) + ι (e a)) - Q (ι (e (Pi.single i z))) - Q (ι (e a)) = 0
    rw [← map_add, ← map_add, he, he, he, hQι, hQι, hQι]
    have hsum : (∑ j, (((Pi.single i z : Fin m → _) + a) j).1 *
          (((Pi.single i z : Fin m → _) + a) j).2) =
        (∑ j, ((Pi.single i z : Fin m → _) j).1 * ((Pi.single i z : Fin m → _) j).2) +
        ∑ j, (a j).1 * (a j).2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hji : j = i
      · subst hji
        simp [hai]
      · simp [Pi.single_apply, hji]
    rw [hsum, map_add]
    ring
  have hT : ∀ a, b ((ι ∘ₗ e.toLinearMap) a) = (ι ∘ₗ e.toLinearMap)
      (fun i => (LinearMap.prodMap (LinearMap.mulLeft (ZMod 2) (AdjoinRoot.root h))
        (LinearMap.mulLeft (ZMod 2) (AdjoinRoot.root h)⁻¹)) (a i)) := by
    intro a
    show b (ι (e a)) = ι (e _)
    rw [he, he, hbι]
    rfl
  have hm : m = 1 := mult_eq_one_of_block hW (ι ∘ₗ e.toLinearMap) (hι.comp e.injective)
    (by rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, hr]) _ hT horth
  let i₀ : Fin m := ⟨0, by omega⟩
  let diag : AdjoinRoot h × AdjoinRoot h →ₗ[ZMod 2]
      (Fin m → AdjoinRoot h) × (Fin m → AdjoinRoot h) :=
    LinearMap.prodMap (LinearMap.pi fun _ => LinearMap.id) (LinearMap.pi fun _ => LinearMap.id)
  have hdiag : ∀ z z', diag (z, z') = (fun _ => z, fun _ => z') := fun z z' => rfl
  refine ⟨ι ∘ₗ diag, ?_, ?_, fun z z' => ?_, fun z z' => ?_⟩
  · rintro ⟨z, z'⟩ ⟨y, y'⟩ hzz
    have h1 := hι hzz
    rw [hdiag, hdiag] at h1
    have h2 := congrFun (congrArg Prod.fst h1) i₀
    have h3 := congrFun (congrArg Prod.snd h1) i₀
    simp only at h2 h3
    rw [h2, h3]
  · refine le_antisymm ((LinearMap.range_comp_le_range _ _).trans hr.le) ?_
    rw [← hr]
    rintro _ ⟨⟨a, c⟩, rfl⟩
    refine ⟨(a i₀, c i₀), ?_⟩
    rw [LinearMap.comp_apply, hdiag]
    congr 1
    ext i <;> rw [fin_one_eq hm i]
  · rw [LinearMap.comp_apply, hdiag, hQι]
    congr 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hm, one_smul]
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, hdiag, hdiag, hbι]
    rfl

theorem normModel_paired (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {b : V ≃ₗ[ZMod 2] V} (hb : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hbp : b ^ p = 1) {W : Submodule (ZMod 2) V} (hW : IsBlock (polarBilin Q) b W)
    {h : (ZMod 2)[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors b.toLinearMap)
    (hne1 : h ≠ X - 1) (hself : h ≠ reciprocalPolynomial h)
    (hO : orbitSpace b.toLinearMap h = W) :
    ∃ ι : AdjoinRoot h × AdjoinRoot h →ₗ[ZMod 2] V, Function.Injective ι ∧
      LinearMap.range ι = W ∧
      (∀ z z' : AdjoinRoot h, Q (ι (z, z')) = Algebra.trace (ZMod 2) (AdjoinRoot h) (z * z')) ∧
      ∀ z z', b (ι (z, z')) = ι (AdjoinRoot.root h * z, (AdjoinRoot.root h)⁻¹ * z') := by
  have hpo := hp.odd_of_ne_two hp2
  have hx := oddOrderIsometry_of hQ hpo hb hbp
  obtain ⟨-, -, ι, hι, hr, hQι, hbι⟩ := hx.pairedModel hh hne1 hself
  exact normalize_paired hW ι hι (hr.trans hO) hQι hbι

theorem witt_data_of_models {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [FiniteDimensional (ZMod 2) M] (ι₁ ι₂ : M →ₗ[ZMod 2] V) (h₁ : Function.Injective ι₁)
    (h₂ : Function.Injective ι₂) (hQ' : ∀ z, Q (ι₂ z) = Q (ι₁ z)) (T : M →ₗ[ZMod 2] M)
    {b₁ c : V ≃ₗ[ZMod 2] V} (hb₁ : ∀ z, b₁ (ι₁ z) = ι₁ (T z)) (hc : ∀ z, c (ι₂ z) = ι₂ (T z)) :
    ∃ (d : ℕ) (u u' : Fin d → V), LinearIndependent (ZMod 2) u ∧
      LinearIndependent (ZMod 2) u' ∧
      Submodule.span (ZMod 2) (Set.range u) = LinearMap.range ι₁ ∧
      Submodule.span (ZMod 2) (Set.range u') = LinearMap.range ι₂ ∧
      (∀ j, Q (u' j) = Q (u j)) ∧ (∀ j j', polar Q (u' j) (u' j') = polar Q (u j) (u j')) ∧
      ∀ g : V →ₗ[ZMod 2] V, (∀ j, g (u j) = u' j) →
        ∀ w ∈ LinearMap.range ι₁, g (b₁ w) = c (g w) := by
  let β := Module.finBasis (ZMod 2) M
  refine ⟨finrank (ZMod 2) M, ι₁ ∘ β, ι₂ ∘ β,
    β.linearIndependent.map' ι₁ (LinearMap.ker_eq_bot.2 h₁),
    β.linearIndependent.map' ι₂ (LinearMap.ker_eq_bot.2 h₂), ?_, ?_, fun j => hQ' _,
    fun j j' => ?_, fun g hg w hw => ?_⟩
  · rw [Set.range_comp, Submodule.span_image, β.span_eq, Submodule.map_top]
  · rw [Set.range_comp, Submodule.span_image, β.span_eq, Submodule.map_top]
  · show Q (ι₂ (β j) + ι₂ (β j')) - Q (ι₂ (β j)) - Q (ι₂ (β j')) =
      Q (ι₁ (β j) + ι₁ (β j')) - Q (ι₁ (β j)) - Q (ι₁ (β j'))
    rw [← map_add ι₂, ← map_add ι₁, hQ', hQ', hQ']
  · have hgι : g ∘ₗ ι₁ = ι₂ := β.ext fun j => hg j
    have e1 : ∀ y, g (ι₁ y) = ι₂ y := fun y => LinearMap.congr_fun hgι y
    obtain ⟨z, rfl⟩ := hw
    rw [hb₁, e1, e1, hc]

theorem block_comparison (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {b₁ b₂ : V ≃ₗ[ZMod 2] V} (hb₁ : b₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hb₁p : b₁ ^ p = 1) (hb₂ : b₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hb₂p : b₂ ^ p = 1)
    {W₁ W₂ : Submodule (ZMod 2) V} (hW₁ : IsBlock (polarBilin Q) b₁ W₁)
    (hW₂ : IsBlock (polarBilin Q) b₂ W₂) :
    ∃ (k d : ℕ) (u u' : Fin d → V), LinearIndependent (ZMod 2) u ∧
      LinearIndependent (ZMod 2) u' ∧
      Submodule.span (ZMod 2) (Set.range u) = W₁ ∧ Submodule.span (ZMod 2) (Set.range u') = W₂ ∧
      (∀ j, Q (u' j) = Q (u j)) ∧ (∀ j j', polar Q (u' j) (u' j') = polar Q (u j) (u j')) ∧
      ∀ g : V →ₗ[ZMod 2] V, (∀ j, g (u j) = u' j) → ∀ w ∈ W₁, g (b₁ w) = (b₂ ^ k) (g w) := by
  have hpo := hp.odd_of_ne_two hp2
  obtain ⟨h₁, hh₁, hne₁, hO₁⟩ := exists_factor_of_block hQ hpo hb₁ hb₁p hW₁
  obtain ⟨h₂, hh₂, hne₂, hO₂⟩ := exists_factor_of_block hQ hpo hb₂ hb₂p hW₂
  obtain ⟨k, hk0, hkp, hh₁', hO₂'⟩ :=
    exists_pow_factor hQ hp hp2 hb₁ hb₁p hb₂ hb₂p hh₁ hne₁ hh₂ hne₂ hW₂ hO₂
  have hc : b₂ ^ k ∈ TauCeti.QuadraticMap.orthogonalGroup Q := pow_mem hb₂ k
  have hcp : (b₂ ^ k) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hb₂p, one_pow]
  have hcW : IsBlock (polarBilin Q) (b₂ ^ k) W₂ :=
    isBlock_pow hp hb₂p hW₂ fun h => by have := Nat.le_of_dvd hk0 h; omega
  haveI : Fact (Irreducible h₁) := ⟨irreducible_of_mem_primaryFactors hh₁⟩
  by_cases hself : h₁ = reciprocalPolynomial h₁
  · obtain ⟨d₁, hd₁, ι₁, hι₁, hr₁, hQ₁, hb₁ι⟩ :=
      normModel_selfDual hQ hp hp2 hb₁ hb₁p hW₁ hh₁ hne₁ hself hO₁
    obtain ⟨d₂, hd₂, ι₂, hι₂, hr₂, hQ₂, hb₂ι⟩ :=
      normModel_selfDual hQ hp hp2 hc hcp hcW hh₁' hne₁ hself hO₂'
    obtain rfl : d₂ = d₁ := by omega
    obtain ⟨d, u, u', hu, hu', hsu, hsu', hQu, hpu, hint⟩ :=
      witt_data_of_models ι₁ ι₂ hι₁ hι₂
        (fun z => by
          obtain ⟨_, e1⟩ := hQ₁ z
          obtain ⟨_, e2⟩ := hQ₂ z
          rw [e1, e2])
        (LinearMap.mulLeft (ZMod 2) (AdjoinRoot.root h₁)) hb₁ι hb₂ι
    exact ⟨k, d, u, u', hu, hu', hsu.trans hr₁, hsu'.trans hr₂, hQu, hpu,
      fun g hg w hw => hint g hg w (hr₁.symm ▸ hw)⟩
  · obtain ⟨ι₁, hι₁, hr₁, hQ₁, hb₁ι⟩ :=
      normModel_paired hQ hp hp2 hb₁ hb₁p hW₁ hh₁ hne₁ hself hO₁
    obtain ⟨ι₂, hι₂, hr₂, hQ₂, hb₂ι⟩ :=
      normModel_paired hQ hp hp2 hc hcp hcW hh₁' hne₁ hself hO₂'
    obtain ⟨d, u, u', hu, hu', hsu, hsu', hQu, hpu, hint⟩ :=
      witt_data_of_models ι₁ ι₂ hι₁ hι₂ (fun z => by rw [hQ₁, hQ₂])
        (LinearMap.prodMap (LinearMap.mulLeft (ZMod 2) (AdjoinRoot.root h₁))
          (LinearMap.mulLeft (ZMod 2) (AdjoinRoot.root h₁)⁻¹))
        (fun z => hb₁ι z.1 z.2) (fun z => hb₂ι z.1 z.2)
    exact ⟨k, d, u, u', hu, hu', hsu.trans hr₁, hsu'.trans hr₂, hQu, hpu,
      fun g hg w hw => hint g hg w (hr₁.symm ▸ hw)⟩

theorem conj_maxEA_orthogonalGroup (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (E₁ E₂ : Subgroup (V ≃ₗ[ZMod 2] V))
    (hE₁O : E₁ ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hE₂O : E₂ ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hE₁ : IsElemAbelian p E₁) (hE₂ : IsElemAbelian p E₂)
    (hm₁ : ∀ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥E₁)
    (hm₂ : ∀ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥E₂) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, E₂ = E₁.map (MulAut.conj g).toMonoidHom := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have hBs := polarBilin_symm Q
  have hG := isRestrClosed_orthogonalGroup Q
  have hsupp : TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      ptw (LinearMap.BilinForm.orthogonal (polarBilin Q) ⊤) =
        TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [LinearMap.BilinForm.orthogonal_top_eq_bot hQ, inf_eq_left]
    intro g _ x hx
    rw [(Submodule.mem_bot _).1 hx, map_zero]
  obtain ⟨r, b, W, hbE, hbl, -, horth, hcl, hcard⟩ :=
    hasBlocks_of_max hBs hQ hp hp2 hG _ ⊤ rfl (nondeg_top hBs hQ) E₁ (hE₁O.trans hsupp.symm.le) hE₁
      (fun F hF hFa => hm₁ F (hF.trans hsupp.le) hFa)
  obtain ⟨r', b', W', hb'E, hbl', -, horth', hcl', hcard'⟩ :=
    hasBlocks_of_max hBs hQ hp hp2 hG _ ⊤ rfl (nondeg_top hBs hQ) E₂ (hE₂O.trans hsupp.symm.le) hE₂
      (fun F hF hFa => hm₂ F (hF.trans hsupp.le) hFa)
  have hEE : Nat.card ↥E₁ = Nat.card ↥E₂ :=
    le_antisymm (hm₂ E₁ hE₁O hE₁) (hm₁ E₂ hE₂O hE₂)
  have hr : r' = r := by
    rw [hcard, hcard'] at hEE
    exact (Nat.pow_right_injective hp.two_le hEE).symm
  subst hr
  have hbO : ∀ i, b i ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun i => hE₁O (hbE i)
  have hbp : ∀ i, b i ^ p = 1 := fun i => hE₁.2 _ (hbE i)
  have hb'O : ∀ i, b' i ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun i => hE₂O (hb'E i)
  have hb'p : ∀ i, b' i ^ p = 1 := fun i => hE₂.2 _ (hb'E i)
  choose k d u u' hu hu' hsu hsu' hQu hpu hint using fun i =>
    block_comparison hQ hp hp2 (hbO i) (hbp i) (hb'O i) (hb'p i) (hbl i) (hbl' i)
  have humem : ∀ i j, u i j ∈ W i := fun i j => hsu i ▸ Submodule.subset_span ⟨j, rfl⟩
  have hu'mem : ∀ i j, u' i j ∈ W' i := fun i j => hsu' i ▸ Submodule.subset_span ⟨j, rfl⟩
  have hLI := linearIndependent_sigma_of_orth (fun i => (hbl i).1) horth hu humem
  have hLI' := linearIndependent_sigma_of_orth (fun i => (hbl' i).1) horth' hu' hu'mem
  let e := (Fintype.equivFin (Σ i, Fin (d i))).symm
  have hpol : ∀ x y : (Σ i, Fin (d i)), polar Q (u' x.1 x.2) (u' y.1 y.2) =
      polar Q (u x.1 x.2) (u y.1 y.2) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩
    by_cases hii : i = i'
    · subst hii
      exact hpu i j j'
    · have h1 : polar Q (u' i j) (u' i' j') = 0 :=
        horth' i' i (Ne.symm hii) (hu'mem i' j') _ (hu'mem i j)
      have h2 : polar Q (u i j) (u i' j') = 0 :=
        horth i' i (Ne.symm hii) (humem i' j') _ (humem i j)
      exact h1.trans h2.symm
  obtain ⟨g, hgO, hg⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    hQ (fun j => u (e j).1 (e j).2) (fun j => u' (e j).1 (e j).2) (hLI.comp e e.injective)
    (hLI'.comp e e.injective) (fun j => hQu _ _) (fun j j' => hpol _ _)
  have hgu : ∀ i j, g (u i j) = u' i j := fun i j => by
    have := hg (e.symm ⟨i, j⟩)
    rw [Equiv.apply_symm_apply] at this
    exact this
  have hgiso := isIsom_of_mem hgO
  have hmapW : ∀ i, (W i).map g.toLinearMap = W' i := fun i => by
    rw [← hsu i, ← hsu' i, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    exact hgu i j
  have hconj : ∀ i, g * b i * g⁻¹ = b' i ^ k i := by
    intro i
    have hWc := isCompl_of_nondeg hBs (hbl' i).1
    refine linearEquiv_ext_of_isCompl hWc (fun v hv => ?_) (fun x hx => ?_)
    · rw [← hmapW i] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      have hw' : (g⁻¹ : V ≃ₗ[ZMod 2] V) (g w) = w := inv_apply_eq_of_apply_eq rfl
      show g (b i ((g⁻¹ : V ≃ₗ[ZMod 2] V) (g w))) = (b' i ^ k i) (g w)
      rw [hw']
      exact hint i g.toLinearMap (fun j => hgu i j) w hw
    · have hx' : (g⁻¹ : V ≃ₗ[ZMod 2] V) x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (W i) := by
        intro w hw
        have hgw : g w ∈ W' i := hmapW i ▸ Submodule.mem_map_of_mem hw
        show polarBilin Q w ((g⁻¹ : V ≃ₗ[ZMod 2] V) x) = 0
        rw [← hgiso w, apply_inv_apply]
        exact hx _ hgw
      show g (b i ((g⁻¹ : V ≃ₗ[ZMod 2] V) x)) = (b' i ^ k i) x
      rw [(hbl i).2.2.2.1 _ hx', apply_inv_apply, pow_apply_eq_self ((hbl' i).2.2.2.1 x hx)]
  refine ⟨g, hgO, (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm⟩
  · rw [hcl, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    show g * b i * g⁻¹ ∈ E₂
    rw [hconj i]
    exact pow_mem (hb'E i) _
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hEE]

end Orth

section Symp

open CFSG.ClassicalGroups.Alternating CFSG.LocalAnalysis.ComponentInitial

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {B : LinearMap.BilinForm (ZMod 2) V}

theorem add_self_zmod_two (x : V) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x]
  have : (2 : ZMod 2) = 0 := rfl
  rw [this, zero_smul]

theorem isRestrClosed_isometryGroup (hBs : ∀ x y, B x y = B y x) :
    IsRestrClosed B (TauCeti.BilinForm.isometryGroup B) := by
  refine ⟨fun g hg => TauCeti.BilinForm.mem_isometryGroup_iff.1 hg,
    fun g hg W hW hgW g' h1 h2 => ?_⟩
  rw [TauCeti.BilinForm.mem_isometryGroup_iff]
  intro v v'
  have hc := isCompl_of_nondeg hBs hW
  obtain ⟨w, hw, x, hx, rfl⟩ := exists_add_of_isCompl hc v
  obtain ⟨w', hw', x', hx', rfl⟩ := exists_add_of_isCompl hc v'
  have hgiso := TauCeti.BilinForm.mem_isometryGroup_iff.1 hg
  have e1 : B (g w) x' = 0 := hx' _ (hgW w hw)
  have e2 : B x (g w') = 0 := by rw [hBs]; exact hx _ (hgW w' hw')
  have e3 : B w x' = 0 := hx' _ hw
  have e4 : B x w' = 0 := by rw [hBs]; exact hx _ hw'
  simp only [map_add, LinearMap.add_apply, h1 w hw, h1 w' hw', h2 x hx, h2 x' hx', hgiso, e1, e2,
    e3, e4]

variable (hBa : B.IsAlt)

@[expose] noncomputable def tvE (a : V) : V ≃ₗ[ZMod 2] V :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V (symplecticTransvection B hBa a 1)

theorem tvE_apply (a x : V) : tvE hBa a x = x + B x a • a := by
  show (symplecticTransvection B hBa a 1 : V →ₗ[ZMod 2] V) x = _
  rw [symplecticTransvection_apply, one_mul]

theorem tvE_mem (a : V) : tvE hBa a ∈ TauCeti.BilinForm.isometryGroup B := by
  rw [TauCeti.BilinForm.mem_isometryGroup_iff]
  intro x y
  exact (mem_bilinIsometryGroup.1 (symplecticTransvection_mem_bilinIsometryGroup hBa a 1)) x y

theorem conj_tvE {g : V ≃ₗ[ZMod 2] V} (hg : IsIsom B g) (a : V) :
    g * tvE hBa a * g⁻¹ = tvE hBa (g a) := by
  ext x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, tvE_apply, tvE_apply, map_add, map_smul,
    apply_inv_apply]
  congr 2
  rw [← hg (g⁻¹ x) a, apply_inv_apply]

theorem isometryGroup_le_of_tvE (hB : B.Nondegenerate) {H : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hH : ∀ a, tvE hBa a ∈ H) : TauCeti.BilinForm.isometryGroup B ≤ H := by
  intro g hg
  let ε := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V
  have h1 : ε.symm g ∈ bilinIsometryGroup B := by
    rw [mem_bilinIsometryGroup]
    intro x y
    exact TauCeti.BilinForm.mem_isometryGroup_iff.1 hg x y
  rw [alternating_transvection_generation hBa hB] at h1
  have h2 : Subgroup.closure {t | ∃ (a : V) (c : ZMod 2), t = symplecticTransvection B hBa a c} ≤
      H.comap ε.toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨a, c, rfl⟩
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · rw [symplecticTransvection_zero]
      exact one_mem _
    · exact hH a
  have h3 := h2 h1
  rw [Subgroup.mem_comap] at h3
  simpa using h3

include hBa in
theorem isometryGroup_le_iSup_centralizer (hBs : ∀ x y, B x y = B y x) (hB : B.Nondegenerate)
    {r : ℕ} {b : Fin r → V ≃ₗ[ZMod 2] V} {W : Fin r → Submodule (ZMod 2) V}
    (hbl : ∀ i, IsBlock B (b i) (W i)) (hbiso : ∀ i, IsIsom B (b i))
    (horth : ∀ i j, i ≠ j → W i ≤ B.orthogonal (W j)) {s : ℕ} (hs : s + 2 ≤ r) :
    TauCeti.BilinForm.isometryGroup B ≤ ⨆ (S : Finset (Fin r)) (_ : S.card = s),
      TauCeti.BilinForm.isometryGroup B ⊓ Subgroup.centralizer (b '' (S : Set (Fin r))) := by
  classical
  set G := TauCeti.BilinForm.isometryGroup B with hG
  set H := ⨆ (S : Finset (Fin r)) (_ : S.card = s), G ⊓ Subgroup.centralizer (b '' (S : Set (Fin r)))
    with hH
  have hHG : H ≤ G := iSup_le fun S => iSup_le fun _ => inf_le_left
  have hcov : ∀ (a : V) (i j : Fin r), i ≠ j →
      (∀ k, k ≠ i → k ≠ j → a ∈ B.orthogonal (W k)) → tvE hBa a ∈ H := by
    intro a i j hij ha
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ.erase i).erase j) (n := s) (by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩),
          Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
        omega)
    have hmem : tvE hBa a ∈ G ⊓ Subgroup.centralizer (b '' (S : Set (Fin r))) := by
      refine Subgroup.mem_inf.2 ⟨tvE_mem hBa a, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k, hk, rfl⟩
      have hk' := hSsub hk
      rw [Finset.mem_erase, Finset.mem_erase] at hk'
      have hbka : b k a = a := (hbl k).2.2.2.1 a (ha k hk'.2.1 hk'.1)
      have h1 := conj_tvE hBa (hbiso k) a
      rw [hbka] at h1
      calc b k * tvE hBa a = b k * tvE hBa a * (b k)⁻¹ * b k := by group
        _ = tvE hBa a * b k := by rw [h1]
    exact (le_iSup_of_le S (le_iSup_of_le hScard le_rfl) : _ ≤ H) hmem
  let bad : V → Finset (Fin r) := fun v => Finset.univ.filter fun k => v ∉ B.orthogonal (W k)
  have hbad : ∀ v k, k ∈ bad v ↔ v ∉ B.orthogonal (W k) := fun v k => by simp [bad]
  have hcollapse : ∀ (n : ℕ) (v : V), (bad v).card = n → ∃ h ∈ H, ∃ i j : Fin r, i ≠ j ∧
      ∀ k, k ≠ i → k ≠ j → h v ∈ B.orthogonal (W k) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro v hn
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · obtain ⟨t, hvt, ht⟩ := Finset.exists_superset_card_eq (s := bad v) (n := 2) (by omega)
        (by rw [Fintype.card_fin]; omega)
      obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 ht
      refine ⟨1, one_mem _, i, j, hij, fun k hki hkj => ?_⟩
      by_contra hk
      have := hvt ((hbad v k).2 hk)
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h
      · exact hki h
      · exact hkj h
    · obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 (by omega : 1 < (bad v).card)
      have hvi := (hbad v i).1 hi
      have hvj := (hbad v j).1 hj
      obtain ⟨xi, hxi, yi, hyi, hvi'⟩ :=
        exists_add_of_isCompl (isCompl_of_nondeg hBs (hbl i).1) v
      obtain ⟨xj, hxj, yj, hyj, hvj'⟩ :=
        exists_add_of_isCompl (isCompl_of_nondeg hBs (hbl j).1) v
      have hxi0 : xi ≠ 0 := by
        rintro rfl
        rw [zero_add] at hvi'
        exact hvi (hvi' ▸ hyi)
      obtain ⟨y, hy, hyx⟩ : ∃ y ∈ W i, B y xi ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hxi0 ((Submodule.disjoint_def.1 (hbl i).1) xi hxi hcon)
      have hyx1 : B y xi = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ hyx
      set a := y + xj with ha
      have hacov : ∀ k, k ≠ i → k ≠ j → a ∈ B.orthogonal (W k) := fun k hki hkj =>
        Submodule.add_mem _ (horth i k (Ne.symm hki) hy) (horth j k (Ne.symm hkj) hxj)
      have hBva : B v a = 1 := by
        have e1 : B v y = 1 := by
          rw [hvi', map_add, LinearMap.add_apply, hBs xi y, hyx1, hBs yi y, hyi y hy, add_zero]
        have e2 : B v xj = 0 := by
          rw [hvj', map_add, LinearMap.add_apply, hBa xj, hBs yj xj, hyj xj hxj, add_zero]
        rw [ha, map_add, e1, e2, add_zero]
      have hv' : tvE hBa a v = v + a := by rw [tvE_apply, hBva, one_smul]
      have hsub : bad (tvE hBa a v) ⊆ (bad v).erase j := by
        intro k hk
        rw [hbad] at hk
        rw [Finset.mem_erase, hbad]
        by_cases hkj : k = j
        · exfalso
          subst hkj
          apply hk
          have : tvE hBa a v = yj + y := by
            rw [hv', ha, hvj']
            have := add_self_zmod_two xj
            calc xj + yj + (y + xj) = yj + y + (xj + xj) := by abel
              _ = yj + y := by rw [this, add_zero]
          rw [this]
          exact Submodule.add_mem _ hyj (horth i k hij hy)
        · refine ⟨hkj, fun hvk => hk ?_⟩
          by_cases hki : k = i
          · subst hki
            exact absurd hvk hvi
          · rw [hv']
            exact Submodule.add_mem _ hvk (hacov k hki hkj)
      have hlt : (bad (tvE hBa a v)).card < n := by
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hj] at this
        omega
      obtain ⟨h', hh', i', j', hij', hk'⟩ := ih _ hlt (tvE hBa a v) rfl
      refine ⟨h' * tvE hBa a, mul_mem hh' (hcov a i j hij hacov), i', j', hij', fun k hki hkj => ?_⟩
      rw [LinearEquiv.mul_apply]
      exact hk' k hki hkj
  refine isometryGroup_le_of_tvE hBa hB fun v => ?_
  obtain ⟨h, hh, i, j, hij, hk⟩ := hcollapse _ v rfl
  have hhiso : IsIsom B h := TauCeti.BilinForm.mem_isometryGroup_iff.1 (hHG hh)
  have h1 := conj_tvE hBa hhiso v
  have h2 : tvE hBa v = h⁻¹ * tvE hBa (h v) * h := by
    rw [← h1]
    group
  rw [h2]
  exact mul_mem (mul_mem (inv_mem hh) (hcov _ i j hij hk)) hh

end Symp

section Split

variable {X : Type*} [Group X] [Finite X]

theorem split_of_inner {p : ℕ} {J B : Subgroup X} (hB : IsElemAbelian p B)
    (hZ : ∀ z ∈ J, (∀ x ∈ J, z * x = x * z) → z = 1) (jB : ↥B →* X) (hjJ : ∀ b, jB b ∈ J)
    (hj : ∀ (b : ↥B) (x : X), x ∈ J → (b : X) * x * (b : X)⁻¹ = jB b * x * (jB b)⁻¹)
    (hmax : ∀ A : Subgroup X, A ≤ B ⊔ J → IsElemAbelian p A → Nat.card A ≤ Nat.card B) :
    (B ⊓ J) ⊔ (B ⊓ Subgroup.centralizer (J : Set X)) = B ∧
      (B ⊓ J) ⊓ (B ⊓ Subgroup.centralizer (J : Set X)) = ⊥ ∧
      ∀ F : Subgroup X, F ≤ J → IsElemAbelian p F → Nat.card F ≤ Nat.card ↥(B ⊓ J) := by
  classical
  set C := Subgroup.centralizer (J : Set X) with hCdef
  have hJC : J ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact (Subgroup.mem_bot).2 (hZ z hz.1 fun x hx => (Subgroup.mem_centralizer_iff.1 hz.2 x hx).symm)
  have hc_mem : ∀ b : ↥B, (jB b)⁻¹ * (b : X) ∈ C := by
    intro b
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hj b x hx
    calc x * ((jB b)⁻¹ * b) = (jB b)⁻¹ * (jB b * x * (jB b)⁻¹) * b := by group
      _ = (jB b)⁻¹ * ((b : X) * x * (b : X)⁻¹) * b := by rw [this]
      _ = (jB b)⁻¹ * b * x := by group
  let c : ↥B →* X :=
    { toFun := fun b => (jB b)⁻¹ * b
      map_one' := by simp
      map_mul' := fun b b' => by
        have h1 := hj b ((jB b')⁻¹) (J.inv_mem (hjJ b'))
        show (jB (b * b'))⁻¹ * ((b * b' : ↥B) : X) = (jB b)⁻¹ * b * ((jB b')⁻¹ * b')
        rw [map_mul, Subgroup.coe_mul]
        calc (jB b * jB b')⁻¹ * ((b : X) * b') =
            (jB b)⁻¹ * (jB b * (jB b')⁻¹ * (jB b)⁻¹) * b * b' := by group
          _ = (jB b)⁻¹ * ((b : X) * (jB b')⁻¹ * (b : X)⁻¹) * b * b' := by rw [h1]
          _ = (jB b)⁻¹ * b * ((jB b')⁻¹ * b') := by group }
  have hc : ∀ b, c b = (jB b)⁻¹ * b := fun b => rfl
  have hker : ∀ b : ↥B, c b = 1 ↔ (b : X) ∈ J := by
    intro b
    constructor
    · intro h
      rw [hc, inv_mul_eq_one] at h
      rw [← h]
      exact hjJ b
    · intro hbJ
      have h1 : c b ∈ J ⊓ C := ⟨J.mul_mem (J.inv_mem (hjJ b)) hbJ, hc_mem b⟩
      rw [hJC] at h1
      exact h1
  set F := B ⊓ J with hFdef
  have hDC : c.range ≤ C := by rintro _ ⟨b, rfl⟩; exact hc_mem b
  have hTJ : jB.range ≤ J := by rintro _ ⟨b, rfl⟩; exact hjJ b
  have hBtop : IsElemAbelian p (⊤ : Subgroup ↥B) :=
    ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext (hB.comm x.1.2 y.1.2))⟩⟩,
      fun x _ => Subtype.ext (by simpa using hB.2 x.1 x.2)⟩
  have hDea : IsElemAbelian p c.range := by rw [MonoidHom.range_eq_map]; exact hBtop.map c
  have hTea : IsElemAbelian p jB.range := by rw [MonoidHom.range_eq_map]; exact hBtop.map jB
  have hDBJ : c.range ≤ B ⊔ J := by
    rintro _ ⟨b, rfl⟩
    exact mul_mem (Subgroup.mem_sup_right (J.inv_mem (hjJ b))) (Subgroup.mem_sup_left b.2)
  have hcommJ : ∀ a ∈ J, ∀ d ∈ c.range, a * d = d * a := fun a ha d hd =>
    Subgroup.mem_centralizer_iff.1 (hDC hd) a ha
  have hinfJ : ∀ A : Subgroup X, A ≤ J → A ⊓ c.range = ⊥ := fun A hA => by
    rw [eq_bot_iff, ← hJC]
    exact fun x hx => ⟨hA hx.1, hDC hx.2⟩
  have hkerF : Nat.card c.ker = Nat.card F := by
    have : c.ker = F.subgroupOf B := by
      ext b
      rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hDF : Nat.card F * Nat.card c.range = Nat.card B := by
    have := Subgroup.card_ker_mul_card_range c
    rwa [hkerF] at this
  have hFT : F ≤ jB.range := by
    intro x hx
    refine ⟨⟨x, hx.1⟩, ?_⟩
    have := (hker ⟨x, hx.1⟩).2 hx.2
    rw [hc, inv_mul_eq_one] at this
    exact this
  have hDpos : 0 < Nat.card c.range := Nat.card_pos
  have hbound : ∀ A : Subgroup X, A ≤ J → IsElemAbelian p A → Nat.card A ≤ Nat.card F := by
    intro A hAJ hAea
    have h := hmax (A ⊔ c.range) (sup_le (hAJ.trans le_sup_right) hDBJ)
      (IsElemAbelian.sup_of_commute hAea hDea fun a ha d hd => hcommJ a (hAJ ha) d hd)
    rw [card_sup_of_inf_eq_bot (fun a ha d hd => hcommJ a (hAJ ha) d hd) (hinfJ A hAJ), ← hDF]
      at h
    exact Nat.le_of_mul_le_mul_right h hDpos
  have hTF : jB.range = F :=
    (Subgroup.eq_of_le_of_card_ge hFT (hbound _ hTJ hTea)).symm
  refine ⟨le_antisymm (sup_le inf_le_left inf_le_left) (fun b hb => ?_), ?_, hbound⟩
  · have hjF : jB ⟨b, hb⟩ ∈ F := hTF ▸ ⟨⟨b, hb⟩, rfl⟩
    have hcK : c ⟨b, hb⟩ ∈ B ⊓ C :=
      ⟨B.mul_mem (B.inv_mem (Subgroup.mem_inf.1 hjF).1) hb, hc_mem ⟨b, hb⟩⟩
    have : b = jB ⟨b, hb⟩ * c ⟨b, hb⟩ := by rw [hc]; group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left hjF) (Subgroup.mem_sup_right hcK)
  · rw [eq_bot_iff, ← hJC]
    exact fun x hx => ⟨hx.1.2, hx.2.2⟩

end Split

section SpModel

open Matrix

@[expose] noncomputable def spForm (n : ℕ) : LinearMap.BilinForm (ZMod 2) (Fin n ⊕ Fin n → ZMod 2) :=
  Matrix.toBilin' (Matrix.fromBlocks 0 1 (-1) 0)

theorem spForm_apply (n : ℕ) (x y : Fin n ⊕ Fin n → ZMod 2) :
    spForm n x y = ∑ i, (x (Sum.inl i) * y (Sum.inr i) - x (Sum.inr i) * y (Sum.inl i)) := by
  rw [spForm, Matrix.toBilin'_apply', Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type,
    Finset.sum_sub_distrib]
  simp [Matrix.neg_mulVec, sub_eq_add_neg, Finset.sum_neg_distrib]

theorem spForm_symm (n : ℕ) (x y : Fin n ⊕ Fin n → ZMod 2) : spForm n x y = spForm n y x := by
  rw [spForm_apply, spForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  generalize x (Sum.inl i) = a
  generalize x (Sum.inr i) = b
  generalize y (Sum.inl i) = c
  generalize y (Sum.inr i) = d
  revert a b c d
  decide

theorem spForm_isAlt (n : ℕ) : (spForm n).IsAlt := by
  intro x
  rw [spForm_apply]
  exact Finset.sum_eq_zero fun i _ => by ring

theorem spForm_nondegenerate (n : ℕ) : (spForm n).Nondegenerate := by
  refine LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' _ ?_
  rw [CFSG.ClassicalGroups.Symplectic.blueprintGram_eq_neg_J]
  intro h
  have h1 := congrArg Matrix.det (Matrix.neg_J_mul_J (l := Fin n) (R := ZMod 2))
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h1
  exact zero_ne_one h1

theorem mem_statedSp_iff {n : ℕ} (A : GL (Fin n ⊕ Fin n) (ZMod 2)) :
    A ∈ StatedSp n (ZMod 2) ↔
      ∀ x y, spForm n ((A : Matrix _ _ (ZMod 2)) *ᵥ x) ((A : Matrix _ _ (ZMod 2)) *ᵥ y) =
        spForm n x y := by
  rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic,
    TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup,
    ← CFSG.ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup]
  constructor
  · intro h x y
    have h1 := congrArg (fun M => Matrix.toBilin' M x y) h
    rw [← Matrix.toBilin'_comp, LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply,
      Matrix.toLin'_apply] at h1
    exact h1
  · intro h
    apply Matrix.toBilin'.injective
    rw [← Matrix.toBilin'_comp]
    refine LinearMap.ext₂ fun x y => ?_
    rw [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact h x y

theorem nonempty_statedSp_mulEquiv (n : ℕ) :
    Nonempty (↥(StatedSp n (ZMod 2)) ≃* ↥(TauCeti.BilinForm.isometryGroup (spForm n))) := by
  let e : GL (Fin n ⊕ Fin n) (ZMod 2) ≃* ((Fin n ⊕ Fin n → ZMod 2) ≃ₗ[ZMod 2]
      (Fin n ⊕ Fin n → ZMod 2)) :=
    Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _)
  have he : ∀ (A : GL (Fin n ⊕ Fin n) (ZMod 2)) x, e A x = (A : Matrix _ _ (ZMod 2)) *ᵥ x :=
    fun _ _ => rfl
  have hmap : (StatedSp n (ZMod 2)).map e.toMonoidHom = TauCeti.BilinForm.isometryGroup (spForm n) := by
    ext g
    constructor
    · rintro ⟨A, hA, rfl⟩
      rw [TauCeti.BilinForm.mem_isometryGroup_iff]
      intro x y
      simp only [MulEquiv.coe_toMonoidHom, he]
      exact (mem_statedSp_iff A).1 hA x y
    · intro hg
      refine ⟨e.symm g, (mem_statedSp_iff _).2 fun x y => ?_, by simp⟩
      rw [← he, ← he, MulEquiv.apply_symm_apply]
      exact TauCeti.BilinForm.mem_isometryGroup_iff.1 hg x y
  exact ⟨(e.subgroupMap (StatedSp n (ZMod 2))).trans (MulEquiv.subgroupCongr hmap)⟩

end SpModel

section Input1

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

theorem nondegenerate_of_isStdSpace {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {ε : Bool} {m : ℕ} (hstd : IsStdSpace ε Q m) :
    (polarBilin Q).Nondegenerate := by
  cases ε
  · obtain ⟨φ, hφ⟩ := hstd
    exact nondegenerate_polarBilin_of_isometry φ hφ
      (nondegenerate_polarBilin_quadMinus_of_finite m (ZMod 2)
        (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0))
  · obtain ⟨φ, hφ⟩ := hstd
    exact nondegenerate_polarBilin_of_isometry φ hφ (nondegenerate_polarBilin_quadPlus m (ZMod 2))

theorem inputIsomMaxEAConj_holds : OmegaFacts2.InputIsomMaxEAConj := by
  intro p hp hp2 ε n _ _ V _ _ _ Q hstd E₁ E₂ hE₁O hE₂O hE₁ hE₂ hm₁ hm₂
  exact conj_maxEA_orthogonalGroup (nondegenerate_of_isStdSpace hstd) hp hp2 E₁ E₂ hE₁O hE₂O hE₁
    hE₂ hm₁ hm₂

end Input1

section Input3

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem mem_gamma_of_commute {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {J B : Subgroup X} (hB : IsElemAbelian p B) {a c x : X} (haB : a ∈ B) (hcB : c ∈ B)
    (ha1 : a ≠ 1) (hc1 : c ≠ 1) (hac : a ∉ Subgroup.zpowers c) (hxJ : x ∈ J)
    (hxa : x * a = a * x) (hxc : x * c = c * x) :
    x ∈ ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
      J ⊓ Subgroup.normalizer (U : Set X) := by
  set U := Subgroup.zpowers a ⊔ Subgroup.zpowers c with hU
  have hUB : U ≤ B := sup_le (Subgroup.zpowers_le.2 haB) (Subgroup.zpowers_le.2 hcB)
  have hcomm : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ Subgroup.zpowers c, u * v = v * u :=
    fun u hu v hv => hB.comm (Subgroup.zpowers_le.2 haB hu) (Subgroup.zpowers_le.2 hcB hv)
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers c = ⊥ := zpowers_inf_eq_bot hp (hB.2 a haB) hac
  have hcard : Nat.card U = p ^ 2 := by
    rw [hU, card_sup_of_inf_eq_bot hcomm hinf, card_zpowers_of_prime hp (hB.2 a haB) ha1,
      card_zpowers_of_prime hp (hB.2 c hcB) hc1, sq]
  have h2 : 2 ≤ CFSG.Open.pRank p U := CFSG.SectionRank.le_pRank hp.one_lt le_rfl (hB.mono hUB) hcard
  have hUC : U ≤ Subgroup.centralizer ({x} : Set X) :=
    sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hxa.symm))
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hxc.symm))
  have hxN : x ∈ Subgroup.normalizer (U : Set X) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.1 (hUC hu)
  exact Subgroup.mem_iSup_of_mem U (Subgroup.mem_iSup_of_mem hUB
    (Subgroup.mem_iSup_of_mem h2 ⟨hxJ, hxN⟩))

theorem statedScalars_zmod_two_eq_bot' (n : ℕ) : StatedScalars (Fin n ⊕ Fin n) (ZMod 2) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨u, rfl⟩
  have hu : u = 1 := Units.ext (((by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (u : ZMod 2)).resolve_left
    (Units.ne_zero u))
  rw [hu, map_one]
  exact Subgroup.one_mem _

theorem statedSp_aut_inner {n : ℕ} (hn : 3 ≤ n) (σ : MulAut ↥(StatedSp n (ZMod 2))) :
    ∃ y, σ = MulAut.conj y := by
  have hO := (CFSG.RankThree.Classical.higher_symplectic_outer_order_divides_field_multiplier_bound
    Nat.prime_two le_rfl hn (K := ZMod 2) (by rw [Nat.card_zmod, pow_one])).1
  norm_num at hO
  have hbot : (StatedScalars (Fin n ⊕ Fin n) (ZMod 2)).subgroupOf (StatedSp n (ZMod 2)) = ⊥ := by
    rw [statedScalars_zmod_two_eq_bot', Subgroup.bot_subgroupOf]
  let φ : ↥(StatedSp n (ZMod 2)) ≃* StatedProj (StatedSp n (ZMod 2)) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)
  have hO1 : Nat.card (Outer ↥(StatedSp n (ZMod 2))) = 1 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence φ).toEquiv]
    exact hO
  have h1 : (QuotientGroup.mk σ : Outer ↥(StatedSp n (ZMod 2))) = 1 := by
    haveI := (Nat.card_eq_one_iff_unique.1 hO1).1
    exact Subsingleton.elim _ _
  obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff σ).1 h1
  exact ⟨y, hy.symm⟩

theorem inputI2319Sp_holds : OmegaFacts2.InputI2319Sp := by
  intro X _ _ p hp hp2 J B hJt hB hBN hmax hB4
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn, ⟨e₀⟩⟩ := hJt
  refine le_antisymm ?_ (iSup_le fun U => iSup_le fun _ => iSup_le fun _ => inf_le_left)
  set S := StatedSp n (ZMod 2) with hS
  haveI hSs : IsSimpleGroup ↥S := OmegaFacts.isSimpleGroup_statedSp_zmod_two hn
  by_cases hcomm : commutator ↥S = ⊥
  · have h1 : ⁅S, S⁆ = ⊥ := by rw [← Subgroup.map_subtype_commutator S, hcomm, Subgroup.map_bot]
    intro x hx
    have h2 : ((e₀ ⟨x, hx⟩ : ↥⁅S, S⁆) : GL (Fin n ⊕ Fin n) (ZMod 2)) = 1 :=
      Subgroup.mem_bot.1 (h1.le (e₀ ⟨x, hx⟩).2)
    have h3 : (⟨x, hx⟩ : ↥J) = 1 := e₀.injective ((Subtype.ext h2).trans (map_one e₀).symm)
    have h4 : x = 1 := congrArg Subtype.val h3
    rw [h4]
    exact one_mem _
  have htop : commutator ↥S = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥S)).resolve_left hcomm
  have hSS : ⁅S, S⁆ = S := by
    rw [← Subgroup.map_subtype_commutator S, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let e₁ : ↥J ≃* ↥S := e₀.trans (MulEquiv.subgroupCongr hSS)
  have hZS : Subgroup.center ↥S = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥S)).resolve_right fun h =>
      hcomm ((commutator_eq_bot_iff_center_eq_top ↥S).2 h)
  have hcenterS : ∀ z : ↥S, (∀ x : ↥S, z * x = x * z) → z = 1 := fun z hz => by
    have : z ∈ Subgroup.center ↥S := Subgroup.mem_center_iff.2 fun g => (hz g).symm
    rw [hZS] at this
    exact this
  let β : ↥B →* MulAut ↥J := J.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hDp : ∀ b : ↥B, b ^ p = 1 := fun b => Subtype.ext (by simpa using hB.2 b b.2)
  obtain ⟨Yh, hY⟩ := OmegaFacts2.exists_inner_hom hDp e₁ β (fun σ _ => statedSp_aut_inner hn σ)
    hcenterS
  let jB : ↥B →* X := J.subtype.comp (e₁.symm.toMonoidHom.comp Yh)
  have hjJ : ∀ b, jB b ∈ J := fun b => (e₁.symm (Yh b)).2
  have hj : ∀ (b : ↥B) (x : X), x ∈ J → (b : X) * x * (b : X)⁻¹ = jB b * x * (jB b)⁻¹ := by
    intro b x hx
    have h2 : β b ⟨x, hx⟩ = e₁.symm (Yh b) * ⟨x, hx⟩ * (e₁.symm (Yh b))⁻¹ := by
      apply e₁.injective
      rw [hY, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val h2
  have hZ : ∀ z ∈ J, (∀ x ∈ J, z * x = x * z) → z = 1 := by
    intro z hz hzc
    have h1 : e₁ ⟨z, hz⟩ = 1 := hcenterS _ fun y => by
      obtain ⟨⟨x, hx⟩, rfl⟩ := e₁.surjective y
      rw [← map_mul, ← map_mul]
      exact congrArg e₁ (Subtype.ext (hzc x hx))
    exact congrArg Subtype.val (e₁.injective (h1.trans (map_one e₁).symm))
  obtain ⟨hsplit, hinf, hFmax⟩ := split_of_inner hB hZ jB hjJ hj hmax
  set F := B ⊓ J with hFdef
  set K := B ⊓ Subgroup.centralizer (J : Set X) with hKdef
  by_cases hK2 : 2 ≤ CFSG.Open.pRank p K
  · exact (Claims138.eq_gamma_of_two_le_pRank hK2).le
  push Not at hK2
  have hrk : CFSG.Open.pRank p B = CFSG.Open.pRank p F + CFSG.Open.pRank p K :=
    Claims138.pRank_split hp hB hsplit hinf
  have hFea : IsElemAbelian p F := hB.mono inf_le_left
  obtain ⟨Φ₀⟩ := nonempty_statedSp_mulEquiv n
  set G := TauCeti.BilinForm.isometryGroup (spForm n) with hG
  let Φ : ↥J ≃* ↥G := e₁.trans Φ₀
  let ι : ↥J →* ((Fin n ⊕ Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n ⊕ Fin n → ZMod 2)) :=
    G.subtype.comp Φ.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp Φ.injective
  have hιG : ∀ x, ι x ∈ G := fun x => (Φ x).2
  have hιsurj : ∀ g ∈ G, ∃ x, ι x = g := fun g hg => ⟨Φ.symm ⟨g, hg⟩, by simp [ι]⟩
  set F' := (F.subgroupOf J).map ι with hF'def
  have hsupp : G ⊓ ptw (LinearMap.BilinForm.orthogonal (spForm n) ⊤) = G := by
    rw [LinearMap.BilinForm.orthogonal_top_eq_bot (spForm_nondegenerate n), inf_eq_left]
    intro g _ x hx
    rw [(Submodule.mem_bot _).1 hx, map_zero]
  have hF'G : F' ≤ G := by rintro _ ⟨x, -, rfl⟩; exact hιG x
  have hF'card : Nat.card F' = Nat.card F := by
    rw [hF'def, Subgroup.card_map_of_injective hι]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hF'max : ∀ F₂ : Subgroup ((Fin n ⊕ Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n ⊕ Fin n → ZMod 2)),
      F₂ ≤ G ⊓ ptw (LinearMap.BilinForm.orthogonal (spForm n) ⊤) → IsElemAbelian p F₂ →
        Nat.card F₂ ≤ Nat.card F' := by
    intro F₂ hF₂ hF₂ea
    have hF₂G : F₂ ≤ G := hF₂.trans inf_le_left
    have hmap : (F₂.comap ι).map ι = F₂ := Subgroup.map_comap_eq_self fun g hg => by
      obtain ⟨x, hx⟩ := hιsurj g (hF₂G hg)
      exact ⟨x, hx⟩
    have h1 : Nat.card ↥((F₂.comap ι).map J.subtype) = Nat.card F₂ := by
      rw [Subgroup.card_map_of_injective J.subtype_injective]
      conv_rhs => rw [← hmap]
      rw [Subgroup.card_map_of_injective hι]
    rw [hF'card, ← h1]
    exact hFmax _ (Subgroup.map_subtype_le _) ((hF₂ea.comap hι).map J.subtype)
  obtain ⟨r, b, W, hbE, hbl, -, horth, -, hcard⟩ :=
    hasBlocks_of_max (spForm_symm n) (spForm_nondegenerate n) hp hp2
      (isRestrClosed_isometryGroup (spForm_symm n)) _ ⊤ rfl
      (nondeg_top (spForm_symm n) (spForm_nondegenerate n)) F' (hF'G.trans hsupp.symm.le)
      ((hFea.subgroupOf J).map ι) hF'max
  have hr : r = CFSG.Open.pRank p F := by
    have := hcard
    rw [hF'card, Claims138.card_eq_pow_pRank hp hFea] at this
    exact (Nat.pow_right_injective hp.two_le this).symm
  have hbiso : ∀ i, IsIsom (spForm n) (b i) := fun i =>
    TauCeti.BilinForm.mem_isometryGroup_iff.1 (hF'G (hbE i))
  choose f hfF hfb using fun i => Subgroup.mem_map.1 (hbE i)
  have hfF' : ∀ i, ((f i : ↥J) : X) ∈ F := fun i => Subgroup.mem_subgroupOf.1 (hfF i)
  have hfB : ∀ i, ((f i : ↥J) : X) ∈ B := fun i => (Subgroup.mem_inf.1 (hfF' i)).1
  have hbmov : ∀ i, b i ∉ ptw (W i) := fun i h => by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hbl i).2.1
    exact hw0 ((hbl i).2.2.2.2.1 w hw (h w hw))
  have hf1 : ∀ i, ((f i : ↥J) : X) ≠ 1 := fun i h => by
    apply hbmov i
    have : f i = 1 := Subtype.ext h
    rw [← hfb i, this, map_one]
    exact one_mem _
  have hcomm_of : ∀ (x : ↥J) (i : Fin r), ι x * b i = b i * ι x →
      (x : X) * (f i : X) = (f i : X) * x := by
    intro x i h
    rw [← hfb i, ← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (hι h)
  set Γ := ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
    J ⊓ Subgroup.normalizer (U : Set X) with hΓ
  suffices hsuff : G ≤ (Γ.subgroupOf J).map ι by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hsuff (hιG ⟨x, hx⟩)
    rw [hι hyx] at hy
    exact hy
  by_cases hK0 : K = ⊥
  ·
    have hK0' : CFSG.Open.pRank p K ≤ 0 := CFSG.SectionRank.pRank_le hp.one_lt fun F₂ hF₂ _ => by
      rw [pow_zero]
      calc Nat.card F₂ ≤ Nat.card K := Subgroup.card_le_of_le hF₂
        _ = 1 := by rw [hK0, Subgroup.card_bot]
    refine (isometryGroup_le_iSup_centralizer (spForm_isAlt n) (spForm_symm n)
      (spForm_nondegenerate n) hbl hbiso horth (s := 2) (by omega)).trans
      (iSup_le fun T => iSup_le fun hT => ?_)
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 hT
    intro g hg
    obtain ⟨hgG, hgC⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨x, rfl⟩ := hιsurj g hgG
    refine ⟨x, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
    have hci : ι x * b i = b i * ι x :=
      (Subgroup.mem_centralizer_iff.1 hgC (b i) ⟨i, by simp, rfl⟩).symm
    have hcj : ι x * b j = b j * ι x :=
      (Subgroup.mem_centralizer_iff.1 hgC (b j) ⟨j, by simp, rfl⟩).symm
    have hij' : ((f i : ↥J) : X) ∉ Subgroup.zpowers ((f j : ↥J) : X) := by
      intro hm
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hm
      apply hbmov i
      have h1 : b i = b j ^ m := by
        rw [← hfb i, ← hfb j, ← map_zpow]
        congr 1
        exact Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm.symm)
      rw [h1]
      exact zpow_mem (mem_ptw.2 fun w hw => (hbl j).2.2.2.1 w (horth i j hij hw)) m
    exact mem_gamma_of_commute hp hB (hfB i) (hfB j) (hf1 i) (hf1 j) hij' x.2
      (hcomm_of x i hci) (hcomm_of x j hcj)
  ·
    obtain ⟨k, hkK, hk1⟩ := (K.bot_or_exists_ne_one).resolve_left hK0
    have hK1 : CFSG.Open.pRank p K = 1 := by
      have h1 : 1 ≤ CFSG.Open.pRank p K := CFSG.SectionRank.le_pRank hp.one_lt
        (Subgroup.zpowers_le.2 hkK) (CFSG.Open.isElemAbelian_zpowers (hB.2 k hkK.1))
        (by rw [card_zpowers_of_prime hp (hB.2 k hkK.1) hk1, pow_one])
      omega
    refine (isometryGroup_le_iSup_centralizer (spForm_isAlt n) (spForm_symm n)
      (spForm_nondegenerate n) hbl hbiso horth (s := 1) (by omega)).trans
      (iSup_le fun T => iSup_le fun hT => ?_)
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hT
    intro g hg
    obtain ⟨hgG, hgC⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨x, rfl⟩ := hιsurj g hgG
    refine ⟨x, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
    have hci : ι x * b i = b i * ι x :=
      (Subgroup.mem_centralizer_iff.1 hgC (b i) ⟨i, by simp, rfl⟩).symm
    have hik : ((f i : ↥J) : X) ∉ Subgroup.zpowers k := by
      intro hm
      have hmK : ((f i : ↥J) : X) ∈ K := Subgroup.zpowers_le.2 hkK hm
      have h1 : ((f i : ↥J) : X) ∈ F ⊓ K := ⟨hfF' i, hmK⟩
      rw [hinf, Subgroup.mem_bot] at h1
      exact hf1 i h1
    have hxk : (x : X) * k = k * x :=
      (Subgroup.mem_centralizer_iff.1 hkK.2 x x.2)
    exact mem_gamma_of_commute hp hB (hfB i) hkK.1 (hf1 i) hk1 hik x.2 (hcomm_of x i hci) hxk

end Input3

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.ClassicalEA
