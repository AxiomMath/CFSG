module

public import CFSG.GH74.Uniqueness.Section1214Semi
public import CFSG.GH74.Uniqueness.Section1213Meta
public import CFSG.GH74.Uniqueness.Section1212
public import CFSG.GH74.Uniqueness.Section124A

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

section Point

omit [Finite X] in
theorem A5.commute_of_mem_point (hZ : IsInvariantInvolutionSet Z)
    (hM : ∀ x ∈ zHull Z M, x ^ 2 = 1) {Y : Subgroup X} (hY : Odd (Nat.card Y)) {s : X}
    (hs : s ∈ Z) (hsN : s ∈ normalizer (Y : Set X)) {g : X} (hsβ : s ∈ conjugate M g)
    (hYβ : Y ≤ conjugate M g) : ∀ y ∈ Y, s * y = y * s := by
  intro y hy
  have hyβ : y ∈ conjugate M g := hYβ hy
  have hsinv : s⁻¹ ∈ normalizer (Y : Set X) := (normalizer (Y : Set X)).inv_mem hsN
  have h1 : y⁻¹ * s * y ∈ Z := hZ.2 s hs y
  have h2 : y⁻¹ * s * y ∈ zHull Z (conjugate M g) :=
    subset_closure ⟨h1, (conjugate M g).mul_mem
      ((conjugate M g).mul_mem ((conjugate M g).inv_mem hyβ) hsβ) hyβ⟩
  have h3 : s ∈ zHull Z (conjugate M g) := subset_closure ⟨hs, hsβ⟩
  have h4 : s⁻¹ * (y⁻¹ * s * y) ∈ zHull Z (conjugate M g) := mul_mem (inv_mem h3) h2
  have h5 : s⁻¹ * (y⁻¹ * s * y) ∈ Y := by
    have e : s⁻¹ * (y⁻¹ * s * y) = (s⁻¹ * y⁻¹ * s) * y := by group
    rw [e]
    refine Y.mul_mem ?_ hy
    have := (mem_normalizer_iff.mp hsinv y⁻¹).mp (Y.inv_mem hy)
    simpa using this
  have h6 : s⁻¹ * (y⁻¹ * s * y) = 1 :=
    eq_one_of_sq_eq_one_of_odd hY h5 (sq_eq_one_of_mem_zHull_conjugate hZ hM g h4)
  have h7 : y⁻¹ * s * y = s := by
    have := congrArg (fun w => s * w) h6
    simpa using this
  calc s * y = y * (y⁻¹ * s * y) := by group
    _ = y * s := by rw [h7]

end Point

section K

variable {c : Ctx12 Z M} {n i : ℕ}

theorem A5.kGrp_le_D (hL : LData c n i) : kGrp M c.t ≤ c.D := by
  rw [hL.k_eq']
  exact inf_le_left

theorem A5.inv_of_mem_kGrp (hL : LData c n i) {x : X} (hx : x ∈ kGrp M c.t) :
    c.t * x * c.t⁻¹ = x⁻¹ := by
  have h : x ∈ (kGrp M c.t : Set X) := hx
  rw [hL.k_eq] at h
  exact h.2

theorem A5.odd_card_kGrp (hL : LData c n i) : Odd (Nat.card (kGrp M c.t)) := by
  rw [hL.k_eq', hL.k_card]
  exact A2.odd_two_pow_sub_one (by have := hL.hn; omega)

theorem A5.isCyclic_kGrp (hL : LData c n i) : IsCyclic (kGrp M c.t) := by
  rw [hL.k_eq']
  exact hL.k_cyclic

theorem A5.mem_normalizer_kGrp_of_mem_D (hL : LData c n i) {d : X} (hd : d ∈ c.D) :
    d ∈ normalizer (kGrp M c.t : Set X) := by
  have hdN : d ∈ normalizer (c.L : Set X) := by
    have h1 : d ∈ (c.L : Set X) * (c.D : Set X) :=
      Set.mem_mul.mpr ⟨1, c.L.one_mem, d, hd, one_mul _⟩
    rw [← hL.normalizer_eq] at h1
    exact h1
  refine mem_normalizer_fintype fun k hk => ?_
  rw [hL.k_eq'] at hk ⊢
  obtain ⟨hkD, hkL⟩ := mem_inf.mp hk
  exact mem_inf.mpr ⟨c.D.mul_mem (c.D.mul_mem hd hkD) (c.D.inv_mem hd),
    (mem_normalizer_iff.mp hdN k).mp hkL⟩

theorem A5.t_mem_normalizer_kGrp (hL : LData c n i) : c.t ∈ normalizer (kGrp M c.t : Set X) :=
  mem_normalizer_fintype fun k hk => by
    have h := A5.inv_of_mem_kGrp hL (show k ∈ kGrp M c.t from hk)
    rw [h]
    exact inv_mem hk

theorem A5.mem_normalizer_zpowers_of_mem_normalizer_kGrp (hL : LData c n i) {x : X}
    (hx : x ∈ kGrp M c.t) {g : X} (hg : g ∈ normalizer (kGrp M c.t : Set X)) :
    g ∈ normalizer ((zpowers x : Subgroup X) : Set X) := by
  have hgx : g * x * g⁻¹ ∈ kGrp M c.t := (mem_normalizer_iff.mp hg x).mp hx
  have heq : zpowers (g * x * g⁻¹) = zpowers x :=
    Bender.eq_of_card_eq_of_cyclic (A5.isCyclic_kGrp hL) (zpowers_le.mpr hgx)
      (zpowers_le.mpr hx) (by rw [Nat.card_zpowers, Nat.card_zpowers, A5.orderOf_conj])
  refine mem_normalizer_fintype fun y hy => ?_
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rw [← conj_zpow, ← heq]
  exact zpow_mem (mem_zpowers _) k

theorem A5.zpowers_conj_eq (hL : LData c n i) {x : X} (hx : x ∈ kGrp M c.t) {g : X}
    (hg : g ∈ normalizer (kGrp M c.t : Set X)) : zpowers (g * x * g⁻¹) = zpowers x :=
  Bender.eq_of_card_eq_of_cyclic (A5.isCyclic_kGrp hL)
    (zpowers_le.mpr ((mem_normalizer_iff.mp hg x).mp hx)) (zpowers_le.mpr hx)
    (by rw [Nat.card_zpowers, Nat.card_zpowers, A5.orderOf_conj])

theorem A5.mem_normalizer_sylow_of_mem_normalizer_kGrp (hL : LData c n i) {P₀ : Subgroup X} (hP₀ : P₀ ≤ kGrp M c.t) {g : X} (hg : g ∈ normalizer (kGrp M c.t : Set X)) :
    g ∈ normalizer (P₀ : Set X) := by
  have hle : P₀.map (MulAut.conj g).toMonoidHom ≤ kGrp M c.t := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hg y).mp (hP₀ hy)
  have heq : P₀.map (MulAut.conj g).toMonoidHom = P₀ :=
    Bender.eq_of_card_eq_of_cyclic (A5.isCyclic_kGrp hL) hle hP₀
      (card_map_of_injective (MulAut.conj g).injective)
  refine mem_normalizer_fintype fun y hy => ?_
  rw [← heq]
  exact ⟨y, hy, by simp⟩

theorem A5.mem_sylow_kGrp (hL : LData c n i) {p : ℕ} (hp : p.Prime) {x : X}
    (hx : x ∈ kGrp M c.t) (hxp : orderOf x = p) {P₀ : Subgroup X}
    (hP₀ : ABGLocalTools.IsSylowOf p P₀ (kGrp M c.t)) : x ∈ P₀ := by
  have : Fact p.Prime := ⟨hp⟩
  have hpK : p ∣ Nat.card (kGrp M c.t) := by
    rw [← hxp]
    have := orderOf_dvd_natCard (⟨x, hx⟩ : ↥(kGrp M c.t))
    rwa [Subgroup.orderOf_mk] at this
  have hpP : p ∣ Nat.card P₀ := by
    rw [hP₀.card_eq]
    exact dvd_pow_self p ((Nat.Prime.factorization_pos_of_dvd hp Nat.card_pos.ne' hpK).ne')
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥P₀) p hpP
  have hyo : orderOf (y : X) = p := by rw [Subgroup.orderOf_coe]; exact hy
  have heq : zpowers (y : X) = zpowers x :=
    Bender.eq_of_card_eq_of_cyclic (A5.isCyclic_kGrp hL) (zpowers_le.mpr (hP₀.le y.2))
      (zpowers_le.mpr hx) (by rw [Nat.card_zpowers, Nat.card_zpowers, hyo, hxp])
  have : x ∈ zpowers (y : X) := heq ▸ mem_zpowers x
  exact zpowers_le.mpr y.2 this

end K

section Twelve

variable {c : Ctx12 Z M} {n i : ℕ}

theorem A5.lemma1212_kGrp (S : ZDSetup X Z M) (h1212 : Lemma1212Stmt Z M) (hL : LData c n i)
    {x : X} (hx : x ∈ kGrp M c.t) (hx1 : x ≠ 1) :
    Open.pRank 2 (zHull Z (normalizer ((zpowers x : Subgroup X) : Set X))) = 1 ∧
      zHull Z (centralizer ((zpowers x : Subgroup X) : Set X)) = ⊥ := by
  have hodd : Odd (orderOf x) := by
    have h1 := orderOf_dvd_natCard (⟨x, hx⟩ : ↥(kGrp M c.t))
    rw [Subgroup.orderOf_mk] at h1
    exact (A5.odd_card_kGrp hL).of_dvd_nat h1
  have hYodd : Odd (Nat.card (zpowers x)) := by rw [Nat.card_zpowers]; exact hodd
  have ht2 : c.t * c.t = 1 := S.invariant.mul_self_eq_one c.ht
  have hinv := A5.inv_of_mem_kGrp hL hx
  have hne : c.t * x ≠ x * c.t := by
    intro h
    have : x * c.t * c.t⁻¹ = x⁻¹ := by rw [← h]; exact hinv
    rw [mul_inv_cancel_right] at this
    exact hx1 (eq_one_of_mul_self_of_odd_orderOf (mul_eq_one_iff_eq_inv.mpr this) hodd)
  exact h1212 c n i hL (zpowers x) hYodd
    ⟨c.t, c.ht, mem_normalizer_zpowers_of_inv ht2 hinv, x, mem_zpowers x, hne⟩

theorem A5.not_commute_of_mem_kGrp (S : ZDSetup X Z M) (h1212 : Lemma1212Stmt Z M)
    (hL : LData c n i) {x : X} (hx : x ∈ kGrp M c.t) (hx1 : x ≠ 1) :
    ∀ s ∈ Z, s * x ≠ x * s := by
  intro s hs hsx
  have hbot := (A5.lemma1212_kGrp S h1212 hL hx hx1).2
  have hsC : s ∈ centralizer ((zpowers x : Subgroup X) : Set X) := by
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left (show Commute x s from hsx.symm) k).eq)
  have hs1 : s ∈ zHull Z (centralizer ((zpowers x : Subgroup X) : Set X)) :=
    subset_closure ⟨hs, hsC⟩
  rw [hbot, mem_bot] at hs1
  have hs2 := S.invariant.1 s hs
  rw [hs1, orderOf_one] at hs2
  exact absurd hs2 (by norm_num)

theorem A5.zNumShare_eq (hL : LData c n i) {p : ℕ} (hp : p.Prime) {P₀ : Subgroup X}
    (hP₀ : ABGLocalTools.IsSylowOf p P₀ (kGrp M c.t)) : zNumShare Z M p = Nat.card P₀ := by
  have : Fact p.Prime := ⟨hp⟩
  have hz : zNum Z M = 2 ^ n - 1 := by
    unfold zNum
    rw [Nat.card_coe_set_eq]
    exact A2.ncard_zM hL
  rw [hP₀.card_eq, zNumShare, hz, hL.k_eq', hL.k_card]

theorem A5.zCosetNum_eq (S : ZDSetup X Z M) (hL : LData c n i) {P₀ : Subgroup X}
    (hP₀ : P₀ ≤ kGrp M c.t) : zCosetNum Z P₀ c.t = Nat.card P₀ := by
  have hmem : ∀ w ∈ P₀, w * c.t ∈ Z := by
    intro w hw
    have hwK := hP₀ hw
    have hodd : Odd (orderOf w) := by
      have h1 := orderOf_dvd_natCard (⟨w, hwK⟩ : ↥(kGrp M c.t))
      rw [Subgroup.orderOf_mk] at h1
      exact (A5.odd_card_kGrp hL).of_dvd_nat h1
    obtain ⟨m, hm⟩ := Bender.exists_sq_eq_of_odd_orderOf hodd
    have hvK : w ^ m ∈ kGrp M c.t := pow_mem hwK m
    have hinv := A5.inv_of_mem_kGrp hL hvK
    have h1 : (w ^ m)⁻¹⁻¹ * c.t * (w ^ m)⁻¹ ∈ Z := S.invariant.2 c.t c.ht _
    have h3 : c.t * (w ^ m)⁻¹ = w ^ m * c.t := by
      have h4 : (c.t * w ^ m * c.t⁻¹)⁻¹ = (w ^ m)⁻¹⁻¹ := by rw [hinv]
      rw [inv_inv] at h4
      calc c.t * (w ^ m)⁻¹ = (c.t * w ^ m * c.t⁻¹)⁻¹ * c.t := by group
        _ = w ^ m * c.t := by rw [h4]
    have e : (w ^ m)⁻¹⁻¹ * c.t * (w ^ m)⁻¹ = w * c.t := by
      rw [inv_inv, mul_assoc, h3, ← mul_assoc, hm]
    rwa [e] at h1
  unfold zCosetNum
  refine Nat.card_congr
    { toFun := fun y => ⟨(y : X) * c.t⁻¹, y.2.2⟩
      invFun := fun w => ⟨(w : X) * c.t, hmem w w.2, by simp⟩
      left_inv := fun y => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp) }

theorem A5.omegaFix_sylow_kGrp
    (S : ZDSetup X Z M) (h1212 : Lemma1212Stmt Z M)
    (hL : LData c n i) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : X} (hx : x ∈ kGrp M c.t)
    (hx1 : x ≠ 1) {P₀ : Subgroup X} (hP₀ : ABGLocalTools.IsSylowOf p P₀ (kGrp M c.t))
    (hxP₀ : x ∈ P₀) :
    ∀ γ ∈ omegaFix M (P₀ : Set X), γ = M ∨ γ = conjugate M c.t := by
  have : Fact p.Prime := ⟨hp⟩
  have hgood := A5.not_commute_of_mem_kGrp S h1212 hL hx hx1
  have hP₀K : P₀ ≤ kGrp M c.t := hP₀.le
  have hP₀D : P₀ ≤ c.D := hP₀K.trans (A5.kGrp_le_D hL)
  have hMt : conjugate M c.t ≠ M := (S.prodDisc.conjugate_ne_iff (self_mem_omega M)).mpr c.htM
  intro γ hγ
  by_contra hcon
  push Not at hcon
  obtain ⟨hγM, hγMt⟩ := hcon
  have hMfix : M ∈ omegaFix M (P₀ : Set X) :=
    S.prodDisc.mem_omegaFix_iff.mpr ⟨self_mem_omega M, hP₀D.trans inf_le_left⟩
  have hMtfix : conjugate M c.t ∈ omegaFix M (P₀ : Set X) :=
    S.prodDisc.mem_omegaFix_iff.mpr ⟨⟨c.t, rfl⟩, hP₀D.trans inf_le_right⟩
  have h3 : 3 ≤ (omegaFix M (P₀ : Set X)).ncard := by
    have hsub : ({γ, M, conjugate M c.t} : Set (Subgroup X)) ⊆ omegaFix M (P₀ : Set X) := by
      intro δ hδ
      rcases hδ with rfl | rfl | rfl
      · exact hγ
      · exact hMfix
      · exact hMtfix
    have hcard : ({γ, M, conjugate M c.t} : Set (Subgroup X)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by simp [hγM, hγMt]) (Set.toFinite _),
        Set.ncard_pair (Ne.symm hMt)]
    rw [← hcard]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hcond : Prop52Cond Z M p P₀ := ⟨hP₀.isPGroup, h3, c.t, c.ht,
    A5.mem_normalizer_sylow_of_mem_normalizer_kGrp hL hP₀K (A5.t_mem_normalizer_kGrp hL),
    by rw [A5.zCosetNum_eq S hL hP₀K, A5.zNumShare_eq hL hp hP₀]⟩
  obtain ⟨Q, hP₀Q, hmax⟩ := Finite.exists_le_maximal hcond
  have h52 := S.prop52 p hp hp2 Q hmax
  obtain ⟨δ, hδ⟩ : (omegaFix M (Q : Set X)).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    have := hmax.1.three_le
    omega
  obtain ⟨s, hs, hsN, hsδ⟩ := h52.2 S.theorem4.1 δ hδ
  obtain ⟨hδΩ, hQδ⟩ := S.prodDisc.mem_omegaFix_iff.mp hδ
  have hsδ' : s ∈ δ := (S.prodDisc.conjugate_eq_iff_mem hδΩ).mp hsδ
  obtain ⟨g, rfl⟩ := hδΩ
  have hcomm := A5.commute_of_mem_point S.invariant hL.m_abelian.2
    (odd_card_of_isPGroup hp hp2 hmax.1.pgroup) hs hsN hsδ' hQδ
  exact hgood s hs (hcomm x (hP₀Q hxP₀))

end Twelve

end CFSG.GH74.Uniqueness
