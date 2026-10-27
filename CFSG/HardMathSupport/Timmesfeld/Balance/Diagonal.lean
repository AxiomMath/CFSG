module

public import CFSG.ClassicalInvolution.Balance.LocalBalance.Moved
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance

open CFSG CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ClassicalInvolution.Balance.LocalBalance CFSG.LocalCores

universe u

section ListProd

variable {G : Type*} [Group G]

theorem prod_ofFn_mul_of_commute :
    ∀ {n : ℕ} (a b : Fin n → G), (∀ i j, i ≠ j → a i * b j = b j * a i) →
      (List.ofFn fun i => a i * b i).prod = (List.ofFn a).prod * (List.ofFn b).prod
  | 0, a, b, _ => by simp
  | n + 1, a, b, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
      List.prod_cons,
      prod_ofFn_mul_of_commute (fun i => a i.succ) (fun i => b i.succ)
        (fun i j hij => h _ _ (fun e => hij (Fin.succ_injective _ e)))]
    have hc : Commute (b 0) (List.ofFn fun i : Fin n => a i.succ).prod :=
      Commute.list_prod_right _ _ fun y hy => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
        exact (h i.succ 0 (Fin.succ_ne_zero i)).symm
    calc a 0 * b 0 * ((List.ofFn fun i : Fin n => a i.succ).prod *
          (List.ofFn fun i : Fin n => b i.succ).prod)
        = a 0 * (b 0 * (List.ofFn fun i : Fin n => a i.succ).prod) *
          (List.ofFn fun i : Fin n => b i.succ).prod := by group
      _ = a 0 * ((List.ofFn fun i : Fin n => a i.succ).prod * b 0) *
          (List.ofFn fun i : Fin n => b i.succ).prod := by rw [hc.eq]
      _ = a 0 * (List.ofFn fun i : Fin n => a i.succ).prod *
          (b 0 * (List.ofFn fun i : Fin n => b i.succ).prod) := by group

theorem conj_list_prod (f : G) (l : List G) :
    f * l.prod * f⁻¹ = (l.map fun y => f * y * f⁻¹).prod := by
  have := map_list_prod (MulAut.conj f) l
  rw [show (⇑(MulAut.conj f) : G → G) = fun y => f * y * f⁻¹ from
    funext fun y => MulAut.conj_apply f y] at this
  exact this

theorem conj_ofFn_prod_rotate {n : ℕ} (f : G) (A : ℕ → G)
    (hshift : ∀ i, f * A i * f⁻¹ = A (i + 1)) (hper : A (n + 1) = A 0)
    (hcomm : ∀ i j, i < n + 1 → j < n + 1 → i ≠ j → A i * A j = A j * A i) :
    f * (List.ofFn fun i : Fin (n + 1) => A i).prod * f⁻¹ =
      (List.ofFn fun i : Fin (n + 1) => A i).prod := by
  have h1 : (List.ofFn fun i : Fin (n + 1) => A i).prod =
      A 0 * (List.ofFn fun i : Fin n => A (i + 1)).prod := by
    rw [List.ofFn_succ, List.prod_cons]; simp
  have h2 : (List.ofFn fun i : Fin (n + 1) => A i).prod =
      (List.ofFn fun i : Fin n => A i).prod * A n := by
    rw [List.ofFn_succ', List.prod_concat]; simp
  have h3 : f * (List.ofFn fun i : Fin n => A i).prod * f⁻¹ =
      (List.ofFn fun i : Fin n => A (i + 1)).prod := by
    rw [conj_list_prod, List.map_ofFn]
    congr 2
    funext i
    exact hshift i
  have hc : Commute (A 0) (List.ofFn fun i : Fin n => A (i + 1)).prod :=
    Commute.list_prod_right _ _ fun y hy => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
      exact hcomm 0 (i + 1) (by omega) (by omega) (by omega)
  calc f * (List.ofFn fun i : Fin (n + 1) => A i).prod * f⁻¹
      = f * ((List.ofFn fun i : Fin n => A i).prod * A n) * f⁻¹ := by rw [← h2]
    _ = (f * (List.ofFn fun i : Fin n => A i).prod * f⁻¹) * (f * A n * f⁻¹) := by group
    _ = (List.ofFn fun i : Fin n => A (i + 1)).prod * A 0 := by rw [h3, hshift, hper]
    _ = A 0 * (List.ofFn fun i : Fin n => A (i + 1)).prod := hc.eq.symm
    _ = _ := h1.symm

end ListProd

section Diag

variable {Y' : Type*} [Group Y']

@[expose] def diagProd (n : ℕ) (f x : Y') : Y' :=
  (List.ofFn fun i : Fin (n + 1) => f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹).prod

@[expose] def PairComm (n : ℕ) (f : Y') (L : Subgroup Y') : Prop :=
  ∀ i j : ℕ, i < n + 1 → j < n + 1 → i ≠ j → ∀ x ∈ L, ∀ y ∈ L,
    (f ^ i * x * (f ^ i)⁻¹) * (f ^ j * y * (f ^ j)⁻¹) =
      (f ^ j * y * (f ^ j)⁻¹) * (f ^ i * x * (f ^ i)⁻¹)

theorem diagProd_mul {n : ℕ} {f : Y'} {L : Subgroup Y'} (hc : PairComm n f L) {x y : Y'}
    (hx : x ∈ L) (hy : y ∈ L) : diagProd n f (x * y) = diagProd n f x * diagProd n f y := by
  unfold diagProd
  rw [← prod_ofFn_mul_of_commute (fun i : Fin (n + 1) => f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹)
    (fun i : Fin (n + 1) => f ^ (i : ℕ) * y * (f ^ (i : ℕ))⁻¹)
    (fun i j hij => hc i j i.2 j.2 (fun h => hij (Fin.ext h)) x hx y hy)]
  congr 2
  funext i
  group

theorem diagProd_conj_comm {n : ℕ} {f : Y'} (hf : f ^ (n + 1) = 1) {L : Subgroup Y'}
    (hc : PairComm n f L) {x : Y'} (hx : x ∈ L) :
    f * diagProd n f x * f⁻¹ = diagProd n f x := by
  unfold diagProd
  refine conj_ofFn_prod_rotate f (fun i : ℕ => f ^ i * x * (f ^ i)⁻¹) ?_ ?_ ?_
  · intro i
    simp only [pow_succ']
    group
  · simp [hf]
  · exact fun i j hi hj hij => hc i j hi hj hij x hx x hx

theorem diagProd_conj_of_commute {n : ℕ} {f k : Y'} (hk : k * f = f * k) (x : Y') :
    k * diagProd n f x * k⁻¹ = diagProd n f (k * x * k⁻¹) := by
  unfold diagProd
  rw [conj_list_prod, List.map_ofFn]
  congr 2
  funext i
  have hki : k * f ^ (i : ℕ) = f ^ (i : ℕ) * k := ((show Commute k f from hk).pow_right _).eq
  have hki' : (f ^ (i : ℕ))⁻¹ * k⁻¹ = k⁻¹ * (f ^ (i : ℕ))⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hki]
  show k * (f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹) * k⁻¹ =
    f ^ (i : ℕ) * (k * x * k⁻¹) * (f ^ (i : ℕ))⁻¹
  calc k * (f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹) * k⁻¹
      = (k * f ^ (i : ℕ)) * x * ((f ^ (i : ℕ))⁻¹ * k⁻¹) := by group
    _ = (f ^ (i : ℕ) * k) * x * (k⁻¹ * (f ^ (i : ℕ))⁻¹) := by rw [hki, hki']
    _ = _ := by group

theorem diagProd_mem_of_normal {n : ℕ} {f x : Y'} {E : Subgroup Y'} (hE : E.Normal)
    (hx : x ∈ E) : diagProd n f x ∈ E := by
  unfold diagProd
  refine Subgroup.list_prod_mem _ fun y hy => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
  exact hE.conj_mem x hx _

theorem comm_of_diagProd_eq_one {n : ℕ} {f : Y'} {L : Subgroup Y'} (hc : PairComm n f L)
    {x : Y'} (hx : x ∈ L) (h : diagProd n f x = 1) : ∀ g ∈ L, g * x = x * g := by
  intro g hg
  unfold diagProd at h
  rw [List.ofFn_succ, List.prod_cons] at h
  simp only [Fin.val_zero, pow_zero, one_mul, inv_one, mul_one] at h
  set R := (List.ofFn fun i : Fin n =>
    f ^ ((i.succ : Fin (n + 1)) : ℕ) * x * (f ^ ((i.succ : Fin (n + 1)) : ℕ))⁻¹).prod with hR
  have hgR : Commute g R := Commute.list_prod_right _ _ fun y hy => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    have := hc 0 (i.succ : Fin (n + 1)) (by omega) (i.succ : Fin (n+1)).2
      (by simp [Fin.val_succ]) g hg x hx
    simp only [pow_zero, one_mul, inv_one, mul_one] at this
    exact this
  have hRx : R = x⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [hRx] at hgR
  exact (Commute.inv_right_iff.mp hgR).eq

end Diag

section Moved

variable {Y : Type u} [Group Y] [Finite Y]

theorem pairComm_of_isComponent {n : ℕ} (hp : (n + 1).Prime) {L : Subgroup Y}
    (hL : IsComponent L) {f : Y} (hf : f ^ (n + 1) = 1) (hmoved : conjSub f L ≠ L) :
    PairComm n f L := by
  have key : ∀ i j : ℕ, i < j → j < n + 1 → conjSub (f ^ i) L ≠ conjSub (f ^ j) L := by
    intro i j hij hj heq
    have h1 : conjSub (f ^ (n + 1 - i)) (conjSub (f ^ i) L) = L := by
      rw [conjSub_conjSub, ← pow_add, Nat.sub_add_cancel (by omega), hf, conjSub_one]
    have h2 : conjSub (f ^ (n + 1 - i)) (conjSub (f ^ j) L) = conjSub (f ^ (j - i)) L := by
      rw [conjSub_conjSub, ← pow_add]
      have : n + 1 - i + j = (n + 1) + (j - i) := by omega
      rw [this, pow_add, hf, one_mul]
    have hm : conjSub (f ^ (j - i)) L = L := by rw [← h2, ← heq, h1]
    have hm0 : 0 < j - i := by omega
    have hmp : j - i < n + 1 := by omega
    have hcop : Nat.Coprime (j - i) (n + 1) :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt hm0 hmp))
    obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    have hft : conjSub ((f ^ (j - i)) ^ t) L = L := conjSub_pow_eq hm t
    apply hmoved
    have hmod := Nat.mod_add_div ((j - i) * t) (n + 1)
    rw [ht] at hmod
    have hpow : (f ^ (j - i)) ^ t = f := by
      rw [← pow_mul, ← hmod, pow_add, pow_mul, hf, one_pow, mul_one, pow_one]
    rw [← hpow]
    exact hft
  have hcomp : ∀ i : ℕ, IsComponent (conjSub (f ^ i) L) := fun i =>
    isComponent_map_mulEquiv (MulAut.conj (f ^ i)) hL
  intro i j hi hj hij x hx y hy
  rcases lt_or_gt_of_ne hij with h | h
  · exact commute_of_isComponent_of_ne (hcomp i) (hcomp j) (key i j h hj) _
      (conj_mem_conjSub hx) _ (conj_mem_conjSub hy)
  · exact (commute_of_isComponent_of_ne (hcomp j) (hcomp i) (key j i h hi) _
      (conj_mem_conjSub hy) _ (conj_mem_conjSub hx)).symm

end Moved

variable {Y : Type u} [Group Y] [Finite Y] {p : ℕ}


theorem exists_diagonal_component_p (hp : p.Prime) {L : Subgroup Y} (hL : IsComponent L) {f : Y}
    (hf : f ^ p = 1) (hmoved : conjSub f L ≠ L) :
    ∃ Δ : Subgroup Y, Δ ≤ Subgroup.centralizer ({f} : Set Y) ∧
      IsComponent (Δ.subgroupOf (Subgroup.centralizer ({f} : Set Y))) ∧
      Nat.card (↥L ⧸ Subgroup.center ↥L) ∣ Nat.card Δ ∧
      ∀ x ∈ L, (List.ofFn fun i : Fin p => f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹).prod ∈ Δ := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have hc : PairComm n f L := pairComm_of_isComponent hp hL hf hmoved
  let ψ : L →* Y :=
    MonoidHom.mk' (fun x : L => diagProd n f (x : Y)) (fun x y => diagProd_mul hc x.2 y.2)
  have hψ : ∀ x : L, ψ x = diagProd n f (x : Y) := fun x => rfl
  set Δ : Subgroup Y := ψ.range with hΔ
  set C : Subgroup Y := Subgroup.centralizer ({f} : Set Y) with hC
  have hΔC : Δ ≤ C := by
    rintro _ ⟨x, rfl⟩
    rw [hC, Subgroup.mem_centralizer_singleton_iff, hψ]
    exact ((mul_inv_eq_iff_eq_mul).mp (diagProd_conj_comm hf hc x.2)).symm
  have hker : ψ.ker ≤ Subgroup.center L := by
    intro x hx
    rw [MonoidHom.mem_ker, hψ] at hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (comm_of_diagProd_eq_one hc x.2 hx g g.2)
  refine ⟨Δ, hΔC, ⟨?_, ?_⟩, ?_, fun x hx => ⟨⟨x, hx⟩, rfl⟩⟩
  ·
    have hker' : ψ.rangeRestrict.ker ≤ Subgroup.center L := by
      rw [MonoidHom.ker_rangeRestrict]
      exact hker
    have hq := isQuasisimple_of_surjective hL.1 ψ.rangeRestrict
      (MonoidHom.rangeRestrict_surjective ψ) hker'
    exact isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hΔC).symm hq
  ·
    set E : Subgroup Y := layer Y with hE
    have hEnorm : E.Normal := by
      have : (layer Y).Characteristic := layer_characteristic
      infer_instance
    have hLE : L ≤ E := component_le_layer hL
    have hΔE : Δ ≤ E := by
      rintro _ ⟨x, rfl⟩
      exact diagProd_mem_of_normal hEnorm (hLE x.2)
    have hEn : E ≤ Subgroup.normalizer (L : Set Y) := layer_le_normalizer hL
    have hN1 : (Δ.subgroupOf (E ⊓ C)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff (le_inf hΔE hΔC)]
      rintro _ k ⟨w, rfl⟩ ⟨hkE, hkC⟩
      have hkf : k * f = f * k := Subgroup.mem_centralizer_singleton_iff.mp hkC
      have hkL : k * (w : Y) * k⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hEn hkE) w).mp w.2
      rw [hψ, diagProd_conj_of_commute hkf]
      exact ⟨⟨_, hkL⟩, rfl⟩
    have hN3 : ((E ⊓ C).subgroupOf C).Normal := by
      rw [Subgroup.normal_subgroupOf_iff inf_le_right]
      rintro h k ⟨hhE, hhC⟩ hkC
      exact ⟨hEnorm.conj_mem h hhE k, C.mul_mem (C.mul_mem hkC hhC) (C.inv_mem hkC)⟩
    have hchain : IsSubnormal Δ C :=
      IsSubnormal.step (le_inf hΔE hΔC) hN1
        (IsSubnormal.step inf_le_right hN3 (IsSubnormal.refl C))
    have h1 : IsSubnormal (Δ.subgroupOf C) ⊤ :=
      (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hΔC).mpr hchain
    exact CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain h1
      Subgroup.IsSubnormal.top
  ·
    have h1 : Nat.card Δ = ψ.ker.index := by
      rw [Subgroup.index_eq_card]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv).symm
    rw [h1, ← Subgroup.index_eq_card]
    exact Subgroup.index_dvd_of_le hker

end CFSG.HardMathSupport.Timmesfeld.Balance
