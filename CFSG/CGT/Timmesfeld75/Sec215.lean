module

public import CFSG.CGT.Timmesfeld75.Reduction
public import CFSG.CGT.Timmesfeld75.Sec215Local
public import CFSG.Timmesfeld.Bridge.Asc72Defs

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Timmesfeld.Bridge.Asc72
open scoped commutatorElement

section Wreath

open SemidirectProduct

private theorem permAct_apply {ι L : Type*} [Group L] (σ : Equiv.Perm ι) (h : ι → L) (i : ι) :
    permAct ι L σ h i = h (σ.symm i) := rfl

private theorem right_eq_one_of_commute_base {P : Type*} [Group P] [Nontrivial P] {n : ℕ}
    {x : (Fin n → P) ⋊[permAct (Fin n) P] Equiv.Perm (Fin n)}
    (hx : ∀ b : Fin n → P, x * inl b = inl b * x) : x.right = 1 := by
  obtain ⟨p, hp⟩ := exists_ne (1 : P)
  have key : ∀ i j : Fin n, x.right.symm i = j → i = j := by
    intro i j hij
    by_contra hne
    have h := congrArg (fun y => y.left i) (hx (Pi.mulSingle j p))
    simp only [mul_left, left_inl, right_inl, map_one, Pi.mul_apply, permAct_apply,
      MulAut.one_apply, hij, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hne] at h
    rw [one_mul] at h
    exact hp (mul_left_cancel (h.trans (mul_one _).symm))
  refine Equiv.ext fun i => ?_
  exact key (x.right i) i (Equiv.symm_apply_apply _ _)

private theorem index_ker_rightHom {P : Type*} [Group P] {n : ℕ} :
    (rightHom : (Fin n → P) ⋊[permAct (Fin n) P] Equiv.Perm (Fin n) →*
      Equiv.Perm (Fin n)).ker.index = n.factorial := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 rightHom_surjective, Subgroup.card_top,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

private theorem not_simple_normal_index_two {P : Type*} [Group P] [Nontrivial P] {n : ℕ}
    (hn : 3 ≤ n) {N₁ : Subgroup ((Fin n → P) ⋊[permAct (Fin n) P] Equiv.Perm (Fin n))}
    [N₁.Normal] (hN : IsSimpleGroup N₁) (hidx : N₁.index = 2) : False := by
  set B : Subgroup ((Fin n → P) ⋊[permAct (Fin n) P] Equiv.Perm (Fin n)) := rightHom.ker with hB
  have hBn : B.Normal := MonoidHom.normal_ker _
  rcases (inferInstance : (B.subgroupOf N₁).Normal).eq_bot_or_eq_top with h | h
  · have hbot : ∀ x ∈ N₁, x ∈ B → x = 1 := by
      intro x hx hxB
      have : (⟨x, hx⟩ : N₁) ∈ B.subgroupOf N₁ := hxB
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    have hcomm : ∀ x ∈ N₁, x = 1 := by
      intro x hx
      refine hbot x hx ?_
      rw [hB, MonoidHom.mem_ker]
      change x.right = 1
      refine right_eq_one_of_commute_base fun c => ?_
      have hc : (inl c : (Fin n → P) ⋊[permAct (Fin n) P] Equiv.Perm (Fin n)) ∈ B := by
        rw [hB, MonoidHom.mem_ker]
        exact rightHom_inl c
      have h1 : x * inl c * x⁻¹ * (inl c)⁻¹ ∈ B :=
        B.mul_mem (hBn.conj_mem _ hc x) (B.inv_mem hc)
      have h2 : x * inl c * x⁻¹ * (inl c)⁻¹ ∈ N₁ := by
        have : x * (inl c * x⁻¹ * (inl c)⁻¹) ∈ N₁ :=
          N₁.mul_mem hx (Subgroup.Normal.conj_mem inferInstance _ (N₁.inv_mem hx) _)
        simpa [mul_assoc] using this
      have h4 : x * inl c * x⁻¹ = inl c := mul_inv_eq_one.1 (hbot _ h2 h1)
      rw [mul_inv_eq_iff_eq_mul] at h4
      exact h4
    obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (1 : N₁)
    exact hy1 (Subtype.ext (hcomm y hy))
  · have hle : N₁ ≤ B := Subgroup.subgroupOf_eq_top.1 h
    have hd := Subgroup.index_dvd_of_le hle
    rw [hidx, hB, index_ker_rightHom] at hd
    have h3 : n.factorial ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have h4 : (3 : ℕ).factorial ≤ n.factorial := Nat.factorial_le hn
    have : (3 : ℕ).factorial = 6 := rfl
    omega

end Wreath

section Simple

variable {G : Type*} [Group G] {N : Subgroup G}

private theorem eq_bot_or_le_of_normalized (hN : IsSimpleGroup N) {P : Subgroup G}
    (hP : ∀ p ∈ P, ∀ n ∈ N, n * p * n⁻¹ ∈ P) : P ⊓ N = ⊥ ∨ N ≤ P := by
  obtain ⟨-, h⟩ := Subgroup.isSimpleGroup_iff.1 hN
  have hnorm : ((P ⊓ N).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff inf_le_right).2 fun h k hh hk =>
      ⟨hP h hh.1 k hk, N.mul_mem (N.mul_mem hk hh.2) (N.inv_mem hk)⟩
  rcases h (P ⊓ N) inf_le_right hnorm with h | h
  · exact Or.inl h
  · exact Or.inr (h ▸ inf_le_left)

private theorem le_centralizer_of_inf_eq_bot [N.Normal] {P : Subgroup G}
    (hP : ∀ p ∈ P, ∀ n ∈ N, n * p * n⁻¹ ∈ P) (h : P ⊓ N = ⊥) :
    P ≤ Subgroup.centralizer (N : Set G) := by
  intro p hp
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have h1 : ⁅p, n⁆ ∈ P := by
    have : p * (n * p⁻¹ * n⁻¹) ∈ P := P.mul_mem hp (hP _ (P.inv_mem hp) n hn)
    simpa [commutatorElement_def, mul_assoc] using this
  have h2 : ⁅p, n⁆ ∈ N := by
    have : (p * n * p⁻¹) * n⁻¹ ∈ N :=
      N.mul_mem (Subgroup.Normal.conj_mem inferInstance n hn p) (N.inv_mem hn)
    simpa [commutatorElement_def, mul_assoc] using this
  have h3 : ⁅p, n⁆ ∈ P ⊓ N := ⟨h1, h2⟩
  rw [h, Subgroup.mem_bot] at h3
  exact (commutatorElement_eq_one_iff_mul_comm.1 h3).symm

private theorem le_of_normalized_ne_bot [N.Normal] (hN : IsSimpleGroup N)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) {P : Subgroup G}
    (hP : ∀ p ∈ P, ∀ n ∈ N, n * p * n⁻¹ ∈ P) (hP0 : P ≠ ⊥) : N ≤ P := by
  rcases eq_bot_or_le_of_normalized hN hP with h | h
  · exact absurd (le_bot_iff.1 ((le_centralizer_of_inf_eq_bot hP h).trans hC.le)) hP0
  · exact h

private theorem eq_bot_of_normalized_solvable [N.Normal] (hN : IsSimpleGroup N)
    (hns : ¬ Group.IsSolvable N) (hC : Subgroup.centralizer (N : Set G) = ⊥) {P : Subgroup G}
    (hP : ∀ p ∈ P, ∀ n ∈ N, n * p * n⁻¹ ∈ P) (hPs : Group.IsSolvable P) : P = ⊥ := by
  rcases eq_bot_or_le_of_normalized hN hP with h | h
  · exact le_bot_iff.1 ((le_centralizer_of_inf_eq_bot hP h).trans hC.le)
  · exact absurd (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h)) hns

private theorem isMinimalNormal_of_isSimpleGroup [N.Normal] (hN : IsSimpleGroup N) :
    IsMinimalNormal N := by
  refine ⟨inferInstance, (Subgroup.nontrivial_iff_ne_bot N).1 inferInstance, fun N' hN' hle => ?_⟩
  rcases eq_bot_or_le_of_normalized hN (P := N') (fun p hp n _ => hN'.conj_mem p hp n) with h | h
  · exact Or.inl (by rwa [inf_eq_left.2 hle] at h)
  · exact Or.inr (le_antisymm hle h)

end Simple

section Abstract

private theorem false_of_simple_index_two_extension (hBS : BenderSimpleInput)
    (hTO : TheoremOne) {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : IsSimpleGroup N) (hns : ¬ Group.IsSolvable N)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) {d : G} (hdN : d ∉ N) (hdd : d * d = 1)
    (hG : ∀ g : G, g ∈ N ∨ g * d ∈ N)
    (hodd : ∀ x y : G, IsConj d x → IsConj d y → orderOf (x * y) ∣ 2 ∨ Odd (orderOf (x * y)))
    {H : Subgroup G} (hH : H ≠ ⊤) (hdH : d ∈ H)
    (hcl : ∀ u : G, IsConj d u → u ∈ H → ∀ v : G, IsConj d v → Commute u v → v ∈ H) :
    False := by
  have hd1 : d ≠ 1 := fun h => hdN (h ▸ N.one_mem)
  have hidx : N.index = 2 := by
    refine Subgroup.index_eq_two_iff.2 ⟨d, fun b => ?_⟩
    by_cases hb : b ∈ N
    · refine Or.inr ⟨hb, fun h => hdN ?_⟩
      simpa using N.mul_mem (N.inv_mem hb) h
    · exact Or.inl ⟨(hG b).resolve_left hb, hb⟩
  have hord : ∀ x ∈ {g : G | IsConj d g}, orderOf x = 2 := by
    intro x hx
    obtain ⟨c, hc⟩ := isConj_iff.1 hx
    have h := orderOf_inv_mul_mul_eq c⁻¹ d
    rw [inv_inv] at h
    rw [← hc, h]
    exact orderOf_eq_prime (by rwa [pow_two]) hd1
  have hclos : Subgroup.closure {g : G | IsConj d g} = ⊤ := by
    have hnc : Subgroup.normalClosure {g : G | IsConj d g} =
        Subgroup.closure {g : G | IsConj d g} := by
      refine le_antisymm (Subgroup.closure_mono fun x hx => ?_)
        (Subgroup.closure_le _ |>.2 Subgroup.subset_normalClosure)
      obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.1 hx
      exact ha.trans hax
    have hPn : (Subgroup.closure {g : G | IsConj d g}).Normal :=
      hnc ▸ Subgroup.normalClosure_normal
    have hdP : d ∈ Subgroup.closure {g : G | IsConj d g} :=
      Subgroup.subset_closure (IsConj.refl d)
    have hNP : N ≤ Subgroup.closure {g : G | IsConj d g} :=
      le_of_normalized_ne_bot hN hC (fun p hp n _ => hPn.conj_mem p hp n)
        (fun h => hd1 (by rw [h] at hdP; exact hdP))
    refine eq_top_iff.2 fun g _ => ?_
    rcases hG g with h | h
    · exact hNP h
    · have := Subgroup.mul_mem _ (hNP h) hdP
      simpa [mul_assoc, hdd] using this
  have hrad : ∀ R : Subgroup G, R.Normal → Group.IsSolvable R → R = ⊥ := fun R hR hRs =>
    eq_bot_of_normalized_solvable hN hns hC (fun p hp n _ => hR.conj_mem p hp n) hRs
  rcases hTO G {g | IsConj d g} ⟨d, rfl⟩ hord (fun x hx y hy => hodd x y hx hy) hclos hrad
      ⟨H, hH, ⟨d, IsConj.refl d, hdH⟩, fun u hu huH v hv hc => hcl u hu huH v hv hc⟩ with
    hB | ⟨f, n, -, hn, ⟨e⟩⟩ | hA
  · have : IsSimpleGroup G := hBS G hB
    rcases Subgroup.Normal.eq_bot_or_eq_top N with h | h
    · exact (Subgroup.nontrivial_iff_ne_bot N).1 inferInstance h
    · exact hdN (h ▸ Subgroup.mem_top d)
  · have hn3 : 3 ≤ n := by omega
    have : (N.map (e : G →* L2Wreath f n)).Normal :=
      Subgroup.Normal.map inferInstance _ e.surjective
    have hN₁ : IsSimpleGroup (N.map (e : G →* L2Wreath f n)) :=
      (Subgroup.equivMapOfInjective N (e : G →* L2Wreath f n) e.injective).symm.isSimpleGroup
    have hidx₁ : (N.map (e : G →* L2Wreath f n)).index = 2 := by
      rw [Subgroup.index_map_of_bijective e.bijective N, hidx]
    exact not_simple_normal_index_two hn3 hN₁ hidx₁
  · obtain ⟨M, hMn, hMmin, huniq, -, -, hM2, -, -⟩ := hA
    have hNM := huniq N (isMinimalNormal_of_isSimpleGroup hN)
    rw [← hNM, hidx] at hM2
    omega

end Abstract

section Dihedral

variable {G : Type*} [Group G]

private theorem dihedral_even_class {S : Set G} {x y : G} (hx : x ∈ S) (hy : y ∈ S)
    (hxx : x * x = 1) (hyy : y * y = 1)
    (hS : ∀ g ∈ Subgroup.zpowers (x * y), ∀ s ∈ S, g⁻¹ * s * g ∈ S) {m : ℕ} (hm0 : 0 < m)
    (hm : orderOf (x * y) = 2 * m) :
    ∃ z : G, z * z = 1 ∧ z ≠ 1 ∧ x * z = z * x ∧ y * z = z * y ∧ x * z ∈ S ∧ y * z ∈ S := by
  have hzz : (x * y) ^ m * (x * y) ^ m = 1 := by
    rw [← pow_add, ← two_mul, ← hm]
    exact pow_orderOf_eq_one _
  have hzinv : ((x * y) ^ m)⁻¹ = (x * y) ^ m := inv_eq_of_mul_eq_one_right hzz
  have hxz : x * (x * y) ^ m = (x * y) ^ m * x := by
    have h1 : x * (x * y) ^ m * x⁻¹ = (x * y) ^ m := by
      rw [← conj_pow, left_invol_inverts hxx hyy, inv_pow, hzinv]
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hxw : x * (x * y) = y := by rw [← mul_assoc, hxx, one_mul]
  have hyz : y * (x * y) ^ m = (x * y) ^ m * y := by
    calc y * (x * y) ^ m = x * (x * y) * (x * y) ^ m := by rw [hxw]
      _ = x * ((x * y) * (x * y) ^ m) := mul_assoc _ _ _
      _ = x * ((x * y) ^ m * (x * y)) := by rw [(Commute.self_pow (x * y) m).eq]
      _ = (x * (x * y) ^ m) * (x * y) := (mul_assoc _ _ _).symm
      _ = ((x * y) ^ m * x) * (x * y) := by rw [hxz]
      _ = (x * y) ^ m * (x * (x * y)) := mul_assoc _ _ _
      _ = (x * y) ^ m * y := by rw [hxw]
  have hconj : ∀ (j : ℕ) (s : G), s ∈ S → ((x * y) ^ j)⁻¹ * s * (x * y) ^ j ∈ S :=
    fun j s hs => hS _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j) s hs
  refine ⟨(x * y) ^ m, hzz, pow_ne_one_of_lt_orderOf hm0.ne' (by omega), hxz, hyz, ?_⟩
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hx' : x * (x * y) ^ m = ((x * y) ^ k)⁻¹ * x * (x * y) ^ k := by
      rw [inv_pow_mul_mul_pow_of_inverts (left_invol_inverts hxx hyy) k,
        show 2 * k = m by omega, hzinv, hxz]
    have hy' : y * (x * y) ^ m = ((x * y) ^ k)⁻¹ * y * (x * y) ^ k := by
      rw [inv_pow_mul_mul_pow_of_inverts (right_invol_inverts hxx hyy) k,
        show 2 * k = m by omega, hzinv, hyz]
    exact ⟨hx' ▸ hconj k x hx, hy' ▸ hconj k y hy⟩
  · have hw : ((x * y) ^ (2 * k))⁻¹ = (x * y) ^ (m + 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add, show 2 * k + (m + 1) = orderOf (x * y) by omega]
      exact pow_orderOf_eq_one _
    have hx' : x * (x * y) ^ m = ((x * y) ^ k)⁻¹ * y * (x * y) ^ k := by
      rw [inv_pow_mul_mul_pow_of_inverts (right_invol_inverts hxx hyy) k, hw, pow_succ']
      have hxy : x * y * y = x := by rw [mul_assoc, hyy, mul_one]
      calc x * (x * y) ^ m = (x * y) * y * (x * y) ^ m := by rw [hxy]
        _ = (x * y) * (y * (x * y) ^ m) := mul_assoc _ _ _
        _ = (x * y) * ((x * y) ^ m * y) := by rw [hyz]
        _ = (x * y) * (x * y) ^ m * y := (mul_assoc _ _ _).symm
    have hy' : y * (x * y) ^ m = ((x * y) ^ (k + 1))⁻¹ * x * (x * y) ^ (k + 1) := by
      have h1 := inv_pow_mul_mul_pow_of_inverts (left_invol_inverts hxx hyy) (k + 1)
      calc y * (x * y) ^ m = (x * y)⁻¹ * x * (x * y) ^ m := by rw [← invol_eq_inv_mul_mul hyy]
        _ = (x * y)⁻¹ * ((x * y) ^ m * x) := by rw [mul_assoc, hxz]
        _ = (x * y)⁻¹ * (x * y) ^ m * x := (mul_assoc _ _ _).symm
        _ = ((x * y) ^ m * (x * y))⁻¹ * x := by rw [mul_inv_rev ((x * y) ^ m) (x * y), hzinv]
        _ = ((x * y) ^ (2 * (k + 1)))⁻¹ * x := by
          rw [show 2 * (k + 1) = m + 1 by omega, pow_succ]
        _ = ((x * y) ^ (k + 1))⁻¹ * x * (x * y) ^ (k + 1) := h1.symm
    exact ⟨hx' ▸ hconj k y hy, hy' ▸ hconj (k + 1) x hx⟩

end Dihedral

section Conjugates

variable {K : Type*} [Group K]

private def nConj (N : Subgroup K) (d : K) : Set K := {x | ∃ n ∈ N, x = n⁻¹ * d * n}

private theorem self_mem_nConj (N : Subgroup K) (d : K) : d ∈ nConj N d :=
  ⟨1, N.one_mem, by simp⟩

private theorem nConj_conj_mem {N : Subgroup K} {d x n : K} (hx : x ∈ nConj N d) (hn : n ∈ N) :
    n⁻¹ * x * n ∈ nConj N d := by
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨m * n, N.mul_mem hm hn, by group⟩

private theorem nConj_conj_self {N : Subgroup K} [N.Normal] {d x : K} (hdd : d * d = 1)
    (hx : x ∈ nConj N d) : d * x * d ∈ nConj N d := by
  obtain ⟨m, hm, rfl⟩ := hx
  have hinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  refine ⟨d * m * d⁻¹, Subgroup.Normal.conj_mem inferInstance m hm d, ?_⟩
  calc d * (m⁻¹ * d * m) * d = d * (m⁻¹ * d * m) * d⁻¹ := by rw [hinv]
    _ = (d * m * d⁻¹)⁻¹ * d * (d * m * d⁻¹) := by group

private theorem eq_one_or_eq_of_mem_zpowers {d h : K} (hdd : d * d = 1)
    (hh : h ∈ Subgroup.zpowers d) : h = 1 ∨ h = d := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  have hd2 : d ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hdd
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, hd2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, hd2, one_zpow, one_mul]

private theorem nConj_conj_mem_sup {N : Subgroup K} [N.Normal] {d x g : K} (hdd : d * d = 1)
    (hx : x ∈ nConj N d) (hg : g ∈ N ⊔ Subgroup.zpowers d) : g⁻¹ * x * g ∈ nConj N d := by
  obtain ⟨n, hn, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
  have hinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  rcases eq_one_or_eq_of_mem_zpowers hdd hh with rfl | rfl
  · simpa [mul_assoc] using nConj_conj_mem hx hn
  · have := nConj_conj_self hdd (nConj_conj_mem hx hn)
    simpa [mul_assoc, hinv] using this

private theorem mem_sup_of_mem_nConj {N : Subgroup K} {d x : K} (hx : x ∈ nConj N d) :
    x ∈ N ⊔ Subgroup.zpowers d := by
  obtain ⟨n, hn, rfl⟩ := hx
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (N.inv_mem hn))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))) (Subgroup.mem_sup_left hn)

private theorem nConj_mul_self {N : Subgroup K} {d x : K} (hdd : d * d = 1)
    (hx : x ∈ nConj N d) : x * x = 1 := by
  obtain ⟨n, hn, rfl⟩ := hx
  calc n⁻¹ * d * n * (n⁻¹ * d * n) = n⁻¹ * (d * d) * n := by group
    _ = 1 := by rw [hdd]; group

private theorem not_mem_of_mem_nConj {N : Subgroup K} [N.Normal] {d x : K} (hdN : d ∉ N)
    (hx : x ∈ nConj N d) : x ∉ N := by
  obtain ⟨n, hn, rfl⟩ := hx
  intro h
  apply hdN
  have := Subgroup.Normal.conj_mem inferInstance _ h n
  simpa [mul_assoc] using this

private theorem exists_conj_of_mem_nConj {N : Subgroup K} {d u v : K} (hu : u ∈ nConj N d)
    (hv : v ∈ nConj N d) : ∃ k ∈ N, v = k⁻¹ * u * k := by
  obtain ⟨n₁, hn₁, rfl⟩ := hu
  obtain ⟨n₂, hn₂, rfl⟩ := hv
  exact ⟨n₁⁻¹ * n₂, N.mul_mem (N.inv_mem hn₁) hn₂, by group⟩

private theorem mem_conjSubgroup_of_eq {T : Subgroup K} {d u n : K} (hdT : d ∈ T)
    (hu : u = n⁻¹ * d * n) : u ∈ conjSubgroup n⁻¹ T := by
  rw [mem_conjSubgroup, hu]
  simpa [mul_assoc] using hdT

end Conjugates

section Weakly

variable {K : Type*} [Group K] [Finite K] {T N : Subgroup K} [N.Normal]

private theorem commute_mem_of_mem_nConj (hT : IsWC T) {d : K} (hdN : d ∉ N) {u v : K}
    (hu : u ∈ nConj N d) (huT : u ∈ T) (hv : v ∈ nConj N d) (hcomm : u * v = v * u) :
    v ∈ T := by
  obtain ⟨k, hk, rfl⟩ := exists_conj_of_mem_nConj hu hv
  exact commute_conj_mem_of_not_mem_normal hT N huT (not_mem_of_mem_nConj hdN hu) hk hcomm

private theorem commute_mem_conjSubgroup (hT : IsWC T) {d : K} (hdT : d ∈ T) (hdN : d ∉ N)
    {n : K} {u v : K} (hu : u = n⁻¹ * d * n) (hn : n ∈ N) (hv : v ∈ nConj N d)
    (hcomm : u * v = v * u) : v ∈ conjSubgroup n⁻¹ T := by
  have hu' : u ∈ nConj N d := ⟨n, hn, hu⟩
  obtain ⟨k, hk, rfl⟩ := exists_conj_of_mem_nConj hu' hv
  exact commute_conj_mem_of_not_mem_normal (hT.conj n⁻¹) N (mem_conjSubgroup_of_eq hdT hu)
    (not_mem_of_mem_nConj hdN hu') hk hcomm

private theorem orderOf_mul_nConj (hT : IsWC T) {d : K} (hdT : d ∈ T) (hdN : d ∉ N) {x y : K}
    (hx : x ∈ nConj N d) (hy : y ∈ nConj N d) :
    orderOf (x * y) ∣ 2 ∨ Odd (orderOf (x * y)) := by
  have hdd : d * d = 1 := elemAbelian_mul_self hT.1 hdT
  have hxx : x * x = 1 := nConj_mul_self hdd hx
  have hyy : y * y = 1 := nConj_mul_self hdd hy
  by_cases hcomm : x * y = y * x
  · exact Or.inl ((orderOf_mul_dvd_two_iff_commute hxx hyy).2 hcomm)
  rcases Nat.even_or_odd (orderOf (x * y)) with ⟨m, hm⟩ | hodd
  swap
  · exact Or.inr hodd
  exfalso
  have hm0 : 0 < m := by
    have := orderOf_pos (x * y)
    omega
  have hS : ∀ g ∈ Subgroup.zpowers (x * y), ∀ s ∈ nConj N d, g⁻¹ * s * g ∈ nConj N d := by
    intro g hg s hs
    refine nConj_conj_mem_sup hdd hs ?_
    have : x * y ∈ N ⊔ Subgroup.zpowers d :=
      Subgroup.mul_mem _ (mem_sup_of_mem_nConj hx) (mem_sup_of_mem_nConj hy)
    exact (Subgroup.zpowers_le.2 this) hg
  obtain ⟨z, -, hz1, hxz, hyz, hxzS, hyzS⟩ :=
    dihedral_even_class hx hy hxx hyy hS hm0 (by omega)
  obtain ⟨n₁, hn₁, hx₁⟩ := hx
  obtain ⟨n₂, hn₂, hy₂⟩ := hy
  have hxT : x ∈ conjSubgroup n₁⁻¹ T := mem_conjSubgroup_of_eq hdT hx₁
  have hyT : y ∈ conjSubgroup n₂⁻¹ T := mem_conjSubgroup_of_eq hdT hy₂
  have hxzT : x * z ∈ conjSubgroup n₁⁻¹ T :=
    commute_mem_conjSubgroup hT hdT hdN hx₁ hn₁ hxzS (calc
      x * (x * z) = x * (z * x) := by rw [hxz]
      _ = x * z * x := (mul_assoc _ _ _).symm)
  have hyzT : y * z ∈ conjSubgroup n₂⁻¹ T :=
    commute_mem_conjSubgroup hT hdT hdN hy₂ hn₂ hyzS (calc
      y * (y * z) = y * (z * y) := by rw [hyz]
      _ = y * z * y := (mul_assoc _ _ _).symm)
  have hzTx : z ∈ conjSubgroup n₁⁻¹ T := by
    have := (conjSubgroup n₁⁻¹ T).mul_mem hxT hxzT
    rwa [← mul_assoc, hxx, one_mul] at this
  have hzTy : z ∈ conjSubgroup n₂⁻¹ T := by
    have := (conjSubgroup n₂⁻¹ T).mul_mem hyT hyzT
    rwa [← mul_assoc, hyy, one_mul] at this
  have hconjeq : conjSubgroup (n₂⁻¹ * n₁) (conjSubgroup n₁⁻¹ T) = conjSubgroup n₂⁻¹ T := by
    rw [conjSubgroup_conjSubgroup, show n₂⁻¹ * n₁ * n₁⁻¹ = n₂⁻¹ by group]
  have hTT : conjSubgroup n₂⁻¹ T = conjSubgroup n₁⁻¹ T := by
    rw [← hconjeq]
    refine (hT.conj n₁⁻¹).conj_eq_of_inf_ne_bot fun hbot => hz1 ?_
    have : z ∈ conjSubgroup n₁⁻¹ T ⊓ conjSubgroup (n₂⁻¹ * n₁) (conjSubgroup n₁⁻¹ T) :=
      ⟨hzTx, hconjeq ▸ hzTy⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  exact hcomm (elemAbelian_mul_comm (hT.conj n₁⁻¹).1 hxT (hTT ▸ hyT))

end Weakly

section Main

private theorem false_of_mem_not_mem_normal (hBS : BenderSimpleInput) (hTO : TheoremOne)
    {K : Type} [Group K] [Finite K] {T N : Subgroup K} [N.Normal] (hT : IsWC T)
    (hN : IsSimpleGroup N) (hns : ¬ Group.IsSolvable N)
    (hC : Subgroup.centralizer (N : Set K) = ⊥) {d : K} (hdT : d ∈ T) (hdN : d ∉ N) :
    False := by
  have hdd : d * d = 1 := elemAbelian_mul_self hT.1 hdT
  set G₀ : Subgroup K := N ⊔ Subgroup.zpowers d
  have hNG : N ≤ G₀ := le_sup_left
  have hdG : d ∈ G₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  have hconj : ∀ x : G₀, IsConj (⟨d, hdG⟩ : G₀) x → (x : K) ∈ nConj N d := by
    intro x hx
    obtain ⟨c, hc⟩ := isConj_iff.1 hx
    have h := nConj_conj_mem_sup hdd (self_mem_nConj N d) (g := (c : K)⁻¹) (G₀.inv_mem c.2)
    rw [inv_inv] at h
    have hcx : (c : K) * d * (c : K)⁻¹ = x := congrArg Subtype.val hc
    rwa [hcx] at h
  have hN' : IsSimpleGroup (N.subgroupOf G₀) := (Subgroup.subgroupOfEquivOfLe hNG).isSimpleGroup
  have hns' : ¬ Group.IsSolvable (N.subgroupOf G₀) := fun h =>
    hns (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNG).symm.toMonoidHom) (MulEquiv.injective _))
  have hC' : Subgroup.centralizer ((N.subgroupOf G₀ : Subgroup G₀) : Set G₀) = ⊥ := by
    refine eq_bot_iff.2 fun g hg => ?_
    rw [Subgroup.mem_bot]
    have : (g : K) ∈ Subgroup.centralizer (N : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have := Subgroup.mem_centralizer_iff.1 hg ⟨n, hNG hn⟩ (Subgroup.mem_subgroupOf.2 hn)
      exact congrArg Subtype.val this
    rw [hC, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hdN' : (⟨d, hdG⟩ : G₀) ∉ N.subgroupOf G₀ := fun h => hdN (Subgroup.mem_subgroupOf.1 h)
  have hdd' : (⟨d, hdG⟩ : G₀) * ⟨d, hdG⟩ = 1 := Subtype.ext hdd
  have hG' : ∀ g : G₀, g ∈ N.subgroupOf G₀ ∨ g * ⟨d, hdG⟩ ∈ N.subgroupOf G₀ := by
    intro g
    obtain ⟨n, hn, h, hh, hg⟩ := Subgroup.mem_sup_of_normal_left.1 g.2
    rcases eq_one_or_eq_of_mem_zpowers hdd hh with rfl | rfl
    · left
      rw [Subgroup.mem_subgroupOf]
      simpa [← hg] using hn
    · right
      rw [Subgroup.mem_subgroupOf]
      have : (g : K) = n * h := hg.symm
      simp [this, mul_assoc, hdd, hn]
  have hodd' : ∀ x y : G₀, IsConj (⟨d, hdG⟩ : G₀) x → IsConj (⟨d, hdG⟩ : G₀) y →
      orderOf (x * y) ∣ 2 ∨ Odd (orderOf (x * y)) := by
    intro x y hx hy
    have h := orderOf_mul_nConj hT hdT hdN (hconj x hx) (hconj y hy)
    rwa [← Subgroup.coe_mul, Subgroup.orderOf_coe] at h
  have hH' : T.subgroupOf G₀ ≠ ⊤ := fun h => hns <| Group.isSolvable_of_comm fun a b =>
    Subtype.ext (elemAbelian_mul_comm hT.1 ((Subgroup.subgroupOf_eq_top.1 h) (hNG a.2))
      ((Subgroup.subgroupOf_eq_top.1 h) (hNG b.2)))
  have hcl' : ∀ u : G₀, IsConj (⟨d, hdG⟩ : G₀) u → u ∈ T.subgroupOf G₀ → ∀ v : G₀,
      IsConj (⟨d, hdG⟩ : G₀) v → Commute u v → v ∈ T.subgroupOf G₀ := by
    intro u hu huH v hv hc
    exact Subgroup.mem_subgroupOf.2 (commute_mem_of_mem_nConj hT hdN (hconj u hu)
      (Subgroup.mem_subgroupOf.1 huH) (hconj v hv) (congrArg Subtype.val hc.eq))
  exact false_of_simple_index_two_extension hBS hTO (N.subgroupOf G₀) hN' hns' hC' hdN' hdd' hG'
    hodd' hH' (Subgroup.mem_subgroupOf.2 hdT) hcl'

end Main

theorem lemma215_of_inputs (h213 : Lemma213Stmt) (hBS : BenderSimpleInput)
    (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) : Lemma215Stmt := by
  intro K _ _ T hT h4 hK hS
  obtain ⟨N, hNn, hN0, hNs, -, hNmin⟩ := h213 K T hT h4 hK hS
  have hns : ¬ Group.IsSolvable N := fun h => hN0 (hS N hNn h)
  have hC : Subgroup.centralizer (N : Set K) = ⊥ := by
    by_contra hne
    have hle : N ≤ Subgroup.centralizer (N : Set K) := hNmin _ Subgroup.normal_centralizer hne
    refine hns (Group.isSolvable_of_comm fun a b => Subtype.ext ?_)
    exact Subgroup.mem_centralizer_iff.1 (hle b.2) a a.2
  have hTN : T ≤ N := fun d hdT => by
    by_contra hdN
    exact false_of_mem_not_mem_normal hBS hTO hT hNs hns hC hdT hdN
  have htop : N = ⊤ := top_le_iff.1 (hK ▸ Subgroup.normalClosure_le_normal hTN)
  subst htop
  exact Subgroup.topEquiv.symm.isSimpleGroup

end CFSG.CGT.Timmesfeld75
