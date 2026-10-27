module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Wreath
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Cm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Prod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbDefs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G]

private noncomputable def zmodPowHom {H : Type*} [Group H] (m : ℕ) [NeZero m] (a : H)
    (ha : orderOf a = m) : Multiplicative (ZMod m) →* H where
  toFun i := a ^ i.toAdd.val
  map_one' := by
    show a ^ (Multiplicative.toAdd (1 : Multiplicative (ZMod m))).val = 1
    rw [toAdd_one, ZMod.val_zero, pow_zero]
  map_mul' i k := by
    show a ^ (Multiplicative.toAdd (i * k)).val =
      a ^ (Multiplicative.toAdd i).val * a ^ (Multiplicative.toAdd k).val
    rw [toAdd_mul, ZMod.val_add]
    rw [show ((Multiplicative.toAdd i).val + (Multiplicative.toAdd k).val) % m =
        ((Multiplicative.toAdd i).val + (Multiplicative.toAdd k).val) % orderOf a by rw [ha]]
    rw [pow_mod_orderOf, pow_add]

@[simp] private theorem zmodPowHom_ofAdd_apply {H : Type*} [Group H] (m : ℕ) [NeZero m]
    (a : H) (ha : orderOf a = m) (i : ZMod m) :
    zmodPowHom m a ha (Multiplicative.ofAdd i) = a ^ i.val := rfl

theorem isZ4Z4E4_of_abelian {Q : Subgroup G} {x₁ x₂ lam : G} (hw : WreathRel x₁ x₂ lam)
    (hx₁ : x₁ ∈ Q) (hx₂ : x₂ ∈ Q) (hab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (hcard : Nat.card Q = 64) (hsq : ∀ a ∈ Q, a ^ 2 ∈ fourGrp x₁ x₂) : IsZ4Z4E4 Q := by
  classical
  letI : CommGroup Q := { (inferInstance : Group Q) with
    mul_comm := fun a b => Subtype.ext (hab a.1 a.2 b.1 b.2) }
  have hB_le_Q : baseGrp x₁ x₂ ≤ Q := by
    rw [hw.baseGrp_eq.2.1]
    exact sup_le (Subgroup.zpowers_le.mpr hx₁) (Subgroup.zpowers_le.mpr hx₂)
  have hV_le_B : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
    rw [fourGrp, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact (baseGrp x₁ x₂).pow_mem (Subgroup.subset_closure (by simp)) 2
    · exact (baseGrp x₁ x₂).pow_mem
        ((baseGrp x₁ x₂).mul_mem (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))) 2
  let sq : Q →* Q := powMonoidHom 2
  let Ω : Subgroup G := sq.ker.map Q.subtype
  have mem_Ω : ∀ a : G, a ∈ Ω ↔ a ∈ Q ∧ a ^ 2 = 1 := by
    intro a
    change a ∈ Subgroup.map Q.subtype sq.ker ↔ a ∈ Q ∧ a ^ 2 = 1
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hq2 : q ^ 2 = 1 := by simpa [sq] using hq
      exact ⟨q.2, by simpa using congrArg Subtype.val hq2⟩
    · rintro ⟨haQ, ha2⟩
      refine ⟨⟨a, haQ⟩, ?_, rfl⟩
      show (⟨a, haQ⟩ : Q) ∈ sq.ker
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      simpa [sq] using ha2
  have hrange_map : sq.range.map Q.subtype = fourGrp x₁ x₂ := by
    apply le_antisymm
    · rintro a ⟨q, hq, rfl⟩
      obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hq
      have h : ((r : G) ^ 2) ∈ fourGrp x₁ x₂ := hsq r r.2
      simpa [sq] using h
    · rw [hw.fourGrp_eq_mho, Subgroup.closure_le]
      rintro g ⟨a, ha, rfl⟩
      have hmem : sq ⟨a, hB_le_Q ha⟩ ∈ sq.range :=
        MonoidHom.mem_range.mpr ⟨_, rfl⟩
      have := Subgroup.mem_map_of_mem Q.subtype hmem
      simpa [sq] using this
  have hcard_range : Nat.card sq.range = 4 := by
    rw [← Subgroup.card_map_of_injective (K := sq.range) Q.subtype_injective, hrange_map,
      hw.fourGrp_eq_omega.2.2]
  have hcard_ker : Nat.card sq.ker = 16 := by
    have h := Subgroup.card_ker_mul_card_range sq
    rw [hcard_range, hcard] at h
    omega
  have hcard_Ω : Nat.card Ω = 16 := by
    change Nat.card (sq.ker.map Q.subtype) = 16
    rw [Subgroup.card_map_of_injective (K := sq.ker) Q.subtype_injective, hcard_ker]
  have hV_le_Ω : fourGrp x₁ x₂ ≤ Ω := by
    intro v hv
    rw [mem_Ω v]
    exact ⟨hB_le_Q (hV_le_B hv), (hw.fourGrp_eq_omega.2.1).2 v hv⟩
  have hΩB : Ω ⊓ baseGrp x₁ x₂ = fourGrp x₁ x₂ := by
    apply le_antisymm
    · intro x hx
      have hx' := (mem_Ω x).mp hx.1
      rw [(hw.fourGrp_eq_omega).1]
      exact Subgroup.subset_closure ⟨hx.2, hx'.2⟩
    · intro x hx
      exact ⟨hV_le_Ω hx, hV_le_B hx⟩
  have hexists1 : ∃ e ∈ Ω, e ∉ fourGrp x₁ x₂ := by
    by_contra h
    push Not at h
    have hle : Ω ≤ fourGrp x₁ x₂ := fun e he => h e he
    have hc := Subgroup.card_le_of_le hle
    rw [hcard_Ω, hw.fourGrp_eq_omega.2.2] at hc
    omega
  obtain ⟨e1, he1Ω, he1V⟩ := hexists1
  have he1Q : e1 ∈ Q := ((mem_Ω e1).mp he1Ω).1
  have he1sq : e1 ^ 2 = 1 := ((mem_Ω e1).mp he1Ω).2
  have he1ne : e1 ≠ 1 := by
    intro h
    rw [h] at he1V
    exact he1V (fourGrp x₁ x₂).one_mem
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord_e1 : orderOf e1 = 2 := orderOf_eq_prime he1sq he1ne
  have he1mul : e1 * e1 = 1 := by simpa [pow_two] using he1sq
  have hord_e1_int : (orderOf e1 : ℤ) = 2 := by rw [hord_e1]; norm_num
  have hmem1 : ∀ x : G, x ∈ zpowers e1 ↔ x = 1 ∨ x = e1 := by
    intro x
    constructor
    · intro hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_mod_orderOf e1 n, hord_e1_int]
      rcases Int.emod_two_eq_zero_or_one n with h | h
      · left; rw [h]; simp
      · right; rw [h]; simp
    · rintro (h | h)
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers e1
  have hV1disj : fourGrp x₁ x₂ ⊓ zpowers e1 = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rcases (hmem1 x).mp hx.2 with rfl | rfl
    · exact Subgroup.mem_bot.mpr rfl
    · exact absurd hx.1 he1V
  have hcard_V1 : Nat.card ↥(fourGrp x₁ x₂ ⊔ zpowers e1) = 8 := by
    have hnorm : ∀ k ∈ zpowers e1, ∀ h ∈ fourGrp x₁ x₂, k * h * k⁻¹ ∈ fourGrp x₁ x₂ := by
      intro k hk h hh
      have hkQ : k ∈ Q := Subgroup.zpowers_le.mpr he1Q hk
      have hhQ : h ∈ Q := hB_le_Q (hV_le_B hh)
      rw [hab k hkQ h hhQ, mul_assoc, mul_inv_cancel, mul_one]
      exact hh
    have h := card_sup_eq_mul hnorm hV1disj
    rw [hw.fourGrp_eq_omega.2.2, Nat.card_zpowers, hord_e1] at h
    exact h
  have hexists2 : ∃ e ∈ Ω, e ∉ fourGrp x₁ x₂ ⊔ zpowers e1 := by
    by_contra h
    push Not at h
    have hle : Ω ≤ fourGrp x₁ x₂ ⊔ zpowers e1 := fun e he => h e he
    have hc := Subgroup.card_le_of_le hle
    rw [hcard_Ω, hcard_V1] at hc
    omega
  obtain ⟨e2, he2Ω, he2notin⟩ := hexists2
  have he2Q : e2 ∈ Q := ((mem_Ω e2).mp he2Ω).1
  have he2sq : e2 ^ 2 = 1 := ((mem_Ω e2).mp he2Ω).2
  have he2ne : e2 ≠ 1 := by
    intro h
    rw [h] at he2notin
    exact he2notin (Subgroup.mem_sup_left (fourGrp x₁ x₂).one_mem)
  have hord_e2 : orderOf e2 = 2 := orderOf_eq_prime he2sq he2ne
  have he2mul : e2 * e2 = 1 := by simpa [pow_two] using he2sq
  let E : Subgroup G := zpowers e1 ⊔ zpowers e2
  have hEeq : E = closure ({e1, e2} : Set G) := by
    change zpowers e1 ⊔ zpowers e2 = closure ({e1, e2} : Set G)
    rw [Subgroup.zpowers_eq_closure e1, Subgroup.zpowers_eq_closure e2,
      ← Subgroup.closure_union]
    congr 1
  have hEV : fourGrp x₁ x₂ ⊓ E = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [hEeq] at hx
    have hcomm : e1 * e2 = e2 * e1 := hab e1 he1Q e2 he2Q
    rcases (mem_closure_pair_of_invol (a := e1) (b := e2) (x := x) he1mul he2mul hcomm).mp
      hx.2 with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_bot.mpr rfl
    · exact absurd hx.1 he1V
    · exact absurd (Subgroup.mem_sup_left hx.1) he2notin
    · have h1 : e1⁻¹ * (e1 * e2) ∈ fourGrp x₁ x₂ ⊔ zpowers e1 :=
        (fourGrp x₁ x₂ ⊔ zpowers e1).mul_mem
          (Subgroup.mem_sup_right ((zpowers e1).inv_mem (Subgroup.mem_zpowers e1)))
          (Subgroup.mem_sup_left hx.1)
      exact absurd (by simpa using h1) he2notin
  have hord_e2_int : (orderOf e2 : ℤ) = 2 := by rw [hord_e2]; norm_num
  have hmem2 : ∀ x : G, x ∈ zpowers e2 ↔ x = 1 ∨ x = e2 := by
    intro x
    constructor
    · intro hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_mod_orderOf e2 n, hord_e2_int]
      rcases Int.emod_two_eq_zero_or_one n with h | h
      · left; rw [h]; simp
      · right; rw [h]; simp
    · rintro (h | h)
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers e2
  have hE12 : zpowers e1 ⊓ zpowers e2 = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rcases (hmem1 x).mp hx.1 with h1 | h1
    · rw [h1]; exact Subgroup.mem_bot.mpr rfl
    · rw [h1] at hx ⊢
      rcases (hmem2 e1).mp hx.2 with h2 | h2
      · exact absurd h2 he1ne
      · have : e2 ∈ fourGrp x₁ x₂ ⊔ zpowers e1 := by
          rw [← h2]
          exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e1)
        exact absurd this he2notin
  let a₁ : Q := ⟨x₁, hx₁⟩
  let a₂ : Q := ⟨x₂, hx₂⟩
  let b₁ : Q := ⟨e1, he1Q⟩
  let b₂ : Q := ⟨e2, he2Q⟩
  have hord_a₁ : orderOf a₁ = 4 := by
    have h := orderOf_injective Q.subtype Q.subtype_injective a₁
    have hx : Q.subtype a₁ = x₁ := rfl
    rw [← h, hx]
    exact hw.ord_x₁
  have hord_a₂ : orderOf a₂ = 4 := by
    have h := orderOf_injective Q.subtype Q.subtype_injective a₂
    have hx : Q.subtype a₂ = x₂ := rfl
    rw [← h, hx]
    exact hw.ord_x₂
  have hord_b₁ : orderOf b₁ = 2 := by
    have h := orderOf_injective Q.subtype Q.subtype_injective b₁
    have hx : Q.subtype b₁ = e1 := rfl
    rw [← h, hx]
    exact hord_e1
  have hord_b₂ : orderOf b₂ = 2 := by
    have h := orderOf_injective Q.subtype Q.subtype_injective b₂
    have hx : Q.subtype b₂ = e2 := rfl
    rw [← h, hx]
    exact hord_e2
  let φ₁ : Multiplicative (ZMod 4) →* Q := zmodPowHom 4 a₁ hord_a₁
  let φ₂ : Multiplicative (ZMod 4) →* Q := zmodPowHom 4 a₂ hord_a₂
  let ψ₁ : Multiplicative (ZMod 2) →* Q := zmodPowHom 2 b₁ hord_b₁
  let ψ₂ : Multiplicative (ZMod 2) →* Q := zmodPowHom 2 b₂ hord_b₂
  let σ : Multiplicative (ZMod 2 × ZMod 2) →* Q :=
    (MonoidHom.noncommCoprod ψ₁ ψ₂ (fun _ _ => mul_comm _ _)).comp
      (MulEquiv.prodMultiplicative (ZMod 2) (ZMod 2))
  let θ : Multiplicative (ZMod 4 × (ZMod 2 × ZMod 2)) →* Q :=
    (MonoidHom.noncommCoprod φ₂ σ (fun _ _ => mul_comm _ _)).comp
      (MulEquiv.prodMultiplicative (ZMod 4) (ZMod 2 × ZMod 2))
  let g : Outside.Z4Z4Z2Z2 →* Q :=
    (MonoidHom.noncommCoprod φ₁ θ (fun _ _ => mul_comm _ _)).comp
      (MulEquiv.prodMultiplicative (ZMod 4) (ZMod 4 × (ZMod 2 × ZMod 2)))
  have hg_eval : ∀ (i j : ZMod 4) (k l : ZMod 2),
      g (Multiplicative.ofAdd (i, (j, (k, l)))) =
        a₁ ^ i.val * (a₂ ^ j.val * (b₁ ^ k.val * b₂ ^ l.val)) := by
    intro i j k l
    rfl
  have hcoord : ∀ (i j : ZMod 4) (k l : ZMod 2),
      g (Multiplicative.ofAdd (i, (j, (k, l)))) = 1 → i = 0 ∧ j = 0 ∧ k = 0 ∧ l = 0 := by
    intro i j k l hg
    have heqQ : a₁ ^ i.val * (a₂ ^ j.val * (b₁ ^ k.val * b₂ ^ l.val)) = 1 := by
      rw [hg_eval i j k l] at hg
      exact hg
    have heqG : x₁ ^ i.val * (x₂ ^ j.val * (e1 ^ k.val * e2 ^ l.val)) = 1 := by
      have := congrArg Subtype.val heqQ
      simpa using this
    set w : G := e1 ^ k.val * e2 ^ l.val with hwdef
    have hw_eq : w = (x₁ ^ i.val * x₂ ^ j.val)⁻¹ := by
      have h : (x₁ ^ i.val * x₂ ^ j.val) * w = 1 := by
        rw [mul_assoc, hwdef]
        exact heqG
      exact eq_inv_of_mul_eq_one_right h
    have hwΩ : w ∈ Ω := by
      rw [hwdef]
      exact Ω.mul_mem (Ω.pow_mem he1Ω k.val) (Ω.pow_mem he2Ω l.val)
    have hwB : w ∈ baseGrp x₁ x₂ := by
      rw [hw_eq]
      exact (baseGrp x₁ x₂).inv_mem
        ((baseGrp x₁ x₂).mul_mem
          ((baseGrp x₁ x₂).pow_mem (Subgroup.subset_closure (by simp)) i.val)
          ((baseGrp x₁ x₂).pow_mem (Subgroup.subset_closure (by simp)) j.val))
    have hwV : w ∈ fourGrp x₁ x₂ := by
      have h : w ∈ Ω ⊓ baseGrp x₁ x₂ := ⟨hwΩ, hwB⟩
      rwa [hΩB] at h
    have hwE : w ∈ E := by
      rw [hwdef]
      exact E.mul_mem (Subgroup.mem_sup_left (Subgroup.npow_mem_zpowers e1 k.val))
        (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers e2 l.val))
    have hw1 : w = 1 := by
      have h : w ∈ fourGrp x₁ x₂ ⊓ E := ⟨hwV, hwE⟩
      rw [hEV] at h
      exact Subgroup.mem_bot.mp h
    have hprod : x₁ ^ i.val * x₂ ^ j.val = 1 := by
      have h := hw_eq
      rw [hw1] at h
      have h2 := congrArg Inv.inv h
      simpa using h2.symm
    have hx1i : x₁ ^ i.val = (x₂ ^ j.val)⁻¹ := by
      calc x₁ ^ i.val = (x₁ ^ i.val * x₂ ^ j.val) * (x₂ ^ j.val)⁻¹ := by group
        _ = (x₂ ^ j.val)⁻¹ := by rw [hprod, one_mul]
    have hx1i1 : x₁ ^ i.val = 1 := by
      have h : x₁ ^ i.val ∈ zpowers x₁ ⊓ zpowers x₂ := by
        refine ⟨Subgroup.npow_mem_zpowers x₁ i.val, ?_⟩
        rw [hx1i]
        exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers x₂ j.val)
      rw [hw.inf_eq_bot] at h
      exact Subgroup.mem_bot.mp h
    have hi_dvd : 4 ∣ i.val := by
      have h := (orderOf_dvd_iff_pow_eq_one (x := x₁) (n := i.val)).mpr hx1i1
      rwa [hw.ord_x₁] at h
    have hi : i = 0 := by
      have hlt : i.val < 4 := ZMod.val_lt i
      have hv : i.val = 0 := by omega
      exact ZMod.val_injective 4 (by simp [hv])
    have hj1 : x₂ ^ j.val = 1 := by
      have h := hprod
      rw [hx1i1, one_mul] at h
      exact h
    have hj_dvd : 4 ∣ j.val := by
      have h := (orderOf_dvd_iff_pow_eq_one (x := x₂) (n := j.val)).mpr hj1
      rwa [hw.ord_x₂] at h
    have hj : j = 0 := by
      have hlt : j.val < 4 := ZMod.val_lt j
      have hv : j.val = 0 := by omega
      exact ZMod.val_injective 4 (by simp [hv])
    have hw1' : e1 ^ k.val * e2 ^ l.val = 1 := by
      rw [hwdef] at hw1
      exact hw1
    have he1k : e1 ^ k.val = (e2 ^ l.val)⁻¹ := by
      calc e1 ^ k.val = (e1 ^ k.val * e2 ^ l.val) * (e2 ^ l.val)⁻¹ := by group
        _ = (e2 ^ l.val)⁻¹ := by rw [hw1', one_mul]
    have he1k1 : e1 ^ k.val = 1 := by
      have h : e1 ^ k.val ∈ zpowers e1 ⊓ zpowers e2 := by
        refine ⟨Subgroup.npow_mem_zpowers e1 k.val, ?_⟩
        rw [he1k]
        exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers e2 l.val)
      rw [hE12] at h
      exact Subgroup.mem_bot.mp h
    have hk_dvd : 2 ∣ k.val := by
      have h := (orderOf_dvd_iff_pow_eq_one (x := e1) (n := k.val)).mpr he1k1
      rwa [hord_e1] at h
    have hk : k = 0 := by
      have hlt : k.val < 2 := ZMod.val_lt k
      have hv : k.val = 0 := by omega
      exact ZMod.val_injective 2 (by simp [hv])
    have hl1 : e2 ^ l.val = 1 := by
      have h := hw1'
      rw [he1k1, one_mul] at h
      exact h
    have hl_dvd : 2 ∣ l.val := by
      have h := (orderOf_dvd_iff_pow_eq_one (x := e2) (n := l.val)).mpr hl1
      rwa [hord_e2] at h
    have hl : l = 0 := by
      have hlt : l.val < 2 := ZMod.val_lt l
      have hv : l.val = 0 := by omega
      exact ZMod.val_injective 2 (by simp [hv])
    exact ⟨hi, hj, hk, hl⟩
  have hker : ∀ z : Outside.Z4Z4Z2Z2, g z = 1 → z = 1 := by
    intro z hz
    have hz' : g (Multiplicative.ofAdd (z.toAdd.1,
        (z.toAdd.2.1, (z.toAdd.2.2.1, z.toAdd.2.2.2)))) = 1 := by
      simpa using hz
    obtain ⟨hi, hj, hk, hl⟩ := hcoord _ _ _ _ hz'
    have hz_eq : z = Multiplicative.ofAdd (z.toAdd.1,
        (z.toAdd.2.1, (z.toAdd.2.2.1, z.toAdd.2.2.2))) := rfl
    rw [hz_eq, hi, hj, hk, hl]
    rfl
  have hinj : Function.Injective g := by
    intro x y hxy
    have h1 : g (x * y⁻¹) = 1 := by
      have h2 : g (y⁻¹) = (g y)⁻¹ := map_inv g y
      rw [map_mul, hxy, h2]
      exact mul_inv_cancel (g y)
    exact mul_inv_eq_one.mp (hker _ h1)
  have hsurj : Function.Surjective g := by
    have hcard_dom : Nat.card Outside.Z4Z4Z2Z2 = 64 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    have hrange : g.range = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcard_dom, hcard]
    exact MonoidHom.range_eq_top.mp hrange
  exact ⟨(MulEquiv.ofBijective g ⟨hinj, hsurj⟩).symm⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
