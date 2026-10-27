module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4ModIsoAct

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.OddStandard.AltStdSmall4.HbarCoords

open Subgroup Equiv Matrix ModIso
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
open scoped Pointwise

section Coords

theorem v3_add_self (v : Fin 3 → ZMod 2) : v + v = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize v i = a
  revert a
  decide

variable {G : Type} [Group G] {z : G} {T : Subgroup G} {κ : GL (Fin 3) (ZMod 2) →* G}
  {E₀ : Subgroup G} {cT : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G} (hc : TCoords z T κ E₀ cT)

include hc

theorem cT_zero : cT 0 0 = 1 := by
  have h : cT (0 + 0) (0 + 0) = cT 0 0 * cT 0 0 := hc.add 0 0 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := cT 0 0) (by rw [mul_one]; exact h.symm)

theorem cT_mul_self (v w : Fin 3 → ZMod 2) : cT v w * cT v w = 1 := by
  rw [← hc.add, v3_add_self, v3_add_self, cT_zero hc]

theorem cT_eq_iff {v w v' w' : Fin 3 → ZMod 2} : cT v w = cT v' w' ↔ v = v' ∧ w = w' := by
  refine ⟨fun h => ?_, fun h => by rw [h.1, h.2]⟩
  have h1 : cT (v + v') (w + w') = 1 := by rw [hc.add, h, cT_mul_self hc]
  obtain ⟨h2, h3⟩ := hc.inj _ _ h1
  have key : ∀ a b : Fin 3 → ZMod 2, a + b = 0 → a = b := fun a b hab => by
    calc a = a + (b + b) := by rw [v3_add_self, add_zero]
      _ = (a + b) + b := by rw [add_assoc]
      _ = b := by rw [hab, zero_add]
  exact ⟨key _ _ h2, key _ _ h3⟩

theorem cT_split (v w : Fin 3 → ZMod 2) : cT v w = cT v 0 * cT 0 w := by
  rw [← hc.add, add_zero, zero_add]

theorem conj_z_cT_zero (v : Fin 3 → ZMod 2) : z * cT v 0 * z⁻¹ = cT v 0 := by
  rw [hc.conj_z, add_zero]

end Coords

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_of_two {K P P' : Subgroup G} (hPK : P ≤ K) (hP'K : P' ≤ K)
    (hP : IsPGroup 2 P) (hP' : IsPGroup 2 P') (hodd : ¬ 2 ∣ P.relIndex K)
    (hcard : Nat.card P' = Nat.card P) :
    ∃ k ∈ K, ∀ x ∈ P', k * x * k⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsPGroup 2 (P.subgroupOf K) := hP.of_equiv (subgroupOfEquivOfLe hPK).symm
  have h1' : IsPGroup 2 (P'.subgroupOf K) := hP'.of_equiv (subgroupOfEquivOfLe hP'K).symm
  have hi : ¬ 2 ∣ (P.subgroupOf K).index := hodd
  have hi' : ¬ 2 ∣ (P'.subgroupOf K).index := by
    have e1 := (P.subgroupOf K).card_mul_index
    have e2 := (P'.subgroupOf K).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hPK).toEquiv] at e1
    rw [Nat.card_congr (subgroupOfEquivOfLe hP'K).toEquiv, hcard] at e2
    have : (P'.subgroupOf K).index = (P.subgroupOf K).index :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos (e2.trans e1.symm)
    rw [this]
    exact hi
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K (h1'.toSylow hi') (h1.toSylow hi)
  refine ⟨k, k.2, fun x hx => ?_⟩
  have hx' : (⟨x, hP'K hx⟩ : K) ∈ ((h1'.toSylow hi' : Sylow 2 K) : Subgroup K) := hx
  have h2 := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj k) _ hx'
  rw [← Sylow.coe_subgroup_smul, hk] at h2
  exact h2

theorem card_sup_eq_mul {T O : Subgroup G} (hTO : T ≤ normalizer (O : Set G))
    (hinf : T ⊓ O = ⊥) : Nat.card (T ⊔ O : Subgroup G) = Nat.card T * Nat.card O := by
  have hm := Subgroup.coe_mul_of_left_le_normalizer_right T O hTO
  let f : T × O → (T ⊔ O : Subgroup G) := fun p =>
    ⟨(p.1 : G) * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨t, o⟩ ⟨t', o'⟩ h
      have e : (t : G) * o = t' * o' := congrArg Subtype.val h
      have h1 : (t' : G)⁻¹ * t ∈ T ⊓ O := by
        refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem t'.2) t.2, ?_⟩
        have : (t' : G)⁻¹ * t = o' * (o : G)⁻¹ := by
          calc (t' : G)⁻¹ * t = (t' : G)⁻¹ * (t * o) * (o : G)⁻¹ := by group
            _ = (t' : G)⁻¹ * (t' * o') * (o : G)⁻¹ := by rw [e]
            _ = o' * (o : G)⁻¹ := by group
        rw [this]
        exact mul_mem o'.2 (inv_mem o.2)
      rw [hinf, mem_bot, inv_mul_eq_one] at h1
      have ht : t = t' := Subtype.ext h1.symm
      subst ht
      exact Prod.ext rfl (Subtype.ext (mul_left_cancel e))
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (T : Set G) * (O : Set G) := by rw [← hm]; exact hx
      obtain ⟨t, ht, o, ho, rfl⟩ := Set.mem_mul.1 hx'
      exact ⟨(⟨t, ht⟩, ⟨o, ho⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

end Sylow

section Comm

private theorem lin8_comm_cases : ∀ a1 a2 a4 : Fin 8,
    (∀ k, lin8 a1 a2 a4 (lin8 2 4 1 k) = lin8 2 4 1 (lin8 a1 a2 a4 k)) →
    (∀ k, lin8 a1 a2 a4 (lin8 1 3 4 k) = lin8 1 3 4 (lin8 a1 a2 a4 k)) →
    (a1 = 0 ∧ a2 = 0 ∧ a4 = 0) ∨ (a1 = 1 ∧ a2 = 2 ∧ a4 = 4) := by
  decide +kernel

theorem eq_zero_or_eq_self_of_comm {α : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2)}
    (hadd : ∀ v w, α (v + w) = α v + α w)
    (hcomm : ∀ (A : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2),
      α ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) =
        (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ α v) :
    (∀ v, α v = 0) ∨ (∀ v, α v = v) := by
  set f : Fin 8 → Fin 8 := fun k => bits.symm (α (bits k)) with hfdef
  have hf : ∀ i j, f (xr i j) = xr (f i) (f j) := by
    intro i j
    simp only [hfdef]
    rw [bits_xr, hadd, bits_symm_add]
  have hcf : ∀ (A : GL (Fin 3) (ZMod 2)) k, f (linPerm8 A k) = linPerm8 A (f k) := by
    intro A k
    simp only [hfdef]
    rw [bits_linPerm8, hcomm, linPerm8_apply, Equiv.apply_symm_apply]
  have hαf : ∀ v, α v = bits (f (bits.symm v)) := fun v => by
    simp only [hfdef, Equiv.apply_symm_apply]
  obtain ⟨S, hS⟩ := exists_GL_of_xr (f := lin8 2 4 1) (by decide) (by decide)
  obtain ⟨U, hU⟩ := exists_GL_of_xr (f := lin8 1 3 4) (by decide) (by decide)
  have hl := eq_lin8 hf
  have h1 : ∀ k, lin8 (f 1) (f 2) (f 4) (lin8 2 4 1 k) = lin8 2 4 1 (lin8 (f 1) (f 2) (f 4) k) := by
    intro k
    rw [← hl, ← hS, ← hS]
    exact hcf S k
  have h2 : ∀ k, lin8 (f 1) (f 2) (f 4) (lin8 1 3 4 k) = lin8 1 3 4 (lin8 (f 1) (f 2) (f 4) k) := by
    intro k
    rw [← hl, ← hU, ← hU]
    exact hcf U k
  rcases lin8_comm_cases _ _ _ h1 h2 with ⟨e1, e2, e4⟩ | ⟨e1, e2, e4⟩
  · left
    intro v
    have h3 : ∀ k, f k = 0 := by
      intro k
      rw [congrFun hl k, e1, e2, e4]
      revert k
      decide
    rw [hαf, h3, bits_zero]
  · right
    intro v
    have h3 : ∀ k, f k = k := by
      intro k
      rw [congrFun hl k, e1, e2, e4]
      revert k
      decide
    rw [hαf, h3, Equiv.apply_symm_apply]

end Comm

section Rho

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (θ : L ≃* alternatingGroup (Fin n))
  (hn : 8 ≤ n)

theorem rho_comm_of_comm {x : normalizer (L : Set G)} {a : alternatingGroup (Fin n)}
    (hx : (x : G) * ((θ.symm a : L) : G) = ((θ.symm a : L) : G) * x) :
    AltStdBal.rho θ hn x * (a : Perm (Fin n)) = a * AltStdBal.rho θ hn x := by
  have h1 := AltStdBal.rho_conj θ hn x a
  have h2 : ∀ p : (x : G) * ((θ.symm a : L) : G) * (x : G)⁻¹ ∈ L,
      (θ ⟨_, p⟩ : alternatingGroup (Fin n)) = a := by
    intro p
    have : (⟨(x : G) * ((θ.symm a : L) : G) * (x : G)⁻¹, p⟩ : L) = θ.symm a :=
      Subtype.ext (by
        show (x : G) * ((θ.symm a : L) : G) * (x : G)⁻¹ = ((θ.symm a : L) : G)
        rw [hx, mul_inv_cancel_right])
    rw [this, MulEquiv.apply_symm_apply]
  rw [h2] at h1
  calc AltStdBal.rho θ hn x * (a : Perm (Fin n))
      = AltStdBal.rho θ hn x * (a : Perm (Fin n)) * (AltStdBal.rho θ hn x)⁻¹ *
          AltStdBal.rho θ hn x := by group
    _ = a * AltStdBal.rho θ hn x := by rw [h1]

theorem comm_of_rho_comm {x : normalizer (L : Set G)} {l : L}
    (hx : AltStdBal.rho θ hn x * ((θ l : alternatingGroup (Fin n)) : Perm (Fin n)) =
      (θ l : Perm (Fin n)) * AltStdBal.rho θ hn x) :
    (x : G) * l = l * x := by
  have h1 := AltStdBal.rho_conj θ hn x (θ l)
  rw [hx, mul_inv_cancel_right] at h1
  have h3 := θ.injective (Subtype.ext h1)
  have h4 := congrArg Subtype.val h3
  simp only [MulEquiv.symm_apply_apply] at h4
  calc (x : G) * l = (x : G) * l * (x : G)⁻¹ * x := by group
    _ = l * x := by rw [← h4]

end Rho

section Setting

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {T : Subgroup G}
  (c : Config G L Q n θ z) (hH : HData θ c.hn8 z T)

include hH in
theorem act_eq_self_of_mem_sup {y t : G} (hy : y ∈ T ⊔ Ocore θ c.hn8 z) (ht : t ∈ T) :
    act T (Ocore θ c.hn8 z) y t = t := by
  have hTO := T_le_normalizer_ocore c hH
  have hinf := T_inf_ocore c hH
  have hm := Subgroup.coe_mul_of_left_le_normalizer_right T (Ocore θ c.hn8 z) hTO
  have hy' : y ∈ (T : Set G) * (Ocore θ c.hn8 z : Set G) := by rw [← hm]; exact hy
  obtain ⟨t₀, ht₀, o, ho, rfl⟩ := Set.mem_mul.1 hy'
  refine proj_eq hTO hinf ht ?_
  have hc : t⁻¹ * t₀ = t₀ * t⁻¹ := comm_T c hH (inv_mem ht) ht₀
  have e : t⁻¹ * (t₀ * o * t * (t₀ * o)⁻¹) = t₀ * ((t⁻¹ * o * t⁻¹⁻¹) * o⁻¹) * t₀⁻¹ := by
    calc t⁻¹ * (t₀ * o * t * (t₀ * o)⁻¹) = (t⁻¹ * t₀) * o * t * o⁻¹ * t₀⁻¹ := by group
      _ = (t₀ * t⁻¹) * o * t * o⁻¹ * t₀⁻¹ := by rw [hc]
      _ = t₀ * ((t⁻¹ * o * t⁻¹⁻¹) * o⁻¹) * t₀⁻¹ := by group
  rw [e]
  have h1 : t⁻¹ * o * t⁻¹⁻¹ ∈ Ocore θ c.hn8 z := (mem_normalizer_iff.1 (hTO (inv_mem ht)) o).1 ho
  have h2 := mul_mem h1 (inv_mem ho)
  have h3 := (mem_normalizer_iff.1 (hTO ht₀) _).1 h2
  exact h3

include hH in
theorem exists_cent_lift {h : G} (hh : h ∈ normalizer (T : Set G))
    (hc : h * z * h⁻¹ * z⁻¹ ∈ centralizer (T : Set G)) :
    ∃ k ∈ centralizer (T : Set G), k * h * z = z * (k * h) := by
  set OH := AltStdSec.oddCoreOf (normalizer (T : Set G))
  have hOC : OH ≤ centralizer (T : Set G) := by rw [hH.cent]; exact le_sup_right
  have hTC : T ≤ centralizer (T : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun y hy => comm_T c hH hy hx
  have hTOH : T ≤ normalizer (OH : Set G) :=
    le_normalizer_of_conj' fun g hg o ho => conj_mem_oddCoreOf' (Subgroup.le_normalizer hg) ho
  have hinf : T ⊓ OH = ⊥ := by
    apply inf_eq_bot_of_coprime
    rw [hH.n0.card_eq]
    exact Nat.Coprime.pow_left 6 (coprime_card_oddCoreOf _)
  have hzN : z ∈ normalizer (T : Set G) := hH.n0.norm
  have hz2 : z * z = 1 := z_mul_self c
  have hzi : z⁻¹ = z := z_inv c
  have hcm : h * z * h⁻¹ * z⁻¹ ∈ T ⊔ OH := by rw [← hH.cent]; exact hc
  have hm := Subgroup.coe_mul_of_left_le_normalizer_right T OH hTOH
  have hcm' : h * z * h⁻¹ * z⁻¹ ∈ (T : Set G) * (OH : Set G) := by rw [← hm]; exact hcm
  obtain ⟨t, ht, o, ho, hto⟩ := Set.mem_mul.1 hcm'
  have hcz : h * z * h⁻¹ = t * o * z := by
    rw [hto]
    group
  have ht' : z * t * z⁻¹ ∈ T := (mem_normalizer_iff.1 hzN t).1 ht
  have ho' : z * o * z⁻¹ ∈ OH := conj_mem_oddCoreOf' hzN ho
  have hot : o * (z * t * z⁻¹) = (z * t * z⁻¹) * o := (mem_centralizer_iff.1 (hOC ho) _ ht').symm
  have hsq : (t * (z * t * z⁻¹)) * (o * (z * o * z⁻¹)) = 1 := by
    have h1 : (h * z * h⁻¹) * (h * z * h⁻¹) = 1 := by
      calc (h * z * h⁻¹) * (h * z * h⁻¹) = h * (z * z) * h⁻¹ := by group
        _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]
    rw [hcz] at h1
    calc (t * (z * t * z⁻¹)) * (o * (z * o * z⁻¹))
        = t * (o * (z * t * z⁻¹)) * (z * o * z⁻¹) := by rw [hot]; group
      _ = t * o * z * (t * o * z) * (z⁻¹ * z⁻¹) := by group
      _ = 1 := by rw [h1, hzi, hz2, mul_one]
  have hT1 : t * (z * t * z⁻¹) = 1 ∧ o * (z * o * z⁻¹) = 1 := by
    have hmem : t * (z * t * z⁻¹) ∈ T ⊓ OH := by
      refine Subgroup.mem_inf.2 ⟨mul_mem ht ht', ?_⟩
      rw [eq_inv_of_mul_eq_one_left hsq]
      exact inv_mem (mul_mem ho ho')
    rw [hinf, mem_bot] at hmem
    refine ⟨hmem, ?_⟩
    rw [hmem, one_mul] at hsq
    exact hsq
  have htz : (t * z) ^ 2 = 1 := by
    calc (t * z) ^ 2 = t * (z * t * z⁻¹) * (z * z) := by rw [sq]; group
      _ = 1 := by rw [hT1.1, hz2, one_mul]
  obtain ⟨x, hx, hxz⟩ := hH.inv t ht htz
  have hodd : Odd (orderOf o) := by
    have h1 := Subgroup.orderOf_dvd_natCard OH ho
    exact Nat.coprime_two_left.1 (Nat.Coprime.coprime_dvd_right h1 (coprime_card_oddCoreOf _))
  obtain ⟨j, hj⟩ := hodd
  set s := o ^ (j + 1) with hs
  have hsO : s ∈ OH := pow_mem ho _
  have hss : s * s = o := by
    rw [hs, ← pow_add, show j + 1 + (j + 1) = orderOf o + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hzo : z * o * z⁻¹ = o⁻¹ := eq_inv_of_mul_eq_one_right hT1.2
  have hzs : z * s * z⁻¹ = s⁻¹ := by
    rw [hs, ← conj_pow, hzo, inv_pow]
  have hsz : s * z * s⁻¹ = o * z := by
    calc s * z * s⁻¹ = s * (z * s * z⁻¹)⁻¹ * z := by group
      _ = o * z := by rw [hzs, inv_inv, hss]
  have hst : s * t = t * s := (mem_centralizer_iff.1 (hOC hsO) t ht).symm
  have hkey : h * z * h⁻¹ = (s * x) * z * (s * x)⁻¹ := by
    calc h * z * h⁻¹ = t * (s * z * s⁻¹) := by rw [hcz, hsz]; group
      _ = s * (t * z) * s⁻¹ := by
          calc t * (s * z * s⁻¹) = (t * s) * z * s⁻¹ := by group
            _ = (s * t) * z * s⁻¹ := by rw [hst]
            _ = s * (t * z) * s⁻¹ := by group
      _ = (s * x) * z * (s * x)⁻¹ := by rw [← hxz]; group
  refine ⟨(s * x)⁻¹, inv_mem (mul_mem (hOC hsO) (hTC hx)), ?_⟩
  calc (s * x)⁻¹ * h * z = (s * x)⁻¹ * (h * z * h⁻¹) * h := by group
    _ = z * ((s * x)⁻¹ * h) := by rw [hkey]; group

variable {cT : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G}
  (hc : TCoords z T (kap θ c.hn8) (E θ c.hn8) cT)
  (hact : ∀ (A : GL (Fin 3) (ZMod 2)) (v w : Fin 3 → ZMod 2),
    act T (Ocore θ c.hn8 z) (kap θ c.hn8 A) (cT v w) =
      cT ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w))

include hH hc hact in
theorem exists_normalizer_dg (A : GL (Fin 3) (ZMod 2)) : ∃ g ∈ normalizer (T : Set G),
    ∀ v w, g * cT v w * g⁻¹ =
      cT ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v)
        ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) := by
  set O := Ocore θ c.hn8 z
  set κ := kap θ c.hn8 A
  have hTO := T_le_normalizer_ocore c hH
  have hinf := T_inf_ocore c hH
  have hON : ∀ g ∈ N0 θ c.hn8 z, ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g hg o ho => ocore_conj c hg ho
  have hκN : κ ∈ N0 θ c.hn8 z := kap_mem_N0 c A
  set T' := T.map (MulAut.conj κ).toMonoidHom
  have hT'K : T' ≤ T ⊔ O := by
    rintro _ ⟨t, ht, rfl⟩
    exact hH.n0.normal κ hκN t ht
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 6) (by rw [hH.n0.card_eq]; norm_num)
  have hT'2 : IsPGroup 2 T' := hT2.map _
  have hcard : Nat.card T' = Nat.card T := card_map_of_injective (MulAut.conj κ).injective
  have hodd : ¬ 2 ∣ T.relIndex (T ⊔ O) := by
    have h1 := T.relIndex_mul_card (T ⊔ O)
    rw [inf_of_le_left le_sup_left, card_sup_eq_mul hTO hinf, mul_comm (Nat.card T)] at h1
    have h2 : T.relIndex (T ⊔ O) = Nat.card O := Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
    rw [h2]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 (coprime_card_oddCoreOf _)
  obtain ⟨k, hk, hkT⟩ := exists_conj_mem_of_two le_sup_left hT'K hT2 hT'2 hodd hcard
  have hkN : k ∈ N0 θ c.hn8 z := (sup_le hH.n0.le (Subgroup.map_subtype_le _)) hk
  have hgT : ∀ t ∈ T, (k * κ) * t * (k * κ)⁻¹ ∈ T := by
    intro t ht
    have h1 : κ * t * κ⁻¹ ∈ T' := ⟨t, ht, rfl⟩
    have h2 := hkT _ h1
    rwa [show k * (κ * t * κ⁻¹) * k⁻¹ = (k * κ) * t * (k * κ)⁻¹ by group] at h2
  refine ⟨k * κ, mem_normalizer_fintype hgT, fun v w => ?_⟩
  rw [← act_of_mem hTO hinf (hgT _ (hc.mem v w)), act_comp hTO hinf hON hH.n0.normal hkN hκN
    (hc.mem v w), act_eq_self_of_mem_sup c hH hk (act_kap_mem c hH A (hc.mem v w)), hact]

include hH hc hact in
theorem cent_act {h : G} (hh : h ∈ normalizer (T : Set G)) (hz : h * z = z * h) :
    ∃ (P : GL (Fin 3) (ZMod 2)) (ε : Bool), ∀ v w,
      h * cT v w * h⁻¹ = cT ((P : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ (if ε then v + w else v))
        ((P : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) := by
  set O := Ocore θ c.hn8 z
  have hTO := T_le_normalizer_ocore c hH
  have hinf := T_inf_ocore c hH
  have hON : ∀ g ∈ N0 θ c.hn8 z, ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g hg o ho => ocore_conj c hg ho
  have hTN := hH.n0.normal
  have hz' : h⁻¹ * z = z * h⁻¹ := by
    calc h⁻¹ * z = h⁻¹ * (z * h) * h⁻¹ := by group
      _ = h⁻¹ * (h * z) * h⁻¹ := by rw [hz]
      _ = z * h⁻¹ := by group
  have hE : ∀ i : Fin 8, ∃ j, h * N0.eps θ c.hn8 i * h⁻¹ = N0.eps θ c.hn8 j := by
    intro i
    have h1 : h * N0.eps θ c.hn8 i * h⁻¹ ∈ T ⊓ centralizer ({z} : Set G) := by
      refine ⟨(mem_normalizer_iff.1 hh _).1 (eps_mem_T c hH i),
        mem_centralizer_singleton_iff.2 ?_⟩
      have he := N0.eps_comm_z c.hn8 c i
      calc h * N0.eps θ c.hn8 i * h⁻¹ * z = h * N0.eps θ c.hn8 i * (h⁻¹ * z) := by group
        _ = h * (N0.eps θ c.hn8 i * z) * h⁻¹ := by rw [hz']; group
        _ = (h * z) * N0.eps θ c.hn8 i * h⁻¹ := by rw [he]; group
        _ = z * (h * N0.eps θ c.hn8 i * h⁻¹) := by rw [hz]; group
    rw [hH.n0.cent] at h1
    exact (N0.mem_E_iff θ c.hn8 _).1 h1
  choose f hf using hE
  have hfx : ∀ i j, f (xr i j) = xr (f i) (f j) := by
    intro i j
    apply N0.eps_injective θ c.hn8
    rw [← hf, N0.xr_eq_xor, N0.xr_eq_xor, ← N0.eps_mul, ← N0.eps_mul, ← hf, ← hf]
    group
  have hfinj : Function.Injective f := by
    intro i j hij
    apply N0.eps_injective θ c.hn8
    have h1 := hf i
    rw [hij, ← hf j] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  obtain ⟨P, hP⟩ := exists_GL_of_xr hfx hfinj
  have hhN : h ∈ N0 θ c.hn8 z := by
    apply mem_normalizer_fintype
    intro x hx
    obtain ⟨i, rfl | rfl⟩ := (N0.mem_B0_iff c.hn8 c x).1 hx
    · rw [hf]
      exact N0.eps_mem_B0 c.hn8 c _
    · have : h * (z * N0.eps θ c.hn8 i) * h⁻¹ = z * N0.eps θ c.hn8 (f i) := by
        rw [← hf, show h * (z * N0.eps θ c.hn8 i) * h⁻¹ = (h * z) * N0.eps θ c.hn8 i * h⁻¹ by
          group, hz]
        group
      rw [this]
      exact (N0.mem_B0_iff c.hn8 c _).2 ⟨f i, Or.inr rfl⟩
  set κP := kap θ c.hn8 P with hκP
  have hκPz : κP * z = z * κP := N0.comm_z_of_mem_L c (kap_mem_L θ c.hn8 P)
  set m := κP⁻¹ * h with hm
  have hmE : ∀ i, m * N0.eps θ c.hn8 i * m⁻¹ = N0.eps θ c.hn8 i := by
    intro i
    calc m * N0.eps θ c.hn8 i * m⁻¹ = κP⁻¹ * (h * N0.eps θ c.hn8 i * h⁻¹) * κP := by
          rw [hm]; group
      _ = κP⁻¹ * N0.eps θ c.hn8 (linPerm8 P i) * κP := by rw [hf, ← hP]
      _ = N0.eps θ c.hn8 i := by rw [← kap_conj_eps θ c.hn8 P i, ← hκP]; group
  have hmz : m * z = z * m := by
    have h1 : κP⁻¹ * z = z * κP⁻¹ := by
      calc κP⁻¹ * z = κP⁻¹ * (z * κP) * κP⁻¹ := by group
        _ = κP⁻¹ * (κP * z) * κP⁻¹ := by rw [hκPz]
        _ = z * κP⁻¹ := by group
    calc m * z = κP⁻¹ * (h * z) := by rw [hm]; group
      _ = (κP⁻¹ * z) * h := by rw [hz]; group
      _ = z * m := by rw [h1, hm]; group
  have hmNL : m ∈ normalizer (L : Set G) :=
    AltStdCycTwo.cent_le_normalizer c.ot.std c.ot.cyc (mem_centralizer_singleton_iff.2 hmz)
  set ρm := AltStdBal.rho θ c.hn8 ⟨m, hmNL⟩
  have hρE : ∀ e ∈ eBar c.hn8, ρm * (e : Perm (Fin n)) = e * ρm := by
    intro e he
    apply rho_comm_of_comm θ c.hn8
    obtain ⟨i, hi⟩ := (N0.mem_E_iff θ c.hn8 _).1 (mem_E_of_mem_eBar θ c.hn8 he)
    show m * ((θ.symm e : L) : G) = ((θ.symm e : L) : G) * m
    rw [hi]
    calc m * N0.eps θ c.hn8 i = m * N0.eps θ c.hn8 i * m⁻¹ * m := by group
      _ = N0.eps θ c.hn8 i * m := by rw [hmE]
  have h0 := (apply_of_comm_eBar c.hn8 hρE (i := pt c.hn8 0) (show (0 : ℕ) < 8 by norm_num)).1
  set s : Fin 8 := ⟨(ρm (pt c.hn8 0)).val, h0⟩
  set es := N0.eps θ c.hn8 s with hes
  set y := es * m with hy
  have hesNL : es ∈ normalizer (L : Set G) := Subgroup.le_normalizer (N0.eps_mem_L θ c.hn8 s)
  have hyNL : y ∈ normalizer (L : Set G) := mul_mem hesNL hmNL
  have hρes : AltStdBal.rho θ c.hn8 ⟨es, hesNL⟩ = tr c.hn8 s := by
    have h1 := AltStdBal.rho_of_mem θ c.hn8
      (θ.symm ⟨tr c.hn8 s, tr_mem_alternatingGroup c.hn8 s⟩) hesNL
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  set ρy := AltStdBal.rho θ c.hn8 ⟨y, hyNL⟩ with hρy
  have hρy' : ρy = tr c.hn8 s * ρm := by
    have : (⟨y, hyNL⟩ : normalizer (L : Set G)) = ⟨es, hesNL⟩ * ⟨m, hmNL⟩ := rfl
    rw [hρy, this, map_mul, hρes]
  have hy8 : ∀ i : Fin n, i.val < 8 → ρy i = i := by
    intro i hi
    obtain ⟨hlt, hval⟩ := apply_of_comm_eBar c.hn8 hρE hi
    apply Fin.ext
    rw [hρy', Perm.mul_apply, val_tr_of_lt c.hn8 s hlt, hval]
    show (ρm (pt c.hn8 0)).val ^^^ i.val ^^^ (ρm (pt c.hn8 0)).val = i.val
    rw [Nat.xor_comm _ i.val, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have hyl : ∀ A, ρy * linPerm c.hn8 A = linPerm c.hn8 A * ρy := by
    intro A
    refine Equiv.ext fun i => ?_
    rw [Perm.mul_apply, Perm.mul_apply]
    by_cases hi : i.val < 8
    · have h8 : (linPerm c.hn8 A i).val < 8 := by
        rw [val_linPerm_of_lt c.hn8 A hi]
        exact (linPerm8 A _).2
      rw [hy8 _ h8, hy8 i hi]
    · push Not at hi
      have hge : 8 ≤ (ρy i).val := by
        by_contra hlt
        push Not at hlt
        have h1 := ρy.injective (hy8 _ hlt)
        rw [h1] at hlt
        omega
      rw [linPerm_of_ge c.hn8 A hi, linPerm_of_ge c.hn8 A hge]
  have hyk : ∀ A, y * kap θ c.hn8 A = kap θ c.hn8 A * y := by
    intro A
    have h1 := comm_of_rho_comm θ c.hn8 (x := ⟨y, hyNL⟩) (l := θ.symm (lin c.hn8 A))
      (by rw [MulEquiv.apply_symm_apply, coe_lin]; exact hyl A)
    exact h1
  have hesN : es ∈ N0 θ c.hn8 z :=
    Subgroup.le_normalizer (mem_sup_left (N0.eps_mem_E θ c.hn8 s))
  have hκPN : κP ∈ N0 θ c.hn8 z := kap_mem_N0 c P
  have hmN : m ∈ N0 θ c.hn8 z := mul_mem (inv_mem hκPN) hhN
  have hyN : y ∈ N0 θ c.hn8 z := mul_mem hesN hmN
  have hyz : y * z = z * y := by
    calc y * z = es * (m * z) := by rw [hy]; group
      _ = (es * z) * m := by rw [hmz]; group
      _ = z * y := by rw [hy, hes, N0.eps_comm_z c.hn8 c s]; group
  have hyE : ∀ i, y * N0.eps θ c.hn8 i * y⁻¹ = N0.eps θ c.hn8 i := by
    intro i
    calc y * N0.eps θ c.hn8 i * y⁻¹ = es * (m * N0.eps θ c.hn8 i * m⁻¹) * es⁻¹ := by
          rw [hy]; group
      _ = N0.eps θ c.hn8 i := by
          rw [hmE, hes, N0.eps_comm θ c.hn8 s i, mul_inv_cancel_right]
  have hyT : ∀ t ∈ T, act T O y t ∈ T := fun t ht => (act_spec hTO hTN hyN ht).1
  have hy0 : ∀ v, act T O y (cT v 0) = cT v 0 := by
    intro v
    have h1 : cT v 0 ∈ T ⊓ centralizer ({z} : Set G) := by
      refine ⟨hc.mem v 0, mem_centralizer_singleton_iff.2 ?_⟩
      calc cT v 0 * z = z * cT v 0 * z⁻¹ * z := by rw [conj_z_cT_zero hc]
        _ = z * cT v 0 := by group
    rw [hH.n0.cent] at h1
    obtain ⟨i, hi⟩ := (N0.mem_E_iff θ c.hn8 _).1 h1
    rw [hi, act_of_mem hTO hinf (by rw [hyE]; exact eps_mem_T c hH i), hyE]
  have hcoord : ∀ w, ∃ a, act T O y (cT 0 w) = cT a w := by
    intro w
    obtain ⟨a, b, hab⟩ := hc.surj _ (hyT _ (hc.mem 0 w))
    refine ⟨a, ?_⟩
    have h1 := act_conj_z hTO hinf hON hTN hyN (z_mem_N0 c) hyz (fun x hx => conj_z_mem c hH hx)
      (hc.mem 0 w)
    rw [hc.conj_z, ← hab, hc.conj_z, zero_add, cT_split hc w w,
      act_mul hTO hinf hTN hyN (hc.mem w 0) (hc.mem 0 w), hy0, ← hab, ← hc.add, zero_add] at h1
    have h2 := ((cT_eq_iff hc).1 h1).1
    have hb : b = w := by
      have h3 : w + a + a = a + b + a := by rw [h2]
      rwa [add_assoc, v3_add_self, add_zero, add_comm a b, add_assoc, v3_add_self, add_zero,
        eq_comm] at h3
    rw [← hab, hb]
  choose α hα using hcoord
  have hαadd : ∀ w w', α (w + w') = α w + α w' := by
    intro w w'
    have h1 : cT 0 (w + w') = cT 0 w * cT 0 w' := by rw [← hc.add, add_zero]
    have h2 := hα (w + w')
    rw [h1, act_mul hTO hinf hTN hyN (hc.mem 0 w) (hc.mem 0 w'), hα, hα, ← hc.add] at h2
    exact (((cT_eq_iff hc).1 h2).1).symm
  have hαcomm : ∀ (A : GL (Fin 3) (ZMod 2)) w,
      α ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) =
        (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ α w := by
    intro A w
    have hκN : kap θ c.hn8 A ∈ N0 θ c.hn8 z := kap_mem_N0 c A
    have h1 := act_comp hTO hinf hON hTN hyN hκN (hc.mem 0 w)
    have h2 := act_comp hTO hinf hON hTN hκN hyN (hc.mem 0 w)
    rw [hyk A, h2, hα, hact, hact, mulVec_zero, hα] at h1
    exact (((cT_eq_iff hc).1 h1).1).symm
  have hyv : ∀ v w, act T O y (cT v w) = cT (v + α w) w := by
    intro v w
    rw [cT_split hc v w, act_mul hTO hinf hTN hyN (hc.mem v 0) (hc.mem 0 w), hy0, hα, ← hc.add,
      zero_add]
  have hes2 : es * y = m := by
    rw [hy, ← mul_assoc, hes, N0.eps_mul_self, one_mul]
  have hesT : ∀ t ∈ T, act T O es t = t := by
    intro t ht
    have h1 : es * t * es⁻¹ = t := by
      rw [comm_T c hH (eps_mem_T c hH s) ht, mul_inv_cancel_right]
    rw [act_of_mem hTO hinf (by rw [h1]; exact ht), h1]
  have hhv : ∀ v w, h * cT v w * h⁻¹ = cT ((P : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ (v + α w))
      ((P : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) := by
    intro v w
    have hhe : h = κP * (es * y) := by rw [hes2, hm, mul_inv_cancel_left]
    have hy' : act T O y (cT v w) ∈ T := hyT _ (hc.mem v w)
    rw [← act_of_mem hTO hinf ((mem_normalizer_iff.1 hh _).1 (hc.mem v w))]
    conv_lhs => rw [hhe]
    rw [act_comp hTO hinf hON hTN hκPN (mul_mem hesN hyN) (hc.mem v w),
      act_comp hTO hinf hON hTN hesN hyN (hc.mem v w), hesT _ hy', hyv, hact]
  rcases eq_zero_or_eq_self_of_comm hαadd hαcomm with h0 | h1
  · refine ⟨P, false, fun v w => ?_⟩
    rw [hhv, h0, add_zero]
    rfl
  · refine ⟨P, true, fun v w => ?_⟩
    rw [hhv, h1]
    rfl

end Setting

end CFSG.OddStandard.AltStdSmall4.HbarCoords
