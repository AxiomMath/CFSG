module

public import CFSG.GH74.GLS.Stage2.Local.P27.L4Iface
public import CFSG.GH74.GLS.Stage2.Local.P27.L4Sylow
public import CFSG.GH74.GLS.Stage2.Local.P34S5Bal
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrNormalClosure
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Aux

omit [Finite G] in
theorem mem_sup_zpowers_invol {z u y : G} (hz : z * z = 1) (hu : u * u = 1) (hzu : z * u = u * z)
    (hy : y ∈ zpowers z ⊔ zpowers u) : y = 1 ∨ y = z ∨ y = u ∨ y = z * u := by
  have hone : ∀ {c : G}, c * c = 1 → ∀ a ∈ zpowers c, a = 1 ∨ a = c := by
    intro c hc a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have h2 : c ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hc
    rw [zpow_eq_zpow_emod k h2]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; rw [h, zpow_zero]
    · right; rw [h, zpow_one]
  have hcomm : ∀ a ∈ zpowers z, ∀ b ∈ zpowers u, a * b = b * a := by
    rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩
    exact (Commute.zpow_zpow (hzu : Commute z u) i j).eq
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_comm hcomm).1 hy
  rcases hone hz a ha with rfl | rfl <;> rcases hone hu b hb with rfl | rfl <;> simp

omit [Finite G] in
theorem card_of_isDihedralTwoGroup {D : Subgroup G} {n : ℕ} (h : IVK.IsDihedralTwoGroup ↥D n) :
    Nat.card ↥D = 2 ^ n := by
  obtain ⟨hn, k, hk, hk2, ⟨e⟩⟩ := h
  have : NeZero k := ⟨by omega⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card, ← hk]

omit [Finite G] in
theorem le_closure_involutions {D : Subgroup G} {n : ℕ} (h : IVK.IsDihedralTwoGroup ↥D n) :
    D ≤ closure {s : G | s ∈ D ∧ orderOf s = 2} := by
  obtain ⟨hn, k, hk, hk2, ⟨e⟩⟩ := h
  have : NeZero k := ⟨by omega⟩
  have hsr : ∀ i : ZMod k, ((e.symm (DihedralGroup.sr i) : ↥D) : G) ∈
      {s : G | s ∈ D ∧ orderOf s = 2} := by
    intro i
    refine ⟨(e.symm (DihedralGroup.sr i)).2, ?_⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact DihedralGroup.orderOf_sr i
  intro d hd
  have hdd : (⟨d, hd⟩ : ↥D) = e.symm (e ⟨d, hd⟩) := (e.symm_apply_apply _).symm
  rcases hy : e ⟨d, hd⟩ with i | i
  · have : (⟨d, hd⟩ : ↥D) = e.symm (DihedralGroup.r i) := by rw [← hy]; exact hdd
    have hr : DihedralGroup.r i = DihedralGroup.sr 0 * DihedralGroup.sr i := by
      rw [DihedralGroup.sr_mul_sr, sub_zero]
    rw [hr, map_mul] at this
    have h2 : d = ((e.symm (DihedralGroup.sr 0) : ↥D) : G) * ((e.symm (DihedralGroup.sr i) : ↥D) : G) :=
      congrArg Subtype.val this
    rw [h2]
    exact Subgroup.mul_mem _ (subset_closure (hsr 0)) (subset_closure (hsr i))
  · have : (⟨d, hd⟩ : ↥D) = e.symm (DihedralGroup.sr i) := by rw [← hy]; exact hdd
    have h2 : d = ((e.symm (DihedralGroup.sr i) : ↥D) : G) := congrArg Subtype.val this
    rw [h2]
    exact subset_closure (hsr i)

omit [Finite G] in
theorem center_map_of_cj_eq {c : G} {H K : Subgroup G} (h : cj c H = K) :
    (center ↥K).map K.subtype = cj c ((center ↥H).map H.subtype) := by
  subst h
  exact center_map_cj c H

omit [Finite G] in
theorem pLayerOf_le_P27 (p : ℕ) (H : Subgroup G) : pLayerOf p H ≤ H := sSup_le fun _ hL => hL.1

omit [Finite G] in
theorem pLayerOf_two_perfect_P27 (H : Subgroup G) :
    ⁅pLayerOf 2 H, pLayerOf 2 H⁆ = pLayerOf 2 H := by
  have h := CFSG.ComponentClassification.UnbalancedCorr.pLayer_two_isPerfect ↥H
  rw [Stage2.Local.P34.pLayerOf_eq_map_P34 2 H, ← Subgroup.map_commutator, h]

end Aux

section Pic

structure L4Pic (z t u x : G) (S US : Subgroup G) (q : ℕ) (Z X : Set G) : Prop where
  x_def : x = t * z
  z_central : IsCentralInvolution z
  S_syl : IsSylowOf 2 S ⊤
  z_S : z ∈ S
  z_comm : ∀ s ∈ S, s * z = z * s
  t_S : t ∈ S
  t_inv : t * t = 1
  t_ne_z : t ≠ z
  t_conj : IsConj z t
  u_S : u ∈ S
  u_inv : u * u = 1
  u_ne : u ≠ 1
  u_ne_z : u ≠ z
  classes : ∀ y : G, orderOf y = 2 → IsConj z y ∨ IsConj u y
  u_nc : ¬ IsCentralInvolution u
  cls_Z : ∀ y ∈ S, y * y = 1 → y ≠ 1 → (IsConj z y ↔ y ∈ Z)
  cls_X : ∀ y ∈ S, y * y = 1 → y ≠ 1 → (IsConj u y ↔ y ∈ X)
  syl_t : IsSylowOf 2 (S ⊓ centralizer ({t} : Set G)) (centralizer ({x, z} : Set G))
  US_syl : IsSylowOf 2 US (Ixz z x)
  I_L2 : IVK.IsL2 (↥(Ixz z x) ⧸ pPrimeCore 2 ↥(Ixz z x)) (fun r => r = q)
  q_odd : Odd q
  q_gt : 3 < q
  I_le_J : Ixz z x ≤ Jx x

end Pic

section Main

structure L4Out (z x : G) (q a : ℕ) (T D₁ D₂ U T₁ : Subgroup G) (t' : G) : Prop where
  cfg : Cfg z x T q
  syl : Syl z x T D₁ D₂ U a t'
  T_le : T ≤ D₁ ⊔ D₂
  T₁_le : T₁ ≤ D₁
  T₁_cyc : IsCyclic ↥T₁
  x_T₁ : x ∈ T₁
  T₁_idx : T₁.relIndex D₁ = 2
  T₁_card : Nat.card ↥T₁ * 2 = Nat.card ↥D₂
  refl : ∀ a ∈ D₁, a ∉ T₁ → a * a = 1
  sepc : ∀ a ∈ D₁, a ∉ T₁ → ∀ m ∈ T₁ ⊔ D₂, m * m = 1 → m ≠ 1 → m ≠ x →
    ¬ ((IsConj z a ↔ IsConj z m) ∧ (IsConj z (x * a) ↔ IsConj z (x * m)))
  D₂_cl : ∀ s ∈ D₂, orderOf s = 2 → IsConj x s
  D₂_gen : D₂ ≤ closure {s | s ∈ D₂ ∧ orderOf s = 2}
  x_D : x ∈ ⁅D₁, D₁⁆
  Ω : ∀ y ∈ ⁅T, T⁆, y * y = 1 → y = 1 ∨ y = x ∨ y = t' ∨ y = x * t'
  D₂_card : Nat.card ↥D₂ = 2 * Nat.card ↥U

theorem l4_out {z t u x : G} {S US : Subgroup G} {a q : ℕ} {Z X : Set G}
    (pic : L4Pic z t u x S US q Z X)
    (A : L4Actual S z t a Z X US) (St : L4Std S z u a Z X) :
    ∃ (T D₁ D₂ T₁ : Subgroup G) (t' : G), L4Out z x q a T D₁ D₂ US T₁ t' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : orderOf z = 2 := pic.z_central.1
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, pow_two] at this
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by decide)
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have htz : t * z = z * t := pic.z_comm t pic.t_S
  have ht1 : t ≠ 1 := fun h => by
    have h' := pic.t_conj
    rw [h] at h'
    exact hz1 (isConj_one_right.1 h'.symm)
  have hxz : x = t * z := pic.x_def
  have hxS : x ∈ S := hxz ▸ S.mul_mem pic.t_S pic.z_S
  have hxzt : x * z = t := by rw [hxz, mul_assoc, hzz, mul_one]
  have hxx : x * x = 1 := by
    rw [hxz]
    calc t * z * (t * z) = t * (z * t) * z := by group
      _ = t * (t * z) * z := by rw [← htz]
      _ = t * t * (z * z) := by group
      _ = 1 := by rw [pic.t_inv, hzz, one_mul]
  have hx1 : x ≠ 1 := fun h => pic.t_ne_z (by
    rw [hxz] at h
    have := mul_eq_one_iff_eq_inv.1 h
    rw [this, hzinv])
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1
  have hux : IsConj u x := (pic.cls_X x hxS hxx hx1).2 (hxz ▸ A.tz_X)
  have hxnc : ¬ IsCentralInvolution x := fun h =>
    pic.u_nc (isCentralInvolution_of_isConj_P27 h hux.symm)
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact pic.u_inv) pic.u_ne
  have hCS : S ⊓ centralizer ({t} : Set G) ≤ centralizer ({x} : Set G) := by
    intro y hy
    refine mem_centralizer_iff.2 (fun h hh => ?_)
    rw [Set.mem_singleton_iff.1 hh, hxz]
    have h1 : t * y = y * t := mem_centralizer_iff.1 hy.2 t rfl
    have h2 : y * z = z * y := pic.z_comm y hy.1
    calc t * z * y = t * (z * y) := by group
      _ = t * (y * z) := by rw [h2]
      _ = (t * y) * z := by group
      _ = (y * t) * z := by rw [h1]
      _ = y * (t * z) := by group
  obtain ⟨T, hTsyl, hCST⟩ : ∃ T : Subgroup G, IsSylowOf 2 T (centralizer ({x} : Set G)) ∧
      S ⊓ centralizer ({t} : Set G) ≤ T := by
    obtain ⟨B, hB, hAB⟩ := exists_isSylowOf_ge_of_le' hCS pic.S_syl.isPGroup.to_inf_left
    exact ⟨B, hB, hAB⟩
  have hzCS : z ∈ S ⊓ centralizer ({t} : Set G) :=
    ⟨pic.z_S, mem_centralizer_iff.2 (fun h hh => by rw [Set.mem_singleton_iff.1 hh]; exact htz)⟩
  have htCS : t ∈ S ⊓ centralizer ({t} : Set G) :=
    ⟨pic.t_S, mem_centralizer_iff.2 (fun h hh => by rw [Set.mem_singleton_iff.1 hh])⟩
  have hzT : z ∈ T := hCST hzCS
  have htT : t ∈ T := hCST htCS
  have hTz : T ⊓ centralizer ({z} : Set G) = S ⊓ centralizer ({t} : Set G) := by
    have hle : S ⊓ centralizer ({t} : Set G) ≤ T ⊓ centralizer ({z} : Set G) :=
      le_inf hCST (fun y hy => mem_centralizer_iff.2 (fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]; exact (pic.z_comm y hy.1).symm))
    have hsub : T ⊓ centralizer ({z} : Set G) ≤ centralizer ({x, z} : Set G) := by
      intro y hy
      rw [mem_centralizer_iff]
      intro h hh
      rcases hh with rfl | hh
      · exact mem_centralizer_iff.1 (hTsyl.le hy.1) _ rfl
      · rw [Set.mem_singleton_iff.1 hh]; exact mem_centralizer_iff.1 hy.2 _ rfl
    exact pic.syl_t.eq_of_le hle hsub hTsyl.isPGroup.to_inf_left
  have hT'syl : IsSylowOf 2 (S ⊓ centralizer ({u} : Set G)) (centralizer ({u} : Set G)) :=
    isSylowOf_inf_centralizer_of_index_two pic.S_syl hu2 pic.u_nc St.index
  obtain ⟨c₀, hc₀⟩ := isConj_iff.1 hux.symm
  have hT₁syl : IsSylowOf 2 (cj c₀ T) (centralizer ({u} : Set G)) := by
    have := isSylowOf_cj (c := c₀) hTsyl
    rwa [cj_centralizer_singleton, hc₀] at this
  obtain ⟨k, hkC, hk⟩ := hT'syl.exists_mem_conj hT₁syl
  obtain ⟨g, hg⟩ : ∃ g : G, g = k⁻¹ * c₀ := ⟨_, rfl⟩
  have hku : k⁻¹ * u * k = u := by
    have := mem_centralizer_iff.1 hkC u rfl
    calc k⁻¹ * u * k = k⁻¹ * (u * k) := by group
      _ = k⁻¹ * (k * u) := by rw [this]
      _ = u := by group
  have hgx : g * x * g⁻¹ = u := by
    calc g * x * g⁻¹ = k⁻¹ * (c₀ * x * c₀⁻¹) * k := by rw [hg]; group
      _ = u := by rw [hc₀, hku]
  have hcjT : cj g T = S ⊓ centralizer ({u} : Set G) := by
    ext y
    rw [mem_cj]
    have h1 := hk (k * y * k⁻¹)
    rw [mem_cj] at h1
    have e1 : g⁻¹ * y * g = c₀⁻¹ * (k * y * k⁻¹) * c₀ := by rw [hg]; group
    have e2 : k⁻¹ * (k * y * k⁻¹) * k = y := by group
    rw [e1, h1, e2]
  have hcjinv : cj g⁻¹ (S ⊓ centralizer ({u} : Set G)) = T := by rw [← hcjT, cj_cj_inv]
  have conj_inv : ∀ y : G, y * y = 1 → (g * y * g⁻¹) * (g * y * g⁻¹) = 1 := fun y hy => by
    calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
      _ = 1 := by rw [hy]; group
  have conj_ne : ∀ y : G, y ≠ 1 → g * y * g⁻¹ ≠ 1 := fun y hy h => hy (by
    have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    rw [this, h]; group)
  have hZ' : ∀ y y' : G, y' = g * y * g⁻¹ → y' ∈ S → y * y = 1 → y ≠ 1 → (y' ∈ Z ↔ IsConj z y) := by
    intro y y' hyy' hy'S hy2 hy1
    have hy'2 : y' * y' = 1 := by rw [hyy']; exact conj_inv y hy2
    have hy'1 : y' ≠ 1 := by rw [hyy']; exact conj_ne y hy1
    rw [← pic.cls_Z y' hy'S hy'2 hy'1, hyy']
    exact ⟨fun h => h.trans (isConj_iff.2 ⟨g⁻¹, by group⟩), fun h => h.trans (isConj_iff.2 ⟨g, rfl⟩)⟩
  have hX' : ∀ y y' : G, y' = g * y * g⁻¹ → y' ∈ S → y * y = 1 → y ≠ 1 → (y' ∈ X ↔ IsConj u y) := by
    intro y y' hyy' hy'S hy2 hy1
    have hy'2 : y' * y' = 1 := by rw [hyy']; exact conj_inv y hy2
    have hy'1 : y' ≠ 1 := by rw [hyy']; exact conj_ne y hy1
    rw [← pic.cls_X y' hy'S hy'2 hy'1, hyy']
    exact ⟨fun h => h.trans (isConj_iff.2 ⟨g⁻¹, by group⟩), fun h => h.trans (isConj_iff.2 ⟨g, rfl⟩)⟩
  have hZtr : ∀ y y' : G, y ∈ S → y * y = 1 → y ≠ 1 → y' ∈ S → y' = g * y * g⁻¹ →
      (y' ∈ Z ↔ y ∈ Z) := fun y y' hyS hy2 hy1 hy'S hyy' =>
    (hZ' y y' hyy' hy'S hy2 hy1).trans (pic.cls_Z y hyS hy2 hy1)
  have hXtr : ∀ y y' : G, y ∈ S → y * y = 1 → y ≠ 1 → y' ∈ S → y' = g * y * g⁻¹ →
      (y' ∈ X ↔ y ∈ X) := fun y y' hyS hy2 hy1 hy'S hyy' =>
    (hX' y y' hyy' hy'S hy2 hy1).trans (pic.cls_X y hyS hy2 hy1)
  obtain ⟨w0, hw0⟩ : ∃ w0 : G, w0 = g * z * g⁻¹ := ⟨_, rfl⟩
  have hw0T' : w0 ∈ S ⊓ centralizer ({u} : Set G) := by
    rw [← hcjT, mem_cj]
    have : g⁻¹ * w0 * g = z := by rw [hw0]; group
    rw [this]; exact hzT
  have hw0S : w0 ∈ S := hw0T'.1
  have hw0w0 : w0 * w0 = 1 := by rw [hw0]; exact conj_inv z hzz
  have hw0conj : IsConj z w0 := isConj_iff.2 ⟨g, hw0.symm⟩
  have hw01 : w0 ≠ 1 := by rw [hw0]; exact conj_ne z hz1
  have hw0Z : w0 ∈ Z := (pic.cls_Z w0 hw0S hw0w0 hw01).1 hw0conj
  have huw0 : u * w0 = g * t * g⁻¹ := by
    calc u * w0 = (g * x * g⁻¹) * (g * z * g⁻¹) := by rw [hgx, hw0]
      _ = g * (x * z) * g⁻¹ := by group
      _ = g * t * g⁻¹ := by rw [hxzt]
  have huw0S : u * w0 ∈ S := S.mul_mem pic.u_S hw0S
  have huw0inv : (u * w0) * (u * w0) = 1 := by rw [huw0]; exact conj_inv t pic.t_inv
  have huw01 : u * w0 ≠ 1 := by rw [huw0]; exact conj_ne t ht1
  have huw0Z : u * w0 ∈ Z := by
    refine (pic.cls_Z _ huw0S huw0inv huw01).1 ?_
    rw [huw0]
    exact pic.t_conj.trans (isConj_iff.2 ⟨g, rfl⟩)
  have hzu : z * u = u * z := (pic.z_comm u pic.u_S).symm
  have huzS : u * z ∈ S := S.mul_mem pic.u_S pic.z_S
  have huzinv : (u * z) * (u * z) = 1 := by
    calc u * z * (u * z) = u * (z * u) * z := by group
      _ = u * (u * z) * z := by rw [hzu]
      _ = u * u * (z * z) := by group
      _ = 1 := by rw [pic.u_inv, hzz, one_mul]
  have huz1 : u * z ≠ 1 := fun h' => pic.u_ne_z (by
    have := mul_eq_one_iff_eq_inv.1 h'
    rw [this, hzinv])
  have hw0z : w0 ≠ z := by
    intro h
    exact (A.partition (u * z) huzS huzinv huz1).2 ⟨h ▸ huw0Z, St.uz_X⟩
  have hCw0 : S ⊓ centralizer ({u} : Set G) ⊓ centralizer ({w0} : Set G) =
      cj g (S ⊓ centralizer ({t} : Set G)) := by
    rw [← hTz, cj_inf, hcjT, cj_centralizer_singleton, ← hw0]
  have hcard : Nat.card ↥(S ⊓ centralizer ({u} : Set G) ⊓ centralizer ({w0} : Set G)) = 2 ^ (a + 2) := by
    rw [hCw0, card_cj]; exact A.card_Ct
  obtain ⟨U', hU'⟩ : ∃ U' : Subgroup G, U' = cj g US := ⟨_, rfl⟩
  have hUle : U' ≤ S ⊓ centralizer ({u} : Set G) ⊓ centralizer ({w0} : Set G) := by
    rw [hCw0, hU']; exact cj_mono A.US_le
  have hUnorm : ∀ c ∈ S ⊓ centralizer ({u} : Set G) ⊓ centralizer ({w0} : Set G), ∀ d ∈ U',
      c * d * c⁻¹ ∈ U' := by
    intro c hc d hd
    rw [hCw0, mem_cj] at hc
    rw [hU', mem_cj] at hd ⊢
    have := A.US_normal _ hc _ hd
    have e : g⁻¹ * (c * d * c⁻¹) * g = (g⁻¹ * c * g) * (g⁻¹ * d * g) * (g⁻¹ * c * g)⁻¹ := by group
    rw [e]; exact this
  have hUcard : Nat.card ↥U' = 2 ^ (a - 1) := by rw [hU', card_cj]; exact A.US_card
  have hUdih : IVK.IsDihedralTwoGroup ↥U' (a - 1) := hU' ▸ isDihedralTwoGroup_cj A.US_dih
  have hxzt' : zpowers x ⊔ zpowers z ≤ zpowers z ⊔ zpowers t := by
    refine sup_le (zpowers_le.2 ?_) le_sup_left
    rw [hxz]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers t)) (Subgroup.mem_sup_left (mem_zpowers z))
  have hUinter : ∀ y ∈ U', y ∈ zpowers u ⊔ zpowers w0 → y = 1 := by
    intro y hy hy'
    have h1 : zpowers u ⊔ zpowers w0 = cj g (zpowers x ⊔ zpowers z) := by
      rw [cj_sup, cj_zpowers, cj_zpowers, hgx, ← hw0]
    rw [h1, mem_cj] at hy'
    rw [hU', mem_cj] at hy
    have := A.US_inter _ hy (hxzt' hy')
    have e : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [e, this]; group
  have hUcls : ∀ d' ∈ U', d' * d' = 1 → d' ≠ 1 →
      d' ∈ X ∧ w0 * d' ∈ X ∧ u * w0 * d' ∈ X ∧ u * d' ∈ Z := by
    intro d' hd' hd'2 hd'1
    have hd'C := hUle hd'
    have hd'S : d' ∈ S := hd'C.1.1
    have hd'w0 : w0 * d' = d' * w0 := mem_centralizer_iff.1 hd'C.2 w0 rfl
    obtain ⟨d, hd_def⟩ : ∃ d : G, d = g⁻¹ * d' * g := ⟨_, rfl⟩
    have hd : d ∈ US := by rw [hU', mem_cj] at hd'; rw [hd_def]; exact hd'
    have hdd' : d' = g * d * g⁻¹ := by rw [hd_def]; group
    have hdS : d ∈ S := (A.US_le hd).1
    have hdt : t * d = d * t := mem_centralizer_iff.1 (A.US_le hd).2 t rfl
    have hdz : d * z = z * d := pic.z_comm d hdS
    have hd2 : d * d = 1 := by
      calc d * d = g⁻¹ * (d' * d') * g := by rw [hd_def]; group
        _ = 1 := by rw [hd'2]; group
    have hd1 : d ≠ 1 := fun h => hd'1 (by rw [hdd', h]; group)
    obtain ⟨h1, h2, h3, h4⟩ := A.US_cls d hd hd2 hd1
    have hdne : ∀ c : G, c ∈ zpowers z ⊔ zpowers t → c ≠ 1 → d ≠ c := by
      intro c hc hc1 h
      exact hc1 (by rw [← h]; exact A.US_inter d hd (h ▸ hc))
    have c1 : d' ∈ X := (hXtr d d' hdS hd2 hd1 hd'S hdd').2 h1
    have hzdS : z * d ∈ S := S.mul_mem pic.z_S hdS
    have hzd2 : (z * d) * (z * d) = 1 := by
      calc z * d * (z * d) = z * (d * z) * d := by group
        _ = z * (z * d) * d := by rw [hdz]
        _ = z * z * (d * d) := by group
        _ = 1 := by rw [hzz, hd2, one_mul]
    have hzd1 : z * d ≠ 1 := fun h => hdne z (Subgroup.mem_sup_left (mem_zpowers z)) hz1 (by
      have := eq_inv_of_mul_eq_one_right h
      rw [hzinv] at this
      exact this)
    have hw0d'S : w0 * d' ∈ S := S.mul_mem hw0S hd'S
    have e2 : w0 * d' = g * (z * d) * g⁻¹ := by rw [hw0, hdd']; group
    have c2 : w0 * d' ∈ X := (hXtr (z * d) (w0 * d') hzdS hzd2 hzd1 hw0d'S e2).2 h2
    have htdS : t * d ∈ S := S.mul_mem pic.t_S hdS
    have htd2 : (t * d) * (t * d) = 1 := by
      calc t * d * (t * d) = t * (d * t) * d := by group
        _ = t * (t * d) * d := by rw [← hdt]
        _ = t * t * (d * d) := by group
        _ = 1 := by rw [pic.t_inv, hd2, one_mul]
    have htd1 : t * d ≠ 1 := fun h => hdne t (Subgroup.mem_sup_right (mem_zpowers t)) ht1 (by
      have := eq_inv_of_mul_eq_one_right h
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right pic.t_inv
      rw [htinv] at this
      exact this)
    have huw0d'S : u * w0 * d' ∈ S := S.mul_mem huw0S hd'S
    have e3 : u * w0 * d' = g * (t * d) * g⁻¹ := by rw [huw0, hdd']; group
    have c3 : u * w0 * d' ∈ X := (hXtr (t * d) (u * w0 * d') htdS htd2 htd1 huw0d'S e3).2 h3
    have htzdS : t * z * d ∈ S := S.mul_mem (S.mul_mem pic.t_S pic.z_S) hdS
    have htzd2 : (t * z * d) * (t * z * d) = 1 := by
      have hxd : t * z * d = d * (t * z) := by
        calc t * z * d = t * (z * d) := by group
          _ = t * (d * z) := by rw [hdz]
          _ = (t * d) * z := by group
          _ = (d * t) * z := by rw [hdt]
          _ = d * (t * z) := by group
      calc t * z * d * (t * z * d) = (t * z) * (d * (t * z)) * d := by group
        _ = (t * z) * (t * z * d) * d := by rw [hxd]
        _ = (t * z) * (t * z) * (d * d) := by group
        _ = 1 := by rw [← hxz, hxx, hd2, one_mul]
    have htzmem : t * z ∈ zpowers z ⊔ zpowers t :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers t)) (Subgroup.mem_sup_left (mem_zpowers z))
    have htzd1 : t * z * d ≠ 1 := fun h => hdne (t * z) htzmem (by rw [← hxz]; exact hx1) (by
      have := eq_inv_of_mul_eq_one_right h
      have hxinv : (t * z)⁻¹ = t * z := inv_eq_of_mul_eq_one_right (by rw [← hxz]; exact hxx)
      rw [hxinv] at this
      exact this)
    have hud'S : u * d' ∈ S := S.mul_mem pic.u_S hd'S
    have e4 : u * d' = g * (t * z * d) * g⁻¹ := by
      calc u * d' = (g * x * g⁻¹) * (g * d * g⁻¹) := by rw [hgx, ← hdd']
        _ = g * (x * d) * g⁻¹ := by group
        _ = g * (t * z * d) * g⁻¹ := by rw [hxz]
    have c4 : u * d' ∈ Z := (hZtr (t * z * d) (u * d') htzdS htzd2 htzd1 hud'S e4).2 h4
    exact ⟨c1, c2, c3, c4⟩
  obtain ⟨D₁', D₂', T₁', hD⟩ := St.decomp w0 hw0T' hw0w0 hw0Z hw0z huw0Z hcard U' hUle hUnorm hUcard
    hUdih hUinter hUcls
  have hmemcj : ∀ (H : Subgroup G) (y : G), y ∈ cj g⁻¹ H ↔ g * y * g⁻¹ ∈ H := fun H y => by
    rw [mem_cj, inv_inv]
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : Subgroup G, D₁ = cj g⁻¹ D₁' := ⟨_, rfl⟩
  obtain ⟨D₂, hD₂⟩ : ∃ D₂ : Subgroup G, D₂ = cj g⁻¹ D₂' := ⟨_, rfl⟩
  obtain ⟨T₁, hT₁⟩ : ∃ T₁ : Subgroup G, T₁ = cj g⁻¹ T₁' := ⟨_, rfl⟩
  have mD₁ : ∀ y, y ∈ D₁ ↔ g * y * g⁻¹ ∈ D₁' := fun y => by rw [hD₁]; exact hmemcj _ _
  have mD₂ : ∀ y, y ∈ D₂ ↔ g * y * g⁻¹ ∈ D₂' := fun y => by rw [hD₂]; exact hmemcj _ _
  have mT₁ : ∀ y, y ∈ T₁ ↔ g * y * g⁻¹ ∈ T₁' := fun y => by rw [hT₁]; exact hmemcj _ _
  have mT : ∀ y, y ∈ T ↔ g * y * g⁻¹ ∈ S ⊓ centralizer ({u} : Set G) := fun y => by
    rw [← hcjinv]; exact hmemcj _ _
  have hD₁T : D₁ ≤ T := fun y hy => (mT y).2 (hD.D₁_le ((mD₁ y).1 hy))
  have hD₂T : D₂ ≤ T := fun y hy => (mT y).2 (hD.D₂_le ((mD₂ y).1 hy))
  have hcomm : ∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a := by
    intro a ha b hb
    have h := hD.comm _ ((mD₁ a).1 ha) _ ((mD₂ b).1 hb)
    have e : ∀ c d : G, g * c * g⁻¹ * (g * d * g⁻¹) = g * (c * d) * g⁻¹ := fun c d => by group
    rw [e, e] at h
    exact mul_left_cancel (mul_right_cancel h)
  have hinter : D₁ ⊓ D₂ = ⊥ := by rw [hD₁, hD₂, ← cj_inf, hD.inter, cj_bot]
  have hTle : T ≤ D₁ ⊔ D₂ := fun y hy => by
    have h := hD.T_le ((mT y).1 hy)
    rw [hD₁, hD₂, ← cj_sup, hmemcj]
    exact h
  have hD₁dih : IVK.IsDihedralTwoGroup ↥D₁ a := by
    rw [hD₁]; exact isDihedralTwoGroup_cj hD.D₁_dih
  have hD₂dih : IVK.IsDihedralTwoGroup ↥D₂ a := by
    rw [hD₂]; exact isDihedralTwoGroup_cj hD.D₂_dih
  obtain ⟨t', ht'⟩ : ∃ t' : G, t' = g⁻¹ * (u * z) * g := ⟨_, rfl⟩
  have hgt' : g * t' * g⁻¹ = u * z := by rw [ht']; group
  have hxeq : g⁻¹ * u * g = x := by
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [hgx] at this
    exact this.symm
  have hxt' : x * t' = g⁻¹ * z * g := by
    calc x * t' = (g⁻¹ * u * g) * (g⁻¹ * (u * z) * g) := by rw [hxeq, ht']
      _ = g⁻¹ * (u * u * z) * g := by group
      _ = g⁻¹ * z * g := by rw [pic.u_inv, one_mul]
  have ht'2 : t' * t' = 1 := by
    calc t' * t' = g⁻¹ * ((u * z) * (u * z)) * g := by rw [ht']; group
      _ = 1 := by rw [huzinv]; group
  have ht'1 : t' ≠ 1 := fun h => huz1 (by
    have : u * z = g * t' * g⁻¹ := by rw [ht']; group
    rw [this, h]; group)
  have ht'ord : orderOf t' = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht'2) ht'1
  have hxcen : x ∈ centralizer ({z} : Set G) := by
    refine mem_centralizer_iff.2 (fun h hh => ?_)
    rw [Set.mem_singleton_iff.1 hh, hxz]
    calc z * (t * z) = (z * t) * z := by group
      _ = (t * z) * z := by rw [← htz]
  have hsyl : Syl z x T D₁ D₂ US a t' :=
    { D₁_dih := hD₁dih
      D₂_dih := hD₂dih
      D₁_le := hD₁T
      D₂_le := hD₂T
      comm := hcomm
      inter := hinter
      index := by rw [Subgroup.relIndex_eq_one.2 hTle]; norm_num
      D₁_normal := by
        intro s hs d hd
        obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := (mem_sup_of_comm hcomm).1 (hTle hs)
        have hbd : b₁ * d = d * b₁ := (hcomm d hd b₁ hb₁).symm
        have e : a₁ * b₁ * d * (a₁ * b₁)⁻¹ = a₁ * d * a₁⁻¹ := by
          calc a₁ * b₁ * d * (a₁ * b₁)⁻¹ = a₁ * (b₁ * d) * b₁⁻¹ * a₁⁻¹ := by group
            _ = a₁ * (d * b₁) * b₁⁻¹ * a₁⁻¹ := by rw [hbd]
            _ = a₁ * d * a₁⁻¹ := by group
        rw [e]
        exact D₁.mul_mem (D₁.mul_mem ha₁ hd) (D₁.inv_mem ha₁)
      x_mem := (mD₁ x).2 (by rw [hgx]; exact hD.u_mem)
      x_center := Or.inr (by
        rw [hD₁, center_map_of_cj_eq rfl, hD.center_D₁, cj_zpowers]
        have : g⁻¹ * u * g⁻¹⁻¹ = x := by rw [inv_inv]; exact hxeq
        rw [this])
      z_mem := (mD₁ z).2 (hw0 ▸ hD.w0_mem)
      z_ne := by
        intro h
        have hwu : w0 = u := by rw [hw0, h, hgx]
        exact (A.partition u pic.u_S pic.u_inv pic.u_ne).2 ⟨hwu ▸ hw0Z, St.u_X⟩
      U_syl := pic.US_syl
      U_le := by
        intro y hy
        refine (mD₂ y).2 (hD.U_le ?_)
        rw [hU', mem_cj]
        have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
        rw [e]; exact hy
      U_card := by
        have h := hD.D₂_card
        rw [hU', card_cj] at h
        rw [hD₂, card_cj, h]
      t'_mem := (mD₂ t').2 (by rw [hgt']; exact hD.uz_mem)
      t'_U := by
        have h := hD.uz_U
        rw [hU', mem_cj] at h
        rw [ht']; exact h
      t'_ord := ht'ord
      center_T := by
        have h1 := center_map_of_cj_eq (c := g⁻¹) (H := S ⊓ centralizer ({u} : Set G)) (K := T) hcjinv
        rw [h1, St.center, cj_sup, cj_zpowers, cj_zpowers, inv_inv]
        have e1 : g⁻¹ * z * g = x * t' := hxt'.symm
        rw [e1, hxeq]
        apply le_antisymm
        · refine sup_le (zpowers_le.2 (Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_zpowers x))
            (Subgroup.mem_sup_right (mem_zpowers t')))) (zpowers_le.2 (Subgroup.mem_sup_left (mem_zpowers x)))
        · refine sup_le (zpowers_le.2 (Subgroup.mem_sup_right (mem_zpowers x))) (zpowers_le.2 ?_)
          have h := Subgroup.mul_mem (zpowers (x * t') ⊔ zpowers x)
            (Subgroup.inv_mem _ (Subgroup.mem_sup_right (mem_zpowers x)))
            (Subgroup.mem_sup_left (mem_zpowers (x * t')))
          have e2 : x⁻¹ * (x * t') = t' := by group
          rwa [e2] at h
      t'_conj := by
        have h1 : IsConj u (u * z) := (pic.cls_X (u * z) huzS huzinv huz1).2 St.uz_X
        exact hux.symm.trans (h1.trans (isConj_iff.2 ⟨g⁻¹, by rw [ht']; simp⟩))
      xt'_conj := by
        rw [hxt']
        exact isConj_iff.2 ⟨g⁻¹, by simp⟩ }
  have hcfg : Cfg z x T q :=
    { z_central := pic.z_central
      x_mem := hxcen
      x_nc := ⟨hx2, hxnc⟩
      xz_conj := by rw [hxzt]; exact pic.t_conj
      classes := fun y hy => (pic.classes y hy).imp id (fun h => hux.symm.trans h)
      T_syl := hTsyl
      z_mem_T := hzT
      z_extremal := by
        show IsSylowOf 2 (T ⊓ centralizer ({z} : Set G)) (centralizer ({x, z} : Set G))
        rw [hTz]; exact pic.syl_t
      q_odd := pic.q_odd
      q_gt := pic.q_gt
      I_L2 := pic.I_L2 }
  have hT₁le : T₁ ≤ D₁ := fun y hy => (mD₁ y).2 (hD.T₁_le ((mT₁ y).1 hy))
  have hT₁cyc : IsCyclic ↥T₁ := by rw [hT₁]; exact isCyclic_cj hD.T₁_cyc
  have hx₁ : x ∈ T₁ := (mT₁ x).2 (by rw [hgx]; exact hD.u_T₁)
  have hT₁idx : T₁.relIndex D₁ = 2 := by rw [hT₁, hD₁, relIndex_cj]; exact hD.T₁_idx
  have hT₁card : Nat.card ↥T₁ * 2 = Nat.card ↥D₂ := by
    have h := Subgroup.relIndex_mul_card T₁ D₁
    rw [hT₁idx, inf_eq_left.2 hT₁le] at h
    rw [mul_comm, h, card_of_isDihedralTwoGroup hD₁dih, card_of_isDihedralTwoGroup hD₂dih]
  have hrefl : ∀ y ∈ D₁, y ∉ T₁ → y * y = 1 := by
    intro y hy hyT
    have h := hD.T₁_refl (g * y * g⁻¹) ((mD₁ y).1 hy) (fun h => hyT ((mT₁ y).2 h))
    have e : y * y = g⁻¹ * ((g * y * g⁻¹) * (g * y * g⁻¹)) * g := by group
    rw [e, h]; group
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hsepc : ∀ b ∈ D₁, b ∉ T₁ → ∀ m ∈ T₁ ⊔ D₂, m * m = 1 → m ≠ 1 → m ≠ x →
      ¬ ((IsConj z b ↔ IsConj z m) ∧ (IsConj z (x * b) ↔ IsConj z (x * m))) := by
    intro b hb hbT m hm hm2 hm1 hmx ⟨h1, h2⟩
    have hb2 := hrefl b hb hbT
    have hb1 : b ≠ 1 := fun h => hbT (h ▸ T₁.one_mem)
    have hmT : m ∈ T := (sup_le (hT₁le.trans hD₁T) hD₂T) hm
    have hcb : x * b = b * x := mem_centralizer_iff.1 (hTsyl.le (hD₁T hb)) x rfl
    have hcm : x * m = m * x := mem_centralizer_iff.1 (hTsyl.le hmT) x rfl
    have hb'D : g * b * g⁻¹ ∈ D₁' := (mD₁ b).1 hb
    have hb'S : g * b * g⁻¹ ∈ S := (hD.D₁_le hb'D).1
    have hm' : g * m * g⁻¹ ∈ T₁' ⊔ D₂' := by
      have h := hm
      rw [hT₁, hD₂, ← cj_sup, hmemcj] at h
      exact h
    have hm'S : g * m * g⁻¹ ∈ S :=
      (sup_le (hD.T₁_le.trans hD.D₁_le) hD.D₂_le hm').1
    have hm'u : g * m * g⁻¹ ≠ u := by
      intro h
      apply hmx
      have h' : g * m * g⁻¹ = g * x * g⁻¹ := h.trans hgx.symm
      exact mul_left_cancel (mul_right_cancel h')
    have hxb2 : (x * b) * (x * b) = 1 := by
      calc x * b * (x * b) = x * (b * x) * b := by group
        _ = x * (x * b) * b := by rw [← hcb]
        _ = x * x * (b * b) := by group
        _ = 1 := by rw [hxx, hb2, one_mul]
    have hxm2 : (x * m) * (x * m) = 1 := by
      calc x * m * (x * m) = x * (m * x) * m := by group
        _ = x * (x * m) * m := by rw [← hcm]
        _ = x * x * (m * m) := by group
        _ = 1 := by rw [hxx, hm2, one_mul]
    have hxb1 : x * b ≠ 1 := fun h => hbT (by
      have := eq_inv_of_mul_eq_one_right h
      rw [hxinv] at this
      exact this ▸ hx₁)
    have hxm1 : x * m ≠ 1 := fun h => hmx (by
      have := eq_inv_of_mul_eq_one_right h
      rw [hxinv] at this
      exact this)
    have eb : u * (g * b * g⁻¹) = g * (x * b) * g⁻¹ := by rw [← hgx]; group
    have em : u * (g * m * g⁻¹) = g * (x * m) * g⁻¹ := by rw [← hgx]; group
    refine hD.sep (g * b * g⁻¹) hb'D (fun h => hbT ((mT₁ b).2 h)) (g * m * g⁻¹) hm' (conj_inv m hm2)
      (conj_ne m hm1) hm'u ⟨?_, ?_⟩
    · exact (hZ' b _ rfl hb'S hb2 hb1).trans (h1.trans (hZ' m _ rfl hm'S hm2 hm1).symm)
    · exact (hZ' (x * b) _ eb (S.mul_mem pic.u_S hb'S) hxb2 hxb1).trans
        (h2.trans (hZ' (x * m) _ em (S.mul_mem pic.u_S hm'S) hxm2 hxm1).symm)
  have hD₂cl : ∀ s ∈ D₂, orderOf s = 2 → IsConj x s := by
    intro s hs hs2
    have hss : s * s = 1 := by
      have := pow_orderOf_eq_one s
      rwa [hs2, pow_two] at this
    have hs1 : s ≠ 1 := fun h => by
      rw [h, orderOf_one] at hs2
      exact absurd hs2 (by decide)
    have hs'D : g * s * g⁻¹ ∈ D₂' := (mD₂ s).1 hs
    have hs'S : g * s * g⁻¹ ∈ S := (hD.D₂_le hs'D).1
    have h1 : IsConj u (g * s * g⁻¹) :=
      (pic.cls_X _ hs'S (conj_inv s hss) (conj_ne s hs1)).2
        (hD.D₂_cls (g * s * g⁻¹) hs'D (conj_inv s hss) (conj_ne s hs1)).1
    exact hux.symm.trans (h1.trans (isConj_iff.2 ⟨g⁻¹, by group⟩))
  have hD₂gen : D₂ ≤ closure {s : G | s ∈ D₂ ∧ orderOf s = 2} := le_closure_involutions hD₂dih
  have hxD : x ∈ ⁅D₁, D₁⁆ := by
    rw [hD₁, ← cj_commutator, hmemcj, hgx]
    exact hD.u_derived
  have hΩ : ∀ y ∈ ⁅T, T⁆, y * y = 1 → y = 1 ∨ y = x ∨ y = t' ∨ y = x * t' := by
    intro y hy hy2
    have hy' : g * y * g⁻¹ ∈ ⁅S ⊓ centralizer ({u} : Set G), S ⊓ centralizer ({u} : Set G)⁆ := by
      have h := hy
      rw [← hcjinv, ← cj_commutator, hmemcj] at h
      exact h
    have h := hD.derived (g * y * g⁻¹) hy' (conj_inv y hy2)
    have hy_eq : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    rcases mem_sup_zpowers_invol hzz pic.u_inv hzu h with h | h | h | h
    · left; rw [hy_eq, h]; group
    · right; right; right
      rw [hy_eq, h, hxt']
    · right; left
      rw [hy_eq, h, hxeq]
    · right; right; left
      rw [hy_eq, h, hzu, ht']
  have hD₂card : Nat.card ↥D₂ = 2 * Nat.card ↥US := by
    have h := hD.D₂_card
    rw [hU', card_cj] at h
    rw [hD₂, card_cj, h]
  exact ⟨T, D₁, D₂, T₁, t', hcfg, hsyl, hTle, hT₁le, hT₁cyc, hx₁, hT₁idx, hT₁card, hrefl, hsepc, hD₂cl,
    hD₂gen, hxD, hΩ, hD₂card⟩

end Main

end CFSG.GH74.GLS.Stage2.Local.P27
