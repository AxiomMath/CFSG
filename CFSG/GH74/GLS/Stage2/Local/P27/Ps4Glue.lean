module

public import CFSG.GH74.GLS.Stage2.Local.P27.L4Glue
public import CFSG.GH74.GLS.Stage2.Local.P27.P3TransferCos
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Compl

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Ps4Out (z x : G) (q : ℕ) (T D₁ D₂ T₁ M : Subgroup G) (n : ℕ) (t' : G) : Prop where
  cfg : Cfg z x T q
  syl : Syl z x T D₁ D₂ D₂ n t'
  I_le_J : Ixz z x ≤ Jx x
  T₁_le : T₁ ≤ D₁
  x_T₁ : x ∈ T₁
  T₁_cyc : IsCyclic ↥T₁
  T₁_card : Nat.card ↥T₁ * 2 = Nat.card ↥D₂
  CTz : ∀ g ∈ T, g * z = z * g → g ∈ D₁ ⊔ D₂
  D₂_M : D₂ ≤ M
  M_T : M ≤ T
  D₂_J : D₂ ≤ Jx x
  sep : ∀ s ∈ T, orderOf s = 2 → s ∉ M → s ∉ ⁅centralizer ({x} : Set G), centralizer ({x} : Set G)⁆
  cos : ∀ w ∈ T, w ∉ M → ∃ d ∈ D₂, orderOf (w * d) = 2
  Mcomm : ⁅M, M⁆ ≤ D₂
  M_D₁ : ∀ g ∈ M, g ∈ D₁ → g ∈ T₁
  M_DD : ∀ g ∈ M, g ∈ D₁ ⊔ D₂ → g ∈ T₁ ⊔ D₂
  index_eq : (D₁ ⊔ D₂).relIndex T = 2

theorem ps4_out {z t u x : G} {S US : Subgroup G} {a q : ℕ} {Z X : Set G}
    (pic : L4Pic z t u x S US q Z X)
    (A : Ps4Actual S z t a Z X US) (SC : Ps4StdC S z u a Z X) :
    ∃ (T D₁ T₁ M : Subgroup G) (n : ℕ) (t' : G) (T₁s : Subgroup G),
      Ps4Out z x q T D₁ US T₁ M n t' ∧ Ps4Compl T D₁ US T₁s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have St : Ps4Std S z u a Z X := SC.std
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
  have hcard : Nat.card ↥(S ⊓ centralizer ({u} : Set G) ⊓ centralizer ({w0} : Set G)) = 2 ^ (a + 1) := by
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
  obtain ⟨D₁', T₁', M', T₁s', hD, hC⟩ := SC.compl w0 hw0T' hw0w0 hw0Z hw0z huw0Z hcard U' hUle hUnorm
    hUcard hUdih hUinter hUcls
  have hmemcj : ∀ (H : Subgroup G) (y : G), y ∈ cj g⁻¹ H ↔ g * y * g⁻¹ ∈ H := fun H y => by
    rw [mem_cj, inv_inv]
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : Subgroup G, D₁ = cj g⁻¹ D₁' := ⟨_, rfl⟩
  obtain ⟨T₁, hT₁⟩ : ∃ T₁ : Subgroup G, T₁ = cj g⁻¹ T₁' := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Subgroup G, M = cj g⁻¹ M' := ⟨_, rfl⟩
  have hUS : US = cj g⁻¹ U' := by rw [hU', cj_cj_inv]
  have mD₁ : ∀ y, y ∈ D₁ ↔ g * y * g⁻¹ ∈ D₁' := fun y => by rw [hD₁]; exact hmemcj _ _
  have mT₁ : ∀ y, y ∈ T₁ ↔ g * y * g⁻¹ ∈ T₁' := fun y => by rw [hT₁]; exact hmemcj _ _
  have mM : ∀ y, y ∈ M ↔ g * y * g⁻¹ ∈ M' := fun y => by rw [hM]; exact hmemcj _ _
  have mU : ∀ y, y ∈ US ↔ g * y * g⁻¹ ∈ U' := fun y => by rw [hUS]; exact hmemcj _ _
  have mT : ∀ y, y ∈ T ↔ g * y * g⁻¹ ∈ S ⊓ centralizer ({u} : Set G) := fun y => by
    rw [← hcjinv]; exact hmemcj _ _
  have hD₁T : D₁ ≤ T := fun y hy => (mT y).2 (hD.D₁_le ((mD₁ y).1 hy))
  have hD₂T : US ≤ T := fun y hy => (mT y).2 (hD.D₂_le ((mU y).1 hy))
  have hcomm : ∀ a ∈ D₁, ∀ b ∈ US, a * b = b * a := by
    intro a ha b hb
    have h := hD.comm _ ((mD₁ a).1 ha) _ ((mU b).1 hb)
    have e : ∀ c d : G, g * c * g⁻¹ * (g * d * g⁻¹) = g * (c * d) * g⁻¹ := fun c d => by group
    rw [e, e] at h
    exact mul_left_cancel (mul_right_cancel h)
  have hinter : D₁ ⊓ US = ⊥ := by rw [hD₁, hUS, ← cj_inf, hD.inter, cj_bot]
  have hidx : (D₁ ⊔ US).relIndex T = 2 := by
    rw [hD₁, hUS, ← cj_sup, ← hcjinv, relIndex_cj]
    exact hD.index
  have hD₁dih : IVK.IsDihedralTwoGroup ↥D₁ (a - 1) := by
    rw [hD₁]; exact isDihedralTwoGroup_cj hD.D₁_dih
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
  have ht'US : t' ∈ US := (mU t').2 (by rw [hgt']; exact hD.uz_mem)
  have hsyl : Syl z x T D₁ US US (a - 1) t' :=
    { D₁_dih := hD₁dih
      D₂_dih := A.US_dih
      D₁_le := hD₁T
      D₂_le := hD₂T
      comm := hcomm
      inter := hinter
      index := by rw [hidx]
      D₁_normal := by
        intro s hs d hd
        have h := hD.D₁_normal (g * s * g⁻¹) ((mT s).1 hs) (g * d * g⁻¹) ((mD₁ d).1 hd)
        have e : g * s * g⁻¹ * (g * d * g⁻¹) * (g * s * g⁻¹)⁻¹ = g * (s * d * s⁻¹) * g⁻¹ := by group
        rw [e] at h
        exact (mD₁ _).2 h
      x_mem := (mD₁ x).2 (by rw [hgx]; exact hD.u_mem)
      x_center := by
        rcases hD.center_D₁ with h3 | hc
        · left; omega
        · right
          rw [hD₁, center_map_of_cj_eq rfl, hc, cj_zpowers]
          have : g⁻¹ * u * g⁻¹⁻¹ = x := by rw [inv_inv]; exact hxeq
          rw [this]
      z_mem := (mD₁ z).2 (hw0 ▸ hD.w0_mem)
      z_ne := by
        intro h
        have hwu : w0 = u := by rw [hw0, h, hgx]
        exact (A.partition u pic.u_S pic.u_inv pic.u_ne).2 ⟨hwu ▸ hw0Z, St.u_X⟩
      U_syl := pic.US_syl
      U_le := le_refl _
      U_card := Nat.le_mul_of_pos_left _ (by norm_num)
      t'_mem := ht'US
      t'_U := ht'US
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
  have hT₁card : Nat.card ↥T₁ * 2 = Nat.card ↥US := by
    have h := Subgroup.relIndex_mul_card T₁ D₁
    rw [hT₁idx, inf_eq_left.2 hT₁le] at h
    rw [mul_comm, h, card_of_isDihedralTwoGroup hD₁dih, card_of_isDihedralTwoGroup A.US_dih]
  have hMT : M ≤ T := fun y hy => (mT y).2 (hD.M_le ((mM y).1 hy))
  have hUM : US ≤ M := fun y hy => (mM y).2 (hD.R_le (Subgroup.mem_sup_right ((mU y).1 hy)))
  have hUJ : US ≤ Jx x := pic.US_syl.le.trans pic.I_le_J
  have hMder : ⁅M, M⁆ ≤ US := by
    rw [hM, hUS, ← cj_commutator]
    exact cj_mono hD.M_der
  have hMDD : ∀ y ∈ M, y ∈ D₁ ⊔ US → y ∈ T₁ ⊔ US := by
    intro y hyM hyD
    have h := hD.M_inter ⟨(mM y).1 hyM, by
      have := hyD
      rw [hD₁, hUS, ← cj_sup, hmemcj] at this
      exact this⟩
    rw [hT₁, hUS, ← cj_sup, hmemcj]
    exact h
  have hMD₁ : ∀ y ∈ M, y ∈ D₁ → y ∈ T₁ := by
    intro y hyM hyD
    have hyDD : y ∈ T₁ ⊔ US := hMDD y hyM (Subgroup.mem_sup_left hyD)
    have hc₁ : ∀ a ∈ T₁, ∀ b ∈ US, a * b = b * a := fun a ha b hb => hcomm a (hT₁le ha) b hb
    obtain ⟨c, hc, b, hb, hcb⟩ := (mem_sup_of_comm hc₁).1 hyDD
    have hb1 : b ∈ D₁ ⊓ US := by
      refine ⟨?_, hb⟩
      have : b = c⁻¹ * y := by rw [← hcb]; group
      rw [this]
      exact D₁.mul_mem (D₁.inv_mem (hT₁le hc)) hyD
    rw [hinter, Subgroup.mem_bot] at hb1
    rw [← hcb, hb1, mul_one]
    exact hc
  have hCTz : ∀ y ∈ T, y * z = z * y → y ∈ D₁ ⊔ US := by
    intro y hyT hyz
    have h := hD.CTw0 (g * y * g⁻¹) ((mT y).1 hyT) (by
      rw [hw0]
      calc g * y * g⁻¹ * (g * z * g⁻¹) = g * (y * z) * g⁻¹ := by group
        _ = g * (z * y) * g⁻¹ := by rw [hyz]
        _ = g * z * g⁻¹ * (g * y * g⁻¹) := by group)
    rw [hD₁, hUS, ← cj_sup, hmemcj]
    exact h
  have hcos : ∀ w ∈ T, w ∉ M → ∃ d ∈ US, orderOf (w * d) = 2 := by
    intro w hwT hwM
    obtain ⟨e', he', hse⟩ := hD.M_cos (g * w * g⁻¹) ((mT w).1 hwT) (fun h => hwM ((mM w).2 h))
    refine ⟨g⁻¹ * e' * g, ?_, ?_⟩
    · rw [mU]
      have e : g * (g⁻¹ * e' * g) * g⁻¹ = e' := by group
      rw [e]; exact he'
    · have e : g * (w * (g⁻¹ * e' * g)) * g⁻¹ = g * w * g⁻¹ * e' := by group
      have hsq : (w * (g⁻¹ * e' * g)) * (w * (g⁻¹ * e' * g)) = 1 := by
        have h2 : (g * (w * (g⁻¹ * e' * g)) * g⁻¹) * (g * (w * (g⁻¹ * e' * g)) * g⁻¹) = 1 := by
          rw [e]; exact hse
        have h3 : (w * (g⁻¹ * e' * g)) * (w * (g⁻¹ * e' * g)) =
            g⁻¹ * ((g * (w * (g⁻¹ * e' * g)) * g⁻¹) * (g * (w * (g⁻¹ * e' * g)) * g⁻¹)) * g := by group
        rw [h3, h2]; group
      have hne : w * (g⁻¹ * e' * g) ≠ 1 := by
        intro h1
        apply hwM
        have hd : g⁻¹ * e' * g ∈ M := hUM ((mU _).2 (by
          have e' : g * (g⁻¹ * e' * g) * g⁻¹ = e' := by group
          rw [e']; exact he'))
        have : w = (g⁻¹ * e' * g)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [this]
        exact M.inv_mem hd
      exact orderOf_eq_prime (by rw [pow_two]; exact hsq) hne
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hT₁M : T₁ ≤ M := fun y hy => (mM y).2 (hD.R_le (Subgroup.mem_sup_left ((mT₁ y).1 hy)))
  have hsep : ∀ s ∈ T, orderOf s = 2 → s ∉ M → s ∉ ⁅centralizer ({x} : Set G), centralizer ({x} : Set G)⁆ := by
    intro s hsT hs2 hsM
    have hss : s * s = 1 := by
      have := pow_orderOf_eq_one s
      rwa [hs2, pow_two] at this
    have hs1 : s ≠ 1 := fun h => by
      rw [h, orderOf_one] at hs2
      exact absurd hs2 (by decide)
    refine not_mem_commutator_of_sep hTsyl hMT (by rw [hM, ← hcjinv, relIndex_cj]; exact hD.M_idx) hsT hsM hss ?_
    intro g' hg' hmT hmM
    have hg'x : x * g' = g' * x := mem_centralizer_iff.1 hg' x rfl
    have hgx' : g'⁻¹ * x * g' = x := by
      rw [mul_assoc, hg'x, ← mul_assoc]
      simp
    have hsx : x * s = s * x := mem_centralizer_iff.1 (hTsyl.le hsT) x rfl
    have hm2 : (g'⁻¹ * s * g') * (g'⁻¹ * s * g') = 1 := by
      calc (g'⁻¹ * s * g') * (g'⁻¹ * s * g') = g'⁻¹ * (s * s) * g' := by group
        _ = 1 := by rw [hss]; group
    have hm1 : g'⁻¹ * s * g' ≠ 1 := fun h => hs1 (by
      have : s = g' * (g'⁻¹ * s * g') * g'⁻¹ := by group
      rw [this, h]; group)
    have hmx : g'⁻¹ * s * g' ≠ x := by
      intro h
      apply hsM
      have : s = g' * (g'⁻¹ * s * g') * g'⁻¹ := by group
      have hgg : g' * x * g'⁻¹ = x := by
        calc g' * x * g'⁻¹ = (g' * x) * g'⁻¹ := rfl
          _ = (x * g') * g'⁻¹ := by rw [← hg'x]
          _ = x := by group
      rw [this, h, hgg]
      exact hT₁M hx₁
    have hs'T : g * s * g⁻¹ ∈ S ⊓ centralizer ({u} : Set G) := (mT s).1 hsT
    have hs'M : g * s * g⁻¹ ∉ M' := fun h => hsM ((mM s).2 h)
    have hm'M : g * (g'⁻¹ * s * g') * g⁻¹ ∈ M' := (mM _).1 hmM
    have hm'S : g * (g'⁻¹ * s * g') * g⁻¹ ∈ S := (hD.M_le hm'M).1
    have hs'S : g * s * g⁻¹ ∈ S := hs'T.1
    have hm'u : g * (g'⁻¹ * s * g') * g⁻¹ ≠ u := by
      intro h
      apply hmx
      have h' : g * (g'⁻¹ * s * g') * g⁻¹ = g * x * g⁻¹ := h.trans hgx.symm
      exact mul_left_cancel (mul_right_cancel h')
    have hxs2 : (x * s) * (x * s) = 1 := by
      calc x * s * (x * s) = x * (s * x) * s := by group
        _ = x * (x * s) * s := by rw [← hsx]
        _ = x * x * (s * s) := by group
        _ = 1 := by rw [hxx, hss, one_mul]
    have hxs1 : x * s ≠ 1 := fun h => hsM (by
      have := eq_inv_of_mul_eq_one_right h
      rw [hxinv] at this
      rw [this]
      exact hT₁M hx₁)
    have hxm_eq : x * (g'⁻¹ * s * g') = g'⁻¹ * (x * s) * g' := by
      calc x * (g'⁻¹ * s * g') = (g'⁻¹ * x * g') * (g'⁻¹ * s * g') := by rw [hgx']
        _ = g'⁻¹ * (x * s) * g' := by group
    have hxm2 : (x * (g'⁻¹ * s * g')) * (x * (g'⁻¹ * s * g')) = 1 := by
      rw [hxm_eq]
      calc g'⁻¹ * (x * s) * g' * (g'⁻¹ * (x * s) * g') = g'⁻¹ * ((x * s) * (x * s)) * g' := by group
        _ = 1 := by rw [hxs2]; group
    have hxm1 : x * (g'⁻¹ * s * g') ≠ 1 := fun h => hmx (by
      have := eq_inv_of_mul_eq_one_right h
      rw [hxinv] at this
      exact this)
    have eS : u * (g * s * g⁻¹) = g * (x * s) * g⁻¹ := by rw [← hgx]; group
    have eM : u * (g * (g'⁻¹ * s * g') * g⁻¹) = g * (x * (g'⁻¹ * s * g')) * g⁻¹ := by
      rw [← hgx]; group
    have hconj1 : IsConj s (g'⁻¹ * s * g') := isConj_iff.2 ⟨g'⁻¹, by simp⟩
    have hconj2 : IsConj (x * s) (x * (g'⁻¹ * s * g')) :=
      isConj_iff.2 ⟨g'⁻¹, by rw [hxm_eq]; simp⟩
    refine hD.M_sep (g * s * g⁻¹) hs'T hs'M (conj_inv s hss) (g * (g'⁻¹ * s * g') * g⁻¹) hm'M
      (conj_inv _ hm2) (conj_ne _ hm1) hm'u ⟨?_, ?_⟩
    · have hmid : IsConj z s ↔ IsConj z (g'⁻¹ * s * g') :=
        ⟨fun h => h.trans hconj1, fun h => h.trans hconj1.symm⟩
      exact Iff.trans (Iff.trans (hZ' s _ rfl hs'S hss hs1) hmid) (hZ' _ _ rfl hm'S hm2 hm1).symm
    · have hmid : IsConj z (x * s) ↔ IsConj z (x * (g'⁻¹ * s * g')) :=
        ⟨fun h => h.trans hconj2, fun h => h.trans hconj2.symm⟩
      exact Iff.trans (Iff.trans (hZ' (x * s) _ eS (S.mul_mem pic.u_S hs'S) hxs2 hxs1) hmid)
        (hZ' (x * (g'⁻¹ * s * g')) _ eM (S.mul_mem pic.u_S hm'S) hxm2 hxm1).symm
  obtain ⟨T₁s, hT₁s⟩ : ∃ T₁s : Subgroup G, T₁s = cj g⁻¹ T₁s' := ⟨_, rfl⟩
  have hcompl : Ps4Compl T D₁ US T₁s := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hT₁s]
      exact (cj_mono (c := g⁻¹) hC.le).trans hcjinv.le
    · rw [hT₁s]
      obtain ⟨m, hm⟩ := hC.dih
      exact ⟨m, isDihedralOrder_of_mulEquiv (cjEquiv g⁻¹ T₁s') hm⟩
    · rw [hD₁, hT₁s]
      exact cj_mono hC.D₁_le
    · rw [hT₁s, hUS, ← cj_inf, hC.inf, cj_bot]
    · rw [hUS, hT₁s, ← cj_sup, hC.sup, hcjinv]
  exact ⟨T, D₁, T₁, M, a - 1, t', T₁s, ⟨hcfg, hsyl, pic.I_le_J, hT₁le, hx₁, hT₁cyc, hT₁card, hCTz, hUM, hMT,
    hUJ, hsep, hcos, hMder, hMD₁, hMDD, hidx⟩, hcompl⟩

end CFSG.GH74.GLS.Stage2.Local.P27
