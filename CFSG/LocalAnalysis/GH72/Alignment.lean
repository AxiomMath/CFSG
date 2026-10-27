module

public import CFSG.LocalAnalysis.GH72.DDSubgroups
public import CFSG.LocalAnalysis.GH72.DDAut
public import CFSG.Walter.PSL2Facts.Odd
public import CFSG.Quasithin.EmptyFaithful.ModBR4Core
public import CFSG.GroupTheory.PSubgroupLeOfPrimeNotDvdIndex

public section

namespace CFSG.GH72

open Subgroup
open scoped MatrixGroups
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)
open CFSG.CGT.Foote81L6 (mem_sup_iff_of_le_normalizer le_normalizer_of_comm
  card_sup_of_le_normalizer)
open CFSG.CGT.Foote81L6.TStruct (eq_and_eq_of_mul_eq_mul)

variable {G : Type} [Group G]

theorem IsDih.exists_mul_eq_of_mem {D : Subgroup G} (hD : IsDih D) {v : G} (hv : v ∈ D) :
    ∃ a ∈ D, ∃ b ∈ D, a * a = 1 ∧ b * b = 1 ∧ v = a * b := by
  obtain ⟨m, -, ⟨e⟩⟩ := hD
  have key : ∀ d : DihedralGroup (2 ^ m), ∃ a b : DihedralGroup (2 ^ m),
      a * a = 1 ∧ b * b = 1 ∧ d = a * b := by
    rintro (i | i)
    · exact ⟨DihedralGroup.sr 0, DihedralGroup.sr i, DihedralGroup.sr_mul_self 0,
        DihedralGroup.sr_mul_self i, by rw [DihedralGroup.sr_mul_sr, sub_zero]⟩
    · exact ⟨DihedralGroup.sr i, 1, DihedralGroup.sr_mul_self i, mul_one 1, (mul_one _).symm⟩
  obtain ⟨a, b, ha, hb, hab⟩ := key (e ⟨v, hv⟩)
  refine ⟨(e.symm a : G), (e.symm a).2, (e.symm b : G), (e.symm b).2, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_mul, ← map_mul, ha, map_one, Subgroup.coe_one]
  · rw [← Subgroup.coe_mul, ← map_mul, hb, map_one, Subgroup.coe_one]
  · rw [← Subgroup.coe_mul, ← map_mul, ← hab, MulEquiv.symm_apply_apply]

theorem IsDih.four_le_card {D : Subgroup G} (hD : IsDih D) : 4 ≤ Nat.card D := by
  obtain ⟨m, hm, ⟨e⟩⟩ := hD
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

theorem IsDih.exists_involution_ne [Finite G] {D : Subgroup G} (hD : IsDih D) (c : G) :
    ∃ u ∈ D, u * u = 1 ∧ u ≠ 1 ∧ u ≠ c := by
  by_contra! h
  have hle : D ≤ zpowers c := by
    intro v hv
    obtain ⟨a, ha, b, hb, ha2, hb2, rfl⟩ := hD.exists_mul_eq_of_mem hv
    have key : ∀ x ∈ D, x * x = 1 → x ∈ zpowers c := by
      intro x hx hx2
      by_cases hx1 : x = 1
      · rw [hx1]
        exact one_mem _
      · rw [h x hx hx2 hx1]
        exact mem_zpowers c
    exact mul_mem (key a ha ha2) (key b hb hb2)
  have hc2 : c * c = 1 := by
    obtain ⟨u, hu, hu2, hu1⟩ : ∃ u ∈ D, u * u = 1 ∧ u ≠ 1 := by
      obtain ⟨m, hm, ⟨e⟩⟩ := hD
      refine ⟨(e.symm (DihedralGroup.sr 0) : G), (e.symm _).2, ?_, ?_⟩
      · rw [← Subgroup.coe_mul, ← map_mul, DihedralGroup.sr_mul_self, map_one, Subgroup.coe_one]
      · intro h1
        have : e.symm (DihedralGroup.sr 0) = 1 := Subtype.ext h1
        rw [MulEquiv.map_eq_one_iff, DihedralGroup.one_def] at this
        cases this
    rw [← h u hu hu2 hu1]
    exact hu2
  have hcard : Nat.card D ≤ 2 := by
    calc Nat.card D ≤ Nat.card (zpowers c) := Subgroup.card_le_of_le hle
      _ = orderOf c := Nat.card_zpowers c
      _ ≤ 2 := Nat.le_of_dvd (by norm_num)
          (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hc2))
  have := hD.four_le_card
  omega

private theorem isConj_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ a b : Y, orderOf a = 2 → orderOf b = 2 → IsConj a b) {x y : X} (hx : orderOf x = 2)
    (hy : orderOf y = 2) : IsConj x y := by
  have h' := h (e x) (e y) ((MulEquiv.orderOf_eq e x).trans hx)
    ((MulEquiv.orderOf_eq e y).trans hy)
  simpa using e.symm.toMonoidHom.map_isConj h'

theorem IsL2OrA7.isConj {X : Type*} [Group X] (hX : IsL2OrA7 X 5) {x y : X}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  rcases hX with hA | ⟨p, k, hp, hp2, h5, hE⟩
  · obtain ⟨e⟩ := hA
    refine isConj_of_mulEquiv e (fun a b ha hb => ?_) hx hy
    have hsq : ∀ c : alternatingGroup (Fin 7), orderOf c = 2 → c * c = 1 := fun c hc => by
      rw [← pow_two, ← hc, pow_orderOf_eq_one]
    have hne : ∀ c : alternatingGroup (Fin 7), orderOf c = 2 → c ≠ 1 := fun c hc h1 => by
      rw [h1, orderOf_one] at hc
      omega
    exact CFSG.Quasithin.ModB.alt_involution_isConj (by norm_num) le_rfl (hne a ha) (hsq a ha)
      (hne b hb) (hsq b hb)
  · obtain ⟨e⟩ := hE
    have hpo : Odd p := hp.out.odd_of_ne_two hp2
    have hk : 0 < k := Nat.pos_of_ne_zero fun h => by rw [h, pow_zero] at h5; omega
    exact isConj_of_mulEquiv e
      (fun a b ha hb => CFSG.Walter.psl2_odd_isConj_of_orderOf_eq_two hpo hk ha hb) hx hy

theorem IsL2OrA7.hasDihedralSylowTwo {X : Type} [Group X] [Finite X] (hX : IsL2OrA7 X 5) :
    CFSG.GorensteinWalter.HasDihedralSylowTwo X := by
  rcases hX with hA | ⟨p, k, hp, hp2, h5, hE⟩
  · obtain ⟨e⟩ := hA
    exact CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv e
      CFSG.GorensteinWalter.hasDihedralSylowTwo_alternatingGroupSeven
  · obtain ⟨e⟩ := hE
    have hk : k ≠ 0 := fun h => by rw [h, pow_zero] at h5; omega
    have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p k)) :=
      ⟨p, k, hp.out, hp.out.odd_of_ne_two hp2, Nat.one_le_iff_ne_zero.mpr hk,
        GaloisField.card p k hk⟩
    exact CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv e
      (CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model (GaloisField p k) hodd)

theorem isDih_of_isSylowOf {V L : Subgroup G} (hV : IsSylowOf 2 V L)
    (hL : CFSG.GorensteinWalter.HasDihedralSylowTwo L) : IsDih V := by
  obtain ⟨Q, rfl⟩ := hV
  obtain ⟨m, hm, ⟨e⟩⟩ := hL Q
  exact ⟨m, hm, ⟨(Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective).symm.trans e⟩⟩

private theorem exists_orderOf_eq_two_of_ne_bot [Finite G] {H : Subgroup G} (hH : IsPGroup 2 H)
    (hne : H ≠ ⊥) : ∃ x ∈ H, orderOf x = 2 := by
  rcases hH.card_eq_or_dvd with h1 | h2
  · exact absurd (Subgroup.card_eq_one.mp h1) hne
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 h2
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem exists_sylow_of_isSylowOf_top [Finite G] {T : Subgroup G} (hT : IsSylowOf 2 T ⊤) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = T := by
  rw [isSylowOf_iff] at hT
  obtain ⟨-, hP, hdvd⟩ := hT
  rw [Subgroup.relIndex_top_right] at hdvd
  exact ⟨hP.toSylow hdvd, IsPGroup.toSylow_coe hP hdvd⟩

section Core

variable {T T₁ T₂ : Subgroup G}

theorem fusion_trichotomy
    (hfus : ∀ x ∈ T, ∀ y ∈ T, orderOf x = 2 → IsConj x y →
      (x ∈ T₁ ↔ y ∈ T₁) ∧ (x ∈ T₂ ↔ y ∈ T₂))
    {V : Subgroup G} (hVT : V ≤ T)
    (hconj : ∀ x ∈ V, ∀ y ∈ V, orderOf x = 2 → orderOf y = 2 → IsConj x y) :
    (∀ x ∈ V, orderOf x = 2 → x ∈ T₁) ∨ (∀ x ∈ V, orderOf x = 2 → x ∈ T₂) ∨
      ∀ x ∈ V, orderOf x = 2 → x ∉ T₁ ∧ x ∉ T₂ := by
  by_cases h₁ : ∃ x₀ ∈ V, orderOf x₀ = 2 ∧ x₀ ∈ T₁
  · obtain ⟨x₀, hx₀V, hx₀2, hx₀T₁⟩ := h₁
    exact Or.inl fun x hxV hx2 =>
      ((hfus x₀ (hVT hx₀V) x (hVT hxV) hx₀2 (hconj x₀ hx₀V x hxV hx₀2 hx2)).1).1 hx₀T₁
  · by_cases h₂ : ∃ x₀ ∈ V, orderOf x₀ = 2 ∧ x₀ ∈ T₂
    · obtain ⟨x₀, hx₀V, hx₀2, hx₀T₂⟩ := h₂
      exact Or.inr (Or.inl fun x hxV hx2 =>
        ((hfus x₀ (hVT hx₀V) x (hVT hxV) hx₀2 (hconj x₀ hx₀V x hxV hx₀2 hx2)).2).1 hx₀T₂)
    · exact Or.inr (Or.inr fun x hxV hx2 =>
        ⟨fun h => h₁ ⟨x, hxV, hx2, h⟩, fun h => h₂ ⟨x, hxV, hx2, h⟩⟩)

theorem IsDih.le_of_forall_involution {V W : Subgroup G} (hV : IsDih V)
    (h : ∀ x ∈ V, orderOf x = 2 → x ∈ W) : V ≤ W := by
  intro v hv
  obtain ⟨a, ha, b, hb, ha2, hb2, rfl⟩ := hV.exists_mul_eq_of_mem hv
  have key : ∀ c ∈ V, c * c = 1 → c ∈ W := by
    intro c hc hc2
    by_cases hc1 : c = 1
    · rw [hc1]
      exact W.one_mem
    · exact h c hc (orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1)
  exact W.mul_mem (key a ha ha2) (key b hb hb2)

theorem DDDecomp.eq_of_sup_eq_of_le (hd : DDDecomp T T₁ T₂) {V W : Subgroup G}
    (hsup : V ⊔ W = T) (hV : V ≤ T₁) (hW : W ≤ T₂) : V = T₁ ∧ W = T₂ := by
  have hdec : ∀ t ∈ T, ∃ v ∈ V, ∃ w ∈ W, t = v * w := fun t ht =>
    (mem_sup_iff_of_le_normalizer
      (le_normalizer_of_comm fun v hv w hw => hd.comm (hV hv) (hW hw))).1 (hsup ▸ ht)
  constructor
  · refine le_antisymm hV fun t ht => ?_
    obtain ⟨v, hv, w, hw, rfl⟩ := hdec _ (hd.le_left ht)
    have := hd.eq_and_eq ht (hV hv) (one_mem _) (hW hw) (by rw [mul_one])
    rw [← this.2, mul_one]
    exact hv
  · refine le_antisymm hW fun t ht => ?_
    obtain ⟨v, hv, w, hw, rfl⟩ := hdec _ (hd.le_right ht)
    have := hd.eq_and_eq (one_mem _) (hV hv) ht (hW hw) (by rw [one_mul])
    rw [← this.1, one_mul]
    exact hw

theorem DDDecomp.not_le_of_sup_eq (hd : DDDecomp T T₁ T₂) {V W : Subgroup G}
    (hsup : V ⊔ W = T) : ¬ (V ≤ T₁ ∧ W ≤ T₁) ∧ ¬ (V ≤ T₂ ∧ W ≤ T₂) := by
  have key : ∀ {A B : Subgroup G}, A ⊓ B = ⊥ → IsDih B → A ⊔ B = T → V ≤ A → W ≤ A →
      False := by
    intro A B hAB hB hAB' hVA hWA
    have hBA : B ≤ A := le_sup_right.trans (hAB' ▸ hsup ▸ sup_le hVA hWA)
    have hB1 : B = ⊥ := le_bot_iff.mp (hAB ▸ le_inf hBA le_rfl)
    have := hB.four_le_card
    rw [hB1, Subgroup.card_bot] at this
    omega
  exact ⟨fun ⟨h₁, h₂⟩ => key hd.inf_eq hd.isDih₂ hd.sup_eq h₁ h₂,
    fun ⟨h₁, h₂⟩ => key (by rw [inf_comm]; exact hd.inf_eq) hd.dih₁
      (by rw [sup_comm]; exact hd.sup_eq) h₁ h₂⟩

variable [Finite G]

theorem DDDecomp.not_forall_involution_not_mem (hd : DDDecomp T T₁ T₂) {V : Subgroup G}
    (hVT : V ≤ T) (hVn : ∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V) (hV4 : 4 ≤ Nat.card V)
    (h : ∀ x ∈ V, orderOf x = 2 → x ∉ T₁ ∧ x ∉ T₂) : False := by
  have hT2 : IsPGroup 2 T := isPGroup_dd hd
  have hinf : ∀ {W : Subgroup G}, (∀ x ∈ V, orderOf x = 2 → x ∉ W) → V ⊓ W = ⊥ := by
    intro W hW
    by_contra hne
    obtain ⟨x, hx, hx2⟩ :=
      exists_orderOf_eq_two_of_ne_bot (hT2.to_le (inf_le_left.trans hVT)) hne
    exact hW x hx.1 hx2 hx.2
  have hinf₁ : V ⊓ T₁ = ⊥ := hinf fun x hx hx2 => (h x hx hx2).1
  have hinf₂ : V ⊓ T₂ = ⊥ := hinf fun x hx hx2 => (h x hx hx2).2
  have hcomm : ∀ v ∈ V, ∀ s ∈ T₂, v * s = s * v := by
    intro v hv s hs
    have h1 : v * s * v⁻¹ * s⁻¹ ∈ V := by
      have h' := mul_mem hv (hVn s (hd.le_right hs) v⁻¹ (inv_mem hv))
      rwa [← mul_assoc, ← mul_assoc] at h'
    have h2 : v * s * v⁻¹ * s⁻¹ ∈ T₂ := mul_mem (hd.conj_mem_right (hVT hv) hs) (inv_mem hs)
    have h3 : v * s * v⁻¹ * s⁻¹ = 1 := by
      have h4 : v * s * v⁻¹ * s⁻¹ ∈ V ⊓ T₂ := ⟨h1, h2⟩
      rwa [hinf₂, mem_bot] at h4
    calc v * s = v * s * v⁻¹ * s⁻¹ * (s * v) := by group
      _ = s * v := by rw [h3, one_mul]
  obtain ⟨f, hf, hfx⟩ := hd.exists_injective_of_inf_left_eq_bot hVT hinf₁
  have hcen : ∀ r : V, f r ∈ Subgroup.center T₂ := by
    intro r
    obtain ⟨x, hx, hrx⟩ := hfx r
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    have hfr : (f r : G) = x⁻¹ * r := by rw [hrx]; group
    have h1 : x⁻¹ * (s : G) = s * x⁻¹ := (show Commute x (s : G) from hd.comm hx s.2).inv_left.eq
    have h2 : (s : G) * r = r * s := (hcomm r r.2 s s.2).symm
    change (s : G) * (f r : G) = (f r : G) * (s : G)
    rw [hfr]
    calc (s : G) * (x⁻¹ * r) = x⁻¹ * (s * r) := by rw [← mul_assoc, ← h1, mul_assoc]
      _ = x⁻¹ * (r * s) := by rw [h2]
      _ = x⁻¹ * r * s := by rw [mul_assoc]
  let g : V → Subgroup.center T₂ := fun r => ⟨f r, hcen r⟩
  have hg : Function.Injective g := fun r r' hrr => hf (congrArg Subtype.val hrr)
  have hle := Nat.card_le_card_of_injective g hg
  rw [card_center_of_isDihNonab hd.dih₂] at hle
  omega

end Core

theorem le_of_conj_of_le_centralizer {T A B L W : Subgroup G} (hsup : A ⊔ B = T)
    (hinf : A ⊓ B = ⊥) (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hAL : A ≤ L)
    (hconjL : ∀ x ∈ L, ∀ y ∈ L, orderOf x = 2 → orderOf y = 2 → ∃ g ∈ L, g * x * g⁻¹ = y)
    (hA2 : ∀ c, ∃ u ∈ A, u * u = 1 ∧ u ≠ 1 ∧ u ≠ c)
    (hWT : W ≤ T) (hW2 : ∀ w ∈ W, w * w = 1) (hWL : W ⊓ L = ⊥)
    (hLW : ∀ g ∈ L, ∀ w ∈ W, g * w = w * g)
    (hfusB : ∀ x ∈ T, ∀ y ∈ T, orderOf x = 2 → IsConj x y → (x ∈ B ↔ y ∈ B)) : W ≤ B := by
  intro w hw
  have hwT : w ∈ A ⊔ B := hsup ▸ hWT hw
  obtain ⟨c, hc, b, hb, rfl⟩ :=
    (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hcomm)).1 hwT
  have hcb : c * c = 1 ∧ b * b = 1 := by
    have h := hW2 _ hw
    have h' : (c * c) * (b * b) = 1 * 1 := by
      calc (c * c) * (b * b) = c * (c * b) * b := by group
        _ = c * (b * c) * b := by rw [hcomm c hc b hb]
        _ = c * b * (c * b) := by group
        _ = 1 * 1 := by rw [h, one_mul]
    exact eq_and_eq_of_mul_eq_mul hinf (mul_mem hc hc) (one_mem _) (mul_mem hb hb) (one_mem _) h'
  by_contra hcontra
  have hc1 : c ≠ 1 := fun h => hcontra (by rw [h, one_mul]; exact hb)
  obtain ⟨u, hu, hu2, hu1, huc⟩ := hA2 c
  have hc2 : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hcb.1) hc1
  have hu2' : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  obtain ⟨g, hg, hgc⟩ := hconjL c (hAL hc) u (hAL hu) hc2 hu2'
  have hgw : g * (c * b) * g⁻¹ = c * b := by rw [hLW g hg _ hw, mul_inv_cancel_right]
  have hgb : g * b * g⁻¹ = u * c * b := by
    have hb' : b = c * (c * b) := by rw [← mul_assoc, hcb.1, one_mul]
    calc g * b * g⁻¹ = g * (c * (c * b)) * g⁻¹ := by rw [← hb']
      _ = (g * c * g⁻¹) * (g * (c * b) * g⁻¹) := by group
      _ = u * (c * b) := by rw [hgc, hgw]
      _ = u * c * b := by rw [mul_assoc]
  have hb1 : b ≠ 1 := by
    intro hb1
    rw [hb1, mul_one] at hw
    have h' : c ∈ W ⊓ L := ⟨hw, hAL hc⟩
    rw [hWL, mem_bot] at h'
    exact hc1 h'
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hcb.2) hb1
  have hbT : b ∈ T := hsup ▸ mem_sup_right hb
  have hucbT : u * c * b ∈ T :=
    hsup ▸ mul_mem (mul_mem (mem_sup_left hu) (mem_sup_left hc)) (mem_sup_right hb)
  have hucb : u * c * b ∈ B := (hfusB b hbT _ hucbT hb2 (isConj_iff.mpr ⟨g, hgb⟩)).1 hb
  have huc1 : u * c = 1 := by
    have h1 : u * c ∈ B := by
      have h' := mul_mem hucb (inv_mem hb)
      rwa [mul_inv_cancel_right] at h'
    have h' : u * c ∈ A ⊓ B := ⟨mul_mem hu hc, h1⟩
    rwa [hinf, mem_bot] at h'
  apply huc
  calc u = u * c * c := by rw [mul_assoc, hcb.1, mul_one]
    _ = c := by rw [huc1, one_mul]

section Alignment

variable [Finite G] {T T₁ T₂ : Subgroup G}

theorem DDDecomp.eq_of_isKleinFour (hd : DDDecomp T T₁ T₂)
    (hfus : ∀ x ∈ T, ∀ y ∈ T, orderOf x = 2 → IsConj x y →
      (x ∈ T₁ ↔ y ∈ T₁) ∧ (x ∈ T₂ ↔ y ∈ T₂))
    {La Lb Va : Subgroup G} (hcommL : ∀ x ∈ La, ∀ y ∈ Lb, x * y = y * x) (hinfL : La ⊓ Lb = ⊥)
    (hconjLa : ∀ x ∈ La, ∀ y ∈ La, orderOf x = 2 → orderOf y = 2 → ∃ g ∈ La, g * x * g⁻¹ = y)
    (hVaL : Va ≤ La) (hKb : IsKleinFour Lb) (hsup : Va ⊔ Lb = T)
    (hle : Va ≤ T₁ ∨ Va ≤ T₂) : (Va = T₁ ∧ Lb = T₂) ∨ (Va = T₂ ∧ Lb = T₁) := by
  have hLb4 : Nat.card Lb = 4 := hKb.card_four
  have hLb2 : ∀ w ∈ Lb, w * w = 1 := fun w hw =>
    congrArg Subtype.val (IsKleinFour.mul_self (⟨w, hw⟩ : Lb))
  have hinfV : Va ⊓ Lb = ⊥ := le_bot_iff.mp (hinfL ▸ inf_le_inf_right Lb hVaL)
  have hcardT : Nat.card T = Nat.card Va * 4 := by
    rw [← hsup, card_sup_of_le_normalizer
      (le_normalizer_of_comm fun x hx y hy => hcommL x (hVaL hx) y hy) hinfV, hLb4]
  have hcardT' : Nat.card T = Nat.card T₁ * Nat.card T₂ := by
    rw [← hd.sup_eq, card_sup_of_le_normalizer
      (le_normalizer_of_comm fun x hx y hy => hd.comm hx hy) hd.inf_eq]
  have h₁4 := hd.dih₁.four_le_card
  have h₂4 := hd.isDih₂.four_le_card
  have hVpos : 0 < Nat.card Va := Nat.card_pos
  have hLbT : Lb ≤ T := hsup ▸ le_sup_right
  have hWL : Lb ⊓ La = ⊥ := by rw [inf_comm]; exact hinfL
  have hLW : ∀ g ∈ La, ∀ w ∈ Lb, g * w = w * g := hcommL
  rcases hle with hle | hle
  · have hcard : Nat.card T₁ ≤ Nat.card Va := by
      by_contra! hlt
      have : Nat.card Va * 4 < Nat.card T₁ * Nat.card T₂ := by
        calc Nat.card Va * 4 < Nat.card T₁ * 4 := by omega
          _ ≤ Nat.card T₁ * Nat.card T₂ := Nat.mul_le_mul_left _ h₂4
      omega
    have hVT : Va = T₁ := eq_of_le_of_card_ge hle hcard
    have hT₂4 : Nat.card T₂ = 4 := by
      rw [hcardT, hVT] at hcardT'
      have hpos : 0 < Nat.card T₁ := Nat.card_pos
      exact (Nat.eq_of_mul_eq_mul_left hpos hcardT').symm
    refine Or.inl ⟨hVT, eq_of_le_of_card_ge (le_of_conj_of_le_centralizer hd.sup_eq hd.inf_eq
      (fun x hx y hy => hd.comm hx hy) (hVT ▸ hVaL) hconjLa hd.dih₁.exists_involution_ne hLbT
      hLb2 hWL hLW fun x hx y hy hx2 hxy => (hfus x hx y hy hx2 hxy).2) (by omega)⟩
  · have hcard : Nat.card T₂ ≤ Nat.card Va := by
      by_contra! hlt
      have : Nat.card Va * 4 < Nat.card T₁ * Nat.card T₂ := by
        calc Nat.card Va * 4 < Nat.card T₂ * 4 := by omega
          _ ≤ Nat.card T₂ * Nat.card T₁ := Nat.mul_le_mul_left _ h₁4
          _ = Nat.card T₁ * Nat.card T₂ := mul_comm _ _
      omega
    have hVT : Va = T₂ := eq_of_le_of_card_ge hle hcard
    have hT₁4 : Nat.card T₁ = 4 := by
      rw [hcardT, hVT, mul_comm (Nat.card T₂) 4] at hcardT'
      have hpos : 0 < Nat.card T₂ := Nat.card_pos
      exact (Nat.eq_of_mul_eq_mul_right hpos hcardT').symm
    refine Or.inr ⟨hVT, eq_of_le_of_card_ge (le_of_conj_of_le_centralizer
      (by rw [sup_comm]; exact hd.sup_eq) (by rw [inf_comm]; exact hd.inf_eq)
      (fun x hx y hy => (hd.comm hy hx).symm) (hVT ▸ hVaL) hconjLa hd.isDih₂.exists_involution_ne
      hLbT hLb2 hWL hLW fun x hx y hy hx2 hxy => (hfus x hx y hy hx2 hxy).1) (by omega)⟩

theorem DDDecomp.factor_cases (hd : DDDecomp T T₁ T₂) (hT : IsSylowOf 2 T ⊤)
    (hfus : ∀ x ∈ T, ∀ y ∈ T, orderOf x = 2 → IsConj x y →
      (x ∈ T₁ ↔ y ∈ T₁) ∧ (x ∈ T₂ ↔ y ∈ T₂))
    {L : Subgroup G} (hL : L.Normal) (hF : IsAStarFactor L) (hV : IsSylowOf 2 (T ⊓ L) L) :
    ((∀ x ∈ L, ∀ y ∈ L, orderOf x = 2 → orderOf y = 2 → ∃ g ∈ L, g * x * g⁻¹ = y) ∧
        (T ⊓ L ≤ T₁ ∨ T ⊓ L ≤ T₂)) ∨
      (IsKleinFour L ∧ T ⊓ L = L) := by
  have hF' : IsL2OrA7 L 5 ∨ IsKleinFour L := by
    rcases hF with h | h | h
    exacts [Or.inl (Or.inl h), Or.inl (Or.inr h), Or.inr h]
  rcases hF' with h7 | hK
  · have hconjL : ∀ x ∈ L, ∀ y ∈ L, orderOf x = 2 → orderOf y = 2 → ∃ g ∈ L, g * x * g⁻¹ = y := by
      intro x hx y hy hx2 hy2
      obtain ⟨g, hg⟩ := isConj_iff.mp (h7.isConj (x := (⟨x, hx⟩ : L)) (y := ⟨y, hy⟩)
        ((Subgroup.orderOf_mk x hx).trans hx2) ((Subgroup.orderOf_mk y hy).trans hy2))
      exact ⟨g, g.2, congrArg Subtype.val hg⟩
    have hdih : IsDih (T ⊓ L) := isDih_of_isSylowOf hV h7.hasDihedralSylowTwo
    refine Or.inl ⟨hconjL, ?_⟩
    have hconjV : ∀ x ∈ T ⊓ L, ∀ y ∈ T ⊓ L, orderOf x = 2 → orderOf y = 2 → IsConj x y := by
      intro x hx y hy hx2 hy2
      obtain ⟨g, -, hg⟩ := hconjL x hx.2 y hy.2 hx2 hy2
      exact isConj_iff.mpr ⟨g, hg⟩
    rcases fusion_trichotomy hfus inf_le_left hconjV with h | h | h
    · exact Or.inl (hdih.le_of_forall_involution h)
    · exact Or.inr (hdih.le_of_forall_involution h)
    · exact (hd.not_forall_involution_not_mem inf_le_left
        (fun t ht v hv => Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem ht (Subgroup.mem_inf.mp hv).1)
          (inv_mem ht), hL.conj_mem v (Subgroup.mem_inf.mp hv).2 t⟩)
        hdih.four_le_card h).elim
  · refine Or.inr ⟨hK, inf_eq_right.mpr ?_⟩
    obtain ⟨S, hS⟩ := exists_sylow_of_isSylowOf_top hT
    have hLp : IsPGroup 2 L := IsPGroup.of_card (n := 2) (by rw [hK.card_four]; norm_num)
    have := hL
    rw [← hS]
    exact hLp.le_sylow_of_normal S

theorem alignment_of_ddDecomp (L₁ L₂ T T₁ T₂ : Subgroup G) (hL₁ : L₁.Normal) (hL₂ : L₂.Normal)
    (hinf : L₁ ⊓ L₂ = ⊥) (hodd : Odd (L₁ ⊔ L₂).index) (hF₁ : IsAStarFactor L₁)
    (hF₂ : IsAStarFactor L₂) (hT : IsSylowOf 2 T ⊤) (hd : DDDecomp T T₁ T₂)
    (hfus : ∀ x ∈ T, ∀ y ∈ T, orderOf x = 2 → IsConj x y →
      (x ∈ T₁ ↔ y ∈ T₁) ∧ (x ∈ T₂ ↔ y ∈ T₂)) :
    (IsSylowOf 2 T₁ L₁ ∧ IsSylowOf 2 T₂ L₂) ∨ (IsSylowOf 2 T₁ L₂ ∧ IsSylowOf 2 T₂ L₁) := by
  have hcommL : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x := fun x hx y hy =>
    Subgroup.commute_of_normal_of_disjoint L₁ L₂ hL₁ hL₂ (disjoint_iff.mpr hinf) x y hx hy
  have htop : ∀ {L : Subgroup G}, L.Normal → (⊤ : Subgroup G) ≤ normalizer (L : Set G) :=
    fun hL => (normalizer_eq_top_iff.mpr hL).ge
  have hV₁ : IsSylowOf 2 (T ⊓ L₁) L₁ := hT.inf_of_le_normalizer le_top (htop hL₁)
  have hV₂ : IsSylowOf 2 (T ⊓ L₂) L₂ := hT.inf_of_le_normalizer le_top (htop hL₂)
  have hVcomm : ∀ x ∈ T ⊓ L₁, ∀ y ∈ T ⊓ L₂, x * y = y * x := fun x hx y hy =>
    hcommL x hx.2 y hy.2
  have hVinf : (T ⊓ L₁) ⊓ (T ⊓ L₂) = ⊥ :=
    le_bot_iff.mp (hinf ▸ inf_le_inf inf_le_right inf_le_right)
  have hVsup : (T ⊓ L₁) ⊔ (T ⊓ L₂) = T := by
    have hTN : T ≤ L₁ ⊔ L₂ := CFSG.pSubgroup_le_of_not_dvd_index Nat.prime_two
      (Subgroup.sup_normal L₁ L₂) (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd)) hT.isPGroup
    have hTsyl : IsSylowOf 2 T (L₁ ⊔ L₂) := hT.of_le hTN le_top
    have hL₁pos : Nat.card L₁ ≠ 0 := Nat.card_pos.ne'
    have hL₂pos : Nat.card L₂ ≠ 0 := Nat.card_pos.ne'
    apply eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left)
    rw [card_sup_of_le_normalizer (le_normalizer_of_comm hVcomm) hVinf, hV₁.card_eq,
      hV₂.card_eq, hTsyl.card_eq, card_sup_of_le_normalizer (le_top.trans (htop hL₁)) hinf,
      Nat.factorization_mul hL₁pos hL₂pos, Finsupp.add_apply, pow_add]
  have hVsup' : (T ⊓ L₂) ⊔ (T ⊓ L₁) = T := by rw [sup_comm]; exact hVsup
  rcases hd.factor_cases hT hfus hL₁ hF₁ hV₁ with ⟨hc₁, h₁⟩ | ⟨hK₁, hVL₁⟩ <;>
    rcases hd.factor_cases hT hfus hL₂ hF₂ hV₂ with ⟨hc₂, h₂⟩ | ⟨hK₂, hVL₂⟩
  · rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact ((hd.not_le_of_sup_eq hVsup).1 ⟨h₁, h₂⟩).elim
    · obtain ⟨e₁, e₂⟩ := hd.eq_of_sup_eq_of_le hVsup h₁ h₂
      exact Or.inl ⟨e₁ ▸ hV₁, e₂ ▸ hV₂⟩
    · obtain ⟨e₂, e₁⟩ := hd.eq_of_sup_eq_of_le hVsup' h₂ h₁
      exact Or.inr ⟨e₂ ▸ hV₂, e₁ ▸ hV₁⟩
    · exact ((hd.not_le_of_sup_eq hVsup).2 ⟨h₁, h₂⟩).elim
  · rw [hVL₂] at hVsup
    rcases hd.eq_of_isKleinFour hfus hcommL hinf hc₁ inf_le_right hK₂ hVsup h₁ with
      ⟨e₁, e₂⟩ | ⟨e₂, e₁⟩
    · refine Or.inl ⟨e₁ ▸ hV₁, ?_⟩
      rw [← hVL₂.trans e₂]
      exact hV₂
    · refine Or.inr ⟨?_, e₂ ▸ hV₁⟩
      rw [← hVL₂.trans e₁]
      exact hV₂
  · rw [hVL₁] at hVsup'
    rcases hd.eq_of_isKleinFour hfus (fun x hx y hy => (hcommL y hy x hx).symm)
        (by rw [inf_comm]; exact hinf) hc₂ inf_le_right hK₁ hVsup' h₂ with
      ⟨e₂, e₁⟩ | ⟨e₁, e₂⟩
    · refine Or.inr ⟨e₂ ▸ hV₂, ?_⟩
      rw [← hVL₁.trans e₁]
      exact hV₁
    · refine Or.inl ⟨?_, e₁ ▸ hV₂⟩
      rw [← hVL₁.trans e₂]
      exact hV₁
  · exfalso
    rw [hVL₁, hVL₂] at hVsup
    have hsq : ∀ t ∈ T, t * t = 1 := by
      intro t ht
      rw [← hVsup] at ht
      obtain ⟨a, ha, b, hb, rfl⟩ :=
        (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hcommL)).1 ht
      have ha2 : a * a = 1 := congrArg Subtype.val (IsKleinFour.mul_self (⟨a, ha⟩ : L₁))
      have hb2 : b * b = 1 := congrArg Subtype.val (IsKleinFour.mul_self (⟨b, hb⟩ : L₂))
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hcommL a ha b hb]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
    obtain ⟨x, hx, y, hy, hxy⟩ := IsDihNonab.exists_mul_ne_mul hd.dih₂
    exact hxy (CFSG.CGT.Foote81L6.TStruct.comm_of_mul_self hsq (hd.le_right hx) (hd.le_right hy))

end Alignment

variable [Finite G]

theorem alignment (h2 : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (L₁ L₂ T T₁ T₂ : Subgroup G)
    (hL₁ : L₁.Normal) (hL₂ : L₂.Normal) (hinf : L₁ ⊓ L₂ = ⊥) (hodd : Odd (L₁ ⊔ L₂).index)
    (hF₁ : IsAStarFactor L₁) (hF₂ : IsAStarFactor L₂)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hTd : DDDecomp T T₁ T₂ ∨ DDDecomp T T₂ T₁)
    (hfus : ∀ x ∈ T, ∀ y ∈ T, orderOf x = 2 → IsConj x y →
      (x ∈ T₁ ↔ y ∈ T₁) ∧ (x ∈ T₂ ↔ y ∈ T₂)) :
    (CFSG.ABGLocalTools.IsSylowOf 2 T₁ L₁ ∧ CFSG.ABGLocalTools.IsSylowOf 2 T₂ L₂) ∨
      (CFSG.ABGLocalTools.IsSylowOf 2 T₁ L₂ ∧ CFSG.ABGLocalTools.IsSylowOf 2 T₂ L₁) := by
  have _ := h2
  rcases hTd with hd | hd
  · exact alignment_of_ddDecomp L₁ L₂ T T₁ T₂ hL₁ hL₂ hinf hodd hF₁ hF₂ hT hd hfus
  · rcases alignment_of_ddDecomp L₁ L₂ T T₂ T₁ hL₁ hL₂ hinf hodd hF₁ hF₂ hT hd
      (fun x hx y hy hx2 hxy => (hfus x hx y hy hx2 hxy).symm) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inr ⟨h₂, h₁⟩
    · exact Or.inl ⟨h₂, h₁⟩

end CFSG.GH72
