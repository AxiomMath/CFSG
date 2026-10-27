module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.CenterAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Closing

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

theorem commute_of_card_le_two {F : Type*} [Group F] [Finite F] (h : Nat.card F ≤ 2) (x y : F) :
    x * y = y * x := by
  by_contra hxy
  have hx : x ≠ 1 := fun e => hxy (by rw [e, one_mul, mul_one])
  have hy : y ≠ 1 := fun e => hxy (by rw [e, one_mul, mul_one])
  have hxy' : x ≠ y := fun e => hxy (by rw [e])
  have := Fintype.ofFinite F
  classical
  have h3 : ({1, x, y} : Finset F).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hx.symm, hy.symm]), Finset.card_pair hxy']
  have : 3 ≤ Nat.card F := by
    calc 3 = ({1, x, y} : Finset F).card := h3.symm
      _ ≤ Fintype.card F := Finset.card_le_univ _
      _ = Nat.card F := Nat.card_eq_fintype_card.symm
  omega

variable {Y : Type} [Group Y] [Finite Y]

theorem le_of_index_two {C D F : Subgroup Y} [IsSimpleGroup F] (hFnab : ∃ x y : F, x * y ≠ y * x)
    (hFC : F ≤ C) (hDC : D ≤ C) (hidx : Nat.card C = 2 * Nat.card D) : F ≤ D := by
  have hD'card : Nat.card (D.subgroupOf C) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv
  have hindex : (D.subgroupOf C).index = 2 := by
    have h := Subgroup.index_mul_card (H := D.subgroupOf C)
    rw [hD'card, hidx] at h
    have hpos : 0 < Nat.card D := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h
  have : (D.subgroupOf C).Normal := Subgroup.normal_of_index_eq_two hindex
  have hsimple : IsSimpleGroup (F.subgroupOf C) :=
    MulEquiv.isSimpleGroup (Subgroup.subgroupOfEquivOfLe hFC)
  let ψ : F.subgroupOf C →* C ⧸ D.subgroupOf C :=
    (QuotientGroup.mk' (D.subgroupOf C)).comp (F.subgroupOf C).subtype
  have hker : ψ.ker.Normal := MonoidHom.normal_ker ψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h0 | h1
  · exfalso
    have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 h0
    have hle := Nat.card_le_card_of_injective ψ hinj
    have hq : Nat.card (C ⧸ D.subgroupOf C) = 2 := hindex
    have hF'card : Nat.card (F.subgroupOf C) = Nat.card F :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv
    have hcomm := commute_of_card_le_two (F := F) (by omega)
    obtain ⟨x, y, hxy⟩ := hFnab
    exact hxy (hcomm x y)
  · intro x hx
    have hxC : x ∈ C := hFC hx
    have hx' : (⟨x, hxC⟩ : C) ∈ F.subgroupOf C := hx
    have h2 : ((⟨⟨x, hxC⟩, hx'⟩ : F.subgroupOf C) ∈ ψ.ker) := by rw [h1]; exact mem_top _
    have h3 : (QuotientGroup.mk' (D.subgroupOf C)) ⟨x, hxC⟩ = 1 := h2
    exact (QuotientGroup.eq_one_iff (N := D.subgroupOf C) (⟨x, hxC⟩ : C)).1 h3

theorem centerInvAt_of_simple_subgroup {r s a : Y} (hr1 : r ≠ 1) (hs1 : s ≠ 1) (hrs : r ≠ s)
    (hr2 : r * r = 1) (hs2 : s * s = 1) (hcomm : r * s = s * r) (ha : a = r * s)
    {F : Subgroup Y} [IsSimpleGroup F] (hFnab : ∃ x y : F, x * y ≠ y * x)
    (hFle : F ≤ centralizer ({a} : Set Y))
    (hcardC : Nat.card (centralizer ({a} : Set Y)) = 8 * Nat.card F)
    (hcardD : Nat.card (centralizer ({a} : Set Y)) =
      2 * Nat.card (centralizer ({r} : Set Y) ⊓ centralizer ({s} : Set Y) : Subgroup Y))
    (hswap : ∃ g, g * a = a * g ∧ g * r * g⁻¹ = s) : CenterInvAt a := by
  classical
  intro z hzz hzc
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hz1, hza⟩ := hne
  have haa : a * a = 1 := by
    rw [ha]
    calc r * s * (r * s) = r * (s * r) * s := by group
      _ = r * (r * s) * s := by rw [hcomm]
      _ = (r * r) * (s * s) := by group
      _ = 1 := by rw [hr2, hs2, mul_one]
  have hra : r * a = a * r := by
    rw [ha]
    calc r * (r * s) = r * (s * r) := by rw [hcomm]
      _ = r * s * r := by group
  have hsa : s * a = a * s := by
    rw [ha]
    calc s * (r * s) = s * r * s := by group
      _ = r * s * s := by rw [← hcomm]
      _ = r * s * s := rfl
  have hza' : z * a = a * z := hzc a rfl
  have hzr' : z * r = r * z := hzc r hra
  have hzs' : z * s = s * z := hzc s hsa
  obtain ⟨g, hga, hgr⟩ := hswap
  have hzg : z * g = g * z := hzc g hga
  have hzr : z ≠ r := by
    rintro rfl
    apply hrs
    have : g * z = z * g := hzg.symm
    calc z = g * z * g⁻¹ := by rw [this]; group
      _ = s := hgr
  have hzs : z ≠ s := by
    rintro rfl
    apply hrs
    have h1 : g * r = z * g := by
      calc g * r = (g * r * g⁻¹) * g := by group
        _ = z * g := by rw [hgr]
    rw [hzg] at h1
    exact mul_left_cancel h1
  have ha1 : a ≠ 1 := by
    intro h
    apply hrs
    have : r * s = 1 := ha ▸ h
    calc r = r * (s * s) := by rw [hs2, mul_one]
      _ = (r * s) * s := by rw [mul_assoc]
      _ = s := by rw [this, one_mul]
  have har : a ≠ r := by
    intro h
    have : r * s = r := ha ▸ h
    exact hs1 (mul_eq_left.1 this)
  have has : a ≠ s := by
    intro h
    have : r * s = s := ha ▸ h
    exact hr1 (mul_eq_right.1 this)
  have hrs' : r * s = a := ha.symm
  have hsr' : s * r = a := by rw [← hcomm]; exact ha.symm
  have hra' : r * a = s := by
    rw [ha]
    calc r * (r * s) = (r * r) * s := by group
      _ = s := by rw [hr2, one_mul]
  have har' : a * r = s := by
    rw [ha]
    calc r * s * r = r * (s * r) := by group
      _ = r * (r * s) := by rw [hcomm]
      _ = s := by rw [← mul_assoc, hr2, one_mul]
  have hsa' : s * a = r := by
    rw [ha]
    calc s * (r * s) = (s * r) * s := by group
      _ = (r * s) * s := by rw [hcomm]
      _ = r := by rw [mul_assoc, hs2, mul_one]
  have has' : a * s = r := by
    rw [ha]
    calc r * s * s = r * (s * s) := by group
      _ = r := by rw [hs2, mul_one]
  set C := centralizer ({a} : Set Y) with hC
  set D : Subgroup Y := centralizer ({r} : Set Y) ⊓ centralizer ({s} : Set Y) with hD
  have hDC : D ≤ C := by
    intro d hd
    have h1 := mem_centralizer_singleton_iff.1 hd.1
    have h2 := mem_centralizer_singleton_iff.1 hd.2
    refine mem_centralizer_singleton_iff.2 ?_
    rw [ha]
    calc d * (r * s) = (d * r) * s := by group
      _ = r * d * s := by rw [h1]
      _ = r * (d * s) := by group
      _ = r * (s * d) := by rw [h2]
      _ = (r * s) * d := by group
  have hFD : F ≤ D := le_of_index_two hFnab hFle hDC hcardD
  have hFr : ∀ f ∈ F, f * r = r * f := fun f hf => mem_centralizer_singleton_iff.1 (hFD hf).1
  have hFs : ∀ f ∈ F, f * s = s * f := fun f hf => mem_centralizer_singleton_iff.1 (hFD hf).2
  have hz1' : 1 ≠ z := fun h => hz1 h.symm
  have hVr : (1 : Y) ≠ r := fun h => hr1 h.symm
  have hVs : (1 : Y) ≠ s := fun h => hs1 h.symm
  have hVa : (1 : Y) ≠ a := fun h => ha1 h.symm
  set V : Finset Y := {1, r, s, a} with hV
  have hVcard : V.card = 4 := by
    rw [hV, Finset.card_insert_of_notMem (by simp [hVr, hVs, hVa]),
      Finset.card_insert_of_notMem (by simp [hrs, har.symm]), Finset.card_pair has.symm]
  have hVmul : ∀ x ∈ V, ∀ y ∈ V, x * y ∈ V := by
    intro x hx y hy
    simp only [hV, Finset.mem_insert, Finset.mem_singleton] at hx hy ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp [hrs', hsr', hra', har', hsa', has', hr2, hs2, haa]
  have hVinv : ∀ x ∈ V, x⁻¹ = x := by
    intro x hx
    simp only [hV, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact inv_one
    · exact inv_eq_of_mul_eq_one_right hr2
    · exact inv_eq_of_mul_eq_one_right hs2
    · exact inv_eq_of_mul_eq_one_right haa
  have hzV : z ∉ V := by
    simp only [hV, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hz1, hzr, hzs, hza⟩
  have hVsq : ∀ x ∈ V, x * x = 1 := by
    intro x hx
    calc x * x = x * x⁻¹ := by rw [hVinv x hx]
      _ = 1 := mul_inv_cancel x
  have hzxV : ∀ x ∈ V, z * x ∉ V := by
    intro x hx hmem
    apply hzV
    have h1 : z * x * x ∈ V := hVmul _ hmem x hx
    have h2 : z * x * x = z := by
      calc z * x * x = z * (x * x) := by group
        _ = z := by rw [hVsq x hx, mul_one]
    rwa [h2] at h1
  set T : Finset Y := V ∪ V.image (fun x => z * x) with hT
  have hTcard : T.card = 8 := by
    rw [hT, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (mul_right_injective z),
      hVcard]
    rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy'
    exact hzxV x hx hy
  have hVr : ∀ x ∈ V, x * r = r * x := by
    intro x hx
    simp only [hV, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · rfl
    · exact hcomm.symm
    · rw [har', hra']
  have hVC : ∀ x ∈ V, x * a = a * x := by
    intro x hx
    simp only [hV, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · exact hra
    · exact hsa
    · rfl
  have hVF : ∀ x ∈ V, ∀ f ∈ F, f * x = x * f := by
    intro x hx f hf
    simp only [hV, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · exact hFr f hf
    · exact hFs f hf
    · exact mem_centralizer_singleton_iff.1 (hFle hf)
  have hTr : ∀ w ∈ T, w * r = r * w := by
    intro w hw
    rcases Finset.mem_union.1 hw with h | h
    · exact hVr w h
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
      calc z * x * r = z * (x * r) := by group
        _ = z * (r * x) := by rw [hVr x hx]
        _ = (z * r) * x := by group
        _ = (r * z) * x := by rw [hzr']
        _ = r * (z * x) := by group
  have hTC : ∀ w ∈ T, w * a = a * w := by
    intro w hw
    rcases Finset.mem_union.1 hw with h | h
    · exact hVC w h
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
      calc z * x * a = z * (x * a) := by group
        _ = z * (a * x) := by rw [hVC x hx]
        _ = (z * a) * x := by group
        _ = (a * z) * x := by rw [hza']
        _ = a * (z * x) := by group
  have hTF : ∀ w ∈ T, ∀ f ∈ F, f * w = w * f := by
    intro w hw f hf
    have hfz : f * z = z * f := (hzc f (mem_centralizer_singleton_iff.1 (hFle hf))).symm
    rcases Finset.mem_union.1 hw with h | h
    · exact hVF w h f hf
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
      calc f * (z * x) = (f * z) * x := by group
        _ = (z * f) * x := by rw [hfz]
        _ = z * (f * x) := by group
        _ = z * (x * f) := by rw [hVF x hx f hf]
        _ = (z * x) * f := by group
  have hTCmem : ∀ w ∈ T, w ∈ C := fun w hw => mem_centralizer_singleton_iff.2 (hTC w hw)
  let ι : F × T → C := fun p =>
    ⟨(p.1 : Y) * (p.2 : Y), C.mul_mem (hFle p.1.2) (hTCmem p.2 p.2.2)⟩
  have hcenterF : center F = ⊥ := center_eq_bot_of_simple_nonabelian hFnab
  have hinj : Function.Injective ι := by
    rintro ⟨f₁, w₁⟩ ⟨f₂, w₂⟩ h
    have h' : (f₁ : Y) * w₁ = f₂ * w₂ := congrArg Subtype.val h
    have hc : (f₂ : Y)⁻¹ * f₁ = (w₂ : Y) * (w₁ : Y)⁻¹ := by
      calc (f₂ : Y)⁻¹ * f₁ = (f₂ : Y)⁻¹ * (f₁ * w₁) * (w₁ : Y)⁻¹ := by group
        _ = (f₂ : Y)⁻¹ * (f₂ * w₂) * (w₁ : Y)⁻¹ := by rw [h']
        _ = (w₂ : Y) * (w₁ : Y)⁻¹ := by group
    have hmem : f₂⁻¹ * f₁ ∈ center F := by
      rw [mem_center_iff]
      intro f
      apply Subtype.ext
      show (f : Y) * ((f₂ : Y)⁻¹ * f₁) = ((f₂ : Y)⁻¹ * f₁) * f
      rw [hc]
      have e1 := hTF w₂ w₂.2 f f.2
      have e2 := hTF w₁ w₁.2 f f.2
      calc (f : Y) * ((w₂ : Y) * (w₁ : Y)⁻¹) = ((f : Y) * w₂) * (w₁ : Y)⁻¹ := by group
        _ = ((w₂ : Y) * f) * (w₁ : Y)⁻¹ := by rw [e1]
        _ = (w₂ : Y) * (f * (w₁ : Y)⁻¹) := by group
        _ = (w₂ : Y) * ((w₁ : Y)⁻¹ * f) := by
            congr 1
            calc (f : Y) * (w₁ : Y)⁻¹ = (w₁ : Y)⁻¹ * ((w₁ : Y) * f) * (w₁ : Y)⁻¹ := by group
              _ = (w₁ : Y)⁻¹ * (f * (w₁ : Y)) * (w₁ : Y)⁻¹ := by rw [e2]
              _ = (w₁ : Y)⁻¹ * f := by group
        _ = ((w₂ : Y) * (w₁ : Y)⁻¹) * f := by group
    rw [hcenterF, mem_bot] at hmem
    have hf : f₁ = f₂ := by
      have := congrArg (f₂ * ·) hmem
      simpa using this
    subst hf
    have hw : (w₁ : Y) = w₂ := mul_left_cancel h'
    exact Prod.ext rfl (Subtype.ext hw)
  have hcardle : Nat.card C ≤ Nat.card (F × T) := by
    rw [Nat.card_prod, hcardC]
    have : Nat.card T = 8 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact hTcard
    rw [this]
    ring_nf
    exact le_refl _
  have hbij : Function.Bijective ι := hinj.bijective_of_nat_card_le hcardle
  obtain ⟨⟨f, w⟩, hfw⟩ := hbij.2 ⟨g, mem_centralizer_singleton_iff.2 hga⟩
  have hg : g = (f : Y) * w := by
    have := congrArg Subtype.val hfw
    exact this.symm
  apply hrs
  have hwr : (w : Y) * r = r * w := hTr w w.2
  calc r = (f : Y) * r * (f : Y)⁻¹ := by rw [hFr f f.2]; group
    _ = (f : Y) * ((w : Y) * r * (w : Y)⁻¹) * (f : Y)⁻¹ := by rw [hwr]; group
    _ = ((f : Y) * w) * r * ((f : Y) * w)⁻¹ := by group
    _ = g * r * g⁻¹ := by rw [hg]
    _ = s := hgr


theorem card_inf_centralizer_mul_ncard_conj {B : Type} [Group B] (H : Subgroup B) (s : B) :
    Nat.card (H ⊓ centralizer ({s} : Set B) : Subgroup B) *
      ({y | ∃ h ∈ H, h * s * h⁻¹ = y} : Set B).ncard = Nat.card H := by
  let _ : MulAction H B := MulAction.compHom B
    ((ConjAct.toConjAct : B ≃* ConjAct B).toMonoidHom.comp H.subtype)
  have hsmul : ∀ (h : H) (x : B), h • x = (h : B) * x * (h : B)⁻¹ := fun h x => by
    show ConjAct.toConjAct (h : B) • x = _
    rw [ConjAct.smul_def]; simp
  have horb : MulAction.orbit H s = {y | ∃ h ∈ H, h * s * h⁻¹ = y} := by
    ext y
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, (hsmul h s).symm⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, hsmul ⟨h, hh⟩ s⟩
  have hstab : Nat.card (MulAction.stabilizer H s) =
      Nat.card (H ⊓ centralizer ({s} : Set B) : Subgroup B) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun h => ⟨(h.1 : B), h.1.2, ?_⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩
        left_inv := fun h => rfl
        right_inv := fun x => rfl }
    · have := h.2
      rw [MulAction.mem_stabilizer_iff, hsmul] at this
      refine mem_centralizer_singleton_iff.2 ?_
      calc (h.1 : B) * s = (h.1 : B) * s * (h.1 : B)⁻¹ * h.1 := by group
        _ = s * h.1 := by rw [this]
    · rw [MulAction.mem_stabilizer_iff, hsmul]
      have := mem_centralizer_singleton_iff.1 x.2.2
      show (x.1 : B) * s * (x.1 : B)⁻¹ = s
      rw [this]; group
  have h1 := MulAction.index_stabilizer H s
  have h2 := Subgroup.index_mul_card (H := MulAction.stabilizer H s)
  rw [h1, horb, hstab] at h2
  rw [mul_comm]
  exact h2

end CFSG.EvenSporadicStandard.Solomon78
