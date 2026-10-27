module

public import CFSG.GH74.Generic.S3.LyTrans
public import CFSG.GH74.Generic.S3.LyRank3

public section

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.ABGLocalTools Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace CFSG.GH74.Generic.S3

section General

variable {G : Type} [Group G]

theorem exists_normalizer_conj [Finite G] {x u : G} {P : Subgroup G}
    (hP : IsSylowOf 2 P (centralizer ({x} : Set G))) (hPu : P ≤ centralizer ({u} : Set G))
    (hxu : IsConj x u) :
    ∃ m : G, (∀ z : G, z ∈ P ↔ m * z * m⁻¹ ∈ P) ∧ m * x * m⁻¹ = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp hxu
  have hC : (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({u} : Set G) := by
    rw [← hg]
    exact CFSG.GH74.Generic.S1.map_centralizer_conj x g
  set P' : Subgroup G := P.map (MulAut.conj g).toMonoidHom with hP'def
  have hP'le : P' ≤ centralizer ({u} : Set G) := hC ▸ Subgroup.map_mono hP.le
  have hCcard : Nat.card ↥(centralizer ({u} : Set G)) = Nat.card ↥(centralizer ({x} : Set G)) := by
    rw [← hC, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hP'syl : IsSylowOf 2 P' (centralizer ({u} : Set G)) := by
    refine isSylowOf_of_card hP'le ?_
    rw [hP'def, Subgroup.card_map_of_injective (MulAut.conj g).injective, hP.card_eq, hCcard]
  have hPsyl : IsSylowOf 2 P (centralizer ({u} : Set G)) := by
    refine isSylowOf_of_card hPu ?_
    rw [hP.card_eq, hCcard]
  obtain ⟨k, hk, hkP⟩ := hPsyl.exists_mem_conj hP'syl
  refine ⟨k⁻¹ * g, fun z => ?_, ?_⟩
  · have h1 : z ∈ P ↔ g * z * g⁻¹ ∈ P' := by
      constructor
      · intro hz
        exact ⟨z, hz, by simp⟩
      · rintro ⟨w, hw, hwz⟩
        have : w = z := by
          have h2 : g * w * g⁻¹ = g * z * g⁻¹ := hwz
          calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
            _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [h2]
            _ = z := by group
        rw [← this]; exact hw
    rw [h1, hkP]
    have : k⁻¹ * (g * z * g⁻¹) * k = k⁻¹ * g * z * (k⁻¹ * g)⁻¹ := by group
    rw [this]
  · have hku : k * u = u * k := mem_centralizer_singleton_iff.1 hk
    calc k⁻¹ * g * x * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * x * g⁻¹) * k := by group
      _ = k⁻¹ * u * k := by rw [hg]
      _ = u := by rw [mul_assoc, ← hku, ← mul_assoc, inv_mul_cancel, one_mul]


theorem isComponent_subgroupOf_conj {C A : Subgroup G} (hA : A ≤ C)
    (hcomp : CFSG.IsComponent (A.subgroupOf C)) (n : G) (hn : conjSub n C = C) :
    CFSG.IsComponent ((conjSub n A).subgroupOf C) := by
  let φ : ↥C ≃* ↥C :=
    (MulEquiv.subgroupMap (MulAut.conj n) C).trans (MulEquiv.subgroupCongr hn)
  have hφ : ∀ c : ↥C, ((φ c : ↥C) : G) = n * (c : G) * n⁻¹ := fun c => rfl
  have : (conjSub n A).subgroupOf C = (A.subgroupOf C).map φ.toMonoidHom := by
    ext ⟨c, hc⟩
    constructor
    · intro h
      have h' : c ∈ conjSub n A := h
      obtain ⟨a, ha, rfl⟩ := h'
      have hnc : n⁻¹ * (n * a * n⁻¹) * n ∈ C := by
        have h2 : n⁻¹ * (n * a * n⁻¹) * n = a := by group
        rw [h2]; exact hA ha
      refine ⟨⟨a, hA ha⟩, ha, ?_⟩
      apply Subtype.ext
      rfl
    · rintro ⟨⟨a, haC⟩, ha, hac⟩
      have h1 : n * a * n⁻¹ = c := congrArg Subtype.val hac
      show c ∈ conjSub n A
      rw [← h1]
      exact ⟨a, ha, rfl⟩
  rw [this]
  exact CFSG.LocalCores.isComponent_map_mulEquiv φ hcomp

theorem eq_or_commute_of_components [Finite G] {C A B : Subgroup G} (hA : A ≤ C) (hB : B ≤ C)
    (hAc : CFSG.IsComponent (A.subgroupOf C)) (hBc : CFSG.IsComponent (B.subgroupOf C)) :
    A = B ∨ ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  rcases CFSG.LocalCores.distinct_components_commute hAc hBc with h | h
  · left
    have := (Subgroup.subgroupOf_inj).1 h
    rwa [inf_eq_left.2 hA, inf_eq_left.2 hB] at this
  · right
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    intro a ha b hb
    have h2 := mem_centralizer_iff.1
      (h1 (show (⟨a, hA ha⟩ : ↥C) ∈ A.subgroupOf C from ha)) ⟨b, hB hb⟩ hb
    exact (congrArg Subtype.val h2).symm

end General


section Nbr

open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem NbrData.isComponent_Iv (hnd : NbrData G t p f x y Iw Iv) :
    CFSG.IsComponent (Iv.subgroupOf (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G))) := by
  have hB := hnd.isPCompIn_Iv
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hB.1).symm
    hnd.Iv_quasisimple, ?_⟩
  exact CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain
    (CFSG.GH74.GLS.TwoThin.isPCompIn_two_iff.mp hB).2.1 Subgroup.IsSubnormal.top

theorem NbrData.x_notin_Iv (hnd : NbrData G t p f x y Iw Iv) : x ∉ Iv := by
  intro hx
  exact not_central_involution_of_odd hnd.odd_w (hnd.Iv_le hx) hnd.x_sq hnd.x_ne_one
    (fun i hi => mem_centralizer_singleton_iff.1 (hnd.Iw_le hi))

theorem NbrData.yx_notin_Iv (hnd : NbrData G t p f x y Iw Iv) : y * x ∉ Iv := by
  intro hyx
  apply hnd.x_notin_Iv
  have := Iv.mul_mem (Iv.inv_mem hnd.y_Iv) hyx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hnd.y_sq
  rw [hy', ← mul_assoc, hnd.y_sq, one_mul] at this
  exact this


theorem NbrData.not_isConj_y_x {K : Subgroup (CentralizerBar x)} (hgen : Gen4 G)
    (hnd : NbrData G t p f x y Iw Iv) (honly : OnlyInvX x K) (himg : imgBar x Iw = K)
    (hxy : IsConj x (y * x)) : ¬ IsConj y x := by
  intro hyx
  obtain ⟨P, hP, hyP, hyc⟩ := hnd.exists_sylow_central
  have hcases := hnd.involution_center_cases honly himg hP hyP hyc
  have hxP : x ∈ P := hnd.x_mem_sylow hP
  have hx2 := hnd.x_sq
  have hy2 := hnd.y_sq
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hxyc : x * y = y * x := hnd.comm.symm
  have hxcP : ∀ a ∈ P, a * x = x * a := fun a ha => mem_centralizer_singleton_iff.1 (hP.le ha)
  have hyxP : y * x ∈ P := P.mul_mem hyP hxP
  have hyxc : ∀ a ∈ P, a * (y * x) = (y * x) * a := by
    intro a ha
    rw [← mul_assoc, hyc a ha, mul_assoc, hxcP a ha, ← mul_assoc]
  have hyx2 : (y * x) * (y * x) = 1 := by
    calc (y * x) * (y * x) = y * (x * y) * x := by group
      _ = y * (y * x) * x := by rw [hxyc]
      _ = (y * y) * (x * x) := by group
      _ = 1 := by rw [hy2, hx2, one_mul]
  have hyx1 : y * x ≠ 1 := by
    intro h
    apply hnd.ne
    have : y = x⁻¹ := mul_eq_one_iff_eq_inv.1 h
    rw [this, hx']
  set C : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) with hC
  have hE1 : ∀ g : G, (g * x = x * g ∧ g * y = y * g) ↔ (g * x = x * g ∧ g * (y * x) = (y * x) * g) := by
    intro g
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      exact (Commute.mul_right (show Commute g y from h2) (show Commute g x from h1)).eq
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have : y = (y * x) * x⁻¹ := by group
      rw [this]
      exact (Commute.mul_right (show Commute g (y * x) from h2)
        (Commute.inv_right (show Commute g x from h1))).eq
  have hE2 : ∀ g : G, (g * y = y * g ∧ g * (y * x) = (y * x) * g) ↔ (g * x = x * g ∧ g * y = y * g) := by
    intro g
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1⟩
      have : x = y⁻¹ * (y * x) := by group
      rw [this]
      exact (Commute.mul_right (Commute.inv_right (show Commute g y from h1))
        (show Commute g (y * x) from h2)).eq
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      exact (Commute.mul_right (show Commute g y from h2) (show Commute g x from h1)).eq
  have hP3 : centralizer ({x} : Set G) ⊓ centralizer ({y * x} : Set G) = C := by
    ext g
    simp only [Subgroup.mem_inf, mem_centralizer_singleton_iff, hC]
    exact (hE1 g).symm
  have hP5 : centralizer ({y} : Set G) ⊓ centralizer ({y * x} : Set G) = C := by
    ext g
    simp only [Subgroup.mem_inf, mem_centralizer_singleton_iff, hC]
    exact hE2 g
  have hinter : ∀ a b : G, (a = x ∨ a = y ∨ a = y * x) → (b = x ∨ b = y ∨ b = y * x) → a ≠ b →
      centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) = C := by
    intro a b ha hb hab
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> subst ha <;> subst hb
    · exact absurd rfl hab
    · rfl
    · exact hP3
    · rw [inf_comm]
    · exact absurd rfl hab
    · exact hP5
    · rw [inf_comm]; exact hP3
    · rw [inf_comm]; exact hP5
    · exact absurd rfl hab
  have hperm : ∀ n : G, (∀ z, z ∈ P ↔ n * z * n⁻¹ ∈ P) → ∀ z ∈ P, (∀ a ∈ P, a * z = z * a) →
      z * z = 1 → z ≠ 1 → (n * z * n⁻¹ = x ∨ n * z * n⁻¹ = y ∨ n * z * n⁻¹ = y * x) := by
    intro n hn z hzP hzc hzz hz1
    have h1 : n * z * n⁻¹ ∈ P := (hn z).mp hzP
    have hc : ∀ a ∈ P, a * (n * z * n⁻¹) = (n * z * n⁻¹) * a := by
      intro a ha
      have ha' : n⁻¹ * a * n ∈ P := by
        refine (hn (n⁻¹ * a * n)).mpr ?_
        have : n * (n⁻¹ * a * n) * n⁻¹ = a := by group
        rw [this]
        exact ha
      calc a * (n * z * n⁻¹) = n * ((n⁻¹ * a * n) * z) * n⁻¹ := by group
        _ = n * (z * (n⁻¹ * a * n)) * n⁻¹ := by rw [hzc _ ha']
        _ = (n * z * n⁻¹) * a := by group
    have h2 : (n * z * n⁻¹) * (n * z * n⁻¹) = 1 := by
      calc (n * z * n⁻¹) * (n * z * n⁻¹) = n * (z * z) * n⁻¹ := by group
        _ = 1 := by rw [hzz]; group
    rcases hcases _ h1 hc h2 with h | h | h | h
    · exfalso
      apply hz1
      have : z = n⁻¹ * (n * z * n⁻¹) * n := by group
      rw [this, h]
      group
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hCinv : ∀ n : G, (∀ z, z ∈ P ↔ n * z * n⁻¹ ∈ P) → conjSub n C = C := by
    intro n hn
    have ha := hperm n hn x hxP hxcP hx2 hnd.x_ne_one
    have hb := hperm n hn y hyP hyc hy2 hnd.y_ne_one
    have hne : n * x * n⁻¹ ≠ n * y * n⁻¹ := by
      intro h
      exact hnd.ne (mul_left_cancel (mul_right_cancel h.symm))
    have h1 : conjSub n C = conjSub n (centralizer ({x} : Set G)) ⊓ conjSub n (centralizer ({y} : Set G)) :=
      Subgroup.map_inf _ _ _ (MulAut.conj n).injective
    rw [h1]
    have h2 : conjSub n (centralizer ({x} : Set G)) = centralizer ({n * x * n⁻¹} : Set G) :=
      CFSG.GH74.Generic.S1.map_centralizer_conj x n
    have h3 : conjSub n (centralizer ({y} : Set G)) = centralizer ({n * y * n⁻¹} : Set G) :=
      CFSG.GH74.Generic.S1.map_centralizer_conj y n
    rw [h2, h3]
    exact hinter _ _ ha hb hne
  obtain ⟨m, hm, hmx⟩ := exists_normalizer_conj hP (u := y)
    (fun a ha => mem_centralizer_singleton_iff.2 (hyc a ha)) hyx.symm
  obtain ⟨m', hm', hm'x⟩ := exists_normalizer_conj hP (u := y * x)
    (fun a ha => mem_centralizer_singleton_iff.2 (hyxc a ha)) hxy
  have hm_inv : ∀ z, z ∈ P ↔ m⁻¹ * z * m⁻¹⁻¹ ∈ P := by
    intro z
    rw [hm (m⁻¹ * z * m⁻¹⁻¹)]
    have : m * (m⁻¹ * z * m⁻¹⁻¹) * m⁻¹ = z := by group
    rw [this]
  have hn_mul : ∀ z, z ∈ P ↔ (m' * m⁻¹) * z * (m' * m⁻¹)⁻¹ ∈ P := by
    intro z
    rw [hm_inv z, hm' (m⁻¹ * z * m⁻¹⁻¹)]
    have : m' * (m⁻¹ * z * m⁻¹⁻¹) * m'⁻¹ = (m' * m⁻¹) * z * (m' * m⁻¹)⁻¹ := by group
    rw [this]
  have hmy : m * y * m⁻¹ = x ∨ m * y * m⁻¹ = y * x := by
    rcases hperm m hm y hyP hyc hy2 hnd.y_ne_one with h | h | h
    · exact Or.inl h
    · exfalso
      apply hnd.ne
      have h' : m * y * m⁻¹ = m * x * m⁻¹ := by rw [h, hmx]
      exact mul_left_cancel (mul_right_cancel h')
    · exact Or.inr h
  set A₂ : Subgroup G := conjSub m⁻¹ Iv with hA₂
  set A₃ : Subgroup G := conjSub (m' * m⁻¹) Iv with hA₃
  have hIvC : Iv ≤ C := hnd.isPCompIn_Iv.1
  have hA1c := hnd.isComponent_Iv
  have hC2 : conjSub m⁻¹ C = C := hCinv _ hm_inv
  have hC3 : conjSub (m' * m⁻¹) C = C := hCinv _ hn_mul
  have hA2C : A₂ ≤ C := (Subgroup.map_mono hIvC).trans hC2.le
  have hA3C : A₃ ≤ C := (Subgroup.map_mono hIvC).trans hC3.le
  have hA2c := isComponent_subgroupOf_conj hIvC hA1c m⁻¹ hC2
  have hA3c := isComponent_subgroupOf_conj hIvC hA1c (m' * m⁻¹) hC3
  have hq2 : CFSG.IsQuasisimple ↥A₂ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hA2C) hA2c.1
  have hq3 : CFSG.IsQuasisimple ↥A₃ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hA3C) hA3c.1
  have hxA2 : x ∈ A₂ := by
    refine ⟨y, hnd.y_Iv, ?_⟩
    show m⁻¹ * y * m⁻¹⁻¹ = x
    calc m⁻¹ * y * m⁻¹⁻¹ = m⁻¹ * (m * x * m⁻¹) * m := by rw [hmx]; group
      _ = x := by group
  have hyxA3 : y * x ∈ A₃ := by
    refine ⟨y, hnd.y_Iv, ?_⟩
    show (m' * m⁻¹) * y * (m' * m⁻¹)⁻¹ = y * x
    calc (m' * m⁻¹) * y * (m' * m⁻¹)⁻¹ = m' * (m⁻¹ * y * m) * m'⁻¹ := by group
      _ = m' * x * m'⁻¹ := by
          congr 2
          calc m⁻¹ * y * m = m⁻¹ * (m * x * m⁻¹) * m := by rw [hmx]
            _ = x := by group
      _ = y * x := hm'x
  have h21 : A₂ ≠ Iv := fun h => hnd.x_notin_Iv (h ▸ hxA2)
  have h31 : A₃ ≠ Iv := fun h => hnd.yx_notin_Iv (h ▸ hyxA3)
  have h32 : A₃ ≠ A₂ := by
    intro h
    have hyxA2 : y * x ∈ A₂ := h ▸ hyxA3
    have hyA2 : y ∈ A₂ := by
      have := A₂.mul_mem hyxA2 (A₂.inv_mem hxA2)
      rw [hx', mul_assoc, hx2, mul_one] at this
      exact this
    obtain ⟨i, hi, hiy⟩ := hyA2
    have hiy' : m⁻¹ * i * m⁻¹⁻¹ = y := hiy
    have hi' : i = m * y * m⁻¹ := by
      calc i = m * (m⁻¹ * i * m⁻¹⁻¹) * m⁻¹ := by group
        _ = m * y * m⁻¹ := by rw [hiy']
    rcases hmy with h' | h'
    · exact hnd.x_notin_Iv (h' ▸ hi' ▸ hi)
    · exact hnd.yx_notin_Iv (h' ▸ hi' ▸ hi)
  have h12 := eq_or_commute_of_components hIvC hA2C hA1c hA2c
  have h13 := eq_or_commute_of_components hIvC hA3C hA1c hA3c
  have h23 := eq_or_commute_of_components hA2C hA3C hA2c hA3c
  exact not_gen4_of_three_commuting_quasisimple (A := Iv) (B := A₂) (J := A₃)
    hnd.Iv_quasisimple hq2 hq3 (h12.resolve_left h21.symm) (h13.resolve_left h31.symm)
    (h23.resolve_left h32.symm) hgen

end Nbr

end CFSG.GH74.Generic.S3
