module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoRoot

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdBal

section Perm

variable {n : ℕ}

theorem exists_ofSubtype_eq_of_fix {F : Finset (Fin n)} {f : Perm (Fin n)}
    (hf : ∀ i, i ∉ F → f i = i) : ∃ σ : Perm ↥F, Perm.ofSubtype σ = f := by
  have h₁ : ∀ x, (f x ∈ F) ↔ x ∈ F := by
    intro x
    constructor
    · intro hfx
      by_contra hx
      exact hx (by rw [← hf x hx]; exact hfx)
    · intro hx
      by_contra hfx
      have : f (f x) = f x := hf _ hfx
      exact hfx (by rw [f.injective this]; exact hx)
  have h₂ : ∀ x, f x ≠ x → x ∈ F := by
    intro x hx
    by_contra hxF
    exact hx (hf x hxF)
  exact ⟨f.subtypePerm h₁, Perm.ofSubtype_subtypePerm h₁ h₂⟩

theorem ofSubtype_comm_of_fixFin {τ : Perm (Fin n)} (π : Perm ↥(fixFin τ)) :
    Perm.ofSubtype π * τ = τ * Perm.ofSubtype π := by
  apply Perm.Disjoint.commute
  intro i
  by_cases hi : i ∈ fixFin τ
  · exact Or.inr (mem_fixFin.1 hi)
  · exact Or.inl (Perm.ofSubtype_apply_of_not_mem π hi)

theorem card_fixFin_mul_of_disjoint {σ₁ σ₂ : Perm (Fin n)} (hd : σ₁.Disjoint σ₂) :
    (fixFin (σ₁ * σ₂)).card + σ₁.support.card + σ₂.support.card = n := by
  have h := card_fixFin_add_card_support (σ₁ * σ₂)
  rw [hd.card_support_mul] at h
  omega

end Perm

section Theta

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z u : G}

theorem permOf_congr' {x y : G} (hxy : x = y) (hx : x ∈ centralizer ({z} : Set G))
    (hy : y ∈ centralizer ({z} : Set G)) (h : Setting G L n) (d : Cyc L Q z)
    (e : L ≃* alternatingGroup (Fin n)) : permOf h d e hx = permOf h d e hy := by
  subst hxy; rfl

omit [Finite G] in
theorem mk_eq_of_eq_or_mul {x : G} (hx2 : x * x = 1) {c : ↥(centralizer ({x} : Set G))} {b : G}
    (hb : b ∈ centralizer ({x} : Set G)) (hbc : b = (c : G) ∨ b = (c : G) * x) :
    (QuotientGroup.mk ⟨b, hb⟩ : TwoSec x) = QuotientGroup.mk c := by
  rcases hbc with h1 | h1
  · congr 1
    exact Subtype.ext h1
  · rw [QuotientGroup.eq]
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    have : (⟨b, hb⟩ : ↥(centralizer ({x} : Set G)))⁻¹ * c = selfC x := by
      apply Subtype.ext
      change b⁻¹ * (c : G) = x
      rw [h1, mul_inv_rev, hxinv]
      group
    rw [this]
    exact mem_zpowers _

theorem swapIota_ofSubtype_mem (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {x : G} (hx : x ∈ centralizer ({z} : Set G))
    (π : Perm ↥(fixFin (permOf h d e hx))) :
    ((swapIota h d T e (Perm.ofSubtype π) : ↥(L ⊔ zpowers u)) : G) ∈
      centralizer ({x} : Set G) := by
  rw [mem_centralizer_singleton_iff]
  refine comm_of_permOf_comm h d T.card e (swapIota_mem_centralizer h d T e _) hx ?_
  rw [permOf_swapIota]
  exact ofSubtype_comm_of_fixFin π

@[expose] noncomputable def twoKappa (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {x : G} (hx : x ∈ centralizer ({z} : Set G)) :
    Perm ↥(fixFin (permOf h d e hx)) →* ↥(centralizer ({x} : Set G)) :=
  (((L ⊔ zpowers u).subtype.comp
      ((swapIota h d T e).toMonoidHom.comp (Perm.ofSubtype :
        Perm ↥(fixFin (permOf h d e hx)) →* Perm (Fin n)))).codRestrict _
    (swapIota_ofSubtype_mem h d T e hx))

theorem twoKappa_apply (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {x : G} (hx : x ∈ centralizer ({z} : Set G))
    (π : Perm ↥(fixFin (permOf h d e hx))) :
    (twoKappa h d T e hx π : G) = (swapIota h d T e (Perm.ofSubtype π) : G) := rfl

@[expose] noncomputable def twoTheta (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {x : G} (hx : x ∈ centralizer ({z} : Set G)) :
    Perm ↥(fixFin (permOf h d e hx)) →* TwoSec x :=
  (QuotientGroup.mk' (zpowers (selfC x))).comp (twoKappa h d T e hx)

theorem twoTheta_apply (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {x : G} (hx : x ∈ centralizer ({z} : Set G))
    (π : Perm ↥(fixFin (permOf h d e hx))) :
    twoTheta h d T e hx π = (QuotientGroup.mk (twoKappa h d T e hx π) : TwoSec x) := rfl

theorem ofSubtype_ne_of_isSwap {τ : Perm (Fin n)} (hτ : τ.IsSwap) (π : Perm ↥(fixFin τ)) :
    Perm.ofSubtype π ≠ τ := by
  obtain ⟨p, q, hpq, hτe⟩ := hτ
  intro hπ
  have hpF : p ∉ fixFin τ := by rw [mem_fixFin, hτe, swap_apply_left]; exact hpq.symm
  have h1 := Perm.ofSubtype_apply_of_not_mem π hpF
  rw [hπ, hτe, swap_apply_left] at h1
  exact hpq h1.symm

theorem twoTheta_injective (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {x : G} (hx : x ∈ centralizer ({z} : Set G))
    (hτ : (permOf h d e hx).IsSwap) : Function.Injective (twoTheta h d T e hx) := by
  obtain ⟨hx2, -, -⟩ := swap_elt_facts h d T e hx hτ
  rw [injective_iff_map_eq_one]
  intro π hπ
  rw [twoTheta_apply, QuotientGroup.eq_one_iff] at hπ
  have hC := swapIota_mem_centralizer h d T e (Perm.ofSubtype π)
  rcases (mem_zpowers_selfC_iff hx2).1 hπ with h1 | h1
  · rw [twoKappa_apply] at h1
    have h2 : swapIota h d T e (Perm.ofSubtype π) = 1 := Subtype.ext h1
    have h3 : Perm.ofSubtype π = 1 := by
      have := congrArg (swapIota h d T e).symm h2
      simpa using this
    exact Perm.ofSubtype_injective (h3.trans (map_one _).symm)
  · exfalso
    rw [twoKappa_apply] at h1
    have h2 : permOf h d e hC = permOf h d e hx := permOf_congr' h1 hC hx h d e
    rw [permOf_swapIota] at h2
    exact ofSubtype_ne_of_isSwap hτ π h2

theorem twoTheta_comm (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {x : G} (hx : x ∈ centralizer ({z} : Set G))
    (hzx : z ∈ centralizer ({x} : Set G)) (π : Perm ↥(fixFin (permOf h d e hx))) :
    twoTheta h d T e hx π * QuotientGroup.mk ⟨z, hzx⟩ =
      QuotientGroup.mk ⟨z, hzx⟩ * twoTheta h d T e hx π := by
  rw [twoTheta_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.1 (swapIota_mem_centralizer h d T e _)

theorem twoTheta_ne (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {x : G} (hx : x ∈ centralizer ({z} : Set G))
    (hτ : (permOf h d e hx).IsSwap) (hzx : z ∈ centralizer ({x} : Set G))
    (π : Perm ↥(fixFin (permOf h d e hx))) :
    twoTheta h d T e hx π ≠ QuotientGroup.mk ⟨z, hzx⟩ := by
  obtain ⟨hx2, -, -⟩ := swap_elt_facts h d T e hx hτ
  intro hπ
  rw [twoTheta_apply, QuotientGroup.eq] at hπ
  set s : G := (swapIota h d T e (Perm.ofSubtype π) : G) with hs
  have hsC : s ∈ centralizer ({z} : Set G) := swapIota_mem_centralizer h d T e _
  have hps : permOf h d e hsC = Perm.ofSubtype π := permOf_swapIota h d T e _
  rcases (mem_zpowers_selfC_iff hx2).1 hπ with h1 | h1
  ·
    have h1' : s⁻¹ * z = 1 := by simpa [twoKappa_apply] using h1
    have hzs : z = s := (inv_mul_eq_one.1 h1').symm
    exact z_notMem_swapComplement h d T.cent T.outer T.sq
      (hzs ▸ (swapIota h d T e (Perm.ofSubtype π)).2)
  ·
    have h1' : s⁻¹ * z = x := by simpa [twoKappa_apply] using h1
    have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
    have hsi : s⁻¹ ∈ centralizer ({z} : Set G) := inv_mem hsC
    have hm : s⁻¹ * z ∈ centralizer ({z} : Set G) := mul_mem hsi hzC
    have hp : permOf h d e hm = (Perm.ofSubtype π)⁻¹ := by
      rw [permOf_mul h d e hsi hzC hm, permOf_self h d e hzC, mul_one, permOf_inv h d e hsC hsi,
        hps]
    have hpx : permOf h d e hm = permOf h d e hx := permOf_congr' h1' hm hx h d e
    rw [hp] at hpx
    have := ofSubtype_ne_of_isSwap hτ π⁻¹
    rw [map_inv] at this
    exact this hpx

theorem mk_eq_twoTheta_or (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {x : G} (hx : x ∈ centralizer ({z} : Set G))
    (hτ : (permOf h d e hx).IsSwap) (hzx : z ∈ centralizer ({x} : Set G)) {b : G}
    (hb : b ∈ centralizer ({z} : Set G)) (hbx : b ∈ centralizer ({x} : Set G)) :
    ∃ σ : Perm ↥(fixFin (permOf h d e hx)),
      (permOf h d e hb = Perm.ofSubtype σ ∨ permOf h d e hb = Perm.ofSubtype σ * permOf h d e hx) ∧
      ((QuotientGroup.mk ⟨b, hbx⟩ : TwoSec x) = twoTheta h d T e hx σ ∨
        (QuotientGroup.mk ⟨b, hbx⟩ : TwoSec x) = QuotientGroup.mk ⟨z, hzx⟩ * twoTheta h d T e hx σ) := by
  obtain ⟨hx2, -, -⟩ := swap_elt_facts h d T e hx hτ
  have hz2 : z * z = 1 := d.mul_self
  set τ := permOf h d e hx with hτdef
  set β := permOf h d e hb with hβ
  obtain ⟨p, q, hpq, hτe⟩ := hτ
  have hcomm : β * τ = τ * β := by
    rw [hβ, hτdef, ← permOf_mul h d e hb hx (mul_mem hb hx),
      ← permOf_mul h d e hx hb (mul_mem hx hb)]
    congr 1
    exact (mem_centralizer_singleton_iff.1 hbx)
  have hmoved : ∀ i, τ i ≠ i → i = p ∨ i = q := by
    intro i hi
    rw [hτe] at hi
    by_contra hcon
    push Not at hcon
    exact hi (swap_apply_of_ne_of_ne hcon.1 hcon.2)
  have hτβ : ∀ i, τ (β i) = β (τ i) := by
    intro i
    have := congrArg (fun f : Perm (Fin n) => f i) hcomm
    simpa [Perm.mul_apply] using this.symm
  have hβp : β p = p ∨ β p = q := by
    apply hmoved
    rw [hτβ, hτe, swap_apply_left]
    intro h'
    exact hpq (β.injective h').symm
  have hβq : β q = p ∨ β q = q := by
    apply hmoved
    rw [hτβ, hτe, swap_apply_right]
    intro h'
    exact hpq (β.injective h')
  have hset : (β p = p ∧ β q = q) ∨ (β p = q ∧ β q = p) := by
    rcases hβp with h1 | h1 <;> rcases hβq with h2 | h2
    · exact absurd (β.injective (h1.trans h2.symm)) hpq
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (β.injective (h1.trans h2.symm)) hpq
  have hnotF : ∀ i, i ∉ fixFin τ → i = p ∨ i = q := by
    intro i hi
    rw [mem_fixFin, hτe] at hi
    by_contra hcon
    push Not at hcon
    exact hi (swap_apply_of_ne_of_ne hcon.1 hcon.2)
  obtain ⟨σ, hσ, hβeq⟩ : ∃ σ : Perm ↥(fixFin τ), (β = Perm.ofSubtype σ ∨
      β = Perm.ofSubtype σ * τ) ∧ (β = Perm.ofSubtype σ ∨ β * τ = Perm.ofSubtype σ) := by
    rcases hset with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · obtain ⟨σ, hσ⟩ := exists_ofSubtype_eq_of_fix (F := fixFin τ) (f := β) (fun i hi => by
        rcases hnotF i hi with rfl | rfl
        · exact hp
        · exact hq)
      exact ⟨σ, Or.inl hσ.symm, Or.inl hσ.symm⟩
    · obtain ⟨σ, hσ⟩ := exists_ofSubtype_eq_of_fix (F := fixFin τ) (f := β * τ) (fun i hi => by
        rcases hnotF i hi with rfl | rfl
        · rw [Perm.mul_apply, hτe, swap_apply_left, hq]
        · rw [Perm.mul_apply, hτe, swap_apply_right, hp])
      refine ⟨σ, Or.inr ?_, Or.inr hσ.symm⟩
      have hτ2 : τ * τ = 1 := by rw [hτe, swap_mul_self]
      calc β = β * τ * τ := by rw [mul_assoc, hτ2, mul_one]
        _ = Perm.ofSubtype σ * τ := by rw [hσ]
  refine ⟨σ, hσ, ?_⟩
  set iτ : G := (swapIota h d T e τ : G) with hiτ
  have hιx : iτ = x ∨ iτ = z * x := by
    rcases eq_swapIota_or h d T e hx with h1 | h1
    · exact Or.inl h1.symm
    · right
      calc iτ = z * (z * iτ) := by rw [← mul_assoc, hz2, one_mul]
        _ = z * x := by rw [← h1]
  have hκ : (twoKappa h d T e hx σ : G) = (swapIota h d T e (Perm.ofSubtype σ) : G) := rfl
  have hιβ : (swapIota h d T e β : G) = twoKappa h d T e hx σ ∨
      (swapIota h d T e β : G) = (twoKappa h d T e hx σ : G) * iτ := by
    rcases hσ with h1 | h1
    · left; rw [hκ, h1]
    · right; rw [hκ, h1, map_mul]; rfl
  set K := twoKappa h d T e hx σ with hK
  set Z : ↥(centralizer ({x} : Set G)) := ⟨z, hzx⟩ with hZ
  have hKz : (K : G) * z = z * K :=
    mem_centralizer_singleton_iff.1 (swapIota_mem_centralizer h d T e _)
  have hZK : ((Z * K : ↥(centralizer ({x} : Set G))) : G) = z * K := rfl
  have hleft : (b = (K : G) ∨ b = (K : G) * x) →
      (QuotientGroup.mk ⟨b, hbx⟩ : TwoSec x) = twoTheta h d T e hx σ := fun hbK =>
    (mk_eq_of_eq_or_mul hx2 hbx hbK).trans (twoTheta_apply h d T e hx σ).symm
  have hright : (b = z * (K : G) ∨ b = z * (K : G) * x) →
      (QuotientGroup.mk ⟨b, hbx⟩ : TwoSec x) =
        QuotientGroup.mk ⟨z, hzx⟩ * twoTheta h d T e hx σ := by
    intro hbK
    rw [twoTheta_apply, ← QuotientGroup.mk_mul]
    exact mk_eq_of_eq_or_mul hx2 hbx (c := Z * K) (by rw [hZK]; exact hbK)
  rcases eq_swapIota_or h d T e hb with hb1 | hb1 <;> rcases hιβ with h2 | h2
  · exact Or.inl (hleft (Or.inl (hb1.trans h2)))
  · rcases hιx with h3 | h3
    · exact Or.inl (hleft (Or.inr (by rw [hb1, h2, h3])))
    · exact Or.inr (hright (Or.inr (by rw [hb1, h2, h3, ← mul_assoc, hKz])))
  · exact Or.inr (hright (Or.inl (by rw [hb1, h2])))
  · rcases hιx with h3 | h3
    · exact Or.inr (hright (Or.inr (by rw [hb1, h2, h3, mul_assoc])))
    · refine Or.inl (hleft (Or.inr ?_))
      rw [hb1, h2, h3]
      calc z * ((K : G) * (z * x)) = z * ((K : G) * z) * x := by group
        _ = z * (z * K) * x := by rw [hKz]
        _ = (z * z) * (K : G) * x := by group
        _ = (K : G) * x := by rw [hz2, one_mul]

end Theta

section Wreath

variable {X : Type} [Group X] [Finite X]

theorem exists_conj_mul_of_wreath {t b : X} {B : Subgroup X} {m : ℕ} (hm : 5 ≤ m)
    (ht : t * t = 1) (hb : b * b = 1) (hW : WreathOutcome t B m) (hbB : b ∈ B) :
    ∃ k : X, k * t * k⁻¹ = t * b := by
  obtain ⟨K, hKc, hKne, -, ⟨eK⟩, hdiag⟩ := hW
  set K' : Subgroup X := K.map (MulAut.conj t).toMonoidHom with hK'
  have hK'c : CFSG.IsComponent K' := CFSG.LocalCores.isComponent_map_mulEquiv _ hKc
  have hKK' : ⁅K, K'⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hKc hK'c with h1 | h1
    · exact absurd h1.symm hKne
    · exact h1
  have hKle : K ≤ centralizer (K' : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hKK'
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hbB' : b ∈ (B : Set X) := hbB
  rw [hdiag] at hbB'
  obtain ⟨k, hkK, hk⟩ := hbB'
  set k' : X := t * k * t⁻¹ with hk'def
  have hk'K' : k' ∈ K' := ⟨k, hkK, by simp [hk'def, MulAut.conj_apply]⟩
  have hkk' : k * k' = k' * k := (mem_centralizer_iff.1 (hKle hkK) k' hk'K').symm
  have hcenter : center K = ⊥ := center_eq_bot_of_alt (by omega) eK
  have hKinf : ∀ y : X, y ∈ K → y ∈ K' → y = 1 := by
    intro y hyK hyK'
    have hy : (⟨y, hyK⟩ : K) ∈ center K := by
      rw [Subgroup.mem_center_iff]
      intro a
      apply Subtype.ext
      exact (mem_centralizer_iff.1 (hKle a.2) y hyK').symm
    rw [hcenter, Subgroup.mem_bot] at hy
    exact congrArg Subtype.val hy
  have hkk2 : k * k = 1 := by
    have h1 : (k * k') * (k * k') = 1 := by rw [← hk]; exact hb
    have h2 : (k * k) * (k' * k') = 1 := by
      calc (k * k) * (k' * k') = k * (k * k') * k' := by group
        _ = k * (k' * k) * k' := by rw [hkk']
        _ = (k * k') * (k * k') := by group
        _ = 1 := h1
    have hk'k'K' : k' * k' ∈ K' := mul_mem hk'K' hk'K'
    have h3 : k * k = (k' * k')⁻¹ := eq_inv_of_mul_eq_one_left h2
    exact hKinf _ (mul_mem hkK hkK) (by rw [h3]; exact inv_mem hk'k'K')
  have hk1 : k⁻¹ = k := inv_eq_of_mul_eq_one_right hkk2
  refine ⟨k, ?_⟩
  rw [hk, hk1]
  have h1 : k * (t * k * t) = (t * k * t) * k := by
    have := hkk'
    rw [hk'def, ht1] at this
    exact this
  calc k * t * k = k * (t * k * t) * t := by
        rw [show k * (t * k * t) * t = k * t * k * (t * t) by group, ht, mul_one]
    _ = (t * k * t) * k * t := by rw [h1]
    _ = t * (k * (t * k * t⁻¹)) := by rw [ht1]; group

end Wreath

section Outcomes

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z u : G}

theorem exists_partner_of_symOutcome (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) (hn : 9 ≤ n) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) (hτ : (permOf h d e hx).IsSwap)
    (hfus : ¬ IsConj z (z * x)) (hzx : z ∈ centralizer ({x} : Set G))
    (hS : SymOutcome (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) (n - 2)) :
    ∃ (b : G) (hb : b ∈ centralizer ({z} : Set G)), IsConj z b ∧ b ≠ z ∧
      ((fixFin (permOf h d e hb)).card = n - 2 ∨ (fixFin (permOf h d e hb)).card = n - 4) := by
  classical
  obtain ⟨hx2, -, -⟩ := swap_elt_facts h d T e hx hτ
  have hz2 : z * z = 1 := d.mul_self
  obtain ⟨ε, hε⟩ := hS
  set zb : TwoSec x := QuotientGroup.mk ⟨z, hzx⟩ with hzb
  have hzb2 : zb * zb = 1 := by
    rw [hzb, ← QuotientGroup.mk_mul]
    have : (⟨z, hzx⟩ : ↥(centralizer ({x} : Set G))) * ⟨z, hzx⟩ = 1 := Subtype.ext hz2
    rw [this]; rfl
  set τ₀ := ε.symm zb with hτ₀
  have hτ₀s : τ₀.IsSwap := hε
  obtain ⟨p₀, q₀, hpq₀, hτ₀e⟩ := hε
  have hq₀ : q₀ ∈ Finset.univ.erase p₀ := Finset.mem_erase.2 ⟨hpq₀.symm, Finset.mem_univ _⟩
  have h2 : 1 < ((Finset.univ.erase p₀).erase q₀).card := by
    rw [Finset.card_erase_of_mem hq₀, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨r₀, hr₀, s₀, hs₀, hrs₀⟩ := Finset.one_lt_card.1 h2
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hr₀ hs₀
  set τ₁ : Perm (Fin (n - 2 + 2)) := swap r₀ s₀ with hτ₁
  have hτ₁s : τ₁.IsSwap := ⟨r₀, s₀, hrs₀, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Perm (Fin (n - 2 + 2)), c = swap p₀ r₀ * swap q₀ s₀ := ⟨_, rfl⟩
  have hcτ : c * τ₀ * c⁻¹ = τ₁ := by
    have hcp : c p₀ = r₀ := by
      rw [hc, Perm.mul_apply, swap_apply_of_ne_of_ne hpq₀ hs₀.2.symm, swap_apply_left]
    have hcq : c q₀ = s₀ := by
      rw [hc, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hs₀.2 hrs₀.symm]
    rw [hτ₀e, ← swap_apply_apply, hcp, hcq]
  have hετ₀ : ε τ₀ = zb := by rw [hτ₀, MulEquiv.apply_symm_apply]
  have hdisj : τ₁ * τ₀ = τ₀ * τ₁ := by
    rw [hτ₀e, hτ₁]
    apply Perm.Disjoint.commute
    intro i
    by_cases hi : i = r₀ ∨ i = s₀
    · right
      rcases hi with rfl | rfl
      · exact swap_apply_of_ne_of_ne hr₀.2 hr₀.1
      · exact swap_apply_of_ne_of_ne hs₀.2 hs₀.1
    · push Not at hi
      exact Or.inl (swap_apply_of_ne_of_ne hi.1 hi.2)
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (ε c)
  set b₀ : ↥(centralizer ({x} : Set G)) := y * ⟨z, hzx⟩ * y⁻¹ with hb₀
  have hmkb : (QuotientGroup.mk b₀ : TwoSec x) = ε τ₁ := by
    have h1 : ε τ₁ = ε c * ε τ₀ * (ε c)⁻¹ := by rw [← hcτ, map_mul, map_mul, map_inv]
    rw [h1, hετ₀, ← hy, hb₀, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  set b : G := (b₀ : G) with hbdef
  have hbx : b ∈ centralizer ({x} : Set G) := b₀.2
  have hmkb' : (QuotientGroup.mk ⟨b, hbx⟩ : TwoSec x) = ε τ₁ := hmkb
  have hb : b ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    refine comm_of_mk_comm hx2 hfus hzx hbx ?_
    rw [hmkb', ← hzb, ← hετ₀, ← map_mul, ← map_mul, hdisj]
  refine ⟨b, hb, isConj_iff.2 ⟨(y : G), by rw [hbdef, hb₀]; simp⟩, ?_, ?_⟩
  · intro hbz
    have h1 : ε τ₁ = ε τ₀ := by
      rw [← hmkb', hετ₀, hzb]
      congr 1
      exact Subtype.ext hbz
    have h2 := ε.injective h1
    have h3 := congrArg (fun f : Perm (Fin (n - 2 + 2)) => f r₀) h2
    simp only [hτ₁, swap_apply_left, hτ₀e, swap_apply_of_ne_of_ne hr₀.2 hr₀.1] at h3
    exact hrs₀ h3.symm
  ·
    obtain ⟨σ, hβ, hmk⟩ := mk_eq_twoTheta_or h d T e hx hτ hzx hb hbx
    set Ψ : Perm ↥(fixFin (permOf h d e hx)) →* Perm (Fin (n - 2 + 2)) :=
      ε.symm.toMonoidHom.comp (twoTheta h d T e hx) with hΨ
    have hFcard : (fixFin (permOf h d e hx)).card = n - 2 := card_fixFin_of_isSwap hτ
    have hinj : Function.Injective Ψ :=
      ε.symm.injective.comp (twoTheta_injective h d T e hx hτ)
    have hcomm : ∀ π, Ψ π * τ₀ = τ₀ * Ψ π := by
      intro π
      simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, hτ₀]
      rw [← map_mul, ← map_mul, twoTheta_comm h d T e hx hzx π]
    have hne : ∀ π, Ψ π ≠ τ₀ := by
      intro π hπ
      simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, hτ₀] at hπ
      exact twoTheta_ne h d T e hx hτ hzx π (ε.symm.injective hπ)
    have hτ₁ne : τ₁ ≠ τ₀ := by
      intro h'
      have h3 := congrArg (fun f : Perm (Fin (n - 2 + 2)) => f r₀) h'
      simp only [hτ₁, swap_apply_left, hτ₀e, swap_apply_of_ne_of_ne hr₀.2 hr₀.1] at h3
      exact hrs₀ h3.symm
    have hσΨ : Ψ σ = τ₁ ∨ Ψ σ = τ₀ * τ₁ := by
      simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
      rcases hmk with h1 | h1
      · left
        rw [← h1, hmkb', MulEquiv.symm_apply_apply]
      · right
        have h1' : twoTheta h d T e hx σ = zb * ε τ₁ := by
          rw [← hmkb', h1, ← mul_assoc, hzb2, one_mul]
        rw [h1', map_mul, MulEquiv.symm_apply_apply]
    have hσs : σ.IsSwap := by
      refine isSwap_of_embedding (α := ↥(fixFin (permOf h d e hx))) (β := Fin (n - 2 + 2)) ?_ ?_
        Ψ hinj hτ₀s hcomm hne hτ₁s hdisj hτ₁ne hσΨ
      · simp only [Fintype.card_fin, Fintype.card_coe, hFcard]
      · simp only [Fintype.card_coe, hFcard]; omega
    have hσ' : (Perm.ofSubtype σ).IsSwap := hσs.of_subtype_isSwap
    rcases hβ with h1 | h1
    · left
      rw [h1]
      exact card_fixFin_of_isSwap hσ'
    · right
      have hd : (Perm.ofSubtype σ).Disjoint (permOf h d e hx) := by
        intro i
        by_cases hi : i ∈ fixFin (permOf h d e hx)
        · exact Or.inr (mem_fixFin.1 hi)
        · exact Or.inl (Perm.ofSubtype_apply_of_not_mem σ hi)
      have h3 := card_fixFin_mul_of_disjoint hd
      rw [Perm.card_support_eq_two.2 hσ', Perm.card_support_eq_two.2 hτ] at h3
      rw [h1]
      omega

theorem exists_partner_of_wreathOutcome (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) (hn : 9 ≤ n) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) (hτ : (permOf h d e hx).IsSwap)
    (hfus : ¬ IsConj z (z * x)) (hzx : z ∈ centralizer ({x} : Set G))
    (hW : WreathOutcome (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x)
      (twoSecComp e x (fixFin (permOf h d e hx))) (n - 2)) :
    ∃ (b : G) (hb : b ∈ centralizer ({z} : Set G)), IsConj z b ∧ b ≠ z ∧
      ((fixFin (permOf h d e hb)).card = n - 4 ∨ (fixFin (permOf h d e hb)).card = n - 6) := by
  classical
  obtain ⟨hx2, -, -⟩ := swap_elt_facts h d T e hx hτ
  have hz2 : z * z = 1 := d.mul_self
  set F : Finset (Fin n) := fixFin (permOf h d e hx) with hF
  have hFcard : F.card = n - 2 := card_fixFin_of_isSwap hτ
  obtain ⟨a₁, ha₁, a₂, ha₂, h12⟩ := Finset.one_lt_card.1 (show 1 < F.card by omega)
  have ha₂' : a₂ ∈ F.erase a₁ := Finset.mem_erase.2 ⟨h12.symm, ha₂⟩
  have h34 : 1 < ((F.erase a₁).erase a₂).card := by
    rw [Finset.card_erase_of_mem ha₂', Finset.card_erase_of_mem ha₁]
    omega
  obtain ⟨a₃, ha₃, a₄, ha₄, h34'⟩ := Finset.one_lt_card.1 h34
  simp only [Finset.mem_erase] at ha₃ ha₄
  obtain ⟨h32, h31, ha₃F⟩ := ha₃
  obtain ⟨h42, h41, ha₄F⟩ := ha₄
  set δ : Perm (Fin n) := swap a₁ a₂ * swap a₃ a₄ with hδ
  have hdisj12 : (swap a₁ a₂).Disjoint (swap a₃ a₄) := by
    intro i
    by_cases hi : i = a₁ ∨ i = a₂
    · right
      rcases hi with rfl | rfl
      · exact swap_apply_of_ne_of_ne h31.symm h41.symm
      · exact swap_apply_of_ne_of_ne h32.symm h42.symm
    · push Not at hi
      exact Or.inl (swap_apply_of_ne_of_ne hi.1 hi.2)
  have hδ2 : δ * δ = 1 := by
    rw [hδ]
    calc swap a₁ a₂ * swap a₃ a₄ * (swap a₁ a₂ * swap a₃ a₄) =
        swap a₁ a₂ * (swap a₃ a₄ * swap a₁ a₂) * swap a₃ a₄ := by group
      _ = swap a₁ a₂ * (swap a₁ a₂ * swap a₃ a₄) * swap a₃ a₄ := by
        rw [hdisj12.commute.eq]
      _ = 1 := by
        rw [← mul_assoc, swap_mul_self, one_mul, swap_mul_self]
  have hδF : δ ∈ altSub F := by
    refine mem_altSub.2 ⟨?_, fun i hi => ?_⟩
    · rw [hδ, Perm.sign_mul, Perm.sign_swap h12, Perm.sign_swap h34']; rfl
    · have hi1 : i ≠ a₁ := fun h' => hi (h' ▸ ha₁)
      have hi2 : i ≠ a₂ := fun h' => hi (h' ▸ ha₂)
      have hi3 : i ≠ a₃ := fun h' => hi (h' ▸ ha₃F)
      have hi4 : i ≠ a₄ := fun h' => hi (h' ▸ ha₄F)
      rw [hδ, Perm.mul_apply, swap_apply_of_ne_of_ne hi3 hi4, swap_apply_of_ne_of_ne hi1 hi2]
  have hδA : δ ∈ alternatingGroup (Fin n) := altSub_le_alternatingGroup F hδF
  set a' : L := e.symm ⟨δ, hδA⟩ with ha'
  have hea' : ((e a' : alternatingGroup (Fin n)) : Perm (Fin n)) = δ := by simp [ha']
  set a : G := (a' : G) with ha
  have haR : a ∈ corr (X := G) e (altSub F) := mem_corr_of_mem (by rw [hea']; exact hδF)
  have hax : a ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact (comm_of_mem_corr_of_permOf_fix h d e hx (fun i hi => mem_fixFin.1 hi) haR).symm
  have haL : a ∈ L := a'.2
  have haz : a ∈ centralizer ({z} : Set G) := le_centralizer_single h d haL
  have hpa : permOf h d e haz = δ := by
    rw [permOf_of_mem h d e haz haL]
    exact hea'
  have ha2 : a * a = 1 := by
    have : a' * a' = 1 := by
      apply e.injective
      apply Subtype.ext
      rw [map_mul, map_one, Subgroup.coe_mul, hea', OneMemClass.coe_one]
      exact hδ2
    exact congrArg Subtype.val this
  set zb : TwoSec x := QuotientGroup.mk ⟨z, hzx⟩ with hzb
  set ab : TwoSec x := QuotientGroup.mk ⟨a, hax⟩ with hab
  have hzb2 : zb * zb = 1 := by
    rw [hzb, ← QuotientGroup.mk_mul]
    have : (⟨z, hzx⟩ : ↥(centralizer ({x} : Set G))) * ⟨z, hzx⟩ = 1 := Subtype.ext hz2
    rw [this]; rfl
  have hab2 : ab * ab = 1 := by
    rw [hab, ← QuotientGroup.mk_mul]
    have : (⟨a, hax⟩ : ↥(centralizer ({x} : Set G))) * ⟨a, hax⟩ = 1 := Subtype.ext ha2
    rw [this]; rfl
  have habB : ab ∈ twoSecComp e x F := ⟨⟨a, hax⟩, Subgroup.mem_subgroupOf.2 haR, rfl⟩
  have haz' : a * z = z * a := mem_centralizer_singleton_iff.1 haz
  have hzab : zb * ab = ab * zb := by
    rw [hzb, hab, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext haz'.symm
  obtain ⟨k, hk⟩ := exists_conj_mul_of_wreath (by omega) hzb2 hab2 hW habB
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective k
  set b₀ : ↥(centralizer ({x} : Set G)) := y * ⟨z, hzx⟩ * y⁻¹ with hb₀
  have hmkb : (QuotientGroup.mk b₀ : TwoSec x) = zb * ab := by
    rw [hb₀, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy]
    exact hk
  set b : G := (b₀ : G) with hbdef
  have hbx : b ∈ centralizer ({x} : Set G) := b₀.2
  have hmkb' : (QuotientGroup.mk ⟨b, hbx⟩ : TwoSec x) = zb * ab := hmkb
  have hb : b ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    refine comm_of_mk_comm hx2 hfus hzx hbx ?_
    rw [hmkb', ← hzb, mul_assoc, ← hzab, ← mul_assoc]
  have hbza : b = z * a ∨ b = z * a * x := by
    have h1 : (QuotientGroup.mk ⟨b, hbx⟩ : TwoSec x) =
        QuotientGroup.mk (⟨z, hzx⟩ * ⟨a, hax⟩ : ↥(centralizer ({x} : Set G))) := by
      rw [hmkb', QuotientGroup.mk_mul]
    have h2 := (mem_zpowers_selfC_iff hx2).1 (QuotientGroup.eq.1 h1.symm)
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    rcases h2 with h2 | h2
    · left
      have h2' : (z * a)⁻¹ * b = 1 := by simpa using h2
      exact (inv_mul_eq_one.1 h2').symm
    · right
      have h2' : (z * a)⁻¹ * b = x := by simpa using h2
      calc b = (z * a) * ((z * a)⁻¹ * b) := by group
        _ = z * a * x := by rw [h2']
  have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hza : z * a ∈ centralizer ({z} : Set G) := mul_mem hzC haz
  have hpza : permOf h d e hza = δ := by
    rw [permOf_mul h d e hzC haz hza, permOf_self h d e hzC, one_mul, hpa]
  refine ⟨b, hb, isConj_iff.2 ⟨(y : G), by rw [hbdef, hb₀]; simp⟩, ?_, ?_⟩
  · intro hbz
    rcases hbza with h1 | h1
    · have : a = 1 := by
        have := h1.symm.trans hbz
        calc a = z⁻¹ * (z * a) := by group
          _ = 1 := by rw [this, inv_mul_cancel]
      have hδ1 : δ = 1 := by
        rw [← hpa, permOf_congr' this haz (one_mem _) h d e]
        show rho e h.hn 1 = 1
        exact map_one _
      have := congrArg (fun f : Perm (Fin n) => f a₁) hδ1
      simp only [hδ, Perm.mul_apply, swap_apply_of_ne_of_ne h31.symm h41.symm, swap_apply_left,
        Perm.one_apply] at this
      exact h12 this.symm
    ·
      have hax' : a = x := by
        have h2 : z * a * x = z := h1.symm.trans hbz
        have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
        calc a = z⁻¹ * (z * a * x) * x⁻¹ := by group
          _ = x := by rw [h2, inv_mul_cancel, one_mul, hxinv]
      have hδτ : δ = permOf h d e hx := by
        rw [← hpa]; exact permOf_congr' hax' haz hx h d e
      have hfa₁ : permOf h d e hx a₁ = a₁ := mem_fixFin.1 ha₁
      have h5 := congrArg (fun f : Perm (Fin n) => f a₁) hδτ
      simp only [hδ, Perm.mul_apply, swap_apply_of_ne_of_ne h31.symm h41.symm, swap_apply_left]
        at h5
      rw [hfa₁] at h5
      exact h12 h5.symm
  ·
    have hdτ : δ.Disjoint (permOf h d e hx) := by
      intro i
      by_cases hi : i ∈ F
      · exact Or.inr (mem_fixFin.1 hi)
      · exact Or.inl ((mem_altSub.1 hδF).2 i hi)
    have hsuppδ : δ.support.card = 4 := by
      rw [hδ, hdisj12.card_support_mul, card_support_swap h12, card_support_swap h34']
    rcases hbza with h1 | h1
    · left
      have hpb : permOf h d e hb = δ := (permOf_congr' h1 hb hza h d e).trans hpza
      have h3 := card_fixFin_add_card_support (permOf h d e hb)
      rw [hpb, hsuppδ] at h3
      rw [hpb]
      omega
    · right
      have hzax : z * a * x ∈ centralizer ({z} : Set G) := mul_mem hza hx
      have hpb : permOf h d e hb = δ * permOf h d e hx :=
        (permOf_congr' h1 hb hzax h d e).trans (by rw [permOf_mul h d e hza hx hzax, hpza])
      have h3 := card_fixFin_mul_of_disjoint hdτ
      rw [hsuppδ, Perm.card_support_eq_two.2 hτ] at h3
      rw [hpb]
      omega

theorem twoSec_cases (htri : ExactShapeTrichotomy) (h : Setting G L n) (d : Cyc L Q z)
    (T : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin n)) (hn : 11 ≤ n) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) (hτ : (permOf h d e hx).IsSwap)
    (hfus : ¬ IsConj z (z * x)) (hzx : z ∈ centralizer ({x} : Set G)) :
    centralizer ({x} : Set G) ≤ centralizer ({z} : Set G) ∨
      (∃ (b : G) (hb : b ∈ centralizer ({z} : Set G)), IsConj z b ∧ b ≠ z ∧
        ((fixFin (permOf h d e hb)).card = n - 2 ∨ (fixFin (permOf h d e hb)).card = n - 4 ∨
          (fixFin (permOf h d e hb)).card = n - 6)) ∨ n = 12 := by
  obtain ⟨hx2, -, hx1⟩ := swap_elt_facts h d T e hx hτ
  have hxord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hE := exactShape_twoSec h d T e (by omega) hx hτ hfus hzx
  rcases htri (TwoSec x) _ _ (n - 2) (by omega) (isKGroupCat_twoSec h hx1)
      (oddCore_twoSec_eq_bot h hxord) hE with h1 | h1 | h1 | h1
  · exact Or.inl (centralizer_le_of_mem_center hx2 hfus hzx h1)
  · obtain ⟨b, hb, h2, h3, h4⟩ :=
      exists_partner_of_wreathOutcome h d T e (by omega) hx hτ hfus hzx h1
    exact Or.inr (Or.inl ⟨b, hb, h2, h3, Or.inr h4⟩)
  · obtain ⟨b, hb, h2, h3, h4⟩ :=
      exists_partner_of_symOutcome h d T e (by omega) hx hτ hfus hzx h1
    exact Or.inr (Or.inl ⟨b, hb, h2, h3, h4.elim Or.inl (fun h5 => Or.inr (Or.inl h5))⟩)
  · exact Or.inr (Or.inr (by omega))

end Outcomes

end CFSG.OddStandard.AltStdSec
