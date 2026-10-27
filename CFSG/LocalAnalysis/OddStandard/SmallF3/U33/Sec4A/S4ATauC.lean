module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

section Transport

variable {K G : Type*} [Group K] [Group G]

theorem map_baseGrp' (f : K →* G) (x₁ x₂ : K) :
    (baseGrp x₁ x₂).map f = baseGrp (f x₁) (f x₂) := by
  rw [show baseGrp x₁ x₂ = Subgroup.closure ({x₁, x₂} : Set K) from rfl,
    show baseGrp (f x₁) (f x₂) = Subgroup.closure ({f x₁, f x₂} : Set G) from rfl,
    MonoidHom.map_closure]
  congr 1
  simp only [Set.image_insert_eq, Set.image_singleton]

theorem map_closure_yzl' (f : K →* G) (x₁ x₂ lam : K) :
    (Subgroup.closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, lam} : Set K)).map f =
      Subgroup.closure ({f x₁ ^ 2, (f x₁ * f x₂) ^ 2, f lam} : Set G) := by
  rw [MonoidHom.map_closure]
  congr 1
  simp only [Set.image_insert_eq, Set.image_singleton, map_pow, map_mul]

theorem map_closure_yzrl' (f : K →* G) (x₁ x₂ rho lam : K) :
    (Subgroup.closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} : Set K)).map f =
      Subgroup.closure ({f x₁ ^ 2, (f x₁ * f x₂) ^ 2, f rho, f lam} : Set G) := by
  rw [MonoidHom.map_closure]
  congr 1
  simp only [Set.image_insert_eq, Set.image_singleton, map_pow, map_mul]

end Transport

section Action

variable {G : Type} [Group G] [Finite G] {t : G} {L : Subgroup G}

theorem hyp_conj_mem_L (h : Hyp G t L) {g : G} (hg : g ∈ invCent t) {x : G} (hx : x ∈ L) :
    g * x * g⁻¹ ∈ L := by
  have hxH : x ∈ invCent t := L_le_invCent h hx
  have hmem : (⟨g, hg⟩ : ↥(invCent t)) * (⟨x, hxH⟩ : ↥(invCent t)) *
      (⟨g, hg⟩ : ↥(invCent t))⁻¹ ∈ L.subgroupOf (invCent t) :=
    h.normal.conj_mem ⟨x, hxH⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨g, hg⟩
  simpa using (Subgroup.mem_subgroupOf.mp hmem)

@[expose] noncomputable def ctxConjAut (h : Hyp G t L) (g : ↥(invCent t)) : MulAut ↥L where
  toFun x := ⟨(g : G) * (x : G) * (g : G)⁻¹, hyp_conj_mem_L h g.2 x.2⟩
  invFun x := ⟨(g : G)⁻¹ * (x : G) * (g : G), by
    simpa using hyp_conj_mem_L h ((invCent t).inv_mem g.2) x.2⟩
  left_inv x := by
    apply Subtype.ext
    change (g : G)⁻¹ * ((g : G) * (x : G) * (g : G)⁻¹) * (g : G) = (x : G)
    group
  right_inv x := by
    apply Subtype.ext
    change (g : G) * ((g : G)⁻¹ * (x : G) * (g : G)) * (g : G)⁻¹ = (x : G)
    group
  map_mul' x y := by
    apply Subtype.ext
    change (g : G) * ((x : G) * (y : G)) * (g : G)⁻¹
      = ((g : G) * (x : G) * (g : G)⁻¹) * ((g : G) * (y : G) * (g : G)⁻¹)
    group

theorem ctxConjAut_apply (h : Hyp G t L) (g : ↥(invCent t)) (x : ↥L) :
    ((ctxConjAut h g x : ↥L) : G) = (g : G) * (x : G) * (g : G)⁻¹ := rfl

theorem ctxConjAut_mul (h : Hyp G t L) (g g' : ↥(invCent t)) :
    ctxConjAut h g * ctxConjAut h g' = ctxConjAut h (g * g') := by
  ext x
  simp only [ctxConjAut_apply, MulAut.mul_apply, Subgroup.coe_mul]
  group

theorem ctxConjAut_one (h : Hyp G t L) : ctxConjAut h (1 : ↥(invCent t)) = 1 := by
  ext x
  simp only [ctxConjAut_apply, MulAut.one_apply, Subgroup.coe_one]
  group

@[expose] noncomputable def ctxConjHom (h : Hyp G t L) : ↥(invCent t) →* MulAut ↥L where
  toFun := ctxConjAut h
  map_one' := ctxConjAut_one h
  map_mul' g g' := (ctxConjAut_mul h g g').symm

theorem ctxConjHom_apply (h : Hyp G t L) (g : ↥(invCent t)) (x : ↥L) :
    ((ctxConjHom h g x : ↥L) : G) = (g : G) * (x : G) * (g : G)⁻¹ := rfl

theorem ctxConjHom_eq_iff (h : Hyp G t L) (g g' : ↥(invCent t)) :
    ctxConjHom h g = ctxConjHom h g' ↔ (g : G)⁻¹ * (g' : G) ∈ twoCore t := by
  constructor
  · intro heq
    have hdH : (g : G)⁻¹ * (g' : G) ∈ invCent t :=
      (invCent t).mul_mem ((invCent t).inv_mem g.2) g'.2
    have hdC : (g : G)⁻¹ * (g' : G) ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hxL : x ∈ L := hx
      have h1 : (g : G) * x * (g : G)⁻¹ = (g' : G) * x * (g' : G)⁻¹ := by
        have hc := congrArg (fun f : MulAut ↥L => (f ⟨x, hxL⟩ : G)) heq
        simpa [ctxConjHom_apply] using hc
      have h2 : x * ((g : G)⁻¹ * (g' : G)) = ((g : G)⁻¹ * (g' : G)) * x := by
        calc x * ((g : G)⁻¹ * (g' : G))
            = (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g' : G) := by group
          _ = (g : G)⁻¹ * ((g' : G) * x * (g' : G)⁻¹) * (g' : G) := by rw [h1]
          _ = ((g : G)⁻¹ * (g' : G)) * x := by group
      exact h2
    have hmem : (g : G)⁻¹ * (g' : G) ∈ Subgroup.centralizer (L : Set G) ⊓ invCent t :=
      ⟨hdC, hdH⟩
    rwa [h.centralizer_eq] at hmem
  · intro hp
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [ctxConjHom_apply, ctxConjHom_apply]
    have hcomm : ((g : G)⁻¹ * (g' : G)) * (x : G) = (x : G) * ((g : G)⁻¹ * (g' : G)) :=
      twoCore_commute h _ hp _ x.2
    have hconj : ((g : G)⁻¹ * (g' : G)) * (x : G) * ((g : G)⁻¹ * (g' : G))⁻¹ = (x : G) := by
      rw [hcomm]
      group
    calc (g : G) * (x : G) * (g : G)⁻¹
        = (g : G) * (((g : G)⁻¹ * (g' : G)) * (x : G) * ((g : G)⁻¹ * (g' : G))⁻¹) *
            (g : G)⁻¹ := by rw [hconj]
      _ = (g' : G) * (x : G) * (g' : G)⁻¹ := by group

theorem ctxConjHom_eq_one_iff (h : Hyp G t L) (g : ↥(invCent t)) :
    ctxConjHom h g = 1 ↔ (g : G) ∈ twoCore t := by
  have h1 := ctxConjHom_eq_iff h g 1
  rw [map_one] at h1
  simpa using h1

theorem ctxConjHom_coe (h : Hyp G t L) (l : ↥L) :
    ctxConjHom h ⟨(l : G), L_le_invCent h l.2⟩ = MulAut.conj l := by
  ext x
  simp only [ctxConjHom_apply, MulAut.conj_apply, Subtype.coe_mk, Subgroup.coe_mul,
    Subgroup.coe_inv]

theorem ctxConjHom_inner_iff (h : Hyp G t L) (g : ↥(invCent t)) :
    (∃ k : ↥L, ctxConjHom h g = MulAut.conj k) ↔ (g : G) ∈ twoCore t ⊔ L := by
  constructor
  · rintro ⟨k, heq⟩
    have hkH : (k : G) ∈ invCent t := L_le_invCent h k.2
    have hcH : (k : G)⁻¹ * (g : G) ∈ invCent t :=
      (invCent t).mul_mem ((invCent t).inv_mem hkH) g.2
    have hcP : (k : G)⁻¹ * (g : G) ∈ twoCore t := by
      have h1 : ctxConjHom h ⟨(k : G), hkH⟩ = ctxConjHom h g := by
        rw [ctxConjHom_coe, heq]
      exact (ctxConjHom_eq_iff h ⟨(k : G), hkH⟩ g).mp h1
    have hmem : (g : G) ∈ L ⊔ twoCore t := by
      have hg : (g : G) = (k : G) * ((k : G)⁻¹ * (g : G)) := by group
      rw [hg]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right hcP)
    rwa [sup_comm] at hmem
  · intro hg
    let Q : Subgroup G := ((MulAut.conj : ↥L →* MulAut ↥L).range.comap (ctxConjHom h)).map
      (invCent t).subtype
    have hPQ : twoCore t ≤ Q := by
      intro p hp
      refine ⟨⟨p, twoCore_le_invCent t hp⟩, ?_, rfl⟩
      refine ⟨1, ?_⟩
      rw [map_one]
      exact ((ctxConjHom_eq_one_iff h ⟨p, twoCore_le_invCent t hp⟩).mpr hp).symm
    have hLQ : L ≤ Q := by
      intro l hl
      refine ⟨⟨l, L_le_invCent h hl⟩, ?_, rfl⟩
      exact ⟨⟨l, hl⟩, ctxConjHom_coe h ⟨l, hl⟩⟩
    obtain ⟨g', hg', hgg'⟩ := sup_le hPQ hLQ hg
    have hg'g : g' = g := Subtype.ext hgg'
    rw [hg'g] at hg'
    obtain ⟨k, hk⟩ := hg'
    exact ⟨k, hk.symm⟩

end Action

section Sylow

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem twoCore_le_S (h : Ctx0 t L S x₁ x₂ lam rho) : twoCore t ≤ S := by
  calc twoCore t ≤ twoCore t ⊔ wreathGrp x₁ x₂ lam := le_sup_left
    _ = S ⊓ (twoCore t ⊔ L) := h.inf_PL.symm
    _ ≤ S := inf_le_left

theorem wreathGrp_le_S (h : Ctx0 t L S x₁ x₂ lam rho) : wreathGrp x₁ x₂ lam ≤ S := by
  rw [← h.inf_eq]
  exact inf_le_left

theorem wreathGrp_le_L_ctx0 (h : Ctx0 t L S x₁ x₂ lam rho) : wreathGrp x₁ x₂ lam ≤ L := by
  rw [← h.inf_eq]
  exact inf_le_right

@[expose] noncomputable def ctxConjHomS (h : Ctx0 t L S x₁ x₂ lam rho) : ↥S →* MulAut ↥L :=
  (ctxConjHom h.hyp).comp (Subgroup.inclusion h.le_invCent)

theorem ctxConjHomS_apply (h : Ctx0 t L S x₁ x₂ lam rho) (s : ↥S) (x : ↥L) :
    ((ctxConjHomS h s x : ↥L) : G) = (s : G) * (x : G) * (s : G)⁻¹ := rfl

theorem ctxConjHomS_eq (h : Ctx0 t L S x₁ x₂ lam rho) (s : ↥S) :
    ctxConjHomS h s = ctxConjHom h.hyp ⟨(s : G), h.le_invCent s.2⟩ := rfl

theorem ctxConjHomS_ker (h : Ctx0 t L S x₁ x₂ lam rho) :
    (ctxConjHomS h).ker = (twoCore t).subgroupOf S := by
  ext s
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ctxConjHomS_eq]
  exact ctxConjHom_eq_one_iff h.hyp ⟨(s : G), h.le_invCent s.2⟩

theorem card_range_ctxConjHomS (h : Ctx0 t L S x₁ x₂ lam rho)
    (hS : Nat.card S = 2 ^ 6 * Nat.card (twoCore t)) :
    Nat.card (ctxConjHomS h).range = 64 := by
  have h1 := Subgroup.card_ker_mul_card_range (ctxConjHomS h)
  have h2 : Nat.card ((twoCore t).subgroupOf S) = Nat.card (twoCore t) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (twoCore_le_S h)).toEquiv
  rw [ctxConjHomS_ker h, h2, hS] at h1
  have hpos : 0 < Nat.card (twoCore t) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (by ring))

theorem ctxConjHomS_inner (h : Ctx0 t L S x₁ x₂ lam rho) {w : ↥L} :
    MulAut.conj w ∈ (ctxConjHomS h).range ↔ (w : G) ∈ wreathGrp x₁ x₂ lam := by
  constructor
  · rintro ⟨s, hs⟩
    have hs' : ctxConjHom h.hyp ⟨(s : G), h.le_invCent s.2⟩ =
        ctxConjHom h.hyp ⟨(w : G), L_le_invCent h.hyp w.2⟩ := by
      rw [ctxConjHom_coe]
      exact hs
    have hp := (ctxConjHom_eq_iff h.hyp _ _).mp hs'
    have hwS : (w : G) ∈ S := by
      have hw : (w : G) = (s : G) * ((s : G)⁻¹ * (w : G)) := by group
      rw [hw]
      exact S.mul_mem s.2 (twoCore_le_S h hp)
    rw [← h.inf_eq]
    exact ⟨hwS, w.2⟩
  · intro hw
    refine ⟨⟨(w : G), wreathGrp_le_S h hw⟩, ?_⟩
    rw [ctxConjHomS_eq]
    exact ctxConjHom_coe h.hyp w

theorem S_eq_of_mem (h : Ctx0 t L S x₁ x₂ lam rho)
    (hidx : (twoCore t ⊔ wreathGrp x₁ x₂ lam).relIndex S = 2) {tau : G} (hτS : tau ∈ S)
    (hτ : tau ∉ twoCore t ⊔ L) : S = twoCore t ⊔ m12Grp x₁ x₂ lam tau := by
  obtain ⟨hx₁L, hx₂L, hlamL⟩ := generators_mem_L h
  have hwS := wreathGrp_le_S h
  have hgen : ∀ g ∈ ({x₁, x₂, lam} : Set G), g ∈ S := fun g hg =>
    hwS (Subgroup.subset_closure hg)
  have hm12S : m12Grp x₁ x₂ lam tau ≤ S := by
    refine (Subgroup.closure_le (K := S)).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg | hg
    · exact hgen g (by simp [hg])
    · exact hgen g (by simp [hg])
    · exact hgen g (by simp [hg])
    · rw [hg]
      exact hτS
  have hXS : twoCore t ⊔ m12Grp x₁ x₂ lam tau ≤ S := sup_le (twoCore_le_S h) hm12S
  have hwm : wreathGrp x₁ x₂ lam ≤ m12Grp x₁ x₂ lam tau := by
    apply Subgroup.closure_mono
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    tauto
  have hAX : twoCore t ⊔ wreathGrp x₁ x₂ lam ≤ twoCore t ⊔ m12Grp x₁ x₂ lam tau :=
    sup_le_sup_left hwm _
  have hτX : tau ∈ twoCore t ⊔ m12Grp x₁ x₂ lam tau :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hAL : twoCore t ⊔ wreathGrp x₁ x₂ lam ≤ twoCore t ⊔ L :=
    sup_le_sup_left (wreathGrp_le_L_ctx0 h) _
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hAX hXS
  rw [hidx] at hmul
  have hne1 : (twoCore t ⊔ wreathGrp x₁ x₂ lam).relIndex
      (twoCore t ⊔ m12Grp x₁ x₂ lam tau) ≠ 1 := fun h1 =>
    hτ (hAL (Subgroup.relIndex_eq_one.mp h1 hτX))
  have hdvd : (twoCore t ⊔ wreathGrp x₁ x₂ lam).relIndex
      (twoCore t ⊔ m12Grp x₁ x₂ lam tau) ∣ 2 := ⟨_, hmul.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact absurd h1 hne1
  · rw [h2] at hmul
    have hX1 : (twoCore t ⊔ m12Grp x₁ x₂ lam tau).relIndex S = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hX1) hXS

end Sylow

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
