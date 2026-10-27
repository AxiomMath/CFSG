module

public import CFSG.Certificates.Kernel.OrbRow.CentGrp

public section

namespace CFSG.KC.OrbRow.CentGrp

open Subgroup

variable {n : ℕ}

@[expose] noncomputable def centP (P : Subgroup (Equiv.Perm (Fin n))) (x : Equiv.Perm (Fin n)) :
    Subgroup (Equiv.Perm (Fin n)) :=
  centralizer {x} ⊓ P

theorem comm_of_mem_centP {P : Subgroup (Equiv.Perm (Fin n))} {x g : Equiv.Perm (Fin n)}
    (hg : g ∈ centP P x) : g * x = x * g :=
  mem_centralizer_singleton_iff.1 hg.1

theorem mem_centP {P : Subgroup (Equiv.Perm (Fin n))} {x g : Equiv.Perm (Fin n)} (hgP : g ∈ P)
    (hg : g * x = x * g) : g ∈ centP P x :=
  ⟨mem_centralizer_singleton_iff.2 hg, hgP⟩

theorem exists_actF {P : Subgroup (Equiv.Perm (Fin n))} {x : Equiv.Perm (Fin n)}
    {F : Fin 5 → Fin n} (hfix : ∀ i, x i = i ↔ i ∈ Set.range F) (g : centP P x) (t : Fin 5) :
    ∃ s, F s = (g : Equiv.Perm (Fin n)) (F t) := by
  have hx : x (F t) = F t := (hfix _).2 ⟨t, rfl⟩
  have hc := comm_of_mem_centP g.2
  have : x ((g : Equiv.Perm (Fin n)) (F t)) = (g : Equiv.Perm (Fin n)) (F t) := by
    have := congrArg (fun σ : Equiv.Perm (Fin n) => σ (F t)) hc
    simp only [Equiv.Perm.mul_apply, hx] at this
    exact this.symm
  exact (hfix _).1 this

@[expose] noncomputable def actFun {P : Subgroup (Equiv.Perm (Fin n))} {x : Equiv.Perm (Fin n)}
    {F : Fin 5 → Fin n} (hfix : ∀ i, x i = i ↔ i ∈ Set.range F) (g : centP P x) : Fin 5 → Fin 5 :=
  fun t => Classical.choose (exists_actF hfix g t)

theorem actFun_spec {P : Subgroup (Equiv.Perm (Fin n))} {x : Equiv.Perm (Fin n)}
    {F : Fin 5 → Fin n} (hfix : ∀ i, x i = i ↔ i ∈ Set.range F) (g : centP P x) (t : Fin 5) :
    F (actFun hfix g t) = (g : Equiv.Perm (Fin n)) (F t) :=
  Classical.choose_spec (exists_actF hfix g t)

theorem actFun_eq {P : Subgroup (Equiv.Perm (Fin n))} {x : Equiv.Perm (Fin n)}
    {F : Fin 5 → Fin n} (hF : Function.Injective F) (hfix : ∀ i, x i = i ↔ i ∈ Set.range F)
    (g : centP P x) {t s : Fin 5} (h : (g : Equiv.Perm (Fin n)) (F t) = F s) :
    actFun hfix g t = s :=
  hF ((actFun_spec hfix g t).trans h)

theorem actFun_bij {P : Subgroup (Equiv.Perm (Fin n))} {x : Equiv.Perm (Fin n)}
    {F : Fin 5 → Fin n} (hF : Function.Injective F) (hfix : ∀ i, x i = i ↔ i ∈ Set.range F)
    (g : centP P x) : Function.Bijective (actFun hfix g) := by
  refine Finite.injective_iff_bijective.1 fun a b hab => ?_
  have h := congrArg F hab
  rw [actFun_spec hfix g a, actFun_spec hfix g b] at h
  exact hF ((g : Equiv.Perm (Fin n)).injective h)

@[expose] noncomputable def actF {P : Subgroup (Equiv.Perm (Fin n))} {x : Equiv.Perm (Fin n)}
    {F : Fin 5 → Fin n} (hF : Function.Injective F) (hfix : ∀ i, x i = i ↔ i ∈ Set.range F) :
    centP P x →* Equiv.Perm (Fin 5) :=
  MonoidHom.mk' (fun g => Equiv.ofBijective _ (actFun_bij hF hfix g)) fun g h => by
    ext t
    simp only [Equiv.ofBijective_apply, Equiv.Perm.mul_apply]
    congr 1
    apply actFun_eq hF hfix
    rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, ← actFun_spec hfix h, ← actFun_spec hfix g]

theorem actF_apply {P : Subgroup (Equiv.Perm (Fin n))} {x : Equiv.Perm (Fin n)}
    {F : Fin 5 → Fin n} (hF : Function.Injective F) (hfix : ∀ i, x i = i ↔ i ∈ Set.range F)
    (g : centP P x) (t : Fin 5) : F (actF hF hfix g t) = (g : Equiv.Perm (Fin n)) (F t) :=
  actFun_spec hfix g t

theorem actF_eq_of {P : Subgroup (Equiv.Perm (Fin n))} {x : Equiv.Perm (Fin n)}
    {F : Fin 5 → Fin n} (hF : Function.Injective F) (hfix : ∀ i, x i = i ↔ i ∈ Set.range F)
    (g : centP P x) (σ : Equiv.Perm (Fin 5)) (h : ∀ t, (g : Equiv.Perm (Fin n)) (F t) = F (σ t)) :
    actF hF hfix g = σ := by
  ext t
  exact congrArg Fin.val (hF ((actF_apply hF hfix g t).trans (h t)))

theorem mem_ker_actF {P : Subgroup (Equiv.Perm (Fin n))} {x : Equiv.Perm (Fin n)}
    {F : Fin 5 → Fin n} (hF : Function.Injective F) (hfix : ∀ i, x i = i ↔ i ∈ Set.range F)
    (g : centP P x) : g ∈ (actF hF hfix).ker ↔ ∀ t, (g : Equiv.Perm (Fin n)) (F t) = F t := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h t
    rw [← actF_apply hF hfix, h]
    rfl
  · intro h
    exact actF_eq_of hF hfix g 1 fun t => h t

theorem caseA_perm {P : Subgroup (Equiv.Perm (Fin n))} {x : Equiv.Perm (Fin n)}
    {F : Fin 5 → Fin n} (hF : Function.Injective F) (hfix : ∀ i, x i = i ↔ i ∈ Set.range F)
    {K : Subgroup (Equiv.Perm (Fin n))} (hKdef : ∀ g, g ∈ K ↔ g ∈ P ∧ ∀ t, g (F t) = F t)
    (hKx : ∀ g ∈ K, g * x = x * g) {Kg : Set (Equiv.Perm (Fin n))} (hKg : K = closure Kg)
    {c1 c2 g0 c5 : Equiv.Perm (Fin n)} (hc1 : c1 ∈ centP P x) (hc2 : c2 ∈ centP P x)
    (hc1F : ∀ t, c1 (F t) = F (c3 t)) (hc2F : ∀ t, c2 (F t) = F (finRotate 5 t))
    (hg0 : g0 ∈ P) (hg0F : ∀ t, g0 (F t) = F (Equiv.swap 0 1 t)) (hg0x : g0 * x ≠ x * g0)
    {R : Subgroup (Equiv.Perm (Fin n))} {Rg : Set (Equiv.Perm (Fin n))} (hRg : R = closure Rg)
    (hRK : R ≤ K) (hnorm : ∀ y ∈ ({c1, c2} ∪ Kg : Set (Equiv.Perm (Fin n))), ∀ r ∈ Rg,
      y * r * y⁻¹ ∈ R)
    (hK : Nat.card K = 2 ^ 5 * 3 ^ 5) (hR : Nat.card R = 3 ^ 5)
    {T : Subgroup (Equiv.Perm (Fin n))} (hTK : T ≤ K) (hT : Nat.card T = 2 ^ 5)
    (hTc : ∀ t ∈ T, t ∈ centralizer (R : Set (Equiv.Perm (Fin n))) → t = 1)
    (hc5 : c5 ∈ centP P x) (hc5o : orderOf c5 = 5)
    (hc5R : c5 ∉ centralizer (R : Set (Equiv.Perm (Fin n)))) :
    (∀ g ∈ centP P x, ∀ r ∈ R, g * r * g⁻¹ ∈ R) ∧
      centralizer (R : Set (Equiv.Perm (Fin n))) ⊓ centP P x ≤ R := by
  set C := centP P x
  set φ := actF hF hfix (P := P)
  have hKC : K ≤ C := fun g hg => mem_centP ((hKdef g).1 hg).1 (hKx g hg)
  have hker : φ.ker = K.subgroupOf C := by
    ext g
    rw [mem_ker_actF, mem_subgroupOf, hKdef]
    exact ⟨fun h => ⟨g.2.2, h⟩, fun h => h.2⟩
  have h1 : c3 ∈ φ.range :=
    ⟨⟨c1, hc1⟩, actF_eq_of hF hfix _ _ hc1F⟩
  have h2 : finRotate 5 ∈ φ.range :=
    ⟨⟨c2, hc2⟩, actF_eq_of hF hfix _ _ hc2F⟩
  have h3 : Equiv.swap 0 1 ∉ φ.range := by
    rintro ⟨g, hg⟩
    have hk : g0⁻¹ * (g : Equiv.Perm (Fin n)) ∈ K := by
      rw [hKdef]
      refine ⟨P.mul_mem (P.inv_mem hg0) g.2.2, fun t => ?_⟩
      rw [Equiv.Perm.mul_apply, ← actF_apply hF hfix, hg, Equiv.Perm.inv_eq_iff_eq, hg0F]
    have hgC : g0 ∈ C := by
      have := C.mul_mem g.2 (C.inv_mem (hKC hk))
      rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
    exact hg0x (comm_of_mem_centP hgC)
  have hrange := range_eq_alt φ h1 h2 h3
  set X : Set (Equiv.Perm (Fin n)) := {c1, c2} ∪ Kg
  have hall : ∀ g ∈ C, g ∈ closure X := by
    have htop := eq_top_of_ker_le φ ((closure X).subgroupOf C) (by
        rw [hker]
        intro g hg
        rw [mem_subgroupOf] at hg ⊢
        rw [hKg] at hg
        exact closure_mono Set.subset_union_right hg) (by
        rw [hrange, ← closure_c3_rot, closure_le]
        rintro _ (rfl | rfl)
        · exact ⟨⟨c1, hc1⟩, mem_subgroupOf.2 (subset_closure (Or.inl (Or.inl rfl))),
            actF_eq_of hF hfix _ _ hc1F⟩
        · exact ⟨⟨c2, hc2⟩, mem_subgroupOf.2 (subset_closure (Or.inl (Or.inr rfl))),
            actF_eq_of hF hfix _ _ hc2F⟩)
    intro g hg
    have : (⟨g, hg⟩ : C) ∈ (closure X).subgroupOf C := by rw [htop]; exact mem_top _
    exact mem_subgroupOf.1 this
  have hN : ∀ g ∈ C, ∀ r ∈ R, g * r * g⁻¹ ∈ R := fun g hg =>
    conj_mem_of_closure hRg hnorm g (hall g hg)
  refine ⟨hN, ?_⟩
  have hRC : R ≤ C := hRK.trans hKC
  have hTC : T ≤ C := hTK.trans hKC
  have hKn : (K.subgroupOf C).Normal := hker ▸ φ.normal_ker
  have hRn : (R.subgroupOf C).Normal := by
    constructor
    intro r hr g
    rw [mem_subgroupOf] at hr ⊢
    exact hN g g.2 r hr
  have hcK : Nat.card (K.subgroupOf C) = 2 ^ 5 * 3 ^ 5 := by
    rw [← hK]
    exact Nat.card_congr (subgroupOfEquivOfLe hKC).toEquiv
  have hcR : Nat.card (R.subgroupOf C) = 3 ^ 5 := by
    rw [← hR]
    exact Nat.card_congr (subgroupOfEquivOfLe hRC).toEquiv
  have hcT : Nat.card (T.subgroupOf C) = 2 ^ 5 := by
    rw [← hT]
    exact Nat.card_congr (subgroupOfEquivOfLe hTC).toEquiv
  have hcent : ∀ g : C, g ∈ centralizer ((R.subgroupOf C : Subgroup C) : Set C) →
      (g : Equiv.Perm (Fin n)) ∈ centralizer (R : Set (Equiv.Perm (Fin n))) := by
    intro g hg
    rw [mem_centralizer_iff] at hg ⊢
    intro r hr
    have := hg ⟨r, hRC hr⟩ (mem_subgroupOf.2 hr)
    exact congrArg Subtype.val this
  have hcent' : ∀ g : C, (g : Equiv.Perm (Fin n)) ∈ centralizer (R : Set (Equiv.Perm (Fin n))) →
      g ∈ centralizer ((R.subgroupOf C : Subgroup C) : Set C) := by
    intro g hg
    rw [mem_centralizer_iff] at hg ⊢
    intro r hr
    exact Subtype.ext (hg r (mem_subgroupOf.1 hr))
  have hres := centralizer_le (H := C) (K.subgroupOf C) (R.subgroupOf C) (T.subgroupOf C)
    (fun r hr => mem_subgroupOf.2 (hRK (mem_subgroupOf.1 hr))) hcK hcR
    (fun t ht => mem_subgroupOf.2 (hTK (mem_subgroupOf.1 ht))) hcT
    (fun t ht htc => Subtype.ext (hTc _ (mem_subgroupOf.1 ht) (hcent t htc))) φ hker hrange
    (c5 := ⟨c5, hc5⟩) (by rw [← Subgroup.orderOf_coe]; exact hc5o)
    (fun h => hc5R (hcent _ h))
  rintro g ⟨hgZ, hgC⟩
  exact mem_subgroupOf.1 (hres (hcent' ⟨g, hgC⟩ hgZ))

end CFSG.KC.OrbRow.CentGrp

end
