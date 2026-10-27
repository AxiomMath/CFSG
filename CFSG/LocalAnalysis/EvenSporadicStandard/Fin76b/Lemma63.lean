module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.EData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Fusion

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

variable {G : Type*} [Group G] {A : Subgroup G} {z t : G} {T₀ E : Subgroup G}

@[expose] noncomputable def prodSupEquiv {A B : Subgroup G} (hAB : B ≤ centralizer (A : Set G))
    (hd : Disjoint A B) : A × B ≃* (A ⊔ B : Subgroup G) :=
  have hcomm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b =>
    mem_centralizer_iff.1 (hAB b.2) a a.2
  have hinj : Function.Injective (A.subtype.noncommCoprod B.subtype hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    exact ⟨A.subtype_injective, B.subtype_injective, by simpa only [range_subtype] using hd⟩
  (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]))

theorem prodSupEquiv_apply {A B : Subgroup G} (hAB : B ≤ centralizer (A : Set G))
    (hd : Disjoint A B) (a : A) (b : B) :
    ((prodSupEquiv hAB hd (a, b) : (A ⊔ B : Subgroup G)) : G) = a * b := rfl

namespace InnerConfig

variable (h : InnerConfig G A z t T₀)

include h in
theorem comm_mem_T₀ {p q : G} (hp : p ∈ T₀ ⊔ zpowers z) (hq : q ∈ T₀ ⊔ zpowers z) :
    p * q * p⁻¹ * q⁻¹ ∈ T₀ := by
  have hzc : ∀ y ∈ T₀ ⊔ zpowers z, z * y * z⁻¹ = y := fun y hy => by
    rw [← h.z_central_T y hy]; group
  obtain ⟨s, hs, hp'⟩ := (h.mem_T_iff).1 hp
  obtain ⟨s', hs', hq'⟩ := (h.mem_T_iff).1 hq
  have hss : s * s' * s⁻¹ * s'⁻¹ ∈ T₀ :=
    mul_mem (mul_mem (mul_mem hs hs') (inv_mem hs)) (inv_mem hs')
  rcases hp' with hp' | hp' <;> rcases hq' with hq' | hq' <;> rw [hp', hq']
  · exact hss
  · have : s * (s' * z) * s⁻¹ * (s' * z)⁻¹ = s * s' * (z * s⁻¹ * z⁻¹) * s'⁻¹ := by group
    rw [this, hzc _ (mem_sup_left (inv_mem hs))]
    exact hss
  · have : s * z * s' * (s * z)⁻¹ * s'⁻¹ = s * (z * s' * z⁻¹) * s⁻¹ * s'⁻¹ := by group
    rw [this, hzc _ (mem_sup_left hs')]
    exact hss
  · have h1 : s * z * (s' * z) * (s * z)⁻¹ * (s' * z)⁻¹ =
        s * (z * (s' * z) * z⁻¹) * s⁻¹ * (s' * z)⁻¹ := by group
    have h2 : z * (s' * z) * z⁻¹ = s' * z := hzc _ (mul_mem (mem_sup_left hs') (z_mem_T T₀ z))
    rw [h1, h2]
    have h3 : s * (s' * z) * s⁻¹ * (s' * z)⁻¹ = s * s' * (z * s⁻¹ * z⁻¹) * s'⁻¹ := by group
    rw [h3, hzc _ (mem_sup_left (inv_mem hs))]
    exact hss

end InnerConfig

namespace EConfig

variable {h : InnerConfig G A z t T₀}

theorem le_sup_of_equiv (h : InnerConfig G A z t T₀) (hE : EConfig A T₀ E t) {P : Subgroup G}
    (hP : P ≤ T₀ ⊔ zpowers z) (hiso : Nonempty (E ≃* P)) : P ≤ E ⊔ zpowers z := by
  obtain ⟨φ⟩ := hiso
  let ψ : E →* G := P.subtype.comp φ.toMonoidHom
  have hψ : Function.Injective ψ := P.subtype_injective.comp φ.injective
  have hψT : ∀ e : E, ψ e ∈ T₀ ⊔ zpowers z := fun e => hP (φ e).2
  have hzP : z ∉ P := by
    intro hz
    have hεz : ψ (φ.symm ⟨z, hz⟩) = z := by simp [ψ]
    set ε : E := φ.symm ⟨z, hz⟩ with hε
    have hεc : ∀ f ∈ E, f * (ε : G) = (ε : G) * f := by
      intro f hf
      have h1 : ψ ⟨f, hf⟩ * ψ ε = ψ ε * ψ ⟨f, hf⟩ := by
        rw [hεz]; exact h.z_central_T _ (hψT _)
      have h2 : (⟨f, hf⟩ : E) * ε = ε * ⟨f, hf⟩ := hψ (by rw [map_mul, map_mul]; exact h1)
      exact congrArg Subtype.val h2
    rcases hE.center ε ε.2 hεc with h1 | h1
    · have : ε = 1 := Subtype.ext h1
      rw [this, map_one] at hεz
      exact h.z_ne hεz.symm
    · have hεt : ε = ⟨t, hE.t_mem⟩ := Subtype.ext h1
      rw [hεt] at hεz
      obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := hE.nonab
      apply hne
      have hcomm : ∀ a b : E, ψ a * ψ b = ψ b * ψ a := by
        intro a b
        have hmem : ψ a * ψ b * (ψ a)⁻¹ * (ψ b)⁻¹ ∈ T₀ := h.comm_mem_T₀ (hψT _) (hψT _)
        have hval : ψ a * ψ b * (ψ a)⁻¹ * (ψ b)⁻¹ = ψ (a * b * a⁻¹ * b⁻¹) := by
          simp [map_mul, map_inv]
        have hcl : ψ (a * b * a⁻¹ * b⁻¹) = 1 := by
          rcases hE.comm a a.2 b b.2 with h1 | h1
          · have : a * b * a⁻¹ * b⁻¹ = 1 := Subtype.ext h1
            rw [this, map_one]
          · exfalso
            have : a * b * a⁻¹ * b⁻¹ = ⟨t, hE.t_mem⟩ := Subtype.ext h1
            rw [hval, this, hεz] at hmem
            exact h.z_not_mem_T₀ hmem
        have h5 : ψ a * ψ b * (ψ a)⁻¹ * (ψ b)⁻¹ = 1 := by rw [hval]; exact hcl
        calc ψ a * ψ b = (ψ a * ψ b * (ψ a)⁻¹ * (ψ b)⁻¹) * (ψ b * ψ a) := by group
          _ = ψ b * ψ a := by rw [h5, one_mul]
      have h4 : (⟨e₁, he₁⟩ : E) * ⟨e₂, he₂⟩ = ⟨e₂, he₂⟩ * ⟨e₁, he₁⟩ :=
        hψ (by rw [map_mul, map_mul]; exact hcomm _ _)
      exact congrArg Subtype.val h4
  let e := prodSupEquiv h.zpowers_le_centralizer h.T₀_disjoint
  let π : ↥(T₀ ⊔ zpowers z) →* ↥T₀ := (MonoidHom.fst _ _).comp e.symm.toMonoidHom
  have hpi : ∀ x : ↥(T₀ ⊔ zpowers z), ∃ w ∈ zpowers z, (x : G) = (π x : G) * w := by
    intro x
    refine ⟨((e.symm x).2 : G), (e.symm x).2.2, ?_⟩
    have h2 := congrArg Subtype.val (e.apply_symm_apply x)
    rw [← h2]
    exact (prodSupEquiv_apply h.zpowers_le_centralizer h.T₀_disjoint _ _).symm
  have hπP : Function.Injective
      (π.comp (P.subgroupOf (T₀ ⊔ zpowers z)).subtype : ↥(P.subgroupOf (T₀ ⊔ zpowers z)) →* _) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨w, hw, hxw⟩ := hpi x.1
    have hx1 : (π x.1 : G) = 1 := congrArg Subtype.val hx
    rw [hx1, one_mul] at hxw
    have hxP : (x.1 : G) ∈ P := mem_subgroupOf.1 x.2
    rcases mem_zpowers_sq_eq_one h.z_sq hw with hw1 | hw1
    · exact Subtype.ext (Subtype.ext (by rw [hxw, hw1]; rfl))
    · exact absurd (by rw [hxw, hw1] at hxP; exact hxP) hzP
  set πP : ↥(P.subgroupOf (T₀ ⊔ zpowers z)) →* ↥T₀ :=
    π.comp (P.subgroupOf (T₀ ⊔ zpowers z)).subtype with hπPdef
  let Q : Subgroup G := πP.range.map T₀.subtype
  have hQle : Q ≤ T₀ := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have eQ : E ≃* Q :=
    ((φ.trans (subgroupOfEquivOfLe hP).symm).trans (MonoidHom.ofInjective hπP)).trans
      (πP.range.equivMapOfInjective T₀.subtype T₀.subtype_injective)
  have hQE : Q = E := hE.unique Q hQle ⟨eQ⟩
  intro p hp
  have hpT : p ∈ T₀ ⊔ zpowers z := hP hp
  obtain ⟨w, hw, hpw⟩ := hpi ⟨p, hpT⟩
  have hπ : (π ⟨p, hpT⟩ : G) ∈ Q :=
    ⟨π ⟨p, hpT⟩, ⟨⟨⟨p, hpT⟩, mem_subgroupOf.2 hp⟩, rfl⟩, rfl⟩
  rw [hQE] at hπ
  have hpw' : p = (π ⟨p, hpT⟩ : G) * w := hpw
  rw [hpw']
  exact mul_mem_sup hπ hw

theorem mem_of_conj_t (h : InnerConfig G A z t T₀) (hE : EConfig A T₀ E t)
    (hzt : ∃ x : G, x * z * x⁻¹ = z * t) {w : G} (hw : w ∈ E ⊔ zpowers z)
    (hconj : ∃ g : G, g * t * g⁻¹ = w) : w ∈ E := by
  obtain ⟨x, hx⟩ := hzt
  obtain ⟨g, hg⟩ := hconj
  have hzE : zpowers z ≤ centralizer (E : Set G) :=
    h.zpowers_le_centralizer.trans (centralizer_le hE.le)
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_centralizer hzE hw
  have haz : a * z = z * a := h.z_comm_of_mem_A (h.T₀_le (hE.le ha))
  rcases mem_zpowers_sq_eq_one h.z_sq hb with hb1 | hb1
  · rw [hab, hb1, mul_one]; exact ha
  · rw [hb1] at hab
    subst hab
    exfalso
    have hsq : a * a = 1 := by
      have h1 : (a * z) * (a * z) = 1 := by
        rw [← hg]
        calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
          _ = 1 := by rw [h.t_sq]; group
      calc a * a = a * (z * z) * a := by rw [h.z_sq, mul_one]
        _ = a * z * (z * a) := by group
        _ = a * z * (a * z) := by rw [← haz]
        _ = 1 := h1
    by_cases ha1 : a = 1
    · subst ha1
      exact h.conj_t_ne_z g (by rw [hg, one_mul])
    · obtain ⟨c, hcA, hc⟩ := hE.conj a ha hsq ha1
      have hcz : c * z = z * c := h.z_comm_of_mem_A hcA
      have hw' : a * z = (c * x) * z * (c * x)⁻¹ := by
        calc a * z = c * t * c⁻¹ * z := by rw [hc]
          _ = c * (t * z) * c⁻¹ := by
            have : c⁻¹ * z = z * c⁻¹ := by
              calc c⁻¹ * z = c⁻¹ * (z * c) * c⁻¹ := by group
                _ = c⁻¹ * (c * z) * c⁻¹ := by rw [hcz]
                _ = z * c⁻¹ := by group
            calc c * t * c⁻¹ * z = c * t * (c⁻¹ * z) := by group
              _ = c * t * (z * c⁻¹) := by rw [this]
              _ = c * (t * z) * c⁻¹ := by group
          _ = c * (z * t) * c⁻¹ := by rw [h.t_comm_z]
          _ = c * (x * z * x⁻¹) * c⁻¹ := by rw [hx]
          _ = (c * x) * z * (c * x)⁻¹ := by group
      refine h.conj_t_ne_z ((c * x)⁻¹ * g) ?_
      calc (c * x)⁻¹ * g * t * ((c * x)⁻¹ * g)⁻¹ = (c * x)⁻¹ * (g * t * g⁻¹) * (c * x) := by group
        _ = (c * x)⁻¹ * (a * z) * (c * x) := by rw [hg]
        _ = z := by rw [hw']; group

theorem map_conj_eq_of_le [Finite G] (h : InnerConfig G A z t T₀) (hE : EConfig A T₀ E t)
    (hzt : ∃ x : G, x * z * x⁻¹ = z * t) {g : G}
    (hg : E.map (MulAut.conj g).toMonoidHom ≤ T₀ ⊔ zpowers z) :
    E.map (MulAut.conj g).toMonoidHom = E := by
  set f : G →* G := (MulAut.conj g).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj g).injective
  have hiso : Nonempty (E ≃* E.map f) := ⟨E.equivMapOfInjective f hfinj⟩
  have hle : E.map f ≤ E ⊔ zpowers z := le_sup_of_equiv h hE hg hiso
  have hEle : E.map f ≤ E := by
    conv_lhs => rw [hE.gen]
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨e, ⟨he, he2, he1⟩, rfl⟩
    obtain ⟨c, -, hc⟩ := hE.conj e he he2 he1
    refine mem_of_conj_t h hE hzt (hle ⟨e, he, rfl⟩) ⟨g * c, ?_⟩
    rw [hc]
    simp [f, MulAut.conj_apply]
    group
  refine Subgroup.eq_of_le_of_card_ge hEle ?_
  rw [Nat.card_congr (E.equivMapOfInjective f hfinj).toEquiv]

theorem mem_normalizer_of_mem_normalizer [Finite G] (h : InnerConfig G A z t T₀)
    (hE : EConfig A T₀ E t) (hzt : ∃ x : G, x * z * x⁻¹ = z * t) {y : G}
    (hy : y ∈ normalizer ((T₀ ⊔ zpowers z : Subgroup G) : Set G)) :
    y ∈ normalizer (E : Set G) := by
  have hEy : E.map (MulAut.conj y).toMonoidHom ≤ T₀ ⊔ zpowers z := by
    rintro _ ⟨e, he, rfl⟩
    have heT : e ∈ T₀ ⊔ zpowers z := mem_sup_left (hE.le he)
    exact (mem_normalizer_iff.1 hy e).1 heT
  have heq := map_conj_eq_of_le h hE hzt hEy
  rw [mem_normalizer_iff]
  intro e
  constructor
  · intro he
    have : y * e * y⁻¹ ∈ E.map (MulAut.conj y).toMonoidHom := ⟨e, he, by simp [MulAut.conj_apply]⟩
    rwa [heq] at this
  · intro he
    rw [← heq] at he
    obtain ⟨e', he', hee'⟩ := he
    have : e' = e := by
      have h2 : y * e' * y⁻¹ = y * e * y⁻¹ := by simpa [MulAut.conj_apply] using hee'
      exact mul_left_cancel (mul_right_cancel h2)
    rwa [← this]

end EConfig

end CFSG.EvenSporadicStandard.Fin76b
