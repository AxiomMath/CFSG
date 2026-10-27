module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.EData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCOuter

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

namespace OuterConfig

variable {G : Type} [Group G] {A : Subgroup G} {z t : G} {T : Subgroup G}
  (h : OuterConfig G A z t T)

include h in
theorem comm_mem [Finite G] {p q : G} (hp : p ∈ centralizer ({z} : Set G))
    (hq : q ∈ centralizer ({z} : Set G)) : p * q * p⁻¹ * q⁻¹ ∈ A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzH : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hAH : A ≤ centralizer ({z} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.2 (h.z_comm_of_mem_A ha)
  have hNn : (A.subgroupOf (centralizer ({z} : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hAH).2 h.cent_le
  have hrel : A.relIndex (centralizer ({z} : Set G)) = 2 * 2 := by
    rw [← Subgroup.relIndex_mul_relIndex A (A ⊔ zpowers z) (centralizer ({z} : Set G))
      le_sup_left (sup_le hAH (zpowers_le.2 hzH)), h.A_relIndex_sup, h.index_two]
  have hcard : Nat.card (centralizer ({z} : Set G) ⧸ A.subgroupOf (centralizer ({z} : Set G))) =
      2 ^ 2 := by
    have : Nat.card (centralizer ({z} : Set G) ⧸ A.subgroupOf (centralizer ({z} : Set G))) =
        A.relIndex (centralizer ({z} : Set G)) := rfl
    rw [this, hrel]
    norm_num
  let _ : CommGroup (centralizer ({z} : Set G) ⧸ A.subgroupOf (centralizer ({z} : Set G))) :=
    IsPGroup.commGroupOfCardEqPrimeSq hcard
  let ψ : centralizer ({z} : Set G) →*
      (centralizer ({z} : Set G) ⧸ A.subgroupOf (centralizer ({z} : Set G))) :=
    QuotientGroup.mk' (A.subgroupOf (centralizer ({z} : Set G)))
  have h1 : ψ (⟨p, hp⟩ * ⟨q, hq⟩ * ⟨p, hp⟩⁻¹ * ⟨q, hq⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    generalize ψ ⟨p, hp⟩ = a
    generalize ψ ⟨q, hq⟩ = b
    rw [mul_comm a b]
    group
  have h2 := (QuotientGroup.eq_one_iff _).1 h1
  exact mem_subgroupOf.1 h2

end OuterConfig

structure OuterE (G : Type*) [Group G] (L : Subgroup G) (z t : G) (T E : Subgroup G) : Prop where
  cfg : OuterConfig G L z t T
  econfig : EConfig L (T ⊓ L) E t
  U : ∀ P : Subgroup G, P ≤ T → z ∉ P → Nonempty (↥E ≃* ↥P) → P ≤ E ⊔ zpowers z
  C : ∀ s ∈ T, (∀ e ∈ E, s * e = e * s) → s = 1 ∨ s = z ∨ s = t ∨ s = z * t

namespace OuterE

variable {G : Type} [Group G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  (h : OuterE G L z t T E)

include h in
theorem E_le_L : E ≤ L := h.econfig.le.trans inf_le_right

include h in
theorem E_le_T : E ≤ T := h.econfig.le.trans inf_le_left

include h in
theorem zpowers_le_cent_E : zpowers z ≤ centralizer (E : Set G) :=
  zpowers_le.2 (centralizer_le h.E_le_L h.cfg.z_cent)

include h in
theorem z_not_mem_of_equiv [Finite G] {P : Subgroup G} (hP : P ≤ T)
    (hiso : Nonempty (↥E ≃* ↥P)) : z ∉ P := by
  intro hz
  obtain ⟨φ⟩ := hiso
  have hH : ∀ y ∈ T, y ∈ centralizer ({z} : Set G) := fun y hy => h.cfg.T_le hy
  let ψ : ↥E →* G := P.subtype.comp φ.toMonoidHom
  have hψ : Function.Injective ψ := P.subtype_injective.comp φ.injective
  have hψT : ∀ e : ↥E, ψ e ∈ T := fun e => hP (φ e).2
  have hεz : ψ (φ.symm ⟨z, hz⟩) = z := by simp [ψ]
  set ε : ↥E := φ.symm ⟨z, hz⟩ with hε
  have hεc : ∀ f ∈ E, f * (ε : G) = (ε : G) * f := by
    intro f hf
    have h1 : ψ ⟨f, hf⟩ * ψ ε = ψ ε * ψ ⟨f, hf⟩ := by
      rw [hεz]; exact h.cfg.z_central_T _ (hψT _)
    have h2 : (⟨f, hf⟩ : ↥E) * ε = ε * ⟨f, hf⟩ := hψ (by rw [map_mul, map_mul]; exact h1)
    exact congrArg Subtype.val h2
  rcases h.econfig.center ε ε.2 hεc with h1 | h1
  · have : ε = 1 := Subtype.ext h1
    rw [this, map_one] at hεz
    exact h.cfg.z_ne hεz.symm
  · have hεt : ε = ⟨t, h.econfig.t_mem⟩ := Subtype.ext h1
    rw [hεt] at hεz
    obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := h.econfig.nonab
    apply hne
    have hcomm : ∀ a b : ↥E, ψ a * ψ b = ψ b * ψ a := by
      intro a b
      have hmem : ψ a * ψ b * (ψ a)⁻¹ * (ψ b)⁻¹ ∈ L :=
        h.cfg.comm_mem (hH _ (hψT a)) (hH _ (hψT b))
      have hval : ψ a * ψ b * (ψ a)⁻¹ * (ψ b)⁻¹ = ψ (a * b * a⁻¹ * b⁻¹) := by
        simp [map_mul, map_inv]
      have hcl : ψ (a * b * a⁻¹ * b⁻¹) = 1 := by
        rcases h.econfig.comm a a.2 b b.2 with h1 | h1
        · have : a * b * a⁻¹ * b⁻¹ = 1 := Subtype.ext h1
          rw [this, map_one]
        · exfalso
          have : a * b * a⁻¹ * b⁻¹ = ⟨t, h.econfig.t_mem⟩ := Subtype.ext h1
          rw [hval, this, hεz] at hmem
          exact h.cfg.z_not_mem_A hmem
      have h5 : ψ a * ψ b * (ψ a)⁻¹ * (ψ b)⁻¹ = 1 := by rw [hval]; exact hcl
      calc ψ a * ψ b = (ψ a * ψ b * (ψ a)⁻¹ * (ψ b)⁻¹) * (ψ b * ψ a) := by group
        _ = ψ b * ψ a := by rw [h5, one_mul]
    have h4 : (⟨e₁, he₁⟩ : ↥E) * ⟨e₂, he₂⟩ = ⟨e₂, he₂⟩ * ⟨e₁, he₁⟩ :=
      hψ (by rw [map_mul, map_mul]; exact hcomm _ _)
    exact congrArg Subtype.val h4

include h in
theorem le_sup_of_equiv [Finite G] {P : Subgroup G} (hP : P ≤ T) (hiso : Nonempty (↥E ≃* ↥P)) :
    P ≤ E ⊔ zpowers z :=
  h.U P hP (h.z_not_mem_of_equiv hP hiso) hiso

include h in
theorem mem_of_conj_t (hzt : ∃ x : G, x * z * x⁻¹ = z * t) {w : G} (hw : w ∈ E ⊔ zpowers z)
    (hconj : ∃ g : G, g * t * g⁻¹ = w) : w ∈ E := by
  obtain ⟨x, hx⟩ := hzt
  obtain ⟨g, hg⟩ := hconj
  obtain ⟨a, ha, b, hb, hab⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer h.zpowers_le_cent_E hw
  have haz : a * z = z * a := h.cfg.z_comm_of_mem_A (h.E_le_L ha)
  rcases mem_zpowers_sq_eq_one h.cfg.z_sq hb with hb1 | hb1
  · rw [hab, hb1, mul_one]; exact ha
  · rw [hb1] at hab
    subst hab
    exfalso
    have hsq : a * a = 1 := by
      have h1 : (a * z) * (a * z) = 1 := by
        rw [← hg]
        calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
          _ = 1 := by rw [h.cfg.t_sq]; group
      calc a * a = a * (z * z) * a := by rw [h.cfg.z_sq, mul_one]
        _ = a * z * (z * a) := by group
        _ = a * z * (a * z) := by rw [← haz]
        _ = 1 := h1
    by_cases ha1 : a = 1
    · subst ha1
      exact h.cfg.conj_t_ne_z g (by rw [hg, one_mul])
    · obtain ⟨c, hcA, hc⟩ := h.econfig.conj a ha hsq ha1
      have hcz : c * z = z * c := h.cfg.z_comm_of_mem_A hcA
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
          _ = c * (z * t) * c⁻¹ := by rw [h.cfg.t_comm_z]
          _ = c * (x * z * x⁻¹) * c⁻¹ := by rw [hx]
          _ = (c * x) * z * (c * x)⁻¹ := by group
      refine h.cfg.conj_t_ne_z ((c * x)⁻¹ * g) ?_
      calc (c * x)⁻¹ * g * t * ((c * x)⁻¹ * g)⁻¹ = (c * x)⁻¹ * (g * t * g⁻¹) * (c * x) := by group
        _ = (c * x)⁻¹ * (a * z) * (c * x) := by rw [hg]
        _ = z := by rw [hw']; group

include h in
theorem map_conj_eq_of_le [Finite G] (hzt : ∃ x : G, x * z * x⁻¹ = z * t) {g : G}
    (hg : E.map (MulAut.conj g).toMonoidHom ≤ T) :
    E.map (MulAut.conj g).toMonoidHom = E := by
  set f : G →* G := (MulAut.conj g).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj g).injective
  have hiso : Nonempty (↥E ≃* ↥(E.map f)) := ⟨E.equivMapOfInjective f hfinj⟩
  have hle : E.map f ≤ E ⊔ zpowers z := h.le_sup_of_equiv hg hiso
  have hEle : E.map f ≤ E := by
    conv_lhs => rw [h.econfig.gen]
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨e, ⟨he, he2, he1⟩, rfl⟩
    obtain ⟨c, -, hc⟩ := h.econfig.conj e he he2 he1
    refine h.mem_of_conj_t hzt (hle ⟨e, he, rfl⟩) ⟨g * c, ?_⟩
    rw [hc]
    simp [f, MulAut.conj_apply]
    group
  refine Subgroup.eq_of_le_of_card_ge hEle ?_
  rw [Nat.card_congr (E.equivMapOfInjective f hfinj).toEquiv]

include h in
theorem mem_normalizer_of_mem_normalizer [Finite G] (hzt : ∃ x : G, x * z * x⁻¹ = z * t) {y : G}
    (hy : y ∈ normalizer (T : Set G)) : y ∈ normalizer (E : Set G) := by
  have hEy : E.map (MulAut.conj y).toMonoidHom ≤ T := by
    rintro _ ⟨e, he, rfl⟩
    exact (mem_normalizer_iff.1 hy e).1 (h.E_le_T he)
  have heq := h.map_conj_eq_of_le hzt hEy
  rw [mem_normalizer_iff]
  intro e
  constructor
  · intro he
    have : y * e * y⁻¹ ∈ E.map (MulAut.conj y).toMonoidHom :=
      ⟨e, he, by simp [MulAut.conj_apply]⟩
    rwa [heq] at this
  · intro he
    rw [← heq] at he
    obtain ⟨e', he', hee'⟩ := he
    have : e' = e := by
      have h2 : y * e' * y⁻¹ = y * e * y⁻¹ := by simpa [MulAut.conj_apply] using hee'
      exact mul_left_cancel (mul_right_cancel h2)
    rwa [← this]

end OuterE

end CFSG.EvenSporadicStandard.Fin76b
