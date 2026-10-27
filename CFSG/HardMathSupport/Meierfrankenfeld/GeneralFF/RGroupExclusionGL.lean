module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderBasic
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderDefs

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

open CFSG.RankThree.FFModules

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem glRep_mul_apply (ρ : Representation (ZMod 2) G V) (a b : G) (v : V) :
    ρ (a * b) v = ρ a (ρ b v) := by
  rw [map_mul, Module.End.mul_apply]

theorem glRep_inv_apply (ρ : Representation (ZMod 2) G V) (a : G) (v : V) :
    ρ a⁻¹ (ρ a v) = v := by
  rw [← glRep_mul_apply, inv_mul_cancel, map_one]; rfl

theorem glRep_apply_inv (ρ : Representation (ZMod 2) G V) (a : G) (v : V) :
    ρ a (ρ a⁻¹ v) = v := by
  rw [← glRep_mul_apply, mul_inv_cancel, map_one]; rfl

variable (ρ : Representation (ZMod 2) G V) (H : Subgroup G) (U : Submodule (ZMod 2) V)
  (hU : IsInvariant ρ H U)

@[expose] noncomputable def resLinEquiv (h : H) : U ≃ₗ[ZMod 2] U where
  toFun u := ⟨ρ h u, hU h h.2 u u.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)
  invFun u := ⟨ρ (h : G)⁻¹ u, hU _ (H.inv_mem h.2) u u.2⟩
  left_inv _ := Subtype.ext (glRep_inv_apply ρ _ _)
  right_inv _ := Subtype.ext (glRep_apply_inv ρ _ _)

@[expose] noncomputable def resGL : H →* (U ≃ₗ[ZMod 2] U) where
  toFun := resLinEquiv ρ H U hU
  map_one' := by
    ext u
    change ρ ((1 : H) : G) (u : V) = u
    rw [Subgroup.coe_one, map_one]; rfl
  map_mul' a b := by
    ext u
    exact glRep_mul_apply ρ _ _ _

@[expose] noncomputable def imgGL (B : Subgroup G) : Subgroup (U ≃ₗ[ZMod 2] U) :=
  (B.subgroupOf H).map (resGL ρ H U hU)

variable {ρ H U hU}

theorem mem_imgGL {B : Subgroup G} {x : U ≃ₗ[ZMod 2] U} :
    x ∈ imgGL ρ H U hU B ↔ ∃ b : H, (b : G) ∈ B ∧ resGL ρ H U hU b = x := by
  simp [imgGL, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem resGL_mem_imgGL {B : Subgroup G} {b : G} (hb : b ∈ B) (hbH : b ∈ H) :
    resGL ρ H U hU ⟨b, hbH⟩ ∈ imgGL ρ H U hU B :=
  mem_imgGL.2 ⟨⟨b, hbH⟩, hb, rfl⟩

theorem imgGL_mono {B B' : Subgroup G} (h : B ≤ B') :
    imgGL ρ H U hU B ≤ imgGL ρ H U hU B' :=
  Subgroup.map_mono fun _ hx => h hx

theorem resGL_eq_one_iff (h : H) :
    resGL ρ H U hU h = 1 ↔ ∀ u ∈ U, ρ h u = u := by
  constructor
  · intro h1 u hu
    exact congrArg (fun x : U => (x : V)) (LinearEquiv.congr_fun h1 ⟨u, hu⟩)
  · intro h1
    exact LinearEquiv.ext fun u => Subtype.ext (h1 _ u.2)

theorem mem_fixSub_imgGL {B : Subgroup G} (hB : B ≤ H) {u : U} :
    u ∈ CFSG.QuasithinUnique.Setup.Offender.fixSub (MonoidHom.id (U ≃ₗ[ZMod 2] U))
        (imgGL ρ H U hU B) ↔ ∀ b ∈ B, ρ b (u : V) = (u : V) := by
  rw [CFSG.QuasithinUnique.Setup.Offender.mem_fixSub]
  constructor
  · intro h b hb
    exact congrArg (fun x : U => (x : V)) (h _ (resGL_mem_imgGL hb (hB hb)))
  · intro h x hx
    obtain ⟨b, hbB, rfl⟩ := mem_imgGL.1 hx
    exact Subtype.ext (h b hbB)

noncomputable def fixSubEquiv {B : Subgroup G} (hB : B ≤ H) :
    ↥(CFSG.QuasithinUnique.Setup.Offender.fixSub (MonoidHom.id (U ≃ₗ[ZMod 2] U))
        (imgGL ρ H U hU B)) ≃ ↥(fixOn ρ B U) where
  toFun v := ⟨(v.1 : V), v.1.2, fun b hb => (mem_fixSub_imgGL hB).1 v.2 b hb⟩
  invFun w := ⟨⟨w.1, w.2.1⟩, (mem_fixSub_imgGL hB).2 fun b hb => w.2.2 b hb⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_fixSub_imgGL {B : Subgroup G} (hB : B ≤ H) :
    Nat.card (CFSG.QuasithinUnique.Setup.Offender.fixSub (MonoidHom.id (U ≃ₗ[ZMod 2] U))
        (imgGL ρ H U hU B)) = Nat.card (fixOn ρ B U) :=
  Nat.card_congr (fixSubEquiv hB)

noncomputable def resGLOn {B : Subgroup G} (hB : B ≤ H) : B →* (U ≃ₗ[ZMod 2] U) :=
  (resGL ρ H U hU).comp (Subgroup.inclusion hB)

theorem range_resGLOn {B : Subgroup G} (hB : B ≤ H) :
    (resGLOn (hU := hU) hB).range = imgGL ρ H U hU B := by
  ext x
  rw [MonoidHom.mem_range, mem_imgGL]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨⟨b, hB b.2⟩, b.2, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, rfl⟩

noncomputable def kerGLEquiv {B : Subgroup G} (hB : B ≤ H) :
    ↥(resGLOn (hU := hU) hB).ker ≃ ↥(cenOn ρ B U) where
  toFun b := ⟨b.1.1, b.1.2, (resGL_eq_one_iff (hU := hU) _).1 b.2⟩
  invFun c := ⟨⟨c.1, c.2.1⟩, (resGL_eq_one_iff (hU := hU) ⟨c.1, hB c.2.1⟩).2 c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_imgGL_mul_card_cenOn {B : Subgroup G} (hB : B ≤ H) :
    Nat.card (imgGL ρ H U hU B) * Nat.card (cenOn ρ B U) = Nat.card B := by
  rw [← range_resGLOn (hU := hU) hB, ← Nat.card_congr (kerGLEquiv (hU := hU) hB), mul_comm]
  exact Subgroup.card_ker_mul_card_range _

theorem weight_imgGL {B : Subgroup G} (hB : B ≤ H) :
    CFSG.QuasithinUnique.Setup.Offender.weight (MonoidHom.id (U ≃ₗ[ZMod 2] U))
        (imgGL ρ H U hU B) = Nat.card (imgGL ρ H U hU B) * Nat.card (fixOn ρ B U) := by
  rw [CFSG.QuasithinUnique.Setup.Offender.weight, card_fixSub_imgGL hB]

theorem imgGL_eq_bot_iff {B : Subgroup G} (hB : B ≤ H) :
    imgGL ρ H U hU B = ⊥ ↔ B ≤ cenOn ρ B U := by
  rw [← range_resGLOn (hU := hU) hB, MonoidHom.range_eq_bot_iff]
  constructor
  · intro h b hb
    have := congrArg (fun f : B →* _ => f ⟨b, hb⟩) h
    exact ⟨hb, (resGL_eq_one_iff (hU := hU) (⟨b, hB hb⟩ : H)).1 this⟩
  · intro h
    refine MonoidHom.ext fun ⟨b, hb⟩ => ?_
    exact (resGL_eq_one_iff (hU := hU) (⟨b, hB hb⟩ : H)).2 (h hb).2

theorem exists_imgGL_eq {B : Subgroup G} (hB : B ≤ H) {B₂ : Subgroup (U ≃ₗ[ZMod 2] U)}
    (h : B₂ ≤ imgGL ρ H U hU B) :
    ∃ B' : Subgroup G, B' ≤ B ∧ cenOn ρ B U ≤ B' ∧ imgGL ρ H U hU B' = B₂ := by
  let B' : Subgroup G := B ⊓ (B₂.comap (resGL ρ H U hU)).map H.subtype
  refine ⟨B', inf_le_left, fun g hg => ⟨hg.1, ?_⟩, ?_⟩
  · refine ⟨⟨g, hB hg.1⟩, ?_, rfl⟩
    show resGL ρ H U hU ⟨g, hB hg.1⟩ ∈ B₂
    rw [(resGL_eq_one_iff (hU := hU) _).2 hg.2]
    exact B₂.one_mem
  · ext x
    rw [mem_imgGL]
    constructor
    · rintro ⟨b, ⟨hbB, c, hc, hcb⟩, rfl⟩
      have : c = b := Subtype.ext hcb
      subst this
      exact hc
    · intro hx
      obtain ⟨b, hbB, rfl⟩ := mem_imgGL.1 (h hx)
      exact ⟨b, ⟨hbB, b, hx, rfl⟩, rfl⟩

theorem imgGL_conj_mem {K : Subgroup G} (hK : H ≤ Subgroup.normalizer (K : Set G))
    {x y : U ≃ₗ[ZMod 2] U} (hx : x ∈ imgGL ρ H U hU H) (hy : y ∈ imgGL ρ H U hU K) :
    x * y * x⁻¹ ∈ imgGL ρ H U hU K := by
  obtain ⟨a, -, rfl⟩ := mem_imgGL.1 hx
  obtain ⟨k, hkK, rfl⟩ := mem_imgGL.1 hy
  refine mem_imgGL.2 ⟨a * k * a⁻¹, ?_, by simp⟩
  exact (Subgroup.mem_normalizer_iff.1 (hK a.2) k).1 hkK

theorem imgGL_le_normalizer {K : Subgroup G} (hK : H ≤ Subgroup.normalizer (K : Set G)) :
    imgGL ρ H U hU H ≤ Subgroup.normalizer (imgGL ρ H U hU K : Set (U ≃ₗ[ZMod 2] U)) := by
  intro x hx
  refine Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => imgGL_conj_mem hK hx hy, fun hy => ?_⟩
  have := imgGL_conj_mem hK ((imgGL ρ H U hU H).inv_mem hx) hy
  simpa [mul_assoc] using this

theorem isElementaryAbelian_of_le {A B : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 A)
    (hBA : B ≤ A) : CFSG.IsElementaryAbelian 2 B := CFSG.IsElementaryAbelian.of_le hA hBA

theorem isElementaryAbelian_imgGL {B A : Subgroup G} (hB : B ≤ H) (hA : CFSG.IsElementaryAbelian 2 A)
    (hBA : B ≤ A) : CFSG.IsElementaryAbelian 2 (imgGL ρ H U hU B) := by
  have : CFSG.IsElementaryAbelian 2 B := isElementaryAbelian_of_le hA hBA
  have : CFSG.IsElementaryAbelian 2 (B.subgroupOf H) := CFSG.IsElementaryAbelian.subgroupOf hB
  exact CFSG.IsElementaryAbelian.map _

end CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
