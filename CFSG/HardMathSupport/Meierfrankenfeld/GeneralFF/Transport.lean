module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderDefs
public import CFSG.Quasithin.Background.Module
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

open CFSG.RankThree.FFModules

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem binU_sq (U : Submodule (ZMod 2) V) (v : Multiplicative ↥U) : v * v = 1 := by
  have h : Multiplicative.toAdd v + Multiplicative.toAdd v = 0 := by
    rw [← two_smul (ZMod 2)]
    have : (2 : ZMod 2) = 0 := rfl
    rw [this, zero_smul]
  apply Multiplicative.toAdd.injective
  simpa using h

theorem rep_mul_apply (ρ : Representation (ZMod 2) G V) (a b : G) (v : V) :
    ρ (a * b) v = ρ a (ρ b v) := by
  rw [map_mul, Module.End.mul_apply]

theorem rep_inv_apply (ρ : Representation (ZMod 2) G V) (a : G) (v : V) :
    ρ a⁻¹ (ρ a v) = v := by
  rw [← rep_mul_apply, inv_mul_cancel, map_one]; rfl

theorem rep_apply_inv (ρ : Representation (ZMod 2) G V) (a : G) (v : V) :
    ρ a (ρ a⁻¹ v) = v := by
  rw [← rep_mul_apply, mul_inv_cancel, map_one]; rfl

variable (ρ : Representation (ZMod 2) G V) (H : Subgroup G) (U : Submodule (ZMod 2) V)
  (hU : IsInvariant ρ H U)

@[expose] noncomputable def resAddEquiv (h : H) : U ≃+ U where
  toFun u := ⟨ρ h u, hU h h.2 u u.2⟩
  invFun u := ⟨ρ (h : G)⁻¹ u, hU _ (H.inv_mem h.2) u u.2⟩
  left_inv _ := Subtype.ext (rep_inv_apply ρ _ _)
  right_inv _ := Subtype.ext (rep_apply_inv ρ _ _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[expose] noncomputable def resBin : H →* MulAut (Multiplicative ↥U) where
  toFun h := AddEquiv.toMultiplicative (resAddEquiv ρ H U hU h)
  map_one' := by
    ext u
    simp [resAddEquiv]
  map_mul' a b := by
    ext u
    simp [resAddEquiv]

@[simp] theorem resBin_apply (h : H) (u : ↥U) :
    Multiplicative.toAdd (resBin ρ H U hU h (Multiplicative.ofAdd u)) =
      ⟨ρ h u, hU h h.2 u u.2⟩ := rfl

theorem resBin_apply_val (h : H) (v : Multiplicative ↥U) :
    ((Multiplicative.toAdd (resBin ρ H U hU h v) : ↥U) : V) = ρ h (Multiplicative.toAdd v : ↥U) :=
  rfl

@[expose] noncomputable def imgBin (B : Subgroup G) : Subgroup (MulAut (Multiplicative ↥U)) :=
  (B.subgroupOf H).map (resBin ρ H U hU)

variable {ρ H U hU}

theorem mem_imgBin {B : Subgroup G} {x : MulAut (Multiplicative ↥U)} :
    x ∈ imgBin ρ H U hU B ↔ ∃ b : H, (b : G) ∈ B ∧ resBin ρ H U hU b = x := by
  simp [imgBin, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem resBin_mem_imgBin {B : Subgroup G} {b : G} (hb : b ∈ B) (hbH : b ∈ H) :
    resBin ρ H U hU ⟨b, hbH⟩ ∈ imgBin ρ H U hU B :=
  mem_imgBin.2 ⟨⟨b, hbH⟩, hb, rfl⟩

theorem resBin_eq_one_iff (h : H) :
    resBin ρ H U hU h = 1 ↔ ∀ u ∈ U, ρ h u = u := by
  constructor
  · intro h1 u hu
    have := congrArg (fun x : MulAut (Multiplicative ↥U) =>
      ((Multiplicative.toAdd (x (Multiplicative.ofAdd ⟨u, hu⟩)) : ↥U) : V)) h1
    simpa using this
  · intro h1
    refine MulEquiv.ext fun u => ?_
    exact Multiplicative.toAdd.injective (Subtype.ext (h1 _ (Multiplicative.toAdd u).2))

theorem imgBin_mono {B B' : Subgroup G} (h : B ≤ B') :
    imgBin ρ H U hU B ≤ imgBin ρ H U hU B' :=
  Subgroup.map_mono fun _ hx => h hx

theorem imgBin_bot : imgBin ρ H U hU ⊥ = ⊥ := by
  simp [imgBin]

theorem mem_fixV_imgBin {B : Subgroup G} (hB : B ≤ H) {v : Multiplicative ↥U} :
    v ∈ CFSG.Quasithin.fixV (imgBin ρ H U hU B) ↔
      ∀ b ∈ B, ρ b ((Multiplicative.toAdd v : ↥U) : V) = (Multiplicative.toAdd v : ↥U) := by
  rw [CFSG.Quasithin.mem_fixV]
  constructor
  · intro h b hb
    exact congrArg (fun x : Multiplicative ↥U => ((Multiplicative.toAdd x : ↥U) : V))
      (h _ (resBin_mem_imgBin hb (hB hb)))
  · intro h x hx
    obtain ⟨b, hbB, rfl⟩ := mem_imgBin.1 hx
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact h b hbB

noncomputable def fixVEquiv {B : Subgroup G} (hB : B ≤ H) :
    ↥(CFSG.Quasithin.fixV (imgBin ρ H U hU B)) ≃ ↥(fixOn ρ B U) where
  toFun v := ⟨((Multiplicative.toAdd (v : Multiplicative ↥U) : ↥U) : V),
    (Multiplicative.toAdd (v : Multiplicative ↥U)).2, fun b hb =>
      (mem_fixV_imgBin hB).1 v.2 b hb⟩
  invFun w := ⟨Multiplicative.ofAdd ⟨w.1, w.2.1⟩, (mem_fixV_imgBin hB).2 fun b hb => w.2.2 b hb⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_fixV_imgBin {B : Subgroup G} (hB : B ≤ H) :
    Nat.card (CFSG.Quasithin.fixV (imgBin ρ H U hU B)) = Nat.card (fixOn ρ B U) :=
  Nat.card_congr (fixVEquiv hB)

noncomputable def resBinOn {B : Subgroup G} (hB : B ≤ H) : B →* MulAut (Multiplicative ↥U) :=
  (resBin ρ H U hU).comp (Subgroup.inclusion hB)

theorem range_resBinOn {B : Subgroup G} (hB : B ≤ H) :
    (resBinOn (hU := hU) hB).range = imgBin ρ H U hU B := by
  ext x
  rw [MonoidHom.mem_range, mem_imgBin]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨⟨b, hB b.2⟩, b.2, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, rfl⟩

noncomputable def kerEquiv {B : Subgroup G} (hB : B ≤ H) :
    ↥(resBinOn (hU := hU) hB).ker ≃ ↥(cenOn ρ B U) where
  toFun b := ⟨b.1.1, b.1.2, (resBin_eq_one_iff (hU := hU) _).1 b.2⟩
  invFun c := ⟨⟨c.1, c.2.1⟩, (resBin_eq_one_iff (hU := hU) ⟨c.1, hB c.2.1⟩).2 c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_imgBin_mul_card_cenOn {B : Subgroup G} (hB : B ≤ H) :
    Nat.card (imgBin ρ H U hU B) * Nat.card (cenOn ρ B U) = Nat.card B := by
  rw [← range_resBinOn (hU := hU) hB, ← Nat.card_congr (kerEquiv (hU := hU) hB), mul_comm]
  exact Subgroup.card_ker_mul_card_range _

theorem imgBin_eq_bot_iff {B : Subgroup G} (hB : B ≤ H) :
    imgBin ρ H U hU B = ⊥ ↔ B ≤ cenOn ρ B U := by
  rw [← range_resBinOn (hU := hU) hB, MonoidHom.range_eq_bot_iff]
  constructor
  · intro h b hb
    have := congrArg (fun f : B →* _ => f ⟨b, hb⟩) h
    exact ⟨hb, (resBin_eq_one_iff (⟨b, hB hb⟩ : H)).1 this⟩
  · intro h
    refine MonoidHom.ext fun ⟨b, hb⟩ => ?_
    exact (resBin_eq_one_iff (hU := hU) (⟨b, hB hb⟩ : H)).2 (h hb).2

theorem imgBin_sup {K B : Subgroup G} (hK : K ≤ H) (hB : B ≤ H) :
    imgBin ρ H U hU (K ⊔ B) = imgBin ρ H U hU K ⊔ imgBin ρ H U hU B := by
  rw [imgBin, Subgroup.subgroupOf_sup hK hB, Subgroup.map_sup]
  rfl

theorem rep_comm_eq (hU : IsInvariant ρ H U) {a b : G} (ha : a ∈ H) (hb : b ∈ H)
    (h : ∀ u ∈ U, ρ (a * b * a⁻¹ * b⁻¹) u = u) {w : V} (hw : w ∈ U) :
    ρ (a * b) w = ρ (b * a) w := by
  have := h _ (hU (b * a) (H.mul_mem hb ha) w hw)
  rw [← rep_mul_apply] at this
  have e : a * b * a⁻¹ * b⁻¹ * (b * a) = a * b := by group
  rwa [e] at this

theorem isElemAbelian2_imgBin {B : Subgroup G} (_hB : B ≤ H) (h : IsElemAbelianOn ρ B U) :
    CFSG.Quasithin.IsElemAbelian2 (imgBin ρ H U hU B) := by
  constructor
  · intro x hx y hy
    obtain ⟨a, haB, rfl⟩ := mem_imgBin.1 hx
    obtain ⟨b, hbB, rfl⟩ := mem_imgBin.1 hy
    rw [← map_mul, ← map_mul]
    refine MulEquiv.ext fun u => Multiplicative.toAdd.injective (Subtype.ext ?_)
    rw [resBin_apply_val, resBin_apply_val]
    exact rep_comm_eq hU a.2 b.2 (h a haB b hbB).1 (Multiplicative.toAdd u).2
  · intro x hx
    obtain ⟨a, haB, rfl⟩ := mem_imgBin.1 hx
    rw [pow_two, ← map_mul, resBin_eq_one_iff]
    exact (h a haB a haB).2

theorem isQuadratic_imgBin {B : Subgroup G} (_hB : B ≤ H) (h : IsQuadraticOn ρ B U) :
    CFSG.Quasithin.IsQuadratic (imgBin ρ H U hU B) := by
  refine Subgroup.closure_le _ |>.2 ?_
  rintro w ⟨x, hx, v, rfl⟩
  obtain ⟨a, haB, rfl⟩ := mem_imgBin.1 hx
  rw [SetLike.mem_coe, CFSG.Quasithin.mem_fixV]
  intro y hy
  obtain ⟨b, hbB, rfl⟩ := mem_imgBin.1 hy
  have hmem : ρ a (Multiplicative.toAdd v : ↥U) - (Multiplicative.toAdd v : ↥U) ∈ fixSub ρ B :=
    h (Submodule.subset_span ⟨a, haB, _, (Multiplicative.toAdd v).2, rfl⟩)
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  have hfix := mem_fixSub.1 hmem b hbB
  simp only [resBin_apply_val, toAdd_mul, toAdd_inv, Submodule.coe_add, Submodule.coe_neg,
    map_add, map_neg]
  have h2 : ρ b (ρ a (Multiplicative.toAdd v : ↥U)) - ρ b (Multiplicative.toAdd v : ↥U) =
      ρ a (Multiplicative.toAdd v : ↥U) - (Multiplicative.toAdd v : ↥U) := by
    rw [← map_sub]; exact hfix
  rw [← sub_eq_add_neg, ← sub_eq_add_neg, h2]

theorem subgroupOf_commutator {K B : Subgroup G} (hK : K ≤ H) (hB : B ≤ H) :
    ⁅K.subgroupOf H, B.subgroupOf H⁆ = ⁅K, B⁆.subgroupOf H := by
  have hKB : ⁅K, B⁆ ≤ H := (Subgroup.commutator_mono hK hB).trans
    (Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => by
      simpa [commutatorElement_def] using
        H.mul_mem (H.mul_mem (H.mul_mem hg₁ hg₂) (H.inv_mem hg₁)) (H.inv_mem hg₂))
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hK, inf_eq_left.2 hB, inf_eq_left.2 hKB]

theorem imgBin_commutator {K B : Subgroup G} (hK : K ≤ H) (hB : B ≤ H) :
    ⁅imgBin ρ H U hU K, imgBin ρ H U hU B⁆ = imgBin ρ H U hU ⁅K, B⁆ := by
  rw [imgBin, imgBin, imgBin, ← Subgroup.map_commutator, subgroupOf_commutator hK hB]

theorem imgBin_normal {K : Subgroup G}
    (hK : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) :
    ∀ x ∈ imgBin ρ H U hU H, ∀ y ∈ imgBin ρ H U hU K,
      x * y * x⁻¹ ∈ imgBin ρ H U hU K := by
  intro x hx y hy
  obtain ⟨a, -, rfl⟩ := mem_imgBin.1 hx
  obtain ⟨k, hkK, rfl⟩ := mem_imgBin.1 hy
  refine mem_imgBin.2 ⟨a * k * a⁻¹, hK a a.2 k hkK, ?_⟩
  simp

theorem imgBin_isQuasisimple {K : Subgroup G} (hKH : K ≤ H) (hK : CFSG.IsQuasisimple K)
    (hne : ¬ K ≤ cenOn ρ K U) : CFSG.IsQuasisimple (imgBin ρ H U hU K) := by
  have hK' : CFSG.IsQuasisimple (K.subgroupOf H) := by
    refine CFSG.LocalCores.isQuasisimple_of_surjective hK
      (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective ?_
    rw [(MonoidHom.ker_eq_bot_iff _).2 (Subgroup.subgroupOfEquivOfLe hKH).symm.injective]
    exact bot_le
  refine CFSG.LocalCores.isQuasisimple_map hK' (resBin ρ H U hU) fun h => hne fun k hk => ?_
  exact ⟨hk, (resBin_eq_one_iff (hU := hU) ⟨k, hKH hk⟩).1 (MonoidHom.mem_ker.1 (h hk))⟩

end CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
