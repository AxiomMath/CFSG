module

public import CFSG.LocalAnalysis.EvenBN.U5.LinTwin39NotNormal
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofNineSylow
public import CFSG.LocalAnalysis.EvenBN.Common.TwoElementary

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

namespace Lin43Out

section SecCenter

variable {G : Type*} [Group G] {L E : Subgroup G}

@[expose] def secCenter (hLE : L ≤ normalizer (E : Set G)) : Subgroup G where
  carrier := {x | x ∈ L ∧ ∀ y ∈ L, ⁅x, y⁆ ∈ E}
  mul_mem' := by
    rintro x x' ⟨hxL, hx⟩ ⟨hx'L, hx'⟩
    refine ⟨L.mul_mem hxL hx'L, fun y hy => ?_⟩
    have e : ⁅x * x', y⁆ = x * ⁅x', y⁆ * x⁻¹ * ⁅x, y⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact E.mul_mem ((mem_normalizer_iff.1 (hLE hxL) _).1 (hx' y hy)) (hx y hy)
  one_mem' := ⟨L.one_mem, fun y _ => by simp⟩
  inv_mem' := by
    rintro x ⟨hxL, hx⟩
    refine ⟨L.inv_mem hxL, fun y hy => ?_⟩
    have e : ⁅x⁻¹, y⁆ = x⁻¹ * (⁅x, y⁆)⁻¹ * x := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h1 := (mem_normalizer_iff.1 (hLE (L.inv_mem hxL)) _).1 (E.inv_mem (hx y hy))
    rwa [inv_inv] at h1

theorem mem_secCenter (hLE : L ≤ normalizer (E : Set G)) {x : G} :
    x ∈ secCenter hLE ↔ x ∈ L ∧ ∀ y ∈ L, ⁅x, y⁆ ∈ E := Iff.rfl

theorem secCenter_le (hLE : L ≤ normalizer (E : Set G)) : secCenter hLE ≤ L := fun _ hx => hx.1

theorem secCenter_cen (hLE : L ≤ normalizer (E : Set G)) :
    ∀ x ∈ secCenter hLE, ∀ y ∈ L, ⁅x, y⁆ ∈ E := fun _ hx y hy => hx.2 y hy

theorem E_le_secCenter (hEL : E ≤ L) (hLE : L ≤ normalizer (E : Set G)) : E ≤ secCenter hLE := by
  intro e he
  refine ⟨hEL he, fun y hy => ?_⟩
  have e1 : ⁅e, y⁆ = e * (y * e⁻¹ * y⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e1]
  exact E.mul_mem he ((mem_normalizer_iff.1 (hLE hy) _).1 (E.inv_mem he))

theorem secCenter_conj (hLE : L ≤ normalizer (E : Set G)) {g : G}
    (hgL : g ∈ normalizer (L : Set G)) (hgE : g ∈ normalizer (E : Set G)) {x : G}
    (hx : x ∈ secCenter hLE) : g * x * g⁻¹ ∈ secCenter hLE := by
  obtain ⟨hxL, hx'⟩ := hx
  refine ⟨(mem_normalizer_iff.1 hgL x).1 hxL, fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ L := by
    have h1 := (mem_normalizer_iff.1 (inv_mem hgL) y).1 hy
    rwa [inv_inv] at h1
  have h1 := hx' _ hy'
  have e : ⁅g * x * g⁻¹, y⁆ = g * ⁅x, g⁻¹ * y * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (mem_normalizer_iff.1 hgE _).1 h1

theorem mem_normalizer_secCenter (hLE : L ≤ normalizer (E : Set G)) {g : G}
    (hgL : g ∈ normalizer (L : Set G)) (hgE : g ∈ normalizer (E : Set G)) :
    g ∈ normalizer (secCenter hLE : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => secCenter_conj hLE hgL hgE hx, fun hx => ?_⟩
  have h1 := secCenter_conj hLE (inv_mem hgL) (inv_mem hgE) hx
  simpa [mul_assoc] using h1

theorem comm_mul_of_commute {m a b : G} (h : m * b = b * m) : ⁅m, a * b⁆ = ⁅m, a⁆ := by
  have h1 : b * m * b⁻¹ = m := by rw [← h]; group
  have h2 : b * m⁻¹ * b⁻¹ = m⁻¹ := by
    calc b * m⁻¹ * b⁻¹ = (b * m * b⁻¹)⁻¹ := by group
      _ = m⁻¹ := by rw [h1]
  calc ⁅m, a * b⁆ = m * a * (b * m⁻¹ * b⁻¹) * a⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = m * a * m⁻¹ * a⁻¹ := by rw [h2]
    _ = ⁅m, a⁆ := by simp only [commutatorElement_def]

end SecCenter

section Char

variable {G : Type*} [Group G]

theorem mem_normalizer_of_characteristic [Finite G] {S D : Subgroup G} (hDS : D ≤ S)
    (hD : (D.subgroupOf S).Characteristic) {g : G} (hg : g ∈ normalizer (S : Set G)) :
    g ∈ normalizer (D : Set G) := by
  refine mem_normalizer_fintype fun x hx => ?_
  set α : MulAut S := S.normalizerMonoidHom ⟨g, hg⟩ with hα
  have hchar : (D.subgroupOf S).comap α.toMonoidHom = D.subgroupOf S := hD.fixed α
  have hx' : (⟨x, hDS hx⟩ : S) ∈ D.subgroupOf S := hx
  have h1 : (⟨x, hDS hx⟩ : S) ∈ (D.subgroupOf S).comap α.toMonoidHom := by rw [hchar]; exact hx'
  have h2 : α ⟨x, hDS hx⟩ ∈ D.subgroupOf S := h1
  have : ((α ⟨x, hDS hx⟩ : S) : G) = g * x * g⁻¹ := by simp [hα]
  rw [← this]
  exact h2

theorem le_normalizer_of_inf_eq {R L S : Subgroup G} (hRL : R ≤ normalizer (L : Set G))
    (hS : R ⊓ L = S) : R ≤ normalizer (S : Set G) := by
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ r ∈ R, ∀ s ∈ S, r * s * r⁻¹ ∈ S := by
    intro r hr s hs
    rw [← hS] at hs ⊢
    exact ⟨R.mul_mem (R.mul_mem hr hs.1) (R.inv_mem hr),
      (mem_normalizer_iff.1 (hRL hr) s).1 hs.2⟩
  intro s
  refine ⟨fun hs => key r hr s hs, fun hs => ?_⟩
  have := key r⁻¹ (R.inv_mem hr) _ hs
  simpa [mul_assoc] using this

end Char

end Lin43Out

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem lin43o_ker_central (hl : d.LinCtx) :
    ∀ m ∈ (linπ hl).ker, ∀ x : d.M₂, x * m = m * x := by
  intro k hk x
  rw [MonoidHom.mem_ker] at hk
  have hmem : (⟨(k : G), lin_M₂_le_H hl k.2⟩ : ↥d.s38dH) ∈ d.s38dO := by
    have h2 := congrArg Subtype.val hk
    exact (QuotientGroup.eq_one_iff _).1 h2
  have hk' : (k : G) ∈ (s39a1O d).map (s39a1H d).subtype :=
    Subgroup.mem_map.2 ⟨⟨(k : G), lin_M₂_le_H hl k.2⟩, hmem, rfl⟩
  apply Subtype.ext
  exact (hl.toCaseHyp.s39a1_odd (k : G) hk' (x : G) x.2).symm

@[expose] def lin43oN (d : Data G h) : Subgroup G :=
  Lin43Out.secCenter (d.L₂_le_normalizer_E)

theorem mem_lin43oN {x : G} : x ∈ d.lin43oN ↔ x ∈ d.L₂ ∧ ∀ y ∈ d.L₂, ⁅x, y⁆ ∈ d.E :=
  Lin43Out.mem_secCenter d.L₂_le_normalizer_E

theorem lin43oN_le : d.lin43oN ≤ d.L₂ :=
  Lin43Out.secCenter_le (d.L₂_le_normalizer_E)

theorem lin43oN_normal : (d.lin43oN.subgroupOf d.L₂).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer d.lin43oN_le).2 fun _ hg =>
    Lin43Out.mem_normalizer_secCenter _ (le_normalizer hg) (d.L₂_le_normalizer_E hg)

theorem lin43o_lieModel (hl : d.LinCtx) (k : d.Know12) [(d.lin43oN.subgroupOf d.L₂).Normal] :
    LieModel (↥d.L₂ ⧸ d.lin43oN.subgroupOf d.L₂) .PSL 3 2 (2 * f) := by
  obtain ⟨hΛs, hΛL, -⟩ := lin_layer_facts hl
  haveI := hΛs
  have hL₂eq : d.L₂ = d.E ⊔ d.M₂ := k.s8.1
  have hM₂L : d.M₂ ≤ d.L₂ := hL₂eq ▸ le_sup_right
  have hLE : d.L₂ ≤ normalizer (d.E : Set G) := d.L₂_le_normalizer_E
  have hM₂N : d.M₂ ≤ normalizer (d.E : Set G) := hM₂L.trans hLE
  have hE2 : IsPGroup 2 d.E := hl.hyp.isPGroup_E hl.gms
  have hEM : d.E ⊓ d.M₂ = ⊥ := lin_E_inf_M₂ hl hE2 hM₂N
  let Φ : ↥d.M₂ →* (↥d.L₂ ⧸ d.lin43oN.subgroupOf d.L₂) :=
    (QuotientGroup.mk' (d.lin43oN.subgroupOf d.L₂)).comp (Subgroup.inclusion hM₂L)
  have hΦ : ∀ m : ↥d.M₂, Φ m = 1 ↔ (m : G) ∈ d.lin43oN := fun m =>
    (QuotientGroup.eq_one_iff (Subgroup.inclusion hM₂L m)).trans Subgroup.mem_subgroupOf
  have hΦsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    have hx : (x : G) ∈ d.M₂ ⊔ d.E := by
      rw [sup_comm, ← hL₂eq]
      exact x.2
    obtain ⟨m, hm, e, he, hxme⟩ := Common.exists_mul_of_le_normalizer' hM₂N (x : G) hx
    refine ⟨⟨m, hm⟩, ?_⟩
    show QuotientGroup.mk' (d.lin43oN.subgroupOf d.L₂) (Subgroup.inclusion hM₂L ⟨m, hm⟩) =
      (x : ↥d.L₂ ⧸ d.lin43oN.subgroupOf d.L₂)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show m⁻¹ * (x : G) ∈ d.lin43oN
    rw [hxme, inv_mul_cancel_left]
    exact Lin43Out.E_le_secCenter (d.E_le_L₂) hLE he
  have hcenter : Subgroup.center ↥(CFSG.layer (d.s38dH ⧸ d.s38dO)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center ↥(CFSG.layer (d.s38dH ⧸ d.s38dO))) with h0 | h1
    · exact h0
    · exfalso
      obtain ⟨x, y, hxy⟩ := lin_layer_nonabelian hl
      apply hxy
      have hx : x ∈ Subgroup.center ↥(CFSG.layer (d.s38dH ⧸ d.s38dO)) := by
        rw [h1]
        exact mem_top x
      exact (Subgroup.mem_center_iff.1 hx y).symm
  have hker : (linπ hl).ker = Φ.ker := by
    ext m
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hΦ]
    constructor
    · intro hm
      have hmk : m ∈ (linπ hl).ker := hm
      refine d.mem_lin43oN.2 ⟨hM₂L m.2, fun y hy => ?_⟩
      have hy' : y ∈ d.E ⊔ d.M₂ := by
        rw [← hL₂eq]
        exact hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Common.exists_mul_of_le_normalizer hM₂N y hy'
      have hc : (b : G) * (m : G) = (m : G) * (b : G) :=
        congrArg Subtype.val (lin43o_ker_central hl m hmk ⟨b, hb⟩)
      rw [Lin43Out.comm_mul_of_commute hc.symm, commutatorElement_def]
      exact d.E.mul_mem ((mem_normalizer_iff.1 (hM₂N m.2) a).1 ha) (d.E.inv_mem ha)
    · intro hm
      have hcomm : ∀ m' : ↥d.M₂, (m : G) * (m' : G) = (m' : G) * (m : G) := by
        intro m'
        have h1 : ⁅(m : G), (m' : G)⁆ ∈ d.E ⊓ d.M₂ :=
          ⟨(d.mem_lin43oN.1 hm).2 _ (hM₂L m'.2), d.M₂.mul_mem (d.M₂.mul_mem (d.M₂.mul_mem m.2 m'.2)
            (d.M₂.inv_mem m.2)) (d.M₂.inv_mem m'.2)⟩
        rw [hEM, Subgroup.mem_bot, commutatorElement_def] at h1
        calc (m : G) * (m' : G) = ((m : G) * (m' : G) * (m : G)⁻¹ * (m' : G)⁻¹) * ((m' : G) * (m : G)) := by
              group
          _ = (m' : G) * (m : G) := by rw [h1, one_mul]
      have hcen : linπ hl m ∈ Subgroup.center ↥(CFSG.layer (d.s38dH ⧸ d.s38dO)) := by
        rw [Subgroup.mem_center_iff]
        intro z
        obtain ⟨m', rfl⟩ := lin_π_surjective hl z
        rw [← map_mul, ← map_mul]
        exact congrArg _ (Subtype.ext (hcomm m').symm)
      rw [hcenter, Subgroup.mem_bot] at hcen
      exact hcen
  let eΛX : ↥(CFSG.layer (d.s38dH ⧸ d.s38dO)) ≃* (↥d.L₂ ⧸ d.lin43oN.subgroupOf d.L₂) :=
    (QuotientGroup.quotientKerEquivOfSurjective (linπ hl) (lin_π_surjective hl)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective Φ hΦsurj))
  exact LieModel.of_mulEquiv eΛX hΛL

end Data

end CFSG.LocalAnalysis.EvenBN.U5
