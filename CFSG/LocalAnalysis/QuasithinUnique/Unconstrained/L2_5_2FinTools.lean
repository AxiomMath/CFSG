module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.QuasithinUnique.Unc25G2

open CFSG.Open CFSG.Quasithin

section Tools

theorem charTwo_of_normal_pGroup {G : Type*} [Group G] {K E : Subgroup G} (hEK : E ≤ K)
    (hn : K ≤ Subgroup.normalizer (E : Set G)) (hE : IsPGroup 2 E)
    (hC : K ⊓ Subgroup.centralizer (E : Set G) ≤ E) : CharTwo K := by
  have hEO : E ≤ pCoreOf 2 K :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 E K hEK
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hEK).mpr hn) hE
  intro x hx
  exact hEO (hC ⟨hx.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hEO) hx.2⟩)

variable {G : Type*} [Group G]

@[expose] def conjAut (L : Subgroup G) (s : G) (hs : s ∈ Subgroup.normalizer (L : Set G)) : MulAut L :=
  L.normalizerMonoidHom ⟨s, hs⟩

theorem coe_conjAut (L : Subgroup G) (s : G) (hs : s ∈ Subgroup.normalizer (L : Set G)) (x : L) :
    ((conjAut L s hs x : L) : G) = s * x * s⁻¹ := rfl

theorem le_normalizer_map_subtype {L S₀ : Subgroup G} (hS : S₀ ≤ Subgroup.normalizer (L : Set G))
    (K' : Subgroup L)
    (h : ∀ s (hs : s ∈ S₀), ∀ x : L, x ∈ K' → conjAut L s (hS hs) x ∈ K') :
    S₀ ≤ Subgroup.normalizer ((K'.map L.subtype : Subgroup G) : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨conjAut L s (hS hs) x, h s hs x hx, rfl⟩
  · rintro ⟨y, hy, hyg⟩
    have hs' : s⁻¹ ∈ S₀ := S₀.inv_mem hs
    refine ⟨conjAut L s⁻¹ (hS hs') y, h s⁻¹ hs' y hy, ?_⟩
    show ((conjAut L s⁻¹ (hS hs') y : L) : G) = g
    rw [coe_conjAut]
    have : (y : G) = s * g * s⁻¹ := hyg
    rw [this]
    group



theorem charTwo_map_subtype_of_normal_pGroup {L : Subgroup G} {K' V' : Subgroup L}
    (hVK : V' ≤ K') (hn : K' ≤ Subgroup.normalizer (V' : Set L)) (hV : IsPGroup 2 V')
    (hC : ∀ x ∈ K', (∀ v ∈ V', x * v = v * x) → x ∈ V') : CharTwo (K'.map L.subtype) := by
  have hV' : IsPGroup 2 (V'.map L.subtype) := hV.map _
  refine charTwo_of_normal_pGroup (Subgroup.map_mono hVK) ?_ hV' ?_
  · rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨k * v * k⁻¹, (Subgroup.mem_normalizer_iff.mp (hn hk) v).mp hv, by simp⟩
    · rintro ⟨w, hw, hwh⟩
      refine ⟨k⁻¹ * w * k, ?_, ?_⟩
      · have e : k * (k⁻¹ * w * k) * k⁻¹ = w := by group
        exact (Subgroup.mem_normalizer_iff.mp (hn hk) (k⁻¹ * w * k)).mpr (by rw [e]; exact hw)
      · have hwh' : (w : G) = k * h * (k : G)⁻¹ := hwh
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hwh']
        group
  · rintro _ ⟨hx, hxC⟩
    obtain ⟨x, hxK, rfl⟩ := hx
    refine ⟨x, hC x hxK (fun v hv => ?_), rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hxC (v : G) ⟨v, hv, rfl⟩
    exact Subtype.ext this.symm

end Tools

section Canonical

variable {X : Type*} [Group X]

@[expose] def commCentralizer (P : Subgroup X) : Subgroup X where
  carrier := {x | x ∈ P ∧ ∀ y ∈ P, ∀ w ∈ P, x * (y * w * y⁻¹ * w⁻¹) = (y * w * y⁻¹ * w⁻¹) * x}
  mul_mem' := by
    rintro a b ⟨haP, ha⟩ ⟨hbP, hb⟩
    refine ⟨P.mul_mem haP hbP, fun y hy w hw => ?_⟩
    rw [mul_assoc, hb y hy w hw, ← mul_assoc, ha y hy w hw, mul_assoc]
  one_mem' := ⟨P.one_mem, fun y _ w _ => by simp⟩
  inv_mem' := by
    rintro a ⟨haP, ha⟩
    refine ⟨P.inv_mem haP, fun y hy w hw => ?_⟩
    have h := ha y hy w hw
    calc a⁻¹ * (y * w * y⁻¹ * w⁻¹) = a⁻¹ * (y * w * y⁻¹ * w⁻¹) * (a * a⁻¹) := by group
      _ = a⁻¹ * ((y * w * y⁻¹ * w⁻¹) * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * (y * w * y⁻¹ * w⁻¹)) * a⁻¹ := by rw [h]
      _ = (y * w * y⁻¹ * w⁻¹) * a⁻¹ := by group

theorem mem_commCentralizer {P : Subgroup X} {x : X} :
    x ∈ commCentralizer P ↔
      x ∈ P ∧ ∀ y ∈ P, ∀ w ∈ P, x * (y * w * y⁻¹ * w⁻¹) = (y * w * y⁻¹ * w⁻¹) * x := Iff.rfl

theorem commCentralizer_le (P : Subgroup X) : commCentralizer P ≤ P := fun _ hx => hx.1

theorem map_commCentralizer {Y : Type*} [Group Y] (e : X ≃* Y) (P : Subgroup X) :
    (commCentralizer P).map e.toMonoidHom = commCentralizer (P.map e.toMonoidHom) := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxP, hx⟩, rfl⟩
    refine ⟨⟨x, hxP, rfl⟩, ?_⟩
    rintro _ ⟨y', hy', rfl⟩ _ ⟨w', hw', rfl⟩
    have := congrArg e (hx y' hy' w' hw')
    simpa only [MulEquiv.coe_toMonoidHom, map_mul, map_inv] using this
  · rintro ⟨⟨x, hxP, rfl⟩, hx⟩
    refine ⟨x, ⟨hxP, fun y' hy' w' hw' => ?_⟩, rfl⟩
    have := hx (e y') ⟨y', hy', rfl⟩ (e w') ⟨w', hw', rfl⟩
    apply e.injective
    simpa [map_mul, map_inv] using this

theorem map_commCentralizer_eq_self (α : MulAut X) {P : Subgroup X}
    (hα : P.map α.toMonoidHom = P) :
    (commCentralizer P).map α.toMonoidHom = commCentralizer P := by
  have := map_commCentralizer α P
  rwa [hα] at this


theorem mem_commCentralizer_map_iff {Y : Type*} [Group Y] {f : X →* Y} (hf : Function.Injective f)
    (P : Subgroup X) (x : X) : f x ∈ commCentralizer (P.map f) ↔ x ∈ commCentralizer P := by
  constructor
  · rintro ⟨hxP, h⟩
    obtain ⟨x', hx'P, hx'⟩ := hxP
    have hx : x' = x := hf hx'
    subst hx
    refine ⟨hx'P, fun y hy w hw => ?_⟩
    have := h (f y) ⟨y, hy, rfl⟩ (f w) ⟨w, hw, rfl⟩
    apply hf
    simpa only [map_mul, map_inv] using this
  · rintro ⟨hxP, h⟩
    refine ⟨⟨x, hxP, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩ _ ⟨w, hw, rfl⟩
    have := congrArg f (h y hy w hw)
    simpa only [map_mul, map_inv] using this

end Canonical


section Sylow

open scoped Pointwise

variable {A : Type*} [Group A] [Finite A]

theorem exists_conj_map_eq {p : ℕ} [Fact p.Prime] {P Q : Subgroup A} (hP : IsPGroup p P)
    (hP' : ¬ p ∣ P.index) (hQ : IsPGroup p Q) (hQ' : ¬ p ∣ Q.index) :
    ∃ a : A, P.map (MulAut.conj a).toMonoidHom = Q := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A (hP.toSylow hP') (hQ.toSylow hQ')
  refine ⟨a, ?_⟩
  have h4 : P.map (MulAut.conj a).toMonoidHom = ((a • hP.toSylow hP' : Sylow p A) : Subgroup A) := by
    rw [Sylow.coe_subgroup_smul]
    rfl
  rw [h4, ha]
  rfl

end Sylow


end CFSG.QuasithinUnique.Unc25G2
