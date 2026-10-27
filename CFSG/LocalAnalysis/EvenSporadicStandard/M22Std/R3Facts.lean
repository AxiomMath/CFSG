module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutEngineData

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.M23Std
open scoped Pointwise

structure E32Facts (Y : Type) [Group Y] (S : Subgroup (MulAut Y)) (F : Subgroup Y)
    (J : Subgroup (MulAut Y)) : Prop where
  le : J ≤ S
  comm : ∀ α ∈ J, ∀ β ∈ J, α * β = β * α
  sq : ∀ α ∈ J, α * α = 1
  card : Nat.card J = 32
  unique : ∀ E : Subgroup (MulAut Y), E ≤ S → (∀ α ∈ E, ∀ β ∈ E, α * β = β * α) →
    (∀ α ∈ E, α * α = 1) → 32 ≤ Nat.card E → E = J
  exists_b : ∃ b : Y, b * b = 1 ∧ b ∉ F ∧ MulAut.conj b ∈ J
  normal_E16 : ∀ V : Subgroup (MulAut Y), V ≤ S → (∀ α ∈ S, ∀ β ∈ V, α * β * α⁻¹ ∈ V) →
    (∀ α ∈ V, ∀ β ∈ V, α * β = β * α) → (∀ α ∈ V, α * α = 1) → Nat.card V = 16 →
    Nat.card ↥(V ⊓ J) ≤ 4 → V = innerImage Y F

variable {X Y : Type} [Group X] [Group Y]

theorem mem_pull (φ : MulAut X ≃* MulAut Y) (E' : Subgroup (MulAut Y)) (α : MulAut X) :
    α ∈ E'.map φ.symm.toMonoidHom ↔ φ α ∈ E' := by
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm]

theorem map_pull (φ : MulAut X ≃* MulAut Y) (E' : Subgroup (MulAut Y)) :
    (E'.map φ.symm.toMonoidHom).map φ.toMonoidHom = E' := by
  ext β
  rw [Subgroup.mem_map_equiv, mem_pull, MulEquiv.apply_symm_apply]

theorem card_pull (φ : MulAut X ≃* MulAut Y) (E' : Subgroup (MulAut Y)) :
    Nat.card ↥(E'.map φ.symm.toMonoidHom) = Nat.card E' :=
  Subgroup.card_map_of_injective (K := E') (f := φ.symm.toMonoidHom) φ.symm.injective

theorem E32Facts.map' (e : X ≃* Y) (φ : MulAut X ≃* MulAut Y)
    (hc : ∀ x, φ (MulAut.conj x) = MulAut.conj (e x)) {S : Subgroup (MulAut X)}
    {F : Subgroup X} {J : Subgroup (MulAut X)} (h : E32Facts X S F J) :
    E32Facts Y (S.map φ.toMonoidHom) (F.map e.toMonoidHom) (J.map φ.toMonoidHom) := by
  have hφinj : ∀ α β : MulAut X, φ α = φ β → α = β := fun α β h => φ.injective h
  refine ⟨Subgroup.map_mono h.le, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩
    show φ α * φ β = φ β * φ α
    rw [← map_mul, ← map_mul, h.comm α hα β hβ]
  · rintro _ ⟨α, hα, rfl⟩
    show φ α * φ α = 1
    rw [← map_mul, h.sq α hα, map_one]
  · rw [Subgroup.card_map_of_injective φ.injective]
    exact h.card
  · intro E' hES hcomm hsq hcard
    set E : Subgroup (MulAut X) := E'.map φ.symm.toMonoidHom with hEdef
    have hmem : ∀ α, α ∈ E ↔ φ α ∈ E' := fun α => mem_pull φ E' α
    have hEle : E ≤ S := fun α hα => by
      have := (Subgroup.mem_map_equiv (f := φ)).1 (hES ((hmem α).1 hα))
      rwa [MulEquiv.symm_apply_apply] at this
    have hEJ : E = J := h.unique E hEle
      (fun α hα β hβ => hφinj _ _ (by
        rw [map_mul, map_mul]; exact hcomm _ ((hmem α).1 hα) _ ((hmem β).1 hβ)))
      (fun α hα => hφinj _ _ (by
        rw [map_mul, map_one]; exact hsq _ ((hmem α).1 hα)))
      (by rw [hEdef, card_pull]; exact hcard)
    rw [← map_pull φ E', ← hEdef, hEJ]
  · obtain ⟨b, hb2, hbF, hbJ⟩ := h.exists_b
    refine ⟨e b, ?_, ?_, ?_⟩
    · rw [← map_mul, hb2, map_one]
    · intro hmem
      exact hbF ((Subgroup.mem_map_iff_mem e.injective).1 hmem)
    · rw [← hc b]
      exact ⟨MulAut.conj b, hbJ, rfl⟩
  · intro V' hVS hVn hVc hVs hVcard hVJ
    set V : Subgroup (MulAut X) := V'.map φ.symm.toMonoidHom with hVdef
    have hmem : ∀ α, α ∈ V ↔ φ α ∈ V' := fun α => mem_pull φ V' α
    have hVle : V ≤ S := fun α hα => by
      have := (Subgroup.mem_map_equiv (f := φ)).1 (hVS ((hmem α).1 hα))
      rwa [MulEquiv.symm_apply_apply] at this
    have hVJ' : Nat.card ↥(V ⊓ J) ≤ 4 := by
      have : (V ⊓ J).map φ.toMonoidHom = V' ⊓ J.map φ.toMonoidHom := by
        ext β
        rw [Subgroup.mem_map_equiv, Subgroup.mem_inf, Subgroup.mem_inf, hmem,
          MulEquiv.apply_symm_apply, Subgroup.mem_map_equiv]
      rw [← Subgroup.card_map_of_injective (K := V ⊓ J) (f := φ.toMonoidHom) φ.injective, this]
      exact hVJ
    have hVeq : V = innerImage X F := h.normal_E16 V hVle
      (fun α hα β hβ => by
        have h1 := hVn (φ α) ((Subgroup.mem_map_equiv (f := φ)).2 (by
          rwa [MulEquiv.symm_apply_apply])) (φ β) ((hmem β).1 hβ)
        rw [hmem, map_mul, map_mul, map_inv]
        exact h1)
      (fun α hα β hβ => hφinj _ _ (by
        rw [map_mul, map_mul]; exact hVc _ ((hmem α).1 hα) _ ((hmem β).1 hβ)))
      (fun α hα => hφinj _ _ (by
        rw [map_mul, map_one]; exact hVs _ ((hmem α).1 hα)))
      (by rw [hVdef, card_pull]; exact hVcard) hVJ'
    rw [← map_pull φ V', ← hVdef, hVeq, innerImage_map' e φ hc]

@[expose] def IsoInv3
    (P : (Y : Type) → [Group Y] → Subgroup (MulAut Y) → Subgroup Y → Prop) : Prop :=
  ∀ {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {S : Subgroup (MulAut X)} {F : Subgroup X},
    P X S F → P Y (S.map (MulAut.congr e).toMonoidHom) (F.map e.toMonoidHom)

@[expose] def AutSylowWith3
    (P : (Y : Type) → [Group Y] → Subgroup (MulAut Y) → Subgroup Y → Prop) (Y : Type)
    [Group Y] : Prop :=
  ∀ S : Subgroup (MulAut Y), IsPGroup 2 S → ¬ 2 ∣ S.index → ∃ (t : Y) (F : Subgroup Y),
    SylowWitness Y S t F ∧ P Y S F

variable {P : (Y : Type) → [Group Y] → Subgroup (MulAut Y) → Subgroup Y → Prop}

theorem AutSylowWith3.of_sylow (hP : IsoInv3 P) {Y : Type} [Group Y] [Finite (MulAut Y)]
    {S₀ : Subgroup (MulAut Y)} (hp : IsPGroup 2 S₀) (hidx : ¬ 2 ∣ S₀.index) {t : Y}
    {F : Subgroup Y} (W : SylowWitness Y S₀ t F) (E : P Y S₀ F) : AutSylowWith3 P Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S hS hSidx
  let P1 : Sylow 2 (MulAut Y) := hp.toSylow hidx
  let P2 : Sylow 2 (MulAut Y) := hS.toSylow hSidx
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (MulAut Y) P1 P2
  have hmem : ∀ α : MulAut Y, α ∈ S ↔ c⁻¹ * α * c ∈ S₀ := by
    intro α
    have h1 : (P2 : Subgroup (MulAut Y)) = MulAut.conj c • (P1 : Subgroup (MulAut Y)) := by
      rw [← hc, Sylow.coe_subgroup_smul]
    have h2 : α ∈ (P2 : Subgroup (MulAut Y)) ↔
        (MulAut.conj c)⁻¹ • α ∈ (P1 : Subgroup (MulAut Y)) := by
      rw [h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have h3 : (P2 : Subgroup (MulAut Y)) = S := rfl
    have h4 : (P1 : Subgroup (MulAut Y)) = S₀ := rfl
    rw [h3, h4] at h2
    rw [h2]
    simp [MulAut.smul_def, mul_assoc]
  have hS_eq : S₀.map (MulAut.congr c).toMonoidHom = S := by
    ext β
    rw [mem_map_phi (MulAut.congr c), congr_self_symm_apply, hmem]
  have W' := SylowWitness.map' c (MulAut.congr c) (congr_conj c) (congr_apply_mk c) W
  have E' := hP c E
  rw [hS_eq] at W' E'
  exact ⟨c t, F.map c.toMonoidHom, W', E'⟩

theorem AutSylowWith3.of_mulEquiv (hP : IsoInv3 P) {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) (h : AutSylowWith3 P X) : AutSylowWith3 P Y := by
  intro S hS hidx
  let φ : MulAut X ≃* MulAut Y := MulAut.congr e
  let S' : Subgroup (MulAut X) := S.map φ.symm.toMonoidHom
  have hS'p : IsPGroup 2 S' :=
    hS.of_equiv (Subgroup.equivMapOfInjective S φ.symm.toMonoidHom φ.symm.injective)
  have hS'idx : ¬ 2 ∣ S'.index := by
    have : S'.index = S.index := Subgroup.index_map_equiv (H := S) φ.symm
    rwa [this]
  obtain ⟨t, F, W, E⟩ := h S' hS'p hS'idx
  have h2 : S'.map φ.toMonoidHom = S := by
    ext β
    rw [mem_map_phi φ, show S' = S.map φ.symm.toMonoidHom from rfl, Subgroup.mem_map_equiv,
      MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  have h1 := SylowWitness.map' e φ (congr_conj e) (congr_apply_mk e) W
  have E' := hP e E
  rw [h2] at h1 E'
  exact ⟨e t, F.map e.toMonoidHom, h1, E'⟩

variable {G : Type} [Group G] {L : Subgroup G} {z t : G}
  {T₁ : Subgroup (centralizer ({z} : Set G))} {F : Subgroup (L ⧸ center L)}
  {tb : L ⧸ center L}

theorem OutData.property3 [Finite G] (D : OutData L z t T₁ F tb)
    (hcZ : center (L ⧸ center L) = ⊥) (hEng : AutSylowWith3 P (L ⧸ center L)) :
    P (L ⧸ center L) (T₁.map (thetaH D.cfg.cent_le)) F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup (MulAut (L ⧸ center L)) := T₁.map (thetaH D.cfg.cent_le) with hS
  have hSp : IsPGroup 2 S := IsPGroup.of_card (n := 8) (by rw [D.W.card_S]; norm_num)
  obtain ⟨Pg, hPg⟩ := hSp.exists_le_sylow
  obtain ⟨t₂, F₂, W₂, E₂⟩ := hEng Pg Pg.isPGroup' Pg.not_dvd_index
  have hPS : S = Pg := Subgroup.eq_of_le_of_card_ge hPg (by rw [W₂.card_S, D.W.card_S])
  have hW : SylowWitness (L ⧸ center L) (Pg : Subgroup _) tb F := hPS ▸ D.W
  have hF : F = F₂ := SylowWitness.F_unique hcZ hW W₂
  rw [hPS, hF]
  exact E₂

end CFSG.EvenSporadicStandard.M22Std
