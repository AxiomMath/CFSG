module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutEngineData

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.M23Std
open scoped Pointwise

@[expose] def IsoInv (P : (Y : Type) → [Group Y] → Subgroup Y → Prop) : Prop :=
  ∀ {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {F : Subgroup X}, P X F →
    P Y (F.map e.toMonoidHom)

@[expose] def AutSylowWith (P : (Y : Type) → [Group Y] → Subgroup Y → Prop) (Y : Type)
    [Group Y] : Prop :=
  ∀ S : Subgroup (MulAut Y), IsPGroup 2 S → ¬ 2 ∣ S.index → ∃ (t : Y) (F : Subgroup Y),
    SylowWitness Y S t F ∧ P Y F

variable {P : (Y : Type) → [Group Y] → Subgroup Y → Prop}

theorem AutSylowWith.of_sylow (hP : IsoInv P) {Y : Type} [Group Y] [Finite (MulAut Y)]
    {S₀ : Subgroup (MulAut Y)} (hp : IsPGroup 2 S₀) (hidx : ¬ 2 ∣ S₀.index) {t : Y}
    {F : Subgroup Y} (W : SylowWitness Y S₀ t F) (E : P Y F) : AutSylowWith P Y := by
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
  rw [hS_eq] at W'
  exact ⟨c t, F.map c.toMonoidHom, W', hP c E⟩

theorem AutSylowWith.of_mulEquiv (hP : IsoInv P) {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : AutSylowWith P X) : AutSylowWith P Y := by
  intro S hS hidx
  let φ : MulAut X ≃* MulAut Y := MulAut.congr e
  let S' : Subgroup (MulAut X) := S.map φ.symm.toMonoidHom
  have hS'p : IsPGroup 2 S' :=
    hS.of_equiv (Subgroup.equivMapOfInjective S φ.symm.toMonoidHom φ.symm.injective)
  have hS'idx : ¬ 2 ∣ S'.index := by
    have : S'.index = S.index := Subgroup.index_map_equiv (H := S) φ.symm
    rwa [this]
  obtain ⟨t, F, W, E⟩ := h S' hS'p hS'idx
  refine ⟨e t, F.map e.toMonoidHom, ?_, hP e E⟩
  have h1 := SylowWitness.map' e φ (congr_conj e) (congr_apply_mk e) W
  have h2 : S'.map φ.toMonoidHom = S := by
    ext β
    rw [mem_map_phi φ, show S' = S.map φ.symm.toMonoidHom from rfl, Subgroup.mem_map_equiv,
      MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  rwa [h2] at h1

variable {G : Type} [Group G] {L : Subgroup G} {z t : G}
  {T₁ : Subgroup (centralizer ({z} : Set G))} {F : Subgroup (L ⧸ center L)}
  {tb : L ⧸ center L}

theorem OutData.property [Finite G] (D : OutData L z t T₁ F tb) (hcZ : center (L ⧸ center L) = ⊥)
    (hEng : AutSylowWith P (L ⧸ center L)) : P (L ⧸ center L) F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup (MulAut (L ⧸ center L)) := T₁.map (thetaH D.cfg.cent_le) with hS
  have hSp : IsPGroup 2 S := IsPGroup.of_card (n := 8) (by rw [D.W.card_S]; norm_num)
  obtain ⟨Pg, hPg⟩ := hSp.exists_le_sylow
  obtain ⟨t₂, F₂, W₂, E₂⟩ := hEng Pg Pg.isPGroup' Pg.not_dvd_index
  have hPS : S = Pg := Subgroup.eq_of_le_of_card_ge hPg (by rw [W₂.card_S, D.W.card_S])
  have hW : SylowWitness (L ⧸ center L) (Pg : Subgroup _) tb F := hPS ▸ D.W
  have hF : F = F₂ := SylowWitness.F_unique hcZ hW W₂
  exact hF ▸ E₂

end CFSG.EvenSporadicStandard.M22Std
