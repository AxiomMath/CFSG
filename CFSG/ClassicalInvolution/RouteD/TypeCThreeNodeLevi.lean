module

public import CFSG.ClassicalInvolution.RouteD.TypeCThreeNodeSolv

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped MatrixGroups commutatorElement

section Generic

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem oddCore_subgroupOf_eq_bot {Y T : Subgroup G} (hTY : T ≤ Y)
    (e : T ≃* SL(2, GaloisField p f)) (hodd : Odd (Nat.card (GaloisField p f)))
    (h3 : 3 ≤ Nat.card (GaloisField p f)) :
    classicalInvolutionOddCore (T.subgroupOf Y) = ⊥ :=
  CFSG.ClassicalInvolution.normal_odd_of_equiv_sl2 hodd h3
    ((Subgroup.subgroupOfEquivOfLe hTY).trans e) _ inferInstance
    (CFSG.ComponentClassification.OddCore.odd_card _)

theorem isClassicalMember_subgroupOf_node {Y T : Subgroup G} (hTY : T ≤ Y)
    (e : T ≃* SL(2, GaloisField p f)) (h4 : 4 ≤ Nat.card (GaloisField p f))
    (hodd : Odd (Nat.card (GaloisField p f))) {zz : G} (hzT : zz ∈ T) (hz2 : orderOf zz = 2)
    (hcent : ∀ t ∈ T, t * zz = zz * t)
    (hnorm : ∀ y ∈ Y, y * zz = zz * y → ∀ t ∈ T, y * t * y⁻¹ ∈ T) :
    IsClassicalMember p f (T.subgroupOf Y) ⟨zz, hTY hzT⟩ := by
  have eS : T.subgroupOf Y ≃* SL(2, GaloisField p f) :=
    (Subgroup.subgroupOfEquivOfLe hTY).trans e
  have hbot : classicalInvolutionOddCore (T.subgroupOf Y) = ⊥ :=
    oddCore_subgroupOf_eq_bot hTY e hodd (by omega)
  refine ⟨by rw [Subgroup.orderOf_mk]; exact hz2, Subgroup.mem_subgroupOf.mpr hzT,
    CFSG.ClassicalInvolution.isPerfect_of_equiv_sl2 h4 eS, ?_, ?_⟩
  · have hle : T.subgroupOf Y ≤ Subgroup.centralizer ({(⟨zz, hTY hzT⟩ : ↥Y)} : Set ↥Y) := by
      intro t ht
      refine Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)
      exact hcent t (Subgroup.mem_subgroupOf.mp ht)
    refine IsSubnormal.step hle ?_ (IsSubnormal.refl _)
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : ↥Y) * ⟨zz, hTY hzT⟩ = ⟨zz, hTY hzT⟩ * (g : ↥Y) :=
      Subgroup.mem_centralizer_singleton_iff.mp g.2
    exact hnorm _ (g : ↥Y).2 (congrArg Subtype.val hg) _ hn
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hbot).trans (QuotientGroup.quotientBot.trans eS)⟩

end Generic

section Levi

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G} {S : CSetupW p f 2 Ω K z} {Fr : Frame p f 2 Ω K z}
  (P : LeviParams S Fr)

namespace LeviParams

theorem T₀_le_Y : P.T₀ ≤ P.T₀ ⊔ P.T₁ := le_sup_left

theorem T₁_le_Y : P.T₁ ≤ P.T₀ ⊔ P.T₁ := le_sup_right

theorem isClassicalMember₀ (hconn : DeltaConnected Ω) (hZ : Subgroup.center G = ⊥) :
    IsClassicalMember p f (P.T₀.subgroupOf (P.T₀ ⊔ P.T₁))
      ⟨Fr.zf 2, P.T₀_le_Y (P.zf_two_mem hconn hZ)⟩ := by
  obtain ⟨e⟩ := P.nonempty_equiv₀
  refine isClassicalMember_subgroupOf_node P.T₀_le_Y e.symm S.four_le S.odd_card
    (P.zf_two_mem hconn hZ) (Fr.clsW S 2).orderOf_eq_two ?_ ?_
  · intro t ht
    exact commutes_Mf_Kf Fr (i := 0) (j := 1) (k := 2) (by decide) (by decide) t (P.T₀_le ht)
      (Fr.zf 2) (Frame.zf_memW S 2)
  · intro y hy hyz t ht
    have hMy : conjSub y (Mf Fr 0 1) = Mf Fr 0 1 :=
      conjSub_Mf_eq_of_commute S Fr (i := 0) (j := 1) (k := 2) (by decide) (by decide)
        (by decide) hyz
    have hk₂ : ∀ m ∈ Mf Fr 0 1, m * P.x₂ = P.x₂ * m := fun m hm =>
      commutes_Mf_Kf Fr (i := 0) (j := 1) (k := 2) (by decide) (by decide) m hm P.x₂
        (Frame.Tf_le 2 P.x₂_mem)
    have hd : P.x₀ * P.x₁ ∈ Mf Fr 0 1 := (Mf Fr 0 1).mul_mem
      (Tf_le_Mf Fr 0 (Or.inl rfl) P.x₀_mem) (Tf_le_Mf Fr 1 (Or.inr rfl) P.x₁_mem)
    have hyh : y * (P.x₀ * P.x₁ * P.x₂) * y⁻¹ = P.x₀ * P.x₁ * P.x₂ :=
      mul_inv_eq_iff_eq_mul.mpr (P.mem_centralizer_h hy)
    have hT := conjSub_leviNode hd hk₂ hMy hyh
    have := conj_mem_conjSub (n := y) ht
    rwa [show conjSub y P.T₀ = P.T₀ from hT] at this

theorem isClassicalMember₁ (hconn : DeltaConnected Ω) (hZ : Subgroup.center G = ⊥) :
    IsClassicalMember p f (P.T₁.subgroupOf (P.T₀ ⊔ P.T₁))
      ⟨Fr.zf 0, P.T₁_le_Y (P.zf_zero_mem hconn hZ)⟩ := by
  obtain ⟨e⟩ := P.nonempty_equiv₁
  refine isClassicalMember_subgroupOf_node P.T₁_le_Y e.symm S.four_le S.odd_card
    (P.zf_zero_mem hconn hZ) (Fr.clsW S 0).orderOf_eq_two ?_ ?_
  · intro t ht
    exact commutes_Mf_Kf Fr (i := 1) (j := 2) (k := 0) (by decide) (by decide) t (P.T₁_le ht)
      (Fr.zf 0) (Frame.zf_memW S 0)
  · intro y hy hyz t ht
    have hMy : conjSub y (Mf Fr 1 2) = Mf Fr 1 2 :=
      conjSub_Mf_eq_of_commute S Fr (i := 1) (j := 2) (k := 0) (by decide) (by decide)
        (by decide) hyz
    have hk₀ : ∀ m ∈ Mf Fr 1 2, m * P.x₀ = P.x₀ * m := fun m hm =>
      commutes_Mf_Kf Fr (i := 1) (j := 2) (k := 0) (by decide) (by decide) m hm P.x₀
        (Frame.Tf_le 0 P.x₀_mem)
    have hd : P.x₁ * P.x₂ ∈ Mf Fr 1 2 := (Mf Fr 1 2).mul_mem
      (Tf_le_Mf Fr 1 (Or.inl rfl) P.x₁_mem) (Tf_le_Mf Fr 2 (Or.inr rfl) P.x₂_mem)
    have hh : P.x₀ * P.x₁ * P.x₂ = P.x₁ * P.x₂ * P.x₀ := by
      rw [Fr.Tf_mul_comm P.x₀_mem P.x₁_mem, mul_assoc, Fr.Tf_mul_comm P.x₀_mem P.x₂_mem,
        ← mul_assoc]
    have hyh : y * (P.x₁ * P.x₂ * P.x₀) * y⁻¹ = P.x₁ * P.x₂ * P.x₀ := by
      rw [← hh]
      exact mul_inv_eq_iff_eq_mul.mpr (P.mem_centralizer_h hy)
    have hT := conjSub_leviNode hd hk₀ hMy hyh
    have := conj_mem_conjSub (n := y) ht
    rwa [show conjSub y P.T₁ = P.T₁ from hT] at this

@[expose] def family : Set (Subgroup ↥(P.T₀ ⊔ P.T₁)) :=
  {L | ∃ y : ↥(P.T₀ ⊔ P.T₁), L = conjSub y (P.T₀.subgroupOf (P.T₀ ⊔ P.T₁)) ∨
    L = conjSub y (P.T₁.subgroupOf (P.T₀ ⊔ P.T₁))}

theorem sup_subgroupOf_eq_top :
    P.T₀.subgroupOf (P.T₀ ⊔ P.T₁) ⊔ P.T₁.subgroupOf (P.T₀ ⊔ P.T₁) = ⊤ := by
  apply Subgroup.map_injective (P.T₀ ⊔ P.T₁).subtype_injective
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr P.T₀_le_Y, inf_eq_left.mpr P.T₁_le_Y, Subgroup.map_top,
    Subgroup.range_subtype]

theorem inClass (hconn : DeltaConnected Ω) (hZ : Subgroup.center G = ⊥) :
    InClass p f P.family where
  nonempty := ⟨_, 1, Or.inl (conjSub_one _).symm⟩
  conjInvariant := by
    rintro n _ ⟨y, hy⟩
    refine ⟨n * y, ?_⟩
    rcases hy with rfl | rfl
    · exact Or.inl (conjSub_mul n y _).symm
    · exact Or.inr (conjSub_mul n y _).symm
  generated := by
    rw [eq_top_iff, ← P.sup_subgroupOf_eq_top]
    refine sup_le ?_ ?_
    · exact le_iSup₂_of_le _ ⟨1, Or.inl (conjSub_one _).symm⟩ le_rfl
    · exact le_iSup₂_of_le _ ⟨1, Or.inr (conjSub_one _).symm⟩ le_rfl
  classical := by
    rintro L ⟨y, rfl | rfl⟩
    · exact ⟨_, (P.isClassicalMember₀ hconn hZ).conj y⟩
    · exact ⟨_, (P.isClassicalMember₁ hconn hZ).conj y⟩

theorem h_ne_one : P.x₀ * P.x₁ * P.x₂ ≠ 1 := by
  intro h
  apply P.hn01
  have hk₂ : ∀ m ∈ Mf Fr 0 1, m * P.x₂ = P.x₂ * m := fun m hm =>
    commutes_Mf_Kf Fr (i := 0) (j := 1) (k := 2) (by decide) (by decide) m hm P.x₂
      (Frame.Tf_le 2 P.x₂_mem)
  have hx : P.x₀ * P.x₁ = P.x₂⁻¹ := eq_inv_of_mul_eq_one_left h
  intro m hm
  rw [Subgroup.mem_centralizer_singleton_iff, hx]
  have := hk₂ m hm
  calc m * P.x₂⁻¹ = P.x₂⁻¹ * (P.x₂ * m) * P.x₂⁻¹ := by group
    _ = P.x₂⁻¹ * (m * P.x₂) * P.x₂⁻¹ := by rw [this]
    _ = P.x₂⁻¹ * m := by group

theorem card_lt (hZ : Subgroup.center G = ⊥) : Nat.card ↥(P.T₀ ⊔ P.T₁) < Nat.card G := by
  have hne : P.T₀ ⊔ P.T₁ ≠ ⊤ := by
    intro htop
    have hcen : P.x₀ * P.x₁ * P.x₂ ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ P.T₀ ⊔ P.T₁ := by
        rw [htop]
        exact Subgroup.mem_top g
      exact P.mem_centralizer_h hg
    rw [hZ, Subgroup.mem_bot] at hcen
    exact P.h_ne_one hcen
  have h1 := Subgroup.card_mul_index (P.T₀ ⊔ P.T₁)
  have h2 : 1 < (P.T₀ ⊔ P.T₁).index := Subgroup.one_lt_index_of_ne_top hne
  have h3 : 0 < Nat.card ↥(P.T₀ ⊔ P.T₁) := Nat.card_pos
  calc Nat.card ↥(P.T₀ ⊔ P.T₁) = Nat.card ↥(P.T₀ ⊔ P.T₁) * 1 := (mul_one _).symm
    _ < Nat.card ↥(P.T₀ ⊔ P.T₁) * (P.T₀ ⊔ P.T₁).index := Nat.mul_lt_mul_of_pos_left h2 h3
    _ = Nat.card G := h1

end LeviParams

end Levi

end CFSG.ClassicalInvolution.RouteD
