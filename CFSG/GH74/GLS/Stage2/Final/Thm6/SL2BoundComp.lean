module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.SL2BoundGrp
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound

open Subgroup Matrix CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage2.Local
open CFSG.GH74.GLS.Bg (Em)


section Bar

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem mem_barOf_iff {K : Subgroup G} (hK : K ≤ Cen z) {x : CentralizerBar z} :
    x ∈ barOf z K ↔ ∃ (k : G) (hk : k ∈ K), toBar z ⟨k, hK hk⟩ = x := by
  unfold barOf
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hK hk⟩, hk, rfl⟩

theorem toBar_inclusion_injective {K : Subgroup G} (hK : K ≤ Cen z) {F : Type} [Field F] [Finite F]
    (e : ↥K ≃* SpecialLinearGroup (Fin 2) F) (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) :
    Function.Injective ((toBar z).comp (Subgroup.inclusion hK)) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have hmem : Subgroup.inclusion hK k ∈ pPrimeCore 2 ↥(Cen z) :=
    (QuotientGroup.eq_one_iff _).1 hk
  let NK : Subgroup ↥K := (pPrimeCore 2 ↥(Cen z)).comap (Subgroup.inclusion hK)
  have hNKn : NK.Normal := (pPrimeCore_normal (p := 2) (G := ↥(Cen z))).comap _
  have hle : NK.map (Subgroup.inclusion hK) ≤ pPrimeCore 2 ↥(Cen z) := Subgroup.map_comap_le _ _
  have hinj : Function.Injective (Subgroup.inclusion hK) := Subgroup.inclusion_injective hK
  have hcop : Nat.Coprime 2 (Nat.card NK) := by
    have h1 : Nat.card NK = Nat.card (NK.map (Subgroup.inclusion hK)) :=
      (Subgroup.card_map_of_injective hinj).symm
    rw [h1]
    exact (pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z))).coprime_dvd_right
      (Subgroup.card_dvd_of_le hle)
  have hbot : NK = ⊥ :=
    (pPrimeCore_eq_bot_iff.1 (SL2Bound.pPrimeCore_eq_bot_of_equiv e hodd h3)) NK hNKn hcop
  have hk' : k ∈ NK := hmem
  rw [hbot] at hk'
  exact hk'


noncomputable def barEquiv {K : Subgroup G} (hK : K ≤ Cen z) {F : Type} [Field F] [Finite F]
    (e : ↥K ≃* SpecialLinearGroup (Fin 2) F) (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) :
    ↥K ≃* ↥(barOf z K) :=
  (MonoidHom.ofInjective (toBar_inclusion_injective hK e hodd h3)).trans
    (MulEquiv.subgroupCongr (by
      ext x
      rw [MonoidHom.mem_range, mem_barOf_iff hK]
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨k, k.2, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨⟨k, hk⟩, rfl⟩))

theorem isQuasisimple_barOf {K : Subgroup G} (hK : K ≤ Cen z) {F : Type} [Field F] [Finite F]
    (e : ↥K ≃* SpecialLinearGroup (Fin 2) F) (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) :
    IsQuasisimple ↥(barOf z K) := by
  have hq : IsQuasisimple ↥K :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (IVK.Lifted.isQuasisimple_sl2' (K := F) (by have := five_le_card_of_odd_gt3 hodd h3; omega))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (barEquiv hK e hodd h3) hq

omit [Finite G] in
theorem isSubnormal_of_comm_normal' {Γ : Type} [Group Γ] {A B : Subgroup Γ}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hN : (A ⊔ B).Normal) : A.IsSubnormal := by
  have hAN : (A.subgroupOf (A ⊔ B)).Normal := by
    constructor
    intro n hn g
    obtain ⟨g, hg⟩ := g
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hcomm hg
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have e : a * b * (n : Γ) * (a * b)⁻¹ = a * n * a⁻¹ := by
      have hbn : b * (n : Γ) = (n : Γ) * b := (hcomm n hn b hb).symm
      calc a * b * (n : Γ) * (a * b)⁻¹ = a * (b * n * b⁻¹) * a⁻¹ := by group
        _ = a * n * a⁻¹ := by rw [hbn]; group
    show a * b * (n : Γ) * (a * b)⁻¹ ∈ A
    rw [e]
    exact A.mul_mem (A.mul_mem ha hn) (A.inv_mem ha)
  exact Subgroup.IsSubnormal.trans le_sup_left hAN.isSubnormal hN.isSubnormal

omit [Finite G] in
theorem barOf_Em_normal : (barOf z (Em (Cen z))).Normal := by
  have hc : (layer ↥(Cen z)).Characteristic := CFSG.LocalCores.layer_characteristic
  have hn : (layer ↥(Cen z)).Normal := inferInstance
  have h : (Em (Cen z)).subgroupOf (Cen z) = layer ↥(Cen z) := by
    unfold Em inSubgroup
    exact Subgroup.comap_map_eq_self_of_injective (Cen z).subtype_injective _
  unfold barOf
  rw [h]
  exact hn.map _ (QuotientGroup.mk'_surjective _)


theorem barOf_mem_pair {S : Subgroup G} {ε : Bool} {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (h : Stage1L4 G z S ε q L₁ L₂) {K₁ K₂ : Subgroup G} (hcp : IsCentralProd K₁ K₂ (Em (Cen z)))
    {F : Type} [Field F] [Finite F] (e : ↥K₁ ≃* SpecialLinearGroup (Fin 2) F)
    (hFq : Nat.card F = q) :
    barOf z K₁ = L₁ ∨ barOf z K₁ = L₂ := by
  have hodd : Odd (Nat.card F) := hFq ▸ h.pair.odd
  have h3 : 3 < Nat.card F := hFq ▸ h.pair.gt3
  have hE : Em (Cen z) ≤ Cen z := Subgroup.map_subtype_le _
  have hK₁E : K₁ ≤ Em (Cen z) := hcp.1 ▸ le_sup_left
  have hK₂E : K₂ ≤ Em (Cen z) := hcp.1 ▸ le_sup_right
  have hK₁C : K₁ ≤ Cen z := hK₁E.trans hE
  have hK₂C : K₂ ≤ Cen z := hK₂E.trans hE
  have hsup : barOf z K₁ ⊔ barOf z K₂ = barOf z (Em (Cen z)) := by
    conv_rhs => rw [← hcp.1]
    unfold barOf
    rw [Subgroup.subgroupOf_sup hK₁C hK₂C, Subgroup.map_sup]
  have hcomm : ∀ a ∈ barOf z K₁, ∀ b ∈ barOf z K₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k₁, hk₁, rfl⟩ := (mem_barOf_iff hK₁C).1 ha
    obtain ⟨k₂, hk₂, rfl⟩ := (mem_barOf_iff hK₂C).1 hb
    have hc := hcp.2.1 k₁ hk₁ k₂ hk₂
    rw [← map_mul, ← map_mul]
    exact congrArg (toBar z) (Subtype.ext hc)
  have hNormal : (barOf z K₁ ⊔ barOf z K₂).Normal := by
    rw [hsup]
    exact barOf_Em_normal
  have hsub : (barOf z K₁).IsSubnormal := isSubnormal_of_comm_normal' hcomm hNormal
  have hcomp : IsComponent (barOf z K₁) := ⟨isQuasisimple_barOf hK₁C e hodd h3, hsub⟩
  have hmem : barOf z K₁ ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := hcomp
  rw [h.pair.comps] at hmem
  simpa using hmem

end Bar

end CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound
