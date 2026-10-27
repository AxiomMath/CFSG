module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.StandardHypA

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

@[expose] def IsLayerInvolutionAut {T : Type*} [Group T] (m : ℕ) (α : MulAut T) : Prop :=
  α * α = 1 ∧ (Nat.card {g : T // α g = g} ≤ 2 ∨
    (m ≤ Nat.card {g : T // α g = g} ∧ Nat.card {g : T // α g = g} ≤ 2 * m ∧
      (Nat.card {g : T // α g = g} = 2 * m → ∃ s : T, α = MulAut.conj s)))

theorem exists_mulAut_of_normal {Y T : Type*} [Group Y] [Group T] {E : Subgroup Y} [E.Normal]
    (e : E ≃* T) {t : Y} (ht : t ^ 2 = 1) :
    ∃ α : MulAut T, α * α = 1 ∧
      Nat.card {g : T // α g = g} = Nat.card (E ⊓ centralizer ({t} : Set Y) : Subgroup Y) ∧
      (t ∈ E → ∃ s : T, α = MulAut.conj s) := by
  refine ⟨MulAut.congr e (MulAut.conjNormal t), ?_, ?_, fun htE => ⟨e ⟨t, htE⟩, ?_⟩⟩
  · rw [← map_mul, ← map_mul, ← sq, ht, map_one, map_one]
  · have hfix : ∀ g : T, MulAut.congr e (MulAut.conjNormal t) g = g ↔
        ((e.symm g : E) : Y) ∈ centralizer ({t} : Set Y) := by
      intro g
      rw [mem_centralizer_singleton_iff]
      change e (MulAut.conjNormal t (e.symm g)) = g ↔ _
      rw [← MulEquiv.eq_symm_apply, ← Subtype.coe_inj, MulAut.conjNormal_apply,
        mul_inv_eq_iff_eq_mul, eq_comm]
    exact Nat.card_congr ((e.symm.toEquiv.subtypeEquiv
      (q := fun x : E => (x : Y) ∈ centralizer ({t} : Set Y)) hfix).trans
      { toFun := fun x => ⟨x.1.1, mem_inf.2 ⟨x.1.2, x.2⟩⟩
        invFun := fun y => ⟨⟨y.1, (mem_inf.1 y.2).1⟩, (mem_inf.1 y.2).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
  · ext g
    change ((e (MulAut.conjNormal t (e.symm g)) : T)) = e ⟨t, htE⟩ * g * (e ⟨t, htE⟩)⁻¹
    have h : MulAut.conjNormal t (e.symm g) = ⟨t, htE⟩ * e.symm g * (⟨t, htE⟩ : E)⁻¹ :=
      Subtype.ext (by rw [MulAut.conjNormal_apply]; rfl)
    rw [h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem exists_isLayerInvolutionAut_of_mulEquiv {X : Type} [Group X] [Finite X] {z : X}
    {H : Subgroup X} [IsSimpleGroup H] (hnab : ∃ a b : H, a * b ≠ b * a) (hz : orderOf z = 2)
    (hC : centralizer ({z} : Set X) = H ⊔ zpowers z) (hz' : z ∈ centralizer (H : Set X))
    {T : Type*} [Group T] (e : egaLayer (X ⧸ fusionOddCore X) ≃* T) :
    ∃ α : MulAut T, IsLayerInvolutionAut (Nat.card H) α := by
  have ht : QuotientGroup.mk' (fusionOddCore X) z ^ 2 = 1 := by
    rw [← map_pow, ← hz, pow_orderOf_eq_one, map_one]
  obtain ⟨α, hα, hcard, hinner⟩ := exists_mulAut_of_normal e ht
  refine ⟨α, hα, ?_⟩
  rw [hcard]
  rcases card_inf_centralizer_mk_le_two_or hnab hz hC hz' (egaLayer_normal _) with
    h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, fun h40 => hinner (h3 h40)⟩

theorem not_nonempty_layer_of_forall_not {X : Type} [Group X] [Finite X] {z : X}
    {H : Subgroup X} [IsSimpleGroup H] (hnab : ∃ a b : H, a * b ≠ b * a) (hz : orderOf z = 2)
    (hC : centralizer ({z} : Set X) = H ⊔ zpowers z) (hz' : z ∈ centralizer (H : Set X))
    {T : Type*} [Group T] (hT : ∀ α : MulAut T, ¬ IsLayerInvolutionAut (Nat.card H) α) :
    ¬ Nonempty (egaLayer (X ⧸ fusionOddCore X) ≃* T) := by
  rintro ⟨e⟩
  obtain ⟨α, hα⟩ := exists_isLayerInvolutionAut_of_mulEquiv hnab hz hC hz' e
  exact hT α hα

theorem not_nonempty_layer_of_alt8 {X : Type} [Group X] [Finite X] {z : X} {H : Subgroup X}
    (hz : orderOf z = 2) (hH : Nonempty (H ≃* alternatingGroup (Fin 8)))
    (hC : centralizer ({z} : Set X) = H ⊔ zpowers z) (hz' : z ∈ centralizer (H : Set X))
    {T : Type*} [Group T] (hT : ∀ α : MulAut T, ¬ IsLayerInvolutionAut 20160 α) :
    ¬ Nonempty (egaLayer (X ⧸ fusionOddCore X) ≃* T) := by
  obtain ⟨e⟩ := hH
  obtain ⟨hs, hnab⟩ := isSimpleGroup_and_not_comm_of_mulEquiv_alt8 e
  have hcard : Nat.card H = 20160 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  exact not_nonempty_layer_of_forall_not hnab hz hC hz' (hcard ▸ hT)

theorem card_mem_of_normal_centralizer_mk_alt8 {X : Type*} [Group X] [Finite X] {z : X}
    {H : Subgroup X} (hz : orderOf z = 2) (hH : Nonempty (H ≃* alternatingGroup (Fin 8)))
    (hC : centralizer ({z} : Set X) = H ⊔ zpowers z) (hz' : z ∈ centralizer (H : Set X))
    {K : Subgroup (X ⧸ fusionOddCore X)}
    (hK : K ≤ centralizer ({QuotientGroup.mk' (fusionOddCore X) z} : Set (X ⧸ fusionOddCore X)))
    (hKn : (K.subgroupOf (centralizer ({QuotientGroup.mk' (fusionOddCore X) z} :
      Set (X ⧸ fusionOddCore X)))).Normal) :
    Nat.card K ∈ ({1, 2, 20160, 40320} : Finset ℕ) := by
  obtain ⟨e⟩ := hH
  obtain ⟨hs, hnab⟩ := isSimpleGroup_and_not_comm_of_mulEquiv_alt8 e
  obtain ⟨hHq, hZ⟩ := isQuasisimple_center_eq_bot_of_isSimpleGroup hnab
  obtain ⟨eH⟩ := nonempty_map_fusionOddCore_mulEquiv (disjoint_fusionOddCore hHq hZ)
  have : IsSimpleGroup (H.map (QuotientGroup.mk' (fusionOddCore X))) := eH.isSimpleGroup
  have hcard : Nat.card (H.map (QuotientGroup.mk' (fusionOddCore X))) = 20160 := by
    rw [Nat.card_congr (eH.trans e).toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  have ht : QuotientGroup.mk' (fusionOddCore X) z ^ 2 = 1 := by
    rw [← map_pow, ← hz, pow_orderOf_eq_one, map_one]
  have ht' : QuotientGroup.mk' (fusionOddCore X) z ∈
      centralizer ((H.map (QuotientGroup.mk' (fusionOddCore X)) : Subgroup _) :
        Set (X ⧸ fusionOddCore X)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hz' h hh]
  have hC' := centralizer_mk_fusionOddCore_eq hz hC hz'
  have hHC : H.map (QuotientGroup.mk' (fusionOddCore X)) ≤
      centralizer ({QuotientGroup.mk' (fusionOddCore X) z} : Set (X ⧸ fusionOddCore X)) :=
    hC' ▸ le_sup_left
  have h := card_le_two_or_of_le_sup_zpowers ht ht' (hC' ▸ hK)
    (fun h hh k hk => (normal_subgroupOf_iff hK).1 hKn k h hk (hHC hh))
  rw [hcard] at h
  have h0 : 0 < Nat.card K := Nat.card_pos
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

end CFSG.EvenSporadicStandard.M24Std
