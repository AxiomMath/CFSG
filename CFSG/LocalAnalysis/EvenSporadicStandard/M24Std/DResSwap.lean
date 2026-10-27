module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResProd
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerD3Alt8

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup CFSG.Open
open scoped commutatorElement

theorem exists_mulAut_of_normal' {Y T : Type*} [Group Y] [Group T] {E : Subgroup Y} [E.Normal]
    (e : E ≃* T) {t : Y} (ht : t ^ 2 = 1) :
    ∃ α : MulAut T, α * α = 1 ∧
      (∀ g : E, ∀ hg : t * (g : Y) * t⁻¹ ∈ E, α (e g) = e ⟨t * g * t⁻¹, hg⟩) ∧
      Nat.card {g : T // α g = g} = Nat.card (E ⊓ centralizer ({t} : Set Y) : Subgroup Y) := by
  refine ⟨MulAut.congr e (MulAut.conjNormal t), ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, ← sq, ht, map_one, map_one]
  · intro g hg
    change e (MulAut.conjNormal t (e.symm (e g))) = _
    rw [MulEquiv.symm_apply_apply]
    congr 1
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


open Equiv in
theorem swap_of_card_mem (α : MulAut (alternatingGroup (Fin 8) × alternatingGroup (Fin 8)))
    (hα : α * α = 1)
    (hcard : Nat.card {g // α g = g} ∈ ({1, 2, 20160, 40320} : Finset ℕ)) :
    ∃ f₁ f₂ : MulAut (alternatingGroup (Fin 8)), (∀ a b, α (a, b) = (f₁ b, f₂ a)) ∧
      (∀ b, f₂ (f₁ b) = b) ∧ Nat.card {g // α g = g} = 20160 := by
  rcases ProdAut.mulAut_prod_cases alt8_hsimple (fun _ => alt8_central) alt8_nontrivial α with
    ⟨hp1, hp2⟩ | ⟨hs1, hs2⟩
  · exfalso
    obtain ⟨f₁, f₂, hf⟩ := ProdAut.exists_prod_preserve α hp1 hp2
    have hff : ∀ a b, (f₁ (f₁ a), f₂ (f₂ b)) = (a, b) := by
      intro a b
      have := congrArg (fun β : MulAut (alternatingGroup (Fin 8) × alternatingGroup (Fin 8)) =>
        β (a, b)) hα
      simpa [MulAut.mul_apply, hf] using this
    have hf1 : f₁ * f₁ = 1 := MulEquiv.ext fun a => by
      simpa using (Prod.ext_iff.1 (hff a 1)).1
    have hf2 : f₂ * f₂ = 1 := MulEquiv.ext fun b => by
      simpa using (Prod.ext_iff.1 (hff 1 b)).2
    obtain ⟨σ₁, hσ₁, hσ₁'⟩ :=
      exists_perm_sq_eq_one_of_mulAut_alternatingGroup (Or.inr (by norm_num)) f₁ hf1
    obtain ⟨σ₂, hσ₂, hσ₂'⟩ :=
      exists_perm_sq_eq_one_of_mulAut_alternatingGroup (Or.inr (by norm_num)) f₂ hf2
    have c1 := card_alternatingGroup_inf_centralizer_eight hσ₁
    have c2 := card_alternatingGroup_inf_centralizer_eight hσ₂
    rw [← card_fixed_mulAut_alternatingGroup hσ₁'] at c1
    rw [← card_fixed_mulAut_alternatingGroup hσ₂'] at c2
    have hprod : Nat.card {g // α g = g} =
        Nat.card {a // f₁ a = a} * Nat.card {b // f₂ b = b} := by
      rw [← Nat.card_prod]
      refine Nat.card_congr
        { toFun := fun g => (⟨g.1.1, ?_⟩, ⟨g.1.2, ?_⟩)
          invFun := fun p => ⟨(p.1.1, p.2.1), ?_⟩
          left_inv := fun g => rfl
          right_inv := fun p => rfl }
      · have := congrArg Prod.fst g.2
        simpa [hf] using this
      · have := congrArg Prod.snd g.2
        simpa [hf] using this
      · rw [hf, p.1.2, p.2.2]
    simp only [Finset.mem_insert, Finset.mem_singleton] at c1 c2 hcard
    rw [hprod] at hcard
    rcases c1 with h | h | h | h | h <;> rcases c2 with h' | h' | h' | h' | h' <;>
      rw [h, h'] at hcard <;> omega
  · obtain ⟨f₁, f₂, hf⟩ := ProdAut.exists_prod_swap α hs1 hs2
    have hf21 : ∀ b, f₂ (f₁ b) = b := by
      intro b
      have := congrArg (fun β : MulAut (alternatingGroup (Fin 8) × alternatingGroup (Fin 8)) =>
        β (1, b)) hα
      simpa [MulAut.mul_apply, hf] using (Prod.ext_iff.1 this).2
    refine ⟨f₁, f₂, hf, hf21, ?_⟩
    rw [← card_alt8]
    refine Nat.card_congr
      { toFun := fun g => g.1.2
        invFun := fun b => ⟨(f₁ b, b), by rw [hf, hf21]⟩
        left_inv := fun g => ?_
        right_inv := fun b => rfl }
    obtain ⟨⟨a, b⟩, hg⟩ := g
    have h1 := congrArg Prod.fst hg
    simp only [hf] at h1
    apply Subtype.ext
    simp only
    rw [h1]

section LayerHyp

variable {Y : Type} [Group Y] [Finite Y] {t : Y} {H : Subgroup Y}

abbrev Yb (Y : Type) [Group Y] [Finite Y] : Type := Y ⧸ fusionOddCore Y

abbrev proj (Y : Type) [Group Y] [Finite Y] : Y →* Yb Y := QuotientGroup.mk' (fusionOddCore Y)

structure LayerHyp (t : Y) (H : Subgroup Y) : Prop where
  order : orderOf t = 2
  iso : Nonempty (H ≃* alternatingGroup (Fin 8))
  cent : centralizer ({t} : Set Y) = H ⊔ zpowers t
  comm : t ∈ centralizer (H : Set Y)

omit [Finite Y] in
theorem LayerHyp.simple (hY : LayerHyp t H) :
    IsSimpleGroup H ∧ ∃ a b : H, a * b ≠ b * a := by
  obtain ⟨e⟩ := hY.iso
  exact isSimpleGroup_and_not_comm_of_mulEquiv_alt8 e

theorem LayerHyp.proj_sq (hY : LayerHyp t H) : proj Y t ^ 2 = 1 := by
  rw [← map_pow, ← hY.order, pow_orderOf_eq_one, map_one]

structure IsSwap (t : Y)
    (e : egaLayer (Yb Y) ≃* alternatingGroup (Fin 8) × alternatingGroup (Fin 8))
    (f₁ f₂ : MulAut (alternatingGroup (Fin 8))) : Prop where
  conj : ∀ g : egaLayer (Yb Y), e ⟨proj Y t * g * (proj Y t)⁻¹,
    (egaLayer_normal _).conj_mem _ g.2 _⟩ = (f₁ (e g).2, f₂ (e g).1)
  inv : ∀ b, f₂ (f₁ b) = b

theorem LayerHyp.swap (hY : LayerHyp t H)
    (e : egaLayer (Yb Y) ≃* alternatingGroup (Fin 8) × alternatingGroup (Fin 8)) :
    ∃ f₁ f₂ : MulAut (alternatingGroup (Fin 8)), IsSwap t e f₁ f₂ ∧
      Nat.card (egaLayer (Yb Y) ⊓ centralizer ({proj Y t} : Set (Yb Y)) :
        Subgroup (Yb Y)) = 20160 := by
  have := (egaLayer_normal (Yb Y))
  obtain ⟨α, hαα, hαe, hαcard⟩ := exists_mulAut_of_normal' e hY.proj_sq
  have hmem := card_mem_of_normal_centralizer_mk_alt8 hY.order hY.iso hY.cent hY.comm
    (K := egaLayer (Yb Y) ⊓ centralizer ({proj Y t} : Set (Yb Y)))
    inf_le_right (inf_centralizer_subgroupOf_normal (egaLayer_normal _) _)
  rw [← hαcard] at hmem
  obtain ⟨f₁, f₂, hf, hinv, hc⟩ := swap_of_card_mem α hαα hmem
  refine ⟨f₁, f₂, ⟨fun g => ?_, hinv⟩, hαcard ▸ hc⟩
  rw [← hαe g, hf]

theorem LayerHyp.map_eq (hY : LayerHyp t H)
    (hc : Nat.card (egaLayer (Yb Y) ⊓ centralizer ({proj Y t} : Set (Yb Y)) :
      Subgroup (Yb Y)) = 20160) :
    H.map (proj Y) = egaLayer (Yb Y) ⊓ centralizer ({proj Y t} : Set (Yb Y)) := by
  obtain ⟨hs, hnab⟩ := hY.simple
  have hHE := map_le_of_two_lt_card_inf_centralizer hnab hY.order hY.cent hY.comm
    (egaLayer_normal _) (by rw [hc]; norm_num)
  obtain ⟨-, -, hHcard, -, -, hC'⟩ := quotient_facts_of_centralizer_eq hnab hY.order hY.cent hY.comm
  have hle : H.map (proj Y) ≤ egaLayer (Yb Y) ⊓ centralizer ({proj Y t} : Set (Yb Y)) :=
    le_inf hHE (hC' ▸ le_sup_left)
  obtain ⟨eH⟩ := hY.iso
  refine eq_of_le_of_card_ge hle ?_
  rw [hc, hHcard, Nat.card_congr eH.toEquiv, card_alt8]

theorem LayerHyp.exists_diag (hY : LayerHyp t H)
    (e : egaLayer (Yb Y) ≃* alternatingGroup (Fin 8) × alternatingGroup (Fin 8))
    {f₁ f₂ : MulAut (alternatingGroup (Fin 8))} (hsw : IsSwap t e f₁ f₂)
    (hc : Nat.card (egaLayer (Yb Y) ⊓ centralizer ({proj Y t} : Set (Yb Y)) :
      Subgroup (Yb Y)) = 20160) (b : alternatingGroup (Fin 8)) :
    ∃ h ∈ H, ∃ hh : proj Y h ∈ egaLayer (Yb Y), e ⟨proj Y h, hh⟩ = (f₁ b, b) := by
  have hmem : ((e.symm (f₁ b, b) : egaLayer (Yb Y)) : Yb Y) ∈
      H.map (proj Y) := by
    rw [hY.map_eq hc]
    refine mem_inf.2 ⟨(e.symm (f₁ b, b)).2, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := hsw.conj (e.symm (f₁ b, b))
    rw [MulEquiv.apply_symm_apply, hsw.inv] at h1
    have h2 : (⟨proj Y t * ((e.symm (f₁ b, b) : egaLayer (Yb Y)) : Yb Y) * (proj Y t)⁻¹,
        (egaLayer_normal _).conj_mem _ (e.symm (f₁ b, b)).2 _⟩ : egaLayer (Yb Y)) =
        e.symm (f₁ b, b) := by
      apply e.injective
      rw [h1, MulEquiv.apply_symm_apply]
    have h3 := congrArg Subtype.val h2
    simp only at h3
    calc (e.symm (f₁ b, b) : Yb Y) * proj Y t
        = proj Y t * (e.symm (f₁ b, b) : Yb Y) * (proj Y t)⁻¹ * proj Y t := by rw [h3]
      _ = proj Y t * (e.symm (f₁ b, b) : Yb Y) := by group
  obtain ⟨h, hh, hhe⟩ := mem_map.1 hmem
  refine ⟨h, hh, hhe ▸ (e.symm (f₁ b, b)).2, ?_⟩
  apply e.symm.injective
  rw [MulEquiv.symm_apply_apply]
  exact Subtype.ext hhe

end LayerHyp

end CFSG.EvenSporadicStandard.M24Std.DRes
