module

public import CFSG.Quasithin.H13.A5X1367e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5X1367d

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative commutatorElement

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_case2_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    (hVv : ¬ Subgroup.centralizer ({S.v12} : Set G) ≤ Subgroup.normalizer (S.Vv : Set G))
    {J : Subgroup (MulAut ↥S.Uv)}
    (hJG : J ≤ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)
    (hGJ : autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv ≤
      Subgroup.normalizer (J : Set (MulAut ↥S.Uv)))
    (h2 : haveI : IsMulCommutative ↥S.Uv := (S.elemAbelian_Uv_F4 h1222 h517 hF).1
      B56Case2 J) : False := by
  have hUe := S.elemAbelian_Uv_F4 h1222 h517 hF
  have : IsMulCommutative ↥S.Uv := hUe.1
  obtain ⟨⟨e⟩, ⟨hsup, hinf⟩, hcard⟩ := h2
  have hsq : ∀ a : ↥S.Uv, a * a = 1 := fun a => by
    have h := hUe.2 (a : G) a.2
    exact Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, h, Subgroup.coe_one])
  have hdec : ∀ u : ↥S.Uv, ∃ a ∈ commV J, ∃ w ∈ fixV J, u = a * w := by
    intro u
    have hu : u ∈ commV J ⊔ fixV J := by rw [hsup]; exact Subgroup.mem_top u
    obtain ⟨a, ha, w, hw, h⟩ := Subgroup.mem_sup.mp hu
    exact ⟨a, ha, w, hw, h.symm⟩

  set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 with hσ
  set τ : Equiv.Perm (Fin 3) := Equiv.swap 1 2 with hτ
  set y₀ : MulAut ↥S.Uv := ⁅((e.symm σ : ↥J) : MulAut ↥S.Uv), ((e.symm τ : ↥J) : MulAut ↥S.Uv)⁆
    with hy₀
  have hy₀Y : y₀ ∈ ⁅J, J⁆ := Subgroup.commutator_mem_commutator (e.symm σ).2 (e.symm τ).2
  have hy₀J : y₀ = ((e.symm ⁅σ, τ⁆ : ↥J) : MulAut ↥S.Uv) := by
    rw [map_commutatorElement, hy₀]
    rfl
  have hy₀1 : y₀ ≠ 1 := by
    rw [hy₀J]
    intro h
    have h1 : e.symm ⁅σ, τ⁆ = 1 := Subtype.ext h
    have h2 : ⁅σ, τ⁆ = 1 := e.symm.injective (h1.trans (map_one e.symm).symm)
    exact absurd h2 (by decide)
  have hy₀3 : orderOf y₀ = 3 := by
    rw [hy₀J, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by decide) (by decide)

  have hy₀U : ∃ u ∈ commV J, y₀ u ≠ u := by
    by_contra hcon
    push Not at hcon
    apply hy₀1
    ext u
    obtain ⟨a, ha, w, hw, rfl⟩ := hdec u
    rw [map_mul, hcon a ha, (fixV J).mem_carrier.mp hw y₀ (commutator_self_le J hy₀Y),
      MulAut.one_apply]

  have hsylJ := A4.isSylowTwoOf_inf_normal (S.isSylowTwoOf_TvS_F4 h1222 h517) hJG hGJ
  have hJ6 : Nat.card ↥J = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  obtain ⟨s, hsTJ, hs1⟩ : ∃ s ∈ autOn S.Tv S.Uv ⊓ J, s ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : autOn S.Tv S.Uv ⊓ J = ⊥ := eq_bot_iff.mpr fun x hx => hcon x hx
    have h : ¬ 2 ∣ (autOn S.Tv S.Uv ⊓ J).relIndex J := hsylJ.2.2
    rw [hbot, Subgroup.relIndex_bot_left, hJ6] at h
    exact h (by norm_num)
  have hsU : ∃ u ∈ commV J, s u ≠ u := by
    by_contra hcon
    push Not at hcon
    apply hs1
    ext u
    obtain ⟨a, ha, w, hw, rfl⟩ := hdec u
    rw [map_mul, hcon a ha, (fixV J).mem_carrier.mp hw s hsTJ.2, MulAut.one_apply]
  apply hVv
  refine S.le_normalizer_Vv_of_three hUe (Y := ⁅J, J⁆) ((commutator_self_le J).trans hJG)
    (hGJ.trans (normalizer_le_normalizer_commutator J))
    (fun h => hy₀1 ((Subgroup.mem_bot).mp (h ▸ hy₀Y))) hcard hdec hinf
    (fun y hy w hw => hw y (commutator_self_le J hy)) ?_
    (fun g hg u hu => commV_apply_of_normalizer (hGJ hg) hu)
    (fun g hg w hw => fixV_apply_of_normalizer (hGJ hg) hw) hsTJ.1
    (fun w hw => hw s hsTJ.2) hsU
  intro u hu hfix
  by_contra hu1
  have hy₀odd : Odd (orderOf y₀) := by rw [hy₀3]; decide
  exact four_odd_nofix hcard (fun e _ => hsq e)
    (fun x hx => commV_apply_of_normalizer (hGJ (hJG (commutator_self_le J hy₀Y))) hx)
    hy₀odd hy₀U hu hu1 (hfix y₀ hy₀Y)

end Setting

end CFSG.Quasithin.H13.A5
