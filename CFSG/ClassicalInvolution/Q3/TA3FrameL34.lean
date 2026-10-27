module

public import CFSG.ClassicalInvolution.Q3.TA3FrameL34Fix
public import CFSG.ClassicalInvolution.Q3.TA3FrameL34Mod
public import CFSG.ClassicalInvolution.Q3.TA3FrameLayer

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.Q3T.MFS
  CFSG.ComponentClassification.PSL3Four

variable {Y : Type} [Group Y] [Finite Y] {z : Y} {L T : Subgroup Y}

theorem false_of_l34 [T.Normal] (hL : IsClassicalMember3 L z) (hTL : T ⊔ L = ⊤)
    (h3 : memberIndex L T = 3) (hC : Subgroup.centralizer (T : Set Y) = ⊥)
    (hT : Blueprint.LieModel ↥T .PSL 3 2 2) : False := by
  obtain ⟨e⟩ := CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel hT
  set zT : T := ⟨z, mem_of_member hL hTL h3⟩ with hzT
  have hs2 : orderOf ((e zT : S) : Equiv.Perm (Fin 42)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hzT, Subgroup.orderOf_mk]
    exact hL.orderOf_eq_two
  have hPc : Nat.card ↥(T ⊓ Subgroup.centralizer ({z} : Set Y)) = 64 := by
    have h1 : (Subgroup.centralizer ({zT} : Set T)).map T.subtype =
        T ⊓ Subgroup.centralizer ({z} : Set Y) := map_centralizer_subtype
    have h2 : (Subgroup.centralizer ({e zT} : Set S)).map S.subtype =
        S ⊓ Subgroup.centralizer ({((e zT : S) : Equiv.Perm (Fin 42))} :
          Set (Equiv.Perm (Fin 42))) := map_centralizer_subtype
    calc Nat.card ↥(T ⊓ Subgroup.centralizer ({z} : Set Y)) =
          Nat.card (Subgroup.centralizer ({zT} : Set T)) := by
          rw [← h1, Subgroup.card_map_of_injective T.subtype_injective]
      _ = Nat.card (Subgroup.centralizer ({e zT} : Set S)) := by
          rw [← map_centralizer e zT, Subgroup.card_map_of_injective (f := e.symm.toMonoidHom)
            e.symm.injective]
      _ = 64 := by
          rw [← Subgroup.card_map_of_injective S.subtype_injective, h2]
          exact L34.card_centralizer (e zT).2 hs2
  have hP2 : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer ({z} : Set Y)) :=
    IsPGroup.of_card (n := 6) (by rw [hPc]; norm_num)
  refine false_of_fix_le_four hL h3 hP2 hPc.ge fun y hyT hy3 hyz => ?_
  set α : MulAut T := MulAut.conjNormal y with hα
  set β : MulAut S := MulAut.congr e α with hβ
  obtain ⟨ρ, hρ⟩ := conjAutS_surjective β
  have hαx : ∀ x : T, (α x : Y) = y * x * y⁻¹ := fun x => MulAut.conjNormal_apply y x
  have hβx : ∀ x : T, β (e x) = e (α x) := fun x => by simp [hβ, MulAut.congr_apply]
  have hρ3 : ρ ^ 3 = 1 := by
    apply conjAutS_injective
    rw [map_pow, hρ, map_one, hβ, ← map_pow, hα, ← map_pow, hy3, map_one, map_one]
  have hρ1 : ρ ≠ 1 := by
    intro h1
    apply hyT
    have hα1 : α = 1 := (MulAut.congr e).injective (by rw [← hβ, ← hρ, h1, map_one, map_one])
    have hyC : y ∈ Subgroup.centralizer (T : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have h2 := hαx ⟨t, ht⟩
      rw [hα1, MulAut.one_apply] at h2
      calc t * y = y * t * y⁻¹ * y := by rw [← h2]
        _ = y * t := by group
    rw [hC, Subgroup.mem_bot] at hyC
    rw [hyC]
    exact T.one_mem
  have hfixr : ∀ x : T, α x = x → ((ρ : R) : Equiv.Perm (Fin 42)) * (e x : S) =
      (e x : S) * ((ρ : R) : Equiv.Perm (Fin 42)) := by
    intro x hx
    have h2 := conjAutS_apply ρ (e x)
    rw [hρ, hβx, hx] at h2
    calc ((ρ : R) : Equiv.Perm (Fin 42)) * (e x : S) =
        ((ρ : R) : Equiv.Perm (Fin 42)) * (e x : S) * ((ρ : R) : Equiv.Perm (Fin 42))⁻¹ *
          ((ρ : R) : Equiv.Perm (Fin 42)) := by group
      _ = (e x : S) * ((ρ : R) : Equiv.Perm (Fin 42)) := by rw [← h2]
  have hαz : α zT = zT := Subtype.ext (by
    rw [hαx]
    change y * z * y⁻¹ = z
    rw [hyz, mul_inv_cancel_right])
  set Q := (T ⊓ Subgroup.centralizer ({z} : Set Y)) ⊓
    Subgroup.centralizer (Subgroup.zpowers y : Set Y) with hQ
  have hQT : Q ≤ T := inf_le_left.trans inf_le_left
  set W := (Q.subgroupOf T).map (S.subtype.comp e.toMonoidHom) with hW
  have hWc : Nat.card W = Nat.card Q := by
    rw [Subgroup.card_map_of_injective (f := S.subtype.comp e.toMonoidHom)
      (S.subtype_injective.comp e.injective)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQT).toEquiv
  have hWS : W ≤ S := by
    rintro _ ⟨x, -, rfl⟩
    exact (e x).2
  have hW2 : IsPGroup 2 W := by
    obtain ⟨n, hn⟩ := (hP2.to_le (inf_le_left : Q ≤ _)).exists_card_eq
    exact IsPGroup.of_card (by rw [hWc, hn])
  have hWr : ∀ w ∈ W,
      w * ((ρ : R) : Equiv.Perm (Fin 42)) = ((ρ : R) : Equiv.Perm (Fin 42)) * w := by
    rintro _ ⟨x, hx, rfl⟩
    have hxQ : (x : Y) ∈ Q := hx
    have hxy : y * x * y⁻¹ = x := by
      rw [Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxQ).2 y (Subgroup.mem_zpowers y),
        mul_inv_cancel_right]
    exact (hfixr x (Subtype.ext (by rw [hαx]; exact hxy))).symm
  have h4 := L34.card_le_four (e zT).2 hs2 ρ.2 (by rw [← Subgroup.coe_pow, hρ3, Subgroup.coe_one])
    (fun h => hρ1 (Subtype.ext h)) (hfixr zT hαz) hWS hW2 hWr
  rwa [hWc] at h4

end CFSG.ClassicalInvolution.Q3.TA3.Frame
