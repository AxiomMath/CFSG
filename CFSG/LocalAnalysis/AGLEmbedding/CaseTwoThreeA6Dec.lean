module

import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeInner
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem d1_isSubnormal_of_open_top {X : Type*} [Group X] {H : Subgroup X}
    (h : CFSG.Open.IsSubnormal H ⊤) : H.IsSubnormal :=
  CFSG.Open.IsSubnormal.top_iff.1 h

theorem exists_pElt_of_pElt_mem_sup {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {L : Subgroup X} {u : X} (hu : u ∈ L ⊔ Subgroup.centralizer (L : Set X))
    (hup : ∃ k : ℕ, u ^ p ^ k = 1) :
    ∃ l ∈ L, (∃ k : ℕ, l ^ p ^ k = 1) ∧ l⁻¹ * u ∈ Subgroup.centralizer (L : Set X) := by
  have hLC : L ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set X) : Set X) :=
    Subgroup.le_normalizer.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLC] at hu
  obtain ⟨a, ha, c, hc, rfl⟩ := hu
  have hac : Commute a c := Subgroup.mem_centralizer_iff.mp hc a ha
  obtain ⟨n, e, hn, hfix⟩ := exists_pPart_pow hp ((a, c) : X × X)
  have hu' : (a * c) ^ n = a * c := by
    refine hfix (a * c) ?_ hup
    have h1 := pow_orderOf_eq_one ((a, c) : X × X)
    rw [Prod.pow_mk, Prod.mk_eq_one] at h1
    rw [hac.mul_pow, h1.1, h1.2, one_mul]
  refine ⟨a ^ n, L.pow_mem ha n, ⟨e, ?_⟩, ?_⟩
  · have := congrArg Prod.fst hn
    simpa [← pow_mul] using this
  · have h2 : (a ^ n)⁻¹ * (a * c) = c ^ n := by
      conv_lhs => rw [← hu', hac.mul_pow]
      group
    rw [h2]
    exact Subgroup.pow_mem _ hc n

theorem card_mul_card_eq_of_sup {X : Type*} [Group X] [Finite X] {A E : Subgroup X}
    (hEN : E ≤ Subgroup.normalizer (A : Set X))
    (hEin : ∀ x ∈ E, x ∈ A ⊔ Subgroup.centralizer (A : Set X)) :
    Nat.card E * Nat.card (Subgroup.centralizer (A : Set X) ⊓
        (A ⊓ (E ⊔ Subgroup.centralizer (A : Set X))) : Subgroup X) =
      Nat.card (A ⊓ (E ⊔ Subgroup.centralizer (A : Set X)) : Subgroup X) *
        Nat.card (E ⊓ Subgroup.centralizer (A : Set X) : Subgroup X) := by
  set Cn := Subgroup.centralizer (A : Set X) with hCn
  set I := A ⊓ (E ⊔ Cn) with hI
  have hENC : E ≤ Subgroup.normalizer (Cn : Set X) := fun x hx =>
    mem_normalizer_centralizer (hEN hx)
  have hANC : A ≤ Subgroup.normalizer (Cn : Set X) := fun x hx =>
    mem_normalizer_centralizer (Subgroup.le_normalizer hx)
  have hsup : Cn ⊔ E = Cn ⊔ I := by
    refine le_antisymm (sup_le le_sup_left fun e he => ?_) (sup_le le_sup_left
      (inf_le_right.trans (sup_le le_sup_right le_sup_left)))
    have he' := hEin e he
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hANC] at he'
    obtain ⟨l, hl, k, hk, rfl⟩ := he'
    have hlI : l ∈ I := ⟨hl, by
      have : l = (l * k) * k⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ hk))⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hlI) (Subgroup.mem_sup_left hk)
  have hc1 := card_sup_mul_card_inf_eq_of_le_normalizer hENC
  have hc2 := card_sup_mul_card_inf_eq_of_le_normalizer (inf_le_left.trans hANC :
    I ≤ Subgroup.normalizer (Cn : Set X))
  rw [hsup] at hc1
  have hpos : 0 < Nat.card Cn := Nat.card_pos
  have e1 : Nat.card (Cn ⊓ E : Subgroup X) = Nat.card (E ⊓ Cn : Subgroup X) := by
    rw [inf_comm]
  rw [e1] at hc1
  have : Nat.card Cn * (Nat.card E * Nat.card (Cn ⊓ I : Subgroup X)) =
      Nat.card Cn * (Nat.card I * Nat.card (E ⊓ Cn : Subgroup X)) := by
    calc Nat.card Cn * (Nat.card E * Nat.card (Cn ⊓ I : Subgroup X))
        = (Nat.card Cn * Nat.card E) * Nat.card (Cn ⊓ I : Subgroup X) := by ring
      _ = (Nat.card (Cn ⊔ I : Subgroup X) * Nat.card (E ⊓ Cn : Subgroup X)) *
          Nat.card (Cn ⊓ I : Subgroup X) := by rw [hc1]
      _ = (Nat.card (Cn ⊔ I : Subgroup X) * Nat.card (Cn ⊓ I : Subgroup X)) *
          Nat.card (E ⊓ Cn : Subgroup X) := by ring
      _ = Nat.card Cn * (Nat.card I * Nat.card (E ⊓ Cn : Subgroup X)) := by rw [hc2]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem exists_dec_of_sylow {X : Type} [Group X] [Finite X] {A : Subgroup X}
    (hA : IsSubnormal A ⊤) (S : Sylow 3 X)
    (hSN : (S : Subgroup X) ≤ Subgroup.normalizer (A : Set X))
    (hSin : ∀ x ∈ (S : Subgroup X), x ∈ A ⊔ Subgroup.centralizer (A : Set X))
    {y : X} (hy : y ∈ (S : Subgroup X)) :
    ∃ l ∈ (S : Subgroup X) ⊓ A, l⁻¹ * y ∈ Subgroup.centralizer (A : Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨y, hy⟩
  have hy3 : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨l, hlA, hl3, hlc⟩ := exists_pElt_of_pElt_mem_sup Nat.prime_three (hSin y hy) ⟨k, hy3⟩
  refine ⟨l, ⟨?_, hlA⟩, hlc⟩
  obtain ⟨TK, hTK⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S
    (d1_isSubnormal_of_open_top hA)
  set T := (S : Subgroup X) ⊓ A with hT
  have hyT : y ∈ Subgroup.normalizer (T : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hy) x
    have h2 := Subgroup.mem_normalizer_iff.mp (hSN hy) x
    simp only [hT, Subgroup.mem_inf]
    exact and_congr h1 h2
  have hcT : (l⁻¹ * y)⁻¹ ∈ Subgroup.normalizer (T : Set X) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le inf_le_right
      (Subgroup.inv_mem _ hlc))
  have hlT : l ∈ Subgroup.normalizer (T : Set X) := by
    have : l = y * (l⁻¹ * y)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hyT hcT
  have hlp : IsPGroup 3 (Subgroup.zpowers l) := by
    obtain ⟨j, hj⟩ := hl3
    exact isPGroup_zpowers_of_pow_eq_one hj
  have hTp : IsPGroup 3 T := S.isPGroup'.to_le inf_le_left
  have hV : IsPGroup 3 (T ⊔ Subgroup.zpowers l : Subgroup X) :=
    IsPGroup.to_sup_of_normal_left' hTp hlp (Subgroup.zpowers_le.mpr hlT)
  have hVA : T ⊔ Subgroup.zpowers l ≤ A := sup_le inf_le_right (Subgroup.zpowers_le.mpr hlA)
  have hmax := TK.is_maximal' (hV.comap_subtype (K := A)) (fun t ht => by
    show (t : X) ∈ T ⊔ Subgroup.zpowers l
    exact Subgroup.mem_sup_left (hTK ▸ ⟨t, ht, rfl⟩))
  have hl' : (⟨l, hlA⟩ : A) ∈ (TK : Subgroup A) := by
    rw [← hmax]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers l)
  have : l ∈ T := hTK ▸ ⟨⟨l, hlA⟩, hl', rfl⟩
  exact this.1

end CFSG.AGLEmbedding
