module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A8Excl
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A4Transport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32K
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Remark31

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup Equiv

theorem two_pow_dvd_card_inf_of_sylow {G : Type} [Group G] [Finite G] {H K S : Subgroup G}
    (hS : IsSylowTwoOf S H) (hKH : K ≤ H) (hHN : H ≤ normalizer (K : Set G)) {m : ℕ}
    (hK : 2 ^ m ∣ Nat.card K) : 2 ^ m ∣ Nat.card ↥(S ⊓ K) := by
  have hSN : S ≤ normalizer (K : Set G) := hS.1.trans hHN
  have h1 := C5.card_sup_mul_card_inf_of_le_normalizer hSN
  have hSle : S ≤ S ⊔ K := le_sup_left
  have hSKH : S ⊔ K ≤ H := sup_le hS.1 hKH
  have hrel := Subgroup.relIndex_mul_relIndex S (S ⊔ K) H hSle hSKH
  have hodd : ¬ 2 ∣ S.relIndex (S ⊔ K) := by
    intro h2
    apply hS.2.2
    show 2 ∣ S.relIndex H
    rw [← hrel]
    exact Dvd.dvd.mul_right h2 _
  have hcard := Subgroup.relIndex_mul_card (H := S) (K := S ⊔ K)
  rw [inf_of_le_left hSle] at hcard
  have hpos : 0 < Nat.card ↥S := Nat.card_pos
  have h2 : S.relIndex (S ⊔ K) * Nat.card ↥(S ⊓ K) = Nat.card ↥K := by
    have h3 : Nat.card ↥S * (S.relIndex (S ⊔ K) * Nat.card ↥(S ⊓ K)) =
        Nat.card ↥S * Nat.card ↥K := by
      rw [← h1, ← hcard]
      ring
    exact Nat.eq_of_mul_eq_mul_left hpos h3
  have hcop : Nat.Coprime (2 ^ m) (S.relIndex (S ⊔ K)) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
  have hdvd : 2 ^ m ∣ S.relIndex (S ⊔ K) * Nat.card ↥(S ⊓ K) := by
    rw [h2]
    exact hK
  exact hcop.dvd_of_dvd_mul_left hdvd

theorem card_subgroupOf_inf {G : Type} [Group G] (X K : Subgroup G) :
    Nat.card ↥((X ⊓ K).subgroupOf K) = Nat.card ↥(X ⊓ K) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : X ⊓ K ≤ K)).toEquiv

theorem k32ExclA8_of_index
    (hidx : ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G),
      A3A3x T M H S L s x z₁ z₂ → (baum S).relIndex (sOne S x) ≤ 2) : K32ExclA8 := by
  intro G _ _ T M H S L s x z₁ z₂ K ctx hpre hK8
  obtain ⟨e8⟩ := hK8
  have hA : A3A3x T M H S L s x z₁ z₂ := ctx.a3
  have hcs := hA.cs
  have h3 := hA.a3
  have hA4 : IsA4Block L (blockU L) := IsA4Block.of_alt3 hcs.block.1.1 h3
  have hLK : L ≤ K := hpre.L_le_K
  have hUL : blockU L ≤ L := hA4.le
  have hUK : blockU L ≤ K := hUL.trans hLK
  obtain ⟨-, hRN, -⟩ := C56.baumann_A3_cs hcs h3
  have hz₁U : z₁ ∈ blockU L := hA.z₁_mem.1
  have hz₁K : z₁ ∈ K := hUK hz₁U
  have hKG₂ : K ≤ centralizerElem z₂ := ctx.comp.1
  have hS₁ : IsSylowTwoOf (sOne S x) (centralizerElem z₂) := ctx.sylow
  have hKcard : Nat.card ↥K = 2 ^ 6 * 315 := by
    rw [Nat.card_congr e8.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  have hP64G : 2 ^ 6 ∣ Nat.card ↥(sOne S x ⊓ K) :=
    two_pow_dvd_card_inf_of_sylow hS₁ hKG₂ hpre.K_norm (m := 6)
      (by rw [hKcard]; exact dvd_mul_right _ _)
  have hRle : baum S ≤ sOne S x := le_sup_left
  have hR32G : 32 ≤ Nat.card ↥(baum S ⊓ K) := by
    have h1 := Subgroup.relIndex_mul_card (H := baum S) (K := sOne S x ⊓ K)
    have hinf : baum S ⊓ (sOne S x ⊓ K) = baum S ⊓ K := by
      rw [← inf_assoc, inf_of_le_left hRle]
    rw [hinf] at h1
    have hle : (baum S).relIndex (sOne S x ⊓ K) ≤ 2 := by
      have : (baum S).IsFiniteRelIndex (sOne S x) :=
        Subgroup.isFiniteRelIndex_of_finiteIndex
      have hmono : (baum S).relIndex (sOne S x ⊓ K) ≤ (baum S).relIndex (sOne S x) :=
        Subgroup.relIndex_le_of_le_right inf_le_left Subgroup.relIndex_ne_zero
      exact hmono.trans (hidx G T M H S L s x z₁ z₂ hA)
    have h64 : 64 ≤ Nat.card ↥(sOne S x ⊓ K) :=
      Nat.le_of_dvd Nat.card_pos (by simpa using hP64G)
    rw [← h1] at h64
    have hpos : 0 < Nat.card ↥(baum S ⊓ K) := Nat.card_pos
    nlinarith
  let ι : ↥K →* Perm (Fin 8) := (alternatingGroup (Fin 8)).subtype.comp e8.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e8.injective
  have hev : ∀ g, Perm.sign (ι g) = 1 := fun g =>
    Perm.mem_alternatingGroup.mp (e8 g).2
  have hLγ : IsA4Block (L.subgroupOf K) ((blockU L).subgroupOf K) :=
    IsA4Block.of_map_injective K.subtype K.subtype_injective (by
      rw [Subgroup.map_subgroupOf_eq_of_le hLK, Subgroup.map_subgroupOf_eq_of_le hUK]
      exact hA4)
  have hPγ2 : IsPGroup 2 ↥((sOne S x ⊓ K).subgroupOf K) := by
    refine ctx.sylow.2.1.of_injective
      ((Subgroup.inclusion (inf_le_left : sOne S x ⊓ K ≤ sOne S x)).comp
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : sOne S x ⊓ K ≤ K)).toMonoidHom) ?_
    exact (Subgroup.inclusion_injective (inf_le_left : sOne S x ⊓ K ≤ sOne S x)).comp
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : sOne S x ⊓ K ≤ K)).injective
  have hPγ64 : 64 ≤ Nat.card ↥((sOne S x ⊓ K).subgroupOf K) := by
    rw [card_subgroupOf_inf]
    exact Nat.le_of_dvd Nat.card_pos (by simpa using hP64G)
  have hPz : ∀ g ∈ (sOne S x ⊓ K).subgroupOf K, g * (⟨z₁, hz₁K⟩ : ↥K) = ⟨z₁, hz₁K⟩ * g := by
    intro g hg
    apply Subtype.ext
    have hgS : (g : G) ∈ sOne S x := (Subgroup.mem_subgroupOf.mp hg).1
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hA.sOne_le_cent₁ hgS))
  have hRγP : (baum S ⊓ K).subgroupOf K ≤ (sOne S x ⊓ K).subgroupOf K := by
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    exact ⟨hRle hg.1, hg.2⟩
  have hRγ2 : IsPGroup 2 ↥((baum S ⊓ K).subgroupOf K) := hPγ2.to_le hRγP
  have hRγ32 : 32 ≤ Nat.card ↥((baum S ⊓ K).subgroupOf K) := by
    rw [card_subgroupOf_inf]
    exact hR32G
  have hRγN : (baum S ⊓ K).subgroupOf K ≤
      normalizer ((L.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    intro r hr
    rw [Subgroup.mem_subgroupOf] at hr
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hr' := Subgroup.mem_normalizer_iff.mp (hRN hr.1) (h : G)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using hr'
  exact A8Excl.false_of_big_two_group hLγ hι hev
    (z := (⟨z₁, hz₁K⟩ : ↥K)) (Subgroup.mem_subgroupOf.mpr hz₁U)
    (fun h => hA.z₁_ne (congrArg Subtype.val h)) hPγ2 hPγ64 hPz hRγ2 hRγ32 hRγN

end CFSG.QuasithinUnique.DoubleA3
