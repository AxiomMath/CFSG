module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.AutHom
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.EmbOfHom
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.GLevel
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Model28Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.XNorm

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Equiv Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Schreier

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

section Certified


theorem exists_isEmb (h : StdHyp G L) (hL : IsSporadic L .M12) {t x : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hout : ¬ centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G))
    (hxL : x ∈ L) (hx2 : orderOf x = 2) (hx : Nat.card ↥(L ⊓ centralizer ({x} : Set G)) = 240)
    {x₀ : Perm (Fin 28)} (hK : ∀ b, Nat.card ↥(K28 b) = 380160)
    (hI3 : ∀ y ∈ D28, orderOf y = 2 →
      Nat.card ↥(D28 ⊓ centralizer ({y} : Set (Perm (Fin 28)))) = 240 →
      ∃ a ∈ D28, a * y * a⁻¹ = x₀) :
    ∃ (b : Bool) (ι : ↥(centralizer ({t} : Set G)) →* Perm (Fin 28)),
      IsEmb L t x (K28 b) D28 pT x₀ ι := by
  let C := centralizer ({t} : Set G)
  haveI : (L.subgroupOf C).Normal := normal_subgroupOf_centralizer h ht ht2
  obtain ⟨θ⟩ := exists_equiv_D24 hL ht
  have htC2 : orderOf (tC t) = 2 := by
    rw [tC, Subgroup.orderOf_mk, ht2]
  have hcardN : Nat.card ↥(L.subgroupOf C) = Nat.card ↥L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_centralizer_singleton (t := t) ht)).toEquiv
  have hcardC : Nat.card ↥C = 380160 := by
    rw [card_centralizer_singleton h hL ht ht2 hout, card_of_isSporadic_m12 hL]
  obtain ⟨π, g, hπker, hπn, hπg⟩ := exists_pi (L.subgroupOf C) θ
    (centralizes_iff_mem_zpowers h hL ht ht2)
    (by rw [hcardN, card_centralizer_singleton h hL ht ht2 hout]) htC2
  have hπN : (L.subgroupOf C).map π = D24 := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨n, hn, rfl⟩
      exact (hπn ⟨n, hn⟩).symm ▸ (θ ⟨n, hn⟩).2
    · intro d hd
      obtain ⟨n, hn⟩ := θ.surjective ⟨d, hd⟩
      exact ⟨n, n.2, by rw [hπn n, hn]⟩
  have htcomm : ∀ c : ↥C, c * tC t = tC t * c := fun c =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c.2)
  have htN : tC t ∉ L.subgroupOf C := fun hmem =>
    not_mem_of_isSporadic_m12 hL ht ht2 (Subgroup.mem_subgroupOf.1 hmem)
  obtain ⟨b, ι, hinj, hιN, hιt, hKι⟩ := exists_emb_of_hom (L.subgroupOf C) htcomm htC2 htN π
    hπker hπN hπg hcardC
  have hrange : ι.range = K28 b := by
    symm
    refine Subgroup.eq_of_le_of_card_ge hKι ?_
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, hcardC, hK b]
  have hpush : push ι L = D28 := by rw [push_def]; exact hιN
  have hιt' : ∀ c : ↥C, (c : G) = t → ι c = pT := fun c hc => by
    have hct : c = tC t := Subtype.ext hc
    rw [hct]
    exact hιt
  obtain ⟨ι', hι'⟩ := exists_isEmb_of_injective ι hinj hrange hpush hιt' ht hxL hx2 hx
    (pT_commute_of_mem_K28 b) (D28_le_K28 b) hI3
  exact ⟨b, ι', hι'⟩

end Certified

end CFSG.EvenSporadicStandard.M12Std.PropA
