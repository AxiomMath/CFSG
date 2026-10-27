
module

public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.KGroupTauCetiClosure

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open

namespace Bridge

@[expose] def B4HypWith (KP : ∀ (Y : Type) [Group Y], Prop) {V : Type} [CommGroup V] [Finite V]
    (G L : Subgroup (MulAut V)) : Prop :=
  (CFSG.Open.SQTKTauCeti.StronglyQuasithin ↥G ∧ KP ↥G) ∧ L = quasithinGenFitting G ∧
    CFSG.IsQuasisimple ↥L ∧ XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤

@[expose] def AsB42With (KP : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B4HypWith KP G L →
      ∀ A : Subgroup (MulAut V), IsFFStarOffender G A → B42Conclusion G L A

theorem asB42With_kGroup : AsB42With CFSG.SectionRank.IsKGroupCat ↔ AsB42 := Iff.rfl

theorem alt_exists_noncomm {m : ℕ} (hm : 5 ≤ m) :
    ∃ a b : alternatingGroup (Fin m), a * b ≠ b * a := by
  by_contra h
  push Not at h
  have h4 : 4 ≤ Nat.card (Fin m) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
  have h3 : 3 ≤ Nat.card (Fin m) := by omega
  have hc := alternatingGroup.center_eq_bot h4
  have : Nontrivial (alternatingGroup (Fin m)) := alternatingGroup.nontrivial_of_three_le_card h3
  obtain ⟨x, hx⟩ := exists_ne (1 : alternatingGroup (Fin m))
  have hxc : x ∈ Subgroup.center (alternatingGroup (Fin m)) :=
    Subgroup.mem_center_iff.2 fun g => h g x
  rw [hc] at hxc
  exact hx (Subgroup.mem_bot.1 hxc)

theorem alt_isSimple {m : ℕ} (hm : 5 ≤ m) : IsSimpleGroup (alternatingGroup (Fin m)) :=
  alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hm)

structure KClosed (KP : ∀ (Y : Type) [Group Y], Prop) : Prop where
  inj : ∀ {A B : Type} [Group A] [Group B] (f : A →* B), Function.Injective f → KP B → KP A
  quot : ∀ {Y : Type} [Group Y] (N : Subgroup Y) [N.Normal], KP Y → KP (Y ⧸ N)

theorem kClosed_tc : KClosed CFSG.Open.SQTKTauCeti.KGroup :=
  ⟨fun f hf hB => TauCetiK.kGroup_of_injective f hf hB, fun N _ h => TauCetiK.kGroup_quotient h N⟩

theorem kClosed_native : KClosed CFSG.SectionRank.IsKGroupCat :=
  ⟨fun {_ _} _ _ f hf hB =>
    CFSG.SectionRank.IsKGroupCat.of_mulEquiv (hB.subgroup f.range) (MonoidHom.ofInjective hf),
    fun N _ h => h.quotient N⟩

namespace KClosed

variable {KP : ∀ (Y : Type) [Group Y], Prop}

theorem of_surjective (hK : KClosed KP) {Y : Type} [Group Y] (hY : KP Y) (H : Subgroup Y)
    {Q : Type} [Group Q] (φ : ↥H →* Q) (hφ : Function.Surjective φ) : KP Q := by
  have h1 : KP ↥H := hK.inj H.subtype H.subtype_injective hY
  have h2 : KP (↥H ⧸ φ.ker) := hK.quot φ.ker h1
  exact hK.inj (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.toMonoidHom
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.injective h2

end KClosed

theorem pRank_top_le_two_of_sq_mem {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (hq : ∀ y : Y, y ^ 2 ∈ L) {m : ℕ} (hm : m ≤ 8) (e : ↥L ≃* alternatingGroup (Fin m))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp1 (⊤ : Subgroup Y)
  have hEL : E ≤ L := by
    intro x hx
    have hxp : x ^ p = 1 := hE.2 x hx
    obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hp2
    have hx' : x = (x ^ 2) ^ (k + 1) := by
      calc x = x ^ p * x := by rw [hxp, one_mul]
        _ = (x ^ 2) ^ (k + 1) := by rw [← pow_mul, ← pow_succ]; congr 1; omega
    rw [hx']
    exact L.pow_mem (hq x) (k + 1)
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ CFSG.Open.pRank p L :=
    CFSG.SectionRank.le_pRank hp1 hEL hE hcard
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup ↥L) = CFSG.Open.pRank p L :=
    CFSG.Quasithin.pRank_top_subtype (p := p) L
  have h3 : CFSG.Open.pRank p (⊤ : Subgroup ↥L) =
      CFSG.Open.pRank p (⊤ : Subgroup (alternatingGroup (Fin m))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 e
  have h4 := CFSG.SectionRank.pRank_alternating_le_two hm hp hp2
  omega

end Bridge

end CFSG.QuasithinUnique
