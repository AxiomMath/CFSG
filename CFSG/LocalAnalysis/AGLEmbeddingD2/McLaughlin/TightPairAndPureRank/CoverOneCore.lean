module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviTransfer
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28Generic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverPerfectFree

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.HallHigman CFSG.Open
open scoped commutatorElement

section Pure

theorem false_of_perfect_three_pSolvable {Y : Type*} [Group Y] [Finite Y] {V : Subgroup Y}
    (hs : IsPSolvable 3 ↥V) (hV : ⁅V, V⁆ = V) (h3 : 3 ∣ Nat.card V) (h9 : ¬ 9 ∣ Nat.card V) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf : ⁅(⊤ : Subgroup ↥V), (⊤ : Subgroup ↥V)⁆ = ⊤ := by
    apply Subgroup.map_injective V.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hV
  refine false_of_perfect_pSolvable_cyclicSylow hperf h3 hs fun P => ?_
  have hcard : Nat.card (P : Subgroup ↥V) ∣ Nat.card V := by
    exact Subgroup.card_subgroup_dvd_card (P : Subgroup ↥V)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hk1 : k ≤ 1 := by
    by_contra hk2
    apply h9
    refine (pow_dvd_pow 3 (by omega : 2 ≤ k)).trans ?_
    rw [← hk]
    exact hcard
  interval_cases k
  · rw [pow_zero] at hk
    haveI : Subsingleton (P : Subgroup ↥V) := (Nat.card_eq_one_iff_unique.mp hk).1
    exact isCyclic_of_subsingleton
  · rw [pow_one] at hk
    haveI : Fact (Nat.card (P : Subgroup ↥V)).Prime := ⟨by rw [hk]; exact Nat.prime_three⟩
    exact isCyclic_of_prime_card hk

end Pure

section Lift

variable {X Y : Type*} [Group X] [Finite X] [Group Y]

theorem exists_elemAbelian_lift (ψ : X →* Y) (hker : Nat.Coprime 3 (Nat.card ψ.ker))
    {E : Subgroup Y} (hE : E ≤ ψ.range) (hel : IsElemAbelian 3 E) :
    ∃ E' : Subgroup X, IsElemAbelian 3 E' ∧ Nat.card E' = Nat.card E := by
  classical
  have hE3 : IsPGroup 3 E := CFSG.AGLEmbedding.isPGroup_three_of_isElemAbelian_three hel
  set ρ : X →* ψ.range := ψ.rangeRestrict with hρ
  have hρs : Function.Surjective ρ := ψ.rangeRestrict_surjective
  set U₁ : Subgroup ψ.range := E.subgroupOf ψ.range with hU₁
  have hU₁3 : IsPGroup 3 U₁ := by
    intro x
    obtain ⟨k, hk⟩ := hE3 ⟨(x : Y), x.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  obtain ⟨U, hUle, hU3, hUm⟩ := CFSG.AGLEmbedding.exists_isPGroup_three_map_eq hρs hU₁3
  have hUE : ∀ u ∈ U, ψ u ∈ E := fun u hu => by
    have := hUle hu
    simpa [hU₁, Subgroup.mem_comap, Subgroup.mem_subgroupOf, hρ] using this
  have hinj : ∀ x ∈ U, ψ x = 1 → x = 1 := by
    intro x hx h1
    have hxk : x ∈ ψ.ker := h1
    obtain ⟨e, he⟩ := hU3 ⟨x, hx⟩
    have hx3 : x ^ (3 ^ e) = 1 := by simpa using congrArg Subtype.val he
    have hd1 : orderOf x ∣ Nat.card ψ.ker := by
      have := Subgroup.orderOf_dvd_natCard ψ.ker hxk
      exact this
    have hd2 : orderOf x ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one hx3
    have hcop : Nat.Coprime (orderOf x) (Nat.card ψ.ker) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd2
      rw [hj]
      exact Nat.Coprime.pow_left j hker
    have := Nat.Coprime.eq_one_of_dvd hcop hd1
    exact orderOf_eq_one_iff.1 this
  refine ⟨U, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · have hc := hel.1.is_comm.comm ⟨ψ a, hUE a a.2⟩ ⟨ψ b, hUE b b.2⟩
    have hc' : ψ ((a : X) * (b : X) * ((b : X) * (a : X))⁻¹) = 1 := by
      have := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul] at this
      rw [map_mul, map_inv, map_mul, map_mul, this, mul_inv_cancel]
    have := hinj _ (mul_mem (mul_mem a.2 b.2) (inv_mem (mul_mem b.2 a.2))) hc'
    simpa using mul_inv_eq_one.1 this
  · refine hinj _ (pow_mem hx 3) ?_
    rw [map_pow]
    exact hel.2 _ (hUE x hx)
  · refine Nat.card_congr (Equiv.ofBijective (fun u : U => (⟨ψ u, hUE u u.2⟩ : E)) ⟨?_, ?_⟩)
    · intro a b hab
      have hab' : ψ (a : X) = ψ (b : X) := congrArg Subtype.val hab
      have h1 : ψ ((a : X) * (b : X)⁻¹) = 1 := by
        rw [map_mul, map_inv, hab', mul_inv_cancel]
      have := hinj _ (mul_mem a.2 (inv_mem b.2)) h1
      exact Subtype.ext (mul_inv_eq_one.1 this)
    · rintro ⟨e, he⟩
      have : (⟨e, hE he⟩ : ψ.range) ∈ U.map ρ := by
        rw [hUm]
        exact Subgroup.mem_subgroupOf.2 he
      obtain ⟨u, hu, hue⟩ := this
      exact ⟨⟨u, hu⟩, Subtype.ext (by simpa [hρ] using congrArg Subtype.val hue)⟩

end Lift

section Image

@[expose] def SolvFree {Y : Type*} [Group Y] (C : Subgroup Y) : Prop :=
  ∀ E V : Subgroup Y, E ≤ C → V ≤ C → IsElemAbelian 3 E → Nat.card E = 9 → IsPSolvable 3 ↥V

@[expose] def E27Free {Y : Type*} [Group Y] (C : Subgroup Y) : Prop :=
  ∀ E : Subgroup Y, E ≤ C → IsElemAbelian 3 E → Nat.card E ≠ 27

variable {W : Type} [Group W] [Finite W]

theorem pRank_top_subgroupOf_le (L A : Subgroup W) :
    Open.pRank 3 (⊤ : Subgroup ↥(A.subgroupOf L)) ≤ Open.pRank 3 A := by
  have h1 := CFSG.RankThreeEvenClassification.Helpers.pRank_top_subgroup 3 Nat.prime_three
    (A.subgroupOf L)
  have h2 := CFSG.RankThreeEvenClassification.Helpers.pRank_subgroupOf 3 Nat.prime_three
    (A ⊓ L) L inf_le_right
  rw [Subgroup.inf_subgroupOf_right] at h2
  have h3 := CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt (inf_le_left : A ⊓ L ≤ A)
  rw [h1, h2]
  exact h3

theorem isPSolvable_image_subgroupOf {A : Subgroup W} (L : Subgroup W) (hA : IsPSolvable 3 ↥A) :
    IsPSolvable 3 ↥((A.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : IsPSolvable 3 ↥(A ⊓ L) :=
    Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le hA inf_le_left
  have h2 : IsPSolvable 3 ↥((A ⊓ L).subgroupOf L) :=
    Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ L ≤ L)).symm h1
  rw [← Subgroup.inf_subgroupOf_right]
  exact Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map _ h2

theorem coverOne_solv (L A : Subgroup W) (h2 : Open.pRank 3 A ≤ 2)
    (hs : Open.pRank 3 A = 2 → IsPSolvable 3 ↥A) :
    SolvFree ((A.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) := by
  classical
  intro E V hEC hVC hel hcard
  set q : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hqdef
  set X : Subgroup ↥L := A.subgroupOf L with hX
  set ψ : ↥X →* ↥L ⧸ Subgroup.center ↥L := q.comp X.subtype with hψ
  have hrange : ψ.range = X.map q := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hr2 : 2 ≤ Open.pRank 3 A := by
    by_contra hlt
    have hrX : Open.pRank 3 (⊤ : Subgroup ↥X) ≤ 1 :=
      (pRank_top_subgroupOf_le L A).trans (by omega)
    exact false_of_lift_elemAbelian ψ hrX (hrange ▸ hEC) hel hcard
  have hsolv : IsPSolvable 3 ↥A := hs (le_antisymm h2 hr2)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
    (isPSolvable_image_subgroupOf L hsolv) hVC

theorem card_ker_image_dvd (L A : Subgroup W) :
    Nat.card (((QuotientGroup.mk' (Subgroup.center ↥L)).comp
      (A.subgroupOf L).subtype).ker) ∣ Nat.card (Subgroup.center ↥L) := by
  set q : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hqdef
  set ψ := q.comp (A.subgroupOf L).subtype with hψ
  have hle : ψ.ker.map (A.subgroupOf L).subtype ≤ Subgroup.center ↥L := by
    rintro _ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff _).1 hx
  have hcard : Nat.card (ψ.ker.map (A.subgroupOf L).subtype) = Nat.card ψ.ker :=
    Subgroup.card_map_of_injective (A.subgroupOf L).subtype_injective
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hle

theorem coverOne_noE27 (L A : Subgroup W) (h2 : Open.pRank 3 A ≤ 2)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥L)) :
    E27Free ((A.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) := by
  classical
  intro E hEC hel hcard
  set q : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hqdef
  set X : Subgroup ↥L := A.subgroupOf L with hX
  set ψ : ↥X →* ↥L ⧸ Subgroup.center ↥L := q.comp X.subtype with hψ
  have hrange : ψ.range = X.map q := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.Coprime 3 (Nat.card ψ.ker) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h
    exact hZ (h.trans (card_ker_image_dvd L A))
  obtain ⟨E', hE', hE'card⟩ := exists_elemAbelian_lift ψ hker (hrange ▸ hEC) hel
  have h3 : 3 ≤ Open.pRank 3 (⊤ : Subgroup ↥X) :=
    CFSG.AGLEmbedding.KFactProofs.G28.three_le_pRank_of_card_27 le_top hE' (by rw [hE'card]; exact hcard)
  have := h3.trans (pRank_top_subgroupOf_le L A)
  omega

end Image

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
