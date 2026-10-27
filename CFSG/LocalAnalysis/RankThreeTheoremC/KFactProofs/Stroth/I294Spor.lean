module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Out
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
import CFSG.RankThree.PartOne.KS.OuterGeneral

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup

private theorem i294Spor_card_centralizer_mulEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (a : A) :
    Nat.card (Subgroup.centralizer ({e a} : Set B)) =
      Nat.card (Subgroup.centralizer ({a} : Set A)) := by
  have hmap : (Subgroup.centralizer ({a} : Set A)).map e.toMonoidHom =
      Subgroup.centralizer ({e a} : Set B) := by
    ext b
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hc
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff] at hk
      rw [hk]
      have hac : a * c = c * a := hc a (Set.mem_singleton a)
      simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hac]
    · intro hb
      rw [Subgroup.mem_centralizer_iff] at hb
      refine ⟨e.symm b, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff] at hk
      rw [hk]
      apply e.injective
      have hab : e a * b = b * e a := hb (e a) (Set.mem_singleton _)
      simpa [map_mul] using hab
  rw [← hmap, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]

private theorem i294Spor_p4_dvd_card {Y : Type} [Group Y] [Finite Y] {p : ℕ} [hp : Fact p.Prime]
    {D : Subgroup Y} (hD : CFSG.Open.IsElemAbelian p D) (hcard : Nat.card D = p ^ 2)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup Y) = 3) {x : Y} (hxD : x ∈ D)
    (hxsyl : CFSG.ABGLocalTools.IsSylowOf p D (Subgroup.centralizer ({x} : Set Y))) :
    p ^ 4 ∣ Nat.card Y := by
  obtain ⟨P, hDP⟩ := (IsPGroup.of_card hcard).exists_le_sylow
  have hPp : IsPGroup p (P : Subgroup Y) := P.isPGroup'
  have hPrank : CFSG.Open.pRank p (P : Subgroup Y) = 3 :=
    (CFSG.SectionRank.pRank_sylow P).1.trans hrank
  obtain ⟨E, hEP, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt (P : Subgroup Y)
  rw [hPrank] at hEcard
  have h3 : p ^ 3 ∣ Nat.card (P : Subgroup Y) := by
    have := Subgroup.card_dvd_of_le hEP
    rwa [hEcard] at this
  have hne : Nat.card (P : Subgroup Y) ≠ p ^ 3 := by
    intro hPcard
    have hEP' : E = (P : Subgroup Y) :=
      Subgroup.eq_of_le_of_card_ge hEP (le_of_eq (by rw [hEcard, hPcard]))
    have hcomm : ∀ a ∈ (P : Subgroup Y), ∀ b ∈ (P : Subgroup Y), a * b = b * a := by
      intro a ha b hb
      have haE : a ∈ E := by rw [hEP']; exact ha
      have hbE : b ∈ E := by rw [hEP']; exact hb
      have hab := hE.1.is_comm.comm (⟨a, haE⟩ : E) ⟨b, hbE⟩
      have hab' := congrArg Subtype.val hab
      simpa using hab'
    have hPC : (P : Subgroup Y) ≤ Subgroup.centralizer ({x} : Set Y) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff] at hk
      rw [hk]
      exact hcomm x (hDP hxD) a ha
    have hDP' : (P : Subgroup Y) = D := hxsyl.eq_of_le hDP hPC hPp
    have hDcard : Nat.card D = p ^ 3 := by
      rw [← hDP']
      exact hPcard
    rw [hcard] at hDcard
    have hlt : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
    exact (ne_of_lt hlt) hDcard
  have h4 : p ^ 4 ∣ Nat.card (P : Subgroup Y) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hPp
    rw [hn] at h3 hne ⊢
    have hn3 : 3 ≤ n := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 h3
    have hn4 : n ≠ 3 := fun h => hne (by rw [h])
    exact Nat.pow_dvd_pow p (by omega)
  exact h4.trans (Subgroup.card_subgroup_dvd_card _)

private theorem i294Spor_p4_dvd_card_socle {Y : Type} [Group Y] {L : Subgroup Y} [L.Normal]
    (hC : Subgroup.centralizer (L : Set Y) = ⊥) {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hY : p ^ 4 ∣ Nat.card Y) {G : Type*} [Group G] (e : ↥L ≃* G)
    (hG : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer G)) :
    p ^ 4 ∣ Nat.card L := by
  have hinj : Function.Injective (MulAut.conjNormal : Y →* MulAut L) :=
    i294_conjNormal_injective hC
  have h1 : Nat.card Y ∣ Nat.card (MulAut L) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have h2 : Nat.card (MulAut L) = Nat.card (MulAut G) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  have h3 : Nat.card G = Nat.card L := (Nat.card_congr e.toEquiv).symm
  rw [h2] at h1
  have h4 : Nat.card (MulAut G) =
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer G) *
        Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner G) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h5 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner G) ∣ Nat.card G := by
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner]
    exact Subgroup.card_range_dvd _
  have hcop : Nat.Coprime (p ^ 4)
      (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer G)) :=
    Nat.Coprime.pow_left 4 ((Nat.Prime.coprime_iff_not_dvd hp).2 hG)
  have h6 : p ^ 4 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer G) *
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner G) := by
    rw [← h4]
    exact hY.trans h1
  rw [← h3]
  exact (hcop.dvd_of_dvd_mul_left h6).trans h5

private theorem i294Spor_pRank_socle {p : ℕ} {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    [L.Normal] {z g : Y} {D : Subgroup Y} (h : I294Cfg p L z g D) {G : Type*} [Group G]
    [Finite G] (e : ↥L ≃* G)
    (hG : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer G)) :
    CFSG.Open.pRank p (⊤ : Subgroup G) = 3 := by
  have hp1 : 1 < p := h.prime.one_lt
  have hout : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L) := by
    rwa [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 e,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
  apply le_antisymm
  · rw [← h.rank]
    exact CFSG.SectionRank.pRank_mono hp1 le_top
  · obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp1 (⊤ : Subgroup Y)
    rw [h.rank] at hcard
    have hEL : E ≤ L := fun x hx =>
      CFSG.RankThree.PartOne.mem_of_pow_eq_one_of_not_dvd_card_outer h.prime h.cent hout
        (hE.2 x hx)
    exact CFSG.SectionRank.le_pRank hp1 hEL hE hcard

theorem i294_false_of_sporadic (hOut : SporadicOuterOddFree) (hC : SporadicCentralizerPPart)
    {p : ℕ} {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal] {z g : Y}
    {D : Subgroup Y} (h : I294Cfg p L z g D) (hDL : D ≤ L) (s : TauCeti.SporadicName)
    (e : ↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group) : False := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨x, hxD, hx1, hxsyl⟩ := h.sylowLine
  have hxord : orderOf x = p := orderOf_eq_prime (h.elem.2 x hxD) hx1
  have hY : p ^ 4 ∣ Nat.card Y :=
    i294Spor_p4_dvd_card h.elem h.card h.rank hxD hxsyl
  have hL : p ^ 4 ∣ Nat.card L :=
    i294Spor_p4_dvd_card_socle h.cent h.prime h.odd hY e (hOut s p h.prime h.odd)
  have hG : p ^ 4 ∣ Nat.card (TauCeti.CFSGIndex.sporadic s).Group := by
    rw [← Nat.card_congr e.toEquiv]
    exact hL
  obtain ⟨xL, hxLval⟩ : ∃ xL : L, (xL : Y) = x := ⟨⟨x, hDL hxD⟩, rfl⟩
  have hxLord : orderOf (e xL) = p := by
    have h1 : orderOf (e xL) = orderOf xL := orderOf_injective e.toMonoidHom e.injective xL
    have h2 : orderOf xL = orderOf x := by
      rw [← hxLval]
      exact (Subgroup.orderOf_coe xL).symm
    rw [h1, h2, hxord]
  haveI : Finite (TauCeti.CFSGIndex.sporadic s).Group := Finite.of_equiv _ e.toEquiv
  have hC3 := hC s p h.prime h.odd (i294Spor_pRank_socle h e (hOut s p h.prime h.odd)) hG
    (e xL) hxLord
  rw [i294Spor_card_centralizer_mulEquiv e xL] at hC3
  have hsub : (Subgroup.centralizer ({xL} : Set L)).map L.subtype ≤
      Subgroup.centralizer ({x} : Set Y) := by
    rintro _ ⟨l, hl, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hl
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    rw [hk]
    have hcomm : xL * l = l * xL := hl xL (Set.mem_singleton _)
    have hcomm' := congrArg Subtype.val hcomm
    simpa [hxLval] using hcomm'
  have hmapcard : Nat.card ((Subgroup.centralizer ({xL} : Set L)).map L.subtype) =
      Nat.card (Subgroup.centralizer ({xL} : Set L)) :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hCY : p ^ 3 ∣ Nat.card (Subgroup.centralizer ({x} : Set Y)) := by
    rw [← hmapcard] at hC3
    exact hC3.trans (Subgroup.card_dvd_of_le hsub)
  have hv : Nat.card D = p ^ (Nat.card (Subgroup.centralizer ({x} : Set Y))).factorization p :=
    hxsyl.card_eq
  rw [h.card] at hv
  have hne : Nat.card (Subgroup.centralizer ({x} : Set Y)) ≠ 0 := Nat.card_pos.ne'
  have h3 : 3 ≤ (Nat.card (Subgroup.centralizer ({x} : Set Y))).factorization p :=
    (h.prime.pow_dvd_iff_le_factorization hne).1 hCY
  have h4 : p ^ 3 ≤ p ^ (Nat.card (Subgroup.centralizer ({x} : Set Y))).factorization p :=
    Nat.pow_le_pow_right h.prime.pos h3
  rw [← hv] at h4
  have h5 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right h.prime.one_lt (by norm_num)
  exact absurd h4 (not_le.2 h5)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
