module

public import CFSG.CGT.PushingUpLit.T2K.FourFourC
public import CFSG.CGT.PushingUpLit.T2KHall.Z4

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Assembly
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)
open scoped commutatorElement

theorem le_of_isPGroup_of_normal_sylow {G : Type} [Group G] [Finite G] {R X P : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R X) (hRn : (R.subgroupOf X).Normal) (hPX : P ≤ X)
    (hP : IsPGroup 2 P) : P ≤ R := by
  have hRX : R ≤ X := hR.le
  have hn : X ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRX).1 hRn
  have h1 : IsPGroup 2 (R ⊔ P : Subgroup G) :=
    hR.isPGroup.to_sup_of_normal_left' hP (hPX.trans hn)
  have h2 := hR.eq_of_le le_sup_left (sup_le hRX hPX) h1
  exact le_sup_right.trans h2.le

namespace T2Hyp

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}
variable (h : T2Hyp G L M n)
include h

theorem four_four (hE1 : FooteNonsolvableSimple) (hE8 : SolomonTimmesfeldTight)
    (h25 : Asc76Lemma25) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    Subgroup.centralizer (L : Set G) ≤ M ∧
      CFSG.Open.IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G)) ∧
      M ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  classical
  have hMN := h.normal hE1
  have hCM := h.centralizer_le hE1
  have hnormX := h.le_normalizer_centralizer hE1
  refine ⟨hCM, ?_⟩
  by_cases hev : Even (Nat.card ↥(Subgroup.centralizer (L : Set G)))
  · rcases hE8 G L M n h hMN (h.isTightlyEmbedded hE1 hev) (h.normalizer_centralizer_eq hE1 hev)
      with ⟨s, hs, hX⟩ | ⟨R, hRsyl, hRn, hRe⟩
    · exact (h.z4_not_weaklyClosed_of_lemma25 hE1 hs hX h25 hT
        (fun g hg => h.z4_conj_eq hE1 hs hX hT hg)).elim
    ·
      have hSsyl : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ Subgroup.centralizer (L : Set G))
          (Subgroup.centralizer (L : Set G)) := hT.inf_of_le_normalizer hCM hnormX
      have hSR : T ⊓ Subgroup.centralizer (L : Set G) ≤ R :=
        le_of_isPGroup_of_normal_sylow hRsyl hRn inf_le_right hSsyl.isPGroup
      have hSeq : R = T ⊓ Subgroup.centralizer (L : Set G) :=
        hSsyl.eq_of_le hSR hRsyl.le hRsyl.isPGroup
      rw [← hSeq]
      refine ⟨hRe, fun m hm => ?_⟩
      rw [Subgroup.mem_normalizer_iff]
      have hconj : ∀ m ∈ M, ∀ x ∈ R, m * x * m⁻¹ ∈ R := by
        intro m hm x hx
        have hmapX : R.map (MulAut.conj m).toMonoidHom ≤ Subgroup.centralizer (L : Set G) := by
          rintro _ ⟨r, hr, rfl⟩
          have hrX := hRsyl.le hr
          exact (Subgroup.mem_normalizer_iff.1 (hnormX hm) r).1 hrX
        have hmapP : IsPGroup 2 (R.map (MulAut.conj m).toMonoidHom) := hRsyl.isPGroup.map _
        exact le_of_isPGroup_of_normal_sylow hRsyl hRn hmapX hmapP ⟨x, hx, rfl⟩
      intro y
      exact ⟨fun hy => hconj m hm y hy, fun hy => by
        have := hconj m⁻¹ (M.inv_mem hm) _ hy
        simpa [mul_assoc] using this⟩
  ·
    have hodd : Odd (Nat.card ↥(Subgroup.centralizer (L : Set G))) := Nat.not_even_iff_odd.1 hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hS2 : IsPGroup 2 (T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :=
      hT.isPGroup.to_le inf_le_left
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hS2
    have hdvd : Nat.card ↥(T ⊓ Subgroup.centralizer (L : Set G)) ∣
        Nat.card ↥(Subgroup.centralizer (L : Set G)) := Subgroup.card_dvd_of_le inf_le_right
    have hk0 : k = 0 := by
      by_contra hne
      have : Even (Nat.card ↥(T ⊓ Subgroup.centralizer (L : Set G))) := by
        rw [hk]
        exact Nat.even_pow.2 ⟨even_two, hne⟩
      obtain ⟨c, hc⟩ := hdvd
      have : Even (Nat.card ↥(Subgroup.centralizer (L : Set G))) := by
        rw [hc]
        exact this.mul_right c
      exact hev this
    rw [hk0, pow_zero] at hk
    have hbot : T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := Subgroup.eq_bot_of_card_eq _ hk
    rw [hbot]
    refine ⟨?_, fun m _ => ?_⟩
    · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · have ha : (a : G) = 1 := Subgroup.mem_bot.1 a.2
        have hb : (b : G) = 1 := Subgroup.mem_bot.1 b.2
        exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ha, hb])
      · rw [Subgroup.mem_bot.1 hx]
        exact one_pow 2
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      simp only [Subgroup.mem_bot]
      constructor
      · intro hy
        rw [hy]
        simp
      · intro hy
        have : y = m⁻¹ * (m * y * m⁻¹) * m := by group
        rw [this, hy]
        group

end T2Hyp

end CFSG.CGT.PushingUpLit.T2K
