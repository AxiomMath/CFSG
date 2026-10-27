module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.RankPSL
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.Index
public import CFSG.HardMathSupport.Foote.E27.Split
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 TauCeti
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL StatedSU)

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem false_of_elemAbelian_card_lt (h : E27Config X K R T z) (hz : z ∈ K) {G : Type} [Group G]
    (e : ↥K ≃* G) (hbound : ∀ E : Subgroup G, CFSG.Open.IsElemAbelian 3 E → Nat.card E < 27) :
    False := by
  have hRK : R ≤ K := h.le_of_mem hz
  set R₁ : Subgroup ↥K := R.subgroupOf K with hR₁
  have hR₁card : Nat.card ↥R₁ = 27 := by
    rw [← h.card_R]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv
  have hR₁e : CFSG.Open.IsElemAbelian 3 R₁ := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
    · have := h.elem.1.is_comm.comm (⟨a.1.1, a.2⟩ : R) ⟨b.1.1, b.2⟩
      simpa using congrArg Subtype.val this
    · exact Subtype.ext (by simpa using h.elem.2 x.1 (Subgroup.mem_subgroupOf.mp hx))
  have hE := CFSG.SectionRank.isElemAbelian_map hR₁e e.toMonoidHom
  have hc := hbound _ hE
  rw [Subgroup.card_map_of_injective e.injective, hR₁card] at hc
  exact lt_irrefl _ hc

theorem false_of_rank_le_two (h : E27Config X K R T z) (hz : z ∈ K) {G : Type} [Group G]
    (e : ↥K ≃* G) (hbound : ∀ E : Subgroup G, CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2) :
    False :=
  false_of_elemAbelian_card_lt h hz e fun E hE => lt_of_le_of_lt (hbound E hE) (by norm_num)

theorem three_ne_zero_of_card {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) (hp3 : p ≠ 3) : ((3 : ℕ) : F) ≠ 0 := by
  have hchar : CharP F p := by
    have := Fintype.ofFinite F
    have : Fact p.Prime := ⟨hp⟩
    exact charP_of_card_eq_prime_pow (f := f) (by rw [Fintype.card_eq_nat_card, hF])
  rw [Ne, CharP.cast_eq_zero_iff F p]
  intro hd
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd)

theorem false_of_typeA_two (h : E27Config X K R T z) (hz : z ∈ K) {q : PrimePower}
    (hv : (LieTypeIndex.A 2 q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.A 2 q, hv⟩)) (hp3 : q.p ≠ 3) : False := by
  obtain ⟨e⟩ := e
  obtain ⟨⟨hp, hf, -⟩, F, hF, hFin, hFcard, ⟨θ⟩⟩ :=
    statedClassicalModel_typeA' hv e
  exact false_of_rank_le_two h hz θ fun E hE =>
    card_le_of_statedProj_SL (n := 3) (three_ne_zero_of_card hp hf hFcard hp3) (by norm_num) E hE

theorem false_of_typeTwistedA_two (h : E27Config X K R T z) (hz : z ∈ K) {q : PrimePower}
    (hv : (LieTypeIndex.twistedA 2 q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩)) (hp3 : q.p ≠ 3) :
    False := by
  obtain ⟨e⟩ := e
  obtain ⟨⟨hp, -, -⟩, F, hF, hFin, hFcard, ⟨θ⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  have hpK : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hFcard]
    have h3 : ¬ 3 ∣ q.p ^ q.exponent := fun hd =>
      hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
        (Nat.prime_three.dvd_of_dvd_pow hd)).symm
    have hm : (q.p ^ q.exponent) % 3 = 1 ∨ (q.p ^ q.exponent) % 3 = 2 := by omega
    have hsq : ((q.p ^ q.exponent) ^ 2) % 3 = 1 := by
      rcases hm with hm | hm <;> simp [Nat.pow_mod, hm]
    omega
  exact false_of_rank_le_two h hz θ fun E hE =>
    card_le_of_statedProj Nat.prime_three (by norm_num) (by norm_num) hpK E hE

end CFSG.HardMathSupport.Malle.E27Lie
