module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRAssemble

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem primePower_card_seven {q : TauCeti.PrimePower} (hq : q.card = 7) :
    q.p = 7 ∧ q.exponent = 1 := by
  have hdvd : q.p ∣ 7 := by
    rw [← hq, TauCeti.PrimePower.card_def]
    exact dvd_pow_self q.p (Nat.ne_of_gt q.exponent_pos)
  have h7 : q.p = 7 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdvd with h | h
    · exact absurd h q.prime_p.ne_one
    · exact h
  have hpow : q.p ^ q.exponent = 7 := by
    rw [← TauCeti.PrimePower.card_def]
    exact hq
  rw [h7] at hpow
  exact ⟨h7, ((by norm_num : Nat.Prime 7).pow_eq_iff.mp hpow).2⟩

theorem l32Atlas_proved : CFSG.AGLEmbeddingD2.McLaughlin.L32Atlas := by
  unfold CFSG.AGLEmbeddingD2.McLaughlin.L32Atlas
  intro X _ hX
  unfold IsLThreeTwo at hX
  obtain ⟨d, ⟨q, hq7, hd⟩, ⟨e⟩⟩ := hX
  obtain ⟨hp, hn⟩ := primePower_card_seven hq7
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hL : IsLinTwoIndex 7 1 d := ⟨q, hd, hp, hn⟩
  have hcard : Nat.card (TauCeti.CFSGIndex.lie d).Group = 7 ^ 1 * (((7 ^ 1) ^ 2 - 1) / 2) :=
    card_catGroup_linTwo (p := 7) (n := 1) (by norm_num) (by norm_num) hL
  rw [Nat.card_congr e.toEquiv, hcard]
  norm_num

theorem centre_eq_bot_of_normal_of_pCore_eq_bot {G : Type*} [Group G] {p : ℕ}
    (hO : ∀ N : Subgroup G, N.Normal → IsPGroup p N → N = ⊥)
    {L : Subgroup G} (hL : L.Normal) (hZ : IsPGroup p ↥(Subgroup.center ↥L)) :
    Subgroup.center ↥L = ⊥ := by
  set Zs : Subgroup G := (Subgroup.center ↥L).map L.subtype with hZs
  have hZn : Zs.Normal := by
    constructor
    rintro n ⟨z, hz, rfl⟩ g
    refine ⟨⟨g * (z : G) * g⁻¹, hL.conj_mem _ z.2 g⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hy' : g⁻¹ * (y : G) * g ∈ L := by
      have := hL.conj_mem _ y.2 g⁻¹
      rwa [inv_inv] at this
    have h3 : (g⁻¹ * (y : G) * g) * (z : G) = (z : G) * (g⁻¹ * (y : G) * g) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g⁻¹ * (y : G) * g, hy'⟩)
    show (y : G) * (g * (z : G) * g⁻¹) = g * (z : G) * g⁻¹ * (y : G)
    calc (y : G) * (g * (z : G) * g⁻¹) = g * ((g⁻¹ * (y : G) * g) * (z : G)) * g⁻¹ := by group
      _ = g * ((z : G) * (g⁻¹ * (y : G) * g)) * g⁻¹ := by rw [h3]
      _ = g * (z : G) * g⁻¹ * (y : G) := by group
  have hZp : IsPGroup p ↥Zs :=
    hZ.of_equiv (Subgroup.equivMapOfInjective _ _ Subtype.val_injective)
  have hbot : Zs = ⊥ := hO Zs hZn hZp
  rw [eq_bot_iff]
  intro x hx
  have hxZ : L.subtype x ∈ Zs := Subgroup.mem_map_of_mem _ hx
  rw [hbot, Subgroup.mem_bot] at hxZ
  rw [Subgroup.mem_bot]
  exact Subtype.ext (by simpa using hxZ)

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
