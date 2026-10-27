module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3Shadow
public import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem u3l45_eq_top {X : Type} [Group X] [Finite X] (hK2 : KFactU3TwoSignalizer)
    (O : Subgroup X) [O.Normal] (hO : Nat.Coprime 3 (Nat.card O)) (hX : IsRankThreeU3 (X ⧸ O))
    (T : Sylow 3 X) {A : Subgroup X} (hOA : O ≤ A) {u : X} (huT : u ∈ (T : Subgroup X))
    (huZ : ∀ t ∈ (T : Subgroup X), u * t = t * u) (huo : orderOf u = 3)
    (hN : ∀ R : Subgroup X, R ≤ (T : Subgroup X) → R ≠ ⊥ → normalizer (R : Set X) ≤ A)
    (hV : ∀ V : Subgroup (X ⧸ O), IsPGroup 2 V →
      QuotientGroup.mk' O u ∈ normalizer (V : Set (X ⧸ O)) →
        V ≤ A.map (QuotientGroup.mk' O)) : A = ⊤ := by
  have hprime : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hprime⟩
  let Qhat : Sylow 3 (X ⧸ O) := T.mapSurjective (QuotientGroup.mk'_surjective O)
  have hQhat : (Qhat : Subgroup (X ⧸ O)) = (T : Subgroup X).map (QuotientGroup.mk' O) :=
    Sylow.coe_mapSurjective _ _
  have huQ : QuotientGroup.mk' O u ∈ (Qhat : Subgroup (X ⧸ O)) := by
    rw [hQhat]
    exact mem_map_of_mem _ huT
  have hucen : QuotientGroup.mk' O u ∈
      ((center ↥(Qhat : Subgroup (X ⧸ O))).map (Qhat : Subgroup (X ⧸ O)).subtype) := by
    refine ⟨⟨QuotientGroup.mk' O u, huQ⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    rintro ⟨q, hq⟩
    rw [hQhat] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    exact Subtype.ext (by
      change QuotientGroup.mk' O t * QuotientGroup.mk' O u =
        QuotientGroup.mk' O u * QuotientGroup.mk' O t
      rw [← map_mul, ← map_mul, huZ t ht])
  have hmain := hK2 (X ⧸ O) hX Qhat _ hucen
    (CFSG.AGLEmbedding.orderOf_mk_of_coprime hprime O hO huo)
  have hΓ : rankThreeGamma 1 3 (Qhat : Subgroup (X ⧸ O)) ≤ A.map (QuotientGroup.mk' O) := by
    refine sSup_le ?_
    rintro _ ⟨Rb, hRbQ, hRb1, rfl⟩ nb hnb
    obtain ⟨t, htR, hto⟩ := GenericShadow3.exists_orderOf_eq_of_one_le_pRank hprime hRb1
    have hRbT : Rb ≤ (T : Subgroup X).map (QuotientGroup.mk' O) := hQhat ▸ hRbQ
    have hRmap := CFSG.AGLEmbedding.map_comap_inf_eq (QuotientGroup.mk' O) hRbT
    set R : Subgroup X := Rb.comap (QuotientGroup.mk' O) ⊓ (T : Subgroup X) with hR
    have hRp : IsPGroup 3 R := T.isPGroup'.to_le inf_le_right
    have hRne : R ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.map_bot] at hRmap
      have : t ∈ (⊥ : Subgroup (X ⧸ O)) := hRmap ▸ htR
      rw [Subgroup.mem_bot] at this
      rw [this, orderOf_one] at hto
      omega
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective O nb
    have hn : n ∈ (normalizer ((R.map (QuotientGroup.mk' O) : Subgroup (X ⧸ O)) :
        Set (X ⧸ O))).comap (QuotientGroup.mk' O) := by
      rw [Subgroup.mem_comap, hRmap]
      exact hnb
    have hn' := CFSG.AGLEmbedding.comap_normalizer_map_le_sup hprime O hO hRp hn
    exact ⟨n, sup_le hOA (hN R inf_le_right hRne) hn', rfl⟩
  have hsup : sSup {T' : Subgroup (X ⧸ O) | IsPGroup 2 T' ∧
      QuotientGroup.mk' O u ∈ normalizer (T' : Set (X ⧸ O))} ≤ A.map (QuotientGroup.mk' O) :=
    sSup_le fun V hV' => hV V hV'.1 hV'.2
  have htop : (⊤ : Subgroup (X ⧸ O)) ≤ A.map (QuotientGroup.mk' O) :=
    hmain.trans (sup_le hΓ hsup)
  refine eq_top_iff.mpr fun a _ => ?_
  obtain ⟨a', ha', hmk⟩ := htop (mem_top (QuotientGroup.mk' O a))
  have hmem : a'⁻¹ * a ∈ O := by
    rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker, map_mul, map_inv, hmk, inv_mul_cancel]
  have : a' * (a'⁻¹ * a) ∈ A := A.mul_mem ha' (hOA hmem)
  rwa [mul_inv_cancel_left] at this

end CFSG.LocalAnalysis.RankThreeTheoremC
