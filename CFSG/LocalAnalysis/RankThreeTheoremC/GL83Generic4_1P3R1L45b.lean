module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3Shadow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

section Transfer

open scoped IsMulCommutative

theorem m11l45_false_of_central {K : Type} [Group K] [Finite K] [Group.IsPerfect K]
    (Q : Sylow 3 K) (hQ : IsMulCommutative (Q : Subgroup K)) {z : K}
    (hz : z ∈ Subgroup.center K) (hzo : orderOf z = 3) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (Q : Subgroup K).FiniteIndex := Subgroup.finiteIndex_of_finite
  let V : K →* ↥(Q : Subgroup K) := MonoidHom.transfer (MonoidHom.id (Q : Subgroup K))
  have hkey : ∀ (k : ℕ) (g₀ : K), g₀⁻¹ * z ^ k * g₀ ∈ (Q : Subgroup K) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk : z ^ k ∈ Subgroup.center K := Subgroup.pow_mem _ hz k
    rw [mem_center_iff] at hzk
    rw [hzk g₀⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  have hV : V z = (MonoidHom.id _) ⟨z ^ (Q : Subgroup K).index,
      MonoidHom.transfer_eq_pow_aux z hkey⟩ := MonoidHom.transfer_eq_pow _ z hkey
  have hV1 : V z = 1 := by
    have : IsMulCommutative ↥(Q : Subgroup K) := hQ
    have := Group.IsPerfect.range V
    have hsub : Subsingleton ↥V.range :=
      Group.IsPerfect.subsingleton_of_isMulCommutative (G := ↥V.range)
    have := Subsingleton.elim (⟨V z, ⟨z, rfl⟩⟩ : ↥V.range) ⟨1, V.range.one_mem⟩
    exact congrArg Subtype.val this
  rw [hV1] at hV
  have hpow : z ^ (Q : Subgroup K).index = 1 := by
    have := congrArg Subtype.val hV.symm
    simpa using this
  have hdvd : 3 ∣ (Q : Subgroup K).index := by
    have := orderOf_dvd_of_pow_eq_one hpow
    rwa [hzo] at this
  exact Q.not_dvd_index hdvd

end Transfer

theorem m11l45_eq_top {X : Type} [Group X] [Finite X] (hKA : KFactM11TwoSignalizer)
    (O : Subgroup X) [O.Normal] (hO : Nat.Coprime 3 (Nat.card O))
    (e : (X ⧸ O) ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M11).Group)
    (T : Sylow 3 X) {A : Subgroup X} (hOA : O ≤ A) {u : X} (huT : u ∈ (T : Subgroup X))
    (huo : orderOf u = 3)
    (hN : ∀ R : Subgroup X, R ≤ (T : Subgroup X) → R ≠ ⊥ → normalizer (R : Set X) ≤ A)
    (hV : ∀ V : Subgroup (X ⧸ O), IsPGroup 2 V →
      QuotientGroup.mk' O u ∈ normalizer (V : Set (X ⧸ O)) →
        V ≤ A.map (QuotientGroup.mk' O)) : A = ⊤ := by
  have hprime : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hprime⟩
  let Qhat : Sylow 3 (X ⧸ O) := T.mapSurjective (QuotientGroup.mk'_surjective O)
  have hQhat : (Qhat : Subgroup (X ⧸ O)) = (T : Subgroup X).map (QuotientGroup.mk' O) :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨-, hfact⟩ := hKA (X ⧸ O) ⟨e⟩ Qhat
  have huQ : QuotientGroup.mk' O u ∈ (Qhat : Subgroup (X ⧸ O)) := by
    rw [hQhat]
    exact mem_map_of_mem _ huT
  have hmain := hfact _ huQ (CFSG.AGLEmbedding.orderOf_mk_of_coprime hprime O hO huo)
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
