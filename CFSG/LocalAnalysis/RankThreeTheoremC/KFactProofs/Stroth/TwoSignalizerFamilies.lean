module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTwoGroupCases
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneLinTwo
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneUnitary
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TwoSignalizer

open CFSG.AGLEmbedding
open scoped commutatorElement

section Criterion

private theorem map_eq_of_ti {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (U : Sylow p K)
    (hti : ∀ t ∈ (U : Subgroup K), t ≠ 1 → ∀ g : K, g * t * g⁻¹ ∈ (U : Subgroup K) →
      g ∈ Subgroup.normalizer ((U : Subgroup K) : Set K))
    (α : MulAut K) {e : K} (heU : e ∈ (U : Subgroup K)) (he1 : e ≠ 1) (hαe : α e = e) :
    (U : Subgroup K).map α.toMonoidHom = (U : Subgroup K) := by
  have hsurj : Function.Surjective α.toMonoidHom := α.surjective
  have hQ : ((U.mapSurjective hsurj : Sylow p K) : Subgroup K) =
      (U : Subgroup K).map α.toMonoidHom := Sylow.coe_mapSurjective hsurj U
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K U (U.mapSurjective hsurj)
  have heQ : e ∈ ((U.mapSurjective hsurj : Sylow p K) : Subgroup K) := by
    rw [hQ]
    exact ⟨e, heU, hαe⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at heQ
  obtain ⟨s, hs, hse⟩ := heQ
  have hge : g * s * g⁻¹ = e := by
    simpa [MulAut.smul_def, MulAut.conj_apply] using hse
  have hs1 : s ≠ 1 := by
    rintro rfl
    apply he1
    rw [← hge]
    group
  have hgN : g ∈ Subgroup.normalizer ((U : Subgroup K) : Set K) :=
    hti s hs hs1 g (hge ▸ heU)
  rw [← hQ, ← hg, Sylow.smul_eq_iff_mem_normalizer.2 hgN]

variable {X : Type} [Group X] [Finite X]

private theorem eq_one_of_mem_of_mem {p : ℕ} (hp : p.Prime) {V T : Subgroup X}
    (hV : IsPGroup p V) (hT : ¬ p ∣ Nat.card T) {x : X} (hxV : x ∈ V) (hxT : x ∈ T) :
    x = 1 := by
  obtain ⟨k, hk⟩ := hV ⟨x, hxV⟩
  have h1 : x ^ p ^ k = 1 := congrArg Subtype.val hk
  have h2 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf x ∣ Nat.card T := Subgroup.orderOf_dvd_natCard T hxT
  have h4 : Nat.Coprime (orderOf x) (p ^ k) :=
    (Nat.Coprime.coprime_dvd_right h3 (Nat.Coprime.pow_left k
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hT))).symm
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h4 h2)

theorem commutator_eq_bot_of_ti_sylow {p : ℕ} [Fact p.Prime] {K : Subgroup X} [K.Normal]
    (U : Sylow p K)
    (hti : ∀ t ∈ (U : Subgroup K), t ≠ 1 → ∀ g : K, g * t * g⁻¹ ∈ (U : Subgroup K) →
      g ∈ Subgroup.normalizer ((U : Subgroup K) : Set K))
    {B : Subgroup X} (hBU : B ≤ (U : Subgroup K).map K.subtype)
    (hBexp : ∀ b ∈ B, b ^ p = 1) (hBcard : Nat.card B = p ^ 2)
    {T : Subgroup X} (hT : ¬ p ∣ Nat.card T) (hBT : B ≤ Subgroup.normalizer (T : Set X)) :
    ⁅B, T⁆ = ⊥ := by
  have hp : p.Prime := Fact.out
  set V : Subgroup X := (U : Subgroup K).map K.subtype
  have hcent : ∀ b ∈ B, b ≠ 1 → ∀ t ∈ T, t * b = b * t →
      t ∈ Subgroup.normalizer (V : Set X) := by
    intro b hb hb1 t _ htb
    obtain ⟨u, hu, rfl⟩ := hBU hb
    have hu1 : u ≠ 1 := by
      rintro rfl
      exact hb1 rfl
    have hα : MulAut.conjNormal t u = u := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul]
      exact htb
    have hUα := map_eq_of_ti U hti (MulAut.conjNormal t) hu hu1 hα
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨x, hx, rfl⟩
    have h1 : MulAut.conjNormal t x ∈
        (U : Subgroup K).map (MulAut.conjNormal t).toMonoidHom := ⟨x, hx, rfl⟩
    rw [hUα] at h1
    exact ⟨_, h1, MulAut.conjNormal_apply t x⟩
  have hpower : ∀ member : B, member ^ p = 1 := fun m => Subtype.ext (hBexp m m.2)
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane p
    hp B T hpower hBcard hT hBT
  have hTle : T ≤ Subgroup.normalizer (V : Set X) := by
    refine hgen.le.trans (iSup_le fun m => iSup_le fun hm => ?_)
    rintro t ⟨htT, htC⟩
    exact hcent m m.2 (fun h => hm (Subtype.ext h)) t htT
      (Subgroup.mem_centralizer_singleton_iff.1 htC)
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro b hb t ht
  have hbV : b ∈ V := hBU hb
  have h1 : ⁅b, t⁆ ∈ V := by
    have h2 : t * b⁻¹ * t⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hTle ht) b⁻¹).1 (V.inv_mem hbV)
    simpa [commutatorElement_def, mul_assoc] using V.mul_mem hbV h2
  have h2 : ⁅b, t⁆ ∈ T := by
    have h3 : b * t * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hBT hb) t).1 ht
    simpa [commutatorElement_def] using T.mul_mem h3 (T.inv_mem ht)
  rw [Subgroup.mem_bot]
  exact eq_one_of_mem_of_mem hp (U.isPGroup'.map K.subtype) hT h1 h2

theorem commutator_eq_bot_of_forall_ti_sylow {p : ℕ} [Fact p.Prime] {K : Subgroup X} [K.Normal]
    (hti : ∀ U : Sylow p K, ∀ t ∈ (U : Subgroup K), t ≠ 1 → ∀ g : K,
      g * t * g⁻¹ ∈ (U : Subgroup K) → g ∈ Subgroup.normalizer ((U : Subgroup K) : Set K))
    {B : Subgroup X} (hBK : B ≤ K) (hBexp : ∀ b ∈ B, b ^ p = 1) (hBcard : Nat.card B = p ^ 2)
    {T : Subgroup X} (hT : ¬ p ∣ Nat.card T) (hBT : B ≤ Subgroup.normalizer (T : Set X)) :
    ⁅B, T⁆ = ⊥ := by
  have hBp : IsPGroup p (B.subgroupOf K) := by
    intro g
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simpa using hBexp g.1.1 g.2
  obtain ⟨U, hU⟩ := hBp.exists_le_sylow
  refine commutator_eq_bot_of_ti_sylow U (hti U) (fun b hb => ?_) hBexp hBcard hT hBT
  exact ⟨⟨b, hBK hb⟩, hU (Subgroup.mem_subgroupOf.2 hb), rfl⟩

private theorem not_dvd_card_of_isPGroup_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T : Subgroup X}
    (hT : IsPGroup 2 T) : ¬ p ∣ Nat.card T := by
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  rw [hk]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))

end Criterion

section Families

theorem twoSignalizerL2_holds : TwoSignalizerL2 := by
  intro p _ hp2 X _ _ K hKn _ _ B hB hBc _ ⟨⟨e⟩, hBK⟩ T hT hBT
  have hfs : Function.Surjective e.toMonoidHom := e.surjective
  have hcomm : ⁅B, T⁆ = ⊥ := commutator_eq_bot_of_forall_ti_sylow
    (fun U => (SmallRankOneData.of_equiv e (Sylow.coe_mapSurjective hfs U).symm
      (smallRankOneData_psl2GF hp2 (U.mapSurjective hfs))).ti)
    hBK hB.2 hBc (not_dvd_card_of_isPGroup_two Fact.out hp2 hT) hBT
  rw [hcomm]
  exact bot_le

theorem twoSignalizerU3_holds : TwoSignalizerU3 := by
  intro p hp hp2 X _ _ K hKn _ _ B hB hBc _ ⟨⟨q, hqp, hq1, hv, ⟨e0⟩⟩, hBK⟩ T hT hBT
  have : Fact p.Prime := ⟨hp⟩
  have hIS : IsSmallUnitary p K := ⟨⟨.twistedA 2 q, hv⟩, ⟨q, hqp, hq1, rfl⟩, ⟨e0⟩⟩
  have hcomm : ⁅B, T⁆ = ⊥ := commutator_eq_bot_of_forall_ti_sylow
    (fun U => (smallRankOneData_of_isSmallUnitary hp hIS U).ti)
    hBK hB.2 hBc (not_dvd_card_of_isPGroup_two hp hp2 hT) hBT
  rw [hcomm]
  exact bot_le

end Families

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TwoSignalizer
