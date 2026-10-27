module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnSub

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.GH74.GLS.Stage2.OddAut CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Main

variable {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L p]

theorem d4Minus_exists_N' (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2)
    (hK : Nat.card K = (p ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {g₀ : ModGL TwistTag.D4.tag L} (hg₀ : D4MinusFrame p f L g₀) :
    ∃ (T' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (m' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (∀ y, y ∈ T' ↔ d4MinusPsi σ L g₀ y ∈ twistedTorusOf (trialityOpposition L)
        (twistHom TwistTag.D4 L (iterateFrobenius L p f))) ∧
      m' ∉ T' ∧ m' ^ 3 ∈ T' ∧ (∀ t ∈ T', m' * t * m'⁻¹ ∈ T') ∧
      fieldActor (t := TwistTag.D4) σ σ m' = m' ∧
      (∀ t ∈ T', fieldActor (t := TwistTag.D4) σ σ t ∈ T') ∧
      ¬ 3 ∣ (T' ⊔ Subgroup.zpowers m').index ∧
      (∀ n ∈ T' ⊔ Subgroup.zpowers m', d4MinusPsi σ L g₀ n ∈ monomialSubgroup TwistTag.D4.tag L ∧
        (d4MinusPsi σ L g₀ n ∈ torusGroup TwistTag.D4.tag L →
          d4MinusPsi σ L g₀ n ∈ twistedTorusOf (trialityOpposition L)
            (twistHom TwistTag.D4 L (iterateFrobenius L p f)))) ∧
      d4MinusPsi σ L g₀ m' ∈ monomialSubgroup TwistTag.D4.tag L ∧
      d4MinusPsi σ L g₀ m' ∉ torusGroup TwistTag.D4.tag L := by
  classical
  have hp : p.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨hg₀C, hg₀P, hg₀F⟩ := hg₀
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, hFr, map_pow]
  set z : ModGL TwistTag.D4.tag L := trialityOpposition L with hz
  set F := twistHom TwistTag.D4 L Fr with hF
  set T0 := twistedTorusOf z F with hT0
  set ψ := d4MinusPsi σ L g₀ with hψ
  have hrange := d4MinusPsi_mem_range_iff hp hf hK hσ Fr hFr hg₀C hg₀F
  have hinj : Function.Injective ψ := d4MinusPsi_injective g₀
  obtain ⟨m, hmM, hmP, hmF, hmT, hm3⟩ := exists_d4Minus_lift Fr (q := p ^ f) hFr
  have hmC : m ∈ adjointGroup TwistTag.D4.tag L := monomialSubgroup_le_adjointGroup' hmM
  obtain ⟨m', hm'⟩ := (hrange m).2 ⟨hmC, hmF⟩
  have hT0ψ : T0 ≤ ψ.range := fun x hx =>
    (hrange x).2 ⟨twistedTorusOf_le_adjointGroup _ _ hx, (mem_twistedTorusOf.1 hx).2⟩
  have hnorm : ∀ t ∈ T0, ψ m' * t * (ψ m')⁻¹ ∈ T0 := by
    intro t ht
    obtain ⟨htT, htF⟩ := mem_twistedTorusOf.1 ht
    rw [hm']
    refine mem_twistedTorusOf.2 ⟨monomial_conj_mem_torus_d4 hmM htT, ?_⟩
    have e : z * F (m * t * m⁻¹) * z⁻¹ = (z * F m * z⁻¹) * (z * F t * z⁻¹) * (z * F m * z⁻¹)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    rw [e, hmF, htF]
  have hm3T : ψ m' ^ 3 ∈ T0 := by
    rw [hm']
    refine mem_twistedTorusOf.2 ⟨hm3, ?_⟩
    have e : z * F (m ^ 3) * z⁻¹ = (z * F m * z⁻¹) ^ 3 := by
      simp only [map_pow, conj_pow]
    rw [e, hmF]
  have hmT0 : ψ m' ∉ T0 := by
    rw [hm']
    exact fun h => hmT (mem_twistedTorusOf.1 h).1
  have hmP' : fieldActor (t := TwistTag.D4) σ σ m' = m' := by
    refine hinj ?_
    rw [hψ, d4MinusPsi_fieldActor Fr hcomm hg₀P m', ← hψ, hm', mul_assoc, ← hmP,
      inv_mul_cancel_left]
  have hTstab : ∀ t ∈ T0.comap ψ, fieldActor (t := TwistTag.D4) σ σ t ∈ T0.comap ψ := by
    intro t ht
    rw [Subgroup.mem_comap] at ht ⊢
    change ψ (fieldActor (t := TwistTag.D4) σ σ t) ∈ T0
    rw [hψ, d4MinusPsi_fieldActor Fr hcomm hg₀P t]
    exact twistedTorus_conj_diagramMap_inv Fr ht
  have hidx : ¬ 3 ∣ (T0.comap ψ ⊔ Subgroup.zpowers m').index := by
    have hcardN := card_comap_sup_zpowers ψ hinj hT0ψ hnorm hm3T hmT0
    have hT0card : Nat.card T0 = (p ^ f + 1) * ((p ^ f) ^ 3 + 1) := by
      rw [hT0, hz, hF, d4Q_twistedTorus Fr, Subgroup.card_map_of_injective rootDiagUnit_injective]
      exact d4Q_card (dvd_pow_self p (by omega)) hFr
    have hY := (triality_both_orientations_exact_finite_order p f hp hf K hK 1 (Or.inl rfl)
      σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)).1
    have h := Subgroup.card_mul_index (T0.comap ψ ⊔ Subgroup.zpowers m')
    rw [hcardN, hT0card, hY] at h
    exact not_dvd_index_minus (p ^ f) _ hq (Nat.one_lt_pow (by omega) hp.one_lt) (by
      rw [← h]
      ring)
  have hmono : ∀ n ∈ T0.comap ψ ⊔ Subgroup.zpowers m', ψ n ∈ monomialSubgroup TwistTag.D4.tag L ∧
      (ψ n ∈ torusGroup TwistTag.D4.tag L → ψ n ∈ T0) := by
    intro n hn
    have hNle : T0.comap ψ ⊔ Subgroup.zpowers m' ≤ (T0 ⊔ Subgroup.zpowers m).comap ψ := by
      refine sup_le (fun t ht => ?_) (Subgroup.zpowers_le.2 ?_)
      · exact Subgroup.mem_comap.2 (Subgroup.mem_sup_left (Subgroup.mem_comap.1 ht))
      · exact Subgroup.mem_comap.2 (by
          rw [hm']
          exact Subgroup.mem_sup_right (Subgroup.mem_zpowers m))
    have hn' : ψ n ∈ T0 ⊔ Subgroup.zpowers m := Subgroup.mem_comap.1 (hNle hn)
    refine ⟨?_, fun htor => ?_⟩
    · exact (sup_le (fun x hx => torusGroup_le_monomialSubgroup (mem_twistedTorusOf.1 hx).1)
        (Subgroup.zpowers_le.2 hmM)) hn'
    · exact mem_twistedTorusOf.2 ⟨htor, ((hrange (ψ n)).1 ⟨n, rfl⟩).2⟩
  refine ⟨T0.comap ψ, m', fun y => Subgroup.mem_comap, hmT0, ?_, ?_, hmP', hTstab, hidx, hmono, ?_,
    ?_⟩
  · rw [Subgroup.mem_comap, map_pow]
    exact hm3T
  · intro t ht
    rw [Subgroup.mem_comap] at ht ⊢
    rw [map_mul, map_mul, map_inv]
    exact hnorm _ ht
  · rw [hm']
    exact hmM
  · rw [hm']
    exact hmT

end Main
end CFSG.GH74.GLS.Stage2.Bender.Thm1
