module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MinusStmt
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnArith
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnCard
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnH90
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnLift

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.GH74.GLS.Stage2.OddAut CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Abstract

open Subgroup

variable {Y G : Type*} [Group Y] [Group G]

theorem card_comap_sup_zpowers [Finite Y] (ψ : Y →* G) (hψ : Function.Injective ψ)
    {T : Subgroup G} (hT : T ≤ ψ.range) {m : Y} (hm : ∀ t ∈ T, ψ m * t * (ψ m)⁻¹ ∈ T)
    (hm3 : ψ m ^ 3 ∈ T) (hmT : ψ m ∉ T) :
    Nat.card ↥(T.comap ψ ⊔ Subgroup.zpowers m) = 3 * Nat.card ↥T := by
  have h1 : ∀ t ∈ T.comap ψ, m * t * m⁻¹ ∈ T.comap ψ := by
    intro t ht
    rw [Subgroup.mem_comap] at ht ⊢
    rw [map_mul, map_mul, map_inv]
    exact hm _ ht
  have h2 : m ^ 3 ∈ T.comap ψ := by
    rw [Subgroup.mem_comap, map_pow]
    exact hm3
  have h3 : m ∉ T.comap ψ := fun h => hmT (Subgroup.mem_comap.1 h)
  rw [card_sup_zpowers_of_cube_mem h1 h2 h3]
  congr 1
  rw [← Subgroup.card_map_of_injective hψ (f := ψ) (K := T.comap ψ), Subgroup.map_comap_eq_self hT]

theorem sup_zpowers_stable (δ : Y →* Y) (T' : Subgroup Y) (m : Y)
    (hT : ∀ t ∈ T', δ t ∈ T') (hm : δ m = m) :
    ∀ n ∈ T' ⊔ Subgroup.zpowers m, δ n ∈ T' ⊔ Subgroup.zpowers m := by
  have hle : T' ⊔ Subgroup.zpowers m ≤ (T' ⊔ Subgroup.zpowers m).comap δ := by
    refine sup_le (fun t ht => ?_) (Subgroup.zpowers_le.2 ?_)
    · exact Subgroup.mem_comap.2 (Subgroup.mem_sup_left (hT t ht))
    · exact Subgroup.mem_comap.2 (by rw [hm]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers m))
  exact fun n hn => Subgroup.mem_comap.1 (hle hn)

end Abstract

section D4

variable {L : Type} [Field L]

theorem monomial_conj_mem_torus_d4 {m h : ModGL TwistTag.D4.tag L}
    (hm : m ∈ monomialSubgroup TwistTag.D4.tag L) (hh : h ∈ torusGroup TwistTag.D4.tag L) :
    m * h * m⁻¹ ∈ torusGroup TwistTag.D4.tag L := by
  have hn := (inferInstance : ((torusGroup TwistTag.D4.tag L).subgroupOf
    (monomialSubgroup TwistTag.D4.tag L)).Normal).conj_mem
      ⟨h, torusGroup_le_monomialSubgroup hh⟩ (Subgroup.mem_subgroupOf.2 hh) ⟨m, hm⟩
  exact Subgroup.mem_subgroupOf.1 hn

theorem twistedTorus_conj_diagramMap_inv [IsAlgClosed L] (Fr : L →+* L)
    {x : ModGL TwistTag.D4.tag L}
    (hx : x ∈ twistedTorusOf (trialityOpposition L) (twistHom TwistTag.D4 L Fr)) :
    (diagramMap TwistTag.D4 L)⁻¹ * x * diagramMap TwistTag.D4 L ∈
      twistedTorusOf (trialityOpposition L) (twistHom TwistTag.D4 L Fr) := by
  obtain ⟨hxT, hxF⟩ := mem_twistedTorusOf.1 hx
  refine mem_twistedTorusOf.2 ⟨?_, ?_⟩
  · obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxT
    rw [d4Minus_h90_conj]
    exact rootDiagUnit_mem_torusGroup _
  · have hc : Commute (diagramMap TwistTag.D4 L) (trialityOpposition L) :=
      diagramMap_comm_trialityOpposition
    have hc1 : (diagramMap TwistTag.D4 L)⁻¹ * trialityOpposition L =
        trialityOpposition L * (diagramMap TwistTag.D4 L)⁻¹ := hc.inv_left.eq
    have hc2 : diagramMap TwistTag.D4 L * (trialityOpposition L)⁻¹ =
        (trialityOpposition L)⁻¹ * diagramMap TwistTag.D4 L := hc.inv_right.eq
    rw [twistHom_conj_diagramMap_inv]
    calc trialityOpposition L * ((diagramMap TwistTag.D4 L)⁻¹ * twistHom TwistTag.D4 L Fr x *
          diagramMap TwistTag.D4 L) * (trialityOpposition L)⁻¹
        = (trialityOpposition L * (diagramMap TwistTag.D4 L)⁻¹) * twistHom TwistTag.D4 L Fr x *
            (diagramMap TwistTag.D4 L * (trialityOpposition L)⁻¹) := by group
      _ = (diagramMap TwistTag.D4 L)⁻¹ * (trialityOpposition L * twistHom TwistTag.D4 L Fr x *
            (trialityOpposition L)⁻¹) * diagramMap TwistTag.D4 L := by
          rw [← hc1, hc2]
          group
      _ = _ := by rw [hxF]

end D4

section Main

variable {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L p]

theorem d4Minus_exists_N (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2)
    (hK : Nat.card K = (p ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {g₀ : ModGL TwistTag.D4.tag L} (hg₀ : D4MinusFrame p f L g₀) :
    ∃ N : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), ¬ 3 ∣ N.index ∧
      (∀ n ∈ N, fieldActor (t := TwistTag.D4) σ σ n ∈ N) ∧
      ∀ n ∈ N, d4MinusPsi σ L g₀ n ∈ monomialSubgroup TwistTag.D4.tag L ∧
        (d4MinusPsi σ L g₀ n ∈ torusGroup TwistTag.D4.tag L →
          d4MinusPsi σ L g₀ n ∈ twistedTorusOf (trialityOpposition L)
            (twistHom TwistTag.D4 L (iterateFrobenius L p f))) := by
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
  refine ⟨T0.comap ψ ⊔ Subgroup.zpowers m', ?_, ?_, ?_⟩
  · have hcardN := card_comap_sup_zpowers ψ hinj hT0ψ hnorm hm3T hmT0
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
  · refine sup_zpowers_stable (fieldActor (t := TwistTag.D4) σ σ).toMonoidHom (T0.comap ψ) m'
      (fun t ht => ?_) ?_
    · rw [Subgroup.mem_comap] at ht ⊢
      change ψ (fieldActor (t := TwistTag.D4) σ σ t) ∈ T0
      rw [hψ, d4MinusPsi_fieldActor Fr hcomm hg₀P t]
      exact twistedTorus_conj_diagramMap_inv Fr ht
    · refine hinj ?_
      change ψ (fieldActor (t := TwistTag.D4) σ σ m') = ψ m'
      rw [hψ, d4MinusPsi_fieldActor Fr hcomm hg₀P m', ← hψ, hm', mul_assoc, ← hmP,
        inv_mul_cancel_left]
  · intro n hn
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

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm1
