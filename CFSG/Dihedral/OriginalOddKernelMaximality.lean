module

public import CFSG.Dihedral.OriginalSylowControl
public import CFSG.Dihedral.OriginalInvolutions
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (d : OriginalData G)

theorem prime_dvd_R_of_involution_fixed (p : ℕ) (hp : p.Prime)
    (U : Subgroup G) (hU : IsPGroup p U) (hne : U ≠ ⊥)
    (x : G) (hx : orderOf x = 2) (hfixed : U ≤ Subgroup.centralizer ({x} : Set G))
    (hodd : Odd p) : p ∣ Nat.card d.R := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := d.involutions_conjugate x d.t hx d.t_order
  let T := U.map (MulAut.conj g).toMonoidHom
  have hT : T ≤ d.C := by
    rw [d.centralizer]
    rintro y ⟨u, hu, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    have hz' : z = d.t := by simpa only [Set.mem_singleton_iff, t] using hz
    subst z
    have hux := Subgroup.mem_centralizer_iff.mp (hfixed hu) x (by simp)
    change d.t * (g * u * g⁻¹) = (g * u * g⁻¹) * d.t
    rw [← hg]
    calc
      (g * x * g⁻¹) * (g * u * g⁻¹) = g * (x * u) * g⁻¹ := by group
      _ = g * (u * x) * g⁻¹ := by rw [hux]
      _ = (g * u * g⁻¹) * (g * x * g⁻¹) := by group
  have hpU : p ∣ Nat.card U := by
    rcases hU.card_eq_or_dvd with hone | hdiv
    · exact (hne ((Subgroup.eq_bot_iff_card U).mpr hone)).elim
    · exact hdiv
  have hpT : p ∣ Nat.card T := by
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hpC := hpT.trans (Subgroup.card_dvd_of_le hT)
  rw [d.centralizer_card] at hpC
  rcases hp.dvd_mul.mp hpC with hR | htwo
  · exact hR
  · have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow htwo
    have heq := (Nat.dvd_prime Nat.prime_two).mp hp2
    rcases heq with hone | htwo
    · exact (hp.ne_one hone).elim
    · exact (hodd.not_two_dvd_nat (htwo ▸ dvd_rfl)).elim

theorem primeSupport_of_normalized_odd (W : Subgroup G) (hodd : Odd (Nat.card W))
    (hW : NormalizedBy W (d.S : Subgroup G)) :
    primeSupport W ⊆ primeSupport d.R := by
  intro p hpW
  obtain ⟨hp, hpdiv⟩ := hpW
  let : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hodd.of_dvd_nat hpdiv
  obtain ⟨U, hUS, hUnontriv⟩ :=
    SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
      2 p Nat.prime_two hp (d.S : Subgroup G) W d.S.isPGroup' hW
      (Nat.prime_two.coprime_iff_not_dvd.mpr hodd.not_two_dvd_nat) hpdiv
  let P := (U : Subgroup W).map W.subtype
  have hP : IsPGroup p P := U.isPGroup'.map W.subtype
  have hPodd : Odd (Nat.card P) := hodd.of_dvd_nat
    (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _))
  obtain ⟨e⟩ := d.sylow_dihedral
  obtain ⟨V, hVS, hV⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (d.S : Subgroup G) (by have := d.three_le; omega) e
  let _ := hV
  have hpower : ∀ v : V, v ^ 2 = 1 := by
    intro v
    simpa only [pow_two] using IsKleinFour.mul_self v
  have hgen := RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    2 Nat.prime_two V P hpower (by simp) hPodd.not_two_dvd_nat (hVS.trans hUS)
  have hex : ∃ v : V, v ≠ 1 ∧ P ⊓ Subgroup.centralizer ({(v : G)} : Set G) ≠ ⊥ := by
    by_contra hno
    have hall : ∀ v : V, v ≠ 1 →
        P ⊓ Subgroup.centralizer ({(v : G)} : Set G) = ⊥ := by
      simpa only [not_exists, not_and, not_not] using hno
    have hzero : P = ⊥ := by
      rw [hgen]
      exact iSup_eq_bot.mpr fun v => iSup_eq_bot.mpr fun hv => hall v hv
    exact hUnontriv hzero
  obtain ⟨v, hv, hfixed⟩ := hex
  have hvorder : orderOf (v : G) = 2 := by
    apply orderOf_eq_prime
    · exact congrArg Subtype.val (hpower v)
    · intro heq
      exact hv (Subtype.ext heq)
  exact ⟨hp, d.prime_dvd_R_of_involution_fixed p hp _ (hP.to_le inf_le_left)
    hfixed v hvorder inf_le_right hpodd⟩

theorem odd_overgroup_eq (hc : d.CanonicalNormalizers)
    (W : Subgroup G) (hodd : Odd (Nat.card W))
    (hW : NormalizedBy W (d.S : Subgroup G)) (hRW : d.R ≤ W) : W = d.R := by
  have hsupp := d.primeSupport_of_normalized_odd W hodd hW
  have hRnorm : NormalizedBy d.R (d.S : Subgroup G) :=
    d.sylow_le_centralizer.trans d.centralizer_le_normalizer
  have htop : d.R.subgroupOf W = ⊤ := by
    apply RankThreeEvenClassification.Helpers.subgroup_eq_top_of_contains_sylows
    intro p hp
    let : Fact p.Prime := ⟨hp⟩
    by_cases hpW : p ∣ Nat.card W
    · have hpR := hsupp ⟨hp, hpW⟩
      obtain ⟨P, hPR, hPS⟩ := normalized_exists_sylow 2 p Nat.prime_two hp
        (d.S : Subgroup G) d.R d.S.isPGroup' hRnorm
        (Nat.prime_two.coprime_iff_not_dvd.mpr d.R_odd.not_two_dvd_nat)
      have hmax := (hc.1 p hpR P hPR hPS).1
      change IsPGroup p P ∧ NormalizedBy P (d.S : Subgroup G) ∧
        (∀ Q : Subgroup G, IsPGroup p Q → NormalizedBy Q (d.S : Subgroup G) →
          P ≤ Q → Q = P) at hmax
      obtain ⟨Q, hQW, hPQ, hQS⟩ := normalized_sylow_containing 2 p Nat.prime_two hp
        (d.S : Subgroup G) W P d.S.isPGroup' hW
        (Nat.prime_two.coprime_iff_not_dvd.mpr hodd.not_two_dvd_nat)
        (hPR.1.trans hRW) hPR.2.1 hPS
      have hQP := hmax.2.2 Q hQW.2.1 hQS hPQ
      obtain ⟨T, hT⟩ := (isSylowIn_iff_exists_sylow p Q W).mp hQW
      refine ⟨T, ?_⟩
      intro x hx
      have hm := Subgroup.mem_map_of_mem W.subtype hx
      rw [hT, hQP] at hm
      exact hPR.1 hm
    · let T : Sylow p W := Classical.choice inferInstance
      have hcard : Nat.card (T : Subgroup W) = 1 := by
        rw [T.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hpW, pow_zero]
      have hT : (T : Subgroup W) = ⊥ := (Subgroup.eq_bot_iff_card _).mpr hcard
      exact ⟨T, by rw [hT]; exact bot_le⟩
  exact (Subgroup.subgroupOf_eq_top.mp htop).antisymm hRW

end CFSG.DihedralBlueprint.OriginalData
