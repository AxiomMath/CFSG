module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3FusionLines
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowLift
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Residues
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Fusion
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Plane
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Planes
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Proved
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3QStruct

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_conj_of_le_centralizer {x : G} {Q : Subgroup G}
    (hQ : IsSylowOf 3 Q (centralizer ({x} : Set G))) {g : G}
    (hg : Q ≤ centralizer ({g * x * g⁻¹} : Set G)) :
    ∃ h ∈ normalizer (Q : Set G), h * x * h⁻¹ = g * x * g⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set Q' : Subgroup G := Q.map (MulAut.conj g⁻¹).toMonoidHom with hQ'
  have hQ'mem : ∀ y : G, y ∈ Q' ↔ g * y * g⁻¹ ∈ Q := by
    intro y
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa [mul_assoc] using hq
    · intro hy
      exact ⟨g * y * g⁻¹, hy, by simp [mul_assoc]⟩
  have hQ'C : Q' ≤ C := fun y hy => by
    have h1 : (g * y * g⁻¹) * (g * x * g⁻¹) = (g * x * g⁻¹) * (g * y * g⁻¹) :=
      mem_centralizer_singleton_iff.mp (hg ((hQ'mem y).mp hy))
    rw [mem_centralizer_singleton_iff]
    have h2 : g * (y * x) * g⁻¹ = g * (x * y) * g⁻¹ := by
      calc g * (y * x) * g⁻¹ = (g * y * g⁻¹) * (g * x * g⁻¹) := by group
        _ = (g * x * g⁻¹) * (g * y * g⁻¹) := h1
        _ = g * (x * y) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hQ'card : Nat.card Q' = 3 ^ (Nat.card C).factorization 3 := by
    rw [hQ', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hQ.card_eq
  have hQ'syl : IsSylowOf 3 Q' C := isSylowOf_of_card hQ'C hQ'card
  obtain ⟨k, hkC, hk⟩ := hQ.exists_mem_conj hQ'syl
  have hkx : k * x = x * k := mem_centralizer_singleton_iff.mp hkC
  refine ⟨g * k, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro q
    have h1 : k * q * k⁻¹ ∈ Q' ↔ k⁻¹ * (k * q * k⁻¹) * k ∈ Q := hk _
    have h2 : k⁻¹ * (k * q * k⁻¹) * k = q := by group
    rw [h2] at h1
    have h3 := hQ'mem (k * q * k⁻¹)
    have h4 : g * k * q * (g * k)⁻¹ = g * (k * q * k⁻¹) * g⁻¹ := by group
    rw [h4]
    rw [h3] at h1
    exact h1.symm
  · have : g * k * x * (g * k)⁻¹ = g * (k * x * k⁻¹) * g⁻¹ := by group
    rw [this, hkx]
    group

omit [Finite G] in
theorem inv_conj_mem_commutator_of_mem_normalizer {Q : Subgroup G} {h y : G}
    (hh : h ∈ normalizer (Q : Set G)) (hy : y ∈ ⁅Q, Q⁆) : h⁻¹ * y * h ∈ ⁅Q, Q⁆ := by
  have hQ : Q.map (MulAut.conj h⁻¹).toMonoidHom = Q := by
    ext q
    constructor
    · rintro ⟨q', hq', rfl⟩
      have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ hh) q').mp hq'
      simpa using this
    · intro hq
      refine ⟨h * q * h⁻¹, (mem_normalizer_iff.mp hh q).mp hq, ?_⟩
      simp [mul_assoc]
  have h1 : (⁅Q, Q⁆).map (MulAut.conj h⁻¹).toMonoidHom = ⁅Q, Q⁆ := by
    rw [Subgroup.map_commutator, hQ]
  have h2 : (MulAut.conj h⁻¹).toMonoidHom y ∈ (⁅Q, Q⁆).map (MulAut.conj h⁻¹).toMonoidHom :=
    mem_map_of_mem _ hy
  rw [h1] at h2
  simpa using h2

private theorem u3wc_commutator_mem {T : Subgroup G} (hc : Nat.card T = 3 ^ 3)
    (hnc : ¬ IsMulCommutative T) {a b : G} (ha : a ∈ T) (hb : b ∈ T) :
    a * b * a⁻¹ * b⁻¹ ∈ (center ↥T).map T.subtype := by
  have hcZ : Nat.card (center ↥T) = 3 := u3plane_card_center hc hnc
  have hq : Nat.card (↥T ⧸ center ↥T) = 3 ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥T)
    rw [hc, hcZ] at h
    omega
  have hqc : IsMulCommutative (↥T ⧸ center ↥T) := IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
  have hcomm : (⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥T)⁻¹ * (⟨b, hb⟩ : ↥T)⁻¹ : ↥T) ∈ center ↥T := by
    rw [← QuotientGroup.ker_mk' (center ↥T), MonoidHom.mem_ker]
    have h := hqc.is_comm.comm (QuotientGroup.mk' (center ↥T) ⟨a, ha⟩)
      (QuotientGroup.mk' (center ↥T) ⟨b, hb⟩)
    simp only [map_mul, map_inv]
    rw [h]
    group
  exact ⟨_, hcomm, rfl⟩

theorem u3_lineWeaklyClosed (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore) (hE1 : KFactL28Three)
    (hE3 : KFactL28BorelCore) (hUAct : KFactU3SylowInversion) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsU3Normal M x J) :
    LineWeaklyClosed x ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxP, hxLO, hQsyl, -⟩ := id hgen
  obtain ⟨-, hx1, hx3, -, -⟩ := id hxLO
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hJC := hJ.le_centralizer
  obtain ⟨hcard, hexp, hnc, Z, hZc, hxZ, hZcomm, hTZ, hQeq⟩ :=
    u3_qstruct hS hU0 u3SylowData_proved u3AutData_proved hp hM hgen hJ
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set Q : Subgroup G := (P : Subgroup G) ⊓ C with hQ
  set T : Subgroup G := (P : Subgroup G) ⊓ J with hT
  set A : Subgroup G := (center ↥T).map T.subtype with hA
  have hTP : T ≤ (P : Subgroup G) := inf_le_left
  have hTM : T ≤ M := hTP.trans hPM
  have hTQ : T ≤ Q := le_inf hTP (inf_le_right.trans hJC)
  have hxT : x ∉ T := fun hxT' => hx1 (by
    have : x ∈ T ⊓ Z := ⟨hxT', hxZ⟩
    rwa [hTZ, mem_bot] at this)
  have hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Z) ⟨b, hb⟩)
  have hAmem : ∀ a, a ∈ A ↔ a ∈ T ∧ ∀ s ∈ T, s * a = a * s := by
    intro a
    constructor
    · rintro ⟨a', ha', rfl⟩
      exact ⟨a'.2, fun s hs =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp ha' ⟨s, hs⟩)⟩
    · rintro ⟨haT, hac⟩
      exact ⟨⟨a, haT⟩, Subgroup.mem_center_iff.mpr fun s => Subtype.ext (hac s s.2), rfl⟩
  have hAT : ∀ a ∈ A, a ∈ T := fun a ha => ((hAmem a).mp ha).1
  have core : ∀ y : G, y ∈ Q → IsLargeObstruction 3 M y → (∃ g : G, g * x * g⁻¹ = y) →
      y ∈ zpowers x := by
    intro y hyQ hyLO hconj
    have hy1 : y ≠ 1 := hyLO.2.1
    have hy3 : y ^ 3 = 1 := hyLO.2.2.1
    obtain ⟨t, ht, z, hz, hyeq⟩ := u3l42_decomp hZcomm (by rw [← hQeq]; exact hyQ)
    subst hyeq
    have htz : t * z = z * t := hZcomm t ht z hz
    have ht3 : t ^ 3 = 1 := hexp t ht
    have hz3 : z ^ 3 = 1 := by
      have h := (Commute.mul_pow (show Commute t z from htz) 3).symm.trans hy3
      rwa [ht3, one_mul] at h
    have hzx : z ∈ zpowers x := mem_zpowers_of_isCyclic_of_pow_three hZc hxZ hz hx1 hx3 hz3
    by_cases ht1 : t = 1
    · rw [ht1, one_mul]
      exact hzx
    exfalso
    have hxt : x ∉ zpowers t := fun h => hxT (zpowers_le.mpr ht h)
    have htx : t * x = x * t := mem_centralizer_singleton_iff.mp (hJC ht.2)
    by_cases htA : t ∈ A
    swap
    ·
      obtain ⟨w, hwT, hwt⟩ : ∃ w ∈ T, w * t ≠ t * w := by
        by_contra hno'
        push Not at hno'
        exact htA ((hAmem t).mpr ⟨ht, hno'⟩)
      have hz₀A : w * t * w⁻¹ * t⁻¹ ∈ A := u3wc_commutator_mem hcard hnc hwT ht
      set z₀ : G := w * t * w⁻¹ * t⁻¹ with hz₀
      have hz₀T : z₀ ∈ T := hAT z₀ hz₀A
      have hz₀1 : z₀ ≠ 1 := fun h => hwt (by
        have h1 : w * t * w⁻¹ = t := by
          have := congrArg (· * t) h
          simpa [hz₀] using this
        exact mul_inv_eq_iff_eq_mul.mp h1)
      have hz₀c : ∀ s ∈ T, s * z₀ = z₀ * s := ((hAmem z₀).mp hz₀A).2
      have hwz : w * z * w⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr (hZcomm w hwT z hz)
      have hwy : w * (t * z) * w⁻¹ = z₀ * (t * z) := by
        calc w * (t * z) * w⁻¹ = (w * t * w⁻¹) * (w * z * w⁻¹) := by group
          _ = (z₀ * t) * z := by rw [hwz, hz₀]; group
          _ = z₀ * (t * z) := mul_assoc _ _ _
      have hwz₀ : w * z₀ * w⁻¹ = z₀ := mul_inv_eq_iff_eq_mul.mpr (hz₀c w hwT)
      have hcomm : z₀ * (t * z) = (t * z) * z₀ := by
        calc z₀ * (t * z) = (z₀ * t) * z := (mul_assoc _ _ _).symm
          _ = (t * z₀) * z := by rw [hz₀c t ht]
          _ = t * (z₀ * z) := mul_assoc _ _ _
          _ = t * (z * z₀) := by rw [hZcomm z₀ hz₀T z hz]
          _ = (t * z) * z₀ := (mul_assoc _ _ _).symm
      have hyz : t * z ∉ zpowers z₀ := fun h => by
        have hyA : t * z ∈ A := zpowers_le.mpr hz₀A h
        have hzT : z ∈ T := by
          have : z = t⁻¹ * (t * z) := by group
          rw [this]
          exact T.mul_mem (T.inv_mem ht) (hAT _ hyA)
        have hz1 : z = 1 := by
          have : z ∈ T ⊓ Z := ⟨hzT, hz⟩
          rwa [hTZ, mem_bot] at this
        rw [hz1, mul_one] at hyA
        exact htA hyA
      exact false_of_coset_lines hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM hyLO
        (hTM hz₀T) hz₀1 (hexp z₀ hz₀T) hyz hcomm (hTM hwT) hwy hwz₀
    by_cases hz1 : z = 1
    ·
      subst hz1
      obtain ⟨g, hg⟩ := hconj
      have hQc : ∀ q ∈ Q, q * (t * 1) = (t * 1) * q := by
        intro q hq
        obtain ⟨t', ht', z', hz', rfl⟩ := u3l42_decomp hZcomm (by rw [← hQeq]; exact hq)
        have h1 : t' * t = t * t' := ((hAmem t).mp htA).2 t' ht'
        have h2 : z' * t = t * z' := (hZcomm t ht z' hz').symm
        calc t' * z' * (t * 1) = t' * (z' * t) := by rw [mul_one, mul_assoc]
          _ = t' * (t * z') := by rw [h2]
          _ = (t' * t) * z' := (mul_assoc _ _ _).symm
          _ = (t * t') * z' := by rw [h1]
          _ = (t * 1) * (t' * z') := by rw [mul_one, mul_assoc]
      have hQy : Q ≤ centralizer ({g * x * g⁻¹} : Set G) := fun q hq => by
        rw [hg]
        exact mem_centralizer_singleton_iff.mpr (hQc q hq)
      obtain ⟨h, hhN, hhx⟩ := exists_mem_normalizer_conj_of_le_centralizer hQsyl hQy
      have htQ' : t ∈ ⁅Q, Q⁆ :=
        Subgroup.commutator_mono hTQ hTQ (u3_center_le_commutator hcard hnc htA)
      have hx' : h⁻¹ * t * h = x := by
        have h1 : h * x * h⁻¹ = t := by rw [hhx, hg, mul_one]
        calc h⁻¹ * t * h = h⁻¹ * (h * x * h⁻¹) * h := by rw [h1]
          _ = x := by group
      have hxQ' : x ∈ ⁅Q, Q⁆ := by
        have := inv_conj_mem_commutator_of_mem_normalizer hhN htQ'
        rwa [hx'] at this
      have hQ'T : ⁅Q, Q⁆ ≤ T := Subgroup.commutator_le.mpr fun a ha b hb =>
        u3l42_commutator_mem hZcomm hZab (by rw [← hQeq]; exact ha) (by rw [← hQeq]; exact hb)
      have : x ∈ T ⊓ Z := ⟨hQ'T hxQ', hxZ⟩
      rw [hTZ, mem_bot] at this
      exact hx1 this
    ·
      obtain ⟨n, hnC, hnN, hninv⟩ := u3_exists_inverting hUAct hgen hJ
      have hnM : n ∈ M := u3_normalizer_le hS hU0 hp hM hTM hexp hcard hnc hnN
      have hnx : n * x * n⁻¹ = x := mul_inv_eq_iff_eq_mul.mpr
        (mem_centralizer_singleton_iff.mp hnC)
      have hyD : t * z ∈ zpowers t ⊔ zpowers x :=
        Subgroup.mul_mem _ (mem_sup_left (mem_zpowers t)) (mem_sup_right hzx)
      have hyk : t * z ∉ zpowers t := fun h => by
        have hz' : z ∈ zpowers t := by
          have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (mem_zpowers t)) h
          simpa using this
        have hcx : zpowers z = zpowers x :=
          p34_zpowers_eq_of_mem (orderOf_eq_prime hx3 hx1) hzx hz1
        have hxz : x ∈ zpowers z := by
          rw [hcx]
          exact mem_zpowers x
        exact hxt (zpowers_le.mpr hz' hxz)
      have hyx : t * z ∉ zpowers x := fun h => by
        have htx' : t ∈ zpowers x := by
          have := Subgroup.mul_mem _ h (Subgroup.inv_mem _ hzx)
          simpa using this
        have : t ∈ T ⊓ Z := ⟨ht, zpowers_le.mpr hxZ htx'⟩
        rw [hTZ, mem_bot] at this
        exact ht1 this
      exact false_of_mixed_pair hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM hxLO
        (hTM ht) ht1 ht3 hxt htx hnM hnx (hninv t htA) hyD hyk hyx hyLO
  intro g hg
  have hyQ : g * x * g⁻¹ ∈ Q := hg ⟨x, mem_zpowers x, rfl⟩
  have hyLO : IsLargeObstruction 3 M (g * x * g⁻¹) :=
    isLargeObstruction_conj_of_map_le hS hU0 hp hM hxP hxLO (hg.trans inf_le_left)
  have hyx : g * x * g⁻¹ ∈ zpowers x := core _ hyQ hyLO ⟨g, rfl⟩
  have hconj : (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers (g * x * g⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [hconj]
  exact p34_zpowers_eq_of_mem (orderOf_eq_prime hx3 hx1) hyx hyLO.2.1

theorem GL83GenericPrimeThreeU3Fusion.of_kfacts (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (K2 : StronglyEmbeddedCyclicOuterKFact) (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree)
    (hno : NoExcludedSection3 G) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three)
    (hKA : KFactM11TwoSignalizer) (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore)
    (hE1 : KFactL28Three) (hE3 : KFactL28BorelCore) (hUAct : KFactU3SylowInversion) :
    GL83GenericPrimeThreeU3Fusion G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ
  subst hp3
  have hJ : IsU3Normal M x J :=
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩
  have hwc := u3_lineWeaklyClosed hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hUAct hp hM
    hgen hJ
  obtain ⟨hxP, ⟨-, hx1, hx3, -, -⟩, -, -⟩ := id hgen
  have hPC := a6fus_le_centralizer_of_wc hxP hx1 hx3 hwc
  exact ⟨hPC, by rwa [inf_eq_left.mpr hPC] at hwc⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
