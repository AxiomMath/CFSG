module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PointConfigCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2GenDefs
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor (PointConfig pointConfig_of_u3)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G} {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}

theorem u3_torus_lift_gen (hTor : TypeTorusOnCenter Typ p) (hc : PointConfig Typ G p P M x J)
    {c : G} (hcT : c ∈ u3T P x J)
    (hcZ : c ∈ Subgroup.centralizer ((u3T P x J : Subgroup G) : Set G)) (hc1 : c ≠ 1) (k : ℤ)
    (hk : ¬ (p : ℤ) ∣ k) :
    ∃ h ∈ J, h ∈ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) ∧ h * c * h⁻¹ = c ^ k := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, instQ, ψ, hψsurj, hker, hU3⟩ := hc.typ
  haveI : Finite Q := Finite.of_surjective ψ hψsurj
  have hcJ : c ∈ J := (Subgroup.mem_inf.mp hcT).2
  obtain ⟨hOJ, -, hcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p J
  have hcardker : Nat.card ψ.ker = Nat.card (rankThreePrimeCore p J) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv
  have hkercop : ¬ p ∣ Nat.card ψ.ker := by
    rw [hcardker]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcop
  have hTJ : CFSG.ABGLocalTools.IsSylowOf p (u3T P x J) J := by
    obtain ⟨-, -, hsyl, -⟩ := hc.generic
    exact hsyl.inf_of_le_normalizer hc.le_cent hc.cent_le
  obtain ⟨T', hT'⟩ := hTJ.exists_sylow_eq_subgroupOf
  have hmemT' : ∀ y : J, y ∈ (T' : Subgroup J) ↔ (y : G) ∈ u3T P x J := by
    intro y
    rw [hT', Subgroup.mem_subgroupOf]
  have hinj : ∀ t ∈ (T' : Subgroup J), ψ t = 1 → t = 1 :=
    u3main_eq_one_of_ker ψ hkercop T'.isPGroup'
  obtain ⟨Ts, hTs⟩ : ∃ Ts : Sylow p Q, (Ts : Subgroup Q) = (T' : Subgroup J).map ψ :=
    ⟨Sylow.mapSurjective hψsurj T', rfl⟩
  have hTsmem : ∀ y : J, y ∈ (T' : Subgroup J) → ψ y ∈ (Ts : Subgroup Q) := by
    intro y hy
    rw [hTs]
    exact Subgroup.mem_map_of_mem ψ hy
  obtain ⟨cJ, hcJdef⟩ : ∃ cJ : J, (cJ : G) = c := ⟨⟨c, hcJ⟩, rfl⟩
  have hcTJ : cJ ∈ (T' : Subgroup J) := (hmemT' cJ).mpr (by rw [hcJdef]; exact hcT)
  have hcZ' : ∀ q ∈ (Ts : Subgroup Q), q * ψ cJ = ψ cJ * q := by
    intro q hq
    rw [hTs] at hq
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hq
    have hyG : (y : G) ∈ u3T P x J := (hmemT' y).mp hy
    have hyc : (y : G) * c = c * (y : G) := Subgroup.mem_centralizer_iff.mp hcZ (y : G) hyG
    have hyc' : y * cJ = cJ * y := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hcJdef]
      exact hyc)
    simpa only [map_mul] using congrArg ψ hyc'
  have hcJ1 : ψ cJ ≠ 1 := by
    intro h1
    apply hc1
    have h2 : (cJ : G) = 1 := congrArg Subtype.val (hinj cJ hcTJ h1)
    rw [hcJdef] at h2
    exact h2
  obtain ⟨n0, hn0mem, hn0eq⟩ := hTor Q hU3 Ts _ (hTsmem cJ hcTJ)
    (Subgroup.mem_centralizer_iff.mpr hcZ') hcJ1 k hk
  obtain ⟨jJ, hjJ⟩ := hψsurj n0
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup G, H = ((Ts : Subgroup Q).comap ψ).map J.subtype :=
    ⟨_, rfl⟩
  have memH : ∀ y : J, (y : G) ∈ H ↔ ψ y ∈ (Ts : Subgroup Q) := by
    intro y
    rw [hHdef]
    constructor
    · intro hy
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
      have hzy' : z = y := Subtype.ext hzy
      rw [hzy'] at hz
      exact hz
    · intro hy
      exact Subgroup.mem_map_of_mem J.subtype (show y ∈ (Ts : Subgroup Q).comap ψ from hy)
  have hHJ : H ≤ J := by
    rw [hHdef]
    exact Subgroup.map_subtype_le _
  have hTH : u3T P x J ≤ H := by
    intro t ht
    have htJ : t ∈ J := (Subgroup.mem_inf.mp ht).2
    exact (memH ⟨t, htJ⟩).mpr (hTsmem ⟨t, htJ⟩ ((hmemT' ⟨t, htJ⟩).mpr ht))
  have hjH : ∀ g : G, g ∈ H → (jJ : G) * g * (jJ : G)⁻¹ ∈ H := by
    intro g hg
    have hgJ : g ∈ J := hHJ hg
    have hy : ψ (⟨g, hgJ⟩ : J) ∈ (Ts : Subgroup Q) := (memH ⟨g, hgJ⟩).mp hg
    have hz : ψ (jJ * (⟨g, hgJ⟩ : J) * jJ⁻¹) ∈ (Ts : Subgroup Q) := by
      rw [map_mul, map_mul, map_inv, hjJ]
      exact (Subgroup.mem_normalizer_iff.mp hn0mem _).mp hy
    exact (memH (jJ * (⟨g, hgJ⟩ : J) * jJ⁻¹)).mpr hz
  have hTHs : CFSG.ABGLocalTools.IsSylowOf p (u3T P x J) H := hTJ.of_le hTH hHJ
  have hP'H : (u3T P x J).map (MulAut.conj (jJ : G)).toMonoidHom ≤ H := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
    exact hjH t (hTH ht)
  have hP'J : (u3T P x J).map (MulAut.conj (jJ : G)).toMonoidHom ≤ J := hP'H.trans hHJ
  have hmemP' : ∀ t : G, (jJ : G) * t * (jJ : G)⁻¹ ∈
      (u3T P x J).map (MulAut.conj (jJ : G)).toMonoidHom ↔ t ∈ u3T P x J := by
    intro t
    constructor
    · intro ht
      obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.mp ht
      have h2 : (jJ : G) * s * (jJ : G)⁻¹ = (jJ : G) * t * (jJ : G)⁻¹ := hst
      have h3 : s = t := mul_left_cancel (mul_right_cancel h2)
      rw [← h3]
      exact hs
    · intro ht
      exact Subgroup.mem_map_of_mem (MulAut.conj (jJ : G)).toMonoidHom ht
  have hcardP' : Nat.card ((u3T P x J).map (MulAut.conj (jJ : G)).toMonoidHom) =
      Nat.card (u3T P x J) :=
    Subgroup.card_map_of_injective (f := (MulAut.conj (jJ : G)).toMonoidHom)
      (MulAut.conj (jJ : G)).injective
  have hP'Syl : CFSG.ABGLocalTools.IsSylowOf p
      ((u3T P x J).map (MulAut.conj (jJ : G)).toMonoidHom) J :=
    CFSG.ABGLocalTools.isSylowOf_of_card hP'J (hcardP'.trans hTJ.card_eq)
  have hP'Hs : CFSG.ABGLocalTools.IsSylowOf p
      ((u3T P x J).map (MulAut.conj (jJ : G)).toMonoidHom) H :=
    hP'Syl.of_le hP'H hHJ
  obtain ⟨kc, hkH, hk'⟩ := hTHs.exists_mem_conj hP'Hs
  have hnorm : ∀ t : G, t ∈ u3T P x J ↔
      (kc⁻¹ * (jJ : G)) * t * (kc⁻¹ * (jJ : G))⁻¹ ∈ u3T P x J := by
    intro t
    have e : (kc⁻¹ * (jJ : G)) * t * (kc⁻¹ * (jJ : G))⁻¹ =
        kc⁻¹ * ((jJ : G) * t * (jJ : G)⁻¹) * kc := by group
    rw [e, ← hk' ((jJ : G) * t * (jJ : G)⁻¹), hmemP' t]
  have hkJ : kc ∈ J := hHJ hkH
  obtain ⟨kJ, hkJdef⟩ : ∃ kJ : J, (kJ : G) = kc := ⟨⟨kc, hkJ⟩, rfl⟩
  have hkTs : ψ kJ ∈ (Ts : Subgroup Q) := (memH kJ).mp (by rw [hkJdef]; exact hkH)
  have hcomm : Commute (ψ kJ) (ψ cJ) := hcZ' _ hkTs
  obtain ⟨X, hXdef⟩ : ∃ X : J, X = (kJ⁻¹ * jJ) * cJ * (kJ⁻¹ * jJ)⁻¹ := ⟨_, rfl⟩
  have hψX : ψ X = (ψ cJ) ^ k := by
    have e : ψ X = (ψ kJ)⁻¹ * (n0 * ψ cJ * n0⁻¹) * ψ kJ := by
      rw [hXdef]
      simp only [map_mul, map_inv, hjJ]
      group
    rw [e, hn0eq]
    have hc' : Commute (ψ kJ) ((ψ cJ) ^ k) := hcomm.zpow_right k
    rw [mul_assoc, ← hc'.eq, inv_mul_cancel_left]
  have hXG : (X : G) = (kc⁻¹ * (jJ : G)) * c * (kc⁻¹ * (jJ : G))⁻¹ := by
    rw [hXdef]
    simp [hkJdef, hcJdef]
  have hXT : X ∈ (T' : Subgroup J) := (hmemT' X).mpr (by rw [hXG]; exact (hnorm c).mp hcT)
  have hYT : cJ ^ k ∈ (T' : Subgroup J) := by
    refine (hmemT' (cJ ^ k)).mpr ?_
    rw [Subgroup.coe_zpow, hcJdef]
    exact zpow_mem hcT k
  have hdiff : X * (cJ ^ k)⁻¹ ∈ (T' : Subgroup J) :=
    (T' : Subgroup J).mul_mem hXT ((T' : Subgroup J).inv_mem hYT)
  have hdiff1 : ψ (X * (cJ ^ k)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_zpow, hψX, mul_inv_cancel]
  have hXeq : X = cJ ^ k := mul_inv_eq_one.mp (hinj _ hdiff hdiff1)
  have hfin : (kc⁻¹ * (jJ : G)) * c * (kc⁻¹ * (jJ : G))⁻¹ = c ^ k := by
    have h1 := congrArg Subtype.val hXeq
    rw [hXG, Subgroup.coe_zpow, hcJdef] at h1
    exact h1
  exact ⟨kc⁻¹ * (jJ : G), J.mul_mem (J.inv_mem hkJ) jJ.2,
    Subgroup.mem_normalizer_iff.mpr hnorm, hfin⟩


theorem u3_torus_lift (hc : U3Config G p P M x J) {c : G} (hcT : c ∈ u3T P x J)
    (hcZ : c ∈ Subgroup.centralizer ((u3T P x J : Subgroup G) : Set G)) (hc1 : c ≠ 1) (k : ℤ)
    (hk : ¬ (p : ℤ) ∣ k) :
    ∃ h ∈ J, h ∈ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) ∧ h * c * h⁻¹ = c ^ k := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  exact u3_torus_lift_gen (typeTorusOnCenter_u3 hc.five) (pointConfig_of_u3 hc) hcT hcZ hc1 k hk

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
