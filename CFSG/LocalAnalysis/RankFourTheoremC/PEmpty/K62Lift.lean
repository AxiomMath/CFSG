module

public import CFSG.RankThree.PartTwo.Sec4.T444.Coprime
import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (IsTwoInvariantIn IsMaxTwoInvariantIn)

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem not_dvd_card_comap (hp : p.Prime) (hp2 : p ≠ 2) {D : Subgroup X} [D.Normal]
    (hD : ¬ p ∣ Nat.card D) {S : Subgroup (X ⧸ D)} (hS : IsPGroup 2 S) :
    ¬ p ∣ Nat.card (S.comap (QuotientGroup.mk' D)) := by
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hgS : QuotientGroup.mk' D (g : X) ∈ S := g.2
  obtain ⟨k, hk⟩ := hS ⟨_, hgS⟩
  have h2 : (QuotientGroup.mk' D (g : X)) ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hgp : (g : X) ^ p = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    simpa using congrArg Subtype.val this
  have hp' : (QuotientGroup.mk' D (g : X)) ^ p = 1 := by rw [← map_pow, hgp, map_one]
  have hcop : Nat.Coprime p (2 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h1 : QuotientGroup.mk' D (g : X) = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hp', h2⟩
  have hgD : (g : X) ∈ D := by
    have : (g : X) ∈ (QuotientGroup.mk' D).ker := h1
    rwa [QuotientGroup.ker_mk'] at this
  apply hD
  rw [← hg, ← Subgroup.orderOf_coe g, ← Subgroup.orderOf_mk (g : X) hgD]
  exact orderOf_dvd_natCard _

theorem mem_normalizer_comap {D : Subgroup X} [D.Normal] {S : Subgroup (X ⧸ D)} {w : X}
    (h : QuotientGroup.mk' D w ∈ normalizer (S : Set (X ⧸ D))) :
    w ∈ normalizer ((S.comap (QuotientGroup.mk' D) : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff]
  intro g
  have := (mem_normalizer_iff.mp h) (QuotientGroup.mk' D g)
  simpa [mem_comap, map_mul, map_inv] using this

theorem le_normalizer_comap {D : Subgroup X} [D.Normal] {B : Subgroup X} {S : Subgroup (X ⧸ D)}
    (h : B.map (QuotientGroup.mk' D) ≤ normalizer (S : Set (X ⧸ D))) :
    B ≤ normalizer ((S.comap (QuotientGroup.mk' D) : Subgroup X) : Set X) :=
  fun b hb => mem_normalizer_comap (h ⟨b, hb, rfl⟩)

theorem fusionIsSylowIn_of_isMax (hp : p.Prime) {B T K : Subgroup X} (hB : IsPGroup p B)
    (hT : IsMaxTwoInvariantIn B ⊤ T) (hTK : T ≤ K) (hK : ¬ p ∣ Nat.card K)
    (hBK : B ≤ normalizer (K : Set X)) : fusionIsSylowIn 2 T K := by
  obtain ⟨⟨-, hT2, hBT⟩, hmax⟩ := hT
  obtain ⟨R, hRsyl, hTR, hBR⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    hp Nat.prime_two hB hK hBK hTK hT2 hBT
  have hRT : R = T := hmax R ⟨le_top, hRsyl.2.1, hBR⟩ hTR
  exact hRT ▸ hRsyl

theorem isMaxTwoInvariantIn_map (hp : p.Prime) (hp2 : p ≠ 2) {D B T : Subgroup X} [D.Normal]
    (hD : ¬ p ∣ Nat.card D) (hB : IsPGroup p B) (hT : IsMaxTwoInvariantIn B ⊤ T) :
    IsMaxTwoInvariantIn (B.map (QuotientGroup.mk' D)) ⊤ (T.map (QuotientGroup.mk' D)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' D with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective D
  obtain ⟨⟨-, hT2, hBT⟩, hmax⟩ := hT
  have hT' : IsMaxTwoInvariantIn B ⊤ T := ⟨⟨le_top, hT2, hBT⟩, hmax⟩
  refine ⟨⟨le_top, hT2.map π, ?_⟩, fun S' hS' hTS' => ?_⟩
  · exact (Subgroup.map_mono hBT).trans (Subgroup.le_normalizer_map π)
  · obtain ⟨-, hS'2, hBS'⟩ := hS'
    have hS3 : ¬ p ∣ Nat.card (S'.comap π) := not_dvd_card_comap hp hp2 hD hS'2
    have hTS : T ≤ S'.comap π := fun t ht => hTS' ⟨t, ht, rfl⟩
    have hsyl := fusionIsSylowIn_of_isMax hp hB hT' hTS hS3 (le_normalizer_comap hBS')
    obtain ⟨P2, hP2⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hsyl
    let ρ : ↥(S'.comap π) →* ↥S' :=
      (π.comp (S'.comap π).subtype).codRestrict S' (fun s => s.2)
    have hρ : Function.Surjective ρ := by
      intro s'
      obtain ⟨s, hs⟩ := hπsurj (s' : X ⧸ D)
      exact ⟨⟨s, show π s ∈ S' by rw [hs]; exact s'.2⟩, Subtype.ext hs⟩
    have hall := (P2.mapSurjective hρ).3 (hS'2.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at hall
    refine le_antisymm (fun s' hs' => ?_) hTS'
    obtain ⟨s, hsP, hs⟩ := hall ▸ (Subgroup.mem_top (⟨s', hs'⟩ : ↥S'))
    have hsT : (s : X) ∈ T := by
      rw [← hP2]
      exact ⟨s, hsP, rfl⟩
    exact ⟨s, hsT, congrArg Subtype.val hs⟩

theorem mem_map_conj_iff {S : Subgroup X} {w x : X} :
    x ∈ S.map (MulAut.conj w).toMonoidHom ↔ w⁻¹ * x * w ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨w⁻¹ * x * w, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem fusionIsSylowIn_map_conj {q : ℕ} {S K : Subgroup X} (hS : fusionIsSylowIn q S K) {w : X}
    (hw : w ∈ normalizer (K : Set X)) :
    fusionIsSylowIn q (S.map (MulAut.conj w).toMonoidHom) K := by
  obtain ⟨hSK, hSq, hmax⟩ := hS
  have hconj : ∀ y ∈ K, w * y * w⁻¹ ∈ K ∧ w⁻¹ * y * w ∈ K := by
    intro y hy
    refine ⟨(mem_normalizer_iff.mp hw y).mp hy, ?_⟩
    have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ hw) y).mp hy
    simpa using this
  refine ⟨?_, hSq.map _, fun P hPK hPq hSP => ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact (hconj s (hSK hs)).1
  · have hP' : P.map (MulAut.conj w⁻¹).toMonoidHom = S := by
      refine hmax _ ?_ (hPq.map _) ?_
      · rintro _ ⟨y, hy, rfl⟩
        simpa [MulAut.conj_apply] using (hconj y (hPK hy)).2
      · intro s hs
        refine ⟨w * s * w⁻¹, hSP ⟨s, hs, rfl⟩, ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
    ext y
    constructor
    · intro hy
      have h1 : (MulAut.conj w⁻¹).toMonoidHom y ∈ P.map (MulAut.conj w⁻¹).toMonoidHom :=
        ⟨y, hy, rfl⟩
      rw [hP'] at h1
      exact mem_map_conj_iff.mpr (by simpa [MulAut.conj_apply] using h1)
    · rintro ⟨s, hs, rfl⟩
      rw [← hP'] at hs
      obtain ⟨u, hu, rfl⟩ := hs
      have e : (MulAut.conj w).toMonoidHom ((MulAut.conj w⁻¹).toMonoidHom u) = u := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [e]
      exact hu

theorem normalizer_map_le_map_normalizer (hp : p.Prime) (hp2 : p ≠ 2) {D T : Subgroup X}
    [D.Normal] (hD : ¬ p ∣ Nat.card D) (hT2 : IsPGroup 2 T)
    (hsyl : fusionIsSylowIn 2 T ((T.map (QuotientGroup.mk' D)).comap (QuotientGroup.mk' D))) :
    normalizer ((T.map (QuotientGroup.mk' D) : Subgroup (X ⧸ D)) : Set (X ⧸ D)) ≤
      (normalizer (T : Set X)).map (QuotientGroup.mk' D) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK3 : ¬ p ∣ Nat.card ((T.map (QuotientGroup.mk' D)).comap (QuotientGroup.mk' D)) :=
    not_dvd_card_comap hp hp2 hD (hT2.map _)
  intro wb hwb
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective D wb
  have hwK := mem_normalizer_comap hwb
  have hbotp : IsPGroup p (⊥ : Subgroup X) := IsPGroup.of_card (n := 0) (by simp)
  obtain ⟨c, hcK, hc⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows (r := p) (q := 2)
    hp Nat.prime_two (A := ⊥) (M := (T.map (QuotientGroup.mk' D)).comap (QuotientGroup.mk' D))
    (S := T) (S' := T.map (MulAut.conj w).toMonoidHom)
    hbotp hK3 bot_le hsyl (fusionIsSylowIn_map_conj hsyl hwK) bot_le bot_le
  have hcK' := (Subgroup.mem_inf.mp hcK).1
  have hn : c⁻¹ * w ∈ normalizer (T : Set X) := by
    rw [mem_normalizer_iff]
    intro x
    have e1 : w⁻¹ * (w * x * w⁻¹) * w = x := by group
    have e2 : (c⁻¹ * w) * x * (c⁻¹ * w)⁻¹ = c⁻¹ * (w * x * w⁻¹) * c := by group
    rw [e2]
    constructor
    · intro hx
      have h1 : w * x * w⁻¹ ∈ T.map (MulAut.conj w).toMonoidHom :=
        mem_map_conj_iff.mpr (by rw [e1]; exact hx)
      rw [hc, mem_map_conj_iff] at h1
      exact h1
    · intro hx
      have h1 : w * x * w⁻¹ ∈ T.map (MulAut.conj c).toMonoidHom := mem_map_conj_iff.mpr hx
      rw [← hc, mem_map_conj_iff, e1] at h1
      exact h1
  obtain ⟨t, ht, htc⟩ : ∃ t ∈ T, QuotientGroup.mk' D t = QuotientGroup.mk' D c := hcK'
  refine ⟨t * (c⁻¹ * w), ?_, ?_⟩
  · exact (normalizer (T : Set X)).mul_mem (Subgroup.le_normalizer ht) hn
  · rw [map_mul, htc, map_mul, map_inv, mul_inv_cancel_left]

theorem le_pRank_normalizer (hp : p.Prime) (hp2 : p ≠ 2) {D B T : Subgroup X} [D.Normal]
    (hD : ¬ p ∣ Nat.card D) (hB : IsPGroup p B) (hT : IsMaxTwoInvariantIn B ⊤ T)
    {W : Subgroup (X ⧸ D)} (hWe : IsElemAbelian p W) {k : ℕ} (hWk : Nat.card W = p ^ k)
    (hW : W ≤ normalizer ((T.map (QuotientGroup.mk' D) : Subgroup (X ⧸ D)) : Set (X ⧸ D))) :
    k ≤ Open.pRank p (normalizer (T : Set X)) := by
  have hT2 : IsPGroup 2 T := hT.1.2.1
  have hBT : B ≤ normalizer (T : Set X) := hT.1.2.2
  set π := QuotientGroup.mk' D with hπ
  have hK3 : ¬ p ∣ Nat.card ((T.map π).comap π) := not_dvd_card_comap hp hp2 hD (hT2.map π)
  have hTK : T ≤ (T.map π).comap π := fun t ht => ⟨t, ht, rfl⟩
  have hBK : B ≤ normalizer (((T.map π).comap π : Subgroup X) : Set X) :=
    le_normalizer_comap ((Subgroup.map_mono hBT).trans (Subgroup.le_normalizer_map π))
  have hsyl := fusionIsSylowIn_of_isMax hp hB hT hTK hK3 hBK
  have hW' : W ≤ (normalizer (T : Set X)).map π :=
    hW.trans (normalizer_map_le_map_normalizer hp hp2 hD hT2 hsyl)
  have h1 : k ≤ Open.pRank p ((normalizer (T : Set X)).map π) :=
    CFSG.SectionRank.le_pRank hp.one_lt hW' hWe hWk
  have hker : ¬ p ∣ Nat.card π.ker := by
    rw [QuotientGroup.ker_mk']
    exact hD
  exact h1.trans (CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hp π hker _)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62
