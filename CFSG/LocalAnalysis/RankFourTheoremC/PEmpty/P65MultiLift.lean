module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62Lift
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Extremal
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65M

open CFSG.Open Subgroup

variable {X : Type} [Group X] [Finite X] {p f : ℕ}

theorem isMaxFInvariantIn_top {G : Type} [Group G] {M : Subgroup G} {B T : Subgroup G}
    (hB : B ≤ M) (hT : IsMaxFInvariantIn f B M T) :
    IsMaxFInvariantIn f (B.subgroupOf M) ⊤ (T.subgroupOf M) := by
  obtain ⟨⟨hTM, hTf, hBT⟩, hmax⟩ := hT
  refine ⟨⟨le_top, hTf.comap_subtype, ?_⟩, fun S' hS' hTS' => ?_⟩
  · rw [← Subgroup.subgroupOf_normalizer_eq hTM]
    exact Subgroup.comap_mono hBT
  · obtain ⟨-, hS'f, hBS'⟩ := hS'
    have hS : IsFInvariantIn f B M (S'.map M.subtype) := by
      refine ⟨Subgroup.map_subtype_le _, hS'f.map M.subtype, fun b hb => ?_⟩
      have hb' : (⟨b, hB hb⟩ : M) ∈ normalizer (S' : Set M) :=
        hBS' (show (⟨b, hB hb⟩ : M) ∈ B.subgroupOf M from hb)
      rw [mem_normalizer_iff] at hb' ⊢
      intro y
      constructor
      · rintro ⟨y', hy', rfl⟩
        exact ⟨_, (hb' y').mp hy', rfl⟩
      · intro hy
        obtain ⟨y', hy'S, hy'eq⟩ := hy
        have hbM : b ∈ M := hB hb
        have hy'G : (y' : G) = b * y * b⁻¹ := hy'eq
        have hyM : y ∈ M := by
          have : y = b⁻¹ * (y' : G) * b := by rw [hy'G]; group
          rw [this]
          exact M.mul_mem (M.mul_mem (M.inv_mem hbM) y'.2) hbM
        refine ⟨⟨y, hyM⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, hb' ⟨y, hyM⟩]
        have : (⟨b, hbM⟩ : M) * ⟨y, hyM⟩ * (⟨b, hbM⟩ : M)⁻¹ = y' :=
          Subtype.ext (by simpa using hy'G.symm)
        rw [this]
        exact hy'S
    have hTS : T ≤ S'.map M.subtype := by
      intro t ht
      exact ⟨⟨t, hTM ht⟩, hTS' (show (⟨t, hTM ht⟩ : M) ∈ T.subgroupOf M from ht), rfl⟩
    have := hmax _ hS hTS
    apply Subgroup.map_injective M.subtype_injective
    rw [this, Subgroup.map_subgroupOf_eq_of_le hTM]

theorem not_dvd_card_comap (hp : p.Prime) (hf : f.Prime) (hfp : f ≠ p) {D : Subgroup X}
    [D.Normal] (hD : ¬ p ∣ Nat.card D) {S : Subgroup (X ⧸ D)} (hS : IsPGroup f S) :
    ¬ p ∣ Nat.card (S.comap (QuotientGroup.mk' D)) := by
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hgS : QuotientGroup.mk' D (g : X) ∈ S := g.2
  obtain ⟨k, hk⟩ := hS ⟨_, hgS⟩
  have h2 : (QuotientGroup.mk' D (g : X)) ^ f ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hgp : (g : X) ^ p = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    simpa using congrArg Subtype.val this
  have hp' : (QuotientGroup.mk' D (g : X)) ^ p = 1 := by rw [← map_pow, hgp, map_one]
  have hcop : Nat.Coprime p (f ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes hp hf).mpr hfp.symm)
  have h1 : QuotientGroup.mk' D (g : X) = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hp', h2⟩
  have hgD : (g : X) ∈ D := by
    have : (g : X) ∈ (QuotientGroup.mk' D).ker := h1
    rwa [QuotientGroup.ker_mk'] at this
  apply hD
  rw [← hg, ← Subgroup.orderOf_coe g, ← Subgroup.orderOf_mk (g : X) hgD]
  exact orderOf_dvd_natCard _

theorem fusionIsSylowIn_of_isMaxF (hp : p.Prime) (hf : f.Prime) {B T K : Subgroup X}
    (hB : IsPGroup p B) (hT : IsMaxFInvariantIn f B ⊤ T) (hTK : T ≤ K)
    (hK : ¬ p ∣ Nat.card K) (hBK : B ≤ normalizer (K : Set X)) : fusionIsSylowIn f T K := by
  obtain ⟨⟨-, hTf, hBT⟩, hmax⟩ := hT
  obtain ⟨R, hRsyl, hTR, hBR⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    hp hf hB hK hBK hTK hTf hBT
  have hRT : R = T := hmax R ⟨le_top, hRsyl.2.1, hBR⟩ hTR
  exact hRT ▸ hRsyl

theorem isMaxFInvariantIn_map (hp : p.Prime) (hf : f.Prime) (hfp : f ≠ p) {D B T : Subgroup X}
    [D.Normal] (hD : ¬ p ∣ Nat.card D) (hB : IsPGroup p B) (hT : IsMaxFInvariantIn f B ⊤ T) :
    IsMaxFInvariantIn f (B.map (QuotientGroup.mk' D)) ⊤ (T.map (QuotientGroup.mk' D)) := by
  haveI : Fact f.Prime := ⟨hf⟩
  set π := QuotientGroup.mk' D with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective D
  obtain ⟨⟨-, hTf, hBT⟩, hmax⟩ := hT
  have hT' : IsMaxFInvariantIn f B ⊤ T := ⟨⟨le_top, hTf, hBT⟩, hmax⟩
  refine ⟨⟨le_top, hTf.map π, ?_⟩, fun S' hS' hTS' => ?_⟩
  · exact (Subgroup.map_mono hBT).trans (Subgroup.le_normalizer_map π)
  · obtain ⟨-, hS'f, hBS'⟩ := hS'
    have hS3 : ¬ p ∣ Nat.card (S'.comap π) := not_dvd_card_comap hp hf hfp hD hS'f
    have hTS : T ≤ S'.comap π := fun t ht => hTS' ⟨t, ht, rfl⟩
    have hsyl := fusionIsSylowIn_of_isMaxF hp hf hB hT' hTS hS3
      (K62.le_normalizer_comap hBS')
    obtain ⟨P2, hP2⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hsyl
    let ρ : ↥(S'.comap π) →* ↥S' :=
      (π.comp (S'.comap π).subtype).codRestrict S' (fun s => s.2)
    have hρ : Function.Surjective ρ := by
      intro s'
      obtain ⟨s, hs⟩ := hπsurj (s' : X ⧸ D)
      exact ⟨⟨s, show π s ∈ S' by rw [hs]; exact s'.2⟩, Subtype.ext hs⟩
    have hall := (P2.mapSurjective hρ).3 (hS'f.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at hall
    refine le_antisymm (fun s' hs' => ?_) hTS'
    obtain ⟨s, hsP, hs⟩ := hall ▸ (Subgroup.mem_top (⟨s', hs'⟩ : ↥S'))
    have hsT : (s : X) ∈ T := by
      rw [← hP2]
      exact ⟨s, hsP, rfl⟩
    exact ⟨s, hsT, congrArg Subtype.val hs⟩

theorem normalizer_map_le_map_normalizer (hp : p.Prime) (hf : f.Prime) (hfp : f ≠ p)
    {D T : Subgroup X} [D.Normal] (hD : ¬ p ∣ Nat.card D) (hTf : IsPGroup f T)
    (hsyl : fusionIsSylowIn f T ((T.map (QuotientGroup.mk' D)).comap (QuotientGroup.mk' D))) :
    normalizer ((T.map (QuotientGroup.mk' D) : Subgroup (X ⧸ D)) : Set (X ⧸ D)) ≤
      (normalizer (T : Set X)).map (QuotientGroup.mk' D) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact f.Prime := ⟨hf⟩
  have hK3 : ¬ p ∣ Nat.card ((T.map (QuotientGroup.mk' D)).comap (QuotientGroup.mk' D)) :=
    not_dvd_card_comap hp hf hfp hD (hTf.map _)
  intro wb hwb
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective D wb
  have hwK := K62.mem_normalizer_comap hwb
  have hbotp : IsPGroup p (⊥ : Subgroup X) := IsPGroup.of_card (n := 0) (by simp)
  obtain ⟨c, hcK, hc⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows (r := p) (q := f)
    hp hf (A := ⊥) (M := (T.map (QuotientGroup.mk' D)).comap (QuotientGroup.mk' D))
    (S := T) (S' := T.map (MulAut.conj w).toMonoidHom)
    hbotp hK3 bot_le hsyl (K62.fusionIsSylowIn_map_conj hsyl hwK) bot_le bot_le
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
        K62.mem_map_conj_iff.mpr (by rw [e1]; exact hx)
      rw [hc, K62.mem_map_conj_iff] at h1
      exact h1
    · intro hx
      have h1 : w * x * w⁻¹ ∈ T.map (MulAut.conj c).toMonoidHom := K62.mem_map_conj_iff.mpr hx
      rw [← hc, K62.mem_map_conj_iff, e1] at h1
      exact h1
  obtain ⟨t, ht, htc⟩ : ∃ t ∈ T, QuotientGroup.mk' D t = QuotientGroup.mk' D c := hcK'
  refine ⟨t * (c⁻¹ * w), ?_, ?_⟩
  · exact (normalizer (T : Set X)).mul_mem (Subgroup.le_normalizer ht) hn
  · rw [map_mul, htc, map_mul, map_inv, mul_inv_cancel_left]

theorem le_pRank_normalizer (hp : p.Prime) (hf : f.Prime) (hfp : f ≠ p) {D B T : Subgroup X}
    [D.Normal] (hD : ¬ p ∣ Nat.card D) (hB : IsPGroup p B) (hT : IsMaxFInvariantIn f B ⊤ T)
    {W : Subgroup (X ⧸ D)} (hWe : IsElemAbelian p W) {k : ℕ} (hWk : Nat.card W = p ^ k)
    (hW : W ≤ normalizer ((T.map (QuotientGroup.mk' D) : Subgroup (X ⧸ D)) : Set (X ⧸ D))) :
    k ≤ Open.pRank p (normalizer (T : Set X)) := by
  have hTf : IsPGroup f T := hT.1.2.1
  have hBT : B ≤ normalizer (T : Set X) := hT.1.2.2
  set π := QuotientGroup.mk' D with hπ
  have hK3 : ¬ p ∣ Nat.card ((T.map π).comap π) :=
    not_dvd_card_comap hp hf hfp hD (hTf.map π)
  have hTK : T ≤ (T.map π).comap π := fun t ht => ⟨t, ht, rfl⟩
  have hBK : B ≤ normalizer (((T.map π).comap π : Subgroup X) : Set X) :=
    K62.le_normalizer_comap ((Subgroup.map_mono hBT).trans (Subgroup.le_normalizer_map π))
  have hsyl := fusionIsSylowIn_of_isMaxF hp hf hB hT hTK hK3 hBK
  have hW' : W ≤ (normalizer (T : Set X)).map π :=
    hW.trans (normalizer_map_le_map_normalizer hp hf hfp hD hTf hsyl)
  have h1 : k ≤ Open.pRank p ((normalizer (T : Set X)).map π) :=
    CFSG.SectionRank.le_pRank hp.one_lt hW' hWe hWk
  have hker : ¬ p ∣ Nat.card π.ker := by
    rw [QuotientGroup.ker_mk']
    exact hD
  exact h1.trans (CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hp π hker _)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65M
