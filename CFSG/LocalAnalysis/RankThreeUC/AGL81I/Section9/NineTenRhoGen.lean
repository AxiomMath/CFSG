module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenQuotGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenRho

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {Q H E : Subgroup G} {k : ℕ}

namespace NineSettingGen

theorem isPSLType_oPPrimeHull_quotKer_of_centralizer_le (h : NineSettingGen G M 3 Q H E k)
    (hp : 3 ∉ sigmaM G M) (hU : NineNineOne M 3)
    (hR : CFSG.Open.pRank 3 (CFSG.pCore 3 (StarGroup 3 H)) ≤ 2)
    (hC : ((Subgroup.centralizer (CFSG.pCore 3 (StarGroup 3 H) : Set (StarGroup 3 H))).comap
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3))).map H.subtype ≤ M) :
    IsPSLType 2 (ZMod 3) ↥(oPPrimeHull 3 (⊤ : Subgroup (QuotKer M H))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (CFSG.pCore 3 (StarGroup 3 H)).Normal := CFSG.pCore_normal
  obtain ⟨ρ, hρ⟩ := exists_hom_GL23_of_pRank_le_two (CFSG.pCore 3 (StarGroup 3 H))
    CFSG.pCore_isPGroup hR
  let ν : ↥H →* StarGroup 3 H := QuotientGroup.mk' (primeComplementCore (G := ↥H) 3)
  let ρ' : ↥H →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) := ρ.comp ν
  let N : Subgroup ↥H := Subgroup.normalCore ((M ⊓ H).subgroupOf H)
  let π : ↥H →* QuotKer M H := QuotientGroup.mk' N
  let Cf : Subgroup ↥H :=
    (Subgroup.centralizer (CFSG.pCore 3 (StarGroup 3 H) : Set (StarGroup 3 H))).comap ν
  have hCf_normal : Cf.Normal :=
    Subgroup.Normal.comap
      (Subgroup.normal_centralizer (H := CFSG.pCore 3 (StarGroup 3 H))) ν
  haveI : Cf.Normal := hCf_normal
  have hCfK : Cf ≤ (M ⊓ H).subgroupOf H := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact ⟨hC (Subgroup.mem_map_of_mem H.subtype hx), x.2⟩
  have hCfN : Cf ≤ N := Subgroup.normal_le_normalCore.mpr hCfK
  have hclaim : IsPGroup 3 ↥(ρ'.ker.map π) := by
    intro g
    obtain ⟨x, hx, hx_eq⟩ := Subgroup.mem_map.1 g.2
    have hg : g = ⟨π x, Subgroup.mem_map_of_mem π hx⟩ := Subtype.ext hx_eq.symm
    rw [hg]
    have hxρ : ν x ∈ ρ.ker := by
      simpa only [ρ', MonoidHom.mem_ker, MonoidHom.comp_apply] using hx
    obtain ⟨a, ha⟩ := hρ
      ⟨MulAut.conjNormal (H := CFSG.pCore 3 (StarGroup 3 H)) (ν x), ⟨ν x, hxρ, rfl⟩⟩
    have ha' : (MulAut.conjNormal (H := CFSG.pCore 3 (StarGroup 3 H)) (ν x)) ^ 3 ^ a = 1 := by
      simpa using congrArg Subtype.val ha
    have hconj1 :
        MulAut.conjNormal (H := CFSG.pCore 3 (StarGroup 3 H)) (ν (x ^ 3 ^ a)) = 1 := by
      rw [map_pow ν x (3 ^ a),
        map_pow (MulAut.conjNormal (H := CFSG.pCore 3 (StarGroup 3 H))) (ν x) (3 ^ a)]
      exact ha'
    have hcent : ν (x ^ 3 ^ a) ∈
        Subgroup.centralizer (CFSG.pCore 3 (StarGroup 3 H) : Set (StarGroup 3 H)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have h1 := congrArg
        (fun σ : MulAut ↥(CFSG.pCore 3 (StarGroup 3 H)) => (σ ⟨r, hr⟩ : StarGroup 3 H)) hconj1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc r * ν (x ^ 3 ^ a)
          = (ν (x ^ 3 ^ a) * r * (ν (x ^ 3 ^ a))⁻¹) * ν (x ^ 3 ^ a) := by rw [h1]
        _ = ν (x ^ 3 ^ a) * r := by group
    have hxCf : x ^ 3 ^ a ∈ Cf := Subgroup.mem_comap.mpr hcent
    have hxN : x ^ 3 ^ a ∈ N := hCfN hxCf
    have hxπ : π (x ^ 3 ^ a) = 1 := by
      have hmem : x ^ 3 ^ a ∈ π.ker := by
        rw [show π.ker = N from QuotientGroup.ker_mk' _]
        exact hxN
      exact MonoidHom.mem_ker.mp hmem
    exact ⟨a, Subtype.ext (by simpa using (map_pow π x (3 ^ a)).symm.trans hxπ)⟩
  exact h.isPSLType_oPPrimeHull_quotKer_of_hom_GL23 hp hU ρ' π
    (QuotientGroup.mk'_surjective _) hclaim

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
