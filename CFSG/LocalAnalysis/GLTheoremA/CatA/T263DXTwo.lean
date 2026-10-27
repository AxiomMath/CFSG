module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CharacterTheory.Semidihedral.Principal.FreeSixCharacterDefectFourSupport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.GLTheoremA.P55.I336.ClassTwo
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem normalizer_le_normalizer_centralizer' (J : Subgroup Ω) :
    Subgroup.normalizer (J : Set Ω) ≤
      Subgroup.normalizer ((Subgroup.centralizer (J : Set Ω) : Subgroup Ω) : Set Ω) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).1
    (Subgroup.normal_subgroupOf_centralizer_normalizer _)

theorem exists_two_of_act {X₀ J P B : Subgroup Ω} (hJX : J ≤ X₀) (hJ : IsQuasisimple ↥J)
    (hP2 : IsPGroup 2 ↥P) (hPX : P ≤ X₀) (hinn : P ≤ J ⊔ (X₀ ⊓ Subgroup.centralizer (J : Set Ω)))
    (hact : ⁅P, J⁆ ≠ ⊥) (hBX : B ≤ Subgroup.normalizer (X₀ : Set Ω))
    (hBJ : B ≤ Subgroup.normalizer (J : Set Ω)) (hBP : B ≤ Subgroup.normalizer (P : Set Ω)) :
    ∃ T'' : Subgroup Ω, T'' ≤ J ∧ IsPGroup 2 ↥T'' ∧ B ≤ Subgroup.normalizer (T'' : Set Ω) ∧
      ¬ T'' ≤ Subgroup.centralizer (J : Set Ω) := by
  set C : Subgroup Ω := Subgroup.centralizer (J : Set Ω)
  set M : Subgroup Ω := X₀ ⊓ C
  have hCN : Subgroup.normalizer (J : Set Ω) ≤ Subgroup.normalizer (C : Set Ω) :=
    normalizer_le_normalizer_centralizer' J
  have hNM : ∀ A : Subgroup Ω, A ≤ Subgroup.normalizer (X₀ : Set Ω) →
      A ≤ Subgroup.normalizer (J : Set Ω) → A ≤ Subgroup.normalizer (M : Set Ω) :=
    fun A h1 h2 => (le_inf h1 (h2.trans hCN)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hMJ : M ≤ Subgroup.normalizer (J : Set Ω) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hPJ : P ≤ Subgroup.normalizer (J : Set Ω) := hinn.trans (sup_le Subgroup.le_normalizer hMJ)
  have hPM : P ≤ Subgroup.normalizer (M : Set Ω) := hNM P (hPX.trans Subgroup.le_normalizer) hPJ
  have hBM : B ≤ Subgroup.normalizer (M : Set Ω) := hNM B hBX hBJ
  set K : Subgroup Ω := P ⊔ M
  have hKM : K ≤ Subgroup.normalizer (M : Set Ω) := sup_le hPM Subgroup.le_normalizer
  have hBK : B ≤ Subgroup.normalizer (K : Set Ω) :=
    (le_inf hBP hBM).trans (Subgroup.inf_normalizer_le_normalizer_sup P M)
  set Y : Subgroup Ω := K ⊓ J
  have hBY : B ≤ Subgroup.normalizer (Y : Set Ω) :=
    (le_inf hBK hBJ).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hYK : Y ≤ K := inf_le_left
  have hYJ : Y ≤ J := inf_le_right
  have hYN : Y ≤ Subgroup.normalizer (M : Set Ω) := hYK.trans hKM
  let f : ↥Y →* ↥(Subgroup.normalizer (M : Set Ω)) ⧸
      M.subgroupOf (Subgroup.normalizer (M : Set Ω)) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hYN)
  have hker : ∀ y : ↥Y, f y = 1 ↔ (y : Ω) ∈ M := by
    intro y
    simp [f, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcent : f.ker ≤ Subgroup.center ↥Y := by
    intro y hy
    have hyM : (y : Ω) ∈ M := (hker y).1 (MonoidHom.mem_ker.mp hy)
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hyM).2 (z : Ω)
      (hYJ z.2))
  have hpg : IsPGroup 2 ↥f.range := by
    rintro ⟨_, y, rfl⟩
    have hyK : (y : Ω) ∈ (↑(P ⊔ M) : Set Ω) := hYK y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right P M hPM] at hyK
    obtain ⟨p, hp, m, hm, hpm⟩ := Set.mem_mul.mp hyK
    obtain ⟨n, hn⟩ := hP2 ⟨p, hp⟩
    refine ⟨n, ?_⟩
    have hpn : p ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hmk : f y = QuotientGroup.mk' (M.subgroupOf (Subgroup.normalizer (M : Set Ω)))
        ⟨p, hPM hp⟩ := by
      have h1 : Subgroup.inclusion hYN y = ⟨p, hPM hp⟩ * ⟨m, Subgroup.le_normalizer hm⟩ :=
        Subtype.ext hpm.symm
      have h2 : QuotientGroup.mk' (M.subgroupOf (Subgroup.normalizer (M : Set Ω)))
          ⟨m, Subgroup.le_normalizer hm⟩ = 1 :=
        (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hm)
      have h3 : f y = QuotientGroup.mk' (M.subgroupOf (Subgroup.normalizer (M : Set Ω)))
          (Subgroup.inclusion hYN y) := rfl
      rw [h3, h1, map_mul, h2, mul_one]
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [hmk, ← map_pow]
    have : (⟨p, hPM hp⟩ : ↥(Subgroup.normalizer (M : Set Ω))) ^ 2 ^ n = 1 :=
      Subtype.ext (by simpa using hpn)
    rw [this, map_one]
  haveI : Group.IsNilpotent ↥f.range := hpg.isNilpotent
  haveI : Group.IsNilpotent ↥Y :=
    Subgroup.isNilpotent_of_ker_le_center f.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict]; exact hcent)
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥Y) := inferInstance
  have hQc : (Q : Subgroup ↥Y).Characteristic :=
    Sylow.characteristic_of_normal Q inferInstance
  refine ⟨(Q : Subgroup ↥Y).map Y.subtype, (Subgroup.map_subtype_le _).trans hYJ,
    Q.isPGroup'.map Y.subtype, ?_, ?_⟩
  · rw [Subgroup.le_normalizer_iff]
    intro b hb t ht
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp ht
    set ϕ := Y.normalizerMonoidHom ⟨b, hBY hb⟩ with hϕ
    have hϕq : ϕ q ∈ (Q : Subgroup ↥Y) := by
      have hq' : q ∈ Subgroup.comap ϕ.toMonoidHom (Q : Subgroup ↥Y) := by
        rw [hQc.fixed ϕ]; exact hq
      exact hq'
    exact Subgroup.mem_map.mpr ⟨ϕ q, hϕq, by simp [hϕ]⟩
  · intro hT
    apply hact
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    have hYC : ∀ y : ↥Y, (y : Ω) ∈ C := by
      intro y
      have hsurj : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
      have hRtop : (⊤ : Subgroup ↥f.range) = (Q.mapSurjective hsurj : Subgroup ↥f.range) :=
        (Q.mapSurjective hsurj).is_maximal' (hpg.to_subgroup ⊤) le_top
      have hy : f.rangeRestrict y ∈ (Q.mapSurjective hsurj : Subgroup ↥f.range) := by
        rw [← hRtop]; exact Subgroup.mem_top _
      rw [Sylow.coe_mapSurjective] at hy
      obtain ⟨q, hq, hqy⟩ := Subgroup.mem_map.mp hy
      have hfq : f q = f y := congrArg Subtype.val hqy
      have hmem : q⁻¹ * y ∈ f.ker := by simp [MonoidHom.mem_ker, map_mul, map_inv, hfq]
      have hqM : ((q⁻¹ * y : ↥Y) : Ω) ∈ M := (hker _).1 hmem
      have hqT : (q : Ω) ∈ (Q : Subgroup ↥Y).map Y.subtype := ⟨q, hq, rfl⟩
      have hyq : (y : Ω) = (q : Ω) * ((q⁻¹ * y : ↥Y) : Ω) := by simp
      rw [hyq]
      exact C.mul_mem (hT hqT) (Subgroup.mem_inf.mp hqM).2
    intro p' hp'
    have hp'J : p' ∈ (↑(J ⊔ M) : Set Ω) := hinn hp'
    rw [Subgroup.coe_mul_of_right_le_normalizer_left J M hMJ] at hp'J
    obtain ⟨j, hj, m, hm, hjm⟩ := Set.mem_mul.mp hp'J
    have hjK : j ∈ K := by
      rw [eq_mul_inv_of_mul_eq hjm]
      exact K.mul_mem (Subgroup.mem_sup_left hp') (K.inv_mem (Subgroup.mem_sup_right hm))
    rw [← hjm]
    exact C.mul_mem (hYC ⟨j, hjK, hj⟩) (Subgroup.mem_inf.mp hm).2

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
