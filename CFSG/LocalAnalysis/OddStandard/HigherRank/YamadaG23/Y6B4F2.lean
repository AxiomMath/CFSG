module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4F1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4X2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private def y6bQ (c : Ctx5 G L) : Subgroup G where
  carrier := {x | x ∈ normalizer (c.s.fr.F : Set G) ∧
    ∀ e ∈ y6bE16 c, x * e * x⁻¹ * e⁻¹ ∈ c.s.fr.F}
  one_mem' := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    intro e _
    simp
  mul_mem' := by
    intro x y hx hy
    obtain ⟨hxN, hxQ⟩ := hx
    obtain ⟨hyN, hyQ⟩ := hy
    refine ⟨Subgroup.mul_mem _ hxN hyN, ?_⟩
    intro e he
    have hye : y * e * y⁻¹ * e⁻¹ ∈ c.s.fr.F := hyQ e he
    have hxye : x * (y * e * y⁻¹ * e⁻¹) * x⁻¹ ∈ c.s.fr.F :=
      (Subgroup.mem_normalizer_iff.mp hxN _).mp hye
    have hxe : x * e * x⁻¹ * e⁻¹ ∈ c.s.fr.F := hxQ e he
    have heq : (x * y) * e * (x * y)⁻¹ * e⁻¹ =
        (x * (y * e * y⁻¹ * e⁻¹) * x⁻¹) * (x * e * x⁻¹ * e⁻¹) := by group
    rw [heq]
    exact Subgroup.mul_mem _ hxye hxe
  inv_mem' := by
    intro x hx
    obtain ⟨hxN, hxQ⟩ := hx
    refine ⟨Subgroup.inv_mem _ hxN, ?_⟩
    intro e he
    have hxe : x * e * x⁻¹ * e⁻¹ ∈ c.s.fr.F := hxQ e he
    have hxa : x⁻¹ * (x * e * x⁻¹ * e⁻¹)⁻¹ * (x⁻¹)⁻¹ ∈ c.s.fr.F :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) _).mp (c.s.fr.F.inv_mem hxe)
    have heq : x⁻¹ * e * (x⁻¹)⁻¹ * e⁻¹ =
        x⁻¹ * (x * e * x⁻¹ * e⁻¹)⁻¹ * (x⁻¹)⁻¹ := by group
    rw [heq]
    exact hxa

theorem y6b_T3_comm_E16 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) :
    ∀ x ∈ y6bT3 c, ∀ e ∈ y6bE16 c, x * e * x⁻¹ * e⁻¹ ∈ c.s.fr.F := by
  have hT : c.s.T ≤ y6bQ c := by
    intro x hx
    refine ⟨y6b_T_le_normalizer_F c hH hRT hx, ?_⟩
    intro e he
    rw [y6b_mem_E16 c hH hRT] at he
    obtain ⟨f, hf, hdisj⟩ := he
    rcases hdisj with hdisj | hdisj
    · rw [hdisj]
      have hxf : x * f * x⁻¹ ∈ c.s.fr.F :=
        (Subgroup.mem_normalizer_iff.mp (y6b_T_le_normalizer_F c hH hRT hx) f).mp hf
      have heq : x * f * x⁻¹ * f⁻¹ = (x * f * x⁻¹) * f⁻¹ := by group
      rw [heq]
      exact Subgroup.mul_mem _ hxf (c.s.fr.F.inv_mem hf)
    · rw [hdisj]
      obtain ⟨f', hf', hxg⟩ := y6b_T_conj_g_mem c hH hRT x hx
      have hxf : x * f * x⁻¹ ∈ c.s.fr.F :=
        (Subgroup.mem_normalizer_iff.mp (y6b_T_le_normalizer_F c hH hRT hx) f).mp hf
      have hg2 : c.g * c.g = 1 := y6b_g_sq c hRT
      have hginv : c.g⁻¹ = c.g := inv_eq_of_mul_eq_one_right hg2
      have heq : x * (f * c.g) * x⁻¹ * (f * c.g)⁻¹ = (x * f * x⁻¹) * f' * f⁻¹ := by
        have h1 : x * (f * c.g) * x⁻¹ = (x * f * x⁻¹) * (f' * c.g) := by
          rw [show x * (f * c.g) * x⁻¹ = (x * f * x⁻¹) * (x * c.g * x⁻¹) by group, hxg]
        have h2 : (f * c.g)⁻¹ = c.g * f⁻¹ := by
          rw [show (f * c.g)⁻¹ = c.g⁻¹ * f⁻¹ by group, hginv]
        rw [h1, h2]
        have h3 : (x * f * x⁻¹) * (f' * c.g) * (c.g * f⁻¹) =
            (x * f * x⁻¹) * (f' * (c.g * c.g)) * f⁻¹ := by group
        rw [h3, hg2]
        group
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hxf hf') (c.s.fr.F.inv_mem hf)
  have hM3 : M3 c.s ≤ y6bQ c := by
    intro m hm
    haveI := y6e_M3_comm c hF
    have hmF : ∀ f ∈ c.s.fr.F, m * f = f * m := by
      intro f hf
      exact congrArg Subtype.val (mul_comm' (⟨m, hm⟩ : ↥(M3 c.s))
        (⟨f, Subgroup.mem_sup_right hf⟩ : ↥(M3 c.s)))
    refine ⟨Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
      (fun f hf => (hmF f hf).symm)), ?_⟩
    intro e he
    rw [y6b_mem_E16 c hH hRT] at he
    obtain ⟨f, hf, hdisj⟩ := he
    rcases hdisj with hdisj | hdisj
    · rw [hdisj]
      have h1 : m * f * m⁻¹ * f⁻¹ = 1 := by rw [hmF f hf]; group
      rw [h1]
      exact c.s.fr.F.one_mem
    · rw [hdisj]
      have hgm : m * c.g = c.g * m := by
        have h := hF.2.2.2.1 hRT m hm
        calc m * c.g = (c.g * m * c.g⁻¹) * c.g := by rw [h]
          _ = c.g * m := by group
      have h1 : m * (f * c.g) * m⁻¹ * (f * c.g)⁻¹ = 1 := by
        rw [show m * (f * c.g) * m⁻¹ = (m * f * m⁻¹) * (m * c.g * m⁻¹) by group,
          show m * f * m⁻¹ = f by rw [hmF f hf]; group,
          show m * c.g * m⁻¹ = c.g by rw [hgm]; group]
        group
      rw [h1]
      exact c.s.fr.F.one_mem
  intro x hx e he
  have hle : c.s.T ⊔ M3 c.s ≤ y6bQ c := sup_le hT hM3
  exact (hle hx).2 e he

theorem y6b_F_normal_P (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) (h1 : Y6bHasX1 c) {P : Subgroup G} (hP : Y6bPData c P) :
    ∀ x ∈ P, ∀ f ∈ c.s.fr.F, x * f * x⁻¹ ∈ c.s.fr.F := by
  obtain ⟨hTP, hPX, hPc, hT3c⟩ := hP
  have hnorm := y6b_normal_of_card hTP hPc
  have hX16 := y6b_X_le_normalizer_E16 c hH hF hRT h1
  intro x hx f hf
  obtain ⟨s, hs, hsg⟩ := y6b_S_conj_g_surj c hH hRT f hf
  have hsT3 : s ∈ y6bT3 c :=
    Subgroup.mem_sup_left ((c.s.S_le_R.trans c.s.R_le_T) hs)
  have hs' : x * s * x⁻¹ ∈ y6bT3 c := hnorm x hx s hsT3
  have hxE16 : x * c.g * x⁻¹ ∈ y6bE16 c :=
    (Subgroup.mem_normalizer_iff.mp (hX16 (hPX hx)) c.g).mp (y6b_g_mem_E16 c)
  have hcomm := y6b_T3_comm_E16 c hH hF hRT (x * s * x⁻¹) hs' (x * c.g * x⁻¹) hxE16
  have hf_eq : f = s * c.g * s⁻¹ * c.g⁻¹ := by rw [hsg]; group
  have heq : x * f * x⁻¹ =
      (x * s * x⁻¹) * (x * c.g * x⁻¹) * (x * s * x⁻¹)⁻¹ * (x * c.g * x⁻¹)⁻¹ := by
    rw [hf_eq]; group
  rw [heq]
  exact hcomm

theorem y6b_exists_a (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hRT : c.s.R ≠ c.s.T) (h1 : Y6bHasX1 c) {P : Subgroup G} (hP : Y6bPData c P) :
    ∃ a ∈ P, (∀ f ∈ c.s.fr.F, a * f = f * a) ∧ a ∉ y6bW c := by
  have hFnorm := y6b_F_normal_P c hH hF hRT h1 hP
  obtain ⟨hTP, hPX, hPc, hT3c⟩ := hP
  by_contra hcon
  push Not at hcon
  have hF_M3 : c.s.fr.F ≤ M3 c.s := fun _ hf => Subgroup.mem_sup_right hf
  have hM3_T3 : M3 c.s ≤ y6bT3 c := fun _ hm => Subgroup.mem_sup_right hm
  have hFP : c.s.fr.F ≤ P := (hF_M3.trans hM3_T3).trans hTP
  haveI : ((c.s.fr.F).subgroupOf P).Normal := by
    refine ⟨fun n hn g => ?_⟩
    change ((g : G) * (n : G) * (g : G)⁻¹) ∈ c.s.fr.F
    exact hFnorm g g.2 n hn
  let eFP := Subgroup.subgroupOfEquivOfLe hFP
  let ρ : ↥P →* MulAut ↥((c.s.fr.F).subgroupOf P) := MulAut.conjNormal
  have hV : Nat.card ↥((c.s.fr.F).subgroupOf P) = 8 := by
    rw [Nat.card_congr eFP.toEquiv, (y54_F_isE3 hH).2]
    norm_num
  have hcomm' : ∀ a b : ↥((c.s.fr.F).subgroupOf P), a * b = b * a := by
    intro a b
    apply eFP.injective
    rw [map_mul, map_mul]
    exact Subtype.ext (y54_F_comm hH (eFP a : G) (eFP a).2 (eFP b : G) (eFP b).2)
  have hsq' : ∀ v : ↥((c.s.fr.F).subgroupOf P), v * v = 1 := by
    intro v
    apply eFP.injective
    rw [map_mul, map_one]
    exact Subtype.ext (by simpa [pow_two] using y54_F_sq hH (eFP v : G) (eFP v).2)
  have hAutCard : Nat.card (MulAut ↥((c.s.fr.F).subgroupOf P)) = 168 :=
    CFSG.GF2Type.Aschbacher1976Full.HS.card_mulAut_eq_168 hV hcomm' hsq'
  have hkerW : ρ.ker.map P.subtype ≤ y6bW c := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    have hy1 : MulAut.conjNormal y = 1 := hy
    have hcent : ∀ f ∈ c.s.fr.F, (y : G) * f = f * (y : G) := by
      intro f hf
      have hfP : f ∈ P := hFP hf
      have h : (y : G) * f * (y : G)⁻¹ = f := by
        have h := congrArg (fun z : ↥((c.s.fr.F).subgroupOf P) => (z : G))
          (DFunLike.congr_fun hy1 (⟨⟨f, hfP⟩, hf⟩ : ↥((c.s.fr.F).subgroupOf P)))
        simpa using h
      calc (y : G) * f = ((y : G) * f * (y : G)⁻¹) * (y : G) := by group
        _ = f * (y : G) := by rw [h]
    exact hcon (y : G) y.2 hcent
  have hker_le : Nat.card ↥ρ.ker ≤ 256 := by
    have h := Subgroup.card_le_of_le (H := ρ.ker.map P.subtype) (K := y6bW c) hkerW
    rw [y6b_card_W c hH hF hRT] at h
    rwa [Subgroup.card_map_of_injective (K := ρ.ker) P.subtype_injective] at h
  have hRangeP : IsPGroup 2 ↥ρ.range := by
    refine IsPGroup.of_card_dvd_pow (n := 12) ?_
    have h := Subgroup.card_range_dvd ρ
    rw [hPc, hT3c] at h
    simpa using h
  have hRangeDvd : Nat.card ↥ρ.range ∣ 168 := by
    have h := Subgroup.card_subgroup_dvd_card ρ.range
    rwa [hAutCard] at h
  have hle8 : Nat.card ↥ρ.range ≤ 8 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRangeP
    rw [hk]
    have hdvd : 2 ^ k ∣ 8 := by
      have h168 : 2 ^ k ∣ 168 := by rwa [hk] at hRangeDvd
      have hcop : Nat.Coprime (2 ^ k) 21 := by
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · simp
        · rw [Nat.coprime_pow_left_iff hkpos]
          exact Nat.coprime_two_left.mpr ⟨10, by norm_num⟩
      have : 2 ^ k ∣ 8 * 21 := by simpa using h168
      exact hcop.dvd_of_dvd_mul_right this
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hcard : Nat.card ↥P = Nat.card ↥ρ.ker * Nat.card ↥ρ.range :=
    (Subgroup.card_ker_mul_card_range ρ).symm
  have hP4096 : Nat.card ↥P = 4096 := by rw [hPc, hT3c]; norm_num
  have hbound : Nat.card ↥P ≤ 2048 := by
    rw [hcard]
    calc Nat.card ↥ρ.ker * Nat.card ↥ρ.range
        ≤ 256 * 8 := Nat.mul_le_mul hker_le hle8
      _ = 2048 := by norm_num
  omega

end CFSG.OddStandard.HigherRank.YamadaG23
