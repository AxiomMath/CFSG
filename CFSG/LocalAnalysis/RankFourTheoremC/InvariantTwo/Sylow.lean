module

public import CFSG.LocalAnalysis.RankFourTheoremC.FischerPending.Rank
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ObstructionSetting.isSylowOf_normalizer_inf (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hDab : IsMulCommutative D)
    (hCM : centralizer (D : Set G) ≤ M) {z : G} (hzD : z ∈ D) (hz1 : z ≠ 1)
    (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M) :
    CFSG.ABGLocalTools.IsSylowOf p ((P : Subgroup G) ⊓ normalizer (D : Set G))
      (normalizer (D : Set G)) := by
  classical
  have hprime := sigmaA_prime p hp
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hM, hDP, hD2, hDM⟩ := hext.obstruction
  obtain ⟨hDe, hDc⟩ := hext.isElemAbelian_of_isMulCommutative hprime hDab
  have hPp : IsPGroup p (P : Subgroup G) := P.isPGroup'
  have hCp : ∀ y ∈ centralizer (D : Set G), y ^ p = 1 → y ∈ D := fun y hyC hyp =>
    hS.mem_of_mem_centralizer_of_isMulCommutative hD1 hp hext hDab hCM hyC hyp
  obtain ⟨Q₀, hQ₀⟩ := ((hPp.to_inf_left (K := normalizer (D : Set G))).comap_subtype
    (K := normalizer (D : Set G))).exists_le_sylow
  set S₀ : Subgroup G := (Q₀ : Subgroup (normalizer (D : Set G))).map
    (normalizer (D : Set G)).subtype with hS₀
  have hS₀syl : CFSG.ABGLocalTools.IsSylowOf p S₀ (normalizer (D : Set G)) := ⟨Q₀, rfl⟩
  have hPS₀ : (P : Subgroup G) ⊓ normalizer (D : Set G) ≤ S₀ := fun e he =>
    ⟨⟨e, he.2⟩, hQ₀ he, rfl⟩
  obtain ⟨P₂, hS₀P₂⟩ := hS₀syl.isPGroup.exists_le_sylow
  obtain ⟨M₂, hM₂, hP₂M₂⟩ := hS.exists_isCoreMaxLocal hp P₂
  have hDS₀ : D ≤ S₀ := fun d hd => hPS₀ ⟨hDP hd, le_normalizer hd⟩
  have hDP₂ : D ≤ (P₂ : Subgroup G) := hDS₀.trans hS₀P₂
  have hiso : IsIsolatedPlane p (P₂ : Subgroup G) D := by
    refine ⟨hDP₂, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p D).2 hDe, hDc,
      fun E' _ hE' hDE' => ?_⟩
    have hE'' : IsElemAbelian p E' :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E').1 hE'
    have hE'D : E' ≤ D := fun e he =>
      hCp e (mem_centralizer_iff.mpr fun d hd => congrArg Subtype.val
        (hE''.1.is_comm.comm ⟨d, hDE' hd⟩ ⟨e, he⟩)) (hE''.2 e he)
    rw [← hDc]
    exact card_le_of_le hE'D
  have hDM₂ : ¬ normalizer (D : Set G) ≤ M₂ := by
    intro hN
    obtain ⟨A, hAP₂, hA, hAc⟩ := hS.exists_elemAbelian_card_eq hp P₂
    obtain ⟨-, z', hz'D, hz'1, hz'c, -, -⟩ := isolatedPlane_structure hprime P₂.isPGroup' hiso
      hAP₂ ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2 hA) hAc
    obtain ⟨g, hgN, hgz⟩ := hS.exists_mem_normalizer_zpowers_eq hD1 hp hext hPD hDab hCM hzD hz1
      hzc hN₀M hz'D hz'1
    have hNz' : normalizer ((zpowers z' : Subgroup G) : Set G) =
        (normalizer ((zpowers z : Subgroup G) : Set G)).map (MulAut.conj g).toMonoidHom := by
      rw [hgz, Subgroup.map_equiv_normalizer_eq]
    have hP₂K : (P₂ : Subgroup G) ≤ normalizer ((zpowers z' : Subgroup G) : Set G) :=
      le_normalizer_zpowers_of_le_centralizer hz'c
    have hPgK : ((g • P : Sylow p G) : Subgroup G) ≤
        normalizer ((zpowers z' : Subgroup G) : Set G) := by
      rw [sylow_coe_smul_eq_map, hNz']
      exact map_mono (le_normalizer_zpowers_of_le_centralizer hzc)
    have hP₂syl : CFSG.ABGLocalTools.IsSylowOf p (P₂ : Subgroup G)
        (normalizer ((zpowers z' : Subgroup G) : Set G)) :=
      ⟨P₂.subtype hP₂K, by rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hP₂K]⟩
    have hPgsyl : CFSG.ABGLocalTools.IsSylowOf p ((g • P : Sylow p G) : Subgroup G)
        (normalizer ((zpowers z' : Subgroup G) : Set G)) :=
      ⟨(g • P).subtype hPgK, by rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hPgK]⟩
    obtain ⟨c, hcK, hconj⟩ := hPgsyl.exists_mem_conj hP₂syl
    have hMg : IsCoreMaxLocal p (g • P) (M.map (MulAut.conj g).toMonoidHom) :=
      hM.smul hprime.one_lt g
    have hcMg : c ∈ M.map (MulAut.conj g).toMonoidHom := by
      have : c ∈ (normalizer ((zpowers z : Subgroup G) : Set G)).map
          (MulAut.conj g).toMonoidHom := hNz' ▸ hcK
      exact map_mono hN₀M this
    have hMgc : (M.map (MulAut.conj g).toMonoidHom).map (MulAut.conj c).toMonoidHom =
        M.map (MulAut.conj g).toMonoidHom :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer hcMg)
    have hPc : c • (g • P) = P₂ := by
      apply Sylow.ext
      rw [sylow_coe_smul_eq_map]
      ext x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine (hconj _).mpr ?_
        have e : c⁻¹ * ((MulAut.conj c).toMonoidHom y) * c = y := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [e]
        exact hy
      · intro hx
        refine ⟨c⁻¹ * x * c, (hconj x).mp hx, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    have hMc : IsCoreMaxLocal p P₂ (M.map (MulAut.conj g).toMonoidHom) := by
      have := hMg.smul hprime.one_lt c
      rwa [hPc, hMgc] at this
    have hP₂Mg := hS.sylow_le hp hMc
    have hle : M.map (MulAut.conj g).toMonoidHom ≤ M₂ :=
      le_of_three_le_pRank_inf hD1 hp hM₂ hMc.1.1
        ((hS.three_le_pRank p hp P₂).trans
          (pRank_mono p hprime.one_lt (le_inf hP₂Mg hP₂M₂)))
    have heq : M₂ = M.map (MulAut.conj g).toMonoidHom := hMc.1.2 M₂ hM₂.1.1 hle
    apply hDM
    intro y hy
    have hgy : g * y * g⁻¹ ∈ normalizer (D : Set G) :=
      mul_mem (mul_mem hgN hy) (inv_mem hgN)
    have hgyM : g * y * g⁻¹ ∈ M.map (MulAut.conj g).toMonoidHom := heq ▸ hN hgy
    obtain ⟨m, hmM, hm⟩ := hgyM
    have : m = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hm
      exact mul_left_cancel (mul_right_cancel hm)
    exact this ▸ hmM
  have hcard := hext.maximal P₂ M₂ D ⟨hM₂, hDP₂, hD2, hDM₂⟩
  have hS₀eq : S₀ = (P : Subgroup G) ⊓ normalizer (D : Set G) := by
    refine (Subgroup.eq_of_le_of_card_ge hPS₀ ?_).symm
    calc Nat.card S₀ ≤ Nat.card ↥((P₂ : Subgroup G) ⊓ normalizer (D : Set G)) :=
          card_le_of_le (le_inf hS₀P₂ hS₀syl.le)
      _ ≤ Nat.card ↥((P : Subgroup G) ⊓ normalizer (D : Set G)) := hcard
  rw [← hS₀eq]
  exact hS₀syl

theorem ObstructionSetting.isSylowOf_centralizer_iff (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hDab : IsMulCommutative D)
    (hCM : centralizer (D : Set G) ≤ M) {z : G} (hzD : z ∈ D) (hz1 : z ≠ 1)
    (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M) :
    CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set G)) ↔
      (P : Subgroup G) ⊓ centralizer (D : Set G) ≤ D := by
  have hprime := sigmaA_prime p hp
  have : Fact p.Prime := ⟨hprime⟩
  have hDP : D ≤ (P : Subgroup G) := hext.obstruction.2.1
  have hDC : D ≤ centralizer (D : Set G) := le_centralizer_iff_isMulCommutative.mpr hDab
  have hCN : centralizer (D : Set G) ≤ normalizer (D : Set G) :=
    Subgroup.centralizer_le_normalizer (D : Set G)
  constructor
  · intro h
    have hle := h.eq_of_le (le_inf hDP hDC) inf_le_right
      (P.isPGroup'.to_inf_left (K := centralizer (D : Set G)))
    exact hle.le
  · intro hCP
    have hN := hS.isSylowOf_normalizer_inf hD1 hp hext hPD hDab hCM hzD hz1 hzc hN₀M
    have hC := hN.inf_of_le_normalizer hCN
      (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup D)
    have hDeq : (P : Subgroup G) ⊓ normalizer (D : Set G) ⊓ centralizer (D : Set G) = D := by
      refine le_antisymm ?_ (le_inf (le_inf hDP le_normalizer) hDC)
      rw [inf_assoc, inf_eq_right.mpr hCN]
      exact hCP
    rwa [hDeq] at hC

end CFSG.LocalAnalysis.RankFourTheoremC
