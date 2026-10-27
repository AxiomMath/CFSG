module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Uni9
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Uni12
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Concl
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcEngine
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Num
public import CFSG.HardMathSupport.Solomon.Coordinator.L5Conj
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GL83PartI.I_22_6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {n p q : ℕ} {F : Type} [Field F] [Finite F] (h : UnitaryFieldData 2 n F)

private noncomputable def exists_sesqJData {N : ℕ}
    (A : Subgroup ↥(sesqSpecialUnitaryGroupLE (idForm h N)))
    (hp : p.Prime) (q : ℕ) (S : SesqBlockData h A hp)
    (h4perp : 4 ≤ Module.finrank F
      ↥(Submodule.orthogonalBilin (idForm h N) (blockSpace S.A'' S.D₁.1)))
    (T : SesqTorusData h A hp q S) : SesqJData h A hp q S T := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hc₁ : IsCompl (blockSpace S.A'' S.D₁.1)
      (Submodule.orthogonalBilin (idForm h N) (blockSpace S.A'' S.D₁.1)) :=
    isCompl_blockSpace_orthogonalBilin S.A'' hp S.hpF S.hA''e S.hB S.hBsym.isRefl S.hBn S.D₁
  have hJq : CFSG.Open.IsQuasisimple
      ↥(pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N)) (blockSpace S.A'' S.D₁.1)) :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp
      (isQuasisimple_pointwiseStab_of_isCompl S.hBsym S.hBn hc₁ (by omega)
        (fun h2 => by
          have hne := T.hne1_two h2
          have h1 : 1 ≤ n := h.one_le
          have hn2 : 2 ≤ n := by omega
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2)
        (fun h3' => by
          have hne := T.hne1_three h3'
          have h1 : 1 ≤ n := h.one_le
          have hn2 : 2 ≤ n := by omega
          calc 3 ≤ 4 := by norm_num
            _ = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2))
  have hJle : pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N)) (blockSpace S.A'' S.D₁.1) ≤
      Subgroup.centralizer ({T.x₁} : Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))) := by
    have hstep := pointwiseStab_le_centralizer_blockEnd_sesq (B := idForm h N) S.A'' hp S.hpF
      S.hA''e S.hB S.hBsym.isRefl S.hBn
      (fun g hg u v => ((mem_sesqSpecialUnitaryGroupLE (B := idForm h N)).mp hg).1 u v) S.t S.ht
      S.D₁ (S.hbSU S.D₁)
    rwa [show (⟨blockEnd S.A'' hp S.hpF S.hA''e S.t S.ht S.D₁, S.hbSU S.D₁⟩ :
        ↥(sesqSpecialUnitaryGroupLE (idForm h N))) = T.x₁ from T.hx₁.symm] at hstep
  have hJn :
      ((pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N)) (blockSpace S.A'' S.D₁.1)).subgroupOf
      (Subgroup.centralizer ({T.x₁} : Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))))).Normal := by
    have hstep := pointwiseStab_normal_in_centralizer (B := idForm h N) S.A'' hp S.hpF S.hA''e
      S.t S.ht S.D₁ (S.hbSU S.D₁)
    rwa [show (⟨blockEnd S.A'' hp S.hpF S.hA''e S.t S.ht S.D₁, S.hbSU S.D₁⟩ :
        ↥(sesqSpecialUnitaryGroupLE (idForm h N))) = T.x₁ from T.hx₁.symm] at hstep
  have hpJ : p ∣ Nat.card
      (pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N)) (blockSpace S.A'' S.D₁.1)) :=
    dvd_card_pointwiseStab_sesq (B := idForm h N) S.A'' hp S.hpF S.hA''e S.t S.ht S.hbSU
      (D := S.D₁) (E := S.D₂) S.hD12.symm S.hV2
  have hzpow :
      Subgroup.centralizer (Subgroup.zpowers T.x₁ :
        Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))) =
      Subgroup.centralizer ({T.x₁} : Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcompJ : GLAPComponent p
      (Subgroup.centralizer (Subgroup.zpowers T.x₁ :
        Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))))
      (pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N)) (blockSpace S.A'' S.D₁.1)) := by
    refine CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp hJq hpJ ?_ ?_
    · rw [hzpow]; exact hJle
    · rw [hzpow]; exact hJn
  have hAnormJ : A ≤ Subgroup.normalizer
      (pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N)) (blockSpace S.A'' S.D₁.1) :
        Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))) := by
    have hstep := le_normalizer_pointwiseStab (H := sesqSpecialUnitaryGroupLE (idForm h N))
      (U := blockSpace S.A'' S.D₁.1) S.hA''le
      (fun a ha u hu => blockSpace_invariant S.A'' hp S.hpF S.hA''e (a := ⟨a, ha⟩) hu)
    rwa [show (⊤ : Subgroup ↥S.A'').map (Subgroup.inclusion S.hA''le) = A from ?_] at hstep
    ext x
    rw [S.hmemA]
    constructor
    · rintro ⟨a, -, rfl⟩
      exact a.2
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  exact ⟨hJle, hzpow, hcompJ, hAnormJ⟩

private noncomputable def exists_sesqQData {N : ℕ}
    (A : Subgroup ↥(sesqSpecialUnitaryGroupLE (idForm h N)))
    (hp : p.Prime) (q : ℕ) (S : SesqBlockData h A hp)
    (T : SesqTorusData h A hp q S) (J : SesqJData h A hp q S T) :
    SesqQData h A hp q S T := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hQleJ : pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N))
      (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1) ≤
      pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N)) (blockSpace S.A'' S.D₁.1) :=
    pointwiseStab_mono (le_sup_left)
  have hQleC₁ : pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N))
      (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1) ≤
      Subgroup.centralizer ({T.x₁} : Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))) :=
    hQleJ.trans J.hJle
  have hQleC₂ : pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N))
      (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1) ≤
      Subgroup.centralizer ({T.x₂} : Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))) := by
    refine (pointwiseStab_mono (H := sesqSpecialUnitaryGroupLE (idForm h N)) le_sup_right).trans ?_
    have hstep := pointwiseStab_le_centralizer_blockEnd_sesq (B := idForm h N) S.A'' hp S.hpF
      S.hA''e S.hB S.hBsym.isRefl S.hBn
      (fun g hg u v => ((mem_sesqSpecialUnitaryGroupLE (B := idForm h N)).mp hg).1 u v) S.t S.ht
      S.D₂ (S.hbSU S.D₂)
    rwa [show (⟨blockEnd S.A'' hp S.hpF S.hA''e S.t S.ht S.D₂, S.hbSU S.D₂⟩ :
        ↥(sesqSpecialUnitaryGroupLE (idForm h N))) = T.x₂ from T.hx₂.symm] at hstep
  have hEgen : Subgroup.centralizer
      (Subgroup.closure ({T.x₁, T.x₂} : Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))) :
        Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))) =
      Subgroup.centralizer ({T.x₁, T.x₂} : Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))) := by
    rw [Subgroup.centralizer_closure]
  have hQleH : pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N))
      (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1) ≤
      pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N)) (blockSpace S.A'' S.D₁.1) ⊓
        Subgroup.centralizer (Subgroup.closure ({T.x₁, T.x₂} :
          Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))) :
          Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))) := by
    refine le_inf hQleJ ?_
    intro z hz
    rw [hEgen, Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with rfl | rfl
    · exact Subgroup.mem_centralizer_iff.mp (hQleC₁ hz) T.x₁ (by simp)
    · exact Subgroup.mem_centralizer_iff.mp (hQleC₂ hz) T.x₂ (by simp)
  have hQn : ((pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N))
      (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1)).subgroupOf
      (pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N)) (blockSpace S.A'' S.D₁.1) ⊓
        Subgroup.centralizer (Subgroup.closure ({T.x₁, T.x₂} :
          Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))) :
          Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))))).Normal := by
    refine pointwiseStab_normal (H := sesqSpecialUnitaryGroupLE (idForm h N)) ?_
    intro g hg x hx
    obtain ⟨hgJ, hgC⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨x₁', hx₁', x₂', hx₂', rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    refine add_mem ?_ ?_
    · have hfix : ((g : ↥(sesqSpecialUnitaryGroupLE (idForm h N))) :
          (Fin N → F) ≃ₗ[F] (Fin N → F)) x₁' = x₁' := mem_pointwiseStab.mp hgJ x₁' hx₁'
      rw [hfix]
      exact Submodule.mem_sup_left hx₁'
    · have hcomm : ((g : ↥(sesqSpecialUnitaryGroupLE (idForm h N))) :
          (Fin N → F) ≃ₗ[F] (Fin N → F)) * blockEnd S.A'' hp S.hpF S.hA''e S.t S.ht S.D₂ =
          blockEnd S.A'' hp S.hpF S.hA''e S.t S.ht S.D₂ *
            ((g : ↥(sesqSpecialUnitaryGroupLE (idForm h N))) :
              (Fin N → F) ≃ₗ[F] (Fin N → F)) := by
        have h1 : T.x₂ * g = g * T.x₂ :=
          Subgroup.mem_centralizer_iff.mp hgC T.x₂ (Subgroup.subset_closure (by simp))
        have h2 := congrArg Subtype.val h1.symm
        simpa [Subgroup.coe_mul, T.hx₂] using h2
      exact Submodule.mem_sup_right (centralizer_mapsTo_blockSpace S.A'' hp S.hpF S.hA''e S.t S.ht
        (D := S.D₂) hcomm hx₂')
  exact ⟨hQleH, hQn⟩

private theorem isQuasisimple_pointwiseStab_sup_blockSpace {N : ℕ}
    (A : Subgroup ↥(sesqSpecialUnitaryGroupLE (idForm h N)))
    (hp : p.Prime) (hp2 : p ≠ 2) (q : ℕ) (S : SesqBlockData h A hp)
    (T : SesqTorusData h A hp q S) :
    CFSG.Open.IsQuasisimple ↥(pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N))
      (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hV3le : blockSpace S.A'' S.D₃.1 ≤
      Submodule.orthogonalBilin (idForm h N)
        (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1) := by
    rw [Submodule.orthogonalBilin_sup]
    refine le_inf ?_ ?_
    · intro v hv
      rw [Submodule.mem_orthogonalBilin]
      intro u hu
      exact blockSpace_sesq_orthogonal S.A'' hp S.hpF S.hA''e (idForm h N) S.hB S.hD13 hu hv
    · intro v hv
      rw [Submodule.mem_orthogonalBilin]
      intro u hu
      exact blockSpace_sesq_orthogonal S.A'' hp S.hpF S.hA''e (idForm h N) S.hB S.hD23 hu hv
  have hfour_V3 : n = 1 → 4 ≤ Module.finrank F ↥(blockSpace S.A'' S.D₃.1) := fun hn1 =>
    le_trans (T.hfour_one hn1) (orderOf_neg_le_finrank_blockSpace (h := h) S.A'' hp S.hpF
      S.hA''e S.hB S.hBsym S.hBn hp2 S.t S.ht S.hV3)
  have hne1_Q₂ : Module.finrank F
      ↥(Submodule.orthogonalBilin (idForm h N)
        (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1)) =
        2 → n ≠ 1 := by
    intro h2 hn1
    have h4 := hfour_V3 hn1
    have hle := Submodule.finrank_mono hV3le
    omega
  have hne1_Q₃ : Module.finrank F
      ↥(Submodule.orthogonalBilin (idForm h N)
        (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1)) =
        3 → n ≠ 1 := by
    intro h3' hn1
    have h4 := hfour_V3 hn1
    have hle := Submodule.finrank_mono hV3le
    omega
  have hQq : CFSG.Open.IsQuasisimple ↥(pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N))
      (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1)) := by
    have hcQ : IsCompl (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1)
        (Submodule.orthogonalBilin (idForm h N)
          (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1)) := by
      have hlin := LinEngine.isCompl_sup_blockSpace_inf_fixedByEnd S.A'' hp S.hpF S.hA''e S.t S.ht
        S.hD12
      rw [OmEngine.fixedByEnd_blockEnd_eq_ker_projBlock S.A'' hp S.hpF S.hA''e S.t S.ht S.D₁,
        OmEngine.fixedByEnd_blockEnd_eq_ker_projBlock S.A'' hp S.hpF S.hA''e S.t S.ht S.D₂,
        ← orthogonalBilin_blockSpace_eq_ker S.A'' hp S.hpF S.hA''e S.hB S.hBsym.isRefl S.hBn S.D₁,
        ← orthogonalBilin_blockSpace_eq_ker S.A'' hp S.hpF S.hA''e S.hB S.hBsym.isRefl S.hBn S.D₂,
        ← Submodule.orthogonalBilin_sup] at hlin
      exact hlin
    refine CFSG.Quasithin.A3.isQuasisimple_iff_open.mp
      (isQuasisimple_pointwiseStab_of_isCompl S.hBsym S.hBn hcQ
        (le_trans S.hdim3 (Submodule.finrank_mono hV3le))
        (fun h2 => by
          have hne := hne1_Q₂ h2
          have h1 : 1 ≤ n := h.one_le
          have hn2 : 2 ≤ n := by omega
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2)
        (fun h3' => by
          have hne := hne1_Q₃ h3'
          have h1 : 1 ≤ n := h.one_le
          have hn2 : 2 ≤ n := by omega
          calc 3 ≤ 4 := by norm_num
            _ = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2))
  exact hQq

private theorem ne_bot_glapLayer {N : ℕ}
    (A : Subgroup ↥(sesqSpecialUnitaryGroupLE (idForm h N)))
    (hp : p.Prime) (q : ℕ) (S : SesqBlockData h A hp)
    (T : SesqTorusData h A hp q S) (Q : SesqQData h A hp q S T)
    (hQq : CFSG.Open.IsQuasisimple ↥(pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N))
      (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1))) :
    GLAPLayer p
      (pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N)) (blockSpace S.A'' S.D₁.1) ⊓
        Subgroup.centralizer (Subgroup.closure ({T.x₁, T.x₂} :
          Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))) :
          Set ↥(sesqSpecialUnitaryGroupLE (idForm h N)))) ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hx₃memQ : T.x₃ ∈ pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N))
      (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1) := by
    rw [mem_pointwiseStab]
    intro u hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add]
    congr 1
    · rw [T.hx₃]
      exact blockEnd_apply_of_mem_block S.A'' hp S.hpF S.hA''e S.t S.ht (D := S.D₃) (E := S.D₁)
        S.hD13 hu₁
    · rw [T.hx₃]
      exact blockEnd_apply_of_mem_block S.A'' hp S.hpF S.hA''e S.t S.ht (D := S.D₃) (E := S.D₂)
        S.hD23 hu₂
  have hpQ : p ∣ Nat.card (pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N))
      (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1)) := by
    have h := orderOf_dvd_natCard (⟨T.x₃, hx₃memQ⟩ : ↥(pointwiseStab
      (sesqSpecialUnitaryGroupLE (idForm h N)) (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1)))
    rwa [Subgroup.orderOf_mk, T.hord₃] at h
  have hcompQ : GLAPComponent p
      (pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N)) (blockSpace S.A'' S.D₁.1) ⊓
        Subgroup.centralizer (Subgroup.closure ({T.x₁, T.x₂} :
          Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))) :
          Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))))
      (pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N))
        (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1)) :=
    CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp hQq hpQ Q.hQleH Q.hQn
  have hQne : pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N))
      (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1) ≠ ⊥ := by
    intro hbot
    have hmem : T.x₃ ∈ (⊥ : Subgroup ↥(sesqSpecialUnitaryGroupLE (idForm h N))) :=
      hbot ▸ hx₃memQ
    rw [Subgroup.mem_bot] at hmem
    exact T.hx₃ne hmem
  intro hbot
  have hle : pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N))
      (blockSpace S.A'' S.D₁.1 ⊔ blockSpace S.A'' S.D₂.1) ≤
      GLAPLayer p (pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N))
        (blockSpace S.A'' S.D₁.1) ⊓
        Subgroup.centralizer (Subgroup.closure ({T.x₁, T.x₂} :
          Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))) :
          Set ↥(sesqSpecialUnitaryGroupLE (idForm h N)))) := by
    rw [GLAPLayer]
    exact le_sSup hcompQ
  exact hQne (le_bot_iff.1 (hbot ▸ hle))

theorem concl165Avoid_sesqSpecialUnitaryGroupLE {N : ℕ}
    (hN : 3 ≤ N) (hm0 : CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ≠ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2) (hqd : q ∣ 2 ^ n + 1)
    (A : Subgroup ↥(sesqSpecialUnitaryGroupLE (idForm h N))) (hAe : IsElemAbelian p A)
    (hmax : CFSG.Open.pRank p (⊤ : Subgroup ↥(sesqSpecialUnitaryGroupLE (idForm h N))) ≤
      CFSG.Open.pRank p A)
    (h3 : 3 ≤ CFSG.Open.pRank p A)
    (Z : Subgroup ↥(sesqSpecialUnitaryGroupLE (idForm h N)))
    (hZ : ∀ z ∈ Z, ∃ c : Fˣ,
      ((z : (Fin N → F) ≃ₗ[F] (Fin N → F)) : (Fin N → F) →ₗ[F] (Fin N → F)) =
        (c : F) • LinearMap.id) :
    Concl165Avoid ↥(sesqSpecialUnitaryGroupLE (idForm h N)) p q A Z := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have S : SesqBlockData h A hp :=
    exists_sesqBlockData (h := h) (A := A) hm0 hp hp2 hAe hmax h3
  have hV2le := blockSpace_le_orthogonalBilin_of_ne (h := h) (A := A) hp S
  have h4perp := four_le_finrank_orthogonalBilin_blockSpace (h := h) (A := A) hp S
  have T : SesqTorusData h A hp q S :=
    exists_sesqTorusData (h := h) (A := A) hm0 hp hp2 hq hq2 hqd S hV2le h4perp
  have J : SesqJData h A hp q S T :=
    exists_sesqJData (h := h) (N := N) (A := A) hp q S h4perp T
  have Qd : SesqQData h A hp q S T :=
    exists_sesqQData (h := h) (N := N) (A := A) hp q S T J
  have hQq := isQuasisimple_pointwiseStab_sup_blockSpace (h := h) (N := N) (A := A) hp hp2 q S T
  have hlayer := ne_bot_glapLayer (h := h) (N := N) (A := A) hp q S T Qd hQq
  have hFleJ : T.Fq.map (pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N))
      (blockSpace S.A'' S.D₁.1)).subtype ≤
      pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N)) (blockSpace S.A'' S.D₁.1) := by
    intro z hz
    obtain ⟨w, -, rfl⟩ := Subgroup.mem_map.mp hz
    exact w.2
  have hFleC : T.Fq.map (pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N))
      (blockSpace S.A'' S.D₁.1)).subtype ≤
      Subgroup.centralizer (Subgroup.zpowers T.x₁ :
        Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))) := by
    rw [J.hzpow]
    exact hFleJ.trans J.hJle
  have hFpRank : CFSG.Open.pRank q (T.Fq.map (pointwiseStab
      (sesqSpecialUnitaryGroupLE (idForm h N)) (blockSpace S.A'' S.D₁.1)).subtype) =
      CFSG.Open.pRank q T.Fq :=
    CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective (p := q) hq.one_lt _
      Subtype.coe_injective T.Fq
  refine ⟨Subgroup.zpowers T.x₁,
    Subgroup.closure ({T.x₁, T.x₂} : Set ↥(sesqSpecialUnitaryGroupLE (idForm h N))),
    T.Fq.map (pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N))
      (blockSpace S.A'' S.D₁.1)).subtype,
    pointwiseStab (sesqSpecialUnitaryGroupLE (idForm h N)) (blockSpace S.A'' S.D₁.1),
    ?_, ?_, ?_, ?_, J.hcompJ, J.hAnormJ, hlayer, hFleC, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  · refine (Subgroup.closure_le (K := A)).mpr ?_
    intro x hx
    rcases hx with rfl | rfl
    · exact T.hx₁A
    · exact T.hx₂A
  · rw [Nat.card_zpowers, T.hord₁]
  · have hmap : (Subgroup.closure ({T.x₁, T.x₂} :
        Set ↥(sesqSpecialUnitaryGroupLE (idForm h N)))).map
        (sesqSpecialUnitaryGroupLE (idForm h N)).subtype =
        Subgroup.closure ({blockEnd S.A'' hp S.hpF S.hA''e S.t S.ht S.D₁,
          blockEnd S.A'' hp S.hpF S.hA''e S.t S.ht S.D₂} :
          Set ((Fin N → F) ≃ₗ[F] (Fin N → F))) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      simp [T.hx₁, T.hx₂]
    rw [← Subgroup.card_map_of_injective (f := (sesqSpecialUnitaryGroupLE (idForm h N)).subtype)
      Subtype.coe_injective, hmap]
    exact card_closure_pair_blockEnd S.A'' hp S.hpF S.hA''e S.t S.ht S.hD12 S.hV1 S.hV2
      (S.hblockA S.D₁) (S.hblockA S.D₂)
  · exact CFSG.SectionRank.isElemAbelian_map T.hFqe _
  · intro z hz
    exact Subgroup.le_normalizer (hFleJ hz)
  · rw [hFpRank]
    exact T.hFq3
  · rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzF, hzZ⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨c, hc⟩ := hZ z hzZ
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot S.hV1
    have hzfix : ((z : ↥(sesqSpecialUnitaryGroupLE (idForm h N))) :
        (Fin N → F) ≃ₗ[F] (Fin N → F)) v = v := mem_pointwiseStab.mp (hFleJ hzF) v hv
    have hcv : ((c : F) • (LinearMap.id : (Fin N → F) →ₗ[F] (Fin N → F))) v = v := by
      rw [← hc]
      exact hzfix
    rw [LinearMap.smul_apply, LinearMap.id_apply] at hcv
    have hc1 : c = 1 := by
      have h2 : ((c : F) - 1) • v = 0 := by
        rw [sub_smul, one_smul, hcv, sub_self]
      rcases smul_eq_zero.mp h2 with h | h
      · exact Units.ext (sub_eq_zero.mp h)
      · exact absurd h hv0
    refine Subtype.ext ?_
    refine LinearEquiv.ext fun w => ?_
    have hzw : ((z : ↥(sesqSpecialUnitaryGroupLE (idForm h N))) :
        (Fin N → F) →ₗ[F] (Fin N → F)) w = w := by
      rw [hc, hc1, Units.val_one, one_smul]
      rfl
    simpa using hzw

end CFSG.LocalAnalysis.GLTheoremA.Y10F
