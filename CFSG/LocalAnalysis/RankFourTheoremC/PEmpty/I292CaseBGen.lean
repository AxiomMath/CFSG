module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBLayer
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBModel

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB

open Matrix Subgroup CFSG.Open
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA

theorem relIndex_map_range_dvd' {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (M : Subgroup G) : (M.map f).relIndex f.range ∣ M.index := by
  have h : (M.map f).subgroupOf f.range = M.map f.rangeRestrict := by
    ext ⟨y, hy⟩
    constructor
    · intro h1
      obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 h1)
      exact ⟨m, hm, Subtype.ext hmy⟩
    · rintro ⟨m, hm, h2⟩
      rw [Subgroup.mem_subgroupOf]
      exact ⟨m, hm, congrArg Subtype.val h2⟩
  rw [Subgroup.relIndex, h]
  exact Subgroup.index_map_dvd (H := M) f.rangeRestrict_surjective

theorem exists_sylow_le_of_not_dvd_index' {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {T : Subgroup G} (hT : ¬ p ∣ T.index) :
    ∃ S : Sylow p G, (S : Subgroup G) ≤ T := by
  obtain ⟨S₀⟩ : Nonempty (Sylow p T) := inferInstance
  have hS : IsPGroup p ((S₀ : Subgroup T).map T.subtype) := S₀.isPGroup'.map T.subtype
  have hSi : ¬ p ∣ ((S₀ : Subgroup T).map T.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim S₀.not_dvd_index hT
  exact ⟨hS.toSylow hSi, by
    rw [IsPGroup.toSylow_coe]
    exact Subgroup.map_subtype_le _⟩

theorem exists_sylow_le_of_matrix {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]
    {P' : Type} [Group P'] (θ : Y →* MulAut P') (hker : IsPGroup p θ.ker)
    {G : Type} [Group G] (c : G →* MulAut P') (hDθ : c.range ≤ θ.range)
    (hDidx : ¬ p ∣ (c.range.comap θ).index) (N : Subgroup G) (hN : ¬ p ∣ N.index)
    {X : Subgroup Y} (hX : ∀ y : Y, θ y ∈ N.map c → y ∈ X) :
    ∃ Q : Sylow p Y, (Q : Subgroup Y) ≤ X := by
  have hND : N.map c ≤ c.range := fun φ hφ => by
    obtain ⟨g, -, rfl⟩ := hφ
    exact ⟨g, rfl⟩
  have hidx : ((N.map c).comap θ).index =
      (N.map c).relIndex c.range * c.range.relIndex θ.range := by
    rw [Subgroup.index_comap, Subgroup.relIndex_mul_relIndex (N.map c) c.range θ.range hND hDθ]
  have hidx' : c.range.relIndex θ.range = (c.range.comap θ).index :=
    (Subgroup.index_comap c.range θ).symm
  have hnd : ¬ p ∣ ((N.map c).comap θ).index := by
    rw [hidx, hidx']
    intro h
    rcases (Fact.out : p.Prime).dvd_mul.1 h with h1 | h1
    · exact hN (h1.trans (relIndex_map_range_dvd' c N))
    · exact hDidx h1
  have hle : (N.map c).comap θ ≤ X := fun y hy => hX y hy
  have hX' : ¬ p ∣ X.index := fun h => hnd (h.trans (Subgroup.index_dvd_of_le hle))
  exact exists_sylow_le_of_not_dvd_index' hX'


section Assembly

variable {p : ℕ} {K : Type} [Field K] {P' : Type} [Group P']

structure ModelHyps (M : MatModel p K P') (ŷ : GL (Fin p) K) : Prop where
  ŷ_mem : ŷ ∈ M.𝔾
  clif : ∀ Th : Subgroup (GL (Fin p) K), Th ≤ M.H → IsPGroup 2 Th → Th ≠ ⊥ →
    ŷ ∈ normalizer (Th : Set (GL (Fin p) K)) → ∃ B : GL (Fin p) K, B ∈ M.𝔾 ∧ DiagData Th ŷ B
  idx : ∀ (Th : Subgroup (GL (Fin p) K)) (B : GL (Fin p) K), B ∈ M.𝔾 → DiagData Th ŷ B →
    ŷ ∈ normalizer (Th : Set (GL (Fin p) K)) →
    ¬ p ∣ ((normalizer (Th : Set (GL (Fin p) K))).comap M.𝔾.subtype).index
  zeta : ∃ ζ : Kˣ, ζ ^ p = 1 ∧ ζ ≠ 1 ∧ ζ ^ 2 ≠ 1 ∧
    ∀ j : Fin p, diagGL p K (Pi.mulSingle j ζ) ∈ M.𝔾

structure AutHyps {Y : Type} [Group Y] (θ : Y →* MulAut P') (M : MatModel p K P') : Prop where
  D_le : M.c.range ≤ θ.range
  D_idx : ¬ p ∣ (M.c.range.comap θ).index
  D_norm : ∀ φ ∈ M.c.range, ∀ ψ : MulAut P', ψ * φ * ψ⁻¹ ∈ M.c.range
  D_ab : ∀ a b : MulAut P', a * b * a⁻¹ * b⁻¹ ∈ M.c.range

variable [Finite K] {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal]

theorem hZ_of_centralizer {p : ℕ} (hCp : IsPGroup p (centralizer (L : Set Y))) :
    ∀ z ∈ center ↥L, ∃ k : ℕ, z ^ (p ^ k) = 1 := by
  intro z hz
  have hzc : (z : Y) ∈ centralizer (L : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have := Subgroup.mem_center_iff.1 hz ⟨l, hl⟩
    exact congrArg Subtype.val this
  obtain ⟨k, hk⟩ := hCp ⟨(z : Y), hzc⟩
  refine ⟨k, Subtype.ext ?_⟩
  simpa using congrArg Subtype.val hk

theorem exists_lift_diag (hp : p.Prime) (hp2 : p ≠ 2)
    (hCp : IsPGroup p (centralizer (L : Set Y))) (eP : (↥L ⧸ center ↥L) ≃* P')
    (M : MatModel p K P') {ŷ : GL (Fin p) K} (hM : ModelHyps M ŷ) {T₀ : Subgroup Y}
    (hT₀L : T₀ ≤ L) (hT₀2 : IsPGroup 2 T₀) (hT₀ : T₀ ≠ ⊥) {x : Y}
    (hxN : x ∈ normalizer (T₀ : Set Y))
    (hx : thetaP L eP x = M.c ⟨ŷ, hM.ŷ_mem⟩) :
    ∃ Th : Subgroup (GL (Fin p) K), M.IsLift ((T₀.subgroupOf L).map (eL L eP)) Th ∧
      ŷ ∈ normalizer (Th : Set (GL (Fin p) K)) ∧
      ∃ B : GL (Fin p) K, B ∈ M.𝔾 ∧ DiagData Th ŷ B := by
  have hZ := hZ_of_centralizer (L := L) hCp
  have hTbne := map_ne_bot L eP hp hp2 hZ hT₀L hT₀2 hT₀
  obtain ⟨Th, hL⟩ := M.exists_isLift (fun t ht => isTwoElt_map L eP hT₀L hT₀2 t ht) hTbne
  have hst : M.c ⟨ŷ, hM.ŷ_mem⟩ ∈ stabSub ((T₀.subgroupOf L).map (eL L eP)) := by
    rw [← hx]
    exact mem_stabSub_of_mem_normalizer eP hT₀L hxN
  have hyN : ŷ ∈ normalizer (Th : Set (GL (Fin p) K)) :=
    hL.mem_normalizer_of_stab (g := ⟨ŷ, hM.ŷ_mem⟩) hst
  obtain ⟨B, hBG, hB⟩ := hM.clif Th hL.le_H hL.two hL.ne_bot hyN
  exact ⟨Th, hL, hyN, B, hBG, hB⟩


theorem exists_sylow_normalizer (hp : p.Prime) (hp2 : p ≠ 2) [Group.IsPerfect ↥L]
    (hCp : IsPGroup p (centralizer (L : Set Y))) (eP : (↥L ⧸ center ↥L) ≃* P')
    (M : MatModel p K P') {ŷ : GL (Fin p) K} (hM : ModelHyps M ŷ)
    (hAut : AutHyps (thetaP L eP) M) {T₀ : Subgroup Y} (hT₀L : T₀ ≤ L) (hT₀2 : IsPGroup 2 T₀)
    (hT₀ : T₀ ≠ ⊥) {x : Y} (hxN : x ∈ normalizer (T₀ : Set Y))
    (hx : thetaP L eP x = M.c ⟨ŷ, hM.ŷ_mem⟩) :
    ∃ Q : Sylow p Y, (Q : Subgroup Y) ≤ normalizer (T₀ : Set Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ := hZ_of_centralizer (L := L) hCp
  obtain ⟨Th, hL, hyN, B, hBG, hB⟩ := exists_lift_diag hp hp2 hCp eP M hM hT₀L hT₀2 hT₀ hxN hx
  have hker : IsPGroup p (thetaP L eP).ker := by
    have : (thetaP L eP).ker = centralizer (L : Set Y) := by
      ext y
      rw [MonoidHom.mem_ker, thetaP_eq_one_iff]
    rw [this]
    exact hCp
  refine exists_sylow_le_of_matrix (thetaP L eP) hker M.c hAut.D_le hAut.D_idx
    ((normalizer (Th : Set (GL (Fin p) K))).comap M.𝔾.subtype) (hM.idx Th B hBG hB hyN) ?_
  intro y hy
  obtain ⟨g, hg, hgy⟩ := hy
  have h1 : M.c g ∈ stabSub ((T₀.subgroupOf L).map (eL L eP)) := hL.stab_of_mem_normalizer hg
  rw [hgy] at h1
  exact (mem_normalizer_iff_mem_stab L eP hp hp2 hZ hT₀L hT₀2 y).2 h1

theorem glaPLayer_normalizer (hp : p.Prime) (hp2 : p ≠ 2) [Group.IsPerfect ↥L]
    (hCp : IsPGroup p (centralizer (L : Set Y))) (eP : (↥L ⧸ center ↥L) ≃* P')
    (M : MatModel p K P') {ŷ : GL (Fin p) K} (hM : ModelHyps M ŷ)
    (hAut : AutHyps (thetaP L eP) M) {T₀ : Subgroup Y} (hT₀L : T₀ ≤ L) (hT₀2 : IsPGroup 2 T₀)
    (hT₀ : T₀ ≠ ⊥) {x : Y} (hxN : x ∈ normalizer (T₀ : Set Y))
    (hx : thetaP L eP x = M.c ⟨ŷ, hM.ŷ_mem⟩) :
    GLAPLayer p (normalizer (T₀ : Set Y)) = ⊥ := by
  have hZ := hZ_of_centralizer (L := L) hCp
  obtain ⟨Th, hL, hyN, B, hBG, hB⟩ := exists_lift_diag hp hp2 hCp eP M hM hT₀L hT₀2 hT₀ hxN hx
  have hker : IsPGroup p (thetaP L eP).ker := by
    have : (thetaP L eP).ker = centralizer (L : Set Y) := by
      ext y
      rw [MonoidHom.mem_ker, thetaP_eq_one_iff]
    rw [this]
    exact hCp
  refine glaPLayer_normalizer_eq_bot hp (thetaP L eP) hker M.c.range hAut.D_norm hAut.D_ab
    hAut.D_le ((T₀.subgroupOf L).map (eL L eP))
    (fun y => mem_normalizer_iff_mem_stab L eP hp hp2 hZ hT₀L hT₀2 y) ?_ ?_
  · intro φ ψ hφ hψ hφf hψf
    obtain ⟨g, rfl⟩ := hφ
    obtain ⟨h, rfl⟩ := hψ
    have hg := (hL.fix_iff_mem_centralizer hp hp2).1 hφf
    have hh := (hL.fix_iff_mem_centralizer hp hp2).1 hψf
    have hcomm := centralizer_commute hB.sep hB.diag hg hh
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm
  · intro φ hφ hst hcomm
    obtain ⟨g, rfl⟩ := hφ
    have hgN : (g : GL (Fin p) K) ∈ normalizer (Th : Set (GL (Fin p) K)) :=
      hL.mem_normalizer_of_stab hst
    refine (hL.fix_iff_mem_centralizer hp hp2).2 ?_
    obtain ⟨ζ, hζp, hζ1, hζ2, hζG⟩ := hM.zeta
    refine mem_centralizer_of_comm_mod_scalar hB.sep hB.diag hBG hζp hζ1 hζ2 hζG ?_
    intro d hdG hdC hdp
    have hfix : ∀ t ∈ (T₀.subgroupOf L).map (eL L eP), M.c ⟨d, hdG⟩ t = t :=
      (hL.fix_iff_mem_centralizer hp hp2).2 hdC
    have hpel : ∃ k : ℕ, (M.c ⟨d, hdG⟩) ^ (p ^ k) = 1 := by
      refine ⟨1, ?_⟩
      rw [← map_pow, pow_one]
      have : (⟨d, hdG⟩ : ↥M.𝔾) ^ p = 1 := Subtype.ext (by simpa using hdp)
      rw [this, map_one]
    have hc := hcomm (M.c ⟨d, hdG⟩) ⟨_, rfl⟩ hfix hpel
    have h1 : M.c (g * ⟨d, hdG⟩ * g⁻¹ * ⟨d, hdG⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hc]
      group
    obtain ⟨z, hz⟩ := M.c_eq_one _ h1
    exact ⟨z, by simpa using hz⟩

end Assembly

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB
