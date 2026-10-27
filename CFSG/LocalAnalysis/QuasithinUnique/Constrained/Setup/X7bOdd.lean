module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bTop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualSp

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.Family

section Geometry

variable {K : Type} [Field K]

theorem spCoordImage_flag {r d : ℕ} (hd : d ≤ r) (σ : K ≃+* K) :
    spCoordImage (r := r) σ (flag r K d) = flag r K d := by
  ext v
  rw [mem_spCoordImage, mem_flag_of_le hd, mem_flag_of_le hd, mem_isoFlag, mem_isoFlag]
  simp only [map_eq_zero_iff _ σ.symm.injective]

theorem isTotallyIsotropic_flag {r d : ℕ} (hd : d ≤ r) :
    IsTotallyIsotropic (pairedSympForm K r) (flag r K d) := by
  intro x hx y hy
  exact isCompleteIsotropicFlag_flag.2.2 d hd x hx y hy

theorem isTotallyIsotropic_map_spAct {r : ℕ} (g : StatedSp r K) {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : IsTotallyIsotropic (pairedSympForm K r) W) :
    IsTotallyIsotropic (pairedSympForm K r) (W.map (spAct g)) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [spAct, mulVecLin_apply, mulVecLin_apply, pairedSympForm_mulVec]
  exact hW x hx y hy

end Geometry

section Standard

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem map_spInner_mul_fieldAut_projStabilizer {d : ℕ} (hd : d ≤ 2) (g : StatedSp 2 K)
    (φ : K ≃+* K) :
    (projStabilizer 2 K (flag 2 K d)).map (spInner 2 K g * fieldAut 2 K φ).toMonoidHom =
      projStabilizer 2 K ((flag 2 K d).map (spAct g)) := by
  have h1 : (spInner 2 K g * fieldAut 2 K φ).toMonoidHom =
      (spInner 2 K g).toMonoidHom.comp (fieldAut 2 K φ).toMonoidHom := rfl
  rw [h1, ← Subgroup.map_map, map_projStabilizer_fieldAut, spCoordImage_flag hd,
    projStabilizer_map_spAct, spInner_eq_conj]

theorem map_projStabilizer_flag_eq (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    {α : MulAut (StatedProj (StatedSp 2 K))} (hα : α ∈ spSemilinearAutGroup 2 K)
    (hU : (projUnipotent 2 K).map α.toMonoidHom = projUnipotent 2 K) (j : Fin 2) :
    (projStabilizer 2 K (flag 2 K ((j : ℕ) + 1))).map α.toMonoidHom =
      projStabilizer 2 K (flag 2 K ((j : ℕ) + 1)) := by
  obtain ⟨g, φ, rfl⟩ := exists_eq_spInner_mul_fieldAut hα
  obtain ⟨-, hUP, hmax, -⟩ := X7a.symplectic_two_residualOvergroupsAt hK
  set α := spInner 2 K g * fieldAut 2 K φ with hαdef
  have hcov : (projStabilizer 2 K (flag 2 K ((j : ℕ) + 1))) ⋖ ⊤ :=
    (hmax _ (hUP j)).mpr ⟨j, rfl⟩
  have hcov' : (projStabilizer 2 K (flag 2 K ((j : ℕ) + 1))).map α.toMonoidHom ⋖ ⊤ := by
    have key := (apply_covBy_apply_iff (MulEquiv.mapSubgroup α)).mpr hcov
    rwa [show (MulEquiv.mapSubgroup α) ⊤ = ⊤ from Subgroup.map_top_of_surjective _ α.surjective]
      at key
  have hle : projUnipotent 2 K ≤ (projStabilizer 2 K (flag 2 K ((j : ℕ) + 1))).map α.toMonoidHom :=
    hU ▸ Subgroup.map_mono (hUP j)
  obtain ⟨j', hj'⟩ := (hmax _ hle).mp hcov'
  have hj2 : (j : ℕ) + 1 ≤ 2 := by omega
  have hj2' : (j' : ℕ) + 1 ≤ 2 := by omega
  rw [map_spInner_mul_fieldAut_projStabilizer hj2] at hj' ⊢
  have hr : 1 ≤ 2 := by norm_num
  have hne : ∀ d : ℕ, 1 ≤ d → d ≤ 2 → ∀ (h : StatedSp 2 K), (flag 2 K d).map (spAct h) ≠ ⊥ := by
    intro d hd1 hd2 h hbot
    have := finrank_map_spAct h (flag 2 K d)
    rw [hbot, finrank_bot, finrank_flag (by omega)] at this
    omega
  have hne' : ∀ d : ℕ, 1 ≤ d → d ≤ 2 → flag 2 K d ≠ ⊥ := by
    intro d hd1 hd2 hbot
    have := congrArg (fun W : Submodule K (Fin 2 ⊕ Fin 2 → K) => Module.finrank K W) hbot
    simp only [finrank_bot] at this
    rw [finrank_flag (by omega)] at this
    omega
  have hW := (maximal_parabolics (K := K) 2 (r := 2) hr).2.2 _ _
    (hne _ (by omega) hj2 g) (isTotallyIsotropic_map_spAct g (isTotallyIsotropic_flag hj2))
    (hne' _ (by omega) hj2') (isTotallyIsotropic_flag hj2') hj'
  have hdim := congrArg (fun W : Submodule K (Fin 2 ⊕ Fin 2 → K) => Module.finrank K W) hW
  simp only [finrank_map_spAct] at hdim
  rw [finrank_flag (by omega), finrank_flag (by omega)] at hdim
  have hjj : j = j' := Fin.ext (by omega)
  rw [hj', hjj]

theorem projStabilizer_flag_not_normal (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) {d : ℕ} (hd1 : 1 ≤ d)
    (hd2 : d ≤ 2) : ¬ (projStabilizer 2 K (flag 2 K d)).Normal := by
  intro hN
  have hr : 1 ≤ 2 := by norm_num
  have hne' : flag 2 K d ≠ ⊥ := by
    intro hbot
    have := congrArg (fun W : Submodule K (Fin 2 ⊕ Fin 2 → K) => Module.finrank K W) hbot
    simp only [finrank_bot] at this
    rw [finrank_flag (by omega)] at this
    omega
  have hall : ∀ g : StatedSp 2 K, (flag 2 K d).map (spAct g) = flag 2 K d := by
    intro g
    have hconj : (projStabilizer 2 K (flag 2 K d)).map (MulAut.conj (proj 2 K g)).toMonoidHom =
        projStabilizer 2 K (flag 2 K d) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hN.conj_mem z hz (proj 2 K g)
      · intro hy
        refine ⟨(proj 2 K g)⁻¹ * y * ((proj 2 K g)⁻¹)⁻¹, hN.conj_mem y hy _, ?_⟩
        simp [MulAut.conj_apply]
        group
    have h1 : projStabilizer 2 K ((flag 2 K d).map (spAct g)) =
        projStabilizer 2 K (flag 2 K d) := by
      rw [projStabilizer_map_spAct, hconj]
    have hne1 : (flag 2 K d).map (spAct g) ≠ ⊥ := by
      intro hbot
      have := finrank_map_spAct g (flag 2 K d)
      rw [hbot, finrank_bot, finrank_flag (by omega)] at this
      omega
    exact (maximal_parabolics (K := K) 2 (r := 2) hr).2.2 _ _ hne1
      (isTotallyIsotropic_map_spAct g (isTotallyIsotropic_flag hd2)) hne'
      (isTotallyIsotropic_flag hd2) h1
  apply stabilizer_flag_ne_top (K := K) hd1 hd2
  rw [eq_top_iff]
  intro g _
  exact mem_stabilizer.mpr (hall g)

theorem map_conj_projStabilizer_flag_eq (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    (k : StatedProj (StatedSp 2 K)) {s : MulAut (StatedProj (StatedSp 2 K))}
    (hsE : s ∈ spSemilinearAutGroup 2 K)
    (hsU : ((projUnipotent 2 K).map (MulAut.conj k).toMonoidHom).map s.toMonoidHom =
      (projUnipotent 2 K).map (MulAut.conj k).toMonoidHom) (j : Fin 2) :
    ((projStabilizer 2 K (flag 2 K ((j : ℕ) + 1))).map (MulAut.conj k).toMonoidHom).map
        s.toMonoidHom =
      (projStabilizer 2 K (flag 2 K ((j : ℕ) + 1))).map (MulAut.conj k).toMonoidHom := by
  set c : MulAut (StatedProj (StatedSp 2 K)) := MulAut.conj k with hc
  have hcE : c ∈ spSemilinearAutGroup 2 K := inner_le_spSemilinearAutGroup ⟨k, rfl⟩
  set s' := c⁻¹ * s * c with hs'
  have hs'E : s' ∈ spSemilinearAutGroup 2 K := mul_mem (mul_mem (inv_mem hcE) hsE) hcE
  have hmul : s * c = c * s' := by rw [hs']; group
  have hs'U : (projUnipotent 2 K).map s'.toMonoidHom = projUnipotent 2 K := by
    have h1 : (projUnipotent 2 K).map s'.toMonoidHom =
        (((projUnipotent 2 K).map c.toMonoidHom).map s.toMonoidHom).map c⁻¹.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h1, hsU, Subgroup.map_map]
    ext y
    simp
  have h2 := map_projStabilizer_flag_eq hK hs'E hs'U j
  calc ((projStabilizer 2 K (flag 2 K ((j : ℕ) + 1))).map c.toMonoidHom).map s.toMonoidHom
      = (projStabilizer 2 K (flag 2 K ((j : ℕ) + 1))).map (s * c).toMonoidHom := by
        rw [Subgroup.map_map]
        rfl
    _ = (projStabilizer 2 K (flag 2 K ((j : ℕ) + 1))).map (c * s').toMonoidHom := by rw [hmul]
    _ = ((projStabilizer 2 K (flag 2 K ((j : ℕ) + 1))).map s'.toMonoidHom).map c.toMonoidHom := by
        rw [Subgroup.map_map]
        rfl
    _ = (projStabilizer 2 K (flag 2 K ((j : ℕ) + 1))).map c.toMonoidHom := by rw [h2]

omit [Finite K] in
theorem conj_injective_PP :
    Function.Injective (MulAut.conj :
      StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))) := by
  intro x y hxy
  obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := K) x
  obtain ⟨h, rfl⟩ := proj_surjective (r := 2) (K := K) y
  have : spInner 2 K g = spInner 2 K h := by rw [spInner_eq_conj, spInner_eq_conj]; exact hxy
  rw [spInner_injective this]

theorem aut_conj_conj {P : Type*} [Group P] (s : MulAut P) (x : P) :
    s * MulAut.conj x * s⁻¹ = MulAut.conj (s x) := by
  ext m
  simp [MulAut.conj_apply]

theorem aut_decomp {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (α : MulAut (StatedProj (StatedSp 2 K))) :
    ∃ (g : StatedSp 2 K) (j : ℕ), j < 2 * f ∧ α = spInner 2 K g * exceptionalAut K ^ j ∧
      (Even j → α ∈ spSemilinearAutGroup 2 K) := by
  obtain ⟨-, -, -, -, -, hmain⟩ := even_symplectic_two_exterior_square_automorphism hf hK
  obtain ⟨hsq, -, -, hdec, -, -, -, -, hEsup, -, -, -⟩ :=
    hmain (exceptionalAut K) exceptionalAut_proj
  obtain ⟨⟨g, j⟩, hα, -⟩ := hdec α
  refine ⟨g, j, j.2, hα, fun hj => ?_⟩
  obtain ⟨m, hm⟩ := hj
  rw [hEsup, hα]
  refine Subgroup.mul_mem_sup (spInner_mem_inner g) ?_
  rw [show (j : ℕ) = 2 * m by omega, pow_mul]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

end Standard

section Counting

theorem card_normal_eq {G : Type*} [Group G] [Finite G] {N H S : Subgroup G} [N.Normal]
    (hNH : N ≤ H) (hSH : S ≤ H) (hHS : N ⊔ S = H) :
    Nat.card N = S.relIndex H * Nat.card (S ⊓ N : Subgroup G) := by
  have h1 := Subgroup.relIndex_mul_card N S
  have h2 := Subgroup.relIndex_mul_card S H
  have h3 := Subgroup.relIndex_mul_card N H
  have h4 : N.relIndex H = N.relIndex S := by
    rw [← hHS, sup_comm]
    exact Subgroup.relIndex_sup_right S N
  rw [inf_eq_left.mpr hSH] at h2
  rw [inf_eq_left.mpr hNH, h4] at h3
  rw [inf_comm] at h1
  have hne : N.relIndex S ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact (Nat.card_pos (α := S)).ne' h1.symm
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) ?_
  calc N.relIndex S * Nat.card N = Nat.card H := h3
    _ = S.relIndex H * Nat.card S := h2.symm
    _ = S.relIndex H * (N.relIndex S * Nat.card (S ⊓ N : Subgroup G)) := by rw [h1]
    _ = N.relIndex S * (S.relIndex H * Nat.card (S ⊓ N : Subgroup G)) := by ring

end Counting

section Abstract

theorem no_fixed_pair_of_unique_maximal {P : Type*} [Group P] [Finite P]
    (hι : Function.Injective (MulAut.conj : P →* MulAut P)) (H S : Subgroup (MulAut P))
    (hInn : (MulAut.conj : P →* MulAut P).range ≤ H) (hSH : S ≤ H)
    (hHS : (MulAut.conj : P →* MulAut P).range ⊔ S = H)
    (huniq : ∃! M : Subgroup ↥H, IsCoatom M ∧ S.subgroupOf H ≤ M)
    (Q : Fin 2 → Subgroup P) (hcoat : ∀ j, IsCoatom (Q j)) (hne : Q 0 ≠ Q 1)
    (hnn : ∀ j, ¬ (Q j).Normal)
    (hfix : ∀ s ∈ S, ∀ j, (Q j).map s.toMonoidHom = Q j) : False := by
  classical
  obtain ⟨M₀, ⟨hM₀c, hSM₀⟩, hM₀u⟩ := huniq
  set ι : P →* MulAut P := MulAut.conj with hιdef
  let A : Fin 2 → Subgroup (MulAut P) := fun j => (Q j).map ι
  have hAH : ∀ j, A j ≤ H := fun j =>
    le_trans (Subgroup.map_le_range ι (Q j)) hInn
  have key : ∀ j, ∀ s ∈ S, ∀ a ∈ A j, s * a * s⁻¹ ∈ A j := by
    intro j s hs
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨s q, ?_, ?_⟩
    · rw [← hfix s hs j]
      exact ⟨q, hq, rfl⟩
    · simp only [hιdef]
      exact (aut_conj_conj s q).symm
  have hSnorm : ∀ j, ∀ s ∈ S, s ∈ Subgroup.normalizer (A j : Set (MulAut P)) := by
    intro j s hs
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨fun ha => key j s hs a ha, fun ha => ?_⟩
    have h1 := key j s⁻¹ (inv_mem hs) _ ha
    have h2 : s⁻¹ * (s * a * s⁻¹) * s⁻¹⁻¹ = a := by group
    rwa [h2] at h1
  let Y : Fin 2 → Subgroup (MulAut P) := fun j => Subgroup.normalizer (A j : Set (MulAut P)) ⊓ H
  have hSY : ∀ j, S ≤ Y j := fun j s hs => ⟨hSnorm j s hs, hSH hs⟩
  have hAY : ∀ j, A j ≤ Y j := fun j a ha => ⟨Subgroup.le_normalizer ha, hAH j ha⟩
  have hYproper : ∀ j, (Y j).subgroupOf H ≠ ⊤ := by
    intro j hY
    have hnot : Subgroup.normalizer (Q j : Set P) ≠ ⊤ := fun h =>
      hnn j (Subgroup.normalizer_eq_top_iff.mp h)
    obtain ⟨x, hx⟩ : ∃ x, x ∉ Subgroup.normalizer (Q j : Set P) := by
      by_contra hcon
      push Not at hcon
      exact hnot (eq_top_iff.mpr fun x _ => hcon x)
    have hιxH : ι x ∈ H := hInn ⟨x, rfl⟩
    have hmem : (⟨ι x, hιxH⟩ : H) ∈ (Y j).subgroupOf H := by
      rw [hY]
      exact Subgroup.mem_top _
    have h1 : ι x ∈ Subgroup.normalizer (A j : Set (MulAut P)) := hmem.1
    apply hx
    rw [Subgroup.mem_normalizer_iff] at h1 ⊢
    intro q
    have h2 := h1 (ι q)
    rw [← map_inv, ← map_mul, ← map_mul] at h2
    exact (Subgroup.mem_map_iff_mem hι).symm.trans (h2.symm.trans (Subgroup.mem_map_iff_mem hι)) |>.symm
  have hYle : ∀ j, (Y j).subgroupOf H ≤ M₀ := by
    intro j
    obtain ⟨M, hMc, hYM⟩ := (eq_top_or_exists_le_coatom ((Y j).subgroupOf H)).resolve_left
      (hYproper j)
    have hSM : S.subgroupOf H ≤ M := fun x hx => hYM (by
      show (x : MulAut P) ∈ Y j
      exact hSY j hx)
    have := hM₀u M ⟨hMc, hSM⟩
    exact this ▸ hYM
  have hAle : ∀ j, (A j).subgroupOf H ≤ M₀ := fun j x hx =>
    hYle j (show x ∈ (Y j).subgroupOf H from hAY j hx)
  have hsupQ : Q 0 ⊔ Q 1 = ⊤ := by
    refine (hcoat 0).2 _ (lt_of_le_of_ne le_sup_left fun h => ?_)
    have h1 : Q 1 ≤ Q 0 := by
      rw [← sup_eq_left]
      exact h.symm
    have h2 : Q 1 < Q 0 := lt_of_le_of_ne h1 (Ne.symm hne)
    exact (hcoat 0).1 ((hcoat 1).2 _ h2)
  have hsupA : A 0 ⊔ A 1 = (MulAut.conj : P →* MulAut P).range := by
    simp only [A]
    rw [← Subgroup.map_sup, hsupQ, Subgroup.map_top]
  have htop : ((A 0 ⊔ A 1) ⊔ S).subgroupOf H = ⊤ := by
    rw [hsupA, hHS, Subgroup.subgroupOf_self]
  have hle : ((A 0 ⊔ A 1) ⊔ S).subgroupOf H ≤ M₀ := by
    rw [Subgroup.subgroupOf_sup (le_trans (sup_le (hAH 0) (hAH 1)) le_rfl) hSH,
      Subgroup.subgroupOf_sup (hAH 0) (hAH 1)]
    exact sup_le (sup_le (hAle 0) (hAle 1)) hSM₀
  rw [htop] at hle
  exact hM₀c.1 (eq_top_iff.mpr hle)

end Abstract

section Main

theorem unique_Sylow_overgroup_forces_odd_diagram_coset : UniqueSylowOddDiagramCoset := by
  intro f K _ _ _ hf hK H S hInn hSH hHS hSyl huniq
  by_contra hcon
  push Not at hcon
  have hf1 : 1 ≤ f := by omega
  have hKex : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hK⟩
  have hSE : ∀ s ∈ S, s ∈ spSemilinearAutGroup 2 K := by
    intro s hs
    obtain ⟨g, j, hj, hsj, hE⟩ := aut_decomp hf1 hK s
    refine hE ?_
    by_contra hodd
    have hodd' := Nat.not_even_iff_odd.mp hodd
    exact hcon s hs g j hodd' (hodd'.pos) hj hsj
  have hι : Function.Injective (MulAut.conj :
      StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))) := conj_injective_PP
  set Ux : Subgroup (StatedProj (StatedSp 2 K)) :=
    S.comap (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))) with hUx
  have hmapUx : Ux.map (MulAut.conj : StatedProj (StatedSp 2 K) →*
      MulAut (StatedProj (StatedSp 2 K))) = S ⊓ inner (StatedProj (StatedSp 2 K)) := by
    rw [hUx, Subgroup.map_comap_eq, inf_comm]
    rfl
  have hUx2 : IsPGroup 2 Ux := by
    intro x
    obtain ⟨k, hk⟩ := hSyl.2.1 ⟨(MulAut.conj : StatedProj (StatedSp 2 K) →*
      MulAut (StatedProj (StatedSp 2 K))) x.1, x.2⟩
    refine ⟨k, Subtype.ext (hι ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hUxidx : ¬ 2 ∣ Ux.index := by
    have h1 := card_normal_eq (G := MulAut (StatedProj (StatedSp 2 K)))
      (N := inner (StatedProj (StatedSp 2 K))) hInn hSH hHS.symm.symm
    have h2 : Nat.card (inner (StatedProj (StatedSp 2 K))) = Nat.card (StatedProj (StatedSp 2 K)) :=
      (Nat.card_congr (MonoidHom.ofInjective hι).toEquiv).symm
    have h3 : Nat.card (S ⊓ inner (StatedProj (StatedSp 2 K)) : Subgroup _) = Nat.card Ux := by
      rw [← hmapUx]
      exact Subgroup.card_map_of_injective hι
    have h4 := Subgroup.card_mul_index Ux
    rw [← h2, h1, h3] at h4
    have hpos : 0 < Nat.card Ux := Nat.card_pos
    have h5 : Ux.index = S.relIndex H := by
      refine Nat.eq_of_mul_eq_mul_left hpos ?_
      rw [h4, mul_comm]
    rw [h5]
    exact hSyl.2.2
  have hUxSyl : IsSylowTwoOf Ux ⊤ := ⟨le_top, hUx2, by
    rw [show (Ux.subgroupOf ⊤).index = Ux.index from Subgroup.relIndex_top_right Ux]
    exact hUxidx⟩
  have hSUx : ∀ s ∈ S, Ux.map s.toMonoidHom = Ux := by
    have h1 : ∀ s ∈ S, ∀ x ∈ Ux, s x ∈ Ux := by
      intro s hs x hx
      have : s * MulAut.conj x * s⁻¹ ∈ S := mul_mem (mul_mem hs hx) (inv_mem hs)
      rw [aut_conj_conj] at this
      exact this
    intro s hs
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact h1 s hs x hx
    · intro hy
      refine ⟨s⁻¹ y, h1 s⁻¹ (inv_mem hs) y hy, ?_⟩
      show s (s⁻¹ y) = y
      simp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  let Sx : Sylow 2 (StatedProj (StatedSp 2 K)) := hUx2.toSylow hUxidx
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (StatedProj (StatedSp 2 K)) P₀ Sx
  have hUxk : Ux = (projUnipotent 2 K).map (MulAut.conj k).toMonoidHom := by
    have h1 : ((k • P₀ : Sylow 2 _) : Subgroup _) = Ux := by
      rw [hk]
      rfl
    rw [← h1, Sylow.coe_subgroup_smul, hP₀]
    rfl
  have hres1 := (X7a.symplectic_two_residualOvergroupsAt hKex).map (MulAut.conj k)
  rw [← hUxk] at hres1
  obtain ⟨hne1, -, -, -⟩ := hres1
  let Qx : Fin 2 → Subgroup (StatedProj (StatedSp 2 K)) := fun j =>
    (projStabilizer 2 K (flag 2 K ((j : ℕ) + 1))).map (MulAut.conj k).toMonoidHom
  have hcoat : ∀ j, IsCoatom (Qx j) := fun j =>
    (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup (MulAut.conj k)) _).mpr
      (isCoatom_projStabilizer_flag (K := K) (by omega) (by have := j.2; omega))
  have hnn : ∀ j, ¬ (Qx j).Normal := by
    intro j hN
    apply projStabilizer_flag_not_normal hKex (d := (j : ℕ) + 1) (by omega)
      (by have := j.2; omega)
    have h1 := hN.map (MulAut.conj k⁻¹).toMonoidHom (MulAut.conj k⁻¹).surjective
    have h2 : (Qx j).map (MulAut.conj k⁻¹).toMonoidHom =
        projStabilizer 2 K (flag 2 K ((j : ℕ) + 1)) := by
      simp only [Qx, Subgroup.map_map]
      ext y
      simp only [Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      constructor
      · rintro ⟨x, hx, hxy⟩
        have : x = y := by rw [← hxy]; group
        rwa [← this]
      · intro hy
        exact ⟨y, hy, by group⟩
    rwa [h2] at h1
  have hfix : ∀ s ∈ S, ∀ j, (Qx j).map s.toMonoidHom = Qx j := fun s hs j =>
    map_conj_projStabilizer_flag_eq hKex k (hSE s hs) (by rw [← hUxk]; exact hSUx s hs) j
  exact no_fixed_pair_of_unique_maximal hι H S hInn hSH hHS huniq Qx hcoat hne1 hnn hfix

end Main

section Top

theorem original_minimal_parabolic_FF_actor_excludes_PSp4_components_of
    (h27 : DiagramNormalizerExcludesOffenders) (hdata : ActualSymplecticFourData) {V : Type}
    [CommGroup V] [Finite V] {H T M E : Subgroup (MulAut V)} (hF : FFHyp V H T M E)
    (hns : ¬ Group.IsSolvable H) {L : Subgroup (MulAut V)} (hL : IsComp L H) {f : ℕ}
    (hf : 2 ≤ f) : ¬ StatedClassicalModel (CQ L) .PSp 2 2 f :=
  original_minimal_parabolic_FF_actor_excludes_PSp4_components
    unique_Sylow_overgroup_forces_odd_diagram_coset h27 hdata hF hns hL hf

theorem noPSp4Component_of
    (h27 : DiagramNormalizerExcludesOffenders)
    (hdata : ActualSymplecticFourData) : CFSG.QuasithinUnique.Setup.Top.NoPSp4Component :=
  noPSp4Component unique_Sylow_overgroup_forces_odd_diagram_coset h27 hdata

end Top

end CFSG.QuasithinUnique.Setup.X7b
