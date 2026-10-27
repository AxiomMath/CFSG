module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinDict
public import CFSG.ClassicalInvolution.RouteD.GapsConj
public import CFSG.ClassicalInvolution.Balance.PassTwoConj

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair B12 B23 blockSL
  coe_blockSL_three_zero coe_blockSL_three_one)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime]

section NotCommute

variable {F : Type} [Field F] {X : Type} [Group X]

theorem not_commutes_B12_B23_map (θ : SL(3, F) →* X) (hker : θ.ker ≤ Subgroup.center SL(3, F)) :
    ¬ Commutes ((B12 F).map θ) ((B23 F).map θ) := by
  intro hc
  let tr : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  set a : SL(3, F) := blockSL F 3 2 0 (by omega) tr with ha
  set b : SL(3, F) := blockSL F 3 2 1 (by omega) tr with hb
  have h := hc (θ a) ⟨a, ⟨tr, rfl⟩, rfl⟩ (θ b) ⟨b, ⟨tr, rfl⟩, rfl⟩
  rw [← map_mul, ← map_mul] at h
  obtain ⟨z, hz⟩ : ∃ z : SL(3, F), z = (b * a)⁻¹ * (a * b) := ⟨_, rfl⟩
  have hk : z ∈ θ.ker := by
    rw [hz, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨ω, -, hω⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hker hk)
  have h' : a * b = b * a * z := by rw [hz]; group
  have hm := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F)) h'
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hm
  rw [← hω, ha, hb, coe_blockSL_three_zero, coe_blockSL_three_one] at hm
  have h02 := congrFun (congrFun hm 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, tr, Matrix.scalar_apply, Matrix.diagonal_apply]
    at h02

theorem B12_map_ne_B23_map (θ : SL(3, F) →* X) (hker : θ.ker ≤ Subgroup.center SL(3, F)) :
    (B12 F).map θ ≠ (B23 F).map θ := by
  intro h
  let tr : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  set a : SL(3, F) := blockSL F 3 2 0 (by omega) tr with ha
  have hx : θ a ∈ (B23 F).map θ := h ▸ ⟨a, ⟨tr, rfl⟩, rfl⟩
  obtain ⟨b, ⟨s, rfl⟩, hb⟩ := hx
  obtain ⟨z, hz⟩ : ∃ z : SL(3, F), z = (blockSL F 3 2 1 (by omega) s)⁻¹ * a := ⟨_, rfl⟩
  have hk : z ∈ θ.ker := by
    rw [hz, MonoidHom.mem_ker, map_mul, map_inv, hb, inv_mul_cancel]
  obtain ⟨ω, -, hω⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hker hk)
  have h' : a = blockSL F 3 2 1 (by omega) s * z := by rw [hz]; group
  have hm := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F)) h'
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hm
  rw [← hω, ha, coe_blockSL_three_zero, coe_blockSL_three_one] at hm
  have h01 := congrFun (congrFun hm 0) 1
  simp [Matrix.mul_apply, tr, Matrix.scalar_apply, Matrix.diagonal_apply] at h01

theorem not_commutes_of_linearBlockStandardPair {W U V : Subgroup X}
    (h : LinearBlockStandardPair F W U V) : ¬ Commutes U V := by
  obtain ⟨θ, c, -, hker, hcases⟩ := h
  let θ' : SL(3, F) →* X := θ.comp (MulAut.conj c⁻¹).toMonoidHom
  have hker' : θ'.ker ≤ Subgroup.center SL(3, F) := by
    intro x hx
    have hy : (MulAut.conj c⁻¹) x ∈ Subgroup.center SL(3, F) := hker hx
    have h1 := (inferInstance : (Subgroup.center SL(3, F)).Normal).conj_mem _ hy c
    have e : c * (MulAut.conj c⁻¹ x) * c⁻¹ = x := by
      simp only [MulAut.conj_apply]
      group
    rwa [e] at h1
  have key : ∀ B : Subgroup SL(3, F), (B.map (MulAut.conj c⁻¹).toMonoidHom).map θ = B.map θ' :=
    fun B => Subgroup.map_map _ _ _
  have hnc := not_commutes_B12_B23_map θ' hker'
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [key] at h1 h2
    rw [← h1, ← h2]
    exact hnc
  · rw [key] at h1 h2
    rw [← h1, ← h2] at *
    intro hc
    exact hnc hc.symm

theorem ne_of_linearBlockStandardPair {W U V : Subgroup X}
    (h : LinearBlockStandardPair F W U V) : U ≠ V := by
  obtain ⟨θ, c, -, hker, hcases⟩ := h
  let θ' : SL(3, F) →* X := θ.comp (MulAut.conj c⁻¹).toMonoidHom
  have hker' : θ'.ker ≤ Subgroup.center SL(3, F) := by
    intro x hx
    have hy : (MulAut.conj c⁻¹) x ∈ Subgroup.center SL(3, F) := hker hx
    have h1 := (inferInstance : (Subgroup.center SL(3, F)).Normal).conj_mem _ hy c
    have e : c * (MulAut.conj c⁻¹ x) * c⁻¹ = x := by
      simp only [MulAut.conj_apply]
      group
    rwa [e] at h1
  have key : ∀ B : Subgroup SL(3, F), (B.map (MulAut.conj c⁻¹).toMonoidHom).map θ = B.map θ' :=
    fun B => Subgroup.map_map _ _ _
  have hne := B12_map_ne_B23_map θ' hker'
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [key] at h1 h2
    rw [← h1, ← h2]
    exact hne
  · rw [key] at h1 h2
    rw [← h1, ← h2]
    exact hne.symm

end NotCommute

section Fund

variable {F : Type} [Field F]

theorem exists_partner_fund {t : StatedLieTag} (Y : LieUniversal) (ht : t ≠ .G2)
    (ht' : t ≠ .trialityD4)
    (h : ∀ γ, IsLongestRoot Y.D γ → ∃ δ, IsLongestRoot Y.D δ ∧
      ∃ W, LinearBlockStandardPair F W (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ))
        (Y.D.rootGroup δ ⊔ Y.D.rootGroup (-δ))) :
    ∀ R ∈ fundamentalSubgroups t Y.D, ∃ R' ∈ fundamentalSubgroups t Y.D,
      ∃ W, LinearBlockStandardPair F W R R' := by
  rintro R ⟨g, γ, hγ | ⟨hG2, -⟩ | ⟨hD4, -⟩, rfl⟩
  · obtain ⟨δ, hδ, W, hW⟩ := h γ hγ
    exact ⟨conjSub g (Y.D.rootGroup δ ⊔ Y.D.rootGroup (-δ)), ⟨g, δ, Or.inl hδ, rfl⟩, _,
      CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW g⟩
  · exact absurd hG2 ht
  · exact absurd hD4 ht'

end Fund

section Conj

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G}

theorem LocalShapeT.conj {a : ℕ} {tY : StatedLieTag} {nY : ℕ} (hΩ : ConjInvariant Ω) (g : G)
    (h : LocalShapeT p f a tY nY Ω z) : LocalShapeT p f a tY nY Ω (g * z * g⁻¹) := by
  obtain ⟨D, hcard, i₁, ht, hr, hrest⟩ := h
  obtain ⟨D', hc, htag⟩ := Gaps.exists_lieSystemData_conj hΩ g z D
  refine ⟨D', hc.trans hcard, Fin.cast hc.symm i₁, ?_, ?_, ?_⟩
  · rw [(htag i₁).1]; exact ht
  · rw [(htag i₁).2.1]; exact hr
  · intro i hi
    have e : Fin.cast hc.symm (Fin.cast hc i) = i := Fin.ext rfl
    have hi' : Fin.cast hc i ≠ i₁ := fun h' => hi (by rw [← e, h'])
    have := htag (Fin.cast hc i)
    rw [e] at this
    rw [this.1, this.2.1]
    exact hrest _ hi'

end Conj

section Twin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem centralizingMembers_eq_of_twin (hp2 : p ≠ 2) (hf : 0 < f) (hΩ : InClass p f Ω)
    {L T : Subgroup G} {zL zT : G} (hL : IsClassicalMember p f L zL)
    (hT : IsClassicalMember p f T zT) (hLT : ∃ g : G, T = conjSub g L)
    (hTmem : T ∈ centralizingMembers Ω {zL})
    (hTcomm : ∀ N ∈ centralizingMembers Ω {zL}, N ≠ T → Commutes T N) :
    centralizingMembers Ω {zT} = centralizingMembers Ω {zL} := by
  have hsub : centralizingMembers Ω {zL} ⊆ centralizingMembers Ω {zT} := by
    intro N hN
    by_cases hNT : N = T
    · subst hNT
      exact ⟨hTmem.1, le_centralizer_of_isClassicalMember hT⟩
    · exact mem_centralizingMembers_of_commutes hN.1 hT.mem (hTcomm N hN hNT).symm
  obtain ⟨g, hg⟩ := hLT
  have hzg : IsClassicalMember p f T (g * zL * g⁻¹) := by
    rw [hg]
    exact hL.conj g
  have hzz : zT = g * zL * g⁻¹ := hzg.eq_of_isCentralInvolution hp2 hf hT.isCentralInvolution
  have hcard : (centralizingMembers Ω {zT}).ncard ≤ (centralizingMembers Ω {zL}).ncard := by
    rw [hzz, ncard_centralizingMembers_conj hΩ.conjInvariant]
  exact (Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)).symm

end Twin

@[expose] def HasFixedMember {G : Type} [Group G] (Ω : Set (Subgroup G)) (K β : Subgroup G)
    (z : G) : Prop :=
  ∃ M ∈ Ω, Commutes K M ∧ Commutes β M ∧
    ¬ ∀ N ∈ centralizingMembers Ω {z}, N ≠ M → Commutes M N

namespace TCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

theorem exists_partner (c : TCtx p f tY nY Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeT p f 2 tY nY Ω z)
    (hne : (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D).Nonempty)
    (hMF4 : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      ∃ R' ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
        ∃ W, LinearBlockStandardPair (GaloisField p f) W R R') :
    ∃ β ∈ Ω, (∃ t : G, IsClassicalMember p f β t) ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) ∧ HasFixedMember Ω K β z := by
  obtain ⟨R₁, hR₁⟩ := hne
  obtain ⟨M, hMz, hMK, hMQ, hMR⟩ := c.exists_member_of_fund hR₁
  obtain ⟨R₂, hR₂, W₂, hW₂⟩ := hMF4 R₁ hR₁
  obtain ⟨N', hN'z, hN'K, hN'Q, hN'R⟩ := c.exists_member_of_fund hR₂
  obtain ⟨W₂', hW₂'⟩ := c.stdPair_of_fund hMz hN'z hW₂ hMR hN'R
  have hnc : ¬ Commutes M N' := not_commutes_of_linearBlockStandardPair hW₂'
  have hN'M : N' ≠ M := fun e => ne_of_linearBlockStandardPair hW₂' e.symm
  obtain ⟨g, hg⟩ := hsingle M hMz.1
  have hzx : IsClassicalMember p f M (g * z * g⁻¹) := by
    rw [hg]
    exact c.hz.conj g
  have hf : 0 < f := Nat.pos_of_ne_zero c.hf
  have hshape_x : LocalShapeT p f 2 tY nY Ω (g * z * g⁻¹) := hshape.conj c.hΩ.conjInvariant g
  have hP1_x : LocalOddCentral Ω {g * z * g⁻¹} :=
    Gaps.localOddCentral_conj c.hΩ.conjInvariant g z c.hP1
  obtain ⟨dx⟩ := hshape_x.nonempty_dictT2 c.hY.ne_d4 c.hY.sc c.hΩ hMz.1 hzx
  obtain ⟨dx', hQx⟩ := exists_dictT2_of_member c.hY hMz.1 hzx dx
  let cx : TCtx p f tY nY Ω M (g * z * g⁻¹) :=
    { hp2 := c.hp2, hq := c.hq, hΩ := c.hΩ, hex := c.hex, hK := hMz.1, hz := hzx, hP1 := hP1_x,
      d := dx', hQ₀ := hQx, hY := c.hY }
  have hKM : Commutes K M := c.commutes_K_of_ne hMz hMK
  have hKx : K ∈ centralizingMembers Ω {g * z * g⁻¹} :=
    mem_centralizingMembers_of_commutes c.hK hzx.mem hKM
  have hKM' : K ≠ M := hMK.symm
  by_cases hKQ : locImg Ω (g * z * g⁻¹) K ≤ dx'.Q₁
  ·
    exfalso
    have hcomm : ∀ N ∈ centralizingMembers Ω {g * z * g⁻¹}, N ≠ K → Commutes K N :=
      fun N hN hNK => cx.commutes_T_of_ne hKx hKQ hN hNK
    have hconj : ∃ g' : G, K = conjSub g' M := ⟨g⁻¹, by rw [hg, ← conjSub_mul, inv_mul_cancel, conjSub_one]⟩
    have heq := centralizingMembers_eq_of_twin c.hp2 hf c.hΩ hzx c.hz hconj hKx hcomm
    have hN'x : N' ∈ centralizingMembers Ω {g * z * g⁻¹} := heq ▸ hN'z
    exact hnc (cx.commutes_K_of_ne hN'x hN'M)
  · obtain ⟨R₀, hR₀, hKR₀⟩ := cx.exists_fund_of_ne hKx hKM' hKQ
    obtain ⟨R', hR', W, hW⟩ := hMF4 R₀ hR₀
    obtain ⟨β, hβx, hβM, hβQ, hβR⟩ := cx.exists_member_of_fund hR'
    obtain ⟨W', hW'⟩ := cx.stdPair_of_fund hKx hβx hW hKR₀ hβR
    obtain ⟨t, ht⟩ := c.hΩ.classical β hβx.1
    exact ⟨β, hβx.1, ⟨t, ht⟩, ⟨W', hW'⟩, M, hMz.1, hKM, (cx.commutes_K_of_ne hβx hβM).symm,
      fun hall => hnc (hall N' hN'z hN'M)⟩

end TCtx

end CFSG.ClassicalInvolution.RouteD
