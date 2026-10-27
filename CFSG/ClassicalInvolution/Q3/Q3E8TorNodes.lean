module

public import CFSG.ClassicalInvolution.Q3.Q3E8TorFrame
public import CFSG.ClassicalInvolution.Q3.Q3E8TorStmt
public import CFSG.ClassicalInvolution.Q3.Q3E8Frame
public import CFSG.ClassicalInvolution.Q3.Q3EPFixed

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.Timmesfeld CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.E7Model CFSG.LieType.HighestRoot CFSG.LieType.RootSystem
open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false

local notation "M₇" => E7sc 3 1
local notation "D₇" => e7Datum (GaloisField 3 1)

section Roots

@[expose] def chainRho : V7 := ![-1, -2, -2, -3, -3, -2, -1]

theorem chain_roots_mem : ∀ r ∈ [simpleV 1, chainRho, simpleV 4, simpleV 5, simpleV 6],
    r ∈ rootFinset .E7 := by decide +kernel

theorem chain_orth_02 : ∀ r ∈ [simpleV 1, chainRho, simpleV 4, simpleV 5, simpleV 6],
    iform (simpleV 0) r = 0 ∧ iform (simpleV 2) r = 0 := by decide +kernel

theorem chain_rel :
    iform (simpleV 1) chainRho = -1 ∧ iform chainRho (simpleV 4) = -1 ∧
    iform (simpleV 4) (simpleV 5) = -1 ∧ iform (simpleV 5) (simpleV 6) = -1 ∧
    iform (simpleV 1) (simpleV 4) = 0 ∧ iform (simpleV 1) (simpleV 5) = 0 ∧
    iform (simpleV 1) (simpleV 6) = 0 ∧ iform chainRho (simpleV 5) = 0 ∧
    iform chainRho (simpleV 6) = 0 ∧ iform (simpleV 4) (simpleV 6) = 0 := by decide +kernel

theorem mem_roots_E7_3 {γ : V7} (hγ : γ ∈ rootFinset .E7) : γ ∈ (TypeE8.D7 3 1).roots :=
  (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField 3 1)).2
    (mem_rootFinset.1 hγ)

end Roots

section Transfer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem ETCtx3.adj_transfer (c : ETCtx3 .E7 0 Ω K z) {N N' : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) (hN' : N' ∈ centralizingMembers Ω {z})
    {T T' : Subgroup (Generic.modelUniv .E7 0 3 1 Nat.prime_three).K}
    (hT : T ∈ Generic.fundamentalSubgroups .E7 (Generic.modelUniv .E7 0 3 1 Nat.prime_three).D)
    (hT' : T' ∈ Generic.fundamentalSubgroups .E7 (Generic.modelUniv .E7 0 3 1 Nat.prime_three).D)
    (hNT : locImg Ω z N = T.map c.d.ψ) (hN'T : locImg Ω z N' = T'.map c.d.ψ)
    (h : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W N N') :
    Gaps.ModelAdj (Subgroup.center (Generic.modelUniv .E7 0 3 1 Nat.prime_three).K) T T' ∧
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W T T' := by
  obtain ⟨wN, hwN⟩ := c.hΩ.classical N hN.1
  obtain ⟨wN', hwN'⟩ := c.hΩ.classical N' hN'.1
  obtain ⟨hne, hnc, hcw, hnw⟩ := stdPair_data3 hwN hwN' h
  exact ⟨c.modelAdj_of_adj hN hN' hT hT' hNT hN'T hwN hwN' hne hnc hcw hnw,
    c.stdPair_model_E7 hN hN' hT hT' hNT hN'T h⟩

theorem ETCtx3.fixed_member (c : ETCtx3 .E7 0 Ω K z) {t : G} (ht : t * z * t⁻¹ = z)
    {M : Subgroup G} (hMz : M ∈ centralizingMembers Ω {z})
    {RM : Subgroup (Generic.modelUniv .E7 0 3 1 Nat.prime_three).K}
    (hRM : RM ∈ Generic.fundamentalSubgroups .E7 (Generic.modelUniv .E7 0 3 1 Nat.prime_three).D)
    (hMR : locImg Ω z M = RM.map c.d.ψ) {xM : G} (cx : ETCtx3 .E7 0 Ω M xM)
    {β : Subgroup G} (htβ : IsClassicalMember3 β t) {g₀ : TypeE8.K7 3 1} {r : Fin 7 → ℤ}
    {N : Subgroup G} (hN : cx.IsFrameMember g₀ r N) (hNK : Commutes N K) (hβN : Commutes β N) :
    ∃ T ∈ Generic.fundamentalSubgroups .E7 (Generic.modelUniv .E7 0 3 1 Nat.prime_three).D,
      N ∈ centralizingMembers Ω {z} ∧ locImg Ω z N = T.map c.d.ψ ∧ Commutes RM T ∧
        ∀ y ∈ T, Gaps.locAut c.hΩ.conjInvariant ht (c.d.ψ y) = c.d.ψ y := by
  have hNz : N ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hN.mem_Ω c.hz.mem hNK
  obtain ⟨T, hT, hNT⟩ := (ETCtx3.IsLayerMember.of_commutes_self c hNz hNK).exists_fund
  refine ⟨T, hT, hNz, hNT, (c.commutes_iff_fund hMz hNz hRM hMR hNT).mp hN.commutes_K, ?_⟩
  intro y hy
  exact c.fixed_of_commutes ht htβ hNz hβN _ (by rw [hNT]; exact ⟨y, hy, rfl⟩)

end Transfer

section Chain

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem ETCtx3.exists_fixed_chain (c : ETCtx3 .E7 0 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {j : Fin 7 → Subgroup G}
    (hj : NodeSystem 3 1 (edgeE 7) Ω K z j)
    (hjimg : ∀ a, locImg Ω z (j a) =
      (rankOne (Generic.modelUniv .E7 0 3 1 Nat.prime_three).D.rootGroup a).map c.d.ψ)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (htβ : IsClassicalMember3 β t)
    (hKβ : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hβ0 : Commutes β (j 0)) (ht : t * z * t⁻¹ = z) :
    ∃ (k₀ : M₇) (Γ : Set V7) (l : V7), (∀ γ ∈ Γ, IsRoot .E7 γ) ∧ l ∈ Submodule.span ℤ Γ ∧
      (∀ σ ∈ rootFinset .E7, iform l σ ≠ 0) ∧ ∀ γ ∈ Γ, ∀ y ∈ stdRankOne D₇ γ,
        Gaps.locAut c.hΩ.conjInvariant ht (c.d.ψ (k₀ * y * k₀⁻¹)) = c.d.ψ (k₀ * y * k₀⁻¹) := by
  classical
  have hB8 : TypeE8.E7FrameRelations 3 1 := e7FrameRelations3
  have hadm : StatedLieAdmissible .E7 0 3 1 := ⟨Nat.prime_three, le_rfl, rfl⟩
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    Gaps.standardPair_involutions_commute two_ne_zero_gf3 hW c.hz.mem htβ.mem
      c.hz.orderOf_eq_two htβ.orderOf_eq_two
  have hnormK : conjSub t K = K :=
    Gaps.conjSub_eq_of_standardPair two_ne_zero_gf3 hW htβ.mem htβ.orderOf_eq_two
  have hMz : j 0 ∈ centralizingMembers Ω {z} := hj.mem 0
  obtain ⟨xM, hxM⟩ := c.hΩ.classical (j 0) hMz.1
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle hMz.1 hxM
  have hKx : K ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes c.hK hxM.mem (hj.commK 0)
  have hβx : β ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes hβ hxM.mem hβ0
  have hKL := ETCtx3.IsLayerMember.of_not_commutes cx hKx hβx hKne hnKβ
  have hβL := ETCtx3.IsLayerMember.of_not_commutes cx hβx hKx hKne.symm
    (fun h => hnKβ (commutes_symm h))
  obtain ⟨RK, hRK, hKR⟩ := hKL.exists_fund
  obtain ⟨Rβ, hRβ, hβR⟩ := hβL.exists_fund
  have hadj : Gaps.ModelAdj (Subgroup.center (Generic.modelUniv .E7 0 3 1 Nat.prime_three).K) RK
      Rβ := cx.modelAdj_of_adj hKx hβx hRK hRβ hKR hβR c.hz htβ hKne hnKβ hzt hnormK
  have hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W RK Rβ :=
    cx.stdPair_model_E7 hKx hβx hRK hRβ hKR hβR ⟨W, hW⟩
  obtain ⟨g₀, hg₀K, hg₀β⟩ := e7PairFrame3 RK hRK Rβ hRβ hadj hlin 0 2 (by decide)
  have hKF : cx.IsFrameMember g₀ (simpleV 0) K := ⟨hKx, hKL.2, by rw [hKR, hg₀K]; rfl⟩
  have hβF : cx.IsFrameMember g₀ (simpleV 2) β := ⟨hβx, hβL.2, by rw [hβR, hg₀β]; rfl⟩
  have hα₀ : simpleV 0 ∈ (TypeE8.D7 3 1).roots := mem_roots_E7_3 (by decide +kernel)
  have hα₂ : simpleV 2 ∈ (TypeE8.D7 3 1).roots := mem_roots_E7_3 (by decide +kernel)
  have hr : ∀ r ∈ [simpleV 1, chainRho, simpleV 4, simpleV 5, simpleV 6],
      r ∈ (TypeE8.D7 3 1).roots := fun r hr => mem_roots_E7_3 (chain_roots_mem r hr)
  have hr₁ : simpleV 1 ∈ (TypeE8.D7 3 1).roots := hr _ (by simp)
  have hr₂ : chainRho ∈ (TypeE8.D7 3 1).roots := hr _ (by simp)
  have hr₃ : simpleV 4 ∈ (TypeE8.D7 3 1).roots := hr _ (by simp)
  have hr₄ : simpleV 5 ∈ (TypeE8.D7 3 1).roots := hr _ (by simp)
  have hr₅ : simpleV 6 ∈ (TypeE8.D7 3 1).roots := hr _ (by simp)
  obtain ⟨N₁, hN₁⟩ := cx.exists_isFrameMember hB8 g₀ hr₁
  obtain ⟨N₂, hN₂⟩ := cx.exists_isFrameMember hB8 g₀ hr₂
  obtain ⟨N₃, hN₃⟩ := cx.exists_isFrameMember hB8 g₀ hr₃
  obtain ⟨N₄, hN₄⟩ := cx.exists_isFrameMember hB8 g₀ hr₄
  obtain ⟨N₅, hN₅⟩ := cx.exists_isFrameMember hB8 g₀ hr₅
  have ho02 := chain_orth_02
  have hrel := chain_rel
  have hNK : ∀ {r : V7} {N : Subgroup G}, r ∈ [simpleV 1, chainRho, simpleV 4, simpleV 5,
      simpleV 6] → cx.IsFrameMember g₀ r N → Commutes N K ∧ Commutes β N := fun hrm hN =>
    ⟨(hKF.commutes_of_orth hB8 hN hα₀ (hr _ hrm) (ho02 _ hrm).1).symm,
      (hβF.commutes_of_orth hB8 hN hα₂ (hr _ hrm) (ho02 _ hrm).2)⟩
  obtain ⟨hN₁K, hβN₁⟩ := hNK (by simp) hN₁
  obtain ⟨hN₂K, hβN₂⟩ := hNK (by simp) hN₂
  obtain ⟨hN₃K, hβN₃⟩ := hNK (by simp) hN₃
  obtain ⟨hN₄K, hβN₄⟩ := hNK (by simp) hN₄
  obtain ⟨hN₅K, hβN₅⟩ := hNK (by simp) hN₅
  have hl := ModelFacts.isLongestRoot_single .E7 0 3 1 Nat.prime_three trivial hadm
  have hRM : rankOne (Generic.modelUniv .E7 0 3 1 Nat.prime_three).D.rootGroup
      ((0 : Fin 7) : Fin (Generic.modelUniv .E7 0 3 1 Nat.prime_three).D.rank) ∈
      Generic.fundamentalSubgroups .E7 (Generic.modelUniv .E7 0 3 1 Nat.prime_three).D :=
    rankOne_mem_fundamental _ (hl _ trivial)
  have hMR := hjimg 0
  obtain ⟨T₁, hT₁, hN₁z, hN₁T, hM1, hf₁⟩ := c.fixed_member ht hMz hRM hMR cx htβ hN₁ hN₁K hβN₁
  obtain ⟨T₂, hT₂, hN₂z, hN₂T, hM2, hf₂⟩ := c.fixed_member ht hMz hRM hMR cx htβ hN₂ hN₂K hβN₂
  obtain ⟨T₃, hT₃, hN₃z, hN₃T, hM3, hf₃⟩ := c.fixed_member ht hMz hRM hMR cx htβ hN₃ hN₃K hβN₃
  obtain ⟨T₄, hT₄, hN₄z, hN₄T, hM4, hf₄⟩ := c.fixed_member ht hMz hRM hMR cx htβ hN₄ hN₄K hβN₄
  obtain ⟨T₅, hT₅, hN₅z, hN₅T, hM5, hf₅⟩ := c.fixed_member ht hMz hRM hMR cx htβ hN₅ hN₅K hβN₅
  have hstd : ∀ {r r' : V7} {N N' : Subgroup G}, cx.IsFrameMember g₀ r N →
      cx.IsFrameMember g₀ r' N' → r ∈ (TypeE8.D7 3 1).roots → r' ∈ (TypeE8.D7 3 1).roots →
      iform r r' = -1 → ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W N N' :=
    fun hN hN' hrr hrr' ha => hN.stdPair_of_adj hB8 hN' hrr hrr' ha
  obtain ⟨a12, l12⟩ := c.adj_transfer hN₁z hN₂z hT₁ hT₂ hN₁T hN₂T
    (hstd hN₁ hN₂ hr₁ hr₂ hrel.1)
  obtain ⟨a23, l23⟩ := c.adj_transfer hN₂z hN₃z hT₂ hT₃ hN₂T hN₃T
    (hstd hN₂ hN₃ hr₂ hr₃ hrel.2.1)
  obtain ⟨a34, l34⟩ := c.adj_transfer hN₃z hN₄z hT₃ hT₄ hN₃T hN₄T
    (hstd hN₃ hN₄ hr₃ hr₄ hrel.2.2.1)
  obtain ⟨a45, l45⟩ := c.adj_transfer hN₄z hN₅z hT₄ hT₅ hN₄T hN₅T
    (hstd hN₄ hN₅ hr₄ hr₅ hrel.2.2.2.1)
  have hcm : ∀ {r r' : V7} {N N' : Subgroup G} {T T' : Subgroup M₇},
      cx.IsFrameMember g₀ r N → cx.IsFrameMember g₀ r' N' → r ∈ (TypeE8.D7 3 1).roots →
      r' ∈ (TypeE8.D7 3 1).roots → iform r r' = 0 → N ∈ centralizingMembers Ω {z} →
      N' ∈ centralizingMembers Ω {z} → T ∈ Generic.fundamentalSubgroups .E7 D₇ →
      locImg Ω z N = T.map c.d.ψ → locImg Ω z N' = T'.map c.d.ψ → Commutes T T' :=
    fun hN hN' hrr hrr' ho hNz hN'z hT hNT hN'T =>
      (c.commutes_iff_fund hNz hN'z hT hNT hN'T).mp (hN.commutes_of_orth hB8 hN' hrr hrr' ho)
  have h13 := hcm hN₁ hN₃ hr₁ hr₃ hrel.2.2.2.2.1 hN₁z hN₃z hT₁ hN₁T hN₃T
  have h14 := hcm hN₁ hN₄ hr₁ hr₄ hrel.2.2.2.2.2.1 hN₁z hN₄z hT₁ hN₁T hN₄T
  have h24 := hcm hN₂ hN₄ hr₂ hr₄ hrel.2.2.2.2.2.2.2.1 hN₂z hN₄z hT₂ hN₂T hN₄T
  have h15 := hcm hN₁ hN₅ hr₁ hr₅ hrel.2.2.2.2.2.2.1 hN₁z hN₅z hT₁ hN₁T hN₅T
  have h25 := hcm hN₂ hN₅ hr₂ hr₅ hrel.2.2.2.2.2.2.2.2.1 hN₂z hN₅z hT₂ hN₂T hN₅T
  have h35 := hcm hN₃ hN₅ hr₃ hr₅ hrel.2.2.2.2.2.2.2.2.2 hN₃z hN₅z hT₃ hN₃T hN₅T
  obtain ⟨x, Γ, l, hΓ, hl, hreg, hΓx⟩ := chain_frame_E7_3 hT₁ hT₂ hT₃ hT₄ hT₅ hRM a12 l12
    a23 l23 a34 l34 a45 l45 h13 h14 h24 h15 h25 h35 (commutes_symm hM1) (commutes_symm hM2)
    (commutes_symm hM3) (commutes_symm hM4) (commutes_symm hM5)
  have hfM : ∀ y ∈ rankOne (Generic.modelUniv .E7 0 3 1 Nat.prime_three).D.rootGroup
      ((0 : Fin 7) : Fin (Generic.modelUniv .E7 0 3 1 Nat.prime_three).D.rank),
      Gaps.locAut c.hΩ.conjInvariant ht (c.d.ψ y) = c.d.ψ y := fun y hy =>
    c.fixed_of_commutes ht htβ hMz hβ0 _ (by rw [hMR]; exact ⟨y, hy, rfl⟩)
  have key : ∀ {T : Subgroup M₇} {γ : V7} {y : M₇},
      (∀ y' ∈ T, Gaps.locAut c.hΩ.conjInvariant ht (c.d.ψ y') = c.d.ψ y') →
      conjSub x T = stdRankOne D₇ γ → y ∈ stdRankOne D₇ γ →
      Gaps.locAut c.hΩ.conjInvariant ht (c.d.ψ (x⁻¹ * y * (x⁻¹)⁻¹)) =
        c.d.ψ (x⁻¹ * y * (x⁻¹)⁻¹) := by
    intro T γ y hf hxT hy
    have hyT : x⁻¹ * y * (x⁻¹)⁻¹ ∈ T := by
      have : y ∈ conjSub x T := hxT ▸ hy
      rw [mem_conjSub_iff] at this
      rw [inv_inv]
      exact this
    exact hf _ hyT
  refine ⟨x⁻¹, Γ, l, hΓ, hl, hreg, fun γ hγ y hy => ?_⟩
  rcases hΓx γ hγ with h | h | h | h | h | h
  · exact key hf₁ h hy
  · exact key hf₂ h hy
  · exact key hf₃ h hy
  · exact key hf₄ h hy
  · exact key hf₅ h hy
  · exact key hfM h hy

end Chain

theorem e8PartnerToral3_of (hP1 : ToralStdE73) : E8PartnerToral3 := by
  intro G _ _ _ _ K z _ _ c j hj hjimg β hβ t htβ hKβ hβ0 ht
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have h2t : t * t = 1 := mul_self_of_isClassicalMember3 htβ
  have hKt : conjSub t K = K := by
    obtain ⟨W, hW⟩ := hKβ
    exact Gaps.conjSub_eq_of_standardPair two_ne_zero_gf3 hW htβ.mem htβ.orderOf_eq_two
  obtain ⟨k₀, Γ, l, hΓ, hl, hreg, hfix⟩ :=
    c.exists_fixed_chain hsingle hj hjimg hβ htβ hKβ hβ0 ht
  have hadm : StatedLieAdmissible .E7 0 3 1 := ⟨Nat.prime_three, le_rfl, rfl⟩
  have hgen := TypeEPattern.range_le_iSup_fund_simplyLaced (p := 3) (f := 1) (t := .E7)
    (n := 0) trivial hadm (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) c.d.ψ
  have hσ2 := Gaps.locAut_locAut c.hΩ.conjInvariant ht h2t
  have hσr := fun k => c.locAut_mem_range ht h2t hKt hgen k
  obtain ⟨v, hv⟩ := hP1 Γ l
    (fun γ hγ => (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField 3 1)).2
      (hΓ γ hγ)) hl hreg c.d.ψ c.d.ker_le (Gaps.locAut c.hΩ.conjInvariant ht) hσ2 hσr k₀
    (fun γ hγ y hy => hfix γ hγ y hy)
  refine ⟨k₀, v, fun γ hγ => ?_⟩
  obtain ⟨hn, hi⟩ := hv γ hγ
  exact ⟨TypeEPattern.map_eq_of_forall_mem _ hσ2 hn, hi⟩

end CFSG.ClassicalInvolution.Q3.Q3W
