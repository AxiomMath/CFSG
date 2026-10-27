module

public import CFSG.ClassicalInvolution.RouteD.TypeUFive
public import CFSG.ClassicalInvolution.RouteD.LocalTwin

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Exceptional CFSG.Timmesfeld
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

structure IsPhanChainE6 (p f : ℕ) [Fact p.Prime] {X : Type} [Group X] (U : Fin 6 → Subgroup X) :
    Prop where
  iso : ∀ i, Nonempty (Su (GaloisField p (2 * f)) p f 2 ≃* U i)
  comm : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i → Commutes (U i) (U j)
  pair : ∀ i j : Fin 6, edgeE 6 i j →
    ∃ W : Subgroup X, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (U i) (U j)

theorem isPhanChainE6_of_members {G : Type} [Group G] [Finite G] (hq : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {U : Fin 6 → Subgroup G}
    (hUΩ : ∀ i, U i ∈ Ω)
    (hcomm : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin 6, edgeE 6 i j →
      ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (U i) (U j)) :
    IsPhanChainE6 p f U where
  iso i := nonempty_su_two_equiv_of_member hq hΩ hex (hUΩ i)
  comm := hcomm
  pair := hpair

structure PhanE6Frame (p f : ℕ) [Fact p.Prime] where
  V : Fin 6 → Subgroup (twistedE6Group p f)
  Rθ : Subgroup (twistedE6Group p f)
  chain : IsPhanChainE6 p f V
  V_mem : ∀ i, V i ∈ fundamentalSubgroups .twistedE6 (twistedE6Datum p f)
  Rθ_mem : Rθ ∈ fundamentalSubgroups .twistedE6 (twistedE6Datum p f)
  Rθ_comm : ∀ i : Fin 6, i ≠ 1 → Commutes (V i) Rθ

@[expose] def PhanE6Universal (F : PhanE6Frame p f) : Prop :=
  ∀ {X : Type} [Group X] (U : Fin 6 → Subgroup X), IsPhanChainE6 p f U →
    ∃ Ψ : twistedE6Group p f →* X, Ψ.ker ≤ Subgroup.center _ ∧ Ψ.range = ⨆ i, U i ∧
      ∀ i, (F.V i).map Ψ = U i

@[expose] def PhanE6 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∃ F : PhanE6Frame p f, PhanE6Universal F

section ExtModelSection

variable (F : PhanE6Frame p f)

@[expose] def PhanE6Frame.path (k : Fin 5) : Subgroup (twistedE6Group p f) :=
  F.V (![0, 2, 3, 4, 5] k)

theorem PhanE6Frame.path_comm :
    ∀ i j : Fin 5, (i : ℕ) + 1 < j → Commutes (F.path i) (F.path j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij <;>
    exact F.chain.comm _ _ (by decide) (by simp [edgeE]) (by simp [edgeE])

theorem PhanE6Frame.path_pair : ∀ i j : Fin 5, (j : ℕ) = i + 1 →
    ∃ W : Subgroup (twistedE6Group p f),
      UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (F.path i) (F.path j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij <;>
    exact F.chain.pair _ _ (by simp [edgeE])

theorem PhanE6Frame.exists_psi (hq : 5 ≤ p ^ f) :
    ∃ ψ : Su (GaloisField p (2 * f)) p f 6 →* twistedE6Group p f,
      ψ.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f 6) ∧ ψ.range = ⨆ k, F.path k ∧
      ∀ i : Fin 5, (blockEmb2 (GaloisField p (2 * f)) p f 5 i).range.map ψ = F.path i :=
  exists_psi_of_chainU hq (m := 3) (by norm_num) (U := F.path) (fun i => F.chain.iso _)
    F.path_comm F.path_pair

theorem PhanE6Frame.nonempty_extModel (F : PhanE6Frame p f) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    Nonempty (ExtModel p f .twistedE6 0 .PSU 6 1) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := typeU_card_field hq
  have hadmP : StatedLieAdmissible .PSU 6 p f :=
    ⟨Fact.out, hf, by norm_num, fun h => by simp [Prod.ext_iff] at h⟩
  obtain ⟨e, he⟩ := psu_model_equiv hp2 hadmP
  obtain ⟨ψ, hψker, hψrange, hψblk⟩ := F.exists_psi hq
  have hscT : FundamentalSingleClass .twistedE6 (twistedE6Datum p f) :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .twistedE6 0 p f Fact.out trivial
      (⟨Fact.out, hf, rfl⟩ : StatedLieAdmissible .twistedE6 0 p f) (by decide) (by decide)
  have hVperf : ∀ i, F.V i ≤ ⁅F.V i, F.V i⁆ := by
    intro i
    have : Group.IsPerfect (Su (GaloisField p (2 * f)) p f 2) := isPerfect_su_two hK hq
    obtain ⟨φ⟩ := F.chain.iso i
    have h := typeU_range_perfect_of_perfect ((F.V i).subtype.comp φ.toMonoidHom)
    rwa [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr φ.surjective, Subgroup.map_top,
      Subgroup.range_subtype] at h
  have hTperf : ∀ R ∈ fundamentalSubgroups .twistedE6 (twistedE6Datum p f), R ≤ ⁅R, R⁆ := by
    intro R hR
    obtain ⟨g, hg⟩ := hscT _ (F.V_mem 0) R hR
    rw [hg]
    exact map_perfect (MulAut.conj g).toMonoidHom (hVperf 0)
  have hrootψ : (rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 6)).map ψ = F.V 0 := by
    have := hψblk 0
    exact this
  refine ⟨{
    Rθ := F.Rθ
    twin := fun i => absurd i.2 (by simp)
    Θ := ψ.comp e.toMonoidHom
    Rθ_mem := F.Rθ_mem
    twin_mem := fun i => absurd i.2 (by simp)
    Θ_ker := ?_
    Θ_mem := ?_
    Θ_comm := ?_
    twin_comm := fun i => absurd i.2 (by simp)
    twin_comm_Θ := fun i => absurd i.2 (by simp)
    twin_inj := fun i => absurd i.2 (by simp)
    perf_T := hTperf
    perf_Y := ?_ }⟩
  · intro x hx
    exact (MulEquivClass.apply_mem_center_iff e).1 (hψker hx)
  · intro R hR
    obtain ⟨g, hg⟩ := (mem_longRootSetU_iff (by norm_num : 2 ≤ 6)).mp ((he R).mp hR)
    have h1 : R.map (ψ.comp e.toMonoidHom) = conjSub (ψ g) (F.V 0) := by
      rw [← Subgroup.map_map, hg, map_map_conj, hrootψ]
      rfl
    have h2 : conjSub (ψ g) (F.V 0) ∈ fundamentalSubgroups .twistedE6 (twistedE6Datum p f) :=
      conjSub_mem_fundamentalSubgroups (F.V_mem 0) (ψ g)
    rw [← h1] at h2
    exact h2
  · intro R hR
    have hRle : R.map (ψ.comp e.toMonoidHom) ≤ ⨆ k, F.path k := by
      rw [← hψrange, ← Subgroup.map_map]
      exact Subgroup.map_le_range ψ _
    have hcent : ⨆ k, F.path k ≤ Subgroup.centralizer (F.Rθ : Set (twistedE6Group p f)) := by
      refine iSup_le fun k => ?_
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hk : ![0, 2, 3, 4, 5] k ≠ (1 : Fin 6) := by
        fin_cases k <;> simp
      exact (F.Rθ_comm _ hk w hw y hy).symm
    intro a ha r hr
    have := Subgroup.mem_centralizer_iff.mp (hcent (hRle ha)) r hr
    exact this.symm
  · intro R hR
    obtain ⟨g, hg⟩ := (mem_longRootSetU_iff (by norm_num : 2 ≤ 6)).mp ((he R).mp hR)
    have hperfroot : (rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 6)) ≤
        ⁅rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 6),
          rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 6)⁆ := by
      have : Group.IsPerfect (Su (GaloisField p (2 * f)) p f 2) := isPerfect_su_two hK hq
      exact typeU_range_perfect_of_perfect (blockEmb (GaloisField p (2 * f)) p f 6 2 0
        (by norm_num))
    have h2 := map_perfect (MulAut.conj g).toMonoidHom hperfroot
    have h3 := map_perfect e.symm.toMonoidHom (hg ▸ h2)
    have h4 : (R.map e.toMonoidHom).map e.symm.toMonoidHom = R := by
      rw [Subgroup.map_map]
      have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
        ext x; simp
      rw [this, Subgroup.map_id]
    rwa [h4] at h3

end ExtModelSection

section Closure

variable {G : Type} [Group G]

theorem LocalShapeU.toT {m : ℕ} {Ω : Set (Subgroup G)} {x : G} (h : LocalShapeU p f m Ω x) :
    LocalShapeT p f 1 .PSU (m + 1) Ω x := by
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := h
  refine ⟨D, hcard, i₁, ht₁, hr₁, fun i hi => ?_⟩
  have h0 := i₀.isLt
  have h1 := i₁.isLt
  have h2 := i.isLt
  have h3 := Fin.val_ne_of_ne hne
  have h4 := Fin.val_ne_of_ne hi
  have : i = i₀ := Fin.ext (by omega)
  subst this
  exact ⟨ht₀, hr₀⟩

variable [Finite G]

theorem routeD_twistedE6_of_phanE6 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {F : PhanE6Frame p f}
    (hF : PhanE6Universal F) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G}
    (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    {z : G} (hz : IsClassicalMember p f K z) (hshape : LocalShapeU p f 5 Ω z)
    (hP1 : LocalOddCentral Ω {z}) {U : Fin 6 → Subgroup G} (hU : IsPhanChainE6 p f U)
    (hUΩ : ∀ i, U i ∈ Ω) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .twistedE6 ∧ D.rank i = 0 := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨M⟩ := F.nonempty_extModel hp2 hq
  obtain ⟨Ψ, hker, -, hV⟩ := hF U hU
  have hadm : StatedLieAdmissible .twistedE6 0 p f := ⟨Fact.out, hf, rfl⟩
  have hadmP : StatedLieAdmissible .PSU 6 p f :=
    ⟨Fact.out, hf, by norm_num, fun h => by simp [Prod.ext_iff] at h⟩
  have hscT : FundamentalSingleClass .twistedE6 (twistedE6Datum p f) :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .twistedE6 0 p f Fact.out trivial
      hadm (by decide) (by decide)
  have hΩψ : ∀ R ∈ fundamentalSubgroups .twistedE6 (twistedE6Datum p f), R.map Ψ ∈ Ω := by
    intro R hR
    obtain ⟨g, hg⟩ := hscT _ (F.V_mem 0) R hR
    rw [hg, ← conjSub_map, hV 0]
    exact hΩ.conjInvariant _ _ (hUΩ 0)
  have hfinY : Finite (modelUniv .PSU 6 p f Fact.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 Fact.out trivial hadmP
  exact routeD_core (t := .twistedE6) (n := 0) (tY := .PSU) (nY := 6) (a := 1) le_rfl trivial hadm
    hscT (by decide) hfinY M hΩ hK hsingle hconn hz hshape.toT hP1 Ψ hker hΩψ

theorem UCtx.five_alternative_E6 {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
    (hPhan : PhanE6 p f) (c : UCtx p f 5 Ω K z) (nd : UNodes c)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    (hshape : LocalShapeU p f 5 Ω z) {β : Subgroup G} (hβ : IsPartnerU c nd β) {wβ : G}
    (hwβ : IsClassicalMember p f β wβ) (hcomm : Commute wβ (nd.w 3)) :
    (∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSU ∧ D.rank i = 8) ∨
      ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .twistedE6 ∧ D.rank i = 0 := by
  obtain ⟨F, hF⟩ := hPhan
  rcases c.five_alternative nd hsingle hconn hshape hβ hwβ hcomm with h | ⟨U, hUΩ, hc, hp⟩
  · exact Or.inl h
  · exact Or.inr (routeD_twistedE6_of_phanE6 c.hp2 c.hq hF c.hΩ c.hK hsingle hconn c.hz hshape
      c.hP1 (isPhanChainE6_of_members c.hq c.hΩ c.hex hUΩ hc hp) hUΩ)

theorem routeD_typeU_five_of_phanE6 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hPhan : PhanE6 p f)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G}
    (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    {z : G} (hz : IsClassicalMember p f K z) (hshape : LocalShapeU p f 5 Ω z)
    (hP1 : LocalOddCentral Ω {z})
    (hcomm : ∀ (c : UCtx p f 5 Ω K z) (nd : UNodes c) {β : Subgroup G} (_ : IsPartnerU c nd β)
      {wβ : G}, IsClassicalMember p f β wβ → Commute wβ (nd.w 3)) :
    (∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSU ∧ D.rank i = 8) ∨
      ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .twistedE6 ∧ D.rank i = 0 := by
  obtain ⟨d⟩ := LocalShapeU.nonempty_dict hp2 (by norm_num) hΩ hK hz hshape
  let c : UCtx p f 5 Ω K z :=
    { hm := by norm_num, hp2 := hp2, hq := hq, hΩ := hΩ, hex := hex, hK := hK, hz := hz,
      hP1 := hP1, d := d, hlift := Or.inl (by norm_num) }
  obtain ⟨nd⟩ := c.nonempty_nodes
  obtain ⟨β, hβ⟩ := c.exists_partnerU nd hsingle
  obtain ⟨wβ, hwβ⟩ := hβ.cl
  exact c.five_alternative_E6 hPhan nd hsingle hconn hshape hβ hwβ (hcomm c nd hβ hwβ)

end Closure

end CFSG.ClassicalInvolution.RouteD
