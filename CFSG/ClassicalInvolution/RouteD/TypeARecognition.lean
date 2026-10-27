module

public import CFSG.ClassicalInvolution.RouteD.ConsistencyA
public import CFSG.ClassicalInvolution.RouteD.GenerationA
public import CFSG.ClassicalInvolution.Generic.TypeA

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

section Recognition

variable {K : Type} [Field K]

theorem linearBlockStandardPair_le_sup {X : Type} [Group X] {W U V : Subgroup X}
    (h : LinearBlockStandardPair K W U V) : W ≤ U ⊔ V := by
  obtain ⟨θ, c, hrange, -, hcases⟩ := h
  have hB : (B12 K).map (MulAut.conj c⁻¹).toMonoidHom ⊔ (B23 K).map (MulAut.conj c⁻¹).toMonoidHom =
      ⊤ := by
    rw [← Subgroup.map_sup, WeakCT.B12_sup_B23]
    exact Subgroup.map_top_of_surjective _ (MulEquiv.surjective _)
  have hW : W = ((B12 K).map (MulAut.conj c⁻¹).toMonoidHom).map θ ⊔
      ((B23 K).map (MulAut.conj c⁻¹).toMonoidHom).map θ := by
    rw [← hrange, MonoidHom.range_eq_map, ← hB, Subgroup.map_sup]
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hW, h1, h2]
  · rw [hW, h1, h2, sup_comm]

theorem weakCT_recognition_blocks [Finite K] (p f : ℕ) (hp : p.Prime) (hK : Nat.card K = p ^ f)
    (hq : 4 ≤ p ^ f) {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X] {U : Fin n → Subgroup X}
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair K W (U i) (U j))
    (hgen : ⨆ i, U i = ⊤) :
    ∃ ψ : SL(n + 1, K) →* X, Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center SL(n + 1, K) ∧
      ∀ i : Fin n, (blockSL2 K n i).range.map ψ = U i := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ hq
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨F, hF⟩ := exists_ctFamily_of_pairs hK4 (by omega) hcomm hpair
  have hgen' : ⨆ i, (F.ι i).range = ⊤ := by
    simp only [fun i => (hF i).1]
    exact hgen
  have hnt : ∃ i, ∃ A, F.ι i A ≠ 1 := by
    obtain ⟨s, hs⟩ := exists_unit_ne_one (by omega : 3 ≤ Nat.card K)
    refine ⟨⟨0, by omega⟩, torusHom K s, fun h => hs ?_⟩
    apply torusHom_injective
    rw [map_one]
    exact (hF ⟨0, by omega⟩).2 (h.trans (map_one _).symm)
  obtain ⟨ψ, hψι, hsurj, hker, -⟩ := exists_recognition hn hp hf hK F hgen' hnt
  refine ⟨ψ, hsurj, hker, fun i => ?_⟩
  have : ψ.comp (blockSL2 K n i) = F.ι i := MonoidHom.ext fun A => hψι i A
  rw [← MonoidHom.range_comp, this, (hF i).1]

end Recognition

section Chain

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem exists_psi_of_chain (hq : 4 ≤ p ^ f) {m : ℕ} (hm : 1 ≤ m) {U : Fin (m + 2) → Subgroup G}
    (hcomm : ∀ i j : Fin (m + 2), (i : ℕ) + 1 < j → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin (m + 2), (j : ℕ) = i + 1 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) :
    ∃ ψ : SL(m + 1 + 2, GaloisField p f) →* G,
      ψ.ker ≤ Subgroup.center SL(m + 1 + 2, GaloisField p f) ∧ ψ.range = ⨆ i, U i ∧
      ∀ i : Fin (m + 2), (blockSL2 (GaloisField p f) (m + 2) i).range.map ψ = U i := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  set Gs := ⨆ i, U i with hGs
  have hUle : ∀ i, U i ≤ Gs := fun i => le_iSup U i
  obtain ⟨ψ', hsurj, hker, hblk⟩ := weakCT_recognition_blocks (K := GaloisField p f) p f Fact.out
    hK hq (n := m + 2) (by omega) (U := fun i => (U i).subgroupOf Gs)
    (fun i j hij x hx y hy => Subtype.ext (hcomm i j hij x.1 hx y.1 hy))
    (fun i j hj => by
      obtain ⟨W, hW⟩ := hpair i j hj
      exact ⟨W.subgroupOf Gs, linearBlockStandardPair_subgroupOf
        ((linearBlockStandardPair_le_sup hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
    (iSup_subgroupOf_self U)
  refine ⟨Gs.subtype.comp ψ', ?_, ?_, ?_⟩
  · intro x hx
    have : ψ' x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
    exact hker this
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · intro i
    rw [← Subgroup.map_map (f := ψ') (g := Gs.subtype) , hblk i, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (hUle i)]

end Chain

section Closure

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem typeA_closure [Finite G] {m : ℕ} (hm : 1 ≤ m) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember p f K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeA p f m Ω z)
    (hP1 : LocalOddCentral Ω {z}) (h2 : (2 : GaloisField p f) ≠ 0)
    {ψ : SL(m + 1 + 2, GaloisField p f) →* G}
    (hker : ψ.ker ≤ Subgroup.center SL(m + 1 + 2, GaloisField p f))
    (hΩψ : ∀ R ∈ longRootSet (K := GaloisField p f) (by omega : 2 ≤ m + 1 + 2), R.map ψ ∈ Ω) :
    ∀ N ∈ {L : Subgroup G | ∃ R ∈ longRootSet (K := GaloisField p f)
        (by omega : 2 ≤ m + 1 + 2), L = R.map ψ}, ∀ L ∈ Ω, L ≠ N → Commutes N L →
      L ∈ {L : Subgroup G | ∃ R ∈ longRootSet (K := GaloisField p f)
        (by omega : 2 ≤ m + 1 + 2), L = R.map ψ} := by
  have hk : 2 ≤ m + 1 := by omega
  have hn : 2 ≤ m + 1 + 2 := by omega
  rintro N ⟨R₀, hR₀, rfl⟩ L hL hLN hcomm
  obtain ⟨g₁, rfl⟩ := (mem_longRootSet_iff hn).mp hR₀
  set F := GaloisField p f
  have hN₀Ω : (rootSL2 F hn).map ψ ∈ Ω := hΩψ _ ⟨_, isLongRootSL2_standard hn⟩
  obtain ⟨g₀, hg₀⟩ := hsingle _ hN₀Ω
  have hNeq : ((rootSL2 F hn).map (MulAut.conj g₁).toMonoidHom).map ψ =
      conjSub (ψ g₁) ((rootSL2 F hn).map ψ) := map_map_conj ψ g₁ _
  rw [hNeq] at hLN hcomm
  set L' := conjSub (ψ g₁)⁻¹ L with hL'
  have hL'Ω : L' ∈ Ω := hΩ.conjInvariant _ L hL
  have hLL' : L = conjSub (ψ g₁) L' := (conjSub_conjSub_inv _ L).symm
  have hL'N : L' ≠ (rootSL2 F hn).map ψ := fun e => hLN (by rw [hLL', e])
  have hcomm' : Commutes ((rootSL2 F hn).map ψ) L' := by
    rw [hLL'] at hcomm
    exact (commutes_conjSub_iff _).mp hcomm
  have hxN : g₀ * z * g₀⁻¹ ∈ (rootSL2 F hn).map ψ := by
    rw [hg₀]; exact conj_mem_conjSub hz.mem
  have hL'x : L' ∈ centralizingMembers Ω {g₀ * z * g₀⁻¹} :=
    ⟨hL'Ω, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm' _ hxN y hy).symm⟩
  rw [typeA_centralizingMembers hm hΩ hK hz hshape hP1 h2 hker hΩψ hg₀] at hL'x
  rcases hL'x with h | ⟨R', hR', hRL'⟩
  · exact absurd h hL'N
  · refine ⟨((R'.map (tailBlock F (m + 1))).map (MulAut.conj g₁).toMonoidHom), ?_, ?_⟩
    · exact longRootSet_conjInvariant hn g₁ _ (map_tailBlock_mem_longRootSet h2 hk hR')
    · have hRL'' : (R'.map (tailBlock F (m + 1))).map ψ = L' := by
        rw [Subgroup.map_map]; exact hRL'
      rw [map_map_conj, hRL'']
      exact hLL'

end Closure

section Closing

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem exists_lieSystemData_of_longRootSet (hq : 5 ≤ p ^ f) {k : ℕ} (hk : 2 ≤ k + 1)
    {Ω : Set (Subgroup G)} (ψ : SL(k + 1, GaloisField p f) →* G) (hsurj : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center SL(k + 1, GaloisField p f))
    (hΩ : ∀ L : Subgroup G, L ∈ Ω ↔
      ∃ R ∈ longRootSet (K := GaloisField p f) hk, L = R.map ψ) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSL ∧ D.rank i = k + 1 := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  refine ⟨{
    card := 1
    tag := fun _ => .PSL
    rank := fun _ => k + 1
    exp := fun _ => f
    hom := fun _ => ψ
    isFundTag := fun _ => trivial
    admissible := ?_
    exp_eq := fun _ => Or.inl rfl
    ker_le_center := fun _ => hker
    commute := fun i j h => absurd (Subsingleton.elim i j) h
    generate := ?_
    fundamental := ?_
    meets := ?_ }, rfl, 0, rfl, rfl⟩
  · intro i
    refine ⟨Fact.out, by omega, hk, ?_, ?_⟩
    · simp [Prod.ext_iff]; omega
    · simp [Prod.ext_iff]; omega
  · rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := hsurj x
    exact Subgroup.mem_iSup_of_mem (0 : Fin 1) ⟨y, rfl⟩
  · intro L hL
    obtain ⟨R, hR, rfl⟩ := (hΩ L).mp hL
    exact ⟨0, R, longRootSet_subset_fundamentalSubgroups_psl hk hR, rfl⟩
  · intro i
    refine ⟨rootSL2 (GaloisField p f) hk,
      longRootSet_subset_fundamentalSubgroups_psl hk ⟨_, isLongRootSL2_standard hk⟩, ?_⟩
    exact (hΩ _).mpr ⟨_, ⟨_, isLongRootSL2_standard hk⟩, rfl⟩

end Closing

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem two_ne_zero_galoisField (hp2 : p ≠ 2) : (2 : GaloisField p f) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p f) p 2).1 (by exact_mod_cast h0)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 hdvd)

theorem routeD_typeA_of_chain [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {m : ℕ} (hm : 1 ≤ m)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeA p f m Ω z)
    (hP1 : LocalOddCentral Ω {z}) (U : Fin (m + 2) → Subgroup G) (hUΩ : ∀ i, U i ∈ Ω)
    (hcomm : ∀ i j : Fin (m + 2), (i : ℕ) + 1 < j → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin (m + 2), (j : ℕ) = i + 1 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSL ∧ D.rank i = m + 3 := by
  have hn : 2 ≤ m + 1 + 2 := by omega
  have h2 : (2 : GaloisField p f) ≠ 0 := two_ne_zero_galoisField hp2
  obtain ⟨ψ, hker, hrange, hblk⟩ := exists_psi_of_chain (p := p) (f := f) (by omega) hm hcomm hpair
  set F := GaloisField p f
  have hU0 : (rootSL2 F hn).map ψ = U ⟨0, by omega⟩ := hblk ⟨0, by omega⟩
  have hΩψ : ∀ R ∈ longRootSet (K := F) hn, R.map ψ ∈ Ω := by
    intro R hR
    obtain ⟨g, rfl⟩ := (mem_longRootSet_iff hn).mp hR
    rw [map_map_conj, hU0]
    exact hΩ.conjInvariant _ _ (hUΩ _)
  set 𝔖 : Set (Subgroup G) := {L | ∃ R ∈ longRootSet (K := F) hn, L = R.map ψ} with h𝔖
  have hsub : 𝔖 ⊆ Ω := by
    rintro _ ⟨R, hR, rfl⟩
    exact hΩψ R hR
  have hne : 𝔖.Nonempty := ⟨(rootSL2 F hn).map ψ, _, ⟨_, isLongRootSL2_standard hn⟩, rfl⟩
  have hcl := typeA_closure hm hΩ hK hz hsingle hshape hP1 h2 hker hΩψ
  have hΩsub : Ω ⊆ 𝔖 := subset_of_adj_closed hconn hsub hne hcl
  refine exists_lieSystemData_of_longRootSet (p := p) (f := f) hq hn ψ ?_ hker ?_
  · refine MonoidHom.range_eq_top.mp (eq_top_iff.mpr ?_)
    calc (⊤ : Subgroup G) = ⨆ L ∈ Ω, L := hΩ.generated.symm
      _ ≤ ψ.range := iSup₂_le fun L hL => by
        obtain ⟨R, -, rfl⟩ := hΩsub hL
        exact Subgroup.map_le_range ψ R
  · intro L
    exact ⟨fun hL => hΩsub hL, fun hL => hsub hL⟩

end Main

end CFSG.ClassicalInvolution.RouteD
