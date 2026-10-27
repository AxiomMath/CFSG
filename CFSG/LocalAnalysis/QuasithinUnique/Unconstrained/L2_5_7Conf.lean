module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7Setup

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

structure Conf257 (N : Notation25 hs) (n : ℕ) (K₁ K₂ V V' : Subgroup G) (s : G) : Prop where
  setup : Setup257 N n K₁ K₂ V V' s
  center_elem : IsElemAbelian 2 (centerOf N.K)
  geom : RankTwoGeometry257 N.SK V V'
  maxrank : ∀ A : Subgroup G, A ≤ Subgroup.normalizer (N.K : Set G) →
    A ≤ Subgroup.normalizer (N.SK : Set G) → IsElemAbelian 2 A →
      Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (N.K : Set G)) ≤
        Nat.card ↥(A ⊓ Subgroup.centralizer (N.K : Set G)) * Nat.card V ∧
      (Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (N.K : Set G)) =
          Nat.card ↥(A ⊓ Subgroup.centralizer (N.K : Set G)) * Nat.card V →
        A ≤ V ⊔ Subgroup.centralizer (N.K : Set G) ∨
          A ≤ V' ⊔ Subgroup.centralizer (N.K : Set G))
  torus : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (∃ P₀ : Subgroup G, P₀ ≤ N.K ∧ IsElemAbelian p P₀ ∧
        Nat.card P₀ = p ^ 2) ∧
      ∃ h ∈ N.K ⊓ Subgroup.normalizer (N.SK : Set G), (∃ k : ℕ, orderOf h = p ^ k) ∧
        ¬ ⁅V, V'⁆ ≤ Subgroup.centralizer ({h} : Set G)
  autodd : ∀ g ∈ Subgroup.normalizer (N.K : Set G), g ∈ Subgroup.normalizer (N.SK : Set G) →
    Odd (orderOf g) → (∀ s ∈ N.SK, s⁻¹ * g⁻¹ * s * g ∈ V ⊓ V') →
      g ∈ Subgroup.centralizer (N.K : Set G)

namespace Notation25

variable (N : Notation25 hs)

theorem SC_eq_inf_of_K0_eq (h : N.K0 = N.K) :
    N.SC = N.S ⊓ Subgroup.centralizer (N.K : Set G) := by
  unfold SC
  rw [h]

theorem S_le_normalizer_K_of_K0_eq (h : N.K0 = N.K) :
    N.S ≤ Subgroup.normalizer (N.K : Set G) := by
  have := N.S_le_normalizer_K0
  rwa [h] at this

theorem centerOf_K_elemAbelian (hCov : Cover257a) (hlv : Lv256 N) {n : ℕ} {K₁ K₂ V V' : Subgroup G}
    {s : G} (hset : Setup257 N n K₁ K₂ V V' s) : IsElemAbelian 2 (centerOf N.K) := by
  by_contra hZ
  have hSN := N.S_le_normalizer_K_of_K0_eq hset.K0_eq
  have hSC := N.SC_eq_inf_of_K0_eq hset.K0_eq
  have hzS : N.z ∈ centerOf N.S :=
    ⟨N.tuple.center_le N.tuple.z_mem,
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr N.S_le_T) N.tuple.z_mem.2⟩
  have hZSC : ∀ w ∈ centerOf N.S, w ∈ N.SC := by
    intro w hw
    rw [hSC]
    refine ⟨hw.1, ?_⟩
    have := hCov G N.K N.SK n hset.quasi hset.model hset.list N.SK_sylow hZ w (hSN hw.1)
      (fun y hy => (Subgroup.mem_centralizer_iff.mp hw.2 y (L257.SK_le_S N hy)).symm)
    exact this
  have hxz : N.x * N.z * N.x⁻¹ ∈ centerOf N.S := by
    refine ⟨L257.x_conj_S N hzS.1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : N.x⁻¹ * y * N.x ∈ N.S := L257.x_conj_S' N hy
    have hc := Subgroup.mem_centralizer_iff.mp hzS.2 _ hy'
    calc y * (N.x * N.z * N.x⁻¹) = N.x * ((N.x⁻¹ * y * N.x) * N.z) * N.x⁻¹ := by group
      _ = N.x * (N.z * (N.x⁻¹ * y * N.x)) * N.x⁻¹ := by rw [hc]
      _ = N.x * N.z * N.x⁻¹ * y := by group
  have hz1 : N.z ∈ N.SC ⊓ CFSG.conjugate N.SC N.x :=
    ⟨hZSC _ hzS, (CFSG.QuasithinUnique.mem_conjugate_iff).mpr (hZSC _ hxz)⟩
  rw [hlv.concl255.1] at hz1
  exact N.tuple.z_ne_one (Subgroup.mem_bot.mp hz1)

end Notation25

theorem Notation25.conf257 (N : Notation25 hs) (hRB : RankTwoBorelFacts) (hNI : NonIso257)
    (h3 : Id2519.Prop121Three) (hGeom : RankTwoGeom257) (hMax : RankTwoMaxRank257)
    (hCov : Cover257a) (hTor : RankTwoTorus257) (hAut : AutOdd257) (hlv : Lv256 N) {n : ℕ}
    (hn : IsRank2Model257 N.K n) :
    ∃ K₁ K₂ V V' : Subgroup G, ∃ s : G, Conf257 N n K₁ K₂ V V' s := by
  obtain ⟨K₁, K₂, s, hset⟩ := N.setup257 hRB hNI h3 hlv hn
  have hZ := N.centerOf_K_elemAbelian hCov hlv hset
  refine ⟨K₁, K₂, pCoreOf 2 K₁, pCoreOf 2 K₂, s, hset, hZ, ?_, ?_, ?_, ?_⟩
  · exact hGeom G N.K N.SK K₁ K₂ _ _ n hset.quasi hn hset.list hset.pair rfl rfl hZ
  · intro A hAK hAP hA
    exact hMax G N.K N.SK K₁ K₂ _ _ n hset.quasi hn hset.list hset.pair rfl rfl hZ A hAK hAP hA
  · exact hTor G N.K N.SK K₁ K₂ _ _ n hset.quasi hn hset.list hset.pair rfl rfl hZ
  · intro g hgK hgP hg hcomm
    exact hAut G N.K N.SK K₁ K₂ _ _ n hset.quasi hn hset.list hset.pair rfl rfl hZ g hgK hgP hg
      hcomm

end CFSG.QuasithinUnique
