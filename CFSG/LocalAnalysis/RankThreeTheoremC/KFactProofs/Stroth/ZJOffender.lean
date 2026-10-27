module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJSetup
public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJ

open CFSG CFSG.Open CFSG.Quasithin Subgroup
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped commutatorElement

section Setup

variable {X : Type} [Group X] [Finite X]

theorem zj_pCore_le_gnC {S : Subgroup X} (hcore : CFSG.pCore 2 X ≤ S)
    (hcent : centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X) :
    CFSG.pCore 2 X ≤ gnC S := by
  intro y hy
  rw [gnC, Subgroup.mem_centralizer_iff]
  intro h hh
  have hh' : h ∈ CFSG.Quasithin.omegaOneCenterOf (CFSG.pCore 2 X) :=
    zjV_le_omegaOneCenter_pCore hcore hcent hh
  have hh2 : h ∈ centralizer (CFSG.pCore 2 X : Set X) :=
    (Subgroup.mem_inf.mp (zj_omegaOneCenter_le_centerOf (CFSG.pCore 2 X) hh')).2
  exact (Subgroup.mem_centralizer_iff.mp hh2 y hy).symm

theorem zj_exists_offender [Nontrivial X] {p : ℕ} {K S : Subgroup X} (hS2 : IsPGroup 2 S)
    (hcore : CFSG.pCore 2 X ≤ S) (hcent : centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X)
    (hchar : ∀ Z : Subgroup X, Z ≤ S → Z ≠ ⊥ → (Z.subgroupOf S).Characteristic →
      ¬ K ≤ normalizer (Z : Set X) ⊔ CFSG.pPrimeCore p X) :
    ∃ A : Subgroup X, IsMaxElemAbelian S A ∧ ¬ A ≤ CFSG.pCore 2 X := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hJQ : thompsonJ S ≤ CFSG.pCore 2 X := by
    unfold thompsonJ
    exact iSup₂_le fun A hA => h A hA
  have hJeq : thompsonJ S = thompsonJ (CFSG.pCore 2 X) := thompsonJ_eq_of_le hJQ hcore
  haveI : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal
  have hJn : (thompsonJ S).Normal := by
    rw [hJeq]
    refine ⟨fun n hn g => ?_⟩
    have h1 := cjSub_thompsonJ (S := CFSG.pCore 2 X) (g := g⁻¹)
      (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; trivial)
    rw [← h1] at hn
    simpa [mem_cjSub] using hn
  refine hchar (thompsonJ S) (thompsonJ_le_self S)
    (CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hS2 (zj_ne_bot_of_pCore_le hcore hcent))
    (CFSG.QuasithinUnique.Setup.characteristic_thompsonJ S) ?_
  rw [Subgroup.normalizer_eq_top_iff.mpr hJn]
  simp

end Setup

section Centralizer

variable {X : Type*} [Group X]

theorem zj_normal_centralizer (N : Subgroup X) [N.Normal] :
    (Subgroup.centralizer (N : Set X)).Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro h hh
    have h' : g⁻¹ * h * g ∈ N := by
      simpa using Subgroup.Normal.conj_mem inferInstance h hh g⁻¹
    have := hx _ h'
    calc h * (g * x * g⁻¹) = g * ((g⁻¹ * h * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * h * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * h := by group⟩

theorem zj_centralizes_of_commutator_ne {G : Type*} [Group G] {Q A : Subgroup G} [Q.Normal]
    (hQ : CFSG.IsQuasisimple ↥Q) (hne : ⁅Q, A⁆ ≠ Q) : ∀ a ∈ A, ∀ q ∈ Q, a * q = q * a := by
  have hMQ : ⁅Q, A⁆ ≤ Q := Subgroup.commutator_le_left Q A
  have hnorm : (⁅Q, A⁆.subgroupOf Q).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (Subgroup.normalizer_commutator_ge_left Q A)
  have hMcent : ∀ m ∈ ⁅Q, A⁆, ∀ q ∈ Q, m * q = q * m := by
    intro m hm q hq
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hnorm with htop | hle
    · exact absurd (le_antisymm hMQ (subgroupOf_eq_top.mp htop)) hne
    · have hmem : (⟨m, hMQ hm⟩ : ↥Q) ∈ ⁅Q, A⁆.subgroupOf Q := mem_subgroupOf.mpr hm
      have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp (hle hmem) ⟨q, hq⟩)
      exact hc.symm
  have hdc : ⁅⁅Q, A⁆, Q⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine commutator_le.mpr fun x hx y hy => ?_
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
    exact hMcent x hx y hy
  have hQA_bot : ⁅Q, A⁆ = ⊥ := CFSG.LocalCores.perfect_double_commutator hQ.1 hdc
  intro a ha q hq
  have hmem : ⁅q, a⁆ ∈ ⁅Q, A⁆ := commutator_mem_commutator hq ha
  rw [hQA_bot, Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at hmem
  exact hmem.symm

end Centralizer

section CentK

variable {X : Type} [Group X] [Finite X]

@[expose] def zjCentK (p : ℕ) (K : Subgroup X) : Subgroup X :=
  (Subgroup.centralizer (↑(K.map (QuotientGroup.mk' (CFSG.pPrimeCore p X))) :
    Set (X ⧸ CFSG.pPrimeCore p X))).comap (QuotientGroup.mk' (CFSG.pPrimeCore p X))

theorem mem_zjCentK {p : ℕ} {K : Subgroup X} {x : X} :
    x ∈ zjCentK p K ↔ ∀ k ∈ K, QuotientGroup.mk' (CFSG.pPrimeCore p X) k *
      QuotientGroup.mk' (CFSG.pPrimeCore p X) x =
      QuotientGroup.mk' (CFSG.pPrimeCore p X) x * QuotientGroup.mk' (CFSG.pPrimeCore p X) k := by
  unfold zjCentK
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    exact h _ (Subgroup.mem_map_of_mem _ hk)
  · rintro h _ ⟨k, hk, rfl⟩
    exact h k hk

instance zjCentK_normal (p : ℕ) (K : Subgroup X) [K.Normal] : (zjCentK p K).Normal := by
  haveI : (K.map (QuotientGroup.mk' (CFSG.pPrimeCore p X))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  haveI := zj_normal_centralizer (K.map (QuotientGroup.mk' (CFSG.pPrimeCore p X)))
  unfold zjCentK
  exact Subgroup.Normal.comap inferInstance _

theorem zj_not_le_zjCentK {p : ℕ} {K : Subgroup X} (hK : CFSG.IsPComponent p K) :
    ¬ K ≤ zjCentK p K := by
  intro hle
  obtain ⟨K₀, hK₀, -, hmap, -⟩ := hK
  haveI := zj_quasisimple_nontrivial hK₀.1
  have hK0bot : K₀ ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K₀).mp inferInstance
  apply hK0bot
  have hperf : ⁅K₀, K₀⁆ = K₀ := Subgroup.isPerfect_iff.mp hK₀.1.1
  rw [← hperf, eq_bot_iff]
  refine commutator_le.mpr fun x hx y hy => ?_
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
  rw [← hmap] at hx hy
  obtain ⟨k, hk, rfl⟩ := hx
  obtain ⟨l, hl, rfl⟩ := hy
  exact mem_zjCentK.mp (hle hl) k hk

theorem zj_zjCentK_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup X} [K.Normal]
    (hK : CFSG.IsPComponent p K) (T : Sylow 2 X) (hKT : K ⊔ (T : Subgroup X) = ⊤) :
    zjCentK p K ≤ CFSG.GH74.GLS.pPrimePCore p X :=
  zj_normal_le_pPrimeP hp hp2 hK T hKT (zj_not_le_zjCentK hK)

theorem zj_commutator_eq_of_not_le_zjCentK {p : ℕ} {K : Subgroup X} [K.Normal]
    (hK : CFSG.IsPComponent p K) {A : Subgroup X} (hA : ¬ A ≤ zjCentK p K) : ⁅K, A⁆ = K := by
  by_contra hne
  apply hA
  obtain ⟨K₀, hK₀, -, hmap, hmin⟩ := hK
  subst hmap
  have hlt : ⁅K, A⁆ < K := lt_of_le_of_ne (Subgroup.commutator_le_left K A) hne
  have hsub : (⁅K, A⁆).IsSubnormal := by
    refine Subgroup.IsSubnormal.trans (Subgroup.commutator_le_left K A) ?_
      (Subgroup.Normal.isSubnormal inferInstance)
    exact (Subgroup.normal_subgroupOf_of_le_normalizer
      (Subgroup.normalizer_commutator_ge_left K A)).isSubnormal
  have hne' := hmin _ hlt hsub
  haveI : (K.map (QuotientGroup.mk' (CFSG.pPrimeCore p X))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hne2 : ⁅K.map (QuotientGroup.mk' (CFSG.pPrimeCore p X)),
      A.map (QuotientGroup.mk' (CFSG.pPrimeCore p X))⁆ ≠
      K.map (QuotientGroup.mk' (CFSG.pPrimeCore p X)) := by
    rw [← Subgroup.map_commutator]
    exact hne'
  have hcen := zj_centralizes_of_commutator_ne hK₀.1 hne2
  intro a ha
  rw [mem_zjCentK]
  intro k hk
  exact (hcen _ (Subgroup.mem_map_of_mem _ ha) _ (Subgroup.mem_map_of_mem _ hk)).symm

theorem zj_commutator_eq_of_not_le_pCore {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup X}
    [K.Normal] (hK : CFSG.IsPComponent p K) (T : Sylow 2 X) (hKT : K ⊔ (T : Subgroup X) = ⊤)
    (h2cl : ∀ T₂ : Sylow 2 (CFSG.pPrimeCore p X), (T₂ : Subgroup (CFSG.pPrimeCore p X)).Normal)
    {A : Subgroup X} (hA2 : IsPGroup 2 A) (hA : ¬ A ≤ CFSG.pCore 2 X) : ⁅K, A⁆ = K := by
  refine zj_commutator_eq_of_not_le_zjCentK hK fun hAle => hA ?_
  intro a ha
  obtain ⟨k, hk⟩ := hA2 ⟨a, ha⟩
  exact zj_two_power_mem_pCore hp hp2 h2cl (zj_zjCentK_le hp hp2 hK T hKT (hAle ha))
    (by simpa using congrArg Subtype.val hk)

end CentK

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJ
