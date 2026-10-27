module

public import CFSG.ClassicalInvolution.RouteD.G2D4E189Rest
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Edge
public import CFSG.ClassicalInvolution.ModelFacts.G2D4ThreeD4
public import CFSG.ClassicalInvolution.Asc77.AscIH8Thm678

public section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance.Q27

section Sylow

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem isMaxPGroup_of_card_eq {J J' R : Subgroup G} (hcard : Nat.card J = Nat.card J')
    (hRJ' : R ≤ J') (hR : IsPGroup p R)
    (hmax : ∀ T : Subgroup G, T ≤ J' → IsPGroup p T → R ≤ T → T = R) :
    ∀ T : Subgroup G, T ≤ J → IsPGroup p T → R ≤ T → T = R := by
  intro T hTJ hT hRT
  let P' : Sylow p J' :=
    ⟨R.subgroupOf J', hR.comap_subtype, fun {Q} hQ hle => by
      have h1 : R ≤ Q.map J'.subtype := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hRJ']
        exact Subgroup.map_mono hle
      have h2 := hmax (Q.map J'.subtype) (Subgroup.map_subtype_le _) (hQ.map _) h1
      rw [← Subgroup.comap_map_eq_self_of_injective J'.subtype_injective Q, h2]
      rfl⟩
  have hP' : Nat.card (R.subgroupOf J') = p ^ (Nat.card J').factorization p :=
    Sylow.card_eq_multiplicity P'
  have hT' : IsPGroup p ↥(T.subgroupOf J) := hT.comap_subtype
  obtain ⟨P, hTP⟩ := hT'.exists_le_sylow
  have hP : Nat.card P = p ^ (Nat.card J).factorization p := Sylow.card_eq_multiplicity P
  have h1 : Nat.card T = Nat.card (T.subgroupOf J) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTJ).toEquiv.symm
  have h2 : Nat.card R = Nat.card (R.subgroupOf J') :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRJ').toEquiv.symm
  have h3 : Nat.card (T.subgroupOf J) ≤ Nat.card P := Subgroup.card_le_of_le hTP
  have h4 : Nat.card T ≤ Nat.card R := by
    rw [h1, h2, hP', ← hcard]
    exact hP ▸ h3
  exact (Subgroup.eq_of_le_of_card_ge hRT h4).symm

end Sylow

section Transport

variable {Kmod G : Type} [Group Kmod] [Group G] [Finite G]

theorem dEdgeless_of_model (ψ : Kmod →* G) (hinj : Function.Injective ψ)
    (hsurj : Function.Surjective ψ) {cls : Set (Subgroup Kmod)} {Ω : Set (Subgroup G)}
    (hΩ : ∀ L, L ∈ Ω ↔ ∃ R ∈ cls, L = R.map ψ)
    (htrans : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    (core : ∀ Q ∈ cls, ∀ g : Kmod, ∀ R : Subgroup Kmod, R ≤ conjSub g Q → IsPGroup 2 R →
      (∀ T : Subgroup Kmod, T ≤ conjSub g Q → IsPGroup 2 T → R ≤ T → T = R) →
      R ≤ Subgroup.normalizer (Q : Set Kmod) → conjSub g Q = Q) :
    Disconnected.DEdgeless Ω := by
  have key : ∀ K ∈ Ω, ∀ J ∈ Ω, J ∉ omegaNbr Ω K := by
    intro K hK J hJ hnbr
    obtain ⟨-, hne, R, hR, hRJ, hRN⟩ := hnbr
    obtain ⟨J', hJ', hRJ', hR2, hRmax⟩ := mem_RSet_iff.mp hR
    obtain ⟨g', hg'⟩ := htrans J' hJ' J hJ
    have hcard : Nat.card J = Nat.card J' := by
      rw [← hg']
      exact Subgroup.card_map_of_injective (MulAut.conj g').injective
    have hmaxJ := isMaxPGroup_of_card_eq hcard hRJ' hR2 hRmax
    obtain ⟨K₀, hK₀, rfl⟩ := (hΩ K).mp hK
    obtain ⟨J₀, hJ₀, rfl⟩ := (hΩ J).mp hJ
    obtain ⟨g₁, hg₁⟩ := htrans _ hK _ hJ
    obtain ⟨g, rfl⟩ := hsurj g₁
    have hJ₀eq : conjSub g K₀ = J₀ := by
      refine Subgroup.map_injective hinj ?_
      rw [← conjSub_map ψ g K₀]
      exact hg₁
    have hR₀J₀ : R.comap ψ ≤ J₀ := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hRJ (hx : ψ x ∈ R)
      have : y = x := hinj hyx
      rwa [this] at hy
    have hR₀max : ∀ T : Subgroup Kmod, T ≤ conjSub g K₀ → IsPGroup 2 T → R.comap ψ ≤ T →
        T = R.comap ψ := by
      intro T hT hT2 hle
      have h1 : T.map ψ ≤ J₀.map ψ := by
        rw [← hJ₀eq]
        exact Subgroup.map_mono hT
      have h2 : R ≤ T.map ψ := by
        rw [← Subgroup.map_comap_eq_self_of_surjective hsurj R]
        exact Subgroup.map_mono hle
      have h3 := hmaxJ (T.map ψ) h1 (hT2.map ψ) h2
      rw [← Subgroup.comap_map_eq_self_of_injective hinj T, h3]
    have hR₀N : R.comap ψ ≤ Subgroup.normalizer (K₀ : Set Kmod) := by
      intro x hx
      have h1 := hRN (hx : ψ x ∈ R)
      rw [normalizer_map_of_bijective ψ hinj hsurj K₀] at h1
      obtain ⟨n, hn, hnx⟩ := h1
      have : n = x := hinj hnx
      rwa [this] at hn
    have h := core K₀ hK₀ g (R.comap ψ) (hJ₀eq ▸ hR₀J₀) (hR2.comap_of_injective ψ hinj)
      (hJ₀eq ▸ hR₀max) hR₀N
    exact hne (by rw [← hJ₀eq, h])
  intro K hK J hJ hadj
  rcases hadj with h | h
  · exact key K hK J hJ h
  · exact key J hJ K hK h

end Transport

section Twins

variable {Kmod G : Type} [Group Kmod] [Group G]

theorem noTwins_of_model (ψ : Kmod →* G) (hinj : Function.Injective ψ)
    (hsurj : Function.Surjective ψ) {cls : Set (Subgroup Kmod)} {Ω : Set (Subgroup G)}
    (hΩ : ∀ L, L ∈ Ω ↔ ∃ R ∈ cls, L = R.map ψ)
    (htrans : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    (hnt : ∀ R ∈ cls, ∀ c : Kmod, IsUniqueInvolution R c → ∀ g : Kmod,
      IsUniqueInvolution (conjSub g R) c → conjSub g R = R) :
    ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K := by
  intro K hK K' hK'
  obtain ⟨R, hR, rfl⟩ := (hΩ K).mp hK
  obtain ⟨hK'Ω, z, hz, hz'⟩ := hK'
  obtain ⟨g, hg⟩ := htrans _ hK _ hK'Ω
  obtain ⟨g', rfl⟩ := hsurj g
  have h1 : (conjSub g' R).map ψ = K' := by
    rw [← conjSub_map ψ g' R]
    exact hg
  subst h1
  obtain ⟨c, hcz, hc⟩ := isUniqueInvolution_comap hinj hz
  obtain ⟨c', hc'z, hc'⟩ := isUniqueInvolution_comap hinj hz'
  have hcc : c' = c := hinj (hc'z.trans hcz.symm)
  rw [hcc] at hc'
  rw [hnt R hR c hc g' hc']

theorem dEdgelessOrConnected_of_coatom (ψ : Kmod →* G) (hinj : Function.Injective ψ)
    (hsurj : Function.Surjective ψ) {cls : Set (Subgroup Kmod)} {Ω : Set (Subgroup G)}
    (hΩ : ∀ L, L ∈ Ω ↔ ∃ R ∈ cls, L = R.map ψ) (hconj : ConjInvariant Ω)
    (htrans : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    (hcoatom : ∀ R ∈ cls, IsCoatom (Subgroup.normalizer (R : Set Kmod))) :
    Disconnected.DEdgeless Ω ∨ Disconnected.DConnected Ω := by
  have hcoatomG : ∀ K ∈ Ω, IsCoatom (Subgroup.normalizer (K : Set G)) := by
    intro K hK
    obtain ⟨R, hR, rfl⟩ := (hΩ K).mp hK
    rw [normalizer_map_of_bijective ψ hinj hsurj R]
    exact isCoatom_map_of_bijective ψ hinj hsurj (hcoatom R hR)
  exact edgeless_or_connected_of_coatom (r := Disconnected.dAdj Ω) hconj htrans hcoatomG
    (fun g K J h => by
      rcases h with h | h
      · exact Or.inl (omegaNbr_conj hconj h g)
      · exact Or.inr (omegaNbr_conj hconj h g))
    (fun K J h => Disconnected.dAdj_symm h) (fun K J h => Disconnected.ne_of_dAdj h)

end Twins

section Ih8

variable {p f : ℕ} [Fact p.Prime]

@[expose] def TD4MaxNormalizer (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .trialityD4 0 p e → p ≠ 2 →
    ∀ R ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 0 p e Fact.out).D,
      IsCoatom (Subgroup.normalizer (R : Set (modelUniv .trialityD4 0 p e Fact.out).K))

theorem td4MaxNormalizer_of_maxNormalizer (hM : G2D4MaxNormalizer p) : TD4MaxNormalizer p :=
  fun e hadm hp2 R hR => hM .trialityD4 0 e hadm hp2 (Or.inr rfl) R hR

theorem ih8G2D4_of_td4MaxNormalizer (hM : TD4MaxNormalizer p) : Ih8G2D4 p f := by
  intro hp2 hq G _ _ _ Ω hΩ _ htrans t k e hMod ht
  obtain ⟨M⟩ := hMod
  have he : 1 ≤ e := M.admissible.2.1
  have hinj : Function.Injective M.ψ :=
    RouteD.G2D4.injective_of_ker_le_center hp2 ht k he M.ψ M.ker_le_center
  have hsurj : Function.Surjective M.ψ := M.surj
  have hZ : Subgroup.center (modelUniv t k p e Fact.out).K = ⊥ :=
    RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 ht k he
  rcases ht with ht2 | ht2
  · subst ht2
    obtain ⟨hk, -⟩ := M.admissible.2.2
    subst hk
    have hqe : 5 ≤ p ^ e := by
      rcases M.exp_eq with h' | ⟨h', -⟩
      · rw [h']
        exact hq
      · exact absurd h' (by decide)
    refine ⟨noTwins_of_model M.ψ hinj hsurj M.mem_iff htrans fun R hR =>
      noTwins_g2 hp2 he R (M.cls_sub hR), Or.inl ?_⟩
    exact dEdgeless_of_model M.ψ hinj hsurj M.mem_iff htrans fun Q hQ =>
      eq_of_isMaxPGroup_le_normalizer_g2 hp2 hqe M.admissible Q (M.cls_sub hQ)
  · subst ht2
    have hk : k = 0 := M.admissible.2.2
    subst hk
    have hcoatom : ∀ R ∈ M.cls,
        IsCoatom (Subgroup.normalizer (R : Set (modelUniv .trialityD4 0 p e Fact.out).K)) :=
      fun R hR => hM e M.admissible hp2 R (M.cls_sub hR)
    exact ⟨noTwins_of_model M.ψ hinj hsurj M.mem_iff htrans fun R hR c hc g hg =>
      conjSub_eq_of_same_involution hc hg hZ (hcoatom R hR),
      dEdgelessOrConnected_of_coatom M.ψ hinj hsurj M.mem_iff hΩ.conjInvariant htrans hcoatom⟩

theorem noTwinsFund_td4_of_td4MaxNormalizer (hM : TD4MaxNormalizer p) {e : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .trialityD4 0 p e) : NoTwinsFund p e .trialityD4 0 := by
  intro F hF c hc g hg
  exact conjSub_eq_of_same_involution hc hg
    (CFSG.ClassicalInvolution.RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inr rfl) 0
      hadm.2.1)
    (hM e hadm hp2 F hF)

theorem e189ModelAt_td4_of_td4MaxNormalizer (hM : TD4MaxNormalizer p) {e : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .trialityD4 0 p e) : E189ModelAt p e .trialityD4 0 :=
  e189ModelAt_of_noTwinsFund
    (CFSG.ClassicalInvolution.RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inr rfl) 0
      hadm.2.1)
    (noTwinsFund_td4_of_td4MaxNormalizer hM hp2 hadm)

theorem e189Rest_of_td4MaxNormalizer (hM : TD4MaxNormalizer p) : E189Rest p where
  g2 _ hp2 hadm := e189ModelAt_g2_odd hp2 hadm
  td4 _ hp2 hadm := e189ModelAt_td4_of_td4MaxNormalizer hM hp2 hadm

end Ih8

section D4Three

variable {p : ℕ} [Fact p.Prime]

theorem centralizer_isCoatom_td4_of_td4 (hM : TD4MaxNormalizer p) (hp2 : p ≠ 2) {e : ℕ}
    (hadm : StatedLieAdmissible .trialityD4 0 p e)
    {u : (modelUniv .trialityD4 0 p e Fact.out).K} (hu : u * u = 1) (hu1 : u ≠ 1) :
    IsCoatom (Subgroup.centralizer ({u} : Set (modelUniv .trialityD4 0 p e Fact.out).K)) := by
  obtain ⟨R, hR, -, hRu⟩ := exists_perfect_fund_of_involution hp2 hadm hu hu1
  rw [← normalizer_eq_centralizer_of_isCoatom hRu
    (CFSG.ClassicalInvolution.RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inr rfl) 0
      hadm.2.1) (hM e hadm hp2 R hR)]
  exact hM e hadm hp2 R hR

theorem involutionCentralizersGenerate_td4_of_td4 (hM : TD4MaxNormalizer p)
    (hp2 : p ≠ 2) {e : ℕ} (hadm : StatedLieAdmissible .trialityD4 0 p e) :
    InvolutionCentralizersGenerate (modelUniv .trialityD4 0 p e Fact.out).K := by
  intro u₁ u₂ hu₁ hu₂ hu₁1 hu₂1 hne _
  by_contra hS
  set S := Subgroup.centralizer ({u₁} : Set (modelUniv .trialityD4 0 p e Fact.out).K) ⊔
    Subgroup.centralizer ({u₂} : Set (modelUniv .trialityD4 0 p e Fact.out).K) ⊔
    Subgroup.centralizer ({u₁ * u₂} : Set (modelUniv .trialityD4 0 p e Fact.out).K) with hSdef
  have h1 : S = Subgroup.centralizer ({u₁} : Set (modelUniv .trialityD4 0 p e Fact.out).K) :=
    ((centralizer_isCoatom_td4_of_td4 hM hp2 hadm hu₁ hu₁1).le_iff.mp
      ((le_sup_left : _ ≤ _ ⊔ _).trans le_sup_left)).resolve_left hS
  have h2 : S = Subgroup.centralizer ({u₂} : Set (modelUniv .trialityD4 0 p e Fact.out).K) :=
    ((centralizer_isCoatom_td4_of_td4 hM hp2 hadm hu₂ hu₂1).le_iff.mp
      ((le_sup_right : _ ≤ _ ⊔ _).trans le_sup_left)).resolve_left hS
  exact hne (eq_of_centralizer_eq_td4 hp2 hadm hu₁ hu₂ hu₁1 hu₂1 (h1.symm.trans h2))

theorem d4ThreeCentralizerFacts_of_td4MaxNormalizer [Fact (Nat.Prime 3)]
    (hM : TD4MaxNormalizer 3) (hB : TD4ThreeOddCore) :
    CFSG.ClassicalInvolution.Balance.Q27.D4ThreeCentralizerFacts := by
  intro n p e hp hadm he3
  have hn : n = 0 := hadm.2.2
  subst hn
  have hp3 : p = 3 := by
    have he : e ≠ 0 := by
      have := hadm.2.1
      omega
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (he3 ▸ dvd_pow_self p he)
  subst hp3
  exact ⟨hB 0 3 e hp hadm he3,
    involutionCentralizersGenerate_td4_of_td4 hM (by norm_num) hadm⟩

end D4Three

end CFSG.ClassicalInvolution.G2D4Models
