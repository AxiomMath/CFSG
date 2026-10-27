module

public import CFSG.ClassicalInvolution.AschTight.Sec7Basic

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

@[expose] def EtaExists (Ω : Set (Subgroup G)) : Prop :=
  ∀ S : Sylow 2 G, ∃ η ∈ etaSet Ω (S : Subgroup G),
    ∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η

@[expose] def EtaAbelian (Ω : Set (Subgroup G)) : Prop :=
  ∀ η ∈ etaG Ω, ∀ x ∈ ⨆ U ∈ η, U, ∀ y ∈ ⨆ U ∈ η, U, x * y = y * x

@[expose] def EtaMeets (Ω : Set (Subgroup G)) : Prop :=
  ∀ S : Sylow 2 G, ∀ η ∈ etaG Ω, (∀ V ∈ η, V ≤ (S : Subgroup G)) →
    ∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) → K ⊓ (⨆ V ∈ η, V) ∈ η

@[expose] def etaGIn (Ω : Set (Subgroup G)) (S : Subgroup G) : Set (Set (Subgroup G)) :=
  {γ | γ ∈ etaG Ω ∧ ∀ V ∈ γ, V ≤ S}

@[expose] def etaGenIn (Ω : Set (Subgroup G)) (S : Subgroup G) : Subgroup G :=
  ⨆ U ∈ {U : Subgroup G | ∃ γ ∈ etaGIn Ω S, U ∈ γ}, U

variable {Ω : Set (Subgroup G)}

theorem mem_USet_of_mem_etaG {η : Set (Subgroup G)} (hη : η ∈ etaG Ω) {U : Subgroup G}
    (hU : U ∈ η) : U ∈ USet Ω := by
  obtain ⟨S, hS, -⟩ := hη
  exact (hS.1 hU).1

theorem exists_sylow_of_mem_etaG {η : Set (Subgroup G)} (hη : η ∈ etaG Ω) :
    ∃ S : Sylow 2 G, ∀ U ∈ η, U ≤ (S : Subgroup G) := by
  obtain ⟨S, hS, -⟩ := hη
  exact ⟨S, fun U hU => (hS.1 hU).2⟩

theorem le_etaGenIn {S : Subgroup G} {γ : Set (Subgroup G)} (hγ : γ ∈ etaGIn Ω S)
    {U : Subgroup G} (hU : U ∈ γ) : U ≤ etaGenIn Ω S :=
  le_iSup₂_of_le (f := fun U (_ : U ∈ {U : Subgroup G | ∃ γ ∈ etaGIn Ω S, U ∈ γ}) => U) U
    ⟨γ, hγ, hU⟩ le_rfl

theorem iSup_le_etaGenIn {S : Subgroup G} {γ : Set (Subgroup G)} (hγ : γ ∈ etaGIn Ω S) :
    (⨆ U ∈ γ, U) ≤ etaGenIn Ω S :=
  iSup₂_le fun _ hU => le_etaGenIn hγ hU

theorem etaGenIn_le (S : Subgroup G) : etaGenIn Ω S ≤ S :=
  iSup₂_le fun _ ⟨_, hγ, hU⟩ => hγ.2 _ hU

theorem isPGroup_etaGenIn (S : Sylow 2 G) : IsPGroup 2 (etaGenIn Ω (S : Subgroup G)) :=
  S.isPGroup'.to_le (etaGenIn_le _)

theorem image_conj_mem_etaGIn (hΩ : ConjInvariant Ω) {S : Subgroup G} {γ : Set (Subgroup G)}
    (hγ : γ ∈ etaGIn Ω S) {g : G} (hg : ∀ V ∈ γ, conjSub g V ≤ S) :
    conjSub g '' γ ∈ etaGIn Ω S := by
  refine ⟨etaG_conj hΩ hγ.1 g, ?_⟩
  rintro _ ⟨V, hV, rfl⟩
  exact hg V hV

theorem weaklyClosedIn_etaGenIn [Finite G] (hΩ : ConjInvariant Ω) (S : Subgroup G) :
    WeaklyClosedIn (etaGenIn Ω S) S := by
  intro g hg
  refine conjSub_eq_of_le_self ?_
  rw [conjSub_le_iff]
  refine iSup₂_le fun U ⟨γ, hγ, hU⟩ => ?_
  rw [← conjSub_le_iff]
  have hγ' : conjSub g '' γ ∈ etaGIn Ω S :=
    image_conj_mem_etaGIn hΩ hγ fun V hV => (conjSub_mono (le_etaGenIn hγ hV)).trans hg
  exact le_etaGenIn hγ' ⟨U, hU, rfl⟩

variable {p f : ℕ} [Fact p.Prime]

theorem le_normalizer_of_mem_etaGIn [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (habel : EtaAbelian Ω) (h611 : EtaMeets Ω) {S : Sylow 2 G}
    {γ : Set (Subgroup G)} (hγ : γ ∈ etaGIn Ω (S : Subgroup G)) {U : Subgroup G} (hU : U ∈ γ)
    {K : Subgroup G} (hK : K ∈ Ω) (hKS : 2 < Nat.card ↥(K ⊓ (S : Subgroup G))) :
    U ≤ Subgroup.normalizer (K : Set G) := by
  have hUU := mem_USet_of_mem_etaG hγ.1 hU
  obtain ⟨K', hK', hUK'⟩ := hΩ.exists_member_of_mem_USet hp hUU
  by_cases hKK' : K = K'
  · subst hKK'
    exact hUK'.trans (Subgroup.le_normalizer)
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK
  have hA : K ⊓ (⨆ V ∈ γ, V) ∈ γ := h611 S γ hγ.1 hγ.2 K hK hKS
  have hAU := mem_USet_of_mem_etaG hγ.1 hA
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hp hAU
  have hzA : z ∈ K ⊓ (⨆ V ∈ γ, V) :=
    hz.mem_of_le inf_le_left (hΩ.isPGroup_of_mem_USet hp hAU) (by omega)
  have hzW : z ∈ ⨆ V ∈ γ, V := (Subgroup.mem_inf.mp hzA).2
  obtain ⟨-, -, -, -, -, -, -, -, hU4⟩ := hΩ.exists_data_of_mem_USet hp hUU
  refine hΩ.le_normalizer_of_le_centralizer hp hq hK hK' hKK' hz hUK'
    (hΩ.isPGroup_of_mem_USet hp hUU) (by omega) fun u hu => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact habel γ hγ.1 u (le_iSup₂_of_le (f := fun V (_ : V ∈ γ) => V) U hU le_rfl hu) z hzW

theorem etaGenIn_le_normalizer [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (habel : EtaAbelian Ω) (h611 : EtaMeets Ω) {S : Sylow 2 G}
    {K : Subgroup G} (hK : K ∈ Ω) (hKS : 2 < Nat.card ↥(K ⊓ (S : Subgroup G))) :
    etaGenIn Ω (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G) :=
  iSup₂_le fun _ ⟨_, hγ, hU⟩ => le_normalizer_of_mem_etaGIn hp hq hΩ habel h611 hγ hU hK hKS

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
