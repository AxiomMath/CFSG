module

public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortAdjoint
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open scoped commutatorElement
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.CurtisTits
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def excTag : StatedLieTag → Tag
  | .F4 => .F4
  | .E6 => .E6
  | .E7 => .E7
  | _ => .E8

@[expose] noncomputable def excEmbed (t : StatedLieTag) (p e : ℕ) [Fact p.Prime] [NeZero e] :
    (Generic.modelUniv t 0 p e Fact.out).K →* ModGL (excTag t) (GaloisField p e) :=
  match t with
  | .F4 => (adjointGroup .F4 (GaloisField p e)).subtype
  | .E6 => (adjointGroup .E6 (GaloisField p e)).subtype.comp (e6Isogeny (GaloisField p e))
  | .E7 => (adjointGroup .E7 (GaloisField p e)).subtype.comp (e7Isogeny (GaloisField p e))
  | .E8 => (adjointGroup .E8 (GaloisField p e)).subtype
  | _ => 1

@[expose] noncomputable def excSignDiag (τ : Tag) (k : Type) [Field k] : Subgroup (ModGL τ k) where
  carrier := {y | ∃ b : Fin τ.rank → kˣ, (∀ i, b i = 1 ∨ b i = -1) ∧ y = rootDiagUnit τ b}
  mul_mem' := by
    rintro _ _ ⟨b, hb, rfl⟩ ⟨b', hb', rfl⟩
    refine ⟨b * b', fun i => ?_, (rootDiagUnit_mul b b').symm⟩
    rcases hb i with h | h <;> rcases hb' i with h' | h' <;> simp [h, h']
  one_mem' := ⟨1, fun _ => Or.inl rfl, rootDiagUnit_one.symm⟩
  inv_mem' := by
    rintro _ ⟨b, hb, rfl⟩
    refine ⟨b⁻¹, fun i => ?_, (rootDiagUnit_inv b).symm⟩
    rcases hb i with h | h <;> simp [h]

@[expose] noncomputable def excSignGroup (t : StatedLieTag) (p e : ℕ) [Fact p.Prime] [NeZero e] :
    Subgroup (Generic.modelUniv t 0 p e Fact.out).K :=
  (excSignDiag (excTag t) (GaloisField p e)).comap (excEmbed t p e)

variable {p e : ℕ} [Fact p.Prime] [NeZero e]

theorem mem_excSignGroup {t : StatedLieTag} {u : (Generic.modelUniv t 0 p e Fact.out).K} :
    u ∈ excSignGroup t p e ↔ ∃ b : Fin (excTag t).rank → (GaloisField p e)ˣ,
      (∀ i, b i = 1 ∨ b i = -1) ∧ excEmbed t p e u = rootDiagUnit (excTag t) b :=
  Iff.rfl

section Commute

theorem central_conj {G : Type*} [Group G] {z : G} (hz : z ∈ Subgroup.center G) (x : G) :
    z * x * z⁻¹ = x := by
  have := (Subgroup.mem_center_iff.1 hz x).symm
  rw [this, mul_inv_cancel_right]

theorem conj_central {G : Type*} [Group G] {z : G} (hz : z ∈ Subgroup.center G) (x : G) :
    x * z * x⁻¹ = z := by
  have := Subgroup.mem_center_iff.1 hz x
  rw [this, mul_inv_cancel_right]

theorem commutator_central_mul {G : Type*} [Group G] {z w a b : G} (hz : z ∈ Subgroup.center G)
    (hw : w ∈ Subgroup.center G) : ⁅z * a, w * b⁆ = ⁅a, b⁆ := by
  have h1 : ⁅z * a, w * b⁆ = (z * (a * (w * b) * a⁻¹) * z⁻¹) * (b⁻¹ * w⁻¹) := by
    simp only [commutatorElement_def, mul_inv_rev]
    group
  have h2 : a * (w * b) * a⁻¹ = w * (a * b * a⁻¹) := by
    have := conj_central hw a
    calc a * (w * b) * a⁻¹ = (a * w * a⁻¹) * (a * b * a⁻¹) := by group
      _ = w * (a * b * a⁻¹) := by rw [this]
  rw [h1, central_conj hz, h2]
  have h3 : w * (a * b * a⁻¹) * (b⁻¹ * w⁻¹) = w * ⁅a, b⁆ * w⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [h3, central_conj hw]

theorem commute_of_commutator_central {G : Type*} [Group G] (R : Subgroup G) (hR : R ≤ ⁅R, R⁆)
    (u : G) (hu : ∀ r ∈ R, u * r * u⁻¹ * r⁻¹ ∈ Subgroup.center G) : ∀ r ∈ R, u * r = r * u := by
  have hcomm : ⁅R, R⁆ ≤ Subgroup.centralizer {u} := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hza := hu a ha
    have hzb := hu b hb
    have ea : h * a * h⁻¹ = (h * a * h⁻¹ * a⁻¹) * a := by group
    have eb : h * b * h⁻¹ = (h * b * h⁻¹ * b⁻¹) * b := by group
    have key : h * ⁅a, b⁆ * h⁻¹ = ⁅a, b⁆ := by
      rw [conjugate_commutatorElement, ea, eb]
      exact commutator_central_mul hza hzb
    calc h * ⁅a, b⁆ = (h * ⁅a, b⁆ * h⁻¹) * h := by group
      _ = ⁅a, b⁆ * h := by rw [key]
  intro r hr
  exact Subgroup.mem_centralizer_iff.1 (hcomm (hR hr)) u (Set.mem_singleton u)

variable {τ : Tag} {K : Type} [Field K]

theorem rootDiagUnit_commute_rankOne (b : Fin τ.rank → Kˣ) (i : Fin τ.rank) (hi : b i = 1)
    {r : adjointGroup τ K} (hr : r ∈ rankOne (rootGroup (rootOperatorFamily τ) K) i) :
    rootDiagUnit τ b * (r : ModGL τ K) = (r : ModGL τ K) * rootDiagUnit τ b := by
  have hS : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → rootChar b γ = 1 →
      rootGroup (rootOperatorFamily τ) K γ ≤
        (Subgroup.centralizer {rootDiagUnit τ b}).comap (adjointGroup τ K).subtype := by
    intro γ hγ hχ g hg
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ g).1 hg
    have h := rootDiagAut_xPar (K := K) b hγ c
    rw [hχ, Units.val_one, one_mul] at h
    have h2 := congrArg (fun x : adjointGroup τ K => (x : ModGL τ K)) h
    simp only [coe_rootDiagAut] at h2
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro d hd
    rw [Set.mem_singleton_iff] at hd
    subst hd
    change rootDiagUnit τ b * _ = _ * rootDiagUnit τ b
    calc rootDiagUnit τ b * ((xPar (rootOperatorFamily τ) γ c : adjointGroup τ K) : ModGL τ K)
        = (rootDiagUnit τ b * ((xPar (rootOperatorFamily τ) γ c : adjointGroup τ K) : ModGL τ K) *
            (rootDiagUnit τ b)⁻¹) * rootDiagUnit τ b := by group
      _ = _ := by rw [h2]; rfl
  have hle : rankOne (rootGroup (rootOperatorFamily τ) K) i ≤
      (Subgroup.centralizer {rootDiagUnit τ b}).comap (adjointGroup τ K).subtype :=
    sup_le (hS _ (isRoot_single τ i) (by rw [rootChar_single_eq, hi]))
      (hS _ (isRoot_neg_single τ i) (by rw [rootChar_neg_eq_inv, rootChar_single_eq, hi]; simp))
  have := Subgroup.mem_centralizer_iff.1 (hle hr) (rootDiagUnit τ b) (Set.mem_singleton _)
  exact this

end Commute


section Transfer

variable {τ : Tag} {K : Type} [Field K] {G : Type} [Group G]

theorem commute_rankOne_of_isogeny (θ : G →* adjointGroup τ K) (hker : θ.ker ≤ Subgroup.center G)
    (X : (Fin τ.rank → ℤ) → Subgroup G)
    (hX : ∀ γ, IsRoot τ γ → (X γ).map θ = rootGroup (rootOperatorFamily τ) K γ) (i : Fin τ.rank)
    (hperf : rankOne X i ≤ ⁅rankOne X i, rankOne X i⁆) {u : G} {b : Fin τ.rank → Kˣ}
    (hu : ((θ u : adjointGroup τ K) : ModGL τ K) = rootDiagUnit τ b) (hi : b i = 1) :
    ∀ r ∈ rankOne X i, u * r = r * u := by
  refine commute_of_commutator_central (rankOne X i) hperf u fun r hr => hker ?_
  have hmap : (rankOne X i).map θ = rankOne (rootGroup (rootOperatorFamily τ) K) i := by
    unfold rankOne
    rw [Subgroup.map_sup, hX _ (isRoot_single τ i), hX _ (isRoot_neg_single τ i)]
  have hr' : θ r ∈ rankOne (rootGroup (rootOperatorFamily τ) K) i := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem θ hr
  have hc := rootDiagUnit_commute_rankOne (K := K) b i hi hr'
  rw [← hu] at hc
  have h1 : θ u * θ r = θ r * θ u := Subtype.ext hc
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
  group

end Transfer

section Tags

variable {p e : ℕ} [Fact p.Prime] [NeZero e]

omit [NeZero e] in
theorem excRank_eq {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .F4) :
    (Generic.modelUniv t 0 p e Fact.out).D.rank = (excTag t).rank := by
  rcases ht with rfl | rfl | rfl | rfl <;> rfl

theorem commute_rankOne_of_excEmbed_eq (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) {t : StatedLieTag}
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .F4) (hadm : StatedLieAdmissible t 0 p e)
    {u : (Generic.modelUniv t 0 p e Fact.out).K} {b : Fin (excTag t).rank → (GaloisField p e)ˣ}
    (hu : excEmbed t p e u = rootDiagUnit (excTag t) b)
    (k : Fin (Generic.modelUniv t 0 p e Fact.out).D.rank)
    (hk : b (Fin.cast (excRank_eq ht) k) = 1) :
    ∀ r ∈ rankOne (Generic.modelUniv t 0 p e Fact.out).D.rootGroup k, u * r = r * u := by
  have h4 : 4 ≤ p ^ e := by omega
  have hperf : ∀ R ∈ fundamentalSubgroups t (Generic.modelUniv t 0 p e Fact.out).D,
      R ≤ ⁅R, R⁆ := fun R hR =>
    fundPerfect_core t 0 p e hp2 (by rcases ht with rfl | rfl | rfl | rfl <;> trivial) hadm h4 R hR
  rcases ht with rfl | rfl | rfl | rfl
  ·
    have hlong := isLongestRoot_single .E6 0 p e Fact.out trivial hadm k trivial
    refine commute_rankOne_of_isogeny (e6Isogeny (GaloisField p e))
      (ker_le_center_of_isQuasisimple (isQuasisimple_e6 (GaloisField p e))
        (e6Isogeny_ne_one (GaloisField p e)))
      (e6Datum (GaloisField p e)).rootGroup (fun γ hγ => map_e6Isogeny_rootGroup _ hγ) k
      (hperf _ ⟨1, Pi.single k 1, Or.inl hlong, (conjSub_one _).symm⟩) hu hk
  ·
    have hlong := isLongestRoot_single .E7 0 p e Fact.out trivial hadm k trivial
    refine commute_rankOne_of_isogeny (e7Isogeny (GaloisField p e))
      (ker_le_center_of_isQuasisimple (isQuasisimple_e7 (GaloisField p e))
        (exists_e7Isogeny_ne_one (GaloisField p e)))
      (e7Datum (GaloisField p e)).rootGroup (fun γ hγ => map_e7Isogeny_rootGroup _ hγ) k
      (hperf _ ⟨1, Pi.single k 1, Or.inl hlong, (conjSub_one _).symm⟩) hu hk
  ·
    intro r hr
    exact Subtype.ext (by
      have := rootDiagUnit_commute_rankOne (K := GaloisField p e) b k hk hr
      rw [← hu] at this
      exact this)
  ·
    intro r hr
    exact Subtype.ext (by
      have := rootDiagUnit_commute_rankOne (K := GaloisField p e) b k hk hr
      rw [← hu] at this
      exact this)

end Tags

end CFSG.ClassicalInvolution.ModelFacts
