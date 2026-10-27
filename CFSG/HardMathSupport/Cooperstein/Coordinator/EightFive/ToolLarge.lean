module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolShape
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolRestrict

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

section RestrictPre

variable {α : Type*}

@[expose] def restrictPre (S : Set α) (R : Subgroup (Perm S)) : Subgroup (Perm α) :=
  (R.comap (restrictSet S)).map (permSetStab S).subtype

theorem mem_restrictPre {S : Set α} {R : Subgroup (Perm S)} {g : Perm α} :
    g ∈ restrictPre S R ↔ ∃ hg : g ∈ permSetStab S, restrictSet S ⟨g, hg⟩ ∈ R := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g'.2, hg'⟩
  · rintro ⟨hg, hR⟩
    exact ⟨⟨g, hg⟩, hR, rfl⟩

theorem restrictPre_le (S : Set α) (R : Subgroup (Perm S)) : restrictPre S R ≤ permSetStab S :=
  Subgroup.map_subtype_le _

theorem permSetStab_compl (S : Set α) : permSetStab Sᶜ = permSetStab S := by
  ext g
  simp only [mem_permSetStab, Set.mem_compl_iff, not_iff_not]

theorem mem_restrictPre_of_fix {S : Set α} {R : Subgroup (Perm S)} {g : Perm α}
    (hg : ∀ x ∈ S, g x = x) : g ∈ restrictPre S R := by
  have hgS : g ∈ permSetStab S := fun x => by
    by_cases hx : x ∈ S
    · rw [hg x hx]
    · refine ⟨fun h => ?_, fun h => absurd h hx⟩
      have := hg _ h
      rw [g.injective this] at h
      exact h
  refine mem_restrictPre.2 ⟨hgS, ?_⟩
  have : restrictSet S ⟨g, hgS⟩ = 1 := Equiv.ext fun x => Subtype.ext (hg x x.2)
  rw [this]
  exact R.one_mem

theorem perm_mul_comm_of_fix {S : Set α} {g h : Perm α} (hg : ∀ x ∈ S, g x = x)
    (hh : ∀ x ∉ S, h x = x) (hgS : g ∈ permSetStab S) (hhS : h ∈ permSetStab S) :
    g * h = h * g := by
  refine Equiv.ext fun x => ?_
  simp only [Perm.mul_apply]
  by_cases hx : x ∈ S
  · rw [hg _ ((hhS x).2 hx), hg x hx]
  · rw [hh x hx, hh _ fun h' => hx ((hgS x).1 h')]

end RestrictPre

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {m n : ℕ} {ψ : ↥H →* Perm (Fin n)}

@[expose] def largeK (ψ : ↥H →* Perm (Fin n)) (ι : Fin m ↪ Fin n)
    (R' : Subgroup (Perm ↥(Set.range ι)ᶜ)) : Subgroup (MulAut V) :=
  preSub ψ (restrictPre (Set.range ι)ᶜ R')

theorem largeK_le (ψ : ↥H →* Perm (Fin n)) (ι : Fin m ↪ Fin n)
    (R' : Subgroup (Perm ↥(Set.range ι)ᶜ)) :
    largeK ψ ι R' ≤ preSub ψ (permSetStab (Set.range ι)) :=
  preSub_mono ((restrictPre_le _ R').trans (permSetStab_compl _).le)

@[expose] noncomputable def largeKappa (ψ : ↥H →* Perm (Fin n)) (ι : Fin m ↪ Fin n)
    (R' : Subgroup (Perm ↥(Set.range ι)ᶜ)) : ↥(largeK ψ ι R') →* Perm (Fin m) :=
  restrictHom ψ ι (largeK ψ ι R') (largeK_le ψ ι R')

@[expose] noncomputable def largeQ (ψ : ↥H →* Perm (Fin n)) (ι : Fin m ↪ Fin n)
    (R' : Subgroup (Perm ↥(Set.range ι)ᶜ)) : Subgroup (MulAut V) :=
  (largeKappa ψ ι R').ker.map (largeK ψ ι R').subtype

variable {ι : Fin m ↪ Fin n} {R' : Subgroup (Perm ↥(Set.range ι)ᶜ)}

theorem largeQ_le : largeQ ψ ι R' ≤ largeK ψ ι R' :=
  Subgroup.map_subtype_le _

theorem mem_largeQ_of_ker {k : ↥(largeK ψ ι R')} (hk : largeKappa ψ ι R' k = 1) :
    (k : MulAut V) ∈ largeQ ψ ι R' :=
  ⟨k, hk, rfl⟩

theorem largeK_le_normalizer :
    largeK ψ ι R' ≤ Subgroup.normalizer (largeQ ψ ι R' : Set (MulAut V)) := by
  have : ((largeQ ψ ι R').subgroupOf (largeK ψ ι R')).Normal := by
    have h : (largeQ ψ ι R').subgroupOf (largeK ψ ι R') = (largeKappa ψ ι R').ker :=
      Subgroup.comap_map_eq_self_of_injective (largeK ψ ι R').subtype_injective _
    rw [h]
    infer_instance
  exact Subgroup.le_normalizer_of_normal_subgroupOf largeQ_le

theorem largeK_le_stabSub (ψ : ↥H →* Perm (Fin n)) (ι : Fin m ↪ Fin n)
    (R' : Subgroup (Perm ↥(Set.range ι)ᶜ)) :
    largeK ψ ι R' ≤ stabSub (fixV (largeQ ψ ι R')) :=
  le_stabSub_fixV largeK_le_normalizer

theorem largeKappa_eq_one_fix {k : ↥(largeK ψ ι R')} (hk : largeKappa ψ ι R' k = 1)
    {w : V} (hw : w ∈ fixV (largeQ ψ ι R')) : (k : MulAut V) w = w :=
  hw _ (mem_largeQ_of_ker hk)

theorem isPGroup_largeQ (hψ : Function.Injective ψ) (hR' : IsPGroup 2 R') :
    IsPGroup 2 (largeQ ψ ι R') := by
  rintro ⟨_, k, hk, rfl⟩
  have hk1 : largeKappa ψ ι R' k = 1 := hk
  set π := ψ (Subgroup.inclusion ((largeK_le ψ ι R').trans preSub_le) k) with hπ
  obtain ⟨hπS, hπR⟩ := mem_restrictPre.1
    ((coe_mem_preSub (ψ := ψ) (x := Subgroup.inclusion ((largeK_le ψ ι R').trans preSub_le) k)).1
      k.2)
  obtain ⟨j, hj⟩ := hR' ⟨_, hπR⟩
  have hj' : (restrictSet (Set.range ι)ᶜ ⟨π, hπS⟩) ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hfixΓ : ∀ i, π (ι i) = ι i := (restrictHom_eq_one_iff k).1 hk1
  have hpow : π ^ 2 ^ j = 1 := by
    refine Equiv.ext fun x => ?_
    rw [Perm.one_apply]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      exact Perm.pow_apply_eq_self_of_apply_eq_self (hfixΓ i) _
    · have h1 := congrArg (fun τ : Perm ↥(Set.range ι)ᶜ => ((τ ⟨x, hx⟩ : ↥(Set.range ι)ᶜ) : Fin n))
        hj'
      simp only [← map_pow] at h1
      exact h1
  refine ⟨j, Subtype.ext ?_⟩
  have h2 : Subgroup.inclusion ((largeK_le ψ ι R').trans preSub_le) k ^ 2 ^ j = 1 :=
    hψ (by rw [map_pow, ← hπ, hpow, map_one])
  have h3 := congrArg (fun x : ↥H => (x : MulAut V)) h2
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h3 ⊢
  exact h3

section Lift

variable (hψ : Function.Injective ψ) (hAlt : alternatingGroup (Fin n) ≤ ψ.range)

include hψ hAlt in
theorem altRho_altLift_mem_largeK (σ : alternatingGroup (Fin m)) :
    altRho hψ hAlt (altLift ι σ) ∈ largeK ψ ι R' :=
  (coe_mem_preSub (x := ⟨_, altRho_mem hψ hAlt _⟩)).2 (by
    rw [apply_altRho]
    exact mem_restrictPre_of_fix fun x hx => altLift_apply_of_notMem ι σ hx)

include hψ hAlt in
theorem commute_altRho_altLift_of_mem_largeQ (σ : alternatingGroup (Fin m)) {q : MulAut V}
    (hq : q ∈ largeQ ψ ι R') : altRho hψ hAlt (altLift ι σ) * q = q * altRho hψ hAlt (altLift ι σ) := by
  obtain ⟨k, hk, rfl⟩ := hq
  have hk1 : largeKappa ψ ι R' k = 1 := hk
  set x : ↥H := ⟨_, altRho_mem hψ hAlt (altLift ι σ)⟩ with hx
  set y := Subgroup.inclusion ((largeK_le ψ ι R').trans preSub_le) k with hy
  have hfix : ∀ z ∈ Set.range ι, ψ y z = z := by
    rintro _ ⟨i, rfl⟩
    exact (restrictHom_eq_one_iff k).1 hk1 i
  have hxy : ψ (x * y) = ψ (y * x) := by
    rw [map_mul, map_mul, hx, apply_altRho]
    exact (perm_mul_comm_of_fix hfix (fun z hz => altLift_apply_of_notMem ι σ hz)
      (apply_mem_permSetStab (hK := largeK_le ψ ι R') k) (altLift_mem_permSetStab ι σ)).symm
  exact congrArg Subtype.val (hψ hxy)

end Lift

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
