module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.QuasithinUnique

namespace BadCaseLocal

theorem inv_conj_mem {G : Type*} [Group G] {X : Subgroup G} {n w : G}
    (hn : n ∈ Subgroup.normalizer (X : Set G)) (hw : w ∈ X) : n⁻¹ * w * n ∈ X := by
  have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (X : Set G)).inv_mem hn)) w
  simpa using this.1 hw

end BadCaseLocal

section Abstract

theorem sq_eq_one_of_sylow {X Y : Type*} [Group X] [Finite X] [Group Y] (ψ : X →* Y)
    (P : Sylow 2 X) (hP : ∀ r ∈ (P : Subgroup X), ψ r * ψ r = 1) (g : X) (hg4 : ψ g ^ 4 = 1) :
    ψ g * ψ g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : X →* ↥ψ.range := ψ.rangeRestrict
  have hf : Function.Surjective f := ψ.rangeRestrict_surjective
  have : Finite ↥ψ.range := Finite.of_surjective f hf
  let P' : Sylow 2 ↥ψ.range := P.mapSurjective hf
  let g' : ↥ψ.range := f g
  have hg'4 : g' ^ 4 = 1 := by
    apply Subtype.ext
    simpa [g', f] using hg4
  have hord : orderOf g' ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hg'4)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have hp : IsPGroup 2 ↥(Subgroup.zpowers g') :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨Q₀, hQ₀⟩ := hp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥ψ.range) P' Q₀
  have hmem : g' ∈ (Q₀ : Subgroup ↥ψ.range) := hQ₀ (Subgroup.mem_zpowers g')
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    ← map_inv, MulAut.conj_apply, inv_inv, Sylow.coe_mapSurjective] at hmem
  obtain ⟨r, hr, hrg⟩ := Subgroup.mem_map.1 hmem
  have hr2 : f r * f r = 1 := by
    apply Subtype.ext
    simpa [f] using hP r hr
  have e : g' * g' = c * (f r * f r) * c⁻¹ := by
    rw [hrg]
    group
  have : g' * g' = 1 := by rw [e, hr2]; group
  simpa [g', f] using congrArg Subtype.val this

end Abstract

section Action

variable {G : Type*} [Group G]

@[expose] noncomputable def conjActOn (A N : Subgroup G) (h : N ≤ Subgroup.normalizer (A : Set G)) :
    ↥N →* Equiv.Perm ↥A where
  toFun n :=
    { toFun := fun a => ⟨(n : G) * a * (n : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (h n.2) a).mp a.2⟩
      invFun := fun a => ⟨(n : G)⁻¹ * a * (n : G), BadCaseLocal.inv_conj_mem (h n.2) a.2⟩
      left_inv := fun a => by
        apply Subtype.ext
        show (n : G)⁻¹ * ((n : G) * a * (n : G)⁻¹) * (n : G) = a
        group
      right_inv := fun a => by
        apply Subtype.ext
        show (n : G) * ((n : G)⁻¹ * a * (n : G)) * (n : G)⁻¹ = a
        group }
  map_one' := by
    ext a
    show (1 : G) * a * (1 : G)⁻¹ = a
    group
  map_mul' := fun m n => by
    ext a
    show ((m * n : ↥N) : G) * a * ((m * n : ↥N) : G)⁻¹ =
      (m : G) * ((n : G) * a * (n : G)⁻¹) * (m : G)⁻¹
    simp only [Subgroup.coe_mul]
    group

theorem conjActOn_pow_eq_one_iff (A N : Subgroup G) (h : N ≤ Subgroup.normalizer (A : Set G))
    (n : ↥N) (k : ℕ) :
    conjActOn A N h (n ^ k) = 1 ↔ ∀ a ∈ A, (n : G) ^ k * a * ((n : G) ^ k)⁻¹ = a := by
  constructor
  · intro h1 a ha
    have h2 : ((n ^ k : ↥N) : G) * a * ((n ^ k : ↥N) : G)⁻¹ = a := by
      have := congrArg (fun f : Equiv.Perm ↥A => ((f ⟨a, ha⟩ : ↥A) : G)) h1
      exact this
    simpa using h2
  · intro h1
    ext a
    show ((n ^ k : ↥N) : G) * a * ((n ^ k : ↥N) : G)⁻¹ = a
    simpa using h1 a a.2

variable [Finite G]

theorem sq_centralizes_of_sylow {A N R : Subgroup G} (hAN : N ≤ Subgroup.normalizer (A : Set G))
    (hR : IsSylowTwoOf R N) (hRsq : ∀ r ∈ R, ∀ a ∈ A, r * r * a * (r * r)⁻¹ = a) {g : G}
    (hg : g ∈ N) (hg4 : ∀ a ∈ A, g ^ 4 * a * (g ^ 4)⁻¹ = a) :
    ∀ a ∈ A, g * g * a * (g * g)⁻¹ = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 ↥N :=
    (hR.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hR.1).symm).toSylow hR.2.2
  have hP : ∀ r ∈ (P : Subgroup ↥N), conjActOn A N hAN r * conjActOn A N hAN r = 1 := by
    intro r hr
    have hr' : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
    rw [← map_mul, ← pow_two, conjActOn_pow_eq_one_iff]
    intro a ha
    simpa [pow_two] using hRsq r hr' a ha
  have h4 : conjActOn A N hAN ⟨g, hg⟩ ^ 4 = 1 := by
    rw [← map_pow]
    exact (conjActOn_pow_eq_one_iff A N hAN ⟨g, hg⟩ 4).2 hg4
  have h2 := sq_eq_one_of_sylow (conjActOn A N hAN) P hP ⟨g, hg⟩ h4
  rw [← map_mul, ← pow_two, conjActOn_pow_eq_one_iff] at h2
  intro a ha
  simpa [pow_two] using h2 a ha

end Action

end CFSG.QuasithinUnique
