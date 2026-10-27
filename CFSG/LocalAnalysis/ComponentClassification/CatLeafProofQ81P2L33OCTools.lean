module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2Base
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81NoNilp
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Tools

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.OC

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem not_isPGroup_of_fixed_perfect {Y : Type} [Group Y] [Finite Y] {α : MulAut Y}
    (h : ∃ P : Subgroup Y, Group.IsPerfect P ∧ Even (Nat.card P) ∧ ∀ s ∈ P, α s = s) :
    ¬ IsPGroup 2 (↥(fixedPoints α) ⧸ pPrimeCore 2 ↥(fixedPoints α)) := by
  obtain ⟨P, hP, he, hfix⟩ := h
  exact not_isPGroup_of_perfect (fun s hs => mem_fixedPoints.2 (hfix s hs))
    (GSThmB.NoNilp.commutator_self hP) (even_iff_two_dvd.1 he)

theorem not_isPGroup_of_fixed_odd {Y : Type} [Group Y] [Finite Y] {α : MulAut Y}
    (h : ∃ T : Set Y, (∀ t ∈ T, α t = t ∧ Odd (orderOf t)) ∧ 2 ∣ Nat.card (closure T)) :
    ¬ IsPGroup 2 (↥(fixedPoints α) ⧸ pPrimeCore 2 ↥(fixedPoints α)) := by
  obtain ⟨T, hT, h2⟩ := h
  exact not_isPGroup_of_closure_odd (fun t ht => mem_fixedPoints.2 (hT t ht).1)
    (fun t ht => (hT t ht).2) h2

theorem exists_fixed_odd_conj {S : Type*} [Group S] {α β γ : MulAut S}
    (hαβ : α = γ * β * γ⁻¹)
    (h : ∃ T : Set S, (∀ t ∈ T, β t = t ∧ Odd (orderOf t)) ∧ 2 ∣ Nat.card (closure T)) :
    ∃ T : Set S, (∀ t ∈ T, α t = t ∧ Odd (orderOf t)) ∧ 2 ∣ Nat.card (closure T) := by
  obtain ⟨T, hT, h2⟩ := h
  refine ⟨γ.toMonoidHom '' T, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hαβ, MulAut.mul_apply, MulAut.mul_apply]
      change γ (β (γ⁻¹ (γ t))) = γ t
      rw [MulAut.inv_apply_self, (hT t ht).1]
    · change Odd (orderOf (γ t))
      rw [MulEquiv.orderOf_eq]
      exact (hT t ht).2
  · rw [← MonoidHom.map_closure, card_map_of_injective γ.injective]
    exact h2

variable {K : Type*} [Field K] {n : ℕ}

theorem eq_one_of_pow_char {p : ℕ} [Fact p.Prime] [CharP K p] {u : Kˣ} (hu : u ^ p = 1) :
    u = 1 := by
  have h : ((u : K) - 1) ^ p = 0 := by
    rw [sub_pow_char, one_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, sub_self]
  exact Units.ext (sub_eq_zero.1 ((pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).1 h))

theorem elementary_pow_char {p m : ℕ} [CharP K p] {s : SpecialLinearGroup (Fin m) K}
    (hs : s ∈ LinearGroups.elementarySet m K) : s ^ p = 1 := by
  obtain ⟨i, j, hij, c, rfl⟩ := hs
  exact GSThmB.Cent516.transvection_pow_char i j hij c

theorem exists_fixed_odd_of_hom {p : ℕ} [CharP K p] (hp : p.Prime) (hp2 : p ≠ 2)
    {G : Type*} [Group G] {S : Set G} (hS : closure S = ⊤) (hSp : ∀ s ∈ S, s ^ p = 1)
    (ρ : G →* GL (Fin n) K) (α : MulAut (projectiveSL n K))
    (hfix : ∀ (g : G) (hg : (ρ g : Matrix (Fin n) (Fin n) K).det = 1),
      α (proj n K ⟨ρ g, hg⟩) = proj n K ⟨ρ g, hg⟩)
    (x : G) (hx4 : x ^ 4 = 1)
    (hxs : ∀ c : K, (ρ x : Matrix (Fin n) (Fin n) K) ≠ scalar (Fin n) c) :
    ∃ T : Set (projectiveSL n K), (∀ t ∈ T, α t = t ∧ Odd (orderOf t)) ∧
      2 ∣ Nat.card (closure T) := by
  have : Fact p.Prime := ⟨hp⟩
  have hker : closure S ≤ (GeneralLinearGroup.det.comp ρ).ker := by
    rw [closure_le]
    intro s hs
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    refine eq_one_of_pow_char (p := p) ?_
    rw [← map_pow, hSp s hs, map_one]
  have hdet : ∀ g, (ρ g : Matrix (Fin n) (Fin n) K).det = 1 := fun g => by
    have h := hker (hS ▸ mem_top g)
    rw [MonoidHom.mem_ker] at h
    have := congrArg Units.val h
    simpa using this
  let ρ' : G →* SpecialLinearGroup (Fin n) K :=
    { toFun := fun g => ⟨ρ g, hdet g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by
        change ((ρ (g * h) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (ρ g : Matrix (Fin n) (Fin n) K) * (ρ h : Matrix (Fin n) (Fin n) K)
        rw [map_mul, Units.val_mul]) }
  set θ := (proj n K).comp ρ' with hθ
  have hne : θ x ≠ 1 := by
    intro h1
    obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 h1)
    exact hxs c hc
  have h4 : θ x ^ 4 = 1 := by rw [← map_pow, hx4, map_one]
  have h2 : 2 ∣ orderOf (θ x) := by
    have hpos : orderOf (θ x) ≠ 1 := fun h => hne (orderOf_eq_one_iff.1 h)
    rcases (Nat.dvd_prime_pow Nat.prime_two).1
        (show orderOf (θ x) ∣ 2 ^ 2 from orderOf_dvd_of_pow_eq_one h4) with ⟨k, hk, hk'⟩
    interval_cases k
    · exact absurd (by rw [hk']; rfl) hpos
    · rw [hk']; exact ⟨1, rfl⟩
    · rw [hk']; exact ⟨2, rfl⟩
  exact CatLeafProof.Q81P2.exists_odd_of_hom θ (fun g => hfix g (hdet g)) hS
    (fun s hs => Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one (hSp s hs)))
    (CatLeafProof.Q81P2.two_dvd_card_range θ rfl h2)

end CFSG.ComponentClassification.HarrisLit.L33.OC
