module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInputs
public import CFSG.GroupTheory.ThompsonIndexTwo

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.GH74.GLS.Bg.Thompson

variable {G : Type*} [Group G]

theorem isExtremalIn_of_thompson {S : Subgroup G} {b : G} (hb : b ∈ S)
    (h : GH74.GLS.Bg.Thompson.IsExtremalIn 2 S b) : IsExtremalIn S b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hle, hp, hidx⟩ := h
  have hp' : IsPGroup 2
      ↥((S ⊓ centralizer ({b} : Set G)).subgroupOf (centralizer ({b} : Set G))) :=
    IsPGroup.of_equiv hp (Subgroup.subgroupOfEquivOfLe hle).symm
  exact ⟨hb, hp'.toSylow hidx, rfl⟩

theorem mem_of_mem_twoResidualOf_top [Finite G] {N : Subgroup G} (hN : N.Normal)
    (hNp : IsPGroup 2 (G ⧸ N)) {a : G} (ha : a ∈ GorensteinWalter.twoResidualOf (⊤ : Subgroup G)) :
    a ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hNp
  obtain ⟨y, hy, rfl⟩ := ha
  have hsurj : Function.Surjective (⊤ : Subgroup G).subtype := fun g => ⟨⟨g, mem_top g⟩, rfl⟩
  have hmem : N.comap (⊤ : Subgroup G).subtype ∈
      {N' : Subgroup (⊤ : Subgroup G) | N'.Normal ∧ ∃ n : ℕ, N'.index = 2 ^ n} :=
    ⟨hN.comap _, n, by rw [index_comap_of_surjective N hsurj, ← hn]; rfl⟩
  exact mem_comap.mp (sInf_le hmem hy)

theorem goldschmidtTransferInput_holds :
    ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (a : G), a ∈ (S : Subgroup G) →
      orderOf a = 2 →
      (∀ M : Subgroup G, M ≤ S → M.relIndex S = 2 →
        ∃ g : G, g⁻¹ * a * g ∈ M ∧ IsExtremalIn (S : Subgroup G) (g⁻¹ * a * g)) ∨
        a ∉ GorensteinWalter.twoResidualOf (⊤ : Subgroup G) := by
  intro G _ _ S a haS ha2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hall : ∀ M : Subgroup G, M ≤ S → M.relIndex S = 2 →
      ∃ g : G, g⁻¹ * a * g ∈ M ∧ IsExtremalIn (S : Subgroup G) (g⁻¹ * a * g)
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨M, hMS, hMidx, hM⟩ := hall
  obtain ⟨D, hDC, hDp, hDsyl, haD⟩ :=
    exists_sylow_centralizer (p := 2) (u := a) ⟨1, by rw [ha2, pow_one]⟩
  obtain ⟨x, hx⟩ := hDp.nonempty_fixed_point_of_prime_not_dvd_card (G ⧸ (S : Subgroup G))
    (Sylow.not_dvd_index S)
  obtain ⟨ha'S, ha'ext⟩ := extremal_of_fixed S.isPGroup' hDC hDsyl haD hx
  set t : G := x.out with ht
  set a' : G := t⁻¹ * a * t with ha'
  have ha'M : a' ∉ M := fun h => hM t h (isExtremalIn_of_thompson ha'S ha'ext)
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have ha'sq : a' ^ 2 = 1 := by
    calc a' ^ 2 = t⁻¹ * (a * a) * t := by rw [ha', pow_two]; group
      _ = 1 := by rw [haa]; group
  have hn : (M.subgroupOf S).Normal := Subgroup.normal_of_index_eq_two hMidx
  have hQn : ∀ s ∈ (S : Subgroup G), ∀ q ∈ M, s * q * s⁻¹ ∈ M := fun s hs q hq =>
    mem_subgroupOf.1 (hn.conj_mem ⟨q, hMS hq⟩ (mem_subgroupOf.2 hq) ⟨s, hs⟩)
  have hcyc : ∃ c ∈ (S : Subgroup G), ∀ s ∈ (S : Subgroup G), ∃ k : ℤ, (c ^ k)⁻¹ * s ∈ M := by
    refine ⟨a', ha'S, fun s hs => ?_⟩
    by_cases hsM : s ∈ M
    · exact ⟨0, by simpa using hsM⟩
    · exact ⟨1, by simpa using ThompsonIndexTwo.inv_mul_mem_of_not_mem hMidx ha'S hs ha'M hsM⟩
  have hb : ∀ (g : G) (k : ℕ), g⁻¹ * a' ^ (2 * k) * g ∈ (S : Subgroup G) →
      g⁻¹ * a' ^ (2 * k) * g ∈ M := by
    intro g k _
    rw [pow_mul, ha'sq, one_pow, mul_one, inv_mul_cancel]
    exact M.one_mem
  have hc : ∀ g : G, g⁻¹ * a' * g ∈ (S : Subgroup G) →
      GH74.GLS.Bg.Thompson.IsExtremalIn 2 (S : Subgroup G) (g⁻¹ * a' * g) →
        g⁻¹ * a' * g ∈ M ∨ a'⁻¹ * (g⁻¹ * a' * g) ∈ M := by
    intro g hgS _
    by_cases hgM : g⁻¹ * a' * g ∈ M
    · exact Or.inl hgM
    · exact Or.inr (ThompsonIndexTwo.inv_mul_mem_of_not_mem hMidx ha'S hgS ha'M hgM)
  rcases thompson_transfer_1515 (p := 2) S.isPGroup' (Sylow.not_dvd_index S) hQn hcyc ha'S
      ha'M hb hc with ⟨N, hNn, -, hNp, ha'N⟩ | ⟨g, hgM, hgext, -⟩
  · intro haO
    have h1 := hNn.conj_mem a (mem_of_mem_twoResidualOf_top hNn hNp haO) t⁻¹
    rw [inv_inv] at h1
    exact ha'N h1
  · exfalso
    have e : (t * g)⁻¹ * a * (t * g) = g⁻¹ * a' * g := by rw [ha']; group
    exact hM (t * g) (e ▸ hgM) (e ▸ isExtremalIn_of_thompson (hMS hgM) hgext)

end CFSG.ComponentClassification.GrSLit
