module

public import CFSG.ClassicalInvolution.AschTight.Sec71Orbit2
public import CFSG.ClassicalInvolution.AschTight.Sec71Cases
public import CFSG.ClassicalInvolution.AschTight.Sec71Orbit

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W R K T J : Subgroup G} {u r z v t j : G}

theorem mem_normalizer_closure_pair {z j g : G}
    (hz : g * z * g⁻¹ ∈ Subgroup.closure ({z, j} : Set G))
    (hj : g * j * g⁻¹ ∈ Subgroup.closure ({z, j} : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq]
  refine Sec7.conjSub_eq_of_le_self ?_
  rw [conjSub, MonoidHom.map_closure, Set.image_pair, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · simpa using hz
  · simpa using hj

theorem false_of_not_four_dvd (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hd : DData Ω W R K u r z) (hd' : DData Ω W T J v t j)
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hKJ : K ≠ J) (hzj : z ≠ j) {i k : ℤ}
    (hi : r * v * r⁻¹ = v * u ^ i) (hk : t * u * t⁻¹ = u * v ^ k) (hio : Odd i) (hko : Odd k)
    (hbad : ¬ (4 : ℤ) ∣ i * k - 1) (hA : AEmpty Ω K) : False := by
  obtain ⟨hJs, hJn⟩ := case_three_of_odd hp hq hΩ hd hd' hWc hKJ hk hko
  obtain ⟨g, hg, hgK⟩ := hA J hJs hJn z j hd.uinv hd'.uinv
  have hrj : r * j * r⁻¹ = j * z := by
    have := conj_pow_eq (hWc u hd.u_memW v hd'.u_memW) hi (orderOf u / 2)
    rwa [hd.j_eq hΩ hd', hd.z_eq, zpow_eq_self_of_odd hd.uinv.sq hio] at this
  have htz : t * z * t⁻¹ = z * j := by
    rw [conj_z_eq hΩ hd hd' hWc hk, zpow_eq_self_of_odd hd'.uinv.sq hko]
  have hrz : r * z * r⁻¹ = z := hd.uinv.conj_eq (conjSub_eq_self_of_mem hd.r_memK)
  have htj : t * j * t⁻¹ = j := hd'.uinv.conj_eq (conjSub_eq_self_of_mem hd'.r_memK)
  have hzj' : z * j = j * z := hWc z hd.z_memW j hd'.z_memW
  have hZ := fun {x : G} => mem_closure_pair_iff (x := x) hd.uinv.sq hd'.uinv.sq hzj'
  set H₀ := Subgroup.closure ({r, t} : Set G) with hH₀
  have hrH : r ∈ H₀ := Subgroup.subset_closure (by simp)
  have htH : t ∈ H₀ := Subgroup.subset_closure (by simp)
  have hH₀W : H₀ ≤ Subgroup.normalizer (W : Set G) := by
    rw [hH₀, Subgroup.closure_le]
    intro x hx
    rcases hx with h | h
    · subst x
      exact hd.r_normW
    · rw [Set.mem_singleton_iff] at h
      subst x
      exact hd'.r_normW
  have hH₀Z : H₀ ≤ Subgroup.normalizer
      ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) := by
    rw [hH₀, Subgroup.closure_le]
    intro x hx
    rcases hx with h | h
    · subst x
      refine mem_normalizer_closure_pair ?_ ?_
      · rw [hrz, hZ]
        exact Or.inr (Or.inl rfl)
      · rw [hrj, hZ, ← hzj']
        exact Or.inr (Or.inr (Or.inr rfl))
    · rw [Set.mem_singleton_iff] at h
      subst x
      refine mem_normalizer_closure_pair ?_ ?_
      · rw [htz, hZ]
        exact Or.inr (Or.inr (Or.inr rfl))
      · rw [htj, hZ]
        exact Or.inr (Or.inr (Or.inl rfl))
  set 𝒪 : Set (Subgroup G) := {A | ∃ w ∈ H₀, A = conjSub w K} with h𝒪def
  obtain ⟨n, hn⟩ := hd.orderOf_eq
  have hU2 : IsPGroup 2 ↥(Subgroup.zpowers u) :=
    IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have h𝒪 : ∀ A ∈ 𝒪, A ∈ Ω ∧ ∃ zA : G, IsUniqueInvolution A zA ∧
      (zA = z ∨ zA = j ∨ zA = z * j) ∧
      ∃ V : Subgroup G, V ≤ A ∧ V ≤ W ∧ IsPGroup 2 ↥V ∧ 4 ≤ Nat.card V := by
    rintro A ⟨w, hw, rfl⟩
    refine ⟨hΩ.conjInvariant w K hd.memK, w * z * w⁻¹, hd.uinv.conj w, ?_,
      conjSub w (Subgroup.zpowers u), conjSub_mono hd.U_le_K, ?_, isPGroup_conjSub w hU2,
      by rw [natCard_conjSub, Nat.card_zpowers]; exact hd.four_le⟩
    · have hzZ : w * z * w⁻¹ ∈ Subgroup.closure ({z, j} : Set G) :=
        conj_mem_of_mem_normalizer (hH₀Z hw) (Subgroup.subset_closure (by simp))
      rw [hZ] at hzZ
      rcases hzZ with h | h | h | h
      · exact absurd (conj_eq_one_iff.mp h) hd.uinv.ne_one
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rw [← mem_normalizer_iff_conjSub_eq.mp (hH₀W hw)]
      exact conjSub_mono hd.U_le_W
  have h𝒪K : ∀ A ∈ 𝒪, A ∈ Ω ∧ ∃ zA : G, IsUniqueInvolution A zA ∧
      (zA = z ∨ zA = j ∨ zA = j * z) ∧
      ∃ V : Subgroup G, V ≤ A ∧ V ≤ W ∧ IsPGroup 2 ↥V ∧ 4 ≤ Nat.card V := by
    intro A hA
    obtain ⟨h1, zA, h2, h3, h4⟩ := h𝒪 A hA
    exact ⟨h1, zA, h2, by rw [← hzj']; exact h3, h4⟩
  have h𝒪J : ∀ A ∈ 𝒪, A ∈ Ω ∧ ∃ zA : G, IsUniqueInvolution A zA ∧
      (zA = j ∨ zA = z ∨ zA = z * j) ∧
      ∃ V : Subgroup G, V ≤ A ∧ V ≤ W ∧ IsPGroup 2 ↥V ∧ 4 ≤ Nat.card V := by
    intro A hA
    obtain ⟨h1, zA, h2, h3, h4⟩ := h𝒪 A hA
    refine ⟨h1, zA, h2, ?_, h4⟩
    rcases h3 with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have h𝒪r : ∀ A ∈ 𝒪, conjSub r A ∈ 𝒪 := by
    rintro A ⟨w, hw, rfl⟩
    exact ⟨r * w, H₀.mul_mem hrH hw, (conjSub_mul r w K).symm⟩
  have h𝒪t : ∀ A ∈ 𝒪, conjSub t A ∈ 𝒪 := by
    rintro A ⟨w, hw, rfl⟩
    exact ⟨t * w, H₀.mul_mem htH hw, (conjSub_mul t w K).symm⟩
  have hgen : ∀ x ∈ ((K ⊓ Subgroup.normalizer
      ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) : Subgroup G) : Set G) ∪
      (J ⊓ Subgroup.normalizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) :
        Subgroup G), ∀ A ∈ 𝒪, conjSub x A ∈ 𝒪 := by
    intro x hx
    rcases hx with hx | hx
    · exact hd.conjSub_mem_orbit hp hq hΩ hWc hd'.z_memW hd'.uinv.sq hrj h𝒪r h𝒪K hx
    · have hx' : x ∈ J ⊓ Subgroup.normalizer
          ((Subgroup.closure ({j, z} : Set G) : Subgroup G) : Set G) := by
        rw [Set.pair_comm]
        exact hx
      exact hd'.conjSub_mem_orbit hp hq hΩ hWc hd.z_memW hd.uinv.sq htz h𝒪t h𝒪J hx'
  have hpN : ∀ x ∈ pairNormalizers K J z j, ∀ A ∈ 𝒪, conjSub x A ∈ 𝒪 := by
    intro x hx
    rw [pairNormalizers, Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction'' with
    | mem x hx => exact hgen x hx
    | inv_mem x hx =>
      refine hgen x⁻¹ ?_
      rcases hx with hx | hx
      · exact Or.inl (Subgroup.inv_mem _ hx)
      · exact Or.inr (Subgroup.inv_mem _ hx)
    | one =>
      intro A hA
      rwa [conjSub_one]
    | mul x y _ _ hx hy =>
      intro A hA
      rw [conjSub_mul]
      exact hx _ (hy A hA)
  have hJ𝒪 : J ∈ 𝒪 := hgK ▸ hpN g hg K ⟨1, H₀.one_mem, (conjSub_one K).symm⟩
  obtain ⟨w, hw, hwJ⟩ := hJ𝒪
  exact conj_ne_of_quad hΩ hd hd' hWc hzj hi hk hko hbad hw (hH₀W hw) hwJ.symm

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
