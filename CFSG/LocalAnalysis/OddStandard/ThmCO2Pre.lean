module

public import CFSG.GroupTheory.PCore.PrimeCoreImages
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.OddStandard.ThmC.O2

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCore_normal_le (N : Subgroup G) [N.Normal] :
    (pPrimeCore 2 N).map N.subtype ≤ pPrimeCore 2 G := by
  have hK : ((pPrimeCore 2 N).map N.subtype).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hc := (pPrimeCore_characteristic (p := 2) (G := N)).fixed (MulAut.conjNormal g)
    have : ((MulAut.conjNormal g) y : N) ∈ pPrimeCore 2 N := by
      have h2 : y ∈ (pPrimeCore 2 N).comap (MulAut.conjNormal g).toMonoidHom := by
        rw [hc]; exact hy
      exact h2
    exact ⟨_, this, by simp [MulAut.conjNormal_apply]⟩
  refine le_sSup ⟨hK, ?_⟩
  rw [Subgroup.card_map_of_injective N.subtype_injective]
  exact pPrimeCore_coprime_card

theorem pPrimeCore_quot_central (hO : pPrimeCore 2 G = ⊥) (R : Subgroup G) [R.Normal]
    (D : Subgroup R) [D.Normal] (hD : D ≤ center R) (hD2 : IsPGroup 2 D) :
    pPrimeCore 2 (R ⧸ D) = ⊥ := by
  rw [central_p_subgroup_prime_core_quotient D hD hD2]
  have h1 : (pPrimeCore 2 R).map R.subtype = ⊥ := le_bot_iff.1 (hO ▸ pPrimeCore_normal_le R)
  have h2 : pPrimeCore 2 R = ⊥ := by
    have := Subgroup.map_injective (f := R.subtype) R.subtype_injective
    exact this (by rw [h1, Subgroup.map_bot])
  rw [h2, Subgroup.map_bot]

theorem eq_of_central_sylow (hO : pPrimeCore 2 G = ⊥) (N P : Subgroup G) [N.Normal] (hPN : P ≤ N)
    (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.relIndex N)
    (hcent : ∀ x ∈ N, ∀ p ∈ P, x * p = p * x) : N = P := by
  have hle : P.subgroupOf N ≤ center N := by
    intro p hp
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (hcent x.1 x.2 p.1 hp)
  have : (P.subgroupOf N).Normal := normal_of_le_center hle
  have hP2 : IsPGroup 2 (P.subgroupOf N) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm
  have hQ := pPrimeCore_quot_central hO N (P.subgroupOf N) hle hP2
  have hcop : Nat.Coprime 2 (Nat.card (N ⧸ P.subgroupOf N)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hidx
  have htop : (⊤ : Subgroup (N ⧸ P.subgroupOf N)) ≤ pPrimeCore 2 (N ⧸ P.subgroupOf N) :=
    le_sSup ⟨inferInstance, by rw [Subgroup.card_top]; exact hcop⟩
  rw [hQ, top_le_iff] at htop
  have hcard1 : Nat.card (N ⧸ P.subgroupOf N) = 1 := by
    have := congrArg (fun K : Subgroup (N ⧸ P.subgroupOf N) => Nat.card K) htop
    simpa [Subgroup.card_top] using this.symm
  have hidx1 : (P.subgroupOf N).index = 1 := hcard1
  have hP1 : P.subgroupOf N = ⊤ := Subgroup.index_eq_one.1 hidx1
  exact le_antisymm (Subgroup.subgroupOf_eq_top.1 hP1) hPN

theorem sylow_inf_normal_relIndex_odd (S : Sylow 2 G) (N : Subgroup G) [N.Normal] :
    ¬ 2 ∣ (S ⊓ N : Subgroup G).relIndex N := by
  have h1 : (S ⊓ N : Subgroup G).relIndex N * N.relIndex (S ⊔ N : Subgroup G) =
      (S ⊓ N : Subgroup G).relIndex (S ⊔ N : Subgroup G) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right
  have h2 : (S ⊓ N : Subgroup G).relIndex (S : Subgroup G) *
      (S : Subgroup G).relIndex (S ⊔ N : Subgroup G) =
      (S ⊓ N : Subgroup G).relIndex (S ⊔ N : Subgroup G) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left
  have h3 : N.relIndex (S ⊔ N : Subgroup G) = N.relIndex (S : Subgroup G) :=
    Subgroup.relIndex_sup_right (S : Subgroup G) N
  have h4 : (S ⊓ N : Subgroup G).relIndex (S : Subgroup G) = N.relIndex (S : Subgroup G) :=
    Subgroup.inf_relIndex_left (S : Subgroup G) N
  have hne : N.relIndex (S : Subgroup G) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h5 : (S ⊓ N : Subgroup G).relIndex N = (S : Subgroup G).relIndex (S ⊔ N : Subgroup G) := by
    rw [h3, ← h2, h4] at h1
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) (by linarith [h1])
  rw [h5]
  intro hdvd
  have h6 : (S : Subgroup G).relIndex (S ⊔ N : Subgroup G) ∣ (S : Subgroup G).index :=
    Subgroup.relIndex_dvd_index_of_le le_sup_left
  exact S.not_dvd_index (hdvd.trans h6)

omit [Finite G] in
theorem mem_normalizer_iff_map (E : Subgroup G) (h : G) :
    h ∈ normalizer (E : Set G) ↔ E.map (MulAut.conj h).toMonoidHom = E := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h1
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h1 x).1 hx
    · intro hy
      refine ⟨h⁻¹ * y * h, ?_, by simp [MulAut.conj_apply]; group⟩
      have := (h1 (h⁻¹ * y * h)).2
      exact this (by simpa [mul_assoc] using hy)
  · intro h1 x
    constructor
    · intro hx
      rw [← h1]
      exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    · intro hx
      rw [← h1] at hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
      have : y = x := by
        have : h * y * h⁻¹ = h * x * h⁻¹ := by simpa [MulAut.conj_apply] using hyx
        simpa using this
      rwa [← this]

theorem normalizer_of_odd_two (H S E E' : Subgroup G) (hSH : S ≤ H) (hodd : ¬ 2 ∣ S.relIndex H)
    (hSE : S ≤ normalizer (E : Set G))
    (hconj : ∀ h ∈ H, E.map (MulAut.conj h).toMonoidHom = E ∨
      E.map (MulAut.conj h).toMonoidHom = E') :
    H ≤ normalizer (E : Set G) := by
  classical
  set K : Subgroup G := H ⊓ normalizer (E : Set G) with hK
  have hSK : S ≤ K := le_inf hSH hSE
  have hle2 : K.relIndex H ≤ 2 := by
    by_cases hall : ∀ h ∈ H, h ∈ normalizer (E : Set G)
    · have : K.relIndex H = 1 := by
        rw [Subgroup.relIndex_eq_one]
        exact fun h hh => ⟨hh, hall h hh⟩
      omega
    · push Not at hall
      obtain ⟨x, hxH, hxN⟩ := hall
      have hx' : E.map (MulAut.conj x).toMonoidHom = E' := by
        rcases hconj x hxH with h1 | h1
        · exact absurd ((mem_normalizer_iff_map E x).2 h1) hxN
        · exact h1
      have key : ∀ h ∈ H, h ∈ K ∨ x⁻¹ * h ∈ K := by
        intro h hh
        rcases hconj h hh with h1 | h1
        · exact Or.inl ⟨hh, (mem_normalizer_iff_map E h).2 h1⟩
        · right
          refine ⟨H.mul_mem (H.inv_mem hxH) hh, ?_⟩
          refine (mem_normalizer_iff_map E (x⁻¹ * h)).2 ?_
          have : E.map (MulAut.conj (x⁻¹ * h)).toMonoidHom =
              (E.map (MulAut.conj h).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom := by
            rw [Subgroup.map_map]
            congr 1
            ext y
            simp [MulAut.conj_apply, mul_assoc]
          rw [this, h1, ← hx', Subgroup.map_map]
          have : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
              MonoidHom.id G := by
            ext y; simp [MulAut.conj_apply, mul_assoc]
          rw [this, Subgroup.map_id]
      have hsurj : Function.Surjective (fun b : Bool => (QuotientGroup.mk (⟨if b then 1 else x,
          by split_ifs; exact H.one_mem; exact hxH⟩ : H) : H ⧸ K.subgroupOf H)) := by
        intro q
        obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
        rcases key h.1 h.2 with h1 | h1
        · refine ⟨true, ?_⟩
          simp only [ite_true]
          rw [QuotientGroup.eq]
          simpa [Subgroup.mem_subgroupOf] using K.inv_mem h1
        · refine ⟨false, ?_⟩
          simp only [Bool.false_eq_true, ite_false]
          rw [QuotientGroup.eq]
          simpa [Subgroup.mem_subgroupOf] using h1
      have := Nat.card_le_card_of_surjective _ hsurj
      simpa [Subgroup.relIndex, Subgroup.index] using this
  have hdvd : K.relIndex H ∣ S.relIndex H := by
    have := Subgroup.relIndex_mul_relIndex S K H hSK inf_le_left
    exact Dvd.intro_left _ this
  have hodd' : ¬ 2 ∣ K.relIndex H := fun h2 => hodd (h2.trans hdvd)
  have hne : K.relIndex H ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : K.relIndex H = 1 := by omega
  rw [Subgroup.relIndex_eq_one] at h1
  exact fun h hh => (h1 hh).2

end CFSG.OddStandard.ThmC.O2
