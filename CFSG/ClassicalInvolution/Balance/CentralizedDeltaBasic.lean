module

public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.ClassicalInvolution.Balance.CentralizedDeltaTools

open CFSG.Open

section Peel

variable {G : Type*} [Group G]

theorem exists_proper_normal_of_isSubnormal {K X : Subgroup G} (h : IsSubnormal K X)
    (hne : K ≠ X) : ∃ X₁ : Subgroup G, X₁ ≤ X ∧ (X₁.subgroupOf X).Normal ∧ X₁ ≠ X ∧
      IsSubnormal K X₁ := by
  revert hne
  induction h with
  | refl => exact fun hne => absurd rfl hne
  | @step H M K' hHM hN hMK ih =>
    intro hne
    by_cases hMK' : M = K'
    · subst hMK'
      exact ⟨H, hHM, hN, hne, IsSubnormal.refl H⟩
    · obtain ⟨X₁, hX₁le, hX₁N, hX₁ne, hX₁sub⟩ := ih hMK'
      exact ⟨X₁, hX₁le, hX₁N, hX₁ne, IsSubnormal.step hHM hN hX₁sub⟩

end Peel

section PerfectOdd

variable {G : Type*} [Group G] [Finite G]

theorem le_of_perfect_of_forall_mul {K N L : Subgroup G}
    (hNK : N ≤ Subgroup.normalizer (K : Set G)) (hodd : Odd (Nat.card N))
    (hL : commutator L = ⊤) (hdec : ∀ x ∈ L, ∃ k ∈ K, ∃ c ∈ N, x = k * c) : L ≤ K := by
  have hconj : ∀ c ∈ N, ∀ k ∈ K, c * k * c⁻¹ ∈ K := fun c hc k hk =>
    (Subgroup.mem_normalizer_iff.mp (hNK hc) k).mp hk
  let M : Subgroup G :=
    { carrier := {x | ∃ k ∈ K, ∃ c ∈ N, x = k * c}
      mul_mem' := by
        rintro _ _ ⟨k, hk, c, hc, rfl⟩ ⟨k', hk', c', hc', rfl⟩
        refine ⟨k * (c * k' * c⁻¹), K.mul_mem hk (hconj c hc k' hk'), c * c', N.mul_mem hc hc', ?_⟩
        group
      one_mem' := ⟨1, K.one_mem, 1, N.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨k, hk, c, hc, rfl⟩
        refine ⟨c⁻¹ * k⁻¹ * c⁻¹⁻¹, ?_, c⁻¹, N.inv_mem hc, ?_⟩
        · exact hconj c⁻¹ (N.inv_mem hc) k⁻¹ (K.inv_mem hk)
        · group }
  have hKM : K ≤ M := fun k hk => ⟨k, hk, 1, N.one_mem, (mul_one k).symm⟩
  have hNM : N ≤ M := fun c hc => ⟨1, K.one_mem, c, hc, (one_mul c).symm⟩
  have hLM : L ≤ M := fun x hx => hdec x hx
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := by
    rintro _ ⟨k, hk, c, hc, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hk) (hNK hc)
  have hnormal : (K.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr hMK
  let g : ↥N →* ↥M ⧸ K.subgroupOf M := (QuotientGroup.mk' (K.subgroupOf M)).comp
    (Subgroup.inclusion hNM)
  have hg : Function.Surjective g := fun y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf M) y
    obtain ⟨k, hk, c, hc, hx⟩ := x.2
    refine ⟨⟨c, hc⟩, ?_⟩
    change (QuotientGroup.mk' (K.subgroupOf M)) ⟨c, hNM hc⟩ = (QuotientGroup.mk' (K.subgroupOf M)) x
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : ((⟨c, hNM hc⟩ : ↥M)⁻¹ * x : ↥M).1 = c⁻¹ * (k * c) := by
      change c⁻¹ * x.1 = c⁻¹ * (k * c)
      rw [← hx]
    rw [this]
    have h2 := hconj c⁻¹ (N.inv_mem hc) k hk
    simpa [mul_assoc] using h2
  have hoddM : Odd (Nat.card (↥M ⧸ K.subgroupOf M)) :=
    hodd.of_dvd_nat (Subgroup.card_dvd_of_surjective hg)
  let ψ : ↥L →* ↥M ⧸ K.subgroupOf M :=
    (QuotientGroup.mk' (K.subgroupOf M)).comp (Subgroup.inclusion hLM)
  have hLperf : Group.IsPerfect L := ⟨hL⟩
  have hrangeperf : Group.IsPerfect ψ.range :=
    Group.IsPerfect.ofSurjective (f := ψ.rangeRestrict) ψ.rangeRestrict_surjective
  have hrangeodd : Odd (Nat.card ψ.range) :=
    hoddM.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  have hbot := eq_bot_of_perfect_of_odd (Group.IsPerfect.commutator_eq_top (G := ψ.range))
    hrangeodd
  intro l hl
  have h1 : ψ ⟨l, hl⟩ ∈ ψ.range := ⟨⟨l, hl⟩, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  have h2 : (⟨l, hLM hl⟩ : ↥M) ∈ K.subgroupOf M := (QuotientGroup.eq_one_iff _).mp h1
  exact Subgroup.mem_subgroupOf.mp h2

end PerfectOdd

section Normalizes

variable {G : Type*} [Group G] [Finite G]

private theorem oddCoreIn_le_normalizer_aux :
    ∀ (n : ℕ) (K X : Subgroup G), Nat.card X = n → IsSubnormal K X → commutator K = ⊤ →
      oddCoreIn X ≤ Subgroup.normalizer (K : Set G) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K X hn hKX hK
    by_cases hKeq : K = X
    · subst hKeq
      exact (oddCoreIn_le K).trans Subgroup.le_normalizer
    · obtain ⟨X₁, hX₁X, hX₁N, hX₁ne, hX₁sub⟩ := exists_proper_normal_of_isSubnormal hKX hKeq
      have hlt : Nat.card X₁ < n := by
        rw [← hn]
        by_contra hge
        push Not at hge
        exact hX₁ne (Subgroup.eq_of_le_of_card_ge hX₁X hge)
      have hIH : oddCoreIn X₁ ≤ Subgroup.normalizer (K : Set G) := ih _ hlt K X₁ rfl hX₁sub hK
      have hKX₁ : K ≤ X₁ := isSubnormal_le hX₁sub
      have hS : X₁ ⊓ oddCoreIn X ≤ oddCoreIn X₁ := by
        refine le_oddCoreIn_of_normalizes inf_le_left ?_
          ((odd_card_oddCoreIn X).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))
        intro y hy
        rw [Subgroup.mem_normalizer_iff]
        intro s
        have h1 : y * s * y⁻¹ ∈ X₁ ↔ s ∈ X₁ := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hy) s)
          exact this.symm
        have h2 : y * s * y⁻¹ ∈ oddCoreIn X ↔ s ∈ oddCoreIn X := by
          have := (Subgroup.mem_normalizer_iff.mp (normalizer_oddCoreIn X (hX₁X hy)) s)
          exact this.symm
        rw [Subgroup.mem_inf, Subgroup.mem_inf, h1, h2]
      have key : ∀ o ∈ oddCoreIn X, ∀ k ∈ K, o * k * o⁻¹ ∈ K := by
        intro o ho
        have hoX : o ∈ X := oddCoreIn_le X ho
        have hperf : commutator (K.map (MulAut.conj o).toMonoidHom) = ⊤ := by
          have : Group.IsPerfect K := ⟨hK⟩
          exact (Group.IsPerfect.map (MulAut.conj o).toMonoidHom).commutator_eq_top
        have hLK : K.map (MulAut.conj o).toMonoidHom ≤ K := by
          refine le_of_perfect_of_forall_mul hIH (odd_card_oddCoreIn X₁) hperf ?_
          rintro _ ⟨k, hk, rfl⟩
          refine ⟨k, hk, k⁻¹ * (o * k * o⁻¹), ?_, ?_⟩
          swap
          · change o * k * o⁻¹ = k * (k⁻¹ * (o * k * o⁻¹))
            group
          apply hS
          refine ⟨?_, ?_⟩
          · have h1 : o * k * o⁻¹ ∈ X₁ := by
              have hk' : (⟨k, hX₁X (hKX₁ hk)⟩ : ↥X) ∈ X₁.subgroupOf X :=
                Subgroup.mem_subgroupOf.mpr (hKX₁ hk)
              have := hX₁N.conj_mem _ hk' ⟨o, hoX⟩
              simpa [Subgroup.mem_subgroupOf] using this
            exact X₁.mul_mem (X₁.inv_mem (hKX₁ hk)) h1
          · have h1 : k⁻¹ * o * k ∈ oddCoreIn X := by
              have := conj_mem_oddCoreIn (X := X) (hX₁X (hKX₁ (K.inv_mem hk))) ho
              simpa using this
            have h2 : k⁻¹ * (o * k * o⁻¹) = (k⁻¹ * o * k) * o⁻¹ := by group
            rw [h2]
            exact (oddCoreIn X).mul_mem h1 ((oddCoreIn X).inv_mem ho)
        intro k hk
        exact hLK ⟨k, hk, rfl⟩
      intro o ho
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · exact key o ho y
      · intro h
        have := key o⁻¹ ((oddCoreIn X).inv_mem ho) _ h
        simpa [mul_assoc] using this

theorem oddCoreIn_le_normalizer_of_perfect_of_isSubnormal {K X : Subgroup G}
    (hKX : IsSubnormal K X) (hK : commutator K = ⊤) :
    oddCoreIn X ≤ Subgroup.normalizer (K : Set G) :=
  oddCoreIn_le_normalizer_aux _ K X rfl hKX hK

end Normalizes

section Commutator

variable {G : Type*} [Group G] [Finite G]

theorem commutator_mem_oddCoreIn_of_perfect_of_isSubnormal {K X : Subgroup G}
    (hKX : IsSubnormal K X) (hK : commutator K = ⊤) {k o : G} (hk : k ∈ K)
    (ho : o ∈ oddCoreIn X) : k * o * k⁻¹ * o⁻¹ ∈ oddCoreIn K := by
  have hKle : K ≤ X := isSubnormal_le hKX
  have hnorm := oddCoreIn_le_normalizer_of_perfect_of_isSubnormal hKX hK ho
  have h1 : o * k⁻¹ * o⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp hnorm k⁻¹).mp (K.inv_mem hk)
  have h2 : k * o * k⁻¹ ∈ oddCoreIn X := conj_mem_oddCoreIn (hKle hk) ho
  have hS : K ⊓ oddCoreIn X ≤ oddCoreIn K := by
    refine le_oddCoreIn_of_normalizes inf_le_left ?_
      ((odd_card_oddCoreIn X).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro s
    have h1 : y * s * y⁻¹ ∈ K ↔ s ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hy) s).symm
    have h2 : y * s * y⁻¹ ∈ oddCoreIn X ↔ s ∈ oddCoreIn X :=
      (Subgroup.mem_normalizer_iff.mp (normalizer_oddCoreIn X (hKle hy)) s).symm
    rw [Subgroup.mem_inf, Subgroup.mem_inf, h1, h2]
  apply hS
  refine ⟨?_, ?_⟩
  · have : k * o * k⁻¹ * o⁻¹ = k * (o * k⁻¹ * o⁻¹) := by group
    rw [this]
    exact K.mul_mem hk h1
  · exact (oddCoreIn X).mul_mem h2 ((oddCoreIn X).inv_mem ho)

end Commutator

section Inverted

variable {G : Type*} [Group G]

theorem centralizes_of_inverted {z n : G} {J : Subgroup G} (hzJ : ∀ j ∈ J, z * j = j * z)
    (hnJ : ∀ j ∈ J, n * j * n⁻¹ ∈ J) (hinv : z * n * z⁻¹ = n⁻¹) (hodd : Odd (orderOf n)) :
    ∀ j ∈ J, n * j = j * n := by
  have hconj : ∀ j ∈ J, n⁻¹ * j * n = n * j * n⁻¹ := by
    intro j hj
    have hj' : n * j * n⁻¹ ∈ J := hnJ j hj
    have e1 : z * (n * j * n⁻¹) * z⁻¹ = n * j * n⁻¹ := by
      have := hzJ _ hj'
      calc z * (n * j * n⁻¹) * z⁻¹ = (n * j * n⁻¹) * z * z⁻¹ := by rw [this]
        _ = n * j * n⁻¹ := by group
    have e2 : z * (n * j * n⁻¹) * z⁻¹ = (z * n * z⁻¹) * (z * j * z⁻¹) * (z * n⁻¹ * z⁻¹) := by
      group
    have e3 : z * j * z⁻¹ = j := by
      have := hzJ j hj
      calc z * j * z⁻¹ = j * z * z⁻¹ := by rw [this]
        _ = j := by group
    have e4 : z * n⁻¹ * z⁻¹ = n := by
      have : z * n⁻¹ * z⁻¹ = (z * n * z⁻¹)⁻¹ := by group
      rw [this, hinv, inv_inv]
    rw [e2, hinv, e3, e4] at e1
    exact e1
  have hsq : ∀ j ∈ J, n * n * j = j * (n * n) := by
    intro j hj
    have h := hconj _ (hnJ j hj)
    have e5 : n⁻¹ * (n * j * n⁻¹) * n = j := by group
    have e6 : n * (n * j * n⁻¹) * n⁻¹ = n * n * j * (n * n)⁻¹ := by group
    rw [e5, e6] at h
    calc n * n * j = n * n * j * (n * n)⁻¹ * (n * n) := by group
      _ = j * (n * n) := by rw [← h]
  obtain ⟨r, hr⟩ := hodd
  have h1 : n ^ (2 * r + 1) = 1 := by
    rw [← hr]
    exact pow_orderOf_eq_one n
  have hn : n = (n * n) ^ (r + 1) := by
    calc n = n ^ (2 * r + 1) * n := by rw [h1, one_mul]
      _ = n ^ (2 * (r + 1)) := by
          rw [← pow_succ]
          congr 1
      _ = (n * n) ^ (r + 1) := by rw [pow_mul, sq]
  intro j hj
  have hc : Commute (n * n) j := hsq j hj
  have : Commute ((n * n) ^ (r + 1)) j := hc.pow_left (r + 1)
  rw [← hn] at this
  exact this

end Inverted

end CFSG.ClassicalInvolution.Balance.CentralizedDeltaTools
