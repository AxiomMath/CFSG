module

public import CFSG.HardMathSupport.MathTwE6.ExtraspecialComponentsApply

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B3B

open CFSG.Open CFSG.HardMathSupport.MathTwE6

theorem perm_pow_eq_one {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) {m : ℕ}
    (hm : ∀ k, 0 < k → k ≤ Fintype.card α → k ∣ m) : σ ^ m = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← Equiv.Perm.lcm_cycleType, Multiset.lcm_dvd]
  intro k hk
  have h2 := Equiv.Perm.two_le_of_mem_cycleType hk
  exact hm k (by omega)
    ((Equiv.Perm.le_card_support_of_mem_cycleType hk).trans (Finset.card_le_univ _))

variable {G : Type*} [Group G]

theorem relIndex_dvd_card_mulAut_exp [Finite G] (w : G) (Q L : Subgroup G) (S : Finset (Subgroup G))
    (n m : ℕ) (hm : ∀ k, 0 < k → k ≤ n → k ∣ m)
    (hQL : Q ≤ L) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hS : ∀ g ∈ L, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S)
    (hSn : S.card ≤ n) (h9 : ∀ J ∈ S, 9 ∣ Nat.card J)
    (hCQ : ∀ P : Subgroup G, P ≤ Subgroup.centralizer (Q : Set G) → IsPGroup 3 P →
      Nat.card P ≤ 3)
    (hdich : ∀ N : Subgroup G, N ≤ Q →
      (∀ g ∈ L, g ^ m ∈ Subgroup.normalizer (N : Set G)) →
        N ≤ Subgroup.zpowers w ∨ N = Q)
    (hidx : ¬ (Subgroup.zpowers w).relIndex Q ∣ n.factorial) :
    ∀ J ∈ S, (Subgroup.zpowers w).relIndex Q ∣ Nat.card (MulAut J) := by
  classical
  let act : L → S → S := fun g J => ⟨J.1.map (MulAut.conj (g : G)).toMonoidHom, hS g g.2 J J.2⟩
  have hact_mul : ∀ a b : L, ∀ J : S, act (a * b) J = act a (act b J) := fun a b J =>
    Subtype.ext (by simp only [act, Subgroup.coe_mul]; exact (map_conj_map_conj J.1 b a).symm)
  have hact_one : ∀ J : S, act 1 J = J := fun J =>
    Subtype.ext (by simp only [act, OneMemClass.coe_one]; exact map_conj_one J.1)
  let φ : L →* Equiv.Perm S :=
    { toFun := fun g =>
        { toFun := act g
          invFun := act g⁻¹
          left_inv := fun J => by rw [← hact_mul, inv_mul_cancel, hact_one]
          right_inv := fun J => by rw [← hact_mul, mul_inv_cancel, hact_one] }
      map_one' := Equiv.ext hact_one
      map_mul' := fun a b => Equiv.ext (hact_mul a b) }
  have hφ : ∀ (g : L) (J : S),
      ((φ g J : S) : Subgroup G) = J.1.map (MulAut.conj (g : G)).toMonoidHom :=
    fun _ _ => rfl
  have hcardS : Nat.card (Equiv.Perm S) ∣ n.factorial := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe]
    exact Nat.factorial_dvd_factorial hSn
  have hpow : ∀ g ∈ L, ∀ J ∈ S, J.map (MulAut.conj (g ^ m)).toMonoidHom = J := by
    intro g hg J hJ
    have h1 : φ ⟨g, hg⟩ ^ m = 1 :=
      perm_pow_eq_one _ fun k hk hkS =>
        hm k hk (hkS.trans (by rw [Fintype.card_coe]; exact hSn))
    have h2 := congrArg (fun σ : Equiv.Perm S => ((σ ⟨J, hJ⟩ : S) : Subgroup G)) h1
    simp only [← map_pow, hφ, Equiv.Perm.coe_one, id_eq, SubgroupClass.coe_pow] at h2
    exact h2
  have hpowN : ∀ g ∈ L, g ^ m ∈ L := fun g hg => L.pow_mem hg _
  have hpowJ : ∀ g ∈ L, ∀ J ∈ S, g ^ m ∈ Subgroup.normalizer (J : Set G) :=
    fun g hg J hJ => (map_conj_eq_iff_mem_normalizer J _).1 (hpow g hg J hJ)
  let ψ : Q →* Equiv.Perm S := φ.comp (Subgroup.inclusion hQL)
  set N : Subgroup G := ψ.ker.map Q.subtype with hNdef
  have hmemN : ∀ x : G, x ∈ N ↔ x ∈ Q ∧ ∀ J ∈ S, x ∈ Subgroup.normalizer (J : Set G) := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun J hJ => (map_conj_eq_iff_mem_normalizer J _).1 ?_⟩
      have h2 := congrArg (fun σ : Equiv.Perm S => ((σ ⟨J, hJ⟩ : S) : Subgroup G))
        (MonoidHom.mem_ker.1 hy)
      exact h2
    · rintro ⟨hxQ, hxJ⟩
      refine ⟨⟨x, hxQ⟩, MonoidHom.mem_ker.2 (Equiv.ext fun J => Subtype.ext ?_), rfl⟩
      exact (map_conj_eq_iff_mem_normalizer J.1 x).2 (hxJ J.1 J.2)
  have hNQ : N ≤ Q := Subgroup.map_subtype_le _
  have hNnorm : ∀ g ∈ L, g ^ m ∈ Subgroup.normalizer (N : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hyQ := hLQ (hpowN g hg)
    rw [hmemN, hmemN, Subgroup.mem_normalizer_iff.1 hyQ x]
    refine and_congr_right fun _ => forall₂_congr fun J hJ => ?_
    have hyJ := hpowJ g hg J hJ
    constructor
    · intro hx
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyJ hx) (Subgroup.inv_mem _ hyJ)
    · intro hx
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hyJ) hx) hyJ
      simpa [mul_assoc] using this
  have hQS : ∀ q ∈ Q, ∀ J ∈ S, q ∈ Subgroup.normalizer (J : Set G) := by
    rcases hdich N hNQ hNnorm with hNw | hNQeq
    · exfalso
      apply hidx
      refine (Subgroup.relIndex_dvd_of_le_left Q hNw).trans ?_
      have hsub : N.subgroupOf Q = ψ.ker := by
        rw [hNdef, ← Subgroup.comap_subtype]
        exact Subgroup.comap_map_eq_self_of_injective Q.subtype_injective _
      rw [Subgroup.relIndex, hsub, Subgroup.index_ker]
      exact (Subgroup.card_subgroup_dvd_card _).trans hcardS
    · intro q hq J hJ
      rw [← hNQeq] at hq
      exact ((hmemN q).1 hq).2 J hJ
  intro J hJ
  set K : Subgroup G := Q ⊓ Subgroup.centralizer (J : Set G) with hKdef
  have hKnorm : ∀ g ∈ L, g ^ m ∈ Subgroup.normalizer (K : Set G) := by
    intro g hg
    have h1 := hLQ (hpowN g hg)
    have h2 := mem_normalizer_centralizer (hpowJ g hg J hJ)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [hKdef, Subgroup.mem_inf]
    rw [Subgroup.mem_normalizer_iff.1 h1 x, Subgroup.mem_normalizer_iff.1 h2 x]
  rcases hdich K inf_le_left hKnorm with hKw | hKQ
  · have hQN : Q ≤ Subgroup.normalizer (J : Set G) := fun q hq => hQS q hq J hJ
    let χ : Q →* MulAut J := (normalizerToMulAut J).comp (Subgroup.inclusion hQN)
    have hker : χ.ker = K.subgroupOf Q := by
      ext x
      rw [Subgroup.mem_subgroupOf, hKdef, Subgroup.mem_inf]
      simp only [χ, MonoidHom.mem_ker, MonoidHom.comp_apply]
      rw [← MonoidHom.mem_ker, mem_ker_normalizerToMulAut]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    haveI : Finite (MulAut J) :=
      Finite.of_injective (fun φ : MulAut J => (φ : J → J)) DFunLike.coe_injective
    refine (Subgroup.relIndex_dvd_of_le_left Q hKw).trans ?_
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
    exact Subgroup.card_subgroup_dvd_card _
  · exfalso
    have hJC : J ≤ Subgroup.centralizer (Q : Set G) := by
      rw [← Subgroup.le_centralizer_iff]
      rw [← hKQ]
      exact inf_le_right
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 J))
    have hcard : Nat.card ((P : Subgroup J).map J.subtype) = 3 ^ (Nat.card J).factorization 3 := by
      rw [Subgroup.card_map_of_injective J.subtype_injective, Sylow.card_eq_multiplicity]
    have hf : 2 ≤ (Nat.card J).factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 (by simpa using h9 J hJ)
    have hle := hCQ ((P : Subgroup J).map J.subtype)
      ((Subgroup.map_subtype_le _).trans hJC) (P.isPGroup'.map J.subtype)
    rw [hcard] at hle
    have : 3 ^ 2 ≤ 3 ^ (Nat.card J).factorization 3 := Nat.pow_le_pow_right (by norm_num) hf
    omega

theorem component_relIndex_dvd_card_mulAut_exp [Finite G] (w : G) (X Q L : Subgroup G) (n m : ℕ)
    (hm : ∀ k, 0 < k → k ≤ n → k ∣ m)
    (hQL : Q ≤ L) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hLX : L ≤ Subgroup.normalizer (X : Set G))
    (hCQ : ∀ P : Subgroup G, P ≤ Subgroup.centralizer (Q : Set G) → IsPGroup 3 P →
      Nat.card P ≤ 3)
    (hdich : ∀ N : Subgroup G, N ≤ Q →
      (∀ g ∈ L, g ^ m ∈ Subgroup.normalizer (N : Set G)) →
        N ≤ Subgroup.zpowers w ∨ N = Q)
    (hidx : ¬ (Subgroup.zpowers w).relIndex Q ∣ n.factorial)
    (hG : ¬ 9 ^ (n + 1) ∣ Nat.card G) :
    ∀ J : Subgroup G, IsComponentOf J X → 9 ∣ (Subgroup.center J).index →
      (Subgroup.zpowers w).relIndex Q ∣ Nat.card (MulAut J) := by
  classical
  set S : Finset (Subgroup G) :=
    (Set.toFinite {J : Subgroup G | IsComponentOf J X ∧ 9 ∣ (Subgroup.center J).index}).toFinset
    with hSdef
  have hmemS : ∀ J, J ∈ S ↔ IsComponentOf J X ∧ 9 ∣ (Subgroup.center J).index := fun J => by
    simp [hSdef]
  have hS : ∀ g ∈ L, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S := by
    intro g hg J hJ
    rw [hmemS] at hJ ⊢
    exact ⟨isComponentOf_map_conj_of_mem_normalizer hJ.1 (hLX hg),
      (index_center_map_conj J g).symm ▸ hJ.2⟩
  have hSn : S.card ≤ n := by
    by_contra hlt
    apply hG
    refine (pow_dvd_pow 9 (by omega)).trans (pow_card_dvd_of_commute S 9 ?_ ?_)
    · intro A hA B hB hne a ha b hb
      exact CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne ((hmemS A).1 hA).1
        ((hmemS B).1 hB).1 hne ha hb
    · exact fun J hJ => ((hmemS J).1 hJ).2
  have h9 : ∀ J ∈ S, 9 ∣ Nat.card J := fun J hJ =>
    ((hmemS J).1 hJ).2.trans (Subgroup.index_dvd_card _)
  intro J hJ hJ9
  exact relIndex_dvd_card_mulAut_exp w Q L S n m hm hQL hLQ hS hSn h9 hCQ hdich hidx J
    ((hmemS J).2 ⟨hJ, hJ9⟩)

end CFSG.HardMathSupport.Solomon.Coordinator.B3B
