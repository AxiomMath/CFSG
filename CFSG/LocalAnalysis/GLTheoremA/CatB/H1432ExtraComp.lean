module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.ExpVariant

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420.SporD4

open CFSG.Open CFSG.HardMathSupport.MathTwE6
open CFSG.HardMathSupport.Solomon.Coordinator.B3B (perm_pow_eq_one)

variable {G : Type*} [Group G]

theorem normalizes_of_dich [Finite G] (w : G) (Q L : Subgroup G) (S : Finset (Subgroup G))
    (n m : ℕ) (hm : ∀ k, 0 < k → k ≤ n → k ∣ m)
    (hQL : Q ≤ L) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hS : ∀ g ∈ L, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S)
    (hSn : S.card ≤ n)
    (hdich : ∀ N : Subgroup G, N ≤ Q →
      (∀ g ∈ L, g ^ m ∈ Subgroup.normalizer (N : Set G)) →
        N ≤ Subgroup.zpowers w ∨ N = Q)
    (hidx : ¬ (Subgroup.zpowers w).relIndex Q ∣ n.factorial) :
    (∀ g ∈ L, ∀ J ∈ S, g ^ m ∈ Subgroup.normalizer (J : Set G)) ∧
      ∀ q ∈ Q, ∀ J ∈ S, q ∈ Subgroup.normalizer (J : Set G) := by
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
  refine ⟨hpowJ, ?_⟩
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

theorem factorization_le_of_dvd {a b : ℕ} (p : ℕ) (hb : b ≠ 0) (h : a ∣ b) :
    a.factorization p ≤ b.factorization p :=
  (Nat.factorization_le_iff_dvd (ne_zero_of_dvd_ne_zero hb h) hb).2 h p

theorem false_of_large_component [Finite G] (w : G) (X Q L : Subgroup G) (n m : ℕ)
    (hm : ∀ k, 0 < k → k ≤ n → k ∣ m)
    (hQL : Q ≤ L) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hLX : L ≤ Subgroup.normalizer (X : Set G))
    (hdich : ∀ N : Subgroup G, N ≤ Q →
      (∀ g ∈ L, g ^ m ∈ Subgroup.normalizer (N : Set G)) →
        N ≤ Subgroup.zpowers w ∨ N = Q)
    (hidx : ¬ (Subgroup.zpowers w).relIndex Q ∣ n.factorial)
    (hG : ¬ 9 ^ (n + 1) ∣ Nat.card G)
    (hw3 : orderOf w = 3) (hwQ : w ∈ Q) (hXw : X ≤ Subgroup.centralizer ({w} : Set G))
    {J : Subgroup G} (hJ : IsComponentOf J X) (hJ9 : 9 ∣ (Subgroup.center J).index)
    (hZ : Subgroup.center J = ⊥)
    (hbig : (Nat.card G).factorization 3 + 1 <
      (Nat.card Q).factorization 3 + (Nat.card J).factorization 3) : False := by
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
  have hJS : J ∈ S := (hmemS J).2 ⟨hJ, hJ9⟩
  obtain ⟨hpowJ, hQS⟩ := normalizes_of_dich w Q L S n m hm hQL hLQ hS hSn hdich hidx
  have hQN : Q ≤ Subgroup.normalizer (J : Set G) := fun q hq => hQS q hq J hJS
  have hNn : ∀ g ∈ L, g ^ m ∈ Subgroup.normalizer ((J ⊓ Q : Subgroup G) : Set G) := by
    intro g hg
    have h1 := hLQ (L.pow_mem hg m)
    have h2 := hpowJ g hg J hJS
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_inf]
    rw [Subgroup.mem_normalizer_iff.1 h2 x, Subgroup.mem_normalizer_iff.1 h1 x]
  rcases hdich (J ⊓ Q) inf_le_right hNn with hJQ | hJQ
  ·
    have hcard := card_sup_mul_card_inf_of_le_normalizer (A := J) (B := Q) hQN
    have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have hsup : (Nat.card ↥(J ⊔ Q)).factorization 3 ≤ (Nat.card G).factorization 3 :=
      factorization_le_of_dvd 3 hG0 (Subgroup.card_subgroup_dvd_card _)
    have hinf : (Nat.card ↥(J ⊓ Q)).factorization 3 ≤ 1 := by
      have h3 : Nat.card ↥(J ⊓ Q) ∣ 3 := by
        have := Subgroup.card_dvd_of_le hJQ
        rwa [Nat.card_zpowers, hw3] at this
      have := factorization_le_of_dvd 3 (by norm_num) h3
      rwa [Nat.Prime.factorization_self Nat.prime_three] at this
    have hJ0 : Nat.card J ≠ 0 := Nat.card_pos.ne'
    have hQ0 : Nat.card Q ≠ 0 := Nat.card_pos.ne'
    have hS0 : Nat.card ↥(J ⊔ Q) ≠ 0 := Nat.card_pos.ne'
    have hI0 : Nat.card ↥(J ⊓ Q) ≠ 0 := Nat.card_pos.ne'
    have e1 := congrArg (fun k => k.factorization 3) hcard
    simp only [Nat.factorization_mul hS0 hI0, Nat.factorization_mul hJ0 hQ0,
      Finsupp.add_apply] at e1
    omega
  ·
    have hwJ : w ∈ J := (hJQ ▸ inf_le_left : Q ≤ J) hwQ
    have hwZ : (⟨w, hwJ⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro j
      apply Subtype.ext
      have hjw := hXw (hJ.1 j.2)
      rw [Subgroup.mem_centralizer_singleton_iff] at hjw
      simp only [Subgroup.coe_mul]
      first
        | exact hjw
        | exact hjw.symm
    rw [hZ, Subgroup.mem_bot] at hwZ
    have hw1 : w = 1 := congrArg Subtype.val hwZ
    rw [hw1, orderOf_one] at hw3
    norm_num at hw3

end CFSG.LocalAnalysis.GLTheoremA.H1420.SporD4

end
