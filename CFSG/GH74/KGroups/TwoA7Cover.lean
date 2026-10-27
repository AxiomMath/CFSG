module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Quaternion
public import CFSG.CharacterTheory.Semidihedral.QuaternionDoubleCoverUniqueness
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Statements

public section

namespace CFSG.GH74.KGroups.TwoA7

open CFSG.ClassicalInvolution.Hat2A7 Equiv Equiv.Perm Subgroup CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.Semidihedral.QuaternionDoubleCoverUniqueness

theorem exists_cover {Q : Type} [Group Q] (hQ : IsDoubleCoverOfAlt Q 7) :
    ∃ (π : Q →* A7) (z : Q), IsDoubleCoverA7 π z ∧
      ∀ w : Q, w ∈ Subgroup.center Q ↔ (w = 1 ∨ w = z) := by
  obtain ⟨hq, hc, ⟨e⟩⟩ := hQ
  set Z : Subgroup Q := Subgroup.center Q with hZ
  obtain ⟨z, hz1, hzu⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hc
  have hZ12 : ∀ w : Z, w = 1 ∨ w = z := fun w => by
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · exact Or.inr (hzu w hw1)
  let π : Q →* A7 := e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hker : ∀ w : Q, π w = 1 ↔ w ∈ Z := fun w => by
    show e (QuotientGroup.mk w) = 1 ↔ w ∈ Z
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hcen : ∀ w : Q, w ∈ Z ↔ (w = 1 ∨ w = (z : Q)) := fun w => by
    constructor
    · intro hw
      rcases hZ12 ⟨w, hw⟩ with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
    · rintro (rfl | rfl)
      · exact Z.one_mem
      · exact z.2
  refine ⟨π, z, ?_, hcen⟩
  exact
    { surjective := e.surjective.comp (QuotientGroup.mk'_surjective Z)
      perfect := hq.1
      ne_one := fun h => hz1 (Subtype.ext h)
      sq_eq_one := by
        have h2 : z ^ 2 = 1 := by
          have := pow_card_eq_one' (G := Z) (x := z)
          rwa [hc] at this
        have h3 : (z : Q) ^ 2 = 1 := by
          have := congrArg Subtype.val h2
          simpa using this
        rwa [pow_two] at h3
      central := fun x => by
        have := Subgroup.mem_center_iff.mp z.2 x
        exact this
      ker_iff := fun w => (hker w).trans (hcen w) }

section Cover

variable {E : Type} [Group E] [Finite E] {π : E →* A7} {z : E}

omit [Finite E] in
theorem orderOf_z (h : IsDoubleCoverA7 π z) : orderOf z = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact h.sq_eq_one) h.ne_one

omit [Finite E] in
theorem z_mem_center (h : IsDoubleCoverA7 π z) : z ∈ Subgroup.center E :=
  Subgroup.mem_center_iff.2 fun g => h.central g

omit [Finite E] in
theorem ker_eq_zpowers (h : IsDoubleCoverA7 π z) : π.ker = Subgroup.zpowers z := by
  ext w
  rw [MonoidHom.mem_ker, h.ker_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  · rintro ⟨k, rfl⟩
    rw [← zpow_mod_orderOf, orderOf_z h, Nat.cast_ofNat]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left; rw [hk]; simp
    · right; rw [hk]; simp

omit [Finite E] in
theorem autPerm_eq_of_forall (h : IsDoubleCoverA7 π z) (α : MulAut E) (σ : Perm (Fin 7))
    (hα : ∀ x : E, ((π (α x) : A7) : Perm (Fin 7)) = σ * (π x : Perm (Fin 7)) * σ⁻¹) :
    h.autPerm α = σ := by
  apply conjEquiv.injective
  refine MulEquiv.ext (fun a => ?_)
  obtain ⟨x, rfl⟩ := h.surjective a
  apply Subtype.ext
  rw [conjEquiv_apply, conjEquiv_apply, ← h.autPerm_spec α x, hα x]

theorem sylow_quaternion (h : IsDoubleCoverA7 π z) (P : Sylow 2 E) :
    Nonempty ((P : Subgroup E) ≃* QuaternionGroup 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnc := h.not_isCyclic_sylow P
  have hcard := h.card_sylow P
  have hinv : ∀ x : E, orderOf x = 2 → x = z := by
    intro x hxo
    have hx2 : x * x = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hxo, pow_two] at this
    rcases h.eq_one_or_eq_z_of_sq_eq_one hx2 with h1 | h1
    · rw [h1, orderOf_one] at hxo
      omega
    · exact h1
  have hdvd : 2 ∣ Nat.card (P : Subgroup E) := by rw [hcard]; norm_num
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := (P : Subgroup E)) 2 hdvd
  have hx₀' : orderOf ((x₀ : ↥(P : Subgroup E)) : E) = 2 := by
    rw [Subgroup.orderOf_coe]; exact hx₀
  have hunique : ∃ U : Subgroup ↥(P : Subgroup E), Nat.card U = 2 ∧
      ∀ V : Subgroup ↥(P : Subgroup E), Nat.card V = 2 → V = U := by
    refine ⟨Subgroup.zpowers x₀, by rw [Nat.card_zpowers, hx₀], fun V hV => ?_⟩
    have hv2 : 2 ∣ Nat.card V := by rw [hV]
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := V) 2 hv2
    have hvo : orderOf (((v : ↥(P : Subgroup E)) : E)) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hv
    have hvx : (v : ↥(P : Subgroup E)) = x₀ :=
      Subtype.ext ((hinv _ hvo).trans (hinv _ hx₀').symm)
    have hle : Subgroup.zpowers (v : ↥(P : Subgroup E)) ≤ V := by
      rw [Subgroup.zpowers_le]; exact v.2
    have hc1 : Nat.card (Subgroup.zpowers (v : ↥(P : Subgroup E))) = 2 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe]; exact hv
    rw [hvx] at hle hc1
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hc1, hV])).symm
  rcases (CFSG.BenderSuzuki.External.huppert_III_8_2_pgroup_unique_order_prime_subgroup
    Nat.prime_two P.isPGroup' hunique).2 rfl with hcyc | ⟨n, hn3, ⟨eq⟩⟩
  · exact absurd hcyc hnc
  · have hne : NeZero (2 ^ (n - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
    have h1 : Nat.card (QuaternionGroup (2 ^ (n - 2))) = 4 * 2 ^ (n - 2) := by
      rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    have h2 := Nat.card_congr eq.toEquiv
    rw [hcard, h1] at h2
    have h3 : 2 ^ (n - 2) = 2 ^ 2 := by omega
    have h4 : n - 2 = 2 := Nat.pow_right_injective (le_refl 2) h3
    have hn : n = 4 := by omega
    subst hn
    exact ⟨eq⟩

theorem exists_autPerm_eq
    (h : IsDoubleCoverA7 π z) (σ : Perm (Fin 7)) :
    ∃ α : MulAut E, h.autPerm α = σ := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 E) := inferInstance
  obtain ⟨eP⟩ := sylow_quaternion h P
  let c : MulAut A7 := (conjEquiv σ)⁻¹
  let π₂ : E →* A7 := (c : A7 ≃* A7).toMonoidHom.comp π
  have hπ₂ : Function.Surjective π₂ := c.surjective.comp h.surjective
  have hker₂ : π₂.ker = Subgroup.zpowers z := by
    rw [← ker_eq_zpowers h]
    ext w
    simp only [MonoidHom.mem_ker, π₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  obtain ⟨-, F, hF, -⟩ :=
    quaternion_sylow_central_double_cover_uniqueness
      z (orderOf_z h) (z_mem_center h) π h.surjective (ker_eq_zpowers h) P 4 (by norm_num) eP
      z (orderOf_z h) (z_mem_center h) π₂ hπ₂ hker₂ P 4 (by norm_num) eP
  have hFx : ∀ x : E, π (F x) = conjEquiv σ (π x) := by
    intro x
    have h1 : c (π (F x)) = π x := hF x
    have h2 : conjEquiv σ (c (π (F x))) = conjEquiv σ (π x) := congrArg _ h1
    have h3 : conjEquiv σ (c (π (F x))) = π (F x) := by
      show (conjEquiv σ * (conjEquiv σ)⁻¹) (π (F x)) = π (F x)
      rw [mul_inv_cancel]
      rfl
    exact h3.symm.trans h2
  refine ⟨F, autPerm_eq_of_forall h F σ (fun x => ?_)⟩
  rw [hFx x, conjEquiv_apply]

@[expose] noncomputable def autPermEquiv
    (h : IsDoubleCoverA7 π z) : MulAut E ≃* Perm (Fin 7) :=
  MulEquiv.ofBijective h.autPerm ⟨h.autPerm_injective, fun σ => exists_autPerm_eq h σ⟩

omit [Finite E] in
theorem autPerm_conj (h : IsDoubleCoverA7 π z) (q : E) :
    h.autPerm (MulAut.conj q) = (π q : Perm (Fin 7)) := by
  apply autPerm_eq_of_forall h
  intro x
  simp [MulAut.conj_apply, map_mul, map_inv]

omit [Finite E] in
theorem orderOf_conj (h : IsDoubleCoverA7 π z) (c : E) :
    orderOf (MulAut.conj c) = orderOf (π c) := by
  rw [← orderOf_injective h.autPerm h.autPerm_injective (MulAut.conj c), autPerm_conj]
  exact Subgroup.orderOf_coe _

omit [Finite E] in
theorem isPGroup_zpowers_of_orderOf_conj (h : IsDoubleCoverA7 π z) {c : E} {k : ℕ}
    (hk : orderOf (MulAut.conj c) = 2 ^ k) : IsPGroup 2 (Subgroup.zpowers c) := by
  rw [orderOf_conj h] at hk
  have h1 : π (c ^ (2 ^ k)) = 1 := by
    rw [map_pow, ← hk]
    exact pow_orderOf_eq_one _
  have h2 : (c ^ (2 ^ k)) ^ 2 = 1 := by
    rcases (h.ker_iff _).1 h1 with h3 | h3
    · rw [h3]; simp
    · rw [h3, pow_two]; exact h.sq_eq_one
  have h3 : c ^ (2 ^ (k + 1)) = 1 := by rw [pow_succ, pow_mul]; exact h2
  have hdvd : orderOf c ∣ 2 ^ (k + 1) := orderOf_dvd_of_pow_eq_one h3
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])

omit [Finite E] in
theorem map_innOf (h : IsDoubleCoverA7 π z) :
    (innOf E).map h.autPerm = alternatingGroup (Fin 7) := by
  ext σ
  constructor
  · rintro ⟨α, ⟨q, rfl⟩, rfl⟩
    show h.autPerm (MulAut.conj q) ∈ alternatingGroup (Fin 7)
    rw [autPerm_conj]
    exact (π q).2
  · intro hσ
    obtain ⟨q, hq⟩ := h.surjective ⟨σ, hσ⟩
    refine ⟨MulAut.conj q, ⟨q, rfl⟩, ?_⟩
    show h.autPerm (MulAut.conj q) = σ
    rw [autPerm_conj, hq]

theorem index_innOf
    (h : IsDoubleCoverA7 π z) : (innOf E).index = 2 := by
  have hb : Function.Bijective h.autPerm := (autPermEquiv h).bijective
  have h1 := Subgroup.index_map_of_bijective (f := h.autPerm) hb (innOf E)
  rw [map_innOf h] at h1
  rw [← h1]
  exact alternatingGroup.index_eq_two

end Cover

end CFSG.GH74.KGroups.TwoA7
