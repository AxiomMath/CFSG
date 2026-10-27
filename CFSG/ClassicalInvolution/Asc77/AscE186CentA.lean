module

public import CFSG.ClassicalInvolution.Asc77.AscE184Dich
public import CFSG.ClassicalInvolution.Asc77.AscL62Final
public import CFSG.ClassicalInvolution.Asc77.AscL62Lem33
public import CFSG.ClassicalInvolution.Asc77.AscSteps185

public section

namespace CFSG.ClassicalInvolution.Asc77.AscE186

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Fact p.Prime] in
theorem commutator_mul_central {a b c d : G} (hc : c ∈ Subgroup.center G)
    (hd : d ∈ Subgroup.center G) : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hc' : ∀ g : G, g * c = c * g := fun g => Subgroup.mem_center_iff.mp hc g
  have hd' : ∀ g : G, g * d = d * g := fun g => Subgroup.mem_center_iff.mp hd g
  have h1 : a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹ = a * (b * d) * a⁻¹ * (b * d)⁻¹ := by
    have hcx : c * (b * d) = (b * d) * c := (hc' (b * d)).symm
    calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
        = a * (c * (b * d)) * c⁻¹ * a⁻¹ * (b * d)⁻¹ := by group
      _ = a * ((b * d) * c) * c⁻¹ * a⁻¹ * (b * d)⁻¹ := by rw [hcx]
      _ = a * (b * d) * a⁻¹ * (b * d)⁻¹ := by group
  have h2 : a * (b * d) * a⁻¹ * (b * d)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
    have hda : d * a⁻¹ = a⁻¹ * d := (hd' a⁻¹).symm
    calc a * (b * d) * a⁻¹ * (b * d)⁻¹ = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by group
      _ = a * b * (a⁻¹ * d) * d⁻¹ * b⁻¹ := by rw [hda]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  rw [commutatorElement_def, commutatorElement_def, h1, h2]

omit [Fact p.Prime] in
theorem le_of_le_sup_central {N : Subgroup G} [N.Normal] (hNc : N ≤ Subgroup.center G)
    {K M : Subgroup G} (hM : Group.IsPerfect ↥M) (h : M ≤ K ⊔ N) : M ≤ K := by
  have hcomm : ⁅M, M⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨k₁, hk₁, n₁, hn₁, e₁⟩ := Subgroup.mem_sup_of_normal_right.mp (h ha)
    obtain ⟨k₂, hk₂, n₂, hn₂, e₂⟩ := Subgroup.mem_sup_of_normal_right.mp (h hb)
    rw [← e₁, ← e₂, commutator_mul_central (hNc hn₁) (hNc hn₂), commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hk₁ hk₂) (K.inv_mem hk₁)) (K.inv_mem hk₂)
  rwa [Subgroup.isPerfect_iff.mp hM] at hcomm

omit [Fact p.Prime] in
theorem conjSub_le_of_le_sup_central {N : Subgroup G} [N.Normal] (hNc : N ≤ Subgroup.center G)
    {K : Subgroup G} (hK : Group.IsPerfect ↥K) (u : G) (h : conjSub u K ≤ K ⊔ N) :
    conjSub u K ≤ K := by
  have hcomm : ⁅K, K⁆ ≤ conjSub u⁻¹ K := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [mem_conjSub_iff, inv_inv]
    have hkey : u * ⁅a, b⁆ * u⁻¹ = ⁅u * a * u⁻¹, u * b * u⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hkey]
    obtain ⟨k₁, hk₁, n₁, hn₁, e₁⟩ := Subgroup.mem_sup_of_normal_right.mp (h (conj_mem_conjSub ha))
    obtain ⟨k₂, hk₂, n₂, hn₂, e₂⟩ := Subgroup.mem_sup_of_normal_right.mp (h (conj_mem_conjSub hb))
    rw [← e₁, ← e₂, commutator_mul_central (hNc hn₁) (hNc hn₂)]
    exact (Subgroup.isPerfect_iff.mp hK).le (Subgroup.commutator_mem_commutator hk₁ hk₂)
  rw [Subgroup.isPerfect_iff.mp hK] at hcomm
  have := conjSub_mono (n := u) hcomm
  rwa [conjSub_conjSub_inv] at this

section Finite

variable [Finite G]

theorem conjSub_eq_of_le_sup_central {N : Subgroup G} [N.Normal] (hNc : N ≤ Subgroup.center G)
    {K : Subgroup G} (hK : Group.IsPerfect ↥K) (u : G) (h : conjSub u K ≤ K ⊔ N) :
    conjSub u K = K :=
  Subgroup.eq_of_le_of_card_ge (conjSub_le_of_le_sup_central hNc hK u h)
    (by rw [AscL62.natCard_conjSub])

omit [Finite G] in
theorem perfect_of_mem (hΩ : HypOmegaMod p f Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    Group.IsPerfect ↥K := hΩ.isPerfect hK

omit [Finite G] in
theorem commutes_of_commutator_le_oddCoreOf_of_exact {V K : Subgroup G} (hK : oddCoreOf K = ⊥)
    (h : ⁅V, K⁆ ≤ oddCoreOf K) : Commutes V K := fun v hv k hk => by
  have h1 : ⁅v, k⁆ ∈ oddCoreOf K := h (Subgroup.commutator_mem_commutator hv hk)
  rw [hK, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

omit [Fact p.Prime] [Finite G] in
theorem exists_mul_of_mem_sup_of_commutes {A B : Subgroup G} (h : Commutes A B) {g : G}
    (hg : g ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  let S : Subgroup G :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, a * b = g}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        rw [mul_assoc a b (a' * b'), ← mul_assoc b a' b', ← h a' ha' b hb]
        simp only [mul_assoc]
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        rw [mul_inv_rev, h a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)] }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩)
  exact hle hg

theorem E187C.exists_commuting_sylow_pair_of
    (hsyl : ∀ {J T : Subgroup G}, J ∈ Ω → T ∈ RSet Ω → T ≤ J → IsSylow2In T J)
    (h8R : ∀ {Q : Subgroup G}, Q ∈ RSet Ω → 8 ≤ Nat.card Q)
    (heq : ∀ {K J A : Subgroup G}, K ∈ Ω → J ∈ Ω → IsPGroup 2 A → 4 ≤ Nat.card A → A ≤ K →
      A ≤ J → K = J)
    (hl67 : ∀ (S : Sylow 2 G) (T : Subgroup G), T ∈ RSet Ω → ∀ R : Subgroup G, R ∈ RSet Ω →
      T ≤ (S : Subgroup G) → R ≤ (S : Subgroup G) → T ≠ R → Commutes T R)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) :
    ∃ R T : Subgroup G, IsSylow2In R K ∧ IsSylow2In T J ∧ T ≤ Subgroup.normalizer (K : Set G) ∧
      Commutes R T := by
  obtain ⟨hJΩ, hne, T, hT, hTJ, hTN⟩ := hJ
  have hTsyl : IsSylow2In T J := hsyl hJΩ hT hTJ
  have hT2 : IsPGroup 2 ↥T := hTsyl.2.1
  have h8 : 8 ≤ Nat.card T := h8R hT
  obtain ⟨R, hR, hRinv⟩ := AscL62.exists_sylow_normalized hT2 hTN
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR
  have hTnR : T ≤ Subgroup.normalizer (R : Set G) := fun t ht =>
    mem_normalizer_iff_conjSub_eq.mpr (hRinv t ht)
  have hTR2 : IsPGroup 2 ↥(T ⊔ R) := hT2.to_sup_of_normal_right' hR.2.1 hTnR
  obtain ⟨S, hS⟩ := hTR2.exists_le_sylow
  have hTneR : T ≠ R := by
    intro h
    exact hne (heq hJΩ hK hT2 (by omega) hTJ (h ▸ hR.1))
  exact ⟨R, T, hR, hTsyl, hTN,
    (hl67 S T hT R hRset (le_sup_left.trans hS) (le_sup_right.trans hS)
      hTneR).symm⟩

theorem exists_commuting_sylow_pair (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) :
    ∃ R T : Subgroup G, IsSylow2In R K ∧ IsSylow2In T J ∧ T ≤ Subgroup.normalizer (K : Set G) ∧
      Commutes R T :=
  E187C.exists_commuting_sylow_pair_of
    (fun hJ hT hTJ => hΩ.isSylow2In_of_mem_RSet_of_le hp hJ hT hTJ)
    (fun hQ => hΩ.eight_le_of_mem_RSet hp hQ)
    (fun hK hJ hA h4 hAK hAJ => hΩ.eq_of_le_of_le hK hJ hA h4 hAK hAJ)
    (l6_7_proved p f hp hq G Ω hΩ)
    hK hJ

theorem commutes_of_mem_omegaNbr (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmega p f Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) : Commutes K J := by
  have hΩm : HypOmegaMod p f Ω := hΩ.toMod
  obtain ⟨R, T, hR, hTsyl, hTN, hcomm⟩ := exists_commuting_sylow_pair hp hq hΩm hK hJ
  obtain ⟨hJΩ, hne, -⟩ := hJ
  have hT2 : IsPGroup 2 ↥T := hTsyl.2.1
  have hTK : Commutes T K :=
    commutes_of_commutator_le_oddCoreOf_of_exact (oddCoreOf_eq_bot_of_exact hΩ.exact hK)
      (lemma_3_3_member hp hq hΩm hK hR hT2 hTN hcomm.symm)
  obtain ⟨t, ht⟩ := hΩm.exists_uniqueInvolution hp hq hJΩ
  have h8T : 8 ≤ Nat.card T := hΩm.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hJΩ hTsyl)
  have htT : t ∈ T := AscL62.mem_of_uniqueInvolution_of_pGroup ht hTsyl.1 hT2 (by omega)
  have hKJ : K ≤ Subgroup.centralizer (J : Set G) := by
    refine AscQuot.le_of_forall_isSylow2In hp hq hΩm hK (M := Subgroup.centralizer (J : Set G)) ?_
    intro V hV
    have h8V := hΩm.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hV)
    have hVc : V ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hTK t htT x (hV.1 hx)).symm
    have hVN : V ≤ Subgroup.normalizer (J : Set G) :=
      hΩm.le_normalizer_of_le_centralizer hp hq hJΩ hK hne ht hV.1 hV.2.1 (by omega) hVc
    have hVT : Commutes V T := fun x hx y hy => (hTK y hy x (hV.1 hx)).symm
    have := commutes_of_commutator_le_oddCoreOf_of_exact (oddCoreOf_eq_bot_of_exact hΩ.exact hJΩ)
      (lemma_3_3_member hp hq hΩm hJΩ hTsyl hV.2.1 hVN hVT)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (this x hx y hy).symm
  intro k hk j hj
  exact (Subgroup.mem_centralizer_iff.mp (hKJ hk) j hj).symm

theorem mem_omegaNbr_of_le_centralizer (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hne : J ≠ K) {z : G}
    (hz : IsUniqueInvolution K z) (hJc : J ≤ Subgroup.centralizer ({z} : Set G)) :
    J ∈ omegaNbr Ω K := by
  obtain ⟨R, hR, hRJ, -⟩ := exists_mem_RSet_ge hJ (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    bot_le
  have h8 := hΩ.eight_le_of_mem_RSet hp hR
  exact ⟨hJ, hne, R, hR, hRJ.1, hΩ.le_normalizer_of_le_centralizer hp hq hK hJ hne.symm hz hRJ.1
    hRJ.2.1 (by omega) (hRJ.1.trans hJc)⟩

theorem exists_orderOf_four_of_mem (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {L : Subgroup G}
    (hL : L ∈ Ω) : ∃ u ∈ L, orderOf u = 4 := by
  obtain ⟨R, hR, hRL, -⟩ := exists_mem_RSet_ge hL (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    bot_le
  obtain ⟨u, huR, hu⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet hp hR
  exact ⟨u, hRL.1 huR, hu⟩

omit [Fact p.Prime] [Finite G] in
theorem exists_orderOf_four_commute_of_isQuatSub {R : Subgroup G} (h : IsQuatSub R) {x : G}
    (hx : x ∈ R) : ∃ u ∈ R, orderOf u = 4 ∧ u * x = x * u := by
  obtain ⟨k, hk, ⟨e⟩⟩ := h
  suffices H : ∀ q : QuaternionGroup (2 ^ k), ∃ v : QuaternionGroup (2 ^ k),
      orderOf v = 4 ∧ v * q = q * v by
    obtain ⟨v, hv4, hvq⟩ := H (e ⟨x, hx⟩)
    refine ⟨((e.symm v : ↥R) : G), (e.symm v).2, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hv4]
    · have h1 : e.symm v * (⟨x, hx⟩ : ↥R) = (⟨x, hx⟩ : ↥R) * e.symm v := by
        have := congrArg e.symm hvq
        rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at this
        exact this
      exact congrArg Subtype.val h1
  intro q
  cases q with
  | a i =>
    refine ⟨(QuaternionGroup.a 1 : QuaternionGroup (2 ^ k)) ^ 2 ^ (k - 1), ?_, ?_⟩
    · have h1 : orderOf (QuaternionGroup.a 1 : QuaternionGroup (2 ^ k)) = 2 ^ (k + 1) := by
        rw [QuaternionGroup.orderOf_a_one]
        ring
      have hdvd : 2 ^ (k - 1) ∣ orderOf (QuaternionGroup.a 1 : QuaternionGroup (2 ^ k)) := by
        rw [h1]
        exact pow_dvd_pow 2 (by omega)
      rw [orderOf_pow_of_dvd (by positivity) hdvd, h1]
      have : k + 1 = (k - 1) + 2 := by omega
      rw [this, pow_add]
      exact Nat.mul_div_cancel_left 4 (by positivity)
    · rw [QuaternionGroup.a_one_pow, QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_a, add_comm]
  | xa j =>
    exact ⟨QuaternionGroup.xa j, QuaternionGroup.orderOf_xa j, rfl⟩

theorem mem_dstarComp_of_twin (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ twinSet Ω K) : L ∈ dstarComp Ω K := by
  by_cases hLK : L = K
  · rw [hLK]
    exact Relation.ReflTransGen.refl
  obtain ⟨hLΩ, z, hzK, hzL⟩ := hL
  exact Relation.ReflTransGen.single
    (dstarAdj_of_le_normalizer hp hΩ hLΩ hLK (hΩ.le_normalizer_of_twin hLΩ hK hLK hzL hzK))

end Finite

end CFSG.ClassicalInvolution.Asc77.AscE186
