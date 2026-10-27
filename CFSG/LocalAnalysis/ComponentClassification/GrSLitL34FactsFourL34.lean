module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsL2Model

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

theorem mem_sup_zpowers {X : Type*} [Group X] {a b y : X} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (hy : y ∈ zpowers b ⊔ zpowers a) :
    y = 1 ∨ y = a ∨ y = b ∨ y = b * a := by
  have hle : zpowers b ≤ normalizer (zpowers a : Set X) :=
    zpowers_le.2 (mem_normalizer_of_commute fun z hz =>
      (commute_zpowers_zpowers hab.symm b (mem_zpowers b) z hz))
  have h1 := coe_mul_of_left_le_normalizer_right _ _ hle
  have hy' : y ∈ ((zpowers b : Set X) * (zpowers a : Set X)) := by
    rw [← h1]
    exact hy
  obtain ⟨b', hb', a', ha', rfl⟩ := Set.mem_mul.mp hy'
  rcases eq_one_or_eq_of_mem_zpowers hb hb' with rfl | rfl <;>
    rcases eq_one_or_eq_of_mem_zpowers ha ha' with rfl | rfl <;> simp

variable {G : Type} [Group G]

variable {J : Subgroup G}

theorem mem_coreActionKernel_of_betaHat {g : G} (hg : g ∈ normalizer (J : Set G))
    (h : ∀ e, betaHat J hg e = e) : g ∈ coreActionKernel J := by
  refine mem_coreActionKernel.mpr ⟨hg, fun j hj => ?_⟩
  have hmem : j⁻¹ * g⁻¹ * j * g ∈ J := by
    have := conj_mem_of_mem_normalizer hg hj
    rw [show j⁻¹ * g⁻¹ * j * g = j⁻¹ * (g⁻¹ * j * g) by group]
    exact J.mul_mem (J.inv_mem hj) this
  show _ ∈ oddIn J
  rw [mem_oddIn_iff hmem]
  have e1 : (⟨j⁻¹ * g⁻¹ * j * g, hmem⟩ : J) = (⟨j, hj⟩ : J)⁻¹ * conjJ J hg ⟨j, hj⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjJ]
    group
  rw [e1, map_mul, map_inv, ← betaHat_jq, h, inv_mul_cancel]

theorem betaHat_eq_of_realization_one (hJ : ⁅J, J⁆ = J)
    {q : Jhat J →* Equiv.Perm (Fin 42)} (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    (hqker : q.ker = center (Jhat J)) {g : G} (hg : g ∈ normalizer (J : Set G))
    (h : ∀ e, q (betaHat J hg e) = 1 * q e * 1⁻¹) (e : Jhat J) : betaHat J hg e = e := by
  obtain ⟨e₀, he₀, hβ⟩ := eq_conj_of_realization hJ hqsurj hqker S.one_mem h
  have hc : e₀ ∈ center (Jhat J) := by rw [← hqker]; exact he₀
  rw [hβ, (mem_center_iff.mp hc e).symm, mul_inv_cancel_right]

variable [Finite G]

theorem pRank_three_of_eightGroup {E F : Subgroup G} (hE : IsEightGroup E) (hEF : E ≤ F) :
    3 ≤ pRank 2 ↥F := by
  have hEA : IsElementaryAbelian 2 ↥(E.subgroupOf F) :=
    { is_comm := ⟨fun x y => Subtype.ext (Subtype.ext (hE.1.1 _ x.2 _ y.2))⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun y =>
        Subtype.ext (Subtype.ext (by
          show ((y : F) : G) ^ 2 = 1
          rw [pow_two]
          exact hE.1.2 _ y.2)) }
  have hcard : Nat.card ↥(E.subgroupOf F) = 2 ^ 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEF).toEquiv, hE.2]
    norm_num
  have hmem : 3 ∈ {r : ℕ | ∃ A : Subgroup ↥F, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r} :=
    ⟨_, hEA, hcard⟩
  have hbdd : BddAbove
      {r : ℕ | ∃ A : Subgroup ↥F, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r} := by
    refine ⟨Nat.card F, ?_⟩
    rintro k ⟨B, -, hB⟩
    calc k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card F := by rw [← Nat.card_congr (Equiv.refl _)]; exact card_le_card_group B
  exact le_csSup hbdd hmem

theorem pow_two_eight_of_mem_R {g : Equiv.Perm (Fin 42)}
    (hg : g ∈ R) {k : ℕ} (hk : g ^ 2 ^ k = 1) : g ^ 2 ^ 8 = 1 := by
  have hdvd : orderOf (⟨g, hg⟩ : R) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hk))
  obtain ⟨m, -, hmo⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hR : orderOf (⟨g, hg⟩ : R) ∣ 241920 := card_R ▸ _root_.orderOf_dvd_natCard _
  rw [hmo] at hR
  have hm8 : m ≤ 8 := by
    by_contra h
    push Not at h
    have : 2 ^ 9 ∣ 241920 := (Nat.pow_dvd_pow 2 h).trans hR
    norm_num at this
  have h1 : (⟨g, hg⟩ : R) ^ 2 ^ 8 = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (hmo ▸ Nat.pow_dvd_pow 2 hm8)
  have := congrArg Subtype.val h1
  simpa using this

omit [Finite G] in
theorem mul_self_of_mem_closure {X : Set G} (hX1 : ∀ a ∈ X, a * a = 1)
    (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) {f : G} (hf : f ∈ closure X) : f * f = 1 := by
  have hA : closure X ≤ centralizer X :=
    (closure_le _).2 fun a ha => mem_centralizer_iff.2 fun b hb => (hX a ha b hb).symm
  have hB : closure X ≤ centralizer (closure X : Set G) :=
    (closure_le _).2 fun b hb => mem_centralizer_iff.2 fun f hf =>
      (mem_centralizer_iff.1 (hA hf) b hb).symm
  induction hf using Subgroup.closure_induction with
  | mem a ha => exact hX1 a ha
  | one => exact mul_one 1
  | mul a b ha hb iha ihb =>
    have hab : a * b = b * a := mem_centralizer_iff.1 (hB hb) a ha
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = a * a * (b * b) := by group
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a ha iha => rw [← mul_inv_rev, iha, inv_one]

theorem four_l34
    (hJ : ⁅J, J⁆ = J) (hL : IsL34Type (J ⧸ Open.fusionZStar J)) {x : G}
    (hx : IsL34Unitary J x) {F : Subgroup G}
    (hFN : F ≤ normalizer (J : Set G) ⊓ centralizer ({x} : Set G)) (hF2 : IsPGroup 2 F)
    (hxF : x ∈ F) (hFo : F = omegaOne F) (hFK : F ⊓ coreActionKernel J = ⊥)
    (hrk : pRank 2 ↥F ≤ 2) : IsElemTwo F ∧ Nat.card F ≤ 4 := by
  obtain ⟨q, hqS, hqsurj, hqker, -, hβ⟩ := exists_unitary_realization hJ hL hx
  have hrel : ∀ g (hg : g ∈ normalizer (J : Set G)), ∃ ρ ∈ R,
      ∀ e, q (betaHat J hg e) = ρ * q e * ρ⁻¹ := fun g hg =>
    exists_realization q hqS hqsurj (betaHat J hg) (fun e => by
      rw [hqker]
      exact mulEquiv_mem_center_iff _ e)
  choose ρ hρR hρ using hrel
  have hcongr : ∀ {g h : G} (hg : g ∈ normalizer (J : Set G)) (hh : h ∈ normalizer (J : Set G)),
      g = h → ρ g hg = ρ h hh := by
    intro g h hg hh e
    subst e
    rfl
  have hmul : ∀ {g h : G} (hg : g ∈ normalizer (J : Set G)) (hh : h ∈ normalizer (J : Set G)),
      ρ (g * h) (mul_mem hg hh) = ρ h hh * ρ g hg := by
    intro g h hg hh
    refine realization_unique hqsurj (hρR _ _) (R.mul_mem (hρR h hh) (hρR g hg)) (hρ _ _) ?_
    intro e
    rw [betaHat_mul J hg hh, hρ h hh, hρ g hg]
    group
  have hone : ∀ {g : G} (hg : g ∈ normalizer (J : Set G)), g = 1 → ρ g hg = 1 := by
    intro g hg h1
    refine realization_unique hqsurj (hρR g hg) R.one_mem (hρ g hg) ?_
    intro e
    rw [betaHat_eq_self J hg h1]
    group
  have hpow : ∀ {g : G} (hg : g ∈ normalizer (J : Set G)) (k : ℕ),
      ρ (g ^ k) (pow_mem hg k) = ρ g hg ^ k := by
    intro g hg k
    induction k with
    | zero => exact hone _ (pow_zero g)
    | succ k ih =>
      rw [hcongr (pow_mem hg (k + 1)) (mul_mem (pow_mem hg k) hg) (pow_succ g k),
        hmul (pow_mem hg k) hg, ih, pow_succ']
  have hN : ∀ {f : G}, f ∈ F → f ∈ normalizer (J : Set G) := fun hf => (mem_inf.mp (hFN hf)).1
  have hC : ∀ {f : G}, f ∈ F → f * x = x * f := fun hf =>
    mem_centralizer_singleton_iff.mp (mem_inf.mp (hFN hf)).2
  have hcore : ∀ {g : G} (hg : g ∈ normalizer (J : Set G)), g ∈ F → ρ g hg = 1 → g = 1 := by
    intro g hg hgF h1
    have hb := betaHat_eq_of_realization_one hJ hqsurj hqker hg (fun e => by rw [hρ g hg, h1])
    have hmem : g ∈ F ⊓ coreActionKernel J :=
      mem_inf.mpr ⟨hgF, mem_coreActionKernel_of_betaHat hg hb⟩
    rw [hFK, mem_bot] at hmem
    exact hmem
  have hinj : ∀ {a b : G} (ha : a ∈ F) (hb : b ∈ F), ρ a (hN ha) = ρ b (hN hb) → a = b := by
    intro a b ha hb hab
    have hinv : ρ a⁻¹ (inv_mem (hN ha)) = (ρ a (hN ha))⁻¹ := by
      have h1 := hmul (hN ha) (inv_mem (hN ha))
      rw [hone _ (mul_inv_cancel a)] at h1
      exact eq_inv_of_mul_eq_one_left h1.symm
    have h2 := hmul (hN hb) (inv_mem (hN ha))
    rw [hinv, hab, inv_mul_cancel] at h2
    exact (mul_inv_eq_one.mp (hcore _ (mul_mem hb (inv_mem ha)) h2)).symm
  have hρx : ρ x hx.1 = r₄ := realization_unique hqsurj (hρR x hx.1) r₄_mem_R (hρ x hx.1) hβ
  have hx2 := hx.2.1
  have hx1 : x ≠ 1 := fun h => hx.2.2.1 (h ▸ one_mem _)
  have hcomm : ∀ u ∈ F, ∀ v ∈ F, u * u = 1 → v * v = 1 → u * v = v * u := by
    intro u hu v hv hu2 hv2
    by_contra huv
    have hu1 : u ≠ 1 := fun h => huv (by rw [h, one_mul, mul_one])
    have hv1 : v ≠ 1 := fun h => huv (by rw [h, one_mul, mul_one])
    have hux : u ≠ x := fun h => huv (by rw [h]; exact (hC hv).symm)
    have hρu2 : ρ u (hN hu) * ρ u (hN hu) = 1 := by
      rw [← hmul (hN hu) (hN hu)]
      exact hone _ hu2
    have hρv2 : ρ v (hN hv) * ρ v (hN hv) = 1 := by
      rw [← hmul (hN hv) (hN hv)]
      exact hone _ hv2
    have hρu1 : ρ u (hN hu) ≠ 1 := fun h => hu1 (hcore (hN hu) hu h)
    have hρv1 : ρ v (hN hv) ≠ 1 := fun h => hv1 (hcore (hN hv) hv h)
    have hρur : ρ u (hN hu) * r₄ = r₄ * ρ u (hN hu) := by
      rw [← hρx]
      exact realization_comm hqsurj (hN hu) hx.1 (hC hu) (hρR _ _) (hρR _ _) (hρ _ _) (hρ _ _)
    have hρvr : ρ v (hN hv) * r₄ = r₄ * ρ v (hN hv) := by
      rw [← hρx]
      exact realization_comm hqsurj (hN hv) hx.1 (hC hv) (hρR _ _) (hρR _ _) (hρ _ _) (hρ _ _)
    have hρuv : ρ u (hN hu) * ρ v (hN hv) ≠ ρ v (hN hv) * ρ u (hN hu) := by
      intro h
      apply huv
      apply hinj (mul_mem hu hv) (mul_mem hv hu)
      rw [hmul (hN hu) (hN hv), hmul (hN hv) (hN hu)]
      exact h.symm
    have hvu : ρ (v * u) (hN (mul_mem hv hu)) = ρ u (hN hu) * ρ v (hN hv) :=
      hmul (hN hv) (hN hu)
    obtain ⟨k, hk⟩ := hF2 ⟨v * u, mul_mem hv hu⟩
    have hk' : (v * u) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h28 : (ρ u (hN hu) * ρ v (hN hv)) ^ 2 ^ 8 = 1 := by
      refine pow_two_eight_of_mem_R (R.mul_mem (hρR _ _) (hρR _ _)) (k := k) ?_
      rw [← hvu, ← hpow (hN (mul_mem hv hu))]
      exact hone _ hk'
    obtain ⟨j, hz2, hz1, hzu, hzr, hzru, hzu'⟩ := exists_four (hρR _ _) (hρR _ _) hρur hρvr hρu2
      hρv2 hρu1 hρv1 hρuv h28
    have hzF : (v * u) ^ 2 ^ j ∈ F := pow_mem (mul_mem hv hu) _
    have hρz : ρ ((v * u) ^ 2 ^ j) (hN hzF) = (ρ u (hN hu) * ρ v (hN hv)) ^ 2 ^ j := by
      rw [← hvu, ← hpow (hN (mul_mem hv hu))]
    have hzz : (v * u) ^ 2 ^ j * (v * u) ^ 2 ^ j = 1 := by
      refine hcore (hN (mul_mem hzF hzF)) (mul_mem hzF hzF) ?_
      rw [hmul (hN hzF) (hN hzF), hρz, hz2]
    have hz1' : (v * u) ^ 2 ^ j ≠ 1 := fun h => hz1 (by rw [← hρz]; exact hone _ h)
    have hzuc : (v * u) ^ 2 ^ j * u = u * (v * u) ^ 2 ^ j := by
      refine hinj (mul_mem hzF hu) (mul_mem hu hzF) ?_
      rw [hmul (hN hzF) (hN hu), hmul (hN hu) (hN hzF), hρz]
      exact hzu.symm
    have hzx : (v * u) ^ 2 ^ j ≠ x := fun h => hzr (by
      rw [← hρz, ← hρx]
      exact hcongr _ _ h)
    have hzux : (v * u) ^ 2 ^ j ≠ u * x := fun h => hzru (by
      rw [← hρz, hcongr _ (hN (mul_mem hu hxF)) h, hmul (hN hu) (hN hxF),
        hcongr (hN hxF) hx.1 rfl, hρx])
    have hzuu : (v * u) ^ 2 ^ j ≠ u := fun h => hzu' (by rw [← hρz]; exact hcongr _ _ h)
    have hb' : u ∉ zpowers x := fun hm => (eq_one_or_eq_of_mem_zpowers hx2 hm).elim hu1 hux
    have hc' : (v * u) ^ 2 ^ j ∉ zpowers u ⊔ zpowers x := fun hm => by
      rcases mem_sup_zpowers hx2 hu2 (hC hu).symm hm with h | h | h | h
      · exact hz1' h
      · exact hzx h
      · exact hzuu h
      · exact hzux h
    have h8 := isEightGroup_of_three hx2 hu2 hzz (hC hu).symm (hC hzF).symm hzuc.symm hx1 hb' hc'
    have hle : zpowers ((v * u) ^ 2 ^ j) ⊔ (zpowers u ⊔ zpowers x) ≤ F :=
      sup_le (zpowers_le.2 hzF) (sup_le (zpowers_le.2 hu) (zpowers_le.2 hxF))
    have := pRank_three_of_eightGroup h8 hle
    omega
  refine elemTwo_card_le_four (fun f hf => ?_) hrk
  have hf' : f ∈ omegaOne F := hFo ▸ hf
  exact mul_self_of_mem_closure (fun a ha => ha.2)
    (fun a ha b hb => hcomm a ha.1 b hb.1 ha.2 hb.2) hf'

end CFSG.ComponentClassification.GrSLit.L34Facts
