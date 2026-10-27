module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverQnode
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverTwo
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.D4Levi

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open scoped Pointwise

theorem exists_conj_of_order_three {K : Type*} [Group K] {Q : Subgroup K} [Finite Q]
    (hQ : ¬ 9 ∣ Nat.card Q) {u q : K} (hu : u ∈ Q) (hq : q ∈ Q) (hu3 : orderOf u = 3)
    (hq3 : orderOf q = 3) : ∃ j ∈ Q, ∃ e : ℕ, q = j * u ^ e * j⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set u' : ↥Q := ⟨u, hu⟩ with hu'
  set q' : ↥Q := ⟨q, hq⟩ with hq'
  have hu'3 : orderOf u' = 3 := by rw [← hu3, ← Subgroup.orderOf_coe]
  have hq'3 : orderOf q' = 3 := by rw [← hq3, ← Subgroup.orderOf_coe]
  have hcard : 3 ∣ Nat.card Q := hu'3 ▸ orderOf_dvd_natCard u'
  obtain ⟨m, hm⟩ := hcard
  have hm3 : ¬ 3 ∣ m := fun h => hQ (by rw [hm]; obtain ⟨t, rfl⟩ := h; exact ⟨t, by ring⟩)
  have hPc : ∀ x : ↥Q, orderOf x = 3 → Nat.card (Subgroup.zpowers x) = 3 := fun x hx => by
    rw [Nat.card_zpowers, hx]
  have hPp : ∀ x : ↥Q, orderOf x = 3 → IsPGroup 3 (Subgroup.zpowers x) := fun x hx =>
    IsPGroup.of_card (by rw [hPc x hx]; exact (pow_one 3).symm)
  have hidx : ∀ x : ↥Q, orderOf x = 3 → ¬ 3 ∣ (Subgroup.zpowers x).index := fun x hx => by
    have h := (Subgroup.card_mul_index (Subgroup.zpowers x))
    rw [hPc x hx, hm] at h
    have : (Subgroup.zpowers x).index = m := by omega
    rw [this]; exact hm3
  obtain ⟨j, hj⟩ := MulAction.exists_smul_eq ↥Q ((hPp u' hu'3).toSylow (hidx u' hu'3))
    ((hPp q' hq'3).toSylow (hidx q' hq'3))
  have hsub : MulAut.conj j • Subgroup.zpowers u' = Subgroup.zpowers q' := by
    have := congrArg (fun P : Sylow 3 ↥Q => (P : Subgroup ↥Q)) hj
    simpa [Sylow.coe_subgroup_smul] using this
  have hqmem : q' ∈ MulAut.conj j • Subgroup.zpowers u' := by rw [hsub]; exact Subgroup.mem_zpowers q'
  rw [Subgroup.pointwise_smul_def] at hqmem
  obtain ⟨t, ht, htq⟩ := hqmem
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
  refine ⟨(j : K), j.2, (k % 3).toNat, ?_⟩
  have h1 : u' ^ k = u' ^ ((k % 3).toNat) := by
    have h := zpow_mod_orderOf u' k
    rw [hu'3] at h
    push_cast at h
    rw [← h, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
  have h2 : q = ((j * u' ^ ((k % 3).toNat) * j⁻¹ : ↥Q) : K) := by
    rw [← h1]
    have := congrArg Subtype.val htq
    simpa [MulAut.conj_apply] using this.symm
  rw [h2]
  simp [hu']

theorem map_normalizer_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (S : Subgroup G) :
    (Subgroup.normalizer (S : Set G)).map e.toMonoidHom =
      Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup G') : Set G') := by
  refine le_antisymm (Subgroup.le_normalizer_map _) ?_
  intro y hy
  obtain ⟨x, rfl⟩ := e.surjective y
  refine ⟨x, ?_, rfl⟩
  show x ∈ Subgroup.normalizer (S : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro s
  have h1 := Subgroup.mem_normalizer_iff.1 hy (e s)
  have e1 : e s ∈ S.map e.toMonoidHom ↔ s ∈ S :=
    ⟨fun ⟨t, ht, hts⟩ => by rwa [← e.injective hts], fun hs => ⟨s, hs, rfl⟩⟩
  have e2 : e x * e s * (e x)⁻¹ ∈ S.map e.toMonoidHom ↔ x * s * x⁻¹ ∈ S := by
    rw [← map_inv, ← map_mul, ← map_mul]
    exact ⟨fun ⟨t, ht, hts⟩ => by rwa [← e.injective hts], fun hs => ⟨_, hs, rfl⟩⟩
  rw [← e1, ← e2]
  exact h1

theorem minimal_map_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') {N A : Subgroup G}
    (hmin : ∀ A' : Subgroup G, N ≤ A' → A' ≤ A → A' = N ∨ A' = A) :
    ∀ A' : Subgroup G', N.map e.toMonoidHom ≤ A' → A' ≤ A.map e.toMonoidHom →
      A' = N.map e.toMonoidHom ∨ A' = A.map e.toMonoidHom := by
  intro A' h1 h2
  have e1 : A'.comap e.toMonoidHom ≥ N := fun x hx => h1 ⟨x, hx, rfl⟩
  have e2 : A'.comap e.toMonoidHom ≤ A := fun x hx => by
    obtain ⟨t, ht, hte⟩ := h2 hx
    rwa [← e.injective hte]
  have hc : (A'.comap e.toMonoidHom).map e.toMonoidHom = A' :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective A'
  rcases hmin _ e1 e2 with h | h
  · left; rw [← hc, h]
  · right; rw [← hc, h]

theorem sylow_conj_mem {K : Type*} [Group K] [Finite K] {U V : Subgroup K} (hU : IsPGroup 2 U)
    (hV : IsPGroup 2 V) (hUi : ¬ 2 ∣ U.index) (hVi : ¬ 2 ∣ V.index) :
    ∃ g0 : K, ∀ x : K, x ∈ V ↔ g0⁻¹ * x * g0 ∈ U := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g0, hg0⟩ := MulAction.exists_smul_eq K (hU.toSylow hUi) (hV.toSylow hVi)
  refine ⟨g0, fun x => ?_⟩
  have h : MulAut.conj g0 • U = V := by
    have := congrArg (fun P : Sylow 2 K => (P : Subgroup K)) hg0
    simpa [Sylow.coe_subgroup_smul] using this
  rw [← h, Subgroup.pointwise_smul_def]
  constructor
  · rintro ⟨u, hu, rfl⟩
    show g0⁻¹ * (g0 * u * g0⁻¹) * g0 ∈ U
    rw [show g0⁻¹ * (g0 * u * g0⁻¹) * g0 = u by group]
    exact hu
  · intro hx
    exact ⟨g0⁻¹ * x * g0, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

section KLevel

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.ClassicalInvolution.WeakCT
  CFSG.AGLEmbeddingD2.McLaughlin.Lie

variable {K : Type} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {M : ℕ} {Y : Type} [Group Y] {π : K →* Y}

theorem not_exists_aut_of_noConj (h : BorelQuotient D n H π M) (hH : ∀ k, H k = ⊥)
    (h6 : ∀ k, Nat.card (rankOne D.rootGroup k) = 6)
    (h3 : ∀ k, ∃ x ∈ D.rootGroup (Pi.single k 1), ∃ y ∈ D.rootGroup (-Pi.single k 1),
      (x * y) ^ 3 = 1 ∧ x * y ≠ 1)
    {i j : Fin D.rank} (hij : i ≠ j) (hcart : D.cartan i j = 0)
    {xi yi xj yj : K} (hxi : xi ∈ D.rootGroup (Pi.single i 1))
    (hyi : yi ∈ D.rootGroup (-Pi.single i 1)) (hxj : xj ∈ D.rootGroup (Pi.single j 1))
    (hyj : yj ∈ D.rootGroup (-Pi.single j 1)) (hi3 : (xi * yi) ^ 3 = 1) (hi1 : xi * yi ≠ 1)
    (hj3 : (xj * yj) ^ 3 = 1) (hj1 : xj * yj ≠ 1)
    (hnot : xj * yj ∉ Subgroup.zpowers (xi * yi))
    (hnoconj : ∀ k, ∀ x ∈ D.rootGroup (Pi.single k 1), ∀ y ∈ D.rootGroup (-Pi.single k 1),
      (x * y) ^ 3 = 1 → x * y ≠ 1 → ∀ g : K, ∀ e : ℕ,
        g * (x * y) ^ e * g⁻¹ ≠ xi * yi * (xj * yj))
    (φ : K ≃* K) : φ (xi * yi) ≠ xi * yi * (xj * yj) := by
  intro hφ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU2 : IsPGroup 2 (posUnipotent D) := isPGroup_iSup_pos h.extras h.pGroup
  have hidx : ¬ 2 ∣ (posUnipotent D).index := h.not_dvd_index
  have hNU : Subgroup.normalizer (posUnipotent D : Set K) = borel D H :=
    le_antisymm (fun k hk => CFSG.ClassicalInvolution.WeakCT.normalizer_posUnipotent_le_borel h.ct h.extras hk)
      (CFSG.LieType.Steinberg.borel_le_normalizer_posUnipotent h.ct)
  have hU2' : IsPGroup 2 ((posUnipotent D).map φ.toMonoidHom) := hU2.map _
  have hidx' : ¬ 2 ∣ ((posUnipotent D).map φ.toMonoidHom).index := by
    have h1 := Subgroup.index_map_equiv (posUnipotent D) φ
    rw [show φ.toMonoidHom = (φ : K →* K) from rfl, h1]; exact hidx
  obtain ⟨g0, hg0⟩ := sylow_conj_mem hU2 hU2' hidx hidx'
  let ψ : K ≃* K := φ.trans (MulAut.conj g0⁻¹)
  have hψx : ∀ x, ψ x = g0⁻¹ * φ x * g0 := fun x => by
    show (MulAut.conj g0⁻¹) (φ x) = _
    simp [MulAut.conj_apply]
  have hψU : (posUnipotent D).map ψ.toMonoidHom = posUnipotent D := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      have : φ u ∈ (posUnipotent D).map φ.toMonoidHom := ⟨u, hu, rfl⟩
      rw [hg0] at this
      show ψ u ∈ _
      rw [hψx]; exact this
    · intro hx
      have h1 : g0 * x * g0⁻¹ ∈ (posUnipotent D).map φ.toMonoidHom := by
        rw [hg0]
        rw [show g0⁻¹ * (g0 * x * g0⁻¹) * g0 = x by group]; exact hx
      obtain ⟨u, hu, hue⟩ := h1
      refine ⟨u, hu, ?_⟩
      show ψ u = x
      rw [hψx]
      have : φ u = g0 * x * g0⁻¹ := hue
      rw [this]; group
  have hψB : (borel D H).map ψ.toMonoidHom = borel D H := by
    rw [← hNU, map_normalizer_equiv ψ, hψU]
  obtain ⟨Q, hQ, hclass⟩ := exists_qnode h.ct h.extras
  obtain ⟨hBQi, hLQi, hneQi, hminQi⟩ := hQ i
  have hBA : borel D H ≤ (Q i).map ψ.toMonoidHom := hψB ▸ Subgroup.map_mono hBQi
  have hAne : (Q i).map ψ.toMonoidHom ≠ borel D H := by
    intro heq
    apply hneQi
    apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
    rw [heq, hψB]
  have hAmin : ∀ A' : Subgroup K, borel D H ≤ A' → A' ≤ (Q i).map ψ.toMonoidHom →
      A' = borel D H ∨ A' = (Q i).map ψ.toMonoidHom := by
    have := minimal_map_equiv ψ hminQi
    rw [hψB] at this
    exact this
  obtain ⟨k, hk⟩ := hclass _ hBA hAne hAmin
  set w : K := xi * yi * (xj * yj) with hw
  have hLi : ∀ k : Fin D.rank, ∀ x ∈ D.rootGroup (Pi.single k 1), ∀ y ∈ D.rootGroup (-Pi.single k 1),
      x * y ∈ rankOne D.rootGroup k := fun k x hx y hy =>
    Subgroup.mul_mem _ (le_sup_left (b := D.rootGroup (-Pi.single k 1)) hx)
      (le_sup_right (a := D.rootGroup (Pi.single k 1)) hy)
  have hui : xi * yi ∈ Q i := hLQi (hLi i xi hxi yi hyi)
  have hψu : ψ (xi * yi) ∈ Q k := by
    have : ψ (xi * yi) ∈ (Q i).map ψ.toMonoidHom := ⟨_, hui, rfl⟩
    rw [hk] at this; exact this
  have hψeq : ψ (xi * yi) = g0⁻¹ * w * g0 := by rw [hψx, hφ]
  obtain ⟨xk, hxk, yk, hyk, hk3, hk1⟩ := h3 k
  obtain ⟨hBQk, hLQk, hneQk, hminQk⟩ := hQ k
  have hBU : borel D H = posUnipotent D := by
    have : (⨆ i, H i) = ⊥ := by simp [hH]
    show (⨆ i, H i) ⊔ posUnipotent D = posUnipotent D
    rw [this, bot_sup_eq]
  have hLB : ¬ rankOne D.rootGroup k ≤ borel D H := by
    intro hle
    have hdvd : 6 ∣ Nat.card (borel D H) := h6 k ▸ Subgroup.card_dvd_of_le hle
    rw [hBU] at hdvd
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hU2
    rw [hm] at hdvd
    have h3d : 3 ∣ 2 ^ m := (show 3 ∣ 6 by norm_num).trans hdvd
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d)
    omega
  have hBsup : borel D H ⊔ rankOne D.rootGroup k = Q k := by
    rcases hminQk _ le_sup_left (sup_le hBQk hLQk) with h1 | h1
    · exact absurd (le_sup_right.trans h1.le) hLB
    · exact h1
  have h9 : ¬ 9 ∣ Nat.card (Q k) := by
    rw [← hBsup]
    exact McLaughlin.Lie.not_nine_dvd_card_borel_sup_rankOne_of h.ct h.extras hH hU2 k (h6 k)
  have huk : orderOf (xk * yk) = 3 := orderOf_eq_prime hk3 hk1
  have hcomm : (xi * yi) * (xj * yj) = (xj * yj) * (xi * yi) :=
    commutes_rankOne_of_cartan_eq_zero h.extras hij hcart _ (hLi i xi hxi yi hyi) _
      (hLi j xj hxj yj hyj)
  have hw3 : w ^ 3 = 1 := by
    rw [hw, (show Commute (xi * yi) (xj * yj) from hcomm).mul_pow, hi3, hj3, mul_one]
  have hw1 : w ≠ 1 := by
    intro h1
    apply hnot
    have : xj * yj = (xi * yi)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  have hq3 : orderOf (g0⁻¹ * w * g0) = 3 := by
    have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective w
    rw [orderOf_eq_prime hw3 hw1] at this
    simpa [MulAut.conj_apply] using this
  obtain ⟨j', hj', e, hje⟩ := exists_conj_of_order_three h9
    (hLQk (hLi k xk hxk yk hyk)) (hψeq ▸ hψu) huk hq3
  refine hnoconj k xk hxk yk hyk hk3 hk1 (g0 * j') e ?_
  rw [mul_inv_rev]
  calc g0 * j' * (xk * yk) ^ e * (j'⁻¹ * g0⁻¹)
      = g0 * (j' * (xk * yk) ^ e * j'⁻¹) * g0⁻¹ := by group
    _ = g0 * (g0⁻¹ * w * g0) * g0⁻¹ := by rw [← hje]
    _ = w := by group

theorem orthSep_of_noConj [Finite Y] (h : BorelQuotient D n H π M) (hinj : Function.Injective π)
    (hH : ∀ k, H k = ⊥) (h6 : ∀ k, Nat.card (rankOne D.rootGroup k) = 6)
    (h3 : ∀ k, ∃ x ∈ D.rootGroup (Pi.single k 1), ∃ y ∈ D.rootGroup (-Pi.single k 1),
      (x * y) ^ 3 = 1 ∧ x * y ≠ 1)
    {i j : Fin D.rank} (hij : i ≠ j) (hcart : D.cartan i j = 0)
    {xi yi xj yj : K} (hxi : xi ∈ D.rootGroup (Pi.single i 1))
    (hyi : yi ∈ D.rootGroup (-Pi.single i 1)) (hxj : xj ∈ D.rootGroup (Pi.single j 1))
    (hyj : yj ∈ D.rootGroup (-Pi.single j 1)) (hi3 : (xi * yi) ^ 3 = 1) (hi1 : xi * yi ≠ 1)
    (hj3 : (xj * yj) ^ 3 = 1) (hj1 : xj * yj ≠ 1)
    (hnot : xj * yj ∉ Subgroup.zpowers (xi * yi))
    (hnoconj : ∀ k, ∀ x ∈ D.rootGroup (Pi.single k 1), ∀ y ∈ D.rootGroup (-Pi.single k 1),
      (x * y) ^ 3 = 1 → x * y ≠ 1 → ∀ g : K, ∀ e : ℕ,
        g * (x * y) ^ e * g⁻¹ ≠ xi * yi * (xj * yj)) :
    OrthSep D π i j := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨hcart, hij, xi, hxi, yi, hyi, xj, hxj, yj, hyj, ?_, ?_, ?_, ?_⟩
  · exact orderOf_eq_prime (by rw [← map_pow, hi3, map_one])
      (fun h1 => hi1 (hinj (by rw [h1, map_one])))
  · exact orderOf_eq_prime (by rw [← map_pow, hj3, map_one])
      (fun h1 => hj1 (hinj (by rw [h1, map_one])))
  · intro hm
    obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.1 hm
    apply hnot
    exact ⟨t, hinj (by rw [map_zpow, ht])⟩
  · intro φ hφ
    let e : K ≃* Y := MulEquiv.ofBijective π ⟨hinj, h.surj⟩
    have he : ∀ k, e k = π k := fun k => rfl
    let φ' : K ≃* K := (e.trans φ).trans e.symm
    refine not_exists_aut_of_noConj h hH h6 h3 hij hcart hxi hyi hxj hyj hi3 hi1 hj3 hj1 hnot
      hnoconj φ' (hinj ?_)
    have h1 : e (φ' (xi * yi)) = φ (π (xi * yi)) := by
      show e (e.symm (φ (e (xi * yi)))) = _
      rw [MulEquiv.apply_symm_apply]; rfl
    rw [← he, h1, hφ]
    simp only [map_mul]

end KLevel

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
