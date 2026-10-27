module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.Transv
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627L32Data

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

theorem kl_comm_check : ∀ u v h k : V3, h ⬝ᵥ u = 0 ∧ k ⬝ᵥ v = 0 ∧ u ≠ 0 ∧ h ≠ 0 ∧ v ≠ 0 ∧
    k ≠ 0 ∧ tvMat u h ≠ tvMat v k ∧ tvMat u h * tvMat v k = tvMat v k * tvMat u h →
      u = v ∨ h = k := by
  decide +kernel

theorem kl_tvMat_transpose : ∀ u h : V3, (tvMat u h).transpose = tvMat h u := by
  decide +kernel

theorem kl_τ_val (g : GL32) :
    ((L32Insp.τ g : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = (g⁻¹ : GL32).val.transpose :=
  CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut_matrix 3 (ZMod 2) g

theorem kl_τ_tvGL (u h : V3) (hu : h ⬝ᵥ u = 0) :
    L32Insp.τ (tvGL u h hu) = tvGL h u (by rwa [dotProduct_comm]) := by
  apply Units.ext
  rw [kl_τ_val]
  have hinv : (tvGL u h hu)⁻¹ = tvGL u h hu := inv_eq_of_mul_eq_one_right (tvGL_mul_self u h hu)
  rw [hinv]
  exact kl_tvMat_transpose u h

theorem kl_klein_elements {S : Subgroup GL32} (hS : Nat.card S = 4)
    (hsq : ∀ g ∈ S, g ^ 2 = 1) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a ∧
      ∀ g ∈ S, g = 1 ∨ g = a ∨ g = b ∨ g = a * b := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial S := Finite.one_lt_card_iff_nontrivial.1 (by rw [hS]; norm_num)
  obtain ⟨⟨a, haS⟩, ha1⟩ := exists_ne (1 : S)
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haord : orderOf a = 2 := orderOf_eq_prime (hsq a haS) ha1'
  have hlt : zpowers a < S := by
    refine lt_of_le_of_ne (zpowers_le.2 haS) fun h => ?_
    have h3 := Nat.card_zpowers a
    rw [haord, h, hS] at h3
    exact absurd h3 (by norm_num)
  obtain ⟨b, hbS, hbn⟩ := SetLike.exists_of_lt hlt
  have hb1 : b ≠ 1 := fun h => hbn (h ▸ one_mem _)
  have hba : b ≠ a := fun h => hbn (h ▸ mem_zpowers a)
  have ha2 : a * a = 1 := by rw [← pow_two]; exact hsq a haS
  have hb2 : b * b = 1 := by rw [← pow_two]; exact hsq b hbS
  have hab2 : a * b * (a * b) = 1 := by rw [← pow_two]; exact hsq _ (mul_mem haS hbS)
  have hcomm : a * b = b * a := by
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab2).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [inv_eq_of_mul_eq_one_right ha2, inv_eq_of_mul_eq_one_right hb2]
  refine ⟨a, haS, b, hbS, ha1', hb1, hba.symm, hcomm, ?_⟩
  have hab_ne1 : a * b ≠ 1 := fun h => hbn (by
    have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_mem_iff.2 (mem_zpowers a))
  have hab_nea : a * b ≠ a := fun h => hb1 (by simpa using h)
  have hab_neb : a * b ≠ b := fun h => ha1' (by simpa using h)
  have hTcard : ({1, a, b, a * b} : Finset GL32).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨ha1'.symm, hb1.symm, hab_ne1.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hba.symm, hab_nea.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact hab_neb.symm),
      Finset.card_singleton]
  have hT : (↑({1, a, b, a * b} : Finset GL32) : Set GL32) = (S : Set GL32) := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · intro g hg
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact one_mem S
      · exact haS
      · exact hbS
      · exact mul_mem haS hbS
    · rw [Set.ncard_coe_finset, hTcard, ← Nat.card_coe_set_eq]
      exact hS.le
  intro g hg
  have : g ∈ (↑({1, a, b, a * b} : Finset GL32) : Set GL32) := hT ▸ hg
  simpa using this

theorem klein_classification {S : Subgroup GL32} (hS : Nat.card S = 4)
    (hsq : ∀ g ∈ S, g ^ 2 = 1) :
    ∃ p : V3, p ≠ 0 ∧ (S = Spt p ∨ S = (Spt p).map L32Insp.τ.toMonoidHom) := by
  obtain ⟨a, haS, b, hbS, ha1, hb1, hab, hcomm, hall⟩ := kl_klein_elements hS hsq
  obtain ⟨u, h, hu, hu0, h0, rfl⟩ := involution_eq_tvGL a (hsq a haS) ha1
  obtain ⟨v, k, hv, hv0, k0, rfl⟩ := involution_eq_tvGL b (hsq b hbS) hb1
  have hMat : tvMat u h * tvMat v k = tvMat v k * tvMat u h := congrArg Units.val hcomm
  have hne : tvMat u h ≠ tvMat v k := fun e => hab (Units.ext e)
  rcases kl_comm_check u v h k ⟨hu, hv, hu0, h0, hv0, k0, hne, hMat⟩ with huv | hhk
  · subst huv
    refine ⟨u, hu0, Or.inl ?_⟩
    have hle : S ≤ Spt u := by
      intro g hg
      rcases hall g hg with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact tv_tvGL_mem_Spt u h hu
      · exact tv_tvGL_mem_Spt u k hv
      · exact mul_mem (tv_tvGL_mem_Spt u h hu) (tv_tvGL_mem_Spt u k hv)
    exact eq_of_le_of_card_ge hle (by rw [Spt_card hu0, hS])
  · subst hhk
    refine ⟨h, h0, Or.inr ?_⟩
    have hmem : ∀ (x : V3) (hx : h ⬝ᵥ x = 0),
        tvGL x h hx ∈ (Spt h).map L32Insp.τ.toMonoidHom := fun x hx =>
      ⟨tvGL h x (by rwa [dotProduct_comm]), tv_tvGL_mem_Spt h x _, kl_τ_tvGL h x _⟩
    have hle : S ≤ (Spt h).map L32Insp.τ.toMonoidHom := by
      intro g hg
      rcases hall g hg with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact hmem u hu
      · exact hmem v hv
      · exact mul_mem (hmem u hu) (hmem v hv)
    have hcard := Subgroup.card_map_of_injective (K := Spt h) (f := L32Insp.τ.toMonoidHom)
      L32Insp.τ.injective
    exact eq_of_le_of_card_ge hle (by rw [hcard, Spt_card h0, hS])

@[expose] def kl_l : GL32 :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide, by decide⟩

theorem kl_l_pow_three : kl_l ^ 3 = 1 := by
  have h : ((kl_l : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * kl_l * kl_l = 1 := by decide
  rw [pow_three']
  exact Units.ext h

theorem kl_l_ne_one : kl_l ≠ 1 := fun h => by
  have := congrArg Units.val h
  revert this
  decide

theorem kl_orderOf_l : orderOf kl_l = 3 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime kl_l_pow_three kl_l_ne_one

theorem kl_exists_conj_mem_zpowers {l : GL32} (hl : l ^ 3 = 1) :
    ∃ g : GL32, g * l * g⁻¹ ∈ zpowers kl_l := by
  by_cases hl1 : l = 1
  · exact ⟨1, by simp [hl1]⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsyl : ∀ y : GL32, orderOf y = 3 → ¬ 3 ∣ (zpowers y).index := fun y hy h => by
    have := card_mul_index (zpowers y)
    rw [Nat.card_zpowers, hy, L32Insp.card_GL] at this
    omega
  have hp : ∀ y : GL32, orderOf y = 3 → IsPGroup 3 (zpowers y) := fun y hy =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  have hol : orderOf l = 3 := orderOf_eq_prime hl hl1
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GL32 ((hp l hol).toSylow (hsyl l hol))
    ((hp kl_l kl_orderOf_l).toSylow (hsyl kl_l kl_orderOf_l))
  refine ⟨g, ?_⟩
  have h := smul_mem_pointwise_smul l (MulAut.conj g)
    (((hp l hol).toSylow (hsyl l hol) : Sylow 3 GL32) : Subgroup GL32) (by simp)
  rw [← Sylow.coe_subgroup_smul, hg] at h
  simpa [MulAut.smul_def] using h

theorem kl_exists_conj_zpowers_eq {l : GL32} (hl : orderOf l = 3) :
    ∃ g : GL32, zpowers (g * l * g⁻¹) = zpowers kl_l := by
  have hl3 : l ^ 3 = 1 := by
    have := pow_orderOf_eq_one l
    rwa [hl] at this
  obtain ⟨g, hg⟩ := kl_exists_conj_mem_zpowers hl3
  refine ⟨g, Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hg) ?_⟩
  have hord : orderOf (g * l * g⁻¹) = 3 :=
    (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective l).trans hl
  rw [Nat.card_zpowers, Nat.card_zpowers, kl_orderOf_l, hord]

theorem kl_det_eq_one (y : GL32) : (y : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
  have h : ∀ u : (ZMod 2)ˣ, (u : ZMod 2) = 1 := by decide
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  exact h _

theorem kl_comm_l_check : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2),
    M.det = 1 ∧ M * ((kl_l : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      ((kl_l : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M →
      M = 1 ∨ M = ((kl_l : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∨
        M = ((kl_l : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          ((kl_l : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  decide +kernel

theorem kl_comm_l (y : GL32) (hy : y * kl_l = kl_l * y) :
    y = 1 ∨ y = kl_l ∨ y = kl_l ^ 2 := by
  have hM : (y : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        ((kl_l : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      ((kl_l : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        (y : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    congrArg Units.val hy
  rcases kl_comm_l_check _ ⟨kl_det_eq_one y, hM⟩ with h | h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Or.inl (Units.ext h))
  · rw [pow_two]
    exact Or.inr (Or.inr (Units.ext h))

theorem centralizer_order3 {d : GL32} (hd : orderOf d = 3) {y : GL32} (hy : y * d = d * y) :
    y ∈ zpowers d := by
  obtain ⟨g, hg⟩ := kl_exists_conj_zpowers_eq hd
  have hc : g * y * g⁻¹ * (g * d * g⁻¹) = g * d * g⁻¹ * (g * y * g⁻¹) := by
    calc g * y * g⁻¹ * (g * d * g⁻¹) = g * (y * d) * g⁻¹ := by group
      _ = g * (d * y) * g⁻¹ := by rw [hy]
      _ = g * d * g⁻¹ * (g * y * g⁻¹) := by group
  have hl : kl_l ∈ zpowers (g * d * g⁻¹) := hg ▸ mem_zpowers kl_l
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hl
  have hcl : g * y * g⁻¹ * kl_l = kl_l * (g * y * g⁻¹) := by
    rw [← hk]
    exact (Commute.zpow_right (show Commute (g * y * g⁻¹) (g * d * g⁻¹) from hc) k).eq
  have hy' : g * y * g⁻¹ ∈ zpowers (g * d * g⁻¹) := by
    rw [hg]
    rcases kl_comm_l _ hcl with h | h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_zpowers _
    · rw [h]
      exact pow_mem (mem_zpowers _) 2
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hy'
  refine mem_zpowers_iff.2 ⟨j, ?_⟩
  rw [conj_zpow] at hj
  have h1 : g * d ^ j * g⁻¹ = g * y * g⁻¹ := hj
  have h2 : g * d ^ j = g * y := mul_right_cancel h1
  exact mul_left_cancel h2

theorem kl_card_modEq_three_of_iterate {α : Type*} [Finite α] (f : α → α)
    (hf : ∀ a, f (f (f a)) = a) : Nat.card α ≡ Nat.card {a // f a = a} [MOD 3] := by
  classical
  have := Fintype.ofFinite α
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) (by
    funext a
    exact hf a)
  rw [Nat.card_eq_fintype_card]
  have h : Nat.card {a // f a = a} = Fintype.card (Function.fixedPoints f) :=
    (Nat.card_eq_fintype_card (α := Function.fixedPoints f))
  rw [h]
  exact key

theorem kl_eq_one_of_commute {N : Subgroup GL32} (hN : IsPGroup 2 N) {l v : GL32}
    (hl : orderOf l = 3) (hv : v ∈ N) (hc : v * l = l * v) : v = 1 := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvz : v ∈ zpowers l := centralizer_order3 hl hc
  have hdvd : orderOf v ∣ 3 := by
    have := orderOf_dvd_natCard (⟨v, hvz⟩ : zpowers l)
    rwa [Subgroup.orderOf_mk, Nat.card_zpowers, hl] at this
  obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.1 hN ⟨v, hv⟩
  rw [Subgroup.orderOf_mk] at hm
  rw [hm] at hdvd
  have h1 : 2 ^ m = 1 := (Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 3)).eq_one_of_dvd hdvd
  exact orderOf_eq_one_iff.1 (hm.trans h1)

theorem kl_card_modEq_one {N : Subgroup GL32} {l : GL32} (hl : orderOf l = 3)
    (hN : IsPGroup 2 N) (hlN : l ∈ normalizer (N : Set GL32)) : Nat.card N ≡ 1 [MOD 3] := by
  have h3 : l * l * l = 1 := by
    rw [← pow_three']
    have := pow_orderOf_eq_one l
    rwa [hl] at this
  let f : N → N := fun v => ⟨l * v * l⁻¹, (mem_normalizer_iff.1 hlN v).1 v.2⟩
  have hf : ∀ v, f (f (f v)) = v := fun v => by
    apply Subtype.ext
    show l * (l * (l * v * l⁻¹) * l⁻¹) * l⁻¹ = v
    calc _ = (l * l * l) * v * (l * l * l)⁻¹ := by group
      _ = v := by rw [h3]; simp
  have hfix1 : ∀ a : N, f a = a → a = 1 := fun a ha =>
    Subtype.ext (kl_eq_one_of_commute hN hl a.2 (by
      have := congrArg Subtype.val ha
      calc (a : GL32) * l = (l * a * l⁻¹) * l := by rw [show l * a * l⁻¹ = a from this]
        _ = l * a := by group))
  have hcard : Nat.card {a // f a = a} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ((hfix1 x x.2).trans (hfix1 y y.2).symm)⟩, ⟨⟨1, ?_⟩⟩⟩
    exact Subtype.ext (by show l * 1 * l⁻¹ = 1; group)
  have hmod := kl_card_modEq_three_of_iterate f hf
  rwa [hcard] at hmod

theorem kl_card_eq_four {S : Subgroup GL32} (hS : IsPGroup 2 S) (hne : S ≠ ⊥) {d : GL32}
    (hd : orderOf d = 3) (hdS : d ∈ normalizer (S : Set GL32)) : Nat.card S = 4 := by
  have hmod := kl_card_modEq_one hd hS hdS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hS
  have hdvd : Nat.card S ∣ 168 := L32Insp.card_GL ▸ card_subgroup_dvd_card S
  have hn3 : n ≤ 3 := by
    by_contra hn3
    have : 2 ^ 4 ∣ 168 := (pow_dvd_pow 2 (by omega)).trans (hn ▸ hdvd)
    norm_num at this
  have hne1 : Nat.card S ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq S h)
  rw [hn] at hmod hne1 ⊢
  interval_cases n
  · exact absurd (by norm_num) hne1
  · exact absurd hmod (by decide)
  · norm_num
  · exact absurd hmod (by decide)

theorem kl_sq_eq_one_of_card_four {S : Subgroup GL32} (hS : IsPGroup 2 S) (hS4 : Nat.card S = 4)
    {d : GL32} (hd : orderOf d = 3) (hdS : d ∈ normalizer (S : Set GL32)) :
    ∀ g ∈ S, g ^ 2 = 1 := by
  intro g hg
  by_contra hg2
  have hdvd : orderOf g ∣ 2 ^ 2 := by
    have := orderOf_dvd_natCard (⟨g, hg⟩ : S)
    rw [Subgroup.orderOf_mk, hS4] at this
    simpa using this
  have hord : orderOf g = 4 := by
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    interval_cases i
    · exfalso
      apply hg2
      have hg1 : g = 1 := orderOf_eq_one_iff.1 (by simpa using hi')
      rw [hg1]
      simp
    · exfalso
      apply hg2
      have := pow_orderOf_eq_one g
      rwa [hi', pow_one] at this
    · simpa using hi'
  have hg4 : g ^ 4 = 1 := by
    have := pow_orderOf_eq_one g
    rwa [hord] at this
  have hd3 : d * d * d = 1 := by
    rw [← pow_three']
    have := pow_orderOf_eq_one d
    rwa [hd] at this
  have hd4 : d * d * (d * d) = d :=
    calc d * d * (d * d) = (d * d * d) * d := by group
      _ = d := by rw [hd3]; simp
  have hzS : zpowers g = S :=
    eq_of_le_of_card_ge (zpowers_le.2 hg) (by rw [Nat.card_zpowers, hord, hS4])
  have hcS : d * g * d⁻¹ ∈ zpowers g := hzS ▸ (mem_normalizer_iff.1 hdS g).1 hg
  have hnc : ¬ g * d = d * g := fun hc => hg2 (by
    rw [kl_eq_one_of_commute hS hd hg hc]
    simp)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hcS
  have hk4 : g ^ (k % 4) = d * g * d⁻¹ := by
    have h := zpow_mod_orderOf g k
    rw [hord] at h
    rw [← hk, ← h]
    norm_num
  have hk4' : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases hk4' with h | h | h | h
  · rw [h, zpow_zero] at hk4
    apply hg2
    have : g = 1 := by
      calc g = d⁻¹ * (d * g * d⁻¹) * d := by group
        _ = 1 := by rw [← hk4]; group
    rw [this]
    simp
  · rw [h, zpow_one] at hk4
    exact hnc (by
      calc g * d = d * g * d⁻¹ * d := by rw [← hk4]
        _ = d * g := by group)
  · rw [h] at hk4
    have hk2 : g ^ 2 = d * g * d⁻¹ := by simpa using hk4
    apply hg2
    have h1 : (d * g * d⁻¹) ^ 2 = 1 := by
      rw [← hk2, ← pow_mul]
      exact hg4
    have h2 : d * g ^ 2 * d⁻¹ = 1 := by rw [← conj_pow]; exact h1
    calc g ^ 2 = d⁻¹ * (d * g ^ 2 * d⁻¹) * d := by group
      _ = 1 := by rw [h2]; group
  · rw [h] at hk4
    have hk3 : g ^ 3 = d * g * d⁻¹ := by simpa using hk4
    have h1 : d * (d * g * d⁻¹) * d⁻¹ = g := by
      calc d * (d * g * d⁻¹) * d⁻¹ = d * g ^ 3 * d⁻¹ := by rw [hk3]
        _ = (d * g * d⁻¹) ^ 3 := conj_pow.symm
        _ = (g ^ 3) ^ 3 := by rw [hk3]
        _ = g := by
          calc (g ^ 3) ^ 3 = g ^ 4 * g ^ 4 * g := by group
            _ = g := by rw [hg4]; simp
    have h1' : d * d * g = g * (d * d) := by
      calc d * d * g = (d * (d * g * d⁻¹) * d⁻¹) * (d * d) := by group
        _ = g * (d * d) := by rw [h1]
    have hc2 : Commute g (d * d) := h1'.symm
    have := hc2.mul_right hc2
    rw [hd4] at this
    exact hnc this.eq

theorem two_group_normalized_card {S : Subgroup GL32} (hS : IsPGroup 2 S) (hne : S ≠ ⊥) {d : GL32}
    (hd : orderOf d = 3) (hdS : d ∈ normalizer (S : Set GL32)) :
    Nat.card S = 4 ∧ ∀ g ∈ S, g ^ 2 = 1 := by
  have hS4 := kl_card_eq_four hS hne hd hdS
  exact ⟨hS4, kl_sq_eq_one_of_card_four hS hS4 hd hdS⟩

@[expose] def kl_E (i j : Fin 3) (hij : i ≠ j) : GL32 :=
  Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2))

theorem kl_closure_E_eq_top :
    Subgroup.closure {g : GL32 | ∃ (i j : Fin 3) (hij : i ≠ j), g = kl_E i j hij} = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : g = Matrix.SpecialLinearGroup.toGL
      ⟨(g : Matrix (Fin 3) (Fin 3) (ZMod 2)), kl_det_eq_one g⟩ := Units.ext rfl
  rw [hg]
  refine Matrix.SpecialLinearGroup.diagonal_transvection_induction'
    (fun M => Matrix.SpecialLinearGroup.toGL M ∈
      Subgroup.closure {g : GL32 | ∃ (i j : Fin 3) (hij : i ≠ j), g = kl_E i j hij}) _ ?_ ?_ ?_
  · intro i j hij c hc
    have hc1 : c = 1 := by
      rcases tv_zmod_two c with h | h
      · exact absurd h hc
      · exact h
    subst hc1
    have h1 : Matrix.SpecialLinearGroup.diag2n hij (1 : ZMod 2) hc = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.diag2n_coe]
      simp
    show Matrix.SpecialLinearGroup.toGL _ ∈ _
    rw [h1, map_one]
    exact one_mem _
  · intro i j hij a
    rcases tv_zmod_two a with rfl | rfl
    · rw [Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one]
      exact one_mem _
    · exact subset_closure ⟨i, j, hij, rfl⟩
  · intro A B hA hB
    show Matrix.SpecialLinearGroup.toGL (A * B) ∈ _
    rw [map_mul]
    exact mul_mem hA hB

@[expose] def kl_x1 : GL32 := kl_E 0 1 (by decide)

@[expose] def kl_x2 : GL32 := kl_E 1 2 (by decide)

@[expose] def kl_x3 : GL32 := kl_E 2 0 (by decide)

theorem kl_x_sq_check : ∀ i j : Fin 3, ∀ hij : i ≠ j,
    ((kl_E i j hij : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (kl_E i j hij : GL32) = 1 := by
  decide +kernel

theorem kl_x_ne_check : ∀ i j : Fin 3, ∀ hij : i ≠ j,
    ((kl_E i j hij : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 1 := by
  decide +kernel

theorem kl_E_sq (i j : Fin 3) (hij : i ≠ j) : kl_E i j hij ^ 2 = 1 := by
  rw [pow_two]
  exact Units.ext (kl_x_sq_check i j hij)

theorem kl_E_ne_one (i j : Fin 3) (hij : i ≠ j) : kl_E i j hij ≠ 1 := fun h =>
  kl_x_ne_check i j hij (congrArg Units.val h)

theorem kl_E02 : kl_E 0 2 (by decide) = kl_x1 * kl_x2 * (kl_x1 * kl_x2) :=
  Units.ext (by decide +kernel)

theorem kl_E10 : kl_E 1 0 (by decide) = kl_x2 * kl_x3 * (kl_x2 * kl_x3) :=
  Units.ext (by decide +kernel)

theorem kl_E21 : kl_E 2 1 (by decide) = kl_x3 * kl_x1 * (kl_x3 * kl_x1) :=
  Units.ext (by decide +kernel)

theorem kl_closure_three :
    Subgroup.closure ({kl_x1, kl_x2, kl_x3} : Set GL32) = ⊤ := by
  rw [eq_top_iff, ← kl_closure_E_eq_top, Subgroup.closure_le]
  rintro g ⟨i, j, hij, rfl⟩
  have h1 : kl_x1 ∈ Subgroup.closure ({kl_x1, kl_x2, kl_x3} : Set GL32) :=
    subset_closure (by simp)
  have h2 : kl_x2 ∈ Subgroup.closure ({kl_x1, kl_x2, kl_x3} : Set GL32) :=
    subset_closure (by simp)
  have h3 : kl_x3 ∈ Subgroup.closure ({kl_x1, kl_x2, kl_x3} : Set GL32) :=
    subset_closure (by simp)
  have hcases : ∀ i j : Fin 3, i ≠ j → (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
      (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 1) := by decide
  rcases hcases i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  · exact h1
  · exact h2
  · exact h3
  · rw [kl_E02]
    exact mul_mem (mul_mem h1 h2) (mul_mem h1 h2)
  · rw [kl_E10]
    exact mul_mem (mul_mem h2 h3) (mul_mem h2 h3)
  · rw [kl_E21]
    exact mul_mem (mul_mem h3 h1) (mul_mem h3 h1)

theorem kl_conj_check : ∀ u h : V3, h ⬝ᵥ u = 0 ∧ u ≠ 0 ∧ h ≠ 0 →
    ∃ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M.det = 1 ∧
      M * tvMat u h = ((kl_x1 : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M := by
  decide +kernel

theorem kl_exists_conj_x1 {s : GL32} (hs : s ^ 2 = 1) (hs1 : s ≠ 1) :
    ∃ c : GL32, c * s * c⁻¹ = kl_x1 := by
  obtain ⟨u, h, hu, hu0, h0, rfl⟩ := involution_eq_tvGL s hs hs1
  obtain ⟨M, hM, hMc⟩ := kl_conj_check u h ⟨hu, hu0, h0⟩
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨M, hM⟩, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  exact Units.ext hMc

theorem kl_exists_conj {s s' : GL32} (hs : s ^ 2 = 1) (hs1 : s ≠ 1) (hs' : s' ^ 2 = 1)
    (hs1' : s' ≠ 1) : ∃ g : GL32, g * s * g⁻¹ = s' := by
  obtain ⟨c, hc⟩ := kl_exists_conj_x1 hs hs1
  obtain ⟨c', hc'⟩ := kl_exists_conj_x1 hs' hs1'
  refine ⟨c'⁻¹ * c, ?_⟩
  calc c'⁻¹ * c * s * (c'⁻¹ * c)⁻¹ = c'⁻¹ * (c * s * c⁻¹) * c' := by group
    _ = c'⁻¹ * (c' * s' * c'⁻¹) * c' := by rw [hc, ← hc']
    _ = s' := by group

theorem kl_conj_inv_sq {x : GL32} (hx : x ^ 2 = 1) (c : GL32) : (c⁻¹ * x * c) ^ 2 = 1 := by
  have hx' : x * x = 1 := by rw [← pow_two]; exact hx
  calc (c⁻¹ * x * c) ^ 2 = c⁻¹ * (x * x) * c := by rw [pow_two]; group
    _ = 1 := by rw [hx']; group

theorem kl_conj_inv_ne {x : GL32} (hx : x ≠ 1) (c : GL32) : c⁻¹ * x * c ≠ 1 := fun h =>
  hx (by
    calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group)

theorem involutions_generate {s : GL32} (hs : s ^ 2 = 1) (hs1 : s ≠ 1) :
    ∃ g₁ g₂ : GL32, Subgroup.closure {s, g₁ * s * g₁⁻¹, g₂ * s * g₂⁻¹} = ⊤ := by
  obtain ⟨c, hc⟩ := kl_exists_conj_x1 hs hs1
  obtain ⟨g₁, hg₁⟩ := kl_exists_conj hs hs1 (kl_conj_inv_sq (kl_E_sq 1 2 (by decide)) c)
    (kl_conj_inv_ne (kl_E_ne_one 1 2 (by decide)) c)
  obtain ⟨g₂, hg₂⟩ := kl_exists_conj hs hs1 (kl_conj_inv_sq (kl_E_sq 2 0 (by decide)) c)
    (kl_conj_inv_ne (kl_E_ne_one 2 0 (by decide)) c)
  refine ⟨g₁, g₂, ?_⟩
  have hs' : s = c⁻¹ * kl_x1 * c := by
    rw [← hc]
    group
  have himg : (MulAut.conj c⁻¹).toMonoidHom '' ({kl_x1, kl_x2, kl_x3} : Set GL32) =
      {c⁻¹ * kl_x1 * c, c⁻¹ * kl_x2 * c, c⁻¹ * kl_x3 * c} := by
    simp [Set.image_insert_eq, MulAut.conj_apply]
  rw [hg₁, hg₂, hs']
  have h2 : c⁻¹ * kl_E 1 2 (by decide) * c = c⁻¹ * kl_x2 * c := rfl
  have h3 : c⁻¹ * kl_E 2 0 (by decide) * c = c⁻¹ * kl_x3 * c := rfl
  rw [h2, h3, ← himg, ← MonoidHom.map_closure, kl_closure_three,
    Subgroup.map_top_of_surjective _ (MulAut.conj c⁻¹).surjective]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
