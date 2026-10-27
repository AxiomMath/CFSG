module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.D4Levi

public section

open scoped Pointwise

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.LieOut CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.AGLEmbeddingD2.McLaughlin.Lie

section Generic

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
@[expose] def threePrimeSub (J : Subgroup G) : Subgroup G :=
  Subgroup.closure {g | g ∈ J ∧ Nat.Coprime (orderOf g) 3}

omit [Finite G] in
theorem mem_threePrimeSub_of {J : Subgroup G} {g : G} (hg : g ∈ J) (h : Nat.Coprime (orderOf g) 3) :
    g ∈ threePrimeSub J :=
  Subgroup.subset_closure ⟨hg, h⟩

omit [Finite G] in
theorem conj_mem_threePrimeSub {J : Subgroup G} {g : G} (hg : g ∈ J) {o : G}
    (ho : o ∈ threePrimeSub J) : g * o * g⁻¹ ∈ threePrimeSub J := by
  refine Subgroup.closure_induction (p := fun o _ => g * o * g⁻¹ ∈ threePrimeSub J) ?_ ?_ ?_ ?_ ho
  · rintro s ⟨hs, hs3⟩
    refine mem_threePrimeSub_of (J.mul_mem (J.mul_mem hg hs) (J.inv_mem hg)) ?_
    have : orderOf (g * s * g⁻¹) = orderOf s := by
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective s
      simpa [MulAut.conj_apply] using this
    rw [this]; exact hs3
  · simp
  · intro a b _ _ ha hb
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]; exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ ha

omit [Finite G] in
theorem map_threePrimeSub_le {J : Subgroup G} (ψ : G ≃* G) (hψ : ∀ g ∈ J, ψ g ∈ J) :
    (threePrimeSub J).map ψ.toMonoidHom ≤ threePrimeSub J := by
  rw [threePrimeSub, MonoidHom.map_closure]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨s, ⟨hs, hs3⟩, rfl⟩
  refine mem_threePrimeSub_of (hψ s hs) ?_
  rw [orderOf_injective ψ.toMonoidHom ψ.injective s]
  exact hs3

end Generic

section OneNode

variable {G : Type} [Group G] [Finite G]

theorem card_closure_pair_dvd_six {x y : G} (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1)
    (hxy3 : (x * y) ^ 3 = 1) (hxy1 : x * y ≠ 1) :
    Nat.card (Subgroup.closure {x, y} : Subgroup G) ∣ 6 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq, hx2])
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq, hy2])
  set C : Subgroup G := Subgroup.zpowers (x * y) with hC
  set X : Subgroup G := Subgroup.zpowers x with hX
  have hCc : Nat.card C = 3 := by
    rw [hC, Nat.card_zpowers]; exact orderOf_eq_prime hxy3 hxy1
  have hXc : Nat.card X ∣ 2 := by
    rw [hX, Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hx2
  have hxN : X ≤ Subgroup.normalizer (C : Set G) := by
    rw [hX, Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨k, rfl⟩ := hn
    have h1 : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
      rw [mul_inv_rev, hxi, hyi]
      calc x * (x * y) * x = x ^ 2 * y * x := by simp only [sq, mul_assoc]
        _ = y * x := by rw [hx2, one_mul]
    have : x * (x * y) ^ k * x⁻¹ = ((x * y)⁻¹) ^ k := by
      have h2 := map_zpow (MulAut.conj x) (x * y) k
      simp only [MulAut.conj_apply] at h2
      rw [h2, h1]
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) k
  have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hxN
  have hD : Nat.card (C ⊔ X : Subgroup G) ∣ 6 := by
    have h1 : Nat.card (C ⊔ X : Subgroup G) ∣ Nat.card C * Nat.card X := Dvd.intro _ h
    rw [hCc] at h1
    exact h1.trans (Nat.mul_dvd_mul_left 3 hXc)
  refine (Subgroup.card_dvd_of_le ?_).trans hD
  rw [Subgroup.closure_le]
  intro z hz
  rcases hz with rfl | hz
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · rw [Set.mem_singleton_iff] at hz
    have : y = x * (x * y) := by
      rw [← mul_assoc, ← sq, hx2, one_mul]
    rw [hz, this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))

theorem card_inf_threePrimeSub_eq_three {J R T : Subgroup G} {x y : G}
    (hRJ : R ≤ J) (hJR : J ≤ Subgroup.normalizer (R : Set G)) (hR2 : IsPGroup 2 R)
    (hxJ : x ∈ J) (hyJ : y ∈ J) (hTJ : T ≤ J)
    (hJ : J ≤ R ⊔ (T ⊔ Subgroup.closure {x, y}))
    (hTx : ∀ t ∈ T, t * x = x * t) (hTy : ∀ t ∈ T, t * y = y * t) (hTc : Nat.card T ∣ 3)
    (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1) (hxy3 : (x * y) ^ 3 = 1) (hxy1 : x * y ≠ 1)
    {E : Subgroup G} (hEJ : E ≤ J) (hE : Nat.card E = 9) :
    Nat.card (E ⊓ threePrimeSub J : Subgroup G) = 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set cl : Subgroup G := Subgroup.closure {x, y} with hcl
  set C : Subgroup G := Subgroup.zpowers (x * y) with hC
  have hCc : Nat.card C = 3 := by rw [hC, Nat.card_zpowers]; exact orderOf_eq_prime hxy3 hxy1
  have hclJ : cl ≤ J := (Subgroup.closure_le _).2 (by
    intro z hz
    rcases hz with rfl | hz
    · exact hxJ
    · rw [Set.mem_singleton_iff] at hz; rw [hz]; exact hyJ)
  have hxycl : x * y ∈ cl := Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl rfl))
    (Subgroup.subset_closure (Or.inr rfl))
  have hCcl : C ≤ cl := by rw [hC, Subgroup.zpowers_le]; exact hxycl
  have hcl6 := card_closure_pair_dvd_six hx2 hy2 hxy3 hxy1
  obtain ⟨a, ha⟩ : ∃ a, Nat.card R = 2 ^ a := IsPGroup.iff_card.mp hR2
  have hTcl : ∀ t ∈ T, ∀ n ∈ cl, n * t = t * n := by
    intro t ht n hn
    have hle : cl ≤ Subgroup.centralizer ({t} : Set G) := by
      rw [hcl, Subgroup.closure_le]
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      rcases hz with rfl | hz
      · exact hTx h ht
      · rw [Set.mem_singleton_iff] at hz; subst hz; exact hTy h ht
    have := Subgroup.mem_centralizer_iff.mp (hle hn) t (Set.mem_singleton t)
    exact this.symm
  have hTNcl : T ≤ Subgroup.normalizer (cl : Set G) := le_normalizer_of_commute fun a ha b hb =>
    hTcl b hb a ha
  have hTNR : T ≤ Subgroup.normalizer (R : Set G) := hTJ.trans hJR
  have hclNR : cl ≤ Subgroup.normalizer (R : Set G) := hclJ.trans hJR
  set W₀ : Subgroup G := R ⊔ cl with hW₀
  have hW₀J : W₀ ≤ J := sup_le hRJ hclJ
  have hTNW : T ≤ Subgroup.normalizer (W₀ : Set G) := by
    rw [hW₀, sup_comm]
    exact le_normalizer_sup_of hTNcl hTNR
  have hJNW : J ≤ Subgroup.normalizer (W₀ : Set G) := by
    refine hJ.trans (sup_le ?_ (sup_le hTNW ?_))
    · exact (le_sup_left : R ≤ W₀).trans Subgroup.le_normalizer
    · exact (le_sup_right : cl ≤ W₀).trans Subgroup.le_normalizer
  have hW₀c : Nat.card W₀ ∣ 2 ^ a * 6 := by
    have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hclNR
    have h1 : Nat.card W₀ ∣ Nat.card R * Nat.card cl := by
      rw [hW₀, sup_comm] at *
      exact Dvd.intro _ h
    rw [ha] at h1
    exact h1.trans (Nat.mul_dvd_mul_left _ hcl6)
  have hJWT : J ≤ W₀ ⊔ T := hJ.trans (sup_le (le_sup_of_le_left le_sup_left)
    (sup_le le_sup_right (le_sup_of_le_left le_sup_right)))
  have hJc : Nat.card J ∣ 2 ^ a * 18 := by
    have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hTNW
    have h1 : Nat.card (W₀ ⊔ T : Subgroup G) ∣ Nat.card W₀ * Nat.card T := Dvd.intro _ h
    have h2 : Nat.card W₀ * Nat.card T ∣ 2 ^ a * 6 * 3 := Nat.mul_dvd_mul hW₀c hTc
    have h3 : (2 ^ a * 6 * 3 : ℕ) = 2 ^ a * 18 := by ring
    rw [h3] at h2
    exact (Subgroup.card_dvd_of_le hJWT).trans (h1.trans h2)
  have hOW : threePrimeSub J ≤ W₀ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨hgJ, hg3⟩
    have hgWT : g ∈ (W₀ : Set G) * (T : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left W₀ T hTNW]
      exact hJWT hgJ
    obtain ⟨w, hw, t, ht, rfl⟩ := hgWT
    have ht3 : t ^ 3 = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 ((Subgroup.orderOf_dvd_natCard T ht).trans hTc)
    have hw1 : t * w * t⁻¹ ∈ W₀ := ((Subgroup.mem_normalizer_iff.1 (hTNW ht)) w).1 hw
    have hw2 : t * (t * w * t⁻¹) * t⁻¹ ∈ W₀ :=
      ((Subgroup.mem_normalizer_iff.1 (hTNW ht)) _).1 hw1
    have hg3W : (w * t) ^ 3 ∈ W₀ := by
      have : (w * t) ^ 3 = w * (t * w * t⁻¹) * (t * (t * w * t⁻¹) * t⁻¹) * t ^ 3 := by
        simp only [pow_succ, pow_zero, one_mul]; group
      rw [this, ht3, mul_one]
      exact W₀.mul_mem (W₀.mul_mem hw hw1) hw2
    have hmem : w * t ∈ Subgroup.zpowers ((w * t) ^ 3) := mem_zpowers_pow_iff.2 hg3.symm
    exact (Subgroup.zpowers_le.2 hg3W) hmem
  have hxO : x ∈ threePrimeSub J := mem_threePrimeSub_of hxJ
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hx2) (by norm_num))
  have hyO : y ∈ threePrimeSub J := mem_threePrimeSub_of hyJ
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hy2) (by norm_num))
  have hxyO : x * y ∈ threePrimeSub J := Subgroup.mul_mem _ hxO hyO
  have hxyJ : x * y ∈ J := J.mul_mem hxJ hyJ
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE]; norm_num)
  let E' : Subgroup J := E.subgroupOf J
  have hE'c : Nat.card E' = 9 := by
    rw [← hE]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv
  have hE'3 : IsPGroup 3 E' := IsPGroup.of_card (n := 2) (by rw [hE'c]; norm_num)
  have hidx : ¬ 3 ∣ E'.index := by
    intro h3
    have h := Subgroup.card_mul_index E'
    rw [hE'c] at h
    have hd : 9 * E'.index ∣ 2 ^ a * 18 := h ▸ hJc
    have h' : E'.index ∣ 2 ^ a * 2 := by
      have : 9 * E'.index ∣ 9 * (2 ^ a * 2) := by
        rw [show 9 * (2 ^ a * 2) = 2 ^ a * 18 by ring]; exact hd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have h32 : 3 ∣ 2 ^ (a + 1) := by rw [pow_succ]; exact h3.trans h'
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h32
    omega
  let sE : Sylow 3 J := hE'3.toSylow hidx
  let C' : Subgroup J := C.subgroupOf J
  have hCJ : C ≤ J := hCcl.trans hclJ
  have hC'c : Nat.card C' = 3 := by
    rw [← hCc]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCJ).toEquiv
  have hC'3 : IsPGroup 3 C' := IsPGroup.of_card (n := 1) (by rw [hC'c]; norm_num)
  obtain ⟨sC, hsC⟩ := hC'3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J sE sC
  have hsub : ((g • sE : Sylow 3 J) : Subgroup J) = (sC : Subgroup J) := by rw [hg]
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hsub
  have hz : (⟨x * y, hxyJ⟩ : J) ∈ (sC : Subgroup J) :=
    hsC (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers _))
  rw [← hsub] at hz
  obtain ⟨c, hc, hcx⟩ := hz
  have hx0 : (g : G) * (c : G) * (g : G)⁻¹ = x * y := by
    have := congrArg Subtype.val hcx
    simpa [MulAut.conj_apply] using this
  have hcE : (c : G) ∈ E := Subgroup.mem_subgroupOf.mp (show c ∈ E' from hc)
  have hcg : (c : G) = (g : G)⁻¹ * (x * y) * (g : G) := by rw [← hx0]; group
  have hmemE : (g : G)⁻¹ * (x * y) * (g : G) ∈ E := by rw [← hcg]; exact hcE
  have hmemO : (g : G)⁻¹ * (x * y) * (g : G) ∈ threePrimeSub J := by
    have := conj_mem_threePrimeSub (J.inv_mem g.2) hxyO
    simpa using this
  have hne : (g : G)⁻¹ * (x * y) * (g : G) ≠ 1 := by
    intro h
    apply hxy1
    have := congrArg (fun z => (g : G) * z * (g : G)⁻¹) h
    simpa [mul_assoc] using this
  have hIE : IsPGroup 3 (E ⊓ threePrimeSub J : Subgroup G) := hE3.to_le inf_le_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hIE
  have hdvd : Nat.card (E ⊓ threePrimeSub J : Subgroup G) ∣ 2 ^ a * 6 :=
    (Subgroup.card_dvd_of_le (inf_le_right.trans hOW)).trans hW₀c
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Subgroup.card_eq_one] at hk
    have : (g : G)⁻¹ * (x * y) * (g : G) ∈ (E ⊓ threePrimeSub J : Subgroup G) :=
      Subgroup.mem_inf.2 ⟨hmemE, hmemO⟩
    rw [hk] at this
    exact hne (Subgroup.mem_bot.1 this)
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have h9 : 9 ∣ 3 ^ k := ⟨3 ^ (k - 2), by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_add]; congr 1; omega⟩
    have h96 : 9 ∣ 2 ^ a * 6 := h9.trans (hk ▸ hdvd)
    have hcop : Nat.Coprime 9 (2 ^ a) := Nat.Coprime.pow_right _ (by norm_num)
    have := hcop.dvd_of_dvd_mul_left h96
    omega
  rw [hk, show k = 1 by omega, pow_one]

end OneNode

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
