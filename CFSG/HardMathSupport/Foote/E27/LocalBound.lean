module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.Open

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
private theorem card_centralizer_conj (g t : X) :
    Nat.card (Subgroup.centralizer ({g * t * g⁻¹} : Set X)) =
      Nat.card (Subgroup.centralizer ({t} : Set X)) := by
  refine Nat.card_congr ?_
  exact
    { toFun := fun c => ⟨g⁻¹ * c * g, by
        have hc := Subgroup.mem_centralizer_singleton_iff.mp c.2
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := congrArg (fun y => g⁻¹ * y * g) hc
        simpa [mul_assoc] using this⟩
      invFun := fun d => ⟨g * d * g⁻¹, by
        have hd := Subgroup.mem_centralizer_singleton_iff.mp d.2
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := congrArg (fun y => g * y * g⁻¹) hd
        simpa [mul_assoc] using this⟩
      left_inv := fun c => by ext; simp [mul_assoc]
      right_inv := fun d => by ext; simp [mul_assoc] }

omit [Finite X] in
private theorem map_card_aux (C : Subgroup X) (S : Subgroup C) :
    Nat.card (S.map C.subtype) = Nat.card S :=
  Subgroup.card_map_of_injective C.subtype_injective

private theorem sylow_aux {G : Type} [Group G] [Finite G] (S : Sylow 3 G) :
    ∃ i, ¬ 3 ∣ i ∧ Nat.card G = Nat.card S * i := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨(S : Subgroup G).index, Sylow.not_dvd_index S, (Subgroup.card_mul_index _).symm⟩

private theorem not_conj_to_z (R T : Subgroup X) (z : X) (hR27 : Nat.card R = 27)
    (hsyl : ∃ S : Sylow 3 ↥(Subgroup.centralizer ({z} : Set X)),
      (S : Subgroup _).map (Subgroup.centralizer ({z} : Set X)).subtype = R)
    (h3c : ∀ t ∈ T, t ≠ 1 → ∃ S : Sylow 3 X,
      (S : Subgroup X) ≤ Subgroup.centralizer ({t} : Set X))
    (h81 : 81 ∣ Nat.card X) : ∀ g : X, ∀ t ∈ T, t ≠ 1 → g * t * g⁻¹ ≠ z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro g t ht ht1 hgt
  obtain ⟨S, hS⟩ := hsyl
  have hSc : Nat.card S = 27 := by
    have := map_card_aux (Subgroup.centralizer ({z} : Set X)) (S : Subgroup _)
    rw [hS, hR27] at this
    exact this.symm
  obtain ⟨i, hi3, hCz⟩ := sylow_aux S
  rw [hSc] at hCz
  obtain ⟨S₁, hS₁⟩ := h3c t ht ht1
  obtain ⟨i₁, hi₁, hX⟩ := sylow_aux S₁
  have hcop : Nat.Coprime 81 i₁ := by
    have := Nat.Coprime.pow_left 4 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hi₁)
    simpa using this
  have h81S : 81 ∣ Nat.card S₁ := by
    rw [hX] at h81
    exact hcop.dvd_of_dvd_mul_right h81
  have h81C : 81 ∣ Nat.card (Subgroup.centralizer ({t} : Set X)) :=
    h81S.trans (Subgroup.card_dvd_of_le hS₁)
  have hcc := card_centralizer_conj g t
  rw [hgt] at hcc
  rw [← hcc, hCz] at h81C
  omega


private theorem main_aux (R T : Subgroup X) (z : X) (hR : IsElemAbelian 3 R) (hR27 : Nat.card R = 27)
    (hTR : T ≤ R) (hT9 : Nat.card T = 9) (hzR : z ∈ R) (hzT : z ∉ T)
    (hfus : ∀ r ∈ R, r ∉ T → ∃ n ∈ Subgroup.normalizer (R : Set X),
      n * r * n⁻¹ ∈ Subgroup.zpowers z)
    (hnc : ∀ g : X, ∀ t ∈ T, t ≠ 1 → g * t * g⁻¹ ≠ z) :
    3 ^ 5 ∣ Nat.card (Subgroup.normalizer (R : Set X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.normalizer (R : Set X) with hN
  have hz1 : z ≠ 1 := fun h => hzT (h ▸ T.one_mem)
  have hz3 : z ^ 3 = 1 := hR.2 z hzR
  let f : N →* Equiv.Perm X := (MulAut.toPerm X).comp ((MulAut.conj : X →* MulAut X).comp N.subtype)
  let _ : MulAction N X := MulAction.compHom X f
  have hsmul : ∀ (n : N) (x : X), n • x = n * x * (n : X)⁻¹ := fun n x => rfl
  have hNR : ∀ n : N, ∀ r ∈ R, (n : X) * r * (n : X)⁻¹ ∈ R := by
    intro n r hr
    exact (Subgroup.mem_normalizer_iff.mp n.2 r).mp hr
  have hconj1 : ∀ (n w : X), n * w * n⁻¹ = 1 → w = 1 := by
    intro n w h
    calc w = n⁻¹ * (n * w * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  have hmem_orb : ∀ (a x : X), x ∈ MulAction.orbit N a ↔ ∃ n : N, (n : X) * a * (n : X)⁻¹ = x := by
    intro a x
    rw [MulAction.mem_orbit_iff]
    rfl
  have hsub : ∀ w : X, (w = z ∨ w = z⁻¹) → MulAction.orbit N w ⊆ (R : Set X) \ (T : Set X) := by
    intro w hw x hx
    obtain ⟨n, rfl⟩ := (hmem_orb w x).mp hx
    have hwR : w ∈ R := by
      rcases hw with rfl | rfl
      exacts [hzR, R.inv_mem hzR]
    have hw1 : w ≠ 1 := by
      rcases hw with rfl | rfl
      · exact hz1
      · simpa using hz1
    refine ⟨hNR n w hwR, fun hxT => ?_⟩
    have hx1 : (n : X) * w * (n : X)⁻¹ ≠ 1 := by
      intro h
      exact hw1 (hconj1 _ _ h)
    have hzT' : (n : X) * z * (n : X)⁻¹ ∈ T := by
      rcases hw with rfl | rfl
      · exact hxT
      · have := T.inv_mem hxT
        convert this using 1
        group
    have hz1' : (n : X) * z * (n : X)⁻¹ ≠ 1 := by
      intro h
      exact hz1 (hconj1 _ _ h)
    exact hnc ((n : X)⁻¹) _ hzT' hz1' (by group)
  have hcover : ∀ r ∈ (R : Set X) \ (T : Set X),
      r ∈ MulAction.orbit N z ∪ MulAction.orbit N z⁻¹ := by
    rintro r ⟨hr, hrT⟩
    obtain ⟨n, hn, hnr⟩ := hfus r hr hrT
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hnr
    have hkz : z ^ k = z ^ (k % 3) := by
      have e : z ^ k = z ^ (k % 3 + 3 * (k / 3)) := by congr 1; omega
      have : z ^ (3 : ℤ) = 1 := by exact_mod_cast hz3
      rw [e, zpow_add, zpow_mul, this, one_zpow, mul_one]
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    have hrn : r = (n : X)⁻¹ * (n * r * n⁻¹) * ((n : X)⁻¹)⁻¹ := by group
    rcases hk3 with h | h | h
    · rw [h, zpow_zero] at hkz
      exfalso
      apply hrT
      have : n * r * n⁻¹ = 1 := by rw [← hk, hkz]
      have : r = 1 := hconj1 _ _ this
      rw [this]; exact T.one_mem
    · rw [h, zpow_one] at hkz
      left
      refine (hmem_orb z r).mpr ⟨⟨(n : X)⁻¹, N.inv_mem hn⟩, ?_⟩
      show (n : X)⁻¹ * z * ((n : X)⁻¹)⁻¹ = r
      rw [hrn, ← hk, hkz]
    · rw [h] at hkz
      right
      refine (hmem_orb z⁻¹ r).mpr ⟨⟨(n : X)⁻¹, N.inv_mem hn⟩, ?_⟩
      show (n : X)⁻¹ * z⁻¹ * ((n : X)⁻¹)⁻¹ = r
      have hz2 : z ^ (2 : ℤ) = z⁻¹ := by
        have : z ^ 2 * z = 1 := by rw [← pow_succ]; exact hz3
        rw [zpow_ofNat]
        exact eq_inv_of_mul_eq_one_left this
      rw [hrn, ← hk, hkz, hz2]
  set O1 := MulAction.orbit N z with hO1
  set O2 := MulAction.orbit N z⁻¹ with hO2
  have hRT : ((R : Set X) \ (T : Set X)).ncard = 18 := by
    have h1 : (T : Set X) ⊆ (R : Set X) := hTR
    rw [Set.ncard_sdiff h1]
    have hR' : (R : Set X).ncard = 27 := by rw [← Nat.card_coe_set_eq]; exact hR27
    have hT' : (T : Set X).ncard = 9 := by rw [← Nat.card_coe_set_eq]; exact hT9
    omega
  have hunion : ((R : Set X) \ (T : Set X)) = O1 ∪ O2 := by
    apply Set.Subset.antisymm
    · exact hcover
    · exact Set.union_subset (hsub z (Or.inl rfl)) (hsub z⁻¹ (Or.inr rfl))
  have hO2eq : O2 = (fun x : X => x⁻¹) '' O1 := by
    ext x
    rw [hO2, hO1, hmem_orb, Set.mem_image]
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨(n : X) * z * (n : X)⁻¹, (hmem_orb z _).mpr ⟨n, rfl⟩, ?_⟩
      group
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨n, rfl⟩ := (hmem_orb z y).mp hy
      exact ⟨n, by group⟩
  have hO2card : O2.ncard = O1.ncard := by
    rw [hO2eq, Set.ncard_image_of_injective _ inv_injective]
  have h9 : 9 ∣ O1.ncard := by
    by_cases hmem : z⁻¹ ∈ O1
    · have : O2 = O1 := MulAction.orbit_eq_iff.mpr hmem
      rw [this, Set.union_self] at hunion
      rw [hunion] at hRT
      rw [hRT]
      norm_num
    · have hdisj : Disjoint O1 O2 := by
        rw [Set.disjoint_left]
        intro x hx1 hx2
        apply hmem
        have e1 : MulAction.orbit N z = MulAction.orbit N x := (MulAction.orbit_eq_iff.mpr hx1).symm
        have e2 : MulAction.orbit N z⁻¹ = MulAction.orbit N x := (MulAction.orbit_eq_iff.mpr hx2).symm
        have : z⁻¹ ∈ MulAction.orbit N z⁻¹ := MulAction.mem_orbit_self _
        rw [e2, ← e1] at this
        exact this
      rw [hunion, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hO2card] at hRT
      omega
  have h27 : 27 ∣ Nat.card (MulAction.stabilizer N z) := by
    have hRN : R ≤ N := Subgroup.le_normalizer
    have hc : Nat.card (R.subgroupOf N) = 27 := by
      rw [← hR27]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv
    have hle : R.subgroupOf N ≤ MulAction.stabilizer N z := by
      intro n hn
      rw [MulAction.mem_stabilizer_iff, hsmul]
      have hnR : (n : X) ∈ R := Subgroup.mem_subgroupOf.mp hn
      have := hR.1.is_comm.comm ⟨(n : X), hnR⟩ ⟨z, hzR⟩
      have h2 : (n : X) * z = z * (n : X) := congrArg Subtype.val this
      rw [h2]; group
    rw [← hc]
    exact Subgroup.card_dvd_of_le hle
  have hfin : Nat.card (MulAction.orbit N z) * Nat.card (MulAction.stabilizer N z) =
      Nat.card N := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup N z)
  have h9' : 9 ∣ Nat.card O1 := by rw [Nat.card_coe_set_eq]; exact h9
  have := Nat.mul_dvd_mul h9' h27
  rw [hfin] at this
  simpa using this


theorem three_pow_five_dvd_card_normalizer
    (R T : Subgroup X) (z : X) (hR : CFSG.Open.IsElemAbelian 3 R) (hR27 : Nat.card R = 27)
    (hTR : T ≤ R) (hT9 : Nat.card T = 9) (hzR : z ∈ R) (hzT : z ∉ T)
    (hfus : ∀ r ∈ R, r ∉ T → ∃ n ∈ Subgroup.normalizer (R : Set X),
      n * r * n⁻¹ ∈ Subgroup.zpowers z)
    (hsyl : ∃ S : Sylow 3 ↥(Subgroup.centralizer ({z} : Set X)),
      (S : Subgroup _).map (Subgroup.centralizer ({z} : Set X)).subtype = R)
    (h3c : ∀ t ∈ T, t ≠ 1 → ∃ S : Sylow 3 X,
      (S : Subgroup X) ≤ Subgroup.centralizer ({t} : Set X))
    (h81 : 81 ∣ Nat.card X) : 3 ^ 5 ∣ Nat.card (Subgroup.normalizer (R : Set X)) :=
  main_aux R T z hR hR27 hTR hT9 hzR hzT hfus (not_conj_to_z R T z hR27 hsyl h3c h81)

theorem three_pow_five_dvd_card_mulAut (K : Subgroup X) [K.Normal]
    (hK : Subgroup.centralizer (K : Set X) = ⊥)
    (R T : Subgroup X) (z : X) (hR : CFSG.Open.IsElemAbelian 3 R) (hR27 : Nat.card R = 27)
    (hTR : T ≤ R) (hT9 : Nat.card T = 9) (hzR : z ∈ R) (hzT : z ∉ T)
    (hfus : ∀ r ∈ R, r ∉ T → ∃ n ∈ Subgroup.normalizer (R : Set X),
      n * r * n⁻¹ ∈ Subgroup.zpowers z)
    (hsyl : ∃ S : Sylow 3 ↥(Subgroup.centralizer ({z} : Set X)),
      (S : Subgroup _).map (Subgroup.centralizer ({z} : Set X)).subtype = R)
    (h3c : ∀ t ∈ T, t ≠ 1 → ∃ S : Sylow 3 X,
      (S : Subgroup X) ≤ Subgroup.centralizer ({t} : Set X))
    (h81 : 81 ∣ Nat.card X) : 3 ^ 5 ∣ Nat.card (MulAut K) := by
  have h5 := three_pow_five_dvd_card_normalizer R T z hR hR27 hTR hT9 hzR hzT hfus hsyl h3c h81
  let N := Subgroup.normalizer (R : Set X)
  let φ : N →* MulAut K := (MulAut.conjNormal : X →* MulAut K).comp N.subtype
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro n hn
    have h1 : MulAut.conjNormal (n : X) = (1 : MulAut K) := hn
    have hc : (n : X) ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have := congrArg (fun a : MulAut K => ((a ⟨k, hk⟩ : K) : X)) h1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc k * (n : X) = (n : X) * k * (n : X)⁻¹ * (n : X) := by rw [this]
        _ = (n : X) * k := by group
        _ = (n : X) * k := rfl
    rw [hK] at hc
    exact Subtype.ext (Subgroup.mem_bot.mp hc)
  have : Nat.card N ∣ Nat.card (MulAut K) := by
    have e : Nat.card N = Nat.card φ.range := Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
    rw [e]
    exact Subgroup.card_subgroup_dvd_card φ.range
  exact h5.trans this

end CFSG.HardMathSupport.Foote.E27
