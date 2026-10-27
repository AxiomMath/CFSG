module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YDihedral
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21Basic
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XSetting
import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G]

section Sylow

theorem exists_isSylowOf_le {p : ℕ} [Fact p.Prime] {Q K : Subgroup G} (hQ : IsPGroup p Q)
    (hQK : Q ≤ K) : ∃ P, IsSylowOf p P K ∧ Q ≤ P := by
  obtain ⟨P, hP⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(P : Subgroup K).map K.subtype, ⟨P, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hQK hx⟩, hP hx, rfl⟩

theorem exists_isSylowOf_normalized [Finite G] {p : ℕ} [Fact p.Prime] {T K : Subgroup G}
    (hT : IsPGroup p T)
    (hTK : T ≤ normalizer (K : Set G)) : ∃ R, IsSylowOf p R K ∧ T ≤ normalizer (R : Set G) := by
  obtain ⟨P, hP, hTP⟩ := exists_isSylowOf_le hT (le_sup_right : T ≤ K ⊔ T)
  have hM : K ⊔ T ≤ normalizer (K : Set G) := sup_le le_normalizer hTK
  refine ⟨P ⊓ K, hP.inf_of_le_normalizer le_sup_left hM, fun t ht => ?_⟩
  exact inf_le_normalizer_inf (mem_inf.mpr ⟨le_normalizer (hTP ht), hTK ht⟩)

end Sylow

theorem centralizer_le_normalizer [Finite G] {J : Subgroup G} (hJ : TightlyEmbedded J) {e : G}
    (heJ : e ∈ J) (he1 : e ≠ 1) (hee : e * e = 1) :
    centralizer ({e} : Set G) ≤ normalizer (J : Set G) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  StandardSubgroupAPI.centralizer_le_normalizer_of_mem_of_orderOf_eq_two hJ heJ
    (orderOf_eq_prime (by rw [pow_two]; exact hee) he1)

section Coprime

variable [Finite G]

theorem exists_mul_of_commutator_le {T K : Subgroup G} (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G)) (hc : ⁅T, K⁆ ≤ oddCoreIn K) {k : G} (hk : k ∈ K) :
    ∃ o ∈ oddCoreIn K, ∃ c ∈ K, c ∈ centralizer (T : Set G) ∧ k = o * c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := oddCoreIn K with hOdef
  have hOK : O ≤ K := oddCoreIn_le K
  have hKO : K ≤ normalizer (O : Set G) := le_normalizer_oddCoreIn K
  have hTO : T ≤ normalizer (O : Set G) := hTK.trans (normalizer_le_normalizer_oddCoreIn K)
  have hX : ∀ t ∈ T, ∀ x : G, k⁻¹ * x ∈ O → k⁻¹ * (t * x * t⁻¹) ∈ O := by
    intro t ht x hx
    have h1 : k⁻¹ * t * k * t⁻¹ ∈ O := by
      apply hc
      rw [commutator_comm]
      have := commutator_mem_commutator (K.inv_mem hk) ht
      simpa [commutatorElement_def] using this
    have h2 : t * (k⁻¹ * x) * t⁻¹ ∈ O := (mem_normalizer_iff.mp (hTO ht) _).mp hx
    have : k⁻¹ * (t * x * t⁻¹) = (k⁻¹ * t * k * t⁻¹) * (t * (k⁻¹ * x) * t⁻¹) := by group
    rw [this]
    exact O.mul_mem h1 h2
  let X := {x : G // k⁻¹ * x ∈ O}
  let act : MulAction T X :=
    { smul := fun t x => ⟨t * x.1 * t⁻¹, hX t t.2 x.1 x.2⟩
      one_smul := fun x => Subtype.ext (by change 1 * x.1 * 1⁻¹ = x.1; group)
      mul_smul := fun s t x => Subtype.ext (by
        change ((s * t : T) : G) * x.1 * ((s * t : T) : G)⁻¹ =
          (s : G) * ((t : G) * x.1 * (t : G)⁻¹) * (s : G)⁻¹
        rw [Subgroup.coe_mul]
        group) }
  have hcard : Nat.card X = Nat.card O := by
    refine Nat.card_congr
      { toFun := fun x => ⟨k⁻¹ * x.1, x.2⟩
        invFun := fun o => ⟨k * o.1, by simp⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun o => Subtype.ext (by simp) }
  have hodd : ¬ 2 ∣ Nat.card X := by
    rw [hcard]
    exact Nat.not_even_iff_odd.mpr (odd_card_oddCoreIn K) ∘ even_iff_two_dvd.mpr
  obtain ⟨x, hx⟩ := hT.nonempty_fixed_point_of_prime_not_dvd_card X hodd
  have hfix : ∀ t ∈ T, t * x.1 * t⁻¹ = x.1 := fun t ht =>
    congrArg Subtype.val (MulAction.mem_fixedPoints.mp hx ⟨t, ht⟩)
  have hxK : x.1 ∈ K := by
    have : x.1 = k * (k⁻¹ * x.1) := by group
    rw [this]
    exact K.mul_mem hk (hOK x.2)
  refine ⟨k * x.1⁻¹, ?_, x.1, hxK, ?_, by group⟩
  · have : k * x.1⁻¹ = x.1 * (k⁻¹ * x.1)⁻¹ * x.1⁻¹ := by group
    rw [this]
    exact (mem_normalizer_iff.mp (hKO hxK) _).mp (O.inv_mem x.2)
  · rw [mem_centralizer_iff]
    intro t ht
    calc t * x.1 = t * x.1 * t⁻¹ * t := by group
      _ = x.1 * t := by rw [hfix t ht]

theorem le_of_fourGroup {E O M : Subgroup G} (hE2 : ∀ e ∈ E, e * e = 1) (hE4 : Nat.card E = 4)
    (hO : Odd (Nat.card O)) (hEO : E ≤ normalizer (O : Set G))
    (hEM : ∀ e ∈ E, e ≠ 1 → O ⊓ centralizer ({e} : Set G) ≤ M) : O ≤ M := by
  rw [CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two E O (fun e => Subtype.ext (by rw [coe_pow, pow_two]; exact hE2 e e.2))
    (by rw [hE4]; norm_num) (Nat.not_even_iff_odd.mpr hO ∘ even_iff_two_dvd.mpr) hEO]
  refine iSup_le fun e => iSup_le fun he => hEM e e.2 ?_
  exact fun h => he (Subtype.ext h)

theorem le_normalizer_of_commutator_le {K J T E : Subgroup G} (hJ : TightlyEmbedded J)
    (hT : IsPGroup 2 T) (hTJ : T ≤ J) (hTK : T ≤ normalizer (K : Set G))
    (hc : ⁅T, K⁆ ≤ oddCoreIn K) (hET : E ≤ T) (hE2 : ∀ e ∈ E, e * e = 1)
    (hE4 : Nat.card E = 4) : K ≤ normalizer (J : Set G) := by
  have hT1 : T ≠ ⊥ := by
    intro h
    have hE1 : E = ⊥ := le_bot_iff.mp (h ▸ hET)
    rw [hE1, card_bot] at hE4
    exact absurd hE4 (by norm_num)
  have hCT : centralizer (T : Set G) ≤ normalizer (J : Set G) :=
    centralizer_two_subgroup_le J T hJ hT hTJ hT1
  have hO : oddCoreIn K ≤ normalizer (J : Set G) := by
    refine le_of_fourGroup hE2 hE4 (odd_card_oddCoreIn K)
      (hET.trans (hTK.trans (normalizer_le_normalizer_oddCoreIn K))) fun e he he1 => ?_
    exact inf_le_right.trans (centralizer_le_normalizer hJ (hTJ (hET he)) he1 (hE2 e he))
  intro k hk
  obtain ⟨o, ho, c, -, hcT, rfl⟩ := exists_mul_of_commutator_le hT hTK hc hk
  exact mul_mem (hO ho) (hCT hcT)

end Coprime

section FourGroup

variable {a b : G}

@[expose] def fourGroup (a b : G) (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    Subgroup G where
  carrier := {1, a, b, a * b}
  one_mem' := by simp
  mul_mem' := by
    have ha_ab : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
    have hb_ab : b * (a * b) = a := by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]
    have hab_a : a * b * a = b := by rw [mul_assoc, ← hab, ha_ab]
    have hab_b : a * b * b = a := by rw [mul_assoc, hb, mul_one]
    have hab_sq : a * b * (a * b) = 1 := by rw [← mul_assoc, hab_a, hb]
    have hba : b * a = a * b := hab.symm
    intro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp [ha, hb, hba, ha_ab, hb_ab, hab_a, hab_b, hab_sq]
  inv_mem' := by
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    have hab' : (a * b)⁻¹ = a * b := by rw [mul_inv_rev, ha', hb', hab]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> simp [ha', hb', hab']

theorem mem_fourGroup {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a} {x : G} :
    x ∈ fourGroup a b ha hb hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := Iff.rfl

theorem isElemAbelian_fourGroup (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    CFSG.Open.IsElemAbelian 2 (fourGroup a b ha hb hab) := by
  have hab_sq : a * b * (a * b) = 1 := by
    rw [mul_assoc, ← mul_assoc b, ← hab, mul_assoc, hb, mul_one, ha]
  have hsq : ∀ x ∈ fourGroup a b ha hb hab, x * x = 1 := by
    intro x hx
    rcases mem_fourGroup.mp hx with rfl | rfl | rfl | rfl
    · exact mul_one 1
    · exact ha
    · exact hb
    · exact hab_sq
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => by rw [pow_two]; exact hsq x hx⟩
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  simp only [coe_mul]
  have hxy := hsq _ ((fourGroup a b ha hb hab).mul_mem hx hy)
  calc x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left hxy
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by
      rw [inv_eq_of_mul_eq_one_right (hsq y hy), inv_eq_of_mul_eq_one_right (hsq x hx)]

theorem card_fourGroup (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hne : a ≠ b) : Nat.card (fourGroup a b ha hb hab) = 4 := by
  classical
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hne
    have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_right ha]
  have haab : a ≠ a * b := by
    intro h
    apply hb1
    have := congrArg (a⁻¹ * ·) h
    simpa using this.symm
  have hbab : b ≠ a * b := by
    intro h
    apply ha1
    have := congrArg (· * b⁻¹) h
    simpa using this.symm
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  change Set.ncard ({1, a, b, a * b} : Set G) = 4
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hbab]
  · simp [haab, hne]
  · simp [Ne.symm ha1, Ne.symm hb1, Ne.symm hab1]

end FourGroup

namespace IsDihedralRot

variable {U R : Subgroup G}

theorem exists_fourGroup [Finite G] (h : IsDihedralRot U R) :
    ∃ E : Subgroup G, E ≤ R ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  obtain ⟨z, hzU, hz1, hzz, -, hzc⟩ := h.exists_involution
  obtain ⟨s, hsR, hsU⟩ := h.exists_not_mem
  have hss := h.mul_self s hsR hsU
  have hsz : s * z = z * s := hzc s hsR
  have hne : s ≠ z := fun h' => hsU (h' ▸ hzU)
  have hs1 : s ≠ 1 := fun h' => hsU (h' ▸ U.one_mem)
  refine ⟨fourGroup s z hss hzz hsz, ?_, isElemAbelian_fourGroup hss hzz hsz,
    card_fourGroup hss hzz hsz hs1 hz1 hne⟩
  intro x hx
  rcases mem_fourGroup.mp hx with rfl | rfl | rfl | rfl
  · exact R.one_mem
  · exact hsR
  · exact h.le hzU
  · exact R.mul_mem hsR (h.le hzU)

theorem one_lt_pRank [Finite G] (h : IsDihedralRot U R) : 1 < CFSG.Open.pRank 2 R := by
  obtain ⟨E, hER, hE, hE4⟩ := h.exists_fourGroup
  exact CFSG.ComponentClassification.Asc76X.one_lt_pRank_of_fourGroup hER hE hE4

theorem not_isMulCommutative (h : IsDihedralRot U R) : ¬ IsMulCommutative R := by
  intro hc
  obtain ⟨s, hsR, hsU⟩ := h.exists_not_mem
  exact hsU (h.mem_of_commute hsR fun u hu =>
    congrArg Subtype.val (hc.is_comm.comm ⟨s, hsR⟩ ⟨u, h.le hu⟩))

theorem ne_bot (h : IsDihedralRot U R) : R ≠ ⊥ := by
  rintro rfl
  obtain ⟨s, hsR, hsU⟩ := h.exists_not_mem
  exact hsU ((mem_bot.mp hsR) ▸ U.one_mem)

theorem conj_eq_inv_of_centralizer [Finite G] (h : IsDihedralRot U R) {v : G}
    (hvR : v ∈ normalizer (R : Set G)) (hvv : v * v = 1)
    (hC : ∀ x ∈ R, x * v = v * x → x ∈ U ∧ x * x = 1) : ∀ u ∈ U, v * u * v⁻¹ = u⁻¹ := by
  have hvU : v ∈ normalizer (U : Set G) := h.normalizer_le hvR
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  set φ : G → G := fun u => v * u * v⁻¹ with hφ
  have hφU : ∀ u ∈ U, φ u ∈ U := fun u hu => (mem_normalizer_iff.mp hvU u).mp hu
  have hφφ : ∀ u, φ (φ u) = u := fun u => by
    simp only [hφ]
    calc v * (v * u * v⁻¹) * v⁻¹ = (v * v) * u * (v * v)⁻¹ := by group
      _ = u := by rw [hvv]; group
  have hφmul : ∀ x y, φ (x * y) = φ x * φ y := fun x y => by simp only [hφ]; group
  have hfix : ∀ u ∈ U, u * φ u * (u * φ u) = 1 := by
    intro u hu
    have h1 : (u * φ u) * v = v * (u * φ u) := by
      have : v * (u * φ u) * v⁻¹ = φ u * u := by
        simp only [hφ]
        calc v * (u * (v * u * v⁻¹)) * v⁻¹ = (v * u * v⁻¹) * ((v * v) * u * (v * v)⁻¹) := by
              group
          _ = v * u * v⁻¹ * u := by rw [hvv]; group
      have hc : φ u * u = u * φ u := h.commute_of_mem (hφU u hu) hu
      calc u * φ u * v = (v * (u * φ u) * v⁻¹) * v := by rw [this, hc]
        _ = v * (u * φ u) := by group
    exact (hC _ (h.le (U.mul_mem hu (hφU u hu))) h1).2
  obtain ⟨ρ, hρ, hρo⟩ := h.exists_gen
  have hρU : ρ ∈ U := hρ ▸ mem_zpowers ρ
  obtain ⟨z, hzU, hz1, hzz, hzuniq, hzc⟩ := h.exists_involution
  suffices hinv : φ ρ = ρ⁻¹ by
    intro u hu
    rw [← hρ] at hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have : φ (ρ ^ k) = φ ρ ^ k := by simp only [hφ]; rw [conj_zpow]
    rw [show v * ρ ^ k * v⁻¹ = φ (ρ ^ k) from rfl, this, hinv, inv_zpow]
  rcases hzuniq _ (U.mul_mem hρU (hφU ρ hρU)) (hfix ρ hρU) with h1 | h1
  · exact eq_inv_of_mul_eq_one_right h1
  exfalso
  have hφρ : φ ρ = ρ⁻¹ * z := by rw [← h1]; group
  have hzc' : ∀ y ∈ U, y * z = z * y := fun y hy => h.commute_of_mem hy hzU
  have hq4 := h.four_le
  obtain ⟨n, hn⟩ := (h.isPGroup.to_le h.le).exists_card_eq
  have hzρ : ∃ t : ℕ, Nat.card U = 2 * t ∧ z = ρ ^ t := by
    have h2 : 2 ∣ Nat.card U := by
      rw [hn]
      have : n ≠ 0 := by rintro rfl; rw [pow_zero] at hn; omega
      exact dvd_pow_self 2 this
    obtain ⟨t, ht⟩ := h2
    refine ⟨t, ht, ?_⟩
    have hzt : ρ ^ t ∈ U := U.pow_mem hρU t
    have hzt1 : ρ ^ t ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
    have hztt : ρ ^ t * ρ ^ t = 1 := by
      rw [← pow_add, ← two_mul, ← ht, ← hρo, pow_orderOf_eq_one]
    rcases hzuniq _ hzt hztt with h3 | h3
    · exact absurd h3 hzt1
    · exact h3.symm
  obtain ⟨t, ht, hzt⟩ := hzρ
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have hn2 : n = 2 := by
      have : 2 ≤ n := by
        by_contra h'
        have : n ≤ 1 := by omega
        have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
        omega
      omega
    rw [hn2] at hn
    have ht2 : t = 2 := by omega
    have hφρ' : φ ρ = ρ := by
      rw [hφρ, hzt, ht2]
      group
    have h3 : ρ * v = v * ρ := by
      calc ρ * v = (v * ρ * v⁻¹) * v := by rw [show v * ρ * v⁻¹ = φ ρ from rfl, hφρ']
        _ = v * ρ := by group
    exact h.gen_mul_self_ne_one hρo (hC ρ (h.le hρU) h3).2
  obtain ⟨c, hc⟩ : 4 ∣ t := by
    have : 8 ∣ Nat.card U := by
      rw [hn]
      exact (Nat.pow_dvd_pow 2 hn3 : 2 ^ 3 ∣ 2 ^ n)
    omega
  obtain ⟨s, hsR, hsU⟩ := h.exists_not_mem
  have hss : s * s = 1 := h.mul_self s hsR hsU
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hs'R : v * s * v⁻¹ ∈ R := (mem_normalizer_iff.mp hvR s).mp hsR
  have hs'U : v * s * v⁻¹ ∉ U := fun h' => hsU (by
    have := (mem_normalizer_iff.mp (inv_mem hvU) _).mp h'
    simpa [mul_assoc] using this)
  set u₀ := s * (v * s * v⁻¹) with hu₀
  have hu₀U : u₀ ∈ U := h.mul_mem_of_not_mem hsR hs'R hsU hs'U
  have hs'ss : (v * s * v⁻¹) * (v * s * v⁻¹) = 1 := h.mul_self _ hs'R hs'U
  have hφu₀ : φ u₀ = u₀⁻¹ := by
    have e1 : φ u₀ = (v * s * v⁻¹) * ((v * v) * s * (v * v)⁻¹) := by
      simp only [hφ, hu₀]; group
    have e2 : u₀⁻¹ = (v * s * v⁻¹)⁻¹ * s⁻¹ := by rw [hu₀, mul_inv_rev]
    rw [e1, e2, hvv, inv_eq_of_mul_eq_one_right hs'ss, hsinv]
    group
  rw [← hρ] at hu₀U
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hu₀U
  have hφpow : ∀ l : ℤ, φ (ρ ^ l) = ρ ^ (-l) * ρ ^ ((t : ℤ) * l) := by
    intro l
    have : φ (ρ ^ l) = φ ρ ^ l := by simp only [hφ]; rw [conj_zpow]
    rw [this, hφρ, hzt]
    have hcomm : Commute ρ⁻¹ (ρ ^ t) := (Commute.refl ρ).inv_left.pow_right t
    rw [hcomm.mul_zpow, inv_zpow', ← zpow_natCast, ← zpow_mul, mul_comm]
  have hρq : ∀ m : ℤ, ρ ^ m = 1 ↔ ((2 * t : ℕ) : ℤ) ∣ m := by
    intro m
    rw [← ht, ← hρo, orderOf_dvd_iff_zpow_eq_one]
  have hjeven : Even j := by
    have h3 := hφpow j
    rw [hj, hφu₀, ← hj, ← zpow_neg] at h3
    have h4 : ρ ^ ((t : ℤ) * j) = 1 := by
      have := congrArg (ρ ^ j * ·) h3
      simpa [← zpow_add] using this.symm
    rw [hρq] at h4
    by_contra hodd
    rw [Int.not_even_iff_odd] at hodd
    obtain ⟨i, rfl⟩ := hodd
    obtain ⟨d, hd⟩ := h4
    push_cast at hd
    have : (t : ℤ) * (2 * i + 1 - 2 * d) = 0 := by linear_combination hd
    rcases mul_eq_zero.mp this with h5 | h5
    · have : t = 0 := by exact_mod_cast h5
      omega
    · omega
  obtain ⟨i, rfl⟩ := hjeven
  have hl : ∃ l : ℤ, ((2 * t : ℕ) : ℤ) ∣ (i + i) - 2 * l + (t : ℤ) * l := by
    rcases Int.even_or_odd i with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact ⟨a + a, ⟨a, by push_cast; ring⟩⟩
    · refine ⟨2 * a + 1 + 2 * c, ⟨a + c, ?_⟩⟩
      rw [hc]
      push_cast
      ring
  obtain ⟨l, hl⟩ := hl
  have hfixed : (s * ρ ^ l) * v = v * (s * ρ ^ l) := by
    have h3 : v * (s * ρ ^ l) * v⁻¹ = (v * s * v⁻¹) * φ (ρ ^ l) := by simp only [hφ]; group
    have h4 : v * s * v⁻¹ = s * u₀ := by rw [hu₀, ← mul_assoc, hss, one_mul]
    have h5 : u₀ * φ (ρ ^ l) = ρ ^ l := by
      rw [hφpow, ← hj, ← zpow_add, ← zpow_add,
        show i + i + (-l + (t : ℤ) * l) = l + ((i + i) - 2 * l + (t : ℤ) * l) by ring, zpow_add,
        (hρq _).mpr hl, mul_one]
    calc s * ρ ^ l * v = (v * (s * ρ ^ l) * v⁻¹) * v := by
          rw [h3, h4, mul_assoc s u₀, h5]
      _ = v * (s * ρ ^ l) := by group
  have hsl := (hC _ (R.mul_mem hsR (h.le (U.zpow_mem hρU l))) hfixed).1
  exact hsU (by
    have : s = s * ρ ^ l * (ρ ^ l)⁻¹ := by group
    rw [this]
    exact U.mul_mem hsl (U.inv_mem (U.zpow_mem hρU l)))

end IsDihedralRot

end CFSG.ComponentClassification.Asc76.Sec4
