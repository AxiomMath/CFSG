module

public import CFSG.CharacterTheory.Semidihedral.Local.ProperSubgroupFormsSupport
public import CFSG.CharacterTheory.Semidihedral.Local.QuaternionNormalForm

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open

theorem closure_pair_subtype_eq_top {G : Type*} [Group G] {T : Subgroup G} {u x : G}
    (hu : u ∈ T) (hx : x ∈ T) (hT : T = Subgroup.closure {u, x}) :
    Subgroup.closure ({⟨u, hu⟩, ⟨x, hx⟩} : Set T) = ⊤ := by
  apply Subgroup.map_injective T.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  conv_rhs => rw [hT]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl | rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr rfl, rfl⟩

theorem proper_subgroup_forms_aux {S : Type*} [Group S] (n : ℕ) (hn : 4 ≤ n)
    (f : SemidihedralGroup n ≃* S) {r s z : S} (hrdef : r = f (CFSG.Semidihedral.r n))
    (hsdef : s = f (CFSG.Semidihedral.s n)) (hzdef : z = r ^ (2 ^ (n - 1) / 2))
    (T : Subgroup S) :
    (T ≠ ⊤ → (IsCyclic T ∨
        (∃ a : ℕ, 1 ≤ a ∧ Nonempty (T ≃* DihedralGroup (2 ^ a)) ∧ Nat.card T = 2 ^ (a + 1)) ∨
        (∃ a : ℕ, 1 ≤ a ∧ Nonempty (T ≃* QuaternionGroup (2 ^ a)) ∧
          Nat.card T = 2 ^ (a + 2)))) ∧
      (¬ T ≤ Subgroup.zpowers r → ∃ k i : ℕ, k ≤ n - 1 ∧ i < 2 ^ (n - 1) ∧
        T ⊓ Subgroup.zpowers r = Subgroup.zpowers (r ^ (2 ^ k)) ∧
        T = Subgroup.closure {r ^ (2 ^ k), r ^ i * s} ∧
        (T ≠ ⊤ → 1 ≤ k ∧
          (Even i →
            (T ⊓ Subgroup.zpowers r ≠ ⊥ →
              ∃ e : DihedralGroup (Nat.card (T ⊓ Subgroup.zpowers r : Subgroup S)) ≃* T,
                (e (DihedralGroup.r 1) : S) = r ^ (2 ^ k) ∧
                  (e (DihedralGroup.sr 0) : S) = r ^ i * s) ∧
            (T ⊓ Subgroup.zpowers r = ⊥ → IsCyclic T ∧ Nat.card T = 2)) ∧
          (Odd i → z ∈ T ⊓ Subgroup.zpowers r ∧
            (Nat.card (T ⊓ Subgroup.zpowers r : Subgroup S) = 2 → IsCyclic T ∧ Nat.card T = 4) ∧
            (4 ≤ Nat.card (T ⊓ Subgroup.zpowers r : Subgroup S) →
              ∃ e : QuaternionGroup (Nat.card (T ⊓ Subgroup.zpowers r : Subgroup S) / 2) ≃* T,
                (e (QuaternionGroup.a 1) : S) = r ^ (2 ^ k) ∧
                  (e (QuaternionGroup.xa 0) : S) = r ^ i * s)))) := by
  set A := Subgroup.zpowers r with hAdef
  have hr : orderOf r = 2 ^ (n - 1) := by rw [hrdef]; exact sd_orderOf_r hn f
  have hidx : A.index = 2 := by rw [hAdef, hrdef]; exact sd_index_two hn f
  have hz : orderOf z = 2 := by rw [hzdef, hrdef]; exact image_z_orderOf (by omega) f
  have hz2 : z ^ 2 = 1 := by rw [← hz, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz; norm_num at hz
  have hzA : z ∈ A := hzdef ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers r) _
  by_cases hTA : T ≤ A
  · exact ⟨fun _ => Or.inl (Subgroup.isCyclic_of_le hTA), fun h => absurd hTA h⟩
  obtain ⟨x, hxT, hxA⟩ := IsConcreteLE.not_le_iff_exists.mp hTA
  obtain ⟨i, hi, hxi⟩ := sd_eq_of_notMem hn f (by rw [← hrdef]; exact hxA)
  rw [← hrdef, ← hsdef] at hxi
  subst hxi
  obtain ⟨k, hk, hTAk⟩ := eq_zpowers_two_pow_of_le hr (inf_le_right : T ⊓ A ≤ A)
  set u := r ^ (2 ^ k) with hudef
  have huTA : u ∈ T ⊓ A := hTAk ▸ Subgroup.mem_zpowers u
  have huT : u ∈ T := huTA.1
  have hcoset : ∀ g : S, g ∉ A → g * (r ^ i * s)⁻¹ ∈ A := fun g hg => by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    exact ⟨fun h => absurd h hg, fun h => absurd (inv_inv (r ^ i * s) ▸ A.inv_mem h) hxA⟩
  have hTgen : T = Subgroup.closure {u, r ^ i * s} := by
    have hule : Subgroup.zpowers u ≤ Subgroup.closure {u, r ^ i * s} :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have hx' : r ^ i * s ∈ Subgroup.closure {u, r ^ i * s} := Subgroup.subset_closure (by simp)
    apply le_antisymm
    · intro t ht
      by_cases htA : t ∈ A
      · have h1 : t ∈ T ⊓ A := ⟨ht, htA⟩
        rw [hTAk] at h1
        exact hule h1
      · have h2 : t * (r ^ i * s)⁻¹ ∈ T ⊓ A := ⟨T.mul_mem ht (T.inv_mem hxT), hcoset t htA⟩
        rw [hTAk] at h2
        have h3 := Subgroup.mul_mem _ (hule h2) hx'
        rwa [inv_mul_cancel_right] at h3
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact huT
      · exact hxT
  by_cases hT : T = ⊤
  · exact ⟨fun h => absurd hT h, fun _ => ⟨k, i, hk, hi, hTAk, hTgen, fun h => absurd hT h⟩⟩
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    apply hT
    have hAT : A ≤ T := fun a ha => by
      have h1 : a ∈ T ⊓ A := by rw [hTAk, hudef, hk0', pow_zero, pow_one]; exact ha
      exact h1.1
    rw [eq_top_iff]
    intro g _
    by_cases hg : g ∈ A
    · exact hAT hg
    · have h3 := T.mul_mem (hAT (hcoset g hg)) hxT
      rwa [inv_mul_cancel_right] at h3
  have hu : orderOf u = 2 ^ (n - 1 - k) := by
    rw [hudef, orderOf_pow_of_dvd (by positivity) (by rw [hr]; exact Nat.pow_dvd_pow 2 hk), hr,
      Nat.pow_div hk (by norm_num)]
  have hcardTA : Nat.card (T ⊓ A : Subgroup S) = 2 ^ (n - 1 - k) := by
    rw [hTAk, Nat.card_zpowers, hu]
  have hxu : (r ^ i * s) * u * (r ^ i * s)⁻¹ = u⁻¹ := by
    have h1 := sd_conj_rotation f (i : ℤ) (2 ^ k)
    rw [← hrdef, ← hsdef, zpow_natCast] at h1
    rw [hudef, h1, eq_inv_iff_mul_eq_one, ← pow_add]
    have harith : (2 ^ (n - 2) - 1) * 2 ^ k + 2 ^ k = 2 ^ (n - 1) * 2 ^ (k - 1) := by
      have h2 : 1 ≤ 2 ^ (n - 2) := Nat.one_le_two_pow
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel h2, ← pow_add, ← pow_add]
      congr 1
      omega
    rw [harith, pow_mul, ← hr, pow_orderOf_eq_one, one_pow]
  have hx2 : (r ^ i * s) ^ 2 = z ^ i := by
    have h1 := sd_sq hn f (i : ℤ)
    rwa [← hrdef, ← hsdef, ← hzdef, zpow_natCast, zpow_natCast] at h1
  have hxnot : r ^ i * s ∉ Subgroup.zpowers u := fun h =>
    hxA ((Subgroup.zpowers_le.mpr huTA.2) h)
  have hgenT := closure_pair_subtype_eq_top huT hxT hTgen
  have hu' : orderOf (⟨u, huT⟩ : T) = 2 ^ (n - 1 - k) := by rw [Subgroup.orderOf_mk, hu]
  have hxnot' : (⟨r ^ i * s, hxT⟩ : T) ∉ Subgroup.zpowers (⟨u, huT⟩ : T) := fun h => by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
    exact hxnot (Subgroup.mem_zpowers_iff.mpr ⟨j, by
      have := congrArg Subtype.val hj
      simpa using this⟩)
  have hxu' : (⟨r ^ i * s, hxT⟩ : T) * ⟨u, huT⟩ * (⟨r ^ i * s, hxT⟩ : T)⁻¹ =
      (⟨u, huT⟩ : T)⁻¹ := Subtype.ext (by simpa using hxu)
  rcases Nat.even_or_odd i with hie | hio
  ·
    have hx1 : (r ^ i * s) ^ 2 = 1 := by
      obtain ⟨t, rfl⟩ := hie
      rw [hx2, ← two_mul, pow_mul, hz2, one_pow]
    have hx1' : (⟨r ^ i * s, hxT⟩ : T) ^ 2 = 1 := Subtype.ext (by simpa using hx1)
    have hdih : 2 ≤ 2 ^ (n - 1 - k) → ∃ e : DihedralGroup (2 ^ (n - 1 - k)) ≃* T,
        (e (DihedralGroup.r 1) : S) = u ∧ (e (DihedralGroup.sr 0) : S) = r ^ i * s := by
      intro _
      obtain ⟨e, he1, he2⟩ := dihedral_normal_form hgenT hu' hxnot' hx1' hxu'
      exact ⟨e, congrArg Subtype.val he1, congrArg Subtype.val he2⟩
    have htriv : 2 ^ (n - 1 - k) = 1 → IsCyclic T ∧ Nat.card T = 2 := by
      intro h1
      have hu1 : u = 1 := orderOf_eq_one_iff.mp (hu.trans h1)
      have hTx : T = Subgroup.zpowers (r ^ i * s) := by
        apply le_antisymm
        · rw [hTgen, Subgroup.closure_le]
          intro g hg
          rcases hg with hg | hg
          · rw [hg, hu1]
            exact Subgroup.one_mem _
          · rw [Set.mem_singleton_iff] at hg
            rw [hg]
            exact Subgroup.mem_zpowers _
        · exact Subgroup.zpowers_le.mpr hxT
      have hxo : orderOf (r ^ i * s) = 2 := orderOf_eq_prime hx1 fun h => hxA (h ▸ A.one_mem)
      refine ⟨by rw [hTx]; infer_instance, by rw [hTx, Nat.card_zpowers, hxo]⟩
    refine ⟨fun _ => ?_, fun _ => ⟨k, i, hk, hi, hTAk, hTgen, fun _ => ⟨hk1,
      fun _ => ⟨fun hne => ?_, fun hbot => htriv (by rw [← hcardTA, hbot, Subgroup.card_bot])⟩,
      fun hodd => absurd hie (Nat.not_even_iff_odd.mpr hodd)⟩⟩⟩
    · by_cases h1 : 2 ^ (n - 1 - k) = 1
      · exact Or.inl (htriv h1).1
      · have h2 : 2 ≤ 2 ^ (n - 1 - k) := by
          have := Nat.one_le_two_pow (n := n - 1 - k)
          omega
        obtain ⟨e, -⟩ := hdih h2
        have ha : 1 ≤ n - 1 - k := by
          by_contra h
          have : n - 1 - k = 0 := by omega
          rw [this] at h1
          exact h1 rfl
        refine Or.inr (Or.inl ⟨n - 1 - k, ha, ⟨e.symm⟩, ?_⟩)
        rw [← Nat.card_congr e.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm]
    · have h2 : 2 ≤ 2 ^ (n - 1 - k) := by
        have h1 : 2 ^ (n - 1 - k) ≠ 1 := fun h => hne (by
          rw [← Subgroup.card_eq_one, hcardTA, h])
        have := Nat.one_le_two_pow (n := n - 1 - k)
        omega
      obtain ⟨e, he1, he2⟩ := hdih h2
      rw [hcardTA]
      exact ⟨e, he1, he2⟩
  ·
    have hxz : (r ^ i * s) ^ 2 = z := by
      obtain ⟨t, rfl⟩ := hio
      rw [hx2, pow_succ, pow_mul, hz2, one_pow, one_mul]
    have hzT : z ∈ T := hxz ▸ T.pow_mem hxT 2
    have hzTA : z ∈ T ⊓ A := ⟨hzT, hzA⟩
    have hh2 : 2 ≤ 2 ^ (n - 1 - k) := by
      have h1 : 2 ^ (n - 1 - k) ≠ 1 := fun h => by
        have hu1 : u = 1 := orderOf_eq_one_iff.mp (hu.trans h)
        rw [hTAk, hu1, Subgroup.zpowers_one_eq_bot] at hzTA
        exact hz1 (Subgroup.mem_bot.mp hzTA)
      have := Nat.one_le_two_pow (n := n - 1 - k)
      omega
    have hcyc4 : 2 ^ (n - 1 - k) = 2 → IsCyclic T ∧ Nat.card T = 4 := by
      intro h2
      have huz : u = z := by
        have hz' : z ∈ Subgroup.zpowers u := by rw [← hTAk]; exact hzTA
        have hcard2 : Nat.card (Subgroup.zpowers u) = 2 := by rw [Nat.card_zpowers, hu, h2]
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hz'
        have hu2 : u ^ (2 : ℕ) = 1 := by rw [← h2, ← hu, pow_orderOf_eq_one]
        rw [zpow_eq_zpow_emod' j hu2] at hj
        have h0 : 0 ≤ j % ((2 : ℕ) : ℤ) := Int.emod_nonneg j (by norm_num)
        have h1 : j % ((2 : ℕ) : ℤ) < 2 := Int.emod_lt_of_pos j (by norm_num)
        obtain ⟨c, hc⟩ : ∃ c, j % ((2 : ℕ) : ℤ) = c := ⟨_, rfl⟩
        rw [hc] at hj h0 h1
        interval_cases c
        · rw [zpow_zero] at hj
          exact absurd hj.symm hz1
        · rw [zpow_one] at hj
          exact hj
      have hxo : orderOf (r ^ i * s) = 4 := by
        have h4 : (r ^ i * s) ^ 4 = 1 := by
          rw [show 4 = 2 * 2 from rfl, pow_mul, hxz, hz2]
        have hdvd := orderOf_dvd_of_pow_eq_one h4
        have hne2 : ¬ orderOf (r ^ i * s) ∣ 2 := fun h => by
          rw [orderOf_dvd_iff_pow_eq_one, hxz] at h
          exact hz1 h
        have hmem : orderOf (r ^ i * s) ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
        have key : ∀ d ∈ Nat.divisors 4, ¬ d ∣ 2 → d = 4 := by decide
        exact key _ hmem hne2
      have hTx : T = Subgroup.zpowers (r ^ i * s) := by
        apply le_antisymm
        · rw [hTgen, Subgroup.closure_le]
          intro g hg
          rcases hg with hg | hg
          · rw [hg, huz, ← hxz]
            exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
          · rw [Set.mem_singleton_iff] at hg
            rw [hg]
            exact Subgroup.mem_zpowers _
        · exact Subgroup.zpowers_le.mpr hxT
      refine ⟨by rw [hTx]; infer_instance, by rw [hTx, Nat.card_zpowers, hxo]⟩
    have hbig : 4 ≤ 2 ^ (n - 1 - k) → k + 2 ≤ n - 1 := fun h4 => by
      by_contra h
      have h1 : n - 1 - k ≤ 1 := by omega
      have : 2 ^ (n - 1 - k) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
      omega
    have hhalf : 4 ≤ 2 ^ (n - 1 - k) → 2 ^ (n - 1 - k) / 2 = 2 ^ (n - 2 - k) := fun h4 => by
      have := hbig h4
      rw [show n - 1 - k = (n - 2 - k) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    have hquat : 4 ≤ 2 ^ (n - 1 - k) → ∃ e : QuaternionGroup (2 ^ (n - 2 - k)) ≃* T,
        (e (QuaternionGroup.a 1) : S) = u ∧ (e (QuaternionGroup.xa 0) : S) = r ^ i * s := by
      intro h4
      have hk2 := hbig h4
      have hzu : z = u ^ (2 ^ (n - 2 - k)) := by
        rw [hzdef, hudef, ← pow_mul, ← pow_add]
        congr 1
        rw [show k + (n - 2 - k) = n - 2 by omega, show n - 1 = (n - 2) + 1 by omega, pow_succ,
          Nat.mul_div_cancel _ (by norm_num)]
      have hu'' : orderOf (⟨u, huT⟩ : T) = 2 * 2 ^ (n - 2 - k) := by
        rw [hu', show n - 1 - k = (n - 2 - k) + 1 by omega, pow_succ, mul_comm]
      have hxz' : (⟨r ^ i * s, hxT⟩ : T) ^ 2 = (⟨u, huT⟩ : T) ^ (2 ^ (n - 2 - k)) :=
        Subtype.ext (by simpa [hzu] using hxz)
      obtain ⟨⟨e, ⟨he1, he2⟩, -⟩, -⟩ := quaternion_normal_form_isomorphism Nat.one_le_two_pow
        hgenT hu'' hxnot' hxz' hxu'
      exact ⟨e, congrArg Subtype.val he1, congrArg Subtype.val he2⟩
    refine ⟨fun _ => ?_, fun _ => ⟨k, i, hk, hi, hTAk, hTgen, fun _ => ⟨hk1,
      fun heven => absurd heven (Nat.not_even_iff_odd.mpr hio),
      fun _ => ⟨hzTA, fun h2 => hcyc4 (by rw [← hcardTA]; exact h2), fun h4 => ?_⟩⟩⟩⟩
    · by_cases h2 : 2 ^ (n - 1 - k) = 2
      · exact Or.inl (hcyc4 h2).1
      · have h4 : 4 ≤ 2 ^ (n - 1 - k) := by
          have h1 : 2 ≤ n - 1 - k := by
            by_contra h
            have : n - 1 - k = 1 := by
              have : n - 1 - k ≠ 0 := fun h0 => by rw [h0] at hh2; norm_num at hh2
              omega
            rw [this] at h2
            exact h2 rfl
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (n - 1 - k) := Nat.pow_le_pow_right (by norm_num) h1
        obtain ⟨e, -⟩ := hquat h4
        have ha : 1 ≤ n - 2 - k := by have := hbig h4; omega
        refine Or.inr (Or.inr ⟨n - 2 - k, ha, ⟨e.symm⟩, ?_⟩)
        rw [← Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card, pow_add,
          mul_comm]
        norm_num
    · rw [hcardTA] at h4 ⊢
      rw [hhalf h4]
      exact hquat h4

theorem proper_subgroup_cyclic_dihedral_quaternion_forms {S : Type*} [Group S] (n : ℕ)
    (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) :
    let r := f (CFSG.Semidihedral.r n)
    let s := f (CFSG.Semidihedral.s n)
    let m := 2 ^ (n - 1)
    let A := Subgroup.zpowers r
    let z := r ^ (m / 2)
    ∀ T : Subgroup S,
      (T ≠ ⊤ → (IsCyclic T ∨
        (∃ a : ℕ, 1 ≤ a ∧ Nonempty (T ≃* DihedralGroup (2 ^ a)) ∧ Nat.card T = 2 ^ (a + 1)) ∨
        (∃ a : ℕ, 1 ≤ a ∧ Nonempty (T ≃* QuaternionGroup (2 ^ a)) ∧
          Nat.card T = 2 ^ (a + 2)))) ∧
      (¬ T ≤ A → ∃ k i : ℕ, k ≤ n - 1 ∧ i < m ∧
        T ⊓ A = Subgroup.zpowers (r ^ (2 ^ k)) ∧
        T = Subgroup.closure {r ^ (2 ^ k), r ^ i * s} ∧
        (T ≠ ⊤ → 1 ≤ k ∧
          (Even i →
            (T ⊓ A ≠ ⊥ → ∃ e : DihedralGroup (Nat.card (T ⊓ A : Subgroup S)) ≃* T,
              (e (DihedralGroup.r 1) : S) = r ^ (2 ^ k) ∧
                (e (DihedralGroup.sr 0) : S) = r ^ i * s) ∧
            (T ⊓ A = ⊥ → IsCyclic T ∧ Nat.card T = 2)) ∧
          (Odd i → z ∈ T ⊓ A ∧
            (Nat.card (T ⊓ A : Subgroup S) = 2 → IsCyclic T ∧ Nat.card T = 4) ∧
            (4 ≤ Nat.card (T ⊓ A : Subgroup S) →
              ∃ e : QuaternionGroup (Nat.card (T ⊓ A : Subgroup S) / 2) ≃* T,
                (e (QuaternionGroup.a 1) : S) = r ^ (2 ^ k) ∧
                  (e (QuaternionGroup.xa 0) : S) = r ^ i * s)))) := by
  intro r s m A z T
  exact proper_subgroup_forms_aux n hn f rfl rfl rfl T

end CFSG.Semidihedral.Local
