module

public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Basic
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltCentralExtThree

public section

namespace CFSG.AGLEmbeddingD2.RealThreeRank

open CFSG.Open CFSG.SectionRank CFSG.SectionRank.ClassicalEven

section Commute

variable {G : Type*} [Group G]

theorem commute_of_mem_commutator {P : Subgroup G} {b : G}
    (hc : ∀ t ∈ P, t * b * t⁻¹ * b⁻¹ ∈ Subgroup.center G) {t : G} (ht : t ∈ ⁅P, P⁆) :
    Commute t b := by
  let f : ↥P →* ↥(Subgroup.center G) :=
    { toFun := fun s => ⟨s * b * (s : G)⁻¹ * b⁻¹, hc s s.2⟩
      map_one' := by ext; simp
      map_mul' := fun s s' => by
        ext
        have hz := Subgroup.mem_center_iff.mp (hc s' s'.2)
        simp only [Subgroup.coe_mul, mul_inv_rev]
        calc (s : G) * s' * b * ((s' : G)⁻¹ * (s : G)⁻¹) * b⁻¹
            = s * (s' * b * (s' : G)⁻¹ * b⁻¹) * b * (s : G)⁻¹ * b⁻¹ := by group
          _ = (s' * b * (s' : G)⁻¹ * b⁻¹) * s * b * (s : G)⁻¹ * b⁻¹ := by rw [hz s]
          _ = (s' * b * (s' : G)⁻¹ * b⁻¹) * (s * b * (s : G)⁻¹ * b⁻¹) := by group
          _ = (s * b * (s : G)⁻¹ * b⁻¹) * (s' * b * (s' : G)⁻¹ * b⁻¹) :=
            (hz (s * b * (s : G)⁻¹ * b⁻¹)).symm }
  rw [← Subgroup.map_subtype_commutator] at ht
  obtain ⟨t', ht', rfl⟩ := ht
  have hk : f t' = 1 := Abelianization.commutator_subset_ker f ht'
  have h1 : (t' : G) * b * (t' : G)⁻¹ * b⁻¹ = 1 := congrArg Subtype.val hk
  change (t' : G) * b = b * t'
  calc (t' : G) * b = ((t' : G) * b * (t' : G)⁻¹ * b⁻¹) * (b * t') := by group
    _ = b * t' := by rw [h1, one_mul]

variable {X Y : Type*} [Group X] [Group Y]

theorem commute_lift_of_commutes (ρ : X →* Y) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center X) {A B : Subgroup Y}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b) {g : Y} (hg : g ∈ ⁅A, A⁆) {x b : X}
    (hx : ρ x = g) (hb : ρ b ∈ B) : Commute x b := by
  have hmap : (⁅A.comap ρ, A.comap ρ⁆).map ρ = ⁅A, A⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hρ]
  rw [← hmap] at hg
  obtain ⟨t, ht, htg⟩ := hg
  have hct : ∀ s ∈ A.comap ρ, s * b * s⁻¹ * b⁻¹ ∈ Subgroup.center X := fun s hs => hker (by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [(hAB _ hs _ hb).eq]
    group)
  have h1 := commute_of_mem_commutator hct ht
  have hz : t⁻¹ * x ∈ Subgroup.center X := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, htg, hx, inv_mul_cancel])
  have hzb : Commute (t⁻¹ * x) b := (Subgroup.mem_center_iff.mp hz b).symm
  have : x = t * (t⁻¹ * x) := by group
  rw [this]
  exact h1.mul_left hzb

end Commute

section Rank

variable {X Y : Type*} [Group X] [Group Y] [Finite X]

omit [Finite X] in
theorem exists_lift_mem (ρ : X →* Y) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center X) {P : Subgroup X} (hkP : ρ.ker ≤ P) {g w : Y}
    (hgP : g ∈ P.map ρ) (hg3 : g ^ 3 = 1) (hw : w * g * w⁻¹ = g⁻¹) :
    ∃ x ∈ P, ρ x = g ∧ x ^ 3 = 1 := by
  obtain ⟨x, hx, hx3⟩ := AltCentralExtThree.exists_lift_pow_three_eq_one ρ hρ hker hg3 hw
  obtain ⟨p, hp, hpg⟩ := hgP
  refine ⟨x, ?_, hx, hx3⟩
  have hk : p⁻¹ * x ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpg, hx, inv_mul_cancel]
  simpa using mul_mem hp (hkP hk)

omit [Finite X] in
theorem eq_one_of_conj_eq_inv_of_conj_eq {g w : Y} (hg3 : g ^ 3 = 1)
    (hw : w * g * w⁻¹ = g⁻¹) (hw' : w * g * w⁻¹ = g) : g = 1 := by
  have h2 : g * g = 1 := by
    have := hw'.symm.trans hw
    calc g * g = g * g⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel g
  have h3 : g ^ 3 = g := by
    rw [pow_succ, sq, h2, one_mul]
  rw [← h3, hg3]

omit [Finite X] in
theorem conj_pow_eq_of_commute {a w : Y} (h : Commute w a) (n : ℕ) :
    w * a ^ n * w⁻¹ = a ^ n := by
  rw [(h.pow_right n).eq, mul_inv_cancel_right]

theorem pRank_top_subtype_le (p : ℕ) (hp : 1 < p) (P : Subgroup X) :
    pRank p (⊤ : Subgroup ↥P) ≤ pRank p P := by
  have h := pRank_le_map hp P.subtype P.subtype_injective ⊤
  rwa [Subgroup.map_top, Subgroup.range_subtype] at h

theorem three_le_pRank_of_real_triple (ρ : X →* Y) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center X) {P : Subgroup X} (hkP : ρ.ker ≤ P)
    {A₁ A₂ A₃ : Subgroup Y} (h12 : ∀ a ∈ A₁, ∀ b ∈ A₂, Commute a b)
    (h13 : ∀ a ∈ A₁, ∀ b ∈ A₃, Commute a b) (h23 : ∀ a ∈ A₂, ∀ b ∈ A₃, Commute a b)
    {g₁ g₂ g₃ w₁ w₂ w₃ : Y} (hg₁ : g₁ ∈ ⁅A₁, A₁⁆) (hg₂ : g₂ ∈ ⁅A₂, A₂⁆) (hg₃ : g₃ ∈ ⁅A₃, A₃⁆)
    (hP₁ : g₁ ∈ P.map ρ) (hP₂ : g₂ ∈ P.map ρ) (hP₃ : g₃ ∈ P.map ρ)
    (h3₁ : g₁ ^ 3 = 1) (h3₂ : g₂ ^ 3 = 1) (h3₃ : g₃ ^ 3 = 1)
    (h1₁ : g₁ ≠ 1) (h1₂ : g₂ ≠ 1) (h1₃ : g₃ ≠ 1)
    (hw₂ : w₂ ∈ A₂) (hw₃ : w₃ ∈ A₃) (hi₁ : w₁ * g₁ * w₁⁻¹ = g₁⁻¹) (hi₂ : w₂ * g₂ * w₂⁻¹ = g₂⁻¹)
    (hi₃ : w₃ * g₃ * w₃⁻¹ = g₃⁻¹) : 3 ≤ pRank 3 P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA₁ : ⁅A₁, A₁⁆ ≤ A₁ := Subgroup.commutator_le_self A₁
  have hA₂ : ⁅A₂, A₂⁆ ≤ A₂ := Subgroup.commutator_le_self A₂
  have hA₃ : ⁅A₃, A₃⁆ ≤ A₃ := Subgroup.commutator_le_self A₃
  obtain ⟨x₁, hx₁P, hx₁, hx₁3⟩ := exists_lift_mem ρ hρ hker hkP hP₁ h3₁ hi₁
  obtain ⟨x₂, hx₂P, hx₂, hx₂3⟩ := exists_lift_mem ρ hρ hker hkP hP₂ h3₂ hi₂
  obtain ⟨x₃, hx₃P, hx₃, hx₃3⟩ := exists_lift_mem ρ hρ hker hkP hP₃ h3₃ hi₃
  have c12 : Commute x₁ x₂ := commute_lift_of_commutes ρ hρ hker h12 hg₁ hx₁ (hx₂ ▸ hA₂ hg₂)
  have c13 : Commute x₁ x₃ := commute_lift_of_commutes ρ hρ hker h13 hg₁ hx₁ (hx₃ ▸ hA₃ hg₃)
  have c23 : Commute x₂ x₃ := commute_lift_of_commutes ρ hρ hker h23 hg₂ hx₂ (hx₃ ▸ hA₃ hg₃)
  set y₁ : ↥P := ⟨x₁, hx₁P⟩
  set y₂ : ↥P := ⟨x₂, hx₂P⟩
  set y₃ : ↥P := ⟨x₃, hx₃P⟩
  have hρ₁ : ∀ n : ℕ, ρ ((y₁ : X) ^ n) = g₁ ^ n := fun n => by rw [map_pow, hx₁]
  have hρ₂ : ∀ n : ℕ, ρ ((y₂ : X) ^ n) = g₂ ^ n := fun n => by rw [map_pow, hx₂]
  refine (three_le_pRank_of_gens (G := ↥P) (p := 3) (x := y₁) (y := y₂) (z := y₃)
    (Subtype.ext hx₁3) (Subtype.ext hx₂3) (Subtype.ext hx₃3)
    (Subtype.ext c12.eq) (Subtype.ext c13.eq) (Subtype.ext c23.eq) ?_ ?_ ?_).trans
    (pRank_top_subtype_le 3 (by norm_num) P)
  · intro h
    apply h1₁
    rw [← hx₁]
    exact congrArg (fun y : ↥P => ρ (y : X)) h |>.trans (map_one ρ)
  · intro n h
    apply h1₂
    have he : g₁ ^ n = g₂ := by
      rw [← hρ₁, ← hx₂]
      exact congrArg (fun y : ↥P => ρ (y : X)) (by simpa using h)
    refine eq_one_of_conj_eq_inv_of_conj_eq h3₂ hi₂ ?_
    rw [← he]
    exact conj_pow_eq_of_commute (h12 _ (hA₁ hg₁) _ hw₂).symm n
  · intro n m h
    apply h1₃
    have he : g₁ ^ n * g₂ ^ m = g₃ := by
      rw [← hρ₁, ← hρ₂, ← map_mul, ← hx₃]
      exact congrArg (fun y : ↥P => ρ (y : X)) (by simpa using h)
    refine eq_one_of_conj_eq_inv_of_conj_eq h3₃ hi₃ ?_
    rw [← he]
    have e1 := conj_pow_eq_of_commute (h13 _ (hA₁ hg₁) _ hw₃).symm n
    have e2 := conj_pow_eq_of_commute (h23 _ (hA₂ hg₂) _ hw₃).symm m
    calc w₃ * (g₁ ^ n * g₂ ^ m) * w₃⁻¹ = (w₃ * g₁ ^ n * w₃⁻¹) * (w₃ * g₂ ^ m * w₃⁻¹) := by
          group
      _ = g₁ ^ n * g₂ ^ m := by rw [e1, e2]

theorem three_le_pRank_of_real_pair (ρ : X →* Y) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center X) {P : Subgroup X} (hkP : ρ.ker ≤ P)
    (h3 : 3 ∣ Nat.card ρ.ker) {A₁ A₂ : Subgroup Y} (h12 : ∀ a ∈ A₁, ∀ b ∈ A₂, Commute a b)
    {g₁ g₂ w₂ : Y} (hg₁ : g₁ ∈ ⁅A₁, A₁⁆) (hg₂ : g₂ ∈ ⁅A₂, A₂⁆)
    (hP₁ : g₁ ∈ P.map ρ) (hP₂ : g₂ ∈ P.map ρ) (h3₁ : g₁ ^ 3 = 1) (h3₂ : g₂ ^ 3 = 1)
    (h1₁ : g₁ ≠ 1) (h1₂ : g₂ ≠ 1) {w₁ : Y} (hi₁ : w₁ * g₁ * w₁⁻¹ = g₁⁻¹)
    (hw₂ : w₂ ∈ A₂) (hi₂ : w₂ * g₂ * w₂⁻¹ = g₂⁻¹) : 3 ≤ pRank 3 P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA₁ : ⁅A₁, A₁⁆ ≤ A₁ := Subgroup.commutator_le_self A₁
  have hA₂ : ⁅A₂, A₂⁆ ≤ A₂ := Subgroup.commutator_le_self A₂
  obtain ⟨x₁, hx₁P, hx₁, hx₁3⟩ := exists_lift_mem ρ hρ hker hkP hP₁ h3₁ hi₁
  obtain ⟨x₂, hx₂P, hx₂, hx₂3⟩ := exists_lift_mem ρ hρ hker hkP hP₂ h3₂ hi₂
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hzk : (z : X) ∈ ρ.ker := z.2
  have hzc : (z : X) ∈ Subgroup.center X := hker hzk
  have hz3 : (z : X) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
  have hz1 : (z : X) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    omega
  have c12 : Commute x₁ x₂ := commute_lift_of_commutes ρ hρ hker h12 hg₁ hx₁ (hx₂ ▸ hA₂ hg₂)
  have c1z : Commute x₁ z := (Subgroup.mem_center_iff.mp hzc x₁)
  have c2z : Commute x₂ z := (Subgroup.mem_center_iff.mp hzc x₂)
  set y₁ : ↥P := ⟨x₁, hx₁P⟩
  set y₂ : ↥P := ⟨x₂, hx₂P⟩
  set y₃ : ↥P := ⟨z, hkP hzk⟩
  have hρ₁ : ∀ n : ℕ, ρ ((y₁ : X) ^ n) = g₁ ^ n := fun n => by rw [map_pow, hx₁]
  have hρ₂ : ∀ n : ℕ, ρ ((y₂ : X) ^ n) = g₂ ^ n := fun n => by rw [map_pow, hx₂]
  have hind : ∀ n : ℕ, g₁ ^ n ≠ g₂ := fun n he => h1₂ (by
    refine eq_one_of_conj_eq_inv_of_conj_eq h3₂ hi₂ ?_
    rw [← he]
    exact conj_pow_eq_of_commute (h12 _ (hA₁ hg₁) _ hw₂).symm n)
  refine (three_le_pRank_of_gens (G := ↥P) (p := 3) (x := y₁) (y := y₂) (z := y₃)
    (Subtype.ext hx₁3) (Subtype.ext hx₂3) (Subtype.ext hz3)
    (Subtype.ext c12.eq) (Subtype.ext c1z) (Subtype.ext c2z) ?_ ?_ ?_).trans
    (pRank_top_subtype_le 3 (by norm_num) P)
  · intro h
    apply h1₁
    rw [← hx₁]
    exact congrArg (fun y : ↥P => ρ (y : X)) h |>.trans (map_one ρ)
  · intro n h
    exact hind n (by
      rw [← hρ₁, ← hx₂]
      exact congrArg (fun y : ↥P => ρ (y : X)) (by simpa using h))
  · intro n m h
    have hzv := congrArg Subtype.val h
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow] at hzv
    have he : g₁ ^ n * g₂ ^ m = 1 := by
      rw [← hρ₁, ← hρ₂, ← map_mul]
      change ρ ((y₁ : X) ^ n * (y₂ : X) ^ m) = 1
      rw [hzv]
      exact hzk
    have he' : g₁ ^ n * (g₂ ^ m)⁻¹ = 1 := by
      have e1 := conj_pow_eq_of_commute (h12 _ (hA₁ hg₁) _ hw₂).symm n
      have e2 : w₂ * g₂ ^ m * w₂⁻¹ = (g₂ ^ m)⁻¹ := by
        rw [← inv_pow, ← hi₂, conj_pow]
      calc g₁ ^ n * (g₂ ^ m)⁻¹ = (w₂ * g₁ ^ n * w₂⁻¹) * (w₂ * g₂ ^ m * w₂⁻¹) := by rw [e1, e2]
        _ = w₂ * (g₁ ^ n * g₂ ^ m) * w₂⁻¹ := by group
        _ = 1 := by rw [he, mul_one, mul_inv_cancel]
    have hm2 : g₂ ^ m = (g₂ ^ m)⁻¹ :=
      (eq_inv_of_mul_eq_one_right he).trans (eq_inv_of_mul_eq_one_right he').symm
    have hgm : g₂ ^ m = 1 := by
      have h2m : (g₂ ^ m) ^ 2 = 1 := by
        rw [sq]
        nth_rewrite 2 [hm2]
        exact mul_inv_cancel _
      have h3m : (g₂ ^ m) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, h3₂, one_pow]
      calc g₂ ^ m = (g₂ ^ m) ^ 3 * ((g₂ ^ m) ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3m, h2m, inv_one, one_mul]
    have hgn : g₁ ^ n = 1 := by rwa [hgm, mul_one] at he
    have ho₁ : orderOf g₁ = 3 := orderOf_eq_prime h3₁ h1₁
    have ho₂ : orderOf g₂ = 3 := orderOf_eq_prime h3₂ h1₂
    obtain ⟨a, rfl⟩ := ho₁ ▸ orderOf_dvd_of_pow_eq_one hgn
    obtain ⟨c, rfl⟩ := ho₂ ▸ orderOf_dvd_of_pow_eq_one hgm
    apply hz1
    rw [← hzv, pow_mul, pow_mul]
    change (x₁ ^ 3) ^ a * (x₂ ^ 3) ^ c = 1
    rw [hx₁3, hx₂3, one_pow, one_pow, one_mul]

end Rank

end CFSG.AGLEmbeddingD2.RealThreeRank
