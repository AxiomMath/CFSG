module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCaseIOuter

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup Equiv CFSG.Open CFSG.ABGLocalTools CFSG.GorensteinWalter
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoAlt

variable {G : Type} [Group G] [Finite G]

theorem pow_six_of_commute_y0 : ∀ σ : Perm (Fin 5), σ * (y0 : Perm (Fin 5)) = y0 * σ →
    σ ^ 6 = 1 := by
  decide +kernel

theorem eq_swap_of_commute_y0 : ∀ σ : Perm (Fin 5), σ * (y0 : Perm (Fin 5)) = y0 * σ →
    σ * σ = 1 → Perm.sign σ = -1 → σ = swap 3 4 := by
  decide +kernel

theorem exists_eq_of_commute_P0 : ∀ σ : Perm (Fin 5), σ * (k1 : Perm (Fin 5)) = k1 * σ →
    σ * (k2 : Perm (Fin 5)) = k2 * σ → ∃ p ∈ (1 :: p0inv), σ = (p : Perm (Fin 5)) := by
  decide +kernel

theorem swap01_conj_P0 : ∀ p ∈ (1 :: p0inv), ∃ q ∈ (1 :: p0inv),
    swap (0 : Fin 5) 1 * (p : Perm (Fin 5)) * (swap (0 : Fin 5) 1)⁻¹ = (q : Perm (Fin 5)) := by
  decide +kernel

theorem x0_mul_swap34 : (x0 : Perm (Fin 5)) * swap 3 4 = swap 0 1 := by decide +kernel

theorem y0_mul_self_ne_one : (y0 : Perm (Fin 5)) * y0 ≠ 1 := by decide +kernel

theorem y0_sq_mul_self_ne_one : (y0 : Perm (Fin 5)) * y0 * ((y0 : Perm (Fin 5)) * y0) ≠ 1 := by
  decide +kernel

theorem isPGroup_zpowers_of_pow {M : Type*} [Group M] {g : M} {k : ℕ} (hk : g ^ 2 ^ k = 1) :
    IsPGroup 2 (zpowers g) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

namespace CaseICoords

variable {A B R T : Subgroup G} (c : CaseICoords A B R T)

omit [Finite G] in
theorem mem_T_iff {g : G} (hg : g ∈ A) : g ∈ T ↔ c.ψA.symm ⟨g, hg⟩ ∈ P0 := by
  rw [← Subgroup.mem_map_equiv, c.mapA, mem_subgroupOf]

omit [Finite G] in
theorem mem_R_iff {g : G} (hg : g ∈ B) : g ∈ R ↔ c.ψB.symm ⟨g, hg⟩ ∈ P0 := by
  rw [← Subgroup.mem_map_equiv, c.mapB, mem_subgroupOf]

omit [Finite G] in
theorem symm_x : c.ψA.symm ⟨c.x, c.x_mem⟩ = x0 := by
  simp [x]

omit [Finite G] in
theorem autPerm_cases {a : G} (ha : a ∈ c.H) (haN : a ∈ normalizer (A : Set G)) {k : ℕ}
    (hk : a ^ 2 ^ k = 1) :
    autPerm c.ψA.symm ⟨a, haN⟩ = 1 ∨ autPerm c.ψA.symm ⟨a, haN⟩ = swap 3 4 := by
  set σ := autPerm c.ψA.symm ⟨a, haN⟩ with hσ
  have hc := c.autPerm_commute ha haN
  have hσk : σ ^ 2 ^ k = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨a, haN⟩ : normalizer (A : Set G)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hσ2 : σ * σ = 1 := by
    obtain ⟨j, -, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hσk)
    have h6 : 2 ^ j ∣ 6 := hjo ▸ orderOf_dvd_of_pow_eq_one (pow_six_of_commute_y0 σ hc)
    have hj1 : j ≤ 1 := by
      by_contra hj1
      have h4 : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 (by omega)).trans h6
      norm_num at h4
    rw [← sq, ← orderOf_dvd_iff_pow_eq_one, hjo]
    exact pow_dvd_pow 2 hj1
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h
  · left
    rcases eq_of_commute_y0 σ hc h with h1 | h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hσ2) y0_mul_self_ne_one
    · exact absurd (h1 ▸ hσ2) y0_sq_mul_self_ne_one
  · exact Or.inr (eq_swap_of_commute_y0 σ hc hσ2 h)

structure IsOuter (u : G) : Prop where
  mem_H : u ∈ c.H
  mem_normalizer : u ∈ normalizer (R : Set G)
  two_elt : ∃ k : ℕ, u ^ 2 ^ k = 1
  act : ∀ h : u ∈ normalizer (A : Set G), autPerm c.ψA.symm ⟨u, h⟩ = swap 3 4

theorem exists_isOuter :
    ∃ u : G, c.IsOuter u := by
  obtain ⟨u, hu, ⟨k, hk⟩, huA, hsign⟩ := c.exists_outer
  refine ⟨u, ⟨(mem_inf.mp hu).1, (mem_inf.mp hu).2, ⟨k, hk⟩, fun h' => ?_⟩⟩
  rcases c.autPerm_cases (mem_inf.mp hu).1 huA hk with h | h
  · rw [h, map_one] at hsign
    exact absurd hsign (by decide)
  · exact h

omit [Finite G] in
include c in
theorem R_comm {a b : G} (ha : a ∈ R) (hb : b ∈ R) : a * b = b * a := by
  have h := (inv_eq_of_mul_eq_one_right (c.mul_self_of_mem_R (mul_mem ha hb))).symm
  rwa [mul_inv_rev, inv_eq_of_mul_eq_one_right (c.mul_self_of_mem_R ha),
    inv_eq_of_mul_eq_one_right (c.mul_self_of_mem_R hb)] at h

omit [Finite G] in
theorem not_mem_centralizer_of_act {ρ : G} (hρ : ρ ∈ normalizer (A : Set G))
    (hact : autPerm c.ψA.symm ⟨ρ, hρ⟩ = swap 3 4) :
    ρ ∉ centralizer (A : Set G) ∧ ρ ^ 3 ∉ centralizer (A : Set G) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 := (autPerm_eq_one_iff c.ψA.symm ⟨ρ, hρ⟩).mpr h
    rw [hact] at h1
    exact absurd h1 (by decide)
  · have h1 := (autPerm_eq_one_iff c.ψA.symm (⟨ρ, hρ⟩ ^ 3)).mpr (by simpa using h)
    rw [map_pow, hact] at h1
    exact absurd h1 (by decide)

namespace IsOuter

variable {c} {u : G} (hu : c.IsOuter u)
include hu

theorem mem_NA : u ∈ normalizer (A : Set G) := c.pair.normalizer_R_le hu.mem_normalizer

theorem sq_mem_centralizer : u ^ 2 ∈ centralizer (A : Set G) := by
  have h : autPerm c.ψA.symm (⟨u, hu.mem_NA⟩ ^ 2) = 1 := by
    rw [map_pow, (hu.act _)]
    decide
  simpa using (autPerm_eq_one_iff c.ψA.symm _).mp h

omit [Finite G] in
theorem isPGroup_zpowers : IsPGroup 2 (zpowers u) := by
  obtain ⟨k, hk⟩ := hu.two_elt
  exact isPGroup_zpowers_of_pow hk

theorem sq_mem_R : u ^ 2 ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : IsPGroup 2 (zpowers (u ^ 2)) :=
    hu.isPGroup_zpowers.to_le (zpowers_le.mpr (pow_mem (mem_zpowers u) 2))
  have hle : zpowers (u ^ 2) ≤ normalizer (R : Set G) :=
    zpowers_le.mpr (pow_mem hu.mem_normalizer 2)
  have hQ := c.pair.isPGroup_R.to_sup_of_normal_left' hz hle
  have hQK : R ⊔ zpowers (u ^ 2) ≤ centralizer (A : Set G) :=
    sup_le c.pair.sylowR.le (zpowers_le.mpr hu.sq_mem_centralizer)
  have h := c.pair.sylowR.eq_of_le le_sup_left hQK hQ
  rw [← h]
  exact mem_sup_right (mem_zpowers _)

theorem exists_not_commute : ∃ r ∈ R, u * r ≠ r * u := by
  by_contra hno
  push Not at hno
  set m := c.x * u with hm
  have hmA : m ∈ normalizer (A : Set G) := mul_mem (le_normalizer c.x_mem) hu.mem_NA
  have hσm : autPerm c.ψA.symm ⟨m, hmA⟩ = swap 0 1 := by
    have : (⟨m, hmA⟩ : normalizer (A : Set G)) =
        ⟨c.x, le_normalizer c.x_mem⟩ * ⟨u, hu.mem_NA⟩ := rfl
    rw [this, map_mul, autPerm_of_mem c.ψA.symm c.x_mem, (hu.act _), c.symm_x, x0_mul_swap34]
  have hmT : m ∈ normalizer (T : Set G) := by
    refine RankTwoAlt.mem_normalizer_of_conj_le fun t ht => ?_
    have htA := c.pair.T_le ht
    have h1 := autPerm_spec c.ψA.symm ⟨m, hmA⟩ t htA
    rw [hσm] at h1
    obtain ⟨q, hq, hqe⟩ := swap01_conj_P0 _ (mem_P0.mp ((c.mem_T_iff htA).mp ht))
    have hmtA : m * t * m⁻¹ ∈ A := (mem_normalizer_iff.mp hmA t).mp htA
    rw [c.mem_T_iff hmtA]
    have h2 : c.ψA.symm ⟨m * t * m⁻¹, hmtA⟩ = q := Subtype.ext (h1.trans hqe)
    rw [h2]
    exact mem_P0.mpr hq
  have hmB : m ∈ normalizer (B : Set G) := c.pair.symm.normalizer_R_le hmT
  have hmR : ∀ r ∈ R, m * r = r * m := by
    intro r hr
    have hx : c.x * r = r * c.x := mem_centralizer_iff.mp (c.pair.sylowR.le hr) c.x c.x_mem
    rw [hm, mul_assoc, hno r hr, ← mul_assoc, hx, mul_assoc]
  set τ := autPerm c.ψB.symm ⟨m, hmB⟩ with hτ
  have hcomm : ∀ k ∈ P0, τ * (k : Perm (Fin 5)) = k * τ := by
    intro k hk
    have hkR : ((c.ψB k : B) : G) ∈ R := by
      rw [c.mem_R_iff (c.ψB k).2]
      simpa using hk
    have hk' := autPerm_of_mem c.ψB.symm (c.ψB k).2
    simp only [Subtype.coe_eta, MulEquiv.symm_apply_apply] at hk'
    rw [← hk', hτ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hmR _ hkR)
  obtain ⟨p, hp, hpτ⟩ := exists_eq_of_commute_P0 τ (hcomm k1 (by decide)) (hcomm k2 (by decide))
  set r : G := (c.ψB p : G) with hr
  have hrR : r ∈ R := by
    rw [c.mem_R_iff (c.ψB p).2]
    simpa using mem_P0.mpr hp
  have hrB : r ∈ B := (c.ψB p).2
  have hrm : r⁻¹ * m ∈ centralizer (B : Set G) := by
    have hN : r⁻¹ * m ∈ normalizer (B : Set G) := mul_mem (inv_mem (le_normalizer hrB)) hmB
    apply (autPerm_eq_one_iff c.ψB.symm ⟨_, hN⟩).mp
    have : (⟨r⁻¹ * m, hN⟩ : normalizer (B : Set G)) =
        (⟨r, le_normalizer hrB⟩ : normalizer (B : Set G))⁻¹ * ⟨m, hmB⟩ := rfl
    rw [this, map_mul, map_inv, autPerm_of_mem c.ψB.symm hrB, ← hτ, hpτ]
    have : c.ψB.symm ⟨r, hrB⟩ = p := by simp [hr]
    rw [this, inv_mul_cancel]
  obtain ⟨y, ⟨hyA, -⟩, hyk⟩ := c.pair.symm.exists_mul_mem hrm
  set k := y⁻¹ * (r⁻¹ * m) with hk
  have hrK : r ∈ centralizer (A : Set G) := c.pair.sylowR.le hrR
  have heq : (⟨m, hmA⟩ : normalizer (A : Set G)) =
      ⟨r, Subgroup.centralizer_le_normalizer _ hrK⟩ * ⟨y, le_normalizer hyA⟩ *
        ⟨k, Subgroup.centralizer_le_normalizer _ hyk⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, hk]; group)
  have h1 : autPerm c.ψA.symm ⟨r, Subgroup.centralizer_le_normalizer _ hrK⟩ = 1 :=
    (autPerm_eq_one_iff c.ψA.symm _).mpr hrK
  have h2 : autPerm c.ψA.symm ⟨k, Subgroup.centralizer_le_normalizer _ hyk⟩ = 1 :=
    (autPerm_eq_one_iff c.ψA.symm _).mpr hyk
  have hsign := congrArg (fun σ => Perm.sign σ) (congrArg (autPerm c.ψA.symm) heq)
  simp only [map_mul, h1, h2, one_mul, mul_one] at hsign
  rw [hσm, autPerm_of_mem c.ψA.symm hyA, Perm.sign_swap (by decide),
    Equiv.Perm.mem_alternatingGroup.mp (c.ψA.symm ⟨y, hyA⟩).2] at hsign
  exact absurd hsign (by decide)

theorem sup_le_H : R ⊔ zpowers u ≤ c.H := sup_le c.R_le_H (zpowers_le.mpr hu.mem_H)

omit [Finite G] in
theorem sup_le_normalizer : R ⊔ zpowers u ≤ normalizer (R : Set G) :=
  sup_le le_normalizer (zpowers_le.mpr hu.mem_normalizer)

omit [Finite G] in
theorem isPGroup_sup : IsPGroup 2 (R ⊔ zpowers u : Subgroup G) :=
  c.pair.isPGroup_R.to_sup_of_normal_left' hu.isPGroup_zpowers
    (zpowers_le.mpr hu.mem_normalizer)

theorem sup_inf_eq : (R ⊔ zpowers u) ⊓ centralizer (A : Set G) = R :=
  c.pair.sylowR.eq_of_le (le_inf le_sup_left c.pair.sylowR.le) inf_le_right
    (hu.isPGroup_sup.to_le inf_le_left)

theorem card_sup : Nat.card (R ⊔ zpowers u : Subgroup G) = 8 := by
  set P := R ⊔ zpowers u with hP
  have hPN : P ≤ normalizer (A : Set G) := hu.sup_le_normalizer.trans c.pair.normalizer_R_le
  set f : P →* Perm (Fin 5) := (autPerm c.ψA.symm).comp (inclusion hPN) with hf
  have hker : Nat.card f.ker = 4 := by
    rw [← c.pair.card_R, ← hu.sup_inf_eq]
    exact Nat.card_congr ⟨fun a => ⟨a.1, a.1.2, (autPerm_eq_one_iff _ _).mp a.2⟩,
      fun b => ⟨⟨b, (mem_inf.mp b.2).1⟩, (autPerm_eq_one_iff _ _).mpr (mem_inf.mp b.2).2⟩,
      fun a => rfl, fun b => rfl⟩
  have hrange : f.range = zpowers (swap 3 4) := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      obtain ⟨k, hk⟩ := hu.isPGroup_sup a
      rcases c.autPerm_cases (hu.sup_le_H a.2) (hPN a.2) (k := k)
          (by simpa using congrArg Subtype.val hk) with h | h
      · rw [show f a = autPerm c.ψA.symm ⟨a, hPN a.2⟩ from rfl, h]
        exact one_mem _
      · rw [show f a = autPerm c.ψA.symm ⟨a, hPN a.2⟩ from rfl, h]
        exact mem_zpowers _
    · rw [zpowers_le]
      exact ⟨⟨u, mem_sup_right (mem_zpowers u)⟩, (hu.act _)⟩
  have h2 : Nat.card f.range = 2 := by
    rw [hrange, Nat.card_zpowers]
    exact orderOf_eq_prime (by decide) (by decide)
  have h := Subgroup.card_ker_mul_card_range f
  rw [hker, h2] at h
  exact h.symm

theorem isSylowOf_sup : IsSylowOf 2 (R ⊔ zpowers u) c.H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := R ⊔ zpowers u with hP
  obtain ⟨S', hS'⟩ := (hu.isPGroup_sup.comap_subtype (K := c.H)).exists_le_sylow
  set S := (S' : Subgroup c.H).map c.H.subtype with hSdef
  have hS : IsSylowOf 2 S c.H := ⟨S', rfl⟩
  have hPS : P ≤ S := fun y hy => ⟨⟨y, hu.sup_le_H hy⟩, hS' (mem_subgroupOf.mpr hy), rfl⟩
  by_cases hSP : S ≤ P
  · have hSeq : S = P := le_antisymm hSP hPS
    rw [hSeq] at hS
    exact hS
  exfalso
  obtain ⟨a, haS, haN, haP⟩ := exists_mem_normalizer_of_not_le hS.isPGroup hPS hSP
  set Ra := R.map (MulAut.conj a).toMonoidHom with hRa
  have hRaP : Ra ≤ P := by
    rintro _ ⟨r, hr, rfl⟩
    exact (mem_normalizer_iff.mp haN r).mp (mem_sup_left hr)
  have hP8 := hu.card_sup
  have hR4 := c.pair.card_R
  have hRa4 : Nat.card Ra = 4 := by
    rw [hRa, card_map_of_injective (MulAut.conj a).injective, hR4]
  have hrel : ∀ Q : Subgroup G, Q ≤ P → Nat.card Q = 4 → Q.relIndex P = 2 := by
    intro Q hQ h4
    have := Subgroup.relIndex_mul_card (H := Q) (K := P)
    rw [inf_eq_left.mpr hQ, h4, hP8] at this
    omega
  have hI : (R ⊓ Ra).relIndex P ≤ 4 := by
    have := Subgroup.relIndex_inf_le (H := R) (K := Ra) (L := P)
    rwa [hrel R le_sup_left hR4, hrel Ra hRaP hRa4] at this
  have hIcard := Subgroup.relIndex_mul_card (H := R ⊓ Ra) (K := P)
  rw [inf_eq_left.mpr (inf_le_left.trans le_sup_left), hP8] at hIcard
  have hI2 : 2 ≤ Nat.card (R ⊓ Ra : Subgroup G) := by
    have hpos : 0 < Nat.card (R ⊓ Ra : Subgroup G) := Nat.card_pos
    by_contra h
    have h1 : Nat.card (R ⊓ Ra : Subgroup G) = 1 := by omega
    rw [h1] at hIcard
    omega
  have haK : a ∈ normalizer (centralizer (A : Set G) : Set G) := by
    by_contra hna
    have hna' : a⁻¹ ∉ normalizer (centralizer (A : Set G) : Set G) := fun h =>
      hna (by simpa using inv_mem h)
    have hodd := c.pair.tightA.2 a⁻¹ hna'
    have hle : R ⊓ Ra ≤ centralizer (A : Set G) ⊓
        rightConjugate (centralizer (A : Set G)) a⁻¹ := by
      refine le_inf (inf_le_left.trans c.pair.sylowR.le) ?_
      intro g hg
      obtain ⟨r, hr, hrg⟩ := (mem_inf.mp hg).2
      rw [mem_rightConjugate_iff, ← hrg]
      have : a⁻¹ * ((MulAut.conj a).toMonoidHom r) * a⁻¹⁻¹ = r := by
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
        group
      rw [this]
      exact c.pair.sylowR.le hr
    have hdvd := Subgroup.card_dvd_of_le hle
    obtain ⟨j, hj⟩ := (c.pair.isPGroup_R.to_le inf_le_left :
      IsPGroup 2 (R ⊓ Ra : Subgroup G)).exists_card_eq
    have hj1 : j ≠ 0 := by
      rintro rfl
      rw [hj, pow_zero] at hI2
      omega
    have heven : 2 ∣ Nat.card (R ⊓ Ra : Subgroup G) := by
      rw [hj]
      exact dvd_pow_self 2 hj1
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (heven.trans hdvd))
  have haA : a ∈ normalizer (A : Set G) := c.pair.normA ▸ haK
  have hRaK : Ra ≤ centralizer (A : Set G) := by
    rintro _ ⟨r, hr, rfl⟩
    exact (mem_normalizer_iff.mp haK r).mp (c.pair.sylowR.le hr)
  have hRaR : Ra ≤ R := hu.sup_inf_eq ▸ le_inf hRaP hRaK
  have haR : a ∈ normalizer (R : Set G) :=
    RankTwoAlt.mem_normalizer_of_conj_le fun r hr => hRaR ⟨r, hr, rfl⟩
  have haH : a ∈ c.H := hS.le haS
  obtain ⟨k, hk⟩ := hS.isPGroup ⟨a, haS⟩
  have hak : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hSK : S ⊓ centralizer (A : Set G) = R :=
    c.pair.sylowR.eq_of_le (le_inf (le_sup_left.trans hPS) c.pair.sylowR.le) inf_le_right
      (hS.isPGroup.to_le inf_le_left)
  have huS : u ∈ S := hPS (mem_sup_right (mem_zpowers u))
  rcases c.autPerm_cases haH haA hak with h | h
  · apply haP
    have h1 : a ∈ S ⊓ centralizer (A : Set G) :=
      mem_inf.mpr ⟨haS, (autPerm_eq_one_iff _ _).mp h⟩
    rw [hSK] at h1
    exact mem_sup_left h1
  · apply haP
    have h1 : u⁻¹ * a ∈ centralizer (A : Set G) := by
      apply (autPerm_eq_one_iff c.ψA.symm ⟨u⁻¹ * a, mul_mem (inv_mem hu.mem_NA) haA⟩).mp
      have : (⟨u⁻¹ * a, mul_mem (inv_mem hu.mem_NA) haA⟩ : normalizer (A : Set G)) =
          (⟨u, hu.mem_NA⟩ : normalizer (A : Set G))⁻¹ * ⟨a, haA⟩ := rfl
      rw [this, map_mul, map_inv, (hu.act _), h, inv_mul_cancel]
    have h2 : u⁻¹ * a ∈ S ⊓ centralizer (A : Set G) :=
      mem_inf.mpr ⟨mul_mem (inv_mem huS) haS, h1⟩
    rw [hSK] at h2
    have : a = u * (u⁻¹ * a) := by group
    rw [this]
    exact mul_mem (mem_sup_right (mem_zpowers u)) (mem_sup_left h2)

theorem nonempty_sup_equiv_of {ρ r : G} (hρP : ρ ∈ R ⊔ zpowers u)
    (hρN : ρ ∈ normalizer (A : Set G)) (hact : autPerm c.ψA.symm ⟨ρ, hρN⟩ = swap 3 4)
    (hρ4 : orderOf ρ = 4) (hr : r ∈ R) (hr1 : r ≠ 1) (hr2 : r ≠ ρ ^ 2) (hinv : r * ρ * r⁻¹ = ρ⁻¹) :
    Nonempty ((R ⊔ zpowers u : Subgroup G) ≃* DihedralGroup 4) := by
  have hrA : r ∈ centralizer (A : Set G) := c.pair.sylowR.le hr
  obtain ⟨hρA, hρ3A⟩ := c.not_mem_centralizer_of_act hρN hact
  have hrT : r ∉ zpowers ρ := by
    classical
    intro h
    rw [mem_zpowers_iff_mem_range_orderOf, hρ4] at h
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp h
    have hn4 : n < 4 := Finset.mem_range.mp hn
    interval_cases n
    · exact hr1 (pow_zero ρ)
    · exact hρA (by rwa [pow_one] at hrA)
    · exact hr2 rfl
    · exact hρ3A hrA
  have hinv' : ∀ y ∈ zpowers ρ, r * y * r⁻¹ = y⁻¹ := by
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hinv, inv_zpow]
  obtain ⟨e⟩ := CFSG.ABGDGroups.nonempty_mulEquiv_dihedral_of_reflected hrT
    (c.mul_self_of_mem_R hr) hinv'
  rw [Nat.card_zpowers, hρ4] at e
  have hle : zpowers ρ ⊔ zpowers r ≤ R ⊔ zpowers u :=
    sup_le (zpowers_le.mpr hρP) (zpowers_le.mpr (mem_sup_left hr))
  have heq : zpowers ρ ⊔ zpowers r = R ⊔ zpowers u := by
    refine eq_of_le_of_card_ge hle ?_
    rw [hu.card_sup, Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  exact ⟨(MulEquiv.subgroupCongr heq).symm.trans e⟩

theorem nonempty_sup_equiv : Nonempty ((R ⊔ zpowers u : Subgroup G) ≃* DihedralGroup 4) := by
  obtain ⟨r, hr, hru⟩ := hu.exists_not_commute
  have hr2 : r * r = 1 := c.mul_self_of_mem_R hr
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hrA : r ∈ centralizer (A : Set G) := c.pair.sylowR.le hr
  have hrN : r ∈ normalizer (A : Set G) := Subgroup.centralizer_le_normalizer _ hrA
  have hr1 : r ≠ 1 := fun h => hru (by rw [h, mul_one, one_mul])
  set r' := u * r * u⁻¹ with hr'
  have hr'R : r' ∈ R := (mem_normalizer_iff.mp hu.mem_normalizer r).mp hr
  have hr'r : r' ≠ r := fun h => hru (by
    have h' : u * r * u⁻¹ = r := h
    calc u * r = u * r * u⁻¹ * u := by group
      _ = r * u := by rw [h'])
  have hu2R := hu.sq_mem_R
  have huP : u ∈ R ⊔ zpowers u := mem_sup_right (mem_zpowers u)
  by_cases hu2 : u * u = 1
  ·
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    have hρN : u * r ∈ normalizer (A : Set G) := mul_mem hu.mem_NA hrN
    have hact : autPerm c.ψA.symm ⟨u * r, hρN⟩ = swap 3 4 := by
      have : (⟨u * r, hρN⟩ : normalizer (A : Set G)) = ⟨u, hu.mem_NA⟩ * ⟨r, hrN⟩ := rfl
      rw [this, map_mul, (hu.act _), (autPerm_eq_one_iff c.ψA.symm _).mpr hrA, mul_one]
    have hρ2 : (u * r) ^ 2 = r' * r := by
      rw [sq, hr', huinv]
      group
    have hρ2ne : (u * r) ^ 2 ≠ 1 := by
      rw [hρ2]
      intro h
      exact hr'r (by rw [eq_inv_of_mul_eq_one_left h, hrinv])
    have hρ4 : (u * r) ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hρ2, sq]
      exact c.mul_self_of_mem_R (mul_mem hr'R hr)
    have hρo : orderOf (u * r) = 4 :=
      orderOf_eq_prime_pow (p := 2) (n := 1) (by rwa [pow_one]) hρ4
    refine hu.nonempty_sup_equiv_of (mul_mem huP (mem_sup_left hr)) hρN hact hρo hr hr1 ?_ ?_
    · rw [hρ2]
      intro h
      have h' : r' = 1 := by
        calc r' = r' * r * r := by rw [mul_assoc, hr2, mul_one]
          _ = 1 := by rw [← h, hr2]
      have h'' : u * r * u⁻¹ = 1 := h'
      exact hr1 (by
        calc r = u⁻¹ * (u * r * u⁻¹) * u := by group
          _ = 1 := by rw [h'', mul_one, inv_mul_cancel])
    · rw [mul_inv_rev, hrinv, huinv]
      simp only [mul_assoc, hr2, mul_one]
  ·
    have hu4 : u ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq (u ^ 2)]
      exact c.mul_self_of_mem_R hu2R
    have huo : orderOf u = 4 :=
      orderOf_eq_prime_pow (p := 2) (n := 1) (by rwa [pow_one, sq]) hu4
    set F := R ⊓ centralizer ({u} : Set G) with hF
    have hu2F : u ^ 2 ∈ F := mem_inf.mpr ⟨hu2R, mem_centralizer_singleton_iff.mpr (by group)⟩
    have hu2r : u ^ 2 * r = r * u ^ 2 := c.R_comm hu2R hr
    have hur' : u * r' * u⁻¹ = r := by
      have h : u * r' * u⁻¹ = u ^ 2 * r * (u ^ 2)⁻¹ := by
        rw [hr', sq]
        group
      rw [h, hu2r, mul_inv_cancel_right]
    have hrr'F : r * r' ∈ F := by
      refine mem_inf.mpr ⟨mul_mem hr hr'R, mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : u * (r * r') * u⁻¹ = r * r' := by
        calc u * (r * r') * u⁻¹ = (u * r * u⁻¹) * (u * r' * u⁻¹) := by group
          _ = r' * r := by rw [← hr', hur']
          _ = r * r' := c.R_comm hr'R hr
      calc r * r' * u = (u * (r * r') * u⁻¹) * u := by rw [h1]
        _ = u * (r * r') := by group
    have hFR : F ≠ R := fun h => hru (by
      have : r ∈ F := h ▸ hr
      exact (mem_centralizer_singleton_iff.mp (mem_inf.mp this).2).symm)
    have hF2 : Nat.card F = 2 := by
      have hd : Nat.card F ∣ 4 := c.pair.card_R ▸ Subgroup.card_dvd_of_le inf_le_left
      have hne4 : Nat.card F ≠ 4 := fun h4 => hFR (eq_of_le_of_card_ge inf_le_left
        (by rw [h4, c.pair.card_R]))
      have hne1 : Nat.card F ≠ 1 := fun h1 => by
        have := (Subgroup.card_eq_one.mp h1) ▸ hu2F
        rw [mem_bot] at this
        exact hu2 (by rw [← sq, this])
      obtain ⟨j, hj, hje⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        (show Nat.card F ∣ 2 ^ 2 from hd)
      interval_cases j
      · exact absurd hje hne1
      · exact hje
      · exact absurd hje hne4
    have hzF : zpowers (u ^ 2) = F := by
      refine eq_of_le_of_card_ge (zpowers_le.mpr hu2F) ?_
      rw [hF2, Nat.card_zpowers]
      have : orderOf (u ^ 2) = 2 :=
        orderOf_eq_prime (by rw [← pow_mul]; exact hu4) (fun h => hu2 (by rw [← sq, h]))
      rw [this]
    have hrr' : r * r' = u ^ 2 := by
      classical
      have h := hzF ▸ hrr'F
      rw [mem_zpowers_iff_mem_range_orderOf] at h
      have ho : orderOf (u ^ 2) = 2 :=
        orderOf_eq_prime (by rw [← pow_mul]; exact hu4) (fun h => hu2 (by rw [← sq, h]))
      rw [ho] at h
      obtain ⟨n, hn, hne⟩ := Finset.mem_image.mp h
      have hn2 : n < 2 := Finset.mem_range.mp hn
      interval_cases n
      · exfalso
        rw [pow_zero] at hne
        exact hr'r (by rw [eq_inv_of_mul_eq_one_right hne.symm, hrinv])
      · rw [← hne, pow_one]
    refine hu.nonempty_sup_equiv_of huP hu.mem_NA (hu.act _) huo hr hr1 ?_ ?_
    · intro h
      exact hru (by rw [h]; group)
    ·
      have h1 : u⁻¹ * r * u = r' := by
        calc u⁻¹ * r * u = (u ^ 2)⁻¹ * (u * r * u⁻¹) * u ^ 2 := by rw [sq]; group
          _ = r' := by
            rw [← hr', mul_assoc, ← c.R_comm hu2R hr'R, inv_mul_cancel_left]
      calc r * u * r⁻¹ = u * (u⁻¹ * r * u) * r := by rw [hrinv]; group
        _ = u * (r' * r) := by rw [h1, mul_assoc]
        _ = u * u ^ 2 := by rw [← c.R_comm hr hr'R, hrr']
        _ = u⁻¹ := by
          rw [← pow_succ', eq_inv_iff_mul_eq_one, ← pow_succ]
          exact hu4

theorem hasDihedralSylowTwo : HasDihedralSylowTwo c.H := by
  obtain ⟨S, hS⟩ := hu.isSylowOf_sup
  obtain ⟨e⟩ := hu.nonempty_sup_equiv
  have e' : (S : Subgroup c.H) ≃* DihedralGroup (2 ^ 2) :=
    ((S : Subgroup c.H).equivMapOfInjective c.H.subtype c.H.subtype_injective).trans
      ((MulEquiv.subgroupCongr hS).trans e)
  exact hasDihedralSylowTwo_of_equiv S (m := 2) (by norm_num) e'

theorem factorization_H : (Nat.card c.H).factorization 2 = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hu.isSylowOf_sup.card_eq
  rw [hu.card_sup] at h
  have h2 : (2 : ℕ) ^ 3 = 2 ^ (Nat.card c.H).factorization 2 := by rw [← h]; norm_num
  exact (Nat.pow_right_injective le_rfl h2).symm

theorem eight_dvd_Hbar : 8 ∣ Nat.card c.Hbar := by
  have hH : 2 ^ 3 ∣ Nat.card c.H := by
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne', hu.factorization_H]
  rw [card_eq_card_quotient_mul_card_subgroup (CFSG.pPrimeCore 2 c.H)] at hH
  exact (Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr c.odd_card_core)).dvd_of_dvd_mul_right hH

theorem not_sixteen_dvd_Hbar : ¬ 16 ∣ Nat.card c.Hbar := by
  intro h16
  have hH : 2 ^ 4 ∣ Nat.card c.H := by
    rw [card_eq_card_quotient_mul_card_subgroup (CFSG.pPrimeCore 2 c.H)]
    exact Dvd.dvd.mul_right h16 _
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne', hu.factorization_H]
    at hH
  omega

end IsOuter

end CaseICoords

end CFSG.ComponentClassification.RankTwoAltFive
