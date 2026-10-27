module

public import CFSG.GH74.E2.OuterDich
public import CFSG.GH74.E2.OuterRank
public import CFSG.GH74.E2.CaseIInner
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.E2

open Subgroup

theorem card_cen_outer {C : Type*} [Group C] [Finite C] {K : Subgroup C} [K.Normal]
    (hcen : Subgroup.center ↥K = ⊥) (hOut2 : Nat.card (MulAut ↥K) = 2 * Nat.card ↥K)
    (hout : ¬ ∀ g : C, ∃ k ∈ K, ∀ x ∈ K, g * x * g⁻¹ = k * x * k⁻¹) :
    Nat.card C = Nat.card ↥(Subgroup.centralizer (K : Set C)) * (2 * Nat.card ↥K) := by
  classical
  let θ : C →* MulAut ↥K := MulAut.conjNormal
  have hker : θ.ker = Subgroup.centralizer (K : Set C) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro h q hq
      have h1 := congrArg (fun σ : MulAut ↥K => (σ ⟨q, hq⟩ : C)) h
      simp only [θ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc q * x = (x * q * x⁻¹) * x := by rw [h1]
        _ = x * q := by group
    · intro h
      ext ⟨q, hq⟩
      simp only [θ, MulAut.conjNormal_apply, MulAut.one_apply]
      rw [← h q hq]
      group
  let Inn : Subgroup (MulAut ↥K) := (MulAut.conj : ↥K →* MulAut ↥K).range
  have hInnCard : Nat.card Inn = Nat.card ↥K := by
    have hinj : Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rw [eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have : x ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro g
        have := congrArg (fun σ : MulAut ↥K => σ g) hx
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc g * x = (x * g * x⁻¹) * x := by rw [this]
          _ = x * g := by group
      rw [hcen] at this
      exact this
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hInnLe : Inn ≤ θ.range := by
    rintro _ ⟨k, rfl⟩
    exact ⟨(k : C), by rw [MulAut.conjNormal_val]⟩
  have hdvdAut : Nat.card θ.range ∣ Nat.card (MulAut ↥K) := Subgroup.card_subgroup_dvd_card _
  have hdvdInn : Nat.card Inn ∣ Nat.card θ.range := Subgroup.card_dvd_of_le hInnLe
  have hne : Inn ≠ θ.range := by
    intro heq
    apply hout
    intro g
    have : θ g ∈ Inn := by rw [heq]; exact ⟨g, rfl⟩
    obtain ⟨k, hk⟩ := this
    refine ⟨(k : C), k.2, fun x hx => ?_⟩
    have := congrArg (fun σ : MulAut ↥K => (σ ⟨x, hx⟩ : C)) hk
    simp only [MulAut.conj_apply, θ, MulAut.conjNormal_apply] at this
    exact this.symm
  have hlt : Nat.card Inn < Nat.card θ.range := by
    refine lt_of_le_of_ne (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hInnLe)) ?_
    intro h
    exact hne (Subgroup.eq_of_le_of_card_ge hInnLe h.ge)
  have hY : Nat.card θ.range = 2 * Nat.card ↥K := by
    obtain ⟨m, hm⟩ := hdvdInn
    rw [hInnCard] at hm
    rw [hOut2, hm] at hdvdAut
    have hKpos : 0 < Nat.card ↥K := Nat.card_pos
    have hm2 : m ∣ 2 := (Nat.mul_dvd_mul_iff_left hKpos).1 (by rwa [mul_comm 2] at hdvdAut)
    have hm1 : m ≠ 1 := by
      intro h1
      rw [h1, mul_one, ← hInnCard] at hm
      omega
    have : m = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hm2 with h | h
      · exact absurd h hm1
      · exact h
    rw [hm, this, mul_comm]
  have := Subgroup.card_ker_mul_card_range θ
  rw [hker, hY] at this
  exact this.symm


theorem card_sylow_outer {C : Type} [Group C] [Finite C] {K D : Subgroup C} {SK SD S₁ : Subgroup C}
    (hcard : Nat.card C = Nat.card D * (2 * Nat.card K)) (hSKK : SK ≤ K) (hSKp : IsPGroup 2 SK)
    (hSKmax : ∀ P : Subgroup C, IsPGroup 2 P → P ≤ K → SK ≤ P → P = SK) (hSDD : SD ≤ D)
    (hSDp : IsPGroup 2 SD)
    (hSDmax : ∀ P : Subgroup C, IsPGroup 2 P → P ≤ D → SD ≤ P → P = SD)
    (hS1p : IsPGroup 2 S₁) (hS1max : ∀ P : Subgroup C, IsPGroup 2 P → S₁ ≤ P → P = S₁) :
    Nat.card S₁ = 2 * (Nat.card SK * Nat.card SD) := by
  have h1 : Nat.card S₁ = 2 ^ (Nat.card C).factorization 2 := by
    have := card_of_max (K := (⊤ : Subgroup C)) le_top hS1p (fun P hP _ h => hS1max P hP h)
    rwa [Subgroup.card_top] at this
  have h2 : Nat.card SK = 2 ^ (Nat.card K).factorization 2 := card_of_max hSKK hSKp hSKmax
  have h3 : Nat.card SD = 2 ^ (Nat.card D).factorization 2 := card_of_max hSDD hSDp hSDmax
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hD0 : Nat.card D ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card C).factorization 2 =
      (Nat.card D).factorization 2 + (1 + (Nat.card K).factorization 2) := by
    rw [hcard, Nat.factorization_mul hD0 (by positivity), Nat.factorization_mul (by norm_num) hK0]
    simp only [Finsupp.add_apply]
    rw [Nat.Prime.factorization_self Nat.prime_two]
  rw [h1, h2, h3, hfac]
  ring


theorem q8_center_eq {C : Type*} [Group C] {Q : Subgroup C} (e : ↥Q ≃* QuaternionGroup 2) {t : C}
    (htQ : t ∈ Q) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∀ y ∈ Q, (∀ q ∈ Q, y * q = q * y) → y = 1 ∨ y = t := by
  intro y hy hc
  have hcen : ∀ x : QuaternionGroup 2, (∀ z : QuaternionGroup 2, x * z = z * x) →
      x = 1 ∨ x = QuaternionGroup.a 2 := by decide
  have hsq := quat_sq_eq_one (m := 2) (Or.inl rfl)
  have het : e ⟨t, htQ⟩ = QuaternionGroup.a 2 := by
    have h1 : e ⟨t, htQ⟩ * e ⟨t, htQ⟩ = 1 := by
      rw [← map_mul]
      have : (⟨t, htQ⟩ : ↥Q) * ⟨t, htQ⟩ = 1 := Subtype.ext ht2
      rw [this, map_one]
    rcases hsq _ h1 with h | h
    · exfalso
      apply ht1
      have : (⟨t, htQ⟩ : ↥Q) = 1 := e.injective (by rw [h, map_one])
      exact congrArg Subtype.val this
    · exact h
  have hy' : (e ⟨y, hy⟩) = 1 ∨ e ⟨y, hy⟩ = QuaternionGroup.a 2 := by
    apply hcen
    intro z
    obtain ⟨q, rfl⟩ := e.surjective z
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc q q.2)
  rcases hy' with h | h
  · left
    have : (⟨y, hy⟩ : ↥Q) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val this
  · right
    have : (⟨y, hy⟩ : ↥Q) = ⟨t, htQ⟩ := e.injective (by rw [h, het])
    exact congrArg Subtype.val this


theorem false_of_sixteen
    {S : Type*} [Group S] [Finite S] (hS : Gen4 S) (hS2 : IsPGroup 2 S)
    {Q T TK : Subgroup S} (hQn : Q.Normal) (hTn : T.Normal)
    (hQ8 : Nonempty (↥Q ≃* QuaternionGroup 2)) (hT16 : Nat.card ↥T = 16)
    (hC : Nat.card ↥(T ⊓ Subgroup.centralizer (Q : Set S)) = 2)
    (hdisj : TK ⊓ T = ⊥) (eK : ↥TK ≃* OuterRank.SD) (hidx : (TK ⊔ T).index = 2) : False := by
  have hA := caseA_of_card_sixteen hS2 hQn hQ8 hT16 hC
  have h2 := dich_case_A_q8 hS hS2 hQn hTn hQ8 hA
  have h3 := rank_quot_ge_three T TK hdisj eK hidx
  omega

theorem dt_structure
    {C : Type} [Group C] [Finite C] {Q K : Subgroup C} (hloc : LocalK C Q K)
    (hQ8 : Nonempty (↥Q ≃* QuaternionGroup 2)) {c : C} (hc3 : orderOf c = 3)
    (hcK : ∀ k ∈ K, c * k = k * c) :
    Q ≤ Subgroup.centralizer (K : Set C) ∧
    ∀ P : Sylow 2 ↥(Subgroup.centralizer (K : Set C)),
      (Nat.card ↥(Subgroup.centralizer (K : Set C)) = 24 ∧
        (P : Subgroup ↥(Subgroup.centralizer (K : Set C))).map
          (Subgroup.centralizer (K : Set C)).subtype = Q) ∨
      (Nat.card ↥(Subgroup.centralizer (K : Set C)) = 48 ∧
        Nat.card ↥((P : Subgroup ↥(Subgroup.centralizer (K : Set C))).map
          (Subgroup.centralizer (K : Set C)).subtype) = 16 ∧
        Q ≤ (P : Subgroup ↥(Subgroup.centralizer (K : Set C))).map
          (Subgroup.centralizer (K : Set C)).subtype) := by
  classical
  set D : Subgroup C := Subgroup.centralizer (K : Set C) with hD
  have hQD : Q ≤ D := fun q hq =>
    Subgroup.mem_centralizer_iff.2 fun k hk => (hloc.commute q hq k hk).symm
  let Q' : Subgroup ↥D := Q.subgroupOf D
  have : Q'.Normal := hloc.Q_normal.subgroupOf D
  have hC' : ∀ d : ↥D, (∀ q ∈ Q', d * q = q * d) → d ∈ Q' := by
    intro d hd
    have h1 : ∀ q ∈ Q, (d : C) * q = q * d := fun q hq =>
      congrArg Subtype.val (hd ⟨q, hQD hq⟩ (Subgroup.mem_subgroupOf.2 hq))
    have h2 : ∀ k ∈ K, (d : C) * k = k * d := fun k hk =>
      (Subgroup.mem_centralizer_iff.1 d.2 k hk).symm
    exact Subgroup.mem_subgroupOf.2 (hloc.self_centralizing d h1 h2)
  have h3 : 3 ∣ Nat.card ↥D := by
    have hcD : c ∈ D := Subgroup.mem_centralizer_iff.2 fun k hk => (hcK k hk).symm
    have : orderOf (⟨c, hcD⟩ : ↥D) = 3 := by rw [← Subgroup.orderOf_coe]; exact hc3
    rw [← this]
    exact orderOf_dvd_natCard _
  have hQ' : Nonempty (↥Q' ≃* QuaternionGroup 2) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hQD).trans hQ8.some⟩
  have hQp' : IsPGroup 2 ↥Q' :=
    hloc.Q_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hQD).symm
  refine ⟨hQD, fun P => ?_⟩
  have hQ'P : Q' ≤ (P : Subgroup ↥D) := hQp'.le_sylow_of_normal P
  have hQP : Q ≤ (P : Subgroup ↥D).map D.subtype := fun x hx =>
    ⟨⟨x, hQD hx⟩, hQ'P (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hPcard : Nat.card (P : Subgroup D) = 2 ^ (Nat.card D).factorization 2 :=
    P.card_eq_multiplicity
  have hmapcard : Nat.card ((P : Subgroup D).map D.subtype) = Nat.card (P : Subgroup D) :=
    Subgroup.card_map_of_injective D.subtype_injective
  rcases sylow_two_of_Dt Q' hQ' hC' h3 P with ⟨h24, hPQ⟩ | ⟨h48, -⟩ | ⟨h48, -⟩
  · left
    refine ⟨h24, ?_⟩
    rw [hPQ]
    exact Subgroup.map_subgroupOf_eq_of_le hQD
  · right
    refine ⟨h48, ?_, hQP⟩
    have hfac : (Nat.card D).factorization 2 = 4 := by
      rw [h48, show (48 : ℕ) = 2 ^ 4 * 3 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization Nat.prime_three]
      simp
    rw [hmapcard, hPcard, hfac]
    norm_num
  · right
    refine ⟨h48, ?_, hQP⟩
    have hfac : (Nat.card D).factorization 2 = 4 := by
      rw [h48, show (48 : ℕ) = 2 ^ 4 * 3 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization Nat.prime_three]
      simp
    rw [hmapcard, hPcard, hfac]
    norm_num


theorem involutions_D24
    {C : Type} [Group C] [Finite C] {Q K : Subgroup C} (hloc : LocalK C Q K)
    (hQ8 : Nonempty (↥Q ≃* QuaternionGroup 2)) {t : C} (ht : orderOf t = 2) (htQ : t ∈ Q)
    {c : C} (hc3 : orderOf c = 3) (hcK : ∀ k ∈ K, c * k = k * c)
    (hD24 : Nat.card ↥(Subgroup.centralizer (K : Set C)) = 24) :
    ∀ u ∈ Subgroup.centralizer (K : Set C), u ^ 2 = 1 → u = 1 ∨ u = t := by
  classical
  intro u hu hu2
  obtain ⟨hQD, hcases⟩ := dt_structure hloc hQ8 hc3 hcK
  set D := Subgroup.centralizer (K : Set C) with hD
  let u' : ↥D := ⟨u, hu⟩
  have hu'2 : u' ^ 2 = 1 := Subtype.ext (by simpa using hu2)
  have hord : orderOf u' ∣ 2 ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one hu'2
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have hZ : IsPGroup 2 ↥(Subgroup.zpowers u') :=
    IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨P, hP⟩ := hZ.exists_le_sylow
  have huP : u' ∈ (P : Subgroup ↥D) := hP (Subgroup.mem_zpowers u')
  rcases hcases P with ⟨-, hPQ⟩ | ⟨h48, -⟩
  · have huQ : u ∈ Q := by
      have : u ∈ (P : Subgroup ↥D).map D.subtype := ⟨u', huP, rfl⟩
      rwa [hPQ] at this
    obtain ⟨e⟩ := hQ8
    have hta := eD_t_eq_a htQ ht (m := 2) (Or.inl rfl) e
    have hsq : e ⟨u, huQ⟩ * e ⟨u, huQ⟩ = 1 := by
      rw [← map_mul]
      have : (⟨u, huQ⟩ : ↥Q) * ⟨u, huQ⟩ = 1 := Subtype.ext (by simpa [sq] using hu2)
      rw [this, map_one]
    rcases quat_sq_eq_one (m := 2) (Or.inl rfl) _ hsq with h | h
    · left
      have : (⟨u, huQ⟩ : ↥Q) = 1 := e.injective (by rw [h, map_one])
      exact congrArg Subtype.val this
    · right
      have : (⟨u, huQ⟩ : ↥Q) = ⟨t, htQ⟩ := e.injective (by rw [h, hta])
      exact congrArg Subtype.val this
  · omega

theorem card_D_ne_48
    {C : Type} [Group C] [Finite C] (hgen : Gen4 C) {Q K : Subgroup C}
    (hloc : LocalK C Q K) (hQ8 : Nonempty (↥Q ≃* QuaternionGroup 2)) {t : C} (ht : orderOf t = 2)
    (htQ : t ∈ Q) (htc : ∀ g : C, g * t = t * g) (hcen : Subgroup.center ↥K = ⊥)
    (hT : SD16Tables ↥K) (hOut2 : Nat.card (MulAut ↥K) = 2 * Nat.card ↥K)
    (hout : ¬ ∀ g : C, ∃ k ∈ K, ∀ x ∈ K, g * x * g⁻¹ = k * x * k⁻¹)
    {c : C} (hc3 : orderOf c = 3) (hcK : ∀ k ∈ K, c * k = k * c) :
    Nat.card ↥(Subgroup.centralizer (K : Set C)) ≠ 48 := by
  classical
  intro h48
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKn := hloc.K_normal
  have hQn := hloc.Q_normal
  set D : Subgroup C := Subgroup.centralizer (K : Set C) with hD
  obtain ⟨hQD, hDcases⟩ := dt_structure hloc hQ8 hc3 hcK
  obtain ⟨PD⟩ : Nonempty (Sylow 2 ↥D) := inferInstance
  obtain ⟨TK⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  obtain ⟨h16, hQSD⟩ : Nat.card ↥((PD : Subgroup ↥D).map D.subtype) = 16 ∧
      Q ≤ (PD : Subgroup ↥D).map D.subtype := by
    rcases hDcases PD with ⟨h24, -⟩ | ⟨-, h16, hQ⟩
    · exact absurd (h24.symm.trans h48) (by norm_num)
    · exact ⟨h16, hQ⟩
  obtain ⟨SK, hSKdef⟩ : ∃ SK : Subgroup C, SK = (TK : Subgroup ↥K).map K.subtype := ⟨_, rfl⟩
  obtain ⟨SD, hSDdef⟩ : ∃ SD : Subgroup C, SD = (PD : Subgroup ↥D).map D.subtype := ⟨_, rfl⟩
  rw [← hSDdef] at h16 hQSD
  have hSKK : SK ≤ K := by rw [hSKdef]; exact sylow_map_le K TK
  have hSKp : IsPGroup 2 SK := by rw [hSKdef]; exact sylow_map_isPGroup K TK
  have hSKmax : ∀ P : Subgroup C, IsPGroup 2 P → P ≤ K → SK ≤ P → P = SK := fun P hP h1 h2 => by
    rw [hSKdef] at h2 ⊢
    exact sylow_map_max K TK P hP h1 h2
  have hSDD : SD ≤ D := by rw [hSDdef]; exact sylow_map_le D PD
  have hSDp : IsPGroup 2 SD := by rw [hSDdef]; exact sylow_map_isPGroup D PD
  have hSDmax : ∀ P : Subgroup C, IsPGroup 2 P → P ≤ D → SD ≤ P → P = SD := fun P hP h1 h2 => by
    rw [hSDdef] at h2 ⊢
    exact sylow_map_max D PD P hP h1 h2
  have hcomm : ∀ k ∈ K, ∀ d ∈ D, k * d = d * k := fun k hk d hd =>
    Subgroup.mem_centralizer_iff.1 hd k hk
  have hdisj : K ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxD⟩
    have hxz : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxD y y.2)
    rw [hcen, Subgroup.mem_bot] at hxz
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxz
  have hcommS : ∀ a ∈ SK, ∀ b ∈ SD, a * b = b * a := fun a ha b hb =>
    hcomm a (hSKK ha) b (hSDD hb)
  have hdisjS : SK ⊓ SD = ⊥ := le_bot_iff.1 ((inf_le_inf hSKK hSDD).trans hdisj.le)
  have hprod : Nat.card ↥(SK ⊔ SD) = Nat.card SK * Nat.card SD := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (prodSupEquiv SK SD hcommS hdisjS).toEquiv).symm
  have hS12 : IsPGroup 2 ↥(SK ⊔ SD) := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hSKp
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hSDp
    exact IsPGroup.of_card (n := a + b) (by rw [hprod, ha, hb, pow_add])
  obtain ⟨S, hS⟩ := hS12.exists_le_sylow
  have hcard := card_cen_outer (K := K) hcen hOut2 hout
  have hS1card := card_sylow_outer (K := K) (D := D) hcard hSKK hSKp hSKmax hSDD hSDp hSDmax
    S.isPGroup' (fun P hP h => S.is_maximal' hP h)
  set S₁ : Subgroup C := (S : Subgroup C) with hS₁def
  have hSKS : SK ≤ S₁ := le_sup_left.trans hS
  have hSDS : SD ≤ S₁ := le_sup_right.trans hS
  have hQS : Q ≤ S₁ := hQSD.trans hSDS
  have hSDeq : S₁ ⊓ D = SD := hSDmax _ S.isPGroup'.to_inf_left inf_le_right (le_inf hSDS hSDD)
  have hDn : D.Normal := Subgroup.normal_centralizer
  have hTn : (SD.subgroupOf S₁).Normal := by
    have : SD.subgroupOf S₁ = D.subgroupOf S₁ := by
      ext x
      simp only [Subgroup.mem_subgroupOf]
      constructor
      · intro h
        exact hSDD h
      · intro h
        rw [← hSDeq]
        exact ⟨x.2, h⟩
    rw [this]
    exact hDn.subgroupOf S₁
  have hQ8S : Nonempty (↥(Q.subgroupOf S₁) ≃* QuaternionGroup 2) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hQS).trans hQ8.some⟩
  have hT16S : Nat.card ↥(SD.subgroupOf S₁) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSDS).toEquiv]
    exact h16
  have hC : Nat.card ↥(SD.subgroupOf S₁ ⊓
      Subgroup.centralizer ((Q.subgroupOf S₁ : Subgroup ↥S₁) : Set ↥S₁)) = 2 := by
    obtain ⟨e⟩ := hQ8
    have ht1 : t ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ht
      exact absurd ht (by norm_num)
    have ht2 : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht, pow_two] at this
    have htSD : t ∈ SD := hQSD htQ
    have htS : t ∈ S₁ := hSDS htSD
    rw [Nat.card_eq_two_iff]
    refine ⟨1, ⟨⟨t, htS⟩, Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 htSD, ?_⟩⟩, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro q _
      exact Subtype.ext (htc q)
    · intro h
      apply ht1
      have := congrArg (fun x : ↥(SD.subgroupOf S₁ ⊓ Subgroup.centralizer
        ((Q.subgroupOf S₁ : Subgroup ↥S₁) : Set ↥S₁)) => ((x : ↥S₁) : C)) h
      simpa using this.symm
    · ext ⟨x, hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      have hxD : (x : C) ∈ D := hSDD (Subgroup.mem_subgroupOf.1 hx1)
      have hxQ : (x : C) ∈ Q := by
        refine hloc.self_centralizing x ?_ ?_
        · intro q hq
          have := Subgroup.mem_centralizer_iff.1 hx2 ⟨q, hQS hq⟩ (Subgroup.mem_subgroupOf.2 hq)
          exact (congrArg Subtype.val this).symm
        · intro k hk
          exact (Subgroup.mem_centralizer_iff.1 hxD k hk).symm
      have hxc : ∀ q ∈ Q, (x : C) * q = q * x := by
        intro q hq
        have := Subgroup.mem_centralizer_iff.1 hx2 ⟨q, hQS hq⟩ (Subgroup.mem_subgroupOf.2 hq)
        exact (congrArg Subtype.val this).symm
      have hxe : (x : C) = 1 ∨ (x : C) = t := by
        have hta := eD_t_eq_a htQ ht (m := 2) (Or.inl rfl) e
        have hcen2 : ∀ z : QuaternionGroup 2, (∀ w : QuaternionGroup 2, z * w = w * z) →
            z = 1 ∨ z = QuaternionGroup.a (2 : ℕ) := by decide
        have h1 : e ⟨x, hxQ⟩ = 1 ∨ e ⟨x, hxQ⟩ = QuaternionGroup.a (2 : ℕ) := by
          apply hcen2
          intro w
          obtain ⟨q, rfl⟩ := e.surjective w
          rw [← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (hxc q q.2)
        rcases h1 with h | h
        · left
          have : (⟨x, hxQ⟩ : ↥Q) = 1 := e.injective (by rw [h, map_one])
          exact congrArg Subtype.val this
        · right
          have : (⟨x, hxQ⟩ : ↥Q) = ⟨t, htQ⟩ := e.injective (by rw [h, hta])
          exact congrArg Subtype.val this
      rcases hxe with h | h
      · left
        exact Subtype.ext (Subtype.ext (by simpa using h))
      · right
        exact Subtype.ext (Subtype.ext h)
  have hdisj' : SK.subgroupOf S₁ ⊓ SD.subgroupOf S₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have : (x : C) ∈ SK ⊓ SD := ⟨hx1, hx2⟩
    rw [hdisjS, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Subtype.ext this
  let eK : ↥(SK.subgroupOf S₁) ≃* OuterRank.SD :=
    (Subgroup.subgroupOfEquivOfLe hSKS).trans
      ((MulEquiv.subgroupCongr hSKdef).trans
        (((sylowMapEquiv K TK).symm.trans (hT.sylow TK).some).trans
          (CFSG.Semidihedral.presentationEquivModel 4 (by norm_num))))
  have hidx : (SK.subgroupOf S₁ ⊔ SD.subgroupOf S₁).index = 2 := by
    rw [← Subgroup.subgroupOf_sup hSKS hSDS]
    have h1 := Subgroup.index_mul_card ((SK ⊔ SD).subgroupOf S₁)
    have hc1 : Nat.card ↥((SK ⊔ SD).subgroupOf S₁) = Nat.card ↥(SK ⊔ SD) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hSKS hSDS)).toEquiv
    rw [hc1, hprod, hS1card] at h1
    have hpos : 0 < Nat.card SK * Nat.card SD := Nat.mul_pos Nat.card_pos Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1])
  exact false_of_sixteen (hgen.subgroup S₁ ) S.isPGroup' (hQn.subgroupOf S₁) hTn hQ8S hT16S hC
    hdisj' eK hidx

end CFSG.GH74.E2
