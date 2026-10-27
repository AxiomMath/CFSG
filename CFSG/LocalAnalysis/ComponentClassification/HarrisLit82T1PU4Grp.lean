module

public import CFSG.GH74.GLS.Bg.Local.Transfer1515

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup
open CFSG.GH74.GLS.Bg.Thompson (IsSylowIn)

section Sylow

theorem mem_zpowers_of_mul_self_eq_one {G : Type*} [Group G] {x y : G} (hx : x * x = 1) :
    y ∈ zpowers x ↔ y = 1 ∨ y = x := by
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, zpow_two, hx, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, hx, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem isPGroup_zpowers_of_mul_self {G : Type*} [Group G] {x : G} (hx : x * x = 1) :
    IsPGroup 2 ↥(zpowers x) := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hx])
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem exists_conj_mem_of_isSylowIn {A : Type*} [Group A] [Finite A] {C P : Subgroup A}
    (hP : IsSylowIn 2 P C) {x : A} (hxC : x ∈ C) (hx : x * x = 1) :
    ∃ c ∈ C, c * x * c⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPC, hP2, hidx⟩ := hP
  have hP2' : IsPGroup 2 ↥(P.subgroupOf C) := hP2.of_equiv (subgroupOfEquivOfLe hPC).symm
  let S : Sylow 2 ↥C := hP2'.toSylow hidx
  have hX : IsPGroup 2 ↥(zpowers (⟨x, hxC⟩ : ↥C)) :=
    isPGroup_zpowers_of_mul_self (Subtype.ext hx)
  obtain ⟨T, hT⟩ := hX.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥C) S T
  have hxT : (⟨x, hxC⟩ : ↥C) ∈ (T : Subgroup ↥C) := hT (mem_zpowers _)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.conj_inv_apply] at hxT
  refine ⟨((g⁻¹ : ↥C) : A), (g⁻¹).2, ?_⟩
  have h1 : ((g⁻¹ * ⟨x, hxC⟩ * g : ↥C) : A) ∈ P := hxT
  simpa using h1

end Sylow

section Conclusion

variable {A : Type*} [Group A]

@[expose] def IsU4Complement (I P V : Subgroup A) : Prop :=
  V ≤ P ∧ P ⊓ I ≤ V ∧ (∀ s ∈ P, ∀ v ∈ V, s * v * s⁻¹ ∈ V) ∧
    (∀ v ∈ V, ∀ w ∈ V, v ∉ I → w ∉ I → v⁻¹ * w ∈ I) ∧
    (∃ b ∈ P, ∀ s ∈ P, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ V) ∧
    (∀ v ∈ V, v * v = 1 → v ∈ I) ∧
    ((∃ s ∈ P, s ∉ V) → ∃ x ∈ P, x ∉ I ∧ x * x = 1)

theorem isU4Complement_inf {I P : Subgroup A} [I.Normal] {g : A} (hg : g ∈ P)
    (hgen : ∀ s ∈ P, ∃ k : ℤ, (g ^ k)⁻¹ * s ∈ P ⊓ I)
    (hlast : (∃ s ∈ P, s ∉ P ⊓ I) → ∃ x ∈ P, x ∉ I ∧ x * x = 1) :
    IsU4Complement I P (P ⊓ I) :=
  ⟨inf_le_left, le_rfl, fun s hs v hv => ⟨P.mul_mem (P.mul_mem hs hv.1) (P.inv_mem hs),
      (inferInstance : I.Normal).conj_mem v hv.2 s⟩,
    fun _ hv _ _ hvI _ => absurd hv.2 hvI, ⟨g, hg, hgen⟩, fun _ hv _ => hv.2, hlast⟩

end Conclusion

section Out

variable {A : Type*} [Group A] {I D : Subgroup A} [I.Normal] {φ : A}

structure OutData (I D : Subgroup A) (φ : A) : Prop where
  comm : ∀ a b : A, a * b * a⁻¹ * b⁻¹ ∈ I
  le : I ≤ D
  two : ∀ d ∈ D, ∀ e ∈ D, d ∉ I → e ∉ I → d⁻¹ * e ∈ I
  gen : ∀ a : A, ∃ k : ℤ, (φ ^ k)⁻¹ * a ∈ D
  pow : ∀ k : ℤ, φ ^ k ∈ D → φ ^ k = 1
  diag : ∀ d ∈ D, d ∉ I → ∃ x : A, x * x = 1 ∧ d⁻¹ * x ∈ I
  desc : ∀ x : A, x * x = 1 → x ∉ D → ∃ k : ℤ, φ ^ k * φ ^ k = 1 ∧ (φ ^ k)⁻¹ * x ∈ I

theorem mem_comap_zpowers {a b : A} (hb : b * b ∈ I) :
    a ∈ (zpowers (QuotientGroup.mk b : A ⧸ I)).comap (QuotientGroup.mk' I) ↔
      a ∈ I ∨ b⁻¹ * a ∈ I := by
  have hb' : (QuotientGroup.mk b : A ⧸ I) * QuotientGroup.mk b = 1 := by
    rw [← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hb
  rw [mem_comap, QuotientGroup.mk'_apply, mem_zpowers_of_mul_self_eq_one hb',
    QuotientGroup.eq_one_iff, eq_comm, QuotientGroup.eq]

namespace OutData

variable (h : OutData I D φ)
include h

omit [I.Normal] in
theorem mk_mul_comm (a b : A) :
    (QuotientGroup.mk (a * b) : A ⧸ I) = QuotientGroup.mk (b * a) := by
  rw [QuotientGroup.eq, mul_inv_rev]
  have h1 := h.comm b⁻¹ a⁻¹
  rw [inv_inv, inv_inv] at h1
  simpa only [mul_assoc] using h1

theorem quot_comm (x y : A ⧸ I) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h.mk_mul_comm]

theorem quot_sq_mul (x y : A ⧸ I) : x * y * (x * y) = x * x * (y * y) := by
  rw [mul_assoc, ← mul_assoc y x y, h.quot_comm y x, mul_assoc x y y, ← mul_assoc]

omit [I.Normal] in
theorem mul_self_mem {d : A} (hd : d ∈ D) : d * d ∈ I := by
  by_cases hdI : d ∈ I
  · exact mul_mem hdI hdI
  · have h1 := h.two d⁻¹ (inv_mem hd) d hd (fun h' => hdI (by simpa using inv_mem h')) hdI
    simpa using h1

omit [I.Normal] in
theorem normal_D : D.Normal :=
  ⟨fun d hd a => by
    have h1 : a * d * a⁻¹ = a * d * a⁻¹ * d⁻¹ * d := by group
    rw [h1]
    exact mul_mem (h.le (h.comm a d)) hd⟩

theorem exists_zpow_sq (u : A) :
    ∃ k : ℤ, (QuotientGroup.mk (u * u) : A ⧸ I) = QuotientGroup.mk (φ ^ k * φ ^ k) := by
  obtain ⟨k, hk⟩ := h.gen u
  refine ⟨k, ?_⟩
  obtain ⟨d, hd, rfl⟩ : ∃ d ∈ D, u = φ ^ k * d := ⟨_, hk, (mul_inv_cancel_left _ _).symm⟩
  have hdd : (QuotientGroup.mk d : A ⧸ I) * QuotientGroup.mk d = 1 := by
    rw [← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (h.mul_self_mem hd)
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, h.quot_sq_mul, hdd,
    mul_one]

theorem mul_self_mem_I {u : A} (hu : u * u ∈ D) : u * u ∈ I := by
  obtain ⟨k, hk⟩ := h.exists_zpow_sq u
  have h1 : (φ ^ k * φ ^ k)⁻¹ * (u * u) ∈ I := QuotientGroup.eq.mp hk.symm
  have h2 : φ ^ (k + k) ∈ D := by
    rw [zpow_add]
    have h3 := mul_mem hu (inv_mem (h.le h1))
    simpa [mul_assoc] using h3
  have h3 := h.pow _ h2
  rw [zpow_add] at h3
  rw [h3, QuotientGroup.mk_one] at hk
  exact (QuotientGroup.eq_one_iff _).mp hk

theorem good_sq {u : A} (hu2 : u * u * (u * u) ∈ D) :
    ∃ x : A, x * x = 1 ∧ (u * u)⁻¹ * x ∈ I := by
  obtain ⟨k, hk⟩ := h.exists_zpow_sq u
  refine ⟨φ ^ k * φ ^ k, ?_, QuotientGroup.eq.mp hk⟩
  have h1 : (QuotientGroup.mk (u * u * (u * u)) : A ⧸ I) =
      QuotientGroup.mk (φ ^ k * φ ^ k * (φ ^ k * φ ^ k)) := by
    rw [QuotientGroup.mk_mul, hk, ← QuotientGroup.mk_mul]
  have h3 : (φ ^ k * φ ^ k * (φ ^ k * φ ^ k))⁻¹ * (u * u * (u * u)) ∈ I :=
    QuotientGroup.eq.mp h1.symm
  have h4 : φ ^ (k + k + (k + k)) ∈ D := by
    rw [zpow_add, zpow_add]
    have h5 := mul_mem hu2 (inv_mem (h.le h3))
    simpa [mul_assoc] using h5
  have h6 := h.pow _ h4
  rwa [zpow_add, zpow_add] at h6

theorem not_good_mul {a δ : A} (ha : a ∉ D) (hga : ∃ x : A, x * x = 1 ∧ a⁻¹ * x ∈ I)
    (hδ : δ ∈ D) (hδI : δ ∉ I) : ¬ ∃ y : A, y * y = 1 ∧ (δ * a)⁻¹ * y ∈ I := by
  rintro ⟨y, hy, hay⟩
  obtain ⟨x, hx, hax⟩ := hga
  have hxD : x ∉ D := fun hxD => ha (by
    have h1 := mul_mem hxD (inv_mem (h.le hax))
    simpa [mul_assoc] using h1)
  have hyD : y ∉ D := fun hyD => ha (by
    have h1 := mul_mem hyD (inv_mem (h.le hay))
    have h2 : δ * a ∈ D := by simpa [mul_assoc] using h1
    simpa using mul_mem (inv_mem hδ) h2)
  obtain ⟨k, -, hk⟩ := h.desc x hx hxD
  obtain ⟨m, -, hm⟩ := h.desc y hy hyD
  have hδφ : (QuotientGroup.mk δ : A ⧸ I) = QuotientGroup.mk (φ ^ (m - k)) := by
    have e1 : (QuotientGroup.mk a : A ⧸ I) = QuotientGroup.mk x := QuotientGroup.eq.mpr hax
    have e2 : (QuotientGroup.mk (δ * a) : A ⧸ I) = QuotientGroup.mk y :=
      QuotientGroup.eq.mpr hay
    have e3 : (QuotientGroup.mk (φ ^ k) : A ⧸ I) = QuotientGroup.mk x := QuotientGroup.eq.mpr hk
    have e4 : (QuotientGroup.mk (φ ^ m) : A ⧸ I) = QuotientGroup.mk y := QuotientGroup.eq.mpr hm
    rw [QuotientGroup.mk_mul, e1, ← e3, ← e4] at e2
    rw [zpow_sub, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← e2, mul_inv_cancel_right]
  have hφD : φ ^ (m - k) ∈ D := by
    have h1 : δ⁻¹ * φ ^ (m - k) ∈ I := QuotientGroup.eq.mp hδφ
    simpa using mul_mem hδ (h.le h1)
  rw [h.pow _ hφD, QuotientGroup.mk_one] at hδφ
  exact hδI ((QuotientGroup.eq_one_iff δ).mp hδφ)

theorem isU4Complement_coset {P : Subgroup A} {b : A} (hbb : b * b ∈ I)
    (hbad : ¬ ∃ x : A, x * x = 1 ∧ b⁻¹ * x ∈ I) {g : A} (hg : g ∈ P)
    (hgen : ∀ s ∈ P, ∃ k : ℤ, (g ^ k)⁻¹ * s ∈
      P ⊓ (zpowers (QuotientGroup.mk b : A ⧸ I)).comap (QuotientGroup.mk' I))
    (hlast : (∃ s ∈ P, s ∉ P ⊓ (zpowers (QuotientGroup.mk b : A ⧸ I)).comap
      (QuotientGroup.mk' I)) → ∃ x ∈ P, x ∉ I ∧ x * x = 1) :
    IsU4Complement I P (P ⊓ (zpowers (QuotientGroup.mk b : A ⧸ I)).comap
      (QuotientGroup.mk' I)) := by
  refine ⟨inf_le_left, fun v hv => ⟨hv.1, (mem_comap_zpowers hbb).mpr (Or.inl hv.2)⟩,
    fun s hs v hv => ⟨P.mul_mem (P.mul_mem hs hv.1) (P.inv_mem hs), ?_⟩,
    fun v hv w hw hvI hwI => ?_, ⟨g, hg, hgen⟩, fun v hv hvv => ?_, hlast⟩
  · have hv2 : v ∈ (zpowers (QuotientGroup.mk b : A ⧸ I)).comap (QuotientGroup.mk' I) := hv.2
    show s * v * s⁻¹ ∈ (zpowers (QuotientGroup.mk b : A ⧸ I)).comap (QuotientGroup.mk' I)
    rw [mem_comap] at hv2 ⊢
    rw [map_mul, map_mul, map_inv, h.quot_comm (QuotientGroup.mk' I s), mul_inv_cancel_right]
    exact hv2
  · have hv' := ((mem_comap_zpowers hbb).mp hv.2).resolve_left hvI
    have hw' := ((mem_comap_zpowers hbb).mp hw.2).resolve_left hwI
    have h1 := mul_mem (inv_mem hv') hw'
    simpa [mul_assoc] using h1
  · by_contra hvI
    exact hbad ⟨v, hvv, ((mem_comap_zpowers hbb).mp hv.2).resolve_left hvI⟩

end OutData

theorem exists_isU4Complement [Finite A] (h : OutData I D φ) {C P : Subgroup A} (hIC : I ≤ C)
    (hP : IsSylowIn 2 P C) : ∃ V : Subgroup A, IsU4Complement I P V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPC : P ≤ C := hP.1
  have hP2 : IsPGroup 2 ↥P := hP.2.1
  have : D.Normal := h.normal_D
  have hinvol : ∀ a ∈ C, a ∉ I → (∃ x : A, x * x = 1 ∧ a⁻¹ * x ∈ I) →
      ∃ x ∈ P, x ∉ I ∧ x * x = 1 := by
    rintro a haC haI ⟨x, hx, hax⟩
    have hxC : x ∈ C := by simpa using mul_mem haC (hIC hax)
    obtain ⟨c, -, hcP⟩ := exists_conj_mem_of_isSylowIn hP hxC hx
    refine ⟨c * x * c⁻¹, hcP, fun hI' => haI ?_, ?_⟩
    · have hxI : x ∈ I := by
        have h1 := (inferInstance : I.Normal).conj_mem _ hI' c⁻¹
        simpa [mul_assoc] using h1
      simpa using mul_mem hxI (inv_mem hax)
    · calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
        _ = 1 := by rw [hx, mul_one, mul_inv_cancel]
  have hcyc : IsCyclic (A ⧸ D) := ⟨⟨QuotientGroup.mk φ, fun y => by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := h.gen a
    refine ⟨k, ?_⟩
    show (QuotientGroup.mk φ : A ⧸ D) ^ k = QuotientGroup.mk a
    rw [← QuotientGroup.mk_zpow]
    exact QuotientGroup.eq.mpr hk⟩⟩
  obtain ⟨⟨g₀, hg₀⟩, hgen⟩ := IsCyclic.exists_generator (α := ↥(P.map (QuotientGroup.mk' D)))
  obtain ⟨s₁, hs₁P, rfl⟩ := hg₀
  have hs₁ : ∀ s ∈ P, ∃ k : ℤ, (s₁ ^ k)⁻¹ * s ∈ D := by
    intro s hs
    obtain ⟨k, hk⟩ :=
      mem_zpowers_iff.mp (hgen ⟨QuotientGroup.mk' D s, Subgroup.mem_map.mpr ⟨s, hs, rfl⟩⟩)
    refine ⟨k, QuotientGroup.eq.mp ?_⟩
    have h1 := congrArg Subtype.val hk
    simpa using h1
  by_cases hPD : P ≤ D
  · by_cases hPI : P ≤ I
    ·
      refine ⟨P ⊓ I, isU4Complement_inf (one_mem P) (fun s hs => ⟨0, by simpa using
        (⟨hs, hPI hs⟩ : s ∈ P ⊓ I)⟩) fun ⟨s, hs, hsV⟩ => absurd ⟨hs, hPI hs⟩ hsV⟩
    ·
      obtain ⟨δ₁, hδ₁P, hδ₁I⟩ := IsConcreteLE.not_le_iff_exists.mp hPI
      refine ⟨P ⊓ I, isU4Complement_inf hδ₁P (fun s hs => ?_) fun _ =>
        hinvol δ₁ (hPC hδ₁P) hδ₁I (h.diag δ₁ (hPD hδ₁P) hδ₁I)⟩
      by_cases hsI : s ∈ I
      · exact ⟨0, by simpa using (⟨hs, hsI⟩ : s ∈ P ⊓ I)⟩
      · refine ⟨1, P.mul_mem (by simpa using P.inv_mem hδ₁P) hs, ?_⟩
        simpa using h.two δ₁ (hPD hδ₁P) s (hPD hs) hδ₁I hsI
  ·
    have hs₁D : s₁ ∉ D := fun hs₁D => hPD fun s hs => by
      obtain ⟨k, hk⟩ := hs₁ s hs
      simpa using mul_mem (zpow_mem hs₁D k) hk
    obtain ⟨e, he₀⟩ := (IsPGroup.iff_orderOf.mp (hP2.map (QuotientGroup.mk' D)))
      ⟨QuotientGroup.mk' D s₁, Subgroup.mem_map.mpr ⟨s₁, hs₁P, rfl⟩⟩
    have he : orderOf (QuotientGroup.mk s₁ : A ⧸ D) = 2 ^ e := (Subgroup.orderOf_coe _).trans he₀
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at he
      exact hs₁D he
    set t := s₁ ^ (2 ^ (e - 1)) with ht
    have htP : t ∈ P := pow_mem hs₁P _
    have hot : orderOf (QuotientGroup.mk t : A ⧸ D) = 2 := by
      rw [ht, QuotientGroup.mk_pow, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
        (by rw [he]; exact pow_dvd_pow 2 (Nat.sub_le e 1)), he, Nat.pow_div (Nat.sub_le e 1)
        two_pos, Nat.sub_sub_self (Nat.one_le_iff_ne_zero.mpr he0), pow_one]
    have htD : t ∉ D := by
      intro htD
      rw [(QuotientGroup.eq_one_iff t).mpr htD, orderOf_one] at hot
      exact absurd hot (by norm_num)
    have httD : t * t ∈ D := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← pow_two, ← hot, pow_orderOf_eq_one]
    have httI : t * t ∈ I := h.mul_self_mem_I httD
    have htI : t ∉ I := fun h' => htD (h.le h')
    have hsq : 2 ≤ e → ∃ x : A, x * x = 1 ∧ t⁻¹ * x ∈ I := by
      intro he2
      have htu : t = s₁ ^ (2 ^ (e - 2)) * s₁ ^ (2 ^ (e - 2)) := by
        rw [ht, ← pow_add, ← two_mul, ← pow_succ']
        congr 2
        omega
      rw [htu] at httD ⊢
      exact h.good_sq httD
    have hP1 : e = 1 → ∀ s ∈ P, s ∈ D ∨ t⁻¹ * s ∈ D := by
      intro he1 s hs
      obtain ⟨k, hk⟩ := hs₁ s hs
      have hts : t = s₁ := by rw [ht, he1]; simp
      have hmk : (QuotientGroup.mk s₁ : A ⧸ D) * QuotientGroup.mk s₁ = 1 := by
        rw [← pow_two, ← hts, ← hot, pow_orderOf_eq_one]
      have hmem : (QuotientGroup.mk s : A ⧸ D) ∈ zpowers (QuotientGroup.mk s₁ : A ⧸ D) := by
        rw [← QuotientGroup.eq.mpr hk, QuotientGroup.mk_zpow]
        exact zpow_mem_zpowers _ k
      rcases (mem_zpowers_of_mul_self_eq_one hmk).mp hmem with h1 | h1
      · exact Or.inl ((QuotientGroup.eq_one_iff s).mp h1)
      · exact Or.inr (by rw [hts]; exact QuotientGroup.eq.mp h1.symm)
    by_cases hPD' : ∃ δ₁ ∈ P, δ₁ ∈ D ∧ δ₁ ∉ I
    · obtain ⟨δ₁, hδ₁P, hδ₁D, hδ₁I⟩ := hPD'
      have hinv₁ : ∃ x ∈ P, x ∉ I ∧ x * x = 1 :=
        hinvol δ₁ (hPC hδ₁P) hδ₁I (h.diag δ₁ hδ₁D hδ₁I)
      by_cases hgt : ∃ x : A, x * x = 1 ∧ t⁻¹ * x ∈ I
      ·
        have hbD : δ₁ * t ∉ D := fun h' => htD (by simpa using mul_mem (inv_mem hδ₁D) h')
        have hbb : δ₁ * t * (δ₁ * t) ∈ I := by
          refine h.mul_self_mem_I ?_
          rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
            (QuotientGroup.eq_one_iff δ₁).mpr hδ₁D, one_mul, ← QuotientGroup.mk_mul,
            QuotientGroup.eq_one_iff]
          exact httD
        refine ⟨_, h.isU4Complement_coset hbb (h.not_good_mul htD hgt hδ₁D hδ₁I) hs₁P
          (fun s hs => ?_) fun _ => hinv₁⟩
        · obtain ⟨k, hk⟩ := hs₁ s hs
          have hkP : (s₁ ^ k)⁻¹ * s ∈ P := P.mul_mem (P.inv_mem (zpow_mem hs₁P k)) hs
          by_cases hkI : (s₁ ^ k)⁻¹ * s ∈ I
          · exact ⟨k, hkP, (mem_comap_zpowers hbb).mpr (Or.inl hkI)⟩
          · refine ⟨k + (2 ^ (e - 1) : ℕ), ?_, (mem_comap_zpowers hbb).mpr (Or.inr ?_)⟩
            · rw [zpow_add, zpow_natCast, ← ht, mul_inv_rev, mul_assoc]
              exact P.mul_mem (P.inv_mem htP) hkP
            ·
              have h1 := h.two δ₁ hδ₁D _ hk hδ₁I hkI
              have hc : (QuotientGroup.mk ((s₁ ^ k)⁻¹ * s) : A ⧸ I) = QuotientGroup.mk δ₁ :=
                (QuotientGroup.eq.mpr h1).symm
              have htinv : (QuotientGroup.mk t : A ⧸ I)⁻¹ = QuotientGroup.mk t := by
                rw [inv_eq_iff_mul_eq_one, ← QuotientGroup.mk_mul]
                exact (QuotientGroup.eq_one_iff _).mpr httI
              refine QuotientGroup.eq.mp ?_
              rw [zpow_add, zpow_natCast, ← ht, mul_inv_rev, mul_assoc, QuotientGroup.mk_mul,
                QuotientGroup.mk_mul, hc, QuotientGroup.mk_inv, htinv, h.quot_comm]
      ·
        have he1 : e = 1 := by
          by_contra he1
          exact hgt (hsq (by omega))
        refine ⟨_, h.isU4Complement_coset httI hgt hδ₁P (fun s hs => ?_) fun _ => hinv₁⟩
        have hsP := hs
        rcases hP1 he1 s hs with hsD | hsD
        · by_cases hsI : s ∈ I
          · exact ⟨0, by simpa using hsP, (mem_comap_zpowers httI).mpr (Or.inl (by simpa))⟩
          · refine ⟨1, by simpa using P.mul_mem (P.inv_mem hδ₁P) hsP,
              (mem_comap_zpowers httI).mpr (Or.inl ?_)⟩
            simpa using h.two δ₁ hδ₁D s hsD hδ₁I hsI
        · by_cases hsI : t⁻¹ * s ∈ I
          · exact ⟨0, by simpa using hsP, (mem_comap_zpowers httI).mpr (Or.inr (by simpa))⟩
          · refine ⟨1, by simpa using P.mul_mem (P.inv_mem hδ₁P) hsP,
              (mem_comap_zpowers httI).mpr (Or.inr ?_)⟩
            have h1 := h.two δ₁ hδ₁D _ hsD hδ₁I hsI
            have hc : (QuotientGroup.mk δ₁ : A ⧸ I) = QuotientGroup.mk (t⁻¹ * s) :=
              QuotientGroup.eq.mpr h1
            refine QuotientGroup.eq.mp ?_
            rw [zpow_one, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hc, QuotientGroup.mk_mul,
              QuotientGroup.mk_inv, mul_inv_rev, inv_inv, h.quot_comm (QuotientGroup.mk s)⁻¹,
              mul_assoc, inv_mul_cancel, mul_one]
    ·
      push Not at hPD'
      by_cases hgt : ∃ x : A, x * x = 1 ∧ t⁻¹ * x ∈ I
      · refine ⟨P ⊓ I, isU4Complement_inf hs₁P (fun s hs => ?_) fun _ =>
          hinvol t (hPC htP) htI hgt⟩
        obtain ⟨k, hk⟩ := hs₁ s hs
        have hkP : (s₁ ^ k)⁻¹ * s ∈ P := P.mul_mem (P.inv_mem (zpow_mem hs₁P k)) hs
        exact ⟨k, hkP, hPD' _ hkP hk⟩
      ·
        have he1 : e = 1 := by
          by_contra he1
          exact hgt (hsq (by omega))
        have hPV : ∀ s ∈ P, s ∈ P ⊓ (zpowers (QuotientGroup.mk t : A ⧸ I)).comap
            (QuotientGroup.mk' I) := by
          intro s hs
          refine ⟨hs, (mem_comap_zpowers httI).mpr ?_⟩
          rcases hP1 he1 s hs with hsD | hsD
          · exact Or.inl (hPD' s hs hsD)
          · exact Or.inr (hPD' _ (P.mul_mem (P.inv_mem htP) hs) hsD)
        refine ⟨_, h.isU4Complement_coset httI hgt (one_mem P)
          (fun s hs => ⟨0, by simpa using hPV s hs⟩) fun ⟨s, hs, hsV⟩ => absurd (hPV s hs) hsV⟩

end Out

end CFSG.ComponentClassification.HarrisLit.T1
