module

public import CFSG.GH74.Uniqueness.SU.SU9Orbit
public import CFSG.GH74.Uniqueness.SU.SU7Tr
public import CFSG.GH74.Uniqueness.SU.SU4Conj
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Fusion

public section

namespace CFSG.GH74.Uniqueness.SU.SU9

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG.GH74.Uniqueness.SU.SU7
  CFSG.GH74.GLS.Bg.TwoGroups CFSG

namespace L34Syl

theorem comm_central : ∀ g h : L34Syl,
    (g * h * g⁻¹ * h⁻¹).a = 0 ∧ (g * h * g⁻¹ * h⁻¹).b = 0 := by decide +kernel

end L34Syl

section Model

variable {G : Type*} [Group G]

theorem comm_mem_Zc {T : Subgroup G} (hT : IsL34Type T) :
    ∀ t ∈ T, ∀ t' ∈ T, t * t' * t⁻¹ * t'⁻¹ ∈ Zc T := by
  obtain ⟨f, hf, hr⟩ := isL34Type_iff_emb.1 hT
  rintro t ht t' ht'
  rw [← hr] at ht ht'
  obtain ⟨g, rfl⟩ := ht
  obtain ⟨g', rfl⟩ := ht'
  have h1 : (g * g' * g⁻¹ * g'⁻¹ : L34Syl) ∈ Zc (⊤ : Subgroup L34Syl) := by
    rw [L34Syl.Zc_top, L34Syl.mem_U]
    exact L34Syl.comm_central g g'
  have h2 := Subgroup.mem_map_of_mem f h1
  have h3 : Zc ((⊤ : Subgroup L34Syl).map f) = (Zc (⊤ : Subgroup L34Syl)).map f := Zc_map hf ⊤
  rw [Subgroup.map_top, hr] at h3
  rw [h3]
  simpa [map_mul, map_inv] using h2

end Model

namespace Cfg

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}
  {A B R : Subgroup G}

omit [Finite G] in
theorem orderOf_conj' (g y : G) : orderOf (g * y * g⁻¹) = orderOf y := by
  have := MulEquiv.orderOf_eq (MulAut.conj g) y
  simpa using this

omit [Finite G] in
theorem mem_normalizer_of_conjSub_eq {g : G} {E : Subgroup G} (h : conjSub g E = E) :
    g ∈ normalizer (E : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : g * y * g⁻¹ ∈ conjSub g E := by
      rw [mem_conjSub]
      have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rw [e]; exact hy
    rwa [h] at this
  · intro hy
    rw [← h, mem_conjSub] at hy
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rwa [e] at hy

theorem j2 (hc : Ctx19 S U M V x z A B R) : J2Facts (S : Subgroup G) (Tsub S U) x z :=
  Base.j2facts hc.hyp hc.conf hc.concl

theorem zc_eq (hc : Ctx19 S U M V x z A B R) : Zc (Tsub S U) = U :=
  Base.Zc_eq_U hc.hyp hc.conf hc.concl

omit [Finite G] in
theorem T_le_S : Tsub S U ≤ (S : Subgroup G) := Base.T_le_S

theorem x_mem (hc : Ctx19 S U M V x z A B R) : x ∈ (S : Subgroup G) := Base.x_mem_S hc.conf

theorem x_sq (hc : Ctx19 S U M V x z A B R) : x * x = 1 := Base.x_mul_self hc.conf

theorem z_sq (hc : Ctx19 S U M V x z A B R) : z * z = 1 := Base.z_mul_self hc.conf

theorem z_mem_S (hc : Ctx19 S U M V x z A B R) : z ∈ (S : Subgroup G) := Base.z_mem_S hc.conf

theorem z_ne_one (hc : Ctx19 S U M V x z A B R) : z ≠ 1 := Base.z_ne_one hc.conf

theorem x_comm_z (hc : Ctx19 S U M V x z A B R) : x * z * x⁻¹ = z := by
  rw [hc.conf.z_center x (x_mem hc)]; group

theorem S_le_M (hc : Ctx19 S U M V x z A B R) : (S : Subgroup G) ≤ M := hc.conf.S_le

theorem U_le_A (hc : Ctx19 S U M V x z A B R) : U ≤ A := by
  rw [← hc.c19.AB_inf]; exact inf_le_left

theorem U_le_B (hc : Ctx19 S U M V x z A B R) : U ≤ B := by
  rw [← hc.c19.AB_inf]; exact inf_le_right

theorem A_le_S (hc : Ctx19 S U M V x z A B R) : A ≤ (S : Subgroup G) :=
  hc.c19.A_le.trans T_le_S

theorem isE_A (hc : Ctx19 S U M V x z A B R) : IsE 4 A :=
  ⟨hc.c19.isE16_A.1, by rw [hc.c19.isE16_A.2]; norm_num⟩

theorem isE_B (hc : Ctx19 S U M V x z A B R) : IsE 4 B :=
  ⟨hc.c19.isE16_B.1, by rw [hc.c19.isE16_B.2]; norm_num⟩

theorem isE_U (hc : Ctx19 S U M V x z A B R) : IsE 2 U := Base.U_isE hc.hyp

theorem card_A (hc : Ctx19 S U M V x z A B R) : Nat.card A = 16 := hc.c19.isE16_A.2

theorem card_B (hc : Ctx19 S U M V x z A B R) : Nat.card B = 16 := hc.c19.isE16_B.2

theorem card_U (hc : Ctx19 S U M V x z A B R) : Nat.card U = 4 := by
  rw [hc.hyp.four.2.2]; norm_num

theorem card_T (hc : Ctx19 S U M V x z A B R) : Nat.card (Tsub S U) = 64 := (j2 hc).card_T

theorem A_ne_B (hc : Ctx19 S U M V x z A B R) : A ≠ B := by
  intro h
  have h1 := hc.c19.AB_inf
  rw [h, inf_idem] at h1
  have h2 := card_B hc
  rw [h1, card_U hc] at h2
  omega

theorem A_comm (hc : Ctx19 S U M V x z A B R) : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
  (isElemAbelian_iff.1 (isE_A hc).1).1

theorem A_sq (hc : Ctx19 S U M V x z A B R) : ∀ a ∈ A, a * a = 1 := fun a ha => by
  rw [← pow_two]; exact (isElemAbelian_iff.1 (isE_A hc).1).2 a ha

theorem B_sq (hc : Ctx19 S U M V x z A B R) : ∀ a ∈ B, a * a = 1 := fun a ha => by
  rw [← pow_two]; exact (isElemAbelian_iff.1 (isE_B hc).1).2 a ha

theorem U_comm (hc : Ctx19 S U M V x z A B R) : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a :=
  (isElemAbelian_iff.1 (isE_U hc).1).1

theorem U_sq (hc : Ctx19 S U M V x z A B R) : ∀ a ∈ U, a * a = 1 := fun a ha => by
  rw [← pow_two]; exact (isElemAbelian_iff.1 (isE_U hc).1).2 a ha

theorem U_central (hc : Ctx19 S U M V x z A B R) :
    ∀ u ∈ U, ∀ t ∈ Tsub S U, u * t = t * u := by
  intro u hu t ht
  have : u ∈ Zc (Tsub S U) := by rw [zc_eq hc]; exact hu
  exact (mem_Zc.1 this).2 t ht

theorem T_comm (hc : Ctx19 S U M V x z A B R) :
    ∀ t ∈ Tsub S U, ∀ t' ∈ Tsub S U, t * t' * t⁻¹ * t'⁻¹ ∈ U := by
  intro t ht t' ht'
  have := comm_mem_Zc hc.concl.typeT t ht t' ht'
  rwa [zc_eq hc] at this

theorem A_normal_T (hc : Ctx19 S U M V x z A B R) :
    ∀ t ∈ Tsub S U, ∀ a ∈ A, t * a * t⁻¹ ∈ A := by
  intro t ht a ha
  have h1 := T_comm hc t ht a (hc.c19.A_le ha)
  have : t * a * t⁻¹ = (t * a * t⁻¹ * a⁻¹) * a := by group
  rw [this]
  exact A.mul_mem (U_le_A hc h1) ha

theorem B_normal_T (hc : Ctx19 S U M V x z A B R) :
    ∀ t ∈ Tsub S U, ∀ a ∈ B, t * a * t⁻¹ ∈ B := by
  intro t ht a ha
  have h1 := T_comm hc t ht a (hc.c19.B_le ha)
  have : t * a * t⁻¹ = (t * a * t⁻¹ * a⁻¹) * a := by group
  rw [this]
  exact B.mul_mem (U_le_B hc h1) ha

theorem unique_E16 (hc : Ctx19 S U M V x z A B R) {E : Subgroup G} (hE : E ≤ Tsub S U)
    (hE16 : IsE 4 E) : E = A ∨ E = B := by
  have hEc := isElemAbelian_iff.1 hE16.1
  have h : ∀ e ∈ E, e ∈ A ∨ e ∈ B := by
    intro e he
    by_cases h1 : e = 1
    · left; rw [h1]; exact A.one_mem
    · apply hc.c19.invol e (hE he)
      have h2 : e ^ 2 = 1 := hEc.2 e he
      exact orderOf_eq_prime h2 h1
  rcases le_or_le_of_subset_union h with h1 | h1
  · left
    exact Subgroup.eq_of_le_of_card_ge h1 (by rw [hE16.2, card_A hc]; norm_num)
  · right
    exact Subgroup.eq_of_le_of_card_ge h1 (by rw [hE16.2, card_B hc]; norm_num)

theorem conjSub_x_B (hc : Ctx19 S U M V x z A B R) : conjSub x B = A := by
  rw [← hc.c19.B_eq, ← conjSub_mul, x_sq hc, conjSub_one]

theorem conjSub_A_of_mem_T (hc : Ctx19 S U M V x z A B R) {s : G} (hs : s ∈ Tsub S U) :
    conjSub s A = A := by
  ext y
  rw [mem_conjSub]
  constructor
  · intro h
    have := A_normal_T hc s hs _ h
    simpa [mul_assoc] using this
  · intro h
    exact A_normal_T hc s⁻¹ ((Tsub S U).inv_mem hs) y h |> fun h' => by simpa [mul_assoc] using h'

theorem conjSub_B_of_mem_T (hc : Ctx19 S U M V x z A B R) {s : G} (hs : s ∈ Tsub S U) :
    conjSub s B = B := by
  ext y
  rw [mem_conjSub]
  constructor
  · intro h
    have := B_normal_T hc s hs _ h
    simpa [mul_assoc] using this
  · intro h
    exact B_normal_T hc s⁻¹ ((Tsub S U).inv_mem hs) y h |> fun h' => by simpa [mul_assoc] using h'

theorem exists_eq_x_mul (hc : Ctx19 S U M V x z A B R) {s : G} (hs : s ∈ (S : Subgroup G))
    (hsT : s ∉ Tsub S U) : ∃ t ∈ Tsub S U, s = x * t := by
  rcases (j2 hc).S_cover s hs with h | h
  · exact absurd h hsT
  · refine ⟨x * s, h, ?_⟩
    rw [← mul_assoc, x_sq hc, one_mul]

theorem conjSub_A_of_not_T (hc : Ctx19 S U M V x z A B R) {s : G} (hs : s ∈ (S : Subgroup G))
    (hsT : s ∉ Tsub S U) : conjSub s A = B := by
  obtain ⟨t, ht, rfl⟩ := exists_eq_x_mul hc hs hsT
  rw [conjSub_mul, conjSub_A_of_mem_T hc ht, hc.c19.B_eq]

theorem conjSub_B_of_not_T (hc : Ctx19 S U M V x z A B R) {s : G} (hs : s ∈ (S : Subgroup G))
    (hsT : s ∉ Tsub S U) : conjSub s B = A := by
  obtain ⟨t, ht, rfl⟩ := exists_eq_x_mul hc hs hsT
  rw [conjSub_mul, conjSub_B_of_mem_T hc ht, conjSub_x_B hc]

theorem S_normalizes_U (hc : Ctx19 S U M V x z A B R) :
    ∀ s ∈ (S : Subgroup G), ∀ u ∈ U, s * u * s⁻¹ ∈ U := Base.U_norm hc.hyp

theorem T_normal_M (hc : Ctx19 S U M V x z A B R) (hN : ((Tsub S U).subgroupOf M).Normal) :
    ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U := by
  intro m hm t ht
  have hTM : Tsub S U ≤ M := T_le_S.trans (S_le_M hc)
  exact hN.conj_mem ⟨t, hTM ht⟩ ht ⟨m, hm⟩

theorem U_normal_M (hc : Ctx19 S U M V x z A B R)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U) :
    ∀ m ∈ M, ∀ u ∈ U, m * u * m⁻¹ ∈ U := by
  intro m hm u hu
  have hmN : m ∈ normalizer ((Tsub S U : Subgroup G) : Set G) :=
    Gen.mem_normalizer_of_conj_le (hTM' m hm)
  have := Base.mem_Zc_of_normalizer hmN (show u ∈ Zc (Tsub S U) by rw [zc_eq hc]; exact hu)
  rwa [zc_eq hc] at this

theorem exists_three_fpf (hc : Ctx19 S U M V x z A B R) (h194M : pPrimeCore 2 ↥M = ⊥) :
    ∃ n : G, n ∈ M ∧ n ∈ normalizer ((Tsub S U : Subgroup G) : Set G) ∧ n ^ 3 = 1 ∧
      ∀ t ∈ Tsub S U, t ≠ 1 → n * t * n⁻¹ ≠ t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Hh, H₀, hN, -, hH₀Hh, ⟨e⟩, -, -, -, hfpf, -⟩ := hc.concl.normalizerT
  have hTM : Tsub S U ≤ M := T_le_S.trans (S_le_M hc)
  have hTp : IsPGroup 2 ↥(Tsub S U) := S.isPGroup'.to_le T_le_S
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 3), orderOf σ = 3 :=
    ⟨finRotate 3, orderOf_eq_prime (by decide) (by decide)⟩
  set a₀ : ↥H₀ := e.symm σ with ha₀
  have hord : orderOf (a₀ : Mbar M) = 3 := by
    rw [Subgroup.orderOf_coe, ha₀, MulEquiv.orderOf_eq e.symm σ, hσ]
  have hmem : (a₀ : Mbar M) ∈ normalizer
      ((barImage M (Tsub S U) : Subgroup (Mbar M)) : Set (Mbar M)) := by
    have h1 : (a₀ : Mbar M) ∈ barImage M (Tsub S U) ⊔ Hh := mem_sup_right (hH₀Hh a₀.2)
    rw [← hN] at h1
    exact h1
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (a₀ : Mbar M)
  have hg' : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨(g : G), g.2⟩ ∈ normalizer
      ((barImage M (Tsub S U) : Subgroup (Mbar M)) : Set (Mbar M)) := by
    have : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨(g : G), g.2⟩ = (a₀ : Mbar M) := hg
    rw [this]; exact hmem
  obtain ⟨n, hnM, hnN, hnā⟩ := Bar.normalizer_lift hTp hTM g.2 hg'
  have hna : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨n, hnM⟩ = (a₀ : Mbar M) := by
    rw [hnā]; exact hg
  refine ⟨n, hnM, hnN, ?_, ?_⟩
  · have h3 : (a₀ : Mbar M) ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
    have h4 : QuotientGroup.mk' (pPrimeCore 2 ↥M) ((⟨n, hnM⟩ : ↥M) ^ 3) = 1 := by
      rw [map_pow, hna, h3]
    have h5 : (⟨n, hnM⟩ : ↥M) ^ 3 ∈ pPrimeCore 2 ↥M := (QuotientGroup.eq_one_iff _).1 h4
    rw [h194M, Subgroup.mem_bot] at h5
    exact congrArg Subtype.val h5
  · intro t ht ht1 hfix
    have htM : t ∈ M := hTM ht
    have hconj : (⟨n, hnM⟩ : ↥M) * ⟨t, htM⟩ * (⟨n, hnM⟩ : ↥M)⁻¹ = ⟨t, htM⟩ :=
      Subtype.ext (by simpa using hfix)
    have hbar : (a₀ : Mbar M) * QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩ * (a₀ : Mbar M)⁻¹ =
        QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩ := by
      rw [← hna, ← map_inv, ← map_mul, ← map_mul, hconj]
    have htP : (⟨t, htM⟩ : ↥M) ∈ (Tsub S U).subgroupOf M := ht
    have hpbar : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩ ∈ barImage M (Tsub S U) :=
      Subgroup.mem_map_of_mem _ htP
    have h1 := hfpf (a₀ : Mbar M) a₀.2 hord _ hpbar hbar
    have h2 : (⟨t, htM⟩ : ↥M) ∈ pPrimeCore 2 ↥M := (QuotientGroup.eq_one_iff _).1 h1
    rw [h194M, Subgroup.mem_bot] at h2
    exact ht1 (congrArg Subtype.val h2)

theorem conjSub_A_of_normalizer (hc : Ctx19 S U M V x z A B R) {n : G}
    (hnN : n ∈ normalizer ((Tsub S U : Subgroup G) : Set G)) (hn3 : n ^ 3 = 1) :
    conjSub n A = A := by
  have e3 : n * n * n = 1 := by simpa [pow_succ, mul_assoc] using hn3
  have hle : ∀ E : Subgroup G, E ≤ Tsub S U → conjSub n E ≤ Tsub S U := by
    intro E hE y hy
    rw [mem_conjSub] at hy
    have h1 : n⁻¹ * y * n ∈ Tsub S U := hE hy
    have := (mem_normalizer_iff.1 hnN _).1 h1
    simpa [mul_assoc] using this
  have hEA : IsE 4 (conjSub n A) :=
    ⟨isElemAbelian_conjSub (isE_A hc).1, by rw [card_conjSub, card_A hc]; norm_num⟩
  have hEB : IsE 4 (conjSub n B) :=
    ⟨isElemAbelian_conjSub (isE_B hc).1, by rw [card_conjSub, card_B hc]; norm_num⟩
  rcases unique_E16 hc (hle A hc.c19.A_le) hEA with hA | hB
  · exact hA
  · exfalso
    rcases unique_E16 hc (hle B hc.c19.B_le) hEB with hA' | hB'
    · have e1 : conjSub (n * n * n) A = B := by
        rw [conjSub_mul, conjSub_mul, hB, hA', hB]
      rw [e3, conjSub_one] at e1
      exact A_ne_B hc e1
    · exact A_ne_B hc (conjSub_injective n (hB.trans hB'.symm))

theorem orbitData (hc : Ctx19 S U M V x z A B R) {n : G}
    (hnN : n ∈ normalizer ((Tsub S U : Subgroup G) : Set G)) (hn3 : n ^ 3 = 1)
    (hfpf : ∀ t ∈ Tsub S U, t ≠ 1 → n * t * n⁻¹ ≠ t) : OrbitData (Tsub S U) A U n where
  card_T := card_T hc
  card_A := card_A hc
  card_U := card_U hc
  U_le_A := U_le_A hc
  A_le_T := hc.c19.A_le
  A_comm := A_comm hc
  A_sq := A_sq hc
  U_central := U_central hc
  T_comm := T_comm hc
  cent_A := hc.c19.centA
  n_U := fun u hu => by
    have := Base.mem_Zc_of_normalizer hnN (show u ∈ Zc (Tsub S U) by rw [zc_eq hc]; exact hu)
    rwa [zc_eq hc] at this
  n_A := fun a ha => by
    have : n * a * n⁻¹ ∈ conjSub n A := by
      rw [mem_conjSub]
      have e : n⁻¹ * (n * a * n⁻¹) * n = a := by group
      rw [e]; exact ha
    rwa [conjSub_A_of_normalizer hc hnN hn3] at this
  n_cube := hn3
  n_fpf := hfpf

theorem exists_M_conj_A (hc : Ctx19 S U M V x z A B R) (h194M : pPrimeCore 2 ↥M = ⊥) {a a' : G}
    (ha : a ∈ A) (haU : a ∉ U) (ha' : a' ∈ A) (ha'U : a' ∉ U) : ∃ m ∈ M, m * a * m⁻¹ = a' := by
  obtain ⟨n, hnM, hnN, hn3, hfpf⟩ := exists_three_fpf hc h194M
  have hO := orbitData hc hnN hn3 hfpf
  obtain ⟨t, ht, k, hk⟩ := hO.exists_conj a ha haU a' ha' ha'U
  have hTM : Tsub S U ≤ M := T_le_S.trans (S_le_M hc)
  exact ⟨t * n ^ k, M.mul_mem (hTM ht) (M.pow_mem hnM k), hk⟩

theorem exists_M_conj (hc : Ctx19 S U M V x z A B R) (h194M : pPrimeCore 2 ↥M = ⊥) {a b : G}
    (ha : a ∈ A) (haU : a ∉ U) (hbT : b ∈ Tsub S U) (hbU : b ∉ U) (hb2 : b * b = 1) :
    ∃ m ∈ M, m * a * m⁻¹ = b := by
  have hb1 : b ≠ 1 := fun h => hbU (h ▸ U.one_mem)
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hb2) hb1
  rcases hc.c19.invol b hbT hbo with hbA | hbB
  · exact exists_M_conj_A hc h194M ha haU hbA hbU
  · have hb' : x⁻¹ * b * x ∈ A := by
      have : b ∈ conjSub x A := by rw [hc.c19.B_eq]; exact hbB
      exact mem_conjSub.1 this
    have hb'U : x⁻¹ * b * x ∉ U := by
      intro hU
      apply hbU
      have h1 := S_normalizes_U hc x (x_mem hc) _ hU
      have : x * (x⁻¹ * b * x) * x⁻¹ = b := by group
      rwa [this] at h1
    obtain ⟨m, hm, hma⟩ := exists_M_conj_A hc h194M ha haU hb' hb'U
    refine ⟨x * m, M.mul_mem (S_le_M hc (x_mem hc)) hm, ?_⟩
    calc x * m * a * (x * m)⁻¹ = x * (m * a * m⁻¹) * x⁻¹ := by group
      _ = b := by rw [hma]; group

theorem isConj_z_of_mem_U (hc : Ctx19 S U M V x z A B R) {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) :
    IsConj z u := by
  obtain ⟨h, -, hh⟩ := Tr.exists_conj_z hc.hyp hc.conf hc.concl hu hu1
  exact isConj_iff.2 ⟨h, hh⟩

theorem exists_mem_U_ne (hc : Ctx19 S U M V x z A B R) : ∃ u ∈ U, u ≠ 1 ∧ u ≠ z := by
  obtain ⟨t₁, ht₁, ht₁1, t₂, ht₂, ht₂1, ht₂₁⟩ := Gen.exists_two_ne_one_of_card_four (card_U hc)
  by_cases h : t₁ = z
  · exact ⟨t₂, ht₂, ht₂1, by rw [h] at ht₂₁; exact ht₂₁⟩
  · exact ⟨t₁, ht₁, ht₁1, h⟩

theorem isConj_z_of_not_T (h191 : Lemma191Stmt) (hc : Ctx19 S U M V x z A B R) {s : G}
    (hs : s ∈ (S : Subgroup G)) (hsT : s ∉ Tsub S U) (hs2 : orderOf s = 2) : IsConj z s := by
  obtain ⟨u, hu, hu1, huz⟩ := exists_mem_U_ne hc
  obtain ⟨g, -, hgs⟩ := h191 G S U M V x z A B R hc s hs hsT hs2 u hu hu1 huz
  have h1 : IsConj u s := isConj_iff.2 ⟨g, by rw [← hgs]; group⟩
  exact (isConj_z_of_mem_U hc hu hu1).trans h1

theorem exists_conj_into_S (hc : Ctx19 S U M V x z A B R) {E : Subgroup G} (hE : IsPGroup 2 E)
    {a : G} (hcomm : ∀ e ∈ E, e * a = a * e) (hza : IsConj z a) :
    ∃ g' : G, g' * a * g'⁻¹ = z ∧ ∀ e ∈ E, g' * e * g'⁻¹ ∈ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := isConj_iff.1 hza
  have hSC : (S : Subgroup G) ≤ centralizer ({z} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.2 (hc.conf.z_center s hs)
  have hE' : IsPGroup 2 (conjSub g⁻¹ E) := isPGroup_conjSub hE
  have hEC : conjSub g⁻¹ E ≤ centralizer ({z} : Set G) := by
    intro y hy
    rw [mem_conjSub] at hy
    rw [mem_centralizer_singleton_iff]
    have h1 := hcomm _ hy
    have h2 : (g⁻¹)⁻¹ * y * g⁻¹ = g * y * g⁻¹ := by simp
    have : z = g⁻¹ * a * g := by rw [← hg]; group
    rw [this]
    have h3 : (g * y * g⁻¹) * a = a * (g * y * g⁻¹) := by rw [h2] at h1; exact h1
    calc y * (g⁻¹ * a * g) = g⁻¹ * ((g * y * g⁻¹) * a) * g := by group
      _ = g⁻¹ * (a * (g * y * g⁻¹)) * g := by rw [h3]
      _ = (g⁻¹ * a * g) * y := by group
  obtain ⟨c, hcC, hc'⟩ := CFSG.LyonsUnitaryFour.exists_conj_le_sylow_of_le (P := S) hSC hEC hE'
  have hcz : c * z = z * c := mem_centralizer_singleton_iff.1 hcC
  refine ⟨c * g⁻¹, ?_, ?_⟩
  · calc c * g⁻¹ * a * (c * g⁻¹)⁻¹ = c * (g⁻¹ * (g * z * g⁻¹) * g) * c⁻¹ := by rw [hg]; group
      _ = c * z * c⁻¹ := by group
      _ = z := by rw [hcz]; group
  · intro e he
    have h1 : g⁻¹ * e * g ∈ conjSub g⁻¹ E := by
      rw [mem_conjSub]
      have e' : (g⁻¹)⁻¹ * (g⁻¹ * e * g) * g⁻¹ = e := by group
      rw [e']; exact he
    have e1 : c * g⁻¹ * e * (c * g⁻¹)⁻¹ = c * (g⁻¹ * e * g) * c⁻¹ := by group
    rw [e1]
    exact hc' _ h1

end Cfg

end CFSG.GH74.Uniqueness.SU.SU9
