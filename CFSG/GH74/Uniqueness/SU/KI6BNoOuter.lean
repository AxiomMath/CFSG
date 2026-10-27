module

public import CFSG.GH74.Uniqueness.SU.KI6BFacts
public import CFSG.GH74.GLS.IVK.L2.KI2Aux
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Outer
public import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6.NoOuter

open Subgroup CFSG.GH74.GLS.IVK

theorem exists_two_ne_one {A : Type*} [Group A] (U : Subgroup A) (hU : Nat.card U = 4) :
    ∃ a ∈ U, ∃ b ∈ U, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have hfin : Finite U := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype U := Fintype.ofFinite U
  have h3 : 2 < Fintype.card U := by rw [← Nat.card_eq_fintype_card, hU]; norm_num
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.1 h3
  by_cases hx : (x : A) = 1
  · refine ⟨y, y.2, z, z.2, ?_, ?_, ?_⟩
    · intro h
      exact hxy (Subtype.ext (hx.trans h.symm))
    · intro h
      exact hxz (Subtype.ext (hx.trans h.symm))
    · intro h
      exact hyz (Subtype.ext h)
  · by_cases hy : (y : A) = 1
    · refine ⟨x, x.2, z, z.2, hx, ?_, ?_⟩
      · intro h
        exact hyz (Subtype.ext (hy.trans h.symm))
      · intro h
        exact hxz (Subtype.ext h)
    · refine ⟨x, x.2, y, y.2, hx, hy, ?_⟩
      intro h
      exact hxy (Subtype.ext h)

theorem comm_of_sq_eq_one {A : Type*} [Group A] {a b : A} (ha : a * a = 1) (hb : b * b = 1)
    (hab : (a * b) * (a * b) = 1) : a * b = b * a := by
  have h1 : a = a⁻¹ := mul_eq_one_iff_eq_inv.1 ha
  have h2 : b = b⁻¹ := mul_eq_one_iff_eq_inv.1 hb
  have h3 : a * b = (a * b)⁻¹ := mul_eq_one_iff_eq_inv.1 hab
  rw [h3, mul_inv_rev, ← h1, ← h2]

theorem mul_ne_one_of_ne {A : Type*} [Group A] {a b : A} (hb : b * b = 1) (hab : a ≠ b) :
    a * b ≠ 1 := by
  intro h
  apply hab
  have h2 : b = b⁻¹ := mul_eq_one_iff_eq_inv.1 hb
  rw [mul_eq_one_iff_eq_inv] at h
  rw [h, ← h2]

theorem mul_mem_of_index_dvd_two {G : Type*} [Group G] (N : Subgroup G) (h : N.index ∣ 2)
    {x y : G} (hx : x ∉ N) (hy : y ∉ N) : x * y ∈ N := by
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
  · exact absurd ((Subgroup.index_eq_one.1 h1) ▸ Subgroup.mem_top x) hx
  · exact (Subgroup.mul_mem_iff_of_index_two h2).2 (iff_of_false hx hy)

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem exists_inner_of_alt7 {L : Type} [Group L] (e : L ≃* alternatingGroup (Fin 7))
    {A : Type*} [Group A] (ρ : A →* MulAut L) (U : Subgroup A) (hU : Nat.card U = 4)
    (hsq : ∀ u ∈ U, u * u = 1) :
    ∃ u ∈ U, u ≠ 1 ∧ ρ u ∈ (MulAut.conj : L →* MulAut L).range := by
  by_contra hno'
  have hno : ∀ u ∈ U, u ≠ 1 → ρ u ∉ (MulAut.conj : L →* MulAut L).range :=
    fun u hu hu1 hmem => hno' ⟨u, hu, hu1, hmem⟩
  obtain ⟨a, haU, b, hbU, ha1, hb1, hab⟩ := exists_two_ne_one U hU
  have hiff : ∀ x : MulAut L,
      x ∈ inner L ↔ MulAut.congr e x ∈ inner (alternatingGroup (Fin 7)) := by
    intro x
    rw [← inner_map_congr e]
    exact (Subgroup.mem_map_iff_mem (MulAut.congr e).injective).symm
  have hidx := CFSG.Quasithin.SteinbergCB.index_inner_dvd_two (n := 7) (Or.inr le_rfl)
  have hmem : MulAut.congr e (ρ (a * b)) ∈ inner (alternatingGroup (Fin 7)) := by
    rw [map_mul, map_mul]
    exact mul_mem_of_index_dvd_two _ hidx (fun h => hno a haU ha1 ((hiff _).2 h))
      (fun h => hno b hbU hb1 ((hiff _).2 h))
  exact hno (a * b) (U.mul_mem haU hbU) (mul_ne_one_of_ne (hsq b hbU) hab) ((hiff _).2 hmem)

theorem mul_mem_innAut_of_not_mem {F : Type} [Field F] [Finite F] {K : Type} [Group K]
    (e : K ≃* L2 F) (hF : L2Field F) {x y : MulAut K} (hx : x ∈ innDiagSub e)
    (hy : y ∈ innDiagSub e) (hxn : x ∉ innAut K) (hyn : y ∉ innAut K) : x * y ∈ innAut K := by
  obtain ⟨X, rfl⟩ := hx
  obtain ⟨Y, rfl⟩ := hy
  rw [← map_mul, innDiagHom_mem_innAut_iff]
  rw [innDiagHom_mem_innAut_iff] at hxn hyn
  exact (Subgroup.mul_mem_iff_of_index_two
    (CFSG.GorensteinWalter.pgl2_psl2Range_index_eq_two F (isOddPrimePower_of_L2Field hF))).2
    (iff_of_false hxn hyn)

theorem exists_ne_one_fieldProj_eq_one {F : Type} [Field F] [Finite F] {K : Type} [Group K]
    (e : K ≃* L2 F) {A : Type*} [Group A] (ρ : A →* MulAut K) (U : Subgroup A)
    (hU : Nat.card U = 4) (hsq : ∀ u ∈ U, u * u = 1) :
    ∃ x ∈ U, x ≠ 1 ∧ fieldProj e (ρ x) = 1 := by
  let φ : U →* (F ≃+* F) := ((fieldProj e).comp ρ).comp U.subtype
  have hφsq : ∀ x : U, φ x ^ 2 = 1 := by
    intro x
    show fieldProj e (ρ (x : A)) ^ 2 = 1
    rw [← map_pow, ← map_pow, pow_two, hsq x x.2, map_one, map_one]
  have hrange : Nat.card φ.range ≤ 2 := by
    have := ringAut_isCyclic F
    have : IsCyclic φ.range := Subgroup.isCyclic _
    have h1 : Monoid.exponent φ.range ∣ 2 := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      rintro ⟨_, x, rfl⟩
      apply Subtype.ext
      exact hφsq x
    rw [IsCyclic.exponent_eq_card] at h1
    exact Nat.le_of_dvd (by norm_num) h1
  have hprod := Subgroup.card_ker_mul_card_range φ
  rw [hU] at hprod
  have hker : 2 ≤ Nat.card φ.ker := by
    have := Nat.mul_le_mul_left (Nat.card φ.ker) hrange
    omega
  have hne : φ.ker ≠ ⊥ := fun h => by
    rw [Subgroup.eq_bot_iff_card] at h
    omega
  obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  refine ⟨(y : U), (y : U).2, ?_, y.2⟩
  intro h
  exact hy (Subtype.ext (Subtype.ext h))

theorem exists_inner_of_psl2 {F : Type} [Field F] [Finite F] (hF : L2Field F) {K : Type}
    [Group K] (e : K ≃* L2 F) {A : Type*} [Group A] (ρ : A →* MulAut K) (U : Subgroup A)
    (hU : Nat.card U = 4) (hsq : ∀ u ∈ U, u * u = 1) :
    ∃ u ∈ U, u ≠ 1 ∧ ρ u ∈ innAut K := by
  by_contra hno'
  have hno : ∀ u ∈ U, u ≠ 1 → ρ u ∉ innAut K :=
    fun u hu hu1 hmem => hno' ⟨u, hu, hu1, hmem⟩
  obtain ⟨a, haU, b, hbU, ha1, hb1, hab⟩ := exists_two_ne_one U hU
  have hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    comm_of_sq_eq_one (hsq x hx) (hsq y hy) (hsq _ (U.mul_mem hx hy))
  have hρsq : ∀ x ∈ U, ρ x * ρ x = 1 := fun x hx => by rw [← map_mul, hsq x hx, map_one]
  by_cases hD : ∀ u ∈ U, fieldProj e (ρ u) = 1
  ·
    have hmem : ρ (a * b) ∈ innAut K := by
      rw [map_mul]
      exact mul_mem_innAut_of_not_mem e hF ((mem_innDiagSub_iff e _).2 (hD a haU))
        ((mem_innDiagSub_iff e _).2 (hD b hbU)) (hno a haU ha1) (hno b hbU hb1)
    exact hno (a * b) (U.mul_mem haU hbU) (mul_ne_one_of_ne (hsq b hbU) hab) hmem
  ·
    obtain ⟨b₀, hb₀U, hb₀⟩ : ∃ b₀ ∈ U, fieldProj e (ρ b₀) ≠ 1 := by
      by_contra hcon
      exact hD fun u hu => by
        by_contra h
        exact hcon ⟨u, hu, h⟩
    obtain ⟨a₀, ha₀U, ha₀1, ha₀f⟩ := exists_ne_one_fieldProj_eq_one e ρ U hU hsq
    have hρb : orderOf (ρ b₀) = 2 := by
      refine orderOf_eq_prime (by rw [pow_two]; exact hρsq b₀ hb₀U) ?_
      intro h
      apply hb₀
      rw [h, map_one]
    have hnD : ρ b₀ ∉ innDiagSub e := fun h => hb₀ ((mem_innDiagSub_iff e _).1 h)
    obtain ⟨c, hcD, hc⟩ := exists_conj_fieldAut e (ρ b₀) hρb hnD
    obtain ⟨σ, hσ⟩ : ∃ σ : F ≃+* F, σ = fieldProj e (ρ b₀) := ⟨_, rfl⟩
    rw [← hσ] at hc
    have hσ2 : σ ^ 2 = 1 := by rw [hσ, ← map_pow, pow_two, hρsq b₀ hb₀U, map_one]
    have hσ1 : σ ≠ 1 := fun h => hb₀ (hσ ▸ h)
    have hσord : orderOf σ = 2 := orderOf_eq_prime hσ2 hσ1
    have hρa₀D : ρ a₀ ∈ innDiagSub e := (mem_innDiagSub_iff e _).2 ha₀f
    have ha'D : c⁻¹ * ρ a₀ * c ∈ innDiagSub e :=
      (innDiagSub e).mul_mem ((innDiagSub e).mul_mem ((innDiagSub e).inv_mem hcD) hρa₀D) hcD
    have hρcomm : ρ b₀ * ρ a₀ = ρ a₀ * ρ b₀ := by
      rw [← map_mul, ← map_mul, hcomm b₀ hb₀U a₀ ha₀U]
    have ha'C : c⁻¹ * ρ a₀ * c ∈ centralizer ({fieldAutHom e σ} : Set (MulAut K)) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
      calc c⁻¹ * ρ a₀ * c * (c⁻¹ * ρ b₀ * c) = c⁻¹ * (ρ a₀ * ρ b₀) * c := by group
        _ = c⁻¹ * (ρ b₀ * ρ a₀) * c := by rw [hρcomm]
        _ = c⁻¹ * ρ b₀ * c * (c⁻¹ * ρ a₀ * c) := by group
    have ha'I : c⁻¹ * ρ a₀ * c ∈ innAut K :=
      centralizer_fieldAut_le_innAut e σ (by rw [hσord]; exact even_two) ⟨ha'C, ha'D⟩
    have hρa₀I : ρ a₀ ∈ innAut K := by
      have h3 : ρ a₀ = c * (c⁻¹ * ρ a₀ * c) * c⁻¹ := by group
      rw [h3]
      exact innAut_normal.conj_mem _ ha'I c
    exact hno a₀ ha₀U ha₀1 hρa₀I

theorem exists_inner_of_simple_dihedral
    {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (hnonab : ∃ x y : L, x * y ≠ y * x) (hL : CFSG.GorensteinWalter.HasDihedralSylowTwo L)
    {A : Type*} [Group A] (ρ : A →* MulAut L) (U : Subgroup A) (hU : Nat.card U = 4)
    (hsq : ∀ u ∈ U, u * u = 1) :
    ∃ u ∈ U, u ≠ 1 ∧ ρ u ∈ (MulAut.conj : L →* MulAut L).range := by
  have hL' : CFSG.ComponentClassification.AschbacherKnownGroup.HasDihedralSylowTwo L := by
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 L))
    obtain ⟨m, hm, ⟨d⟩⟩ := hL S
    exact ⟨S, m + 1, by omega, ⟨d⟩⟩
  rcases CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.simple_dihedral_cases
      hnonab hL' with ⟨⟨e⟩⟩ | ⟨F, _, _, p, f, hp, hcard, hodd, h3, ⟨e⟩⟩
  · exact exists_inner_of_alt7 e ρ U hU hsq
  · obtain ⟨p', n, -, hp', -, hn⟩ := hodd
    have hF : L2Field F := ⟨by rw [hn]; exact hp'.pow, h3⟩
    exact exists_inner_of_psl2 hF (e.trans (L2.equivPSL F).symm) ρ U hU hsq

open CFSG.ComponentClassification.PerfectAutomorphisms in
@[expose] noncomputable def actOnCenterQuotient {H : Type} [Group H] (K : Subgroup H)
    [K.Normal] : H →* MulAut (↥K ⧸ center ↥K) :=
  (centerQuotientHom ↥K).comp MulAut.conjNormal

section Action

variable {H : Type} [Group H] (K : Subgroup H) [K.Normal]

open CFSG.ComponentClassification.PerfectAutomorphisms in
theorem actOnCenterQuotient_apply_mk (h : H) (k : ↥K) :
    actOnCenterQuotient K h (QuotientGroup.mk k) = QuotientGroup.mk (MulAut.conjNormal h k) :=
  onCenterQuotient_apply_mk (MulAut.conjNormal h) k

theorem actOnCenterQuotient_coe (k : ↥K) :
    actOnCenterQuotient K (k : H) = MulAut.conj (QuotientGroup.mk k : ↥K ⧸ center ↥K) := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [actOnCenterQuotient_apply_mk]
  have : MulAut.conjNormal (k : H) y = k * y * k⁻¹ :=
    Subtype.ext (by simp [MulAut.conjNormal_apply])
  rw [this]
  simp [MulAut.conj_apply]

open CFSG.ComponentClassification.PerfectAutomorphisms in
theorem mem_centralizer_of_actOnCenterQuotient_eq_one [Group.IsPerfect ↥K] {h : H}
    (hh : actOnCenterQuotient K h = 1) : h ∈ centralizer (K : Set H) := by
  have h1 : MulAut.conjNormal h = (1 : MulAut ↥K) := by
    apply centerQuotientHom_injective ↥K
    rw [map_one]
    exact hh
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h2 := congrArg (fun f : MulAut ↥K => ((f ⟨k, hk⟩ : ↥K) : H)) h1
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
  calc k * h = (h * k * h⁻¹) * h := by rw [h2]
    _ = h * k := by group

end Action

end CFSG.GH74.Uniqueness.SU.K.R6.NoOuter

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup NoOuter

theorem noOuterFourGroup
    (h1 : RankOneFacts) : NoOuterFourGroup := by
  intro H _ _ K hKn hq hrank hcenter hC U hU hsq
  have : K.Normal := hKn
  have : Group.IsPerfect ↥K := hq.1
  by_contra hUK
  obtain ⟨-, -, -, -, -, hsimple, hdih⟩ := h1 ↥K hq hrank hcenter
  have : IsSimpleGroup (↥K ⧸ center ↥K) := hsimple
  obtain ⟨u, huU, hu1, hkbar⟩ := exists_inner_of_simple_dihedral hq.2.2 hdih
    (actOnCenterQuotient K) U hU hsq
  obtain ⟨kbar, hk⟩ := hkbar
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective kbar
  have hρk := actOnCenterQuotient_coe K k
  have h2 : actOnCenterQuotient K (u * (k : H)⁻¹) = 1 := by
    rw [map_mul, map_inv, hρk, ← hk]
    simp
  have h3 : u * (k : H)⁻¹ ∈ K := hC (mem_centralizer_of_actOnCenterQuotient_eq_one K h2)
  have h4 : u ∈ K := by
    have := K.mul_mem h3 k.2
    simpa using this
  have h5 : u ∈ U ⊓ K := ⟨huU, h4⟩
  rw [hUK] at h5
  exact hu1 (Subgroup.mem_bot.1 h5)

end CFSG.GH74.Uniqueness.SU.K.R6
