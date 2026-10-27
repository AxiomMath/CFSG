module

public import CFSG.GH74.Uniqueness.Section166B
public import CFSG.GH74.Uniqueness.Section166D
public import CFSG.GH74.Uniqueness.Bender.Out

public section

namespace CFSG.GH74.Uniqueness.Cor166

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem benderAut_eq_one_of_mem_centralizer {F : Subgroup X} {g : ↥(normalizer (F : Set X))}
    (hg : (g : X) ∈ centralizer (F : Set X)) : benderAut F g = 1 := by
  ext k
  induction k using QuotientGroup.induction_on with
  | H x =>
    rw [MulAut.one_apply]
    refine benderAut_mk F g x x ?_
    have := Subgroup.mem_centralizer_iff.mp hg x x.2
    calc (x : X) = (x : X) * g * (g : X)⁻¹ := by group
      _ = g * x * (g : X)⁻¹ := by rw [this]

omit [Finite X] in
theorem exists_pow_mul_self_eq {R : Subgroup X} (hR : IsPGroup 2 R) {u : X}
    (huniq : ∀ y ∈ R, orderOf y = 2 → y = u) {x : X} (hx : x ∈ R) (hxu : x ∉ zpowers u) :
    ∃ m : ℕ, x ^ m * x ^ m = u := by
  obtain ⟨k, hk⟩ := hR ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  have ha2 : 2 ≤ a := by
    by_contra hlt
    have hlt' : a < 2 := by omega
    interval_cases a
    · rw [pow_zero, orderOf_eq_one_iff] at ha
      exact hxu (ha ▸ one_mem _)
    · rw [pow_one] at ha
      exact hxu (huniq x hx ha ▸ mem_zpowers u)
  refine ⟨2 ^ (a - 2), ?_⟩
  have hsum : 2 ^ (a - 2) + 2 ^ (a - 2) = 2 ^ (a - 1) := by
    have : a - 1 = (a - 2) + 1 := by omega
    rw [this, pow_succ]
    ring
  rw [← pow_add, hsum]
  refine huniq _ (R.pow_mem hx _) ?_
  have hdvd : 2 ^ (a - 1) ∣ orderOf x := by
    rw [ha]
    exact pow_dvd_pow 2 (Nat.sub_le a 1)
  rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, ha, Nat.pow_div (Nat.sub_le a 1)
    (by norm_num)]
  have : a - (a - 1) = 1 := by omega
  rw [this, pow_one]

section Main

variable (S : ZDSetup X Z M) (c : Conf16 Z M) (h163 : Lemma163Stmt Z M) (h164 : Lemma164Stmt Z M)
  (h165 : Prop165Stmt Z M) {n i e : ℕ} (hB : BenderSub Z M c.B0 n i e)

include S c h163 h164 h165 hB in
theorem eq_of_comm_of_disjoint
    {R : Subgroup X} (hRZ : ∀ x ∈ R, x ∉ Z) :
    ∀ a ∈ R, ∀ b ∈ R, orderOf a = 2 → orderOf b = 2 → a * b = b * a → a = b := by
  intro a ha b hb ha2 hb2 hab
  by_contra hne
  have hbb : b * b = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hb2, sq] at this
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb2
    exact absurd hb2 (by norm_num)
  rcases cor166d_pair S c h163 h164 h165 hB ha2 hbb hb1 (Ne.symm hne) hab.symm with h | h | h
  · exact hRZ a ha h
  · exact hRZ b hb h
  · exact hRZ _ (R.mul_mem hb ha) h

include S c h163 h164 h165 hB in
theorem isCyclic_of_isPGroup_of_mem
    {R : Subgroup X} (hR : IsPGroup 2 R) (hRZ : ∀ x ∈ R, x ∉ Z)
    (huR : c.u ∈ R) : IsCyclic R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcommR := eq_of_comm_of_disjoint S c h163 h164 h165 hB hRZ
  have huniq : ∀ y ∈ R, orderOf y = 2 → y = c.u := fun y hy hy2 =>
    eq_of_isPGroup_of_comm hR hcommR hy huR hy2 c.hu2
  have hRB : R ≤ c.B := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (comm_of_isPGroup_of_comm hR hcommR huR c.hu2 x hx)
  have hRN : R ≤ normalizer (c.B0 : Set X) := hRB.trans (B_le_normalizer c S)
  set K := ↥c.B0 ⧸ center ↥c.B0
  have : Finite (MulAut K) := Finite.of_injective (fun f : MulAut K => (f : K → K))
    DFunLike.coe_injective
  let f : ↥R →* Outer K :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner K)).comp
      ((benderAut c.B0).comp (Subgroup.inclusion hRN))
  have hker : ∀ x : ↥R, f x = 1 → (x : X) ∈ zpowers c.u := by
    intro x hx
    by_contra hxu
    obtain ⟨m, hm⟩ := exists_pow_mul_self_eq hR huniq x.2 hxu
    have hfx : f (x ^ m) = 1 := by rw [map_pow, hx, one_pow]
    have hin : benderAut c.B0 (Subgroup.inclusion hRN (x ^ m)) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner K :=
      (QuotientGroup.eq_one_iff (benderAut c.B0 (Subgroup.inclusion hRN (x ^ m)))).mp hfx
    obtain ⟨y', hy'⟩ : ∃ y' : K, MulAut.conj y' = benderAut c.B0 (Subgroup.inclusion hRN (x ^ m)) :=
      hin
    set g4 : ↥(normalizer (c.B0 : Set X)) := Subgroup.inclusion hRN (x ^ m) with hg4
    have hg4X : (g4 : X) = (x : X) ^ m := rfl
    have hsq : MulAut.conj (y' * y') = 1 := by
      have hu : benderAut c.B0 (g4 * g4) = 1 := by
        apply benderAut_eq_one_of_mem_centralizer
        have : ((g4 * g4 : ↥(normalizer (c.B0 : Set X))) : X) = c.u := by
          rw [Subgroup.coe_mul, hg4X, hm]
        rw [this]
        exact u_mem_J c
      rw [map_mul, ← hy'] at hu
      rw [map_mul]
      exact hu
    have hy'2 : y' * y' = 1 := by
      have hcent : y' * y' ∈ center K := by
        rw [Subgroup.mem_center_iff]
        intro k
        have := congrArg (fun φ : MulAut K => φ k) hsq
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc k * (y' * y') = ((y' * y') * k * (y' * y')⁻¹) * (y' * y') := by rw [this]
          _ = (y' * y') * k := by group
      have hcb : center K = ⊥ := hB.bender.center_eq_bot
      rw [hcb, Subgroup.mem_bot] at hcent
      exact hcent
    obtain ⟨y, hy, hyy⟩ := exists_sq_eq_one_lift (benderSub_odd_card_center hB) hy'2
    rw [← hy] at hy'
    have hj := benderSub_mem_centralizer_of_eq_conj S.invariant hB hy'.symm
    set j := (y : X)⁻¹ * g4 with hjdef
    have hjB : j ∈ c.B := c.B.mul_mem (c.B.inv_mem (B0_le_B c y.2)) (hRB (R.pow_mem x.2 m))
    have hjy : j * y = y * j := (Subgroup.mem_centralizer_iff.mp hj y y.2).symm
    have hyX : (y : X) * y = 1 := congrArg Subtype.val hyy
    have hj2 : j * j = c.u := by
      have hx4 : (g4 : X) = y * j := by rw [hjdef]; group
      calc j * j = (y * y) * (j * j) := by rw [hyX, one_mul]
        _ = y * (y * j) * j := by group
        _ = y * (j * y) * j := by rw [hjy]
        _ = (y * j) * (y * j) := by group
        _ = c.u := by rw [← hx4, hg4X, hm]
    have hj4 : j ^ 2 ^ 2 = 1 := by
      have h4 : j ^ 2 ^ 2 = (j * j) * (j * j) := by
        rw [show (2 : ℕ) ^ 2 = 2 + 2 by norm_num, pow_add, sq]
      rw [h4, hj2]
      exact u_mul_self c
    have hjmem := mem_zpowers_of_mem_J_B S c h163 h164 h165 hB hj hjB hj4
    by_cases hj1 : j = 1
    · rw [hj1, one_mul] at hj2
      exact u_ne_one c hj2.symm
    · have := eq_of_mem_zpowers_of_ne_one c.hu2 hjmem hj1
      rw [this, u_mul_self c] at hj2
      exact u_ne_one c hj2.symm
  have hrange : IsCyclic f.range := by
    have hp : IsPGroup 2 f.range := by
      rintro ⟨_, x, rfl⟩
      obtain ⟨k, hk⟩ := hR x
      refine ⟨k, Subtype.ext ?_⟩
      change (f x) ^ 2 ^ k = 1
      rw [← map_pow, hk, map_one]
    obtain ⟨P₀, hP₀⟩ := hp.exists_le_sylow
    have := hB.bender.isCyclic_sylow_outer P₀
    exact isCyclic_of_le hP₀
  obtain ⟨γ, hγ⟩ := hrange.exists_generator
  obtain ⟨x₀, hx₀⟩ := γ.2
  have hall : ∀ r : ↥R, ∃ k : ℤ, ((r : X) * ((x₀ : X) ^ k)⁻¹) ∈ zpowers c.u := by
    intro r
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hγ ⟨f r, r, rfl⟩)
    refine ⟨k, ?_⟩
    have h1 : f (r * (x₀ ^ k)⁻¹) = 1 := by
      have hk' : f r = (f x₀) ^ k := by
        have h1 : ((γ ^ k : ↥f.range) : Outer K) = f r := congrArg Subtype.val hk
        rw [SubgroupClass.coe_zpow, ← hx₀] at h1
        exact h1.symm
      rw [map_mul, map_inv, map_zpow, hk', mul_inv_cancel]
    have := hker _ h1
    simpa using this
  by_cases hx₀u : (x₀ : X) ∈ zpowers c.u
  · have hle : R ≤ zpowers c.u := by
      intro r hr
      obtain ⟨k, hk⟩ := hall ⟨r, hr⟩
      have : r = (r * ((x₀ : X) ^ k)⁻¹) * (x₀ : X) ^ k := by group
      rw [this]
      exact mul_mem hk (zpow_mem hx₀u k)
    exact isCyclic_of_le hle
  · have hx₀1 : (x₀ : X) ≠ 1 := fun h => hx₀u (h ▸ one_mem _)
    obtain ⟨w, hw, hw2⟩ := exists_involution_mem_zpowers
      (hR.to_le (zpowers_le.mpr x₀.2)) hx₀1
    have hwu : w = c.u := huniq w (zpowers_le.mpr x₀.2 hw) hw2
    have hux₀ : zpowers c.u ≤ zpowers (x₀ : X) := zpowers_le.mpr (hwu ▸ hw)
    have hle : R ≤ zpowers (x₀ : X) := by
      intro r hr
      obtain ⟨k, hk⟩ := hall ⟨r, hr⟩
      have : r = (r * ((x₀ : X) ^ k)⁻¹) * (x₀ : X) ^ k := by group
      rw [this]
      exact mul_mem (hux₀ hk) (zpow_mem (mem_zpowers _) k)
    exact isCyclic_of_le hle

include S c h163 h164 h165 hB in
theorem isCyclic_of_isPGroup
    {R : Subgroup X} (hR : IsPGroup 2 R) (hRZ : ∀ x ∈ R, x ∉ Z) :
    IsCyclic R := by
  by_cases hinv : ∃ a ∈ R, orderOf a = 2
  · obtain ⟨a, haR, ha2⟩ := hinv
    have hau : IsConj c.u a := by
      rcases cor166c_invol S c h163 h164 h165 hB ha2 with h | h
      · exact absurd (S.invariant.isConj_mem c.hz h.symm) (hRZ a haR)
      · exact h
    obtain ⟨g, hg⟩ := isConj_iff.mp hau
    have hR₁ : IsPGroup 2 (conjugate R g) := isPGroup_conjugate hR g
    have hR₁Z : ∀ x ∈ conjugate R g, x ∉ Z := by
      intro x hx hxZ
      rw [mem_conjugate_iff] at hx
      refine hRZ _ hx ?_
      have := S.invariant.2 x hxZ g⁻¹
      simpa using this
    have hu₁ : c.u ∈ conjugate R g := by
      rw [mem_conjugate_iff, hg]
      exact haR
    have hcyc := isCyclic_of_isPGroup_of_mem S c h163 h164 h165 hB hR₁ hR₁Z hu₁
    have hRe : conjugate (conjugate R g) g⁻¹ = R := by
      rw [conjugate_conjugate, mul_inv_cancel, conjugate_one]
    rw [← hRe]
    exact isCyclic_of_surjective
      ((MulAut.conj g⁻¹⁻¹).toMonoidHom.subgroupMap (conjugate R g))
      (MonoidHom.subgroupMap_surjective _ _)
  · push Not at hinv
    have hbot : R = ⊥ := eq_bot_of_no_involution hR hinv
    rw [hbot]
    exact isCyclic_of_le (bot_le : (⊥ : Subgroup X) ≤ zpowers 1)

include S c h163 h164 h165 hB in
theorem cor166e
    (Y : Subgroup X) (hY : zHull Z Y = ⊥) :
    (∃ N : Subgroup X, N ≤ Y ∧ (N.subgroupOf Y).Normal ∧ Odd (Nat.card N) ∧
        ∃ k : ℕ, Nat.card Y = Nat.card N * 2 ^ k) ∧
      ∀ Sy : Sylow 2 ↥Y, IsCyclic (Sy : Subgroup ↥Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYZ : ∀ x ∈ Y, x ∉ Z := by
    intro x hx hxZ
    have h1 : x ∈ zHull Z Y := Subgroup.subset_closure ⟨hxZ, hx⟩
    rw [hY, Subgroup.mem_bot] at h1
    have h2 := S.invariant.1 x hxZ
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hcyc : ∀ Sy : Sylow 2 ↥Y, IsCyclic (Sy : Subgroup ↥Y) := by
    intro Sy
    have hmap : IsCyclic ((Sy : Subgroup ↥Y).map Y.subtype) :=
      isCyclic_of_isPGroup S c h163 h164 h165 hB (Sy.isPGroup'.map Y.subtype) (fun x hx => by
        obtain ⟨y, -, rfl⟩ := hx
        exact hYZ y y.2)
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (Sy : Subgroup ↥Y) Y.subtype Y.subtype_injective).symm
      (MulEquiv.surjective _)
  refine ⟨?_, hcyc⟩
  by_cases hodd : Odd (Nat.card Y)
  · exact ⟨Y, le_rfl, by
      rw [Subgroup.subgroupOf_self]
      infer_instance, hodd, 0, by rw [pow_zero, mul_one]⟩
  · have heven : Even (Nat.card ↥Y) := Nat.not_odd_iff_even.mp hodd
    have hmin : (Nat.card ↥Y).minFac = 2 :=
      (Nat.minFac_eq_two_iff _).mpr (even_iff_two_dvd.mp heven)
    obtain ⟨Sy⟩ := (inferInstance : Nonempty (Sylow 2 ↥Y))
    obtain ⟨Kc, hKn, hcomp⟩ : ∃ Kc : Subgroup ↥Y, Kc.Normal ∧ Kc.IsComplement' (Sy : Subgroup ↥Y) :=
      ⟨_, MonoidHom.normal_ker _, IsCyclic.isComplement' hmin (hcyc Sy)⟩
    have hKodd : Odd (Nat.card Kc) := by
      rw [← hcomp.index_eq_card]
      exact Nat.not_even_iff_odd.mp (fun hevenIndex => Sy.not_dvd_index
        (even_iff_two_dvd.mp hevenIndex))
    refine ⟨Kc.map Y.subtype, Subgroup.map_subtype_le _, ?_, ?_,
      (Nat.card ↥Y).factorization 2, ?_⟩
    · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]
      exact hKn
    · rw [Subgroup.card_map_of_injective Y.subtype_injective]
      exact hKodd
    · rw [Subgroup.card_map_of_injective Y.subtype_injective, ← Sylow.card_eq_multiplicity Sy,
        hcomp.card_mul_card]

end Main

end CFSG.GH74.Uniqueness.Cor166
