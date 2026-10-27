module

public import CFSG.Walter.Cited.HuppertPlane
public import CFSG.Quasithin.H13.U3S1347G

public section

namespace CFSG.GroupTheory

open Subgroup

theorem no_orderOf_five_mulAut {V : Type*} [Group V] [Finite V]
    (hV2 : IsPGroup 2 V) (h8 : Nat.card V ≤ 8) {σ : MulAut V} (hσ : orderOf σ = 5) :
    False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : σ ^ 5 ^ 1 = 1 := by
    simpa [hσ] using pow_orderOf_eq_one σ
  have hmod := CFSG.Walter.Huppert.card_fixedSubgroup_modEq (p := 5) (σ := σ) (k := 1) h5
  obtain ⟨d, hd⟩ := (IsPGroup.iff_card (p := 2) (G := V)).mp hV2
  have hfix2 : IsPGroup 2 ↥(CFSG.Walter.Huppert.fixedSubgroup σ) := by
    refine IsPGroup.of_card_dvd_pow (n := d) ?_
    simpa [hd] using Subgroup.card_subgroup_dvd_card (CFSG.Walter.Huppert.fixedSubgroup σ)
  obtain ⟨c, hc⟩ :=
    (IsPGroup.iff_card (p := 2) (G := ↥(CFSG.Walter.Huppert.fixedSubgroup σ))).mp hfix2
  have hc_le : 2 ^ c ≤ 2 ^ d := by
    calc 2 ^ c = Nat.card ↥(CFSG.Walter.Huppert.fixedSubgroup σ) := hc.symm
      _ ≤ Nat.card V := by simpa using Subgroup.card_le_of_le (K := ⊤) le_top
      _ = 2 ^ d := hd
  have hd8 : 2 ^ d ≤ 8 := by rw [← hd]; exact h8
  have hd3 : d ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ d := by omega
    have h16 : 2 ^ 4 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) h4
    norm_num at h16
    omega
  have hcd : c ≤ d := by
    by_contra h
    have hlt : 2 ^ d < 2 ^ c := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hc3 : c ≤ 3 := by omega
  have hmod' : 2 ^ d % 5 = 2 ^ c % 5 := by
    rw [← hd, ← hc]
    exact hmod
  have hdc : d = c := by
    interval_cases d <;> interval_cases c <;> simp at hmod' ⊢
  have hcard : Nat.card ↥(CFSG.Walter.Huppert.fixedSubgroup σ) = Nat.card V := by
    rw [hd, hc, hdc]
  have htop : CFSG.Walter.Huppert.fixedSubgroup σ = ⊤ :=
    Subgroup.eq_top_of_card_eq _ hcard
  have hσ1 : σ = 1 := by
    ext v
    have hv : v ∈ CFSG.Walter.Huppert.fixedSubgroup σ := by rw [htop]; exact Subgroup.mem_top v
    exact hv
  rw [hσ1] at hσ
  simp at hσ

theorem eq_one_of_perfect_of_simple_quotient_of_dvd
    {L Q : Type*} [Group L] [Finite L] [Group Q] [Finite Q]
    (P : Subgroup L) [hPN : P.Normal] (hP2 : IsPGroup 2 P)
    (hsimple : IsSimpleGroup (L ⧸ P)) {n : ℕ} (h5 : n ∣ Nat.card (L ⧸ P))
    [hperf : Group.IsPerfect L]
    (φ : L →* Q) (hQ5 : ¬ n ∣ Nat.card ↥φ.range) : φ = 1 := by
  classical
  haveI hperf' : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
  let ψ : L →* ↥φ.range := φ.codRestrict φ.range (fun x => MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    exact ⟨x, Subtype.ext hx⟩
  by_contra hφ
  have hrange_ne : φ.range ≠ ⊥ := by
    intro hbot
    apply hφ
    ext x
    have hmem : (ψ x).1 ∈ φ.range := (ψ x).2
    have h1 : (ψ x).1 = 1 := Subgroup.mem_bot.mp (by simpa [hbot] using hmem)
    simpa [ψ] using h1
  let R : Subgroup ↥φ.range := P.map ψ
  have hR2 : IsPGroup 2 R := hP2.map ψ
  have hRnormal : R.Normal := hPN.map ψ hψsurj
  let f : (L ⧸ P) →* (↥φ.range ⧸ R) :=
    QuotientGroup.map P R ψ (by
      intro x hx
      exact Subgroup.mem_comap.mpr (Subgroup.mem_map_of_mem ψ hx))
  have hfsurj : Function.Surjective f := by
    refine QuotientGroup.map_surjective_of_surjective P R ψ ?_ _
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨x, rfl⟩ := hψsurj y'
    exact ⟨x, rfl⟩
  haveI : (f.ker).Normal := MonoidHom.normal_ker f
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.ker) with hk | hk
  · have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hk
    have hbij : Function.Bijective f := ⟨hinj, hfsurj⟩
    have hcard : Nat.card (L ⧸ P) = Nat.card (↥φ.range ⧸ R) :=
      Nat.card_congr (Equiv.ofBijective f hbij)
    have h5' : n ∣ Nat.card (↥φ.range ⧸ R) := by rw [← hcard]; exact h5
    have hcardQ : Nat.card ↥φ.range = Nat.card (↥φ.range ⧸ R) * Nat.card ↥R :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup R
    exact hQ5 (hcardQ ▸ dvd_mul_of_dvd_left h5' _)
  · have htriv : ∀ x : L, f (QuotientGroup.mk' P x) = 1 := fun x => by
      have hx : QuotientGroup.mk' P x ∈ f.ker := by rw [hk]; exact Subgroup.mem_top _
      simpa using hx
    have hRtop : R = ⊤ := by
      rw [eq_top_iff]
      intro y _
      obtain ⟨x, hx⟩ := hψsurj y
      have h1 := htriv x
      rw [QuotientGroup.map_mk'] at h1
      rw [hx] at h1
      exact (QuotientGroup.eq_one_iff y).mp h1
    have htopbot : (⊤ : Subgroup ↥φ.range) = ⊥ :=
      CFSG.Quasithin.H13.U3.eq_bot_of_isPerfect_of_isPGroup
        (inferInstance : Group.IsPerfect ↥φ.range).commutator_eq_top (hRtop ▸ hR2)
    have hone : ∀ y : ↥φ.range, y = 1 := fun y => by
      have hy : y ∈ (⊤ : Subgroup ↥φ.range) := Subgroup.mem_top y
      rw [htopbot] at hy
      exact Subgroup.mem_bot.mp hy
    exact hrange_ne (by
      rw [eq_bot_iff]
      intro y hy
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val (hone ⟨y, hy⟩)))

theorem eq_one_of_perfect_of_simple_quotient
    {L Q : Type*} [Group L] [Finite L] [Group Q] [Finite Q]
    (P : Subgroup L) [hPN : P.Normal] (hP2 : IsPGroup 2 P)
    (hsimple : IsSimpleGroup (L ⧸ P)) (h5 : 5 ∣ Nat.card (L ⧸ P))
    [hperf : Group.IsPerfect L]
    (φ : L →* Q) (hQ5 : ¬ 5 ∣ Nat.card ↥φ.range) : φ = 1 :=
  eq_one_of_perfect_of_simple_quotient_of_dvd P hP2 hsimple h5 φ hQ5

theorem le_centralizer_of_perfect_of_isSimple_quotient
    {G : Type} [Group G] [Finite G] {V L : Subgroup G} (P : Subgroup ↥L) [P.Normal]
    (hLperf : ⁅L, L⁆ = L) (hP2 : IsPGroup 2 P)
    (hLsimple : IsSimpleGroup (↥L ⧸ P)) (h5 : 5 ∣ Nat.card (↥L ⧸ P))
    (hLN : L ≤ normalizer (V : Set G)) (hV2 : IsPGroup 2 V) (h8 : Nat.card V ≤ 8) :
    L ≤ centralizer (V : Set G) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro l hl
  let φ : ↥L →* MulAut ↥V := (CFSG.Quasithin.conjAct V).comp (Subgroup.inclusion hLN)
  haveI hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLperf
  have hQ5 : ¬ 5 ∣ Nat.card ↥φ.range := by
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 hdvd
    exact no_orderOf_five_mulAut hV2 h8 (σ := (x : MulAut ↥V)) (by simpa using hx)
  have hφ1 : φ = 1 :=
    eq_one_of_perfect_of_simple_quotient P hP2 hLsimple h5 φ hQ5
  have hconj : CFSG.Quasithin.conjAct V ⟨l, hLN hl⟩ = 1 := by
    have := congrArg (fun f : ↥L →* MulAut ↥V => f ⟨l, hl⟩) hφ1
    simpa [φ, Subgroup.inclusion] using this
  exact (CFSG.Quasithin.AutOn.conjAct_eq_one_iff _).mp hconj

end CFSG.GroupTheory
