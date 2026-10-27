module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1Num
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1

section GLP

open Module CFSG.RankThree.PartOne.LIT

variable {f : ℕ} [Fact f.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod f) V]
  [FiniteDimensional (ZMod f) V]

theorem card_pow_modEq_one_of_free {p : ℕ} (hp : p.Prime) (x : V ≃ₗ[ZMod f] V) (hx : x ^ p = 1)
    (hfree : ∀ v : V, x v = v → v = 0) : f ^ finrank (ZMod f) V ≡ 1 [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite V := Module.finite_of_finite (ZMod f)
  have hG : IsPGroup p ↥(Subgroup.zpowers x) := by
    refine isPGroup_iff_pow_pow_eq_one.mpr fun g => ⟨1, ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    rw [pow_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hk, ← zpow_natCast, ← zpow_mul', zpow_mul,
      zpow_natCast, hx, one_zpow]
  have hfix : MulAction.fixedPoints ↥(Subgroup.zpowers x) V = {0} := by
    ext v
    rw [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro h
      exact hfree v (h ⟨x, Subgroup.mem_zpowers x⟩)
    · rintro rfl m
      rw [Subgroup.smul_def]
      exact smul_zero _
  have key := hG.card_modEq_card_fixedPoints V
  have h1 : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers x) V) = 1 := by
    rw [hfix]
    exact Nat.card_unique
  have hV : Nat.card V = f ^ finrank (ZMod f) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod f), Nat.card_zmod]
  rw [h1, hV] at key
  exact key

theorem three_le_finrank_of_free {p : ℕ} (hp : p.Prime) (hpf : f + 1 < p) (x : V ≃ₗ[ZMod f] V)
    (hx : x ^ p = 1) (hfree : ∀ v : V, x v = v → v = 0) (hne : Nontrivial V) :
    3 ≤ finrank (ZMod f) V := by
  have hmod := card_pow_modEq_one_of_free hp x hx hfree
  have hpos : 0 < finrank (ZMod f) V := Module.finrank_pos
  have hf2 : 2 ≤ f := (Fact.out : f.Prime).two_le
  by_contra hlt
  rcases (show finrank (ZMod f) V = 1 ∨ finrank (ZMod f) V = 2 by omega) with h1 | h2
  ·
    rw [h1, pow_one] at hmod
    unfold Nat.ModEq at hmod
    rw [Nat.mod_eq_of_lt (by omega : f < p), Nat.mod_eq_of_lt hp.one_lt] at hmod
    omega
  ·
    rw [h2] at hmod
    have key : f ^ 2 = (f - 1) * (f + 1) + 1 := by
      obtain ⟨m, hm⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel]
      ring
    rw [key] at hmod
    have hdvd : p ∣ (f - 1) * (f + 1) := by
      have h := (Nat.modEq_iff_dvd' (Nat.le_add_left 1 _)).mp hmod.symm
      rwa [Nat.add_sub_cancel] at h
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h3 | h3
    · have := Nat.le_of_dvd (by omega) h3
      omega
    · have := Nat.le_of_dvd (by omega) h3
      omega

theorem card_le_of_pgroup_gl_le_three {p : ℕ} (hp : p.Prime) (hpf : f + 1 < p)
    (hV : finrank (ZMod f) V ≤ 3) (E : Subgroup (V ≃ₗ[ZMod f] V)) [Finite E]
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ p = 1) :
    Nat.card E ≤ p := by
  by_contra hlt
  rw [not_le] at hlt
  have hpK : (p : ZMod f) ≠ 0 := by
    intro h
    have hdvd : f ∣ p := (ZMod.natCast_eq_zero_iff p f).mp h
    have hfp : f = p := (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime f) hp).mp hdvd
    omega
  have hexpE : ∀ a : E, a ^ p = 1 := fun a => Subtype.ext (hexp a a.2)
  have hsq : p ^ 2 ≤ Nat.card E := by
    obtain ⟨k, hk⟩ := CFSG.RankThree.PartTwo.Census.exists_card_eq_pow_of_exponent hp hexpE
    rw [hk] at hlt ⊢
    have hk2 : 2 ≤ k := by
      by_contra h
      rw [not_le] at h
      interval_cases k <;> simp at hlt <;> omega
    exact Nat.pow_le_pow_right hp.pos hk2
  obtain ⟨x, hxE, hx1, v, hv0, hxv⟩ := exists_fixed_of_sq_le_card hp hpK E hcomm hexp hsq
  have hc := isCompl_fixedSpace_commSpace hpK (hexp x hxE)
  have hxcomm : ∀ g ∈ E, g * x = x * g := fun g hg => hcomm g hg x hxE
  have hWinv : ∀ g : E, ∀ w ∈ commSpace x, (E.subtype g) w ∈ commSpace x :=
    fun g w hw => map_mem_commSpace (hxcomm g g.2) hw
  have hsum : finrank (ZMod f) (fixedSpace x) + finrank (ZMod f) (commSpace x)
      = finrank (ZMod f) V :=
    Submodule.finrank_add_eq_of_isCompl hc
  have hUpos : 0 < finrank (ZMod f) (fixedSpace x) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    exact ⟨⟨v, mem_fixedSpace.mpr hxv⟩, fun h => hv0 (congrArg Subtype.val h)⟩
  have hWpos : 0 < finrank (ZMod f) (commSpace x) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    by_contra hcon
    have hcon' : ∀ w : commSpace x, w = 0 := fun w => by_contra fun hw => hcon ⟨w, hw⟩
    apply hx1
    apply LinearEquiv.ext
    intro y
    have hy : x y - y ∈ commSpace x := mem_commSpace.mpr ⟨y, rfl⟩
    have h2 : x y - y = 0 := congrArg Subtype.val (hcon' ⟨x y - y, hy⟩)
    simpa [sub_eq_zero] using h2
  have hxE1 : (⟨x, hxE⟩ : E) ^ p = 1 := Subtype.ext (hexp x hxE)
  have hxW : (restrictAction E.subtype (commSpace x) hWinv ⟨x, hxE⟩) ^ p = 1 := by
    rw [← map_pow, hxE1, map_one]
  have hfreeW : ∀ w : commSpace x,
      (restrictAction E.subtype (commSpace x) hWinv ⟨x, hxE⟩) w = w → w = 0 := by
    intro w hw
    have hxw : x (w : V) = (w : V) :=
      (restrictAction_apply E.subtype (commSpace x) hWinv ⟨x, hxE⟩ w).symm.trans
        (congrArg Subtype.val hw)
    have hw0 : (w : V) ∈ fixedSpace x := mem_fixedSpace.mpr hxw
    exact Subtype.ext (Submodule.disjoint_def.mp hc.disjoint _ hw0 w.2)
  have hWnt : Nontrivial (commSpace x) := Module.finrank_pos_iff.mp hWpos
  have h3 : 3 ≤ finrank (ZMod f) (commSpace x) :=
    three_le_finrank_of_free hp hpf (restrictAction E.subtype (commSpace x) hWinv ⟨x, hxE⟩)
      hxW hfreeW hWnt
  omega

theorem card_le_of_pgroup_gl_le_four {p : ℕ} (hp : p.Prime) (hpf : f + 1 < p)
    (hV : finrank (ZMod f) V ≤ 4) (E : Subgroup (V ≃ₗ[ZMod f] V)) [Finite E]
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ p = 1) :
    Nat.card E ≤ p := by
  by_cases h3 : finrank (ZMod f) V ≤ 3
  · exact card_le_of_pgroup_gl_le_three hp hpf h3 E hcomm hexp
  have h4 : finrank (ZMod f) V = 4 := by omega
  have hfp : Nat.Prime f := Fact.out
  have hf2 : 2 ≤ f := hfp.two_le
  have hrK : (p : ZMod f) ≠ 0 := by
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    rcases (Nat.dvd_prime hp).1 h0 with h | h
    · omega
    · omega
  have hcop : Nat.Coprime p (f - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  by_contra hlt
  rw [not_le] at hlt
  have hexpE : ∀ a : E, a ^ p = 1 := fun a => Subtype.ext (hexp a a.2)
  have hsq : p ^ 2 ≤ Nat.card E := by
    obtain ⟨k, hk⟩ := CFSG.RankThree.PartTwo.Census.exists_card_eq_pow_of_exponent hp hexpE
    rw [hk] at hlt ⊢
    have hk2 : 2 ≤ k := by
      by_contra h
      rw [not_le] at h
      interval_cases k <;> simp at hlt <;> omega
    exact Nat.pow_le_pow_right hp.pos hk2
  obtain ⟨x, hxE, hx1, v, hv0, hxv⟩ := exists_fixed_of_sq_le_card hp hrK E hcomm hexp hsq
  have hc := isCompl_fixedSpace_commSpace hrK (hexp x hxE)
  have hxcomm : ∀ g ∈ E, g * x = x * g := fun g hg => hcomm g hg x hxE
  have hUinv : ∀ g : E, ∀ u ∈ fixedSpace x, (E.subtype g) u ∈ fixedSpace x :=
    fun g u hu => map_mem_fixedSpace (hxcomm g g.2) hu
  have hWinv : ∀ g : E, ∀ w ∈ commSpace x, (E.subtype g) w ∈ commSpace x :=
    fun g w hw => map_mem_commSpace (hxcomm g g.2) hw
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hUpos : 0 < finrank (ZMod f) (fixedSpace x) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    exact ⟨⟨v, mem_fixedSpace.mpr hxv⟩, fun h => hv0 (congrArg Subtype.val h)⟩
  have hWpos : 0 < finrank (ZMod f) (commSpace x) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    by_contra hcon
    have hcon' : ∀ w : commSpace x, w = 0 := fun w => by_contra fun hw => hcon ⟨w, hw⟩
    apply hx1
    apply LinearEquiv.ext
    intro y
    have hy : x y - y ∈ commSpace x := mem_commSpace.mpr ⟨y, rfl⟩
    have h2 : x y - y = 0 := congrArg Subtype.val (hcon' ⟨x y - y, hy⟩)
    simpa [sub_eq_zero] using h2
  let ρ : E →* (V ≃ₗ[ZMod f] V) := E.subtype
  let ρU := restrictAction ρ (fixedSpace x) hUinv
  let ρW := restrictAction ρ (commSpace x) hWinv
  let xE : E := ⟨x, hxE⟩
  have hxpow : (ρW xE) ^ p = 1 := by rw [← map_pow, hexpE xE, map_one]
  have hfreeW : ∀ w : commSpace x, ρW xE w = w → w = 0 := by
    intro w hw
    have hx' : x (w : V) = (w : V) := congrArg Subtype.val hw
    have hfix : (w : V) ∈ fixedSpace x := mem_fixedSpace.mpr hx'
    exact Subtype.ext (Submodule.disjoint_def.mp hc.disjoint _ hfix w.2)
  have hW3 : 3 ≤ finrank (ZMod f) (commSpace x) :=
    three_le_finrank_of_free hp hpf (ρW xE) hxpow hfreeW (Module.nontrivial_of_finrank_pos hWpos)
  have hU1 : finrank (ZMod f) (fixedSpace x) = 1 := by omega
  have hW3' : finrank (ZMod f) (commSpace x) = 3 := by omega
  obtain ⟨u0, hu0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hUpos
  have hU_triv : ∀ g : E, ρU g = 1 := by
    intro g
    obtain ⟨c, hc', -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hU1
      (ρU g : fixedSpace x →ₗ[ZMod f] fixedSpace x)
    have hφ : ∀ a : fixedSpace x, ρU g a = c • a := fun a => by
      have := LinearMap.congr_fun hc' a
      simpa using this
    have hpow : ∀ n : ℕ, ∀ a : fixedSpace x, (ρU g ^ n) a = c ^ n • a := by
      intro n
      induction n with
      | zero =>
        intro a
        simp only [pow_zero, one_smul]
        rfl
      | succ n ih =>
        intro a
        rw [pow_succ (ρU g) n, LinearEquiv.mul_apply, hφ a, map_smul, ih a, smul_smul,
          pow_succ' c n]
    have hpowE : ρU g ^ p = 1 := by rw [← map_pow, hexpE g, map_one]
    have hcp : c ^ p = 1 := by
      have h1 : (ρU g ^ p) u0 = c ^ p • u0 := hpow p u0
      rw [hpowE] at h1
      have h2 : (c ^ p - 1) • u0 = 0 := by
        rw [sub_smul, one_smul]
        exact sub_eq_zero.mpr h1.symm
      rcases smul_eq_zero.mp h2 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hu0
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hcp
      exact zero_ne_one hcp
    have hcf : c ^ (f - 1) = 1 := ZMod.pow_card_sub_one_eq_one hc0
    have hc1 : c = 1 := by
      have h := (pow_gcd_eq_one (a := c) (m := p) (n := f - 1)).2 ⟨hcp, hcf⟩
      rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h
      exact h
    apply LinearEquiv.ext
    intro a
    show ρU g a = a
    rw [hφ a, hc1, one_smul]
  have hext : ∀ g : E, ρU g = 1 → ρW g = 1 → g = 1 := by
    intro g h1 h2
    apply Subtype.ext
    apply LinearEquiv.ext
    intro y
    have hfun : (g : V ≃ₗ[ZMod f] V).toLinearMap = LinearMap.id := by
      apply ext_of_isCompl hc
      · intro u hu
        exact (restrictAction_apply ρ (fixedSpace x) hUinv g ⟨u, hu⟩).symm.trans
          (congrArg Subtype.val (LinearEquiv.congr_fun h1 ⟨u, hu⟩))
      · intro w hw
        exact (restrictAction_apply ρ (commSpace x) hWinv g ⟨w, hw⟩).symm.trans
          (congrArg Subtype.val (LinearEquiv.congr_fun h2 ⟨w, hw⟩))
    exact LinearMap.congr_fun hfun y
  have hinj : Function.Injective ρW :=
    (injective_iff_map_eq_one ρW).2 fun g hg => hext g (hU_triv g) hg
  have hfin : Finite ρW.range :=
    Finite.of_surjective ρW.rangeRestrict (MonoidHom.rangeRestrict_surjective ρW)
  have hcardEq : Nat.card E = Nat.card ρW.range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hcomm' : ∀ g ∈ ρW.range, ∀ h ∈ ρW.range, g * h = h * g := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have hab : a * b = b * a := Subtype.ext (hcomm a a.2 b b.2)
    rw [← map_mul, ← map_mul, hab]
  have hexp' : ∀ g ∈ ρW.range, g ^ p = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, hexpE a, map_one]
  have hle := card_le_of_pgroup_gl_le_three hp hpf hW3'.le ρW.range hcomm' hexp'
  omega


end GLP

section Bound

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem exists_rank_bound_ge5 {f p : ℕ} [Fact f.Prime] (hf2 : f ≠ 2) (hp : p.Prime)
    (hpf : p ≠ f) {Fs N : Subgroup K} (hFs : IsPGroup f Fs) (hN : N ≤ normalizer (Fs : Set K))
    (hrank : ∀ E : Subgroup K, E ≤ Fs → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a ^ f = 1) → Nat.card E ≤ f ^ 3)
    (hdisj : (∀ E : Subgroup K, E ≤ Fs → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a ^ f = 1) → Nat.card E ≤ f ^ 2) ∨ f + 1 < p) :
    ∃ χ : ↥N →* (ZMod f)ˣ, ∀ (E : Subgroup K) (hEN : E ≤ N),
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ p = 1) →
      (∀ (a : K) (ha : a ∈ E), χ ⟨a, hEN ha⟩ = 1) →
      Nat.card E ≤ p * Nat.card (E ⊓ centralizer (Fs : Set K) : Subgroup K) := by
  have hf : f.Prime := Fact.out
  obtain ⟨Ω, hΩ⟩ := exists_omega hf2 hp hpf hFs hN
  have hΩ5 : Nat.card Ω ≤ f ^ 5 := card_le_pow_five hf hΩ.exp hΩ.central
    (fun E hEΩ hEc => hrank E (hEΩ.trans hΩ.le) hEc (fun a ha => hΩ.exp a (hEΩ ha)))
  have hle : (⁅Ω, Ω⁆ : Subgroup K) ≤ Ω := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2.commutator_le_self Ω
  obtain ⟨W, _, _, _, π, ρ, hs⟩ := exists_elemSec (f := f) (Y := Ω) (M := ⁅Ω, Ω⁆) (G := N) hle
    (fun x hx m hm => (mem_normalizer_iff.mp
      (normalizer_le_normalizer_commutator Ω (le_normalizer hx)) m).mp hm)
    (fun x hx y hy => Subgroup.commutator_mem_commutator hx hy)
    (fun x hx => by rw [hΩ.exp x hx]; exact one_mem _)
    hΩ.norm (fun g hg => normalizer_le_normalizer_commutator Ω (hΩ.norm hg))
  haveI : Finite W := Module.finite_of_finite (ZMod f)
  set d := Module.finrank (ZMod f) W with hd
  have hrK : ((p : ℕ) : ZMod f) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff p f).mp h
    exact hpf ((Nat.prime_dvd_prime_iff_eq hf hp).mp this).symm
  have hfaith : ∀ (a : K) (haN : a ∈ N), a ^ p = 1 → actEquiv ρ ⟨a, haN⟩ = 1 →
      a ∈ centralizer (Fs : Set K) := by
    intro a haN hap h1
    rw [mem_centralizer_iff]
    intro x hx
    refine (hΩ.faithful a haN 1 (by simpa using hap) (fun y hy => ?_) x hx).symm
    have hay : a * y * a⁻¹ ∈ Ω := (mem_normalizer_iff.mp (hΩ.norm haN) y).mp hy
    refine (hs.eq_iff hy hay).mp ?_
    have h2 := hs.act ⟨a, haN⟩ y hy
    have h3 : ρ ⟨a, haN⟩ (π y) = π y := by
      have := LinearEquiv.congr_fun h1 (π y)
      exact this
    rw [h3] at h2
    exact h2
  have hcardW : Nat.card Ω = Nat.card (⁅Ω, Ω⁆ : Subgroup K) * f ^ d := by
    rw [hs.card_eq hle, Module.natCard_eq_pow_finrank (K := ZMod f) (V := W), Nat.card_zmod]
  obtain ⟨k, hk⟩ := (hFs.to_le (hle.trans hΩ.le)).exists_card_eq
  have hdcase : d ≤ 3 ∨ (d = 4 ∧ Nat.card (⁅Ω, Ω⁆ : Subgroup K) = f) := by
    by_cases hk0 : k = 0
    · left
      have hbot : (⁅Ω, Ω⁆ : Subgroup K) = ⊥ :=
        Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])
      have hcomm : ∀ a ∈ Ω, ∀ b ∈ Ω, a * b = b * a := by
        intro a ha b hb
        have : ⁅a, b⁆ ∈ (⁅Ω, Ω⁆ : Subgroup K) := Subgroup.commutator_mem_commutator ha hb
        rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
        exact this
      have h1 := hrank Ω hΩ.le hcomm hΩ.exp
      rw [hcardW, hk, hk0, pow_zero, one_mul] at h1
      exact (Nat.pow_le_pow_iff_right hf.one_lt).mp h1
    · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
      have h5 : f ^ (k + d) ≤ f ^ 5 := by rw [pow_add, ← hk, ← hcardW]; exact hΩ5
      have h6 : k + d ≤ 5 := (Nat.pow_le_pow_iff_right hf.one_lt).mp h5
      by_cases hd4 : d ≤ 3
      · exact Or.inl hd4
      · right
        have hd : d = 4 := by omega
        refine ⟨hd, ?_⟩
        have hk' : k = 1 := by omega
        rw [hk, hk', pow_one]
  have himg : ∀ (E : Subgroup K) (hEN : E ≤ N), (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a ^ p = 1) →
      Finite (actEquiv ρ |>.comp (Subgroup.inclusion hEN)).range ∧
      (∀ g ∈ (actEquiv ρ |>.comp (Subgroup.inclusion hEN)).range,
        ∀ h ∈ (actEquiv ρ |>.comp (Subgroup.inclusion hEN)).range, g * h = h * g) ∧
      (∀ g ∈ (actEquiv ρ |>.comp (Subgroup.inclusion hEN)).range, g ^ p = 1) := by
    intro E hEN hEc hEp
    refine ⟨Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective _), ?_, ?_⟩
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hEc a a.2 b b.2)
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ p = 1 := Subtype.ext (hEp a a.2)
      rw [this, map_one]
  have hker : ∀ (E : Subgroup K) (hEN : E ≤ N), (∀ a ∈ E, a ^ p = 1) → ∀ a : ↥E,
      actEquiv ρ (Subgroup.inclusion hEN a) = 1 → (a : K) ∈ centralizer (Fs : Set K) :=
    fun E hEN hEp a h => hfaith (a : K) (hEN a.2) (hEp a a.2) h
  rcases hdisj with hrank2 | hlt
  ·
    have hΩ3 : Nat.card Ω ≤ f ^ 3 := card_le_pow_three hf hΩ.exp
      (fun E hEΩ hEc => hrank2 E (hEΩ.trans hΩ.le) hEc (fun a ha => hΩ.exp a (hEΩ ha)))
    have hd2 : d ≤ 2 := by
      by_cases hk0 : k = 0
      · have hbot : (⁅Ω, Ω⁆ : Subgroup K) = ⊥ :=
          Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])
        have hcomm : ∀ a ∈ Ω, ∀ b ∈ Ω, a * b = b * a := by
          intro a ha b hb
          have : ⁅a, b⁆ ∈ (⁅Ω, Ω⁆ : Subgroup K) := Subgroup.commutator_mem_commutator ha hb
          rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
          exact this
        have h1 := hrank2 Ω hΩ.le hcomm hΩ.exp
        rw [hcardW, hk, hk0, pow_zero, one_mul] at h1
        exact (Nat.pow_le_pow_iff_right hf.one_lt).mp h1
      · have h3 : f ^ (k + d) ≤ f ^ 3 := by
          rw [pow_add, ← hk, ← hcardW]
          exact hΩ3
        have h4 := (Nat.pow_le_pow_iff_right hf.one_lt).mp h3
        omega
    refine ⟨LinearEquiv.det.comp (actEquiv ρ), fun E hEN hEc hEp hχ => ?_⟩
    obtain ⟨hfin, hcomm, hexp⟩ := himg E hEN hEc hEp
    haveI := hfin
    refine card_le_of_range (actEquiv ρ) hEN (hker E hEN hEp) ?_
    by_cases hd1 : d ≤ 1
    · have h1 := CFSG.RankThree.PartOne.LIT.card_le_pow_finrank_sub hp hrK
        (actEquiv ρ |>.comp (Subgroup.inclusion hEN)).range hcomm hexp
      calc _ ≤ p ^ d := h1
        _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hd1
        _ = p := pow_one p
    · have hd2' : d = 2 := by omega
      refine card_le_of_det_eq_one_of_finrank_eq_two hp hrK hd2'
        (actEquiv ρ |>.comp (Subgroup.inclusion hEN)).range hcomm hexp ?_
      rintro _ ⟨a, rfl⟩
      have h2 : LinearMap.det (((actEquiv ρ) ⟨(a : K), hEN a.2⟩ : W ≃ₗ[ZMod f] W) :
          W →ₗ[ZMod f] W) = 1 := by
        have h3 := congrArg (fun z : (ZMod f)ˣ => (z : ZMod f)) (hχ (a : K) a.2)
        simpa [LinearEquiv.coe_det] using h3
      exact h2
  ·
    have hd4 : d ≤ 4 := by
      rcases hdcase with h | ⟨h, -⟩ <;> omega
    refine ⟨1, fun E hEN hEc hEp _ => ?_⟩
    obtain ⟨hfin, hcomm, hexp⟩ := himg E hEN hEc hEp
    haveI := hfin
    refine card_le_of_range (actEquiv ρ) hEN (hker E hEN hEp) ?_
    exact card_le_of_pgroup_gl_le_four hp hlt hd4 _ hcomm hexp

theorem lemma69_ge5 {A : Type} [Group A] [Finite A] {p f : ℕ} (hp : p.Prime) (_hp5 : 5 ≤ p)
    (hf : f.Prime) (hf2 : f ≠ 2) (hfp : f ≠ p) {X D Fs R : Subgroup A}
    (hperf : ∀ (M : Subgroup ↥X) [M.Normal], IsPGroup p (↥X ⧸ M) → M = ⊤)
    (hDX : D ≤ X) (hDn : ∀ x ∈ X, ∀ d ∈ D, x * d * x⁻¹ ∈ D) (hD : ¬ p ∣ Nat.card D)
    (hFsp : IsPGroup f Fs) (hFsX : Fs ≤ X)
    (hXDN : ∀ x ∈ X, ∃ d ∈ D, ∃ n ∈ X ⊓ normalizer (Fs : Set A), x = d * n)
    (hRN : R ≤ X ⊓ normalizer (Fs : Set A)) (hR3 : 3 ≤ Open.pRank p R)
    (hcyc : IsCyclic (R ⊓ centralizer (Fs : Set A) : Subgroup A))
    (hX3 : Open.pRank f X ≤ 3) : 3 ≤ Open.pRank f Fs ∧ p ≤ f + 1 := by
  haveI : Fact f.Prime := ⟨hf⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero f := ⟨hf.ne_zero⟩
  obtain ⟨E, hER, hEab, hEcard⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_isElemAbelian_of_le_pRank hp hR3
  have hEN : E ≤ X ⊓ normalizer (Fs : Set A) := hER.trans hRN
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h2 : Nat.card (E ⊓ centralizer (Fs : Set A) : Subgroup A) ≤ p :=
    card_le_of_cyclic hp.pos hcyc (inf_le_inf_right _ hER) (fun t ht => hEab.2 t ht.1)
  have key : ((∀ E' : Subgroup A, E' ≤ Fs → (∀ a ∈ E', ∀ b ∈ E', a * b = b * a) →
      (∀ a ∈ E', a ^ f = 1) → Nat.card E' ≤ f ^ 2) ∨ f + 1 < p) → False := by
    intro hdisj
    obtain ⟨χ, hχ⟩ := exists_rank_bound_ge5 hf2 hp hfp.symm hFsp
      (N := X ⊓ normalizer (Fs : Set A)) inf_le_right (card_le_pow_of_pRank_le hf hFsX hX3) hdisj
    have hχE : ∀ (a : A) (ha : a ∈ E), χ ⟨a, hEN ha⟩ = 1 := fun a ha =>
      trivial_of_perfect hp hperf hDX hDn hD inf_le_left hXDN χ a (hEN ha) 1
        (by simpa using hEab.2 a ha)
    have h1 := hχ E hEN hEc hEab.2 hχE
    rw [hEcard] at h1
    have h3 : p ^ 3 ≤ p * p := h1.trans (Nat.mul_le_mul_left _ h2)
    have h4 : p * p < p ^ 3 := by
      have := hp.one_lt
      calc p * p = p ^ 2 := by ring
        _ < p ^ 3 := Nat.pow_lt_pow_right this (by norm_num)
    omega
  refine ⟨?_, ?_⟩
  · by_contra h
    push Not at h
    exact key (Or.inl (card_le_pow_of_pRank_le hf (le_refl Fs) (by omega : Open.pRank f Fs ≤ 2)))
  · by_contra h
    push Not at h
    exact key (Or.inr h)

theorem lemma69_ge5_lt {A : Type} [Group A] [Finite A] {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hf : f.Prime) (hf2 : f ≠ 2) (hfp : f ≠ p) {X D Fs R : Subgroup A}
    (hperf : ∀ (M : Subgroup ↥X) [M.Normal], IsPGroup p (↥X ⧸ M) → M = ⊤)
    (hDX : D ≤ X) (hDn : ∀ x ∈ X, ∀ d ∈ D, x * d * x⁻¹ ∈ D) (hD : ¬ p ∣ Nat.card D)
    (hFsp : IsPGroup f Fs) (hFsX : Fs ≤ X)
    (hXDN : ∀ x ∈ X, ∃ d ∈ D, ∃ n ∈ X ⊓ normalizer (Fs : Set A), x = d * n)
    (hRN : R ≤ X ⊓ normalizer (Fs : Set A)) (hR3 : 3 ≤ Open.pRank p R)
    (hcyc : IsCyclic (R ⊓ centralizer (Fs : Set A) : Subgroup A))
    (hX3 : Open.pRank f X ≤ 3) : 3 ≤ Open.pRank f Fs ∧ p < f := by
  obtain ⟨h3, hle⟩ := lemma69_ge5 hp hp5 hf hf2 hfp hperf hDX hDn hD hFsp hFsX hXDN hRN hR3 hcyc hX3
  refine ⟨h3, ?_⟩
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left (by omega)
  have hfodd : Odd f := hf.eq_two_or_odd'.resolve_left hf2
  obtain ⟨a, ha⟩ := hpodd
  obtain ⟨b, hb⟩ := hfodd
  omega

end Bound

section Sigma

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem f_mem_sigmaA_of_pRank {G : Type} [Group G] [Finite G] (hrank : evenRank G = 3)
    {p f : ℕ} (hp7 : 7 ≤ p) (hp : p ∈ rankThreeSigmaA G) (hf : f.Prime) (hf5 : p < f)
    {M : Subgroup G} (hM : IsTwoLocal M) (h3 : 3 ≤ Open.pRank f M) : f ∈ rankThreeSigmaA G := by
  classical
  haveI : Fact f.Prime := ⟨hf⟩
  have hle : Open.pRank f M ≤ 3 :=
    (local_pRank_le_evenRank f hf (by omega) M hM).trans hrank.le
  have hbdd : BddAbove {k | ∃ K : Subgroup G, IsTwoLocal K ∧ CFSG.Open.pRank f K = k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨K, -, rfl⟩
    refine CFSG.SectionRank.pRank_le hf.one_lt (k := Nat.card G) (fun E _ hE => ?_)
    exact (Subgroup.card_le_card_group E).trans (Nat.lt_pow_self hf.one_lt).le
  have hloc3 : rankThreeLocalRank f G = 3 := by
    have h1 : Open.pRank f M ≤ rankThreeLocalRank f G := le_csSup hbdd ⟨M, hM, rfl⟩
    have h2 := rankThreeLocalRank_le_evenRank (G := G) f hf (by omega)
    omega
  have hdvd : f ∣ Nat.card G :=
    (CFSG.LocalAnalysis.RankFourTheoremC.dvd_card_of_one_le_pRank hf
      (by omega : 1 ≤ Open.pRank f M)).trans (Subgroup.card_subgroup_dvd_card M)
  dsimp only [rankThreeSigmaA] at hp ⊢
  split_ifs at hp ⊢ with h1 h2 h3'
  · exfalso
    have hlt := hp.2.2.2
    have hle5 := rankThreeLocalRank_le_evenRank (G := G) p hp.1 (by omega)
    omega
  · exact ⟨hf, by omega, hdvd, hloc3⟩
  · exact absurd ⟨f, hf, by omega, hdvd, hloc3⟩ h2
  · exact absurd ⟨f, hf, by omega, hdvd, hloc3⟩ h2

end Sigma

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1
