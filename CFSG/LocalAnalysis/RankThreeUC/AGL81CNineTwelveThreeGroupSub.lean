module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveThreeGroupA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveThreeGroupB

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem center_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (center A).map e.toMonoidHom = center B := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_center_iff,
    Subgroup.mem_center_iff]
  constructor
  · intro hx g
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx]
  · intro hx g
    apply e.injective
    rw [map_mul, map_mul, hx]

private theorem isExtraspecialPGroup_of_mulEquiv {p : ℕ} {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : CFSG.IsExtraspecialPGroup p A) : CFSG.IsExtraspecialPGroup p B := by
  obtain ⟨hp, hcomm, hfrat, hcard⟩ := h
  have hc : (commutator A).map e.toMonoidHom = commutator B := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  have hf : (frattini A).map e.toMonoidHom = frattini B :=
    OrderIso.map_radical (MulEquiv.mapSubgroup e)
  refine ⟨hp.of_equiv e, ?_, ?_, ?_⟩
  · rw [← hc, hcomm, center_map_mulEquiv]
  · rw [← hf, hfrat, center_map_mulEquiv]
  · rw [← center_map_mulEquiv e, Subgroup.card_map_of_injective e.injective, hcard]

private theorem pow_apply_eq_of_forall_eq {A : Type*} [Group A] (α : MulAut A) {D : Subgroup A}
    (h : ∀ x ∈ D, α x = x) (m : ℕ) {x : A} (hx : x ∈ D) : (α ^ m) x = x := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, h x hx]
    exact ih

theorem omegaOnePSub_of_pElement {R : Subgroup G} (hR : IsPGroup 3 ↥R)
    (hrk : CFSG.Open.pRank 3 R ≤ 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {y : G}
    (hyN : y ∈ normalizer (R : Set G)) (hyp : ∃ n : ℕ, y ^ p ^ n = 1)
    (hyC : y ∉ centralizer (R : Set G)) :
    (p = 13 ∧ CFSG.Open.IsElemAbelian 3 (omegaOnePSub 3 R) ∧
        Nat.card (omegaOnePSub 3 R) = 27 ∧ omegaOnePSub 3 R ≤ centralizer (R : Set G) ∧
        ∃ d ∈ omegaOnePSub 3 R, y * d * y⁻¹ ≠ d) ∨
      (p = 5 ∧ CFSG.IsExtraspecialPGroup 3 ↥(omegaOnePSub 3 R) ∧
        Nat.card (omegaOnePSub 3 R) = 3 ^ 5 ∧ Monoid.exponent ↥(omegaOnePSub 3 R) = 3) := by
  let g : normalizer (R : Set G) := ⟨y, hyN⟩
  let α₀ : MulAut ↥R := R.normalizerMonoidHom g
  have hα₀ne : α₀ ≠ 1 := by
    intro hα01
    apply hyC
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    let r' : ↥R := ⟨r, hr⟩
    have hfix : α₀ r' = r' := by
      rw [hα01, MulAut.one_apply]
    have hco : ((α₀ r' : ↥R) : G) = y * r * y⁻¹ := by
      simpa [α₀, g, r'] using Subgroup.normalizerMonoidHom_apply_apply_coe R g r'
    have h : y * r * y⁻¹ = r := by
      rw [← hco, hfix]
    have h' : y * r = r * y := by
      have hh := congrArg (fun t => t * y) h
      simpa [mul_assoc] using hh
    exact h'.symm
  obtain ⟨n, hn⟩ := hyp
  have hg : g ^ p ^ n = 1 := Subtype.ext (by simpa [g] using hn)
  have hdvd : orderOf α₀ ∣ p ^ n := by
    have h1 : orderOf α₀ ∣ orderOf g := orderOf_map_dvd R.normalizerMonoidHom g
    exact h1.trans (orderOf_dvd_of_pow_eq_one hg)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hjpos : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with hj0 | hpos
    · exfalso
      have h1 : orderOf α₀ = 1 := by rw [hj, hj0, pow_zero]
      exact hα₀ne (orderOf_eq_one_iff.mp h1)
    · exact hpos
  let α : MulAut ↥R := α₀ ^ p ^ (j - 1)
  have hα : orderOf α = p := by
    dsimp only [α]
    have hdvdα : p ^ (j - 1) ∣ orderOf α₀ := by
      rw [hj]
      exact pow_dvd_pow p (Nat.sub_le j 1)
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) hdvdα, hj,
      Nat.pow_div (Nat.sub_le j 1) hp.pos]
    have hjm : j - (j - 1) = 1 := by omega
    rw [hjm, pow_one]
  have hmap : (⊤ : Subgroup ↥R).map R.subtype = R := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨a, -, rfl⟩; exact a.2
    · intro hx; exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hrk' : CFSG.Open.pRank 3 (⊤ : Subgroup ↥R) ≤ 3 := by
    have h := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num)
      R.subtype R.subtype_injective (⊤ : Subgroup ↥R)
    rw [hmap] at h
    exact h.trans hrk
  obtain ⟨D, hDchar, hDexp, hDcomm, hDmove, hcase⟩ :=
    exists_omega_of_mulAut (R := ↥R) hR hrk' hp hp2 hp3 hα
  have hmem : ∀ x : ↥R, x ^ 3 = 1 → x ∈ D := by
    intro x hx
    rcases hcase with ⟨-, -, hDcard27, hDc⟩ | ⟨-, hDext, hDcard5⟩
    · exact mem_of_pow_three_eq_one_of_le_center hR hrk' hDexp hDc hDcard27 hx
    · haveI : D.Characteristic := hDchar
      exact mem_of_pow_three_eq_one_of_extraspecial hR hrk' hDexp hDcomm hDext hDcard5 hx
  have himg : R.subtype '' (D : Set ↥R) = {x : G | x ∈ R ∧ x ^ 3 = 1} := by
    ext x
    constructor
    · rintro ⟨d, hdD, rfl⟩
      exact ⟨d.2, by simpa using congrArg Subtype.val (hDexp d hdD)⟩
    · rintro ⟨hxR, hx3⟩
      exact ⟨⟨x, hxR⟩, hmem ⟨x, hxR⟩ (Subtype.ext (by simpa using hx3)), rfl⟩
  have hΩ : omegaOnePSub 3 R = D.map R.subtype := by
    unfold omegaOnePSub
    rw [← himg, ← MonoidHom.map_closure, Subgroup.closure_eq]
  have hcardΩ : Nat.card (omegaOnePSub 3 R) = Nat.card D := by
    rw [hΩ, Subgroup.card_map_of_injective R.subtype_injective]
  have hα₀move : ∃ d ∈ D, α₀ d ≠ d := by
    by_contra h
    push Not at h
    obtain ⟨d, hdD, hαd⟩ := hDmove
    exact hαd (by
      have hfix := pow_apply_eq_of_forall_eq α₀ h (p ^ (j - 1)) hdD
      simpa [α] using hfix)
  rcases hcase with ⟨hp13, hDcomm', hDcard27, hDc⟩ | ⟨hp5, hDext, hDcard5⟩
  · refine Or.inl ⟨hp13, ?_, ?_, ?_, ?_⟩
    · rw [hΩ]
      exact CFSG.SectionRank.isElemAbelian_map ⟨hDcomm', hDexp⟩ R.subtype
    · rw [hcardΩ, hDcard27]
    · rw [hΩ]
      rintro a ha
      obtain ⟨d, hdD, rfl⟩ := Subgroup.mem_map.1 ha
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hc := Subgroup.mem_center_iff.mp (hDc hdD) (⟨r, hr⟩ : ↥R)
      simpa using congrArg Subtype.val hc
    · obtain ⟨d, hdD, hα0d⟩ := hα₀move
      refine ⟨(d : G), ?_, ?_⟩
      · rw [hΩ]; exact Subgroup.mem_map_of_mem R.subtype hdD
      · intro hconj
        apply hα0d
        apply Subtype.ext
        have hcoe : ((α₀ d : ↥R) : G) = y * (d : G) * y⁻¹ := by
          simpa [α₀, g] using Subgroup.normalizerMonoidHom_apply_apply_coe R g d
        rw [hcoe]
        exact hconj
  · refine Or.inr ⟨hp5, ?_, ?_, ?_⟩
    · rw [hΩ]
      exact isExtraspecialPGroup_of_mulEquiv
        (D.equivMapOfInjective R.subtype R.subtype_injective) hDext
    · rw [hcardΩ, hDcard5]
    · rw [hΩ]
      have hpow : ∀ a : ↥(D.map R.subtype), a ^ 3 = 1 := by
        intro a
        obtain ⟨d, hd, hgd⟩ := Subgroup.mem_map.1 a.2
        apply Subtype.ext
        change (a : G) ^ 3 = (1 : G)
        rw [← hgd]
        simpa using congrArg Subtype.val (hDexp d hd)
      have hexpne : Monoid.exponent ↥(D.map R.subtype) ≠ 1 := by
        intro h1
        haveI : Subsingleton ↥(D.map R.subtype) := Monoid.exp_eq_one_iff.mp h1
        have hle : Nat.card ↥(D.map R.subtype) ≤ 1 :=
          Finite.card_le_one_iff_subsingleton.mpr inferInstance
        rw [Subgroup.card_map_of_injective R.subtype_injective, hDcard5] at hle
        norm_num at hle
      have hdvd3 : Monoid.exponent ↥(D.map R.subtype) ∣ 3 :=
        Monoid.exponent_dvd_of_forall_pow_eq_one hpow
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
      · exact absurd h hexpne
      · exact h

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
