module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Glauberman.Basic
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Glauberman.CharP
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Glauberman.Tiling

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB

open Subgroup MulAction
open scoped commutatorElement

section TransferFormula

variable {G : Type*} [Group G] {H : Subgroup G} {A : Type*} [CommGroup A]

theorem transfer_eq_prod_of_conj_mem [H.FiniteIndex] [Fintype (G ⧸ H)] (ϕ : H →* A) (g : G)
    (hg : ∀ x : G, x⁻¹ * g * x ∈ H) :
    ϕ.transfer g = ∏ q : G ⧸ H, ϕ ⟨(Quotient.out q)⁻¹ * g * Quotient.out q, hg _⟩ := by
  have hf : ∀ q : G ⧸ H, ((Quotient.out q : G) : G ⧸ H) = q := fun q => QuotientGroup.out_eq' q
  let T : H.LeftTransversal := ⟨Set.range (fun q : G ⧸ H => Quotient.out q),
    isComplement_range_left hf⟩
  have hT : ∀ q, ((T.2.leftQuotientEquiv q : Set.range _) : G) = Quotient.out q :=
    fun q => IsComplement.leftQuotientEquiv_apply hf q
  have hfix : ∀ q : G ⧸ H, g⁻¹ • q = q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
      simpa [mul_assoc] using hg x
  rw [MonoidHom.transfer_def ϕ T g]
  unfold Subgroup.leftTransversals.diff
  simp only
  refine Finset.prod_congr (by ext; simp) fun q _ => ?_
  congr 1
  apply Subtype.ext
  dsimp only
  rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, hfix, hT, smul_eq_mul, mul_assoc]

end TransferFormula

section Wielandt

variable {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ} [hp : Fact p.Prime]

theorem mem_normalizer_closure_of_conj {E₀ : Set Γ} {g : Γ} (h : ∀ e ∈ E₀, g⁻¹ * e * g ∈ E₀) :
    g ∈ normalizer ((closure E₀ : Subgroup Γ) : Set Γ) := by
  have hle : (closure E₀).map (MulAut.conj g⁻¹).toMonoidHom ≤ closure E₀ := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨e, he, rfl⟩
    exact subset_closure (by simpa [MulAut.conj_apply] using h e he)
  have heq : (closure E₀).map (MulAut.conj g⁻¹).toMonoidHom = closure E₀ :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g⁻¹).injective])
  have hmem : g⁻¹ ∈ normalizer ((closure E₀ : Subgroup Γ) : Set Γ) :=
    mem_normalizer_iff_map_conj_eq.mpr heq
  simpa using (normalizer _).inv_mem hmem

theorem wielandt (S : Sylow p Γ) {Y : Subgroup Γ} (hYn : Y.Normal) (hYS : Y ≤ S)
    (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hYp : ∀ y ∈ Y, y ^ p = 1) (E₀ : Set Γ)
    (hE₀S : E₀ ⊆ (S : Subgroup Γ))
    (hwc : ∀ g : Γ, (∀ e ∈ E₀, g⁻¹ * e * g ∈ (S : Subgroup Γ)) → ∀ e ∈ E₀, g⁻¹ * e * g ∈ E₀)
    (hnil : ∀ e ∈ E₀, ∀ y ∈ Y, iterComm y e (p - 1) = 1) :
    (S : Subgroup Γ) ≤ normalizer ((closure E₀ : Subgroup Γ) : Set Γ) ∧
      Y ⊓ commutator Γ ≤ ⁅normalizer ((closure E₀ : Subgroup Γ) : Set Γ),
        normalizer ((closure E₀ : Subgroup Γ) : Set Γ)⁆ := by
  classical
  set E : Subgroup Γ := closure E₀ with hEdef
  set L : Subgroup Γ := normalizer (E : Set Γ) with hLdef
  have hES : E ≤ S := (closure_le _).mpr hE₀S
  have hEp : IsPGroup p E := S.isPGroup'.to_le hES
  have hSL : (S : Subgroup Γ) ≤ L := by
    intro s hs
    refine mem_normalizer_closure_of_conj (hwc s fun e he => ?_)
    exact S.mul_mem (S.mul_mem (S.inv_mem hs) (hE₀S he)) hs
  have hEL : E ≤ L := hES.trans hSL
  have hYL : Y ≤ L := hYS.trans hSL
  have hfixL : ∀ x : Γ, (∀ e ∈ E, x⁻¹ * e * x ∈ L) → x ∈ L := by
    intro x hx
    have hB : E.map (MulAut.conj x⁻¹).toMonoidHom ≤ L := by
      rintro _ ⟨e, he, rfl⟩
      simpa [MulAut.conj_apply] using hx e he
    obtain ⟨l, hl, hlS⟩ := (IsSylowOf.of_sylow S hSL).exists_conj_le hB (hEp.map _)
    have hxl : x * l ∈ L := by
      refine mem_normalizer_closure_of_conj (hwc _ fun e he => ?_)
      have := hlS _ ⟨e, subset_closure he, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using this
    simpa using L.mul_mem hxl (L.inv_mem hl)
  haveI : Fintype (Γ ⧸ L) := Fintype.ofFinite _
  let ϕ : ↥L →* Abelianization ↥L := Abelianization.of
  refine ⟨hSL, ?_⟩
  rintro g ⟨hgY, hgc⟩
  have hgconj : ∀ x : Γ, x⁻¹ * g * x ∈ L := fun x => hYL (by
    have := hYn.conj_mem g hgY x⁻¹
    simpa using this)
  have hV1 : ϕ.transfer g = 1 := Abelianization.commutator_subset_ker _ hgc
  let F : Γ ⧸ L → Abelianization ↥L := fun q =>
    ϕ ⟨(Quotient.out q)⁻¹ * g * Quotient.out q, hgconj _⟩
  have hFrep : ∀ y : Γ, F (y : Γ ⧸ L) = ϕ ⟨y⁻¹ * g * y, hgconj y⟩ := by
    intro y
    obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul L y
    show ϕ ⟨(Quotient.out (y : Γ ⧸ L))⁻¹ * g * Quotient.out (y : Γ ⧸ L), _⟩ = _
    have e1 : (⟨(Quotient.out (y : Γ ⧸ L))⁻¹ * g * Quotient.out (y : Γ ⧸ L), hgconj _⟩ : ↥L) =
        l⁻¹ * ⟨y⁻¹ * g * y, hgconj y⟩ * l := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hl]
      group
    rw [e1, map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  have hVF : ϕ.transfer g = ∏ q : Γ ⧸ L, F q := transfer_eq_prod_of_conj_mem ϕ g hgconj
  haveI : Fintype (orbitRel.Quotient (↥E) (Γ ⧸ L)) := Fintype.ofFinite _
  have hfiber : ∀ j : orbitRel.Quotient (↥E) (Γ ⧸ L),
      (Finset.univ.filter fun q : Γ ⧸ L => (Quotient.mk (orbitRel (↥E) (Γ ⧸ L)) q) = j) =
        orbF E (Quotient.out j) := by
    intro j
    ext q
    rw [Finset.mem_filter, mem_orbF]
    simp only [Finset.mem_univ, true_and]
    conv_lhs => rw [← Quotient.out_eq j]
    rw [Quotient.eq, orbitRel_apply, mem_orbit_iff]
    constructor
    · rintro ⟨e, he⟩
      exact ⟨e, e.2, he⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨e, he⟩, rfl⟩
  have hprod : ∏ q : Γ ⧸ L, F q =
      ∏ j : orbitRel.Quotient (↥E) (Γ ⧸ L), ∏ q ∈ orbF E (Quotient.out j), F q := by
    rw [← Finset.prod_fiberwise Finset.univ (fun q => Quotient.mk (orbitRel (↥E) (Γ ⧸ L)) q) F]
    exact Finset.prod_congr rfl fun j _ => by rw [hfiber]
  set j₁ : orbitRel.Quotient (↥E) (Γ ⧸ L) := Quotient.mk _ ((1 : Γ) : Γ ⧸ L) with hj₁
  have horb1 : ∀ q₀ : Γ ⧸ L, Quotient.mk (orbitRel (↥E) (Γ ⧸ L)) q₀ = j₁ →
      orbF E q₀ = {((1 : Γ) : Γ ⧸ L)} := by
    intro q₀ hq₀
    have hq₀' : q₀ = ((1 : Γ) : Γ ⧸ L) := by
      rw [hj₁, Quotient.eq, orbitRel_apply, mem_orbit_iff] at hq₀
      obtain ⟨e, he⟩ := hq₀
      rw [← he, Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
        QuotientGroup.eq]
      simpa using L.inv_mem (hEL e.2)
    ext q
    rw [mem_orbF, Finset.mem_singleton, hq₀']
    constructor
    · rintro ⟨e, he, rfl⟩
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
      simpa using L.inv_mem (hEL he)
    · rintro rfl
      exact ⟨1, E.one_mem, one_smul _ _⟩
  have horb : ∀ q₀ : Γ ⧸ L, Quotient.mk (orbitRel (↥E) (Γ ⧸ L)) q₀ ≠ j₁ →
      ∏ q ∈ orbF E q₀, F q = 1 := by
    intro q₀ hq₀
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q₀
    have hmove : ∃ a ∈ E₀, a • (x : Γ ⧸ L) ≠ (x : Γ ⧸ L) := by
      by_contra hcon
      push Not at hcon
      apply hq₀
      have hxL : x ∈ L := by
        refine hfixL x fun e he => ?_
        have hst : E ≤ stabilizer Γ (x : Γ ⧸ L) := by
          rw [hEdef, closure_le]
          intro a ha
          exact hcon a ha
        have := hst he
        rw [mem_stabilizer_iff, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at this
        simpa [mul_assoc] using L.inv_mem this
      rw [hj₁, Quotient.eq, orbitRel_apply, mem_orbit_iff]
      refine ⟨1, ?_⟩
      rw [one_smul, QuotientGroup.eq]
      simpa using hxL
    obtain ⟨a, haE₀, ha⟩ := hmove
    have haE : a ∈ E := subset_closure haE₀
    obtain ⟨ι, _, u, hT⟩ := tiles_of_isPGroup hEp (x : Γ ⧸ L) (zpowers a) (zpowers_le.mpr haE)
    rw [hT (Abelianization ↥L) F]
    refine Finset.prod_eq_one fun i _ => ?_
    set m := Function.minimalPeriod (a • ·) (x : Γ ⧸ L) with hm
    have haS : a ∈ (S : Subgroup Γ) := hE₀S haE₀
    obtain ⟨s, hs⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') ⟨a, haS⟩
    have hos : orderOf a = p ^ s := by
      rw [← Subgroup.orderOf_mk a haS]
      exact hs
    have hmdvd : m ∣ p ^ s := by
      rw [← hos]
      exact MulAction.pow_smul_eq_iff_minimalPeriod_dvd.mp (by rw [pow_orderOf_eq_one, one_smul])
    obtain ⟨r, -, hr⟩ := (Nat.dvd_prime_pow hp.out).mp hmdvd
    have hm1 : m ≠ 1 := by
      intro h1
      apply ha
      have := MulAction.pow_smul_eq_iff_minimalPeriod_dvd (a := a) (b := (x : Γ ⧸ L)) (n := 1)
      rw [pow_one] at this
      exact this.mpr (by rw [← hm, h1])
    have hr1 : 1 ≤ r := by
      rcases r with _ | r
      · exact absurd (by rw [hr, pow_zero]) hm1
      · omega
    have hm0 : 0 < m := by rw [hr]; exact pow_pos hp.out.pos r
    have himage : orbF (zpowers a) (x : Γ ⧸ L) =
        (Finset.range m).image fun k => a ^ k • (x : Γ ⧸ L) := by
      ext q
      rw [mem_orbF, Finset.mem_image]
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hz
        refine ⟨(n % (m : ℤ)).toNat, Finset.mem_range.mpr ?_, ?_⟩
        · have h1 := Int.emod_lt_of_pos n (by exact_mod_cast hm0 : (0 : ℤ) < m)
          have h2 := Int.emod_nonneg n (by exact_mod_cast hm0.ne' : (m : ℤ) ≠ 0)
          omega
        · rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg n
            (by exact_mod_cast hm0.ne' : (m : ℤ) ≠ 0)), hm, MulAction.zpow_smul_mod_minimalPeriod]
      · rintro ⟨k, -, rfl⟩
        exact ⟨a ^ k, pow_mem (mem_zpowers a) k, rfl⟩
    have hinj : Set.InjOn (fun k => a ^ k • (x : Γ ⧸ L)) ↑(Finset.range m) := by
      intro k₁ hk₁ k₂ hk₂ h
      have := Function.iterate_injOn_Iio_minimalPeriod (f := (a • ·)) (x := (x : Γ ⧸ L))
      refine this (by simpa using hk₁) (by simpa using hk₂) ?_
      simp only [smul_iterate_apply]
      exact h
    rw [himage, Finset.prod_image hinj]
    letI : CommGroup ↥Y :=
      { (inferInstance : Group ↥Y) with mul_comm := fun c d => Subtype.ext (hYc _ c.2 _ d.2) }
    have hconjY : ∀ (c : Γ), ∀ y ∈ Y, c⁻¹ * y * c ∈ Y := fun c y hy => by
      have := hYn.conj_mem y hy c⁻¹
      simpa using this
    let ψ : ↥Y →* Abelianization ↥L :=
      { toFun := fun y => ϕ ⟨x⁻¹ * y * x, hYL (hconjY x y y.2)⟩
        map_one' := by
          have : (⟨x⁻¹ * ((1 : ↥Y) : Γ) * x, hYL (hconjY x _ (1 : ↥Y).2)⟩ : ↥L) = 1 :=
            Subtype.ext (by simp)
          simp only [this, map_one]
        map_mul' := fun c d => by
          have : (⟨x⁻¹ * ((c * d : ↥Y) : Γ) * x, hYL (hconjY x _ (c * d : ↥Y).2)⟩ : ↥L) =
              ⟨x⁻¹ * (c : Γ) * x, hYL (hconjY x _ c.2)⟩ *
                ⟨x⁻¹ * (d : Γ) * x, hYL (hconjY x _ d.2)⟩ :=
            Subtype.ext (by simp only [Subgroup.coe_mul]; group)
          simp only [this, map_mul] }
    let α : ↥Y →* ↥Y :=
      { toFun := fun y => ⟨a * y * a⁻¹, by simpa using hconjY a⁻¹ y y.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun c d => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    let β : ↥Y →* ↥Y :=
      { toFun := fun y => ⟨a⁻¹ * y * a, hconjY a y y.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun c d => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    have hβk : ∀ (k : ℕ) (y : ↥Y), ((β^[k] y : ↥Y) : Γ) = (a ^ k)⁻¹ * y * a ^ k := by
      intro k
      induction k with
      | zero => intro y; simp
      | succ k ih =>
        intro y
        rw [Function.iterate_succ_apply', pow_succ]
        show a⁻¹ * ((β^[k] y : ↥Y) : Γ) * a = _
        rw [ih]
        group
    have hαk : ∀ (n : ℕ) (y : ↥Y),
        (((fun z => z * (α z)⁻¹)^[n] y : ↥Y) : Γ) = iterComm (y : Γ) a n := by
      intro n
      induction n with
      | zero => intro y; rfl
      | succ n ih =>
        intro y
        rw [Function.iterate_succ_apply', iterComm_succ, ← ih]
        show ((((fun z => z * (α z)⁻¹)^[n] y : ↥Y) : Γ) *
          (a * (((fun z => z * (α z)⁻¹)^[n] y : ↥Y) : Γ) * a⁻¹)⁻¹) = _
        simp only [commutatorElement_def]
        group
    set h : ↥Y := ⟨(u i)⁻¹ * g * u i, hconjY (u i) g hgY⟩ with hhdef
    have hterm : ∀ k, F (u i • (a ^ k • (x : Γ ⧸ L))) = ψ (β^[k] h) := by
      intro k
      rw [MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, hFrep]
      show ϕ _ = ϕ _
      congr 1
      apply Subtype.ext
      simp only [smul_eq_mul]
      rw [hβk]
      show _ = x⁻¹ * ((a ^ k)⁻¹ * ((u i)⁻¹ * g * u i) * a ^ k) * x
      group
    simp only [hterm]
    rw [← map_prod, hr]
    rw [prod_iterate_eq_one p (fun y => Subtype.ext (by
        simpa using hYp y y.2)) α β
      (fun y => Subtype.ext (by show a * (a⁻¹ * (y : Γ) * a) * a⁻¹ = y; group))
      (fun y => Subtype.ext (by show a⁻¹ * (a * (y : Γ) * a⁻¹) * a = y; group))
      (fun y => Subtype.ext (by rw [hαk]; exact hnil a haE₀ y y.2)) hr1 h, map_one]
  have hmain : ϕ.transfer g = ϕ ⟨g, hYL hgY⟩ := by
    rw [hVF, hprod, Finset.prod_eq_single j₁]
    · rw [horb1 _ (Quotient.out_eq _), Finset.prod_singleton, hFrep]
      congr 1
      apply Subtype.ext
      simp
    · intro j _ hj
      exact horb _ (by rw [Quotient.out_eq]; exact hj)
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hV1] at hmain
  have hker : (⟨g, hYL hgY⟩ : ↥L) ∈ commutator ↥L := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact hmain.symm
  rw [← map_subtype_commutator]
  exact ⟨_, hker, rfl⟩

end Wielandt

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB

end
