module

public import CFSG.LieType.OutStructureFixedRank
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinearLang
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.LieType.OutStructureHInputLinear
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveSylow
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenPClosed

public section

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Diagonal

variable {K : Type} [Field K] [Finite K]

private theorem exists_pow_eq_of_pow_eq {n p : ℕ} (hp : p.Prime)
    (hdiv : ¬ p ∣ Nat.gcd n (Nat.card K - 1)) {x lam : Kˣ} (h : x ^ p = lam ^ n) :
    ∃ c : Kˣ, c ^ n = x := by
  classical
  have : Fintype K := Fintype.ofFinite K
  by_cases hpn : p ∣ n
  ·
    have hpq : ¬ p ∣ Nat.card K - 1 := fun h' => hdiv (Nat.dvd_gcd hpn h')
    have hcardU : Nat.card Kˣ = Nat.card K - 1 := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
    have hcop : (Nat.card Kˣ).Coprime p := by
      rw [hcardU]
      exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq))
    refine ⟨lam ^ (Nat.card Kˣ).gcdB p, ?_⟩
    have hx : x = (powCoprime hcop).symm (x ^ p) := by
      rw [← powCoprime_apply hcop, Equiv.symm_apply_apply]
    rw [hx, h, powCoprime_symm_apply, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
      mul_comm]
  ·
    have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpn
    have hcomm : ∀ (y : Kˣ) (a : ℤ), (y ^ a) ^ n = (y ^ n) ^ a := fun y a => by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    have key : x = (x ^ p) ^ p.gcdA n * (x ^ n) ^ p.gcdB n := by
      have h1 := congrArg (fun k : ℤ => x ^ k) (Nat.gcd_eq_gcd_ab p n)
      simp only [hcop.gcd_eq_one, Nat.cast_one, zpow_one] at h1
      exact h1.trans (by rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast])
    refine ⟨lam ^ p.gcdA n * x ^ p.gcdB n, ?_⟩
    calc (lam ^ p.gcdA n * x ^ p.gcdB n) ^ n
        = (lam ^ n) ^ p.gcdA n * (x ^ n) ^ p.gcdB n := by rw [mul_pow, hcomm, hcomm]
      _ = (x ^ p) ^ p.gcdA n * (x ^ n) ^ p.gcdB n := by rw [h]
      _ = x := key.symm

theorem conjAut_mem_inner_of_pow_eq_one {n p : ℕ} (hn : 2 ≤ n)
    (hpar : 3 ≤ n ∨ 4 ≤ Nat.card K) (hp : p.Prime)
    (hdiv : ¬ p ∣ Nat.gcd n (Nat.card K - 1)) (A : GL (Fin n) K)
    (h : conjAut n K A ^ p = 1) : conjAut n K A ∈ inner (projectiveSL n K) := by
  have h1 : conjAut n K (A ^ p) * fieldAut n K 1 = 1 := by
    rw [map_one, mul_one, map_pow, h]
  obtain ⟨-, lam, hlam⟩ :=
    CFSG.StandardType.RecipeFieldLinear.eq_one_of_conjAut_mul_fieldAut_eq_one' hn hpar (A ^ p) 1 h1
  have hdetp : (Matrix.GeneralLinearGroup.det A) ^ p = lam ^ n := by
    rw [← map_pow, ← hlam, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
  obtain ⟨c, hc⟩ := exists_pow_eq_of_pow_eq hp hdiv hdetp
  exact conjAut_mem_range_conj_of_det_eq_pow hc.symm

end Diagonal

section Rank

variable {K : Type} [Field K] [Finite K]

theorem pRank_autFixedSubgroup_eq_of_pow_eq_one {n p : ℕ} (hn : 3 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K) (hdiv : ¬ p ∣ Nat.gcd n (Nat.card K - 1))
    (α : MulAut (projectiveSL n K)) (hα : α ^ p = 1)
    (hout : α ∉ inner (projectiveSL n K)) :
    CFSG.Open.pRank p (CFSG.autFixedSubgroup α) =
      CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL n K)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, σ, rfl⟩ :=
    mem_semilinearAutGroup_iff.mp (mem_semilinearAutGroup_of_pow_odd hn (hp.odd_of_ne_two hp2) hα)
  by_cases hσ : σ = 1
  · subst hσ
    rw [map_one, mul_one] at hα hout
    exact absurd (conjAut_mem_inner_of_pow_eq_one (by omega) (Or.inl hn) hp hdiv A hα) hout
  obtain ⟨hord, H, hH⟩ :=
    CFSG.StandardType.RecipeFieldLang.lang_field_linear (by omega) (Or.inl hn) hp A σ hσ hα
  have hσp : σ ^ p = 1 := by
    have h1 : conjAut n K 1 * fieldAut n K (σ ^ p) = 1 := by
      rw [map_one, one_mul, map_pow, ← hord, pow_orderOf_eq_one]
    exact (CFSG.StandardType.RecipeFieldLinear.eq_one_of_conjAut_mul_fieldAut_eq_one' (by omega)
      (Or.inl hn) 1 (σ ^ p) h1).1
  have hσord : orderOf σ = p := orderOf_eq_prime hσp hσ
  have hc : MulAut.congr (conjAut n K H) (fieldAut n K σ) =
      conjAut n K A * fieldAut n K σ := by
    rw [hH]
    ext z
    simp [MulAut.congr]
  rw [← hc, ← pRank_autFixedSubgroup_congr hp.one_lt (conjAut n K H) (fieldAut n K σ)]
  exact pRank_autFixedSubgroup_eq σ hσord hp hp2 (by omega) hpK hdiv

end Rank

section HInput

variable {X : Type*} [Group X] [Finite X] {L : Subgroup X} [L.Normal] {p : ℕ}

omit [Finite X] in
theorem not_mem_inner_congr_conjHom (hL : CFSG.IsComponent L) {K : Type} [Field K] [Finite K]
    {m : ℕ} (e : (↥L ⧸ Subgroup.center ↥L) ≃* projectiveSL m K) {x : X}
    (hxU : x ∉ L ⊔ Subgroup.centralizer (L : Set X)) :
    MulAut.congr e (conjHom (L := L) x) ∉ inner (projectiveSL m K) := by
  rintro ⟨z, hz⟩
  apply hxU
  rw [← mem_ker_conjOuterHom_iff hL, conjOuterHom_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  refine ⟨e.symm z, ?_⟩
  apply (MulAut.congr e).injective
  rw [← hz]
  ext w
  simp [MulAut.congr]

theorem hInput_linear_of_exists_of_cross (hL : CFSG.IsComponent L) {K : Type} [Field K]
    [Finite K] {m : ℕ} (e : (↥L ⧸ Subgroup.center ↥L) ≃* projectiveSL m K) (hm : 3 ≤ m)
    (hp : p.Prime) (hp2 : p ≠ 2) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    (hpK : ¬ p ∣ Nat.card K) (hdiv : ¬ p ∣ Nat.gcd m (Nat.card K - 1))
    (hExists : ¬ CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
        (L ⊔ Subgroup.centralizer (L : Set X)) →
      ¬ (∃ c : X, c ∈ Subgroup.centralizer (L : Set X) ∧ orderOf c = p) →
      ∃ x : X, orderOf x = p ∧ x ∉ L ⊔ Subgroup.centralizer (L : Set X)) :
    ¬ CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
        (L ⊔ Subgroup.centralizer (L : Set X)) →
      (∃ c : X, c ∈ Subgroup.centralizer (L : Set X) ∧ orderOf c = p) ∨
      ∃ x : X, orderOf x = p ∧
        x ∉ L ⊔ Subgroup.centralizer (L : Set X) ∧
        ∃ E : Subgroup X, E ≤ L ∧ CFSG.Open.IsElemAbelian p E ∧
          Nat.card E = p ^ CFSG.Open.pRank p L ∧ ∀ a ∈ E, a * x = x * a := by
  intro hnot
  by_cases hc : ∃ c : X, c ∈ Subgroup.centralizer (L : Set X) ∧ orderOf c = p
  · exact Or.inl hc
  · obtain ⟨x, hxord, hxU⟩ := hExists hnot hc
    refine Or.inr ⟨x, hxord, hxU, ?_⟩
    have : Fact p.Prime := ⟨hp⟩
    let Z : Subgroup ↥L := Subgroup.center ↥L
    let S := ↥L ⧸ Z
    let α : MulAut ↥L := MulAut.conjNormal (H := L) x
    let a : MulAut S := conjHom (L := L) x
    have hxpow : x ^ p = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
    have hαp : α ^ p = 1 := by
      change MulAut.conjNormal (H := L) x ^ p = 1
      rw [← map_pow, hxpow, map_one]
    have haq : CFSG.quotientAut α = a := quotientAut_conjNormal_eq_conjHom x
    have hRankS : CFSG.Open.pRank p (CFSG.autFixedSubgroup a) =
        CFSG.Open.pRank p (⊤ : Subgroup S) := by
      have h1 : CFSG.Open.pRank p (CFSG.autFixedSubgroup a) =
          CFSG.Open.pRank p (CFSG.autFixedSubgroup (MulAut.congr e a)) :=
        pRank_autFixedSubgroup_congr hp.one_lt e a
      have h2 : CFSG.Open.pRank p (CFSG.autFixedSubgroup (MulAut.congr e a)) =
          CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL m K)) :=
        pRank_autFixedSubgroup_eq_of_pow_eq_one hm hp hp2 hpK hdiv _
          (by rw [← map_pow, ← map_pow, ← hxord, pow_orderOf_eq_one, map_one, map_one])
          (not_mem_inner_congr_conjHom hL e hxU)
      have h3 : CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL m K)) =
          CFSG.Open.pRank p (⊤ : Subgroup S) :=
        (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e).symm
      exact h1.trans (h2.trans h3)
    have hSrank : CFSG.Open.pRank p (⊤ : Subgroup S) = CFSG.Open.pRank p L := by
      calc CFSG.Open.pRank p (⊤ : Subgroup S)
          = CFSG.pRank p S := (CFSG.SectionRank.pRank_eq_open_pRank_top p S).symm
        _ = CFSG.pRank p ↥L :=
            CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp Z hZ
        _ = CFSG.Open.pRank p (⊤ : Subgroup ↥L) :=
            CFSG.SectionRank.pRank_eq_open_pRank_top p ↥L
        _ = CFSG.Open.pRank p L := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup L).symm
    obtain ⟨E₀, hE₀le, hE₀e, hE₀card⟩ :=
      CFSG.SectionRank.exists_pRank hp.one_lt (CFSG.autFixedSubgroup a)
    have hE₀card' : Nat.card E₀ = p ^ CFSG.Open.pRank p L := by
      rw [hE₀card, hRankS, hSrank]
    have hfix : CFSG.autFixedSubgroup a =
        (CFSG.autFixedSubgroup α).map (QuotientGroup.mk' Z) := by
      rw [← haq]
      exact autFixedSubgroup_quotientAut_eq_map hp α hαp hZ
    let C : Subgroup ↥L := CFSG.autFixedSubgroup α
    let ψ : ↥C →* S := (QuotientGroup.mk' Z).comp C.subtype
    have hrange : E₀ ≤ ψ.range := by
      rw [show ψ.range = C.map (QuotientGroup.mk' Z) from
        (MonoidHom.range_comp _ _).trans (by rw [Subgroup.range_subtype])]
      rw [← hfix]
      exact hE₀le
    have hker : ψ.ker = Z.subgroupOf C := by
      ext y
      exact (QuotientGroup.eq_one_iff (C.subtype y)).trans Subgroup.mem_subgroupOf.symm
    have hkerdvd : Nat.card ↥ψ.ker ∣ Nat.card ↥Z := by
      have hcard : Nat.card ↥ψ.ker = Nat.card ↥(Z ⊓ C) := by
        rw [hker, ← Subgroup.inf_subgroupOf_right Z C]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Z ⊓ C ≤ C)).toEquiv
      rw [hcard]
      exact Subgroup.card_dvd_of_le (inf_le_left : Z ⊓ C ≤ Z)
    have hkerp : ¬ p ∣ Nat.card ↥ψ.ker := fun h => hZ (h.trans hkerdvd)
    obtain ⟨E', hE'e, hE'map, hE'card⟩ :=
      CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.exists_lift_of_le_range ψ hkerp hrange hE₀e
    have hinj : Function.Injective (L.subtype.comp C.subtype) := by
      intro y₁ y₂ h
      exact Subtype.ext (Subtype.ext h)
    refine ⟨E'.map (L.subtype.comp C.subtype), ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨y, -, rfl⟩
      exact (C.subtype y).2
    · exact hE'e.map (L.subtype.comp C.subtype)
    · rw [Subgroup.card_map_of_injective hinj, hE'card, hE₀card']
    · intro y hy
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
      have hyC : α y' = y' := CFSG.mem_autFixedSubgroup.mp y'.2
      have hconj : x * (y' : X) * x⁻¹ = (y' : X) := by
        have h := congrArg Subtype.val hyC
        simpa [α, MulAut.conjNormal_apply] using h
      have hcomm : x * (y' : X) = (y' : X) * x := by
        calc x * (y' : X) = (x * (y' : X) * x⁻¹) * x := by group
          _ = (y' : X) * x := by rw [hconj]
      exact hcomm.symm

end HInput

end CFSG.LieType.OutStructure
