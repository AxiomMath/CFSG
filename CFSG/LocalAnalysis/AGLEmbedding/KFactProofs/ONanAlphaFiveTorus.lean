module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaFiveLift
public import CFSG.RankThree.Classical2.UnitarySplitPrimeRank

public section

namespace CFSG.AGLEmbedding.KFactProofs.AlphaFive

open CFSG.RankThree.Classical2 CFSG.RankThree.Classical CFSG.SectionRank.OddCover
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec4.Census

section Matrices

variable {F : Type} [Field F] {n : ℕ}

@[expose] def dlt (ζ : Fˣ) (a c : Fin n) : Fin n → Fˣ :=
  fun i => (if i = a then ζ else 1) * (if i = c then ζ⁻¹ else 1)

theorem dlt_pow {ζ : Fˣ} {p : ℕ} (hζ : ζ ^ p = 1) (a c i : Fin n) : dlt ζ a c i ^ p = 1 := by
  unfold dlt
  rw [mul_pow]
  split_ifs <;> simp [hζ]

theorem prod_dlt (ζ : Fˣ) (a c : Fin n) : ∏ i, dlt ζ a c i = 1 := by
  unfold dlt
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
  simp

theorem dlt_comp_swap_self (ζ : Fˣ) {a c : Fin n} (hac : a ≠ c) :
    dlt ζ a c ∘ Equiv.swap a c = (dlt ζ a c)⁻¹ := by
  funext i
  simp only [Function.comp_apply, Pi.inv_apply, dlt]
  by_cases hia : i = a
  · subst hia
    rw [Equiv.swap_apply_left]
    simp [hac, hac.symm]
  · by_cases hic : i = c
    · subst hic
      rw [Equiv.swap_apply_right]
      simp [hac, hac.symm]
    · rw [Equiv.swap_apply_of_ne_of_ne hia hic]
      simp [hia, hic]

theorem dlt_comp_swap (ζ : Fˣ) {a b c : Fin n} (hac : a ≠ c) (hbc : b ≠ c) :
    dlt ζ a c ∘ Equiv.swap a b = dlt ζ b c := by
  funext i
  simp only [Function.comp_apply, dlt]
  by_cases hia : i = a
  · subst hia
    by_cases hib : i = b
    · subst hib
      simp
    · rw [Equiv.swap_apply_left]
      simp [hib, hac, hbc, Ne.symm hib]
  · by_cases hib : i = b
    · subst hib
      rw [Equiv.swap_apply_right]
      simp [hac, hbc]
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
      simp [hia, hib]

theorem dlt_split (ζ : Fˣ) (a c c₀ : Fin n) :
    dlt ζ a c = dlt ζ a c₀ * (dlt ζ c c₀)⁻¹ := by
  funext i
  simp only [dlt, Pi.mul_apply, Pi.inv_apply]
  split_ifs <;> simp [mul_comm]

variable (F) in
@[expose] noncomputable def sw (a c : Fin n) : GL (Fin n) F :=
  permGL (Equiv.swap a c) * diagHom n (Function.update 1 c (-1))

theorem sw_conj_diagHom (a c : Fin n) (e : Fin n → Fˣ) :
    sw F a c * diagHom n e * (sw F a c)⁻¹ = diagHom n (e ∘ Equiv.swap a c) := by
  unfold sw
  have h := permGL_mul_diagHom_mul_inv (K := F) (Equiv.swap a c) e
  rw [Equiv.symm_swap] at h
  rw [← h]
  have hcomm := (diagHom_commute (K := F) (Function.update (1 : Fin n → Fˣ) c (-1)) e).eq
  calc permGL (Equiv.swap a c) * diagHom n (Function.update 1 c (-1)) * diagHom n e *
        (permGL (Equiv.swap a c) * diagHom n (Function.update 1 c (-1)))⁻¹ =
      permGL (Equiv.swap a c) * (diagHom n (Function.update 1 c (-1)) * diagHom n e) *
        (diagHom n (Function.update 1 c (-1)))⁻¹ * (permGL (Equiv.swap a c))⁻¹ := by group
    _ = permGL (Equiv.swap a c) * (diagHom n e * diagHom n (Function.update 1 c (-1))) *
        (diagHom n (Function.update 1 c (-1)))⁻¹ * (permGL (Equiv.swap a c))⁻¹ := by rw [hcomm]
    _ = permGL (Equiv.swap a c) * diagHom n e * (permGL (Equiv.swap a c))⁻¹ := by group

end Matrices

section Torus

variable {F : Type} [Field F] {n : ℕ}

structure TorusHyp (H : Subgroup (GL (Fin n) F)) (p : ℕ) (ζ : Fˣ) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  orderOf_eq : orderOf ζ = p
  four_le : 4 ≤ n
  diag_mem : ∀ d : Fin n → Fˣ, ∏ i, d i = 1 → (∀ i, d i ^ p = 1) → diagHom n d ∈ H
  sw_mem : ∀ a c : Fin n, a ≠ c → sw F a c ∈ H

variable {H : Subgroup (GL (Fin n) F)} {p : ℕ} {ζ : Fˣ}

theorem TorusHyp.zeta_pow (h : TorusHyp H p ζ) : ζ ^ p = 1 := by
  rw [← h.orderOf_eq]
  exact pow_orderOf_eq_one ζ

noncomputable abbrev projH (H : Subgroup (GL (Fin n) F)) : H →* StatedProj H :=
  QuotientGroup.mk' _

theorem scalar_of_projH_eq_one {s : H} (hs : projH H s = 1) :
    ∃ r : Fˣ, (s : GL (Fin n) F) = Matrix.GeneralLinearGroup.scalar (Fin n) r := by
  have := (QuotientGroup.eq_one_iff s).mp hs
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at this
  obtain ⟨r, hr⟩ := this
  exact ⟨r, hr.symm⟩

theorem scalar_eq_diagHom (r : Fˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin n) r = diagHom n (fun _ => r) := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.coe_scalar, coe_diagHom, Matrix.scalar_apply]

theorem projH_conj_eq {x y z : H}
    (hxyz : (x : GL (Fin n) F) * (y : GL (Fin n) F) * (x : GL (Fin n) F)⁻¹ = z) :
    projH H x * projH H y * (projH H x)⁻¹ = projH H z := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simpa using hxyz

section Family

variable [NeZero p]

theorem diagHom_expHom_mem (h : TorusHyp H p ζ) {J : Type} [Fintype J] (c : J → Fin n → Fˣ)
    (hc : ∀ j i, c j i ^ p = 1) (hprod : ∀ j, ∏ i, c j i = 1)
    (v : Multiplicative (J → ZMod p)) : diagHom n (expHom c hc v) ∈ H := by
  refine h.diag_mem _ ?_ fun i => ?_
  · simp only [expHom_apply]
    rw [Finset.prod_comm]
    simp_rw [Finset.prod_pow, hprod, one_pow, Finset.prod_const_one]
  · rw [expHom_apply, ← Finset.prod_pow]
    simp_rw [← pow_mul, mul_comm _ p, pow_mul, hc, one_pow, Finset.prod_const_one]

@[expose] noncomputable def famHom (h : TorusHyp H p ζ) {J : Type} [Fintype J]
    (c : J → Fin n → Fˣ) (hc : ∀ j i, c j i ^ p = 1) (hprod : ∀ j, ∏ i, c j i = 1) :
    Multiplicative (J → ZMod p) →* StatedProj H :=
  (projH H).comp (((diagHom n).comp (expHom c hc)).codRestrict H
    (diagHom_expHom_mem h c hc hprod))

theorem famHom_single (h : TorusHyp H p ζ) {J : Type} [Fintype J] [DecidableEq J]
    (c : J → Fin n → Fˣ) (hc : ∀ j i, c j i ^ p = 1) (hprod : ∀ j, ∏ i, c j i = 1) (j : J) :
    famHom h c hc hprod (Multiplicative.ofAdd (Pi.single j 1)) =
      projH H ⟨diagHom n (c j), h.diag_mem _ (hprod j) (hc j)⟩ := by
  have : Fact (1 < p) := ⟨h.prime.one_lt⟩
  have h1 : expHom c hc (Multiplicative.ofAdd (Pi.single j 1)) = c j := expHom_single c hc j
  unfold famHom
  rw [MonoidHom.comp_apply]
  congr 1
  apply Subtype.ext
  show diagHom n (expHom c hc (Multiplicative.ofAdd (Pi.single j 1))) = diagHom n (c j)
  rw [h1]

theorem famHom_injective (h : TorusHyp H p ζ) {J : Type} [Fintype J] [DecidableEq J]
    (c : J → Fin n → Fˣ) (hc : ∀ j i, c j i ^ p = 1) (hprod : ∀ j, ∏ i, c j i = 1)
    (hpriv : ∀ j, ∃ i, (∀ j', j' ≠ j → c j' i = 1) ∧ orderOf (c j i) = p) (d : Fin n)
    (hd : ∀ j, c j d = 1) : Function.Injective (famHom h c hc hprod) := by
  have : Fact p.Prime := ⟨h.prime⟩
  refine (injective_iff_map_eq_one _).mpr fun v hv => ?_
  obtain ⟨r, hr⟩ := scalar_of_projH_eq_one (s := ⟨diagHom n (expHom c hc v),
    diagHom_expHom_mem h c hc hprod v⟩) hv
  have h1 : expHom c hc v = fun _ => r := by
    apply diagHom_injective n
    rw [← scalar_eq_diagHom]
    exact hr
  have h2 : r = 1 := by
    have := congrFun h1 d
    rw [expHom_apply] at this
    simpa [hd] using this.symm
  rw [h2] at h1
  exact expHom_injective c hc hpriv (h1.trans (map_one _).symm)

end Family

section Cover

variable [NeZero p] {K : Type} [Group K] {φ : K →* StatedProj H}

@[expose] noncomputable def torus0 (h : TorusHyp H p ζ) (c₀ : Fin n) :
    Multiplicative (Fin n → ZMod p) →* StatedProj H :=
  famHom h (fun a => dlt ζ a c₀) (fun a i => dlt_pow h.zeta_pow a c₀ i)
    (fun a => prod_dlt ζ a c₀)

theorem dlt_self (ζ : Fˣ) (c : Fin n) : dlt ζ c c = 1 := by
  funext i
  simp only [dlt, Pi.one_apply]
  split_ifs <;> simp

theorem torus0_comm (h : TorusHyp H p ζ) (c₀ : Fin n) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center K) :
    ∀ x ∈ (torus0 h c₀).range.comap φ, ∀ y ∈ (torus0 h c₀).range.comap φ, x * y = y * x := by
  intro x hx y hy
  have hodd : Odd p := h.prime.odd_of_ne_two h.ne_two
  have : Fact (1 < p) := ⟨h.prime.one_lt⟩
  set θ0 := torus0 h c₀ with hθ0
  set g0 : Fin n → StatedProj H := fun a => θ0 (Multiplicative.ofAdd (Pi.single a 1)) with hg0
  have hcl : Subgroup.closure (Set.range g0) = θ0.range := closure_range_basis θ0
  have hgs : ∀ a, g0 a = projH H ⟨diagHom n (dlt ζ a c₀), h.diag_mem _ (prod_dlt ζ a c₀)
      (fun i => dlt_pow h.zeta_pow a c₀ i)⟩ := fun a => famHom_single h _ _ _ a
  have hone : g0 c₀ = 1 := by
    rw [hgs]
    have : (⟨diagHom n (dlt ζ c₀ c₀), h.diag_mem _ (prod_dlt ζ c₀ c₀)
        (fun i => dlt_pow h.zeta_pow c₀ c₀ i)⟩ : H) = 1 :=
      Subtype.ext (by simp [dlt_self])
    rw [this, map_one]
  refine TripleCoverLift.commute_of_mem_closure hφ hker (S := Set.range g0) ?_ ?_ ?_
  · rintro x y ⟨a, ha⟩ ⟨b, hb⟩ hne
    by_cases hac : a = c₀
    · have hxk : x ∈ φ.ker := MonoidHom.mem_ker.mpr (by rw [← ha, hac]; exact hone)
      exact (Subgroup.mem_center_iff.mp (hker hxk) y).symm
    by_cases hbc : b = c₀
    · have hyk : y ∈ φ.ker := MonoidHom.mem_ker.mpr (by rw [← hb, hbc]; exact hone)
      exact Subgroup.mem_center_iff.mp (hker hyk) x
    have hab : a ≠ b := fun e => hne (by rw [← ha, ← hb, e])
    have hw1 : projH H ⟨sw F a b, h.sw_mem a b hab⟩ * g0 a *
        (projH H ⟨sw F a b, h.sw_mem a b hab⟩)⁻¹ = g0 b := by
      rw [hgs a, hgs b]
      refine projH_conj_eq ?_
      show sw F a b * diagHom n (dlt ζ a c₀) * (sw F a b)⁻¹ = diagHom n (dlt ζ b c₀)
      rw [sw_conj_diagHom, dlt_comp_swap ζ hac hbc]
    have hw2 : projH H ⟨sw F a b, h.sw_mem a b hab⟩ * g0 b *
        (projH H ⟨sw F a b, h.sw_mem a b hab⟩)⁻¹ = g0 a := by
      rw [hgs a, hgs b]
      refine projH_conj_eq ?_
      show sw F a b * diagHom n (dlt ζ b c₀) * (sw F a b)⁻¹ = diagHom n (dlt ζ a c₀)
      rw [sw_conj_diagHom, ← Equiv.swap_comm, dlt_comp_swap ζ hbc hac]
    refine TripleCoverLift.commute_of_conj hφ hker hodd (x := x) (y := y)
      (n := projH H ⟨sw F a b, h.sw_mem a b hab⟩) ?_ ?_ (Or.inr ⟨?_, ?_⟩)
    · rw [← ha, ← hb]
      exact (Commute.all _ _).map θ0
    · rw [← hb, hg0]
      simp only
      rw [← map_pow, pow_eq_one_zmod, map_one]
    · rw [← ha, ← hb]
      exact hw1
    · rw [← ha, ← hb]
      exact hw2
  · rw [hcl]
    exact hx
  · rw [hcl]
    exact hy

@[expose] noncomputable def dH (h : TorusHyp H p ζ) (a c : Fin n) : H :=
  ⟨diagHom n (dlt ζ a c), h.diag_mem _ (prod_dlt ζ a c) (fun i => dlt_pow h.zeta_pow a c i)⟩

theorem torus0_single (h : TorusHyp H p ζ) (c₀ a : Fin n) :
    torus0 h c₀ (Multiplicative.ofAdd (Pi.single a 1)) = projH H (dH h a c₀) :=
  famHom_single h _ _ _ a

theorem projH_dH_mem_torus0 (h : TorusHyp H p ζ) (c₀ a c : Fin n) :
    projH H (dH h a c) ∈ (torus0 h c₀).range := by
  have hsplit : dH h a c = dH h a c₀ * (dH h c c₀)⁻¹ := by
    apply Subtype.ext
    show diagHom n (dlt ζ a c) = diagHom n (dlt ζ a c₀) * (diagHom n (dlt ζ c c₀))⁻¹
    rw [dlt_split ζ a c c₀, map_mul, map_inv]
  rw [hsplit, map_mul, map_inv]
  refine (torus0 h c₀).range.mul_mem ?_ ((torus0 h c₀).range.inv_mem ?_)
  · exact ⟨Multiplicative.ofAdd (Pi.single a 1), torus0_single h c₀ a⟩
  · exact ⟨Multiplicative.ofAdd (Pi.single c 1), torus0_single h c₀ c⟩

@[expose] def tripleFam (ζ : Fˣ) (a b c : Fin n) : Fin 2 → Fin n → Fˣ :=
  ![dlt ζ a c, dlt ζ b c]

@[expose] noncomputable def tripleHom (h : TorusHyp H p ζ) (a b c : Fin n) :
    Multiplicative (Fin 2 → ZMod p) →* StatedProj H :=
  famHom h (tripleFam ζ a b c)
    (fun j i => by
      fin_cases j
      · exact dlt_pow h.zeta_pow a c i
      · exact dlt_pow h.zeta_pow b c i)
    (fun j => by
      fin_cases j
      · exact prod_dlt ζ a c
      · exact prod_dlt ζ b c)

theorem dlt_apply_left (ζ : Fˣ) {a c : Fin n} (hac : a ≠ c) : dlt ζ a c a = ζ := by
  simp [dlt, hac]

theorem dlt_apply_other (ζ : Fˣ) {a c i : Fin n} (hia : i ≠ a) (hic : i ≠ c) :
    dlt ζ a c i = 1 := by
  simp [dlt, hia, hic]

theorem exists_fourth {a b c : Fin n} (hn : 4 ≤ n) : ∃ d : Fin n, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b, c} := by
    intro d _
    by_cases hda : d = a
    · simp [hda]
    by_cases hdb : d = b
    · simp [hdb]
    have := hcon d hda hdb
    simp [this]
  have h1 := Finset.card_le_card hsub
  have h2 : ({a, b, c} : Finset (Fin n)).card ≤ 3 := Finset.card_le_three
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem exists_triple_subgroup [Finite K] (h : TorusHyp H p ζ) (c₀ : Fin n)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center K) {z : K} (hz : z ∈ φ.ker)
    (hz1 : z ≠ 1) (hzp : z ^ p = 1) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ Q : Subgroup K, Q ≤ TripleCoverLift.powOneSubgroup φ (torus0 h c₀).range p
        (torus0_comm h c₀ hφ hker) ∧ Open.IsElemAbelian p Q ∧ p ^ 3 ≤ Nat.card Q ∧
      ∀ g : K, ∀ s : H, Commute (s : GL (Fin n) F) (diagHom n (dlt ζ a c)) →
        Commute (s : GL (Fin n) F) (diagHom n (dlt ζ b c)) → φ g = projH H s →
          g ∈ Subgroup.normalizer (Q : Set K) := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨d, hda, hdb, hdc⟩ := exists_fourth (a := a) (b := b) (c := c) h.four_le
  set θ := tripleHom h a b c with hθ
  have hθ0 : θ (Multiplicative.ofAdd (Pi.single 0 1)) = projH H (dH h a c) :=
    famHom_single h _ _ _ 0
  have hθ1 : θ (Multiplicative.ofAdd (Pi.single 1 1)) = projH H (dH h b c) :=
    famHom_single h _ _ _ 1
  have hθinj : Function.Injective θ := by
    refine famHom_injective h _ _ _ ?_ d ?_
    · intro j
      fin_cases j
      · refine ⟨a, ?_, ?_⟩
        · intro j' hj'
          fin_cases j'
          · exact absurd rfl hj'
          · exact dlt_apply_other ζ hab hac
        · show orderOf (dlt ζ a c a) = p
          rw [dlt_apply_left ζ hac, h.orderOf_eq]
      · refine ⟨b, ?_, ?_⟩
        · intro j' hj'
          fin_cases j'
          · exact dlt_apply_other ζ (Ne.symm hab) hbc
          · exact absurd rfl hj'
        · show orderOf (dlt ζ b c b) = p
          rw [dlt_apply_left ζ hbc, h.orderOf_eq]
    · intro j
      fin_cases j
      · exact dlt_apply_other ζ hda hdc
      · exact dlt_apply_other ζ hdb hdc
  have hinv : ∀ j : Fin 2, ∃ w : StatedProj H, w * θ (Multiplicative.ofAdd (Pi.single j 1)) *
      w⁻¹ = (θ (Multiplicative.ofAdd (Pi.single j 1)))⁻¹ := by
    rw [Fin.forall_fin_two]
    refine ⟨⟨projH H ⟨sw F a c, h.sw_mem a c hac⟩, ?_⟩, ⟨projH H ⟨sw F b c, h.sw_mem b c hbc⟩, ?_⟩⟩
    · rw [hθ0, ← map_inv]
      refine projH_conj_eq ?_
      show sw F a c * diagHom n (dlt ζ a c) * (sw F a c)⁻¹ = (diagHom n (dlt ζ a c))⁻¹
      rw [sw_conj_diagHom, dlt_comp_swap_self ζ hac, map_inv]
    · rw [hθ1, ← map_inv]
      refine projH_conj_eq ?_
      show sw F b c * diagHom n (dlt ζ b c) * (sw F b c)⁻¹ = (diagHom n (dlt ζ b c))⁻¹
      rw [sw_conj_diagHom, dlt_comp_swap_self ζ hbc, map_inv]
  have hDθ : θ.range ≤ (torus0 h c₀).range := by
    refine range_le_of_basis θ ?_
    rw [Fin.forall_fin_two]
    exact ⟨by rw [hθ0]; exact projH_dH_mem_torus0 h c₀ a c,
      by rw [hθ1]; exact projH_dH_mem_torus0 h c₀ b c⟩
  obtain ⟨Q, hQD, hQe, hQc, hQn⟩ := exists_lift_subgroup hφ hker h.prime h.ne_two hz hz1 hzp θ
    hθinj hinv hDθ (torus0_comm h c₀ hφ hker)
  refine ⟨Q, hQD, hQe, hQc, ?_⟩
  intro g s hs1 hs2 hgs
  refine hQn g ?_
  have hcen : θ.range ≤ Subgroup.centralizer {φ g} := by
    refine range_le_of_basis θ ?_
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [hθ0, Subgroup.mem_centralizer_singleton_iff, hgs]
      have : s * dH h a c = dH h a c * s := Subtype.ext hs1.eq
      rw [← map_mul, ← map_mul, this]
    · rw [hθ1, Subgroup.mem_centralizer_singleton_iff, hgs]
      have : s * dH h b c = dH h b c * s := Subtype.ext hs2.eq
      rw [← map_mul, ← map_mul, this]
  exact fun e he => (Subgroup.mem_centralizer_singleton_iff.mp (hcen he)).symm

theorem glbCore_eq_top_of_torus [Finite K] (h : TorusHyp H p ζ)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center K) (hperf : commutator K = ⊤)
    {z : K} (hz : z ∈ φ.ker) (hz1 : z ≠ 1) (hzp : z ^ p = 1)
    (hgen : H ≤ Subgroup.closure {A : GL (Fin n) F | A ∈ H ∧ ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧
      b ≠ c ∧ Commute A (diagHom n (dlt ζ a c)) ∧ Commute A (diagHom n (dlt ζ b c))})
    (T : Sylow p K) :
    Open.GLBCore p 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank p (⊤ : Subgroup K) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hn4 := h.four_le
  let c₀ : Fin n := ⟨0, by omega⟩
  let ι := {t : Fin n × Fin n × Fin n // t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
  choose Q hQP hQe hQc hQn using fun t : ι => exists_triple_subgroup h c₀ hφ hker hz hz1 hzp
    t.2.1 t.2.2.1 t.2.2.2
  have hQp : ∀ t, IsPGroup p (Q t) := fun t x =>
    ⟨1, Subtype.ext (by simpa using (hQe t).2 x x.2)⟩
  have hQr : ∀ t, 3 ≤ Open.pRank p (Q t) := by
    intro t
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hQp t)
    have h3 : 3 ≤ k := by
      have := hQc t
      rw [hk] at this
      exact (Nat.pow_le_pow_iff_right h.prime.one_lt).mp this
    exact h3.trans (CFSG.SectionRank.le_pRank h.prime.one_lt le_rfl (hQe t) hk)
  have hP : IsPGroup p (TripleCoverLift.powOneSubgroup φ (torus0 h c₀).range p
      (torus0_comm h c₀ hφ hker)) := fun x =>
    ⟨1, Subtype.ext (by simpa using (TripleCoverLift.mem_powOneSubgroup.mp x.2).2)⟩
  let C : ι → Subgroup (StatedProj H) := fun t =>
    (Subgroup.centralizer ({dH h t.1.1 t.1.2.2, dH h t.1.2.1 t.1.2.2} : Set H)).map (projH H)
  have hne : Nonempty ι :=
    ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩), by
      refine ⟨?_, ?_, ?_⟩ <;> simp [Fin.ext_iff]⟩⟩
  have hQC : ∀ t : ι, ∀ g : K, φ g ∈ C t → g ∈ Subgroup.normalizer (Q t : Set K) := by
    intro t g hg
    obtain ⟨s, hs, hsg⟩ := hg
    have hs' : s ∈ Subgroup.centralizer ({dH h t.1.1 t.1.2.2, dH h t.1.2.1 t.1.2.2} : Set H) := hs
    rw [Subgroup.mem_centralizer_iff] at hs'
    refine hQn t g s ?_ ?_ hsg.symm
    · exact (congrArg Subtype.val (hs' (dH h t.1.1 t.1.2.2) (by simp))).symm
    · exact (congrArg Subtype.val (hs' (dH h t.1.2.1 t.1.2.2) (by simp))).symm
  have hC : Subgroup.closure (⋃ t, (C t : Set (StatedProj H))) = ⊤ := by
    set Y := Subgroup.closure (⋃ t, (C t : Set (StatedProj H))) with hY
    rw [eq_top_iff]
    intro x _
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective
      ((StatedScalars (Fin n) F).subgroupOf H) x
    have hW : H ≤ (Y.comap (projH H)).map H.subtype := by
      refine hgen.trans ?_
      rw [Subgroup.closure_le]
      rintro A ⟨hA, a, b, c, hab, hac, hbc, h1, h2⟩
      refine ⟨⟨A, hA⟩, ?_, rfl⟩
      refine Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨⟨(a, b, c), hab, hac, hbc⟩, ?_⟩)
      refine ⟨⟨A, hA⟩, Subgroup.mem_centralizer_iff.mpr ?_, rfl⟩
      intro k hk
      rcases hk with rfl | hk
      · exact Subtype.ext h1.eq.symm
      · rw [Set.mem_singleton_iff] at hk
        subst hk
        exact Subtype.ext h2.eq.symm
    obtain ⟨w, hw, hws⟩ := hW s.2
    have : w = s := Subtype.ext hws
    rw [← this]
    exact hw
  exact glbCore_eq_top_of_family hφ hker hperf h.prime hP hne Q hQP hQr C hQC hC T

end Cover

end Torus

end CFSG.AGLEmbedding.KFactProofs.AlphaFive
