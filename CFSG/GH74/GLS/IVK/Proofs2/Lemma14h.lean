module

public import CFSG.GH74.GLS.IVK.Proofs2.Pgl2Three
public import CFSG.GH74.GLS.IVK.L2.Hilbert90
public import CFSG.GH74.GLS.IVK.L2.NotationTransport
public import CFSG.GH74.GLS.IVK.L2.Fixed14a
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid
public import CFSG.Dihedral.Glauberman.DicksonMaxCases
public import CFSG.GroupTheory.ABGDGroups.LinearStructure
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open scoped commutatorElement Pointwise

namespace CFSG.GH74.GLS.IVK.Proofs2

section Lemma14h


variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem exists_four_le_of_isL2 (I : Subgroup K) (hI : IsL2 ↥I (fun q₀ => Odd q₀ ∧ 3 ≤ q₀)) :
    ∃ V : Subgroup K, V ≤ I ∧ Nat.card V = 4 ∧ ∀ v ∈ V, v * v = 1 := by
  obtain ⟨F₀, _, _, ⟨hodd, h3⟩, ⟨e₀⟩⟩ := hI
  have : Fintype F₀ := Fintype.ofFinite F₀
  have h2 : (2 : F₀) ≠ 0 := by
    have hc : ringChar F₀ ≠ 2 := by
      intro hc
      have := (FiniteField.even_card_iff_char_two).mp hc
      rw [← Nat.card_eq_fintype_card] at this
      obtain ⟨k, hk⟩ := hodd
      omega
    exact Ring.two_ne_zero hc
  obtain ⟨H₀, ⟨eA⟩⟩ := CFSG.Glauberman.Dickson.QuatTable.exists_alternatingFour_subgroup (F := F₀) h2
  let ψ : ↥I ≃* PSL2 F₀ := e₀.trans (L2.equivPSL F₀)
  let M : Subgroup ↥I := H₀.map ψ.symm.toMonoidHom
  let eM : M ≃* alternatingGroup (Fin 4) :=
    (Subgroup.equivMapOfInjective H₀ ψ.symm.toMonoidHom ψ.symm.injective).symm.trans eA
  let N : Subgroup K := M.map I.subtype
  let eN : N ≃* alternatingGroup (Fin 4) :=
    (Subgroup.equivMapOfInjective M I.subtype I.subtype_injective).symm.trans eM
  obtain ⟨V, hV4, hV⟩ := CFSG.Glauberman.Dickson.MaxCases.exists_kleinFour eN
  refine ⟨V, ?_, hV4, fun v hv => (hV v).mp hv |>.2⟩
  intro v hv
  obtain ⟨m, -, rfl⟩ := ((hV v).mp hv).1
  exact m.2

theorem isFourSubgroup_of_card_sq {G : Type} [Group G] (V : Subgroup G) (h4 : Nat.card V = 4)
    (hsq : ∀ v ∈ V, v * v = 1) : IsFourSubgroup V := by
  have hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := by
    intro v hv w hw
    have h1 : v * w * (v * w) = 1 := hsq _ (V.mul_mem hv hw)
    have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hsq v hv)
    have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hsq w hw)
    have h2 : v * w = (v * w)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    rw [h2, mul_inv_rev, hv', hw']
  refine ⟨?_, h4⟩
  exact
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hVcomm a a.2 b b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (fun a => by
        apply Subtype.ext
        simpa [sq] using hsq a a.2) }

omit [Finite K] in
theorem centralizer_inf_innDiagSub_eq_bot
    (hF : L2Field F) (e : K ≃* L2 F) (I : Subgroup K)
    (hI : IsL2 ↥I (fun q₀ => Odd q₀ ∧ 3 ≤ q₀)) :
    centralizer ((I.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) : Set (MulAut K)) ⊓
      innDiagSub e = ⊥ := by
  have hinj := conj_injective_of_L2 e
  obtain ⟨V, hVI, hV4, hVsq⟩ := exists_four_le_of_isL2 I hI
  obtain ⟨F₀, _, _, -, ⟨e₀⟩⟩ := hI
  have hcenter : Subgroup.center ↥I = ⊥ :=
    center_eq_bot_of_mulEquiv (e₀.trans (L2.equivPSL F₀)) (psl2_center_eq_bot F₀)
  let V' : Subgroup (MulAut K) := V.map (MulAut.conj : K →* MulAut K)
  have hV'inn : V' ≤ innAut K := by
    rintro _ ⟨k, -, rfl⟩
    exact ⟨k, rfl⟩
  have hV'4 : IsFourSubgroup V' := by
    refine isFourSubgroup_of_card_sq V' ?_ ?_
    · rw [Subgroup.card_map_of_injective hinj]
      exact hV4
    · rintro _ ⟨k, hk, rfl⟩
      rw [← map_mul, hVsq k hk, map_one]
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  rw [Subgroup.mem_inf] at ha
  obtain ⟨haC, haD⟩ := ha
  have haV : a ∈ centralizer (V' : Set (MulAut K)) ⊓ innDiagSub e := by
    refine ⟨Subgroup.mem_centralizer_iff.mpr (fun g hg => ?_), haD⟩
    exact (Subgroup.mem_centralizer_iff.mp haC) g (Subgroup.map_mono hVI hg)
  rw [centralizer_four_inf_innDiagSub e hF V' hV'inn hV'4] at haV
  obtain ⟨v, hv, rfl⟩ := haV
  have hvI : v ∈ I := hVI hv
  have hcent : (⟨v, hvI⟩ : ↥I) ∈ Subgroup.center ↥I := by
    rw [Subgroup.mem_center_iff]
    intro i
    have h1 := (Subgroup.mem_centralizer_iff.mp haC) (MulAut.conj (i : K)) ⟨i, i.2, rfl⟩
    apply Subtype.ext
    apply hinj
    simp only [Subgroup.coe_mul, map_mul]
    exact h1
  rw [hcenter, Subgroup.mem_bot] at hcent
  have hv1 : v = 1 := congrArg Subtype.val hcent
  rw [hv1, map_one]


section PartA

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem isCyclic_ringAut_of_L2 (hF : L2Field F) (e : K ≃* L2 F) : IsCyclic (F ≃+* F) := by
  obtain ⟨hcyc, ⟨ψ⟩, -⟩ := ivk_1_2e F hF K e
  exact ψ.isCyclic.mp hcyc

theorem centralizer_cyclic_fieldAut
    (hF : L2Field F) (e : K ≃* L2 F) (I : Subgroup K)
    (hI : IsL2 ↥I (fun q₀ => Odd q₀ ∧ 3 ≤ q₀)) :
    ∃ e' : K ≃* L2 F,
      IsCyclic ↥(centralizer ((I.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
        Set (MulAut K))) ∧
      centralizer ((I.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
        Set (MulAut K)) ≤ fieldAutSub e' := by
  set C := centralizer ((I.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
    Set (MulAut K)) with hC
  have hbot := centralizer_inf_innDiagSub_eq_bot hF e I hI
  have hinj : Function.Injective ((fieldProj e).comp C.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro c hc
    have h1 : fieldProj e (c : MulAut K) = 1 := hc
    have h2 : (c : MulAut K) ∈ innDiagSub e := (mem_innDiagSub_iff e _).mpr h1
    have h3 : (c : MulAut K) ∈ C ⊓ innDiagSub e := ⟨c.2, h2⟩
    rw [hbot, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have := isCyclic_ringAut_of_L2 hF e
  have hCcyc : IsCyclic ↥C := isCyclic_of_injective _ hinj
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥C)
  set c : MulAut K := (g : MulAut K) with hcdef
  set x : PGammaL2 F := thetaAut e c with hx
  have hpow : x ^ orderOf x.right = 1 := by
    have h1 : c ^ orderOf (fieldProj e c) ∈ C ⊓ innDiagSub e := by
      refine ⟨C.pow_mem g.2 _, (mem_innDiagSub_iff e _).mpr ?_⟩
      rw [map_pow, pow_orderOf_eq_one]
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : x ^ orderOf x.right = thetaAut e (c ^ orderOf (fieldProj e c)) := by
      rw [map_pow]; rfl
    rw [h2, h1, map_one]
  obtain ⟨C₀, hC₀⟩ := H90.pgammaL2_conj_inr_of_pow_eq_one x hpow
  set h : MulAut K := innDiagHom e C₀ with hh
  have hth : thetaAut e h = SemidirectProduct.inl C₀ := thetaAut_innDiagHom e C₀
  have hconj : h⁻¹ * c * h = fieldAutHom e x.right := by
    apply (thetaAut e).injective
    rw [map_mul, map_mul, map_inv, hth, thetaAut_fieldAutHom]
    exact hC₀
  refine ⟨twistEquiv e h⁻¹, hCcyc, ?_⟩
  have hcmem : c ∈ fieldAutSub (twistEquiv e h⁻¹) := by
    rw [mem_fieldAutSub_twist_iff]
    rw [hconj]
    exact ⟨x.right, rfl⟩
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥C) ∈ Subgroup.zpowers g := hg _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'
  have : y = c ^ k := by
    have := congrArg (fun z : ↥C => (z : MulAut K)) hk
    simpa using this.symm
  rw [this]
  exact (fieldAutSub (twistEquiv e h⁻¹)).zpow_mem hcmem k

end PartA

section PartB

variable {F₀ : Type} [Field F₀] [Finite F₀]

theorem index_oResidual_pgl2_le_two (hodd : Odd (Nat.card F₀)) (h3 : 3 ≤ Nat.card F₀) :
    (oResidual 2 (PGL2 F₀)).index ≤ 2 := by
  rcases h3.lt_or_eq with hlt | heq
  · have hF : IsOddPrimePower (Nat.card F₀) := isOddPrimePower_of_L2Field ⟨hodd, hlt⟩
    set J := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F₀)).range with hJ
    have hJidx : J.index = 2 := pgl2_psl2Range_index_eq_two F₀ hF
    have hJN : J ≤ oResidual 2 (PGL2 F₀) := by
      have hsimple : IsSimpleGroup (PSL2 F₀) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
      let ψ : PSL2 F₀ ≃* J :=
        MonoidHom.ofInjective Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      have : IsSimpleGroup ↥J := ψ.symm.isSimpleGroup
      have hNn : ((oResidual 2 (PGL2 F₀)).subgroupOf J).Normal :=
        Subgroup.Normal.subgroupOf (CFSG.GH74.GLS.Stage1.Thm6.Prod.oResidual_normal 2 _) J
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((oResidual 2 (PGL2 F₀)).subgroupOf J) with
        hbot | htop
      · exfalso
        have hcard : Nat.card J * 2 = Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) := by
          have h1 := Subgroup.card_mul_index J
          rw [hJidx, pgl2_card_formula F₀] at h1
          exact h1
        have hq1 : Nat.card F₀ ≠ 1 := by omega
        set p := (Nat.card F₀).minFac with hp
        have hpp : p.Prime := Nat.minFac_prime hq1
        have hpq : p ∣ Nat.card F₀ := Nat.minFac_dvd _
        have hp2 : p ≠ 2 := by
          rintro h2
          rw [h2] at hpq
          obtain ⟨k, hk⟩ := hodd
          omega
        have hpJ : p ∣ Nat.card J := by
          have : p ∣ Nat.card J * 2 := by
            rw [hcard]; exact Dvd.dvd.mul_right hpq _
          rcases (Nat.Prime.dvd_mul hpp).mp this with h | h
          · exact h
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h) hp2
        have : Fact p.Prime := ⟨hpp⟩
        obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpJ
        have hxo : orderOf (x : PGL2 F₀) = p := by rw [Subgroup.orderOf_coe]; exact hx
        have hxN : (x : PGL2 F₀) ∈ oResidual 2 (PGL2 F₀) := by
          apply Subgroup.subset_closure
          show Nat.Coprime (orderOf (x : PGL2 F₀)) 2
          rw [hxo]
          exact (Nat.coprime_primes hpp Nat.prime_two).mpr hp2
        have hxmem : x ∈ (oResidual 2 (PGL2 F₀)).subgroupOf J := hxN
        rw [hbot, Subgroup.mem_bot] at hxmem
        rw [hxmem, orderOf_one] at hx
        exact hpp.one_lt.ne hx
      · intro x hx
        have : (⟨x, hx⟩ : J) ∈ (oResidual 2 (PGL2 F₀)).subgroupOf J := by
          rw [htop]; exact Subgroup.mem_top _
        exact this
    have : J.FiniteIndex := ⟨by rw [hJidx]; norm_num⟩
    exact (Subgroup.index_antitone hJN).trans hJidx.le
  · have h3 : Nat.card F₀ = 3 := heq.symm
    obtain ⟨e⟩ := exists_pgl2_equiv_perm h3
    have hmap : (oResidual 2 (PGL2 F₀)).map e.toMonoidHom = oResidual 2 (Equiv.Perm (Fin 4)) :=
      CFSG.GH74.GLS.Stage1.Thm6.Prod.map_oResidual e.toMonoidHom e.surjective Nat.prime_two
    rw [← Subgroup.index_map_equiv (oResidual 2 (PGL2 F₀)) e]
    have hmap' : (oResidual 2 (PGL2 F₀)).map (e : PGL2 F₀ →* Equiv.Perm (Fin 4)) =
        oResidual 2 (Equiv.Perm (Fin 4)) := hmap
    rw [hmap']
    have hle : alternatingGroup (Fin 4) ≤ oResidual 2 (Equiv.Perm (Fin 4)) := by
      rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
      refine (Subgroup.closure_le _).mpr ?_
      intro σ hσ
      apply Subgroup.subset_closure
      show Nat.Coprime (orderOf σ) 2
      rw [hσ.orderOf]
      norm_num
    calc (oResidual 2 (Equiv.Perm (Fin 4))).index ≤ (alternatingGroup (Fin 4)).index :=
        Subgroup.index_antitone hle
      _ = 2 := alternatingGroup.index_eq_two

theorem card_le_two_mul_oResidual (hodd : Odd (Nat.card F₀)) (h3 : 3 ≤ Nat.card F₀) :
    Nat.card (PGL2 F₀) ≤ 2 * Nat.card ↥(oResidual 2 (PGL2 F₀)) := by
  have h1 := Subgroup.card_mul_index (oResidual 2 (PGL2 F₀))
  have h2 := index_oResidual_pgl2_le_two hodd h3
  calc Nat.card (PGL2 F₀) = Nat.card ↥(oResidual 2 (PGL2 F₀)) * (oResidual 2 (PGL2 F₀)).index :=
      h1.symm
    _ ≤ Nat.card ↥(oResidual 2 (PGL2 F₀)) * 2 := Nat.mul_le_mul_left _ h2
    _ = 2 * Nat.card ↥(oResidual 2 (PGL2 F₀)) := by ring

theorem two_mul_card_ge {K : Type} [Group K] [Finite K] (Gs : Subgroup K)
    (φ : ↥Gs ≃* PGL2 F₀) (hodd : Odd (Nat.card F₀)) (h3 : 3 ≤ Nat.card F₀) :
    Nat.card (PGL2 F₀) ≤ 2 * Nat.card ↥((oResidual 2 ↥Gs).map Gs.subtype) := by
  have hc1 : Nat.card ↥((oResidual 2 ↥Gs).map Gs.subtype) = Nat.card ↥(oResidual 2 ↥Gs) :=
    Subgroup.card_map_of_injective Gs.subtype_injective
  have hmap := CFSG.GH74.GLS.Stage1.Thm6.Prod.map_oResidual φ.toMonoidHom φ.surjective
    (p := 2) Nat.prime_two
  have hc2 : Nat.card ↥(oResidual 2 (PGL2 F₀)) = Nat.card ↥(oResidual 2 ↥Gs) := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective φ.injective
  rw [hc1, ← hc2]
  exact card_le_two_mul_oResidual hodd h3

end PartB

section PartB2

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem fixedSubgroup_card_bound (hF : L2Field F) (e : K ≃* L2 F) (τ : F ≃+* F) :
    ∃ q₁ : ℕ, 2 ≤ q₁ ∧ q₁ ^ orderOf τ = Nat.card F ∧
      Nat.card ↥(fixedSubgroup K (fieldAutHom e τ)) < q₁ ^ 3 := by
  obtain ⟨-, hodd, heven⟩ := ivk_1_4a F hF K e τ
  have key : ∀ q₁ : ℕ, 2 ≤ q₁ → q₁ * (q₁ ^ 2 - 1) < q₁ ^ 3 := by
    intro q₁ h2
    have h1 : 0 < q₁ ^ 2 := by positivity
    have : q₁ ^ 2 - 1 < q₁ ^ 2 := by omega
    calc q₁ * (q₁ ^ 2 - 1) < q₁ * q₁ ^ 2 := Nat.mul_lt_mul_of_pos_left this (by omega)
      _ = q₁ ^ 3 := by ring
  rcases Nat.even_or_odd (orderOf τ) with hev | hod
  · obtain ⟨F₁, _, _, hq, ⟨ψ⟩⟩ := heven hev
    have h2 : 2 ≤ Nat.card F₁ := Finite.one_lt_card
    refine ⟨Nat.card F₁, h2, hq, ?_⟩
    rw [Nat.card_congr ψ.toEquiv, pgl2_card_formula F₁]
    exact key _ h2
  · obtain ⟨⟨F₁, _, _, hq, ⟨ψ⟩⟩, -⟩ := hodd hod
    have h2 : 2 ≤ Nat.card F₁ := Finite.one_lt_card
    refine ⟨Nat.card F₁, h2, hq, ?_⟩
    have h1 : Nat.card ↥(fixedSubgroup K (fieldAutHom e τ)) = Nat.card (L2 F₁) :=
      Nat.card_congr ψ.toEquiv
    have h3 : Nat.card (L2 F₁) ≤ Nat.card (PGL2 F₁) :=
      Nat.card_le_card_of_injective
        (fun x => Matrix.ProjectiveSpecialLinearGroup.toPGL (L2.equivPSL F₁ x))
        (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp (L2.equivPSL F₁).injective)
    rw [h1]
    refine lt_of_le_of_lt h3 ?_
    rw [pgl2_card_formula F₁]
    exact key _ h2

theorem centralizer_eq_zpowers
    (hF : L2Field F) (e : K ≃* L2 F) (I : Subgroup K)
    (hI : IsL2 ↥I (fun q₀ => Odd q₀ ∧ 3 ≤ q₀)) (σ' : F ≃+* F) (hσ2 : orderOf σ' = 2)
    (hIσ : I = (oResidual 2 ↥(fixedSubgroup K (fieldAutHom e σ'))).map
      (fixedSubgroup K (fieldAutHom e σ')).subtype) :
    centralizer ((I.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) : Set (MulAut K)) =
      zpowers (fieldAutHom e σ') := by
  set σ : MulAut K := fieldAutHom e σ' with hσ
  set C := centralizer ((I.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
    Set (MulAut K)) with hC
  have hσo : orderOf σ = 2 := by
    rw [hσ, orderOf_injective (fieldAutHom e) (fieldAutHom_injective e) σ', hσ2]
  have hconjinj := conj_injective_of_L2 e
  have hIfix : ∀ i ∈ I, σ i = i := by
    intro i hi
    rw [hIσ] at hi
    obtain ⟨y, -, rfl⟩ := hi
    exact y.2
  have hσC : σ ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    rintro h ⟨i, hi, rfl⟩
    have h1 := mul_conj_mul_inv_eq_conj_apply σ i
    rw [hIfix i hi] at h1
    calc MulAut.conj i * σ = (σ * MulAut.conj i * σ⁻¹) * σ := by rw [h1]
      _ = σ * MulAut.conj i := by group
  obtain ⟨-, -, heven⟩ := ivk_1_4a F hF K e σ'
  obtain ⟨F₀, _, _, hq₀, ⟨φ⟩⟩ := heven (by rw [hσ2]; exact even_two)
  rw [hσ2] at hq₀
  have hq₀odd : Odd (Nat.card F₀) := by
    have : Odd (Nat.card F₀ ^ 2) := by rw [hq₀]; exact hF.1
    exact (Nat.odd_mul.mp (by simpa [pow_two] using this)).1
  have hq₀ge : 3 ≤ Nat.card F₀ := by
    have h2 : 2 ≤ Nat.card F₀ := Finite.one_lt_card
    obtain ⟨k, hk⟩ := hq₀odd
    omega
  have hIcard : Nat.card (PGL2 F₀) ≤ 2 * Nat.card I := by
    rw [hIσ]
    exact two_mul_card_ge (fixedSubgroup K σ) φ hq₀odd hq₀ge
  rw [pgl2_card_formula F₀] at hIcard
  obtain ⟨e'', hCcyc, hCle⟩ := centralizer_cyclic_fieldAut hF e I hI
  have hordle : ∀ c ∈ C, orderOf c ≤ 2 := by
    intro c hc
    by_contra hlt
    push Not at hlt
    obtain ⟨τ, hτ⟩ := hCle hc
    subst hτ
    have hτo : orderOf τ = orderOf (fieldAutHom e'' τ) :=
      (orderOf_injective (fieldAutHom e'') (fieldAutHom_injective e'') τ).symm
    obtain ⟨q₁, hq₁2, hq₁pow, hbound⟩ := fixedSubgroup_card_bound hF e'' τ
    have hIle : I ≤ fixedSubgroup K (fieldAutHom e'' τ) := by
      intro i hi
      have h1 : MulAut.conj i * fieldAutHom e'' τ = fieldAutHom e'' τ * MulAut.conj i :=
        (Subgroup.mem_centralizer_iff.mp hc) (MulAut.conj i) ⟨i, hi, rfl⟩
      have h2 := mul_conj_mul_inv_eq_conj_apply (fieldAutHom e'' τ) i
      have h3 : fieldAutHom e'' τ * MulAut.conj i * (fieldAutHom e'' τ)⁻¹ = MulAut.conj i := by
        rw [← h1]; group
      rw [h3] at h2
      exact (hconjinj h2).symm
    have hcardI : Nat.card I ≤ Nat.card ↥(fixedSubgroup K (fieldAutHom e'' τ)) :=
      Subgroup.card_le_of_le hIle
    have hpow : q₁ ^ 3 ≤ Nat.card F := by
      rw [← hq₁pow]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hlt2 : Nat.card I < Nat.card F₀ ^ 2 := by
      rw [hq₀]; omega
    set a := Nat.card F₀ with ha
    have h1a : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h5 : a * (a ^ 2 - 1) + a = a ^ 3 := by
      zify [h1a]; ring
    have h6 : 3 * a ^ 2 ≤ a * a ^ 2 := Nat.mul_le_mul_right _ hq₀ge
    have h7 : a ≤ a ^ 2 := by nlinarith
    have h8 : a * a ^ 2 = a ^ 3 := by ring
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥C)
  have hCcard : orderOf g = Nat.card ↥C := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgle : orderOf g ≤ 2 := by
    rw [← Subgroup.orderOf_coe g]
    exact hordle g g.2
  have hcard2 : Nat.card ↥C ≤ 2 := by rw [← hCcard]; exact hgle
  have hle : zpowers σ ≤ C := (Subgroup.zpowers_le).mpr hσC
  have hzcard : Nat.card ↥(zpowers σ) = 2 := by rw [Nat.card_zpowers, hσo]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hzcard]; exact hcard2)).symm

end PartB2

theorem ivk_1_4h : IVK_1_4h := by
  intro F _ _ hF K _ _ e I hI
  refine ⟨centralizer_cyclic_fieldAut hF e I hI, ?_⟩
  intro e' σ hσ hσ2 hIσ
  obtain ⟨σ', rfl⟩ := hσ
  have hσ2' : orderOf σ' = 2 := by
    rw [← orderOf_injective (fieldAutHom e') (fieldAutHom_injective e') σ']
    exact hσ2
  exact centralizer_eq_zpowers hF e' I hI σ' hσ2' hIσ

end Lemma14h

end CFSG.GH74.GLS.IVK.Proofs2
