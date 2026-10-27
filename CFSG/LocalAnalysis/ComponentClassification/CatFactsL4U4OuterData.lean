module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OuterAct
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Inputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxRed

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OutInv

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer

theorem isSimpleGroup_of_center_eq_bot {Y : Type*} [Group Y] (hY : IsQuasisimple Y)
    (hZ : center Y = ⊥) : IsSimpleGroup Y := by
  have : IsSimpleGroup (Y ⧸ center Y) := hY.2.1
  exact (MulEquiv.isSimpleGroup_congr (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm))).mpr this

theorem nonempty_quotient_center_equiv {X Q Y : Type*} [Group X] [Group Q] [Group Y]
    [Finite Q] (hQ : IsQuasisimple Q) (θ : X →* Q) (hθ : Function.Surjective θ)
    (O : Subgroup X) [O.Normal] (hO : Odd (Nat.card (O.map θ))) (e : X ⧸ O ≃* Y)
    [IsSimpleGroup Y] : Nonempty (Q ⧸ center Q ≃* Y) := by
  set M : Subgroup X := (center Q).comap θ with hM
  have hOM : O ≤ M := by
    have hn : (O.map θ).Normal := Subgroup.Normal.map inferInstance θ hθ
    rcases LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hQ (O.map θ) with hc | ht
    · intro x hx
      exact hc (mem_map_of_mem θ hx)
    · exfalso
      have hodd : Odd (Nat.card Q) := by
        rw [ht, Subgroup.card_top] at hO
        exact hO
      exact false_of_isSolvable hQ (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
  have hMO : M ≤ O := by
    have hMn : M.Normal := Subgroup.Normal.comap inferInstance θ
    set Mb : Subgroup Y := (M.map (QuotientGroup.mk' O)).map e.toMonoidHom with hMb
    have hMbn : Mb.Normal := (hMn.map _ (QuotientGroup.mk'_surjective O)).map _ e.surjective
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Mb with hb | ht
    · intro x hx
      have h1 : e (QuotientGroup.mk' O x) ∈ Mb := ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [hb, mem_bot, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at h1
      exact h1
    · exfalso
      have hall : ∀ x : X, x ∈ M := by
        intro x
        have h1 : e (QuotientGroup.mk' O x) ∈ Mb := by
          rw [ht]
          exact mem_top _
        obtain ⟨_, ⟨m, hm, rfl⟩, hme⟩ := h1
        have h2 : QuotientGroup.mk' O m = QuotientGroup.mk' O x := e.injective hme
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h2
        have := mul_mem hm (hOM h2)
        rwa [mul_inv_cancel_left] at this
      obtain ⟨-, -, a, b, hab⟩ := hQ
      apply hab
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      obtain ⟨x', rfl⟩ := hθ x
      obtain ⟨y', rfl⟩ := hθ y
      have hx : θ x' ∈ center Q := hall x'
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hx (θ y')]
  have hMeq : M = O := le_antisymm hMO hOM
  set ψ : X →* Q ⧸ center Q := (QuotientGroup.mk' (center Q)).comp θ with hψ
  have hψs : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hθ
  have hker : ψ.ker = O := by
    rw [← hMeq, hM, hψ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans e)⟩

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

noncomputable abbrev GAut : Subgroup (MulAut (LK h)) := (rhoBar hKa).range

noncomputable abbrev phi : Wbar h.B →* ↥(GAut hKa) := (rhoBar hKa).rangeRestrict

theorem phi_surjective : Function.Surjective (phi hKa) := MonoidHom.rangeRestrict_surjective _

theorem ker_phi : (phi hKa).ker = (rhoBar hKa).ker := MonoidHom.ker_rangeRestrict _

theorem center_LK : center (LK h) = ⊥ :=
  LieType.CurtisTits.center_quotient_center_eq_bot_of_isQuasisimple h.isQuasisimple_K

theorem conj_injective : Function.Injective (MulAut.conj : LK h →* MulAut (LK h)) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have hc : y ∈ center (LK h) := by
    rw [mem_center_iff]
    intro x
    have := congrArg (fun φ : MulAut (LK h) => φ x) hy
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * y = (y * x * y⁻¹) * y := by rw [this]
      _ = y * x := by group
  rw [center_LK, mem_bot] at hc
  exact hc

theorem conj_apply_eq (σ : MulAut (LK h)) (x : LK h) :
    MulAut.conj (σ x) = σ * MulAut.conj x * σ⁻¹ := by
  ext y
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv, MulAut.apply_inv_self]

theorem conj_mem_GAut (l : LK h) : MulAut.conj l ∈ GAut hKa := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective l
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨wbarMk h.B ⟨k, K_le_W h k.2⟩, by rw [rhoBar_mk, rhoL_of_mem_K]⟩

theorem inn_le_GAut : (MulAut.conj : LK h →* MulAut (LK h)).range ≤ GAut hKa := by
  rintro _ ⟨l, rfl⟩
  exact conj_mem_GAut hKa l

noncomputable abbrev NL : Subgroup ↥(GAut hKa) :=
  (MulAut.conj : LK h →* MulAut (LK h)).range.subgroupOf (GAut hKa)

theorem NL_normal : (NL hKa).Normal := by
  constructor
  intro n hn γ
  rw [mem_subgroupOf] at hn ⊢
  obtain ⟨l, hl⟩ := hn
  refine ⟨(γ : MulAut (LK h)) l, ?_⟩
  rw [conj_apply_eq, hl]
  simp

theorem centralizer_NL : centralizer ((NL hKa : Subgroup ↥(GAut hKa)) : Set ↥(GAut hKa)) = ⊥ := by
  rw [eq_bot_iff]
  intro γ hγ
  rw [mem_centralizer_iff] at hγ
  rw [mem_bot]
  apply Subtype.ext
  ext x
  have h1 := hγ ⟨MulAut.conj x, conj_mem_GAut hKa x⟩ (by
    rw [SetLike.mem_coe, mem_subgroupOf]
    exact ⟨x, rfl⟩)
  have h2 := congrArg (fun g : ↥(GAut hKa) => (g : MulAut (LK h))) h1
  simp only [Subgroup.coe_mul] at h2
  have h3 : MulAut.conj ((γ : MulAut (LK h)) x) = MulAut.conj x := by
    rw [conj_apply_eq, ← h2, mul_inv_cancel_right]
  exact conj_injective h3

theorem nonempty_NL_equiv : Nonempty (↥(NL hKa) ≃* LK h) :=
  ⟨(subgroupOfEquivOfLe (inn_le_GAut hKa)).trans
    (MonoidHom.ofInjective (f := (MulAut.conj : LK h →* MulAut (LK h))) conj_injective).symm⟩

theorem lieModel_NL {t : Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (hn : n ≠ 0)
    (hK : Blueprint.LieModel (ZStarBar h.K) t n p f) : Blueprint.LieModel ↥(NL hKa) t n p f := by
  obtain ⟨eN⟩ := nonempty_NL_equiv hKa
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  exact lieModel_of_mulEquiv_ne_zero (eN.trans eZ).symm hn hK

noncomputable abbrev abar (h : Hyp52 H) : Wbar h.B := wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩

theorem abar_mul_self : abar h * abar h = 1 := by
  have ha2 : h.a * h.a = 1 := by rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  rw [← map_mul, ← map_one (wbarMk h.B)]
  congr 1
  exact Subtype.ext ha2

theorem phi_abar_not_mem (hout : h.a ∉ h.K ⊔ coreActionKernel h.K) :
    phi hKa (abar h) ∉ NL hKa := by
  intro hmem
  rw [mem_subgroupOf] at hmem
  obtain ⟨l, hl⟩ := hmem
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective l
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  have h1 : rhoL hKa ⟨k, K_le_W h k.2⟩ = rhoL hKa ⟨h.a, h.a_mem_normalizer⟩ := by
    rw [rhoL_of_mem_K, ← rhoBar_mk]
    exact hl
  have h2 : rhoL hKa ((⟨k, K_le_W h k.2⟩ : h.W)⁻¹ * ⟨h.a, h.a_mem_normalizer⟩) = 1 := by
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  rw [rhoL_eq_one_iff] at h2
  apply hout
  have e : h.a = (k : H) * ((k : H)⁻¹ * h.a) := by group
  rw [e]
  refine mul_mem (mem_sup_left k.2) (mem_sup_right ?_)
  simpa using h2

theorem orderOf_phi_abar (hout : h.a ∉ h.K ⊔ coreActionKernel h.K) :
    orderOf (phi hKa (abar h)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [sq, ← map_mul, abar_mul_self, map_one]
  · intro h1
    apply phi_abar_not_mem hKa hout
    rw [h1]
    exact one_mem _

include hKa in
theorem JBbar_le_Khat : wbarImage h.B (GSLit.fixedLayer h.J h.B) ≤ Khat h := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, fixedLayer_le_K h hKa hx, rfl⟩

noncomputable abbrev Jhat : Subgroup ↥(GAut hKa) :=
  (wbarImage h.B (GSLit.fixedLayer h.J h.B)).map (phi hKa)

theorem ker_phi_le : (phi hKa).ker ≤
    centralizer ((wbarImage h.B (GSLit.fixedLayer h.J h.B) : Subgroup (Wbar h.B)) :
      Set (Wbar h.B)) := by
  rw [ker_phi]
  exact ker_le_centralizer hKa (JBbar_le_Khat hKa)

theorem odd_card_ker_phi : Odd (Nat.card (phi hKa).ker) := by
  rw [ker_phi]
  exact odd_card_ker hKa

theorem Jhat_le_NL : Jhat hKa ≤ NL hKa := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, mem_subgroupOf] at hy
  have hyK : (y : H) ∈ h.K := fixedLayer_le_K h hKa hy
  rw [mem_subgroupOf]
  refine ⟨(((⟨(y : H), hyK⟩ : h.K) : OddBar h.K) : LK h), ?_⟩
  show _ = rhoBar hKa (wbarMk h.B y)
  rw [rhoBar_mk, ← rhoL_of_mem_K hKa ⟨(y : H), hyK⟩]

theorem Jhat_component : Jhat hKa ≤ centralizer ({phi hKa (abar h)} : Set ↥(GAut hKa)) ∧
    IsComponent ((Jhat hKa).subgroupOf (centralizer ({phi hKa (abar h)} : Set ↥(GAut hKa)))) :=
  B5a.isComponent_map_centralizer (phi_surjective hKa) (odd_card_ker_phi hKa) (ker_phi_le hKa)
    abar_mul_self h.isComponent_bar.1 h.isComponent_bar.2

theorem Jhat_standard : IsStandardSubgroup (Jhat hKa) :=
  B5a.isStandardSubgroup_map (phi_surjective hKa) h.isStandard_bar (odd_card_ker_phi hKa)
    (ker_phi_le hKa)

theorem nonempty_Jhat_equiv (hZJ : center (OddBar h.J) = ⊥) :
    Nonempty (↥(Jhat hKa) ⧸ center ↥(Jhat hKa) ≃* OddBar h.J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set JB := GSLit.fixedLayer h.J h.B with hJB
  have hJBW : JB ≤ h.W := (fixedLayer_le_K h hKa).trans (K_le_W h)
  set JB' : Subgroup h.W := JB.subgroupOf h.W with hJB'
  set χ : h.W →* ↥(GAut hKa) := (phi hKa).comp (wbarMk h.B) with hχ
  have heq : Jhat hKa = JB'.map χ := Subgroup.map_map _ _ _
  have hBJ : h.B ≤ coreActionKernel h.J := h.B_le.trans inf_le_right
  have hB2 : IsPGroup 2 h.B := h.isPGroup_S.to_le (h.B_le.trans inf_le_left)
  have hsup := (GSLit.fixedLayer_sup_pPrimeCore (B5a.isQuasisimple_J h) hBJ hB2).1
  have hJBJ : JB ≤ h.J := (GSLit.fixedLayer_le_inf h.J h.B).trans inf_le_left
  obtain ⟨-, e1, -⟩ := restriction_quotient_mulEquiv hJBJ hsup
  let e2 : JB ≃* JB' := (subgroupOfEquivOfLe hJBW).symm
  let e3 : JB ⧸ pPrimeCore 2 JB ≃* JB' ⧸ pPrimeCore 2 JB' :=
    QuotientGroup.congr (pPrimeCore 2 JB) (pPrimeCore 2 JB') e2 (pPrimeCore_map_iso 2 e2)
  have hsimp : IsSimpleGroup (OddBar h.J) := isSimpleGroup_of_center_eq_bot h.isQuasisimple_J hZJ
  have hQ : IsQuasisimple ↥(JB'.map χ) := by
    rw [← heq]
    exact (Jhat_standard hKa).1
  have hO : Odd (Nat.card ((pPrimeCore 2 JB').map (χ.subgroupMap JB'))) := by
    have h1 := Subgroup.card_map_dvd (H := pPrimeCore 2 JB') (χ.subgroupMap JB')
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card) h1
  obtain ⟨eQ⟩ := nonempty_quotient_center_equiv hQ (χ.subgroupMap JB')
    (χ.subgroupMap_surjective JB') (pPrimeCore 2 JB') hO (e3.symm.trans e1)
  rw [heq]
  exact ⟨eQ⟩

theorem outer_config {p f : ℕ} (hJ : Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f))
    (hK : Blueprint.LieModel (ZStarBar h.K) .PSL 4 p f ∨
      Blueprint.LieModel (ZStarBar h.K) .PSU 4 p f ∨
      ∃ e : ℕ, f = 2 * e ∧ Blueprint.LieModel (ZStarBar h.K) .POmegaMinus 4 p e)
    (hout : h.a ∉ h.K ⊔ coreActionKernel h.K) :
    OuterL2Config ↥(GAut hKa) (NL hKa) p f (phi hKa (abar h)) (Jhat hKa) := by
  refine ⟨NL_normal hKa, centralizer_NL hKa, ?_, orderOf_phi_abar hKa hout,
    phi_abar_not_mem hKa hout, (Jhat_component hKa).1, (Jhat_component hKa).2, ?_,
    Jhat_standard hKa⟩
  · rcases hK with hK | hK | ⟨e, he, hK⟩
    · exact Or.inl (lieModel_NL hKa (by norm_num) hK)
    · exact Or.inr (Or.inl (lieModel_NL hKa (by norm_num) hK))
    · exact Or.inr (Or.inr ⟨e, he, lieModel_NL hKa (by norm_num) hK⟩)
  · obtain ⟨eJ⟩ := nonempty_Jhat_equiv hKa (IdxRed.center_eq_bot_of_psl2 hJ)
    exact lieModel_of_mulEquiv_ne_zero eJ.symm (by norm_num) hJ

end OutInv

end CFSG.ComponentClassification.CatFactsL4U4
