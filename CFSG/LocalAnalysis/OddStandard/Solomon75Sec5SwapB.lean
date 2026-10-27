module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapA
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapCentral

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.LocalCores
  CFSG.ComponentClassification.Sol76 CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section Aux

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))} {s : X}

theorem le_LPlusIn_of_isPCompIn {H M : Subgroup X} (hM : IsPCompIn 2 H M) : M ≤ LPlusIn H := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro m hm
  refine ⟨⟨m, hM.1 hm⟩, ?_, rfl⟩
  rw [LPlus_eq_pLayer_sup_NPlus]
  exact Subgroup.mem_sup_left ((le_sSup hM.2 : M.subgroupOf H ≤ pLayer ↥H 2) hm)

theorem Sec5Comp.le_LPlusIn_centralizer (h : Sec5Data X n z Z S) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) {v : X} (hvZ : v ∈ Z) (hv1 : v ≠ 1) :
    A ≤ LPlusIn (centralizer ({v} : Set X)) := by
  classical
  have hv2o : orderOf v = 2 := h.orderOf_eq_two_of_mem_Z hvZ hv1
  have hAK : A ≤ K0 X n (normalizer (Z : Set X)) := le_sSup hA
  have hAv : A ≤ centralizer ({v} : Set X) :=
    hAK.trans (h.K0_le_centralizer_Z.trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hvZ)))
  have hAH : A ≤ normalizer (Z : Set X) ⊓ centralizer ({v} : Set X) :=
    le_inf hA.isPCompIn.1 hAv
  have hAc : IsPCompIn 2 (normalizer (Z : Set X) ⊓ centralizer ({v} : Set X)) A :=
    ⟨hAH, isPComponent_subgroupOf_mono hAH inf_le_left hA.isPCompIn.2⟩
  have hcen := h.cen_eq_odd_sup hvZ hv2o
  have hLeq : LPlusIn (centralizer ({v} : Set X)) = oddCoreOf (centralizer ({v} : Set X)) ⊔
      LPlusIn (normalizer (Z : Set X) ⊓ centralizer ({v} : Set X)) := by
    refine LPlusIn_eq_oddCore_sup_of_cover inf_le_right fun c hc => ?_
    have hc' : c ∈ oddCoreOf (centralizer ({v} : Set X)) ⊔
        (normalizer (Z : Set X) ⊓ centralizer ({v} : Set X)) := hcen ▸ hc
    obtain ⟨o, ho, a, ha, hoa⟩ := (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing
      (oddCoreOf (centralizer ({v} : Set X))) (normalizer (Z : Set X) ⊓ centralizer ({v} : Set X))
      (fun x hx => le_normalizer_oddCoreOf _ hx.2) c).1 hc'
    refine ⟨a, ha, a⁻¹ * o * a, ?_, ?_⟩
    · have hn1 := Subgroup.mem_normalizer_iff.1
        (le_normalizer_oddCoreOf _ (Subgroup.inv_mem _ ha.2)) o
      have := hn1.1 ho
      simpa [mul_assoc] using this
    · rw [← hoa]; group
  rw [hLeq]
  exact (le_LPlusIn_of_isPCompIn hAc).trans le_sup_right

omit [Finite X] in
theorem Sec5Comp.isPGroup_center_quot {H B : Subgroup X} (hB : Sec5Comp X n H B) :
    IsPGroup 2 ↥(center (↥(B.subgroupOf H) ⧸ pPrimeCore 2 ↥(B.subgroupOf H))) := by
  have hBH : B ≤ H := hB.isPCompIn.1
  have hc : Nat.card (center (↥B ⧸ pPrimeCore 2 ↥B)) = 2 := hB.2.2.1
  have h0 : IsPGroup 2 ↥(center (↥B ⧸ pPrimeCore 2 ↥B)) :=
    IsPGroup.of_card (n := 1) (by rw [hc, pow_one])
  obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.subgroupOfEquivOfLe hBH)
  exact h0.of_equiv (centerCongr f).symm

theorem Sec5Comp.isPGroup_center_image {H B : Subgroup X} (hB : Sec5Comp X n H B) :
    IsPGroup 2 ↥(center ↥((B.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)))) := by
  obtain ⟨e⟩ := exists_mulEquiv_quot_image hB.isPCompIn.2
  exact hB.isPGroup_center_quot.of_equiv (centerCongr e)

theorem map_cover_eq {H M E : Subgroup X} (hM : IsPCompIn 2 H M) (hEM : E ≤ M)
    (hcov : E.subgroupOf M ⊔ pPrimeCore 2 ↥M = ⊤) :
    (E.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) =
      (M.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) := by
  refine le_antisymm (Subgroup.map_mono (Subgroup.subgroupOf_mono H hEM)) ?_
  rintro _ ⟨m, hm, rfl⟩
  have hm' : (⟨(m : X), hm⟩ : ↥M) ∈ E.subgroupOf M ⊔ pPrimeCore 2 ↥M := by
    rw [hcov]; exact Subgroup.mem_top _
  obtain ⟨e', he', o', ho', hm'e⟩ := Subgroup.mem_sup_of_normal_right.1 hm'
  have hoO : (o' : X) ∈ oddCoreOf M := ⟨o', ho', rfl⟩
  obtain ⟨hoH, hoP⟩ := mem_oddCoreOf_iff.1 (oddCoreOf_le_of_isPCompIn hM hoO)
  have hmeo : m = ⟨(e' : X), hM.1 e'.2⟩ * ⟨(o' : X), hoH⟩ :=
    Subtype.ext (congrArg Subtype.val hm'e).symm
  refine ⟨⟨(e' : X), hM.1 e'.2⟩, he', ?_⟩
  have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥H) (⟨(o' : X), hoH⟩ : ↥H) = 1 :=
    (QuotientGroup.eq_one_iff _).2 hoP
  rw [hmeo, map_mul, h1, mul_one]

end Aux

section Contra

variable {X : Type} [Group X] [Finite X] {n : ℕ}

theorem swap_contra {C M E : Subgroup X} {s : X} (hs2 : s * s = 1)
    (hM : Sec5Comp X n C M) (hM' : Sec5Comp X n C (M.map (MulAut.conj s).toMonoidHom))
    (hne : M.map (MulAut.conj s).toMonoidHom ≠ M)
    (hEM : E ≤ M) (hcov : E.subgroupOf M ⊔ pPrimeCore 2 ↥M = ⊤)
    (hcov' : (E.map (MulAut.conj s).toMonoidHom).subgroupOf (M.map (MulAut.conj s).toMonoidHom) ⊔
      pPrimeCore 2 ↥(M.map (MulAut.conj s).toMonoidHom) = ⊤)
    {OO W₂ : Subgroup X} (hOO : Odd (Nat.card OO))
    (hΛOO : E ⊔ E.map (MulAut.conj s).toMonoidHom ≤ normalizer (OO : Set X))
    (hW₂ : IsPGroup 2 ↥W₂) (hW₂OO : W₂ ≤ normalizer (OO : Set X))
    (hV : ∀ x ∈ E ⊔ E.map (MulAut.conj s).toMonoidHom, ⁅x, s⁆ ∈ OO ⊔ W₂) : False := by
  classical
  set M' : Subgroup X := M.map (MulAut.conj s).toMonoidHom with hM'def
  set E' : Subgroup X := E.map (MulAut.conj s).toMonoidHom with hE'def
  set Λ : Subgroup X := E ⊔ E' with hΛ
  have hMC : M ≤ C := hM.isPCompIn.1
  have hM'C : M' ≤ C := hM'.isPCompIn.1
  have hEC : E ≤ C := hEM.trans hMC
  have hE'M' : E' ≤ M' := Subgroup.map_mono hEM
  have hE'C : E' ≤ C := hE'M'.trans hM'C
  have hΛC : Λ ≤ C := sup_le hEC hE'C
  set π : ↥C →* ↥C ⧸ pPrimeCore 2 ↥C := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  set K₁ : Subgroup (↥C ⧸ pPrimeCore 2 ↥C) := (M.subgroupOf C).map π with hK₁
  set K₂ : Subgroup (↥C ⧸ pPrimeCore 2 ↥C) := (M'.subgroupOf C).map π with hK₂
  have hK₁c : IsComponent K₁ := by
    obtain ⟨K, hK, -, hKeq, -⟩ := hM.isPCompIn.2
    show IsComponent ((M.subgroupOf C).map π)
    rw [hKeq]
    exact hK
  have hK₂c : IsComponent K₂ := by
    obtain ⟨K, hK, -, hKeq, -⟩ := hM'.isPCompIn.2
    show IsComponent ((M'.subgroupOf C).map π)
    rw [hKeq]
    exact hK
  have hK₁₂ : K₁ ≠ K₂ := by
    intro heq
    apply hne
    have h1 := eq_of_map_pPrimeCore_eq hM'.isPCompIn.2 hM.isPCompIn.2 heq.symm
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hM'C, inf_of_le_left hMC] at h1
    exact h1
  have hcomm₁₂ : ∀ a ∈ K₁, ∀ b ∈ K₂, Commute a b := fun a ha b hb =>
    commute_of_ne hK₁c hK₂c hK₁₂ ha hb
  have hZ₁ : IsPGroup 2 ↥(center ↥K₁) := hM.isPGroup_center_image
  have hZ₂ : IsPGroup 2 ↥(center ↥K₂) := hM'.isPGroup_center_image
  have hKE₁ : (E.subgroupOf C).map π = K₁ := map_cover_eq hM.isPCompIn hEM hcov
  have hKE₂ : (E'.subgroupOf C).map π = K₂ := map_cover_eq hM'.isPCompIn hE'M' hcov'
  let ψ₀ : ↥Λ →* ↥C ⧸ pPrimeCore 2 ↥C := π.comp (Subgroup.inclusion hΛC)
  have hΛsub : Λ.subgroupOf C = E.subgroupOf C ⊔ E'.subgroupOf C :=
    Subgroup.subgroupOf_sup hEC hE'C
  have hψ₀ : ∀ y : ↥Λ, ψ₀ y ∈ K₁ ⊔ K₂ := by
    intro y
    have h1 : (⟨(y : X), hΛC y.2⟩ : ↥C) ∈ Λ.subgroupOf C := y.2
    rw [hΛsub] at h1
    have h2 := Subgroup.mem_map_of_mem π h1
    rwa [Subgroup.map_sup, hKE₁, hKE₂] at h2
  let ψ : ↥Λ →* ↥(K₁ ⊔ K₂) := ψ₀.codRestrict (K₁ ⊔ K₂) hψ₀
  have hrange : K₁ ⊔ K₂ ≤ ψ₀.range := by
    refine sup_le ?_ ?_
    · rw [← hKE₁]
      rintro _ ⟨ec, hec, rfl⟩
      exact ⟨⟨(ec : X), Subgroup.mem_sup_left (show (ec : X) ∈ E from hec)⟩, rfl⟩
    · rw [← hKE₂]
      rintro _ ⟨ec, hec, rfl⟩
      exact ⟨⟨(ec : X), Subgroup.mem_sup_right (show (ec : X) ∈ E' from hec)⟩, rfl⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨q, hq⟩
    obtain ⟨y, hy⟩ := hrange hq
    exact ⟨y, Subtype.ext hy⟩
  have hQ : ∀ M₀ : Subgroup ↥(K₁ ⊔ K₂), M₀.Normal → Odd (Nat.card M₀) → M₀ = ⊥ := by
    intro M₀ hM₀ hodd
    have hb := odd_normal_eq_bot_sup hK₁c.1 hZ₁ hK₂c.1 hZ₂ hcomm₁₂
      (M := M₀.map (K₁ ⊔ K₂).subtype) (by rintro _ ⟨x, -, rfl⟩; exact x.2)
      (by
        rintro q hq _ ⟨m, hm, rfl⟩
        exact ⟨⟨q, hq⟩ * m * ⟨q, hq⟩⁻¹, hM₀.conj_mem m hm ⟨q, hq⟩, rfl⟩)
      (by rwa [Subgroup.card_map_of_injective (K₁ ⊔ K₂).subtype_injective])
    exact (Subgroup.map_eq_bot_iff_of_injective M₀ (K₁ ⊔ K₂).subtype_injective).1 hb
  have hwΛ : ∀ x ∈ Λ, s * x * s⁻¹ ∈ Λ := by
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    have h1 : E ≤ Λ.comap (MulAut.conj s).toMonoidHom := fun x hx =>
      Subgroup.mem_sup_right ⟨x, hx, rfl⟩
    have h2 : E' ≤ Λ.comap (MulAut.conj s).toMonoidHom := by
      rintro _ ⟨e, he, rfl⟩
      show s * (s * e * s⁻¹) * s⁻¹ ∈ Λ
      have : s * (s * e * s⁻¹) * s⁻¹ = e := by
        calc s * (s * e * s⁻¹) * s⁻¹ = (s * s) * e * (s * s)⁻¹ := by group
          _ = e := by rw [hs2]; simp
      rw [this]
      exact Subgroup.mem_sup_left he
    intro x hx
    exact (sup_le h1 h2 : Λ ≤ Λ.comap (MulAut.conj s).toMonoidHom) hx
  obtain ⟨R, hRn, hRp, hRmem⟩ :=
    commutator_image_normal_two (X := X) ψ hψs hwΛ hOO hΛOO hW₂ hW₂OO hQ hV
  set R' : Subgroup (↥C ⧸ pPrimeCore 2 ↥C) := R.map (K₁ ⊔ K₂).subtype with hR'
  have hRQ : R' ≤ K₁ ⊔ K₂ := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hRn' : ∀ q ∈ K₁ ⊔ K₂, ∀ ρ ∈ R', q * ρ * q⁻¹ ∈ R' := by
    rintro q hq _ ⟨ρ, hρ, rfl⟩
    exact ⟨⟨q, hq⟩ * ρ * ⟨q, hq⟩⁻¹, hRn.conj_mem ρ hρ ⟨q, hq⟩, rfl⟩
  have hRp' : IsPGroup 2 ↥R' :=
    hRp.of_equiv (Subgroup.equivMapOfInjective R (K₁ ⊔ K₂).subtype (K₁ ⊔ K₂).subtype_injective)
  have hmem : ∀ k ∈ K₁, ∃ k' ∈ K₂, k * k'⁻¹ ∈ R' := by
    intro k hk
    rw [← hKE₁] at hk
    obtain ⟨ec, hec, rfl⟩ := hk
    have heE : (ec : X) ∈ E := hec
    have hse : s * (ec : X) * s⁻¹ ∈ E' := ⟨ec, heE, rfl⟩
    have hseC : s * (ec : X) * s⁻¹ ∈ C := hE'C hse
    refine ⟨π ⟨s * (ec : X) * s⁻¹, hseC⟩, ?_, ?_⟩
    · rw [← hKE₂]
      exact ⟨⟨_, hseC⟩, hse, rfl⟩
    · have hxΛ : (ec : X) ∈ Λ := Subgroup.mem_sup_left heE
      have hcΛ : ⁅(ec : X), s⁆ ∈ Λ := by
        have e : ⁅(ec : X), s⁆ = (ec : X) * (s * (ec : X)⁻¹ * s⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Λ.mul_mem hxΛ (hwΛ _ (Λ.inv_mem hxΛ))
      refine ⟨ψ ⟨⁅(ec : X), s⁆, hcΛ⟩, hRmem ⟨(ec : X), hxΛ⟩ hcΛ, ?_⟩
      change ψ₀ ⟨⁅(ec : X), s⁆, hcΛ⟩ = _
      have hC1 : (⟨⁅(ec : X), s⁆, hΛC hcΛ⟩ : ↥C) = ec * (⟨s * (ec : X) * s⁻¹, hseC⟩ : ↥C)⁻¹ := by
        apply Subtype.ext
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      change π ⟨⁅(ec : X), s⁆, hΛC hcΛ⟩ = _
      rw [hC1, map_mul, map_inv]
  exact swap_central_contra hK₁c.1 hcomm₁₂ hRQ hRn' hRp' hmem

end Contra

section SwapA

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))} {s : X}

theorem K0_inf_centralizer_eq_bot_of_swap (hF : Solomon75Frac53) (h : Sec5Data X n z Z S)
    (hs : IsSec5Inv X Z s) {A : Subgroup X} (hA : Sec5Comp X n (normalizer (Z : Set X)) A)
    (hAs : A.map (MulAut.conj s).toMonoidHom ≠ A) {v : X} (hvZ : v ∈ Z) (hv1 : v ≠ 1) :
    K0 X n (K0 X n (centralizer ({s} : Set X)) ⊓ centralizer ({v} : Set X)) = ⊥ := by
  classical
  have hn : 8 ≤ n := h.maxdeg.1
  have hZs : Z ≤ centralizer ({s} : Set X) := Z_le_centralizer_of_frac53 hF h hs
  have hv2 : v * v = 1 := h.Z_sq_eq_one hvZ
  have hv2' : v ^ 2 = 1 := by rw [sq]; exact hv2
  have hv2o : orderOf v = 2 := h.orderOf_eq_two_of_mem_Z hvZ hv1
  have hvs : v * s = s * v := Subgroup.mem_centralizer_singleton_iff.1 (hZs hvZ)
  by_contra hcon
  obtain ⟨Zs, hZs', hvZs, -⟩ := exists_mirror_sylow_normalized X n (s := s)
    (B := Subgroup.zpowers v) (aux_isPGroup_zpowers_of_sq hv2')
    (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hvs))
  obtain ⟨g, S₁, -, -, -, hS₁⟩ := h.exists_mirror_of_sylow hs hZs'
  have hvNs : v ∈ normalizer (Zs : Set X) := hvZs (Subgroup.mem_zpowers v)
  have hJ := exists_K0_normalizer_inf_ne_bot hS₁ hv2o hvs hvNs hcon
  have hL34 := hS₁.l52.c v hvNs hv2o hJ
  obtain ⟨M, E, hMc, hMs, hEA, hEM, hEn, hcov⟩ := exists_swapped_comp h hs hA hAs
  have hzs : z * s = s * z := Subgroup.mem_centralizer_singleton_iff.1 (hZs h.z_mem)
  have hsCz : s ∈ centralizer ({z} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.2 hzs.symm
  have hsCv : s ∈ centralizer ({v} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hvs.symm
  set M' : Subgroup X := M.map (MulAut.conj s).toMonoidHom with hM'
  set E' : Subgroup X := E.map (MulAut.conj s).toMonoidHom with hE'
  have hMc' : Sec5Comp X n (centralizer ({z} : Set X)) M' :=
    hMc.map_conj (Subgroup.le_normalizer hsCz)
  have hE'M' : E' ≤ M' := Subgroup.map_mono hEM
  have hE'n : IsDoubleCoverOfAlt (↥E' ⧸ pPrimeCore 2 ↥E') n := by
    let ψ : ↥E ≃* ↥E' := Subgroup.equivMapOfInjective E _ (MulAut.conj s).injective
    obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv ψ
    exact isDoubleCoverOfAlt_congr' f hEn
  have hcov' : E'.subgroupOf M' ⊔ pPrimeCore 2 ↥M' = ⊤ :=
    covers_of_card_le hE'M' (by
      rw [natCard_eq_factorial_of_isDoubleCoverOfAlt (by omega) hMc'.2,
        natCard_eq_factorial_of_isDoubleCoverOfAlt (by omega) hE'n])
  have hEL : E ≤ LPlusIn (centralizer ({v} : Set X)) :=
    hEA.trans (hA.le_LPlusIn_centralizer h hvZ hv1)
  have hE'L : E' ≤ LPlusIn (centralizer ({v} : Set X)) := by
    rintro _ ⟨e, he, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_LPlusIn _ hsCv) e).1 (hEL he)
  have hΛL : E ⊔ E' ≤ LPlusIn (centralizer ({v} : Set X)) := sup_le hEL hE'L
  set OO : Subgroup X := pPrimeCoreOf 2 (LPlusIn (centralizer ({v} : Set X))) with hOO
  have hCn : centralizer ({v} : Set X) ≤ normalizer (OO : Set X) :=
    (le_normalizer_LPlusIn _).trans (normalizer_le_normalizer_pPrimeCoreOf _)
  refine swap_contra (C := centralizer ({z} : Set X)) hs.sq hMc hMc' hMs hEM hcov hcov'
    (OO := OO) (W₂ := Zs ⊓ centralizer ({v} : Set X)) (odd_card_oddCoreOf _)
    (fun x hx => hCn (LPlusIn_le _ (hΛL hx))) (hS₁.isPGroup_Z.to_le inf_le_left)
    (inf_le_right.trans hCn) ?_
  intro x hx
  obtain ⟨o, ho, w, hw, hxs⟩ := commutator_decomp_of_mirror hS₁.pair.mem hvs hL34 (hΛL hx)
  rw [hxs]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ho) (Subgroup.mem_sup_right hw)

end SwapA

end CFSG.OddStandard.Solomon75
