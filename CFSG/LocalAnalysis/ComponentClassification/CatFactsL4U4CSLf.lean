module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSLe
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AltCentC
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InputsCenter
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AZ
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSLd

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace CSL

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag DiagL
  CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank

theorem isPGroup_zpowers {X : Type*} [Group X] {g : X} {k : ℕ} (h : g ^ 2 ^ k = 1) :
    IsPGroup 2 ↥(zpowers g) := by
  have hd : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])

theorem proj_kSL_sq {F : Type} [Field F] [Finite F] :
    proj 4 F (kSL : SpecialLinearGroup (Fin 4) F) ^ 2 = 1 := by
  apply conj_injective
  rw [map_pow, ← conjAut_kG_eq, conjAut_kG_sq, map_one]

theorem normalizes_of_conj_mem_CA {F : Type} [Field F] {x : projectiveSL 4 F}
    (hx : MulAut.conj x ∈ CA F neg_one_ne_zero') (y : projectiveSL 4 F) :
    y ∈ JK F neg_one_ne_zero' ↔ x * y * x⁻¹ ∈ JK F neg_one_ne_zero' := by
  constructor
  · intro hy
    have := hx y hy
    rw [MulAut.conj_apply] at this
    rwa [this]
  · intro hy
    have hinv : (MulAut.conj x)⁻¹ ∈ CA F neg_one_ne_zero' := inv_mem hx
    have := hinv _ hy
    rw [← map_inv, MulAut.conj_apply] at this
    have e : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
    rw [e] at this
    rw [this]
    exact hy

theorem centerSylow_L4 {G : Type} [Group G] [Finite G] {N : Subgroup G} {α : G}
    {J R : Subgroup G} {τ : G} (hcfg : OutInv.CenterSylowConfig G N α J R τ) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hαN : α ∈ N)
    (hL : Blueprint.LieModel ↥N .PSL 4 p f)
    (hJ : Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 2 p (2 * f)) : τ ∈ zpowers α := by
  classical
  obtain ⟨hNn, hC, hα2, hJα, -, hstd, hRM, hRα, hRS, hτα, hτJ, hτR, -⟩ := hcfg
  have : N.Normal := hNn
  obtain ⟨-, F, _, _, hF, ⟨eL⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hL
  let : Fintype F := Fintype.ofFinite F
  have hFq : Fintype.card F = p ^ f := by rw [Fintype.card_eq_nat_card, hF]
  have hq : Odd (Fintype.card F) := hFq ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_card_odd hq
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  set e : ↥N ≃* projectiveSL 4 F :=
    eL.trans ((projectiveSpecialLinearGroupEquivStatedProj 4 F).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 4 F).symm)) with he
  have hJq : IsQuasisimple ↥J := hstd.1
  have hJp : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJq.1
  have hJN : J ≤ N := AZ.le_of_perfect_of_le_inner N hC
    (AZ.le_inner_of_mulEquiv e (fun J hJ => DiagL.le_range_conj_of_perfect hJ)) hJp
  have hJtype : IsSec8JType (↥J ⧸ center ↥J) p f := Or.inl hJ
  obtain ⟨s, hs, hs2, hsq, hsJ⟩ := AZ.exists_prime_dvd_card_of_isSec8JType hp hp2 hf hJtype
  have := Fact.mk hs
  obtain ⟨⟨y, hyJ⟩, hys⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) s
    (hsJ.trans (Subgroup.card_quotient_dvd_card _))
  rw [Subgroup.orderOf_mk] at hys
  have hyN := hJN hyJ
  obtain ⟨Yα, hYα⟩ := proj_surjective 4 F (e ⟨α, hαN⟩)
  set A := SpecialLinearGroup.toGL Yα with hA
  have hαA : actP e α = conjAut 4 F A := by rw [actP_eq_conj e hαN, ← hYα, hA, conjAut_toGL]
  have hαα : α * α = 1 := by rw [← sq, ← hα2, pow_orderOf_eq_one]
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hα2
    norm_num at hα2
  have hA1 : conjAut 4 F A ≠ 1 := fun h => hα1 (eq_one_of_actP_eq_one hC e (hαA ▸ h))
  have hA2 : conjAut 4 F A ^ 2 = 1 := by rw [← hαA, ← map_pow, sq, hαα, map_one]
  have hyα : y * α = α * y := mem_centralizer_singleton_iff.mp (hJα hyJ)
  have hAy : conjAut 4 F A (e ⟨y, hyN⟩) = e ⟨y, hyN⟩ := by
    rw [← hαA]
    have := actP_comm_conj e hyN hyα.symm
    rw [← mul_inv_eq_iff_eq_mul, mul_conj_mul_inv] at this
    exact conj_injective this
  have hys' : orderOf (e ⟨y, hyN⟩) = s := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hys]
  obtain ⟨l, hl2, hns⟩ := exists_nonsquare_of_conjAut hq hs hs2 (by rw [hFq]; exact hsq) A hA1
    hA2 hys' hAy
  obtain ⟨P, hP⟩ := exists_conj_eq_kG hns hl2
  have hll : (l : F) = -1 := by
    have hdet : (A : Matrix (Fin 4) (Fin 4) F).det = 1 := Yα.2
    have h1 := congrArg (fun X : GL (Fin 4) F => (X : Matrix (Fin 4) (Fin 4) F).det) hP
    simp only [Units.val_mul, Matrix.det_mul, coe_kG, det_kZero] at h1
    have h3 : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det *
        (P : Matrix (Fin 4) (Fin 4) F).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    have h4' : (l : F) ^ 2 = 1 := by
      rw [← h1, hdet, mul_one, h3]
    have h5 : (l : F) * l = 1 := by rw [← sq]; exact h4'
    rcases mul_self_eq_one_iff.mp h5 with h | h
    · exact absurd ⟨1, by rw [h, mul_one]⟩ hns
    · exact h
  have hneg : ¬ IsSquare (-1 : F) := hll ▸ hns
  have hkG : kG (Units.ne_zero l) = kG (neg_one_ne_zero' (F := F)) :=
    Units.ext (by rw [coe_kG, coe_kG, hll])
  set e' : ↥N ≃* projectiveSL 4 F := e.trans (conjAut 4 F P⁻¹) with he'
  have hα' : actP e' α = conjAut 4 F (kG neg_one_ne_zero') := by
    rw [he', actP_trans, hαA, ← map_inv, ← map_mul, ← map_mul, inv_inv, hP, hkG]
  have hαk : e' ⟨α, hαN⟩ = proj 4 F kSL := by
    apply conj_injective
    rw [← actP_eq_conj, hα', conjAut_kG_eq]
  set J' : Subgroup (projectiveSL 4 F) := (J.subgroupOf N).map e'.toMonoidHom with hJ'
  have hJ'p : ⁅J', J'⁆ = J' := by
    rw [hJ', ← Subgroup.map_commutator, AZ.subgroupOf_perfect hJN hJp]
  have hfix : ∀ g : G, (∀ j ∈ J, g * j * g⁻¹ = j) → ∀ x ∈ J', actP e' g x = x := by
    rintro g hg _ ⟨z, hz, rfl⟩
    change actP e' g (e' z) = e' z
    rw [actP_apply]
    congr 1
    exact Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hg _ (mem_subgroupOf.1 hz))
  have hJ'k : ∀ x ∈ J', conjAut 4 F (kG neg_one_ne_zero') x = x := by
    rw [← hα']
    refine hfix α fun j hj => ?_
    have := mem_centralizer_singleton_iff.mp (hJα hj)
    rw [← this]; group
  have hcJ : Nat.card J' = Nat.card J := by
    rw [hJ', Subgroup.card_map_of_injective e'.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJN).toEquiv]
  have hcard : Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) ≤ 2 * Nat.card J' := by
    have h1 := AZ.two_mul_card_of_isSec8JType hp hp2 hJtype
    have h2' := Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card (center ↥J))
    rw [hcJ, hF, show ((p ^ f) ^ 2) ^ 2 = (p ^ f) ^ 4 by ring, ← h1]
    omega
  have hJK : J' = JK F neg_one_ne_zero' := eq_JK h2 neg_one_ne_zero' hneg hJ'k hJ'p hcard
  have hτ' : actP e' τ ∈ CA F neg_one_ne_zero' := by
    intro x hx
    rw [← hJK] at hx
    refine hfix τ (fun j hj => ?_) x hx
    rw [hτJ j hj, mul_inv_cancel_right]
  obtain ⟨c, hc⟩ := exists_c hneg h2
  set xu := proj 4 F (uSL hc) with hxu
  set xs := proj 4 F (sSL : SpecialLinearGroup (Fin 4) F) with hxs
  set u : G := (e'.symm xu : G) with hu
  set w : G := (e'.symm xs : G) with hw
  have huN : u ∈ N := (e'.symm xu).2
  have hwN : w ∈ N := (e'.symm xs).2
  have heu : e' ⟨u, huN⟩ = xu := by simp [hu]
  have hew : e' ⟨w, hwN⟩ = xs := by simp [hw]
  have hM : ∀ {g : G} (hgN : g ∈ N), (∀ x, x ∈ JK F neg_one_ne_zero' ↔
      e' ⟨g, hgN⟩ * x * (e' ⟨g, hgN⟩)⁻¹ ∈ JK F neg_one_ne_zero') →
      e' ⟨g, hgN⟩ * proj 4 F kSL = proj 4 F kSL * e' ⟨g, hgN⟩ →
      g ∈ (N ⊓ normalizer (J : Set G)) ⊓ centralizer ({α} : Set G) := by
    intro g hgN hgJ hgk
    refine mem_inf.2 ⟨mem_inf.2 ⟨hgN, mem_normalizer_of_normalizes e' hJN hgN ?_⟩, ?_⟩
    · rw [← hJ', hJK]
      exact hgJ
    · rw [mem_centralizer_singleton_iff]
      have h1 : e' (⟨g, hgN⟩ * ⟨α, hαN⟩) = e' (⟨α, hαN⟩ * ⟨g, hgN⟩) := by
        rw [map_mul, map_mul, hαk, hgk]
      exact congrArg Subtype.val (e'.injective h1)
  have hxuk : xu * proj 4 F kSL = proj 4 F kSL * xu := by
    rw [hxu, ← proj_uSL_sq hc, ← pow_succ, ← pow_succ']
  have huM := hM huN (by rw [heu]; exact normalizes_of_conj_mem_CA (conj_uSL_mem_CA hc))
    (by rw [heu]; exact hxuk)
  have hxs2 : xs * xs = 1 := by rw [← sq, hxs, proj_sSL_sq]
  have hxs_inv : xs⁻¹ = xs := inv_eq_of_mul_eq_one_right hxs2
  have hwM := hM hwN (by
      rw [hew]
      intro x
      constructor
      · intro hx
        have := conj_sSL_mem_JK hx
        rwa [MulAut.conj_apply, ← hxs] at this
      · intro hx
        have := conj_sSL_mem_JK hx
        rw [MulAut.conj_apply, ← hxs] at this
        have e2 : xs * (xs * x * xs⁻¹) * xs⁻¹ = x := by
          rw [hxs_inv]
          calc xs * (xs * x * xs) * xs = (xs * xs) * x * (xs * xs) := by group
            _ = x := by rw [hxs2, one_mul, mul_one]
        rwa [e2] at this)
    (by
      rw [hew]
      have h1 : MulAut.conj (xs * proj 4 F kSL) = MulAut.conj (proj 4 F kSL * xs) := by
        rw [map_mul, map_mul, hxs, ← conjAut_kG_eq]
        exact conj_sSL_comm
      exact conj_injective h1)
  have hu4 : u ^ 2 ^ 2 = 1 := by
    have h1 : e' ⟨u, huN⟩ ^ 4 = 1 := by
      rw [heu, show xu ^ 4 = (xu ^ 2) ^ 2 by rw [← pow_mul], hxu, proj_uSL_sq hc,
        proj_kSL_sq]
    have h2 : (⟨u, huN⟩ : ↥N) ^ 4 = 1 := by
      apply e'.injective
      rw [map_pow, h1, map_one]
    have := congrArg Subtype.val h2
    simpa using this
  have hw2 : w ^ 2 ^ 1 = 1 := by
    have h1 : e' ⟨w, hwN⟩ ^ 2 = 1 := by rw [hew, hxs, proj_sSL_sq]
    have h2 : (⟨w, hwN⟩ : ↥N) ^ 2 = 1 := by
      apply e'.injective
      rw [map_pow, h1, map_one]
    have := congrArg Subtype.val h2
    simpa using this
  have hzle : ∀ {g : G}, g ∈ (N ⊓ normalizer (J : Set G)) ⊓ centralizer ({α} : Set G) →
      zpowers g ≤ (N ⊓ normalizer (J : Set G)) ⊓ centralizer ({α} : Set G) :=
    fun hg => zpowers_le.mpr hg
  obtain ⟨c₁, hc₁, hc₁R⟩ := AltCent.exists_conj_le hRM hRα hRS (hzle huM) (isPGroup_zpowers hu4)
  obtain ⟨c₂, hc₂, hc₂R⟩ := AltCent.exists_conj_le hRM hRα hRS (hzle hwM) (isPGroup_zpowers hw2)
  have hc₁N : c₁ ∈ N := (mem_inf.1 (mem_inf.1 hc₁).1).1
  have hc₂N : c₂ ∈ N := (mem_inf.1 (mem_inf.1 hc₂).1).1
  have hc₁J : c₁ ∈ normalizer (J : Set G) := (mem_inf.1 (mem_inf.1 hc₁).1).2
  have hc₂J : c₂ ∈ normalizer (J : Set G) := (mem_inf.1 (mem_inf.1 hc₂).1).2
  have hc₁α : c₁ * α = α * c₁ := mem_centralizer_singleton_iff.mp (mem_inf.1 hc₁).2
  have hc₂α : c₂ * α = α * c₂ := mem_centralizer_singleton_iff.mp (mem_inf.1 hc₂).2
  have hcomm : ∀ {g : G} (hgN : g ∈ N), g * α = α * g →
      e' ⟨g, hgN⟩ * proj 4 F kSL = proj 4 F kSL * e' ⟨g, hgN⟩ := by
    intro g hgN hgα
    rw [← hαk, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hgα
  have hτcomm : ∀ {g x : G} (hgN : g ∈ N) (hxN : x ∈ N), g * x * g⁻¹ ∈ R →
      actP e' τ * MulAut.conj (e' ⟨g, hgN⟩ * e' ⟨x, hxN⟩ * (e' ⟨g, hgN⟩)⁻¹) =
        MulAut.conj (e' ⟨g, hgN⟩ * e' ⟨x, hxN⟩ * (e' ⟨g, hgN⟩)⁻¹) * actP e' τ := by
    intro g x hgN hxN hR
    have hm : g * x * g⁻¹ ∈ N := mul_mem (mul_mem hgN hxN) (inv_mem hgN)
    have h1 := actP_comm_conj e' hm (hτR _ hR)
    have e1 : e' ⟨g * x * g⁻¹, hm⟩ = e' ⟨g, hgN⟩ * e' ⟨x, hxN⟩ * (e' ⟨g, hgN⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rwa [e1] at h1
  have h₁ := hτcomm hc₁N huN (hc₁R u (mem_zpowers u))
  have h₂ := hτcomm hc₂N hwN (hc₂R w (mem_zpowers w))
  rw [heu] at h₁
  rw [hew] at h₂
  rcases eq_one_or_eq_kG h4 hτ' (x₁ := e' ⟨c₁, hc₁N⟩) (x₂ := e' ⟨c₂, hc₂N⟩)
      (by rw [← hJK]; exact normalizes_of_mem_normalizer e' hc₁N hc₁J)
      (by rw [← hJK]; exact normalizes_of_mem_normalizer e' hc₂N hc₂J)
      (hcomm hc₁N hc₁α) (hcomm hc₂N hc₂α) hc h₁ h₂ with h | h
  · have : τ = 1 := eq_one_of_actP_eq_one hC e' h
    rw [this]
    exact one_mem _
  · have : τ = α := by
      have h1 : actP e' (τ * α⁻¹) = 1 := by rw [map_mul, map_inv, h, hα', mul_inv_cancel]
      exact mul_inv_eq_one.mp (eq_one_of_actP_eq_one hC e' h1)
    rw [this]
    exact mem_zpowers α

end CSL

end CFSG.ComponentClassification.CatFactsL4U4
