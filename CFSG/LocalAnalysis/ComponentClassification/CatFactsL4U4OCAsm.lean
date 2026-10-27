module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OCUb
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InputsOuter

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OutInv

open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag DiagL CSL DiagU
  CFSG.ComponentClassification.GSThmB CFSG.Assembly.LowTwoRank

section Transport

variable {G X : Type} [Group G] [Group X] {N : Subgroup G} [N.Normal] (e : ↥N ≃* X)
  (Φ : G →* MulAut X) (hΦ : ∀ (g : G) (x : ↥N), Φ g (e x) = e (MulAut.conjNormal g x))

include hΦ in
theorem fix_of_comm {J : Subgroup G} {g : G} (hg : ∀ j ∈ J, g * j * g⁻¹ = j) :
    ∀ x ∈ (J.subgroupOf N).map e.toMonoidHom, Φ g x = x := by
  rintro _ ⟨z, hz, rfl⟩
  change Φ g (e z) = e z
  rw [hΦ]
  congr 1
  exact Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hg _ (mem_subgroupOf.1 hz))

include hΦ in
theorem fixSub_component {α : G} {J : Subgroup G} (hJN : J ≤ N)
    (hJα : J ≤ centralizer ({α} : Set G))
    (hJ : IsComponent (J.subgroupOf (centralizer ({α} : Set G)))) :
    (J.subgroupOf N).map e.toMonoidHom ≤ fixSub (Φ α) ∧
      IsComponent (((J.subgroupOf N).map e.toMonoidHom).subgroupOf (fixSub (Φ α))) := by
  set J' := (J.subgroupOf N).map e.toMonoidHom with hJ'
  have hαfix : ∀ j ∈ J, α * j * α⁻¹ = j := fun j hj => by
    have := mem_centralizer_singleton_iff.mp (hJα hj)
    rw [← this]; group
  have hle : J' ≤ fixSub (Φ α) := fun x hx => fix_of_comm e Φ hΦ hαfix x hx
  refine ⟨hle, ?_, ?_⟩
  · have iso : ↥(J.subgroupOf (centralizer ({α} : Set G))) ≃* ↥(J'.subgroupOf (fixSub (Φ α))) :=
      (Subgroup.subgroupOfEquivOfLe hJα).trans (((Subgroup.subgroupOfEquivOfLe hJN).symm.trans
        (e.subgroupMap (J.subgroupOf N))).trans (Subgroup.subgroupOfEquivOfLe hle).symm)
    exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv iso hJ.1
  · have hmemC : ∀ y : ↥(fixSub (Φ α)),
        ((e.symm (y : X) : ↥N) : G) ∈ centralizer ({α} : Set G) := by
      intro y
      rw [mem_centralizer_singleton_iff]
      have h1 : Φ α (e (e.symm (y : X))) = e (e.symm (y : X)) := by
        rw [MulEquiv.apply_symm_apply]
        exact y.2
      rw [hΦ] at h1
      have h2 := congrArg Subtype.val (e.injective h1)
      rw [MulAut.conjNormal_apply] at h2
      calc ((e.symm (y : X) : ↥N) : G) * α =
          α * ((e.symm (y : X) : ↥N) : G) * α⁻¹ * α := by rw [h2]
        _ = α * ((e.symm (y : X) : ↥N) : G) := by group
    set fh : ↥(fixSub (Φ α)) →* ↥(centralizer ({α} : Set G)) :=
      MonoidHom.codRestrict ((N.subtype.comp e.symm.toMonoidHom).comp (fixSub (Φ α)).subtype) _
        hmemC with hfh
    have hcomap : (J.subgroupOf (centralizer ({α} : Set G))).comap fh =
        J'.subgroupOf (fixSub (Φ α)) := by
      ext y
      rw [mem_comap, mem_subgroupOf, mem_subgroupOf]
      change ((e.symm (y : X) : ↥N) : G) ∈ J ↔ (y : X) ∈ J'
      constructor
      · intro hy
        exact ⟨e.symm y, mem_subgroupOf.2 hy, by simp⟩
      · rintro ⟨z, hz, hzy⟩
        have hz' : e.symm (y : X) = z := by
          rw [← hzy]
          exact e.symm_apply_apply z
        rw [hz']
        exact mem_subgroupOf.1 hz
    rw [← hcomap]
    exact hJ.2.comap fh

omit [N.Normal] in
theorem lieModel_map {J : Subgroup G} (hJN : J ≤ N) {t : StatedLieTag} {n p f : ℕ}
    (hJ : Blueprint.LieModel (↥J ⧸ center ↥J) t n p f) :
    Blueprint.LieModel (↥((J.subgroupOf N).map e.toMonoidHom) ⧸
      center ↥((J.subgroupOf N).map e.toMonoidHom)) t n p f := by
  let iso : ↥J ≃* ↥((J.subgroupOf N).map e.toMonoidHom) :=
    (Subgroup.subgroupOfEquivOfLe hJN).symm.trans (e.subgroupMap (J.subgroupOf N))
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.congr (center ↥J) (center _) iso (Subgroup.map_center_eq iso)) hJ

end Transport

variable {G : Type} [Group G] [Finite G] {N : Subgroup G} {p f : ℕ} {α : G} {J : Subgroup G}

theorem outer_L4 (hI : OuterInvCentL4) (hcfg : OuterL2Config G N p f α J) (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hL : Blueprint.LieModel ↥N .PSL 4 p f) {τ : G}
    (hτα : τ * α = α * τ) (hτJ : ∀ x ∈ J, τ * x = x * τ) (hτ2 : ∃ k : ℕ, τ ^ 2 ^ k = 1) :
    τ ∈ zpowers α := by
  classical
  have hcfg' := hcfg
  obtain ⟨hNn, hC, -, hα2, -, hJα, hJc, hJ, hstd⟩ := hcfg
  have : N.Normal := hNn
  obtain ⟨-, F, _, _, hF, ⟨eL⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hL
  let : Fintype F := Fintype.ofFinite F
  have hFq : Fintype.card F = p ^ f := by rw [Fintype.card_eq_nat_card, hF]
  set e : ↥N ≃* projectiveSL 4 F :=
    eL.trans ((projectiveSpecialLinearGroupEquivStatedProj 4 F).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 4 F).symm)) with he
  by_cases hd : actP e α ∈ (conjAut 4 F).range
  · obtain ⟨A, hA⟩ := hd
    exact OCL.outer_diag_L4 hcfg' hp hp2 hf hFq e hA.symm hτα hτJ hτ2
  have hJq : IsQuasisimple ↥J := hstd.1
  have hJp : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJq.1
  have hJN : J ≤ N := AZ.le_of_perfect_of_le_inner N hC
    (AZ.le_inner_of_mulEquiv e (fun J hJ => DiagL.le_range_conj_of_perfect hJ)) hJp
  have hΦ : ∀ (g : G) (x : ↥N), actP e g (e x) = e (MulAut.conjNormal g x) := actP_apply e
  obtain ⟨hle, hcomp⟩ := fixSub_component e (actP e) hΦ hJN hJα hJc
  have hαα : α * α = 1 := by rw [← sq, ← hα2, pow_orderOf_eq_one]
  have hφ2 : actP e α ^ 2 = 1 := by rw [← map_pow, sq, hαα, map_one]
  have hψφ : actP e τ * actP e α = actP e α * actP e τ := by rw [← map_mul, ← map_mul, hτα]
  have hψJ := fix_of_comm e (actP e) hΦ (J := J) (g := τ) (fun j hj => by
    rw [hτJ j hj, mul_inv_cancel_right])
  obtain ⟨k, hk⟩ := hτ2
  have hmem := (hI F p f hp hp2 hf hFq (actP e α) hφ2 hd _ hle hcomp (lieModel_map e hJN hJ)).1
    (actP e τ) hψφ hψJ ⟨k, by rw [← map_pow, hk, map_one]⟩
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hmem
  have h1 : actP e (τ * (α ^ n)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_zpow, hn, mul_inv_cancel]
  rw [mul_inv_eq_one.mp (eq_one_of_actP_eq_one hC e h1)]
  exact zpow_mem (mem_zpowers α) n

theorem outer_U4 (hI : OuterInvCentU4) (hcfg : OuterL2Config G N p f α J) (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hU : Blueprint.LieModel ↥N .PSU 4 p f) {τ : G}
    (hτα : τ * α = α * τ) (hτJ : ∀ x ∈ J, τ * x = x * τ) (hτ2 : ∃ k : ℕ, τ ^ 2 ^ k = 1) :
    τ ∈ zpowers α := by
  classical
  have hcfg' := hcfg
  obtain ⟨hNn, hC, -, hα2, -, hJα, hJc, hJ, hstd⟩ := hcfg
  have : N.Normal := hNn
  obtain ⟨-, K, _, _, hK, ⟨eU⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hU
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  by_cases hd : AZ.actE eU α ∈ InnU p f K h
  · obtain ⟨A, hA⟩ := hd
    exact OCU.outer_diag_U4 hcfg' hp hp2 hf h eU hA hτα hτJ hτ2
  have hJq : IsQuasisimple ↥J := hstd.1
  have hJp : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJq.1
  have hJN : J ≤ N := AZ.le_of_perfect_of_le_inner N hC
    (AZ.le_inner_of_mulEquiv eU (fun J hJ => DiagU.le_range_conj_of_perfect_U h hp2 hJ)) hJp
  have hΦ : ∀ (g : G) (x : ↥N), AZ.actE eU g (eU x) = eU (MulAut.conjNormal g x) :=
    AZ.actE_apply eU
  obtain ⟨hle, hcomp⟩ := fixSub_component eU (AZ.actE eU) hΦ hJN hJα hJc
  have hαα : α * α = 1 := by rw [← sq, ← hα2, pow_orderOf_eq_one]
  have hφ2 : AZ.actE eU α ^ 2 = 1 := by rw [← map_pow, sq, hαα, map_one]
  have hψφ : AZ.actE eU τ * AZ.actE eU α = AZ.actE eU α * AZ.actE eU τ := by
    rw [← map_mul, ← map_mul, hτα]
  have hψJ := fix_of_comm eU (AZ.actE eU) hΦ (J := J) (g := τ) (fun j hj => by
    rw [hτJ j hj, mul_inv_cancel_right])
  obtain ⟨k, hk⟩ := hτ2
  have hmem := (hI K p f h hp2 (AZ.actE eU α) hφ2 hd _ hle hcomp (lieModel_map eU hJN hJ)).1
    (AZ.actE eU τ) hψφ hψJ ⟨k, by rw [← map_pow, hk, map_one]⟩
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hmem
  have h1 : AZ.actE eU (τ * (α ^ n)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_zpow, hn, mul_inv_cancel]
  rw [mul_inv_eq_one.mp (AZ.eq_one_of_actE_eq_one hC eU h1)]
  exact zpow_mem (mem_zpowers α) n

omit [Finite G] in
theorem outer_O8 (hI : OuterInvCentO8) (hcfg : OuterL2Config G N p f α J) (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hJN : J ≤ N) {e : ℕ} (he : f = 2 * e)
    (hO : Blueprint.LieModel ↥N .POmegaMinus 4 p e) {τ : G} (hτα : τ * α = α * τ)
    (hτJ : ∀ x ∈ J, τ * x = x * τ) (hτ2 : ∃ k : ℕ, τ ^ 2 ^ k = 1) : τ ∈ zpowers α := by
  classical
  obtain ⟨hNn, hC, -, hα2, hαN, hJα, hJc, hJ, -⟩ := hcfg
  have : N.Normal := hNn
  obtain ⟨-, K, _, _, hK, b, c, hbc, ⟨eO⟩⟩ :=
    statedClassicalModel_of_lieModel_ne_zero (by norm_num) hO
  let : Fintype K := Fintype.ofFinite K
  have hKq : Fintype.card K = p ^ e := by rw [Fintype.card_eq_nat_card, hK]
  have he1 : 1 ≤ e := by omega
  set Φ := AZ.actE eO with hΦdef
  have hΦ : ∀ (g : G) (x : ↥N), Φ g (eO x) = eO (MulAut.conjNormal g x) := AZ.actE_apply eO
  have hout : Φ α ∉
      (MulAut.conj : StatedProj (StatedOmega (StatedQuadMinus 4 K b c)) →* _).range := by
    rintro ⟨y, hy⟩
    apply hαN
    set x : G := (eO.symm y : G) with hx
    have hxN : x ∈ N := (eO.symm y).2
    have hex : eO ⟨x, hxN⟩ = y := by simp [hx]
    have h1 : Φ (α * x⁻¹) = 1 := by
      rw [map_mul, map_inv, hΦdef, CSU.actE_eq_conj eO hxN, hex, ← hΦdef, ← hy, mul_inv_cancel]
    rw [mul_inv_eq_one.mp (AZ.eq_one_of_actE_eq_one hC eO h1)]
    exact hxN
  obtain ⟨hle, hcomp⟩ := fixSub_component eO Φ hΦ hJN hJα hJc
  have hαα : α * α = 1 := by rw [← sq, ← hα2, pow_orderOf_eq_one]
  have hφ2 : Φ α ^ 2 = 1 := by rw [← map_pow, sq, hαα, map_one]
  have hψφ : Φ τ * Φ α = Φ α * Φ τ := by rw [← map_mul, ← map_mul, hτα]
  have hψJ := fix_of_comm eO Φ hΦ (J := J) (g := τ) (fun j hj => by
    rw [hτJ j hj, mul_inv_cancel_right])
  have hJ' := lieModel_map eO hJN hJ
  rw [he] at hJ'
  obtain ⟨k, hk⟩ := hτ2
  have hmem := (hI K p e hp hp2 he1 hKq b c hbc (Φ α) hφ2 hout _ hle hcomp hJ').1 (Φ τ) hψφ hψJ
    ⟨k, by rw [← map_pow, hk, map_one]⟩
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hmem
  have h1 : Φ (τ * (α ^ n)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_zpow, hn, mul_inv_cancel]
  rw [mul_inv_eq_one.mp (AZ.eq_one_of_actE_eq_one hC eO h1)]
  exact zpow_mem (mem_zpowers α) n

theorem outerL2Cent_of (hL4 : OuterInvCentL4) (hU4 : OuterInvCentU4) (hO8 : OuterInvCentO8) :
    OuterL2Cent := by
  intro G _ _ N p f hp hp2 hf α J hcfg hJN τ hτα hτJ hτ2
  rcases hcfg.2.2.1 with hL | hU | ⟨e, he, hO⟩
  · exact outer_L4 hL4 hcfg hp hp2 hf hL hτα hτJ hτ2
  · exact outer_U4 hU4 hcfg hp hp2 hf hU hτα hτJ hτ2
  · exact outer_O8 hO8 hcfg hp hp2 hf hJN he hO hτα hτJ hτ2

end OutInv

end CFSG.ComponentClassification.CatFactsL4U4
