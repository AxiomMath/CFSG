module

public import CFSG.GH74.Generic.BProg.B2.T4P151L
public import CFSG.GH74.Generic.BProg.B2.ShapeGenS13
public import CFSG.GH74.Generic.S3.L3Cover
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicQuot

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.P151P

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup
open CFSG.GH74.Generic.BProg.B2.T4.P151G CFSG.GH74.Generic.BProg.B2.T4.P151L CFSG.RankThree.PerfectCover
open scoped commutatorElement

theorem genInner_of_isL3Odd {J : Type} [Group J] (h : IsL3Odd J) : GenLocL5Out.GenInner J := by
  obtain ⟨p, f, hp, hp2, hm | hm⟩ := h
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := GenLocL5Out.stated_PSL hm
    let ψ : J ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
      e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F))
    exact GenLocL5Out.GenInner.of_mulEquiv ψ.symm (ShapeGenS13.genInner_projectiveSL3 hp hp2 hF)
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := GenLocL5Out.stated_PSU hm
    exact GenLocL5Out.GenInner.of_mulEquiv e.symm (ShapeGenS13.genInner_statedSU3 hp hp2 hK)

section Cover

variable {L : Type} [Group L] [Finite L]

omit [Finite L] in
theorem not_mem_center_of_invol (hZ : Odd (Nat.card ↥(center L))) {u : L} (huu : u * u = 1) (hu1 : u ≠ 1) :
    u ∉ center L := by
  intro hu
  have h2 : orderOf (⟨u, hu⟩ : ↥(center L)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq]; exact huu) hu1
  have hdvd := orderOf_dvd_natCard (⟨u, hu⟩ : ↥(center L))
  rw [h2] at hdvd
  exact absurd (Odd.of_dvd_nat hZ hdvd) (by decide)

theorem sup_centralizer_eq_top_of_L3 (hq : IsQuasisimple L) (hT : IsL3Odd (L ⧸ center L))
    (hZ : Odd (Nat.card ↥(center L))) {u₁ u₂ : L} (h₁ : u₁ * u₁ = 1) (h₂ : u₂ * u₂ = 1)
    (h₁₂ : u₁ * u₂ = u₂ * u₁) (h₁1 : u₁ ≠ 1) (h₂1 : u₂ ≠ 1) (hne : u₁ ≠ u₂) :
    centralizer ({u₁} : Set L) ⊔ centralizer ({u₂} : Set L) ⊔ centralizer ({u₁ * u₂} : Set L) = ⊤ := by
  classical
  set E : Subgroup L := zpowers u₁ ⊔ zpowers u₂ with hEdef
  have hc₁₂ : ∀ h ∈ zpowers u₁, h * u₂ = u₂ * h := by
    intro h hh
    obtain h' | h' := mem_zpowers_invol h₁ hh
    · rw [h']; simp
    · rw [h']; exact h₁₂
  have hEel : CFSG.IsElementaryAbelian 2 ↥E :=
    B3.S3Sec29H.isElementaryAbelian_sup_zpowers (isElementaryAbelian_zpowers_invol h₁) h₂ hc₁₂
  have hE4 : Nat.card ↥E = 4 := card_four h₁ h₂ h₁₂ h₁1 h₂1 hne
  have hrank : pRank 2 ↥E = 2 := by
    have h1 := WeakSigGen.card_eq_two_pow_pRank hEel
    rw [hE4] at h1
    have h2 : 2 ^ pRank 2 ↥E = 2 ^ 2 := by rw [← h1]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  set α : ↥E →* MulAut L := ShapeGenS13.conjOn E with hα
  set ρ : ↥E →* L ⧸ center L := (QuotientGroup.mk' (center L)).comp E.subtype with hρ
  set α' : ↥E →* MulAut (L ⧸ center L) := (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).comp ρ
    with hα'
  have hcompat : ∀ (a : ↥E) (x : L), α' a (QuotientGroup.mk x) = QuotientGroup.mk (α a x) := by
    intro a x
    simp only [hα', hρ, hα, MonoidHom.comp_apply, MulAut.conj_apply, ShapeGenS13.conjOn_apply]
    rfl
  have hγ' : gammaAct α' = ⊤ :=
    genInner_of_isL3Odd hT ↥E α' ⟨hEel, Or.inl hrank⟩ (by rintro _ ⟨b, rfl⟩; exact ⟨ρ b, rfl⟩)
  have hperf : commutator L = ⊤ := by
    have : Group.IsPerfect L := hq.1
    exact Group.IsPerfect.commutator_eq_top
  have hγ : gammaAct α = ⊤ :=
    gammaAct_eq_top_of_quotient hEel hperf (center L) le_rfl hZ α α' hcompat hγ'
  have hnc : ∀ E' : Subgroup ↥E, pRank 2 ↥E - 1 ≤ pRank 2 ↥E' → ∃ b ∈ E', (b : L) ∉ center L := by
    intro E' hE'
    obtain ⟨b, hbE', hb1⟩ := ShapeGenS13.exists_ne_one_of_one_le_pRank (E := E') (by omega)
    refine ⟨b, hbE', not_mem_center_of_invol hZ ?_ ?_⟩
    · exact congrArg Subtype.val (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hEel b)
    · intro h
      exact hb1 (Subtype.ext h)
  have hsup := ShapeGenS13.shapeGen_of_gammaAct hnc hγ
  refine eq_top_iff.2 (hsup.symm.le.trans ?_)
  refine iSup₂_le fun b hb => ?_
  obtain ⟨hbE, hbZ⟩ := hb
  rcases mem_four h₁ h₂ h₁₂ hbE with rfl | rfl | rfl | rfl
  · exact absurd (Subgroup.one_mem _) hbZ
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

theorem odd_card_center_of_isL3Odd (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hq : IsQuasisimple L) (hT : IsL3Odd (L ⧸ center L)) : Odd (Nat.card ↥(center L)) := by
  obtain ⟨p, f, hp, hp2, hm⟩ := hT
  have hM : Odd (Nat.card (hopfMultiplier (L ⧸ center L))) := by
    rcases hm with hm | hm
    · have hm' : CFSG.Models.LieModel (L ⧸ center L) .PSL 3 p f :=
        models_of_blueprint_of_ne_zero (by norm_num) hm
      rw [S3.card_hopfMultiplier_psl_three hGA hp2 hm']
      exact odd_gcd_of_odd_left (by decide)
    · have hm' : CFSG.Models.LieModel (L ⧸ center L) .PSU 3 p f :=
        models_of_blueprint_of_ne_zero (by norm_num) hm
      rw [S3.card_hopfMultiplier_psu_three hGA hm']
      exact odd_gcd_of_odd_left (by decide)
  have hperf : Group.IsPerfect L := hq.1
  have hd := card_ker_dvd_hopfMultiplier hperf (QuotientGroup.mk' (center L)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk'])
  rw [QuotientGroup.ker_mk'] at hd
  exact Odd.of_dvd_nat hM hd

end Cover

section Cases

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem le_sup_of_top {L : Subgroup X} {u₁ u₂ : ↥L}
    (h : centralizer ({u₁} : Set ↥L) ⊔ centralizer ({u₂} : Set ↥L) ⊔ centralizer ({u₁ * u₂} : Set ↥L) = ⊤) :
    L ≤ (L ⊓ centralizer ({(u₁ : X)} : Set X)) ⊔ (L ⊓ centralizer ({(u₂ : X)} : Set X)) ⊔
      (L ⊓ centralizer ({(u₁ : X) * u₂} : Set X)) := by
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥L) ∈ (⊤ : Subgroup ↥L) := Subgroup.mem_top _
  rw [← h] at hx'
  have h1 := Subgroup.mem_map_of_mem L.subtype hx'
  rw [Subgroup.map_sup, Subgroup.map_sup, B3aG.map_subtype_centralizer, B3aG.map_subtype_centralizer,
    B3aG.map_subtype_centralizer] at h1
  exact h1

theorem odd_card_center_of_noInvol {J : Subgroup X}
    (hJZ : ∀ z ∈ J, (∀ l ∈ J, z * l = l * z) → z * z = 1 → z = 1) : Odd (Nat.card ↥(center ↥J)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hev)
  have hzz : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hzc : ∀ l ∈ J, ((z : ↥J) : X) * l = l * z := by
    intro l hl
    have := Subgroup.mem_center_iff.1 z.2 ⟨l, hl⟩
    exact (congrArg Subtype.val this).symm
  have h1 := hJZ ((z : ↥J) : X) (z : ↥J).2 hzc (congrArg (fun w : ↥(center ↥J) => ((w : ↥J) : X)) hzz)
  have hz1 : z = 1 := Subtype.ext (Subtype.ext h1)
  rw [hz1, orderOf_one] at hz
  omega

theorem eq_of_centralizes {σ : X} {L J : Subgroup X} (hL : IsComponent L) (hc : ∀ l ∈ L, l * σ = σ * l)
    (hJ : IsCompIn (centralizer ({σ} : Set X)) J) (hJL : J ≤ L) : J = L := by
  set C := centralizer ({σ} : Set X) with hC
  have hLC : L ≤ C := fun l hl => Subgroup.mem_centralizer_singleton_iff.2 (hc l hl)
  have hL' : IsComponent (L.subgroupOf C) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLC).symm hL.1,
      hL.2.comap C.subtype⟩
  rcases CFSG.LocalCores.distinct_components_commute hJ.2 hL' with h | h
  · have h2 := (Subgroup.subgroupOf_inj).1 h
    rwa [inf_of_le_left hJ.1, inf_of_le_left hLC] at h2
  · exfalso
    have hle : J.subgroupOf C ≤ L.subgroupOf C := Subgroup.subgroupOf_mono _ hJL
    have hJq := hJ.2.1
    have hperf : ⁅J.subgroupOf C, J.subgroupOf C⁆ = J.subgroupOf C := Subgroup.isPerfect_iff.mp hJq.1
    have hbot : J.subgroupOf C = ⊥ := by
      rw [← hperf, eq_bot_iff]
      exact (Subgroup.commutator_mono le_rfl hle).trans h.le
    have := CFSG.LocalCores.isQuasisimple_nontrivial hJq
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this hbot

omit [Finite X] in
theorem exists_mul_of_mem_sup' {H K : Subgroup X} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {g : X}
    (hg : g ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, g = h * k := by
  let S : Subgroup X :=
    { carrier := {g | ∃ h ∈ H, ∃ k ∈ K, g = h * k}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
        refine ⟨h₁ * h₂, mul_mem hh₁ hh₂, k₁ * k₂, mul_mem hk₁ hk₂, ?_⟩
        calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
          _ = h₁ * (h₂ * k₁) * k₂ := by rw [← hc h₂ hh₂ k₁ hk₁]
          _ = h₁ * h₂ * (k₁ * k₂) := by group
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, inv_mem hh, k⁻¹, inv_mem hk, ?_⟩
        calc (h * k)⁻¹ = (k * h)⁻¹ := by rw [hc h hh k hk]
          _ = h⁻¹ * k⁻¹ := by group }
  have hle : H ⊔ K ≤ S := sup_le (fun h hh => ⟨h, hh, 1, one_mem _, by simp⟩)
    (fun k hk => ⟨1, one_mem _, k, hk, by simp⟩)
  exact hle hg

theorem le_sup_of_diag (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {σ : X}
    (hσ : orderOf σ = 2) {L J : Subgroup X} (hL : IsComponent L) (hne : L.map (MulAut.conj σ).toMonoidHom ≠ L)
    (hJ : IsCompIn (centralizer ({σ} : Set X)) J) (hJT : IsL3Odd (↥J ⧸ center ↥J))
    (hJL : J ≤ L ⊔ L.map (MulAut.conj σ).toMonoidHom) {e₁ e₂ : X} (he₁ : e₁ ∈ J) (he₂ : e₂ ∈ J)
    (h₁ : e₁ * e₁ = 1) (h₂ : e₂ * e₂ = 1) (h₁₂ : e₁ * e₂ = e₂ * e₁) (h₁1 : e₁ ≠ 1) (h₂1 : e₂ ≠ 1)
    (hne₁₂ : e₁ ≠ e₂) :
    L ≤ (L ⊓ centralizer ({e₁} : Set X)) ⊔ (L ⊓ centralizer ({e₂} : Set X)) ⊔
      (L ⊓ centralizer ({e₁ * e₂} : Set X)) := by
  classical
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσσ
  set L' := CFSG.LocalAnalysis.ComponentInitial.conjSub σ⁻¹ L with hL'
  have hL'eq : L' = L.map (MulAut.conj σ).toMonoidHom := by rw [hL', hσi]
  have hL'c : IsComponent L' := CFSG.LocalAnalysis.ComponentInitial.isComponent_conjSub hL σ⁻¹
  have hAB : ⁅L, L'⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hL hL'c).resolve_left
    fun h => hne (by rw [← hL'eq, ← h])
  have hcomm : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a := fun a ha b hb =>
    CFSG.LocalAnalysis.ComponentInitial.commute_of_commutator_conj_eq_bot hAB ha hb
  set δ : ↥L →* X := CFSG.LocalAnalysis.ComponentInitial.swapDiag hAB with hδ
  have hδa : ∀ l : ↥L, δ l = (l : X) * (σ⁻¹ * (l : X) * σ) := fun l => rfl
  have hconjL' : ∀ l ∈ L, σ⁻¹ * l * σ ∈ L' := fun l hl =>
    CFSG.LocalAnalysis.ComponentInitial.conj_mem_conjSub hl
  have hconjL : ∀ m ∈ L', σ⁻¹ * m * σ ∈ L := by
    rintro _ ⟨l, hl, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have e : σ⁻¹ * (σ⁻¹ * l * σ) * σ = l := by
      calc σ⁻¹ * (σ⁻¹ * l * σ) * σ = (σ * σ)⁻¹ * l * (σ * σ) := by group
        _ = l := by rw [hσσ]; group
    rw [e]
    exact hl
  have hJdec : ∀ j ∈ J, ∃ l : ↥L, ∃ z ∈ L ⊓ L', j = δ l * z := by
    intro j hj
    have hjsup : j ∈ L ⊔ L' := by rw [hL'eq]; exact hJL hj
    obtain ⟨l, hl, m, hm, rfl⟩ := exists_mul_of_mem_sup' hcomm hjsup
    have hjσ : l * m * σ = σ * (l * m) := Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hj)
    have hl₀L : σ⁻¹ * m * σ ∈ L := hconjL m hm
    have hm' : m = σ⁻¹ * (σ⁻¹ * m * σ) * σ := by
      calc m = (σ * σ)⁻¹ * m * (σ * σ) := by rw [hσσ]; group
        _ = σ⁻¹ * (σ⁻¹ * m * σ) * σ := by group
    have h1 : (σ⁻¹ * l * σ) * (σ⁻¹ * m * σ) = l * m := by
      calc (σ⁻¹ * l * σ) * (σ⁻¹ * m * σ) = σ⁻¹ * (l * m * σ) := by group
        _ = σ⁻¹ * (σ * (l * m)) := by rw [hjσ]
        _ = l * m := by group
    have h2 : (σ⁻¹ * m * σ) * (σ⁻¹ * l * σ) = l * m := by
      rw [hcomm _ hl₀L _ (hconjL' l hl)]
      exact h1
    have hzL : l⁻¹ * (σ⁻¹ * m * σ) ∈ L := L.mul_mem (L.inv_mem hl) hl₀L
    have h3 : l⁻¹ * (σ⁻¹ * m * σ) = σ⁻¹ * ((σ⁻¹ * m * σ) * l⁻¹) * σ := by
      calc l⁻¹ * (σ⁻¹ * m * σ)
          = l⁻¹ * ((σ⁻¹ * m * σ) * (σ⁻¹ * l * σ)) * (σ⁻¹ * l * σ)⁻¹ := by group
        _ = l⁻¹ * (l * m) * (σ⁻¹ * l * σ)⁻¹ := by rw [h2]
        _ = σ⁻¹ * ((σ⁻¹ * m * σ) * l⁻¹) * σ := by
          conv_lhs => rw [hm']
          group
    have hzL' : l⁻¹ * (σ⁻¹ * m * σ) ∈ L' := by
      rw [h3]
      exact hconjL' _ (L.mul_mem hl₀L (L.inv_mem hl))
    refine ⟨⟨l, hl⟩, σ⁻¹ * (l⁻¹ * (σ⁻¹ * m * σ)) * σ,
      Subgroup.mem_inf.2 ⟨hconjL _ hzL', hconjL' _ hzL⟩, ?_⟩
    rw [hδa]
    show l * m = l * (σ⁻¹ * l * σ) * (σ⁻¹ * (l⁻¹ * (σ⁻¹ * m * σ)) * σ)
    conv_lhs => rw [hm']
    group
  have hzc : ∀ z ∈ L ⊓ L', ∀ l : ↥L, z * δ l = δ l * z := by
    intro z hz l
    obtain ⟨hzL, hzL'⟩ := Subgroup.mem_inf.1 hz
    rw [hδa]
    have e1 : z * (l : X) = l * z := (hcomm l l.2 z hzL').symm
    have e2 : z * (σ⁻¹ * (l : X) * σ) = (σ⁻¹ * l * σ) * z := hcomm z hzL _ (hconjL' l l.2)
    calc z * ((l : X) * (σ⁻¹ * l * σ)) = (z * l) * (σ⁻¹ * l * σ) := by group
      _ = l * (z * (σ⁻¹ * l * σ)) := by rw [e1]; group
      _ = l * ((σ⁻¹ * l * σ) * z) := by rw [e2]
      _ = l * (σ⁻¹ * l * σ) * z := by group
  have hJq : IsQuasisimple ↥J := Prop31.isQuasisimple_of_isCompIn hJ
  have hJperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJq.1
  have hJR : J ≤ δ.range := by
    rw [← hJperf]
    refine Subgroup.commutator_le.2 fun j₁ hj₁ j₂ hj₂ => ?_
    obtain ⟨l₁, z₁, hz₁, rfl⟩ := hJdec j₁ hj₁
    obtain ⟨l₂, z₂, hz₂, rfl⟩ := hJdec j₂ hj₂
    have hzz : z₁ * z₂ = z₂ * z₁ := hcomm z₁ (Subgroup.mem_inf.1 hz₁).1 z₂ (Subgroup.mem_inf.1 hz₂).2
    rw [CFSG.LocalAnalysis.ComponentInitial.commutatorElement_mul_mul_of_commute (hzc z₁ hz₁ l₂) hzz
      (hzc z₂ hz₂ l₁)]
    exact ⟨⁅l₁, l₂⁆, map_commutatorElement δ l₁ l₂⟩
  have hRC : δ.range ≤ centralizer ({σ} : Set X) := by
    rintro _ ⟨l, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hδa]
    have e : (σ⁻¹ * (l : X) * σ) * l = l * (σ⁻¹ * l * σ) := (hcomm l l.2 _ (hconjL' l l.2)).symm
    calc (l : X) * (σ⁻¹ * l * σ) * σ = σ * ((σ⁻¹ * l * σ) * ((σ * σ)⁻¹ * l * (σ * σ))) := by group
      _ = σ * ((σ⁻¹ * l * σ) * l) := by rw [hσσ]; group
      _ = σ * (l * (σ⁻¹ * l * σ)) := by rw [e]
  have hδker : δ.ker ≤ center ↥L := by
    intro l hl
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : (l : X) * (σ⁻¹ * l * σ) = 1 := hl
    have hlL' : (l : X) ∈ L' := by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact L'.inv_mem (hconjL' l l.2)
    exact Subtype.ext (hcomm g g.2 l hlL')
  have hδker' : δ.rangeRestrict.ker ≤ center ↥L := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hδker
  have hRq : IsQuasisimple ↥δ.range :=
    CFSG.LocalCores.isQuasisimple_of_surjective hL.1 δ.rangeRestrict δ.rangeRestrict_surjective hδker'
  have hJeq : J = δ.range := by
    have hJsub : (J.subgroupOf δ.range).IsSubnormal := TwoThin.isSubnormal_inf_subgroupOf hJ.2.2 hRC
    have hJc : IsComponent (J.subgroupOf δ.range) :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJR).symm hJq, hJsub⟩
    have htop : IsComponent (⊤ : Subgroup ↥δ.range) :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hRq, Subgroup.IsSubnormal.top⟩
    rcases CFSG.LocalCores.distinct_components_commute hJc htop with h | h
    · refine le_antisymm hJR fun r hr => ?_
      have : (⟨r, hr⟩ : ↥δ.range) ∈ J.subgroupOf δ.range := h ▸ Subgroup.mem_top _
      exact this
    · exfalso
      have hperf : ⁅J.subgroupOf δ.range, J.subgroupOf δ.range⁆ = J.subgroupOf δ.range :=
        Subgroup.isPerfect_iff.mp hJc.1.1
      have hbot : J.subgroupOf δ.range = ⊥ := by
        rw [← hperf, eq_bot_iff]
        exact (Subgroup.commutator_mono le_rfl le_top).trans h.le
      exact (Subgroup.nontrivial_iff_ne_bot _).mp (CFSG.LocalCores.isQuasisimple_nontrivial hJc.1) hbot
  obtain ⟨eL⟩ := CFSG.LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hL.1 δ.rangeRestrict
    δ.rangeRestrict_surjective hδker'
  have hLT : IsL3Odd (↥L ⧸ center ↥L) :=
    P151Model.isL3Odd_equiv ((CFSG.ComponentClassification.UnbalancingLocal.centerQuotientCongr
      (MulEquiv.subgroupCongr hJeq)).trans eL.symm) hJT
  have hZodd : Odd (Nat.card ↥(center ↥L)) := odd_card_center_of_isL3Odd hGA hL.1 hLT
  have hlift : ∀ e ∈ J, e * e = 1 → ∃ u : ↥L, u * u = 1 ∧ δ u = e := by
    intro e he hee
    obtain ⟨v, hv⟩ := hJR he
    refine ⟨v ^ Nat.card ↥(center ↥L), ?_, ?_⟩
    · have hvv : v * v ∈ center ↥L := hδker (show δ (v * v) = 1 by rw [map_mul, hv, hee])
      have h1 : (⟨v * v, hvv⟩ : ↥(center ↥L)) ^ Nat.card ↥(center ↥L) = 1 := pow_card_eq_one'
      have h2 : (v * v) ^ Nat.card ↥(center ↥L) = 1 := congrArg Subtype.val h1
      rw [← (Commute.refl v).mul_pow, h2]
    · obtain ⟨k, hk⟩ := hZodd
      rw [map_pow, hv, hk, pow_succ, pow_mul, sq, hee, one_pow, one_mul]
  obtain ⟨u₁, hu₁, hδu₁⟩ := hlift e₁ he₁ h₁
  obtain ⟨u₂, hu₂, hδu₂⟩ := hlift e₂ he₂ h₂
  have hu₁1 : u₁ ≠ 1 := fun h => h₁1 (by rw [← hδu₁, h, map_one])
  have hu₂1 : u₂ ≠ 1 := fun h => h₂1 (by rw [← hδu₂, h, map_one])
  have hune : u₁ ≠ u₂ := fun h => hne₁₂ (by rw [← hδu₁, ← hδu₂, h])
  have hu₁₂ : u₁ * u₂ = u₂ * u₁ := by
    set c := u₁ * u₂ * u₁⁻¹ * u₂⁻¹ with hc
    have hcZ : c ∈ center ↥L := hδker (show δ c = 1 by
      rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv, hδu₁, hδu₂, h₁₂]; group)
    have hi₁ : u₁⁻¹ = u₁ := inv_eq_of_mul_eq_one_right hu₁
    have hi₂ : u₂⁻¹ = u₂ := inv_eq_of_mul_eq_one_right hu₂
    have hcc : c * c = 1 := by
      have h1 : u₂ * c * u₂⁻¹ = c := by
        have := Subgroup.mem_center_iff.1 hcZ u₂
        rw [this]; group
      have h2 : u₂ * c * u₂⁻¹ = c⁻¹ := by
        rw [hc, hi₁, hi₂]
        calc u₂ * (u₁ * u₂ * u₁ * u₂) * u₂ = u₂ * u₁ * u₂ * u₁ * (u₂ * u₂) := by group
          _ = (u₁ * u₂ * u₁ * u₂)⁻¹ := by rw [hu₂, mul_one]; simp [mul_assoc, hi₁, hi₂]
      have h3 : c = c⁻¹ := h1.symm.trans h2
      calc c * c = c * c⁻¹ := by rw [← h3]
        _ = 1 := mul_inv_cancel c
    have hc1 : c = 1 := by
      by_contra hne'
      exact not_mem_center_of_invol hZodd hcc hne' hcZ
    calc u₁ * u₂ = c * (u₂ * u₁) := by rw [hc]; group
      _ = u₂ * u₁ := by rw [hc1, one_mul]
  have htop := sup_centralizer_eq_top_of_L3 hL.1 hLT hZodd hu₁ hu₂ hu₁₂ hu₁1 hu₂1 hune
  have hLC : ∀ u : ↥L, L ⊓ centralizer ({(u : X)} : Set X) ≤ L ⊓ centralizer ({δ u} : Set X) := by
    intro u l hl
    obtain ⟨hlL, hlc⟩ := Subgroup.mem_inf.1 hl
    refine Subgroup.mem_inf.2 ⟨hlL, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hlc ⊢
    rw [hδa]
    have e : l * (σ⁻¹ * (u : X) * σ) = (σ⁻¹ * u * σ) * l := hcomm l hlL _ (hconjL' u u.2)
    calc l * ((u : X) * (σ⁻¹ * u * σ)) = (l * u) * (σ⁻¹ * u * σ) := by group
      _ = u * (l * (σ⁻¹ * u * σ)) := by rw [hlc]; group
      _ = u * ((σ⁻¹ * u * σ) * l) := by rw [e]
      _ = u * (σ⁻¹ * u * σ) * l := by group
  have hδu₁₂ : δ (u₁ * u₂) = e₁ * e₂ := by rw [map_mul, hδu₁, hδu₂]
  refine (le_sup_of_top htop).trans (sup_le (sup_le ?_ ?_) ?_)
  · exact ((hLC u₁).trans (by rw [hδu₁])).trans (le_sup_left.trans le_sup_left)
  · exact ((hLC u₂).trans (by rw [hδu₂])).trans (le_sup_right.trans le_sup_left)
  · exact ((hLC (u₁ * u₂)).trans (by rw [hδu₁₂])).trans le_sup_right

end Cases

@[expose] def PumpGenVert3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Gen4 X → pPrimeCore 2 X = ⊥ →
    ∀ σ : X, orderOf σ = 2 → ∀ L : Subgroup X, IsComponent L → GHList (↥L ⧸ center ↥L) →
      L.map (MulAut.conj σ).toMonoidHom = L → (∃ l ∈ L, l * σ ≠ σ * l) →
    ∀ J : Subgroup X, IsCompIn (centralizer ({σ} : Set X)) J → J ≤ L →
      P151Model.IsL3OddSD (↥J ⧸ center ↥J) → (∀ z ∈ J, (∀ l ∈ J, z * l = l * z) → z * z = 1 → z = 1) →
    ∀ e₁ e₂ : X, e₁ ∈ J → e₂ ∈ J → e₁ * e₁ = 1 → e₂ * e₂ = 1 → e₁ * e₂ = e₂ * e₁ →
      e₁ ≠ 1 → e₂ ≠ 1 → e₁ ≠ e₂ →
      L ≤ (L ⊓ centralizer ({e₁} : Set X)) ⊔ (L ⊓ centralizer ({e₂} : Set X)) ⊔
        (L ⊓ centralizer ({e₁ * e₂} : Set X))

theorem pumpGen3_of_vert (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hV : PumpGenVert3) : PumpGen3 := by
  intro X _ _ hG4 hO σ hσ J hJ hJT hJZ L hL hGH hJL e₁ e₂ he₁ he₂ h₁ h₂ h₁₂ h₁1 h₂1 hne
  by_cases hLσ : L.map (MulAut.conj σ).toMonoidHom = L
  · have hJL' : J ≤ L := by rw [hLσ, sup_idem] at hJL; exact hJL
    by_cases hc : ∃ l ∈ L, l * σ ≠ σ * l
    · exact hV X hG4 hO σ hσ L hL hGH hLσ hc J hJ hJL' hJT hJZ e₁ e₂ he₁ he₂ h₁ h₂ h₁₂ h₁1 h₂1 hne
    · push Not at hc
      have hJeq : J = L := eq_of_centralizes hL hc hJ hJL'
      have hJq : IsQuasisimple ↥J := Prop31.isQuasisimple_of_isCompIn hJ
      have htop : centralizer ({(⟨e₁, he₁⟩ : ↥J)} : Set ↥J) ⊔ centralizer ({(⟨e₂, he₂⟩ : ↥J)} : Set ↥J) ⊔
          centralizer ({(⟨e₁, he₁⟩ : ↥J) * ⟨e₂, he₂⟩} : Set ↥J) = ⊤ :=
        sup_centralizer_eq_top_of_L3 hJq hJT.isL3Odd (odd_card_center_of_noInvol hJZ) (Subtype.ext h₁)
          (Subtype.ext h₂) (Subtype.ext h₁₂) (fun h => h₁1 (congrArg Subtype.val h))
          (fun h => h₂1 (congrArg Subtype.val h)) (fun h => hne (congrArg Subtype.val h))
      have h3 := le_sup_of_top htop
      rw [← hJeq]
      exact h3
  · exact le_sup_of_diag hGA hσ hL hLσ hJ hJT.isL3Odd hJL he₁ he₂ h₁ h₂ h₁₂ h₁1 h₂1 hne

end CFSG.GH74.Generic.BProg.B2.T4.P151P
