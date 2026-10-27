module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptIsolated
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptOrth
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptOrder
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptSign
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptSkew

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.G2D4
  CFSG.Assembly.LowTwoRank Module
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open scoped MatrixGroups

section Involutions

variable {Y : Type} [Group Y] [Finite Y]

theorem commute_of_involution_of_mk (hO : classicalInvolutionOddCore Y ≤ Subgroup.center Y)
    {a b : Y} (ha : a * a = 1)
    (h : Commute (QuotientGroup.mk' (classicalInvolutionOddCore Y) a)
      (QuotientGroup.mk' (classicalInvolutionOddCore Y) b)) : Commute a b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  set c : Y := a * b * a⁻¹ * b⁻¹ with hc
  have hcO : c ∈ classicalInvolutionOddCore Y := by
    rw [← QuotientGroup.eq_one_iff (N := classicalInvolutionOddCore Y)]
    change QuotientGroup.mk' (classicalInvolutionOddCore Y) c = 1
    simp only [hc, map_mul, map_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact h.eq
  have hcen : a * c = c * a := Subgroup.mem_center_iff.mp (hO hcO) a
  have h1 : a * c * a⁻¹ = c⁻¹ := by
    calc a * c * a⁻¹ = a * a * b * a⁻¹ * b⁻¹ * a⁻¹ := by rw [hc]; group
      _ = (a * a) * b * a * b⁻¹ * a := by rw [ha']
      _ = b * a * b⁻¹ * a := by rw [ha, one_mul]
      _ = b * a * b⁻¹ * a⁻¹ := by rw [ha']
      _ = c⁻¹ := by rw [hc]; group
  have h2 : a * c * a⁻¹ = c := by rw [hcen, mul_inv_cancel_right]
  have hcc : c * c = 1 := by
    have : c = c⁻¹ := h2.symm.trans h1
    calc c * c = c * c⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel c
  have hord2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hcc)
  have hodd := CFSG.ComponentClassification.OddCore.odd_card Y
  have hdvd : orderOf (⟨c, hcO⟩ : classicalInvolutionOddCore Y) ∣
      Nat.card (classicalInvolutionOddCore Y) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hdvd
  have hc1 : c = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      rw [h] at hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  exact (commutatorElement_eq_one_iff_mul_comm (g₁ := a) (g₂ := b)).mp hc1

end Involutions

section Units

theorem exists_unit_orderOf_card_sub_one {F : Type*} [Field F] [Finite F] :
    ∃ ρ : Fˣ, orderOf ρ = Nat.card F - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  exact ⟨g, by rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]⟩

end Units

section Center

variable {p f : ℕ} [Fact p.Prime]

theorem eq_one_of_central_of_mem_planeGroupU (hf : 1 ≤ f) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {P : Submodule (GaloisField p (2 * f)) (Fin 6 → GaloisField p (2 * f))}
    (hPnd : Nondeg (unitaryInvolution (GaloisField p (2 * f)) p f) P)
    (hP2 : finrank (GaloisField p (2 * f)) P = 2) {ζ : Su (GaloisField p (2 * f)) p f 6}
    (hζ : ζ ∈ Subgroup.center (Su (GaloisField p (2 * f)) p f 6))
    (hζP : ζ ∈ planeGroupU (GaloisField p (2 * f)) p f P) : ζ = 1 := by
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := card_galoisField_two_mul_eq hq
  have hσ := isUnitaryInvolution_unitaryInvolution (p := p) (f := f) hK
  obtain ⟨a, ha⟩ := eq_smul_one_of_commute (unitaryFieldData_te6 hf) hp2 (by norm_num : 3 ≤ 6)
    (suMat ζ) (by
      intro y hy
      set x : Su (GaloisField p (2 * f)) p f 6 :=
        (suEquivUnitarySU (GaloisField p (2 * f)) p f hK 6).symm ⟨y, hy⟩ with hx
      have hxy : suMat x = (y : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) := rfl
      have h2 := congrArg suMat (Subgroup.mem_center_iff.mp hζ x)
      rw [suMat_mul, suMat_mul, hxy] at h2
      exact h2.symm)
  have hdim := finrank_add_finrank_herm_perp hσ hPnd
  have hne : perp (unitaryInvolution (GaloisField p (2 * f)) p f) P ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot, hP2] at hdim
    omega
  obtain ⟨w, hwP, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hfix : suMat ζ *ᵥ w = w := by
    rw [← suMat_smul]
    exact ((mem_fixingSubgroup_iff _).mp hζP) w hwP
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw0 (funext hcon)
  have ha1 : a = 1 := by
    have := congrFun hfix i
    rw [ha] at this
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hi (by rw [this, one_mul])
  apply suMat_injective
  rw [ha, ha1, one_smul, suMat_one]

end Center

section Context

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem te6_lie_context (hMFZ : Gaps.FundNoncentral p) (hIH : LocalLieSystems p f Ω)
    (c : UCtx p f 5 Ω K z) (nd : UNodes c) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (Dz : LieSystemData p f (locQuot Ω z) (locFamily Ω z)) {β : Subgroup G}
    (hβ : IsPartnerU c nd β) (hn3 : ¬ Commutes β (nd.j 3))
    (hP1x : LocalOddCentral Ω {z * nd.w 0}) :
    ∃ (D : LieSystemData p f (locQuot Ω (z * nd.w 0)) (locFamily Ω (z * nd.w 0)))
      (i : Fin D.card),
      (∀ N ∈ centralizingMembers Ω {z * nd.w 0}, N ∈ compMembers Ω (z * nd.w 0) D i) ∧
      FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D ∧
      NoCommonCommutant p f (D.tag i) (D.rank i) (D.exp i) ∧
      SignLinear p f (D.tag i) (D.rank i) (D.exp i) := by
  classical
  obtain ⟨D⟩ := exists_lieSystemData hIH (not_subset_center_mul hMFZ c nd hsingle Dz)
  have hβx : β ∈ centralizingMembers Ω {z * nd.w 0} :=
    ⟨hβ.mem, UCtx.partner_le_centralizer_mul c nd (by norm_num : 0 < 5) hβ.mem hβ.pK hβ.p0⟩
  have hlink := linked_of_visible c nd hβx hβ.nK hβ.n0 hn3
  obtain ⟨φ, hφ, hφK⟩ := exists_visible_equiv' c nd
  have hKx := UNodes.K_mem_centralizingMembers_mul c nd (by norm_num : 0 < 5)
  have hcard₀ : D.card = 1 := card_eq_one_of_linked c.hΩ c.hex hP1x D hKx c.hz.mem hlink
  have hsub : Subsingleton (Fin D.card) := Fin.subsingleton_iff_le_one.mpr hcard₀.le
  have hM0' := UNodes.mem_centralizingMembers_mul c nd (by norm_num : 0 < 5) (Or.inl rfl)
  have hM2' := UNodes.mem_centralizingMembers_mul c nd (by norm_num : 2 < 5)
    (Or.inr (by norm_num))
  obtain ⟨i₀, hi₀⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨K, hKx, rfl⟩)
  have hall : ∀ N ∈ centralizingMembers Ω {z * nd.w 0},
      N ∈ compMembers Ω (z * nd.w 0) D i₀ := by
    intro N hN
    obtain ⟨j, hj⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
    exact ⟨hN, hsub.elim j i₀ ▸ hj⟩
  have hexc : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
    intro i
    have hi : i = i₀ := hsub.elim i i₀
    subst hi
    exact tag_ne_of_commuting_triple c.hp2 c.hΩ c.hex D (hall K hKx) (hall _ hM0') (hall _ hM2')
      (nd.commK 0 (by norm_num)) (nd.commK 2 (by norm_num))
      (nd.far 0 (by norm_num) 2 (by norm_num) (by norm_num))
  obtain ⟨hsc, hperf⟩ := componentFacts_of_no_exotic D c.hp2 (by have := c.hq; omega) hexc
  obtain ⟨hcard, i₁, ht, hn, R₀, hR₀⟩ := shape_of_perpTableR c.hp2 c.hq c.hΩ c.hex hP1x D hexc
    hKx c.hz hlink TE6Layer.rel φ hφ hφK (te6PerpTableR p f)
  have hexp : D.exp i₁ = f := by
    rcases D.exp_eq i₁ with h | ⟨h, -⟩
    · exact h
    · exact absurd (ht.symm.trans h) (by decide)
  refine ⟨D, i₁, fun N hN => ?_, hperf i₁, ?_, ?_⟩
  · have := hsub.elim i₀ i₁
    subst this
    exact hall N hN
  · rw [ht, hn, hexp]
    exact noCommonCommutant_pOmegaMinus_five c.hp2 c.hq
  · rw [ht, hn, hexp]
    exact signLinear_pOmegaMinus_five c.hp2 c.hq

end Context

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

@[expose] def TE6NotGraphField' (c : UCtx p f 5 Ω K z) (nd : UNodes c) : Prop :=
  ∀ N ∈ centralizingMembers Ω {z * nd.w 0},
    (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K N) →
    (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W N (nd.j 0)) →
    ∀ Θ : Su (GaloisField p (2 * f)) p f 6 →* G, TE6Chart c nd Θ →
    ∀ v : G, IsClassicalMember p f N v →
    ∀ (α : Su (GaloisField p (2 * f)) p f 6 →* Su (GaloisField p (2 * f)) p f 6)
      (g : GL (Fin 6) (GaloisField p (2 * f)))
      (φ : GaloisField p (2 * f) ≃+* GaloisField p (2 * f)),
      (∀ x, Θ (α x) = v * Θ x * v⁻¹) →
      (∀ x, ((α x : GL (Fin 6) (GaloisField p (2 * f))) :
        Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) =
        (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          φ.mapMatrix ((x : GL (Fin 6) (GaloisField p (2 * f))) :
            Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          ((g⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) :
            Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))) →
      conjTr (unitaryInvolution (GaloisField p (2 * f)) p f)
        (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) = 1 →
      (φ = RingEquiv.refl (GaloisField p (2 * f)) ∨
        φ = unitaryInvolution (GaloisField p (2 * f)) p f) →
      α.comp α = MonoidHom.id _ → φ = RingEquiv.refl (GaloisField p (2 * f))

theorem te6NotGraphField_of_partner (hMFZ : Gaps.FundNoncentral p) (hIH : LocalLieSystems p f Ω)
    (c : UCtx p f 5 Ω K z) (nd : UNodes c) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeU p f 5 Ω z) {β : Subgroup G} (hβ : IsPartnerU c nd β)
    (hn3 : ¬ Commutes β (nd.j 3)) (hP1x : LocalOddCentral Ω {z * nd.w 0}) :
    TE6NotGraphField' c nd := by
  classical
  obtain ⟨Dz, -⟩ := id hshape
  have hF1 := te6PartnerIsolated_of_partner hMFZ hIH c nd hsingle Dz hβ hn3 hP1x
  obtain ⟨D, i, hall, hperf, -, hSign⟩ := te6_lie_context hMFZ hIH c nd hsingle Dz hβ hn3 hP1x
  have hp2 := c.hp2
  have hq := c.hq
  have hK := c.card_eq
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  intro N hN pKN pNJ Θ hΘ v hv α g φ hα hmat hiso hφ hα2
  rcases hφ with rfl | rfl
  · rfl
  exfalso
  obtain ⟨a, ha⟩ := sq_scalar_bar hf hp2 hq hmat hα2
  have hW := g_commutes_te6Inv c nd hΘ hN hv pKN _ hα hmat
  rcases mu_eq_one_or_neg_one _ hiso ha with h1 | h1
  · rw [h1, one_smul] at ha
    obtain ⟨P, hPnd, hP2, hPle, hPstab, hPfix⟩ := exists_stable_aniso_plane hf hp2 hmat hiso ha hW
    have hR := planeGroupU_mem hK hp2 (by norm_num : 2 ≤ 5 + 1) hPnd hP2
    obtain ⟨hLmem, hLK⟩ := hΘ.member _ hR
    set S := planeGroupU (GaloisField p (2 * f)) p f P with hS
    have hw0 : Θ (te6Inv p f) = nd.w 0 := map_te6Inv_eq hΘ
    have hLvis : S.map Θ ∈ centralizingMembers Ω {z * nd.w 0, z} := by
      rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair]
      refine ⟨hLmem, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hw0, ← map_mul, ← map_mul]
      have := planeGroupU_le_centralizer hp2 hf hPnd hP2 hPle hx
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      rw [this]
    have hnc : ¬ Commutes N (S.map Θ) := hF1 N hN pKN pNJ _ hLvis hLK
    have hLx : S.map Θ ∈ centralizingMembers Ω {z * nd.w 0} :=
      (mem_centralizingMembers_pair.mp hLvis).1
    have hKx := UNodes.K_mem_centralizingMembers_mul c nd (by norm_num : 0 < 5)
    have hKL : Commutes K (S.map Θ) := fun k hk y hy =>
      hΘ.commutes_K_range k hk y (Subgroup.map_le_range Θ S hy)
    obtain ⟨R_K, hRK⟩ := exists_corr_left c.hΩ c.hex D (hall K hKx)
    obtain ⟨R_N, hRN⟩ := exists_corr_left c.hΩ c.hex D (hall N hN)
    obtain ⟨R_L, hRL⟩ := exists_corr_left c.hΩ c.hex D (hall _ hLx)
    have hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W (R_K.map (D.hom i))
        (R_N.map (D.hom i)) := by
      obtain ⟨W₀, hW₀⟩ := pKN
      obtain ⟨W, hW⟩ := RouteD.linearBlockStandardPair_locImg hP1x (le_centralizingLayer hKx)
        (le_centralizingLayer hN) ⟨W₀, hW₀⟩
      rw [hRK.2.2, hRN.2.2] at hW
      exact ⟨W, hW⟩
    have hcKL : Commutes R_K R_L := (corr_commutes c.hΩ hP1x hperf hRK hRL).mp hKL
    have hcLN : ¬ Commutes R_L R_N := fun h =>
      hnc ((corr_commutes c.hΩ hP1x hperf hRN hRL).mpr h.symm)
    have hneLN : R_L ≠ R_N := by
      intro h
      obtain ⟨W, hW⟩ := hlin
      exact not_commutes_of_linearBlockStandardPair hW
        (commutes_map_of_commutes (D.hom i) (h ▸ hcKL))
    have hv2 : orderOf v = 2 := hv.orderOf_eq_two
    have hvv : v * v = 1 := by
      have := pow_orderOf_eq_one v
      rwa [hv2, pow_two] at this
    have hvY : v ∈ locLayer Ω (z * nd.w 0) := le_centralizingLayer hN hv.mem
    have hybN : locElt Ω (z * nd.w 0) v hvY ∈ R_N.map (D.hom i) :=
      hRN.2.2 ▸ locElt_mem_locImg (le_centralizingLayer hN) hv.mem
    have hyb2 : orderOf (locElt Ω (z * nd.w 0) v hvY) = 2 := orderOf_locElt hvY hv2
    have hLnorm : ∀ y ∈ S.map Θ, v * y * v⁻¹ ∈ S.map Θ := by
      rintro _ ⟨y₁, hy₁, rfl⟩
      exact ⟨α y₁, hPstab y₁ hy₁, hα y₁⟩
    have hnorm : ∀ w ∈ R_L.map (D.hom i),
        locElt Ω (z * nd.w 0) v hvY * w * (locElt Ω (z * nd.w 0) v hvY)⁻¹ ∈
          R_L.map (D.hom i) := by
      rw [← hRL.2.2]
      rintro _ ⟨⟨y₀, hy₀⟩, hy₀L, rfl⟩
      have hy₀L' : y₀ ∈ S.map Θ := hy₀L
      refine ⟨⟨v * y₀ * v⁻¹, (locLayer Ω (z * nd.w 0)).mul_mem
        ((locLayer Ω (z * nd.w 0)).mul_mem hvY hy₀) ((locLayer Ω (z * nd.w 0)).inv_mem hvY)⟩,
        hLnorm y₀ hy₀L', ?_⟩
      simp only [locElt, ← map_inv, ← map_mul]
      rfl
    obtain ⟨W, hW⟩ := hSign (D.hom i) (D.ker_le_center i) R_K hRK.2.1 R_N hRN.2.1 R_L hRL.2.1
      hlin hcKL hcLN hneLN _ hybN hyb2 hnorm
    obtain ⟨ρ, hρ⟩ := exists_unit_orderOf_card_sub_one (F := GaloisField p f)
    have h2F : (2 : GaloisField p f) ≠ 0 := two_ne_zero_of_charP_ne_two (K := GaloisField p f)
      (p := p) hp2
    obtain ⟨t, htL, htv, hto⟩ := exists_pair_torus_element h2F hW hybN hyb2 ρ
    rw [← hRL.2.2] at htL
    obtain ⟨⟨y₀, hy₀⟩, hy₀L, rfl⟩ := htL
    have hy₀L' : y₀ ∈ S.map Θ := hy₀L
    have hcomm : Commute (⟨v, hvY⟩ : ↥(locLayer Ω (z * nd.w 0))) ⟨y₀, hy₀⟩ :=
      commute_of_involution_of_mk hP1x (Subtype.ext hvv) htv.symm
    have hvy' : v * y₀ = y₀ * v := congrArg Subtype.val hcomm
    obtain ⟨y, hyS, hy⟩ := hy₀L'
    have hvy : v * y₀ * v⁻¹ = y₀ := by rw [mul_inv_eq_iff_eq_mul]; exact hvy'
    have hΘα : Θ (α y) = Θ y := by rw [hα y, hy, hvy]
    have hζ : α y * y⁻¹ = 1 := by
      refine eq_one_of_central_of_mem_planeGroupU hf hp2 hq hPnd hP2 ?_ ?_
      · apply hΘ.ker_le
        rw [MonoidHom.mem_ker, map_mul, map_inv, hΘα, mul_inv_cancel]
      · exact S.mul_mem (hPstab y hyS) (S.inv_mem hyS)
    have hpow : y ^ (p ^ f + 1) = 1 := hPfix y hyS (mul_inv_eq_one.mp hζ)
    have hty : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω (z * nd.w 0)))
        ⟨y₀, hy₀⟩) ^ (p ^ f + 1) = 1 := by
      rw [← map_pow]
      have : (⟨y₀, hy₀⟩ : ↥(locLayer Ω (z * nd.w 0))) ^ (p ^ f + 1) = 1 := by
        apply Subtype.ext
        show y₀ ^ (p ^ f + 1) = 1
        rw [← hy, ← map_pow, hpow, map_one]
      rw [this, map_one]
    have hdvd := orderOf_dvd_of_pow_eq_one hty
    rw [hto, hρ, GaloisField.card p f c.hf] at hdvd
    have h2 : p ^ f - 1 ∣ 2 := by
      have e : p ^ f + 1 = (p ^ f - 1) + 2 := by omega
      rw [e] at hdvd
      exact (Nat.dvd_add_right (dvd_refl _)).mp hdvd
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · rw [h1] at ha
    have hfix := alpha_fixes_te6Node_of_skew hp2 hmat hiso ha hW
    have hperf' : ⁅te6Node p f, te6Node p f⁆ = te6Node p f :=
      Subgroup.isPerfect_iff.mp (c.isPerfect_of_isLongRootSU2 (isLongRootSU2_te6Node hp2))
    have hcomm := commutes_of_alpha_fixed hMFZ hsingle hshape hΘ hN.1 hv pKN hα hperf' hfix
    have hj0 : (te6Node p f).map Θ = nd.j 0 := by
      show (LcU (GaloisField p (2 * f)) p f (nodePair 5 0 (by norm_num))).map Θ = nd.j 0
      rw [← range_blockEmb2_eq_LcU_nodePair c.h2 (by norm_num : 0 < 5)]
      exact hΘ.block ⟨0, by norm_num⟩
    rw [hj0] at hcomm
    obtain ⟨W', hW'⟩ := pNJ
    exact not_commutes_of_linearBlockStandardPair hW' hcomm

end Main

end CFSG.ClassicalInvolution.RouteD.NonClassical
