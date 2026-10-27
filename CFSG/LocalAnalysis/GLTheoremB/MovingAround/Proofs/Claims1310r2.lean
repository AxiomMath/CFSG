module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1310r
public import CFSG.LocalAnalysis.StandardType.SpTwoThreeFixedPoints
public import CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.Holds

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310r

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

set_option linter.unusedSectionVars false

section SpModule

open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical

variable {r : ℕ} {F : Type} [Field F] [Finite F]

theorem exists_plane_fix (hF : Nat.card F = 2) (hr : 1 ≤ r) {A1 : Subgroup (StatedSp r F)}
    (hcomm : ∀ x ∈ A1, ∀ y ∈ A1, x * y = y * x) (hexp : ∀ x ∈ A1, x ^ 3 = 1)
    (hcard : 27 ≤ Nat.card A1) :
    ∃ E1 : Subgroup (StatedSp r F), E1 ≤ A1 ∧ Nat.card E1 = 9 ∧ spPlaneFix E1 ≠ ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAel : IsElemAbelian 3 A1 := ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, hexp⟩
  haveI : IsElementaryAbelian 3 ↥A1 := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A1).2 hAel
  haveI : Finite ↥A1 := inferInstance
  obtain ⟨k, hk⟩ := GL83.CompFam.exists_card_eq_pow hAel
  have hk3 : 3 ≤ k := by
    by_contra hcon
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  haveI : Nontrivial ↥A1 := (Finite.one_lt_card_iff_nontrivial).1 (by omega)
  letI act : MulDistribMulAction ↥A1 (Multiplicative (Fin r ⊕ Fin r → F)) :=
    { smul := fun g x => Multiplicative.ofAdd (spRep A1 g (Multiplicative.toAdd x))
      one_smul := fun x => by
        show Multiplicative.ofAdd (spRep A1 1 (Multiplicative.toAdd x)) = x
        rw [map_one, Module.End.one_apply, ofAdd_toAdd]
      mul_smul := fun g h x => by
        show Multiplicative.ofAdd (spRep A1 (g * h) (Multiplicative.toAdd x)) =
          Multiplicative.ofAdd (spRep A1 g (Multiplicative.toAdd
            (Multiplicative.ofAdd (spRep A1 h (Multiplicative.toAdd x)))))
        rw [map_mul, Module.End.mul_apply, toAdd_ofAdd]
      smul_mul := fun g x y => by
        show Multiplicative.ofAdd (spRep A1 g (Multiplicative.toAdd (x * y))) =
          Multiplicative.ofAdd (spRep A1 g (Multiplicative.toAdd x)) *
            Multiplicative.ofAdd (spRep A1 g (Multiplicative.toAdd y))
        rw [toAdd_mul, map_add, ofAdd_add]
      smul_one := fun g => by
        show Multiplicative.ofAdd (spRep A1 g (Multiplicative.toAdd 1)) = 1
        rw [toAdd_one, map_zero, ofAdd_zero] }
  have hsmul : ∀ (g : ↥A1) (x : Multiplicative (Fin r ⊕ Fin r → F)),
      Multiplicative.toAdd (g • x) = spRep A1 g (Multiplicative.toAdd x) := fun _ _ => rfl
  have hVcard : Nat.card (Multiplicative (Fin r ⊕ Fin r → F)) = 2 ^ (2 * r) := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, hF, Nat.card_sum, Nat.card_fin, two_mul]
  have hnd : ¬ 3 ∣ Nat.card (Multiplicative (Fin r ⊕ Fin r → F)) := by
    rw [hVcard]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 3) (A := ↥A1)
    (H := Multiplicative (Fin r ⊕ Fin r → F)) hnd
  obtain ⟨B, hBidx, hBne⟩ : ∃ B : Subgroup ↥A1, B.index = 3 ∧
      CFSG.fixedPointSubgroup ↥B (Multiplicative (Fin r ⊕ Fin r → F)) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have hbot : (⨆ (B : Subgroup ↥A1) (_ : B.index = 3),
        CFSG.fixedPointSubgroup ↥B (Multiplicative (Fin r ⊕ Fin r → F))) = ⊥ :=
      iSup₂_eq_bot.2 hcon
    rw [hbot] at hgen
    haveI : Nontrivial (Multiplicative (Fin r ⊕ Fin r → F)) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hVcard]
      exact Nat.one_lt_two_pow (by omega)
    exact bot_ne_top hgen
  obtain ⟨⟨x, hxB⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hBne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hBcard : Nat.card B = 3 ^ (k - 1) := by
    have h1 := Subgroup.card_mul_index B
    rw [hBidx, Nat.card_congr (Equiv.refl ↥A1)] at h1
    have h2 : Nat.card ↥A1 = 3 ^ (k - 1) * 3 := by
      rw [hk, ← pow_succ]
      congr 1
      omega
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  obtain ⟨E', hE'⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 2)
    (show 3 ^ 2 ∣ Nat.card B by rw [hBcard]; exact Nat.pow_dvd_pow 3 (by omega))
  set E1 : Subgroup (StatedSp r F) := (E'.map B.subtype).map A1.subtype with hE1
  refine ⟨E1, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [hE1, Subgroup.card_map_of_injective A1.subtype_injective,
      Subgroup.card_map_of_injective B.subtype_injective, hE']
    norm_num
  · rw [Ne, Submodule.eq_bot_iff]
    push Not
    refine ⟨Multiplicative.toAdd x, ?_, ?_⟩
    · rw [spPlaneFix, CFSG.RankThree.Classical.mem_fixSub]
      rintro ⟨g, hg⟩ -
      obtain ⟨_, ⟨b, -, rfl⟩, rfl⟩ := hg
      have hfix := hxB b
      have h1 : Multiplicative.toAdd ((b : ↥A1) • x) = Multiplicative.toAdd x :=
        congrArg Multiplicative.toAdd hfix
      rw [hsmul, spRep_apply] at h1
      rw [spRep_apply]
      exact h1
    · intro h0
      apply hx1'
      rw [← ofAdd_toAdd x, h0, ofAdd_zero]

end SpModule

section LiftBot

open CFSG.HardMathSupport.Dickson.I271 (actPre autImage actHom mem_actPre actHom_mk
  coe_normalizerMonoidHom actPre_le_left eq_top_of_sup_center_eq_top pRank_actPre)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns (gammaPrimeIn)

variable {X : Type} [Group X] [Finite X]

theorem le_gammaPrime_of_fixed_bot {k : ℕ} {B K : Subgroup X} (hperf : commutator ↥K = ⊤)
    (hZ : Subgroup.center ↥K = ⊥) (Fam : Set (Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))))
    (hFam : ∀ P ∈ Fam, k ≤ CFSG.Open.pRank 3 (actPre B K P))
    (hgen : Subgroup.closure {s : ↥K ⧸ Subgroup.center ↥K | ∃ P ∈ Fam, ∀ e ∈ P, e s = s} = ⊤) :
    K ≤ gammaPrimeIn 3 k B K := by
  set Γ : Subgroup X := gammaPrimeIn 3 k B K with hΓ
  set Γ₀ : Subgroup ↥K := Γ.subgroupOf K with hΓ₀
  set S : Set (↥K ⧸ Subgroup.center ↥K) := {s | ∃ P ∈ Fam, ∀ e ∈ P, e s = s} with hS
  have hlift : ∀ s ∈ S, ∃ k' ∈ Γ₀, (QuotientGroup.mk k' : ↥K ⧸ Subgroup.center ↥K) = s := by
    rintro s ⟨P, hP, hs⟩
    obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective s
    refine ⟨k', ?_, rfl⟩
    show (k' : X) ∈ Γ
    have hcent : (k' : X) ∈ Subgroup.centralizer (actPre B K P : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      obtain ⟨hqN, hqB, hqP⟩ := mem_actPre.1 hq
      set k'' : ↥K := K.normalizerMonoidHom ⟨q, hqN⟩ k' with hk''
      have h1 : (QuotientGroup.mk k'' : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk k' := by
        have := hs _ hqP
        rwa [actHom_mk] at this
      have h3 : k'' = k' := by
        have h2 := QuotientGroup.eq.1 h1
        rw [hZ, Subgroup.mem_bot] at h2
        exact inv_mul_eq_one.1 h2
      have h4 : (k'' : X) = q * (k' : X) * q⁻¹ := coe_normalizerMonoidHom K ⟨q, hqN⟩ k'
      have h5 : q * (k' : X) * q⁻¹ = (k' : X) := by rw [← h4, h3]
      calc q * (k' : X) = q * (k' : X) * q⁻¹ * q := by group
        _ = (k' : X) * q := by rw [h5]
    have hle : K ⊓ Subgroup.centralizer (actPre B K P : Set X) ≤ Γ :=
      le_iSup₂_of_le (f := fun (E : Subgroup X) (_ : E ≤ B ∧ k ≤ CFSG.Open.pRank 3 E) =>
        K ⊓ Subgroup.centralizer (E : Set X)) (actPre B K P) ⟨actPre_le_left, hFam P hP⟩ le_rfl
    exact hle ⟨k'.2, hcent⟩
  have hle : Subgroup.closure S ≤ Γ₀.map (QuotientGroup.mk' (Subgroup.center ↥K)) := by
    rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨k', hk', rfl⟩ := hlift s hs
    exact ⟨k', hk', rfl⟩
  have hsup : Γ₀ ⊔ Subgroup.center ↥K = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : (QuotientGroup.mk g : ↥K ⧸ Subgroup.center ↥K) ∈ Subgroup.closure S := by
      rw [hgen]; exact Subgroup.mem_top _
    obtain ⟨γ, hγ, hγg⟩ := hle hg
    have hz : γ⁻¹ * g ∈ Subgroup.center ↥K := QuotientGroup.eq.1 hγg
    have : g = γ * (γ⁻¹ * g) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hγ hz
  have htop : Γ₀ = ⊤ := eq_top_of_sup_center_eq_top hperf hsup
  intro x hx
  have : (⟨x, hx⟩ : ↥K) ∈ Γ₀ := by rw [htop]; exact Subgroup.mem_top _
  exact this

end LiftBot

section SpCase

open CFSG.HardMathSupport.Dickson.I271 (actPre autImage actHom mem_actPre pRank_actPre)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {G : Type} [Group G] [Finite G]

theorem le_M_of_sp (hGA : GriessMultipliersAllModels) {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139b : Prop139b p M D) {U : Subgroup G}
    (hU : IsU1312 p B M D L0 d U) {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) {Kc : Subgroup G}
    (hKc : GLAPComponent 3 (Cg u) Kc) (hN : B ≤ Subgroup.normalizer (Kc : Set G))
    (hcen : CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
      Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
        Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) ≤ 1)
    (i : TauCeti.ValidLieTypeIndex)
    (e : barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc) ≃* (TauCeti.CFSGIndex.lie i).Group)
    (q : TauCeti.PrimePower) (hq2 : q.p = 2) (hq1 : q.exponent = 1) {r : ℕ} (hr : 3 ≤ r)
    (hi : i.1 = .B r q) : Kc ≤ M := by
  classical
  obtain ⟨hp3, -⟩ := h139b
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hS : GLStanding G m 3 := h.standing
  have hBel : IsElemAbelian 3 B := h.bOne.1.1
  have huB : u ∈ B := hU.1.1 hu
  have hBC : B ≤ Cg u := Prop1310a5b.le_cg_of_mem hBel huB
  have hBm : CFSG.Open.pRank 3 B = m := Claims1310.pRank_B_eq h
  have hB4 : 4 ≤ CFSG.Open.pRank 3 B := hBm ▸ hS.four_le
  have hnorm : ∀ E' : Subgroup G, E' ≤ B → 2 ≤ CFSG.Open.pRank 3 E' →
      Subgroup.normalizer (E' : Set G) ≤ M :=
    fun E' hE' hr => (normalizer_le_glbCore hE' hr).trans h.uniq.clause_d
  have hcore : GLAPPrimeCoreOf 3 (Cg u) ≤ M := le_sup_left.trans (h.uniq.clause_a u huB hu1)
  have eK : barOf 3 Kc ≃* ↥(barX 3 (Cg u) Kc) := quotEquivBarX hp hKc.1 hKc.2.1
  have hKt : IsComponentOf (barX 3 (Cg u) Kc) ⊤ :=
    Lemma1314.isComponentOf_barX_of_glaPComponent hKc
  have hBtel : IsElemAbelian 3 (barX 3 (Cg u) B) := isElemAbelian_barX hBel
  have hBtrk : CFSG.Open.pRank 3 (barX 3 (Cg u) B) = CFSG.Open.pRank 3 B :=
    rank_barX_of_isPGroup hp (CFSG.Open.IsElemAbelian.isPGroup hBel) hBC
  have hBtN : barX 3 (Cg u) B ≤
      Subgroup.normalizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
        Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :=
    barX_le_normalizer hN
  have hperf : commutator ↥(barX 3 (Cg u) Kc) = ⊤ := hKt.2.2.1
  have hc1 := InputsSeitz6.one_le_pRank_cen_bar hBel huB hu1 Kc
  have eZ : ↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc) ≃*
      (TauCeti.CFSGIndex.lie i).Group := (Lemma1315b.centerQuotEquiv eK.symm).trans e
  have hpi3 : 3 ≠ i.1.characteristic := by
    rw [hi, TauCeti.LieTypeIndex.characteristic_B, hq2]
    norm_num
  have hZ : Subgroup.center ↥(barX 3 (Cg u) Kc) = ⊥ := by
    by_contra hZ
    have hZp : IsPGroup 3 ↥(Subgroup.center ↥(barX 3 (Cg u) Kc)) :=
      Inputs245b.isPGroup_center_of_component hp (glaPPrimeCore_quotient_eq_bot hp) hKt
    have hc := CFSG.LieType.SeitzGeneration.QuasiHigh.coverIndex_of_dvd_card_center hGA hp
      (by norm_num) hKt.2.2 i eZ hpi3 (InputsSeitz6.dvd_card_of_isPGroup hZp hZ)
    rw [hi] at hc
    exact hc
  set Aim := autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) with hAim
  have hAel : IsElemAbelian 3 Aim :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.isElemAbelian_autImage hBtel
  obtain ⟨a, ha⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_pow_autOrderIn hp hBtel hBtN
  have hrk := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.pRank_eq_add_autOrderIn hp hBtel hBtN ha
  have hAcard : Nat.card Aim = 3 ^ a :=
    (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.card_autImage hperf).trans ha
  have ha3 : 3 ≤ a := by omega
  have hA27 : 27 ≤ Nat.card Aim := by
    rw [hAcard]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) ha3
  obtain ⟨-, F, _, _, hF, ⟨e'⟩⟩ :=
    (CFSG.StandardType.ggLieModel_symplectic_two i q hq2 hq1 r hr hi eZ).statedClassicalModel
      (by decide)
  have hF2 : Nat.card F = 2 := by simpa using hF
  have hinj : Function.Injective (proj r F) :=
    CFSG.RankThree.PartOne.proj_injective_sp (f := 1) (by simpa using hF) le_rfl (by omega)
  let φ : StatedSp r F ≃* (↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc)) :=
    (MulEquiv.ofBijective (proj r F) ⟨hinj, proj_surjective⟩).trans e'.symm
  have hin : ∀ α : MulAut (↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc)),
      ∃ k, α = MulAut.conj k := by
    intro α
    obtain ⟨g, hg⟩ := CFSG.StandardType.SpTwoThree.all_inner_statedProj hF2 hr (MulAut.congr e' α)
    obtain ⟨k, hk⟩ := (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr e' α).mp ⟨g, hg.symm⟩
    exact ⟨k, hk.symm⟩
  let ψ : StatedSp r F →* MulAut (↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc)) :=
    (MulAut.conj : _ →* MulAut _).comp φ.toMonoidHom
  have hψ : ∀ (g : StatedSp r F) (s), ψ g s = φ g * s * (φ g)⁻¹ := fun _ _ => rfl
  have hfix : ∀ x g : StatedSp r F, ψ x (φ g) = φ g ↔ g * x = x * g := by
    intro x g
    rw [hψ, mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul, φ.injective.eq_iff, eq_comm]
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    refine CFSG.StandardType.SpTwoThree.eq_one_of_forall_commute hF2 (by omega) g fun b => ?_
    have h1 := hfix g b
    rw [hg, MulAut.one_apply] at h1
    exact (h1.mp rfl).symm
  have hψsurj : Function.Surjective ψ := by
    intro α
    obtain ⟨k, rfl⟩ := hin α
    exact ⟨φ.symm k, by ext m; simp [ψ]⟩
  set A1 : Subgroup (StatedSp r F) := Aim.comap ψ with hA1
  have hA1card : Nat.card A1 = Nat.card Aim := by
    rw [← Subgroup.card_map_of_injective hψinj, Subgroup.map_comap_eq_self_of_surjective hψsurj]
  have hA1comm : ∀ x ∈ A1, ∀ y ∈ A1, x * y = y * x := by
    intro x hx y hy
    have h1 := congrArg Subtype.val (hAel.1.is_comm.comm (⟨ψ x, hx⟩ : Aim) ⟨ψ y, hy⟩)
    exact hψinj (by simpa using h1)
  have hA1exp : ∀ x ∈ A1, x ^ 3 = 1 := by
    intro x hx
    apply hψinj
    rw [map_pow, map_one]
    exact hAel.2 _ hx
  obtain ⟨E1, hE1A, hE1card, hE1fix⟩ := exists_plane_fix hF2 (by omega) hA1comm hA1exp
    (hA1card ▸ hA27)
  have hgen1 := CFSG.LieType.SeitzGeneration.closure_centralizers_spPlane_three_F2_of_big_or_fixed hF2
    (fun x hx y hy => hA1comm x (hE1A hx) y (hE1A hy)) (fun x hx => hA1exp x (hE1A hx)) hE1card
    (Or.inl hE1fix)
  set Fam : Set (Subgroup (MulAut (↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc)))) :=
    {P | ∃ x ∈ E1, x ≠ 1 ∧ P = Subgroup.zpowers (ψ x)} with hFam
  have hgenS : Subgroup.closure {s : ↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc) |
      ∃ P ∈ Fam, ∀ ε ∈ P, ε s = s} = ⊤ := by
    rw [eq_top_iff]
    have hmap : (Subgroup.closure {g : StatedSp r F | ∃ x ∈ E1, x ≠ 1 ∧ g * x = x * g}).map
        φ.toMonoidHom ≤ Subgroup.closure {s | ∃ P ∈ Fam, ∀ ε ∈ P, ε s = s} := by
      rw [MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨g, ⟨x, hx, hx1, hgx⟩, rfl⟩
      refine ⟨Subgroup.zpowers (ψ x), ⟨x, hx, hx1, rfl⟩, ?_⟩
      intro ε hε
      have h1 : ψ x (φ g) = φ g := (hfix x g).mpr hgx
      have hst : Subgroup.zpowers (ψ x) ≤ MulAction.stabilizer (MulAut _) (φ g) :=
        (Subgroup.zpowers_le).2 (by rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact h1)
      have h2 := hst hε
      rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h2
    rw [hgen1, Subgroup.map_top_of_surjective _ φ.surjective] at hmap
    exact hmap
  have hFamrk : ∀ P ∈ Fam, 2 ≤ CFSG.Open.pRank 3
      (actPre (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) P) := by
    rintro P ⟨x, hx, hx1, rfl⟩
    have hxA : ψ x ∈ Aim := hE1A hx
    have hψx1 : ψ x ≠ 1 := fun h1 => hx1 (hψinj (by rw [h1, map_one]))
    have hcard : Nat.card (Subgroup.zpowers (ψ x)) = 3 ^ 1 := by
      rw [Nat.card_zpowers, pow_one, orderOf_eq_prime (hAel.2 _ hxA) hψx1]
    rw [pRank_actPre hp hBtel hperf ((Subgroup.zpowers_le).2 hxA) hcard]
    omega
  have hgam := le_gammaPrime_of_fixed_bot hperf hZ Fam hFamrk hgenS
  exact Prop1310a5b.comp_le_M_of_gamma hBel huB hnorm hcore hKc
    (hgam.trans (gammaPrimeIn_le_glbCore le_rfl _ _))

end SpCase

section Unitary

open Matrix CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313UnitaryProof

section HeisC

variable {K : Type*} [Field K] {R : Type*} [Ring R] [Algebra K R]

@[expose] def heisInvC (X Xi N : R) : R := 1 + N + X * N * Xi + X * X * N * (Xi * Xi)

theorem heisC_eq_zero_of_smul {a : K} (ha : a ≠ 0) {Z : R} (hZ : a • Z = 0) : Z = 0 := by
  rw [← one_smul K Z, ← inv_mul_cancel₀ ha, mul_smul, hZ, smul_zero]

variable {X Xi Y N : R} {κ c : K}

theorem heisC_YX (hκ : κ ^ 2 + κ + 1 = 0) (hXY : X * Y = κ • (Y * X)) :
    Y * X = κ ^ 2 • (X * Y) := by
  rw [hXY, smul_smul, ← pow_succ, cube_eq_one_of_sq_add hκ, one_smul]

theorem heisC_YXX (hκ : κ ^ 2 + κ + 1 = 0) (hXY : X * Y = κ • (Y * X)) :
    Y * (X * X) = κ • (X * X * Y) := by
  have h3 := cube_eq_one_of_sq_add hκ
  have hYX := heisC_YX hκ hXY
  have e1 : κ ^ 2 * κ ^ 2 = κ := by
    calc κ ^ 2 * κ ^ 2 = κ ^ 3 * κ := by ring
      _ = κ := by rw [h3, one_mul]
  calc Y * (X * X) = (Y * X) * X := (mul_assoc _ _ _).symm
    _ = κ ^ 2 • (X * (Y * X)) := by conv_lhs => rw [hYX]
                                    rw [smul_mul_assoc, mul_assoc]
    _ = κ ^ 2 • (X * (κ ^ 2 • (X * Y))) := by rw [hYX]
    _ = (κ ^ 2 * κ ^ 2) • (X * X * Y) := by rw [mul_smul_comm, smul_smul, mul_assoc]
    _ = κ • (X * X * Y) := by rw [e1]

theorem heisC_XiY (hκ : κ ^ 2 + κ + 1 = 0) (hXY : X * Y = κ • (Y * X)) (hXXi : X * Xi = 1)
    (hXiX : Xi * X = 1) : Xi * Y = κ ^ 2 • (Y * Xi) := by
  have hYX := heisC_YX hκ hXY
  calc Xi * Y = Xi * (Y * X) * Xi := by rw [mul_assoc, mul_assoc, hXXi, mul_one]
    _ = Xi * (κ ^ 2 • (X * Y)) * Xi := by rw [hYX]
    _ = κ ^ 2 • (Xi * X * (Y * Xi)) := by
        rw [mul_smul_comm, smul_mul_assoc]
        simp only [mul_assoc]
    _ = κ ^ 2 • (Y * Xi) := by rw [hXiX, one_mul]

theorem heisC_kappa_ne (h2 : (2 : K) = 0) (hκ : κ ^ 2 + κ + 1 = 0) : κ ≠ 1 ∧ κ ^ 2 ≠ 1 := by
  constructor
  · rintro rfl
    have h3 : (3 : K) = 0 := by linear_combination hκ
    have : (1 : K) = 0 := by linear_combination h3 - h2
    exact one_ne_zero this
  · intro h1
    have hk : κ = 0 := by linear_combination hκ - h1 - h2
    rw [hk] at h1
    norm_num at h1

variable (h2 : (2 : K) = 0) (hκ : κ ^ 2 + κ + 1 = 0) (hXY : X * Y = κ • (Y * X))
  (hXXi : X * Xi = 1) (hXiX : Xi * X = 1) (hX3 : X * X * X = c • 1) (hc : c ≠ 0)
  (hYN : Y * N = N) (hNY : N * Y = N) (hNN : N * N = 0)

include h2 hκ hXY hYN hNY in
theorem heisC_NXN : N * X * N = 0 := by
  have hYX := heisC_YX hκ hXY
  have e1 : N * X * N = κ ^ 2 • (N * X * N) := by
    calc N * X * N = N * Y * X * N := by rw [hNY]
      _ = N * (Y * X) * N := by rw [mul_assoc N Y X]
      _ = N * (κ ^ 2 • (X * Y)) * N := by rw [hYX]
      _ = κ ^ 2 • (N * X * (Y * N)) := by
          rw [mul_smul_comm, smul_mul_assoc]
          simp only [mul_assoc]
      _ = κ ^ 2 • (N * X * N) := by rw [hYN]
  have hne := (heisC_kappa_ne h2 hκ).2
  have h0 : (κ ^ 2 - 1) • (N * X * N) = 0 := by rw [sub_smul, one_smul, ← e1, sub_self]
  exact heisC_eq_zero_of_smul (sub_ne_zero.2 hne) h0

include h2 hκ hXY hYN hNY in
theorem heisC_NXXN : N * (X * X) * N = 0 := by
  have hYXX := heisC_YXX hκ hXY
  have e1 : N * (X * X) * N = κ • (N * (X * X) * N) := by
    calc N * (X * X) * N = N * Y * (X * X) * N := by rw [hNY]
      _ = N * (Y * (X * X)) * N := by rw [mul_assoc N Y]
      _ = N * (κ • (X * X * Y)) * N := by rw [hYXX]
      _ = κ • (N * (X * X) * (Y * N)) := by
          rw [mul_smul_comm, smul_mul_assoc]
          simp only [mul_assoc]
      _ = κ • (N * (X * X) * N) := by rw [hYN]
  have hne := (heisC_kappa_ne h2 hκ).1
  have h0 : (κ - 1) • (N * (X * X) * N) = 0 := by rw [sub_smul, one_smul, ← e1, sub_self]
  exact heisC_eq_zero_of_smul (sub_ne_zero.2 hne) h0

include hXiX hX3 hc in
theorem heisC_Xi : Xi = c⁻¹ • (X * X) := by
  calc Xi = Xi * (c⁻¹ • (X * X * X)) := by
        rw [hX3, smul_smul, inv_mul_cancel₀ hc, one_smul, mul_one]
    _ = c⁻¹ • (X * X) := by
        rw [mul_smul_comm]
        congr 1
        simp only [← mul_assoc, hXiX, one_mul]

include hXXi hXiX hX3 hc in
theorem heisC_XiXi : Xi * Xi = c⁻¹ • X := by
  have hXi := heisC_Xi hXiX hX3 hc
  calc Xi * Xi = (c⁻¹ • (X * X)) * Xi := by nth_rewrite 1 [hXi]; rfl
    _ = c⁻¹ • X := by rw [smul_mul_assoc, mul_assoc, hXXi, mul_one]

include h2 hκ hXY hXiX hX3 hc hYN hNY in
theorem heisC_NXiN : N * Xi * N = 0 := by
  rw [heisC_Xi hXiX hX3 hc, mul_smul_comm, smul_mul_assoc, heisC_NXXN h2 hκ hXY hYN hNY, smul_zero]

include h2 hκ hXY hXXi hXiX hX3 hc hYN hNY in
theorem heisC_NXiXiN : N * (Xi * Xi) * N = 0 := by
  rw [heisC_XiXi hXXi hXiX hX3 hc, mul_smul_comm, smul_mul_assoc, heisC_NXN h2 hκ hXY hYN hNY,
    smul_zero]

include h2 hκ hXY hXXi hXiX hX3 hc hYN hNY hNN in
theorem heisC_sq_zero :
    (N + X * N * Xi + X * X * N * (Xi * Xi)) * (N + X * N * Xi + X * X * N * (Xi * Xi)) = 0 := by
  have hXiX' : ∀ Z : R, Xi * (X * Z) = Z := fun Z => by rw [← mul_assoc, hXiX, one_mul]
  have n1 := heisC_NXN h2 hκ hXY hYN hNY
  have n2 := heisC_NXXN h2 hκ hXY hYN hNY
  have n3 := heisC_NXiN h2 hκ hXY hXiX hX3 hc hYN hNY
  have n4 := heisC_NXiXiN h2 hκ hXY hXXi hXiX hX3 hc hYN hNY
  have e1 : N * (X * N * Xi) = (N * X * N) * Xi := by simp only [mul_assoc]
  have e2 : N * (X * X * N * (Xi * Xi)) = (N * (X * X) * N) * (Xi * Xi) := by simp only [mul_assoc]
  have e3 : X * N * Xi * N = X * (N * Xi * N) := by simp only [mul_assoc]
  have e4 : X * N * Xi * (X * N * Xi) = X * (N * N) * Xi := by simp only [mul_assoc, hXiX']
  have e5 : X * N * Xi * (X * X * N * (Xi * Xi)) = X * (N * X * N) * (Xi * Xi) := by
    simp only [mul_assoc, hXiX']
  have e6 : X * X * N * (Xi * Xi) * N = (X * X) * (N * (Xi * Xi) * N) := by simp only [mul_assoc]
  have e7 : X * X * N * (Xi * Xi) * (X * N * Xi) = (X * X) * (N * Xi * N) * Xi := by
    simp only [mul_assoc, hXiX']
  have e8 : X * X * N * (Xi * Xi) * (X * X * N * (Xi * Xi)) = (X * X) * (N * N) * (Xi * Xi) := by
    simp only [mul_assoc, hXiX']
  simp only [add_mul, mul_add, hNN, e1, e2, e3, e4, e5, e6, e7, e8, n1, n2, n3, n4, mul_zero,
    zero_mul, add_zero]

include h2 hκ hXY hXXi hXiX hX3 hc hYN hNY hNN in
theorem heisInvC_mul_self : heisInvC X Xi N * heisInvC X Xi N = 1 := by
  have hS := heisC_sq_zero h2 hκ hXY hXXi hXiX hX3 hc hYN hNY hNN
  set S := N + X * N * Xi + X * X * N * (Xi * Xi) with hSdef
  have hT : heisInvC X Xi N = 1 + S := by simp only [heisInvC, hSdef, add_assoc]
  have hSS : S + S = 0 := by rw [← two_smul K S, h2, zero_smul]
  calc heisInvC X Xi N * heisInvC X Xi N = (1 + S) * (1 + S) := by rw [hT]
    _ = 1 + (S + S) + S * S := by noncomm_ring
    _ = 1 := by rw [hSS, hS, add_zero, add_zero]

include hXXi hXiX hX3 hc in
theorem heisInvC_comm_X : X * heisInvC X Xi N = heisInvC X Xi N * X := by
  have hXiXi := heisC_XiXi hXXi hXiX hX3 hc
  have hXiX' : ∀ Z : R, Xi * (X * Z) = Z := fun Z => by rw [← mul_assoc, hXiX, one_mul]
  have e1 : X * (X * N * Xi) = X * X * N * (Xi * Xi) * X := by
    simp only [mul_assoc, hXiX', hXiX, mul_one]
  have e2 : X * N * Xi * X = X * N := by simp only [mul_assoc, hXiX', hXiX, mul_one]
  have e3 : X * (X * X * N * (Xi * Xi)) = N * X := by
    rw [hXiXi]
    simp only [← mul_assoc]
    rw [hX3, smul_mul_assoc, one_mul, smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hc,
      one_smul]
  simp only [heisInvC, mul_add, add_mul, mul_one, one_mul, e1, e2, e3]
  abel

include hκ hXY in
theorem heisC_YM : Y * (X * N * Xi) = κ ^ 2 • (X * Y * N * Xi) := by
  calc Y * (X * N * Xi) = (Y * X) * N * Xi := by simp only [mul_assoc]
    _ = κ ^ 2 • (X * Y * N * Xi) := by rw [heisC_YX hκ hXY, smul_mul_assoc, smul_mul_assoc]

include hκ hXY in
theorem heisC_YM' : Y * (X * X * N * (Xi * Xi)) = κ • (X * X * Y * N * (Xi * Xi)) := by
  calc Y * (X * X * N * (Xi * Xi)) = (Y * (X * X)) * N * (Xi * Xi) := by simp only [mul_assoc]
    _ = κ • (X * X * Y * N * (Xi * Xi)) := by
        rw [heisC_YXX hκ hXY, smul_mul_assoc, smul_mul_assoc]

include hκ hXY hXXi hXiX in
theorem heisC_MY : X * N * Xi * Y = κ ^ 2 • (X * N * Y * Xi) := by
  calc X * N * Xi * Y = X * N * (Xi * Y) := by simp only [mul_assoc]
    _ = κ ^ 2 • (X * N * Y * Xi) := by
        rw [heisC_XiY hκ hXY hXXi hXiX, mul_smul_comm]
        simp only [mul_assoc]

include hκ hXY hXXi hXiX in
theorem heisC_XiXiY : Xi * Xi * Y = κ • (Y * (Xi * Xi)) := by
  have h3 := cube_eq_one_of_sq_add hκ
  have hXiY := heisC_XiY hκ hXY hXXi hXiX
  have e1 : κ ^ 2 * κ ^ 2 = κ := by
    calc κ ^ 2 * κ ^ 2 = κ ^ 3 * κ := by ring
      _ = κ := by rw [h3, one_mul]
  calc Xi * Xi * Y = Xi * (Xi * Y) := mul_assoc _ _ _
    _ = Xi * (κ ^ 2 • (Y * Xi)) := by rw [hXiY]
    _ = κ ^ 2 • ((Xi * Y) * Xi) := by rw [mul_smul_comm, mul_assoc]
    _ = κ ^ 2 • ((κ ^ 2 • (Y * Xi)) * Xi) := by rw [hXiY]
    _ = (κ ^ 2 * κ ^ 2) • (Y * (Xi * Xi)) := by rw [smul_mul_assoc, smul_smul, mul_assoc]
    _ = κ • (Y * (Xi * Xi)) := by rw [e1]

include hκ hXY hXXi hXiX in
theorem heisC_M'Y : X * X * N * (Xi * Xi) * Y = κ • (X * X * N * Y * (Xi * Xi)) := by
  calc X * X * N * (Xi * Xi) * Y = X * X * N * (Xi * Xi * Y) := by simp only [mul_assoc]
    _ = κ • (X * X * N * Y * (Xi * Xi)) := by
        rw [heisC_XiXiY hκ hXY hXXi hXiX, mul_smul_comm]
        simp only [mul_assoc]

include hκ hXY hXXi hXiX hYN hNY in
theorem heisInvC_comm_Y : Y * heisInvC X Xi N = heisInvC X Xi N * Y := by
  have e1 := heisC_YM (N := N) (Xi := Xi) hκ hXY
  have e2 := heisC_MY (N := N) hκ hXY hXXi hXiX
  have e3 := heisC_YM' (N := N) (Xi := Xi) hκ hXY
  have e4 := heisC_M'Y (N := N) hκ hXY hXXi hXiX
  rw [mul_assoc X Y N, hYN] at e1
  rw [mul_assoc X N Y, hNY] at e2
  rw [mul_assoc (X * X) Y N, hYN] at e3
  rw [mul_assoc (X * X) N Y, hNY] at e4
  simp only [heisInvC, mul_add, add_mul, mul_one, one_mul, e1, e2, e3, e4, hYN, hNY]

include h2 hκ hXY hXXi hXiX hYN hNY hNN in
theorem heisInvC_ne_smul (hN0 : N ≠ 0) (d : K) : heisInvC X Xi N ≠ d • 1 := by
  intro hd
  have h3 := cube_eq_one_of_sq_add hκ
  have hYX := heisC_YX hκ hXY
  have hXiY := heisC_XiY hκ hXY hXXi hXiX
  set π : R := Y * Y + Y + 1 with hπ
  have hNπ : N * π = N := by
    have hNN' : N + N = 0 := by rw [← two_smul K N, h2, zero_smul]
    rw [hπ, mul_add, mul_add, ← mul_assoc, hNY, hNY, mul_one, hNN', zero_add]
  have hMY := heisC_MY (N := N) hκ hXY hXXi hXiX
  rw [mul_assoc X N Y, hNY] at hMY
  have hMπ : X * N * Xi * π = 0 := by
    have e : X * N * Xi * π = (κ ^ 2 * κ ^ 2 + κ ^ 2 + 1) • (X * N * Xi) := by
      rw [hπ, mul_add, mul_add, mul_one, ← mul_assoc, hMY, smul_mul_assoc, hMY, smul_smul, add_smul,
        add_smul, one_smul]
    rw [e]
    have : κ ^ 2 * κ ^ 2 + κ ^ 2 + 1 = 0 := by
      have : κ ^ 2 * κ ^ 2 = κ := by
        calc κ ^ 2 * κ ^ 2 = κ ^ 3 * κ := by ring
          _ = κ := by rw [h3, one_mul]
      rw [this]
      linear_combination hκ
    rw [this, zero_smul]
  have hM'Y := heisC_M'Y (N := N) hκ hXY hXXi hXiX
  rw [mul_assoc (X * X) N Y, hNY] at hM'Y
  have hM'π : X * X * N * (Xi * Xi) * π = 0 := by
    have e : X * X * N * (Xi * Xi) * π = (κ * κ + κ + 1) • (X * X * N * (Xi * Xi)) := by
      rw [hπ, mul_add, mul_add, mul_one, ← mul_assoc, hM'Y, smul_mul_assoc, hM'Y, smul_smul, add_smul,
        add_smul, one_smul]
    rw [e]
    have : κ * κ + κ + 1 = 0 := by linear_combination hκ
    rw [this, zero_smul]
  have hTπ : heisInvC X Xi N * π = π + N := by
    simp only [heisInvC, add_mul, one_mul, hNπ, hMπ, hM'π, add_zero]
  rw [hd, smul_mul_assoc, one_mul] at hTπ
  have hN : N = (d - 1) • π := by
    rw [sub_smul, one_smul, hTπ]
    abel
  have h0 : (d - 1) • N = 0 := by
    calc (d - 1) • N = (d - 1) • (N * π) := by rw [hNπ]
      _ = N * ((d - 1) • π) := by rw [mul_smul_comm]
      _ = N * N := by rw [← hN]
      _ = 0 := hNN
  by_cases hd1 : d - 1 = 0
  · rw [hd1, zero_smul] at hN
    exact hN0 hN
  · exact hN0 (heisC_eq_zero_of_smul hd1 h0)

end HeisC

section MatC

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K)

theorem ct_heisInvC {X Xi N : Matrix (Fin n) (Fin n) K} (hX : ct h X = Xi) (hXi : ct h Xi = X)
    (hN : ct h N = N) : ct h (heisInvC X Xi N) = heisInvC X Xi N := by
  simp only [heisInvC, ct_add, ct_mul, ct_one, hX, hXi, hN]
  simp only [mul_assoc]

theorem exists_heis_involution_c [CharP K 2] (hq3 : 3 ∣ p ^ f + 1) (hn : 4 ≤ n)
    {x y : GL (Fin n) K}
    (hx : x ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hy : y ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hy3 : y ^ 3 = 1) {c : Kˣ} (hx3 : x ^ 3 = GeneralLinearGroup.scalar (Fin n) c) {κ : K}
    (hxy : (x : Matrix (Fin n) (Fin n) K) * y = κ • ((y : Matrix (Fin n) (Fin n) K) * x))
    (hκ1 : κ ≠ 1) :
    ∃ t ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), t ^ 2 = 1 ∧
      (∀ d : Kˣ, t ≠ GeneralLinearGroup.scalar (Fin n) d) ∧ x * t = t * x ∧ y * t = t * y := by
  classical
  haveI : Finite K := h.finite
  have hn1 : 1 ≤ n := by omega
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hκ3 : κ ^ 3 = 1 := cube_eq_one_of_comm hn1 hxy ⟨1, by rw [hy3, map_one]⟩
  have hκ : κ ^ 2 + κ + 1 = 0 := by
    have : (κ - 1) * (κ ^ 2 + κ + 1) = 0 := by linear_combination hκ3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hκ1)
  set U := primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hUdef
  set yU : ↥U := ⟨y, hy⟩ with hyUdef
  have hyU3 : yU ^ 3 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hy3)
  have hA₁comm : ∀ a ∈ Subgroup.zpowers yU, ∀ b ∈ Subgroup.zpowers yU, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (Commute.zpow_zpow_self yU i j).eq
  have hA₁pow : ∀ a ∈ Subgroup.zpowers yU, a ^ 3 = 1 := by
    rintro _ ⟨i, rfl⟩
    simp only
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hyU3,
      _root_.one_zpow]
  obtain ⟨W₀, hW₀⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h Nat.prime_three hq3
    (Subgroup.zpowers yU) hA₁comm hA₁pow
  set W : GL (Fin n) K := (W₀ : GL (Fin n) K) with hWdef
  have hWU : W ∈ U := W₀.2
  set Wm : Matrix (Fin n) (Fin n) K := (W : Matrix (Fin n) (Fin n) K) with hWm
  set Wim : Matrix (Fin n) (Fin n) K := ((W⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hWim
  have hWW : Wm * Wim = 1 := by rw [hWm, hWim, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hWiW : Wim * Wm = 1 := by rw [hWm, hWim, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨Dy, hDydef⟩ : ∃ Dy : Matrix (Fin n) (Fin n) K,
      Dy = ((W⁻¹ * y * W : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := ⟨_, rfl⟩
  have hDy : Dy.IsDiag := by
    have h1 := hW₀ yU (Subgroup.mem_zpowers yU)
    rw [hDydef]
    simpa [hWdef, hyUdef] using h1
  have hDyM : Dy = Wim * (y : Matrix (Fin n) (Fin n) K) * Wm := by
    rw [hDydef, Units.val_mul, Units.val_mul]
  have hyM : (y : Matrix (Fin n) (Fin n) K) = Wm * Dy * Wim := by
    rw [hDyM]
    simp only [← mul_assoc, hWW, one_mul]
    rw [mul_assoc, hWW, mul_one]
  have hDy3 : Dy * Dy * Dy = 1 := by
    have e : (W⁻¹ * y * W) ^ 3 = W⁻¹ * y ^ 3 * W := by
      rw [pow_three', pow_three']
      group
    rw [hy3, mul_one, inv_mul_cancel] at e
    rw [hDydef, ← Units.val_mul, ← Units.val_mul, ← pow_three', e, Units.val_one]
  have hd3 : ∀ a, Dy a a ^ 3 = 1 := by
    intro a
    have e := congrFun (congrFun hDy3 a) a
    rw [← hDy.diagonal_diag] at e
    simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
      Matrix.diag_apply] at e
    rw [pow_three']
    exact e
  obtain ⟨a, -, b, -, hab, hdab⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := (Finset.univ : Finset (Fin n))) (t := (Polynomial.nthRoots 3 (1 : K)).toFinset)
    (f := fun i => Dy i i) (by
      calc (Polynomial.nthRoots 3 (1 : K)).toFinset.card ≤
            Multiset.card (Polynomial.nthRoots 3 (1 : K)) := Multiset.toFinset_card_le _
        _ ≤ 3 := Polynomial.card_nthRoots 3 1
        _ < (Finset.univ : Finset (Fin n)).card := by rw [Finset.card_univ, Fintype.card_fin]; omega)
    (fun i _ => by
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]
      exact hd3 i)
  have hdab' : Dy a a = Dy b b := hdab
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ = Dy a a := ⟨_, rfl⟩
  have hμ0 : μ ≠ 0 := by
    intro h0
    have := hd3 a
    rw [← hμ, h0] at this
    norm_num at this
  obtain ⟨Y', hY'⟩ : ∃ Y' : Matrix (Fin n) (Fin n) K, Y' = μ⁻¹ • (y : Matrix (Fin n) (Fin n) K) :=
    ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin n → K, v = Pi.single a 1 + Pi.single b 1 := ⟨_, rfl⟩
  have hva : v a = 1 := by simp [hv, Pi.single_apply, hab]
  have hvb : v b = 1 := by simp [hv, Pi.single_apply, Ne.symm hab]
  have hvo : ∀ r, r ≠ a → r ≠ b → v r = 0 := by
    intro r h1 h3
    simp [hv, Pi.single_apply, h1, h3]
  have hvv : v ⬝ᵥ v = 0 := by
    calc v ⬝ᵥ v = v ⬝ᵥ (Pi.single a 1 + Pi.single b 1) := by rw [← hv]
      _ = v a * 1 + v b * 1 := by rw [dotProduct_add, dotProduct_single, dotProduct_single]
      _ = 0 := by rw [hva, hvb, mul_one, one_add_one_eq_two, h2]
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin n) K, M = vecMulVec v v := ⟨_, rfl⟩
  have hMM : M * M = 0 := by rw [hM, vecMulVec_mul_vecMulVec, hvv, zero_smul, vecMulVec_zero]
  have hMe : ∀ r s, M r s = v r * v s := fun r s => by rw [hM, vecMulVec_apply]
  have hD'diag : (μ⁻¹ • Dy).IsDiag := hDy.smul _
  have hD'a : (μ⁻¹ • Dy) a a = 1 := by rw [Matrix.smul_apply, smul_eq_mul, ← hμ, inv_mul_cancel₀ hμ0]
  have hD'b : (μ⁻¹ • Dy) b b = 1 := by
    rw [Matrix.smul_apply, smul_eq_mul, ← hdab', ← hμ, inv_mul_cancel₀ hμ0]
  have hD'M : (μ⁻¹ • Dy) * M = M := by
    rw [← hD'diag.diagonal_diag]
    ext r s
    rw [Matrix.diagonal_mul, Matrix.diag_apply, hMe]
    by_cases hra : r = a
    · rw [hra, hD'a, one_mul]
    · by_cases hrb : r = b
      · rw [hrb, hD'b, one_mul]
      · rw [hvo r hra hrb, zero_mul, mul_zero]
  have hMD' : M * (μ⁻¹ • Dy) = M := by
    rw [← hD'diag.diagonal_diag]
    ext r s
    rw [Matrix.mul_diagonal, Matrix.diag_apply, hMe]
    by_cases hsa : s = a
    · rw [hsa, hD'a, mul_one]
    · by_cases hsb : s = b
      · rw [hsb, hD'b, mul_one]
      · rw [hvo s hsa hsb, mul_zero, zero_mul]
  have hbv : ∀ r, h.bar (v r) = v r := by
    intro r
    by_cases hra : r = a
    · rw [hra, hva, map_one]
    · by_cases hrb : r = b
      · rw [hrb, hvb, map_one]
      · rw [hvo r hra hrb, map_zero]
  have hctM : ct h M = M := by
    ext r s
    rw [ct, Matrix.transpose_apply, Matrix.map_apply, hMe, hMe, map_mul, hbv, hbv, mul_comm]
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin n) K, N = Wm * M * Wim := ⟨_, rfl⟩
  have hNN : N * N = 0 := by
    rw [hN]
    calc Wm * M * Wim * (Wm * M * Wim) = Wm * (M * (Wim * Wm) * M) * Wim := by
          simp only [mul_assoc]
      _ = 0 := by rw [hWiW, mul_one, hMM, mul_zero, zero_mul]
  have hY'W : Y' = Wm * (μ⁻¹ • Dy) * Wim := by
    rw [hY', hyM, Matrix.mul_smul, Matrix.smul_mul]
  have hY'N : Y' * N = N := by
    rw [hY'W, hN]
    calc Wm * (μ⁻¹ • Dy) * Wim * (Wm * M * Wim) = Wm * ((μ⁻¹ • Dy) * (Wim * Wm) * M) * Wim := by
          simp only [mul_assoc]
      _ = Wm * M * Wim := by rw [hWiW, mul_one, hD'M]
  have hNY' : N * Y' = N := by
    rw [hY'W, hN]
    calc Wm * M * Wim * (Wm * (μ⁻¹ • Dy) * Wim) = Wm * (M * (Wim * Wm) * (μ⁻¹ • Dy)) * Wim := by
          simp only [mul_assoc]
      _ = Wm * M * Wim := by rw [hWiW, mul_one, hMD']
  have hctW : ct h Wm = Wim := ct_eq_inv_of_mem h hWU
  have hctWi : ct h Wim = Wm := by
    have := ct_eq_inv_of_mem h (inv_mem hWU)
    rwa [inv_inv] at this
  have hctN : ct h N = N := by
    rw [hN, ct_mul, ct_mul, hctW, hctWi, hctM, mul_assoc]
  have hN0 : N ≠ 0 := by
    intro h0
    have hM0 : M = 0 := by
      calc M = Wim * (Wm * M * Wim) * Wm := by
            simp only [← mul_assoc, hWiW, one_mul]
            rw [mul_assoc, hWiW, mul_one]
        _ = 0 := by rw [← hN, h0, mul_zero, zero_mul]
    have := hMe a a
    rw [hM0, hva, Matrix.zero_apply, mul_one] at this
    exact one_ne_zero this.symm
  set X : Matrix (Fin n) (Fin n) K := (x : Matrix (Fin n) (Fin n) K) with hXdef
  set Xi : Matrix (Fin n) (Fin n) K := ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hXidef
  have hXXi : X * Xi = 1 := by rw [hXdef, hXidef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hXiX : Xi * X = 1 := by rw [hXdef, hXidef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hX3 : X * X * X = (c : K) • 1 := by
    rw [hXdef, ← Units.val_mul, ← Units.val_mul, ← pow_three', hx3, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, smul_one_eq_diagonal]
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hXY' : X * Y' = κ • (Y' * X) := by
    rw [hY', Matrix.mul_smul, Matrix.smul_mul, hxy, smul_comm]
  have hTT := heisInvC_mul_self h2 hκ hXY' hXXi hXiX hX3 hc0 hY'N hNY' hNN
  have hTX := heisInvC_comm_X (N := N) hXXi hXiX hX3 hc0
  have hTY := heisInvC_comm_Y hκ hXY' hXXi hXiX hY'N hNY'
  have hTns := heisInvC_ne_smul h2 hκ hXY' hXXi hXiX hY'N hNY' hNN hN0
  have hctX : ct h X = Xi := ct_eq_inv_of_mem h hx
  have hctXi : ct h Xi = X := by
    have := ct_eq_inv_of_mem h (inv_mem hx)
    rwa [inv_inv] at this
  have hTct := ct_heisInvC h hctX hctXi hctN
  set T := heisInvC X Xi N with hTdef
  let t : GL (Fin n) K := ⟨T, T, hTT, hTT⟩
  have htU : t ∈ U := by
    rw [hUdef, mem_primeFormUnitary, Units.val_one, Matrix.mul_one]
    change ct h T * T = 1
    rw [hTct, hTT]
  have hdet : (T : Matrix (Fin n) (Fin n) K).det = 1 := by
    have e1 : T.det * T.det = 1 := by rw [← Matrix.det_mul, hTT, Matrix.det_one]
    have e2 : (T.det - 1) * (T.det - 1) = 0 := by linear_combination e1 - T.det * h2 + h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp e2)
  refine ⟨t, (mem_gramSU_iff_unitary h).mpr ⟨htU, hdet⟩, ?_, fun d hd => ?_, ?_, ?_⟩
  · rw [sq]
    exact Units.ext hTT
  · apply hTns (d : K)
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hd
    simp only [GeneralLinearGroup.coe_scalar] at this
    rw [smul_one_eq_diagonal]
    exact this
  · exact Units.ext hTX
  · apply Units.ext
    change (y : Matrix (Fin n) (Fin n) K) * T = T * y
    have hyY : (y : Matrix (Fin n) (Fin n) K) = μ • Y' := by
      rw [hY', smul_smul, mul_inv_cancel₀ hμ0, one_smul]
    rw [hyY, Matrix.smul_mul, Matrix.mul_smul, hTY]

end MatC

section SwapIJ

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K)

theorem exists_swap_involution_ij [CharP K 2] (W : GL (Fin n) K)
    (hW : W ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    {i₀ i₁ : Fin n} (h01 : i₀ ≠ i₁) :
    ∃ t ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), t ^ 2 = 1 ∧
      (∀ c : Kˣ, t ≠ GeneralLinearGroup.scalar (Fin n) c) ∧
      ∀ e : GL (Fin n) K, ((W⁻¹ * e * W : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag →
        ((W⁻¹ * e * W : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i₀ i₀ =
          ((W⁻¹ * e * W : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i₁ i₁ →
        e * t = t * e := by
  set s : GL (Fin n) K := CFSG.RankThree.Classical.unitaryPermGL (Equiv.swap i₀ i₁) with hsdef
  have hmap : ((Equiv.swap i₀ i₁).permMatrix K).map h.bar = (Equiv.swap i₀ i₁).permMatrix K :=
    Matrix.ext fun a b => by
      rw [Matrix.map_apply, CFSG.RankThree.Classical.permMatrix_apply']
      split_ifs <;> simp
  have hs : s ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    refine mem_gramSU.2 ⟨?_, ?_⟩
    · rw [Units.val_one, Matrix.mul_one, hsdef, CFSG.RankThree.Classical.coe_unitaryPermGL, hmap,
        Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
        Matrix.permMatrix_one]
    · rw [hsdef, CFSG.RankThree.Classical.coe_unitaryPermGL, Matrix.det_permutation,
        Equiv.Perm.sign_swap h01, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
      exact CharTwo.neg_eq 1
  have hs2 : s * s = 1 := Units.ext (by
    rw [Units.val_mul, hsdef, CFSG.RankThree.Classical.coe_unitaryPermGL, ← Matrix.permMatrix_mul,
      Equiv.swap_mul_self, Matrix.permMatrix_one, Units.val_one])
  refine ⟨W * s * W⁻¹, conj_mem_gramSU h _ hW hs, ?_, ?_, ?_⟩
  · rw [sq]
    calc W * s * W⁻¹ * (W * s * W⁻¹) = W * (s * s) * W⁻¹ := by group
      _ = 1 := by rw [hs2, mul_one, mul_inv_cancel]
  · intro c hc
    have hsc : s = GeneralLinearGroup.scalar (Fin n) c := by
      have e1 : s = W⁻¹ * (W * s * W⁻¹) * W := by group
      rw [e1, hc, (commute_scalar c W⁻¹).eq, mul_assoc, inv_mul_cancel, mul_one]
    have e2 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i₁ i₀) hsc
    simp only [hsdef, CFSG.RankThree.Classical.coe_unitaryPermGL,
      CFSG.RankThree.Classical.permMatrix_apply', Equiv.swap_apply_right, if_true,
      GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h01.symm] at e2
    exact one_ne_zero e2
  · intro e hD hd
    have hDs : (W⁻¹ * e * W) * s = s * (W⁻¹ * e * W) := Units.ext (by
      rw [Units.val_mul, Units.val_mul, hsdef, CFSG.RankThree.Classical.coe_unitaryPermGL]
      exact diag_mul_swap_comm hD hd)
    calc e * (W * s * W⁻¹) = W * ((W⁻¹ * e * W) * s) * W⁻¹ := by group
      _ = W * (s * (W⁻¹ * e * W)) * W⁻¹ := by rw [hDs]
      _ = W * s * W⁻¹ * e := by group

end SwapIJ

section Local3

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313InAux

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K)

theorem exists_centralized_involution_three [CharP K 2] (hq3 : 3 ∣ p ^ f + 1) (hn : 4 ≤ n)
    (P : Subgroup (GL (Fin n) K))
    (hPU : P ≤ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hZ : ∀ c : Kˣ, h.norm (c : K) = 1 → GeneralLinearGroup.scalar (Fin n) c ∈ P)
    (hcube : ∀ g ∈ P, ∃ c : Kˣ, g ^ 3 = GeneralLinearGroup.scalar (Fin n) c)
    (hcomm : ∀ g ∈ P, ∀ g' ∈ P, ∃ c : Kˣ,
      g * g' = GeneralLinearGroup.scalar (Fin n) c * (g' * g)) :
    ∃ E : Subgroup (GL (Fin n) K), E ≤ P ∧
      (Nat.card P ≤ 3 * Nat.card E ∨ ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) ∧
      ∃ t ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), t ^ 2 = 1 ∧
        (∀ c : Kˣ, t ≠ GeneralLinearGroup.scalar (Fin n) c) ∧ ∀ e ∈ E, e * t = t * e := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  haveI : Finite K := h.finite
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite (GL (Fin n) K) := inferInstance
  by_cases hc3 : ∃ y ∈ P, y ^ 3 = 1 ∧ ∃ x ∈ P, x * y ≠ y * x
  ·
    obtain ⟨y, hyP, hy3, x, hxP, hxy⟩ := hc3
    obtain ⟨c, hc⟩ := hcomm x hxP y hyP
    have hc' : (x : Matrix (Fin n) (Fin n) K) * y =
        (c : K) • ((y : Matrix (Fin n) (Fin n) K) * x) := by
      rw [← Units.val_mul, hc, coe_scalar_mul, Units.val_mul]
    have hc1 : (c : K) ≠ 1 := by
      intro h1
      apply hxy
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hc', h1, one_smul]
    obtain ⟨d, hd⟩ := hcube x hxP
    obtain ⟨t, htSU, ht2, htns, htx, hty⟩ :=
      exists_heis_involution_c h hq3 hn (hPU hxP) (hPU hyP) hy3 hd hc' hc1
    refine ⟨P ⊓ Subgroup.centralizer ({t} : Set (GL (Fin n) K)), inf_le_left,
      Or.inr ⟨x, ⟨hxP, Subgroup.mem_centralizer_singleton_iff.2 htx⟩, y,
        ⟨hyP, Subgroup.mem_centralizer_singleton_iff.2 hty⟩, hxy⟩, t, htSU, ht2, htns,
      fun e he => Subgroup.mem_centralizer_singleton_iff.1 he.2⟩
  · push Not at hc3
    set U := primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hUdef
    let A₁ : Subgroup ↥U :=
      { carrier := {a | (a : GL (Fin n) K) ∈ P ∧ (a : GL (Fin n) K) ^ 3 = 1}
        mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
          rw [Subgroup.coe_mul,
            (show Commute (a : GL (Fin n) K) b from hc3 _ hb.1 hb.2 _ ha.1).mul_pow, ha.2, hb.2,
            one_mul]⟩
        one_mem' := ⟨one_mem _, one_pow 3⟩
        inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [Subgroup.coe_inv, inv_pow, ha.2, inv_one]⟩ }
    have hA₁comm : ∀ a ∈ A₁, ∀ b ∈ A₁, a * b = b * a := fun a ha b hb =>
      Subtype.ext (hc3 _ hb.1 hb.2 _ ha.1)
    have hA₁pow : ∀ a ∈ A₁, a ^ 3 = 1 := fun a ha =>
      Subtype.ext (by rw [Subgroup.coe_pow, ha.2, Subgroup.coe_one])
    obtain ⟨W₀, hW₀⟩ :=
      CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h Nat.prime_three hq3 A₁ hA₁comm hA₁pow
    set W : GL (Fin n) K := (W₀ : GL (Fin n) K) with hWdef
    have hcs : ∀ g : ↥P, ∃ c : Kˣ, (g : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) c :=
      fun g => hcube g g.2
    have hmul3 : ∀ g ∈ P, ∀ g' ∈ P, (g * g') ^ 3 = g ^ 3 * g' ^ 3 := fun g hg g' hg' => by
      obtain ⟨c, hc⟩ := hcomm g hg g' hg'
      exact cube_mul_of_comm hn1 hc (hcube g' hg')
    let ψ : ↥P →* Kˣ :=
      { toFun := fun g => (hcs g).choose
        map_one' := scalar_injective hn1 (by
          rw [← (hcs 1).choose_spec, Subgroup.coe_one, one_pow, map_one])
        map_mul' := fun g g' => scalar_injective hn1 (by
          rw [map_mul, ← (hcs g).choose_spec, ← (hcs g').choose_spec, ← (hcs (g * g')).choose_spec,
            Subgroup.coe_mul, hmul3 g g.2 g' g'.2]) }
    have hψ : ∀ g : ↥P, (g : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) (ψ g) :=
      fun g => (hcs g).choose_spec
    have hψN : ∀ g : ↥P, ψ g ∈ rootsOfUnity (p ^ f + 1) K := fun g => by
      have hmem : GeneralLinearGroup.scalar (Fin n) (ψ g) ∈ U := by
        rw [← hψ g]
        exact pow_mem (hPU g.2) 3
      have hN := norm_eq_one_of_scalar_mem_primeFormUnitary h hn1 1 hmem
      rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one,
        ← h.norm_eq_pow]
      exact hN
    let ψ' : ↥P →* ↥(rootsOfUnity (p ^ f + 1) K) := ψ.codRestrict _ hψN
    set C3 := (powMonoidHom 3 : ↥(rootsOfUnity (p ^ f + 1) K) →*
      ↥(rootsOfUnity (p ^ f + 1) K)).range with hC3
    set P₁ : Subgroup ↥P := C3.comap ψ' with hP₁
    have hP₁idx : P₁.index ≤ 3 := by
      rw [hP₁, Subgroup.index_comap]
      have hdvd : C3.relIndex ψ'.range ∣ C3.index := Subgroup.relIndex_dvd_index_of_normal _ _
      have hidx3 : C3.index = (Nat.card ↥(rootsOfUnity (p ^ f + 1) K)).gcd 3 :=
        IsCyclic.index_powMonoidHom_range _ 3
      have hpos : 0 < C3.index := by
        rw [hidx3]
        exact Nat.gcd_pos_of_pos_right _ (by norm_num)
      exact (Nat.le_of_dvd hpos hdvd).trans (hidx3 ▸ Nat.gcd_le_right _ (by norm_num))
    have hdecomp : ∀ g : ↥P, g ∈ P₁ → ∃ d : Kˣ, ∃ a : GL (Fin n) K, a ∈ P ∧ a ^ 3 = 1 ∧
        (g : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) d * a := by
      intro g hg
      obtain ⟨d, hd⟩ := hg
      have hd' : ((d : Kˣ)) ^ 3 = ψ g := by
        have := congrArg Subtype.val hd
        simpa [ψ'] using this
      have hdN : h.norm ((d : Kˣ) : K) = 1 := by
        have h1 := d.2
        rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one,
          ← h.norm_eq_pow] at h1
        exact h1
      have hdinvN : h.norm (((d : Kˣ)⁻¹ : Kˣ) : K) = 1 := by
        rw [Units.val_inv_eq_inv_val, CFSG.ClassicalGroups.UnitaryFlag.norm_inv_eq h, hdN, inv_one]
      refine ⟨(d : Kˣ), GeneralLinearGroup.scalar (Fin n) (d : Kˣ)⁻¹ * g,
        mul_mem (hZ _ hdinvN) g.2, ?_, ?_⟩
      · rw [((commute_scalar ((d : Kˣ)⁻¹) (g : GL (Fin n) K)).symm).mul_pow, hψ g, ← map_pow,
          ← map_mul, inv_pow, hd', inv_mul_cancel, map_one]
      · rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    have hP₁cen : ∀ g : ↥P, g ∈ P₁ → ∀ x ∈ P, x * (g : GL (Fin n) K) = (g : GL (Fin n) K) * x := by
      intro g hg x hx
      obtain ⟨d, a, haP, ha3, hga⟩ := hdecomp g hg
      have hxa : x * a = a * x := hc3 a haP ha3 x hx
      rw [hga]
      calc x * (GeneralLinearGroup.scalar (Fin n) d * a) =
            GeneralLinearGroup.scalar (Fin n) d * (x * a) := by
            rw [← mul_assoc, (commute_scalar d x).eq, mul_assoc]
        _ = GeneralLinearGroup.scalar (Fin n) d * a * x := by rw [hxa, mul_assoc]
    set D : ↥P → Matrix (Fin n) (Fin n) K := fun g =>
      ((W⁻¹ * (g : GL (Fin n) K) * W : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hDdef
    have hdiag : ∀ g : ↥P, g ∈ P₁ → (D g).IsDiag := by
      intro g hg
      obtain ⟨d, a, haP, ha3, hga⟩ := hdecomp g hg
      have haA : (⟨a, hPU haP⟩ : ↥U) ∈ A₁ := ⟨haP, ha3⟩
      have hDa := hW₀ _ haA
      have hconjga : W⁻¹ * (g : GL (Fin n) K) * W =
          GeneralLinearGroup.scalar (Fin n) d * (W⁻¹ * a * W) := by
        rw [hga, ← mul_assoc W⁻¹, (commute_scalar d W⁻¹).eq]
        simp only [mul_assoc]
      have hDg : D g = (d : K) • ((W⁻¹ * a * W : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        simp only [hDdef]
        rw [hconjga, coe_scalar_mul]
      rw [hDg]
      exact hDa.smul _
    have hDmul : ∀ g g' : ↥P, D (g * g') = D g * D g' := fun g g' => by
      simp only [hDdef]
      rw [← Units.val_mul]
      congr 1
      simp only [Subgroup.coe_mul]
      group
    by_cases hsep : ∃ i₀ i₁ : Fin n, i₀ ≠ i₁ ∧ ∀ g : ↥P, g ∈ P₁ → D g i₀ i₀ = D g i₁ i₁
    ·
      obtain ⟨i₀, i₁, h01, heq⟩ := hsep
      obtain ⟨t, htSU, ht2, htns, htc⟩ := exists_swap_involution_ij h W W₀.2 h01
      refine ⟨P₁.map P.subtype, Subgroup.map_subtype_le _, Or.inl ?_, t, htSU, ht2, htns, ?_⟩
      · have hE1 : Nat.card (P₁.map P.subtype) = Nat.card P₁ :=
          Subgroup.card_map_of_injective P.subtype_injective
        have h1 := Subgroup.card_mul_index P₁
        rw [hE1]
        calc Nat.card P = Nat.card P₁ * P₁.index := h1.symm
          _ ≤ Nat.card P₁ * 3 := Nat.mul_le_mul_left _ hP₁idx
          _ = 3 * Nat.card P₁ := mul_comm _ _
      · rintro _ ⟨g, hg, rfl⟩
        exact htc _ (hdiag g hg) (heq g hg)
    · push Not at hsep
      have hdiagP : ∀ g : ↥P, (D g).IsDiag := by
        intro g i j hij
        obtain ⟨k, hk, hne⟩ := hsep i j hij
        have hgk : D g * D k = D k * D g := by
          rw [← hDmul, ← hDmul]
          congr 1
          exact Subtype.ext (hP₁cen k hk g g.2)
        have e := congrFun (congrFun hgk i) j
        rw [← (hdiag k hk).diagonal_diag, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diag_apply,
          Matrix.diag_apply] at e
        have : D g i j * (D k j j - D k i i) = 0 := by linear_combination e
        exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 (Ne.symm hne))
      have hDne : ∀ g : ↥P, ∀ i, D g i i ≠ 0 := by
        intro g i hi
        have hdet : (D g).det ≠ 0 := (Matrix.isUnits_det_units _).ne_zero
        rw [← (hdiagP g).diagonal_diag, Matrix.det_diagonal] at hdet
        exact hdet (Finset.prod_eq_zero (Finset.mem_univ i) hi)
      have hDentry : ∀ g g' : ↥P, ∀ i, D (g * g') i i = D g i i * D g' i i := by
        intro g g' i
        rw [hDmul]
        calc (D g * D g') i i = (Matrix.diagonal (Matrix.diag (D g)) * D g') i i := by
              rw [(hdiagP g).diagonal_diag]
          _ = D g i i * D g' i i := by rw [Matrix.diagonal_mul]; rfl
      obtain ⟨t, htSU, ht2, htns, htc⟩ := exists_swap_involution h hn2 W W₀.2
      set i₀ : Fin n := ⟨0, by omega⟩
      set i₁ : Fin n := ⟨1, by omega⟩
      let χ : ↥P →* Kˣ :=
        { toFun := fun g => Units.mk0 (D g i₀ i₀) (hDne g i₀) * (Units.mk0 (D g i₁ i₁) (hDne g i₁))⁻¹
          map_one' := by
            apply Units.ext
            have h1 : D (1 : ↥P) = 1 := by
              simp only [hDdef, OneMemClass.coe_one, mul_one, inv_mul_cancel, Units.val_one]
            simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, h1,
              Matrix.one_apply_eq, inv_one, mul_one, Units.val_one]
          map_mul' := fun g g' => by
            apply Units.ext
            simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
            rw [hDentry _ _ i₀, hDentry _ _ i₁, mul_inv]
            ring }
      have hχ3 : ∀ g : ↥P, χ g ^ 3 = 1 := by
        intro g
        rw [← map_pow]
        apply Units.ext
        have h1 : D (g ^ 3) = ((ψ g : Kˣ) : K) • 1 := by
          have e1 : ((g ^ 3 : ↥P) : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) (ψ g) := by
            rw [SubgroupClass.coe_pow, hψ]
          simp only [hDdef]
          rw [e1, (commute_scalar (ψ g) W⁻¹).eq, mul_assoc, inv_mul_cancel, mul_one,
            GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, smul_one_eq_diagonal]
        change ((Units.mk0 (D _ i₀ i₀) _ * (Units.mk0 (D _ i₁ i₁) _)⁻¹ : Kˣ) : K) = 1
        simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, h1, Matrix.smul_apply,
          Matrix.one_apply_eq, smul_eq_mul, mul_one]
        exact mul_inv_cancel₀ (ψ g).ne_zero
      have hrange : χ.range ≤ rootsOfUnity 3 K := by
        rintro _ ⟨g, rfl⟩
        exact (mem_rootsOfUnity 3 _).2 (hχ3 g)
      have hkeridx : χ.ker.index ≤ 3 := by
        rw [Subgroup.index_ker]
        exact (Subgroup.card_le_of_le hrange).trans (card_rootsOfUnity K 3)
      refine ⟨χ.ker.map P.subtype, Subgroup.map_subtype_le _, Or.inl ?_, t, htSU, ht2, htns, ?_⟩
      · have hE1 : Nat.card (χ.ker.map P.subtype) = Nat.card χ.ker :=
          Subgroup.card_map_of_injective P.subtype_injective
        have h2 := Subgroup.card_mul_index χ.ker
        rw [hE1]
        calc Nat.card P = Nat.card χ.ker * χ.ker.index := h2.symm
          _ ≤ Nat.card χ.ker * 3 := Nat.mul_le_mul_left _ hkeridx
          _ = 3 * Nat.card χ.ker := mul_comm _ _
      · rintro _ ⟨k, hk, rfl⟩
        have hk1 : χ k = 1 := hk
        have heq : D k i₀ i₀ = D k i₁ i₁ := by
          have := congrArg (fun u : Kˣ => (u : K)) hk1
          simp only [χ, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul, Units.val_mk0,
            Units.val_inv_eq_inv_val, Units.val_one] at this
          exact (mul_inv_eq_one₀ (hDne _ i₁)).1 this
        exact htc _ (hdiagP k) heq

end Local3

section Star3

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313InAux
  CFSG.Open CFSG.LieType.Chevalley

@[expose] def Star3Concl {S : Type*} [Group S] (D : Subgroup (MulAut S)) : Prop :=
  ∃ E : Subgroup (MulAut S), E ≤ D ∧ (Nat.card D ≤ 3 * Nat.card E ∨ 9 ≤ Nat.card E) ∧
    ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U

theorem star3Concl_of_congr {S C : Type*} [Group S] [Group C] [Finite S] (e : S ≃* C)
    (D : Subgroup (MulAut S)) (h : Star3Concl (D.map (MulAut.congr e).toMonoidHom)) :
    Star3Concl D := by
  obtain ⟨E', hE'D, hcard, U', hU'0, hU'2, hU'⟩ := h
  set c := MulAut.congr e with hc
  have hEA : E'.map c.symm.toMonoidHom ≤ D := by
    rintro _ ⟨φ', hφ', rfl⟩
    obtain ⟨ψ, hψ, rfl⟩ := hE'D hφ'
    simpa using hψ
  have h2 : Nat.card D = Nat.card (D.map c.toMonoidHom) :=
    (Subgroup.card_map_of_injective c.injective).symm
  have h3 : Nat.card (E'.map c.symm.toMonoidHom) = Nat.card E' :=
    Subgroup.card_map_of_injective c.symm.injective
  refine ⟨E'.map c.symm.toMonoidHom, hEA, ?_, U'.map e.symm.toMonoidHom, ?_, hU'2.map _, ?_⟩
  · rw [h2, h3]
    exact hcard
  · intro h
    exact hU'0 ((Subgroup.map_eq_bot_iff_of_injective U' (f := e.symm.toMonoidHom)
      e.symm.injective).1 h)
  · rintro _ ⟨φ', hφ', rfl⟩ _ ⟨u', hu', rfl⟩
    refine ⟨φ' u', hU' φ' hφ' u' hu', ?_⟩
    simp [hc, MulAut.congr_apply]

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem star3Concl_of_le_primeFormD (h : UnitaryFieldData p f K) [CharP K 2] (hq3 : 3 ∣ p ^ f + 1)
    (hn : 4 ≤ n)
    (D : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))
    (hD : IsElemAbelian 3 D)
    (hDle : D ≤ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    Star3Concl D := by
  classical
  haveI : Finite K := h.finite
  haveI : Finite (GL (Fin n) K) := inferInstance
  have hn3 : 3 ≤ n := by omega
  set U := primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hUdef
  set c := primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hcdef
  set PU : Subgroup ↥U := D.comap c with hPUdef
  set P : Subgroup (GL (Fin n) K) := PU.map U.subtype with hPdef
  have hPU : P ≤ U := Subgroup.map_subtype_le PU
  have hmemP : ∀ A : ↥U, (A : GL (Fin n) K) ∈ P ↔ c A ∈ D := fun A =>
    ⟨fun ⟨B, hB, hBA⟩ => by rw [← Subtype.ext hBA]; exact hB, fun hA => ⟨A, hA, rfl⟩⟩
  have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hZ : ∀ z : Kˣ, h.norm (z : K) = 1 → GeneralLinearGroup.scalar (Fin n) z ∈ P := by
    intro z hz
    have hzU := scalar_mem_primeFormUnitary h (n := n) hz
    refine (hmemP ⟨_, hzU⟩).2 ?_
    rw [hcdef, CFSG.RankThree.Classical.primeFormConjHom_scalar h n z hzU]
    exact one_mem D
  have hcube : ∀ g ∈ P, ∃ z : Kˣ, g ^ 3 = GeneralLinearGroup.scalar (Fin n) z := by
    rintro _ ⟨A, hA, rfl⟩
    have h1 : c (A ^ 3) = 1 := by rw [map_pow]; exact hD.2 _ hA
    obtain ⟨z, hz⟩ := exists_scalar_of_conjHom_eq_one h hn3 h1
    exact ⟨z, by rw [← hz]; rfl⟩
  have hcomm : ∀ g ∈ P, ∀ g' ∈ P, ∃ z : Kˣ,
      g * g' = GeneralLinearGroup.scalar (Fin n) z * (g' * g) := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    have h1 : c (A * B * A⁻¹ * B⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hDcomm _ hA _ hB]
      group
    obtain ⟨z, hz⟩ := exists_scalar_of_conjHom_eq_one h hn3 h1
    refine ⟨z, ?_⟩
    have hz' : (A : GL (Fin n) K) * B * (A : GL (Fin n) K)⁻¹ * (B : GL (Fin n) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin n) z := hz
    calc (A : GL (Fin n) K) * B = ((A : GL (Fin n) K) * B * (A : GL (Fin n) K)⁻¹ *
          (B : GL (Fin n) K)⁻¹) * (B * A) := by group
      _ = GeneralLinearGroup.scalar (Fin n) z * (B * A) := by rw [hz']
  obtain ⟨EG, hEGP, hcard, t, htSU, ht2, htns, htc⟩ :=
    exists_centralized_involution_three h hq3 hn P hPU hZ hcube hcomm
  set EU : Subgroup ↥U := EG.comap U.subtype with hEUdef
  have hEUPU : EU ≤ PU := fun x hx => (hmemP x).1 (hEGP hx)
  set E : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :=
    EU.map c with hEdef
  have hED : E ≤ D := by
    rintro _ ⟨x, hx, rfl⟩
    exact hEUPU hx
  set tP : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    ((⟨t, htSU⟩ : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
      primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) with htPdef
  have htP2 : tP ^ 2 = 1 := by
    rw [htPdef, ← QuotientGroup.mk_pow]
    have : (⟨t, htSU⟩ : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ 2 = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow]; exact ht2)
    rw [this, QuotientGroup.mk_one]
  have htP1 : tP ≠ 1 := by
    intro h1
    rw [htPdef, QuotientGroup.eq_one_iff] at h1
    obtain ⟨z, -, -, hz⟩ := h1
    exact htns z hz
  have hEfix : ∀ φ ∈ E, φ tP = tP := by
    rintro _ ⟨x, hx, rfl⟩
    rw [htPdef, hcdef, primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    change (x : GL (Fin n) K) * t * (x : GL (Fin n) K)⁻¹ = t
    rw [htc (x : GL (Fin n) K) hx, mul_inv_cancel_right]
  refine ⟨E, hED, ?_, Subgroup.zpowers tP, ?_, ?_, ?_⟩
  · rcases hcard with hcard | ⟨x, hxE, y, hyE, hxy⟩
    ·
      left
      let fP : ↥PU →* ↥D := (c.comp PU.subtype).codRestrict D (fun x => x.2)
      have hfP : Function.Surjective fP := by
        rintro ⟨α, hα⟩
        obtain ⟨A, hA⟩ := hDle hα
        exact ⟨⟨A, show c A ∈ D by rw [hA]; exact hα⟩, Subtype.ext hA⟩
      have hmap : (EU.subgroupOf PU).map fP = E.subgroupOf D := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact Subgroup.mem_subgroupOf.2 ⟨y, Subgroup.mem_subgroupOf.1 hy, rfl⟩
        · intro hx
          obtain ⟨y, hy, hyx⟩ := Subgroup.mem_subgroupOf.1 hx
          exact ⟨⟨y, hEUPU hy⟩, Subgroup.mem_subgroupOf.2 hy, Subtype.ext hyx⟩
      have hcardPU : Nat.card PU = Nat.card P := by
        rw [hPdef, Subgroup.card_map_of_injective U.subtype_injective]
      have hEGU : EG ≤ U := hEGP.trans hPU
      have hmapEU : EU.map U.subtype = EG :=
        Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hEGU)
      have hcardEU : Nat.card (EU.subgroupOf PU) = Nat.card EG := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEUPU).toEquiv, ← hmapEU,
          Subgroup.card_map_of_injective U.subtype_injective]
      have hidxEU : (EU.subgroupOf PU).index ≤ 3 := by
        have h1 := Subgroup.card_mul_index (EU.subgroupOf PU)
        rw [hcardEU, hcardPU] at h1
        have hpos : 0 < Nat.card EG := Nat.card_pos
        by_contra hlt
        push Not at hlt
        have : 4 * Nat.card EG ≤ (EU.subgroupOf PU).index * Nat.card EG :=
          Nat.mul_le_mul_right _ hlt
        rw [mul_comm (EU.subgroupOf PU).index, h1] at this
        omega
      have hdvd := Subgroup.index_map_dvd (H := EU.subgroupOf PU) hfP
      rw [hmap] at hdvd
      have hne : (EU.subgroupOf PU).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hrel : E.relIndex D ≤ 3 := (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd).trans hidxEU
      have h2 := Subgroup.relIndex_mul_card E D
      rw [inf_of_le_left hED] at h2
      rw [← h2]
      exact Nat.mul_le_mul_right _ hrel
    ·
      right
      have hxU : x ∈ U := hPU (hEGP hxE)
      have hyU : y ∈ U := hPU (hEGP hyE)
      have hcxE : c ⟨x, hxU⟩ ∈ E := ⟨⟨x, hxU⟩, hxE, rfl⟩
      have hcyE : c ⟨y, hyU⟩ ∈ E := ⟨⟨y, hyU⟩, hyE, rfl⟩
      have hEp : IsPGroup 3 E := (hD.mono hED).isPGroup
      have hcy1 : c ⟨y, hyU⟩ ≠ 1 := by
        intro h1
        obtain ⟨z, hz⟩ := exists_scalar_of_conjHom_eq_one h hn3 h1
        apply hxy
        have hz' : y = GeneralLinearGroup.scalar (Fin n) z := hz
        rw [hz']
        exact (commute_scalar z x).eq
      have hcy3 : c ⟨y, hyU⟩ ^ 3 = 1 := hD.2 _ (hED hcyE)
      have hord : orderOf (c ⟨y, hyU⟩) = 3 := orderOf_eq_prime hcy3 hcy1
      by_contra hlt
      push Not at hlt
      obtain ⟨k, hk⟩ := hEp.exists_card_eq
      have hk1 : k ≤ 1 := by
        by_contra hk2
        push Not at hk2
        have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
        omega
      have hzp : Subgroup.zpowers (c ⟨y, hyU⟩) = E := by
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hcyE)
        rw [hk, Nat.card_zpowers, hord]
        calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
          _ = 3 := pow_one 3
      rw [← hzp] at hcxE
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hcxE
      have h1 : c ((⟨y, hyU⟩ : ↥U) ^ m * (⟨x, hxU⟩ : ↥U)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_zpow, hm, mul_inv_cancel]
      obtain ⟨z, hz⟩ := exists_scalar_of_conjHom_eq_one h hn3 h1
      have hz' : y ^ m * x⁻¹ = GeneralLinearGroup.scalar (Fin n) z := by
        rw [← hz]
        rfl
      have hx' : x = (GeneralLinearGroup.scalar (Fin n) z)⁻¹ * y ^ m := by
        rw [← hz', _root_.mul_inv_rev, inv_inv, inv_mul_cancel_right]
      apply hxy
      rw [hx']
      calc (GeneralLinearGroup.scalar (Fin n) z)⁻¹ * y ^ m * y =
            (GeneralLinearGroup.scalar (Fin n) z)⁻¹ * (y * y ^ m) := by
            rw [mul_assoc, (Commute.zpow_self y m).eq]
        _ = y * ((GeneralLinearGroup.scalar (Fin n) z)⁻¹ * y ^ m) := by
            rw [← mul_assoc, ← map_inv, ← (commute_scalar z⁻¹ y).eq, mul_assoc]
  · intro hbot
    apply htP1
    have : tP ∈ Subgroup.zpowers tP := Subgroup.mem_zpowers tP
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  · intro u
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 u.2
    rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm,
      _root_.zpow_mul, zpow_natCast, htP2, _root_.one_zpow, Subgroup.coe_one]
  · intro φ hφ u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [map_zpow, hEfix φ hφ]
    exact Subgroup.zpow_mem_zpowers tP k

theorem star3Concl_two (h : UnitaryFieldData p f K) (hp : p = 2) (hf : f = 1) (hn : 4 ≤ n)
    (D : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))
    (hD : IsElemAbelian 3 D) : Star3Concl D := by
  subst hp hf
  haveI : CharP K 2 := h.charP
  haveI : Finite K := h.finite
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ 1 = 2) := by omega
  refine star3Concl_of_le_primeFormD h (by norm_num) hn D hD ?_
  intro β hβ
  rw [← ker_primeFormFieldFactor h isPrimeFormGram_one hn3 hq, MonoidHom.mem_ker]
  set θ := primeFormFieldFactor h isPrimeFormGram_one hn3 hq β
  have hcard : Nat.card (RingAut K) = 2 :=
    (card_ringAut_and_isCyclic Nat.prime_two K (h.card.trans (by norm_num))).1
  haveI : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h2 : θ ^ 2 = 1 := by
    have := pow_card_eq_one' (G := RingAut K) (x := θ)
    rwa [hcard] at this
  have h3 : θ ^ 3 = 1 := by rw [← map_pow, hD.2 β hβ, map_one]
  calc θ = θ ^ 3 * (θ ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2, one_mul, inv_one]

theorem star3Concl_eight (h : UnitaryFieldData p f K) (hp : p = 2) (hf : f = 3) (hn : 4 ≤ n)
    (D : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))
    (hD : IsElemAbelian 3 D) : Star3Concl D := by
  subst hp hf
  classical
  haveI : CharP K 2 := h.charP
  haveI : Finite K := h.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn3 : 3 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ 3 = 2) := by omega
  haveI : Finite (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :=
    MulEquiv.finite_left
  set Θ := primeFormFieldFactor h isPrimeFormGram_one hn3 hq with hΘ
  have hkerΘ := ker_primeFormFieldFactor h isPrimeFormGram_one hn3 hq
  by_cases hDle : D ≤ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  · exact star3Concl_of_le_primeFormD h (by norm_num) hn D hD hDle
  obtain ⟨b, hbD, hbout⟩ := Set.not_subset.1 hDle
  have hb3 : b ^ 3 = 1 := hD.2 b hbD
  set σ := Θ b with hσdef
  have hσ1 : σ ≠ 1 := fun h1 => hbout (by rw [← hkerΘ]; exact h1)
  have hσ3 : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, hb3, map_one]
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hb1 : b ≠ 1 := fun h1 => hσ1 (by rw [hσdef, h1, map_one])
  have hbord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn3 hq Nat.prime_three
      (by norm_num) (by norm_num) b hbord σ rfl hσord
  set cM := primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M with hcM
  set fσ := primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ with hfσ
  refine star3Concl_of_congr cM⁻¹ D ?_
  set D' := D.map (MulAut.congr cM⁻¹).toMonoidHom with hD'
  have hD'el : IsElemAbelian 3 D' := hD.map _
  have hfσD' : fσ ∈ D' := ⟨b, hbD, by
    simp only [MulEquiv.coe_toMonoidHom]
    rw [mulAut_congr_eq, inv_inv, hM]⟩
  have hΘfσ : Θ fσ = σ := by
    have := primeFormFieldFactor_apply h isPrimeFormGram_one hn3 hq 1 σ
    rwa [map_one, one_mul] at this
  have hfσout : fσ ∉ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← hkerΘ, MonoidHom.mem_ker, hΘfσ]
    exact hσ1
  set D'₀ := D' ⊓ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hD'₀
  have hcard3 : Nat.card D' ≤ 3 * Nat.card D'₀ := by
    have hRcard : Nat.card (RingAut K) = 6 :=
      (card_ringAut_and_isCyclic Nat.prime_two K (h.card.trans (by norm_num))).1
    haveI : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hRcard]; norm_num)
    let fD : ↥D' →* RingAut K := Θ.comp D'.subtype
    have hker : Nat.card fD.ker ≤ Nat.card D'₀ := by
      refine Nat.card_le_card_of_injective (fun x => ⟨((x : ↥D') : MulAut _), ?_⟩) ?_
      · refine Subgroup.mem_inf.2 ⟨(x : ↥D').2, ?_⟩
        rw [← hkerΘ, MonoidHom.mem_ker]
        exact x.2
      · intro x y hxy
        have h1 := congrArg Subtype.val hxy
        simp only at h1
        exact Subtype.ext (Subtype.ext h1)
    have hr3 : Nat.card fD.range ≤ 3 := by
      have hpg : IsPGroup 3 fD.range := by
        rintro ⟨_, ⟨x, rfl⟩⟩
        refine ⟨1, Subtype.ext ?_⟩
        simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
        rw [← map_pow]
        have : x ^ 3 = 1 := Subtype.ext (by simpa using hD'el.2 x x.2)
        rw [this, map_one]
      obtain ⟨m, hm⟩ := hpg.exists_card_eq
      have hdvd : Nat.card fD.range ∣ 6 := hRcard ▸ Subgroup.card_subgroup_dvd_card _
      rw [hm] at hdvd ⊢
      have hm1 : m ≤ 1 := by
        by_contra hm2
        push Not at hm2
        have : 3 ^ 2 ∣ 6 := (pow_dvd_pow 3 hm2).trans hdvd
        norm_num at this
      interval_cases m <;> norm_num
    have h1 := Subgroup.card_mul_index fD.ker
    rw [Subgroup.index_ker] at h1
    calc Nat.card D' = Nat.card fD.ker * Nat.card fD.range := h1.symm
      _ ≤ Nat.card D'₀ * 3 := Nat.mul_le_mul hker hr3
      _ = 3 * Nat.card D'₀ := mul_comm _ _
  have h₀ : UnitaryFieldData 2 (3 / 3) ↥(fixSubfield σ) :=
    CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h Nat.prime_three (by norm_num) hσord
  have hbar : ∀ c : ↥(fixSubfield σ), (h₀.bar c : K) = h.bar c :=
    CFSG.RankThree.Classical.fixSubfield_unitaryFieldData_bar h Nat.prime_three (by norm_num) hσord
  set ι := CFSG.RankThree.Classical.subfieldPSU h h₀ hbar n with hιdef
  have hιinj : Function.Injective ι :=
    CFSG.RankThree.Classical.subfieldPSU_injective h h₀ hbar n hn1
  have hfσY : ∀ y, fσ (ι y) = ι y := fun y =>
    CFSG.RankThree.Classical.range_subfieldPSU_le h n h₀ hbar ⟨y, rfl⟩
  have hpres : ∀ δ ∈ D'₀, ∀ x, ∃ y, ι y = δ (ι x) := by
    rintro δ ⟨hδD', B, rfl⟩ x
    have hcomm : primeFormConjHom h _ B * fσ = fσ * primeFormConjHom h _ B :=
      congrArg Subtype.val (hD'el.1.is_comm.comm ⟨_, hδD'⟩ ⟨fσ, hfσD'⟩)
    have hσB : primeFormConjHom h _ (primeFormFieldU h isPrimeFormGram_one σ B) =
        primeFormConjHom h _ B := by
      rw [← primeFormField_conj_eq, ← hcomm, mul_inv_cancel_right]
    obtain ⟨l, hl⟩ := exists_scalar_of_conjHom_eq_one h hn3
      (A := primeFormFieldU h isPrimeFormGram_one σ B * B⁻¹) (by
        rw [map_mul, map_inv, hσB, mul_inv_cancel])
    have hσB' : glAut σ (B : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) l * B := by
      have e1 : glAut σ (B : GL (Fin n) K) * (B : GL (Fin n) K)⁻¹ =
          GeneralLinearGroup.scalar (Fin n) l := by
        rw [← hl, Subgroup.coe_mul, Subgroup.coe_inv, coe_primeFormFieldU]
      rw [← e1, inv_mul_cancel_right]
    induction x using QuotientGroup.induction_on with
    | H g₀ =>
      set M : GL (Fin n) K := (B : GL (Fin n) K) *
        CFSG.RankThree.Classical.subfieldGL (fixSubfield σ) n (g₀ : GL (Fin n) ↥(fixSubfield σ)) *
          (B : GL (Fin n) K)⁻¹ with hMdef
      have hfix0 : glAut σ (CFSG.RankThree.Classical.subfieldGL (fixSubfield σ) n
          (g₀ : GL (Fin n) ↥(fixSubfield σ))) =
          CFSG.RankThree.Classical.subfieldGL (fixSubfield σ) n
            (g₀ : GL (Fin n) ↥(fixSubfield σ)) := by
        apply Units.ext
        rw [coe_glAut, CFSG.RankThree.Classical.coe_subfieldGL]
        ext i j
        simp only [Matrix.map_apply]
        exact (mem_fixSubfield σ).1
          (((g₀ : GL (Fin n) ↥(fixSubfield σ)) : Matrix (Fin n) (Fin n) ↥(fixSubfield σ)) i j).2
      have hMfix : glAut σ M = M := by
        rw [hMdef, map_mul, map_mul, map_inv, hσB', hfix0, _root_.mul_inv_rev]
        set G₀ := CFSG.RankThree.Classical.subfieldGL (fixSubfield σ) n
          (g₀ : GL (Fin n) ↥(fixSubfield σ))
        have hc : ∀ g : GL (Fin n) K, GeneralLinearGroup.scalar (Fin n) l * g =
            g * GeneralLinearGroup.scalar (Fin n) l := fun g => ((commute_scalar l g).eq).symm
        calc GeneralLinearGroup.scalar (Fin n) l * (B : GL (Fin n) K) * G₀ *
              ((B : GL (Fin n) K)⁻¹ * (GeneralLinearGroup.scalar (Fin n) l)⁻¹) =
            GeneralLinearGroup.scalar (Fin n) l * ((B : GL (Fin n) K) * G₀ * (B : GL (Fin n) K)⁻¹) *
              (GeneralLinearGroup.scalar (Fin n) l)⁻¹ := by group
          _ = (B : GL (Fin n) K) * G₀ * (B : GL (Fin n) K)⁻¹ := by
              rw [hc, mul_inv_cancel_right]
      obtain ⟨g₀', hg₀'⟩ := CFSG.RankThree.Classical.exists_subfieldGL_eq_of_fixed n hMfix
      have hMSU : M ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
        conj_mem_gramSU h _ B.2
          (CFSG.RankThree.Classical.subfieldGL_mem_gramSU h h₀ hbar n g₀.2)
      have hg₀'SU : g₀' ∈ gramSU h₀ ((1 : GL (Fin n) ↥(fixSubfield σ)) :
          Matrix (Fin n) (Fin n) ↥(fixSubfield σ)) :=
        CFSG.RankThree.Classical.mem_gramSU_of_subfieldGL h n h₀ hbar (by rw [hg₀']; exact hMSU)
      refine ⟨((⟨g₀', hg₀'SU⟩ : gramSU h₀ _) : primeFormP h₀ _), ?_⟩
      rw [hιdef, CFSG.RankThree.Classical.subfieldPSU_mk, CFSG.RankThree.Classical.subfieldPSU_mk,
        primeFormConjHom_mk]
      congr 1
      apply Subtype.ext
      rw [CFSG.RankThree.Classical.coe_subfieldSU]
      change CFSG.RankThree.Classical.subfieldGL (fixSubfield σ) n g₀' = M
      exact hg₀'
  obtain ⟨ρ, hρ⟩ := exists_restrict_hom ι hιinj D'₀ hpres
  have hρel : IsElemAbelian 3 ρ.range := by
    have h1 := (hD'el.mono (inf_le_left : D'₀ ≤ D')).subgroupOf D'₀
    rw [Subgroup.subgroupOf_self] at h1
    rw [MonoidHom.range_eq_map]
    exact h1.map ρ
  obtain ⟨E'', hE''le, hE''card, U'', hU''ne, hU''2, hU''inv⟩ :=
    star3Concl_two h₀ rfl (by norm_num) hn ρ.range hρel
  set E₀' : Subgroup ↥D'₀ := E''.comap ρ with hE₀'
  set E₀ := E₀'.map D'₀.subtype with hE₀
  have hE₀D'₀ : E₀ ≤ D'₀ := Subgroup.map_subtype_le _
  have hcardE₀ : Nat.card E₀ = Nat.card E₀' :=
    Subgroup.card_map_of_injective D'₀.subtype_injective
  set U := U''.map ι with hUdef
  set E := Subgroup.zpowers fσ ⊔ E₀ with hEdef
  have hED' : E ≤ D' := sup_le (Subgroup.zpowers_le.2 hfσD') (hE₀D'₀.trans inf_le_left)
  let Nstab : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :=
    { carrier := {φ | ∀ u, u ∈ U ↔ φ u ∈ U}
      mul_mem' := fun {φ ψ} hφ hψ u => (hψ u).trans (hφ (ψ u))
      one_mem' := fun u => Iff.rfl
      inv_mem' := fun {φ} hφ u => by
        have := hφ (φ⁻¹ u)
        rw [MulAut.inv_apply, MulEquiv.apply_symm_apply] at this
        rw [MulAut.inv_apply]
        exact this.symm }
  have hfσN : fσ ∈ Nstab := by
    intro u
    constructor
    · rintro ⟨u'', hu'', rfl⟩
      rw [hfσY]
      exact ⟨u'', hu'', rfl⟩
    · rintro ⟨u'', hu'', hu⟩
      have : u = ι u'' := fσ.injective (by rw [hfσY]; exact hu.symm)
      rw [this]
      exact ⟨u'', hu'', rfl⟩
  have hE₀N : E₀ ≤ Nstab := by
    have hfwd : ∀ k ∈ E₀', ∀ u ∈ U, (k : MulAut _) u ∈ U := by
      rintro k hk _ ⟨u'', hu'', rfl⟩
      rw [← hρ]
      exact ⟨_, hU''inv _ hk u'' hu'', rfl⟩
    rintro _ ⟨k, hk, rfl⟩ u
    have hk' : (D'₀.subtype k : MulAut _) = (k : MulAut _) := rfl
    rw [hk']
    constructor
    · exact hfwd k hk u
    · intro hu
      have := hfwd k⁻¹ (inv_mem hk) _ hu
      rwa [Subgroup.coe_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply] at this
  have hEN : E ≤ Nstab := sup_le (Subgroup.zpowers_le.2 hfσN) hE₀N
  have hE₀E : E₀ ≤ E := le_sup_right
  have hcardE : 3 * Nat.card E₀ ≤ Nat.card E := by
    have hidx3 : 3 ≤ E₀.relIndex E := by
      have hdvd : E₀.relIndex E ∣ Nat.card E := Subgroup.relIndex_dvd_card _ _
      have hEp : IsPGroup 3 E := (hD'el.mono hED').isPGroup
      obtain ⟨m, hm⟩ := hEp.exists_card_eq
      rw [hm] at hdvd
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
      have hne : E₀.relIndex E ≠ 1 := by
        intro h1
        have hle := (Subgroup.relIndex_eq_one).1 h1
        exact hfσout (hE₀D'₀ (hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers fσ)))).2
      rw [hj] at hne ⊢
      have : j ≠ 0 := by
        rintro rfl
        exact hne (pow_zero 3)
      calc 3 = 3 ^ 1 := (pow_one 3).symm
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 this)
    have h := Subgroup.relIndex_mul_card E₀ E
    rw [inf_of_le_left hE₀E] at h
    rw [← h]
    exact Nat.mul_le_mul_right _ hidx3
  refine ⟨E, hED', ?_, U, ?_, hU''2.map ι, fun φ hφ u hu => (hEN hφ u).1 hu⟩
  · rcases hE''card with hE''card | hE''card
    ·
      left
      have hE₀'idx : E₀'.index ≤ 3 := by
        rw [hE₀', Subgroup.index_comap]
        exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313InAux.relIndex_le_of_card_le
          hE''le hE''card
      have hcardD'₀ : Nat.card D'₀ ≤ 3 * Nat.card E₀ := by
        have := Subgroup.card_mul_index E₀'
        rw [hcardE₀, ← this, mul_comm]
        exact Nat.mul_le_mul_right _ hE₀'idx
      omega
    ·
      right
      have hmap : E₀'.map ρ = E'' := Subgroup.map_comap_eq_self hE''le
      have hle : Nat.card (E₀'.map ρ) ≤ Nat.card E₀' :=
        Nat.card_le_card_of_surjective _ (ρ.subgroupMap_surjective E₀')
      rw [hmap] at hle
      have hE₀le : Nat.card E₀ ≤ Nat.card E := Subgroup.card_le_of_le hE₀E
      omega
  · intro hbot
    exact hU''ne ((Subgroup.map_eq_bot_iff_of_injective U'' hιinj).1 hbot)

theorem card_le_nine_of_star3 {S : Type*} [Group S] [Finite S] {D : Subgroup (MulAut S)}
    (hD : IsElemAbelian 3 D) (hst : Star3Concl D) (hno : NoPlaneTwoSub D) : Nat.card D ≤ 9 := by
  haveI : Finite (MulAut S) := MulEquiv.finite_left
  obtain ⟨E, hED, hcard, V, hV1, hV2, hVinv⟩ := hst
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ := hD.isPGroup.exists_card_eq
  have hk3 : 3 ≤ k := by
    by_contra hk3
    push Not at hk3
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h27 : 27 ≤ Nat.card D := by
    rw [hk]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
  have hE9 : 9 ≤ Nat.card E := by
    rcases hcard with hc | hc
    · omega
    · exact hc
  exact hV1 (hno E hED hE9 V hV2 hVinv)

theorem card_le_nine_of_noPlaneTwoSub_unitary {S : Type} [Group S] [Finite S] {r : ℕ}
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hr : 3 ≤ r)
    (hq2 : q.p = 2) (hq13 : q.exponent = 1 ∨ q.exponent = 3)
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group)
    {D : Subgroup (MulAut S)} (hD : IsElemAbelian 3 D) (hno : NoPlaneTwoSub D) : Nat.card D ≤ 9 := by
  obtain ⟨⟨hℓ, hf, -, -⟩, K, _, _, hK, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv eS
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hn : 4 ≤ r + 1 := by omega
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := r + 1) (K := K))
  let e : S ≃* primeFormP h ((1 : GL (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hst : Star3Concl D := by
    refine star3Concl_of_congr e D ?_
    rcases hq13 with he | he
    · exact star3Concl_two h hq2 he hn _ (hD.map _)
    · exact star3Concl_eight h hq2 he hn _ (hD.map _)
  exact card_le_nine_of_star3 hD hst hno

end Star3

end Unitary

section U38All

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

section PGU3

variable {p f : ℕ} {K : Type} [Field K]

theorem card_le_nine_of_le_primeFormD_three (h : UnitaryFieldData p f K) (h3 : 3 ∣ Nat.card Kˣ)
    (D : Subgroup (MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))))
    (hD : IsElemAbelian 3 D)
    (hDle : D ≤ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    Nat.card D ≤ 9 := by
  haveI : Finite K := h.finite
  have hker : ∀ A : ↥(primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)),
      primeFormConjHom h _ A = 1 ↔ (A : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
    intro A
    constructor
    · intro hA
      obtain ⟨z, hz⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313UnitaryProof.exists_scalar_of_conjHom_eq_one
          h le_rfl hA
      rw [hz]
      exact Subgroup.mem_center_iff.2 fun g => (commute_scalar z g).eq
    · intro hA
      ext x
      induction x using QuotientGroup.induction_on with
      | H g =>
        rw [primeFormConjHom_mk, MulAut.one_apply]
        congr 1
        apply Subtype.ext
        change (A : GL (Fin 3) K) * g * (A : GL (Fin 3) K)⁻¹ = g
        rw [(Subgroup.mem_center_iff.1 hA g).symm, mul_inv_cancel_right]
  have := CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_scalar_kernel Nat.prime_three
    (by norm_num) h3 (by norm_num) (primeFormUnitary h _) (primeFormConjHom h _) hker D hDle hD
  simpa using this

end PGU3

section U38

open CFSG.HardMathSupport.Dickson.I271 (autImage actHom mem_autImage actHom_mk coe_normalizerMonoidHom)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns (gammaPrimeIn fixedSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance (IsFieldAutThree IsThreeType)
open CFSG.RankThree.PartTwo.KFacts (centerDescend psuField psuPrimeFormEquiv congr_psuField)

theorem le_gammaPrime_of_u38 {X : Type} [Group X] [Finite X] {B K : Subgroup X}
    (hKq : CFSG.Open.IsQuasisimple ↥K) (hBel : IsElemAbelian 3 B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) {z : X} (hzB : z ∈ B) (hz1 : z ≠ 1)
    (hzK : z ∈ Subgroup.centralizer (K : Set X)) (h27 : 27 ≤ Nat.card (autImage B K))
    {p f : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData p f F) (hp : p = 2) (hf : f = 3)
    (eU : (↥K ⧸ Subgroup.center ↥K) ≃* unitaryPSU hF 3) :
    K ≤ gammaPrimeIn 3 2 B K := by
  subst hp hf
  classical
  haveI : Finite F := hF.finite
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := hF.charP
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A := autImage B K with hAdef
  have hAel : IsElemAbelian 3 A :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.isElemAbelian_autImage hBel
  set pPE := psuPrimeFormEquiv hF with hpPE
  set eP := eU.trans pPE with heP
  set cP := MulAut.congr eP with hcP
  set A' := A.map cP.toMonoidHom with hA'
  have hA'card : Nat.card A' = Nat.card A := Subgroup.card_map_of_injective cP.injective
  have hA'el : IsElemAbelian 3 A' := hAel.map _
  have hq : ¬(3 = 3 ∧ 2 ^ 3 = 2) := by norm_num
  set Θ := primeFormFieldFactor hF isPrimeFormGram_one (le_refl 3) hq with hΘ
  have hkerΘ := ker_primeFormFieldFactor hF isPrimeFormGram_one (le_refl 3) hq
  have h3F : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hF.card]
    norm_num
  have hnotle : ¬ A' ≤ primeFormD hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro hle
    have h9 := card_le_nine_of_le_primeFormD_three hF h3F A' hA'el hle
    omega
  obtain ⟨β', hβ'A', hβ'out⟩ := Set.not_subset.1 hnotle
  obtain ⟨β, hβA, rfl⟩ := hβ'A'
  obtain ⟨b, hbN, hbB, hβb⟩ := mem_autImage.1 hβA
  have hβ3 : β ^ 3 = 1 := hAel.2 β hβA
  have hβ1 : β ≠ 1 := by
    rintro rfl
    apply hβ'out
    simp only [MulEquiv.coe_toMonoidHom, map_one]
    exact one_mem _
  set β' := cP β with hβ'
  have hσ1 : Θ β' ≠ 1 := fun h1 => hβ'out (by rw [← hkerΘ]; exact h1)
  have hβ'3 : β' ^ 3 = 1 := by rw [hβ', ← map_pow, hβ3, map_one]
  have hσ3 : Θ β' ^ 3 = 1 := by rw [← map_pow, hβ'3, map_one]
  have hσord : orderOf (Θ β') = 3 := orderOf_eq_prime hσ3 hσ1
  have hβ'1 : β' ≠ 1 := fun h1 => hσ1 (by rw [h1, map_one])
  have hβ'ord : orderOf β' = 3 := orderOf_eq_prime hβ'3 hβ'1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent hF (le_refl 3) hq
      Nat.prime_three (by norm_num) (by norm_num) β' hβ'ord (Θ β') rfl hσord
  set σ := Θ β' with hσdef
  set cM := primeFormConjHom hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) M with hcM
  set γ : MulAut (unitaryPSU hF 3) := MulAut.congr pPE.symm cM with hγ
  have hβ'eq : β' = cM * primeFormFieldHom hF isPrimeFormGram_one σ * cM⁻¹ := by
    rw [← hM]
    group
  have hcongr_trans : ∀ x : MulAut (↥K ⧸ Subgroup.center ↥K),
      MulAut.congr pPE (MulAut.congr eU x) = cP x := fun x => by
    ext y
    simp [hcP, heP, MulAut.congr_apply]
  have hcongr_γ : MulAut.congr pPE γ = cM := by
    ext y
    simp [hγ, MulAut.congr_apply]
  have hconj : ∀ k : ℕ, MulAut.congr eU (β ^ k) = γ * psuField hF (σ ^ k) * γ⁻¹ := by
    intro k
    apply (MulAut.congr pPE).injective
    have e1 : MulAut.congr pPE (MulAut.congr eU (β ^ k)) = β' ^ k := by
      rw [hcongr_trans, map_pow]
    have e2 : MulAut.congr pPE (γ * psuField hF (σ ^ k) * γ⁻¹) =
        cM * primeFormFieldHom hF isPrimeFormGram_one σ ^ k * cM⁻¹ := by
      rw [map_mul, map_mul, map_inv, hcongr_γ, congr_psuField, map_pow]
    rw [e1, e2, hβ'eq, conj_pow]
  set ρN : ↥(Subgroup.normalizer (K : Set X)) →* MulAut ↥K := K.normalizerMonoidHom with hρN
  have hcd : ∀ n : ↥(Subgroup.normalizer (K : Set X)), centerDescend ↥K (ρN n) = actHom K n := by
    intro n
    ext y
    induction y using QuotientGroup.induction_on with
    | H k => rfl
  have hfield : ∀ k : ℕ, IsFieldAutThree (ρN (⟨b, hbN⟩ ^ k)) := by
    intro k
    refine Or.inr (Or.inr ?_)
    refine CFSG.HardMathSupport.Solomon.Coordinator.isFieldAutPSU3_of_data hF eU (σ ^ k) ?_ γ ?_
    · have : (σ ^ k) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hσ3, one_pow]
      exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one this)
    · rw [hcd, map_pow, hβb, hconj]
  obtain ⟨β₂, hβ₂A, hβ₂⟩ : ∃ β₂ ∈ A, β₂ ∉ Subgroup.zpowers β := by
    by_contra hcon
    push Not at hcon
    have hle : A ≤ Subgroup.zpowers β := fun x hx => hcon x hx
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_eq_prime hβ3 hβ1] at this
    omega
  obtain ⟨d, hdN, hdB, hβ₂d⟩ := mem_autImage.1 hβ₂A
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply hβ1
    rw [← hβb, show (⟨1, hbN⟩ : ↥(Subgroup.normalizer (K : Set X))) = 1 from rfl, map_one]
  have hdb : d ∉ Subgroup.zpowers b := by
    rintro ⟨k, rfl⟩
    apply hβ₂
    rw [← hβ₂d]
    have e1 : (⟨b ^ k, hdN⟩ : ↥(Subgroup.normalizer (K : Set X))) = ⟨b, hbN⟩ ^ k :=
      Subtype.ext (SubgroupClass.coe_zpow (⟨b, hbN⟩ : ↥(Subgroup.normalizer (K : Set X))) k).symm
    rw [e1, map_zpow, hβb]
    exact Subgroup.zpow_mem_zpowers β k
  set B₀ : Subgroup X := Subgroup.closure ({b, d} : Set X) with hB₀
  have hB₀B : B₀ ≤ B := by
    rw [hB₀, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact hbB
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hdB
  have hB₀N : B₀ ≤ Subgroup.normalizer (K : Set X) := hB₀B.trans hBN
  have hB₀card : Nat.card B₀ = 3 ^ 2 :=
    CFSG.LieType.SeitzGeneration.card_closure_pair_of_not_mem Nat.prime_three hBel hbB hdB hb1 hdb
  have hB₀el : IsElemAbelian 3 B₀ := hBel.mono hB₀B
  have hbB₀ : b ∈ B₀ := Subgroup.subset_closure (by simp)
  have hdB₀ : d ∈ B₀ := Subgroup.subset_closure (by simp)
  set φ : ↥B₀ →* MulAut (↥K ⧸ Subgroup.center ↥K) := (actHom K).comp (Subgroup.inclusion hB₀N)
    with hφ
  have hφb : φ ⟨b, hbB₀⟩ = β := hβb
  have hφd : φ ⟨d, hdB₀⟩ = β₂ := hβ₂d
  have hrange : 9 ≤ Nat.card φ.range := by
    have hcl : Subgroup.closure ({β, β₂} : Set (MulAut (↥K ⧸ Subgroup.center ↥K))) ≤ φ.range := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | hx
      · exact ⟨⟨b, hbB₀⟩, hφb⟩
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact ⟨⟨d, hdB₀⟩, hφd⟩
    have hc9 := CFSG.LieType.SeitzGeneration.card_closure_pair_of_not_mem Nat.prime_three hAel hβA
      hβ₂A hβ1 hβ₂
    have := Subgroup.card_le_of_le hcl
    omega
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker] at h1
    have hpos : 0 < Nat.card φ.ker := Nat.card_pos
    have hk1 : Nat.card φ.ker = 1 := by
      by_contra hne
      have h2 : 2 ≤ Nat.card φ.ker := by omega
      have : 2 * 9 ≤ Nat.card φ.ker * Nat.card φ.range := Nat.mul_le_mul h2 hrange
      have h9 : Nat.card ↥B₀ = 9 := by rw [hB₀card]; norm_num
      omega
    exact Subgroup.eq_bot_of_card_eq _ hk1
  have hzN : z ∈ Subgroup.normalizer (K : Set X) := hBN hzB
  have hact_z : ∀ k : ℤ, actHom K ⟨z ^ k, zpow_mem hzN k⟩ = 1 := by
    intro k
    ext y
    induction y using QuotientGroup.induction_on with
    | H w =>
      rw [actHom_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [coe_normalizerMonoidHom]
      have hzk : z ^ k ∈ Subgroup.centralizer (K : Set X) := zpow_mem hzK k
      have hc : (w : X) * z ^ k = z ^ k * (w : X) := Subgroup.mem_centralizer_iff.1 hzk w w.2
      rw [← hc, mul_inv_cancel_right]
  have hnotz : ∀ x : ↥B₀, x ≠ 1 → (x : X) ∉ Subgroup.zpowers z := by
    rintro x hx1 ⟨k, hk⟩
    apply hx1
    apply hφinj
    rw [map_one]
    have e1 : (Subgroup.inclusion hB₀N x : ↥(Subgroup.normalizer (K : Set X))) =
        ⟨z ^ k, zpow_mem hzN k⟩ := Subtype.ext hk.symm
    rw [hφ, MonoidHom.comp_apply, e1, hact_z]
  set ρ : ↥B₀ →* MulAut ↥K := ρN.comp (Subgroup.inclusion hB₀N) with hρ
  have hT : IsThreeType ↥K := Or.inr ⟨F, inferInstance, inferInstance, 2 ^ 3,
    by rw [hF.card]; norm_num, ⟨eU.trans (CFSG.HardMathSupport.Solomon.Coordinator.psuO hF)⟩⟩
  have hBel' : IsElemAbelian 3 (⊤ : Subgroup ↥B₀) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hB₀el.1.is_comm.comm a.1 b.1)⟩⟩, fun x _ => ?_⟩
    exact Subtype.ext (by simpa using hB₀el.2 (x : X) x.2)
  have hbord : orderOf (⟨b, hbB₀⟩ : ↥B₀) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hBel.2 b hbB) hb1
  have hH : ∃ H : Subgroup ↥B₀, Nat.card ↥B₀ = 3 * Nat.card H ∧
      ∀ g ∈ H, IsFieldAutThree (ρ g) := by
    refine ⟨Subgroup.zpowers ⟨b, hbB₀⟩, ?_, ?_⟩
    · rw [Nat.card_zpowers, hbord, hB₀card]
      norm_num
    · intro g hg
      rw [mem_zpowers_iff_mem_range_orderOf] at hg
      obtain ⟨k, -, hkg⟩ := Finset.mem_image.mp hg
      rw [← hkg, hρ, MonoidHom.comp_apply, map_pow]
      exact hfield k
  have hgen := CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.input23_16Three_holds
    ↥K hKq hT ↥B₀ ρ hBel' hH
  have hrkB₀ : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥B₀) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hBel' (by rw [Subgroup.card_top]; exact hB₀card)
  have hfix : ∀ E : Subgroup ↥B₀, CFSG.Open.pRank 3 (⊤ : Subgroup ↥B₀) - 1 ≤ CFSG.Open.pRank 3 E →
      fixedSubgroup ρ E ≤ (gammaPrimeIn 3 2 B K).comap K.subtype := by
    intro E hE k hk
    have hE1 : 1 ≤ CFSG.Open.pRank 3 E := by omega
    obtain ⟨e₀, he₀E, he₀1⟩ : ∃ e₀ ∈ E, e₀ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hEbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hcon
      have h0 : CFSG.Open.pRank 3 E ≤ 0 := CFSG.SectionRank.pRank_le (by norm_num) fun F hF _ => by
        rw [hEbot] at hF
        rw [pow_zero]
        exact (Subgroup.card_le_one_iff_eq_bot F).2 (le_bot_iff.1 hF)
      omega
    have he₀z : (e₀ : X) ∉ Subgroup.zpowers z := hnotz e₀ he₀1
    have he₀B : (e₀ : X) ∈ B := hB₀B e₀.2
    set E' : Subgroup X := Subgroup.closure ({z, (e₀ : X)} : Set X) with hE'
    have hE'B : E' ≤ B := by
      rw [hE', Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | hx
      · exact hzB
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact he₀B
    have hE'card : Nat.card E' = 3 ^ 2 :=
      CFSG.LieType.SeitzGeneration.card_closure_pair_of_not_mem Nat.prime_three hBel hzB he₀B hz1 he₀z
    have hE'rk : 2 ≤ CFSG.Open.pRank 3 E' :=
      CFSG.SectionRank.le_pRank (by norm_num) le_rfl (hBel.mono hE'B) hE'card
    have hkc : (k : X) ∈ Subgroup.centralizer (E' : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hle : E' ≤ Subgroup.centralizer ({(k : X)} : Set X) := by
        rw [hE', Subgroup.closure_le]
        intro x hx
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        rcases hx with rfl | hx
        · exact (Subgroup.mem_centralizer_iff.1 hzK k k.2).symm
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          have h1 := hk e₀ he₀E
          have h2 : ((ρ e₀ k : ↥K) : X) = (e₀ : X) * k * (e₀ : X)⁻¹ :=
            coe_normalizerMonoidHom K (Subgroup.inclusion hB₀N e₀) k
          rw [h1] at h2
          calc (e₀ : X) * k = ((e₀ : X) * k * (e₀ : X)⁻¹) * e₀ := by group
            _ = k * e₀ := by rw [← h2]
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
    show (k : X) ∈ gammaPrimeIn 3 2 B K
    exact le_iSup₂_of_le (f := fun (E : Subgroup X) (_ : E ≤ B ∧ 2 ≤ CFSG.Open.pRank 3 E) =>
      K ⊓ Subgroup.centralizer (E : Set X)) E' ⟨hE'B, hE'rk⟩ le_rfl ⟨k.2, hkc⟩
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥K) ∈ (⊤ : Subgroup ↥K) := Subgroup.mem_top _
  exact iSup₂_le hfix (hgen hmem)

end U38

end U38All

section CardAut

open CFSG.HardMathSupport.Dickson.I271 (autImage)

variable {G : Type} [Group G] [Finite G]

theorem card_autImage_eq {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139b : Prop139b p M D) {U : Subgroup G}
    (hU : IsU1312 p B M D L0 d U) {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) {Kc : Subgroup G}
    (hKc : GLAPComponent 3 (Cg u) Kc) (hN : B ≤ Subgroup.normalizer (Kc : Set G))
    (hcen : CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
      Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
        Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) ≤ 1) :
    Nat.card (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) = 3 ^ (CFSG.Open.pRank 3 B - 1) ∧
      4 ≤ CFSG.Open.pRank 3 B := by
  obtain ⟨hp3, -⟩ := h139b
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hBel : IsElemAbelian 3 B := h.bOne.1.1
  have huB : u ∈ B := hU.1.1 hu
  have hBC : B ≤ Cg u := Prop1310a5b.le_cg_of_mem hBel huB
  have hB4 : 4 ≤ CFSG.Open.pRank 3 B := Claims1310.pRank_B_eq h ▸ h.standing.four_le
  have hKt : IsComponentOf (barX 3 (Cg u) Kc) ⊤ :=
    Lemma1314.isComponentOf_barX_of_glaPComponent hKc
  have hBtel : IsElemAbelian 3 (barX 3 (Cg u) B) := isElemAbelian_barX hBel
  have hBtrk : CFSG.Open.pRank 3 (barX 3 (Cg u) B) = CFSG.Open.pRank 3 B :=
    rank_barX_of_isPGroup hp (CFSG.Open.IsElemAbelian.isPGroup hBel) hBC
  have hBtN : barX 3 (Cg u) B ≤
      Subgroup.normalizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
        Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :=
    barX_le_normalizer hN
  have hc1 := InputsSeitz6.one_le_pRank_cen_bar hBel huB hu1 Kc
  obtain ⟨a, ha⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_pow_autOrderIn hp hBtel hBtN
  have hrk := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.pRank_eq_add_autOrderIn hp hBtel hBtN ha
  refine ⟨?_, hB4⟩
  rw [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.card_autImage hKt.2.2.1, ha]
  congr 1
  omega

end CardAut

section U38Config

open CFSG.HardMathSupport.Dickson.I271 (autImage)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (IsTwoPow)

variable {G : Type} [Group G] [Finite G]

theorem le_M_of_u38 {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139b : Prop139b p M D) {U : Subgroup G}
    (hU : IsU1312 p B M D L0 d U) {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) {Kc : Subgroup G}
    (hKc : GLAPComponent 3 (Cg u) Kc) (hN : B ≤ Subgroup.normalizer (Kc : Set G))
    (hcen : CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
      Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
        Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) ≤ 1)
    (i : TauCeti.ValidLieTypeIndex)
    (e : barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc) ≃* (TauCeti.CFSGIndex.lie i).Group)
    {q : TauCeti.PrimePower} (hq : IsTwoPow q 3) (hi : i.1 = .twistedA 2 q) : Kc ≤ M := by
  obtain ⟨hcard, hB4⟩ := card_autImage_eq h h139b hU hu hu1 hKc hN hcen
  obtain ⟨hp3, -⟩ := h139b
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hBel : IsElemAbelian 3 B := h.bOne.1.1
  have huB : u ∈ B := hU.1.1 hu
  have hnorm : ∀ E' : Subgroup G, E' ≤ B → 2 ≤ CFSG.Open.pRank 3 E' →
      Subgroup.normalizer (E' : Set G) ≤ M :=
    fun E' hE' hr => (normalizer_le_glbCore hE' hr).trans h.uniq.clause_d
  have hcore : GLAPPrimeCoreOf 3 (Cg u) ≤ M := le_sup_left.trans (h.uniq.clause_a u huB hu1)
  have eK : barOf 3 Kc ≃* ↥(barX 3 (Cg u) Kc) := quotEquivBarX hp hKc.1 hKc.2.1
  have hKt : IsComponentOf (barX 3 (Cg u) Kc) ⊤ :=
    Lemma1314.isComponentOf_barX_of_glaPComponent hKc
  have hBtel : IsElemAbelian 3 (barX 3 (Cg u) B) := isElemAbelian_barX hBel
  have hBtN : barX 3 (Cg u) B ≤
      Subgroup.normalizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
        Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :=
    barX_le_normalizer hN
  obtain ⟨⟨z, hz⟩, hz1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1 (InputsSeitz6.cen_bar_ne_bot hBel huB hu1 Kc)
  have hz1' : z ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have h27 : 27 ≤ Nat.card (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) := by
    rw [hcard]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (CFSG.Open.pRank 3 B - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have eZ : ↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc) ≃*
      (TauCeti.CFSGIndex.lie i).Group := (Lemma1315b.centerQuotEquiv eK.symm).trans e
  obtain ⟨i1, hv⟩ := i
  simp only at hi
  subst hi
  obtain ⟨⟨hℓ, hf, -, -⟩, F, _, _, hK, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv eZ
  have hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData q.p q.exponent F :=
    ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hgam := le_gammaPrime_of_u38 hKt.2.2 hBtel hBtN hz.1 hz1' hz.2 h27 hF hq.1 hq.2
    (eT.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hF (by norm_num)).symm)
  exact Prop1310a5b.comp_le_M_of_gamma hBel huB hnorm hcore hKc
    (hgam.trans (gammaPrimeIn_le_glbCore le_rfl _ _))

end U38Config

section Indices

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (IsTwoPow Bal207Index Gen2318Index Bal209TwoIndex
  IsTwistedE6FourIndex IsSixIndex IsF4EightIndex IsD4FourIndex FourIndex ExcIndex IsL2EightIndex)
open CFSG.AGLEmbeddingD2 (IsD2SeitzException)
open CFSG.LieType.SeitzGeneration.QuasiHigh (CoverIndex)

theorem residual_index {i : TauCeti.LieTypeIndex} (hexc : ExcIndex 3 i) (htits : i ≠ .tits)
    (hl28 : ¬ IsL2EightIndex i) (hrest : CoverIndex 3 i ∨ IsD2SeitzException 3 i)
    (hg : ¬ Gen2318Index i) (hB : ∀ (r : ℕ) (q : TauCeti.PrimePower), i ≠ .B r q)
    (hU : ∀ q : TauCeti.PrimePower, i ≠ .twistedA 3 q) :
    CoverIndex 3 i ∧
      ((∃ q, IsTwoPow q 1 ∧ i = .twistedA 5 q) ∨ (∃ q, IsTwoPow q 3 ∧ i = .twistedA 5 q) ∨
        (∃ q, IsTwoPow q 3 ∧ i = .twistedA 2 q) ∨ (∃ q, IsTwoPow q 1 ∧ i = .twistedE6 q) ∨
        (∃ q, IsTwoPow q 3 ∧ i = .twistedE6 q)) := by
  have hcov : CoverIndex 3 i := by
    rcases hrest with hc | hd
    · exact hc
    · exfalso
      simp only [IsD2SeitzException] at hd
      rcases hd with ⟨-, ⟨q, hq2, hq3, rfl⟩ | ⟨q, hq2, hq3, rfl⟩ | ⟨q, -, -, rfl⟩ |
          ⟨q, -, -, rfl | rfl⟩ | rfl⟩ | ⟨h5, -⟩
      · exact hl28 ⟨rfl, hq2, hq3⟩
      · rcases hexc with h207 | ⟨-, h1 | h1 | h1 | h1 | h1⟩
        · exact h207
        · exact absurd h1.1 (by norm_num)
        · exact hg h1
        · exact h1
        · exact h1
        · rcases h1 with h1 | h1 | h1 <;> exact h1
      · exact hU q rfl
      · exact hB 3 q rfl
      · exact hB 4 q rfl
      · exact htits rfl
      · omega
  refine ⟨hcov, ?_⟩
  cases i with
  | A r q =>
    exfalso
    rcases hexc with h207 | ⟨-, h1 | h1 | h1 | h1 | h1⟩
    · exact h207
    · exact hl28 h1
    · exact hg h1
    · exact h1
    · exact h1
    · rcases h1 with h1 | h1 | h1 <;> exact h1
  | twistedA r q =>
    rcases hexc with ⟨-, ⟨-, hr⟩ | ⟨hq, rfl⟩⟩ | ⟨-, h1 | h1 | h1 | h1 | h1⟩
    · exact absurd hcov.1 hr
    · exact Or.inl ⟨q, hq, rfl⟩
    · exact h1.elim
    · exact absurd h1 hg
    · exact h1.elim
    · exact h1.elim
    · rcases h1 with h1 | h1 | ⟨hq, rfl | rfl⟩
      · exact h1.elim
      · exact h1.elim
      · exact Or.inr (Or.inr (Or.inl ⟨q, hq, rfl⟩))
      · exact Or.inr (Or.inl ⟨q, hq, rfl⟩)
  | B r q => exact absurd rfl (hB r q)
  | twistedE6 q =>
    rcases hexc with h207 | ⟨-, h1 | h1 | h1 | h1 | h1⟩
    · exact h207.elim
    · exact h1.elim
    · exact absurd h1 hg
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, h1, rfl⟩)))
    · exfalso
      obtain ⟨-, h3⟩ := hcov
      obtain ⟨hq2, hq4⟩ := h1
      rw [TauCeti.PrimePower.card_def, hq2, hq4] at h3
      omega
    · rcases h1 with h1 | h1 | h1
      · exact h1.elim
      · exact h1.elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨q, h1, rfl⟩)))
  | tits => exact absurd rfl htits
  | _ =>
    exfalso
    first
      | exact hcov
      | (rcases hexc with h207 | ⟨-, h1 | h1 | h1 | h1 | h1⟩
         · first | exact h207 | exact absurd h207.1 (by norm_num)
         · exact h1
         · exact hg h1
         · exact h1
         · exact h1
         · rcases h1 with h1 | h1 | h1 <;> exact h1)

end Indices

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (ExcIndex IsSixIndex IsL2EightIndex Gen2318Index)
open CFSG.HardMathSupport.Dickson.I271 (autImage)
open CFSG.AGLEmbeddingD2 (KFactSeitzRankTwo IsD2SeitzException)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

@[expose] def Rank3CuResExcFour : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G},
    Cex1310 G m p B M E A D T R L0 d → Prop139b p M D → ∀ {U : Subgroup G}, IsU1312 p B M D L0 d U →
      ∀ u ∈ U, u ≠ 1 →
        CFSG.Open.pRank 3 B < CFSG.Open.pRank 3 (⊤ : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) →
        ∀ Kc : Subgroup G, GLAPComponent 3 (Cg u) Kc → Prop1310a5b.Good2319 (barOf 3 Kc) →
          B ≤ Subgroup.normalizer (Kc : Set G) →
          CFSG.Open.pRank 3 B < 2 + CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 Kc))) →
          CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
            Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
              Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) ≤ 1 →
          ¬ IsPiGroup 3 (barOf 3 Kc) →
          IsStronglyLocallyOneBalanced 3 B u Kc →
          (∃ i : TauCeti.ValidLieTypeIndex,
              Nonempty (barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc) ≃* (TauCeti.CFSGIndex.lie i).Group) ∧
              i.1.characteristic ≠ 3 ∧
              ExcIndex 3 i.1 ∧ i.1 ≠ .tits ∧ ¬ IsL2EightIndex i.1 ∧
              (IsSixIndex i.1 → ¬ InputsSeitz3.autIm (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) ≤
                (MulAut.conj : ↥(barX 3 (Cg u) Kc) →* MulAut ↥(barX 3 (Cg u) Kc)).range) ∧
              ((Subgroup.center (barOf 3 Kc) ≠ ⊥ ∧
                  CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex 3 i.1) ∨
                IsD2SeitzException 3 i.1) ∧
              ¬ Gen2318Index i.1 ∧
              (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.EvenScope i.1 →
                NoPlaneTwoSub (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc))) ∧
              ∀ (r : ℕ) (q : TauCeti.PrimePower), i.1 ≠ .B r q) →
          Kc ≤ M

theorem rank3CuResExcThree_of_four (hGA : GriessMultipliersAllModels) (hX : Rank3CuResExcFour) :
    Rank3CuResExcThree := by
  intro G _ _ m p B M E A D T R L0 d h h139b U hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal htype
  obtain ⟨i, ⟨e⟩, hi3, hexc, htits, hl28, hsix, hrest, hg, hpl⟩ := htype
  by_cases hBt : ∃ (r : ℕ) (q : TauCeti.PrimePower), i.1 = .B r q
  · obtain ⟨r, q, hiB⟩ := hBt
    rcases hrest with ⟨-, hc⟩ | hD
    · rw [hiB] at hc
      exact hc.elim
    · rw [hiB] at hD
      simp only [IsD2SeitzException] at hD
      rcases hD with ⟨-, ⟨q', -, -, h1⟩ | ⟨q', -, -, h1⟩ | ⟨q', -, -, h1⟩ |
          ⟨q', hq'2, hq'1, h1 | h1⟩ | h1⟩ | ⟨-, h1 | h1⟩
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · obtain ⟨rfl, rfl⟩ := TauCeti.LieTypeIndex.B.inj h1
        exact le_M_of_sp hGA h h139b hU hu hu1 hKc hN hcen i e q hq'2 hq'1 le_rfl hiB
      · obtain ⟨rfl, rfl⟩ := TauCeti.LieTypeIndex.B.inj h1
        exact le_M_of_sp hGA h h139b hU hu hu1 hKc hN hcen i e q hq'2 hq'1 (by norm_num) hiB
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
  · push Not at hBt
    exact hX h h139b hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal
      ⟨i, ⟨e⟩, hi3, hexc, htits, hl28, hsix, hrest, hg, hpl, hBt⟩

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (IsTwoPow)

@[expose] def Rank3CuResExcFive : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G},
    Cex1310 G m p B M E A D T R L0 d → Prop139b p M D → ∀ {U : Subgroup G}, IsU1312 p B M D L0 d U →
      ∀ u ∈ U, u ≠ 1 →
        CFSG.Open.pRank 3 B < CFSG.Open.pRank 3 (⊤ : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) →
        ∀ Kc : Subgroup G, GLAPComponent 3 (Cg u) Kc → Prop1310a5b.Good2319 (barOf 3 Kc) →
          B ≤ Subgroup.normalizer (Kc : Set G) →
          CFSG.Open.pRank 3 B < 2 + CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 Kc))) →
          CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
            Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
              Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) ≤ 1 →
          ¬ IsPiGroup 3 (barOf 3 Kc) →
          IsStronglyLocallyOneBalanced 3 B u Kc →
          Subgroup.center (barOf 3 Kc) ≠ ⊥ →
          (∃ i : TauCeti.ValidLieTypeIndex,
            Nonempty (barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc) ≃* (TauCeti.CFSGIndex.lie i).Group) ∧
            ((∃ q, IsTwoPow q 1 ∧ i.1 = .twistedE6 q ∧
                NoPlaneTwoSub (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc))) ∨
              (∃ q, IsTwoPow q 3 ∧ i.1 = .twistedE6 q ∧
                NoPlaneTwoSub (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) ∧
                ¬ InputsSeitz3.autIm (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) ≤
                  (MulAut.conj : ↥(barX 3 (Cg u) Kc) →* MulAut ↥(barX 3 (Cg u) Kc)).range))) →
          Kc ≤ M

section FourOfFive

theorem rank3CuResExcFour_of_five (hX : Rank3CuResExcFive) : Rank3CuResExcFour := by
  intro G _ _ m p B M E A D T R L0 d h h139b U hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal htype
  obtain ⟨i, ⟨e⟩, hi3, hexc, htits, hl28, hsix, hrest, hg, hpl, hBt⟩ := htype
  have hp3 : p = 3 := h139b.1
  obtain ⟨hcard, hB4⟩ := card_autImage_eq h h139b hU hu hu1 hKc hN hcen
  have hBel : IsElemAbelian 3 B := hp3 ▸ h.bOne.1.1
  have hBtel : IsElemAbelian 3 (barX 3 (Cg u) B) := isElemAbelian_barX hBel
  have hAel : IsElemAbelian 3 (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.isElemAbelian_autImage hBtel
  have h27 : 27 ≤ Nat.card (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) := by
    rw [hcard]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (CFSG.Open.pRank 3 B - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have eK : barOf 3 Kc ≃* ↥(barX 3 (Cg u) Kc) := quotEquivBarX Nat.prime_three hKc.1 hKc.2.1
  have eZ : ↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc) ≃*
      (TauCeti.CFSGIndex.lie i).Group := (Lemma1315b.centerQuotEquiv eK.symm).trans e
  have hUr : ∀ (r : ℕ) (q : TauCeti.PrimePower), 3 ≤ r → i.1 = .twistedA r q → q.p = 2 →
      (q.exponent = 1 ∨ q.exponent = 3) → False := by
    intro r q hr hiq hq2 hq13
    have hno := hpl (by rw [hiq]; exact ⟨hq2, hr⟩)
    obtain ⟨i1, hv⟩ := i
    simp only at hiq
    subst hiq
    have hle := card_le_nine_of_noPlaneTwoSub_unitary hv hr hq2 hq13 eZ hAel hno
    omega
  by_cases hU4 : ∃ q, i.1 = .twistedA 3 q
  · exfalso
    obtain ⟨q, hiq⟩ := hU4
    have hq : q.p = 2 ∧ q.exponent = 1 := by
      rcases hrest with ⟨-, hc⟩ | hD
      · rw [hiq] at hc
        exact absurd hc.1 (by norm_num)
      · rw [hiq] at hD
        simp only [IsD2SeitzException] at hD
        rcases hD with ⟨-, ⟨q', -, -, h1⟩ | ⟨q', -, -, h1⟩ | ⟨q', hq'2, hq'1, h1⟩ |
            ⟨q', -, -, h1 | h1⟩ | h1⟩ | ⟨-, h1 | h1⟩
        · exact absurd h1 (by simp)
        · exact absurd h1 (by simp)
        · obtain ⟨-, rfl⟩ := TauCeti.LieTypeIndex.twistedA.inj h1
          exact ⟨hq'2, hq'1⟩
        · exact absurd h1 (by simp)
        · exact absurd h1 (by simp)
        · exact absurd h1 (by simp)
        · exact absurd h1 (by simp)
        · exact absurd h1 (by simp)
    exact hUr 3 q le_rfl hiq hq.1 (Or.inl hq.2)
  have hU4' : ∀ q, i.1 ≠ .twistedA 3 q := fun q h => hU4 ⟨q, h⟩
  have hres := residual_index hexc htits hl28 (hrest.imp And.right id) hg hBt hU4'
  obtain ⟨-, hlist⟩ := hres
  have hZ : Subgroup.center (barOf 3 Kc) ≠ ⊥ := by
    rcases hrest with ⟨hZ, -⟩ | hD
    · exact hZ
    · exfalso
      rcases hlist with ⟨q, -, hiq⟩ | ⟨q, -, hiq⟩ | ⟨q, -, hiq⟩ | ⟨q, -, hiq⟩ | ⟨q, -, hiq⟩ <;>
        rw [hiq] at hD <;> simp [IsD2SeitzException] at hD
  rcases hlist with ⟨q, hq, hiq⟩ | ⟨q, hq, hiq⟩ | ⟨q, hq, hiq⟩ | ⟨q, hq, hiq⟩ | ⟨q, hq, hiq⟩
  · exact (hUr 5 q (by norm_num) hiq hq.1 (Or.inl hq.2)).elim
  · exact (hUr 5 q (by norm_num) hiq hq.1 (Or.inr hq.2)).elim
  · exact le_M_of_u38 h h139b hU hu hu1 hKc hN hcen i e hq hiq
  · exact hX h h139b hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal hZ
      ⟨i, ⟨e⟩, Or.inl ⟨q, hq, hiq, hpl (by rw [hiq]; exact hq.1)⟩⟩
  · exact hX h h139b hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal hZ
      ⟨i, ⟨e⟩, Or.inr ⟨q, hq, hiq, hpl (by rw [hiq]; exact hq.1),
        hsix (by rw [hiq]; exact Or.inr (Or.inr hq))⟩⟩

end FourOfFive

section Consumers

theorem rank3CuResExcTwo_of_five (hGA : GriessMultipliersAllModels) (hX : Rank3CuResExcFive) :
    InputsSeitz6.Rank3CuResExcTwo :=
  rank3CuResExcTwo_of_three hGA (rank3CuResExcThree_of_four hGA (rank3CuResExcFour_of_five hX))

theorem rank3CuRes_of_five (h2 : KFactSeitzRankTwo)
    (hQ : InputsSeitz6.SeitzQuasiAt 3) (hGA : GriessMultipliersAllModels) (hX : Rank3CuResExcFive) :
    Claims1310.Rank3CuRes :=
  InputsSeitz6.rank3CuRes_of_two h2 hQ hGA (rank3CuResExcTwo_of_five hGA hX)

end Consumers

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310r

end
