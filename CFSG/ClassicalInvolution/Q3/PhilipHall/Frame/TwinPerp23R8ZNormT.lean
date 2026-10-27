module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZOdd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoKF
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU22

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.Lemma54Local

open CFSG CFSG.Open CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.LocalBalance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.Lemma52Proof CFSG.ClassicalInvolution.Asc77.Lemma54Proof
open CFSG.Assembly.Dichotomy (involutionOddCore)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {B A D : Subgroup G}

theorem weak_of_hyp51At (hBel : IsElemAbelian 2 B) (hB8 : Nat.card B = 8) {d c : G}
    (hdB : d ∈ B) (hd1 : d ≠ 1) (hcB : c ∈ B) (hc1 : c ≠ 1) (hH : Hyp51At B c) :
    ⁅involutionOddCore d ⊓ Subgroup.centralizer ({c} : Set G), B⁆ ≤ involutionOddCore c := by
  have hBle := le_centralizer_of_mem hBel hcB
  by_cases hdc : d = c
  · subst hdc
    rw [Subgroup.commutator_le]
    intro r hr b hb
    have e : ⁅r, b⁆ = r * (b * r⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact (involutionOddCore d).mul_mem hr.1 (conj_mem_involutionOddCore
      (le_centralizer_of_mem hBel hdB hb) ((involutionOddCore d).inv_mem hr.1))
  · have H := hyp51In_of_hyp51At hH
    have hdC : d ∈ Subgroup.centralizer ({c} : Set G) := hBle hdB
    have hmain := commutator_involutionOddCore_eq_bot_of_hyp51In (pPrimeCore_oddQuot_eq_bot c)
      (modOdd_comm hBel) (modOdd_sq hBel) (card_modOdd_eq_eight hBel hB8 hcB)
      (oddQuotSelf_mem hcB) (oddQuotSelf_ne_one hBel hcB hc1) (oddQuotSelf_central c)
      (mem_modOdd_zpowers_iff hBel hcB hc1) H (oddQuotMk_mem_modOdd hdB hdC)
      (oddQuotMk_not_mem_zpowers hBel hcB hc1 hdB hd1 hdc hdC)
    rw [Subgroup.commutator_le]
    intro r hr b hb
    obtain ⟨hrd, hrC⟩ := Subgroup.mem_inf.mp hr
    have hbC := hBle hb
    have h1 : oddQuotMk c ⟨r, hrC⟩ ∈ involutionOddCore (oddQuotMk c ⟨d, hdC⟩) :=
      oddQuotMk_mem_involutionOddCore hdC hrC (mul_self_eq_one_of_mem hBel hdB) hrd
    have h3 := Subgroup.commutator_mem_commutator h1 (oddQuotMk_mem_modOdd hb hbC)
    rw [hmain, Subgroup.mem_bot] at h3
    have hcom := commutatorElement_mem_centralizer hrC hbC
    refine mem_involutionOddCore_of_oddQuotMk_eq_one hcom ?_
    have e : (⟨⁅r, b⁆, hcom⟩ : ↥(Subgroup.centralizer ({c} : Set G))) =
        ⁅(⟨r, hrC⟩ : ↥(Subgroup.centralizer ({c} : Set G))), ⟨b, hbC⟩⁆ := rfl
    rw [e, map_commutatorElement]
    exact h3

theorem two_of_hyp51At (hBel : IsElemAbelian 2 B) (hB8 : Nat.card B = 8) {F : Subgroup G}
    (hFB : F ≤ B) (hF4 : Nat.card F = 4) {a : G} (ha : a ∈ B) (ha1 : a ≠ 1)
    (hH : Hyp51At B a) :
    deltaCore F ⊓ Subgroup.centralizer ({a} : Set G) ≤ involutionOddCore a := by
  have hBle := le_centralizer_of_mem hBel ha
  have hFsq : ∀ f ∈ F, f * f = 1 := fun f hf => mul_self_eq_one_of_mem hBel (hFB hf)
  have hFt : Nat.card (modOdd a F) = 4 :=
    (card_modOdd_of_exponent_two (hFB.trans hBle) hFsq).trans hF4
  have hFtB : modOdd a F ≤ modOdd a B := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨k, hFB hk, rfl⟩
  have hdelta := deltaCore_eq_bot_of_hyp51In (pPrimeCore_oddQuot_eq_bot a) (modOdd_comm hBel)
    (modOdd_sq hBel) (card_modOdd_eq_eight hBel hB8 ha) (oddQuotSelf_mem ha)
    (oddQuotSelf_ne_one hBel ha ha1) (oddQuotSelf_central a)
    (mem_modOdd_zpowers_iff hBel ha ha1) (hyp51In_of_hyp51At hH) hFtB hFt
  intro y hy
  obtain ⟨hyD, hyC⟩ := Subgroup.mem_inf.mp hy
  refine mem_involutionOddCore_of_oddQuotMk_eq_one hyC ?_
  have hmem : oddQuotMk a ⟨y, hyC⟩ ∈ deltaCore (modOdd a F) := by
    rw [mem_deltaCore_iff]
    intro ft hft hft1
    obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hft
    have hk1 : (k : G) ≠ 1 := fun h => hft1 (by
      have : k = 1 := Subtype.ext h
      rw [this, map_one])
    exact oddQuotMk_mem_involutionOddCore k.2 hyC (hFsq _ hk)
      (mem_deltaCore_iff.mp hyD _ hk hk1)
  rw [hdelta, Subgroup.mem_bot] at hmem
  exact hmem

theorem commutator_le_alphaOf_of_hyp51At (hB : IsElemAbelian 2 B) (hB8 : Nat.card B = 8)
    (hAB : A ≤ B) (hDB : D ≤ B) (hD4 : Nat.card D = 4) (hH : ∀ d ∈ D, d ≠ 1 → Hyp51At B d)
    {α : G} (hα : α ∈ B) (hα1 : α ≠ 1) : ⁅involutionOddCore α, A⁆ ≤ alphaOf D := by
  have hweak : ∀ d ∈ D, d ≠ 1 →
      ⁅involutionOddCore α ⊓ Subgroup.centralizer ({d} : Set G), B⁆ ≤ involutionOddCore d :=
    fun d hd hd1 => weak_of_hyp51At hB hB8 hα hα1 (hDB hd) hd1 (hH d hd hd1)
  have hcomm := comm_of_isElemAbelian hB
  have hAel : IsElemAbelian 2 A :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hB hAB
  have hDel : IsElemAbelian 2 D :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hB hDB
  have hAp : IsPGroup 2 A := isPGroup_two hAel
  have hDp : IsPGroup 2 D := isPGroup_two hDel
  have hBO := le_normalizer_involutionOddCore hB hα
  have hOodd : Odd (Nat.card (involutionOddCore α)) :=
    odd_card_oddCoreIn (Subgroup.centralizer ({α} : Set G))
  have hAO : A ≤ Subgroup.normalizer (involutionOddCore α : Set G) := fun x hx => hBO (hAB hx)
  have hJB := le_normalizer_commutator hB hAB hα
  set J : Subgroup G := ⁅involutionOddCore α, A⁆ with hJ
  have hJle : J ≤ involutionOddCore α := commutator_le_self hAO
  have hJodd : Odd (Nat.card J) := hOodd.of_dvd_nat (Subgroup.card_dvd_of_le hJle)
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) := fun x hx => hJB (hAB hx)
  have hDJ : D ≤ Subgroup.normalizer (J : Set G) := fun x hx => hJB (hDB hx)
  have hJA : ⁅J, A⁆ = J := commutator_commutator_eq hAp hAO hOodd
  have hAJD : A ≤ Subgroup.normalizer ((⁅J, D⁆ : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_commutator (hAJ hx) (le_normalizer_of_le hcomm hDB (hAB hx))
  have hF7 : ⁅J ⊓ Subgroup.centralizer (D : Set G), A⁆ ≤ deltaCore D := by
    refine le_deltaCore fun d hd hd1 => ?_
    calc ⁅J ⊓ Subgroup.centralizer (D : Set G), A⁆
        ≤ ⁅involutionOddCore α ⊓ Subgroup.centralizer ({d} : Set G), B⁆ :=
          Subgroup.commutator_mono (le_inf (inf_le_left.trans hJle)
            (inf_le_right.trans (centralizer_le_singleton hd))) hAB
      _ ≤ involutionOddCore d := hweak d hd hd1
  have hF8 : ⁅J, D⁆ ≤ alphaOf D := by
    rw [commutator_eq_iSup_centralizer hDel hD4 hDJ hJodd]
    refine iSup₂_le fun d hd => iSup_le fun hd1 => ?_
    have hdC : ∀ x ∈ B, x ∈ Subgroup.centralizer ({d} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx d (hDB hd))
    have hZB : B ≤ Subgroup.normalizer
        ((involutionOddCore α ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G) :=
      fun x hx => mem_normalizer_inf (hBO hx) (Subgroup.le_normalizer (hdC x hx))
    have hDZ := fun x (hx : x ∈ D) => hZB (hDB hx)
    have hZodd : Odd (Nat.card
        (involutionOddCore α ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G)) :=
      hOodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have h1 : ⁅involutionOddCore α ⊓ Subgroup.centralizer ({d} : Set G), D⁆ ≤
        involutionOddCore d :=
      (Subgroup.commutator_mono le_rfl hDB).trans (hweak d hd hd1)
    calc ⁅J ⊓ Subgroup.centralizer ({d} : Set G), D⁆
        ≤ ⁅involutionOddCore α ⊓ Subgroup.centralizer ({d} : Set G), D⁆ :=
          Subgroup.commutator_mono (le_inf (inf_le_left.trans hJle) inf_le_right) le_rfl
      _ = ⁅⁅involutionOddCore α ⊓ Subgroup.centralizer ({d} : Set G), D⁆, D⁆ :=
          (commutator_commutator_eq hDp hDZ hZodd).symm
      _ ≤ ⁅involutionOddCore d, D⁆ := Subgroup.commutator_mono h1 le_rfl
      _ ≤ alphaOf D := commutator_le_alphaOf D hd hd1
  have hJQ : J ≤ ⁅J, D⁆ ⊔ ⁅J ⊓ Subgroup.centralizer (D : Set G), A⁆ := by
    calc J = ⁅J, A⁆ := hJA.symm
      _ ≤ ⁅J, D⁆ ⊔ ⁅J ⊓ Subgroup.centralizer (D : Set G), A⁆ := by
        rw [Subgroup.commutator_le]
        intro j hj a ha
        obtain ⟨p, hp, q, hq, rfl⟩ := Lemma54Proof.exists_mul_of_mem hDp hDJ hJodd hj
        have e : ⁅p * q, a⁆ = p * ⁅q, a⁆ * (a * p⁻¹ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hp)
          (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hq ha)))
          (Subgroup.mem_sup_left ?_)
        exact (Subgroup.mem_normalizer_iff.mp (hAJD ha) p⁻¹).mp ((⁅J, D⁆).inv_mem hp)
  exact hJQ.trans (sup_le hF8 (hF7.trans (iInf_le_alphaOf D)))

theorem deltaCore_le_alphaOf_of_hyp51At (hB : IsElemAbelian 2 B) (hB8 : Nat.card B = 8)
    (hAB : A ≤ B) (hDB : D ≤ B) (hA4 : Nat.card A = 4) (hD4 : Nat.card D = 4)
    (hH : ∀ d ∈ D, d ≠ 1 → Hyp51At B d) : deltaCore A ≤ alphaOf D := by
  have hDel : IsElemAbelian 2 D :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hB hDB
  have hDp : IsPGroup 2 D := isPGroup_two hDel
  obtain ⟨z, hz, hz1⟩ := exists_ne_one_mem_inf hB8 hA4 hD4 hAB hDB
  have hDK : D ≤ Subgroup.normalizer ((deltaCore A : Subgroup G) : Set G) := fun x hx =>
    normalizer_deltaCore hB.1 hAB (hDB hx)
  have hKodd : Odd (Nat.card (deltaCore A)) := odd_card_deltaCore hz.1 hz1
  refine (commutator_sup_centralizer hDp hDK hKodd).symm.le.trans (sup_le ?_ ?_)
  · exact (Subgroup.commutator_mono (deltaCore_le_involutionOddCore hz.1 hz1) le_rfl).trans
      (commutator_le_alphaOf D hz.2 hz1)
  · refine (le_deltaCore fun d hd hd1 => ?_).trans (iInf_le_alphaOf D)
    calc deltaCore A ⊓ Subgroup.centralizer (D : Set G)
        ≤ deltaCore A ⊓ Subgroup.centralizer ({d} : Set G) :=
          inf_le_inf_left _ (centralizer_le_singleton hd)
      _ ≤ involutionOddCore d := two_of_hyp51At hB hB8 hAB hA4 (hDB hd) hd1 (hH d hd hd1)

theorem alphaOf_le_alphaOf_of_hyp51At (hB : IsElemAbelian 2 B) (hB8 : Nat.card B = 8)
    (hAB : A ≤ B) (hDB : D ≤ B) (hA4 : Nat.card A = 4) (hD4 : Nat.card D = 4)
    (hH : ∀ d ∈ D, d ≠ 1 → Hyp51At B d) : alphaOf A ≤ alphaOf D := by
  rw [alphaOf_eq A]
  exact sup_le (iSup₂_le fun a ha => iSup_le fun ha1 =>
    commutator_le_alphaOf_of_hyp51At hB hB8 hAB hDB hD4 hH (hAB ha) ha1)
    (deltaCore_le_alphaOf_of_hyp51At hB hB8 hAB hDB hA4 hD4 hH)

theorem alphaOf_eq_alphaOf_of_hyp51At (hB : IsElemAbelian 2 B) (hB8 : Nat.card B = 8)
    (hAB : A ≤ B) (hDB : D ≤ B) (hA4 : Nat.card A = 4) (hD4 : Nat.card D = 4)
    (hHA : ∀ a ∈ A, a ≠ 1 → Hyp51At B a) (hHD : ∀ d ∈ D, d ≠ 1 → Hyp51At B d) :
    alphaOf A = alphaOf D :=
  le_antisymm (alphaOf_le_alphaOf_of_hyp51At hB hB8 hAB hDB hA4 hD4 hHD)
    (alphaOf_le_alphaOf_of_hyp51At hB hB8 hDB hAB hD4 hA4 hHA)

end CFSG.ClassicalInvolution.Asc77.Lemma54Local

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Balance

section Witness

variable {G : Type} [Group G] [Finite G]

theorem hyp51At_of_quiet_witness {B : Subgroup G} (hB : IsElemAbelian 2 B) {c d : G}
    (hcB : c ∈ B) (hdB : d ∈ B) (hc1 : c ≠ 1) (hd1 : d ≠ 1) (hdc : d ≠ c)
    (hdC : d ∈ Subgroup.centralizer ({c} : Set G))
    (hq : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L →
      ∀ y ∈ L, oddQuotMk c ⟨d, hdC⟩ * y = y * oddQuotMk c ⟨d, hdC⟩) : Hyp51At B c := by
  have hno : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → MovedByAll B c L → False := by
    intro L hL hm
    obtain ⟨w, hw, hne⟩ := hm _ (oddQuotMk_mem_modOdd hdB hdC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hdB hd1 hdc hdC)
    exact hne (hq L hL w hw)
  exact ⟨fun L₁ _ h₁ _ m₁ _ => (hno L₁ h₁ m₁).elim, fun L hL hm => (hno L hL hm).elim⟩

theorem hyp51At_conj_of_quiet_witness {B : Subgroup G} (hB : IsElemAbelian 2 B) {g c d : G}
    (hcB : g * c * g⁻¹ ∈ B) (hdB : g * d * g⁻¹ ∈ B) (hc1 : c ≠ 1) (hd1 : d ≠ 1) (hdc : d ≠ c)
    (hdC : d ∈ Subgroup.centralizer ({c} : Set G))
    (hq : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L →
      ∀ y ∈ L, oddQuotMk c ⟨d, hdC⟩ * y = y * oddQuotMk c ⟨d, hdC⟩) :
    Hyp51At B (g * c * g⁻¹) := by
  have hB' : IsElemAbelian 2 (Generic.conjSub g⁻¹ B) := ExactLayer.isElemAbelian_conjSub hB g⁻¹
  have hmem : ∀ x : G, g * x * g⁻¹ ∈ B → x ∈ Generic.conjSub g⁻¹ B := fun x hx =>
    Generic.mem_conjSub_iff.mpr (by rwa [inv_inv])
  have h := hyp51At_of_quiet_witness hB' (hmem c hcB) (hmem d hdB) hc1 hd1 hdc hdC hq
  have h2 := (ExactLayer.hyp51At_conj g c (Generic.conjSub g⁻¹ B)).mpr h
  rwa [Generic.conjSub_conjSub_inv] at h2

end Witness

section Cert


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23E8Z_e_quiet_at_t (hT : Thm4RTwinBelow 3 n) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hZ : u * e ∈ zStarOf (rLayer (Om R) u)) (heC : e ∈ Subgroup.centralizer ({t} : Set Y)) :
    ∀ L : Subgroup (OddQuot t), CFSG.IsComponent L →
      ∀ y ∈ L, oddQuotMk t ⟨e, heC⟩ * y = y * oddQuotMk t ⟨e, heC⟩ := fun L hL =>
  TL4.commute_of_mem_normal_isPGroup hL CFSG.pCore_normal CFSG.pCore_isPGroup
    (p23E8Z_e_mem_pCore_bar hT hcit hP hc hZ heC)

theorem p23E8Z_t_quiet_at_e (hc : P23Cfg n Y R S t K' W u e g)
    (hAE : SecAE R e 6) (htC : t ∈ Subgroup.centralizer ({e} : Set Y)) :
    ∀ L : Subgroup (OddQuot e), CFSG.IsComponent L →
      ∀ y ∈ L, oddQuotMk e ⟨t, htC⟩ * y = y * oddQuotMk e ⟨t, htC⟩ := by
  classical
  obtain ⟨D⟩ := ZTwo.exists_cover hc hAE
  obtain ⟨β, hβ, -, -, -, hz, -, -, -⟩ := ZTwo.twin_labels hc D
  have hΩ := ZTwo.hΩ_of hc
  have hc2 := ZTwo.hc2e_of hc
  have hzt : IsUniqueInvolution (tightCore R) t :=
    Inner.isUniqueInvolution_core (CoreData.of_S hc.std.perp.core).datum
  obtain ⟨htC', htY, -⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 (ZTwo.twins_tq hc).1 hzt
  have htb : ZTwo.tbar hc = QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) e))
      (⟨⟨t, htC'⟩, htY⟩ : ↥(coreHull (Om R) e)) := ZTwo.piE_mk hc ⟨⟨t, htC'⟩, htY⟩ _
  have hVn : ((AE.permHom 6).ker.map (AE.mkQ 6)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hPn : (((AE.permHom 6).ker.map (AE.mkQ 6)).comap D.φ).Normal := hVn.comap _
  have hP2 : IsPGroup 2 (((AE.permHom 6).ker.map (AE.mkQ 6)).comap D.φ) := by
    intro q
    obtain ⟨a, ha, hφ⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp q.2)
    have hperm : a.perm = 1 := MonoidHom.mem_ker.mp ha
    have haa : a * a = 1 := by
      refine AE.Wr.ext (funext fun i => ?_) ?_
      · show a.vec i + a.vec (a.perm.symm i) = (0 : Fin 6 → ZMod 2) i
        rw [hperm]
        exact AE.Wr.zmod_two_add_self _
      · show a.perm * a.perm = (1 : Equiv.Perm (Fin 6))
        rw [hperm, one_mul]
    have hk : (q : SecQ R e) * q ∈ D.φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, ← hφ, ← map_mul, haa, map_one]
    have hx2 : ((q : SecQ R e) * q) * ((q : SecQ R e) * q) = 1 := by
      have hpow : (⟨_, hk⟩ : D.φ.ker) ^ Nat.card D.φ.ker = 1 := pow_card_eq_one'
      have hcard : Nat.card D.φ.ker = 1 ∨ Nat.card D.φ.ker = 2 := by
        have h1 := D.ker_card
        have h2 : 0 < Nat.card D.φ.ker := Nat.card_pos
        omega
      rcases hcard with h1 | h1
      · rw [h1, pow_one] at hpow
        have h3 : (q : SecQ R e) * q = 1 := congrArg Subtype.val hpow
        rw [h3, one_mul]
      · rw [h1, pow_two] at hpow
        exact congrArg Subtype.val hpow
    refine ⟨2, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, show (2 : ℕ) ^ 2 = 2 + 2 from rfl, pow_add, pow_two]
    exact hx2
  have htP : ZTwo.tbar hc ∈ ((AE.permHom 6).ker.map (AE.mkQ 6)).comap D.φ := by
    show D.φ (ZTwo.tbar hc) ∈ (AE.permHom 6).ker.map (AE.mkQ 6)
    rw [hz]
    exact ⟨AE.zOf (AE.emb β hβ), MonoidHom.mem_ker.mpr (AE.zOf_perm _), rfl⟩
  have hHs : IsSubnormal (coreHull (Om R) e) ⊤ :=
    CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal
      (TwinExitPf6.normal_coreHull hΩ hc2).isSubnormal
  intro L hL
  exact TL4.quiet_of_inO2_sub hHs htY ⟨_, hPn, hP2, by rw [← htb]; exact htP⟩ L hL

theorem p23E8Z_t_quiet_at_te (hT : Thm4RTwinBelow 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hZ : u * e ∈ zStarOf (rLayer (Om R) u))
    (htC : t ∈ Subgroup.centralizer ({t * e} : Set Y)) :
    ∀ L : Subgroup (OddQuot (t * e)), CFSG.IsComponent L →
      ∀ y ∈ L, oddQuotMk (t * e) ⟨t, htC⟩ * y = y * oddQuotMk (t * e) ⟨t, htC⟩ := by
  have h := ZTwo.t_mem_zStar hT hc hZ (c' := 1) (Subgroup.one_mem _)
  rw [one_mul, inv_one, mul_one] at h
  obtain ⟨h0, hh, hht⟩ := Subgroup.mem_map.mp h
  have e1 : h0 = ⟨t, htC⟩ := Subtype.ext hht
  subst e1
  intro L _ y _
  exact ((Subgroup.mem_center_iff.mp (Subgroup.mem_comap.mp hh)) y).symm

theorem p23E8Z_mem_normalizer_alpha_te
    (hT : Thm4RTwinBelow 3 n) (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hZ : u * e ∈ zStarOf (rLayer (Om R) u))
    (hAE : SecAE R e 6) {Z : Subgroup Y} (hZd : P23ZData t u e Z) {m : Y}
    (hmC : m ∈ Subgroup.centralizer ({t} : Set Y)) (hmN : m ∈ Subgroup.normalizer (Z : Set Y)) :
    m ∈ Subgroup.normalizer (alphaOf (Subgroup.closure ({t, e} : Set Y)) : Set Y) := by
  have hd := hc.data
  have hzt : IsUniqueInvolution (tightCore R) t :=
    Inner.isUniqueInvolution_core (CoreData.of_S hc.std.perp.core).datum
  have ht2 : t * t = 1 := hzt.sq
  have ht1 : t ≠ 1 := hzt.ne_one
  have he2 : e * e = 1 := hd.he2
  have he1 : e ≠ 1 := hd.he1
  have het : e ≠ t := fun h => e_not_mem_sup hc (h ▸ Subgroup.mem_sup_left hzt.mem)
  have hte : t * e = e * t := T7K.comm_e_of_mem_W hd hd.hzW
  have hmt : m * t * m⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hmC, mul_inv_cancel_right]
  obtain ⟨y, hy⟩ : ∃ y : Y, m * e * m⁻¹ = y := ⟨_, rfl⟩
  have hyZ : y ∈ Z := by
    rw [← hy]
    exact (Subgroup.mem_normalizer_iff.mp hmN e).mp hZd.he
  have hy2 : y * y = 1 := by
    rw [← hy]
    calc m * e * m⁻¹ * (m * e * m⁻¹) = m * (e * e) * m⁻¹ := by group
      _ = 1 := by rw [he2, mul_one, mul_inv_cancel]
  have hey' : e = m⁻¹ * y * m := by rw [← hy]; group
  have hy1 : y ≠ 1 := fun h => he1 (by rw [hey', h]; group)
  have hyt : y ≠ t := fun h => het (by
    rw [hey', h]
    calc m⁻¹ * t * m = m⁻¹ * (m * t * m⁻¹) * m := by rw [hmt]
      _ = t := by group)
  have hty : t * y = y * t := hZd.comm t hZd.ht y hyZ
  have hey : e * y = y * e := hZd.comm e hZd.he y hyZ
  have hconj : Generic.conjSub m (Subgroup.closure ({t, e} : Set Y)) =
      Subgroup.closure ({t, y} : Set Y) := by
    rw [T7A.conjSub_closure_pair, hmt, hy]
  have hA4 := T7A.isElemAbelian2_closure_pair ht2 he2 ht1 he1 het.symm hte
  have hD4 := T7A.isElemAbelian2_closure_pair ht2 hy2 ht1 hy1 hyt.symm hty
  have key : alphaOf (Subgroup.closure ({t, y} : Set Y)) =
      alphaOf (Subgroup.closure ({t, e} : Set Y)) := by
    by_cases hyA : y ∈ Subgroup.closure ({t, e} : Set Y)
    ·
      have hle : Subgroup.closure ({t, y} : Set Y) ≤ Subgroup.closure ({t, e} : Set Y) := by
        rw [Subgroup.closure_le]
        intro x hx
        rcases hx with h | h
        · rw [h]
          exact Subgroup.subset_closure (by simp)
        · rw [Set.mem_singleton_iff.mp h]
          exact hyA
      rw [Subgroup.eq_of_le_of_card_ge hle (hA4.1.trans hD4.1.symm).le]
    ·
      obtain ⟨B₃, hB₃⟩ : ∃ B₃ : Subgroup Y, B₃ = Subgroup.closure ({t * y, t, e} : Set Y) :=
        ⟨_, rfl⟩
      have hB : IsElemAbelian 2 B₃ := by
        rw [hB₃]
        exact S24.B_isElemAbelian_of ht2 he2 hy2 hte hty hey
      have hB8 : Nat.card B₃ = 8 := by
        rw [hB₃]
        exact S24.B_natCard_of ht2 he2 hy2 ht1 he1 het.symm hte hty hey hyA
      have hmemB : ∀ x ∈ ({t * y, t, e} : Set Y), x ∈ B₃ := fun x hx => by
        rw [hB₃]
        exact Subgroup.subset_closure hx
      have htB : t ∈ B₃ := hmemB _ (by simp)
      have heB : e ∈ B₃ := hmemB _ (by simp)
      have htyB : t * y ∈ B₃ := hmemB _ (by simp)
      have hyB : y ∈ B₃ := by
        have h := B₃.mul_mem (B₃.inv_mem htB) htyB
        rwa [inv_mul_cancel_left] at h
      have hteB : t * e ∈ B₃ := B₃.mul_mem htB heB
      have hAB : Subgroup.closure ({t, e} : Set Y) ≤ B₃ := by
        rw [Subgroup.closure_le]
        intro x hx
        rcases hx with h | h
        · rw [h]; exact htB
        · rw [Set.mem_singleton_iff.mp h]; exact heB
      have hDB : Subgroup.closure ({t, y} : Set Y) ≤ B₃ := by
        rw [Subgroup.closure_le]
        intro x hx
        rcases hx with h | h
        · rw [h]; exact htB
        · rw [Set.mem_singleton_iff.mp h]; exact hyB
      have hC : ∀ {a b : Y}, a ∈ B₃ → b ∈ B₃ → b ∈ Subgroup.centralizer ({a} : Set Y) :=
        fun ha hb => Lemma52Proof.le_centralizer_of_mem hB ha hb
      have hte1 : t * e ≠ 1 := fun h => het (by
        calc e = t⁻¹ * (t * e) := by group
          _ = t := by rw [h, mul_one]; exact inv_eq_of_mul_eq_one_right ht2)
      have htte : t ≠ t * e := fun h => he1 (by
        calc e = t⁻¹ * (t * e) := by group
          _ = 1 := by rw [← h, inv_mul_cancel])
      have hmte : m * (t * e) * m⁻¹ = t * y := by
        rw [← hy]
        calc m * (t * e) * m⁻¹ = (m * t * m⁻¹) * (m * e * m⁻¹) := by group
          _ = t * (m * e * m⁻¹) := by rw [hmt]
      have htCe : t ∈ Subgroup.centralizer ({e} : Set Y) := hC heB htB
      have htCte : t ∈ Subgroup.centralizer ({t * e} : Set Y) := hC hteB htB
      have v_t : Hyp51At B₃ t :=
        hyp51At_of_quiet_witness hB htB heB ht1 he1 het (hC htB heB)
          (p23E8Z_e_quiet_at_t hT hcit hP hc hZ _)
      have v_e : Hyp51At B₃ e :=
        hyp51At_of_quiet_witness hB heB htB he1 ht1 het.symm htCe
          (p23E8Z_t_quiet_at_e hc hAE htCe)
      have v_te : Hyp51At B₃ (t * e) :=
        hyp51At_of_quiet_witness hB hteB htB hte1 ht1 htte htCte
          (p23E8Z_t_quiet_at_te hT hc hZ htCte)
      have v_y : Hyp51At B₃ y := by
        have h := hyp51At_conj_of_quiet_witness hB (g := m) (c := e) (d := t)
          (by rw [hy]; exact hyB) (by rw [hmt]; exact htB) he1 ht1 het.symm htCe
          (p23E8Z_t_quiet_at_e hc hAE htCe)
        rwa [hy] at h
      have v_ty : Hyp51At B₃ (t * y) := by
        have h := hyp51At_conj_of_quiet_witness hB (g := m) (c := t * e) (d := t)
          (by rw [hmte]; exact htyB) (by rw [hmt]; exact htB) hte1 ht1 htte htCte
          (p23E8Z_t_quiet_at_te hT hc hZ htCte)
        rwa [hmte] at h
      have hHA : ∀ a ∈ Subgroup.closure ({t, e} : Set Y), a ≠ 1 → Hyp51At B₃ a := by
        intro a ha ha1
        rcases T8.mem_closure_pair_involutions ht2 he2 hte ha with h | h | h | h
        · exact absurd h ha1
        · rw [h]; exact v_t
        · rw [h]; exact v_e
        · rw [h]; exact v_te
      have hHD : ∀ d ∈ Subgroup.closure ({t, y} : Set Y), d ≠ 1 → Hyp51At B₃ d := by
        intro d hd hd1
        rcases T8.mem_closure_pair_involutions ht2 hy2 hty hd with h | h | h | h
        · exact absurd h hd1
        · rw [h]; exact v_t
        · rw [h]; exact v_y
        · rw [h]; exact v_ty
      exact (Lemma54Local.alphaOf_eq_alphaOf_of_hyp51At hB hB8 hAB hDB hA4.1 hD4.1 hHA
        hHD).symm
  rw [mem_normalizer_iff_conjSub_eq, ← alphaOf_conjSub, hconj, key]

theorem p23E8ZNormT_of_alpha (hT : Thm4RTwinBelow 3 n)
    (hα : P23Alpha n) : P23E8ZNormT n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hZ hAE
  have hd := hc.data
  have hzt : IsUniqueInvolution (tightCore R) t :=
    Inner.isUniqueInvolution_core (CoreData.of_S hc.std.perp.core).datum
  have hte : t * e = e * t := T7K.comm_e_of_mem_W hd hd.hzW
  have het : e ≠ t := fun h => e_not_mem_sup hc (h ▸ Subgroup.mem_sup_left hzt.mem)
  obtain ⟨-, hbal⟩ := hα Y R S t K' W u e g hc (Or.inl hZ)
  have hmemB : ∀ x ∈ ({u * e, u, t} : Set Y), x ∈ Subgroup.closure ({u * e, u, t} : Set Y) :=
    fun x hx => Subgroup.subset_closure hx
  have heB : e ∈ Subgroup.closure ({u * e, u, t} : Set Y) := by
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hmemB u (by simp)))
      (hmemB (u * e) (by simp))
    rwa [inv_mul_cancel_left] at h
  have hAB : Subgroup.closure ({t, e} : Set Y) ≤ Subgroup.closure ({u * e, u, t} : Set Y) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with h | h
    · rw [h]; exact hmemB t (by simp)
    · rw [Set.mem_singleton_iff.mp h]; exact heB
  have hA := hbal _ hAB
    (T7A.isElemAbelian2_closure_pair hzt.sq hd.he2 hzt.ne_one hd.he1 het.symm hte)
  rw [← hA]
  obtain ⟨Z, hZd⟩ := p23E8Z_zdata hT hcit hP hc hZ
  intro c hcC
  obtain ⟨o, ho, m, hm, rfl⟩ := hZd.frattini c hcC
  obtain ⟨hmC, hmN⟩ := Subgroup.mem_inf.mp hm
  exact Subgroup.mul_mem _
    (oddCoreOf_centralizer_le_normalizer_alphaOf (c := t) (z := e) hd.he2 hzt.ne_one hte ho)
    (p23E8Z_mem_normalizer_alpha_te hT hcit hP hc hZ hAE hZd hmC hmN)

theorem p23E8ZNormT_proved (hD4 : TwinCentRes.ModelFactD42)
    (hM12 : TwinCentRes.ModelFactM12) (hT4 : TwinThmE.T4Supply) : P23E8ZNormT n := by
  intro hcit hP
  exact p23E8ZNormT_of_alpha (hT4 n hcit hP) (p23Alpha_proved hD4 hM12 hT4 hcit hP) hcit hP

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
