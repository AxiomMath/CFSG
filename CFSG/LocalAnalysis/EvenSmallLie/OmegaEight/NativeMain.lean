module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeClasses
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaFullCentralizer
public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernelSylow

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open CFSG.ComponentClassification.M12Cover (FourClassesLarge NoNormalFour
  FourClassesLarge.noNormalFour)
open CFSG.ComponentClassification.UnbalancedCatalog
  (even_orthogonal_all_involution_full_centralizer_odd_core)
open CFSG.ComponentClassification.J2Cover (rep_arrTable)

@[expose] def FullOddCore (Y : Type*) [Group Y] : Prop :=
  ∀ H : Subgroup (MulAut Y), (MulAut.conj : Y →* MulAut Y).range ≤ H → ∀ α ∈ H,
    orderOf α = 2 → CFSG.Assembly.oddCore ↥(H ⊓ Subgroup.centralizer ({α} : Set (MulAut Y))) = ⊥

theorem FullOddCore.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : FullOddCore X) : FullOddCore Y := by
  intro H' hH' α' hα'H hα'2
  set E : MulAut X ≃* MulAut Y := MulAut.congr e with hEdef
  have hEconj : ∀ a : X, E (MulAut.conj a) = MulAut.conj (e a) := by
    intro a
    ext y
    simp [hEdef, MulAut.conj_apply]
  set H : Subgroup (MulAut X) := H'.comap E.toMonoidHom with hHdef
  set α : MulAut X := E.symm α' with hαdef
  have hH : (MulAut.conj : X →* MulAut X).range ≤ H := by
    rintro _ ⟨a, rfl⟩
    show E (MulAut.conj a) ∈ H'
    rw [hEconj]
    exact hH' ⟨e a, rfl⟩
  have hαH : α ∈ H := by
    show E α ∈ H'
    simpa [hαdef] using hα'H
  have hα2 : orderOf α = 2 := by rw [hαdef, MulEquiv.orderOf_eq, hα'2]
  have hK : (H ⊓ Subgroup.centralizer ({α} : Set (MulAut X))).map E.toMonoidHom =
      H' ⊓ Subgroup.centralizer ({α'} : Set (MulAut Y)) := by
    ext z
    rw [Subgroup.mem_map_equiv, Subgroup.mem_inf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by simpa [hHdef] using h1, ?_⟩
      have := congrArg E h2
      simpa [hαdef] using this
    · rintro ⟨h1, h2⟩
      refine ⟨by simpa [hHdef] using h1, ?_⟩
      rw [hαdef, ← map_mul, ← map_mul, h2]
  let f := (E.subgroupMap (H ⊓ Subgroup.centralizer ({α} : Set (MulAut X)))).trans
    (MulEquiv.subgroupCongr hK)
  rw [← oddCore_map_mulEquiv f, h H hH α hαH hα2, Subgroup.map_bot]

theorem fullOddCore_omegaT : FullOddCore omegaT := by
  have h := even_orthogonal_all_involution_full_centralizer_odd_core
    omegaT .POmegaPlus (.inl rfl) 4 1 statedClassicalModel_omegaT
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := statedClassicalModel_omegaT
  have hfull := h K hK e
  refine FullOddCore.of_mulEquiv
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinatePlusWitnessEquiv K e).symm
    ?_
  intro H hH α hα hα2
  exact hfull H hH α hα hα2

theorem orderOf_eq_four_of_pow {G : Type*} [Group G] {g : G} (h4 : g ^ 4 = 1) (h2 : g ^ 2 ≠ 1) :
    orderOf g = 4 := by
  have hd : orderOf g ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have h1 : orderOf g ≠ 1 := fun h => h2 (by rw [orderOf_eq_one_iff.1 h, one_pow])
  have h2' : orderOf g ≠ 2 := fun h => h2 (by rw [← h, pow_orderOf_eq_one])
  have hmem : orderOf g ∈ Nat.divisors 4 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
  have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

theorem autEquiv_omegaT
    (w : omegaT) : autEquiv ⟨w, omegaT_le_autT w.2⟩ = MulAut.conj w := by
  ext g
  rw [autEquiv_apply, MulAut.conj_apply]
  rfl

theorem autEquiv_mem_of_dGroup (M : Subgroup (MulAut omegaT))
    (hM : (MulAut.conj : omegaT →* MulAut omegaT).range ≤ M) {x' : autT} (hx : autEquiv x' ∈ M)
    {d : Equiv.Perm (Fin 360)} (hd : d ∈ dGroup x') :
    ∃ hdA : d ∈ autT, autEquiv ⟨d, hdA⟩ ∈
      M ⊓ Subgroup.centralizer ({autEquiv x'} : Set (MulAut omegaT)) := by
  obtain ⟨hd1, hd2⟩ := Subgroup.mem_inf.1 hd
  set K : Subgroup (Equiv.Perm (Fin 360)) := (M.comap autEquiv.toMonoidHom).map autT.subtype
  have hle : omegaT ⊔ Subgroup.zpowers (x' : Equiv.Perm (Fin 360)) ≤ K := by
    refine sup_le ?_ ?_
    · intro w hw
      refine ⟨⟨w, omegaT_le_autT hw⟩, ?_, rfl⟩
      show autEquiv ⟨(⟨w, hw⟩ : omegaT), omegaT_le_autT hw⟩ ∈ M
      rw [autEquiv_omegaT]
      exact hM ⟨_, rfl⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨x', hx, rfl⟩
  obtain ⟨d', hd'M, rfl⟩ := hle hd1
  refine ⟨d'.2, ?_⟩
  change autEquiv d' ∈ _
  refine Subgroup.mem_inf.2 ⟨hd'M, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hd2 ⊢
  rw [← map_mul, ← map_mul]
  exact congrArg autEquiv (Subtype.ext hd2)

theorem fourClassesLarge_centralizer (M : Subgroup (MulAut omegaT))
    (hM : (MulAut.conj : omegaT →* MulAut omegaT).range ≤ M) {x : MulAut omegaT} (hxM : x ∈ M)
    (hx2 : orderOf x = 2) :
    FourClassesLarge ↥(M ⊓ Subgroup.centralizer ({x} : Set (MulAut omegaT))) := by
  set C := M ⊓ Subgroup.centralizer ({x} : Set (MulAut omegaT)) with hCdef
  intro y hy4 hy2
  set x' : autT := autEquiv.symm x with hx'def
  set y' : autT := autEquiv.symm (y : MulAut omegaT) with hy'def
  have hxx : autEquiv x' = x := autEquiv.apply_symm_apply x
  have hyy : autEquiv y' = y := autEquiv.apply_symm_apply _
  have hyo : orderOf (y : MulAut omegaT) = 4 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_four_of_pow hy4 hy2
  have hx2' : orderOf (x' : Equiv.Perm (Fin 360)) = 2 := by
    rw [Subgroup.orderOf_coe, hx'def, MulEquiv.orderOf_eq, hx2]
  have hy4' : orderOf (y' : Equiv.Perm (Fin 360)) = 4 := by
    rw [Subgroup.orderOf_coe, hy'def, MulEquiv.orderOf_eq, hyo]
  have hyx : (y : MulAut omegaT) * x = x * y :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 y.2).2
  have hcomm : (x' : Equiv.Perm (Fin 360)) * y' = y' * x' := by
    have : x' * y' = y' * x' := by
      apply autEquiv.injective
      rw [map_mul, map_mul, hxx, hyy, hyx]
    exact congrArg Subtype.val this
  have h5 := five_conj x'.2 hx2' y'.2 hy4' hcomm
  set S := conjClass (dGroup (x' : Equiv.Perm (Fin 360))) (y' : Equiv.Perm (Fin 360))
  have hSA : ∀ s ∈ S, s ∈ autT := by
    rintro s ⟨d, hd, rfl⟩
    obtain ⟨hdA, -⟩ := autEquiv_mem_of_dGroup M hM (hxx ▸ hxM) hd
    exact autT.mul_mem (autT.mul_mem hdA y'.2) (autT.inv_mem hdA)
  have hSC : ∀ s (hs : s ∈ S), ∃ c ∈ C,
      autEquiv ⟨s, hSA s hs⟩ = c * (y : MulAut omegaT) * c⁻¹ := by
    rintro s ⟨d, hd, rfl⟩
    obtain ⟨hdA, hdC⟩ := autEquiv_mem_of_dGroup M hM (hxx ▸ hxM) hd
    rw [hxx] at hdC
    refine ⟨autEquiv ⟨d, hdA⟩, hdC, ?_⟩
    have e : (⟨d * y' * d⁻¹, hSA _ ⟨d, hd, rfl⟩⟩ : autT) = ⟨d, hdA⟩ * y' * ⟨d, hdA⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hyy]
  have hmemC : ∀ s (hs : s ∈ S), autEquiv ⟨s, hSA s hs⟩ ∈ C := by
    intro s hs
    obtain ⟨c, hc, e⟩ := hSC s hs
    rw [e]
    exact C.mul_mem (C.mul_mem hc y.2) (C.inv_mem hc)
  have hfin : Finite (MulAut omegaT) := finite_mulAut_omegaT
  let f : S → {z : C // IsConj y z} := fun s =>
    ⟨⟨autEquiv ⟨s.1, hSA s.1 s.2⟩, hmemC s.1 s.2⟩, by
      obtain ⟨c, hc, e⟩ := hSC s.1 s.2
      exact isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext e.symm⟩⟩
  have hf : Function.Injective f := by
    intro s t hst
    have h1 := congrArg (fun z => ((z.1 : C) : MulAut omegaT)) hst
    have h2 := autEquiv.injective h1
    have h3 : (s : Equiv.Perm (Fin 360)) = t :=
      congrArg (fun z : autT => (z : Equiv.Perm (Fin 360))) h2
    exact Subtype.ext h3
  calc 5 ≤ S.ncard := h5
    _ = Nat.card S := (Nat.card_coe_set_eq S).symm
    _ ≤ Nat.card {z : C // IsConj y z} := Nat.card_le_card_of_injective f hf

theorem hypothesisOne_omegaT : HypothesisOne omegaT := by
  intro M hM x hxM hx2 B hB hiso
  have hfin : Finite (MulAut omegaT) := finite_mulAut_omegaT
  set C := M ⊓ Subgroup.centralizer ({x} : Set (MulAut omegaT))
  have hO : CFSG.Assembly.oddCore C = ⊥ := fullOddCore_omegaT M hM x hxM hx2
  have hN : NoNormalFour C := (fourClassesLarge_centralizer M hM hxM hx2).noNormalFour
  let e : C ⧸ CFSG.Assembly.oddCore C ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have hBn : (B.map e.toMonoidHom).Normal := hB.map _ e.surjective
  obtain ⟨h4, h24⟩ := hN _ hBn
  have eB : B ≃* B.map e.toMonoidHom := e.subgroupMap B
  rcases hiso with hi | hi
  · obtain ⟨i⟩ := hi
    exact h4.false (eB.symm.trans i)
  · obtain ⟨i⟩ := hi
    exact h24.false (eB.symm.trans i)

theorem exists_conj_mem_sylowT_single
    {x : Equiv.Perm (Fin 360)} (hx : x ∈ autT)
    (hx2 : orderOf x = 2) : ∃ a ∈ autT, a * x * a⁻¹ ∈ sylowT := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set x' : autT := ⟨x, hx⟩
  have hX : IsPGroup 2 (Subgroup.zpowers x') := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx2, pow_one])
  obtain ⟨Q, hQ⟩ := hX.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq autT sylowA Q
  have h1 : x' ∈ (Q : Subgroup autT) := hQ (Subgroup.mem_zpowers x')
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply, coe_sylowA,
    Subgroup.mem_subgroupOf] at h1
  exact ⟨(g⁻¹ : autT), (g⁻¹ : autT).2, by simpa using h1⟩

theorem exists_conj_main
    {x : Equiv.Perm (Fin 360)} (hx : x ∈ autT) (hx2 : orderOf x = 2) :
    ∃ i < 5, ∃ h ∈ autT, x = h * mainPerm i * h⁻¹ ∧ (x ∈ omegaT ↔ i < 3) := by
  obtain ⟨a, ha, hxa⟩ := exists_conj_mem_sylowT_single hx hx2
  have hx2' : orderOf (a * x * a⁻¹) = 2 := by
    rw [show a * x * a⁻¹ = MulAut.conj a x from rfl, MulEquiv.orderOf_eq, hx2]
  obtain ⟨j, hj, c, hc, hcj⟩ := exists_rep_of_involution hxa hx2'
  have hg : a⁻¹ * c ∈ autT := autT.mul_mem (autT.inv_mem ha) (sylowT_le_autT hc)
  have hxr : x = (a⁻¹ * c) * repPerm j * (a⁻¹ * c)⁻¹ := by
    calc x = a⁻¹ * (a * x * a⁻¹) * a := by group
      _ = (a⁻¹ * c) * repPerm j * (a⁻¹ * c)⁻¹ := by rw [hcj]; group
  refine ⟨repTypes.getD j 0, repTypes_lt hj, a⁻¹ * c * conjPerm j,
    autT.mul_mem hg (conjPerm_spec hj).2, ?_, ?_⟩
  · rw [hxr, ← conj_mainPerm hj]
    group
  · rw [hxr, ← conj_mem_omegaT hg, repPerm_mem_omegaT_iff hj]

theorem fgWords_letters : fgWords.all (lettersOK 17) = true := by decide

@[expose] def fgPerm (i : ℕ) : Equiv.Perm (Fin 360) := permOfArr 360 (omegaW (fgWords.getD i []))

theorem fgPerm_spec {i : ℕ} (hi : i < 2) :
    Rep 360 (omegaW (fgWords.getD i [])) (fgPerm i) ∧
      Rep 360 (invCand 360 (omegaW (fgWords.getD i []))) (fgPerm i)⁻¹ ∧ fgPerm i ∈ omegaT := by
  obtain ⟨h1, h2⟩ := omegaW_spec (letters_of_all fgWords_letters i)
  refine ⟨h1, rep_inv_of_isInvA h1 (invs_ok.2.2.2 _ (getD_mem_of_lt (d := []) ?_)), h2⟩
  have : fgWords.length = 2 := rfl
  omega

theorem fg_main {i : ℕ} (hi : i < 2) :
    (fgPerm i * mainPerm (i + 3) * (fgPerm i)⁻¹ * mainPerm (i + 3)) ^ 2 = 1 ∧
      fgPerm i * mainPerm (i + 3) * (fgPerm i)⁻¹ * mainPerm (i + 3) ≠ 1 := by
  have h := fg_check
  simp only [fgCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true']
    at h
  obtain ⟨h1, h2⟩ := h i hi
  obtain ⟨r1, r2, -⟩ := fgPerm_spec hi
  have rx := (mainPerm_spec (show i + 3 < 5 by omega)).1
  have rv := rep_compA (rep_conjArr r1 r2 rx) rx
  refine ⟨?_, fun h0 => ?_⟩
  · rw [sq]
    exact eq_of_eqA (rep_compA rv rv) rep_idA h1
  · rw [h0] at rv
    rw [(eqA_iff rv rep_idA).2 rfl] at h2
    exact Bool.noConfusion h2

theorem foursGroupCondition_omegaT : FoursGroupCondition omegaT := by
  intro φ hφ hout
  set a : autT := autEquiv.symm φ with hadef
  have hφa : autEquiv a = φ := autEquiv.apply_symm_apply φ
  have ha2 : (a : Equiv.Perm (Fin 360)) * a = 1 := by
    have : a * a = 1 := autEquiv.injective (by rw [map_mul, hφa, hφ, map_one])
    exact congrArg Subtype.val this
  have ha1 : (a : Equiv.Perm (Fin 360)) ≠ 1 := by
    intro h
    apply hout 1
    rw [← hφa, show a = 1 from Subtype.ext h, map_one, map_one]
  have hnot : (a : Equiv.Perm (Fin 360)) ∉ omegaT := by
    intro h
    apply hout ⟨a, h⟩
    rw [← hφa, ← autEquiv_omegaT]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hao : orderOf (a : Equiv.Perm (Fin 360)) = 2 := orderOf_eq_prime (by rw [sq, ha2]) ha1
  obtain ⟨i, hi, h, hh, hx, hiff⟩ := exists_conj_main a.2 hao
  have hi3 : 3 ≤ i := by
    by_contra hlt
    exact hnot (hiff.2 (by omega))
  obtain ⟨hv2, hv1⟩ := fg_main (i := i - 3) (by omega)
  rw [show i - 3 + 3 = i by omega] at hv2 hv1
  set l := fgPerm (i - 3) with hldef
  set x := mainPerm i with hxdef
  have hl : l ∈ omegaT := (fgPerm_spec (by omega)).2.2
  have hxx : x * x = 1 := by
    have e : (a : Equiv.Perm (Fin 360)) * a = h * (x * x) * h⁻¹ := by rw [hx]; group
    rw [ha2] at e
    have e2 := congrArg (fun g => h⁻¹ * g * h) e
    rw [show h⁻¹ * 1 * h = 1 by group, show h⁻¹ * (h * (x * x) * h⁻¹) * h = x * x by group]
      at e2
    exact e2.symm
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  set L : omegaT := ⟨h * l * h⁻¹, (conj_mem_omegaT hh).1 hl⟩
  have key : ((L * (φ L)⁻¹ : omegaT) : Equiv.Perm (Fin 360)) =
      h * (l * x * l⁻¹ * x) * h⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hφa, autEquiv_apply]
    change h * l * h⁻¹ * ((a : Equiv.Perm (Fin 360)) * (h * l * h⁻¹) *
      (a : Equiv.Perm (Fin 360))⁻¹)⁻¹ = _
    rw [hx]
    simp only [mul_inv_rev, inv_inv, hxinv]
    group
  refine ⟨L, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_pow, key, Subgroup.coe_one,
      show h * (l * x * l⁻¹ * x) * h⁻¹ = MulAut.conj h (l * x * l⁻¹ * x) from rfl, ← map_pow, hv2,
      map_one]
  · rw [center_omegaT, Subgroup.mem_bot]
    intro h0
    apply hv1
    have e := congrArg Subtype.val h0
    rw [key, Subgroup.coe_one] at e
    calc l * x * l⁻¹ * x = h⁻¹ * (h * (l * x * l⁻¹ * x) * h⁻¹) * h := by group
      _ = 1 := by rw [e]; group

theorem rep_powArr {t : Array ℕ} {g : Equiv.Perm (Fin 360)} (ht : Rep 360 t g) :
    ∀ k, Rep 360 (powArr t k) (g ^ k)
  | 0 => by simpa [powArr] using (rep_idA (n := 360))
  | k + 1 => by
    rw [powArr, pow_succ']
    exact rep_compA ht (rep_powArr ht k)

theorem oddData_letters :
    (oddData.all fun d => lettersOK 17 d.1 && lettersOK 17 d.2.1) = true := by decide

theorem odd_main
    {i : ℕ} (hi : i < 3) : ∃ u ∈ omegaT, ∃ v ∈ omegaT, Odd (orderOf u) ∧
    Odd (orderOf v) ∧ u * mainPerm i = mainPerm i * u ∧ v * mainPerm i = mainPerm i * v ∧
    ∃ k, (u * v) ^ k = mainPerm i := by
  have hn : (360 : ℕ) < 2 ^ 32 := by norm_num
  have h := odd_check
  simp only [oddCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hou, hov⟩, htu⟩, htv⟩, hcu⟩, hcv⟩, hpow⟩ := h i hi
  have hlen : oddData.length = 3 := rfl
  have hd := List.all_eq_true.1 oddData_letters _
    (getD_mem_of_lt (d := ([], [], 0, 0, 0)) (show i < oddData.length by omega))
  rw [Bool.and_eq_true] at hd
  obtain ⟨ru, hu⟩ := omegaW_spec hd.1
  obtain ⟨rv, hv⟩ := omegaW_spec hd.2
  have rx := (mainPerm_spec (show i < 5 by omega)).1
  refine ⟨_, hu, _, hv, ?_, ?_, eq_of_eqA (rep_compA ru rx) (rep_compA rx ru) hcu,
    eq_of_eqA (rep_compA rv rx) (rep_compA rx rv) hcv, _,
    eq_of_eqA (rep_powArr (rep_compA ru rv) _) rx hpow⟩
  · rw [(ordTest_iff perm_faithful (rep_arrTable hn ru) (by omega)).1 htu]
    exact Nat.odd_iff.2 hou
  · rw [(ordTest_iff perm_faithful (rep_arrTable hn rv) (by omega)).1 htv]
    exact Nat.odd_iff.2 hov

theorem involutionsInOddPart_omegaT
    : InvolutionsInOddPart omegaT := by
  intro u hu
  have hu0 : orderOf (u : Equiv.Perm (Fin 360)) = 2 := by rw [Subgroup.orderOf_coe, hu]
  obtain ⟨i, -, h, hh, hx, hiff⟩ := exists_conj_main (omegaT_le_autT u.2) hu0
  obtain ⟨p, hp, q, hq, hpo, hqo, hpc, hqc, k, hk⟩ := odd_main (hiff.1 u.2)
  set P : omegaT := ⟨h * p * h⁻¹, (conj_mem_omegaT hh).1 hp⟩
  set Q : omegaT := ⟨h * q * h⁻¹, (conj_mem_omegaT hh).1 hq⟩
  have hord : ∀ g : Equiv.Perm (Fin 360), orderOf (h * g * h⁻¹) = orderOf g := fun g => by
    rw [show h * g * h⁻¹ = MulAut.conj h g from rfl, MulEquiv.orderOf_eq]
  have hcomm : ∀ g : Equiv.Perm (Fin 360), g * mainPerm i = mainPerm i * g →
      h * g * h⁻¹ * u = u * (h * g * h⁻¹) := by
    intro g hg
    rw [hx]
    calc h * g * h⁻¹ * (h * mainPerm i * h⁻¹) = h * (g * mainPerm i) * h⁻¹ := by group
      _ = h * (mainPerm i * g) * h⁻¹ := by rw [hg]
      _ = h * mainPerm i * h⁻¹ * (h * g * h⁻¹) := by group
  have hP : P ∈ {g : omegaT | g * u = u * g ∧ Odd (orderOf g)} :=
    ⟨Subtype.ext (hcomm p hpc), by rw [Subgroup.orderOf_mk, hord]; exact hpo⟩
  have hQ : Q ∈ {g : omegaT | g * u = u * g ∧ Odd (orderOf g)} :=
    ⟨Subtype.ext (hcomm q hqc), by rw [Subgroup.orderOf_mk, hord]; exact hqo⟩
  have huPQ : u = (P * Q) ^ k := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_mul, hx, ← hk]
    change h * (p * q) ^ k * h⁻¹ = (h * p * h⁻¹ * (h * q * h⁻¹)) ^ k
    rw [show h * p * h⁻¹ * (h * q * h⁻¹) = MulAut.conj h (p * q) by
      rw [MulAut.conj_apply]; group, ← map_pow, MulAut.conj_apply]
  have hmem := Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure hP)
    (Subgroup.subset_closure hQ)) k
  rwa [← huPQ] at hmem

theorem omegaEightNativePackage :
    ∀ (X : Type) [Group X], CFSG.Blueprint.LieModel X .POmegaPlus 4 2 1 →
      Nat.card X = 174182400 ∧ Nat.card (MulAut X) = 6 * 174182400 ∧ HypothesisOne X ∧
        FoursGroupCondition X ∧ InvolutionsInOddPart X := by
  intro X _ hX
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hX
  refine ⟨?_, ?_, hypothesisOne_of_mulEquiv e.symm hypothesisOne_omegaT,
    FoursGroupCondition.of_mulEquiv e.symm foursGroupCondition_omegaT,
    InvolutionsInOddPart.of_mulEquiv e.symm involutionsInOddPart_omegaT⟩
  · rw [Nat.card_congr e.toEquiv, card_omegaT]
  · rw [Nat.card_congr (MulAut.congr e).toEquiv, card_mulAut_omegaT]

section LieModel

variable {X : Type} [Group X] (hX : CFSG.Blueprint.LieModel X .POmegaPlus 4 2 1)
include hX

theorem card_of_lieModel
    : Nat.card X = 174182400 := (omegaEightNativePackage X hX).1

theorem card_mulAut_of_lieModel
    : Nat.card (MulAut X) = 6 * 174182400 :=
  (omegaEightNativePackage X hX).2.1

theorem hypothesisOne_of_lieModel
    : HypothesisOne X := (omegaEightNativePackage X hX).2.2.1

theorem foursGroupCondition_of_lieModel : FoursGroupCondition X :=
  (omegaEightNativePackage X hX).2.2.2.1

theorem involutionsInOddPart_of_lieModel : InvolutionsInOddPart X :=
  (omegaEightNativePackage X hX).2.2.2.2

end LieModel

section Centerless

variable {L : Type} [Group L] (hZ : Subgroup.center L = ⊥)
  (h : CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .POmegaPlus 4 2 1)
include hZ h

theorem foursGroupCondition_of_center_eq_bot
    : FoursGroupCondition L :=
  FoursGroupCondition.of_mulEquiv (mulEquivQuotientCenter hZ) (foursGroupCondition_of_lieModel h)

theorem involutionsInOddPart_of_center_eq_bot
    : InvolutionsInOddPart L :=
  (involutionsInOddPart_of_lieModel h).of_mulEquiv (mulEquivQuotientCenter hZ)

end Centerless

end CFSG.EvenSmallLie.OmegaEight
