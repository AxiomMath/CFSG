module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracEng
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapNorm
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapContraComp
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracDich
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracPc

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.LocalCores
  CFSG.ComponentClassification.Sol76 CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section SW2

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))} {s : X}

theorem piece_map_conj_ne {C D M P : Subgroup X} {t : X} (hM : IsPCompIn 2 C M)
    (hM' : IsPCompIn 2 C (M.map (MulAut.conj t).toMonoidHom))
    (hMt : M.map (MulAut.conj t).toMonoidHom ≠ M) (hPM : P ≤ M) (hDC : D ≤ C)
    (hP : IsPCompIn 2 D P) : P.map (MulAut.conj t).toMonoidHom ≠ P := by
  classical
  intro hPt
  set M' : Subgroup X := M.map (MulAut.conj t).toMonoidHom with hM'def
  have hPM' : P ≤ M' := by
    rw [← hPt]
    exact Subgroup.map_mono hPM
  have hPD : P ≤ D := hP.1
  have hPC : P ≤ C := hPD.trans hDC
  have hMC : M ≤ C := hM.1
  have hM'C : M' ≤ C := hM'.1
  set π : ↥C →* ↥C ⧸ pPrimeCore 2 ↥C := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  set K₁ : Subgroup (↥C ⧸ pPrimeCore 2 ↥C) := (M.subgroupOf C).map π with hK₁
  set K₂ : Subgroup (↥C ⧸ pPrimeCore 2 ↥C) := (M'.subgroupOf C).map π with hK₂
  have hK₁c : IsComponent K₁ := by
    obtain ⟨K, hK, -, hKeq, -⟩ := hM.2
    show IsComponent ((M.subgroupOf C).map π)
    rw [hKeq]
    exact hK
  have hK₂c : IsComponent K₂ := by
    obtain ⟨K, hK, -, hKeq, -⟩ := hM'.2
    show IsComponent ((M'.subgroupOf C).map π)
    rw [hKeq]
    exact hK
  have hK₁₂ : K₁ ≠ K₂ := by
    intro heq
    apply hMt
    have h1 := eq_of_map_pPrimeCore_eq hM'.2 hM.2 heq.symm
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hM'C, inf_of_le_left hMC] at h1
    exact h1
  have hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, Commute a b := fun a ha b hb =>
    commute_of_ne hK₁c hK₂c hK₁₂ ha hb
  have hcommP : ∀ x y : ↥P, (⁅(x : X), (y : X)⁆ : X) ∈ oddCoreOf P := by
    intro x y
    have hxC : (x : X) ∈ C := hPC x.2
    have hyC : (y : X) ∈ C := hPC y.2
    set xc : ↥C := ⟨(x : X), hxC⟩ with hxc
    set yc : ↥C := ⟨(y : X), hyC⟩ with hyc
    have hx1 : π xc ∈ K₁ := ⟨xc, show xc ∈ M.subgroupOf C from hPM x.2, rfl⟩
    have hy2 : π yc ∈ K₂ := ⟨yc, show yc ∈ M'.subgroupOf C from hPM' y.2, rfl⟩
    have h1 : ⁅xc, yc⁆ ∈ pPrimeCore 2 ↥C := by
      rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥C), MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ hx1 _ hy2).eq
    have h2 : (⁅(x : X), (y : X)⁆ : X) ∈ oddCoreOf C := ⟨⁅xc, yc⁆, h1, rfl⟩
    have h3 : (⁅(x : X), (y : X)⁆ : X) ∈ P := by
      have e : (⁅(x : X), (y : X)⁆ : X) = ((⁅x, y⁆ : ↥P) : X) := by
        simp [commutatorElement_def]
      rw [e]
      exact (⁅x, y⁆ : ↥P).2
    exact inf_oddCoreOf_le hPC ⟨h3, h2⟩
  have hq : IsTwoGenQuasi ↥P :=
    (isTwoGenQuasi_subgroupOf_iff hPD).1 (isPComponent_two_iff.1 hP.2).2
  obtain ⟨a, b, hab⟩ := hq.2.2.2
  induction a using QuotientGroup.induction_on with
  | H a =>
  induction b using QuotientGroup.induction_on with
  | H b =>
  induction a using QuotientGroup.induction_on with
  | H x =>
  induction b using QuotientGroup.induction_on with
  | H y =>
  apply hab
  have hc := hcommP x y
  obtain ⟨hcP, hcO⟩ := mem_oddCoreOf_iff.1 hc
  have h4 : (QuotientGroup.mk x : ↥P ⧸ pPrimeCore 2 ↥P) * QuotientGroup.mk y =
      QuotientGroup.mk y * QuotientGroup.mk x := by
    have h5 : (QuotientGroup.mk' (pPrimeCore 2 ↥P)) (⁅x, y⁆ : ↥P) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hcO
    rw [map_commutatorElement] at h5
    exact commutatorElement_eq_one_iff_mul_comm.1 h5
  exact congrArg (fun w : ↥P ⧸ pPrimeCore 2 ↥P =>
    (QuotientGroup.mk w : (↥P ⧸ pPrimeCore 2 ↥P) ⧸ center (↥P ⧸ pPrimeCore 2 ↥P))) h4

theorem exists_piece_of_model_center {Lu : Subgroup X} (M : AhatModel X n Lu) (hn : 8 ≤ n) {s : X}
    (hs : s ∈ normalizer (Lu : Set X)) (hs2 : s * s = 1)
    (h5 : 5 ≤ fixCount (M.perm s hs)) :
    ∃ P : Subgroup X, P ≤ Lu ⊓ centralizer ({s} : Set X) ∧
      (P.subgroupOf (Lu ⊓ centralizer ({s} : Set X))).Normal ∧ IsTwoGenQuasi ↥P ∧
      Nat.card (center (↥P ⧸ pPrimeCore 2 ↥P)) = 2 := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite M.K := M.finite_K
  set Lc : Subgroup X := Lu ⊓ centralizer ({s} : Set X) with hLc
  set σ : Perm (Fin n) := M.perm s hs with hσdef
  have hσ2 : σ * σ = 1 := by
    have key : ∀ (c : X) (hc : c ∈ normalizer (Lu : Set X)), c = 1 → M.perm c hc = 1 := by
      rintro c hc rfl
      exact M.perm_one hn
    rw [hσdef, ← M.perm_mul hn hs hs]
    exact key _ _ hs2
  obtain ⟨k, hk⟩ := exists_support_card_of_mul_self hσ2
  have hm : 5 ≤ n - 2 * k := by
    have := fixCount_add_support σ
    omega
  have hind : M.C.Induces (M.autOf s hs) σ := M.induces_perm hn s hs
  let θ : ↥Lc →* M.K :=
    (M.e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥Lu))).comp
      (Subgroup.inclusion (inf_le_left : Lc ≤ Lu))
  have hθ : ∀ g : ↥Lc, θ g = M.e (QuotientGroup.mk (⟨g.1, g.2.1⟩ : ↥Lu)) := fun g => rfl
  have hker : ¬ 2 ∣ Nat.card θ.ker := by
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥Lu)) := pPrimeCore_coprime_card
    let f : θ.ker →* pPrimeCore 2 ↥Lu :=
      { toFun := fun g => ⟨⟨g.1.1, g.1.2.1⟩, by
          have h1 : θ g.1 = 1 := g.2
          rw [hθ] at h1
          exact (QuotientGroup.eq_one_iff _).1 (M.e.injective (h1.trans (map_one M.e).symm))⟩
        map_one' := rfl
        map_mul' := fun a b => rfl }
    have hf : Function.Injective f := by
      intro a b hab
      have := congrArg (fun y : pPrimeCore 2 ↥Lu => ((y : ↥Lu) : X)) hab
      exact Subtype.ext (Subtype.ext this)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_injective f hf) hcop)
  obtain ⟨hLKfix, hLKdc, hLKmap⟩ := hind.fixedCompOf_isDoubleCover M.C hn hσ2 hk hm
  set LK : Subgroup M.K := M.C.fixedCompOf σ with hLK
  have hθfix : ∀ g : ↥Lc, θ g ∈ AhatData.fixSub (M.autOf s hs) := by
    intro g
    show M.autOf s hs (θ g) = θ g
    rw [hθ, M.autOf_mk]
    congr 2
    apply Subtype.ext
    rw [coe_conjAut]
    have hg := Subgroup.mem_centralizer_singleton_iff.1 g.2.2
    show s * g.1 * s⁻¹ = g.1
    rw [← hg]
    group
  have hnormK : ∀ g : ↥Lc, θ g ∈ normalizer (LK : Set M.K) := fun g =>
    M.C.mem_normalizer_fixedCompOf hn hind hσ2 hk hm (hθfix g)
  have hsurj : ∀ l ∈ LK, ∃ g : ↥Lc, θ g = l := by
    intro l hl
    obtain ⟨a, ha⟩ := M.surj_mk l
    have hlfix : M.autOf s hs l = l := hLKfix hl
    have h1 : M.e (QuotientGroup.mk (conjAut hs a)) = M.e (QuotientGroup.mk a) := by
      rw [← M.autOf_mk hs a, ha, hlfix]
    have h3 : (a⁻¹ * conjAut hs a : ↥Lu) ∈ pPrimeCore 2 ↥Lu :=
      (QuotientGroup.eq (a := a) (b := conjAut hs a)).1 (M.e.injective h1).symm
    have h4 : ((a⁻¹ * conjAut hs a : ↥Lu) : X) ∈ oddCoreOf Lu :=
      mem_oddCoreOf_iff.2 ⟨(a⁻¹ * conjAut hs a).2, h3⟩
    have e1 : ((a⁻¹ * conjAut hs a : ↥Lu) : X) = (a : X)⁻¹ * (s * (a : X) * s⁻¹) := by
      simp [coe_conjAut]
    rw [e1] at h4
    obtain ⟨p, hp, hpc⟩ := exists_mul_mem_centralizer_of_fixes_coset (P := oddCoreOf Lu)
      (odd_card_oddCoreOf Lu) (a := s) (k := 1) (by simpa [pow_two] using hs2)
      (mem_normalizer_oddCoreOf_of_mem_normalizer hs) (y := (a : X)) h4
    have hpL : p ∈ Lu := oddCoreOf_le Lu hp
    refine ⟨⟨(a : X) * p, Lu.mul_mem a.2 hpL, hpc⟩, ?_⟩
    have hpO : (⟨p, hpL⟩ : ↥Lu) ∈ pPrimeCore 2 ↥Lu := (mem_oddCoreOf_iff.1 hp).2
    rw [hθ]
    show M.e (QuotientGroup.mk (a * (⟨p, hpL⟩ : ↥Lu))) = l
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hpO, mul_one, ha]
  obtain ⟨-, hPG, -, -, hPq, hPdc⟩ := exists_piece_abstract θ hker hm hLKdc hnormK hsurj
  set Pc : Subgroup ↥Lc := oTwoPrimeOf (LK.comap θ) with hPc
  refine ⟨Pc.map Lc.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Lc.subtype_injective]
    exact hPG
  · exact (isTwoGenQuasi_congr_iff
      (Subgroup.equivMapOfInjective Pc Lc.subtype Lc.subtype_injective)).1 hPq
  · obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv
      (Subgroup.equivMapOfInjective Pc Lc.subtype Lc.subtype_injective)
    exact (Nat.card_congr (centerCongr f).toEquiv).symm.trans hPdc.2.1

theorem card_center_quot_map_conj {P : Subgroup X} (t : X)
    (hc : Nat.card (center (↥P ⧸ pPrimeCore 2 ↥P)) = 2) :
    Nat.card (center (↥(P.map (MulAut.conj t).toMonoidHom) ⧸
      pPrimeCore 2 ↥(P.map (MulAut.conj t).toMonoidHom))) = 2 := by
  let ψ : ↥P ≃* ↥(P.map (MulAut.conj t).toMonoidHom) :=
    Subgroup.equivMapOfInjective P _ (MulAut.conj t).injective
  obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv ψ
  exact (Nat.card_congr (centerCongr f).toEquiv).symm.trans hc

theorem isPGroup_center_image_of_card {C P : Subgroup X} (hP : IsPCompIn 2 C P)
    (hc : Nat.card (center (↥P ⧸ pPrimeCore 2 ↥P)) = 2) :
    IsPGroup 2 ↥(center ↥((P.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C)))) := by
  have h0 : IsPGroup 2 ↥(center (↥P ⧸ pPrimeCore 2 ↥P)) :=
    IsPGroup.of_card (n := 1) (by rw [hc, pow_one])
  obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.subgroupOfEquivOfLe hP.1)
  have h1 : IsPGroup 2 ↥(center (↥(P.subgroupOf C) ⧸ pPrimeCore 2 ↥(P.subgroupOf C))) :=
    h0.of_equiv (centerCongr f).symm
  obtain ⟨e⟩ := exists_mulEquiv_quot_image hP.2
  exact h1.of_equiv (centerCongr e)

theorem sw2_contra_ge9 (h : Sec5Data X n z Z S) (hs : IsSec5Inv X Z s) (hzs : z * s = s * z)
    (hn9 : 9 ≤ n) {M : Subgroup X} (hM : Sec5Comp X n (centralizer ({z} : Set X)) M)
    (hMs : M.map (MulAut.conj s).toMonoidHom ≠ M) {y : X} (hy2 : y * y = 1)
    (hyz : y * z = z * y) (hys : y * s = s * y) (hyM : y ∈ normalizer (M : Set X))
    (hfix : fixCount ((AhatModel.ofCover hM.2).perm y hyM) = n - 4) :
    ∃ B, Sec5Comp X n (centralizer ({s} : Set X)) B ∧
      ∃ b ∈ B, ⁅b, y⁆ ∉ oddCoreOf (centralizer ({s} : Set X)) := by
  classical
  by_contra hcon
  push Not at hcon
  have hn : 8 ≤ n := h.maxdeg.1
  have hy1 : y ≠ 1 := by
    intro e
    subst e
    have h1 : (AhatModel.ofCover hM.2).perm 1 hyM = 1 := (AhatModel.ofCover hM.2).perm_one hn
    rw [h1] at hfix
    have h8 : fixCount (1 : Perm (Fin n)) = n := by unfold fixCount; simp
    omega
  have hy2' : y ^ 2 = 1 := by rw [sq]; exact hy2
  have hy2o : orderOf y = 2 := orderOf_eq_prime hy2' hy1
  have hyCs : y ∈ centralizer ({s} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hys
  obtain ⟨B, hB, -⟩ := h.exists_comp_centralizer hs
  have hscj : y ∈ centralizerSection B (pPrimeCoreOf 2 B) :=
    normalizes_isPCompIn_of_comm_mem hB.isPCompIn (Subgroup.le_normalizer hyCs)
      (fun l hl => hcon B hB l hl)
  have hJ := K0_ne_bot_of_centralizerSection hy2' hB hscj
  obtain ⟨W, hW2, hWn, hV⟩ := exists_mirror_comm h hs hy2o hys hJ
  obtain ⟨P, hPL, hPn, hPq, hPc⟩ := exists_piece_of_model_center (AhatModel.ofCover hM.2) hn hyM
    hy2 (by rw [hfix]; omega)
  have hPcomp : IsPCompIn 2 (centralizer ({z} : Set X) ⊓ centralizer ({y} : Set X)) P :=
    isPCompIn_piece hM.isPCompIn hPL hPn hPq
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_z] at this
  have hzy : z * y = y * z := hyz.symm
  have hsC : s ∈ centralizer ({z} : Set X) ⊓ centralizer ({y} : Set X) :=
    ⟨Subgroup.mem_centralizer_singleton_iff.2 hzs.symm,
      Subgroup.mem_centralizer_singleton_iff.2 hys.symm⟩
  have hP'comp : IsPCompIn 2 (centralizer ({z} : Set X) ⊓ centralizer ({y} : Set X))
      (P.map (MulAut.conj s).toMonoidHom) := by
    have := Stage1.Thm2.Recip.isPCompIn_map_conj hPcomp s
    rwa [map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hsC)] at this
  have hPL' : P ≤ LPlusIn (centralizer ({y} : Set X)) :=
    le_LPlusIn_of_isPCompIn_inf hz2 hzy hPcomp
  have hP'L : P.map (MulAut.conj s).toMonoidHom ≤ LPlusIn (centralizer ({y} : Set X)) :=
    le_LPlusIn_of_isPCompIn_inf hz2 hzy hP'comp
  have hne : P.map (MulAut.conj s).toMonoidHom ≠ P := by
    have hM' : Sec5Comp X n (centralizer ({z} : Set X)) (M.map (MulAut.conj s).toMonoidHom) :=
      hM.map_conj (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.2 hzs.symm))
    exact piece_map_conj_ne hM.isPCompIn hM'.isPCompIn hMs (hPL.trans inf_le_left) inf_le_left
      hPcomp
  have hZ := isPGroup_center_image_of_card hPcomp hPc
  have hZ' := isPGroup_center_image_of_card hP'comp (card_center_quot_map_conj s hPc)
  have hCn : centralizer ({y} : Set X) ≤
      normalizer (pPrimeCoreOf 2 (LPlusIn (centralizer ({y} : Set X))) : Set X) :=
    (le_normalizer_LPlusIn _).trans (normalizer_le_normalizer_pPrimeCoreOf _)
  have hΛL : P ⊔ P.map (MulAut.conj s).toMonoidHom ≤ LPlusIn (centralizer ({y} : Set X)) :=
    sup_le hPL' hP'L
  exact swap_contra_comp (C := centralizer ({z} : Set X) ⊓ centralizer ({y} : Set X)) hs.sq
    hPcomp hP'comp hne hZ hZ' (OO := pPrimeCoreOf 2 (LPlusIn (centralizer ({y} : Set X))))
    (W₂ := W) (odd_card_oddCoreOf _) (fun x hx => hCn (LPlusIn_le _ (hΛL hx))) hW2 hWn
    (fun x hx => hV x (hΛL hx))

end SW2

end CFSG.OddStandard.Solomon75
