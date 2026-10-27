module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDefs
public import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.GroupTheory.PLayer.CenterQuotientAction
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzAutFixOfN0
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzAutCentralizerN0Proved
public import CFSG.CharacterTheory.Semidihedral.OddCentralizerSylowTwo
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {t y : G}

omit [Finite G] in
private theorem le_A_and_centralizes_of_l34SuzOdd (hD : L34SuzOddData A V K y) :
    K ≤ A ∧ K ≤ centralizer (V : Set G) := by
  have hKA : K ≤ A := hD.K_eq ▸ (Subgroup.commutator_le_self _).trans inf_le_left
  have hKV : K ≤ centralizer (V : Set G) :=
    hD.K_eq ▸ (Subgroup.commutator_le_self _).trans inf_le_right
  exact ⟨hKA, hKV⟩

omit [Finite G] in
private theorem action_le_autFixing {M : Subgroup G} (hMN : M ≤ normalizer (A : Set G))
    (hMK : M ≤ centralizer (K : Set G)) :
    (CFSG.normalizerToCenterQuotientAut A M hMN).range ≤
      CFSG.EvenSporadicStandard.Induction.Cover.autFixing
        ((K.subgroupOf A).map (QuotientGroup.mk' (center ↥A))) := by
  rintro β ⟨m, rfl⟩ y hy
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hy
  have hmK : (m : G) ∈ centralizer (K : Set G) := hMK m.2
  have hconj : CFSG.normalizerConjAutOfMem A M hMN m k = k := by
    apply Subtype.ext
    simp only [CFSG.normalizerConjAutOfMem, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_inclusion]
    rw [← Subgroup.mem_centralizer_iff.1 hmK (k : G) hk, mul_inv_cancel_right]
  rw [← CFSG.normalizerConjAutOfMem_comp_mk A M hMN m k, hconj]

theorem sup_zpowers_le_centralizer_inf_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) :
    V ⊔ zpowers t ≤ centralizer ({t} : Set G) ⊓ centralizer (K : Set G) := by
  obtain ⟨hKA, hKV⟩ := le_A_and_centralizes_of_l34SuzOdd hD
  refine sup_le (fun v hv => ?_) (Subgroup.zpowers_le.mpr ?_)
  · refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hS.t_mem v (hD.le_A hv)
    · rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (Subgroup.mem_centralizer_iff.1 (hKV hk) v hv).symm
  · refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
    · rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact Subgroup.mem_centralizer_iff.1 hS.t_mem k (hKA hk)

private theorem not_mem_A_of_l34SuzOdd (hS : L34SuzOddSetting A t) : t ∉ A := by
  intro htA
  have htZ : (⟨t, htA⟩ : ↥A) ∈ center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hS.t_mem (a : G) a.2)
  have h2 : 2 ∣ Nat.card (center ↥A) := by
    have hd := orderOf_dvd_natCard (⟨⟨t, htA⟩, htZ⟩ : ↥(center ↥A))
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hS.orderOf_t] at hd
  exact hS.odd_card_center.not_two_dvd_nat h2

theorem card_sup_zpowers_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) : Nat.card ↥(V ⊔ zpowers t) = 8 := by
  have hdisj : Disjoint V (zpowers t) := by
    rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxV, hxt⟩ := Subgroup.mem_inf.1 hx
    rcases (CFSG.Semidihedral.OddCentralizerSylowTwo.mem_zpowers_involution t
      hS.orderOf_t x).1 hxt with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hxV (fun htV => not_mem_A_of_l34SuzOdd hS (hD.le_A htV))
  have hnorm : zpowers t ≤ normalizer (V : Set G) := by
    have ht : t ∈ centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subgroup.mem_centralizer_iff.1 hS.t_mem v (hD.le_A hv)
    exact (Subgroup.zpowers_le.mpr ht).trans (Subgroup.centralizer_le_normalizer _)
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer V (zpowers t)
      hnorm hdisj, hD.card_V, Nat.card_zpowers, hS.orderOf_t]

private theorem isSolvable_centralizer_of_l34SuzOdd (hS : L34SuzOddSetting A t) :
    Group.IsSolvable ↥(centralizer (A : Set G)) := by
  let X : Subgroup G := centralizer (A : Set G)
  let tX : ↥X := ⟨t, hS.t_mem⟩
  have htX : orderOf tX = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hS.orderOf_t
  have hC : ∀ P : Sylow 2 (Subgroup.centralizer ({tX} : Set ↥X)), Nat.card P = 2 := by
    intro P
    let CX : Subgroup ↥X := Subgroup.centralizer ({tX} : Set ↥X)
    let j : CX := ⟨tX, Subgroup.mem_centralizer_singleton_iff.2 (by simp)⟩
    have hj : orderOf j = 2 := by rw [Subgroup.orderOf_mk, htX]
    have hIj : IsPGroup 2 (Subgroup.zpowers j) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hj]; norm_num)
    obtain ⟨P₁, hP₁⟩ := hIj.exists_le_sylow
    have hcard₁ : Nat.card P₁ = 2 := by
      have hle : Nat.card P₁ ≤ 2 := by
        have hmap : IsPGroup 2 (P₁.map CX.subtype) := P₁.isPGroup'.map CX.subtype
        obtain ⟨R, hR⟩ := hmap.exists_le_sylow
        calc Nat.card P₁ = Nat.card (P₁.map CX.subtype) :=
              (Subgroup.card_map_of_injective CX.subtype_injective).symm
          _ ≤ Nat.card R := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hR)
          _ = 2 := hS.card_sylow R
      have hge : 2 ≤ Nat.card P₁ := by
        have hz : Nat.card (Subgroup.zpowers j) = 2 := by rw [Nat.card_zpowers, hj]
        calc 2 = Nat.card (Subgroup.zpowers j) := hz.symm
          _ ≤ Nat.card P₁ := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hP₁)
      exact le_antisymm hle hge
    calc Nat.card P = Nat.card P₁ := Nat.card_congr (Sylow.equiv P P₁).toEquiv
      _ = 2 := hcard₁
  obtain ⟨-, hodd, -, hquotcard, -⟩ :=
    CFSG.Semidihedral.OddCentralizerSylowTwo.involution_centralizer_two_part_odd_core tX htX hC
  have : Group.IsSolvable ↥(CFSG.oddCore ↥X) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hquot : Group.IsSolvable (↥X ⧸ CFSG.oddCore ↥X) := by
    have hp : IsPGroup 2 (↥X ⧸ CFSG.oddCore ↥X) :=
      IsPGroup.of_card (n := 1) (by rw [hquotcard]; norm_num)
    have : Group.IsNilpotent (↥X ⧸ CFSG.oddCore ↥X) := hp.isNilpotent
    exact IsNilpotent.to_isSolvable
  have : Group.IsSolvable (↥X ⧸ CFSG.oddCore ↥X) := hquot
  exact CFSG.isSolvable_of_normal_subgroup_and_quotient (CFSG.oddCore ↥X)

section Certificates


private theorem autFixFacts_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) :
    CFSG.EvenSporadicStandard.Induction.AutFixFacts
        ((K.subgroupOf A).map (QuotientGroup.mk' (center ↥A))) 4 ∧
      ∀ Q : Subgroup (CFSG.EvenSporadicStandard.Induction.Cover.autFixing
        ((K.subgroupOf A).map (QuotientGroup.mk' (center ↥A)))),
        IsPGroup 2 Q → ∀ x ∈ Q, x * x = 1 := by
  have hKA : K ≤ A := (le_A_and_centralizes_of_l34SuzOdd hD).1
  have hVne : V ≠ ⊥ := by
    intro h
    have hcv := hD.card_V
    rw [h, Subgroup.card_bot] at hcv
    norm_num at hcv
  obtain ⟨u, huV, hu1⟩ := (Subgroup.bot_or_exists_ne_one V).resolve_left hVne
  have hu2 : orderOf u = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hD.mul_self u huV) hu1
  have huA : u ∈ A := hD.le_A huV
  have huNotCenter : (⟨u, huA⟩ : ↥A) ∉ center ↥A := by
    intro huZ
    have h2 : 2 ∣ Nat.card (center ↥A) := by
      have hd := orderOf_dvd_natCard (⟨⟨u, huA⟩, huZ⟩ : ↥(center ↥A))
      rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hu2] at hd
    exact hS.odd_card_center.not_two_dvd_nat h2
  have hqu1 : QuotientGroup.mk' (center ↥A) ⟨u, huA⟩ ≠ 1 := fun h =>
    huNotCenter ((QuotientGroup.eq_one_iff _).1 h)
  have hqu2 : orderOf (QuotientGroup.mk' (center ↥A) ⟨u, huA⟩) = 2 := by
    refine orderOf_eq_prime ?_ hqu1
    rw [← map_pow, show (⟨u, huA⟩ : ↥A) ^ 2 = 1 from
      Subtype.ext (by simpa [pow_two] using hD.mul_self u huV), map_one]
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hD.perfect
  have hKsubPerf : Group.IsPerfect ↥(K.subgroupOf A) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKA).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKA).symm.surjective
  have : Group.IsPerfect ↥(K.subgroupOf A) := hKsubPerf
  let Kbar : Subgroup (↥A ⧸ center ↥A) :=
    (K.subgroupOf A).map (QuotientGroup.mk' (center ↥A))
  have hKbarperf : Group.IsPerfect ↥Kbar :=
    Group.IsPerfect.map (f := QuotientGroup.mk' (center ↥A)) (H := K.subgroupOf A)
  have hKbarcomm : ∀ k ∈ Kbar,
      k * (QuotientGroup.mk' (center ↥A) ⟨u, huA⟩) =
        (QuotientGroup.mk' (center ↥A) ⟨u, huA⟩) * k := by
    intro k hk
    obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.1 hk
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1
      ((le_A_and_centralizes_of_l34SuzOdd hD).2 (Subgroup.mem_subgroupOf.1 hk₀))
      u huV).symm
  have hPair : CFSG.EvenSporadicStandard.Solomon78.SuzPair (↥A ⧸ center ↥A) ⊤ Kbar
      (QuotientGroup.mk' (center ↥A) ⟨u, huA⟩) :=
    ⟨Subgroup.mem_top _, hqu2, le_top, hKbarcomm, hKbarperf, hD.card_image⟩
  have haux := (CFSG.EvenSporadicStandard.Induction.suzAutFix_of_autCentralizerN0
    CFSG.EvenSporadicStandard.Induction.suzAutCentralizerN0_proved)
    (↥A ⧸ center ↥A) hS.suz Kbar (QuotientGroup.mk' (center ↥A) ⟨u, huA⟩) hPair
  simpa only [Kbar] using haux

private theorem card_le_eight_of_action (hS : L34SuzOddSetting A t)
    {M P : Subgroup G} (hMN : M ≤ normalizer (A : Set G))
    (hMK : M ≤ centralizer (K : Set G))
    (hfix : CFSG.EvenSporadicStandard.Induction.AutFixFacts
      ((K.subgroupOf A).map (QuotientGroup.mk' (center ↥A))) 4)
    (hfix2 : ∀ Q : Subgroup (CFSG.EvenSporadicStandard.Induction.Cover.autFixing
      ((K.subgroupOf A).map (QuotientGroup.mk' (center ↥A)))),
        IsPGroup 2 Q → ∀ x ∈ Q, x * x = 1)
    (hP : P ≤ M) (h2 : IsPGroup 2 P) : Nat.card P ≤ 8 := by
  let Kbar : Subgroup (↥A ⧸ center ↥A) :=
    (K.subgroupOf A).map (QuotientGroup.mk' (center ↥A))
  let φ := CFSG.normalizerToCenterQuotientAut A M hMN
  let f := φ.comp (Subgroup.inclusion hP)
  have hrange_le : φ.range ≤ CFSG.EvenSporadicStandard.Induction.Cover.autFixing Kbar :=
    action_le_autFixing hMN hMK
  have hkerEq : φ.ker = (M ⊓ centralizer (A : Set G)).subgroupOf M :=
    CFSG.ker_normalizerToCenterQuotientAut hS.standard.1.1 hMN
  have hker2 : IsPGroup 2 ↥f.ker := h2.to_subgroup f.ker
  let ψ : ↥f.ker →* ↥(centralizer (A : Set G)) :=
    { toFun := fun x =>
        ⟨Subgroup.inclusion hP (x : P), by
          have hxM : Subgroup.inclusion hP (x : P) ∈ φ.ker := by
            rw [MonoidHom.mem_ker]
            simpa only [f, MonoidHom.comp_apply] using MonoidHom.mem_ker.1 x.2
          have hx : Subgroup.inclusion hP (x : P) ∈
              (M ⊓ centralizer (A : Set G)).subgroupOf M := by
            rw [← hkerEq]
            exact hxM
          exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hψ : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    have hval : ((a : P) : G) = ((b : P) : G) := by
      have h := congrArg (fun z : ↥(centralizer (A : Set G)) => (z : G)) hab
      have h1 : ((ψ a : ↥(centralizer (A : Set G))) : G) = ((a : P) : G) := by
        change (Subgroup.inclusion hP (a : P) : G) = ((a : P) : G)
        exact Subgroup.coe_inclusion hP (a : P)
      have h2 : ((ψ b : ↥(centralizer (A : Set G))) : G) = ((b : P) : G) := by
        change (Subgroup.inclusion hP (b : P) : G) = ((b : P) : G)
        exact Subgroup.coe_inclusion hP (b : P)
      rwa [h1, h2] at h
    exact Subtype.ext hval
  have hkerLe : Nat.card ↥f.ker ≤ 2 := by
    have htop2 : IsPGroup 2 (⊤ : Subgroup ↥f.ker) := hker2.to_subgroup ⊤
    have hmap2 : IsPGroup 2 ((⊤ : Subgroup ↥f.ker).map ψ) := htop2.map ψ
    obtain ⟨R, hR⟩ := hmap2.exists_le_sylow
    calc Nat.card ↥f.ker = Nat.card ((⊤ : Subgroup ↥f.ker).map ψ) := by
          rw [Subgroup.card_map_of_injective hψ, Subgroup.card_top]
      _ ≤ Nat.card R := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hR)
      _ = 2 := hS.card_sylow R
  have hrange2 : IsPGroup 2 ↥f.range := by
    have hmap := (h2.to_subgroup (⊤ : Subgroup P)).map f
    rw [← MonoidHom.range_eq_map] at hmap
    exact hmap
  have hfrange : f.range ≤ φ.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨Subgroup.inclusion hP x, rfl⟩
  let g : ↥f.range →* ↥(CFSG.EvenSporadicStandard.Induction.Cover.autFixing Kbar) :=
    f.range.subtype.codRestrict _ (fun x => hrange_le (hfrange x.2))
  have hg : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : ↥(CFSG.EvenSporadicStandard.Induction.Cover.autFixing Kbar) =>
      (z : MulAut (↥A ⧸ center ↥A))) hab
  have hE2 : IsPGroup 2 ↥g.range := by
    have hmap := (hrange2.to_subgroup (⊤ : Subgroup ↥f.range)).map g
    rw [← MonoidHom.range_eq_map] at hmap
    exact hmap
  have hEsq : ∀ x ∈ g.range, x * x = 1 := hfix2 _ hE2
  have hEcomm : ∀ x ∈ g.range, ∀ y ∈ g.range, x * y = y * x := by
    intro x hx y hy
    have hx2 := hEsq x hx
    have hy2 := hEsq y hy
    have hxy2 := hEsq (x * y) (g.range.mul_mem hx hy)
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy2).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [inv_eq_of_mul_eq_one_right hy2, inv_eq_of_mul_eq_one_right hx2]
  have hEcard : Nat.card ↥g.range ≤ 4 := hfix.elem _ hEsq hEcomm
  have hrangeLe : Nat.card ↥f.range ≤ 4 := by
    have hcard : Nat.card ↥g.range = Nat.card ↥f.range := by
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hg, Subgroup.card_top]
    rw [← hcard]
    exact hEcard
  calc Nat.card P = Nat.card ↥f.ker * Nat.card ↥f.range :=
        (Subgroup.card_ker_mul_card_range f).symm
    _ ≤ 2 * 4 := Nat.mul_le_mul hkerLe hrangeLe
    _ = 8 := by norm_num

theorem isSolvable_centralizer_inf_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) :
    Group.IsSolvable ↥(centralizer ({t} : Set G) ⊓ centralizer (K : Set G)) := by
  let M : Subgroup G := centralizer ({t} : Set G) ⊓ centralizer (K : Set G)
  change Group.IsSolvable ↥M
  have hMN : M ≤ normalizer (A : Set G) := by
    intro m hm
    have hmCt : m ∈ centralizer ({t} : Set G) := (Subgroup.mem_inf.1 hm).1
    exact CFSG.Open.standardComponentIsStandard.mem_normalizer_of_commute
      hS.standard.standardComponentIsStandard hS.t_mem hS.orderOf_t
      (Subgroup.mem_centralizer_singleton_iff.1 hmCt)
  have hMK : M ≤ centralizer (K : Set G) := inf_le_right
  let φ := CFSG.normalizerToCenterQuotientAut A M hMN
  let Kbar : Subgroup (↥A ⧸ center ↥A) :=
    (K.subgroupOf A).map (QuotientGroup.mk' (center ↥A))
  have hrange_le : φ.range ≤ CFSG.EvenSporadicStandard.Induction.Cover.autFixing Kbar :=
    action_le_autFixing hMN hMK
  obtain ⟨hfix, -⟩ := autFixFacts_of_l34SuzOdd hS hD
  have hrangeSolv : Group.IsSolvable ↥φ.range := by
    have : Group.IsSolvable ↥(CFSG.EvenSporadicStandard.Induction.Cover.autFixing Kbar) :=
      hfix.solvable
    let f : ↥φ.range →* ↥(CFSG.EvenSporadicStandard.Induction.Cover.autFixing Kbar) :=
      φ.range.subtype.codRestrict _ (fun x => hrange_le x.2)
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      exact congrArg
        (fun z : ↥(CFSG.EvenSporadicStandard.Induction.Cover.autFixing Kbar) =>
          (z : MulAut (↥A ⧸ center ↥A))) hab
    exact Group.isSolvable_of_isSolvable_injective hf
  have hkerEq : φ.ker = (M ⊓ centralizer (A : Set G)).subgroupOf M :=
    CFSG.ker_normalizerToCenterQuotientAut hS.standard.1.1 hMN
  have hkerSolv : Group.IsSolvable ↥φ.ker := by
    have : Group.IsSolvable ↥(centralizer (A : Set G)) :=
      isSolvable_centralizer_of_l34SuzOdd hS
    let f : ↥φ.ker →* ↥(centralizer (A : Set G)) :=
      { toFun := fun x =>
          ⟨((x : M) : G), by
            have hx : (x : M) ∈ (M ⊓ centralizer (A : Set G)).subgroupOf M := by
              rw [← hkerEq]
              exact x.2
            exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(centralizer (A : Set G)) => (z : G)) hab
    exact Group.isSolvable_of_isSolvable_injective hf
  have hquotSolv : Group.IsSolvable (↥M ⧸ φ.ker) := by
    have : Group.IsSolvable ↥φ.range := hrangeSolv
    exact Group.isSolvable_of_isSolvable_injective
      (f := (QuotientGroup.quotientKerEquivRange φ).toMonoidHom)
      (QuotientGroup.quotientKerEquivRange φ).injective
  have : Group.IsSolvable ↥φ.ker := hkerSolv
  have : Group.IsSolvable (↥M ⧸ φ.ker) := hquotSolv
  exact Group.isSolvable_of_subgroup_quotient φ.ker

theorem card_le_eight_of_isPGroup_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) {P : Subgroup G}
    (hP : P ≤ centralizer ({t} : Set G) ⊓ centralizer (K : Set G)) (h2 : IsPGroup 2 P) :
    Nat.card P ≤ 8 := by
  let M : Subgroup G := centralizer ({t} : Set G) ⊓ centralizer (K : Set G)
  change P ≤ M at hP
  have hMN : M ≤ normalizer (A : Set G) := by
    intro m hm
    have hmCt : m ∈ centralizer ({t} : Set G) := (Subgroup.mem_inf.1 hm).1
    exact CFSG.Open.standardComponentIsStandard.mem_normalizer_of_commute
      hS.standard.standardComponentIsStandard hS.t_mem hS.orderOf_t
      (Subgroup.mem_centralizer_singleton_iff.1 hmCt)
  have hMK : M ≤ centralizer (K : Set G) := inf_le_right
  obtain ⟨hfix, hfix2⟩ := autFixFacts_of_l34SuzOdd hS hD
  exact card_le_eight_of_action hS hMN hMK hfix hfix2 hP h2

theorem mul_self_eq_one_of_isPGroup_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) {P : Subgroup G}
    (hP : P ≤ centralizer ({t} : Set G) ⊓ centralizer (K : Set G)) (h2 : IsPGroup 2 P) :
    ∀ x ∈ P, x * x = 1 := by
  let M : Subgroup G := centralizer ({t} : Set G) ⊓ centralizer (K : Set G)
  change P ≤ M at hP
  let E : Subgroup G := V ⊔ zpowers t
  have hEM : E ≤ M := sup_zpowers_le_centralizer_inf_of_l34SuzOdd hS hD
  have hEcard : Nat.card E = 8 := card_sup_zpowers_of_l34SuzOdd hS hD
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hS.orderOf_t] at h
    simpa [pow_two] using h
  have hEcomm : ∀ a ∈ V, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    have ht : t ∈ centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subgroup.mem_centralizer_iff.1 hS.t_mem v (hD.le_A hv)
    have hb' : b ∈ centralizer (V : Set G) := (Subgroup.zpowers_le.mpr ht) hb
    exact Subgroup.mem_centralizer_iff.1 hb' a ha
  have hEsq : ∀ z ∈ E, z * z = 1 := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hEcomm hz
    have ha2 : a * a = 1 := hD.mul_self a ha
    have hb2 : b * b = 1 := by
      rcases (CFSG.Semidihedral.OddCentralizerSylowTwo.mem_zpowers_involution t
        hS.orderOf_t b).1 hb with rfl | rfl
      · simp
      · exact ht2
    have hab : a * b = b * a := hEcomm a ha b hb
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, mul_one]
  let EM : Subgroup ↥M := E.subgroupOf M
  have hEMcard : Nat.card EM = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv, hEcard]
  have hEM2 : IsPGroup 2 EM := IsPGroup.of_card (n := 3) (by rw [hEMcard]; norm_num)
  let Esyl : Sylow 2 ↥M :=
    { toSubgroup := EM
      isPGroup' := hEM2
      is_maximal' := by
        intro Q hQ hEQ
        have hQ2 : IsPGroup 2 (Q.map M.subtype) := hQ.map M.subtype
        have hQM : Q.map M.subtype ≤ M := by
          rintro _ ⟨q, -, rfl⟩
          exact q.2
        have hbound := card_le_eight_of_isPGroup_of_l34SuzOdd hS hD hQM hQ2
        have hQle : Nat.card Q ≤ 8 := by
          rw [← Subgroup.card_map_of_injective M.subtype_injective]
          exact hbound
        have hQge : 8 ≤ Nat.card Q := by
          calc 8 = Nat.card EM := hEMcard.symm
            _ ≤ Nat.card Q := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hEQ)
        have hQcard : Nat.card Q = 8 := le_antisymm hQle hQge
        exact (Subgroup.eq_of_le_of_card_ge hEQ (by rw [hQcard, hEMcard])).symm }
  have hPM2 : IsPGroup 2 (P.subgroupOf M) :=
    h2.of_equiv (Subgroup.subgroupOfEquivOfLe hP).symm
  obtain ⟨Q, hPQ⟩ := hPM2.exists_le_sylow
  let e : ↥Q ≃* ↥E :=
    (Sylow.equiv Q Esyl).trans (Subgroup.subgroupOfEquivOfLe hEM)
  intro x hxP
  have hxPM : (⟨x, hP hxP⟩ : ↥M) ∈ P.subgroupOf M := hxP
  let z : ↥Q := ⟨⟨x, hP hxP⟩, hPQ hxPM⟩
  have hzz : z * z = 1 := by
    apply e.injective
    rw [map_mul, map_one]
    exact Subtype.ext (hEsq (e z) (e z).2)
  have hMxx : (⟨x, hP hxP⟩ : ↥M) * ⟨x, hP hxP⟩ = 1 :=
    congrArg Subtype.val hzz
  exact congrArg (fun w : ↥M => (w : G)) hMxx

end Certificates

end CFSG.ComponentClassification.GrSLit.L34Sec5S
