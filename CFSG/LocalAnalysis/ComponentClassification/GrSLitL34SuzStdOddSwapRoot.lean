module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddSwapAction
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Rank
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.GroupTheory.SteinbergCBFTSCNRank

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {t y : G}

omit [Finite G] in
private theorem le_A_of_l34SuzOdd (hD : L34SuzOddData A V K y) : K ≤ A := by
  rw [hD.K_eq]
  exact (Subgroup.commutator_le_self _).trans inf_le_left

omit [Finite G] in
private theorem centralizes_V_of_l34SuzOdd (hD : L34SuzOddData A V K y) :
    K ≤ centralizer (V : Set G) := by
  rw [hD.K_eq]
  exact (Subgroup.commutator_le_self _).trans inf_le_right

omit [Finite G] in
private theorem isQuasisimple_of_isComponent_of_l34SuzOdd {P : Subgroup G} {u : G}
    (hPu : P ≤ centralizer ({u} : Set G))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({u} : Set G)))) :
    CFSG.IsQuasisimple ↥P :=
  (CFSG.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hPu)).mp hcomp.1

omit [Finite G] in
private theorem root_commutator_mem_centralizer {P : Subgroup G} {t v : G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hvt : v * t = t * v) (hvK : v ∈ centralizer ((HarrisLit.swapDiag P t hc).range : Set G))
    (hPperf : Group.IsPerfect ↥P) (hvP : P.map (MulAut.conj v).toMonoidHom =
      P.map (MulAut.conj t).toMonoidHom) (ht2 : t ^ 2 = 1) :
    t * v ∈ centralizer (P : Set G) :=
  HarrisLit.mul_mem_centralizer_of_map_conj_eq_map ht2 hc hPperf hvP hvt hvK

theorem exists_root_involution_of_l34SuzOdd
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) (hu1 : u ≠ 1)
    {P : Subgroup G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hPu : P ≤ centralizer ({u} : Set G))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({u} : Set G))))
    (hne : P.map (MulAut.conj t).toMonoidHom ≠ P) (hK : K = (HarrisLit.swapDiag P t hc).range) :
    ∃ a ∈ P, a * a = 1 ∧ t * a * t⁻¹ ≠ a := by
  by_contra hcon
  push Not at hcon
  have huV : u ∈ V := hu
  have hu_ne : u ≠ 1 := hu1
  have hKA : K ≤ A := le_A_of_l34SuzOdd hD
  have hPQ : CFSG.IsQuasisimple ↥P := isQuasisimple_of_isComponent_of_l34SuzOdd hPu hcomp
  have ht2 : t ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [hS.orderOf_t] at h
  have htP : t ∉ P := by
    intro ht
    apply hne
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ht)
  obtain ⟨e⟩ := CFSG.OddStandard.HigherRank.F3.nonempty_quotCenter_equiv_swapDiag hc hPQ
  rw [← hK] at e
  have hcard : Nat.card (↥P ⧸ center ↥P) = 20160 := by
    calc Nat.card (↥P ⧸ center ↥P) = Nat.card (↥K ⧸ center ↥K) := Nat.card_congr e.toEquiv
      _ = 20160 := CFSG.ComponentClassification.CatLeaf.card_of_isL34Type hD.l34
  have h2dvd : 2 ∣ Nat.card ↥P := by
    have hdvd : Nat.card (↥P ⧸ center ↥P) ∣ Nat.card ↥P :=
      Subgroup.card_quotient_dvd_card (center ↥P)
    rw [hcard] at hdvd
    exact (by norm_num : 2 ∣ 20160).trans hdvd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 2 h2dvd
  have hZstar : Open.fusionZStar ↥P = center ↥P :=
    CFSG.OddStandard.HigherRank.F3.fusionZStar_eq_center_of_involution hPQ hy
  let eZ : (↥P ⧸ Open.fusionZStar ↥P) ≃* (↥P ⧸ center ↥P) :=
    QuotientGroup.quotientMulEquivOfEq hZstar
  have hL34 : IsL34Type (↥P ⧸ Open.fusionZStar ↥P) :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (e.symm.trans eZ.symm) hD.l34
  have h3 : 3 ≤ pRank 2 ↥P :=
    CFSG.ComponentClassification.GrSLit.GrS5.three_le_pRank_of_l34 hL34
  have h3top : 3 ≤ CFSG.pRank 2 ↥(⊤ : Subgroup ↥P) := by
    rw [CFSG.pRank_congr_of_mulEquiv (Subgroup.topEquiv (G := ↥P)) 2]
    exact h3
  obtain ⟨E, hE, hE3⟩ :=
    CFSG.GroupTheory.FT63ChII.exists_isElementaryAbelian_of_three_le_pRank
      (P := ↥P) (p := 2) (B := ⊤) h3top
  let E' : Subgroup ↥P := E.map (⊤ : Subgroup ↥P).subtype
  have hE' : IsElementaryAbelian 2 E' := hE.map (⊤ : Subgroup ↥P).subtype
  have hE'card : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective (⊤ : Subgroup ↥P))
  have hE'3 : 2 ^ 3 ≤ Nat.card E' := by rwa [hE'card]
  let F : Subgroup G := E'.map P.subtype
  have hEF : IsElementaryAbelian 2 F := hE'.map_subtype
  have hFcard : Nat.card F = Nat.card E' :=
    Subgroup.card_map_of_injective P.subtype_injective
  have hFP : F ≤ P := Subgroup.map_subtype_le E'
  have hF2 : IsPGroup 2 F := IsElementaryAbelian.isPGroup 2 ↥F
  have hFFix : ∀ x ∈ F, t * x * t⁻¹ = x := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    exact hcon (z : G) z.2 (by
      have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E') (z : ↥P) hz
      simpa [pow_two] using congrArg (fun w : ↥P => (w : G)) h)
  have hFPt : ∀ x ∈ F, x ∈ P.map (MulAut.conj t).toMonoidHom := by
    intro x hx
    refine ⟨x, hFP hx, ?_⟩
    exact hFFix x hx
  have hFK : F ≤ centralizer (K : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [hK] at hk
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hk
    rw [← hp, HarrisLit.swapDiag_apply]
    have hxp : x * (p : G) = (p : G) * x :=
      Subgroup.mem_centralizer_iff.1 (hc p.2) x (hFPt x hx)
    have hxpt : x * MulAut.conj t (p : G) = MulAut.conj t (p : G) * x :=
      (Subgroup.mem_centralizer_iff.1 (hc (hFP hx)) _ ⟨p, p.2, rfl⟩).symm
    calc ((p : G) * MulAut.conj t (p : G)) * x
        = (p : G) * (MulAut.conj t (p : G) * x) := by group
      _ = (p : G) * (x * MulAut.conj t (p : G)) := by rw [hxpt]
      _ = ((p : G) * x) * MulAut.conj t (p : G) := by group
      _ = (x * (p : G)) * MulAut.conj t (p : G) := by rw [hxp]
      _ = x * ((p : G) * MulAut.conj t (p : G)) := by group
  have htK : t ∈ centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_iff.1 hS.t_mem k (hKA hk)
  have hsub : F ⊔ zpowers t ≤ centralizer ({t} : Set G) ⊓ centralizer (K : Set G) := by
    refine sup_le ?_ ?_
    · refine le_inf ?_ hFK
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * t = (t * x * t⁻¹) * t := by rw [hFFix x hx]
        _ = t * x := by group
    · refine le_inf ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      · exact Subgroup.zpowers_le.mpr htK
  have hz2 : IsPGroup 2 (zpowers t) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hS.orderOf_t]
    norm_num
  have hzF : zpowers t ≤ normalizer (F : Set G) := by
    refine (Subgroup.zpowers_le.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    calc x * t = (t * x * t⁻¹) * t := by rw [hFFix x hx]
      _ = t * x := by group
  have h2sup : IsPGroup 2 ↥(F ⊔ zpowers t) := by
    rw [sup_comm]
    exact IsPGroup.to_sup_of_normal_right' hz2 hF2 hzF
  have hdisj : Disjoint F (zpowers t) := by
    rw [disjoint_iff_inf_le]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxF : x ∈ F := hx.1
    have hxt : x ∈ zpowers t := hx.2
    rcases (CFSG.Semidihedral.OddCentralizerSylowTwo.mem_zpowers_involution t hS.orderOf_t x).1
      hxt with h | h
    · exact h
    · exact absurd (h ▸ hFP hxF) htP
  have hsupcard : Nat.card ↥(F ⊔ zpowers t) = Nat.card F * 2 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer F (zpowers t) hzF hdisj,
      Nat.card_zpowers, hS.orderOf_t]
  have hE8 : 8 ≤ Nat.card E' := by
    simpa using hE'3
  have h16 : 16 ≤ Nat.card ↥(F ⊔ zpowers t) := by
    rw [hsupcard, hFcard]
    calc 16 = 8 * 2 := by norm_num
      _ ≤ Nat.card E' * 2 := Nat.mul_le_mul_right 2 hE8
  have hle := card_le_eight_of_isPGroup_of_l34SuzOdd hS hD hsub h2sup
  omega

theorem root_identities_of_l34SuzOdd (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) {P : Subgroup G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hPu : P ≤ centralizer ({u} : Set G))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({u} : Set G))))
    (hK : K = (HarrisLit.swapDiag P t hc).range) {v : G} (hv : v ∈ V)
    (hvP : P.map (MulAut.conj v).toMonoidHom = P.map (MulAut.conj t).toMonoidHom) {a : G}
    (haP : a ∈ P) (ha : a * a = 1) (hat : t * a * t⁻¹ ≠ a) {d : G}
    (hd : d = a * (t * a * t⁻¹)) :
    d ∈ K ∧ d ≠ 1 ∧ d * d = 1 ∧ a * u * a⁻¹ = u ∧ a * t * a⁻¹ = d * t ∧
      a * v * a⁻¹ = d * v ∧ a * d * a⁻¹ = d := by
  have huV : u ∈ V := hu
  have hu_ne : u ≠ 1 := hu1
  have hPK : CFSG.IsQuasisimple ↥P := isQuasisimple_of_isComponent_of_l34SuzOdd hPu hcomp
  have hPperf : Group.IsPerfect ↥P := hPK.1
  have hKV : K ≤ centralizer (V : Set G) := centralizes_V_of_l34SuzOdd hD
  have ht2pow : t ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [hS.orderOf_t] at h
  have ht2 : t * t = 1 := by simpa [pow_two] using ht2pow
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hdK : d ∈ K := by
    rw [hK]
    refine ⟨⟨a, haP⟩, ?_⟩
    rw [HarrisLit.swapDiag_apply]
    exact hd.symm
  have hd1 : d ≠ 1 := by
    intro hd1
    apply hat
    have hmul : a * (t * a * t⁻¹) = 1 := by rw [← hd]; exact hd1
    have h := inv_eq_of_mul_eq_one_right hmul
    rw [hainv] at h
    exact h.symm
  have haT : (t * a * t⁻¹) * (t * a * t⁻¹) = 1 := by
    calc (t * a * t⁻¹) * (t * a * t⁻¹) = t * (a * a) * t⁻¹ := by group
      _ = 1 := by rw [ha]; group
  have hcommT : a * (t * a * t⁻¹) = (t * a * t⁻¹) * a :=
    (Subgroup.mem_centralizer_iff.1 (hc haP) _ ⟨a, haP, rfl⟩).symm
  have hd2 : d * d = 1 := by
    rw [hd]
    calc (a * (t * a * t⁻¹)) * (a * (t * a * t⁻¹))
        = a * ((t * a * t⁻¹) * a) * (t * a * t⁻¹) := by group
      _ = a * (a * (t * a * t⁻¹)) * (t * a * t⁻¹) := by rw [← hcommT]
      _ = (a * a) * ((t * a * t⁻¹) * (t * a * t⁻¹)) := by group
      _ = 1 := by rw [ha, haT, one_mul]
  have hcommau : a * u = u * a :=
    Subgroup.mem_centralizer_singleton_iff.mp (hPu haP)
  have hu' : a * u * a⁻¹ = u := by
    rw [hcommau]
    group
  have hat' : a * t * a⁻¹ = d * t := by
    rw [hainv, hd]
    group
  have hvt : v * t = t * v :=
    Subgroup.mem_centralizer_iff.1 hS.t_mem v (hD.le_A hv)
  have hvK : v ∈ centralizer ((HarrisLit.swapDiag P t hc).range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxK : x ∈ K := hK ▸ hx
    exact (Subgroup.mem_centralizer_iff.1 (hKV hxK) v hv).symm
  have htv : t * v ∈ centralizer (P : Set G) :=
    root_commutator_mem_centralizer hc hvt hvK hPperf hvP ht2pow
  have hconj : v * a * v⁻¹ = t * a * t⁻¹ := by
    have h0 : a * (t * v) = (t * v) * a :=
      Subgroup.mem_centralizer_iff.1 htv a haP
    have h1 : (t * v) * a * (t * v)⁻¹ = a := by
      rw [← h0]
      group
    have h2 : t * (v * a * v⁻¹) * t⁻¹ = a := by
      calc t * (v * a * v⁻¹) * t⁻¹ = (t * v) * a * (t * v)⁻¹ := by group
        _ = a := h1
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    calc v * a * v⁻¹ = t⁻¹ * (t * (v * a * v⁻¹) * t⁻¹) * t := by group
      _ = t⁻¹ * a * t := by rw [h2]
      _ = t * a * t⁻¹ := by rw [htinv]
  have hav : a * v * a⁻¹ = d * v := by
    rw [hainv]
    calc a * v * a = a * (v * a * v⁻¹) * v := by group
      _ = a * (t * a * t⁻¹) * v := by rw [hconj]
      _ = d * v := by rw [hd]
  have had : a * d * a⁻¹ = d := by
    rw [hainv, hd]
    calc a * (a * (t * a * t⁻¹)) * a
        = (a * a) * ((t * a * t⁻¹) * a) := by group
      _ = a * (t * a * t⁻¹) := by rw [ha, one_mul, hcommT]
  exact ⟨hdK, hd1, hd2, hu', hat', hav, had⟩

theorem conj_eq_or_eq_mul_of_l34SuzOdd
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) {P : Subgroup G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hPu : P ≤ centralizer ({u} : Set G))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({u} : Set G))))
    (hne : P.map (MulAut.conj t).toMonoidHom ≠ P) (hK : K = (HarrisLit.swapDiag P t hc).range)
    {v : G} (hv : v ∈ V)
    (hvP : P.map (MulAut.conj v).toMonoidHom = P.map (MulAut.conj t).toMonoidHom) {a : G}
    (haP : a ∈ P) (ha : a * a = 1) {r : G} (hrK : r ∈ K)
    (hrd : r * (a * (t * a * t⁻¹)) = a * (t * a * t⁻¹) * r) (hra : a * r * a⁻¹ ∈ A) :
    a * r * a⁻¹ = r ∨ a * r * a⁻¹ = u * r := by
  have hKA : K ≤ A := le_A_of_l34SuzOdd hD
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hrR : r ∈ (HarrisLit.swapDiag P t hc).range := hK ▸ hrK
  obtain ⟨p, hpr⟩ := MonoidHom.mem_range.mp hrR
  let cP : ↥P := ⟨a, haP⟩ * p * ⟨a, haP⟩⁻¹ * p⁻¹
  have hq_mem : MulAut.conj t (p : G) ∈ P.map (MulAut.conj t).toMonoidHom :=
    ⟨p, p.2, rfl⟩
  have ha_q : a * MulAut.conj t (p : G) = MulAut.conj t (p : G) * a :=
    (Subgroup.mem_centralizer_iff.1 (hc haP) _ hq_mem).symm
  have hp_q : (p : G) * MulAut.conj t (p : G) = MulAut.conj t (p : G) * (p : G) :=
    (Subgroup.mem_centralizer_iff.1 (hc p.2) _ hq_mem).symm
  have hq_inv : MulAut.conj t (p : G) * a⁻¹ = a⁻¹ * MulAut.conj t (p : G) :=
    (Commute.inv_left ha_q).symm.eq
  have hcPval : (cP : G) = a * r * a⁻¹ * r⁻¹ := by
    have hc0 : (cP : G) = a * (p : G) * a⁻¹ * (p : G)⁻¹ := rfl
    rw [hc0, ← hpr, HarrisLit.swapDiag_apply, mul_inv_rev]
    calc a * (p : G) * a⁻¹ * (p : G)⁻¹
        = a * (p : G) * (a⁻¹ * MulAut.conj t (p : G) *
            (MulAut.conj t (p : G))⁻¹) * (p : G)⁻¹ := by group
      _ = a * (p : G) * (MulAut.conj t (p : G) * a⁻¹ *
            (MulAut.conj t (p : G))⁻¹) * (p : G)⁻¹ := by rw [← hq_inv]
      _ = a * ((p : G) * MulAut.conj t (p : G)) * a⁻¹ *
            ((MulAut.conj t (p : G))⁻¹ * (p : G)⁻¹) := by group
  have hdelta : HarrisLit.swapDiag P t hc cP = 1 := by
    have hDmap : HarrisLit.swapDiag P t hc cP =
        HarrisLit.swapDiag P t hc ⟨a, haP⟩ * HarrisLit.swapDiag P t hc p *
          (HarrisLit.swapDiag P t hc ⟨a, haP⟩)⁻¹ * (HarrisLit.swapDiag P t hc p)⁻¹ := by
      dsimp [cP]
      simp only [map_mul, map_inv]
    rw [hDmap]
    have hda : HarrisLit.swapDiag P t hc ⟨a, haP⟩ = a * (t * a * t⁻¹) := by
      rw [HarrisLit.swapDiag_apply]
      rfl
    rw [hda, hpr]
    have hdr : a * (t * a * t⁻¹) * r = r * (a * (t * a * t⁻¹)) := hrd.symm
    rw [hdr]
    group
  have hcZ : cP ∈ center ↥P :=
    CFSG.OddStandard.HigherRank.F3.ker_swapDiag_le_center hc (MonoidHom.mem_ker.mpr hdelta)
  have hcCent : (cP : G) ∈ centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hcZ ⟨x, hx⟩)
  have hca : (cP : G) * a = a * (cP : G) :=
    (congrArg Subtype.val (Subgroup.mem_center_iff.1 hcZ ⟨a, haP⟩)).symm
  have hc2 : (cP : G) * (cP : G) = 1 := by
    let y : G := (p : G) * a * (p : G)⁻¹
    have hy : y * y = 1 := by
      dsimp [y]
      calc ((p : G) * a * (p : G)⁻¹) * ((p : G) * a * (p : G)⁻¹)
          = (p : G) * (a * a) * (p : G)⁻¹ := by group
        _ = 1 := by rw [ha]; group
    have hcy : (cP : G) = a * y := by
      change ((⟨a, haP⟩ : ↥P) : G) * (p : G) * (((⟨a, haP⟩ : ↥P) : G))⁻¹ *
          (p : G)⁻¹ = a * ((p : G) * a * (p : G)⁻¹)
      rw [hainv]
      group
    have hay : a * y = y * a := by
      have h1 : (a * y) * a = a * (a * y) := by rw [← hcy]; exact hca
      have h1' : (a * y) * a = y := by
        calc (a * y) * a = a * (a * y) := h1
          _ = (a * a) * y := by group
          _ = y := by rw [ha, one_mul]
      calc a * y = (a * y) * (a * a) := by rw [ha, mul_one]
        _ = ((a * y) * a) * a := by group
        _ = y * a := by rw [h1']
    rw [hcy]
    calc (a * y) * (a * y) = (a * y) * (y * a) := by rw [hay]
      _ = a * (y * y) * a := by group
      _ = 1 := by rw [hy, mul_one, ha]
  have hcA : (cP : G) ∈ A := by
    rw [hcPval]
    exact Subgroup.mul_mem A hra (Subgroup.inv_mem A (hKA hrK))
  have hcE : (cP : G) ∈ V ⊔ zpowers t :=
    mem_sup_zpowers_of_mem_center_of_l34SuzOdd hS hD hu hu1 hc hPu hcomp hK cP.2 hcCent hc2
  have hcV : (cP : G) ∈ V := mem_of_mem_sup_zpowers_of_mem_of_l34SuzOdd hS hD hcE hcA
  have hcPmap : P.map (MulAut.conj (cP : G)).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer (P : Set G) hcCent)
  have hcase := eq_one_or_eq_of_map_conj_eq_of_l34SuzOdd hS hD hu hu1 hPu hne hv hvP hcV hcPmap
  have hmain : a * r * a⁻¹ = (cP : G) * r := by
    rw [hcPval]
    group
  rcases hcase with h | h
  · left
    rw [hmain, h, one_mul]
  · right
    rw [hmain, h]

end CFSG.ComponentClassification.GrSLit.L34Sec5S
