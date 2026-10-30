module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma93
public import CFSG.LocalAnalysis.GLTheoremA.S9.L94Core
public import CFSG.LocalAnalysis.GLTheoremA.S9.L94Quot
public import CFSG.LocalAnalysis.GLTheoremA.S9.L94Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S9

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def IsDirectZpowersInf (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  B = Subgroup.zpowers x ⊔ (B ⊓ L) ∧ Subgroup.zpowers x ⊓ (B ⊓ L) = ⊥

structure Lemma94Inputs (G : Type) [Group G] [Finite G] : Prop where
  l93 : Lemma93Inputs G 3
  lbal : LBalanceAt G 3
  i269 : I269At G
  i117 : I117At G
  rank23 : Rank23At G
  hy : L94TypeHyAt G

theorem catalogIs_mono {S : Type} [Group S] {Q Q' : TauCeti.CFSGIndex → Prop}
    (hQ : ∀ i, Q i → Q' i) (h : catalogIs S Q) : catalogIs S Q' := by
  obtain ⟨i, hi, f⟩ := h
  exact ⟨i, hQ i hi, f⟩

private theorem l94_mem_sup_of_normalizes {Y E : Subgroup G} (hYE : E ≤ Subgroup.normalizer (Y : Set G)) :
    ∀ g ∈ Y ⊔ E, ∃ y ∈ Y, ∃ e ∈ E, g = y * e := by
  let S : Subgroup G :=
    { carrier := {g | ∃ y ∈ Y, ∃ e ∈ E, g = y * e}
      mul_mem' := by
        rintro _ _ ⟨y1, hy1, e1, he1, rfl⟩ ⟨y2, hy2, e2, he2, rfl⟩
        have h2 : e1 * y2 * e1⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.1 (hYE he1) y2).1 hy2
        exact ⟨y1 * (e1 * y2 * e1⁻¹), Y.mul_mem hy1 h2, e1 * e2, E.mul_mem he1 he2, by group⟩
      one_mem' := ⟨1, Y.one_mem, 1, E.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨y, hy, e, he, rfl⟩
        have h2 : e⁻¹ * y⁻¹ * e⁻¹⁻¹ ∈ Y :=
          (Subgroup.mem_normalizer_iff.1 (hYE (E.inv_mem he)) y⁻¹).1 (Y.inv_mem hy)
        exact ⟨e⁻¹ * y⁻¹ * e⁻¹⁻¹, h2, e⁻¹, E.inv_mem he, by group⟩ }
  have hle : Y ⊔ E ≤ S :=
    sup_le (fun y hy => ⟨y, hy, 1, E.one_mem, by simp⟩) (fun e he => ⟨1, Y.one_mem, e, he, by simp⟩)
  intro g hg
  exact hle hg

private theorem l94_conj_mem_centralizer {D : Subgroup G} {e : G} (he : ∀ d ∈ D, e * d = d * e)
    {y : G} (hy : y ∈ Subgroup.centralizer (D : Set G)) :
    e * y * e⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro d hd
  have hd' : e⁻¹ * d = d * e⁻¹ := by
    calc e⁻¹ * d = e⁻¹ * (d * e) * e⁻¹ := by group
      _ = e⁻¹ * (e * d) * e⁻¹ := by rw [he d hd]
      _ = d * e⁻¹ := by group
  calc d * (e * y * e⁻¹) = (d * e) * y * e⁻¹ := by group
    _ = (e * d) * y * e⁻¹ := by rw [← he d hd]
    _ = e * (d * y) * e⁻¹ := by group
    _ = e * (y * d) * e⁻¹ := by rw [hy d hd]
    _ = e * y * (d * e⁻¹) := by group
    _ = e * y * (e⁻¹ * d) := by rw [hd']
    _ = (e * y * e⁻¹) * d := by group

private theorem l94_fwd {L E : Subgroup G} {g : G} (hgL : g ∈ Subgroup.normalizer (L : Set G))
    (hgC : g ∈ Subgroup.centralizer (E : Set G)) {y : G}
    (hy : y ∈ L ⊓ Subgroup.centralizer (E : Set G)) :
    g * y * g⁻¹ ∈ L ⊓ Subgroup.centralizer (E : Set G) := by
  have hC : ∀ e ∈ E, e * g = g * e := fun e he => Subgroup.mem_centralizer_iff.1 hgC e he
  refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hgL y).1 (Subgroup.mem_inf.1 hy).1,
    Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
  have hyE : e * y = y * e := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy).2 e he
  have hg' : e * g⁻¹ = g⁻¹ * e := by
    calc e * g⁻¹ = g⁻¹ * (g * e) * g⁻¹ := by group
      _ = g⁻¹ * (e * g) * g⁻¹ := by rw [hC e he]
      _ = g⁻¹ * e := by group
  calc e * (g * y * g⁻¹) = (e * g) * y * g⁻¹ := by group
    _ = (g * e) * y * g⁻¹ := by rw [hC e he]
    _ = g * (e * y) * g⁻¹ := by group
    _ = g * (y * e) * g⁻¹ := by rw [hyE]
    _ = g * y * (e * g⁻¹) := by group
    _ = g * y * (g⁻¹ * e) := by rw [hg']
    _ = (g * y * g⁻¹) * e := by group

private theorem l94_normalizes_inf {L E : Subgroup G} {g : G} (hgL : g ∈ Subgroup.normalizer (L : Set G))
    (hgC : g ∈ Subgroup.centralizer (E : Set G)) :
    g ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact l94_fwd hgL hgC hy
  · intro hy
    have h2 := l94_fwd (inv_mem hgL) (inv_mem hgC) hy
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e] at h2

theorem notIsGB_of_I269 (hc : S9Ctx G 3) (hLB : LBalanceAt G 3) (h269 : I269At G) {B : Subgroup G}
    {x : G} {L : Subgroup G} (h : H92 3 B x L) (hL : catalogIs (PSimple 3 L) isList269) :
    ¬ IsGB 3 B L := by
  rintro ⟨E, hEB, hEel, hEcard, hEN, hLay⟩
  have hp3 : Nat.Prime 3 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hBel : IsElemAbelian 3 B := h.bmax.1
  have hBC : B ≤ cx x := isElemAbelian_le_centralizer hBel h.mem
  have hEC : E ≤ cx x := hEB.trans hBC
  have hLC : L ≤ cx x := h.comp.1
  have hE3 : IsPGroup 3 E := isPGroup_of_isElemAbelian hEel
  have hx3 : orderOf x = 3 := orderOf_eq_prime (hBel.2 x h.mem) h.ne_one
  have hMx : E ⊓ centModSubgroup 3 L ≤ Subgroup.zpowers x := fun e he =>
    (h.cent e (hEB (Subgroup.mem_inf.1 he).1)).1 (centMod_iff.2 (Subgroup.mem_inf.1 he).2)
  have hMcard : Nat.card ↥(E ⊓ centModSubgroup 3 L) ∣ 3 := by
    have := Subgroup.card_dvd_of_le hMx
    rwa [Nat.card_zpowers, hx3] at this
  obtain ⟨D, hDE, hDel, hDcard⟩ : ∃ D : Subgroup G, D ≤ E ∧ IsElemAbelian 3 D ∧
      Nat.card D = 3 ^ 2 * Nat.card ↥(D ⊓ centModSubgroup 3 L) := by
    rcases (Nat.dvd_prime hp3).1 hMcard with h1 | h1
    · have hdvd : 3 ^ 2 ∣ Nat.card ↥E := by
        rw [hEcard]
        exact pow_dvd_pow 3 (by norm_num)
      obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) 3 hdvd
      have hDE : K.map E.subtype ≤ E := Subgroup.map_subtype_le K
      have hMbot : E ⊓ centModSubgroup 3 L = ⊥ := Subgroup.card_eq_one.1 h1
      have hDbot : K.map E.subtype ⊓ centModSubgroup 3 L = ⊥ := by
        apply le_bot_iff.1
        rw [← hMbot]
        exact inf_le_inf_right _ hDE
      refine ⟨K.map E.subtype, hDE, isElemAbelian_mono hEel hDE, ?_⟩
      rw [hDbot, Subgroup.card_bot, Subgroup.card_map_of_injective (Subgroup.subtype_injective E), hK]
      norm_num
    · exact ⟨E, le_rfl, hEel, by rw [hEcard, h1]; norm_num⟩
  have hDN : D ≤ Subgroup.normalizer (L : Set G) := hDE.trans hEN
  have hLD : GLAPLayer 3 (L ⊓ Subgroup.centralizer (D : Set G)) = ⊥ :=
    h269 (cx x) L D (isKGroup_cx hc h.ne_one) h.comp hL hDel hDN hDcard
  set Y : Subgroup G := L ⊓ Subgroup.centralizer (D : Set G) with hYdef
  have hEY : E ≤ Subgroup.normalizer (Y : Set G) := by
    intro e he
    have hc1 : ∀ d ∈ D, e * d = d * e := fun d hd => isElemAbelian_commute hEel he (hDE hd)
    have hc2 : ∀ d ∈ D, e⁻¹ * d = d * e⁻¹ := fun d hd =>
      isElemAbelian_commute hEel (E.inv_mem he) (hDE hd)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hN := Subgroup.mem_normalizer_iff.1 (hEN he) y
    simp only [SetLike.mem_coe, hYdef, Subgroup.mem_inf]
    constructor
    · rintro ⟨hyL, hyC⟩
      exact ⟨hN.1 hyL, l94_conj_mem_centralizer hc1 hyC⟩
    · rintro ⟨hyL', hyC'⟩
      refine ⟨hN.2 hyL', ?_⟩
      have h3 := l94_conj_mem_centralizer hc2 hyC'
      have e2 : e⁻¹ * (e * y * e⁻¹) * e⁻¹⁻¹ = y := by group
      rwa [e2] at h3
  set X : Subgroup G := Y ⊔ E with hXdef
  have hYX : Y ≤ X := le_sup_left
  have hEX : E ≤ X := le_sup_right
  have hXC : X ≤ cx x := sup_le (inf_le_left.trans hLC) hEC
  have hXL : X ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (inf_le_left.trans Subgroup.le_normalizer) hEN
  have hXN : X ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hEY
  have hXK : CFSG.Open.IsKGroup ↥X := CFSG.Open.IsKGroup.of_le (isKGroup_cx hc h.ne_one) hXC
  have hYnorm : (Y.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).2 hXN
  have hbal : GLAPLayer 3 (X ⊓ Subgroup.centralizer (E : Set G)) ≤ GLAPLayer 3 X :=
    hLB X E hXK hEX hE3
  have hcompY : ∀ K : Subgroup G, GLAPComponent 3 X K → K ≤ Y := by
    intro K hK
    let φ : ↥X →* ↥X ⧸ (Y.subgroupOf X) := QuotientGroup.mk' (Y.subgroupOf X)
    have hQ3 : IsPGroup 3 (↥X ⧸ (Y.subgroupOf X)) := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨y, hy, e, he, hge⟩ := l94_mem_sup_of_normalizes hEY (g : G) g.2
      obtain ⟨k, hk⟩ := hE3 ⟨e, he⟩
      refine ⟨k, ?_⟩
      have hpow : (⟨e, hEX he⟩ : ↥X) ^ 3 ^ k = 1 := by
        apply Subtype.ext
        have := congrArg Subtype.val hk
        simpa using this
      have hyX : (⟨y, hYX hy⟩ : ↥X) ∈ Y.subgroupOf X := Subgroup.mem_subgroupOf.2 hy
      have hgeq : g = ⟨y, hYX hy⟩ * ⟨e, hEX he⟩ := Subtype.ext hge
      have hy1 : QuotientGroup.mk' (Y.subgroupOf X) (⟨y, hYX hy⟩ : ↥X) = 1 :=
        (QuotientGroup.eq_one_iff _).2 hyX
      have hφg : φ g = φ ⟨e, hEX he⟩ := by
        show QuotientGroup.mk' (Y.subgroupOf X) g = QuotientGroup.mk' (Y.subgroupOf X) ⟨e, hEX he⟩
        rw [hgeq, map_mul, hy1, one_mul]
      show φ g ^ 3 ^ k = 1
      rw [hφg, ← map_pow, hpow, map_one]
    haveI := hQ3.isNilpotent
    haveI : Group.IsSolvable (↥X ⧸ (Y.subgroupOf X)) := inferInstance
    have hKX : K ≤ X := hK.1
    have hKxperf : ⁅K.subgroupOf X, K.subgroupOf X⁆ = K.subgroupOf X := by
      have h1 : ⁅K, K⁆ = K := glaPComponent_perfect hK
      have h2 := subgroupOf_commutator hKX hKX
      rw [h1] at h2
      exact h2.symm
    have hKqperf : ⁅(K.subgroupOf X).map φ, (K.subgroupOf X).map φ⁆ = (K.subgroupOf X).map φ := by
      rw [← Subgroup.map_commutator, hKxperf]
    have hKq1 : (K.subgroupOf X).map φ = ⊥ := by
      by_contra hne
      haveI : Nontrivial ↥((K.subgroupOf X).map φ) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
      haveI : Group.IsPerfect ↥((K.subgroupOf X).map φ) := Subgroup.isPerfect_iff.2 hKqperf
      exact Group.IsPerfect.not_isSolvable (G := ↥((K.subgroupOf X).map φ)) inferInstance
    intro k hk
    have hmem : φ ⟨k, hKX hk⟩ ∈ (K.subgroupOf X).map φ :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hk)
    rw [hKq1, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hmem)
  have hlayX : GLAPLayer 3 X ≤ GLAPLayer 3 Y :=
    sSup_le fun K hK => le_sSup (glaPComponent_of_le hp3 hK (hcompY K hK) hYX)
  have hLE : GLAPLayer 3 (L ⊓ Subgroup.centralizer (E : Set G)) ≤
      GLAPLayer 3 (X ⊓ Subgroup.centralizer (E : Set G)) := by
    refine sSup_le fun K hK => le_sSup ?_
    refine glaPComponent_of_isSubnormal' hp3 ?_ hK
    have hCE : Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer (D : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hDE)
    have hle : L ⊓ Subgroup.centralizer (E : Set G) ≤ X ⊓ Subgroup.centralizer (E : Set G) :=
      le_inf ((inf_le_inf_left _ hCE).trans hYX) inf_le_right
    refine IsSubnormal.step hle ?_ (IsSubnormal.refl _)
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 ?_
    intro g hg
    exact l94_normalizes_inf (hXL (Subgroup.mem_inf.1 hg).1) (Subgroup.mem_inf.1 hg).2
  have hL0 : GLAPLayer 3 (L ⊓ Subgroup.centralizer (E : Set G)) ≤ ⊥ :=
    hLE.trans (hbal.trans (hlayX.trans hLD.le))
  exact hLay (le_bot_iff.1 hL0)

private theorem l94_card_le_of_normalizes_coprime_even {Q Y : Subgroup G} (hQ : IsElemAbelian 3 Q)
    (hQY : Q ≤ Subgroup.normalizer (Y : Set G)) (hY3 : ¬ 3 ∣ Nat.card Y)
    (hY2 : 2 ∣ Nat.card Y) : Nat.card Q ≤ 3 ^ GLATwoLocalRank 3 G := by
  obtain ⟨R, ⟨S, rfl⟩, -, hQR⟩ :=
    CFSG.ABGLocalTools.exists_invariant_isSylowOf_ge_of_coprime (q := 3) (r := 2)
      Nat.prime_three Nat.prime_two (isPGroup_of_isElemAbelian hQ) hQY hY3 bot_le
      IsPGroup.of_bot (fun g _ => Subgroup.mem_normalizer_iff.2 fun h => by
        simp only [SetLike.mem_coe, Subgroup.mem_bot]
        constructor <;> intro hh <;> simp_all)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : (S : Subgroup Y) ≠ ⊥ := S.ne_bot_of_dvd_card hY2
  refine card_le_pow_glaTwoLocalRank Nat.prime_three hQ ?_ (S.isPGroup'.map _) hQR
  intro h
  exact hS ((Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).1 h)

theorem decomp_of_inner (hc : S9Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} (h : H92 3 B x L)
    (hess : IsEssential 3 B x) (hodd : Odd (Nat.card (GLAPPrimeCoreOf 3 (cx x))))
    (hZ : Subgroup.center (PQuot 3 L) = ⊥) (hin : ∀ b ∈ B, InducesInnerMod 3 L b)
    (hy : ∃ y : PQuot 3 L, orderOf y = 3 ∧ ∃ W : Subgroup (PQuot 3 L), IsPGroup 2 W ∧
      W ≠ ⊥ ∧ y ∈ Subgroup.normalizer (W : Set (PQuot 3 L))) :
    IsDirectZpowersInf B x L := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold IsDirectZpowersInf
  have hBel : IsElemAbelian 3 B := h.bmax.1
  have hB3 : IsPGroup 3 B := isPGroup_of_isElemAbelian hBel
  have hxB : x ∈ B := h.mem
  have hBX : B ≤ cx x := isElemAbelian_le_centralizer hBel hxB
  have hLX : L ≤ cx x := h.comp.1
  have hLsn : IsSubnormal L (cx x) := h.comp.2.1
  have hxX : x ∈ cx x := Subgroup.mem_centralizer_singleton_iff.2 (Commute.refl x)
  have hxc : ∀ w ∈ cx x, w * x = x * w := fun w hw => Subgroup.mem_centralizer_singleton_iff.1 hw
  have hx3 : orderOf x = 3 := orderOf_eq_prime (hBel.2 x hxB) h.ne_one
  have hOcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 (cx x))) :=
    (Nat.Prime.coprime_iff_not_dvd hp3).2 (not_dvd_card_glaPPrimeCoreOf hp3 (cx x))
  have hBO : B ⊓ GLAPPrimeCoreOf 3 (cx x) = ⊥ := by
    have hcopB : Nat.Coprime (Nat.card B) (Nat.card (GLAPPrimeCoreOf 3 (cx x))) := by
      rw [h.bmax.2.1]
      exact Nat.Coprime.pow_left _ hOcop
    have h1 := Nat.eq_one_of_dvd_coprimes hcopB (Subgroup.card_dvd_of_le inf_le_left)
      (Subgroup.card_dvd_of_le inf_le_right)
    exact Subgroup.card_eq_one.1 h1
  obtain ⟨-, -, T₀, hT₀C, hT₀2, hBT₀, hne, -⟩ := hess
  obtain ⟨hTT₀, hT'2, hT'B, hdbl⟩ := l94t_commutator_facts hBel hT₀2 hBT₀
  have hT'X : ⁅T₀, B⁆ ≤ cx x := hTT₀.trans hT₀C
  have hBb_el : IsElemAbelian 3 (barX 3 (cx x) B) := l94t_isElemAbelian_barX hBel hBX
  have hBb_card : Nat.card (barX 3 (cx x) B) = Nat.card B := l94t_card_barX hBX hBO
  have hK : IsComponentOf (barX 3 (cx x) L) ⊤ := h.comp.2.2.1
  have hKs : IsSimpleGroup ↥(barX 3 (cx x) L) :=
    l94t_isSimple_barX hp3 hLX hLsn hZ (isQuasisimple_pQuot_of_glaPComponent hp3 h.comp)
  have hyK := l94t_transport_hy (quotEquivBarX hp3 hLX hLsn) hy
  have hBK : barX 3 (cx x) B ≤ Subgroup.normalizer ((barX 3 (cx x) L : Subgroup _) : Set _) :=
    l94t_barX_le_normalizer (p := 3) hLX h.norm
  have hinner := l94t_barX_le_sup_centralizer h hin
  have hxBb : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(cx x)) (⟨x, hxX⟩ : ↥(cx x)) ∈
      barX 3 (cx x) B :=
    ⟨⟨x, hxX⟩, Subgroup.mem_subgroupOf.2 hxB, rfl⟩
  have hxZ := l94t_central_mk (p := 3) hxX hxc
  have hBR := l94t_barX_inter_centralizer h
  have hT2b : IsPGroup 2 (barX 3 (cx x) ⁅T₀, B⁆) := l94t_isPGroup_barX hT'X hT'2
  have hTne : barX 3 (cx x) ⁅T₀, B⁆ ≠ ⊥ := l94t_barX_ne_bot hT'X hT'2 hne hodd
  have hBT : barX 3 (cx x) B ≤
      Subgroup.normalizer ((barX 3 (cx x) ⁅T₀, B⁆ : Subgroup _) : Set _) :=
    l94t_barX_le_normalizer (p := 3) hT'X hT'B
  have hTB : ⁅barX 3 (cx x) ⁅T₀, B⁆, barX 3 (cx x) B⁆ = barX 3 (cx x) ⁅T₀, B⁆ := by
    rw [← barX_commutator 3 hT'X hBX, hdbl]
  rcases l94_decomp_or_large (K := barX 3 (cx x) L) (Bb := barX 3 (cx x) B)
      (Tb := barX 3 (cx x) ⁅T₀, B⁆)
      (xb := QuotientGroup.mk' (GLAPPrimeCore 3 ↥(cx x)) (⟨x, hxX⟩ : ↥(cx x)))
      hK hKs hyK hBb_el hBK hinner hxBb hxZ hBR hT2b hTne hBT hTB with
    hdec | ⟨P, W, hP, hW2, hWne, hPW, hlt⟩
  ·
    have hYI : preimBarX 3 (cx x) L ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (le_preimBarX 3 hLX)).1
        (glaPComponent_normal_preimBarX h.comp)
    have hsupY := l94t_sup_eq_preimBarX (L := L) (X := cx x) hLX
    have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 (cx x)) := not_dvd_card_glaPPrimeCoreOf hp3 (cx x)
    have hxL : x ∉ L := l94t_x_not_mem_L h hZ
    have hsup : B = Subgroup.zpowers x ⊔ (B ⊓ L) := by
      have hzN : (Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(cx x))
          (⟨x, hxX⟩ : ↥(cx x)))).Normal := by
        refine ⟨fun n hn g => ?_⟩
        have hc : g * n = n * g := Subgroup.mem_center_iff.1 (Subgroup.zpowers_le.2 hxZ hn) g
        rw [hc, mul_inv_cancel_right]
        exact hn
      apply le_antisymm
      · intro b hb
        have hbBb : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(cx x)) (⟨b, hBX hb⟩ : ↥(cx x)) ∈
            barX 3 (cx x) B :=
          ⟨⟨b, hBX hb⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩
        rw [hdec] at hbBb
        obtain ⟨k, hk, z, hz, hkz⟩ := Subgroup.mem_sup_of_normal_right.1 hbBb
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hz
        have hzc : z ∈ Subgroup.center (↥(cx x) ⧸ GLAPPrimeCore 3 ↥(cx x)) :=
          Subgroup.zpowers_le.2 hxZ hz
        have hkz' : k * z = z * k := Subgroup.mem_center_iff.1 hzc k
        have hgB : x ^ (-i) * b ∈ B := B.mul_mem (B.zpow_mem hxB (-i)) hb
        have hgX : x ^ (-i) * b ∈ cx x := (cx x).mul_mem ((cx x).zpow_mem hxX (-i)) (hBX hb)
        have hπg : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(cx x))
            (⟨x ^ (-i) * b, hgX⟩ : ↥(cx x)) = k := by
          have e1 : (⟨x ^ (-i) * b, hgX⟩ : ↥(cx x)) =
              (⟨x, hxX⟩ : ↥(cx x)) ^ (-i) * ⟨b, hBX hb⟩ :=
            Subtype.ext (by simp)
          rw [e1, map_mul, map_zpow, ← hkz, hkz', ← hi]
          group
        have hkL : k ∈ barX 3 (cx x) L := (Subgroup.mem_inf.1 hk).2
        have hmemK : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(cx x))
            (⟨x ^ (-i) * b, hgX⟩ : ↥(cx x)) ∈ barX 3 (cx x) L := by
          rw [hπg]
          exact hkL
        have hgP : x ^ (-i) * b ∈ preimBarX 3 (cx x) L :=
          Subgroup.mem_map.2 ⟨⟨x ^ (-i) * b, hgX⟩, Subgroup.mem_comap.2 hmemK, rfl⟩
        have hyp : IsPGroup 3 (Subgroup.zpowers (x ^ (-i) * b)) :=
          hB3.to_le (Subgroup.zpowers_le.2 hgB)
        have hgL : x ^ (-i) * b ∈ L :=
          mem_of_isPGroup_of_sup_eq hp3 (le_preimBarX 3 hLX) hYI hN hsupY hgP hyp
        have hmem_sup : x ^ i * (x ^ (-i) * b) ∈ Subgroup.zpowers x ⊔ (B ⊓ L) :=
          Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers x i) (Subgroup.mem_inf.2 ⟨hgB, hgL⟩)
        rw [show b = x ^ i * (x ^ (-i) * b) by group]
        exact hmem_sup
      · exact sup_le (Subgroup.zpowers_le.2 hxB) inf_le_left
    have hdisj : Subgroup.zpowers x ⊓ (B ⊓ L) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
      obtain ⟨hyB, hyL⟩ := Subgroup.mem_inf.1 hy2
      rw [Subgroup.mem_bot]
      by_contra hy0
      have hy3 : orderOf y = 3 := orderOf_eq_prime (hBel.2 y hyB) hy0
      have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hy1
      have hcard : Nat.card (Subgroup.zpowers x) ≤ Nat.card (Subgroup.zpowers y) := by
        rw [Nat.card_zpowers, Nat.card_zpowers, hy3, hx3]
      have heq := Subgroup.eq_of_le_of_card_ge hle hcard
      have hxy : x ∈ Subgroup.zpowers y := by
        rw [heq]
        exact Subgroup.mem_zpowers x
      exact hxL (Subgroup.zpowers_le.2 hyL hxy)
    exact ⟨hsup, hdisj⟩
  ·
    exfalso
    have hle := l94_card_le_of_quot (C := cx x) hP hW2 hWne hPW
    rw [hBb_card, h.bmax.2.1] at hlt
    exact lt_irrefl _ (lt_of_lt_of_le hlt hle)

private theorem l94_le_of_subnormal_comm {X A : Subgroup G} (hA : IsSubnormal A X) :
    ∀ {I S : Subgroup G}, I ≤ A → S ≤ X → ⁅S, I⁆ = S → S ≤ A := by
  induction hA with
  | refl H =>
    intro I S _ hSX _
    exact hSX
  | step hAM hn hMX ih =>
    intro I S hI hSX hS
    have hSM := ih (hI.trans hAM) hSX hS
    have hNM := (Subgroup.normal_subgroupOf_iff_le_normalizer hAM).1 hn
    rw [← hS]
    refine Subgroup.commutator_le.2 fun s hs i hi => ?_
    have h1 : s * i * s⁻¹ ∈ _ :=
      (Subgroup.mem_normalizer_iff.1 (hNM (hSM hs)) i).1 (hI hi)
    rw [commutatorElement_def]
    exact _root_.Subgroup.mul_mem _ h1 (_root_.Subgroup.inv_mem _ (hI hi))

private theorem l94_mem_zpowers_mul {B L : Subgroup G} {x : G}
    (hxL : ∀ c ∈ L, Commute x c) (hsup : B = Subgroup.zpowers x ⊔ (B ⊓ L)) :
    ∀ b ∈ B, ∃ i : ℤ, ∃ c ∈ B ⊓ L, b = x ^ i * c := by
  let P : Subgroup G :=
    { carrier := {g | ∃ i : ℤ, ∃ c ∈ B ⊓ L, g = x ^ i * c}
      mul_mem' := by
        rintro _ _ ⟨i, c, hc, rfl⟩ ⟨j, d, hd, rfl⟩
        refine ⟨i + j, c * d, (B ⊓ L).mul_mem hc hd, ?_⟩
        have hcx : c * x ^ j = x ^ j * c := ((hxL c hc.2).symm.zpow_right j).eq
        calc x ^ i * c * (x ^ j * d) = x ^ i * (c * x ^ j) * d := by group
          _ = x ^ i * (x ^ j * c) * d := by rw [hcx]
          _ = x ^ (i + j) * (c * d) := by rw [zpow_add]; group
      one_mem' := ⟨0, 1, (B ⊓ L).one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, c, hc, rfl⟩
        refine ⟨-i, c⁻¹, (B ⊓ L).inv_mem hc, ?_⟩
        have hcx : c⁻¹ * x ^ (-i) = x ^ (-i) * c⁻¹ :=
          ((hxL c hc.2).symm.zpow_right (-i)).inv_left.eq
        rw [mul_inv_rev, ← zpow_neg]
        exact hcx }
  have hle : Subgroup.zpowers x ⊔ (B ⊓ L) ≤ P :=
    sup_le (Subgroup.zpowers_le.2 ⟨1, 1, (B ⊓ L).one_mem, by simp⟩)
      (fun c hc => ⟨0, c, hc, by simp⟩)
  intro b hb
  rw [hsup] at hb
  exact hle hb

theorem exists_T_in_L (hc : S9Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} (h : H92 3 B x L)
    (hess : IsEssential 3 B x) (hodd : Odd (Nat.card (GLAPPrimeCoreOf 3 (cx x))))
    (hdir : IsDirectZpowersInf B x L) :
    ∃ T : Subgroup G, T ≤ L ∧ IsPGroup 2 T ∧ B ⊓ L ≤ Subgroup.normalizer (T : Set G) ∧
      ¬ T ≤ GLAPPrimeCoreOf 3 L := by
  have hp3 : Nat.Prime 3 := by norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  obtain ⟨-, -, T₀, hT₀C, hT₀2, hBT₀, hne, -⟩ := hess
  have hBel : IsElemAbelian 3 B := h.bmax.1
  have hB3 : IsPGroup 3 B := isPGroup_of_isElemAbelian hBel
  have hxL : ∀ c ∈ L, Commute x c := fun c hc =>
    (Subgroup.mem_centralizer_singleton_iff.1 (h.comp.1 hc)).symm
  have hLx : L ≤ cx x := h.comp.1
  have hTT₀ : ⁅T₀, B⁆ ≤ T₀ := by
    refine Subgroup.commutator_le.2 fun t ht b hb => ?_
    have e : ⁅t, b⁆ = t * (b * t⁻¹ * b⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact T₀.mul_mem ht ((Subgroup.mem_normalizer_iff.1 (hBT₀ hb) t⁻¹).1 (T₀.inv_mem ht))
  have hTC : ⁅T₀, B⁆ ≤ cx x := hTT₀.trans hT₀C
  have hT2 : IsPGroup 2 ↥(⁅T₀, B⁆ : Subgroup G) := hT₀2.to_le hTT₀
  have hBnT : B ≤ Subgroup.normalizer ((⁅T₀, B⁆ : Subgroup G) : Set G) := by
    have key : ∀ b' ∈ B, ⁅T₀, B⁆ ≤ (⁅T₀, B⁆ : Subgroup G).comap (MulAut.conj b').toMonoidHom := by
      intro b' hb'
      refine Subgroup.commutator_le.2 fun t ht c hc => ?_
      rw [Subgroup.mem_comap]
      have hbc : b' * c = c * b' := isElemAbelian_commute hBel hb' hc
      have hct : (MulAut.conj b') c = c := by
        rw [MulAut.conj_apply, hbc]
        group
      show (MulAut.conj b') ⁅t, c⁆ ∈ ⁅T₀, B⁆
      rw [map_commutatorElement, hct]
      exact Subgroup.commutator_mem_commutator
        ((Subgroup.mem_normalizer_iff.1 (hBT₀ hb') t).1 ht) hc
    intro b' hb'
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact key b' hb' hy
    · intro hy
      have h1 : b'⁻¹ * (b' * y * b'⁻¹) * b'⁻¹⁻¹ ∈ ⁅T₀, B⁆ := key b'⁻¹ (B.inv_mem hb') hy
      have e : b'⁻¹ * (b' * y * b'⁻¹) * b'⁻¹⁻¹ = y := by group
      rwa [e] at h1
  have hsolv : Group.IsSolvable ↥T₀ := by
    haveI := hT₀2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card B) (Nat.card ↥T₀) :=
    IsPGroup.coprime_card_of_ne 3 2 (by norm_num) B T₀ hB3 hT₀2
  have hdbl : ⁅⁅T₀, B⁆, B⁆ = ⁅T₀, B⁆ := GL83.commutator_double_eq_self B T₀ hBT₀ hcop hsolv
  have hdec := l94_mem_zpowers_mul (B := B) (L := L) (x := x) (fun c hc => hxL c hc) hdir.1
  have hTBL : ⁅⁅T₀, B⁆, B ⊓ L⁆ = ⁅T₀, B⁆ := by
    refine le_antisymm ((Subgroup.commutator_mono le_rfl inf_le_left).trans hdbl.le)
      (hdbl.symm.le.trans (Subgroup.commutator_le.2 fun t ht b hb => ?_))
    obtain ⟨i, c, hc, rfl⟩ := hdec b hb
    have hxt : Commute t x := Subgroup.mem_centralizer_singleton_iff.1 (hTC ht)
    have htv : t * x ^ i = x ^ i * t := (hxt.zpow_right i).eq
    have htc : ⁅t, c⁆ ∈ cx x := by
      rw [commutatorElement_def]
      exact (cx x).mul_mem ((cx x).mul_mem ((cx x).mul_mem (hTC ht) (hLx hc.2))
        ((cx x).inv_mem (hTC ht))) ((cx x).inv_mem (hLx hc.2))
    have hgx : Commute ⁅t, c⁆ x := Subgroup.mem_centralizer_singleton_iff.1 htc
    have hcomm_eq : ⁅t, x ^ i * c⁆ = ⁅t, c⁆ := by
      rw [commutatorElement_mul_right]
      have h1 : ⁅t, x ^ i⁆ = 1 := by
        rw [commutatorElement_def, htv]
        group
      have h2 : x ^ i * ⁅t, c⁆ * (x ^ i)⁻¹ = ⁅t, c⁆ := by
        rw [← (hgx.zpow_right i).eq]
        group
      rw [h1, one_mul, h2]
    rw [hcomm_eq]
    exact Subgroup.commutator_mem_commutator ht hc
  have hTL : ⁅T₀, B⁆ ≤ L := l94_le_of_subnormal_comm h.comp.2.1 inf_le_right hTC hTBL
  have hTO : ¬ ⁅T₀, B⁆ ≤ GLAPPrimeCoreOf 3 L := by
    intro hle
    have h1 : ⁅T₀, B⁆ ≤ GLAPPrimeCoreOf 3 (cx x) :=
      hle.trans (glaPPrimeCoreOf_le_of_isSubnormal hp3 h.comp.2.1)
    rcases hT2.card_eq_or_dvd with h2 | h2
    · exact hne (Subgroup.card_eq_one.1 h2)
    · exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2.trans (Subgroup.card_dvd_of_le h1)))
  exact ⟨⁅T₀, B⁆, hTL, hT2, inf_le_left.trans hBnT, hTO⟩

theorem lemma94_aux (hc : S9Ctx G 3) (hin : Lemma94Inputs G) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : H92 3 B x L) (hL4 : catalogIs (PSimple 3 L) isList94) :
    ¬ catalogIs (PSimple 3 L) (fun i => isSp6two i ∨ isU4two i) ∧
      (Nat.card B = 3 ^ 4 ∧ IsDirectZpowersInf B x L ∧
        Odd (Nat.card (GLAPPrimeCoreOf 3 (cx x)))) := by
  have hX : CFSG.Open.IsKGroup ↥(cx x) := isKGroup_cx hc h.ne_one
  obtain ⟨hZ, hOut, hrank⟩ := hin.rank23 (cx x) L h.comp hL4
  have hnoGB : ¬ IsGB 3 B L := by
    refine notIsGB_of_I269 hc hin.lbal hin.i269 h (catalogIs_mono (fun i hi => ?_) hL4)
    rcases hi with hi | hi | hi | hi
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (Or.inl hi))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hi))))
  have hess : IsEssential 3 B x := by
    rcases h.alt with h0 | hGB | ⟨-, he⟩
    · exact h0.1.2.1
    · exact absurd hGB hnoGB
    · exact he
  have hodd : Odd (Nat.card (GLAPPrimeCoreOf 3 (cx x))) := odd_core_of_not_isGB hc hin.l93 h hnoGB
  have hinner : ∀ b ∈ B, InducesInnerMod 3 L b := by
    by_contra hcon
    push Not at hcon
    obtain ⟨b, hbB, hb⟩ := hcon
    exact hb (hin.i117 B x L h.bmax hess hX h.comp h.norm (hOut b (h.norm hbB) (h.bmax.1.2 b hbB) hb) b hbB)
  have hdir := decomp_of_inner hc h hess hodd hZ hinner (hin.hy L hL4 hZ)
  obtain ⟨T, hTL, hT2, hBLT, hTO⟩ := exists_T_in_L hc h hess hodd hdir
  have hEel : IsElemAbelian 3 (B ⊓ L) := isElemAbelian_mono h.bmax.1 inf_le_left
  obtain ⟨hE27, hE9⟩ := hrank (B ⊓ L) T inf_le_right hEel hTL hT2 hTO hBLT
  have hcard : Nat.card B = 3 * Nat.card ↥(B ⊓ L) := by
    have hnorm : B ⊓ L ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      intro g hg
      have hg' : g ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
        rw [S3.centralizer_zpowers]
        exact (inf_le_left.trans h.le_cx) hg
      exact Subgroup.centralizer_le_normalizer _ hg'
    have h1 := card_sup_mul_card_inf_of_le_normalizer hnorm
    have hz : Nat.card (Subgroup.zpowers x) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (h.bmax.1.2 x h.mem) h.ne_one
    rw [← hdir.1, hdir.2, Subgroup.card_bot, hz, mul_one] at h1
    exact h1
  have h4 := h.pow_four_le hc
  norm_num at h4
  refine ⟨fun hSp => ?_, ?_, hdir, hodd⟩
  · have := hE9 hSp
    omega
  · norm_num
    omega

theorem lemma94 (hc : S9Ctx G 3) (hin : Lemma94Inputs G) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : H92 3 B x L) :
    ¬ catalogIs (PSimple 3 L) (fun i => isSp6two i ∨ isU4two i) ∧
      (catalogIs (PSimple 3 L) (fun i => isD4two i ∨ isU5two i) →
        Nat.card B = 3 ^ 4 ∧ IsDirectZpowersInf B x L ∧
          Odd (Nat.card (GLAPPrimeCoreOf 3 (cx x)))) := by
  refine ⟨fun hSp => ?_, fun hD => ?_⟩
  · refine (lemma94_aux hc hin h (catalogIs_mono (fun i hi => ?_) hSp)).1 hSp
    rcases hi with hi | hi
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
  · refine (lemma94_aux hc hin h (catalogIs_mono (fun i hi => ?_) hD)).2
    rcases hi with hi | hi
    · exact Or.inr (Or.inr (Or.inl hi))
    · exact Or.inr (Or.inr (Or.inr hi))

end CFSG.LocalAnalysis.GLTheoremA.S9
