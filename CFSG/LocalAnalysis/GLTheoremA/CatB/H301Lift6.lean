module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Lift5
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Tools
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Lift2
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma88

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

structure SporCfgCore (G : Type) [Group G] [Finite G] (p : ℕ) (x : G) (L : Subgroup G)
    (row : Row) where
  Bs : Subgroup G
  R : Subgroup G
  D : Subgroup G
  hBs : GLAIsBmax p Bs
  hBsCard : Nat.card Bs = p ^ row.rank
  hRL : R ≤ L
  hR : IsExtraSpec2 R ∧ Nat.card R = 2 ^ row.rexp
  hBsN : Bs ≤ cfgN x R
  hRN : R = pCoreOf 2 (cfgN x R)
  hD : D ≤ Bs ∧ IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧ x ∈ D
  hData : RowData row p Bs (cfgI p L D) (cfgK p x L D R) (cfgR0 R D)
  hMax : IsMaxInvTwo (cfgK p x L D R ⊔ Bs) (cx x) R
  hR0 : IsExtraSpec2 (cfgR0 R D) ∨ Nat.card (cfgR0 R D) = 2
  hNL : row = .m5 → ∃ J₀ : Subgroup G, GLAPComponent 5 (L ⊓ cfgN x R) J₀ ∧
    catalogIs (PSimple 5 J₀) (sporIs .Co1)
  hLn : cx x ≤ Subgroup.normalizer (L : Set G)
  hK6L : row = .ly ∨
    (cfgK p x L D R ≤ GLAPLayer p (L ⊓ (Subgroup.centralizer (D : Set G) ⊓
        Subgroup.centralizer (centerOf (cfgR0 R D) : Set G))) ∧
      lImg p L (GLAPLayer p (L ⊓ (Subgroup.centralizer (D : Set G) ⊓
        Subgroup.centralizer (centerOf (cfgR0 R D) : Set G)))) = lImg p L (cfgK p x L D R))

private theorem catalogIs_pSimple_of_pQuot_equiv {H : Type} [Group H] {p : ℕ} {X : Subgroup G}
    {Y : Subgroup H} (e : PQuot p X ≃* PQuot p Y) {Q : TauCeti.CFSGIndex → Prop}
    (h : catalogIs (PSimple p Y) Q) : catalogIs (PSimple p X) Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans f⟩⟩

theorem nonempty_sporCfgCore {p : ℕ} {row : Row} (hrowS : I301ARow row) (hc : row.center = 1)
    {x : G} {L : Subgroup G} (hx1 : x ≠ 1) (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L)
    (hrow : RowL row p L) (hodd : Odd (Nat.card (GLAPPrimeCoreOf p (cx x))))
    (hrk1 : ∀ A : Subgroup G, IsElemAbelian p A → A ≤ cx x → (∀ a ∈ A, CentMod p L a) →
      Nat.card A ≤ p)
    (hrk : GLATwoLocalRank p G ≤ row.rank) : Nonempty (SporCfgCore G p x L row) := by
  obtain ⟨hprow, hcat, hZ1⟩ := hrow
  subst hprow
  have hp : row.prime.Prime := by cases row <;> norm_num [Row.prime]
  have hp2 : row.prime ≠ 2 := by cases row <;> norm_num [Row.prime]
  set p : ℕ := row.prime with hpdef
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Subgroup.center (PQuot p L) = ⊥ := Subgroup.card_eq_one.1 (hZ1.trans hc)
  have hKcat : catalogIs (PQuot p L) (sporIs row.name) :=
    S8.L89.catalogIs_of_mulEquiv
      ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm⟩ hcat
  obtain ⟨Rt, Bt, dt, cfg⟩ := hrowS hc (PQuot p L) hKcat
  set π : ↥L →* PQuot p L := pQuotHom p L with hπdef
  have hπ : Function.Surjective π := pQuotHom_surjective p L
  have hkp : ¬ p ∣ Nat.card π.ker := not_dvd_card_ker_pQuotHom hp L
  have hOL : GLAPPrimeCoreOf p L ≤ GLAPPrimeCoreOf p (cx x) :=
    HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal p hL.2.1
  have hk2 : ¬ 2 ∣ Nat.card π.ker := by
    rw [hπdef, ker_pQuotHom]
    have h1 : Nat.card (GLAPPrimeCoreOf p L) = Nat.card (GLAPPrimeCore p ↥L) :=
      Subgroup.card_map_of_injective L.subtype_injective
    rw [← h1]
    intro h2
    have h3 : Nat.card (GLAPPrimeCoreOf p L) ∣ Nat.card (GLAPPrimeCoreOf p (cx x)) :=
      Subgroup.card_dvd_of_le hOL
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2.trans h3))
  have hRt2 : IsPGroup 2 Rt := cfg.hR.1.1
  obtain ⟨Rl, hRl2, hRlmap, hRlinj⟩ := CatB.exists_pSubgroup_lift Nat.prime_two π hk2 hRt2
    (by rw [MonoidHom.range_eq_top.2 hπ]; exact le_top)
  have hBt : IsPGroup p Bt := isPGroup_of_isElemAbelian cfg.hB.1
  have hBtN : Bt ≤ Subgroup.normalizer ((Rl.map π : Subgroup (PQuot p L)) : Set (PQuot p L)) := by
    rw [hRlmap]
    exact cfg.hBN
  obtain ⟨Wl, hWlN, hWlp, hWlmap, hWlinj⟩ :=
    exists_pGroup_lift_normalizer hp hp2 π hπ hkp hk2 hRl2 hRlinj hBt hBtN
  obtain ⟨dl, hdlW, hdl⟩ : dt ∈ Wl.map π := by
    rw [hWlmap]
    exact cfg.hd.1
  set R : Subgroup G := Rl.map L.subtype with hRdef
  set B₁ : Subgroup G := Wl.map L.subtype with hB₁def
  set d : G := (dl : G) with hddef
  have hdL : d ∈ L := dl.2
  have hdB : d ∈ B₁ := ⟨dl, hdlW, rfl⟩
  have hRL : R ≤ L := Subgroup.map_subtype_le _
  have hB₁L : B₁ ≤ L := Subgroup.map_subtype_le _
  have hLx : L ≤ cx x := hL.1
  have hRimg : lImg p L R = Rt := by rw [lImg_map_subtype]; exact hRlmap
  have hBimg : lImg p L B₁ = Bt := by rw [lImg_map_subtype]; exact hWlmap
  have hRsub : R.subgroupOf L = Rl := subgroupOf_map_subtype' Rl
  obtain ⟨hB₁e, hB₁c⟩ := CatB.map_subtype_isElemAbelian_card π hWlmap hWlinj cfg.hB.1
  have hB₁card : Nat.card B₁ = p ^ (row.rank - 1) := hB₁c.trans cfg.hB.2
  let eR : R ≃* Rt := (Rl.equivMapOfInjective L.subtype L.subtype_injective).symm.trans
    ((CatB.mulEquivMap π hRlinj).trans (MulEquiv.subgroupCongr hRlmap))
  have hRe : IsExtraSpec2 R ∧ Nat.card R = 2 ^ row.rexp :=
    ⟨(isExtraSpec2_congr eR).2 cfg.hR.1, (Nat.card_congr eR.toEquiv).trans cfg.hR.2⟩
  have hR2 : IsPGroup 2 R := hRl2.map _
  have hRne : R ≠ ⊥ := by
    intro h
    have h1 : Nat.card R = 1 := by rw [h, Subgroup.card_bot]
    rw [hRe.2] at h1
    have h2 : 2 ^ row.rexp = 2 ^ 0 := h1
    have h3 := Nat.pow_right_injective (le_refl 2) h2
    cases row <;> simp [Row.rexp] at h3
  have hxB : x ∉ B₁ := by
    rintro ⟨w, hw, hwx⟩
    have hcen : π w ∈ Subgroup.center (PQuot p L) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨l, rfl⟩ := hπ q
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show (l : G) * w = w * l
      have hwx' : (w : G) = x := hwx
      rw [hwx']
      exact Subgroup.mem_centralizer_singleton_iff.1 (hLx l.2)
    rw [hZ, Subgroup.mem_bot] at hcen
    have h1 : (⟨w, hw⟩ : Wl) = 1 := hWlinj (by simpa using hcen)
    apply hx1
    have hwx' : (w : G) = x := hwx
    rw [← hwx']
    simpa using congrArg (fun u : Wl => ((u : ↥L) : G)) h1
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hB₁x : B₁ ≤ cx x := hB₁L.trans hLx
  have hxC : x ∈ Subgroup.centralizer (B₁ : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun b hb => Subgroup.mem_centralizer_singleton_iff.1 (hB₁x hb)
  set Bs : Subgroup G := Subgroup.zpowers x ⊔ B₁ with hBsdef
  have hBse : IsElemAbelian p Bs :=
    S8.L89.isElemAbelian_sup (isElemAbelian_zpowers' hxp) hB₁e (Subgroup.zpowers_le.2 hxC)
  have hrank4 := S8.L89.four_le_rank row
  have hBscard : Nat.card Bs = p ^ row.rank := by
    rw [card_zpowers_sup hp hx hxB hB₁x, hB₁card, ← pow_succ']
    congr 1
    omega
  have hxR : x ∈ Subgroup.normalizer (R : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun r hr =>
      Subgroup.mem_centralizer_singleton_iff.1 (hLx (hRL hr)))
  have hB₁N : B₁ ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.map_mono hWlN).trans (Subgroup.le_normalizer_map L.subtype)
  have hBsNR : Bs ≤ Subgroup.normalizer (R : Set G) := sup_le (Subgroup.zpowers_le.2 hxR) hB₁N
  have hxX : x ∈ cx x := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hBsX : Bs ≤ cx x := sup_le (Subgroup.zpowers_le.2 hxX) hB₁x
  have hrank : GLATwoLocalRank p G = row.rank := le_antisymm hrk
    (HardMathSupport.Timmesfeld.ComponentBalance.le_glaTwoLocalRank_of_le_normalizer hp.one_lt
      hRne hR2 hBse hBsNR hBscard)
  have hBmax : GLAIsBmax p Bs := ⟨hBse, by rw [hrank]; exact hBscard, R, hRne, hR2, hBsNR⟩
  have hd1 : d ≠ 1 := by
    intro h
    apply cfg.hd.2
    rw [← hdl]
    have h1 : dl = 1 := Subtype.ext h
    rw [h1, map_one]
  have hdp : d ^ p = 1 := hB₁e.2 d hdB
  have hdx : d ∈ cx x := hB₁x hdB
  have hxd : x ∉ Subgroup.zpowers d := fun h => hxB (Subgroup.zpowers_le.2 hdB h)
  set D : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers d with hDdef
  have hDcard : Nat.card D = p ^ 2 := by
    rw [card_zpowers_sup hp hx hxd (Subgroup.zpowers_le.2 hdx), Nat.card_zpowers,
      orderOf_eq_prime hdp hd1, sq]
  have hDBs : D ≤ Bs := sup_le le_sup_left (le_sup_of_le_right (Subgroup.zpowers_le.2 hdB))
  have hDe : IsElemAbelian p D := isElemAbelian_mono hBse hDBs
  have hxD : x ∈ D := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hCD : Subgroup.centralizer (D : Set G) = cx x ⊓ cx d := centralizer_zpowers_sup x d
  have hLD : L ⊓ Subgroup.centralizer (D : Set G) = L ⊓ cx d := by
    rw [hCD, ← inf_assoc, inf_eq_left.2 hLx]
  have hdlp : dl ^ p = 1 := Subtype.ext (by simpa using hdp)
  have hdlpg : IsPGroup p (Subgroup.zpowers dl) := isPGroup_zpowers_of_pow_eq_one hdlp
  have hdpg : IsPGroup p (Subgroup.zpowers d) := isPGroup_zpowers_of_pow_eq_one hdp
  have hdlN : dl ∈ Subgroup.normalizer (Rl : Set ↥L) := hWlN hdlW
  set Cl : Subgroup ↥L := Subgroup.centralizer ({dl} : Set ↥L) with hCldef
  set Il : Subgroup ↥L := GLAPLayer p Cl with hIldef
  have hClsub : (L ⊓ cx d).subgroupOf L = Cl := by
    rw [subgroupOf_inf_centralizer hdL, Subgroup.subgroupOf_self, top_inf_eq]
  have hClmap : Cl.map π = Subgroup.centralizer ({dt} : Set (PQuot p L)) := by
    have h := lImg_inf_centralizer hp hkp hdL hdpg
    unfold lImg at h
    rw [hClsub] at h
    rw [h, ← hdl]
  have hIdef : cfgI p L D = GLAPLayer p (L ⊓ cx d) := by
    unfold cfgI
    rw [hLD]
  have hIL : cfgI p L D ≤ L := by
    rw [hIdef]
    exact (glaPLayer_le_self' _).trans inf_le_left
  have hIlsub : (cfgI p L D).subgroupOf L = Il := by
    rw [hIdef, glaPLayer_subgroupOf hp inf_le_left, hClsub]
  have hIlmap : Il.map π = rowIOf p dt := by
    rw [hIldef, S267.map_glaPLayer hp π hkp Cl, hClmap]
    rfl
  have hIimg : lImg p L (cfgI p L D) = rowIOf p dt := by
    unfold lImg
    rw [hIlsub, hIlmap]
  have hRowI : RowI row p (cfgI p L D) := by
    unfold RowI
    exact isTypeWithCenter_of_lImg hp hIL (hIimg ▸ cfg.hI)
  have hIN : cfgI p L D ⊓ cfgN x R = cfgI p L D ⊓ Subgroup.normalizer (R : Set G) := by
    unfold cfgN
    rw [← inf_assoc, inf_eq_left.2 (hIL.trans hLx)]
  have hKdef : cfgK p x L D R = GLAPLayer p (cfgI p L D ⊓ Subgroup.normalizer (R : Set G)) := by
    unfold cfgK
    rw [hIN]
  have hINL : cfgI p L D ⊓ Subgroup.normalizer (R : Set G) ≤ L := inf_le_left.trans hIL
  have hKL : cfgK p x L D R ≤ L := by
    rw [hKdef]
    exact (glaPLayer_le_self' _).trans hINL
  have hNsub : (Subgroup.normalizer (R : Set G)).subgroupOf L =
      Subgroup.normalizer (Rl : Set ↥L) := by
    rw [Subgroup.subgroupOf_normalizer_eq hRL, hRsub]
  have hKsub : (cfgI p L D ⊓ Subgroup.normalizer (R : Set G)).subgroupOf L =
      Il ⊓ Subgroup.normalizer (Rl : Set ↥L) := by
    rw [← hIlsub, ← hNsub]
    exact Subgroup.comap_inf _ _ _
  have hCN : (Cl ⊓ Subgroup.normalizer (Rl : Set ↥L)).map π =
      Cl.map π ⊓ Subgroup.normalizer ((Rl.map π : Subgroup (PQuot p L)) : Set (PQuot p L)) := by
    rw [map_centralizer_inf_normalizer hp hp2 π hπ hkp hk2 hRl2 hRlinj hdlpg hdlN, hClmap, hdl]
  have hKmap := map_glaPLayer_inf_normalizer hp π hkp (glaPLayer_le_self' Cl)
    (HardMathSupport.Solomon.UniquenessMaximal.Sec7.le_normalizer_glaPLayer p Cl) hCN
  have hKimg : lImg p L (cfgK p x L D R) = rowKOf p dt Rt := by
    unfold lImg
    rw [hKdef, glaPLayer_subgroupOf hp hINL, hKsub, hKmap, hIlmap, hRlmap]
    rfl
  have hRowK : RowK row p (cfgK p x L D R) := by
    rw [hKdef]
    apply rowK_of_lImg hp hINL
    rw [← lImg_glaPLayer hp hINL, ← hKdef, hKimg]
    exact cfg.hK
  have hR0def : cfgR0 R D = R ⊓ cx d := by
    unfold cfgR0
    rw [hCD, ← inf_assoc, inf_eq_left.2 (hRL.trans hLx)]
  have hR0L : R ⊓ cx d ≤ L := inf_le_left.trans hRL
  set R0l : Subgroup ↥L := Rl ⊓ Subgroup.centralizer ({dl} : Set ↥L) with hR0ldef
  have hR0sub : (R ⊓ cx d).subgroupOf L = R0l := by
    rw [subgroupOf_inf_centralizer hdL, hRsub]
  have hR0inj : Function.Injective (π.comp R0l.subtype) := by
    intro a b hab
    have h1 : (⟨a.1, a.2.1⟩ : Rl) = ⟨b.1, b.2.1⟩ := hRlinj hab
    have h2 : (a : ↥L) = (b : ↥L) := congrArg (fun u : Rl => (u : ↥L)) h1
    exact Subtype.ext h2
  have hR0map : R0l.map π = rowR0Of dt Rt := by
    apply le_antisymm
    · rintro _ ⟨r, ⟨hrR, hrC⟩, rfl⟩
      refine ⟨hRlmap ▸ Subgroup.mem_map_of_mem π hrR, ?_⟩
      have hrC' : r ∈ Subgroup.centralizer ({dl} : Set ↥L) := hrC
      show π r ∈ Subgroup.centralizer ({dt} : Set (PQuot p L))
      rw [Subgroup.mem_centralizer_singleton_iff] at hrC' ⊢
      rw [← hdl, ← map_mul, ← map_mul, hrC']
    · intro t ht
      have htR : t ∈ Rt := ht.1
      have htC : t ∈ Subgroup.centralizer ({dt} : Set (PQuot p L)) := ht.2
      rw [← hRlmap] at htR
      obtain ⟨r, hrR, rfl⟩ := htR
      refine ⟨r, ⟨hrR, ?_⟩, rfl⟩
      have hconj : dl * r * dl⁻¹ ∈ Rl := (Subgroup.mem_normalizer_iff.1 hdlN r).1 hrR
      have h1 : π (dl * r * dl⁻¹) = π r := by
        rw [Subgroup.mem_centralizer_singleton_iff] at htC
        rw [map_mul, map_mul, map_inv, hdl, ← htC, mul_inv_cancel_right]
      have h2 : (⟨dl * r * dl⁻¹, hconj⟩ : Rl) = ⟨r, hrR⟩ := hRlinj (by simpa using h1)
      have h3 : dl * r * dl⁻¹ = r := congrArg Subtype.val h2
      show r ∈ Subgroup.centralizer ({dl} : Set ↥L)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc r * dl = dl * r * dl⁻¹ * dl := by rw [h3]
        _ = dl * r := by group
  let e0 : cfgR0 R D ≃* rowR0Of dt Rt :=
    ((MulEquiv.subgroupCongr hR0def).trans (Subgroup.subgroupOfEquivOfLe hR0L).symm).trans
      ((MulEquiv.subgroupCongr hR0sub).trans
        ((CatB.mulEquivMap π hR0inj).trans (MulEquiv.subgroupCongr hR0map)))
  have hData : RowData row p Bs (cfgI p L D) (cfgK p x L D R) (cfgR0 R D) :=
    ⟨rfl, hBscard, hRowI, hRowK, (Nat.card_congr e0.toEquiv).trans cfg.hR0⟩
  have hR0t : IsExtraSpec2 (cfgR0 R D) ∨ Nat.card (cfgR0 R D) = 2 := by
    rcases cfg.hR0t with h | h
    · exact Or.inl ((isExtraSpec2_congr e0).2 h)
    · exact Or.inr ((Nat.card_congr e0.toEquiv).trans h)
  have hLn : cx x ≤ Subgroup.normalizer (L : Set G) := by
    refine le_normalizer_of_elemAbelian hp hL hB₁L hB₁e ?_ hrk1
    rw [hB₁card]
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ (row.rank - 1) := Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hKN : cfgK p x L D R ≤ Subgroup.normalizer (R : Set G) := by
    rw [hKdef]
    exact (glaPLayer_le_self' _).trans inf_le_right
  have hKBN : cfgK p x L D R ⊔ Bs ≤ Subgroup.normalizer (R : Set G) := sup_le hKN hBsNR
  haveI : Finite (MulAut (PQuot p L)) := finite_mulAut
  have hMax : IsMaxInvTwo (cfgK p x L D R ⊔ Bs) (cx x) R := by
    refine ⟨hRL.trans hLx, hR2, hKBN, fun R' hR'X hR'2 hR'N hRR' => ?_⟩
    have hA₀N : cfgK p x L D R ⊔ B₁ ≤ Subgroup.normalizer (R' : Set G) :=
      (sup_le_sup_left (le_sup_right : B₁ ≤ Bs) _).trans hR'N
    refine eq_of_le_of_map_barAut hp hp2 hx hL hLn hZ hodd hrk1 hRL (sup_le hKL hB₁L) ?_ hR'X
      hR'2 hA₀N hRR'
    intro R'' hR''2 hR''N hR''R
    rw [lImg_sup p hKL hB₁L, hKimg, hBimg] at hR''N
    rw [hRimg] at hR''R ⊢
    exact cfg.hMax (MulAut (PQuot p L)) MulAut.conj (mulAut_conj_injective hZ)
      range_mulAut_conj_normal (centralizer_range_mulAut_conj hZ) R'' hR''2 hR''N hR''R
  have hRN : R = pCoreOf 2 (cfgN x R) := by
    set P : Subgroup G := pCoreOf 2 (cfgN x R) with hPdef
    have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup.map _
    have hPN : P ≤ cfgN x R := Subgroup.map_subtype_le _
    have hRN' : R ≤ cfgN x R := le_inf (hRL.trans hLx) Subgroup.le_normalizer
    have hRP : R ≤ P := by
      have hn : (R.subgroupOf (cfgN x R)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hRN').2 inf_le_right
      have hle : R.subgroupOf (cfgN x R) ≤ CFSG.pCore 2 ↥(cfgN x R) :=
        le_sSup ⟨hn, hR2.comap_subtype⟩
      rw [← Subgroup.map_subgroupOf_eq_of_le hRN']
      exact Subgroup.map_mono hle
    have hKBP : cfgK p x L D R ⊔ Bs ≤ Subgroup.normalizer (P : Set G) := by
      have hKBcfgN : cfgK p x L D R ⊔ Bs ≤ cfgN x R := by
        refine sup_le ?_ (le_inf hBsX hBsNR)
        unfold cfgK
        exact glaPLayer_le_self' _ |>.trans inf_le_right
      refine hKBcfgN.trans ?_
      have hn : (P.subgroupOf (cfgN x R)).Normal := by
        rw [hPdef, pCoreOf, subgroupOf_map_subtype']
        exact CFSG.pCore_normal
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hPN).1 hn
    exact (hMax.2.2.2 P (hPN.trans inf_le_left) hP2 hKBP hRP).symm
  have hK6L : row = .ly ∨
      (cfgK p x L D R ≤ GLAPLayer p (L ⊓ (Subgroup.centralizer (D : Set G) ⊓
          Subgroup.centralizer (centerOf (cfgR0 R D) : Set G))) ∧
        lImg p L (GLAPLayer p (L ⊓ (Subgroup.centralizer (D : Set G) ⊓
          Subgroup.centralizer (centerOf (cfgR0 R D) : Set G)))) = lImg p L (cfgK p x L D R)) := by
    rcases cfg.hK6 with h6 | h6
    · exact Or.inl h6
    right
    have hZ0L : centerOf (cfgR0 R D) ≤ L := by
      rw [S8.L89.centerOf_eq_inf, hR0def]
      exact inf_le_left.trans hR0L
    set Z0l : Subgroup ↥L := R0l ⊓ Subgroup.centralizer (R0l : Set ↥L) with hZ0ldef
    have hZ0sub : (centerOf (cfgR0 R D)).subgroupOf L = Z0l := by
      rw [S8.L89.centerOf_eq_inf, hR0def]
      show (R ⊓ cx d ⊓ Subgroup.centralizer ((R ⊓ cx d : Subgroup G) : Set G)).comap L.subtype = _
      rw [Subgroup.comap_inf]
      change (R ⊓ cx d).subgroupOf L ⊓
        (Subgroup.centralizer ((R ⊓ cx d : Subgroup G) : Set G)).subgroupOf L = _
      rw [centralizer_subgroupOf' hR0L, hR0sub]
    have hZ0card : Nat.card (centerOf (cfgR0 R D)) = 2 := by
      rcases hR0t with h | h
      · have h1 : Nat.card (Subgroup.center ↥(cfgR0 R D)) = 2 := h.2.2.2
        rw [← h1]
        exact Subgroup.card_map_of_injective (cfgR0 R D).subtype_injective
      · have h1 : centerOf (cfgR0 R D) = cfgR0 R D := by
          apply le_antisymm
          · rw [S8.L89.centerOf_eq_inf]
            exact inf_le_left
          · intro r hr
            rw [S8.L89.mem_centerOf_iff]
            refine ⟨hr, fun s hs => ?_⟩
            haveI : IsCyclic ↥(cfgR0 R D) := isCyclic_of_prime_card (p := 2) h
            letI : CommGroup ↥(cfgR0 R D) := IsCyclic.commGroup
            have := mul_comm (⟨s, hs⟩ : ↥(cfgR0 R D)) ⟨r, hr⟩
            simpa using congrArg Subtype.val this
        rw [h1, h]
    have hZ0lcard : Nat.card Z0l = 2 := by
      rw [← hZ0sub, ← hZ0card]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ0L).toEquiv
    obtain ⟨zl, hzZ, hZ0eq, hz2⟩ := exists_eq_zpowers_of_card_two hZ0lcard
    have hzR : zl ∈ Rl := hzZ.1.1
    have hzC : zl ∈ Cl := hzZ.1.2
    have hz2g : IsPGroup 2 (Subgroup.zpowers zl) := isPGroup_zpowers_of_pow_eq_one hz2
    have hWsub : (L ⊓ (Subgroup.centralizer (D : Set G) ⊓
        Subgroup.centralizer (centerOf (cfgR0 R D) : Set G))).subgroupOf L =
        Cl ⊓ Subgroup.centralizer ({zl} : Set ↥L) := by
      rw [← inf_assoc, hLD]
      show ((L ⊓ cx d) ⊓ Subgroup.centralizer (centerOf (cfgR0 R D) : Set G)).comap L.subtype = _
      rw [Subgroup.comap_inf]
      change (L ⊓ cx d).subgroupOf L ⊓
        (Subgroup.centralizer (centerOf (cfgR0 R D) : Set G)).subgroupOf L = _
      rw [hClsub, centralizer_subgroupOf' hZ0L, hZ0sub, hZ0eq, S3.centralizer_zpowers]
    have hWL : L ⊓ (Subgroup.centralizer (D : Set G) ⊓
        Subgroup.centralizer (centerOf (cfgR0 R D) : Set G)) ≤ L := inf_le_left
    have hZt : centerOf (rowR0Of dt Rt) = Subgroup.zpowers (π zl) := by
      rw [S8.L89.centerOf_eq_inf, ← hR0map, ← map_inf_centralizer_self π hR0inj, ← hZ0ldef,
        hZ0eq, MonoidHom.map_zpowers]
    have hWmap : (Cl ⊓ Subgroup.centralizer ({zl} : Set ↥L)).map π =
        Subgroup.centralizer ({dt} : Set (PQuot p L)) ⊓
          Subgroup.centralizer (centerOf (rowR0Of dt Rt) : Set (PQuot p L)) := by
      rw [map_inf_centralizer_eq Nat.prime_two π hk2 hzC hz2g, hClmap, hZt,
        S3.centralizer_zpowers]
    set El : Subgroup ↥L := GLAPLayer p (Cl ⊓ Subgroup.centralizer ({zl} : Set ↥L)) with hEldef
    have hElmap : El.map π = rowKOf p dt Rt := by
      rw [hEldef, S267.map_glaPLayer hp π hkp, hWmap, ← h6]
    have hEsub : (GLAPLayer p (L ⊓ (Subgroup.centralizer (D : Set G) ⊓
        Subgroup.centralizer (centerOf (cfgR0 R D) : Set G)))).subgroupOf L = El := by
      rw [glaPLayer_subgroupOf hp hWL, hWsub]
    set Kl : Subgroup ↥L := GLAPLayer p (Il ⊓ Subgroup.normalizer (Rl : Set ↥L)) with hKldef
    have hKsub' : (cfgK p x L D R).subgroupOf L = Kl := by
      rw [hKdef, glaPLayer_subgroupOf hp hINL, hKsub]
    have hKlmap : Kl.map π = rowKOf p dt Rt := by
      rw [← hKsub']
      exact hKimg
    have hzKl : zl ∈ Subgroup.normalizer (Kl : Set ↥L) := by
      refine HardMathSupport.Solomon.UniquenessMaximal.Sec7.mem_normalizer_glaPLayer ?_
      exact S10.mem_normalizer_inf_of
        (HardMathSupport.Solomon.UniquenessMaximal.Sec7.le_normalizer_glaPLayer p Cl hzC)
        (Subgroup.le_normalizer (Subgroup.le_normalizer hzR))
    have hKlN : Kl ≤ Subgroup.normalizer (Rl : Set ↥L) := (glaPLayer_le_self' _).trans inf_le_right
    have hKlz : Kl.map π ≤ Subgroup.centralizer ({π zl} : Set (PQuot p L)) := by
      rw [hKlmap, h6, hZt, S3.centralizer_zpowers]
      exact (glaPLayer_le_self' _).trans inf_le_right
    have hKlC : Kl ≤ Subgroup.centralizer ({zl} : Set ↥L) :=
      le_centralizer_of_map_le π hk2 hRl2 hRlinj hzR hKlN hzKl hKlz
    have hKlCl : Kl ≤ Cl := (glaPLayer_le_self' _).trans (inf_le_left.trans (glaPLayer_le_self' Cl))
    have hKlE : Kl ≤ El :=
      le_glaPLayer_of_map_le hp π hkp (S10.pPrimePerfect_glaPLayer p _) (le_inf hKlCl hKlC)
        (by rw [hKlmap, hElmap])
    refine ⟨?_, ?_⟩
    · intro k hk
      have hkL : k ∈ L := hKL hk
      have h1 : (⟨k, hkL⟩ : ↥L) ∈ Kl := by
        rw [← hKsub']
        exact hk
      have h2 := hKlE h1
      rw [← hEsub] at h2
      exact h2
    · unfold lImg
      rw [hEsub, hKsub', hElmap, hKlmap]
  have hNL : row = .m5 → ∃ J₀ : Subgroup G, GLAPComponent 5 (L ⊓ cfgN x R) J₀ ∧
      catalogIs (PSimple 5 J₀) (sporIs .Co1) := by
    intro hm5
    obtain ⟨J₁, hJ₁, hJ₁cat⟩ := cfg.hNL hm5
    have hp5 : p = 5 := by rw [hpdef, hm5]; rfl
    have h5 : Nat.Prime 5 := by norm_num
    set A : Subgroup ↥L := Subgroup.normalizer (Rl : Set ↥L) with hAdef
    have hAmap : A.map π = Subgroup.normalizer (Rt : Set (PQuot p L)) := by
      rw [hAdef, map_normalizer_eq hp hp2 π hπ hkp hk2 hRl2 hRlinj, hRlmap]
    have hk5 : Nat.Coprime 5 (Nat.card ↥(A ⊓ π.ker)) := by
      rw [← hp5]
      exact coprime_card_inf_ker_pQuotHom hp L A
    have hk5' : ¬ 5 ∣ Nat.card π.ker := by
      rw [← hp5]
      exact hkp
    rw [← hAmap] at hJ₁
    obtain ⟨J, hJ, hJmap⟩ := exists_glaPComponent_map_eq h5 π hk5 hJ₁
    have hAsub : A.map L.subtype = L ⊓ cfgN x R := by
      rw [← hNsub, Subgroup.subgroupOf_map_subtype]
      unfold cfgN
      rw [← inf_assoc, inf_eq_left.2 hLx, inf_comm]
    refine ⟨J.map L.subtype, ?_, ?_⟩
    · rw [← hAsub]
      exact (Y10F.glaPComponent_map_iff h5 L.subtype_injective).2 hJ
    · have hJL : J.map L.subtype ≤ L := Subgroup.map_subtype_le _
      obtain ⟨e₀⟩ := nonempty_pQuot_equiv_subgroupOf 5 hJL
      rw [subgroupOf_map_subtype'] at e₀
      obtain ⟨e₁⟩ := nonempty_pQuot_equiv_map h5 hk5' J
      rw [hJmap] at e₁
      exact catalogIs_pSimple_of_pQuot_equiv (e₀.symm.trans e₁) hJ₁cat
  exact ⟨{
    Bs := Bs
    R := R
    D := D
    hBs := hBmax
    hBsCard := hBscard
    hRL := hRL
    hR := hRe
    hBsN := le_inf hBsX hBsNR
    hRN := hRN
    hD := ⟨hDBs, hDe, hDcard, hxD⟩
    hData := hData
    hMax := hMax
    hR0 := hR0t
    hNL := hNL
    hLn := hLn
    hK6L := hK6L }⟩

end CFSG.LocalAnalysis.GLTheoremA.H301
