module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourA67Fix
public import CFSG.CGT.PushingUpLit.CGT6.SixFourA6End
public import CFSG.CGT.PushingUpLit.CGT6.SixFourAlt7
public import CFSG.CGT.PushingUpLit.CGT6.SixFourA6Z

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement Pointwise MatrixGroups

section Transport

variable {Q Γ : Type*} [Group Q] [Group Γ]

theorem map_comap_eq_of_le (κ : Q →* Γ) {S : Subgroup Γ} (hS : S ≤ κ.range) :
    (S.comap κ).map κ = S := by
  rw [Subgroup.map_comap_eq, inf_of_le_right hS]

theorem card_comap_of_le {κ : Q →* Γ} (hκ : Function.Injective κ) {S : Subgroup Γ}
    (hS : S ≤ κ.range) : Nat.card (S.comap κ) = Nat.card S := by
  rw [← Subgroup.card_map_of_injective hκ, map_comap_eq_of_le κ hS]

theorem map_map_conj (κ : Q →* Γ) (S : Subgroup Q) (q : Q) :
    (S.map (MulAut.conj q).toMonoidHom).map κ =
      (S.map κ).map (MulAut.conj (κ q)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem range_mulEquiv {L : Type*} [Group L] (ρ : L →* Γ) (N : Subgroup L) [N.Normal]
    (hρker : ∀ y : L, ρ y = 1 ↔ y ∈ N) {M : Type*} [Group M] (φ : L ⧸ N ≃* M) :
    Nonempty (↥ρ.range ≃* M) := by
  have hker : ρ.ker = N := by
    ext y
    rw [MonoidHom.mem_ker]
    exact hρker y
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange ρ)).symm.trans φ⟩

end Transport

variable {G : Type} [Group G] [Finite G]

theorem eight_sl_not_good {Y R : Subgroup G} {T : Sylow 2 G} [R.Normal] (h : EightCtx Y T R)
    (hnat : IsNaturalSLTwoModule ↥Y 2) {K : Subgroup (G ⧸ R)} (hJbK : jBar R T ≤ K)
    (ρ : ↥Y →* ↥K) (hρval : ∀ z : ↥Y, ((ρ z : ↥K) : G ⧸ R) = QuotientGroup.mk' R z)
    (hρker : ∀ y : ↥Y, ρ y = 1 ↔ y ∈ pCore 2 ↥Y)
    {Q : Type} [Group Q] [Finite Q] (κ : Q →* ↥K) (hκ : Function.Injective κ)
    (hYκ : ρ.range ≤ κ.range) (hperf : commutator Q = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center Q)))
    (h6 : Nonempty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6)))
    {U₀ : Subgroup G} (hU : ⁅oTwoIn Y, Y⁆ ≤ U₀) (hU₀T : U₀ ≤ (T : Subgroup G))
    (hYU : Y ≤ Subgroup.normalizer (U₀ : Set G))
    (hYs : (Y.subgroupOf (Subgroup.normalizer (U₀ : Set G))).IsSubnormal) : False := by
  classical
  have hn : 1 ≤ 2 := by norm_num
  have hnat0 := hnat
  obtain ⟨hJfix, hJquad⟩ := h.jBar_fix hn hnat0
  have hidx : (h.cV (jBar R T)).index = 2 ^ 2 := h.index_cV_jBar hn hnat0
  obtain ⟨A, hA, hnot, hJA, hJY, hrel, -⟩ := eight_sl_nine h hn hnat0
  have hCB := eight_sl_corB h hn hnat0
  have hWC : CFSG.CGT.Timmesfeld75.IsWC (jBar R T) := CFSG.CGT.Timmesfeld75.isWC_of_corBHyp hCB
  have hAJ : A ≤ jIn (T : Subgroup G) := by
    rw [jIn_eq_thompsonJ]
    exact le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian (T : Subgroup G) A) => A) A hA
  have hcardJb : Nat.card (jBar R T) = 4 := by
    rw [jBar, (card_map_jIn_eq hAJ hJA).2, hrel, GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hSLeq : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨φ, ψ, hψs, hψk, hψe⟩ := hnat
  have hOY : oTwoIn Y ≤ R := h.le_R_of_le_centralizerModCore
    (ThreeFromEight.isPGroup_oTwoIn Y) (EightOneWindow.oTwoIn_le_centralizerModCore Y)
  let θK : ↥K →* MulAut ↥(omegaOneCenterIn R) := h.vAct.comp K.subtype
  let θ : Q →* MulAut ↥(omegaOneCenterIn R) := θK.comp κ
  have hθval : ∀ q : Q, θ q = h.vAct ((κ q : ↥K) : G ⧸ R) := fun q => rfl
  obtain ⟨Jb, hJbdef⟩ : ∃ Jb : Subgroup ↥K, Jb = (jBar R T).subgroupOf K := ⟨_, rfl⟩
  have hmemJb : ∀ x : ↥K, x ∈ Jb ↔ (x : G ⧸ R) ∈ jBar R T := fun x => by rw [hJbdef]; rfl
  have hJbmap : Jb.map K.subtype = jBar R T := by
    rw [hJbdef, Subgroup.subgroupOf_map_subtype, inf_of_le_left hJbK]
  have hJbcard : Nat.card Jb = 4 := by
    rw [← hcardJb, hJbdef]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJbK).toEquiv
  obtain ⟨eYb⟩ := range_mulEquiv ρ (pCore 2 ↥Y) hρker φ
  have hJbYb : Jb ≤ ρ.range := by
    intro x hx
    rw [hmemJb] at hx
    obtain ⟨j, hj, hjx⟩ := hx
    obtain ⟨y, hy, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hJY hj)
    have hr1 : QuotientGroup.mk' R r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    rw [hρval]
    rw [← hjx, map_mul, hr1, mul_one]
  obtain ⟨hYgen, hYcent⟩ := l2_four_facts hJbYb hJbcard eYb
  have hYbcard : Nat.card ρ.range = 60 := card_sl2_four eYb
  let J : Subgroup Q := Jb.comap κ
  let Y₀ : Subgroup Q := ρ.range.comap κ
  have hJκ : Jb ≤ κ.range := hJbYb.trans hYκ
  have hmemJ : ∀ a : Q, a ∈ J ↔ ((κ a : ↥K) : G ⧸ R) ∈ jBar R T := fun a => hmemJb (κ a)
  have hfixJ : fixQ θ J = h.cV (jBar R T) := by
    show autFixGrp (J.map θ) = autFixGrp ((jBar R T).map h.vAct)
    congr 1
    show (J.map (θK.comp κ)) = _
    rw [← Subgroup.map_map, map_comap_eq_of_le κ hJκ]
    show Jb.map (h.vAct.comp K.subtype) = _
    rw [← Subgroup.map_map, hJbmap]
  have S : A6Setting θ J Y₀ := by
    refine
      { hc := omegaOneCenterIn_comm R
        hV := omegaOneCenterIn_mul_self R
        faithful := ?_
        perfect := hperf
        odd := hodd
        alt6 := h6
        JY := Subgroup.comap_mono hJbYb
        Jcard := ?_
        Jexp := ?_
        Y60 := ?_
        Ygen := ?_
        Ycent := ?_
        Jidx := ?_
        JC := ?_
        Jquad := ?_
        y3 := ?_ }
    · exact (h.vAct_injective.comp K.subtype_injective).comp hκ
    · rw [card_comap_of_le hκ hJκ, hJbcard]
    · intro a ha
      have haJ := (hmemJ a).mp ha
      have h2 := hWC.1.2 _ haJ
      have h3 : ((κ a * κ a : ↥K) : G ⧸ R) = 1 := by
        rw [Subgroup.coe_mul, ← sq]
        exact h2
      apply hκ
      rw [map_mul, map_one]
      exact Subtype.ext h3
    · rw [card_comap_of_le hκ hYκ, hYbcard]
    · obtain ⟨g, hg, hgen⟩ := hYgen
      obtain ⟨q, hq⟩ := hYκ hg
      refine ⟨q, Subgroup.mem_comap.mpr (hq ▸ hg), ?_⟩
      apply Subgroup.map_injective hκ
      rw [Subgroup.map_sup, map_map_conj, map_comap_eq_of_le κ hJκ, map_comap_eq_of_le κ hYκ, hq]
      exact hgen
    · intro a ha ha1 g hg hgc
      have haJ : κ a ∈ Jb := ha
      have ha1' : κ a ≠ 1 := fun hh => ha1 (hκ (by rw [hh, map_one]))
      have hgY : κ g ∈ ρ.range := hg
      have hc : κ g * κ a = κ a * κ g := by rw [← map_mul, ← map_mul, hgc]
      exact hYcent (κ a) haJ ha1' (κ g) hgY hc
    · intro a ha ha1
      have haJ := (hmemJ a).mp ha
      have ha1' : ((κ a : ↥K) : G ⧸ R) ≠ 1 := by
        intro hh
        have hh' : κ a = 1 := Subtype.ext hh
        exact ha1 (hκ (by rw [hh', map_one]))
      rw [hθval, hJfix _ haJ ha1', hidx]
      norm_num
    · rw [hfixJ, hidx]
      norm_num
    · intro a ha v
      have haJ := (hmemJ a).mp ha
      rw [hfixJ, hθval]
      exact hJquad _ haJ v
    · intro y hy hord
      obtain ⟨y', hy'⟩ := Subgroup.mem_comap.mp hy
      have hθy : θ y = h.vAct (QuotientGroup.mk (y' : G)) := by
        rw [hθval, ← hy', hρval]
        rfl
      have hy3 : y ^ 3 = 1 := by
        rw [← hord]
        exact pow_orderOf_eq_one y
      have hy1 : y ≠ 1 := by
        intro hh
        rw [hh, orderOf_one] at hord
        omega
      have hφ3 : (φ (QuotientGroup.mk y')) ^ 3 = 1 := by
        have h1 : ρ (y' ^ 3) = 1 := by
          rw [map_pow, hy', ← map_pow, hy3, map_one]
        have h2 : (QuotientGroup.mk (y' ^ 3) : ↥Y ⧸ pCore 2 ↥Y) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr ((hρker _).mp h1)
        rw [← map_pow, ← QuotientGroup.mk_pow, h2, map_one]
      have hφ1 : φ (QuotientGroup.mk y') ≠ 1 := by
        intro hh
        have h1 : (QuotientGroup.mk y' : ↥Y ⧸ pCore 2 ↥Y) = 1 := by
          apply φ.injective
          rw [hh, map_one]
        have h2 : y' ∈ pCore 2 ↥Y := (QuotientGroup.eq_one_iff _).mp h1
        have h3 : ρ y' = 1 := (hρker _).mpr h2
        rw [hy'] at h3
        exact hy1 (hκ (by rw [h3, map_one]))
      have hfix : ∀ w : Fin 2 → GaloisField 2 2,
          ((φ (QuotientGroup.mk y') : SL(2, GaloisField 2 2)) :
            Matrix (Fin 2) (Fin 2) (GaloisField 2 2)).mulVec w = w → w = 0 :=
        fun w hw => fixed_vec_eq_zero_of_order_three hφ3 hφ1 w hw
      have hle := h.le_index_autFixSub φ ψ hψs hψe y' hfix
      rw [hSLeq] at hle
      rw [hθy]
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ _ := hle
  have hstab := stabComm_eq_top S
  let κ' : Q →* G ⧸ R := K.subtype.comp κ
  have hκ' : Function.Injective κ' := K.subtype_injective.comp hκ
  let π : G →* G ⧸ R := QuotientGroup.mk' R
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective R
  obtain ⟨X, hX⟩ : ∃ X : Subgroup G, X = κ'.range.comap π := ⟨_, rfl⟩
  have hmemX : ∀ x : G, x ∈ X ↔ π x ∈ κ'.range := fun x => by rw [hX]; rfl
  have hYX : Y ≤ X := by
    intro y hy
    rw [hmemX]
    obtain ⟨q, hq⟩ := hYκ (⟨⟨y, hy⟩, rfl⟩ : ρ ⟨y, hy⟩ ∈ ρ.range)
    refine ⟨q, ?_⟩
    show ((κ q : ↥K) : G ⧸ R) = π y
    rw [hq, hρval]
  have hUV : blockU Y ≤ omegaOneCenterIn R := h.blockU_le_V
  have hY := h.hY.1
  obtain ⟨hmax, hcR⟩ := normal_setting_facts h.hchar h.hRP
  obtain ⟨hRU, hVU, -, -⟩ := step_two hY h.hR2 hcR h.R_le_centralizerModCore
  have hcomm : commSub θ Y₀ ≤ (blockU Y).subgroupOf (omegaOneCenterIn R) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨s, hs, v, rfl⟩
    obtain ⟨y, hy⟩ := Subgroup.mem_comap.mp hs
    have h1 : θ s = h.vAct (QuotientGroup.mk (y : G)) := by
      rw [hθval, ← hy, hρval]
      rfl
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, h1,
      h.vAct_mk]
    have h2 : ⁅(y : G), (v : G)⁆ ∈ ⁅Y, omegaOneCenterIn R⁆ :=
      Subgroup.commutator_mem_commutator y.2 v.2
    rw [Subgroup.commutator_comm, hVU, commutatorElement_def] at h2
    exact h2
  have hconjU : ∀ x ∈ X, ∀ u ∈ blockU Y, x * u * x⁻¹ ∈ blockU Y := by
    intro x hx u hu
    obtain ⟨q, hq⟩ := (hmemX x).mp hx
    have hqS : q ∈ stabComm θ Y₀ := hstab ▸ Subgroup.mem_top q
    have hv : u ∈ omegaOneCenterIn R := hUV hu
    have h1 := hcomm (hqS ⟨u, hv⟩)
    have hθq : θ q = h.vAct (QuotientGroup.mk x) := by
      rw [hθval]
      show h.vAct (κ' q) = _
      rw [hq]
      rfl
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hθq, h.vAct_mk] at h1
    have h2 : x * u * x⁻¹ = (x * u * x⁻¹ * u⁻¹) * u := by group
    rw [h2]
    exact (blockU Y).mul_mem h1 hu
  have hXU : X ≤ Subgroup.normalizer ((blockU Y : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      exact hconjU x hx u hu
    · intro hu
      have h3 : x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = u := by group
      have := hconjU x⁻¹ (X.inv_mem hx) (x * u * x⁻¹) hu
      rw [h3] at this
      exact this
  have hU₀2 : IsPGroup 2 U₀ := T.isPGroup'.to_le hU₀T
  have hsubX := isSubnormal_of_clause hY hcR h.hR hU₀2 hU hYU hYs hYX hXU
  let lam : ↥X →* Q := ((MonoidHom.ofInjective hκ').symm.toMonoidHom).comp
    ((π.subgroupComap κ'.range).comp (MulEquiv.subgroupCongr hX).toMonoidHom)
  have hlam : ∀ x : ↥X, κ' (lam x) = π (x : G) := by
    intro x
    have h1 := (MonoidHom.ofInjective hκ').apply_symm_apply
      ((π.subgroupComap κ'.range) ((MulEquiv.subgroupCongr hX) x))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  have hlam_surj : Function.Surjective lam := by
    intro q
    obtain ⟨g, hg⟩ := hπ (κ' q)
    have hgX : g ∈ X := (hmemX g).mpr ⟨q, hg.symm⟩
    refine ⟨⟨g, hgX⟩, hκ' ?_⟩
    rw [hlam]
    exact hg
  have himg : (Y.subgroupOf X).map lam = Y₀ := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxY : (x : G) ∈ Y := hx
      show κ (lam x) ∈ ρ.range
      refine ⟨⟨x, hxY⟩, Subtype.ext ?_⟩
      rw [hρval]
      exact (hlam x).symm
    · intro hq
      obtain ⟨y, hy⟩ := Subgroup.mem_comap.mp hq
      refine ⟨⟨(y : G), hYX y.2⟩, y.2, ?_⟩
      apply hκ'
      rw [hlam]
      show π (y : G) = ((κ q : ↥K) : G ⧸ R)
      rw [← hy, hρval]
  have hsubQ : Y₀.IsSubnormal := himg ▸ hsubX.map hlam_surj
  exact S.false_of_isSubnormal hsubQ

theorem eight_sl_not_alt67 {Y R : Subgroup G} {T : Sylow 2 G} [R.Normal] (h : EightCtx Y T R) {n : ℕ}
    (hn : 1 ≤ n) (hnat : IsNaturalSLTwoModule ↥Y n)
    (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt) (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt)
    (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification)
    (hA : Nonempty (↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T) ≃*
        alternatingGroup (Fin 6)) ∨
      Nonempty (↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T) ≃*
        alternatingGroup (Fin 7)))
    {U₀ : Subgroup G} (hU : ⁅oTwoIn Y, Y⁆ ≤ U₀) (hU₀T : U₀ ≤ (T : Subgroup G))
    (hYU : Y ≤ Subgroup.normalizer (U₀ : Set G))
    (hYs : (Y.subgroupOf (Subgroup.normalizer (U₀ : Set G))).IsSubnormal) : False := by
  classical
  obtain ⟨hn2, hsimple, hlist, hstd, hcardTh, hperf, ρ, ι', hρval, hι'mk, hι'inj, hWCb, hZodd⟩ :=
    eight_sl_ident h hn hnat hS h215 hL
  have hcard4 : Nat.card (((jBar R T).subgroupOf (jBarClosure R T)).map
      (QuotientGroup.mk' (Subgroup.center ↥(jBarClosure R T)))) = 4 := by
    rcases hA with hA | hA
    · simpa using hstd.card_alternating (k := 6) (by norm_num) (by norm_num) hA
    · simpa using hstd.card_alternating (k := 7) (by norm_num) (by norm_num) hA
  have hn2' : n = 2 := by
    have h2n : 2 ^ n = 2 ^ 2 := by rw [← hcardTh, hcard4]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h2n
  subst hn2'
  have hOY : oTwoIn Y ≤ R := h.le_R_of_le_centralizerModCore
    (ThreeFromEight.isPGroup_oTwoIn Y) (EightOneWindow.oTwoIn_le_centralizerModCore Y)
  have hρker : ∀ y : ↥Y, ρ y = 1 ↔ y ∈ pCore 2 ↥Y := by
    intro y
    constructor
    · intro hy
      have h1 : ι' (QuotientGroup.mk y) = 1 := by rw [hι'mk, hy, map_one]
      have h2 : (QuotientGroup.mk y : ↥Y ⧸ pCore 2 ↥Y) = 1 := hι'inj (by rw [h1, map_one])
      exact (QuotientGroup.eq_one_iff y).mp h2
    · intro hy
      have hyR : (y : G) ∈ R := hOY ⟨y, hy, rfl⟩
      have h3 : QuotientGroup.mk' R (y : G) = 1 := (QuotientGroup.eq_one_iff _).mpr hyR
      apply Subtype.ext
      rw [hρval]
      exact h3
  have hJbK : jBar R T ≤ jBarClosure R T := Subgroup.le_normalClosure
  rcases hA with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact eight_sl_not_good h hnat hJbK ρ hρval hρker (MonoidHom.id _) Function.injective_id
      (fun x _ => ⟨x, rfl⟩) hperf hZodd ⟨e⟩ hU hU₀T hYU hYs
  · obtain ⟨φ, -⟩ := id hnat
    obtain ⟨eYb⟩ := range_mulEquiv ρ (pCore 2 ↥Y) hρker φ
    have hsimpleYb : IsSimpleGroup ↥ρ.range := isSimpleGroup_of_sl2_four eYb
    have h60 : Nat.card ρ.range = 60 := card_sl2_four eYb
    obtain ⟨K', hYK', hK'perf, hK'odd, hK'6⟩ := exists_alt6_sub_of_alt7 e hZodd hsimpleYb h60
    exact eight_sl_not_good h hnat hJbK ρ hρval hρker K'.subtype (Subgroup.subtype_injective K')
      (by rw [Subgroup.range_subtype]; exact hYK') hK'perf hK'odd hK'6 hU hU₀T hYU hYs

end CFSG.CGT.PushingUpLit.CGT6
