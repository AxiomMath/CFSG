module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamComp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveFinal

public section

namespace CFSG.QuasithinUnique.Lin2.Exam

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Vol2Native
open CFSG.ComponentClassification.CatalogueBSymplecticTwo

section Config

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D) {s x : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S)
  (hs2 : s ^ 2 = 1) (hc : centerOf L ≠ ⊥) (h4 : 4 < 2 ^ n)
  (hx : x ∈ T ⊓ Subgroup.centralizer ({s} : Set G)) (hxS : x ∉ S)
  {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({s} : Set G)))
  (hLK : L ⊓ Subgroup.centralizer ({s} : Set G) ≤ K)

include E hcfg hs hsR hs2 hc h4 hx hxS hK hLK

theorem exam_config
    :
    ∃ m : ℕ, n = 2 * m ∧
      ExamConfig K (L ⊓ Subgroup.centralizer ({s} : Set G))
        (conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x)
        ((T ⊓ Subgroup.centralizer ({s} : Set G)) ⊓ K)
        (thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G)) m := by
  obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxs : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  obtain ⟨m, hm, hm1, hsh, hlin, hUs, hO, hRsyl⟩ := exam_block E hcfg hs hsR hs2 h4
  obtain ⟨hZs, hZcard⟩ := exam_blockZ E hcfg hs hsR hs2 hc h4 hm hsh hUs hO
  have hKs := exam_Ks_le_K E hcfg hs hsR hs2 hc h4 hx hxS hK hLK
  have hUs' := exam_blockU_conj hxs L hUs
  refine ⟨m, hm, ?_⟩
  exact
  { two_le := hm1
    quasisimple := exam_K_quasisimple E hcfg hs hsR hs2 hc h4 hx hxS hK hLK
    list := exam_K_list E hcfg hs hsR hs2 hc h4 hx hxS hK hLK
    card_pCore := by
      have h1 := Subgroup.card_le_of_le (exam_K_pCore_le E hcfg hs hsR hs2 hc h4 hx hxS hK)
      have h2 : Nat.card (Subgroup.zpowers s) ≤ 2 := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hs2)
      exact h1.trans h2
    le_K := hLK
    le_K' := le_sup_right.trans hKs
    short := hsh
    short' := (isShort2_conjR_iff _ _).mpr hsh
    lin2 := hlin
    lin2' := (isLin2Type_conjR_iff _ _ _).mpr hlin
    pCore := hO.trans hUs
    pCore' := by rw [conjR_pCoreOf, hO.trans hUs, blockU_conjR]
    card_Z := hZcard
    card_Z' := by rw [exam_blockZ_conjR, card_conjR]; exact hZcard
    sylowP := exam_K_sylow E hcfg hs hsR hs2 h4 hK
    R_le_P := le_inf (Lin2Hyp.R_inf_le_T_inf hcfg) ((exam_Rs_le E hcfg).trans hLK)
    sylowB := hRsyl
    sylowB' := by
      refine isSylowTwoOf_of_card_eq (exam_Rs_le_conj E hcfg hxT hxs)
        (hcfg.S_isPGroup.to_le (inf_le_left.trans (thompsonJ_le_self S))) ?_
      have h1 : twoPart (conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x) =
          twoPart (L ⊓ Subgroup.centralizer ({s} : Set G)) :=
        twoPart_map_equiv (MulAut.conj x⁻¹) _
      rw [h1]
      exact hRsyl.card_eq
    R_eq := by
      rw [hUs', ← hUs]
      exact exam_Rs_eq_sup E hcfg hs hsR hs2 hxT hxS
    U_ne := by
      rw [hUs', ← hUs]
      exact exam_Us_ne E hcfg hs hsR hs2 hc h4 hxT hxS
    elem_le := by
      intro E' hE'R hE'
      rw [hUs', ← hUs]
      exact E.elem_le_U_s_or_V_s hcfg hxT hxS hE'R hE'
    strong := by
      intro i hi hi2 g hg hgi
      have hR' := (E.h21 G T M H S L D n hcfg).2 i hi.1 hi2 g hgi.1.1
      exact Subgroup.mem_inf.mpr ⟨hR', hgi.1.2⟩
    card_R := by
      rw [(E.card_R_inf_centralizer hcfg hs hsR hs2).2 hc]
      congr 1
      omega
    card_U := by
      have h1 := ((E.U_s_values hcfg hs hsR hs2 hxT hxS).2 hc).1
      rw [← hUs, h1]
      congr 1
      omega
    card_U' := by
      have h1 := E.card_conjR_U_inf_centralizer hcfg hs hsR hs2 hxT
      have h2 := ((E.U_s_values hcfg hs hsR hs2 hxT hxS).2 hc).1
      rw [hUs', h1, h2]
      congr 1
      omega
    center_inf_R := by
      intro z hz hzR
      have hRS : (thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G)) ≤ S :=
        inf_le_left.trans (thompsonJ_le_self S)
      have hz2 : IsPGroup 2 (Subgroup.zpowers (z : G)) :=
        (hcfg.S_isPGroup.to_le hRS).to_le (Subgroup.zpowers_le.mpr hzR)
      have hzK : Subgroup.zpowers (z : G) ≤ K := Subgroup.zpowers_le.mpr z.2
      have hzc : ∀ k ∈ K, ∀ w ∈ Subgroup.zpowers (z : G), w * k = k * w := by
        intro k hk w hw
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        have hkz : (k : G) * (z : G) = (z : G) * (k : G) :=
          congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)
        exact (Commute.zpow_left (show Commute (z : G) k from hkz.symm) j).eq
      have hzn : K ≤ Subgroup.normalizer ((Subgroup.zpowers (z : G) : Subgroup G) : Set G) := by
        intro k hk
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          have h1 := hzc k hk y hy
          rw [← h1, mul_inv_cancel_right]
          exact hy
        · intro hy
          have h2 := hzc k hk _ hy
          have e : y = k⁻¹ * (k * y * k⁻¹) * k := by group
          have e2 : k⁻¹ * (k * y * k⁻¹) * k = k * y * k⁻¹ := by
            rw [mul_assoc, h2, inv_mul_cancel_left]
          rw [e, e2]
          exact hy
      have hzO : Subgroup.zpowers (z : G) ≤ pCoreOf 2 K := le_pCoreOf_of_normalizes hzK hzn hz2
      have hzs : (z : G) ∈ Subgroup.zpowers s :=
        (exam_K_pCore_le E hcfg hs hsR hs2 hc h4 hx hxS hK) (hzO (Subgroup.mem_zpowers _))
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hzs
      have hss : s ^ (2 : ℤ) = 1 := by
        rw [zpow_two, ← sq]
        exact hs2
      have hkey : s ^ j = s ^ (j % 2) := by
        conv_lhs => rw [← Int.mul_ediv_add_emod j 2]
        rw [zpow_add, zpow_mul, hss, one_zpow, one_mul]
      rcases Int.emod_two_eq_zero_or_one j with h0 | h1
      · rw [h0, zpow_zero] at hkey
        exact Subtype.ext (hj.symm.trans hkey)
      · rw [h1, zpow_one] at hkey
        exfalso
        apply hsR
        have hzeq : (z : G) = s := hj.symm.trans hkey
        have hzJ : (z : G) ∈ thompsonJ S := hzR.1
        rw [hzeq] at hzJ
        exact hzJ }

end Config

section Final

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D) {s x : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S)
  (hs2 : s ^ 2 = 1) (hc : centerOf L ≠ ⊥) (h4 : 4 < 2 ^ n)
  (hx : x ∈ T ⊓ Subgroup.centralizer ({s} : Set G)) (hxS : x ∉ S)
  {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({s} : Set G)))
  (hLK : L ⊓ Subgroup.centralizer ({s} : Set G) ≤ K)

include E hcfg hx

omit hs hsR hs2 hc h4 hxS hK hLK in
theorem exam_conjR_inv : conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x⁻¹ =
    conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x := by
  obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxs : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  have hxxS : x * x ∈ S := Five.mul_self_mem_S E hcfg hxT
  have hxxs : (x * x) * s = s * (x * x) := by
    calc x * x * s = x * (x * s) := by group
      _ = x * (s * x) := by rw [hxs]
      _ = (x * s) * x := by group
      _ = (s * x) * x := by rw [hxs]
      _ = s * (x * x) := by group
  have hxxs' : (x * x)⁻¹ * s = s * (x * x)⁻¹ := Five.comm_inv_of_comm hxxs
  have h1 : conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) (x * x)⁻¹ =
      L ⊓ Subgroup.centralizer ({s} : Set G) :=
    Five.conjR_Ls_eq hcfg (S.inv_mem hxxS) hxxs'
  have e1 : x⁻¹ = (x * x)⁻¹ * x := by group
  rw [e1, ← conjR_conjR, h1]

end Final

end CFSG.QuasithinUnique.Lin2.Exam

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Vol2Native
open CFSG.QuasithinUnique.Lin2.Exam

theorem lemma2_4_23_five_exam_of
    (E : Lin2Hyp) (a39 : A39ForSQTKCat)
    (hD : Lemma2_4_23_five_examK) : Lemma2_4_23_five_exam := by
  intro G _ _ T M H S L D n hcfg s hs hsR hs2 hc h4 x hx hxS
  obtain ⟨K, hK, hLK⟩ := exam_exists_K E hcfg hs hsR hs2 h4 a39
  obtain ⟨m, hm, hcfgK⟩ := exam_config E hcfg hs hsR hs2 hc h4 hx hxS hK hLK
  obtain ⟨F, hFfield, hFfin, hF, ⟨e⟩⟩ := hD G K _ _ _ _ m hcfgK
  obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxs : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  have hm2 : 2 ≤ m := hcfgK.two_le
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCharP : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hFfin' : Finite F := Finite.of_fintype F
  have hKs := exam_Ks_le_K E hcfg hs hsR hs2 hc h4 hx hxS hK hLK
  have hLsK : L ⊓ Subgroup.centralizer ({s} : Set G) ≤ K := hLK
  have hLs'K : conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x ≤ K := le_sup_right.trans hKs
  have hRsK : IsSylowTwoOf (thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G)) K := by
    refine Five.isSylowTwoOf_of_card hF (by omega) e ((exam_Rs_le E hcfg).trans hLsK)
      (hcfg.S_isPGroup.to_le (inf_le_left.trans (thompsonJ_le_self S))) ?_
    rw [(E.card_R_inf_centralizer hcfg hs hsR hs2).2 hc]
    congr 1
    omega
  have hLsc : L ⊓ Subgroup.centralizer ({s} : Set G) ∈ cComp
      (L ⊓ Subgroup.centralizer ({s} : Set G) ⊔ S ⊓ Subgroup.centralizer ({s} : Set G)) :=
    (exam_isLocal E hcfg hs hsR hs2 h4).2.1
  have hLsperf : ⁅L ⊓ Subgroup.centralizer ({s} : Set G),
      L ⊓ Subgroup.centralizer ({s} : Set G)⁆ = L ⊓ Subgroup.centralizer ({s} : Set G) :=
    perfect_of_mem_cComp hLsc
  have hLsns : ¬ Group.IsSolvable ↥(L ⊓ Subgroup.centralizer ({s} : Set G)) := fun hs' =>
    not_isSolvable_of_mem_cComp hLsc hs'
  have hLs'perf : ⁅conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x,
      conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x⁆ =
      conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x := by
    rw [conjR_def, ← Subgroup.map_commutator, hLsperf]
  have hLs'ns : ¬ Group.IsSolvable ↥(conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x) :=
    fun hs' => hLsns (CFSG.QuasithinUnique.Setup.X6.isSolvable_of_map_equiv (MulAut.conj x⁻¹) _ hs')
  have hRX : IsSylowTwoOf ((thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf K) ⊤ :=
    isSylowTwoOf_top_subgroupOf hRsK
  have hRB : (thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf K ≤
      (L ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf K := fun y hy =>
    Subgroup.mem_subgroupOf.mpr ((exam_Rs_le E hcfg) (Subgroup.mem_subgroupOf.mp hy))
  have hRB' : (thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf K ≤
      (conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x).subgroupOf K := fun y hy =>
    Subgroup.mem_subgroupOf.mpr ((exam_Rs_le_conj E hcfg hxT hxs) (Subgroup.mem_subgroupOf.mp hy))
  have hBp : ⁅(L ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf K,
      (L ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf K⁆ =
      (L ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf K := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLsK]
    exact hLsperf
  have hBp' : ⁅(conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x).subgroupOf K,
      (conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x).subgroupOf K⁆ =
      (conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x).subgroupOf K := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLs'K]
    exact hLs'perf
  have hBns : ¬ Group.IsSolvable ↥((L ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf K) :=
    fun hs' => hLsns (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hLsK).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLsK).symm.injective)
  have hBns' : ¬ Group.IsSolvable
      ↥((conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x).subgroupOf K) :=
    fun hs' => hLs'ns (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hLs'K).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLs'K).symm.injective)
  have hF4 : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨m, by rw [Nat.card_eq_fintype_card, hF]⟩
  obtain ⟨m', hm', hm1', hsh, hlin, hUs, hO, hRsyl⟩ := exam_block E hcfg hs hsR hs2 h4
  have hUscard := ((E.U_s_values hcfg hs hsR hs2 hxT hxS).2 hc).1
  have hn3 := Five.three_le_of_four_lt_two_pow h4
  have hbig : 2 < Nat.card (blockU L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) := by
    rw [hUscard]
    calc 2 < 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (3 * n / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hzp : Nat.card (Subgroup.zpowers s) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hs2)
  have hpc := exam_K_pCore_le E hcfg hs hsR hs2 hc h4 hx hxS hK
  have hBtop : (L ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf K ≠ ⊤ := by
    intro h
    have hKLs : K ≤ L ⊓ Subgroup.centralizer ({s} : Set G) := Subgroup.subgroupOf_eq_top.mp h
    have hKeq : K = L ⊓ Subgroup.centralizer ({s} : Set G) := le_antisymm hKLs hLsK
    have hle : blockU L ⊓ Subgroup.centralizer ({s} : Set G) ≤ Subgroup.zpowers s := by
      rw [hKeq, hO] at hpc
      exact hpc
    have := Subgroup.card_le_of_le hle
    omega
  have hBtop' : (conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x).subgroupOf K ≠ ⊤ := by
    intro h
    have hKLs : K ≤ conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x :=
      Subgroup.subgroupOf_eq_top.mp h
    have hKeq : K = conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x := le_antisymm hKLs hLs'K
    have hle : conjR (blockU L) x ⊓ Subgroup.centralizer ({s} : Set G) ≤ Subgroup.zpowers s := by
      rw [hKeq, hcfgK.pCore', exam_blockU_conj hxs L hUs] at hpc
      exact hpc
    have h1 := Subgroup.card_le_of_le hle
    have h2 := E.card_conjR_U_inf_centralizer hcfg hs hsR hs2 hxT
    omega
  have hne : (L ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf K ≠
      (conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x).subgroupOf K := by
    intro h
    have h1 := Subgroup.subgroupOf_inj.mp h
    rw [inf_eq_left.mpr hLsK, inf_eq_left.mpr hLs'K] at h1
    exact hcfgK.U_ne (congrArg blockU h1)
  obtain ⟨hgen, hsw⟩ := exam_sp4_swap hF4 e hRX hRB hRB' hBp hBp' hBns hBns' hBtop hBtop' hne
  have hKeq : L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
      conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x = K := by
    refine le_antisymm hKs ?_
    have h1 : (L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
        conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x).subgroupOf K = ⊤ := by
      rw [Subgroup.subgroupOf_sup hLsK hLs'K]
      exact hgen
    exact Subgroup.subgroupOf_eq_top.mp h1
  refine ⟨F, hFfield, hFfin, ?_, (MulEquiv.subgroupCongr hKeq).trans e, fun β hβ => ?_⟩
  · rw [hF]
    congr 1
    omega
  · set β' : MulAut ↥K := MulAut.congr (MulEquiv.subgroupCongr hKeq) β with hβ'
    have hβ'x : ∀ k : ↥K, ((β' k : ↥K) : G) = x * (k : G) * x⁻¹ := by
      intro k
      have := hβ ((MulEquiv.subgroupCongr hKeq).symm k)
      simpa [hβ', MulAut.congr_apply] using this
    have hcongr : MulAut.congr ((MulEquiv.subgroupCongr hKeq).trans e) β = MulAut.congr e β' := by
      ext y
      simp [hβ', MulAut.congr_apply]
    rw [hcongr]
    refine hsw β' ?_
    have hinv := exam_conjR_inv E hcfg hx
    have hle : ((L ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf K).map β'.toMonoidHom ≤
        (conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x).subgroupOf K := by
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      show ((β' y : ↥K) : G) ∈ conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x
      rw [← hinv, mem_conjR, hβ'x y]
      have e1 : x⁻¹ * (x * (y : G) * x⁻¹) * x⁻¹⁻¹ = (y : G) := by group
      rw [e1]
      exact Subgroup.mem_subgroupOf.mp hy
    have hcardB : Nat.card ((L ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf K) =
        Nat.card (L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLsK).toEquiv
    have hcardB' : Nat.card ((conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x).subgroupOf K) =
        Nat.card (conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLs'K).toEquiv
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective β'.injective, hcardB, hcardB', card_conjR]

theorem lemma2_4_23_five_of_examK
    (E : Lin2Hyp) (a39 : A39ForSQTKCat)
    (hD : Lemma2_4_23_five_examK) : Lemma2_4_23_five :=
  lemma2_4_23_five_of_exam E (lemma2_4_23_five_exam_of E a39 hD)

end CFSG.QuasithinUnique.Lin2
