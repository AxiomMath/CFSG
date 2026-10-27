module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6CtrlNDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Restrict
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Lemma51B
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracPiece
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6CtrlDefs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

structure Sec6T67Facts (n : ℕ) : Prop where
  deg : n = 8 ∨ n = 11
  simple : ∀ (Q : Type) [Group Q], IsSec6MType n Q → IsSimpleGroup Q
  cen : ∀ (Q : Type) [Group Q], IsSec6MType n Q → ∀ c : Q, orderOf c = 2 →
    IsDoubleCoverOfAlt ↥(centralizer ({c} : Set Q)) n
  conj : ∀ (Q : Type) [Group Q], IsSec6MType n Q → ∀ a b : Q, orderOf a = 2 → orderOf b = 2 →
    IsConj a b
  gen : ∀ (Q : Type) [Group Q] [Finite Q], IsSec6MType n Q → ∀ x y : Q, orderOf x = 2 →
    orderOf y = 2 → x ≠ y → x * y = y * x →
      centralizer ({x} : Set Q) ⊔ centralizer ({y} : Set Q) = ⊤
  cf : ∀ (Q : Type) [Group Q], IsQuasisimple Q →
    (Nonempty (Q ≃* Blueprint.NativeSporadic.McL) ∨ Nonempty (Q ≃* Blueprint.NativeSporadic.Ly)) →
      center Q = ⊥

private theorem t67Facts_of
    {n : ℕ} (hdeg : n = 8 ∨ n = 11)
    (hgenM : ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* Blueprint.NativeSporadic.McL) →
      ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x ≠ y → x * y = y * x →
        centralizer ({x} : Set G) ⊔ centralizer ({y} : Set G) = ⊤)
    (hgenL : ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* Blueprint.NativeSporadic.Ly) →
      ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x ≠ y → x * y = y * x →
        centralizer ({x} : Set G) ⊔ centralizer ({y} : Set G) = ⊤) :
    Sec6T67Facts n := by
  refine ⟨hdeg, fun Q _ h => ?_, fun Q _ h c hc => ?_, fun Q _ h a b ha hb => ?_,
    fun Q _ _ h => ?_, fun Q _ hq h => Sec6L51B.center_eq_bot_of_McL_or_Ly hq h⟩
  · rcases h with ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
    · exact @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.McL.isSimpleGroup_McL e
    · exact @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.Ly.fam_ly_simplicity.2.2 e
  · rcases h with ⟨rfl, ⟨e⟩⟩ | ⟨rfl, ⟨e⟩⟩
    · exact Sec6L51B.isDoubleCoverOfAlt_centralizer_McL e c hc
    · exact Sec6L51B.isDoubleCoverOfAlt_centralizer_Ly e c hc
  · rcases h with ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
    · exact Sec6L51B.isConj_of_equiv_McL e a b ha hb
    · exact Sec6L51B.isConj_of_equiv_Ly e a b ha hb
  · rcases h with ⟨-, he⟩ | ⟨-, he⟩
    · exact hgenM Q he
    · exact hgenL Q he

section Thm67

variable {X : Type} [Group X] [Finite X] {n : ℕ} {t : X}

private theorem t67_isPCompIn {H L : Subgroup X} (h : Sec6KComp X n H L) : IsPCompIn 2 H L := by
  rcases h with ⟨⟨u, hu⟩, -⟩ | ⟨hM, -⟩
  · exact hu.2.2.1
  · exact hM.1

private theorem t67_le_of_sec6KComp {H L : Subgroup X} (h : Sec6KComp X n H L) : L ≤ H :=
  (t67_isPCompIn h).1

private theorem t67_twoGenQuasi {H L : Subgroup X} (h : Sec6KComp X n H L) : IsTwoGenQuasi ↥L :=
  (isTwoGenQuasi_subgroupOf_iff (t67_isPCompIn h).1).1
    (isPComponent_two_iff.1 (t67_isPCompIn h).2).2

private theorem t67_subnormal {H L : Subgroup X} (h : Sec6KComp X n H L) :
    (L.subgroupOf H).IsSubnormal :=
  (isPComponent_two_iff.1 (t67_isPCompIn h).2).1

private theorem t67_le_K {H L : Subgroup X} (h : Sec6KComp X n H L) : L ≤ Sec6K X n H :=
  le_sSup (s := {L | Sec6KComp X n H L}) h

private theorem t67_le_M {H M : Subgroup X} (h : Sec6MComp X n H M) : M ≤ Sec6M X n H :=
  le_sSup (s := {M | Sec6MComp X n H M}) h

private theorem t67_le_A {H A : Subgroup X} (h : Sec5Comp X n H A) : A ≤ K0 X n H := by
  rw [K0_eq_sSup_sec5Comp]
  exact le_sSup (s := {A | Sec5Comp X n H A}) h

private theorem t67_A_le_K (H : Subgroup X) : K0 X n H ≤ Sec6K X n H := by
  rw [sec6K_eq]
  exact le_sup_left

private theorem t67_mem_centralizer_iff {H : Subgroup X} {z : X} :
    z ∈ centralizer (H : Set X) ↔ H ≤ cen z := by
  rw [mem_centralizer_iff]
  exact ⟨fun h a ha => mem_centralizer_singleton_iff.2 (h a ha),
    fun h a ha => mem_centralizer_singleton_iff.1 (h ha)⟩

private theorem t67_comm_mem {H M J : Subgroup X} (hM : IsPCompIn 2 H M)
    (hJ : IsPCompIn 2 H J) (hne : M ≠ J) {m j : X} (hm : m ∈ M) (hj : j ∈ J) :
    ⁅m, j⁆ ∈ pPrimeCoreOf 2 M := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne' : M.subgroupOf H ≠ J.subgroupOf H := by
    intro h
    apply hne
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hM.1, inf_of_le_left hJ.1] at h
    exact h
  obtain ⟨-, -, hcore, -⟩ :=
    (distinct_p_components_core_commutation 2 Nat.prime_two _ _ hM.2 hJ.2).2 hne'
  have hc : ⁅(⟨m, hM.1 hm⟩ : ↥H), (⟨j, hJ.1 hj⟩ : ↥H)⁆ ∈
      (pPrimeCore 2 ↥(M.subgroupOf H)).map (M.subgroupOf H).subtype :=
    (hcore.trans inf_le_left) (Subgroup.commutator_mem_commutator hm hj)
  obtain ⟨y, hy, hyeq⟩ := hc
  let e : ↥(M.subgroupOf H) ≃* ↥M := Subgroup.subgroupOfEquivOfLe hM.1
  have hey : e y ∈ pPrimeCore 2 ↥M := by
    rw [← pPrimeCore_map_iso 2 e]
    exact ⟨y, hy, rfl⟩
  refine ⟨e y, hey, ?_⟩
  change ((y : ↥H) : X) = ⁅m, j⁆
  exact congrArg Subtype.val hyeq

private theorem t67_commute {H M J : Subgroup X} (hM : IsPCompIn 2 H M) (hJ : IsPCompIn 2 H J)
    (hne : M ≠ J) (hO : pPrimeCoreOf 2 M = ⊥) {m j : X} (hm : m ∈ M) (hj : j ∈ J) :
    m * j = j * m := by
  have h := t67_comm_mem hM hJ hne hm hj
  rw [hO, mem_bot] at h
  exact commutatorElement_eq_one_iff_mul_comm.1 h

private theorem t67_le_centralizer {H M J : Subgroup X} (hM : IsPCompIn 2 H M)
    (hJ : IsPCompIn 2 H J) (hne : M ≠ J) (hO : pPrimeCoreOf 2 M = ⊥) :
    J ≤ centralizer (M : Set X) :=
  fun _ hj => mem_centralizer_iff.2 fun _ hm => t67_commute hM hJ hne hO hm hj

private theorem t67_subnormal_mono {L D D' : Subgroup X} (hDD' : D ≤ D')
    (h : (L.subgroupOf D').IsSubnormal) : (L.subgroupOf D).IsSubnormal := by
  have h1 : L.subgroupOf D = (L.subgroupOf D').comap (Subgroup.inclusion hDD') := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_inclusion]
  rw [h1]
  exact h.comap _

private theorem t67_odd_eq_bot {H L : Subgroup X} (h : Sec6KComp X n H L)
    (hO : oddCoreOf H = ⊥) : pPrimeCoreOf 2 L = ⊥ :=
  le_bot_iff.1 (hO ▸ pPrimeCoreOf_le_oddCoreOf (t67_isPCompIn h).1 (t67_subnormal h))

private theorem t67_oTwo_eq {L : Subgroup X} (hq : IsTwoGenQuasi ↥L) : oTwoPrimeOf L = L :=
  oTwoPrimeOf_eq_self_of_primeResidual hq.1

private theorem t67_piece_eq {L : Subgroup X} {y : X} (hq : IsTwoGenQuasi ↥L)
    (hy : L ≤ cen y) : sec6Piece L y = L := by
  unfold sec6Piece
  rw [inf_of_le_left hy]
  exact t67_oTwo_eq hq

private theorem t67_piece_le {L : Subgroup X} {y : X} : sec6Piece L y ≤ L :=
  (oTwoPrimeOf_le _).trans inf_le_left

private theorem t67_exists_noncomm {L : Subgroup X} (hq : IsTwoGenQuasi ↥L) :
    ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := by
  by_contra hno
  push Not at hno
  obtain ⟨a, b, hab⟩ := hq.2.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have h : a * b = b * a := Subtype.ext (hno a a.2 b b.2)
  have h2 := congrArg (fun z : ↥L => ((z : ↥L ⧸ pPrimeCore 2 ↥L) :
    (↥L ⧸ pPrimeCore 2 ↥L) ⧸ center (↥L ⧸ pPrimeCore 2 ↥L))) h
  simpa only [QuotientGroup.mk_mul] using h2

private theorem t67_not_sec5_of_M (hT : Sec6T67Facts n) {H H' L : Subgroup X}
    (h5 : Sec5Comp X n H L) (hM : Sec6MComp X n H' L) : False := by
  have hdc := h5.2
  have hcen := hT.cf _ hdc.1 hM.1.2.1
  have h2 := hdc.2.1
  rw [hcen, Subgroup.card_bot] at h2
  exact absurd h2 (by norm_num)

private theorem t67_K_le (H : Subgroup X) : Sec6K X n H ≤ H :=
  sSup_le fun _ hL => t67_le_of_sec6KComp hL

private theorem t67_M_le_K (H : Subgroup X) : Sec6M X n H ≤ Sec6K X n H := by
  rw [sec6K_eq]
  exact le_sup_right

private theorem t67_Mt_ne_bot (hS : Sec6Setting X n t) : Sec6M X n (cen t) ≠ ⊥ := by
  obtain ⟨M, hM⟩ := hS.choice.hasM
  have hq := isTwoGenQuasi_of_isMLIntr (isMLIntr_iff.2 hM.1)
  intro hbot
  have hMbot : M = ⊥ := le_bot_iff.1 (hbot ▸ le_sSup hM)
  subst hMbot
  obtain ⟨a, b, hab⟩ := hq.2.2.2
  exact hab (Subsingleton.elim (a * b) (b * a))

private theorem t67_not_top_le_cen (hS : Sec6Setting X n t) : ¬ (⊤ : Subgroup X) ≤ cen t := by
  intro h
  haveI := hS.cex.simple
  have hct : t ∈ center X :=
    mem_center_iff.2 fun g => mem_centralizer_singleton_iff.1 (h (mem_top g))
  have hbot : center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with hb | htop
    · exact hb
    · exfalso
      obtain ⟨a, b, hab⟩ := hS.cex.nonabelian
      exact hab (mem_center_iff.1 (htop ▸ mem_top b) a)
  rw [hbot, mem_bot] at hct
  have h2 := hS.choice.inv
  rw [hct, orderOf_one] at h2
  exact absurd h2 (by norm_num)

private theorem t67_zStar_le (H : Subgroup X) : zStar H ≤ H := inf_le_left

private theorem t67_oddL (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) {L : Subgroup X}
    (hL : Sec6KComp X n (cen t) L) : pPrimeCoreOf 2 L = ⊥ :=
  le_bot_iff.1 (hodd ▸ pPrimeCoreOf_le_oddCoreOf (t67_le_K hL)
    (t67_subnormal_mono (t67_K_le (cen t)) (t67_subnormal hL)))

private theorem t67_Kt_cen (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) {L L' : Subgroup X}
    (hL : Sec6KComp X n (cen t) L) (hL' : Sec6KComp X n (cen t) L') (hne : L ≠ L') :
    L' ≤ centralizer (L : Set X) :=
  t67_le_centralizer (t67_isPCompIn hL) (t67_isPCompIn hL') hne (t67_oddL hodd hL)

private theorem t67_Mt_le_cen_At (hT : Sec6T67Facts n) (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) :
    Sec6M X n (cen t) ≤ centralizer (K0 X n (cen t) : Set X) := by
  rw [le_centralizer_iff, K0_eq_sSup_sec5Comp]
  refine sSup_le fun A hA => ?_
  rw [le_centralizer_iff]
  unfold Sec6M
  refine sSup_le fun M hM => ?_
  refine t67_Kt_cen hodd (Or.inl hA) (Or.inr hM) fun h => ?_
  subst h
  exact t67_not_sec5_of_M hT hA hM

private theorem t67_oddA (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) :
    pPrimeCoreOf 2 (K0 X n (cen t)) = ⊥ := by
  have h : oddCoreOf (K0 X n (cen t)) ≤ oddCoreOf (Sec6K X n (cen t)) :=
    le_oddCoreOf_of_normalized ((oddCoreOf_le _).trans (t67_A_le_K _))
      ((t67_K_le _).trans ((K0_cen_normal n t).trans (normalizer_le_normalizer_pPrimeCoreOf _)))
      (odd_card_oddCoreOf _)
  rw [hodd] at h
  exact le_bot_iff.1 h

private theorem t67_zStar_le_cen (hT : Sec6T67Facts n) (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) :
    zStar (K0 X n (cen t)) ≤ centralizer (Sec6K X n (cen t) : Set X) := by
  intro z hz
  have hzA : z ∈ K0 X n (cen t) := hz.1
  have hzc : ∀ k ∈ K0 X n (cen t), ⁅k, z⁆ ∈ pPrimeCoreOf 2 (K0 X n (cen t)) := hz.2.2.2
  rw [t67_oddA hodd] at hzc
  rw [t67_mem_centralizer_iff, sec6K_eq]
  refine sup_le (fun k hk => ?_) ?_
  · exact mem_centralizer_singleton_iff.2
      (commutatorElement_eq_one_iff_mul_comm.1 (mem_bot.1 (hzc k hk)))
  · exact t67_mem_centralizer_iff.1 ((le_centralizer_iff.1 (t67_Mt_le_cen_At hT hodd)) hzA)

private theorem t67_zStar_le_Q (hT : Sec6T67Facts n) (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) :
    zStar (K0 X n (cen t)) ≤ Sec6Q X n (cen t) := by
  intro z hz
  have hzc := t67_zStar_le_cen hT hodd hz
  refine mem_inf.2 ⟨?_, mem_QOf_iff.2 ⟨centralizer_le_normalizer _ hzc, fun k hk => ?_⟩⟩
  · exact ((t67_zStar_le _).trans ((t67_A_le_K _).trans (t67_K_le _))) hz
  · rw [commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_iff.1 hzc k hk)]
    exact one_mem _

private theorem t67_base_le_MQ (hT : Sec6T67Facts n) (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) :
    Sec6Base X n t ≤ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) :=
  sup_le le_sup_left (le_sup_of_le_right (t67_zStar_le_Q hT hodd))

private theorem t67_base_le_K : Sec6Base X n t ≤ Sec6K X n (cen t) :=
  sup_le (t67_M_le_K _) ((t67_zStar_le _).trans (t67_A_le_K _))

private theorem t67_base_le_cen_A (hT : Sec6T67Facts n) (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) :
    Sec6Base X n t ≤ centralizer (K0 X n (cen t) : Set X) := by
  refine sup_le (t67_Mt_le_cen_At hT hodd) fun z hz => ?_
  rw [t67_mem_centralizer_iff]
  exact (t67_A_le_K _).trans (t67_mem_centralizer_iff.1 (t67_zStar_le_cen hT hodd hz))

private theorem t67_oddK_le (x : X) : oddCoreOf (Sec6K X n (cen x)) ≤ oddCoreOf (cen x) :=
  le_oddCoreOf_of_normalized ((oddCoreOf_le _).trans (t67_K_le _))
    ((Sec6K_cen_normal n x).trans (normalizer_le_normalizer_pPrimeCoreOf _))
    (odd_card_oddCoreOf _)

private theorem t67_K_le_of_Q (h61 : Sec6L61 X n t) {z : X} (hzQ : z ∈ Sec6Q X n (cen t))
    (hz2 : orderOf z = 2) (hO : oddCoreOf (cen z) = ⊥) :
    Sec6K X n (cen z) ≤ Sec6K X n (cen t) := by
  have hcov := h61.a z hzQ hz2
  unfold Sec6Covers at hcov
  rw [hcov]
  refine sup_le ?_ inf_le_right
  exact ((t67_oddK_le z).trans (le_of_eq hO)).trans bot_le

private def t67VE (n : ℕ) (E : Subgroup X) : Subgroup X :=
  ⨆ (y : X) (_ : y ∈ E) (_ : orderOf y = 2), Sec6K X n (cen y)

private theorem t67_le_VE {E : Subgroup X} {y : X} (hy : y ∈ E) (hy2 : orderOf y = 2) :
    Sec6K X n (cen y) ≤ t67VE n E :=
  le_iSup_of_le y (le_iSup_of_le hy (le_iSup_of_le hy2 le_rfl))

private theorem t67_VE_le {E W : Subgroup X}
    (h : ∀ y ∈ E, orderOf y = 2 → Sec6K X n (cen y) ≤ W) : t67VE n E ≤ W :=
  iSup_le fun y => iSup_le fun hy => iSup_le fun hy2 => h y hy hy2

private theorem t67_map_map_symm (φ : X ≃* X) (K : Subgroup X) :
    (K.map φ.symm.toMonoidHom).map φ.toMonoidHom = K := by
  rw [Subgroup.map_map]
  have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id X := by ext x; simp
  rw [this, Subgroup.map_id]

private theorem t67_map_symm_map (φ : X ≃* X) (K : Subgroup X) :
    (K.map φ.toMonoidHom).map φ.symm.toMonoidHom = K := by
  rw [Subgroup.map_map]
  have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id X := by ext x; simp
  rw [this, Subgroup.map_id]

private theorem t67VE_map_le (φ : X ≃* X) (E : Subgroup X) :
    (t67VE n E).map φ.toMonoidHom ≤ t67VE n (E.map φ.toMonoidHom) := by
  unfold t67VE
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun hx2 => ?_
  rw [← Subgroup.map_le_iff_le_comap, Sec6K_map, cen_map]
  have hy : φ x ∈ E.map φ.toMonoidHom := Subgroup.mem_map_of_mem _ hx
  have hy2 : orderOf (φ x) = 2 := (MulEquiv.orderOf_eq φ x).trans hx2
  exact le_iSup_of_le (φ x) (le_iSup_of_le hy (le_iSup_of_le hy2 le_rfl))

private theorem t67VE_map (φ : X ≃* X) (E : Subgroup X) :
    (t67VE n E).map φ.toMonoidHom = t67VE n (E.map φ.toMonoidHom) := by
  refine le_antisymm (t67VE_map_le φ E) ?_
  have h := Subgroup.map_mono (f := φ.toMonoidHom)
      (t67VE_map_le (n := n) φ.symm (E.map φ.toMonoidHom))
  rwa [t67_map_map_symm, t67_map_symm_map] at h

private theorem t67_le_normalizer_of_VE {E V H : Subgroup X} (hH : H ≤ normalizer (E : Set X))
    (hE : t67VE n E = V) : H ≤ normalizer (V : Set X) := by
  intro g hg
  apply mem_normalizer_of_map_conj_eq
  rw [← hE, t67VE_map, map_conj_eq_of_mem_normalizer (hH hg)]

private theorem t67_normalizer_le_normalizer_Z (K : Subgroup X) :
    normalizer (K : Set X) ≤ normalizer ((K ⊓ centralizer (K : Set X) : Subgroup X) : Set X) := by
  intro g hg
  rw [mem_normalizer_iff] at hg ⊢
  intro h
  rw [mem_inf, mem_inf, ← hg h]
  refine and_congr_right fun _ => ?_
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hc k hk
    have hk' : g⁻¹ * k * g ∈ K :=
      (hg (g⁻¹ * k * g)).2 (by rwa [show g * (g⁻¹ * k * g) * g⁻¹ = k by group])
    have := hc _ hk'
    calc k * (g * h * g⁻¹) = g * ((g⁻¹ * k * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * k * g)) * g⁻¹ := by rw [this]
      _ = g * h * g⁻¹ * k := by group
  · intro hc k hk
    have hk' : g * k * g⁻¹ ∈ K := (hg k).1 hk
    have := hc _ hk'
    have e1 : k * h = g⁻¹ * ((g * k * g⁻¹) * (g * h * g⁻¹)) * g := by group
    have e2 : h * k = g⁻¹ * ((g * h * g⁻¹) * (g * k * g⁻¹)) * g := by group
    rw [e1, e2, this]

private theorem t67_pPrimeCore_eq_bot {L : Subgroup X} (h : pPrimeCoreOf 2 L = ⊥) :
    pPrimeCore 2 ↥L = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 h

private theorem t67_quotEquiv {L : Subgroup X} (h : pPrimeCoreOf 2 L = ⊥) :
    Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* ↥L) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (t67_pPrimeCore_eq_bot h)).trans QuotientGroup.quotientBot⟩

private theorem t67_type_M {H M : Subgroup X} (hM : Sec6MComp X n H M)
    (hO : pPrimeCoreOf 2 M = ⊥) : IsSec6MType n ↥M := by
  obtain ⟨e⟩ := t67_quotEquiv hO
  exact hM.2.congr e

private theorem t67_dc_A {H A : Subgroup X} (hA : Sec5Comp X n H A) (hO : pPrimeCoreOf 2 A = ⊥) :
    IsDoubleCoverOfAlt ↥A n := by
  obtain ⟨e⟩ := t67_quotEquiv hO
  exact GH74.GLS.Stage12.McLRec.isDoubleCoverOfAlt_congr e hA.2

private theorem t67_card_dc {K : Type} [Group K] [Finite K] {m : ℕ} (hm : 2 ≤ m)
    (h : IsDoubleCoverOfAlt K m) : Nat.card K = m.factorial := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin, hc] at h1
  rw [h1]
  exact Nat.div_mul_cancel (Nat.dvd_factorial (by norm_num) hm)

private theorem t67_two_le (hT : Sec6T67Facts n) : 2 ≤ n := by
  rcases hT.deg with rfl | rfl <;> norm_num

private theorem t67_four_le (hT : Sec6T67Facts n) : 4 ≤ n := by
  rcases hT.deg with rfl | rfl <;> norm_num

private theorem t67_exists_noncentral (hT : Sec6T67Facts n) {K : Type} [Group K]
    (h : IsDoubleCoverOfAlt K n) : ∃ u : K, u ^ 2 = 1 ∧ u ∉ center K := by
  rcases hT.deg with rfl | rfl
  · exact GH74.GLS.Stage12.McLRec.exists_noncentral_involution_of_doubleCover h
  · exact Sporadic.Recognition.LyonsSims.exists_noncentral_involution_of_doubleCover_eleven h

private theorem t67_center_eq_bot (hT : Sec6T67Facts n) {Q : Type} [Group Q] (hQ : IsSec6MType n Q)
    (hnc : ∃ a b : Q, a * b ≠ b * a) : center Q = ⊥ := by
  haveI := hT.simple Q hQ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (mem_center_iff.1 (h ▸ mem_top b) a)

private theorem t67_Z_eq_bot (hT : Sec6T67Facts n) {H M : Subgroup X} (hM : Sec6MComp X n H M)
    (hO : pPrimeCoreOf 2 M = ⊥) : M ⊓ centralizer (M : Set X) = ⊥ := by
  have hty := t67_type_M hM hO
  obtain ⟨a, ha, b, hb, hab⟩ := t67_exists_noncomm (t67_twoGenQuasi (Or.inr hM))
  have hc := t67_center_eq_bot hT hty ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  refine le_bot_iff.1 fun x hx => ?_
  have hxc : (⟨x, hx.1⟩ : ↥M) ∈ center ↥M := mem_center_iff.2 fun g =>
    Subtype.ext (mem_centralizer_iff.1 hx.2 g g.2)
  rw [hc, mem_bot] at hxc
  exact mem_bot.2 (congrArg Subtype.val hxc)

private theorem t67_decomp (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) {L : Subgroup X}
    (hL : Sec6KComp X n (cen t) L) {y : X} (hy : y ∈ Sec6K X n (cen t)) :
    ∃ m ∈ L, ∃ d ∈ Subgroup.centralizer (L : Set X), m * d = y := by
  have hle : Sec6K X n (cen t) ≤ L ⊔ centralizer (L : Set X) := by
    refine sSup_le fun L' hL' => ?_
    by_cases h : L' = L
    · rw [h]
      exact le_sup_left
    · exact le_sup_of_le_right (t67_Kt_cen hodd hL hL' (Ne.symm h))
  have hmem : y ∈ ((L ⊔ centralizer (L : Set X) : Subgroup X) : Set X) := hle hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L _ (centralizer_le_normalizer _)] at hmem
  exact Set.mem_mul.1 hmem

private theorem t67_sq_of_decomp {L : Subgroup X} (hZ : L ⊓ centralizer (L : Set X) = ⊥)
    {m d y : X} (hm : m ∈ L) (hd : d ∈ Subgroup.centralizer (L : Set X)) (hy : m * d = y)
    (hy2 : y ^ 2 = 1) : m ^ 2 = 1 := by
  have hcomm : Commute m d := mem_centralizer_iff.1 hd m hm
  have h1 : m ^ 2 = (d ^ 2)⁻¹ := by
    have h := hy2
    rw [← hy, hcomm.mul_pow 2] at h
    exact eq_inv_of_mul_eq_one_left h
  have h2 : m ^ 2 ∈ L ⊓ centralizer (L : Set X) := by
    refine Subgroup.mem_inf.2 ⟨pow_mem hm 2, ?_⟩
    rw [h1]
    exact inv_mem (pow_mem hd 2)
  rw [hZ, mem_bot] at h2
  exact h2

private theorem t67_sq_eq_one {y : X} (hy2 : orderOf y = 2) : y ^ 2 = 1 := by
  rw [← hy2]
  exact pow_orderOf_eq_one y

private theorem t67_map_cen_le {M : Subgroup X} {w : X} (hw : w ∈ M) :
    (centralizer ({⟨w, hw⟩} : Set ↥M)).map M.subtype ≤ M ⊓ cen w := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y.2, mem_centralizer_singleton_iff.2
    (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy))⟩

private theorem t67_piece_inv (hT : Sec6T67Facts n) (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥)
    {M : Subgroup X} (hM : Sec6MComp X n (cen t) M) {y : X} (hy : y ∈ Sec6K X n (cen t))
    (hy2 : orderOf y = 2) :
    ∃ w w' : X, w ∈ M ∧ w' ∈ M ∧ orderOf w = 2 ∧ orderOf w' = 2 ∧ w ≠ w' ∧ w * w' = w' * w ∧
      w ∈ sec6Piece M y ∧ w' ∈ sec6Piece M y := by
  have hO := t67_oddL hodd (Or.inr hM)
  have hZ := t67_Z_eq_bot hT hM hO
  have hty := t67_type_M hM hO
  obtain ⟨m, hm, d, hd, hmd⟩ := t67_decomp hodd (Or.inr hM) hy
  have hm2 := t67_sq_of_decomp hZ hm hd hmd (t67_sq_eq_one hy2)
  obtain ⟨w, hwM, hw2, hkey⟩ : ∃ w ∈ M, orderOf w = 2 ∧ ∀ u ∈ M, u * w = w * u → u * y = y * u := by
    by_cases hm1 : m = 1
    · obtain ⟨w, hwM, hw2⟩ :=
        Sec6L51B.exists_involution_of_isTwoGenQuasi (t67_twoGenQuasi (Or.inr hM))
      refine ⟨w, hwM, hw2, fun u hu _ => ?_⟩
      rw [← hmd, hm1, one_mul]
      exact mem_centralizer_iff.1 hd u hu
    · refine ⟨m, hm, orderOf_eq_prime hm2 hm1, fun u hu hum => ?_⟩
      rw [← hmd]
      have hud : u * d = d * u := mem_centralizer_iff.1 hd u hu
      calc u * (m * d) = (u * m) * d := by group
        _ = (m * u) * d := by rw [hum]
        _ = m * (u * d) := by group
        _ = m * (d * u) := by rw [hud]
        _ = (m * d) * u := by group
  have hcdc := hT.cen ↥M hty ⟨w, hwM⟩ (by rw [Subgroup.orderOf_mk]; exact hw2)
  obtain ⟨u, hu2, hunc⟩ := t67_exists_noncentral hT hcdc
  have huc : (u : ↥M) * ⟨w, hwM⟩ = ⟨w, hwM⟩ * (u : ↥M) := mem_centralizer_singleton_iff.1 u.2
  have huc' : ((u : ↥M) : X) * w = w * ((u : ↥M) : X) := congrArg Subtype.val huc
  have hu2' : ((u : ↥M) : X) ^ 2 = 1 := by
    have := congrArg (fun z : ↥(centralizer ({⟨w, hwM⟩} : Set ↥M)) => ((z : ↥M) : X)) hu2
    simpa using this
  have hu1 : ((u : ↥M) : X) ≠ 1 := by
    intro h
    apply hunc
    have : u = 1 := Subtype.ext (Subtype.ext h)
    rw [this]
    exact one_mem _
  have hne : w ≠ ((u : ↥M) : X) := by
    intro h
    apply hunc
    rw [mem_center_iff]
    intro v
    have hv : (v : ↥M) * ⟨w, hwM⟩ = ⟨w, hwM⟩ * (v : ↥M) := mem_centralizer_singleton_iff.1 v.2
    have hu : (u : ↥M) = ⟨w, hwM⟩ := Subtype.ext h.symm
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hu]; exact hv)
  have hpiece : ∀ z ∈ M, z * w = w * z → z ^ 2 = 1 → z ∈ sec6Piece M y := fun z hz hzw hz2 =>
    mem_oTwoPrimeOf ⟨hz, mem_centralizer_singleton_iff.2 (hkey z hz hzw)⟩ 1 (by simpa using hz2)
  refine ⟨w, (u : ↥M), hwM, (u : ↥M).2, hw2, orderOf_eq_prime hu2' hu1, hne, huc'.symm,
    hpiece w hwM rfl (t67_sq_eq_one hw2), hpiece _ (u : ↥M).2 huc' hu2'⟩

private theorem t67_cenM_dc (hT : Sec6T67Facts n) {H M : Subgroup X} (hM : Sec6MComp X n H M)
    (hO : pPrimeCoreOf 2 M = ⊥) {w : X} (hwM : w ∈ M) (hw2 : orderOf w = 2) :
    IsDoubleCoverOfAlt ↥(M ⊓ cen w) n := by
  have hdc := hT.cen ↥M (t67_type_M hM hO) ⟨w, hwM⟩ (by rw [Subgroup.orderOf_mk]; exact hw2)
  have heq : (centralizer ({⟨w, hwM⟩} : Set ↥M)).map M.subtype = M ⊓ cen w := by
    refine le_antisymm (t67_map_cen_le hwM) ?_
    rintro x ⟨hxM, hxw⟩
    exact ⟨⟨x, hxM⟩, mem_centralizer_singleton_iff.2
      (Subtype.ext (mem_centralizer_singleton_iff.1 hxw)), rfl⟩
  exact GH74.GLS.Stage12.McLRec.isDoubleCoverOfAlt_congr
    ((Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).trans
      (MulEquiv.subgroupCongr heq)) hdc

private theorem t67_cenM_le_K (hT : Sec6T67Facts n) (hC : Sec6CtrlAt X n t)
    (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) {M : Subgroup X} (hM : Sec6MComp X n (cen t) M)
    {w : X} (hwM : w ∈ M) (hw2 : orderOf w = 2) : M ⊓ cen w ≤ Sec6K X n (cen w) := by
  have hO := t67_oddL hodd (Or.inr hM)
  have hdc := t67_cenM_dc hT hM hO hwM hw2
  have hpr := primeResidual_two_eq_top_of_isDoubleCoverOfAlt (t67_four_le hT) hdc
  have hpc : sec6Piece M w = M ⊓ cen w := oTwoPrimeOf_eq_self_of_primeResidual hpr
  have hwMQ : w ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) := Subgroup.mem_sup_left (t67_le_M hM hwM)
  obtain ⟨F, hF, hPF⟩ := hC.land w hwMQ hw2 M (Or.inr hM)
  rw [← hpc]
  exact hPF.trans (t67_le_K hF)

private theorem t67_gen (hT : Sec6T67Facts n) (hC : Sec6CtrlAt X n t)
    (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) {M : Subgroup X} (hM : Sec6MComp X n (cen t) M)
    {w w' : X} (hw : w ∈ M) (hw' : w' ∈ M) (hw2 : orderOf w = 2) (hw2' : orderOf w' = 2)
    (hne : w ≠ w') (hc : w * w' = w' * w) :
    M ≤ Sec6K X n (cen w) ⊔ Sec6K X n (cen w') := by
  have hO := t67_oddL hodd (Or.inr hM)
  have hg := hT.gen ↥M (t67_type_M hM hO) ⟨w, hw⟩ ⟨w', hw'⟩
    (by rw [Subgroup.orderOf_mk]; exact hw2) (by rw [Subgroup.orderOf_mk]; exact hw2')
    (fun h => hne (congrArg Subtype.val h)) (Subtype.ext hc)
  have hmap := congrArg (Subgroup.map M.subtype) hg
  rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at hmap
  rw [← hmap]
  exact sup_le_sup ((t67_map_cen_le hw).trans (t67_cenM_le_K hT hC hodd hM hw hw2))
    ((t67_map_cen_le hw').trans (t67_cenM_le_K hT hC hodd hM hw' hw2'))

private theorem t67_le_V {w : X} (hwM : w ∈ Sec6M X n (cen t)) (hw2 : orderOf w = 2) :
    Sec6K X n (cen w) ≤ sec6V X n t :=
  le_iSup_of_le w (le_iSup_of_le hwM (le_iSup_of_le hw2 le_rfl))

private theorem t67_inf_AM (hT : Sec6T67Facts n) (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥)
    {A M : Subgroup X} (hA : Sec5Comp X n (cen t) A) (hM : Sec6MComp X n (cen t) M) :
    A ⊓ M = ⊥ := by
  have hne : M ≠ A := fun h => by
    subst h
    exact t67_not_sec5_of_M hT hA hM
  have hAc := t67_Kt_cen hodd (Or.inr hM) (Or.inl hA) hne
  refine le_bot_iff.1 fun x hx => ?_
  have : x ∈ M ⊓ centralizer (M : Set X) := Subgroup.mem_inf.2 ⟨hx.2, hAc hx.1⟩
  rwa [t67_Z_eq_bot hT hM (t67_oddL hodd (Or.inr hM))] at this

private theorem t67_center_inv (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) {A : Subgroup X}
    (hA : Sec5Comp X n (cen t) A) :
    ∃ z ∈ A, orderOf z = 2 ∧ z ∈ zStar (K0 X n (cen t)) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdc := t67_dc_A hA (t67_oddL hodd (Or.inl hA))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥A)) 2 (by rw [hdc.2.1])
  refine ⟨((x : ↥A) : X), (x : ↥A).2, by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx], ?_⟩
  have hzAt : ((x : ↥A) : X) ∈ K0 X n (cen t) := t67_le_A hA (x : ↥A).2
  have hcomm : K0 X n (cen t) ≤ cen ((x : ↥A) : X) := by
    rw [K0_eq_sSup_sec5Comp]
    refine sSup_le fun A' hA' => ?_
    by_cases h : A' = A
    · subst h
      intro k hk
      exact mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_center_iff.1 x.2 ⟨k, hk⟩))
    · intro k hk
      exact mem_centralizer_singleton_iff.2
        (mem_centralizer_iff.1 (t67_Kt_cen hodd (Or.inl hA) (Or.inl hA') (Ne.symm h) hk) _
          (x : ↥A).2).symm
  refine Subgroup.mem_inf.2 ⟨hzAt, Subgroup.le_normalizer hzAt,
    normalizer_le_normalizer_pPrimeCoreOf _ (Subgroup.le_normalizer hzAt), fun k hk => ?_⟩
  rw [commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_singleton_iff.1 (hcomm hk))]
  exact one_mem _

private theorem t67_le_M_of_cent (hK : Sec6Lemma51 X n) {y w : X} {F : Subgroup X}
    (hF : Sec6MComp X n (cen y) F) (hw2 : orderOf w = 2) (hFw : F ≤ cen w) :
    F ≤ Sec6M X n (cen w) := by
  have hwc : w ∈ centralizer (F : Set X) := t67_mem_centralizer_iff.2 hFw
  have hgL : w ∈ centralizerSection F (pPrimeCoreOf 2 F) := by
    refine ⟨centralizer_le_normalizer _ hwc,
      normalizer_le_normalizer_pPrimeCoreOf _ (centralizer_le_normalizer _ hwc), fun k hk => ?_⟩
    rw [commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_singleton_iff.1 (hFw hk))]
    exact one_mem _
  have hres := sec6MComp_restrict hF (t67_sq_eq_one hw2) hgL
  rw [inf_of_le_left hFw, t67_oTwo_eq (t67_twoGenQuasi (Or.inr hF))] at hres
  exact (t67_le_M hres).trans (hK.sub w hw2 _ inf_le_right).2

private theorem t67_pump_inf (hT : Sec6T67Facts n) (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥)
    (ht2 : orderOf t = 2) {y : X} {F A : Subgroup X} (hF : Sec6MComp X n (cen y) F)
    (hOF : pPrimeCoreOf 2 F = ⊥) (hnc : ¬ CentModOdd F t) {f : X} (hf : f ∈ F)
    (hcf : CentModOdd F (f * t)) (hA : Sec5Comp X n (cen t) A) (hAF : A ≤ F) :
    F ⊓ cen t = A := by
  have hOF' : oddCoreOf F = ⊥ := hOF
  have hc : ∀ a ∈ F, a * (f * t) = (f * t) * a := fun a ha => by
    have := hcf a ha
    rw [hOF', mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  have hft : f * t = t * f := by
    have h := hc f hf
    have h' : f * (f * t) = f * (t * f) := by rw [h]; group
    exact mul_left_cancel h'
  have heq : F ⊓ cen t = F ⊓ cen f := by
    ext a
    simp only [Subgroup.mem_inf, mem_centralizer_singleton_iff]
    refine and_congr_right fun ha => ?_
    have h := hc a ha
    constructor
    · intro hat
      have : a * f * t = f * a * t := by
        calc a * f * t = a * (f * t) := by group
          _ = f * t * a := h
          _ = f * (t * a) := by group
          _ = f * (a * t) := by rw [hat]
          _ = f * a * t := by group
      exact mul_right_cancel this
    · intro haf
      have : f * (a * t) = f * (t * a) := by
        calc f * (a * t) = (f * a) * t := by group
          _ = (a * f) * t := by rw [haf]
          _ = a * (f * t) := by group
          _ = f * t * a := h
          _ = f * (t * a) := by group
      exact mul_left_cancel this
  have ht2' : t * t = 1 := by rw [← sq]; exact t67_sq_eq_one ht2
  have hff : f * f ∈ F ⊓ centralizer (F : Set X) := by
    refine Subgroup.mem_inf.2 ⟨mul_mem hf hf, ?_⟩
    have hcc : (f * t) * (f * t) ∈ centralizer (F : Set X) :=
      mul_mem (mem_centralizer_iff.2 fun a ha => hc a ha)
          (mem_centralizer_iff.2 fun a ha => hc a ha)
    have : (f * t) * (f * t) = f * f := by
      calc (f * t) * (f * t) = f * (t * f) * t := by group
        _ = f * (f * t) * t := by rw [hft]
        _ = f * f * (t * t) := by group
        _ = f * f := by rw [ht2', mul_one]
    rwa [this] at hcc
  rw [t67_Z_eq_bot hT hF hOF, mem_bot] at hff
  have hf1 : f ≠ 1 := by
    intro h1
    apply hnc
    intro a ha
    have := hc a ha
    rw [h1, one_mul] at this
    rw [commutatorElement_eq_one_iff_mul_comm.2 this]
    exact one_mem _
  have hf2 : orderOf f = 2 := orderOf_eq_prime (by rw [sq]; exact hff) hf1
  have hcard1 : Nat.card ↥(F ⊓ cen f) = n.factorial :=
    t67_card_dc (t67_two_le hT) (t67_cenM_dc hT hF hOF hf hf2)
  have hcard2 : Nat.card ↥A = n.factorial :=
    t67_card_dc (t67_two_le hT) (t67_dc_A hA (t67_oddL hodd (Or.inl hA)))
  have hAle : A ≤ F ⊓ cen t := le_inf hAF (t67_le_of_sec6KComp (Or.inl hA))
  refine (Subgroup.eq_of_le_of_card_ge hAle ?_).symm
  rw [heq, hcard1, hcard2]

private theorem t67_no_pump (hT : Sec6T67Facts n) (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n)
    (h61 : Sec6L61 X n t) (hC : Sec6CtrlAt X n t) (h65 : Sec6L65 X n t)
    (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) {y : X} (hy : y ∈ Sec6Base X n t)
    (hy2 : orderOf y = 2) (hVy : sec6V X n t ⊓ cen y ≤ cen t) {F L : Subgroup X}
    (hFM : Sec6MComp X n (cen y) F) (hL : Sec6KComp X n (cen t) L) (hPL : sec6Piece L y ≤ F)
    (hnc : ¬ CentModOdd F t) {f : X} (hf : f ∈ F) (hcf : CentModOdd F (f * t)) : False := by
  have hOy : oddCoreOf (cen y) = ⊥ := h65 y hy hy2
  have hOF : pPrimeCoreOf 2 F = ⊥ := t67_odd_eq_bot (Or.inr hFM) hOy
  have hyK : y ∈ Sec6K X n (cen t) := t67_base_le_K hy
  have hyMQ := t67_base_le_MQ hT hodd hy
  have hyA : K0 X n (cen t) ≤ cen y := t67_mem_centralizer_iff.1 (t67_base_le_cen_A hT hodd hy)
  have hFy : F ≤ cen y := t67_le_of_sec6KComp (Or.inr hFM)
  have hnct : ¬ F ≤ cen t := fun h => hnc fun a ha => by
    rw [commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_singleton_iff.1 (h ha))]
    exact one_mem _
  have finM : ∀ w, orderOf w = 2 → w ∈ Sec6M X n (cen t) → F ≤ cen w → False :=
    fun w hw2 hwM hFw => hnct ((le_inf (((t67_le_M_of_cent hK hFM hw2 hFw).trans
      (t67_M_le_K _)).trans (t67_le_V hwM hw2)) hFy).trans hVy)
  have finZ : ∀ w, orderOf w = 2 → w ∈ zStar (K0 X n (cen t)) → F ≤ cen w → False :=
    fun w hw2 hwZ hFw => by
      have hwB : w ∈ Sec6Base X n t := Subgroup.mem_sup_right hwZ
      have hKw := t67_K_le_of_Q h61 (t67_zStar_le_Q hT hodd hwZ) hw2 (h65 w hwB hw2)
      exact hnct (((t67_le_M_of_cent hK hFM hw2 hFw).trans (t67_M_le_K _)).trans
        (hKw.trans (t67_K_le _)))
  have hcomm : ∀ F' : Subgroup X, Sec6KComp X n (cen y) F' → F' ≠ F → ∀ w ∈ F', F ≤ cen w :=
    fun F' hF' hne w hw a ha => mem_centralizer_singleton_iff.2
      ((mem_centralizer_iff.1 (t67_le_centralizer (t67_isPCompIn hF') (t67_isPCompIn (Or.inr hFM))
        hne (t67_odd_eq_bot hF' hOy) ha) w hw).symm)
  rcases hL with hLA | hLM
  ·
    have hLy : L ≤ cen y := (t67_le_A hLA).trans hyA
    have hpL : sec6Piece L y = L := t67_piece_eq (t67_twoGenQuasi (Or.inl hLA)) hLy
    have hLF : L ≤ F := hpL ▸ hPL
    have hFt := t67_pump_inf hT hodd hS.choice.inv hFM hOF hnc hf hcf hLA hLF
    obtain ⟨M, hM⟩ := hS.choice.hasM
    obtain ⟨w, -, hwM, -, hw2, -, -, -, hwP, -⟩ := t67_piece_inv hT hodd hM hyK hy2
    obtain ⟨F'', hF'', hPF''⟩ := hC.land y hyMQ hy2 M (Or.inr hM)
    by_cases hFF : F'' = F
    · have hwL : w ∈ L := by
        rw [← hFt]
        exact Subgroup.mem_inf.2 ⟨hFF ▸ hPF'' hwP, t67_le_of_sec6KComp (Or.inr hM) hwM⟩
      have h1 : w ∈ L ⊓ M := Subgroup.mem_inf.2 ⟨hwL, hwM⟩
      rw [t67_inf_AM hT hodd hLA hM, mem_bot] at h1
      rw [h1, orderOf_one] at hw2
      exact absurd hw2 (by norm_num)
    · exact finM w hw2 (t67_le_M hM hwM) (hcomm F'' hF'' hFF w (hPF'' hwP))
  · by_cases hA : ∃ A, Sec5Comp X n (cen t) A
    · obtain ⟨A, hA⟩ := hA
      have hAy : A ≤ cen y := (t67_le_A hA).trans hyA
      have hpA : sec6Piece A y = A := t67_piece_eq (t67_twoGenQuasi (Or.inl hA)) hAy
      obtain ⟨F', hF', hPF'⟩ := hC.land y hyMQ hy2 A (Or.inl hA)
      rw [hpA] at hPF'
      by_cases hFF : F' = F
      · have hFt := t67_pump_inf hT hodd hS.choice.inv hFM hOF hnc hf hcf hA (hFF ▸ hPF')
        obtain ⟨w, -, hwL, -, hw2, -, -, -, hwP, -⟩ := t67_piece_inv hT hodd hLM hyK hy2
        have hwA : w ∈ A := by
          rw [← hFt]
          exact Subgroup.mem_inf.2 ⟨hPL hwP, t67_le_of_sec6KComp (Or.inr hLM) hwL⟩
        have h1 : w ∈ A ⊓ L := Subgroup.mem_inf.2 ⟨hwA, hwL⟩
        rw [t67_inf_AM hT hodd hA hLM, mem_bot] at h1
        rw [h1, orderOf_one] at hw2
        exact absurd hw2 (by norm_num)
      · obtain ⟨z, hzA, hz2, hzZ⟩ := t67_center_inv hodd hA
        exact finZ z hz2 hzZ (hcomm F' hF' hFF z (hPF' hzA))
    · have hK0 : K0 X n (cen t) = ⊥ := by
        rw [K0_eq_sSup_sec5Comp]
        exact sSup_eq_bot.2 fun A hA' => absurd ⟨A, hA'⟩ hA
      have hyM : y ∈ Sec6M X n (cen t) := by
        have h := hy
        unfold Sec6Base at h
        rwa [hK0, le_bot_iff.1 (t67_zStar_le ⊥), sup_bot_eq] at h
      exact finM y hy2 hyM hFy

private theorem t67_pu (hT : Sec6T67Facts n) (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n)
    (h61 : Sec6L61 X n t) (hC : Sec6CtrlAt X n t) (h65 : Sec6L65 X n t)
    (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) {y : X} (hy : y ∈ Sec6Base X n t)
    (hy2 : orderOf y = 2) (hVy : sec6V X n t ⊓ cen y ≤ cen t) {F : Subgroup X}
    (hF : Sec6KComp X n (cen y) F) : ∃ L, Sec6KComp X n (cen t) L ∧ F = sec6Piece L y := by
  have hOy : oddCoreOf (cen y) = ⊥ := h65 y hy hy2
  have hyMQ := t67_base_le_MQ hT hodd hy
  obtain ⟨L, hL, hPL⟩ := hC.piece y hyMQ hy2 F hF
  rcases (hC.dich y hyMQ hy2 L F hL hF hPL).2 with heq | ⟨hFM, hnc, f, hf, hcf⟩
  · refine ⟨L, hL, ?_⟩
    have hOF : oddCoreOf F = ⊥ := t67_odd_eq_bot hF hOy
    rw [hOF, bot_sup_eq] at heq
    exact heq
  · exact (t67_no_pump hT hS hK h61 hC h65 hodd hy hy2 hVy hFM hL hPL hnc hf hcf).elim

private theorem t67_K_le_of_pu (hT : Sec6T67Facts n) (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n)
    (h61 : Sec6L61 X n t) (hC : Sec6CtrlAt X n t) (h65 : Sec6L65 X n t)
    (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) {y : X} (hy : y ∈ Sec6Base X n t)
    (hy2 : orderOf y = 2) (hVy : sec6V X n t ⊓ cen y ≤ cen t) :
    Sec6K X n (cen y) ≤ Sec6K X n (cen t) := by
  refine sSup_le fun F hF => ?_
  obtain ⟨L, hL, rfl⟩ := t67_pu hT hS hK h61 hC h65 hodd hy hy2 hVy hF
  exact t67_piece_le.trans (t67_le_K hL)

private theorem t67_mem_normalizer_inf {A B : Subgroup X} {g : X}
    (hA : g ∈ normalizer (A : Set X)) (hB : g ∈ normalizer (B : Set X)) :
    g ∈ normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_inf] at hA hB ⊢
  rw [hA h, hB h]

private theorem t67_oddN_inf {V : Subgroup X} (hOV : oddCoreOf V = ⊥) :
    oddCoreOf (normalizer (V : Set X)) ⊓ V = ⊥ := by
  have hVN : V ≤ normalizer (V : Set X) := Subgroup.le_normalizer
  have hle : oddCoreOf (normalizer (V : Set X)) ⊓ V ≤ oddCoreOf V := by
    refine le_oddCoreOf_of_normalized inf_le_right (fun v hv => t67_mem_normalizer_inf ?_
      (Subgroup.le_normalizer hv)) ?_
    · exact normalizer_le_normalizer_pPrimeCoreOf _ (Subgroup.le_normalizer (hVN hv))
    · exact Odd.of_dvd_nat (odd_card_oddCoreOf _) (Subgroup.card_dvd_of_le inf_le_left)
  rw [hOV] at hle
  exact le_bot_iff.1 hle

private theorem t67_oddN_le_cen {V : Subgroup X} (hOV : oddCoreOf V = ⊥) :
    oddCoreOf (normalizer (V : Set X)) ≤ centralizer (V : Set X) := by
  intro o ho
  rw [mem_centralizer_iff]
  intro v hv
  have hvN : v ∈ normalizer (V : Set X) := Subgroup.le_normalizer hv
  have hoN : o ∈ normalizer (V : Set X) := oddCoreOf_le _ ho
  have h1 : ⁅o, v⁆ ∈ oddCoreOf (normalizer (V : Set X)) := by
    have h := (mem_normalizer_iff.1 (normalizer_le_normalizer_pPrimeCoreOf _
      (Subgroup.le_normalizer hvN)) o⁻¹).1 (inv_mem ho)
    have h' : v * o⁻¹ * v⁻¹ ∈ oddCoreOf (normalizer (V : Set X)) := h
    have e : ⁅o, v⁆ = o * (v * o⁻¹ * v⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem ho h'
  have h2 : ⁅o, v⁆ ∈ V := by
    rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.1 hoN v).1 hv) (inv_mem hv)
  have h3 : ⁅o, v⁆ ∈ oddCoreOf (normalizer (V : Set X)) ⊓ V := Subgroup.mem_inf.2 ⟨h1, h2⟩
  rw [t67_oddN_inf hOV, mem_bot] at h3
  exact (commutatorElement_eq_one_iff_mul_comm.1 h3).symm

private theorem t67_normal_cover {F D : Subgroup X} (hq : IsTwoGenQuasi ↥F) (hDF : D ≤ F)
    (hFD : F ≤ normalizer (D : Set X)) :
    F ≤ pPrimeCoreOf 2 F ⊔ D ∨ ∀ d ∈ D, ∀ f ∈ F, ⁅d, f⁆ ∈ pPrimeCoreOf 2 F := by
  have hn : (D.subgroupOf F).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (mem_normalizer_iff.1 (hFD g.2) _).1 ha
  have hn' : ((D.subgroupOf F).map (QuotientGroup.mk' (pPrimeCore 2 ↥F))).Normal :=
    hn.map _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq.2 hn' with htop | hcen
  · left
    intro f hf
    have hmem : QuotientGroup.mk' (pPrimeCore 2 ↥F) ⟨f, hf⟩ ∈
        (D.subgroupOf F).map (QuotientGroup.mk' (pPrimeCore 2 ↥F)) := htop ▸ mem_top _
    obtain ⟨d, hd, hdf⟩ := hmem
    have hk : d⁻¹ * ⟨f, hf⟩ ∈ pPrimeCore 2 ↥F := QuotientGroup.eq.1 hdf
    have hf' : f = (d : X) * ((d⁻¹ * ⟨f, hf⟩ : ↥F) : X) := by simp
    rw [hf']
    exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.1 hd))
      (Subgroup.mem_sup_left ⟨_, hk, rfl⟩)
  · right
    intro d hd f hf
    have hdc : QuotientGroup.mk' (pPrimeCore 2 ↥F) ⟨d, hDF hd⟩ ∈ center _ :=
      hcen ⟨⟨d, hDF hd⟩, Subgroup.mem_subgroupOf.2 hd, rfl⟩
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥F) ⁅(⟨d, hDF hd⟩ : ↥F), ⟨f, hf⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.1 hdc _).symm
    have h2 : ⁅(⟨d, hDF hd⟩ : ↥F), ⟨f, hf⟩⁆ ∈ pPrimeCore 2 ↥F := by
      rwa [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥F), MonoidHom.mem_ker]
    exact ⟨_, h2, rfl⟩

private theorem t67_le_of_mul {F O D : Subgroup X} (hF : oTwoPrimeOf F = F) (hFOD : F ≤ O ⊔ D)
    (hDO : D ≤ normalizer (O : Set X)) (hOdd : Odd (Nat.card O))
    (hc : ∀ o ∈ O, ∀ d ∈ D, o * d = d * o) : F ≤ D := by
  have key : oTwoPrimeOf F ≤ D := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxF, k, hk⟩
    have hx : x ∈ ((O ⊔ D : Subgroup X) : Set X) := hFOD hxF
    rw [Subgroup.coe_mul_of_right_le_normalizer_left O D hDO] at hx
    obtain ⟨o, ho, d, hd, rfl⟩ := Set.mem_mul.1 hx
    have hcomm : Commute o d := hc o ho d hd
    have h1 : o ^ (2 ^ k) = (d ^ (2 ^ k))⁻¹ := by
      rw [hcomm.mul_pow] at hk
      exact eq_inv_of_mul_eq_one_left hk
    have h2 : o ^ (2 ^ k) ∈ D := by
      rw [h1]
      exact inv_mem (pow_mem hd _)
    have hodd : Nat.Coprime 2 (orderOf o) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard O ho)
        (Nat.coprime_two_left.2 hOdd)
    have h3 : o ∈ Subgroup.zpowers (o ^ (2 ^ k)) := by
      rw [mem_zpowers_pow_iff]
      exact Nat.Coprime.pow_left k hodd
    exact mul_mem ((Subgroup.zpowers_le.2 h2) h3) hd
  rwa [hF] at key

private theorem t67_KN (hII : Sec6CtrlNAt X n t (normalizer (sec6V X n t : Set X)))
    (hOV : oddCoreOf (sec6V X n t) = ⊥) (hKV : Sec6K X n (cen t) ≤ sec6V X n t)
    {F : Subgroup X} (hF : Sec6KComp X n (normalizer (sec6V X n t : Set X)) F) :
    ∃ L, Sec6KComp X n (cen t) L ∧ (F = L ∨
      (Sec6MComp X n (normalizer (sec6V X n t : Set X)) F ∧ Sec5Comp X n (cen t) L ∧ L ≤ F ∧
        ¬ CentModOdd F t ∧ F ≤ sec6V X n t)) := by
  obtain ⟨L, hL, hLF⟩ := hII.piece F hF
  have hON := t67_oddN_le_cen hOV
  have hOF : pPrimeCoreOf 2 F ≤ oddCoreOf (normalizer (sec6V X n t : Set X)) :=
    pPrimeCoreOf_le_oddCoreOf (t67_isPCompIn hF).1 (t67_subnormal hF)
  have hFn : F ≤ normalizer (pPrimeCoreOf 2 F : Set X) := fun f hf =>
    mem_normalizer_pPrimeCoreOf_of_mem hf
  have hq := t67_twoGenQuasi hF
  have hcV : ∀ o ∈ pPrimeCoreOf 2 F, ∀ v ∈ sec6V X n t, o * v = v * o := fun o ho v hv =>
    (mem_centralizer_iff.1 (hON (hOF ho)) v hv).symm
  refine ⟨L, hL, ?_⟩
  rcases hII.dich L F hL hF hLF with heq | ⟨hFM, hLA, hnc, f, hf, hcf⟩
  · left
    exact le_antisymm (t67_le_of_mul (t67_oTwo_eq hq) heq.le (hLF.trans hFn)
      (odd_card_oddCoreOf F) fun o ho d hd => hcV o ho d (hKV (t67_le_K hL hd))) hLF
  · right
    refine ⟨hFM, hLA, hLF, hnc, ?_⟩
    have hFV : F ≤ normalizer ((F ⊓ sec6V X n t : Subgroup X) : Set X) := fun g hg =>
      t67_mem_normalizer_inf (Subgroup.le_normalizer hg) ((t67_le_of_sec6KComp hF) hg)
    rcases t67_normal_cover hq inf_le_left hFV with hcov | hcen
    · exact (t67_le_of_mul (t67_oTwo_eq hq) hcov (inf_le_left.trans hFn) (odd_card_oddCoreOf F)
        fun o ho d hd => hcV o ho d hd.2).trans inf_le_right
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := t67_exists_noncomm (t67_twoGenQuasi hL)
      have hLV : L ≤ sec6V X n t := (t67_le_K hL).trans hKV
      have h1 := hcen a (Subgroup.mem_inf.2 ⟨hLF ha, hLV ha⟩) b (hLF hb)
      have h2 : ⁅a, b⁆ ∈ sec6V X n t := by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem (hLV ha) (hLV hb)) (inv_mem (hLV ha))) (inv_mem (hLV hb))
      have h3 : ⁅a, b⁆ ∈ oddCoreOf (normalizer (sec6V X n t : Set X)) ⊓ sec6V X n t :=
        Subgroup.mem_inf.2 ⟨hOF h1, h2⟩
      rw [t67_oddN_inf hOV, mem_bot] at h3
      exact hab (commutatorElement_eq_one_iff_mul_comm.1 h3)

private theorem t67_KC_le_base (hT : Sec6T67Facts n) (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) :
    Sec6K X n (cen t) ⊓ centralizer (K0 X n (cen t) : Set X) ≤ Sec6Base X n t := by
  intro k hk
  obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.1 hk
  have hkK : k ∈ ((K0 X n (cen t) ⊔ Sec6M X n (cen t) : Subgroup X) : Set X) := by
    rw [← sec6K_eq]
    exact hk1
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    ((t67_Mt_le_cen_At hT hodd).trans (centralizer_le_normalizer _))] at hkK
  obtain ⟨a, ha, m, hm, rfl⟩ := Set.mem_mul.1 hkK
  have hmc : m ∈ centralizer (K0 X n (cen t) : Set X) := t67_Mt_le_cen_At hT hodd hm
  have hac : a ∈ centralizer (K0 X n (cen t) : Set X) := by
    have := mul_mem hk2 (inv_mem hmc)
    rwa [mul_inv_cancel_right] at this
  have haZ : a ∈ zStar (K0 X n (cen t)) := by
    refine Subgroup.mem_inf.2 ⟨ha, Subgroup.le_normalizer ha,
      normalizer_le_normalizer_pPrimeCoreOf _ (Subgroup.le_normalizer ha), fun k' hk' => ?_⟩
    rw [commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_iff.1 hac k' hk')]
    exact one_mem _
  exact mul_mem (Subgroup.mem_sup_right haZ) (Subgroup.mem_sup_left hm)

private theorem t67_A_le_Kx (hT : Sec6T67Facts n) (hC : Sec6CtrlAt X n t)
    (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) {x : X} (hx : x ∈ Sec6Base X n t)
    (hx2 : orderOf x = 2) : K0 X n (cen t) ≤ Sec6K X n (cen x) := by
  have hxA : K0 X n (cen t) ≤ cen x := t67_mem_centralizer_iff.1 (t67_base_le_cen_A hT hodd hx)
  rw [K0_eq_sSup_sec5Comp]
  refine sSup_le fun A hA => ?_
  obtain ⟨F, hF, hPF⟩ := hC.land x (t67_base_le_MQ hT hodd hx) hx2 A (Or.inl hA)
  rw [t67_piece_eq (t67_twoGenQuasi (Or.inl hA)) ((t67_le_A hA).trans hxA)] at hPF
  exact hPF.trans (t67_le_K hF)

private theorem t67_cen_le_V1 (hT : Sec6T67Facts n) (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n)
    (h61 : Sec6L61 X n t) (hC : Sec6CtrlAt X n t) (h65 : Sec6L65 X n t)
    (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) (hA : K0 X n (cen t) ≠ ⊥)
    (hV1 : sec6V X n t = Sec6K X n (cen t)) {x : X} (hx : x ∈ Sec6Base X n t)
    (hx2 : orderOf x = 2) : cen x ≤ normalizer (sec6V X n t : Set X) := by
  have hVy : ∀ y : X, sec6V X n t ⊓ cen y ≤ cen t := fun y =>
    inf_le_left.trans (hV1 ▸ t67_K_le (cen t))
  have hKx := t67_K_le_of_pu hT hS hK h61 hC h65 hodd hx hx2 (hVy x)
  have hAx := t67_A_le_Kx hT hC hodd hx hx2
  set W := Sec6K X n (cen x) ⊓ centralizer (Sec6K X n (cen x) : Set X) with hWdef
  have htW : t ∈ W := by
    refine Subgroup.mem_inf.2 ⟨hAx (hS.central hA), t67_mem_centralizer_iff.2 ?_⟩
    exact hKx.trans (t67_K_le (cen t))
  have hVE : t67VE n W = sec6V X n t := by
    rw [hV1]
    refine le_antisymm (t67_VE_le fun w hw hw2 => ?_) (t67_le_VE htW hS.choice.inv)
    obtain ⟨hw1, hw2'⟩ := Subgroup.mem_inf.1 hw
    have hwC : w ∈ centralizer (K0 X n (cen t) : Set X) := by
      rw [t67_mem_centralizer_iff]
      exact hAx.trans (t67_mem_centralizer_iff.1 hw2')
    have hwB : w ∈ Sec6Base X n t := t67_KC_le_base hT hodd (Subgroup.mem_inf.2 ⟨hKx hw1, hwC⟩)
    exact t67_K_le_of_pu hT hS hK h61 hC h65 hodd hwB hw2 (hVy w)
  exact t67_le_normalizer_of_VE ((Sec6K_cen_normal n x).trans
    (t67_normalizer_le_normalizer_Z _)) hVE

private theorem t67_R_le_base (hT : Sec6T67Facts n)
    (hII : Sec6CtrlNAt X n t (normalizer (sec6V X n t : Set X)))
    (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) (hV1 : sec6V X n t = Sec6K X n (cen t)) :
    Sec6R X n (normalizer (sec6V X n t : Set X)) ≤ Sec6Base X n t := by
  have hOV : oddCoreOf (sec6V X n t) = ⊥ := hV1 ▸ hodd
  have hKV : Sec6K X n (cen t) ≤ sec6V X n t := hV1 ▸ le_rfl
  have hVt : sec6V X n t ≤ cen t := hV1 ▸ t67_K_le (cen t)
  have hKN : ∀ F, Sec6KComp X n (normalizer (sec6V X n t : Set X)) F →
      (Sec5Comp X n (normalizer (sec6V X n t : Set X)) F → Sec5Comp X n (cen t) F) ∧
      (Sec6MComp X n (normalizer (sec6V X n t : Set X)) F → Sec6MComp X n (cen t) F) := by
    intro F hF
    obtain ⟨L, hL, hFL | ⟨-, -, -, hnc, hFV⟩⟩ := t67_KN hII hOV hKV hF
    · subst hFL
      refine ⟨fun h5 => ?_, fun h6 => ?_⟩
      · rcases hL with hL | hL
        · exact hL
        · exact (t67_not_sec5_of_M hT h5 hL).elim
      · rcases hL with hL | hL
        · exact (t67_not_sec5_of_M hT hL h6).elim
        · exact hL
    · exfalso
      refine hnc fun a ha => ?_
      rw [commutatorElement_eq_one_iff_mul_comm.2
        (mem_centralizer_singleton_iff.1 (hVt (hFV ha)))]
      exact one_mem _
  refine sup_le (fun z hz => ?_) ?_
  ·
    have hA'A : K0 X n (normalizer (sec6V X n t : Set X)) ≤ K0 X n (cen t) := by
      rw [K0_eq_sSup_sec5Comp, K0_eq_sSup_sec5Comp]
      exact sSup_le fun F hF => le_sSup ((hKN F (Or.inl hF)).1 hF)
    have hzA' : z ∈ K0 X n (normalizer (sec6V X n t : Set X)) := hz.1
    have hOA' : pPrimeCoreOf 2 (K0 X n (normalizer (sec6V X n t : Set X))) = ⊥ := by
      have h : oddCoreOf (K0 X n (normalizer (sec6V X n t : Set X))) ≤
          oddCoreOf (Sec6K X n (cen t)) := by
        refine le_oddCoreOf_of_normalized ((oddCoreOf_le _).trans (hA'A.trans (t67_A_le_K _)))
          (fun c hc => ?_) (odd_card_oddCoreOf _)
        have hcN : c ∈ normalizer (sec6V X n t : Set X) := Subgroup.le_normalizer (hKV hc)
        exact normalizer_le_normalizer_pPrimeCoreOf _
          (mem_normalizer_of_map_conj_eq (map_conj_K0 n (Subgroup.le_normalizer hcN)))
      rw [hodd] at h
      exact le_bot_iff.1 h
    have hzc : ∀ k ∈ K0 X n (normalizer (sec6V X n t : Set X)), k * z = z * k := fun k hk => by
      have := hz.2.2.2 k hk
      rw [hOA', mem_bot] at this
      exact commutatorElement_eq_one_iff_mul_comm.1 this
    have hzC : K0 X n (cen t) ≤ cen z := by
      rw [K0_eq_sSup_sec5Comp]
      refine sSup_le fun A hA => ?_
      by_cases hAN : Sec5Comp X n (normalizer (sec6V X n t : Set X)) A
      · intro a ha
        exact mem_centralizer_singleton_iff.2 (hzc a (t67_le_A hAN ha))
      · have hle : K0 X n (normalizer (sec6V X n t : Set X)) ≤ centralizer (A : Set X) := by
          rw [K0_eq_sSup_sec5Comp]
          refine sSup_le fun F hF => t67_Kt_cen hodd (Or.inl hA)
              (Or.inl ((hKN F (Or.inl hF)).1 hF)) ?_
          rintro rfl
          exact hAN hF
        intro a ha
        exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hle hzA') a ha)
    have hzAt : z ∈ K0 X n (cen t) := hA'A hzA'
    refine Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hzAt, Subgroup.le_normalizer hzAt,
      normalizer_le_normalizer_pPrimeCoreOf _ (Subgroup.le_normalizer hzAt), fun k hk => ?_⟩)
    rw [commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_singleton_iff.1 (hzC hk))]
    exact one_mem _
  ·
    refine sSup_le fun F hF => le_sup_of_le_left ?_
    exact t67_le_M ((hKN F (Or.inr hF)).2 hF)

private theorem t67_ne_one_of_orderOf {x : X} (hx : orderOf x = 2) : x ≠ 1 := fun h => by
  rw [h, orderOf_one] at hx
  exact absurd hx (by norm_num)

private theorem t67_comm_central {g c h d : X} (hcg : Commute c g) (hch : Commute c h)
    (hcd : Commute c d) (hdg : Commute d g) : ⁅g * c, h * d⁆ = ⁅g, h⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have e1 : g * c * (h * d) * (g * c)⁻¹ * (h * d)⁻¹ =
      g * (c * (h * d)) * c⁻¹ * g⁻¹ * d⁻¹ * h⁻¹ := by group
  rw [e1, (hch.mul_right hcd).eq]
  have e2 : g * (h * d * c) * c⁻¹ * g⁻¹ * d⁻¹ * h⁻¹ = g * h * (d * g⁻¹) * d⁻¹ * h⁻¹ := by group
  rw [e2, hdg.inv_right.eq]
  group

private theorem t67b_eq_one_of_sq {O : Subgroup X} (hO : Odd (Nat.card O)) {c : X} (hc : c ∈ O)
    (h2 : c ^ 2 = 1) : c = 1 := by
  have h1 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have h3 : Nat.Coprime (orderOf c) 2 :=
    Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard O hc) (Nat.coprime_two_right.2 hO)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h3 h1)

private theorem t67b_comm_of_mod {O : Subgroup X} (hO : Odd (Nat.card O)) {a w : X}
    (hw2 : w ^ 2 = 1) (hc : ⁅a, w⁆ ∈ O) (hcw : ⁅a, w⁆ * w = w * ⁅a, w⁆) : a * w = w * a := by
  have h1 : a * w * a⁻¹ = ⁅a, w⁆ * w := by rw [commutatorElement_def]; group
  have h2 : (a * w * a⁻¹) ^ 2 = 1 := by
    rw [sq, show a * w * a⁻¹ * (a * w * a⁻¹) = a * (w * w) * a⁻¹ by group, ← sq, hw2, mul_one,
      mul_inv_cancel]
  rw [h1, (show Commute ⁅a, w⁆ w from hcw).mul_pow 2, hw2, mul_one] at h2
  exact commutatorElement_eq_one_iff_mul_comm.1 (t67b_eq_one_of_sq hO hc h2)

private theorem t67b_perfect {L : Subgroup X} (hq : IsTwoGenQuasi ↥L)
    (hOc : pPrimeCoreOf 2 L ≤ centralizer (L : Set X)) : ⁅L, L⁆ = L := by
  have hle : ⁅L, L⁆ ≤ L := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  refine le_antisymm hle ?_
  have hmap : Subgroup.map (QuotientGroup.mk' (pPrimeCore 2 ↥L))
      (⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ : Subgroup ↥L) = ⊤ := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
      ← _root_.commutator_def]
    exact hq.2.1.commutator_eq_top
  have hcomm : Subgroup.map L.subtype (⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ : Subgroup ↥L) =
      ⁅L, L⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hcov : L ≤ pPrimeCoreOf 2 L ⊔ ⁅L, L⁆ := by
    intro l hl
    have hmem : QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨l, hl⟩ ∈ Subgroup.map
        (QuotientGroup.mk' (pPrimeCore 2 ↥L))
            (⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ : Subgroup ↥L) :=
      hmap ▸ mem_top _
    obtain ⟨c, hc, hcl⟩ := hmem
    have hk : c⁻¹ * ⟨l, hl⟩ ∈ pPrimeCore 2 ↥L := QuotientGroup.eq.1 hcl
    have hcX : (c : X) ∈ ⁅L, L⁆ := hcomm ▸ ⟨c, hc, rfl⟩
    have hl' : l = (c : X) * ((c⁻¹ * ⟨l, hl⟩ : ↥L) : X) := by simp
    rw [hl']
    exact mul_mem (Subgroup.mem_sup_right hcX) (Subgroup.mem_sup_left ⟨_, hk, rfl⟩)
  exact t67_le_of_mul (t67_oTwo_eq hq) hcov
    (hle.trans fun g hg => mem_normalizer_pPrimeCoreOf_of_mem hg) (odd_card_oddCoreOf L)
    fun o ho d hd => (mem_centralizer_iff.1 (hOc ho) d (hle hd)).symm

private theorem t67b_cent {G Z : Subgroup X} {o : X} (hperf : ⁅G, G⁆ = G)
    (hZG : Z ≤ centralizer (G : Set X)) (hZle : Z ≤ G) (ho : ∀ g ∈ G, ⁅o, g⁆ ∈ Z) :
    o ∈ centralizer (G : Set X) := by
  have hcomm : ∀ z ∈ Z, ∀ g ∈ G, g * z = z * g := fun z hz g hg =>
    mem_centralizer_iff.1 (hZG hz) g hg
  have hmul : ∀ a ∈ G, ∀ b ∈ G, ⁅o, a * b⁆ = ⁅o, a⁆ * ⁅o, b⁆ := by
    intro a ha b hb
    have h1 : a * ⁅o, b⁆ * a⁻¹ = ⁅o, b⁆ := by
      rw [hcomm _ (ho b hb) a ha, mul_inv_cancel_right]
    calc ⁅o, a * b⁆ = ⁅o, a⁆ * (a * ⁅o, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = ⁅o, a⁆ * ⁅o, b⁆ := by rw [h1]
  have hinv : ∀ a ∈ G, ⁅o, a⁻¹⁆ = ⁅o, a⁆⁻¹ := by
    intro a ha
    have h := hmul a ha a⁻¹ (inv_mem ha)
    rw [mul_inv_cancel, commutatorElement_one_right] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hcc : ⁅G, G⁆ ≤ G ⊓ cen o := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    · have hab : a * b * a⁻¹ ∈ G := mul_mem (mul_mem ha hb) (inv_mem ha)
      have e : ⁅o, ⁅a, b⁆⁆ = ⁅o, a⁆ * ⁅o, b⁆ * ⁅o, a⁆⁻¹ * ⁅o, b⁆⁻¹ := by
        rw [commutatorElement_def a b, hmul _ hab _ (inv_mem hb),
          hmul _ (mul_mem ha hb) _ (inv_mem ha), hmul _ ha _ hb, hinv a ha, hinv b hb]
      have hz : ⁅o, a⁆ * ⁅o, b⁆ = ⁅o, b⁆ * ⁅o, a⁆ :=
        (hcomm _ (ho a ha) _ (hZle (ho b hb))).symm
      have e2 : ⁅o, ⁅a, b⁆⁆ = 1 := by rw [e, hz]; group
      exact mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.1 e2).symm
  rw [hperf] at hcc
  rw [t67_mem_centralizer_iff]
  exact fun g hg => (Subgroup.mem_inf.1 (hcc hg)).2

private theorem t67b_comm_L {L L' : Subgroup X} (hL : Sec6KComp X n (cen t) L)
    (hL' : Sec6KComp X n (cen t) L') (hne : L ≠ L')
    (hOc : pPrimeCoreOf 2 L ≤ centralizer (L : Set X)) : L' ≤ centralizer (L : Set X) := by
  have hperf := t67b_perfect (t67_twoGenQuasi hL) hOc
  intro l' hl'
  refine t67b_cent hperf hOc (Subgroup.map_subtype_le _) fun g hg => ?_
  rw [← commutatorElement_inv]
  exact inv_mem (t67_comm_mem (t67_isPCompIn hL) (t67_isPCompIn hL') hne hg hl')

private theorem t67b_Z_le_odd (hT : Sec6T67Facts n) {H L : Subgroup X} (hM : Sec6MComp X n H L) :
    L ⊓ centralizer (L : Set X) ≤ pPrimeCoreOf 2 L := by
  intro x hx
  obtain ⟨hxL, hxc⟩ := Subgroup.mem_inf.1 hx
  have hq := t67_twoGenQuasi (Or.inr hM)
  have hcf := hT.cf _ hq.2 hM.1.2.1
  have hxZ : QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨x, hxL⟩ ∈ center (↥L ⧸ pPrimeCore 2 ↥L) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.1 hxc g g.2)
  rw [hcf, mem_bot, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hxZ
  exact ⟨_, hxZ, rfl⟩

private theorem t67b_lift2 {L : Subgroup X} (q : ↥L ⧸ pPrimeCore 2 ↥L) {k : ℕ}
    (hq : q ^ (2 ^ k) = 1) :
    ∃ a : ↥L, QuotientGroup.mk' (pPrimeCore 2 ↥L) a = q ∧ a ^ (2 ^ k) = 1 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L) q
  have hr : Odd (Nat.card (pPrimeCore 2 ↥L)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hk : a ^ (2 ^ k) ∈ pPrimeCore 2 ↥L := by
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥L), MonoidHom.mem_ker, map_pow, hq]
  have hkr : (a ^ (2 ^ k)) ^ Nat.card (pPrimeCore 2 ↥L) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard _ hk)
  have hcop : (Nat.card (pPrimeCore 2 ↥L)).Coprime
      (orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥L) a)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hq)
      (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hr))
  obtain ⟨s, hs⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨(a ^ Nat.card (pPrimeCore 2 ↥L)) ^ s, by rw [map_pow, map_pow, hs], ?_⟩
  calc ((a ^ Nat.card (pPrimeCore 2 ↥L)) ^ s) ^ (2 ^ k) =
        ((a ^ (2 ^ k)) ^ Nat.card (pPrimeCore 2 ↥L)) ^ s := by
        rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
        congr 1
        ring
    _ = 1 := by rw [hkr, one_pow]

private theorem t67b_no5 (hA0 : K0 X n (cen t) = ⊥) {L : Subgroup X}
    (hL : Sec5Comp X n (cen t) L) : False := by
  have hLb : L = ⊥ := le_bot_iff.1 (hA0 ▸ t67_le_A hL)
  obtain ⟨v, hv, hv2⟩ := Sec6L51B.exists_involution_of_isTwoGenQuasi (t67_twoGenQuasi (Or.inl hL))
  rw [hLb, mem_bot] at hv
  exact t67_ne_one_of_orderOf hv2 hv

private theorem t67b_KM (hA0 : K0 X n (cen t) = ⊥) : Sec6K X n (cen t) = Sec6M X n (cen t) := by
  rw [sec6K_eq, hA0, bot_sup_eq]

private theorem t67b_Oc
    (hOZ : oddCoreOf (Sec6K X n (cen t)) ≤ centralizer (Sec6K X n (cen t) : Set X))
    {L : Subgroup X} (hL : Sec6KComp X n (cen t) L) :
    pPrimeCoreOf 2 L ≤ centralizer (L : Set X) := by
  have h1 : pPrimeCoreOf 2 L ≤ oddCoreOf (Sec6K X n (cen t)) :=
    pPrimeCoreOf_le_oddCoreOf (t67_le_K hL)
        (t67_subnormal_mono (t67_K_le (cen t)) (t67_subnormal hL))
  exact (h1.trans hOZ).trans (Subgroup.centralizer_le (t67_le_K hL))

private theorem t67b_decomp (hT : Sec6T67Facts n) (hA0 : K0 X n (cen t) = ⊥)
    (hOZ : oddCoreOf (Sec6K X n (cen t)) ≤ centralizer (Sec6K X n (cen t) : Set X))
    {L : Subgroup X} (hM : Sec6MComp X n (cen t) L) {y : X} (hy : y ∈ Sec6K X n (cen t))
    (hy2 : y ^ 2 = 1) :
    ∃ m ∈ L, ∃ d ∈ Subgroup.centralizer (L : Set X), m * d = y ∧ m ^ 2 = 1 := by
  have hle : Sec6K X n (cen t) ≤ L ⊔ centralizer (L : Set X) := by
    refine sSup_le fun L' hL' => ?_
    by_cases h : L' = L
    · rw [h]
      exact le_sup_left
    · exact le_sup_of_le_right (t67b_comm_L (Or.inr hM) hL' (Ne.symm h) (t67b_Oc hOZ (Or.inr hM)))
  have hmem : y ∈ ((L ⊔ centralizer (L : Set X) : Subgroup X) : Set X) := hle hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L _ (centralizer_le_normalizer _)] at hmem
  obtain ⟨m, hm, d, hd, hmd⟩ := Set.mem_mul.1 hmem
  have hcomm : Commute m d := mem_centralizer_iff.1 hd m hm
  have hz : m ^ 2 ∈ L ⊓ centralizer (L : Set X) := by
    have h1 : m ^ 2 = (d ^ 2)⁻¹ := by
      have h := hy2
      rw [← hmd, hcomm.mul_pow 2] at h
      exact eq_inv_of_mul_eq_one_left h
    refine Subgroup.mem_inf.2 ⟨pow_mem hm 2, ?_⟩
    rw [h1]
    exact inv_mem (pow_mem hd 2)
  have hzO : m ^ 2 ∈ pPrimeCoreOf 2 L := t67b_Z_le_odd hT hM hz
  have hzodd : Odd (orderOf (m ^ 2)) :=
    Odd.of_dvd_nat (odd_card_oddCoreOf L) (Subgroup.orderOf_dvd_natCard _ hzO)
  set u := (m ^ 2) ^ ((orderOf (m ^ 2) + 1) / 2) with hu
  have hu2 : u ^ 2 = m ^ 2 := by
    obtain ⟨j, hj⟩ := hzodd
    have he : (orderOf (m ^ 2) + 1) / 2 * 2 = orderOf (m ^ 2) + 1 := by omega
    rw [hu, ← pow_mul, he, pow_succ, pow_orderOf_eq_one, one_mul]
  have huO : u ∈ pPrimeCoreOf 2 L := pow_mem hzO _
  have huc : u ∈ Subgroup.centralizer (L : Set X) := t67b_Oc hOZ (Or.inr hM) huO
  have hmu : Commute m u⁻¹ := (show Commute m u from mem_centralizer_iff.1 huc m hm).inv_right
  refine ⟨m * u⁻¹, mul_mem hm (inv_mem (Subgroup.map_subtype_le _ huO)), u * d,
    mul_mem huc hd, ?_, ?_⟩
  · rw [← hmd]
    group
  · rw [hmu.mul_pow, inv_pow, hu2, mul_inv_cancel]

private theorem t67b_not_mem_odd {L : Subgroup X} {v : X} (hv2 : orderOf v = 2) :
    v ∉ pPrimeCoreOf 2 L := fun h => by
  have := Subgroup.orderOf_dvd_natCard _ h
  rw [hv2] at this
  exact (Nat.not_even_iff_odd.2 (odd_card_oddCoreOf L)) (even_iff_two_dvd.2 this)

private theorem t67b_orderOf_mk {L : Subgroup X} {v : X} (hv : v ∈ L) (hv2 : orderOf v = 2) :
    orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨v, hv⟩) = 2 := by
  refine orderOf_eq_prime ?_ fun h => ?_
  · rw [← map_pow]
    have : (⟨v, hv⟩ : ↥L) ^ 2 = 1 := Subtype.ext (by simpa using t67_sq_eq_one hv2)
    rw [this, map_one]
  · rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h
    exact t67b_not_mem_odd hv2 ⟨_, h, rfl⟩

private theorem t67b_comm_mem_odd {L : Subgroup X} {a v : ↥L}
    (h : QuotientGroup.mk' (pPrimeCore 2 ↥L) a * QuotientGroup.mk' (pPrimeCore 2 ↥L) v =
      QuotientGroup.mk' (pPrimeCore 2 ↥L) v * QuotientGroup.mk' (pPrimeCore 2 ↥L) a) :
    ⁅(a : X), (v : X)⁆ ∈ pPrimeCoreOf 2 L := by
  have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥L) ⁅a, v⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h1
  exact ⟨_, h1, rfl⟩

private theorem t67b_piece_inv (hT : Sec6T67Facts n) (hA0 : K0 X n (cen t) = ⊥)
    (hOZ : oddCoreOf (Sec6K X n (cen t)) ≤ centralizer (Sec6K X n (cen t) : Set X))
    {L : Subgroup X} (hM : Sec6MComp X n (cen t) L) {y : X} (hy : y ∈ Sec6K X n (cen t))
    (hy2 : orderOf y = 2) :
    ∃ w w' : X, w ∈ L ∧ w' ∈ L ∧ orderOf w = 2 ∧ orderOf w' = 2 ∧ w ≠ w' ∧ w * w' = w' * w ∧
      w ∈ sec6Piece L y ∧ w' ∈ sec6Piece L y := by
  obtain ⟨m, hm, d, hd, hmd, hm2⟩ := t67b_decomp hT hA0 hOZ hM hy (t67_sq_eq_one hy2)
  have hOc := t67b_Oc hOZ (Or.inr hM)
  obtain ⟨w, hwM, hw2, hkey⟩ : ∃ w ∈ L, orderOf w = 2 ∧ ∀ u ∈ L, u * w = w * u → u * y = y * u := by
    by_cases hm1 : m = 1
    · obtain ⟨w, hwM, hw2⟩ :=
        Sec6L51B.exists_involution_of_isTwoGenQuasi (t67_twoGenQuasi (Or.inr hM))
      refine ⟨w, hwM, hw2, fun u hu _ => ?_⟩
      rw [← hmd, hm1, one_mul]
      exact mem_centralizer_iff.1 hd u hu
    · refine ⟨m, hm, orderOf_eq_prime hm2 hm1, fun u hu hum => ?_⟩
      rw [← hmd]
      have hud : u * d = d * u := mem_centralizer_iff.1 hd u hu
      calc u * (m * d) = (u * m) * d := by group
        _ = (m * u) * d := by rw [hum]
        _ = m * (u * d) := by group
        _ = m * (d * u) := by rw [hud]
        _ = (m * d) * u := by group
  have hπw := t67b_orderOf_mk hwM hw2
  obtain ⟨u, hu2, hunc⟩ := t67_exists_noncentral hT (hT.cen _ hM.2 _ hπw)
  have hu2' : (u : ↥L ⧸ pPrimeCore 2 ↥L) ^ (2 ^ 1) = 1 := by
    rw [pow_one]
    exact congrArg Subtype.val hu2
  obtain ⟨a, hπa, ha2⟩ := t67b_lift2 (u : ↥L ⧸ pPrimeCore 2 ↥L) hu2'
  have huw : (u : ↥L ⧸ pPrimeCore 2 ↥L) * QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨w, hwM⟩ =
      QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨w, hwM⟩ * (u : ↥L ⧸ pPrimeCore 2 ↥L) :=
    mem_centralizer_singleton_iff.1 u.2
  have hcO : ⁅(a : X), w⁆ ∈ pPrimeCoreOf 2 L :=
    t67b_comm_mem_odd (a := a) (v := ⟨w, hwM⟩) (by rw [hπa]; exact huw)
  have hac : (a : X) * w = w * (a : X) :=
    t67b_comm_of_mod (odd_card_oddCoreOf L) (t67_sq_eq_one hw2) hcO
      (mem_centralizer_iff.1 (hOc hcO) w hwM).symm
  have ha2' : (a : X) ^ 2 = 1 := by
    have := congrArg Subtype.val ha2
    simpa using this
  have ha1 : (a : X) ≠ 1 := by
    intro h
    apply hunc
    have : a = 1 := Subtype.ext h
    rw [this, map_one] at hπa
    have hu1 : u = 1 := Subtype.ext hπa.symm
    rw [hu1]
    exact one_mem _
  have hne : w ≠ (a : X) := by
    intro h
    apply hunc
    have hau : a = ⟨w, hwM⟩ := Subtype.ext h.symm
    rw [hau] at hπa
    rw [mem_center_iff]
    intro v
    have hv : (v : ↥L ⧸ pPrimeCore 2 ↥L) * QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨w, hwM⟩ =
        QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨w, hwM⟩ * (v : ↥L ⧸ pPrimeCore 2 ↥L) :=
      mem_centralizer_singleton_iff.1 v.2
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hπa]; exact hv)
  have hpiece : ∀ z ∈ L, z * w = w * z → z ^ 2 = 1 → z ∈ sec6Piece L y := fun z hz hzw hz2 =>
    mem_oTwoPrimeOf ⟨hz, mem_centralizer_singleton_iff.2 (hkey z hz hzw)⟩ 1 (by simpa using hz2)
  exact ⟨w, (a : X), hwM, a.2, hw2, orderOf_eq_prime ha2' ha1, hne, hac.symm,
    hpiece w hwM rfl (t67_sq_eq_one hw2), hpiece _ a.2 hac ha2'⟩

private theorem t67b_gen (hT : Sec6T67Facts n) (hC : Sec6CtrlAt X n t)
    (hOZ : oddCoreOf (Sec6K X n (cen t)) ≤ centralizer (Sec6K X n (cen t) : Set X))
    {L : Subgroup X} (hM : Sec6MComp X n (cen t) L) {w w' : X} (hw : w ∈ L) (hw' : w' ∈ L)
    (hw2 : orderOf w = 2) (hw2' : orderOf w' = 2) (hne : w ≠ w') (hc : w * w' = w' * w) :
    L ≤ Sec6K X n (cen w) ⊔ Sec6K X n (cen w') := by
  have hOc := t67b_Oc hOZ (Or.inr hM)
  have hq := t67_twoGenQuasi (Or.inr hM)
  have hperf := t67b_perfect hq hOc
  have hQ : IsSec6MType n (↥L ⧸ pPrimeCore 2 ↥L) := hM.2
  have hπne : QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨w, hw⟩ ≠
      QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨w', hw'⟩ := by
    intro h
    have h1 : (⟨w, hw⟩ : ↥L)⁻¹ * ⟨w', hw'⟩ ∈ pPrimeCore 2 ↥L := QuotientGroup.eq.1 h
    have h2 : w⁻¹ * w' ∈ pPrimeCoreOf 2 L := ⟨_, h1, rfl⟩
    have hcw : Commute w⁻¹ w' := (show Commute w w' from hc).inv_left
    have h3 : orderOf (w⁻¹ * w') = 2 := by
      refine orderOf_eq_prime ?_ fun h4 => hne ?_
      · rw [hcw.mul_pow, inv_pow, t67_sq_eq_one hw2, t67_sq_eq_one hw2', inv_one, one_mul]
      · rw [inv_mul_eq_one] at h4
        exact h4
    exact t67b_not_mem_odd h3 h2
  have hπc : QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨w, hw⟩ *
      QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨w', hw'⟩ =
      QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨w', hw'⟩ *
      QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨w, hw⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hc
  have hg := hT.gen _ hQ _ _ (t67b_orderOf_mk hw hw2) (t67b_orderOf_mk hw' hw2') hπne hπc
  set H := (L ⊓ Sec6K X n (cen w)) ⊔ (L ⊓ Sec6K X n (cen w')) with hH
  have hHL : H ≤ L := sup_le inf_le_left inf_le_left
  have hCle : ∀ v (hv : v ∈ L), orderOf v = 2 → L ⊓ Sec6K X n (cen v) ≤ H →
      centralizer ({QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨v, hv⟩} : Set (↥L ⧸ pPrimeCore 2 ↥L)) ≤
        (H.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) := by
    intro v hv hv2 hvH
    have hdc := hT.cen _ hQ _ (t67b_orderOf_mk hv hv2)
    have hpr := primeResidual_two_eq_top_of_isDoubleCoverOfAlt (t67_four_le hT) hdc
    rw [← oTwoPrimeOf_eq_self_of_primeResidual hpr]
    refine (Subgroup.closure_le _).2 ?_
    rintro q ⟨hqC, k, hqk⟩
    obtain ⟨a, hπa, hak⟩ := t67b_lift2 q hqk
    have hcO : ⁅(a : X), v⁆ ∈ pPrimeCoreOf 2 L :=
      t67b_comm_mem_odd (a := a) (v := ⟨v, hv⟩)
        (by rw [hπa]; exact mem_centralizer_singleton_iff.1 hqC)
    have hav : (a : X) * v = v * (a : X) :=
      t67b_comm_of_mod (odd_card_oddCoreOf L) (t67_sq_eq_one hv2) hcO
        (mem_centralizer_iff.1 (hOc hcO) v hv).symm
    have hak' : (a : X) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hak
      simpa using this
    have haP : (a : X) ∈ sec6Piece L v :=
      mem_oTwoPrimeOf (Subgroup.mem_inf.2 ⟨a.2, mem_centralizer_singleton_iff.2 hav⟩) k hak'
    obtain ⟨F, hF, hPF⟩ := hC.land v (Subgroup.mem_sup_left (t67_le_M hM hv)) hv2 L (Or.inr hM)
    have haK : (a : X) ∈ L ⊓ Sec6K X n (cen v) :=
      Subgroup.mem_inf.2 ⟨a.2, t67_le_K hF (hPF haP)⟩
    exact ⟨a, Subgroup.mem_subgroupOf.2 (hvH haK), hπa⟩
  have htop : (H.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← hg]
    exact sup_le (hCle w hw hw2 le_sup_left) (hCle w' hw' hw2' le_sup_right)
  have hLHO : L ≤ H ⊔ pPrimeCoreOf 2 L := by
    intro l hl
    have hmem : QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨l, hl⟩ ∈
        (H.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) := htop ▸ mem_top _
    obtain ⟨h, hh, hhl⟩ := hmem
    have hk : h⁻¹ * ⟨l, hl⟩ ∈ pPrimeCore 2 ↥L := QuotientGroup.eq.1 hhl
    have hl' : l = (h : X) * ((h⁻¹ * ⟨l, hl⟩ : ↥L) : X) := by simp
    rw [hl']
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hh))
      (Subgroup.mem_sup_right ⟨_, hk, rfl⟩)
  have hOH : pPrimeCoreOf 2 L ≤ normalizer (H : Set X) :=
    (hOc.trans (Subgroup.centralizer_le hHL)).trans (centralizer_le_normalizer _)
  have hdec : ∀ x ∈ L, ∃ h ∈ H, ∃ o ∈ pPrimeCoreOf 2 L, h * o = x := fun x hx => by
    have hx' : x ∈ ((H ⊔ pPrimeCoreOf 2 L : Subgroup X) : Set X) := hLHO hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left H _ hOH] at hx'
    exact Set.mem_mul.1 hx'
  have hLH : L ≤ H := by
    rw [← hperf, Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨h1, hh1, o1, ho1, rfl⟩ := hdec a ha
    obtain ⟨h2, hh2, o2, ho2, rfl⟩ := hdec b hb
    have hc1 : ∀ g ∈ L, Commute o1 g := fun g hg => (mem_centralizer_iff.1 (hOc ho1) g hg).symm
    have hc2 : ∀ g ∈ L, Commute o2 g := fun g hg => (mem_centralizer_iff.1 (hOc ho2) g hg).symm
    rw [t67_comm_central (hc1 h1 (hHL hh1)) (hc1 h2 (hHL hh2))
      (hc1 o2 (Subgroup.map_subtype_le _ ho2)) (hc2 h1 (hHL hh1))]
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hh1 hh2) (inv_mem hh1)) (inv_mem hh2)
  exact hLH.trans (sup_le_sup inf_le_right inf_le_right)

private theorem t67_Z_eq_bot' (hT : Sec6T67Facts n) {M : Subgroup X} (hty : IsSec6MType n ↥M)
    (hnc : ∃ a ∈ M, ∃ b ∈ M, a * b ≠ b * a) : M ⊓ centralizer (M : Set X) = ⊥ := by
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  have hc := t67_center_eq_bot hT hty ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  refine le_bot_iff.1 fun x hx => ?_
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
  have hxc : (⟨x, hx1⟩ : ↥M) ∈ center ↥M := mem_center_iff.2 fun g =>
    Subtype.ext (mem_centralizer_iff.1 hx2 g g.2)
  rw [hc, mem_bot] at hxc
  exact mem_bot.2 (congrArg Subtype.val hxc)

private theorem t67_commutator_eq {A : Subgroup X} (h : Group.IsPerfect ↥A) : ⁅A, A⁆ = A := by
  have h1 := h.commutator_eq_top
  rw [_root_.commutator_def] at h1
  have h2 := congrArg (Subgroup.map A.subtype) h1
  rwa [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h2

private theorem t67_zStar_le_cenM (hT : Sec6T67Facts n) (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) :
    zStar (K0 X n (cen t)) ≤ centralizer (Sec6M X n (cen t) : Set X) := fun _ hz =>
  t67_mem_centralizer_iff.2 ((t67_M_le_K _).trans
    (t67_mem_centralizer_iff.1 (t67_zStar_le_cen hT hodd hz)))

section V2

variable {M0 : Subgroup X}

private theorem t67_v2_le_normalizer_M0 (hMc : M0 ≤ centralizer (Sec6M X n (cen t) : Set X)) :
    Sec6M X n (cen t) ≤ normalizer (M0 : Set X) :=
  (le_centralizer_iff.1 hMc).trans (centralizer_le_normalizer _)

private theorem t67_v2_decomp (hMc : M0 ≤ centralizer (Sec6M X n (cen t) : Set X)) {v : X}
    (hv : v ∈ M0 ⊔ Sec6M X n (cen t)) : ∃ a ∈ M0, ∃ b ∈ Sec6M X n (cen t), a * b = v := by
  have hv' : v ∈ ((M0 ⊔ Sec6M X n (cen t) : Subgroup X) : Set X) := hv
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (t67_v2_le_normalizer_M0 hMc)] at hv'
  exact Set.mem_mul.1 hv'

private theorem t67_v2_normal_Mt (hMc : M0 ≤ centralizer (Sec6M X n (cen t) : Set X)) :
    M0 ⊔ Sec6M X n (cen t) ≤ normalizer (Sec6M X n (cen t) : Set X) :=
  sup_le (hMc.trans (centralizer_le_normalizer _)) Subgroup.le_normalizer

private theorem t67_v2_normal_M0 (hMc : M0 ≤ centralizer (Sec6M X n (cen t) : Set X)) :
    M0 ⊔ Sec6M X n (cen t) ≤ normalizer (M0 : Set X) :=
  sup_le Subgroup.le_normalizer (t67_v2_le_normalizer_M0 hMc)

private theorem t67_K_le_V (hT : Sec6T67Facts n) (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) : Sec6K X n (cen t) ≤ sec6V X n t := by
  obtain ⟨M, hM⟩ := hS.choice.hasM
  obtain ⟨y, hyM, hy2⟩ := Sec6L51B.exists_involution_of_isTwoGenQuasi (t67_twoGenQuasi (Or.inr hM))
  have hyMt : y ∈ Sec6M X n (cen t) := t67_le_M hM hyM
  have hyB : y ∈ Sec6Base X n t := Subgroup.mem_sup_left hyMt
  rw [sec6K_eq]
  refine sup_le ((t67_A_le_Kx hT hC hodd hyB hy2).trans (t67_le_V hyMt hy2)) ?_
  unfold Sec6M
  refine sSup_le fun M' hM' => ?_
  obtain ⟨w, hwM, hw2⟩ :=
    Sec6L51B.exists_involution_of_isTwoGenQuasi (t67_twoGenQuasi (Or.inr hM'))
  have hwMt : w ∈ Sec6M X n (cen t) := t67_le_M hM' hwM
  obtain ⟨a, b, haM, hbM, ha2, hb2, hab, hc, -, -⟩ :=
    t67_piece_inv hT hodd hM' (t67_M_le_K _ hwMt) hw2
  exact (t67_gen hT hC hodd hM' haM hbM ha2 hb2 hab hc).trans
    (sup_le (t67_le_V (t67_le_M hM' haM) ha2) (t67_le_V (t67_le_M hM' hbM) hb2))

private theorem t67_v2_A_le (hT : Sec6T67Facts n) (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥)
    (hMc : M0 ≤ centralizer (Sec6M X n (cen t) : Set X))
    (hVeq : sec6V X n t = M0 ⊔ Sec6M X n (cen t)) : K0 X n (cen t) ≤ M0 := by
  have hKV := t67_K_le_V hT hS hC hodd
  rw [K0_eq_sSup_sec5Comp]
  refine sSup_le fun A hA => ?_
  have hAV : A ≤ M0 ⊔ Sec6M X n (cen t) := hVeq ▸ (t67_le_A hA).trans ((t67_A_le_K _).trans hKV)
  have hAc : A ≤ centralizer (Sec6M X n (cen t) : Set X) :=
    (t67_le_A hA).trans (le_centralizer_iff.1 (t67_Mt_le_cen_At hT hodd))
  have hperf := (t67_dc_A hA (t67_oddL hodd (Or.inl hA))).1.1
  rw [← t67_commutator_eq hperf, Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨a0, ha0, a1, ha1, rfl⟩ := t67_v2_decomp hMc (hAV ha)
  obtain ⟨b0, hb0, b1, hb1, rfl⟩ := t67_v2_decomp hMc (hAV hb)
  have hc0 : ∀ g ∈ M0, ∀ m ∈ Sec6M X n (cen t), Commute m g := fun g hg m hm =>
    (mem_centralizer_iff.1 (hMc hg) m hm)
  have ha1c : a1 ∈ centralizer (Sec6M X n (cen t) : Set X) := by
    have := mul_mem (inv_mem (hMc ha0)) (hAc ha)
    rwa [inv_mul_cancel_left] at this
  have hb1c : b1 ∈ centralizer (Sec6M X n (cen t) : Set X) := by
    have := mul_mem (inv_mem (hMc hb0)) (hAc hb)
    rwa [inv_mul_cancel_left] at this
  rw [t67_comm_central (hc0 a0 ha0 a1 ha1) (hc0 b0 hb0 a1 ha1)
    (mem_centralizer_iff.1 ha1c b1 hb1).symm (hc0 a0 ha0 b1 hb1)]
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha0 hb0) (inv_mem ha0)) (inv_mem hb0)

private theorem t67_v2_odd (hT : Sec6T67Facts n) (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥) (hA : K0 X n (cen t) ≠ ⊥)
    (hM0 : IsSec6MType n ↥M0) (hMc : M0 ≤ centralizer (Sec6M X n (cen t) : Set X))
    (hVeq : sec6V X n t = M0 ⊔ Sec6M X n (cen t)) : oddCoreOf (sec6V X n t) = ⊥ := by
  have htM0 : t ∈ M0 := t67_v2_A_le hT hS hC hodd hMc hVeq (hS.central hA)
  have ht1 : t ≠ 1 := fun h => by
    have := hS.choice.inv
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hnc : ∃ a ∈ M0, ∃ b ∈ M0, a * b ≠ b * a := by
    obtain ⟨A, hA'⟩ : ∃ A, Sec5Comp X n (cen t) A := by
      by_contra hno
      apply hA
      rw [K0_eq_sSup_sec5Comp]
      exact sSup_eq_bot.2 fun A h => absurd ⟨A, h⟩ hno
    obtain ⟨a, ha, b, hb, hab⟩ := t67_exists_noncomm (t67_twoGenQuasi (Or.inl hA'))
    have hAM := (t67_le_A hA').trans (t67_v2_A_le hT hS hC hodd hMc hVeq)
    exact ⟨a, hAM ha, b, hAM hb, hab⟩
  have hZ := t67_Z_eq_bot' hT hM0 hnc
  haveI := hT.simple _ hM0
  have hVM0 : sec6V X n t ≤ normalizer (M0 : Set X) := hVeq ▸ t67_v2_normal_M0 hMc
  have hM0V : M0 ≤ sec6V X n t := hVeq ▸ le_sup_left
  have hVO : sec6V X n t ≤ normalizer (oddCoreOf (sec6V X n t) : Set X) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_pPrimeCoreOf _)
  have hOM0 : oddCoreOf (sec6V X n t) ⊓ M0 = ⊥ := by
    have hn : ((oddCoreOf (sec6V X n t) ⊓ M0).subgroupOf M0).Normal := by
      refine ⟨fun a ha g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      obtain ⟨ha1, ha2⟩ := Subgroup.mem_inf.1 ha
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (hVO (hM0V g.2)) _).1 ha1,
        mul_mem (mul_mem g.2 ha2) (inv_mem g.2)⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((oddCoreOf (sec6V X n t) ⊓ M0).subgroupOf M0) with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      exact h.eq_bot_of_le inf_le_right
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at h
      have htO : t ∈ oddCoreOf (sec6V X n t) := (Subgroup.mem_inf.1 (h htM0)).1
      have h2 := Subgroup.orderOf_dvd_natCard _ htO
      rw [hS.choice.inv] at h2
      exact (Nat.not_even_iff_odd.2 (odd_card_oddCoreOf _)) (even_iff_two_dvd.2 h2)
  have hOc : oddCoreOf (sec6V X n t) ≤ centralizer (M0 : Set X) := by
    intro o ho
    rw [mem_centralizer_iff]
    intro g hg
    have h1 : ⁅o, g⁆ ∈ oddCoreOf (sec6V X n t) := by
      have h := (mem_normalizer_iff.1 (hVO (hM0V hg)) o⁻¹).1 (inv_mem ho)
      have e : ⁅o, g⁆ = o * (g * o⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact mul_mem ho h
    have h2 : ⁅o, g⁆ ∈ M0 := by
      rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.1 (hVM0 (oddCoreOf_le _ ho)) g).1 hg) (inv_mem hg)
    have h3 : ⁅o, g⁆ ∈ oddCoreOf (sec6V X n t) ⊓ M0 := Subgroup.mem_inf.2 ⟨h1, h2⟩
    rw [hOM0, mem_bot] at h3
    exact (commutatorElement_eq_one_iff_mul_comm.1 h3).symm
  have hOM : oddCoreOf (sec6V X n t) ≤ Sec6M X n (cen t) := by
    intro o ho
    obtain ⟨a, ha, b, hb, rfl⟩ := t67_v2_decomp hMc (hVeq ▸ oddCoreOf_le _ ho : o ∈ _)
    have hbc : b ∈ centralizer (M0 : Set X) := le_centralizer_iff.1 hMc hb
    have hac : a ∈ M0 ⊓ centralizer (M0 : Set X) := by
      refine Subgroup.mem_inf.2 ⟨ha, ?_⟩
      have := mul_mem (hOc ho) (inv_mem hbc)
      rwa [mul_inv_cancel_right] at this
    rw [hZ, mem_bot] at hac
    rw [hac, one_mul]
    exact hb
  have hKV := t67_K_le_V hT hS hC hodd
  have h : oddCoreOf (sec6V X n t) ≤ oddCoreOf (Sec6K X n (cen t)) :=
    le_oddCoreOf_of_normalized (hOM.trans (t67_M_le_K _)) (hKV.trans hVO)
      (odd_card_oddCoreOf _)
  rw [hodd] at h
  exact le_bot_iff.1 h

private theorem t67_cen_dc (hT : Sec6T67Facts n) {M : Subgroup X} (hty : IsSec6MType n ↥M) {w : X}
    (hwM : w ∈ M) (hw2 : orderOf w = 2) : IsDoubleCoverOfAlt ↥(M ⊓ cen w) n := by
  have hdc := hT.cen ↥M hty ⟨w, hwM⟩ (by rw [Subgroup.orderOf_mk]; exact hw2)
  have heq : (centralizer ({⟨w, hwM⟩} : Set ↥M)).map M.subtype = M ⊓ cen w := by
    refine le_antisymm (t67_map_cen_le hwM) ?_
    rintro x ⟨hxM, hxw⟩
    exact ⟨⟨x, hxM⟩, mem_centralizer_singleton_iff.2
      (Subtype.ext (mem_centralizer_singleton_iff.1 hxw)), rfl⟩
  exact GH74.GLS.Stage12.McLRec.isDoubleCoverOfAlt_congr
    ((Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).trans
      (MulEquiv.subgroupCongr heq)) hdc

private theorem t67_cen_center (hT : Sec6T67Facts n) {M : Subgroup X} (hty : IsSec6MType n ↥M)
    {w : X} (hwM : w ∈ M) (hw2 : orderOf w = 2) {z : X} (hz : z ∈ M ⊓ cen w)
    (hzc : M ⊓ cen w ≤ cen z) : z = 1 ∨ z = w := by
  have hc2 := (t67_cen_dc hT hty hwM hw2).2.1
  have hwC : w ∈ M ⊓ cen w := Subgroup.mem_inf.2 ⟨hwM, mem_centralizer_singleton_iff.2 rfl⟩
  let z' : ↥(center ↥(M ⊓ cen w)) := ⟨⟨z, hz⟩, mem_center_iff.2 fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.1 (hzc g.2))⟩
  let w' : ↥(center ↥(M ⊓ cen w)) := ⟨⟨w, hwC⟩, mem_center_iff.2 fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).2)⟩
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(center ↥(M ⊓ cen w)))).1 hc2
  by_cases hz1 : z' = 1
  · left
    exact congrArg (fun u : ↥(center ↥(M ⊓ cen w)) => ((u : ↥(M ⊓ cen w)) : X)) hz1
  · right
    have hw1 : w' ≠ 1 := fun h => by
      have hw : w = 1 := congrArg (fun u : ↥(center ↥(M ⊓ cen w)) => ((u : ↥(M ⊓ cen w)) : X)) h
      rw [hw, orderOf_one] at hw2
      exact absurd hw2 (by norm_num)
    exact congrArg (fun u : ↥(center ↥(M ⊓ cen w)) => ((u : ↥(M ⊓ cen w)) : X))
      ((huniq z' hz1).trans (huniq w' hw1).symm)

private theorem t67_card_type {Q Q' : Type} [Group Q] [Group Q'] (h : IsSec6MType n Q)
    (h' : IsSec6MType n Q') : Nat.card Q = Nat.card Q' := by
  rcases h with ⟨hn, ⟨e⟩⟩ | ⟨hn, ⟨e⟩⟩ <;> rcases h' with ⟨hn', ⟨e'⟩⟩ | ⟨hn', ⟨e'⟩⟩
  · exact Nat.card_congr (e.trans e'.symm).toEquiv
  · omega
  · omega
  · exact Nat.card_congr (e.trans e'.symm).toEquiv

private theorem t67_exists_A (hA : K0 X n (cen t) ≠ ⊥) : ∃ A, Sec5Comp X n (cen t) A := by
  by_contra hno
  apply hA
  rw [K0_eq_sSup_sec5Comp]
  exact sSup_eq_bot.2 fun A h => absurd ⟨A, h⟩ hno

private theorem t67_v2_pump_disj (hT : Sec6T67Facts n)
    (hMc : M0 ≤ centralizer (Sec6M X n (cen t) : Set X))
    {y : X} {F : Subgroup X} (hFM : Sec6MComp X n (cen y) F) (hOF : pPrimeCoreOf 2 F = ⊥)
    (hFV : F ≤ M0 ⊔ Sec6M X n (cen t)) (hnc : ¬ CentModOdd F t) :
    Disjoint (Sec6M X n (cen t)) F := by
  haveI := hT.simple _ (t67_type_M hFM hOF)
  have hn : ((Sec6M X n (cen t)).subgroupOf F).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (mem_normalizer_iff.1 (t67_v2_normal_Mt hMc (hFV g.2)) _).1 ha
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Sec6M X n (cen t)).subgroupOf F) with h | h
  · exact Subgroup.subgroupOf_eq_bot.1 h
  · exfalso
    rw [Subgroup.subgroupOf_eq_top] at h
    refine hnc fun a ha => ?_
    have hat : a ∈ cen t := (t67_M_le_K _).trans (t67_K_le (cen t)) (h ha)
    rw [commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_singleton_iff.1 hat)]
    exact one_mem _

section V2Facts

variable (hT : Sec6T67Facts n) (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n) (h61 : Sec6L61 X n t)
  (hC : Sec6CtrlAt X n t) (h65 : Sec6L65 X n t) (hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥)
  (hA : K0 X n (cen t) ≠ ⊥) (hM0 : IsSec6MType n ↥M0) (hMM : M0 ⊓ Sec6M X n (cen t) = ⊥)
  (hMc : M0 ≤ centralizer (Sec6M X n (cen t) : Set X))
  (hVeq : sec6V X n t = M0 ⊔ Sec6M X n (cen t))

include hT hS hC hodd hA hMc hVeq in
private theorem t67_v2_t_mem : t ∈ M0 := t67_v2_A_le hT hS hC hodd hMc hVeq (hS.central hA)

include hT hS hC hodd hA hMc hVeq in
private theorem t67_v2_Z (hM0 : IsSec6MType n ↥M0) : M0 ⊓ centralizer (M0 : Set X) = ⊥ := by
  obtain ⟨A, hA'⟩ := t67_exists_A hA
  obtain ⟨a, ha, b, hb, hab⟩ := t67_exists_noncomm (t67_twoGenQuasi (Or.inl hA'))
  have hAM := (t67_le_A hA').trans (t67_v2_A_le hT hS hC hodd hMc hVeq)
  exact t67_Z_eq_bot' hT hM0 ⟨a, hAM ha, b, hAM hb, hab⟩

include hT hS hC hodd hA hMc hVeq hM0 in
private theorem t67_v2_zStar {z : X} (hz : z ∈ zStar (K0 X n (cen t))) : z = 1 ∨ z = t := by
  have hAM0 := t67_v2_A_le hT hS hC hodd hMc hVeq
  have htM0 := t67_v2_t_mem hT hS hC hodd hA hMc hVeq
  obtain ⟨A, hA'⟩ := t67_exists_A hA
  have hle : K0 X n (cen t) ≤ M0 ⊓ cen t :=
    le_inf hAM0 ((t67_A_le_K _).trans (t67_K_le _))
  have hcardA : Nat.card ↥A = n.factorial :=
    t67_card_dc (t67_two_le hT) (t67_dc_A hA' (t67_oddL hodd (Or.inl hA')))
  have hcardC : Nat.card ↥(M0 ⊓ cen t) = n.factorial :=
    t67_card_dc (t67_two_le hT) (t67_cen_dc hT hM0 htM0 hS.choice.inv)
  have hAeq : A = M0 ⊓ cen t :=
    Subgroup.eq_of_le_of_card_ge ((t67_le_A hA').trans hle) (by rw [hcardA, hcardC])
  have hAt : K0 X n (cen t) = M0 ⊓ cen t := le_antisymm hle (hAeq ▸ t67_le_A hA')
  have hzA := t67_zStar_le _ hz
  have hzc : K0 X n (cen t) ≤ cen z :=
    (t67_A_le_K _).trans (t67_mem_centralizer_iff.1 (t67_zStar_le_cen hT hodd hz))
  rw [hAt] at hzA hzc
  exact t67_cen_center hT hM0 htM0 hS.choice.inv hzA hzc

include hT hS hC hodd hA hMM hMc hVeq in
private theorem t67_v2_hV {b : X} (hb : b ∈ Sec6M X n (cen t)) :
    sec6V X n t ⊓ cen (b * t) ≤ cen t := by
  have htM0 := t67_v2_t_mem hT hS hC hodd hA hMc hVeq
  have hcomm : ∀ g ∈ M0, ∀ m ∈ Sec6M X n (cen t), m * g = g * m := fun g hg m hm =>
    mem_centralizer_iff.1 (hMc hg) m hm
  intro v hv
  obtain ⟨hvV, hvc⟩ := Subgroup.mem_inf.1 hv
  obtain ⟨a, ha, c, hc, rfl⟩ := t67_v2_decomp hMc (hVeq ▸ hvV)
  have h1 : a * c * (b * t) = b * t * (a * c) := mem_centralizer_singleton_iff.1 hvc
  have htcb : t * (c * b) = c * b * t := (hcomm t htM0 _ (mul_mem hc hb)).symm
  have hbta : b * (t * a) = t * a * b := hcomm _ (mul_mem htM0 ha) b hb
  have h2 : a * t * (c * b) = t * a * (b * c) := by
    calc a * t * (c * b) = a * (t * (c * b)) := by group
      _ = a * (c * b * t) := by rw [htcb]
      _ = a * c * (b * t) := by group
      _ = b * t * (a * c) := h1
      _ = b * (t * a) * c := by group
      _ = t * a * b * c := by rw [hbta]
      _ = t * a * (b * c) := by group
  have h3 : a * t = t * a * (b * c) * (c * b)⁻¹ := eq_mul_inv_of_mul_eq h2
  have key : (t * a)⁻¹ * (a * t) = (b * c) * (c * b)⁻¹ := by rw [h3]; group
  have hmem : (t * a)⁻¹ * (a * t) ∈ M0 ⊓ Sec6M X n (cen t) := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (mul_mem htM0 ha)) (mul_mem ha htM0), ?_⟩
    rw [key]
    exact mul_mem (mul_mem hb hc) (inv_mem (mul_mem hc hb))
  rw [hMM, mem_bot, inv_mul_eq_one] at hmem
  have hct : c * t = t * c := hcomm t htM0 c hc
  refine mem_centralizer_singleton_iff.2 ?_
  calc a * c * t = a * (c * t) := by group
    _ = a * (t * c) := by rw [hct]
    _ = (a * t) * c := by group
    _ = (t * a) * c := by rw [hmem]
    _ = t * (a * c) := by group

include hT hS hK h61 hC h65 hodd hA hM0 hMM hMc hVeq in
private theorem t67_v2_K_le_V {w : X} (hw : w ∈ Sec6Base X n t) (hw2 : orderOf w = 2) :
    Sec6K X n (cen w) ≤ sec6V X n t := by
  have hw' : w ∈ ((Sec6M X n (cen t) ⊔ zStar (K0 X n (cen t)) : Subgroup X) : Set X) := hw
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    ((t67_zStar_le_cenM hT hodd).trans (centralizer_le_normalizer _))] at hw'
  obtain ⟨m', hm', z, hz, hwz⟩ := Set.mem_mul.1 hw'
  rcases t67_v2_zStar hT hS hC hodd hA hM0 hMc hVeq hz with h1 | h1
  · rw [h1, mul_one] at hwz
    subst hwz
    exact t67_le_V hm' hw2
  · rw [h1] at hwz
    subst hwz
    exact (t67_K_le_of_pu hT hS hK h61 hC h65 hodd hw hw2
      (t67_v2_hV hT hS hC hodd hA hMM hMc hVeq hm')).trans (t67_K_le_V hT hS hC hodd)

include hT hS hK hC h65 hodd hA hM0 hMc hVeq in
private theorem t67_v2_exists_M0 : ∃ y0, orderOf y0 = 2 ∧ Sec6MComp X n (cen y0) M0 := by
  have htM0 := t67_v2_t_mem hT hS hC hodd hA hMc hVeq
  have hZ := t67_v2_Z hT hS hC hodd hA hMc hVeq hM0
  have hex : ∃ y0 ∈ Sec6M X n (cen t), orderOf y0 = 2 ∧
      ¬ Sec6K X n (cen y0) ≤ Sec6K X n (cen t) := by
    by_contra hno
    push Not at hno
    have hVK : sec6V X n t ≤ Sec6K X n (cen t) :=
      iSup_le fun y => iSup_le fun hy => iSup_le fun hy2 => hno y hy hy2
    have hM0t : M0 ≤ cen t := (hVeq ▸ le_sup_left : M0 ≤ sec6V X n t).trans (hVK.trans (t67_K_le _))
    have : t ∈ M0 ⊓ centralizer (M0 : Set X) :=
      Subgroup.mem_inf.2 ⟨htM0, t67_mem_centralizer_iff.2 hM0t⟩
    rw [hZ, mem_bot] at this
    exact t67_ne_one_of_orderOf hS.choice.inv this
  obtain ⟨y0, hy0, hy02, hnot⟩ := hex
  have hy0B : y0 ∈ Sec6Base X n t := Subgroup.mem_sup_left hy0
  have hOy := h65 y0 hy0B hy02
  have hy0MQ := t67_base_le_MQ hT hodd hy0B
  have hy0K : y0 ∈ Sec6K X n (cen t) := t67_base_le_K hy0B
  obtain ⟨F, hF, hFn⟩ : ∃ F, Sec6KComp X n (cen y0) F ∧ ¬ F ≤ Sec6K X n (cen t) := by
    by_contra hno
    push Not at hno
    exact hnot (sSup_le fun F hF => hno F hF)
  obtain ⟨L, hL, hPL⟩ := hC.piece y0 hy0MQ hy02 F hF
  rcases (hC.dich y0 hy0MQ hy02 L F hL hF hPL).2 with heq | ⟨hFM, hnc, -, -, -⟩
  · exfalso
    apply hFn
    rw [heq, show oddCoreOf F = ⊥ from t67_odd_eq_bot hF hOy, bot_sup_eq]
    exact t67_piece_le.trans (t67_le_K hL)
  · refine ⟨y0, hy02, ?_⟩
    have hOF : pPrimeCoreOf 2 F = ⊥ := t67_odd_eq_bot (Or.inr hFM) hOy
    have hFV : F ≤ M0 ⊔ Sec6M X n (cen t) :=
      hVeq ▸ (t67_le_K (Or.inr hFM)).trans (t67_le_V hy0 hy02)
    have hdisj := t67_v2_pump_disj hT hMc hFM hOF hFV hnc
    haveI := hT.simple _ (t67_type_M hFM hOF)
    rcases hL with hLA | hLM
    ·
      have hLy : L ≤ cen y0 := (t67_le_A hLA).trans
        (t67_mem_centralizer_iff.1 (t67_base_le_cen_A hT hodd hy0B))
      have hLF : L ≤ F := (t67_piece_eq (t67_twoGenQuasi (Or.inl hLA)) hLy) ▸ hPL
      have hLM0 : L ≤ M0 := (t67_le_A hLA).trans (t67_v2_A_le hT hS hC hodd hMc hVeq)
      have hn : (M0.subgroupOf F).Normal := by
        refine ⟨fun a ha g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at ha ⊢
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact (mem_normalizer_iff.1 (t67_v2_normal_M0 hMc (hFV g.2)) _).1 ha
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M0.subgroupOf F) with h | h
      · exfalso
        obtain ⟨v, hvL, hv2⟩ :=
          Sec6L51B.exists_involution_of_isTwoGenQuasi (t67_twoGenQuasi (Or.inl hLA))
        have := (Subgroup.subgroupOf_eq_bot.1 h).le_bot
          (show v ∈ M0 ⊓ F from Subgroup.mem_inf.2 ⟨hLM0 hvL, hLF hvL⟩)
        exact t67_ne_one_of_orderOf hv2 this
      · rw [Subgroup.subgroupOf_eq_top] at h
        have hcard : Nat.card ↥M0 ≤ Nat.card ↥F :=
          (t67_card_type hM0 (t67_type_M hFM hOF)).le
        have hFeq : F = M0 := Subgroup.eq_of_le_of_card_ge h hcard
        exact hFeq ▸ hFM
    · exfalso
      obtain ⟨w, -, hwL, -, hw2, -, -, -, hwP, -⟩ := t67_piece_inv hT hodd hLM hy0K hy02
      have := hdisj.le_bot (show w ∈ Sec6M X n (cen t) ⊓ F from
        Subgroup.mem_inf.2 ⟨t67_le_M hLM hwL, hPL hwP⟩)
      exact t67_ne_one_of_orderOf hw2 this

include hT hS hK hC h65 hodd hA hM0 hMc hVeq in
private theorem t67_v2_M0_le {w : X} (hw : w ∈ Sec6M X n (cen t)) (hw2 : orderOf w = 2) :
    M0 ≤ Sec6M X n (cen w) := by
  obtain ⟨y0, -, hM0y⟩ := t67_v2_exists_M0 hT hS hK hC h65 hodd hA hM0 hMc hVeq
  exact t67_le_M_of_cent hK hM0y hw2 (t67_mem_centralizer_iff.1 (le_centralizer_iff.1 hMc hw))

include hT hS hK hC h65 hodd hA hM0 hMc hVeq in
private theorem t67_v2_Ay {y : X} (hy : y ∈ Sec6M X n (cen t)) (hy2 : orderOf y = 2) :
    K0 X n (cen y) ≤ Sec6M X n (cen t) := by
  have hyB : y ∈ Sec6Base X n t := Subgroup.mem_sup_left hy
  have hOy := h65 y hyB hy2
  have hyMQ := t67_base_le_MQ hT hodd hyB
  rw [K0_eq_sSup_sec5Comp]
  refine sSup_le fun F hF => ?_
  obtain ⟨L, hL, hPL⟩ := hC.piece y hyMQ hy2 F (Or.inl hF)
  rcases (hC.dich y hyMQ hy2 L F hL (Or.inl hF) hPL).2 with heq | ⟨hFM, -⟩
  · have hFP : F = sec6Piece L y := by
      rw [show oddCoreOf F = ⊥ from t67_odd_eq_bot (Or.inl hF) hOy, bot_sup_eq] at heq
      exact heq
    rcases hL with hLA | hLM
    · exfalso
      have hLy : L ≤ cen y := (t67_le_A hLA).trans
        (t67_mem_centralizer_iff.1 (t67_base_le_cen_A hT hodd hyB))
      rw [t67_piece_eq (t67_twoGenQuasi (Or.inl hLA)) hLy] at hFP
      rw [hFP] at hF
      have hLMy : L ≤ Sec6M X n (cen y) := ((t67_le_A hLA).trans
        (t67_v2_A_le hT hS hC hodd hMc hVeq)).trans
            (t67_v2_M0_le hT hS hK hC h65 hodd hA hM0 hMc hVeq hy hy2)
      have hcen : Sec6M X n (cen y) ≤ centralizer (L : Set X) := by
        unfold Sec6M
        refine sSup_le fun G hG => t67_le_centralizer (t67_isPCompIn (Or.inl hF))
          (t67_isPCompIn (Or.inr hG)) ?_ (t67_odd_eq_bot (Or.inl hF) hOy)
        rintro rfl
        exact t67_not_sec5_of_M hT hF hG
      obtain ⟨a, ha, b, hb, hab⟩ := t67_exists_noncomm (t67_twoGenQuasi (Or.inl hF))
      exact hab (mem_centralizer_iff.1 (hcen (hLMy hb)) a ha)
    · rw [hFP]
      exact t67_piece_le.trans (t67_le_M hLM)
  · exact (t67_not_sec5_of_M hT hF hFM).elim

include hT hS hK hC h65 hodd hA hM0 hMM hMc hVeq in
private theorem t67_v2_exists_noncen {y : X} (hy : y ∈ Sec6M X n (cen t)) (hy2 : orderOf y = 2) :
    ∃ M, Sec6MComp X n (cen t) M ∧ ¬ M ≤ cen y := by
  by_contra hno
  push Not at hno
  have hMtMy : Sec6M X n (cen t) ≤ Sec6M X n (cen y) :=
    sSup_le fun M hM => t67_le_M_of_cent hK hM hy2 (hno M hM)
  have hM0My := t67_v2_M0_le hT hS hK hC h65 hodd hA hM0 hMc hVeq hy hy2
  have hVMy : sec6V X n t ≤ Sec6M X n (cen y) := hVeq ▸ sup_le hM0My hMtMy
  have h1 : modOddCard (sec6V X n t) ≤ modOddCard (Sec6M X n (cen t)) :=
    (modOddCard_le_of_le hVMy).trans (hS.choice.maxM y hy2)
  have hOV := t67_v2_odd hT hS hC hodd hA hM0 hMc hVeq
  have h2 : modOddCard (sec6V X n t) = Nat.card ↥(sec6V X n t) := by
    obtain ⟨e⟩ := t67_quotEquiv (show pPrimeCoreOf 2 (sec6V X n t) = ⊥ from hOV)
    unfold modOddCard
    exact Nat.card_congr e.toEquiv
  have h3 : modOddCard (Sec6M X n (cen t)) ≤ Nat.card ↥(Sec6M X n (cen t)) := by
    unfold modOddCard
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have hlt : Sec6M X n (cen t) < sec6V X n t := by
    refine lt_of_le_of_ne (hVeq ▸ le_sup_right) fun h => ?_
    have htM0 := t67_v2_t_mem hT hS hC hodd hA hMc hVeq
    have htV : t ∈ sec6V X n t := hVeq ▸ Subgroup.mem_sup_left htM0
    have : t ∈ M0 ⊓ Sec6M X n (cen t) := Subgroup.mem_inf.2 ⟨htM0, h ▸ htV⟩
    rw [hMM, mem_bot] at this
    exact t67_ne_one_of_orderOf hS.choice.inv this
  have h4 := Subgroup.card_lt_of_lt hlt
  omega

include hT hS hK hC h65 hodd hA hM0 hMM hMc hVeq in
private theorem t67_v2_piece_A {y : X} (hy : y ∈ Sec6M X n (cen t)) (hy2 : orderOf y = 2)
    {M : Subgroup X} (hM : Sec6MComp X n (cen t) M) (hMy : ¬ M ≤ cen y) :
    sec6Piece M y ≤ K0 X n (cen y) := by
  have hyB : y ∈ Sec6Base X n t := Subgroup.mem_sup_left hy
  have hOy := h65 y hyB hy2
  have hyMQ := t67_base_le_MQ hT hodd hyB
  have hyK := t67_base_le_K hyB
  obtain ⟨F, hF, hPF⟩ := hC.land y hyMQ hy2 M (Or.inr hM)
  obtain ⟨w, -, hwM, -, hw2, -, -, -, hwP, -⟩ := t67_piece_inv hT hodd hM hyK hy2
  rcases (hC.dich y hyMQ hy2 M F (Or.inr hM) hF hPF).2 with heq | ⟨hFM, hnc, -, -, -⟩
  · have hFP : F = sec6Piece M y := by
      rw [show oddCoreOf F = ⊥ from t67_odd_eq_bot hF hOy, bot_sup_eq] at heq
      exact heq
    rcases hF with hFA | hFM
    · rw [← hFP]
      exact t67_le_A hFA
    · exfalso
      apply hMy
      have hOF := t67_odd_eq_bot (Or.inr hFM) hOy
      have hOM := t67_oddL hodd (Or.inr hM)
      have hFle : F ≤ M := hFP ▸ t67_piece_le
      have hFeq : F = M := Subgroup.eq_of_le_of_card_ge hFle
        (t67_card_type (t67_type_M hM hOM) (t67_type_M hFM hOF)).le
      rw [← hFeq]
      exact t67_le_of_sec6KComp (Or.inr hFM)
  · exfalso
    have hOF := t67_odd_eq_bot (Or.inr hFM) hOy
    have hFV : F ≤ M0 ⊔ Sec6M X n (cen t) :=
      hVeq ▸ (t67_le_K (Or.inr hFM)).trans (t67_le_V hy hy2)
    have hdisj := t67_v2_pump_disj hT hMc hFM hOF hFV hnc
    have := hdisj.le_bot (show w ∈ Sec6M X n (cen t) ⊓ F from
      Subgroup.mem_inf.2 ⟨t67_le_M hM hwM, hPF hwP⟩)
    exact t67_ne_one_of_orderOf hw2 this

include hT hS hK hC h65 hodd hA hM0 hMM hMc hVeq in
private theorem t67_v2_cen_le_M {y : X} (hy : y ∈ Sec6M X n (cen t)) (hy2 : orderOf y = 2) :
    cen y ≤ normalizer (sec6V X n t : Set X) := by
  have hyK := t67_base_le_K (Subgroup.mem_sup_left hy : y ∈ Sec6Base X n t)
  obtain ⟨M1, hM1, hM1y⟩ := t67_v2_exists_noncen hT hS hK hC h65 hodd hA hM0 hMM hMc hVeq hy hy2
  obtain ⟨w1, -, hw1M, -, hw12, -, -, -, hw1P, -⟩ := t67_piece_inv hT hodd hM1 hyK hy2
  have hw1A : w1 ∈ K0 X n (cen y) :=
    t67_v2_piece_A hT hS hK hC h65 hodd hA hM0 hMM hMc hVeq hy hy2 hM1 hM1y hw1P
  have hw1Mt : w1 ∈ Sec6M X n (cen t) := t67_le_M hM1 hw1M
  have hVE : t67VE n (K0 X n (cen y)) = sec6V X n t := by
    refine le_antisymm (t67_VE_le fun w hw hw2 => t67_le_V
      (t67_v2_Ay hT hS hK hC h65 hodd hA hM0 hMc hVeq hy hy2 hw) hw2) ?_
    rw [hVeq]
    refine sup_le ?_ ?_
    · exact (t67_v2_M0_le hT hS hK hC h65 hodd hA hM0 hMc hVeq hw1Mt hw12).trans
        ((t67_M_le_K _).trans (t67_le_VE hw1A hw12))
    · refine sSup_le fun M hM => ?_
      by_cases hMy : M ≤ cen y
      · have hne : M ≠ M1 := fun h => hM1y (h ▸ hMy)
        have hMw : M ≤ cen w1 :=
          t67_mem_centralizer_iff.1 ((t67_Kt_cen hodd (Or.inr hM) (Or.inr hM1) hne) hw1M)
        exact (t67_le_M_of_cent hK hM hw12 hMw).trans ((t67_M_le_K _).trans (t67_le_VE hw1A hw12))
      · obtain ⟨w, w', hwM, hw'M, hw2, hw2', hne, hc, hwP, hw'P⟩ :=
          t67_piece_inv hT hodd hM hyK hy2
        have hwA := t67_v2_piece_A hT hS hK hC h65 hodd hA hM0 hMM hMc hVeq hy hy2 hM hMy hwP
        have hw'A := t67_v2_piece_A hT hS hK hC h65 hodd hA hM0 hMM hMc hVeq hy hy2 hM hMy hw'P
        exact (t67_gen hT hC hodd hM hwM hw'M hw2 hw2' hne hc).trans
          (sup_le (t67_le_VE hwA hw2) (t67_le_VE hw'A hw2'))
  exact t67_le_normalizer_of_VE (K0_cen_normal n y) hVE

include hT hS hC hodd hA hMc hVeq in
private theorem t67_v2_t_zStar : t ∈ zStar (K0 X n (cen t)) := by
  have htA := hS.central hA
  refine Subgroup.mem_inf.2 ⟨htA, Subgroup.le_normalizer htA,
    normalizer_le_normalizer_pPrimeCoreOf _ (Subgroup.le_normalizer htA), fun k hk => ?_⟩
  have hkt : k ∈ cen t := ((t67_A_le_K _).trans (t67_K_le _)) hk
  rw [commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_singleton_iff.1 hkt)]
  exact one_mem _

include hT hS hK h61 hC h65 hodd hA hM0 hMM hMc hVeq in
private theorem t67_v2_cen_le_mt {m : X} (hm : m ∈ Sec6M X n (cen t)) (hm2 : orderOf m = 2) :
    cen (m * t) ≤ normalizer (sec6V X n t : Set X) := by
  have htM0 := t67_v2_t_mem hT hS hC hodd hA hMc hVeq
  have htZ := t67_v2_t_zStar hT hS hC hodd hA hMc hVeq
  have hmt : m * t = t * m := mem_centralizer_iff.1 (hMc htM0) m hm
  have hyB : m * t ∈ Sec6Base X n t :=
    mul_mem (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right htZ)
  have hy2 : orderOf (m * t) = 2 := by
    refine orderOf_eq_prime ?_ fun h => ?_
    · rw [(show Commute m t from hmt).mul_pow, t67_sq_eq_one hm2, t67_sq_eq_one hS.choice.inv,
        one_mul]
    · have htm : t = m⁻¹ := eq_inv_of_mul_eq_one_right h
      have htMt : m⁻¹ ∈ Sec6M X n (cen t) := inv_mem hm
      rw [← htm] at htMt
      have : t ∈ M0 ⊓ Sec6M X n (cen t) := Subgroup.mem_inf.2 ⟨htM0, htMt⟩
      rw [hMM, mem_bot] at this
      exact t67_ne_one_of_orderOf hS.choice.inv this
  have hVy := t67_v2_hV hT hS hC hodd hA hMM hMc hVeq hm
  have hKy := t67_K_le_of_pu hT hS hK h61 hC h65 hodd hyB hy2 hVy
  have hAy := t67_A_le_Kx hT hC hodd hyB hy2
  have htW : t ∈ Sec6K X n (cen (m * t)) ⊓ centralizer (Sec6K X n (cen (m * t)) : Set X) :=
    Subgroup.mem_inf.2 ⟨hAy (hS.central hA), t67_mem_centralizer_iff.2 (hKy.trans (t67_K_le _))⟩
  obtain ⟨M, hM, hMm⟩ := t67_v2_exists_noncen hT hS hK hC h65 hodd hA hM0 hMM hMc hVeq hm hm2
  obtain ⟨m0, hm0M, d, hd, hm0d⟩ := t67_decomp hodd (Or.inr hM) (t67_M_le_K _ hm)
  have hZM := t67_Z_eq_bot hT hM (t67_oddL hodd (Or.inr hM))
  have hm02 := t67_sq_of_decomp hZM hm0M hd hm0d (t67_sq_eq_one hm2)
  have hm01 : m0 ≠ 1 := fun h => hMm (by
    rw [← hm0d, h, one_mul]
    exact t67_mem_centralizer_iff.1 hd)
  have hm0o : orderOf m0 = 2 := orderOf_eq_prime hm02 hm01
  have hm0eq : m0 = m * d⁻¹ := by rw [← hm0d]; group
  have hdm0 : d * m0 = m0 * d := (mem_centralizer_iff.1 hd m0 hm0M).symm
  have hMMt : M ≤ cen t := t67_le_of_sec6KComp (Or.inr hM)
  have hMc0 : ∀ x ∈ M, x * (m * t) = (m * t) * x → x * m0 = m0 * x := by
    intro x hx hxy
    have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 (hMMt hx)
    have hxm : x * m = m * x := by
      have h1 : x * m * t = m * x * t := by
        calc x * m * t = x * (m * t) := by group
          _ = m * t * x := hxy
          _ = m * (t * x) := by group
          _ = m * (x * t) := by rw [hxt]
          _ = m * x * t := by group
      exact mul_right_cancel h1
    have hxd : x * d = d * x := mem_centralizer_iff.1 hd x hx
    rw [hm0eq]
    calc x * (m * d⁻¹) = (x * m) * d⁻¹ := by group
      _ = (m * x) * d⁻¹ := by rw [hxm]
      _ = m * (x * d⁻¹) := by group
      _ = m * (d⁻¹ * x) := by
          rw [show x * d⁻¹ = d⁻¹ * x from by
            rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hxd, mul_assoc, mul_inv_cancel, mul_one]]
      _ = m * d⁻¹ * x := by group
  have hm0y : m0 ∈ cen (m * t) := by
    refine mem_centralizer_singleton_iff.2 ?_
    have hm0t : m0 * t = t * m0 := mem_centralizer_singleton_iff.1 (hMMt hm0M)
    have hm0m : m0 * m = m * m0 := by
      rw [← hm0d]
      calc m0 * (m0 * d) = m0 * m0 * d := by group
        _ = m0 * (m0 * d) := by group
        _ = m0 * (d * m0) := by rw [hdm0]
        _ = m0 * d * m0 := by group
    calc m0 * (m * t) = (m0 * m) * t := by group
      _ = (m * m0) * t := by rw [hm0m]
      _ = m * (m0 * t) := by group
      _ = m * (t * m0) := by rw [hm0t]
      _ = m * t * m0 := by group
  have hm0W : m0 ∈ Sec6K X n (cen (m * t)) ⊓ centralizer (Sec6K X n (cen (m * t)) : Set X) := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have hm0P : m0 ∈ sec6Piece M (m * t) :=
        mem_oTwoPrimeOf (Subgroup.mem_inf.2 ⟨hm0M, hm0y⟩) 1 (by simpa using hm02)
      obtain ⟨F, hF, hPF⟩ := hC.land (m * t) (t67_base_le_MQ hT hodd hyB) hy2 M (Or.inr hM)
      exact t67_le_K hF (hPF hm0P)
    · rw [t67_mem_centralizer_iff]
      refine sSup_le fun F hF => ?_
      obtain ⟨L, hL, rfl⟩ := t67_pu hT hS hK h61 hC h65 hodd hyB hy2 hVy hF
      intro x hx
      by_cases hLM : L = M
      · subst hLM
        obtain ⟨hxL, hxy⟩ := Subgroup.mem_inf.1 ((oTwoPrimeOf_le _) hx)
        exact mem_centralizer_singleton_iff.2 (hMc0 x hxL (mem_centralizer_singleton_iff.1 hxy))
      · have hxL : x ∈ L := t67_piece_le hx
        exact mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1
          (t67_Kt_cen hodd (Or.inr hM) hL (Ne.symm hLM) hxL) m0 hm0M).symm)
  have hm0Mt : m0 ∈ Sec6M X n (cen t) := t67_le_M hM hm0M
  have hVE : t67VE n (Sec6K X n (cen (m * t)) ⊓ centralizer (Sec6K X n (cen (m * t)) : Set X)) =
      sec6V X n t := by
    refine le_antisymm (t67_VE_le fun w hw hw2 => ?_) ?_
    · obtain ⟨hw1, hw2'⟩ := Subgroup.mem_inf.1 hw
      have hwC : w ∈ centralizer (K0 X n (cen t) : Set X) := by
        rw [t67_mem_centralizer_iff]
        exact hAy.trans (t67_mem_centralizer_iff.1 hw2')
      have hwB : w ∈ Sec6Base X n t :=
        t67_KC_le_base hT hodd (Subgroup.mem_inf.2 ⟨hKy hw1, hwC⟩)
      exact t67_v2_K_le_V hT hS hK h61 hC h65 hodd hA hM0 hMM hMc hVeq hwB hw2
    · rw [hVeq]
      refine sup_le ?_ ((t67_M_le_K _).trans (t67_le_VE htW hS.choice.inv))
      exact (t67_v2_M0_le hT hS hK hC h65 hodd hA hM0 hMc hVeq hm0Mt hm0o).trans
        ((t67_M_le_K _).trans (t67_le_VE hm0W hm0o))
  exact t67_le_normalizer_of_VE ((Sec6K_cen_normal n (m * t)).trans
    (t67_normalizer_le_normalizer_Z _)) hVE

include hT hS hK h61 hC h65 hodd hA hM0 hMM hMc hVeq in
private theorem t67_v2_main (hII : Sec6CtrlNAt X n t (normalizer (sec6V X n t : Set X))) {x : X}
    (hx : x ∈ Sec6R X n (normalizer (sec6V X n t : Set X))) (hx2 : orderOf x = 2) :
    cen x ≤ normalizer (sec6V X n t : Set X) := by
  have hOV := t67_v2_odd hT hS hC hodd hA hM0 hMc hVeq
  have hKV := t67_K_le_V hT hS hC hodd
  have hFV : ∀ F, Sec6KComp X n (normalizer (sec6V X n t : Set X)) F → F ≤ sec6V X n t := by
    intro F hF
    obtain ⟨L, hL, hFL | ⟨-, -, -, -, hFV⟩⟩ := t67_KN hII hOV hKV hF
    · rw [hFL]
      exact (t67_le_K hL).trans hKV
    · exact hFV
  have hRV : Sec6R X n (normalizer (sec6V X n t : Set X)) ≤ sec6V X n t := by
    refine sup_le ((t67_zStar_le _).trans ?_) (sSup_le fun F h => hFV F (Or.inr h))
    rw [K0_eq_sSup_sec5Comp]
    exact sSup_le fun F h => hFV F (Or.inl h)
  have htM0 := t67_v2_t_mem hT hS hC hodd hA hMc hVeq
  obtain ⟨a, ha, b, hb, rfl⟩ := t67_v2_decomp hMc (hVeq ▸ hRV hx)
  have hba : b * a = a * b := mem_centralizer_iff.1 (hMc ha) b hb
  have ha2b2 : a ^ 2 = 1 ∧ b ^ 2 = 1 := by
    have h1 := t67_sq_eq_one hx2
    rw [(show Commute a b from hba.symm).mul_pow] at h1
    have h2 : a ^ 2 = (b ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : a ^ 2 ∈ M0 ⊓ Sec6M X n (cen t) := by
      refine Subgroup.mem_inf.2 ⟨pow_mem ha 2, ?_⟩
      rw [h2]
      exact inv_mem (pow_mem hb 2)
    rw [hMM, mem_bot] at h3
    refine ⟨h3, ?_⟩
    rw [h3, one_mul] at h1
    exact h1
  have hVN : sec6V X n t ≤ normalizer (sec6V X n t : Set X) := Subgroup.le_normalizer
  by_cases ha1 : a = 1
  · subst ha1
    rw [one_mul] at hx2 ⊢
    exact t67_v2_cen_le_M hT hS hK hC h65 hodd hA hM0 hMM hMc hVeq hb hx2
  · have ha2 : orderOf a = 2 := orderOf_eq_prime ha2b2.1 ha1
    obtain ⟨g, hg⟩ := isConj_iff.1 (hT.conj ↥M0 hM0 ⟨a, ha⟩ ⟨t, htM0⟩
      (by rw [Subgroup.orderOf_mk]; exact ha2) (by rw [Subgroup.orderOf_mk]; exact hS.choice.inv))
    have hg' : (g : X) * a * (g : X)⁻¹ = t := congrArg Subtype.val hg
    have hgb : (g : X) * b = b * (g : X) := (mem_centralizer_iff.1 (hMc g.2) b hb).symm
    have hxeq : a * b = (MulAut.conj (g : X)⁻¹) (b * t) := by
      rw [MulAut.conj_apply, inv_inv, ← hg']
      calc a * b = (g : X)⁻¹ * ((g : X) * a * (g : X)⁻¹) * (g : X) * b := by group
        _ = (g : X)⁻¹ * ((g : X) * a * (g : X)⁻¹) * ((g : X) * b) := by group
        _ = (g : X)⁻¹ * ((g : X) * a * (g : X)⁻¹) * (b * (g : X)) := by rw [hgb]
        _ = (g : X)⁻¹ * (b * ((g : X) * a * (g : X)⁻¹)) * (g : X) := by
            rw [show (g : X) * a * (g : X)⁻¹ = t from hg']
            rw [show b * t = t * b from (mem_centralizer_iff.1 (hMc htM0) b hb)]
            group
    have hcy : cen (b * t) ≤ normalizer (sec6V X n t : Set X) := by
      by_cases hb1 : b = 1
      · rw [hb1, one_mul]
        exact cen_le_normalizer_sec6V n t
      · exact t67_v2_cen_le_mt hT hS hK h61 hC h65 hodd hA hM0 hMM hMc hVeq hb
          (orderOf_eq_prime ha2b2.2 hb1)
    have hgN : (g : X)⁻¹ ∈ normalizer (sec6V X n t : Set X) :=
      inv_mem (hVN (hVeq ▸ Subgroup.mem_sup_left g.2))
    rw [hxeq, ← cen_map]
    calc (cen (b * t)).map (MulAut.conj (g : X)⁻¹).toMonoidHom
        ≤ (normalizer (sec6V X n t : Set X)).map (MulAut.conj (g : X)⁻¹).toMonoidHom :=
          Subgroup.map_mono hcy
      _ = normalizer (sec6V X n t : Set X) :=
          map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hgN)

end V2Facts

end V2

theorem sec6Thm67_ne_top (hS : Sec6Setting X n t)
    (hV : sec6V X n t = Sec6K X n (cen t) ∨ ∃ M0 : Subgroup X, IsSec6MType n ↥M0 ∧
      M0 ⊓ Sec6M X n (cen t) = ⊥ ∧ M0 ≤ centralizer (Sec6M X n (cen t) : Set X) ∧
      sec6V X n t = M0 ⊔ Sec6M X n (cen t)) :
    normalizer (sec6V X n t : Set X) ≠ ⊤ := by
  haveI := hS.cex.simple
  intro htop
  haveI hVn : (sec6V X n t).Normal := normalizer_eq_top_iff.1 htop
  have hMV : Sec6M X n (cen t) ≤ sec6V X n t := by
    rcases hV with hV | ⟨M0, -, -, -, hV⟩
    · rw [hV]
      exact t67_M_le_K _
    · rw [hV]
      exact le_sup_right
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (sec6V X n t) with hb | hVt
  · exact t67_Mt_ne_bot hS (le_bot_iff.1 (hb ▸ hMV))
  · rcases hV with hVK | ⟨M0, -, -, hM0c, hVM⟩
    · exact t67_not_top_le_cen hS (hVt ▸ hVK ▸ t67_K_le (cen t))
    ·
      haveI hMn : (Sec6M X n (cen t)).Normal := by
        refine normalizer_eq_top_iff.1 (eq_top_iff.2 ?_)
        rw [← hVt, hVM]
        exact sup_le (hM0c.trans (centralizer_le_normalizer _))
          (le_normalizer (H := Sec6M X n (cen t)))
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Sec6M X n (cen t)) with hb | hMt
      · exact t67_Mt_ne_bot hS hb
      · exact t67_not_top_le_cen hS (hMt ▸ (t67_M_le_K _).trans (t67_K_le (cen t)))

private theorem t67_oddN_inf_le (V : Subgroup X) :
    oddCoreOf (normalizer (V : Set X)) ⊓ V ≤ oddCoreOf V := by
  have hVN : V ≤ normalizer (V : Set X) := Subgroup.le_normalizer
  refine le_oddCoreOf_of_normalized inf_le_right (fun v hv => t67_mem_normalizer_inf ?_
    (Subgroup.le_normalizer hv)) ?_
  · exact normalizer_le_normalizer_pPrimeCoreOf _ (Subgroup.le_normalizer (hVN hv))
  · exact Odd.of_dvd_nat (odd_card_oddCoreOf _) (Subgroup.card_dvd_of_le inf_le_left)

private theorem t67_comm_mem_oddN_inf {V : Subgroup X} {o v : X}
    (ho : o ∈ oddCoreOf (normalizer (V : Set X))) (hv : v ∈ V) :
    ⁅o, v⁆ ∈ oddCoreOf (normalizer (V : Set X)) ⊓ V := by
  have hvN : v ∈ normalizer (V : Set X) := Subgroup.le_normalizer hv
  have hoN : o ∈ normalizer (V : Set X) := oddCoreOf_le _ ho
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have h := (mem_normalizer_iff.1 (normalizer_le_normalizer_pPrimeCoreOf _
      (Subgroup.le_normalizer hvN)) o⁻¹).1 (inv_mem ho)
    have h' : v * o⁻¹ * v⁻¹ ∈ oddCoreOf (normalizer (V : Set X)) := h
    have e : ⁅o, v⁆ = o * (v * o⁻¹ * v⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem ho h'
  · rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.1 hoN v).1 hv) (inv_mem hv)

private theorem t67_t_zStar (hS : Sec6Setting X n t) (hA : K0 X n (cen t) ≠ ⊥) :
    t ∈ zStar (K0 X n (cen t)) := by
  have htA := hS.central hA
  refine Subgroup.mem_inf.2 ⟨htA, Subgroup.le_normalizer htA,
    normalizer_le_normalizer_pPrimeCoreOf _ (Subgroup.le_normalizer htA), fun k hk => ?_⟩
  have hkt : k ∈ cen t := ((t67_A_le_K _).trans (t67_K_le _)) hk
  rw [commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_singleton_iff.1 hkt)]
  exact one_mem _

private theorem t67b_main (hT : Sec6T67Facts n) (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (h65 : Sec6L65 X n t) (hA0 : K0 X n (cen t) = ⊥)
    (hOZ : oddCoreOf (Sec6K X n (cen t)) ≤ centralizer (Sec6K X n (cen t) : Set X))
    (hV : sec6V X n t = Sec6K X n (cen t) ∨ ∃ M0 : Subgroup X, IsSec6MType n ↥M0 ∧
      M0 ⊓ Sec6M X n (cen t) = ⊥ ∧ M0 ≤ centralizer (Sec6M X n (cen t) : Set X) ∧
      sec6V X n t = M0 ⊔ Sec6M X n (cen t))
    (hII : Sec6CtrlNAt X n t (normalizer (sec6V X n t : Set X))) {x : X}
    (hx : x ∈ Sec6R X n (normalizer (sec6V X n t : Set X))) (hx2 : orderOf x = 2) :
    cen x ≤ normalizer (sec6V X n t : Set X) := by
  have hKM := t67b_KM hA0
  have hV1 : sec6V X n t = Sec6K X n (cen t) := by
    rcases hV with hV1 | ⟨M0, hM0, hMM, hMc, hVeq⟩
    · exact hV1
    · exfalso
      have hKy : ∀ y ∈ Sec6M X n (cen t), orderOf y = 2 →
          Sec6K X n (cen y) ≤ Sec6M X n (cen t) := by
        intro y hy hy2
        refine sSup_le fun F hF => ?_
        have hyB : y ∈ Sec6Base X n t := Subgroup.mem_sup_left hy
        have hOy := h65 y hyB hy2
        have hyMQ : y ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) := Subgroup.mem_sup_left hy
        obtain ⟨L, hL, hPL⟩ := hC.piece y hyMQ hy2 F hF
        have hLM : Sec6MComp X n (cen t) L := hL.resolve_left fun h => t67b_no5 hA0 h
        rcases (hC.dich y hyMQ hy2 L F hL hF hPL).2 with heq | ⟨hFM, hnc, -, -, -⟩
        · rw [heq, show oddCoreOf F = ⊥ from t67_odd_eq_bot hF hOy, bot_sup_eq]
          exact t67_piece_le.trans (t67_le_M hLM)
        · exfalso
          have hOF := t67_odd_eq_bot (Or.inr hFM) hOy
          have hFV : F ≤ M0 ⊔ Sec6M X n (cen t) :=
            hVeq ▸ (t67_le_K (Or.inr hFM)).trans (t67_le_V hy hy2)
          have hdisj := t67_v2_pump_disj hT hMc hFM hOF hFV hnc
          obtain ⟨w, -, hwL, -, hw2, -, -, -, hwP, -⟩ :=
            t67b_piece_inv hT hA0 hOZ hLM (t67_M_le_K _ hy) hy2
          exact t67_ne_one_of_orderOf hw2 (hdisj.le_bot
            (Subgroup.mem_inf.2 ⟨t67_le_M hLM hwL, hPL hwP⟩))
      have hVM : sec6V X n t ≤ Sec6M X n (cen t) :=
        iSup_le fun y => iSup_le fun hy => iSup_le fun hy2 => hKy y hy hy2
      have hM0b : M0 ≤ ⊥ := by
        rw [← hMM]
        exact le_inf le_rfl ((hVeq ▸ le_sup_left : M0 ≤ sec6V X n t).trans hVM)
      haveI := hT.simple _ hM0
      obtain ⟨a, b, hab⟩ := exists_pair_ne ↥M0
      apply hab
      have ha : (a : X) = 1 := mem_bot.1 (hM0b a.2)
      have hb : (b : X) = 1 := mem_bot.1 (hM0b b.2)
      exact Subtype.ext (ha.trans hb.symm)
  have hVp : ⁅sec6V X n t, sec6V X n t⁆ = sec6V X n t := by
    rw [hV1, hKM]
    refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) ?_
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    · refine sSup_le fun L hL => ?_
      rw [← t67b_perfect (t67_twoGenQuasi (Or.inr hL)) (t67b_Oc hOZ (Or.inr hL))]
      exact Subgroup.commutator_mono (t67_le_M hL) (t67_le_M hL)
  have hOVc : oddCoreOf (sec6V X n t) ≤ centralizer (sec6V X n t : Set X) := hV1 ▸ hOZ
  have hON : oddCoreOf (normalizer (sec6V X n t : Set X)) ≤
      centralizer (sec6V X n t : Set X) := fun o ho =>
    t67b_cent hVp hOVc (oddCoreOf_le _) fun g hg =>
      t67_oddN_inf_le _ (t67_comm_mem_oddN_inf ho hg)
  have hKN : ∀ F, Sec6KComp X n (normalizer (sec6V X n t : Set X)) F →
      ∃ L, Sec6MComp X n (cen t) L ∧ F = L := by
    intro F hF
    obtain ⟨L, hL, hLF⟩ := hII.piece F hF
    have hLM : Sec6MComp X n (cen t) L := hL.resolve_left fun h => t67b_no5 hA0 h
    rcases hII.dich L F hL hF hLF with heq | ⟨-, hLA, -⟩
    · refine ⟨L, hLM, le_antisymm ?_ hLF⟩
      have hOF : pPrimeCoreOf 2 F ≤ oddCoreOf (normalizer (sec6V X n t : Set X)) :=
        pPrimeCoreOf_le_oddCoreOf (t67_isPCompIn hF).1 (t67_subnormal hF)
      have hLV : L ≤ sec6V X n t := by
        rw [hV1]
        exact t67_le_K hL
      exact t67_le_of_mul (t67_oTwo_eq (t67_twoGenQuasi hF)) heq.le
        (hLF.trans fun f hf => mem_normalizer_pPrimeCoreOf_of_mem hf) (odd_card_oddCoreOf F)
        fun o ho d hd => (mem_centralizer_iff.1 (hON (hOF ho)) d (hLV hd)).symm
    · exact (t67b_no5 hA0 hLA).elim
  have hRM : Sec6R X n (normalizer (sec6V X n t : Set X)) ≤ Sec6M X n (cen t) := by
    have hA'0 : K0 X n (normalizer (sec6V X n t : Set X)) = ⊥ := by
      rw [K0_eq_sSup_sec5Comp]
      refine sSup_eq_bot.2 fun F hF => ?_
      obtain ⟨L, hLM, rfl⟩ := hKN F (Or.inl hF)
      exact (t67_not_sec5_of_M hT hF hLM).elim
    refine sup_le ?_ (sSup_le fun F hF => ?_)
    · rw [hA'0]
      exact (t67_zStar_le ⊥).trans bot_le
    · obtain ⟨L, hLM, rfl⟩ := hKN F (Or.inr hF)
      exact t67_le_M hLM
  have hxM : x ∈ Sec6M X n (cen t) := hRM hx
  have hVE : t67VE n (Sec6K X n (cen x)) = sec6V X n t := by
    refine le_antisymm (t67_VE_le fun w hw hw2 => t67_le_V ?_ hw2) ?_
    · have := t67_le_V hxM hx2 hw
      rwa [hV1, hKM] at this
    · rw [hV1, hKM]
      refine sSup_le fun L hL => ?_
      obtain ⟨w, w', hwL, hw'L, hw2, hw2', hne, hc, hwP, hw'P⟩ :=
        t67b_piece_inv hT hA0 hOZ hL (t67_M_le_K _ hxM) hx2
      obtain ⟨F, hF, hPF⟩ := hC.land x (Subgroup.mem_sup_left hxM) hx2 L (Or.inr hL)
      exact (t67b_gen hT hC hOZ hL hwL hw'L hw2 hw2' hne hc).trans
        (sup_le (t67_le_VE (t67_le_K hF (hPF hwP)) hw2) (t67_le_VE (t67_le_K hF (hPF hw'P)) hw2'))
  exact t67_le_normalizer_of_VE (Sec6K_cen_normal n x) hVE

theorem sec6Thm67Cen_ofV
    (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n) (h61 : Sec6L61 X n t)
    (hC : Sec6CtrlAt X n t) (h65 : Sec6L65 X n t)
    (hV : sec6V X n t = Sec6K X n (cen t) ∨ ∃ M0 : Subgroup X, IsSec6MType n ↥M0 ∧
      M0 ⊓ Sec6M X n (cen t) = ⊥ ∧ M0 ≤ centralizer (Sec6M X n (cen t) : Set X) ∧
      sec6V X n t = M0 ⊔ Sec6M X n (cen t))
    (hOZ : K0 X n (cen t) = ⊥ →
      oddCoreOf (Sec6K X n (cen t)) ≤ centralizer (Sec6K X n (cen t) : Set X))
    (hII : Sec6CtrlNAt X n t (normalizer (sec6V X n t : Set X)))
    (hgenM : ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* Blueprint.NativeSporadic.McL) →
      ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x ≠ y → x * y = y * x →
        centralizer ({x} : Set G) ⊔ centralizer ({y} : Set G) = ⊤)
    (hgenL : ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* Blueprint.NativeSporadic.Ly) →
      ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x ≠ y → x * y = y * x →
        centralizer ({x} : Set G) ⊔ centralizer ({y} : Set G) = ⊤) :
    normalizer (sec6V X n t : Set X) ≠ ⊤ ∧
      ∀ x ∈ Sec6R X n (normalizer (sec6V X n t : Set X)), orderOf x = 2 →
        cen x ≤ normalizer (sec6V X n t : Set X) := by
  have hT := t67Facts_of hS.deg hgenM hgenL
  refine ⟨sec6Thm67_ne_top hS hV, fun x hx hx2 => ?_⟩
  by_cases hA : K0 X n (cen t) = ⊥
  · exact t67b_main hT hS hC h65 hA (hOZ hA) hV hII hx hx2
  · have htZ := t67_t_zStar hS hA
    have hodd : oddCoreOf (Sec6K X n (cen t)) = ⊥ := le_bot_iff.1 ((t67_oddK_le t).trans
      (le_of_eq (h65 t (Subgroup.mem_sup_right htZ) hS.choice.inv)))
    rcases hV with hV1 | ⟨M0, hM0, hMM, hMc, hVeq⟩
    · exact t67_cen_le_V1 hT hS hK h61 hC h65 hodd hA hV1 (t67_R_le_base hT hII hodd hV1 hx) hx2
    · exact t67_v2_main hT hS hK h61 hC h65 hodd hA hM0 hMM hMc hVeq hII hx hx2

end Thm67

end CFSG.OddStandard.Solomon75
