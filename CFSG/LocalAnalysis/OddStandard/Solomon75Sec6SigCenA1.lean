module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6CtrlNDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Equiv
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3CenterFree
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33Cover
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GammaHub
import CFSG.Holt.StarCase.Lemma26Basic
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Reduce
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6CtrlDefs
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51Cover

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

section SigCen

variable {X : Type} [Group X] [Finite X]

private theorem sigcen_isPCompIn_of_sec6KComp {n : ℕ} {H L : Subgroup X}
    (hL : Sec6KComp X n H L) : IsPCompIn 2 H L := by
  rcases hL with ⟨⟨u, hu⟩, -⟩ | ⟨hM, -⟩
  · exact hu.2.2.1
  · exact hM.1

private theorem sigcen_isTwoGenQuasi {H L : Subgroup X} (hL : IsPCompIn 2 H L) :
    IsTwoGenQuasi ↥L :=
  (isTwoGenQuasi_subgroupOf_iff hL.1).1 (isPComponent_two_iff.1 hL.2).2

private theorem sigcen_oddCoreOf_le {H L : Subgroup X} (hL : IsPCompIn 2 H L) :
    oddCoreOf L ≤ oddCoreOf H :=
  pPrimeCoreOf_le_oddCoreOf hL.1 (isPComponent_two_iff.1 hL.2).1

private theorem sigcen_not_sec5Comp {n : ℕ} {H L : Subgroup X} (h : K0 X n H = ⊥) :
    ¬ Sec5Comp X n H L := by
  intro hL
  have hle : L ≤ K0 X n H := by
    rw [K0_eq_sSup_sec5Comp]
    exact le_sSup hL
  rw [h] at hle
  obtain ⟨⟨u, hu⟩, -⟩ := hL
  exact not_le_oddCoreOf_of_isTwoGenQuasi (C := ⊤) (sigcen_isTwoGenQuasi hu.2.2.1)
    (hle.trans bot_le)

private theorem sigcen_two_dvd_card {E : Subgroup X} (hq : IsTwoGenQuasi ↥E) :
    2 ∣ Nat.card E := by
  by_contra h
  have hodd : Odd (Nat.card E) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)
  exact not_le_oddCoreOf_of_isTwoGenQuasi hq
    (le_oddCoreOf_of_normalized le_rfl Subgroup.le_normalizer hodd)

private theorem sigcen_map_map_symm (φ : X ≃* X) (K : Subgroup X) :
    (K.map φ.symm.toMonoidHom).map φ.toMonoidHom = K := by
  rw [Subgroup.map_map]
  have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id X := by ext x; simp
  rw [this, Subgroup.map_id]

private theorem sigcen_map_symm_map (φ : X ≃* X) (K : Subgroup X) :
    (K.map φ.toMonoidHom).map φ.symm.toMonoidHom = K := by
  rw [Subgroup.map_map]
  have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id X := by ext x; simp
  rw [this, Subgroup.map_id]

private theorem sigcen_isElemAbelian_map (φ : X ≃* X) {B : Subgroup X}
    (hB : CFSG.Open.IsElemAbelian 2 B) : CFSG.Open.IsElemAbelian 2 (B.map φ.toMonoidHom) := by
  have h2 : ∀ y ∈ B.map φ.toMonoidHom, y ^ 2 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, hB.2 b hb, map_one]
  exact ⟨⟨⟨fun a b => Subtype.ext (comm_of_sq_eq_one h2 a.2 b.2)⟩⟩, h2⟩

private theorem sigcen_map_sigB_le (φ : X ≃* X) (B : Subgroup X) :
    (⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), oddCoreOf (cen b)).map φ.toMonoidHom ≤
      ⨆ (b : X) (_ : b ∈ B.map φ.toMonoidHom) (_ : b ≠ 1), oddCoreOf (cen b) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
  rw [← Subgroup.map_le_iff_le_comap, oddCoreOf_map_mulEquiv', cen_map]
  exact le_iSup_of_le (φ b) (le_iSup_of_le (Subgroup.mem_map_of_mem φ.toMonoidHom hb)
    (le_iSup_of_le (fun h => hb1 ((MulEquiv.map_eq_one_iff φ).1 h)) le_rfl))

private theorem sigcen_sigB_map (φ : X ≃* X) (B : Subgroup X) :
    (⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), oddCoreOf (cen b)).map φ.toMonoidHom =
      ⨆ (b : X) (_ : b ∈ B.map φ.toMonoidHom) (_ : b ≠ 1), oddCoreOf (cen b) := by
  refine le_antisymm (sigcen_map_sigB_le φ B) ?_
  have h := Subgroup.map_mono (f := φ.toMonoidHom)
    (sigcen_map_sigB_le φ.symm (B.map φ.toMonoidHom))
  rwa [sigcen_map_map_symm, sigcen_map_symm_map] at h

private theorem sigcen_exists_conj_le_of_normal {G : Type*} [Group G] [Finite G]
    {A N P : Subgroup G} [N.Normal] (hN : Odd (Nat.card N)) (hP : IsPGroup 2 P)
    (hPAN : P ≤ A ⊔ N) : ∃ o ∈ N, ∀ y ∈ P, o⁻¹ * y * o ∈ A := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAH : A ≤ A ⊔ N := le_sup_left
  have hidxA : ¬ 2 ∣ A.relIndex (A ⊔ N) := by
    have h1 : A.relIndex (A ⊔ N) * Nat.card A = Nat.card ↥(A ⊔ N) := by
      have := Subgroup.relIndex_mul_card A (A ⊔ N)
      rwa [inf_of_le_left hAH] at this
    have h2 : N.relIndex A * Nat.card N = Nat.card ↥(A ⊔ N) := by
      have := Subgroup.relIndex_mul_card N (A ⊔ N)
      rwa [inf_of_le_left (le_sup_right : N ≤ A ⊔ N), Subgroup.relIndex_sup_right] at this
    have h3 : N.relIndex A * Nat.card ↥(N ⊓ A) = Nat.card A := Subgroup.relIndex_mul_card N A
    have hpos : 0 < N.relIndex A := Nat.pos_of_ne_zero fun h => by
      rw [h, zero_mul] at h3
      exact Nat.card_pos.ne' h3.symm
    have h4 : N.relIndex A * (A.relIndex (A ⊔ N) * Nat.card ↥(N ⊓ A)) =
        N.relIndex A * Nat.card N := by
      rw [h2, ← h1, ← h3]
      ring
    have h5 := Nat.eq_of_mul_eq_mul_left hpos h4
    intro hd
    exact (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 (hd.trans ⟨_, h5.symm⟩))
  let A₀ : Subgroup ↥(A ⊔ N) := A.subgroupOf (A ⊔ N)
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥A₀) := inferInstance
  let T₁ : Subgroup ↥(A ⊔ N) := (T : Subgroup ↥A₀).map A₀.subtype
  have hT₁p : IsPGroup 2 T₁ := T.isPGroup'.map A₀.subtype
  have hT₁idx : ¬ 2 ∣ T₁.index := by
    rw [Subgroup.index_map_subtype]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with h | h
    · exact T.not_dvd_index h
    · exact hidxA h
  let S : Sylow 2 ↥(A ⊔ N) := hT₁p.toSylow hT₁idx
  have hPH : IsPGroup 2 (P.subgroupOf (A ⊔ N)) := hP.comap_subtype
  obtain ⟨Q, hQ⟩ := hPH.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥(A ⊔ N) S Q
  have hh' : (h : G) ∈ N ⊔ A := by
    rw [sup_comm]
    exact h.2
  obtain ⟨n, hn, a, ha, hna⟩ := Subgroup.mem_sup_of_normal_left.1 hh'
  refine ⟨n, hn, fun y hy => ?_⟩
  have hyH : y ∈ A ⊔ N := hPAN hy
  have hyQ : (⟨y, hyH⟩ : ↥(A ⊔ N)) ∈ (Q : Subgroup ↥(A ⊔ N)) :=
    hQ (show (⟨y, hyH⟩ : ↥(A ⊔ N)) ∈ P.subgroupOf (A ⊔ N) from hy)
  rw [← hh, mem_smul_sylow_iff_aux] at hyQ
  have h1 : h⁻¹ * ⟨y, hyH⟩ * h ∈ A₀ := by
    have hT : h⁻¹ * ⟨y, hyH⟩ * h ∈ T₁ := (IsPGroup.mem_toSylow hT₁p hT₁idx).1 hyQ
    obtain ⟨w, -, hw⟩ := hT
    rw [← hw]
    exact w.2
  have h2 : (h : G)⁻¹ * y * h ∈ A := Subgroup.mem_subgroupOf.1 h1
  have e : n⁻¹ * y * n = a * ((h : G)⁻¹ * y * h) * a⁻¹ := by
    rw [← hna]
    group
  rw [e]
  exact A.mul_mem (A.mul_mem ha h2) (A.inv_mem ha)

private theorem sigcen_exists_conj_le {A O P : Subgroup X} (hAO : A ≤ normalizer (O : Set X))
    (hO : Odd (Nat.card O)) (hP : IsPGroup 2 P) (hPAO : P ≤ A ⊔ O) :
    ∃ o ∈ O, ∀ y ∈ P, o⁻¹ * y * o ∈ A := by
  have hOD : O ≤ normalizer (O : Set X) := Subgroup.le_normalizer
  have hPD : P ≤ normalizer (O : Set X) := hPAO.trans (sup_le hAO hOD)
  have hMn : (O.subgroupOf (normalizer (O : Set X))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOD).2 le_rfl
  have hO' : Odd (Nat.card (O.subgroupOf (normalizer (O : Set X)))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOD).toEquiv]
    exact hO
  have hP' : IsPGroup 2 (P.subgroupOf (normalizer (O : Set X))) := hP.comap_subtype
  have hPAO' : P.subgroupOf (normalizer (O : Set X)) ≤
      A.subgroupOf (normalizer (O : Set X)) ⊔ O.subgroupOf (normalizer (O : Set X)) := by
    rw [← Subgroup.subgroupOf_sup hAO hOD]
    exact fun y hy => hPAO hy
  obtain ⟨o, ho, hoP⟩ := sigcen_exists_conj_le_of_normal hO' hP' hPAO'
  exact ⟨(o : X), Subgroup.mem_subgroupOf.1 ho, fun y hy =>
    Subgroup.mem_subgroupOf.1 (hoP ⟨y, hPD hy⟩ hy)⟩

private theorem sigcen_exists_sq_eq_one_mk {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] (hN : Odd (Nat.card N)) (u : G ⧸ N) (hu : u ^ 2 = 1) :
    ∃ s : G, s ^ 2 = 1 ∧ (s : G ⧸ N) = u := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective u
  have hg2 : g ^ 2 ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hu
  refine ⟨g ^ Nat.card N, ?_, ?_⟩
  · have h1 : (⟨g ^ 2, hg2⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
    rw [← pow_mul, mul_comm, pow_mul]
    exact h2
  · obtain ⟨k, hk⟩ := hN
    rw [QuotientGroup.mk_pow, hk, pow_succ, pow_mul, hu, one_pow, one_mul]

private theorem sigcen_exists_ne_of_isAhatIntr {J : Subgroup X} {s : X} (hJ : IsAhatIntr X s J) :
    ∃ r ∈ J, r ^ 2 = 1 ∧ r ≠ 1 ∧ r ≠ s := by
  obtain ⟨hJC, hsJ, -, m, hm, hdc⟩ := hJ
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, y, -, hy2, hyZ, -⟩ := AhatData.exists_hub hm (AhatData.CoverSetup.ofCover hdc)
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥J)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨r, hr2, hry⟩ :=
    sigcen_exists_sq_eq_one_mk (pPrimeCore 2 ↥J) hodd y (by rw [sq]; exact hy2)
  have hsZ : (⟨s, hsJ⟩ : ↥J) ∈ center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hJC g.2))
  have hmkZ : ∀ z : ↥J, z ∈ center ↥J →
      (z : ↥J ⧸ pPrimeCore 2 ↥J) ∈ center (↥J ⧸ pPrimeCore 2 ↥J) := fun z hz =>
    Subgroup.map_center_le_center (f := QuotientGroup.mk' (pPrimeCore 2 ↥J))
      (QuotientGroup.mk'_surjective _) (Subgroup.mem_map_of_mem _ hz)
  refine ⟨r, r.2, ?_, ?_, ?_⟩
  · have h := congrArg Subtype.val hr2
    simpa using h
  · intro h
    have hr : r = 1 := Subtype.ext h
    apply hyZ
    rw [← hry, hr, QuotientGroup.mk_one]
    exact Subgroup.one_mem _
  · intro h
    have hr : r = ⟨s, hsJ⟩ := Subtype.ext h
    apply hyZ
    rw [← hry, hr]
    exact hmkZ _ hsZ

private theorem sigcen_exists_four_of_isAhatIntr {s : X} {D J : Subgroup X} (hs : orderOf s = 2)
    (hsD : s ∈ D) (hJ : IsAhatIntr X s J) (hJD : J ≤ (D ⊓ cen s) ⊔ oddCoreOf (cen s)) :
    ∃ B : Subgroup X, B ≤ D ∧ CFSG.Open.IsElemAbelian 2 B ∧ Nat.card B = 4 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hrJ, hr2, hr1, hrs⟩ := sigcen_exists_ne_of_isAhatIntr hJ
  have hr2' : r ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact hr2
  obtain ⟨o, ho, a, ha, ha2, hra⟩ := exists_conj_twoElt_of_mem_sup_odd_X
    (A := D ⊓ cen s) (N := oddCoreOf (cen s))
    (fun c hc => le_normalizer_oddCoreOf (cen s) (Subgroup.mem_inf.1 hc).2)
    (odd_card_oddCoreOf _) (hJD hrJ) hr2'
  rw [pow_one] at ha2
  have hoC : o ∈ cen s := oddCoreOf_le _ ho
  have haD : a ∈ D := (Subgroup.mem_inf.1 ha).1
  have ha1 : a ≠ 1 := by
    intro h
    apply hr1
    rw [hra, h, mul_one, mul_inv_cancel]
  have has : a ≠ s := by
    intro h
    apply hrs
    have hcomm : o * s = s * o := Subgroup.mem_centralizer_singleton_iff.1 hoC
    rw [hra, h, hcomm, mul_inv_cancel_right]
  have hsa : s * a = a * s :=
    (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ha).2).symm
  have hss : s * s = 1 := by
    rw [← pow_two, ← hs]
    exact pow_orderOf_eq_one s
  have haa : a * a = 1 := by
    rw [← pow_two]
    exact ha2
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hs
    exact absurd hs (by norm_num)
  have hB2 : ∀ y ∈ Holt.StarLemma26.fourSubgroup hss haa hsa, y ^ 2 = 1 := fun y hy => by
    rw [pow_two]
    exact Holt.StarLemma26.mul_self_of_mem_fourSubgroup hy
  refine ⟨Holt.StarLemma26.fourSubgroup hss haa hsa, ?_,
    ⟨⟨⟨fun c d => Subtype.ext (comm_of_sq_eq_one hB2 c.2 d.2)⟩⟩, hB2⟩,
    Holt.StarLemma26.card_fourSubgroup hs1 ha1 has.symm⟩
  intro y hy
  rcases Holt.StarLemma26.mem_fourSubgroup.1 hy with rfl | rfl | rfl | rfl
  · exact D.one_mem
  · exact hsD
  · exact haD
  · exact D.mul_mem hsD haD

private theorem sigcen_exists_four_of_sec6KComp {n : ℕ} {H F : Subgroup X}
    (hF : Sec6KComp X n H F) :
    ∃ B : Subgroup X, B ≤ F ∧ CFSG.Open.IsElemAbelian 2 B ∧ Nat.card B = 4 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hF with ⟨⟨u, hu⟩, -⟩ | ⟨⟨hpc, -, hJ⟩, -⟩
  · obtain ⟨hu2, huF, -, -, Lu, hLu, hLueq⟩ := hu
    refine sigcen_exists_four_of_isAhatIntr hu2 huF hLu (hLueq.le.trans (sup_le ?_ ?_))
    · exact (pPrimeCoreOf_le_oddCoreOf hLu.1 (isPComponent_two_iff.1 hLu.2.2.1).1).trans
        le_sup_right
    · rw [oPrimeResidualOf_two_eq_oTwoPrimeOf]
      exact (oTwoPrimeOf_le _).trans le_sup_left
  · obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ↥F) 2
      (sigcen_two_dvd_card (sigcen_isTwoGenQuasi hpc))
    have hs2 : orderOf (s : X) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hs
    obtain ⟨J, hJs, hJle⟩ := hJ s s.2 hs2
    exact sigcen_exists_four_of_isAhatIntr hs2 s.2 hJs hJle

theorem sec6SigCen_of_mem_sec6M {n : ℕ} {t : X}
    (hM : ∃ M, Sec6MComp X n (cen t) M) (hC : Sec6CtrlAt X n t)
    (hA1 : K0 X n (cen t) = ⊥)
    (hU : ∀ x ∈ Sec6M X n (cen t), orderOf x = 2 → ∀ L F : Subgroup X,
      Sec6MComp X n (cen t) L → Sec6KComp X n (cen x) F → sec6Piece L x ≤ F →
        F = oddCoreOf F ⊔ sec6Piece L x)
    (hcan : ∀ B : Subgroup X, B ≤ Sec6M X n (cen t) → CFSG.Open.IsElemAbelian 2 B →
      Nat.card B = 4 → (⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), oddCoreOf (cen b)) = sec6Sig X n t)
    {x : X} (hx : x ∈ Sec6M X n (cen t)) (hx2 : orderOf x = 2) :
    cen x ≤ normalizer (sec6Sig X n t : Set X) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKt : ∀ L, Sec6KComp X n (cen t) L → Sec6MComp X n (cen t) L :=
    fun L hL => Or.resolve_left hL (sigcen_not_sec5Comp hA1)
  have hxb : x ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) := Subgroup.mem_sup_left hx
  have hOV : oddCoreOf (cen x) ≤ sec6Sig X n t :=
    le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le hx2 le_rfl))
  have hON : oddCoreOf (cen x) ≤ normalizer (sec6Sig X n t : Set X) :=
    hOV.trans Subgroup.le_normalizer
  have hKx : Sec6K X n (cen x) ≤ (Sec6M X n (cen t) ⊓ cen x) ⊔ oddCoreOf (cen x) := by
    refine sSup_le fun F hF => ?_
    obtain ⟨L, hL, hPF⟩ := hC.piece x hxb hx2 F hF
    have hLM := hKt L hL
    refine (hU x hx hx2 L F hLM hF hPF).le.trans (sup_le ?_ ?_)
    · exact (sigcen_oddCoreOf_le (sigcen_isPCompIn_of_sec6KComp hF)).trans le_sup_right
    · refine le_sup_of_le_left (le_inf ?_ ((oTwoPrimeOf_le (L ⊓ cen x)).trans inf_le_right))
      exact (oTwoPrimeOf_le (L ⊓ cen x)).trans
        (inf_le_left.trans (le_sSup (s := {M | Sec6MComp X n (cen t) M}) hLM))
  have hVB : ∀ B : Subgroup X, B ≤ Sec6K X n (cen x) → CFSG.Open.IsElemAbelian 2 B →
      Nat.card B = 4 →
        (⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), oddCoreOf (cen b)) = sec6Sig X n t := by
    intro B hB hBe hB4
    obtain ⟨o, ho, hoB⟩ := sigcen_exists_conj_le (A := Sec6M X n (cen t) ⊓ cen x)
      (O := oddCoreOf (cen x))
      (fun c hc => le_normalizer_oddCoreOf (cen x) (Subgroup.mem_inf.1 hc).2)
      (odd_card_oddCoreOf _) (isPGroup_two_of_sq hBe.2) (hB.trans hKx)
    obtain ⟨B₁, hB₁⟩ : ∃ B₁ : Subgroup X, B₁ = B.map (MulAut.conj o).symm.toMonoidHom := ⟨_, rfl⟩
    have hB₁M : B₁ ≤ Sec6M X n (cen t) := by
      rw [hB₁]
      rintro _ ⟨y, hy, rfl⟩
      have h := (Subgroup.mem_inf.1 (hoB y hy)).1
      simpa [MulAut.conj_symm_apply] using h
    have hB₁e : CFSG.Open.IsElemAbelian 2 B₁ := by
      rw [hB₁]
      exact sigcen_isElemAbelian_map _ hBe
    have hB₁4 : Nat.card B₁ = 4 := by
      rw [hB₁, Subgroup.card_map_of_injective (MulAut.conj o).symm.injective]
      exact hB4
    have hBB₁ : B = B₁.map (MulAut.conj o).toMonoidHom := by
      rw [hB₁, sigcen_map_map_symm]
    rw [hBB₁, ← sigcen_sigB_map, hcan B₁ hB₁M hB₁e hB₁4]
    exact map_conj_eq_of_mem_normalizer (hON ho)
  obtain ⟨M, hMt⟩ := hM
  obtain ⟨F, hF, -⟩ := hC.land x hxb hx2 M (Or.inr hMt)
  obtain ⟨B₀, hB₀F, hB₀e, hB₀4⟩ := sigcen_exists_four_of_sec6KComp hF
  have hB₀K : B₀ ≤ Sec6K X n (cen x) :=
    hB₀F.trans (le_sSup (s := {L | Sec6KComp X n (cen x) L}) hF)
  intro g hg
  apply mem_normalizer_of_map_conj_eq
  have hgK := map_conj_eq_of_mem_normalizer (Sec6K_cen_normal n x hg)
  have hB₀g : B₀.map (MulAut.conj g).toMonoidHom ≤ Sec6K X n (cen x) := by
    rw [← hgK]
    exact Subgroup.map_mono hB₀K
  have hB₀g4 : Nat.card ↥(B₀.map (MulAut.conj g).toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hB₀4
  calc (sec6Sig X n t).map (MulAut.conj g).toMonoidHom
      = (⨆ (b : X) (_ : b ∈ B₀) (_ : b ≠ 1), oddCoreOf (cen b)).map
          (MulAut.conj g).toMonoidHom := by
        rw [hVB B₀ hB₀K hB₀e hB₀4]
    _ = ⨆ (b : X) (_ : b ∈ B₀.map (MulAut.conj g).toMonoidHom) (_ : b ≠ 1),
          oddCoreOf (cen b) := sigcen_sigB_map _ B₀
    _ = sec6Sig X n t := hVB _ hB₀g (sigcen_isElemAbelian_map _ hB₀e) hB₀g4

end SigCen

theorem sec6SigCen_of_A_eq_bot_of_centerFree (hcf : McLLyCenterFree) {X : Type} [Group X]
    [Finite X] {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hA1 : K0 X n (cen t) = ⊥)
    (hU : ∀ x ∈ Sec6M X n (cen t), orderOf x = 2 → ∀ L F : Subgroup X,
      Sec6MComp X n (cen t) L → Sec6KComp X n (cen x) F → sec6Piece L x ≤ F →
        F = oddCoreOf F ⊔ sec6Piece L x)
    (hII : Sec6CtrlNAt X n t (normalizer (sec6Sig X n t : Set X)))
    (hcan : ∀ B : Subgroup X, B ≤ Sec6M X n (cen t) → CFSG.Open.IsElemAbelian 2 B →
      Nat.card B = 4 → (⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), oddCoreOf (cen b)) = sec6Sig X n t) :
    ∀ x ∈ Sec6R X n (normalizer (sec6Sig X n t : Set X)), orderOf x = 2 →
      cen x ≤ normalizer (sec6Sig X n t : Set X) := by
  intro x hx hx2
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnoA : ∀ L, ¬ Sec5Comp X n (cen t) L := fun L => sigcen_not_sec5Comp hA1
  have hN1 : ∀ F, Sec6KComp X n (normalizer (sec6Sig X n t : Set X)) F →
      ∃ L, Sec6MComp X n (cen t) L ∧ L ≤ F ∧ F = oddCoreOf F ⊔ L := by
    intro F hF
    obtain ⟨L, hL, hLF⟩ := hII.piece F hF
    refine ⟨L, Or.resolve_left hL (hnoA L), hLF, ?_⟩
    rcases hII.dich L F hL hF hLF with h | ⟨-, h, -⟩
    · exact h
    · exact absurd h (hnoA L)
  have hAN : K0 X n (normalizer (sec6Sig X n t : Set X)) = ⊥ := by
    rw [K0_eq_sSup_sec5Comp, sSup_eq_bot]
    intro A hA
    exfalso
    have hA' : Sec5Comp X n (normalizer (sec6Sig X n t : Set X)) A := hA
    obtain ⟨L, hL, hLA, hAeq⟩ := hN1 A (Or.inl hA')
    have hcov : L.subgroupOf A ⊔ pPrimeCore 2 ↥A = ⊤ := by
      rw [covers_subgroupOf_iff hLA, sup_comm]
      exact hAeq.symm
    obtain ⟨e⟩ := nonempty_quot_mulEquiv_of_covers hLA hcov
    have hZ : center (↥A ⧸ pPrimeCore 2 ↥A) = ⊥ := by
      rw [← Subgroup.map_center_eq e, hcf _ hL.1.2.1, Subgroup.map_bot]
    obtain ⟨-, hdc⟩ := hA'
    have h2 := hdc.2.1
    rw [hZ, Subgroup.card_bot] at h2
    exact absurd h2 (by norm_num)
  have hR : Sec6R X n (normalizer (sec6Sig X n t : Set X)) =
      Sec6M X n (normalizer (sec6Sig X n t : Set X)) := by
    have hz : zStar (⊥ : Subgroup X) = ⊥ := eq_bot_iff.2 inf_le_left
    unfold Sec6R
    rw [hAN, hz, bot_sup_eq]
  have hMN : Sec6M X n (normalizer (sec6Sig X n t : Set X)) ≤
      Sec6M X n (cen t) ⊔ oddCoreOf (normalizer (sec6Sig X n t : Set X)) := by
    refine sSup_le fun F hF => ?_
    have hF' : Sec6MComp X n (normalizer (sec6Sig X n t : Set X)) F := hF
    obtain ⟨L, hL, -, hFeq⟩ := hN1 F (Or.inr hF')
    refine hFeq.le.trans (sup_le ?_ ?_)
    · exact (sigcen_oddCoreOf_le hF'.1.1).trans le_sup_right
    · exact (le_sSup (s := {M | Sec6MComp X n (cen t) M}) hL).trans le_sup_left
  rw [hR] at hx
  have hx2' : x ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact hx2 ▸ pow_orderOf_eq_one x
  have hMtN : Sec6M X n (cen t) ≤ normalizer (sec6Sig X n t : Set X) :=
    (sSup_le fun L hL => hL.1.1.1).trans (cen_le_normalizer_sec6Sig n t)
  obtain ⟨o, ho, a, ha, ha2, hxa⟩ := exists_conj_twoElt_of_mem_sup_odd_X
    (A := Sec6M X n (cen t)) (N := oddCoreOf (normalizer (sec6Sig X n t : Set X)))
    (hMtN.trans (le_normalizer_oddCoreOf _)) (odd_card_oddCoreOf _) (hMN hx) hx2'
  rw [pow_one] at ha2
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, mul_one, mul_inv_cancel] at hxa
    rw [hxa, orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  have ha2' : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hCa := sec6SigCen_of_mem_sec6M hS.choice.hasM hC hA1 hU hcan ha ha2'
  have hoN : o ∈ normalizer (sec6Sig X n t : Set X) := oddCoreOf_le _ ho
  have hcx : cen x = (cen a).map (MulAut.conj o).toMonoidHom := by
    rw [cen_map, MulAut.conj_apply, hxa]
  rw [hcx]
  exact (Subgroup.map_mono hCa).trans
    (map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hoN)).le

theorem sec6SigCen_of_A_eq_bot
    {X : Type} [Group X] [Finite X] {n : ℕ} {t : X}
    (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n) (hC : Sec6CtrlAt X n t)
    (hA1 : K0 X n (cen t) = ⊥)
    (hU : ∀ x ∈ Sec6M X n (cen t), orderOf x = 2 → ∀ L F : Subgroup X, Sec6MComp X n (cen t) L →
      Sec6KComp X n (cen x) F → sec6Piece L x ≤ F → F = oddCoreOf F ⊔ sec6Piece L x)
    (hII : Sec6CtrlNAt X n t (normalizer (sec6Sig X n t : Set X)))
    (hcan : ∀ B : Subgroup X, B ≤ Sec6M X n (cen t) → CFSG.Open.IsElemAbelian 2 B →
      Nat.card B = 4 → (⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), oddCoreOf (cen b)) = sec6Sig X n t) :
    ∀ x ∈ Sec6R X n (normalizer (sec6Sig X n t : Set X)), orderOf x = 2 →
      cen x ≤ normalizer (sec6Sig X n t : Set X) :=
  sec6SigCen_of_A_eq_bot_of_centerFree mcLLyCenterFree hS hC hA1 hU hII hcan

end CFSG.OddStandard.Solomon75
