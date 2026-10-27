module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Parts
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Equiv
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33Cover
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51Cover

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section Restrict

variable {X : Type} [Group X] [Finite X]

theorem modOddCard_le_of_le {H K : Subgroup X} (h : H ≤ K) : modOddCard H ≤ modOddCard K :=
  card_quot_pPrimeCore_le_of_covers le_rfl h (by rw [Subgroup.subgroupOf_self, top_sup_eq])

theorem modOddCard_eq_of_covers {D K : Subgroup X} (hDK : D ≤ K)
    (hcov : K = pPrimeCoreOf 2 K ⊔ D) : modOddCard D = modOddCard K := by
  have hcov' : D.subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤ := by
    rw [covers_subgroupOf_iff hDK, sup_comm]
    exact hcov.symm
  exact Nat.card_congr (nonempty_quot_mulEquiv_of_covers hDK hcov').some.toEquiv

private theorem restr_odd_card (L : Subgroup X) : Odd (Nat.card (pPrimeCoreOf 2 L)) :=
  odd_card_oddCoreOf L

private theorem restr_conj_mem {S : Subgroup X} {c h : X} (hc : c ∈ normalizer (S : Set X))
    (hh : h ∈ S) : c * h * c⁻¹ ∈ S :=
  (Subgroup.mem_normalizer_iff.1 hc h).1 hh

private theorem restr_conj_inv_mem {S : Subgroup X} {c h : X} (hc : c ∈ normalizer (S : Set X))
    (hh : h ∈ S) : c⁻¹ * h * c ∈ S := by
  have := restr_conj_mem (Subgroup.inv_mem _ hc) hh
  rwa [inv_inv] at this

private theorem restr_comm_mem {O : Subgroup X} {a b s : X} (hs : s ∈ normalizer (O : Set X))
    (ha : a ∈ normalizer (O : Set X)) (hm : b⁻¹ * a ∈ O) (has : a * s = s * a) :
    ⁅b, s⁆ ∈ O := by
  generalize hm' : b⁻¹ * a = m at hm
  have hb : b = a * m⁻¹ := by rw [← hm']; group
  have e : ⁅b, s⁆ = a * (m⁻¹ * (s * m * s⁻¹)) * a⁻¹ := by
    rw [hb, commutatorElement_def]
    calc a * m⁻¹ * s * (a * m⁻¹)⁻¹ * s⁻¹ = a * m⁻¹ * s * m * (s * a)⁻¹ := by group
      _ = a * m⁻¹ * s * m * (a * s)⁻¹ := by rw [← has]
      _ = a * (m⁻¹ * (s * m * s⁻¹)) * a⁻¹ := by group
  rw [e]
  exact restr_conj_mem ha (O.mul_mem (O.inv_mem hm) (restr_conj_mem hs hm))

private theorem restr_isSubnormal_inf {K D D' H : Subgroup X} (hHD : H ≤ D) (hHD' : H ≤ D')
    (hK : (K.subgroupOf D).IsSubnormal) : ((K ⊓ D').subgroupOf H).IsSubnormal := by
  have h1 : (K ⊓ D').subgroupOf H = (K.subgroupOf D).comap (Subgroup.inclusion hHD) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, hHD' x.2⟩⟩
  rw [h1]
  exact hK.comap _

private theorem restr_isPCompIn_oTwoPrimeOf {H A : Subgroup X} (hAH : A ≤ H)
    (hA : (A.subgroupOf H).IsSubnormal) (hq : IsTwoGenQuasi ↥(oTwoPrimeOf A)) :
    IsPCompIn 2 H (oTwoPrimeOf A) := by
  have hEH : oTwoPrimeOf A ≤ H := (oTwoPrimeOf_le A).trans hAH
  refine ⟨hEH, isPComponent_two_iff.2 ⟨?_, (isTwoGenQuasi_subgroupOf_iff hEH).2 hq⟩⟩
  exact isSubnormal_subgroupOf_of_normal_of_subnormal hAH (oTwoPrimeOf_le A) hA
    (normal_subgroupOf_oTwoPrimeOf A)

private theorem restr_pPrimeCoreOf_le {F K : Subgroup X} (hFK : F ≤ K)
    (hcov : F.subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤) : pPrimeCoreOf 2 F ≤ pPrimeCoreOf 2 K := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥F →* ↥K ⧸ pPrimeCore 2 ↥K :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (Subgroup.inclusion hFK)
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    have hx : x ∈ F.subgroupOf K ⊔ pPrimeCore 2 ↥K := hcov ▸ Subgroup.mem_top x
    obtain ⟨f, hf, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    refine ⟨⟨(f : X), hf⟩, ?_⟩
    have h1 : (QuotientGroup.mk (f * o) : ↥K ⧸ pPrimeCore 2 ↥K) = QuotientGroup.mk f := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o).2 ho, mul_one]
    rw [h1]
    rfl
  have hN : ((pPrimeCore 2 ↥F).map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  have hcard : Nat.card ((pPrimeCore 2 ↥F).map φ) ∣ Nat.card (pPrimeCore 2 ↥F) :=
    Subgroup.card_map_dvd _ _
  have hle : (pPrimeCore 2 ↥F).map φ ≤ pPrimeCore 2 (↥K ⧸ pPrimeCore 2 ↥K) :=
    le_sSup ⟨hN, Nat.Coprime.coprime_dvd_right hcard pPrimeCore_coprime_card⟩
  rw [pPrimeCore_quotient_pPrimeCore_eq_bot] at hle
  rintro _ ⟨a, ha, rfl⟩
  have h2 : φ a = 1 := Subgroup.mem_bot.1 (hle ⟨a, ha, rfl⟩)
  exact ⟨Subgroup.inclusion hFK a, (QuotientGroup.eq_one_iff (Subgroup.inclusion hFK a)).1 h2,
    rfl⟩

private theorem restr_mem_centralizerSection_of_le_cen {K G : Subgroup X} {v : X}
    (hvK : v ∈ normalizer (K : Set X)) (hvO : v ∈ normalizer (pPrimeCoreOf 2 K : Set X))
    (hGK : G ≤ K) (hGv : G ≤ cen v) (hcov : G.subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤) :
    v ∈ centralizerSection K (pPrimeCoreOf 2 K) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hvK, hvO, fun k hk => ?_⟩
  have hk' : (⟨k, hk⟩ : ↥K) ∈ G.subgroupOf K ⊔ pPrimeCore 2 ↥K := hcov ▸ Subgroup.mem_top _
  obtain ⟨f, hf, o, ho, hfo⟩ := Subgroup.mem_sup_of_normal_right.1 hk'
  have hkfo : k = (f : X) * (o : X) := (congrArg Subtype.val hfo).symm
  have hfG : (f : X) ∈ G := hf
  have hoO : (o : X) ∈ pPrimeCoreOf 2 K := ⟨o, ho, rfl⟩
  have hfv : ⁅(f : X), v⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_singleton_iff.1 (hGv hfG))
  have hid : ⁅(f : X) * (o : X), v⁆ = (f : X) * ⁅(o : X), v⁆ * (f : X)⁻¹ * ⁅(f : X), v⁆ := by
    simp only [commutatorElement_def]
    group
  rw [hkfo, hid, hfv, mul_one]
  have hov : ⁅(o : X), v⁆ ∈ pPrimeCoreOf 2 K := by
    have h1 : v * (o : X)⁻¹ * v⁻¹ ∈ pPrimeCoreOf 2 K :=
      restr_conj_mem hvO ((pPrimeCoreOf 2 K).inv_mem hoO)
    have : ⁅(o : X), v⁆ = (o : X) * (v * (o : X)⁻¹ * v⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact (pPrimeCoreOf 2 K).mul_mem hoO h1
  exact restr_conj_mem (mem_normalizer_pPrimeCoreOf_of_mem f.2) hov

private theorem restr_commutatorElement_mem {H M J : Subgroup X} (hM : IsPCompIn 2 H M)
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

theorem isPCompIn_restrict {H L : Subgroup X} {g : X} (hL : IsPCompIn 2 H L) (hg2 : g ^ 2 = 1)
    (hgL : g ∈ centralizerSection L (pPrimeCoreOf 2 L)) :
    IsPCompIn 2 (H ⊓ cen g) (oTwoPrimeOf (L ⊓ cen g)) ∧
      (oTwoPrimeOf (L ⊓ cen g)).subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤ := by
  have hLq : IsTwoGenQuasi ↥L :=
    (isTwoGenQuasi_subgroupOf_iff hL.1).1 (isPComponent_two_iff.1 hL.2).2
  have hcov := oTwoPrimeOf_inf_centralizer_covers hg2 hLq.1 hgL
  have hEL : oTwoPrimeOf (L ⊓ cen g) ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hEq : IsTwoGenQuasi ↥(oTwoPrimeOf (L ⊓ cen g)) :=
    isTwoGenQuasi_of_covers hEL hcov (primeResidual_oTwoPrimeOf _) hLq
  exact ⟨restr_isPCompIn_oTwoPrimeOf (inf_le_inf_right _ hL.1)
    (restr_isSubnormal_inf inf_le_left inf_le_right (isPComponent_two_iff.1 hL.2).1) hEq, hcov⟩

private theorem restr_exists_isIntrinsicIn {H H' K : Subgroup X} {u g : X}
    (hK : IsIntrinsicIn X H K u)
    (hcovE : (oTwoPrimeOf (K ⊓ cen g)).subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤)
    (hEpc : IsPCompIn 2 H' (oTwoPrimeOf (K ⊓ cen g))) :
    ∃ v, IsIntrinsicIn X H' (oTwoPrimeOf (K ⊓ cen g)) v := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E : Subgroup X := oTwoPrimeOf (K ⊓ cen g) with hEdef
  have hKH : K ≤ H := hK.2.2.1.1
  have hKq : IsTwoGenQuasi ↥K :=
    (isTwoGenQuasi_subgroupOf_iff hKH).1 (isPComponent_two_iff.1 hK.2.2.1.2).2
  have hEK : E ≤ K := (oTwoPrimeOf_le _).trans inf_le_left
  have hu2 : u ^ 2 = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hK.1] at this
  have hu2' : (⟨u, hK.2.1⟩ : ↥K) ^ (2 ^ 1) = 1 := Subtype.ext (by simpa using hu2)
  have hmem : (⟨u, hK.2.1⟩ : ↥K) ∈ E.subgroupOf K ⊔ pPrimeCore 2 ↥K := by
    rw [hcovE]
    exact Subgroup.mem_top _
  obtain ⟨o, -, a, ha, -, hua⟩ := exists_conj_twoElt_of_mem_sup_odd
    (Nat.coprime_two_left.1 pPrimeCore_coprime_card) hmem hu2'
  have hua' : u = (o : X) * (a : X) * (o : X)⁻¹ := by
    simpa using congrArg Subtype.val hua
  obtain ⟨φ, hφ⟩ : ∃ φ : X ≃* X, φ = MulAut.conj (o : X)⁻¹ := ⟨_, rfl⟩
  have hφH : H.map φ.toMonoidHom = H := by
    rw [hφ]
    exact map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer (H.inv_mem (hKH o.2)))
  have hφK : K.map φ.toMonoidHom = K := by
    rw [hφ]
    exact map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer (K.inv_mem o.2))
  have hφu : φ u = (a : X) := by
    rw [hφ, MulAut.conj_apply, hua']
    group
  have hK' := hK.map_mulEquiv φ
  rw [hφH, hφK, hφu] at hK'
  have haE : (a : X) ∈ E := ha
  obtain ⟨hv, hvK, -, hKeq, Lv, hLv, hLveq⟩ := hK'
  rw [oPrimeResidualOf_two_eq_oTwoPrimeOf] at hKeq hLveq
  have hGK : oTwoPrimeOf (K ⊓ cen (a : X)) ≤ K := (oTwoPrimeOf_le _).trans inf_le_left
  have hGv : oTwoPrimeOf (K ⊓ cen (a : X)) ≤ cen (a : X) :=
    (oTwoPrimeOf_le _).trans inf_le_right
  have hcovG : (oTwoPrimeOf (K ⊓ cen (a : X))).subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤ := by
    rw [covers_subgroupOf_iff hGK, sup_comm]
    exact hKeq.symm
  have hGLv : oTwoPrimeOf (K ⊓ cen (a : X)) ≤ Lv := le_sup_right.trans hLveq.ge
  have hcovGL : (oTwoPrimeOf (K ⊓ cen (a : X))).subgroupOf Lv ⊔ pPrimeCore 2 ↥Lv = ⊤ := by
    rw [covers_subgroupOf_iff hGLv, sup_comm]
    exact hLveq.symm
  have hvK' : (a : X) ∈ centralizerSection K (pPrimeCoreOf 2 K) :=
    restr_mem_centralizerSection_of_le_cen (Subgroup.le_normalizer hvK)
      (mem_normalizer_pPrimeCoreOf_of_mem hvK) hGK hGv hcovG
  have hEO : E ⊓ pPrimeCoreOf 2 K ≤ pPrimeCoreOf 2 E := inf_pPrimeCoreOf_le_pPrimeCoreOf hEK
  have hvE : (a : X) ∈ centralizerSection E (pPrimeCoreOf 2 E) := by
    refine ⟨Subgroup.le_normalizer haE, mem_normalizer_pPrimeCoreOf_of_mem haE,
      fun e he => hEO ⟨?_, hvK'.2.2 e (hEK he)⟩⟩
    rw [commutatorElement_def]
    exact E.mul_mem (E.mul_mem (E.mul_mem he haE) (E.inv_mem he)) (E.inv_mem haE)
  have hv2 : (a : X) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (a : X)
    rwa [hv] at this
  have hFE : oTwoPrimeOf (E ⊓ cen (a : X)) ≤ E := (oTwoPrimeOf_le _).trans inf_le_left
  have hcovF : (oTwoPrimeOf (E ⊓ cen (a : X))).subgroupOf E ⊔ pPrimeCore 2 ↥E = ⊤ :=
    oTwoPrimeOf_inf_centralizer_covers hv2 (primeResidual_oTwoPrimeOf _) hvE
  have hFLv : oTwoPrimeOf (E ⊓ cen (a : X)) ≤ Lv :=
    (oTwoPrimeOf_mono (inf_le_inf_right _ hEK)).trans hGLv
  have hc1 := Nat.card_congr (nonempty_quot_mulEquiv_of_covers hFE hcovF).some.toEquiv
  have hc2 := Nat.card_congr (nonempty_quot_mulEquiv_of_covers hEK hcovE).some.toEquiv
  have hc3 := Nat.card_congr (nonempty_quot_mulEquiv_of_covers hGK hcovG).some.toEquiv
  have hc4 := Nat.card_congr (nonempty_quot_mulEquiv_of_covers hGLv hcovGL).some.toEquiv
  have hcovFL : (oTwoPrimeOf (E ⊓ cen (a : X))).subgroupOf Lv ⊔ pPrimeCore 2 ↥Lv = ⊤ :=
    covers_of_card_le hFLv (by omega)
  refine ⟨(a : X), hv, haE, hEpc, ?_, Lv, hLv, ?_⟩
  · rw [oPrimeResidualOf_two_eq_oTwoPrimeOf]
    exact ((covers_subgroupOf_iff hFE).1 hcovF).symm.trans (sup_comm _ _)
  · rw [oPrimeResidualOf_two_eq_oTwoPrimeOf]
    exact ((covers_subgroupOf_iff hFLv).1 hcovFL).symm.trans (sup_comm _ _)

theorem sec5Comp_restrict {n : ℕ} {H L : Subgroup X} {g : X} (hL : Sec5Comp X n H L)
    (hg2 : g ^ 2 = 1) (hgL : g ∈ centralizerSection L (pPrimeCoreOf 2 L)) :
    Sec5Comp X n (H ⊓ cen g) (oTwoPrimeOf (L ⊓ cen g)) := by
  obtain ⟨⟨u, hu⟩, hLn⟩ := hL
  obtain ⟨hpc, hcov⟩ := isPCompIn_restrict hu.2.2.1 hg2 hgL
  have hEL : oTwoPrimeOf (L ⊓ cen g) ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  exact ⟨restr_exists_isIntrinsicIn hu hcov hpc,
    (isDoubleCoverOfAlt_quot_iff_of_covers hEL hcov n).2 hLn⟩

private theorem restr_comm_mem_oddCoreOf {L J : Subgroup X} {s : X} (hs : orderOf s = 2)
    (hJ : IsAhatIntr X s J) (hJL : J ≤ (L ⊓ cen s) ⊔ oddCoreOf (cen s)) {x w : X}
    (hx : x ∈ J) (hw : w ∈ pPrimeCoreOf 2 L ⊓ cen s) : ⁅x, w⁆ ∈ oddCoreOf (cen s) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup X := cen s with hC
  set N : Subgroup X := oddCoreOf C with hN
  set W : Subgroup X := pPrimeCoreOf 2 L ⊓ C with hW
  set Y : Subgroup X := J ⊔ (W ⊔ N) with hY
  have hJC : J ≤ C := hJ.1
  have hYC : Y ≤ C := sup_le hJC (sup_le inf_le_right (oddCoreOf_le C))
  have hJY : J ≤ Y := le_sup_left
  have hVY : W ⊔ N ≤ Y := le_sup_right
  have hLCn : L ⊓ C ≤ normalizer ((W ⊔ N : Subgroup X) : Set X) := fun c hc =>
    mem_normalizer_sup (mem_normalizer_inf (mem_normalizer_pPrimeCoreOf_of_mem hc.1)
      (Subgroup.le_normalizer hc.2)) (le_normalizer_oddCoreOf C hc.2)
  have hYn : Y ≤ normalizer ((W ⊔ N : Subgroup X) : Set X) :=
    sup_le (hJL.trans (sup_le hLCn (le_sup_right.trans Subgroup.le_normalizer)))
      Subgroup.le_normalizer
  have hV : ((W ⊔ N).subgroupOf Y).Normal := (normal_subgroupOf_iff_le_normalizer hVY).2 hYn
  have hJpc : IsPComponent 2 (J.subgroupOf Y) := isPComponent_subgroupOf_mono hJY hYC hJ.2.2.1
  rcases contains_or_normalizes_core 2 (J.subgroupOf Y) ((W ⊔ N).subgroupOf Y) hJpc
      hV.isSubnormal with hle | ⟨-, hcomm⟩
  · exfalso
    have hsWN : s ∈ W ⊔ N := hle (show (⟨s, hJY hJ.2.1⟩ : ↥Y) ∈ J.subgroupOf Y from hJ.2.1)
    have hs2 : s ^ (2 ^ 1) = 1 := by
      rw [pow_one, ← hs]
      exact pow_orderOf_eq_one s
    obtain ⟨o, -, a, ha, ha2, hsa⟩ := exists_conj_twoElt_of_mem_sup_odd_X (A := W) (N := N)
      (fun c hc => le_normalizer_oddCoreOf C (Subgroup.mem_inf.1 hc).2) (odd_card_oddCoreOf C)
      hsWN hs2
    have hWodd : Odd (Nat.card W) :=
      (restr_odd_card L).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    rw [eq_one_of_pow_two_pow_of_mem_odd_subgroup hWodd ha ha2, mul_one, mul_inv_cancel] at hsa
    rw [hsa, orderOf_one] at hs
    exact absurd hs (by norm_num)
  · have hwWN : w ∈ W ⊔ N := Subgroup.mem_sup_left hw
    have hc : ⁅(⟨x, hJY hx⟩ : ↥Y), (⟨w, hVY hwWN⟩ : ↥Y)⁆ ∈
        (pPrimeCore 2 ↥(J.subgroupOf Y)).map (J.subgroupOf Y).subtype :=
      hcomm (Subgroup.commutator_mem_commutator
        (show (⟨x, hJY hx⟩ : ↥Y) ∈ J.subgroupOf Y from hx)
        (show (⟨w, hVY hwWN⟩ : ↥Y) ∈ (W ⊔ N).subgroupOf Y from hwWN))
    obtain ⟨y, hy, hyeq⟩ := hc
    let e : ↥(J.subgroupOf Y) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJY
    have hey : e y ∈ pPrimeCore 2 ↥J := by
      rw [← pPrimeCore_map_iso 2 e]
      exact ⟨y, hy, rfl⟩
    have h1 : ⁅x, w⁆ ∈ pPrimeCoreOf 2 J := by
      refine ⟨e y, hey, ?_⟩
      change ((y : ↥Y) : X) = ⁅x, w⁆
      exact congrArg Subtype.val hyeq
    exact pPrimeCoreOf_le_oddCoreOf hJC (isPComponent_two_iff.1 hJ.2.2.1).1 h1

private theorem restr_le_inf_cen_sup {L D J : Subgroup X} {s : X} (hs : orderOf s = 2)
    (hsD : s ∈ D) (hDL : D ≤ L) (hcov : D.subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤)
    (hJ : IsAhatIntr X s J) (hJL : J ≤ (L ⊓ cen s) ⊔ oddCoreOf (cen s)) :
    J ≤ (D ⊓ cen s) ⊔ oddCoreOf (cen s) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs2 : s ^ 2 = 1 := by
    rw [← hs]
    exact pow_orderOf_eq_one s
  have hLDO : D ⊔ pPrimeCoreOf 2 L = L := (covers_subgroupOf_iff hDL).1 hcov
  have hODL : pPrimeCoreOf 2 D ≤ pPrimeCoreOf 2 L := restr_pPrimeCoreOf_le hDL hcov
  have hWodd : Odd (Nat.card ↥(pPrimeCoreOf 2 L ⊓ cen s)) :=
    (restr_odd_card L).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hNs : cen s ≤ normalizer (oddCoreOf (cen s) : Set X) := le_normalizer_oddCoreOf (cen s)
  have key : ∀ x ∈ J, ∀ k : ℕ, x ^ (2 ^ k) = 1 → x ∈ (D ⊓ cen s) ⊔ oddCoreOf (cen s) := by
    intro x hxJ k hxk
    have hxC : x ∈ cen s := hJ.1 hxJ
    obtain ⟨o, ho, a, ha, hak, hxa⟩ := exists_conj_twoElt_of_mem_sup_odd_X
      (A := L ⊓ cen s) (N := oddCoreOf (cen s)) (fun c hc => hNs (Subgroup.mem_inf.1 hc).2)
      (odd_card_oddCoreOf (cen s)) (hJL hxJ) hxk
    have haDO : a ∈ D ⊔ pPrimeCoreOf 2 L := by
      rw [hLDO]
      exact ha.1
    obtain ⟨o₁, ho₁, b, hb, hbk, hab⟩ := exists_conj_twoElt_of_mem_sup_odd_X
      (A := D) (N := pPrimeCoreOf 2 L) (fun d hd => mem_normalizer_pPrimeCoreOf_of_mem (hDL hd))
      (restr_odd_card L) haDO hak
    have hba : b⁻¹ * a ∈ pPrimeCoreOf 2 L := by
      have e : b⁻¹ * a = (b⁻¹ * o₁ * b) * o₁⁻¹ := by
        rw [hab]
        group
      rw [e]
      exact (pPrimeCoreOf 2 L).mul_mem
        (restr_conj_inv_mem (mem_normalizer_pPrimeCoreOf_of_mem (hDL hb)) ho₁)
        ((pPrimeCoreOf 2 L).inv_mem ho₁)
    have hbs : ⁅b, s⁆ ∈ pPrimeCoreOf 2 D := by
      refine inf_pPrimeCoreOf_le_pPrimeCoreOf hDL ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        exact D.mul_mem (D.mul_mem (D.mul_mem hb hsD) (D.inv_mem hb)) (D.inv_mem hsD)
      · exact restr_comm_mem (mem_normalizer_pPrimeCoreOf_of_mem (hDL hsD))
          (mem_normalizer_pPrimeCoreOf_of_mem ha.1) hba
          (Subgroup.mem_centralizer_singleton_iff.1 ha.2)
    obtain ⟨c, hc, -, hcb⟩ := exists_twoElt_centralizer_of_comm_mem hs2
      (mem_normalizer_pPrimeCoreOf_of_mem hsD) hb hbs hbk
    have hca : c⁻¹ * a ∈ pPrimeCoreOf 2 L ⊓ cen s := by
      refine ⟨?_, (cen s).mul_mem ((cen s).inv_mem hc.2) ha.2⟩
      have e : c⁻¹ * a = (c⁻¹ * b) * (b⁻¹ * a) := by group
      rw [e]
      exact (pPrimeCoreOf 2 L).mul_mem (hODL hcb) hba
    have haDW : a ∈ (D ⊓ cen s) ⊔ (pPrimeCoreOf 2 L ⊓ cen s) := by
      have e : a = c * (c⁻¹ * a) := by group
      rw [e]
      exact Subgroup.mul_mem_sup hc hca
    obtain ⟨w, hw, c', hc', -, hac⟩ := exists_conj_twoElt_of_mem_sup_odd_X
      (A := D ⊓ cen s) (N := pPrimeCoreOf 2 L ⊓ cen s)
      (fun d hd => mem_normalizer_inf
        (mem_normalizer_pPrimeCoreOf_of_mem (hDL (Subgroup.mem_inf.1 hd).1))
        (Subgroup.le_normalizer (Subgroup.mem_inf.1 hd).2)) hWodd haDW hak
    have hc'x : c'⁻¹ * x ∈ oddCoreOf (cen s) := by
      have hxw : ⁅x⁻¹, w⁻¹⁆ ∈ oddCoreOf (cen s) :=
        restr_comm_mem_oddCoreOf hs hJ hJL (J.inv_mem hxJ) ((pPrimeCoreOf 2 L ⊓ cen s).inv_mem hw)
      have h1 : x⁻¹ * o * x ∈ oddCoreOf (cen s) := restr_conj_inv_mem (hNs hxC) ho
      have h2 : w⁻¹ * (o⁻¹ * (x⁻¹ * o * x)) * w ∈ oddCoreOf (cen s) :=
        restr_conj_inv_mem (hNs hw.2) ((oddCoreOf (cen s)).mul_mem
          ((oddCoreOf (cen s)).inv_mem ho) h1)
      have e : c'⁻¹ * x = (w⁻¹ * (o⁻¹ * (x⁻¹ * o * x)) * w) * (⁅x⁻¹, w⁻¹⁆)⁻¹ := by
        have hc'eq : c' = w⁻¹ * (o⁻¹ * x * o) * w := by
          rw [hxa, hac]
          group
        rw [hc'eq, commutatorElement_def]
        group
      rw [e]
      exact (oddCoreOf (cen s)).mul_mem h2 ((oddCoreOf (cen s)).inv_mem hxw)
    have e : x = c' * (c'⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hc' hc'x
  have hJq := isTwoGenQuasi_of_isAhatIntr hJ
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥J) ∈ primeResidual 2 ↥J := by
    rw [hJq.1]
    exact Subgroup.mem_top _
  rw [primeResidual_eq_closure] at hy'
  have hcl : Subgroup.closure {z : ↥J | ∃ k : ℕ, orderOf z = 2 ^ k} ≤
      ((D ⊓ cen s) ⊔ oddCoreOf (cen s)).comap J.subtype := by
    rw [Subgroup.closure_le]
    rintro z ⟨k, hk⟩
    have hzk : (z : X) ^ (2 ^ k) = 1 := by
      have := pow_orderOf_eq_one z
      rw [hk] at this
      exact congrArg Subtype.val this
    exact key z z.2 k hzk
  exact hcl hy'

theorem IsMLIntrIn.of_covers {H H' L D : Subgroup X} (hL : IsMLIntrIn X H L) (hDL : D ≤ L)
    (hcov : D.subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤) (hD : IsPCompIn 2 H' D) :
    IsMLIntrIn X H' D := by
  obtain ⟨-, hty, hJ⟩ := hL
  obtain ⟨e⟩ := nonempty_quot_mulEquiv_of_covers hDL hcov
  refine ⟨hD, hty.imp (Nonempty.map e.trans) (Nonempty.map e.trans), fun s hs hs2 => ?_⟩
  obtain ⟨J, hJs, hJle⟩ := hJ s (hDL hs) hs2
  exact ⟨J, hJs, restr_le_inf_cen_sup hs2 hs hDL hcov hJs hJle⟩

theorem sec6MComp_restrict {n : ℕ} {H L : Subgroup X} {g : X} (hL : Sec6MComp X n H L)
    (hg2 : g ^ 2 = 1) (hgL : g ∈ centralizerSection L (pPrimeCoreOf 2 L)) :
    Sec6MComp X n (H ⊓ cen g) (oTwoPrimeOf (L ⊓ cen g)) := by
  obtain ⟨hpc, hcov⟩ := isPCompIn_restrict hL.1.1 hg2 hgL
  have hDL : oTwoPrimeOf (L ⊓ cen g) ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  obtain ⟨e⟩ := nonempty_quot_mulEquiv_of_covers hDL hcov
  exact ⟨hL.1.of_covers hDL hcov hpc, hL.2.congr e.symm⟩

theorem sec6KComp_restrict {n : ℕ} {H L : Subgroup X} {g : X} (hL : Sec6KComp X n H L)
    (hg2 : g ^ 2 = 1) (hgL : g ∈ centralizerSection L (pPrimeCoreOf 2 L)) :
    Sec6KComp X n (H ⊓ cen g) (oTwoPrimeOf (L ⊓ cen g)) :=
  hL.imp (fun h => sec5Comp_restrict h hg2 hgL) (fun h => sec6MComp_restrict h hg2 hgL)

theorem sSup_eq_sup_iSup_restrict {H : Subgroup X} {g : X} {P : Subgroup X → Prop}
    (hP : ∀ L, P L → IsPCompIn 2 H L) (hg2 : g ^ 2 = 1)
    (hgP : ∀ L, P L → g ∈ centralizerSection L (pPrimeCoreOf 2 L)) :
    sSup {L | P L} = pPrimeCoreOf 2 (sSup {L | P L}) ⊔
      ⨆ (L : Subgroup X) (_ : P L), oTwoPrimeOf (L ⊓ cen g) := by
  have hSH : sSup {L | P L} ≤ H := sSup_le fun L hL => (hP L hL).1
  refine le_antisymm (sSup_le fun L hL => ?_) (sup_le (Subgroup.map_subtype_le _)
    (iSup₂_le fun L hL =>
      ((oTwoPrimeOf_le _).trans inf_le_left).trans (le_sSup (s := {L | P L}) hL)))
  obtain ⟨-, hcov⟩ := isPCompIn_restrict (hP L hL) hg2 (hgP L hL)
  have hEL : oTwoPrimeOf (L ⊓ cen g) ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hOL : pPrimeCoreOf 2 L ≤ pPrimeCoreOf 2 (sSup {L | P L}) :=
    (le_inf ((Subgroup.map_subtype_le _).trans (le_sSup hL))
      (pPrimeCoreOf_le_oddCoreOf (hP L hL).1 (isPComponent_two_iff.1 (hP L hL).2).1)).trans
      (inf_pPrimeCoreOf_le_pPrimeCoreOf hSH)
  exact ((covers_subgroupOf_iff hEL).1 hcov).ge.trans
    (sup_le (le_sup_of_le_right (le_iSup₂_of_le L hL le_rfl)) (le_sup_of_le_left hOL))

theorem modOddCard_iSup_restrict {H : Subgroup X} {g : X} {P : Subgroup X → Prop}
    (hP : ∀ L, P L → IsPCompIn 2 H L) (hg2 : g ^ 2 = 1)
    (hgP : ∀ L, P L → g ∈ centralizerSection L (pPrimeCoreOf 2 L)) :
    modOddCard (⨆ (L : Subgroup X) (_ : P L), oTwoPrimeOf (L ⊓ cen g)) =
      modOddCard (sSup {L | P L}) :=
  modOddCard_eq_of_covers
    (iSup₂_le fun L hL =>
      ((oTwoPrimeOf_le _).trans inf_le_left).trans (le_sSup (s := {L | P L}) hL))
    (sSup_eq_sup_iSup_restrict hP hg2 hgP)

private theorem restr_sec6KComp_isPCompIn {n : ℕ} {H L : Subgroup X} (hL : Sec6KComp X n H L) :
    IsPCompIn 2 H L := by
  rcases hL with ⟨⟨u, hu⟩, -⟩ | ⟨hM, -⟩
  · exact hu.2.2.1
  · exact hM.1

private theorem restr_sq_eq_one {g : X} (hg : orderOf g = 2) : g ^ 2 = 1 := by
  rw [← hg]
  exact pow_orderOf_eq_one g

private theorem restr_le_sec6K {n : ℕ} {H L : Subgroup X} (hL : Sec6KComp X n H L) :
    L ≤ Sec6K X n H :=
  le_sSup (s := {L | Sec6KComp X n H L}) hL

private theorem restr_le_sec6M {n : ℕ} {H M : Subgroup X} (hM : Sec6MComp X n H M) :
    M ≤ Sec6M X n H :=
  le_sSup (s := {M | Sec6MComp X n H M}) hM

private theorem restr_iSup_le_K {n : ℕ} {t g : X} (h51 : Sec6Lemma51 X n) (hg : orderOf g = 2)
    (hgS : ∀ L, Sec6KComp X n (cen t) L → g ∈ centralizerSection L (pPrimeCoreOf 2 L)) :
    (⨆ (L : Subgroup X) (_ : Sec6KComp X n (cen t) L), oTwoPrimeOf (L ⊓ cen g)) ≤
      Sec6K X n (cen g) := by
  refine (iSup₂_le fun L hL => ?_).trans (h51.sub g hg (cen t ⊓ cen g) inf_le_right).1
  exact restr_le_sec6K (sec6KComp_restrict hL (restr_sq_eq_one hg) (hgS L hL))

private theorem restr_iSup_le_Kt {n : ℕ} {t g : X} :
    (⨆ (L : Subgroup X) (_ : Sec6KComp X n (cen t) L), oTwoPrimeOf (L ⊓ cen g)) ≤
      Sec6K X n (cen t) :=
  iSup₂_le fun _ hL => ((oTwoPrimeOf_le _).trans inf_le_left).trans (restr_le_sec6K hL)

private theorem restr_modOddCard_K {n : ℕ} {t g : X} (hg : orderOf g = 2)
    (hgS : ∀ L, Sec6KComp X n (cen t) L → g ∈ centralizerSection L (pPrimeCoreOf 2 L)) :
    modOddCard (⨆ (L : Subgroup X) (_ : Sec6KComp X n (cen t) L), oTwoPrimeOf (L ⊓ cen g)) =
      modOddCard (Sec6K X n (cen t)) :=
  modOddCard_iSup_restrict (fun _ hL => restr_sec6KComp_isPCompIn hL) (restr_sq_eq_one hg) hgS

private theorem restr_modOddCard_M_le {n : ℕ} {t g : X} (h51 : Sec6Lemma51 X n)
    (hg : orderOf g = 2)
    (hgS : ∀ L, Sec6KComp X n (cen t) L → g ∈ centralizerSection L (pPrimeCoreOf 2 L)) :
    modOddCard (Sec6M X n (cen t)) ≤ modOddCard (Sec6M X n (cen g)) := by
  have hg2 := restr_sq_eq_one hg
  have hgM : ∀ L, Sec6MComp X n (cen t) L → g ∈ centralizerSection L (pPrimeCoreOf 2 L) :=
    fun L hL => hgS L (Or.inr hL)
  have hle : (⨆ (L : Subgroup X) (_ : Sec6MComp X n (cen t) L), oTwoPrimeOf (L ⊓ cen g)) ≤
      Sec6M X n (cen g) := by
    refine (iSup₂_le fun L hL => ?_).trans (h51.sub g hg (cen t ⊓ cen g) inf_le_right).2
    exact restr_le_sec6M (sec6MComp_restrict hL hg2 (hgM L hL))
  exact (modOddCard_iSup_restrict (fun _ hL => hL.1.1) hg2 hgM).ge.trans (modOddCard_le_of_le hle)

private theorem restr_exists_sec6MComp {n : ℕ} {t g : X} (h51 : Sec6Lemma51 X n)
    (hg : orderOf g = 2)
    (hgS : ∀ L, Sec6KComp X n (cen t) L → g ∈ centralizerSection L (pPrimeCoreOf 2 L))
    (hex : ∃ M, Sec6MComp X n (cen t) M) : ∃ M, Sec6MComp X n (cen g) M := by
  obtain ⟨M, hM⟩ := hex
  have hD := sec6MComp_restrict hM (restr_sq_eq_one hg) (hgS M (Or.inr hM))
  have hDle : oTwoPrimeOf (M ⊓ cen g) ≤ Sec6M X n (cen g) :=
    (restr_le_sec6M hD).trans (h51.sub g hg (cen t ⊓ cen g) inf_le_right).2
  by_contra hno
  have hbot : Sec6M X n (cen g) = ⊥ :=
    sSup_eq_bot.2 fun M' hM' => absurd hM' fun h => hno ⟨M', h⟩
  have hq : IsTwoGenQuasi ↥(oTwoPrimeOf (M ⊓ cen g)) :=
    (isTwoGenQuasi_subgroupOf_iff hD.1.1.1).1 (isPComponent_two_iff.1 hD.1.1.2).2
  rw [hbot] at hDle
  exact not_le_oddCoreOf_of_isTwoGenQuasi (C := ⊤) hq (hDle.trans bot_le)

private theorem restr_mem_centralizerSection_of_mem_sec6Q {n : ℕ} {t x : X} {L : Subgroup X}
    (hx : x ∈ Sec6Q X n (cen t)) (hL : Sec6KComp X n (cen t) L) :
    x ∈ centralizerSection L (pPrimeCoreOf 2 L) := by
  obtain ⟨hxt, hxQ⟩ := Subgroup.mem_inf.1 hx
  have hcomm : ∀ k ∈ Sec6K X n (cen t), ⁅k, x⁆ ∈ oddCoreOf (Sec6K X n (cen t)) :=
    (mem_QOf_iff.1 hxQ).2
  have hKt : Sec6K X n (cen t) ≤ cen t := sSup_le fun L hL => (restr_sec6KComp_isPCompIn hL).1
  have hOK : oddCoreOf (Sec6K X n (cen t)) ≤ oddCoreOf (cen t) :=
    le_oddCoreOf_of_normalized ((oddCoreOf_le _).trans hKt)
      ((Sec6K_cen_normal n t).trans (normalizer_le_normalizer_pPrimeCoreOf _))
      (odd_card_oddCoreOf _)
  exact normalizes_isPCompIn_of_comm_mem (restr_sec6KComp_isPCompIn hL)
    (Subgroup.le_normalizer hxt) fun l hl => hOK (hcomm l (restr_le_sec6K hL hl))

private theorem restr_mem_centralizerSection_of_isIntrinsicIn {H L A : Subgroup X} {u : X}
    (hA : IsIntrinsicIn X H A u) (hL : IsPCompIn 2 H L) :
    u ∈ centralizerSection L (pPrimeCoreOf 2 L) := by
  obtain ⟨-, huA, hApc, hAeq, -⟩ := hA
  by_cases hLA : L = A
  · rw [hLA]
    rw [oPrimeResidualOf_two_eq_oTwoPrimeOf] at hAeq
    have hGA : oTwoPrimeOf (A ⊓ cen u) ≤ A := (oTwoPrimeOf_le _).trans inf_le_left
    have hcov : (oTwoPrimeOf (A ⊓ cen u)).subgroupOf A ⊔ pPrimeCore 2 ↥A = ⊤ := by
      rw [covers_subgroupOf_iff hGA, sup_comm]
      exact hAeq.symm
    exact restr_mem_centralizerSection_of_le_cen (Subgroup.le_normalizer huA)
      (mem_normalizer_pPrimeCoreOf_of_mem huA) hGA ((oTwoPrimeOf_le _).trans inf_le_right) hcov
  · refine normalizes_isPCompIn_of_comm_mem hL (Subgroup.le_normalizer (hApc.1 huA))
      fun l hl => ?_
    exact pPrimeCoreOf_le_oddCoreOf hL.1 (isPComponent_two_iff.1 hL.2).1
      (restr_commutatorElement_mem hL hApc hLA hl huA)

private theorem restr_mem_K0_cen {n : ℕ} {H A : Subgroup X} {u : X}
    (hu : IsIntrinsicIn X H A u) (hAn : IsDoubleCoverOfAlt (↥A ⧸ pPrimeCore 2 ↥A) n) :
    u ∈ K0 X n (cen u) := by
  obtain ⟨hu2, -, -, hAeq, Lu, hLu, hLueq⟩ := hu
  rw [oPrimeResidualOf_two_eq_oTwoPrimeOf] at hAeq hLueq
  have hEA : oTwoPrimeOf (A ⊓ cen u) ≤ A := (oTwoPrimeOf_le _).trans inf_le_left
  have hELu : oTwoPrimeOf (A ⊓ cen u) ≤ Lu := le_sup_right.trans hLueq.ge
  have hcovA : (oTwoPrimeOf (A ⊓ cen u)).subgroupOf A ⊔ pPrimeCore 2 ↥A = ⊤ := by
    rw [covers_subgroupOf_iff hEA, sup_comm]
    exact hAeq.symm
  have hcovLu : (oTwoPrimeOf (A ⊓ cen u)).subgroupOf Lu ⊔ pPrimeCore 2 ↥Lu = ⊤ := by
    rw [covers_subgroupOf_iff hELu, sup_comm]
    exact hLueq.symm
  have hLun : IsDoubleCoverOfAlt (↥Lu ⧸ pPrimeCore 2 ↥Lu) n :=
    (isDoubleCoverOfAlt_quot_iff_of_covers hELu hcovLu n).1
      ((isDoubleCoverOfAlt_quot_iff_of_covers hEA hcovA n).2 hAn)
  have hmem : Sec5Comp X n (cen u) Lu := ⟨⟨u, hLu.isIntrinsicIn hu2⟩, hLun⟩
  rw [K0_eq_sSup_sec5Comp]
  exact le_sSup (s := {A | Sec5Comp X n (cen u) A}) hmem hLu.2.1

end Restrict

theorem sec6L61_a {X : Type} [Group X] [Finite X] {n : ℕ} {t : X} (hS : Sec6Setting X n t)
    (hK : Sec6Lemma51 X n) : ∀ x ∈ Sec6Q X n (cen t), orderOf x = 2 → Sec6Covers X n t x := by
  intro x hx hx2
  have hgS : ∀ L, Sec6KComp X n (cen t) L → x ∈ centralizerSection L (pPrimeCoreOf 2 L) :=
    fun L hL => restr_mem_centralizerSection_of_mem_sec6Q hx hL
  have hDx := restr_iSup_le_K hK hx2 hgS
  have hDt := restr_iSup_le_Kt (n := n) (t := t) (g := x)
  have hDc := restr_modOddCard_K hx2 hgS
  have hMeq : modOddCard (Sec6M X n (cen x)) = modOddCard (Sec6M X n (cen t)) :=
    le_antisymm (hS.choice.maxM x hx2) (restr_modOddCard_M_le hK hx2 hgS)
  have hKx : modOddCard (Sec6K X n (cen x)) ≤ modOddCard (Sec6K X n (cen t)) :=
    hS.choice.maxK x hx2 (restr_exists_sec6MComp hK hx2 hgS hS.choice.hasM) hMeq
  have hcov := covers_of_card_le hDx (hKx.trans hDc.ge)
  have heq := (covers_subgroupOf_iff hDx).1 hcov
  unfold Sec6Covers
  refine le_antisymm ?_ (sup_le (oddCoreOf_le _) inf_le_left)
  calc Sec6K X n (cen x) = _ := heq.symm
    _ ≤ _ := sup_le (le_sup_of_le_right (le_inf hDx hDt)) le_sup_left

theorem sec6CentralChoiceHolds : Sec6CentralChoiceHolds := by
  intro X _ _ n t _ _ _ _ h51 hch
  by_cases hne : K0 X n (cen t) = ⊥
  · exact ⟨t, hch, fun h => absurd hne h⟩
  obtain ⟨A₁, ⟨u, hu⟩, hA₁n⟩ : ∃ A₁, Sec5Comp X n (cen t) A₁ := by
    by_contra hno
    rw [K0_eq_sSup_sec5Comp] at hne
    exact hne (sSup_eq_bot.2 fun A hA => absurd hA fun h => hno ⟨A, h⟩)
  have hu2 : orderOf u = 2 := hu.1
  have hgS : ∀ L, Sec6KComp X n (cen t) L → u ∈ centralizerSection L (pPrimeCoreOf 2 L) :=
    fun L hL => restr_mem_centralizerSection_of_isIntrinsicIn hu (restr_sec6KComp_isPCompIn hL)
  have hK : modOddCard (Sec6K X n (cen t)) ≤ modOddCard (Sec6K X n (cen u)) :=
    (restr_modOddCard_K hu2 hgS).ge.trans (modOddCard_le_of_le (restr_iSup_le_K h51 hu2 hgS))
  have hM := restr_modOddCard_M_le h51 hu2 hgS
  refine ⟨u, ⟨hu2, restr_exists_sec6MComp h51 hu2 hgS hch.hasM,
    fun s hs => (hch.maxM s hs).trans hM, fun s hs hsM heq => ?_⟩, fun _ => ?_⟩
  · exact (hch.maxK s hs hsM (heq.trans (le_antisymm (hch.maxM u hu2) hM))).trans hK
  · exact restr_mem_K0_cen hu hA₁n

end CFSG.OddStandard.Solomon75
