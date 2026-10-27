module

public import CFSG.GH74.GLS.TwoThin.DPair
public import CFSG.GH74.GLS.TwoThin.Central
public import CFSG.GH74.GLS.TwoThin.SwapH

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_dpair_mu_max
    (hR : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)))
    (hC : B2PumpupClosed G) {x : G} {K : Subgroup G} (hP : IsB2Pair x K)
    (hmax : ∀ (x' : G) (K' : Subgroup G), IsB2Pair x' K' →
      hatCard K' < hatCard K ∨ (hatCard K' = hatCard K ∧ sylVal x' K' ≤ sylVal x K)) :
    ∃ (u : G) (M : Subgroup G), IsB2Pair u M ∧ u ∈ M ∧ hatCard M = hatCard K ∧
      sylVal u M = sylVal x K := by
  have hxo : orderOf x = 2 := hP.1.1
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hP.1.2.2
  have hKB : InB2 (↥K ⧸ pPrimeCore 2 ↥K) := hP.2
  obtain ⟨Q, hQ, u, huQ, huc, hucl, huo⟩ := exists_sylow_central_lift hKc hKB
  have huK : u ∈ K := centralLift_le K hucl
  have hucs : u ∈ centralizerSection K (pPrimeCoreOf 2 K) :=
    centralLift_le_centralizerSection K hucl
  have hux : u ∈ centralizer ({x} : Set G) := hKc.1 huK
  obtain ⟨Λ, hΛX, hΛlay, hΛpc, hΛuniq, hΛW, h2el, hcovΛ⟩ := pumpup_cover huo hKc hucs
  have hxY : x ∈ centralizer ({u} : Set G) := mem_centralizer_symm hux
  set Y' := centralizer ({u} : Set G) with hY'
  have hso : orderOf (⟨x, hxY⟩ : ↥Y') = 2 := orderOf_mk_centralizer hxY hxo
  have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp hΛW).1 hxY
  have hΛ2 := isTwoComponent_centralizer_mk hΛW hxY
  obtain ⟨hΛE, hJsub, L, hL, hcases, hLJ, hLsJ, hiff⟩ := pumpupY_structure hso hΛC hΛ2
  have hΛK : Λ ≤ K := hΛX.trans inf_le_left
  have hΛY : Λ ≤ Y' := hΛX.trans inf_le_right
  obtain ⟨φ, hφs, hφo, hφρ⟩ := exists_phi hΛK hΛY hcovΛ
  have hL2 : TwoComponents.IsTwoComponent L :=
    TwoLayerTransport.ordinary_isTwoComponent_of_corefree oddCore_barQ L
      ((CFSG.isComponent_iff_open L).mp hL)
  obtain ⟨M, hM2, hML⟩ := OddKernelTwoComponents.exists_lift (barMk ↥Y') barMk_surjective
    odd_card_ker_barMk L hL2
  have hMJ : M ≤ pumpupY (Λ.subgroupOf Y') := (hiff M hM2).mpr (Or.inl hML)
  set MG : Subgroup G := M.map Y'.subtype with hMG
  have hMGY : MG ≤ Y' := Subgroup.map_subtype_le M
  have hMGsub : MG.subgroupOf Y' = M :=
    Subgroup.comap_map_eq_self_of_injective Y'.subtype_injective M
  have hMG2 : TwoComponents.IsTwoComponent (MG.subgroupOf Y') := by
    rw [hMGsub]
    exact hM2
  have hJ : pumpUp 2 K u = (pumpupY (Λ.subgroupOf Y')).map Y'.subtype := by
    rw [pumpUp_eq_map_pumpupY, hΛlay]
  have hMGJ : MG ≤ pumpUp 2 K u := by
    rw [hJ]
    exact Subgroup.map_mono hMJ
  have hpumpPC : IsPCompIn 2 (pumpUp 2 K u) MG :=
    ⟨hMGJ, (CatalogueBAlternating.pComponent_two_iff _).mpr
      (TwoComponentTransport.restrict_nested MG (pumpUp 2 K u) Y' hMGJ
        (pumpUp_le_centralizer K u) hMG2)⟩
  have hILo : IsILo 2 u MG :=
    ⟨huo, by simpa [oBound] using hR u huo, isPCompIn_two_iff.mpr ⟨hMGY, hMG2⟩⟩
  have hlt : PumpUpLT 2 x K u MG := ⟨hP.1, hILo, hux, hucs, hpumpPC⟩
  have hMB : InB2 (↥MG ⧸ pPrimeCore 2 ↥MG) := hC x K u MG hKB hlt
  have hPu : IsB2Pair u MG := ⟨hILo, hMB⟩
  have hmu := hmax u MG hPu
  have hMGL : (MG.subgroupOf Y').map (barMk ↥Y') = L := by
    rw [hMGsub]
    exact hML
  obtain ⟨e1⟩ := hat_equiv_subgroupOf hMGY
  have hMGsubn : (MG.subgroupOf Y').IsSubnormal := by
    rw [hMGsub]
    exact Components.mathlib_subnormal_of_chain hM2.1 Subgroup.IsSubnormal.top
  obtain ⟨e2⟩ := hat_equiv_map hMGsubn
  have hcardMG : Nat.card (↥MG ⧸ pPrimeCore 2 ↥MG) = Nat.card ↥L := by
    rw [Nat.card_congr (e1.trans e2).toEquiv]
    exact Nat.card_congr (MulEquiv.subgroupCongr hMGL).toEquiv
  let I : Subgroup (barQ ↥Y') := (Λ.subgroupOf Y').map (barMk ↥Y')
  have hKI : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) ≤ Nat.card ↥I :=
    Nat.card_le_card_of_surjective φ hφs
  have hIL : Nat.card ↥I ≤ Nat.card ↥L := by
    rcases hcases with ⟨-, hAL⟩ | ⟨-, hAB, hAD⟩
    · exact Subgroup.card_le_of_le hAL
    · exact (Subgroup.card_le_of_le hAD).trans
        (Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _))
  unfold hatCard at hmu ⊢
  have hle1 : Nat.card (↥MG ⧸ pPrimeCore 2 ↥MG) ≤ Nat.card (↥K ⧸ pPrimeCore 2 ↥K) :=
    hmu.elim le_of_lt (fun h => h.1.le)
  have hMGK : Nat.card (↥MG ⧸ pPrimeCore 2 ↥MG) = Nat.card (↥K ⧸ pPrimeCore 2 ↥K) := by omega
  have hIK : Nat.card ↥I = Nat.card (↥K ⧸ pPrimeCore 2 ↥K) := by omega
  have hLK : Nat.card ↥L = Nat.card (↥K ⧸ pPrimeCore 2 ↥K) := by omega
  have hsyl : sylVal u MG ≤ sylVal x K := hmu.elim (fun h => by omega) (fun h => h.2)
  have hφb : Function.Bijective φ := hφs.bijective_of_nat_card_le hIK.le
  have hqY : ∀ q ∈ Q, q ∈ Y' := fun q hq => by
    rw [hY', Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact huc q hq
  have hqs : ∀ q ∈ Q, q ∈ centralizerSection K (pPrimeCoreOf 2 K) := fun q hq => (hQ.le hq).2
  have hΛq : ∀ q ∈ Q, ∀ a ∈ Λ, q * a * q⁻¹ ∈ Λ := fun q hq a ha =>
    conj_mem_of_unique_isPCompIn hΛpc hΛuniq
      (mem_normalizer_inf (hqs q hq).1 (Subgroup.le_normalizer (hqY q hq))) ha
  have hstar : ∀ (q : G) (hq : q ∈ Q) (a : G) (ha : a ∈ Λ),
      barMk ↥Y' (⟨q, hqY q hq⟩ * ⟨a, hΛY ha⟩ * ⟨q, hqY q hq⟩⁻¹) = barMk ↥Y' ⟨a, hΛY ha⟩ := by
    intro q hq a ha
    have haq : q * a * q⁻¹ ∈ Λ := hΛq q hq a ha
    have hbΛ : q * a * q⁻¹ * a⁻¹ ∈ Λ := mul_mem haq (inv_mem ha)
    have hbO : q * a * q⁻¹ * a⁻¹ ∈ pPrimeCoreOf 2 K := by
      have := inv_mem ((hqs q hq).2.2 a (hΛK ha))
      simpa [commutatorElement_def, mul_assoc] using this
    have h1 : hatMap hΛK ⟨q * a * q⁻¹ * a⁻¹, hbΛ⟩ = 1 := (hatMap_eq_one_iff hΛK _).mpr hbO
    have h2 := hφρ _ hbΛ
    rw [h1] at h2
    have h3 : (⟨barMk ↥Y' ⟨q * a * q⁻¹ * a⁻¹, hΛY hbΛ⟩,
        ⟨⟨_, hΛY hbΛ⟩, Subgroup.mem_subgroupOf.mpr hbΛ, rfl⟩⟩ : ↥I) = 1 :=
      hφb.1 (h2.trans (map_one φ).symm)
    have h4 : barMk ↥Y' ⟨q * a * q⁻¹ * a⁻¹, hΛY hbΛ⟩ = 1 := congrArg Subtype.val h3
    have h5 : (⟨q * a * q⁻¹ * a⁻¹, hΛY hbΛ⟩ : ↥Y') =
        ⟨q, hqY q hq⟩ * ⟨a, hΛY ha⟩ * ⟨q, hqY q hq⟩⁻¹ * ⟨a, hΛY ha⟩⁻¹ := rfl
    rw [h5, map_mul, mul_eq_one_iff_eq_inv, ← map_inv] at h4
    rw [h4]
    simp
  rcases hcases with ⟨hLs, hAL⟩ | ⟨hLs, hAB, hAD⟩
  ·
    have hIeq : I = L := Subgroup.eq_of_le_of_card_ge hAL (by omega)
    have hQle : Q ≤ CxK u MG := by
      intro q hq
      have hπ : ∀ m ∈ MG.subgroupOf Y',
          barMk ↥Y' (⟨q, hqY q hq⟩ * m * ⟨q, hqY q hq⟩⁻¹) = barMk ↥Y' m := by
        intro m hm
        have hmL : barMk ↥Y' m ∈ I := by
          rw [hIeq, ← hMGL]
          exact ⟨m, hm, rfl⟩
        obtain ⟨a', ha', hmm⟩ := hmL
        have ha'Λ : (a' : G) ∈ Λ := Subgroup.mem_subgroupOf.mp ha'
        have h1 := hstar q hq a' ha'Λ
        have e1 : barMk ↥Y' (⟨q, hqY q hq⟩ * m * ⟨q, hqY q hq⟩⁻¹) =
            barMk ↥Y' ⟨q, hqY q hq⟩ * barMk ↥Y' m * (barMk ↥Y' ⟨q, hqY q hq⟩)⁻¹ := by
          simp [map_mul]
        have e2 : barMk ↥Y' (⟨q, hqY q hq⟩ * a' * ⟨q, hqY q hq⟩⁻¹) =
            barMk ↥Y' ⟨q, hqY q hq⟩ * barMk ↥Y' a' * (barMk ↥Y' ⟨q, hqY q hq⟩)⁻¹ := by
          simp [map_mul]
        rw [e1, ← hmm, ← e2]
        exact h1
      have hcs := mem_centralizerSection_of_map_eq hMGY hMG2 (hqY q hq) hπ
      show q ∈ centralizer ({u} : Set G) ⊓ centralizerSection MG (pPrimeCoreOf 2 MG)
      exact Subgroup.mem_inf.mpr ⟨hqY q hq, hcs⟩
    have hcardQ : Nat.card Q = 2 ^ sylVal x K := hQ.card_eq
    have hdvd : Nat.card Q ∣ Nat.card ↥(CxK u MG) := Subgroup.card_dvd_of_le hQle
    rw [hcardQ] at hdvd
    have hle : sylVal x K ≤ sylVal u MG :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
    have huY : u ∈ Y' := by
      rw [hY', Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
    have hu2 : u ^ (2 ^ 1) = 1 := by
      have := pow_orderOf_eq_one u
      rwa [huo, ← pow_one 2] at this
    have huΛ : u ∈ Λ := h2el u (Subgroup.mem_inf.mpr ⟨huK, huY⟩) ⟨1, hu2⟩
    have huM : (⟨u, huY⟩ : ↥Y') ∈ M := by
      refine le_of_isPGroup_of_map_le (barMk ↥Y') barMk_surjective odd_card_ker_barMk
        (Subgroup.zpowers ⟨u, huY⟩) M ?_ hM2.1 ?_ (Subgroup.mem_zpowers _)
      · exact isPGroup_zpowers_of_pow_eq_one (n := 1) (Subtype.ext (by simpa using hu2))
      · rw [hML, Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le]
        have : barMk ↥Y' ⟨u, huY⟩ ∈ I := ⟨⟨u, huY⟩, Subgroup.mem_subgroupOf.mpr huΛ, rfl⟩
        rw [hIeq] at this
        exact this
    exact ⟨u, MG, hPu, ⟨⟨u, huY⟩, huM, rfl⟩, hMGK, le_antisymm hsyl hle⟩
  ·
    exfalso
    have hsb2 : orderOf (barMk ↥Y' ⟨x, hxY⟩) = 2 := orderOf_barMk hso
    have hsbinv : (barMk ↥Y' ⟨x, hxY⟩)⁻¹ = barMk ↥Y' ⟨x, hxY⟩ :=
      inv_eq_self_of_orderOf_eq_two hsb2
    have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hL.1.1
    have hL'comp : CFSG.IsComponent (conjSub (barMk ↥Y' ⟨x, hxY⟩)⁻¹ L) :=
      isComponent_conjSub hL _
    have hrange : Nat.card ↥(swapDiag hAB).range ≤ Nat.card ↥L :=
      Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
    have hIeq : I = (swapDiag hAB).range :=
      Subgroup.eq_of_le_of_card_ge hAD (hrange.trans (hLK.trans hIK.symm).le)
    have hqx : ∀ q ∈ Q, x * q = q * x := fun q hq =>
      (Subgroup.mem_centralizer_iff.mp ((hQ.le hq).1)) x (Set.mem_singleton x)
    have hwt : ∀ (q : G) (hq : q ∈ Q), barMk ↥Y' ⟨q, hqY q hq⟩ * barMk ↥Y' ⟨x, hxY⟩ =
        barMk ↥Y' ⟨x, hxY⟩ * barMk ↥Y' ⟨q, hqY q hq⟩ := by
      intro q hq
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hqx q hq).symm
    have hwI : ∀ (q : G) (hq : q ∈ Q) (l : ↥L), barMk ↥Y' ⟨q, hqY q hq⟩ * swapDiag hAB l =
        swapDiag hAB l * barMk ↥Y' ⟨q, hqY q hq⟩ := by
      intro q hq l
      have hmem : swapDiag hAB l ∈ I := by
        rw [hIeq]
        exact ⟨l, rfl⟩
      obtain ⟨a', ha', hδ⟩ := hmem
      have ha'Λ : (a' : G) ∈ Λ := Subgroup.mem_subgroupOf.mp ha'
      have h1 := hstar q hq a' ha'Λ
      rw [← hδ]
      have e : barMk ↥Y' (⟨q, hqY q hq⟩ * a' * ⟨q, hqY q hq⟩⁻¹) =
          barMk ↥Y' ⟨q, hqY q hq⟩ * barMk ↥Y' a' * (barMk ↥Y' ⟨q, hqY q hq⟩)⁻¹ := by
        simp [map_mul]
      have h2 : barMk ↥Y' ⟨q, hqY q hq⟩ * barMk ↥Y' a' * (barMk ↥Y' ⟨q, hqY q hq⟩)⁻¹ =
          barMk ↥Y' a' := by
        rw [← e]
        exact h1
      exact mul_inv_eq_iff_eq_mul.mp h2
    have hcommP : ∀ (a b : barQ ↥Y'),
        (MulAut.conj (a⁻¹ * b)).toMonoidHom =
          (MulAut.conj a⁻¹).toMonoidHom.comp (MulAut.conj b).toMonoidHom := by
      intro a b
      ext z
      simp [MulAut.conj_apply, mul_assoc]
    have hθ : ∀ (q : G) (hq : q ∈ Q),
        L.map (MulAut.conj (barMk ↥Y' ⟨q, hqY q hq⟩)).toMonoidHom = L ∨
        L.map (MulAut.conj (barMk ↥Y' ⟨q, hqY q hq⟩)).toMonoidHom =
          conjSub (barMk ↥Y' ⟨x, hxY⟩)⁻¹ L := by
      intro q hq
      let qY : ↥Y' := ⟨q, hqY q hq⟩
      have h2 : TwoComponents.IsTwoComponent (M.map (MulAut.conj qY).toMonoidHom) :=
        (TwoComponentTransport.equiv_iff (MulAut.conj qY) M).mpr hM2
      have hΛq' : ∀ a ∈ Λ.subgroupOf Y', qY * a * qY⁻¹ ∈ Λ.subgroupOf Y' := fun a ha =>
        Subgroup.mem_subgroupOf.mpr (hΛq q hq a (Subgroup.mem_subgroupOf.mp ha))
      have hle : M.map (MulAut.conj qY).toMonoidHom ≤ pumpupY (Λ.subgroupOf Y') :=
        (Subgroup.map_mono hMJ).trans (map_conj_pumpupY_le_of_map_le _ hΛq')
      have himg := (hiff _ h2).mp hle
      have hcomp : (barMk ↥Y').comp (MulAut.conj qY).toMonoidHom =
          (MulAut.conj (barMk ↥Y' qY)).toMonoidHom.comp (barMk ↥Y') := by
        ext a
        simp [qY]
      have hM' : (M.map (MulAut.conj qY).toMonoidHom).map (barMk ↥Y') =
          L.map (MulAut.conj (barMk ↥Y' qY)).toMonoidHom := by
        rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hML]
      rw [hM'] at himg
      exact himg
    have hA : ∀ (q : G) (hq : q ∈ Q),
        L.map (MulAut.conj (barMk ↥Y' ⟨q, hqY q hq⟩)).toMonoidHom = L → q ∈ CxK u MG := by
      intro q hq hθq
      have hwL : ∀ l ∈ L, barMk ↥Y' ⟨q, hqY q hq⟩ * l * (barMk ↥Y' ⟨q, hqY q hq⟩)⁻¹ ∈ L := by
        intro l hl
        have := Subgroup.mem_map_of_mem (MulAut.conj (barMk ↥Y' ⟨q, hqY q hq⟩)).toMonoidHom hl
        rw [hθq] at this
        exact this
      have hcentL := centralizes_of_swap hAB hLperf (hwt q hq) hwL (hwI q hq)
      have hπ : ∀ m ∈ MG.subgroupOf Y',
          barMk ↥Y' (⟨q, hqY q hq⟩ * m * ⟨q, hqY q hq⟩⁻¹) = barMk ↥Y' m := by
        intro m hm
        have hmL : barMk ↥Y' m ∈ L := by
          rw [← hMGL]
          exact ⟨m, hm, rfl⟩
        have := hcentL _ hmL
        rw [map_mul, map_mul, map_inv]
        exact this
      have hcs := mem_centralizerSection_of_map_eq hMGY hMG2 (hqY q hq) hπ
      show q ∈ centralizer ({u} : Set G) ⊓ centralizerSection MG (pPrimeCoreOf 2 MG)
      exact Subgroup.mem_inf.mpr ⟨hqY q hq, hcs⟩
    have hQ0 : Nat.card ↥Q ≤ 2 * Nat.card ↥(CxK u MG ⊓ Q) := by
      have h := card_le_two_mul_of_forall ((CxK u MG).subgroupOf Q) (by
        intro p₁ p₂ hp₁ hp₂
        have hp₁' : (p₁ : G) ∉ CxK u MG := fun h => hp₁ (Subgroup.mem_subgroupOf.mpr h)
        have hp₂' : (p₂ : G) ∉ CxK u MG := fun h => hp₂ (Subgroup.mem_subgroupOf.mpr h)
        have h1 : L.map (MulAut.conj (barMk ↥Y' ⟨p₁, hqY p₁ p₁.2⟩)).toMonoidHom =
            conjSub (barMk ↥Y' ⟨x, hxY⟩)⁻¹ L :=
          (hθ p₁ p₁.2).resolve_left fun h => hp₁' (hA p₁ p₁.2 h)
        have h2 : L.map (MulAut.conj (barMk ↥Y' ⟨p₂, hqY p₂ p₂.2⟩)).toMonoidHom =
            conjSub (barMk ↥Y' ⟨x, hxY⟩)⁻¹ L :=
          (hθ p₂ p₂.2).resolve_left fun h => hp₂' (hA p₂ p₂.2 h)
        refine Subgroup.mem_subgroupOf.mpr (hA (p₁⁻¹ * p₂ : ↥Q) (p₁⁻¹ * p₂).2 ?_)
        have e : barMk ↥Y' ⟨((p₁⁻¹ * p₂ : ↥Q) : G), hqY _ (p₁⁻¹ * p₂).2⟩ =
            (barMk ↥Y' ⟨p₁, hqY p₁ p₁.2⟩)⁻¹ * barMk ↥Y' ⟨p₂, hqY p₂ p₂.2⟩ := by
          rw [← map_inv, ← map_mul]
          rfl
        rw [e, hcommP, ← Subgroup.map_map, h2, ← h1, Subgroup.map_map]
        have hid : (MulAut.conj (barMk ↥Y' ⟨p₁, hqY p₁ p₁.2⟩)⁻¹).toMonoidHom.comp
            (MulAut.conj (barMk ↥Y' ⟨p₁, hqY p₁ p₁.2⟩)).toMonoidHom = MonoidHom.id _ := by
          ext z
          simp
        rw [hid, Subgroup.map_id])
      have hcard : Nat.card ↥((CxK u MG).subgroupOf Q) = Nat.card ↥(CxK u MG ⊓ Q) := by
        rw [← Subgroup.inf_subgroupOf_right (CxK u MG) Q]
        exact card_subgroupOf_eq inf_le_right
      rw [hcard] at h
      exact h
    let sY : ↥Y' := ⟨x, hxY⟩
    let NY : Subgroup ↥Y' := M.map (MulAut.conj sY).toMonoidHom
    let NG : Subgroup G := NY.map Y'.subtype
    have hNπ : NY.map (barMk ↥Y') = conjSub (barMk ↥Y' sY)⁻¹ L := by
      have hcomp : (barMk ↥Y').comp (MulAut.conj sY).toMonoidHom =
          (MulAut.conj (barMk ↥Y' sY)).toMonoidHom.comp (barMk ↥Y') := by
        ext a
        simp [sY]
      show (M.map (MulAut.conj sY).toMonoidHom).map (barMk ↥Y') = _
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hML, hsbinv]
    have hNG : ∀ g : G, g ∈ NG ↔ ∃ m ∈ MG, g = x * m * x⁻¹ := by
      intro g
      constructor
      · rintro ⟨n, ⟨m', hm', rfl⟩, rfl⟩
        exact ⟨(m' : G), ⟨m', hm', rfl⟩, rfl⟩
      · rintro ⟨m, ⟨m', hm', rfl⟩, rfl⟩
        exact ⟨sY * m' * sY⁻¹, ⟨m', hm', rfl⟩, rfl⟩
    have hNGY : NG ≤ Y' := Subgroup.map_subtype_le NY
    have hNGCum : NG ≤ CxK u MG := by
      rintro _ ⟨c', hc', rfl⟩
      have hπ : ∀ m ∈ MG.subgroupOf Y', barMk ↥Y' (c' * m * c'⁻¹) = barMk ↥Y' m := by
        intro m hm
        have hmL : barMk ↥Y' m ∈ L := by
          rw [← hMGL]
          exact ⟨m, hm, rfl⟩
        have hcL' : barMk ↥Y' c' ∈ conjSub (barMk ↥Y' sY)⁻¹ L := by
          rw [← hNπ]
          exact ⟨c', hc', rfl⟩
        have hcomm : barMk ↥Y' m * barMk ↥Y' c' = barMk ↥Y' c' * barMk ↥Y' m :=
          commute_of_commutator_conj_eq_bot hAB hmL hcL'
        rw [map_mul, map_mul, map_inv]
        exact mul_inv_eq_iff_eq_mul.mpr hcomm.symm
      have hcs := mem_centralizerSection_of_map_eq hMGY hMG2 c'.2 hπ
      show (c' : G) ∈ centralizer ({u} : Set G) ⊓ centralizerSection MG (pPrimeCoreOf 2 MG)
      exact Subgroup.mem_inf.mpr ⟨c'.2, hcs⟩
    have hnormNG : CxK u MG ⊓ Q ≤ normalizer (NG : Set G) := by
      have hconj : ∀ q ∈ CxK u MG ⊓ Q, ∀ g ∈ NG, q * g * q⁻¹ ∈ NG := by
        intro q hq g hg
        obtain ⟨m, hm, rfl⟩ := (hNG g).mp hg
        have hqN : q ∈ normalizer (MG : Set G) := (Subgroup.mem_inf.mp hq).1.2.1
        have hm' : q * m * q⁻¹ ∈ MG := (Subgroup.mem_normalizer_iff.mp hqN m).mp hm
        refine (hNG _).mpr ⟨q * m * q⁻¹, hm', ?_⟩
        have hq1 : x * q = q * x := hqx q (Subgroup.mem_inf.mp hq).2
        have hq2 : q * x * q⁻¹ = x := by
          rw [← hq1]
          group
        have hq3 : q * x⁻¹ * q⁻¹ = x⁻¹ := by
          rw [show q * x⁻¹ * q⁻¹ = (q * x * q⁻¹)⁻¹ by group, hq2]
        calc q * (x * m * x⁻¹) * q⁻¹
            = (q * x * q⁻¹) * (q * m * q⁻¹) * (q * x⁻¹ * q⁻¹) := by group
          _ = x * (q * m * q⁻¹) * x⁻¹ := by rw [hq2, hq3]
      intro q hq
      rw [Subgroup.mem_normalizer_iff]
      intro g
      exact ⟨fun hg => hconj q hq g hg, fun hg => by
        have := hconj q⁻¹ (inv_mem hq) _ hg
        simpa [mul_assoc] using this⟩
    have hL'q : CFSG.IsQuasisimple ↥(conjSub (barMk ↥Y' sY)⁻¹ L) := hL'comp.1
    have hZ : IsPGroup 2 ↥(center ↥(conjSub (barMk ↥Y' sY)⁻¹ L)) :=
      isPGroup_two_center_of_subnormal (pPrimeCore_quotient_eq_bot ↥Y') hL'comp.2
    obtain ⟨b, hb, hdvdL'⟩ := exists_pow_dvd_card_of_isQuasisimple hL'q hZ
    have hdvdNG : 2 ^ (b + 2) ∣ Nat.card ↥NG := by
      have h1 : Nat.card ↥(conjSub (barMk ↥Y' sY)⁻¹ L) ∣ Nat.card ↥NY := by
        rw [← hNπ]
        exact Subgroup.card_map_dvd NY (barMk ↥Y')
      have h2 : Nat.card ↥NG = Nat.card ↥NY := Subgroup.card_map_of_injective Y'.subtype_injective
      rw [h2]
      exact hdvdL'.trans h1
    have hzY : ∀ z : ↥(NG ⊓ (CxK u MG ⊓ Q)), (z : G) ∈ Y' := fun z =>
      hNGY (Subgroup.mem_inf.mp z.2).1
    have hzQ : ∀ z : ↥(NG ⊓ (CxK u MG ⊓ Q)), (z : G) ∈ Q := fun z =>
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp z.2).2).2
    have hzL' : ∀ z : ↥(NG ⊓ (CxK u MG ⊓ Q)),
        barMk ↥Y' ⟨z, hzY z⟩ ∈ conjSub (barMk ↥Y' sY)⁻¹ L := by
      intro z
      obtain ⟨n', hn', hn'z⟩ := (Subgroup.mem_inf.mp z.2).1
      have : (⟨z, hzY z⟩ : ↥Y') = n' := Subtype.ext hn'z.symm
      rw [this, ← hNπ]
      exact ⟨n', hn', rfl⟩
    have hzc : ∀ z : ↥(NG ⊓ (CxK u MG ⊓ Q)), ∀ m ∈ conjSub (barMk ↥Y' sY)⁻¹ L,
        barMk ↥Y' ⟨z, hzY z⟩ * m = m * barMk ↥Y' ⟨z, hzY z⟩ := by
      intro z
      have hwI' : ∀ l : ↥L, barMk ↥Y' ⟨z, hzY z⟩ * swapDiag hAB l =
          swapDiag hAB l * barMk ↥Y' ⟨z, hzY z⟩ := hwI z (hzQ z)
      exact commute_of_mem_conjSub_of_centralizes_swap hAB (hzL' z) hwI'
    let f : ↥(NG ⊓ (CxK u MG ⊓ Q)) → ↥(center ↥(conjSub (barMk ↥Y' sY)⁻¹ L)) := fun z =>
      ⟨⟨barMk ↥Y' ⟨z, hzY z⟩, hzL' z⟩,
        Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hzc z g.1 g.2).symm⟩
    have hf : Function.Injective f := by
      intro z₁ z₂ h
      have hπeq : barMk ↥Y' ⟨z₁, hzY z₁⟩ = barMk ↥Y' ⟨z₂, hzY z₂⟩ :=
        congrArg (fun t => (t.1 : barQ ↥Y')) h
      have hgQ : (z₁ : G)⁻¹ * z₂ ∈ Q := mul_mem (inv_mem (hzQ z₁)) (hzQ z₂)
      have hgY : (z₁ : G)⁻¹ * z₂ ∈ Y' := mul_mem (inv_mem (hzY z₁)) (hzY z₂)
      have hgker : (⟨(z₁ : G)⁻¹ * z₂, hgY⟩ : ↥Y') ∈ pPrimeCore 2 ↥Y' := by
        rw [← QuotientGroup.eq_one_iff]
        have : (⟨(z₁ : G)⁻¹ * z₂, hgY⟩ : ↥Y') = ⟨z₁, hzY z₁⟩⁻¹ * ⟨z₂, hzY z₂⟩ := rfl
        change barMk ↥Y' (⟨(z₁ : G)⁻¹ * z₂, hgY⟩ : ↥Y') = 1
        rw [this, map_mul, map_inv, hπeq, inv_mul_cancel]
      have hodd : Odd (orderOf (⟨(z₁ : G)⁻¹ * z₂, hgY⟩ : ↥Y')) :=
        (odd_card_pPrimeCore ↥Y').of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hgker)
      obtain ⟨n, hn⟩ := hQ.isPGroup ⟨(z₁ : G)⁻¹ * z₂, hgQ⟩
      have hn' : ((z₁ : G)⁻¹ * z₂) ^ (2 ^ n) = 1 := by
        have := congrArg Subtype.val hn
        simpa using this
      have h1 : (⟨(z₁ : G)⁻¹ * z₂, hgY⟩ : ↥Y') = 1 :=
        eq_one_of_pow_two_pow_eq_one_of_odd (n := n) (Subtype.ext (by simpa using hn')) hodd
      have h2 : (z₁ : G)⁻¹ * z₂ = 1 := congrArg Subtype.val h1
      exact Subtype.ext (inv_mul_eq_one.mp h2)
    have hinter : Nat.card ↥(NG ⊓ (CxK u MG ⊓ Q)) ≤ 2 ^ b := by
      have := Nat.card_le_card_of_injective f hf
      rw [hb] at this
      exact this
    have hQp : IsPGroup 2 ↥Q := hQ.isPGroup
    have hfinal := factorization_lt_of_sup (A := NG) (B := CxK u MG ⊓ Q) (C := CxK u MG) (Q := Q)
      hnormNG (sup_le hNGCum inf_le_left) (hQp.to_le inf_le_right) hQp hQ0 hdvdNG hinter
    have hcardQ : Nat.card ↥Q = 2 ^ sylVal x K := hQ.card_eq
    rw [hcardQ, Nat.Prime.factorization_pow Nat.prime_two] at hfinal
    simp only [Finsupp.single_eq_same] at hfinal
    unfold sylVal at hsyl
    exact absurd hsyl (not_le.mpr hfinal)

end CFSG.GH74.GLS.TwoThin
