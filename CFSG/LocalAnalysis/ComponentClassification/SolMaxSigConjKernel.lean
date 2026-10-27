module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigSylow
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36U

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem le_oddCore_of_le_coreActionKernel {M L : Subgroup X} (hLM : L ≤ M)
    (hLK : L ≤ UnbalancedLayer.coreActionKernel M) (hperf : ⁅L, L⁆ = L) :
    L ≤ (pPrimeCore 2 ↥M).map M.subtype := by
  rw [← hperf, commutator_le]
  intro l₁ h₁ l₂ h₂
  have h := (UnbalancedLayer.mem_coreActionKernel.mp (hLK (inv_mem h₂))).2 l₁⁻¹
    (inv_mem (hLM h₁))
  rw [inv_inv, inv_inv] at h
  rw [commutatorElement_def]
  exact h

theorem false_of_le_oddCore [Finite X] {M L : Subgroup X} {m : ℕ} (hm : 4 ≤ m)
    (θL : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin m))
    (hLO : L ≤ (pPrimeCore 2 ↥M).map M.subtype) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := card_eq_of_alt (by omega) θL
  have h2 : 2 ∣ m.factorial / 2 := by
    obtain ⟨k, hk⟩ : 4 ∣ m.factorial := Nat.dvd_factorial (by norm_num) hm
    exact ⟨k, by rw [hk]; omega⟩
  have h3 : 2 ∣ Nat.card L := by
    rw [h1]
    exact Dvd.dvd.mul_right h2 _
  have h4 : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 ↥M).map M.subtype)) := by
    rw [card_map_of_injective M.subtype_injective]
    exact pPrimeCore_coprime_card
  have h5 := Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hLO) h4
  have h6 := Nat.Coprime.eq_one_of_dvd h5 h3
  omega

theorem isPComponent_subgroupOf_map_conj [Finite X] {Y L : Subgroup X} (hLY : L ≤ Y)
    (hL : IsPComponent 2 (L.subgroupOf Y)) (g : X) :
    IsPComponent 2 ((L.map (MulAut.conj g).toMonoidHom).subgroupOf
      (Y.map (MulAut.conj g).toMonoidHom)) := by
  let f : ↥Y ≃* ↥(Y.map (MulAut.conj g).toMonoidHom) := (MulAut.conj g).subgroupMap Y
  have h1 := ((LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2 Nat.prime_two
    f).1 (L.subgroupOf Y)).mp hL
  have h2 : (L.subgroupOf Y).map f.toMonoidHom =
      (L.map (MulAut.conj g).toMonoidHom).subgroupOf (Y.map (MulAut.conj g).toMonoidHom) := by
    apply Subgroup.map_injective (Y.map (MulAut.conj g).toMonoidHom).subtype_injective
    rw [map_subgroupOf_eq_of_le (map_mono hLY), Subgroup.map_map]
    have h3 : (Y.map (MulAut.conj g).toMonoidHom).subtype.comp f.toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp Y.subtype := by
      ext y
      rfl
    rw [h3, ← Subgroup.map_map, map_subgroupOf_eq_of_le hLY]
  rwa [h2] at h1

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}

theorem false_of_conj_le_coreActionKernel_of_sup (S : Sig36 X t J n e E D)
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {a b : X}
    (haM : a ∈ M) (hbM : b ∈ M) (ha2 : orderOf a = 2) (hb2 : b * b = 1) (hab : a * b = b * a)
    (hCT : centralizer ((zpowers a ⊔ zpowers b : Subgroup X) : Set X) ≤
      normalizer (Sol78.signalizerCompletion E E : Set X))
    {x : X} (hxT : x ∈ zpowers a ⊔ zpowers b) (hxN : x ∈ normalizer (M : Set X))
    (hx2 : x * x = 1) (hx4 : (ρ ⟨x, hxN⟩).support.card = 4) {g : X}
    (hgH : (zpowers a ⊔ zpowers b).map (MulAut.conj g).toMonoidHom ≤
      normalizer (Sol78.signalizerCompletion E E : Set X))
    (hgK : (zpowers a ⊔ zpowers b).map (MulAut.conj g).toMonoidHom ≤
      UnbalancedLayer.coreActionKernel M) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn9 := S.nine_le
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  set T : Subgroup X := zpowers a ⊔ zpowers b with hTdef
  have ha2' : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha2, pow_one])
  have hT2 : IsPGroup 2 T :=
    IsPGroup.to_sup_of_normal_right' ha2' (isPGroup_zpowers_of_mul_self hb2)
      (zpowers_le.mpr (mem_normalizer_zpowers_of_commute hab.symm))
  have hTM : T ≤ M := sup_le (zpowers_le.mpr haM) (zpowers_le.mpr hbM)
  have hTH : T ≤ H := hTM.trans hMH
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha2
    omega
  have hT1 : T ≠ ⊥ := fun h => ha1 (by
    have h1 : a ∈ T := mem_sup_left (mem_zpowers a)
    rwa [h, mem_bot] at h1)
  set T' := T.map (MulAut.conj g).toMonoidHom with hT'def
  have hT'2 : IsPGroup 2 T' := hT2.map _
  have hT'1 : T' ≠ ⊥ := by
    rw [hT'def, Ne, map_eq_bot_iff_of_injective _ (MulAut.conj g).injective]
    exact hT1
  have hCT' : centralizer (T' : Set X) ≤ H :=
    S.centralizer_le_of_le_coreActionKernel h33 h35 hT13 hML hSch hMH hMpc hHN θ hsup hgH hgK
      hT'2 hT'1
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M H hMH).mp hMpc).2.2
  have hMsub : (M.subgroupOf H).IsSubnormal := hMpc.choose_spec.2.1
  set L' := GSLit.fixedLayer M T' with hL'def
  have hL'pc : IsPComponent 2 (L'.subgroupOf (centralizer (T' : Set X))) := by
    have h1 := GSLit.fixedLayer_isPComponent hMH hMsub hgH hgK hT'2 hMq
    rwa [inf_eq_right.mpr hCT'] at h1
  have hL'C : L' ≤ centralizer (T' : Set X) :=
    (GSLit.fixedLayer_le_inf M T').trans inf_le_right
  have hL'M : L' ≤ M := (GSLit.fixedLayer_le_inf M T').trans inf_le_left
  obtain ⟨hL'sup, -⟩ := GSLit.fixedLayer_sup_pPrimeCore hMq hgK hT'2
  obtain ⟨θ', -⟩ := exists_coreQuot_of_sup hL'M hL'sup θ
  have hTT' : T'.map (MulAut.conj g⁻¹).toMonoidHom = T := by
    rw [hT'def, Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id T]
    congr 1
    ext y
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, MonoidHom.id_apply]
    group
  set L := L'.map (MulAut.conj g⁻¹).toMonoidHom with hLdef
  have hCmap : (centralizer (T' : Set X)).map (MulAut.conj g⁻¹).toMonoidHom =
      centralizer (T : Set X) := by
    rw [GSLit.map_centralizer_subgroup, hTT']
  have hLC : L ≤ centralizer (T : Set X) := by
    rw [← hCmap]
    exact map_mono hL'C
  have hLpc : IsPComponent 2 (L.subgroupOf (centralizer (T : Set X))) := by
    have h1 := isPComponent_subgroupOf_map_conj hL'C hL'pc g⁻¹
    rwa [hCmap] at h1
  have hLH : L ≤ H := hLC.trans hCT
  let θL : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin n) :=
    (Sol78.coreQuotCongr (L'.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective)).symm.trans θ'
  have hLperf : ⁅L, L⁆ = L := UnbalancedCorr.commutator_eq_of_isPComponent hLC hLpc
  have hLx : L ≤ centralizer ({x} : Set X) :=
    hLC.trans (centralizer_le (Set.singleton_subset_iff.mpr hxT))
  have hLK : L ≤ UnbalancedLayer.coreActionKernel M :=
    le_coreActionKernel_of_le_centralizer hρ hn9 hxN hx2 hx4 (hLH.trans hHN) hLx θL hLperf
  have hCTab : centralizer (T : Set X) =
      centralizer ({a} : Set X) ⊓ centralizer ({b} : Set X) := by
    rw [hTdef, UnbalancedCorr.centralizer_sup_zpowers, UnbalancedLayer.centralizer_zpowers_eq]
  have hCabH : centralizer ({a} : Set X) ⊓ centralizer ({b} : Set X) ≤ H := hCTab ▸ hCT
  have haH : a ∈ H := hMH haM
  have hbH : b ∈ H := hMH hbM
  set Y₁ := H ⊓ centralizer ({a} : Set X) with hY₁def
  have hCTY : centralizer (T : Set X) = Y₁ ⊓ centralizer ({b} : Set X) := by
    rw [hCTab, hY₁def, inf_assoc]
    exact (inf_eq_right.mpr hCabH).symm
  obtain ⟨K₁, hK₁Y, hK₁pc, hLK₁⟩ : ∃ K₁ : Subgroup X, K₁ ≤ Y₁ ∧
      IsPComponent 2 (K₁.subgroupOf Y₁) ∧ L ≤ K₁ ⊔ K₁.map (MulAut.conj b).toMonoidHom := by
    by_cases hb1 : b = 1
    · have hC1 : centralizer ({b} : Set X) = ⊤ := by
        rw [hb1]
        ext y
        simp [mem_centralizer_singleton_iff]
      have hCY : centralizer (T : Set X) = Y₁ := by rw [hCTY, hC1, inf_top_eq]
      exact ⟨L, hCY ▸ hLC, hCY ▸ hLpc, le_sup_left⟩
    · have hb2' : orderOf b = 2 := orderOf_eq_prime (by rw [sq, hb2]) hb1
      have hbY : b ∈ Y₁ := mem_inf.mpr ⟨hbH, mem_centralizer_singleton_iff.mpr hab.symm⟩
      exact orbit_location_in hbY hb2' (hCTY ▸ hLC) (hCTY ▸ hLpc)
  obtain ⟨K, hKH, hKpc, hK₁K⟩ := orbit_location_in haH ha2 hK₁Y hK₁pc
  have hMa : M.map (MulAut.conj a).toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer haM)
  have hMb : M.map (MulAut.conj b).toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer hbM)
  have hKM : K ≠ M := by
    intro hKMeq
    rw [hKMeq, hMa, sup_idem] at hK₁K
    have hLM : L ≤ M := by
      refine hLK₁.trans (sup_le hK₁K ?_)
      rw [← hMb]
      exact map_mono hK₁K
    exact false_of_le_oddCore (by omega) θL (le_oddCore_of_le_coreActionKernel hLM hLK hLperf)
  have hMK : M ≤ UnbalancedLayer.coreActionKernel K :=
    GSThmB.B5a.le_coreActionKernel_of_ne hKH hMH hKpc hMpc hKM
  have hKa : K.map (MulAut.conj a).toMonoidHom = K :=
    mem_normalizer_iff_map_conj_eq.mp (UnbalancedLayer.mem_coreActionKernel.mp (hMK haM)).1
  have hKb : K.map (MulAut.conj b).toMonoidHom = K :=
    mem_normalizer_iff_map_conj_eq.mp (UnbalancedLayer.mem_coreActionKernel.mp (hMK hbM)).1
  rw [hKa, sup_idem] at hK₁K
  have hLKK : L ≤ K := by
    refine hLK₁.trans (sup_le hK₁K ?_)
    rw [← hKb]
    exact map_mono hK₁K
  have hTK : T ≤ UnbalancedLayer.coreActionKernel K := hTM.trans hMK
  have hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K H hKH).mp hKpc).2.2
  have hKsub : (K.subgroupOf H).IsSubnormal := hKpc.choose_spec.2.1
  set KT := GSLit.fixedLayer K T with hKTdef
  have hKTpc : IsPComponent 2 (KT.subgroupOf (centralizer (T : Set X))) := by
    have h1 := GSLit.fixedLayer_isPComponent hKH hKsub hTH hTK hT2 hKq
    rwa [inf_eq_right.mpr hCT] at h1
  have hKTC : KT ≤ centralizer (T : Set X) := (GSLit.fixedLayer_le_inf K T).trans inf_le_right
  have hLKT : L ≤ KT := by
    have hLKC : L ≤ K ⊓ centralizer (T : Set X) := le_inf hLKK hLC
    have h1 : IsPComponent 2 (L.subgroupOf (K ⊓ centralizer (T : Set X))) :=
      UnbalancedCorr.isPComponent_subgroupOf_of_le hLKC inf_le_right hLpc
    have h2 : L.subgroupOf (K ⊓ centralizer (T : Set X)) ≤
        pLayer ↥(K ⊓ centralizer (T : Set X)) 2 := le_sSup h1
    intro y hy
    exact ⟨⟨y, hLKC hy⟩, h2 (show (⟨y, hLKC hy⟩ : ↥(K ⊓ centralizer (T : Set X))) ∈
      L.subgroupOf (K ⊓ centralizer (T : Set X)) from hy), rfl⟩
  have hLeq : L = KT := by
    have h1 := CatalogueBPrimeJoin.eq_of_le 2 (L.subgroupOf (centralizer (T : Set X)))
      (KT.subgroupOf (centralizer (T : Set X))) hLpc hKTpc (fun y hy => hLKT hy)
    have h2 := Subgroup.subgroupOf_inj.mp h1
    rwa [inf_of_le_left hLC, inf_of_le_left hKTC] at h2
  obtain ⟨hKTsup, hKTcore⟩ := GSLit.fixedLayer_sup_pPrimeCore hKq hTK hT2
  rw [← hKTdef, ← hLeq] at hKTsup hKTcore
  obtain ⟨φK, -⟩ := UnbalancedCorr.exists_quotient_equiv_of_sup hLKK hKTsup hKTcore
  have htM : t ∈ normalizer (M : Set X) :=
    hHN (S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
      (mem_centralizer_singleton_iff.mpr rfl))
  exact hKM (S.eq_of_isPComponent_alt_of_sup h33 h35 hT13 hML hSch hMH hMpc hKH hKpc htM hsup
    ⟨θ⟩ ⟨φK.symm.trans θL⟩)

theorem false_of_conj_le_coreActionKernel_of_sup_zpowers (S : Sig36 X t J n e E D)
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {x : X}
    (hxM : x ∈ M) (hxN : x ∈ normalizer (M : Set X)) (hx2 : x * x = 1)
    (hx4 : (ρ ⟨x, hxN⟩).support.card = 4)
    (hCx : centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {g : X} (hgH : (zpowers x).map (MulAut.conj g).toMonoidHom ≤
      normalizer (Sol78.signalizerCompletion E E : Set X))
    (hgK : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ UnbalancedLayer.coreActionKernel M) :
    False := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    have h1 : ρ ⟨1, hxN⟩ = 1 := map_one ρ
    rw [h1, Perm.support_one, Finset.card_empty] at hx4
    omega
  have hx2' : orderOf x = 2 := orderOf_eq_prime (by rw [sq, hx2]) hx1
  have hT : zpowers x ⊔ zpowers (1 : X) = zpowers x := by
    rw [zpowers_one_eq_bot, sup_bot_eq]
  have hCT : centralizer ((zpowers x ⊔ zpowers (1 : X) : Subgroup X) : Set X) ≤
      normalizer (Sol78.signalizerCompletion E E : Set X) := by
    rw [hT, UnbalancedLayer.centralizer_zpowers_eq]
    exact hCx
  exact S.false_of_conj_le_coreActionKernel_of_sup h33 h35 hT13 hML hSch hMH hMpc hHN hsup hρ
    hxM (one_mem M) hx2' (mul_one 1) (by rw [mul_one, one_mul]) hCT
    (mem_sup_left (mem_zpowers x)) hxN hx2 hx4 (by rwa [hT]) (by rwa [hT])

theorem false_of_conj_le_coreActionKernel_of_sup_four (S : Sig36 X t J n e E D)
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {F : Subgroup X}
    (hFM : F ≤ M) (hF4 : Nat.card F = 4) (hFsq : ∀ y ∈ F, y * y = 1)
    (hCF : centralizer (F : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {x : X} (hxF : x ∈ F) (hxN : x ∈ normalizer (M : Set X)) (hx2 : x * x = 1)
    (hx4 : (ρ ⟨x, hxN⟩).support.card = 4) {g : X}
    (hgH : F.map (MulAut.conj g).toMonoidHom ≤
      normalizer (Sol78.signalizerCompletion E E : Set X))
    (hgK : F.map (MulAut.conj g).toMonoidHom ≤ UnbalancedLayer.coreActionKernel M) : False := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    have h1 : ρ ⟨1, hxN⟩ = 1 := map_one ρ
    rw [h1, Perm.support_one, Finset.card_empty] at hx4
    omega
  have hx2' : orderOf x = 2 := orderOf_eq_prime (by rw [sq, hx2]) hx1
  obtain ⟨b, hbF, hbx⟩ : ∃ b ∈ F, b ∉ zpowers x := by
    by_contra h
    push Not at h
    have h1 : Nat.card F ≤ Nat.card (zpowers x) := Subgroup.card_le_of_le h
    rw [Nat.card_zpowers, hx2', hF4] at h1
    omega
  have hinv : ∀ y ∈ F, y⁻¹ = y := fun y hy => inv_eq_of_mul_eq_one_right (hFsq y hy)
  have hab : x * b = b * x := by
    have h1 := hinv (x * b) (mul_mem hxF hbF)
    rw [mul_inv_rev, hinv b hbF, hinv x hxF] at h1
    exact h1.symm
  have hTF : zpowers x ⊔ zpowers b ≤ F := sup_le (zpowers_le.mpr hxF) (zpowers_le.mpr hbF)
  have hTeq : zpowers x ⊔ zpowers b = F := by
    refine Subgroup.eq_of_le_of_card_ge hTF ?_
    have hdvd : Nat.card ↥(zpowers x ⊔ zpowers b) ∣ 4 := hF4 ▸ Subgroup.card_dvd_of_le hTF
    obtain ⟨k, hk⟩ : 2 ∣ Nat.card ↥(zpowers x ⊔ zpowers b) := by
      have h1 := Subgroup.card_dvd_of_le (le_sup_left : zpowers x ≤ zpowers x ⊔ zpowers b)
      rwa [Nat.card_zpowers, hx2'] at h1
    have hne2 : Nat.card ↥(zpowers x ⊔ zpowers b) ≠ 2 := by
      intro h2
      apply hbx
      have h3 : zpowers x = zpowers x ⊔ zpowers b :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h2, Nat.card_zpowers, hx2'])
      rw [h3]
      exact mem_sup_right (mem_zpowers b)
    have hle : Nat.card ↥(zpowers x ⊔ zpowers b) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card ↥(zpowers x ⊔ zpowers b) := Nat.card_pos
    rw [hF4]
    omega
  have hCT : centralizer ((zpowers x ⊔ zpowers b : Subgroup X) : Set X) ≤
      normalizer (Sol78.signalizerCompletion E E : Set X) := by
    rw [hTeq]
    exact hCF
  exact S.false_of_conj_le_coreActionKernel_of_sup h33 h35 hT13 hML hSch hMH hMpc hHN hsup hρ
    (hFM hxF) (hFM hbF) hx2' (hFsq b hbF) hab hCT (mem_sup_left (mem_zpowers x)) hxN hx2 hx4
    (by rw [hTeq]; exact hgH) (by rw [hTeq]; exact hgK)

end Sig36

@[expose] def SignalizerConjKernelExclusion : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n)),
    Sig36 X t J n e E D →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X) →
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)), IsPermAction θ ρ →
    ∀ x : X, x ∈ M → ∀ hxN : x ∈ normalizer (M : Set X), x * x = 1 →
      (ρ ⟨x, hxN⟩).support.card = 4 →
      centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
    ∀ g : X, (zpowers x).map (MulAut.conj g).toMonoidHom ≤
        normalizer (Sol78.signalizerCompletion E E : Set X) →
      (zpowers x).map (MulAut.conj g).toMonoidHom ≤ UnbalancedLayer.coreActionKernel M → False

theorem signalizerConjKernelExclusion_of_inputs (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput) :
    SignalizerConjKernelExclusion := by
  intro X _ _ _ t J n e E D S M hMH hMpc hHN hsup θ ρ hρ x hxM hxN hx2 hx4 hCx g hgH hgK
  exact S.false_of_conj_le_coreActionKernel_of_sup_zpowers h33 h35 hT13 hML hSch hMH hMpc hHN
    hsup hρ hxM hxN hx2 hx4 hCx hgH hgK

end CFSG.ComponentClassification.SolMax
