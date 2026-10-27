module

public import CFSG.HardMathSupport.Timmesfeld.Balance.Core
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Input19DeltaReduction
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance

open CFSG CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.Coordinator (DeltaOfLocalBalance)

section Transport

variable {M M' : Type*} [Group M] [Group M']

theorem gLAPPrimeCoreOf_map_mulEquiv (p : ℕ) (φ : M ≃* M') (S : Subgroup M) :
    GLAPPrimeCoreOf p (S.map φ.toMonoidHom) = (GLAPPrimeCoreOf p S).map φ.toMonoidHom := by
  have hp := glaPPrimeCore_map_iso p (S.equivMapOfInjective φ.toMonoidHom φ.injective)
  have hf : (S.map φ.toMonoidHom).subtype.comp
      (S.equivMapOfInjective φ.toMonoidHom φ.injective).toMonoidHom =
      φ.toMonoidHom.comp S.subtype := by
    ext t
    rfl
  calc GLAPPrimeCoreOf p (S.map φ.toMonoidHom)
      = ((GLAPPrimeCore p ↥S).map
          (S.equivMapOfInjective φ.toMonoidHom φ.injective).toMonoidHom).map
          (S.map φ.toMonoidHom).subtype := by
        rw [hp]; rfl
    _ = (GLAPPrimeCore p ↥S).map ((S.map φ.toMonoidHom).subtype.comp
      (S.equivMapOfInjective φ.toMonoidHom φ.injective).toMonoidHom) :=
        Subgroup.map_map _ _ _
    _ = (GLAPPrimeCore p ↥S).map (φ.toMonoidHom.comp S.subtype) := by rw [hf]
    _ = (GLAPPrimeCoreOf p S).map φ.toMonoidHom := (Subgroup.map_map _ _ _).symm

theorem map_centralizer_singleton_mulEquiv (φ : M ≃* M') (d : M) :
    (Subgroup.centralizer ({d} : Set M)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ d} : Set M') := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg φ h
    simpa [eq_comm] using this
  · intro h
    apply φ.injective
    simpa [eq_comm] using h

theorem gLAPPrimeCoreOf_map_inf_centralizer (p : ℕ) (φ : M ≃* M') (H : Subgroup M) (d : M) :
    GLAPPrimeCoreOf p (H.map φ.toMonoidHom ⊓ Subgroup.centralizer ({φ d} : Set M')) =
      (GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({d} : Set M))).map φ.toMonoidHom := by
  rw [← gLAPPrimeCoreOf_map_mulEquiv, Subgroup.map_inf_eq _ _ φ.toMonoidHom φ.injective,
    map_centralizer_singleton_mulEquiv]

theorem localDeltaIn_map_mulEquiv (p : ℕ) (φ : M ≃* M') (H D : Subgroup M) :
    localDeltaIn p (H.map φ.toMonoidHom) (D.map φ.toMonoidHom) =
      (localDeltaIn p H D).map φ.toMonoidHom := by
  ext y
  rw [Subgroup.mem_map_equiv]
  simp only [localDeltaIn, Subgroup.mem_iInf]
  constructor
  · intro h d hd hd1
    have h1 := h (φ d) ⟨d, hd, rfl⟩ (fun h' => hd1 (φ.injective (by simpa using h')))
    rw [gLAPPrimeCoreOf_map_inf_centralizer, Subgroup.mem_map_equiv] at h1
    exact h1
  · rintro h d' ⟨d, hd, rfl⟩ hd1
    have h1 := h d hd (fun h' => hd1 (by simp [h']))
    have e := gLAPPrimeCoreOf_map_inf_centralizer p φ H d
    change y ∈ GLAPPrimeCoreOf p (H.map φ.toMonoidHom ⊓ Subgroup.centralizer ({φ d} : Set M'))
    rw [e, Subgroup.mem_map_equiv]
    exact h1

theorem map_map_symm_mulEquiv (φ : M ≃* M') (S : Subgroup M) :
    (S.map φ.toMonoidHom).map φ.symm.toMonoidHom = S := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
  simp

theorem map_symm_map_mulEquiv (φ : M ≃* M') (S : Subgroup M') :
    (S.map φ.symm.toMonoidHom).map φ.toMonoidHom = S := by
  have := map_map_symm_mulEquiv φ.symm S
  simpa using this

theorem isEkIn_map_mulEquiv (p k : ℕ) (φ : M ≃* M') {A D : Subgroup M}
    (h : IsEkIn p k A D) : IsEkIn p k (A.map φ.toMonoidHom) (D.map φ.toMonoidHom) := by
  obtain ⟨hDA, ⟨hcomm, hexp⟩, hcard⟩ := h
  refine ⟨Subgroup.map_mono hDA, ⟨?_, ?_⟩, ?_⟩
  · have := hcomm
    infer_instance
  · rintro _ ⟨d, hd, rfl⟩
    simpa using congrArg φ (hexp d hd)
  · rw [Subgroup.card_map_of_injective φ.injective, hcard]

theorem mem_normalizer_map_symm (φ : M ≃* M') {S : Subgroup M'} {d : M'}
    (hd : d ∈ Subgroup.normalizer (S : Set M')) :
    φ.symm d ∈ Subgroup.normalizer ((S.map φ.symm.toMonoidHom : Subgroup M) : Set M) := by
  rw [Subgroup.mem_normalizer_iff] at hd ⊢
  intro x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
  simpa using hd (φ x)

end Transport

section TransportBalanced

variable {K K' : Type*} [Group K] [Group K']

theorem congr_conj_apply (θ : K ≃* K') (k : K) :
    MulAut.congr θ (MulAut.conj k) = MulAut.conj (θ k) := by
  ext z
  simp [MulAut.congr_apply]

theorem isLocallyBalanced_map_congr (p k : ℕ) (θ : K ≃* K') {A : Subgroup (MulAut K)}
    (h : IsLocallyBalanced p k A) :
    IsLocallyBalanced p k (A.map (MulAut.congr θ).toMonoidHom) := by
  intro D' hD' H' hH' hDH'
  set φ := MulAut.congr θ with hφ
  have hD : IsEkIn p k A (D'.map φ.symm.toMonoidHom) := by
    have := isEkIn_map_mulEquiv p k φ.symm hD'
    rwa [map_map_symm_mulEquiv] at this
  have hH : innerAut K ≤ H'.map φ.symm.toMonoidHom := by
    rintro _ ⟨k, rfl⟩
    rw [Subgroup.mem_map_equiv]
    have h1 := hH' ⟨θ k, rfl⟩
    have e : φ (MulAut.conj k) = MulAut.conj (θ k) := congr_conj_apply θ k
    show φ (MulAut.conj k) ∈ H'
    rw [e]
    exact h1
  have hDH : D'.map φ.symm.toMonoidHom ≤
      Subgroup.normalizer ((H'.map φ.symm.toMonoidHom : Subgroup _) : Set _) := by
    rintro _ ⟨d', hd', rfl⟩
    exact mem_normalizer_map_symm φ (hDH' hd')
  have key := h _ hD _ hH hDH
  have := localDeltaIn_map_mulEquiv p φ (H'.map φ.symm.toMonoidHom) (D'.map φ.symm.toMonoidHom)
  rw [key, map_symm_map_mulEquiv, map_symm_map_mulEquiv, Subgroup.map_bot] at this
  exact this

theorem isLocallyBalanced_mono (p k : ℕ) {A A' : Subgroup (MulAut K)} (hA : A' ≤ A)
    (h : IsLocallyBalanced p k A) : IsLocallyBalanced p k A' :=
  fun D hD => h D ⟨hD.1.trans hA, hD.2⟩

end TransportBalanced


section BarIso

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

@[expose] noncomputable def barHom (p : ℕ) {H J : Subgroup G} (hJH : J ≤ H) : ↥J →* ↥(barX p H J) :=
  ((QuotientGroup.mk' (GLAPPrimeCore p ↥H)).comp (Subgroup.inclusion hJH)).codRestrict
    (barX p H J) (fun x => ⟨Subgroup.inclusion hJH x, (Subgroup.mem_subgroupOf).2 x.2, rfl⟩)

theorem coe_barHom (p : ℕ) {H J : Subgroup G} (hJH : J ≤ H) (x : ↥J) :
    ((barHom p hJH x : ↥(barX p H J)) : ↥H ⧸ GLAPPrimeCore p ↥H) =
      QuotientGroup.mk (Subgroup.inclusion hJH x) := rfl

theorem barHom_surjective (p : ℕ) {H J : Subgroup G} (hJH : J ≤ H) :
    Function.Surjective (barHom p hJH) := by
  rintro ⟨z, x, hx, rfl⟩
  exact ⟨⟨x, (Subgroup.mem_subgroupOf).1 hx⟩, Subtype.ext rfl⟩

theorem ker_barHom (hp : p.Prime) {H J : Subgroup G} (hJH : J ≤ H) (hsn : IsSubnormal J H) :
    (barHom p hJH).ker = GLAPPrimeCore p ↥J := by
  have h := glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsn
  ext x
  rw [MonoidHom.mem_ker]
  have h1 : barHom p hJH x = 1 ↔ Subgroup.inclusion hJH x ∈ GLAPPrimeCore p ↥H := by
    rw [← Subtype.coe_inj, coe_barHom]
    exact (QuotientGroup.eq_one_iff _)
  have h2 : (x : G) ∈ GLAPPrimeCoreOf p H ↔ Subgroup.inclusion hJH x ∈ GLAPPrimeCore p ↥H := by
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = Subgroup.inclusion hJH x := Subtype.ext hyx
      rwa [← this]
    · intro hx
      exact ⟨_, hx, rfl⟩
  have h3 : (x : G) ∈ GLAPPrimeCoreOf p J ↔ x ∈ GLAPPrimeCore p ↥J :=
    Subgroup.mem_map_iff_mem J.subtype_injective
  rw [h1, ← h2, ← h3, ← h]
  simp [x.2]

@[expose] noncomputable def barIso (hp : p.Prime) {H J : Subgroup G} (hJH : J ≤ H)
    (hsn : IsSubnormal J H) : barOf p J ≃* ↥(barX p H J) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_barHom hp hJH hsn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (barHom p hJH) (barHom_surjective p hJH))

theorem barIso_mk (hp : p.Prime) {H J : Subgroup G} (hJH : J ≤ H) (hsn : IsSubnormal J H)
    (x : ↥J) : barIso hp hJH hsn (QuotientGroup.mk x) = barHom p hJH x := rfl

theorem barIso_equivariant (hp : p.Prime) {H J : Subgroup G} (hJH : J ≤ H)
    (hsn : IsSubnormal J H) {e : G} (heH : e ∈ H)
    (heJ : e ∈ Subgroup.normalizer (J : Set G))
    (hy : QuotientGroup.mk (⟨e, heH⟩ : ↥H) ∈
      Subgroup.normalizer ((barX p H J : Subgroup (↥H ⧸ GLAPPrimeCore p ↥H)) :
        Set (↥H ⧸ GLAPPrimeCore p ↥H))) :
    CFSG.LocalAnalysis.ComponentInitial.normalizerConjHom (barX p H J)
        ⟨QuotientGroup.mk (⟨e, heH⟩ : ↥H), hy⟩ =
      MulAut.congr (barIso hp hJH hsn) (barAut p J ⟨e, heJ⟩) := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨z, rfl⟩ := (barIso hp hJH hsn).surjective y
  induction z using QuotientGroup.induction_on with
  | _ x =>
  apply Subtype.ext
  rw [CFSG.LocalAnalysis.ComponentInitial.coe_normalizerConjHom_apply]
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [barAut_mk]
  simp only [barIso_mk, coe_barHom]
  have h : Subgroup.inclusion hJH (J.normalizerMonoidHom ⟨e, heJ⟩ x) =
      (⟨e, heH⟩ : ↥H) * Subgroup.inclusion hJH x * (⟨e, heH⟩ : ↥H)⁻¹ := by
    apply Subtype.ext
    rfl
  rw [h, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

end BarIso

section Normalizes

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

omit [Finite G] in
theorem mem_barX_iff (p : ℕ) (X K : Subgroup G) (z : ↥X ⧸ GLAPPrimeCore p ↥X) :
    z ∈ barX p X K ↔ ∃ x : ↥X, (x : G) ∈ K ∧ (QuotientGroup.mk x : ↥X ⧸ GLAPPrimeCore p ↥X) = z := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (Subgroup.mem_subgroupOf).1 hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (Subgroup.mem_subgroupOf).2 hx, rfl⟩

omit [Finite G] in
theorem gLBConj_eq_of_mem {e : G} {H : Subgroup G} (he : e ∈ H) : GLBConj e H = H := by
  ext y
  rw [mem_gLBConj]
  constructor
  · intro h
    have := H.mul_mem (H.mul_mem (H.inv_mem he) h) he
    simpa [mul_assoc] using this
  · intro h
    exact H.mul_mem (H.mul_mem he h) (H.inv_mem he)

omit [Finite G] in
theorem barX_gLBConj_eq_of_mem_normalizer {H J : Subgroup G} {e : G} (heH : e ∈ H)
    (hy : (QuotientGroup.mk (⟨e, heH⟩ : ↥H) : ↥H ⧸ GLAPPrimeCore p ↥H) ∈
      Subgroup.normalizer ((barX p H J : Subgroup (↥H ⧸ GLAPPrimeCore p ↥H)) :
        Set (↥H ⧸ GLAPPrimeCore p ↥H))) :
    barX p H (GLBConj e J) = barX p H J := by
  set q : ↥H ⧸ GLAPPrimeCore p ↥H := QuotientGroup.mk (⟨e, heH⟩ : ↥H) with hq
  have hN := Subgroup.mem_normalizer_iff.1 hy
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := (mem_barX_iff p H _ z).1 hz
    rw [hN]
    refine (mem_barX_iff p H J _).2 ⟨⟨e, heH⟩ * x * ⟨e, heH⟩⁻¹, ?_, ?_⟩
    · exact mem_gLBConj.1 hx
    · simp [hq]
  · intro hz
    have hz' := (hN z).1 hz
    obtain ⟨j, hj, hjz⟩ := (mem_barX_iff p H J _).1 hz'
    refine (mem_barX_iff p H _ z).2 ⟨⟨e, heH⟩⁻¹ * j * ⟨e, heH⟩, ?_, ?_⟩
    · rw [mem_gLBConj]
      simpa [mul_assoc] using hj
    · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hjz]
      rw [← hq]
      group

theorem mem_normalizer_of_barX_normalizer {H J : Subgroup G}
    (hJ : GLAPComponent p H J) {e : G} (heH : e ∈ H)
    (hy : (QuotientGroup.mk (⟨e, heH⟩ : ↥H) : ↥H ⧸ GLAPPrimeCore p ↥H) ∈
      Subgroup.normalizer ((barX p H J : Subgroup (↥H ⧸ GLAPPrimeCore p ↥H)) :
        Set (↥H ⧸ GLAPPrimeCore p ↥H))) :
    e ∈ Subgroup.normalizer (J : Set G) := by
  have h1 := glaPComponent_gLBConj hJ e
  rw [gLBConj_eq_of_mem heH] at h1
  have h2 := glaPComponent_unique h1 hJ (barX_gLBConj_eq_of_mem_normalizer heH hy)
  exact mem_normalizer_iff_gLBConj_eq.2 h2

end Normalizes

section FImage

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem isLocallyBalanced_fImage (hp : p.Prime) {k : ℕ} {H B E : Subgroup G} (hEB : E ≤ B)
    (hEH : E ≤ H) {J : Subgroup G} (hJ : GLAPComponent p H J)
    (hbal : IsCompLocallyBalanced p k B J)
    (hF : ∀ e : ↥H, (e : G) ∈ E → (QuotientGroup.mk e : ↥H ⧸ GLAPPrimeCore p ↥H) ∈
      Subgroup.normalizer ((barX p H J : Subgroup (↥H ⧸ GLAPPrimeCore p ↥H)) :
        Set (↥H ⧸ GLAPPrimeCore p ↥H))) :
    IsLocallyBalanced p k
      (fImage ((E.subgroupOf H).map (QuotientGroup.mk' (GLAPPrimeCore p ↥H)))
        (barX p H J)) := by
  set θ := barIso hp hJ.1 hJ.2.1 with hθ
  have hmap : IsLocallyBalanced p k ((autBar p B J).map (MulAut.congr θ).toMonoidHom) :=
    isLocallyBalanced_map_congr p k θ hbal
  refine isLocallyBalanced_mono p k ?_ hmap
  rintro _ ⟨γ, hγ, rfl⟩
  obtain ⟨e', he', hee'⟩ := (Subgroup.mem_map).1 ((Subgroup.mem_subgroupOf).1 hγ)
  have heE : (e' : G) ∈ E := (Subgroup.mem_subgroupOf).1 he'
  have heJ : (e' : G) ∈ Subgroup.normalizer (J : Set G) :=
    mem_normalizer_of_barX_normalizer hJ e'.2 (hF e' heE)
  have hγe : γ = ⟨QuotientGroup.mk e', hF e' heE⟩ := Subtype.ext hee'.symm
  refine ⟨barAut p J ⟨e', heJ⟩, ?_, ?_⟩
  · refine Subgroup.mem_map.2 ⟨⟨e', heJ⟩, ?_, rfl⟩
    exact (Subgroup.mem_subgroupOf).2 ⟨hEB heE, heJ⟩
  · rw [hγe]
    exact (barIso_equivariant hp hJ.1 hJ.2.1 e'.2 heJ (hF e' heE)).symm

end FImage

section Main

variable {G : Type*} [Group G]

theorem eq_one_of_mem_of_coprime {p : ℕ} {N E' : Subgroup G}
    (hN : Nat.Coprime p (Nat.card N)) (hE : ∀ x ∈ E', x ^ p = 1) {z : G} (hzE : z ∈ E')
    (hzN : z ∈ N) : z = 1 := by
  have h1 : orderOf z ∣ Nat.card N := by
    have := Subgroup.orderOf_dvd_natCard N hzN
    simpa using this
  have h2 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one (hE z hzE)
  have h3 : orderOf z ∣ Nat.gcd p (Nat.card N) := Nat.dvd_gcd h2 h1
  rw [hN] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

end Main

section QuotientImage

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem elemAbelian_subgroupOf {H E : Subgroup G} (hEH : E ≤ H) (hel : IsElemAbelian p E) :
    IsElemAbelian p (E.subgroupOf H) := by
  refine ⟨?_, fun x hx => Subtype.ext (by simpa using hel.2 (x : G) hx)⟩
  have e := Subgroup.subgroupOfEquivOfLe hEH
  have hc := hel.1
  exact ⟨⟨fun a b => e.injective (by
    have := hc.is_comm.comm (e a) (e b)
    simpa using this)⟩⟩

theorem card_subgroupOf_eq {H E : Subgroup G} (hEH : E ≤ H) :
    Nat.card (E.subgroupOf H) = Nat.card E :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv

theorem domRestrict_mk_injective (hp : p.Prime) {H E : Subgroup G} (hEH : E ≤ H)
    (hel : IsElemAbelian p E) :
    Function.Injective ((QuotientGroup.mk' (GLAPPrimeCore p ↥H)).domRestrict (E.subgroupOf H)) := by
  intro a b hab
  have h1 : (QuotientGroup.mk (a : ↥H) : ↥H ⧸ GLAPPrimeCore p ↥H) = QuotientGroup.mk (b : ↥H) :=
    hab
  have h2 : (a : ↥H)⁻¹ * (b : ↥H) ∈ GLAPPrimeCore p ↥H := QuotientGroup.eq.1 h1
  have h3 : (a : ↥H)⁻¹ * (b : ↥H) ∈ E.subgroupOf H := Subgroup.mul_mem _ (Subgroup.inv_mem _ a.2) b.2
  have h4 := eq_one_of_mem_of_coprime (N := GLAPPrimeCore p ↥H) (E' := E.subgroupOf H)
    (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore hp _)
    (elemAbelian_subgroupOf hEH hel).2 h3 h2
  exact Subtype.ext (inv_mul_eq_one.1 h4)

theorem mk_ne_one (hp : p.Prime) {H E : Subgroup G} (hEH : E ≤ H) (hel : IsElemAbelian p E)
    {e : ↥H} (he : (e : G) ∈ E) (hne : e ≠ 1) :
    (QuotientGroup.mk e : ↥H ⧸ GLAPPrimeCore p ↥H) ≠ 1 := by
  intro h
  refine hne ?_
  have hinj := domRestrict_mk_injective hp hEH hel
  have : (⟨e, (Subgroup.mem_subgroupOf).2 he⟩ : ↥(E.subgroupOf H)) = 1 := by
    apply hinj
    simpa using h
  simpa using congrArg Subtype.val this

theorem elemAbelian_image (hp : p.Prime) {H E : Subgroup G} (hEH : E ≤ H)
    (hel : IsElemAbelian p E) :
    IsElemAbelian p ((E.subgroupOf H).map (QuotientGroup.mk' (GLAPPrimeCore p ↥H))) := by
  have h := elemAbelian_subgroupOf hEH hel
  refine ⟨?_, ?_⟩
  · have := h.1
    infer_instance
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, h.2 x hx, map_one]

theorem card_image (hp : p.Prime) {H E : Subgroup G} (hEH : E ≤ H)
    (hel : IsElemAbelian p E) :
    Nat.card ((E.subgroupOf H).map (QuotientGroup.mk' (GLAPPrimeCore p ↥H))) = Nat.card E := by
  rw [← card_subgroupOf_eq hEH, ← MonoidHom.domRestrict_range]
  exact (Nat.card_congr (MonoidHom.ofInjective (domRestrict_mk_injective hp hEH hel)).toEquiv).symm

end QuotientImage

theorem mk_mem_centralizer_core {G : Type} [Group G] [Finite G] {p : ℕ} (hH1 : H1Stmt.{0})
    (hp : p.Prime) {H E : Subgroup G} (hEH : E ≤ H) (hel : IsElemAbelian p E) {x : ↥H} {e : ↥H}
    (he : (e : G) ∈ E) (hne : e ≠ 1)
    (hx : (x : G) ∈ GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({(e : G)} : Set G))) :
    (QuotientGroup.mk x : ↥H ⧸ GLAPPrimeCore p ↥H) ∈
      GLAPPrimeCoreOf p (Subgroup.centralizer
        ({(QuotientGroup.mk e : ↥H ⧸ GLAPPrimeCore p ↥H)} :
          Set (↥H ⧸ GLAPPrimeCore p ↥H))) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [gLAPPrimeCoreOf_inf_centralizer_eq_map p H e.2] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : y = x := Subtype.ext hyx
  subst hyx'
  have hpe : e ^ p = 1 := Subtype.ext (by simpa using hel.2 (e : G) he)
  have hQ : IsPGroup p (Subgroup.zpowers e) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hpe hne, pow_one])
  have h1 := hH1 (QuotientGroup.mk' (GLAPPrimeCore p ↥H)) (QuotientGroup.mk'_surjective _) hp hQ
  have e1 : (Subgroup.centralizer ((Subgroup.zpowers e : Subgroup ↥H) : Set ↥H)) =
      Subgroup.centralizer ({e} : Set ↥H) := by
    rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.centralizer_closure _
  have e2 : ((Subgroup.zpowers e).map (QuotientGroup.mk' (GLAPPrimeCore p ↥H)) :
      Subgroup (↥H ⧸ GLAPPrimeCore p ↥H)) =
      Subgroup.zpowers (QuotientGroup.mk e : ↥H ⧸ GLAPPrimeCore p ↥H) :=
    MonoidHom.map_zpowers _ e
  have e3 : (Subgroup.centralizer ((Subgroup.zpowers
      (QuotientGroup.mk e : ↥H ⧸ GLAPPrimeCore p ↥H) : Subgroup _) : Set _)) =
      Subgroup.centralizer ({(QuotientGroup.mk e : ↥H ⧸ GLAPPrimeCore p ↥H)} : Set _) := by
    rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.centralizer_closure _
  rw [e1] at h1
  rw [e2, e3] at h1
  exact h1 ⟨y, hy, rfl⟩

theorem deltaOfLocalBalance_of_H1 (hH1 : H1Stmt.{0}) : DeltaOfLocalBalance := by
  intro G _ _ p hp _ k hk H B E hBH _ hE hloc
  have hEB : E ≤ B := hE.1
  have hEH : E ≤ H := hEB.trans hBH
  have hel : IsElemAbelian p E := hE.2.1
  have hcard : Nat.card E = p ^ k := hE.2.2
  set F : Subgroup (↥H ⧸ GLAPPrimeCore p ↥H) :=
    (E.subgroupOf H).map (QuotientGroup.mk' (GLAPPrimeCore p ↥H)) with hF
  have hFel : IsElemAbelian p F := elemAbelian_image hp hEH hel
  have hFcard : Nat.card F = p ^ k := (card_image hp hEH hel).trans hcard
  have hO : GLAPPrimeCore p (↥H ⧸ GLAPPrimeCore p ↥H) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hFloc : ∀ L : Subgroup (↥H ⧸ GLAPPrimeCore p ↥H), IsComponent L →
      F ≤ Subgroup.normalizer (L : Set (↥H ⧸ GLAPPrimeCore p ↥H)) →
      (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f) → IsLocallyBalanced p k (fImage F L) := by
    intro L hL hFn _
    obtain ⟨J, hJ, rfl⟩ := exists_glaPComponent_barX_eq (p := p) H ((isComponent_iff_open L).1 hL)
    refine isLocallyBalanced_fImage hp hEB hEH hJ (hloc J hJ) fun e he => ?_
    exact hFn ⟨e, (Subgroup.mem_subgroupOf).2 he, rfl⟩
  have hdelta := delta_eq_bot_of_locallyBalanced hH1 hp hk hO hFel hFcard hFloc
  obtain ⟨e₀, he₀E, he₀⟩ : ∃ e ∈ E, e ≠ 1 := by
    have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hcard]; exact Nat.one_lt_pow (by omega) hp.one_lt)
    obtain ⟨⟨e, he⟩, hne⟩ := exists_ne (1 : E)
    exact ⟨e, he, fun h => hne (Subtype.ext h)⟩
  intro x hx
  rw [Subgroup.mem_iInf] at hx
  have hx₀ := hx e₀
  rw [Subgroup.mem_iInf, Subgroup.mem_iInf] at hx₀
  have hxH : x ∈ H := (Subgroup.mem_inf.1 (Subgroup.map_subtype_le _ (hx₀ he₀E he₀))).1
  have hmem : (QuotientGroup.mk (⟨x, hxH⟩ : ↥H) : ↥H ⧸ GLAPPrimeCore p ↥H) ∈
      (⨅ (f : ↥H ⧸ GLAPPrimeCore p ↥H) (_ : f ∈ F) (_ : f ≠ 1),
        GLAPPrimeCoreOf p (Subgroup.centralizer ({f} : Set (↥H ⧸ GLAPPrimeCore p ↥H)))) := by
    simp only [Subgroup.mem_iInf]
    rintro f ⟨e', he', rfl⟩ hf1
    have heE : (e' : G) ∈ E := (Subgroup.mem_subgroupOf).1 he'
    have hne : e' ≠ 1 := fun h => hf1 (by rw [h, map_one])
    have hene : (e' : G) ≠ 1 := fun h => hne (Subtype.ext h)
    have hx1 := hx (e' : G)
    rw [Subgroup.mem_iInf, Subgroup.mem_iInf] at hx1
    exact mk_mem_centralizer_core hH1 hp hEH hel heE hne (hx1 heE hene)
  rw [hdelta, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
  exact ⟨_, hmem, rfl⟩

end CFSG.HardMathSupport.Timmesfeld.Balance
