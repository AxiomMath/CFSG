module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeGlue
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeGlueCert
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModelsCert
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeNormXR
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeInputs
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeTransport
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeEnd
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeCase
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Main

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81.HeTri

open Subgroup CFSG.Monster.B.Co2 CFSG.ComponentClassification.AS81.HeSylow
open CFSG.ComponentClassification.AS81.Hexa CFSG.ComponentClassification.AS81.HePres.Native
open CFSG.ComponentClassification.AS81.HePres CFSG.Open CFSG.Sporadic.Schreier CFSG.Sporadic.HeldB
open CFSG.LargeExtraspecial
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F S₁ Q : Subgroup G}
  {z : G}

theorem z_mem_of_card (hQ : Sec4Q G A R g E F S₁ Q z) {X : Subgroup G}
    (hQX : Q ≤ normalizer (X : Set G)) (hcard : Nat.card (Q ⊓ X : Subgroup G) = 16) : z ∈ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent Q := hQ.extraspecial.1.isNilpotent
  have hN : (X.subgroupOf Q).Normal := by
    constructor
    intro x hx q
    rw [mem_subgroupOf] at hx ⊢
    simp only [coe_mul, coe_inv]
    exact (mem_normalizer_iff.mp (hQX q.2) x).mp hx
  have hne : X.subgroupOf Q ≠ ⊥ := by
    intro h
    have h1 : Nat.card (X.subgroupOf Q) = 16 := by
      rw [← hcard, inf_comm, ← inf_subgroupOf_right X Q]
      exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [h, card_bot] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyX : ((y : Q) : G) ∈ X := mem_subgroupOf.mp (mem_inf.mp y.2).1
  have hyZ : ((y : Q) : G) ∈ centerIn Q := by
    refine mem_centerIn.mpr ⟨(y : Q).2, mem_centralizer_iff.mpr fun w hw => ?_⟩
    exact congrArg Subtype.val ((mem_center_iff.mp (mem_inf.mp y.2).2) ⟨w, hw⟩)
  rw [hQ.center_Q] at hyZ
  rcases eq_one_or_eq_of_mem_zpowers hQ.order_z hyZ with h | h
  · exact absurd (Subtype.ext (Subtype.ext h)) hy1
  · rwa [← h]

omit [Finite G] in
theorem centralizer_le_of_mulEquiv {X : Subgroup G} (hzX : z ∈ X)
    {U : Subgroup (Equiv.Perm (Fin 32))}
    (hUC : U ≤ hePC) (fC : ↥hePC ≃* ↥(centralizer ({z} : Set G)))
    (hCX : ∀ n : ↥hePC, (n : Equiv.Perm (Fin 32)) ∈ U ↔ (fC n : G) ∈ X)
    (hcent : hePC ⊓ centralizer (U : Set (Equiv.Perm (Fin 32))) ≤ U) :
    centralizer (X : Set G) ≤ X := by
  intro x hx
  have hxz : x ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hx z hzX).symm)
  set n := fC.symm ⟨x, hxz⟩ with hn
  have hfn : (fC n : G) = x := by rw [hn, MulEquiv.apply_symm_apply]
  have hnU : (n : Equiv.Perm (Fin 32)) ∈ U := by
    refine hcent ⟨n.2, mem_centralizer_iff.mpr fun u hu => ?_⟩
    have hfu := (hCX ⟨u, hUC hu⟩).mp hu
    have hc := mem_centralizer_iff.mp hx _ hfu
    have : fC (⟨u, hUC hu⟩ * n) = fC (n * ⟨u, hUC hu⟩) := by
      apply Subtype.ext
      rw [map_mul, map_mul, coe_mul, coe_mul, hfn]
      exact hc
    exact congrArg Subtype.val (fC.injective this)
  rw [← hfn]
  exact (hCX n).mp hnU

theorem injective_of_ne_one {P K : Type*} [Group P] [Group K] [IsSimpleGroup P] (Φ : P →* K)
    {x : P} (hx : Φ x ≠ 1) : Function.Injective Φ := by
  rcases (Φ.normal_ker).eq_bot_or_eq_top with h | h
  · exact (MonoidHom.ker_eq_bot_iff Φ).mp h
  · exfalso
    have : x ∈ Φ.ker := h ▸ mem_top x
    exact hx this

omit [Finite G] in
theorem hexaR0_le_of {K : Subgroup (Equiv.Perm (Fin 64))}
    (h₀ : permOfArr 64 (hexaR0Gens.getD 0 #[]) ∈ K)
    (h₁ : permOfArr 64 (hexaR0Gens.getD 1 #[]) ∈ K) :
    hexaR0 ≤ K := by
  refine grpN_le fun a ha => ?_
  simp only [hexaR0Gens, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact h₀
  · exact h₁

omit [Finite G] in
theorem comap_eq_conj {P : Type*} [Group P] (Φ : P →* G) (hΦ : Function.Injective Φ)
    {L : Subgroup G} (fE : ↥heN0 ≃* ↥L) (hLΦ : L ≤ Φ.range) {c p : ↥heN0}
    (hR : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ hexaR0 ↔ (fE (c * n * c⁻¹) : G) ∈ R)
    (hRL : R ≤ L) {w₀ w₁ : P}
    (hw₀ : ∃ h : permOfArr 64 (hexaR0Gens.getD 0 #[]) ∈ heN0,
      Φ w₀ = (fE (p * ⟨_, h⟩ * p⁻¹) : G))
    (hw₁ : ∃ h : permOfArr 64 (hexaR0Gens.getD 1 #[]) ∈ heN0,
      Φ w₁ = (fE (p * ⟨_, h⟩ * p⁻¹) : G)) :
    ∃ π : P, R.comap Φ = (closure ({w₀, w₁} : Set P)).map (MulAut.conj π).toMonoidHom := by
  obtain ⟨h₀, hw₀⟩ := hw₀
  obtain ⟨h₁, hw₁⟩ := hw₁
  set θ : ↥heN0 →* G := L.subtype.comp (fE.toMonoidHom.comp (MulAut.conj p).toMonoidHom)
    with hθ
  have hθa : ∀ n, θ n = (fE (p * n * p⁻¹) : G) := fun n => rfl
  obtain ⟨π, hπ⟩ := hLΦ (fE (c * p⁻¹)).2
  have hconj : ∀ n : ↥heN0, Φ π * θ n * (Φ π)⁻¹ = (fE (c * n * c⁻¹) : G) := by
    intro n
    rw [hπ, hθa, ← coe_inv, ← map_inv, ← coe_mul, ← coe_mul, ← map_mul, ← map_mul]
    congr 2
    group
  set K := closure ({w₀, w₁} : Set P) with hKdef
  have hK1 : K.map Φ ≤ (hexaR0.subgroupOf heN0).map θ := by
    rw [hKdef, MonoidHom.map_closure, closure_le]
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl
    · exact ⟨⟨_, h₀⟩, mem_subgroupOf.mpr (gen_mem_grpN (by simp [hexaR0Gens])), hw₀.symm⟩
    · exact ⟨⟨_, h₁⟩, mem_subgroupOf.mpr (gen_mem_grpN (by simp [hexaR0Gens])), hw₁.symm⟩
  have hK2 : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ hexaR0 → θ n ∈ K.map Φ := by
    intro n hn
    have hle : hexaR0 ≤ ((K.map Φ).comap θ).map heN0.subtype :=
      hexaR0_le_of ⟨⟨_, h₀⟩, by
          show θ _ ∈ K.map Φ
          rw [hθa, ← hw₀]
          exact mem_map_of_mem Φ (subset_closure (Set.mem_insert _ _)), rfl⟩
        ⟨⟨_, h₁⟩, by
          show θ _ ∈ K.map Φ
          rw [hθa, ← hw₁]
          exact mem_map_of_mem Φ (subset_closure (Set.mem_insert_of_mem _ rfl)), rfl⟩
    obtain ⟨n', hn', he⟩ := hle hn
    rw [show n' = n from Subtype.ext he] at hn'
    exact hn'
  refine ⟨π, le_antisymm (fun x hx => ?_) ?_⟩
  ·
    have hxL := hRL hx
    set m : ↥heN0 := fE.symm ⟨Φ x, hxL⟩ with hm
    set n : ↥heN0 := c⁻¹ * m * c with hn
    have hfn : (fE (c * n * c⁻¹) : G) = Φ x := by
      rw [show c * n * c⁻¹ = m by rw [hn]; group, hm, MulEquiv.apply_symm_apply]
    have hnR : (n : Equiv.Perm (Fin 64)) ∈ hexaR0 := (hR n).mpr (by rw [hfn]; exact hx)
    obtain ⟨y, hyK, hy⟩ := hK2 n hnR
    refine ⟨y, hyK, hΦ ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv, hy, hconj, hfn]
  ·
    rintro _ ⟨y, hyK, rfl⟩
    obtain ⟨n, hn, hny⟩ := hK1 (mem_map_of_mem Φ hyK)
    rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv,
      ← hny, hconj]
    exact (hR n).mp (mem_subgroupOf.mp hn)

omit [Finite G] in
theorem map_subgroupOf_range_eq {P K : Type*} [Group P] [Group K] (Φ : P →* G)
    (hΦ : Function.Injective Φ) (ψ : P →* K) {R : Subgroup G} :
    (R.subgroupOf Φ.range).map (ψ.comp (MonoidHom.ofInjective hΦ).symm.toMonoidHom) =
      (R.comap Φ).map ψ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(MonoidHom.ofInjective hΦ).symm y, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_comap]
    have : Φ ((MonoidHom.ofInjective hΦ).symm y) = y := by
      have h := MonoidHom.ofInjective_apply hΦ (x := (MonoidHom.ofInjective hΦ).symm y)
      rw [MulEquiv.apply_symm_apply] at h
      exact h.symm
    rw [this]
    exact mem_subgroupOf.mp hy
  · rintro ⟨a, ha, rfl⟩
    refine ⟨MonoidHom.ofInjective hΦ a, mem_subgroupOf.mpr ?_, ?_⟩
    · rw [MonoidHom.ofInjective_apply]
      exact ha
    · simp

omit [Finite G] in
theorem map_map_conj {P K : Type*} [Group P] [Group K] (ψ : P →* K) (π : P) (S : Subgroup P) :
    (S.map (MulAut.conj π).toMonoidHom).map ψ = (S.map ψ).map (MulAut.conj (ψ π)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem isSporadic_of_hePiHom
    (hQ : Sec4Q G A R g E F S₁ Q z) (hs : IsSimpleGroup G)
    (hO2 : pCoreOf 2 (centralizer ({z} : Set G)) = Q) (hRA : R ≤ A)
    (hS₁E : S₁ ≤ normalizer (E : Set G)) (hCE : centralizer (E : Set G) ≤ E)
    (hCz : Nat.card (centralizer ({z} : Set G)) = 21504) (Φ : HePi →* G) (hΦz : Φ hePiZ = z)
    (hCΦ : centralizer ({z} : Set G) ≤ Φ.range)
    (hLΦ : AS76b.oUpperTwoPrime (normalizer (E : Set G)) ≤ Φ.range) {W : Set HePi} {π : HePi}
    (hRΦ : R.comap Φ = (closure W).map (MulAut.conj π).toMonoidHom)
    {M : Subgroup (Equiv.Perm (Fin 8330))}
    (hM : M = (closure ((fun w => (hePiEquivP w : Equiv.Perm (Fin 8330))) '' W)).map
      (MulAut.conj (hePiEquivP π : Equiv.Perm (Fin 8330))).toMonoidHom)
    (hMc : ∀ x ∈ M, x ≠ 1 → x ∈ conjClass heP (heGenPerm 0))
    (hMp : ⁅heP ⊓ centralizer (M : Set (Equiv.Perm (Fin 8330))),
      heP ⊓ centralizer (M : Set (Equiv.Perm (Fin 8330)))⁆ =
        heP ⊓ centralizer (M : Set (Equiv.Perm (Fin 8330))))
    (hMn : Nat.card ↥(heP ⊓ centralizer (M : Set (Equiv.Perm (Fin 8330)))) = 80640) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .He := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hePi_simple
  have hF := hQ.setting.frame
  have hinj : Function.Injective Φ :=
    injective_of_ne_one Φ (x := hePiZ) (by rw [hΦz]; exact hQ.z_ne_one)
  set H := Φ.range with hH
  set e : ↥H ≃* ↥heP := (MonoidHom.ofInjective hinj).symm.trans hePiEquivP
    with he
  set ψP : HePi →* Equiv.Perm (Fin 8330) :=
    heP.subtype.comp hePiEquivP.toMonoidHom with hψP
  have hT : HeEnd.transportHom e = ψP.comp (MonoidHom.ofInjective hinj).symm.toMonoidHom := rfl
  have heΦ : ∀ (a : HePi) (h : Φ a ∈ H), (e ⟨Φ a, h⟩ : Equiv.Perm (Fin 8330)) = ψP a := by
    intro a h
    have : (MonoidHom.ofInjective hinj).symm ⟨Φ a, h⟩ = a := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext (MonoidHom.ofInjective_apply hinj).symm
    simp [he, hψP, this]
  have hRM : (R.subgroupOf H).map (HeEnd.transportHom e) = M := by
    rw [hT, map_subgroupOf_range_eq, hRΦ, map_map_conj, MonoidHom.map_closure, hM]
    rfl
  have hzH : z ∈ H := hCΦ (mem_centralizer_singleton_iff.mpr rfl)
  have hEL : E ≤ AS76b.oUpperTwoPrime (normalizer (E : Set G)) :=
    le_oUpper_of_card le_normalizer (n := 6) (by rw [hF.cardE]; norm_num)
  have hRH : R ≤ H := (hF.R_le_E.trans hEL).trans hLΦ
  have hR1 : R ≠ ⊥ := by
    intro h
    have := hF.cardR
    rw [h, card_bot] at this
    omega
  have hz : ((e ⟨z, hzH⟩ : heP) : Equiv.Perm (Fin 8330)) ∈
      conjClass heP heT1P := by
    have h1 : (e ⟨z, hzH⟩ : Equiv.Perm (Fin 8330)) = heT1P := by
      have := heΦ hePiZ (hΦz ▸ hzH)
      simp only [hΦz] at this
      rw [this, hψP]
      exact hePiEquivP_z
    rw [h1]
    exact ⟨1, heP.one_mem, by group⟩
  have hR : ∀ (r : G) (hr : r ∈ R), r ≠ 1 →
      ((e ⟨r, hRH hr⟩ : heP) : Equiv.Perm (Fin 8330)) ∈
        conjClass heP
          (heGenPerm 0) := by
    intro r hr hr1
    refine hMc _ ?_ ?_
    · rw [← hRM]
      exact ⟨⟨r, hRH hr⟩, mem_subgroupOf.mpr hr, rfl⟩
    · intro h1
      have : e ⟨r, hRH hr⟩ = 1 := Subtype.ext h1
      rw [← map_one e] at this
      exact hr1 (congrArg Subtype.val (e.injective this))
  obtain ⟨hinv, hCr, hAp, hAc⟩ := HeEnd.he_facts e hzH hz hRH hR1 hR (by rw [hRM]; exact hMp)
    (by rw [hRM]; exact hMn)
  have htop := HeEnd.eq_top hQ hs hO2 hRA hS₁E hCE hCz hCΦ hLΦ hinv hCr hAp hAc
  exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop).symm).trans
    ((MonoidHom.ofInjective hinj).symm.trans hePiEquivHe)⟩

@[expose] def heRWordPi (k : ℕ) : HePi :=
  PresentedGroup.mk _ (FreeGroup.mk (ofCodes (heGenWordsR.getD k [])))

theorem heGenWordsR_letters : ∀ k < 2, ∀ l ∈ ofCodes (heGenWordsR.getD k []),
    (l.1 : ℕ) ≤ 4 ∨ (l.1 : ℕ) = 6 ∨ (l.1 : ℕ) = 7 := by
  decide

theorem sec4HeCase_of_cent
    {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hRc : ∀ d ∈ heP, ∀ x ∈ (closure {(hePiEquivP (heRWordPi 0) : Equiv.Perm (Fin 8330)),
        (hePiEquivP (heRWordPi 1) : Equiv.Perm (Fin 8330))}).map (MulAut.conj d).toMonoidHom,
      x ≠ 1 → x ∈ conjClass heP (heGenPerm 0))
    (hRp : ∀ d ∈ heP,
      let M := (closure {(hePiEquivP (heRWordPi 0) : Equiv.Perm (Fin 8330)),
        (hePiEquivP (heRWordPi 1) : Equiv.Perm (Fin 8330))}).map (MulAut.conj d).toMonoidHom
      ⁅heP ⊓ centralizer (M : Set (Equiv.Perm (Fin 8330))),
        heP ⊓ centralizer (M : Set (Equiv.Perm (Fin 8330)))⁆ =
        heP ⊓ centralizer (M : Set (Equiv.Perm (Fin 8330))))
    (hRn : ∀ d ∈ heP,
      let M := (closure {(hePiEquivP (heRWordPi 0) : Equiv.Perm (Fin 8330)),
        (hePiEquivP (heRWordPi 1) : Equiv.Perm (Fin 8330))}).map (MulAut.conj d).toMonoidHom
      Nat.card ↥(heP ⊓ centralizer (M : Set (Equiv.Perm (Fin 8330)))) = 80640) :
    Sec4HeCase := by
  intro G _ _ A R g E F S₁ Q z hQ hs hO2 hY h46 hNX hS₁ hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : HexaFacts := hexaFacts
  have hm : heModelCheck = true := he_modelCheck
  have hg : heGlueCheck = true := he_glueCheck
  have hM : HeModelFacts := heModelFacts_of hm hF
  have hset := hQ.setting
  have hFr := hset.frame
  obtain ⟨h46a, -⟩ := h46
  obtain ⟨hS₁c, hN, hEFS, hS₁I, hIE, hIF⟩ := sec4He_inputs hE16 h11 hM hQ
    (fun X hX => ⟨(h46a X hX).1, (h46a X hX).2.1⟩) hC
  have hCz := card_centralizer_eq hM hC
  have hz1 := hQ.z_ne_one
  have hzE : z ∈ E := z_mem_of_card hQ hQ.normE (h46a E (by simp)).2.2.2
  have hzF : z ∈ F := z_mem_of_card hQ hQ.normF (h46a F (by simp)).2.2.2
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hFr.elemE.2 x hx
  have hF2 : ∀ x ∈ F, x * x = 1 := fun x hx => by rw [← sq]; exact hFr.elemF.2 x hx
  obtain ⟨s, fC, hCz', hCB, hCE, hCF, hCEE, -⟩ := exists_normC hM hC hz1 hQ.le_centralizer hS₁c
    hN hEFS hFr.ne hIE hIF hE2 hFr.cardE hF2 hFr.cardF
  obtain ⟨ιE, ψE, hψEs, hψEk, hEeq, hER⟩ := hNX E (by simp)
  obtain ⟨ιF, ψF, hψFs, hψFk, hFeq, -⟩ := hNX F (by simp)
  obtain ⟨fE, -, -, hEP, hEB, -, hE23, cE, hcE⟩ := exists_normX_R hF hM ιE ψE hψEs hψEk hEeq
    hE2 hFr.cardE hzE hz1 hCz (hS₁I.trans inf_le_left) hS₁c (le_sup_right.trans hEFS)
    (hN.trans inf_le_right) hF2 hFr.cardF hFr.ne.symm hFr.R_le_E hER
  obtain ⟨fF, -, -, hFP, hFB, -, hF23, -⟩ := exists_normX hF hM ιF ψF hψFs hψFk hFeq hF2
    hFr.cardF hzF hz1 hCz (hS₁I.trans inf_le_right) hS₁c (le_sup_left.trans hEFS)
    (hN.trans inf_le_left) hE2 hFr.cardE hFr.ne
  obtain ⟨Φ, pN, hΦC, hΦE, hΦz, -, hΦw⟩ := exists_hePiHom hm hg hF s fC fE fF hCz' hCB hCE hCF
    hEP hEB hE23 hFP hFB hF23
  have := hePi_simple
  have hinj : Function.Injective Φ :=
    injective_of_ne_one Φ (x := hePiZ) (by rw [hΦz]; exact hz1)
  have hEL : E ≤ AS76b.oUpperTwoPrime (normalizer (E : Set G)) :=
    le_oUpper_of_card le_normalizer (n := 6) (by rw [hFr.cardE]; norm_num)
  have hw : ∀ k < 2, ∃ h : permOfArr 64 (hexaR0Gens.getD k #[]) ∈ heN0,
      Φ (heRWordPi k) = (fE (pN * ⟨_, h⟩ * pN⁻¹) : G) := by
    intro k hk
    obtain ⟨hw', he⟩ := hΦw _ (heGenWordsR_letters k hk)
    have heq := heGenWordsR_eval hg hk
    refine ⟨heq ▸ hw', ?_⟩
    have h1 : (⟨_, hw'⟩ : ↥heN0) = ⟨_, heq ▸ hw'⟩ := Subtype.ext heq
    rw [heRWordPi, he, h1]
  obtain ⟨π, hπ⟩ := comap_eq_conj Φ hinj fE hΦE hcE (hFr.R_le_E.trans hEL) (hw 0 (by norm_num))
    (hw 1 (by norm_num))
  have hCE' : centralizer (E : Set G) ≤ E :=
    centralizer_le_of_mulEquiv hzE ((hM.EC_le s).trans (hM.P12C_le s).2) fC hCEE (hM.cent_EC s)
  have hd := (hePiEquivP π).2
  exact isSporadic_of_hePiHom hQ hs hO2 (step16 hE16 h11 G A R g E F hFr hset.even).1
    (hN.trans inf_le_left) hCE' hCz Φ hΦz hΦC hΦE hπ (by rw [Set.image_pair]) (hRc _ hd)
    (hRp _ hd) (hRn _ hd)

end CFSG.ComponentClassification.AS81.HeTri
