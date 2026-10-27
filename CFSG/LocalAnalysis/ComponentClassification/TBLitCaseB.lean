module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitSwap
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCoreBasics
public import CFSG.LocalAnalysis.ComponentClassification.TBLitStepFour

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.UnbalancingLocal
open scoped commutatorElement Pointwise MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem conj_mem_gsFixedLayer {L : Subgroup X} {e g : X} (hgL : g ∈ normalizer (L : Set X))
    (hge : g * e = e * g) {x : X} (hx : x ∈ UnbalancedGS.gsFixedLayer L e) :
    g * x * g⁻¹ ∈ UnbalancedGS.gsFixedLayer L e := by
  set C := L ⊓ centralizer ({e} : Set X) with hC
  have hconj : g * e * g⁻¹ = e := by rw [hge]; group
  have hgC : g ∈ normalizer (C : Set X) := by
    rw [mem_normalizer_iff]
    intro x
    have he : x ∈ centralizer ({e} : Set X) ↔ g * x * g⁻¹ ∈ centralizer ({e} : Set X) := by
      rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
      constructor
      · intro h
        calc g * x * g⁻¹ * e = g * x * g⁻¹ * (g * e * g⁻¹) := by rw [hconj]
          _ = g * (x * e) * g⁻¹ := by group
          _ = g * (e * x) * g⁻¹ := by rw [h]
          _ = (g * e * g⁻¹) * (g * x * g⁻¹) := by group
          _ = e * (g * x * g⁻¹) := by rw [hconj]
      · intro h
        calc x * e = g⁻¹ * (g * x * g⁻¹ * (g * e * g⁻¹)) * g := by group
          _ = g⁻¹ * (g * x * g⁻¹ * e) * g := by rw [hconj]
          _ = g⁻¹ * (e * (g * x * g⁻¹)) * g := by rw [h]
          _ = g⁻¹ * ((g * e * g⁻¹) * (g * x * g⁻¹)) * g := by rw [hconj]
          _ = e * x := by group
    rw [hC, mem_inf, mem_inf, (mem_normalizer_iff.mp hgL x), he]
  have hchar : (pLayer C 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
  have hmap := map_mulAut_eq_of_characteristic (pLayer C 2) (C.normalizerMonoidHom ⟨g, hgC⟩)
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : C.normalizerMonoidHom ⟨g, hgC⟩ y ∈ pLayer C 2 := by
    rw [← hmap]
    exact mem_map_of_mem _ hy
  exact ⟨_, hy', rfl⟩

theorem mem_normalizer_gsFixedLayer {L : Subgroup X} {e g : X} (hgL : g ∈ normalizer (L : Set X))
    (hge : g * e = e * g) :
    g ∈ normalizer ((UnbalancedGS.gsFixedLayer L e : Subgroup X) : Set X) := by
  have hge' : g⁻¹ * e = e * g⁻¹ := (Commute.inv_left hge).eq
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_gsFixedLayer hgL hge hx, fun hx => ?_⟩
  have h1 := conj_mem_gsFixedLayer (inv_mem hgL) hge' hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1

omit [Finite X] in
theorem centralizer_mul_inf (γ ρ : X) :
    centralizer ({γ * ρ} : Set X) ⊓ centralizer ({ρ} : Set X) =
      centralizer ({γ} : Set X) ⊓ centralizer ({ρ} : Set X) := by
  ext x
  simp only [mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have h3 : x * γ * ρ = γ * x * ρ := by
      calc x * γ * ρ = x * (γ * ρ) := by group
        _ = γ * ρ * x := h1
        _ = γ * (ρ * x) := by group
        _ = γ * (x * ρ) := by rw [h2]
        _ = γ * x * ρ := by group
    exact mul_right_cancel h3
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    calc x * (γ * ρ) = x * γ * ρ := by group
      _ = γ * x * ρ := by rw [h1]
      _ = γ * (x * ρ) := by group
      _ = γ * (ρ * x) := by rw [h2]
      _ = γ * ρ * x := by group

omit [Finite X] in
theorem mem_normalizer_sup_conjugate {g : X} (hg : g * g = 1) (E : Subgroup X) :
    g ∈ normalizer ((E ⊔ conjugate E g : Subgroup X) : Set X) := by
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have h1 : E.map (MulAut.conj g).toMonoidHom = conjugate E g := by
    rw [conjugate, hginv]
  have h2 : (conjugate E g).map (MulAut.conj g).toMonoidHom = E := by
    rw [conjugate, hginv, Subgroup.map_map]
    have : ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g).toMonoidHom) = MonoidHom.id X := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      calc g * (g * x * g⁻¹) * g⁻¹ = (g * g) * x * (g * g)⁻¹ := by group
        _ = x := by rw [hg]; group
    rw [this, Subgroup.map_id]
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (E ⊔ conjugate E g).map (MulAut.conj g).toMonoidHom = E ⊔ conjugate E g
  rw [Subgroup.map_sup, h1, h2, sup_comm]

omit [Finite X] in
theorem conjugate_le_oddCentralizerCore {a ρ : X} (hρ : ρ ∈ centralizer ({a} : Set X))
    {E : Subgroup X} (hE : E ≤ oddCentralizerCore a) : conjugate E ρ ≤ oddCentralizerCore a := by
  intro x hx
  rw [UnbalancedLayer.mem_conjugate_iff] at hx
  have h1 := conj_mem_oddCentralizerCore (inv_mem hρ) (hE hx)
  rwa [show ρ⁻¹ * (ρ * x * ρ⁻¹) * ρ⁻¹⁻¹ = x by group] at h1

omit [Finite X] in
theorem mem_normalizer_conjugate_of_commute {M : Subgroup X} {b g : X}
    (hgM : g ∈ normalizer (M : Set X)) (hgb : g * b = b * g) :
    g ∈ normalizer ((conjugate M b : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff]
  intro x
  rw [UnbalancedLayer.mem_conjugate_iff, UnbalancedLayer.mem_conjugate_iff,
    (mem_normalizer_iff.mp hgM (b * x * b⁻¹))]
  have hgb' : b * g = g * b := hgb.symm
  have hgbi : g⁻¹ * b⁻¹ = b⁻¹ * g⁻¹ := (Commute.inv_inv (show Commute g b from hgb)).eq
  rw [show b * (g * x * g⁻¹) * b⁻¹ = g * (b * x * b⁻¹) * g⁻¹ by
    calc b * (g * x * g⁻¹) * b⁻¹ = (b * g) * x * (g⁻¹ * b⁻¹) := by group
      _ = (g * b) * x * (b⁻¹ * g⁻¹) := by rw [hgb', hgbi]
      _ = g * (b * x * b⁻¹) * g⁻¹ := by group]

theorem forall_mem_oddCoreIn_of_conjugate {C M : Subgroup X} (hMC : M ≤ C)
    {b g : X} (hbC : b ∈ C) (hgb : g * b = b * g)
    (hgM : g ∈ normalizer (M : Set X)) (hMbC : conjugate M b ≤ C)
    (hMbc : IsPComponent 2 ((conjugate M b).subgroupOf C))
    (h : ∀ x ∈ conjugate M b, ⁅x, g⁆ ∈ oddCoreIn (conjugate M b)) :
    ∀ m ∈ M, ⁅m, g⁆ ∈ oddCoreIn M := by
  intro m hm
  have hx : b⁻¹ * m * b ∈ conjugate M b := by
    rw [UnbalancedLayer.mem_conjugate_iff]
    rwa [show b * (b⁻¹ * m * b) * b⁻¹ = m by group]
  have h1 := UGSChain.map_pPrimeCore_le_of_isPComponent hMbC hMbc (h _ hx)
  have hCn : C ≤ normalizer ((oddCoreIn C : Subgroup X) : Set X) :=
    le_normalizer.trans (normalizer_le_normalizer_oddCoreIn C)
  have h2 := (mem_normalizer_iff.mp (hCn hbC) _).mp h1
  have hconj : b * g * b⁻¹ = g := by rw [show b * g = g * b from hgb.symm]; group
  have hconj' : b * g⁻¹ * b⁻¹ = g⁻¹ := by
    rw [show b * g⁻¹ = g⁻¹ * b from (Commute.inv_right (show Commute b g from hgb.symm)).eq]
    group
  have heq : b * ⁅b⁻¹ * m * b, g⁆ * b⁻¹ = ⁅m, g⁆ := by
    calc b * ⁅b⁻¹ * m * b, g⁆ * b⁻¹ = m * (b * g * b⁻¹) * m⁻¹ * (b * g⁻¹ * b⁻¹) := by
          simp only [commutatorElement_def]
          group
      _ = ⁅m, g⁆ := by rw [hconj, hconj', commutatorElement_def]
  rw [heq] at h2
  refine inf_le_oddCoreIn (odd_card_oddCoreIn C) (hMC.trans hCn) (mem_inf.mpr ⟨?_, h2⟩)
  exact commutator_le_of_le_normalizer (zpowers_le.mpr hgM)
    (commutator_mem_commutator hm (mem_zpowers g))

omit [Finite X] in
theorem mem_of_eq_mul_of_odd' {N : Subgroup X} {w n o : X} (hw : w ^ 2 = 1) (hn : n ∈ N)
    (hwo : w = n * o) (hodd : Odd (orderOf o)) (hnw : n * w = w * n) : w ∈ N := by
  refine mem_of_eq_mul_of_odd hw hn hwo hodd ?_
  have ho : o = n⁻¹ * w := by rw [hwo]; group
  have hnw' : n⁻¹ * w = w * n⁻¹ := (Commute.inv_left (show Commute n w from hnw)).eq
  rw [ho]
  calc w * (n⁻¹ * w) = (w * n⁻¹) * w := by group
    _ = (n⁻¹ * w) * w := by rw [hnw']

theorem actsProperly_fixedLayer {a ρ : X} (ha : orderOf a = 2) (hρ : ρ ^ 2 = 1)
    (haρ : a * ρ = ρ * a) {L F : Subgroup X} (hFa : F ≤ oddCentralizerCore a)
    (hρF : ρ ∈ normalizer (F : Set X)) (haL : a ∈ normalizer (L : Set X))
    (hFL : F ≤ normalizer (L : Set X)) (hρL : ρ ∈ normalizer (L : Set X))
    (hρtriv : ∀ l ∈ L, ⁅l, ρ⁆ ∈ oddCoreIn L)
    (hcov : (UnbalancedGS.gsFixedLayer L ρ : Set X) * (oddCoreIn L : Set X) = L)
    (hcore : oddCoreIn (UnbalancedGS.gsFixedLayer L ρ) =
      UnbalancedGS.gsFixedLayer L ρ ⊓ oddCoreIn L)
    (hanL : ¬ ∀ l ∈ L, ⁅l, a⁆ ∈ oddCoreIn L) (henL : ∃ e ∈ F, ¬ ∀ l ∈ L, ⁅l, e⁆ ∈ oddCoreIn L) :
    ActsProperly a (F ⊓ centralizer ({ρ} : Set X)) (UnbalancedGS.gsFixedLayer L ρ)
      (oddCoreIn (UnbalancedGS.gsFixedLayer L ρ)) := by
  have hTL : UnbalancedGS.gsFixedLayer L ρ ≤ L :=
    (UnbalancedGS.gsFixedLayer_le_inf L ρ).trans inf_le_left
  have hFodd : Odd (Nat.card F) := Nat.coprime_two_left.mp
    ((coprime_card_oddCentralizerCore a).coprime_dvd_right (card_dvd_of_le hFa))
  have hEodd : Odd (Nat.card (F ⊓ centralizer ({ρ} : Set X) : Subgroup X)) :=
    Odd.of_dvd_nat hFodd (card_dvd_of_le inf_le_left)
  have hFC : ∀ x ∈ F, x * a = a * x := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hFa hx
    exact mem_centralizer_singleton_iff.mp y.2
  have haE : a ∈ normalizer ((F ⊓ centralizer ({ρ} : Set X) : Subgroup X) : Set X) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rwa [show a * x * a⁻¹ = x by rw [← hFC x (mem_inf.mp hx).1]; group]
    · intro hx
      have h1 : a * x * a⁻¹ ∈ F := (mem_inf.mp hx).1
      have h2 := hFC _ h1
      have hxy : x = a * x * a⁻¹ := by
        calc x = a⁻¹ * ((a * x * a⁻¹) * a) := by group
          _ = a⁻¹ * (a * (a * x * a⁻¹)) := by rw [h2]
          _ = a * x * a⁻¹ := by group
      rw [hxy]
      exact hx
  have haT := mem_normalizer_gsFixedLayer haL haρ
  have hET : F ⊓ centralizer ({ρ} : Set X) ≤
      normalizer ((UnbalancedGS.gsFixedLayer L ρ : Subgroup X) : Set X) := fun e he =>
    mem_normalizer_gsFixedLayer (hFL (mem_inf.mp he).1)
      (mem_centralizer_singleton_iff.mp (mem_inf.mp he).2)
  refine actsProperly_of_involution ha haE hEodd haT hET ?_ ?_
  · exact fun h => hanL ((actsTrivially_iff_of_cover hTL hcov hcore haL haT).mpr h)
  · obtain ⟨e₀, he₀, hne₀⟩ := henL
    obtain ⟨l₀, hl₀, hl₀e⟩ : ∃ l ∈ L, ⁅l, e₀⁆ ∉ oddCoreIn L := by
      by_contra hall
      exact hne₀ fun l hl => by
        by_contra h
        exact hall ⟨l, hl, h⟩
    obtain ⟨e, he, l, hl, hle⟩ := exists_centralizer_mem_nontrivial hρ hρF hFodd hρL hFL
      hρtriv ⟨e₀, he₀, l₀, hl₀, hl₀e⟩
    refine ⟨e, he, ?_⟩
    have heT := hET he
    by_contra hall
    apply hle
    refine ((actsTrivially_iff_of_cover hTL hcov hcore (hFL (mem_inf.mp he).1) heT).mpr
      (fun s hs => ?_)) l hl
    by_contra h
    exact hall ⟨s, hs, h⟩

theorem caseB_star (hI : TBInputs) (hX : TBSetting X) {a b γ : X} {S E : Subgroup X}
    (hC : CoreConfig a b γ S E) {M : Subgroup X} (hM : M ≤ centralizer ({γ} : Set X))
    (hMc : IsPComponent 2 (M.subgroupOf (centralizer ({γ} : Set X))))
    (hSK : S ≤ M ⊔ conjugate M b)
    (hSKc : IsPComponent 2 (S.subgroupOf ((M ⊔ conjugate M b) ⊓ centralizer ({b} : Set X))))
    (haM : a ∈ normalizer (M : Set X)) (hEM : E ≤ normalizer (M : Set X))
    (hanM : ¬ ∀ m ∈ M, ⁅m, a⁆ ∈ oddCoreIn M) (henM : ∃ e ∈ E, ¬ ∀ m ∈ M, ⁅m, e⁆ ∈ oddCoreIn M)
    (hne : M ≠ conjugate M b) :
    ∃ (δ₁ δ₂ : X) (N₁ N₂ E' : Subgroup X), StarConfig a δ₁ δ₂ N₁ N₂ E' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p, n, hpf, hp2, hn, ⟨eS⟩⟩ := hC.hSL
  set Cγ := centralizer ({γ} : Set X) with hCγ
  have hbC : b ∈ Cγ := mem_centralizer_singleton_iff.mpr hC.hbγ
  have haC : a ∈ Cγ := mem_centralizer_singleton_iff.mpr hC.haγ
  have hγC : γ ∈ Cγ := mem_centralizer_singleton_iff.mpr rfl
  have hb2 : b * b = 1 := by rw [← pow_two, ← hC.hb, pow_orderOf_eq_one]
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have ha2 : a ^ 2 = 1 := by rw [← hC.ha, pow_orderOf_eq_one]
  obtain ⟨hM₂, hM₂c⟩ := UGSChain.conjugate_isPComponent_centralizer hC.hbγ hM hMc
  have hSC : S ≤ Cγ := hC.hS.trans inf_le_right
  have hSfix : UnbalancedGS.gsFixedLayer (M ⊔ conjugate M b) b = S :=
    (UGSChain.orbit_fixed_component_comparison hC.hb hC.hbγ hM hMc
      (le_inf hSK (hC.hS.trans inf_le_left)) hSKc).2.1 hne
  set t : Cγ := ⟨b, hbC⟩ with ht
  have htt : t * t = 1 := Subtype.ext hb2
  have hne' : M.subgroupOf Cγ ≠ (conjugate M b).subgroupOf Cγ := by
    intro h
    apply hne
    rwa [subgroupOf_inj, inf_eq_left.mpr hM, inf_eq_left.mpr hM₂] at h
  have hL₂ : (conjugate M b).subgroupOf Cγ = (M.subgroupOf Cγ).map (MulAut.conj t).toMonoidHom := by
    ext x
    rw [mem_map_equiv, mem_subgroupOf, mem_subgroupOf, MulAut.conj_symm_apply,
      UnbalancedLayer.mem_conjugate_iff]
    change b * (x : X) * b⁻¹ ∈ M ↔ b⁻¹ * (x : X) * b ∈ M
    rw [hbinv]
  have hT : S.subgroupOf Cγ =
      UnbalancedGS.gsFixedLayer (M.subgroupOf Cγ ⊔ (conjugate M b).subgroupOf Cγ) t := by
    rw [← hSfix, UnbalancingLocal.Correspondence.gsFixedLayer_subgroupOf (sup_le hM hM₂) hbC,
      subgroupOf_sup hM hM₂]
  have eT : S.subgroupOf Cγ ⧸ pPrimeCore 2 (S.subgroupOf Cγ) ≃* SL(2, GaloisField p n) :=
    (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe hSC)).trans eS
  have hSq := (isPComponent_data hC.hS hC.hSc).2.2
  have h5 : 5 ≤ p ^ n :=
    five_le_of_isQuasisimple_sl hp2 hn (LocalCores.isQuasisimple_of_mulEquiv eS hSq)
  obtain ⟨⟨eA⟩, hAB1, z, hzA, hz2, hzc, hzuniq, hπγ⟩ := swap_analysis hI.griessTable
    hI.griessCovers htt hMc hM₂c hne' hL₂ hp2 h5 hT eT (g := ⟨γ, hγC⟩) hC.hγS
    (fun x hx => Subtype.ext (mem_centralizer_singleton_iff.mp (hC.hS hx).2).symm)
    (by rw [Subgroup.orderOf_mk]; exact hC.hγ)
  set π := QuotientGroup.mk' (pPrimeCore 2 Cγ) with hπ
  have hAcomp : IsComponent ((M.subgroupOf Cγ).map π) :=
    (UnbalancingLocal.Correspondence.image_components hMc hM₂c hne').1
  have hAcore := UnbalancingLocal.Correspondence.pPrimeCore_eq_bot_of_isComponent hAcomp
  obtain ⟨eL, -⟩ := CatalogueBPrimeJoin.exists_restrict_core_quotient_equiv (p := 2) π
    (M.subgroupOf Cγ) (UnbalancingLocal.Correspondence.not_two_dvd_card_ker_restrict _)
  let eM : M ⧸ pPrimeCore 2 M ≃* SL(2, GaloisField p n) :=
    (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe hM).symm).trans
      (eL.trans ((QuotientGroup.quotientMulEquivOfEq hAcore).trans
        (QuotientGroup.quotientBot.trans eA)))
  let eM₂ : conjugate M b ⧸ pPrimeCore 2 (conjugate M b) ≃* SL(2, GaloisField p n) :=
    (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      ((MulAut.conj b⁻¹).subgroupMap M).symm).trans eM
  have hOin : ∀ {N : Subgroup X}, N ≤ Cγ → ∀ x ∈ N, x ∈ oddCoreIn Cγ → x ∈ oddCoreIn N :=
    fun hN x hxN hxO => inf_le_oddCoreIn (odd_card_oddCoreIn Cγ)
      (hN.trans (le_normalizer.trans (normalizer_le_normalizer_oddCoreIn Cγ)))
      (mem_inf.mpr ⟨hxN, hxO⟩)
  have hπO : ∀ y : Cγ, π y = 1 ↔ (y : X) ∈ oddCoreIn Cγ := by
    intro y
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨fun h => ⟨y, h, rfl⟩, fun ⟨y', hy', hyy'⟩ => by rwa [← Subtype.ext hyy']⟩
  obtain ⟨z', hz'L, hz'z⟩ := hzA
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have haL : (⟨a, haC⟩ : Cγ) ∈ normalizer (M.subgroupOf Cγ : Set Cγ) :=
    UnbalancedLayer.mem_normalizer_subgroupOf_of_mem haM
  have haA := UnbalancedLayer.map_mem_normalizer π haL
  have hazA : π ⟨a, haC⟩ * z * (π ⟨a, haC⟩)⁻¹ = z := by
    have hmem : π ⟨a, haC⟩ * z * (π ⟨a, haC⟩)⁻¹ ∈ (M.subgroupOf Cγ).map π :=
      (mem_normalizer_iff.mp haA z).mp (hz'z ▸ mem_map_of_mem π hz'L)
    have hcen : ∀ x ∈ (M.subgroupOf Cγ).map π,
        π ⟨a, haC⟩ * z * (π ⟨a, haC⟩)⁻¹ * x = x * (π ⟨a, haC⟩ * z * (π ⟨a, haC⟩)⁻¹) := by
      intro x hx
      have hx' : (π ⟨a, haC⟩)⁻¹ * x * π ⟨a, haC⟩ ∈ (M.subgroupOf Cγ).map π := by
        have h1 := (mem_normalizer_iff.mp (inv_mem haA) x).mp hx
        rwa [inv_inv] at h1
      have h2 := hzc _ hx'
      calc π ⟨a, haC⟩ * z * (π ⟨a, haC⟩)⁻¹ * x
          = π ⟨a, haC⟩ * (z * ((π ⟨a, haC⟩)⁻¹ * x * π ⟨a, haC⟩)) * (π ⟨a, haC⟩)⁻¹ := by group
        _ = π ⟨a, haC⟩ * (((π ⟨a, haC⟩)⁻¹ * x * π ⟨a, haC⟩) * z) * (π ⟨a, haC⟩)⁻¹ := by rw [h2]
        _ = x * (π ⟨a, haC⟩ * z * (π ⟨a, haC⟩)⁻¹) := by group
    rcases hzuniq _ hmem hcen with h | h
    · exact absurd (conj_eq_one_iff.mp h) hz1
    · exact h
  have hOMn : ((oddCoreIn M).subgroupOf M).Normal := by
    rw [show (oddCoreIn M).subgroupOf M = pPrimeCore 2 M from
      comap_map_eq_self_of_injective M.subtype_injective _]
    infer_instance
  have hz'M : (z' : X) ∈ M := hz'L
  have hzsq : z ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by simp [hz2])
  obtain ⟨ρ, hρM, hρ2, hρa, hρz⟩ := exists_involution_lift (oddCoreIn_le M) hOMn
    (odd_card_oddCoreIn M) ha2 (normalizer_le_normalizer_oddCoreIn M haM) hz'M
    (by
      refine hOin hM _ (pow_mem hz'M 2) ?_
      change ((z' ^ 2 : Cγ) : X) ∈ oddCoreIn Cγ
      rw [← hπO, map_pow, hz'z, hzsq])
    (by
      intro h
      apply hz1
      rw [← hz'z, hπO]
      exact UGSChain.map_pPrimeCore_le_of_isPComponent hM hMc h)
    (by
      refine hOin hM _ (mul_mem (inv_mem hz'M) ((mem_normalizer_iff.mp haM _).mp hz'M)) ?_
      change (((z'⁻¹ * (⟨a, haC⟩ * z' * (⟨a, haC⟩ : Cγ)⁻¹)) : Cγ) : X) ∈ oddCoreIn Cγ
      rw [← hπO, map_mul, map_inv, map_mul, map_mul, map_inv, hz'z, hazA, inv_mul_cancel])
  have hρC : ρ ∈ Cγ := hM hρM
  have hπρ : π ⟨ρ, hρC⟩ = z := by
    have h1 : ((⟨ρ, hρC⟩⁻¹ * z' : Cγ) : X) ∈ oddCoreIn Cγ :=
      UGSChain.map_pPrimeCore_le_of_isPComponent hM hMc hρz
    rw [← hπO, map_mul, map_inv, hz'z, inv_mul_eq_one] at h1
    exact h1
  obtain ⟨-, -, -, hABcomm⟩ := UnbalancingLocal.Correspondence.image_components hMc hM₂c hne'
  have hzt : π t * z * (π t)⁻¹ ∈ ((conjugate M b).subgroupOf Cγ).map π := by
    refine ⟨t * z' * t⁻¹, ?_, ?_⟩
    · change b * (z' : X) * b⁻¹ ∈ conjugate M b
      rw [UnbalancedLayer.mem_conjugate_iff]
      rwa [show b * (b * (z' : X) * b⁻¹) * b⁻¹ = (b * b) * z' * (b * b)⁻¹ by group, hb2,
        one_mul, inv_one, mul_one]
    · rw [map_mul, map_mul, map_inv, hz'z]
  have hρρ : ρ * ρ = 1 := by rw [← pow_two, ← hρ2, pow_orderOf_eq_one]
  have hγρ : γ * ρ = ρ * γ := (mem_centralizer_singleton_iff.mp hρC).symm
  have hγρC : γ * ρ ∈ Cγ := mul_mem hγC hρC
  have hπγρ : π ⟨γ * ρ, hγρC⟩ = π t * z * (π t)⁻¹ := by
    have h1 : (⟨γ * ρ, hγρC⟩ : Cγ) = ⟨γ, hγC⟩ * ⟨ρ, hρC⟩ := rfl
    rw [h1, map_mul, hπγ, hπρ]
    have hc := hABcomm z (hz'z ▸ mem_map_of_mem π hz'L) _ hzt
    calc z * (π t * z * (π t)⁻¹) * z = (π t * z * (π t)⁻¹) * z * z := by rw [hc]
      _ = π t * z * (π t)⁻¹ * (z * z) := by group
      _ = π t * z * (π t)⁻¹ := by rw [← pow_two, hzsq, mul_one]
  have hγρ2 : orderOf (γ * ρ) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · have hγsq : γ ^ 2 = 1 := by rw [← hC.hγ, pow_orderOf_eq_one]
      have hρsq : ρ ^ 2 = 1 := by rw [← hρ2, pow_orderOf_eq_one]
      rw [(Commute.mul_pow (show Commute γ ρ from hγρ)), hγsq, hρsq, one_mul]
    · intro h1
      have h2 : π ⟨γ * ρ, hγρC⟩ = 1 := by
        rw [show (⟨γ * ρ, hγρC⟩ : Cγ) = 1 from Subtype.ext h1, map_one]
      rw [hπγρ, conj_eq_one_iff] at h2
      exact hz1 h2
  have hρtriv : ∀ {N : Subgroup X}, N ≤ Cγ →
      (∀ x ∈ N, ∀ hx : x ∈ Cγ, π ⟨x, hx⟩ * z = z * π ⟨x, hx⟩) →
      ∀ k ∈ N, k⁻¹ * ρ⁻¹ * k * ρ ∈ oddCoreIn Cγ := by
    intro N hN hcomm k hk
    have h1 : ((⟨k, hN hk⟩⁻¹ * ⟨ρ, hρC⟩⁻¹ * ⟨k, hN hk⟩ * ⟨ρ, hρC⟩ : Cγ) : X) ∈ oddCoreIn Cγ := by
      rw [← hπO, map_mul, map_mul, map_mul, map_inv, map_inv, hπρ, mul_assoc _ (π ⟨k, hN hk⟩) z,
        hcomm k hk (hN hk)]
      group
    exact h1
  have hMz : ∀ x ∈ M, ∀ hx : x ∈ Cγ, π ⟨x, hx⟩ * z = z * π ⟨x, hx⟩ :=
    fun x hx hxC => (hzc _ (mem_map_of_mem π (show (⟨x, hxC⟩ : Cγ) ∈ M.subgroupOf Cγ from hx))).symm
  have hM₂z : ∀ x ∈ conjugate M b, ∀ hx : x ∈ Cγ, π ⟨x, hx⟩ * z = z * π ⟨x, hx⟩ :=
    fun x hx hxC => (hABcomm z (hz'z ▸ mem_map_of_mem π hz'L) _
      (mem_map_of_mem π (show (⟨x, hxC⟩ : Cγ) ∈ (conjugate M b).subgroupOf Cγ from hx))).symm
  have hconj1 : ∀ L : Subgroup X, conjugate L 1 = L := fun L =>
    UnbalancedLayer.conjugate_eq_of_mem_normalizer (one_mem _)
  have hρZ : ρ ∉ center X := hX.not_mem_center hρ2
  have h1γ : (1 : X) * γ = γ * 1 := by group
  obtain ⟨hρNM, -, hρtM, -, hN₁, hN₁c, -, -, hN₁cov, hN₁core, φ₁, -⟩ :=
    UGSChain.kProper_core_trivial_orbit_fixed_layer_containment_of_schreier (a := 1)
      hI.schreier hX.kProper hC.hγ hρ2 h1γ hγρ hρZ hM hMc (fun k hk => by
        rw [hconj1, sup_idem] at hk
        exact hρtriv hM hMz k hk)
  obtain ⟨hρNM₂, -, hρtM₂, -, hN₂, hN₂c, -, -, hN₂cov, hN₂core, φ₂, -⟩ :=
    UGSChain.kProper_core_trivial_orbit_fixed_layer_containment_of_schreier (a := 1)
      hI.schreier hX.kProper hC.hγ hρ2 h1γ hγρ hρZ hM₂ hM₂c (fun k hk => by
        rw [hconj1, sup_idem] at hk
        exact hρtriv hM₂ hM₂z k hk)
  have hCC := centralizer_mul_inf γ ρ
  have hρsq : ρ ^ 2 = 1 := by rw [← hρ2, pow_orderOf_eq_one]
  have hoddO : ∀ {N : Subgroup X} {o : X}, o ∈ oddCoreIn N → Odd (orderOf o) := by
    intro N o ho
    exact Odd.of_dvd_nat (odd_card_oddCoreIn N)
      (by rw [← Subgroup.orderOf_mk o ho]; exact orderOf_dvd_natCard _)
  have hρN₁ : ρ ∈ UnbalancedGS.gsFixedLayer M ρ := by
    have h1 : ρ ∈ ((UnbalancedGS.gsFixedLayer M ρ : Set X) * (oddCoreIn M : Set X)) := by
      rw [hN₁cov]
      exact hρM
    obtain ⟨n₁, hn₁, o₁, ho₁, hρeq⟩ := h1
    exact mem_of_eq_mul_of_odd' hρsq hn₁ hρeq.symm (hoddO ho₁)
      (mem_centralizer_singleton_iff.mp (hN₁ hn₁).2)
  have hγρN₂ : γ * ρ ∈ UnbalancedGS.gsFixedLayer (conjugate M b) ρ := by
    obtain ⟨y, hy, hyeq⟩ := hπγρ ▸ hzt
    have ho₀ : ((y⁻¹ * ⟨γ * ρ, hγρC⟩ : Cγ) : X) ∈ oddCoreIn Cγ := by
      rw [← hπO, map_mul, map_inv, hyeq, inv_mul_cancel]
    have hyM₂ : (y : X) ∈ ((UnbalancedGS.gsFixedLayer (conjugate M b) ρ : Set X) *
        (oddCoreIn (conjugate M b) : Set X)) := by
      rw [hN₂cov]
      exact hy
    obtain ⟨n₂, hn₂, o₂, ho₂, hyeq'⟩ := hyM₂
    have ho' : o₂ * ((y⁻¹ * ⟨γ * ρ, hγρC⟩ : Cγ) : X) ∈ oddCoreIn Cγ :=
      mul_mem (UGSChain.map_pPrimeCore_le_of_isPComponent hM₂ hM₂c ho₂) ho₀
    refine mem_of_eq_mul_of_odd' ?_ hn₂ ?_ (hoddO ho') ?_
    · rw [← hγρ2, pow_orderOf_eq_one]
    · have hyeq'' : n₂ * o₂ = (y : X) := hyeq'
      rw [← mul_assoc, hyeq'']
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    · have hn₂γ := mem_centralizer_singleton_iff.mp (hN₂ hn₂).1
      have hn₂ρ := mem_centralizer_singleton_iff.mp (hN₂ hn₂).2
      calc n₂ * (γ * ρ) = (n₂ * γ) * ρ := by group
        _ = (γ * n₂) * ρ := by rw [hn₂γ]
        _ = γ * (n₂ * ρ) := by group
        _ = γ * (ρ * n₂) := by rw [hn₂ρ]
        _ = γ * ρ * n₂ := by group
  have hρaC : ρ ∈ centralizer ({a} : Set X) := mem_centralizer_singleton_iff.mpr hρa
  set F := E ⊔ conjugate E ρ with hF
  have hFa : F ≤ oddCentralizerCore a :=
    sup_le hC.hEa (conjugate_le_oddCentralizerCore hρaC hC.hEa)
  have hρF : ρ ∈ normalizer (F : Set X) := mem_normalizer_sup_conjugate hρρ E
  have hρMn : ρ ∈ normalizer (M : Set X) := le_normalizer hρM
  have hconjN : ∀ {N : Subgroup X}, E ≤ normalizer (N : Set X) → ρ ∈ normalizer (N : Set X) →
      F ≤ normalizer (N : Set X) := by
    intro N hEN hρN
    refine sup_le hEN ?_
    intro x hx
    rw [UnbalancedLayer.mem_conjugate_iff] at hx
    have h1 := mul_mem (mul_mem (inv_mem hρN) (hEN hx)) hρN
    rwa [show ρ⁻¹ * (ρ * x * ρ⁻¹) * ρ = x by group] at h1
  have hEb : ∀ e ∈ E, e * b = b * e := fun e he => mem_centralizer_singleton_iff.mp (hC.hE he).1
  have hEM₂ : E ≤ normalizer ((conjugate M b : Subgroup X) : Set X) := fun e he =>
    mem_normalizer_conjugate_of_commute (hEM he) (hEb e he)
  have hρM₂n : ρ ∈ normalizer ((conjugate M b : Subgroup X) : Set X) := by
    have hMle : M.subgroupOf Cγ ≤ pLayer Cγ 2 := le_sSup hMc
    have hρL : ρ ∈ (pLayer Cγ 2).map Cγ.subtype :=
      ⟨⟨ρ, hρC⟩, hMle (show (⟨ρ, hρC⟩ : Cγ) ∈ M.subgroupOf Cγ from hρM), rfl⟩
    exact UGSChain.map_pLayer_le_normalizer hM₂ hM₂c hρL
  have haM₂ := mem_normalizer_conjugate_of_commute haM hC.hab
  have hanM₂ : ¬ ∀ x ∈ conjugate M b, ⁅x, a⁆ ∈ oddCoreIn (conjugate M b) := fun h =>
    hanM (forall_mem_oddCoreIn_of_conjugate hM hbC hC.hab haM hM₂ hM₂c h)
  obtain ⟨e₀, he₀, hne₀⟩ := henM
  have hne₀₂ : ¬ ∀ x ∈ conjugate M b, ⁅x, e₀⁆ ∈ oddCoreIn (conjugate M b) := fun h =>
    hne₀ (forall_mem_oddCoreIn_of_conjugate hM hbC (hEb e₀ he₀) (hEM he₀) hM₂ hM₂c h)
  have hρtriv' : ∀ {N : Subgroup X}, ρ ∈ normalizer (N : Set X) →
      (∀ l ∈ N, l⁻¹ * ρ⁻¹ * l * ρ ∈ oddCoreIn N) → ∀ l ∈ N, ⁅l, ρ⁆ ∈ oddCoreIn N :=
    fun hρN h => (forall_commutator_mem_iff hρN).mpr h
  have hprop₁ := actsProperly_fixedLayer hC.ha hρsq hρa.symm hFa hρF haM (hconjN hEM hρMn) hρMn
    (hρtriv' hρMn hρtM) hN₁cov hN₁core hanM ⟨e₀, mem_sup_left he₀, hne₀⟩
  have hprop₂ := actsProperly_fixedLayer hC.ha hρsq hρa.symm hFa hρF haM₂ (hconjN hEM₂ hρM₂n)
    hρM₂n (hρtriv' hρM₂n hρtM₂) hN₂cov hN₂core hanM₂ ⟨e₀, mem_sup_left he₀, hne₀₂⟩
  refine ⟨ρ, γ * ρ, UnbalancedGS.gsFixedLayer M ρ, UnbalancedGS.gsFixedLayer (conjugate M b) ρ,
    F ⊓ centralizer ({ρ} : Set X), ⟨hC.ha, hρ2, hγρ2, ?_, hρa.symm, ?_, ?_, ?_, ?_, ?_, hρN₁, hγρN₂,
    ⟨p, n, hpf, hp2, hn, ⟨φ₁.trans eM⟩, ⟨φ₂.trans eM₂⟩⟩, inf_le_left.trans hFa, ?_, hprop₁,
    hprop₂⟩⟩
  · calc ρ * (γ * ρ) = (ρ * γ) * ρ := by group
      _ = (γ * ρ) * ρ := by rw [← hγρ]
  · calc a * (γ * ρ) = (a * γ) * ρ := by group
      _ = (γ * a) * ρ := by rw [hC.haγ]
      _ = γ * (a * ρ) := by group
      _ = γ * (ρ * a) := by rw [← hρa]
      _ = γ * ρ * a := by group
  · rw [hCC]
    exact hN₁
  · rw [hCC]
    exact hN₁c
  · rw [hCC]
    exact hN₂
  · rw [hCC]
    exact hN₂c
  · rw [hCC]
    refine le_inf (inf_le_left.trans (sup_le (hC.hE.trans inf_le_right) ?_)) inf_le_right
    intro x hx
    rw [UnbalancedLayer.mem_conjugate_iff] at hx
    have h1 := mul_mem (mul_mem (inv_mem hρC) ((hC.hE hx).2)) hρC
    rwa [show ρ⁻¹ * (ρ * x * ρ⁻¹) * ρ = x by group] at h1

end CFSG.ComponentClassification.TBLit
