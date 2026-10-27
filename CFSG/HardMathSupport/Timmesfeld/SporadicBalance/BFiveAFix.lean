module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BTwoBLocal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2FiveRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster.GMS
  CFSG.Blueprint.NativeSporadic CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.SpinLattice
  CFSG.Monster.Spin CFSG.Monster.Code CFSG.Monster.Griess

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Generic

variable {G : Type*} [Group G]

theorem card_le_two_of_map {α : Type*} [Finite α] {v : α → G} (hv : Function.Injective v) {a : G}
    (h : ∀ x, v x = 1 ∨ v x = a) : Nat.card α ≤ 2 := by
  classical
  have hinj : Function.Injective fun x : α => decide (v x = a) := by
    intro x y hxy
    apply hv
    simp only at hxy
    rcases h x with hx | hx <;> rcases h y with hy | hy
    · rw [hx, hy]
    · by_cases ha : (1 : G) = a
      · rw [hx, hy, ha]
      · rw [hx, hy] at hxy
        simp [ha] at hxy
    · by_cases ha : (1 : G) = a
      · rw [hx, hy, ha]
      · rw [hx, hy] at hxy
        simp [ha] at hxy
    · rw [hx, hy]
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

theorem mem_ker_of_local_quotient [Finite G] {p : ℕ} (hp : p.Prime) {K : Type*} [Group K]
    {x : G} (F : ↥(Subgroup.centralizer ({x} : Set G)) →* K) (hF : Function.Surjective F)
    (hN : Nat.Coprime p (Nat.card F.ker)) (hK : OPrimeCoreTrivialAt p K) {s : G}
    (hs : orderOf s = p) (hsx : s ∈ Subgroup.centralizer ({x} : Set G)) {q : G}
    (hq : q ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)))
    (hqx : q ∈ Subgroup.centralizer ({x} : Set G)) :
    (⟨q, hqx⟩ : ↥(Subgroup.centralizer ({x} : Set G))) ∈ F.ker := by
  let e := QuotientGroup.quotientKerEquivOfSurjective F hF
  set Y := GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)) ⊓
    Subgroup.centralizer ({x} : Set G) with hY
  have hYH : Y ≤ Subgroup.centralizer ({x} : Set G) := inf_le_right
  have hYs : ∀ y ∈ Y, y * s = s * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.1 (GLAPPrimeCoreOf_le _ hy.1)
  have hYn : ∀ g ∈ Subgroup.centralizer ({x} : Set G), g * s = s * g → ∀ y ∈ Y,
      g * y * g⁻¹ ∈ Y := fun g hg hgs y hy =>
    ⟨GLAPPrimeCoreOf_conj_mem g (Subgroup.mem_centralizer_singleton_iff.2 hgs) y hy.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hy.2) (Subgroup.inv_mem _ hg)⟩
  have hYc : Nat.Coprime p (Nat.card Y) :=
    (coprime_card_GLAPPrimeCoreOf hp _).coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  exact mem_of_oPrimeCoreTrivial_quotient hp (H := Subgroup.centralizer ({x} : Set G))
    (N := F.ker) hN e hK hsx hs hYH hYs hYn hYc q ⟨hq, hqx⟩

theorem mem_centralizer_singleton_symm {a b : G} (h : a ∈ Subgroup.centralizer ({b} : Set G)) :
    b ∈ Subgroup.centralizer ({a} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
  exact h.symm

theorem conj_mem_centralizer_conj {w g : G} (c : G) (hg : g ∈ Subgroup.centralizer ({w} : Set G)) :
    c * g * c⁻¹ ∈ Subgroup.centralizer ({c * w * c⁻¹} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
  calc c * g * c⁻¹ * (c * w * c⁻¹) = c * (g * w) * c⁻¹ := by group
    _ = c * (w * g) * c⁻¹ := by rw [hg]
    _ = c * w * c⁻¹ * (c * g * c⁻¹) := by group

theorem card_gLAPPrimeCoreOf_inf_le_conj [Finite G] {p : ℕ} (c y w : G) :
    Nat.card ↥(GLAPPrimeCoreOf p (Subgroup.centralizer ({y} : Set G)) ⊓
      Subgroup.centralizer ({w} : Set G)) ≤
    Nat.card ↥(GLAPPrimeCoreOf p (Subgroup.centralizer ({c * y * c⁻¹} : Set G)) ⊓
      Subgroup.centralizer ({c * w * c⁻¹} : Set G)) := by
  refine Nat.card_le_card_of_injective
    (fun q => ⟨c * (q : G) * c⁻¹, conj_mem_gLAPPrimeCoreOf_centralizer c y (q : G) q.2.1,
      conj_mem_centralizer_conj c q.2.2⟩) ?_
  intro a b hab
  have h1 : c * (a : G) * c⁻¹ = c * (b : G) * c⁻¹ := congrArg Subtype.val hab
  apply Subtype.ext
  simpa using h1

theorem card_le_card_map_of_coprime_ker [Finite G] {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    {K : Type*} [Group K] [Finite K] (F : ↥H →* K) (hN : Nat.Coprime p (Nat.card F.ker))
    {R : Subgroup G}
    (hRp : IsPGroup p R) (hRH : R ≤ H) : Nat.card R ≤ Nat.card ((R.subgroupOf H).map F) := by
  set R1 := R.subgroupOf H with hR1
  have hR1p : IsPGroup p R1 := hRp.comap_of_injective H.subtype H.subtype_injective
  have hR1card : Nat.card R1 = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv
  have hbot : F.ker ⊓ R1 = ⊥ := inf_eq_bot_of_coprime_isPGroup hp hN hR1p
  have hinj : Function.Injective fun a : ↥R1 => (⟨F a, a, a.2, rfl⟩ : ↥(R1.map F)) := by
    intro a b hab
    have h1 : F a = F b := congrArg Subtype.val hab
    have h2k : (a : ↥H)⁻¹ * b ∈ F.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have h2 : (a : ↥H)⁻¹ * b ∈ F.ker ⊓ R1 :=
      Subgroup.mem_inf.2 ⟨h2k, R1.mul_mem (R1.inv_mem a.2) b.2⟩
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at h2
    exact Subtype.ext h2
  rw [← hR1card]
  exact Nat.card_le_card_of_injective _ hinj

theorem card_ker_eq_two_pow {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] (f : W →ₗ[ZMod 2] W) {n : ℕ} (hn : Module.finrank (ZMod 2) W = n) :
    Nat.card ↥(LinearMap.ker f) = 2 ^ (n - Module.finrank (ZMod 2) ↥(LinearMap.range f)) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  congr 1
  have h := LinearMap.finrank_range_add_finrank_ker f
  omega

end Generic

section Fix


@[expose] noncomputable def fiveHom : ↥(Subgroup.centralizer ({xB} : Set B)) →* Co2 := by
  with_reducible_and_instances exact CTIB.psiCo2.toMonoidHom.comp (jbarToKv.comp centralizerXBHom)

set_option linter.unusedSectionVars false in
theorem fiveHom_apply (y : ↥(Subgroup.centralizer ({xB} : Set B))) :
    fiveHom y = CTIB.psiCo2 (jbarToKv (centralizerXBHom y)) := rfl

theorem fiveHom_surjective : Function.Surjective fiveHom := by
  intro σ
  obtain ⟨j, hj⟩ := jbarToKv_surjective (CTIB.psiCo2.symm σ)
  obtain ⟨e, he⟩ := centralizerXBHom_bijective.2 j
  exact ⟨e, by rw [fiveHom_apply, he, hj, MulEquiv.apply_symm_apply]⟩

theorem mem_ker_fiveHom {e : ↥(Subgroup.centralizer ({xB} : Set B))} :
    e ∈ fiveHom.ker ↔ ((centralizerXBHom e : Cbar) ∈ Ebar) := by
  rw [MonoidHom.mem_ker, fiveHom_apply, MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker,
    ker_jbarToKv, Subgroup.mem_subgroupOf]

set_option linter.unusedSectionVars false in
theorem centralizerXBHom_coe (y : ↥(Subgroup.centralizer ({xB} : Set B))) :
    (centralizerXBHom y : Cbar) = bCbarHom y := rfl

@[expose] noncomputable def kerPsi : ↥fiveHom.ker →* Multiplicative (Wv (phi0 (coordOf rStar))) :=
  psiBar.comp
    { toFun := fun e => ⟨(centralizerXBHom e.1 : Cbar), mem_ker_fiveHom.1 e.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp }

theorem kerPsi_apply (e : ↥fiveHom.ker) :
    kerPsi e = psiBar ⟨(centralizerXBHom e.1 : Cbar), mem_ker_fiveHom.1 e.2⟩ := rfl

theorem kerPsi_fixed {y : ↥(Subgroup.centralizer ({xB} : Set B))} {e : ↥fiveHom.ker}
    (he : (e : ↥(Subgroup.centralizer ({xB} : Set B))) * y = y * e) :
    wAct _ (jbarToKv (centralizerXBHom y)) (Multiplicative.toAdd (kerPsi e)) =
      Multiplicative.toAdd (kerPsi e) := by
  set yb := centralizerXBHom y with hyb
  have hmemE := mem_ker_fiveHom.1 e.2
  have hc : (yb : Cbar)⁻¹ * (centralizerXBHom e.1 : Cbar) * yb = centralizerXBHom e.1 := by
    have h1 : centralizerXBHom e.1 * yb = yb * centralizerXBHom e.1 := by
      rw [hyb, ← map_mul, ← map_mul, he]
    have h2 : (centralizerXBHom e.1 : Cbar) * yb = yb * centralizerXBHom e.1 :=
      congrArg Subtype.val h1
    calc (yb : Cbar)⁻¹ * (centralizerXBHom e.1 : Cbar) * yb
        = (yb : Cbar)⁻¹ * ((centralizerXBHom e.1 : Cbar) * yb) := by group
      _ = (yb : Cbar)⁻¹ * (yb * centralizerXBHom e.1) := by rw [h2]
      _ = centralizerXBHom e.1 := by group
  have h := psiBar_conj yb.2 hmemE
  have e1 : (⟨(yb : Cbar)⁻¹ * (centralizerXBHom e.1 : Cbar) * yb,
      conj_mem_Ebar yb.2 hmemE⟩ : Ebar) = ⟨(centralizerXBHom e.1 : Cbar), hmemE⟩ :=
    Subtype.ext hc
  rw [e1] at h
  rw [kerPsi_apply]
  have h' := congrArg Multiplicative.toAdd h
  rw [toAdd_ofAdd] at h'
  exact h'.symm

theorem kerPsi_mem_ker {y : ↥(Subgroup.centralizer ({xB} : Set B))} {e : ↥fiveHom.ker}
    (he : (e : ↥(Subgroup.centralizer ({xB} : Set B))) * y = y * e) :
    Multiplicative.toAdd (kerPsi e) ∈
      LinearMap.ker (wAct (phi0 (coordOf rStar)) (jbarToKv (centralizerXBHom y)) - 1) := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, kerPsi_fixed he, Module.End.one_apply, sub_self]

theorem card_ker_inf_centralizer_le (y : ↥(Subgroup.centralizer ({xB} : Set B))) :
    Nat.card ↥((fiveHom.ker ⊓ Subgroup.centralizer {y} :
      Subgroup ↥(Subgroup.centralizer ({xB} : Set B)))) ≤
      2 * 2 ^ (22 - ((fiveHom y).val.val - 1).rank) := by
  have hfin : Finite B :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_B_eq]; norm_num)
  set Y : Subgroup ↥(Subgroup.centralizer ({xB} : Set B)) :=
    fiveHom.ker ⊓ Subgroup.centralizer {y} with hY
  set φ : ↥Y →* Multiplicative (Wv (phi0 (coordOf rStar))) :=
    kerPsi.comp (Subgroup.inclusion (inf_le_left : Y ≤ fiveHom.ker)) with hφ
  set k := jbarToKv (centralizerXBHom y) with hk
  have hker : Nat.card φ.ker ≤ 2 := by
    refine card_le_two_of_map (v := fun x : ↥φ.ker => ((x : ↥Y) : B))
      (fun a b hab => Subtype.ext (Subtype.ext (Subtype.ext hab))) (a := xB) ?_
    intro x
    have hx : kerPsi (Subgroup.inclusion (inf_le_left : Y ≤ fiveHom.ker) x) = 1 := x.2
    rw [kerPsi_apply, psiBar_eq_one_iff] at hx
    rcases hx with hx | hx
    · left
      have h1 : centralizerXBHom ((x : ↥Y) : ↥(Subgroup.centralizer ({xB} : Set B))) = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hx)
      have h2 := centralizerXBHom_bijective.1 (h1.trans (map_one _).symm)
      exact congrArg Subtype.val h2
    · right
      have h1 : bCbarHom ((x : ↥Y) : B) = bCbarHom xB := by
        rw [bCbarHom_xB, ← centralizerXBHom_coe]
        simpa using congrArg Subtype.val hx
      exact bCbarHom_injective h1
  have hrange : Nat.card φ.range ≤
      Nat.card ↥(LinearMap.ker (wAct (phi0 (coordOf rStar)) k - 1)) := by
    refine Nat.card_le_card_of_injective (fun m => ⟨Multiplicative.toAdd (m : _), ?_⟩) ?_
    · obtain ⟨x, hx⟩ := m.2
      have hcomm : (((x : ↥Y) : ↥(Subgroup.centralizer ({xB} : Set B)))) * y =
          y * ((x : ↥Y) : ↥(Subgroup.centralizer ({xB} : Set B))) :=
        (Subgroup.mem_centralizer_singleton_iff (g := y)
          (k := ((x : ↥Y) : ↥(Subgroup.centralizer ({xB} : Set B))))).1 (Subgroup.mem_inf.1 x.2).2
      have h := kerPsi_mem_ker (e := Subgroup.inclusion (inf_le_left : Y ≤ fiveHom.ker) x) hcomm
      rw [← hx]
      exact h
    · intro a b hab
      apply Subtype.ext
      have := congrArg Subtype.val hab
      simpa using this
  have hfinW : Module.Finite (ZMod 2) (Wv (phi0 (coordOf rStar))) :=
    Module.finite_of_finrank_pos (by rw [finrank_Wv_rStar]; norm_num)
  have hcardK : Nat.card ↥(LinearMap.ker (wAct (phi0 (coordOf rStar)) k - 1)) =
      2 ^ (22 - CTIB.rkW k) :=
    card_ker_eq_two_pow _ finrank_Wv_rStar
  have hrk : CTIB.rkW k = ((fiveHom y).val.val - 1).rank := by
    rw [fiveHom_apply, CTIB.rank_psiCo2]
  have htot := Subgroup.card_ker_mul_card_range φ
  rw [← htot, ← hrk, ← hcardK]
  exact Nat.mul_le_mul hker hrange


theorem ker_fiveHom_eq : fiveHom.ker = (Ebar.subgroupOf Jbar).comap centralizerXBHom := by
  ext e
  rw [mem_ker_fiveHom, Subgroup.mem_comap, Subgroup.mem_subgroupOf]

theorem card_ker_fiveHom : Nat.card fiveHom.ker = 2 ^ 23 := by
  rw [ker_fiveHom_eq]
  have h1 : Nat.card ↥((Ebar.subgroupOf Jbar).comap centralizerXBHom) =
      Nat.card ↥(Ebar.subgroupOf Jbar) :=
    Nat.card_congr ((Equiv.ofBijective _ centralizerXBHom_bijective).subtypeEquiv
      fun x => Iff.rfl)
  rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Ebar_le_Jbar).toEquiv,
    Ebar_extraspecial.2]

theorem mem_ker_fiveHom_of_mem {y : B} (hy : orderOf y = 5)
    (hyx : y ∈ Subgroup.centralizer ({xB} : Set B)) {q : B}
    (hq : q ∈ GLAPPrimeCoreOf 5 (Subgroup.centralizer ({y} : Set B)))
    (hqx : q ∈ Subgroup.centralizer ({xB} : Set B)) :
    (⟨q, hqx⟩ : ↥(Subgroup.centralizer ({xB} : Set B))) ∈ fiveHom.ker := by
  have hfin : Finite B :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_B_eq]; norm_num)
  have hN : Nat.Coprime 5 (Nat.card fiveHom.ker) := by
    rw [card_ker_fiveHom]
    norm_num
  exact mem_ker_of_local_quotient Nat.prime_five fiveHom fiveHom_surjective hN
    oPrimeCoreTrivialAt_Co2_five hy hyx hq hqx

theorem card_inf_centralizer_xB_le {y : B} (hy : orderOf y = 5)
    (hyx : y ∈ Subgroup.centralizer ({xB} : Set B)) :
    Nat.card ↥(GLAPPrimeCoreOf 5 (Subgroup.centralizer ({y} : Set B)) ⊓
      Subgroup.centralizer ({xB} : Set B)) ≤
      2 * 2 ^ (22 - ((fiveHom ⟨y, hyx⟩).val.val - 1).rank) := by
  refine le_trans (Nat.card_le_card_of_injective
    (β := ↥((fiveHom.ker ⊓ Subgroup.centralizer {(⟨y, hyx⟩ : ↥(Subgroup.centralizer
      ({xB} : Set B)))} : Subgroup ↥(Subgroup.centralizer ({xB} : Set B)))))
    (fun q => ⟨⟨q.1, q.2.2⟩, mem_ker_fiveHom_of_mem hy hyx q.2.1 q.2.2, ?_⟩) ?_)
    (card_ker_inf_centralizer_le ⟨y, hyx⟩)
  · refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
    exact (Subgroup.mem_centralizer_singleton_iff (g := y) (k := (q : B))).1
      (GLAPPrimeCoreOf_le _ q.2.1)
  · intro a b hab
    apply Subtype.ext
    have h1 := congrArg Subtype.val hab
    have h2 := congrArg Subtype.val h1
    simpa using h2

theorem orderOf_fiveHom {y : B} (hy : orderOf y = 5)
    (hyx : y ∈ Subgroup.centralizer ({xB} : Set B)) : orderOf (fiveHom ⟨y, hyx⟩) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hy' : orderOf (⟨y, hyx⟩ : ↥(Subgroup.centralizer ({xB} : Set B))) = 5 := by
    rw [Subgroup.orderOf_mk, hy]
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, ← hy', pow_orderOf_eq_one, map_one]
  · intro h1
    have hmem : (⟨y, hyx⟩ : ↥(Subgroup.centralizer ({xB} : Set B))) ∈ fiveHom.ker := h1
    have hd : orderOf (⟨⟨y, hyx⟩, hmem⟩ : ↥fiveHom.ker) ∣ Nat.card fiveHom.ker :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hy', card_ker_fiveHom] at hd
    have : (5 : ℕ) ∣ 2 := (Nat.Prime.dvd_of_dvd_pow Nat.prime_five hd)
    omega



theorem card_inf_centralizer_xB_le_seven {y : B} (hy : orderOf y = 5)
    (hyx : y ∈ Subgroup.centralizer ({xB} : Set B)) :
    Nat.card ↥(GLAPPrimeCoreOf 5 (Subgroup.centralizer ({y} : Set B)) ⊓
      Subgroup.centralizer ({xB} : Set B)) ≤ 2 ^ 7 := by
  have h := card_inf_centralizer_xB_le hy hyx
  have hr := sixteen_le_rank_co2 (orderOf_fiveHom hy hyx)
  calc _ ≤ _ := h
    _ ≤ 2 * 2 ^ 6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ = 2 ^ 7 := by norm_num

theorem card_inf_centralizer_xB_le_three {y : B} (hy : orderOf y = 5)
    (hyx : y ∈ Subgroup.centralizer ({xB} : Set B)) {R : Subgroup B} (hR : IsPGroup 5 R)
    (hRc : 125 ≤ Nat.card R) (hRx : R ≤ Subgroup.centralizer ({xB} : Set B))
    (hRy : R ≤ Subgroup.centralizer ({y} : Set B)) (hyR : y ∈ R) :
    Nat.card ↥(GLAPPrimeCoreOf 5 (Subgroup.centralizer ({y} : Set B)) ⊓
      Subgroup.centralizer ({xB} : Set B)) ≤ 2 ^ 3 := by
  have hfin : Finite B :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_B_eq]; norm_num)
  have hN : Nat.Coprime 5 (Nat.card fiveHom.ker) := by
    rw [card_ker_fiveHom]
    norm_num
  have hS := card_le_card_map_of_coprime_ker Nat.prime_five fiveHom hN hR hRx
  have hyR1 : (⟨y, hyx⟩ : ↥(Subgroup.centralizer ({xB} : Set B))) ∈ R.subgroupOf
      (Subgroup.centralizer ({xB} : Set B)) := Subgroup.mem_subgroupOf.2 hyR
  have hr : 20 ≤ ((fiveHom ⟨y, hyx⟩).val.val - 1).rank := by
    refine twenty_le_rank_co2 (orderOf_fiveHom hy hyx)
      ((hR.comap_of_injective _ (Subgroup.centralizer ({xB} : Set B)).subtype_injective).map _)
      (le_trans hRc hS) ⟨_, hyR1, rfl⟩ ?_
    rintro _ ⟨a, ha, rfl⟩
    have hay : (a : B) ∈ Subgroup.centralizer ({y} : Set B) := hRy (Subgroup.mem_subgroupOf.1 ha)
    have hcomm : a * (⟨y, hyx⟩ : ↥(Subgroup.centralizer ({xB} : Set B))) = ⟨y, hyx⟩ * a :=
      Subtype.ext ((Subgroup.mem_centralizer_singleton_iff (g := y) (k := (a : B))).1 hay)
    rw [← map_mul, ← map_mul, hcomm]
  have h := card_inf_centralizer_xB_le hy hyx
  calc _ ≤ _ := h
    _ ≤ 2 * 2 ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ = 2 ^ 3 := by norm_num

theorem card_gLAPPrimeCoreOf_inf_centralizer_le {w y : B} (hw : BabyInv 1 w)
    (hy : orderOf y = 5) (hwy : w ∈ Subgroup.centralizer ({y} : Set B)) :
    Nat.card ↥(GLAPPrimeCoreOf 5 (Subgroup.centralizer ({y} : Set B)) ⊓
      Subgroup.centralizer ({w} : Set B)) ≤ 2 ^ 7 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (CFSG.Monster.Existence.babyTableIII.2 1 w xB hw babyInv_one_xB)
  have hyx : c * y * c⁻¹ ∈ Subgroup.centralizer ({xB} : Set B) := by
    rw [← hc]
    exact conj_mem_centralizer_conj c (mem_centralizer_singleton_symm hwy)
  have hy' : orderOf (c * y * c⁻¹) = 5 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hy
  have h := card_gLAPPrimeCoreOf_inf_le_conj (p := 5) c y w
  rw [hc] at h
  exact h.trans (card_inf_centralizer_xB_le_seven hy' hyx)

theorem card_gLAPPrimeCoreOf_inf_centralizer_le_of_central {w y : B} (hw : BabyInv 1 w)
    (hy : orderOf y = 5) (hwy : w ∈ Subgroup.centralizer ({y} : Set B)) {R : Subgroup B}
    (hR : IsPGroup 5 R) (hRc : 125 ≤ Nat.card R) (hRw : R ≤ Subgroup.centralizer ({w} : Set B))
    (hRy : R ≤ Subgroup.centralizer ({y} : Set B)) (hyR : y ∈ R) :
    Nat.card ↥(GLAPPrimeCoreOf 5 (Subgroup.centralizer ({y} : Set B)) ⊓
      Subgroup.centralizer ({w} : Set B)) ≤ 2 ^ 3 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (CFSG.Monster.Existence.babyTableIII.2 1 w xB hw babyInv_one_xB)
  have hyx : c * y * c⁻¹ ∈ Subgroup.centralizer ({xB} : Set B) := by
    rw [← hc]
    exact conj_mem_centralizer_conj c (mem_centralizer_singleton_symm hwy)
  have hy' : orderOf (c * y * c⁻¹) = 5 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hy
  set R' : Subgroup B := R.map (MulAut.conj c).toMonoidHom with hR'
  have hR'x : R' ≤ Subgroup.centralizer ({xB} : Set B) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← hc]
    exact conj_mem_centralizer_conj c (hRw hg)
  have hR'y : R' ≤ Subgroup.centralizer ({c * y * c⁻¹} : Set B) := by
    rintro _ ⟨g, hg, rfl⟩
    exact conj_mem_centralizer_conj c (hRy hg)
  have hR'c : Nat.card R' = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have h := card_gLAPPrimeCoreOf_inf_le_conj (p := 5) c y w
  rw [hc] at h
  exact h.trans (card_inf_centralizer_xB_le_three hy' hyx (hR.map _) (hR'c ▸ hRc) hR'x hR'y
    ⟨y, hyR, rfl⟩)

end Fix

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
