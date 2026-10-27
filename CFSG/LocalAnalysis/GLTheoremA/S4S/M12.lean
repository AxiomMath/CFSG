module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Lift
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_1Aut
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10FiCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

section M12

variable {G : Type} [Group G]

private theorem m12_catalogIs_of_mulEquiv {S T : Type} [Group S] [Group T]
    {Q : TauCeti.CFSGIndex → Prop} (e : S ≃* T) (h : catalogIs S Q) : catalogIs T Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

private theorem m12_isPGroup_center_pQuot [Finite G] (K : Subgroup G) :
    IsPGroup 3 (Subgroup.center (PQuot 3 K)) :=
  isPGroup_center_of_pPrimeCore_eq_bot (by norm_num : Nat.Prime 3)
    (glaPPrimeCore_quotient_eq_bot (by norm_num : Nat.Prime 3))

private theorem m12_centralizerQuot_eq_centModSubgroup (p : ℕ) (L : Subgroup G) :
    CFSG.HardMathSupport.Solomon.LocalBalance.centralizerQuot L (GLAPPrimeCoreOf p L) =
      centModSubgroup p L := by
  ext g
  constructor
  · rintro ⟨hgL, -, hg⟩
    exact ⟨hgL, fun l hl => by simpa [commutatorElement_def] using hg l hl⟩
  · rintro ⟨hgL, hg⟩
    exact ⟨hgL, CFSG.LocalAnalysis.GLTheoremA.normalizer_le_normalizer_glaPPrimeCoreOf p L hgL,
      fun l hl => by simpa [commutatorElement_def] using hg l hl⟩

private theorem m12_isPGroup_three_of_isElemAbelian {A : Subgroup G} (hA : IsElemAbelian 3 A) :
    IsPGroup 3 A :=
  isPGroup_iff_pow_pow_eq_one.2 fun a =>
    ⟨1, Subtype.ext (by simpa using hA.2 (a : G) a.2)⟩

theorem i71M12At_of [Finite G] (h : KDM12) : I71M12At G := by
  intro X L B hL hcat hB hBN
  have hp : Nat.Prime 3 := by norm_num
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 L) := isQuasisimple_pQuot_of_glaPComponent hp hL
  have hZ : IsPGroup 3 (Subgroup.center (PQuot 3 L)) := m12_isPGroup_center_pQuot L
  have hc : Subgroup.center (PQuot 3 L) = ⊥ :=
    (h (PSimple 3 L) hcat).1 (PQuot 3 L) hq hZ ⟨MulEquiv.refl _⟩
  have e : PSimple 3 L ≃* PQuot 3 L :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hM : catalogIs (PQuot 3 L) isM12 := m12_catalogIs_of_mulEquiv e hcat
  have hbound : ∀ D : Subgroup (MulAut (PQuot 3 L)), IsElemAbelian 3 D → Nat.card D ≤ 9 :=
    (h (PQuot 3 L) hM).2.1
  set N : Subgroup G := Subgroup.normalizer (L : Set G) with hN
  set B' : Subgroup ↥N := B.subgroupOf N with hB'
  let φ : ↥B' →* MulAut (PQuot 3 L) :=
    (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 L).domRestrict B'
  have hker : ∀ b : ↥B', b ∈ φ.ker ↔ (((b : ↥N) : G) ∈ centModSubgroup 3 L) := by
    intro b
    rw [MonoidHom.mem_ker, ← m12_centralizerQuot_eq_centModSubgroup,
      CFSG.HardMathSupport.Solomon.Coordinator.mem_centralizerQuot_iff_barAut_eq_one]
    rfl
  have hkercard : Nat.card φ.ker = Nat.card ↥(B ⊓ centModSubgroup 3 L) := by
    have hinj : Function.Injective (N.subtype.comp B'.subtype) :=
      N.subtype_injective.comp B'.subtype_injective
    rw [← Subgroup.card_map_of_injective hinj]
    congr 2
    ext g
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨(Subgroup.mem_subgroupOf.1 b.2), (hker b).1 hb⟩
    · rintro ⟨hgB, hgc⟩
      have hgN : g ∈ N := hgc.1
      exact ⟨⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.2 hgB⟩, (hker _).2 hgc, rfl⟩
  have hB'card : Nat.card ↥B' = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card ↥B' := by
    rw [← Subgroup.index_ker]
    exact Subgroup.card_mul_index _
  have hrange : IsElemAbelian 3 φ.range := by
    rw [MonoidHom.domRestrict_range]
    exact CFSG.SectionRank.isElemAbelian_map
      (CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_subgroupOf hB N)
      (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 L)
  have hbd : Nat.card φ.range ≤ 9 := hbound φ.range hrange
  calc Nat.card B = Nat.card ↥B' := hB'card.symm
    _ = Nat.card φ.ker * Nat.card φ.range := h1.symm
    _ ≤ Nat.card ↥(B ⊓ centModSubgroup 3 L) * 9 := by
        rw [hkercard]
        exact Nat.mul_le_mul_left _ hbd
    _ = 9 * Nat.card ↥(B ⊓ centModSubgroup 3 L) := mul_comm _ _

private theorem m12_mem_primeCoreOf_iff {L : Subgroup G} {g : G} :
    g ∈ GLAPPrimeCoreOf 3 L ↔ ∃ hg : g ∈ L, (QuotientGroup.mk ⟨g, hg⟩ : PQuot 3 L) = 1 := by
  unfold GLAPPrimeCoreOf
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, (QuotientGroup.eq_one_iff y).2 hy⟩
  · rintro ⟨hg, h1⟩
    exact ⟨⟨g, hg⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩

private def m12Pre (L : Subgroup G) (K : Subgroup (PQuot 3 L)) : Subgroup G :=
  (K.comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))).map L.subtype

private theorem m12_mem_pre_iff {L : Subgroup G} {K : Subgroup (PQuot 3 L)} {g : G} :
    g ∈ m12Pre L K ↔ ∃ hg : g ∈ L, (QuotientGroup.mk ⟨g, hg⟩ : PQuot 3 L) ∈ K := by
  unfold m12Pre
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hg, hK⟩
    exact ⟨⟨g, hg⟩, hK, rfl⟩

private theorem m12_primeCoreOf_le_pre (L : Subgroup G) (K : Subgroup (PQuot 3 L)) :
    GLAPPrimeCoreOf 3 L ≤ m12Pre L K := fun o ho => by
  obtain ⟨hoL, h1⟩ := m12_mem_primeCoreOf_iff.1 ho
  exact m12_mem_pre_iff.2 ⟨hoL, by rw [h1]; exact K.one_mem⟩

private theorem m12_not_dvd_card_O [Finite G] (L : Subgroup G) :
    ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 L) :=
  (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).1
    (CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf
      (by norm_num : Nat.Prime 3) L)

private theorem m12_comm_mem {L A : Subgroup G} (hAC : ∀ a ∈ A, CentMod 3 L a) {a e : G}
    (ha : a ∈ A) (he : e ∈ L) : a * e * a⁻¹ * e⁻¹ ∈ GLAPPrimeCoreOf 3 L := by
  have hc : ⁅e⁻¹, a⁆ ∈ GLAPPrimeCoreOf 3 L :=
    (mem_centModSubgroup.1 (centMod_iff.1 (hAC a ha))).2 e⁻¹ (L.inv_mem he)
  have h1 : e⁻¹ * a * e * a⁻¹ ∈ GLAPPrimeCoreOf 3 L := by
    have e1 : ⁅e⁻¹, a⁆ = e⁻¹ * a * e * a⁻¹ := by
      rw [commutatorElement_def, inv_inv]
    rw [e1] at hc
    exact hc
  have hn : e ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.normalizer_le_normalizer_glaPPrimeCoreOf 3 L
      (Subgroup.le_normalizer he)
  have h2 := (Subgroup.mem_normalizer_iff.1 hn _).1 h1
  have heq : a * e * a⁻¹ * e⁻¹ = e * (e⁻¹ * a * e * a⁻¹) * e⁻¹ := by group
  rw [heq]
  exact h2

private theorem m12_coset_fix [Finite G] {L A : Subgroup G} (hA : IsElemAbelian 3 A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hAC : ∀ a ∈ A, CentMod 3 L a) {e : G}
    (he : e ∈ L) :
    e ∈ (L ⊓ Subgroup.centralizer (A : Set G)) ⊔ GLAPPrimeCoreOf 3 L := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hA3 : IsPGroup 3 A := m12_isPGroup_three_of_isElemAbelian hA
  have hact : ∀ a ∈ A, ∀ x : G, x * e⁻¹ ∈ GLAPPrimeCoreOf 3 L →
      a * x * a⁻¹ * e⁻¹ ∈ GLAPPrimeCoreOf 3 L := by
    intro a ha x hx
    have h1 : a * (x * e⁻¹) * a⁻¹ ∈ GLAPPrimeCoreOf 3 L :=
      (Subgroup.mem_normalizer_iff.1
        (CFSG.LocalAnalysis.GLTheoremA.normalizer_le_normalizer_glaPPrimeCoreOf 3 L (hAN ha))
        (x * e⁻¹)).1 hx
    have h2 : a * e * a⁻¹ * e⁻¹ ∈ GLAPPrimeCoreOf 3 L := m12_comm_mem hAC ha he
    have heq : a * x * a⁻¹ * e⁻¹ = (a * (x * e⁻¹) * a⁻¹) * (a * e * a⁻¹ * e⁻¹) := by group
    rw [heq]
    exact (GLAPPrimeCoreOf 3 L).mul_mem h1 h2
  letI : MulAction A {x : G // x * e⁻¹ ∈ GLAPPrimeCoreOf 3 L} :=
    { smul := fun a x => ⟨(a : G) * x.1 * (a : G)⁻¹, hact a a.2 x.1 x.2⟩
      one_smul := fun x => Subtype.ext (by
        show (1 : G) * x.1 * (1 : G)⁻¹ = x.1
        group)
      mul_smul := fun a b x => Subtype.ext (by
        show ((a : G) * (b : G)) * x.1 * ((a : G) * (b : G))⁻¹ =
          (a : G) * ((b : G) * x.1 * (b : G)⁻¹) * (a : G)⁻¹
        group) }
  have hX : ¬ 3 ∣ Nat.card {x : G // x * e⁻¹ ∈ GLAPPrimeCoreOf 3 L} := by
    have eqv : {x : G // x * e⁻¹ ∈ GLAPPrimeCoreOf 3 L} ≃ GLAPPrimeCoreOf 3 L :=
      { toFun := fun x => ⟨x.1 * e⁻¹, x.2⟩
        invFun := fun o => ⟨o.1 * e, by simpa using o.2⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun o => Subtype.ext (by simp) }
    rw [Nat.card_congr eqv]
    exact m12_not_dvd_card_O L
  obtain ⟨x0, hx0⟩ := hA3.nonempty_fixed_point_of_prime_not_dvd_card _ hX
  have hfix : ∀ a ∈ A, a * x0.1 * a⁻¹ = x0.1 := fun a ha =>
    congrArg Subtype.val (MulAction.mem_fixedPoints.1 hx0 ⟨a, ha⟩)
  have hcent : x0.1 ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    calc a * x0.1 = a * x0.1 * a⁻¹ * a := by group
      _ = x0.1 * a := by rw [hfix a ha]
  have hx0O : x0.1 * e⁻¹ ∈ GLAPPrimeCoreOf 3 L := x0.2
  have hx0L : x0.1 ∈ L := by
    obtain ⟨h1, -⟩ := m12_mem_primeCoreOf_iff.1 hx0O
    have := L.mul_mem h1 he
    simpa using this
  have hmem : (x0.1 * e⁻¹)⁻¹ * x0.1 = e := by group
  have hsup : (x0.1 * e⁻¹)⁻¹ * x0.1 ∈
      GLAPPrimeCoreOf 3 L ⊔ (L ⊓ Subgroup.centralizer (A : Set G)) :=
    Subgroup.mul_mem_sup ((GLAPPrimeCoreOf 3 L).inv_mem hx0O)
      (Subgroup.mem_inf.2 ⟨hx0L, hcent⟩)
  rw [hmem, sup_comm] at hsup
  exact hsup

private theorem m12_lift [Finite G] {L A : Subgroup G} {Dbar : Subgroup (PQuot 3 L)}
    (hA : IsElemAbelian 3 A) (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hAC : ∀ a ∈ A, CentMod 3 L a) (hD : IsElemAbelian 3 Dbar) (hDcard : Nat.card Dbar = 9) :
    ∃ W : Subgroup G, W ≤ L ⊓ Subgroup.centralizer (A : Set G) ∧ IsPGroup 3 W ∧
      (∀ w ∈ W, ∃ hw : w ∈ L, (QuotientGroup.mk ⟨w, hw⟩ : PQuot 3 L) ∈ Dbar) ∧
      IsElemAbelian 3 W ∧ Nat.card W = 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp : Nat.Prime 3 := by norm_num
  have hO3 : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 L) := m12_not_dvd_card_O L
  have hEL : m12Pre L Dbar ≤ L := fun g hg => by
    obtain ⟨hgL, -⟩ := m12_mem_pre_iff.1 hg
    exact hgL
  have hLN : ∀ g ∈ L, g ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 L : Set G) := fun g hg =>
    CFSG.LocalAnalysis.GLTheoremA.normalizer_le_normalizer_glaPPrimeCoreOf 3 L
      (Subgroup.le_normalizer hg)
  have hOE : GLAPPrimeCoreOf 3 L ≤ m12Pre L Dbar := m12_primeCoreOf_le_pre L Dbar
  have hEN : m12Pre L Dbar ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 L : Set G) :=
    fun g hg => hLN g (hEL hg)
  have hEp : ∀ e ∈ m12Pre L Dbar, ∃ k : ℕ, e ^ (3 ^ k) ∈ GLAPPrimeCoreOf 3 L := by
    intro e he
    obtain ⟨heL, hK⟩ := m12_mem_pre_iff.1 he
    refine ⟨1, ?_⟩
    simp only [pow_one]
    refine m12_mem_primeCoreOf_iff.2 ⟨L.pow_mem heL 3, ?_⟩
    have h3 : (QuotientGroup.mk ⟨e, heL⟩ : PQuot 3 L) ^ 3 = 1 := hD.2 _ hK
    rw [← QuotientGroup.mk_pow] at h3
    exact h3
  have hNO : (L ⊓ Subgroup.centralizer (A : Set G)) ≤
      Subgroup.normalizer (GLAPPrimeCoreOf 3 L : Set G) :=
    fun g hg => hLN g (Subgroup.mem_inf.1 hg).1
  have hENO : m12Pre L Dbar ≤ (L ⊓ Subgroup.centralizer (A : Set G)) ⊔ GLAPPrimeCoreOf 3 L :=
    fun e he => m12_coset_fix hA hAN hAC (hEL he)
  obtain ⟨W, hWN, hWp, -, hWO⟩ :=
    exists_pGroup_lift hp hO3 hOE hEN hEp IsPGroup.of_bot bot_le bot_le hNO hENO
  have hWLC : W ≤ L ⊓ Subgroup.centralizer (A : Set G) := fun w hw =>
    (Subgroup.mem_inf.1 (hWN hw)).1
  have hWsubL : W ≤ L := fun w hw => (Subgroup.mem_inf.1 (hWLC hw)).1
  have hWE : ∀ w ∈ W, ∃ hw : w ∈ L, (QuotientGroup.mk ⟨w, hw⟩ : PQuot 3 L) ∈ Dbar :=
    fun w hw => m12_mem_pre_iff.1 (Subgroup.mem_inf.1 (hWN hw)).2
  have hWNO : W ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 L : Set G) :=
    fun w hw => hLN w (hWsubL hw)
  have hWO' : ∀ w ∈ W, w ∈ GLAPPrimeCoreOf 3 L → w = 1 := by
    intro w hw hwO
    obtain ⟨k, hk⟩ := hWp ⟨w, hw⟩
    have hk' : w ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf w ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h2 : orderOf w ∣ Nat.card (GLAPPrimeCoreOf 3 L) := by
      rw [← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.2 hwO)
    have hcop : Nat.Coprime (3 ^ k) (Nat.card (GLAPPrimeCoreOf 3 L)) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hO3)
    have h3 : orderOf w ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd h1 h2
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  let ψ : ↥W →* PQuot 3 L :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).comp (Subgroup.inclusion hWsubL)
  have hψ : ∀ w : ↥W, ψ w = QuotientGroup.mk ⟨w.1, hWsubL w.2⟩ := fun w => rfl
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    rw [hψ] at hw
    apply Subtype.ext
    exact hWO' w.1 w.2 (m12_mem_primeCoreOf_iff.2 ⟨hWsubL w.2, hw⟩)
  have hψmem : ∀ w : ↥W, ψ w ∈ Dbar := fun w => by
    obtain ⟨_, hmem⟩ := hWE w.1 w.2
    rw [hψ]
    exact hmem
  have hrange : ψ.range = Dbar := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      exact hψmem w
    · intro x hx
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      have hyE : (y : G) ∈ m12Pre L Dbar := m12_mem_pre_iff.2 ⟨y.2, hx⟩
      have hyWO : (y : G) ∈ W ⊔ GLAPPrimeCoreOf 3 L := by
        rw [hWO]
        exact hyE
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right W _ hWNO] at hyWO
      obtain ⟨w, hw, o, ho, hwo⟩ := Set.mem_mul.1 hyWO
      refine ⟨⟨w, hw⟩, ?_⟩
      have ho1 : (QuotientGroup.mk ⟨o, (m12_mem_primeCoreOf_iff.1 ho).1⟩ : PQuot 3 L) = 1 :=
        (m12_mem_primeCoreOf_iff.1 ho).2
      have hy : y = ⟨w, hWsubL hw⟩ * ⟨o, (m12_mem_primeCoreOf_iff.1 ho).1⟩ :=
        Subtype.ext hwo.symm
      rw [hψ, hy, QuotientGroup.mk_mul, ho1, mul_one]
  have hWcard : Nat.card W = 9 := by
    have e1 : Nat.card ↥W = Nat.card ↥(ψ.range) :=
      Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv
    rw [e1, hrange, hDcard]
  have hWab : IsElemAbelian 3 W := by
    refine ⟨isMulCommutative_iff.2 (fun a b => ?_), fun x hx => ?_⟩
    · apply hψinj
      rw [map_mul, map_mul]
      have hcomm := isMulCommutative_iff.1 hD.1 ⟨ψ a, hψmem a⟩ ⟨ψ b, hψmem b⟩
      exact congrArg Subtype.val hcomm
    · have h1 : ψ ⟨x, hx⟩ ^ 3 = 1 := hD.2 _ (hψmem ⟨x, hx⟩)
      have h2 : (⟨x, hx⟩ : ↥W) ^ 3 = 1 := hψinj (by rw [map_pow, h1, map_one])
      exact congrArg Subtype.val h2
  exact ⟨W, hWLC, hWp, hWE, hWab, hWcard⟩

private theorem m12_conj_pre_of_mem {L : Subgroup G} {Ubar Dbar : Subgroup (PQuot 3 L)}
    (hDN : Dbar ≤ Subgroup.normalizer (Ubar : Set (PQuot 3 L))) {d : G} (hdL : d ∈ L)
    (hd : (QuotientGroup.mk ⟨d, hdL⟩ : PQuot 3 L) ∈ Dbar) {y : G}
    (hy : y ∈ m12Pre L Ubar) : d * y * d⁻¹ ∈ m12Pre L Ubar := by
  obtain ⟨hyL, hyU⟩ := m12_mem_pre_iff.1 hy
  have hdyL : d * y * d⁻¹ ∈ L := L.mul_mem (L.mul_mem hdL hyL) (L.inv_mem hdL)
  refine m12_mem_pre_iff.2 ⟨hdyL, ?_⟩
  have h1 := (Subgroup.mem_normalizer_iff.1 (hDN hd) _).1 hyU
  have heq : (QuotientGroup.mk ⟨d * y * d⁻¹, hdyL⟩ : PQuot 3 L) =
      QuotientGroup.mk ⟨d, hdL⟩ * QuotientGroup.mk ⟨y, hyL⟩ * (QuotientGroup.mk ⟨d, hdL⟩)⁻¹ := by
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
  rw [heq]
  exact h1

private theorem m12_sylow_two [Finite G] {L S : Subgroup G} {Ubar : Subgroup (PQuot 3 L)}
    (hU1 : Ubar ≠ ⊥) (hU2 : IsPGroup 2 Ubar) (hS3 : IsPGroup 3 S)
    (hSN : S ≤ Subgroup.normalizer ((m12Pre L Ubar : Subgroup G) : Set G)) :
    ∃ U : Subgroup G, U ≤ L ∧ IsPGroup 2 U ∧ S ≤ Subgroup.normalizer (U : Set G) ∧
      ¬ U ≤ GLAPPrimeCoreOf 3 L := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : Nat.Prime 3 := by norm_num
  have hO3 : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 L) := m12_not_dvd_card_O L
  have hTL : m12Pre L Ubar ≤ L := fun g hg => by
    obtain ⟨hgL, -⟩ := m12_mem_pre_iff.1 hg
    exact hgL
  have hOT : GLAPPrimeCoreOf 3 L ≤ m12Pre L Ubar := m12_primeCoreOf_le_pre L Ubar
  have hLN : ∀ g ∈ L, g ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 L : Set G) := fun g hg =>
    CFSG.LocalAnalysis.GLTheoremA.normalizer_le_normalizer_glaPPrimeCoreOf 3 L
      (Subgroup.le_normalizer hg)
  have hT2 : ∀ t ∈ m12Pre L Ubar, ∃ k : ℕ, t ^ (2 ^ k) ∈ GLAPPrimeCoreOf 3 L := by
    intro t ht
    obtain ⟨htL, hmem⟩ := m12_mem_pre_iff.1 ht
    obtain ⟨k, hk⟩ := hU2 ⟨_, hmem⟩
    refine ⟨k, m12_mem_primeCoreOf_iff.2 ⟨L.pow_mem htL _, ?_⟩⟩
    have hk' : (QuotientGroup.mk ⟨t, htL⟩ : PQuot 3 L) ^ (2 ^ k) = 1 := by
      simpa using congrArg Subtype.val hk
    rw [← QuotientGroup.mk_pow] at hk'
    exact hk'
  have hTO : ∃ t ∈ m12Pre L Ubar, t ∉ GLAPPrimeCoreOf 3 L := by
    obtain ⟨u, hu, hu1⟩ : ∃ u ∈ Ubar, u ≠ 1 := by
      by_contra hcon
      exact hU1 ((Subgroup.eq_bot_iff_forall _).2 fun u hu => by
        by_contra hu1
        exact hcon ⟨u, hu, hu1⟩)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective u
    refine ⟨y.1, m12_mem_pre_iff.2 ⟨y.2, hu⟩, fun hyO => ?_⟩
    obtain ⟨hyL, h1⟩ := m12_mem_primeCoreOf_iff.1 hyO
    exact hu1 h1
  set Q : Subgroup (m12Pre L Ubar) := (GLAPPrimeCoreOf 3 L).subgroupOf (m12Pre L Ubar) with hQdef
  have hTN : m12Pre L Ubar ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 L : Set G) :=
    fun g hg => hLN g (hTL hg)
  haveI : Q.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOT).2 hTN
  have hQ2 : IsPGroup 2 (↥(m12Pre L Ubar) ⧸ Q) := by
    refine isPGroup_iff_pow_pow_eq_one.2 ?_
    intro g
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨k, hk⟩ := hT2 (t : G) t.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.2 (by simpa using hk)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ2
  have hindex : Q.index = 2 ^ n := hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    obtain ⟨t, htT, htO⟩ := hTO
    have htop : Q = ⊤ := Subgroup.index_eq_one.1 (by rw [hindex, pow_zero])
    have htQ : (⟨t, htT⟩ : ↥(m12Pre L Ubar)) ∈ Q := by
      rw [htop]
      exact Subgroup.mem_top _
    exact htO (Subgroup.mem_subgroupOf.1 htQ)
  have h2dvd : 2 ∣ Q.index := by
    rw [hindex]
    exact dvd_pow_self 2 hn0
  have hcardT : ¬ 3 ∣ Nat.card (m12Pre L Ubar) := by
    have h1 : Nat.card Q * Q.index = Nat.card (m12Pre L Ubar) := Subgroup.card_mul_index Q
    have h2 : Nat.card Q = Nat.card (GLAPPrimeCoreOf 3 L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOT).toEquiv
    rw [← h1, h2, hindex]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h3 | h3
    · exact hO3 h3
    · have := Nat.Prime.dvd_of_dvd_pow hp h3
      norm_num at this
  obtain ⟨P, hP⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_sylow_normalized (r := 2) hSN hS3 hcardT
  refine ⟨(P : Subgroup (m12Pre L Ubar)).map (m12Pre L Ubar).subtype, ?_, ?_, hP, ?_⟩
  · exact (Subgroup.map_subtype_le _).trans hTL
  · exact P.isPGroup'.map (m12Pre L Ubar).subtype
  · intro hUO
    have hPle : (P : Subgroup (m12Pre L Ubar)) ≤ Q := by
      intro t ht
      exact Subgroup.mem_subgroupOf.2 (hUO (Subgroup.mem_map_of_mem _ ht))
    have hdvd : Q.index ∣ (P : Subgroup (m12Pre L Ubar)).index :=
      Subgroup.index_dvd_of_le hPle
    exact Sylow.not_dvd_index P (h2dvd.trans hdvd)

theorem i1016At_of [Finite G] (h : KDM12) : I1016At G := by
  intro X L A hL hcat hA hAN hAC
  have hp : Nat.Prime 3 := by norm_num
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 L) := isQuasisimple_pQuot_of_glaPComponent hp hL
  have hZ : IsPGroup 3 (Subgroup.center (PQuot 3 L)) := m12_isPGroup_center_pQuot L
  have hc : Subgroup.center (PQuot 3 L) = ⊥ :=
    (h (PSimple 3 L) hcat).1 (PQuot 3 L) hq hZ ⟨MulEquiv.refl _⟩
  have e : PSimple 3 L ≃* PQuot 3 L :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hM : catalogIs (PQuot 3 L) isM12 := m12_catalogIs_of_mulEquiv e hcat
  obtain ⟨Dbar, Ubar, hD, hDcard, hU1, hU2, hDN⟩ := (h (PQuot 3 L) hM).2.2
  refine ⟨hc, ?_⟩
  obtain ⟨W, hWLC, hWp, hWE, hWab, hWcard⟩ := m12_lift hA hAN hAC hD hDcard
  have hA3 : IsPGroup 3 A := m12_isPGroup_three_of_isElemAbelian hA
  have hWA : W ≤ Subgroup.normalizer (A : Set G) := fun w hw =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.1 (hWLC hw)).2
  have hS3 : IsPGroup 3 ↥(A ⊔ W) := IsPGroup.to_sup_of_normal_left' hA3 hWp hWA
  have hconj : ∀ a ∈ A, ∀ y ∈ m12Pre L Ubar, a * y * a⁻¹ ∈ m12Pre L Ubar := by
    intro a ha y hy
    obtain ⟨hyL, -⟩ := m12_mem_pre_iff.1 hy
    have hc' : a * y * a⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf 3 L := m12_comm_mem hAC ha hyL
    have heq : a * y * a⁻¹ = (a * y * a⁻¹ * y⁻¹) * y := by group
    rw [heq]
    exact (m12Pre L Ubar).mul_mem (m12_primeCoreOf_le_pre L Ubar hc') hy
  have hAT : A ≤ Subgroup.normalizer ((m12Pre L Ubar : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hconj a ha y
    · intro hy
      have h1 := hconj a⁻¹ (A.inv_mem ha) _ hy
      have e2 : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
      rwa [e2] at h1
  have hWT : W ≤ Subgroup.normalizer ((m12Pre L Ubar : Subgroup G) : Set G) := by
    intro d hd
    obtain ⟨hdL, hdD⟩ := hWE d hd
    obtain ⟨hdL', hdD'⟩ := hWE d⁻¹ (W.inv_mem hd)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact m12_conj_pre_of_mem hDN hdL hdD
    · intro hy
      have h1 := m12_conj_pre_of_mem hDN hdL' hdD' hy
      have e2 : d⁻¹ * (d * y * d⁻¹) * d⁻¹⁻¹ = y := by group
      rwa [e2] at h1
  obtain ⟨U, hUL, hU2', hSU, hUO⟩ :=
    m12_sylow_two hU1 hU2 hS3 (sup_le hAT hWT)
  exact ⟨W, hWLC, hWab, hWcard, U, hUL, hU2', hSU, hUO⟩

end M12

end CFSG.LocalAnalysis.GLTheoremA
