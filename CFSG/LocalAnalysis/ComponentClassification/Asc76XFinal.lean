module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XFinalG
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XFinalLayer
public import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.Adapters.WholeGroupLayer
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XGoldschmidt
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma316

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76 CFSG.LocalCores

open CFSG.Open Matrix in
open scoped MatrixGroups in
@[expose] def GoldschmidtTheoremA : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : Sylow 2 X) (A : Subgroup X), A ≤ S →
    IsMulCommutative A →
    (∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A) →
    let M : Subgroup X := Subgroup.normalClosure (A : Set X)
    let π := QuotientGroup.mk' (CFSG.Open.goldschmidtOddCore M)
    let T := ((S : Subgroup X).subgroupOf M).map π ⊓
      CFSG.Open.goldschmidtLayer (M ⧸ CFSG.Open.goldschmidtOddCore M)
    CFSG.Open.pCore 2 (M ⧸ CFSG.Open.goldschmidtOddCore M) ⊔
        CFSG.Open.goldschmidtLayer (M ⧸ CFSG.Open.goldschmidtOddCore M) = ⊤ ∧
    (A.subgroupOf M).map π =
      CFSG.Open.pCore 2 (M ⧸ CFSG.Open.goldschmidtOddCore M) ⊔
        Subgroup.closure {t | t ∈ T ∧ t ^ 2 = 1} ∧
    ∀ K : Subgroup (M ⧸ CFSG.Open.goldschmidtOddCore M), CFSG.Open.IsComponentOf K ⊤ →
      CFSG.Open.goldschmidtSimpleType (K ⧸ Subgroup.center K)

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def conjQuot {X : Subgroup G} (hX : X.Normal) (g : G) :
    MulAut (↥X ⧸ CFSG.Open.goldschmidtOddCore ↥X) :=
  QuotientGroup.congr (CFSG.Open.goldschmidtOddCore ↥X) (CFSG.Open.goldschmidtOddCore ↥X)
    (conjAutOf X (show g ∈ normalizer (X : Set G) by
      rw [normalizer_eq_top_iff.mpr hX]
      exact mem_top g))
    (oddCore_map_mulEquiv' _)

theorem conjQuot_mk {X : Subgroup G} (hX : X.Normal) (g : G) (x : X) :
    ((conjQuot hX g) (QuotientGroup.mk' _ x) : ↥X ⧸ CFSG.Open.goldschmidtOddCore ↥X) =
      QuotientGroup.mk' _ ⟨g * x * g⁻¹, hX.conj_mem x x.2 g⟩ :=
  rfl

theorem conjQuot_mul {X : Subgroup G} (hX : X.Normal) (g h : G) :
    conjQuot hX (g * h) = conjQuot hX g * conjQuot hX h := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
  rw [MulAut.mul_apply, conjQuot_mk, conjQuot_mk, conjQuot_mk]
  congr 1
  apply Subtype.ext
  change g * h * (x : G) * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹
  group

theorem conjQuot_one {X : Subgroup G} (hX : X.Normal) : conjQuot hX 1 = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
  rw [conjQuot_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  change 1 * (x : G) * 1⁻¹ = x
  group

theorem map_conjQuot_mul {X : Subgroup G} (hX : X.Normal) (g h : G)
    (L : Subgroup (↥X ⧸ CFSG.Open.goldschmidtOddCore ↥X)) :
    L.map (conjQuot hX (g * h)).toMonoidHom =
      (L.map (conjQuot hX h).toMonoidHom).map (conjQuot hX g).toMonoidHom := by
  rw [Subgroup.map_map, conjQuot_mul]
  rfl

@[expose] def compFix {X : Subgroup G} (hX : X.Normal) : Subgroup G where
  carrier := {g | ∀ L : Subgroup (↥X ⧸ CFSG.Open.goldschmidtOddCore ↥X), IsComponent L →
    L.map (conjQuot hX g).toMonoidHom = L}
  one_mem' := by
    intro L _
    rw [conjQuot_one]
    exact Subgroup.map_id L
  mul_mem' := by
    intro a b ha hb L hL
    rw [map_conjQuot_mul, hb L hL, ha L hL]
  inv_mem' := by
    intro a ha L hL
    have hL' := isComponent_map_mulEquiv (conjQuot hX a⁻¹) hL
    have h1 := ha _ hL'
    rw [← map_conjQuot_mul, mul_inv_cancel, conjQuot_one] at h1
    exact h1.symm.trans (Subgroup.map_id L)

theorem compFix_normal {X : Subgroup G} (hX : X.Normal) : (compFix hX).Normal := by
  refine ⟨fun g hg h L hL => ?_⟩
  have hg' : ∀ L : Subgroup (↥X ⧸ CFSG.Open.goldschmidtOddCore ↥X), IsComponent L →
      L.map (conjQuot hX g).toMonoidHom = L := hg
  have hL' := isComponent_map_mulEquiv (conjQuot hX h⁻¹) hL
  rw [map_conjQuot_mul, map_conjQuot_mul, hg' _ hL', ← map_conjQuot_mul, mul_inv_cancel,
    conjQuot_one]
  exact Subgroup.map_id L

theorem openPCore_map_eq {E : Type} [Group E] (p : ℕ) (φ : E ≃* E) :
    (CFSG.Open.pCore p E).map φ.toMonoidHom = CFSG.Open.pCore p E := by
  have key : ∀ ψ : E ≃* E, (CFSG.Open.pCore p E).map ψ.toMonoidHom ≤ CFSG.Open.pCore p E := by
    intro ψ
    rw [CFSG.pCore_eq_iSup, Subgroup.map_iSup]
    refine iSup_le fun N => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hN => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hN2 => ?_
    exact le_iSup_of_le (N.map ψ.toMonoidHom) (le_iSup_of_le (hN.map _ ψ.surjective)
      (le_iSup_of_le (hN2.map _) le_rfl))
  refine le_antisymm (key φ) ?_
  have h := map_map_symm φ.symm (CFSG.Open.pCore p E)
  rw [MulEquiv.symm_symm] at h
  calc CFSG.Open.pCore p E = ((CFSG.Open.pCore p E).map φ.symm.toMonoidHom).map φ.toMonoidHom :=
        h.symm
    _ ≤ (CFSG.Open.pCore p E).map φ.toMonoidHom := map_mono (key φ.symm)

theorem le_openPCore {E : Type} [Group E] {p : ℕ} {N : Subgroup E} (hN : N.Normal)
    (hN2 : IsPGroup p N) : N ≤ CFSG.Open.pCore p E :=
  le_sSup ⟨hN, hN2⟩

theorem MinCounter.exists_config {Ω : Set (Subgroup G)} (hM : MinCounter Ω) (hI : Sec3Inputs) :
    ∃ K J R T S : Subgroup G, Config Ω K J R T S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.setting
  obtain ⟨K, hK⟩ : Ω.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hM.not_conc fun K hK => absurd (h ▸ hK) (Set.notMem_empty K)
  obtain ⟨R, hR⟩ := Sec3Setting.exists_sylow K
  obtain ⟨S, hS, hRS, hgood⟩ := hM.exists_sylow_good hK hR
  obtain ⟨hπ, -, -⟩ := hM.nbr_facts hI hK
  obtain ⟨J₀, hJ₀, -⟩ := hπ.nontrivial
  have hJ₀' : adj Ω K J₀ := hJ₀
  have hXN : sSup (perp Ω K) ≤ normalizer (K : Set G) := hΩ.sSup_perp_le_normalizer hI.h22 hK
  obtain ⟨T₀, hT₀⟩ := Sec3Setting.exists_sylow J₀
  have hT₀' := isSylowOf_iff_card.mp hT₀
  have hJ₀X : J₀ ≤ sSup (perp Ω K) := le_sSup (hΩ.mem_perp_of_le_normalizer hJ₀'.1 hJ₀'.2.2)
  obtain ⟨P, hP, hT₀P⟩ := exists_isSylowOf_le (hT₀'.1.trans hJ₀X) (IsPGroup.of_card hT₀'.2)
  obtain ⟨x, hx, hPx⟩ := exists_conj_of_isSylowOf hgood hP
  have hTS : rightConjugate T₀ x⁻¹ ≤ S := by
    intro y hy
    rw [mem_rightConjugate_iff, inv_inv] at hy
    have h1 := hT₀P hy
    rw [hPx, mem_rightConjugate_iff] at h1
    have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rw [e] at h1
    exact h1.1
  exact ⟨K, rightConjugate J₀ x⁻¹, R, rightConjugate T₀ x⁻¹, S,
    ⟨hK, adj_rightConjugate_of_mem_normalizer hΩ.conj_mem hJ₀' (inv_mem (hXN hx)), hR,
      isSylowOf_rightConjugate hT₀ x⁻¹, hS, hRS, hTS, hgood⟩⟩

theorem MinCounter.false_of_goldschmidt {Ω : Set (Subgroup G)} (hM : MinCounter Ω)
    (hI : Sec3Inputs) (hgold : GoldschmidtTheoremA) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.setting
  obtain ⟨K, J, R, T, S, hc⟩ := hM.exists_config hI
  set Z := omega1 R ⊔ omega1 T with hZdef
  have hZab := hc.isElemAbelian_Z hM hI
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => by
    have h1 : (⟨a, ha⟩ : ↥Z) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := hZab.1.is_comm.comm _ _
    simpa using congrArg Subtype.val h1
  have hclosed := hc.lemma316 hM hI goldschmidtEscape
  obtain ⟨P₀, hP₀⟩ := exists_sylow_eq_of_isSylowOf_top hc.sylowS
  have hZP₀ : Z ≤ (P₀ : Subgroup G) := hP₀ ▸ hc.Z_le
  obtain ⟨hGa, hGb, hGc⟩ := hgold G P₀ Z hZP₀ hZab.1 (by rw [hP₀]; exact hclosed)
  set M := normalClosure (Z : Set G) with hMdef
  have hMn : M.Normal := normalClosure_normal
  have hZM : Z ≤ M := subset_normalClosure
  have hO : CFSG.Open.goldschmidtOddCore ↥M = ⊥ := oddCore_eq_bot_of_normal' hΩ.oddCore hMn
  set π := QuotientGroup.mk' (CFSG.Open.goldschmidtOddCore ↥M) with hπdef
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hO]
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hOE : ∀ N : Subgroup (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M), N.Normal →
      Odd (Nat.card N) → N = ⊥ := by
    intro N hN hNodd
    have h : CFSG.oddCore (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) = ⊥ :=
      oddCore_quotient_oddCore ↥M
    rw [eq_bot_iff, ← h]
    exact le_sSup ⟨hN, hNodd⟩
  set Zb := (Z.subgroupOf M).map π with hZbdef
  have hGb' : Zb = CFSG.Open.pCore 2 (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) ⊔
      Subgroup.closure {t | t ∈ (S.subgroupOf M).map π ⊓
        CFSG.Open.goldschmidtLayer (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) ∧ t ^ 2 = 1} := by
    rw [hZbdef, ← hP₀]
    exact hGb
  have hQZ : CFSG.Open.pCore 2 (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) ≤ Zb := by
    rw [hGb']
    exact le_sup_left
  set Q₀ := ((CFSG.Open.pCore 2 (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M)).comap π).map M.subtype
    with hQ₀def
  have hQ₀Z : Q₀ ≤ Z := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨z, hz, hzm⟩ := hQZ hm
    have hzm' : z = m := hπinj hzm
    rw [← hzm']
    exact hz
  have hQ₀n : Q₀.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨m, hm, rfl⟩ := hx
    have h1 : (conjQuot hMn g) (π m) ∈
        CFSG.Open.pCore 2 (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) := by
      rw [← openPCore_map_eq 2 (conjQuot hMn g)]
      exact ⟨π m, hm, rfl⟩
    rw [hπdef, conjQuot_mk] at h1
    exact ⟨⟨g * m * g⁻¹, hMn.conj_mem m m.2 g⟩, h1, rfl⟩
  have hQ₀bot := hc.eq_bot_of_normal_le hM hI hQ₀n hQ₀Z
  have hQbot : CFSG.Open.pCore 2 (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨m, rfl⟩ := hπsurj q
    have hm : (m : G) ∈ Q₀ := ⟨m, hq, rfl⟩
    rw [hQ₀bot, mem_bot] at hm
    rw [mem_bot, show m = 1 from Subtype.ext hm, map_one]
  have hlayer : CFSG.Open.goldschmidtLayer (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) =
      CFSG.layer (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) :=
    CFSG.Adapters.goldschmidtLayer_eq_foundations _
  have hLE : CFSG.layer (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) = ⊤ := by
    have hGa' : CFSG.Open.pCore 2 (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) ⊔
        CFSG.Open.goldschmidtLayer (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) = ⊤ := hGa
    rw [hQbot, bot_sup_eq, hlayer] at hGa'
    exact hGa'
  have hO2E : ∀ N : Subgroup (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M), N.Normal →
      IsPGroup 2 N → N = ⊥ := fun N hN hN2 =>
    le_bot_iff.mp ((le_openPCore hN hN2).trans hQbot.le)
  have hZE := center_eq_bot_of hOE hO2E
  have hCE : ∀ L : Subgroup (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M), IsComponent L →
      CFSG.Open.goldschmidtSimpleType (↥L ⧸ center ↥L) := fun L hL =>
    hGc L ((CFSG.isComponent_iff_open L).mp hL)
  set Pb := (S.subgroupOf M).map π with hPbdef
  have hSM : IsSylowOf 2 (S ⊓ M) M :=
    isSylowOf_inf le_top (by rw [normalizer_eq_top_iff.mpr hMn]) hc.sylowS
  have hcardE : Nat.card (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) = Nat.card M :=
    (Nat.card_congr (MulEquiv.ofBijective π ⟨hπinj, hπsurj⟩).toEquiv).symm
  have hPb : IsSylowOf 2 Pb ⊤ := by
    rw [isSylowOf_iff_card]
    refine ⟨le_top, ?_⟩
    rw [card_top, hcardE, hPbdef, card_map_of_injective hπinj]
    have h1 : Nat.card (S.subgroupOf M) = Nat.card ↥(S ⊓ M) := by
      rw [← card_map_of_injective M.subtype_injective, subgroupOf_map_subtype]
    rw [h1]
    exact (isSylowOf_iff_card.mp hSM).2
  have hZb : Zb = omega1 Pb := by
    rw [hGb', hQbot, bot_sup_eq, hlayer, hLE, inf_top_eq]
    rfl
  set A₁ := ((omega1 R).subgroupOf M).map π with hA₁def
  set B₁ := ((omega1 T).subgroupOf M).map π with hB₁def
  have hRM : omega1 R ≤ M := le_sup_left.trans hZM
  have hTM : omega1 T ≤ M := le_sup_right.trans hZM
  have hAB : A₁ ⊔ B₁ = omega1 Pb := by
    rw [← hZb, hA₁def, hB₁def, hZbdef, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hRM hTM]
  have hinf : A₁ ⊓ B₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨a, haR, rfl⟩, ⟨b, hbT, hba⟩⟩
    have hba' : b = a := hπinj hba
    rw [hba'] at hbT
    have h1 : (a : G) ∈ R ⊓ T := mem_inf.mpr ⟨omega1_le R haR, omega1_le T hbT⟩
    rw [hc.inf_RT hΩ, mem_bot] at h1
    rw [mem_bot, show a = 1 from Subtype.ext h1, map_one]
  have hZbab : IsMulCommutative (omega1 Pb) := by
    rw [← hZb]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    obtain ⟨a, haZ, hax⟩ := x.2
    obtain ⟨b, hbZ, hby⟩ := y.2
    change (x : ↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) * y = y * x
    rw [← hax, ← hby, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hZcomm _ haZ _ hbZ)
  have hA1 : A₁ ≠ ⊥ := by
    obtain ⟨E₄, hE₄R, -, hE₄4⟩ := exists_fourGroup_le (hΩ.rank K hc.mem R hc.sylowR).1
    have hE₄2 : IsPGroup 2 E₄ := IsPGroup.of_card (n := 2) (by rw [hE₄4]; norm_num)
    have hE₄1 : E₄ ≠ ⊥ := fun h => by
      rw [h, card_bot] at hE₄4
      norm_num at hE₄4
    obtain ⟨e, heE, he2⟩ := exists_involution hE₄2 hE₄1
    have heR : e ∈ omega1 R :=
      mem_omega1_of_sq (hE₄R heE) (by rw [← he2]; exact pow_orderOf_eq_one e)
    intro h
    have h1 : π ⟨e, hRM heR⟩ ∈ A₁ := ⟨⟨e, hRM heR⟩, heR, rfl⟩
    rw [h, mem_bot, ← map_one π] at h1
    have h3 : e = 1 := congrArg Subtype.val (hπinj h1)
    rw [h3, orderOf_one] at he2
    exact absurd he2 (by decide)
  have hpure : ∀ z m : (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M), (z ∈ A₁ ∨ z ∈ B₁) →
      m⁻¹ * z * m ∈ omega1 Pb → m⁻¹ * z * m ∈ A₁ ∨ m⁻¹ * z * m ∈ B₁ := by
    intro z m hz hzm
    obtain ⟨m₀, rfl⟩ := hπsurj m
    have hz' : ∃ z₀ : ↥M, ((z₀ : G) ∈ omega1 R ∨ (z₀ : G) ∈ omega1 T) ∧ π z₀ = z := by
      rcases hz with ⟨z₀, hz₀, rfl⟩ | ⟨z₀, hz₀, rfl⟩
      · exact ⟨z₀, Or.inl hz₀, rfl⟩
      · exact ⟨z₀, Or.inr hz₀, rfl⟩
    obtain ⟨z₀, hz₀, rfl⟩ := hz'
    rw [← hZb] at hzm
    obtain ⟨w, hw, hwe⟩ := hzm
    have hw' : w = m₀⁻¹ * z₀ * m₀ := hπinj (by rw [hwe, map_mul, map_mul, map_inv])
    have hwZ : (m₀ : G)⁻¹ * z₀ * m₀ ∈ Z := by
      have h1 := mem_subgroupOf.mp hw
      rw [hw'] at h1
      simpa using h1
    have e : π (m₀⁻¹ * z₀ * m₀) = (π m₀)⁻¹ * π z₀ * π m₀ := by rw [map_mul, map_mul, map_inv]
    rcases hc.pure_of_conj hM hI hz₀ hwZ with h | h
    · exact Or.inl ⟨m₀⁻¹ * z₀ * m₀, by rw [SetLike.mem_coe, mem_subgroupOf]; simpa using h, e⟩
    · exact Or.inr ⟨m₀⁻¹ * z₀ * m₀, by rw [SetLike.mem_coe, mem_subgroupOf]; simpa using h, e⟩
  have hfixZ : ∀ r ∈ R, ∀ z ∈ omega1 Pb, (conjQuot hMn r) z = z := by
    intro r hr z hz
    rw [← hZb] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    rw [hπdef, conjQuot_mk]
    congr 1
    apply Subtype.ext
    change r * (z₀ : G) * r⁻¹ = z₀
    have h1 := mem_centralizer_iff.mp (hc.Z_le_centralizer hM hI (mem_subgroupOf.mp hz₀)) r hr
    rw [h1, mul_inv_cancel_right]
  have hRfix : R ≤ compFix hMn := fun r hr L hL =>
    map_eq_of_forall_fix hLE hZE hCE hPb hZbab (conjQuot hMn r) (hfixZ r hr) hL
  have htop : compFix hMn = ⊤ := by
    have := compFix_normal hMn
    rw [eq_top_iff, ← hc.normalClosure_eq_top hM hI]
    exact normalClosure_le_normal hRfix
  obtain ⟨g', hg'⟩ := hc.exists_omega1_conj hM hI
  have hg'fix : g'⁻¹ ∈ compFix hMn := by
    rw [htop]
    exact mem_top _
  have hψA : A₁.map (conjQuot hMn g'⁻¹).toMonoidHom = B₁ := by
    ext y
    constructor
    · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      refine ⟨⟨g'⁻¹ * r * g'⁻¹⁻¹, hMn.conj_mem r r.2 g'⁻¹⟩, ?_, ?_⟩
      · have hr' : (r : G) ∈ omega1 R := hr
        show _ ∈ (omega1 T).subgroupOf M
        rw [mem_subgroupOf, ← hg', mem_rightConjugate_iff]
        simpa [mul_assoc] using hr'
      · rw [hπdef]
        exact (conjQuot_mk hMn g'⁻¹ r).symm
    · rintro ⟨t, ht, rfl⟩
      have ht' : (t : G) ∈ rightConjugate (omega1 R) g' := by
        rw [hg']
        exact ht
      rw [mem_rightConjugate_iff] at ht'
      refine ⟨π ⟨g' * t * g'⁻¹, hMn.conj_mem t t.2 g'⟩, ⟨_, ht', rfl⟩, ?_⟩
      change (conjQuot hMn g'⁻¹) (π ⟨g' * t * g'⁻¹, _⟩) = π t
      rw [hπdef, conjQuot_mk]
      congr 1
      apply Subtype.ext
      change g'⁻¹ * (g' * (t : G) * g'⁻¹) * g'⁻¹⁻¹ = t
      group
  obtain ⟨L, hL, hW, hLpure⟩ := exists_pure_component hLE hZE hCE hPb hZbab hAB hA1 hpure
  exact false_of_pure_component hAB hinf hW hLpure (conjQuot hMn g'⁻¹) (hg'fix L hL) hψA

theorem asc76Theorem4_of (h22 : Lemma22Four) (h26 : L26.Asc76Lemma26) (h28 : Asc76Lemma28)
    (hgold : GoldschmidtTheoremA) : Asc76Theorem4 :=
  asc76Theorem4_of_forall_not_minCounter fun _ _ _ _ hM =>
    hM.false_of_goldschmidt ⟨h22, benderFacts, h26, h28⟩ hgold

theorem asc76Theorem1_of (h22 : Lemma22Four) (h26 : L26.Asc76Lemma26) (h28 : Asc76Lemma28)
    (hgold : GoldschmidtTheoremA) : Asc76Theorem1 :=
  asc76Theorem1_of_theorem4 benderFacts (asc76Theorem4_of h22 h26 h28 hgold)

end CFSG.ComponentClassification.Asc76X
