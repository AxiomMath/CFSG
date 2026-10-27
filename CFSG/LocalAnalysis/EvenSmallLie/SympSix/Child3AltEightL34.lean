module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3AltEightFix
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBMSp6EvenLinearAmbientExclusion
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6TwoFactorAltLayer
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6TwoFactorGroup
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6TwoFactorModel
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.KProperOddCoreFreeLayer
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.SteinbergBVSp6LayerStatements

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.Child3

open Subgroup Module Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.RadicalLabels
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
open LinearFlag GL3TwoFixedModel FieldFourCover
open CFSG.LocalAnalysis.ComponentInitial.SteinbergBM
open CFSG.EvenSmallLie.Child3.AltEight
open LinearMap (BilinForm)

variable {G : Type} [Group G] {L : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
  (he : IsSymplecticBasis b e) (z : G)

theorem alt8_even_linear_false [Finite G] (hGs : IsSimpleGroup G)
    (hGnab : ∃ x y : G, x * y ≠ y * x) (hzL : z ∈ centralizer (L : Set G))
    (hLz : L ⊔ zpowers z = centralizer ({z} : Set G)) (hinf : L ⊓ zpowers z = ⊥)
    (hz : orderOf z = 2) [FiniteDimensional (ZMod 2) V] (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) {C : Subgroup G} (hCel : IsElementaryAbelian 2 C)
    (hCcard : Nat.card C = 512) (hA₂C : sp6A₂ φ e ≤ C)
    (hfixz : ∀ c ∈ C, c * z = z * c ↔ c ∈ sp6A₂ φ e) (hA₂card : Nat.card (sp6A₂ φ e) = 2 ^ 6)
    (hcomm : {x | ∃ c ∈ C, c⁻¹ * z⁻¹ * c * z = x} = tauSet φ e (fun B => ∀ i, B i i = 0))
    (hCN₂ : C ≤ sp6N₂ φ e z)
    (hN₂u : ∀ F : Subgroup G, F ≤ sp6N₂ φ e z → IsElementaryAbelian 2 F → Nat.card F = 512 →
      F = C)
    (hzX : z ∈ layX C) (hLX : ∀ g, leviHom φ he g ∈ layX C)
    (hCaN : centralizer {laya C z} = ((sp6N₂ φ e z).subgroupOf (layX C)).map (layπ C))
    (hιinj : Function.Injective (layLeviHom C (leviHom φ he) hLX))
    (hιrange : (layLeviHom C (leviHom φ he) hLX).range = layJL C (leviHom φ he))
    (ha2 : orderOf (laya C z) = 2)
    (hJCa : layJL C (leviHom φ he) ≤ centralizer {laya C z})
    (hRoinv : ∀ r ∈ layRo C, (laya C z)⁻¹ * r * laya C z = r⁻¹)
    (hθCa : Set.InjOn (layθ C) (centralizer {laya C z}))
    (hāo : orderOf (layaBar C z) = 2)
    (hJCā : layJLBar C (leviHom φ he) ≤ centralizer {layaBar C z})
    (hCā : zpowers (layaBar C z) ⊔ layJLBar C (leviHom φ he) = centralizer {layaBar C z})
    (hCD : centralizer (layDstar C (leviHom φ he) : Set (LayY C)) = ⊥)
    (hQmap : (normalClosure (layJL C (leviHom φ he) : Set (LayF C))).map (layθ C) =
      layDstar C (leviHom φ he))
    (hQcomap : (layDstar C (leviHom φ he)).comap (layθ C) =
      layRo C ⊔ normalClosure (layJL C (leviHom φ he) : Set (LayF C)))
    (hQcen : (center (normalClosure (layJL C (leviHom φ he) : Set (LayF C)))).map
      (normalClosure (layJL C (leviHom φ he) : Set (LayF C))).subtype =
        normalClosure (layJL C (leviHom φ he) : Set (LayF C)) ⊓ layRo C)
    (hsimple : LayerSimple C z (leviHom φ he)) {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f) {k : Type}
    [Field k] (hk : Nat.card k = 2 ^ f)
    (η : layDstar C (leviHom φ he) ≃* projectiveSL n k) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmz2 := SteinbergBM.mult_zmod_two_cases
  set X := layX C with hXdef
  set A₂ := sp6A₂ φ e with hA₂def
  set θ := layθ C with hθdef
  set πX := layπ C with hπXdef
  set Q := normalClosure (layJL C (leviHom φ he) : Set (LayF C)) with hQdef
  set Ro := layRo C with hRodef
  set a := laya C z with hadef
  set ā := layaBar C z with hādef
  set JL := layJL C (leviHom φ he) with hJLdef
  set JLBar := layJLBar C (leviHom φ he) with hJLBardef
  set D := layDstar C (leviHom φ he) with hDdef
  set ι := layLeviHom C (leviHom φ he) hLX with hιdef
  have hDn : D.Normal := Subgroup.normalClosure_normal
  have : Q.Normal := Subgroup.normalClosure_normal
  obtain ⟨hDs, hDnab, hJD, hact⟩ := hsimple
  have hā2 : ā * ā = 1 := by
    have h := pow_orderOf_eq_one ā
    rwa [hāo, pow_two] at h
  have hāinv : ā⁻¹ = ā := inv_eq_of_mul_eq_one_right hā2
  have hιJL : ∀ g, ι g ∈ JL := fun g => by
    rw [← hιrange]
    exact ⟨g, rfl⟩
  have hJLCa' : ∀ g, ι g ∈ centralizer {a} := fun g => hJCa (hιJL g)
  have hψinj : Function.Injective (θ.comp ι) := by
    intro g g' hgg
    exact hιinj (hθCa (hJLCa' g) (hJLCa' g') hgg)
  have hψrange : (θ.comp ι).range = JLBar := by
    rw [MonoidHom.range_comp, hιrange]
    rfl
  set κ : JLBar ≃* GL (Fin 3) (ZMod 2) :=
    ((MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr hψrange)).symm with hκ
  have hκsymm : ∀ g, ((κ.symm g : JLBar) : LayY C) = θ (ι g) := fun _ => rfl
  have : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := isSimpleGroup_GL_three_two
  have : IsSimpleGroup JLBar := κ.isSimpleGroup
  have : IsSimpleGroup D := hDs
  have hSnab : ∃ x y : JLBar, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := SteinbergBM.exists_mul_ne_mul_GL_three_two
    refine ⟨κ.symm x, κ.symm y, fun h => hxy (κ.symm.injective ?_)⟩
    rw [map_mul, map_mul, h]
  have hSn : (JLBar.subgroupOf (centralizer {ā})).Normal := by
    have haN : ā ∈ normalizer (JLBar : Set (LayY C)) :=
      centralizer_le_normalizer _ (mem_centralizer_iff.2 fun j hj =>
        mem_centralizer_singleton_iff.1 (hJCā hj))
    rw [normal_subgroupOf_iff_le_normalizer hJCā, ← hCā]
    exact sup_le (zpowers_le.2 haN) le_normalizer
  have hact' : ∃ d ∈ D, ā * d * ā⁻¹ ≠ d := by
    obtain ⟨d, hd, hne⟩ := hact
    refine ⟨d, hd, ?_⟩
    rw [hāinv] at hne ⊢
    exact hne
  obtain ⟨hn3, hf2, -, -, -, -, haD, hn3', hchar, σ, hσ, -, -, B, e₀, -, hint, hlab⟩ :=
    SteinbergBM.even_linear_simple_layer_core hāo hact' hJD.le hJCā hSn hSnab κ hn hf hk η
  subst hn3
  have hk4 : Nat.card k = 4 := by rw [hk, hf2]; norm_num
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk4]; norm_num)
  set χ : D ≃* projectiveSL 3 k := η.trans (conjAut 3 k B * dualAut 3 k ^ e₀) with hχ
  have hχapp : ∀ d, χ d = (conjAut 3 k B * dualAut 3 k ^ e₀) (η d) := fun _ => rfl
  have hχint : ∀ d : D, χ (MulAut.conjNormal ā d) = fieldAut 3 k σ (χ d) := hint
  have hlabι : ∀ (g : GL (Fin 3) (ZMod 2)) (h : θ (ι g) ∈ D), χ ⟨θ (ι g), h⟩ =
      binaryEmbed k rfl g := by
    intro g h
    have h1 : (⟨θ (ι g), h⟩ : D) = ⟨(κ.symm g : JLBar), hJD.le (κ.symm g).2⟩ :=
      Subtype.ext (hκsymm g).symm
    rw [h1, hχapp, hlab, MulEquiv.apply_symm_apply]
  have hθsurj : Function.Surjective θ := QuotientGroup.mk'_surjective _
  have hθker : θ.ker = Ro := QuotientGroup.ker_mk' _
  have hπsurj : Function.Surjective πX := QuotientGroup.mk'_surjective _
  have hπker : πX.ker = C.subgroupOf X := QuotientGroup.ker_mk' _
  have hRodd : Nat.Coprime 2 (Nat.card θ.ker) := by
    rw [hθker]
    exact CFSG.pPrimeCore_coprime_card
  have hZ : ∀ c ∈ Q, θ c = 1 → ∀ q ∈ Q, q * c = c * q := by
    intro c hc hθc q hq
    have hcR : c ∈ Ro := by
      rw [← hθker]
      exact hθc
    have hcZ : c ∈ (center Q).map Q.subtype := by
      rw [hQcen]
      exact mem_inf.2 ⟨hc, hcR⟩
    obtain ⟨c', hc', rfl⟩ := hcZ
    exact congrArg Subtype.val (mem_center_iff.1 hc' ⟨q, hq⟩)
  have hQcomap' : D.comap θ = θ.ker ⊔ Q := by rw [hθker]; exact hQcomap
  have hθa : θ a = ā := rfl
  have hadef2 : a = πX ⟨z, hzX⟩ := laya_eq C z hzX
  have ha2' : a ^ 2 = 1 := by rw [← ha2]; exact pow_orderOf_eq_one a
  have hJLQ : JL ≤ Q := le_normalClosure
  have hRinv : ∀ r ∈ θ.ker, a⁻¹ * r * a = r⁻¹ := fun r hr => hRoinv r (by rw [← hθker]; exact hr)
  have hιX : ∀ g, ι g = πX ⟨leviHom φ he g, hLX g⟩ := fun g => rfl
  have hιD : ∀ g, θ (ι g) ∈ D := fun g => hJD.le ⟨ι g, hιJL g, rfl⟩
  obtain ⟨hsq1, hsq2, hsq3⟩ := SteinbergBM.glTrans_sq
  have htQ : ι glTransThreeOne ∈ Q := hJLQ (hιJL _)
  have ht2 : ι glTransThreeOne ^ 2 = 1 := by rw [← map_pow, hsq2, map_one]
  have hχt : χ ⟨θ (ι glTransThreeOne), hιD _⟩ = proj 3 k (unipU k 0 0 1) := by
    rw [hlabι, binaryEmbed_glTransThreeOne]
  have hCa' : centralizer {ā} ≤ zpowers ā ⊔ D := by
    rw [← hCā]
    exact sup_le_sup_left hJD.le _
  obtain ⟨ηY, -, -, hηker, hηconj, -⟩ :=
    SteinbergBM.even_linear_layer_extension_core hk4 hσ χ hχint hCD hCa'
  have hθ1' : ∀ x : LayF C, x ^ 2 = 1 → θ x = 1 → x = 1 := fun x hx h =>
    eq_one_of_mem_ker_of_pow hRodd h (m := 1) (by rw [pow_one]; exact hx)
  have hinner : ∀ x : LayF C, x ^ 2 = 1 → θ x ∈ D → θ x ≠ 1 →
      ∃ q ∈ Q, q * x * q⁻¹ = ι glTransThreeOne := by
    intro x hx2 hxD hx1
    have hord : orderOf (χ ⟨θ x, hxD⟩) = 2 := by
      apply orderOf_eq_prime
      · rw [← map_pow]
        have : (⟨θ x, hxD⟩ : D) ^ 2 = 1 := Subtype.ext (by
          rw [Subgroup.coe_pow, ← map_pow, hx2, map_one]
          rfl)
        rw [this, map_one]
      · intro h
        apply hx1
        have h' := χ.injective (h.trans (map_one χ).symm)
        exact congrArg Subtype.val h'
    obtain ⟨p, hp⟩ := exists_conj_eq_projW hk4 hord
    have hd : χ.symm p * ⟨θ x, hxD⟩ * (χ.symm p)⁻¹ = ⟨θ (ι glTransThreeOne), hιD _⟩ :=
      χ.injective (by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hp, hχt])
    exact exists_conj_eq_of_conj_map hRodd hZ hQmap hQcomap' hx2 htQ ht2 hxD (χ.symm p).2
      (congrArg Subtype.val hd)
  have houter : ∀ x : LayF C, x ^ 2 = 1 → θ x ∉ D → ∃ w, w * x * w⁻¹ = a := by
    intro x hx2 hxD
    have hθx2 : θ x ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
    rcases hmz2 (ηY (θ x)) with h | h
    · exact absurd (hηker _ hθx2 h) hxD
    · obtain ⟨y, hy⟩ := hηconj _ hθx2 h
      exact exists_conj_eq_of_inverts hRodd hθsurj hRinv hy
  have : IsElementaryAbelian 2 C := hCel
  have hC₂ab : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c := fun c hc d hd =>
    congrArg Subtype.val (hCel.toIsMulCommutative.is_comm.comm ⟨c, hc⟩ ⟨d, hd⟩)
  have hC₂el : ∀ c ∈ C, c ^ 2 = 1 := fun c hc =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) c hc
  have hzC : ∀ c ∈ C, z⁻¹ * c * z ∈ C := fun c hc => (mem_set_normalizer_iff''.1 hzX c).1 hc
  have htC : ∀ c ∈ C,
      leviHom φ he glTransThreeOne * c * (leviHom φ he glTransThreeOne)⁻¹ ∈ C :=
    fun c hc => (mem_normalizer_iff.1 (hLX glTransThreeOne) c).1 hc
  have hzA : C ⊓ centralizer ({z} : Set G) = A₂ := by
    ext c
    rw [mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun ⟨hc, h⟩ => (hfixz c hc).1 h, fun h => ⟨hA₂C h, (hfixz c (hA₂C h)).2 h⟩⟩
  have hEout : ∀ x : X, πX x ^ 2 = 1 → θ (πX x) ∉ D →
      Nat.card ↥(C ⊓ centralizer ({(x : G)} : Set G)) = 2 ^ 6 := by
    intro x hx2 hD
    obtain ⟨w, hw⟩ := houter _ hx2 hD
    obtain ⟨xw, rfl⟩ := hπsurj w
    have hker : (⟨z, hzX⟩ : X)⁻¹ * (xw * x * xw⁻¹) ∈ πX.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hadef2, map_mul, map_mul, map_inv, hw,
        inv_mul_cancel]
    rw [hπker, mem_subgroupOf] at hker
    have hc : z⁻¹ * ((xw : G) * x * (xw : G)⁻¹) ∈ C := hker
    calc Nat.card ↥(C ⊓ centralizer ({(x : G)} : Set G))
        = Nat.card ↥(C ⊓ centralizer ((fun m => (xw : G) * m * (xw : G)⁻¹) '' {(x : G)})) :=
          (card_inf_centralizer_conj xw.2 _).symm
      _ = Nat.card ↥(C ⊓ centralizer ({z * (z⁻¹ * ((xw : G) * x * (xw : G)⁻¹))} : Set G)) := by
          rw [Set.image_singleton, mul_inv_cancel_left]
      _ = Nat.card ↥(C ⊓ centralizer ({z} : Set G)) := by
          rw [inf_centralizer_mul hC₂ab hc]
      _ = 2 ^ 6 := by rw [hzA, hA₂card]
  have h6 : 2 ^ 6 ≤ Nat.card ↥(C ⊓ centralizer {z * leviHom φ he glTransThreeOne}) := by
    set x₀ : X := ⟨z, hzX⟩ * ⟨leviHom φ he glTransThreeOne, hLX _⟩ with hx₀
    have hπx₀ : πX x₀ = a * ι glTransThreeOne := by
      rw [hx₀, map_mul, ← hadef2, hιX]
    have hat : a * ι glTransThreeOne = ι glTransThreeOne * a :=
      (mem_centralizer_singleton_iff.1 (hJLCa' _)).symm
    have hx₀2 : πX x₀ ^ 2 = 1 := by
      have ha' : a * a = 1 := by rw [← pow_two]; exact ha2'
      have ht' : ι glTransThreeOne * ι glTransThreeOne = 1 := by rw [← pow_two]; exact ht2
      calc πX x₀ ^ 2 = a * (ι glTransThreeOne * a) * ι glTransThreeOne := by
            rw [hπx₀, pow_two]; group
        _ = a * a * (ι glTransThreeOne * ι glTransThreeOne) := by rw [← hat]; group
        _ = 1 := by rw [ha', ht', one_mul]
    have hx₀D : θ (πX x₀) ∉ D := by
      intro h
      apply haD
      have h1 : ā = θ (πX x₀) * (θ (ι glTransThreeOne))⁻¹ := by
        rw [hπx₀, map_mul, hθa, mul_inv_cancel_right]
      rw [h1]
      exact mul_mem h (inv_mem (hιD _))
    have h := hEout x₀ hx₀2 hx₀D
    exact h.symm.le
  have h5 := card_inf_centralizer_leviTrans_le φ he hzL hC₂ab hzC htC hA₂C hfixz hA₂card hcomm h6
  have hEin : ∀ x : X, πX x ≠ 1 → πX x ^ 2 = 1 → θ (πX x) ∈ D →
      Nat.card ↥(C ⊓ centralizer ({(x : G)} : Set G)) ≤ 2 ^ 5 := by
    intro x hx1 hx2 hD
    have hθx1 : θ (πX x) ≠ 1 := fun h => hx1 (hθ1' _ hx2 h)
    obtain ⟨q, -, hq⟩ := hinner _ hx2 hD hθx1
    obtain ⟨xq, rfl⟩ := hπsurj q
    have hker : (⟨leviHom φ he glTransThreeOne, hLX _⟩ : X)⁻¹ * (xq * x * xq⁻¹) ∈
        πX.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hιX, map_mul, map_mul, map_inv, hq,
        inv_mul_cancel]
    rw [hπker, mem_subgroupOf] at hker
    have hc : (leviHom φ he glTransThreeOne)⁻¹ * ((xq : G) * x * (xq : G)⁻¹) ∈ C := hker
    calc Nat.card ↥(C ⊓ centralizer ({(x : G)} : Set G))
        = Nat.card ↥(C ⊓ centralizer ((fun m => (xq : G) * m * (xq : G)⁻¹) '' {(x : G)})) :=
          (card_inf_centralizer_conj xq.2 _).symm
      _ = Nat.card ↥(C ⊓ centralizer ({leviHom φ he glTransThreeOne *
            ((leviHom φ he glTransThreeOne)⁻¹ * ((xq : G) * x * (xq : G)⁻¹))} : Set G)) := by
          rw [Set.image_singleton, mul_inv_cancel_left]
      _ = Nat.card ↥(C ⊓ centralizer ({leviHom φ he glTransThreeOne} : Set G)) := by
          rw [inf_centralizer_mul hC₂ab hc]
      _ ≤ 2 ^ 5 := h5
  have hlevW : ∀ i : Fin 2, ∃ s : GL (Fin 3) (ZMod 2), s ^ 2 = 1 ∧
      binaryEmbed k rfl s ∈ projRad k i ∧
      Nat.card ↥(C ⊓ centralizer (leviHom φ he '' {s, glTransThreeOne})) ≤ 2 ^ 4 := by
    intro i
    fin_cases i
    · refine ⟨glTransTwoOne, hsq1, ?_,
        card_inf_centralizer_leviPair_le φ he hA₂C h5 (Or.inl rfl)⟩
      rw [binaryEmbed_glTransTwoOne]
      exact mem_projRad_zero.2 ⟨1, 0, rfl⟩
    · refine ⟨glTransThreeTwo, hsq3, ?_,
        card_inf_centralizer_leviPair_le φ he hA₂C h5 (Or.inr rfl)⟩
      rw [binaryEmbed_glTransThreeTwo]
      exact mem_projRad_one.2 ⟨1, 0, rfl⟩
  have huniq : ∀ U : Subgroup G, U ≤ normalizer (C : Set G) → (∀ u ∈ U, u ^ 2 = 1) →
      (∀ u ∈ U, ∀ v ∈ U, u * v = v * u) → Nat.card U = Nat.card C → U = C := by
    intro U hUX' hU2 hUab hUcard
    have hUX : U ≤ X := hUX'
    by_contra hne
    have hUC : ¬ U ≤ C := fun h => hne (Subgroup.eq_of_le_of_card_ge h (by rw [hUcard]))
    obtain ⟨x₀, hx₀U, hx₀C⟩ := Set.not_subset.1 hUC
    set ρ := πX.comp (U.subgroupOf X).subtype with hρ
    have hρker : ∀ u : U.subgroupOf X, u ∈ ρ.ker ↔ ((u : X) : G) ∈ C := by
      intro u
      rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hπker,
        mem_subgroupOf]
      rfl
    have hUcard' : Nat.card (U.subgroupOf X) = 2 ^ 9 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hUX).toEquiv, hUcard, hCcard]
      norm_num
    have hcard := Subgroup.card_ker_mul_card_range ρ
    rw [hUcard'] at hcard
    have hkerle : ∀ M : Set G, (∀ c ∈ C, (∀ u ∈ U, u * c = c * u) → c ∈ centralizer M) →
        Nat.card ρ.ker ≤ Nat.card ↥(C ⊓ centralizer M) := by
      intro M hM
      refine Nat.card_le_card_of_injective
        (fun u => ⟨(((u : U.subgroupOf X) : X) : G), ?_⟩) ?_
      · have hu := (hρker _).1 u.2
        exact mem_inf.2 ⟨hu, hM _ hu fun v hv =>
          hUab v hv _ (mem_subgroupOf.1 (u : U.subgroupOf X).2)⟩
      · intro u v h
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext (Subtype.ext h'))
    have hB2 : ∀ y ∈ ρ.range, y ^ 2 = 1 := by
      rintro _ ⟨u, rfl⟩
      have hu : u ^ 2 = 1 := Subtype.ext (Subtype.ext (hU2 _ (mem_subgroupOf.1 u.2)))
      rw [← map_pow, hu, map_one]
    have hρ1 : ∀ u : U.subgroupOf X, ((u : X) : G) ∉ C → ρ u ≠ 1 :=
      fun u hu h => hu ((hρker u).1 h)
    have hx₀X := hUX hx₀U
    by_cases hout : ∃ u : U.subgroupOf X, θ (ρ u) ∉ D
    ·
      obtain ⟨u, hu⟩ := hout
      have hu2 : ρ u ^ 2 = 1 := hB2 _ ⟨u, rfl⟩
      obtain ⟨w, hw⟩ := houter _ hu2 hu
      obtain ⟨xw, rfl⟩ := hπsurj w
      set U' := U.map (MulAut.conj (xw : G)).toMonoidHom with hU'
      have hU'N : U' ≤ sp6N₂ φ e z := by
        rintro _ ⟨v, hv, rfl⟩
        have hvX := hUX hv
        set vX : U.subgroupOf X := ⟨⟨v, hvX⟩, mem_subgroupOf.2 hv⟩ with hvXdef
        have hvu : ρ vX * ρ u = ρ u * ρ vX := by
          rw [← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (Subtype.ext (hUab _ hv _ (mem_subgroupOf.1 u.2)))
        have hmem : πX (xw * ⟨v, hvX⟩ * xw⁻¹) ∈ centralizer {a} := by
          rw [mem_centralizer_singleton_iff, ← hw, map_mul, map_mul, map_inv]
          change πX xw * ρ vX * (πX xw)⁻¹ * (πX xw * ρ u * (πX xw)⁻¹) =
            πX xw * ρ u * (πX xw)⁻¹ * (πX xw * ρ vX * (πX xw)⁻¹)
          calc πX xw * ρ vX * (πX xw)⁻¹ * (πX xw * ρ u * (πX xw)⁻¹)
              = πX xw * (ρ vX * ρ u) * (πX xw)⁻¹ := by group
            _ = πX xw * (ρ u * ρ vX) * (πX xw)⁻¹ := by rw [hvu]
            _ = _ := by group
        rw [hCaN] at hmem
        obtain ⟨m, hm, hmeq⟩ := hmem
        have hker : m⁻¹ * (xw * ⟨v, hvX⟩ * xw⁻¹) ∈ πX.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hmeq, inv_mul_cancel]
        rw [hπker, mem_subgroupOf] at hker
        have hm' : (m : G) ∈ sp6N₂ φ e z := mem_subgroupOf.1 hm
        have h1 : (MulAut.conj (xw : G)).toMonoidHom v =
            (m : G) * (((m⁻¹ * (xw * ⟨v, hvX⟩ * xw⁻¹) : X)) : G) := by
          change (xw : G) * v * (xw : G)⁻¹ = _
          rw [Subgroup.coe_mul, Subgroup.coe_inv]
          change _ = (m : G) * ((m : G)⁻¹ * ((xw : G) * v * (xw : G)⁻¹))
          group
        rw [h1]
        exact mul_mem hm' (hCN₂ hker)
      have hU'2 : ∀ x ∈ U', x ^ 2 = 1 := by
        rintro _ ⟨v, hv, rfl⟩
        rw [← map_pow, hU2 v hv, map_one]
      have hU'el : IsElementaryAbelian 2 U' := isElementaryAbelian_of_sq_eq_one hU'2
      have hU'card : Nat.card U' = 512 := by
        rw [hU', Subgroup.card_map_of_injective (MulAut.conj (xw : G)).injective, hUcard,
          hCcard]
      have hU'C := hN₂u U' hU'N hU'el hU'card
      apply hUC
      intro v hv
      have h1 : (xw : G) * v * (xw : G)⁻¹ ∈ U' := ⟨v, hv, rfl⟩
      rw [hU'C] at h1
      have h2 := (mem_normalizer_iff.1
        (inv_mem xw.2 : (xw : G)⁻¹ ∈ normalizer (C : Set G)) _).1 h1
      rwa [inv_inv, show (xw : G)⁻¹ * ((xw : G) * v * (xw : G)⁻¹) * (xw : G) = v by group]
        at h2
    ·
      push Not at hout
      have hk5 : Nat.card ρ.ker ≤ 2 ^ 5 := by
        refine (hkerle {x₀} fun c _ h =>
          mem_centralizer_singleton_iff.2 (h x₀ hx₀U).symm).trans ?_
        exact hEin ⟨x₀, hx₀X⟩ (hρ1 ⟨⟨x₀, hx₀X⟩, hx₀U⟩ hx₀C)
          (hB2 _ ⟨⟨⟨x₀, hx₀X⟩, hx₀U⟩, rfl⟩) (hout ⟨⟨x₀, hx₀X⟩, hx₀U⟩)
      have hBdvd : Nat.card ρ.range ∣ 2 ^ 9 := Dvd.intro_left _ hcard
      obtain ⟨j, -, hBj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hBdvd
      have hj4 : 4 ≤ j := by
        by_contra h
        push Not at h
        have h1 : 2 ^ 9 ≤ 2 ^ 5 * 2 ^ 3 := by
          rw [← hcard, hBj]
          exact Nat.mul_le_mul hk5 (Nat.pow_le_pow_right (by norm_num) (by omega))
        norm_num at h1
      have hBQ : ∀ y ∈ ρ.range, y ∈ Q := by
        rintro _ ⟨u, rfl⟩
        exact mem_of_pow_two_pow_eq_one hRodd hQcomap' (hout u) (m := 1)
          (by rw [pow_one]; exact hB2 _ ⟨u, rfl⟩)
      set Eθ := ρ.range.map θ with hEθ
      have hEθD : Eθ ≤ D := by
        rintro _ ⟨y, hy, rfl⟩
        rw [← hQmap]
        exact mem_map_of_mem θ (hBQ y hy)
      set E := (Eθ.subgroupOf D).map χ.toMonoidHom with hE
      have hEcard : Nat.card E = Nat.card ρ.range := by
        rw [hE, Subgroup.card_map_of_injective χ.injective,
          Nat.card_congr (subgroupOfEquivOfLe hEθD).toEquiv]
        have hinj : Function.Injective (θ.comp ρ.range.subtype) := by
          rw [injective_iff_map_eq_one]
          intro y hy
          exact Subtype.ext (hθ1' y (hB2 y y.2) hy)
        have hr : (θ.comp ρ.range.subtype).range = Eθ := by
          rw [hEθ, MonoidHom.range_comp, range_subtype]
        rw [← hr]
        exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      have hE2 : ∀ y ∈ E, y ^ 2 = 1 := by
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨b, hb, hby⟩ := mem_subgroupOf.1 hy
        have hy2 : y ^ 2 = 1 := Subtype.ext (by
          rw [Subgroup.coe_pow, ← hby, ← map_pow, hB2 b hb, map_one]
          rfl)
        rw [← map_pow, hy2, map_one]
      obtain ⟨hE16, p, i, hpi⟩ := exists_conj_projRad_le hk4 hE2 (by
        rw [hEcard, hBj]
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj4)
      obtain ⟨q, hqQ, hqd⟩ : ((χ.symm p : D) : LayY C) ∈ Q.map θ := by
        rw [hQmap]
        exact (χ.symm p).2
      obtain ⟨s, hs2, hsR, hsC⟩ := hlevW i
      have hgen : ∀ g : GL (Fin 3) (ZMod 2), g ^ 2 = 1 → binaryEmbed k rfl g ∈ projRad k i →
          ∃ ug : U.subgroupOf X, ρ ug = q * ι g * q⁻¹ := by
        intro g hg2 hgR
        obtain ⟨y, hy, hyeq⟩ := hpi _ hgR
        obtain ⟨b, ⟨ug, rfl⟩, hby⟩ := mem_subgroupOf.1 hy
        refine ⟨ug, eq_of_sq_eq_one_of_map_eq hRodd hZ (hBQ _ ⟨ug, rfl⟩)
          (‹Q.Normal›.conj_mem _ (hJLQ (hιJL g)) _) (hB2 _ ⟨ug, rfl⟩)
          (conj_sq_eq_one (by rw [← map_pow, hg2, map_one]) q) ?_⟩
        have h1 : y = χ.symm p * ⟨θ (ι g), hιD g⟩ * (χ.symm p)⁻¹ := χ.injective (by
          rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hlabι]
          exact hyeq)
        rw [map_mul, map_mul, map_inv, hqd, hby, h1]
        rfl
      obtain ⟨us, hus⟩ := hgen s hs2 hsR
      obtain ⟨ut, hut⟩ := hgen glTransThreeOne hsq2
        (projCenterW_le_projRad i (by
          rw [binaryEmbed_glTransThreeOne]
          exact mem_projCenterW.2 ⟨1, rfl⟩))
      obtain ⟨xq, rfl⟩ := hπsurj q
      have hlift : ∀ (g : GL (Fin 3) (ZMod 2)) (ug : U.subgroupOf X),
          ρ ug = πX xq * ι g * (πX xq)⁻¹ →
          ((xq : G) * leviHom φ he g * (xq : G)⁻¹)⁻¹ * ((ug : X) : G) ∈ C := by
        intro g ug hug
        have hker : (xq * ⟨leviHom φ he g, hLX g⟩ * xq⁻¹)⁻¹ * (ug : X) ∈ πX.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, ← hιX]
          change _ * ρ ug = 1
          rw [hug, inv_mul_cancel]
        rw [hπker, mem_subgroupOf] at hker
        exact hker
      have hk4' : Nat.card ρ.ker ≤ 2 ^ 4 := by
        refine (hkerle ((fun m => (xq : G) * m * (xq : G)⁻¹) ''
          (leviHom φ he '' {s, glTransThreeOne})) ?_).trans ?_
        · intro c hc hcU
          rw [mem_centralizer_iff]
          have key : ∀ (g : GL (Fin 3) (ZMod 2)) (ug : U.subgroupOf X),
              ρ ug = πX xq * ι g * (πX xq)⁻¹ →
              (xq : G) * leviHom φ he g * (xq : G)⁻¹ * c =
                c * ((xq : G) * leviHom φ he g * (xq : G)⁻¹) := by
            intro g ug hug
            have h1 := hlift g ug hug
            set m := (xq : G) * leviHom φ he g * (xq : G)⁻¹ with hm
            have hmu : m = ((ug : X) : G) * (m⁻¹ * ((ug : X) : G))⁻¹ := by
              group
            have hc1 : Commute c ((ug : X) : G) :=
              Commute.symm (hcU _ (mem_subgroupOf.1 ug.2))
            have hc2 : Commute c (m⁻¹ * ((ug : X) : G)) := hC₂ab c hc _ h1
            have hcm : Commute c m := by
              rw [hmu]
              exact hc1.mul_right hc2.inv_right
            exact hcm.eq.symm
          rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
          rcases hg with rfl | hg
          · exact key _ us hus
          · rw [Set.mem_singleton_iff] at hg
            subst hg
            exact key _ ut hut
        · rw [card_inf_centralizer_conj xq.2]
          exact hsC
      have h1 : 2 ^ 9 ≤ 2 ^ 4 * 2 ^ 4 := by
        rw [← hcard, ← hEcard, hE16]
        exact Nat.mul_le_mul hk4' (by norm_num)
      norm_num at h1
  have hindex : ¬ 2 ∣ X.index := not_two_dvd_index_normalizer hC₂el hC₂ab huniq
  have hCz11 : ¬ 2 ^ 11 ∣ Nat.card (centralizer ({z} : Set G)) := by
    intro h
    have h1 := card_sup_dvd_of_commute (H := L) (K := zpowers z) (by
      intro l hl m hm
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hm
      exact (Commute.zpow_right (mem_centralizer_iff.1 hzL l hl) j).eq)
    rw [hLz, SteinbergBM.card_L φ he, Nat.card_zpowers, hz] at h1
    have h2 := h.trans h1
    norm_num at h2
  have hrank : ∀ P : Subgroup G, P ≤ centralizer ({z} : Set G) →
      (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) → (∀ x ∈ P, x * x = 1) → Nat.card P ≤ 128 :=
    fun P hP hc hs => ChevTwoFactor.card_le_of_le_centralizer hzL hLz hinf hz
      (fun P' hP'L hc' hs' => ChevTwoFactor.card_le_sixtyFour_of_le hb hnd hV φ hP'L hc' hs')
      hP hc hs
  set ξ : X →* Multiplicative (ZMod 2) := ηY.comp (θ.comp πX) with hξ
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hξz : ∀ (g : G) (h : g⁻¹ * z * g ∈ X), ξ ⟨_, h⟩ = Multiplicative.ofAdd 1 := by
    intro g hg
    set u : X := ⟨_, hg⟩ with hu
    have hCu : Nat.card (centralizer ({(u : G)} : Set G)) =
        Nat.card (centralizer ({z} : Set G)) := by
      have h := card_centralizer_conj g⁻¹ z
      rwa [inv_inv] at h
    have hu2 : (u : G) ^ 2 = 1 := by
      have h := conj_sq_eq_one hz2 g⁻¹
      rwa [inv_inv] at h
    rcases hmz2 (ξ u) with hξu | hξu
    · exfalso
      by_cases huC : (u : G) ∈ C
      ·
        set P := C.map (MulAut.conj g).toMonoidHom with hP
        have hPz : P ≤ centralizer ({z} : Set G) := by
          rintro _ ⟨c, hc, rfl⟩
          rw [mem_centralizer_singleton_iff]
          have h1 : c * (g⁻¹ * z * g) = (g⁻¹ * z * g) * c := hC₂ab c hc _ huC
          change g * c * g⁻¹ * z = z * (g * c * g⁻¹)
          calc g * c * g⁻¹ * z = g * (c * (g⁻¹ * z * g)) * g⁻¹ := by group
            _ = g * ((g⁻¹ * z * g) * c) * g⁻¹ := by rw [h1]
            _ = z * (g * c * g⁻¹) := by group
        have hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
          rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
          rw [← map_mul, ← map_mul, hC₂ab c hc d hd]
        have hPs : ∀ x ∈ P, x * x = 1 := by
          rintro _ ⟨c, hc, rfl⟩
          rw [← map_mul, ← pow_two, hC₂el c hc, map_one]
        have h1 := hrank P hPz hPc hPs
        rw [hP, Subgroup.card_map_of_injective (MulAut.conj g).injective, hCcard] at h1
        norm_num at h1
      · have hf1 : πX u ≠ 1 := by
          intro h
          apply huC
          have h' : u ∈ πX.ker := h
          rw [hπker, mem_subgroupOf] at h'
          exact h'
        have hf2 : πX u ^ 2 = 1 := by
          rw [← map_pow, show u ^ 2 = 1 from Subtype.ext hu2, map_one]
        have hθf2 : θ (πX u) ^ 2 = 1 := by rw [← map_pow, hf2, map_one]
        have hθfD : θ (πX u) ∈ D := hηker _ hθf2 hξu
        have hθf1 : θ (πX u) ≠ 1 := fun h => hf1 (hθ1' _ hf2 h)
        obtain ⟨q, -, hq⟩ := hinner _ hf2 hθfD hθf1
        set Uθ := ((projUnip k).map χ.symm.toMonoidHom).map D.subtype with hUθ
        have hUθD : Uθ ≤ D := map_subtype_le _
        have hUθcard : Nat.card Uθ = 64 := by
          rw [hUθ, Subgroup.card_map_of_injective D.subtype_injective,
            Subgroup.card_map_of_injective χ.symm.injective, card_projUnip, hk4]
        have hUθt : ∀ y ∈ Uθ, y * θ (ι glTransThreeOne) = θ (ι glTransThreeOne) * y := by
          rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
          have hvw := mem_centralizer_singleton_iff.1 (projUnip_le_centralizer_projW hv)
          have h1 : χ.symm v * ⟨θ (ι glTransThreeOne), hιD _⟩ =
              ⟨θ (ι glTransThreeOne), hιD _⟩ * χ.symm v := χ.injective (by
            rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hχt]
            exact hvw)
          exact congrArg Subtype.val h1
        have hat : a * ι glTransThreeOne = ι glTransThreeOne * a :=
          (mem_centralizer_singleton_iff.1 (hJLCa' _)).symm
        have h128 : 2 ^ 7 ∣ Nat.card (centralizer ({πX u} : Set (LayF C))) := by
          rw [← card_centralizer_conj q, hq]
          have h1 := two_mul_card_dvd_card_centralizer hRodd hZ hQmap htQ ht2 hUθD hUθt ha2'
            hat haD
          rw [hUθcard] at h1
          exact h1
        obtain ⟨P', hP'⟩ := Sylow.exists_subgroup_card_pow_prime 2 h128
        set P₁ := (P'.map (centralizer ({πX u} : Set (LayF C))).subtype).comap πX with hP₁
        have hC₂X : C ≤ X := le_normalizer
        have hP₁card : Nat.card P₁ = 2 ^ 16 := by
          rw [hP₁, card_comap_of_surjective hπsurj, Subgroup.card_map_of_injective
            (Subgroup.subtype_injective _), hP', hπker,
            Nat.card_congr (subgroupOfEquivOfLe hC₂X).toEquiv, hCcard]
          norm_num
        have hPcard : Nat.card (P₁.map X.subtype) = 2 ^ 16 := by
          rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hP₁card]
        have hPu : ∀ x ∈ P₁.map X.subtype, (u : G)⁻¹ * (x * u * x⁻¹) ∈ C := by
          rintro _ ⟨x, hx, rfl⟩
          obtain ⟨y, -, hy⟩ := hx
          have hyc := mem_centralizer_singleton_iff.1 y.2
          have hker : u⁻¹ * (x * u * x⁻¹) ∈ πX.ker := by
            rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv]
            have hy' : (y : LayF C) = πX x := hy
            rw [← hy', hyc, mul_inv_cancel_right, inv_mul_cancel]
          rw [hπker, mem_subgroupOf] at hker
          exact hker
        have h11 := two_pow_dvd_card_centralizer hu2 hC₂el hPcard hPu (hEin u hf1 hf2 hθfD)
        rw [hCu] at h11
        exact hCz11 h11
    · exact hξu
  exact false_of_transfer_of_not_two_dvd_index hGs hGnab hindex ξ hz hξz

end CFSG.EvenSmallLie.Child3
