module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigDefs
public import CFSG.ClassicalInvolution.Q3.TL4MF163Psl

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Act

variable {G : Type} [Group G]

theorem eq_one_of_mem_oddCoreOf [Finite G] {Λ : Subgroup G} {y : G}
    (hy : y ∈ oddCoreOf Λ) {k : ℕ} (hk : y ^ 2 ^ k = 1) : y = 1 := by
  obtain ⟨hyΛ, hyO⟩ := mem_oddCoreOf_iff.mp hy
  have hodd : Odd (orderOf y) := by
    have h1 := orderOf_dvd_natCard (⟨⟨y, hyΛ⟩, hyO⟩ : ↥(classicalInvolutionOddCore ↥Λ))
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h1
    exact (CFSG.ComponentClassification.OddCore.odd_card ↥Λ).of_dvd_nat h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
  have hj0 : j = 0 := by
    by_contra h
    rw [hj] at hodd
    exact Nat.not_even_iff_odd.2 hodd (Nat.even_pow.2 ⟨even_two, h⟩)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  exact hj

theorem eq_one_of_mem_oddCoreOf_of_mul_self [Finite G] {Λ : Subgroup G} {y : G}
    (hy : y ∈ oddCoreOf Λ) (hy2 : y * y = 1) : y = 1 :=
  eq_one_of_mem_oddCoreOf hy (k := 1) (by rw [pow_one, pow_two]; exact hy2)

theorem exists_pow_two_pow_eq_one {P : Sylow 2 G} {y : G} (hy : y ∈ (P : Subgroup G)) :
    ∃ k : ℕ, y ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨y, hy⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem exists_pow_involution {x : G} {k : ℕ} (hk : x ^ 2 ^ k = 1) (hx : x ≠ 1) :
    ∃ m : ℕ, x ^ m * x ^ m = 1 ∧ x ^ m ≠ 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hx hj
  refine ⟨2 ^ (j - 1), ?_, pow_ne_one_of_lt_orderOf (by positivity)
    (by rw [hj]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))⟩
  rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0),
    ← hj, pow_orderOf_eq_one]

theorem comm_of_actsTriv [Finite G] {P : Sylow 2 G} {Λ : Subgroup G} {x r : G}
    (hx : x ∈ (P : Subgroup G)) (hr : r ∈ (P : Subgroup G)) (hrΛ : r ∈ Λ) (h : ActsTriv Λ x) :
    x * r = r * x := by
  have hc : x * r * x⁻¹ * r⁻¹ ∈ (P : Subgroup G) :=
    (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem hx hr)
      ((P : Subgroup G).inv_mem hx)) ((P : Subgroup G).inv_mem hr)
  obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one hc
  have h1 : x * r * x⁻¹ * r⁻¹ = 1 := eq_one_of_mem_oddCoreOf (h r hrΛ) hk
  calc x * r = x * r * x⁻¹ * r⁻¹ * (r * x) := by group
    _ = r * x := by rw [h1, one_mul]

theorem actsTriv_mul {Λ : Subgroup G} {x y : G}
    (hxN : x ∈ Subgroup.normalizer (Λ : Set G)) (hx : ActsTriv Λ x) (hy : ActsTriv Λ y) :
    ActsTriv Λ (x * y) := by
  intro z hz
  have hxO := mem_normalizer_oddCore_of_mem_normalizer hxN
  have h1 : x * (y * z * y⁻¹ * z⁻¹) * x⁻¹ ∈ oddCoreOf Λ :=
    (Subgroup.mem_normalizer_iff.mp hxO _).mp (hy z hz)
  have h2 := (oddCoreOf Λ).mul_mem h1 (hx z hz)
  have e : x * (y * z * y⁻¹ * z⁻¹) * x⁻¹ * (x * z * x⁻¹ * z⁻¹) =
      x * y * z * (x * y)⁻¹ * z⁻¹ := by
    group
  rwa [e] at h2

theorem actsTriv_pow {Λ : Subgroup G} {x : G} (hxN : x ∈ Subgroup.normalizer (Λ : Set G))
    (hx : ActsTriv Λ x) (m : ℕ) : ActsTriv Λ (x ^ m) := by
  induction m with
  | zero =>
    intro z _
    simp
  | succ m ih =>
    rw [pow_succ]
    exact actsTriv_mul (Subgroup.pow_mem _ hxN m) ih hx

theorem actsTriv_mul_of_comm {Λ : Subgroup G} {x c : G} (hc : ∀ y ∈ Λ, c * y = y * c)
    (h : ActsTriv Λ x) : ActsTriv Λ (x * c) := by
  intro y hy
  have e : x * c * y * (x * c)⁻¹ * y⁻¹ = x * y * x⁻¹ * y⁻¹ := by
    calc x * c * y * (x * c)⁻¹ * y⁻¹ = x * (c * y) * c⁻¹ * x⁻¹ * y⁻¹ := by group
      _ = x * (y * c) * c⁻¹ * x⁻¹ * y⁻¹ := by rw [hc y hy]
      _ = x * y * x⁻¹ * y⁻¹ := by group
  rw [e]
  exact h y hy

theorem actsTriv_mul_of_actsLike {Λ : Subgroup G} {x w : G} (hwΛ : w ∈ Λ)
    (hw2 : w * w = 1) (h : ActsLike Λ x w) : ActsTriv Λ (x * w) := by
  intro y hy
  have h1 := h _ (Λ.mul_mem (Λ.mul_mem hwΛ hy) (Λ.inv_mem hwΛ))
  have e1 : w * (w * y * w⁻¹) * w⁻¹ = y := by
    calc w * (w * y * w⁻¹) * w⁻¹ = (w * w) * y * (w * w)⁻¹ := by group
      _ = y := by rw [hw2]; group
  rw [e1] at h1
  have e2 : x * (w * y * w⁻¹) * x⁻¹ * y⁻¹ = x * w * y * (x * w)⁻¹ * y⁻¹ := by group
  rwa [e2] at h1

theorem actsTriv_conjSub_iff {Λ : Subgroup G} {g y : G} :
    ActsTriv (conjSub g Λ) y ↔ ActsTriv Λ (g⁻¹ * y * g) := by
  constructor
  · intro h z hz
    have h1 := h _ (Generic.conj_mem_conjSub (n := g) hz)
    rw [Thompson.oddCoreOf_conjSub_eq, mem_conjSub_iff] at h1
    have e : g⁻¹ * (y * (g * z * g⁻¹) * y⁻¹ * (g * z * g⁻¹)⁻¹) * g =
        g⁻¹ * y * g * z * (g⁻¹ * y * g)⁻¹ * z⁻¹ := by
      group
    rwa [e] at h1
  · intro h z hz
    rw [mem_conjSub_iff] at hz
    rw [Thompson.oddCoreOf_conjSub_eq, mem_conjSub_iff]
    have e : g⁻¹ * (y * z * y⁻¹ * z⁻¹) * g =
        g⁻¹ * y * g * (g⁻¹ * z * g) * (g⁻¹ * y * g)⁻¹ * (g⁻¹ * z * g)⁻¹ := by
      group
    rw [e]
    exact h _ hz

theorem mem_normalizer_of_conj {H Λ : Subgroup G}
    (h : ∀ c ∈ H, ∀ y ∈ Λ, c * y * c⁻¹ ∈ Λ) {x : G} (hx : x ∈ H) :
    x ∈ Subgroup.normalizer (Λ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h x hx y hy, fun hy => ?_⟩
  have h1 := h x⁻¹ (H.inv_mem hx) _ hy
  rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at h1

theorem mul_inv_mem_oddCoreOf_of_mk_eq {Λ : Subgroup G} {a b : G} (ha : a ∈ Λ)
    (hb : b ∈ Λ) (h : (QuotientGroup.mk ⟨a, ha⟩ : ↥Λ ⧸ classicalInvolutionOddCore ↥Λ) =
      QuotientGroup.mk ⟨b, hb⟩) : a * b⁻¹ ∈ oddCoreOf Λ := by
  rw [QuotientGroup.eq] at h
  have h1 := Subgroup.inv_mem _ h
  rw [mul_inv_rev, inv_inv] at h1
  have h2 := Subgroup.Normal.conj_mem inferInstance _ h1 ⟨b, hb⟩
  rw [show (⟨b, hb⟩ : ↥Λ) * ((⟨b, hb⟩ : ↥Λ)⁻¹ * ⟨a, ha⟩) * (⟨b, hb⟩ : ↥Λ)⁻¹ =
    ⟨a, ha⟩ * (⟨b, hb⟩ : ↥Λ)⁻¹ by group] at h2
  exact ⟨_, h2, rfl⟩

end Act

section Cit3

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2SetR.comm_t_u (hs : Z2SetR r n R S t J u R₀ T₀ P) : t * u = u * t :=
  Q3CL.T8.mul_comm_of_mem_omegaNbr hs.large.datum.hypOmegaGen
    hs.large.datum.isUniqueInvolution_core hs.hJ hs.hu

theorem Z2SetR.T₀_le_cent_t (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    T₀ ≤ Subgroup.centralizer ({t} : Set Y) := fun _ hx =>
  S1916.normalizer_le_centralizer_of_isUniqueInvolution hs.large.datum.isUniqueInvolution_core
    (hs.hT₀N hx)

theorem Z2SetR.T₀_le_linkLayer (hs : Z2SetR r n R S t J u R₀ T₀ P) : T₀ ≤ linkLayer R t :=
  (le_coreAt t hs.hT₀.2.1 hs.hT₀.1 hs.T₀_le_cent_t).trans (coreAt_le_linkLayerAt hs.hJ)

theorem Z2SetR.R₀_le_linkLayerAt (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    R₀ ≤ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u := by
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  have hKJ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hs.large.datum.hypOmegaGen hK hs.hJ.1 hs.hJ
  exact (le_coreAt u hs.hR₀.2.1 hs.hR₀.1 hs.hR₀u).trans (coreAt_le_linkLayerAt hKJ)

theorem Z2SetR.t_mem_R₀ (hs : Z2SetR r n R S t J u R₀ T₀ P) : t ∈ R₀ :=
  T3.mem_of_isPGroup hs.large.datum.isUniqueInvolution_core hs.hR₀.1 hs.hR₀.2.1
    (le_trans (by norm_num) (Sec6Gen.eight_le_of_mem_RSet hs.large.datum.hypOmegaGen
      (mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self _) hs.hR₀)))

theorem Z2SetR.u_mem_T₀ (hs : Z2SetR r n R S t J u R₀ T₀ P) : u ∈ T₀ :=
  T3.mem_of_isPGroup hs.hu hs.hT₀.1 hs.hT₀.2.1
    (le_trans (by norm_num) (Sec6Gen.eight_le_of_mem_RSet hs.large.datum.hypOmegaGen
      (mem_RSet_of_isSylow2In hs.hJ.1 hs.hT₀)))

theorem Z2SetR.conj_mem_T₀ (hs : Z2SetR r n R S t J u R₀ T₀ P) {x : Y}
    (hxP : x ∈ (P : Subgroup Y)) (hxu : x ∈ Subgroup.centralizer ({u} : Set Y)) {y : Y}
    (hy : y ∈ T₀) : x * y * x⁻¹ ∈ T₀ := by
  have hT : J ⊓ (P : Subgroup Y) = T₀ := hs.hT₀.2.2 _ inf_le_left
    (P.isPGroup'.to_le inf_le_right) (le_inf hs.hT₀.1 hs.hT₀P)
  have hxN : x ∈ Subgroup.normalizer (J : Set Y) :=
    (TightLargeHypR.typeRFam hs.large).tight J hs.hJ.1 u hs.hu hxu
  rw [← hT] at hy ⊢
  exact ⟨(Subgroup.mem_normalizer_iff.mp hxN y).mp hy.1,
    (P : Subgroup Y).mul_mem ((P : Subgroup Y).mul_mem hxP hy.2) ((P : Subgroup Y).inv_mem hxP)⟩

theorem Z2SetR.conj_mem_R₀ (hs : Z2SetR r n R S t J u R₀ T₀ P) {x : Y}
    (hxP : x ∈ (P : Subgroup Y)) (hxt : x ∈ Subgroup.centralizer ({t} : Set Y)) {y : Y}
    (hy : y ∈ R₀) : x * y * x⁻¹ ∈ R₀ := by
  have hR : tightCore R ⊓ (P : Subgroup Y) = R₀ := hs.hR₀.2.2 _ inf_le_left
    (P.isPGroup'.to_le inf_le_right) (le_inf hs.hR₀.1 hs.hR₀P)
  have hxN : x ∈ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) :=
    (TightLargeHypR.typeRFam hs.large).tight (tightCore R) ⟨1, conjSub_one _⟩ t
      hs.large.datum.isUniqueInvolution_core hxt
  rw [← hR] at hy ⊢
  exact ⟨(Subgroup.mem_normalizer_iff.mp hxN y).mp hy.1,
    (P : Subgroup Y).mul_mem ((P : Subgroup Y).mul_mem hxP hy.2) ((P : Subgroup Y).inv_mem hxP)⟩

theorem Z2SetR.mem_normalizer_linkLayer (hs : Z2SetR r n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ Subgroup.centralizer ({t} : Set Y)) :
    x ∈ Subgroup.normalizer (linkLayer R t : Set Y) :=
  mem_normalizer_of_conj (H := Subgroup.centralizer ({t} : Set Y))
    (fun _ hc _ hy => conj_mem_linkLayer hs.large hc hy) hx

theorem Z2SetR.mem_normalizer_linkLayerAt (hs : Z2SetR r n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ Subgroup.centralizer ({u} : Set Y)) :
    x ∈ Subgroup.normalizer
      (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u : Set Y) := by
  refine mem_normalizer_of_conj (H := Subgroup.centralizer ({u} : Set Y)) (fun c hc y hy => ?_) hx
  have hcJ : conjSub c J = J := mem_normalizer_iff_conjSub_eq.mp
    ((TightLargeHypR.typeRFam hs.large).tight J hs.hJ.1 u hs.hu hc)
  exact conj_mem_linkLayerAt hs.large.datum.hypOmegaGen.conjInvariant hc hcJ hy

theorem Z2SetR.exists_linkLayerAt_eq (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    ∃ g : Y, conjSub g (tightCore R) = J ∧ u = g * t * g⁻¹ ∧
      linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u = conjSub g (linkLayer R t) := by
  obtain ⟨g, hg⟩ := hs.hJ.1
  have hg' : conjSub g (tightCore R) = J := hg
  have hug : u = g * t * g⁻¹ := by
    have h1 := hs.large.datum.isUniqueInvolution_core.conj g
    rw [hg'] at h1
    exact hs.hu.eq h1
  refine ⟨g, hg', hug, ?_⟩
  show _ = conjSub g (linkLayerAt (CoreAssembly.conjClass (tightCore R)) (tightCore R) t)
  rw [conjSub_linkLayerAt hs.large.datum.hypOmegaGen.conjInvariant g, hg', ← hug]

theorem Z2SetR.mem_oddCoreOf_of_actsTriv (hs : Z2SetR r n R S t J u R₀ T₀ P) {w : Y}
    (hw : w ∈ linkLayer R t) (h : ActsTriv (linkLayer R t) w) :
    w ∈ oddCoreOf (linkLayer R t) := by
  obtain ⟨p, f, -, -, -, -, hk⟩ := hs.model
  have hZ : Subgroup.center ↥(linkGrp R t) = ⊥ := by
    haveI := hs.simple
    obtain ⟨-, h4, F, _, _, hFcard, ⟨e⟩⟩ := MF163.psl2_of_lieModel hk
    have hnab : ∃ a b : ↥(genFittingFStar ↥(linkGrp R t)), a * b ≠ b * a := by
      obtain ⟨x, y, hxy⟩ :=
        ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian F
          (by omega) (by omega)
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (e.symm x)
      obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (e.symm y)
      refine ⟨a, b, fun hab => hxy ?_⟩
      have := congrArg (fun g => e (QuotientGroup.mk g : FStarQuot ↥(linkGrp R t))) hab
      simp only [QuotientGroup.mk_mul, map_mul] at this
      rwa [ha, hb, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
    exact le_bot_iff.mp ((centralizer_genFittingFStar_eq_bot hnab) ▸
      Subgroup.center_le_centralizer (genFittingFStar ↥(linkGrp R t) : Set ↥(linkGrp R t)))
  have hc : linkLayerEquiv hs.large (QuotientGroup.mk ⟨w, hw⟩) ∈
      Subgroup.center ↥(linkGrp R t) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨q, rfl⟩ := (linkLayerEquiv hs.large).surjective g
    obtain ⟨⟨z, hz⟩, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← map_mul, ← map_mul]
    congr 1
    obtain ⟨_, hO⟩ := mem_oddCoreOf_iff.mp (h z hz)
    have h2 : (QuotientGroup.mk ((⟨w, hw⟩ : ↥(linkLayer R t)) * ⟨z, hz⟩ *
        (⟨w, hw⟩ : ↥(linkLayer R t))⁻¹ * (⟨z, hz⟩ : ↥(linkLayer R t))⁻¹) :
        ↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hO
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h2
    calc (QuotientGroup.mk ⟨z, hz⟩ : ↥(linkLayer R t) ⧸
          classicalInvolutionOddCore ↥(linkLayer R t)) * QuotientGroup.mk ⟨w, hw⟩ =
        (QuotientGroup.mk ⟨w, hw⟩ * QuotientGroup.mk ⟨z, hz⟩ *
          (QuotientGroup.mk ⟨w, hw⟩)⁻¹ * (QuotientGroup.mk ⟨z, hz⟩)⁻¹)⁻¹ *
            (QuotientGroup.mk ⟨w, hw⟩ * QuotientGroup.mk ⟨z, hz⟩) := by group
      _ = QuotientGroup.mk ⟨w, hw⟩ * QuotientGroup.mk ⟨z, hz⟩ := by rw [h2, inv_one, one_mul]
  rw [hZ, Subgroup.mem_bot, map_eq_one_iff _ (linkLayerEquiv hs.large).injective,
    QuotientGroup.eq_one_iff] at hc
  exact ⟨_, hc, rfl⟩

theorem Z2SetR.not_actsTriv_u (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    ¬ ActsTriv (linkLayer R t) u := by
  intro h
  exact hs.hu.ne_one (eq_one_of_mem_oddCoreOf_of_mul_self
    (hs.mem_oddCoreOf_of_actsTriv (hs.T₀_le_linkLayer hs.u_mem_T₀) h) hs.hu.sq)

theorem Z2SetR.not_actsTriv_t (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    ¬ ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) t := by
  intro h
  have ht := hs.large.datum.isUniqueInvolution_core
  obtain ⟨g, -, -, hΛ⟩ := hs.exists_linkLayerAt_eq
  have htΛ := hs.R₀_le_linkLayerAt hs.t_mem_R₀
  rw [hΛ, mem_conjSub_iff] at htΛ
  rw [hΛ, actsTriv_conjSub_iff] at h
  have h2 : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht.sq]; group
  have h3 := eq_one_of_mem_oddCoreOf_of_mul_self (hs.mem_oddCoreOf_of_actsTriv htΛ h) h2
  apply ht.ne_one
  calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
    _ = 1 := by rw [h3]; group

theorem Z2SetR.eq_one_of_actsTriv (hs : Z2SetR r n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ edgeCent (P : Subgroup Y) t u) (htx : ActsTriv (linkLayer R t) x)
    (hux : ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) x) : x = 1 := by
  obtain ⟨⟨hxP, hxt⟩, hxu⟩ := hx
  have ht := hs.large.datum.isUniqueInvolution_core
  have hxT₀ : ∀ r ∈ T₀, x * r = r * x := fun r hr =>
    comm_of_actsTriv hxP (hs.hT₀P hr) (hs.T₀_le_linkLayer hr) htx
  have hxR₀ : ∀ r ∈ R₀, x * r = r * x := fun r hr =>
    comm_of_actsTriv hxP (hs.hR₀P hr) (hs.R₀_le_linkLayerAt hr) hux
  obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one hxP
  by_contra hx1
  obtain ⟨m, hm2, hm1⟩ := exists_pow_involution hk hx1
  have hwt : x ^ m * t = t * x ^ m :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.pow_mem _ hxt m)
  have hwu : x ^ m * u = u * x ^ m :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.pow_mem _ hxu m)
  have hwE : x ^ m ∈ Subgroup.closure ({t, u} : Set Y) := by
    by_contra hwE
    exact hs.noA1 ⟨x ^ m, hm2, hwt, hwu, hwE,
      fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr
        ((Commute.pow_right (hxR₀ r hr).symm m).eq),
      fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr
        ((Commute.pow_right (hxT₀ r hr).symm m).eq)⟩
  have hwΛt : ActsTriv (linkLayer R t) (x ^ m) :=
    actsTriv_pow (hs.mem_normalizer_linkLayer hxt) htx m
  have hwΛu : ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (x ^ m) :=
    actsTriv_pow (hs.mem_normalizer_linkLayerAt hxu) hux m
  rcases Asc77.T8.mem_closure_pair_involutions ht.sq hs.hu.sq hs.comm_t_u hwE with h | h | h | h
  · exact hm1 h
  · rw [h] at hwΛu
    exact hs.not_actsTriv_t hwΛu
  · rw [h] at hwΛt
    exact hs.not_actsTriv_u hwΛt
  ·
    rw [h, hs.comm_t_u] at hwΛt
    have htΛ : ∀ y ∈ linkLayer R t, t⁻¹ * y = y * t⁻¹ := fun y hy => by
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hy)
      calc t⁻¹ * y = t⁻¹ * (y * t) * t⁻¹ := by group
        _ = t⁻¹ * (t * y) * t⁻¹ := by rw [h1]
        _ = y * t⁻¹ := by group
    have h1 := actsTriv_mul_of_comm htΛ hwΛt
    rw [mul_inv_cancel_right] at h1
    exact hs.not_actsTriv_u h1

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
