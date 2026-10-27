module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellShort
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellAlt3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellFrattiniKernel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellOffender
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped commutatorElement

structure NaturalOvergroupSetup {G : Type*} [Group G] (X K : Subgroup G) : Prop where
  charTwo : CharTwo X
  le : K ≤ X
  normal : (K.subgroupOf X).Normal
  noPQ : NoPQuotient 2 K
  two_quot : ∀ x ∈ X, ∃ m : ℕ, x ^ 2 ^ m ∈ K
  central : ⁅blockQ X, K⁆ ≤ Subgroup.centralizer (blockQ X : Set G)

section BlockQ

variable {G : Type*} [Group G]

theorem isPGroup_blockQ (X : Subgroup G) : IsPGroup 2 (blockQ X) :=
  CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 X

theorem blockQ_le_self (X : Subgroup G) : blockQ X ≤ X :=
  CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 X

theorem blockQ_normal_subgroupOf (X : Subgroup G) : ((blockQ X).subgroupOf X).Normal :=
  CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 X X le_rfl
    (by rw [Subgroup.subgroupOf_self]; infer_instance)

theorem le_normalizer_blockQ (X : Subgroup G) : X ≤ Subgroup.normalizer (blockQ X : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (blockQ_le_self X)).mp (blockQ_normal_subgroupOf X)

end BlockQ

namespace NaturalOvergroupSetup

variable {G : Type*} [Group G] {X K : Subgroup G} (h : NaturalOvergroupSetup X K)
include h

theorem le_normalizer_K : X ≤ Subgroup.normalizer (K : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mp h.normal

theorem U_le_Q : ⁅blockQ X, K⁆ ≤ blockQ X :=
  commutator_le_left_of_normalizes (h.le.trans (le_normalizer_blockQ X))

theorem U_le_K : ⁅blockQ X, K⁆ ≤ K := by
  rw [Subgroup.commutator_comm]
  exact commutator_le_left_of_normalizes ((blockQ_le_self X).trans h.le_normalizer_K)

theorem le_normalizer_U : X ≤ Subgroup.normalizer ((⁅blockQ X, K⁆ : Subgroup G) : Set G) := by
  have key : ∀ x ∈ X, ∀ y ∈ (⁅blockQ X, K⁆ : Subgroup G), x * y * x⁻¹ ∈ (⁅blockQ X, K⁆ : Subgroup G) := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨q, hq, k, hk, rfl⟩ := hy
      have h1 : x * q * x⁻¹ ∈ blockQ X := (Subgroup.mem_normalizer_iff.mp ((le_normalizer_blockQ X) hx) q).mp hq
      have h2 : x * k * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_K hx) k).mp hk
      have := Subgroup.commutator_mem_commutator h1 h2
      convert this using 1
      simp only [commutatorElement_def]; group
    | one => simp
    | mul y z _ _ ihy ihz =>
      have := mul_mem ihy ihz
      simpa [mul_assoc] using this
    | inv y _ ih =>
      have := inv_mem ih
      simpa [mul_assoc] using this
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key x hx y, fun hy => ?_⟩
  have := key x⁻¹ (inv_mem hx) _ hy
  simpa [mul_assoc] using this

end NaturalOvergroupSetup

theorem isPGroup_two_of_forall_odd {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (h : ∀ t ∈ T, Odd (orderOf t) → t = 1) : IsPGroup 2 T := by
  intro t
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (t : G)).ne'
  refine ⟨a, ?_⟩
  have h1 : orderOf ((t : G) ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hord ▸ dvd_mul_right _ _), hord,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  have h2 : (t : G) ^ 2 ^ a = 1 := h _ (T.pow_mem t.2 _) (by rw [h1]; exact hm)
  exact Subtype.ext (by simpa using h2)

theorem eq_one_of_isPGroup_of_odd {G : Type*} [Group G] {P : Subgroup G} (hP : IsPGroup 2 P)
    {y : G} (hy : y ∈ P) (hodd : Odd (orderOf y)) : y = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨y, hy⟩
  have h1 : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have hcop : Nat.Coprime (orderOf y) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl h2)

namespace NaturalOvergroupSetup

variable {G : Type*} [Group G] [Finite G] {X K : Subgroup G} (h : NaturalOvergroupSetup X K)
include h

theorem centralizer_U :
    X ⊓ Subgroup.centralizer ((⁅blockQ X, K⁆ : Subgroup G) : Set G) = blockQ X := by
  set U : Subgroup G := ⁅blockQ X, K⁆ with hU
  apply le_antisymm
  · set T : Subgroup G := X ⊓ Subgroup.centralizer (U : Set G) with hT
    have hTX : T ≤ X := inf_le_left
    have hkey : ∀ x ∈ X, ∀ t ∈ T, x * t * x⁻¹ ∈ T := by
      intro x hx t ht
      refine Subgroup.mem_inf.mpr ⟨X.mul_mem (X.mul_mem hx ht.1) (X.inv_mem hx), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu' : x⁻¹ * u * x ∈ U := by
        have := (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_U (X.inv_mem hx)) u).mp hu
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp ht.2 _ hu'
      calc u * (x * t * x⁻¹) = x * ((x⁻¹ * u * x) * t) * x⁻¹ := by group
        _ = x * (t * (x⁻¹ * u * x)) * x⁻¹ := by rw [h1]
        _ = (x * t * x⁻¹) * u := by group
    have hTn : (T.subgroupOf X).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hTX]
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro t
      exact ⟨hkey x hx t, fun ht => by simpa [mul_assoc] using hkey x⁻¹ (X.inv_mem hx) _ ht⟩
    have hodd : ∀ t ∈ T, Odd (orderOf t) → t = 1 := by
      intro t ht hto
      obtain ⟨m, hm⟩ := h.two_quot t ht.1
      have htK : t ∈ K := mem_of_odd_orderOf_of_pow_mem hto hm
      set L : Subgroup G := Subgroup.zpowers t with hL
      have hLK : L ≤ K := by rw [hL, Subgroup.zpowers_le]; exact htK
      have hLX : L ≤ X := hLK.trans h.le
      have hLU : ⁅U, L⁆ ≤ ⊥ := by
        rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro u hu
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have : L ≤ Subgroup.centralizer (U : Set G) := by
          rw [hL, Subgroup.zpowers_le]; exact ht.2
        exact (Subgroup.mem_centralizer_iff.mp (this hl) u hu).symm
      have hcomm : ⁅blockQ X, L⁆ ≤ ⊥ := by
        refine commutator_le_of_gen (p := 2) (U := U) (W := ⊥) (L := L) h.U_le_Q bot_le
          ((isPGroup_blockQ X).to_le h.U_le_Q) (fun q _ w hw => by rw [Subgroup.mem_bot.mp hw]; simp) ?_
          hLU (Subgroup.commutator_mono le_rfl hLK) (hLX.trans (le_normalizer_blockQ X))
        apply le_antisymm
        · rw [Subgroup.closure_le]; exact fun x hx => hx.1
        · rw [hL, Subgroup.zpowers_le]
          refine Subgroup.subset_closure ⟨Subgroup.mem_zpowers t, ?_⟩
          intro hd
          exact (Nat.not_even_iff_odd.mpr hto) (even_iff_two_dvd.mpr hd)
      have htQ : t ∈ blockQ X := by
        apply h.charTwo
        refine Subgroup.mem_inf.mpr ⟨ht.1, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        have : blockQ X ≤ Subgroup.centralizer (L : Set G) :=
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hcomm))
        exact (Subgroup.mem_centralizer_iff.mp (this hq) t (Subgroup.mem_zpowers t)).symm
      exact eq_one_of_isPGroup_of_odd (isPGroup_blockQ X) htQ hto
    exact le_pCoreOf_of_normal_subgroupOf 2 hTX hTn (isPGroup_two_of_forall_odd hodd)
  · intro q hq
    refine Subgroup.mem_inf.mpr ⟨(blockQ_le_self X) hq, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.mp (h.central hu) q hq).symm

theorem exp_two (hsq : ∀ x ∈ ⁅blockQ X, K⁆, x ^ 2 ∈ Subgroup.centralizer (K : Set G)) :
    ∀ x ∈ ⁅blockQ X, K⁆, x ^ 2 = 1 := by
  have hKQ : K ≤ Subgroup.normalizer (blockQ X : Set G) := h.le.trans (le_normalizer_blockQ X)
  have hsat : ⁅⁅blockQ X, K⁆, K⁆ = ⁅blockQ X, K⁆ :=
    prime_residual_central_commutator_saturation (isPGroup_blockQ X) hKQ h.noPQ h.central
  have hUab : ∀ u ∈ ⁅blockQ X, K⁆, ∀ v ∈ ⁅blockQ X, K⁆, u * v = v * u := fun u hu v hv =>
    (Subgroup.mem_centralizer_iff.mp (h.central hv) u (h.U_le_Q hu))
  have hUnorm : K ≤ Subgroup.normalizer ((⁅blockQ X, K⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hKQ
  have hUU : (⁅⁅blockQ X, K⁆, K⁆ : Subgroup G) ≤ ⁅blockQ X, K⁆ :=
    commutator_le_left_of_normalizes hUnorm
  have key : ∀ x ∈ (⁅⁅blockQ X, K⁆, K⁆ : Subgroup G), x ^ 2 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨u, hu, k, hk, rfl⟩ := hx
      obtain ⟨w, hw_def⟩ : ∃ w : G, w = k * u⁻¹ * k⁻¹ := ⟨_, rfl⟩
      have hwU : w ∈ (⁅blockQ X, K⁆ : Subgroup G) := by
        rw [hw_def]
        exact (Subgroup.mem_normalizer_iff.mp (hUnorm hk) u⁻¹).mp (inv_mem hu)
      have hu2 : u ^ 2 ∈ Subgroup.centralizer (K : Set G) := hsq u hu
      have hk2 : Commute k (u ^ 2) := Subgroup.mem_centralizer_iff.mp hu2 k hk
      have hcomm : u * w = w * u := hUab u hu w hwU
      have hx : ⁅u, k⁆ = u * w := by
        rw [hw_def]; simp only [commutatorElement_def]; group
      have hw2 : w * w = (u ^ 2)⁻¹ := by
        have h1 : w * w = k * (u ^ 2)⁻¹ * k⁻¹ := by rw [hw_def]; group
        rw [h1, hk2.inv_right.eq]; group
      calc ⁅u, k⁆ ^ 2 = (u * w) * (u * w) := by rw [hx, pow_two]
        _ = u * (w * u) * w := by group
        _ = u * (u * w) * w := by rw [← hcomm]
        _ = u ^ 2 * (w * w) := by rw [pow_two]; simp only [mul_assoc]
        _ = 1 := by rw [hw2]; exact mul_inv_cancel _
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hxU : x ∈ (⁅blockQ X, K⁆ : Subgroup G) := hUU hx
      have hyU : y ∈ (⁅blockQ X, K⁆ : Subgroup G) := hUU hy
      have hcomm : Commute x y := hUab x hxU y hyU
      rw [hcomm.mul_pow, ihx, ihy]; simp
    | inv x hx ih => rw [inv_pow, ih]; simp
  rw [hsat] at key
  exact key

end NaturalOvergroupSetup

structure NaturalOvergroupModule {G : Type*} [Group G] (X K D : Subgroup G) {F : Type*} [Field F]
    (ρ : D →* Matrix.SpecialLinearGroup (Fin 2) F)
    (β : (⁅blockQ X, K⁆ : Subgroup G) →* Multiplicative (Fin 2 → F)) : Prop where
  KD : K ≤ D
  DX : D ≤ X
  ρ_surj : Function.Surjective ρ
  β_surj : Function.Surjective β
  β_ker : β.ker = (⁅blockQ X, K⁆ ⊓ Subgroup.centralizer (X : Set G)).subgroupOf ⁅blockQ X, K⁆
  β_equiv : ∀ (d : D) (u u' : (⁅blockQ X, K⁆ : Subgroup G)), (u' : G) = d * u * d⁻¹ →
    Multiplicative.toAdd (β u') =
      (ρ d : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))

namespace NaturalOvergroupSetup

variable {G : Type*} [Group G] [Finite G] {X K D : Subgroup G} (h : NaturalOvergroupSetup X K)
include h

theorem D_subnormal (hKD : K ≤ D) : (D.subgroupOf X).IsSubnormal := by
  have : (K.subgroupOf X).Normal := h.normal
  have hq : IsPGroup 2 (X ⧸ K.subgroupOf X) := by
    intro x
    obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨m, hm⟩ := h.two_quot g hg
    refine ⟨m, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hm
  exact isSubnormal_of_pGroup_quotient (p := 2) (K.subgroupOf X) hq
    (fun x hx => Subgroup.mem_subgroupOf.mpr (hKD (Subgroup.mem_subgroupOf.mp hx)))

theorem blockQ_D (hKD : K ≤ D) (hDX : D ≤ X) : blockQ D = D ⊓ blockQ X := by
  apply le_antisymm
  · exact le_inf (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 D)
      (pCoreOf_le_of_isSubnormal 2 hDX (h.D_subnormal hKD))
  · have hn : ((D ⊓ blockQ X).subgroupOf D).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
      intro d hd
      rw [Subgroup.mem_normalizer_iff]
      have key : ∀ d ∈ D, ∀ y ∈ D ⊓ blockQ X, d * y * d⁻¹ ∈ D ⊓ blockQ X := by
        intro d hd y hy
        refine Subgroup.mem_inf.mpr ⟨D.mul_mem (D.mul_mem hd hy.1) (D.inv_mem hd), ?_⟩
        exact (Subgroup.mem_normalizer_iff.mp ((le_normalizer_blockQ X) (hDX hd)) y).mp hy.2
      intro y
      exact ⟨key d hd y, fun hy => by simpa [mul_assoc] using key d⁻¹ (D.inv_mem hd) _ hy⟩
    exact le_pCoreOf_of_normal_subgroupOf 2 inf_le_left hn ((isPGroup_blockQ X).to_le inf_le_right)

end NaturalOvergroupSetup

namespace NaturalOvergroupModule

variable {G : Type*} [Group G] [Finite G] {X K D : Subgroup G} {F : Type*} [Field F]
  {ρ : D →* Matrix.SpecialLinearGroup (Fin 2) F}
  {β : (⁅blockQ X, K⁆ : Subgroup G) →* Multiplicative (Fin 2 → F)}
  (m : NaturalOvergroupModule X K D ρ β)
include m

omit [Finite G] in
theorem β_eq_one_iff (u : (⁅blockQ X, K⁆ : Subgroup G)) :
    β u = 1 ↔ (u : G) ∈ Subgroup.centralizer (X : Set G) := by
  have h1 : u ∈ β.ker ↔ β u = 1 := MonoidHom.mem_ker
  rw [← h1, m.β_ker, Subgroup.mem_subgroupOf]
  exact ⟨fun h => h.2, fun h => ⟨u.2, h⟩⟩

omit [Finite G] in
theorem sq_mem_centralizer [CharP F 2] (u : (⁅blockQ X, K⁆ : Subgroup G)) :
    (u : G) ^ 2 ∈ Subgroup.centralizer (X : Set G) := by
  rw [← m.β_eq_one_iff ⟨(u : G) ^ 2, (⁅blockQ X, K⁆ : Subgroup G).pow_mem u.2 2⟩]
  have : (⟨(u : G) ^ 2, (⁅blockQ X, K⁆ : Subgroup G).pow_mem u.2 2⟩ :
      (⁅blockQ X, K⁆ : Subgroup G)) = u ^ 2 := rfl
  rw [this, map_pow]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow]
  funext i
  simp only [Pi.smul_apply, Pi.zero_apply, toAdd_one]
  rw [two_nsmul]
  exact CharTwo.add_self_eq_zero _

theorem exp_two' [CharP F 2] (h : NaturalOvergroupSetup X K) : ∀ x ∈ ⁅blockQ X, K⁆, x ^ 2 = 1 :=
  h.exp_two fun x hx => Subgroup.centralizer_le h.le (m.sq_mem_centralizer ⟨x, hx⟩)

omit [Finite G] in
theorem inf_Q_le_ker (d : D) (hd : (d : G) ∈ blockQ X) (h : NaturalOvergroupSetup X K) : ρ d = 1 := by
  have hall : ∀ w : Fin 2 → F, (ρ d : Matrix.SpecialLinearGroup (Fin 2) F) • w = w := by
    intro w
    obtain ⟨u, hu⟩ := m.β_surj (Multiplicative.ofAdd w)
    have hcomm : (d : G) * u * (d : G)⁻¹ = u := by
      have := Subgroup.mem_centralizer_iff.mp (h.central u.2) (d : G) hd
      rw [this]; group
    have := m.β_equiv d u u hcomm.symm
    rw [hu] at this
    rw [Matrix.SpecialLinearGroup.smul_def]
    exact this.symm
  exact eq_one_of_forall_smul_vec hall

theorem sq_mem_Q_of_ker [CharP F 2] (h : NaturalOvergroupSetup X K) (d : D) (hd : ρ d = 1) :
    (d : G) ^ 2 ∈ blockQ X := by
  have hexp := m.exp_two' h
  rw [← h.centralizer_U]
  refine Subgroup.mem_inf.mpr ⟨X.pow_mem (m.DX d.2) 2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hdu : (d : G) * u * (d : G)⁻¹ ∈ (⁅blockQ X, K⁆ : Subgroup G) := by
    have := (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_U (m.DX d.2)) u).mp hu
    exact this
  have hc : (d : G) * u * (d : G)⁻¹ * u⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    rw [← m.β_eq_one_iff ⟨(d : G) * u * (d : G)⁻¹ * u⁻¹,
      (⁅blockQ X, K⁆ : Subgroup G).mul_mem hdu ((⁅blockQ X, K⁆ : Subgroup G).inv_mem hu)⟩]
    have e1 := m.β_equiv d ⟨u, hu⟩ ⟨(d : G) * u * (d : G)⁻¹, hdu⟩ rfl
    rw [hd] at e1
    have e2 : (⟨(d : G) * u * (d : G)⁻¹ * u⁻¹, (⁅blockQ X, K⁆ : Subgroup G).mul_mem hdu
        ((⁅blockQ X, K⁆ : Subgroup G).inv_mem hu)⟩ : (⁅blockQ X, K⁆ : Subgroup G)) =
        ⟨(d : G) * u * (d : G)⁻¹, hdu⟩ * ⟨u, hu⟩⁻¹ := rfl
    rw [e2, map_mul, map_inv]
    have : Multiplicative.toAdd (β ⟨(d : G) * u * (d : G)⁻¹, hdu⟩) =
        Multiplicative.toAdd (β ⟨u, hu⟩) := by
      rw [e1]; simp
    rw [Multiplicative.toAdd.injective this]
    exact mul_inv_cancel _
  set c : G := (d : G) * u * (d : G)⁻¹ * u⁻¹ with hcdef
  have hcU : c ∈ (⁅blockQ X, K⁆ : Subgroup G) :=
    (⁅blockQ X, K⁆ : Subgroup G).mul_mem hdu ((⁅blockQ X, K⁆ : Subgroup G).inv_mem hu)
  have hc2 : c * c = 1 := by simpa [pow_two] using hexp c hcU
  have hcd : (d : G) * c = c * (d : G) := by
    have := Subgroup.mem_centralizer_iff.mp hc (d : G) (m.DX d.2)
    exact this
  have hdu_eq : (d : G) * u * (d : G)⁻¹ = c * u := by rw [hcdef]; group
  have : (d : G) ^ 2 * u * ((d : G) ^ 2)⁻¹ = u := by
    rw [pow_two]
    calc (d : G) * (d : G) * u * ((d : G) * (d : G))⁻¹
        = (d : G) * ((d : G) * u * (d : G)⁻¹) * (d : G)⁻¹ := by group
      _ = (d : G) * (c * u) * (d : G)⁻¹ := by rw [hdu_eq]
      _ = ((d : G) * c * (d : G)⁻¹) * ((d : G) * u * (d : G)⁻¹) := by group
      _ = c * (c * u) := by
          rw [hcd, mul_inv_cancel_right, hdu_eq]
      _ = (c * c) * u := by group
      _ = u := by rw [hc2, one_mul]
  have h3 : (d : G) ^ 2 * u = u * (d : G) ^ 2 := by
    calc (d : G) ^ 2 * u = ((d : G) ^ 2 * u * ((d : G) ^ 2)⁻¹) * (d : G) ^ 2 := by group
      _ = u * (d : G) ^ 2 := by rw [this]
  exact h3.symm

theorem ker_map_eq [CharP F 2] (h : NaturalOvergroupSetup X K) :
    ρ.ker.map D.subtype = D ⊓ blockQ X := by
  apply le_antisymm
  · set N : Subgroup G := ρ.ker.map D.subtype with hN
    have hND : N ≤ D := by rintro _ ⟨d, -, rfl⟩; exact d.2
    have hN2 : IsPGroup 2 N := by
      intro n
      obtain ⟨d, hd, hdn⟩ := n.2
      obtain ⟨k, hk⟩ := (isPGroup_blockQ X) ⟨(d : G) ^ 2, m.sq_mem_Q_of_ker h d hd⟩
      refine ⟨k + 1, ?_⟩
      apply Subtype.ext
      have : ((d : G) ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      show (n : G) ^ 2 ^ (k + 1) = 1
      rw [← hdn, pow_succ', pow_mul]
      exact this
    have hNn : (N.subgroupOf D).Normal := by
      have : N.subgroupOf D = ρ.ker := Subgroup.comap_map_eq_self_of_injective D.subtype_injective _
      rw [this]
      infer_instance
    have h1 := le_pCoreOf_of_normal_subgroupOf 2 hND hNn hN2
    exact h1.trans (h.blockQ_D m.KD m.DX).le
  · rintro d ⟨hdD, hdQ⟩
    exact ⟨⟨d, hdD⟩, m.inf_Q_le_ker ⟨d, hdD⟩ hdQ h, rfl⟩

end NaturalOvergroupModule

@[expose] def rhoK {G : Type*} [Group G] {D : Subgroup G} {F : Type*} [Field F] (K : Subgroup G)
    (ρ : D →* Matrix.SpecialLinearGroup (Fin 2) F) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
  (K.subgroupOf D).map ρ

namespace NaturalOvergroupModule

variable {G : Type*} [Group G] [Finite G] {X K D : Subgroup G} {F : Type*} [Field F]
  {ρ : D →* Matrix.SpecialLinearGroup (Fin 2) F}
  {β : (⁅blockQ X, K⁆ : Subgroup G) →* Multiplicative (Fin 2 → F)}
  (m : NaturalOvergroupModule X K D ρ β)
include m

omit [Finite G] in
theorem K_normal_in_D (h : NaturalOvergroupSetup X K) : (K.subgroupOf D).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer m.KD]
  exact m.DX.trans h.le_normalizer_K

omit [Finite G] in
theorem rhoK_normal (h : NaturalOvergroupSetup X K) : (rhoK K ρ).Normal :=
  have := m.K_normal_in_D h
  Subgroup.Normal.map this ρ m.ρ_surj

omit [Finite G] in
theorem rhoK_two_quot (h : NaturalOvergroupSetup X K) (s : Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ j : ℕ, s ^ 2 ^ j ∈ rhoK K ρ := by
  obtain ⟨d, rfl⟩ := m.ρ_surj s
  obtain ⟨j, hj⟩ := h.two_quot (d : G) (m.DX d.2)
  exact ⟨j, ⟨d ^ 2 ^ j, Subgroup.mem_subgroupOf.mpr (by simpa using hj), by simp⟩⟩

omit [Finite G] in
theorem rhoK_noPQuotient (h : NaturalOvergroupSetup X K) : NoPQuotient 2 (rhoK K ρ) := by
  have hf : Function.Surjective
      ((ρ.comp (Subgroup.inclusion m.KD)).codRestrict (rhoK K ρ) (fun x =>
        ⟨Subgroup.inclusion m.KD x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩)) := by
    rintro ⟨_, ⟨d, hd, rfl⟩⟩
    exact ⟨⟨(d : G), Subgroup.mem_subgroupOf.mp hd⟩, rfl⟩
  exact NoPQuotient.of_surjective _ hf h.noPQ

end NaturalOvergroupModule

section SL2Facts

variable {F : Type*} [Field F] [CharP F 2]

theorem smul_ne_self_of_cube_eq_one {s : Matrix.SpecialLinearGroup (Fin 2) F} (hs1 : s ≠ 1)
    (hs3 : s * s * s = 1) {w : Fin 2 → F} (hw : w ≠ 0) : s • w ≠ w := by
  intro h
  have hmem : s ∈ rootGrp (Projectivization.mk F w hw) := mem_rootGrp_mk_of_smul_eq hw h
  have hss : s * s = 1 := mul_self_eq_one_of_mem_rootGrp hmem
  apply hs1
  have : s = s * s * s * (s * s)⁻¹ := by group
  rw [this, hs3, hss]; simp

theorem eq_of_four_distinct {V : Type*} [Fintype V] (hV : Fintype.card V = 4) {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (v : V) : v = a ∨ v = b ∨ v = c ∨ v = d := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hva, hvb, hvc, hvd⟩ := hcon
  have hinj : Function.Injective (![a, b, c, d, v] : Fin 5 → V) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have := Fintype.card_le_of_injective _ hinj
  simp at this
  omega

end SL2Facts

namespace NaturalOvergroupModule

variable {G : Type*} [Group G] [Finite G] {X K D : Subgroup G} {F : Type*} [Field F] [CharP F 2]
  [Finite F]
  {ρ : D →* Matrix.SpecialLinearGroup (Fin 2) F}
  {β : (⁅blockQ X, K⁆ : Subgroup G) →* Multiplicative (Fin 2 → F)}
  (m : NaturalOvergroupModule X K D ρ β) (h : NaturalOvergroupSetup X K)
include m h

omit [CharP F 2] [Finite G] in
theorem rhoK_eq_top {n : ℕ} (hn : 1 < n) (hcard : Nat.card F = 2 ^ n) : rhoK K ρ = ⊤ := by
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have : Fintype F := Fintype.ofFinite F
    have h4' : 4 ≤ Fintype.card F := by
      rw [← Nat.card_eq_fintype_card, hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by simpa using h4')
    exact ⟨t, ht⟩
  have hperf := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  have := m.rhoK_normal h
  refine NoPQuotient.of_isPerfect (p := 2) hperf (rhoK K ρ) ?_
  intro x
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨j, hj⟩ := m.rhoK_two_quot h s
  exact ⟨j, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hj⟩

omit [Finite G] in
theorem rhoK_eq_zpowers (hcard : Nat.card F = 2) :
    ∃ t : Matrix.SpecialLinearGroup (Fin 2) F, orderOf t = 3 ∧ rhoK K ρ = Subgroup.zpowers t := by
  obtain ⟨t, ht3⟩ := exists_slPerm_orderOf_three (k := F)
  obtain ⟨j, hj⟩ := m.rhoK_two_quot h t
  have htK : t ∈ rhoK K ρ := mem_of_odd_orderOf_of_pow_mem (by rw [ht3]; decide) hj
  refine ⟨t, ht3, ?_⟩
  have hS6 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 6 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hcard]; norm_num
  have hz3 : Nat.card (Subgroup.zpowers t) = 3 := by rw [Nat.card_zpowers, ht3]
  have hle : Subgroup.zpowers t ≤ rhoK K ρ := Subgroup.zpowers_le.mpr htK
  refine le_antisymm ?_ hle
  set N' : Subgroup (rhoK K ρ) := (Subgroup.zpowers t).subgroupOf (rhoK K ρ) with hN'
  have hN'card : Nat.card N' = 3 := by
    rw [← hz3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hdvd : Nat.card (rhoK K ρ) ∣ 6 := hS6 ▸ Subgroup.card_subgroup_dvd_card _
  have hidx := Subgroup.card_mul_index N'
  rw [hN'card] at hidx
  have hidx12 : N'.index = 1 ∨ N'.index = 2 := by
    have : N'.index ∣ 2 := by
      have h6 : 3 * N'.index ∣ 3 * 2 := by simpa using (hidx ▸ hdvd : 3 * N'.index ∣ 6)
      exact (Nat.mul_dvd_mul_iff_left (by norm_num)).mp h6
    rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h2
    · exact Or.inl h1
    · exact Or.inr h2
  have hN'top : N' = ⊤ := by
    rcases hidx12 with h1 | h2
    · exact Subgroup.index_eq_one.mp h1
    · have : N'.Normal := Subgroup.normal_of_index_eq_two h2
      have hq : IsPGroup 2 (rhoK K ρ ⧸ N') := by
        apply IsPGroup.of_card (n := 1)
        rw [← Subgroup.index_eq_card, h2]; norm_num
      exact m.rhoK_noPQuotient h N' hq
  intro x hx
  have : (⟨x, hx⟩ : rhoK K ρ) ∈ N' := hN'top ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

omit [Finite G] in
theorem rhoK_trans {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n) {w w' : Fin 2 → F}
    (hw : w ≠ 0) (hw' : w' ≠ 0) : ∃ A ∈ rhoK K ρ, A • w = w' := by
  rcases Nat.lt_or_ge 1 n with hn1 | hn1
  · have htop := m.rhoK_eq_top h hn1 hcard
    obtain ⟨A₁, hA₁⟩ := exists_smul_e0 hw
    obtain ⟨A₂, hA₂⟩ := exists_smul_e0 hw'
    refine ⟨A₂ * A₁⁻¹, htop ▸ Subgroup.mem_top _, ?_⟩
    rw [mul_smul, ← hA₁, inv_smul_smul, hA₂]
  · have hn1' : n = 1 := le_antisymm hn1 hn
    subst hn1'
    have hcard2 : Nat.card F = 2 := by simpa using hcard
    obtain ⟨t, ht3, hrho⟩ := m.rhoK_eq_zpowers h hcard2
    have t1 : t * t * t = 1 := by
      have := pow_orderOf_eq_one t
      rw [ht3] at this
      rw [← pow_two, ← pow_succ]; exact this
    have ht1 : t ≠ 1 := by
      intro h1; rw [h1, orderOf_one] at ht3; omega
    have htt1 : t * t ≠ 1 := by
      intro h1
      apply ht1
      have : t = t * t * t * (t * t)⁻¹ := by group
      rw [this, t1, h1]; simp
    have htt3 : (t * t) * (t * t) * (t * t) = 1 := by
      calc (t * t) * (t * t) * (t * t) = (t * t * t) * (t * t * t) := by group
        _ = 1 := by rw [t1]; simp
    have hz : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F, A • (0 : Fin 2 → F) = 0 := by
      intro A; rw [Matrix.SpecialLinearGroup.smul_def]; exact Matrix.mulVec_zero _
    have hzero : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F, A • w = 0 → False := by
      intro A hA
      apply hw
      have h1 : A⁻¹ • (A • w) = A⁻¹ • (0 : Fin 2 → F) := by rw [hA]
      rw [inv_smul_smul, hz] at h1
      exact h1
    have : Fintype F := Fintype.ofFinite F
    have hV : Fintype.card (Fin 2 → F) = 4 := by
      rw [← Nat.card_eq_fintype_card, card_fin_two_pi, hcard2]; norm_num
    have hcases := eq_of_four_distinct hV (a := (0 : Fin 2 → F)) (b := w) (c := t • w)
      (d := (t * t) • w) hw.symm (fun h => hzero t h.symm) (fun h => hzero (t * t) h.symm)
      (smul_ne_self_of_cube_eq_one ht1 t1 hw).symm
      (smul_ne_self_of_cube_eq_one htt1 htt3 hw).symm
      (by
        intro h
        apply smul_ne_self_of_cube_eq_one ht1 t1 hw
        have h1 : t⁻¹ • (t • w) = t⁻¹ • ((t * t) • w) := by rw [h]
        rw [inv_smul_smul, ← mul_smul] at h1
        have h2 : t⁻¹ * (t * t) = t := by group
        rw [h2] at h1
        exact h1.symm) w'
    rcases hcases with h0 | h1 | h2 | h3
    · exact absurd h0 hw'
    · exact ⟨1, one_mem _, by rw [one_smul, h1]⟩
    · exact ⟨t, hrho ▸ Subgroup.mem_zpowers t, h2.symm⟩
    · exact ⟨t * t, hrho ▸ (Subgroup.mul_mem _ (Subgroup.mem_zpowers t) (Subgroup.mem_zpowers t)),
        h3.symm⟩

omit [Finite G] in
theorem rhoK_fixed_zero {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n) {w : Fin 2 → F}
    (hfix : ∀ A ∈ rhoK K ρ, A • w = w) : w = 0 := by
  by_contra hw
  have h0 : (Pi.single 0 1 : Fin 2 → F) ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
  have h1 : (Pi.single 1 1 : Fin 2 → F) ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
  obtain ⟨A, hA, hAe⟩ := m.rhoK_trans h hn hcard hw h0
  obtain ⟨B, hB, hBe⟩ := m.rhoK_trans h hn hcard hw h1
  have : (Pi.single 0 1 : Fin 2 → F) = Pi.single 1 1 := by
    rw [← hAe, hfix A hA, ← hBe, hfix B hB]
  have h2 := congrFun this 0
  simp at h2

omit [Finite G] in
theorem inf_centralizer_K_eq {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n) :
    ⁅blockQ X, K⁆ ⊓ Subgroup.centralizer (K : Set G) =
      ⁅blockQ X, K⁆ ⊓ Subgroup.centralizer (X : Set G) := by
  apply le_antisymm
  · intro u hu
    refine Subgroup.mem_inf.mpr ⟨hu.1, ?_⟩
    rw [← m.β_eq_one_iff ⟨u, hu.1⟩]
    apply Multiplicative.toAdd.injective
    show Multiplicative.toAdd (β ⟨u, hu.1⟩) = 0
    refine m.rhoK_fixed_zero h hn hcard (fun A hA => ?_)
    obtain ⟨d, hd, rfl⟩ := hA
    have hdK : (d : G) ∈ K := Subgroup.mem_subgroupOf.mp hd
    have hcomm : (d : G) * u * (d : G)⁻¹ = u := by
      have := Subgroup.mem_centralizer_iff.mp hu.2 (d : G) hdK
      rw [this]; group
    have := m.β_equiv d ⟨u, hu.1⟩ ⟨u, hu.1⟩ hcomm.symm
    rw [Matrix.SpecialLinearGroup.smul_def]
    exact this.symm
  · exact inf_le_inf_left _ (Subgroup.centralizer_le h.le)

omit [Finite G] in
theorem inf_centralizer_K_lt {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n) :
    ⁅blockQ X, K⁆ ⊓ Subgroup.centralizer (K : Set G) < ⁅blockQ X, K⁆ := by
  rw [m.inf_centralizer_K_eq h hn hcard]
  refine lt_of_le_of_ne inf_le_left fun heq => ?_
  have h0 : (Pi.single 0 1 : Fin 2 → F) ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
  obtain ⟨u, hu⟩ := m.β_surj (Multiplicative.ofAdd (Pi.single 0 1))
  have hC : (u : G) ∈ Subgroup.centralizer (X : Set G) := by
    have : (u : G) ∈ (⁅blockQ X, K⁆ ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := by
      rw [heq]; exact u.2
    exact this.2
  have := (m.β_eq_one_iff u).mpr hC
  rw [hu] at this
  apply h0
  have h2 := congrArg Multiplicative.toAdd this
  simp at h2

omit [Finite G] in
theorem irreducible {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n) (W : Subgroup G)
    (hZW : ⁅blockQ X, K⁆ ⊓ Subgroup.centralizer (K : Set G) ≤ W) (hWU : W ≤ ⁅blockQ X, K⁆)
    (hN : K ≤ Subgroup.normalizer (W : Set G)) :
    W = ⁅blockQ X, K⁆ ⊓ Subgroup.centralizer (K : Set G) ∨ W = ⁅blockQ X, K⁆ := by
  rw [m.inf_centralizer_K_eq h hn hcard] at hZW ⊢
  set Wβ : Set (Fin 2 → F) := {w | ∃ x : (⁅blockQ X, K⁆ : Subgroup G), (x : G) ∈ W ∧
    Multiplicative.toAdd (β x) = w} with hWβ
  have h0 : (0 : Fin 2 → F) ∈ Wβ := ⟨1, W.one_mem, by simp⟩
  have hinv : ∀ A ∈ rhoK K ρ, ∀ w ∈ Wβ, A • w ∈ Wβ := by
    rintro A ⟨d, hd, rfl⟩ w ⟨x, hxW, rfl⟩
    have hdK : (d : G) ∈ K := Subgroup.mem_subgroupOf.mp hd
    have hxU : (d : G) * x * (d : G)⁻¹ ∈ (⁅blockQ X, K⁆ : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_U (m.DX d.2)) x).mp x.2
    refine ⟨⟨(d : G) * x * (d : G)⁻¹, hxU⟩, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hN hdK) x).mp hxW
    · rw [Matrix.SpecialLinearGroup.smul_def]
      exact m.β_equiv d x ⟨(d : G) * x * (d : G)⁻¹, hxU⟩ rfl
  by_cases hex : ∃ w ∈ Wβ, w ≠ 0
  · right
    obtain ⟨w, hwW, hw0⟩ := hex
    have hall : ∀ w' : Fin 2 → F, w' ∈ Wβ := by
      intro w'
      by_cases hw' : w' = 0
      · rw [hw']; exact h0
      · obtain ⟨A, hA, hAe⟩ := m.rhoK_trans h hn hcard hw0 hw'
        rw [← hAe]; exact hinv A hA w hwW
    apply le_antisymm hWU
    intro y hy
    obtain ⟨x, hxW, hxy⟩ := hall (Multiplicative.toAdd (β ⟨y, hy⟩))
    have hker : (⟨y, hy⟩ : (⁅blockQ X, K⁆ : Subgroup G)) * x⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have : β x = β ⟨y, hy⟩ := Multiplicative.toAdd.injective hxy
      rw [this, mul_inv_cancel]
    rw [m.β_ker, Subgroup.mem_subgroupOf] at hker
    have hyx : y * (x : G)⁻¹ ∈ W := hZW hker
    have : y = (y * (x : G)⁻¹) * (x : G) := by group
    rw [this]
    exact W.mul_mem hyx hxW
  · left
    push Not at hex
    apply le_antisymm
    · intro y hy
      refine Subgroup.mem_inf.mpr ⟨hWU hy, ?_⟩
      have hβy : Multiplicative.toAdd (β ⟨y, hWU hy⟩) = 0 :=
        hex _ ⟨⟨y, hWU hy⟩, hy, rfl⟩
      have : β ⟨y, hWU hy⟩ = 1 := Multiplicative.toAdd.injective (by simpa using hβy)
      exact (m.β_eq_one_iff _).mp this
    · exact hZW

end NaturalOvergroupModule

theorem isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.IsQuasisimple A) : CFSG.IsQuasisimple B :=
  hA.of_mulEquiv e.symm

theorem isQuasisimple_sl2 {F : Type*} [Field F] [Finite F] (h4 : ∃ s : Finset F, s.card = 4) :
    CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hperf := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  obtain ⟨hnt, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl
    (Or.inr h4)
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hcomm
  simp only [not_exists, not_not] at hcomm
  have hPerfPSL : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := inferInstance
  have : IsMulCommutative (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := ⟨⟨hcomm⟩⟩
  exact Group.IsPerfect.not_isMulCommutative _ this

namespace NaturalOvergroupModule

variable {G : Type*} [Group G] [Finite G] {X K D : Subgroup G} {F : Type*} [Field F] [CharP F 2]
  [Finite F]
  {ρ : D →* Matrix.SpecialLinearGroup (Fin 2) F}
  {β : (⁅blockQ X, K⁆ : Subgroup G) →* Multiplicative (Fin 2 → F)}
  (m : NaturalOvergroupModule X K D ρ β) (h : NaturalOvergroupSetup X K)
include m h

omit [Finite G] [CharP F 2] [Finite F] h in
theorem range_fK : (ρ.comp (Subgroup.inclusion m.KD)).range = rhoK K ρ := by
  ext y
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨Subgroup.inclusion m.KD k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨(d : G), Subgroup.mem_subgroupOf.mp hd⟩, rfl⟩

omit [Finite F] in
theorem ker_fK : (ρ.comp (Subgroup.inclusion m.KD)).ker = CFSG.pCore 2 K := by
  have hKQ : blockQ K = K ⊓ blockQ X := h.blockQ_D le_rfl h.le
  have hmap : blockQ K = (CFSG.pCore 2 K).map K.subtype := blockQ_eq_map K
  ext x
  have h1 : x ∈ CFSG.pCore 2 K ↔ (x : G) ∈ blockQ X := by
    have : (x : G) ∈ (CFSG.pCore 2 K).map K.subtype ↔ x ∈ CFSG.pCore 2 K :=
      Subgroup.mem_map_iff_mem K.subtype_injective
    rw [← this, ← hmap, hKQ]
    exact ⟨fun hx => hx.2, fun hx => ⟨x.2, hx⟩⟩
  rw [h1, MonoidHom.mem_ker]
  constructor
  · intro hx
    have : (x : G) ∈ ρ.ker.map D.subtype := ⟨Subgroup.inclusion m.KD x, hx, rfl⟩
    rw [m.ker_map_eq h] at this
    exact this.2
  · intro hx
    have : (x : G) ∈ D ⊓ blockQ X := ⟨m.KD x.2, hx⟩
    rw [← m.ker_map_eq h] at this
    obtain ⟨d, hd, hdx⟩ := this
    have hd' : d = Subgroup.inclusion m.KD x := Subtype.ext hdx
    show ρ (Subgroup.inclusion m.KD x) = 1
    rw [← hd']
    exact hd

end NaturalOvergroupModule

section Main

open scoped commutatorElement

theorem natural_overgroup_recognizes_actual_chi0_block
    {G : Type*} [Group G] [Finite G] {X K D : Subgroup G} {F : Type} [Field F] [Finite F]
    [CharP F 2] {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n)
    {ρ : D →* Matrix.SpecialLinearGroup (Fin 2) F}
    {β : (⁅blockQ X, K⁆ : Subgroup G) →* Multiplicative (Fin 2 → F)}
    (h : NaturalOvergroupSetup X K) (m : NaturalOvergroupModule X K D ρ β) :
    (∀ x ∈ ⁅blockQ X, K⁆, x ^ 2 = 1) ∧
      X ⊓ Subgroup.centralizer ((⁅blockQ X, K⁆ : Subgroup G) : Set G) = blockQ X ∧
      ρ.ker.map D.subtype = D ⊓ blockQ X ∧ blockQ D = D ⊓ blockQ X ∧
      IsShort2 K ∧ IsChi0Block X K ∧ blockU K = ⁅blockQ X, K⁆ ∧
      blockZ K = ⁅blockQ X, K⁆ ⊓ Subgroup.centralizer (X : Set G) ∧
      (ρ.comp (Subgroup.inclusion m.KD)).ker = CFSG.pCore 2 K ∧
      (1 < n → Function.Surjective (ρ.comp (Subgroup.inclusion m.KD)) ∧ IsLin2Type K n) ∧
      (n = 1 → Nat.card (K ⧸ CFSG.pCore 2 K) = 3 ∧ Nonempty (K ≃* alternatingGroup (Fin 4)) ∧
        IsAltType K 3) := by
  classical
  have hexp := m.exp_two' h
  have hnz := m.inf_centralizer_K_lt h hn hcard
  have hirr := fun W hZW hWU hN => m.irreducible h hn hcard W hZW hWU hN
  have hZK := m.inf_centralizer_K_eq h hn hcard
  have hsq : ∀ x ∈ ⁅blockQ X, K⁆, x ^ 2 ∈ ⁅blockQ X, K⁆ ⊓ Subgroup.centralizer (K : Set G) := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨(⁅blockQ X, K⁆ : Subgroup G).pow_mem hx 2, ?_⟩
    exact Subgroup.centralizer_le h.le (m.sq_mem_centralizer ⟨x, hx⟩)
  have hfKker := m.ker_fK h
  have hrange := m.range_fK
  set fK : K →* Matrix.SpecialLinearGroup (Fin 2) F := ρ.comp (Subgroup.inclusion m.KD) with hfK
  let eK : K ⧸ CFSG.pCore 2 K ≃* fK.range :=
    (QuotientGroup.quotientMulEquivOfEq hfKker.symm).trans (QuotientGroup.quotientKerEquivRange fK)
  have hcard3 : n = 1 → Nat.card (K ⧸ CFSG.pCore 2 K) = 3 := by
    intro hn1'
    subst hn1'
    have hcard2 : Nat.card F = 2 := by simpa using hcard
    obtain ⟨t, ht3, hrho⟩ := m.rhoK_eq_zpowers h hcard2
    rw [Nat.card_congr eK.toEquiv, hrange, hrho, Nat.card_zpowers, ht3]
  have hq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K) ∨ Nat.card (K ⧸ CFSG.pCore 2 K) = 3 := by
    rcases Nat.lt_or_ge 1 n with hn1 | hn1
    · left
      have htop := m.rhoK_eq_top h hn1 hcard
      have h4 : ∃ s : Finset F, s.card = 4 := by
        have : Fintype F := Fintype.ofFinite F
        have h4' : 4 ≤ Fintype.card F := by
          rw [← Nat.card_eq_fintype_card, hcard]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
        obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
          (by simpa using h4')
        exact ⟨t, ht⟩
      have hfKtop : fK.range = ⊤ := hrange.trans htop
      let e2 : fK.range ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
        (MulEquiv.subgroupCongr hfKtop).trans Subgroup.topEquiv
      exact isQuasisimple_of_mulEquiv (eK.trans e2).symm (isQuasisimple_sl2 h4)
    · right
      exact hcard3 (le_antisymm hn1 hn)
  obtain ⟨hQK, hUK, -, hchar, hshort, hblock, hchi⟩ :=
    central_core_module_recognizes_short_subgroup h.charTwo h.le h.normal.isSubnormal h.noPQ hq
      h.central hnz hsq hirr
  have hZKK : blockZ K = ⁅blockQ X, K⁆ ⊓ Subgroup.centralizer (X : Set G) := by
    unfold blockZ; rw [hUK, hZK]
  have hLin : 1 < n → Function.Surjective fK ∧ IsLin2Type K n := by
    intro hn1
    have htop := m.rhoK_eq_top h hn1 hcard
    have hfKs : Function.Surjective fK := MonoidHom.range_eq_top.mp (hrange.trans htop)
    refine ⟨hfKs, F, inferInstance, Fintype.ofFinite F, ?_, fK, hfKs, hfKker, ?_⟩
    · exact (@Nat.card_eq_fintype_card F (Fintype.ofFinite F)).symm.trans hcard
    · let e : ↥(blockU K) ≃* ↥(⁅blockQ X, K⁆ : Subgroup G) := MulEquiv.subgroupCongr hUK
      refine ⟨β.comp e.toMonoidHom, m.β_surj.comp e.surjective, ?_, ?_⟩
      · ext u
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hZKK]
        show β (e u) = 1 ↔ _
        rw [m.β_eq_one_iff (e u)]
        exact ⟨fun hc => Subgroup.mem_inf.mpr ⟨(e u).2, hc⟩, fun hc => hc.2⟩
      · intro ℓ u v huv
        exact m.β_equiv (Subgroup.inclusion m.KD ℓ) (e u) (e v) huv
  have hAlt : n = 1 → Nat.card (K ⧸ CFSG.pCore 2 K) = 3 ∧
      Nonempty (K ≃* alternatingGroup (Fin 4)) ∧ IsAltType K 3 := by
    intro hn1
    have h3 := hcard3 hn1
    obtain ⟨-, -, -, hA4, hA⟩ := short_order_three_is_alternating_four hshort h3
    exact ⟨h3, hA4, hA⟩
  refine ⟨hexp, h.centralizer_U, m.ker_map_eq h, h.blockQ_D m.KD m.DX, hshort, ?_, hUK, hZKK,
    hfKker, hLin, hAlt⟩
  rcases Nat.lt_or_ge 1 n with hn1 | hn1
  · exact hchi (Or.inl ⟨n, hn1, (hLin hn1).2⟩)
  · exact hchi (Or.inr (Or.inl (hAlt (le_antisymm hn1 hn)).2.2))

end Main


end CFSG.QuasithinUnique.Setup.Campbell
