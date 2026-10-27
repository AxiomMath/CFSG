module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q2201
public import CFSG.ClassicalInvolution.Q3.Q3T8C262A
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01
public import CFSG.ClassicalInvolution.Q3.Q3T7W21A01

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace T7A
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7A

theorem mem_omegaOfSet_of_mem_kPerp
    (hΩ
    : Q3T7M.HM Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ KPerp Ω K) (hJnot : J ∉ twinSet Ω K) :
    J ∈ omegaOfSet Ω (twinSet Ω K) := by
  have hJΩ : J ∈ Ω := by
    rcases Set.mem_insert_iff.mp hJ with h | h
    · exact h ▸ hK
    · exact h.1
  refine ⟨hJΩ, fun L hL => ?_⟩
  have hKL := (CFSG.ClassicalInvolution.Q3.Q3T7M.l6_3 G Ω hΩ K hK L hL).1
  have hJL : J ∈ KPerp Ω L := hKL ▸ hJ
  rcases Set.mem_insert_iff.mp hJL with h | h
  · exact absurd (h ▸ hL) hJnot
  · exact h
end T7A
section Alpha
variable [IsSimpleGroup G]

@[expose] def TwinNormAlpha : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      ∀ L ∈ twinSet Ω K, L ≤ Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G)

structure AlphaSteps : Prop where
  h3 : Q3T8.Asc77.C21_3
  h4 : Q3T8.Asc77.TwinNormAlpha

theorem AlphaSteps.alpha_zt
    (hs
    : Q3T8.Asc77.AlphaSteps) {K K' J W : Subgroup G} {z u t : G}
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) :
    alphaOf (Subgroup.closure ({z, t} : Set G)) = alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hfr := h.twinFrameData
  have hz2 : z * z = 1 := h.std.hz.sq
  have hA : IsElemAbelian2 (Subgroup.closure ({z, t} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hz2 h.ht.sq h.std.hz.ne_one h.ht.ne_one hfr.t_ne_z.symm
      (hfr.comm_zt hΩ)
  have hle : Subgroup.closure ({z, t} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) := by
    apply Subgroup.closure_mono
    intro x hx
    rcases hx with rfl | rfl <;> simp
  exact (hs.h3 G Ω K K' z u J t W h).2 _ hle hA

theorem AlphaSteps.sup_le_normalizer
    (hs
    : Q3T8.Asc77.AlphaSteps) {K K' J W : Subgroup G} {z u t : G}
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) :
    ∀ g ∈ K ⊔ K', conjSub g (alphaOf (Subgroup.closure ({u, z} : Set G))) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hK : K ∈ Ω := h.std.stand.mem
  have h1 := hs.h4 G Ω K K' z u J t W h
  have hKn : K ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    h1 K (mem_twinSet_self hK h.std.hz)
  have hK'n : K' ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    h1 K' h.std.hK'
  intro g hg
  exact mem_normalizer_iff_conjSub_eq.mp ((sup_le hKn hK'n) hg)

theorem AlphaSteps.alpha_eq
    (hs
    : Q3T8.Asc77.AlphaSteps) {K K' J W J' : Subgroup G} {z u t t' : G}
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) (hJ' : J' ∈ omegaOfSet Ω (twinSet Ω K))
    (ht' : IsUniqueInvolution J' t') :
    alphaOf (Subgroup.closure ({z, t'} : Set G)) = alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  obtain ⟨g, hgQ, W'', hfr, hW'', hzW'', htW''⟩ :=
    Q3T8.Asc77.exists_twinFrameData_at hΩ h.std.stand.mem h.std.hz h.std.hK' h.std.hne h.hu h.hu2
      h.hu1 h.huz hJ' ht'
  have h' : Q3T8.Asc77.Hyp21 Ω K K' z u (conjSub g J') (g * t' * g⁻¹) W'' :=
    Q3T8.Asc77.Hyp21.of_twinFrameData h.std hfr hW'' hzW'' htW''
  have h1 := hs.alpha_zt h'
  have hgz : g * z * g⁻¹ = z := by
    have := T7A.z_comm_of_mem_sup h.std.hz (isUniqueInvolution_of_mem_twinSet h.std.hz h.std.hK')
      hgQ
    calc g * z * g⁻¹ = (g * z) * g⁻¹ := rfl
      _ = (z * g) * g⁻¹ := by rw [← this]
      _ = z := by group
  have h2 : conjSub g (Subgroup.closure ({z, t'} : Set G)) =
      Subgroup.closure ({z, g * t' * g⁻¹} : Set G) := by
    rw [T7A.conjSub_closure_pair, hgz]
  have h3 : alphaOf (Subgroup.closure ({z, g * t' * g⁻¹} : Set G)) =
      conjSub g (alphaOf (Subgroup.closure ({z, t'} : Set G))) := by
    rw [← h2, alphaOf_conjSub]
  have hgi := hs.sup_le_normalizer h g⁻¹ (Subgroup.inv_mem _ hgQ)
  have : conjSub g (alphaOf (Subgroup.closure ({z, t'} : Set G))) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := h3 ▸ h1
  calc alphaOf (Subgroup.closure ({z, t'} : Set G))
      = conjSub g⁻¹ (conjSub g (alphaOf (Subgroup.closure ({z, t'} : Set G)))) :=
        (conjSub_inv_conjSub g _).symm
    _ = conjSub g⁻¹ (alphaOf (Subgroup.closure ({u, z} : Set G))) := by rw [this]
    _ = alphaOf (Subgroup.closure ({u, z} : Set G)) := hgi

theorem AlphaSteps.conj_alpha_of_mem_centralizer
    (hs : Q3T8.Asc77.AlphaSteps) {K K' J W : Subgroup G}
    {z u t : G} (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    conjSub c (alphaOf (Subgroup.closure ({u, z} : Set G))) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
      _ = z := by group
  have hL : conjSub c K ∈ twinSet Ω K :=
    ⟨hΩ.conjInvariant c K hK, z, h.std.hz, hcz ▸ h.std.hz.conj c⟩
  have hc' := h.conj c
  have hJc : conjSub c J ∈ omegaOfSet Ω (twinSet Ω K) := by
    have := hc'.hJ
    rwa [twinSet_eq_of_mem_twinSet h.std.hz hL] at this
  have hB := hs.alpha_zt hc'
  rw [hcz] at hB
  have hD := hs.alpha_eq h hJc (hc'.ht)
  have hA : conjSub c (alphaOf (Subgroup.closure ({u, z} : Set G))) =
      alphaOf (Subgroup.closure ({c * u * c⁻¹, z} : Set G)) := by
    rw [← hcz, ← T7A.conjSub_closure_pair, ← alphaOf_conjSub]
    rw [hcz]
  exact hA.trans (hB.symm.trans hD)

theorem AlphaSteps.conj_alpha_of_omegaNbr
    (hs
    : Q3T8.Asc77.AlphaSteps) {K K' J W L : Subgroup G}
    {z u t : G} (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) (hL : L ∈ omegaNbr Ω K) {y : G}
    (hy : conjSub y K = L) :
    conjSub y (alphaOf (Subgroup.closure ({u, z} : Set G))) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hLΩ : L ∈ Ω := hL.1
  have htL : IsUniqueInvolution L (y * z * y⁻¹) := hy ▸ h.std.hz.conj y
  by_cases htw : L ∈ twinSet Ω K
  · have hzL := isUniqueInvolution_of_mem_twinSet h.std.hz htw
    have : y * z * y⁻¹ = z := (htL.eq hzL).symm ▸ rfl
    exact hs.conj_alpha_of_mem_centralizer h (T7A.mem_centralizer_of_conj_eq this)
  · have hLmem : L ∈ omegaOfSet Ω (twinSet Ω K) :=
      Q3T8.Asc77.T7A.mem_omegaOfSet_of_mem_kPerp hΩ hK (Set.mem_insert_of_mem _ hL) htw
    have hD := hs.alpha_eq h hLmem htL
    have hy' := h.conj y
    rw [hy] at hy'
    have hKL : K ∈ omegaNbr Ω L := Q3CL.T3.omegaNbr_symm (Q3T8.Asc77.l6_2) hΩ hK hLΩ hL
    have hKnot : K ∉ twinSet Ω L := by
      rintro ⟨-, z₀, hz₀L, hz₀K⟩
      exact htw ⟨hLΩ, z₀, hz₀K, hz₀L⟩
    have hKmem : K ∈ omegaOfSet Ω (twinSet Ω L) :=
      Q3T8.Asc77.T7A.mem_omegaOfSet_of_mem_kPerp hΩ hLΩ (Set.mem_insert_of_mem _ hKL) hKnot
    have hC := hs.alpha_eq hy' hKmem h.std.hz
    have hA : conjSub y (alphaOf (Subgroup.closure ({u, z} : Set G))) =
        alphaOf (Subgroup.closure ({y * u * y⁻¹, y * z * y⁻¹} : Set G)) := by
      rw [← T7A.conjSub_closure_pair, ← alphaOf_conjSub]
    calc conjSub y (alphaOf (Subgroup.closure ({u, z} : Set G)))
        = alphaOf (Subgroup.closure ({y * u * y⁻¹, y * z * y⁻¹} : Set G)) := hA
      _ = alphaOf (Subgroup.closure ({y * z * y⁻¹, z} : Set G)) := hC.symm
      _ = alphaOf (Subgroup.closure ({z, y * z * y⁻¹} : Set G)) := by rw [Set.pair_comm]
      _ = alphaOf (Subgroup.closure ({u, z} : Set G)) := hD

theorem AlphaSteps.conj_alpha_of_mem_dComp
    (hs : Q3T8.Asc77.AlphaSteps) {K K' J W : Subgroup G}
    {z u t : G} (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) :
    ∀ M ∈ dComp Ω K, ∀ x : G, conjSub x K = M →
      conjSub x (alphaOf (Subgroup.closure ({u, z} : Set G))) =
        alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hΩc : ConjInvariant Ω := hΩ.conjInvariant
  have hbase : ∀ n : G, conjSub n K = K →
      conjSub n (alphaOf (Subgroup.closure ({u, z} : Set G))) =
        alphaOf (Subgroup.closure ({u, z} : Set G)) := fun n hn =>
    hs.conj_alpha_of_mem_centralizer h (T7A.mem_centralizer_of_conj_eq (h.std.hz.conj_eq hn))
  intro M hM
  induction hM with
  | refl => exact fun x hx => hbase x hx
  | @tail b c hab hbc ih =>
    intro x' hx'
    have hbΩ : b ∈ Ω := T7A.mem_of_mem_dComp hK hab
    obtain ⟨x₀, hx₀⟩ := h.std.stand.trans b hbΩ
    have hcΩ : c ∈ Ω := hbc.1
    have hLΩ : conjSub x₀⁻¹ c ∈ Ω := hΩc _ _ hcΩ
    have hadj : dAdj Ω K (conjSub x₀⁻¹ c) := by
      have := T7A.dAdj_conjSub hΩc hbc.2 x₀⁻¹
      rwa [← hx₀, conjSub_inv_conjSub] at this
    have hLnbr : conjSub x₀⁻¹ c ∈ omegaNbr Ω K := by
      rcases hadj with h1 | h1
      · exact h1
      · exact Q3CL.T3.omegaNbr_symm (Q3T8.Asc77.l6_2) hΩ hLΩ hK h1
    obtain ⟨y, hy⟩ := h.std.stand.trans _ hLΩ
    have hyα := hs.conj_alpha_of_omegaNbr h hLnbr hy
    have hxy : conjSub (x₀ * y) K = c := by
      rw [conjSub_mul, hy, conjSub_conjSub_inv]
    have hn : conjSub ((x₀ * y)⁻¹ * x') K = K := by
      rw [conjSub_mul, hx', ← hxy, conjSub_inv_conjSub]
    have hnα := hbase _ hn
    have hx'eq : x' = x₀ * y * ((x₀ * y)⁻¹ * x') := by group
    rw [hx'eq, conjSub_mul, conjSub_mul, hnα, hyα, ih x₀ hx₀]

theorem AlphaSteps.exists_mem_normalizer
    (hs
    : Q3T8.Asc77.AlphaSteps) {K K' J W : Subgroup G}
    {z u t : G} (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) {M : Subgroup G} (hM : M ∈ dComp Ω K) :
    ∃ x ∈ Subgroup.normalizer
        (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G), conjSub x K = M := by
  obtain ⟨x, hx⟩ := h.std.stand.trans M (T7A.mem_of_mem_dComp h.std.stand.mem hM)
  exact ⟨x, mem_normalizer_iff_conjSub_eq.mpr (hs.conj_alpha_of_mem_dComp h M hM x hx), hx⟩
end Alpha
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
section Cases
variable {G : Type} [Group G] [Finite G]

theorem twinFrameHyp51_of_cases
    (hz
    : Q3T8.Asc77.TwinFrameHyp51z) (ht : Q3T8.Asc77.TwinFrameHyp51t)
    (hu : Q3T8.Asc77.TwinFrameHyp51u) : Q3T8.Asc77.TwinFrameHyp51 := by
  intro G _ _ _ Ω K K' J z u t hs
  have hfr := hs.frame
  have hcg := hfr.comm_gen hs.hyp
  have hzu : Commute z u := hcg z (by simp) u (by simp)
  have hzt : Commute z t := hcg z (by simp) t (by simp)
  have hut : Commute u t := hcg u (by simp) t (by simp)
  have hz2 : z * z = 1 := hfr.hz.sq
  have hu2 : u * u = 1 := hfr.hu2
  have ht2 : t * t = 1 := hfr.ht.sq
  refine ⟨Q3T8.Asc77.twinFrame_isElemAbelian hs.hyp hfr,
    Q3T8.Asc77.twinFrame_natCard_eight hs.hyp hfr, ?_⟩
  intro c hc hc1
  obtain ⟨a, b, d, rfl⟩ := T7A.mem_closure_words hz2 hu2 ht2 hzu hzt hut hc
  have hz' := hz G Ω K K' J z u t hs
  have ht' := ht G Ω K K' J z u t hs
  have hu' := hu G Ω K K' J z u t hs
  rw [T7A.pow_eq_pow_mod_two hz2 a, T7A.pow_eq_pow_mod_two hu2 b,
    T7A.pow_eq_pow_mod_two ht2 d] at hc1 ⊢
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    rcases Nat.mod_two_eq_zero_or_one d with hd | hd <;> rw [ha, hb, hd] at hc1 ⊢
  · exact absurd (by simp) hc1
  · simpa using ht'.1
  · simpa using hu'.1
  · simpa [hut.eq] using hu'.2.2.1
  · simpa using hz'
  · simpa [hzt.eq] using ht'.2
  · simpa [hzu.eq] using hu'.2.1
  · have e : z * u * t = u * t * z := by
      calc z * u * t = u * z * t := by rw [hzu.eq]
        _ = u * (z * t) := by rw [mul_assoc]
        _ = u * (t * z) := by rw [hzt.eq]
        _ = u * t * z := by rw [mul_assoc]
    simpa [e] using hu'.2.2.2
end Cases
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
namespace T7A
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7A

theorem commutator_twin_mem_oddCoreOf
    [Finite G] (hΩ : Q3T7M.HM Ω) {K K' J : Subgroup G} {z u t : G}
    (h : TwinFrameData Ω K K' z u J t) {L : Subgroup G} (hL : L ∈ twinSet Ω K) :
    ∀ ℓ ∈ L, ⁅t, ℓ⁆ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
  have hLΩ : L ∈ Ω := hL.1
  have hzL := isUniqueInvolution_of_mem_twinSet h.hz hL
  have hJΩ : J ∈ Ω := h.hJ.1
  obtain ⟨-, -, R, hR, hRJ, hRN⟩ := h.hJ.2 L hL
  have hRsyl : IsSylow2In R J := hΩ.isSylow2In_of_mem_RSet_of_le hJΩ hR hRJ
  have h8 := hΩ.eight_le_of_mem_RSet hR
  have htR : t ∈ R := mem_of_isUniqueInvolution_of_isPGroup h.ht hRsyl.1 hRsyl.2.1 (by omega)
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_le_normalizer hzL hRN
  have hJnot : J ∉ twinSet Ω L := by
    rintro ⟨-, z₀, hz₀L, hz₀J⟩
    exact h.t_ne_z ((h.ht.eq hz₀J).trans (hzL.eq hz₀L).symm)
  have hV : IsSylow2In R (J ⊓ Subgroup.centralizer ({z} : Set G)) :=
    ⟨le_inf hRJ hRC, hRsyl.2.1, fun V' hV' hV'p hRV' =>
      hRsyl.2.2 V' (hV'.trans inf_le_left) hV'p hRV'⟩
  have htord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.ht.sq) h.ht.ne_one
  rcases Q3T8.Asc77.l6_2 G Ω hΩ L hLΩ z hzL J hJΩ hJnot t h.ht R hV htR with h1 | h1 | h1 | h1
  · exfalso
    have := h8
    rw [h1.1, Nat.card_zpowers, htord] at this
    omega
  · exfalso
    have := h8
    rw [h1.1, Nat.card_zpowers, htord] at this
    omega
  · exfalso
    obtain ⟨R', hR', hle, hcyc, hidx⟩ := h1.1
    obtain ⟨x, hx, y, hy, hxy⟩ := (hΩ.isQuatSub_of_mem_RSet hR).exists_not_commute
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥R)
    have hc : (⟨x, hx⟩ : ↥R) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
      obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
      obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
      rw [← ha, ← hb]
      exact (Commute.zpow_zpow_self g a b).eq
    exact hxy (congrArg Subtype.val hc)
  · intro ℓ hℓ
    have h2 : ⁅t, ℓ⁆ ∈ ⁅R, L⁆ := Subgroup.commutator_mem_commutator htR hℓ
    exact CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal
      (Q3T8.Asc77.T7A.isSubnormal_centralizer hΩ hLΩ hzL) (h1.2 h2)
end T7A

theorem twinNormAlpha_of
    (h3
    : Q3T8.Asc77.C21_3) : Q3T8.Asc77.TwinNormAlpha := by
  intro G _ _ _ Ω K K' z u J t W h L hL
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hfr := h.twinFrameData
  have hB := Q3T8.Asc77.twinFrame_isElemAbelian hΩ hfr
  have hB8 := Q3T8.Asc77.twinFrame_natCard_eight hΩ hfr
  have h3' := (h3 G Ω K K' z u J t W h).2
  have hzu : z * u = u * z := hfr.comm_zu
  have hzt : z * t = t * z := hfr.comm_zt hΩ
  have hz2 : z * z = 1 := h.std.hz.sq
  have ht2 : t * t = 1 := h.ht.sq
  have hBC : Subgroup.closure ({z, u, t} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hzu.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm
  have hO := T7A.oddCore_le_normalizer_alpha hB hB8 hBC h3'
  intro ℓ hℓ
  have hzL := isUniqueInvolution_of_mem_twinSet h.std.hz hL
  have hℓC : ℓ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL.commute_of_mem hℓ).symm
  have htC : t ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm
  have hcommO := Q3T8.Asc77.T7A.commutator_twin_mem_oddCoreOf hΩ hfr hL ℓ hℓ
  have hc' : t * ℓ * t⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
    rwa [commutatorElement_def] at hcommO
  obtain ⟨o, hoO, hfix⟩ := T7A.exists_fixed_mul_of_odd
    (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (Subgroup.centralizer ({z} : Set G)))
    ht2 (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ htC)
    (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ hℓC) hc'
  have hoC : o ∈ Subgroup.centralizer ({z} : Set G) :=
    CFSG.ClassicalInvolution.Balance.oddCoreIn_le _ hoO
  have hcz : ℓ * o ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.mul_mem _ hℓC hoC
  have hct : (ℓ * o) * t = t * (ℓ * o) := (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hE₀ : IsElemAbelian2 (Subgroup.closure ({z, t} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hz2 ht2 h.std.hz.ne_one h.ht.ne_one hfr.t_ne_z.symm hzt
  have hE₀B : Subgroup.closure ({z, t} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) := by
    apply Subgroup.closure_mono
    intro x hx
    rcases hx with rfl | rfl <;> simp
  have hcE₀ : ℓ * o ∈ Subgroup.centralizer ((Subgroup.closure ({z, t} : Set G) : Subgroup G) :
      Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hle : Subgroup.closure ({z, t} : Set G) ≤ Subgroup.centralizer ({ℓ * o} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp
          hcz).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hct.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle he)
  have hcN := T7A.centralizer_le_normalizer_alpha hE₀ hE₀B h3' hcE₀
  have h2 : (ℓ * o) * o⁻¹ ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    Subgroup.mul_mem _ hcN (Subgroup.inv_mem _ (hO hoO))
  rwa [mul_inv_cancel_right] at h2
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}

theorem AlphaSteps.twin_sup_le
    (hs
    : Q3T8.Asc77.AlphaSteps) {K K' J W L L' : Subgroup G} {z u t : G}
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) (hL : L ∈ twinSet Ω K) (hL' : L' ∈ twinSet Ω K) :
    ∀ g ∈ L ⊔ L', conjSub g (alphaOf (Subgroup.closure ({u, z} : Set G))) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hmem := hs.h4 G Ω K K' z u J t W h
  intro g hg
  exact mem_normalizer_iff_conjSub_eq.mp ((sup_le (hmem L hL) (hmem L' hL')) hg)
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
namespace T7A
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7A

theorem sup_le_normalizer_of_twin
    [Finite G] (hΩ : Q3T8.Asc77.HypOmegaMod Ω) {K K' : Subgroup G}
    {z : G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) : K ⊔ K' ≤ Subgroup.normalizer (K : Set G) :=
  sup_le Subgroup.le_normalizer (hΩ.le_normalizer_of_twin hK' hK hne hz' hz)

theorem mem_sigmaStarNorm_of_mem_sup
    [Finite G] (hΩ : Q3T8.Asc77.HypOmegaMod Ω) {K K' : Subgroup G}
    {z : G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) {g : G} (hg : g ∈ K ⊔ K') : g ∈ sigmaStarNorm Ω K := by
  have hgK : conjSub g K = K :=
    mem_normalizer_iff_conjSub_eq.mp (Q3T8.Asc77.T7A.sup_le_normalizer_of_twin hΩ hK hK' hne hz hz'
        hg)
  exact mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK
    (by rw [hgK]; exact Relation.ReflTransGen.refl)
end T7A
section Finite
variable [Finite G]

theorem stdCent_sigmaStarNorm
    (hΩ
    : Q3T7M.HM Ω)
    {K : Subgroup G} {z : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g K = M)
    (htail : StdCentTail Ω K (sigmaStarNorm Ω K) z) : StdCent Ω K (sigmaStarNorm Ω K) z := by
  have hz_le : Subgroup.centralizer ({z} : Set G) ≤ sigmaStarNorm Ω K := by
    intro c hc
    have hcz : c * z * c⁻¹ = z := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc
      calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
        _ = z := by group
    have hL : conjSub c K ∈ twinSet Ω K :=
      ⟨hΩ.conjInvariant c K hK, z, hz, hcz ▸ hz.conj c⟩
    exact T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK
      (Q3T8.Asc77.AscE186.mem_dstarComp_of_twin hΩ hK hL)
  refine ⟨hz_le, ?_, htail.twin⟩
  intro L hL J hJ z' hz' hzz
  have hKL := (CFSG.ClassicalInvolution.Q3.Q3T7M.l6_3 G Ω hΩ K hK L hL).1
  have hJperp : J ∈ KPerp Ω K := hKL ▸ Set.mem_insert_of_mem _ hJ
  have hnot : J ∉ twinSet Ω K := by
    rintro ⟨-, z₀, hz₀K, hz₀J⟩
    exact hzz ((hz₀J.eq hz').symm.trans (hz.eq hz₀K).symm)
  have hJΩ : J ∈ Ω := hJ.1
  have hJd : J ∈ dstarComp Ω K := by
    rcases Set.mem_insert_iff.mp hJperp with h | h
    · exact absurd (by rw [h]; exact mem_twinSet_self hK hz) hnot
    · exact Relation.ReflTransGen.single ⟨hJΩ, Or.inl (Q3T8.Asc77.T3.omegaNbr_subset_omegaStarNbr
        hΩ K h)⟩
  obtain ⟨y, hy⟩ := htrans J hJΩ
  have hyH : y ∈ sigmaStarNorm Ω K :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (hy ▸ hJd)
  have hzy : IsUniqueInvolution J (y * z * y⁻¹) := hy ▸ hz.conj y
  exact ⟨T7A.centralizer_conj_le hyH (hz'.eq hzy) hz_le, htail.nonTwin L hL J hJ z' hz' hzz⟩

theorem stdCentTail_of_frames
    (hΩ
    : Q3T7M.HM Ω)
    {K K' J W : Subgroup G} {z u t : G} (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hfr : ∀ {L L' J₁ W₁ : Subgroup G} {u₁ t₁ : G}, L ∈ twinSet Ω K →
      Q3T8.Asc77.Hyp21 Ω L L' z u₁ J₁ t₁ W₁ →
        Subgroup.centralizer ({t₁ * z} : Set G) ≤ sigmaStarNorm Ω L ∧
          Subgroup.centralizer ({u₁} : Set G) ≤ sigmaStarNorm Ω L) :
    StdCentTail Ω K (sigmaStarNorm Ω K) z := by
  have hK : K ∈ Ω := h.std.stand.mem
  have hK'Ω : K' ∈ Ω := h.std.hK'.1
  have hzK' := isUniqueInvolution_of_mem_twinSet h.std.hz h.std.hK'
  have hKK : K ∈ twinSet Ω K := mem_twinSet_self hK h.std.hz
  have hstar : ∀ {L : Subgroup G}, L ∈ twinSet Ω K → sigmaStarNorm Ω L = sigmaStarNorm Ω K :=
    fun {L} hL => sigmaStarNorm_congr (T7A.dstarComp_eq_of_mem hK
      (Q3T8.Asc77.AscE186.mem_dstarComp_of_twin hΩ hK hL))
  refine ⟨?_, ?_⟩
  · intro L hL J'' hJ'' z'' hz'' hzz
    have hKL := (CFSG.ClassicalInvolution.Q3.Q3T7M.l6_3 G Ω hΩ K hK L hL).1
    have hJperp : J'' ∈ KPerp Ω K := hKL ▸ Set.mem_insert_of_mem _ hJ''
    have hnot : J'' ∉ twinSet Ω K := by
      rintro ⟨-, z₀, hz₀K, hz₀J⟩
      exact hzz ((hz₀J.eq hz'').symm.trans (h.std.hz.eq hz₀K).symm)
    have hJmem : J'' ∈ omegaOfSet Ω (twinSet Ω K) :=
      Q3T8.Asc77.T7A.mem_omegaOfSet_of_mem_kPerp hΩ hK hJperp hnot
    obtain ⟨g, hgQ, W₁, hfr', hW₁, hzW₁, htW₁⟩ :=
      Q3T8.Asc77.exists_twinFrameData_at hΩ hK h.std.hz h.std.hK' h.std.hne h.hu h.hu2 h.hu1 h.huz
        hJmem hz''
    have h' : Q3T8.Asc77.Hyp21 Ω K K' z u (conjSub g J'') (g * z'' * g⁻¹) W₁ :=
      Q3T8.Asc77.Hyp21.of_twinFrameData h.std hfr' hW₁ hzW₁ htW₁
    have hcl := (hfr hKK h').1
    have hgH : g ∈ sigmaStarNorm Ω K :=
      Q3T8.Asc77.T7A.mem_sigmaStarNorm_of_mem_sup hΩ hK hK'Ω h.std.hne h.std.hz hzK' hgQ
    have hgz : g * z * g⁻¹ = z := by
      have := T7A.z_comm_of_mem_sup h.std.hz hzK' hgQ
      calc g * z * g⁻¹ = (g * z) * g⁻¹ := rfl
        _ = (z * g) * g⁻¹ := by rw [← this]
        _ = z := by group
    have hcomm : z * (g * z'' * g⁻¹) = (g * z'' * g⁻¹) * z := hfr'.comm_zt hΩ
    have e1 : (g * z'' * g⁻¹) * z = g * (z * z'') * g⁻¹ := by
      calc (g * z'' * g⁻¹) * z = z * (g * z'' * g⁻¹) := hcomm.symm
        _ = (g * z * g⁻¹) * (g * z'' * g⁻¹) := by rw [hgz]
        _ = g * (z * z'') * g⁻¹ := by group
    intro c hc
    refine T7A.mem_of_conj_mem hgH ?_
    have hc' := T7A.mem_centralizer_conj (g := g) hc
    rw [← e1] at hc'
    exact hcl hc'
  · intro L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy hx4 hy4
    have hLΩ : L ∈ Ω := hL.1
    have hzL := isUniqueInvolution_of_mem_twinSet h.std.hz hL
    have htwL : twinSet Ω L = twinSet Ω K := twinSet_eq_of_mem_twinSet h.std.hz hL
    have hL'L : L' ∈ twinSet Ω L := by rw [htwL]; exact hL'
    have hJL : J ∈ omegaOfSet Ω (twinSet Ω L) := by rw [htwL]; exact h.hJ
    obtain ⟨g, hgQ, W₂, hJg, htg, hW₂, hzW₂, htW₂, hfr'⟩ :=
      Q3T8.Asc77.exists_twinFrameData_of_sylows hΩ hLΩ hzL hL'L hne hJL h.ht hR₁ hR₂ hc
    have hfr'' := hfr' x hx y hy hx4 hy4
    have h' : Q3T8.Asc77.Hyp21 Ω L L' z (x * y) (conjSub g J) (g * t * g⁻¹) W₂ :=
      Q3T8.Asc77.Hyp21.of_twinFrameData (Q3T8.Asc77.Std7.of_twin h.std hL hL' hne) hfr'' hW₂ hzW₂
          htW₂
    have := (hfr hL h').2
    rwa [hstar hL] at this
end Finite
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

@[expose] def C21_17_cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → rLayer Ω (t * z) ≤ sigmaGen Ω K →
        dComp Ω K = dstarComp Ω K →
          Subgroup.centralizer ({t * z} : Set G) ≤ sigmaStarNorm Ω K ∧
            Subgroup.centralizer ({u} : Set G) ≤ sigmaStarNorm Ω K

@[expose] def C21_E_cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K →
        (∀ M ∈ dComp Ω K, M ≤ Subgroup.centralizer ({t * z} : Set G)) → MuIsoWylD4 Ω W →
          (∀ M : Subgroup G,
            M ∈ dstarComp Ω K ↔ M ∈ Ω ∧ M ≤ Subgroup.centralizer ({t * z} : Set G)) ∧
            Subgroup.centralizer ({u} : Set G) ≤ sigmaStarNorm Ω K
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson.Ctx
variable (c : Q3CL.Thompson.Ctx Ω W)
include c

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.conj_involution_of_comm
    (σ ρ : Rep Ω W) (hcomm : σ.img *
    ρ.img = ρ.img * σ.img) {v : G}
    (hv : v ∈ ρ.K ⊓ W) (hv2 : v * v = 1) : σ.r * v * σ.r⁻¹ = v := by
  by_cases hK : σ.K = ρ.K
  · have hvσ : v ∈ σ.K ⊓ W := by rw [hK]; exact hv
    rw [c.conj_inv σ hvσ]
    exact inv_eq_of_mul_eq_one_left hv2
  · have hnbr := c.omega_of_comm σ ρ hK hcomm
    have := c.centralizes σ ρ hnbr hv
    rw [this]
    group

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.conj_mul_involutions_eq (hclC :
    Q3CL.ClassicalClause Ω)
    (hnc : ¬ DbarConnected Ω W) (ρ ρ' : Rep Ω W)
    (hnbr : ρ'.K ∈ omegaNbr Ω ρ.K) {z t : G} (hz : IsUniqueInvolution ρ.K z)
    (ht : IsUniqueInvolution ρ'.K t) (σ : Rep Ω W) :
    σ.r * (t * z) * σ.r⁻¹ = t * z := by
  obtain ⟨hcl, hAON⟩ := c.clique_dichotomy hclC hnc (T7D.imgQ_mem ρ)
  have hzW : z ∈ W := c.mem_W_of_isUniqueInvolution ρ hz
  have htW : t ∈ W := c.mem_W_of_isUniqueInvolution ρ' ht
  have hρ' : T7D.imgQ ρ' ∈ Star3T.cent (muDelta Ω W) (T7D.imgQ ρ) :=
    ⟨T7D.imgQ_mem ρ', Subtype.ext (c.comm_of_omega ρ ρ' hnbr).symm⟩
  by_cases hx : T7D.imgQ σ ∈ Star3T.cent (muDelta Ω W) (T7D.imgQ ρ)
  · have hxρ : σ.img * ρ.img = ρ.img * σ.img := congrArg Subtype.val hx.2
    have hxρ' : σ.img * ρ'.img = ρ'.img * σ.img :=
      congrArg Subtype.val (hcl _ hx _ hρ')
    have e1 := c.conj_involution_of_comm σ ρ hxρ ⟨hz.mem, hzW⟩ hz.sq
    have e2 := c.conj_involution_of_comm σ ρ' hxρ' ⟨ht.mem, htW⟩ ht.sq
    calc σ.r * (t * z) * σ.r⁻¹ = (σ.r * t * σ.r⁻¹) * (σ.r * z * σ.r⁻¹) := by group
      _ = t * z := by rw [e1, e2]
  · have hxρ : σ.img * ρ.img ≠ ρ.img * σ.img := fun h =>
      hx ⟨T7D.imgQ_mem σ, Subtype.ext h⟩
    have hxρ' : σ.img * ρ'.img ≠ ρ'.img * σ.img := fun h =>
      hx (hAON _ (T7D.imgQ_mem σ) _ hρ' (Subtype.ext h))
    obtain ⟨zσ, hzσ⟩ := c.hΩ.exists_uniqueInvolution σ.hK
    have hzσW : zσ ∈ W := c.mem_W_of_isUniqueInvolution σ hzσ
    have e1 := c.conj_involution_of_noncomm σ ρ hxρ hzσ hz
    have e2 := c.conj_involution_of_noncomm σ ρ' hxρ' hzσ ht
    have hc : t * zσ = zσ * t := c.comm_W t htW zσ hzσW
    calc σ.r * (t * z) * σ.r⁻¹ = (σ.r * t * σ.r⁻¹) * (σ.r * z * σ.r⁻¹) := by group
      _ = (zσ * t) * (zσ * z) := by rw [e1, e2]
      _ = zσ * (t * zσ) * z := by group
      _ = zσ * (zσ * t) * z := by rw [hc]
      _ = (zσ * zσ) * (t * z) := by group
      _ = t * z := by rw [hzσ.sq, one_mul]

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.le_centralizer_mul_involutions (hclC :
    Q3CL.ClassicalClause Ω)
    (hnc : ¬ DbarConnected Ω W) (ρ ρ' : Rep Ω W)
    (hnbr : ρ'.K ∈ omegaNbr Ω ρ.K) {z t : G} (hz : IsUniqueInvolution ρ.K z)
    (ht : IsUniqueInvolution ρ'.K t) :
    ∀ R ∈ DSet Ω W, R ≤ Subgroup.centralizer ({t * z} : Set G) := by
  intro R hR x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  by_cases hxW : x ∈ W
  · exact c.comm_W x hxW (t * z)
      (W.mul_mem (c.mem_W_of_isUniqueInvolution ρ' ht) (c.mem_W_of_isUniqueInvolution ρ hz))
  · obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
    have h := c.conj_mul_involutions_eq hclC hnc ρ ρ' hnbr hz ht
      (⟨K, R, x, hK, hR, hRK, hx, hxW⟩ : Rep Ω W)
    calc x * (t * z) = (x * (t * z) * x⁻¹) * x := by group
      _ = (t * z) * x := by rw [show x * (t * z) * x⁻¹ = t * z from h]
end Ctx
end Thompson
section Frame
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J W : Subgroup G} {z u t : G}

theorem Hyp21.not_dbarConnected
    (h
    : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) : ¬ DbarConnected Ω W :=
  Q3T8.Asc77.thompsonGraphAll G Ω ⟨h.std.stand.hyp, h.std.stand.cls, h.std.stand.aEmpty⟩
    h.std.stand.mem hne h.hW

theorem Hyp21.exists_reps
    (h
    : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) :
    ∃ ρ ρ' : Thompson.Rep Ω W, ρ.K = K ∧ ρ'.K = J ∧ ρ'.K ∈ omegaNbr Ω ρ.K := by
  have hst := h.std.stand
  have c : Q3CL.Thompson.Ctx Ω W := Q3T8.Asc77.T7D.ctx_of_stand hst h.hW
  obtain ⟨ρ, hρ⟩ := c.exists_rep_of_involution_mem hst.cls hst.mem h.std.hz h.hzW
  obtain ⟨ρ', hρ'⟩ := c.exists_rep_of_involution_mem hst.cls h.hJ.1 h.ht h.htW
  refine ⟨ρ, ρ', hρ, hρ', ?_⟩
  rw [hρ, hρ']
  exact h.hJ.2 K (mem_twinSet_self hst.mem h.std.hz)

theorem Hyp21.dSet_le_centralizer_tz
    (h
    : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hnc : ¬ DbarConnected Ω W) :
    ∀ R ∈ DSet Ω W, R ≤ Subgroup.centralizer ({t * z} : Set G) := by
  have c : Q3CL.Thompson.Ctx Ω W := Q3T8.Asc77.T7D.ctx_of_stand h.std.stand h.hW
  obtain ⟨ρ, ρ', hρ, hρ', hnbr⟩ := h.exists_reps
  exact c.le_centralizer_mul_involutions h.std.stand.cls hnc ρ ρ' hnbr (hρ ▸ h.std.hz) (hρ' ▸ h.ht)

theorem Hyp21.mGrp_le_rLayer_tz
    (h
    : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) : MGrp Ω W ≤ rLayer Ω (t * z) := by
  have hle := h.dSet_le_centralizer_tz (h.not_dbarConnected hne)
  exact iSup₂_le fun R hR =>
    le_iSup₂_of_le R hR.1 (le_iSup_of_le (hle R hR) le_rfl)
end Frame
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

@[expose] def C21_YSigma : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → ExactLayer.exactLayer Ω u ≤ sigmaGen Ω K →
        Subgroup.centralizer ({t * z} : Set G) ≤ sigmaStarNorm Ω K →
          Subgroup.centralizer ({u} : Set G) ≤ sigmaStarNorm Ω K

@[expose] def C21_17_tz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → rLayer Ω (t * z) ≤ sigmaGen Ω K →
        dComp Ω K = dstarComp Ω K →
          Subgroup.centralizer ({t * z} : Set G) ≤ sigmaStarNorm Ω K

@[expose] def C21_E_star : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K →
        (∀ M ∈ dComp Ω K, M ≤ Subgroup.centralizer ({t * z} : Set G)) → MuIsoWylD4 Ω W →
          ∀ M : Subgroup G,
            M ∈ dstarComp Ω K ↔ M ∈ Ω ∧ M ≤ Subgroup.centralizer ({t * z} : Set G)
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.Thompson
section Frame
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J W : Subgroup G} {z u t : G}

theorem Hyp21.exists_mem_conj_of_dstarComp
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) {H : Subgroup G} (hM : MGrp Ω W ≤ H)
    (hN : Subgroup.normalizer (K : Set G) ≤ H) :
    ∀ L ∈ dstarComp Ω K, ∃ x ∈ H, conjSub x K = L := by
  have hst := h.std.stand
  have hΩ : Q3T8.Asc77.HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have c : Q3CL.Thompson.Ctx Ω W := Q3T8.Asc77.T7D.ctx_of_stand hst h.hW
  have hnc : ¬ DbarConnected Ω W := h.not_dbarConnected hne
  obtain ⟨ρ, ρ', hρ, -, -⟩ := h.exists_reps
  have hA : ∀ J₁ ∈ omegaStarNbr Ω K, ∃ x ∈ H, conjSub x K = J₁ := by
    intro J₁ hJ₁
    obtain ⟨g, ρ₁, σ₁, hρ₁, hσ₁⟩ := c.exists_conj_reps_of_mem_omegaStarNbr hK hJ₁
    obtain ⟨m₁, hm₁, hm₁K⟩ := c.exists_conj_of_rep h.std.stand.cls hnc ρ ρ₁
    obtain ⟨m₂, hm₂, hm₂K⟩ := c.exists_conj_of_rep h.std.stand.cls hnc ρ σ₁
    rw [hρ, hρ₁] at hm₁K
    rw [hρ, hσ₁] at hm₂K
    have hg' : conjSub (m₁⁻¹ * g) K = K := by
      rw [conjSub_mul, ← hm₁K, conjSub_inv_conjSub]
    have hg'N : m₁⁻¹ * g ∈ Subgroup.normalizer (K : Set G) :=
      mem_normalizer_iff_conjSub_eq.mpr hg'
    refine ⟨(m₁⁻¹ * g)⁻¹ * (m₁⁻¹ * m₂), H.mul_mem (H.inv_mem (hN hg'N))
      (H.mul_mem (H.inv_mem (hM hm₁)) (hM hm₂)), ?_⟩
    have e : (m₁⁻¹ * g)⁻¹ * (m₁⁻¹ * m₂) = g⁻¹ * m₂ := by group
    rw [e, conjSub_mul, hm₂K, conjSub_inv_conjSub]
  intro L hL
  have hL' : Relation.ReflTransGen (dstarAdj Ω) K L := hL
  clear hL
  induction hL' with
  | refl => exact ⟨1, H.one_mem, conjSub_one K⟩
  | @tail b c' _ hbc ih =>
    obtain ⟨x, hxH, hx⟩ := ih
    have hbΩ : b ∈ Ω := hx ▸ hΩ.conjInvariant x K hK
    have hc'Ω : c' ∈ Ω := hbc.1
    have hnbr : c' ∈ omegaStarNbr Ω b := by
      rcases hbc.2 with h1 | h1
      · exact h1
      · exact Q3T8.Asc77.T3.omegaStarNbr_symm (Q3T8.Asc77.l6_2) hΩ hc'Ω hbΩ h1
    have h2 := omegaStarNbr_conj hΩ.conjInvariant hnbr x⁻¹
    rw [← hx, conjSub_inv_conjSub] at h2
    obtain ⟨y, hyH, hy⟩ := hA _ h2
    refine ⟨x * y, H.mul_mem hxH hyH, ?_⟩
    rw [conjSub_mul, hy, conjSub_conjSub_inv]

theorem Hyp21.not_rLayer_le_sigmaGen
    (h
    : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) : ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K := by
  intro hD
  have hst := h.std.stand
  have hΩ : Q3T8.Asc77.HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have c : Q3CL.Thompson.Ctx Ω W := Q3T8.Asc77.T7D.ctx_of_stand hst h.hW
  have hnc : ¬ DbarConnected Ω W := h.not_dbarConnected hne
  obtain ⟨ρ, ρ', hρ, -, -⟩ := h.exists_reps
  have hMN : MGrp Ω W ≤ sigmaNorm Ω K :=
    (h.mGrp_le_rLayer_tz hne).trans (hD.trans (T7A.sigmaGen_le_sigmaNorm hΩ.conjInvariant hK))
  obtain ⟨K₁, hK₁d, J₁, hJ₁, hJ₁n⟩ := Q3T8.Asc77.Thompson.exists_boundary_of_dComp_ne hΩ hK hne
  have hK₁Ω : K₁ ∈ Ω := mem_of_mem_dComp' hK hK₁d
  obtain ⟨g, ρ₁, σ₁, hρ₁, hσ₁⟩ := c.exists_conj_reps_of_mem_omegaStarNbr hK₁Ω hJ₁
  obtain ⟨m₁, hm₁, hm₁K⟩ := c.exists_conj_of_rep h.std.stand.cls hnc ρ ρ₁
  obtain ⟨m₂, hm₂, hm₂K⟩ := c.exists_conj_of_rep h.std.stand.cls hnc ρ σ₁
  rw [hρ, hρ₁] at hm₁K
  rw [hρ, hσ₁] at hm₂K
  have h1 : conjSub g K₁ ∈ dComp Ω K := by
    rw [← hm₁K]
    exact (T8.mem_sigmaNorm_iff hΩ.conjInvariant hK).mp (hMN hm₁)
  have h2 : conjSub g J₁ ∈ dComp Ω K := by
    rw [← hm₂K]
    exact (T8.mem_sigmaNorm_iff hΩ.conjInvariant hK).mp (hMN hm₂)
  have hgN : g ∈ sigmaNorm Ω K :=
    T8.mem_sigmaNorm_of_mem_dComp hΩ.conjInvariant hK hK₁d h1
  exact hJ₁n ((hgN J₁).mpr h2)

theorem dComp_eq_dstarComp_of_rLayer_le
    (h
    : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hD : rLayer Ω (t * z) ≤ sigmaGen Ω K) : dComp Ω K = dstarComp Ω K := by
  by_contra hne
  exact h.not_rLayer_le_sigmaGen hne hD
end Frame
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
