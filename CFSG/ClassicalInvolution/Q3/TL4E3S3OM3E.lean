module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM3A
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM3C
public import CFSG.ClassicalInvolution.Q3.TL4OrthQ8

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O.OM3

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.TL4.OrthQ8 QuadraticMap
open scoped MatrixGroups

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {S : Type} [Group S]

theorem false_of_odd_finrank [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    {g : V ≃ₗ[K] V} (hg : ∀ v, g (g v) = -v) (hodd : Odd (Module.finrank K V)) : False := by
  have h1 : (g : V →ₗ[K] V) ∘ₗ (g : V →ₗ[K] V) = (-1 : K) • LinearMap.id := by
    ext v
    simp [hg]
  have h2 := congrArg LinearMap.det h1
  rw [LinearMap.det_comp, LinearMap.det_smul, LinearMap.det_id, hodd.neg_one_pow, mul_one] at h2
  exact sq_ne_neg_one hK _ h2

private theorem exists_mem_eq_one [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    {P : Submodule K V} (hP : PolarNondegOn Q P) (h2 : 2 ≤ Module.finrank K P) :
    ∃ v ∈ P, Q v = 1 := by
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  have : Invertible (2 : K) := invertibleOfNonzero (OrthQ8.two_ne_zero' hK)
  obtain ⟨v, hv, hQv⟩ := ModelFacts.exists_mem_eq_unit hodd
    (QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_restrict hP)) h2 1
  exact ⟨v, hv, by rwa [Units.val_one] at hQv⟩

private theorem exists_regular_orth [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) {P : Submodule K V}
    (hP : PolarNondegOn Q P) {v : V} (hvP : v ∈ P) (hv : Q v = 1) :
    ∃ P' : Submodule K V, (∀ x, x ∈ P' ↔ x ∈ P ∧ polar Q v x = 0) ∧ PolarNondegOn Q P' ∧
      Module.finrank K P ≤ Module.finrank K P' + 1 := by
  have hvv : polar Q v v = 2 := by rw [polar_self_eq_two_mul, hv]; ring
  let φ : P →ₗ[K] K := (polarBilin Q v).domRestrict P
  let P' : Submodule K V := (LinearMap.ker φ).map P.subtype
  have hmem : ∀ x, x ∈ P' ↔ x ∈ P ∧ polar Q v x = 0 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hx'⟩
      exact ⟨⟨x, hx⟩, hx', rfl⟩
  refine ⟨P', hmem, ?_, ?_⟩
  · intro x hx hxy
    have hxP := ((hmem x).mp hx).1
    have hxv : polar Q v x = 0 := ((hmem x).mp hx).2
    apply hP x hxP
    intro y hy
    have hy' : y - (polar Q y v / 2) • v ∈ P' := by
      rw [hmem]
      refine ⟨P.sub_mem hy (P.smul_mem _ hvP), ?_⟩
      rw [polar_sub_right, polar_smul_right_eq, hvv, polar_comm Q v y]
      field_simp
      ring
    have h1 := hxy _ hy'
    have h3 : y = (y - (polar Q y v / 2) • v) + (polar Q y v / 2) • v := by abel
    rw [h3, polar_add_right, h1, polar_smul_right_eq, polar_comm Q x v, hxv]
    ring
  · have hr := LinearMap.finrank_range_add_finrank_ker φ
    have h1 : Module.finrank K (LinearMap.range φ) ≤ 1 := by
      calc Module.finrank K (LinearMap.range φ) ≤ Module.finrank K K := Submodule.finrank_le _
        _ = 1 := Module.finrank_self K
    have h4 : Module.finrank K P' = Module.finrank K (LinearMap.ker φ) :=
      LinearEquiv.finrank_eq
        ((LinearMap.ker φ).equivMapOfInjective P.subtype P.injective_subtype).symm
    omega

private theorem exists_orthoQuad_of_isometry [Finite K] [FiniteDimensional K V]
    (hK : Nat.card K = 3) (hQ : (polarBilin Q).Nondegenerate) {F : Frame Q}
    (hn : 8 ≤ Module.finrank K V) {g : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg : ∀ v, g (g v) = -v) (hgF : ∀ v ∈ F.perp, g v ∈ F.perp) :
    ∃ w₀ w₂ : V, w₀ ∈ F.perp ∧ w₂ ∈ F.perp ∧ OrthoQuad Q w₀ (g w₀) w₂ (g w₂) := by
  have h2 : (2 : K) ≠ 0 := OrthQ8.two_ne_zero' hK
  have hPn : PolarNondegOn Q F.perp := ModelFacts.polarNondegOn_perp hQ F
  have hdim := ModelFacts.finrank_perp_add_four F
  have hgQ : ∀ v, Q (g v) = Q v := fun v => map_of_mem hgO v
  have hp : ∀ v, polar Q v (g v) = 0 := fun v => polar_eq_zero_of_mul_self h2 hgO (hg v)
  obtain ⟨w₀, hw₀P, hQ₀⟩ := exists_mem_eq_one hK hPn (by omega)
  obtain ⟨P₁, hP₁, hP₁n, hP₁d⟩ := exists_regular_orth h2 hPn hw₀P hQ₀
  have hQ₁ : Q (g w₀) = 1 := by rw [hgQ, hQ₀]
  obtain ⟨P₂, hP₂, hP₂n, hP₂d⟩ :=
    exists_regular_orth h2 hP₁n ((hP₁ _).mpr ⟨hgF w₀ hw₀P, hp w₀⟩) hQ₁
  obtain ⟨w₂, hw₂P₂, hQ₂⟩ := exists_mem_eq_one hK hP₂n (by omega)
  obtain ⟨hw₂P₁, hw₂₁⟩ := (hP₂ w₂).mp hw₂P₂
  obtain ⟨hw₂P, hw₂₀⟩ := (hP₁ w₂).mp hw₂P₁
  refine ⟨w₀, w₂, hw₀P, hw₂P, hQ₀, hQ₁, hQ₂, by rw [hgQ, hQ₂], hp w₀, hw₂₀, ?_, hw₂₁, ?_, hp w₂⟩
  · rw [← polar_map_of_mem hgO w₀ (g w₂), hg w₂, polar_neg_right, hw₂₁, neg_zero]
  · rw [polar_map_of_mem hgO, hw₂₀]

private theorem commute_swap_La_of_orthoQuad {w₀ w₂ : V} (h3 : (3 : K) = 0) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg : ∀ v, g (g v) = -v)
    (ho : OrthoQuad Q w₀ (g w₀) w₂ (g w₂)) (b : SL(2, K)) :
    g * (ho.frame h3).swap.La b = (ho.frame h3).swap.La b * g := by
  have hspan : ∀ v ∈ (ho.frame h3).span, g v = (ho.frame h3).La sl2I v := by
    intro v hv
    have hle : (ho.frame h3).span ≤ Submodule.span K {w₀, g w₀, w₂, g w₂} :=
      ho.span_le h3 (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
        (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
    refine LinearMap.eqOn_span (f := (g : V →ₗ[K] V))
      (g := ((ho.frame h3).La sl2I : V →ₗ[K] V)) (s := {w₀, g w₀, w₂, g w₂}) ?_ (hle hv)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (ho.La_sl2I_w₀ h3).symm
    · exact (hg w₀).trans (ho.La_sl2I_w₁ h3).symm
    · exact (ho.La_sl2I_w₂ h3).symm
    · exact (hg w₂).trans (ho.La_sl2I_w₃ h3).symm
  refine commute_swap_La_of_eqOn_La (ho.frame h3) sl2I (fun v hv => ?_) hspan b
  rw [Frame.mem_perp_iff_forall_incl] at hv ⊢
  intro Y
  have h1 := polar_map_of_mem hgO v (-(g ((ho.frame h3).incl Y)))
  rw [map_neg, hg, neg_neg, polar_neg_right] at h1
  rw [h1, hspan ((ho.frame h3).incl Y) ⟨Y, rfl⟩, Frame.La_apply_incl, hv, neg_zero]

theorem exists_frame_commute_swap [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) {F : Frame Q} (hn : 8 ≤ Module.finrank K V)
    {g : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg : ∀ v, g (g v) = -v) (hgF : ∀ v ∈ F.perp, g v ∈ F.perp) :
    ∃ G : Frame Q, G.span ≤ F.perp ∧ ∀ b : SL(2, K), g * G.swap.La b = G.swap.La b * g := by
  obtain ⟨w₀, w₂, h₀, h₂, ho⟩ := exists_orthoQuad_of_isometry hK hQ hn hgO hg hgF
  have h3 := three_eq_zero hK
  exact ⟨ho.frame h3, ho.span_le h3 h₀ (hgF _ h₀) h₂ (hgF _ h₂),
    commute_swap_La_of_orthoQuad h3 hgO hg ho⟩

theorem La_comm_of_span_le_perp {F G : Frame Q} (h : G.span ≤ F.perp) (a b : SL(2, K)) :
    F.La a * G.La b = G.La b * F.La a :=
  Frame.La_comm_of_orth (fun X Y => by
    have hY : G.incl Y ∈ F.perp := h ⟨Y, rfl⟩
    rw [polar_comm]
    exact (Frame.mem_perp_iff_forall_incl F).mp hY X) a b

theorem frameMember_ne_of_span_le_perp [Finite K] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) {θ : ↥(orthDerived Q) →* S}
    (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q)) {F G : Frame Q}
    (h : G.span ≤ F.perp) : frameMember θ G ≠ frameMember θ F := by
  intro heq
  have hi := sl2I_mem_commutator (K := K) hK
  have hmem : θ ⟨G.La sl2I, frameQ8_le G (La_mem_frameQ8 G hi)⟩ ∈ frameMember θ F :=
    heq ▸ La_mem_frameMember θ G hi
  obtain ⟨a, ha, hθ⟩ := (mem_frameMember_iff θ F).mp hmem
  have hu : G.incl 1 ≠ 0 := fun h0 => by
    have := congrArg G.coords h0
    rw [Frame.coords_incl, map_zero] at this
    exact one_ne_zero this
  have : Nontrivial V := ⟨⟨G.incl 1, 0, hu⟩⟩
  obtain ⟨s, -, hsv⟩ := exists_smul_of_map_eq hQ hker hθ
  have hperp : G.incl 1 ∈ F.perp := h ⟨1, rfl⟩
  have e1 : F.La a (G.incl 1) = G.incl 1 :=
    F.La_apply_of_coords_eq_zero a ((Frame.mem_perp_iff F).mp hperp)
  have e2 := hsv (G.incl 1)
  simp only at e2
  rw [Frame.La_apply_incl, Matrix.mul_one, e1] at e2
  have e3 : G.incl (((sl2I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) - s • 1) = 0 := by
    rw [map_sub, map_smul, e2, sub_self]
  have e4 := G.incl_injective (e3.trans (map_zero G.incl).symm)
  have e5 := congrFun (congrFun e4 0) 1
  simp [coe_sl2I] at e5

theorem false_of_fixed_member [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hn : 7 ≤ Module.finrank K V)
    {θ : ↥(orthDerived Q) →* S} {F G : Frame Q} {g : V ≃ₗ[K] V} {x : MulAut S}
    (hx : InducedBy θ g x) (hG : ∀ b ∈ commutator SL(2, K), g * G.La b = G.La b * g)
    (hne : frameMember θ G ≠ frameMember θ F)
    (hcomm : ∀ a ∈ commutator SL(2, K), ∀ b ∈ commutator SL(2, K),
      F.La a * G.La b = G.La b * F.La a)
    (hnb : ∀ C ∈ CoreAssembly.conjClass (frameMember θ F), (∀ c ∈ C, x c = c) →
      C ≠ frameMember θ F → ¬ C ≤ Subgroup.normalizer ((frameMember θ F : Subgroup S) : Set S)) :
    False := by
  refine hnb (frameMember θ G) (frameMember_mem_conjClass_frameMember hK hQ hn θ F G) ?_ hne ?_
  · intro c hc
    obtain ⟨b, hb, rfl⟩ := (mem_frameMember_iff θ G).mp hc
    rw [hx.act]
    congr 1
    refine Subtype.ext ?_
    show g * G.La b * g⁻¹ = G.La b
    rw [mul_inv_eq_iff_eq_mul, hG b hb]
  · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨b, hb, rfl⟩ := (mem_frameMember_iff θ G).mp hc
    obtain ⟨a', ha', rfl⟩ := (mem_frameMember_iff θ F).mp ha
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext (hcomm a' ha' b hb))

theorem false_of_fixed_frame_perp [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hn : 7 ≤ Module.finrank K V)
    {θ : ↥(orthDerived Q) →* S} (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q))
    {F G : Frame Q} {g : V ≃ₗ[K] V} {x : MulAut S} (hx : InducedBy θ g x)
    (hGF : G.span ≤ F.perp) (hG : ∀ b ∈ commutator SL(2, K), g * G.La b = G.La b * g)
    (hnb : ∀ C ∈ CoreAssembly.conjClass (frameMember θ F), (∀ c ∈ C, x c = c) →
      C ≠ frameMember θ F → ¬ C ≤ Subgroup.normalizer ((frameMember θ F : Subgroup S) : Set S)) :
    False :=
  false_of_fixed_member hK hQ hn hx hG (frameMember_ne_of_span_le_perp hK hQ hker hGF)
    (fun a _ b _ => La_comm_of_span_le_perp hGF a b) hnb

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O.OM3
