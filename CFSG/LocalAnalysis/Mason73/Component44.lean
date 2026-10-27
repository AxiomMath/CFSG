module

public import CFSG.LocalAnalysis.Mason73.Quotient44
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallCover
public import CFSG.Walter.FinalNative

public section

namespace CFSG.LocalAnalysis.Mason73

open Subgroup
open scoped MatrixGroups commutatorElement

section General

variable {A B : Type*} [Group A] [Group B]

theorem commutator_eq_top_of_mulEquiv (e : A ≃* B) (h : commutator A = ⊤) :
    commutator B = ⊤ := by
  have hs : Function.Surjective e.toMonoidHom := e.surjective
  rw [eq_top_iff, ← map_top_of_surjective _ hs, ← h, _root_.commutator_def,
    _root_.commutator_def, map_commutator, map_top_of_surjective _ hs]

theorem center_eq_bot_of_commutator_eq_top [IsSimpleGroup A] (h : commutator A = ⊤) :
    center A = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center A) with hc | hc
  · exact hc
  · exfalso
    have hb : commutator A = ⊥ := (commutator_eq_bot_iff_center_eq_top A).2 hc
    rw [h] at hb
    obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial A)
    exact hab ((mem_bot.1 (hb ▸ mem_top a)).trans (mem_bot.1 (hb ▸ mem_top b)).symm)

theorem commutator_eq_top_of_inf_eq_bot_of_sup_eq_top (hperf : commutator A = ⊤)
    {L₁ L₂ : Subgroup A} [L₂.Normal] (hinf : L₁ ⊓ L₂ = ⊥) (hsup : L₁ ⊔ L₂ = ⊤) :
    commutator L₁ = ⊤ := by
  let ρ : L₁ →* A ⧸ L₂ := (QuotientGroup.mk' L₂).comp L₁.subtype
  have hρi : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have : (x : A) ∈ L₁ ⊓ L₂ := ⟨x.2, hx⟩
    rw [hinf, mem_bot] at this
    exact (mem_bot).2 (Subtype.ext this)
  have hρs : Function.Surjective ρ := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective L₂ y
    obtain ⟨b, hb, c, hc, rfl⟩ := mem_sup_of_normal_right.1 (hsup ▸ mem_top a :
      a ∈ L₁ ⊔ L₂)
    refine ⟨⟨b, hb⟩, ?_⟩
    change (QuotientGroup.mk' L₂) b = (QuotientGroup.mk' L₂) (b * c)
    rw [map_mul, show QuotientGroup.mk' L₂ c = 1 from (QuotientGroup.eq_one_iff c).2 hc, mul_one]
  exact commutator_eq_top_of_mulEquiv (MulEquiv.ofBijective ρ ⟨hρi, hρs⟩).symm
    (commutator_quotient_eq_top hperf)

theorem commutator_sup_eq_of_le_center {H Z : Subgroup A} [H.Normal] [Z.Normal]
    (hZ : Z ≤ center A) : ⁅H ⊔ Z, H ⊔ Z⁆ = ⁅H, H⁆ := by
  have hHZ : ⁅H, Z⁆ = ⊥ := le_bot_iff.1 (commutator_center_right (H := H) ▸
    commutator_mono le_rfl hZ)
  have hZH : ⁅Z, H⁆ = ⊥ := by rw [commutator_comm, hHZ]
  have hZZ : ⁅Z, Z⁆ = ⊥ := le_bot_iff.1 (commutator_center_right (H := Z) ▸
    commutator_mono le_rfl hZ)
  rw [commutator_sup_right, commutator_sup_left, commutator_sup_left, hHZ, hZH, hZZ, sup_bot_eq,
    bot_sup_eq, sup_bot_eq]

end General

section Component

variable {X : Type} [Group X] [Finite X]

theorem map_commutator_comap {Y : Type*} [Group Y] {π : X →* Y} (hπ : Function.Surjective π)
    {L : Subgroup Y} (hL : ⁅L, L⁆ = L) : (⁅L.comap π, L.comap π⁆).map π = L := by
  rw [map_commutator, map_comap_eq_self_of_surjective hπ, hL]

theorem commutator_comap_sup_ker {Y : Type*} [Group Y] {π : X →* Y}
    (hπ : Function.Surjective π) {L : Subgroup Y} (hL : ⁅L, L⁆ = L) :
    ⁅L.comap π, L.comap π⁆ ⊔ π.ker = L.comap π := by
  rw [← comap_map_eq, map_commutator_comap hπ hL]

variable {N : Subgroup X} [N.Normal] {z : X}

theorem eq_one_of_mem_zpowers_of_not_mem (hzN : N = zpowers z) (hz2 : orderOf z = 2)
    {K : Subgroup X} (hzK : z ∉ K) {x : X} (hxK : x ∈ K) (hxN : x ∈ N) : x = 1 := by
  rw [hzN, mem_zpowers_iff_of_orderOf_eq_two hz2] at hxN
  rcases hxN with h | h
  · exact h
  · exact absurd (h ▸ hxK) hzK

theorem mem_of_commute_of_center_eq_bot {L : Subgroup (X ⧸ N)} {K : Subgroup X}
    (hK : K.map (QuotientGroup.mk' N) = L) (hc : center L = ⊥) {a : X} (ha : a ∈ K)
    (hac : ∀ x ∈ K, a * x = x * a) : a ∈ N := by
  have haL : QuotientGroup.mk' N a ∈ L := hK ▸ mem_map_of_mem _ ha
  have hπa : (⟨QuotientGroup.mk' N a, haL⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := (hK.symm ▸ hy : y ∈ K.map (QuotientGroup.mk' N))
    apply Subtype.ext
    change QuotientGroup.mk' N x * QuotientGroup.mk' N a =
      QuotientGroup.mk' N a * QuotientGroup.mk' N x
    rw [← map_mul, ← map_mul, hac x hx]
  rw [hc, mem_bot] at hπa
  have : QuotientGroup.mk' N a = 1 := congrArg Subtype.val hπa
  rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at this

theorem mem_or_mem_commutator_comap (hperf : commutator X = ⊤) (hNc : N ≤ center X)
    (hzN : N = zpowers z) (hz2 : orderOf z = 2) {L₁ L₂ : Subgroup (X ⧸ N)} [L₁.Normal]
    [L₂.Normal] (hinf : L₁ ⊓ L₂ = ⊥) (hsup : L₁ ⊔ L₂ = ⊤) (hL₁ : ⁅L₁, L₁⁆ = L₁)
    (hL₂ : ⁅L₂, L₂⁆ = L₂) (hc₁ : center L₁ = ⊥) (hc₂ : center L₂ = ⊥) :
    z ∈ ⁅L₁.comap (QuotientGroup.mk' N), L₁.comap (QuotientGroup.mk' N)⁆ ∨
      z ∈ ⁅L₂.comap (QuotientGroup.mk' N), L₂.comap (QuotientGroup.mk' N)⁆ := by
  have hπ : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  haveI : (L₁.comap (QuotientGroup.mk' N)).Normal := Subgroup.Normal.comap inferInstance _
  haveI : (L₂.comap (QuotientGroup.mk' N)).Normal := Subgroup.Normal.comap inferInstance _
  set K₁ := ⁅L₁.comap (QuotientGroup.mk' N), L₁.comap (QuotientGroup.mk' N)⁆ with hK₁def
  set K₂ := ⁅L₂.comap (QuotientGroup.mk' N), L₂.comap (QuotientGroup.mk' N)⁆ with hK₂def
  have hK₁ : K₁.map (QuotientGroup.mk' N) = L₁ := map_commutator_comap hπ hL₁
  have hK₂ : K₂.map (QuotientGroup.mk' N) = L₂ := map_commutator_comap hπ hL₂
  by_contra hcon
  push Not at hcon
  obtain ⟨hz1, hz2'⟩ := hcon
  have hK12 : ∀ x ∈ K₁, x ∈ K₂ → x = 1 := by
    intro x h1 h2
    have : QuotientGroup.mk' N x ∈ L₁ ⊓ L₂ :=
      ⟨hK₁ ▸ mem_map_of_mem _ h1, hK₂ ▸ mem_map_of_mem _ h2⟩
    rw [hinf, mem_bot, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at this
    exact eq_one_of_mem_zpowers_of_not_mem hzN hz2 hz1 h1 this
  have hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a := by
    intro a ha b hb
    have hc : ⁅a, b⁆ ∈ K₁ ⊓ K₂ := commutator_le_inf K₁ K₂ (commutator_mem_commutator ha hb)
    exact commutatorElement_eq_one_iff_mul_comm.1 (hK12 _ hc.1 hc.2)
  have hsupK : K₁ ⊔ K₂ = ⊤ := by
    have h1 : (K₁ ⊔ K₂) ⊔ N = ⊤ := by
      have h := comap_map_eq (QuotientGroup.mk' N) (K₁ ⊔ K₂)
      rw [Subgroup.map_sup, hK₁, hK₂, hsup, comap_top, QuotientGroup.ker_mk'] at h
      exact h.symm
    have h2 : ⁅(K₁ ⊔ K₂) ⊔ N, (K₁ ⊔ K₂) ⊔ N⁆ = ⁅K₁ ⊔ K₂, K₁ ⊔ K₂⁆ :=
      commutator_sup_eq_of_le_center hNc
    rw [h1] at h2
    rw [eq_top_iff, ← hperf, _root_.commutator_def, h2]
    exact commutator_le_self _
  have hzc : z ∈ center X := hNc (hzN ▸ mem_zpowers z)
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_right.1 (hsupK ▸ mem_top z : z ∈ K₁ ⊔ K₂)
  have hzx : ∀ x : X, a * b * x = x * (a * b) := fun x => by
    rw [hab]
    exact (mem_center_iff.1 hzc x).symm
  have ha1 : a = 1 := by
    refine eq_one_of_mem_zpowers_of_not_mem hzN hz2 hz1 ha
      (mem_of_commute_of_center_eq_bot hK₁ hc₁ ha fun x hx => ?_)
    have hbx : b * x = x * b := (hcomm x hx b hb).symm
    have : a * x * b = x * a * b := by
      calc a * x * b = a * (b * x) := by rw [mul_assoc, hbx]
        _ = a * b * x := by rw [mul_assoc]
        _ = x * (a * b) := hzx x
        _ = x * a * b := by rw [mul_assoc]
    exact mul_right_cancel this
  have hb1 : b = 1 := by
    refine eq_one_of_mem_zpowers_of_not_mem hzN hz2 hz2' hb
      (mem_of_commute_of_center_eq_bot hK₂ hc₂ hb fun x hx => ?_)
    have hax : a * x = x * a := hcomm a ha x hx
    have : a * (b * x) = a * (x * b) := by
      calc a * (b * x) = a * b * x := by rw [mul_assoc]
        _ = x * (a * b) := hzx x
        _ = x * a * b := by rw [mul_assoc]
        _ = a * x * b := by rw [hax]
        _ = a * (x * b) := by rw [mul_assoc]
    exact mul_left_cancel this
  rw [ha1, hb1, one_mul] at hab
  rw [← hab, orderOf_one] at hz2
  exact absurd hz2 (by norm_num)

theorem commutator_commutator_comap (hNc : N ≤ center X) {L : Subgroup (X ⧸ N)} [L.Normal]
    (hL : ⁅L, L⁆ = L) :
    ⁅⁅L.comap (QuotientGroup.mk' N), L.comap (QuotientGroup.mk' N)⁆,
        ⁅L.comap (QuotientGroup.mk' N), L.comap (QuotientGroup.mk' N)⁆⁆ =
      ⁅L.comap (QuotientGroup.mk' N), L.comap (QuotientGroup.mk' N)⁆ := by
  haveI : (L.comap (QuotientGroup.mk' N)).Normal := Subgroup.Normal.comap inferInstance _
  have h := commutator_comap_sup_ker (QuotientGroup.mk'_surjective N) hL
  rw [QuotientGroup.ker_mk'] at h
  conv_rhs => rw [← h]
  rw [commutator_sup_eq_of_le_center hNc]

theorem le_commutator_comap_of_mem (hzN : N = zpowers z) {K : Subgroup X} (hzK : z ∈ K) :
    N ≤ K := by
  intro x hx
  rw [hzN] at hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  exact zpow_mem hzK k

theorem center_commutator_comap (hNc : N ≤ center X) {L : Subgroup (X ⧸ N)} [L.Normal]
    (hL : ⁅L, L⁆ = L) (hc : center L = ⊥) :
    center ↥(⁅L.comap (QuotientGroup.mk' N), L.comap (QuotientGroup.mk' N)⁆ : Subgroup X) =
      N.subgroupOf ⁅L.comap (QuotientGroup.mk' N), L.comap (QuotientGroup.mk' N)⁆ := by
  have hK := map_commutator_comap (QuotientGroup.mk'_surjective N) hL
  ext ⟨x, hx⟩
  rw [mem_center_iff, mem_subgroupOf]
  constructor
  · intro hcen
    exact mem_of_commute_of_center_eq_bot hK hc hx fun y hy =>
      (congrArg Subtype.val (hcen ⟨y, hy⟩)).symm
  · intro hxN g
    exact Subtype.ext (mem_center_iff.1 (hNc hxN) g)

theorem exists_surjective_commutator_comap {L : Subgroup (X ⧸ N)} [L.Normal]
    (hL : ⁅L, L⁆ = L) :
    ∃ θ : ↥(⁅L.comap (QuotientGroup.mk' N), L.comap (QuotientGroup.mk' N)⁆ : Subgroup X) →* L,
      Function.Surjective θ ∧
        θ.ker = N.subgroupOf ⁅L.comap (QuotientGroup.mk' N), L.comap (QuotientGroup.mk' N)⁆ := by
  set K := ⁅L.comap (QuotientGroup.mk' N), L.comap (QuotientGroup.mk' N)⁆ with hKdef
  have hK : K.map (QuotientGroup.mk' N) = L :=
    map_commutator_comap (QuotientGroup.mk'_surjective N) hL
  have hKL : ∀ x : K, QuotientGroup.mk' N (x : X) ∈ L := fun x => hK ▸ mem_map_of_mem _ x.2
  let θ : K →* L := ((QuotientGroup.mk' N).comp K.subtype).codRestrict L hKL
  refine ⟨θ, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := (hK.symm ▸ hy : y ∈ K.map (QuotientGroup.mk' N))
    exact ⟨⟨x, hx⟩, rfl⟩
  · ext ⟨x, hx⟩
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro hθ
      have : QuotientGroup.mk' N x = 1 := congrArg Subtype.val hθ
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at this
    · intro hxN
      apply Subtype.ext
      change QuotientGroup.mk' N x = 1
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk']

theorem card_subgroupOf_zpowers (hzN : N = zpowers z) (hz2 : orderOf z = 2) {K : Subgroup X}
    (hzK : z ∈ K) : Nat.card (N.subgroupOf K) = 2 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe (le_commutator_comap_of_mem hzN hzK)).toEquiv, hzN,
    card_zpowers_of_orderOf_eq_two hz2]

end Component

theorem exists_classical_component_of_quaternion_central_product
    {X : Type} [Group X] [Finite X] (hperf : commutator X = ⊤)
    (hO : CFSG.Open.classicalInvolutionOddCore X = ⊥) {z : X} (hz : z ∈ center X)
    (hz2 : orderOf z = 2) {Q₁ Q₂ : Subgroup X} (hcomm : Q₂ ≤ centralizer (Q₁ : Set X))
    (hinf : Q₁ ⊓ Q₂ = zpowers z) (S : Sylow 2 X) (hS : (S : Subgroup X) = Q₁ ⊔ Q₂)
    {k : ℕ} (hk : 2 ≤ k) (e₁ : Q₁ ≃* QuaternionGroup (2 ^ k))
    (e₂ : Q₂ ≃* QuaternionGroup (2 ^ k))
    (hDD : ∀ (Y : Type) [Group Y] [Finite Y], commutator Y = ⊤ →
      CFSG.Open.classicalInvolutionOddCore Y = ⊥ →
      ∀ (P : Sylow 2 Y) (m : ℕ), 2 ≤ m →
        Nonempty ((P : Subgroup Y) ≃* DihedralGroup (2 ^ m) × DihedralGroup (2 ^ m)) →
        ∃ L₁ L₂ : Subgroup Y, L₁.Normal ∧ L₂.Normal ∧ L₁ ⊓ L₂ = ⊥ ∧ L₁ ⊔ L₂ = ⊤ ∧
          ∀ L ∈ ({L₁, L₂} : Set (Subgroup Y)), Nonempty (L ≃* alternatingGroup (Fin 7)) ∨
            ∃ p k : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 5 ≤ p ^ k ∧
              Nonempty (L ≃* PSL(2, GaloisField p k))) :
    ∃ K : Subgroup X, K.Normal ∧ z ∈ K ∧
      ((∃ (F : Type) (_ : Field F) (_ : Finite F), ringChar F ≠ 2 ∧ Nonempty (K ≃* SL(2, F))) ∨
        (CFSG.Open.IsQuasisimple K ∧ Nat.card (center K) = 2 ∧
          Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 7)))) := by
  classical
  haveI hNn : (zpowers z).Normal := zpowers_normal_of_mem_center hz
  have hNc : zpowers z ≤ center X := (zpowers_le (H := center X)).2 hz
  have hπs : Function.Surjective (QuotientGroup.mk' (zpowers z)) :=
    QuotientGroup.mk'_surjective _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 (X ⧸ zpowers z) := S.mapSurjective hπs
  have hS' : (S' : Subgroup (X ⧸ zpowers z)) = (Q₁ ⊔ Q₂).map (QuotientGroup.mk' (zpowers z)) := by
    rw [Sylow.coe_mapSurjective, hS]
  obtain ⟨eS⟩ := nonempty_map_sup_mulEquiv_dihedral hcomm hinf hz2 (by omega) e₁ e₂
  obtain ⟨L₁, L₂, hL₁n, hL₂n, hLinf, hLsup, hLtype⟩ :=
    hDD (X ⧸ zpowers z) (commutator_quotient_eq_top hperf)
      (oddCore_quotient_zpowers_eq_bot hO hz hz2) S' k hk ⟨(MulEquiv.subgroupCongr hS').trans eS⟩
  have hsimple : ∀ L ∈ ({L₁, L₂} : Set (Subgroup (X ⧸ zpowers z))), IsSimpleGroup L := by
    intro L hL
    rcases hLtype L hL with he | ⟨p, k', hp, -, h5, ⟨e⟩⟩
    · obtain ⟨e⟩ := he
      haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
      exact e.isSimpleGroup
    · have hk' : k' ≠ 0 := by
        rintro rfl
        rw [pow_zero] at h5
        omega
      haveI : IsSimpleGroup PSL(2, GaloisField p k') :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
          rw [GaloisField.card p k' hk']
          omega)
      exact e.isSimpleGroup
  have hperf₁ : commutator L₁ = ⊤ :=
    commutator_eq_top_of_inf_eq_bot_of_sup_eq_top (commutator_quotient_eq_top hperf) hLinf hLsup
  have hperf₂ : commutator L₂ = ⊤ :=
    commutator_eq_top_of_inf_eq_bot_of_sup_eq_top (commutator_quotient_eq_top hperf)
      (by rw [inf_comm, hLinf]) (by rw [sup_comm, hLsup])
  have hL₁ : ⁅L₁, L₁⁆ = L₁ := Subgroup.isPerfect_iff.1 ⟨hperf₁⟩
  have hL₂ : ⁅L₂, L₂⁆ = L₂ := Subgroup.isPerfect_iff.1 ⟨hperf₂⟩
  have hc₁ : center L₁ = ⊥ := by
    haveI := hsimple L₁ (Set.mem_insert _ _)
    exact center_eq_bot_of_commutator_eq_top hperf₁
  have hc₂ : center L₂ = ⊥ := by
    haveI := hsimple L₂ (Set.mem_insert_of_mem _ rfl)
    exact center_eq_bot_of_commutator_eq_top hperf₂
  have key : ∀ L ∈ ({L₁, L₂} : Set (Subgroup (X ⧸ zpowers z))), L.Normal → ⁅L, L⁆ = L →
      center L = ⊥ →
      z ∈ ⁅L.comap (QuotientGroup.mk' (zpowers z)), L.comap (QuotientGroup.mk' (zpowers z))⁆ →
      ∃ K : Subgroup X, K.Normal ∧ z ∈ K ∧
        ((∃ (F : Type) (_ : Field F) (_ : Finite F), ringChar F ≠ 2 ∧
            Nonempty (K ≃* SL(2, F))) ∨
          (CFSG.Open.IsQuasisimple K ∧ Nat.card (center K) = 2 ∧
            Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 7)))) := by
    intro L hL hLn hLp hLc hzK
    haveI := hLn
    haveI hLhat : (L.comap (QuotientGroup.mk' (zpowers z))).Normal :=
      Subgroup.Normal.comap inferInstance _
    set K := ⁅L.comap (QuotientGroup.mk' (zpowers z)), L.comap (QuotientGroup.mk' (zpowers z))⁆
      with hKdef
    have hKp : ⁅K, K⁆ = K := commutator_commutator_comap hNc hLp
    have hKperf : commutator K = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hKp)
    have hcen : center K = (zpowers z).subgroupOf K := center_commutator_comap hNc hLp hLc
    have hcard : Nat.card (center K) = 2 := by
      rw [hcen]
      exact card_subgroupOf_zpowers rfl hz2 hzK
    obtain ⟨θ, hθs, hθker⟩ := exists_surjective_commutator_comap (N := zpowers z) hLp
    have hθker' : θ.ker = center K := hθker.trans hcen.symm
    let eQ : K ⧸ center K ≃* L :=
      (QuotientGroup.quotientMulEquivOfEq hθker'.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective θ hθs)
    refine ⟨K, inferInstance, hzK, ?_⟩
    rcases hLtype L hL with he | ⟨p, k', hp, hp2, h5, ⟨e⟩⟩
    · right
      obtain ⟨e⟩ := he
      haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
      exact ⟨⟨hKperf, (eQ.trans e).isSimpleGroup⟩, hcard, ⟨eQ.trans e⟩⟩
    · left
      haveI : Group.IsPerfect K := ⟨hKperf⟩
      obtain ⟨hpp, -, F, hF, hFin, hFcard, ⟨eK⟩⟩ :=
        CFSG.ComponentClassification.CatFactsSmall.exists_sl2_equiv_of_perfect
          (P := K) (Q := L) inferInstance hθs (hθker'.le) (hθker'.symm ▸ hcard) hp2
          (CFSG.Walter.blueprintLieModel_psl_two_of_mulEquiv p k' (by omega) e)
      exact ⟨F, hF, hFin, CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hpp hp2 hFcard,
        ⟨eK⟩⟩
  rcases mem_or_mem_commutator_comap hperf hNc rfl hz2 hLinf hLsup hL₁ hL₂ hc₁ hc₂ with h | h
  · exact key L₁ (Set.mem_insert _ _) hL₁n hL₁ hc₁ h
  · exact key L₂ (Set.mem_insert_of_mem _ rfl) hL₂n hL₂ hc₂ h


end CFSG.LocalAnalysis.Mason73
