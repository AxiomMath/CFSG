module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsCentL

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Solomon.Coordinator

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} [hLn : L.Normal] {π : Bool} {p f : ℕ}
  {K : Type} [Field K] {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

theorem isCyclic_centImage_of {u : GL (Fin 3) K}
    (hC : IsCyclic ↥(slPi π 3 (p ^ f) K ⊓ centralizer ({u} : Set (GL (Fin 3) K)))) :
    IsCyclic ↥(centImage ν u : Subgroup X) := by
  set C := slPi π 3 (p ^ f) K ⊓ centralizer ({u} : Set (GL (Fin 3) K))
  have hle : C ≤ slPi π 3 (p ^ f) K := inf_le_left
  haveI : IsCyclic ↥(C.subgroupOf (slPi π 3 (p ^ f) K)) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hle).symm.surjective
  exact isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)

theorem card_le_three_mul_inf {A : Subgroup X} {x : X} (hx3 : x ^ 3 = 1)
    (hA : ∀ a ∈ A, (QuotientGroup.mk a : X ⧸ L) ∈ zpowers (QuotientGroup.mk x : X ⧸ L)) :
    Nat.card A ≤ 3 * Nat.card ↥(A ⊓ L) := by
  set φ : ↥A →* X ⧸ L := (QuotientGroup.mk' L).comp A.subtype
  have hker : Nat.card φ.ker = Nat.card ↥(A ⊓ L) := by
    have : φ.ker = L.subgroupOf A := by
      ext a
      simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rw [this, ← Subgroup.card_map_of_injective A.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have hrange : Nat.card φ.range ≤ 3 := by
    have hle : φ.range ≤ zpowers (QuotientGroup.mk x : X ⧸ L) := by
      rintro _ ⟨a, rfl⟩
      exact hA a a.2
    refine (Subgroup.card_le_of_le hle).trans ?_
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by
      rw [← QuotientGroup.mk_pow, hx3, QuotientGroup.mk_one]))
  have hcard : Nat.card A = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
      mul_comm, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  rw [hcard, hker, mul_comm 3]
  exact Nat.mul_le_mul_left _ hrange

theorem LModel.false_of_no_field_cover (M : LModel L π p f K ν) (hinj : Function.Injective ν)
    (hCL : centralizer (L : Set X) ≤ L) (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3) {x : X}
    (hx3 : x ^ 3 = 1) {y : GL (Fin 3) K} (hx : IsLiftAt ν x y) (hT : IsTypeThree π (p ^ f) K y)
    (hno : ∀ (φ : X) (σ : K ≃+* K) (H : GL (Fin 3) K), φ ^ 3 = 1 → ¬ IsFieldAt ν φ σ H) :
    False := by
  have := M.piField.finite
  obtain ⟨A, hA, hA27⟩ := exists_elemAbelian_27 hX
  have hlift : ∀ a ∈ A, ∃ y', IsLiftAt ν a y' := fun a ha => by
    rcases M.dichotomy (hA.2 a ha) with h' | ⟨σ, H, h'⟩
    · exact h'
    · exact absurd h' (hno a σ H (hA.2 a ha))
  have hny := hT.not_isInnerMat M.piField M.modThree
  have hinner : ∀ {g : X} {y' : GL (Fin 3) K}, IsLiftAt ν g y' → IsInnerMat π (p ^ f) K y' →
      g ∈ L := by
    intro g y' hg hin
    obtain ⟨l, hl, hlc⟩ := hg.exists_of_isInnerMat M hin
    have := mul_mem hl (hCL hlc)
    rwa [mul_inv_cancel_left] at this
  have hAx : ∀ a ∈ A, (QuotientGroup.mk a : X ⧸ L) ∈ zpowers (QuotientGroup.mk x : X ⧸ L) := by
    intro a ha
    obtain ⟨y', hy'⟩ := hlift a ha
    rcases inner_or_of_det M.piField M.modThree hx.mem hy'.mem hny with h1 | h1 | h1
    · rw [(QuotientGroup.eq_one_iff a).2 (hinner hy' h1)]
      exact one_mem _
    · have hm := hinner (hy'.mul M hx.inv) h1
      have : (QuotientGroup.mk a : X ⧸ L) = QuotientGroup.mk x := by
        have h' := (QuotientGroup.eq_one_iff (a * x⁻¹)).2 hm
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at h'
        exact h'
      rw [this]
      exact Subgroup.mem_zpowers _
    · have hm := hinner (hy'.mul M hx) h1
      have : (QuotientGroup.mk a : X ⧸ L) = (QuotientGroup.mk x)⁻¹ := by
        have h' := (QuotientGroup.eq_one_iff (a * x)).2 hm
        rw [QuotientGroup.mk_mul] at h'
        exact eq_inv_of_mul_eq_one_left h'
      rw [this]
      exact inv_mem (Subgroup.mem_zpowers _)
  have h9 : 9 ≤ Nat.card ↥(A ⊓ L) := by
    have := card_le_three_mul_inf hx3 hAx
    omega
  have hbij : Function.Bijective ν := ⟨hinj, M.surj⟩
  set e := MulEquiv.ofBijective ν hbij
  have hAL : ¬ A ≤ L := by
    intro hle
    apply not_elemAbelian_27_slPi M.piField M.modThree
      (E := ((A.subgroupOf L).map e.symm.toMonoidHom).map (slPi π 3 (p ^ f) K).subtype)
      (Subgroup.map_subtype_le _)
    · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
      · obtain ⟨_, ⟨_, ⟨s, hs, rfl⟩, rfl⟩⟩ := a
        obtain ⟨_, ⟨_, ⟨t, ht, rfl⟩, rfl⟩⟩ := b
        show ((e.symm s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) *
            (e.symm t : ↥(slPi π 3 (p ^ f) K)) =
          (e.symm t : ↥(slPi π 3 (p ^ f) K)) * (e.symm s : ↥(slPi π 3 (p ^ f) K))
        have h1 : s * t = t * s :=
          Subtype.ext (hA.comm (Subgroup.mem_subgroupOf.1 hs) (Subgroup.mem_subgroupOf.1 ht))
        rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, h1]
      · rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
        have h1 : s ^ 3 = 1 := Subtype.ext (by
          rw [Subgroup.coe_pow]
          exact hA.2 _ (Subgroup.mem_subgroupOf.1 hs))
        show ((e.symm s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) ^ 3 = 1
        rw [← SubgroupClass.coe_pow, ← map_pow, h1, map_one, OneMemClass.coe_one]
    · rw [Subgroup.card_map_of_injective (slPi π 3 (p ^ f) K).subtype_injective,
        Subgroup.card_map_of_injective e.symm.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hA27]
  obtain ⟨a, haA, haL⟩ := Set.not_subset.1 hAL
  have hxq : (QuotientGroup.mk x : X ⧸ L) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hx3, QuotientGroup.mk_one]
  obtain ⟨b, hbA, hbx⟩ : ∃ b ∈ A, b * x⁻¹ ∈ L := by
    rcases eq_of_mem_zpowers_of_pow_three hxq (hAx a haA) with h1 | h1 | h1
    · exact absurd ((QuotientGroup.eq_one_iff a).1 h1) haL
    · refine ⟨a, haA, (QuotientGroup.eq_one_iff _).1 ?_⟩
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1, mul_inv_cancel]
    · refine ⟨a⁻¹, inv_mem haA, (QuotientGroup.eq_one_iff _).1 ?_⟩
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, h1]
      calc ((QuotientGroup.mk x : X ⧸ L) ^ 2)⁻¹ * (QuotientGroup.mk x)⁻¹ =
          ((QuotientGroup.mk x : X ⧸ L) ^ 3)⁻¹ := by group
        _ = 1 := by rw [hxq, inv_one]
  obtain ⟨s, hs⟩ := M.surj ⟨b * x⁻¹, hbx⟩
  have hsl : ((ν s : ↥L) : X) = b * x⁻¹ := by rw [hs]
  have hbsx : b = ((ν s : ↥L) : X) * x := by rw [hsl, inv_mul_cancel_right]
  have hb := (isLiftAt_of_mem M s).mul M hx
  rw [← hbsx] at hb
  obtain ⟨t, ht, ht3⟩ := hx.pow_three_mul M hx3 s
  rw [← hbsx, hA.2 b hbA] at ht3
  have ht1 : t = 1 := hinj (by rw [map_one]; exact Subtype.ext ht3.symm)
  have hu3 : ((s : GL (Fin 3) K) * y) ^ 3 = y ^ 3 := by
    have h1 := congrArg Subtype.val ht1
    rw [ht, OneMemClass.coe_one] at h1
    exact mul_inv_eq_one.1 h1
  obtain ⟨ℓ, hℓy, hℓ⟩ := hT.not_cube M.piField M.modThree
  have hu : (((s : GL (Fin 3) K) * y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 =
      (ℓ : K) • 1 := by
    rw [← Units.val_pow_eq_pow_val, hu3, Units.val_pow_eq_pow_val, hℓy]
  have huH : (s : GL (Fin 3) K) * y ∈ glPi π 3 (p ^ f) K :=
    mul_mem (slPi_le_glPi M.hπ s.2) hx.mem
  have hcyc := (centralizer_slPi_cyclic M.piField M.modThree huH hℓ hu).1
  have hle : A ⊓ L ≤ centImage ν ((s : GL (Fin 3) K) * y) := by
    intro a' ha'
    obtain ⟨ha'A, ha'L⟩ := Subgroup.mem_inf.1 ha'
    obtain ⟨s', hs'⟩ := M.surj ⟨a', ha'L⟩
    have hs'a : ((ν s' : ↥L) : X) = a' := by rw [hs']
    refine mem_centImage.2 ⟨s', ?_, hs'a⟩
    have h1 := hb.act s' (M.conjBy hb.mem s') (M.coe_conjBy hb.mem s')
    have hcomm := hA.comm hbA ha'A
    rw [hs'a, show b * a' * b⁻¹ = a' by rw [hcomm, mul_inv_cancel_right], ← hs'a] at h1
    have h2 : M.conjBy hb.mem s' = s' := hinj (Subtype.ext h1.symm)
    have h3 : (s : GL (Fin 3) K) * y * s' * ((s : GL (Fin 3) K) * y)⁻¹ = s' := by
      rw [← M.coe_conjBy hb.mem s', h2]
    calc (s' : GL (Fin 3) K) * ((s : GL (Fin 3) K) * y) =
        (s : GL (Fin 3) K) * y * s' * ((s : GL (Fin 3) K) * y)⁻¹ * ((s : GL (Fin 3) K) * y) := by
          rw [h3]
      _ = (s : GL (Fin 3) K) * y * s' := by group
  haveI : IsCyclic ↥(centImage ν ((s : GL (Fin 3) K) * y) : Subgroup X) :=
    isCyclic_centImage_of hcyc
  haveI : IsCyclic ↥((A ⊓ L).subgroupOf (centImage ν ((s : GL (Fin 3) K) * y))) :=
    Subgroup.isCyclic _
  haveI : IsCyclic ↥(A ⊓ L) := isCyclic_of_surjective
    (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom (Subgroup.subgroupOfEquivOfLe hle).surjective
  have h3 : Nat.card ↥(A ⊓ L) ≤ 3 :=
    card_le_three_of_isCyclic (fun w => Subtype.ext (hA.2 _ w.2.1))
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
