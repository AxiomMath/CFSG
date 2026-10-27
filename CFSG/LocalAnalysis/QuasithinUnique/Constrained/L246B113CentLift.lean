module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Rank2
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.QuasithinUnique.Bridge

open CFSG.QuasithinUnique

theorem SylowAutTrivial.of_mulEquiv {S S' : Type} [Group S] [Finite S] [Group S'] (e : S ≃* S')
    (h : SylowAutTrivial S') : SylowAutTrivial S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite S' := Finite.of_equiv S e.toEquiv
  intro P α hα hfix
  have hP2 : IsPGroup 2 ↥((P : Subgroup S).map e.toMonoidHom) := P.isPGroup'.map e.toMonoidHom
  have hPi : ¬ 2 ∣ ((P : Subgroup S).map e.toMonoidHom).index := by
    rw [Subgroup.index_map_of_bijective e.bijective]
    exact P.not_dvd_index
  let P' : Sylow 2 S' := hP2.toSylow hPi
  have hα' : Odd (orderOf (MulAut.congr e α)) := by
    rwa [MulEquiv.orderOf_eq]
  have hfix' : ∀ t ∈ (P' : Subgroup S'), (MulAut.congr e α) t = t := by
    intro t ht
    have ht' : t ∈ (P : Subgroup S).map e.toMonoidHom := by simpa [P'] using ht
    obtain ⟨s, hs, rfl⟩ := ht'
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulEquiv.coe_toMonoidHom]
    rw [hfix s hs]
  have h1 : MulAut.congr e α = 1 := h P' (MulAut.congr e α) hα' hfix'
  exact (MulAut.congr e).injective (by rw [h1, map_one])

theorem centralizes_of_sylowAutTrivial {Ω : Type} [Group Ω] [Finite Ω] {L T : Subgroup Ω}
    (hq : CFSG.IsQuasisimple ↥L) (hT : IsSylowTwoOf T L)
    (hS : SylowAutTrivial (↥L ⧸ Subgroup.center ↥L)) {x : Ω}
    (hxN : x ∈ Subgroup.normalizer (L : Set Ω)) (hxT : x ∈ Subgroup.centralizer (T : Set Ω))
    (hxo : Odd (orderOf x)) : x ∈ Subgroup.centralizer (L : Set Ω) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZ
  have hperf : Group.IsPerfect ↥L := hq.1
  let cx : ↥L ≃* ↥L := L.normalizerMonoidHom ⟨x, hxN⟩
  have hcx : ∀ l : ↥L, ((cx l : ↥L) : Ω) = x * (l : Ω) * x⁻¹ := fun l => rfl
  have hker0 : cx.toMonoidHom.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff cx.toMonoidHom).2 cx.injective
  have hmap : Z.map cx.toMonoidHom = Z :=
    CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel cx.toMonoidHom
      cx.surjective (by rw [hker0]; exact bot_le)
  let ᾱ : MulAut (↥L ⧸ Z) := QuotientGroup.congr Z Z cx hmap
  have hᾱ : ∀ l : ↥L, ᾱ (QuotientGroup.mk l) = QuotientGroup.mk (cx l) := fun l => rfl
  have hcxpow : cx ^ orderOf x = 1 := by
    have h1 : (L.normalizerMonoidHom ⟨x, hxN⟩) ^ orderOf x = 1 := by
      rw [← map_pow]
      have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (L : Set Ω))) ^ orderOf x = 1 :=
        Subtype.ext (pow_orderOf_eq_one x)
      rw [this, map_one]
    exact h1
  have hpow : ∀ k : ℕ, ∀ l : ↥L,
      (ᾱ ^ k) (QuotientGroup.mk l) = QuotientGroup.mk ((cx ^ k) l) := by
    intro k
    induction k with
    | zero => intro l; simp
    | succ k ih =>
      intro l
      rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply, ih, hᾱ]
  have hᾱpow : ᾱ ^ orderOf x = 1 := by
    refine MulEquiv.ext fun m => ?_
    induction m using QuotientGroup.induction_on with
    | H l => rw [hpow, hcxpow]; rfl
  have hodd' : Odd (orderOf ᾱ) := Odd.of_dvd_nat hxo (orderOf_dvd_of_pow_eq_one hᾱpow)
  have hT2 : IsPGroup 2 ↥(T.subgroupOf L) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  have hTp : IsPGroup 2 ↥((T.subgroupOf L).map (QuotientGroup.mk' Z)) := hT2.map _
  have hTi : ¬ 2 ∣ ((T.subgroupOf L).map (QuotientGroup.mk' Z)).index := fun h =>
    hT.2.2 (h.trans (Subgroup.index_map_dvd (T.subgroupOf L) (QuotientGroup.mk'_surjective Z)))
  let P : Sylow 2 (↥L ⧸ Z) := hTp.toSylow hTi
  have hfix : ∀ t ∈ (P : Subgroup (↥L ⧸ Z)), ᾱ t = t := by
    intro y hy
    have hy' : y ∈ (T.subgroupOf L).map (QuotientGroup.mk' Z) := by simpa [P] using hy
    obtain ⟨t', ht', rfl⟩ := hy'
    have hc : (t' : Ω) * x = x * (t' : Ω) := Subgroup.mem_centralizer_iff.1 hxT t' ht'
    have : cx t' = t' := Subtype.ext (by rw [hcx]; rw [mul_inv_eq_iff_eq_mul, ← hc])
    show ᾱ (QuotientGroup.mk t') = QuotientGroup.mk t'
    rw [hᾱ, this]
  have h1 : ᾱ = 1 := hS P ᾱ hodd' hfix
  have hz : ∀ l : ↥L, l⁻¹ * cx l ∈ Z := by
    intro l
    have := congrArg (fun φ : MulAut (↥L ⧸ Z) => φ (QuotientGroup.mk l)) h1
    simp only [hᾱ, MulAut.one_apply] at this
    exact QuotientGroup.eq.1 this.symm
  let c : ↥L →* ↥Z :=
    { toFun := fun l => ⟨l⁻¹ * cx l, hz l⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have hca : (a⁻¹ * cx a) * b⁻¹ = b⁻¹ * (a⁻¹ * cx a) :=
          (Subgroup.mem_center_iff.1 (hz a) b⁻¹).symm
        show (a * b)⁻¹ * cx (a * b) = (a⁻¹ * cx a) * (b⁻¹ * cx b)
        calc (a * b)⁻¹ * cx (a * b) = b⁻¹ * (a⁻¹ * cx a) * cx b := by rw [map_mul]; group
          _ = (a⁻¹ * cx a) * b⁻¹ * cx b := by rw [← hca]
          _ = (a⁻¹ * cx a) * (b⁻¹ * cx b) := by group }
  have hker : commutator ↥L ≤ c.ker := Abelianization.commutator_subset_ker c
  have hall : ∀ l : ↥L, cx l = l := by
    intro l
    have hl : l ∈ c.ker := hker (by rw [hperf.commutator_eq_top]; trivial)
    have := congrArg Subtype.val hl
    have h2 : l⁻¹ * cx l = 1 := by simpa [c] using this
    exact (inv_mul_eq_one.1 h2).symm
  refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
  have := congrArg Subtype.val (hall ⟨h, hh⟩)
  rw [hcx] at this
  simp only at this
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

end CFSG.QuasithinUnique.Bridge
