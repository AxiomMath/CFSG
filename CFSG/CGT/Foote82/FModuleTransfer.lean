module

public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes
public import CFSG.CGT.Foote82.FPrimeDefs

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {L : Subgroup (GLV V)}

private structure UMap (K : Subgroup G) (L : Subgroup (GLV V)) where
  φ : ↥K →* ↥L
  φ_surj : Function.Surjective φ
  ψ : ↥(blockU K) →* Multiplicative ↥(commSpace L ⊤)
  ψ_surj : Function.Surjective ψ
  ψ_mem_fixedSpace_iff : ∀ u : ↥(blockU K),
    ((Multiplicative.toAdd (ψ u) : ↥(commSpace L ⊤)) : V) ∈ fixedSpace L ↔ (u : G) ∈ blockZ K
  ψ_conj : ∀ (k : ↥K) (u v : ↥(blockU K)), (v : G) = k * u * (k : G)⁻¹ →
    ((Multiplicative.toAdd (ψ v) : ↥(commSpace L ⊤)) : V) =
      (φ k : GLV V) ((Multiplicative.toAdd (ψ u) : ↥(commSpace L ⊤)) : V)

private theorem conj_mem_blockU_of_mem {k g : G} (hk : k ∈ K) (hg : g ∈ blockU K) :
    k * g * k⁻¹ ∈ blockU K :=
  (Subgroup.mem_normalizer_iff.mp (Subgroup.normalizer_commutator_ge_right (blockQ K) K hk) g).mp hg

namespace UMap

private def vec (D : UMap K L) (u : ↥(blockU K)) : V :=
  ((Multiplicative.toAdd (D.ψ u) : ↥(commSpace L ⊤)) : V)

private theorem vec_mem (D : UMap K L) (u : ↥(blockU K)) : D.vec u ∈ commSpace L ⊤ :=
  (Multiplicative.toAdd (D.ψ u)).2

private theorem vec_mem_fixedSpace_iff (D : UMap K L) (u : ↥(blockU K)) :
    D.vec u ∈ fixedSpace L ↔ (u : G) ∈ blockZ K :=
  D.ψ_mem_fixedSpace_iff u

private theorem vec_conj (D : UMap K L) (k : ↥K) (u v : ↥(blockU K))
    (h : (v : G) = k * u * (k : G)⁻¹) :
    D.vec v = (D.φ k : GLV V) (D.vec u) :=
  D.ψ_conj k u v h

private theorem vec_eq_of_eq (D : UMap K L) {u : ↥(blockU K)} {x : Multiplicative ↥(commSpace L ⊤)}
    (h : D.ψ u = x) : D.vec u = ((Multiplicative.toAdd x : ↥(commSpace L ⊤)) : V) :=
  congrArg
    (fun x : Multiplicative ↥(commSpace L ⊤) => ((Multiplicative.toAdd x : ↥(commSpace L ⊤)) : V))
    h

private theorem exists_vec_eq (D : UMap K L) {y : V} (hy : y ∈ commSpace L ⊤) :
    ∃ u, D.vec u = y := by
  obtain ⟨u, hu⟩ := D.ψ_surj (Multiplicative.ofAdd ⟨y, hy⟩)
  exact ⟨u, D.vec_eq_of_eq hu⟩

private def preU (D : UMap K L) (S : Submodule (ZMod 2) V) : Subgroup G :=
  ((AddSubgroup.toSubgroup (S.comap (commSpace L ⊤).subtype).toAddSubgroup).comap D.ψ).map
    (blockU K).subtype

private theorem mem_preU (D : UMap K L) {S : Submodule (ZMod 2) V} {g : G} :
    g ∈ D.preU S ↔ ∃ h : g ∈ blockU K, D.vec ⟨g, h⟩ ∈ S := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.2, hu⟩
  · rintro ⟨h, hv⟩
    exact ⟨⟨g, h⟩, hv, rfl⟩

private theorem conj_mem_preU (D : UMap K L) {S : Submodule (ZMod 2) V} (hS : Invariant L S)
    {k g : G} (hk : k ∈ K) (hg : g ∈ D.preU S) : k * g * k⁻¹ ∈ D.preU S := by
  obtain ⟨hgU, hv⟩ := (D.mem_preU).mp hg
  have hconj : k * g * k⁻¹ ∈ blockU K := conj_mem_blockU_of_mem hk hgU
  refine (D.mem_preU).mpr ⟨hconj, ?_⟩
  rw [D.vec_conj ⟨k, hk⟩ ⟨g, hgU⟩ ⟨k * g * k⁻¹, hconj⟩ rfl]
  exact hS _ (D.φ ⟨k, hk⟩).2 _ hv

private theorem hasIrrTildeV (D : UMap K L) (hK : IsFooteBlock K K) : HasIrrTildeV L := by
  unfold HasIrrTildeV IrrSec
  refine ⟨?_, ?_⟩
  · obtain ⟨g, hgU, hgZ⟩ := SetLike.exists_of_lt hK.chief.1
    refine lt_of_le_of_ne inf_le_right fun h => hgZ ?_
    have hv : D.vec ⟨g, hgU⟩ ∈ commSpace L ⊤ := D.vec_mem _
    rw [← h] at hv
    exact (D.vec_mem_fixedSpace_iff _).mp hv.1
  · intro Y hY hCY hYL
    have hZ : blockZ K ≤ D.preU Y := fun z hz => (D.mem_preU).mpr
      ⟨blockZ_le_blockU K hz,
        hCY ⟨(D.vec_mem_fixedSpace_iff ⟨z, blockZ_le_blockU K hz⟩).mpr hz, D.vec_mem _⟩⟩
    have hle : D.preU Y ≤ blockU K := fun g hg => ((D.mem_preU).mp hg).1
    have hnorm : K ≤ Subgroup.normalizer (D.preU Y : Set G) :=
      Subgroup.le_normalizer_iff.mpr fun k hk g hg => D.conj_mem_preU hY hk hg
    rcases hK.chief.2 (D.preU Y) hZ hle hnorm with h | h
    · left
      refine le_antisymm (fun y hy => ?_) hCY
      obtain ⟨u, rfl⟩ := D.exists_vec_eq (hYL hy)
      have hu : (u : G) ∈ D.preU Y := (D.mem_preU).mpr ⟨u.2, hy⟩
      rw [h] at hu
      exact ⟨(D.vec_mem_fixedSpace_iff u).mpr hu, D.vec_mem u⟩
    · right
      refine le_antisymm hYL fun y hy => ?_
      obtain ⟨u, rfl⟩ := D.exists_vec_eq hy
      have hu : (u : G) ∈ D.preU Y := by
        rw [h]
        exact u.2
      exact ((D.mem_preU).mp hu).2

private theorem tildeVWitness (D : UMap K L) {T M : Type} [Group T] [AddGroup M]
    (R : T → M → M → Prop) (α : ↥K →* T) (hα : Function.Surjective α) (hαk : D.φ.ker ≤ α.ker)
    (β : ↥(blockU K) →* Multiplicative M) (hβ : Function.Surjective β)
    (hβk : β.ker = (blockZ K).subgroupOf (blockU K))
    (hR : ∀ (ℓ : ↥K) (u v : ↥(blockU K)), (v : G) = ℓ * u * (ℓ : G)⁻¹ →
      R (α ℓ) (Multiplicative.toAdd (β u)) (Multiplicative.toAdd (β v))) :
    TildeVWitness L T M R := by
  obtain ⟨α', hα'⟩ : ∃ α' : ↥L →* T, ∀ k, α' (D.φ k) = α k :=
    ⟨D.φ.liftOfSurjective D.φ_surj ⟨α, hαk⟩,
      fun k => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k⟩
  have hker : D.ψ.ker ≤ β.ker := by
    intro u hu
    rw [hβk, Subgroup.mem_subgroupOf]
    refine (D.vec_mem_fixedSpace_iff u).mp ?_
    have h0 : D.vec u = 0 := D.vec_eq_of_eq (MonoidHom.mem_ker.mp hu)
    rw [h0]
    exact Submodule.zero_mem _
  obtain ⟨β', hβ'⟩ : ∃ β' : Multiplicative ↥(commSpace L ⊤) →* Multiplicative M,
      ∀ u, β' (D.ψ u) = β u :=
    ⟨D.ψ.liftOfSurjective D.ψ_surj ⟨β, hker⟩,
      fun u => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ u⟩
  have hw : ∀ (w : ↥(commSpace L ⊤)) (u : ↥(blockU K)), D.ψ u = Multiplicative.ofAdd w →
      (w : V) = D.vec u := fun w u hu => (D.vec_eq_of_eq hu).symm
  have hβw : ∀ (w : ↥(commSpace L ⊤)) (u : ↥(blockU K)), D.ψ u = Multiplicative.ofAdd w →
      (AddMonoidHom.toMultiplicative.symm β' w) = Multiplicative.toAdd (β u) := fun w u hu => by
    show Multiplicative.toAdd (β' (Multiplicative.ofAdd w)) = _
    rw [← hu, hβ']
  refine ⟨α', ?_, AddMonoidHom.toMultiplicative.symm β', ?_, ?_, ?_⟩
  · intro t
    obtain ⟨k, rfl⟩ := hα t
    exact ⟨D.φ k, hα' k⟩
  · intro a
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd a)
    refine ⟨Multiplicative.toAdd (D.ψ u), ?_⟩
    show Multiplicative.toAdd (β' (Multiplicative.ofAdd (Multiplicative.toAdd (D.ψ u)))) = a
    rw [ofAdd_toAdd, hβ', hu]
    rfl
  · ext w
    obtain ⟨u, hu⟩ := D.ψ_surj (Multiplicative.ofAdd w)
    simp only [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Submodule.mem_comap,
      Submodule.subtype_apply]
    rw [hβw w u hu, hw w u hu, toAdd_eq_zero, ← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
    exact (D.vec_mem_fixedSpace_iff u).symm
  · intro ℓ w w' hww'
    obtain ⟨k, rfl⟩ := D.φ_surj ℓ
    obtain ⟨u, hu⟩ := D.ψ_surj (Multiplicative.ofAdd w)
    obtain ⟨u', hu'⟩ := D.ψ_surj (Multiplicative.ofAdd w')
    let v : ↥(blockU K) := ⟨(k : G) * (u : G) * (k : G)⁻¹, conj_mem_blockU_of_mem k.2 u.2⟩
    have hvec : D.ψ u' = D.ψ v := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      show D.vec u' = D.vec v
      rw [← hw w' u' hu', D.vec_conj k u v rfl, ← hw w u hu]
      exact hww'
    have hβv : β u' = β v := by
      rw [← hβ', ← hβ', hvec]
    rw [hα', hβw w u hu, hβw w' u' hu', hβv]
    exact hR k u v rfl

private theorem exists_surjective_of_ker_le (D : UMap K L) {T : Type} [Group T] (α : ↥K →* T)
    (hα : Function.Surjective α) (hαk : D.φ.ker ≤ α.ker) :
    ∃ α' : ↥L →* T, Function.Surjective α' := by
  refine ⟨D.φ.liftOfSurjective D.φ_surj ⟨α, hαk⟩, fun t => ?_⟩
  obtain ⟨k, rfl⟩ := hα t
  exact ⟨D.φ k, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k⟩

private theorem finrank_tildeV (D : UMap K L) {k : ℕ} (hk : CFSG.pRank 2 (tildeU K) = k) :
    Module.finrank (ZMod 2) (TildeV L) = k := by
  let q : Submodule (ZMod 2) ↥(commSpace L ⊤) := (fixedSpace L).comap (commSpace L ⊤).subtype
  let Θ : ↥(blockU K) →* Multiplicative (TildeV L) :=
    (AddMonoidHom.toMultiplicative (Submodule.mkQ q).toAddMonoidHom).comp D.ψ
  have hΘs : Function.Surjective Θ := by
    intro y
    obtain ⟨w, hw⟩ := Submodule.mkQ_surjective q (Multiplicative.toAdd y)
    obtain ⟨u, hu⟩ := D.ψ_surj (Multiplicative.ofAdd w)
    refine ⟨u, ?_⟩
    apply Multiplicative.toAdd.injective
    show (Submodule.mkQ q) (Multiplicative.toAdd (D.ψ u)) = _
    rw [hu, toAdd_ofAdd, hw]
  have hΘk : Θ.ker = (blockZ K).subgroupOf (blockU K) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← D.vec_mem_fixedSpace_iff]
    show Multiplicative.ofAdd (Submodule.mkQ q (Multiplicative.toAdd (D.ψ u))) = 1 ↔ _
    rw [ofAdd_eq_one, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    rfl
  let e : tildeU K ≃* Multiplicative (TildeV L) :=
    (QuotientGroup.quotientMulEquivOfEq hΘk).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hΘs)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CFSG.IsElementaryAbelian 2 (tildeU K) :=
    { toIsMulCommutative := ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => e.injective (by
        rw [map_pow, map_one]
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_self,
          zero_smul]) }
  have hcard := card_tildeU_eq_of_surjective Θ hΘs hΘk
  have h2 : Nat.card (TildeV L) = 2 ^ Module.finrank (ZMod 2) (TildeV L) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [h2] at hcard
  exact (CFSG.pRank_eq_of_card_eq_pow one_lt_two hcard).symm.trans hk

end UMap

theorem hasIrrTildeV_of_uMap (hK : IsFooteBlock K K)
    (φ : ↥K →* ↥L) (hφ : Function.Surjective φ)
    (ψ : ↥(blockU K) →* Multiplicative ↥(commSpace L ⊤)) (hψ : Function.Surjective ψ)
    (hψZ : ∀ u : ↥(blockU K),
      ((Multiplicative.toAdd (ψ u) : ↥(commSpace L ⊤)) : V) ∈ fixedSpace L ↔ (u : G) ∈ blockZ K)
    (hψe : ∀ (k : ↥K) (u v : ↥(blockU K)), (v : G) = k * u * (k : G)⁻¹ →
      ((Multiplicative.toAdd (ψ v) : ↥(commSpace L ⊤)) : V) =
        (φ k : GLV V) ((Multiplicative.toAdd (ψ u) : ↥(commSpace L ⊤)) : V)) :
    HasIrrTildeV L :=
  (UMap.mk φ hφ ψ hψ hψZ hψe).hasIrrTildeV hK

theorem isFPrimeModule_of_uMap (hKF : IsFPrimeType K)
    (φ : ↥K →* ↥L) (hφ : Function.Surjective φ) (hφk : φ.ker ≤ CFSG.pCore 2 ↥K)
    (ψ : ↥(blockU K) →* Multiplicative ↥(commSpace L ⊤)) (hψ : Function.Surjective ψ)
    (hψZ : ∀ u : ↥(blockU K),
      ((Multiplicative.toAdd (ψ u) : ↥(commSpace L ⊤)) : V) ∈ fixedSpace L ↔ (u : G) ∈ blockZ K)
    (hψe : ∀ (k : ↥K) (u v : ↥(blockU K)), (v : G) = k * u * (k : G)⁻¹ →
      ((Multiplicative.toAdd (ψ v) : ↥(commSpace L ⊤)) : V) =
        (φ k : GLV V) ((Multiplicative.toAdd (ψ u) : ↥(commSpace L ⊤)) : V)) :
    IsFPrimeModule L := by
  let D : UMap K L := ⟨φ, hφ, ψ, hψ, hψZ, hψe⟩
  rcases hKF with ⟨n, hn, α, hα, hαk, β, hβ, hβk, hR⟩ | ⟨⟨α, hα, hαk⟩, hr⟩ |
    ⟨α, hα, hαk, β, hβ, hβk, hR⟩ | ⟨α, hα, hαk, β, hβ, hβk, hR⟩ |
    ⟨α, hα, hαk, β, hβ, hβk, hR⟩ | ⟨⟨α, hα, hP, -⟩, hr⟩
  ·
    exact Or.inl ⟨n, hn, D.tildeVWitness _ α hα (hφk.trans hαk.ge) β hβ hβk hR⟩
  ·
    exact Or.inr (Or.inl ⟨D.exists_surjective_of_ker_le α hα (hφk.trans hαk.ge),
      D.finrank_tildeV hr⟩)
  ·
    exact Or.inr (Or.inr (Or.inl (D.tildeVWitness _ α hα (hφk.trans hαk.ge) β hβ hβk hR)))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inl
      (D.tildeVWitness _ α hα (hφk.trans hαk.ge) β hβ hβk hR))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (D.tildeVWitness _ α hα (hφk.trans hαk.ge) β hβ hβk hR)))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨D.exists_surjective_of_ker_le α hα (hφk.trans hP), D.finrank_tildeV hr⟩))))

end CFSG.CGT.Foote82
