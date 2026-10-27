module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L56PartB

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_mul_right_of_commute {a w t : G}
    (h : w * (t * a⁻¹ * t⁻¹) = (t * a⁻¹ * t⁻¹) * w) : ⁅a, w * t⁆ = ⁅a, t⁆ := by
  calc ⁅a, w * t⁆ = a * (w * (t * a⁻¹ * t⁻¹)) * w⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = a * ((t * a⁻¹ * t⁻¹) * w) * w⁻¹ := by rw [h]
    _ = ⁅a, t⁆ := by simp only [commutatorElement_def]; group

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem commutes_of_commutator_le {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (J : Set G)) (hJT : ⁅J, T⁆ ≤ blockU J) :
    ∀ t ∈ T, ∀ v ∈ blockU J, t * v = v * t := by
  intro t ht
  have hJ := c.block
  have hVc : ∀ a ∈ blockU J, ∀ b ∈ blockU J, a * b = b * a := hJ.blockU_comm
  have htN : t ∈ Subgroup.normalizer (J : Set G) := hTN ht
  have htV : ∀ v ∈ blockU J, t * v * t⁻¹ ∈ blockU J := fun v hv => conj_mem_blockU htN hv
  have hjV : ∀ j ∈ J, ∀ v ∈ blockU J, j * v * j⁻¹ ∈ blockU J := fun j hj v hv =>
    conj_mem_blockU (Subgroup.le_normalizer hj) hv
  have hjt : ∀ j ∈ J, ⁅j, t⁆ ∈ blockU J := fun j hj =>
    hJT (Subgroup.commutator_mem_commutator hj ht)
  have hvt : ∀ v ∈ blockU J, ⁅v, t⁆ ∈ blockU J := fun v hv => by
    have : ⁅v, t⁆ = v * (t * v⁻¹ * t⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact (blockU J).mul_mem hv (htV v⁻¹ ((blockU J).inv_mem hv))
  have hmul : ∀ v ∈ blockU J, ∀ v' ∈ blockU J, ⁅v * v', t⁆ = ⁅v, t⁆ * ⁅v', t⁆ :=
    fun v hv v' hv' => commutator_mul_left_of_commute (hVc _ hv _ (hvt v' hv'))
      (hVc _ (hvt v' hv') _ (hvt v hv))
  have heq : ∀ j ∈ J, ∀ v ∈ blockU J, j * ⁅v, t⁆ * j⁻¹ = ⁅j * v * j⁻¹, t⁆ := by
    intro j hj v hv
    have ha := hjV j hj v hv
    have hw := hjt j hj
    have hb : t * (j * v * j⁻¹)⁻¹ * t⁻¹ ∈ blockU J := htV _ ((blockU J).inv_mem ha)
    have e1 : j * ⁅v, t⁆ * j⁻¹ = ⁅j * v * j⁻¹, ⁅j, t⁆ * t⁆ := by
      simp only [commutatorElement_def]; group
    rw [e1]
    exact commutator_mul_right_of_commute (hVc _ hw _ hb)
  let φ : ↥(blockU J) →* ↥(blockU J) :=
    MonoidHom.mk' (fun v => ⟨⁅(v : G), t⁆, hvt v v.2⟩) (fun v v' => by
      apply Subtype.ext
      exact hmul v v.2 v' v'.2)
  obtain ⟨D, hD⟩ : ∃ D : Subgroup G, D = φ.range.map (blockU J).subtype := ⟨_, rfl⟩
  have hDmem : ∀ d, d ∈ D ↔ ∃ v ∈ blockU J, d = ⁅v, t⁆ := by
    intro d
    rw [hD]
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨v, v.2, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨φ ⟨v, hv⟩, ⟨⟨v, hv⟩, rfl⟩, rfl⟩
  have hDV : D ≤ blockU J := by
    rw [hD]
    exact Subgroup.map_subtype_le _
  have hDJ : ∀ j ∈ J, ∀ d ∈ D, j * d * j⁻¹ ∈ D := by
    intro j hj d hd
    obtain ⟨v, hv, rfl⟩ := (hDmem d).1 hd
    rw [heq j hj v hv]
    exact (hDmem _).2 ⟨j * v * j⁻¹, hjV j hj v hv, rfl⟩
  have hZJ : ∀ j ∈ J, ∀ z ∈ blockZ J, j * z * j⁻¹ = z := by
    intro j hj z hz
    have h := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 j hj
    rw [h]
    group
  have hDZ : ∀ d ∈ D, ∀ z ∈ blockZ J, d * z = z * d := fun d hd z hz =>
    hVc d (hDV hd) z (blockZ_le_blockU J hz)
  have hNn : ∀ g ∈ J, ∀ n ∈ D ⊔ blockZ J, g * n * g⁻¹ ∈ D ⊔ blockZ J := by
    intro g hg n hn
    obtain ⟨d, hd, z, hz, rfl⟩ := (mem_sup_iff_of_commute hDZ).1 hn
    have e : g * (d * z) * g⁻¹ = (g * d * g⁻¹) * z := by
      calc g * (d * z) * g⁻¹ = (g * d * g⁻¹) * (g * z * g⁻¹) := by group
        _ = (g * d * g⁻¹) * z := by rw [hZJ g hg z hz]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hDJ g hg d hd)) (Subgroup.mem_sup_right hz)
  rcases blockU_irred_of_short hJ.short (D ⊔ blockZ J) le_sup_right
    (sup_le hDV (blockZ_le_blockU J)) hNn with hN | hN
  ·
    have hDZ' : ∀ v ∈ blockU J, ⁅v, t⁆ ∈ blockZ J := fun v hv => by
      have h1 : ⁅v, t⁆ ∈ D ⊔ blockZ J :=
        Subgroup.mem_sup_left ((hDmem _).2 ⟨v, hv, rfl⟩)
      rwa [hN] at h1
    have hψ : ∀ v ∈ blockU J, ∀ j ∈ J, ⁅j * v * j⁻¹, t⁆ = ⁅v, t⁆ := fun v hv j hj => by
      rw [← heq j hj v hv]
      exact hZJ j hj _ (hDZ' v hv)
    have hker : ⁅blockU J, J⁆ ≤ (φ.ker).map (blockU J).subtype := by
      refine Subgroup.commutator_le.2 fun v hv j hj => ?_
      have hw : j * v⁻¹ * j⁻¹ ∈ blockU J := hjV j hj v⁻¹ ((blockU J).inv_mem hv)
      have hx : ⁅v, j⁆ = v * (j * v⁻¹ * j⁻¹) := by rw [commutatorElement_def]; group
      have hxV : ⁅v, j⁆ ∈ blockU J := by
        rw [hx]
        exact (blockU J).mul_mem hv hw
      refine ⟨⟨⁅v, j⁆, hxV⟩, MonoidHom.mem_ker.2 (Subtype.ext ?_), rfl⟩
      show ⁅⁅v, j⁆, t⁆ = 1
      rw [hx, hmul v hv _ hw, hψ v⁻¹ ((blockU J).inv_mem hv) j hj,
        ← hmul v hv v⁻¹ ((blockU J).inv_mem hv), mul_inv_cancel]
      simp [commutatorElement_def]
    intro v hv
    have hmem : v ∈ (φ.ker).map (blockU J).subtype :=
      hker (by rw [hJ.blockU_stable]; exact hv)
    obtain ⟨x, hx, rfl⟩ := hmem
    have h1 : ⁅(x : G), t⁆ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  ·
    exfalso
    have hVD : blockU J ≤ D := by
      have hle : ⁅blockU J, J⁆ ≤ D := by
        refine Subgroup.commutator_le.2 fun v hv j hj => ?_
        rw [← hN] at hv
        obtain ⟨d, hd, z, hz, rfl⟩ := (mem_sup_iff_of_commute hDZ).1 hv
        have hzj' : j * z = z * j := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 j hj
        have hzj : z * j * z⁻¹ = j := by
          rw [← hzj']
          group
        have e : ⁅d * z, j⁆ = d * (j * d⁻¹ * j⁻¹) := by
          calc ⁅d * z, j⁆ = d * (z * j * z⁻¹) * d⁻¹ * j⁻¹ := by
                simp only [commutatorElement_def]; group
            _ = d * j * d⁻¹ * j⁻¹ := by rw [hzj]
            _ = d * (j * d⁻¹ * j⁻¹) := by group
        rw [e]
        exact D.mul_mem hd (hDJ j hj d⁻¹ (D.inv_mem hd))
      rwa [hJ.blockU_stable] at hle
    have hsurj : Function.Surjective φ := by
      rintro ⟨v, hv⟩
      obtain ⟨w, hw, hwv⟩ := (hDmem v).1 (hVD hv)
      exact ⟨⟨w, hw⟩, Subtype.ext hwv.symm⟩
    have hinj : Function.Injective φ := Finite.injective_iff_surjective.2 hsurj
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have ht2 : IsPGroup 2 (Subgroup.zpowers t) := by
      obtain ⟨n, hn⟩ := hT2 ⟨t, ht⟩
      have hn' : t ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      have : orderOf t ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 this
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have htz : Subgroup.zpowers t ≤ Subgroup.normalizer (blockU J : Set G) :=
      Subgroup.zpowers_le.2 (mem_normalizer_blockU htN)
    have hne := SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot Nat.prime_two
      ht2 hJ.isPGroup_blockU (blockU_ne_bot_of_short hJ.short) htz
    obtain ⟨⟨v, hv⟩, hv1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    obtain ⟨hvV, hvC⟩ := Subgroup.mem_inf.1 hv
    have hvt' : t * v = v * t := Subgroup.mem_centralizer_iff.1 hvC t (Subgroup.mem_zpowers t)
    have h1 : φ ⟨v, hvV⟩ = 1 :=
      Subtype.ext (commutatorElement_eq_one_iff_mul_comm.2 hvt'.symm)
    have h2 : (⟨v, hvV⟩ : ↥(blockU J)) = 1 := hinj (h1.trans (map_one φ).symm)
    have h3 : v = 1 := congrArg Subtype.val h2
    exact hv1' (Subtype.ext h3)

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
