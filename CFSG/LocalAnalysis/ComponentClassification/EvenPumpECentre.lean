module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpERed
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingLocal

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup Equiv Equiv.Perm

variable {L : Type} [Group L]

noncomputable def altAutHom {n : ℕ} (eA : L ⧸ center L ≃* alternatingGroup (Fin n)) :
    MulAut L →* MulAut (alternatingGroup (Fin n)) where
  toFun α := eA.symm.trans ((QuotientGroup.congr (center L) (center L) α
    (Subgroup.map_center_eq α)).trans eA)
  map_one' := by
    refine MulEquiv.ext fun a => ?_
    obtain ⟨x, rfl⟩ := eA.surjective a
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (center L) x
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, QuotientGroup.congr_mk']
    rfl
  map_mul' α β := by
    refine MulEquiv.ext fun a => ?_
    obtain ⟨x, rfl⟩ := eA.surjective a
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (center L) x
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, QuotientGroup.congr_mk',
      MulAut.mul_apply]

theorem altAutHom_mk {n : ℕ} (eA : L ⧸ center L ≃* alternatingGroup (Fin n)) (α : MulAut L)
    (l : L) : altAutHom eA α (eA (QuotientGroup.mk' (center L) l)) =
      eA (QuotientGroup.mk' (center L) (α l)) := by
  simp only [altAutHom, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, QuotientGroup.congr_mk']

theorem center_eq_bot_of_autFixed_alt [Finite L] (hq : IsQuasisimple L) {n : ℕ} (hn : 8 ≤ n)
    (eA : L ⧸ center L ≃* alternatingGroup (Fin n)) {Q : Subgroup (MulAut L)}
    (hQ : IsPGroup 2 Q) {T : Subgroup L} (hTF : T ≤ autFixed Q)
    (hT : IsPComponent 2 (T.subgroupOf (autFixed Q)))
    (eT : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin 10)) : center L = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect L := hq.1
  set π : L →* alternatingGroup (Fin n) := eA.toMonoidHom.comp (QuotientGroup.mk' (center L))
    with hπdef
  have hπs : Function.Surjective π := eA.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : π.ker = center L := by
    ext x
    rw [MonoidHom.mem_ker, hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ eA.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hZ2 : Nat.card (center L) ∣ 2 := by
    have h := RankTwoAlt.card_ker_dvd_two hq.1.commutator_eq_top hn hπs hπk.le
    rwa [hπk] at h
  have hTZ : ∀ z ∈ T, z ∈ center L → z = 1 := by
    intro z hzT hzZ
    have hzc : (⟨z, hzT⟩ : T) ∈ center T :=
      mem_center_iff.mpr fun t => Subtype.ext ((mem_center_iff.mp hzZ) t)
    have h1 : eT (QuotientGroup.mk' _ ⟨z, hzT⟩) ∈ center (alternatingGroup (Fin 10)) := by
      rw [mem_center_iff]
      intro a
      obtain ⟨y, rfl⟩ := eT.surjective a
      obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective _ y
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, (mem_center_iff.mp hzc) t]
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega), mem_bot,
      map_eq_one_iff _ eT.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have ho1 := orderOf_dvd_natCard (⟨⟨z, hzT⟩, h1⟩ : pPrimeCore 2 T)
    have ho2 := orderOf_dvd_natCard (⟨z, hzZ⟩ : center L)
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at ho1
    rw [Subgroup.orderOf_mk] at ho2
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 T)) := pPrimeCore_coprime_card
    have h4 : orderOf z = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp (ho2.trans hZ2) with h | h
      · exact h
      · exfalso
        rw [h] at ho1
        exact (Nat.prime_two.coprime_iff_not_dvd.mp hcop) ho1
    exact orderOf_eq_one_iff.mp h4
  have hπT : ∀ t₁ ∈ T, ∀ t₂ ∈ T, π t₁ = π t₂ → t₁ = t₂ := by
    intro t₁ h₁ t₂ h₂ h
    have h3 : t₁⁻¹ * t₂ ∈ center L := by
      rw [← hπk, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have h4 := hTZ _ (mul_mem (inv_mem h₁) h₂) h3
    rw [inv_mul_eq_one] at h4
    exact h4
  set Ψ := altAutHom eA with hΨdef
  have hbij := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n (by omega)
    (by omega)
  set cN : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective MulAut.conjNormal hbij with hcNdef
  set Φ : ↥Q →* Perm (Fin n) := cN.symm.toMonoidHom.comp (Ψ.comp Q.subtype) with hΦdef
  set Q' : Subgroup (Perm (Fin n)) := Φ.range with hQ'def
  have hQ' : IsPGroup 2 Q' := hQ.of_surjective Φ.rangeRestrict Φ.rangeRestrict_surjective
  have hΦ : ∀ (q : ↥Q) (a : alternatingGroup (Fin n)),
      (Φ q : Perm (Fin n)) * a * (Φ q)⁻¹ = (Ψ q a : Perm (Fin n)) := by
    intro q a
    have h1 : MulAut.conjNormal (Φ q) = Ψ q := cN.apply_symm_apply (Ψ q)
    rw [← h1, MulAut.conjNormal_apply]
  set F : Subgroup (alternatingGroup (Fin n)) := autFixed (Q.map Ψ) with hFdef
  have hFmem : ∀ a : alternatingGroup (Fin n),
      a ∈ F ↔ ∀ τ ∈ Q', τ * (a : Perm (Fin n)) = a * τ := by
    intro a
    rw [mem_autFixed]
    constructor
    · rintro h _ ⟨q, rfl⟩
      have h2 := hΦ q a
      rw [h (Ψ q) ⟨q, q.2, rfl⟩] at h2
      calc (Φ q : Perm (Fin n)) * a = Φ q * a * (Φ q)⁻¹ * Φ q := by group
        _ = a * Φ q := by rw [h2]
    · rintro h _ ⟨α, hα, rfl⟩
      apply Subtype.ext
      have h2 := hΦ ⟨α, hα⟩ a
      rw [h (Φ ⟨α, hα⟩) ⟨⟨α, hα⟩, rfl⟩, mul_inv_cancel_right] at h2
      exact h2.symm
  have hπF : (autFixed Q).map π ≤ F := by
    rintro _ ⟨l, hl, rfl⟩
    rw [mem_autFixed]
    rintro _ ⟨α, hα, rfl⟩
    show Ψ α (eA (QuotientGroup.mk' _ l)) = eA (QuotientGroup.mk' _ l)
    rw [hΨdef, altAutHom_mk, hl α hα]
  have hnorm : (((autFixed Q).map π).subgroupOf F).Normal := by
    constructor
    rintro ⟨y₀, hy₀F⟩ hy ⟨g₀, hg₀F⟩
    rw [mem_subgroupOf] at hy ⊢
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨l, rfl⟩ := hπs g₀
    refine ⟨l * c * l⁻¹, ?_, by simp only [map_mul, map_inv, Subgroup.coe_mul,
      Subgroup.coe_inv]⟩
    refine mem_autFixed.mpr fun α hα => ?_
    have h1 : π (α l) = π l := by
      have h2 := (mem_autFixed.mp hg₀F) (Ψ α) ⟨α, hα, rfl⟩
      rw [show π l = eA (QuotientGroup.mk' _ l) from rfl, hΨdef, altAutHom_mk] at h2
      exact h2
    have hz : l⁻¹ * α l ∈ center L := by
      rw [← hπk, MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    rw [map_mul, map_mul, map_inv, (mem_autFixed.mp hc) α hα]
    have hzc := (mem_center_iff.mp hz) c
    calc α l * c * (α l)⁻¹ = l * ((l⁻¹ * α l) * c) * (l⁻¹ * α l)⁻¹ * l⁻¹ := by group
      _ = l * (c * (l⁻¹ * α l)) * (l⁻¹ * α l)⁻¹ * l⁻¹ := by rw [hzc]
      _ = l * c * l⁻¹ := by group
  have hT1 : IsPComponent 2 ((T.map π).subgroupOf ((autFixed Q).map π)) := by
    have h := CatalogueBCentralQuotient.pComponent_map 2 (π.subgroupMap (autFixed Q))
      (π.subgroupMap_surjective _) ?_ (T.subgroupOf (autFixed Q)) hT
    · rwa [GSThmB.OddQuot.map_subgroupOf_subgroupMap π hTF] at h
    · intro x hx
      have h1 : (x : L) ∈ center L := by
        rw [← hπk, MonoidHom.mem_ker]
        exact congrArg Subtype.val hx
      exact mem_center_iff.mpr fun y => Subtype.ext ((mem_center_iff.mp h1) y)
  have hTF' : T.map π ≤ (autFixed Q).map π := map_mono hTF
  have hT2 : IsPComponent 2 ((T.map π).subgroupOf F) :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hTF' hπF
      hnorm.isSubnormal).mpr hT1
  set ι := (alternatingGroup (Fin n)).subtype with hιdef
  set Nq := normalizer (Q' : Set (Perm (Fin n))) with hNqdef
  set Fp := F.map ι with hFpdef
  have hFpN : Fp ≤ Nq := by
    rintro _ ⟨a, ha, rfl⟩
    apply centralizer_le_normalizer
    rw [mem_centralizer_iff]
    exact (hFmem a).mp ha
  have hFpn : (Fp.subgroupOf Nq).Normal := by
    constructor
    rintro ⟨x, hxN⟩ hx ⟨g, hg⟩
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := hx
    have hga : g * (a : Perm (Fin n)) * g⁻¹ ∈ alternatingGroup (Fin n) :=
      (alternatingGroup.normal (α := Fin n)).conj_mem _ a.2 g
    refine ⟨⟨_, hga⟩, (hFmem _).mpr fun τ hτ => ?_, rfl⟩
    have h1 : g⁻¹ * τ * g ∈ Q' := by
      have h2 := (mem_normalizer_iff.mp (inv_mem hg) τ).mp hτ
      rwa [inv_inv] at h2
    have h3 := (hFmem a).mp ha _ h1
    calc τ * (g * (a : Perm (Fin n)) * g⁻¹) = g * ((g⁻¹ * τ * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * τ * g)) * g⁻¹ := by rw [h3]
      _ = g * (a : Perm (Fin n)) * g⁻¹ * τ := by group
  set Tp := (T.map π).map ι with hTpdef
  have hTpFp : Tp ≤ Fp := map_mono (hTF'.trans hπF)
  have hι : ¬ 2 ∣ Nat.card ι.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr (subtype_injective _), Subgroup.card_bot]
    norm_num
  have hT3 : IsPComponent 2 (Tp.subgroupOf Fp) :=
    GSThmB.OddQuot.isPComponent_map ι hι (hTF'.trans hπF) hT2
  have hT4 : IsPComponent 2 (Tp.subgroupOf Nq) :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hTpFp hFpN
      hFpn.isSubnormal).mpr hT3
  obtain ⟨hdeg, hLeq, -⟩ :=
    CatalogueBAlternating.symmetric_normalizer_pComponent 2 Q' hQ' (Tp.subgroupOf Nq) hT4
  set Ω := MulAction.fixedPoints Q' (Fin n) with hΩdef
  obtain ⟨j⟩ : Nonempty (Fin 4 ↪ Ω) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    omega
  set ιn : Fin 4 ↪ Fin n := j.trans (Function.Embedding.subtype _) with hιndef
  have hne : ∀ a b : Fin 4, a ≠ b → j a ≠ j b := fun a b h => j.injective.ne h
  have key : ∀ (a b c d : Fin 4), a ≠ b → c ≠ d → ∃ t ∈ T,
      (π t : Perm (Fin n)) = viaEmbeddingHom ιn (swap a b * swap c d) := by
    intro a b c d hab hcd
    have hδ : swap (j a) (j b) * swap (j c) (j d) ∈ alternatingGroup Ω :=
      Alternating.Multipliers.swap_mul_swap_mem_alternatingGroup (hne a b hab) (hne c d hcd)
    have hd : CatalogueBAlternating.fixedPointsNormalizerHom Q'
        (swap (j a) (j b) * swap (j c) (j d)) ∈ Tp.subgroupOf Nq := by
      rw [hLeq]
      exact mem_map_of_mem _ hδ
    obtain ⟨u, ⟨t, ht, rfl⟩, hu⟩ := hd
    refine ⟨t, ht, ?_⟩
    rw [show (π t : Perm (Fin n)) = ι (π t) from rfl, hu, Subgroup.coe_subtype,
      CatalogueBAlternating.fixedPointsNormalizerHom_coe, map_mul, map_mul,
      Equiv.Perm.ofSubtype_swap_eq, Equiv.Perm.ofSubtype_swap_eq,
      RankTwoAlt.viaEmbeddingHom_swap, RankTwoAlt.viaEmbeddingHom_swap]
    rfl
  obtain ⟨t₁, ht₁, hx⟩ := key 0 1 2 3 (by decide) (by decide)
  obtain ⟨t₂, ht₂, hy⟩ := key 0 2 1 3 (by decide) (by decide)
  have hcomm : t₁ * t₂ = t₂ * t₁ := by
    apply hπT _ (mul_mem ht₁ ht₂) _ (mul_mem ht₂ ht₁)
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hx, hy, ← map_mul, ← map_mul,
      show (swap 0 1 * swap 2 3 : Perm (Fin 4)) * (swap 0 2 * swap 1 3) =
        (swap 0 2 * swap 1 3) * (swap 0 1 * swap 2 3) by decide]
  rcases (Nat.dvd_prime Nat.prime_two).mp hZ2 with h1 | h2
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exact absurd hcomm (RankTwoAlt.mul_ne_mul_of_card_ker_eq_two hn hπs hπk.le
      (by rw [hπk]; exact h2) ιn hx hy)

end CFSG.ComponentClassification.EvenPump
