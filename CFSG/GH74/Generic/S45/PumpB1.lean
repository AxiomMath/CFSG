module

public import CFSG.GH74.Generic.S45.PumpA3

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.ABGLocalTools Subgroup

section B

variable {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)} {T : Subgroup G}

theorem S45Conf.false_of_subnormal_autGv' (h : S45Conf x K T) {v : ↥T} (hv : (v : G) ∈ Pre x K) (hv1 : v ≠ 1)
    (Av : Subgroup (MulAut ↥T))
    (hAv : Av = T.normalizerMonoidHom.range ⊓ MulAction.stabilizer (MulAut ↥T) v)
    (M : Subgroup ↥Av) (hM : M.IsSubnormal) (hM1 : M ≠ ⊥)
    (hMx : ∀ f ∈ M, (f : MulAut ↥T) (⟨x, h.x_mem⟩ : ↥T) = ⟨x, h.x_mem⟩) : False := by
  subst hAv
  exact h.false_of_subnormal_autGv hv hv1 M hM hM1 hMx

theorem S45Conf.false_of_subnormal_pre (h : S45Conf x K T) {v : ↥T} (hv : (v : G) ∈ Pre x K) (hv1 : v ≠ 1)
    (M : Subgroup G) (hMH : M ≤ centralizer ({(v : G)} : Set G))
    (hMsub : (M.subgroupOf (centralizer ({(v : G)} : Set G))).IsSubnormal)
    (c : G) (hcM : c ∈ M) (hcN : c ∈ normalizer (T : Set G))
    (hc1 : T.normalizerMonoidHom ⟨c, hcN⟩ ≠ 1)
    (hcent : ∀ n ∈ M, ∀ _ : n ∈ normalizer (T : Set G), n * x * n⁻¹ = x) : False := by
  set H : Subgroup G := centralizer ({(v : G)} : Set G) with hH
  set Nv : Subgroup G := normalizer (T : Set G) ⊓ H with hNv
  let ρ : ↥Nv →* MulAut ↥T :=
    T.normalizerMonoidHom.comp (Subgroup.inclusion (inf_le_left : Nv ≤ normalizer (T : Set G)))
  have hρ : ∀ (n : ↥Nv) (t : ↥T), ((ρ n t : ↥T) : G) = (n : G) * (t : G) * (n : G)⁻¹ := fun n t => rfl
  have hnv : ∀ n : ↥Nv, ρ n v = v := by
    intro n
    apply Subtype.ext
    rw [hρ]
    have hnH : (n : G) ∈ centralizer ({(v : G)} : Set G) := (Subgroup.mem_inf.1 n.2).2
    rw [Subgroup.mem_centralizer_singleton_iff] at hnH
    rw [mul_inv_eq_iff_eq_mul]
    exact hnH
  have hrange : ρ.range = T.normalizerMonoidHom.range ⊓ MulAction.stabilizer (MulAut ↥T) v := by
    ext f
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨⟨_, rfl⟩, MulAction.mem_stabilizer_iff.2 (hnv n)⟩
    · rintro ⟨⟨m, rfl⟩, hf⟩
      have hfv : (T.normalizerMonoidHom m) v = v := MulAction.mem_stabilizer_iff.1 hf
      have h1 : (m : G) * (v : G) * (m : G)⁻¹ = (v : G) := congrArg Subtype.val hfv
      have hmH : (m : G) ∈ H := by
        rw [hH, Subgroup.mem_centralizer_singleton_iff]
        rw [mul_inv_eq_iff_eq_mul] at h1
        exact h1
      exact ⟨⟨(m : G), m.2, hmH⟩, rfl⟩
  have hsubNv : (M.subgroupOf Nv).IsSubnormal := by
    have := hMsub.comap (Subgroup.inclusion (inf_le_right : Nv ≤ H))
    exact this
  have hsurj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
  have hM1sub : ((M.subgroupOf Nv).map ρ.rangeRestrict).IsSubnormal := hsubNv.map hsurj
  refine h.false_of_subnormal_autGv' hv hv1 ρ.range hrange ((M.subgroupOf Nv).map ρ.rangeRestrict)
    hM1sub ?_ ?_
  ·
    intro hbot
    have hcNv : c ∈ Nv := ⟨hcN, hMH hcM⟩
    have hmem : (ρ.rangeRestrict ⟨c, hcNv⟩) ∈ (M.subgroupOf Nv).map ρ.rangeRestrict :=
      ⟨⟨c, hcNv⟩, hcM, rfl⟩
    rw [hbot] at hmem
    have h1 : ρ.rangeRestrict ⟨c, hcNv⟩ = 1 := hmem
    have h2 : ρ ⟨c, hcNv⟩ = 1 := congrArg Subtype.val h1
    exact hc1 h2
  · rintro f ⟨n, hn, rfl⟩
    show ((ρ n : MulAut ↥T) (⟨x, h.x_mem⟩ : ↥T)) = ⟨x, h.x_mem⟩
    apply Subtype.ext
    rw [hρ]
    exact hcent (n : G) hn n.2.1

end B

end CFSG.GH74.Generic.S45
