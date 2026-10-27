module

public import CFSG.ClassicalInvolution.RouteD.TWZPair

public section

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.NonClassical
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.FrameVertex CFSG.Assembly.LowTwoRank
open CFSG.Open (classicalInvolutionOddCore)

set_option linter.unusedSectionVars false


section Dichotomy

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem actX_sq_dichotomy (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) (hcard : D.card = 1) (i : Fin D.card)
    (hsmall : (D.tag i = .PSp ∧ D.rank i = 2) ∨ (D.tag i = .PSL ∧ D.rank i = 4) ∨
      (D.tag i = .PSU ∧ D.rank i = 4))
    {J J₂ : Subgroup G} {t : G} (hJ : J ∈ centralizingMembers Ω {x})
    (hJ₂ : J₂ ∈ centralizingMembers Ω {x}) (hne : J ≠ J₂) (hc : Commutes J J₂)
    (hJt : IsClassicalMember p f J t) (hJ₂t : IsClassicalMember p f J₂ t)
    {c : G} (hcx : c * x = x * c) (hc4 : c * c * (c * c) = 1)
    (hcJ : ∀ j ∈ J, c * j = j * c) (hcJ₂ : ∀ j ∈ J₂, c * j = j * c) :
    (∀ N ∈ centralizingMembers Ω {x}, N ≤ Subgroup.centralizer ({c * c} : Set G)) ∨
      (∀ N ∈ centralizingMembers Ω {x}, N ≤ Subgroup.centralizer ({t * (c * c)} : Set G)) := by
  classical
  have hsub : Subsingleton (Fin D.card) := Fin.subsingleton_iff_le_one.mpr hcard.le
  have hD : ∀ j, D.tag j ≠ .G2 ∧ D.tag j ≠ .trialityD4 := by
    intro j
    rw [hsub.elim j i]
    rcases hsmall with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> exact ⟨by decide, by decide⟩
  have hexp : D.exp i = f := (D.exp_eq i).resolve_right fun h => (hD i).2 h.1
  have hq4 : 4 ≤ p ^ f := by omega
  obtain ⟨hsc, hperf⟩ := componentFacts_of_no_exotic D hp2 hq4 hD
  have hnc : ¬ (D.tag i = .PSL ∧ D.rank i = 2) := by
    rintro ⟨h1, h2⟩
    rcases hsmall with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · rw [h] at h1; exact absurd h1 (by decide)
    · omega
    · rw [h] at h1; exact absurd h1 (by decide)
  have hadm := D.admissible i
  have hperfK : Group.IsPerfect (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K :=
    Group.isPerfect_def.2 (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero (D.tag i)
      (D.rank i) p (D.exp i) Fact.out (D.isFundTag i) hadm).1.1
  have hsurj : Function.Surjective (D.hom i) := by
    have h := D.generate
    have h2 : (⨆ j, (D.hom j).range) = (D.hom i).range := by
      refine le_antisymm (iSup_le fun j => ?_) (le_iSup (fun j => (D.hom j).range) i)
      rw [hsub.elim j i]
    rw [h2] at h
    exact MonoidHom.range_eq_top.mp h
  have hvac := CFSG.ClassicalInvolution.ModelFacts.Orth15.twinOuterVac_of_small hp2
    (by rw [hexp]; exact hq) hadm hsmall
  obtain ⟨RJ, RJ₂, xJ, xJ₂, hRJ, hRJ₂, hxJ, hxJ₂, hpair⟩ :=
    exists_twinPairOn hΩ hex hP1 D hcard i (hperf i) hnc hperfK hJ hJ₂ hne hc hJt hJ₂t
  have hty : t ∈ locLayer Ω x := le_centralizingLayer hJ hJt.mem
  have hcN : c ∈ Subgroup.normalizer (locLayer Ω x : Set G) :=
    centralizer_le_normalizer_centralizingLayer hΩ.conjInvariant x
      (Subgroup.mem_centralizer_singleton_iff.mpr hcx)
  have hccx : c * c * x = x * (c * c) := by
    calc c * c * x = c * (c * x) := by group
      _ = c * (x * c) := by rw [hcx]
      _ = (c * x) * c := by group
      _ = (x * c) * c := by rw [hcx]
      _ = x * (c * c) := by group
  have hccN : c * c ∈ Subgroup.normalizer (locLayer Ω x : Set G) :=
    centralizer_le_normalizer_centralizingLayer hΩ.conjInvariant x
      (Subgroup.mem_centralizer_singleton_iff.mpr hccx)
  set α : MulAut (locQuot Ω x) := actX c hcN with hα
  have hαα : actX (c * c) hccN = α * α := actX_mul c c hcN hcN hccN
  set ψ' : (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K →*
      MulAut (locQuot Ω x) :=
    (MulAut.conj : locQuot Ω x →* MulAut (locQuot Ω x)).comp (D.hom i) with hψ'
  have hαN : α ∈ Subgroup.normalizer ((ψ'.range : Subgroup (MulAut (locQuot Ω x))) :
      Set (MulAut (locQuot Ω x))) := mem_normalizer_range_conj (D.hom i) hsurj α
  have hfix : ∀ N : Subgroup G, N ∈ centralizingMembers Ω {x} → (∀ n ∈ N, c * n = n * c) →
      ∀ g ∈ locImg Ω x N, α g = g := by
    intro N hN hcN' g hg
    obtain ⟨y, hy, rfl⟩ := hg
    rw [hα, actX_mk]
    congr 1
    apply Subtype.ext
    show c * (y : G) * c⁻¹ = y
    rw [hcN' y (Subgroup.mem_subgroupOf.mp hy)]
    group
  have hvcomm : ∀ (R : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K)
      (N : Subgroup G), N ∈ centralizingMembers Ω {x} → (∀ n ∈ N, c * n = n * c) →
      locImg Ω x N = R.map (D.hom i) → ∀ r ∈ R,
        toInducedAutOn ψ'.range ⟨α, hαN⟩ * innerHom ψ' r =
          innerHom ψ' r * toInducedAutOn ψ'.range ⟨α, hαN⟩ := by
    intro R N hN hcN' hR r hr
    rw [innerHom_apply, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show α * ψ' r = ψ' r * α
    have hg : D.hom i r ∈ locImg Ω x N := hR ▸ Subgroup.mem_map_of_mem _ hr
    have hfx := hfix N hN hcN' _ hg
    calc α * ψ' r = (α * MulAut.conj (D.hom i r) * α⁻¹) * α := by
          show α * MulAut.conj (D.hom i r) = (α * MulAut.conj (D.hom i r) * α⁻¹) * α
          group
      _ = MulAut.conj (α (D.hom i r)) * α := by rw [mulAut_mul_conj_mul_inv]
      _ = ψ' r * α := by rw [hfx]; rfl
  have h4 : α * α * (α * α) = 1 := by
    have hc4N : c * c * (c * c) ∈ Subgroup.normalizer (locLayer Ω x : Set G) :=
      Subgroup.mul_mem _ hccN hccN
    have e1 : actX (c * c * (c * c)) hc4N = actX (c * c) hccN * actX (c * c) hccN :=
      actX_mul _ _ hccN hccN hc4N
    have e2 : actX (Ω := Ω) (x := x) (c * c * (c * c)) hc4N = 1 := by
      have h1 : (1 : G) ∈ Subgroup.normalizer (locLayer Ω x : Set G) := Subgroup.one_mem _
      rw [← actX_one h1]
      exact actX_congr hc4 hc4N h1
    rw [e1, hαα] at e2
    exact e2
  have hv4 : toInducedAutOn ψ'.range ⟨α, hαN⟩ * toInducedAutOn ψ'.range ⟨α, hαN⟩ *
      (toInducedAutOn ψ'.range ⟨α, hαN⟩ * toInducedAutOn ψ'.range ⟨α, hαN⟩) = 1 := by
    have : (⟨α, hαN⟩ * ⟨α, hαN⟩ * (⟨α, hαN⟩ * ⟨α, hαN⟩) :
        ↥(Subgroup.normalizer ((ψ'.range : Subgroup (MulAut (locQuot Ω x))) :
          Set (MulAut (locQuot Ω x))))) = 1 := Subtype.ext h4
    have h' : toInducedAutOn ψ'.range ⟨α, hαN⟩ * toInducedAutOn ψ'.range ⟨α, hαN⟩ *
        (toInducedAutOn ψ'.range ⟨α, hαN⟩ * toInducedAutOn ψ'.range ⟨α, hαN⟩) =
        toInducedAutOn ψ'.range (⟨α, hαN⟩ * ⟨α, hαN⟩ * (⟨α, hαN⟩ * ⟨α, hαN⟩)) := by
      simp only [map_mul]
    rw [h', this, map_one]
  have hvv : toInducedAutOn ψ'.range ⟨α, hαN⟩ * toInducedAutOn ψ'.range ⟨α, hαN⟩ =
      toInducedAutOn ψ'.range ⟨α * α, Subgroup.mul_mem _ hαN hαN⟩ := by
    rw [← map_mul]
    rfl
  have hinn : ∀ g : locQuot Ω x, MulAut.conj g ∈ ψ'.range := by
    intro g
    obtain ⟨m, rfl⟩ := hsurj g
    exact ⟨m, rfl⟩
  have hmemN : ∀ N (hN : N ∈ centralizingMembers Ω {x}) (n : G) (hn : n ∈ N),
      locMk Ω x ⟨n, le_centralizingLayer hN hn⟩ ∈ locImg Ω x N := fun N hN n hn =>
    ⟨⟨n, le_centralizingLayer hN hn⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
  rcases hvac (MulAut (locQuot Ω x)) ψ' RJ RJ₂ xJ xJ₂ hpair _
      (hvcomm RJ J hJ hcJ hRJ.2.2) (hvcomm RJ₂ J₂ hJ₂ hcJ₂ hRJ₂.2.2) hv4 with h | h
  · left
    have key : ∀ g : locQuot Ω x, g⁻¹ * (α * α) g ∈ Subgroup.center (locQuot Ω x) := by
      intro g
      have h1 := conj_eq_of_toInducedAutOn_eq ψ'.range
        (n₁ := ⟨α * α, Subgroup.mul_mem _ hαN hαN⟩) (n₂ := 1)
        (by rw [← hvv, h, map_one]) (hinn g)
      simp only at h1
      rw [mulAut_mul_conj_mul_inv] at h1
      exact inv_mul_mem_center_of_conj_eq h1.symm
    intro N hN
    refine centralizes_of_actX_fix hΩ hex hP1 hccx hccN hN (fun n hn => ?_)
    rw [hαα]
    exact eq_of_perfect_of_central (locImg_le_commutator hΩ hN) (α * α) (fun y _ => key y) _
      (hmemN N hN n hn)
  · right
    set tb : locQuot Ω x := locMk Ω x ⟨t, hty⟩ with htb
    have hψxJ : ψ' xJ = MulAut.conj tb := by
      show MulAut.conj (D.hom i xJ) = _
      rw [hxJ]
    have key2 : ∀ g : locQuot Ω x,
        (tb * g * tb⁻¹)⁻¹ * (α * α) g ∈ Subgroup.center (locQuot Ω x) := by
      intro g
      have h1 := conj_eq_of_toInducedAutOn_eq ψ'.range
        (n₁ := ⟨α * α, Subgroup.mul_mem _ hαN hαN⟩)
        (n₂ := ⟨ψ' xJ, mem_normalizer_range ψ' xJ⟩)
        (by rw [← hvv, h, innerHom_apply]) (hinn g)
      simp only at h1
      rw [mulAut_mul_conj_mul_inv, hψxJ] at h1
      have h2 : MulAut.conj tb * MulAut.conj g * (MulAut.conj tb)⁻¹ =
          MulAut.conj (tb * g * tb⁻¹) := by simp [map_mul, map_inv]
      rw [h2] at h1
      exact inv_mul_mem_center_of_conj_eq h1.symm
    have htt : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two hJt.orderOf_eq_two
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    have htx : t * x = x * t :=
      Subgroup.mem_centralizer_singleton_iff.mp (centralizingLayer_le_centralizer Ω {x} hty)
    have hdx : t * (c * c) * x = x * (t * (c * c)) := by
      calc t * (c * c) * x = t * ((c * c) * x) := by group
        _ = t * (x * (c * c)) := by rw [hccx]
        _ = (t * x) * (c * c) := by group
        _ = (x * t) * (c * c) := by rw [htx]
        _ = x * (t * (c * c)) := by group
    have hdN : t * (c * c) ∈ Subgroup.normalizer (locLayer Ω x : Set G) :=
      centralizer_le_normalizer_centralizingLayer hΩ.conjInvariant x
        (Subgroup.mem_centralizer_singleton_iff.mpr hdx)
    have htN : t ∈ Subgroup.normalizer (locLayer Ω x : Set G) := Subgroup.le_normalizer hty
    have hdmul : actX (t * (c * c)) hdN = actX t htN * actX (c * c) hccN :=
      actX_mul t (c * c) htN hccN hdN
    intro N hN
    refine centralizes_of_actX_fix hΩ hex hP1 hdx hdN hN (fun n hn => ?_)
    have hnY := le_centralizingLayer hN hn
    have hβ : ∀ y ∈ locImg Ω x N,
        y⁻¹ * (MulAut.conj tb⁻¹ * (α * α)) y ∈ Subgroup.center (locQuot Ω x) := by
      intro y _
      have hw := key2 y
      have e : y⁻¹ * (MulAut.conj tb⁻¹ * (α * α)) y =
          tb⁻¹ * ((tb * y * tb⁻¹)⁻¹ * (α * α) y) * tb := by
        simp
        group
      rw [e]
      have hc' := Subgroup.mem_center_iff.mp hw tb⁻¹
      have e' : tb⁻¹ * ((tb * y * tb⁻¹)⁻¹ * (α * α) y) * tb =
          (tb * y * tb⁻¹)⁻¹ * (α * α) y :=
        calc tb⁻¹ * ((tb * y * tb⁻¹)⁻¹ * (α * α) y) * tb
            = ((tb * y * tb⁻¹)⁻¹ * (α * α) y) * tb⁻¹ * tb := by rw [← hc']
          _ = (tb * y * tb⁻¹)⁻¹ * (α * α) y := by group
      rw [e']
      exact hw
    have hβfix := eq_of_perfect_of_central (locImg_le_commutator hΩ hN)
      (MulAut.conj tb⁻¹ * (α * α)) hβ _ (hmemN N hN n hn)
    have hα2 : (α * α) (locMk Ω x ⟨n, hnY⟩) = tb * locMk Ω x ⟨n, hnY⟩ * tb⁻¹ := by
      have h3 : tb⁻¹ * (α * α) (locMk Ω x ⟨n, hnY⟩) * tb = locMk Ω x ⟨n, hnY⟩ := by
        have := hβfix
        simpa [MulAut.conj_apply] using this
      calc (α * α) (locMk Ω x ⟨n, hnY⟩)
          = tb * (tb⁻¹ * (α * α) (locMk Ω x ⟨n, hnY⟩) * tb) * tb⁻¹ := by group
        _ = tb * locMk Ω x ⟨n, hnY⟩ * tb⁻¹ := by rw [h3]
    have e1 : (α * α) (locMk Ω x ⟨n, hnY⟩) =
        locMk Ω x (⟨t, hty⟩ * ⟨n, hnY⟩ * ⟨t, hty⟩⁻¹) := by
      rw [hα2, htb, map_mul, map_mul, map_inv]
    have e2 : actX t htN (locMk Ω x (⟨t, hty⟩ * ⟨n, hnY⟩ * ⟨t, hty⟩⁻¹)) =
        locMk Ω x ⟨n, hnY⟩ := by
      rw [actX_mk]
      congr 1
      apply Subtype.ext
      show t * (t * n * t⁻¹) * t⁻¹ = n
      rw [htinv]
      calc t * (t * n * t) * t = (t * t) * n * (t * t) := by group
        _ = n := by rw [htt]; group
    rw [hdmul, hαα]
    show actX t htN ((α * α) (locMk Ω x ⟨n, hnY⟩)) = locMk Ω x ⟨n, hnY⟩
    rw [e1, e2]

end Dichotomy

end CFSG.ClassicalInvolution.RouteD.TWZ
