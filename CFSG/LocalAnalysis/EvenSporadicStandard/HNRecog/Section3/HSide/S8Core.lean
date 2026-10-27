module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

open scoped Pointwise

private lemma mulAut_congr_apply' {G H : Type*} [Group G] [Group H] (ϕ : G ≃* H)
    (f : MulAut G) (h : H) : (MulAut.congr ϕ f) h = ϕ (f (ϕ.symm h)) := rfl

private lemma mulAut_congr_symm_apply' {G H : Type*} [Group G] [Group H] (ϕ : G ≃* H)
    (f : MulAut H) (g : G) : ((MulAut.congr ϕ).symm f) g = ϕ.symm (f (ϕ g)) := rfl

theorem inner_or_nonempty_mulEquiv_sym_eight {H : Type} [Group H] (K : Subgroup H)
    (φ : alternatingGroup (Fin 8) ≃* ↥K) (c : H) (hc2 : c * c = 1) (hcK : c ∉ K)
    (hnorm : ∀ k ∈ K, c * k * c⁻¹ ∈ K) :
    (∃ k ∈ K, ∀ x ∈ K, c * x * c⁻¹ = k * x * k⁻¹) ∨
      Nonempty (↥(K ⊔ Subgroup.zpowers c) ≃* Sym 8) := by
  classical
  by_cases hinner : ∃ k ∈ K, ∀ x ∈ K, c * x * c⁻¹ = k * x * k⁻¹
  · exact Or.inl hinner
  · right
    let L : Subgroup H := K ⊔ Subgroup.zpowers c
    have hKL : K ≤ L := le_sup_left
    have hcL : c ∈ L := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
    have hc_inv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
    have hnormL : L ≤ Subgroup.normalizer K := by
      show K ⊔ Subgroup.zpowers c ≤ Subgroup.normalizer K
      rw [sup_le_iff]
      refine ⟨Subgroup.le_normalizer, ?_⟩
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro k
      refine ⟨hnorm k, ?_⟩
      intro hk
      have h2 := hnorm (c * k * c⁻¹) hk
      convert h2 using 1
      rw [hc_inv]
      rw [show c * (c * k * c) * c = (c * c) * k * (c * c) by group, hc2]
      simp
    haveI : (K.subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).mpr hnormL
    let e : ↥(K.subgroupOf L) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKL
    let g : L →* MulAut ↥K :=
      (MulAut.congr e).toMonoidHom.comp
        (MulAut.conjNormal : L →* MulAut ↥(K.subgroupOf L))
    let E : Sym 8 ≃* MulAut (alternatingGroup (Fin 8)) :=
      MulEquiv.ofBijective
        (MulAut.conjNormal (H := alternatingGroup (Fin 8)) :
          Sym 8 →* MulAut (alternatingGroup (Fin 8)))
        (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8
          (by norm_num) (by norm_num))
    let θ : L →* MulAut (alternatingGroup (Fin 8)) :=
      (MulAut.congr φ).symm.toMonoidHom.comp g
    let Ψ : L →* Sym 8 := E.symm.toMonoidHom.comp θ
    have hE_theta : ∀ x : L, E (Ψ x) = θ x := by
      intro x
      change E (E.symm (θ x)) = θ x
      exact MulEquiv.apply_symm_apply E (θ x)
    have conjOnK_apply : ∀ (x : L) (y : ↥K),
        ((g x y : ↥K) : H) = x.1 * y.1 * x.1⁻¹ := by
      intro x y
      have hgx : g x = MulAut.congr e (MulAut.conjNormal x) := rfl
      rw [hgx, mulAut_congr_apply']
      change (((MulAut.conjNormal x) (e.symm y) : L) : H) = x.1 * y.1 * x.1⁻¹
      rw [congrArg (fun t : L => (t : H)) (MulAut.conjNormal_apply x (e.symm y))]
      rfl
    have theta_of_mem_K : ∀ (x : L) (hxK : x.1 ∈ K),
        θ x = MulAut.conjNormal (H := alternatingGroup (Fin 8))
          (φ.symm (⟨x.1, hxK⟩ : ↥K) : Sym 8) := by
      intro x hxK
      apply MulEquiv.ext
      intro a
      have hθ : θ x = (MulAut.congr φ).symm (g x) := rfl
      rw [hθ, mulAut_congr_symm_apply']
      set z : alternatingGroup (Fin 8) := φ.symm (⟨x.1, hxK⟩ : ↥K) with hz_def
      have hgxa : (g x) (φ a) = φ (z * a * z⁻¹) := by
        apply Subtype.ext
        rw [conjOnK_apply x (φ a)]
        simp only [MulEquiv.map_mul, MulEquiv.map_inv]
        have hzx : (φ z : H) = x.1 := by
          rw [hz_def]
          simp
        rw [← hzx]
        simp
      rw [hgxa, MulEquiv.symm_apply_apply]
      exact Subtype.ext
        (MulAut.conjNormal_apply (H := alternatingGroup (Fin 8)) (z : Sym 8) a).symm
    have hPsi_K : ∀ (x : L) (hxK : x.1 ∈ K),
        Ψ x = (φ.symm (⟨x.1, hxK⟩ : ↥K) : Sym 8) := by
      intro x hxK
      change E.symm (θ x) = (φ.symm (⟨x.1, hxK⟩ : ↥K) : Sym 8)
      rw [theta_of_mem_K x hxK]
      exact MulEquiv.symm_apply_apply E (φ.symm (⟨x.1, hxK⟩ : ↥K))
    have hc_pow : ∀ m : ℤ, c ^ m = 1 ∨ c ^ m = c := by
      intro m
      have hdvd : orderOf c ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]
        simpa [pow_two] using hc2
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · left
        rw [← zpow_mod_orderOf c m, h1]
        simp
      · have hm : m % (orderOf c : ℤ) = 0 ∨ m % (orderOf c : ℤ) = 1 := by
          have h2' : (orderOf c : ℤ) = 2 := by rw [h2]; norm_num
          rw [h2']
          exact Int.emod_two_eq_zero_or_one m
        rcases hm with hm | hm
        · left
          rw [← zpow_mod_orderOf c m, hm]
          simp
        · right
          rw [← zpow_mod_orderOf c m, hm]
          simp
    have hker : ∀ z : L, Ψ z = 1 → z = 1 := by
      intro z hz
      have hθz : θ z = 1 := by
        simpa [hz] using (hE_theta z).symm
      have hg_one : g z = 1 := by
        have h1 : (MulAut.congr φ) (θ z) = g z := by
          change (MulAut.congr φ) ((MulAut.congr φ).symm (g z)) = g z
          exact MulEquiv.apply_symm_apply (MulAut.congr φ) (g z)
        rw [← h1, hθz]
        ext a
        simp
      have hzp_norm : Subgroup.zpowers c ≤ Subgroup.normalizer K :=
        le_trans le_sup_right hnormL
      have hset := Subgroup.coe_mul_of_right_le_normalizer_left K (Subgroup.zpowers c) hzp_norm
      have hz_mem : z.1 ∈ (K : Set H) * (Subgroup.zpowers c : Set H) := by
        rw [← hset]
        exact z.2
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hz_mem
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
      rcases hc_pow n with hcn | hcn
      ·
        have hb1 : b = 1 := hn.symm.trans hcn
        have hza : z.1 = a := by rw [← hab, hb1, mul_one]
        have hzK : z.1 ∈ K := by rw [hza]; exact ha
        have hconj : ∀ w : ↥K, z.1 * w.1 * z.1⁻¹ = w.1 := by
          intro w
          have h := conjOnK_apply z w
          rw [hg_one] at h
          simpa using h.symm
        have hcenterK : (⟨z.1, hzK⟩ : ↥K) ∈ Subgroup.center ↥K := by
          rw [Subgroup.mem_center_iff]
          intro w
          have hw := hconj w
          have hw' : (w : H) * z.1 = z.1 * w := by
            nth_rewrite 1 [← hw]
            group
          apply Subtype.ext
          simpa only [Subgroup.coe_mul] using hw'
        have hcenterA : (φ.symm (⟨z.1, hzK⟩ : ↥K) : alternatingGroup (Fin 8)) ∈
            Subgroup.center (alternatingGroup (Fin 8)) := by
          rw [Subgroup.mem_center_iff]
          intro b'
          apply φ.injective
          simp only [map_mul, MulEquiv.apply_symm_apply]
          exact Subgroup.mem_center_iff.mp hcenterK (φ b')
        have hm1 : (φ.symm (⟨z.1, hzK⟩ : ↥K) : alternatingGroup (Fin 8)) = 1 := by
          have h := hcenterA
          rw [alternatingGroup.center_eq_bot (α := Fin 8)
            (by rw [Nat.card_fin]; norm_num), Subgroup.mem_bot] at h
          exact h
        apply Subtype.ext
        have h := congrArg (fun m : alternatingGroup (Fin 8) => (φ m : H)) hm1
        simpa using h
      ·
        have hbc : b = c := hn.symm.trans hcn
        have hza : z.1 = a * c := by rw [← hab, hbc]
        exfalso
        apply hinner
        refine ⟨a⁻¹, K.inv_mem ha, ?_⟩
        intro y hy
        let yy : ↥K := ⟨y, hy⟩
        have hconj : z.1 * y * z.1⁻¹ = y := by
          have h := conjOnK_apply z yy
          rw [hg_one] at h
          simpa [yy] using h.symm
        rw [hza] at hconj
        have hcy : c * y * c⁻¹ = a⁻¹ * y * a := by
          have h := congrArg (fun t => a⁻¹ * t * a) hconj
          rw [show a⁻¹ * ((a * c) * y * (a * c)⁻¹) * a = c * y * c⁻¹ by group] at h
          exact h
        simpa using hcy
    have hinj : Function.Injective Ψ := by
      intro x y hxy
      have h1 : Ψ (x * y⁻¹) = 1 := by
        simp [map_mul, map_inv, hxy]
      have h2 : x * y⁻¹ = 1 := hker (x * y⁻¹) h1
      exact mul_inv_eq_one.mp h2
    have hσc_notMem : (Ψ ⟨c, hcL⟩ : Sym 8) ∉ alternatingGroup (Fin 8) := by
      intro hmem
      apply hinner
      let σc : alternatingGroup (Fin 8) := ⟨(Ψ ⟨c, hcL⟩ : Sym 8), hmem⟩
      have hE1 : E (Ψ ⟨c, hcL⟩) =
          MulAut.conjNormal (H := alternatingGroup (Fin 8)) (σc : Sym 8) := rfl
      have hgg : (MulAut.congr φ)
            (MulAut.conjNormal (H := alternatingGroup (Fin 8)) (σc : Sym 8)) =
          g ⟨c, hcL⟩ := by
        rw [← hE1, hE_theta ⟨c, hcL⟩]
        change (MulAut.congr φ) ((MulAut.congr φ).symm (g ⟨c, hcL⟩)) = g ⟨c, hcL⟩
        exact MulEquiv.apply_symm_apply (MulAut.congr φ) (g ⟨c, hcL⟩)
      refine ⟨(φ σc : H), (φ σc).2, ?_⟩
      intro y hy
      let yy : ↥K := ⟨y, hy⟩
      have h := congrArg (fun (f : MulAut ↥K) => ((f yy : ↥K) : H)) hgg
      have hL : (((MulAut.congr φ)
            (MulAut.conjNormal (H := alternatingGroup (Fin 8)) (σc : Sym 8))) yy : H)
          = (φ σc : H) * y * (φ σc : H)⁻¹ := by
        rw [mulAut_congr_apply']
        have hconjA : MulAut.conjNormal (H := alternatingGroup (Fin 8)) (σc : Sym 8)
              (φ.symm yy) = σc * (φ.symm yy) * σc⁻¹ :=
          Subtype.ext (MulAut.conjNormal_apply (σc : Sym 8) (φ.symm yy))
        rw [hconjA]
        simp only [MulEquiv.map_mul, MulEquiv.map_inv, MulEquiv.apply_symm_apply]
        rfl
      have hR : ((g ⟨c, hcL⟩ yy : ↥K) : H) = c * y * c⁻¹ := by
        have h := conjOnK_apply ⟨c, hcL⟩ yy
        simpa [yy] using h
      rw [hL, hR] at h
      exact h.symm
    have hsurj : Function.Surjective Ψ := by
      intro σ
      by_cases hσ : Equiv.Perm.sign σ = 1
      · have hmem : σ ∈ alternatingGroup (Fin 8) := Equiv.Perm.mem_alternatingGroup.mpr hσ
        let x : L := ⟨(φ ⟨σ, hmem⟩).1, hKL (φ ⟨σ, hmem⟩).2⟩
        refine ⟨x, ?_⟩
        have hxK : x.1 ∈ K := (φ ⟨σ, hmem⟩).2
        have hxval : (φ.symm (⟨x.1, hxK⟩ : ↥K) : Sym 8) = σ := by
          have h1 : (⟨x.1, hxK⟩ : ↥K) = φ ⟨σ, hmem⟩ := Subtype.ext rfl
          rw [h1]
          simp
        rw [hPsi_K x hxK, hxval]
      · have hσ' : Equiv.Perm.sign σ = -1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
          · exact absurd h1 hσ
          · exact h1
        have hσc'_ne : Equiv.Perm.sign (Ψ ⟨c, hcL⟩) ≠ 1 := by
          intro h1
          exact hσc_notMem (Equiv.Perm.mem_alternatingGroup.mpr h1)
        have hσc' : Equiv.Perm.sign (Ψ ⟨c, hcL⟩) = -1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign (Ψ ⟨c, hcL⟩)) with h1 | h1
          · exact absurd h1 hσc'_ne
          · exact h1
        have hτmem : σ * (Ψ ⟨c, hcL⟩)⁻¹ ∈ alternatingGroup (Fin 8) := by
          rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hσ', hσc',
            Int.units_inv_eq_self, Int.units_mul_self]
        let x : L := ⟨(φ ⟨σ * (Ψ ⟨c, hcL⟩)⁻¹, hτmem⟩).1,
          hKL (φ ⟨σ * (Ψ ⟨c, hcL⟩)⁻¹, hτmem⟩).2⟩
        refine ⟨x * ⟨c, hcL⟩, ?_⟩
        have hxK : x.1 ∈ K := (φ ⟨σ * (Ψ ⟨c, hcL⟩)⁻¹, hτmem⟩).2
        have hxval : (φ.symm (⟨x.1, hxK⟩ : ↥K) : Sym 8) = σ * (Ψ ⟨c, hcL⟩)⁻¹ := by
          have h1 : (⟨x.1, hxK⟩ : ↥K) = φ ⟨σ * (Ψ ⟨c, hcL⟩)⁻¹, hτmem⟩ := Subtype.ext rfl
          rw [h1]
          simp
        rw [map_mul, hPsi_K x hxK, hxval]
        group
    exact ⟨MulEquiv.ofBijective Ψ ⟨hinj, hsurj⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
