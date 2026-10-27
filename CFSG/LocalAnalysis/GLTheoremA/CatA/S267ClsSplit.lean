module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsForm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt

variable {K : Type*} [Field K] {A : Type*} [CommGroup A] {p : ℕ}
variable {V : Type*} [AddCommGroup V] [Module K V] {σ : K →+* K}

section Block

variable (ρ : Representation K A V)

@[expose] noncomputable def blk (i₀ : Option (Hyperplane A p)) (g : V →ₗ[K] V) : V →ₗ[K] V :=
  LinearMap.id - ρ.asAlgebraHom (eps K A p i₀) + g ∘ₗ ρ.asAlgebraHom (eps K A p i₀)

theorem blk_apply (i₀ : Option (Hyperplane A p)) (g : V →ₗ[K] V) (v : V) :
    blk ρ i₀ g v = v - ρ.asAlgebraHom (eps K A p i₀) v + g (ρ.asAlgebraHom (eps K A p i₀) v) :=
  rfl

variable [Finite A] (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0)

include hp hA hpK

private theorem eps_eps (i : Option (Hyperplane A p)) (v : V) :
    ρ.asAlgebraHom (eps K A p i) (ρ.asAlgebraHom (eps K A p i) v) =
      ρ.asAlgebraHom (eps K A p i) v :=
  eps_apply_of_mem ρ hp hA hpK i ⟨v, rfl⟩

theorem eps_blk {i₀ : Option (Hyperplane A p)} {g : V →ₗ[K] V}
    (hg : ∀ v, ρ.asAlgebraHom (eps K A p i₀) (g v) = g (ρ.asAlgebraHom (eps K A p i₀) v))
    (v : V) :
    ρ.asAlgebraHom (eps K A p i₀) (blk ρ i₀ g v) = g (ρ.asAlgebraHom (eps K A p i₀) v) := by
  rw [blk_apply, map_add, map_sub, eps_eps ρ hp hA hpK, hg, eps_eps ρ hp hA hpK, sub_self,
    zero_add]

theorem blk_blk {i₀ : Option (Hyperplane A p)} (g : V →ₗ[K] V) {g' : V →ₗ[K] V}
    (hg' : ∀ v, ρ.asAlgebraHom (eps K A p i₀) (g' v) = g' (ρ.asAlgebraHom (eps K A p i₀) v))
    (v : V) : blk ρ i₀ g (blk ρ i₀ g' v) = blk ρ i₀ (g ∘ₗ g') v := by
  rw [blk_apply ρ i₀ g, eps_blk ρ hp hA hpK hg', blk_apply ρ i₀ g', blk_apply ρ i₀ (g ∘ₗ g'),
    LinearMap.comp_apply]
  abel

theorem blk_id (i₀ : Option (Hyperplane A p)) (v : V) : blk ρ i₀ LinearMap.id v = v := by
  rw [blk_apply, LinearMap.id_apply, sub_add_cancel]

theorem blk_apply_of_mem {i₀ : Option (Hyperplane A p)} (g : V →ₗ[K] V) {v : V}
    (hv : v ∈ weightFamily (p := p) ρ i₀) : blk ρ i₀ g v = g v := by
  rw [blk_apply, eps_apply_of_mem ρ hp hA hpK i₀ hv, sub_self, zero_add]

theorem blk_apply_of_mem_ne {i₀ j : Option (Hyperplane A p)} (hj : i₀ ≠ j) (g : V →ₗ[K] V)
    {v : V} (hv : v ∈ weightFamily (p := p) ρ j) : blk ρ i₀ g v = v := by
  rw [blk_apply, eps_apply_of_mem_ne ρ hp hA hpK hj hv, map_zero, sub_zero, add_zero]

variable (β : V →ₗ[K] V →ₛₗ[σ] K) (hρ : IsIsomRep β ρ)

include hρ in
private theorem cross_left (i : Option (Hyperplane A p)) (x y : V) :
    β (x - ρ.asAlgebraHom (eps K A p i) x) (ρ.asAlgebraHom (eps K A p i) y) = 0 := by
  rw [← eps_left β ρ hρ i, map_sub, eps_eps ρ hp hA hpK, sub_self, map_zero, LinearMap.zero_apply]

include hρ in
private theorem cross_right (i : Option (Hyperplane A p)) (x y : V) :
    β (ρ.asAlgebraHom (eps K A p i) x) (y - ρ.asAlgebraHom (eps K A p i) y) = 0 := by
  rw [eps_left β ρ hρ i, map_sub, eps_eps ρ hp hA hpK, sub_self, map_zero]

include hρ in
theorem blk_isometry {i₀ : Option (Hyperplane A p)} {g : V →ₗ[K] V}
    (hgβ : ∀ x y, β (g x) (g y) = β x y)
    (hg : ∀ v, ρ.asAlgebraHom (eps K A p i₀) (g v) = g (ρ.asAlgebraHom (eps K A p i₀) v))
    (x y : V) : β (blk ρ i₀ g x) (blk ρ i₀ g y) = β x y := by
  set π := ρ.asAlgebraHom (eps K A p i₀)
  have h1 : β (x - π x) (g (π y)) = 0 := by
    rw [← hg]; exact cross_left ρ hp hA hpK β hρ i₀ x (g y)
  have h2 : β (g (π x)) (y - π y) = 0 := by
    rw [← hg]; exact cross_right ρ hp hA hpK β hρ i₀ (g x) y
  have h3 : β (x - π x) (π y) = 0 := cross_left ρ hp hA hpK β hρ i₀ x y
  have h4 : β (π x) (y - π y) = 0 := cross_right ρ hp hA hpK β hρ i₀ x y
  have e1 : β (x - π x + g (π x)) (y - π y + g (π y)) = β (x - π x) (y - π y) + β (π x) (π y) := by
    simp only [map_add, LinearMap.add_apply, h1, h2, hgβ, add_zero, zero_add]
  have e2 : β (x - π x + π x) (y - π y + π y) = β (x - π x) (y - π y) + β (π x) (π y) := by
    simp only [map_add, LinearMap.add_apply, h3, h4, add_zero, zero_add]
  rw [sub_add_cancel, sub_add_cancel] at e2
  rw [blk_apply, blk_apply]
  exact e1.trans e2.symm

end Block

section Split

variable (β : V →ₗ[K] V →ₛₗ[σ] K) (ρ : Representation K A V) [Finite A]
variable {𝒮 : Set (V →+ V)}

theorem rho_rho (x y : A) (v : V) : ρ x (ρ y v) = ρ (x * y) v := by
  rw [map_mul, Module.End.mul_apply]

theorem rho_comp (x y : A) : ρ x ∘ₗ ρ y = ρ (x * y) := (map_mul ρ x y).symm

@[expose] noncomputable def rhoEquiv (a : A) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinear (ρ a) (ρ a⁻¹)
    (LinearMap.ext fun v => Representation.self_inv_apply ρ a v)
    (LinearMap.ext fun v => Representation.inv_self_apply ρ a v)

theorem exists_not_mem_hyperplane (hp : p.Prime) (H : Hyperplane A p) : ∃ x : A, x ∉ H.1 := by
  by_contra hcon
  push Not at hcon
  have htop : H.1 = ⊤ := (Subgroup.eq_top_iff' _).mpr hcon
  have h := H.2
  rw [htop, Subgroup.index_top] at h
  exact hp.ne_one h.symm

variable (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0)

include hp hA hpK

@[expose] noncomputable def blkEquiv (i₀ : Option (Hyperplane A p)) (x : A) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinear (blk ρ i₀ (ρ x)) (blk ρ i₀ (ρ x⁻¹))
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, blk_blk ρ hp hA hpK (ρ x)
          (fun w => (apply_asAlgebraHom_comm ρ _ x⁻¹ w).symm),
        rho_comp, mul_inv_cancel, map_one]
      exact blk_id ρ hp hA hpK i₀ v)
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, blk_blk ρ hp hA hpK (ρ x⁻¹)
          (fun w => (apply_asAlgebraHom_comm ρ _ x w).symm),
        rho_comp, inv_mul_cancel, map_one]
      exact blk_id ρ hp hA hpK i₀ v)

theorem blkEquiv_apply (i₀ : Option (Hyperplane A p)) (x : A) (v : V) :
    blkEquiv ρ hp hA hpK i₀ x v = blk ρ i₀ (ρ x) v :=
  rfl

theorem blkEquiv_pow_apply (i₀ : Option (Hyperplane A p)) (x : A) (n : ℕ) (v : V) :
    (blkEquiv ρ hp hA hpK i₀ x ^ n) v = blk ρ i₀ (ρ (x ^ n)) v := by
  induction n generalizing v with
  | zero =>
    rw [pow_zero, pow_zero, map_one]
    exact (blk_id ρ hp hA hpK i₀ v).symm
  | succ n ih =>
    rw [pow_succ, LinearEquiv.mul_apply, ih, blkEquiv_apply,
      blk_blk ρ hp hA hpK _ (fun w => (apply_asAlgebraHom_comm ρ _ x w).symm), pow_succ,
      map_mul]
    rfl

variable (hρ : IsIsomRep β ρ)

include hρ in
theorem exists_split (hmax : IsMaxElem β ρ p 𝒮) (h𝒮 : ∀ s ∈ 𝒮, ∀ a v, s (ρ a v) = ρ a (s v))
    (h𝒮W : ∀ s ∈ 𝒮, ∀ i, ∀ v ∈ weightFamily (p := p) ρ i, s v ∈ weightFamily (p := p) ρ i)
    (H : Hyperplane A p) (hH : weightSpace ρ H.1 ≠ ⊥) :
    ∃ a : A, a ∉ H.1 ∧ ∀ H' : Hyperplane A p, H' ≠ H → weightSpace ρ H'.1 ≠ ⊥ → a ∈ H'.1 := by
  obtain ⟨x, hx⟩ := exists_not_mem_hyperplane hp H
  have hcomm : ∀ v, ρ.asAlgebraHom (eps K A p (some H)) (ρ x v) =
      ρ x (ρ.asAlgebraHom (eps K A p (some H)) v) :=
    fun w => (apply_asAlgebraHom_comm ρ _ x w).symm
  obtain ⟨a, ha⟩ := hmax (blkEquiv ρ hp hA hpK (some H) x)
    (fun u w => blk_isometry ρ hp hA hpK β hρ (hρ x) hcomm u w)
    (fun b v => by
      change blk ρ (some H) (ρ x) (ρ b v) = ρ b (blk ρ (some H) (ρ x) v)
      rw [blk_apply, blk_apply, map_add, map_sub, ← apply_asAlgebraHom_comm ρ _ b v,
        rho_rho ρ x b, mul_comm x b, ← rho_rho ρ b x])
    (fun s hs v => by
      change blk ρ (some H) (ρ x) (s v) = s (blk ρ (some H) (ρ x) v)
      rw [blk_apply, blk_apply, map_add, map_sub,
        eps_comm_of_preserves ρ hp hA hpK s (h𝒮W s hs) (some H) v, h𝒮 s hs x])
    (fun v => by
      rw [blkEquiv_pow_apply, hA x, map_one]
      exact blk_id ρ hp hA hpK _ v)
  refine ⟨a, fun haH => ?_, fun H' hne hH' => ?_⟩
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH
    have h1 : ρ a v = v := apply_eq_of_mem_weightSpace ρ haH hv
    have h2 : blkEquiv ρ hp hA hpK (some H) x v = ρ x v := blk_apply_of_mem ρ hp hA hpK (ρ x) hv
    rw [ha v, h2] at h1
    exact hv0 (eq_zero_of_mem_weightSpace_of_fixed ρ hp hA hpK hx hv h1)
  · by_contra haH'
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH'
    have h1 : blkEquiv ρ hp hA hpK (some H) x v = v :=
      blk_apply_of_mem_ne ρ hp hA hpK (fun h => hne (Option.some_injective _ h).symm) (ρ x) hv
    rw [← ha v] at h1
    exact hv0 (eq_zero_of_mem_weightSpace_of_fixed ρ hp hA hpK haH' hv h1)

include hρ in
theorem index_biInf_eq (hmax : IsMaxElem β ρ p 𝒮)
    (h𝒮 : ∀ s ∈ 𝒮, ∀ a v, s (ρ a v) = ρ a (s v))
    (h𝒮W : ∀ s ∈ 𝒮, ∀ i, ∀ v ∈ weightFamily (p := p) ρ i, s v ∈ weightFamily (p := p) ρ i)
    (S : Finset (Hyperplane A p)) (hS : ∀ H ∈ S, weightSpace ρ H.1 ≠ ⊥) :
    (⨅ H ∈ S, H.1).index = p ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert H S hHS ih =>
    have hS' : ∀ H' ∈ S, weightSpace ρ H'.1 ≠ ⊥ := fun H' h => hS H' (Finset.mem_insert_of_mem h)
    obtain ⟨a, haH, ha⟩ := exists_split β ρ hp hA hpK hρ hmax h𝒮 h𝒮W H
      (hS H (Finset.mem_insert_self H S))
    have haN : a ∈ ⨅ H' ∈ S, H'.1 := by
      simp only [Subgroup.mem_iInf]
      intro H' hH'
      exact ha H' (fun h => hHS (h ▸ hH')) (hS' H' hH')
    have hrel : H.1.relIndex (⨅ H' ∈ S, H'.1) = p := by
      have hd := Subgroup.relIndex_dvd_index_of_normal (H := H.1) (K := ⨅ H' ∈ S, H'.1)
      rw [H.2] at hd
      rcases (Nat.dvd_prime hp).mp hd with h1 | h1
      · exact absurd (Subgroup.relIndex_eq_one.mp h1 haN) haH
      · exact h1
    rw [Finset.iInf_insert, ← Subgroup.relIndex_mul_index inf_le_right,
      Subgroup.inf_relIndex_right, hrel, ih hS', Finset.card_insert_of_notMem hHS, pow_succ,
      mul_comm]

include hρ in
theorem card_eq_pow_support (hmax : IsMaxElem β ρ p 𝒮)
    (h𝒮 : ∀ s ∈ 𝒮, ∀ a v, s (ρ a v) = ρ a (s v))
    (h𝒮W : ∀ s ∈ 𝒮, ∀ i, ∀ v ∈ weightFamily (p := p) ρ i, s v ∈ weightFamily (p := p) ρ i)
    (hinj : Function.Injective ρ) (T : Finset (Hyperplane A p))
    (hT : ∀ H : Hyperplane A p, H ∈ T ↔ weightSpace ρ H.1 ≠ ⊥) : Nat.card A = p ^ T.card := by
  have h1 := index_biInf_eq β ρ hp hA hpK hρ hmax h𝒮 h𝒮W T (fun H hH => (hT H).mp hH)
  rwa [iInf_eq_bot_of_faithful ρ hp hA hpK hinj hT, Subgroup.index_bot] at h1

private theorem apply_eq_of_fix_weightSpaces (g : V ≃ₗ[K] V)
    (hgW : ∀ H : Hyperplane A p, ∀ v ∈ weightSpace ρ H.1, g v = v) (v : V) :
    g v = g (ρ.asAlgebraHom (eps K A p none) v) + (v - ρ.asAlgebraHom (eps K A p none) v) := by
  classical
  haveI : Fintype (Hyperplane A p) := Fintype.ofFinite _
  have hsum := sum_eps_apply ρ hp hA hpK v
  rw [Fintype.sum_option] at hsum
  have hv : v - ρ.asAlgebraHom (eps K A p none) v =
      ∑ H : Hyperplane A p, ρ.asAlgebraHom (eps K A p (some H)) v := by
    rw [sub_eq_iff_eq_add, add_comm]
    exact hsum.symm
  have hrest : g (v - ρ.asAlgebraHom (eps K A p none) v) =
      v - ρ.asAlgebraHom (eps K A p none) v := by
    rw [hv, map_sum]
    exact Finset.sum_congr rfl fun H _ => hgW H _ ⟨v, rfl⟩
  calc g v = g (ρ.asAlgebraHom (eps K A p none) v + (v - ρ.asAlgebraHom (eps K A p none) v)) := by
        rw [add_sub_cancel]
    _ = _ := by rw [map_add, hrest]

include hρ in
theorem fixed_of_supported (hβ : β.SeparatingLeft) (hmax : IsMaxElem β ρ p 𝒮) (g : V ≃ₗ[K] V)
    (hg : ∀ x y, β (g x) (g y) = β x y) (hgp : ∀ v, (g ^ p) v = v)
    (hg𝒮 : ∀ s ∈ 𝒮, ∀ v, g (s v) = s (g v))
    (hgW : ∀ H : Hyperplane A p, ∀ v ∈ weightSpace ρ H.1, g v = v) : g = 1 := by
  classical
  haveI : Fintype (Hyperplane A p) := Fintype.ofFinite _
  have hdec := apply_eq_of_fix_weightSpaces ρ hp hA hpK g hgW
  have hfix : ∀ v, g (ρ.asAlgebraHom (eps K A p none) v) ∈ fixedSpace ρ ⊤ := by
    intro v
    rw [← weightFamily_none ρ hp hA hpK]
    have hu : ∀ H : Hyperplane A p,
        ρ.asAlgebraHom (eps K A p (some H)) (g (ρ.asAlgebraHom (eps K A p none) v)) = 0 := by
      intro H
      refine weightFamily_nondeg β ρ hρ hp hA hpK hβ (some H) ⟨_, rfl⟩ fun w hw => ?_
      rw [eps_left β ρ hρ, eps_apply_of_mem ρ hp hA hpK _ hw, ← hgW H w hw, hg]
      exact weightFamily_orthogonal β ρ hρ hp hA hpK (Option.some_ne_none H).symm ⟨v, rfl⟩ hw
    have hsum := sum_eps_apply ρ hp hA hpK (g (ρ.asAlgebraHom (eps K A p none) v))
    rw [Fintype.sum_option, Finset.sum_eq_zero fun H _ => hu H, add_zero] at hsum
    exact ⟨_, hsum⟩
  have hπ₀fix : ∀ (a : A) (v : V),
      ρ a (ρ.asAlgebraHom (eps K A p none) v) = ρ.asAlgebraHom (eps K A p none) v :=
    fun a v => apply_asAlgebraHom_eSub ρ (Subgroup.mem_top a) v
  have hgρ : ∀ (a : A) (v : V), g (ρ a v) = ρ a (g v) := by
    intro a v
    have hπ : ρ.asAlgebraHom (eps K A p none) (ρ a v) = ρ.asAlgebraHom (eps K A p none) v := by
      rw [← apply_asAlgebraHom_comm ρ _ a v, hπ₀fix]
    rw [hdec (ρ a v), hdec v, hπ, map_add, map_sub, hfix v a (Subgroup.mem_top a), hπ₀fix]
  obtain ⟨a, ha⟩ := hmax g hg hgρ hg𝒮 hgp
  ext v
  show g v = v
  rw [hdec v, ← ha, hπ₀fix, add_sub_cancel]

include hρ in
theorem eq_rho_of_supported (hmax : IsMaxElem β ρ p 𝒮) (H : Hyperplane A p) (g : V ≃ₗ[K] V)
    (hg : ∀ x y, β (g x) (g y) = β x y) (hgp : ∀ v, (g ^ p) v = v)
    (hgA : ∀ a v, g (ρ a v) = ρ a (g v)) (hg𝒮 : ∀ s ∈ 𝒮, ∀ v, g (s v) = s (g v))
    (hgW : ∀ i : Option (Hyperplane A p), i ≠ some H → ∀ v ∈ weightFamily (p := p) ρ i, g v = v) :
    ∃ a : A, (∀ v, ρ a v = g v) ∧
      ∀ H' : Hyperplane A p, H' ≠ H → weightSpace ρ H'.1 ≠ ⊥ → a ∈ H'.1 := by
  obtain ⟨a, ha⟩ := hmax g hg hgA hg𝒮 hgp
  refine ⟨a, ha, fun H' hne hH' => ?_⟩
  by_contra haH'
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH'
  have h1 : ρ a v = v := by
    rw [ha v]
    exact hgW (some H') (fun h => hne (Option.some_injective _ h)) v hv
  exact hv0 (eq_zero_of_mem_weightSpace_of_fixed ρ hp hA hpK haH' hv h1)

end Split

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
