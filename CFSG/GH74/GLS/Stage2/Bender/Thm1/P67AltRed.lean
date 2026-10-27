module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67AltComb
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.SectionRank.Framework.Semisimple
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 Equiv Equiv.Perm
open scoped commutatorElement

section QuotAut

variable {J : Type} [Group J]

theorem map_center_eq (α : MulAut J) : (center J).map α.toMonoidHom = center J := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := Subgroup.mem_center_iff.1 hx (α.symm g)
    apply α.symm.injective
    simpa using h1
  · intro hy
    refine ⟨α.symm y, Subgroup.mem_center_iff.2 fun g => ?_, by simp⟩
    apply α.injective
    simpa using (Subgroup.mem_center_iff.1 hy (α g))

@[expose] noncomputable def quotAut : MulAut J →* MulAut (J ⧸ center J) where
  toFun α := QuotientGroup.congr (center J) (center J) α (map_center_eq α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem quotAut_mk (α : MulAut J) (x : J) :
    quotAut α (x : J ⧸ center J) = ((α x : J) : J ⧸ center J) := rfl

theorem eq_one_of_forall_mem_center (hJ : Group.IsPerfect J) (α : MulAut J)
    (h : ∀ x : J, x⁻¹ * α x ∈ center J) : α = 1 := by
  have hfix : ∀ x y : J, α ⁅x, y⁆ = ⁅x, y⁆ := by
    intro x y
    have hx : α x = x * (x⁻¹ * α x) := by group
    have hy : α y = y * (y⁻¹ * α y) := by group
    rw [map_commutatorElement, hx, hy]
    exact CFSG.SectionRank.commutatorElement_mul_mem_center x y (h x) (h y) ▸ rfl
  have hle : ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ ≤ α.toMonoidHom.eqLocus (MonoidHom.id J) := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    exact hfix x y
  have htop : ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ = ⊤ := by
    have := hJ.commutator_eq_top
    rwa [_root_.commutator_def] at this
  rw [htop] at hle
  ext x
  have : x ∈ α.toMonoidHom.eqLocus (MonoidHom.id J) := hle (Subgroup.mem_top x)
  exact this

end QuotAut

section Transfer

variable {N : Type} [Group N] (J : Subgroup N)

@[expose] noncomputable def altPerm {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (θ : ↥J ⧸ center ↥J ≃* alternatingGroup (Fin n)) :
    ↥(normalizer (J : Set N)) →* Perm (Fin n) :=
  (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6)).symm.toMonoidHom.comp
    ((MulAut.congr θ).toMonoidHom.comp ((quotAut (J := ↥J)).comp J.normalizerMonoidHom))

variable {J}

theorem conjNormal_altPerm {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (θ : ↥J ⧸ center ↥J ≃* alternatingGroup (Fin n)) (g : ↥(normalizer (J : Set N))) :
    (MulAut.conjNormal (altPerm J hn5 hn6 θ g) : MulAut (alternatingGroup (Fin n))) =
      MulAut.congr θ (quotAut (J.normalizerMonoidHom g)) := by
  have := (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6)).apply_symm_apply
    (MulAut.congr θ (quotAut (J.normalizerMonoidHom g)))
  exact this

theorem altPerm_inner {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (θ : ↥J ⧸ center ↥J ≃* alternatingGroup (Fin n)) (j : ↥J)
    (hj : (j : N) ∈ normalizer (J : Set N)) :
    altPerm J hn5 hn6 θ ⟨j, hj⟩ = ((θ (j : ↥J ⧸ center ↥J) : alternatingGroup (Fin n)) : Perm (Fin n)) := by
  have hinj := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6).1
  apply hinj
  rw [conjNormal_altPerm]
  refine MulEquiv.ext fun a => ?_
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (θ.symm a)
  have ha : a = θ (x : ↥J ⧸ center ↥J) := by rw [hx]; simp
  rw [ha]
  apply Subtype.ext
  have hρ : (J.normalizerMonoidHom ⟨(j : N), hj⟩ x : ↥J) = j * x * j⁻¹ :=
    Subtype.ext (by simp [Subgroup.normalizerMonoidHom_apply_apply_coe])
  have hL : ((MulAut.congr θ) (quotAut (J.normalizerMonoidHom ⟨(j : N), hj⟩))) (θ (x : ↥J ⧸ center ↥J)) =
      θ (j : ↥J ⧸ center ↥J) * θ (x : ↥J ⧸ center ↥J) * (θ (j : ↥J ⧸ center ↥J))⁻¹ := by
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [quotAut_mk, hρ]
    simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hL]
  simp [MulAut.conjNormal_apply]

theorem altPerm_faithful {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6) (hJ : Group.IsPerfect ↥J)
    (θ : ↥J ⧸ center ↥J ≃* alternatingGroup (Fin n)) (g : ↥(normalizer (J : Set N)))
    (h : altPerm J hn5 hn6 θ g = 1) : ∀ x ∈ J, (g : N) * x * (g : N)⁻¹ = x := by
  have h1 : MulAut.congr θ (quotAut (J.normalizerMonoidHom g)) = 1 := by
    rw [← conjNormal_altPerm hn5 hn6 θ g, h, map_one]
  have h2 : quotAut (J.normalizerMonoidHom g) = 1 := by
    apply (MulAut.congr θ).injective
    rw [h1, map_one]
  have h3 : J.normalizerMonoidHom g = 1 := by
    apply eq_one_of_forall_mem_center hJ
    intro x
    have := congrArg (fun φ : MulAut (↥J ⧸ center ↥J) => φ (x : ↥J ⧸ center ↥J)) h2
    simp only [quotAut_mk, MulAut.one_apply] at this
    exact QuotientGroup.eq.1 this.symm
  intro x hx
  have := congrArg (fun φ : MulAut ↥J => ((φ ⟨x, hx⟩ : ↥J) : N)) h3
  simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using this

end Transfer

section Main

theorem cf67_alt {N : Type} [Group N] (J : Subgroup N) (hJ : IsComponent J)
    {n : ℕ} (hn7 : 7 ≤ n) (hn11 : n ≤ 11) (θ : ↥J ⧸ center ↥J ≃* alternatingGroup (Fin n))
    (r : ℕ) (hr : r.Prime) (hr2 : Odd r) (V Z : Subgroup N)
    (hVe : IsElementaryAbelian r ↥V) (hVc : Nat.card ↥V = r ^ 2)
    (hZodd : Odd (Nat.card ↥Z)) (hZcop : Nat.Coprime (Nat.card ↥Z) r)
    (hcomm : ∀ v ∈ V, ∀ w ∈ Z, v * w = w * v)
    (hVn : V ≤ normalizer (J : Set N)) (hZn : Z ≤ normalizer (J : Set N))
    (hfaith : ∀ v ∈ V, v ≠ 1 → ¬ J ≤ centralizer ({v} : Set N))
    (hZnt : ¬ J ≤ centralizer (Z : Set N))
    (hP3 : ∀ v ∈ V, v ≠ 1 → ∀ c ∈ J, c ∈ centralizer ({v} : Set N) → c ∈ normalizer (Z : Set N)) :
    False := by
  classical
  have hperf : Group.IsPerfect ↥J := hJ.1.1
  have hn5 : 5 ≤ n := by omega
  have hn6 : n ≠ 6 := by omega
  let NJ : Subgroup N := normalizer (J : Set N)
  let Ψ : ↥NJ →* Perm (Fin n) := altPerm J hn5 hn6 θ
  have hker : ∀ g : ↥NJ, Ψ g = 1 → J ≤ centralizer ({(g : N)} : Set N) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.1 (altPerm_faithful hn5 hn6 hperf θ g hg x hx)).symm
  let V₀ : Subgroup ↥NJ := V.subgroupOf NJ
  let Z₀ : Subgroup ↥NJ := Z.subgroupOf NJ
  let ΨV : ↥V₀ →* Perm (Fin n) := Ψ.comp V₀.subtype
  let ΨZ : ↥Z₀ →* Perm (Fin n) := Ψ.comp Z₀.subtype
  have hV₀ : ∀ a : ↥V₀, ((a : ↥NJ) : N) ∈ V := fun a => a.2
  have hZ₀ : ∀ a : ↥Z₀, ((a : ↥NJ) : N) ∈ Z := fun a => a.2
  have hΨV_inj : Function.Injective ΨV := by
    rw [injective_iff_map_eq_one]
    intro a ha
    by_contra hne
    have h1 : ((a : ↥NJ) : N) ≠ 1 := fun h => hne (Subtype.ext (Subtype.ext h))
    exact hfaith _ (hV₀ a) h1 (hker a ha)
  let V₁ : Subgroup (Perm (Fin n)) := ΨV.range
  let Z₁ : Subgroup (Perm (Fin n)) := ΨZ.range
  have : IsElementaryAbelian r ↥V := hVe
  have hVcomm₀ : ∀ a b : ↥V₀, a * b = b * a := by
    intro a b
    have h := congrArg Subtype.val (mul_comm' (⟨(a : ↥NJ), hV₀ a⟩ : ↥V) ⟨(b : ↥NJ), hV₀ b⟩)
    exact Subtype.ext (Subtype.ext h)
  have hVpow₀ : ∀ a : ↥V₀, a ^ r = 1 := by
    intro a
    have h := elemPow_eq_one_of_isElementaryAbelian (p := r) (A := V) ((a : ↥NJ) : N) (hV₀ a)
    exact Subtype.ext (Subtype.ext (by simpa using h))
  have hV₁comm : ∀ a ∈ V₁, ∀ b ∈ V₁, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, hVcomm₀ a b]
  have hV₁pow : ∀ a ∈ V₁, a ^ r = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, hVpow₀ a, map_one]
  have hV₁card : Nat.card ↥V₁ = r ^ 2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hΨV_inj).toEquiv, ← hVc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVn).toEquiv
  have hZ₁ne : Z₁ ≠ ⊥ := by
    intro hbot
    apply hZnt
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 : ΨZ ⟨⟨w, hZn hw⟩, hw⟩ = 1 := by
      have : ΨZ ⟨⟨w, hZn hw⟩, hw⟩ ∈ Z₁ := ⟨_, rfl⟩
      rw [hbot] at this
      exact this
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hker ⟨w, hZn hw⟩ h1 hx)).symm
  have hZ₁card : Nat.card ↥Z₁ ∣ Nat.card ↥Z := by
    have h := Subgroup.card_range_dvd ΨZ
    rwa [show Nat.card ↥Z₀ = Nat.card ↥Z from Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZn).toEquiv] at h
  have hZ₁odd : Odd (Nat.card ↥Z₁) := Odd.of_dvd_nat hZodd hZ₁card
  have hZ₁cop : Nat.Coprime (Nat.card ↥Z₁) r := Nat.Coprime.coprime_dvd_left hZ₁card hZcop
  have hcomm₁ : ∀ v ∈ V₁, ∀ w ∈ Z₁, v * w = w * v := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    show Ψ (a : ↥NJ) * Ψ (b : ↥NJ) = Ψ (b : ↥NJ) * Ψ (a : ↥NJ)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm _ (hV₀ a) _ (hZ₀ b))
  have hxN : ∀ x : ↥J, (x : N) ∈ normalizer (J : Set N) := fun x => Subgroup.le_normalizer x.2
  have hlift : ∀ σ : Perm (Fin n), Perm.sign σ = 1 → ∃ x : ↥J, Ψ ⟨(x : N), hxN x⟩ = σ := by
    intro σ hσ
    let a : ↥(alternatingGroup (Fin n)) := ⟨σ, Equiv.Perm.mem_alternatingGroup.2 hσ⟩
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (θ.symm a)
    refine ⟨x, ?_⟩
    have h1 : θ (x : ↥J ⧸ center ↥J) = a := by rw [hx]; exact θ.apply_symm_apply a
    show altPerm J hn5 hn6 θ ⟨(x : N), hxN x⟩ = σ
    rw [altPerm_inner hn5 hn6 θ x (hxN x), h1]
  have hnorm : ∀ E : ↥NJ, (E : N) ∈ normalizer (Z : Set N) →
      Ψ E ∈ normalizer (Z₁ : Set (Perm (Fin n))) := by
    have key : ∀ E : ↥NJ, (E : N) ∈ normalizer (Z : Set N) → ∀ h ∈ Z₁, Ψ E * h * (Ψ E)⁻¹ ∈ Z₁ := by
      intro E hE h hh
      obtain ⟨w₀, rfl⟩ := hh
      have h1 : (E * (w₀ : ↥NJ) * E⁻¹ : ↥NJ) ∈ Z₀ := by
        show ((E * (w₀ : ↥NJ) * E⁻¹ : ↥NJ) : N) ∈ Z
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact (Subgroup.mem_normalizer_iff.1 hE _).1 (hZ₀ w₀)
      exact ⟨⟨_, h1⟩, by simp [ΨZ, map_mul, map_inv]⟩
    intro E hE
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => key E hE h hh, fun hh => ?_⟩
    have hE' : ((E⁻¹ : ↥NJ) : N) ∈ normalizer (Z : Set N) := by
      have := (normalizer (Z : Set N)).inv_mem hE
      simpa using this
    have := key E⁻¹ hE' _ hh
    simpa [map_inv, mul_assoc] using this
  have hP3₁ : ∀ v ∈ V₁, v ≠ 1 → ∀ σ τ : Perm (Fin n), Perm.sign σ = 1 → Perm.sign τ = 1 →
      σ * v = v * σ → τ * v = v * τ → σ * τ * σ⁻¹ * τ⁻¹ ∈ normalizer (Z₁ : Set (Perm (Fin n))) := by
    rintro _ ⟨a₀, rfl⟩ hv1 σ τ hσ hτ hσv hτv
    set v₀ : ↥NJ := (a₀ : ↥NJ) with hv₀
    have hv₀V : (v₀ : N) ∈ V := hV₀ a₀
    have hv₀1 : (v₀ : N) ≠ 1 := by
      intro h
      apply hv1
      have : v₀ = 1 := Subtype.ext h
      show Ψ v₀ = 1
      rw [this, map_one]
    obtain ⟨x, hx⟩ := hlift σ hσ
    obtain ⟨y, hy⟩ := hlift τ hτ
    have hcen : ∀ (x : ↥J) (σ : Perm (Fin n)), Ψ ⟨(x : N), hxN x⟩ = σ → σ * Ψ v₀ = Ψ v₀ * σ →
        x⁻¹ * J.normalizerMonoidHom v₀ x ∈ center ↥J := by
      intro x σ hxσ hcm
      have hspec := conjNormal_altPerm hn5 hn6 θ v₀
      have hxa : Ψ ⟨(x : N), hxN x⟩ = ((θ (x : ↥J ⧸ center ↥J) : alternatingGroup (Fin n)) : Perm (Fin n)) :=
        altPerm_inner hn5 hn6 θ x (hxN x)
      have h1 := congrArg (fun φ : MulAut (alternatingGroup (Fin n)) => φ (θ (x : ↥J ⧸ center ↥J))) hspec
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, quotAut_mk] at h1
      have h2 : (MulAut.conjNormal (Ψ v₀) : MulAut (alternatingGroup (Fin n))) (θ (x : ↥J ⧸ center ↥J)) =
          θ (x : ↥J ⧸ center ↥J) := by
        apply Subtype.ext
        rw [MulAut.conjNormal_apply, ← hxa, hxσ]
        rw [mul_inv_eq_iff_eq_mul]
        exact hcm.symm
      have h3 : θ (((J.normalizerMonoidHom v₀ x : ↥J) : ↥J ⧸ center ↥J)) = θ (x : ↥J ⧸ center ↥J) := by
        rw [← h2]; exact h1.symm
      have h4 := θ.injective h3
      exact QuotientGroup.eq.1 h4.symm
    have hdx := hcen x σ hx (by simpa [v₀, ΨV] using hσv)
    have hdy := hcen y τ hy (by simpa [v₀, ΨV] using hτv)
    set ρ : MulAut ↥J := J.normalizerMonoidHom v₀ with hρ
    have hρx : ρ x = x * (x⁻¹ * ρ x) := by group
    have hρy : ρ y = y * (y⁻¹ * ρ y) := by group
    have hρc : ρ ⁅x, y⁆ = ⁅x, y⁆ := by
      rw [map_commutatorElement, hρx, hρy]
      exact CFSG.SectionRank.commutatorElement_mul_mem_center x y hdx hdy
    have hcv : ((⁅x, y⁆ : ↥J) : N) ∈ centralizer ({(v₀ : N)} : Set N) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.normalizerMonoidHom_apply_apply_coe J v₀ ⁅x, y⁆
      rw [← hρ, hρc] at h1
      exact (mul_inv_eq_iff_eq_mul.1 h1.symm).symm
    have hcn := hP3 (v₀ : N) hv₀V hv₀1 _ (⁅x, y⁆ : ↥J).2 hcv
    let X : ↥NJ := ⟨(x : N), hxN x⟩
    let Y : ↥NJ := ⟨(y : N), hxN y⟩
    have hC : (⁅X, Y⁆ : ↥NJ) = ⟨((⁅x, y⁆ : ↥J) : N), hxN _⟩ := by
      apply Subtype.ext
      simp [X, Y, commutatorElement_def]
    have hΨC : Ψ ⁅X, Y⁆ = σ * τ * σ⁻¹ * τ⁻¹ := by
      rw [map_commutatorElement, show Ψ X = σ from hx, show Ψ Y = τ from hy, commutatorElement_def]
    rw [← hΨC]
    exact hnorm _ (by rw [hC]; exact hcn)
  exact alt_comb hn11 hr hr2 V₁ Z₁ hV₁comm hV₁pow hV₁card hZ₁ne hZ₁odd hZ₁cop hcomm₁ hP3₁

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm1
