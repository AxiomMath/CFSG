module

public import CFSG.Quasithin.H13.L32NLem1442f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1442a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L1442

open CFSG.Quasithin.F6.L28Res

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx_F4
open CFSG.Quasithin.H13.L1442.Ctx_F4

variable {T L V V₂ : Subgroup G} {g a : G} {D : HatModelU (fsuU T V)}
  (C : Ctx_F4 G T L V V₂ g a D)
include C

theorem false_of_concl11_F4 (h12813 : Lemma12_8_13_F4)
    (h11 : G112Concl11 (D.img (l32nH T V))) : False := by
  classical
  have hB := C.g111.toG101Hyp
  have H := C.g111
  set Γ := D.img (l32nH T V) with hΓ
  set X := D.img (CFSG.conjugate (l32nW T V V₂) g) with hX
  have : Finite (D.V ≃ₗ[ZMod 2] D.V) :=
    Finite.of_injective (fun e => (e : D.V → D.V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  have h11' := h11
  obtain ⟨hd8, ⟨φ⟩⟩ := h11
  set N : Subgroup ↥Γ := genFittingFStar ↥Γ with hN
  have hNn : N.Normal := A7Mod.genFittingFStar_normal' ↥Γ

  have : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 3) = Fintype.card CFSG.Quasithin.GF8 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num)]
    rfl
  let ψ : ↥N ≃* G8 :=
    φ.trans ((CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 2)
      (FiniteField.ringEquivOfCardEq hcard)).trans slEquiv)
  have hNcard : Nat.card N = 504 := by rw [Nat.card_congr ψ.toEquiv, card_G8]

  have hZ : Subgroup.center ↥N = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : ψ z ∈ Subgroup.center G8 := Subgroup.mem_center_iff.mpr fun y => by
      obtain ⟨y', rfl⟩ := ψ.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y']
    have h2 : Subgroup.center G8 = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      have h3 : slEquiv.symm w ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
          CFSG.Quasithin.GF8) := Subgroup.mem_center_iff.mpr fun y => by
        obtain ⟨y', rfl⟩ := slEquiv.symm.surjective y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hw y']
      rw [sl_center_eq_bot, Subgroup.mem_bot] at h3
      rw [Subgroup.mem_bot]
      simpa using congrArg slEquiv h3
    rw [h2, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact ψ.injective (h1.trans (map_one ψ).symm)
  let cN : ↥Γ →* MulAut ↥N := MulAut.conjNormal
  have hc : Function.Injective cN := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have hγC : γ ∈ Subgroup.centralizer (N : Set ↥Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have h1 := congrArg (fun f : MulAut ↥N => ((f ⟨n, hn⟩ : ↥N) : ↥Γ)) hγ
      simp only [cN, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc n * γ = γ * n * γ⁻¹ * γ := by rw [h1]
        _ = γ * n := by group
    have hγN : γ ∈ N := CFSG.Adapters.generalized_fitting_self_centralizing ↥Γ hγC
    have hγZ : (⟨γ, hγN⟩ : ↥N) ∈ Subgroup.center ↥N := Subgroup.mem_center_iff.mpr fun n =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hγC n n.2)
    rw [hZ, Subgroup.mem_bot] at hγZ
    exact congrArg Subtype.val hγZ
  have hAut : Nat.card (MulAut ↥N) = 1512 := by
    rw [Nat.card_congr (MulAut.congr ψ).toEquiv, card_mulAut]
  have hdvdΓ : Nat.card ↥Γ ∣ 1512 := by
    have h1 := Subgroup.card_subgroup_dvd_card cN.range
    rwa [← Nat.card_congr (MonoidHom.ofInjective hc).toEquiv, hAut] at h1
  have hidx : N.index ∣ 3 := by
    have h1 := N.card_mul_index
    rw [hNcard] at h1
    obtain ⟨r, hr⟩ := hdvdΓ
    have h2 : 504 * N.index * r = 504 * 3 := by rw [h1]; linarith
    exact Dvd.intro r (by nlinarith)

  have hxN : ∀ x (hx : x ∈ X), (⟨x, C.X_le_F4 hx⟩ : ↥Γ) ∈ N := by
    intro x hx
    set q := QuotientGroup.mk' N (⟨x, C.X_le_F4 hx⟩ : ↥Γ) with hq
    have h2 : q ^ 2 = 1 := by
      rw [hq, ← map_pow, sq]
      have : (⟨x, C.X_le_F4 hx⟩ : ↥Γ) * ⟨x, C.X_le_F4 hx⟩ = 1 := Subtype.ext (hB.X_sq x hx)
      rw [this, map_one]
    have h3 : orderOf q ∣ N.index := by
      rw [Subgroup.index]
      exact orderOf_dvd_natCard q
    have h4 : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have h5 : orderOf q = 1 := by
      have := Nat.dvd_gcd h4 (h3.trans hidx)
      simpa using this
    rw [orderOf_eq_one_iff, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h5
    exact h5

  set χ₀ : G8 →* (D.V ≃ₗ[ZMod 2] D.V) :=
    Γ.subtype.comp (N.subtype.comp ψ.symm.toMonoidHom) with hχ₀
  have hχ₀inj : Function.Injective χ₀ :=
    Γ.subtype_injective.comp (N.subtype_injective.comp ψ.symm.injective)
  have hχ₀X : ∀ x ∈ X, ∃ f, χ₀ f = x := fun x hx =>
    ⟨ψ ⟨⟨x, C.X_le_F4 hx⟩, hxN x hx⟩, by simp [hχ₀]⟩
  have hNorm : ∀ γ ∈ Γ, ∀ f, ∃ f', γ * χ₀ f * γ⁻¹ = χ₀ f' := by
    intro γ hγ f
    have h1 : (⟨γ, hγ⟩ : ↥Γ) * (ψ.symm f : ↥Γ) * (⟨γ, hγ⟩ : ↥Γ)⁻¹ ∈ N :=
      hNn.conj_mem _ (ψ.symm f).2 _
    refine ⟨ψ ⟨_, h1⟩, ?_⟩
    simp [hχ₀]

  have hX8 : Nat.card X = 8 := by
    obtain ⟨k, hk⟩ := C.exists_card_X_F4
    have hlt := L14324.lt_of_concl11 C.X_le_F4 hk h11'
    have hlow := C.lower_F4
    rw [hd8] at hlow
    norm_num at hlow
    rw [hk] at hlt hlow ⊢
    have hk3 : 3 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using hlow)
    have hk4 : k < 4 := by
      by_contra h4
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 4 ≤ k by omega)
      omega
    rw [show k = 3 by omega]
    norm_num

  set X₈ := X.comap χ₀ with hX₈
  have hX₈c : Nat.card X₈ = 8 := by
    rw [← hX8, hX₈, ← Subgroup.card_map_of_injective hχ₀inj, Subgroup.map_comap_eq,
      inf_eq_right.mpr fun x hx => (hχ₀X x hx).imp fun f hf => hf]
  obtain ⟨g₈, hg₈⟩ := exists_conj_U hX₈c
  set χ : G8 →* (D.V ≃ₗ[ZMod 2] D.V) := χ₀.comp (MulAut.conj g₈⁻¹).toMonoidHom with hχ
  have hχinj : Function.Injective χ := hχ₀inj.comp (MulAut.conj g₈⁻¹).injective
  have hχapp : ∀ f, χ f = χ₀ (g₈⁻¹ * f * g₈⁻¹⁻¹) := fun f => rfl

  have hsurjU : ∀ t, ∃ x ∈ X₈, g₈ * x * g₈⁻¹ = uHom t := by
    have hinj : Function.Injective (fun x : X₈ => (⟨g₈ * x * g₈⁻¹, hg₈ x x.2⟩ : uHom.range)) := by
      intro x x' h
      have := congrArg Subtype.val h
      exact Subtype.ext (by simpa using this)
    have hUc : Nat.card uHom.range = 8 := by
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective uHom_injective,
        Subgroup.card_top, Nat.card_eq_fintype_card]
      rfl
    have hbij : Function.Bijective (fun x : X₈ => (⟨g₈ * x * g₈⁻¹, hg₈ x x.2⟩ : uHom.range)) :=
      (Function.Injective.bijective_of_nat_card_le hinj (by rw [hUc, hX₈c]))
    intro t
    obtain ⟨x, hx⟩ := hbij.2 ⟨uHom t, t, rfl⟩
    exact ⟨x, x.2, congrArg Subtype.val hx⟩
  have hXU : ∀ t, χ (uHom t) ∈ X := by
    intro t
    obtain ⟨x, hx, hxe⟩ := hsurjU t
    rw [hχapp, ← hxe, show g₈⁻¹ * (g₈ * x * g₈⁻¹) * g₈⁻¹⁻¹ = x by group]
    exact hx
  have hXχ : ∀ x ∈ X, ∃ t, χ (uHom t) = x := by
    intro x hx
    obtain ⟨f, rfl⟩ := hχ₀X x hx
    obtain ⟨t, ht⟩ := hg₈ f hx
    refine ⟨t, ?_⟩
    rw [hχapp, ht, show g₈⁻¹ * (g₈ * f * g₈⁻¹) * g₈⁻¹⁻¹ = f by group]

  obtain ⟨_, S⟩ := C.base.set14_F4
  have hV₂ := C.base.plane
  have hV₂4 : Nat.card V₂ = 4 := hV₂.1.2.1
  have hlt2 : V₂ < V := lt_of_le_of_ne hV₂.1.1 fun he => by rw [he, S.card_V_F4] at hV₂4; omega
  obtain ⟨c, hcV, hc2⟩ := IsConcreteLE.exists_of_lt hlt2
  have haV₂ := C.aV₂
  have ha1 := C.a1
  have haV : a ∈ V := hV₂.1.1 haV₂
  obtain ⟨z, -, -, hz, hz1, -⟩ := S.exists_basis_F4
  have hzV₂ : z ∈ V₂ := hV₂.2 hz
  obtain ⟨l, -, -, hlz, hla, hlc⟩ := S.exists_rot_F4 (Subgroup.mem_inf.mp hz).1 haV hcV
    (fun he => ha1 (by rw [he]; exact one_mem _)) (fun he => hc2 (by rw [he]; exact one_mem _))
    (fun he => ha1 (by rw [he]; exact hz)) (fun he => hc2 (by rw [he]; exact hzV₂))
    (fun he => hc2 (by rw [← he]; exact haV₂))
    (fun he => hc2 (by rw [he]; exact V₂.mul_mem hzV₂ haV₂))
  have hlH : l ∈ l32nH T V := S.mem_g1_F4 hz hz1 hlz
  set y : D.V ≃ₗ[ZMod 2] D.V := D.ρ ⟨l, CFSG.Quasithin.H13.L1442.Ctx.H_N hlH⟩ with hy
  have hyΓ : y ∈ Γ := L128A.HatU.rho_mem_img D hlH (CFSG.Quasithin.H13.L1442.Ctx.H_N hlH)
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hya : y (D.π a) = D.π c := by
    rw [hy, D.ρ_π _ a (hVU haV)]
    exact congrArg D.π hla
  have hyc : y (D.π c) = D.π a + D.π c := by
    rw [hy, D.ρ_π _ c (hVU hcV)]
    rw [show l * c * l⁻¹ = a * c from hlc, D.π_mul a (hVU haV) c (hVU hcV)]

  have hcE : c ∈ l32nE T V V₂ g :=
    (h12813 G T L V 3 (fsuV1 T V) V₂ C.base.s1282 g C.base.gP C.base.gH).1 hcV
  have hcÊ : D.π c ∈ D.hat (l32nE T V V₂ g) := L128A.HatU.π_mem_hat D hcE (hVU hcV)
  have hπc0 : D.π c ≠ 0 := by
    rw [Ne, L128A.HatU.π_eq_zero_iff D (hVU hcV), C.base.zU]
    exact fun h => hc2 (hV₂.2 h)
  have hπca : D.π c ≠ D.π a := by
    intro he
    have h1 : D.π (a⁻¹ * c) = 0 := by
      rw [D.π_mul _ (hVU (V.inv_mem haV)) _ (hVU hcV), L128A.HatU.π_inv D (hVU haV), he,
        neg_add_cancel]
    rw [L128A.HatU.π_eq_zero_iff D (hVU (V.mul_mem (V.inv_mem haV) hcV)), C.base.zU] at h1
    apply hc2
    have : c = a * (a⁻¹ * c) := by group
    rw [this]
    exact V₂.mul_mem haV₂ (hV₂.2 h1)
  have hXc : ∀ x ∈ X, x (D.π c) = D.π c ∨ x (D.π c) = D.π c + D.π a := by
    intro x hx
    obtain ⟨f, -, hf⟩ := H.transvection x hx
    have h1 := hf ⟨D.π c, hcÊ⟩
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (f ⟨D.π c, hcÊ⟩) with h | h
    · left
      rw [h, zero_smul, add_zero] at h1
      exact h1
    · right
      rw [h, one_smul] at h1
      exact h1
  have hx₀ : ∃ x ∈ X, x (D.π c) = D.π c + D.π a := by
    have hspan : (⟨D.π c, hcÊ⟩ : D.hat (l32nE T V V₂ g)) ∉
        (ZMod 2) ∙ (⟨D.π a, H.mem_W⟩ : D.hat (l32nE T V V₂ g)) := by
      intro hmem
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hmem
      have hr' : r • D.π a = D.π c := by
        have := congrArg Subtype.val hr
        simpa using this
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) r with rfl | rfl
      · exact hπc0 (by rw [← hr', zero_smul])
      · exact hπca (by rw [← hr', one_smul])
    obtain ⟨f, hf, hker⟩ := Submodule.exists_le_ker_of_notMem hspan
    have hfv : f ⟨D.π a, H.mem_W⟩ = 0 :=
      LinearMap.mem_ker.1 (hker (Submodule.mem_span_singleton_self _))
    obtain ⟨x, hxX, hx⟩ := H.transvection_full f hfv
    have h1 := hx ⟨D.π c, hcÊ⟩
    have hf1 : f ⟨D.π c, hcÊ⟩ = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ hf
    rw [hf1, one_smul] at h1
    exact ⟨x, hxX, h1⟩

  have hyN : ∀ f, ∃ f', y * χ f * y⁻¹ = χ f' := by
    intro f
    obtain ⟨f₁, hf₁⟩ := hNorm y hyΓ (g₈⁻¹ * f * g₈⁻¹⁻¹)
    refine ⟨g₈ * f₁ * g₈⁻¹, ?_⟩
    rw [hχapp, hχapp, hf₁, show g₈⁻¹ * (g₈ * f₁ * g₈⁻¹) * g₈⁻¹⁻¹ = f₁ by group]

  have hfix : (∀ f, χ f (D.π a) = D.π a) → False := by
    intro hall
    have hall₀ : ∀ f, χ₀ f (D.π a) = D.π a := fun f => by
      have := hall (g₈ * f * g₈⁻¹)
      rwa [hχapp, show g₈⁻¹ * (g₈ * f * g₈⁻¹) * g₈⁻¹⁻¹ = f by group] at this

    have horb : ∀ f, ∀ w ∈ MulAction.orbit Γ (D.π a), χ₀ f w = w := by
      rintro f _ ⟨γ, rfl⟩
      obtain ⟨f', hf'⟩ := hNorm (γ⁻¹ : ↥Γ) (γ⁻¹).2 f
      have h1 : (γ : D.V ≃ₗ[ZMod 2] D.V)⁻¹ * χ₀ f * γ = χ₀ f' := by simpa using hf'
      have h2 := hall₀ f'
      rw [← h1, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h2
      have h3 := congrArg (γ : D.V ≃ₗ[ZMod 2] D.V) h2
      rw [← LinearEquiv.mul_apply (γ : D.V ≃ₗ[ZMod 2] D.V), mul_inv_cancel] at h3
      exact h3
    have hone : ∀ f, χ₀ f = 1 := by
      intro f
      have hle : Submodule.span (ZMod 2) (MulAction.orbit Γ (D.π a)) ≤
          LinearMap.ker ((χ₀ f).toLinearMap - LinearMap.id) := by
        rw [Submodule.span_le]
        intro w hw
        simp [horb f w hw]
      rw [H.span_orbit] at hle
      ext w
      have := hle (Submodule.mem_top (x := w))
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe,
        LinearMap.id_apply, sub_eq_zero] at this
      simpa using this
    have h1 := hχ₀inj ((hone gb).trans (hone 1).symm)
    exact gen_facts_ab.2.2.1 h1
  exact core11 χ hχinj hXU hXχ hyN C.πa_ne_F4 (fun x hx => hB.X_fixes x hx) hXc hx₀ hya hyc hfix

end Ctx_F4

end L1442

end CFSG.Quasithin.H13
