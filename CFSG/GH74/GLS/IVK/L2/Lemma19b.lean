module

public import CFSG.GH74.GLS.IVK.L2.Lemma19Aux
public import CFSG.GH74.GLS.IVK.L2.Lemma19Aut
public import CFSG.GH74.GLS.IVK.L2.Lemma19c

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup Matrix CFSG CFSG.GorensteinWalter CFSG.ABGDGroups CFSG.ABGLocalTools

section Kernel

variable {F : Type} [Field F] [Finite F] {H : Type} [Group H] {Khat : Subgroup H} [Khat.Normal]

theorem lam_center (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (φ : ↥Khat ≃* SpecialLinearGroup (Fin 2) F) {h : H} (hh : h ∈ center H) :
    lam hodd h3 φ h = 1 := by
  have hact : actHom φ h = 1 := by
    apply MulEquiv.ext
    intro b
    obtain ⟨y, rfl⟩ := φ.surjective b
    rw [actHom_apply, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have e := Subgroup.mem_center_iff.1 hh (y : H)
    calc h * y * h⁻¹ = (y * h) * h⁻¹ := by rw [e]
      _ = y := by group
  simp [lam, hact]

theorem mem_center_of_lam_eq_one (hC : centralizer (Khat : Set H) ≤ Khat)
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (φ : ↥Khat ≃* SpecialLinearGroup (Fin 2) F) {h : H} (hh : lam hodd h3 φ h = 1) :
    h ∈ center H := by
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  obtain ⟨z, hzK, hz1, hzz, hzu, hzc, hzcen⟩ := exists_z Khat hC φ h2
  have hinl : lam hodd h3 φ h = SemidirectProduct.inl
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F))
          (1 : SpecialLinearGroup (Fin 2) F))) := by
    rw [hh]; simp
  have hhK : h ∈ Khat := mem_of_lam_eq_inl hC hodd h3 φ h 1 hinl
  have hact : actHom φ h = 1 := by
    rw [actHom_eq_conj hodd h3 φ h 1 hinl, map_one]
  have hcomm : ∀ κ : ↥Khat, (κ : H) * h = h * κ := by
    intro κ
    have e1 := congrArg (fun a : MulAut (SpecialLinearGroup (Fin 2) F) => a (φ κ)) hact
    simp only [actHom_apply, MulAut.one_apply] at e1
    have e2 := congrArg Subtype.val (φ.injective e1)
    rw [MulAut.conjNormal_apply] at e2
    calc (κ : H) * h = (h * κ * h⁻¹) * h := by rw [e2]
      _ = h * κ := by group
  have hcent : φ ⟨h, hhK⟩ ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨κ, rfl⟩ := φ.surjective b
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hcomm κ
  have hsq : φ ⟨h, hhK⟩ ^ 2 = 1 := sq_eq_one_of_mem_center hcent
  have hhh : h * h = 1 := by
    have e : (⟨h, hhK⟩ : ↥Khat) ^ 2 = 1 := φ.injective (by rw [map_pow, hsq, map_one])
    have := congrArg Subtype.val e
    simpa [pow_two] using this
  rcases hzu h hhK hhh with h1 | h1
  · rw [h1]; exact Subgroup.one_mem _
  · rw [h1]; exact Subgroup.mem_center_iff.2 hzc

@[expose] noncomputable def lamBar (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (φ : ↥Khat ≃* SpecialLinearGroup (Fin 2) F) : (H ⧸ center H) →* PGammaL2 F :=
  QuotientGroup.lift (center H) (lam hodd h3 φ) (fun _ hh => lam_center hodd h3 φ hh)

theorem lamBar_mk (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (φ : ↥Khat ≃* SpecialLinearGroup (Fin 2) F) (h : H) :
    lamBar hodd h3 φ (QuotientGroup.mk' (center H) h) = lam hodd h3 φ h := rfl

theorem lamBar_injective (hC : centralizer (Khat : Set H) ≤ Khat) (hodd : Odd (Nat.card F))
    (h3 : 3 < Nat.card F) (φ : ↥Khat ≃* SpecialLinearGroup (Fin 2) F) :
    Function.Injective (lamBar hodd h3 φ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rw [MonoidHom.mem_ker, lamBar_mk] at hx
  have := mem_center_of_lam_eq_one hC hodd h3 φ hx
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff h).2 this

end Kernel

section OddOrder

theorem odd_orderOf_mul_of_commute {G : Type*} [Group G] {a b : G} (hab : Commute a b)
    (ha : Odd (orderOf a)) (hb : Odd (orderOf b)) : Odd (orderOf (a * b)) := by
  have h1 := hab.orderOf_mul_dvd_lcm
  have h2 : Nat.lcm (orderOf a) (orderOf b) ∣ orderOf a * orderOf b := Nat.lcm_dvd_mul _ _
  exact (ha.mul hb).of_dvd_nat (h1.trans h2)

theorem eq_one_of_odd_orderOf_pow_two {G : Type*} [Group G] {x : G} {k : ℕ} (hx : x ^ (2 ^ k) = 1)
    (ho : Odd (orderOf x)) : x = 1 := by
  have hd := orderOf_dvd_of_pow_eq_one hx
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  have hi0 : i = 0 := by
    by_contra hne
    rw [hi] at ho
    exact (Nat.not_even_iff_odd.2 ho) (Nat.even_pow.2 ⟨even_two, hne⟩)
  rw [hi0, pow_zero] at hi
  exact orderOf_eq_one_iff.1 hi

end OddOrder


section CasePGL

variable {F : Type} [Field F] [Finite F] {H : Type} [Group H] {Khat : Subgroup H} [Khat.Normal]

open CFSG.Semidihedral.SemilinearOuterQuotient (SquareClass pglDet)

theorem case_pgl (hC : centralizer (Khat : Set H) ≤ Khat) (hodd : Odd (Nat.card F))
    (h3 : 3 < Nat.card F) (φ : ↥Khat ≃* SpecialLinearGroup (Fin 2) F)
    (hex : ∃ h₁ : H, pGammaL2DetClass F (isOddPrimePower_card_of_odd hodd) (lam hodd h3 φ h₁) ≠ 1) :
    Nonempty (↥(oPrimeResidual 2 (H ⧸ center H)) ≃* PGL2 F) := by
  classical
  have hK := isOddPrimePower_card_of_odd hodd
  have : IsCyclic (F ≃+* F) := isCyclic_ringEquiv F
  have hodd_ord : ∀ h : H, Odd (orderOf (lam hodd h3 φ h).right) := by
    obtain ⟨h₁, hh₁⟩ := hex
    have h1odd : Odd (orderOf (lam hodd h3 φ h₁).right) := by
      by_contra hn
      exact hh₁ (sign_h hC hodd h3 φ h₁ (Nat.not_odd_iff_even.1 hn))
    intro h
    by_cases hd : pGammaL2DetClass F hK (lam hodd h3 φ h) = 1
    · have hdd : pGammaL2DetClass F hK (lam hodd h3 φ (h * h₁)) ≠ 1 := by
        rw [map_mul, map_mul, hd, one_mul]; exact hh₁
      have hodd' : Odd (orderOf (lam hodd h3 φ (h * h₁)).right) := by
        by_contra hn
        exact hdd (sign_h hC hodd h3 φ (h * h₁) (Nat.not_odd_iff_even.1 hn))
      have e : (lam hodd h3 φ h).right =
          (lam hodd h3 φ (h * h₁)).right * ((lam hodd h3 φ h₁).right)⁻¹ := by
        rw [map_mul, SemidirectProduct.mul_right]; group
      rw [e]
      refine odd_orderOf_mul_of_commute (ringEquiv_mul_comm _ _) hodd' ?_
      rw [orderOf_inv]; exact h1odd
    · by_contra hn
      exact hd (sign_h hC hodd h3 φ h (Nat.not_odd_iff_even.1 hn))
  have hlamC : ∀ g : PGL2 F, ∃ h : H, lam hodd h3 φ h = SemidirectProduct.inl g := by
    obtain ⟨h₁, hh₁⟩ := hex
    have hm : Odd (orderOf (lam hodd h3 φ h₁).right) := hodd_ord h₁
    obtain ⟨h₂, h2right, h2D⟩ : ∃ h₂ : H, (lam hodd h3 φ h₂).right = 1 ∧
        pGammaL2DetClass F hK (lam hodd h3 φ h₂) ≠ 1 := by
      refine ⟨h₁ ^ orderOf (lam hodd h3 φ h₁).right, ?_, ?_⟩
      · rw [map_pow, pGammaL2_pow_right]
        exact pow_orderOf_eq_one _
      · rw [map_pow, map_pow]
        have hsq := squareClass_sq (pGammaL2DetClass F hK (lam hodd h3 φ h₁))
        obtain ⟨k, hk⟩ := hm
        rw [hk, pow_succ, pow_mul, hsq, one_pow, one_mul]
        exact hh₁
    have h2inl : lam hodd h3 φ h₂ = SemidirectProduct.inl (lam hodd h3 φ h₂).left := by
      have := SemidirectProduct.inl_left_mul_inr_right (lam hodd h3 φ h₂)
      rw [h2right, map_one, mul_one] at this
      exact this.symm
    intro g
    by_cases hg : g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
    · obtain ⟨y, rfl⟩ := hg
      obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective _ y
      exact ⟨(φ.symm j : H), by rw [lam_coe, MulEquiv.apply_symm_apply]⟩
    · have hga : pglDet F g ≠ 1 := fun h => hg ((mem_range_toPGL_iff_pglDet g).2 h)
      have hgb : pglDet F (lam hodd h3 φ h₂).left ≠ 1 := by
        rw [← pGammaL2DetClass_apply hK]; exact h2D
      have heq : pglDet F g = pglDet F (lam hodd h3 φ h₂).left :=
        squareClass_eq_of_ne_one hK hga hgb
      have hmem : g * ((lam hodd h3 φ h₂).left)⁻¹ ∈
          (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
        rw [mem_range_toPGL_iff_pglDet, map_mul, map_inv, ← heq, mul_inv_cancel]
      obtain ⟨y, hy⟩ := hmem
      obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective _ y
      refine ⟨(φ.symm j : H) * h₂, ?_⟩
      rw [map_mul, lam_coe, MulEquiv.apply_symm_apply]
      conv_lhs => rw [h2inl]
      rw [hy, ← map_mul, inv_mul_cancel_right]
  obtain ⟨DH, hDH⟩ : ∃ DH : Subgroup H, DH = (SemidirectProduct.rightHom.comp (lam hodd h3 φ)).ker :=
    ⟨_, rfl⟩
  have hmemDH : ∀ h : H, h ∈ DH ↔ (lam hodd h3 φ h).right = 1 := by
    intro h
    rw [hDH, MonoidHom.mem_ker, MonoidHom.comp_apply, SemidirectProduct.rightHom_eq_right]
  have hΛDH : ∀ h ∈ DH, lam hodd h3 φ h = SemidirectProduct.inl (lam hodd h3 φ h).left := by
    intro h hh
    have := SemidirectProduct.inl_left_mul_inr_right (lam hodd h3 φ h)
    rw [(hmemDH h).1 hh, map_one, mul_one] at this
    exact this.symm
  have hE1 : oPrimeResidual 2 (H ⧸ center H) ≤ DH.map (QuotientGroup.mk' (center H)) := by
    unfold oPrimeResidual
    rw [Subgroup.closure_le]
    rintro y ⟨k, hk⟩
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ y
    refine ⟨h, ?_, rfl⟩
    have hc : h ^ (2 ^ k) ∈ center H := by
      have : (QuotientGroup.mk' (center H)) (h ^ (2 ^ k)) = 1 := by rw [map_pow]; exact hk
      exact (QuotientGroup.eq_one_iff _).1 this
    have hl : (lam hodd h3 φ h) ^ (2 ^ k) = 1 := by
      rw [← map_pow]; exact lam_center hodd h3 φ hc
    have hr : (lam hodd h3 φ h).right ^ (2 ^ k) = 1 := by
      have := congrArg SemidirectProduct.right hl
      rw [pGammaL2_pow_right] at this
      simpa using this
    exact (hmemDH h).2 (eq_one_of_odd_orderOf_pow_two hr (hodd_ord h))
  have hE2 : DH.map (QuotientGroup.mk' (center H)) ≤ oPrimeResidual 2 (H ⧸ center H) := by
    obtain ⟨Ō, hŌ⟩ : ∃ Ō : Subgroup H,
        Ō = (oPrimeResidual 2 (H ⧸ center H)).comap (QuotientGroup.mk' (center H)) := ⟨_, rfl⟩
    have hmemŌ : ∀ h : H, h ∈ Ō ↔ (QuotientGroup.mk' (center H)) h ∈ oPrimeResidual 2 (H ⧸ center H) := by
      intro h; rw [hŌ]; exact Iff.rfl
    have hcenterŌ : center H ≤ Ō := by
      intro c hc
      rw [hmemŌ, show (QuotientGroup.mk' (center H)) c = 1 from (QuotientGroup.eq_one_iff c).2 hc]
      exact Subgroup.one_mem _
    have hgen : ∀ g : PGL2 F, ∀ k : ℕ, g ^ (2 ^ k) = 1 →
        ∃ o ∈ Ō, lam hodd h3 φ o = SemidirectProduct.inl g := by
      intro g k hg
      obtain ⟨h, hh⟩ := hlamC g
      refine ⟨h, ?_, hh⟩
      rw [hmemŌ]
      refine mem_oPrimeResidual_of_pow (k := k) ?_
      have hc : h ^ (2 ^ k) ∈ center H := by
        apply mem_center_of_lam_eq_one hC hodd h3 φ
        rw [map_pow, hh, ← map_pow, hg, map_one]
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).2 hc
    have hall : ∀ g : PGL2 F, ∃ o ∈ Ō, lam hodd h3 φ o = SemidirectProduct.inl g := by
      have hle : oPrimeResidual 2 (PGL2 F) ≤
          (Ō.map (lam hodd h3 φ)).comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) := by
        unfold oPrimeResidual
        rw [Subgroup.closure_le]
        rintro g ⟨k, hk⟩
        obtain ⟨o, ho, hoΛ⟩ := hgen g k hk
        exact ⟨o, ho, hoΛ⟩
      intro g
      have hg : g ∈ oPrimeResidual 2 (PGL2 F) := by
        rw [oPrimeResidual_pgl2 (F := F) hodd h3]; exact Subgroup.mem_top g
      obtain ⟨o, ho, hoΛ⟩ := hle hg
      exact ⟨o, ho, hoΛ⟩
    rintro _ ⟨d, hd, rfl⟩
    have hdl := hΛDH d hd
    obtain ⟨o, ho, hoΛ⟩ := hall (lam hodd h3 φ d).left
    have hker : o⁻¹ * d ∈ center H := by
      apply mem_center_of_lam_eq_one hC hodd h3 φ
      rw [map_mul, map_inv, hoΛ, ← hdl, inv_mul_cancel]
    have hd' : d = o * (o⁻¹ * d) := by group
    have : d ∈ Ō := by
      rw [hd']
      exact Ō.mul_mem ho (hcenterŌ hker)
    exact (hmemŌ d).1 this
  have hE : oPrimeResidual 2 (H ⧸ center H) = DH.map (QuotientGroup.mk' (center H)) :=
    le_antisymm hE1 hE2
  have hΛDH_range : DH.map (lam hodd h3 φ) =
      (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range := by
    ext x
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨(lam hodd h3 φ d).left, (hΛDH d hd).symm⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨h, hh⟩ := hlamC g
      exact ⟨h, (hmemDH h).2 (by rw [hh]; simp), hh⟩
  have hinj := lamBar_injective hC hodd h3 φ
  have hmapO : (oPrimeResidual 2 (H ⧸ center H)).map (lamBar hodd h3 φ) =
      (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range := by
    rw [hE, Subgroup.map_map]
    have : (lamBar hodd h3 φ).comp (QuotientGroup.mk' (center H)) = lam hodd h3 φ := rfl
    rw [this, hΛDH_range]
  exact ⟨((oPrimeResidual 2 (H ⧸ center H)).equivMapOfInjective (lamBar hodd h3 φ) hinj).trans
    ((MulEquiv.subgroupCongr hmapO).trans
      (MonoidHom.ofInjective SemidirectProduct.inl_injective).symm)⟩

end CasePGL

section CaseField

variable {F : Type} [Field F] [Finite F] {H : Type} [Group H] {Khat : Subgroup H} [Khat.Normal]

@[expose] def kbarHom (Khat : Subgroup H) [Khat.Normal] :
    ↥Khat →* ↥(Khat.map (QuotientGroup.mk' (center H))) :=
  ((QuotientGroup.mk' (center H)).comp Khat.subtype).codRestrict _ (fun κ => ⟨κ, κ.2, rfl⟩)

theorem kbarHom_surjective (Khat : Subgroup H) [Khat.Normal] : Function.Surjective (kbarHom Khat) := by
  rintro ⟨_, κ, hκ, rfl⟩
  exact ⟨⟨κ, hκ⟩, rfl⟩

theorem exists_kbarEquiv (hC : centralizer (Khat : Set H) ≤ Khat) (hodd : Odd (Nat.card F))
    (φ : ↥Khat ≃* SpecialLinearGroup (Fin 2) F) :
    ∃ eP : ↥(Khat.map (QuotientGroup.mk' (center H))) ≃* PSL2 F,
      ∀ κ : ↥Khat, eP (kbarHom Khat κ) = QuotientGroup.mk' _ (φ κ) := by
  classical
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  obtain ⟨z, hzK, hz1, hzz, hzu, hzc, hzcen⟩ := exists_z Khat hC φ h2
  have hcen : ∀ κ : ↥Khat, (φ κ ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) ↔
      ((κ : H) ∈ center H) := by
    intro κ
    constructor
    · intro hc
      have hsq : φ κ ^ 2 = 1 := sq_eq_one_of_mem_center hc
      have e : κ ^ 2 = 1 := φ.injective (by rw [map_pow, hsq, map_one])
      have e' : (κ : H) * κ = 1 := by simpa [pow_two] using congrArg Subtype.val e
      rcases hzu κ κ.2 e' with h1 | h1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [h1]; exact Subgroup.mem_center_iff.2 hzc
    · intro hc
      rw [Subgroup.mem_center_iff]
      intro b
      obtain ⟨κ', rfl⟩ := φ.surjective b
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_center_iff.1 hc κ'
  let f : PSL2 F →* ↥(Khat.map (QuotientGroup.mk' (center H))) :=
    QuotientGroup.lift (Subgroup.center (SpecialLinearGroup (Fin 2) F))
      ((kbarHom Khat).comp φ.symm.toMonoidHom) (by
        intro c hc
        rw [MonoidHom.mem_ker]
        have hcc : ((φ.symm c : ↥Khat) : H) ∈ center H := by
          rw [← hcen]; simpa using hc
        apply Subtype.ext
        show QuotientGroup.mk' (center H) ((φ.symm c : ↥Khat) : H) = 1
        exact (QuotientGroup.eq_one_iff _).2 hcc)
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ x
    rw [MonoidHom.mem_ker] at hx
    have h1 := congrArg Subtype.val hx
    have h2' : (QuotientGroup.mk' (center H) ((φ.symm b : ↥Khat) : H)) = 1 := h1
    have h3' : ((φ.symm b : ↥Khat) : H) ∈ center H := (QuotientGroup.eq_one_iff _).1 h2'
    have h4 : φ (φ.symm b) ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := (hcen _).2 h3'
    rw [MulEquiv.apply_symm_apply] at h4
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff b).2 h4
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨κ, hκ⟩ := kbarHom_surjective Khat y
    refine ⟨QuotientGroup.mk' _ (φ κ), ?_⟩
    show (kbarHom Khat) (φ.symm (φ κ)) = y
    rw [MulEquiv.symm_apply_apply]; exact hκ
  refine ⟨(MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩).symm, fun κ => ?_⟩
  have : f (QuotientGroup.mk' _ (φ κ)) = kbarHom Khat κ := by
    show (kbarHom Khat) (φ.symm (φ κ)) = _
    rw [MulEquiv.symm_apply_apply]
  rw [← this]
  show (MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩).symm
    ((MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩) (QuotientGroup.mk' _ (φ κ))) = _
  exact MulEquiv.symm_apply_apply _ _

theorem case_field (hC : centralizer (Khat : Set H) ≤ Khat) (hodd : Odd (Nat.card F))
    (h3 : 3 < Nat.card F) (φ : ↥Khat ≃* SpecialLinearGroup (Fin 2) F)
    (hall : ∀ h : H, pGammaL2DetClass F (isOddPrimePower_card_of_odd hodd) (lam hodd h3 φ h) = 1) :
    ∃ Fb : Subgroup (H ⧸ center H),
      Khat.map (QuotientGroup.mk' (center H)) ⊔ Fb = ⊤ ∧
      ∀ x ∈ Fb, orderOf x = 2 →
        IsFAutL2 (MulAut.conjNormal x : MulAut ↥(Khat.map (QuotientGroup.mk' (center H)))) := by
  classical
  have hK := isOddPrimePower_card_of_odd hodd
  obtain ⟨eP, heP⟩ := exists_kbarEquiv hC hodd φ
  obtain ⟨FH, hFH⟩ : ∃ FH : Subgroup H, FH = (pGammaL2FieldRange F).comap (lam hodd h3 φ) :=
    ⟨_, rfl⟩
  have hmemFH : ∀ h : H, h ∈ FH ↔ lam hodd h3 φ h ∈ pGammaL2FieldRange F := by
    intro h; rw [hFH]; exact Iff.rfl
  refine ⟨FH.map (QuotientGroup.mk' (center H)), ?_, ?_⟩
  · rw [eq_top_iff]
    intro x _
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ x
    obtain ⟨y, hy⟩ := (left_mem_range_toPGL_iff hK (lam hodd h3 φ h)).2 (hall h)
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have hκ : lam hodd h3 φ ((φ.symm j : ↥Khat) : H) =
        SemidirectProduct.inl (lam hodd h3 φ h).left := by
      rw [lam_coe, MulEquiv.apply_symm_apply, hy]
    have hfld : ((φ.symm j : ↥Khat) : H)⁻¹ * h ∈ FH := by
      rw [hmemFH, map_mul, map_inv, hκ]
      exact ⟨(lam hodd h3 φ h).right,
        (inv_mul_eq_iff_eq_mul.2 (SemidirectProduct.inl_left_mul_inr_right (lam hodd h3 φ h)).symm).symm⟩
    have e : (QuotientGroup.mk' (center H)) h = (QuotientGroup.mk' (center H))
        ((φ.symm j : ↥Khat) : H) * (QuotientGroup.mk' (center H))
          (((φ.symm j : ↥Khat) : H)⁻¹ * h) := by
      rw [← map_mul]; congr 1; group
    rw [e]
    exact Subgroup.mul_mem_sup ⟨_, (φ.symm j).2, rfl⟩ ⟨_, hfld, rfl⟩
  · rintro x ⟨f, hf, rfl⟩ _
    obtain ⟨σ, hσ⟩ := (hmemFH f).1 hf
    refine ⟨F, inferInstance, inferInstance, eP.trans (L2.equivPSL F).symm, ⟨σ, ?_⟩⟩
    have htp : ∀ y, toPSL (eP.trans (L2.equivPSL F).symm) y = eP y := by
      intro y
      simp [toPSL]
    have hcore : ∀ y : ↥(Khat.map (QuotientGroup.mk' (center H))),
        eP (MulAut.conjNormal ((QuotientGroup.mk' (center H)) f) y) = psl2FieldAut F σ (eP y) := by
      intro y
      obtain ⟨κ, rfl⟩ := kbarHom_surjective Khat y
      have e1 : MulAut.conjNormal ((QuotientGroup.mk' (center H)) f) (kbarHom Khat κ) =
          kbarHom Khat (MulAut.conjNormal f κ) := by
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        show _ = (QuotientGroup.mk' (center H)) ((MulAut.conjNormal f κ : ↥Khat) : H)
        rw [MulAut.conjNormal_apply, map_mul, map_mul, map_inv]
        rfl
      rw [e1, heP, heP, ← actHom_apply, ← thetaEquiv_inr hodd h3 σ, hσ, theta_lam hodd h3 φ f]
      rfl
    show (MulAut.congr (toPSL (eP.trans (L2.equivPSL F).symm))).symm (psl2FieldAut F σ) = _
    rw [MulEquiv.symm_apply_eq]
    ext b
    obtain ⟨y, rfl⟩ := (toPSL (eP.trans (L2.equivPSL F).symm)).surjective b
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [htp, htp]
    exact (hcore y).symm

end CaseField

section Main19b

theorem ivk_1_9_b : IVK_1_9_b := by
  intro F _ _ hF H _ _ Khat _ hC hK
  obtain ⟨hKS⟩ := hK
  have hodd : Odd (Nat.card F) := hF.1
  have h3 : 3 < Nat.card F := hF.2
  let φ : ↥Khat ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    hKS.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  by_cases hex : ∃ h₁ : H,
      pGammaL2DetClass F (isOddPrimePower_card_of_odd hodd) (lam hodd h3 φ h₁) ≠ 1
  · exact Or.inl (case_pgl hC hodd h3 φ hex)
  · exact Or.inr (case_field hC hodd h3 φ (fun h => not_not.1 (fun hh => hex ⟨h, hh⟩)))

theorem ivk_1_9 : IVK_1_9 := IVK_1_9_of_parts ivk_1_9_a ivk_1_9_b ivk_1_9_c

end Main19b

end CFSG.GH74.GLS.IVK
