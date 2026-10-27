module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5Inputs

public section

namespace CFSG.ComponentClassification.FooteLit.Aut5

open CFSG Subgroup CFSG.ComponentClassification.Foote5

variable {𝕊 𝕊' : Type} [Group 𝕊] [Group 𝕊'] (φ : 𝕊 ≃* 𝕊')

theorem congr_apply_apply (α : MulAut 𝕊) (x : 𝕊') :
    MulAut.congr φ α x = φ (α (φ.symm x)) := by
  simp [MulAut.congr_apply]

theorem congr_symm_apply_apply (α' : MulAut 𝕊') (x : 𝕊) :
    (MulAut.congr φ).symm α' x = φ.symm (α' (φ x)) := by
  apply φ.injective
  have h := congrArg (fun β : MulAut 𝕊' => β (φ x)) ((MulAut.congr φ).apply_symm_apply α')
  simp only [congr_apply_apply, MulEquiv.symm_apply_apply] at h
  rw [h, MulEquiv.apply_symm_apply]

theorem congr_conj (s : 𝕊) : MulAut.congr φ (MulAut.conj s) = MulAut.conj (φ s) := by
  ext x
  simp [MulAut.conj_apply]

theorem congr_symm_conj (s' : 𝕊') :
    (MulAut.congr φ).symm (MulAut.conj s') = MulAut.conj (φ.symm s') := by
  apply (MulAut.congr φ).injective
  rw [MulEquiv.apply_symm_apply, congr_conj, MulEquiv.apply_symm_apply]

theorem congr_mem_innAut5_iff (α : MulAut 𝕊) :
    MulAut.congr φ α ∈ innAut5 𝕊' ↔ α ∈ innAut5 𝕊 := by
  constructor
  · rintro ⟨s', hs'⟩
    refine ⟨φ.symm s', ?_⟩
    apply (MulAut.congr φ).injective
    rw [congr_conj, MulEquiv.apply_symm_apply]
    exact hs'
  · rintro ⟨s, rfl⟩
    exact ⟨φ s, (congr_conj φ s).symm⟩

theorem exists_sylow_pullback [Finite 𝕊'] (R' : Sylow 2 𝕊') :
    ∃ R : Sylow 2 𝕊, ∀ x : 𝕊, x ∈ (R : Subgroup 𝕊) ↔ φ x ∈ (R' : Subgroup 𝕊') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : Function.Surjective φ.symm.toMonoidHom := φ.symm.surjective
  refine ⟨R'.mapSurjective hsurj, fun x => ?_⟩
  rw [Sylow.coe_mapSurjective, mem_map_equiv, MulEquiv.symm_symm]

theorem nonempty_sylow_equiv [Finite 𝕊'] {R : Sylow 2 𝕊} {R' : Sylow 2 𝕊'}
    (hR : ∀ x : 𝕊, x ∈ (R : Subgroup 𝕊) ↔ φ x ∈ (R' : Subgroup 𝕊')) :
    Nonempty ((R' : Subgroup 𝕊') ≃* (R : Subgroup 𝕊)) := by
  have heq : (R' : Subgroup 𝕊').map φ.symm.toMonoidHom = R := by
    ext x
    rw [mem_map_equiv, MulEquiv.symm_symm, hR]
  exact ⟨(MulEquiv.subgroupMap φ.symm (R' : Subgroup 𝕊')).trans (MulEquiv.subgroupCongr heq)⟩

theorem map_eq_iff (α : MulAut 𝕊) (R : Subgroup 𝕊) :
    R.map α.toMonoidHom = R ↔ ∀ y : 𝕊, α.symm y ∈ R ↔ y ∈ R := by
  constructor
  · intro h y
    rw [← mem_map_equiv, h]
  · intro h
    ext y
    rw [mem_map_equiv, h]

variable [Finite 𝕊] [Finite 𝕊']

theorem foote5AutData_map {Lin : Subgroup (MulAut 𝕊)} (h : Foote5AutData 𝕊 Lin) :
    Foote5AutData 𝕊' (Lin.map (MulAut.congr φ).toMonoidHom) := by
  set Φ := MulAut.congr φ with hΦ
  have hinn : ∀ α' : MulAut 𝕊', α' ∈ innAut5 𝕊' ↔ Φ.symm α' ∈ innAut5 𝕊 := fun α' => by
    rw [← congr_mem_innAut5_iff φ, MulEquiv.apply_symm_apply]
  have hfix : ∀ (R : Sylow 2 𝕊) (R' : Sylow 2 𝕊'),
      (∀ x : 𝕊, x ∈ (R : Subgroup 𝕊) ↔ φ x ∈ (R' : Subgroup 𝕊')) → ∀ α' : MulAut 𝕊',
      (∀ r ∈ (R' : Subgroup 𝕊'), α' r = r) → ∀ r ∈ (R : Subgroup 𝕊), Φ.symm α' r = r :=
    fun R R' hR α' hα' r hr => by
      rw [congr_symm_apply_apply, hα' _ ((hR r).mp hr), MulEquiv.symm_apply_apply]
  refine
    { inn_le := ?_, normal := ?_, sq_mem := ?_, commutator_mem := ?_, conj_involution := ?_,
      centralizer_sylow := ?_, centralizer_sylow_lin := ?_, not_commute := ?_,
      conj_centralizer := ?_, pgl_fixed := ?_, field_inner := ?_, center_le := ?_,
      two_generated := ?_ }
  · rintro _ ⟨s', rfl⟩
    rw [mem_map_equiv, congr_symm_conj]
    exact h.inn_le ⟨_, rfl⟩
  · exact h.normal.map _ Φ.surjective
  · intro α' hα'
    rw [mem_map_equiv] at hα'
    rw [hinn, map_mul]
    exact h.sq_mem _ hα'
  · intro α' β'
    rw [hinn, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact h.commutator_mem _ _
  · intro x y hx hy
    obtain ⟨g, hg⟩ := h.conj_involution (φ.symm x) (φ.symm y)
      (by rw [MulEquiv.orderOf_eq]; exact hx) (by rw [MulEquiv.orderOf_eq]; exact hy)
    refine ⟨φ g, φ.symm.injective ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    exact hg
  · intro R' P' hP' hP'R'
    obtain ⟨R, hR⟩ := exists_sylow_pullback φ R'
    obtain ⟨h1, h2⟩ := h.centralizer_sylow R (P'.map Φ.symm.toMonoidHom) (hP'.map _)
      (by rintro _ ⟨α', hα', rfl⟩; exact hfix R R' hR α' (hP'R' α' hα'))
    refine ⟨fun α' hα' => Φ.symm.injective ?_, ?_⟩
    · rw [map_mul, map_one]
      exact h1 _ ⟨α', hα', rfl⟩
    · rwa [card_map_of_injective Φ.symm.injective] at h2
  · intro R' hna' α' hα' h2k hfix'
    obtain ⟨R, hR⟩ := exists_sylow_pullback φ R'
    obtain ⟨a', ha', b', hb', hab'⟩ := hna'
    obtain ⟨c, hc, hcZ, hcα⟩ := h.centralizer_sylow_lin R
      ⟨φ.symm a', (hR _).mpr (by rwa [MulEquiv.apply_symm_apply]), φ.symm b',
        (hR _).mpr (by rwa [MulEquiv.apply_symm_apply]),
        fun hab => hab' (by simpa using congrArg φ hab)⟩
      (Φ.symm α') (mem_map_equiv.mp hα')
      (by obtain ⟨k, hk⟩ := h2k; exact ⟨k, by rw [← map_pow, hk, map_one]⟩)
      (hfix R R' hR α' hfix')
    refine ⟨φ c, (hR c).mp hc, fun r' hr' => ?_, ?_⟩
    · have h1 := hcZ (φ.symm r') ((hR _).mpr (by rwa [MulEquiv.apply_symm_apply]))
      simpa using congrArg φ h1
    · rw [← congr_conj, ← hcα, MulEquiv.apply_symm_apply]
  · intro α' β' hα' hα'I hα'2 hβ' hβ'2 hcomm
    refine h.not_commute (Φ.symm α') (Φ.symm β') (mem_map_equiv.mp hα')
      (fun hI => hα'I ((hinn α').mpr hI)) (by rw [← map_mul, hα'2, map_one])
      (fun hL => hβ' (mem_map_equiv.mpr hL)) (by rw [← map_mul, hβ'2, map_one]) ?_
    rw [← map_mul, ← map_mul, hcomm]
  · intro R' β' hβ' hβ'2
    obtain ⟨R, hR⟩ := exists_sylow_pullback φ R'
    obtain ⟨g, hg⟩ := h.conj_centralizer R (Φ.symm β') (fun hL => hβ' (mem_map_equiv.mpr hL))
      (by rw [← map_mul, hβ'2, map_one])
    refine ⟨φ g, fun r' hr' => ?_⟩
    have hγ : MulAut.conj (φ g) * β' * (MulAut.conj (φ g))⁻¹ =
        Φ (MulAut.conj g * Φ.symm β' * (MulAut.conj g)⁻¹) := by
      rw [map_mul, map_mul, map_inv, congr_conj, MulEquiv.apply_symm_apply]
    rw [hγ, congr_apply_apply, hg _ ((hR _).mpr (by rwa [MulEquiv.apply_symm_apply])),
      MulEquiv.apply_symm_apply]
  · intro R' α' hα' hα'I hα'2 hmap
    obtain ⟨R, hR⟩ := exists_sylow_pullback φ R'
    have hmapR : (R : Subgroup 𝕊).map (Φ.symm α').toMonoidHom = R := by
      rw [map_eq_iff]
      intro y
      rw [hR, hR, ← (map_eq_iff α' _).mp hmap (φ y)]
      have h1 : (Φ.symm α').symm y = Φ.symm α'⁻¹ y := rfl
      rw [h1, congr_symm_apply_apply, MulEquiv.apply_symm_apply]
      rfl
    have h2 := h.pgl_fixed R (Φ.symm α') (mem_map_equiv.mp hα')
      (fun hI => hα'I ((hinn α').mpr hI)) (by rw [← map_mul, hα'2, map_one]) hmapR
    have heq : (R' : Subgroup 𝕊') ⊓ MonoidHom.eqLocus α'.toMonoidHom (MonoidHom.id 𝕊') =
        ((R : Subgroup 𝕊) ⊓ MonoidHom.eqLocus (Φ.symm α').toMonoidHom (MonoidHom.id 𝕊)).map
          φ.toMonoidHom := by
      ext y'
      rw [mem_map_equiv, mem_inf, mem_inf, hR, MulEquiv.apply_symm_apply]
      change y' ∈ (R' : Subgroup 𝕊') ∧ α' y' = y' ↔
        y' ∈ (R' : Subgroup 𝕊') ∧ Φ.symm α' (φ.symm y') = φ.symm y'
      rw [congr_symm_apply_apply, MulEquiv.apply_symm_apply]
      constructor
      · rintro ⟨h1, h3⟩
        exact ⟨h1, by rw [h3]⟩
      · rintro ⟨h1, h3⟩
        exact ⟨h1, φ.symm.injective h3⟩
    rwa [heq, card_map_of_injective φ.injective]
  · intro R' β' hβ' hβ'2 hmap
    obtain ⟨R, hR⟩ := exists_sylow_pullback φ R'
    have hmapR : (R : Subgroup 𝕊).map (Φ.symm β').toMonoidHom = R := by
      rw [map_eq_iff]
      intro y
      rw [hR, hR, ← (map_eq_iff β' _).mp hmap (φ y)]
      have h1 : (Φ.symm β').symm y = Φ.symm β'⁻¹ y := rfl
      rw [h1, congr_symm_apply_apply, MulEquiv.apply_symm_apply]
      rfl
    obtain ⟨r₀, hr₀, hr₀2, hr₀β⟩ := h.field_inner R (Φ.symm β')
      (fun hL => hβ' (mem_map_equiv.mpr hL)) (by rw [← map_mul, hβ'2, map_one]) hmapR
    refine ⟨φ r₀, (hR _).mp hr₀, by rw [← map_mul, hr₀2, map_one], fun r' hr' => ?_⟩
    have h1 := hr₀β (φ.symm r') ((hR _).mpr (by rwa [MulEquiv.apply_symm_apply]))
    rw [congr_symm_apply_apply, MulEquiv.apply_symm_apply] at h1
    have h3 := congrArg φ h1
    rwa [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h3
  · intro R' hna' X' hX' hRX' R₁' hR₁X' ⟨e₁⟩ c' hc' hc'Z
    obtain ⟨R, hR⟩ := exists_sylow_pullback φ R'
    obtain ⟨a', ha', b', hb', hab'⟩ := hna'
    obtain ⟨eR⟩ := nonempty_sylow_equiv φ hR
    have hR₁ : Nonempty (↥(R₁'.map Φ.symm.toMonoidHom) ≃* (R : Subgroup 𝕊)) :=
      ⟨((MulEquiv.subgroupMap Φ.symm R₁').symm.trans e₁).trans eR⟩
    obtain ⟨r, hr, hrZ, hrc⟩ := h.center_le R
      ⟨φ.symm a', (hR _).mpr (by rwa [MulEquiv.apply_symm_apply]), φ.symm b',
        (hR _).mpr (by rwa [MulEquiv.apply_symm_apply]),
        fun hab => hab' (by simpa using congrArg φ hab)⟩
      (X'.map Φ.symm.toMonoidHom) (hX'.map _)
      (by
        rintro _ ⟨s, hs, rfl⟩
        rw [mem_map_equiv, MulEquiv.symm_symm, congr_conj]
        exact hRX' ⟨φ s, (hR s).mp hs, rfl⟩)
      (R₁'.map Φ.symm.toMonoidHom) (map_mono hR₁X') hR₁ (Φ.symm c') ⟨c', hc', rfl⟩
      (by
        rintro _ ⟨d', hd', rfl⟩
        simp only [MulEquiv.coe_toMonoidHom]
        rw [← map_mul, ← map_mul, hc'Z d' hd'])
    refine ⟨φ r, (hR r).mp hr, fun s' hs' => ?_, ?_⟩
    · have h1 := hrZ (φ.symm s') ((hR _).mpr (by rwa [MulEquiv.apply_symm_apply]))
      simpa using congrArg φ h1
    · rw [← congr_conj, ← hrc, MulEquiv.apply_symm_apply]
  · intro R' hab' P' hP'
    obtain ⟨R, hR⟩ := exists_sylow_pullback φ R'
    obtain ⟨s, hs, hcl⟩ := h.two_generated R
      (fun a ha b hb => φ.injective (by
        rw [map_mul, map_mul]
        exact hab' _ ((hR a).mp ha) _ ((hR b).mp hb)))
      (P'.map Φ.symm.toMonoidHom) (hP'.map _)
    classical
    refine ⟨s.image Φ, Finset.card_image_le.trans hs, ?_⟩
    have h1 : (closure (s : Set (MulAut 𝕊))).map Φ.toMonoidHom =
        closure (Φ.toMonoidHom '' (s : Set (MulAut 𝕊))) := MonoidHom.map_closure _ _
    rw [Finset.coe_image]
    change closure (Φ.toMonoidHom '' (s : Set (MulAut 𝕊))) = P'
    rw [← h1, hcl, map_map]
    convert map_id P' using 2
    ext α
    simp

end CFSG.ComponentClassification.FooteLit.Aut5
