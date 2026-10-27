module

public import CFSG.GH74.Generic.BProg.B2.GenLocL2SL
public import CFSG.GH74.Generic.BProg.B2.GenLocBasic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2OddInnerFixingKleinFour
public import CFSG.LieType.SteinbergBRSemidirectSL2

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
open scoped MatrixGroups

namespace GenLocL2Small

theorem f_le_two {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : p ^ f ∈ ({5, 7, 9} : Finset ℕ)) :
    f ≤ 2 := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  by_contra hf
  have h1 : 3 ^ 3 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 3 ^ f ≤ p ^ f := Nat.pow_le_pow_left hp3 f
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  omega

theorem mem_psl2Range_of_odd {F : Type} [Field F] (t : PGL2 F) (ht : Odd (orderOf t)) :
    t ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (Nat.coprime_two_left.mpr ht)
  rw [← hm]
  apply Subgroup.pow_mem
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective t
  rw [← map_pow, pgl2_mk_mem_psl2_range_iff_det_isSquare, Matrix.GeneralLinearGroup.val_det_apply,
    Units.val_pow_eq_pow_val, Matrix.det_pow]
  exact ⟨_, sq _⟩

section PGammaLevel

theorem odd_mem_pslRange {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : p ^ f ∈ ({5, 7, 9} : Finset ℕ)) (hF : Nat.card F = p ^ f) (g : PGammaL2 F)
    (hg : Odd (orderOf g)) : g ∈ pGammaL2PSLRange F := by
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · simp only [h0, pow_zero, Finset.mem_insert, Finset.mem_singleton] at hq
      omega
    · exact h0
  have hright : g.right = 1 := by
    have h1 : orderOf g.right ∣ f := by
      have := orderOf_dvd_natCard g.right
      rwa [card_ringAut F hp hF] at this
    have h1' : orderOf g.right ∣ 2 := by
      have hf2 := f_le_two hp hp2 hq
      interval_cases f
      · exact h1.trans (one_dvd 2)
      · exact h1
    have h2 : orderOf g.right ∣ orderOf g :=
      orderOf_map_dvd (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F)) _
    have := Nat.dvd_gcd h1' h2
    rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hg), Nat.dvd_one,
      orderOf_eq_one_iff] at this
  have hx : g = SemidirectProduct.inl g.left := SemidirectProduct.ext rfl hright
  have hlo : Odd (orderOf g.left) := by
    rw [hx, orderOf_injective _ SemidirectProduct.inl_injective] at hg
    exact hg
  obtain ⟨z, hz⟩ := mem_psl2Range_of_odd _ hlo
  refine ⟨z, ?_⟩
  change SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL z) = g
  rw [hz]
  exact hx.symm
end PGammaLevel

section FieldLevel

theorem commute_involution_two_power_F {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hq : p ^ f ∈ ({5, 7, 9} : Finset ℕ)) (hF : Nat.card F = p ^ f) {s : PSL2 F}
    (hs : orderOf s = 2) (x : PSL2 F) (hx : s * x = x * s) : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  have hf1 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · simp only [h0, pow_zero, Finset.mem_insert, Finset.mem_singleton] at hq
      omega
    · exact h0
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have : Fact p.Prime := ⟨hp⟩
  have hcard := CFSG.Walter.psl2_centralizer_involution F hF hodd hf1 hs
  have h8 : Nat.card (Subgroup.centralizer ({s} : Set (PSL2 F))) = 2 ^ 2 ∨
      Nat.card (Subgroup.centralizer ({s} : Set (PSL2 F))) = 2 ^ 3 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with h | h | h
    · left
      rw [(hcard.1 (by omega)).1]
      omega
    · right
      rw [(hcard.2 (by omega)).1]
      omega
    · right
      rw [(hcard.1 (by omega)).1]
      omega
  have hP : IsPGroup 2 (Subgroup.centralizer ({s} : Set (PSL2 F))) := by
    rcases h8 with h | h
    · exact IsPGroup.of_card h
    · exact IsPGroup.of_card h
  have hxc : x ∈ Subgroup.centralizer ({s} : Set (PSL2 F)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hx.symm
  obtain ⟨k, hk⟩ := hP ⟨x, hxc⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem exists_klein_of_card_eight
    {F : Type} [Field F] [Finite F] (hodd : IsOddPrimePower (Nat.card F)) {D : Type} [Group D]
    [Finite D] (hD : CFSG.IsElementaryAbelian 2 D) (h8 : Nat.card D = 8) (ι : D →* PGammaL2 F)
    (hι : Function.Injective ι) :
    ∃ B : Subgroup D, Nat.card ↥B = 4 ∧ (∀ b ∈ B, ι b ∈ pGammaL2PSLRange F) ∧
      ∀ d : D, d ∉ B → (ι d).right ≠ 1 := by
  set E' : Subgroup (PGammaL2 F) := ι.range with hE'
  have hDsq : ∀ x : D, x * x = 1 := fun x => WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD x
  have hE2 : ∀ x ∈ E', x * x = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul, hDsq x, map_one]
  have hE8 : Nat.card E' = 8 := by
    rw [hE', ← h8]
    exact (Nat.card_congr (MonoidHom.ofInjective hι).toEquiv).symm
  obtain ⟨x₀, hx₀E, hx₀r⟩ := exists_right_ne_one_of_card_eight hodd E' hE2 hE8.ge
  set L : Subgroup (PGammaL2 F) :=
    (linearPart E').map (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) with hL
  have hLE : L ≤ E' := by
    rintro _ ⟨g, hg, rfl⟩
    exact hg
  have hL4 : Nat.card L = 4 := by
    rw [hL, card_map_of_injective SemidirectProduct.inl_injective]
    exact card_linearPart_of_card_eight hodd hE2 hE8
  refine ⟨L.comap ι, ?_, ?_, ?_⟩
  · have hmap : (L.comap ι).map ι = L := Subgroup.map_comap_eq_self hLE
    rw [← card_map_of_injective hι, hmap, hL4]
  · intro b hb
    obtain ⟨g, hg, hgb⟩ := hb
    rw [← hgb]
    exact mem_pslRange_of_right_eq_one hodd hE2 hx₀E hx₀r hg (SemidirectProduct.right_inl g)
  · intro d hd hright
    apply hd
    have hx : ι d = SemidirectProduct.inl (ι d).left := SemidirectProduct.ext rfl hright
    have hmem : SemidirectProduct.inl (ι d).left ∈ E' := by
      rw [← hx]
      exact ⟨d, rfl⟩
    exact ⟨(ι d).left, hmem, hx.symm⟩
end FieldLevel

section Instance

theorem center_trivial {J : Type} [Group J] {F : Type} [Field F] [Finite F] (e : J ≃* PSL2 F) :
    ∀ z : J, (∀ g : J, g * z = z * g) → z = 1 := by
  intro z hz
  have h1 : e z ∈ Subgroup.center (PSL2 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg e (hz (e.symm g))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h
  rw [psl2_center_eq_bot F, Subgroup.mem_bot] at h1
  exact e.injective (h1.trans (map_one e).symm)

theorem exists_inner_of_odd {S : Type} [Group S] [Finite S] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : p ^ f ∈ ({5, 7, 9} : Finset ℕ)) (hS : LieModel S .PSL 2 p f) (σ : MulAut S)
    (hσ : Odd (orderOf σ)) : ∃ s : S, σ = MulAut.conj s := by
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hS
  have hxo : Odd (orderOf (autEquiv e σ)) := by rwa [MulEquiv.orderOf_eq]
  obtain ⟨z, hz⟩ := odd_mem_pslRange hp hp2 hq hF _ hxo
  refine ⟨e.symm z, (autEquiv e).injective ?_⟩
  rw [autEquiv_conj, MulEquiv.apply_symm_apply]
  exact hz.symm

theorem commute_involution_two_power {J : Type} [Group J] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hq : p ^ f ∈ ({5, 7, 9} : Finset ℕ)) (hJ : LieModel J .PSL 2 p f) {s : J}
    (hs : orderOf s = 2) (x : J) (hx : s * x = x * s) : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hJ
  have hs' : orderOf (e s) = 2 := by rw [MulEquiv.orderOf_eq]; exact hs
  obtain ⟨k, hk⟩ := commute_involution_two_power_F hp hp2 hq hF hs' (e x)
    (by rw [← map_mul, ← map_mul, hx])
  exact ⟨k, e.injective (by rw [map_pow, hk, map_one])⟩

theorem klein_fix_trivial {J : Type} [Group J]
    {F : Type} [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F)) (e : J ≃* PSL2 F)
    (φ : MulAut J) (hφ : Odd (orderOf φ)) (hin : ∃ a : J, φ = MulAut.conj a) (t s : J)
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hts : t ≠ s) (hcomm : t * s = s * t)
    (hφt : φ t = t) (hφs : φ s = s) : φ = 1 := by
  have hinv : ∀ x : J, orderOf x = 2 → BenderSuzuki.PFAppendixIII.IsInvolution (e x) := by
    intro x hx
    refine ⟨fun h => ?_, ?_⟩
    · have : x = 1 := e.injective (h.trans (map_one e).symm)
      rw [this, orderOf_one] at hx
      omega
    · have h := pow_orderOf_eq_one x
      rw [hx] at h
      rw [← map_pow, h, map_one]
  have hφ' : MulAut.congr e φ ^ orderOf φ = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have key := psl2_odd_inner_fixing_commuting_involutions_eq_one F hF (MulAut.congr e φ)
    (orderOf φ) hφ hφ' (e t) (e s) (hinv t ht) (hinv s hs) (fun h => hts (e.injective h))
    (by
      change e t * e s = e s * e t
      rw [← map_mul, ← map_mul, hcomm])
    (by simp [MulAut.congr_apply, hφt])
    (by simp [MulAut.congr_apply, hφs])
    (by
      obtain ⟨a, rfl⟩ := hin
      refine ⟨e a, ?_⟩
      ext x
      simp [MulAut.congr_apply, MulAut.conj_apply])
  exact (MulAut.congr e).injective (key.trans (map_one _).symm)

theorem exists_inner_klein_sub
    {J : Type} [Group J] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hJ : LieModel J .PSL 2 p f)
    {D : Subgroup (MulAut J)} (hD : CFSG.IsElementaryAbelian 2 ↥D) (h8 : Nat.card ↥D = 8) :
    ∃ B : Subgroup ↥D, Nat.card ↥B = 4 ∧ ∀ b ∈ B, ∃ s : J, (b : MulAut J) = MulAut.conj s := by
  obtain ⟨-, hf1, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hJ
  have hodd : IsOddPrimePower (Nat.card F) := isOddPrimePower_of hp hp2 hf1 hF
  have : Finite ↥D := Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
  have hιinj : Function.Injective ((autEquiv e).toMonoidHom.comp D.subtype) :=
    (autEquiv e).injective.comp Subtype.val_injective
  obtain ⟨B, hB4, hB, -⟩ := exists_klein_of_card_eight hodd hD h8
    ((autEquiv e).toMonoidHom.comp D.subtype) hιinj
  refine ⟨B, hB4, fun b hb => ?_⟩
  obtain ⟨z, hz⟩ := hB b hb
  refine ⟨e.symm z, (autEquiv e).injective ?_⟩
  rw [autEquiv_conj, MulEquiv.apply_symm_apply]
  exact hz.symm
end Instance

section Criterion
variable {J : Type} [Group J]

theorem conj_injective_of_center (hZ : ∀ z : J, (∀ g : J, g * z = z * g) → z = 1) :
    Function.Injective (MulAut.conj : J →* MulAut J) := by
  intro g h hgh
  have hc : ∀ x : J, g * x * g⁻¹ = h * x * h⁻¹ := fun x => by
    simpa [MulAut.conj_apply] using congrArg (fun φ : MulAut J => φ x) hgh
  have := hZ (h⁻¹ * g) fun x => by
    have := hc x
    calc x * (h⁻¹ * g) = h⁻¹ * (h * x * h⁻¹) * g := by group
      _ = h⁻¹ * (g * x * g⁻¹) * g := by rw [this]
      _ = (h⁻¹ * g) * x := by group
  exact (inv_mul_eq_one.1 this).symm

theorem orderOf_eq_two_of_conj (hZ : ∀ z : J, (∀ g : J, g * z = z * g) → z = 1)
    {D : Subgroup (MulAut J)} (hD : CFSG.IsElementaryAbelian 2 ↥D) {b : ↥D} (hb1 : b ≠ 1) {s : J}
    (hs : (b : MulAut J) = MulAut.conj s) : orderOf s = 2 := by
  have hsq : (b : MulAut J) * (b : MulAut J) = 1 :=
    congrArg Subtype.val (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD b)
  rw [hs, ← map_mul] at hsq
  have h1 : s * s = 1 := conj_injective_of_center hZ (by rw [hsq, map_one])
  have hs1 : s ≠ 1 := by
    rintro rfl
    apply hb1
    exact Subtype.ext (by rw [hs, map_one]; rfl)
  exact orderOf_eq_prime (by rw [pow_two]; exact h1) hs1

theorem commute_of_conj (hZ : ∀ z : J, (∀ g : J, g * z = z * g) → z = 1)
    {D : Subgroup (MulAut J)} (hD : CFSG.IsElementaryAbelian 2 ↥D) {b b' : ↥D} {s s' : J}
    (hs : (b : MulAut J) = MulAut.conj s) (hs' : (b' : MulAut J) = MulAut.conj s') :
    s * s' = s' * s := by
  have h := congrArg Subtype.val (mul_comm' b b')
  change (b : MulAut J) * (b' : MulAut J) = (b' : MulAut J) * (b : MulAut J) at h
  rw [hs, hs', ← map_mul, ← map_mul] at h
  exact conj_injective_of_center hZ h

theorem locE_of_klein_data
    (hZ : ∀ z : J, (∀ g : J, g * z = z * g) → z = 1)
    (hodd : ∀ σ : MulAut J, Odd (orderOf σ) → ∃ s : J, σ = MulAut.conj s)
    (hC : ∀ s : J, orderOf s = 2 → ∀ x : J, s * x = x * s → ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hK : ∀ φ : MulAut J, Odd (orderOf φ) → (∃ a : J, φ = MulAut.conj a) →
      ∀ t s : J, orderOf t = 2 → orderOf s = 2 → t ≠ s → t * s = s * t → φ t = t → φ s = s → φ = 1)
    {D : Subgroup (MulAut J)} [Finite ↥D] (hD : IsRank23 ↥D) (B : Subgroup ↥D)
    (hB4 : Nat.card ↥B = 4) (hBinn : ∀ b ∈ B, ∃ s : J, (b : MulAut J) = MulAut.conj s) :
    LocE1 D.subtype ∧ LocE2 D.subtype ∧ LocE3 D.subtype := by
  have hEA := hD.1
  have hcardD : Nat.card ↥D = 4 ∨ Nat.card ↥D = 8 := by
    rw [GenLocBasic.card_eq_two_pow_pRank_type hEA]
    rcases hD.2 with h | h <;> rw [h] <;> norm_num
  have hBidx : B.index ≤ 2 := by
    have h1 := Subgroup.card_mul_index B
    rw [hB4] at h1
    omega
  have hBadm : pRank 2 ↥D - 1 ≤ pRank 2 ↥B := (GenLocBasic.adm_iff_index hEA B).2 hBidx
  obtain ⟨a, b, ha1, hb1, hab, -⟩ :=
    GenLocL2.exists_klein_gens (GenLocBasic.isEA_subgroup hEA B) hB4
  obtain ⟨s₁, hs₁⟩ := hBinn a.1 a.2
  obtain ⟨s₂, hs₂⟩ := hBinn b.1 b.2
  have ha1' : (a.1 : ↥D) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hb1' : (b.1 : ↥D) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have ho₁ : orderOf s₁ = 2 := orderOf_eq_two_of_conj hZ hEA ha1' hs₁
  have ho₂ : orderOf s₂ = 2 := orderOf_eq_two_of_conj hZ hEA hb1' hs₂
  have hc₁₂ : s₁ * s₂ = s₂ * s₁ := commute_of_conj hZ hEA hs₁ hs₂
  have hne : s₁ ≠ s₂ := by
    intro h
    apply hab
    apply Subtype.ext
    apply Subtype.ext
    rw [hs₁, hs₂, h]
  have hfixed : ∀ (c c' : ↥D) (t t' : J), (c : MulAut J) = MulAut.conj t →
      (c' : MulAut J) = MulAut.conj t' → (c' : MulAut J) t = t := by
    intro c c' t t' ht ht'
    have hcomm := commute_of_conj hZ hEA ht' ht
    rw [ht', MulAut.conj_apply, hcomm]
    group
  have hs₁fix : s₁ ∈ fixedIn J (B.map D.subtype) := by
    rw [GenLocBasic.mem_fixedIn_map]
    intro c hc
    obtain ⟨t, ht⟩ := hBinn c hc
    exact hfixed a.1 c s₁ t hs₁ ht
  have hs₂fix : s₂ ∈ fixedIn J (B.map D.subtype) := by
    rw [GenLocBasic.mem_fixedIn_map]
    intro c hc
    obtain ⟨t, ht⟩ := hBinn c hc
    exact hfixed b.1 c s₂ t hs₂ ht
  refine ⟨?_, ?_, ?_⟩
  · intro E hE
    have hEidx : E.index ≤ 2 := (GenLocBasic.adm_iff_index hEA E).1 hE
    have hne' : E ⊓ B ≠ ⊥ := by
      intro hbot
      have h1 : (E ⊓ B).index ≤ E.index * B.index := Subgroup.index_inf_le
      rw [hbot, Subgroup.index_bot] at h1
      have h2 := Subgroup.card_mul_index B
      rw [hB4] at h2
      have hpos : 0 < Nat.card ↥D := Nat.card_pos
      have h3 : E.index * B.index ≤ 2 * B.index := Nat.mul_le_mul_right _ hEidx
      omega
    obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne'
    obtain ⟨s, hs⟩ := hBinn c.1 c.2.2
    have hc1' : (c.1 : ↥D) ≠ 1 := fun h => hc1 (Subtype.ext h)
    have hos : orderOf s = 2 := orderOf_eq_two_of_conj hZ hEA hc1' hs
    have hP : IsPGroup 2 ↥(fixedIn J (E.map D.subtype)) := by
      intro x
      have hx := (GenLocBasic.mem_fixedIn_map D.subtype E (x : J)).1 x.2 c.1 c.2.1
      have hx' : (c.1 : MulAut J) (x : J) = x := hx
      rw [hs, MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hx'
      obtain ⟨k, hk⟩ := hC s hos x hx'
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    exact noOddNormal_of_isPGroup hP
  · intro φ hφodd hφ
    exact hK φ hφodd (hodd φ hφodd) s₁ s₂ ho₁ ho₂ hne hc₁₂
      (hφ _ (le_gammaAct D.subtype hBadm hs₁fix)) (hφ _ (le_gammaAct D.subtype hBadm hs₂fix))
  · refine ⟨B, hBadm, s₁, hs₁fix, ⟨1, by simpa [ho₁] using pow_orderOf_eq_one s₁⟩, ?_⟩
    by_contra h
    push Not at h
    have : s₁ = 1 := hZ s₁ (fun g => h g)
    rw [this, orderOf_one] at ho₁
    omega
end Criterion

section Main

theorem locE_psl2_small_sub
    {J : Type} [Group J] [Finite J] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : p ^ f ∈ ({5, 7, 9} : Finset ℕ)) (hJ : LieModel J .PSL 2 p f)
    {D : Subgroup (MulAut J)} [Finite ↥D] (hD : IsRank23 ↥D) (B : Subgroup ↥D)
    (hB4 : Nat.card ↥B = 4) (hBinn : ∀ b ∈ B, ∃ s : J, (b : MulAut J) = MulAut.conj s) :
    LocE1 D.subtype ∧ LocE2 D.subtype ∧ LocE3 D.subtype := by
  obtain ⟨-, hf1, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hJ
  have hodd : IsOddPrimePower (Nat.card F) := isOddPrimePower_of hp hp2 hf1 hF
  exact locE_of_klein_data (center_trivial e) (exists_inner_of_odd hp hp2 hq hJ)
    (fun s hs x hx => commute_involution_two_power hp hp2 hq hJ hs x hx)
    (fun φ hφ hin t s ht hs hts hc hφt hφs => klein_fix_trivial hodd e φ hφ hin t s ht hs hts hc hφt hφs)
    hD B hB4 hBinn
end Main

section CriterionSL
variable {J : Type} [Group J]

theorem apply_eq_of_mem_center (hZc : Nat.card ↥(Subgroup.center J) = 2) (φ : MulAut J) {z : J}
    (hz : z ∈ Subgroup.center J) : φ z = z := by
  have hφz : φ z ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    have h := congrArg φ (hz (φ.symm g))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  · have hu := (Nat.card_eq_two_iff' (1 : ↥(Subgroup.center J))).1 hZc
    obtain ⟨y, -, hy⟩ := hu
    have h1 : (⟨z, hz⟩ : ↥(Subgroup.center J)) = y := hy _ (fun h => hz1 (congrArg Subtype.val h))
    have h2 : (⟨φ z, hφz⟩ : ↥(Subgroup.center J)) = y := hy _ (fun h => hz1 (φ.injective
      ((congrArg Subtype.val h).trans (map_one φ).symm)))
    exact congrArg Subtype.val (h2.trans h1.symm)

theorem mul_self_eq_one_of_mem_center (hZc : Nat.card ↥(Subgroup.center J) = 2) {z : J}
    (hz : z ∈ Subgroup.center J) : z * z = 1 := by
  have h := pow_card_eq_one' (G := ↥(Subgroup.center J)) (x := ⟨z, hz⟩)
  rw [hZc] at h
  have h' := congrArg Subtype.val h
  simpa [pow_two] using h'

theorem conj_eq_one_iff (s : J) : MulAut.conj s = 1 ↔ s ∈ Subgroup.center J := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h g
    have := congrArg (fun φ : MulAut J => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * s = (s * g * s⁻¹) * s := by rw [this]
      _ = s * g := by group
  · intro h
    ext g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h g]
    group
end CriterionSL

section CriterionSL2
variable {J : Type} [Group J]

theorem exists_admissible_fix_of_conj (hZc : Nat.card ↥(Subgroup.center J) = 2)
    {D : Subgroup (MulAut J)} [Finite ↥D] (hD : CFSG.IsElementaryAbelian 2 ↥D) {b : ↥D} {s : J}
    (hs : (b : MulAut J) = MulAut.conj s) :
    ∃ E : Subgroup ↥D, pRank 2 ↥D - 1 ≤ pRank 2 ↥E ∧ ∀ d ∈ E, (d : MulAut J) s = s := by
  have hcent : ∀ d : ↥D, s⁻¹ * (d : MulAut J) s ∈ Subgroup.center J := by
    intro d
    rw [Subgroup.mem_center_iff]
    intro g
    have hcomm : (d : MulAut J) * (b : MulAut J) = (b : MulAut J) * (d : MulAut J) :=
      congrArg Subtype.val (mul_comm' d b)
    have h1 := congrArg (fun φ : MulAut J => φ ((d : MulAut J)⁻¹ g)) hcomm
    simp only [MulAut.mul_apply, hs, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
      at h1
    calc g * (s⁻¹ * (d : MulAut J) s) = s⁻¹ * (s * g * s⁻¹) * (d : MulAut J) s := by group
      _ = s⁻¹ * ((d : MulAut J) s * g * ((d : MulAut J) s)⁻¹) * (d : MulAut J) s := by rw [h1]
      _ = (s⁻¹ * (d : MulAut J) s) * g := by group
  let χ : ↥D →* ↥(Subgroup.center J) :=
    { toFun := fun d => ⟨s⁻¹ * (d : MulAut J) s, hcent d⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro d d'
        apply Subtype.ext
        have hz' : (d : MulAut J) (s⁻¹ * (d' : MulAut J) s) = s⁻¹ * (d' : MulAut J) s :=
          apply_eq_of_mem_center hZc _ (hcent d')
        have e1 : (d' : MulAut J) s = s * (s⁻¹ * (d' : MulAut J) s) := by group
        change s⁻¹ * (d : MulAut J) ((d' : MulAut J) s) =
          (s⁻¹ * (d : MulAut J) s) * (s⁻¹ * (d' : MulAut J) s)
        conv_lhs => rw [e1, map_mul, hz']
        group }
  have hfin : Finite ↥(Subgroup.center J) := Nat.finite_of_card_ne_zero (by rw [hZc]; norm_num)
  have hχ : Nat.card χ.range ≤ 2 := by
    calc Nat.card χ.range ≤ Nat.card ↥(Subgroup.center J) := Subgroup.card_le_card_group _
      _ = 2 := hZc
  refine ⟨χ.ker, rank_ker_ge hD χ hχ, fun d hd => ?_⟩
  have h := congrArg Subtype.val (MonoidHom.mem_ker.1 hd)
  exact (inv_mul_eq_one.1 h).symm
end CriterionSL2

section CriterionSL3
variable {J : Type} [Group J]

theorem locE_of_klein_data_sl2
    (hZc : Nat.card ↥(Subgroup.center J) = 2)
    (hodd : ∀ σ : MulAut J, Odd (orderOf σ) → ∃ s : J, σ = MulAut.conj s)
    (hC : ∀ s : J, s ∉ Subgroup.center J → s * s ∈ Subgroup.center J →
      ∀ x : J, s * x = x * s → ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hK : ∀ φ : MulAut J, Odd (orderOf φ) → (∃ a : J, φ = MulAut.conj a) → ∀ t s : J,
      t ∉ Subgroup.center J → s ∉ Subgroup.center J → t * t ∈ Subgroup.center J →
      s * s ∈ Subgroup.center J → t * s * t⁻¹ * s⁻¹ ∈ Subgroup.center J →
      t * s⁻¹ ∉ Subgroup.center J → φ t = t → φ s = s → φ = 1)
    {D : Subgroup (MulAut J)} [Finite ↥D] (hD : IsRank23 ↥D) (B : Subgroup ↥D)
    (hB4 : Nat.card ↥B = 4) (hBinn : ∀ b ∈ B, ∃ s : J, (b : MulAut J) = MulAut.conj s) :
    LocE1 D.subtype ∧ LocE2 D.subtype ∧ LocE3 D.subtype := by
  have hEA := hD.1
  have hcardD : Nat.card ↥D = 4 ∨ Nat.card ↥D = 8 := by
    rw [GenLocBasic.card_eq_two_pow_pRank_type hEA]
    rcases hD.2 with h | h <;> rw [h] <;> norm_num
  have hBidx : B.index ≤ 2 := by
    have h1 := Subgroup.card_mul_index B
    rw [hB4] at h1
    omega
  have hnc : ∀ (b : ↥D) (s : J), b ≠ 1 → (b : MulAut J) = MulAut.conj s →
      s ∉ Subgroup.center J := by
    intro b s hb1 hs hsc
    apply hb1
    apply Subtype.ext
    rw [hs, (conj_eq_one_iff s).2 hsc]
    rfl
  have hsq : ∀ (b : ↥D) (s : J), (b : MulAut J) = MulAut.conj s → s * s ∈ Subgroup.center J := by
    intro b s hs
    rw [← conj_eq_one_iff, map_mul, ← hs]
    exact congrArg Subtype.val (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hEA b)
  obtain ⟨a, b, ha1, hb1, hab, -⟩ :=
    GenLocL2.exists_klein_gens (GenLocBasic.isEA_subgroup hEA B) hB4
  obtain ⟨s₁, hs₁⟩ := hBinn a.1 a.2
  obtain ⟨s₂, hs₂⟩ := hBinn b.1 b.2
  have ha1' : (a.1 : ↥D) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hb1' : (b.1 : ↥D) ≠ 1 := fun h => hb1 (Subtype.ext h)
  obtain ⟨E₁, hE₁, hE₁fix⟩ := exists_admissible_fix_of_conj hZc hEA hs₁
  obtain ⟨E₂, hE₂, hE₂fix⟩ := exists_admissible_fix_of_conj hZc hEA hs₂
  have hs₁fix : s₁ ∈ fixedIn J (E₁.map D.subtype) := by
    rw [GenLocBasic.mem_fixedIn_map]
    exact hE₁fix
  have hs₂fix : s₂ ∈ fixedIn J (E₂.map D.subtype) := by
    rw [GenLocBasic.mem_fixedIn_map]
    exact hE₂fix
  refine ⟨?_, ?_, ?_⟩
  · intro E hE
    have hEidx : E.index ≤ 2 := (GenLocBasic.adm_iff_index hEA E).1 hE
    have hne' : E ⊓ B ≠ ⊥ := by
      intro hbot
      have h1 : (E ⊓ B).index ≤ E.index * B.index := Subgroup.index_inf_le
      rw [hbot, Subgroup.index_bot] at h1
      have h2 := Subgroup.card_mul_index B
      rw [hB4] at h2
      have hpos : 0 < Nat.card ↥D := Nat.card_pos
      have h3 : E.index * B.index ≤ 2 * B.index := Nat.mul_le_mul_right _ hEidx
      omega
    obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne'
    obtain ⟨s, hs⟩ := hBinn c.1 c.2.2
    have hc1' : (c.1 : ↥D) ≠ 1 := fun h => hc1 (Subtype.ext h)
    have hP : IsPGroup 2 ↥(fixedIn J (E.map D.subtype)) := by
      intro x
      have hx := (GenLocBasic.mem_fixedIn_map D.subtype E (x : J)).1 x.2 c.1 c.2.1
      have hx' : (c.1 : MulAut J) (x : J) = x := hx
      rw [hs, MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hx'
      obtain ⟨k, hk⟩ := hC s (hnc _ s hc1' hs) (hsq _ s hs) x hx'
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    exact noOddNormal_of_isPGroup hP
  · intro φ hφodd hφ
    refine hK φ hφodd (hodd φ hφodd) s₁ s₂ (hnc _ s₁ ha1' hs₁) (hnc _ s₂ hb1' hs₂)
      (hsq _ s₁ hs₁) (hsq _ s₂ hs₂) ?_ ?_
      (hφ _ (le_gammaAct D.subtype hE₁ hs₁fix)) (hφ _ (le_gammaAct D.subtype hE₂ hs₂fix))
    · rw [← conj_eq_one_iff]
      simp only [map_mul, map_inv, ← hs₁, ← hs₂]
      have hcomm : (a.1 : MulAut J) * (b.1 : MulAut J) = (b.1 : MulAut J) * (a.1 : MulAut J) :=
        congrArg Subtype.val (mul_comm' a.1 b.1)
      rw [hcomm]
      group
    · rw [← conj_eq_one_iff]
      simp only [map_mul, map_inv, ← hs₁, ← hs₂]
      intro h
      apply hab
      apply Subtype.ext
      apply Subtype.ext
      exact (mul_inv_eq_one.1 h)
  · refine ⟨E₁, hE₁, s₁, hs₁fix, ?_, ?_⟩
    · refine ⟨2, ?_⟩
      have h := mul_self_eq_one_of_mem_center hZc (hsq _ s₁ hs₁)
      calc s₁ ^ 2 ^ 2 = (s₁ * s₁) * (s₁ * s₁) := by simp [pow_succ, mul_assoc]
        _ = 1 := h
    · by_contra h
      push Not at h
      exact hnc _ s₁ ha1' hs₁ (Subgroup.mem_center_iff.2 h)
end CriterionSL3

section SL2Instance
variable {K : Type} [Field K] [Finite K]

theorem ringChar_ne_two (h : Odd (Nat.card K)) : ringChar K ≠ 2 := by
  have : Fintype K := Fintype.ofFinite K
  intro h2
  have h1 := FiniteField.even_card_iff_char_two.1 h2
  have h3 := Nat.odd_iff.1 h
  rw [Nat.card_eq_fintype_card] at h3
  omega

theorem card_center_sl2 (h : Odd (Nat.card K)) : Nat.card ↥(Subgroup.center SL(2, K)) = 2 :=
  CFSG.LieType.SteinbergBR.card_center_SL2_eq_two (ringChar_ne_two h)

theorem exists_inner_of_odd_sl2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : p ^ f ∈ ({5, 7, 9} : Finset ℕ)) (hK : Nat.card K = p ^ f) (hodd : Odd (Nat.card K))
    (h3 : 3 < Nat.card K) (σ : MulAut SL(2, K)) (hσ : Odd (orderOf σ)) :
    ∃ s : SL(2, K), σ = MulAut.conj s := by
  have hg : Odd (orderOf (GLS.IVK.Lifted.gammaOf hodd h3 σ)) :=
    Odd.of_dvd_nat hσ (orderOf_map_dvd (GLS.IVK.Lifted.gammaOf hodd h3) σ)
  obtain ⟨y, hy⟩ := odd_mem_pslRange hp hp2 hq hK _ hg
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨s, GLS.IVK.Lifted.gammaOf_injective hodd h3 ?_⟩
  rw [GLS.IVK.Lifted.gammaOf_conj]
  exact hy.symm

theorem commute_lift_two_power {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : p ^ f ∈ ({5, 7, 9} : Finset ℕ)) (hK : Nat.card K = p ^ f)
    {s : SL(2, K)} (hs : s ∉ Subgroup.center SL(2, K)) (hs2 : s * s ∈ Subgroup.center SL(2, K))
    (x : SL(2, K)) (hx : s * x = x * s) : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  set π : SL(2, K) →* PSL2 K := QuotientGroup.mk' (Subgroup.center SL(2, K)) with hπ
  have hπs : orderOf (π s) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, pow_two]
      exact (QuotientGroup.eq_one_iff _).2 hs2
    · intro h
      exact hs ((QuotientGroup.eq_one_iff _).1 h)
  obtain ⟨k, hk⟩ := commute_involution_two_power_F hp hp2 hq hK hπs (π x)
    (by rw [← map_mul, ← map_mul, hx])
  refine ⟨k + 1, ?_⟩
  have hmem : x ^ 2 ^ k ∈ Subgroup.center SL(2, K) := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
    exact hk
  have h1 := GLS.IVK.Lifted.sq_eq_one_of_mem_center_sl2 hmem
  rw [pow_succ, pow_mul, pow_two]
  exact h1
end SL2Instance

section SL2Klein
variable {K : Type} [Field K] [Finite K]

theorem klein_fix_trivial_sl2
    (hOPP : IsOddPrimePower (Nat.card K)) (φ : MulAut SL(2, K)) (hφ : Odd (orderOf φ))
    (hin : ∃ a : SL(2, K), φ = MulAut.conj a) (t s : SL(2, K))
    (ht : t ∉ Subgroup.center SL(2, K)) (hs : s ∉ Subgroup.center SL(2, K))
    (ht2 : t * t ∈ Subgroup.center SL(2, K)) (hs2 : s * s ∈ Subgroup.center SL(2, K))
    (hcomm : t * s * t⁻¹ * s⁻¹ ∈ Subgroup.center SL(2, K))
    (hne : t * s⁻¹ ∉ Subgroup.center SL(2, K)) (hφt : φ t = t) (hφs : φ s = s) : φ = 1 := by
  obtain ⟨a, rfl⟩ := hin
  set π : SL(2, K) →* PSL2 K := QuotientGroup.mk' (Subgroup.center SL(2, K)) with hπ
  have hπ1 : ∀ x : SL(2, K), π x = 1 ↔ x ∈ Subgroup.center SL(2, K) := fun x =>
    QuotientGroup.eq_one_iff x
  have hinv : ∀ x : SL(2, K), x ∉ Subgroup.center SL(2, K) →
      x * x ∈ Subgroup.center SL(2, K) → BenderSuzuki.PFAppendixIII.IsInvolution (π x) := by
    intro x hx hx2
    refine ⟨fun h => hx ((hπ1 x).1 h), ?_⟩
    rw [← map_pow, pow_two]
    exact (hπ1 _).2 hx2
  have hm : (MulAut.conj (π a)) ^ orderOf (MulAut.conj a) = 1 := by
    have h1 : (MulAut.conj a) ^ orderOf (MulAut.conj a) = 1 := pow_orderOf_eq_one _
    rw [← map_pow] at h1
    have h2 : a ^ orderOf (MulAut.conj a) ∈ Subgroup.center SL(2, K) := (conj_eq_one_iff _).1 h1
    rw [← map_pow, ← map_pow, (hπ1 _).2 h2, map_one]
  have hfixed : ∀ x : SL(2, K), (MulAut.conj a) x = x → (MulAut.conj (π a)) (π x) = π x := by
    intro x hx
    rw [MulAut.conj_apply] at hx ⊢
    rw [← map_inv, ← map_mul, ← map_mul, hx]
  have key := psl2_odd_inner_fixing_commuting_involutions_eq_one K hOPP (MulAut.conj (π a))
    (orderOf (MulAut.conj a)) hφ hm (π t) (π s) (hinv t ht ht2) (hinv s hs hs2)
    (fun h => hne ((hπ1 _).1 (by rw [map_mul, map_inv, h, mul_inv_cancel])))
    (by
      have h1 : π (t * s * t⁻¹ * s⁻¹) = 1 := (hπ1 _).2 hcomm
      simp only [map_mul, map_inv] at h1
      change π t * π s = π s * π t
      calc π t * π s = (π t * π s * (π t)⁻¹ * (π s)⁻¹) * (π s * π t) := by group
        _ = π s * π t := by rw [h1, one_mul])
    (hfixed t hφt) (hfixed s hφs) ⟨π a, rfl⟩
  have hac : π a ∈ Subgroup.center (PSL2 K) := (conj_eq_one_iff _).1 key
  rw [psl2_center_eq_bot K, Subgroup.mem_bot] at hac
  exact (conj_eq_one_iff a).2 ((hπ1 a).1 hac)
end SL2Klein

section SL2Main
variable {K : Type} [Field K] [Finite K]

theorem inner_of_mem_pslRange_sl2 (hodd : Odd (Nat.card K)) (h3 : 3 < Nat.card K)
    (σ : MulAut SL(2, K)) (h : GLS.IVK.Lifted.gammaOf hodd h3 σ ∈ pGammaL2PSLRange K) :
    ∃ s : SL(2, K), σ = MulAut.conj s := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨s, GLS.IVK.Lifted.gammaOf_injective hodd h3 ?_⟩
  rw [GLS.IVK.Lifted.gammaOf_conj]
  exact hy.symm

theorem locE_sl2_small_sub {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hq : p ^ f ∈ ({5, 7, 9} : Finset ℕ)) (hK : Nat.card K = p ^ f)
    {D : Subgroup (MulAut SL(2, K))} [Finite ↥D] (hD : IsRank23 ↥D) (B : Subgroup ↥D)
    (hB4 : Nat.card ↥B = 4) (hBinn : ∀ b ∈ B, ∃ s : SL(2, K), (b : MulAut SL(2, K)) = MulAut.conj s) :
    LocE1 D.subtype ∧ LocE2 D.subtype ∧ LocE3 D.subtype := by
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · simp only [h0, pow_zero, Finset.mem_insert, Finset.mem_singleton] at hq
      omega
    · exact h0
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have h3 : 3 < Nat.card K := by
    rw [hK]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    omega
  have hOPP : IsOddPrimePower (Nat.card K) := isOddPrimePower_of hp hp2 hf1 hK
  exact locE_of_klein_data_sl2 (card_center_sl2 hodd)
    (exists_inner_of_odd_sl2 hp hp2 hq hK hodd h3)
    (fun s hs hs2 x hx => commute_lift_two_power hp hp2 hq hK hs hs2 x hx)
    (fun φ hφ hin t s ht hs ht2 hs2 hc hne hφt hφs =>
      klein_fix_trivial_sl2 hOPP φ hφ hin t s ht hs ht2 hs2 hc hne hφt hφs) hD B hB4 hBinn
end SL2Main
end GenLocL2Small

section L2Small

variable {A : Type} [Group A] [Finite A]

theorem loc_psl2_small
    {J : Type} [Group J] [Finite J] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hq : p ^ f ∈ ({5, 7, 9} : Finset ℕ)) (hJ : LieModel J .PSL 2 p f)
    (α : A →* MulAut J) (hA : IsRank23 A) (hgen : gammaAct α ≠ ⊤) :
    LocE1 α ∧ LocE2 α ∧ LocE3 α := by
  have h5 : 5 ≤ p ^ f := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    omega
  have hker : ∀ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E → ¬ E ≤ α.ker := fun E hE hle =>
    hgen (gammaAct_eq_top_of_le_ker α hE hle)
  obtain ⟨hD, hγ, h1, h2, h3⟩ := range_reduction α hA hker
  have : Finite ↥α.range := Finite.of_surjective _ α.rangeRestrict_surjective
  have hgenD : gammaAct α.range.subtype ≠ ⊤ := fun h => hgen (hγ.trans h)
  have key : LocE1 α.range.subtype ∧ LocE2 α.range.subtype ∧ LocE3 α.range.subtype := by
    rcases hD.2 with hr2 | hr3
    · have h4 : Nat.card α.range = 4 := by
        rw [GenLocBasic.card_eq_two_pow_pRank_type hD.1, hr2]
        norm_num
      rcases GenLocL2.gammaAct_psl2_core hp hp2 h5 hJ hD.1 h4 α.range.subtype with h | ⟨-, hinn⟩
      · exact absurd h hgenD
      · refine GenLocL2Small.locE_psl2_small_sub hp hp2 hq hJ hD ⊤ ?_ ?_
        · rw [Subgroup.card_top, h4]
        · intro b _
          obtain ⟨s, hs⟩ := hinn (MonoidHom.mem_range.2 ⟨b, rfl⟩)
          exact ⟨s, hs.symm⟩
    · have h8 : Nat.card α.range = 8 := by
        rw [GenLocBasic.card_eq_two_pow_pRank_type hD.1, hr3]
        norm_num
      obtain ⟨B, hB4, hBinn⟩ := GenLocL2Small.exists_inner_klein_sub hp hp2 hJ hD.1 h8
      exact GenLocL2Small.locE_psl2_small_sub hp hp2 hq hJ hD B hB4 hBinn
  exact ⟨h1.2 key.1, h2.2 key.2.1, h3.2 key.2.2⟩

end L2Small

section L2SmallSL

variable {A : Type} [Group A] [Finite A]

theorem loc_sl2_small
    {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hq : p ^ f ∈ ({5, 7, 9} : Finset ℕ))
    (α : A →* MulAut (SL(2, K))) (hA : IsRank23 A) (hgen : gammaAct α ≠ ⊤) :
    LocE1 α ∧ LocE2 α ∧ LocE3 α := by
  have h5 : 5 ≤ p ^ f := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    omega
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at h5
      omega
    · exact h0
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have h3 : 3 < Nat.card K := by
    rw [hK]
    omega
  have hOPP : IsOddPrimePower (Nat.card K) := isOddPrimePower_of hp hp2 hf1 hK
  have hker : ∀ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E → ¬ E ≤ α.ker := fun E hE hle =>
    hgen (gammaAct_eq_top_of_le_ker α hE hle)
  obtain ⟨hD, hγ, h1, h2, h3'⟩ := range_reduction α hA hker
  have : Finite ↥α.range := Finite.of_surjective _ α.rangeRestrict_surjective
  have hgenD : gammaAct α.range.subtype ≠ ⊤ := fun h => hgen (hγ.trans h)
  have key : LocE1 α.range.subtype ∧ LocE2 α.range.subtype ∧ LocE3 α.range.subtype := by
    rcases hD.2 with hr2 | hr3
    · have h4 : Nat.card α.range = 4 := by
        rw [GenLocBasic.card_eq_two_pow_pRank_type hD.1, hr2]
        norm_num
      rcases GenLocL2SL.gammaAct_sl2_core hp hp2 hK h5 hD.1 h4 α.range.subtype with h | ⟨-, hinn⟩
      · exact absurd h hgenD
      · refine GenLocL2Small.locE_sl2_small_sub hp hp2 hq hK hD ⊤ ?_ ?_
        · rw [Subgroup.card_top, h4]
        · intro b _
          obtain ⟨s, hs⟩ := hinn (MonoidHom.mem_range.2 ⟨b, rfl⟩)
          exact ⟨s, hs.symm⟩
    · have h8 : Nat.card α.range = 8 := by
        rw [GenLocBasic.card_eq_two_pow_pRank_type hD.1, hr3]
        norm_num
      set ι : ↥α.range →* PGammaL2 K :=
        (GLS.IVK.Lifted.gammaOf hodd h3).comp α.range.subtype with hι
      have hιinj : Function.Injective ι :=
        (GLS.IVK.Lifted.gammaOf_injective hodd h3).comp Subtype.val_injective
      obtain ⟨B, hB4, hBψ, -⟩ := GenLocL2Small.exists_klein_of_card_eight hOPP hD.1 h8 ι hιinj
      refine GenLocL2Small.locE_sl2_small_sub hp hp2 hq hK hD B hB4 ?_
      intro b hb
      exact GenLocL2Small.inner_of_mem_pslRange_sl2 hodd h3 _ (hBψ b hb)
  exact ⟨h1.2 key.1, h2.2 key.2.1, h3'.2 key.2.2⟩

end L2SmallSL

end CFSG.GH74.Generic.BProg.B2
