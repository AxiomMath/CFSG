module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bZsig
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bInvol
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bGroup
public import CFSG.LocalAnalysis.SectionRank.EvenCover.UnitaryThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bModel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bAut
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.QuasithinUnique.Setup.X5

open CFSG.Quasithin CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.SectionRank.EvenCover

section Cover

open Subgroup in
theorem perfect_cover_map_of_section_compat {H L : Type*} [Group H] [Group L] [Group.IsPerfect L]
    {D : Subgroup H} [D.Normal] (e : L ⧸ center L ≃* H ⧸ D)
    (σ : H →* pullback (centralQuotientMap e) (QuotientGroup.mk' D))
    (hσ : ∀ g, pullbackFst _ _ (σ g) = g) :
    ∃ φ : H →* L, Function.Surjective φ ∧ φ.ker ≤ D ∧ D.map φ = center L ∧
      ∀ x, centralQuotientMap e (φ x) = (x : H ⧸ D) := by
  set φ : H →* L := (MonoidHom.snd H L).comp
    ((pullback (centralQuotientMap e) (QuotientGroup.mk' D)).subtype.comp σ) with hφ
  have hfφ : (centralQuotientMap e).comp φ = QuotientGroup.mk' D := comp_snd_section σ hσ
  have hfφ' : ∀ h, centralQuotientMap e (φ h) = (h : H ⧸ D) := fun h => congrArg (· h) hfφ
  have hker := ker_centralQuotientMap e
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    refine eq_top_of_forall_mul_center fun x => ?_
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective D (centralQuotientMap e x)
    refine ⟨φ h, ⟨h, rfl⟩, ?_⟩
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hfφ', ← hh, QuotientGroup.mk'_apply,
      inv_mul_cancel]
  refine ⟨φ, hsurj, fun h hh => ?_, ?_, hfφ'⟩
  · rw [MonoidHom.mem_ker] at hh
    have := hfφ' h
    rw [hh, map_one] at this
    exact (QuotientGroup.eq_one_iff h).1 this.symm
  · ext z
    constructor
    · rintro ⟨h, hh, rfl⟩
      rw [← hker, MonoidHom.mem_ker, hfφ', (QuotientGroup.eq_one_iff h).2 hh]
    · intro hz
      obtain ⟨h, rfl⟩ := hsurj z
      refine ⟨h, ?_, rfl⟩
      rw [← hker, MonoidHom.mem_ker, hfφ'] at hz
      exact (QuotientGroup.eq_one_iff h).1 hz

variable {f : ℕ} {K : Type} [Field K]

theorem exists_cover_map
    (hf : 2 ≤ f) (h : UnitaryFieldData 2 f K) {L : Type} [Group L] [Finite L]
    [Group.IsPerfect L] (hodd : Odd (Nat.card (Subgroup.center L)))
    (α : L ⧸ Subgroup.center L ≃* unitaryPSU h 3) :
    ∃ φ : unitarySU 2 f K 3 →* L, Function.Surjective φ ∧ φ.ker ≤ unitaryScalars h 3 ∧
      (unitaryScalars h 3).map φ = Subgroup.center L ∧
      ∀ s, α (QuotientGroup.mk (φ s)) = unitaryProj h 3 s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  obtain ⟨e, he⟩ : ∃ e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSU 3 (2 ^ f) K),
      e = α.trans (unitaryPSUEquiv h (by norm_num)) := ⟨_, rfl⟩
  obtain ⟨hsurj, hcen, hdvd⟩ := pullbackFst_centralQuotientMap e
  obtain ⟨σ, hσ, -⟩ := even_unitary_three_central_odd_extension_splitting h.card_eq_sq hf hsurj
    hcen (Odd.of_dvd_nat hodd hdvd)
  obtain ⟨φ, hφs, hφk, hφD, hφc⟩ := perfect_cover_map_of_section_compat e σ hσ
  have hDeq : unitaryScalars h 3 = (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ f) K) :=
    unitaryScalars_eq h (by norm_num)
  refine ⟨φ, hφs, ?_, ?_, fun s => ?_⟩
  · rw [hDeq]; exact hφk
  · rw [hDeq]; exact hφD
  · apply (unitaryPSUEquiv h (by norm_num)).injective
    rw [unitaryPSUEquiv_unitaryProj]
    have := hφc s
    rw [centralQuotientMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, he,
      MulEquiv.trans_apply, QuotientGroup.mk'_apply] at this
    exact this

end Cover

section Props

@[expose] def ThreeInvolutionProduct : Prop :=
  ∀ (f : ℕ), 2 ≤ f → ∀ (K : Type) [Field K], UnitaryFieldData 2 f K → ∀ (ℓ : ℕ), ℓ.Prime →
    ℓ ≠ 2 → ℓ ≠ 3 → orderOf (2 : ZMod ℓ) = 6 * f →
      ∃ s₁ s₂ s₃ : unitarySU 2 f K 3, s₁ * s₁ = 1 ∧ s₁ ≠ 1 ∧ s₂ * s₂ = 1 ∧ s₂ ≠ 1 ∧
        s₃ * s₃ = 1 ∧ s₃ ≠ 1 ∧ orderOf (s₁ * s₂ * s₃) = ℓ

@[expose] def OuterInverter : Prop :=
  ∀ (f : ℕ), 2 ≤ f → ∀ (K : Type) [Field K] (h : UnitaryFieldData 2 f K) (ℓ : ℕ), ℓ.Prime →
    ℓ ≠ 2 → orderOf (2 : ZMod ℓ) = 6 * f →
      ∀ α : MulAut (unitaryPSU h 3), α * α = 1 →
        α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (unitaryPSU h 3) →
          ∃ x : unitaryPSU h 3, orderOf x = ℓ ∧ α x = x⁻¹

end Props

section InnerInvolutions

variable {f : ℕ} {K : Type} [Field K]

theorem scalar_pow_three_matrix {h : UnitaryFieldData 2 f K} {z : unitarySU 2 f K 3}
    (hz : z ∈ unitaryScalars h 3) : z ^ 3 = 1 := by
  obtain ⟨c, -, hc3, hc⟩ := hz
  apply Subtype.ext
  rw [Subgroup.coe_pow, hc, ← map_pow, hc3, map_one]
  rfl

theorem two_pow_le_index_involution (hf : 2 ≤ f) (h : UnitaryFieldData 2 f K)
    (hN4 : ThreeInvolutionProduct) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hord : orderOf (2 : ZMod ℓ) = 6 * f) {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) (L : Subgroup (MulAut W)) {φ : unitarySU 2 f K 3 →* L}
    (hφs : Function.Surjective φ) (hφk : φ.ker ≤ unitaryScalars h 3) {t : MulAut W} (ht : t ∈ L)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) : 2 ^ (2 * f) ≤ (fixV (Subgroup.zpowers t)).index := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨s₁, s₂, s₃, h1, h1', h2, h2', h3, h3', hprod⟩ := hN4 f hf K h ℓ hℓ hℓ2 hℓ3 hord
  have hC3 : ∀ z ∈ φ.ker, z ^ 3 = 1 := fun z hz => scalar_pow_three_matrix (hφk hz)
  have hinv : ∀ s : unitarySU 2 f K 3, s * s = 1 → s ≠ 1 → φ s * φ s = 1 ∧ φ s ≠ 1 := by
    intro s hs hs1
    refine ⟨by rw [← map_mul, hs, map_one], fun h0 => hs1 ?_⟩
    have hk : s ∈ φ.ker := h0
    have h3 := hC3 s hk
    calc s = s ^ 3 * (s * s)⁻¹ := by group
      _ = 1 := by rw [h3, hs]; simp
  obtain ⟨hq1, hq1'⟩ := hinv s₁ h1 h1'
  obtain ⟨hq2, hq2'⟩ := hinv s₂ h2 h2'
  obtain ⟨hq3, hq3'⟩ := hinv s₃ h3 h3'
  have htL : (⟨t, ht⟩ : L) * ⟨t, ht⟩ = 1 := Subtype.ext ht2
  have htL' : (⟨t, ht⟩ : L) ≠ 1 := fun h0 => ht1 (congrArg Subtype.val h0)
  have hconj : ∀ q : L, q * q = 1 → q ≠ 1 → (fixV (Subgroup.zpowers (q : MulAut W))).index =
      (fixV (Subgroup.zpowers t)).index := by
    intro q hq hq1
    obtain ⟨k, hk⟩ := isConj_iff.mp (matrix_quotient_involutions_isConj h hφs hφk htL htL' hq hq1)
    have := congrArg Subtype.val hk
    rw [← this]
    simpa using index_fixV_conj (k : MulAut W) t
  have hc : orderOf (φ (s₁ * s₂ * s₃)) = ℓ := by
    have hne : φ (s₁ * s₂ * s₃) ≠ 1 := by
      intro h0
      have hk : s₁ * s₂ * s₃ ∈ φ.ker := h0
      have h3 := hC3 _ hk
      have : ℓ ∣ 3 := by rw [← hprod]; exact orderOf_dvd_of_pow_eq_one h3
      exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp this)
    exact orderOf_eq_prime (by rw [← map_pow, ← hprod, pow_orderOf_eq_one, map_one]) hne
  set c : L := φ s₁ * φ s₂ * φ s₃ with hcdef
  have hcphi : c = φ (s₁ * s₂ * s₃) := by rw [hcdef, map_mul, map_mul]
  have hcord : orderOf c = ℓ := by rw [hcphi]; exact hc
  have hcpow : (c : MulAut W) ^ ℓ = 1 := by
    have : c ^ ℓ = 1 := by rw [← hcord]; exact pow_orderOf_eq_one _
    simpa using congrArg Subtype.val this
  have hc1 : (c : MulAut W) ≠ 1 := by
    intro h0
    have : c = 1 := Subtype.ext h0
    rw [this, orderOf_one] at hcord
    exact hℓ.one_lt.ne hcord
  have hR1 := two_pow_orderOf_le_index_fixV hW hℓ2 hcpow hc1
  rw [hord] at hR1
  have hmul : (c : MulAut W) = ((φ s₁ : L) : MulAut W) * ((φ s₂ : L) : MulAut W) *
      ((φ s₃ : L) : MulAut W) := by
    rw [hcdef]; simp
  have hidx : (fixV (Subgroup.zpowers (c : MulAut W))).index ≤
      (fixV (Subgroup.zpowers t)).index ^ 3 := by
    rw [hmul]
    calc _ ≤ (fixV (Subgroup.zpowers (((φ s₁ : L) : MulAut W) * ((φ s₂ : L) : MulAut W)))).index *
          (fixV (Subgroup.zpowers ((φ s₃ : L) : MulAut W))).index := index_fixV_mul_le _ _
      _ ≤ ((fixV (Subgroup.zpowers ((φ s₁ : L) : MulAut W))).index *
          (fixV (Subgroup.zpowers ((φ s₂ : L) : MulAut W))).index) *
          (fixV (Subgroup.zpowers ((φ s₃ : L) : MulAut W))).index :=
        Nat.mul_le_mul_right _ (index_fixV_mul_le _ _)
      _ = (fixV (Subgroup.zpowers t)).index ^ 3 := by
        rw [hconj _ hq1 hq1', hconj _ hq2 hq2', hconj _ hq3 hq3']; ring
  have h6 : (2 ^ (2 * f)) ^ 3 ≤ (fixV (Subgroup.zpowers t)).index ^ 3 := by
    calc (2 ^ (2 * f)) ^ 3 = 2 ^ (6 * f) := by rw [← pow_mul]; ring_nf
      _ ≤ _ := hR1.trans hidx
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h6

end InnerInvolutions

section OuterInvolutions

variable {f : ℕ} {K : Type} [Field K]

theorem two_pow_le_index_outer (hf : 2 ≤ f) (h : UnitaryFieldData 2 f K)
    (hN2 : OuterInverter) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hord : orderOf (2 : ZMod ℓ) = 6 * f) {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) (L : Subgroup (MulAut W))
    (α : L ⧸ Subgroup.center L ≃* unitaryPSU h 3) (hZ3 : ∀ z ∈ Subgroup.center L, z ^ 3 = 1)
    {a : MulAut W} (ha : a ∈ Subgroup.normalizer (L : Set (MulAut W))) (ha2 : a * a = 1)
    (hout : normalizerAct L ⟨a, ha⟩ ∉
      (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) :
    2 ^ (3 * f) ≤ (fixV (Subgroup.zpowers a)).index := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set τa := normalizerAct L ⟨a, ha⟩ with hτa
  set αa : MulAut (unitaryPSU h 3) := MulAut.congr α τa with hαa
  have hτ2 : τa * τa = 1 := by
    have : (⟨a, ha⟩ * ⟨a, ha⟩ : Subgroup.normalizer (L : Set (MulAut W))) = 1 := Subtype.ext ha2
    rw [hτa, ← map_mul, this, map_one]
  have hαa2 : αa * αa = 1 := by rw [hαa, ← map_mul, hτ2, map_one]
  have hinner : αa ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (unitaryPSU h 3) := by
    rintro ⟨x, hx⟩
    apply hout
    refine ⟨α.symm x, ?_⟩
    have h1 : MulAut.congr α.symm (MulAut.conj x) = MulAut.conj (α.symm x) :=
      CFSG.ComponentClassification.OuterAutomorphisms.congr_conj α.symm x
    have h2 : MulAut.congr α.symm αa = τa := by
      ext y
      simp [hαa, MulAut.congr_apply]
    show MulAut.conj (α.symm x) = τa
    rw [← h1, ← h2]
    exact congrArg (MulAut.congr α.symm) hx
  obtain ⟨x, hxord, hxinv⟩ := hN2 f hf K h ℓ hℓ hℓ2 hord αa hαa2 hinner
  have hy : orderOf (α.symm x) = ℓ := by rw [MulEquiv.orderOf_eq]; exact hxord
  have hay : τa (α.symm x) = (α.symm x)⁻¹ := by
    have h1 : αa x = α (τa (α.symm x)) := by simp [hαa, MulAut.congr_apply]
    rw [hxinv] at h1
    apply α.injective
    rw [← h1, map_inv, MulEquiv.apply_symm_apply]
  obtain ⟨c, hcℓ, hc1, hac⟩ := exists_inverted_lift L hℓ hℓ3 hZ3 ha hy hay
  have hCℓ : (c : MulAut W) ^ ℓ = 1 := by simpa using congrArg Subtype.val hcℓ
  have hC1 : (c : MulAut W) ≠ 1 := fun h0 => hc1 (Subtype.ext h0)
  obtain ⟨m, hm⟩ : ∃ m, ℓ = 2 * m + 1 := by
    rcases hℓ.eq_two_or_odd' with h2 | hodd
    · exact absurd h2 hℓ2
    · obtain ⟨m, hm⟩ := hodd; exact ⟨m, hm⟩
  obtain ⟨hconj, hCeq⟩ := conj_involution_inverting ha2 hac (by rw [← hm]; exact hCℓ)
  have hR1 := two_pow_orderOf_le_index_fixV hW hℓ2 hCℓ hC1
  rw [hord] at hR1
  have hidx : (fixV (Subgroup.zpowers (c : MulAut W))).index ≤
      (fixV (Subgroup.zpowers a)).index ^ 2 := by
    calc _ = (fixV (Subgroup.zpowers (a * (a * (c : MulAut W))))).index := by rw [← hCeq]
      _ ≤ (fixV (Subgroup.zpowers a)).index * (fixV (Subgroup.zpowers (a * (c : MulAut W)))).index :=
        index_fixV_mul_le _ _
      _ = (fixV (Subgroup.zpowers a)).index ^ 2 := by
        rw [← hconj, index_fixV_conj, sq]
  have h6 : (2 ^ (3 * f)) ^ 2 ≤ (fixV (Subgroup.zpowers a)).index ^ 2 := by
    calc (2 ^ (3 * f)) ^ 2 = 2 ^ (6 * f) := by rw [← pow_mul]; ring_nf
      _ ≤ _ := hR1.trans hidx
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h6

end OuterInvolutions

section Offender

variable {f : ℕ} {K : Type} [Field K]

theorem normalizerAct_not_inner {W : Type} [CommGroup W] (L : Subgroup (MulAut W)) {a : MulAut W}
    (ha : a ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hout : ¬ ∃ l ∈ L, ∀ x ∈ L, ∃ z ∈ L, (∀ y ∈ L, y * z = z * y) ∧
      a * x * a⁻¹ = l * x * l⁻¹ * z) :
    normalizerAct L ⟨a, ha⟩ ∉
      (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range := by
  rintro ⟨y, hy⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  apply hout
  refine ⟨(l : MulAut W), l.2, fun x hx => ?_⟩
  have h1 := congrArg (fun m : MulAut (L ⧸ Subgroup.center L) => m (QuotientGroup.mk ⟨x, hx⟩)) hy
  simp only [MulAut.conj_apply] at h1
  rw [normalizerAct_apply_mk] at h1
  have h2 : (QuotientGroup.mk (l * ⟨x, hx⟩ * l⁻¹) : L ⧸ Subgroup.center L) =
      QuotientGroup.mk (conjOn L ⟨a, ha⟩ ⟨x, hx⟩) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact h1
  have h3 := QuotientGroup.eq.mp h2
  refine ⟨(((l * ⟨x, hx⟩ * l⁻¹)⁻¹ * conjOn L ⟨a, ha⟩ ⟨x, hx⟩ : L) : MulAut W),
    (((l * ⟨x, hx⟩ * l⁻¹)⁻¹ * conjOn L ⟨a, ha⟩ ⟨x, hx⟩ : L)).2, fun y hy => ?_, ?_⟩
  · have := (Subgroup.mem_center_iff.mp h3) ⟨y, hy⟩
    simpa using congrArg Subtype.val this
  · have := congrArg Subtype.val (show (l * ⟨x, hx⟩ * l⁻¹ : L) *
        ((l * ⟨x, hx⟩ * l⁻¹)⁻¹ * conjOn L ⟨a, ha⟩ ⟨x, hx⟩) = conjOn L ⟨a, ha⟩ ⟨x, hx⟩ by group)
    rw [coe_conjOn] at this
    simpa [mul_assoc] using this.symm

theorem card_le_two_mul_ker {A M : Type*} [Group A] [Finite A] [Group M] (ψ : A →* M)
    (hrange : Nat.card ψ.range ≤ 2) : Nat.card A ≤ 2 * Nat.card ψ.ker := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv] at h1
  rw [h1]
  exact Nat.mul_le_mul_right _ hrange

end Offender

section Main

variable {f : ℕ} {K : Type} [Field K]

theorem irreducible_even_unitary_three_full_normalizer_excludes_binary_offenders_of
    (hf : 2 ≤ f) (h : UnitaryFieldData 2 f K) (hN4 : ThreeInvolutionProduct)
    (hN2 : OuterInverter) {W : Type} [CommGroup W] [Finite W] [Nontrivial W]
    (hW : ∀ w : W, w * w = 1) (L : Subgroup (MulAut W)) (hperf : Group.IsPerfect L)
    (hirr : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (α : L ⧸ Subgroup.center L ≃* unitaryPSU h 3) :
    (∃ φ : unitarySU 2 f K 3 →* L, Function.Surjective φ ∧ φ.ker ≤ unitaryScalars h 3 ∧
      (unitaryScalars h 3).map φ = Subgroup.center L ∧
      ∀ s, α (QuotientGroup.mk (φ s)) = unitaryProj h 3 s) ∧
    Nat.card (Subgroup.center L) ∣ Nat.gcd 3 (2 ^ f + 1) ∧
    (∀ t ∈ L, t * t = 1 → t ≠ 1 → 2 ^ (2 * f) ≤ (fixV (Subgroup.zpowers t)).index) ∧
    (∀ a ∈ Subgroup.normalizer (L : Set (MulAut W)), a * a = 1 →
      (¬ ∃ l ∈ L, ∀ x ∈ L, ∃ z ∈ L, (∀ y ∈ L, y * z = z * y) ∧
        a * x * a⁻¹ = l * x * l⁻¹ * z) →
      2 ^ (3 * f) ≤ (fixV (Subgroup.zpowers a)).index) ∧
    (∀ A : Subgroup (MulAut W), A ≤ Subgroup.normalizer (L : Set (MulAut W)) → A ≠ ⊥ →
      IsElemAbelian2 A → Nat.card A * Nat.card (fixV A) < Nat.card W) := by
  have := hperf
  have hfin : Finite (MulAut W) := Finite.of_injective (fun σ : MulAut W => (σ : W → W))
    DFunLike.coe_injective
  have hCodd := centralizer_odd hW L hirr
  have hZodd : Odd (Nat.card (Subgroup.center L)) := by
    let ι : Subgroup.center L →* Subgroup.centralizer (L : Set (MulAut W)) :=
      (L.subtype.comp (Subgroup.center L).subtype).codRestrict _ (fun z =>
        Subgroup.mem_centralizer_iff.mpr fun g hg => by
          have := (Subgroup.mem_center_iff.mp z.2) ⟨g, hg⟩
          exact congrArg Subtype.val this)
    have hinj : Function.Injective ι := fun x y hxy => by
      have := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext this)
    exact Odd.of_dvd_nat hCodd (Subgroup.card_dvd_of_injective ι hinj)
  obtain ⟨φ, hφs, hφk, hφZ, hφα⟩ := exists_cover_map hf h hZodd α
  have hZdvd : Nat.card (Subgroup.center L) ∣ Nat.gcd 3 (2 ^ f + 1) := by
    rw [← card_unitaryScalars h (by norm_num : 1 ≤ 3), ← hφZ]
    exact Subgroup.card_map_dvd _ _
  have hZ3 : ∀ z ∈ Subgroup.center L, z ^ 3 = 1 := by
    intro z hz
    have h3 : Nat.card (Subgroup.center L) ∣ 3 := hZdvd.trans (Nat.gcd_dvd_left _ _)
    obtain ⟨k, hk⟩ := h3
    have : (⟨z, hz⟩ : Subgroup.center L) ^ Nat.card (Subgroup.center L) = 1 := pow_card_eq_one'
    have h' := congrArg (fun w : Subgroup.center L => (w : L)) this
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h'
    rw [hk, pow_mul, h', one_pow]
  obtain ⟨ℓ, hℓ, hℓ2, hord, -, -, hnot3⟩ :=
    binary_multiple_six_exponents_have_primitive_prime_divisors hf
  have hℓ3 : ℓ ≠ 3 := fun h0 => hnot3 (by rw [h0]; exact dvd_mul_right 3 _)
  have hinv := fun {t : MulAut W} (ht : t ∈ L) (ht2 : t * t = 1) (ht1 : t ≠ 1) =>
    two_pow_le_index_involution hf h hN4 hℓ hℓ2 hℓ3 hord hW L hφs hφk ht ht2 ht1
  have hout := fun {a : MulAut W} (ha : a ∈ Subgroup.normalizer (L : Set (MulAut W)))
      (ha2 : a * a = 1) (hout : normalizerAct L ⟨a, ha⟩ ∉
        (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) =>
    two_pow_le_index_outer hf h hN2 hℓ hℓ2 hℓ3 hord hW L α hZ3 ha ha2 hout
  refine ⟨⟨φ, hφs, hφk, hφZ, hφα⟩, hZdvd, fun t ht ht2 ht1 => hinv ht ht2 ht1,
    fun a ha ha2 ha' => hout ha ha2 (normalizerAct_not_inner L ha ha'), ?_⟩
  intro A hAN hA1 hAe
  obtain ⟨Ψ, hΨ⟩ := exists_fieldFactor_hom hf h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have hAsq : ∀ a ∈ A, a * a = 1 := fun a ha => by simpa [sq] using hAe.2 a ha
  let τ : Subgroup.normalizer (L : Set (MulAut W)) →* MulAut (unitaryPSU h 3) :=
    (MulAut.congr α).toMonoidHom.comp (normalizerAct L)
  let ψ : A →* (K ≃+* K) := (Ψ.comp τ).comp (Subgroup.inclusion hAN)
  have hψ : ∀ a : A, ψ a = Ψ (τ ⟨(a : MulAut W), hAN a.2⟩) := fun a => rfl
  have hinner_iff : ∀ (a : MulAut W) (ha : a ∈ Subgroup.normalizer (L : Set (MulAut W))),
      τ ⟨a, ha⟩ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (unitaryPSU h 3) →
        normalizerAct L ⟨a, ha⟩ ∈
          (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range := by
    rintro a ha ⟨x, hx⟩
    refine ⟨α.symm x, ?_⟩
    have h1 : MulAut.congr α.symm (MulAut.conj x) = MulAut.conj (α.symm x) :=
      CFSG.ComponentClassification.OuterAutomorphisms.congr_conj α.symm x
    have h2 : MulAut.congr α.symm (τ ⟨a, ha⟩) = normalizerAct L ⟨a, ha⟩ := by
      ext y
      simp [τ, MulAut.congr_apply]
    show MulAut.conj (α.symm x) = normalizerAct L ⟨a, ha⟩
    rw [← h1, ← h2]
    exact congrArg (MulAut.congr α.symm) hx
  have hker : ∀ a : A, ψ a = 1 → (a : MulAut W) ∈ L := by
    intro a ha
    have haN : (a : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) := hAN a.2
    have hββ : τ ⟨(a : MulAut W), haN⟩ * τ ⟨(a : MulAut W), haN⟩ = 1 := by
      rw [← map_mul]
      have : (⟨(a : MulAut W), haN⟩ * ⟨(a : MulAut W), haN⟩ :
          Subgroup.normalizer (L : Set (MulAut W))) = 1 := Subtype.ext (hAsq a a.2)
      rw [this, map_one]
    have hβ := hΨ _ (by rw [← hψ]; exact ha) hββ
    exact mem_of_involution_inner L hCodd haN (hAsq a a.2) (hinner_iff _ haN hβ)
  have hrange : Nat.card ψ.range ≤ 2 := by
    refine card_le_two_of_sq_eq_one (p := 2) ψ.range ?_
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (hAe.2 a a.2)
    rw [this, map_one]
  have hc : Nat.card A ≤ 2 * Nat.card ψ.ker := card_le_two_mul_ker ψ hrange
  have hAL_fin : Finite ↥(A ⊓ L) := inferInstance
  have hd : Nat.card ψ.ker ≤ Nat.card ↥(A ⊓ L) := by
    refine Nat.card_le_card_of_injective (fun a : ψ.ker =>
      (⟨((a : A) : MulAut W), ⟨(a : A).2, hker a a.2⟩⟩ : ↥(A ⊓ L))) ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg Subtype.val hab
    simpa using this
  have he : Nat.card ↥(A ⊓ L) ≤ 2 ^ f := by
    set E : Subgroup L := (A ⊓ L).subgroupOf L with hE
    have hEe : IsElemAbelianTwo E := by
      refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
      · exact Subtype.ext (hAe.1 _ ((Subgroup.mem_subgroupOf.mp hx).1) _
          ((Subgroup.mem_subgroupOf.mp hy).1))
      · exact Subtype.ext (hAe.2 _ ((Subgroup.mem_subgroupOf.mp hx).1))
    have hcardE : Nat.card E = Nat.card ↥(A ⊓ L) := by
      rw [← Subgroup.card_map_of_injective (f := L.subtype) L.subtype_injective,
        hE, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
    rw [← hcardE]
    exact matrix_quotient_card_elemAbelian_le h hφs hφk E hEe
  have hAbound : Nat.card A ≤ 2 * 2 ^ f := hc.trans (Nat.mul_le_mul_left _ (hd.trans he))
  rw [card_mul_card_fixV_lt_iff]
  have hq : 2 * 2 ^ f < 2 ^ (2 * f) := by
    calc 2 * 2 ^ f = 2 ^ (f + 1) := by rw [pow_succ']
      _ < 2 ^ (2 * f) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  by_cases hAL : ∃ t ∈ A, t ∈ L ∧ t ≠ 1
  · obtain ⟨t, htA, htL, ht1⟩ := hAL
    have h1 := hinv htL (hAsq t htA) ht1
    have h2 : (fixV (Subgroup.zpowers t)).index ≤ (fixV A).index :=
      index_fixV_antitone ((Subgroup.zpowers_le).mpr htA)
    omega
  · push Not at hAL
    have hker1 : Nat.card ψ.ker = 1 := by
      rw [Subgroup.card_eq_one, Subgroup.eq_bot_iff_forall]
      intro a ha
      exact Subtype.ext (hAL _ a.2 (hker a ha))
    have hA2 : Nat.card A ≤ 2 := by
      have := hc; rw [hker1] at this; omega
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
    have haN : (a : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) := hAN a.2
    have haL : (a : MulAut W) ∉ L := fun hL => ha1 (Subtype.ext (hAL _ a.2 hL))
    have houta : normalizerAct L ⟨(a : MulAut W), haN⟩ ∉
        (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range :=
      fun hin => haL (mem_of_involution_inner L hCodd haN (hAsq a a.2) hin)
    have h1 := hout haN (hAsq a a.2) houta
    have h2 : (fixV (Subgroup.zpowers (a : MulAut W))).index ≤ (fixV A).index :=
      index_fixV_antitone ((Subgroup.zpowers_le).mpr a.2)
    have h3 : 2 < 2 ^ (3 * f) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ < 2 ^ (3 * f) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

end Main

end CFSG.QuasithinUnique.Setup.X5
