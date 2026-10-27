module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcoveToral
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcovePositive
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangCanonical

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality

private theorem rootChar_pow_of_conj_frob
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {e : ℕ}
    {b : Fin τ.rank → Lˣ} {u g : ModGL τ L} {w : WeylGroup τ}
    (huF : entrywiseFrobGL τ L 2 e u = u)
    (hgu : g⁻¹ * u * g = rootDiagUnit τ b)
    (hgw : g⁻¹ * entrywiseFrobGL τ L 2 e g = canonicalRep (coxeterSystem τ) L w) :
    ∀ v, rootChar b (w • v) = rootChar b v ^ 2 ^ e := by
  have hFg : entrywiseFrobGL τ L 2 e g = g * canonicalRep (coxeterSystem τ) L w := by
    calc entrywiseFrobGL τ L 2 e g = g * (g⁻¹ * entrywiseFrobGL τ L 2 e g) := by group
      _ = g * canonicalRep (coxeterSystem τ) L w := by rw [hgw]
  have hFd : entrywiseFrobGL τ L 2 e (rootDiagUnit τ b) =
      (canonicalRep (coxeterSystem τ) L w)⁻¹ * rootDiagUnit τ b *
        canonicalRep (coxeterSystem τ) L w := by
    calc entrywiseFrobGL τ L 2 e (rootDiagUnit τ b)
        = entrywiseFrobGL τ L 2 e (g⁻¹ * u * g) := by rw [hgu]
      _ = (entrywiseFrobGL τ L 2 e g)⁻¹ * entrywiseFrobGL τ L 2 e u *
            entrywiseFrobGL τ L 2 e g := by rw [map_mul, map_mul, map_inv]
      _ = (entrywiseFrobGL τ L 2 e g)⁻¹ * u * entrywiseFrobGL τ L 2 e g := by rw [huF]
      _ = (g * canonicalRep (coxeterSystem τ) L w)⁻¹ * u *
            (g * canonicalRep (coxeterSystem τ) L w) := by rw [hFg]
      _ = (canonicalRep (coxeterSystem τ) L w)⁻¹ * (g⁻¹ * u * g) *
            canonicalRep (coxeterSystem τ) L w := by group
      _ = (canonicalRep (coxeterSystem τ) L w)⁻¹ * rootDiagUnit τ b *
            canonicalRep (coxeterSystem τ) L w := by rw [hgu]
  have hconj : rootDiagUnit τ b = canonicalRep (coxeterSystem τ) L w *
      entrywiseFrobGL τ L 2 e (rootDiagUnit τ b) *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ := by
    rw [hFd]
    group
  intro v
  have hconj' : rootDiagUnit τ b = canonicalRep (coxeterSystem τ) L w *
      rootDiagUnit τ (b ^ 2 ^ e) * (canonicalRep (coxeterSystem τ) L w)⁻¹ := by
    rwa [entrywiseFrobGL_rootDiagUnit_eq_pow (ℓ := 2) e b] at hconj
  have h := (rootDiagUnit_eq_conj_canonicalRep_iff (K := L) b (b ^ 2 ^ e) w).1 hconj' v
  rwa [rootChar_pow'] at h

private theorem exists_lang_canonicalRep_char
    {τ : Tag} (K : KacData τ) (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    (e : ℕ) (he : 1 ≤ e) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Lˣ} (hζ : orderOf ζ = p) {u : ModGL τ L} (hu : u ∈ adjointGroup τ L)
    (huF : entrywiseFrobGL τ L 2 e u = u) (hup1 : u ^ p = 1) :
    ∃ g ∈ adjointGroup τ L, ∃ μ : Fin τ.rank → ℤ, ∃ w : WeylGroup τ,
      K.IsNormal p μ ∧ g⁻¹ * u * g = rootDiagUnit τ (fun i => ζ ^ μ i) ∧
      g⁻¹ * entrywiseFrobGL τ L 2 e g = canonicalRep (coxeterSystem τ) L w := by
  obtain ⟨g₁, hg₁, μ, hμ, hgu₁⟩ :=
    exists_conj_rootDiagUnit_normal (K := K) hτ halg hp hp2 hζ hu hup1
  let b : Fin τ.rank → Lˣ := fun i => ζ ^ μ i
  have hb : ∀ i, b i ^ p = 1 := by
    intro i
    have hζp : ζ ^ (p : ℤ) = 1 := by
      rw [zpow_natCast, ← hζ]
      exact pow_orderOf_eq_one ζ
    change (ζ ^ μ i) ^ p = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm (μ i) (p : ℤ), zpow_mul, hζp, one_zpow]
  have hpq : Nat.Coprime p (2 ^ e) := by
    refine (hp.coprime_iff_not_dvd).2 fun hdvd => hp2 ?_
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
  obtain ⟨g₂, hg₂, w, hgu₂, hgw₂⟩ :=
    exists_lang_canonicalRep (L := L) (ℓ := 2) (b := b) e he hpq hb hg₁ huF hgu₁
  exact ⟨g₂, hg₂, μ, w, hμ, hgu₂, hgw₂⟩

private theorem exists_smul_weylGroup_linearEquiv {τ : Tag} (w : WeylGroup τ) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) :
    ∃ f : (Fin τ.rank → ℤ) ≃ₗ[ℤ] (Fin τ.rank → ℤ), ∀ γ, f γ = ε • (w • γ) := by
  rcases hε with rfl | rfl
  · exact ⟨DistribMulAction.toLinearEquiv ℤ (Fin τ.rank → ℤ) w, fun γ => by
      rw [DistribMulAction.toLinearEquiv_apply, one_smul]⟩
  · refine ⟨(DistribMulAction.toLinearEquiv ℤ (Fin τ.rank → ℤ) w).trans
      (LinearEquiv.neg ℤ), fun γ => ?_⟩
    rw [LinearEquiv.trans_apply, DistribMulAction.toLinearEquiv_apply, LinearEquiv.neg_apply,
      neg_one_smul]

theorem kernelRoots_image_smul_of_rootCharPow
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {b : Fin τ.rank → Lˣ} {p q : ℕ} (hpq : Nat.Coprime p q) (hb : ∀ i, b i ^ p = 1)
    {w : WeylGroup τ} (hchar : ∀ v, rootChar b (w • v) = rootChar b v ^ q) :
    (fun α => w • α) '' kernelRoots (rootCharHom b) = kernelRoots (rootCharHom b) := by
  have key : ∀ x : Lˣ, x ^ p = 1 → x ^ q = 1 → x = 1 := by
    intro x h1 h2
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    rw [hpq] at h
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h)
  ext β
  constructor
  · rintro ⟨α, hα, rfl⟩
    refine ⟨IsRoot.smul hα.1 w, ?_⟩
    change rootChar b (w • α) = 1
    rw [hchar]
    rw [show rootChar b α = 1 from hα.2, one_pow]
  · rintro ⟨hβ, hβ1⟩
    refine ⟨w⁻¹ • β, ⟨IsRoot.smul hβ w⁻¹, ?_⟩, smul_inv_smul w β⟩
    change rootChar b (w⁻¹ • β) = 1
    refine key _ (rootChar_pow_eq_one b hb _) ?_
    rw [← hchar (w⁻¹ • β), smul_inv_smul]
    exact hβ1

private theorem dvd_dotProduct_sub_of_rootCharEq {τ : Tag} {L : Type} [Field L]
    {ζ : Lˣ} {p : ℕ} (hζ : orderOf ζ = p) {μ : Fin τ.rank → ℤ}
    {b : Fin τ.rank → Lˣ} (hb : ∀ i, b i = ζ ^ μ i) {x y : WeylGroup τ}
    (h : ∀ v, rootChar b (x • v) = rootChar b (y • v)) :
    ∀ v, (p : ℤ) ∣ (x • v) ⬝ᵥ μ - (y • v) ⬝ᵥ μ := by
  intro v
  have h1 : rootChar b (x • v) = ζ ^ ((x • v) ⬝ᵥ μ) := by
    rw [funext hb]
    exact KacData.rootChar_eq_zpow ζ μ (x • v)
  have h2 : rootChar b (y • v) = ζ ^ ((y • v) ⬝ᵥ μ) := by
    rw [funext hb]
    exact KacData.rootChar_eq_zpow ζ μ (y • v)
  have hz : ζ ^ ((x • v) ⬝ᵥ μ) = ζ ^ ((y • v) ⬝ᵥ μ) := by
    rw [← h1, h v, h2]
  have hmod : ((x • v) ⬝ᵥ μ) ≡ ((y • v) ⬝ᵥ μ) [ZMOD (p : ℤ)] := by
    have := zpow_eq_zpow_iff_modEq.1 hz
    rwa [hζ] at this
  have hd := Int.modEq_iff_dvd.1 hmod
  simpa [neg_sub] using dvd_neg.mpr hd

theorem dvd_dotProduct_sub_of_rootCharPow {τ : Tag} {L : Type} [Field L]
    {ζ : Lˣ} {p : ℕ} {N : ℕ} {ε : ℤ} (hq : (p : ℤ) ∣ (N : ℤ) - ε)
    (hζ : orderOf ζ = p) {μ : Fin τ.rank → ℤ} {b : Fin τ.rank → Lˣ}
    (hb : ∀ i, b i = ζ ^ μ i) {w : WeylGroup τ}
    (hchar : ∀ v, rootChar b (w • v) = rootChar b v ^ N) :
    ∀ v, (p : ℤ) ∣ (w • v) ⬝ᵥ μ - ε * (v ⬝ᵥ μ) := by
  intro v
  have h1 : rootChar b (w • v) = ζ ^ ((w • v) ⬝ᵥ μ) := by
    rw [funext hb]
    exact KacData.rootChar_eq_zpow ζ μ (w • v)
  have h2 : rootChar b v ^ N = ζ ^ ((N : ℤ) * (v ⬝ᵥ μ)) := by
    have hv : rootChar b v = ζ ^ (v ⬝ᵥ μ) := by
      rw [funext hb]
      exact KacData.rootChar_eq_zpow ζ μ v
    rw [hv, ← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  have hz : ζ ^ ((w • v) ⬝ᵥ μ) = ζ ^ ((N : ℤ) * (v ⬝ᵥ μ)) := by
    rw [← h1, hchar v, h2]
  have hmod : ((w • v) ⬝ᵥ μ) ≡ ((N : ℤ) * (v ⬝ᵥ μ)) [ZMOD (p : ℤ)] := by
    have := zpow_eq_zpow_iff_modEq.1 hz
    rwa [hζ] at this
  have hd1 : (p : ℤ) ∣ ((N : ℤ) * (v ⬝ᵥ μ)) - ((w • v) ⬝ᵥ μ) :=
    Int.modEq_iff_dvd.1 hmod
  have hd2 : (p : ℤ) ∣ ((N : ℤ) - ε) * (v ⬝ᵥ μ) := hq.mul_right _
  have hd3 := dvd_sub hd2 hd1
  convert hd3 using 1
  ring

theorem dvd_dotProduct_sub_of_kernelWeyl
    {τ : Tag} {L : Type} [Field L] {ζ : Lˣ} {p : ℕ}
    {N : ℕ} {ε : ℤ} (hq : (p : ℤ) ∣ (N : ℤ) - ε) (hζ : orderOf ζ = p)
    {μ : Fin τ.rank → ℤ} {b : Fin τ.rank → Lˣ} (hb : ∀ i, b i = ζ ^ μ i)
    {v w₁ : WeylGroup τ} (hv : v ∈ kernelWeylGroup (rootCharHom b))
    (hchar : ∀ x, rootChar b (w₁ • x) = rootChar b x ^ N) :
    ∀ x, (p : ℤ) ∣ ((v⁻¹ * w₁) • x) ⬝ᵥ μ - ε * (x ⬝ᵥ μ) := by
  intro x
  have hstab : ∀ y, rootChar b ((v⁻¹ * w₁) • y) = rootChar b (w₁ • y) := by
    intro y
    have hmem : v⁻¹ ∈ kernelWeylGroup (rootCharHom b) := inv_mem hv
    have h := (kernelWeylGroup_le (χ := rootCharHom b) hmem) (w₁ • y)
    rw [mul_smul]
    exact h
  have h1 := dvd_dotProduct_sub_of_rootCharPow (τ := τ) (L := L) hq hζ hb hchar x
  have h2 := dvd_dotProduct_sub_of_rootCharEq (τ := τ) (L := L) hζ hb hstab x
  have h3 := dvd_add h2 h1
  convert h3 using 1
  ring

private theorem alcoveValue_eq_zero_dvd {τ : Tag} {p : ℕ} {μ γ : Fin τ.rank → ℤ}
    (h : alcoveValue p μ γ = 0) : (p : ℤ) ∣ γ ⬝ᵥ μ := by
  by_cases hpos : ∀ j, 0 ≤ γ j
  · rw [alcoveValue, if_pos hpos, add_zero] at h
    rw [h]
    exact dvd_zero _
  · rw [alcoveValue, if_neg hpos] at h
    have hμ : γ ⬝ᵥ μ = -(p : ℤ) := by linarith
    rw [hμ]
    exact dvd_neg.mpr dvd_rfl

theorem exists_perm_extRoot_of_alcoveValue'
    {τ : Tag} (K : KacData τ) (hK : K.Facts)
    (hup : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → (∀ j, 0 ≤ γ j) → γ ≠ K.θ →
      ∃ j, IsRoot τ (γ + Pi.single j 1))
    (hdown : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → (∀ j, 0 ≤ γ j) → (∀ j, γ ≠ Pi.single j 1) →
      ∃ j, IsRoot τ (γ - Pi.single j 1) ∧ ∀ k, 0 ≤ (γ - Pi.single j 1 : Fin τ.rank → ℤ) k)
    {p : ℕ} (hp : 0 < p) {μ : Fin τ.rank → ℤ} (hμ : K.IsNormal p μ)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {w : WeylGroup τ}
    (hdvd_w : ∀ x, (p : ℤ) ∣ (w • x) ⬝ᵥ μ - ε * (x ⬝ᵥ μ))
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hχ : ∀ γ, IsRoot τ γ → (χ (Multiplicative.ofAdd γ) = 1 ↔ (p : ℤ) ∣ γ ⬝ᵥ μ))
    (hstable : ∀ γ ∈ kernelRoots χ, alcoveValue p μ γ = 0 →
      alcoveValue p μ (ε • (w • γ)) = 0) :
    ∃ σ : Equiv.Perm (Option (Fin τ.rank)),
      (∀ x, ε • (w • K.extRoot x) = K.extRoot (σ x)) ∧
      ∀ x, alcoveValue p μ (K.extRoot (σ x)) = alcoveValue p μ (K.extRoot x) := by
  obtain ⟨f, hf_apply⟩ := exists_smul_weylGroup_linearEquiv w hε
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hdvd_f : ∀ γ, IsRoot τ γ → (p : ℤ) ∣ f γ ⬝ᵥ μ - γ ⬝ᵥ μ := by
    intro γ _
    have h := (hdvd_w γ).mul_left ε
    have h' : ε * ((w • γ) ⬝ᵥ μ - ε * (γ ⬝ᵥ μ)) =
        ε * ((w • γ) ⬝ᵥ μ) - γ ⬝ᵥ μ := by
      rw [mul_sub, ← mul_assoc, hε2, one_mul]
    rw [h'] at h
    rwa [hf_apply γ, smul_dotProduct]
  have hεroot : ∀ {x : Fin τ.rank → ℤ}, IsRoot τ (ε • x) ↔ IsRoot τ x := by
    rcases hε with rfl | rfl
    · simp
    · intro x
      rw [neg_one_smul]
      exact isRoot_neg_iff
  have hf_iff : ∀ γ, IsRoot τ (f γ) ↔ IsRoot τ γ := by
    intro γ
    rw [hf_apply γ, hεroot, isRoot_smul_iff]
  have hzero : ∀ γ, IsRoot τ γ → alcoveValue p μ γ = 0 → alcoveValue p μ (f γ) = 0 := by
    intro γ hγ h0
    have hγk : γ ∈ kernelRoots χ := ⟨hγ, (hχ γ hγ).2 (alcoveValue_eq_zero_dvd h0)⟩
    have h := hstable γ hγk h0
    rw [hf_apply γ]
    exact h
  have hmap : ∀ γ, IsRoot τ γ → alcoveValue p μ (f γ) = alcoveValue p μ γ :=
    KacData.alcoveValue_map_eq (K := K) hK hμ f.toLinearMap
      (fun γ hγ => (hf_iff γ).2 hγ) hdvd_f hzero
  obtain ⟨σ, hσ⟩ :=
    KacData.exists_perm_extRoot_of_alcoveValue (K := K) hK hup hdown hp f hf_iff hmap
  refine ⟨σ, fun x => ?_, fun x => ?_⟩
  · rw [← hf_apply (K.extRoot x)]
    exact hσ x
  · have h1 := hmap (K.extRoot x) (K.isRoot_extRoot x)
    rwa [hσ x] at h1

theorem exists_lang_alcove_normal
    {τ : Tag} (K : KacData τ) (hK : K.Facts)
    (hup : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → (∀ j, 0 ≤ γ j) → γ ≠ K.θ →
      ∃ j, IsRoot τ (γ + Pi.single j 1))
    (hdown : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → (∀ j, 0 ≤ γ j) → (∀ j, γ ≠ Pi.single j 1) →
      ∃ j, IsRoot τ (γ - Pi.single j 1) ∧ ∀ k, 0 ≤ (γ - Pi.single j 1 : Fin τ.rank → ℤ) k)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    (e : ℕ) (he : 1 ≤ e) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hq : (p : ℤ) ∣ 2 ^ e - ε) {ζ : Lˣ} (hζ : orderOf ζ = p)
    {u : ModGL τ L} (hu : u ∈ adjointGroup τ L) (huF : entrywiseFrobGL τ L 2 e u = u)
    (hup1 : u ^ p = 1) :
    ∃ g ∈ adjointGroup τ L, ∃ μ : Fin τ.rank → ℤ, ∃ w : WeylGroup τ,
      ∃ σ : Equiv.Perm (Option (Fin τ.rank)),
      K.IsNormal p μ ∧ g⁻¹ * u * g = rootDiagUnit τ (fun i => ζ ^ μ i) ∧
      g⁻¹ * entrywiseFrobGL τ L 2 e g = canonicalRep (coxeterSystem τ) L w ∧
      (∀ x, ε • (w • K.extRoot x) = K.extRoot (σ x)) ∧
      ∀ x, alcoveValue p μ (K.extRoot (σ x)) = alcoveValue p μ (K.extRoot x) := by
  obtain ⟨g₀, hg₀, μ, w₀, hμ, hgu₀, hgw₀⟩ :=
    exists_lang_canonicalRep_char (K := K) hτ halg e he hp hp2 hζ hu huF hup1
  let b : Fin τ.rank → Lˣ := fun i => ζ ^ μ i
  have hbp : ∀ i, b i ^ p = 1 := by
    intro i
    have hζp : ζ ^ (p : ℤ) = 1 := by
      rw [zpow_natCast, ← hζ]
      exact pow_orderOf_eq_one ζ
    change (ζ ^ μ i) ^ p = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm (μ i) (p : ℤ), zpow_mul, hζp, one_zpow]
  have hchar₀ : ∀ v, rootChar b (w₀ • v) = rootChar b v ^ 2 ^ e :=
    rootChar_pow_of_conj_frob huF hgu₀ hgw₀
  have hpq : Nat.Coprime p (2 ^ e) := by
    refine (hp.coprime_iff_not_dvd).2 fun hdvd => hp2 ?_
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
  let χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ := rootCharHom b
  have hχ : ∀ γ, IsRoot τ γ → (χ (Multiplicative.ofAdd γ) = 1 ↔ (p : ℤ) ∣ γ ⬝ᵥ μ) := by
    intro γ _
    have hz : rootChar b γ = ζ ^ (γ ⬝ᵥ μ) := by
      change rootChar (fun i => ζ ^ μ i) γ = ζ ^ (γ ⬝ᵥ μ)
      exact KacData.rootChar_eq_zpow ζ μ γ
    change rootChar b γ = 1 ↔ (p : ℤ) ∣ γ ⬝ᵥ μ
    rw [hz, ← orderOf_dvd_iff_zpow_eq_one, hζ]
  have hx : (fun α => w₀ • α) '' kernelRoots χ = kernelRoots χ :=
    kernelRoots_image_smul_of_rootCharPow hpq hbp hchar₀
  obtain ⟨v, hv, hstable⟩ :=
    KacData.exists_kernelWeyl_alcove_stable (K := K) hK hp.pos hμ hχ hx hε
  obtain ⟨g, hg, hgu, hgw⟩ :=
    exists_lang_canonicalRep_kernelWeyl (L := L) e he (hp.odd_of_ne_two hp2) hbp
      hg₀ huF hgu₀ hgw₀ hv
  let w : WeylGroup τ := v⁻¹ * w₀
  have hgw' : g⁻¹ * entrywiseFrobGL τ L 2 e g = canonicalRep (coxeterSystem τ) L w := hgw
  have hdvd_w : ∀ x, (p : ℤ) ∣ (w • x) ⬝ᵥ μ - ε * (x ⬝ᵥ μ) := by
    have h := dvd_dotProduct_sub_of_kernelWeyl (τ := τ) (L := L) (N := 2 ^ e)
      (by exact_mod_cast hq) hζ (fun i => rfl) hv hchar₀
    simpa [w] using h
  have hstable' : ∀ γ ∈ kernelRoots χ, alcoveValue p μ γ = 0 →
      alcoveValue p μ (ε • (w • γ)) = 0 := by
    simpa [w] using hstable
  obtain ⟨σ, hσ', hσμ⟩ :=
    exists_perm_extRoot_of_alcoveValue' (K := K) hK hup hdown hp.pos hμ hε hdvd_w hχ hstable'
  exact ⟨g, hg, μ, w, σ, hμ, hgu, hgw', hσ', hσμ⟩

end CFSG.HardMathSupport.Timmesfeld.CrossChar
