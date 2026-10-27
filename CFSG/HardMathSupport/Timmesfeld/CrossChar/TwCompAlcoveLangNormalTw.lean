module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcoveLangNormal
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LangCanonicalTw
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.Weyl

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality

private theorem rootChar_pow_of_conj_twist
    {L : Type} [Field L] [CharP L 2] {e : ℕ}
    {b : Fin TwistTag.E6.tag.rank → Lˣ} {u g : ModGL TwistTag.E6.tag L}
    {w : WeylGroup TwistTag.E6.tag}
    (huF : twistHom TwistTag.E6 L (iterateFrobenius L 2 e) u = u)
    (hgu : g⁻¹ * u * g = rootDiagUnit TwistTag.E6.tag b)
    (hgw : g⁻¹ * twistHom TwistTag.E6 L (iterateFrobenius L 2 e) g =
      canonicalRep (coxeterSystem TwistTag.E6.tag) L w) :
    ∀ γ, rootChar b (w • permLattice TwistTag.E6.perm γ) = rootChar b γ ^ 2 ^ e := by
  let F : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L :=
    twistHom TwistTag.E6 L (iterateFrobenius L 2 e)
  have huF' : F u = u := huF
  have hgwF : g⁻¹ * F g = canonicalRep (coxeterSystem TwistTag.E6.tag) L w := hgw
  have hn : (g⁻¹ * F g) * F (rootDiagUnit TwistTag.E6.tag b) * (g⁻¹ * F g)⁻¹ =
      rootDiagUnit TwistTag.E6.tag b := conj_frob_rootDiag_of_conj_eq huF' hgu
  have hnw : canonicalRep (coxeterSystem TwistTag.E6.tag) L w *
      F (rootDiagUnit TwistTag.E6.tag b) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)⁻¹ =
      rootDiagUnit TwistTag.E6.tag b := by
    rw [hgwF] at hn
    exact hn
  have hconj : rootDiagUnit TwistTag.E6.tag b =
      canonicalRep (coxeterSystem TwistTag.E6.tag) L w *
        rootDiagUnit TwistTag.E6.tag
          (fun i => Units.map (iterateFrobenius L 2 e).toMonoidHom
            (b (TwistTag.E6.perm.symm i))) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)⁻¹ := by
    rw [show F (rootDiagUnit TwistTag.E6.tag b) =
        rootDiagUnit TwistTag.E6.tag
          (fun i => Units.map (iterateFrobenius L 2 e).toMonoidHom
            (b (TwistTag.E6.perm.symm i))) from twistHom_rootDiagUnit_eq b] at hnw
    exact hnw.symm
  intro γ
  have h := (rootDiagUnit_eq_conj_canonicalRep_iff (K := L) b
      (fun i => Units.map (iterateFrobenius L 2 e).toMonoidHom
        (b (TwistTag.E6.perm.symm i))) w).1 hconj
    (permLattice TwistTag.E6.perm γ)
  rw [CFSG.RankThree.PartOne.KE.rootChar_map_tuple,
    ← rootChar_permLattice b TwistTag.E6.perm.symm (permLattice TwistTag.E6.perm γ),
    CFSG.LieType.Chevalley.permLattice_symm_permLattice] at h
  rw [h]
  refine Units.ext ?_
  simp

private theorem exists_conj_lang_twE6
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (K : KacData TwistTag.E6.tag)
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    (e : ℕ) (he : 1 ≤ e) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Lˣ} (hζ : orderOf ζ = p) {u : ModGL TwistTag.E6.tag L}
    (hu : u ∈ adjointGroup TwistTag.E6.tag L)
    (huF : twistHom TwistTag.E6 L (iterateFrobenius L 2 e) u = u) (hup1 : u ^ p = 1) :
    ∃ (g : ModGL TwistTag.E6.tag L) (w : WeylGroup TwistTag.E6.tag)
      (μ : Fin TwistTag.E6.tag.rank → ℤ),
      K.IsNormal p μ ∧ g ∈ adjointGroup TwistTag.E6.tag L ∧
      g⁻¹ * u * g = rootDiagUnit TwistTag.E6.tag (fun i => ζ ^ μ i) ∧
      g⁻¹ * twistHom TwistTag.E6 L (iterateFrobenius L 2 e) g =
        canonicalRep (coxeterSystem TwistTag.E6.tag) L w ∧
      (∀ i, (ζ ^ μ i) ^ p = 1) ∧
      ∀ v, rootChar (fun i => ζ ^ μ i) (w • permLattice TwistTag.E6.perm v) =
        rootChar (fun i => ζ ^ μ i) v ^ 2 ^ e := by
  obtain ⟨g₁, hg₁, μ, hμ, hgu₁⟩ :=
    exists_conj_rootDiagUnit_normal (K := K) (Or.inr (Or.inl rfl)) halg hp hp2 hζ hu hup1
  obtain ⟨g₀, hg₀, w₀, hgu₀, hgw₀⟩ :=
    exists_lang_canonicalRep_tw (L := L) 2 TwistTag.E6 e he hg₁ huF hgu₁
  have hbp : ∀ i, (ζ ^ μ i) ^ p = 1 := by
    intro i
    have hζp : ζ ^ (p : ℤ) = 1 := by
      rw [zpow_natCast, ← hζ]
      exact pow_orderOf_eq_one ζ
    rw [← zpow_natCast, ← zpow_mul, mul_comm (μ i) (p : ℤ), zpow_mul, hζp, one_zpow]
  have hchar₀ : ∀ v, rootChar (fun i => ζ ^ μ i)
      (w₀ • permLattice TwistTag.E6.perm v) = rootChar (fun i => ζ ^ μ i) v ^ 2 ^ e :=
    rootChar_pow_of_conj_twist huF hgu₀ hgw₀
  exact ⟨g₀, w₀, μ, hμ, hg₀, hgu₀, hgw₀, hbp, hchar₀⟩

private theorem exists_char_pow_e6W0
    {L : Type} [Field L] [IsAlgClosed L] {e p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : ℤ}
    (hq : (p : ℤ) ∣ 2 ^ e - ε) {w₀ : WeylGroup TwistTag.E6.tag}
    (W0 : WeylGroup TwistTag.E6.tag)
    (hW0 : ∀ v, W0 • v = -(permLattice TwistTag.E6.perm v))
    {b : Fin TwistTag.E6.tag.rank → Lˣ} (hbp : ∀ i, b i ^ p = 1)
    (hchar₀ : ∀ v, rootChar b (w₀ • permLattice TwistTag.E6.perm v) = rootChar b v ^ 2 ^ e) :
    ∃ N : ℕ, Nat.Coprime p N ∧ (p : ℤ) ∣ (N : ℤ) - (-ε) ∧
      ∀ v, rootChar b ((w₀ * W0) • v) = rootChar b v ^ N := by
  refine ⟨2 ^ e * (p - 1), ?_, ?_, ?_⟩
  · have hpq : Nat.Coprime p (2 ^ e) := by
      refine (hp.coprime_iff_not_dvd).2 fun hdvd => ?_
      exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
        (hp.dvd_of_dvd_pow hdvd)) hp2
    have hp1 : Nat.Coprime p (p - 1) :=
      (Nat.coprime_self_sub_right (le_of_lt hp.one_lt)).2 (Nat.coprime_one_right p)
    exact hpq.mul_right hp1
  · have h1 : (p : ℤ) ∣ (p : ℤ) * (2 : ℤ) ^ e := dvd_mul_right _ _
    have h2 : (p : ℤ) ∣ (2 : ℤ) ^ e - ε := by simpa using hq
    have h3 := dvd_sub h1 h2
    have h4 : ((2 ^ e * (p - 1) : ℕ) : ℤ) - (-ε) =
        (p : ℤ) * (2 : ℤ) ^ e - ((2 : ℤ) ^ e - ε) := by
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        Nat.cast_sub (le_of_lt hp.one_lt), Nat.cast_one]
      ring
    rwa [h4]
  · intro v
    have hχp : rootChar b v ^ p = 1 := rootChar_pow_eq_one b hbp v
    have h1 : (w₀ * W0) • v = -(w₀ • permLattice TwistTag.E6.perm v) := by
      rw [mul_smul, hW0 v, smul_neg]
    have h2 : rootChar b ((w₀ * W0) • v) =
        (rootChar b (w₀ • permLattice TwistTag.E6.perm v))⁻¹ := by
      rw [h1, ← zero_sub, rootChar_sub, rootChar_zero, one_mul]
    have hpq : 2 ^ e * (p - 1) + 2 ^ e = 2 ^ e * p := by
      calc 2 ^ e * (p - 1) + 2 ^ e = 2 ^ e * (p - 1) + 2 ^ e * 1 := by rw [Nat.mul_one]
        _ = 2 ^ e * ((p - 1) + 1) := by rw [← Nat.mul_add]
        _ = 2 ^ e * p := by rw [Nat.sub_add_cancel (le_of_lt hp.one_lt)]
    have h3 : rootChar b v ^ (2 ^ e * (p - 1)) * rootChar b v ^ 2 ^ e = 1 := by
      rw [← pow_add, hpq, Nat.mul_comm (2 ^ e) p, pow_mul, hχp, one_pow]
    rw [h2, hchar₀ v]
    exact inv_eq_of_mul_eq_one_left h3

private theorem exists_kernelWeyl_lang_twE6
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (K : KacData TwistTag.E6.tag) (hK : K.Facts)
    (hup : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ → (∀ j, 0 ≤ γ j) →
      γ ≠ K.θ → ∃ j, IsRoot TwistTag.E6.tag (γ + Pi.single j 1))
    (hdown : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ → (∀ j, 0 ≤ γ j) →
      (∀ j, γ ≠ Pi.single j 1) → ∃ j, IsRoot TwistTag.E6.tag (γ - Pi.single j 1) ∧
        ∀ k, 0 ≤ (γ - Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) k)
    {p : ℕ} (hp : p.Prime) {μ : Fin TwistTag.E6.tag.rank → ℤ} (hμ : K.IsNormal p μ)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {ζ : Lˣ} (hζ : orderOf ζ = p)
    (e : ℕ) (he : 1 ≤ e) {u g₀ : ModGL TwistTag.E6.tag L} {w₀ : WeylGroup TwistTag.E6.tag}
    (hg₀ : g₀ ∈ adjointGroup TwistTag.E6.tag L)
    (huF : twistHom TwistTag.E6 L (iterateFrobenius L 2 e) u = u)
    (hgu₀ : g₀⁻¹ * u * g₀ = rootDiagUnit TwistTag.E6.tag (fun i => ζ ^ μ i))
    (hgw₀ : g₀⁻¹ * twistHom TwistTag.E6 L (iterateFrobenius L 2 e) g₀ =
      canonicalRep (coxeterSystem TwistTag.E6.tag) L w₀)
    {W0 : WeylGroup TwistTag.E6.tag} (hbp : ∀ i, (ζ ^ μ i) ^ p = 1) {N : ℕ}
    (hcop : Nat.Coprime p N) (hN : (p : ℤ) ∣ (N : ℤ) - (-ε))
    (hcharx : ∀ v, rootChar (fun i => ζ ^ μ i) ((w₀ * W0) • v) =
      rootChar (fun i => ζ ^ μ i) v ^ N) :
    ∃ (g : ModGL TwistTag.E6.tag L) (w : WeylGroup TwistTag.E6.tag)
      (σ : Equiv.Perm (Option (Fin TwistTag.E6.tag.rank))),
      g ∈ adjointGroup TwistTag.E6.tag L ∧
      g⁻¹ * u * g = rootDiagUnit TwistTag.E6.tag (fun i => ζ ^ μ i) ∧
      g⁻¹ * twistHom TwistTag.E6 L (iterateFrobenius L 2 e) g =
        canonicalRep (coxeterSystem TwistTag.E6.tag) L w ∧
      (∀ x, (-ε) • ((w * W0) • K.extRoot x) = K.extRoot (σ x)) ∧
      ∀ x, alcoveValue p μ (K.extRoot (σ x)) = alcoveValue p μ (K.extRoot x) := by
  let b : Fin TwistTag.E6.tag.rank → Lˣ := fun i => ζ ^ μ i
  let χ : Multiplicative (Fin TwistTag.E6.tag.rank → ℤ) →* Lˣ := rootCharHom b
  have hχ : ∀ γ, IsRoot TwistTag.E6.tag γ →
      (χ (Multiplicative.ofAdd γ) = 1 ↔ (p : ℤ) ∣ γ ⬝ᵥ μ) := by
    intro γ _
    have hz : rootChar b γ = ζ ^ (γ ⬝ᵥ μ) := by
      change rootChar (fun i => ζ ^ μ i) γ = ζ ^ (γ ⬝ᵥ μ)
      exact KacData.rootChar_eq_zpow ζ μ γ
    change rootChar b γ = 1 ↔ (p : ℤ) ∣ γ ⬝ᵥ μ
    rw [hz, ← orderOf_dvd_iff_zpow_eq_one, hζ]
  have hx : (fun α => (w₀ * W0) • α) '' kernelRoots χ = kernelRoots χ :=
    kernelRoots_image_smul_of_rootCharPow (w := w₀ * W0) hcop hbp hcharx
  have hεneg : -ε = 1 ∨ -ε = -1 := by rcases hε with rfl | rfl <;> norm_num
  obtain ⟨v, hv, hstable⟩ :=
    KacData.exists_kernelWeyl_alcove_stable (K := K) hK hp.pos hμ hχ hx (ε := -ε) hεneg
  obtain ⟨g, hg, hgu, hgw⟩ :=
    exists_lang_canonicalRep_kernelWeyl_tw (L := L) TwistTag.E6 e he hg₀ huF hgu₀ hgw₀ hv
  let w : WeylGroup TwistTag.E6.tag := v⁻¹ * w₀
  have hgw' : g⁻¹ * twistHom TwistTag.E6 L (iterateFrobenius L 2 e) g =
      canonicalRep (coxeterSystem TwistTag.E6.tag) L w := hgw
  have hdvd_w : ∀ y, (p : ℤ) ∣ ((w * W0) • y) ⬝ᵥ μ - (-ε) * (y ⬝ᵥ μ) := by
    have h := dvd_dotProduct_sub_of_kernelWeyl (τ := TwistTag.E6.tag) (L := L) (N := N)
      (ε := -ε) hN hζ (fun i => rfl) hv hcharx
    intro y
    simpa [w, mul_assoc] using h y
  have hstable' : ∀ γ ∈ kernelRoots χ, alcoveValue p μ γ = 0 →
      alcoveValue p μ ((-ε) • ((w * W0) • γ)) = 0 := by
    simpa [w, mul_assoc] using hstable
  obtain ⟨σ, hσ, hσμ⟩ :=
    exists_perm_extRoot_of_alcoveValue' (K := K) hK hup hdown hp.pos hμ hεneg hdvd_w hχ hstable'
  exact ⟨g, w, σ, hg, hgu, hgw', hσ, hσμ⟩

theorem exists_lang_alcove_normal_twE6
    (K : KacData TwistTag.E6.tag) (hK : K.Facts)
    (hup : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ → (∀ j, 0 ≤ γ j) →
      γ ≠ K.θ → ∃ j, IsRoot TwistTag.E6.tag (γ + Pi.single j 1))
    (hdown : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ → (∀ j, 0 ≤ γ j) →
      (∀ j, γ ≠ Pi.single j 1) → ∃ j, IsRoot TwistTag.E6.tag (γ - Pi.single j 1) ∧
        ∀ k, 0 ≤ (γ - Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) k)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    (e : ℕ) (he : 1 ≤ e) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hq : (p : ℤ) ∣ 2 ^ e - ε) {ζ : Lˣ} (hζ : orderOf ζ = p)
    {u : ModGL TwistTag.E6.tag L} (hu : u ∈ adjointGroup TwistTag.E6.tag L)
    (huF : twistHom TwistTag.E6 L (iterateFrobenius L 2 e) u = u) (hup1 : u ^ p = 1) :
    ∃ g ∈ adjointGroup TwistTag.E6.tag L, ∃ μ : Fin TwistTag.E6.tag.rank → ℤ,
      ∃ w : WeylGroup TwistTag.E6.tag, ∃ σ : Equiv.Perm (Option (Fin TwistTag.E6.tag.rank)),
      K.IsNormal p μ ∧ g⁻¹ * u * g = rootDiagUnit TwistTag.E6.tag (fun i => ζ ^ μ i) ∧
      g⁻¹ * twistHom TwistTag.E6 L (iterateFrobenius L 2 e) g =
        canonicalRep (coxeterSystem TwistTag.E6.tag) L w ∧
      (∀ x, ε • (w • permLattice TwistTag.E6.perm (K.extRoot x)) = K.extRoot (σ x)) ∧
      ∀ x, alcoveValue p μ (K.extRoot (σ x)) = alcoveValue p μ (K.extRoot x) := by
  obtain ⟨g₀, w₀, μ, hμ, hg₀, hgu₀, hgw₀, hbp, hchar₀⟩ :=
    exists_conj_lang_twE6 (K := K) (L := L) (ζ := ζ) (u := u) halg e he hp hp2 hζ hu huF hup1
  let W0 : WeylGroup TwistTag.E6.tag :=
    (coxeterSystem TwistTag.E6.tag).wordProd
      CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.e6W0Word
  have hW0 : ∀ v, W0 • v = -(permLattice TwistTag.E6.perm v) :=
    fun v => CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.e6W0_smul v
  obtain ⟨N, hcop, hN, hcharx⟩ :=
    exists_char_pow_e6W0 (L := L) (w₀ := w₀) (b := fun i => ζ ^ μ i)
      hp hp2 hq W0 hW0 hbp hchar₀
  obtain ⟨g, w, σ, hg, hgu, hgw, hσ, hσμ⟩ :=
    exists_kernelWeyl_lang_twE6 (K := K) (L := L) (ζ := ζ) (u := u) (g₀ := g₀) (w₀ := w₀)
      (μ := μ) (W0 := W0) (N := N) hK hup hdown hp hμ hε hζ e he hg₀ huF hgu₀ hgw₀ hbp hcop hN
      hcharx
  refine ⟨g, hg, μ, w, σ, hμ, hgu, hgw, ?_, hσμ⟩
  intro x
  have hconv : (-ε) • ((w * W0) • K.extRoot x) =
      ε • (w • permLattice TwistTag.E6.perm (K.extRoot x)) := by
    rw [mul_smul, hW0 (K.extRoot x)]
    rw [smul_neg, neg_smul, smul_neg, neg_neg]
  rw [← hσ x]
  exact hconv.symm

end CFSG.HardMathSupport.Timmesfeld.CrossChar
