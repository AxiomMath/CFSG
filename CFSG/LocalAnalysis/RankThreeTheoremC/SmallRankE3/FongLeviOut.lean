module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundCyc
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

theorem exists_outer_of_faithful {A : Type} [Group A] [Finite A] {K B : Subgroup A} {p : ℕ}
    (hp : p.Prime) (hKr : CFSG.Open.pRank p K ≤ 1) (hZ : Subgroup.center ↥K = ⊥)
    (hB : CFSG.Open.IsElemAbelian p B) (hBc : Nat.card B = p ^ 2)
    (hBK : B ≤ Subgroup.normalizer (K : Set A))
    (hnb : ∀ b ∈ B, b ≠ 1 → ¬ ∀ k ∈ K, b * k = k * b) :
    ∃ b ∈ B, ¬ ∃ k ∈ K, ∀ x ∈ K, b * x * b⁻¹ = k * x * k⁻¹ := by
  by_contra h
  have h2 : ∀ b ∈ B, ∃ k ∈ K, ∀ x ∈ K, b * x * b⁻¹ = k * x * k⁻¹ :=
    fun b hb => Classical.byContradiction fun hn => h ⟨b, hb, hn⟩
  have huniq : ∀ k k' : ↥K,
      (∀ x : ↥K, (k : A) * (x : A) * (k : A)⁻¹ = (k' : A) * (x : A) * (k' : A)⁻¹) → k = k' := by
    intro k k' hc
    have hz : k'⁻¹ * k ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have hg := hc g
      have key : ((k' : A)⁻¹ * (k : A)) * (g : A) * ((k' : A)⁻¹ * (k : A))⁻¹ = (g : A) := by
        calc ((k' : A)⁻¹ * (k : A)) * (g : A) * ((k' : A)⁻¹ * (k : A))⁻¹
            = (k' : A)⁻¹ * ((k : A) * (g : A) * (k : A)⁻¹) * (k' : A) := by group
          _ = (k' : A)⁻¹ * ((k' : A) * (g : A) * (k' : A)⁻¹) * (k' : A) := by rw [hg]
          _ = (g : A) := by group
      calc (g : A) * ((k' : A)⁻¹ * (k : A))
          = ((k' : A)⁻¹ * (k : A)) * (g : A) * ((k' : A)⁻¹ * (k : A))⁻¹
              * ((k' : A)⁻¹ * (k : A)) := by rw [key]
        _ = ((k' : A)⁻¹ * (k : A)) * (g : A) := by group
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hz
    exact hz.symm
  have h' : ∀ b : ↥B, ∃ k : ↥K, ∀ x : ↥K,
      (b : A) * (x : A) * (b : A)⁻¹ = (k : A) * (x : A) * (k : A)⁻¹ := by
    intro b
    obtain ⟨k, hk, hx⟩ := h2 (b : A) b.2
    exact ⟨⟨k, hk⟩, fun x => hx x x.2⟩
  choose κ₀ hκ₀ using h'
  have hmul : ∀ b b' : ↥B, κ₀ (b * b') = κ₀ b * κ₀ b' := by
    intro b b'
    apply huniq
    intro x
    have hd := hκ₀ b (κ₀ b')
    have hbx := hκ₀ b x
    calc ((κ₀ (b * b') : ↥K) : A) * (x : A) * ((κ₀ (b * b') : ↥K) : A)⁻¹
        = ((b * b' : ↥B) : A) * (x : A) * ((b * b' : ↥B) : A)⁻¹ := (hκ₀ (b * b') x).symm
      _ = (b : A) * ((b' : A) * (x : A) * (b' : A)⁻¹) * (b : A)⁻¹ := by
          simp only [Subgroup.coe_mul]
          group
      _ = (b : A) * (((κ₀ b' : ↥K) : A) * (x : A) * ((κ₀ b' : ↥K) : A)⁻¹) * (b : A)⁻¹ := by
          rw [hκ₀ b' x]
      _ = ((b : A) * ((κ₀ b' : ↥K) : A) * (b : A)⁻¹) * ((b : A) * (x : A) * (b : A)⁻¹) *
            ((b : A) * ((κ₀ b' : ↥K) : A) * (b : A)⁻¹)⁻¹ := by
          group
      _ = (((κ₀ b : ↥K) : A) * ((κ₀ b' : ↥K) : A) * ((κ₀ b : ↥K) : A)⁻¹) *
            (((κ₀ b : ↥K) : A) * (x : A) * ((κ₀ b : ↥K) : A)⁻¹) *
            (((κ₀ b : ↥K) : A) * ((κ₀ b' : ↥K) : A) * ((κ₀ b : ↥K) : A)⁻¹)⁻¹ := by
          rw [hd, hbx]
      _ = (((κ₀ b : ↥K) : A) * ((κ₀ b' : ↥K) : A)) * (x : A) *
            (((κ₀ b : ↥K) : A) * ((κ₀ b' : ↥K) : A))⁻¹ := by
          group
      _ = ((κ₀ b * κ₀ b' : ↥K) : A) * (x : A) * ((κ₀ b * κ₀ b' : ↥K) : A)⁻¹ := by
          simp only [Subgroup.coe_mul]
  obtain ⟨κ, hκ⟩ : ∃ κ : ↥B →* ↥K, ∀ b, κ b = κ₀ b :=
    ⟨MonoidHom.mk' κ₀ hmul, fun _ => rfl⟩
  have hinj : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    by_contra hb1
    have hκb : κ₀ b = 1 := by
      rw [← hκ b]
      exact hb
    have hne : (b : A) ≠ 1 := fun e => hb1 (Subtype.ext e)
    refine hnb (b : A) b.2 hne (fun k hk => ?_)
    have h3 : (b : A) * k * (b : A)⁻¹ = ((κ₀ b : ↥K) : A) * k * ((κ₀ b : ↥K) : A)⁻¹ :=
      hκ₀ b ⟨k, hk⟩
    rw [hκb] at h3
    simp only [Subgroup.coe_one, one_mul, inv_one, mul_one] at h3
    exact mul_inv_eq_iff_eq_mul.1 h3
  haveI := hB.1
  have hcomm : ∀ a b : ↥B, a * b = b * a := fun a b => mul_comm' a b
  have hpow : ∀ a : ↥B, a ^ p = 1 := fun a => Subtype.ext (by simpa using hB.2 (a : A) a.2)
  have hf : Function.Injective (K.subtype.comp κ) := K.subtype_injective.comp hinj
  have hH : (K.subtype.comp κ).range ≤ K := by
    intro y hy
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hy
    exact (κ b).2
  have hk2 : 2 ≤ CFSG.Open.pRank p K :=
    CFSG.SectionRank.le_pRank_of_injective hp.one_lt hcomm hpow hBc (K.subtype.comp κ) hf hH
  omega

theorem field_degree_of_faithful {A : Type} [Group A] [Finite A] {K B : Subgroup A} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hKr : CFSG.Open.pRank p K ≤ 1)
    (hZ : Subgroup.center ↥K = ⊥) (hB : CFSG.Open.IsElemAbelian p B) (hBc : Nat.card B = p ^ 2)
    (hBK : B ≤ Subgroup.normalizer (K : Set A))
    (hnb : ∀ b ∈ B, b ≠ 1 → ¬ ∀ k ∈ K, b * k = k * b)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n ℓ f : ℕ}
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n ℓ f)
    (hm : CFSG.Blueprint.LieModel ↥K t n ℓ f) (ht : t ≠ .Tits)
    (hdiv : ¬ p ∣ CFSG.ComponentClassification.CatLeaf.lieOrderDivisor t n (ℓ ^ f))
    (hD4 : ¬ (t = .POmegaPlus ∧ n = 4 ∧ p = 3)) (hT3 : ¬ (t = .trialityD4 ∧ p = 3)) :
    ∃ f₀ : ℕ, f = p * f₀ := by
  obtain ⟨b, hbB, hb⟩ := exists_outer_of_faithful hp hKr hZ hB hBc hBK hnb
  have hbK : b ∈ Subgroup.normalizer (K : Set A) := hBK hbB
  let α : MulAut ↥K := K.normalizerMonoidHom ⟨b, hbK⟩
  have hαp : α ^ p = 1 := by
    rw [← map_pow]
    have : (⟨b, hbK⟩ : Subgroup.normalizer (K : Set A)) ^ p = 1 :=
      Subtype.ext (by simpa using hB.2 b hbB)
    rw [this, map_one]
  have hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K := by
    rintro ⟨k, hk⟩
    apply hb
    refine ⟨(k : A), k.2, fun x hx => ?_⟩
    have h1 := congrArg (fun γ : MulAut ↥K => ((γ ⟨x, hx⟩ : ↥K) : A)) hk
    simpa [α, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] using h1.symm
  obtain ⟨f₀, hf, -⟩ := CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundCyc_holds ↥K t n ℓ f
    hadm hm ht p hp hp2 hdiv hD4 hT3 α hαp hαin
  exact ⟨f₀, hf⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
