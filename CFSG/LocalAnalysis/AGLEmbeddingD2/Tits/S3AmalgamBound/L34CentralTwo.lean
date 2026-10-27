module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourL34Check
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Three
public import Certificates.Certificate295200

public section

namespace CFSG.ComponentClassification.PSL3Four

open CFSG.PSL3Four CFSG.PSL3Four.Native

section Model


theorem exists_rep_of_memTab {H : Subgroup (Equiv.Perm (Fin 42))} {T : Array Tab}
    (hH : Enumerates H T.toList) {x : Tab} (hx : memTab T x = true) :
    ∃ g ∈ H, TabRep x g := by
  obtain ⟨k, hk, rfl⟩ := memTab_iff.1 hx
  obtain ⟨g, hg, hrep⟩ := hH.sound _ (getElem!_mem hk)
  exact ⟨g, hg, hrep⟩

theorem mem_closure_pair_pow {G : Type*} [Group G] {a b : G} (hab : a * b = b * a)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) {x : G} (hx : x ∈ Subgroup.closure {a, b}) :
    ∃ i j : ℕ, x = a ^ i * b ^ j := by
  have hc : Commute a b := hab
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨i', j', rfl⟩ := hy
    refine ⟨i + i', j + j', ?_⟩
    have : b ^ j * a ^ i' = a ^ i' * b ^ j := ((hc.symm.pow_pow j i')).eq
    calc a ^ i * b ^ j * (a ^ i' * b ^ j') = a ^ i * (b ^ j * a ^ i') * b ^ j' := by group
      _ = a ^ i * (a ^ i' * b ^ j) * b ^ j' := by rw [this]
      _ = a ^ (i + i') * b ^ (j + j') := by rw [pow_add, pow_add]; group
  | inv x _ hx =>
    obtain ⟨i, j, rfl⟩ := hx
    refine ⟨2 * i, 2 * j, ?_⟩
    have h1 : a ^ i * a ^ (2 * i) = 1 := by
      rw [← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, ha, one_pow]
    have h2 : b ^ j * b ^ (2 * j) = 1 := by
      rw [← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, hb, one_pow]
    have hcom : b ^ j * a ^ (2 * i) = a ^ (2 * i) * b ^ j := ((hc.symm.pow_pow j (2 * i))).eq
    rw [inv_eq_iff_mul_eq_one]
    calc a ^ i * b ^ j * (a ^ (2 * i) * b ^ (2 * j))
        = a ^ i * (b ^ j * a ^ (2 * i)) * b ^ (2 * j) := by group
      _ = a ^ i * (a ^ (2 * i) * b ^ j) * b ^ (2 * j) := by rw [hcom]
      _ = (a ^ i * a ^ (2 * i)) * (b ^ j * b ^ (2 * j)) := by group
      _ = 1 := by rw [h1, h2, one_mul]

theorem pow_eq_pow_mod_three {G : Type*} [Group G] {a : G} (ha : a ^ 3 = 1) (i : ℕ) :
    a ^ i = a ^ (i % 3) := by
  conv_lhs => rw [← Nat.mod_add_div i 3, pow_add, pow_mul, ha, one_pow, mul_one]


theorem l34CentSpec :
    ∃ A₀ : Subgroup (Equiv.Perm (Fin 42)), A₀ ≤ S ∧ Nat.card A₀ = 9 ∧
      ∃ β ∈ R, β ^ 2 = 1 ∧ β ≠ 1 ∧ (∀ a ∈ A₀, β * a = a * β) ∧
        (∀ x ∈ R, (∀ a ∈ A₀, x * a = a * x) → ∃ c ∈ A₀, x = c ∨ x = c * β) ∧
        (∀ y ∈ R, (∀ a ∈ A₀, y * a * y⁻¹ ∈ A₀) → y * β = β * y) :=
  Certificates.certificate295200

end Model

end CFSG.ComponentClassification.PSL3Four

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four CFSG.PSL3Four.Native

theorem exists_rep_hom {X : Type} [Group X] {K : Subgroup X}
    [K.Normal] (hKc : Subgroup.centralizer (K : Set X) = ⊥) (ε : K ≃* ↥S) :
    ∃ ρ : X →* Equiv.Perm (Fin 42), Function.Injective ρ ∧ (∀ x, ρ x ∈ R) ∧
      ∀ (x : X) (k : K), ((ε (MulAut.conjNormal x k) : S) : Equiv.Perm (Fin 42)) =
        ρ x * (ε k : Equiv.Perm (Fin 42)) * (ρ x)⁻¹ := by
  obtain ⟨E, hE, -⟩ := full_automorphism_action
  let φ : X →* MulAut ↥S :=
    ((MulAut.congr ε).toMonoidHom).comp (MulAut.conjNormal : X →* MulAut K)
  let ρ : X →* Equiv.Perm (Fin 42) := (R.subtype).comp ((E.symm.toMonoidHom).comp φ)
  refine ⟨ρ, ?_, fun x => (E.symm (φ x)).2, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : E.symm (φ x) = 1 := Subtype.ext hx
    have h2 : φ x = 1 := by simpa using congrArg E h1
    have h3 : (MulAut.conjNormal x : MulAut K) = 1 := by
      have := (MulAut.congr ε).injective (h2.trans (map_one (MulAut.congr ε)).symm)
      exact this
    have hx' : x ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have := congrArg (fun f : MulAut K => ((f ⟨k, hk⟩ : K) : X)) h3
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc k * x = (x * k * x⁻¹) * x := by rw [this]
        _ = x * k := by group
    rw [hKc, Subgroup.mem_bot] at hx'
    exact hx'
  · intro x k
    have h1 := hE (E.symm (φ x)) (ε k)
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 : (φ x) (ε k) = ε (MulAut.conjNormal x k) := by
      simp [φ, MulAut.congr_apply]
    rw [h2] at h1
    simpa [ρ] using h1

theorem exists_equiv_map_eq {X : Type} [Group X] {K : Subgroup X}
    (ε : K ≃* ↥S) {A : Subgroup X} (hAK : A ≤ K) (hA9 : Nat.card A = 9)
    {A₀ : Subgroup (Equiv.Perm (Fin 42))} (hA₀S : A₀ ≤ S) (hA₀9 : Nat.card A₀ = 9) :
    ∃ ε' : K ≃* ↥S,
      (∀ (a : X) (ha : a ∈ A), ((ε' ⟨a, hAK ha⟩ : S) : Equiv.Perm (Fin 42)) ∈ A₀) ∧
      (∀ a ∈ A₀, ∃ (b : X) (hb : b ∈ A), ((ε' ⟨b, hAK hb⟩ : S) : Equiv.Perm (Fin 42)) = a) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS : Nat.card S = 20160 := card_S
  let P₀ : Subgroup ↥S := A₀.subgroupOf S
  let P₁ : Subgroup ↥S := (A.subgroupOf K).map ε.toMonoidHom
  have hP₀ : Nat.card P₀ = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀S).toEquiv, hA₀9]
  have hP₁ : Nat.card P₁ = 9 := by
    rw [Subgroup.card_map_of_injective ε.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hA9]
  have hidx : ∀ P : Subgroup ↥S, Nat.card P = 9 → ¬ 3 ∣ P.index := by
    intro P hP
    have h := P.index_mul_card
    rw [hP, hS] at h
    have : P.index = 2240 := by omega
    rw [this]
    norm_num
  have hp : ∀ P : Subgroup ↥S, Nat.card P = 9 → IsPGroup 3 P := fun P hP =>
    IsPGroup.of_card (n := 2) (by rw [hP]; norm_num)
  let Q₀ : Sylow 3 ↥S := (hp P₀ hP₀).toSylow (hidx P₀ hP₀)
  let Q₁ : Sylow 3 ↥S := (hp P₁ hP₁).toSylow (hidx P₁ hP₁)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥S Q₀ Q₁
  have hQg : P₁ = P₀.map (MulAut.conj g).toMonoidHom := by
    have h1 : (Q₁ : Subgroup ↥S) = (Q₀ : Subgroup ↥S).map (MulAut.conj g).toMonoidHom := by
      rw [← hg, Sylow.coe_subgroup_smul]
      rfl
    simpa [Q₀, Q₁, IsPGroup.toSylow_coe] using h1
  refine ⟨ε.trans (MulAut.conj g⁻¹), ?_, ?_⟩
  · intro a ha
    have h1 : ε ⟨a, hAK ha⟩ ∈ P₁ := ⟨⟨a, hAK ha⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
    rw [hQg] at h1
    obtain ⟨p, hp0, hpe⟩ := h1
    have h2 : ((ε.trans (MulAut.conj g⁻¹)) ⟨a, hAK ha⟩ : ↥S) = p := by
      have : ε ⟨a, hAK ha⟩ = g * p * g⁻¹ := hpe.symm
      simp [MulEquiv.trans_apply, MulAut.conj_apply, this, mul_assoc]
    rw [h2]
    exact Subgroup.mem_subgroupOf.1 hp0
  · intro a ha
    have h1 : (g * ⟨a, hA₀S ha⟩ * g⁻¹ : ↥S) ∈ P₁ := by
      rw [hQg]
      exact ⟨⟨a, hA₀S ha⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
    obtain ⟨k, hk, hke⟩ := h1
    refine ⟨k, Subgroup.mem_subgroupOf.1 hk, ?_⟩
    have : ε k = g * ⟨a, hA₀S ha⟩ * g⁻¹ := hke
    simp [MulEquiv.trans_apply, MulAut.conj_apply, this, mul_assoc]

@[expose] def KFactL34CentralTwo : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, IsL34Index d →
    ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
      Subgroup.centralizer (K : Set X) = ⊥ → Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ A : Subgroup X, A ≤ K → Nat.card A = 9 →
        ∀ t ∈ Subgroup.centralizer (A : Set X), (∃ k : ℕ, t ^ 2 ^ k = 1) →
          ∀ y ∈ Subgroup.normalizer (A : Set X), y * t = t * y

theorem kFactL34CentralTwo :
    KFactL34CentralTwo := by
  intro d hd X _ _ K hKn hKc ⟨e⟩ A hAK hA9 t ht ⟨k, htk⟩ y hy
  obtain ⟨ε₀⟩ := nonempty_equiv_S_of_index hd e
  obtain ⟨A₀, hA₀S, hA₀9, β, hβR, hβ2, hβ1, hβc, hcent, hnorm⟩ := l34CentSpec
  obtain ⟨ε, hεA, hεA₀⟩ := exists_equiv_map_eq ε₀ hAK hA9 hA₀S hA₀9
  obtain ⟨ρ, hρinj, hρR, hρ⟩ := exists_rep_hom hKc ε
  have hρt : ∀ a ∈ A₀, ρ t * a = a * ρ t := by
    intro a ha
    obtain ⟨b, hb, hba⟩ := hεA₀ a ha
    have h1 := hρ t ⟨b, hAK hb⟩
    have h2 : (MulAut.conjNormal t ⟨b, hAK hb⟩ : K) = ⟨b, hAK hb⟩ := by
      apply Subtype.ext
      show t * b * t⁻¹ = b
      rw [← Subgroup.mem_centralizer_iff.mp ht b hb]
      group
    rw [h2, hba] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1.symm
  have hρy : ∀ a ∈ A₀, ρ y * a * (ρ y)⁻¹ ∈ A₀ := by
    intro a ha
    obtain ⟨b, hb, hba⟩ := hεA₀ a ha
    have h1 := hρ y ⟨b, hAK hb⟩
    have hyb : y * b * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hy b).mp hb
    have h2 : (MulAut.conjNormal y ⟨b, hAK hb⟩ : K) = ⟨y * b * y⁻¹, hAK hyb⟩ := rfl
    rw [h2, hba] at h1
    rw [← h1]
    exact hεA _ hyb
  have hρtk : (ρ t) ^ 2 ^ k = 1 := by rw [← map_pow, htk, map_one]
  have hc9 : ∀ c ∈ A₀, c ^ 9 = 1 := by
    intro c hc
    have h := pow_card_eq_one' (G := A₀) (x := ⟨c, hc⟩)
    rw [hA₀9] at h
    exact congrArg Subtype.val h
  have hcop : ∀ c : Equiv.Perm (Fin 42), c ∈ A₀ → ∀ m : ℕ, c ^ 2 ^ m = 1 → c = 1 := by
    intro c hc m hm
    have h1 : orderOf c ∣ 9 := orderOf_dvd_of_pow_eq_one (hc9 c hc)
    have h2 : orderOf c ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
    have hcp : Nat.Coprime 9 (2 ^ m) := Nat.Coprime.pow_right m (by norm_num)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcp h1 h2)
  obtain ⟨c, hcA, hc⟩ := hcent (ρ t) (hρR t) hρt
  have hρt' : ρ t = 1 ∨ ρ t = β := by
    rcases hc with hc | hc
    · left
      rw [hc] at hρtk ⊢
      exact hcop c hcA k hρtk
    · right
      have hcom : Commute c β := (hβc c hcA).symm
      have h1 : (c * β) ^ 2 ^ (k + 1) = 1 := by
        rw [pow_succ, pow_mul]
        rw [← hc]
        rw [hρtk, one_pow]
      have hβp : β ^ 2 ^ (k + 1) = 1 := by
        rw [pow_succ, mul_comm, pow_mul, hβ2, one_pow]
      rw [hcom.mul_pow, hβp, mul_one] at h1
      have hc1 : c = 1 := hcop c hcA (k + 1) h1
      rw [hc, hc1, one_mul]
  have hcomm : ρ y * ρ t = ρ t * ρ y := by
    rcases hρt' with h | h
    · rw [h]; simp
    · rw [h]; exact hnorm (ρ y) (hρR y) hρy
  apply hρinj
  rw [map_mul, map_mul, hcomm]

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
