module

public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSetup
public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSylow
public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterRegAut
public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSL3Core

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open scoped commutatorElement
open Matrix CFSG.AGLEmbedding CFSG.AGLEmbedding.ToralReduce CFSG.LocalAnalysis.ComponentInitial
  LinearFlag CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding.LinearThreeKit

structure ToralCfg {Y : Type} [Group Y] (L J : Subgroup Y) {K : Type} [Field K]
    (ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K) (d : ℕ) (u : Y) : Prop where
  hd : d = 1 ∨ d = 2
  hJ : ∀ l : ↥L, (l : Y) ∈ J ↔ ψ l ∈ stabilizer (flagSpace 3 K d)
  hu : u ∈ L ⊔ Subgroup.centralizer (L : Set Y)
  hu3 : u ^ 3 = 1
  huC : u ∉ Subgroup.centralizer (L : Set Y)
  hfix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J

variable {Y : Type} [Group Y] {L J : Subgroup Y} {K : Type} [Field K]
  {d : ℕ} {u : Y}

theorem toral_a [Finite K] (ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K) (ζ : Y) (hζL : ζ ∈ L) (hζC : ζ ∈ Subgroup.centralizer (L : Set Y))
    (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) :
    ∀ x ∈ L, x ∈ Subgroup.centralizer (L : Set Y) → x ∈ Subgroup.zpowers ζ := by
  intro x hxL hxC
  have : Finite ↥L := Finite.of_equiv _ ψ.symm.toEquiv
  set z : ↥L := ⟨ζ, hζL⟩ with hz
  have hzc : z ∈ Subgroup.center ↥L := (mem_center_iff_mem_centralizer z).mpr hζC
  have hxc : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := (mem_center_iff_mem_centralizer _).mpr hxC
  have hz3 : z ^ 3 = 1 := Subtype.ext (by simpa [hz] using hζ3)
  have hz1 : z ≠ 1 := fun h => hζ1 (by simpa [hz] using congrArg Subtype.val h)
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hle : Subgroup.zpowers z ≤ Subgroup.center ↥L := by
    rw [Subgroup.zpowers_le]; exact hzc
  have hcardc : Nat.card (Subgroup.center ↥L) ≤ 3 := by
    have h1 : Nat.card (Subgroup.center ↥L) = Nat.card (scalars 3 K) := by
      rw [← map_center_eq_scalars ψ, Subgroup.card_map_of_injective ψ.injective]
    rw [h1]; exact card_scalars_le_three
  have hcard : Nat.card (Subgroup.center ↥L) ≤ Nat.card (Subgroup.zpowers z) := by
    rw [Nat.card_zpowers, hord]; exact hcardc
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  have hmem : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.zpowers z := heq ▸ hxc
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact Subgroup.mem_zpowers_iff.mpr ⟨i, by simpa [hz] using congrArg Subtype.val hi⟩

theorem comm_u_of_comm_t {t : ↥L} {c : Y} (hc : c ∈ Subgroup.centralizer (L : Set Y)) {l : ↥L}
    (hlt : l * t = t * l) : (l : Y) * ((t : Y) * c) = ((t : Y) * c) * (l : Y) := by
  have h1 : (l : Y) * t = t * l := congrArg Subtype.val hlt
  have h2 : (l : Y) * c = c * l := Subgroup.mem_centralizer_iff.mp hc l l.2
  calc (l : Y) * (t * c) = (l * t) * c := by rw [mul_assoc]
    _ = (t * l) * c := by rw [h1]
    _ = t * (l * c) := by rw [mul_assoc]
    _ = t * (c * l) := by rw [h2]
    _ = (t * c) * l := by rw [mul_assoc]

theorem toral_b [Finite K] [CharP K 2] {ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K} (cfg : ToralCfg L J ψ d u) {ω : K} (hω1 : ω ≠ 1)
    (hω3 : ω ^ 3 = 1) :
    ∃ v ∈ L, v ^ 3 = 1 ∧ v ∉ Subgroup.centralizer (L : Set Y) ∧ v * u = u * v := by
  obtain ⟨t, c, hc, htc⟩ := exists_mul_of_mem_sup_centralizer' cfg.hu
  have hs := psi_not_mem_scalars ψ hc htc cfg.huC
  have hs3 := psi_pow_three_mem_scalars ψ hc htc cfg.hu3
  have hsJ : ψ t ∈ stabilizer (flagSpace 3 K d) :=
    (cfg.hJ t).mp (coe_mem_J hc htc cfg.hfix)
  obtain ⟨v, hvS, hv3, hvs⟩ := exists_comm_order_three hω1 hω3 cfg.hd hs hs3 hsJ
  refine ⟨((ψ.symm v : ↥L) : Y), (ψ.symm v).2, ?_, ?_, ?_⟩
  · have : (ψ.symm v) ^ 3 = 1 := by rw [← map_pow, hv3, map_one]
    simpa using congrArg Subtype.val this
  · intro hC
    apply hvS
    have := (ψ_mem_scalars_iff ψ (ψ.symm v)).mpr ((mem_center_iff_mem_centralizer _).mpr hC)
    simpa using this
  · have h1 : (ψ.symm v) * t = t * (ψ.symm v) := ψ.injective (by
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]; exact hvs)
    rw [← htc]
    exact comm_u_of_comm_t hc h1

theorem toral_c1_nine [Finite K] [CharP K 2] [Finite Y] {ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K}
    (cfg : ToralCfg L J ψ d u) {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    (h9 : 9 ∣ Nat.card K - 1) {Q X : Subgroup Y} (hJQ : J ≤ Q) (hX3 : IsPGroup 3 X)
    (hXL : X ≤ Subgroup.normalizer (L : Set Y)) (hXQ : X ≤ Q)
    (hXu : X ≤ Subgroup.centralizer ({u} : Set Y)) (hX81 : Nat.card X ≤ 3 ^ 4)
    (hmax : ∀ Z : Subgroup Y, IsPGroup 3 Z → Z ≤ Subgroup.normalizer (L : Set Y) → Z ≤ Q →
      Z ≤ Subgroup.centralizer ({u} : Set Y) → Nat.card Z ≤ Nat.card X) :
    ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t, c, hc, htc⟩ := exists_mul_of_mem_sup_centralizer' cfg.hu
  have hs3 := psi_pow_three_mem_scalars ψ hc htc cfg.hu3
  have hsJ : ψ t ∈ stabilizer (flagSpace 3 K d) := (cfg.hJ t).mp (coe_mem_J hc htc cfg.hfix)
  obtain ⟨c0, hc0, hcs⟩ := mem_scalars.mp hs3
  have hS3 : ((ψ t : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 =
      (c0 : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hcs, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  obtain ⟨x, hx⟩ := exists_eigenvalue_cube cfg.hd hsJ hS3
  have hx0 : x ≠ 0 := fun h0 => by
    rw [h0] at hx
    have : (c0 : K) = 0 := by rw [← hx]; norm_num
    exact c0.ne_zero this
  have hSx : ((ψ t : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 =
      (x ^ 3) • (1 : Matrix (Fin 3) (Fin 3) K) := by rw [hx]; exact hS3
  obtain ⟨b, j, hb, hbs⟩ := exists_eigenbasis_of_cube hx0 hω1 hω3 hSx
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd (K := K) (d := 9) h9
  set T := diagSub b 9 (by norm_num) with hT
  set TY : Subgroup Y := (T.map ψ.symm.toMonoidHom).map L.subtype with hTY
  have hTYmem : ∀ y : Y, y ∈ TY ↔ ∃ g ∈ T, ((ψ.symm g : ↥L) : Y) = y := by
    intro y
    constructor
    · rintro ⟨l, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨ψ.symm g, ⟨g, hg, rfl⟩, rfl⟩
  have hTYL : TY ≤ L := by
    intro y hy
    obtain ⟨g, -, rfl⟩ := (hTYmem y).mp hy
    exact (ψ.symm g).2
  have hTYu : TY ≤ Subgroup.centralizer ({u} : Set Y) := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := (hTYmem y).mp hy
    rw [Subgroup.mem_centralizer_singleton_iff, ← htc]
    have h1 : g * ψ t = ψ t * g := mul_comm_of_mem_diagSub hb hg _ hbs
    have h2 : (ψ.symm g) * t = t * (ψ.symm g) := ψ.injective (by
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]; exact h1)
    exact comm_u_of_comm_t hc h2
  have hTYQ : TY ≤ Q := by
    intro y hy
    have hyL := hTYL hy
    have hyu := Subgroup.mem_centralizer_singleton_iff.mp (hTYu hy)
    exact hJQ (cfg.hfix y hyL (by rw [mul_inv_eq_iff_eq_mul]; exact hyu.symm))
  have hTY3 : IsPGroup 3 TY := by
    intro y
    obtain ⟨g, hg, hgy⟩ := (hTYmem y).mp y.2
    refine ⟨2, ?_⟩
    have h9 : g ^ 9 = 1 := pow_eq_one_of_mem_diagSub hb hg
    refine Subtype.ext ?_
    have : (ψ.symm g) ^ 9 = 1 := by rw [← map_pow, h9, map_one]
    simpa [← hgy] using congrArg Subtype.val this
  have hTYcomm : ∀ a ∈ TY, ∀ a' ∈ TY, a * a' = a' * a := by
    intro a ha a' ha'
    obtain ⟨g, hg, rfl⟩ := (hTYmem a).mp ha
    obtain ⟨g', hg', rfl⟩ := (hTYmem a').mp ha'
    have := diagSub_comm hb hg hg'
    have h2 : (ψ.symm g) * (ψ.symm g') = (ψ.symm g') * (ψ.symm g) := by
      rw [← map_mul, ← map_mul, this]
    exact congrArg Subtype.val h2
  have hTYcard : 81 ≤ Nat.card TY := by
    have h1 := card_diagSub_ge hb (hm := (by norm_num : 0 < 9)) hζ
    rw [hTY, Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective ψ.symm.injective]
    simpa using h1
  have hTYle := hmax TY hTY3 (hTYL.trans Subgroup.le_normalizer) hTYQ hTYu
  exact abelian_of_max_isPGroup (N := Subgroup.normalizer (L : Set Y) ⊓ Q ⊓
    Subgroup.centralizer ({u} : Set Y)) hX3 (le_inf (le_inf hXL hXQ) hXu)
    (fun Z hZ hZN => hmax Z hZ (hZN.trans (inf_le_left.trans inf_le_left))
      (hZN.trans (inf_le_left.trans inf_le_right)) (hZN.trans inf_le_right))
    hTY3 (le_inf (le_inf (hTYL.trans Subgroup.le_normalizer) hTYQ) hTYu)
    (by omega) hTYcomm

theorem aut_diag_small [Finite K] [CharP K 2] [Finite Y]
    {ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K} (cfg : ToralCfg L J ψ d u) {ω : K}
    (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card K = 2 ^ f)
    (h3f : ¬ 3 ∣ f) {t : ↥L} {c : Y} (hc : c ∈ Subgroup.centralizer (L : Set Y))
    (htc : (t : Y) * c = u) {b : Fin 3 → Fin 3 → K} (hb : LinearIndependent K b)
    (hb0 : (ψ t : Matrix (Fin 3) (Fin 3) K) *ᵥ b 0 = b 0)
    (hb1 : (ψ t : Matrix (Fin 3) (Fin 3) K) *ᵥ b 1 = ω • b 1)
    (hb2 : (ψ t : Matrix (Fin 3) (Fin 3) K) *ᵥ b 2 = ω ^ 2 • b 2) {Q : Subgroup Y}
    (hQJ : ∀ x ∈ Q, x ∈ Subgroup.normalizer (L : Set Y) → ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    {x : Y} (hxL : x ∈ Subgroup.normalizer (L : Set Y)) (hxQ : x ∈ Q)
    (hxu : x * u * x⁻¹ = u) (hx3 : ∃ k : ℕ, x ^ 3 ^ k = 1) :
    ∃ (A : GL (Fin 3) K) (a : Fin 3 → K),
      normAut ψ ⟨x, hxL⟩ =
        CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A ∧
      (∀ i, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = a i • b i) ∧
      normAut ψ ⟨x, hxL⟩ ^ 3 = 1 := by
  have hsJ : ψ t ∈ stabilizer (flagSpace 3 K d) := (cfg.hJ t).mp (coe_mem_J hc htc cfg.hfix)
  set xN : ↥(Subgroup.normalizer (L : Set Y)) := ⟨x, hxL⟩ with hxN
  have hxNc : (xN : Y) = x := rfl
  obtain ⟨k, hk3⟩ := hx3
  have hβpow : (normAut ψ xN) ^ 3 ^ k = 1 := by
    rw [← map_pow]
    have : xN ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk3)
    rw [this, map_one]
  obtain ⟨z, hzc, hz⟩ := exists_center_of_conj hc htc xN hxu
  obtain ⟨c', hc'3, hzc'⟩ := mem_scalars.mp ((ψ_mem_scalars_iff ψ z).mpr hzc)
  have hc'3' : (c' : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc'3, Units.val_one]
  have hβs : ((normAut ψ xN (ψ t) : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = (c' : K) • ((ψ t : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) := by
    rw [normAut_apply, hz, map_mul, Matrix.SpecialLinearGroup.coe_mul, hzc',
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  have hβJ : (stabilizer (flagSpace 3 K d)).map (normAut ψ xN).toMonoidHom =
      stabilizer (flagSpace 3 K d) := by
    have hiff : ∀ g : Matrix.SpecialLinearGroup (Fin 3) K,
        normAut ψ xN g ∈ stabilizer (flagSpace 3 K d) ↔ g ∈ stabilizer (flagSpace 3 K d) := by
      intro g
      obtain ⟨l, rfl⟩ := ψ.surjective g
      rw [normAut_apply, ← cfg.hJ, ← cfg.hJ, coe_normalizerMonoidHom, hxNc]
      constructor
      · intro h
        have h1 := hQJ x⁻¹ (Subgroup.inv_mem _ hxQ) (Subgroup.inv_mem _ hxL) _ h
        simpa [mul_assoc] using h1
      · intro h
        exact hQJ x hxQ hxL _ h
    refine Subgroup.ext fun g => ⟨?_, fun hg => ⟨(normAut ψ xN).symm g, ?_, by simp⟩⟩
    · rintro ⟨h, hh, rfl⟩
      exact (hiff h).mpr hh
    · exact (hiff _).mp (by rw [MulEquiv.apply_symm_apply]; exact hg)
  obtain ⟨A, a, hA, hAa⟩ := three_pow_aut_diagonal hf hk h3f hω1 hω3 cfg.hd hb hb0 hb1 hb2 hsJ
    hβpow hc'3' hβs hβJ
  refine ⟨A, a, hA, hAa, ?_⟩
  rw [hA]
  exact slConjugation_cube_eq_one hk h3f hω3 hb hb0 hb1 hb2 hAa (hA ▸ hβpow)

theorem toral_c1_small [Finite K] [CharP K 2] [Finite Y]
    {ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K}
    (cfg : ToralCfg L J ψ d u) {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card K = 2 ^ f) (h3f : ¬ 3 ∣ f) (h9 : ¬ 9 ∣ Nat.card K - 1) {Q X : Subgroup Y}
    (hQJ : ∀ x ∈ Q, x ∈ Subgroup.normalizer (L : Set Y) → ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (hX3 : IsPGroup 3 X) (hXL : X ≤ Subgroup.normalizer (L : Set Y)) (hXQ : X ≤ Q)
    (hXu : X ≤ Subgroup.centralizer ({u} : Set Y)) :
    ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (L : Set Y) := by
  obtain ⟨t, c, hc, htc⟩ := exists_mul_of_mem_sup_centralizer' cfg.hu
  have hs := psi_not_mem_scalars ψ hc htc cfg.huC
  have hs3 := psi_pow_three_mem_scalars ψ hc htc cfg.hu3
  have hsJ : ψ t ∈ stabilizer (flagSpace 3 K d) := (cfg.hJ t).mp (coe_mem_J hc htc cfg.hfix)
  have hs31 := pow_three_eq_one_of_not_nine_dvd h9 cfg.hd hsJ hs3
  obtain ⟨b, hb, hb0, hb1, hb2⟩ := exists_eigenbasis_of_pow_three (coe_pow_eq_one hs31)
    (ψ t).2 (ne_smul_one_of_notMem_scalars hs) hω1 hω3
  have key : ∀ (x : Y) (hx : x ∈ X), ∃ (A : GL (Fin 3) K) (a : Fin 3 → K),
      normAut ψ ⟨x, hXL hx⟩ =
        CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A ∧
      ∀ i, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = a i • b i := by
    intro x hx
    have hxu : x * u * x⁻¹ = u := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hXu hx)
      rw [mul_inv_eq_iff_eq_mul]; exact this
    obtain ⟨A, a, h1, h2, -⟩ := aut_diag_small cfg hω1 hω3 hf hk h3f hc htc hb hb0 hb1 hb2 hQJ
      (hXL hx) (hXQ hx) hxu (by
        obtain ⟨k, hk3⟩ := hX3 ⟨x, hx⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk3⟩)
    exact ⟨A, a, h1, h2⟩
  intro a ha a' ha'
  obtain ⟨A, aa, hA, hAa⟩ := key a ha
  obtain ⟨A', aa', hA', hAa'⟩ := key a' ha'
  have hcomm : normAut ψ ⟨a, hXL ha⟩ * normAut ψ ⟨a', hXL ha'⟩ =
      normAut ψ ⟨a', hXL ha'⟩ * normAut ψ ⟨a, hXL ha⟩ := by
    rw [hA, hA']
    exact slConjugation_comm_of_diag hb hAa hAa'
  have h1 : normAut ψ ⁅(⟨a, hXL ha⟩ : ↥(Subgroup.normalizer (L : Set Y))),
      ⟨a', hXL ha'⟩⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  have := (normAut_eq_one_iff ψ _).mp h1
  simpa [commutatorElement_def] using this

theorem toralF_b_small [Finite K] [CharP K 2] [Finite Y]
    {ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K}
    (cfg : ToralCfg L J ψ d u) {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card K = 2 ^ f) (h3f : ¬ 3 ∣ f) (h9 : ¬ 9 ∣ Nat.card K - 1) {Q : Subgroup Y}
    (hQJ : ∀ x ∈ Q, x ∈ Subgroup.normalizer (L : Set Y) → ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (huL : u ∈ L) :
    ∀ x ∈ Subgroup.normalizer (L : Set Y), x ∈ Q → x * u = u * x → (∃ k : ℕ, x ^ 3 ^ k = 1) →
      x ^ 3 ∈ Subgroup.centralizer (L : Set Y) := by
  intro x hxL hxQ hxu hx3
  have hc : (1 : Y) ∈ Subgroup.centralizer (L : Set Y) := Subgroup.one_mem _
  have htc : ((⟨u, huL⟩ : ↥L) : Y) * 1 = u := mul_one u
  set t : ↥L := ⟨u, huL⟩ with ht
  have hs := psi_not_mem_scalars ψ hc htc cfg.huC
  have hs3 := psi_pow_three_mem_scalars ψ hc htc cfg.hu3
  have hsJ : ψ t ∈ stabilizer (flagSpace 3 K d) := (cfg.hJ t).mp (coe_mem_J hc htc cfg.hfix)
  have hs31 := pow_three_eq_one_of_not_nine_dvd h9 cfg.hd hsJ hs3
  obtain ⟨b, hb, hb0, hb1, hb2⟩ := exists_eigenbasis_of_pow_three (coe_pow_eq_one hs31)
    (ψ t).2 (ne_smul_one_of_notMem_scalars hs) hω1 hω3
  have hxu' : x * u * x⁻¹ = u := by rw [mul_inv_eq_iff_eq_mul]; exact hxu
  obtain ⟨A, a, -, -, h3⟩ := aut_diag_small cfg hω1 hω3 hf hk h3f hc htc hb hb0 hb1 hb2 hQJ hxL
    hxQ hxu' hx3
  have : normAut ψ ⟨x ^ 3, Subgroup.pow_mem _ hxL 3⟩ = 1 := by
    have e : (⟨x ^ 3, Subgroup.pow_mem _ hxL 3⟩ : ↥(Subgroup.normalizer (L : Set Y))) =
        (⟨x, hxL⟩ : ↥(Subgroup.normalizer (L : Set Y))) ^ 3 := rfl
    rw [e, map_pow]; exact h3
  exact (normAut_eq_one_iff ψ _).mp this

theorem toralF_b_big [Finite K] [CharP K 2] [Finite Y]
    {ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K} (cfg : ToralCfg L J ψ d u) {ω : K}
    (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) (h9 : 9 ∣ Nat.card K - 1) {Q : Subgroup Y} (hJQ : J ≤ Q)
    (huL : u ∈ L) {Yg X : Subgroup Y} (hY3 : IsPGroup 3 Yg)
    (hYL : Yg ≤ Subgroup.normalizer (L : Set Y)) (hXY : X ≤ Yg) (hXQ : X ≤ Q)
    (hXu : X ≤ Subgroup.centralizer ({u} : Set Y))
    (hmax : ∀ Z : Subgroup Y, IsPGroup 3 Z → Z ≤ Subgroup.normalizer (L : Set Y) → Z ≤ Q →
      Z ≤ Subgroup.centralizer ({u} : Set Y) → Nat.card Z ≤ Nat.card X) :
    ∀ y ∈ Yg, y * u * y⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : (1 : Y) ∈ Subgroup.centralizer (L : Set Y) := Subgroup.one_mem _
  have htc : ((⟨u, huL⟩ : ↥L) : Y) * 1 = u := mul_one u
  set t : ↥L := ⟨u, huL⟩ with ht
  have hs := psi_not_mem_scalars ψ hc htc cfg.huC
  have hsJ : ψ t ∈ stabilizer (flagSpace 3 K d) := (cfg.hJ t).mp (coe_mem_J hc htc cfg.hfix)
  have hs31 : ψ t ^ 3 = 1 := by
    rw [← map_pow]
    have : t ^ 3 = 1 := Subtype.ext (by simpa [ht] using cfg.hu3)
    rw [this, map_one]
  obtain ⟨b, hb, hb0, hb1, hb2⟩ := exists_eigenbasis_of_pow_three (coe_pow_eq_one hs31)
    (ψ t).2 (ne_smul_one_of_notMem_scalars hs) hω1 hω3
  let r : Fin 3 → K := ![1, ω, ω ^ 2]
  have hr : Function.Injective r := cubeRoots_injective hω1 hω3
  have hbs : ∀ i, (ψ t : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = r i • b i := by
    refine forall_fin_three ?_ ?_ ?_
    · show _ = (1 : K) • b 0
      rw [one_smul]; exact hb0
    · exact hb1
    · exact hb2
  have hKne : Nat.card K - 1 ≠ 0 := by
    have : 1 < Nat.card K := Finite.one_lt_card
    omega
  obtain ⟨m, t₀, ht0, hmt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hKne 3 (by norm_num)
  have hm2 : 2 ≤ m := by
    by_contra hlt
    push Not at hlt
    interval_cases m <;> simp at hmt <;> omega
  have hc3m : 0 < 3 ^ m := pow_pos (by norm_num) m
  set T := diagSub b (3 ^ m) hc3m with hT
  set TY : Subgroup Y := (T.map ψ.symm.toMonoidHom).map L.subtype with hTY
  have hTYmem : ∀ y : Y, y ∈ TY ↔ ∃ g ∈ T, ((ψ.symm g : ↥L) : Y) = y := by
    intro y
    constructor
    · rintro ⟨l, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨ψ.symm g, ⟨g, hg, rfl⟩, rfl⟩
  have hTYL : TY ≤ L := by
    intro y hy
    obtain ⟨g, -, rfl⟩ := (hTYmem y).mp hy
    exact (ψ.symm g).2
  have hTYu : TY ≤ Subgroup.centralizer ({u} : Set Y) := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := (hTYmem y).mp hy
    rw [Subgroup.mem_centralizer_singleton_iff, ← htc]
    have h1 : g * ψ t = ψ t * g := mul_comm_of_mem_diagSub hb hg _ hbs
    have h2 : (ψ.symm g) * t = t * (ψ.symm g) := ψ.injective (by
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]; exact h1)
    exact comm_u_of_comm_t hc h2
  have hTYQ : TY ≤ Q := by
    intro y hy
    have hyL := hTYL hy
    have hyu := Subgroup.mem_centralizer_singleton_iff.mp (hTYu hy)
    exact hJQ (cfg.hfix y hyL (by rw [mul_inv_eq_iff_eq_mul]; exact hyu.symm))
  have hTY3 : IsPGroup 3 TY := by
    intro y
    obtain ⟨g, hg, hgy⟩ := (hTYmem y).mp y.2
    refine ⟨m, ?_⟩
    have h9' : g ^ 3 ^ m = 1 := pow_eq_one_of_mem_diagSub hb hg
    refine Subtype.ext ?_
    have : (ψ.symm g) ^ 3 ^ m = 1 := by rw [← map_pow, h9', map_one]
    simpa [← hgy] using congrArg Subtype.val this
  have hXTY : X ≤ Subgroup.normalizer (TY : Set Y) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun l hl => ?_
    obtain ⟨g, hg, rfl⟩ := (hTYmem l).mp hl
    have hxN : x ∈ Subgroup.normalizer (L : Set Y) := hYL (hXY hx)
    set xN : ↥(Subgroup.normalizer (L : Set Y)) := ⟨x, hxN⟩ with hxNdef
    have hxu : x * u * x⁻¹ = u := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hXu hx)
      rw [mul_inv_eq_iff_eq_mul]; exact this
    have hβs : normAut ψ xN (ψ t) = ψ t := by
      rw [normAut_apply]
      congr 1
      refine Subtype.ext ?_
      rw [coe_normalizerMonoidHom]
      exact hxu
    have hβT : normAut ψ xN g ∈ T := by
      refine mem_diagSub_of_comm hb hr hbs ?_ hc3m ?_
      · have h1 : g * ψ t = ψ t * g := mul_comm_of_mem_diagSub hb hg _ hbs
        have := congrArg (normAut ψ xN) h1
        rw [map_mul, map_mul, hβs] at this
        exact this
      · rw [← map_pow, pow_eq_one_of_mem_diagSub hb hg, map_one]
    refine (hTYmem _).mpr ⟨normAut ψ xN g, hβT, ?_⟩
    have := normAut_apply ψ xN (ψ.symm g)
    rw [MulEquiv.apply_symm_apply] at this
    have h2 : ψ.symm (normAut ψ xN g) = (Subgroup.normalizerMonoidHom L xN) (ψ.symm g) := by
      rw [this, MulEquiv.symm_apply_apply]
    rw [h2, coe_normalizerMonoidHom]
  have hX3 : IsPGroup 3 X := IsPGroup.to_le hY3 hXY
  have hTYX : TY ≤ X := by
    have hsup3 : IsPGroup 3 (X ⊔ TY : Subgroup Y) := hX3.to_sup_of_normal_right' hTY3 hXTY
    have hXL' : X ≤ Subgroup.normalizer (L : Set Y) := hXY.trans hYL
    have hle := hmax (X ⊔ TY) hsup3 (sup_le hXL' (hTYL.trans Subgroup.le_normalizer))
      (sup_le hXQ hTYQ) (sup_le hXu hTYu)
    have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : X ≤ X ⊔ TY) hle
    exact heq ▸ le_sup_right
  set R : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) :=
    (Yg.subgroupOf L).map ψ.toMonoidHom with hR
  have hR3 : IsPGroup 3 R := (hY3.comap_subtype (K := L)).map ψ.toMonoidHom
  have hTR : diagSub b (3 ^ m) hc3m ≤ R := by
    intro g hg
    refine ⟨ψ.symm g, ?_, by simp⟩
    exact Subgroup.mem_subgroupOf.mpr (hXY (hTYX ((hTYmem _).mpr ⟨g, hg, rfl⟩)))
  intro y hy
  have hyN : y ∈ Subgroup.normalizer (L : Set Y) := hYL hy
  set yN : ↥(Subgroup.normalizer (L : Set Y)) := ⟨y, hyN⟩ with hyNdef
  obtain ⟨k, hk3⟩ := hY3 ⟨y, hy⟩
  have hβpow : (normAut ψ yN) ^ 3 ^ k = 1 := by
    rw [← map_pow]
    have : yN ^ 3 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk3)
    rw [this, map_one]
  have hRle : R.map (normAut ψ yN).toMonoidHom ≤ R := by
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    refine ⟨Subgroup.normalizerMonoidHom L yN l, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.mpr ?_
      rw [coe_normalizerMonoidHom]
      exact Yg.mul_mem (Yg.mul_mem hy (Subgroup.mem_subgroupOf.mp hl)) (Yg.inv_mem hy)
    · simp [normAut_apply]
  have hβR : R.map (normAut ψ yN).toMonoidHom = R := by
    refine Subgroup.eq_of_le_of_card_ge hRle ?_
    have hinj : Function.Injective (normAut ψ yN).toMonoidHom := (normAut ψ yN).injective
    exact (Subgroup.card_map_of_injective (K := R) hinj).ge
  obtain ⟨c', hc'3, hβs⟩ := aut_apply_eq_scalar_smul_of_three_group hω1 hω3 hm2 hmt ht0 hb hb0 hb1
    hb2 hs hR3 hTR hβpow hβR
  set w : ↥L := (Subgroup.normalizerMonoidHom L yN t) * t⁻¹ with hw
  have hwY : (w : Y) = y * u * y⁻¹ * u⁻¹ := by
    rw [hw, Subgroup.coe_mul, Subgroup.coe_inv, coe_normalizerMonoidHom]
  have hc'0 : c' ≠ 0 := fun h0 => by rw [h0] at hc'3; simp at hc'3
  have hψw : ψ w ∈ scalars 3 K := by
    refine ⟨Units.mk0 c' hc'0, Units.ext (by simpa using hc'3), ?_⟩
    rw [hw, map_mul, map_inv, ← normAut_apply, Matrix.SpecialLinearGroup.coe_mul, hβs,
      Matrix.smul_mul]
    have : ((ψ t : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((ψ t)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    rw [this, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    rfl
  have hwc := (mem_center_iff_mem_centralizer w).mp ((ψ_mem_scalars_iff ψ w).mp hψw)
  rw [hwY] at hwc
  exact hwc

open CFSG.AGLEmbedding.ParabPrime in
theorem perfectJoin_conj_le {x : Y} (hx : ∀ j ∈ J, x * j * x⁻¹ ∈ J) {z : Y}
    (hz : z ∈ perfectJoin J) : x * z * x⁻¹ ∈ perfectJoin J := by
  have hU : ⁅(perfectJoin J).map (MulAut.conj x).toMonoidHom,
      (perfectJoin J).map (MulAut.conj x).toMonoidHom⁆ =
      (perfectJoin J).map (MulAut.conj x).toMonoidHom := by
    rw [← Subgroup.map_commutator, perfectJoin_perfect]
  have hle : (perfectJoin J).map (MulAut.conj x).toMonoidHom ≤ J := by
    rintro _ ⟨p, hp, rfl⟩
    exact hx p (perfectJoin_le J hp)
  exact le_perfectJoin hle hU ⟨z, hz, by simp [MulAut.conj_apply]⟩

open CFSG.AGLEmbedding.ParabPrime in
theorem toralF_a [Finite K] [CharP K 2] [Finite Y]
    {ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K} (cfg : ToralCfg L J ψ d u) {Q : Subgroup Y}
    (hJL : J ≤ L) (hQJ : ∀ x ∈ Q, x ∈ Subgroup.normalizer (L : Set Y) → ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (hjoin : u ∈ perfectJoin J ⊔ Subgroup.centralizer (L : Set Y)) :
    ∀ r ∈ L, r⁻¹ * u ∈ Subgroup.centralizer (L : Set Y) → r ^ 3 = 1 ∧
      ∀ x ∈ Subgroup.normalizer (L : Set Y), x ∈ Q → x * u = u * x → (∃ k : ℕ, x ^ 3 ^ k = 1) →
        x * r = r * x := by
  have hPL : perfectJoin J ≤ L := (perfectJoin_le J).trans hJL
  have hu' := hjoin
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (hPL.trans (ToralCensus.le_normalizer_centralizer L))] at hu'
  obtain ⟨j, hj, c, hc, hjc⟩ := hu'
  set t : ↥L := ⟨j, hPL hj⟩ with ht
  have htc : (t : Y) * c = u := hjc
  set V : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) :=
    ((perfectJoin J).subgroupOf L).map ψ.toMonoidHom with hV
  have hVp : ⁅V, V⁆ = V := by
    rw [hV, ← Subgroup.map_commutator]
    congr 1
    refine Subgroup.map_injective L.subtype_injective ?_
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPL, perfectJoin_perfect]
  have hVs : V ≤ stabilizer (flagSpace 3 K d) := by
    rintro _ ⟨l, hl, rfl⟩
    exact (cfg.hJ l).mp ((perfectJoin_le J) (Subgroup.mem_subgroupOf.mp hl))
  have htV : ψ t ∈ V := ⟨t, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
  have hs3 := psi_pow_three_mem_scalars ψ hc htc cfg.hu3
  have hs31 : ψ t ^ 3 = 1 :=
    eq_one_of_mem_scalars_of_perfect cfg.hd hVs hVp (V.pow_mem htV 3) hs3
  intro r hr hru
  set r' : ↥L := ⟨r, hr⟩ with hr'
  have hwc : (r'⁻¹ * t : ↥L) ∈ Subgroup.center ↥L := by
    rw [mem_center_iff_mem_centralizer]
    have h1 : ((r'⁻¹ * t : ↥L) : Y) = (r⁻¹ * u) * c⁻¹ := by
      rw [← htc, Subgroup.coe_mul, Subgroup.coe_inv]
      show r⁻¹ * (t : Y) = r⁻¹ * ((t : Y) * c) * c⁻¹
      group
    rw [h1]
    exact Subgroup.mul_mem _ hru (Subgroup.inv_mem _ hc)
  set w : ↥L := r'⁻¹ * t with hw
  have hwscal : ψ w ∈ scalars 3 K := (ψ_mem_scalars_iff ψ w).mpr hwc
  have hrw : r' = t * w⁻¹ := by rw [hw]; group
  have hw3 : w ^ 3 = 1 := ψ.injective (by rw [map_pow, pow_three_of_mem_scalars hwscal, map_one])
  have ht3 : t ^ 3 = 1 := ψ.injective (by rw [map_pow, hs31, map_one])
  have hcomm : Commute t w⁻¹ :=
    Commute.inv_right (show Commute t w from (Subgroup.mem_center_iff.mp hwc t))
  refine ⟨?_, ?_⟩
  · have : r' ^ 3 = 1 := by
      rw [hrw, hcomm.mul_pow, ht3, inv_pow, hw3]; simp
    simpa [hr'] using congrArg Subtype.val this
  · intro x hxN hxQ hxu hx3
    set xN : ↥(Subgroup.normalizer (L : Set Y)) := ⟨x, hxN⟩ with hxNdef
    have hxu' : x * u * x⁻¹ = u := by rw [mul_inv_eq_iff_eq_mul]; exact hxu
    obtain ⟨k, hk3⟩ := hx3
    have hβpow : (normAut ψ xN) ^ 3 ^ k = 1 := by
      rw [← map_pow]
      have : xN ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk3)
      rw [this, map_one]
    obtain ⟨z, hzc, hz⟩ := exists_center_of_conj hc htc xN hxu'
    have hzP : (z : Y) ∈ perfectJoin J := by
      have h1 : ((Subgroup.normalizerMonoidHom L xN t : ↥L) : Y) = x * j * x⁻¹ := by
        rw [coe_normalizerMonoidHom]
      have h2 : x * j * x⁻¹ ∈ perfectJoin J := perfectJoin_conj_le (hQJ x hxQ hxN) hj
      have h3 : ((t * z : ↥L) : Y) ∈ perfectJoin J := by rw [← hz, h1]; exact h2
      rw [Subgroup.coe_mul] at h3
      have := (perfectJoin J).mul_mem ((perfectJoin J).inv_mem hj) h3
      simpa [ht] using this
    have hzV : ψ z ∈ V := ⟨z, Subgroup.mem_subgroupOf.mpr hzP, rfl⟩
    have hz1 : z = 1 := by
      have := eq_one_of_mem_scalars_of_perfect cfg.hd hVs hVp hzV
        ((ψ_mem_scalars_iff ψ z).mpr hzc)
      exact ψ.injective (by rw [this, map_one])
    have hxt : Subgroup.normalizerMonoidHom L xN t = t := by rw [hz, hz1, mul_one]
    have hxw : Subgroup.normalizerMonoidHom L xN w⁻¹ = w⁻¹ := by
      have h1 := aut_fixes_scalars hβpow
        ((ψ_mem_scalars_iff ψ w⁻¹).mpr ((Subgroup.center ↥L).inv_mem hwc))
      rw [normAut_apply] at h1
      exact ψ.injective h1
    have hxr : Subgroup.normalizerMonoidHom L xN r' = r' := by
      rw [hrw, map_mul, hxt, hxw]
    have := congrArg Subtype.val hxr
    rw [coe_normalizerMonoidHom] at this
    simp only [hr'] at this
    exact (mul_inv_eq_iff_eq_mul.mp this)


end CFSG.HardMathSupport.Curtis.Coordinator
