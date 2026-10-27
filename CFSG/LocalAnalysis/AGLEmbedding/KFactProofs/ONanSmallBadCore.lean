module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallInvolveComm
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOrbitsCubeCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneCoreData

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallBad

open scoped commutatorElement
open CFSG.AGLEmbedding.KFactProofs.OrbitsCube CFSG.AGLEmbedding.KFactProofs.RankOneCore
open CFSG.RankThree.SubgroupLists

theorem not_normalizerQuotientComm_of_witness {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) (hT : (T : Subgroup G) ≠ ⊥) {x y : G}
    (hx : x ∈ Subgroup.normalizer ((T : Subgroup G) : Set G))
    (hy : y ∈ Subgroup.normalizer ((T : Subgroup G) : Set G))
    (h : x * y * x⁻¹ * y⁻¹ ∉ (T : Subgroup G)) : ¬ NormalizerQuotientComm p G :=
  fun hc => h (hc T hT x hx y hy)

theorem commutator_not_mem_heisenberg {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (Q : Subgroup G) (hcard : Nat.card Q = p ^ 3) {x y : G}
    (hQ : Q = Subgroup.closure ({x, y} : Set G)) (hx : x ^ p = 1) (hz : ⁅x, y⁆ ≠ 1)
    {h₁ h₂ : G} (hh₁ : h₁ ∈ Subgroup.normalizer (Q : Set G))
    (hh₂ : h₂ ∈ Subgroup.normalizer (Q : Set G)) (a₁ b₁ c₁ d₁ e₁ f₁ a₂ b₂ c₂ d₂ e₂ f₂ : ℕ)
    (h₁x : h₁ * x * h₁⁻¹ = x ^ a₁ * y ^ b₁ * ⁅x, y⁆ ^ e₁)
    (h₁y : h₁ * y * h₁⁻¹ = x ^ c₁ * y ^ d₁ * ⁅x, y⁆ ^ f₁)
    (h₂x : h₂ * x * h₂⁻¹ = x ^ a₂ * y ^ b₂ * ⁅x, y⁆ ^ e₂)
    (h₂y : h₂ * y * h₂⁻¹ = x ^ c₂ * y ^ d₂ * ⁅x, y⁆ ^ f₂)
    (hne : (c₁ : ZMod p) * b₂ ≠ c₂ * b₁) : ⁅h₁, h₂⁆ ∉ Q := by
  intro hc
  have : Fact p.Prime := ⟨hp⟩
  have hxQ : x ∈ Q := hQ ▸ Subgroup.subset_closure (by simp)
  have hyQ : y ∈ Q := hQ ▸ Subgroup.subset_closure (by simp)
  have hnc : ∃ u ∈ Q, ∃ v ∈ Q, u * v ≠ v * u :=
    ⟨x, hxQ, y, hyQ, fun h' => hz (commutatorElement_eq_one_iff_mul_comm.2 h')⟩
  have hclass := commutator_le_center_of_card_pow_three hp Q hcard hnc
  set xS : Q := ⟨x, hxQ⟩ with hxS
  set yS : Q := ⟨y, hyQ⟩ with hyS
  have hcomm : ∀ u v : Q, (((⁅u, v⁆ : Q)) : G) = ⁅(u : G), (v : G)⁆ := fun u v => by
    simp [commutatorElement_def]
  let α₁ : MulAut Q := Q.normalizerMonoidHom ⟨h₁, hh₁⟩
  let α₂ : MulAut Q := Q.normalizerMonoidHom ⟨h₂, hh₂⟩
  have hα₁ : ∀ u : Q, ((α₁ u : Q) : G) = h₁ * u * h₁⁻¹ := fun u => rfl
  have hα₂ : ∀ u : Q, ((α₂ u : Q) : G) = h₂ * u * h₂⁻¹ := fun u => rfl
  have key : ∀ (α : MulAut Q) (h : G), (∀ u : Q, ((α u : Q) : G) = h * u * h⁻¹) →
      ∀ a b c d e f : ℕ, h * x * h⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ e →
        h * y * h⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ f →
        α xS = xS ^ a * yS ^ b * ⁅xS, yS⁆ ^ e ∧ α yS = xS ^ c * yS ^ d * ⁅xS, yS⁆ ^ f := by
    intro α h hα a b c d e f hhx hhy
    refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
    · rw [hα, hxS]
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, hcomm, hyS]
      exact hhx
    · rw [hα, hyS]
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, hcomm, hxS]
      exact hhy
  obtain ⟨hα₁x, hα₁y⟩ := key α₁ h₁ hα₁ a₁ b₁ c₁ d₁ e₁ f₁ h₁x h₁y
  obtain ⟨hα₂x, hα₂y⟩ := key α₂ h₂ hα₂ a₂ b₂ c₂ d₂ e₂ f₂ h₂x h₂y
  have hzS : ⁅xS, yS⁆ ≠ 1 := by
    intro h1
    apply hz
    have := congrArg Subtype.val h1
    rw [hcomm] at this
    simpa using this
  have hxS' : xS ^ p = 1 := Subtype.ext (by simpa [hxS] using hx)
  have hzc : ⁅xS, yS⁆ ∈ Subgroup.center Q := commutatorElement_mem_center hclass xS yS
  have hzp : ⁅xS, yS⁆ ^ p = 1 := by
    rw [← commutatorElement_pow_left hclass, hxS']
    simp [commutatorElement_def]
  have hzo : orderOf ⁅xS, yS⁆ = p := orderOf_eq_prime hzp hzS
  set cS : Q := ⟨⁅h₁, h₂⁆, hc⟩ with hcS
  have hrel : ∀ u : Q, α₁ (α₂ u) = cS * α₂ (α₁ u) * cS⁻¹ := by
    intro u
    apply Subtype.ext
    simp only [hα₁, hα₂, Subgroup.coe_mul, Subgroup.coe_inv, hcS]
    simp only [commutatorElement_def]
    group
  obtain ⟨w₁, hw₁, hA⟩ := map_normalForm hclass xS yS α₁ a₁ b₁ c₁ d₁ e₁ f₁ a₂ b₂
    (w := ⁅xS, yS⁆ ^ e₂) (pow_mem hzc e₂) hα₁x hα₁y
  obtain ⟨w₂, hw₂, hB⟩ := map_normalForm hclass xS yS α₂ a₂ b₂ c₂ d₂ e₂ f₂ a₁ b₁
    (w := ⁅xS, yS⁆ ^ e₁) (pow_mem hzc e₁) hα₂x hα₂y
  rw [← hα₂x] at hA
  rw [← hα₁x] at hB
  have hcentral : ∀ u : Q, ⁅cS, u⁆ ∈ Subgroup.center Q := fun u =>
    commutatorElement_mem_center hclass cS u
  have hAB : α₁ (α₂ xS) = ⁅cS, α₂ (α₁ xS)⁆ * α₂ (α₁ xS) := by
    rw [hrel]
    simp only [commutatorElement_def]
    group
  have hpair : ⁅α₁ (α₂ xS), yS⁆ = ⁅α₂ (α₁ xS), yS⁆ := by
    rw [hAB, commutatorElement_mul_left hclass]
    have h1 : ⁅⁅cS, α₂ (α₁ xS)⁆, yS⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.mp (hcentral _) yS).symm
    rw [h1, one_mul]
  have hyform : ∀ (i j : ℕ) (w : Q), w ∈ Subgroup.center Q →
      ⁅xS ^ i * yS ^ j * w, yS⁆ = ⁅xS, yS⁆ ^ i := by
    intro i j w hw
    have := commutator_normalForm hclass xS yS i j 0 1 hw (one_mem (Subgroup.center Q))
    simpa using this
  rw [hA, hyform _ _ _ hw₁, hB, hyform _ _ _ hw₂] at hpair
  have h2 := pow_eq_pow_iff_modEq.1 hpair
  rw [hzo] at h2
  have h3 := (ZMod.natCast_eq_natCast_iff _ _ _).2 h2
  push_cast at h3
  exact hne (by linear_combination h3)

theorem factorization_pow_mul {p k m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) (hm0 : m ≠ 0) :
    (p ^ k * m).factorization p = k := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero, Nat.Prime.factorization_pow hp,
    Finsupp.single_eq_same]

theorem conj_pow_pair {G : Type*} [Group G] {x y h : G} (hxy : Commute x y) {a b c d : ℕ}
    (hx : h * x * h⁻¹ = x ^ a * y ^ b) (hy : h * y * h⁻¹ = x ^ c * y ^ d) (i j : ℕ) :
    h * (x ^ i * y ^ j) * h⁻¹ = x ^ (a * i + c * j) * y ^ (b * i + d * j) := by
  have h1 := map_mul (MulAut.conj h) (x ^ i) (y ^ j)
  simp only [map_pow, MulAut.conj_apply] at h1
  rw [h1, hx, hy, (Commute.pow_pow hxy a b).mul_pow, (Commute.pow_pow hxy c d).mul_pow,
    ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, pow_add, pow_add]
  have h2 : Commute (y ^ (b * i)) (x ^ (c * j)) := (Commute.pow_pow hxy (c * j) (b * i)).symm
  calc x ^ (a * i) * y ^ (b * i) * (x ^ (c * j) * y ^ (d * j))
      = x ^ (a * i) * (y ^ (b * i) * x ^ (c * j)) * y ^ (d * j) := by group
    _ = x ^ (a * i) * (x ^ (c * j) * y ^ (b * i)) * y ^ (d * j) := by rw [h2.eq]
    _ = x ^ (a * i) * x ^ (c * j) * (y ^ (b * i) * y ^ (d * j)) := by group

theorem pow_pair_mul {G : Type*} [Group G] {x y : G} (hcm : Commute x y) (m n m' n' : ℕ) :
    (x ^ m * y ^ n) * (x ^ m' * y ^ n') = x ^ (m + m') * y ^ (n + n') := by
  have h2 : Commute (y ^ n) (x ^ m') := (Commute.pow_pow hcm m' n).symm
  calc x ^ m * y ^ n * (x ^ m' * y ^ n') = x ^ m * (y ^ n * x ^ m') * y ^ n' := by group
    _ = x ^ m * (x ^ m' * y ^ n) * y ^ n' := by rw [h2.eq]
    _ = x ^ (m + m') * y ^ (n + n') := by rw [pow_add, pow_add]; group

theorem commutator_not_mem_plane {G : Type*} [Group G] {x y : G} (hxy : x * y = y * x)
    (hx : x ^ 5 = 1) (hy : y ^ 5 = 1)
    (hind : ∀ m n : ℕ, x ^ m * y ^ n = 1 → (m : ZMod 5) = 0 ∧ (n : ZMod 5) = 0) {h₁ h₂ : G}
    (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℕ) (h₁x : h₁ * x * h₁⁻¹ = x ^ a₁ * y ^ b₁)
    (h₁y : h₁ * y * h₁⁻¹ = x ^ c₁ * y ^ d₁) (h₂x : h₂ * x * h₂⁻¹ = x ^ a₂ * y ^ b₂)
    (h₂y : h₂ * y * h₂⁻¹ = x ^ c₂ * y ^ d₂) (hne : (c₁ : ZMod 5) * b₂ ≠ c₂ * b₁) :
    ⁅h₁, h₂⁆ ∉ Subgroup.closure ({x, y} : Set G) := by
  intro hc
  have hcm : Commute x y := hxy
  have hQc : IsMulCommutative (Subgroup.closure ({x, y} : Set G)) := by
    refine Subgroup.isMulCommutative_closure ?_
    rintro a (rfl | rfl) b (rfl | rfl) hab
    · exact absurd rfl hab
    · exact hcm
    · exact hcm.symm
    · exact absurd rfl hab
  have hnorm : ∀ i j : ℕ, x ^ i * y ^ j ∈ Subgroup.closure ({x, y} : Set G) := fun i j =>
    Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  have hA : h₁ * (h₂ * x * h₂⁻¹) * h₁⁻¹ =
      x ^ (a₁ * a₂ + c₁ * b₂) * y ^ (b₁ * a₂ + d₁ * b₂) := by
    rw [h₂x, conj_pow_pair hcm h₁x h₁y]
  have hB : h₂ * (h₁ * x * h₁⁻¹) * h₂⁻¹ =
      x ^ (a₂ * a₁ + c₂ * b₁) * y ^ (b₂ * a₁ + d₂ * b₁) := by
    rw [h₁x, conj_pow_pair hcm h₂x h₂y]
  have hAB : h₁ * (h₂ * x * h₂⁻¹) * h₁⁻¹ =
      ⁅h₁, h₂⁆ * (h₂ * (h₁ * x * h₁⁻¹) * h₂⁻¹) * ⁅h₁, h₂⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  have hBQ : h₂ * (h₁ * x * h₁⁻¹) * h₂⁻¹ ∈ Subgroup.closure ({x, y} : Set G) := by
    rw [hB]
    exact hnorm _ _
  have hcB : ⁅h₁, h₂⁆ * (h₂ * (h₁ * x * h₁⁻¹) * h₂⁻¹) =
      (h₂ * (h₁ * x * h₁⁻¹) * h₂⁻¹) * ⁅h₁, h₂⁆ :=
    congrArg Subtype.val (hQc.is_comm.comm (⟨_, hc⟩ : Subgroup.closure ({x, y} : Set G)) ⟨_, hBQ⟩)
  have hAB' : h₁ * (h₂ * x * h₂⁻¹) * h₁⁻¹ = h₂ * (h₁ * x * h₁⁻¹) * h₂⁻¹ := by
    calc h₁ * (h₂ * x * h₂⁻¹) * h₁⁻¹
        = ⁅h₁, h₂⁆ * (h₂ * (h₁ * x * h₁⁻¹) * h₂⁻¹) * ⁅h₁, h₂⁆⁻¹ := hAB
      _ = (h₂ * (h₁ * x * h₁⁻¹) * h₂⁻¹) * ⁅h₁, h₂⁆ * ⁅h₁, h₂⁆⁻¹ := by rw [hcB]
      _ = h₂ * (h₁ * x * h₁⁻¹) * h₂⁻¹ := by group
  rw [hA, hB] at hAB'
  generalize hm : a₁ * a₂ + c₁ * b₂ = m at hAB'
  generalize hn : b₁ * a₂ + d₁ * b₂ = n at hAB'
  generalize hm' : a₂ * a₁ + c₂ * b₁ = m' at hAB'
  generalize hn' : b₂ * a₁ + d₂ * b₁ = n' at hAB'
  have hone : x ^ (m + 4 * m') * y ^ (n + 4 * n') = 1 := by
    rw [← pow_pair_mul hcm m n (4 * m') (4 * n'), hAB', pow_pair_mul hcm m' n' (4 * m') (4 * n')]
    have e1 : m' + 4 * m' = 5 * m' := by omega
    have e2 : n' + 4 * n' = 5 * n' := by omega
    rw [e1, e2, pow_mul, pow_mul, hx, hy]
    simp
  obtain ⟨h0, -⟩ := hind _ _ hone
  apply hne
  have h4 : (4 : ZMod 5) = -1 := by decide
  push_cast at h0
  rw [h4] at h0
  have e : (m : ZMod 5) = m' := by linear_combination h0
  rw [← hm, ← hm'] at e
  push_cast at e
  linear_combination e

end CFSG.AGLEmbedding.KFactProofs.SmallBad
