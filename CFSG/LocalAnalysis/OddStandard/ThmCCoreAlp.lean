module

public import CFSG.GroupTheory.FrobeniusNormalComplement

public section

namespace CFSG.OddStandard.ThmC.Core

open CFSG Subgroup CFSG.RankTwoShapes CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem exists_mem_sylow_of_alperin [Finite G] (S : Sylow 2 G)
    (hyp : ∀ Q : Subgroup G, IsAlperinSubgroup 2 (S : Subgroup G) Q →
      IsPGroup 2 (normalizer (Q : Set G) ⧸
        (centralizer (Q : Set G)).subgroupOf (normalizer (Q : Set G))))
    {P : Subgroup G} {c : G} (hc : AlperinDecomposition 2 (S : Subgroup G) P c) :
    ∃ u ∈ (S : Subgroup G), ∀ x ∈ P, u⁻¹ * x * u = c⁻¹ * x * c := by
  induction hc with
  | one => exact ⟨1, one_mem _, fun x _ => by group⟩
  | @step c n Q _ hQ hPQ hn ih =>
    obtain ⟨u, hu, hux⟩ := ih
    obtain ⟨s, hsS, hsN, hsC⟩ :=
      FrobeniusNormalComplement.exists_mul_mem_centralizer (hyp Q hQ) hQ.2.1 hn
    refine ⟨u * s, mul_mem hu hsS, fun x hx => ?_⟩
    have hy : c⁻¹ * x * c ∈ Q := by
      have h := hPQ ⟨x, hx, rfl⟩
      rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h
    have hsy : s⁻¹ * (c⁻¹ * x * c) * s ∈ Q := by
      have h := (mem_normalizer_iff.mp (inv_mem hsN) (c⁻¹ * x * c)).mp hy
      rwa [inv_inv] at h
    have hcomm := Subgroup.mem_centralizer_iff.mp hsC _ hsy
    calc (u * s)⁻¹ * x * (u * s) = s⁻¹ * (u⁻¹ * x * u) * s := by group
      _ = s⁻¹ * (c⁻¹ * x * c) * s := by rw [hux x hx]
      _ = (s⁻¹ * n)⁻¹ * ((s⁻¹ * n) * (s⁻¹ * (c⁻¹ * x * c) * s)) := by group
      _ = (s⁻¹ * n)⁻¹ * ((s⁻¹ * (c⁻¹ * x * c) * s) * (s⁻¹ * n)) := by rw [hcomm]
      _ = (c * n)⁻¹ * x * (c * n) := by group

omit [Group G] in
theorem isPGroup_automizer_of {G : Type*} [Group G] {Q : Subgroup G}
    (h : ∀ n ∈ normalizer (Q : Set G), ∃ a : ℕ, n ^ (2 ^ a) ∈ centralizer (Q : Set G)) :
    IsPGroup 2 (normalizer (Q : Set G) ⧸
      (centralizer (Q : Set G)).subgroupOf (normalizer (Q : Set G))) := by
  intro x
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨a, ha⟩ := h n n.2
  refine ⟨a, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact ha

theorem exists_pow_mem_centralizer_of_odd [Finite G] {Q : Subgroup G}
    (h : ∀ x ∈ normalizer (Q : Set G), Odd (orderOf x) → x ∈ centralizer (Q : Set G))
    (n : G) (hn : n ∈ normalizer (Q : Set G)) :
    ∃ a : ℕ, n ^ (2 ^ a) ∈ centralizer (Q : Set G) := by
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf n)
    (orderOf_pos n).ne'
  refine ⟨a, h _ (pow_mem hn _) ?_⟩
  have hdvd : 2 ^ a ∣ orderOf n := hab ▸ dvd_mul_right _ _
  rw [orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) hdvd, hab,
    Nat.mul_div_cancel_left _ (by positivity)]
  exact hb

theorem pow_mem_centralizer_conj {Q : Subgroup G} {g n : G} {k : ℕ}
    (h : (g * n * g⁻¹) ^ k ∈ centralizer ((Q.map (MulAut.conj g).toMonoidHom : Subgroup G) :
      Set G)) : n ^ k ∈ centralizer (Q : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : g * x * g⁻¹ ∈ (Q.map (MulAut.conj g).toMonoidHom : Subgroup G) :=
    ⟨x, hx, by simp⟩
  have h1 := Subgroup.mem_centralizer_iff.mp h _ hx'
  rw [conj_pow] at h1
  calc x * n ^ k = g⁻¹ * ((g * x * g⁻¹) * (g * n ^ k * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * n ^ k * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h1]
    _ = n ^ k * x := by group

theorem conj_mem_normalizer_map {Q : Subgroup G} {g n : G} (hn : n ∈ normalizer (Q : Set G)) :
    g * n * g⁻¹ ∈ normalizer ((Q.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 := (mem_normalizer_iff.mp hn x).mp hx
    exact ⟨n * x * n⁻¹, h1, by simp [mul_assoc]⟩
  · rintro ⟨x, hx, hxy⟩
    have hy : y = g * (n⁻¹ * x * n) * g⁻¹ := by
      have h1 : g * n * g⁻¹ * y * (g * n * g⁻¹)⁻¹ = g * x * g⁻¹ := by
        simpa using hxy.symm
      calc y = (g * n * g⁻¹)⁻¹ * (g * n * g⁻¹ * y * (g * n * g⁻¹)⁻¹) * (g * n * g⁻¹) := by group
        _ = (g * n * g⁻¹)⁻¹ * (g * x * g⁻¹) * (g * n * g⁻¹) := by rw [h1]
        _ = _ := by group
    have h2 : n⁻¹ * x * n ∈ Q := by
      have := (mem_normalizer_iff.mp (inv_mem hn) x).mp hx
      simpa using this
    exact ⟨n⁻¹ * x * n, h2, by rw [hy]; simp⟩

theorem exists_normalComplement_of_alperin [Finite G] (S : Sylow 2 G)
    (h : ∀ Q : Subgroup G, IsAlperinSubgroup 2 (S : Subgroup G) Q →
      ∀ x ∈ normalizer (Q : Set G), Odd (orderOf x) → x ∈ centralizer (Q : Set G)) :
    ∃ N : Subgroup G, IsNormalPComplement 2 N := by
  have hyp : ∀ Q : Subgroup G, IsAlperinSubgroup 2 (S : Subgroup G) Q →
      IsPGroup 2 (normalizer (Q : Set G) ⧸
        (centralizer (Q : Set G)).subgroupOf (normalizer (Q : Set G))) := fun Q hQ =>
    isPGroup_automizer_of (exists_pow_mem_centralizer_of_odd (h Q hQ))
  have hS : ∀ Q : Subgroup G, Q ≤ (S : Subgroup G) → ∀ n ∈ normalizer (Q : Set G),
      ∃ a : ℕ, n ^ (2 ^ a) ∈ centralizer (Q : Set G) := by
    intro Q hQS n hn
    have hPg : Q.map (MulAut.conj n⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
      rintro _ ⟨x, hx, rfl⟩
      have : n⁻¹ * x * n ∈ Q := by
        have := (mem_normalizer_iff.mp (inv_mem hn) x).mp hx
        simpa using this
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact hQS this
    obtain ⟨c, hc, hcg⟩ := alperin_centric_radical_fusion S hQS hPg
    obtain ⟨u, hu, hux⟩ := exists_mem_sylow_of_alperin S hyp hc
    have hux' : ∀ x ∈ Q, u⁻¹ * x * u = n⁻¹ * x * n := fun x hx => (hux x hx).trans (hcg x hx)
    have hcn : u⁻¹ * n ∈ centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hy : n * x * n⁻¹ ∈ Q := (mem_normalizer_iff.mp hn x).mp hx
      have := hux' _ hy
      calc x * (u⁻¹ * n) = u⁻¹ * (n * x * n⁻¹) * u * (u⁻¹ * n) := by
            rw [this]; group
        _ = (u⁻¹ * n) * x := by group
    have huN : u ∈ normalizer (Q : Set G) := by
      have : u = n * (u⁻¹ * n)⁻¹ := by group
      rw [this]
      exact mul_mem hn (inv_mem (Subgroup.centralizer_le_normalizer _ hcn))
    obtain ⟨b, hb⟩ := S.isPGroup' ⟨u, hu⟩
    have hu1 : u ^ (2 ^ b) = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    refine ⟨b, ?_⟩
    have heq : (QuotientGroup.mk (⟨u, huN⟩ : normalizer (Q : Set G)) :
        normalizer (Q : Set G) ⧸ (centralizer (Q : Set G)).subgroupOf (normalizer (Q : Set G))) =
        QuotientGroup.mk ⟨n, hn⟩ := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using hcn
    have h1 : (QuotientGroup.mk (⟨n, hn⟩ : normalizer (Q : Set G)) :
        normalizer (Q : Set G) ⧸ (centralizer (Q : Set G)).subgroupOf (normalizer (Q : Set G))) ^
        (2 ^ b) = 1 := by
      rw [← heq, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      show (((⟨u, huN⟩ : normalizer (Q : Set G)) ^ 2 ^ b : normalizer (Q : Set G)) : G) ∈ _
      rw [Subgroup.coe_pow]
      show u ^ 2 ^ b ∈ _
      rw [hu1]
      exact one_mem _
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hall : ∀ Q : Subgroup G, IsPGroup 2 Q → IsPGroup 2 (normalizer (Q : Set G) ⧸
      (centralizer (Q : Set G)).subgroupOf (normalizer (Q : Set G))) := by
    intro Q hQ
    apply isPGroup_automizer_of
    intro n hn
    obtain ⟨S', hQS'⟩ := hQ.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' S
    have hQg : Q.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : MulAut.conj g • x ∈ ((g • S' : Sylow 2 G) : Subgroup G) := by
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQS' hx)
      rw [hg] at h1
      simpa [MulAut.smul_def] using h1
    obtain ⟨a, ha⟩ := hS _ hQg _ (conj_mem_normalizer_map (g := g) hn)
    exact ⟨a, pow_mem_centralizer_conj ha⟩
  exact (frobenius_normal_p_complement 2).1.2 hall

theorem track_alperin [Finite G] (S : Sylow 2 G) (W : Set G)
    (hW : ∀ Q : Subgroup G, IsAlperinSubgroup 2 (S : Subgroup G) Q → ∀ w ∈ W, w ∈ Q →
      ∀ n ∈ normalizer (Q : Set G), n⁻¹ * w * n ∈ W)
    {u g : G} (huS : u ∈ (S : Subgroup G)) (hu : u ∈ W)
    (hg : g⁻¹ * u * g ∈ (S : Subgroup G)) : g⁻¹ * u * g ∈ W := by
  have hP : zpowers u ≤ (S : Subgroup G) := Subgroup.zpowers_le.2 huS
  have hPg : (zpowers u).map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.2 (by simpa using hg)
  obtain ⟨c, hc, hcg⟩ := alperin_centric_radical_fusion S hP hPg
  have hcu : c⁻¹ * u * c = g⁻¹ * u * g := hcg u (Subgroup.mem_zpowers u)
  rw [← hcu]
  have key : ∀ c', AlperinDecomposition 2 (S : Subgroup G) (zpowers u) c' → c'⁻¹ * u * c' ∈ W := by
    intro c' hc'
    induction hc' with
    | one => simpa using hu
    | @step c₀ n Q _ hQ hPQ hn ih =>
      have hmem : c₀⁻¹ * u * c₀ ∈ Q := by
        have h := hPQ ⟨u, Subgroup.mem_zpowers u, rfl⟩
        rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h
      have := hW Q hQ _ ih hmem n hn
      simpa [mul_assoc] using this
  exact key c hc

end CFSG.OddStandard.ThmC.Core
