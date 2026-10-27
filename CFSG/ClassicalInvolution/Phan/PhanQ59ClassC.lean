module

public import CFSG.ClassicalInvolution.Phan.PhanQ58Side
public import CFSG.ClassicalInvolution.Phan.PhanQ56CaseI

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan

section ClassC

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem exists_cone_rational [Finite F] [Finite K] (hodd : Odd (Nat.card F)) (h2 : (2 : K) ≠ 0)
    (hε : ε ≠ 0) {σ : K ≃+* K} (hσ : ∀ x, σ x = D.τ x) (hσu : IsUnitaryInvolution σ) {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hFq : Nat.card F = q) (hq : 5 ≤ q) {a b c r : V8 K}
    (ha : ffK D a) (hb : ffK D b) (hc : ffK D c) (hab : ColK D a b) (hbc : ColK D b c)
    (hac : ColK D a c) (hr : r ∈ Submodule.span K {a, b, c}) (hr0 : r ≠ 0)
    (hrc : conj D r = r) :
    ∃ e, ffK D e ∧ ColK D a e ∧ ColK D b e ∧ ColK D c e ∧
      (∃ W, PhanSolid D W ∧ a ∈ W ∧ b ∈ W ∧ e ∈ W) ∧
      (∃ W, PhanSolid D W ∧ b ∈ W ∧ c ∈ W ∧ e ∈ W) ∧
      (∃ W, PhanSolid D W ∧ c ∈ W ∧ a ∈ W ∧ e ∈ W) := by
  classical
  have hP : ∀ u ∈ Submodule.span K {a, b}, ∀ v ∈ Submodule.span K {a, b}, B8 u v = 0 :=
    ts_pair ha.1 hb.1 hab.1
  have haP : a ∈ Submodule.span K {a, b} := Submodule.subset_span (by simp)
  have hbP : b ∈ Submodule.span K {a, b} := Submodule.subset_span (by simp)
  obtain ⟨W₀, hW₀, hPW₀⟩ : ∃ W₀, PhanSolid D W₀ ∧ Submodule.span K {a, b} ≤ W₀ := by
    refine exists_phanSolid_of_nondeg D hP ?_ (by rw [hab.finrank_span D]; norm_num) hodd h2 hε hσ
    intro u hu hu'
    exact hab.eq_zero_of_her D hu (hu' a haP) (hu' b hbP)
  have haW : a ∈ W₀ := hPW₀ haP
  have hbW : b ∈ W₀ := hPW₀ hbP
  have hPl := ts_triple ha.1 hb.1 hc.1 hab.1 hac.1 hbc.1
  have haPl : a ∈ Submodule.span K {a, b, c} := Submodule.subset_span (by simp)
  have hbPl : b ∈ Submodule.span K {a, b, c} := Submodule.subset_span (by simp)
  have hcPl : c ∈ Submodule.span K {a, b, c} := Submodule.subset_span (by simp)
  have hPPl : Submodule.span K {a, b} ≤ Submodule.span K {a, b, c} := by
    rw [Submodule.span_le]
    rintro z (rfl | rfl)
    · exact haPl
    · exact hbPl
  have hQr : Q8 r = 0 := by
    have h1 := hPl r hr r hr
    rw [B8_self] at h1
    exact (mul_eq_zero.1 h1).resolve_left h2
  have hrad : ∀ w ∈ Submodule.span K {a, b, c}, her D r w = 0 ∧ her D w r = 0 :=
    fun w hw => rat_her_zero D hrc (hPl r hr w hw)
  obtain ⟨r₁, hr₁, hrr⟩ := decomp_rat D hW₀ hrc
  have hr₁0 : r₁ ≠ 0 := by
    rintro rfl
    apply hr0
    rw [hrr, conj_zero', add_zero]
  have har₁ : her D a r₁ = 0 := by
    rw [← B8_rat_eq D hW₀ hrr hr₁ haW]
    exact hPl r hr a haPl
  have hbr₁ : her D b r₁ = 0 := by
    rw [← B8_rat_eq D hW₀ hrr hr₁ hbW]
    exact hPl r hr b hbPl
  have hr₁a : her D r₁ a = 0 := by rw [her_conj_symm D a r₁, har₁, map_zero]
  have hr₁b : her D r₁ b = 0 := by rw [her_conj_symm D b r₁, hbr₁, map_zero]
  have hr₁r₁ : her D r₁ r₁ = 0 := her_r1_self D hW₀ h2 hrr hr₁ hQr
  have hr₁r : her D r₁ r = 0 := by
    have h1 : her D r₁ r = B8 r₁ r := by
      unfold her
      rw [hrc]
    rw [h1, hrr, B8_add_right, hW₀.ts _ hr₁ _ hr₁, zero_add]
    exact hr₁r₁
  have hrr₁ : her D r r₁ = 0 := by rw [her_conj_symm D r₁ r, hr₁r, map_zero]
  have hrad₁ : ∀ z ∈ Submodule.span K {a, b}, her D z r₁ = 0 ∧ her D r₁ z = 0 :=
    fun z hz => her_zero_of_mem_span_pair D har₁ hbr₁ hz
  obtain ⟨s, t, u, hstu⟩ := mem_span_triple' hr
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hr0
    have hmem : r ∈ W₀ := by
      rw [hstu, zero_smul, add_zero]
      exact W₀.add_mem (W₀.smul_mem _ haW) (W₀.smul_mem _ hbW)
    exact hW₀.inf r hmem (by rw [hrc]; exact hmem)
  obtain ⟨α, β, γ, hcdec⟩ : ∃ α β γ : K, c = α • a + β • b + γ • r := by
    refine ⟨-(u⁻¹ * s), -(u⁻¹ * t), u⁻¹, ?_⟩
    have h1 : u • c = r - s • a - t • b := by
      rw [hstu]
      abel
    calc c = u⁻¹ • (u • c) := by rw [smul_smul, inv_mul_cancel₀ hu0, one_smul]
      _ = u⁻¹ • (r - s • a - t • b) := by rw [h1]
      _ = (-(u⁻¹ * s)) • a + (-(u⁻¹ * t)) • b + u⁻¹ • r := by module
  have hβ : β ≠ 0 := by
    rintro rfl
    apply hac.2
    rw [hcdec, zero_smul, add_zero]
    exact gram_eq_zero_of_rad D a r α γ (hrad a haPl).2 (hrad a haPl).1 (hrad r hr).1
  have hα : α ≠ 0 := by
    rintro rfl
    apply hbc.2
    rw [hcdec, zero_smul, zero_add]
    exact gram_eq_zero_of_rad D b r β γ (hrad b hbPl).2 (hrad b hbPl).1 (hrad r hr).1
  have hc₀P : α • a + β • b ∈ Submodule.span K {a, b} := Submodule.mem_span_pair.2 ⟨α, β, rfl⟩
  have hc₀W : α • a + β • b ∈ W₀ := hPW₀ hc₀P
  have hc₀Pl : α • a + β • b ∈ Submodule.span K {a, b, c} := hPPl hc₀P
  have hc₀rad := hrad _ hc₀Pl
  have hher_c₀ : her D (α • a + β • b) (α • a + β • b) = her D c c := by
    rw [hcdec]
    exact (her_add_rad D (α • a + β • b) (α • a + β • b) r γ γ hc₀rad.2 hc₀rad.1
      (hrad r hr).1).symm
  have hffc₀ : ffK D (α • a + β • b) :=
    ⟨hW₀.Q_eq_zero D h2 hc₀W, by rw [hher_c₀]; exact hc.2⟩
  obtain ⟨e₀, he₀P, hffe₀, hcole₀⟩ := PhanSolid.exists_colK_in_plane D hW₀ h2 hε hσ hσu hK
    haW hbW ha hb hab {a, b, α • a + β • b}
    (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨haW, ha⟩
      · exact ⟨hbW, hb⟩
      · exact ⟨hc₀W, hffc₀⟩)
    (lt_of_le_of_lt (Nat.mul_le_mul_right _ Finset.card_le_three) (three_card_lt hq))
  obtain ⟨α', β', he₀eq⟩ := Submodule.mem_span_pair.1 he₀P
  have hae₀ : ColK D a e₀ := hcole₀ a (by simp)
  have hbe₀ : ColK D b e₀ := hcole₀ b (by simp)
  have hce₀ : ColK D (α • a + β • b) e₀ := hcole₀ _ (by simp)
  have hβ' : β' ≠ 0 := by
    rintro rfl
    apply hae₀.2
    rw [← he₀eq, zero_smul, add_zero]
    exact gram_smul_self D a α'
  have hα' : α' ≠ 0 := by
    rintro rfl
    apply hbe₀.2
    rw [← he₀eq, zero_smul, zero_add]
    exact gram_smul_self D b β'
  have hFcard : ({0, ((β' * γ) * D.τ β + β * D.τ (β' * γ)) / (β * D.τ β),
      ((α' * γ) * D.τ α + α * D.τ (α' * γ)) / (α * D.τ α)} : Finset K).card < Nat.card F := by
    have := Finset.card_le_three (a := (0 : K)) (b := ((β' * γ) * D.τ β + β * D.τ (β' * γ)) /
      (β * D.τ β)) (c := ((α' * γ) * D.τ α + α * D.τ (α' * γ)) / (α * D.τ α))
    omega
  obtain ⟨f₀, hf₀⟩ := exists_alg_not_mem hFcard
  have hf : D.τ (algebraMap F K f₀) = algebraMap F K f₀ := D.tau_alg f₀
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hf₀
  obtain ⟨hf0, hfz₁, hfz₂⟩ := hf₀
  have hN₁ := norm_sub_ne D hβ hf hf0 hfz₁
  have hN₂ := norm_sub_ne D hα hf hf0 hfz₂
  have he₀W : e₀ ∈ W₀ := hPW₀ he₀P
  have he₀Pl : e₀ ∈ Submodule.span K {a, b, c} := hPPl he₀P
  have heW : e₀ + algebraMap F K f₀ • r₁ ∈ W₀ := W₀.add_mem he₀W (W₀.smul_mem _ hr₁)
  have he₀r₁ := hrad₁ e₀ he₀P
  have hc₀r₁ := hrad₁ _ hc₀P
  have her₁ : her D (e₀ + algebraMap F K f₀ • r₁) r₁ = 0 := by
    rw [her_add_left, her_smul_left, he₀r₁.1, hr₁r₁, mul_zero, add_zero]
  have hQe : Q8 (e₀ + algebraMap F K f₀ • r₁) = 0 := hW₀.Q_eq_zero D h2 heW
  have hher_e : her D (e₀ + algebraMap F K f₀ • r₁) (e₀ + algebraMap F K f₀ • r₁) =
      her D e₀ e₀ :=
    her_add_rad D e₀ e₀ r₁ _ _ he₀r₁.1 he₀r₁.2 hr₁r₁
  have hffe : ffK D (e₀ + algebraMap F K f₀ • r₁) := ⟨hQe, by rw [hher_e]; exact hffe₀.2⟩
  have hae : ColK D a (e₀ + algebraMap F K f₀ • r₁) := by
    refine ⟨hW₀.ts _ haW _ heW, ?_⟩
    have h := gram_add_rad D a e₀ r₁ 0 (algebraMap F K f₀) har₁ hr₁a he₀r₁.1 he₀r₁.2 hr₁r₁
    rw [zero_smul, add_zero] at h
    rw [h]
    exact hae₀.2
  have hbe : ColK D b (e₀ + algebraMap F K f₀ • r₁) := by
    refine ⟨hW₀.ts _ hbW _ heW, ?_⟩
    have h := gram_add_rad D b e₀ r₁ 0 (algebraMap F K f₀) hbr₁ hr₁b he₀r₁.1 he₀r₁.2 hr₁r₁
    rw [zero_smul, add_zero] at h
    rw [h]
    exact hbe₀.2
  have hB_r_e : B8 r (e₀ + algebraMap F K f₀ • r₁) = 0 := by
    rw [B8_rat_eq D hW₀ hrr hr₁ heW]
    exact her₁
  have hce : ColK D c (e₀ + algebraMap F K f₀ • r₁) := by
    refine ⟨?_, ?_⟩
    · rw [hcdec, B8_add_left, B8_add_left, B8_smul_left, B8_smul_left, B8_smul_left,
        hW₀.ts _ haW _ heW, hW₀.ts _ hbW _ heW, hB_r_e]
      simp
    · have her_er : her D (e₀ + algebraMap F K f₀ • r₁) r = 0 := by
        rw [her_add_left, her_smul_left, (hrad e₀ he₀Pl).2, hr₁r, mul_zero, add_zero]
      have her_re : her D r (e₀ + algebraMap F K f₀ • r₁) = 0 := by
        rw [her_conj_symm D (e₀ + algebraMap F K f₀ • r₁) r, her_er, map_zero]
      have h1 := gram_add_rad D (α • a + β • b) (e₀ + algebraMap F K f₀ • r₁) r γ 0
        (hrad _ hc₀Pl).2 (hrad _ hc₀Pl).1 her_er her_re (hrad r hr).1
      rw [zero_smul, add_zero, ← hcdec] at h1
      have h2' := gram_add_rad D (α • a + β • b) e₀ r₁ 0 (algebraMap F K f₀)
        hc₀r₁.1 hc₀r₁.2 he₀r₁.1 he₀r₁.2 hr₁r₁
      rw [zero_smul, add_zero] at h2'
      rw [h1, h2']
      exact hce₀.2
  have hQc : Q8 c = 0 := hc.1
  have hcdef : c = α • a + β • b + γ • (r₁ + conj D r₁) := by rw [hcdec, hrr]
  have hedef : e₀ + algebraMap F K f₀ • r₁ = α' • a + β' • b + algebraMap F K f₀ • r₁ := by
    rw [← he₀eq]
  have hcdef' : c = β • b + α • a + γ • (r₁ + conj D r₁) := by rw [hcdef]; abel
  have hedef' : e₀ + algebraMap F K f₀ • r₁ = β' • b + α' • a + algebraMap F K f₀ • r₁ := by
    rw [hedef]; abel
  refine ⟨e₀ + algebraMap F K f₀ • r₁, hffe, hae, hbe, hce, ⟨W₀, hW₀, haW, hbW, heW⟩, ?_, ?_⟩
  · exact side_solid D hodd h2 hε hσ hW₀ hbW haW hr₁ hr₁0 hab.symm hr₁b hr₁a hf hα' hN₂ hcdef'
      hedef' hb.1 hQc hQe hbc (hW₀.ts _ hbW _ heW) hce.1
  · obtain ⟨W, hW, haW', hcW', heW'⟩ := side_solid D hodd h2 hε hσ hW₀ haW hbW hr₁ hr₁0 hab
      hr₁a hr₁b hf hβ' hN₁ hcdef hedef ha.1 hQc hQe hac (hW₀.ts _ haW _ heW) hce.1
    exact ⟨W, hW, hcW', haW', heW'⟩

end ClassC

end CFSG.ClassicalInvolution.PhanQ
