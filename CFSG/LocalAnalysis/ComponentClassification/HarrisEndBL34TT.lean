module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEnd413L34d
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

theorem EndB.exists_conj_le_T (hs : Setting46e t L p f S w z V i j) (hw2 : orderOf w = 2)
    (hT64 : Nat.card ↥(zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) = 64) {x : X} (hxD : x ∈ S ⊓ L)
    (hx2 : x ^ 2 = 1) {c : X} (hc : c * t * c⁻¹ = x * t) {R : Subgroup X}
    (hRle : R ≤ centralizer ({x * t} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})
    (hRp : IsPGroup 2 R) (hβR : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ R) (hxtR : x * t ∈ R)
    (hzR : z ∈ R) (hzc : ∀ r ∈ R, r * z = z * r) (h64 : 64 ≤ Nat.card R) :
    ∃ d : X, ∀ r ∈ R, d⁻¹ * r * d ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) ^ 2 = 1 :=
    hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp
    (hs.standing.config.le_centralizer hxD.2)
  have hxt2 : (x * t) ^ 2 = 1 := by
    rw [(show Commute x t from hxt).mul_pow, hx2, ht2, one_mul]
  have hRt : ∀ r ∈ R, c⁻¹ * r * c ∈ centralizer ({t} : Set X) := by
    intro r hr
    rw [mem_centralizer_singleton_iff]
    have h1 : r * (x * t) = (x * t) * r :=
      mem_centralizer_singleton_iff.mp (mem_inf.mp (hRle hr)).1
    calc c⁻¹ * r * c * t = c⁻¹ * (r * (c * t * c⁻¹)) * c := by group
      _ = c⁻¹ * (r * (x * t)) * c := by rw [hc]
      _ = c⁻¹ * ((x * t) * r) * c := by rw [h1]
      _ = c⁻¹ * ((c * t * c⁻¹) * r) * c := by rw [hc]
      _ = t * (c⁻¹ * r * c) := by group
  have hPH : R.map (MulAut.conj c⁻¹).toMonoidHom ≤ centralizer ({t} : Set X) := by
    rintro _ ⟨r, hr, rfl⟩
    have := hRt r hr
    simpa [MulAut.conj_apply] using this
  obtain ⟨S', hS', hPS'⟩ := exists_isSylowOf_ge (hRp.map _) hPH
  obtain ⟨h₁, hh₁H, hh₁S⟩ := hs.sylow.exists_mem_conj hS'
  have hdS : ∀ r ∈ R, (c * h₁)⁻¹ * r * (c * h₁) ∈ S := by
    intro r hr
    have h1 : c⁻¹ * r * c ∈ S' := hPS' ⟨r, hr, by simp⟩
    have h2 := (hh₁S _).mp h1
    rwa [show h₁⁻¹ * (c⁻¹ * r * c) * h₁ = (c * h₁)⁻¹ * r * (c * h₁) by group] at h2
  set d := c * h₁ with hd
  set R'' := R.map (MulAut.conj d⁻¹).toMonoidHom with hR''
  have hconj : ∀ g : X, (MulAut.conj d⁻¹).toMonoidHom g = d⁻¹ * g * d := fun g => by
    simp
  have hR''S : R'' ≤ S := by
    rintro _ ⟨r, hr, rfl⟩
    rw [hconj]
    exact hdS r hr
  set T := zpowers t ⊔ (S ⊓ L) ⊔ zpowers w with hT
  have hu : w ^ (orderOf w / 2) = w := by rw [hw2]; norm_num
  have hR''T : R'' ≤ T := by
    by_cases hST : S = T
    · exact hST ▸ hR''S
    obtain ⟨-, -, -, -, hcardS, -, hCu, -⟩ :=
      hs.standing.lemma41_of_lift hs.sylow hs.setup.lift hs.setup.gen3
    rw [← hT] at hcardS hCu
    have hR''card : 64 ≤ Nat.card R'' := by
      rw [hR'', Subgroup.card_map_of_injective (MulAut.conj d⁻¹).injective]
      exact h64
    set J := R''.subgroupOf S with hJ
    have hJcard : Nat.card J = Nat.card R'' :=
      Nat.card_congr (subgroupOfEquivOfLe hR''S).toEquiv
    have hidx : J.index ≤ 2 := by
      have h := J.card_mul_index
      rw [hJcard] at h
      by_contra hlt
      have : 64 * 3 ≤ Nat.card R'' * J.index := Nat.mul_le_mul hR''card (by omega)
      omega
    have hRn : ∀ s ∈ S, ∀ r ∈ R'', s * r * s⁻¹ ∈ R'' := by
      intro s hs' r hr
      have hpos : J.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      rcases (show J.index = 1 ∨ J.index = 2 by omega) with h1 | h2
      · have hJt := Subgroup.index_eq_one.mp h1
        have hsr : (⟨s * r * s⁻¹, mul_mem (mul_mem hs' (hR''S hr)) (inv_mem hs')⟩ : ↥S) ∈ J := by
          rw [hJt]
          exact mem_top _
        exact hsr
      · have hn := Subgroup.normal_of_index_eq_two h2
        exact hn.conj_mem ⟨r, hR''S hr⟩ hr ⟨s, hs'⟩
    set F := omegaCenter R'' with hF
    have hFS : F ≤ S := fun g hg => hR''S hg.1
    have hFn : ∀ g ∈ S ⊓ L, ∀ y ∈ F, g * y * g⁻¹ ∈ F := by
      intro g hg y hy
      obtain ⟨hyR, hyc, hy2⟩ := hy
      refine ⟨hRn g hg.1 y hyR, fun r hr => ?_, ?_⟩
      · have h1 := hyc (g⁻¹ * r * g) (by
          have := hRn g⁻¹ (inv_mem hg.1) r hr
          rwa [inv_inv] at this)
        calc r * (g * y * g⁻¹) = g * ((g⁻¹ * r * g) * y) * g⁻¹ := by group
          _ = g * (y * (g⁻¹ * r * g)) * g⁻¹ := by rw [h1]
          _ = g * y * g⁻¹ * r := by group
      · rw [sq, show g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ by group, ← sq, hy2,
          mul_one, mul_inv_cancel]
    have hFX := hs.setup.le_X_of_normal_S hFS hFn (fun y hy => hy.2.2)
    have hBR : zpowers (x * t) ⊔ zpowers z ⊔ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≤
        omegaCenter R := by
      refine sup_le (sup_le (zpowers_le.mpr ⟨hxtR, fun r hr => ?_, hxt2⟩)
        (zpowers_le.mpr ⟨hzR, hzc, hz2⟩)) (zpowers_le.mpr ⟨hβR, fun r hr => ?_, hβ2⟩)
      · exact mem_centralizer_singleton_iff.mp (mem_inf.mp (hRle hr)).1
      · exact mem_centralizer_singleton_iff.mp (mem_inf.mp (hRle hr)).2
    set B := (zpowers (x * t) ⊔ zpowers z ⊔ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j)).map
      (MulAut.conj d⁻¹).toMonoidHom with hB
    have hBF : B ≤ F := by
      rintro _ ⟨g, hg, rfl⟩
      obtain ⟨hgR, hgc, hg2⟩ := hBR hg
      refine ⟨⟨g, hgR, rfl⟩, ?_, by rw [← map_pow, hg2, map_one]⟩
      rintro _ ⟨r, hr, rfl⟩
      rw [← map_mul, ← map_mul, hgc r hr]
    have hBcard : Nat.card B = 8 := by
      rw [hB, Subgroup.card_map_of_injective (MulAut.conj d⁻¹).injective,
        hs.card_closure_xt_z_beta hxD hx2]
    have hBX : B = closure {t, w ^ (orderOf w / 2), z} :=
      Subgroup.eq_of_le_of_card_ge (hBF.trans hFX) (by rw [hs.setup.card_X, hBcard])
    have huF : w ^ (orderOf w / 2) ∈ F := hBF (by rw [hBX]; exact subset_closure (by simp))
    intro r hr
    rw [← hCu]
    exact mem_inf.mpr ⟨hR''S hr, mem_centralizer_singleton_iff.mpr (huF.2.1 r hr)⟩
  exact ⟨d, fun r hr => hR''T ⟨r, hr, hconj r⟩⟩

end CFSG.ComponentClassification.HarrisLit
