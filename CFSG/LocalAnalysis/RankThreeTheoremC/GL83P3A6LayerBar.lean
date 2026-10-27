module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6LayerPoint
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2Img
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2Sylow
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43E9R

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer

open CFSG.Open Subgroup CFSG.ABGLocalTools CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Aux
  CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Img CFSG.AGLEmbedding

namespace PointData

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M J : Subgroup G} {x e₂ e₃ t ρ : G}
  {s : ℤ} (hpd : PointData P M J x e₂ e₃ t ρ s)

include hpd

theorem e₂_memM : e₂ ∈ M := hpd.P_le (mem_inf.mp hpd.e₂_mem).1

theorem e₃_memM : e₃ ∈ M := hpd.P_le (mem_inf.mp hpd.e₃_mem).1

theorem t_memM : t ∈ M := hpd.P_le hpd.t_mem

theorem Q_le_P : Qf x e₂ e₃ ≤ (P : Subgroup G) := hpd.Q_eq ▸ inf_le_left

theorem Q_le_M : Qf x e₂ e₃ ≤ M := hpd.Q_le_P.trans hpd.P_le

theorem O_cop : ¬ 3 ∣ Nat.card (GLBPrimeCore 3 M) :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (glbPrimeCore_coprime 3 M)

theorem P_inf_O : (P : Subgroup G) ⊓ GLBPrimeCore 3 M = ⊥ :=
  GL83P3A6Syl.inf_eq_bot_of_pGroup P.isPGroup' hpd.O_cop

theorem Q_inf_O : Qf x e₂ e₃ ⊓ GLBPrimeCore 3 M = ⊥ :=
  le_bot_iff.mp (hpd.P_inf_O ▸ inf_le_inf_right _ hpd.Q_le_P)

theorem tri_M : VITriple (⟨x, hpd.x_memM⟩ : M) ⟨e₂, hpd.e₂_memM⟩ ⟨e₃, hpd.e₃_memM⟩ :=
  vitriple_comap M.subtype M.subtype_injective hpd.tri

theorem Q_subgroupOf :
    (Qf x e₂ e₃).subgroupOf M = Qf (⟨x, hpd.x_memM⟩ : M) ⟨e₂, hpd.e₂_memM⟩ ⟨e₃, hpd.e₃_memM⟩ := by
  have h := map_Qf M.subtype (⟨x, hpd.x_memM⟩ : M) ⟨e₂, hpd.e₂_memM⟩ ⟨e₃, hpd.e₃_memM⟩
  simp only [Subgroup.subtype_apply] at h
  rw [← h]
  exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _

variable [((GLBPrimeCore 3 M).subgroupOf M).Normal]

theorem inj_Q (w : ↥M)
    (hw : w ∈ Qf (⟨x, hpd.x_memM⟩ : M) ⟨e₂, hpd.e₂_memM⟩ ⟨e₃, hpd.e₃_memM⟩)
    (h1 : QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) w = 1) : w = 1 := by
  have hwO : (w : G) ∈ GLBPrimeCore 3 M := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    exact h1
  have hwQ : (w : G) ∈ Qf x e₂ e₃ := by
    rw [← hpd.Q_subgroupOf] at hw
    exact hw
  have : (w : G) ∈ Qf x e₂ e₃ ⊓ GLBPrimeCore 3 M := mem_inf.mpr ⟨hwQ, hwO⟩
  rw [hpd.Q_inf_O, mem_bot] at this
  exact Subtype.ext this

theorem xframe :
    XFrame (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨x, hpd.x_memM⟩ : M))
      (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨e₂, hpd.e₂_memM⟩ : M))
      (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨e₃, hpd.e₃_memM⟩ : M))
      (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨t, hpd.t_memM⟩ : M))
      (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨ρ, hpd.ρ_mem⟩ : M)) s := by
  set π := QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) with hπ
  have hrel : ∀ (a b c : M), a * b * a⁻¹ = c → π a * π b * (π a)⁻¹ = π c := by
    intro a b c habc
    rw [← map_inv, ← map_mul, ← map_mul, habc]
  have hzp : ∀ (b : M) (k : ℤ), π (b ^ k) = π b ^ k := fun b k => map_zpow π b k
  refine ⟨vitriple_map π hpd.tri_M hpd.inj_Q, hrel _ _ _ (Subtype.ext hpd.t_x),
    hrel _ _ _ (Subtype.ext hpd.t_e₂), hrel _ _ _ (Subtype.ext hpd.t_e₃),
    hrel _ _ _ (Subtype.ext hpd.ρ_x), ?_, ?_, hpd.s_cases⟩
  · rw [← hzp]
    exact hrel _ _ _ (Subtype.ext (by simpa using hpd.ρ_e₂))
  · rw [← hzp]
    exact hrel _ _ _ (Subtype.ext (by simpa using hpd.ρ_e₃))

theorem img_Q_eq :
    img M (GLBPrimeCore 3 M) ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) =
      Qf (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨x, hpd.x_memM⟩ : M))
        (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨e₂, hpd.e₂_memM⟩ : M))
        (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨e₃, hpd.e₃_memM⟩ : M)) := by
  rw [← hpd.Q_eq]
  unfold img
  rw [hpd.Q_subgroupOf, map_Qf]

theorem lines_bar_mk (g' : ↥M)
    (hg : QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (g' * ⟨x, hpd.x_memM⟩ * g'⁻¹) ∈
      Qf (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨x, hpd.x_memM⟩ : M))
        (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨e₂, hpd.e₂_memM⟩ : M))
        (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨e₃, hpd.e₃_memM⟩ : M))) :
    QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (g' * ⟨x, hpd.x_memM⟩ * g'⁻¹) ∈
        zpowers (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨x, hpd.x_memM⟩ : M)) ∨
      QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (g' * ⟨x, hpd.x_memM⟩ * g'⁻¹) ∈
        zpowers (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨e₂, hpd.e₂_memM⟩ : M)) ∨
      QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (g' * ⟨x, hpd.x_memM⟩ * g'⁻¹) ∈
        zpowers (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨e₃, hpd.e₃_memM⟩ : M)) := by
  set O := GLBPrimeCore 3 M with hOdef
  set π := QuotientGroup.mk' (O.subgroupOf M) with hπ
  have hT := hpd.tri
  set xm : M := ⟨x, hpd.x_memM⟩ with hxm
  rw [← map_Qf] at hg
  obtain ⟨u', hu'Q, hu'⟩ := hg
  set w : G := (g' : G) * x * (g' : G)⁻¹ with hwdef
  have hwM : w ∈ M := M.mul_mem (M.mul_mem g'.2 hpd.x_memM) (M.inv_mem g'.2)
  have huQ : (u' : G) ∈ Qf x e₂ e₃ := by
    rw [← hpd.Q_subgroupOf] at hu'Q
    exact hu'Q
  have hO : (u' : G)⁻¹ * w ∈ O := by
    have := QuotientGroup.eq.mp hu'
    rw [mem_subgroupOf] at this
    simpa [w] using this
  have hw3 : w ^ 3 = 1 := by rw [hwdef, conj_pow, hT.x_pow]; group
  have hw1 : w ≠ 1 := by
    intro h1
    apply hT.x_ne
    have : x = (g' : G)⁻¹ * w * g' := by rw [hwdef]; group
    rw [this, h1]; group
  have hu1 : (u' : G) ≠ 1 := by
    intro h1
    rw [h1, inv_one, one_mul] at hO
    have hord : orderOf w = 3 := orderOf_eq_prime hw3 hw1
    have hdvd : orderOf (⟨w, hO⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hord] at hdvd
    exact hpd.O_cop hdvd
  have hu3 : (u' : G) ^ 3 = 1 := hT.Q_exp _ huQ
  have hU3 : Nat.card (zpowers (u' : G)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hu3 hu1]
  have huM : (u' : G) ∈ M := u'.2
  have hUN : zpowers (u' : G) ≤ normalizer (O : Set G) :=
    (zpowers_le.mpr huM).trans (le_normalizer_glbPrimeCore 3 M)
  have hwU : w ∈ zpowers (u' : G) ⊔ O := by
    have : w = (u' : G) * ((u' : G)⁻¹ * w) := by group
    rw [this]
    exact mul_mem_sup (mem_zpowers _) hO
  obtain ⟨k, -, hkw⟩ := e9r_exists_conj_zpowers_eq hUN hpd.O_cop hU3 hwU hw3 hw1
  have hzQ : k⁻¹ * w * k ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G) := by
    rw [← hpd.Q_eq]
    have : k⁻¹ * w * k ∈ zpowers (u' : G) := by rw [← hkw]; exact mem_zpowers _
    exact (zpowers_le.mpr huQ) this
  have hzw : k⁻¹ * w * k = (k⁻¹ * g') * x * (k⁻¹ * g')⁻¹ := by rw [hwdef]; group
  have hline := hpd.lines (k⁻¹ * g') (hzw ▸ hzQ)
  rw [← hzw] at hline
  have hz1 : k⁻¹ * w * k ≠ 1 := by
    intro h1
    apply hw1
    have : w = k * (k⁻¹ * w * k) * k⁻¹ := by group
    rw [this, h1]; group
  have key : ∀ (e : G) (he : e ∈ M), e ^ 3 = 1 → e ≠ 1 → k⁻¹ * w * k ∈ zpowers e →
      π (g' * xm * g'⁻¹) ∈ zpowers (π ⟨e, he⟩) := by
    intro e he he3 he1 hze
    have h1 : zpowers (k⁻¹ * w * k) = zpowers e := zpowers_eq_of_mem he3 he1 hze hz1
    have hue : (u' : G) ∈ zpowers e := by rw [← h1, hkw]; exact mem_zpowers _
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hue
    refine mem_zpowers_iff.mpr ⟨m, ?_⟩
    rw [← hu', ← map_zpow]
    congr 1
    exact Subtype.ext (by simpa using hm)
  rcases hline with h | h | h
  · exact Or.inl (key x hpd.x_memM hT.x_pow hT.x_ne h)
  · exact Or.inr (Or.inl (key e₂ hpd.e₂_memM hT.e₂_pow hT.e₂_ne h))
  · exact Or.inr (Or.inr (key e₃ hpd.e₃_memM hT.e₃_pow hT.e₃_ne h))

theorem lines_bar (g : M ⧸ (GLBPrimeCore 3 M).subgroupOf M)
    (hg : g * QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨x, hpd.x_memM⟩ : M) * g⁻¹ ∈
      Qf (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨x, hpd.x_memM⟩ : M))
        (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨e₂, hpd.e₂_memM⟩ : M))
        (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨e₃, hpd.e₃_memM⟩ : M))) :
    g * QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨x, hpd.x_memM⟩ : M) * g⁻¹ ∈
        zpowers (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨x, hpd.x_memM⟩ : M)) ∨
      g * QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨x, hpd.x_memM⟩ : M) * g⁻¹ ∈
        zpowers (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨e₂, hpd.e₂_memM⟩ : M)) ∨
      g * QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨x, hpd.x_memM⟩ : M) * g⁻¹ ∈
        zpowers (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨e₃, hpd.e₃_memM⟩ : M)) := by
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective ((GLBPrimeCore 3 M).subgroupOf M) g
  rw [← map_inv, ← map_mul, ← map_mul] at hg ⊢
  exact hpd.lines_bar_mk g' hg

end PointData

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer
