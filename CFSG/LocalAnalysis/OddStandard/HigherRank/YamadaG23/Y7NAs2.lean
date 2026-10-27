module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NAs1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {t g : G} {Lam P S U P1 : Subgroup G}

namespace NtAbs

theorem P_le_P0 (h : NtAbs t g Lam P S U P1) : P ≤ normIn P1 Lam := by
  rw [normIn]
  exact le_inf h.P_le h.P_le_normalizer

theorem g_mem_P0 (h : NtAbs t g Lam P S U P1) : g ∈ normIn P1 Lam := by
  rw [normIn, Subgroup.mem_inf]
  refine ⟨h.g_mem, ?_⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  simpa [conjSub] using h.g_norm_Lam

theorem Z1_le_P0 (h : NtAbs t g Lam P S U P1) : centIn P1 Lam ≤ normIn P1 Lam := by
  intro x hx
  rw [centIn, Subgroup.mem_inf] at hx
  rw [normIn, Subgroup.mem_inf]
  exact ⟨hx.1, Subgroup.centralizer_le_normalizer (Lam : Set G) hx.2⟩

theorem U0_le_P0 (h : NtAbs t g Lam P S U P1) :
    conjSub t (centIn P1 Lam) ≤ normIn P1 Lam := by
  intro x hx
  rw [mem_conjSub_iff'] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  have hcP0 : c ∈ normIn P1 Lam := Z1_le_P0 h hc
  have hc' : t⁻¹ * c * t ∈ normIn P1 Lam :=
    (Subgroup.mem_set_normalizer_iff''.mp (h.normal h.t_mem) c).mp hcP0
  have htinv : t⁻¹ = t := by
    have ht : t * t = 1 := by simpa [pow_two] using h.t_sq
    exact inv_eq_of_mul_eq_one_left ht
  simpa [htinv] using hc'

theorem P0_normalizes_Z1 (h : NtAbs t g Lam P S U P1) :
    ∀ y ∈ normIn P1 Lam, ∀ u ∈ centIn P1 Lam, y * u * y⁻¹ ∈ centIn P1 Lam := by
  intro y hy u hu
  rw [normIn, Subgroup.mem_inf] at hy
  rw [centIn, Subgroup.mem_inf] at hu ⊢
  refine ⟨?_, ?_⟩
  · exact P1.mul_mem (P1.mul_mem hy.1 hu.1) (P1.inv_mem hy.1)
  · rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hyl : y⁻¹ * l * y ∈ Lam :=
      (Subgroup.mem_set_normalizer_iff''.mp hy.2 l).mp hl
    have hcomm : (y⁻¹ * l * y) * u = u * (y⁻¹ * l * y) :=
      Subgroup.mem_centralizer_iff.mp hu.2 (y⁻¹ * l * y) hyl
    calc l * (y * u * y⁻¹) = y * ((y⁻¹ * l * y) * u) * y⁻¹ := by group
      _ = y * (u * (y⁻¹ * l * y)) * y⁻¹ := by rw [hcomm]
      _ = (y * u * y⁻¹) * l := by group

theorem P0_normalizes_U0 (h : NtAbs t g Lam P S U P1) :
    ∀ y ∈ normIn P1 Lam, ∀ u ∈ conjSub t (centIn P1 Lam),
      y * u * y⁻¹ ∈ conjSub t (centIn P1 Lam) := by
  intro y hy u hu
  rw [mem_conjSub_iff'] at hu
  obtain ⟨c, hc, rfl⟩ := hu
  set y' : G := t⁻¹ * y * t with hy'_def
  have hy'P0 : y' ∈ normIn P1 Lam := by
    rw [hy'_def]
    exact (Subgroup.mem_set_normalizer_iff''.mp (h.normal h.t_mem) y).mp hy
  have hc' : y' * c * y'⁻¹ ∈ centIn P1 Lam := P0_normalizes_Z1 h y' hy'P0 c hc
  rw [mem_conjSub_iff']
  refine ⟨y' * c * y'⁻¹, hc', ?_⟩
  rw [hy'_def]
  group

theorem U_le_U0 (h : NtAbs t g Lam P S U P1) : U ≤ conjSub t (centIn P1 Lam) := by
  have hUt : conjSub t U ≤ centIn P1 Lam := by
    intro v hv
    rw [centIn, Subgroup.mem_inf]
    refine ⟨h.P_le (h.wr.le_left.2 hv), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hvLam : v ∈ conjSub t Lam :=
      (Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) h.U_le) hv
    exact h.comm l hl v hvLam
  calc U = conjSub t (conjSub t U) := (conjSub_conjSub_of_sq h.t_sq U).symm
    _ ≤ conjSub t (centIn P1 Lam) := Subgroup.map_mono hUt

theorem Z1_inf_U0 (h : NtAbs t g Lam P S U P1) :
    centIn P1 Lam ⊓ conjSub t (centIn P1 Lam) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_inf] at hx
  rw [Subgroup.mem_bot]
  have hx1 := hx.1
  rw [centIn, Subgroup.mem_inf] at hx1
  have hx2 := hx.2
  rw [mem_conjSub_iff'] at hx2
  obtain ⟨c, hc, rfl⟩ := hx2
  rw [centIn, Subgroup.mem_inf] at hc
  refine h.cent_K (t * c * t⁻¹) hx1.1 ?_ ?_
  · intro l hl
    exact (Subgroup.mem_centralizer_iff.mp hx1.2 l hl).symm
  · intro y hy
    rw [mem_conjSub_iff'] at hy
    obtain ⟨l, hl, rfl⟩ := hy
    have hcl : c * l = l * c := (Subgroup.mem_centralizer_iff.mp hc.2 l hl).symm
    calc (t * c * t⁻¹) * (t * l * t⁻¹) = t * (c * l) * t⁻¹ := by group
      _ = t * (l * c) * t⁻¹ := by rw [hcl]
      _ = (t * l * t⁻¹) * (t * c * t⁻¹) := by group

theorem Z1_comm_U0 (h : NtAbs t g Lam P S U P1) :
    ∀ a ∈ centIn P1 Lam, ∀ b ∈ conjSub t (centIn P1 Lam), a * b = b * a := by
  intro a ha b hb
  have haP0 : a ∈ normIn P1 Lam := Z1_le_P0 h ha
  have hbP0 : b ∈ normIn P1 Lam := U0_le_P0 h hb
  have hab : a * b * a⁻¹ ∈ conjSub t (centIn P1 Lam) := P0_normalizes_U0 h a haP0 b hb
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ conjSub t (centIn P1 Lam) :=
    (conjSub t (centIn P1 Lam)).mul_mem hab ((conjSub t (centIn P1 Lam)).inv_mem hb)
  have hba : b * a * b⁻¹ ∈ centIn P1 Lam := P0_normalizes_Z1 h b hbP0 a ha
  have h2 : b * a * b⁻¹ * a⁻¹ ∈ centIn P1 Lam :=
    (centIn P1 Lam).mul_mem hba ((centIn P1 Lam).inv_mem ha)
  have hinv : a * b * a⁻¹ * b⁻¹ = (b * a * b⁻¹ * a⁻¹)⁻¹ := by group
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ centIn P1 Lam ⊓ conjSub t (centIn P1 Lam) :=
    ⟨by rw [hinv]; exact (centIn P1 Lam).inv_mem h2, h1⟩
  rw [Z1_inf_U0 h, Subgroup.mem_bot] at hmem
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [hmem, one_mul]

end NtAbs

end CFSG.OddStandard.HigherRank.YamadaG23
