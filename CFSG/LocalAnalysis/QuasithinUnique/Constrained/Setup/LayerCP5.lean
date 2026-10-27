module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerCP3

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.ABGLocalTools CFSG.LocalCores CFSG.Quasithin.B6
open scoped commutatorElement

section Helpers

variable {G : Type*} [Group G]

theorem commutator_mul_mul_of_commute {z w a b : G} (hza : Commute z a) (hzb : Commute z b)
    (hwa : Commute w a) (hwb : Commute w b) (hzw : Commute z w) :
    ⁅z * a, w * b⁆ = ⁅a, b⁆ := by
  have h1 : z * a * (w * b) = (z * w) * (a * b) := by
    calc z * a * (w * b) = z * (a * w) * b := by group
      _ = z * (w * a) * b := by rw [hwa.eq]
      _ = (z * w) * (a * b) := by group
  have h2 : w * b * (z * a) = (z * w) * (b * a) := by
    calc w * b * (z * a) = w * (b * z) * a := by group
      _ = w * (z * b) * a := by rw [hzb.eq]
      _ = (w * z) * (b * a) := by group
      _ = (z * w) * (b * a) := by rw [hzw.eq]
  have hzwa : Commute (z * w) a := hza.mul_left hwa
  have hzwb : Commute (z * w) b := hzb.mul_left hwb
  have hc : Commute (z * w) ((a * b) * (b * a)⁻¹) :=
    (hzwa.mul_right hzwb).mul_right (hzwb.mul_right hzwa).inv_right
  calc ⁅z * a, w * b⁆ = (z * a * (w * b)) * (w * b * (z * a))⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
    _ = ((z * w) * (a * b)) * ((z * w) * (b * a))⁻¹ := by rw [h1, h2]
    _ = (z * w) * ((a * b) * (b * a)⁻¹) * (z * w)⁻¹ := by group
    _ = (a * b) * (b * a)⁻¹ := hc.mul_inv_cancel
    _ = ⁅a, b⁆ := by simp only [commutatorElement_def, mul_inv_rev, mul_assoc]

end Helpers

section Centralizer

variable {H : Type*} [Group H] {L₀ : Subgroup H}

theorem conj_mem_centL {n c : H} (hn : n ∈ normL L₀) (hc : c ∈ centL L₀) :
    n * c * n⁻¹ ∈ centL L₀ := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl' : n⁻¹ * l * n ∈ L₀ := by
    have := (Subgroup.mem_normalizer_iff.1 ((normL L₀).inv_mem hn) l).1 hl
    simpa using this
  have hc' := Subgroup.mem_centralizer_iff.1 hc _ hl'
  calc l * (n * c * n⁻¹) = n * ((n⁻¹ * l * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * l * n)) * n⁻¹ := by rw [hc']
    _ = n * c * n⁻¹ * l := by group

theorem normL_le_normalizer_centL (L₀ : Subgroup H) :
    normL L₀ ≤ Subgroup.normalizer (centL L₀ : Set H) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => conj_mem_centL hn hc, fun hc => ?_⟩
  have := conj_mem_centL ((normL L₀).inv_mem hn) hc
  simpa [mul_assoc] using this

theorem normL_le_normalizer_Z0 (L₀ : Subgroup H) :
    normL L₀ ≤ Subgroup.normalizer ((L₀ ⊓ centL L₀ : Subgroup H) : Set H) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro c
  have h1 := Subgroup.mem_normalizer_iff.1 hn c
  have h2 := Subgroup.mem_normalizer_iff.1 (normL_le_normalizer_centL L₀ hn) c
  exact ⟨fun hc => ⟨h1.1 hc.1, h2.1 hc.2⟩, fun hc => ⟨h1.2 hc.1, h2.2 hc.2⟩⟩

end Centralizer

section Setting

variable {H : Type*} [Group H] {p : ℕ} {T M : Subgroup H} {ι : Type*} {L : ι → Subgroup H}

theorem CPSetting.Z0_le_M [Finite H] [Nonempty ι] (hS : CPSetting p T M L) (i₀ : ι) :
    L i₀ ⊓ centL (L i₀) ≤ M := by
  intro c hc
  refine hS.center_le_M ⟨le_iSup L i₀ hc.1, Subgroup.mem_centralizer_iff.2 ?_⟩
  · intro k hk
    have hKc : (⨆ i, L i : Subgroup H) ≤ Subgroup.centralizer ({c} : Set H) := by
      refine iSup_le fun j => ?_
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      by_cases hj : j = i₀
      · subst hj
        exact ((Subgroup.mem_centralizer_iff.1 hc.2) x hx).symm
      · exact (hS.mul_comm' hj hx hc.1).symm
    exact ((Subgroup.mem_centralizer_iff.1 (hKc hk)) c rfl).symm

def uSub (L₀ : Subgroup H) (Y : Subgroup (MulAut ↥L₀)) : Subgroup H :=
  (Y.comap (MulAut.conj : ↥L₀ →* MulAut ↥L₀)).map L₀.subtype

theorem mem_uSub {L₀ : Subgroup H} {Y : Subgroup (MulAut ↥L₀)} {l : H} :
    l ∈ uSub L₀ Y ↔ ∃ hl : l ∈ L₀, (MulAut.conj (⟨l, hl⟩ : ↥L₀) : MulAut ↥L₀) ∈ Y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hl, hY⟩
    exact ⟨⟨l, hl⟩, hY, rfl⟩

theorem uSub_le {L₀ : Subgroup H} {Y : Subgroup (MulAut ↥L₀)} : uSub L₀ Y ≤ L₀ :=
  fun _ hl => (mem_uSub.1 hl).1

theorem conj_mul_eq {L₀ : Subgroup H} {n l : H} (hn : n ∈ normL L₀) (hl : l ∈ L₀)
    (hnl : n * l * n⁻¹ ∈ L₀) :
    (MulAut.conj (⟨n * l * n⁻¹, hnl⟩ : ↥L₀) : MulAut ↥L₀) =
      actOf L₀ n * MulAut.conj (⟨l, hl⟩ : ↥L₀) * (actOf L₀ n)⁻¹ := by
  rw [← actOf_of_mem_self hnl, ← actOf_of_mem_self hl,
    ← actOf_inv hn, ← actOf_mul hn (Subgroup.le_normalizer hl),
    ← actOf_mul ((normL L₀).mul_mem hn (Subgroup.le_normalizer hl)) ((normL L₀).inv_mem hn)]

end Setting

end CFSG.QuasithinUnique.Setup.Layer
