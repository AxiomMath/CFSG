module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFFusion
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFPreimage
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.EmptyFaithful.S14118

public section

set_option linter.unusedSectionVars false

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {G : Type} [Group G] [Finite G]

section PreAut

variable {M V : Subgroup G} {hU : IsElemAbelian 2 V} {hMN : M ≤ Subgroup.normalizer (V : Set G)}

omit [Finite G] in
theorem le_normalizer_preAutM {Y : Subgroup G} {L : Subgroup (MulAut (IntMod V hU))}
    (hYM : Y ≤ M) (hL : ∀ g ∈ autI hU Y, ∀ φ ∈ L, g * φ * g⁻¹ ∈ L) :
    Y ≤ Subgroup.normalizer (preAutM hU hMN L : Set G) := by
  have key : ∀ y ∈ Y, ∀ k ∈ preAutM hU hMN L, y * k * y⁻¹ ∈ preAutM hU hMN L := by
    intro y hy k hk
    obtain ⟨hkM, hkL⟩ := (mem_preAutM hU hMN).1 hk
    have hyM : y ∈ M := hYM hy
    refine (mem_preAutM hU hMN).2 ⟨M.mul_mem (M.mul_mem hyM hkM) (M.inv_mem hyM), ?_⟩
    have e : (⟨y * k * y⁻¹, M.mul_mem (M.mul_mem hyM hkM) (M.inv_mem hyM)⟩ : ↥M) =
        ⟨y, hyM⟩ * ⟨k, hkM⟩ * ⟨y, hyM⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    refine hL _ ?_ _ hkL
    rw [actM_eq_convI]
    exact convI_mem_autI hU hy (hMN hyM)
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => key y hy x hx, fun hx => by simpa [mul_assoc] using key y⁻¹ (Y.inv_mem hy) _ hx⟩

end PreAut

structure FFCtx (M T V : Subgroup G) (hU : IsElemAbelian 2 V)
    (hMN : M ≤ Subgroup.normalizer (V : Set G))
    (I : Finset (Subgroup (MulAut (IntMod V hU)))) : Prop where
  hVM : V ≤ M
  hVdef : V = conjClosure (quasithinOmegaOneCenter T) M
  hT : IsSylowTwoOf T M
  hCT : CharTwo M
  hcard : ∀ L ∈ I, Nat.card L = 6
  hJM : autI hU (thompsonJ M) = ⨆ L ∈ I, L
  hSyl : IsSylowTwoOf (autI hU (thompsonJ T)) (autI hU (thompsonJ M))
  hperm : ∀ g ∈ autI hU M, ∀ L ∈ I, B1.conjAut g L ∈ I
  hfam : S3Family I
  hBJ : autI hU (baum T) ≤ autI hU (thompsonJ M)

namespace FFCtx

variable {M T V : Subgroup G} {hU : IsElemAbelian 2 V} {hMN : M ≤ Subgroup.normalizer (V : Set G)}
  {I : Finset (Subgroup (MulAut (IntMod V hU)))} (ctx : FFCtx M T V hU hMN I)
include ctx

omit [Finite G] in
theorem V_le_pCoreOf : V ≤ pCoreOf 2 M :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ctx.hVM hMN
    (isPGroup_of_isElemAbelian hU)

theorem pCoreOf_le_centralizer : pCoreOf 2 M ≤ Subgroup.centralizer (V : Set G) ⊓ M := by
  have hQT : pCoreOf 2 M ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf ctx.hT
  have hQM : pCoreOf 2 M ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hVQ : V ≤ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    rw [ctx.hVdef]
    refine conjClosure_le fun h hh z hz => ?_
    have hzT : z ∈ Subgroup.centralizer (T : Set G) :=
      (quasithinOmegaOneCenter_le_center T hz).2
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : h⁻¹ * q * h ∈ pCoreOf 2 M := by
      have := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (M.inv_mem hh)) q).mp hq
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hzT _ (hQT hq')
    calc q * (h * z * h⁻¹) = h * ((h⁻¹ * q * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * q * h)) * h⁻¹ := by rw [hc]
      _ = h * z * h⁻¹ * q := by group
  refine le_inf (fun x hx => ?_) hQM
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (hVQ hv) x hx).symm

theorem iSup_le_normalizer {L : Subgroup (MulAut (IntMod V hU))} (hL : L ∈ I) :
    (⨆ L' ∈ I, L') ≤ Subgroup.normalizer (L : Set (MulAut (IntMod V hU))) := by
  refine iSup₂_le fun L' hL' => ?_
  by_cases h : L' = L
  · subst h; exact Subgroup.le_normalizer
  · intro a ha
    have hc : ∀ b ∈ L, a * b = b * a := fun b hb => ctx.hfam.comm L' hL' L hL h a ha b hb
    have hcen : a ∈ Subgroup.centralizer (L : Set (MulAut (IntMod V hU))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hc b hb).symm
    exact Subgroup.centralizer_le_normalizer _ hcen

theorem conj_mem_iSup {g : MulAut (IntMod V hU)} (hg : g ∈ autI hU M) {φ : MulAut (IntMod V hU)}
    (hφ : φ ∈ ⨆ L ∈ I, L) : g * φ * g⁻¹ ∈ ⨆ L ∈ I, L := by
  have h : (⨆ L ∈ I, L) ≤ (⨆ L ∈ I, L).comap (MulAut.conj g).toMonoidHom := by
    refine iSup₂_le fun L' hL' x hx => ?_
    rw [Subgroup.mem_comap]
    have hmem : (MulAut.conj g).toMonoidHom x ∈ B1.conjAut g L' := by
      rw [B1.mem_conjAut]
      simp [MulAut.conj_apply, mul_assoc, hx]
    exact (le_iSup₂ (f := fun (L : Subgroup (MulAut (IntMod V hU))) (_ : L ∈ I) => L)
      (B1.conjAut g L') (ctx.hperm g hg L' hL')) hmem
  have := h hφ
  simpa [MulAut.conj_apply] using this

theorem M_le_normalizer_preAutM_iSup :
    M ≤ Subgroup.normalizer (preAutM hU hMN (⨆ L ∈ I, L) : Set G) :=
  le_normalizer_preAutM le_rfl fun _ hg _ hφ => ctx.conj_mem_iSup hg hφ

theorem preAutM_le_preAutM_iSup {L : Subgroup (MulAut (IntMod V hU))} (hL : L ∈ I) :
    preAutM hU hMN L ≤ preAutM hU hMN (⨆ L' ∈ I, L') :=
  preAutM_mono hU hMN (le_iSup₂ (f := fun (L' : Subgroup (MulAut (IntMod V hU)))
    (_ : L' ∈ I) => L') L hL)

theorem preAutM_iSup_le_normalizer_preAutM {L : Subgroup (MulAut (IntMod V hU))} (hL : L ∈ I) :
    preAutM hU hMN (⨆ L' ∈ I, L') ≤ Subgroup.normalizer (preAutM hU hMN L : Set G) := by
  refine le_normalizer_preAutM (preAutM_le hU hMN _) fun g hg φ hφ => ?_
  obtain ⟨x, hx, rfl⟩ := (mem_autI hU).1 hg
  obtain ⟨hxM, hxJ⟩ := (mem_preAutM hU hMN).1 hx
  have : convI hU x = actM hU hMN ⟨(x : G), hxM⟩ := rfl
  rw [this]
  exact (Subgroup.mem_normalizer_iff.mp (ctx.iSup_le_normalizer hL hxJ) φ).mp hφ

end FFCtx

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
