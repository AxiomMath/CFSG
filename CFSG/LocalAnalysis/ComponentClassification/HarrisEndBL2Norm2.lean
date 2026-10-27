module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2Norm1

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.L2Ctx

variable {hs : Setting46e t L p f S w z V i j} {W : Subgroup X}

theorem mul_inv_mem_qTilde (hc : L2Ctx hs W) {x g : X} (hxW : x ∈ W) (hgW : g ∈ W)
    (h : conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
        (QuotientGroup.mk ⟨x, hc.sylow.le hxW⟩) =
      conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
        (QuotientGroup.mk ⟨g, hc.sylow.le hgW⟩)) :
    x * g⁻¹ ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W := by
  have hxgM := mul_mem (hc.sylow.le hxW) (inv_mem (hc.sylow.le hgW))
  refine ⟨W.mul_mem hxW (W.inv_mem hgW), (mem_preimageOf hxgM).mpr ?_⟩
  rw [← hs.centralizer_layer_eq hc.h412, ← conjOn_eq_one_iff]
  have : (QuotientGroup.mk ⟨x * g⁻¹, hxgM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      QuotientGroup.mk ⟨x, hc.sylow.le hxW⟩ * (QuotientGroup.mk ⟨g, hc.sylow.le hgW⟩)⁻¹ := rfl
  rw [this, map_mul, map_inv, h, mul_inv_cancel]

theorem mem_N0_of_conjOn_mem (hKC : AutPSL2CentralizerInput)
    (hFC : AutPSL2FieldCentralizerInput) (hc : L2Ctx hs W)
    {v : MulAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))}
    (hv : SylowAutData ((barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
      W).map (conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))) v) {x : X}
    (hxW : x ∈ W)
    (hxc : conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
        (QuotientGroup.mk ⟨x, hc.sylow.le hxW⟩) ∈
      centralizer (((barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} :
        Set X)) W).map (conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ⊓
          innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) : Subgroup _) : Set _)) :
    x ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ closure ({t, z} : Set X) := by
  have hxP : conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
      (QuotientGroup.mk ⟨x, hc.sylow.le hxW⟩) ∈
      (barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) W).map
        (conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) :=
    ⟨_, mk_mem_barOf _ hxW, rfl⟩
  have htz : t ∈ closure ({t, z} : Set X) := subset_closure (Set.mem_insert _ _)
  have hzz : z ∈ closure ({t, z} : Set X) := subset_closure (Set.mem_insert_of_mem _ rfl)
  have key : ∀ g (hgW : g ∈ W), g ∈ closure ({t, z} : Set X) →
      conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
        (QuotientGroup.mk ⟨x, hc.sylow.le hxW⟩) =
      conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
        (QuotientGroup.mk ⟨g, hc.sylow.le hgW⟩) →
      x ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ closure ({t, z} : Set X) := by
    intro g hgW hgc h
    have := hc.mul_inv_mem_qTilde hxW hgW h
    have hx : x = (x * g⁻¹) * g := by group
    rw [hx]
    exact mul_mem (mem_sup_left this) (mem_sup_right hgc)
  rcases hc.mem_centralizer_R hKC hFC hv ⟨hxP, hxc⟩ with h | h | h | h
  · refine key 1 (one_mem W) (one_mem _) ?_
    rw [h]
    exact (map_one _).symm.trans (by rfl)
  · exact key z hc.z_mem_W hzz h
  · exact key t hc.t_mem_W htz h
  · refine key (z * t) (mul_mem hc.z_mem_W hc.t_mem_W) (mul_mem hzz htz) ?_
    rw [h, ← map_mul]
    rfl

theorem N0_le (hc : L2Ctx hs W) :
    qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ closure ({t, z} : Set X) ≤ W :=
  sup_le hc.qTilde_le ((closure_le _).mpr (by
    rintro x (rfl | rfl)
    · exact hc.t_mem_W
    · exact hc.z_mem_W))

theorem _root_.CFSG.ComponentClassification.HarrisLit.EndB.mul_conj_mul_inv {Y : Type*} [Group Y]
    (φ : MulAut Y) (y : Y) : φ * MulAut.conj y * φ⁻¹ = MulAut.conj (φ y) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  rw [← MulEquiv.apply_symm_apply φ x]
  simp [MulAut.inv_apply]

theorem conjOn_mem_of_mem_N0 (hKC : AutPSL2CentralizerInput)
    (hFC : AutPSL2FieldCentralizerInput) (hc : L2Ctx hs W) {x : X}
    (hx : x ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ closure ({t, z} : Set X)) :
    conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
        (QuotientGroup.mk ⟨x, hc.sylow.le (hc.N0_le hx)⟩) ∈
      centralizer (((barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} :
        Set X)) W).map (conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ⊓
          innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) : Subgroup _) : Set _) := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set S₀ : Subgroup X := ((centralizer (((barOf M W).map (conjOn (layer (MBar β))) ⊓
      innAut ↥(layer (MBar β)) : Subgroup _) : Set _)).comap
        ((conjOn (layer (MBar β))).comp (QuotientGroup.mk' (pPrimeCore 2 ↥M)))).map M.subtype
    with hS₀
  have hmemS : ∀ y (hy : y ∈ M), conjOn (layer (MBar β)) (QuotientGroup.mk ⟨y, hy⟩) ∈
      centralizer (((barOf M W).map (conjOn (layer (MBar β))) ⊓
        innAut ↥(layer (MBar β)) : Subgroup _) : Set _) → y ∈ S₀ := fun y hy h =>
    ⟨⟨y, hy⟩, h, rfl⟩
  have hzZW : z ∈ W ⊓ centralizer (W : Set X) := by
    rw [hc.center_eq hKC]
    exact subset_closure (Set.mem_insert_of_mem _ rfl)
  have hle : qTilde β W ⊔ closure ({t, z} : Set X) ≤ S₀ := by
    refine sup_le (fun y hy => hmemS y (hc.sylow.le hy.1) ?_) ((closure_le _).mpr ?_)
    · have hyQ := (mem_preimageOf (hc.sylow.le hy.1)).mp hy.2
      have hyC : (QuotientGroup.mk ⟨y, hc.sylow.le hy.1⟩ : MBar β) ∈
          centralizer (layer (MBar β) : Set (MBar β)) := by
        rw [hs.centralizer_layer_eq hc.h412]
        exact hyQ
      rw [conjOn_eq_one_iff.mpr hyC]
      exact one_mem _
    · rintro y (rfl | rfl)
      · exact hmemS _ (hs.setup.t_mem_centralizer_beta i j)
          (mem_centralizer_iff.mpr fun r hr => (hc.tau_comm hFC hr).symm)
      · refine hmemS _ hc.z_mem_M (Subgroup.mem_centralizer_iff.mpr ?_)
        rintro r ⟨⟨g, hg, rfl⟩, -⟩
        obtain ⟨x', hx'W, rfl⟩ := mem_barOf.mp hg
        rw [← map_mul, ← map_mul]
        congr 1
        have hxz : (x' : X) * y = y * x' := ((mem_centralizer_iff.mp hzZW.2) _ hx'W)
        change (QuotientGroup.mk (x' * ⟨y, hc.z_mem_M⟩) : MBar β) =
          QuotientGroup.mk (⟨y, hc.z_mem_M⟩ * x')
        congr 1
        exact Subtype.ext hxz
  obtain ⟨⟨y, hyM⟩, hy, hyx⟩ := hle hx
  have : (⟨y, hyM⟩ : ↥M) = ⟨x, hc.sylow.le (hc.N0_le hx)⟩ := Subtype.ext hyx
  rw [← this]
  exact hy

theorem N0_normal (hKC : AutPSL2CentralizerInput) (hFC : AutPSL2FieldCentralizerInput)
    (hKG : AutPSL2SylowInput) (hc : L2Ctx hs W) {g x : X} (hg : g ∈ W)
    (hx : x ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ closure ({t, z} : Set X)) :
    g * x * g⁻¹ ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ closure ({t, z} : Set X) := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  obtain ⟨v, hv⟩ := hc.exists_sylowAutData hKG
  have hxW := hc.N0_le hx
  have hgxW : g * x * g⁻¹ ∈ W := W.mul_mem (W.mul_mem hg hxW) (W.inv_mem hg)
  refine hc.mem_N0_of_conjOn_mem hKC hFC hv hgxW ?_
  have hxc := hc.conjOn_mem_of_mem_N0 hKC hFC hx
  have heq : conjOn (layer (MBar β)) (QuotientGroup.mk ⟨g * x * g⁻¹, hc.sylow.le hgxW⟩) =
      conjOn (layer (MBar β)) (QuotientGroup.mk ⟨g, hc.sylow.le hg⟩) *
        conjOn (layer (MBar β)) (QuotientGroup.mk ⟨x, hc.sylow.le hxW⟩) *
        (conjOn (layer (MBar β)) (QuotientGroup.mk ⟨g, hc.sylow.le hg⟩))⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [heq]
  set π := conjOn (layer (MBar β)) (QuotientGroup.mk ⟨g, hc.sylow.le hg⟩) with hπ
  have hπP : π ∈ (barOf M W).map (conjOn (layer (MBar β))) := ⟨_, mk_mem_barOf _ hg, rfl⟩
  refine Subgroup.mem_centralizer_iff.mpr fun r hr => ?_
  have hrR : π⁻¹ * r * π ∈ (barOf M W).map (conjOn (layer (MBar β))) ⊓
      innAut ↥(layer (MBar β)) := by
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hπP) hr.1) hπP, ?_⟩
    obtain ⟨y, hy⟩ := hr.2
    refine ⟨π⁻¹ y, ?_⟩
    rw [← hy]
    have := EndB.mul_conj_mul_inv π⁻¹ y
    rw [inv_inv] at this
    exact this.symm
  have h1 := (Subgroup.mem_centralizer_iff.mp hxc) _ hrR
  calc r * (π * conjOn (layer (MBar β)) (QuotientGroup.mk ⟨x, hc.sylow.le hxW⟩) * π⁻¹) =
        π * ((π⁻¹ * r * π) * conjOn (layer (MBar β))
          (QuotientGroup.mk ⟨x, hc.sylow.le hxW⟩)) * π⁻¹ := by group
    _ = π * (conjOn (layer (MBar β)) (QuotientGroup.mk ⟨x, hc.sylow.le hxW⟩) *
          (π⁻¹ * r * π)) * π⁻¹ := by rw [h1]
    _ = _ := by group

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit
