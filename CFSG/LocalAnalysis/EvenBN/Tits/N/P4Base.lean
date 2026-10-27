module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S17
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Elem

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits

section Generic

variable {Γ : Type*} [Group Γ]

theorem mem_normalizer_commutator {A B : Subgroup Γ} {g : Γ} (hA : g ∈ normalizer (A : Set Γ))
    (hB : g ∈ normalizer (B : Set Γ)) : g ∈ normalizer ((⁅A, B⁆ : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

theorem mem_normalizer_sup' {A B : Subgroup Γ} {g : Γ} (hA : g ∈ normalizer (A : Set Γ))
    (hB : g ∈ normalizer (B : Set Γ)) : g ∈ normalizer ((A ⊔ B : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem isF20_of_data {U : Subgroup Γ} {x v : Γ} (hU : IsElemAbelian 2 U) (hcard : Nat.card U = 16)
    (hxn : x ∈ normalizer (U : Set Γ)) (hvn : v ∈ normalizer (U : Set Γ)) (hx5 : x ^ 5 = 1)
    (hv4 : v ^ 4 = 1) (hvx : v * x * v⁻¹ = x ^ 3)
    (hfpf : ∀ u ∈ U, x * u * x⁻¹ = u → u = 1) : IsF20 U x v where
  comm := fun a ha b hb => congrArg Subtype.val (hU.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
  sq := fun a ha => by
    have := hU.2 a ha
    rwa [pow_two] at this
  card := hcard
  x_norm := hxn
  v_norm := hvn
  x5 := hx5
  v4 := hv4
  vx := Or.inr hvx
  fpf := hfpf

end Generic

section Star

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem star_mem_normalizer_Us (h49 : d.Thm49Statement) (hd : d.Hyp) {g : G} (hg : g ∈ CMt d)
    (hgX : g ∈ normalizer ((Xg d : Subgroup G) : Set G)) :
    star d g ∈ normalizer ((Us d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) := by
  have hO : g ∈ normalizer ((pCoreOf 2 (CMt d) : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (CMt d) hg
  have hOle : pCoreOf 2 (CMt d) ≤ normalizer (d.s56V : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (CMt_le_Hg h49 hd)
  have hXle : Xg d ≤ normalizer (d.s56V : Set G) := Xg_le_Hg h49 hd
  have hcomm : Us d = imgIn d.s56V ⁅pCoreOf 2 (CMt d), Xg d⁆ :=
    (imgIn_commutator d.s56V hOle hXle).symm
  rw [hcomm]
  exact actFun_mem_normalizer_imgIn d.s56V _ (CMt_le_Hg h49 hd hg) (mem_normalizer_commutator hO hgX)

theorem img_Xg (h49 : d.Thm49Statement) (hd : d.Hyp) : img d (Xg d) = zpowers (star d d.x₅) :=
  imgIn_zpowers d.s56V (x5_mem_Hg h49 hd)

theorem x5_mem_normalizer_Xg : d.x₅ ∈ normalizer ((Xg d : Subgroup G) : Set G) :=
  Subgroup.le_normalizer (mem_zpowers d.x₅)

theorem star_x5_mem_normalizer_Us (h49 : d.Thm49Statement) (hd : d.Hyp) :
    star d d.x₅ ∈ normalizer ((Us d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) :=
  star_mem_normalizer_Us h49 hd (Xg_le_CMt hd (mem_zpowers d.x₅)) x5_mem_normalizer_Xg

theorem node19b (h49 : d.Thm49Statement) (hd : d.Hyp) : Node19b d z₀ := by
  show img d (Xg d) ≤ Ks d
  rw [img_Xg h49 hd, Subgroup.zpowers_le]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · show star d d.x₅ ∈ normalizer (((Us d ⊔ zpowers (star d d.t) : Subgroup (MulAut ↥d.s56V))) :
      Set (MulAut ↥d.s56V))
    refine mem_normalizer_sup' (star_x5_mem_normalizer_Us h49 hd) ?_
    apply Subgroup.centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨n, rfl⟩ := hg
    have hc : Commute (star d d.t) (star d d.x₅) := by
      have := actFun_comm_of_comm d.s56V (g := d.x₅) (h := d.t) hd.s56_x5_comm_t
      exact this.symm
    exact (hc.zpow_left n).eq
  · exact actFun_mem_imgIn (x5_mem_Hg h49 hd) (x5_mem_Hg h49 hd)

end Star

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

section Final19b


theorem step19b_holds : Step19b := by
  intro G _ _ d z₀ h49 hd hz
  exact P4.node19b h49 hd

end Final19b

end CFSG.LocalAnalysis.EvenBN.Tits.N
