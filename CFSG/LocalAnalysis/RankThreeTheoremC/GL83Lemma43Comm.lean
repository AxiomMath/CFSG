module

public import CFSG.Quasithin.Background.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.Quasithin.Background.Equivariance

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits Subgroup

variable {G : Type} [Group G]

theorem l43_card_commutator_conj {X M : Subgroup G} (hMX : M ≤ normalizer (X : Set G)) {m u : G}
    (hm : m ∈ M) :
    Nat.card (⁅X, zpowers (m * u * m⁻¹)⁆ : Subgroup G) =
      Nat.card (⁅X, zpowers u⁆ : Subgroup G) := by
  have hX : X.map (MulAut.conj m).toMonoidHom = X := map_conj_eq_of_mem_normalizer (hMX hm)
  have hz : (zpowers u).map (MulAut.conj m).toMonoidHom = zpowers (m * u * m⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  have h1 : (⁅X, zpowers u⁆ : Subgroup G).map (MulAut.conj m).toMonoidHom =
      ⁅X, zpowers (m * u * m⁻¹)⁆ := by
    rw [Subgroup.map_commutator, hX, hz]
  rw [← h1]
  exact Subgroup.card_map_of_injective (fun a b h => (MulAut.conj m).injective h)

theorem l43_isElemAbelian_omegaOneCenter {R : Subgroup G} (hR : IsPGroup 2 R) :
    IsElemAbelian 2 (omegaOneCenterOf R) := by
  have _ := hR
  have hle : omegaOneCenterOf R ≤ centerOf R := (Subgroup.closure_le _).mpr fun _ hx => hx.1
  have hcomm : ∀ x ∈ centerOf R, ∀ y ∈ centerOf R, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp hx.2 y hy.1).symm
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ (hle a.2) _ (hle b.2))⟩⟩, fun x hx => ?_⟩
  change x ∈ Subgroup.closure {x : G | x ∈ centerOf R ∧ x ^ 2 = 1} at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    rw [Commute.mul_pow (hcomm _ (hle hx) _ (hle hy)) 2, ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem l43_normalizer_omegaOneCenter {R N : Subgroup G} (h : N ≤ normalizer (R : Set G)) :
    N ≤ normalizer (omegaOneCenterOf R : Set G) := fun _ hn =>
  normalizer_le_normalizer_of_map_mulEquiv omegaOneCenterOf_map_mulEquiv R (h hn)

theorem l43_card_commutator_omegaOneCenter {M W : Subgroup G} {u : G} (hWM : W ≤ M) (hu : u ∈ W)
    (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) (hF : CharTwo M) (hO₂ : pCoreOf 2 M ≤ pCoreOf 2 W)
    (h4 : Nat.card (⁅pCoreOf 2 W, zpowers u⁆ : Subgroup G) = 4 ∧
      ⁅pCoreOf 2 W, zpowers u⁆ ≤ omegaOneCenterOf (pCoreOf 2 W) ∧
      ⁅omegaOneCenterOf (pCoreOf 2 W), zpowers u⁆ = ⁅pCoreOf 2 W, zpowers u⁆) :
    Nat.card (⁅omegaOneCenterOf (pCoreOf 2 M), zpowers u⁆ : Subgroup G) = 4 := by
  have _ := hu
  have _ := hu3
  have _ := hu1
  obtain ⟨hcard, -, hZ⟩ := h4
  have hZR : omegaOneCenterOf (pCoreOf 2 W) ≤ pCoreOf 2 W :=
    (Subgroup.closure_le _).mpr fun _ hx => hx.1.1
  have hZM : omegaOneCenterOf (pCoreOf 2 W) ≤ M :=
    hZR.trans ((pCoreOf_le 2 W).trans hWM)
  have hZc' : omegaOneCenterOf (pCoreOf 2 W) ≤ Subgroup.centralizer (pCoreOf 2 W : Set G) :=
    (Subgroup.closure_le _).mpr fun _ hx => hx.1.2
  have hZc : omegaOneCenterOf (pCoreOf 2 W) ≤ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
    fun z hz => Subgroup.centralizer_le hO₂ (hZc' hz)
  have hZF : omegaOneCenterOf (pCoreOf 2 W) ≤ pCoreOf 2 M := fun z hz =>
    hF ⟨hZM hz, hZc hz⟩
  have hZX : omegaOneCenterOf (pCoreOf 2 W) ≤ omegaOneCenterOf (pCoreOf 2 M) := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    have hxZ : x ∈ omegaOneCenterOf (pCoreOf 2 W) := Subgroup.subset_closure hx
    exact Subgroup.subset_closure ⟨⟨hZF hxZ, hZc hxZ⟩, hx.2⟩
  have hXR : omegaOneCenterOf (pCoreOf 2 M) ≤ pCoreOf 2 W :=
    ((Subgroup.closure_le _).mpr fun _ hx => hx.1.1).trans hO₂
  have heq : ⁅omegaOneCenterOf (pCoreOf 2 M), zpowers u⁆ = ⁅pCoreOf 2 W, zpowers u⁆ :=
    le_antisymm (Subgroup.commutator_mono hXR le_rfl)
      (hZ ▸ Subgroup.commutator_mono hZX le_rfl)
  rw [heq]
  exact hcard

end CFSG.LocalAnalysis.RankThreeTheoremC
