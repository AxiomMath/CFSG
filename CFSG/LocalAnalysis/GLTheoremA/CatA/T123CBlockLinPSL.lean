module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockAbs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockLinA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockLinDefs
public import CFSG.RankThree.PartOne.KC.LinearCommutantLift
public import CFSG.RankThree.PartOne.FOC.CentralQuot

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123CB

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem centralizer_image_eq_map_of_comm {S T : Type*} [Group S] [Group T] (f : S →* T)
    (hf : Function.Surjective f) {X : Set S}
    (hc : ∀ x ∈ X, ∀ g : S, f x * f g = f g * f x → x * g = g * x) :
    Subgroup.centralizer (f '' X) = (Subgroup.centralizer X).map f := by
  ext w
  constructor
  · intro hw
    obtain ⟨g, rfl⟩ := hf w
    refine ⟨g, Subgroup.mem_centralizer_iff.2 fun x hx => hc x hx g ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.1 hw (f x) ⟨x, hx, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hg x hx]

private theorem isComponentOf_map_of_normalized {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hker : ∀ g : G, f g = 1 → g ∈ Subgroup.center G) {C P : Subgroup G} (hPC : P ≤ C)
    (hPN : ∀ g ∈ C, ∀ x ∈ P, g * x * g⁻¹ ∈ P) (hPq : CFSG.IsQuasisimple ↥P) :
    CFSG.Open.IsComponentOf (P.map f) (C.map f) := by
  have hnot : ¬ P ≤ f.ker := fun hle =>
    CFSG.RankThree.PartOne.not_le_center_of_isQuasisimple hPq fun x hx =>
      hker x (MonoidHom.mem_ker.1 (hle hx))
  have hq := CFSG.LocalCores.isQuasisimple_map hPq f hnot
  have hN : (P.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff hPC).2 fun x g hx hg => hPN g hg x hx
  exact ⟨Subgroup.map_mono hPC,
    (CFSG.Open.IsSubnormal.step hPC hN (CFSG.Open.IsSubnormal.refl C)).map f,
    hq.1.commutator_eq_top, hq.2.1⟩

theorem innerBlockAt_projectiveSL_of_sl {p n : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hn : 1 ≤ n) (hZp : ∀ c : Kˣ, c ^ p = 1 → c ^ n = 1 → c = 1)
    (h : SLInnerBlockAt p n K) : InnerBlockAt p (projectiveSL n K) := by
  intro A a hA hAc haA ha1 hns
  have hZ : ¬ p ∣ Nat.card (proj n K).ker :=
    CFSG.RankThree.PartOne.KCLinComm.not_dvd_card_ker_proj hp hn hZp
  have hZ' : ¬ p ∣ Nat.card (scalars n K) := by rwa [ker_proj] at hZ
  have hker : ∀ g : Matrix.SpecialLinearGroup (Fin n) K, proj n K g = 1 →
      g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := fun g hg =>
    scalars_le_center n K (proj_eq_one_iff.1 hg)
  haveI : CFSG.IsElementaryAbelian p A := hA.isElementaryAbelian
  obtain ⟨E0, hE0, hE0c, hE0A⟩ := CFSG.RankThree.PartOne.exists_lift_elementaryAbelian
    (proj n K) hp hZ A (fun x _ => MonoidHom.mem_range.2 (proj_surjective n K x)) hAc
  haveI := hE0
  have hE0p : ∀ x ∈ E0, x ^ p = 1 := fun x hx =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
  have hinj : ∀ x ∈ E0, ∀ y ∈ E0, proj n K x = proj n K y → x = y := by
    intro x hx y hy hxy
    have h1 : proj n K (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    exact inv_mul_eq_one.1 (CFSG.RankThree.PartOne.FOC.eq_one_of_pow_eq_one_of_not_dvd_card
      (scalars n K) hp hZ' (proj_eq_one_iff.1 h1) (hE0p _ (E0.mul_mem (E0.inv_mem hx) hy)))
  have hcomm : ∀ x ∈ E0, ∀ g : Matrix.SpecialLinearGroup (Fin n) K,
      proj n K x * proj n K g = proj n K g * proj n K x → x * g = g * x := fun x hx g hc =>
    CFSG.RankThree.PartOne.FOC.commute_of_mk_commute (scalars n K) hp hZ'
      (scalars_le_center n K) (hE0p x hx) hc
  subst hE0A
  have hCA : Subgroup.centralizer (↑(E0.map (proj n K)) : Set (projectiveSL n K)) =
      (Subgroup.centralizer (E0 : Set (Matrix.SpecialLinearGroup (Fin n) K))).map (proj n K) := by
    rw [Subgroup.coe_map]
    exact centralizer_image_eq_map_of_comm (proj n K) (proj_surjective n K) hcomm
  have hCa : ∀ a' ∈ E0, Subgroup.centralizer ({proj n K a'} : Set (projectiveSL n K)) =
      (Subgroup.centralizer ({a'} : Set (Matrix.SpecialLinearGroup (Fin n) K))).map
        (proj n K) := by
    intro a' ha'
    rw [show ({proj n K a'} : Set (projectiveSL n K)) = proj n K '' {a'} from
      Set.image_singleton.symm]
    exact centralizer_image_eq_map_of_comm (proj n K) (proj_surjective n K) fun x hx g hc =>
      hcomm x (by rwa [Set.mem_singleton_iff.1 hx]) g hc
  have hns' : ¬ Group.IsSolvable ↥(Subgroup.centralizer
      (E0 : Set (Matrix.SpecialLinearGroup (Fin n) K))) := by
    intro hsol
    rw [hCA] at hns
    exact hns (Group.isSolvable_of_surjective ((proj n K).subgroupMap_surjective _))
  obtain ⟨â, hâE, hâa⟩ := Subgroup.mem_map.1 haA
  have hâ1 : â ≠ 1 := fun h1 => ha1 (by rw [← hâa, h1, map_one])
  obtain ⟨a', ha'E, ha'â, P, M, hPC, hPN, hPq, hMC, hMN, hMq, hPM, hPd, hâM⟩ :=
    h E0 hE0 hE0c â hâE hâ1 hns'
  have hPperf : ⁅P, P⁆ = P :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.comm_self_eq_of_commutator_top hPq.1.commutator_eq_top
  have hPd' : p ∣ Nat.card (↥(P.map (proj n K)) ⧸ Subgroup.center ↥(P.map (proj n K))) := by
    rw [card_center_quot_map (proj n K) hker hPperf]
    exact hPd
  refine ⟨proj n K a', Subgroup.mem_map_of_mem _ ha'E, ?_, P.map (proj n K), M.map (proj n K),
    ?_, ?_, Subgroup.map_mono hPM, hPd', dvd_card_quot_center_of_le (Subgroup.map_mono hPM) hPd',
    ?_⟩
  · intro hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
    refine ha'â (Subgroup.mem_zpowers_iff.2 ⟨k, hinj _ (E0.zpow_mem hâE k) a' ha'E ?_⟩)
    rw [map_zpow, hâa, hk]
  · rw [hCA]
    exact isComponentOf_map_of_normalized (proj n K) hker hPC hPN hPq
  · rw [hCa a' ha'E]
    exact isComponentOf_map_of_normalized (proj n K) hker hMC hMN hMq
  · intro hc
    apply hâM
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h1 := Subgroup.mem_centralizer_iff.1 hc (proj n K m) (Subgroup.mem_map_of_mem _ hm)
    rw [← hâa] at h1
    exact (hcomm â hâE m h1.symm).symm

end CFSG.LocalAnalysis.GLTheoremA.T123CB

end
