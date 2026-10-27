module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F1Wr
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {t : G} {T1 T2 : Subgroup G}

@[expose] def sec8t84g4_diag (W : Sec8T84Wr G t T1 T2) : ↥T1 →* G where
  toFun a := (a : G) * (t * (a : G) * t⁻¹)
  map_one' := by simp
  map_mul' a b := by
    have hta : t * (a : G) * t⁻¹ ∈ T2 := W.swap1 a a.2
    have hcomm : (t * (a : G) * t⁻¹) * (b : G) = (b : G) * (t * (a : G) * t⁻¹) :=
      (W.comm (b : G) b.2 (t * (a : G) * t⁻¹) hta).symm
    show ((a : G) * (b : G)) * (t * ((a : G) * (b : G)) * t⁻¹) =
      ((a : G) * (t * (a : G) * t⁻¹)) * ((b : G) * (t * (b : G) * t⁻¹))
    rw [show t * ((a : G) * (b : G)) * t⁻¹ =
      (t * (a : G) * t⁻¹) * (t * (b : G) * t⁻¹) from by group]
    calc ((a : G) * (b : G)) * ((t * (a : G) * t⁻¹) * (t * (b : G) * t⁻¹))
        = (a : G) * ((b : G) * (t * (a : G) * t⁻¹)) * (t * (b : G) * t⁻¹) := by group
      _ = (a : G) * ((t * (a : G) * t⁻¹) * (b : G)) * (t * (b : G) * t⁻¹) := by rw [← hcomm]
      _ = ((a : G) * (t * (a : G) * t⁻¹)) * ((b : G) * (t * (b : G) * t⁻¹)) := by group

theorem sec8t84g4_diag_apply (W : Sec8T84Wr G t T1 T2) (a : ↥T1) :
    sec8t84g4_diag W a = (a : G) * (t * (a : G) * t⁻¹) := rfl

theorem sec8t84g4_diag_injective (W : Sec8T84Wr G t T1 T2) :
    Function.Injective (sec8t84g4_diag W) := fun a b h =>
  Subtype.ext (sec8t84_wr_diag_inj W a.2 b.2 h)

theorem sec8t84g4_diag_mem (W : Sec8T84Wr G t T1 T2) (a : ↥T1) :
    sec8t84g4_diag W a ∈ (T1 ⊔ T2) ⊓ centralizer ({t} : Set G) :=
  (sec8t84_wr_mem_cent W).mpr ⟨a, a.2, rfl⟩

theorem sec8t84g4_diag_conj (W : Sec8T84Wr G t T1 T2) {γ : G} (hγt : γ * t = t * γ)
    (a b : ↥T1) (hab : (b : G) = γ * a * γ⁻¹) :
    γ * sec8t84g4_diag W a * γ⁻¹ = sec8t84g4_diag W b := by
  rw [sec8t84g4_diag_apply, sec8t84g4_diag_apply, hab]
  have key : γ * t * (a : G) * t⁻¹ * γ⁻¹ = t * (γ * (a : G) * γ⁻¹) * t⁻¹ := by
    have e : γ * t * (a : G) * t⁻¹ * γ⁻¹ = (γ * t) * (a : G) * (γ * t)⁻¹ := by group
    rw [e, hγt]; group
  calc γ * ((a : G) * (t * (a : G) * t⁻¹)) * γ⁻¹
      = (γ * (a : G) * γ⁻¹) * (γ * t * (a : G) * t⁻¹ * γ⁻¹) := by group
    _ = (γ * (a : G) * γ⁻¹) * (t * (γ * (a : G) * γ⁻¹) * t⁻¹) := by rw [key]

@[expose] def sec8t84g4_diagSub (W : Sec8T84Wr G t T1 T2) (A : Subgroup G) : Subgroup G :=
  (A.subgroupOf T1).map (sec8t84g4_diag W)

theorem sec8t84g4_mem_diagSub (W : Sec8T84Wr G t T1 T2) {A : Subgroup G} {x : G} :
    x ∈ sec8t84g4_diagSub W A ↔ ∃ a ∈ A ⊓ T1, x = a * (t * a * t⁻¹) := by
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨a, ⟨Subgroup.mem_subgroupOf.mp ha, a.2⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact Subgroup.mem_map.mpr ⟨⟨a, ha.2⟩, Subgroup.mem_subgroupOf.mpr ha.1, rfl⟩

theorem sec8t84g4_diagSub_le (W : Sec8T84Wr G t T1 T2) (A : Subgroup G) :
    sec8t84g4_diagSub W A ≤ (T1 ⊔ T2) ⊓ centralizer ({t} : Set G) := by
  intro x hx
  obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp hx
  exact sec8t84g4_diag_mem W a

theorem sec8t84g4_card_diagSub (W : Sec8T84Wr G t T1 T2) {A : Subgroup G} (hA : A ≤ T1) :
    Nat.card ↥(sec8t84g4_diagSub W A) = Nat.card ↥A := by
  unfold sec8t84g4_diagSub
  rw [Subgroup.card_map_of_injective (sec8t84g4_diag_injective W)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv

theorem sec8t84g4_diagSub_sup (W : Sec8T84Wr G t T1 T2) {A A' : Subgroup G} (hA : A ≤ T1)
    (hA' : A' ≤ T1) :
    sec8t84g4_diagSub W (A ⊔ A') = sec8t84g4_diagSub W A ⊔ sec8t84g4_diagSub W A' := by
  unfold sec8t84g4_diagSub
  rw [Subgroup.subgroupOf_sup hA hA', Subgroup.map_sup]

theorem sec8t84g4_isElemAbelian_of_diagSub (W : Sec8T84Wr G t T1 T2) {A : Subgroup G}
    (hA : A ≤ T1) {p : ℕ} (h : IsElemAbelian p (sec8t84g4_diagSub W A)) : IsElemAbelian p A := by
  have h1 : IsElemAbelian p ((sec8t84g4_diagSub W A).comap (sec8t84g4_diag W)) :=
    h.comap (sec8t84g4_diag_injective W)
  have h2 : (sec8t84g4_diagSub W A).comap (sec8t84g4_diag W) = A.subgroupOf T1 :=
    Subgroup.comap_map_eq_self_of_injective (sec8t84g4_diag_injective W) _
  rw [h2] at h1
  have h3 := h1.map T1.subtype
  rwa [Subgroup.map_subgroupOf_eq_of_le hA] at h3

theorem sec8t84g4_diagSub_cent (W : Sec8T84Wr G t T1 T2) {A : Subgroup G} (hA : A ≤ T1) {γ : G}
    (hγt : γ * t = t * γ) (hγ : γ ∈ normalizer (A : Set G)) :
    sec8t84g4_diagSub W (A ⊓ centralizer ({γ} : Set G)) =
      sec8t84g4_diagSub W A ⊓ centralizer ({γ} : Set G) := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := (sec8t84g4_mem_diagSub W).mp hx
    have haT : a ∈ T1 := ha.2
    have hac : a * γ = γ * a := Subgroup.mem_centralizer_singleton_iff.mp ha.1.2
    have hconj : γ * sec8t84g4_diag W ⟨a, haT⟩ * γ⁻¹ = sec8t84g4_diag W ⟨a, haT⟩ := by
      apply sec8t84g4_diag_conj W hγt
      show a = γ * a * γ⁻¹
      rw [← hac]; group
    refine Subgroup.mem_inf.mpr ⟨(sec8t84g4_mem_diagSub W).mpr ⟨a, ⟨ha.1.1, haT⟩, rfl⟩, ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    show sec8t84g4_diag W ⟨a, haT⟩ * γ = γ * sec8t84g4_diag W ⟨a, haT⟩
    calc sec8t84g4_diag W ⟨a, haT⟩ * γ = (γ * sec8t84g4_diag W ⟨a, haT⟩ * γ⁻¹) * γ := by
          rw [hconj]
      _ = γ * sec8t84g4_diag W ⟨a, haT⟩ := by group
  · intro hx
    obtain ⟨hxd, hxc⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨a, ha, rfl⟩ := (sec8t84g4_mem_diagSub W).mp hxd
    have haT : a ∈ T1 := ha.2
    have hbA : γ * a * γ⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hγ a).mp ha.1
    have hbT : γ * a * γ⁻¹ ∈ T1 := hA hbA
    have hconj : γ * sec8t84g4_diag W ⟨a, haT⟩ * γ⁻¹ = sec8t84g4_diag W ⟨_, hbT⟩ :=
      sec8t84g4_diag_conj W hγt _ _ rfl
    have hxc' : sec8t84g4_diag W ⟨a, haT⟩ * γ = γ * sec8t84g4_diag W ⟨a, haT⟩ :=
      Subgroup.mem_centralizer_singleton_iff.mp hxc
    have hfix : γ * sec8t84g4_diag W ⟨a, haT⟩ * γ⁻¹ = sec8t84g4_diag W ⟨a, haT⟩ := by
      rw [← hxc']; group
    have hba : γ * a * γ⁻¹ = a :=
      congrArg Subtype.val (sec8t84g4_diag_injective W (hconj.symm.trans hfix))
    refine (sec8t84g4_mem_diagSub W).mpr
      ⟨a, Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨ha.1, ?_⟩, haT⟩, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc a * γ = (γ * a * γ⁻¹) * γ := by rw [hba]
      _ = γ * a := by group

end CFSG.OddStandard.SmallF3.Omega
