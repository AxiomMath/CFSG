module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ScalarTorus
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CentralAuxTorus
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordProd

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.LieType.Steinberg.Adjoint

set_option linter.unusedSectionVars false


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]

theorem scalar_conj_trivial {γ : Fin τ.rank → ℤ} {l : ModGL τ L}
    (hl : l ∈ Subgroup.normalizer (rootSubgroup τ L γ : Set (ModGL τ L)))
    (t : Lˣ → ModGL τ L) (ht : ∀ lam, t lam * l = l * t lam) {e : ℤ} (he : e ≠ 0)
    (hconj : ∀ (lam : Lˣ) (c : L), t lam * pinnedX τ L γ c * (t lam)⁻¹ =
      pinnedX τ L γ (((lam ^ e : Lˣ) : L) * c))
    (h1 : l * pinnedX τ L γ 1 * l⁻¹ = pinnedX τ L γ 1) :
    ∀ c, l * pinnedX τ L γ c * l⁻¹ = pinnedX τ L γ c := by
  have hmem : ∀ c, ∃ d, pinnedX τ L γ d = l * pinnedX τ L γ c * l⁻¹ := fun c =>
    mem_rootSubgroup.1 ((Subgroup.mem_normalizer_iff.1 hl _).1 (mem_rootSubgroup.2 ⟨c, rfl⟩))
  choose u hu using hmem
  have hinj := pinnedX_injective τ L γ
  have hadd : ∀ c c', u (c + c') = u c + u c' := fun c c' => by
    apply hinj
    rw [hu (c + c'), pinnedX_add, pinnedX_add, hu c, hu c']
    group
  have h0 : u 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    have h2 : u 0 + u 0 = u 0 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  have hu1 : u 1 = 1 := by
    apply hinj
    rw [hu, h1]
  have hsc : ∀ (lam : Lˣ) (c : L), u (((lam ^ e : Lˣ) : L) * c) = ((lam ^ e : Lˣ) : L) * u c := by
    intro lam c
    apply hinj
    have e1 : l * (t lam * pinnedX τ L γ c * (t lam)⁻¹) * l⁻¹ =
        t lam * (l * pinnedX τ L γ c * l⁻¹) * (t lam)⁻¹ := by
      have h : l * t lam = t lam * l := (ht lam).symm
      calc l * (t lam * pinnedX τ L γ c * (t lam)⁻¹) * l⁻¹
          = (l * t lam) * pinnedX τ L γ c * (l * t lam)⁻¹ := by group
        _ = (t lam * l) * pinnedX τ L γ c * (t lam * l)⁻¹ := by rw [h]
        _ = t lam * (l * pinnedX τ L γ c * l⁻¹) * (t lam)⁻¹ := by group
    rw [hu, ← hconj lam c, e1, ← hu c, hconj lam (u c)]
  have huid : ∀ c, u c = c := by
    intro c
    by_cases hc : c = 0
    · rw [hc, h0]
    · obtain ⟨lam, hlam⟩ := units_zpow_surjective L he (Units.mk0 c hc)
      have := hsc lam 1
      rw [mul_one, hu1, mul_one] at this
      have e2 : ((lam ^ e : Lˣ) : L) = c := by
        have := congrArg (fun x : Lˣ => (x : L)) hlam
        simpa using this
      rw [e2] at this
      exact this
  intro c
  rw [← hu c, huid c]

theorem iform_highRoot_self_ne_zero (τ : Tag) : iform (highRoot τ) (highRoot τ) ≠ 0 := by
  rw [iform_highRoot_apply, CoordAux.highRoot_degree]
  exact mul_ne_zero (cθ_ne_zero τ) two_ne_zero

omit [IsAlgClosed L] in
theorem Lθ_central_torus (lam : Lˣ) {l : ModGL τ L} (hl : l ∈ Lθ τ L) :
    rootTorusSL2 τ L (highRoot τ) lam * l = l * rootTorusSL2 τ L (highRoot τ) lam := by
  set h := rootTorusSL2 τ L (highRoot τ) lam with hh
  have hθ := isRoot_highRoot τ
  obtain ⟨-, hdH, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ L hθ
  have hconj0 : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → iform (highRoot τ) γ = 0 → ∀ c : L,
      h * pinnedX τ L γ c * h⁻¹ = pinnedX τ L γ c := by
    intro γ hγ h0 c
    rw [hh, ScalarTorusAux.torus_conj_pinnedX hθ hγ lam c, h0, mul_zero, Int.zero_ediv, zpow_zero]
    simp
  have hle : Lθ τ L ≤ Subgroup.centralizer ({h} : Set (ModGL τ L)) := by
    show torusGroup τ L ⊔ subsystemGroup τ L (Jθ τ) ≤ _
    refine sup_le ?_ ?_
    · intro t ht
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((triangular_borel_structure.{0, 0} τ L).1 h (hdH lam) t ht).symm
    · refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨j, hj, c, rfl | rfl⟩
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        have hj' : j ≠ iθ τ := hj
        have e := hconj0 (Pi.single j 1) (isRoot_single τ j) (by
          rw [iform_highRoot_apply]; simp [Pi.single_apply, hj']) c
        rw [pinnedX_single] at e
        exact (mul_inv_eq_iff_eq_mul.1 e).symm
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        have hj' : j ≠ iθ τ := hj
        have e := hconj0 (-Pi.single j 1) (isRoot_neg_single τ j) (by
          rw [iform_highRoot_apply]; simp [Pi.single_apply, hj']) c
        rw [pinnedX_neg_single] at e
        exact (mul_inv_eq_iff_eq_mul.1 e).symm
  have := Subgroup.mem_centralizer_singleton_iff.1 (hle hl)
  exact this.symm

theorem Lθ_centralizes_Uθ {l : ModGL τ L} (hl : l ∈ Lθ τ L)
    (h1 : l * pinnedX τ L (highRoot τ) 1 * l⁻¹ = pinnedX τ L (highRoot τ) 1) :
    ∀ x ∈ Uθ τ L, l * x = x * l := by
  have hθ := isRoot_highRoot τ
  have key := scalar_conj_trivial (γ := highRoot τ)
    (Pθ_le_normalizer_Uθ τ L (Lθ_le_Pθ τ L hl))
    (fun lam => rootTorusSL2 τ L (highRoot τ) lam) (fun lam => Lθ_central_torus lam hl)
    (e := 2) (by norm_num)
    (fun lam c => by
      rw [ScalarTorusAux.torus_conj_pinnedX hθ hθ lam c]
      have : 2 * iform (highRoot τ) (highRoot τ) / iform (highRoot τ) (highRoot τ) = 2 :=
        Int.mul_ediv_cancel 2 (iform_highRoot_self_ne_zero τ)
      rw [this]) h1
  intro x hx
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  have := key c
  exact (mul_inv_eq_iff_eq_mul.1 this)

theorem Lθ_centralizes_Uneg {l : ModGL τ L} (hl : l ∈ Lθ τ L)
    (h1 : l * pinnedX τ L (-highRoot τ) 1 * l⁻¹ = pinnedX τ L (-highRoot τ) 1) :
    ∀ x ∈ Heis.Uneg τ L, l * x = x * l := by
  have hθ := isRoot_highRoot τ
  have hnθ : IsRoot τ (-highRoot τ) := isRoot_neg_highRoot τ
  have key := scalar_conj_trivial (γ := -highRoot τ)
    (Lθ_le_normalizer_Uneg τ L hl)
    (fun lam => rootTorusSL2 τ L (highRoot τ) lam) (fun lam => Lθ_central_torus lam hl)
    (e := -2) (by norm_num)
    (fun lam c => by
      rw [ScalarTorusAux.torus_conj_pinnedX hθ hnθ lam c]
      have e1 : iform (highRoot τ) (-highRoot τ) = -iform (highRoot τ) (highRoot τ) := by
        rw [iform_highRoot_apply, iform_highRoot_apply]
        simp
      have : 2 * iform (highRoot τ) (-highRoot τ) / iform (highRoot τ) (highRoot τ) = -2 := by
        rw [e1, show 2 * -iform (highRoot τ) (highRoot τ) = (-2) * iform (highRoot τ) (highRoot τ)
          by ring]
        exact Int.mul_ediv_cancel (-2) (iform_highRoot_self_ne_zero τ)
      rw [this]) h1
  intro x hx
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  have := key c
  exact (mul_inv_eq_iff_eq_mul.1 this)

@[expose] def CQ (ĝ : ModGL τ L) : Subgroup (ModGL τ L) :=
  Qθ τ L ⊓ Subgroup.centralizer ({ĝ} : Set (ModGL τ L))

theorem mem_CQ {ĝ q : ModGL τ L} : q ∈ CQ ĝ ↔ q ∈ Qθ τ L ∧ ĝ * q = q * ĝ := by
  rw [CQ, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, h2.symm⟩

omit [IsAlgClosed L] in
theorem centralizes_sup {ĝ : ModGL τ L} (hθ : ∀ x ∈ Uθ τ L, ĝ * x = x * ĝ)
    (hn : ∀ x ∈ Heis.Uneg τ L, ĝ * x = x * ĝ) : ∀ x ∈ Uθ τ L ⊔ Heis.Uneg τ L, ĝ * x = x * ĝ := by
  have : Uθ τ L ⊔ Heis.Uneg τ L ≤ Subgroup.centralizer ({ĝ} : Set (ModGL τ L)) :=
    sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hθ x hx).symm)
      (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hn x hx).symm)
  exact fun x hx => (Subgroup.mem_centralizer_singleton_iff.1 (this hx)).symm

def Wsub (ĝ : ModGL τ L) (hθ : ∀ x ∈ Uθ τ L, ĝ * x = x * ĝ)
    (hn : ∀ x ∈ Heis.Uneg τ L, ĝ * x = x * ĝ) : Submodule L ((Fin τ.rank → ℤ) → L) where
  carrier := {v | ∃ q ∈ CQ ĝ, heisCoord τ L q = v}
  add_mem' := by
    rintro _ _ ⟨q, hq, rfl⟩ ⟨q', hq', rfl⟩
    exact ⟨q * q', mul_mem hq hq',
      (heisCoord_spec τ L).mul q (mem_CQ.1 hq).1 q' (mem_CQ.1 hq').1⟩
  zero_mem' := ⟨1, one_mem _, heisCoord_one⟩
  smul_mem' := by
    rintro lam _ ⟨q, hq, rfl⟩
    by_cases hl : lam = 0
    · subst hl
      rw [zero_smul]
      exact ⟨1, one_mem _, heisCoord_one⟩
    · obtain ⟨h, hhU, -, hh⟩ := exists_scalarTorus τ L hl
      have hcomm : ĝ * h = h * ĝ := centralizes_sup hθ hn h hhU
      obtain ⟨hQ, hc⟩ := hh q (mem_CQ.1 hq).1
      refine ⟨h * q * h⁻¹, mem_CQ.2 ⟨hQ, ?_⟩, hc⟩
      have hq' := (mem_CQ.1 hq).2
      have hcomm' : ĝ * h⁻¹ = h⁻¹ * ĝ := by
        calc ĝ * h⁻¹ = h⁻¹ * (h * ĝ) * h⁻¹ := by group
          _ = h⁻¹ * (ĝ * h) * h⁻¹ := by rw [hcomm]
          _ = h⁻¹ * ĝ := by group
      calc ĝ * (h * q * h⁻¹) = (ĝ * h) * q * h⁻¹ := by group
        _ = h * ĝ * q * h⁻¹ := by rw [hcomm]
        _ = h * (ĝ * q) * h⁻¹ := by group
        _ = h * (q * ĝ) * h⁻¹ := by rw [hq']
        _ = h * q * (ĝ * h⁻¹) := by group
        _ = h * q * (h⁻¹ * ĝ) := by rw [hcomm']
        _ = (h * q * h⁻¹) * ĝ := by group

theorem mem_CQ_of_coord {ĝ : ModGL τ L} (hθ : ∀ x ∈ Uθ τ L, ĝ * x = x * ĝ)
    (hn : ∀ x ∈ Heis.Uneg τ L, ĝ * x = x * ĝ) {q : ModGL τ L} (hq : q ∈ Qθ τ L)
    (hW : heisCoord τ L q ∈ Wsub ĝ hθ hn) : q ∈ CQ ĝ := by
  obtain ⟨q₀, hq₀, hc⟩ := hW
  have hq₀Q := (mem_CQ.1 hq₀).1
  have hq₀c := (mem_CQ.1 hq₀).2
  have hu : q₀⁻¹ * q ∈ Uθ τ L := by
    refine ((heisCoord_spec τ L).eq_zero_iff _ (mul_mem (inv_mem hq₀Q) hq)).1 ?_
    rw [(heisCoord_spec τ L).mul _ (inv_mem hq₀Q) _ hq, heisCoord_inv hq₀Q, hc]
    abel
  have huc := hθ _ hu
  refine mem_CQ.2 ⟨hq, ?_⟩
  calc ĝ * q = ĝ * (q₀ * (q₀⁻¹ * q)) := by group
    _ = (ĝ * q₀) * (q₀⁻¹ * q) := by group
    _ = (q₀ * ĝ) * (q₀⁻¹ * q) := by rw [hq₀c]
    _ = q₀ * (ĝ * (q₀⁻¹ * q)) := by group
    _ = q₀ * ((q₀⁻¹ * q) * ĝ) := by rw [huc]
    _ = q * ĝ := by group

theorem coord_mem_Wsub {ĝ : ModGL τ L} (hθ : ∀ x ∈ Uθ τ L, ĝ * x = x * ĝ)
    (hn : ∀ x ∈ Heis.Uneg τ L, ĝ * x = x * ĝ) {q : ModGL τ L} (hq : q ∈ CQ ĝ) :
    heisCoord τ L q ∈ Wsub ĝ hθ hn := ⟨q, hq, rfl⟩

theorem pinnedX_mem_CQ {ĝ : ModGL τ L} (hθ : ∀ x ∈ Uθ τ L, ĝ * x = x * ĝ)
    (hn : ∀ x ∈ Heis.Uneg τ L, ĝ * x = x * ĝ) {β : Fin τ.rank → ℤ} (hβ : β ∈ Deg1 τ) (c : L)
    (hW : (Pi.single β c : (Fin τ.rank → ℤ) → L) ∈ Wsub ĝ hθ hn) :
    pinnedX τ L β c ∈ CQ ĝ :=
  mem_CQ_of_coord hθ hn (pinnedX_mem_Qθ_of_mem_Deg1 hβ c) (by
    rw [(heisCoord_spec τ L).pinnedX_deg1 β hβ c]
    exact hW)

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux
