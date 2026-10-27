module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB2
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralAlg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem nonempty_pSimple_equiv_map_of_central {G H : Type} [Group G] [Group H] [Finite G] (p : ℕ)
    [Fact p.Prime] (f : G →* H) (hf : ∀ g : G, f g = 1 → g ∈ Subgroup.center G) {L : Subgroup G}
    (hL : Group.IsPerfect ↥L) : Nonempty (PSimple p L ≃* PSimple p (L.map f)) := by
  haveI := hL
  let φ : ↥L →* ↥(L.map f) := f.subgroupMap L
  have hφ : Function.Surjective φ := f.subgroupMap_surjective L
  have hker : φ.ker ≤ Subgroup.center ↥L := by
    intro l hl
    have h1 : f (l : G) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hl)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hf _ h1) (g : G))
  have hcore : GLAPPrimeCore p ↥(L.map f) = (GLAPPrimeCore p ↥L).map φ :=
    CFSG.HardMathSupport.Solomon.Coordinator.pPrimeCore_eq_map_of_central p φ hφ hker
  let ψ : PQuot p L →* PQuot p (L.map f) :=
    QuotientGroup.map (GLAPPrimeCore p ↥L) (GLAPPrimeCore p ↥(L.map f)) φ
      (Subgroup.map_le_iff_le_comap.1 hcore.ge)
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, rfl⟩ := hφ a'
    exact ⟨QuotientGroup.mk a, rfl⟩
  have hψker : ψ.ker ≤ Subgroup.center (PQuot p L) := by
    intro x hx
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    have h2 : φ l ∈ GLAPPrimeCore p ↥(L.map f) := (QuotientGroup.eq_one_iff _).1 hx
    rw [hcore] at h2
    obtain ⟨n, hn, hnl⟩ := Subgroup.mem_map.1 h2
    have hz : n⁻¹ * l ∈ Subgroup.center ↥L :=
      hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hnl, inv_mul_cancel])
    have e : (QuotientGroup.mk l : PQuot p L) = QuotientGroup.mk (n⁻¹ * l) := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (Subgroup.inv_mem _ hn), one_mul]
    rw [e, Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (Subgroup.mem_center_iff.1 hz g')
  haveI : Group.IsPerfect (PQuot p L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (GLAPPrimeCore p ↥L))
      (QuotientGroup.mk'_surjective _)
  exact Y10F.quotEquiv_of_perfect_central ψ hψ inferInstance hψker

namespace S172Model

variable {Ω : Type} [Group Ω] {S B : Subgroup Ω} {G₀ : Type} [Group G₀] (M : S172Model S B G₀)

theorem π_eq_one_mem_center {g : ↥S} (hg : M.π g = 1) : g ∈ Subgroup.center ↥S := by
  rw [← M.ker_π]
  exact hg

theorem nonempty_pSimple_equiv_map [Finite Ω] (p : ℕ) [Fact p.Prime] {K : Subgroup ↥S}
    (hK : Group.IsPerfect ↥K) : Nonempty (PSimple p K ≃* PSimple p (K.map M.π)) :=
  nonempty_pSimple_equiv_map_of_central p M.π (fun _ hg => M.π_eq_one_mem_center hg) hK

theorem conjHom_eq_self_of_mem_centralizer {K : Subgroup ↥S} (hK : Group.IsPerfect ↥K) {b : ↥B}
    (hb : M.β b ∈ Subgroup.centralizer ((K.map M.π : Subgroup G₀) : Set G₀)) {k : ↥S} (hk : k ∈ K) :
    M.conjHom b k = k := by
  have hz : ∀ k : ↥S, k ∈ K → M.conjHom b k * k⁻¹ ∈ Subgroup.center ↥S := by
    intro k hk
    rw [← M.ker_π, MonoidHom.mem_ker, map_mul, map_inv, M.π_conjHom b k]
    have h : M.π k * M.β b = M.β b * M.π k :=
      Subgroup.mem_centralizer_iff.1 hb (M.π k) (Subgroup.mem_map_of_mem _ hk)
    calc M.β b * M.π k * (M.β b)⁻¹ * (M.π k)⁻¹
        = (M.β b * M.π k) * (M.β b)⁻¹ * (M.π k)⁻¹ := by rfl
      _ = (M.π k * M.β b) * (M.β b)⁻¹ * (M.π k)⁻¹ := by rw [h]
      _ = 1 := by group
  let χ : ↥K →* ↥S :=
    { toFun := fun k => M.conjHom b (k : ↥S) * (k : ↥S)⁻¹
      map_one' := by simp
      map_mul' := fun k₁ k₂ => by
        have hc := Subgroup.mem_center_iff.1 (hz (k₂ : ↥S) k₂.2) ((k₁ : ↥S)⁻¹)
        calc M.conjHom b ((k₁ : ↥S) * (k₂ : ↥S)) * ((k₁ : ↥S) * (k₂ : ↥S))⁻¹
            = M.conjHom b (k₁ : ↥S) * ((M.conjHom b (k₂ : ↥S) * (k₂ : ↥S)⁻¹) * (k₁ : ↥S)⁻¹) := by
              rw [map_mul, mul_inv_rev]; group
          _ = M.conjHom b (k₁ : ↥S) * ((k₁ : ↥S)⁻¹ * (M.conjHom b (k₂ : ↥S) * (k₂ : ↥S)⁻¹)) := by
              rw [hc]
          _ = (M.conjHom b (k₁ : ↥S) * (k₁ : ↥S)⁻¹) * (M.conjHom b (k₂ : ↥S) * (k₂ : ↥S)⁻¹) := by
              group }
  have hker : commutator ↥K ≤ χ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ c _
    have h : χ c * χ a = χ a * χ c := Subgroup.mem_center_iff.1 (hz (a : ↥S) a.2) (χ c)
    simp only [commutatorElement_def, MonoidHom.mem_ker, map_mul, map_inv]
    calc χ a * χ c * (χ a)⁻¹ * (χ c)⁻¹ = χ c * χ a * (χ a)⁻¹ * (χ c)⁻¹ := by rw [h]
      _ = 1 := by group
  haveI := hK
  rw [Group.IsPerfect.commutator_eq_top] at hker
  have h1 : χ ⟨k, hk⟩ = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top _))
  exact mul_inv_eq_one.1 h1

theorem mem_centralizer_map_iff {K : Subgroup ↥S} (hK : Group.IsPerfect ↥K) (b : ↥B) :
    (b : Ω) ∈ Subgroup.centralizer ((K.map S.subtype : Subgroup Ω) : Set Ω) ↔
      M.β b ∈ Subgroup.centralizer ((K.map M.π : Subgroup G₀) : Set G₀) := by
  constructor
  · intro hb
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    have hbk : M.conjHom b k = k := by
      apply Subtype.ext
      rw [coe_conjHom]
      have h := Subgroup.mem_centralizer_iff.1 hb (k : Ω) (Subgroup.mem_map_of_mem _ hk)
      calc (b : Ω) * k * (b : Ω)⁻¹ = (k : Ω) * b * (b : Ω)⁻¹ := by rw [← h]
        _ = k := by group
    have h2 := M.π_conjHom b k
    rw [hbk] at h2
    calc M.π k * M.β b = (M.β b * M.π k * (M.β b)⁻¹) * M.β b := by rw [← h2]
      _ = M.β b * M.π k := by group
  · intro hb
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    have h := M.conjHom_eq_self_of_mem_centralizer hK hb hk
    have h2 := congrArg Subtype.val h
    rw [coe_conjHom] at h2
    show (k : Ω) * b = b * k
    calc (k : Ω) * b = ((b : Ω) * k * (b : Ω)⁻¹) * b := by rw [h2]
      _ = b * k := by group

end S172Model

end CFSG.LocalAnalysis.GLTheoremA.S172X

end
