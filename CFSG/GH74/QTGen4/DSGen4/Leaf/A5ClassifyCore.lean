module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyFrame

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem conj_mem_pCoreOf {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    {x : G} (hx : x ∈ pCoreOf 2 L) : g * x * g⁻¹ ∈ pCoreOf 2 L := by
  let φ : ↥L ≃* ↥L :=
    ((MulAut.conj g).subgroupMap L).trans
      (MulEquiv.subgroupCongr (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg))
  obtain ⟨y, hy, rfl⟩ := hx
  have hfix := (inferInstance : (pCore 2 ↥L).Characteristic).fixed φ
  have hy' : φ y ∈ pCore 2 ↥L := by
    have : y ∈ (pCore 2 ↥L).comap φ.toMonoidHom := by rw [hfix]; exact hy
    exact Subgroup.mem_comap.mp this
  exact ⟨φ y, hy', rfl⟩

theorem normalizer_le_normalizer_pCoreOf (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_pCoreOf hg hx, fun hx => ?_⟩
  have := conj_mem_pCoreOf (Subgroup.inv_mem _ hg) hx
  simpa [mul_assoc] using this

theorem pCoreOf_le_pCoreOf [Finite G] {P L : Subgroup G} (hLP : L ≤ P)
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) : pCoreOf 2 L ≤ pCoreOf 2 P :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLP)
    (hPL.trans (normalizer_le_normalizer_pCoreOf L))
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L)

theorem eq_one_of_mulVec_eq (A : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (h : ∀ v : Fin 4 → ZMod 2, A *ᵥ v = v) : A = 1 := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h v, Matrix.one_mulVec]

namespace ElemFrame

variable {P E K : Subgroup G}

theorem phi_comm (F : ElemFrame P E K) (hPE : P ≤ Subgroup.normalizer (E : Set G))
    (p : ↥P) (e c : ↥E) (hc : (c : G) = ⁅(e : G), (p : G)⁆) :
    Multiplicative.toAdd (F.φ c) =
      Multiplicative.toAdd (F.φ e) - glMat (F.M p) *ᵥ Multiplicative.toAdd (F.φ e) := by
  have h := F.act p e (conjE hPE p e) (coe_conjE hPE p e)
  have hc' : c = e * (conjE hPE p e)⁻¹ := by
    apply Subtype.ext
    rw [hc]
    simp only [coe_conjE, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  rw [hc', map_mul, map_inv, toAdd_mul, toAdd_inv, h]
  abel

theorem phi_comm' (F : ElemFrame P E K) (hPE : P ≤ Subgroup.normalizer (E : Set G))
    (p : ↥P) (e c : ↥E) (hc : (c : G) = ⁅(p : G), (e : G)⁆) :
    Multiplicative.toAdd (F.φ c) =
      glMat (F.M p) *ᵥ Multiplicative.toAdd (F.φ e) - Multiplicative.toAdd (F.φ e) := by
  have h := F.act p e (conjE hPE p e) (coe_conjE hPE p e)
  have hc' : c = conjE hPE p e * e⁻¹ := by
    apply Subtype.ext
    rw [hc]
    simp only [coe_conjE, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
  rw [hc', map_mul, map_inv, toAdd_mul, toAdd_inv, h]
  abel

theorem comm_left_mem (hPE : P ≤ Subgroup.normalizer (E : Set G)) {p : G} (hp : p ∈ P) {e : G}
    (he : e ∈ E) : ⁅p, e⁆ ∈ E := by
  have : ⁅p, e⁆ = (p * e * p⁻¹) * e⁻¹ := by simp [commutatorElement_def]
  rw [this]
  exact E.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPE hp) _).mp he) (E.inv_mem he)

theorem comm_right_mem (hPE : P ≤ Subgroup.normalizer (E : Set G)) {p : G} (hp : p ∈ P) {e : G}
    (he : e ∈ E) : ⁅e, p⁆ ∈ E := by
  rw [← commutatorElement_inv]
  exact E.inv_mem (comm_left_mem hPE hp he)

theorem M_eq_one (F : ElemFrame P E K) (hPE : P ≤ Subgroup.normalizer (E : Set G))
    (p : ↥P) (hp : ∀ e ∈ E, ⁅(p : G), e⁆ ∈ K) : F.M p = 1 := by
  apply Units.ext
  rw [Units.val_one]
  apply eq_one_of_mulVec_eq
  intro v
  obtain ⟨e, he⟩ := F.surj (Multiplicative.ofAdd v)
  have hv : v = Multiplicative.toAdd (F.φ e) := by rw [he]; rfl
  rw [hv]
  have hcomm : ⁅(p : G), ((e : ↥E) : G)⁆ ∈ K := hp e e.2
  let c : ↥E := ⟨⁅(p : G), ((e : ↥E) : G)⁆, comm_left_mem hPE p.2 e.2⟩
  have hφ := F.phi_comm' hPE p e c rfl
  have hc1 : F.φ c = 1 := (F.ker c).mpr hcomm
  rw [hc1, toAdd_one] at hφ
  exact (sub_eq_zero.mp hφ.symm)

theorem comm_mem_of_M_eq_one (F : ElemFrame P E K) (hPE : P ≤ Subgroup.normalizer (E : Set G))
    (p : ↥P) (hp : F.M p = 1) {e : G} (he : e ∈ E) : ⁅(p : G), e⁆ ∈ K := by
  let c : ↥E := ⟨⁅(p : G), e⁆, comm_left_mem hPE p.2 he⟩
  have hφ := F.phi_comm' hPE p ⟨e, he⟩ c rfl
  have h1 : glMat (1 : GL (Fin 4) (ZMod 2)) = 1 := Units.val_one
  rw [hp, h1, Matrix.one_mulVec, sub_self] at hφ
  exact (F.ker c).mp (by
    apply Multiplicative.toAdd.injective
    simpa using hφ)

end ElemFrame

end CFSG.GH74.QTGen4.DSGen4
