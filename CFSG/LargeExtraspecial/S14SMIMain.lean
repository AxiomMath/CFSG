module

public import CFSG.LargeExtraspecial.S14SMICert
public import CFSG.LargeExtraspecial.S14SMFMain
public import CFSG.LargeExtraspecial.S14SMGMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open CFSG.SmithE CFSG.F4.Native SMG

namespace SMI

theorem eq_of_braid {A B : Nat → Nat} (hAA : ∀ c < 2 ^ 20, A (A c) = c)
    (hBB : ∀ c < 2 ^ 20, B (B c) = c) (hAlt : ∀ c < 2 ^ 20, A c < 2 ^ 20)
    (hBlt : ∀ c < 2 ^ 20, B c < 2 ^ 20) (hc : ∀ c < 2 ^ 20, A (B c) = B (A c))
    (hbr : ∀ c < 2 ^ 20, A (B (A c)) = B (A (B c))) : ∀ c < 2 ^ 20, B c = A c := by
  intro c hc'
  calc B c = A (A (B c)) := (hAA _ (hBlt c hc')).symm
    _ = A (B (A c)) := by rw [hc c hc']
    _ = B (A (B c)) := hbr c hc'
    _ = B (B (A c)) := by rw [hc c hc']
    _ = A c := hBB _ (hAlt c hc')

variable {G : Type} [Group G] [Finite G]

theorem mul_mem_QG
    (hM : SmithE22Module) [IsSimpleGroup G] (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {a b : G} (ha : IsConj S.z a)
    (hb : IsConj S.z b) (haM : a ∈ S.M) (hbM : b ∈ S.M) (haQ : a ∉ S.QG) (hbQ : b ∉ S.QG)
    (hab : Commute a b) (habc : IsConj S.z (a * b)) : a * b ∈ S.QG := by
  by_contra habQ
  obtain ⟨φ, -, -, -, h4⟩ := hM G S hw hU
  have habM : a * b ∈ S.M := S.M.mul_mem haM hbM
  obtain ⟨k, hk, hA⟩ := h4 a ha haM haQ
  obtain ⟨l, hl, hB⟩ := h4 b hb hbM hbQ
  obtain ⟨m, hm, hC⟩ := h4 (a * b) habc habM habQ
  change Acts S φ a (applyCols (tvCols k)) at hA
  change Acts S φ b (applyCols (tvCols l)) at hB
  change Acts S φ (a * b) (applyCols (tvCols m)) at hC
  have hAA := hA.invol ha haM
  have hBB := hB.invol hb hbM
  have hAB := hA.mul hbM hB
  have hBA := hB.mul haM hA
  have e1 : ∀ c < 2 ^ 20,
      applyCols (tvCols m) c = applyCols (tvCols k) (applyCols (tvCols l) c) := by
    intro c hc
    obtain ⟨u, hu, rfl⟩ := exists_psi S φ hc
    rw [← hC u hu, hAB u hu]
  have e2 : ∀ c < 2 ^ 20,
      applyCols (tvCols m) c = applyCols (tvCols l) (applyCols (tvCols k) c) := by
    intro c hc
    obtain ⟨u, hu, rfl⟩ := exists_psi S φ hc
    rw [← hC u hu, hab.eq, hBA u hu]
  refine habQ (mem_QG_of_acts habM hC fun c hc => ?_)
  suffices hlk : ∀ c < 2 ^ 20, applyCols (tvCols l) c = applyCols (tvCols k) c by
    rw [e1 c hc, hlk c hc, hAA c hc]
  have hcomm : ∀ c < 2 ^ 20, applyCols (tvCols k) (applyCols (tvCols l) c) =
      applyCols (tvCols l) (applyCols (tvCols k) c) := fun c hc => (e1 c hc).symm.trans (e2 c hc)
  rcases lt_trichotomy k l with hkl | rfl | hkl
  · by_cases h0 : hermC uPts[k]! uPts[l]! = 0
    · exact absurd (prodCols_eq e1) (prodCols_ne hkl hl hm h0)
    · exact eq_of_braid hAA hBB (fun c hc => hA.lt hc) (fun c hc => hB.lt hc) hcomm
        ((pair_rel hkl hl).2 h0)
  · exact fun _ _ => rfl
  · by_cases h0 : hermC uPts[l]! uPts[k]! = 0
    · exact absurd (prodCols_eq e2) (prodCols_ne hkl hk hm h0)
    · exact fun c hc => (eq_of_braid hBB hAA (fun c hc => hB.lt hc) (fun c hc => hA.lt hc)
        (fun c hc => (hcomm c hc).symm) ((pair_rel hkl hk).2 h0) c hc).symm

theorem exists_conj_mem_commutator
    (hM : SmithE22Module) [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {g : G}
    (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG) :
    ∃ y : G, IsConj S.z y ∧ y ∈ S.QG ∧ y ∈ (⁅zpowers (g * S.z * g⁻¹), S.QG⁆ : Subgroup G) ∧
      Commute (g * S.z * g⁻¹) y ∧ y ∈ S.Qa g := by
  obtain ⟨φ, -, h2b, -, h4⟩ := hM G S hw hU
  have hx : IsConj S.z (g * S.z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  have hz'Q : g⁻¹ * S.z * g ∉ S.QG := SMF.conj_z_not_mem_QG S hxQ
  set x := g * S.z * g⁻¹ with hxdef
  have hxx : x * x = 1 := SmithQ.mul_self_eq_one_of_isConj S hx
  have hxi : x⁻¹ = x := SME.inv_eq_of_isConj S hx
  have hx2 : x ^ 2 = 1 := by rw [sq, hxx]
  obtain ⟨k, hk, hA⟩ := h4 x hx hxM hxQ
  change Acts S φ x (applyCols (tvCols k)) at hA
  obtain ⟨e, he, j, hj, hje⟩ := exists_comm_wt hk
  obtain ⟨u, hu, hue⟩ := exists_psi S φ he
  have hdQ : x * u * x⁻¹ * u⁻¹ ∈ S.QG := S.commutator_mem_QG hxM hu
  have hdcode : code (φ (S.cl (x * u * x⁻¹ * u⁻¹))) = wt j := by
    rw [hje, S.cl_mul (S.conj_mem_QG hxM hu) (S.QG.inv_mem hu), S.cl_inv hu, psi_add, hA u hu,
      hue]
  have hdJ : x * u * x⁻¹ * u⁻¹ ∈ (⁅zpowers x, S.QG⁆ : Subgroup G) := SME.commutator_mem S x hu
  set d := x * u * x⁻¹ * u⁻¹ with hd
  obtain ⟨c, hc, hcQ, hcj⟩ := h2b j hj
  have hd0 : S.cl d ≠ 0 := by
    intro h0
    rw [h0, psi_zero] at hdcode
    exact wt_ne_zero hj hdcode.symm
  have hd1 : d ≠ 1 := fun h => hd0 (by rw [h, S.cl_one])
  have hdz : d ≠ S.z := fun h => hd0 (by rw [h, S.cl_z])
  have hdc : IsConj S.z d :=
    SME.isConj_of_cl_eq S hc hcQ hdQ hd1 (psi_inj S φ (hcj.trans hdcode.symm))
  have hdi : d⁻¹ = d := SME.inv_eq_of_isConj S hdc
  have hxd : Commute x d := by
    have h1 : x * d * x⁻¹ = d⁻¹ := by
      calc x * d * x⁻¹ = (x * x) * u * x⁻¹ * u⁻¹ * x⁻¹ := by rw [hd]; group
        _ = u * x * u⁻¹ * x := by rw [hxx, one_mul, hxi]
        _ = u * x * u⁻¹ * x⁻¹ := by rw [hxi]
        _ = d⁻¹ := by rw [hd]; group
    rw [hdi] at h1
    calc x * d = x * d * x⁻¹ * x := by group
      _ = d * x := by rw [h1]
  have hzx : Commute S.z x := (S.z_comm hxM).symm
  have hz : S.z ∈ (⁅zpowers x, S.QG⁆ : Subgroup G) := by
    rw [S.commutator_zpowers_eq_clPre hxM hxQ hx2]
    exact S.z_mem_clPre _
  have hdzc : IsConj S.z (d * S.z) := by
    obtain ⟨q, -, hq⟩ := SME.exists_conj_eq_mul_z S hdQ hd1 hdz
    exact hdc.trans (isConj_iff.mpr ⟨q, hq⟩)
  have hz'M : g⁻¹ * S.z * g ∈ S.M := (SME.mem_M_conj_iff S g S.z).mpr hzx
  have hd'M : g⁻¹ * d * g ∈ S.M := (SME.mem_M_conj_iff S g d).mpr hxd.symm
  by_cases hd'Q : g⁻¹ * d * g ∈ S.QG
  · exact ⟨d, hdc, hdQ, hdJ, hxd, (SME.mem_Qa_iff S g d).mpr hd'Q⟩
  · have hdz' : Commute d S.z := S.z_comm_QG hdQ
    have hconj : g⁻¹ * (d * S.z) * g = g⁻¹ * d * g * (g⁻¹ * S.z * g) := by group
    have key := mul_mem_QG hM S hw hU (SmithGraph.isConj_conj hdc g)
      (SmithGraph.isConj_conj (IsConj.refl S.z) g) hd'M hz'M hd'Q hz'Q
      ((SmithGraph.commute_conj_iff g d S.z).mpr hdz')
      (by rw [← hconj]; exact SmithGraph.isConj_conj hdzc g)
    refine ⟨d * S.z, hdzc, S.QG.mul_mem hdQ S.z_mem_QG, mul_mem hdJ hz,
      hxd.mul_right hzx.symm, ?_⟩
    rw [SME.mem_Qa_iff, hconj]
    exact key

end SMI

theorem smithE33_of_module
    (hM : SmithE22Module) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
      Nonempty (Mbar0 S ≃* timmesfeldPSU 6) →
        ∀ g : G, g * S.z * g⁻¹ ∈ S.M → g * S.z * g⁻¹ ∉ S.QG →
          ∃ v : G, IsConj S.z v ∧ v ∈ S.QG ∧ v ∈ S.Qa g := by
  intro G _ _ _ S hw hU g hxM hxQ
  obtain ⟨y, hy, hyQ, -, -, hyQx⟩ := SMI.exists_conj_mem_commutator hM S hw hU hxM hxQ
  exact ⟨y, hy, hyQ, hyQx⟩

theorem smithE33Conj_of_module
    (hM : SmithE22Module) :
    SmithE33Conj := by
  intro G _ _ _ S hw hU g hxM hxQ _
  exact smithE33_of_module hM G S hw hU g hxM hxQ

theorem smithE34a_of_module
    (hM : SmithE22Module) :
    SmithE34a :=
  smithE34a_of_smithE33Conj (smithE33Conj_of_module hM) (smithE34Q_of hM)

theorem smithE34b_of_module
    (hM : SmithE22Module) :
    SmithE34b :=
  smithE34b_of (smithE34a_of_module hM)

end CFSG.LargeExtraspecial.S14
