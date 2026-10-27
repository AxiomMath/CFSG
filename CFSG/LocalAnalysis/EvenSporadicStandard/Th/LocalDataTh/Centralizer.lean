module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.Orbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.ABasis
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.Assembly

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open scoped Matrix commutatorElement

@[expose] def bilWit : List ℕ := [0, 2, 8, 10, 14, 12, 6, 4]

theorem bilWit_spec : ∀ k : Fin 8, ∀ j : Fin 3,
    CFSG.Certificates.ExtraspecialNF.bil c (codeVec 8 (bilWit.getD k 0))
      (codeVec 8 (uCodes.getD j 0)) = codeVec 3 k j := by
  decide

section Group

theorem exists_bil_eq (φ : Fin 3 → ZMod 2) :
    ∃ e : Vec, ∀ j : Fin 3, CFSG.Certificates.ExtraspecialNF.bil c e (uVec j) = φ j := by
  obtain ⟨k, hk, rfl⟩ := exists_codeVec 3 φ
  have hk' : k < 8 := by simpa using hk
  exact ⟨codeVec 8 (bilWit.getD k 0), fun j => bilWit_spec ⟨k, hk'⟩ j⟩

theorem mem_zpowers_z_iff {u : J} : u ∈ Subgroup.zpowers z ↔ u = 1 ∨ u = z := by
  rw [CFSG.Certificates.ExtraspecialNF.mem_zpowers_iff_exists symplectic_rel]
  constructor
  · rintro ⟨b, rfl⟩
    rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases b with rfl | rfl
    · left
      simp
    · right
      simp [CFSG.Certificates.ExtraspecialNF.val_one_two]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp [CFSG.Certificates.ExtraspecialNF.val_one_two]⟩

theorem zpowers_z_comm {u v : J} (hu : u ∈ Subgroup.zpowers z) (hv : v ∈ Subgroup.zpowers z) :
    u * v = v * u := by
  rcases mem_zpowers_z_iff.1 hu with rfl | rfl <;> rcases mem_zpowers_z_iff.1 hv with rfl | rfl <;>
    simp

theorem conj_eq_of_mem_zpowers_z {m u : J} (hm : m ∈ M) (hu : u ∈ Subgroup.zpowers z) :
    m * u * m⁻¹ = u := by
  rcases mem_zpowers_z_iff.1 hu with rfl | rfl
  · simp
  · have h : z * m = m * z := (commute_z_of_mem_M hm).eq
    rw [← h]
    simp

theorem comm_eq_one_iff {a b : J} : ⁅a, b⁆ = 1 ↔ a * b = b * a := by
  constructor
  · intro h1
    rw [commutatorElement_def] at h1
    calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
      _ = b * a := by rw [h1, one_mul]
  · intro h
    rw [commutatorElement_def, h]
    group

theorem comm_mem_zpowers_of_fix {m : J} (hm : m ∈ M) {v : Vec} (hv : rho m *ᵥ v = v) :
    ⁅m, nf 0 v⁆ ∈ Subgroup.zpowers z := by
  obtain ⟨t, ht⟩ := comm_nf hm 0 v
  rw [ht, Matrix.add_mulVec, Matrix.one_mulVec, hv, vec_add_self, nf_zero_vec]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _

theorem comm_mul_of_mem_zpowers {m m' a : J} (hm : m ∈ M) (h : ⁅m, a⁆ ∈ Subgroup.zpowers z)
    (h' : ⁅m', a⁆ ∈ Subgroup.zpowers z) : ⁅m * m', a⁆ = ⁅m, a⁆ * ⁅m', a⁆ := by
  have e1 : ⁅m * m', a⁆ = m * ⁅m', a⁆ * m⁻¹ * ⁅m, a⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e1, conj_eq_of_mem_zpowers_z hm h']
  exact zpowers_z_comm h' h

@[expose] noncomputable def Kt : Subgroup J where
  carrier := {m | m ∈ M ∧ ∀ j : Fin 3, rho m *ᵥ uVec j = uVec j}
  one_mem' := ⟨M.one_mem, fun j => by rw [rho_one, Matrix.one_mulVec]⟩
  mul_mem' := fun {a b} ha hb => ⟨M.mul_mem ha.1 hb.1, fun j => by
    rw [rho_mul ha.1 hb.1, ← Matrix.mulVec_mulVec, hb.2 j, ha.2 j]⟩
  inv_mem' := fun {a} ha => ⟨M.inv_mem ha.1, fun j => by
    have h : rho a⁻¹ *ᵥ uVec j = rho a⁻¹ *ᵥ (rho a *ᵥ uVec j) := by rw [ha.2 j]
    rw [h, Matrix.mulVec_mulVec, ← rho_mul (M.inv_mem ha.1) ha.1, inv_mul_cancel, rho_one,
      Matrix.one_mulVec]⟩

theorem Q_le_Kt : Q ≤ Kt := fun q hq =>
  ⟨Q_le_M hq, fun j => by rw [(rho_eq_one_iff (Q_le_M hq)).2 hq, Matrix.one_mulVec]⟩

@[expose] noncomputable def theta : ↥Kt →* (Fin 3 → ↥(Subgroup.zpowers z)) where
  toFun m j := ⟨⁅(m : J), nf 0 (uVec j)⁆, comm_mem_zpowers_of_fix m.2.1 (m.2.2 j)⟩
  map_one' := by
    funext j
    apply Subtype.ext
    simp [commutatorElement_def]
  map_mul' m m' := by
    funext j
    apply Subtype.ext
    exact comm_mul_of_mem_zpowers m.2.1 (comm_mem_zpowers_of_fix m.2.1 (m.2.2 j))
      (comm_mem_zpowers_of_fix m'.2.1 (m'.2.2 j))

theorem theta_apply (m : ↥Kt) (j : Fin 3) :
    ((theta m j : ↥(Subgroup.zpowers z)) : J) = ⁅(m : J), nf 0 (uVec j)⁆ := rfl

theorem theta_surjective : Function.Surjective theta := by
  intro f
  have hφ : ∀ j : Fin 3, ∃ b : ZMod 2, ((f j : ↥(Subgroup.zpowers z)) : J) = z ^ b.val := fun j =>
    (CFSG.Certificates.ExtraspecialNF.mem_zpowers_iff_exists symplectic_rel).1 (f j).2 |>.imp
      fun _ h => h.symm
  choose φ hφ using hφ
  obtain ⟨e, he⟩ := exists_bil_eq φ
  refine ⟨⟨nf 0 e, Q_le_Kt (nf_mem_Q 0 e)⟩, ?_⟩
  funext j
  apply Subtype.ext
  rw [theta_apply]
  show ⁅nf 0 e, nf 0 (uVec j)⁆ = _
  rw [hφ j]
  exact (CFSG.Certificates.ExtraspecialNF.commutator_eq_zpow symplectic_rel
    (fun i j => c_symm j i) (by decide) 0 0 e (uVec j)).trans (by rw [he j])

theorem card_pi_zpowers : Nat.card (Fin 3 → ↥(Subgroup.zpowers z)) = 8 := by
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_zpowers,
    CFSG.Certificates.ExtraspecialNF.orderOf_eq_two symplectic_rel z_ne_one]
  norm_num

theorem B_le_Kt (hcent : ∀ g : J, g * z = z * g → g ∈ M) : B ≤ Kt := by
  intro x hx
  have hxM : x ∈ M := hcent x ((mem_B_iff x).1 hx z z_mem_A)
  refine ⟨hxM, fun j => ?_⟩
  have hcomm : x * nf 0 (uVec j) = nf 0 (uVec j) * x :=
    (mem_B_iff x).1 hx _ (nf_zero_uVec_mem j)
  obtain ⟨t, ht⟩ := conj_nf hxM 0 (uVec j)
  have h2 : x * nf 0 (uVec j) * x⁻¹ = nf 0 (uVec j) := by
    rw [hcomm]
    simp
  rw [h2] at ht
  exact (congrArg Prod.snd
    (nf_injective (a₁ := (0, uVec j)) (a₂ := (t, rho x *ᵥ uVec j)) ht)).symm

theorem mem_B_of_comm {m : J} (hm : m ∈ Kt)
    (h : ∀ j : Fin 3, m * nf 0 (uVec j) = nf 0 (uVec j) * m) : m ∈ B := by
  rw [mem_B_iff]
  have hC : ∀ i : Fin 4, aGen i ∈ Subgroup.centralizer ({m} : Set J) := by
    intro i
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    fin_cases i
    · exact (commute_z_of_mem_M hm.1).eq.symm
    · exact h 0
    · exact h 1
    · exact h 2
  intro a ha
  obtain ⟨e, rfl⟩ := exists_cA ha
  exact (Subgroup.mem_centralizer_iff.1 (cA_mem_of _ hC e)) m (Set.mem_singleton m)

theorem ker_theta : theta.ker = B.subgroupOf Kt := by
  ext ⟨m, hm⟩
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    refine mem_B_of_comm hm (fun j => ?_)
    have h1 : ((theta ⟨m, hm⟩ j : ↥(Subgroup.zpowers z)) : J) = 1 := by
      rw [h]
      rfl
    rw [theta_apply] at h1
    exact comm_eq_one_iff.1 h1
  · intro hB
    funext j
    apply Subtype.ext
    show ⁅m, nf 0 (uVec j)⁆ = 1
    exact comm_eq_one_iff.2 ((mem_B_iff m).1 hB _ (nf_zero_uVec_mem j))

end Group

section Count

theorem mem_stabilizer_rootY3_iff (m : ↥M) :
    m ∈ MulAction.stabilizer ↥M rootY3 ↔ ∀ j : Fin 3, rho (m : J) *ᵥ uVec j = uVec j := by
  rw [MulAction.mem_stabilizer_iff]
  have e1 : m • rootY3 = (m • (1 : Fin 256), m • (50 : Fin 256), m • (100 : Fin 256)) := rfl
  rw [e1]
  simp only [rootY3, Prod.mk.injEq]
  rw [smul_eq_iff, smul_eq_iff, smul_eq_iff]
  have hu0 : decV (1 : Fin 256) = uVec 0 := rfl
  have hu1 : decV (50 : Fin 256) = uVec 1 := rfl
  have hu2 : decV (100 : Fin 256) = uVec 2 := rfl
  rw [hu0, hu1, hu2]
  constructor
  · rintro ⟨h1, h2, h3⟩ j
    fin_cases j
    · exact h1
    · exact h2
    · exact h3
  · intro h
    exact ⟨h 0, h 1, h 2⟩

theorem Kt_eq_map : Kt = (MulAction.stabilizer ↥M rootY3).map M.subtype := by
  ext m
  rw [Subgroup.mem_map]
  constructor
  · intro hm
    exact ⟨⟨m, hm.1⟩, (mem_stabilizer_rootY3_iff _).2 hm.2, rfl⟩
  · rintro ⟨m', hm', rfl⟩
    exact ⟨m'.2, (mem_stabilizer_rootY3_iff m').1 hm'⟩

theorem card_Kt : Nat.card Kt = 4096 := by
  rw [Kt_eq_map, Subgroup.card_map_of_injective M.subtype_injective]
  exact card_stabilizer_rootY3

theorem card_B (hcent : ∀ g : J, g * z = z * g → g ∈ M) : Nat.card B = 2 ^ 9 := by
  have h1 : Nat.card ↥theta.ker = Nat.card B := by
    rw [ker_theta]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (B_le_Kt hcent)).toEquiv
  have h2 : Nat.card ↥theta.range = 8 := by
    rw [MonoidHom.range_eq_top.2 theta_surjective, Subgroup.card_top]
    exact card_pi_zpowers
  have h3 := theta.ker.card_mul_index
  rw [Subgroup.index_ker, h1, h2, card_Kt] at h3
  omega

end Count

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
