module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128OddY

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private lemma sec128_conj_inverts {Y : Type} [Group Y] {tau : Y}
    (hinv : ∀ o ∈ oddCore Y, tau * o * tau⁻¹ = o⁻¹)
    {y : Y} (hy : y ∈ conjClassIn (⊤ : Subgroup Y) tau) :
    ∀ o ∈ oddCore Y, y * o * y⁻¹ = o⁻¹ := by
  rintro o ho
  obtain ⟨h, -, rfl⟩ := hy
  have hho : h⁻¹ * o * h ∈ oddCore Y := by
    simpa using (inferInstance : (oddCore Y).Normal).conj_mem o ho h⁻¹
  have hstep := hinv (h⁻¹ * o * h) hho
  calc
    (h * tau * h⁻¹) * o * (h * tau * h⁻¹)⁻¹
        = h * (tau * (h⁻¹ * o * h) * tau⁻¹) * h⁻¹ := by group
    _ = h * (h⁻¹ * o * h)⁻¹ * h⁻¹ := by rw [hstep]
    _ = o⁻¹ := by group

private lemma sec128_cent_of_sq {Y : Type} [Group Y] (tau : Y) (h2 : orderOf tau = 2)
    (hinv : ∀ o ∈ oddCore Y, tau * o * tau⁻¹ = o⁻¹)
    (hfus : ∀ y : Y, (y ∈ conjClassIn (⊤ : Subgroup Y) tau ∧
      y ∈ centralizer ({tau} : Set Y)) ↔
      (∃ x ∈ oTwoRes (centralizer ({tau} : Set Y)), y = tau * x ∧ y * y = 1))
    {x : Y} (hxT : x ∈ oTwoRes (centralizer ({tau} : Set Y))) (hx2 : x * x = 1) :
    x ∈ centralizer (oddCore Y : Set Y) := by
  have htau : tau * tau = 1 := by
    rw [← pow_two, ← h2]
    exact pow_orderOf_eq_one tau
  rw [Subgroup.mem_centralizer_iff]
  intro o ho
  have hTK : oTwoRes (centralizer ({tau} : Set Y)) ≤ centralizer ({tau} : Set Y) := by
    rw [oTwoRes, Subgroup.closure_le]
    exact fun _ hy => hy.1
  have hxK : x ∈ centralizer ({tau} : Set Y) := hTK hxT
  have hcomm : tau * x = x * tau :=
    (Subgroup.mem_centralizer_iff.mp hxK) tau (by simp)
  have hyy : (tau * x) * (tau * x) = 1 := by
    calc
      (tau * x) * (tau * x) = tau * (x * tau) * x := by group
      _ = tau * (tau * x) * x := by rw [hcomm]
      _ = (tau * tau) * (x * x) := by group
      _ = 1 := by rw [htau, hx2, mul_one]
  have hconj : tau * x ∈ conjClassIn (⊤ : Subgroup Y) tau :=
    ((hfus (tau * x)).mpr ⟨x, hxT, rfl, hyy⟩).1
  have hyinv : (tau * x) * o * (tau * x)⁻¹ = o⁻¹ :=
    sec128_conj_inverts hinv hconj o ho
  have hxeq : x = tau * (tau * x) := by rw [← mul_assoc, htau, one_mul]
  have hxcomm : x * o = o * x := by
    have h1 : x * o * x⁻¹ = tau * ((tau * x) * o * (tau * x)⁻¹) * tau⁻¹ := by
      conv_lhs => rw [hxeq]
      group
    have hxinv : x * o * x⁻¹ = o := by
      rw [h1, hyinv]
      calc
        tau * o⁻¹ * tau⁻¹ = (tau * o * tau⁻¹)⁻¹ := by group
        _ = o := by rw [hinv o ho, inv_inv]
    calc
      x * o = (x * o * x⁻¹) * x := by group
      _ = o * x := by rw [hxinv]
  exact hxcomm.symm

private lemma sec128_oTwoRes_centralizes {Y : Type} [Group Y] [Finite Y] (tau : Y)
    (h2 : orderOf tau = 2)
    (hK : Nonempty (↥(centralizer ({tau} : Set Y)) ≃*
      (Multiplicative (ZMod 2) × ↥(alternatingGroup (Fin 5)))))
    (hfus : ∀ y : Y, (y ∈ conjClassIn (⊤ : Subgroup Y) tau ∧
      y ∈ centralizer ({tau} : Set Y)) ↔
      (∃ x ∈ oTwoRes (centralizer ({tau} : Set Y)), y = tau * x ∧ y * y = 1)) :
    ∀ o ∈ oddCore Y, ∀ x ∈ oTwoRes (centralizer ({tau} : Set Y)), x * o = o * x := by
  let M := Multiplicative (ZMod 2) × ↥(alternatingGroup (Fin 5))
  let K : Subgroup Y := centralizer ({tau} : Set Y)
  have hK' : Nonempty (↥K ≃* M) := hK
  obtain ⟨e⟩ := hK'
  let T : Subgroup Y := oTwoRes K
  let O : Subgroup Y := oddCore Y
  let S : Set M := {m : M | Odd (orderOf m)}
  let Cl : Subgroup M := Subgroup.closure S
  let P' : Subgroup ↥K := (Subgroup.centralizer (O : Set Y)).subgroupOf K
  let PM : Subgroup M := P'.map e.toMonoidHom
  change ∀ o ∈ O, ∀ x ∈ T, x * o = o * x
  have hinv : ∀ o ∈ O, tau * o * tau⁻¹ = o⁻¹ :=
    fun o ho => sec128_tau_inverts_oddCore tau h2 ⟨e⟩ o ho
  have hcent_sq : ∀ x : Y, x ∈ T → x * x = 1 → x ∈ Subgroup.centralizer (O : Set Y) :=
    fun x hx hx2 => sec128_cent_of_sq tau h2 hinv hfus hx hx2
  have hφmem : ∀ m ∈ Cl, ((e.symm m : ↥K) : Y) ∈ T := by
    let φ : M →* Y := K.subtype.comp e.symm.toMonoidHom
    have hφS : φ '' S ⊆ T := by
      rintro _ ⟨m', hm', rfl⟩
      refine Subgroup.subset_closure ⟨(e.symm m').2, ?_⟩
      change Odd (orderOf (((e.symm m' : ↥K) : Y)))
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact hm'
    have hclosure : Subgroup.closure (φ '' S) ≤ T := (Subgroup.closure_le T).mpr hφS
    intro m hm
    have hmem : φ m ∈ (Subgroup.closure S).map φ := Subgroup.mem_map.mpr ⟨m, hm, rfl⟩
    rw [MonoidHom.map_closure] at hmem
    exact hclosure hmem
  have hPM : ∀ m ∈ Cl, m * m = 1 → m ∈ PM := by
    intro m hm hmm
    have hmT : ((e.symm m : ↥K) : Y) ∈ T := hφmem m hm
    have hsq : ((e.symm m : ↥K) : Y) * ((e.symm m : ↥K) : Y) = 1 := by
      have hmul : e.symm m * e.symm m = 1 := by
        have h := map_mul e.symm m m
        rw [hmm, map_one] at h
        exact h.symm
      simpa using congrArg Subtype.val hmul
    have hcent : ((e.symm m : ↥K) : Y) ∈ Subgroup.centralizer (O : Set Y) :=
      hcent_sq ((e.symm m : ↥K) : Y) hmT hsq
    have hkP' : e.symm m ∈ P' := by
      change ((e.symm m : ↥K) : Y) ∈ Subgroup.centralizer (O : Set Y)
      exact hcent
    exact Subgroup.mem_map.mpr ⟨e.symm m, hkP', by simp⟩
  have hC_normal : (Subgroup.centralizer (O : Set Y)).Normal := inferInstance
  have hP'_normal : P'.Normal := hC_normal.subgroupOf K
  haveI hPM_normal : PM.Normal := hP'_normal.map e.toMonoidHom e.surjective
  have hP_le : ∀ m ∈ Cl, m ∈ PM := sec128_model_oTwo_le PM hPM
  have hT_le : T ≤ Subgroup.centralizer (O : Set Y) := by
    change oTwoRes K ≤ Subgroup.centralizer (O : Set Y)
    rw [oTwoRes, Subgroup.closure_le]
    intro x hx
    obtain ⟨hxK, hxodd⟩ := hx
    set m : M := e ⟨x, hxK⟩ with hm
    have hmS : m ∈ S := by
      change Odd (orderOf m)
      rw [hm, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact hxodd
    have hmCl : m ∈ Cl := Subgroup.subset_closure hmS
    have hmmem : m ∈ PM := hP_le m hmCl
    rcases Subgroup.mem_map.mp hmmem with ⟨k', hk', hk'e⟩
    have hk'eq : k' = ⟨x, hxK⟩ := e.injective (hk'e.trans hm)
    have hxcent : x ∈ Subgroup.centralizer (O : Set Y) := by
      have hk'' := hk'
      rw [hk'eq] at hk''
      change ((⟨x, hxK⟩ : ↥K) : Y) ∈ Subgroup.centralizer (O : Set Y) at hk''
      simpa using hk''
    exact hxcent
  intro o ho x hxT
  exact ((Subgroup.mem_centralizer_iff.mp (hT_le hxT)) o ho).symm

theorem sec128_oddCore_cent {Y : Type} [Group Y] [Finite Y] (tau : Y) (h2 : orderOf tau = 2)
    (hK : Nonempty (↥(centralizer ({tau} : Set Y)) ≃*
      (Multiplicative (ZMod 2) × ↥(alternatingGroup (Fin 5)))))
    (hfus : ∀ y : Y, (y ∈ conjClassIn ⊤ tau ∧ y ∈ centralizer ({tau} : Set Y)) ↔
      (∃ x ∈ oTwoRes (centralizer ({tau} : Set Y)), y = tau * x ∧ y * y = 1)) :
    (∀ o ∈ oddCore Y, tau * o * tau⁻¹ = o⁻¹) ∧
      ∀ o ∈ oddCore Y, ∀ x ∈ oTwoRes (centralizer ({tau} : Set Y)), x * o = o * x :=
  ⟨sec128_tau_inverts_oddCore tau h2 hK,
    sec128_oTwoRes_centralizes tau h2 hK hfus⟩

end CFSG.OddStandard.SmallF3.Omega
