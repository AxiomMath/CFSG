module

public import Certificates.Certificate272020
public import CFSG.ClassicalInvolution.SmallCases.NobqCriteria
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import Certificates.Data.O8p2NoDatum

public section

namespace CFSG.ClassicalInvolution.Q3.O8

open CFSG.EvenSmallLie.OmegaEight CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
  CFSG.ComponentClassification.J2Cover
  CFSG.ClassicalInvolution.Nobq CFSG.ClassicalInvolution.O8Data

theorem le_ncard_conjClass_of_closureOK {H : Subgroup (Equiv.Perm (Fin 360))}
    {GT GI : Array Table} {gg : ℕ → Equiv.Perm (Fin 360)}
    (hg : ∀ l < GT.size, CFSG.Sporadic.Th.Rep 360 GT[l]! (gg l) ∧
      CFSG.Sporadic.Th.Rep 360 GI[l]! (gg l)⁻¹ ∧ gg l ∈ H)
    {T : Table} {b : Equiv.Perm (Fin 360)} (hT : CFSG.Sporadic.Th.Rep 360 T b) {m : ℕ}
    {c : Array Table × Array ℕ × Array ℕ}
    (h : (conjTreeOK 360 GT GI T c.1 c.2.1 c.2.2 && hkeysDistinct 360 c.1.toList &&
      decide (m ≤ c.1.size)) = true) :
    m ≤ (conjClass H b).ncard := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨htree, hdist⟩, hsize⟩ := h
  have hent := conjTreeOK_spec H hg hT htree
  have hrepL : ∀ U ∈ c.1.toList, ∃ d ∈ H, CFSG.Sporadic.Th.Rep 360 U (d * b * d⁻¹) := by
    intro U hU
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hU
    rw [Array.length_toList] at hk
    obtain ⟨d, hd, hrep⟩ := hent k hk
    refine ⟨d, hd, ?_⟩
    rw [Array.getElem_toList]
    rwa [getElem!_pos c.1 k hk] at hrep
  set E := c.1.toList.map (tablePerm 360)
  have hF : List.Forall₂ (CFSG.Sporadic.Th.Rep 360) c.1.toList E := by
    rw [List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun U hU => ?_
    obtain ⟨d, -, hrep⟩ := hrepL U hU
    rw [tablePerm_eq hrep]
    exact hrep
  have hnodup : E.Nodup := CFSG.Sporadic.SmallOddCore.nodup_of_hkeysDistinct hF hdist
  have hEcls : ∀ y ∈ E, y ∈ conjClass H b := by
    intro y hy
    obtain ⟨U, hU, rfl⟩ := List.mem_map.1 hy
    obtain ⟨d, hd, hrep⟩ := hrepL U hU
    exact ⟨d, hd, tablePerm_eq hrep⟩
  have hlen : E.length = c.1.size := by simp [E]
  have hfin : Finite H := Subtype.finite
  calc m ≤ c.1.size := hsize
    _ = E.toFinset.card := by rw [List.toFinset_card_of_nodup hnodup, hlen]
    _ = (E.toFinset : Set (Equiv.Perm (Fin 360))).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (conjClass H b).ncard :=
      Set.ncard_le_ncard (fun y hy => hEcls y (List.mem_toFinset.1 hy)) (conjClass_finite H b)

theorem word_spec {w : List Int} (hw : lettersOK 17 w = true)
    (hinv : isInvA 360 (omegaW w) (invCand 360 (omegaW w)) = true) :
    permOfArr 360 (omegaW w) ∈ omegaT ∧ Rep 360 (omegaW w) (permOfArr 360 (omegaW w)) ∧
      Rep 360 (invCand 360 (omegaW w)) (permOfArr 360 (omegaW w))⁻¹ :=
  ⟨(omegaW_spec hw).2, (omegaW_spec hw).1, (rep_permOfArr hinv).2⟩

theorem main_rep {i : ℕ} (hi : i < 3) :
    Rep 360 (mainArrs.getD i #[]) (mainPerm i) :=
  (mainPerm_spec (by omega)).1

theorem getElem!_toArray_map {α β : Type*} [Inhabited β] (L : List α) (f : α → β) (d : α) {l : ℕ}
    (hl : l < L.length) : ((L.map f).toArray)[l]! = f (L.getD l d) := by
  rw [getElem!_pos _ l (by simpa using hl), List.getElem_toArray, List.getElem_map,
    List.getD_eq_getElem _ _ hl]

theorem exists_conj_mem_sylowT_of_involution
    {x : Equiv.Perm (Fin 360)} (hx : x ∈ autT) (hx2 : orderOf x = 2) :
    ∃ a ∈ autT, a * x * a⁻¹ ∈ sylowT := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set x' : autT := ⟨x, hx⟩
  have hX : IsPGroup 2 (Subgroup.zpowers x') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx2, pow_one])
  obtain ⟨Q, hQ⟩ := hX.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq autT sylowA Q
  have h1 : x' ∈ (Q : Subgroup autT) := hQ (Subgroup.mem_zpowers x')
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply, coe_sylowA,
    Subgroup.mem_subgroupOf] at h1
  refine ⟨(g⁻¹ : autT), (g⁻¹ : autT).2, ?_⟩
  simpa using h1

theorem exists_conj_main {u : Equiv.Perm (Fin 360)}
    (hu : u ∈ omegaT) (hu2 : orderOf u = 2) :
    ∃ i < 3, ∃ g ∈ autT, u = g * mainPerm i * g⁻¹ := by
  obtain ⟨a, ha, hau⟩ := exists_conj_mem_sylowT_of_involution (omegaT_le_autT hu) hu2
  have hau2 : orderOf (a * u * a⁻¹) = 2 := by
    rw [show a * u * a⁻¹ = MulAut.conj a u from rfl, MulEquiv.orderOf_eq, hu2]
  obtain ⟨j, hj, c, hc, hcj⟩ := exists_rep_of_involution hau hau2
  have hcA : c ∈ autT := sylowT_le_autT hc
  have hrj : repPerm j ∈ omegaT := by
    have e : repPerm j = c⁻¹ * (a * u * a⁻¹) * c := by rw [hcj]; group
    rw [e, show c⁻¹ * (a * u * a⁻¹) * c = (c⁻¹ * a) * u * (c⁻¹ * a)⁻¹ by group]
    exact (conj_mem_omegaT (autT.mul_mem (autT.inv_mem hcA) ha)).1 hu
  have htype : repTypes.getD j 0 < 3 := (repPerm_mem_omegaT_iff hj).1 hrj
  refine ⟨repTypes.getD j 0, htype, a⁻¹ * c * conjPerm j, autT.mul_mem (autT.mul_mem
    (autT.inv_mem ha) hcA) (conjPerm_spec hj).2, ?_⟩
  have h1 := conj_mainPerm hj
  calc u = a⁻¹ * (a * u * a⁻¹) * a := by group
    _ = a⁻¹ * (c * repPerm j * c⁻¹) * a := by rw [hcj]
    _ = a⁻¹ * (c * (conjPerm j * mainPerm (repTypes.getD j 0) * (conjPerm j)⁻¹) * c⁻¹) * a := by
      rw [h1]
    _ = (a⁻¹ * c * conjPerm j) * mainPerm (repTypes.getD j 0) * (a⁻¹ * c * conjPerm j)⁻¹ := by
      group

theorem noUniqueInvNormal_omegaT :
    NoUniqueInvNormal omegaT := by
  intro t N _ hN
  obtain ⟨s, hsN, hst, hs4⟩ := hN.exists_sq_eq
  obtain ⟨g, hg, h1, h2, h3, h4⟩ := Certificates.certificate272020.1 (s : Equiv.Perm (Fin 360))
    s.2 (by rw [Subgroup.orderOf_coe]; exact hs4)
  set g' : omegaT := ⟨g, hg⟩
  have hgc : g' ∈ Subgroup.centralizer ({t} : Set omegaT) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hst]
    exact Subtype.ext h1
  have hy : s * (g' * s * g'⁻¹) ∈ N := N.mul_mem hsN (hN.conj_mem g' hgc s hsN)
  have ey : ((s * (g' * s * g'⁻¹) : omegaT) : Equiv.Perm (Fin 360)) =
      (s : Equiv.Perm (Fin 360)) * (g * s * g⁻¹) := rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy2 : orderOf (s * (g' * s * g'⁻¹)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      rw [pow_two, Subgroup.coe_mul, ey]
      exact h2
    · intro e
      exact h3 (by rw [← ey, e]; rfl)
  have e := hN.eq_of_orderOf_eq_two _ hy hy2
  apply h4
  rw [← ey, e, ← hst]
  rfl

theorem noUniqueInvNormal_omega8plus2
    {Y : Type} [Group Y]
    (hY : CFSG.Blueprint.LieModel Y .POmegaPlus 4 2 1) : NoUniqueInvNormal Y := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hY
  exact NoUniqueInvNormal.of_mulEquiv e noUniqueInvNormal_omegaT

end CFSG.ClassicalInvolution.Q3.O8
