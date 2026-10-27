module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6S
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwinFactsQ8Spec
public import Certificates.Certificate517501
public import CFSG.Certificates.Kernel.HeModelKSound
public import CFSG.Certificates.Kernel.HexaKSound
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

open CFSG.ClassicalInvolution.Generic CFSG.Certificates CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.EvenSmallLie.OmegaEight Certificates.AE6Model Certificates.S7Twin
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Twin CFSG.Monster.B.Co2.Native

section Enum

variable {n : ℕ}

theorem exists_allTables (hn : n < 2 ^ 32) {Q : RawSchreierDatum n} (hQ : ValidSchreier Q)
    {x : Equiv.Perm (Fin n)} (hx : x ∈ Q.originalSubgroup) : ∃ X ∈ allTables Q, Rep n X x := by
  refine exists_of_forall₂_right (forall₂_allTables hn Q) ?_
  rw [List.mem_reverse]
  exact (mem_enumeration_iff Q hQ x).mpr hx

theorem mem_of_memT_allTables (hn : n < 2 ^ 32) {Q : RawSchreierDatum n} (hQ : ValidSchreier Q)
    {X : Table} {x : Equiv.Perm (Fin n)} (hX : Rep n X x) (h : memT n (allTables Q) X = true) :
    x ∈ Q.originalSubgroup := by
  rw [memT_iff (forall₂_allTables hn Q) hX, List.mem_reverse] at h
  exact (mem_enumeration_iff Q hQ x).mp h

end Enum

theorem degree_lt : (360 : ℕ) < 2 ^ 32 := by norm_num

theorem rep_permOfInv {n : ℕ} {t r : Array ℕ} (h : invPairB n t r = true) :
    CFSG.Monster.B.Co2.Rep n t (permOfInv n t r) := by
  intro x
  unfold permOfInv
  rw [dif_pos h]
  rfl

section Gens

theorem curtisPerms_getD {i : ℕ} (hi : i < 8) : (curtisPerms ()).getD i 1 = gen i := by
  have h : ((List.range 8).all fun i =>
      invPairB 360 (curtisArr i) (invCand 360 (curtisArr i))) = true :=
    Certificates.certificate517501.1
  simp only [List.all_eq_true, List.mem_range] at h
  have h1 : CFSG.Monster.B.Co2.Rep 360 (curtisArr i) (gen i) := by
    unfold curtisArr
    exact rep_gen (by omega)
  have h2 :
      (curtisPerms ()).getD i 1 = permOfInv 360 (curtisArr i) (invCand 360 (curtisArr i)) := by
    rw [curtisPerms, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    rfl
  rw [h2]
  exact CFSG.Monster.B.Co2.Rep.unique (rep_permOfInv (h i hi)) h1

theorem curtisPerms_mem : ∀ g ∈ curtisPerms (), g ∈ omegaT := by
  intro g hg
  simp only [curtisPerms, List.mem_map, List.mem_range] at hg
  obtain ⟨i, hi, rfl⟩ := hg
  have h := curtisPerms_getD hi
  simp only [curtisPerms, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some] at h
  rw [h]
  exact gen_mem_omegaT hi

theorem evalCodes_mem_omegaT (w : List ℤ) : evalCodes (curtisPerms ()) w ∈ omegaT :=
  evalCodes_mem _ curtisPerms_mem w

theorem coe_ae6Word (w : List (Fin 8)) :
    ((ae6Word w : AE6Om) : Equiv.Perm (Fin 360)) = aeWord (curtisPerms ()) (w.map Fin.val) := by
  unfold ae6Word aeWord
  rw [← Subgroup.coe_subtype, map_list_prod, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, Subgroup.coe_subtype]
  rw [curtisPerms_getD i.2]
  rfl

theorem aeWord_mem_omegaT (w : List ℕ) : aeWord (curtisPerms ()) w ∈ omegaT := by
  unfold aeWord
  refine Subgroup.list_prod_mem omegaT fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg
  rw [List.getD_eq_getElem?_getD]
  cases h : (curtisPerms ())[i]? with
  | none => exact omegaT.one_mem
  | some g => exact curtisPerms_mem g (List.mem_of_getElem? h)

theorem coe_ae6ModelZ : ((ae6ModelZ : AE6Om) : Equiv.Perm (Fin 360)) = z0 () := by
  rw [ae6ModelZ, coe_ae6Word]
  rfl

theorem chains_parts : (plQ ()).check = true ∧ (plQ ()).orderCertificate = 512 ∧
    (wQ ()).check = true ∧ (wQ ()).orderCertificate = 64 := by
  have h : ((plQ ()).check && (plQ ()).orderCertificate == 512 && (wQ ()).check &&
      (wQ ()).orderCertificate == 64) = true := Certificates.certificate517501.2.2
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem plQ_valid : ValidSchreier (plQ ()) := chains_parts.1

theorem wQ_valid : ValidSchreier (wQ ()) := chains_parts.2.2.1

theorem cPerms_mem : ∀ c ∈ cPerms (), c ∈ omegaT := by
  intro c hc
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hc
  exact evalCodes_mem_omegaT w

theorem cPerms_comm : ∀ c ∈ cPerms (), c * z0 () = z0 () * c := by
  have h : ((cPerms ()).all fun c => commT 360 (toTable c) (toTable (z0 ()))) = true :=
    Certificates.certificate517501.2.1
  rw [List.all_eq_true] at h
  intro c hc
  exact (commT_iff_commute (rep_toTable degree_lt c) (rep_toTable degree_lt _)).mp (h c hc)

theorem k0Gens_mem : ∀ x ∈ k0Gens (), ∃ x' ∈ ae6ModelK, (x' : Equiv.Perm (Fin 360)) = x := by
  intro x hx
  simp only [k0Gens, kWords, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl
  · refine ⟨ae6Word [2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6],
      Subgroup.subset_closure (Set.mem_insert _ _), ?_⟩
    rw [coe_ae6Word]
    rfl
  · refine ⟨ae6Word [0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6],
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)), ?_⟩
    rw [coe_ae6Word]
    rfl

theorem le_ae6ModelP : ∀ y : AE6Om, (y : Equiv.Perm (Fin 360)) ∈ (plQ ()).originalSubgroup →
    y ∈ ae6ModelP := by
  have hle : (plQ ()).originalSubgroup ≤ ae6ModelP.map omegaT.subtype := by
    rw [plQ, certificate_originalSubgroup, Subgroup.closure_le]
    intro g hg
    have hg' : g ∈ (cPerms ()).flatMap fun c => (k0Gens ()).map fun x => c * x * c⁻¹ := hg
    obtain ⟨c, hc, hgc⟩ := List.mem_flatMap.mp hg'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hgc
    obtain ⟨x', hx', hxx⟩ := k0Gens_mem x hx
    set c' : AE6Om := ⟨c, cPerms_mem c hc⟩
    have hcz : c' ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, coe_ae6ModelZ, c']
      exact cPerms_comm c hc
    have htw : conjSub c' ae6ModelK ∈ ae6ModelTwins := ⟨c', hcz, rfl⟩
    have hmem : c' * x' * c'⁻¹ ∈ ae6ModelP :=
      le_sSup htw (conj_mem_conjSub hx')
    refine ⟨c' * x' * c'⁻¹, hmem, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hxx, c']
  intro y hy
  obtain ⟨p, hp, hpy⟩ := hle hy
  rwa [show p = y from Subtype.ext hpy] at hp

theorem mem_wQ : ∀ y ∈ ae6ModelW, (y : Equiv.Perm (Fin 360)) ∈ (wQ ()).originalSubgroup := by
  have hmap : ae6ModelW.map omegaT.subtype = (wQ ()).originalSubgroup := by
    rw [wQ, certificate_originalSubgroup, ae6ModelW, MonoidHom.map_closure]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      w0Gens, wWords, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> rw [coe_ae6Word] <;> simp
    · rintro (rfl | rfl | rfl | rfl | rfl)
      · exact ⟨_, Or.inl rfl, by rw [coe_ae6Word]; rfl⟩
      · exact ⟨_, Or.inr (Or.inl rfl), by rw [coe_ae6Word]; rfl⟩
      · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), by rw [coe_ae6Word]; rfl⟩
      · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), by rw [coe_ae6Word]; rfl⟩
      · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr rfl))), by rw [coe_ae6Word]; rfl⟩
  intro y hy
  rw [← hmap]
  exact ⟨y, hy, rfl⟩

end Gens

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
