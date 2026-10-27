module

public import CFSG.Quasithin.Recognition.CertU33Simple
public import Certificates.Certificate17627
public import Certificates.Certificate17628
public import Certificates.Certificate17629
import CFSG.ClassicalInvolution.Q3.Q3TLTO8
import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.D42Tri

open CFSG.EvenSmallLie.OmegaEight CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.SmallOddCore
  CFSG.ComponentClassification.J2Cover CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42
  CFSG.Quasithin CFSG.CosetTable

theorem n360_lt : (360 : ℕ) < 2 ^ 32 := by norm_num

theorem getElem!_range_map {α : Type*} [Inhabited α] (f : ℕ → α) {n m : ℕ} (hm : m < n) :
    ((List.range n).map f).toArray[m]! = f m := by
  rw [getElem!_pos _ m (by simpa using hm)]
  simp

theorem genArrs_eight : genArrs[8]! = rhoArr := by
  have hlen : rootPairs.length = 8 := rfl
  rw [genArrs, getElem!_pos _ 8 (by simp [hlen]), Array.getElem_append_right (by simp [hlen])]
  simp [hlen]

theorem rep_rhoTbl : Rep 360 (rhoTbl ()) (gen 8) := by
  have h := rep_gen (i := 8) (by norm_num)
  rw [genArrs_eight] at h
  exact rep_arrTable n360_lt h

theorem omG_spec : ∀ l < (omGT ()).size,
    Rep 360 (omGT ())[l]! (gen l) ∧ Rep 360 (omGI ())[l]! (gen l)⁻¹ ∧ gen l ∈ omegaT := by
  intro l hl
  have hl8 : l < 8 := by simpa [omGT] using hl
  refine ⟨?_, ?_, gen_mem_omegaT hl8⟩
  · rw [omGT, getElem!_range_map _ hl8]
    exact rep_arrTable n360_lt (rep_gen (by omega))
  · rw [omGI, getElem!_range_map _ hl8]
    exact rep_arrTable n360_lt (rep_gen_inv (by omega))

theorem exists_conj_rho_or_t2
    {a : Equiv.Perm (Fin 360)} (ha : a ∈ autT) (h3 : a ^ 3 = 1) (hout : a ∉ omegaT) :
    ∃ y, (y = a ∨ y = a⁻¹) ∧ ∃ g ∈ autT, g * y * g⁻¹ = gen 8 ∨ g * y * g⁻¹ = t2Perm :=
  Certificates.certificate17627.1 a ha h3 hout

theorem card_centralizer_rho_le :
    Nat.card (CFSG.Sporadic.Schreier.centralizerIn omegaT (gen 8)) ≤ 12096 := by
  have hle : 14400 ≤ (CFSG.Sporadic.Schreier.conjClass omegaT (gen 8)).ncard :=
    CFSG.ClassicalInvolution.Q3.O8.le_ncard_conjClass_of_closureOK
      (c := conjClosureH 360 (omGT ()) (omGI ()) (rhoTbl ()) 14400) omG_spec rep_rhoTbl
      Certificates.certificate17628
  have hos := CFSG.Sporadic.Schreier.ncard_conjClass_mul_card omegaT (gen 8)
  rw [card_omegaT] at hos
  have h2 : 14400 * Nat.card (CFSG.Sporadic.Schreier.centralizerIn omegaT (gen 8)) ≤
      174182400 := by
    rw [← hos]
    exact Nat.mul_le_mul_right _ hle
  omega

theorem l0Sub_le :
    l0Sub ≤ CFSG.Sporadic.Schreier.centralizerIn omegaT (gen 8) := by
  rw [l0Sub, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact CFSG.Sporadic.Schreier.mem_centralizerIn.2 (Certificates.certificate17627.2.1 i)

theorem nonempty_l0_mulEquiv :
    Nonempty (↥l0Sub ≃* PG 5 u33PresRels) := by
  let φ : PG 5 u33PresRels →* Equiv.Perm (Fin 360) := PresentedGroup.toGroup (f := l0Gen) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact Certificates.certificate17627.2.2.1 w hw)
  have hφ : ∀ i, φ (PresentedGroup.of i) = l0Gen i := fun i => PresentedGroup.toGroup.of _
  have hrange : φ.range = l0Sub := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
      {r : FreeGroup (Fin 5) | r ∈ u33PresRels.map FreeGroup.mk}, MonoidHom.map_closure,
      ← Set.range_comp]
    exact congrArg (fun f => Subgroup.closure (Set.range f)) (funext hφ)
  have hinj : Function.Injective φ := by
    have := isSimpleGroup_u33Pres
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff φ).1 h
    · exfalso
      have h0 : (PresentedGroup.of (0 : Fin 5) : PG 5 u33PresRels) ∈ φ.ker := by
        rw [h]
        exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hφ] at h0
      exact Certificates.certificate17627.2.2.2.1 h0
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

theorem isSimpleGroup_l0Sub :
    IsSimpleGroup ↥l0Sub := by
  obtain ⟨e⟩ := nonempty_l0_mulEquiv
  have := isSimpleGroup_u33Pres
  exact e.isSimpleGroup

theorem card_l0Sub :
    Nat.card ↥l0Sub = 6048 := by
  obtain ⟨e⟩ := nonempty_l0_mulEquiv
  rw [Nat.card_congr e.toEquiv]
  exact card_u33Pres

theorem relIndex_l0Sub_le :
    l0Sub.relIndex (CFSG.Sporadic.Schreier.centralizerIn omegaT (gen 8)) ≤ 2 := by
  have h1 := Subgroup.relIndex_mul_card l0Sub
    (CFSG.Sporadic.Schreier.centralizerIn omegaT (gen 8))
  rw [inf_eq_left.2 l0Sub_le, card_l0Sub] at h1
  have h2 := card_centralizer_rho_le
  omega

theorem k2_spec :
    genOf 360 (k2Tbls ()) ≤ CFSG.Sporadic.Schreier.centralizerIn omegaT t2Perm ∧
      Nat.card (genOf 360 (k2Tbls ())) = 216 :=
  Certificates.certificate17627.2.2.2.2

theorem card_centralizer_t2_le :
    Nat.card (CFSG.Sporadic.Schreier.centralizerIn omegaT t2Perm) ≤ 431 :=
  Certificates.certificate17629

theorem card_centralizer_t2 :
    Nat.card (CFSG.Sporadic.Schreier.centralizerIn omegaT t2Perm) = 216 := by
  obtain ⟨hK, hKcard⟩ := k2_spec
  have hd := Subgroup.card_dvd_of_le hK
  rw [hKcard] at hd
  obtain ⟨t, ht⟩ := hd
  have hle := card_centralizer_t2_le
  have hpos : 0 < Nat.card (CFSG.Sporadic.Schreier.centralizerIn omegaT t2Perm) := Nat.card_pos
  rw [ht] at hle hpos ⊢
  omega

theorem isSolvable_centralizer_t2 :
    Group.IsSolvable ↥(CFSG.Sporadic.Schreier.centralizerIn omegaT t2Perm) := by
  let _ : Fintype ↥(CFSG.Sporadic.Schreier.centralizerIn omegaT t2Perm) := Fintype.ofFinite _
  have h := card_centralizer_t2
  rw [Nat.card_eq_fintype_card] at h
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
    Nat.prime_two Nat.prime_three (by norm_num) (h.trans (by norm_num))

end CFSG.HardMathSupport.Dickson.Bal207.D42Tri
