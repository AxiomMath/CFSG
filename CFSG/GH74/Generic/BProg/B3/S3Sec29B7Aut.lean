module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFourgroupInner
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful
public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Sec29B7Aut

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.AutL2Facts
  CFSG.ComponentClassification CFSG.GH74.GLS CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

@[expose] def fixSub {L : Type*} [Group L] (σ : MulAut L) : Subgroup L where
  carrier := {l | σ l = l}
  one_mem' := map_one σ
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_inv, ha]

theorem mem_fixSub {L : Type*} [Group L] {σ : MulAut L} {l : L} : l ∈ fixSub σ ↔ σ l = l :=
  Iff.rfl

theorem quot_center_equiv_psl {A : Type} [Group A] {r : ℕ} (hA : HasSL2Model A (fun q => q = r)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = r ∧
      Nonempty (A ⧸ Subgroup.center A ≃* PSL2 F) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hA
  refine ⟨F, inferInstance, inferInstance, hF, ⟨?_⟩⟩
  let e' : SL(2, F) ≃* A := (specialLinearGroupEquivStatedSL 2 F).trans e.symm
  exact (QuotientGroup.congr (Subgroup.center SL(2, F)) (Subgroup.center A) e'
    (Subgroup.map_center_eq e')).symm

theorem fourgroup_inner_of_psl2 {S : Type} [Group S] {F : Type} [Field F] [Finite F]
    (hodd : IsOddPrimePower (Nat.card F)) (e : S ≃* PSL2 F) (W : Subgroup (MulAut S))
    (hW2 : ∀ w ∈ W, w * w = 1) (hW4 : Nat.card W = 4) :
    ∃ w ∈ W, w ≠ 1 ∧ w ∈ (MulAut.conj : S →* MulAut S).range := by
  set Φ := autEquiv e
  obtain ⟨_, ⟨w, hwW, rfl⟩, hw1, hwL⟩ := fourgroup_meets_psl hodd (W.map Φ.toMonoidHom)
    (by
      rintro _ ⟨w, hw, rfl⟩
      change Φ w * Φ w = 1
      rw [← map_mul, hW2 w hw, map_one])
    (by rw [Subgroup.card_map_of_injective Φ.injective, hW4])
  refine ⟨w, hwW, fun h => hw1 (by rw [h]; exact map_one _), ?_⟩
  rw [← map_autEquiv_innAut e] at hwL
  obtain ⟨β, hβ, hβw⟩ := hwL
  rwa [← Φ.injective hβw]

theorem isSolvable_centralizer_psl2 {S : Type} [Group S] {F : Type} [Field F] [Finite F]
    (hodd : IsOddPrimePower (Nat.card F)) (e : S ≃* PSL2 F) {s : S} (hs : orderOf s = 2) :
    Group.IsSolvable ↥(centralizer ({s} : Set S)) := by
  obtain ⟨p, f, hp, hpodd, hf, hF⟩ := hodd
  apply isSolvable_centralizer_of_equiv e s
  have : Fact p.Prime := ⟨hp⟩
  have hes : orderOf (e s) = 2 := by rwa [MulEquiv.orderOf_eq]
  obtain ⟨h1, h3⟩ := CFSG.Walter.psl2_centralizer_involution F hF hpodd hf hes
  have hq3 : 3 ≤ p ^ f := by
    have h2 := hp.two_le
    have h3' : p ≤ p ^ f := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf
    rcases hpodd with ⟨m, hm⟩
    omega
  have hqmod : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
    have := Nat.odd_iff.mp (hpodd.pow (n := f))
    omega
  rcases hqmod with hq | hq
  · obtain ⟨-, ⟨φ⟩⟩ := h1 hq
    have : NeZero ((p ^ f - 1) / 2) := ⟨by omega⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup ((p ^ f - 1) / 2)
    exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
  · obtain ⟨-, ⟨φ⟩⟩ := h3 hq
    have : NeZero ((p ^ f + 1) / 2) := ⟨by omega⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup ((p ^ f + 1) / 2)
    exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective

theorem exists_solvable_fix {M : Type} [Group M] [Finite M] [Group.IsPerfect M]
    {F : Type} [Field F] [Finite F] (hodd : IsOddPrimePower (Nat.card F))
    (e : (M ⧸ center M) ≃* PSL2 F) (D : Subgroup (MulAut M))
    (hD2 : ∀ d ∈ D, d * d = 1) (hD4 : Nat.card D = 4) :
    ∃ d ∈ D, d ≠ 1 ∧ Group.IsSolvable ↥(fixSub d) := by
  classical
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : MulAut M →* MulAut (M ⧸ center M),
      Φ = PerfectAutomorphisms.centerQuotientHom M := ⟨_, rfl⟩
  have hΦinj : Function.Injective Φ := by
    rw [hΦ]
    exact CentralCover.perfect_central_quotient_automorphism_faithful M
  have hΦapp : ∀ (σ : MulAut M) (g : M),
      Φ σ (QuotientGroup.mk g : M ⧸ center M) = QuotientGroup.mk (σ g) := by
    intro σ g
    rw [hΦ]
    exact CentralCover.centerQuotientHom_apply_mk M σ g
  obtain ⟨_, ⟨d, hdD, rfl⟩, hd1, s, hsd⟩ := fourgroup_inner_of_psl2 hodd e (D.map Φ)
    (by
      rintro _ ⟨w, hw, rfl⟩
      rw [← map_mul, hD2 w hw, map_one])
    (by rw [Subgroup.card_map_of_injective hΦinj, hD4])
  have hd1' : d ≠ 1 := fun h => hd1 (by rw [h, map_one])
  refine ⟨d, hdD, hd1', ?_⟩
  have hsd' : ∀ g : M ⧸ center M, s * g * s⁻¹ = Φ d g := fun g => by
    rw [← hsd]
    rfl
  have hs1 : s ≠ 1 := by
    intro h
    apply hd1
    rw [← hsd, h, map_one]
  have hss : s * s = 1 := by
    have hsq : (s * s) ∈ center (M ⧸ center M) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 : Φ d (Φ d g) = g := by
        have h3 := congrArg (fun w : MulAut M => (Φ w) g) (hD2 d hdD)
        simpa [map_mul] using h3
      have h6 : s * (s * g * s⁻¹) * s⁻¹ = g := by
        rw [hsd' g, hsd' (Φ d g), h2]
      calc g * (s * s) = (s * (s * g * s⁻¹) * s⁻¹) * (s * s) := by rw [h6]
        _ = (s * s) * g := by group
    rwa [Group.IsPerfect.center_quotient_center_eq_bot M, Subgroup.mem_bot] at hsq
  have hso : orderOf s = 2 := orderOf_eq_prime (by rwa [pow_two]) hs1
  have hCS : Group.IsSolvable ↥(centralizer ({s} : Set (M ⧸ center M))) :=
    isSolvable_centralizer_psl2 hodd e hso
  have hmem : ∀ l : ↥(fixSub d), (QuotientGroup.mk (l : M) : M ⧸ center M) ∈
      centralizer ({s} : Set (M ⧸ center M)) := by
    intro l
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hsd' (QuotientGroup.mk (l : M))
    have h2 : Φ d (QuotientGroup.mk (l : M)) = QuotientGroup.mk (l : M) := by
      rw [hΦapp, mem_fixSub.1 l.2]
    rw [h2] at h1
    refine Eq.symm ?_
    calc s * QuotientGroup.mk (l : M) = (s * QuotientGroup.mk (l : M) * s⁻¹) * s := by group
      _ = QuotientGroup.mk (l : M) * s := by rw [h1]
  let θ : ↥(fixSub d) →* ↥(centralizer ({s} : Set (M ⧸ center M))) :=
    ((QuotientGroup.mk' (center M)).comp (fixSub d).subtype).codRestrict _ hmem
  have hker : Group.IsSolvable ↥θ.ker := by
    refine Group.isSolvable_of_comm (fun a b => ?_)
    have ha : (a : ↥(fixSub d)) ∈ θ.ker := a.2
    have ha' : ((a : ↥(fixSub d)) : M) ∈ center M := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 ha)
      exact (QuotientGroup.eq_one_iff _).1 this
    exact Subtype.ext (Subtype.ext ((Subgroup.mem_center_iff.1 ha' (b : ↥(fixSub d))).symm))
  exact Group.isSolvable_of_ker_le_range θ.ker.subtype θ (by simp)

theorem exists_solvable_fix_sl2 {M : Type} [Group M] [Finite M] [Group.IsPerfect M] {r : ℕ}
    (hr : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ r = p ^ f)
    (hM : HasSL2Model M (fun q => q = r)) (D : Subgroup (MulAut M))
    (hD2 : ∀ d ∈ D, d * d = 1) (hD4 : Nat.card D = 4) :
    ∃ d ∈ D, d ≠ 1 ∧ Group.IsSolvable ↥(fixSub d) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := quot_center_equiv_psl hM
  obtain ⟨p, f, hp, hp2, hf, hrpf⟩ := hr
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hF.trans hrpf⟩
  exact exists_solvable_fix hodd e D hD2 hD4

end S3Sec29B7Aut

end CFSG.GH74.Generic.BProg.B3
