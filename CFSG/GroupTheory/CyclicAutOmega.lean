module

public import CFSG.GroupTheory.PGroup.OmegaComm
public import Mathlib.GroupTheory.IsPerfect
import CFSG.HardMathSupport.Lang.Proving.CubeClassCyclic
import CFSG.Mathlib.GroupTheory.Focal
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.GroupTheory

theorem mem_range_pow_three_of_fixes_omega₁ {X : Type*} [CommGroup X] [IsCyclic X] [Finite X]
    (φ : MulAut X) (h3 : 3 ∣ Nat.card X)
    (hfix : ∀ x ∈ CFSG.omega₁ X (p := 3), φ x = x) (x : X) :
    x⁻¹ * φ x ∈ (powMonoidHom 3 : X →* X).range := by
  rw [CFSG.HardMathSupport.Lang.Proving.mem_range_pow_three_iff h3]
  have hxΩ : x ^ (Nat.card X / 3) ∈ CFSG.omega₁ X (p := 3) := by
    rw [CFSG.mem_omega₁_iff_of_comm (fun a b => mul_comm a b)]
    rw [← pow_mul, Nat.div_mul_cancel h3]
    exact pow_card_eq_one' (G := X)
  have hφx : (φ x) ^ (Nat.card X / 3) = x ^ (Nat.card X / 3) := by
    have h := hfix _ hxΩ
    rwa [map_pow] at h
  rw [mul_pow, inv_pow, hφx, inv_mul_cancel]

theorem omega_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (p k : ℕ) :
    (CFSG.omega X (p := p) k).map e.toMonoidHom = CFSG.omega Y (p := p) k := by
  simp only [CFSG.omega, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using congrArg e hx
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    simpa using congrArg e.symm hy

theorem normalizer_le_normalizer_omega₁_map_subtype {X : Type*} [Group X] (Q : Subgroup X) :
    Subgroup.normalizer (Q : Set X) ≤
      Subgroup.normalizer ((CFSG.omega₁ ↥Q (p := 3)).map Q.subtype : Set X) := by
  haveI : (CFSG.omega₁ ↥Q (p := 3)).Characteristic := CFSG.omega₁_characteristic ↥Q
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (CFSG.omega₁ ↥Q (p := 3))

theorem exists_mem_normalizer_conj_eq_inv_of_perfect
    {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (Q : Sylow 3 X) [IsCyclic ↥(Q : Subgroup X)] (hQ : (Q : Subgroup X) ≠ ⊥) :
    ∃ n ∈ Subgroup.normalizer (Q : Set X),
      ∀ a ∈ (CFSG.omega₁ ↥(Q : Subgroup X) (p := 3)).map (Q : Subgroup X).subtype,
        n * a * n⁻¹ = a⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : CommGroup ↥(Q : Subgroup X) := IsCyclic.commGroup
  let A : Subgroup X := (CFSG.omega₁ ↥(Q : Subgroup X) (p := 3)).map (Q : Subgroup X).subtype
  have h3dvd : 3 ∣ Nat.card ↥(Q : Subgroup X) := by
    rcases Q.isPGroup'.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hQ
    · exact h
  have hAcard : Nat.card A = 3 := by
    rw [show A = (CFSG.omega₁ ↥(Q : Subgroup X) (p := 3)).map
        (Q : Subgroup X).subtype from rfl,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      CFSG.card_omega₁_of_isCyclic, Nat.gcd_eq_right h3dvd]
  have hnormA := normalizer_le_normalizer_omega₁_map_subtype (Q : Subgroup X)
  by_contra hcon
  push Not at hcon
  have hcentral : ∀ n ∈ Subgroup.normalizer (Q : Set X), ∀ a ∈ A, n * a * n⁻¹ = a := by
    intro n hn a ha
    obtain ⟨b, hbA, hbne⟩ := hcon n hn
    have hb1 : b ≠ 1 := by
      rintro rfl
      exact hbne (by group)
    have hbpow3 : b ^ 3 = 1 := by
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hbA
      have h := (CFSG.mem_omega₁_iff_of_comm (X := ↥(Q : Subgroup X)) (p := 3)
        (fun x y => mul_comm x y)).mp hb'
      simpa using congrArg (fun z : ↥(Q : Subgroup X) => (z : X)) h
    have hborder : orderOf b = 3 := orderOf_eq_prime hbpow3 hb1
    have hbgen : A = Subgroup.zpowers b := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbA) ?_).symm
      rw [Nat.card_zpowers, hborder, hAcard]
    have hnbA : n * b * n⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hnormA hn) b).mp hbA
    have hnb1 : n * b * n⁻¹ ≠ 1 := by
      intro h
      apply hb1
      calc b = n⁻¹ * (n * b * n⁻¹) * n := by group
        _ = n⁻¹ * 1 * n := by rw [h]
        _ = 1 := by group
    have hnb : n * b * n⁻¹ = b := by
      have hbne' : b ≠ b⁻¹ := by
        intro h
        have h2 : b ^ 2 = 1 := by
          rw [pow_two]
          nth_rewrite 2 [h]
          exact mul_inv_cancel b
        have hdvd : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one h2
        rw [hborder] at hdvd
        omega
      have hset : ({1, b, b⁻¹} : Set X) = A := by
        refine Set.eq_of_subset_of_ncard_le ?_ ?_
        · intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl
          · exact A.one_mem
          · exact hbA
          · exact A.inv_mem hbA
        · have hA : (A : Set X).ncard = 3 := by
            rw [← Nat.card_coe_set_eq]
            exact hAcard
          rw [hA]
          have hcard : ({1, b, b⁻¹} : Set X).ncard = 3 := by
            rw [Set.ncard_eq_toFinset_card']
            simp only [Set.toFinset_insert, Set.toFinset_singleton]
            have h1 : b ∉ ({b⁻¹} : Finset X) := by simpa using hbne'
            have h2 : (1 : X) ∉ insert b ({b⁻¹} : Finset X) := by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hb1.symm, fun h => hb1 (inv_eq_one.mp h.symm)⟩
            rw [Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h1,
              Finset.card_singleton]
          omega
      have hmem : n * b * n⁻¹ ∈ ({1, b, b⁻¹} : Set X) := hset ▸ hnbA
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h | h
      · exact absurd h hnb1
      · exact h
      · exact absurd h hbne
    have hcomm : MulAut.conj n b = b := by
      simpa [MulAut.conj_apply] using hnb
    have ha_mem : a ∈ Subgroup.zpowers b := by
      rw [← hbgen]
      exact ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha_mem
    have hconj : MulAut.conj n a = a := by
      rw [← hk, map_zpow, hcomm]
    simpa [MulAut.conj_apply] using hconj
  have hfocal : False := by
    let QX : Subgroup X := (Q : Subgroup X)
    let Q3 : Subgroup X := (powMonoidHom 3 : ↥QX →* ↥QX).range.map QX.subtype
    have h3dvdQX : 3 ∣ Nat.card ↥QX := h3dvd
    have hfocal_le : QX.focalSubgroup ≤ Q3 := by
      rw [Subgroup.focalSubgroup_eq_closure_isConj]
      refine (Subgroup.closure_le (K := Q3)).2 ?_
      rintro z ⟨x, hxQ, y, hyQ, hxy, rfl⟩
      obtain ⟨c, hc⟩ := isConj_iff.mp hxy
      have hyQ' : (c⁻¹)⁻¹ * x * c⁻¹ ∈ QX := by
        simpa [hc] using hyQ
      obtain ⟨n, hnN, hn⟩ := Q.conj_eq_normalizer_conj_of_mem x c⁻¹ hxQ hyQ'
      have hnNinv : n⁻¹ ∈ Subgroup.normalizer (Q : Set X) := Subgroup.inv_mem _ hnN
      have hfix : ∀ a ∈ CFSG.omega₁ ↥QX (p := 3),
          (Q.normalizerMonoidHom ⟨n⁻¹, hnNinv⟩) a = a := by
        intro a ha
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        simp only [Subgroup.coe_mk, inv_inv]
        have haA : (a : X) ∈ A := Subgroup.mem_map_of_mem _ ha
        have h := hcentral n hnN (a : X) haA
        calc n⁻¹ * (a : X) * n = n⁻¹ * (n * (a : X) * n⁻¹) * n := by rw [h]
          _ = (a : X) := by group
      have hmem := mem_range_pow_three_of_fixes_omega₁ (X := ↥QX)
        (Q.normalizerMonoidHom ⟨n⁻¹, hnNinv⟩) h3dvdQX hfix ⟨x, hxQ⟩
      have hval : (((⟨x, hxQ⟩ : ↥QX)⁻¹ * (Q.normalizerMonoidHom ⟨n⁻¹, hnNinv⟩) ⟨x, hxQ⟩ : ↥QX) : X)
          = x⁻¹ * y := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        simp only [Subgroup.coe_mk, inv_inv]
        have : n⁻¹ * x * n = y := by
          rw [← hn]
          simpa using hc
        rw [this]
      rw [← hval]
      exact Subgroup.mem_map_of_mem _ hmem
    have hfocal_eq : QX.focalSubgroup = QX := by
      have h := Subgroup.commutator_inf_eq_focalSubgroup Q
      rw [Group.IsPerfect.commutator_eq_top, top_inf_eq] at h
      exact h.symm
    have hQle : QX ≤ Q3 := hfocal_eq ▸ hfocal_le
    have hQ3lt : Q3 < QX := by
      refine lt_of_le_of_ne (Subgroup.map_subtype_le _) ?_
      intro heq
      have hcardrange : Nat.card ↥(powMonoidHom 3 : ↥QX →* ↥QX).range = Nat.card ↥QX / 3 := by
        rw [IsCyclic.card_powMonoidHom_range, Nat.gcd_eq_right h3dvdQX]
      have hcardQ3 : Nat.card Q3 = Nat.card ↥QX / 3 := by
        rw [show Q3 = (powMonoidHom 3 : ↥QX →* ↥QX).range.map QX.subtype from rfl,
          Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hcardrange]
      have hlt : Nat.card ↥QX / 3 < Nat.card ↥QX := by
        have hpos : 0 < Nat.card ↥QX := Nat.card_pos
        obtain ⟨m, hm⟩ := h3dvdQX
        have hmpos : 0 < m := by
          by_contra hm0
          have hmzero : m = 0 := by omega
          rw [hmzero, mul_zero] at hm
          exact Nat.card_pos.ne' hm
        rw [hm]
        have h3m : 3 * 1 ≤ 3 * m := Nat.mul_le_mul_left 3 hmpos
        omega
      have : Nat.card Q3 = Nat.card QX := by rw [heq]
      rw [hcardQ3] at this
      omega
    exact hQ3lt.2 hQle
  exact hfocal


end CFSG.GroupTheory

end
