module

import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeUC.CoreWitness

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

@[expose] def twoLocalClosure {G : Type*} [Group G] (E : Subgroup G) : Subgroup G :=
  ⨆ (H : Subgroup G) (_ : IsTwoLocal H ∧ E ≤ H), H

theorem twoLocalClosure_ne_top {G : Type} [Group G] [Finite G] (hS : Standing G)
    (hUC : rankThreeUC G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {E : Subgroup G} (hE : IsPGroup p E) (hE2 : 2 ≤ CFSG.Open.pRank p E) :
    twoLocalClosure E ≠ ⊤ := by
  have hprime : p.Prime := sigmaA_prime p hp
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨Q, hEQ⟩ := hE.exists_le_sylow
  obtain ⟨M, hM⟩ := exists_isCoreWitness hUC hp Q
  have hQM : (Q : Subgroup G) ≤ M := le_normalizer.trans (hM.normalizer_le hS hp)
  have hle : twoLocalClosure E ≤ M := by
    refine iSup₂_le fun H hH => ?_
    exact hM.u2 H hH.1 (hE2.trans (pRank_mono p hprime.one_lt (le_inf hH.2 (hEQ.trans hQM))))
  intro htop
  have := hS.simple
  exact twoLocal_ne_top hS.nonab M hM.maxLocal.1 (top_le_iff.mp (htop ▸ hle))

theorem map_twoLocalClosure_le {G H : Type} [Group G] [Group H] (e : G ≃* H) (E : Subgroup G) :
    (twoLocalClosure E).map e.toMonoidHom ≤ twoLocalClosure (E.map e.toMonoidHom) := by
  rw [twoLocalClosure, Subgroup.map_iSup]
  refine iSup_le fun H' => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun h => ?_
  exact le_iSup₂_of_le (H'.map e.toMonoidHom)
    ⟨CFSG.RankThree.PartTwo.Census.isTwoLocal_map_mulEquiv h.1 e, Subgroup.map_mono h.2⟩ le_rfl



theorem twoLocalClosure_eq_top_of_invariant_two_subgroups {G : Type*} [Group G] (E : Subgroup G) (𝒮 : Set (Subgroup G))
    (h2 : ∀ S ∈ 𝒮, S ≠ ⊥ ∧ IsPGroup 2 S ∧ E ≤ normalizer (S : Set G))
    (hgen : ⨆ S ∈ 𝒮, S = ⊤) : twoLocalClosure E = ⊤ := by
  refine top_le_iff.mp (hgen ▸ iSup₂_le fun S hS => ?_)
  obtain ⟨hS1, hS2, hE⟩ := h2 S hS
  exact le_iSup₂_of_le (normalizer (S : Set G)) ⟨⟨S, hS1, hS2, rfl⟩, hE⟩ le_normalizer

theorem exists_orderOf_two {H : Type*} [Group H] [Finite H] (h2 : 2 ∣ Nat.card H) :
    ∃ x : H, orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite H
  exact exists_prime_orderOf_dvd_card 2 (by rwa [Nat.card_eq_fintype_card] at h2)

theorem map_ne_bot_of_noInvolution {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* G)
    (hker : ∀ z ∈ φ.ker, z ^ 2 = 1 → z = 1) {R : Subgroup A} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) :
    R.map φ ≠ ⊥ := by
  intro hbot
  have hRker : R ≤ φ.ker := by
    rw [← Subgroup.map_eq_bot_iff]; exact hbot
  have hcard : 2 ∣ Nat.card R := by
    rcases hR2.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hR
    · exact h
  obtain ⟨x, hx⟩ := exists_orderOf_two hcard
  have hx2 : (x : A) ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  have hx1 : (x : A) = 1 := hker x (hRker x.2) hx2
  have : x = 1 := Subtype.ext hx1
  rw [this, orderOf_one] at hx
  omega

theorem map_twoLocalClosure_le_of_ker {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* G)
    (hker : ∀ z ∈ φ.ker, z ^ 2 = 1 → z = 1) (E : Subgroup A) :
    (twoLocalClosure E).map φ ≤ twoLocalClosure (E.map φ) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun H hH => ?_
  obtain ⟨R, hR1, hR2, rfl⟩ := hH.1
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_iSup₂_of_le (normalizer ((R.map φ : Subgroup G) : Set G))
    ⟨⟨R.map φ, map_ne_bot_of_noInvolution φ hker hR1 hR2, hR2.map φ, rfl⟩,
      (Subgroup.map_mono hH.2).trans (Subgroup.le_normalizer_map φ)⟩
    (Subgroup.le_normalizer_map φ)

theorem odd_card_comap {A G : Type*} [Group A] [Group G] [Finite A] (φ : A →* G)
    (hker : ∀ z ∈ φ.ker, z ^ 2 = 1 → z = 1) {E : Subgroup G} (hE : Odd (Nat.card E)) :
    Odd (Nat.card (E.comap φ)) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card (E.comap φ) := by
    rw [Nat.not_odd_iff_even] at hodd
    exact even_iff_two_dvd.mp hodd
  obtain ⟨x, hx⟩ := exists_orderOf_two h2
  have hx2 : (x : A) ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  have hφx : φ (x : A) ∈ E := x.2
  have hsq : (⟨φ (x : A), hφx⟩ : E) ^ 2 = 1 := by
    apply Subtype.ext
    simp [← map_pow, hx2]
  have hd1 : orderOf (⟨φ (x : A), hφx⟩ : E) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hd2 : orderOf (⟨φ (x : A), hφx⟩ : E) ∣ Nat.card E := orderOf_dvd_natCard _
  have hodd' : Odd (orderOf (⟨φ (x : A), hφx⟩ : E)) := hE.of_dvd_nat hd2
  have h1 : orderOf (⟨φ (x : A), hφx⟩ : E) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd1 with h | h
    · exact h
    · rw [h] at hodd'; exact absurd hodd' (by decide)
  have hφ1 : φ (x : A) = 1 := congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
  have hx1 : (x : A) = 1 := hker x (MonoidHom.mem_ker.mpr hφ1) hx2
  have : x = 1 := Subtype.ext hx1
  rw [this, orderOf_one] at hx
  omega


theorem mem_sylow_of_pow_eq_one {Q : Type*} [Group Q] [Finite Q] (P : Sylow 2 Q)
    [Subsingleton (Sylow 2 Q)] {y : Q} {k : ℕ} (h : y ^ 2 ^ k = 1) : y ∈ (P : Subgroup Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : IsPGroup 2 (Subgroup.zpowers y) := by
    intro w
    obtain ⟨m, hm⟩ := w.2
    refine ⟨k, ?_⟩
    apply Subtype.ext
    have hw : ((w : Q)) = y ^ m := hm.symm
    show (w : Q) ^ 2 ^ k = 1
    rw [hw, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]
  obtain ⟨P2, hP2⟩ := hz.exists_le_sylow
  have : P2 = P := Subsingleton.elim _ _
  exact this ▸ hP2 (Subgroup.mem_zpowers y)

theorem exists_normalized_two_subgroup {A G : Type*} [Group A] [Group G] [Finite A]
    (φ : A →* G) (hφ : Function.Surjective φ) (hc : φ.ker ≤ Subgroup.center A)
    {S : Subgroup G} (hS : S ≠ ⊥) (hS2 : IsPGroup 2 S) {E : Subgroup G}
    (hEN : E ≤ normalizer (S : Set G)) :
    ∃ P : Subgroup A, P ≠ ⊥ ∧ IsPGroup 2 P ∧ E.comap φ ≤ normalizer (P : Set A) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite G := Finite.of_surjective φ hφ
  set Q : Subgroup A := S.comap φ with hQdef
  let ψ : Q →* S := (φ.comp Q.subtype).codRestrict S (fun x => x.2)
  have hψ_apply : ∀ x : Q, ((ψ x : S) : G) = φ (x : A) := fun x => rfl
  have hψker : ψ.ker ≤ Subgroup.center Q := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx' : (x : A) ∈ φ.ker := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact MonoidHom.mem_ker.mpr (by simpa [hψ_apply] using this)
    have hxc := (Subgroup.mem_center_iff.mp (hc hx')) (y : A)
    exact Subtype.ext hxc
  have : Group.IsNilpotent S := hS2.isNilpotent
  have : Group.IsNilpotent Q := Subgroup.isNilpotent_of_ker_le_center ψ hψker
  obtain ⟨P⟩ : Nonempty (Sylow 2 Q) := inferInstance
  have hPn : (P : Subgroup Q).Normal :=
    Sylow.normal_of_normalizerCondition Group.normalizerCondition_of_isNilpotent P
  have : Unique (Sylow 2 Q) := Sylow.unique_of_normal P hPn
  have hψs : Function.Surjective ψ := by
    intro s
    obtain ⟨a, ha⟩ := hφ (s : G)
    have haQ : a ∈ Q := by
      show φ a ∈ S
      rw [ha]; exact s.2
    exact ⟨⟨a, haQ⟩, Subtype.ext (by simpa [hψ_apply] using ha)⟩
  have hQdvd : 2 ∣ Nat.card Q := by
    have h1 : Nat.card S ∣ Nat.card Q := Subgroup.card_dvd_of_surjective hψs
    have h2 : 2 ∣ Nat.card S :=
      (hS2.card_eq_or_dvd).resolve_left (fun h => hS (Subgroup.card_eq_one.mp h))
    exact h2.trans h1
  obtain ⟨x, hx⟩ := exists_orderOf_two hQdvd
  have hxP : x ∈ (P : Subgroup Q) :=
    mem_sylow_of_pow_eq_one P (k := 1) (by rw [pow_one]; exact hx ▸ pow_orderOf_eq_one x)
  refine ⟨(P : Subgroup Q).map Q.subtype, ?_, ?_, ?_⟩
  · intro hbot
    have : (x : A) = 1 := by
      have hmem : (x : A) ∈ (P : Subgroup Q).map Q.subtype := ⟨x, hxP, rfl⟩
      rw [hbot] at hmem
      exact hmem
    have hx1 : x = 1 := Subtype.ext this
    rw [hx1, orderOf_one] at hx
    omega
  · exact (P.isPGroup').map Q.subtype
  ·
    have heQ : ∀ g ∈ E.comap φ, ∀ a : A, a ∈ Q ↔ g * a * g⁻¹ ∈ Q := by
      intro g hg a
      have := Subgroup.mem_normalizer_iff.mp (hEN hg) (φ a)
      simpa [hQdef, Subgroup.mem_comap, map_mul, map_inv] using this
    have key : ∀ g ∈ E.comap φ, ∀ y ∈ (P : Subgroup Q).map Q.subtype,
        g * y * g⁻¹ ∈ (P : Subgroup Q).map Q.subtype := by
      intro g hg y hy
      obtain ⟨y', hy', rfl⟩ := hy
      have hgQ : g * (y' : A) * g⁻¹ ∈ Q := (heQ g hg _).mp y'.2
      obtain ⟨k, hk⟩ := P.isPGroup' ⟨y', hy'⟩
      have hk' : y' ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have hz : (⟨g * (y' : A) * g⁻¹, hgQ⟩ : Q) ^ 2 ^ k = 1 := by
        apply Subtype.ext
        simp only [Subgroup.coe_pow, Subgroup.coe_one]
        rw [conj_pow, ← Subgroup.coe_pow, hk', Subgroup.coe_one]
        simp
      exact ⟨_, mem_sylow_of_pow_eq_one P hz, rfl⟩
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => key g hg h hh
    · intro hh
      have := key g⁻¹ ((E.comap φ).inv_mem hg) _ hh
      simpa [mul_assoc] using this


end CFSG.LocalAnalysis.RankThreeUC
