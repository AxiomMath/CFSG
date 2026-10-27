module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_exists_normalizing_of_lt [Finite G] {R R' : Subgroup G} (hR' : IsPGroup 2 R')
    (hle : R ≤ R') (hne : R ≠ R') :
    ∃ y ∈ R', y ∉ R ∧ y ∈ normalizer (R : Set G) := by
  let H : Subgroup ↥R' := R.subgroupOf R'
  have hHlt : H < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    exact hne (le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop))
  haveI : Group.IsNilpotent ↥R' := hR'.isNilpotent
  obtain ⟨y', hy'norm, hy'H⟩ :=
    SetLike.exists_of_lt ((Group.normalizerCondition_of_isNilpotent (G := ↥R')) H hHlt)
  refine ⟨(y' : G), y'.2, ?_, ?_⟩
  · intro hyR
    exact hy'H (by rwa [Subgroup.mem_subgroupOf])
  · rw [Subgroup.mem_set_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hx' : (⟨x, hle hx⟩ : ↥R') ∈ H := by
        rw [Subgroup.mem_subgroupOf]; exact hx
      have hmem := (Subgroup.mem_normalizer_iff.mp hy'norm (⟨x, hle hx⟩ : ↥R')).mp hx'
      rw [Subgroup.mem_subgroupOf] at hmem
      simpa using hmem
    · intro hx
      have hxR' : x ∈ R' := by
        have h1 : (y' : G)⁻¹ * ((y' : G) * x * (y' : G)⁻¹) * (y' : G) ∈ R' :=
          R'.mul_mem (R'.mul_mem (R'.inv_mem y'.2) (hle hx)) y'.2
        have heq : (y' : G)⁻¹ * ((y' : G) * x * (y' : G)⁻¹) * (y' : G) = x := by group
        rwa [heq] at h1
      have hconj : (y' : ↥R') * (⟨x, hxR'⟩ : ↥R') * (y' : ↥R')⁻¹ ∈ H := by
        rw [Subgroup.mem_subgroupOf]
        simpa using hx
      have hx'H := (Subgroup.mem_normalizer_iff.mp hy'norm (⟨x, hxR'⟩ : ↥R')).mpr hconj
      rwa [Subgroup.mem_subgroupOf] at hx'H

private lemma map_mem_zpowers_of_eq {z w : G} (e : G ≃* G) (hez : e z = z)
    (hw : w ∈ zpowers z) : e w ∈ zpowers z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [map_zpow, hez]
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩

private lemma isElemAbelianMod_map {z : G} {U : Subgroup G} (e : G ≃* G)
    (hez : e z = z) (hU : IsElemAbelianMod z U) :
    IsElemAbelianMod z (U.map e.toMonoidHom) := by
  intro a' ha' b' hb'
  obtain ⟨a, haU, rfl⟩ := Subgroup.mem_map.mp ha'
  obtain ⟨b, hbU, rfl⟩ := Subgroup.mem_map.mp hb'
  obtain ⟨hc, hs⟩ := hU a haU b hbU
  refine ⟨?_, ?_⟩
  · change e a * e b * (e a)⁻¹ * (e b)⁻¹ ∈ zpowers z
    have h : e (a * b * a⁻¹ * b⁻¹) = e a * e b * (e a)⁻¹ * (e b)⁻¹ := by
      simp only [map_mul, map_inv]
    rw [← h]
    exact map_mem_zpowers_of_eq e hez hc
  · change e a * e a ∈ zpowers z
    have h : e (a * a) = e a * e a := by simp only [map_mul]
    rw [← h]
    exact map_mem_zpowers_of_eq e hez hs

private lemma map_isMaxElemAbelianMod {z : G} {R : Subgroup G} (e : G ≃* G)
    (hez : e z = z) (heR : ∀ w : G, w ∈ R ↔ e w ∈ R)
    {U : Subgroup G} (hU : IsMaxElemAbelianMod z R U) :
    IsMaxElemAbelianMod z R (U.map e.toMonoidHom) := by
  have heinvR : ∀ w : G, w ∈ R ↔ e.symm w ∈ R := by
    intro w
    have h := heR (e.symm w)
    simpa using h.symm
  have hezi : e.symm z = z := by
    have h := congrArg (⇑e.symm) hez
    simpa using h.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨a, haU, rfl⟩ := Subgroup.mem_map.mp hb
    exact (heR a).mp (hU.1 haU)
  · rw [Subgroup.mem_map_equiv]
    simpa [hezi] using hU.2.1
  · exact isElemAbelianMod_map e hez hU.2.2.1
  · intro V hVR hzV hVmod
    have hV0R : V.map e.symm.toMonoidHom ≤ R := fun w hw => by
      obtain ⟨v, hvV, rfl⟩ := Subgroup.mem_map.mp hw
      exact (heinvR v).mp (hVR hvV)
    have hV0z : z ∈ V.map e.symm.toMonoidHom := by
      rw [Subgroup.mem_map_equiv]
      simpa [hez] using hzV
    have hV0mod : IsElemAbelianMod z (V.map e.symm.toMonoidHom) :=
      isElemAbelianMod_map e.symm hezi hVmod
    have hcard := hU.2.2.2 _ hV0R hV0z hV0mod
    calc Nat.card V = Nat.card (V.map e.symm.toMonoidHom) :=
          (Subgroup.card_map_of_injective e.symm.injective).symm
      _ ≤ Nat.card U := hcard
      _ = Nat.card (U.map e.toMonoidHom) :=
          (Subgroup.card_map_of_injective e.injective).symm

theorem sec11_JMod_conj {z y : G} {R : Subgroup G} (hyz : y * z * y⁻¹ = z)
    (hy : y ∈ normalizer (R : Set G)) {x : G} (hx : x ∈ JMod z R) : y * x * y⁻¹ ∈ JMod z R := by
  have hez : (MulAut.conj y) z = z := hyz
  have heR : ∀ w : G, w ∈ R ↔ (MulAut.conj y) w ∈ R :=
    fun w => Subgroup.mem_set_normalizer_iff.mp hy w
  have key : ∀ U : Subgroup G, IsMaxElemAbelianMod z R U →
      IsMaxElemAbelianMod z R (U.map (MulAut.conj y).toMonoidHom) :=
    fun U hU => map_isMaxElemAbelianMod (MulAut.conj y) hez heR hU
  refine Subgroup.closure_induction (p := fun w _ => y * w * y⁻¹ ∈ JMod z R) ?_ ?_ ?_ ?_ hx
  · intro a ha
    obtain ⟨U, hU, haU⟩ := ha
    exact Subgroup.subset_closure ⟨U.map (MulAut.conj y).toMonoidHom, key U hU,
      Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom haU⟩
  · simpa using (JMod z R).one_mem
  · intro a b _ _ iha ihb
    have heq : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
    rw [heq]; exact (JMod z R).mul_mem iha ihb
  · intro a _ iha
    have heq : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
    rw [heq]; exact (JMod z R).inv_mem iha

theorem sec11_conj_mem_oTwoRes {X Y : Subgroup G} {g : G} (hXY : ∀ x ∈ X, g⁻¹ * x * g ∈ Y)
    {v : G} (hv : v ∈ oTwoRes X) : g⁻¹ * v * g ∈ oTwoRes Y := by
  refine Subgroup.closure_induction (p := fun w _ => g⁻¹ * w * g ∈ oTwoRes Y) ?_ ?_ ?_ ?_ hv
  · intro x hx
    obtain ⟨hxX, hxodd⟩ := hx
    refine Subgroup.subset_closure ⟨hXY x hxX, ?_⟩
    rw [← SemiconjBy.orderOf_eq (g⁻¹) (by show g⁻¹ * x = (g⁻¹ * x * g) * g⁻¹; group)]
    exact hxodd
  · simpa using (oTwoRes Y).one_mem
  · intro a b _ _ iha ihb
    have heq : g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by group
    rw [heq]; exact (oTwoRes Y).mul_mem iha ihb
  · intro a _ iha
    have heq : g⁻¹ * a⁻¹ * g = (g⁻¹ * a * g)⁻¹ := by group
    rw [heq]; exact (oTwoRes Y).inv_mem iha

theorem sec11_le_of_sup_odd [Finite G] {A N K Q : Subgroup G} (hNK : N ≤ K) (hAK : A ≤ K)
    (hNn : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) (hodd : Odd (Nat.card N)) (hsup : K = A ⊔ N)
    (hQ : IsPGroup 2 Q) (hQK : Q ≤ K)
    (h2 : ∀ v ∈ K, (∃ m : ℕ, v ^ (2 ^ m) = 1) → v ∈ Q) : Q ≤ A := by
  have hNnormal : (N.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNK]
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn; exact hNn k hk n hn
    · intro hn
      have h := hNn k⁻¹ (K.inv_mem hk) (k * n * k⁻¹) hn
      simpa [mul_assoc] using h
  have hrelNK : N.relIndex K = N.relIndex A := by
    haveI : (N.subgroupOf K).Normal := hNnormal
    have h := Subgroup.relIndex_sup_right (H := A.subgroupOf K) (K := N.subgroupOf K)
    rw [← Subgroup.subgroupOf_sup hAK hNK, ← hsup, Subgroup.subgroupOf_self,
      Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hAK] at h
    exact h
  have hcount : A.relIndex K * Nat.card (N ⊓ A : Subgroup G) = Nat.card N := by
    have h1 : A.relIndex K * Nat.card A = Nat.card K := by
      have h := Subgroup.relIndex_mul_card A K
      rwa [inf_eq_left.mpr hAK] at h
    have h2 : N.relIndex K * Nat.card N = Nat.card K := by
      have h := Subgroup.relIndex_mul_card N K
      rwa [inf_eq_left.mpr hNK] at h
    have h3 : N.relIndex A * Nat.card (N ⊓ A : Subgroup G) = Nat.card A :=
      Subgroup.relIndex_mul_card N A
    have hpos : N.relIndex A ≠ 0 :=
      (Subgroup.finiteIndex_of_finite (H := N.subgroupOf A)).index_ne_zero
    have eq1 : A.relIndex K * Nat.card A = N.relIndex A * Nat.card N := by
      rw [h1, ← h2, hrelNK]
    have eq2 : A.relIndex K * (N.relIndex A * Nat.card (N ⊓ A : Subgroup G)) =
        N.relIndex A * Nat.card N := by
      rw [h3]; exact eq1
    have eq3 : (A.relIndex K * Nat.card (N ⊓ A : Subgroup G)) * N.relIndex A =
        Nat.card N * N.relIndex A := by
      calc (A.relIndex K * Nat.card (N ⊓ A : Subgroup G)) * N.relIndex A
          = A.relIndex K * (N.relIndex A * Nat.card (N ⊓ A : Subgroup G)) := by ring
        _ = N.relIndex A * Nat.card N := eq2
        _ = Nat.card N * N.relIndex A := by ring
    exact Nat.mul_right_cancel (Nat.pos_iff_ne_zero.mpr hpos) eq3
  have hoddAK : Odd (A.relIndex K) :=
    hodd.of_dvd_nat ⟨Nat.card (N ⊓ A : Subgroup G), hcount.symm⟩
  obtain ⟨P, hP⟩ := exists_isSylow2Of (G := G) A
  have hPA : P ≤ A := hP.1
  have hP2 : IsPGroup 2 P := hP.2.1
  have hoddPA : Odd (P.relIndex A) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact hP.2.2
  have hoddPK : Odd (P.relIndex K) := by
    rw [← Subgroup.relIndex_mul_relIndex (H := P) (K := A) (L := K) hPA hAK]
    exact hoddPA.mul hoddAK
  have hPKsyl : IsSylow2Of P K :=
    ⟨hPA.trans hAK, hP2,
      fun h => (Nat.not_even_iff_odd.mpr hoddPK) (even_iff_two_dvd.mpr h)⟩
  have hPQ : P ≤ Q := by
    intro v hv
    obtain ⟨m, hm⟩ := (isPGroup_iff_pow_pow_eq_one.mp hP2) (⟨v, hv⟩ : ↥P)
    exact h2 v (hAK (hPA hv)) ⟨m, by simpa using congrArg (Subtype.val) hm⟩
  have hQeqP : Q = P := hPKsyl.eq_of_le hQK hQ hPQ
  rw [hQeqP]
  exact hPA

end CFSG.OddStandard.SmallF3.Omega
