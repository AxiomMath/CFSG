module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec12a3
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec12a4

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims122

open Equiv Equiv.Perm CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open scoped commutatorElement

section Perfect

variable {G : Type} [Group G] [Finite G]

theorem eq_bot_of_perfect_of_two {B : Subgroup G} (hB : ⁅B, B⁆ = B) (hB2 : IsPGroup 2 ↥B) :
    B = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  haveI : Nontrivial ↥B := (Subgroup.nontrivial_iff_ne_bot B).2 hne
  haveI : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.2 hB
  haveI : Group.IsNilpotent ↥B := hB2.isNilpotent
  exact Group.IsPerfect.not_isSolvable ↥B inferInstance

omit [Finite G] in
theorem mul_pow_mul_inv_mem {J : Subgroup G} {u p : G} (hu : u ∈ J)
    (hp : p ∈ Subgroup.normalizer (J : Set G)) (m : ℕ) : (u * p) ^ m * (p ^ m)⁻¹ ∈ J := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hpm : p ^ m ∈ Subgroup.normalizer (J : Set G) := Subgroup.pow_mem _ hp m
    have h1 : p ^ m * u * (p ^ m)⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hpm u).1 hu
    have e : (u * p) ^ (m + 1) * (p ^ (m + 1))⁻¹ =
        ((u * p) ^ m * (p ^ m)⁻¹) * (p ^ m * u * (p ^ m)⁻¹) := by
      rw [pow_succ, pow_succ]; group
    rw [e]
    exact J.mul_mem ih h1

theorem perfect_le_of_two_quot {X J Y : Subgroup G} (hXY : X ≤ Y) (hJY : J ≤ Y)
    (hYJ : Y ≤ Subgroup.normalizer (J : Set G)) (hX : ⁅X, X⁆ = X)
    (h2 : ∀ y ∈ Y, ∃ n : ℕ, y ^ 2 ^ n ∈ J) : X ≤ J := by
  haveI hN : (J.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJY).2 hYJ
  set φ := QuotientGroup.mk' (J.subgroupOf Y) with hφ
  set B : Subgroup (↥Y ⧸ J.subgroupOf Y) := (X.subgroupOf Y).map φ with hB
  have hXc : ⁅X.subgroupOf Y, X.subgroupOf Y⁆ = X.subgroupOf Y := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXY, hX]
  have hBc : ⁅B, B⁆ = B := by rw [hB, ← Subgroup.map_commutator, hXc]
  have hB2 : IsPGroup 2 ↥B := by
    rintro ⟨_, x, -, rfl⟩
    obtain ⟨n, hn⟩ := h2 x x.2
    refine ⟨n, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.2 (by simpa using hn)
  have hB0 := eq_bot_of_perfect_of_two hBc hB2
  intro x hx
  have h1 : φ ⟨x, hXY hx⟩ ∈ B := Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.2 hx)
  rw [hB0, Subgroup.mem_bot, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact Subgroup.mem_subgroupOf.1 h1

theorem le_normalizer_of_isSubnormal_perfect (n : ℕ) :
    ∀ X : Subgroup G, Nat.card X = n → ∀ J R : Subgroup G, IsSubnormal J X → ⁅J, J⁆ = J →
      R ≤ X → X ≤ Subgroup.normalizer (R : Set G) → IsPGroup 2 ↥R →
        R ≤ Subgroup.normalizer (J : Set G) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hXn J R hJX hJ hRX hXR hR2
  by_cases hJeq : J = X
  · subst hJeq
    exact hRX.trans Subgroup.le_normalizer
  obtain ⟨Y, hJY, hYX, hYne, hYn, hJY'⟩ := isSubnormal_exists_normal hJX hJeq
  have hYlt : Nat.card Y < n := hXn ▸ card_lt_of_lt' (lt_of_le_of_ne hYX hYne)
  have hXY : X ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).1 hYn
  have hRY : R ⊓ Y ≤ Subgroup.normalizer (J : Set G) :=
    ih _ hYlt Y rfl J (R ⊓ Y) hJY' hJ inf_le_right
      (fun y hy => mem_normalizer_inf (hXR (hYX hy)) (Subgroup.le_normalizer hy))
      (hR2.to_le inf_le_left)
  have hJXle : J ≤ X := isSubnormal_le' hJX
  have key : ∀ x ∈ R, ∀ j ∈ J, x * j * x⁻¹ ∈ J := by
    intro x hx
    set W : Subgroup G := J ⊔ (R ⊓ Y) with hW
    have hWJ : W ≤ Subgroup.normalizer (J : Set G) := sup_le Subgroup.le_normalizer hRY
    set Jx : Subgroup G := J.map (MulAut.conj x).toMonoidHom with hJx
    have hJxW : Jx ≤ W := by
      rintro _ ⟨j, hj, rfl⟩
      have hjX : j ∈ X := hJXle hj
      have hc : x * j * x⁻¹ * j⁻¹ ∈ R ⊓ Y := by
        refine ⟨?_, ?_⟩
        · have h1 : j * x⁻¹ * j⁻¹ ∈ R :=
            (Subgroup.mem_normalizer_iff.1 (hXR hjX) _).1 (R.inv_mem hx)
          have h2 := R.mul_mem hx h1
          simpa [mul_assoc] using h2
        · have h1 : x * j * x⁻¹ ∈ Y :=
            (Subgroup.mem_normalizer_iff.1 (hXY (hRX hx)) j).1 (hJY hj)
          exact Y.mul_mem h1 (Y.inv_mem (hJY hj))
      have e : (MulAut.conj x).toMonoidHom j = (x * j * x⁻¹ * j⁻¹) * j := by
        simp [MulAut.conj_apply]
      rw [e]
      exact W.mul_mem ((le_sup_right : R ⊓ Y ≤ W) hc) ((le_sup_left : J ≤ W) hj)
    have hJxp : ⁅Jx, Jx⁆ = Jx := by rw [hJx, ← Subgroup.map_commutator, hJ]
    have h2 : ∀ w ∈ W, ∃ m : ℕ, w ^ 2 ^ m ∈ J := by
      intro w hw
      obtain ⟨u, hu, p, hp, rfl⟩ := Sec12a2.mem_sup_of_le_normalizer le_rfl hRY hw
      obtain ⟨m, hm⟩ := (hR2.to_le inf_le_left) ⟨p, hp⟩
      refine ⟨m, ?_⟩
      have hpm : p ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      have h3 := mul_pow_mul_inv_mem hu (hRY hp) (2 ^ m)
      rwa [hpm, inv_one, mul_one] at h3
    have hle := perfect_le_of_two_quot hJxW le_sup_left hWJ hJxp h2
    intro j hj
    exact hle ⟨j, hj, by simp [MulAut.conj_apply]⟩
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key x hx g, fun hg => ?_⟩
  have h1 := key x⁻¹ (R.inv_mem hx) _ hg
  simpa [mul_assoc] using h1

end Perfect

section Components

variable {G : Type} [Group G] [Finite G]

theorem core_le_normalizer {M J : Subgroup G} (hJ : Sec12a3.CompSet M J) :
    pCoreOf 2 M ≤ Subgroup.normalizer (J : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_normalizer_of_isSubnormal_perfect _ M rfl J (pCoreOf 2 M) hJ.2.1 hJ.2.2.1
    (CFSG.LieType.BorelTits.pCoreOf_le 2 M) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)

theorem le_of_le_sup_core {M J K : Subgroup G} (hK : Sec12a3.CompSet M K) (hJ : ⁅J, J⁆ = J)
    (hJK : J ≤ K ⊔ pCoreOf 2 M) : J ≤ K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO := core_le_normalizer hK
  refine perfect_le_of_two_quot hJK le_sup_left (sup_le Subgroup.le_normalizer hO) hJ ?_
  intro w hw
  obtain ⟨u, hu, p, hp, rfl⟩ := Sec12a2.mem_sup_of_le_normalizer le_rfl hO hw
  obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M ⟨p, hp⟩
  refine ⟨m, ?_⟩
  have hpm : p ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have h3 := mul_pow_mul_inv_mem hu (hO hp) (2 ^ m)
  rwa [hpm, inv_one, mul_one] at h3

theorem isTwoPrimeComp_of_compSet {M J : Subgroup G} (hJ : Sec12a3.CompSet M J) :
    IsTwoPrimeComp M J :=
  isTwoPrimeComp_of_le (Sec12a3.isTwoPrimeComp_self_of_hatSeven J hJ.2.2.2 hJ.2.2.1) hJ.1 hJ.2.1

theorem comm_mem_core {M J K : Subgroup G} (hJ : Sec12a3.CompSet M J)
    (hK : Sec12a3.CompSet M K) (hne : J ≠ K) {j k : G} (hj : j ∈ J) (hk : k ∈ K) :
    j * k * j⁻¹ * k⁻¹ ∈ pCoreOf 2 M := by
  set q := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hq
  have hJc := (isTwoPrimeComp_of_compSet hJ).2.2.2
  have hKc := (isTwoPrimeComp_of_compSet hK).2.2.2
  have hsup : ∀ {X Y : Subgroup G}, Sec12a3.CompSet M X → Sec12a3.CompSet M Y →
      (X.subgroupOf M).map q = (Y.subgroupOf M).map q → X ≤ Y ⊔ pCoreOf 2 M := by
    intro X Y hX hY heq x hx
    have h1 : q ⟨x, hX.1 hx⟩ ∈ (Y.subgroupOf M).map q :=
      heq ▸ Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.2 hx)
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h1
    have h2 : y⁻¹ * ⟨x, hX.1 hx⟩ ∈ CFSG.pCore 2 ↥M := QuotientGroup.eq.1 hyx
    have e : x = (y : G) * ((y⁻¹ * ⟨x, hX.1 hx⟩ : ↥M) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem _ ((le_sup_left : Y ≤ Y ⊔ pCoreOf 2 M) (Subgroup.mem_subgroupOf.1 hy))
      ((le_sup_right : pCoreOf 2 M ≤ Y ⊔ pCoreOf 2 M) ⟨_, h2, rfl⟩)
  have hne' : (J.subgroupOf M).map q ≠ (K.subgroupOf M).map q := fun heq =>
    hne (le_antisymm (le_of_le_sup_core hK hJ.2.2.1 (hsup hJ hK heq))
      (le_of_le_sup_core hJ hK.2.2.1 (hsup hK hJ heq.symm)))
  have hcomm : ⁅(J.subgroupOf M).map q, (K.subgroupOf M).map q⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute ((CFSG.isComponent_iff_open _).2 hJc)
      ((CFSG.isComponent_iff_open _).2 hKc)).resolve_left hne'
  have h1 : ⁅q ⟨j, hJ.1 hj⟩, q ⟨k, hK.1 hk⟩⁆ ∈
      ⁅(J.subgroupOf M).map q, (K.subgroupOf M).map q⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.2 hj))
      (Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.2 hk))
  rw [hcomm, Subgroup.mem_bot, ← map_commutatorElement, hq, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at h1
  refine ⟨_, h1, ?_⟩
  simp [commutatorElement_def]

theorem alpha_le_normalizer {M J : Subgroup G} (hJ : Sec12a3.CompSet M J) :
    alphaOf 3 M ≤ Subgroup.normalizer (J : Set G) := by
  unfold alphaOf
  refine sup_le (core_le_normalizer hJ) (iSup₂_le fun K hK => ?_)
  have hKc : Sec12a3.CompSet M K := ⟨hK.2.1, hK.2.2.1, hK.2.2.2.1, hK.2.2.2.2⟩
  by_cases hKJ : K = J
  · subst hKJ
    exact Subgroup.le_normalizer
  have key : ∀ k ∈ K, ∀ j ∈ J, k * j * k⁻¹ ∈ J := by
    intro k hk
    have hle : J.map (MulAut.conj k).toMonoidHom ≤ J ⊔ pCoreOf 2 M := by
      rintro _ ⟨j, hj, rfl⟩
      have hc := comm_mem_core hKc hJ hKJ hk hj
      have e : (MulAut.conj k).toMonoidHom j = (k * j * k⁻¹ * j⁻¹) * j := by
        simp [MulAut.conj_apply]
      rw [e]
      exact Subgroup.mul_mem _ ((le_sup_right : pCoreOf 2 M ≤ J ⊔ pCoreOf 2 M) hc)
        ((le_sup_left : J ≤ J ⊔ pCoreOf 2 M) hj)
    have hp : ⁅J.map (MulAut.conj k).toMonoidHom, J.map (MulAut.conj k).toMonoidHom⁆ =
        J.map (MulAut.conj k).toMonoidHom := by rw [← Subgroup.map_commutator, hJ.2.2.1]
    have h1 := le_of_le_sup_core hJ hp hle
    intro j hj
    exact h1 ⟨j, hj, by simp [MulAut.conj_apply]⟩
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key k hk g, fun hg => ?_⟩
  have h1 := key k⁻¹ (K.inv_mem hk) _ hg
  simpa [mul_assoc] using h1

theorem compSet_conj {M J : Subgroup G} (hJ : Sec12a3.CompSet M J) {g : G} (hg : g ∈ M) :
    Sec12a3.CompSet M (GLBConj g J) := by
  have hM : GLBConj g M = M := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg)
  obtain ⟨hJM, hsn, hperf, hhat⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc GLBConj g J ≤ GLBConj g M := Subgroup.map_mono hJM
      _ = M := hM
  · have h1 := isSubnormal_gLBConj hsn g
    rwa [hM] at h1
  · have h1 := Subgroup.map_commutator (H₁ := J) (H₂ := J) (MulAut.conj g⁻¹).toMonoidHom
    change GLBConj g ⁅J, J⁆ = ⁅GLBConj g J, GLBConj g J⁆ at h1
    rw [← h1, hperf]
  · have hpc : (CFSG.pCore 2 ↥J).map (conjEquiv g J).toMonoidHom = CFSG.pCore 2 ↥(GLBConj g J) :=
      CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (conjEquiv g J)
    exact IsHatSeven.of_mulEquiv (QuotientGroup.congr _ _ (conjEquiv g J) hpc) hhat

end Components

section Action

variable {G : Type} [Group G] [Finite G]

@[expose] def ActTriv (g : G) (J : Subgroup G) : Prop :=
  ∀ y ∈ J, g * y * g⁻¹ * y⁻¹ ∈ pCoreOf 2 J

theorem actTriv_one (J : Subgroup G) : ActTriv 1 J := fun y _ => by
  simp only [one_mul, inv_one, mul_one, mul_inv_cancel]
  exact (pCoreOf 2 J).one_mem

theorem actTriv_mul {J : Subgroup G} {g h : G} (hg : g ∈ Subgroup.normalizer (J : Set G))
    (h1 : ActTriv g J) (h2 : ActTriv h J) : ActTriv (g * h) J := by
  intro y hy
  have hgO := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J hg
  have hc : g * (h * y * h⁻¹ * y⁻¹) * g⁻¹ ∈ pCoreOf 2 J :=
    (Subgroup.mem_normalizer_iff.1 hgO _).1 (h2 y hy)
  have e : g * h * y * (g * h)⁻¹ * y⁻¹ =
      (g * (h * y * h⁻¹ * y⁻¹) * g⁻¹) * (g * y * g⁻¹ * y⁻¹) := by group
  rw [e]
  exact (pCoreOf 2 J).mul_mem hc (h1 y hy)

theorem actTriv_inv {J : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (J : Set G))
    (h1 : ActTriv g J) : ActTriv g⁻¹ J := by
  intro y hy
  have hz : g⁻¹ * y * g⁻¹⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) y).1 hy
  have h2 := h1 _ hz
  have e : g⁻¹ * y * g⁻¹⁻¹ * y⁻¹ =
      (g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ * (g⁻¹ * y * g⁻¹⁻¹)⁻¹)⁻¹ := by group
  rw [e]
  exact inv_mem h2

theorem actTriv_conj {J : Subgroup G} {g r : G} (hgr : g * r = r * g) (h1 : ActTriv g J) :
    ActTriv g (GLBConj r J) := by
  intro y hy
  rw [mem_gLBConj] at hy
  rw [pCoreOf_gLBConj, mem_gLBConj]
  have h2 := h1 _ hy
  have hgr' : r * g * r⁻¹ = g := by rw [← hgr]; group
  have e : r * (g * y * g⁻¹ * y⁻¹) * r⁻¹ =
      (r * g * r⁻¹) * (r * y * r⁻¹) * (r * g * r⁻¹)⁻¹ * (r * y * r⁻¹)⁻¹ := by group
  rw [e, hgr']
  exact h2

theorem sign_commutator (σ p : Perm (Fin 7)) : Perm.sign (σ * p * σ⁻¹ * p⁻¹) = 1 := by
  simp only [Perm.sign_mul, Perm.sign_inv]
  rw [mul_assoc (Perm.sign σ * Perm.sign p), Int.units_mul_self]

theorem a_isThreeCycle : S7.a.IsThreeCycle := card_support_eq_three_iff.1 (by decide)

theorem a_pow_two_pow_ne_one (k : ℕ) : S7.a ^ 2 ^ k ≠ 1 := by
  intro h
  have h1 := orderOf_dvd_of_pow_eq_one h
  rw [a_isThreeCycle.orderOf] at h1
  have h2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
    (Nat.prime_three.dvd_of_dvd_pow h1)
  omega

theorem eq_bot_of_two_subgroup_normalized {P : Subgroup (Perm (Fin 7))} (hP : IsPGroup 2 ↥P)
    (hn : ∀ σ ∈ alternatingGroup (Fin 7), ∀ p ∈ P, σ * p * σ⁻¹ ∈ P) : P = ⊥ := by
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := S7.isSimple_Alt7
  have hN : ((P ⊓ alternatingGroup (Fin 7)).subgroupOf (alternatingGroup (Fin 7))).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨hn _ g.2 _ hx.1, (alternatingGroup (Fin 7)).mul_mem
      ((alternatingGroup (Fin 7)).mul_mem g.2 hx.2) ((alternatingGroup (Fin 7)).inv_mem g.2)⟩
  rcases hN.eq_bot_or_eq_top with h | h
  · rw [eq_bot_iff]
    intro p hp
    rw [Subgroup.mem_bot]
    apply Sec12a3.eq_one_of_centralizes_alt7
    intro σ hσ
    have hc : σ * p * σ⁻¹ * p⁻¹ ∈ P ⊓ alternatingGroup (Fin 7) :=
      ⟨P.mul_mem (hn σ hσ p hp) (P.inv_mem hp),
        Equiv.Perm.mem_alternatingGroup.2 (sign_commutator σ p)⟩
    have h1 : (⟨_, hc.2⟩ : ↥(alternatingGroup (Fin 7))) ∈
        (P ⊓ alternatingGroup (Fin 7)).subgroupOf (alternatingGroup (Fin 7)) :=
      Subgroup.mem_subgroupOf.2 hc
    rw [h, Subgroup.mem_bot] at h1
    have h2 : σ * p * σ⁻¹ * p⁻¹ = 1 := congrArg Subtype.val h1
    calc p * σ = (σ * p * σ⁻¹ * p⁻¹)⁻¹ * (σ * p) := by group
      _ = σ * p := by rw [h2]; group
  · exfalso
    have ha : S7.a ∈ alternatingGroup (Fin 7) := a_isThreeCycle.mem_alternatingGroup
    have h1 : (⟨S7.a, ha⟩ : ↥(alternatingGroup (Fin 7))) ∈
        (P ⊓ alternatingGroup (Fin 7)).subgroupOf (alternatingGroup (Fin 7)) :=
      h ▸ Subgroup.mem_top _
    obtain ⟨k, hk⟩ := hP ⟨S7.a, (Subgroup.mem_subgroupOf.1 h1).1⟩
    exact a_pow_two_pow_ne_one k (congrArg Subtype.val hk)

theorem perm_kill_pCore {D : Type} [Group D] [Finite D] (ρ : D →* Perm (Fin 7))
    (hρS : ∀ σ ∈ alternatingGroup (Fin 7), ∃ d, ρ d = σ) {w : D} (hw : w ∈ CFSG.pCore 2 D) :
    ρ w = 1 := by
  set Q := (CFSG.pCore 2 D).map ρ with hQ
  have hQ2 : IsPGroup 2 ↥Q := CFSG.pCore_isPGroup.map _
  have hQn : ∀ σ ∈ alternatingGroup (Fin 7), ∀ q ∈ Q, σ * q * σ⁻¹ ∈ Q := by
    intro σ hσ q hq
    obtain ⟨x, rfl⟩ := hρS σ hσ
    obtain ⟨w', hw', rfl⟩ := hq
    exact ⟨x * w' * x⁻¹, (CFSG.pCore_normal (p := 2) (G := D)).conj_mem _ hw' x, by
      simp [map_mul, map_inv]⟩
  have hQb := eq_bot_of_two_subgroup_normalized hQ2 hQn
  have h1 : ρ w ∈ Q := Subgroup.mem_map_of_mem _ hw
  rwa [hQb, Subgroup.mem_bot] at h1

theorem psiOf_eq_one_of_mem {J : Subgroup G}
    (ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7)))
    {w : ↥J} (hw : w ∈ CFSG.pCore 2 ↥J) : Sec12a3.psiOf J ι w = 1 :=
  perm_kill_pCore (Sec12a3.psiOf J ι) (Sec12a3.psiOf_surj J ι) hw

theorem mk_mem_center_of_psiOf {J : Subgroup G} (hX : IsHatSeven (Sec12a3.JbarQ J))
    (ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7)))
    {k : ↥J} (hk : Sec12a3.psiOf J ι k = 1) :
    (QuotientGroup.mk k : Sec12a3.JbarQ J) ∈ Subgroup.center (Sec12a3.JbarQ J) := by
  set π₁ := QuotientGroup.mk' (CFSG.pCore 2 ↥J) with hπ₁
  set Z := Subgroup.center (Sec12a3.JbarQ J) with hZ
  set N : Subgroup (Sec12a3.JbarQ J) := (Sec12a3.psiOf J ι).ker.map π₁ with hN
  haveI hNn : N.Normal := (MonoidHom.normal_ker _).map π₁ (QuotientGroup.mk'_surjective _)
  haveI : IsSimpleGroup (Sec12a3.JbarQ J ⧸ Z) := by
    haveI : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := S7.isSimple_Alt7
    exact ι.isSimpleGroup
  have hNm : (N.map (QuotientGroup.mk' Z)).Normal := hNn.map _ (QuotientGroup.mk'_surjective _)
  have hkN : (QuotientGroup.mk k : Sec12a3.JbarQ J) ∈ N := ⟨k, hk, rfl⟩
  rcases hNm.eq_bot_or_eq_top with h | h
  · have h1 : QuotientGroup.mk' Z (QuotientGroup.mk k) = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.mem_map_of_mem _ hkN
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  · exfalso
    have hdec : ∀ x : Sec12a3.JbarQ J, ∃ n ∈ N, n⁻¹ * x ∈ Z := fun x => by
      have hx : QuotientGroup.mk' Z x ∈ N.map (QuotientGroup.mk' Z) := by
        rw [h]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := hx
      exact ⟨n, hn, QuotientGroup.eq.1 hnx⟩
    have hle : ⁅(⊤ : Subgroup (Sec12a3.JbarQ J)), ⊤⁆ ≤ N := by
      refine Subgroup.commutator_le.2 fun x _ y _ => ?_
      obtain ⟨n, hn, hzx⟩ := hdec x
      obtain ⟨m, hm, hzy⟩ := hdec y
      have hx : x = n * (n⁻¹ * x) := by group
      have hy : y = m * (m⁻¹ * y) := by group
      rw [hx, hy, Sec12a4.commutatorElement_mul_central_left hzx,
        Sec12a4.commutatorElement_mul_central_right hzy, commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem hn hm) (N.inv_mem hn)) (N.inv_mem hm)
    have htop : N = ⊤ := top_le_iff.1 (hX.1.symm.le.trans hle)
    obtain ⟨x, hx⟩ := Sec12a3.psiOf_surj J ι S7.a a_isThreeCycle.mem_alternatingGroup
    have hxN : π₁ x ∈ N := htop ▸ Subgroup.mem_top _
    obtain ⟨n, hn, hnx⟩ := hxN
    have h1 : n⁻¹ * x ∈ CFSG.pCore 2 ↥J := QuotientGroup.eq.1 hnx
    have h2 := psiOf_eq_one_of_mem ι h1
    rw [map_mul, map_inv, MonoidHom.mem_ker.1 hn, inv_one, one_mul, hx] at h2
    exact a_pow_two_pow_ne_one 0 (by simpa using h2)

@[expose] def IsConj (J : Subgroup G)
    (ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7)))
    (g : G) (π : Perm (Fin 7)) : Prop :=
  ∀ x y : ↥J, (y : G) = g * x * g⁻¹ → Sec12a3.psiOf J ι y = π * Sec12a3.psiOf J ι x * π⁻¹

theorem isConj_of_conjsBy {J : Subgroup G}
    {ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7))}
    {g : G} {π : Perm (Fin 7)} (hg : g ∈ Subgroup.normalizer (J : Set G))
    (h : Sec12a3.ConjsBy J ι g π) : IsConj J ι g π := by
  intro x y hxy
  obtain ⟨y', hy', hψ⟩ := Sec12a3.conjsBy_pow J ι g π
    (fun z hz => (Subgroup.mem_normalizer_iff.1 hg z).1 hz) h 1 x
  have e : y = y' := Subtype.ext (by rw [hxy, hy']; simp)
  rw [e, hψ]
  simp

theorem isConj_unique {J : Subgroup G}
    {ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7))}
    {g : G} (hg : g ∈ Subgroup.normalizer (J : Set G)) {π σ : Perm (Fin 7)}
    (hπ : IsConj J ι g π) (hσ : IsConj J ι g σ) : π = σ := by
  have key : ∀ τ ∈ alternatingGroup (Fin 7), (σ⁻¹ * π) * τ = τ * (σ⁻¹ * π) := by
    intro τ hτ
    obtain ⟨x, rfl⟩ := Sec12a3.psiOf_surj J ι τ hτ
    have hy : g * (x : G) * g⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hg x).1 x.2
    have h1 := hπ x ⟨_, hy⟩ rfl
    have h2 := hσ x ⟨_, hy⟩ rfl
    rw [h1] at h2
    calc σ⁻¹ * π * Sec12a3.psiOf J ι x
        = σ⁻¹ * (π * Sec12a3.psiOf J ι x * π⁻¹) * π := by group
      _ = σ⁻¹ * (σ * Sec12a3.psiOf J ι x * σ⁻¹) * π := by rw [h2]
      _ = Sec12a3.psiOf J ι x * (σ⁻¹ * π) := by group
  have h1 := Sec12a3.eq_one_of_centralizes_alt7 key
  rw [inv_mul_eq_one] at h1
  exact h1.symm

theorem conjsBy_of_isConj {J : Subgroup G}
    {ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7))}
    {g : G} {π : Perm (Fin 7)} (hg : g ∈ Subgroup.normalizer (J : Set G))
    (h : IsConj J ι g π) : Sec12a3.ConjsBy J ι g π := by
  obtain ⟨π₀, h₀⟩ := Sec12a3.exists_perm_conjsBy J ι g hg
  have e := isConj_unique hg (isConj_of_conjsBy hg h₀) h
  rwa [e] at h₀

theorem exists_isConj {J : Subgroup G}
    (ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7)))
    {g : G} (hg : g ∈ Subgroup.normalizer (J : Set G)) : ∃ π, IsConj J ι g π := by
  obtain ⟨π₀, h₀⟩ := Sec12a3.exists_perm_conjsBy J ι g hg
  exact ⟨π₀, isConj_of_conjsBy hg h₀⟩

theorem isConj_mul {J : Subgroup G}
    {ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7))}
    {g h : G} {π σ : Perm (Fin 7)} (hh : h ∈ Subgroup.normalizer (J : Set G))
    (hπ : IsConj J ι g π) (hσ : IsConj J ι h σ) : IsConj J ι (g * h) (π * σ) := by
  intro x y hxy
  have hw : h * (x : G) * h⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hh x).1 x.2
  have h1 := hσ x ⟨_, hw⟩ rfl
  have h2 := hπ ⟨_, hw⟩ y (by rw [hxy]; group)
  rw [h2, h1]
  group

theorem isConj_of_mem {J : Subgroup G}
    (ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7)))
    (y : ↥J) : IsConj J ι y (Sec12a3.psiOf J ι y) := by
  intro x z hxz
  have e : z = y * x * y⁻¹ := Subtype.ext (by simp [hxz])
  rw [e, map_mul, map_inv, map_mul]

theorem actTriv_of_isConj_one {J : Subgroup G} (hX : IsHatSeven (Sec12a3.JbarQ J))
    (ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7)))
    {g : G} (hg : g ∈ Subgroup.normalizer (J : Set G)) (h1 : IsConj J ι g 1) :
    ActTriv g J := by
  set φ : MulAut ↥J := (Subgroup.normalizerMonoidHom J) ⟨g, hg⟩ with hφ
  have hφapp : ∀ x : ↥J, ((φ x : ↥J) : G) = g * (x : G) * g⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe J ⟨g, hg⟩ x
  have hpc : (CFSG.pCore 2 ↥J).map φ.toMonoidHom = CFSG.pCore 2 ↥J := by
    have h := (CFSG.pCore_characteristic (p := 2) (G := ↥J)).fixed φ.symm
    ext x
    rw [Subgroup.mem_map_equiv]
    have h2 := SetLike.ext_iff.1 h x
    simpa [Subgroup.mem_comap] using h2
  set Φ : Sec12a3.JbarQ J ≃* Sec12a3.JbarQ J :=
    QuotientGroup.congr (CFSG.pCore 2 ↥J) (CFSG.pCore 2 ↥J) φ hpc with hΦdef
  have hΦ : ∀ x : ↥J, Φ (QuotientGroup.mk x) = QuotientGroup.mk (φ x) := fun x =>
    QuotientGroup.congr_mk _ _ φ hpc x
  have hcen : ∀ x : Sec12a3.JbarQ J, x⁻¹ * Φ x ∈ Subgroup.center (Sec12a3.JbarQ J) := by
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hΦ]
    have hψ : Sec12a3.psiOf J ι (x⁻¹ * φ x) = 1 := by
      have h2 := h1 x (φ x) (hφapp x)
      rw [map_mul, map_inv, h2]
      group
    have h3 := mk_mem_center_of_psiOf hX ι hψ
    simpa using h3
  let S : Subgroup (Sec12a3.JbarQ J) :=
    { carrier := {x | Φ x = x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul] at ha hb ⊢
        rw [ha, hb]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, map_inv] at ha ⊢
        rw [ha] }
  have hS : ⁅(⊤ : Subgroup (Sec12a3.JbarQ J)), ⊤⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    show Φ ⁅x, y⁆ = ⁅x, y⁆
    rw [map_commutatorElement]
    have hx : Φ x = x * (x⁻¹ * Φ x) := by group
    have hy : Φ y = y * (y⁻¹ * Φ y) := by group
    rw [hx, hy, Sec12a4.commutatorElement_mul_central_left (hcen x),
      Sec12a4.commutatorElement_mul_central_right (hcen y)]
  have htop : S = ⊤ := top_le_iff.1 (hX.1.symm.le.trans hS)
  intro y hy
  have hfix : Φ (QuotientGroup.mk ⟨y, hy⟩) = QuotientGroup.mk ⟨y, hy⟩ := by
    have h2 : (QuotientGroup.mk ⟨y, hy⟩ : Sec12a3.JbarQ J) ∈ S := htop ▸ Subgroup.mem_top _
    exact h2
  rw [hΦ, QuotientGroup.eq_iff_div_mem] at hfix
  refine ⟨_, hfix, ?_⟩
  simp [div_eq_mul_inv, hφapp]

theorem isConj_one_of_actTriv {J : Subgroup G}
    (ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7)))
    {g : G} (h : ActTriv g J) : IsConj J ι g 1 := by
  intro x y hxy
  have hy : (y : G) * (x : G)⁻¹ ∈ pCoreOf 2 J := by
    have h2 := h x x.2
    rw [← hxy] at h2
    exact h2
  obtain ⟨w, hw, hwe⟩ := hy
  have hwe' : (w : G) = y * (x : G)⁻¹ := hwe
  have e : y = w * x := Subtype.ext (by rw [Subgroup.coe_mul, hwe']; group)
  rw [e, map_mul, psiOf_eq_one_of_mem ι hw]
  simp

noncomputable def permHom (J : Subgroup G)
    (ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7))) :
    ↥(Subgroup.normalizer (J : Set G)) →* Perm (Fin 7) where
  toFun g := Classical.choose (exists_isConj ι g.2)
  map_one' := isConj_unique (Subgroup.one_mem _)
    (Classical.choose_spec (exists_isConj ι (1 : ↥(Subgroup.normalizer (J : Set G))).2))
    (isConj_one_of_actTriv ι (actTriv_one J))
  map_mul' g h := isConj_unique (g * h).2 (Classical.choose_spec (exists_isConj ι (g * h).2))
    (isConj_mul h.2 (Classical.choose_spec (exists_isConj ι g.2))
      (Classical.choose_spec (exists_isConj ι h.2)))

theorem permHom_spec (J : Subgroup G)
    (ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7)))
    (g : ↥(Subgroup.normalizer (J : Set G))) : IsConj J ι g (permHom J ι g) :=
  Classical.choose_spec (exists_isConj ι g.2)

theorem permHom_eq {J : Subgroup G}
    {ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7))}
    (g : ↥(Subgroup.normalizer (J : Set G))) {π : Perm (Fin 7)} (h : IsConj J ι g π) :
    permHom J ι g = π :=
  isConj_unique g.2 (permHom_spec J ι g) h

theorem actTriv_iff_permHom {J : Subgroup G} (hX : IsHatSeven (Sec12a3.JbarQ J))
    (ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7)))
    (g : ↥(Subgroup.normalizer (J : Set G))) : ActTriv (g : G) J ↔ permHom J ι g = 1 :=
  ⟨fun h => permHom_eq g (isConj_one_of_actTriv ι h),
    fun h => actTriv_of_isConj_one hX ι g.2 (h ▸ permHom_spec J ι g)⟩

end Action

section TofBasic

variable {G : Type} [Group G] [Finite G]

theorem zpowers_isPGroup_three {a : G} (ha3 : a ^ 3 = 1) : IsPGroup 3 ↥(Subgroup.zpowers a) := by
  rintro ⟨g, hg⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]

theorem not_three_dvd_of_two {V : Subgroup G} (hV : IsPGroup 2 ↥V) : ¬ 3 ∣ Nat.card ↥V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hV
  rw [hn]
  intro h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
    (Nat.prime_three.dvd_of_dvd_pow h)
  omega

theorem actTriv_of_mem_core {M J : Subgroup G} (hJ : Sec12a3.CompSet M J) {o : G}
    (ho : o ∈ pCoreOf 2 M) : ActTriv o J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro y hy
  have h1 : o * y * o⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 (core_le_normalizer hJ ho) y).1 hy
  have h2 : o * y * o⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
    have h3 : y * o⁻¹ * y⁻¹ ∈ pCoreOf 2 M := (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hJ.1 hy)) _).1 (inv_mem ho)
    have h4 := (pCoreOf 2 M).mul_mem ho h3
    simpa [mul_assoc] using h4
  rw [← inf_pCoreOf_eq_of_isSubnormal 2 hJ.2.1 hJ.1]
  exact ⟨J.mul_mem h1 (J.inv_mem hy), h2⟩

theorem actTriv_of_mem_other {M J K : Subgroup G} (hJ : Sec12a3.CompSet M J)
    (hK : Sec12a3.CompSet M K) (hne : K ≠ J) {k : G} (hk : k ∈ K) : ActTriv k J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro y hy
  have h1 : k * y * k⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1
    (alpha_le_normalizer hJ (Sec12a3.compSet_le_alpha hK hk)) y).1 hy
  rw [← inf_pCoreOf_eq_of_isSubnormal 2 hJ.2.1 hJ.1]
  exact ⟨J.mul_mem h1 (J.inv_mem hy), comm_mem_core hK hJ hne hk hy⟩

theorem permHom_mem_alt {M J : Subgroup G} (hJ : Sec12a3.CompSet M J)
    (ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7)))
    {g : G} (hg : g ∈ alphaOf 3 M) :
    permHom J ι ⟨g, alpha_le_normalizer hJ hg⟩ ∈ alternatingGroup (Fin 7) := by
  let S : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ Subgroup.normalizer (J : Set G),
        permHom J ι ⟨g, hg⟩ ∈ alternatingGroup (Fin 7)}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
        have e : (⟨a * b, Subgroup.mul_mem _ ha hb⟩ : ↥(Subgroup.normalizer (J : Set G))) =
            ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
        rw [e, map_mul]
        exact Subgroup.mul_mem _ ha' hb'
      one_mem' := ⟨Subgroup.one_mem _, by
        have e : (⟨1, Subgroup.one_mem _⟩ : ↥(Subgroup.normalizer (J : Set G))) = 1 := rfl
        rw [e, map_one]
        exact Subgroup.one_mem _⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, ?_⟩
        have e : (⟨a⁻¹, Subgroup.inv_mem _ ha⟩ : ↥(Subgroup.normalizer (J : Set G))) =
            (⟨a, ha⟩)⁻¹ := rfl
        rw [e, map_inv]
        exact Subgroup.inv_mem _ ha' }
  have hαS : alphaOf 3 M ≤ S := by
    unfold alphaOf
    refine sup_le ?_ (iSup₂_le fun K hK => ?_)
    · intro o ho
      refine ⟨core_le_normalizer hJ ho, ?_⟩
      rw [permHom_eq _ (isConj_one_of_actTriv ι (actTriv_of_mem_core hJ ho))]
      exact Subgroup.one_mem _
    · have hKc : Sec12a3.CompSet M K := ⟨hK.2.1, hK.2.2.1, hK.2.2.2.1, hK.2.2.2.2⟩
      intro k hk
      refine ⟨alpha_le_normalizer hJ (Sec12a3.compSet_le_alpha hKc hk), ?_⟩
      by_cases hKJ : K = J
      · subst hKJ
        rw [permHom_eq _ (isConj_of_mem ι ⟨k, hk⟩)]
        exact Sec12a3.psiOf_mem_alt _ ι _
      · rw [permHom_eq _ (isConj_one_of_actTriv ι (actTriv_of_mem_other hJ hKc hKJ hk))]
        exact Subgroup.one_mem _
  obtain ⟨_, h⟩ := hαS hg
  exact h

theorem inv_eq_mul_self {a : G} (ha3 : a ^ 3 = 1) : a⁻¹ = a * a :=
  inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ← pow_three', ha3])

end TofBasic

section General

variable {G : Type} [Group G] [Finite G]

theorem exists_derivedSeries_stable (X : Type*) [Group X] [Finite X] :
    ∃ n : ℕ, derivedSeries X (n + 1) = derivedSeries X n := by
  by_contra h
  push Not at h
  have key : ∀ n : ℕ, Nat.card (derivedSeries X n) + n ≤ Nat.card X := by
    intro n
    induction n with
    | zero => rw [derivedSeries_zero, Subgroup.card_top, add_zero]
    | succ n ih =>
      have hle : derivedSeries X (n + 1) ≤ derivedSeries X n :=
        derivedSeries_antitone X (Nat.le_succ n)
      have hlt : Nat.card (derivedSeries X (n + 1)) < Nat.card (derivedSeries X n) :=
        Subgroup.card_lt_of_lt (lt_of_le_of_ne hle (h n))
      omega
  have h1 := key (Nat.card X)
  have h2 := Nat.card_pos (α := derivedSeries X (Nat.card X))
  omega

theorem derivedSeries_alt7 (n : ℕ) : derivedSeries ↥(alternatingGroup (Fin 7)) n = ⊤ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [derivedSeries_succ, ih, ← commutator_def, commutator_alternatingGroup_eq_top (by simp)]

def modCent (M : Subgroup G) (w : G) : Subgroup G where
  carrier := {g | g ∈ M ∧ w * g * w⁻¹ * g⁻¹ ∈ pCoreOf 2 M}
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨M.mul_mem hx hy, ?_⟩
    have h1 : x * (w * y * w⁻¹ * y⁻¹) * x⁻¹ ∈ pCoreOf 2 M :=
      (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hx) _).1 hy'
    have e : w * (x * y) * w⁻¹ * (x * y)⁻¹ =
        (w * x * w⁻¹ * x⁻¹) * (x * (w * y * w⁻¹ * y⁻¹) * x⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 M).mul_mem hx' h1
  one_mem' := ⟨M.one_mem, by simp⟩
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨M.inv_mem hx, ?_⟩
    have h1 : x⁻¹ * (w * x * w⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ ∈ pCoreOf 2 M :=
      (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
        (M.inv_mem hx)) _).1 (inv_mem hx')
    have e : w * x⁻¹ * w⁻¹ * x⁻¹⁻¹ = x⁻¹ * (w * x * w⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact h1

def actTrivSub (J : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (J : Set G) ∧ ActTriv g J}
  mul_mem' := fun {x y} hx hy => ⟨Subgroup.mul_mem _ hx.1 hy.1, actTriv_mul hx.1 hx.2 hy.2⟩
  one_mem' := ⟨Subgroup.one_mem _, actTriv_one J⟩
  inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, actTriv_inv hx.1 hx.2⟩

@[expose] def orbitProd (M J₀ : Subgroup G) (X : Set G) : Subgroup G :=
  (⨆ (x : G) (_ : x ∈ X), GLBConj x J₀) ⊔ pCoreOf 2 M

theorem le_orbitProd {M J₀ : Subgroup G} {X : Set G} {x : G} (hx : x ∈ X) :
    GLBConj x J₀ ≤ orbitProd M J₀ X :=
  (le_iSup₂_of_le (f := fun (x : G) (_ : x ∈ X) => GLBConj x J₀) x hx le_rfl).trans le_sup_left

theorem core_le_orbitProd (M J₀ : Subgroup G) (X : Set G) : pCoreOf 2 M ≤ orbitProd M J₀ X :=
  le_sup_right

theorem orbitProd_le_alpha {M J₀ : Subgroup G} (hJ₀ : Sec12a3.CompSet M J₀) {X : Set G}
    (hXM : X ⊆ M) : orbitProd M J₀ X ≤ alphaOf 3 M :=
  sup_le (iSup₂_le fun x hx => Sec12a3.compSet_le_alpha (compSet_conj hJ₀ (hXM hx)))
    (Sec12a.le_alphaOf_two M)

theorem actTriv_of_mem_orbitProd {M J₀ Y : Subgroup G} (hJ₀ : Sec12a3.CompSet M J₀)
    (hY : Sec12a3.CompSet M Y) {X : Set G} (hXM : X ⊆ M) (hYX : ∀ x ∈ X, GLBConj x J₀ ≠ Y)
    {g : G} (hg : g ∈ orbitProd M J₀ X) : ActTriv g Y := by
  have hle : orbitProd M J₀ X ≤ actTrivSub Y := by
    refine sup_le (iSup₂_le fun x hx => ?_) ?_
    · intro k hk
      have hc := compSet_conj hJ₀ (hXM hx)
      exact ⟨alpha_le_normalizer hY (Sec12a3.compSet_le_alpha hc hk),
        actTriv_of_mem_other hY hc (hYX x hx) hk⟩
    · intro o ho
      exact ⟨core_le_normalizer hY ho, actTriv_of_mem_core hY ho⟩
  exact (hle hg).2

theorem comm_core_of_mem_orbitProd {M J₀ : Subgroup G} (hJ₀ : Sec12a3.CompSet M J₀)
    {X : Set G} (hXM : X ⊆ M) {w : G} (hwM : w ∈ M) (h : ∀ x ∈ X, ActTriv w (GLBConj x J₀))
    {g : G} (hg : g ∈ orbitProd M J₀ X) : w * g * w⁻¹ * g⁻¹ ∈ pCoreOf 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : orbitProd M J₀ X ≤ modCent M w := by
    refine sup_le (iSup₂_le fun x hx => ?_) ?_
    · intro k hk
      have hc := compSet_conj hJ₀ (hXM hx)
      exact ⟨hc.1 hk, pCoreOf_le_of_isSubnormal 2 hc.2.1 (h x hx k hk)⟩
    · intro o ho
      refine ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 M ho, ?_⟩
      have h1 : w * o * w⁻¹ ∈ pCoreOf 2 M := (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hwM) o).1 ho
      exact (pCoreOf 2 M).mul_mem h1 (inv_mem ho)
  exact (hle hg).2

end General

section Diagonal

variable {G : Type} [Group G] [Finite G]

structure DiagData (M J₀ R : Subgroup G) : Prop where
  comp : Sec12a3.CompSet M J₀
  le : R ≤ M
  pow3 : ∀ r ∈ R, r ^ 3 = 1
  comm : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r
  triv : ∀ r ∈ R, r ∈ Subgroup.normalizer (J₀ : Set G) → ActTriv r J₀

theorem isPGroup_three_of_pow3 {S : Subgroup G} (h : ∀ r ∈ S, r ^ 3 = 1) : IsPGroup 3 ↥S :=
  fun g => ⟨1, Subtype.ext (by simpa using h g g.2)⟩

@[expose] def DiagSurj (M J₀ : Subgroup G)
    (ι : (Sec12a3.JbarQ J₀ ⧸ Subgroup.center (Sec12a3.JbarQ J₀)) ≃* ↥(alternatingGroup (Fin 7)))
    (S : Subgroup G) : Prop :=
  ∀ σ ∈ alternatingGroup (Fin 7), ∃ z ∈ orbitProd M J₀ (S : Set G) ⊓
    Subgroup.centralizer (S : Set G), ∃ hz : z ∈ Subgroup.normalizer (J₀ : Set G),
      permHom J₀ ι ⟨z, hz⟩ = σ

omit [Finite G] in
theorem gLBConj_eq_imp {J₀ : Subgroup G} {u v : G} (h : GLBConj u J₀ = GLBConj v J₀) :
    u * v⁻¹ ∈ Subgroup.normalizer (J₀ : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  have h1 := congrArg (GLBConj v⁻¹) h
  rw [gLBConj_gLBConj, gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] at h1
  exact h1

theorem orbitProd_mono {M J₀ : Subgroup G} {X X' : Set G} (h : X ⊆ X') :
    orbitProd M J₀ X ≤ orbitProd M J₀ X' :=
  sup_le_sup_right (iSup₂_le fun x hx => le_iSup₂_of_le (f := fun (x : G) (_ : x ∈ X') =>
    GLBConj x J₀) x (h hx) le_rfl) _

theorem gLBConj_orbitProd_le {M J₀ : Subgroup G} {b : G} (hbM : b ∈ M) (X : Set G) :
    GLBConj b (orbitProd M J₀ X) ≤ orbitProd M J₀ ((fun x => x * b) '' X) := by
  unfold orbitProd GLBConj
  rw [Subgroup.map_sup, Subgroup.map_iSup]
  refine sup_le (iSup_le fun x => ?_) ?_
  · rw [Subgroup.map_iSup]
    refine iSup_le fun hx => ?_
    change GLBConj b (GLBConj x J₀) ≤ _
    rw [gLBConj_gLBConj]
    exact le_orbitProd ⟨x, hx, rfl⟩
  · change GLBConj b (pCoreOf 2 M) ≤ _
    rw [gLBConj_eq_of_mem_normalizer (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hbM)]
    exact core_le_orbitProd _ _ _

theorem diagSurj_base {M J₀ R : Subgroup G} (hD : DiagData M J₀ R)
    (ι : (Sec12a3.JbarQ J₀ ⧸ Subgroup.center (Sec12a3.JbarQ J₀)) ≃* ↥(alternatingGroup (Fin 7))) :
    DiagSurj M J₀ ι (R ⊓ Subgroup.normalizer (J₀ : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro σ hσ
  obtain ⟨y, rfl⟩ := Sec12a3.psiOf_surj J₀ ι σ hσ
  obtain ⟨v, hv, hfix⟩ := exists_fixed_in_coset' (p := 3)
    (U := R ⊓ Subgroup.normalizer (J₀ : Set G)) (V := pCoreOf 2 J₀)
    (isPGroup_three_of_pow3 fun r hr => hD.pow3 r hr.1)
    (not_three_dvd_of_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J₀))
    (fun r hr => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J₀ hr.2)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J₀ y.2)
    (fun r hr => hD.triv r hr.1 hr.2 y y.2)
  obtain ⟨v', hv', rfl⟩ := hv
  have hz : (y : G) * v' ∈ J₀ := J₀.mul_mem y.2 v'.2
  refine ⟨(y : G) * v', Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_iff.2 ?_⟩,
    Subgroup.le_normalizer hz, ?_⟩
  · have h1 : GLBConj (1 : G) J₀ ≤ orbitProd M J₀
        ((R ⊓ Subgroup.normalizer (J₀ : Set G) : Subgroup G) : Set G) :=
      le_orbitProd (Subgroup.one_mem _)
    rw [gLBConj_one] at h1
    exact h1 hz
  · intro r hr
    have h1 : r * ((y : G) * v') * r⁻¹ = (y : G) * v' := hfix r hr
    calc r * ((y : G) * v') = (r * ((y : G) * v') * r⁻¹) * r := by group
      _ = ((y : G) * v') * r := by rw [h1]
  · rw [permHom_eq _ (isConj_of_mem ι (y * v'))]
    rw [map_mul, psiOf_eq_one_of_mem ι hv', mul_one]

theorem diagSurj_step {M J₀ R : Subgroup G} (hD : DiagData M J₀ R)
    (ι : (Sec12a3.JbarQ J₀ ⧸ Subgroup.center (Sec12a3.JbarQ J₀)) ≃* ↥(alternatingGroup (Fin 7)))
    {S : Subgroup G} (hSR : S ≤ R) (hR₀ : R ⊓ Subgroup.normalizer (J₀ : Set G) ≤ S) {b : G}
    (hbR : b ∈ R) (hbS : b ∉ S) (hQ : DiagSurj M J₀ ι S) :
    DiagSurj M J₀ ι (S ⊔ Subgroup.zpowers b) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ₀ := hD.comp
  have hbM : b ∈ M := hD.le hbR
  have hb3 : b ^ 3 = 1 := hD.pow3 b hbR
  have hbb := inv_eq_mul_self hb3
  have hSM : (S : Set G) ⊆ M := fun x hx => hD.le (hSR hx)
  have hbcomm : ∀ x ∈ S, x * b = b * x := fun x hx => hD.comm x (hSR hx) b hbR
  set U : Subgroup G := S ⊔ Subgroup.zpowers b with hU
  have hUR : U ≤ R := sup_le hSR ((Subgroup.zpowers_le).2 hbR)
  have hUM : (U : Set G) ⊆ M := fun x hx => hD.le (hUR hx)
  set X₁ : Set G := (fun x => x * b) '' (S : Set G) with hX₁
  set X₂ : Set G := (fun x => x * b⁻¹) '' (S : Set G) with hX₂
  have hbU : b ∈ U := (le_sup_right : Subgroup.zpowers b ≤ U) (Subgroup.mem_zpowers b)
  have hX₁U : X₁ ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact U.mul_mem ((le_sup_left : S ≤ U) hx) hbU
  have hX₂U : X₂ ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact U.mul_mem ((le_sup_left : S ≤ U) hx) (U.inv_mem hbU)
  have hX₁M : X₁ ⊆ M := hX₁U.trans hUM
  have hX₂M : X₂ ⊆ M := hX₂U.trans hUM
  have key : ∀ u v : G, u ∈ R → v ∈ R → GLBConj u J₀ = GLBConj v J₀ → u * v⁻¹ ∈ S :=
    fun u v hu hv h => hR₀ ⟨R.mul_mem hu (R.inv_mem hv), gLBConj_eq_imp h⟩
  have d01 : ∀ x ∈ (S : Set G), ∀ y ∈ X₁, GLBConj x J₀ ≠ GLBConj y J₀ := by
    rintro x hx _ ⟨y, hy, rfl⟩ h
    apply hbS
    have h1 := key _ _ (hSR hx) (R.mul_mem (hSR hy) hbR) h
    have e : (x * (y * b)⁻¹)⁻¹ * x * y⁻¹ = b := by
      calc (x * (y * b)⁻¹)⁻¹ * x * y⁻¹ = y * b * y⁻¹ := by group
        _ = b := by rw [hbcomm y hy]; group
    rw [← e]
    exact S.mul_mem (S.mul_mem (S.inv_mem h1) hx) (S.inv_mem hy)
  have d02 : ∀ x ∈ (S : Set G), ∀ y ∈ X₂, GLBConj x J₀ ≠ GLBConj y J₀ := by
    rintro x hx _ ⟨y, hy, rfl⟩ h
    apply hbS
    have h1 := key _ _ (hSR hx) (R.mul_mem (hSR hy) (R.inv_mem hbR)) h
    have e : x⁻¹ * (x * (y * b⁻¹)⁻¹) * y = b := by group
    rw [← e]
    exact S.mul_mem (S.mul_mem (S.inv_mem hx) h1) hy
  have d12 : ∀ x ∈ X₂, ∀ y ∈ X₁, GLBConj x J₀ ≠ GLBConj y J₀ := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ h
    apply hbS
    have h1 := key _ _ (R.mul_mem (hSR hx) (R.inv_mem hbR)) (R.mul_mem (hSR hy) hbR) h
    have h2 : b⁻¹ * b⁻¹ ∈ S := by
      have e : x⁻¹ * (x * b⁻¹ * (y * b)⁻¹) * y = b⁻¹ * b⁻¹ := by
        calc x⁻¹ * (x * b⁻¹ * (y * b)⁻¹) * y = b⁻¹ * (b⁻¹ * y⁻¹) * y := by group
          _ = b⁻¹ * b⁻¹ := by group
      rw [← e]
      exact S.mul_mem (S.mul_mem (S.inv_mem hx) h1) hy
    have e : (b⁻¹ * b⁻¹) * (b⁻¹ * b⁻¹) = b⁻¹ := by
      have e1 : (b⁻¹ * b⁻¹) * (b⁻¹ * b⁻¹) = b⁻¹ * (b ^ 3)⁻¹ := by group
      rw [e1, hb3, inv_one, mul_one]
    have h3 : b⁻¹ ∈ S := by rw [← e]; exact S.mul_mem h2 h2
    simpa using S.inv_mem h3
  intro σ hσ
  obtain ⟨z, hzKC, hzN, hzσ⟩ := hQ σ hσ
  obtain ⟨hzK, hzC⟩ := Subgroup.mem_inf.1 hzKC
  have hzM : z ∈ M := (orbitProd_le_alpha hJ₀ hSM).trans (Sec12a.alphaOf_le_self M) hzK
  have hz₁K : b⁻¹ * z * b ∈ orbitProd M J₀ X₁ :=
    gLBConj_orbitProd_le hbM (S : Set G) (mem_gLBConj.2 (by group; exact hzK))
  have hz₂K : b * z * b⁻¹ ∈ orbitProd M J₀ X₂ :=
    gLBConj_orbitProd_le (inv_mem hbM) (S : Set G) (mem_gLBConj.2 (by group; exact hzK))
  have t01 : ∀ y ∈ X₁, ActTriv z (GLBConj y J₀) := fun y hy =>
    actTriv_of_mem_orbitProd hJ₀ (compSet_conj hJ₀ (hX₁M hy)) hSM (fun x hx => d01 x hx y hy) hzK
  have t02 : ∀ y ∈ X₂, ActTriv z (GLBConj y J₀) := fun y hy =>
    actTriv_of_mem_orbitProd hJ₀ (compSet_conj hJ₀ (hX₂M hy)) hSM (fun x hx => d02 x hx y hy) hzK
  have t21 : ∀ y ∈ X₁, ActTriv (b * z * b⁻¹) (GLBConj y J₀) := fun y hy =>
    actTriv_of_mem_orbitProd hJ₀ (compSet_conj hJ₀ (hX₁M hy)) hX₂M (fun x hx => d12 x hx y hy)
      hz₂K
  have h1S : (1 : G) ∈ (S : Set G) := S.one_mem
  have t10 : ActTriv (b⁻¹ * z * b) J₀ := by
    have h1 := actTriv_of_mem_orbitProd hJ₀ hJ₀ hX₁M (fun y hy h => d01 1 h1S y hy
      (by rw [gLBConj_one]; exact h.symm)) hz₁K
    exact h1
  have t20 : ActTriv (b * z * b⁻¹) J₀ :=
    actTriv_of_mem_orbitProd hJ₀ hJ₀ hX₂M (fun y hy h => d02 1 h1S y hy
      (by rw [gLBConj_one]; exact h.symm)) hz₂K
  have c1 : (b * z * b⁻¹) * z * (b * z * b⁻¹)⁻¹ * z⁻¹ ∈ pCoreOf 2 M := by
    have h1 := comm_core_of_mem_orbitProd hJ₀ hX₂M hzM t02 hz₂K
    have e : (b * z * b⁻¹) * z * (b * z * b⁻¹)⁻¹ * z⁻¹ =
        (z * (b * z * b⁻¹) * z⁻¹ * (b * z * b⁻¹)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1
  have c2 : (b * z * b⁻¹) * (b⁻¹ * z * b) * (b * z * b⁻¹)⁻¹ * (b⁻¹ * z * b)⁻¹ ∈ pCoreOf 2 M :=
    comm_core_of_mem_orbitProd hJ₀ hX₁M (M.mul_mem (M.mul_mem hbM hzM) (inv_mem hbM)) t21 hz₁K
  set d : G := z * (b⁻¹ * z * b) * (b * z * b⁻¹) with hd
  have hdM : d ∈ M := M.mul_mem (M.mul_mem hzM (M.mul_mem (M.mul_mem (inv_mem hbM) hzM) hbM))
    (M.mul_mem (M.mul_mem hbM hzM) (inv_mem hbM))
  have hbd : b * d * b⁻¹ * d⁻¹ ∈ pCoreOf 2 M := by
    have e1 : b * d * b⁻¹ = (b * z * b⁻¹) * z * ((b * b) * z * (b * b)⁻¹) := by rw [hd]; group
    rw [← hbb, inv_inv] at e1
    have hzO : z * ((b * z * b⁻¹) * (b⁻¹ * z * b) * (b * z * b⁻¹)⁻¹ * (b⁻¹ * z * b)⁻¹) * z⁻¹ ∈
        pCoreOf 2 M :=
      (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hzM) _).1 c2
    have e2 : (b * z * b⁻¹) * z * (b⁻¹ * z * b) * d⁻¹ =
        ((b * z * b⁻¹) * z * (b * z * b⁻¹)⁻¹ * z⁻¹) *
          (z * ((b * z * b⁻¹) * (b⁻¹ * z * b) * (b * z * b⁻¹)⁻¹ * (b⁻¹ * z * b)⁻¹) * z⁻¹) := by
      rw [hd]; group
    rw [e1, e2]
    exact (pCoreOf 2 M).mul_mem c1 hzO
  have hzc : ∀ x ∈ S, x * z = z * x := fun x hx => (Subgroup.mem_centralizer_iff.1 hzC) x hx
  have hdC : ∀ x ∈ S, x * d = d * x := by
    intro x hx
    have cb : Commute x b := hbcomm x hx
    have cz : Commute x z := hzc x hx
    have c1 : Commute x (b⁻¹ * z * b) := (cb.inv_right.mul_right cz).mul_right cb
    have c2 : Commute x (b * z * b⁻¹) := (cb.mul_right cz).mul_right cb.inv_right
    exact ((cz.mul_right c1).mul_right c2).eq
  have hUmc : U ≤ modCent M d := by
    refine sup_le (fun x hx => ⟨hSM hx, ?_⟩) ((Subgroup.zpowers_le).2 ⟨hbM, ?_⟩)
    · rw [show d * x * d⁻¹ * x⁻¹ = 1 by rw [← hdC x hx]; group]
      exact one_mem _
    · have e : d * b * d⁻¹ * b⁻¹ = (b * d * b⁻¹ * d⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem hbd
  obtain ⟨v, hv, hfix⟩ := exists_fixed_in_coset' (p := 3) (U := U) (V := pCoreOf 2 M)
    (isPGroup_three_of_pow3 fun r hr => hD.pow3 r (hUR hr))
    (not_three_dvd_of_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M))
    (fun u hu => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hUM hu))
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hdM)
    (fun u hu => by
      have h1 := (hUmc hu).2
      have e : u * d * u⁻¹ * d⁻¹ = (d * u * d⁻¹ * u⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem h1)
  have hα := orbitProd_le_alpha hJ₀ hUM
  have hK₀ : orbitProd M J₀ (S : Set G) ≤ orbitProd M J₀ (U : Set G) :=
    orbitProd_mono (fun x hx => (le_sup_left : S ≤ U) hx)
  have hdK : d * v ∈ orbitProd M J₀ (U : Set G) := by
    rw [hd]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hK₀ hzK)
      (orbitProd_mono hX₁U hz₁K)) (orbitProd_mono hX₂U hz₂K)) (core_le_orbitProd _ _ _ hv)
  refine ⟨d * v, Subgroup.mem_inf.2 ⟨hdK, Subgroup.mem_centralizer_iff.2 ?_⟩,
    alpha_le_normalizer hJ₀ (hα hdK), ?_⟩
  · intro u hu
    have h1 := hfix u hu
    calc u * (d * v) = (u * (d * v) * u⁻¹) * u := by group
      _ = (d * v) * u := by rw [h1]
  · apply permHom_eq
    have hz₁N := alpha_le_normalizer hJ₀ (hα (orbitProd_mono hX₁U hz₁K))
    have hz₂N := alpha_le_normalizer hJ₀ (hα (orbitProd_mono hX₂U hz₂K))
    have hvN := core_le_normalizer hJ₀ hv
    have h0 : IsConj J₀ ι z σ := hzσ ▸ permHom_spec J₀ ι ⟨z, hzN⟩
    have h1 := isConj_mul hz₁N h0 (isConj_one_of_actTriv ι t10)
    have h2 := isConj_mul hz₂N h1 (isConj_one_of_actTriv ι t20)
    have h3 := isConj_mul hvN h2 (isConj_one_of_actTriv ι (actTriv_of_mem_core hJ₀ hv))
    simpa [hd] using h3

theorem diagSurj {M J₀ R : Subgroup G} (hD : DiagData M J₀ R)
    (ι : (Sec12a3.JbarQ J₀ ⧸ Subgroup.center (Sec12a3.JbarQ J₀)) ≃* ↥(alternatingGroup (Fin 7))) :
    DiagSurj M J₀ ι R := by
  classical
  haveI := Fintype.ofFinite ↥R
  set R₀ := R ⊓ Subgroup.normalizer (J₀ : Set G) with hR₀
  have key : ∀ F : Finset ↥R, DiagSurj M J₀ ι (R₀ ⊔ ⨆ b ∈ F, Subgroup.zpowers (b : G)) := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      have e : R₀ ⊔ ⨆ b ∈ (∅ : Finset ↥R), Subgroup.zpowers (b : G) = R₀ := by simp
      rw [e]
      exact diagSurj_base hD ι
    | insert b F hbF ih =>
      rw [Finset.iSup_insert, sup_left_comm, sup_comm]
      have hSR : R₀ ⊔ ⨆ b ∈ F, Subgroup.zpowers (b : G) ≤ R :=
        sup_le inf_le_left (iSup₂_le fun b _ => (Subgroup.zpowers_le).2 b.2)
      by_cases hbS : (b : G) ∈ R₀ ⊔ ⨆ b ∈ F, Subgroup.zpowers (b : G)
      · rw [sup_eq_left.2 ((Subgroup.zpowers_le).2 hbS)]
        exact ih
      · exact diagSurj_step hD ι hSR le_sup_left b.2 hbS ih
  have htop : R₀ ⊔ ⨆ b ∈ (Finset.univ : Finset ↥R), Subgroup.zpowers (b : G) = R := by
    refine le_antisymm (sup_le inf_le_left (iSup₂_le fun b _ => (Subgroup.zpowers_le).2 b.2)) ?_
    intro r hr
    exact (le_sup_right : (⨆ b ∈ (Finset.univ : Finset ↥R), Subgroup.zpowers (b : G)) ≤ _)
      ((le_iSup₂_of_le (f := fun (b : ↥R) (_ : b ∈ (Finset.univ : Finset ↥R)) =>
        Subgroup.zpowers (b : G)) ⟨r, hr⟩ (Finset.mem_univ _) le_rfl) (Subgroup.mem_zpowers r))
  rw [← htop]
  exact key Finset.univ

end Diagonal

section ZPowers

variable {G : Type} [Group G] [Finite G]

theorem wpc_le_orbitProd {M J : Subgroup G} {e a : G} :
    Sec12a3.Wpc e a J ≤ orbitProd M J (Subgroup.zpowers e : Set G) :=
  iSup_le fun k => (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
    (inf_le_left.trans (le_orbitProd (Subgroup.pow_mem _ (Subgroup.mem_zpowers e) _)))

theorem mem_centralizer_zpowers_iff {e x : G} :
    x ∈ Subgroup.centralizer ((Subgroup.zpowers e : Subgroup G) : Set G) ↔ x ∈ Cg e := by
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.1 hx) e (Subgroup.mem_zpowers e)).symm
  · intro hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.1 hx).symm k).eq

theorem diagData_zpowers {M J : Subgroup G} {e : G} (hJ : Sec12a3.CompSet M J) (heM : e ∈ M)
    (he3 : e ^ 3 = 1)
    (hcase : GLBConj e J ≠ J ∨ (e ∈ Subgroup.normalizer (J : Set G) ∧ ActTriv e J)) :
    DiagData M J (Subgroup.zpowers e) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨hJ, (Subgroup.zpowers_le).2 heM, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he3, one_zpow]
  · intro r hr s hs
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    exact (Commute.zpow_zpow_self e i j).eq
  · rcases hcase with hne | ⟨heN, heT⟩
    · intro r hr hrN
      by_cases hr1 : r = 1
      · rw [hr1]; exact actTriv_one J
      exfalso
      apply hne
      rw [← mem_normalizer_iff_gLBConj_eq]
      have hr3 : r ^ 3 = 1 := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he3, one_zpow]
      have he1 : e ≠ 1 := fun h => hr1 (by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
        rw [h, one_zpow])
      have hle : Subgroup.zpowers r ≤ Subgroup.zpowers e := (Subgroup.zpowers_le).2 hr
      have hcard : Nat.card ↥(Subgroup.zpowers e) ≤ Nat.card ↥(Subgroup.zpowers r) := by
        rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime he3 he1,
          orderOf_eq_prime hr3 hr1]
      have heq := Subgroup.eq_of_le_of_card_ge hle hcard
      have he : e ∈ Subgroup.zpowers r := heq ▸ Subgroup.mem_zpowers e
      exact ((Subgroup.zpowers_le).2 hrN) he
    · intro r hr _
      have hle : Subgroup.zpowers e ≤ actTrivSub J := (Subgroup.zpowers_le).2 ⟨heN, heT⟩
      exact (hle hr).2

end ZPowers

section Tof

variable {G : Type} [Group G] [Finite G]

theorem tof_actTriv_of_cover {M J : Subgroup G} {a : G} (hJ : Sec12a3.CompSet M J)
    (ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7)))
    (hcov : ∀ σ ∈ alternatingGroup (Fin 7), ∃ z, ∃ hz : z ∈ alphaOf 3 M, z ∈ Cg a ∧
      permHom J ι ⟨z, alpha_le_normalizer hJ hz⟩ = σ) :
    ∀ t ∈ Tof 3 M a, ActTriv t J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN : Tof 3 M a ≤ Subgroup.normalizer (J : Set G) :=
    (Sec12a.tof_le_alphaOf M a).trans (alpha_le_normalizer hJ)
  set P : Subgroup (Perm (Fin 7)) :=
    ((Tof 3 M a).subgroupOf (Subgroup.normalizer (J : Set G))).map (permHom J ι) with hP
  have hT2 : IsPGroup 2 ↥(Tof 3 M a) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hP2 : IsPGroup 2 ↥P := (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTN).symm).map _
  have hPn : ∀ σ ∈ alternatingGroup (Fin 7), ∀ p ∈ P, σ * p * σ⁻¹ ∈ P := by
    intro σ hσ p hp
    obtain ⟨z, hz, hza, rfl⟩ := hcov σ hσ
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hp
    have ht' : (t : G) ∈ Tof 3 M a := Subgroup.mem_subgroupOf.1 ht
    have hzt : z * (t : G) * z⁻¹ ∈ Tof 3 M a :=
      (Subgroup.mem_normalizer_iff.1 (Sec12a2.normalizer_tof M a
        (Sec12a.alphaOf_le_self M hz) hza) _).1 ht'
    refine Subgroup.mem_map.2 ⟨⟨z, alpha_le_normalizer hJ hz⟩ * t *
      (⟨z, alpha_le_normalizer hJ hz⟩)⁻¹, Subgroup.mem_subgroupOf.2 hzt, ?_⟩
    simp only [map_mul, map_inv]
  have hPb := eq_bot_of_two_subgroup_normalized hP2 hPn
  intro t ht
  have h1 : permHom J ι ⟨t, hTN ht⟩ = 1 := by
    have h2 : permHom J ι ⟨t, hTN ht⟩ ∈ P :=
      Subgroup.mem_map.2 ⟨⟨t, hTN ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
    rwa [hPb, Subgroup.mem_bot] at h2
  exact (actTriv_iff_permHom hJ.2.2.2 ι ⟨t, hTN ht⟩).2 h1

theorem tof_actTriv {M J : Subgroup G} {a : G} (hJ : Sec12a3.CompSet M J) (haM : a ∈ M)
    (ha3 : a ^ 3 = 1) (hnot : ¬ Sec12a3.ThreeCycComp a J) : ∀ t ∈ Tof 3 M a, ActTriv t J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι⟩ := hJ.2.2.2.2.2
  have hTN : Tof 3 M a ≤ Subgroup.normalizer (J : Set G) :=
    (Sec12a.tof_le_alphaOf M a).trans (alpha_le_normalizer hJ)
  by_cases haN : a ∈ Subgroup.normalizer (J : Set G)
  · have hA : IsConj J ι a (permHom J ι ⟨a, haN⟩) := permHom_spec J ι ⟨a, haN⟩
    have h3 : (permHom J ι ⟨a, haN⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have e : (⟨a, haN⟩ : ↥(Subgroup.normalizer (J : Set G))) ^ 3 = 1 :=
        Subtype.ext (by simpa using ha3)
      rw [e, map_one]
    by_cases h1 : permHom J ι ⟨a, haN⟩ = 1
    · have haT : ActTriv a J := (actTriv_iff_permHom hJ.2.2.2 ι ⟨a, haN⟩).2 h1
      apply tof_actTriv_of_cover hJ ι
      intro σ hσ
      obtain ⟨y, rfl⟩ := Sec12a3.psiOf_surj J ι σ hσ
      obtain ⟨v, hv, hyv⟩ := exists_mul_mem_centralizer (p := 3) (zpowers_isPGroup_three ha3)
        (not_three_dvd_of_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J))
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J haN)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J y.2) (haT y y.2)
      obtain ⟨v', hv', rfl⟩ := hv
      refine ⟨(y : G) * v', Sec12a3.compSet_le_alpha hJ (J.mul_mem y.2 v'.2), hyv, ?_⟩
      rw [permHom_eq _ (isConj_of_mem ι (y * v'))]
      rw [map_mul, psiOf_eq_one_of_mem ι hv', mul_one]
    · rcases Sec12a3.cycleType_of_pow_three h3 h1 with hc | hc
      · exact absurd ⟨fun x hx => (Subgroup.mem_normalizer_iff.1 haN x).1 hx, ι, _, hc,
          conjsBy_of_isConj haN hA⟩ hnot
      · intro t ht
        have hπA := permHom_mem_alt hJ ι (Sec12a.tof_le_alphaOf M a ht)
        have hcomm : permHom J ι ⟨t, hTN ht⟩ ∈
            Subgroup.centralizer ({permHom J ι ⟨a, haN⟩} : Set (Perm (Fin 7))) := by
          rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Sec12a.tof_le_cg M a ht))
        obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _ ⟨t, ht⟩
        have hk' : (permHom J ι ⟨t, hTN ht⟩) ^ 2 ^ k = 1 := by
          rw [← map_pow]
          have e : (⟨t, hTN ht⟩ : ↥(Subgroup.normalizer (J : Set G))) ^ 2 ^ k = 1 :=
            Subtype.ext (by simpa using congrArg Subtype.val hk)
          rw [e, map_one]
        have hodd := Sec12a3.double_cent_odd hc
        have hd1 : orderOf (permHom J ι ⟨t, hTN ht⟩) ∣ Nat.card ↥(Subgroup.centralizer
            ({permHom J ι ⟨a, haN⟩} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) := by
          have h := orderOf_dvd_natCard (⟨permHom J ι ⟨t, hTN ht⟩, Subgroup.mem_inf.2 ⟨hcomm, hπA⟩⟩ :
            ↥(Subgroup.centralizer ({permHom J ι ⟨a, haN⟩} : Set (Perm (Fin 7))) ⊓
              alternatingGroup (Fin 7)))
          rwa [Subgroup.orderOf_mk] at h
        have hd2 := orderOf_dvd_of_pow_eq_one hk'
        have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥(Subgroup.centralizer
            ({permHom J ι ⟨a, haN⟩} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7))) :=
          Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
        have hord : orderOf (permHom J ι ⟨t, hTN ht⟩) = 1 :=
          Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd hd2 hd1)
        exact (actTriv_iff_permHom hJ.2.2.2 ι ⟨t, hTN ht⟩).2 (orderOf_eq_one_iff.1 hord)
  · have hD := diagData_zpowers hJ haM ha3 (Or.inl fun h => haN (mem_normalizer_iff_gLBConj_eq.2 h))
    refine tof_actTriv_of_cover hJ ι fun σ hσ => ?_
    obtain ⟨z, hz, hzN, hzσ⟩ := diagSurj hD ι σ hσ
    exact ⟨z, orbitProd_le_alpha hJ (fun x hx => hD.le hx) (Subgroup.mem_inf.1 hz).1,
      mem_centralizer_zpowers_iff.1 (Subgroup.mem_inf.1 hz).2, hzσ⟩

end Tof

section Lifts

variable {G : Type} [Group G] [Finite G]

theorem two_elems_comm {π : Perm (Fin 7)} (hπ : π.cycleType = {3}) {u v : Perm (Fin 7)}
    (hu : u * π = π * u) (huA : Perm.sign u = 1) (hu2 : ∃ k : ℕ, u ^ 2 ^ k = 1)
    (hv : v * π = π * v) (hvA : Perm.sign v = 1) (hv2 : ∃ k : ℕ, v ^ 2 ^ k = 1) :
    u * v = v * u := by
  obtain ⟨c, hc⟩ := Sec12a3.conj_of_cycleType_three hπ
  subst hc
  have red : ∀ w : Perm (Fin 7), w * (c * S7.a * c⁻¹) = (c * S7.a * c⁻¹) * w →
      Perm.sign w = 1 → (∃ k : ℕ, w ^ 2 ^ k = 1) →
      c⁻¹ * w * c = 1 ∨ c⁻¹ * w * c = S7.x ∨ c⁻¹ * w * c = S7.y ∨ c⁻¹ * w * c = S7.x * S7.y := by
    intro w hw hwA ⟨k, hk⟩
    have h1 : (c⁻¹ * w * c) * S7.a = S7.a * (c⁻¹ * w * c) := by
      calc (c⁻¹ * w * c) * S7.a = c⁻¹ * (w * (c * S7.a * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * S7.a * c⁻¹) * w) * c := by rw [hw]
        _ = S7.a * (c⁻¹ * w * c) := by group
    have h2 : Perm.sign (c⁻¹ * w * c) = 1 := by
      rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hwA]
      simp
    have h3 : (c⁻¹ * w * c) ^ 2 ^ k = 1 := by rw [Sec12a3.conj_pow', hk]; group
    exact (Sec12a3.mem_klein_iff _).1
      (Sec12a3.V_le_kleinGroup (Sec12a3.elem_two_cent_mem_V h1 h2 ⟨k, h3⟩))
  have hu' := red u hu huA hu2
  have hv' := red v hv hvA hv2
  have key : (c⁻¹ * u * c) * (c⁻¹ * v * c) = (c⁻¹ * v * c) * (c⁻¹ * u * c) := by
    rcases hu' with h | h | h | h <;> rcases hv' with h' | h' | h' | h' <;> rw [h, h'] <;> decide
  calc u * v = c * ((c⁻¹ * u * c) * (c⁻¹ * v * c)) * c⁻¹ := by group
    _ = c * ((c⁻¹ * v * c) * (c⁻¹ * u * c)) * c⁻¹ := by rw [key]
    _ = v * u := by group

theorem two_elem_mem_pCoreOf {Y : Subgroup G} (ρ : ↥Y →* Perm (Fin 7)) {π : Perm (Fin 7)}
    (hπ : π.cycleType = {3}) (hρA : ∀ y, ρ y ∈ alternatingGroup (Fin 7))
    (hρC : ∀ y, ρ y * π = π * ρ y) {L : Subgroup G} (hLY : L ≤ Y) (hL2 : IsPGroup 2 ↥L)
    (hLρ : ∀ y : ↥Y, (y : G) ∈ L → ρ y = 1)
    (hK : ∀ k y : ↥Y, ρ k = 1 → ((k * y * k⁻¹ * y⁻¹ : ↥Y) : G) ∈ L) {g : G} (hgY : g ∈ Y)
    (hg2 : ∃ n : ℕ, g ^ 2 ^ n = 1) : g ∈ pCoreOf 2 Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, -, -, hV3, -, hV5, -⟩ := Sec12a3.three_cycle_klein hπ
  set W : Subgroup ↥Y := V.comap ρ with hW
  set K : Subgroup ↥W := ρ.ker.subgroupOf W with hKdef
  set L' : Subgroup ↥W := (L.subgroupOf Y).subgroupOf W with hL'
  haveI : K.Normal := (MonoidHom.normal_ker ρ).subgroupOf W
  have hLK : L' ≤ K := by
    intro x hx
    rw [hL', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
    rw [hKdef, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact hLρ _ hx
  have hL2' : IsPGroup 2 ↥L' := by
    intro x
    have hx : (((x : ↥W) : ↥Y) : G) ∈ L :=
      Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 x.2)
    obtain ⟨n, hn⟩ := hL2 ⟨_, hx⟩
    refine ⟨n, Subtype.ext (Subtype.ext (Subtype.ext ?_))⟩
    simpa using congrArg Subtype.val hn
  have hcomm : ∀ k ∈ K, ∀ y : ↥W, k * y * k⁻¹ * y⁻¹ ∈ L' := by
    intro k hk y
    rw [hKdef, Subgroup.mem_subgroupOf, MonoidHom.mem_ker] at hk
    rw [hL', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using hK k y hk
  have hquot : ∀ w : ↥W, ∃ n : ℕ, w ^ 2 ^ n ∈ K := by
    intro w
    obtain ⟨n, hn⟩ := hV3 ⟨ρ w, w.2⟩
    refine ⟨n, ?_⟩
    rw [hKdef, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.coe_pow, map_pow]
    simpa using congrArg Subtype.val hn
  obtain ⟨P, hP2, -, -, hPel⟩ := Sec12a3.sylow_core hLK hL2' hcomm hquot
  have hW2 : ∀ y : ↥Y, (∃ n : ℕ, y ^ 2 ^ n = 1) → y ∈ W := by
    rintro y ⟨n, hn⟩
    show ρ y ∈ V
    exact hV5 (ρ y) ⟨Subgroup.mem_centralizer_singleton_iff.2 (hρC y), hρA y⟩ n
      (by rw [← map_pow, hn, map_one])
  set P' : Subgroup ↥Y := P.map W.subtype with hP'
  have hP'2 : IsPGroup 2 ↥P' := hP2.map W.subtype
  have hP'all : ∀ y : ↥Y, (∃ n : ℕ, y ^ 2 ^ n = 1) → y ∈ P' := by
    intro y hy
    refine Subgroup.mem_map.2 ⟨⟨y, hW2 y hy⟩, hPel _ ?_, rfl⟩
    obtain ⟨n, hn⟩ := hy
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hP'n : P'.Normal := ⟨fun x hx h => by
    apply hP'all
    obtain ⟨n, hn⟩ := hP'2 ⟨x, hx⟩
    refine ⟨n, ?_⟩
    have hxn : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    rw [conj_pow, hxn]
    group⟩
  have hle : P' ≤ CFSG.pCore 2 ↥Y := CFSG.LieType.BorelTits.le_pCore 2 hP'n hP'2
  have hgP : (⟨g, hgY⟩ : ↥Y) ∈ P' := by
    apply hP'all
    obtain ⟨n, hn⟩ := hg2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  exact ⟨_, hle hgP, rfl⟩

theorem comm_mem_pCore_of_psiOf {J : Subgroup G} (hX : IsHatSeven (Sec12a3.JbarQ J))
    (ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7)))
    {k : ↥J} (hk : Sec12a3.psiOf J ι k = 1) (y : ↥J) : k * y * k⁻¹ * y⁻¹ ∈ CFSG.pCore 2 ↥J := by
  have hc := Subgroup.mem_center_iff.1 (mk_mem_center_of_psiOf hX ι hk)
  have h1 : (QuotientGroup.mk (k * y * k⁻¹ * y⁻¹) : Sec12a3.JbarQ J) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, ← hc (QuotientGroup.mk y)]
    group
  exact (QuotientGroup.eq_one_iff _).1 h1

theorem two_elem_mem_vpc {J : Subgroup G} (hX : IsHatSeven (Sec12a3.JbarQ J))
    (ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7)))
    {e : G} {πa : Perm (Fin 7)} (hπa : πa.cycleType = {3})
    (hC : ∀ y : ↥J, (y : G) ∈ Cg e → Sec12a3.psiOf J ι y * πa = πa * Sec12a3.psiOf J ι y)
    {g : G} (hgJ : g ∈ J) (hge : g ∈ Cg e) (hg2 : ∃ n : ℕ, g ^ 2 ^ n = 1) :
    g ∈ pCoreOf 2 (J ⊓ Cg e) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine two_elem_mem_pCoreOf ((Sec12a3.psiOf J ι).comp (Subgroup.inclusion inf_le_left)) hπa
    (fun y => Sec12a3.psiOf_mem_alt J ι _) (fun y => hC _ y.2.2) (L := pCoreOf 2 J ⊓ Cg e)
    (inf_le_inf_right _ (CFSG.LieType.BorelTits.pCoreOf_le 2 J))
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J).to_le inf_le_left) ?_ ?_ ⟨hgJ, hge⟩ hg2
  · rintro y ⟨⟨w, hw, hwe⟩, -⟩
    have e : Subgroup.inclusion (inf_le_left : J ⊓ Cg e ≤ J) y = w := Subtype.ext hwe.symm
    simp only [MonoidHom.coe_comp, Function.comp_apply, e]
    exact psiOf_eq_one_of_mem ι hw
  · intro k y hk
    have h1 := comm_mem_pCore_of_psiOf hX ι hk (Subgroup.inclusion inf_le_left y)
    refine ⟨⟨_, h1, ?_⟩, (k * y * k⁻¹ * y⁻¹).2.2⟩
    simp

theorem odd_pow_two_pow_modEq {r : ℕ} (hr : Odd r) (k : ℕ) : r ^ 2 ^ k ≡ 1 [MOD 2 ^ k] := by
  induction k with
  | zero => simp [Nat.modEq_one]
  | succ k ih =>
    rw [Nat.modEq_iff_dvd] at ih ⊢
    obtain ⟨c, hc⟩ := ih
    obtain ⟨m, hm⟩ := hr.pow (n := 2 ^ k)
    refine ⟨c * (m + 1), ?_⟩
    have hm' : ((r ^ 2 ^ k : ℕ) : ℤ) = 2 * m + 1 := by exact_mod_cast hm
    push_cast at hc hm' ⊢
    rw [pow_succ, pow_mul]
    linear_combination (1 + (r : ℤ) ^ 2 ^ k) * hc + 2 ^ k * c * hm'

theorem exists_two_elem_lift {H K : Type*} [Group H] [Finite H] [Group K] (f : H →* K) (y : H)
    {k : ℕ} (hk : (f y) ^ 2 ^ k = 1) : ∃ y' : H, (∃ n : ℕ, y' ^ 2 ^ n = 1) ∧ f y' = f y := by
  obtain ⟨i, r, hr, hN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  refine ⟨y ^ (r ^ 2 ^ k), ⟨i, ?_⟩, ?_⟩
  · rw [← pow_mul]
    apply orderOf_dvd_iff_pow_eq_one.1
    rw [hN, mul_comm (r ^ 2 ^ k)]
    exact Nat.mul_dvd_mul_left _ (dvd_pow_self r (pow_ne_zero _ two_ne_zero))
  · rw [map_pow]
    conv_rhs => rw [← pow_one (f y)]
    rw [pow_eq_pow_iff_modEq]
    exact Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hk) (odd_pow_two_pow_modEq hr k)

theorem exists_vpc_lift {J : Subgroup G} (hX : IsHatSeven (Sec12a3.JbarQ J))
    (ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7)))
    {a : G} {πa : Perm (Fin 7)} (haN : a ∈ Subgroup.normalizer (J : Set G)) (ha3 : a ^ 3 = 1)
    (hπa : πa.cycleType = {3}) (hA : IsConj J ι a πa) {v : Perm (Fin 7)}
    (hvA : v ∈ alternatingGroup (Fin 7)) (hvc : v * πa = πa * v) {k : ℕ} (hvk : v ^ 2 ^ k = 1) :
    ∃ u : ↥J, (u : G) ∈ Sec12a3.Vpc a J ∧ Sec12a3.psiOf J ι u = v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := Sec12a3.psiOf_surj J ι v hvA
  obtain ⟨y₂, ⟨n, hn⟩, hy₂⟩ := exists_two_elem_lift (Sec12a3.psiOf J ι) y (k := k)
    (by rw [hy]; exact hvk)
  rw [hy] at hy₂
  have hay : a * (y₂ : G) * a⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 haN _).1 y₂.2
  set x : ↥J := ⟨_, hay⟩ with hx
  have hψx : Sec12a3.psiOf J ι x = v := by
    rw [hA y₂ x rfl, hy₂]
    calc πa * v * πa⁻¹ = (v * πa) * πa⁻¹ := by rw [hvc]
      _ = v := by group
  have hc : (QuotientGroup.mk (x * y₂⁻¹) : Sec12a3.JbarQ J) ∈
      Subgroup.center (Sec12a3.JbarQ J) :=
    mk_mem_center_of_psiOf hX ι (by rw [map_mul, map_inv, hψx, hy₂, mul_inv_cancel])
  have hxn : x ^ 2 ^ n = 1 := by
    apply Subtype.ext
    simp only [hx, Subgroup.coe_pow, Subgroup.coe_one]
    rw [conj_pow, show (y₂ : G) ^ 2 ^ n = 1 from by simpa using congrArg Subtype.val hn]
    group
  have hz : (QuotientGroup.mk (x * y₂⁻¹) : Sec12a3.JbarQ J) = 1 := by
    set z := (QuotientGroup.mk (x * y₂⁻¹) : Sec12a3.JbarQ J) with hzdef
    have hcomm : Commute z (QuotientGroup.mk y₂) := (Subgroup.mem_center_iff.1 hc _).symm
    have h1 : (QuotientGroup.mk x : Sec12a3.JbarQ J) = z * QuotientGroup.mk y₂ := by
      rw [hzdef, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      group
    have h2 : z ^ 2 ^ n = 1 := by
      have h3 : (QuotientGroup.mk x : Sec12a3.JbarQ J) ^ 2 ^ n = 1 := by
        rw [← QuotientGroup.mk_pow, hxn, QuotientGroup.mk_one]
      have h4 : (QuotientGroup.mk y₂ : Sec12a3.JbarQ J) ^ 2 ^ n = 1 := by
        rw [← QuotientGroup.mk_pow, hn, QuotientGroup.mk_one]
      have h5 : z ^ 2 ^ n * (QuotientGroup.mk y₂ : Sec12a3.JbarQ J) ^ 2 ^ n = 1 := by
        rw [← hcomm.mul_pow, ← h1, h3]
      rwa [h4, mul_one] at h5
    have h4 : orderOf z ∣ 3 := by
      have h5 := orderOf_dvd_natCard (⟨z, hc⟩ : Subgroup.center (Sec12a3.JbarQ J))
      rw [hX.2.1, Subgroup.orderOf_mk] at h5
      exact h5
    have h6 : orderOf z ∣ Nat.gcd 3 (2 ^ n) := Nat.dvd_gcd h4 (orderOf_dvd_of_pow_eq_one h2)
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)),
      Nat.dvd_one, orderOf_eq_one_iff] at h6
    exact h6
  have hcm : a * (y₂ : G) * a⁻¹ * (y₂ : G)⁻¹ ∈ pCoreOf 2 J :=
    ⟨x * y₂⁻¹, (QuotientGroup.eq_one_iff _).1 hz, by simp [hx]⟩
  obtain ⟨w, hw, hyw⟩ := exists_mul_mem_centralizer (p := 3) (zpowers_isPGroup_three ha3)
    (not_three_dvd_of_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J))
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J haN)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J y₂.2) hcm
  obtain ⟨w', hw', rfl⟩ := hw
  refine ⟨y₂ * w', ?_, by rw [map_mul, psiOf_eq_one_of_mem ι hw', mul_one, hy₂]⟩
  have hC : ∀ y : ↥J, (y : G) ∈ Cg a →
      Sec12a3.psiOf J ι y * πa = πa * Sec12a3.psiOf J ι y := by
    intro y hya
    have h1 := hA y y (by
      rw [show a * (y : G) * a⁻¹ = (y * a) * a⁻¹ by
        rw [Subgroup.mem_centralizer_singleton_iff.1 hya]]
      group)
    calc Sec12a3.psiOf J ι y * πa = (πa * Sec12a3.psiOf J ι y * πa⁻¹) * πa := by rw [← h1]
      _ = πa * Sec12a3.psiOf J ι y := by group
  have h2 : ∃ m : ℕ, ((y₂ * w' : ↥J) : G) ^ 2 ^ m = 1 := by
    have h3 : (y₂ * w') ^ 2 ^ n ∈ CFSG.pCore 2 ↥J := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff w').2 hw', mul_one, ← QuotientGroup.mk_pow, hn,
        QuotientGroup.mk_one]
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥J)) ⟨_, h3⟩
    refine ⟨n + j, ?_⟩
    have h4 : ((y₂ * w') ^ 2 ^ n) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    rw [pow_add, pow_mul]
    simpa using congrArg Subtype.val h4
  exact two_elem_mem_vpc hX ι hπa hC (y₂ * w').2 hyw h2

end Lifts

section Separation

variable {G : Type} [Group G] [Finite G]

theorem comm_core_of_actTriv {M : Subgroup G} {w : G} (hwM : w ∈ M)
    (htriv : ∀ J, Sec12a3.CompSet M J → ActTriv w J) {g : G} (hg : g ∈ alphaOf 3 M) :
    w * g * w⁻¹ * g⁻¹ ∈ pCoreOf 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hαC : alphaOf 3 M ≤ modCent M w := by
    unfold alphaOf
    refine sup_le ?_ (iSup₂_le fun K hK => ?_)
    · intro o ho
      refine ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 M ho, ?_⟩
      have h1 : w * o * w⁻¹ ∈ pCoreOf 2 M := (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hwM) o).1 ho
      exact (pCoreOf 2 M).mul_mem h1 (inv_mem ho)
    · have hKc : Sec12a3.CompSet M K := ⟨hK.2.1, hK.2.2.1, hK.2.2.2.1, hK.2.2.2.2⟩
      intro k hk
      exact ⟨hKc.1 hk, pCoreOf_le_of_isSubnormal 2 hKc.2.1 (htriv K hKc k hk)⟩
  exact (hαC hg).2

theorem mem_core_of_actTriv {M : Subgroup G} {w : G} (hw : w ∈ alphaOf 3 M)
    (htriv : ∀ J, Sec12a3.CompSet M J → ActTriv w J) {n : ℕ} (hn : w ^ 2 ^ n ∈ pCoreOf 2 M) :
    w ∈ pCoreOf 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hwM : w ∈ M := Sec12a.alphaOf_le_self M hw
  have hOM := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  set N : Subgroup G := pCoreOf 2 M ⊔ Subgroup.zpowers w with hN
  have hzM : Subgroup.zpowers w ≤ M := (Subgroup.zpowers_le).2 hwM
  have hdec : ∀ x ∈ N, ∃ o ∈ pCoreOf 2 M, ∃ k : ℤ, x = o * w ^ k := by
    intro x hx
    obtain ⟨o, ho, p, hp, rfl⟩ := Sec12a2.mem_sup_of_le_normalizer hzM hOM hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
    exact ⟨o, ho, k, rfl⟩
  have hNα : N ≤ alphaOf 3 M := sup_le (Sec12a.le_alphaOf_two M) ((Subgroup.zpowers_le).2 hw)
  have hwN : w ∈ N := (le_sup_right : Subgroup.zpowers w ≤ N) (Subgroup.mem_zpowers w)
  have hconj : ∀ g ∈ alphaOf 3 M, ∀ x ∈ N, g * x * g⁻¹ ∈ N := by
    intro g hg x hx
    obtain ⟨o, ho, k, rfl⟩ := hdec x hx
    have hgM : g ∈ M := Sec12a.alphaOf_le_self M hg
    have h1 : g * o * g⁻¹ ∈ N := (le_sup_left : pCoreOf 2 M ≤ N)
      ((Subgroup.mem_normalizer_iff.1 (hOM hgM) o).1 ho)
    have h2 : g * w * g⁻¹ ∈ N := by
      have hc := comm_core_of_actTriv hwM htriv hg
      have e : g * w * g⁻¹ = (w * g * w⁻¹ * g⁻¹)⁻¹ * w := by group
      rw [e]
      exact N.mul_mem ((le_sup_left : pCoreOf 2 M ≤ N) (inv_mem hc)) hwN
    have e : g * (o * w ^ k) * g⁻¹ = (g * o * g⁻¹) * (g * w * g⁻¹) ^ k := by
      rw [conj_zpow]; group
    rw [e]
    exact N.mul_mem h1 (N.zpow_mem h2 k)
  have hαN : alphaOf 3 M ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj g hg x, fun hx => ?_⟩
    have h1 := hconj g⁻¹ (inv_mem hg) _ hx
    simpa [mul_assoc] using h1
  have hN2 : IsPGroup 2 ↥N := by
    rintro ⟨x, hx⟩
    obtain ⟨o, ho, k, rfl⟩ := hdec x hx
    have h1 : (o * w ^ k) ^ 2 ^ n ∈ pCoreOf 2 M := by
      have h2 := mul_pow_mul_inv_mem ho (hOM (Subgroup.zpow_mem _ hwM k)) (2 ^ n)
      have h3 : (w ^ k) ^ 2 ^ n ∈ pCoreOf 2 M := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
        exact Subgroup.zpow_mem _ hn k
      have e : (o * w ^ k) ^ 2 ^ n =
          ((o * w ^ k) ^ 2 ^ n * ((w ^ k) ^ 2 ^ n)⁻¹) * (w ^ k) ^ 2 ^ n := by group
      rw [e]
      exact (pCoreOf 2 M).mul_mem h2 h3
    obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M ⟨_, h1⟩
    refine ⟨n + j, Subtype.ext ?_⟩
    have h4 : ((o * w ^ k) ^ 2 ^ n) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_add, pow_mul]
    exact h4
  have hle : N ≤ pCoreOf 2 (alphaOf 3 M) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNα hαN hN2
  have hαM : alphaOf 3 M ≤ M := Sec12a.alphaOf_le_self M
  have hle2 : pCoreOf 2 (alphaOf 3 M) ≤ pCoreOf 2 M := pCoreOf_le_of_normal 2 hαM
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hαM).2 (le_normalizer_alphaOf 3 M))
  exact hle2 (hle hwN)

theorem mul_inv_mem_core {M : Subgroup G} {x y : G} (hx : x ∈ alphaOf 3 M)
    (hy : y ∈ alphaOf 3 M) (hx2 : ∃ n : ℕ, x ^ 2 ^ n = 1) (hy2 : ∃ n : ℕ, y ^ 2 ^ n = 1)
    (htriv : ∀ J, Sec12a3.CompSet M J → ActTriv (x * y⁻¹) J) : x * y⁻¹ ∈ pCoreOf 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxM := Sec12a.alphaOf_le_self M hx
  have hyM := Sec12a.alphaOf_le_self M hy
  have hwM : x * y⁻¹ ∈ M := M.mul_mem hxM (M.inv_mem hyM)
  have hc := comm_core_of_actTriv hwM htriv hy
  obtain ⟨n₁, hn₁⟩ := hx2
  obtain ⟨n₂, hn₂⟩ := hy2
  refine mem_core_of_actTriv ((alphaOf 3 M).mul_mem hx (inv_mem hy)) htriv (n := n₁ + n₂) ?_
  set q := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hq
  have hcomm : Commute (q ⟨x * y⁻¹, hwM⟩) (q ⟨y, hyM⟩) := by
    have h1 : q (⟨x * y⁻¹, hwM⟩ * ⟨y, hyM⟩ * (⟨x * y⁻¹, hwM⟩)⁻¹ * (⟨y, hyM⟩)⁻¹) = 1 := by
      rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      obtain ⟨z, hz, hze⟩ := hc
      have e : z = ⟨x * y⁻¹, hwM⟩ * ⟨y, hyM⟩ * (⟨x * y⁻¹, hwM⟩)⁻¹ * (⟨y, hyM⟩)⁻¹ :=
        Subtype.ext (by simpa using hze)
      rwa [← e]
    simp only [map_mul, map_inv] at h1
    show q ⟨x * y⁻¹, hwM⟩ * q ⟨y, hyM⟩ = q ⟨y, hyM⟩ * q ⟨x * y⁻¹, hwM⟩
    calc q ⟨x * y⁻¹, hwM⟩ * q ⟨y, hyM⟩
        = (q ⟨x * y⁻¹, hwM⟩ * q ⟨y, hyM⟩ * (q ⟨x * y⁻¹, hwM⟩)⁻¹ * (q ⟨y, hyM⟩)⁻¹) *
          (q ⟨y, hyM⟩ * q ⟨x * y⁻¹, hwM⟩) := by group
      _ = q ⟨y, hyM⟩ * q ⟨x * y⁻¹, hwM⟩ := by rw [h1, one_mul]
  have hxq : q ⟨x, hxM⟩ ^ 2 ^ (n₁ + n₂) = 1 := by
    rw [← map_pow]
    have e : (⟨x, hxM⟩ : ↥M) ^ 2 ^ (n₁ + n₂) = 1 :=
      Subtype.ext (by simp [pow_add, pow_mul, hn₁])
    rw [e, map_one]
  have hyq : q ⟨y, hyM⟩ ^ 2 ^ (n₁ + n₂) = 1 := by
    rw [← map_pow]
    have e : (⟨y, hyM⟩ : ↥M) ^ 2 ^ (n₁ + n₂) = 1 :=
      Subtype.ext (by simp [pow_add, mul_comm (2 ^ n₁), pow_mul, hn₂])
    rw [e, map_one]
  have hwq : q ⟨x * y⁻¹, hwM⟩ ^ 2 ^ (n₁ + n₂) = 1 := by
    have e : q ⟨x, hxM⟩ = q ⟨x * y⁻¹, hwM⟩ * q ⟨y, hyM⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext (by simp)
    rw [e, hcomm.mul_pow, hyq, mul_one] at hxq
    exact hxq
  rw [← map_pow, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hwq
  exact ⟨_, hwq, by simp⟩

theorem normalizer_of_conj_mem {J : Subgroup G} {a : G} (ha3 : a ^ 3 = 1)
    (h : ∀ x ∈ J, a * x * a⁻¹ ∈ J) : a ∈ Subgroup.normalizer (J : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have h1 := h _ (h _ hx)
  have e : a * (a * (a * x * a⁻¹) * a⁻¹) * a⁻¹ = x := by
    have e1 : a * (a * (a * x * a⁻¹) * a⁻¹) * a⁻¹ = (a * a * a) * x * (a * a * a)⁻¹ := by group
    rw [e1, ← pow_three', ha3]
    group
  rw [← e]
  exact h1

theorem vpc_le_tof {M J : Subgroup G} {a : G} (hJ : Sec12a3.CompSet M J) :
    Sec12a3.Vpc a J ≤ Tof 3 M a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : J ⊓ Cg a ≤ alphaOf 3 M ⊓ Cg a := inf_le_inf_right _ (Sec12a3.compSet_le_alpha hJ)
  refine pCoreOf_le_of_normal 2 hle ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 ?_)
  intro g hg
  exact mem_normalizer_inf (alpha_le_normalizer hJ hg.1) (Subgroup.le_normalizer hg.2)

theorem tof_perm_props {M J : Subgroup G} {a : G} (hJ : Sec12a3.CompSet M J)
    (ι : (Sec12a3.JbarQ J ⧸ Subgroup.center (Sec12a3.JbarQ J)) ≃* ↥(alternatingGroup (Fin 7)))
    {πa : Perm (Fin 7)} (haN : a ∈ Subgroup.normalizer (J : Set G)) (hA : IsConj J ι a πa)
    {t : G} (ht : t ∈ Tof 3 M a) :
    permHom J ι ⟨t, alpha_le_normalizer hJ (Sec12a.tof_le_alphaOf M a ht)⟩ ∈
        alternatingGroup (Fin 7) ∧
      permHom J ι ⟨t, alpha_le_normalizer hJ (Sec12a.tof_le_alphaOf M a ht)⟩ * πa =
        πa * permHom J ι ⟨t, alpha_le_normalizer hJ (Sec12a.tof_le_alphaOf M a ht)⟩ ∧
      ∃ k : ℕ, (permHom J ι ⟨t, alpha_le_normalizer hJ (Sec12a.tof_le_alphaOf M a ht)⟩) ^ 2 ^ k = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨permHom_mem_alt hJ ι (Sec12a.tof_le_alphaOf M a ht), ?_, ?_⟩
  · rw [← permHom_eq ⟨a, haN⟩ hA, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Sec12a.tof_le_cg M a ht))
  · obtain ⟨k, hk⟩ := Sec12a3.exists_pow_eq_one_of_pCoreOf _ ht
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have e : (⟨t, alpha_le_normalizer hJ (Sec12a.tof_le_alphaOf M a ht)⟩ :
        ↥(Subgroup.normalizer (J : Set G))) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [e, map_one]

theorem tof_le_sup_vpc {M : Subgroup G} {a : G} (haM : a ∈ M) (ha3 : a ^ 3 = 1) :
    Tof 3 M a ≤ (pCoreOf 2 M ⊓ Tof 3 M a) ⊔
      ⨆ (J : Subgroup G) (_ : Sec12a3.CompSet M J ∧ Sec12a3.ThreeCycComp a J), Sec12a3.Vpc a J := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := (pCoreOf 2 M ⊓ Tof 3 M a) ⊔
    ⨆ (J : Subgroup G) (_ : Sec12a3.CompSet M J ∧ Sec12a3.ThreeCycComp a J), Sec12a3.Vpc a J
    with hR
  suffices key : ∀ F : Finset (Subgroup G), ∀ t ∈ Tof 3 M a,
      (∀ J, Sec12a3.CompSet M J → J ∉ F → ActTriv t J) → t ∈ R by
    intro t ht
    haveI := Fintype.ofFinite (Subgroup G)
    exact key Finset.univ t ht (fun J _ hJ => absurd (Finset.mem_univ J) hJ)
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro t ht htriv
    obtain ⟨n, hn⟩ := Sec12a3.exists_pow_eq_one_of_pCoreOf _ ht
    have h1 := mem_core_of_actTriv (Sec12a.tof_le_alphaOf M a ht)
      (fun J hJ => htriv J hJ (by simp)) (n := n) (by rw [hn]; exact one_mem _)
    exact (le_sup_left : pCoreOf 2 M ⊓ Tof 3 M a ≤ R) ⟨h1, ht⟩
  | insert J₀ F hJ₀F ih =>
    intro t ht htriv
    by_cases hJ₀ : Sec12a3.CompSet M J₀ ∧ Sec12a3.ThreeCycComp a J₀
    · have hJ₀' := hJ₀
      obtain ⟨hJ₀c, hnorm, ι, πa, hπa, hCB⟩ := hJ₀'
      have haN : a ∈ Subgroup.normalizer (J₀ : Set G) := normalizer_of_conj_mem ha3 hnorm
      have hA : IsConj J₀ ι a πa := isConj_of_conjsBy haN hCB
      obtain ⟨hvA, hvc, k, hvk⟩ := tof_perm_props hJ₀c ι haN hA ht
      obtain ⟨u, hu, hψu⟩ := exists_vpc_lift hJ₀c.2.2.2 ι haN ha3 hπa hA hvA hvc hvk
      have huT : (u : G) ∈ Tof 3 M a := vpc_le_tof hJ₀c hu
      have ht' : t * (u : G)⁻¹ ∈ Tof 3 M a := (Tof 3 M a).mul_mem ht ((Tof 3 M a).inv_mem huT)
      have h1 : t * (u : G)⁻¹ ∈ R := by
        refine ih (t * (u : G)⁻¹) ht' (fun J hJ hJF => ?_)
        have hTN : Tof 3 M a ≤ Subgroup.normalizer (J : Set G) :=
          (Sec12a.tof_le_alphaOf M a).trans (alpha_le_normalizer hJ)
        by_cases hJJ₀ : J = J₀
        · subst hJJ₀
          have huN : (u : G) ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer u.2
          have e : t * (u : G)⁻¹ = ((⟨t, hTN ht⟩ * (⟨(u : G), huN⟩)⁻¹ :
              ↥(Subgroup.normalizer (J : Set G))) : G) := rfl
          rw [e, actTriv_iff_permHom hJ.2.2.2 ι, map_mul, map_inv,
            permHom_eq ⟨(u : G), huN⟩ (isConj_of_mem ι u), hψu, mul_inv_cancel]
        · have h2 := htriv J hJ (by simp [Finset.mem_insert, hJJ₀, hJF])
          have huN : (u : G) ∈ Subgroup.normalizer (J : Set G) :=
            alpha_le_normalizer hJ (Sec12a3.compSet_le_alpha hJ₀c u.2)
          have h3 := actTriv_of_mem_other hJ hJ₀c (Ne.symm hJJ₀) u.2
          exact actTriv_mul (hTN ht) h2 (actTriv_inv huN h3)
      have e : t = t * (u : G)⁻¹ * u := by group
      rw [e]
      exact R.mul_mem h1 ((le_sup_right : _ ≤ R)
        ((le_iSup₂_of_le J₀ hJ₀ le_rfl :
          Sec12a3.Vpc a J₀ ≤ ⨆ (J : Subgroup G) (_ : Sec12a3.CompSet M J ∧
            Sec12a3.ThreeCycComp a J), Sec12a3.Vpc a J) hu))
    · refine ih t ht (fun J hJ hJF => ?_)
      by_cases hJJ₀ : J = J₀
      · subst hJJ₀
        exact tof_actTriv hJ haM ha3 (fun h => hJ₀ ⟨hJ, h⟩) t ht
      · exact htriv J hJ (by simp [Finset.mem_insert, hJJ₀, hJF])

theorem tof_comm_mem_core {M : Subgroup G} {a : G} (haM : a ∈ M) (ha3 : a ^ 3 = 1) {x y : G}
    (hx : x ∈ Tof 3 M a) (hy : y ∈ Tof 3 M a) : x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hw : x * y * x⁻¹ * y⁻¹ ∈ Tof 3 M a :=
    (Tof 3 M a).mul_mem ((Tof 3 M a).mul_mem ((Tof 3 M a).mul_mem hx hy) ((Tof 3 M a).inv_mem hx))
      ((Tof 3 M a).inv_mem hy)
  obtain ⟨n, hn⟩ := Sec12a3.exists_pow_eq_one_of_pCoreOf _ hw
  refine mem_core_of_actTriv (Sec12a.tof_le_alphaOf M a hw) (fun J hJ => ?_) (n := n)
    (by rw [hn]; exact one_mem _)
  have hTN : Tof 3 M a ≤ Subgroup.normalizer (J : Set G) :=
    (Sec12a.tof_le_alphaOf M a).trans (alpha_le_normalizer hJ)
  by_cases h3 : Sec12a3.ThreeCycComp a J
  · obtain ⟨hnorm, ι, πa, hπa, hCB⟩ := h3
    have haN : a ∈ Subgroup.normalizer (J : Set G) := normalizer_of_conj_mem ha3 hnorm
    have hA : IsConj J ι a πa := isConj_of_conjsBy haN hCB
    obtain ⟨hxA, hxc, hx2⟩ := tof_perm_props hJ ι haN hA hx
    obtain ⟨hyA, hyc, hy2⟩ := tof_perm_props hJ ι haN hA hy
    have hc := two_elems_comm hπa hxc (Equiv.Perm.mem_alternatingGroup.1 hxA) hx2 hyc
      (Equiv.Perm.mem_alternatingGroup.1 hyA) hy2
    have e : x * y * x⁻¹ * y⁻¹ = ((⟨x, hTN hx⟩ * ⟨y, hTN hy⟩ * (⟨x, hTN hx⟩)⁻¹ * (⟨y, hTN hy⟩)⁻¹ :
        ↥(Subgroup.normalizer (J : Set G))) : G) := rfl
    rw [e, actTriv_iff_permHom hJ.2.2.2 ι, map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [hc]
    group
  · have h1 := tof_actTriv hJ haM ha3 h3 x hx
    have h2 := tof_actTriv hJ haM ha3 h3 y hy
    exact actTriv_mul ((Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem
      (hTN hx) (hTN hy)) (inv_mem (hTN hx))) (actTriv_mul ((Subgroup.normalizer _).mul_mem
      (hTN hx) (hTN hy)) (actTriv_mul (hTN hx) h1 h2) (actTriv_inv (hTN hx) h1))
      (actTriv_inv (hTN hy) h2)

end Separation

section BlockDecomp

variable {G : Type} [Group G] [Finite G]

theorem pow_mod_three {e : G} (he3 : e ^ 3 = 1) (n : ℕ) : e ^ n = e ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, he3, one_pow, one_mul]

theorem mem_normalizer_of_gLBConj_le {g : G} {H : Subgroup G} (h : GLBConj g H ≤ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  refine Subgroup.eq_of_le_of_card_ge h ?_
  rw [GLBConj, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

omit [Finite G] in
theorem gLBConj_inf (g : G) (A B : Subgroup G) :
    GLBConj g (A ⊓ B) = GLBConj g A ⊓ GLBConj g B := by
  ext x
  simp only [mem_gLBConj, Subgroup.mem_inf]

omit [Finite G] in
theorem gLBConj_cg {e a : G} (hae : a * e = e * a) : GLBConj e (Cg a) = Cg a := by
  have h1 : e * a * e⁻¹ = a := by rw [← hae]; group
  have h2 : e⁻¹ * a * e = a := by rw [mul_assoc, hae]; group
  ext x
  rw [mem_gLBConj, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * a = e⁻¹ * ((e * x * e⁻¹) * (e * a * e⁻¹)) * e := by group
      _ = e⁻¹ * ((e * x * e⁻¹) * a) * e := by rw [h1]
      _ = e⁻¹ * (a * (e * x * e⁻¹)) * e := by rw [h]
      _ = (e⁻¹ * a * e) * x := by group
      _ = a * x := by rw [h2]
  · intro h
    calc e * x * e⁻¹ * a = e * (x * (e⁻¹ * a * e)) * e⁻¹ := by group
      _ = e * (x * a) * e⁻¹ := by rw [h2]
      _ = e * (a * x) * e⁻¹ := by rw [h]
      _ = (e * a * e⁻¹) * (e * x * e⁻¹) := by group
      _ = a * (e * x * e⁻¹) := by rw [h1]

omit [Finite G] in
theorem mem_normalizer_sup {g : G} {A B : Subgroup G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) : g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hA hB ⊢
  rw [GLBConj, Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) hA hB

omit [Finite G] in
theorem mem_normalizer_iSup {g : G} {ι : Sort*} {f : ι → Subgroup G}
    (h : ∀ i, g ∈ Subgroup.normalizer ((f i : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer (((⨆ i, f i) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  rw [GLBConj, Subgroup.map_iSup]
  exact iSup_congr fun i => mem_normalizer_iff_gLBConj_eq.1 (h i)

theorem gLBConj_wpc_le {e a : G} (he3 : e ^ 3 = 1) (hae : a * e = e * a) (J : Subgroup G) :
    GLBConj e (Sec12a3.Wpc e a J) ≤ Sec12a3.Wpc e a J := by
  unfold Sec12a3.Wpc
  rw [GLBConj, Subgroup.map_iSup]
  refine iSup_le fun k => ?_
  have h1 : (pCoreOf 2 (GLBConj (e ^ (k : ℕ)) J ⊓ Cg a)).map (MulAut.conj e⁻¹).toMonoidHom =
      pCoreOf 2 (GLBConj (e ^ (((k : ℕ) + 1) % 3)) J ⊓ Cg a) := by
    change GLBConj e (pCoreOf 2 (GLBConj (e ^ (k : ℕ)) J ⊓ Cg a)) = _
    rw [← pCoreOf_gLBConj, gLBConj_inf, gLBConj_gLBConj, gLBConj_cg hae, ← pow_succ,
      ← pow_mod_three he3]
  rw [h1]
  exact le_iSup_of_le (⟨((k : ℕ) + 1) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) le_rfl

theorem wpc_le_tof {M J : Subgroup G} {a e : G} (hJ : Sec12a3.CompSet M J) (heM : e ∈ M) :
    Sec12a3.Wpc e a J ≤ Tof 3 M a :=
  iSup_le fun k => vpc_le_tof (compSet_conj hJ (M.pow_mem heM _))

theorem vpc_le_wpc (e a : G) (J : Subgroup G) : Sec12a3.Vpc a J ≤ Sec12a3.Wpc e a J := by
  refine le_iSup_of_le (0 : Fin 3) ?_
  show pCoreOf 2 (J ⊓ Cg a) ≤ pCoreOf 2 (GLBConj (e ^ ((0 : Fin 3) : ℕ)) J ⊓ Cg a)
  simp [gLBConj_one]

theorem sup_inf_cg_le {X W : Subgroup G} {e : G} (he3 : e ^ 3 = 1)
    (heX : e ∈ Subgroup.normalizer (X : Set G)) (heW : e ∈ Subgroup.normalizer (W : Set G))
    (hWX : W ≤ Subgroup.normalizer (X : Set G)) (h2 : IsPGroup 2 ↥(X ⊓ W)) :
    (X ⊔ W) ⊓ Cg e ≤ (X ⊓ Cg e) ⊔ (W ⊓ Cg e) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro x ⟨hxXW, hxe⟩
  obtain ⟨u, hu, w, hw, rfl⟩ := Sec12a2.mem_sup_of_le_normalizer le_rfl hWX hxXW
  have heV : e ∈ Subgroup.normalizer ((X ⊓ W : Subgroup G) : Set G) := mem_normalizer_inf heX heW
  have hUV : Subgroup.zpowers e ≤ Subgroup.normalizer ((X ⊓ W : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le).2 heV
  have hwV : w ∈ Subgroup.normalizer ((X ⊓ W : Subgroup G) : Set G) :=
    mem_normalizer_inf (hWX hw) (Subgroup.le_normalizer hw)
  have hcond : ∀ u' ∈ Subgroup.zpowers e, u' * w * u'⁻¹ * w⁻¹ ∈ X ⊓ W := by
    intro u' hu'
    have hu'X : u' ∈ Subgroup.normalizer (X : Set G) := (Subgroup.zpowers_le.2 heX) hu'
    have hu'W : u' ∈ Subgroup.normalizer (W : Set G) := (Subgroup.zpowers_le.2 heW) hu'
    have hu'x : u' * (u * w) * u'⁻¹ = u * w := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu'
      have hc : Commute e (u * w) := (Subgroup.mem_centralizer_singleton_iff.1 hxe).symm
      rw [(hc.zpow_left k).eq]
      group
    refine ⟨?_, ?_⟩
    · have h1 : u' * u⁻¹ * u'⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 hu'X _).1 (X.inv_mem hu)
      have e1 : u' * w * u'⁻¹ * w⁻¹ = (u' * u⁻¹ * u'⁻¹) * (u' * (u * w) * u'⁻¹) * w⁻¹ := by group
      rw [e1, hu'x]
      have e2 : u' * u⁻¹ * u'⁻¹ * (u * w) * w⁻¹ = (u' * u⁻¹ * u'⁻¹) * u := by group
      rw [e2]
      exact X.mul_mem h1 hu
    · exact W.mul_mem ((Subgroup.mem_normalizer_iff.1 hu'W w).1 hw) (W.inv_mem hw)
  obtain ⟨v, hv, hfix⟩ := exists_fixed_in_coset' (p := 3) (zpowers_isPGroup_three he3)
    (not_three_dvd_of_two h2) hUV hwV hcond
  have hwv : w * v ∈ Cg e := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hfix e (Subgroup.mem_zpowers e)
    calc w * v * e = (e * (w * v) * e⁻¹) * e := by rw [h1]
      _ = e * (w * v) := by group
  have hwvW : w * v ∈ W := W.mul_mem hw hv.2
  have hu' : u * w * (w * v)⁻¹ ∈ X := by
    have h1 : w * v⁻¹ * w⁻¹ ∈ X := (hWX hw |> fun h => (Subgroup.mem_normalizer_iff.1 h _).1
      (X.inv_mem hv.1))
    have e1 : u * w * (w * v)⁻¹ = u * (w * v⁻¹ * w⁻¹) := by group
    rw [e1]
    exact X.mul_mem hu h1
  have hu'e : u * w * (w * v)⁻¹ ∈ Cg e := (Cg e).mul_mem hxe ((Cg e).inv_mem hwv)
  have e1 : u * w = (u * w * (w * v)⁻¹) * (w * v) := by group
  rw [e1]
  exact Subgroup.mul_mem _ ((le_sup_left : X ⊓ Cg e ≤ _) ⟨hu', hu'e⟩)
    ((le_sup_right : W ⊓ Cg e ≤ _) ⟨hwvW, hwv⟩)

theorem tof_inf_cg_le {M : Subgroup G} {a e : G} (haM : a ∈ M) (ha3 : a ^ 3 = 1) (heM : e ∈ M)
    (he3 : e ^ 3 = 1) (hae : a * e = e * a) :
    Tof 3 M a ⊓ Cg e ≤ (pCoreOf 2 M ⊓ Cg e) ⊔
      ⨆ (J : Subgroup G) (_ : Sec12a3.CompSet M J ∧ Sec12a3.ThreeCycComp a J),
        Sec12a3.Wpc e a J ⊓ Cg e := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := Tof 3 M a with hTdef
  set N := pCoreOf 2 M ⊓ T with hNdef
  have heCa : e ∈ Cg a := Subgroup.mem_centralizer_singleton_iff.2 hae.symm
  have heT : e ∈ Subgroup.normalizer (T : Set G) := Sec12a2.normalizer_tof M a heM heCa
  have heN : e ∈ Subgroup.normalizer (N : Set G) :=
    mem_normalizer_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M heM) heT
  have heW : ∀ J, e ∈ Subgroup.normalizer ((Sec12a3.Wpc e a J : Subgroup G) : Set G) :=
    fun J => mem_normalizer_of_gLBConj_le (gLBConj_wpc_le he3 hae J)
  set X : Finset (Subgroup G) → Subgroup G := fun F => N ⊔
    ⨆ (J : Subgroup G) (_ : J ∈ F ∧ Sec12a3.CompSet M J ∧ Sec12a3.ThreeCycComp a J),
      Sec12a3.Wpc e a J with hX
  set Rh : Finset (Subgroup G) → Subgroup G := fun F => (N ⊓ Cg e) ⊔
    ⨆ (J : Subgroup G) (_ : J ∈ F ∧ Sec12a3.CompSet M J ∧ Sec12a3.ThreeCycComp a J),
      Sec12a3.Wpc e a J ⊓ Cg e with hRh
  have hXT : ∀ F, X F ≤ T := fun F =>
    sup_le inf_le_right (iSup₂_le fun J hJ => wpc_le_tof hJ.2.1 heM)
  have heX : ∀ F, e ∈ Subgroup.normalizer ((X F : Subgroup G) : Set G) := fun F =>
    mem_normalizer_sup heN (mem_normalizer_iSup fun J => mem_normalizer_iSup fun _ => heW J)
  have hWX : ∀ F J, Sec12a3.CompSet M J →
      Sec12a3.Wpc e a J ≤ Subgroup.normalizer ((X F : Subgroup G) : Set G) := by
    intro F J hJ w hw
    have hwT := wpc_le_tof hJ heM hw
    have key : ∀ g ∈ T, ∀ x ∈ X F, g * x * g⁻¹ ∈ X F := by
      intro g hg x hx
      have hc := tof_comm_mem_core haM ha3 hg (hXT F hx)
      have hcT : g * x * g⁻¹ * x⁻¹ ∈ T :=
        T.mul_mem (T.mul_mem (T.mul_mem hg (hXT F hx)) (T.inv_mem hg)) (T.inv_mem (hXT F hx))
      have e1 : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
      rw [e1]
      exact (X F).mul_mem ((le_sup_left : N ≤ X F) ⟨hc, hcT⟩) hx
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key w hwT x, fun hx => ?_⟩
    have h1 := key w⁻¹ (T.inv_mem hwT) _ hx
    simpa [mul_assoc] using h1
  have hstep : ∀ F : Finset (Subgroup G), X F ⊓ Cg e ≤ Rh F := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      have h1 : X ∅ ≤ N := sup_le le_rfl (iSup₂_le fun J hJ => absurd hJ.1 (by simp))
      intro x hx
      exact (le_sup_left : N ⊓ Cg e ≤ Rh ∅) ⟨h1 hx.1, hx.2⟩
    | insert J₀ F hJ₀F ih =>
      have hRmono : Rh F ≤ Rh (insert J₀ F) := sup_le_sup_left (iSup₂_le fun J hJ =>
        le_iSup₂_of_le (f := fun J (_ : J ∈ insert J₀ F ∧ Sec12a3.CompSet M J ∧
          Sec12a3.ThreeCycComp a J) => Sec12a3.Wpc e a J ⊓ Cg e) J
          ⟨Finset.mem_insert_of_mem hJ.1, hJ.2⟩ le_rfl) _
      by_cases hJ₀ : Sec12a3.CompSet M J₀ ∧ Sec12a3.ThreeCycComp a J₀
      · have hle : X (insert J₀ F) ≤ X F ⊔ Sec12a3.Wpc e a J₀ := by
          refine sup_le (le_sup_left.trans le_sup_left) (iSup₂_le fun J hJ => ?_)
          rcases Finset.mem_insert.1 hJ.1 with rfl | hJF
          · exact le_sup_right
          · exact (le_iSup₂_of_le (f := fun J (_ : J ∈ F ∧ Sec12a3.CompSet M J ∧
              Sec12a3.ThreeCycComp a J) => Sec12a3.Wpc e a J) J ⟨hJF, hJ.2⟩ le_rfl).trans
              (le_sup_right.trans le_sup_left)
        have h2 : IsPGroup 2 ↥(X F ⊓ Sec12a3.Wpc e a J₀) :=
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le (inf_le_left.trans (hXT F))
        have hc := sup_inf_cg_le he3 (heX F) (heW J₀) (hWX F J₀ hJ₀.1) h2
        intro x hx
        have hx' : x ∈ (X F ⊔ Sec12a3.Wpc e a J₀) ⊓ Cg e := ⟨hle hx.1, hx.2⟩
        refine (sup_le (ih.trans hRmono) ?_) (hc hx')
        exact (le_iSup₂_of_le (f := fun J (_ : J ∈ insert J₀ F ∧ Sec12a3.CompSet M J ∧
          Sec12a3.ThreeCycComp a J) => Sec12a3.Wpc e a J ⊓ Cg e) J₀
          ⟨Finset.mem_insert_self J₀ F, hJ₀⟩ le_rfl).trans le_sup_right
      · have hle : X (insert J₀ F) ≤ X F := by
          refine sup_le le_sup_left (iSup₂_le fun J hJ => ?_)
          rcases Finset.mem_insert.1 hJ.1 with rfl | hJF
          · exact absurd hJ.2 hJ₀
          · exact (le_iSup₂_of_le (f := fun J (_ : J ∈ F ∧ Sec12a3.CompSet M J ∧
              Sec12a3.ThreeCycComp a J) => Sec12a3.Wpc e a J) J ⟨hJF, hJ.2⟩ le_rfl).trans
              le_sup_right
        intro x hx
        exact hRmono (ih ⟨hle hx.1, hx.2⟩)
  haveI := Fintype.ofFinite (Subgroup G)
  have hTX : T ≤ X Finset.univ := by
    refine (tof_le_sup_vpc haM ha3).trans (sup_le le_sup_left (iSup₂_le fun J hJ => ?_))
    exact (vpc_le_wpc e a J).trans ((le_iSup₂_of_le (f := fun J (_ : J ∈ Finset.univ ∧
      Sec12a3.CompSet M J ∧ Sec12a3.ThreeCycComp a J) => Sec12a3.Wpc e a J) J
      ⟨Finset.mem_univ J, hJ⟩ le_rfl).trans le_sup_right)
  have hfin : Rh Finset.univ ≤ (pCoreOf 2 M ⊓ Cg e) ⊔
      ⨆ (J : Subgroup G) (_ : Sec12a3.CompSet M J ∧ Sec12a3.ThreeCycComp a J),
        Sec12a3.Wpc e a J ⊓ Cg e :=
    sup_le_sup (inf_le_inf_right _ inf_le_left) (iSup₂_le fun J hJ =>
      le_iSup₂_of_le (f := fun J (_ : Sec12a3.CompSet M J ∧ Sec12a3.ThreeCycComp a J) =>
        Sec12a3.Wpc e a J ⊓ Cg e) J hJ.2 le_rfl)
  intro x hx
  exact hfin (hstep Finset.univ ⟨hTX hx.1, hx.2⟩)

end BlockDecomp

theorem blockDecomp_holds : Sec12a3.BlockDecomp := by
  intro G _ _ m B M E A a h _hT e he he1
  have hE : IsUniquenessTwoLocal 3 E M := h.pair.1.1.2
  obtain ⟨hAM, hAel, -⟩ : IsSCp 3 M A := h.pair.1.2.1.1.1
  have haM : a ∈ M := hAM h.ha.1
  have ha3 : a ^ 3 = 1 := hAel.2 a h.ha.1
  have heE : e ∈ E := (Subgroup.mem_inf.1 he).1
  have heA : e ∈ A := (Subgroup.mem_inf.1 he).2
  have heM : e ∈ M := hAM heA
  have he3 : e ^ 3 = 1 := hAel.2 e heA
  have hae : a * e = e * a := CFSG.Open.IsElemAbelian.comm hAel h.ha.1 heA
  refine (tof_inf_cg_le haM ha3 heM he3 hae).trans (sup_le_sup_right ?_ _)
  exact (Sec12a.pCoreOf_two_inf_le_alpha_inf (p := 3) M e).trans (hE.clause_b e heE he1)

section Quasisimple

theorem quotient_alt7 {D : Type} [Group D] [Finite D] (hperf : commutator D = ⊤)
    (ρ : D →* Perm (Fin 7)) (hρA : ∀ d, ρ d ∈ alternatingGroup (Fin 7))
    (hρS : ∀ σ ∈ alternatingGroup (Fin 7), ∃ d, ρ d = σ)
    (hK : ∀ k, ρ k = 1 → ∀ y, k * y * k⁻¹ * y⁻¹ ∈ CFSG.pCore 2 D) :
    CFSG.Open.IsQuasisimple (D ⧸ CFSG.pCore 2 D) ∧
      Nonempty (((D ⧸ CFSG.pCore 2 D) ⧸ Subgroup.center (D ⧸ CFSG.pCore 2 D)) ≃*
        ↥(alternatingGroup (Fin 7))) ∧
      ∀ x : D, (QuotientGroup.mk x : D ⧸ CFSG.pCore 2 D) ∈ Subgroup.center (D ⧸ CFSG.pCore 2 D) →
        ρ x = 1 := by
  set ρb : D ⧸ CFSG.pCore 2 D →* Perm (Fin 7) :=
    QuotientGroup.lift (CFSG.pCore 2 D) ρ (fun w hw => perm_kill_pCore ρ hρS hw) with hρb
  have hρb' : ∀ x : D, ρb (QuotientGroup.mk x) = ρ x := fun x => QuotientGroup.lift_mk _ _ x
  have hρbA : ∀ q, ρb q ∈ alternatingGroup (Fin 7) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hρb']
    exact hρA x
  set ρ' : D ⧸ CFSG.pCore 2 D →* ↥(alternatingGroup (Fin 7)) := ρb.codRestrict _ hρbA with hρ'
  have hsurj : Function.Surjective ρ' := by
    rintro ⟨σ, hσ⟩
    obtain ⟨x, hx⟩ := hρS σ hσ
    refine ⟨QuotientGroup.mk x, Subtype.ext ?_⟩
    show ρb (QuotientGroup.mk x) = σ
    rw [hρb', hx]
  have hcen : ∀ x : D, (QuotientGroup.mk x : D ⧸ CFSG.pCore 2 D) ∈
      Subgroup.center (D ⧸ CFSG.pCore 2 D) → ρ x = 1 := by
    intro x hx
    apply Sec12a3.eq_one_of_centralizes_alt7
    intro σ hσ
    obtain ⟨y, rfl⟩ := hρS σ hσ
    have h1 := Subgroup.mem_center_iff.1 hx (QuotientGroup.mk y)
    have h2 := congrArg ρb h1
    rw [map_mul, map_mul, hρb', hρb'] at h2
    exact h2.symm
  have hker : ρ'.ker = Subgroup.center (D ⧸ CFSG.pCore 2 D) := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : ρ x = 1 := by
        have h2 := congrArg Subtype.val h
        rw [← hρb']
        exact h2
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
      have h3 : (QuotientGroup.mk (x * y * x⁻¹ * y⁻¹) : D ⧸ CFSG.pCore 2 D) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (hK x h1 y)
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h3
      calc (QuotientGroup.mk y : D ⧸ CFSG.pCore 2 D) * QuotientGroup.mk x =
          ((QuotientGroup.mk x : D ⧸ CFSG.pCore 2 D) * QuotientGroup.mk y *
            (QuotientGroup.mk x)⁻¹ * (QuotientGroup.mk y)⁻¹)⁻¹ *
            (QuotientGroup.mk x * QuotientGroup.mk y) := by group
        _ = QuotientGroup.mk x * QuotientGroup.mk y := by rw [h3]; group
    · intro h
      apply Subtype.ext
      show ρb (QuotientGroup.mk x) = 1
      rw [hρb']
      exact hcen x h
  have e : ((D ⧸ CFSG.pCore 2 D) ⧸ Subgroup.center (D ⧸ CFSG.pCore 2 D)) ≃*
      ↥(alternatingGroup (Fin 7)) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ' hsurj)
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := S7.isSimple_Alt7
  refine ⟨⟨?_, e.isSimpleGroup⟩, ⟨e⟩, hcen⟩
  have h1 : (commutator D).map (QuotientGroup.mk' (CFSG.pCore 2 D)) =
      commutator (D ⧸ CFSG.pCore 2 D) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  rw [← h1, hperf, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

variable {G : Type} [Group G] [Finite G]

theorem isTwoPrimeComp_self_of_quasisimple (J : Subgroup G) (hp : ⁅J, J⁆ = J)
    (hq : CFSG.Open.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) : IsTwoPrimeComp J J := by
  refine ⟨le_rfl, IsSubnormal.refl J, hp, ?_⟩
  have htop : (J.subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) = ⊤ := by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  rw [htop]
  exact ⟨le_top, IsSubnormal.refl _,
    CFSG.ComponentClassification.Components.quasisimple_of_equiv Subgroup.topEquiv hq⟩

end Quasisimple

section Delta

variable {G : Type} [Group G] [Finite G]

@[expose] def diagY (M J₀ R : Subgroup G) : Subgroup G :=
  orbitProd M J₀ (R : Set G) ⊓ Subgroup.centralizer (R : Set G)

@[expose] noncomputable def diagΔ (M J₀ R : Subgroup G) : Subgroup G :=
  (derivedSeries ↥(diagY M J₀ R)
    (Classical.choose (exists_derivedSeries_stable ↥(diagY M J₀ R)))).map (diagY M J₀ R).subtype

theorem diagΔ_le_Y (M J₀ R : Subgroup G) : diagΔ M J₀ R ≤ diagY M J₀ R :=
  Subgroup.map_subtype_le _

theorem diagY_le_alpha {M J₀ R : Subgroup G} (hD : DiagData M J₀ R) :
    diagY M J₀ R ≤ alphaOf 3 M :=
  inf_le_left.trans (orbitProd_le_alpha hD.comp (fun x hx => hD.le hx))

theorem diagΔ_perfect (M J₀ R : Subgroup G) : ⁅diagΔ M J₀ R, diagΔ M J₀ R⁆ = diagΔ M J₀ R := by
  unfold diagΔ
  rw [← Subgroup.map_commutator, ← derivedSeries_succ,
    Classical.choose_spec (exists_derivedSeries_stable ↥(diagY M J₀ R))]

theorem normalizer_diagΔ {M J₀ R : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer ((diagY M J₀ R : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((diagΔ M J₀ R : Subgroup G) : Set G) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _ hg

theorem mem_normalizer_orbitProd {M J₀ : Subgroup G} {X : Set G} {g : G} (hgM : g ∈ M)
    (h : ∀ x ∈ X, g ∈ Subgroup.normalizer ((GLBConj x J₀ : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((orbitProd M J₀ X : Subgroup G) : Set G) :=
  mem_normalizer_sup (mem_normalizer_iSup fun x => mem_normalizer_iSup fun hx => h x hx)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hgM)

omit [Finite G] in
theorem mem_normalizer_centralizer {R : Subgroup G} {g : G} (h : ∀ r ∈ R, g * r = r * g) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (R : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hx r hr
    have cg : Commute r g := (h r hr).symm
    exact ((cg.mul_right (hx r hr)).mul_right cg.inv_right).eq
  · intro hx r hr
    have cg : Commute r g := (h r hr).symm
    have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [e]
    exact ((cg.inv_right.mul_right (hx r hr)).mul_right cg).eq

theorem diagΔ_surj {M J₀ R : Subgroup G} (hD : DiagData M J₀ R)
    (ι : (Sec12a3.JbarQ J₀ ⧸ Subgroup.center (Sec12a3.JbarQ J₀)) ≃* ↥(alternatingGroup (Fin 7))) :
    ∀ σ ∈ alternatingGroup (Fin 7), ∃ δ ∈ diagΔ M J₀ R,
      ∃ hδ : δ ∈ Subgroup.normalizer (J₀ : Set G), permHom J₀ ι ⟨δ, hδ⟩ = σ := by
  have hYα := diagY_le_alpha hD
  have hYN : diagY M J₀ R ≤ Subgroup.normalizer (J₀ : Set G) :=
    hYα.trans (alpha_le_normalizer hD.comp)
  set ρ : ↥(diagY M J₀ R) →* ↥(alternatingGroup (Fin 7)) :=
    ((permHom J₀ ι).comp (Subgroup.inclusion hYN)).codRestrict (alternatingGroup (Fin 7))
      (fun y => permHom_mem_alt hD.comp ι (hYα y.2)) with hρ
  have hρs : Function.Surjective ρ := by
    rintro ⟨σ, hσ⟩
    obtain ⟨z, hz, hzN, hzσ⟩ := diagSurj hD ι σ hσ
    exact ⟨⟨z, hz⟩, Subtype.ext hzσ⟩
  intro σ hσ
  have h1 := map_derivedSeries_eq hρs
    (Classical.choose (exists_derivedSeries_stable ↥(diagY M J₀ R)))
  rw [derivedSeries_alt7] at h1
  have h2 : (⟨σ, hσ⟩ : ↥(alternatingGroup (Fin 7))) ∈ (derivedSeries ↥(diagY M J₀ R)
      (Classical.choose (exists_derivedSeries_stable ↥(diagY M J₀ R)))).map ρ := by
    rw [h1]; exact Subgroup.mem_top _
  obtain ⟨d, hd, hdσ⟩ := Subgroup.mem_map.1 h2
  exact ⟨(d : G), ⟨d, hd, rfl⟩, hYN d.2, congrArg Subtype.val hdσ⟩

theorem diagY_actTriv {M J₀ R : Subgroup G} (hD : DiagData M J₀ R) {z : G}
    (hz : z ∈ diagY M J₀ R) (h : ActTriv z J₀) : ∀ K, Sec12a3.CompSet M K → ActTriv z K := by
  intro K hK
  by_cases hKR : ∃ r ∈ R, GLBConj r J₀ = K
  · obtain ⟨r, hr, rfl⟩ := hKR
    exact actTriv_conj ((Subgroup.mem_centralizer_iff.1 hz.2 r hr).symm) h
  · push Not at hKR
    exact actTriv_of_mem_orbitProd hD.comp hK (fun x hx => hD.le hx) hKR hz.1

theorem mem_pCore_of_mem_core {M X : Subgroup G} (hXM : X ≤ M) {x : ↥X}
    (hx : (x : G) ∈ pCoreOf 2 M) : x ∈ CFSG.pCore 2 ↥X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ((pCoreOf 2 M).subgroupOf X).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hXM g.2)) _).1 hn⟩
  have hN2 : IsPGroup 2 ↥((pCoreOf 2 M).subgroupOf X) := by
    intro y
    obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M ⟨_, Subgroup.mem_subgroupOf.1 y.2⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
  exact CFSG.LieType.BorelTits.le_pCore 2 hN hN2 (Subgroup.mem_subgroupOf.2 hx)

theorem diagΔ_kernel {M J₀ R : Subgroup G} (hD : DiagData M J₀ R)
    (ι : (Sec12a3.JbarQ J₀ ⧸ Subgroup.center (Sec12a3.JbarQ J₀)) ≃* ↥(alternatingGroup (Fin 7)))
    (hΔN : diagΔ M J₀ R ≤ Subgroup.normalizer (J₀ : Set G)) :
    (∀ k : ↥(diagΔ M J₀ R), ((permHom J₀ ι).comp (Subgroup.inclusion hΔN)) k = 1 →
      ∀ y : ↥(diagΔ M J₀ R), k * y * k⁻¹ * y⁻¹ ∈ CFSG.pCore 2 ↥(diagΔ M J₀ R)) ∧
    (∀ k : ↥(diagΔ M J₀ R), ((permHom J₀ ι).comp (Subgroup.inclusion hΔN)) k = 1 →
      ∀ K, Sec12a3.CompSet M K → ActTriv (k : G) K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΔα := (diagΔ_le_Y M J₀ R).trans (diagY_le_alpha hD)
  have hΔM : diagΔ M J₀ R ≤ M := hΔα.trans (Sec12a.alphaOf_le_self M)
  have htriv : ∀ k : ↥(diagΔ M J₀ R), ((permHom J₀ ι).comp (Subgroup.inclusion hΔN)) k = 1 →
      ∀ K, Sec12a3.CompSet M K → ActTriv (k : G) K := by
    intro k hk
    have h1 : ActTriv (k : G) J₀ := (actTriv_iff_permHom hD.comp.2.2.2 ι ⟨k, hΔN k.2⟩).2 hk
    exact diagY_actTriv hD (diagΔ_le_Y M J₀ R k.2) h1
  refine ⟨fun k hk y => ?_, htriv⟩
  have h2 := comm_core_of_actTriv (hΔM k.2) (htriv k hk) (hΔα y.2)
  exact mem_pCore_of_mem_core hΔM (by simpa using h2)

theorem diagΔ_quot {M J₀ R : Subgroup G} (hD : DiagData M J₀ R)
    (ι : (Sec12a3.JbarQ J₀ ⧸ Subgroup.center (Sec12a3.JbarQ J₀)) ≃* ↥(alternatingGroup (Fin 7))) :
    CFSG.Open.IsQuasisimple (↥(diagΔ M J₀ R) ⧸ CFSG.pCore 2 ↥(diagΔ M J₀ R)) ∧
      Sec12a4.IsOddCenterAltSeven (↥(diagΔ M J₀ R) ⧸ CFSG.pCore 2 ↥(diagΔ M J₀ R)) ∧
      pCoreOf 2 (diagΔ M J₀ R) ≤ pCoreOf 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΔα := (diagΔ_le_Y M J₀ R).trans (diagY_le_alpha hD)
  have hΔN : diagΔ M J₀ R ≤ Subgroup.normalizer (J₀ : Set G) :=
    hΔα.trans (alpha_le_normalizer hD.comp)
  set ρ := (permHom J₀ ι).comp (Subgroup.inclusion hΔN) with hρ
  haveI : Group.IsPerfect ↥(diagΔ M J₀ R) := Subgroup.isPerfect_iff.2 (diagΔ_perfect M J₀ R)
  have hperf : commutator ↥(diagΔ M J₀ R) = ⊤ := Group.isPerfect_def.1 inferInstance
  have hρA : ∀ d, ρ d ∈ alternatingGroup (Fin 7) := fun d => permHom_mem_alt hD.comp ι (hΔα d.2)
  have hρS : ∀ σ ∈ alternatingGroup (Fin 7), ∃ d, ρ d = σ := by
    intro σ hσ
    obtain ⟨δ, hδ, hδN, hδσ⟩ := diagΔ_surj hD ι σ hσ
    exact ⟨⟨δ, hδ⟩, hδσ⟩
  obtain ⟨hK, htriv⟩ := diagΔ_kernel hD ι hΔN
  obtain ⟨hq, ⟨e⟩, hcen⟩ := quotient_alt7 hperf ρ hρA hρS hK
  have hO : ∀ w : ↥(diagΔ M J₀ R), w ∈ CFSG.pCore 2 ↥(diagΔ M J₀ R) → (w : G) ∈ pCoreOf 2 M := by
    intro w hw
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(diagΔ M J₀ R))) ⟨w, hw⟩
    exact mem_core_of_actTriv (hΔα w.2) (htriv w (perm_kill_pCore ρ hρS hw)) (n := n)
      (by rw [show (w : G) ^ 2 ^ n = 1 by simpa using congrArg Subtype.val (congrArg Subtype.val hn)];
          exact one_mem _)
  refine ⟨hq, ⟨hq.1, ?_, ⟨e⟩⟩, ?_⟩
  · by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hodd)
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (z : ↥(diagΔ M J₀ R) ⧸ CFSG.pCore 2 ↥(diagΔ M J₀ R))
    have hk1 : ρ k = 1 := hcen k (hk ▸ z.2)
    have hz2 : (z : ↥(diagΔ M J₀ R) ⧸ CFSG.pCore 2 ↥(diagΔ M J₀ R)) ^ 2 = 1 := by
      have h1 := pow_orderOf_eq_one z
      rw [hz] at h1
      simpa using congrArg Subtype.val h1
    have hk2 : k ^ 2 ∈ CFSG.pCore 2 ↥(diagΔ M J₀ R) := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hk, hz2]
    have hkO : (k : G) ∈ pCoreOf 2 M := by
      refine mem_core_of_actTriv (hΔα k.2) (htriv k hk1) (n := 1) ?_
      simpa using hO _ hk2
    have hkP : k ∈ CFSG.pCore 2 ↥(diagΔ M J₀ R) :=
      mem_pCore_of_mem_core (hΔα.trans (Sec12a.alphaOf_le_self M)) hkO
    have hz1 : (z : ↥(diagΔ M J₀ R) ⧸ CFSG.pCore 2 ↥(diagΔ M J₀ R)) = 1 := by
      rw [← hk]
      exact (QuotientGroup.eq_one_iff k).2 hkP
    have : z = 1 := Subtype.ext hz1
    rw [this, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · rintro _ ⟨w, hw, rfl⟩
    exact hO w hw

end Delta

section DiagLift

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_diagY_of {M J₀ R : Subgroup G} (hD : DiagData M J₀ R) {g : G}
    (hgM : g ∈ M) (hgN : g ∈ Subgroup.normalizer (J₀ : Set G)) (hgR : ∀ r ∈ R, g * r = r * g) :
    g ∈ Subgroup.normalizer ((diagY M J₀ R : Subgroup G) : Set G) := by
  refine mem_normalizer_inf (mem_normalizer_orbitProd hgM fun x hx => ?_)
    (mem_normalizer_centralizer hgR)
  rw [mem_normalizer_iff_gLBConj_eq] at hgN ⊢
  rw [gLBConj_gLBConj, ← hgR x hx, ← gLBConj_gLBConj, hgN]

theorem mem_normalizer_diagY_of_alpha {M J₀ R : Subgroup G} (hD : DiagData M J₀ R) {g : G}
    (hg : g ∈ alphaOf 3 M) (hgR : ∀ r ∈ R, g * r = r * g) :
    g ∈ Subgroup.normalizer ((diagY M J₀ R : Subgroup G) : Set G) :=
  mem_normalizer_inf (mem_normalizer_orbitProd (Sec12a.alphaOf_le_self M hg) fun x hx =>
    alpha_le_normalizer (compSet_conj hD.comp (hD.le hx)) hg) (mem_normalizer_centralizer hgR)

theorem exists_diagΔ_lift {M J₀ R : Subgroup G} (hD : DiagData M J₀ R)
    (ι : (Sec12a3.JbarQ J₀ ⧸ Subgroup.center (Sec12a3.JbarQ J₀)) ≃* ↥(alternatingGroup (Fin 7)))
    {a : G} {πa : Perm (Fin 7)} (haM : a ∈ M) (ha3 : a ^ 3 = 1)
    (haN : a ∈ Subgroup.normalizer (J₀ : Set G)) (haR : ∀ r ∈ R, a * r = r * a)
    (hπa : πa.cycleType = {3}) (hA : IsConj J₀ ι a πa) {v : Perm (Fin 7)}
    (hvA : v ∈ alternatingGroup (Fin 7)) (hvc : v * πa = πa * v) {k : ℕ} (hvk : v ^ 2 ^ k = 1) :
    ∃ y ∈ pCoreOf 2 (diagΔ M J₀ R ⊓ Cg a), ∃ hy : y ∈ Subgroup.normalizer (J₀ : Set G),
      permHom J₀ ι ⟨y, hy⟩ = v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ₀ := hD.comp
  set Δ := diagΔ M J₀ R with hΔ
  have hΔY := diagΔ_le_Y M J₀ R
  have hΔα := hΔY.trans (diagY_le_alpha hD)
  have hΔM : Δ ≤ M := hΔα.trans (Sec12a.alphaOf_le_self M)
  have hΔN : Δ ≤ Subgroup.normalizer (J₀ : Set G) := hΔα.trans (alpha_le_normalizer hJ₀)
  set ρ := (permHom J₀ ι).comp (Subgroup.inclusion hΔN) with hρ
  obtain ⟨-, htriv⟩ := diagΔ_kernel hD ι hΔN
  obtain ⟨δ, hδ, hδN, hδv⟩ := diagΔ_surj hD ι v hvA
  have hρδ : ρ ⟨δ, hδ⟩ = v := hδv
  obtain ⟨y₀, ⟨n, hn⟩, hy₀⟩ := exists_two_elem_lift ρ ⟨δ, hδ⟩ (k := k) (by rw [hρδ]; exact hvk)
  rw [hρδ] at hy₀
  have hy₀n : (y₀ : G) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have haΔ : a ∈ Subgroup.normalizer ((Δ : Subgroup G) : Set G) :=
    normalizer_diagΔ (mem_normalizer_diagY_of hD haM haN haR)
  have hay : a * (y₀ : G) * a⁻¹ ∈ Δ := (Subgroup.mem_normalizer_iff.1 haΔ _).1 y₀.2
  have hψ : permHom J₀ ι ⟨a * (y₀ : G) * a⁻¹, hΔN hay⟩ = v := by
    have h1 : (⟨a * (y₀ : G) * a⁻¹, hΔN hay⟩ : ↥(Subgroup.normalizer (J₀ : Set G))) =
        ⟨a, haN⟩ * ⟨y₀, hΔN y₀.2⟩ * (⟨a, haN⟩)⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv, permHom_eq ⟨a, haN⟩ hA]
    change πa * ρ y₀ * πa⁻¹ = v
    rw [hy₀]
    calc πa * v * πa⁻¹ = (v * πa) * πa⁻¹ := by rw [hvc]
      _ = v := by group
  have hyO : a * (y₀ : G) * a⁻¹ * (y₀ : G)⁻¹ ∈ pCoreOf 2 M := by
    have hm : a * (y₀ : G) * a⁻¹ * (y₀ : G)⁻¹ ∈ Δ := Δ.mul_mem hay (Δ.inv_mem y₀.2)
    have hρ1 : ρ ⟨_, hm⟩ = 1 := by
      have h1 : (⟨_, hm⟩ : ↥Δ) = ⟨_, hay⟩ * y₀⁻¹ := rfl
      rw [h1, map_mul, map_inv]
      change permHom J₀ ι ⟨a * (y₀ : G) * a⁻¹, hΔN hay⟩ * (ρ y₀)⁻¹ = 1
      rw [hψ, hy₀, mul_inv_cancel]
    have h2 := htriv ⟨_, hm⟩ hρ1
    have hx2 : ∃ m : ℕ, (a * (y₀ : G) * a⁻¹) ^ 2 ^ m = 1 := ⟨n, by rw [conj_pow, hy₀n]; group⟩
    exact mul_inv_mem_core (hΔα hay) (hΔα y₀.2) hx2 ⟨n, hy₀n⟩ h2
  have hV2 : IsPGroup 2 ↥(pCoreOf 2 M ⊓ Δ) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left
  obtain ⟨w, hw, hyw⟩ := exists_mul_mem_centralizer (p := 3) (zpowers_isPGroup_three ha3)
    (not_three_dvd_of_two hV2)
    (mem_normalizer_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M haM) haΔ)
    (mem_normalizer_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hΔM y₀.2))
      (Subgroup.le_normalizer y₀.2))
    ⟨hyO, Δ.mul_mem hay (Δ.inv_mem y₀.2)⟩
  have hyΔ : (y₀ : G) * w ∈ Δ := Δ.mul_mem y₀.2 hw.2
  have hyN : (y₀ : G) * w ∈ Subgroup.normalizer (J₀ : Set G) := hΔN hyΔ
  have hwN : w ∈ Subgroup.normalizer (J₀ : Set G) := core_le_normalizer hJ₀ hw.1
  have hyv : permHom J₀ ι ⟨(y₀ : G) * w, hyN⟩ = v := by
    have h1 : (⟨(y₀ : G) * w, hyN⟩ : ↥(Subgroup.normalizer (J₀ : Set G))) =
        ⟨y₀, hΔN y₀.2⟩ * ⟨w, hwN⟩ := rfl
    rw [h1, map_mul, permHom_eq ⟨w, hwN⟩ (isConj_one_of_actTriv ι (actTriv_of_mem_core hJ₀ hw.1)),
      mul_one]
    exact hy₀
  have hy2 : ∃ m : ℕ, ((y₀ : G) * w) ^ 2 ^ m = 1 := by
    have hu : (y₀ : G) * w * (y₀ : G)⁻¹ ∈ pCoreOf 2 M :=
      (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
        (hΔM y₀.2)) _).1 hw.1
    have h1 := mul_pow_mul_inv_mem hu
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hΔM y₀.2)) (2 ^ n)
    have e : (y₀ : G) * w * (y₀ : G)⁻¹ * y₀ = (y₀ : G) * w := by group
    rw [e, hy₀n, inv_one, mul_one] at h1
    obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M ⟨_, h1⟩
    refine ⟨n + j, ?_⟩
    rw [pow_add, pow_mul]
    simpa using congrArg Subtype.val hj
  refine ⟨(y₀ : G) * w, ?_, hyN, hyv⟩
  refine two_elem_mem_pCoreOf (Y := Δ ⊓ Cg a)
    ((permHom J₀ ι).comp (Subgroup.inclusion (inf_le_left.trans hΔN))) hπa ?_ ?_
    (L := pCoreOf 2 M ⊓ (Δ ⊓ Cg a)) inf_le_right
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left) ?_ ?_ ⟨hyΔ, hyw⟩ hy2
  · intro y'
    exact permHom_mem_alt hJ₀ ι (hΔα y'.2.1)
  · intro y'
    rw [← permHom_eq ⟨a, haN⟩ hA]
    change permHom J₀ ι _ * permHom J₀ ι _ = permHom J₀ ι _ * permHom J₀ ι _
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 y'.2.2)
  · rintro y' ⟨hy'O, -⟩
    exact permHom_eq _ (isConj_one_of_actTriv ι (actTriv_of_mem_core hJ₀ hy'O))
  · intro k' y' hk'
    have h1 := htriv ⟨k', k'.2.1⟩ hk'
    exact ⟨comm_core_of_actTriv (hΔM k'.2.1) h1 (hΔα y'.2.1), (k' * y' * k'⁻¹ * y'⁻¹).2⟩

end DiagLift

theorem diagPiece_holds : Sec12a3.DiagPiece := by
  intro G _ _ m B M E A a h e he he1 J hJ hJT hcase
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : IsUniquenessTwoLocal 3 E M := h.pair.1.1.2
  obtain ⟨hAM, hAel, -⟩ : IsSCp 3 M A := h.pair.1.2.1.1.1
  have haM : a ∈ M := hAM h.ha.1
  have ha3 : a ^ 3 = 1 := hAel.2 a h.ha.1
  have heE : e ∈ E := (Subgroup.mem_inf.1 he).1
  have heA : e ∈ A := (Subgroup.mem_inf.1 he).2
  have heM : e ∈ M := hAM heA
  have he3 : e ^ 3 = 1 := hAel.2 e heA
  have hae : a * e = e * a := CFSG.Open.IsElemAbelian.comm hAel h.ha.1 heA
  obtain ⟨hnorm, ι, πa, hπa, hCB⟩ := hJT
  have haN := normalizer_of_conj_mem ha3 hnorm
  have hA := isConj_of_conjsBy haN hCB
  have hcase' : GLBConj e J ≠ J ∨ (e ∈ Subgroup.normalizer (J : Set G) ∧ ActTriv e J) := by
    rcases hcase with hne | ⟨heN, ι', πe, hCBe, hπe1, -⟩
    · exact Or.inl hne
    · refine Or.inr ⟨heN, actTriv_of_isConj_one hJ.2.2.2 ι' heN ?_⟩
      rw [← hπe1]
      exact isConj_of_conjsBy heN hCBe
  have hD := diagData_zpowers hJ heM he3 hcase'
  set Δ := diagΔ M J (Subgroup.zpowers e) with hΔ
  have hΔY := diagΔ_le_Y M J (Subgroup.zpowers e)
  have hΔα := hΔY.trans (diagY_le_alpha hD)
  have hΔe : Δ ≤ Cg e := fun x hx => mem_centralizer_zpowers_iff.1 (hΔY hx).2
  obtain ⟨hq, -, -⟩ := diagΔ_quot hD ι
  have hcomm_e : ∀ g ∈ Cg e, ∀ r ∈ Subgroup.zpowers e, g * r = r * g := by
    intro g hg r hr
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 hg) k).eq
  refine ⟨Δ, hΔα, ?_, ?_⟩
  · apply hE.clause_f rfl e heE he1
    have hle : Δ ≤ alphaOf 3 M ⊓ Cg e := le_inf hΔα hΔe
    refine isTwoPrimeComp_of_le (isTwoPrimeComp_self_of_quasisimple Δ
      (diagΔ_perfect M J (Subgroup.zpowers e)) hq) hle ?_
    refine Sec12a2.isSubnormal_of_normal hle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 ?_)
    intro g hg
    exact normalizer_diagΔ (mem_normalizer_diagY_of_alpha hD hg.1 (hcomm_e g hg.2))
  · intro x hx
    obtain ⟨hxW, hxe⟩ := Subgroup.mem_inf.1 hx
    have hxT : x ∈ Tof 3 M a := wpc_le_tof hJ heM hxW
    have hxY : x ∈ diagY M J (Subgroup.zpowers e) :=
      ⟨wpc_le_orbitProd hxW, mem_centralizer_zpowers_iff.2 hxe⟩
    obtain ⟨hvA, hvc, k, hvk⟩ := tof_perm_props hJ ι haN hA hxT
    have haR : ∀ r ∈ Subgroup.zpowers e, a * r = r * a :=
      hcomm_e a (Subgroup.mem_centralizer_singleton_iff.2 hae)
    obtain ⟨y, hy, hyN, hyv⟩ := exists_diagΔ_lift hD ι haM ha3 haN haR hπa hA hvA hvc hvk
    have hyΔ : y ∈ Δ := (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hy).1
    have hxα := Sec12a.tof_le_alphaOf M a hxT
    have hxN : x ∈ Subgroup.normalizer (J : Set G) := alpha_le_normalizer hJ hxα
    have hxyY : x * y⁻¹ ∈ diagY M J (Subgroup.zpowers e) :=
      (diagY M J (Subgroup.zpowers e)).mul_mem hxY ((diagY M J (Subgroup.zpowers e)).inv_mem
        (hΔY hyΔ))
    have hxyJ : ActTriv (x * y⁻¹) J := by
      have e1 : x * y⁻¹ = ((⟨x, hxN⟩ * (⟨y, hyN⟩)⁻¹ : ↥(Subgroup.normalizer (J : Set G))) : G) :=
        rfl
      rw [e1, actTriv_iff_permHom hJ.2.2.2 ι, map_mul, map_inv, hyv]
      exact mul_inv_cancel _
    have hxyO := mul_inv_mem_core hxα (hΔα hyΔ) (Sec12a3.exists_pow_eq_one_of_pCoreOf _ hxT)
      (Sec12a3.exists_pow_eq_one_of_pCoreOf _ hy) (diagY_actTriv hD hxyY hxyJ)
    have hxyC : x * y⁻¹ ∈ Cg e := (Cg e).mul_mem hxe ((Cg e).inv_mem (hΔe hyΔ))
    have e1 : x = (x * y⁻¹) * y := by group
    rw [e1]
    exact Subgroup.mul_mem _ ((le_sup_left : pCoreOf 2 (Cg e) ≤ _)
      (((Sec12a.pCoreOf_two_inf_le_alpha_inf (p := 3) M e).trans (hE.clause_b e heE he1))
        ⟨hxyO, hxyC⟩)) ((le_sup_right : pCoreOf 2 (Δ ⊓ Cg a) ≤ _) hy)

theorem blockLayer_holds : Sec12a2.BlockLayer :=
  Sec12a3.blockLayer_of_inputs blockDecomp_holds diagPiece_holds

theorem lemma122_i_ii_holds : Lemma122_i_iiStatement :=
  lemma122_i_ii_of_caseB (Sec12a2.caseB122i_of_inputs blockLayer_holds)

section BlockIII

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_of_pow3 {b c : G} (hb3 : b ^ 3 = 1) (hc : c ∈ Subgroup.zpowers b)
    (hc1 : c ≠ 1) : b ∈ Subgroup.zpowers c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  have hc3 : (b ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
  have hb1 : b ≠ 1 := fun h => hc1 (by rw [h, one_zpow])
  have hcard : Nat.card ↥(Subgroup.zpowers b) ≤ Nat.card ↥(Subgroup.zpowers (b ^ k)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hb3 hb1, orderOf_eq_prime hc3 hc1]
  rw [Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hc) hcard]
  exact Subgroup.mem_zpowers b

theorem le_normalizer_of_elemAbelian {A S : Subgroup G} (hAel : CFSG.Open.IsElemAbelian 3 A)
    (hSA : S ≤ A) : A ≤ Subgroup.normalizer (S : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [CFSG.Open.IsElemAbelian.comm hAel hx (hSA hy)]
    simpa using hy
  · intro hy
    have hz := hSA hy
    have e : y = x * y * x⁻¹ := by
      calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
        _ = (x * y * x⁻¹) * x⁻¹ * x := by
          rw [CFSG.Open.IsElemAbelian.comm hAel (A.inv_mem hx) hz]
        _ = x * y * x⁻¹ := by group
    rw [e]
    exact hy

theorem exists_D₁ {A J₀ : Subgroup G} {a : G} (hAel : CFSG.Open.IsElemAbelian 3 A)
    (haA : a ∈ A) (haN : a ∈ Subgroup.normalizer (J₀ : Set G))
    (hGood : ∀ d ∈ A, d ∈ Subgroup.normalizer (J₀ : Set G) → ∃ j : ℕ, ActTriv (d * a ^ j) J₀) :
    ∃ D₁ : Subgroup G, D₁ ≤ A ∧ A ≤ D₁ ⊔ Subgroup.zpowers a ∧
      ∀ r ∈ D₁, r ∈ Subgroup.normalizer (J₀ : Set G) → ActTriv r J₀ := by
  classical
  haveI := Fintype.ofFinite (Subgroup G)
  set P : Subgroup G → Prop := fun S =>
    S ≤ A ∧ ∀ r ∈ S, r ∈ Subgroup.normalizer (J₀ : Set G) → ActTriv r J₀ with hP
  have hne : (Finset.univ.filter P).Nonempty := ⟨⊥, Finset.mem_filter.2 ⟨Finset.mem_univ _,
    bot_le, fun r hr _ => by rw [Subgroup.mem_bot.1 hr]; exact actTriv_one J₀⟩⟩
  obtain ⟨D₁, hD₁, hmax⟩ := Finset.exists_max_image _ (fun S : Subgroup G => Nat.card ↥S) hne
  obtain ⟨-, hD₁A, hD₁t⟩ := Finset.mem_filter.1 hD₁
  have hD₀ : A ⊓ actTrivSub J₀ ≤ D₁ := by
    have hS : P (D₁ ⊔ (A ⊓ actTrivSub J₀)) := by
      refine ⟨sup_le hD₁A inf_le_left, fun r hr hrN => ?_⟩
      obtain ⟨u, hu, d, hd, rfl⟩ := Sec12a2.mem_sup_of_le_normalizer (K := A) inf_le_left
        (le_normalizer_of_elemAbelian hAel hD₁A) hr
      have huN : u ∈ Subgroup.normalizer (J₀ : Set G) := by
        have e : u = (u * d) * d⁻¹ := by group
        rw [e]
        exact Subgroup.mul_mem _ hrN (Subgroup.inv_mem _ hd.2.1)
      exact actTriv_mul huN (hD₁t u hu huN) hd.2.2
    have hcard := hmax _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hS⟩)
    have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : D₁ ≤ D₁ ⊔ (A ⊓ actTrivSub J₀)) hcard
    rw [heq]
    exact le_sup_right
  refine ⟨D₁, hD₁A, fun b hbA => ?_, hD₁t⟩
  by_contra hb
  have hS : P (D₁ ⊔ Subgroup.zpowers b) := by
    refine ⟨sup_le hD₁A ((Subgroup.zpowers_le).2 hbA), fun r hr hrN => ?_⟩
    obtain ⟨s, hs, c, hc, rfl⟩ := Sec12a2.mem_sup_of_le_normalizer (K := A)
      ((Subgroup.zpowers_le).2 hbA) (le_normalizer_of_elemAbelian hAel hD₁A) hr
    have hcA : c ∈ A := (Subgroup.zpowers_le.2 hbA) hc
    obtain ⟨j, hj⟩ := hGood (s * c) (A.mul_mem (hD₁A hs) hcA) hrN
    have hra : s * c * a ^ j ∈ D₁ := hD₀ ⟨A.mul_mem (A.mul_mem (hD₁A hs) hcA) (A.pow_mem haA j),
      Subgroup.mul_mem _ hrN (Subgroup.pow_mem _ haN j), hj⟩
    by_cases hc1 : c = 1
    · rw [hc1, mul_one] at hrN ⊢
      exact hD₁t s hs hrN
    · exfalso
      apply hb
      have hcD : c ∈ D₁ ⊔ Subgroup.zpowers a := by
        have e : c = s⁻¹ * (s * c * a ^ j) * (a ^ j)⁻¹ := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ((le_sup_left : D₁ ≤ _) (D₁.inv_mem hs))
          ((le_sup_left : D₁ ≤ _) hra)) ((le_sup_right : Subgroup.zpowers a ≤ _)
            (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) j)))
      exact (Subgroup.zpowers_le.2 hcD) (mem_zpowers_of_pow3 (hAel.2 b hbA) hc hc1)
  have hlt : D₁ < D₁ ⊔ Subgroup.zpowers b := by
    refine lt_of_le_of_ne le_sup_left fun h => hb ?_
    have hbD : b ∈ D₁ := by
      rw [h]
      exact (le_sup_right : Subgroup.zpowers b ≤ _) (Subgroup.mem_zpowers b)
    exact (le_sup_left : D₁ ≤ _) hbD
  exact absurd (hmax _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hS⟩))
    (not_le.2 (Subgroup.card_lt_of_lt hlt))

theorem card_le_three_mul {A D : Subgroup G} {a : G} (ha3 : a ^ 3 = 1)
    (hAD : A ≤ D ⊔ Subgroup.zpowers a)
    (hDa : Subgroup.zpowers a ≤ Subgroup.normalizer (D : Set G)) :
    Nat.card A ≤ 3 * Nat.card D := by
  set f : ↥D × Fin 3 → ↥(D ⊔ Subgroup.zpowers a) := fun q => ⟨(q.1 : G) * a ^ (q.2 : ℕ),
    Subgroup.mul_mem _ ((le_sup_left : D ≤ _) q.1.2) ((le_sup_right : Subgroup.zpowers a ≤ _)
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _))⟩ with hf
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨d, hd, c, hc, rfl⟩ := Sec12a2.mem_sup_of_le_normalizer le_rfl hDa hx
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers).2 hc
    refine ⟨(⟨d, hd⟩, ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩), Subtype.ext ?_⟩
    show d * a ^ (n % 3) = d * c
    rw [← hn, ← pow_mod_three ha3]
  have h1 := Nat.card_le_card_of_surjective f hsurj
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h1
  calc Nat.card A ≤ Nat.card ↥(D ⊔ Subgroup.zpowers a) := Subgroup.card_le_of_le hAD
    _ ≤ Nat.card ↥D * 3 := h1
    _ = 3 * Nat.card D := mul_comm _ _

theorem actTriv_conj_both {J : Subgroup G} {g : G} (r : G) (h : ActTriv g J) :
    ActTriv (r⁻¹ * g * r) (GLBConj r J) := by
  intro y hy
  rw [mem_gLBConj] at hy
  rw [pCoreOf_gLBConj, mem_gLBConj]
  have e : r * (r⁻¹ * g * r * y * (r⁻¹ * g * r)⁻¹ * y⁻¹) * r⁻¹ =
      g * (r * y * r⁻¹) * g⁻¹ * (r * y * r⁻¹)⁻¹ := by group
  rw [e]
  exact h _ hy

theorem actTriv_conj_mem {J : Subgroup G} {t u : G} (h : ActTriv t J)
    (hu : u ∈ Subgroup.normalizer (J : Set G)) : ActTriv (u * t * u⁻¹) J := by
  intro y hy
  have hy' : u⁻¹ * y * u⁻¹⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 (inv_mem hu) y).1 hy
  have hO := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J hu
  have h3 := (Subgroup.mem_normalizer_iff.1 hO _).1 (h _ hy')
  have e : u * t * u⁻¹ * y * (u * t * u⁻¹)⁻¹ * y⁻¹ =
      u * (t * (u⁻¹ * y * u⁻¹⁻¹) * t⁻¹ * (u⁻¹ * y * u⁻¹⁻¹)⁻¹) * u⁻¹ := by group
  rw [e]
  exact h3

theorem mem_vpc_conj {J : Subgroup G} {a r u : G} (har : a * r = r * a)
    (hu : u ∈ Sec12a3.Vpc a J) : r⁻¹ * u * r ∈ Sec12a3.Vpc a (GLBConj r J) := by
  show r⁻¹ * u * r ∈ pCoreOf 2 (GLBConj r J ⊓ Cg a)
  rw [← gLBConj_cg har, ← gLBConj_inf, pCoreOf_gLBConj, mem_gLBConj]
  rw [show r * (r⁻¹ * u * r) * r⁻¹ = u by group]
  exact hu

theorem diag_pcore_le_tof {M J₀ R : Subgroup G} (hD : DiagData M J₀ R)
    (ι : (Sec12a3.JbarQ J₀ ⧸ Subgroup.center (Sec12a3.JbarQ J₀)) ≃* ↥(alternatingGroup (Fin 7)))
    {a : G} {πa : Perm (Fin 7)} (haM : a ∈ M) (ha3 : a ^ 3 = 1)
    (haN : a ∈ Subgroup.normalizer (J₀ : Set G)) (haR : ∀ r ∈ R, a * r = r * a)
    (hπa : πa.cycleType = {3}) (hA : IsConj J₀ ι a πa) :
    pCoreOf 2 (diagΔ M J₀ R ⊓ Cg a) ≤ Tof 3 M a := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro y hy
  have hJ₀ := hD.comp
  have hyΔa := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hy
  have hyY := diagΔ_le_Y M J₀ R hyΔa.1
  have hyα := diagY_le_alpha hD hyY
  have hyM := Sec12a.alphaOf_le_self M hyα
  obtain ⟨n, hn⟩ := Sec12a3.exists_pow_eq_one_of_pCoreOf _ hy
  have hyN : y ∈ Subgroup.normalizer (J₀ : Set G) := alpha_le_normalizer hJ₀ hyα
  have hvc : permHom J₀ ι ⟨y, hyN⟩ * πa = πa * permHom J₀ ι ⟨y, hyN⟩ := by
    rw [← permHom_eq ⟨a, haN⟩ hA, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hyΔa.2)
  have hvk : (permHom J₀ ι ⟨y, hyN⟩) ^ 2 ^ n = 1 := by
    rw [← map_pow]
    have e : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (J₀ : Set G))) ^ 2 ^ n = 1 :=
      Subtype.ext (by simpa using hn)
    rw [e, map_one]
  obtain ⟨u₀, hu₀, hψu₀⟩ := exists_vpc_lift hJ₀.2.2.2 ι haN ha3 hπa hA
    (permHom_mem_alt hJ₀ ι hyα) hvc hvk
  have hu₀N : (u₀ : G) ∈ Subgroup.normalizer (J₀ : Set G) := Subgroup.le_normalizer u₀.2
  have hyu₀ : ActTriv (y * (u₀ : G)⁻¹) J₀ := by
    have e : y * (u₀ : G)⁻¹ = ((⟨y, hyN⟩ * (⟨(u₀ : G), hu₀N⟩)⁻¹ :
        ↥(Subgroup.normalizer (J₀ : Set G))) : G) := rfl
    rw [e, actTriv_iff_permHom hJ₀.2.2.2 ι, map_mul, map_inv,
      permHom_eq ⟨(u₀ : G), hu₀N⟩ (isConj_of_mem ι u₀), hψu₀, mul_inv_cancel]
  have hTN : ∀ K, Sec12a3.CompSet M K → Tof 3 M a ≤ Subgroup.normalizer (K : Set G) :=
    fun K hK => (Sec12a.tof_le_alphaOf M a).trans (alpha_le_normalizer hK)
  set 𝒪 : Set (Subgroup G) := {K | ∃ r ∈ R, GLBConj r J₀ = K} with h𝒪def
  have h𝒪 : 𝒪.Finite := Set.toFinite _
  have key : ∀ F : Finset (Subgroup G), (∀ K ∈ F, K ∈ 𝒪) → ∃ t ∈ Tof 3 M a,
      (∀ K, Sec12a3.CompSet M K → K ∉ F → ActTriv t K) ∧ (∀ K ∈ F, ActTriv (y * t) K) := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, one_mem _, fun K _ _ => actTriv_one K, fun K hK => absurd hK (by simp)⟩
    | insert K₀ F hK₀F ih =>
      intro hF
      obtain ⟨t, ht, ht1, ht2⟩ := ih (fun K hK => hF K (Finset.mem_insert_of_mem hK))
      obtain ⟨r, hr, hK₀⟩ := hF K₀ (Finset.mem_insert_self _ _)
      subst hK₀
      have hrM := hD.le hr
      have hK₀c := compSet_conj hJ₀ hrM
      have huK : r⁻¹ * (u₀ : G) * r ∈ GLBConj r J₀ :=
        mem_gLBConj.2 (by rw [show r * (r⁻¹ * (u₀ : G) * r) * r⁻¹ = u₀ by group]; exact u₀.2)
      have huT : r⁻¹ * (u₀ : G) * r ∈ Tof 3 M a := vpc_le_tof hK₀c (mem_vpc_conj (haR r hr) hu₀)
      refine ⟨t * (r⁻¹ * u₀ * r)⁻¹, (Tof 3 M a).mul_mem ht ((Tof 3 M a).inv_mem huT),
        fun K hK hKF => ?_, fun K hKF => ?_⟩
      · have hKF' : K ∉ F := fun h => hKF (Finset.mem_insert_of_mem h)
        have hKne : GLBConj r J₀ ≠ K := fun h => hKF (h ▸ Finset.mem_insert_self _ _)
        have huN := hTN K hK huT
        exact actTriv_mul (hTN K hK ht) (ht1 K hK hKF')
          (actTriv_inv huN (actTriv_of_mem_other hK hK₀c hKne huK))
      · have huN := hTN _ hK₀c huT
        rcases Finset.mem_insert.1 hKF with rfl | hKF
        ·
          have hyr : y * r = r * y := (Subgroup.mem_centralizer_iff.1 hyY.2 r hr).symm
          have h1 : ActTriv (y * (r⁻¹ * u₀ * r)⁻¹) (GLBConj r J₀) := by
            have hyr' : y * r⁻¹ = r⁻¹ * y := (Commute.inv_right (show Commute y r from hyr)).eq
            have e : y * (r⁻¹ * (u₀ : G) * r)⁻¹ = r⁻¹ * (y * (u₀ : G)⁻¹) * r := by
              calc y * (r⁻¹ * (u₀ : G) * r)⁻¹ = (y * r⁻¹) * (u₀ : G)⁻¹ * r := by group
                _ = (r⁻¹ * y) * (u₀ : G)⁻¹ * r := by rw [hyr']
                _ = r⁻¹ * (y * (u₀ : G)⁻¹) * r := by group
            rw [e]
            exact actTriv_conj_both r hyu₀
          have h2 := actTriv_conj_mem (ht1 _ hK₀c hK₀F) huN
          have e : y * (t * (r⁻¹ * u₀ * r)⁻¹) =
              (y * (r⁻¹ * u₀ * r)⁻¹) * ((r⁻¹ * u₀ * r) * t * (r⁻¹ * u₀ * r)⁻¹) := by group
          rw [e]
          exact actTriv_mul ((Subgroup.normalizer _).mul_mem
            (alpha_le_normalizer hK₀c hyα) (inv_mem huN)) h1 h2
        · have hKne : GLBConj r J₀ ≠ K := fun h => hK₀F (h ▸ hKF)
          have hK := (hF K (Finset.mem_insert_of_mem hKF))
          obtain ⟨r', hr', rfl⟩ := hK
          have hKc := compSet_conj hJ₀ (hD.le hr')
          have huN' := hTN _ hKc huT
          have e : y * (t * (r⁻¹ * u₀ * r)⁻¹) = (y * t) * (r⁻¹ * u₀ * r)⁻¹ := by group
          rw [e]
          exact actTriv_mul ((Subgroup.normalizer _).mul_mem (alpha_le_normalizer hKc hyα)
            (hTN _ hKc ht)) (ht2 _ hKF) (actTriv_inv huN'
              (actTriv_of_mem_other hKc hK₀c hKne huK))
  obtain ⟨t, ht, ht1, ht2⟩ := key h𝒪.toFinset (fun K hK => (Set.Finite.mem_toFinset h𝒪).1 hK)
  have hall : ∀ K, Sec12a3.CompSet M K → ActTriv (y * t) K := by
    intro K hK
    by_cases hK𝒪 : K ∈ 𝒪
    · exact ht2 K ((Set.Finite.mem_toFinset h𝒪).2 hK𝒪)
    · have h1 := ht1 K hK (fun h => hK𝒪 ((Set.Finite.mem_toFinset h𝒪).1 h))
      have h2 : ActTriv y K := actTriv_of_mem_orbitProd hJ₀ hK (fun x hx => hD.le hx)
        (fun x hx h => hK𝒪 ⟨x, hx, h⟩) hyY.1
      exact actTriv_mul (alpha_le_normalizer hK hyα) h2 h1
  have hyT : y ∈ Subgroup.normalizer ((Tof 3 M a : Subgroup G) : Set G) :=
    Sec12a2.normalizer_tof M a hyM hyΔa.2
  have hyt2 : (y * t) ^ 2 ^ n ∈ Tof 3 M a := by
    have hu : y * t * y⁻¹ ∈ Tof 3 M a := (Subgroup.mem_normalizer_iff.1 hyT t).1 ht
    have h1 := mul_pow_mul_inv_mem hu hyT (2 ^ n)
    rwa [show y * t * y⁻¹ * y = y * t by group, hn, inv_one, mul_one] at h1
  obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _ ⟨_, hyt2⟩
  have hytO : y * t ∈ pCoreOf 2 M := by
    refine mem_core_of_actTriv ((alphaOf 3 M).mul_mem hyα (Sec12a.tof_le_alphaOf M a ht)) hall
      (n := n + j) ?_
    rw [pow_add, pow_mul, show ((y * t) ^ 2 ^ n) ^ 2 ^ j = 1 by
      simpa using congrArg Subtype.val hj]
    exact one_mem _
  have hytT : y * t ∈ Tof 3 M a := Sec12a.pCoreOf_two_inf_le_alpha_inf (p := 3) M a
    ⟨hytO, (Cg a).mul_mem hyΔa.2 (Sec12a.tof_le_cg M a ht)⟩
  have e : y = (y * t) * t⁻¹ := by group
  rw [e]
  exact (Tof 3 M a).mul_mem hytT ((Tof 3 M a).inv_mem ht)

theorem exists_two_cent_ne_one {π : Perm (Fin 7)} (hπ : π.cycleType = {3}) :
    ∃ v : Perm (Fin 7), v ∈ alternatingGroup (Fin 7) ∧ v * π = π * v ∧ v ^ 2 ^ 1 = 1 ∧ v ≠ 1 := by
  obtain ⟨c, hc⟩ := Sec12a3.conj_of_cycleType_three hπ
  subst hc
  have hx : S7.x * S7.a = S7.a * S7.x :=
    Subgroup.mem_centralizer_singleton_iff.1 (S7.V_le_centralizer S7.x_mem_V)
  have hxA : Perm.sign S7.x = 1 := Equiv.Perm.mem_alternatingGroup.1 (S7.V_le_Alt7 S7.x_mem_V)
  have hx2 : S7.x ^ 2 = 1 := by decide
  refine ⟨c * S7.x * c⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hxA]
    simp
  · calc c * S7.x * c⁻¹ * (c * S7.a * c⁻¹) = c * (S7.x * S7.a) * c⁻¹ := by group
      _ = c * (S7.a * S7.x) * c⁻¹ := by rw [hx]
      _ = c * S7.a * c⁻¹ * (c * S7.x * c⁻¹) := by group
  · rw [pow_one, conj_pow, hx2]
    group
  · intro h
    apply Sec12a3.x_ne_one
    have e : S7.x = c⁻¹ * (c * S7.x * c⁻¹) * c := by group
    rw [e, h]
    group

@[expose] def GoodBlock (A J₀ : Subgroup G) (a : G) : Prop :=
  ∀ d ∈ A, d ∈ Subgroup.normalizer (J₀ : Set G) → ∃ j : ℕ, ActTriv (d * a ^ j) J₀

end BlockIII

theorem blockCoverIII_holds : Sec12a4.BlockCoverIII := by
  intro G _ _ m p B M E A a h F _hF hT
  classical
  obtain ⟨rfl, -⟩ := Sec12a.caseB_p3_hatSeven hT
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAM, hAel, -⟩ : IsSCp 3 M A := h.pair.1.2.1.1.1
  have haA : a ∈ A := h.ha.1
  have haM : a ∈ M := hAM haA
  have ha3 : a ^ 3 = 1 := hAel.2 a haA
  set κ := {J₀ : Subgroup G // Sec12a3.CompSet M J₀ ∧ Sec12a3.ThreeCycComp a J₀ ∧
    GoodBlock A J₀ a} with hκ
  have hD₁ : ∀ i : κ, ∃ D₁ : Subgroup G, D₁ ≤ A ∧ A ≤ D₁ ⊔ Subgroup.zpowers a ∧
      ∀ r ∈ D₁, r ∈ Subgroup.normalizer ((i.1 : Subgroup G) : Set G) → ActTriv r i.1 :=
    fun i => exists_D₁ hAel haA (normalizer_of_conj_mem ha3 i.2.2.1.1) i.2.2.2
  choose D hDA hAD hDt using hD₁
  have hDD : ∀ i : κ, DiagData M i.1 (D i) := fun i => ⟨i.2.1, (hDA i).trans hAM,
    fun r hr => hAel.2 r (hDA i hr),
    fun r hr s hs => CFSG.Open.IsElemAbelian.comm hAel (hDA i hr) (hDA i hs), hDt i⟩
  have haD : ∀ i : κ, ∀ r ∈ D i, a * r = r * a :=
    fun i r hr => CFSG.Open.IsElemAbelian.comm hAel haA (hDA i hr)
  have hCA : ∀ i : κ, ∀ x, x ∈ Subgroup.centralizer ((D i : Subgroup G) : Set G) → x ∈ Cg a →
      x ∈ Subgroup.centralizer (A : Set G) := by
    intro i x hxD hxa
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨d, hd, c, hc, rfl⟩ := Sec12a2.mem_sup_of_le_normalizer (K := A)
      ((Subgroup.zpowers_le).2 haA) (le_normalizer_of_elemAbelian hAel (hDA i)) (hAD i hb)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    have h1 : Commute d x := (Subgroup.mem_centralizer_iff.1 hxD) d hd
    have h2 : Commute (a ^ k) x :=
      Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.1 hxa).symm k
    exact (h1.mul_left h2).eq
  refine ⟨κ, D, fun i => pCoreOf 2 (diagΔ M i.1 (D i) ⊓ Cg a), fun i => diagΔ M i.1 (D i),
    fun i => ⟨hDA i, card_le_three_mul ha3 (hAD i)
      ((Subgroup.zpowers_le).2 (le_normalizer_of_elemAbelian hAel (hDA i) haA))⟩,
    fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, ?_⟩
  · obtain ⟨hnorm, ι₀, πa, hπa, hCB⟩ := i.2.2.1
    have haN := normalizer_of_conj_mem ha3 hnorm
    have hA := isConj_of_conjsBy haN hCB
    intro y hy
    have hyΔa := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hy
    exact ⟨diag_pcore_le_tof (hDD i) ι₀ haM ha3 haN (haD i) hπa hA hy,
      hCA i y (diagΔ_le_Y _ _ _ hyΔa.1).2 hyΔa.2⟩
  · exact ⟨(CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left,
      le_inf ((diagΔ_le_Y _ _ _).trans (diagY_le_alpha (hDD i)))
        ((diagΔ_le_Y _ _ _).trans inf_le_right), diagΔ_perfect _ _ _⟩
  · obtain ⟨-, ι₀, -⟩ := i.2.2.1
    exact (diagΔ_quot (hDD i) ι₀).2.1
  · obtain ⟨hnorm, ι₀, πa, hπa, hCB⟩ := i.2.2.1
    have haN := normalizer_of_conj_mem ha3 hnorm
    have hA := isConj_of_conjsBy haN hCB
    obtain ⟨v, hvA, hvc, hv2, hv1⟩ := exists_two_cent_ne_one hπa
    obtain ⟨y, hy, hyN, hyv⟩ := exists_diagΔ_lift (hDD i) ι₀ haM ha3 haN (haD i) hπa hA hvA hvc hv2
    intro hle
    have hyO := (diagΔ_quot (hDD i) ι₀).2.2 (hle hy)
    apply hv1
    rw [← hyv]
    exact permHom_eq _ (isConj_one_of_actTriv ι₀ (actTriv_of_mem_core i.2.1 hyO))
  · set Vf : κ → Subgroup G := fun i => pCoreOf 2 (diagΔ M i.1 (D i) ⊓ Cg a) with hVf
    set RHS := (Tof 3 M a ⊓ Subgroup.centralizer (A : Set G) ⊓ pCoreOf 2 M) ⊔ ⨆ i, Vf i with hRHS
    suffices key : ∀ F : Finset (Subgroup G), ∀ x ∈ Tof 3 M a ⊓ Subgroup.centralizer (A : Set G),
        (∀ K, Sec12a3.CompSet M K → K ∉ F → ActTriv x K) → x ∈ RHS by
      intro x hx
      haveI := Fintype.ofFinite (Subgroup G)
      exact key Finset.univ x hx (fun K _ hK => absurd (Finset.mem_univ K) hK)
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro x hx htriv
      obtain ⟨n, hn⟩ := Sec12a3.exists_pow_eq_one_of_pCoreOf _ hx.1
      exact (le_sup_left : _ ≤ RHS) ⟨hx, mem_core_of_actTriv (Sec12a.tof_le_alphaOf M a hx.1)
        (fun K hK => htriv K hK (by simp)) (n := n) (by rw [hn]; exact one_mem _)⟩
    | insert J₀ F hJ₀F ih =>
      intro x hx htriv
      by_cases hJ₀ : Sec12a3.CompSet M J₀ ∧ ¬ ActTriv x J₀
      · obtain ⟨hJ₀c, hnx⟩ := hJ₀
        have hTC : Sec12a3.ThreeCycComp a J₀ := by
          by_contra hn
          exact hnx (tof_actTriv hJ₀c haM ha3 hn x hx.1)
        have hTC' := hTC
        obtain ⟨hnorm, ι₀, πa, hπa, hCB⟩ := hTC'
        have haN := normalizer_of_conj_mem ha3 hnorm
        have hA := isConj_of_conjsBy haN hCB
        obtain ⟨hvA, hvc, k, hvk⟩ := tof_perm_props hJ₀c ι₀ haN hA hx.1
        have hxα := Sec12a.tof_le_alphaOf M a hx.1
        have hxN := alpha_le_normalizer hJ₀c hxα
        have hGood : GoodBlock A J₀ a := by
          intro d hd hdN
          have hdc : permHom J₀ ι₀ ⟨d, hdN⟩ * πa = πa * permHom J₀ ι₀ ⟨d, hdN⟩ := by
            rw [← permHom_eq ⟨a, haN⟩ hA, ← map_mul, ← map_mul]
            congr 1
            exact Subtype.ext (CFSG.Open.IsElemAbelian.comm hAel hd haA)
          have hd3 : (permHom J₀ ι₀ ⟨d, hdN⟩) ^ 3 = 1 := by
            rw [← map_pow]
            have e : (⟨d, hdN⟩ : ↥(Subgroup.normalizer (J₀ : Set G))) ^ 3 = 1 :=
              Subtype.ext (by simpa using hAel.2 d hd)
            rw [e, map_one]
          have hvd : permHom J₀ ι₀ ⟨d, hdN⟩ * permHom J₀ ι₀ ⟨x, hxN⟩ *
              (permHom J₀ ι₀ ⟨d, hdN⟩)⁻¹ = permHom J₀ ι₀ ⟨x, hxN⟩ := by
            have hdx : d * x = x * d := (Subgroup.mem_centralizer_iff.1 hx.2 d hd)
            rw [← map_mul, ← map_inv, ← map_mul]
            congr 1
            apply Subtype.ext
            show d * x * d⁻¹ = x
            rw [hdx]
            group
          have hπ3 := Sec12a3.three_cycle_pow_three hπa
          have htr : ∀ j : ℕ, permHom J₀ ι₀ ⟨d, hdN⟩ * πa ^ j = 1 →
              ∃ j : ℕ, ActTriv (d * a ^ j) J₀ := by
            intro j hj
            refine ⟨j, ?_⟩
            have hN : d * a ^ j ∈ Subgroup.normalizer (J₀ : Set G) :=
              Subgroup.mul_mem _ hdN (Subgroup.pow_mem _ haN j)
            have e : (⟨d * a ^ j, hN⟩ : ↥(Subgroup.normalizer (J₀ : Set G))) =
                ⟨d, hdN⟩ * ⟨a, haN⟩ ^ j := Subtype.ext (by simp)
            rw [show d * a ^ j = ((⟨d * a ^ j, hN⟩ : ↥(Subgroup.normalizer (J₀ : Set G))) : G)
              from rfl, actTriv_iff_permHom hJ₀c.2.2.2 ι₀, e, map_mul, map_pow,
              permHom_eq ⟨a, haN⟩ hA]
            exact hj
          by_cases h1 : permHom J₀ ι₀ ⟨d, hdN⟩ = 1
          · exact htr 0 (by rw [h1, pow_zero, mul_one])
          by_cases h2 : permHom J₀ ι₀ ⟨d, hdN⟩ = πa
          · exact htr 2 (by rw [h2, show πa * πa ^ 2 = πa ^ 3 from (pow_succ' πa 2).symm, hπ3])
          by_cases h3 : permHom J₀ ι₀ ⟨d, hdN⟩ = πa ^ 2
          · exact htr 1 (by rw [h3, pow_one, show πa ^ 2 * πa = πa ^ 3 from (pow_succ πa 2).symm,
              hπ3])
          exfalso
          obtain ⟨V, -, -, -, -, hV5, hV6⟩ := Sec12a3.three_cycle_klein hπa
          have hvV := hV5 _ ⟨Subgroup.mem_centralizer_singleton_iff.2 hvc, hvA⟩ k hvk
          exact hnx ((actTriv_iff_permHom hJ₀c.2.2.2 ι₀ ⟨x, hxN⟩).2
            (hV6 _ hdc hd3 h1 h2 h3 _ hvV hvd))
        set i : κ := ⟨J₀, hJ₀c, hTC, hGood⟩ with hi
        obtain ⟨y, hy, hyN, hyv⟩ :=
          exists_diagΔ_lift (hDD i) ι₀ haM ha3 haN (haD i) hπa hA hvA hvc hvk
        have hyΔa := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hy
        have hyY := diagΔ_le_Y M J₀ (D i) hyΔa.1
        have hyT : y ∈ Tof 3 M a := diag_pcore_le_tof (hDD i) ι₀ haM ha3 haN (haD i) hπa hA hy
        have hyA : y ∈ Subgroup.centralizer (A : Set G) := hCA i y hyY.2 hyΔa.2
        have hx' : x * y⁻¹ ∈ Tof 3 M a ⊓ Subgroup.centralizer (A : Set G) :=
          ⟨(Tof 3 M a).mul_mem hx.1 ((Tof 3 M a).inv_mem hyT),
            (Subgroup.centralizer _).mul_mem hx.2 ((Subgroup.centralizer _).inv_mem hyA)⟩
        have hxyJ : ActTriv (x * y⁻¹) J₀ := by
          have e : x * y⁻¹ = ((⟨x, hxN⟩ * (⟨y, hyN⟩)⁻¹ :
              ↥(Subgroup.normalizer (J₀ : Set G))) : G) := rfl
          rw [e, actTriv_iff_permHom hJ₀c.2.2.2 ι₀, map_mul, map_inv, hyv, mul_inv_cancel]
        have hxD : x * y⁻¹ ∈ Subgroup.centralizer ((D i : Subgroup G) : Set G) :=
          Subgroup.centralizer_le (hDA i) hx'.2
        have h1 := ih (x * y⁻¹) hx' (fun K hK hKF => ?_)
        · have e : x = x * y⁻¹ * y := by group
          rw [e]
          exact RHS.mul_mem h1 ((le_sup_right : (⨆ i, Vf i) ≤ RHS) ((le_iSup Vf i) hy))
        · by_cases hKo : ∃ r ∈ D i, GLBConj r J₀ = K
          · obtain ⟨r, hr, rfl⟩ := hKo
            exact actTriv_conj ((Subgroup.mem_centralizer_iff.1 hxD r hr).symm) hxyJ
          · push Not at hKo
            have hKJ₀ : K ≠ J₀ := fun h => hKo 1 (D i).one_mem (by rw [gLBConj_one, h])
            have h2 := htriv K hK (by simp [Finset.mem_insert, hKJ₀, hKF])
            have h3 : ActTriv y K := actTriv_of_mem_orbitProd hJ₀c hK (fun x hx => (hDD i).le hx)
              hKo hyY.1
            have hKN := alpha_le_normalizer hK
            exact actTriv_mul (hKN hxα) h2 (actTriv_inv (hKN (diagY_le_alpha (hDD i) hyY)) h3)
      · refine ih x hx (fun K hK hKF => ?_)
        by_cases hKJ₀ : K = J₀
        · subst hKJ₀
          by_contra hn
          exact hJ₀ ⟨hK, hn⟩
        · exact htriv K hK (by simp [Finset.mem_insert, hKJ₀, hKF])

theorem lemma122_iii_holds : Lemma122_iiiStatement :=
  Sec12a4.lemma122_iii_of_blockCover blockCoverIII_holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims122

end
