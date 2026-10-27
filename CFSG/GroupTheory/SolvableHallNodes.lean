module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
public import Mathlib.Algebra.Group.PUnit

public section

open scoped Pointwise

namespace CFSG.SolvableHall

universe u v

abbrev trivialUnitAction (G : Type*) [Group G] : MulDistribMulAction Unit G where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_mul _ _ _ := rfl
  smul_one _ := rfl

theorem solvable_hall_containment {G : Type u} [Group G] [Finite G] (hG : Group.IsSolvable G)
    (π : Set Nat.Primes) (U : Subgroup G) (hU : IsPiSubgroup π U) :
    ∃ H : Subgroup G, IsHallSubgroup π H ∧ U ≤ H := by
  let := trivialUnitAction G
  obtain ⟨H, hH, -, hUH⟩ := exists_isHallSubgroup_isInvariant_of_isPiSubgroup (A := Unit) hG
    (by simp) π U hU ⟨fun _ _ => Iff.rfl⟩
  exact ⟨H, hH, hUH⟩

theorem solvable_hall_existence {G : Type u} [Group G] [Finite G] (hG : Group.IsSolvable G)
    (π : Set Nat.Primes) : ∃ H : Subgroup G, IsHallSubgroup π H := by
  obtain ⟨H, hH, -⟩ := solvable_hall_containment hG π ⊥ (fun p hp => by
    rw [Subgroup.card_bot] at hp
    exact absurd (Nat.le_of_dvd one_pos hp) (not_le.mpr p.2.one_lt))
  exact ⟨H, hH⟩

theorem complement_fst_eq_of_mem {F : Type*} [Group F] {N K : Subgroup F}
    (hK : Subgroup.IsComplement' N K) {h n : F} (hn : n ∈ N) (hk : n⁻¹ * h ∈ K) :
    n = ((hK.equiv h).1 : F) := by
  have hinj := hK.1
  have h1 : ((⟨n, hn⟩ : ↥(N : Set F)), (⟨n⁻¹ * h, hk⟩ : ↥(K : Set F))) = hK.equiv h := by
    apply hinj
    simp only
    rw [mul_inv_cancel_left, Subgroup.IsComplement.equiv_fst_mul_equiv_snd]
  exact congrArg (fun x : ↥(N : Set F) × ↥(K : Set F) => (x.1 : F)) h1

theorem solvable_normal_hall_complement_conjugacy {F : Type u} [Group F] [Finite F]
    (N : Subgroup F) [N.Normal] (hNsolv : Group.IsSolvable N)
    (hcop : Nat.Coprime (Nat.card N) N.index) {H K : Subgroup F}
    (hNH : (N : Set F) * (H : Set F) = Set.univ) (hNK : (N : Set F) * (K : Set F) = Set.univ)
    (hNH' : N ⊓ H = ⊥) (hNK' : N ⊓ K = ⊥) :
    ∃ n ∈ N, K = H.map (MulAut.conj n⁻¹).toMonoidHom := by
  classical
  have hHc : Subgroup.IsComplement' N H :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hNH') hNH
  have hKc : Subgroup.IsComplement' N K :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hNK') hNK
  have hcardH : Nat.card H = N.index := by
    have h1 := hHc.card_mul_card
    have h2 := Subgroup.card_mul_index N
    have hN0 : 0 < Nat.card N := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hN0 (h1.trans h2.symm)
  have hcardK : Nat.card K = N.index := by
    have h1 := hKc.card_mul_card
    have h2 := Subgroup.card_mul_index N
    have hN0 : 0 < Nat.card N := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hN0 (h1.trans h2.symm)
  let : MulDistribMulAction H N :=
    MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp H.subtype)
  have hsmul : ∀ (h : H) (x : N), ((h • x : N) : F) = (h : F) * x * (h : F)⁻¹ :=
    fun h x => MulAut.conjNormal_apply (h : F) x
  set nn : H → F := fun h => ((hKc.equiv (h : F)).1 : F) with hnn_def
  have hnn : ∀ h : H, nn h ∈ N := fun h => (hKc.equiv (h : F)).1.2
  have hkk : ∀ h : H, (nn h)⁻¹ * h ∈ K := by
    intro h
    rw [hnn_def, ← Subgroup.IsComplement.equiv_snd_eq_inv_mul]
    exact (hKc.equiv (h : F)).2.2
  let c : H → N := fun h => ⟨(nn h)⁻¹, N.inv_mem (hnn h)⟩
  have hc : ∀ a b : H, c (a * b) = c a * (a • c b) := by
    intro a b
    have hmem : (a : F) * nn b * (a : F)⁻¹ * nn a ∈ N :=
      N.mul_mem (Subgroup.Normal.conj_mem inferInstance _ (hnn b) _) (hnn a)
    have hk : ((a : F) * nn b * (a : F)⁻¹ * nn a)⁻¹ * ((a * b : H) : F) ∈ K := by
      have : ((a : F) * nn b * (a : F)⁻¹ * nn a)⁻¹ * ((a * b : H) : F) =
          ((nn a)⁻¹ * a) * ((nn b)⁻¹ * b) := by
        rw [Subgroup.coe_mul]
        group
      rw [this]
      exact K.mul_mem (hkk a) (hkk b)
    have hab : (a : F) * nn b * (a : F)⁻¹ * nn a = nn (a * b) :=
      complement_fst_eq_of_mem hKc hmem hk
    apply Subtype.ext
    change (nn (a * b))⁻¹ = (nn a)⁻¹ * ((a • c b : N) : F)
    rw [hsmul, ← hab]
    simp only [c]
    group
  obtain ⟨x, hx⟩ := exists_principal_cocycle_of_solvable_coprime (A := H) hNsolv
    (by rw [hcardH]; exact hcop.symm) c hc
  have hconj : ∀ h : H, (x : F) * h * (x : F)⁻¹ ∈ K := by
    intro h
    have h1 := congrArg (fun y : N => (y : F)) (hx h)
    simp only [c, Subgroup.coe_mul, Subgroup.coe_inv, hsmul] at h1
    have : (x : F) * h * (x : F)⁻¹ = (nn h)⁻¹ * h := by
      rw [h1]
      group
    rw [this]
    exact hkk h
  refine ⟨(x : F)⁻¹, N.inv_mem x.2, ?_⟩
  rw [inv_inv]
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨h, hh, rfl⟩
    exact hconj ⟨h, hh⟩
  · rw [hcardK, Subgroup.card_map_of_injective (MulAut.conj (x : F)).injective, hcardH]

theorem abelian_normal_hall_complement_conjugacy {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [IsMulCommutative N]
    (hcop : Nat.Coprime (Nat.card N) N.index) {H K : Subgroup G}
    (hNH : (N : Set G) * (H : Set G) = Set.univ) (hNK : (N : Set G) * (K : Set G) = Set.univ)
    (hNH' : N ⊓ H = ⊥) (hNK' : N ⊓ K = ⊥) :
    ∃ n ∈ N, K = H.map (MulAut.conj n⁻¹).toMonoidHom :=
  solvable_normal_hall_complement_conjugacy N inferInstance hcop hNH hNK hNH' hNK'

section Coprime

variable {A H : Type*} [Group A] [Group H] [MulDistribMulAction A H]

theorem map_smul_eq_of_invariant [Finite H] {U : Subgroup H} (hU : ∀ a : A, ∀ x ∈ U, a • x ∈ U)
    (a : A) : U.map (MulDistribMulAction.toMonoidHom H a) = U := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hU a x hx
  · intro x hx
    refine ⟨a⁻¹ • x, hU a⁻¹ x hx, ?_⟩
    change a • (a⁻¹ • x) = x
    rw [smul_inv_smul]

omit [MulDistribMulAction A H] in
theorem map_conj_mul (U : Subgroup H) (a b : H) :
    U.map (MulAut.conj (a * b)).toMonoidHom =
      (U.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

omit [MulDistribMulAction A H] in
theorem map_conj_one (U : Subgroup H) : U.map (MulAut.conj (1 : H)).toMonoidHom = U := by
  rw [map_one]
  exact Subgroup.map_id U

theorem coprime_fixed_conjugator {p : ℕ} [Fact p.Prime] [Finite A] [Finite H]
    (hA : IsPGroup p A) (hp : ¬ p ∣ Nat.card H) {U V : Subgroup H}
    (hU : ∀ a : A, ∀ x ∈ U, a • x ∈ U) (hV : ∀ a : A, ∀ x ∈ V, a • x ∈ V)
    (hUV : ∃ h : H, U.map (MulAut.conj h⁻¹).toMonoidHom = V) :
    ∃ c ∈ fixedPointSubgroup A H, U.map (MulAut.conj c⁻¹).toMonoidHom = V := by
  classical
  obtain ⟨h₀, hh₀⟩ := hUV
  have hTinv : ∀ (a : A) (h : H), U.map (MulAut.conj h⁻¹).toMonoidHom = V →
      U.map (MulAut.conj (a • h)⁻¹).toMonoidHom = V := by
    intro a h hh
    have hcomm : (MulAut.conj (a • h)⁻¹).toMonoidHom.comp (MulDistribMulAction.toMonoidHom H a) =
        (MulDistribMulAction.toMonoidHom H a).comp (MulAut.conj h⁻¹).toMonoidHom := by
      ext y
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MulDistribMulAction.toMonoidHom_apply, smul_mul', smul_inv', inv_inv]
    rw [← map_smul_eq_of_invariant hU a, Subgroup.map_map, hcomm, ← Subgroup.map_map, hh,
      map_smul_eq_of_invariant hV a]
  let T : SubMulAction A H :=
    { carrier := {h | U.map (MulAut.conj h⁻¹).toMonoidHom = V}
      smul_mem' := fun a h hh => hTinv a h hh }
  have hTcard : Nat.card T = Nat.card (Subgroup.normalizer (U : Set H)) := by
    symm
    refine Nat.card_congr
      { toFun := fun m => ⟨(m : H)⁻¹ * h₀, ?_⟩
        invFun := fun h => ⟨h₀ * (h : H)⁻¹, ?_⟩
        left_inv := fun m => by ext; simp
        right_inv := fun h => by ext; simp }
    · change U.map (MulAut.conj ((m : H)⁻¹ * h₀)⁻¹).toMonoidHom = V
      have hm : U.map (MulAut.conj (m : H)).toMonoidHom = U := by
        rw [MulEquiv.toMonoidHom_eq_coe]
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp m.2
      rw [mul_inv_rev, inv_inv, map_conj_mul, hm, hh₀]
    · rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe, map_conj_mul]
      have hh : U.map (MulAut.conj (h : H)⁻¹).toMonoidHom = V := h.2
      rw [hh, ← hh₀, ← map_conj_mul, mul_inv_cancel, map_conj_one]
  have hTp : ¬ p ∣ Nat.card T := by
    rw [hTcard]
    exact fun h => hp (h.trans (Subgroup.card_subgroup_dvd_card _))
  obtain ⟨⟨c, hcT⟩, hcfix⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card T hTp
  refine ⟨c, ?_, hcT⟩
  intro a
  have := hcfix a
  exact congrArg Subtype.val this

omit [MulDistribMulAction A H] in
theorem map_conj_eq_coe_smul {q : ℕ} (P : Sylow q H) (g : H) :
    (P : Subgroup H).map (MulAut.conj g).toMonoidHom = ((g • P : Sylow q H) : Subgroup H) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  rfl

theorem coprime_invariant_sylow_conjugacy {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [Finite A]
    [Finite H] (hA : IsPGroup p A) (hp : ¬ p ∣ Nat.card H) (P Q : Sylow q H)
    (hP : ∀ a : A, ∀ x ∈ (P : Subgroup H), a • x ∈ (P : Subgroup H))
    (hQ : ∀ a : A, ∀ x ∈ (Q : Subgroup H), a • x ∈ (Q : Subgroup H)) :
    ∃ c ∈ fixedPointSubgroup A H, (P : Subgroup H).map (MulAut.conj c⁻¹).toMonoidHom = Q := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P Q
  refine coprime_fixed_conjugator hA hp hP hQ ⟨g⁻¹, ?_⟩
  rw [inv_inv, map_conj_eq_coe_smul, hg]

theorem coprime_invariant_hall_containment {p : ℕ} [Fact p.Prime] [Finite A] [Finite H]
    (hA : IsPGroup p A) (hp : ¬ p ∣ Nat.card H) (hH : Group.IsSolvable H) (π : Set Nat.Primes)
    (U : Subgroup H) (hUπ : IsPiSubgroup π U) (hU : ∀ a : A, ∀ x ∈ U, a • x ∈ U) :
    ∃ P : Subgroup H, IsHallSubgroup π P ∧ (∀ a : A, ∀ x ∈ P, a • x ∈ P) ∧ U ≤ P := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  have hcop : Nat.Coprime (Nat.card A) (Nat.card H) := by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hp)
  have hUinv : IsInvariant A H U := ⟨fun a g => ⟨fun hg => hU a g hg, fun hag => by
    have := hU a⁻¹ _ hag
    rwa [inv_smul_smul] at this⟩⟩
  obtain ⟨P, hPhall, hPinv, hUP⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup (G := H) (A := A) hH hcop π U hUπ hUinv
  exact ⟨P, hPhall, fun a x hx => (hPinv.invariant a x).1 hx, hUP⟩

end Coprime

theorem coprime_solvable_kernel_fixed_point_lifting {G : Type u} {A : Type v} [Group G]
    [Finite G] [Group A] [Finite A] [MulDistribMulAction A G] (N : Subgroup G) [N.Normal]
    (hNinv : IsInvariant A G N) (hNsolv : Group.IsSolvable N)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card N)) :
    letI : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction (A := A) (G := G) N hNinv
    fixedPointSubgroup A (G ⧸ N) = (fixedPointSubgroup A G).map (QuotientGroup.mk' N) := by
  let : IsInvariant A G N := hNinv
  let : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction (A := A) (G := G) N hNinv
  let : MulAction.QuotientAction A N := quotientAction_of_isInvariant (A := A) N hNinv
  apply le_antisymm _ (fixedPointSubgroup_map_mk'_le_fixedPointSubgroup_quotient N hNinv)
  intro q hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have hfix : ∀ a : A, ((a • g : G) : G ⧸ N) = (g : G ⧸ N) := by
    intro a
    have h := hq a
    rw [← h]
    exact (MulAction.Quotient.smul_coe (H := N) a g).symm
  have hmem : ∀ a : A, g⁻¹ * (a • g) ∈ N := by
    intro a
    have h := (QuotientGroup.eq (s := N)).mp (hfix a).symm
    exact h
  let c : A → N := fun a => ⟨g⁻¹ * (a • g), hmem a⟩
  have hc : ∀ a b : A, c (a * b) = c a * (a • c b) := by
    intro a b
    apply Subtype.ext
    change g⁻¹ * ((a * b) • g) = g⁻¹ * (a • g) * (a • (g⁻¹ * (b • g)))
    rw [smul_mul', smul_inv', mul_smul]
    group
  obtain ⟨x, hx⟩ := exists_principal_cocycle_of_solvable_coprime (A := A) hNsolv hcop c hc
  refine ⟨g * x, ?_, ?_⟩
  · intro a
    have h := congrArg (fun y : N => (y : G)) (hx a)
    change g⁻¹ * (a • g) = (x : G) * (a • (x : G))⁻¹ at h
    change a • (g * (x : G)) = g * x
    rw [smul_mul']
    calc a • g * a • (x : G) = g * (g⁻¹ * (a • g)) * a • (x : G) := by group
      _ = g * x := by rw [h]; group
  · change ((g * (x : G) : G) : G ⧸ N) = (g : G ⧸ N)
    rw [QuotientGroup.eq]
    simp

end CFSG.SolvableHall
