module

public import CFSG.LieType.Steinberg.CentralExt.LinearPerfect
public import CFSG.GH74.Generic.S45.LQData
public import CFSG.GH74.Generic.S45.LSporCommon

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg CFSG.GH74.GLS Subgroup
open scoped MatrixGroups

theorem sl2_sq_eq_one_mem_center {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {x : SL(2, F)}
    (hx : x * x = 1) : x ∈ Subgroup.center SL(2, F) := by
  obtain ⟨a, b, c, d, hxa⟩ : ∃ a b c d : F,
      (x : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hm := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) hx
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hxa] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e10 := congrFun (congrFun hm 1) 0
  have e11 := congrFun (congrFun hm 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have hdet := x.2
  rw [hxa, Matrix.det_fin_two_of] at hdet
  have ht : a + d ≠ 0 := by
    intro h
    have hd' : d = -a := by linear_combination h
    rw [hd'] at hdet
    apply h2
    linear_combination -e00 - hdet
  have hb0 : b = 0 := by
    have : b * (a + d) = 0 := by linear_combination e01
    exact (mul_eq_zero.1 this).resolve_right ht
  have hc0 : c = 0 := by
    have : c * (a + d) = 0 := by linear_combination e10
    exact (mul_eq_zero.1 this).resolve_right ht
  have had : a = d := by
    have : (a - d) * (a + d) = 0 := by linear_combination e00 - e11
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right ht)
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨a, ?_, ?_⟩
  · simp only [Fintype.card_fin]
    rw [hb0, hc0, ← had] at hdet
    linear_combination hdet
  · rw [hxa, hb0, hc0, ← had]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

theorem exists_mulEquiv_sl_two_of_center_ne_bot {K : Type} [Group K] [Finite K]
    (hKp : Group.IsPerfect K) (hZ2 : IsPGroup 2 (Subgroup.center K))
    (hZ : Subgroup.center K ≠ ⊥) {r f : ℕ} (hr2 : r ≠ 2)
    (hmodel : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 2 r f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), ringChar F ≠ 2 ∧ Nonempty (K ≃* SL(2, F)) := by
  classical
  have := hKp
  obtain ⟨⟨hp, -, -, -⟩, F, _, _, hF, ⟨e⟩⟩ := hmodel
  have hk : ringChar F ≠ 2 := ringChar_ne_two_of_card_eq_pow hp hr2 hF
  let φ := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F
  let η : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  let β : SL(2, F) →* K ⧸ Subgroup.center K :=
    (e.symm.toMonoidHom.comp (QuotientGroup.mk' _)).comp φ.toMonoidHom
  have hβ : Function.Surjective β :=
    (e.symm.surjective.comp (QuotientGroup.mk'_surjective _)).comp φ.surjective
  have hη : Function.Surjective η := QuotientGroup.mk'_surjective _
  have hηker : η.ker = Subgroup.center K := QuotientGroup.ker_mk' _
  have hker : β.ker = Subgroup.center SL(2, F) := by
    ext x
    have h1 : x ∈ β.ker ↔
        φ x ∈ (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F) := by
      rw [← ker_comp_mk' _ e.symm]
      rfl
    rw [h1, ← CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars]
    exact ⟨fun ⟨y, hy, hxy⟩ => (φ.injective hxy) ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* SL(2, F)), Function.Surjective π →
      π.ker ≤ Subgroup.center E → IsPGroup 2 π.ker →
        ∃ σ : SL(2, F) →* E, ∀ x, π (σ x) = x :=
    fun E _ _ π hπ hcen h2 =>
      (sl_central_two_extension_splitting 1 hk hπ hcen h2).imp fun _ h => h.1
  have hZ2' : IsPGroup 2 η.ker := by rw [hηker]; exact hZ2
  obtain ⟨α, hα, hαs, hαker⟩ := exists_surjective_of_isPerfect hsplit hβ hη hηker.le hZ2'
  obtain ⟨z, hzK, hz1⟩ : ∃ z ∈ Subgroup.center K, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hZ ((Subgroup.eq_bot_iff_forall _).2 hcon)
  obtain ⟨s, hs, hsz⟩ : z ∈ β.ker.map α := by rw [← hαker, hηker]; exact hzK
  rw [hker] at hs
  have hs1 : α s ≠ 1 := by rw [hsz]; exact hz1
  have hs1' : s ≠ 1 := fun h => hs1 (by rw [h, map_one])
  have hcard : Nat.card (Subgroup.center SL(2, F)) ∣ 2 :=
    (card_center_specialLinearGroup_dvd (n := 2) (by norm_num) F).trans (Nat.gcd_dvd_left 2 _)
  have hcard2 : Nat.card (Subgroup.center SL(2, F)) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hcard with h | h
    · exfalso
      have hsub : Subsingleton (Subgroup.center SL(2, F)) := Finite.card_le_one_iff_subsingleton.1 h.le
      exact hs1' (congrArg Subtype.val (hsub.elim ⟨s, hs⟩ 1))
    · exact h
  have hinj : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    have hxβ : x ∈ β.ker := by
      rw [MonoidHom.mem_ker, ← hα]
      have : α x = 1 := hx
      rw [this, map_one]
    rw [hker] at hxβ
    obtain ⟨u, hu⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center SL(2, F))).1 hcard2
    have hxs : (⟨x, hxβ⟩ : Subgroup.center SL(2, F)) = ⟨s, hs⟩ :=
      (hu.2 _ (fun h => hx1 (congrArg Subtype.val h))).trans
        (hu.2 _ (fun h => hs1' (congrArg Subtype.val h))).symm
    have hxs' : x = s := congrArg Subtype.val hxs
    exact hs1 (by rw [← hxs']; exact hx)
  exact ⟨F, inferInstance, inferInstance, hk,
    ⟨(MulEquiv.ofBijective α ⟨hinj, hαs⟩).symm⟩⟩

theorem Hyp1310.false_of_center_ne_bot_psl2 {K : Type} [Group K] [Finite K] {y : MulAut K}
    {L : Subgroup K} (hyp : Hyp1310 K y L) {r f : ℕ} (hr2 : r ≠ 2)
    (hmodel : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 2 r f)
    (hZ : Subgroup.center K ≠ ⊥) : False := by
  obtain ⟨hKp, hZ2, -, -, -, hLs, hLnab, ⟨v, hvL, hv⟩, -⟩ := hyp.data
  obtain ⟨F, _, _, hk, ⟨a⟩⟩ := exists_mulEquiv_sl_two_of_center_ne_bot hKp hZ2 hZ hr2 hmodel
  have hvv : v * v = 1 := by
    have h := pow_orderOf_eq_one v
    rw [hv, pow_two] at h
    exact h
  have hc : a v ∈ Subgroup.center SL(2, F) :=
    sl2_sq_eq_one_mem_center (Ring.two_ne_zero hk) (by rw [← map_mul, hvv, map_one])
  have hvc : v ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply a.injective
    rw [map_mul, map_mul]
    exact (Subgroup.mem_center_iff.1 hc (a g))
  have hvz : (⟨v, hvL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 hvc g)
  rw [center_eq_bot_of_simple_nonab hLs hLnab, Subgroup.mem_bot] at hvz
  have hv1 : v = 1 := congrArg Subtype.val hvz
  rw [hv1, orderOf_one] at hv
  omega

end CFSG.GH74.Generic.S45
