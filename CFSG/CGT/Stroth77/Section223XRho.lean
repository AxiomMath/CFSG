module

public import CFSG.CGT.Stroth77.Section223Odd
public import CFSG.CGT.Stroth77.Stroth34Local

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)
open scoped Pointwise

namespace S223X

variable {G : Type} [Group G]

@[expose] def commN (D V : Subgroup G) : Subgroup G where
  carrier := {y | y ∈ Subgroup.normalizer (D : Set G) ∧ ∀ v ∈ V, y⁻¹ * (v⁻¹ * y * v) ∈ D}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun v hv => ?_⟩
    have e : (a * b)⁻¹ * (v⁻¹ * (a * b) * v) =
        (b⁻¹ * (a⁻¹ * (v⁻¹ * a * v)) * b) * (b⁻¹ * (v⁻¹ * b * v)) := by group
    rw [e]
    exact mul_mem ((Subgroup.mem_normalizer_iff''.mp hb _).mp (ha' v hv)) (hb' v hv)
  one_mem' := ⟨one_mem _, fun v _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun v hv => ?_⟩
    have e : a⁻¹⁻¹ * (v⁻¹ * a⁻¹ * v) = a * (a⁻¹ * (v⁻¹ * a * v))⁻¹ * a⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp ha _).mp (inv_mem (ha' v hv))

theorem mem_normalizer_commN [Finite G] {D V : Subgroup G} {g : G}
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) (hgV : g ∈ Subgroup.normalizer (V : Set G)) :
    g ∈ Subgroup.normalizer (commN D V : Set G) := by
  refine S223.mem_normalizer_of_conj_mem fun k hk => ⟨?_, fun v hv => ?_⟩
  · exact mul_mem (mul_mem hgD hk.1) (inv_mem hgD)
  · have hv' : g⁻¹ * v * g ∈ V := (Subgroup.mem_normalizer_iff''.mp hgV v).mp hv
    have h2 := (Subgroup.mem_normalizer_iff.mp hgD _).mp (hk.2 _ hv')
    convert h2 using 1
    group

theorem exists_pow_mul_eq {N : Subgroup G} {x k : G} (hx : x ∈ Subgroup.normalizer (N : Set G))
    (hk : k ∈ N) (n : ℕ) : ∃ k' ∈ N, (x * k) ^ n = x ^ n * k' := by
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨k', hk', e⟩ := ih
    refine ⟨x⁻¹ * k' * x * k, mul_mem ((Subgroup.mem_normalizer_iff''.mp hx k').mp hk') hk, ?_⟩
    rw [pow_succ, e, pow_succ]
    group

end S223X

namespace StrothFrame

variable {G : Type} [Group G] [Finite G]

theorem comm_mem_of_gens (F : StrothFrame G) {D : Subgroup G} {x : G}
    (hVD : F.V ≤ Subgroup.normalizer (D : Set G))
    (huv : x⁻¹ * (F.dA.uv⁻¹ * x * F.dA.uv) ∈ D) (ht : x⁻¹ * (F.dA.t⁻¹ * x * F.dA.t) ∈ D) :
    ∀ v ∈ F.V, x⁻¹ * (v⁻¹ * x * v) ∈ D := by
  intro v hv
  induction hv using Subgroup.closure_induction with
  | mem v hv =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact huv
    · exact ht
  | one => simp
  | mul v w hv hw ihv ihw =>
    have e : x⁻¹ * ((v * w)⁻¹ * x * (v * w)) =
        x⁻¹ * (w⁻¹ * x * w) * (w⁻¹ * (x⁻¹ * (v⁻¹ * x * v)) * w) := by group
    rw [e]
    exact mul_mem ihw ((Subgroup.mem_normalizer_iff''.mp (hVD hw) _).mp ihv)
  | inv v hv ihv =>
    have e : x⁻¹ * (v⁻¹⁻¹ * x * v⁻¹) = v * (x⁻¹ * (v⁻¹ * x * v))⁻¹ * v⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hVD hv) _).mp (inv_mem ihv)

end StrothFrame

namespace StrothFrame.IsTyped

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem exists_rho_change_of_isSylowIn (h : F.IsTyped D dD) {K W Q : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer (F.E : Set G)) (hKodd : Odd (Nat.card K))
    (hKiff : ∀ c : G, c ∈ K ↔ c ∈ Subgroup.centralizer (F.E : Set G) ∧ Odd (orderOf c))
    (hQ : IsSylowIn 2 W Q) (hOW : K ⊓ Subgroup.centralizer (D : Set G) ≤ W)
    (hWO : W ≤ Subgroup.normalizer
      ((K ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G))
    (hpow : ∀ y ∈ W, ∃ n : ℕ, y ^ (2 ^ n) ∈ K ⊓ Subgroup.centralizer (D : Set G))
    (hρW : F.dA.ρ ∈ Subgroup.normalizer (W : Set G))
    (huQ : F.dA.u ∈ Subgroup.normalizer (Q : Set G)) :
    ∃ o : G, o ∈ Subgroup.centralizer (F.E : Set G) ∧ o ∈ Subgroup.centralizer (D : Set G) ∧
      Odd (orderOf o) ∧ Odd (orderOf (F.dA.ρ * o)) ∧
      F.dA.u * (F.dA.ρ * o) * F.dA.u * (F.dA.ρ * o) = 1 ∧
      F.dA.ρ * o ∈ Subgroup.normalizer (Q : Set G) ∧
      (F.dA.ρ * o) ^ 3 ∈ Subgroup.centralizer (Q : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := K ⊓ Subgroup.centralizer (D : Set G) with hOdef
  have hOodd : Odd (Nat.card O) := hKodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hρO := h.ρ_mem_normalizer_odd hKiff
  have huO := h.u_mem_normalizer_odd hKiff
  have huinv : F.dA.u⁻¹ = F.dA.u := inv_eq_of_mul_eq_one_right F.dA.u_sq
  have hQρ := S223.isSylowIn_map_conj hQ (inv_mem hρW)
  obtain ⟨x, hxW, hxQ⟩ := S223.exists_conj_of_isSylowIn hQ hQρ
  obtain ⟨q, hq, o', ho', rfl⟩ := S223.exists_mul_eq_of_isSylowIn hQ hOW hWO hOodd hpow x hxW
  set o'' := q * o' * q⁻¹ with ho''def
  have ho'' : o'' ∈ O := (Subgroup.mem_normalizer_iff.mp (hWO (hQ.1 hq)) o').mp ho'
  have hρ₁Q : F.dA.ρ * o'' ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro z
    have h1 := hxQ (F.dA.ρ⁻¹ * z * F.dA.ρ)
    rw [S223.mem_map_conj, inv_inv,
      show F.dA.ρ * (F.dA.ρ⁻¹ * z * F.dA.ρ) * F.dA.ρ⁻¹ = z by group] at h1
    rw [h1]
    have e : (q * o')⁻¹ * (F.dA.ρ⁻¹ * z * F.dA.ρ) * (q * o') =
        q⁻¹ * ((F.dA.ρ * o'')⁻¹ * z * (F.dA.ρ * o'')) * q := by
      rw [ho''def]; group
    rw [e]
    constructor
    · intro hz
      have := mul_mem (mul_mem hq hz) (inv_mem hq)
      rwa [show q * (q⁻¹ * ((F.dA.ρ * o'')⁻¹ * z * (F.dA.ρ * o'')) * q) * q⁻¹ =
        (F.dA.ρ * o'')⁻¹ * z * (F.dA.ρ * o'') by group] at this
    · intro hz
      exact mul_mem (mul_mem (inv_mem hq) hz) hq
  set Y := O ⊔ Subgroup.zpowers F.dA.ρ with hYdef
  have hYodd : Odd (Nat.card Y) := h.odd_card_sup_rho hKiff
  set K₁ := Y ⊓ Subgroup.normalizer (Q : Set G) with hK₁def
  have hK₁odd : Odd (Nat.card K₁) := hYodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have huρ : F.dA.u * F.dA.ρ * F.dA.u⁻¹ = F.dA.ρ⁻¹ := by
    have e := F.dA.u_rho
    rw [huinv]
    calc F.dA.u * F.dA.ρ * F.dA.u = F.dA.u * F.dA.ρ * F.dA.u * (F.dA.ρ * F.dA.ρ⁻¹) := by group
      _ = (F.dA.u * F.dA.ρ * F.dA.u * F.dA.ρ) * F.dA.ρ⁻¹ := by group
      _ = F.dA.ρ⁻¹ := by rw [e, one_mul]
  have huY : F.dA.u ∈ Subgroup.normalizer (Y : Set G) := by
    refine S223.mem_normalizer_of_conj_mem fun y hy => ?_
    obtain ⟨c, hc, j, rfl⟩ := h.mem_sup_rho hKiff hy
    have e : F.dA.u * (c * F.dA.ρ ^ j) * F.dA.u⁻¹ =
        (F.dA.u * c * F.dA.u⁻¹) * (F.dA.u * F.dA.ρ * F.dA.u⁻¹) ^ j := by
      rw [conj_zpow]; group
    rw [e, huρ]
    exact mul_mem (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp huO c).mp hc))
      (Subgroup.mem_sup_right ((Subgroup.zpowers F.dA.ρ).zpow_mem
        ((Subgroup.zpowers F.dA.ρ).inv_mem (Subgroup.mem_zpowers _)) j))
  have huK₁ : F.dA.u ∈ Subgroup.normalizer (K₁ : Set G) :=
    S223.mem_normalizer_of_conj_mem fun y hy =>
      ⟨(Subgroup.mem_normalizer_iff.mp huY y).mp hy.1,
        (Subgroup.normalizer (Q : Set G)).mul_mem
          ((Subgroup.normalizer (Q : Set G)).mul_mem huQ hy.2)
          ((Subgroup.normalizer (Q : Set G)).inv_mem huQ)⟩
  have hρ₁K₁ : F.dA.ρ * o'' ∈ K₁ :=
    ⟨Y.mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers F.dA.ρ))
      (Subgroup.mem_sup_left ho''), hρ₁Q⟩
  obtain ⟨⟨c, i⟩, ⟨hc, hi⟩, hci⟩ :=
    (CFSG.OddInversion.odd_involution_product_decomposition hK₁odd F.orderOf_u huK₁).1.surjOn
      hρ₁K₁
  dsimp only at hc hi hci
  have hcO : c ∈ O := by
    obtain ⟨c', hc', j, hcj⟩ := h.mem_sup_rho hKiff hc.1.1
    have hcu : c * F.dA.u = F.dA.u * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    have e1 : F.dA.u * c * F.dA.u⁻¹ = c := by rw [← hcu]; group
    have e2 : F.dA.u * c * F.dA.u⁻¹ = (F.dA.u * c' * F.dA.u⁻¹) * F.dA.ρ ^ (-j) := by
      rw [hcj, zpow_neg, ← inv_zpow, ← huρ, conj_zpow]; group
    have e3 : c'⁻¹ * (F.dA.u * c' * F.dA.u⁻¹) = F.dA.ρ ^ (2 * j) := by
      have h3 := e2.symm.trans (e1.trans hcj)
      have h4 : F.dA.u * c' * F.dA.u⁻¹ = c' * F.dA.ρ ^ j * F.dA.ρ ^ j := by
        calc F.dA.u * c' * F.dA.u⁻¹ =
            (F.dA.u * c' * F.dA.u⁻¹) * F.dA.ρ ^ (-j) * F.dA.ρ ^ j := by
              rw [mul_assoc _ (F.dA.ρ ^ (-j)), ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
          _ = c' * F.dA.ρ ^ j * F.dA.ρ ^ j := by rw [h3]
      rw [h4, two_mul, zpow_add]
      group
    have hρj := zpow_rho_mem_of_two (F := F) (O := O)
      (e3 ▸ mul_mem (inv_mem hc') ((Subgroup.mem_normalizer_iff.mp huO c').mp hc'))
    rw [hcj]
    exact mul_mem hc' hρj
  have hi' : i = c⁻¹ * (F.dA.ρ * o'') := by rw [← hci]; group
  have ho : F.dA.ρ⁻¹ * i ∈ O := by
    rw [hi']
    have h1 : F.dA.ρ⁻¹ * c⁻¹ * F.dA.ρ⁻¹⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (inv_mem hρO) c⁻¹).mp (inv_mem hcO)
    rw [inv_inv] at h1
    have := mul_mem h1 ho''
    convert this using 1
    group
  refine ⟨F.dA.ρ⁻¹ * i, hKC ho.1, ho.2, ((hKiff _).1 ho.1).2, ?_, ?_, ?_, ?_⟩
  · rw [mul_inv_cancel_left]
    exact hK₁odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard K₁ hi.1)
  · rw [mul_inv_cancel_left]
    have hinv := hi.2
    rw [huinv] at hinv
    rw [hinv]
    group
  · rw [mul_inv_cancel_left]
    exact hi.1.2
  · rw [mul_inv_cancel_left]
    set w := i ^ 3 with hw
    have hρ3D : F.dA.ρ ^ 3 ∈ Subgroup.centralizer (D : Set G) := h.ρ_eq ▸ dD.rho_cube_mem
    have hρ3E := F.rho_cube_mem_centralizer_E
    obtain ⟨o₀, ho₀⟩ : ∃ o₀, o₀ = F.dA.ρ⁻¹ * i := ⟨_, rfl⟩
    have hio : i = F.dA.ρ * o₀ := by rw [ho₀, mul_inv_cancel_left]
    rw [← ho₀] at ho
    have hwsplit : w = F.dA.ρ ^ 3 * ((F.dA.ρ⁻¹ * F.dA.ρ⁻¹ * o₀ * F.dA.ρ * F.dA.ρ) *
        (F.dA.ρ⁻¹ * o₀ * F.dA.ρ) * o₀) := by
      rw [hw, hio, pow_three]; group
    have hO1 : F.dA.ρ⁻¹ * o₀ * F.dA.ρ ∈ O := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hρO) o₀).mp ho
      rwa [inv_inv] at this
    have hO2 : F.dA.ρ⁻¹ * F.dA.ρ⁻¹ * o₀ * F.dA.ρ * F.dA.ρ ∈ O := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hρO) _).mp hO1
      rw [inv_inv] at this
      convert this using 1
      group
    have hprod := mul_mem (mul_mem hO2 hO1) ho
    have hwD : w ∈ Subgroup.centralizer (D : Set G) := by
      rw [hwsplit]; exact mul_mem hρ3D hprod.2
    have hwE : w ∈ Subgroup.centralizer (F.E : Set G) := by
      rw [hwsplit]; exact mul_mem hρ3E (hKC hprod.1)
    have hwodd : Odd (orderOf w) :=
      (hK₁odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard K₁ hi.1)).of_dvd_nat
        (orderOf_pow_dvd 3)
    have hwO : w ∈ O := ⟨(hKiff w).2 ⟨hwE, hwodd⟩, hwD⟩
    have hwQ : w ∈ Subgroup.normalizer (Q : Set G) := pow_mem hi.1.2 3
    rw [Subgroup.mem_centralizer_iff]
    intro q' hq'
    set z := q'⁻¹ * (w⁻¹ * q' * w) with hz
    have hzQ : z ∈ Q :=
      mul_mem (inv_mem hq') ((Subgroup.mem_normalizer_iff''.mp hwQ q').mp hq')
    have hzO : z ∈ O := by
      have h1 : q'⁻¹ * w⁻¹ * q'⁻¹⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp (inv_mem (hWO (hQ.1 hq'))) w⁻¹).mp (inv_mem hwO)
      rw [inv_inv] at h1
      have := mul_mem h1 hwO
      convert this using 1
      rw [hz]; group
    have hz1 : z = 1 := by
      obtain ⟨k, hk⟩ := hQ.2.1 ⟨z, hzQ⟩
      have hk' : z ^ (2 ^ k) = 1 := congrArg Subtype.val hk
      have hzodd : Odd (orderOf z) := hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hzO)
      have hdvd : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      have hcop : Nat.Coprime (orderOf z) (2 ^ k) :=
        Nat.Coprime.pow_right _ ((Nat.coprime_comm).mp (Nat.coprime_two_left.mpr hzodd))
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)
    calc q' * w = w * (w⁻¹ * q' * w) := by group
      _ = w * (q' * z) := by rw [hz]; group
      _ = w * q' := by rw [hz1, mul_one]

end StrothFrame.IsTyped

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem exists_rho_change_X (h : F.IsD D dD)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)))
    {X : Subgroup G} (hXp : IsPGroup 2 X) (hXS : X ≤ (F.S : Subgroup G))
    (hXN : X ≤ Subgroup.normalizer (D : Set G))
    (hXV : ∀ x ∈ X, x⁻¹ * F.dA.uv * x * F.dA.uv⁻¹ ∈ D ∧ x⁻¹ * F.dA.t * x * F.dA.t⁻¹ ∈ D)
    (hL : F.dA.L ≤ Subgroup.normalizer
      ((X ⊔ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G)) :
    ∃ o : G, o ∈ Subgroup.centralizer (F.E : Set G) ∧ o ∈ Subgroup.centralizer (D : Set G) ∧
      Odd (orderOf o) ∧ Odd (orderOf (F.dA.ρ * o)) ∧
      F.dA.u * (F.dA.ρ * o) * F.dA.u * (F.dA.ρ * o) = 1 ∧
      F.dA.uv ∈ Subgroup.normalizer ((X ⊔ D : Subgroup G) : Set G) ∧
      F.dA.t ∈ Subgroup.normalizer ((X ⊔ D : Subgroup G) : Set G) ∧
      F.dA.u ∈ Subgroup.normalizer ((X ⊔ D : Subgroup G) : Set G) ∧
      F.dA.ρ * o ∈ Subgroup.normalizer ((X ⊔ D : Subgroup G) : Set G) ∧
      (F.dA.ρ * o) ^ 3 ∈ Subgroup.centralizer ((X ⊔ D : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : F.IsTyped D dD := h.isTyped
  have hcomm := h.comm
  obtain ⟨K, hKC, hKodd, hKiff, hdec, -⟩ := exists_odd_complement_centralizer F.E_isE F.E_syl
  set Z := Subgroup.centralizer (D : Set G) with hZ
  set O := K ⊓ Z with hOdef
  set W := (X ⊔ Z) ⊓ S223X.commN D F.V with hW
  set C := X ⊔ D with hC
  have hDZ : D ≤ Z := fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hcomm y hy x hx
  have hDsyl : IsSylowIn 2 Z D := Local.isSylowIn_centralizer h.cent hns
  have hXZ : X ≤ Subgroup.normalizer (Z : Set G) := fun x hx =>
    S223.mem_normalizer_centralizer (hXN hx)
  have hsplit : ((X ⊔ Z : Subgroup G) : Set G) = (X : Set G) * (Z : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right X Z hXZ
  have huvinv : F.dA.uv⁻¹ = F.dA.uv := inv_eq_of_mul_eq_one_right F.dA.uv_sq
  have htinv : F.dA.t⁻¹ = F.dA.t := inv_eq_of_mul_eq_one_right F.dA.t_sq
  have hXcommN : X ≤ S223X.commN D F.V := fun x hx => by
    refine ⟨hXN hx, F.comm_mem_of_gens hT.V_le_normalizer ?_ ?_⟩
    · have e : x⁻¹ * (F.dA.uv⁻¹ * x * F.dA.uv) = x⁻¹ * F.dA.uv * x * F.dA.uv⁻¹ := by
        rw [huvinv]; group
      rw [e]
      exact (hXV x hx).1
    · have e : x⁻¹ * (F.dA.t⁻¹ * x * F.dA.t) = x⁻¹ * F.dA.t * x * F.dA.t⁻¹ := by
        rw [htinv]; group
      rw [e]
      exact (hXV x hx).2
  have hDcommN : D ≤ S223X.commN D F.V := fun d hd =>
    ⟨Subgroup.le_normalizer hd, fun v hv =>
      mul_mem (inv_mem hd) ((Subgroup.mem_normalizer_iff''.mp (hT.V_le_normalizer hv) d).mp hd)⟩
  have hCW : C ≤ W :=
    le_inf (sup_le le_sup_left (hDZ.trans le_sup_right)) (sup_le hXcommN hDcommN)
  have hCS : C ≤ (F.S : Subgroup G) := sup_le hXS h.le_S
  have hCp : IsPGroup 2 C := F.S.2.to_le hCS
  have hCsyl : IsSylowIn 2 W C := by
    obtain ⟨Q, hQ, hCQ⟩ := S223.exists_isSylowIn_ge hCW hCp
    have hQC : Q ≤ C := by
      intro q hq
      have hqM : q ∈ ((X ⊔ Z : Subgroup G) : Set G) := (hQ.1 hq).1
      rw [hsplit] at hqM
      obtain ⟨x, hx, k, hk, rfl⟩ := hqM
      have hxQ : x ∈ Q := hCQ (Subgroup.mem_sup_left hx)
      have hkQ : k ∈ Q := by
        have := mul_mem (inv_mem hxQ) hq
        rwa [inv_mul_cancel_left] at this
      have hkD : k ∈ D :=
        S223.le_of_isSylowIn hDsyl (le_inf ((le_sup_right : D ≤ C).trans hCQ) hDZ)
          inf_le_right (hQ.2.1.to_le inf_le_left) ⟨hkQ, hk⟩
      exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hkD)
    rwa [le_antisymm hQC hCQ] at hQ
  have hSWC : (F.S : Subgroup G) ⊓ W ≤ C :=
    S223.le_of_isSylowIn hCsyl (le_inf hCS hCW) inf_le_right (F.S.2.to_le inf_le_left)
  have hnormC : ∀ g ∈ (F.S : Subgroup G), g ∈ Subgroup.normalizer (W : Set G) →
      g ∈ Subgroup.normalizer (C : Set G) := fun g hgS hgW =>
    S223.mem_normalizer_of_conj_mem fun c hc =>
      hSWC (Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hgS (hCS hc)) (inv_mem hgS),
        (Subgroup.mem_normalizer_iff.mp hgW c).mp (hCW hc)⟩)
  have hnormW : ∀ g ∈ F.dA.L, g ∈ Subgroup.normalizer (D : Set G) →
      g ∈ Subgroup.normalizer (F.V : Set G) → g ∈ Subgroup.normalizer (W : Set G) :=
    fun g hgL hgD hgV =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hL hgL, S223X.mem_normalizer_commN hgD hgV⟩
  have huvW := hnormW _ F.dA.uv_mem_L hT.uv_mem_normalizer (Subgroup.le_normalizer F.uv_mem_V)
  have htW := hnormW _ F.dA.t_mem_L hT.t_mem_normalizer (Subgroup.le_normalizer F.t_mem_V)
  have huW := hnormW _ F.dA.u_mem_L hT.u_mem_normalizer F.u_mem_normalizer_V
  have hρW := hnormW _ F.dA.ρ_mem_L hT.ρ_mem_normalizer F.ρ_mem_normalizer_V
  have huC := hnormC _ F.u_mem_S huW
  have hOW : O ≤ W := fun o ho =>
    ⟨Subgroup.mem_sup_right ho.2, Subgroup.centralizer_le_normalizer _ ho.2, fun v hv => by
      have hc := (Subgroup.mem_centralizer_iff.mp (hKC ho.1)) v (F.V_le_E hv)
      rw [show v⁻¹ * o * v = o by rw [mul_assoc, ← hc]; group, inv_mul_cancel]
      exact one_mem _⟩
  have hWO : W ≤ Subgroup.normalizer (O : Set G) := by
    intro y hy
    refine S223.mem_normalizer_of_conj_mem fun o ho => ?_
    have hcD : y * o * y⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (S223.mem_normalizer_centralizer hy.2.1) o).mp ho.2
    have hcommV : ∀ v ∈ F.V, v * (y * o * y⁻¹) = (y * o * y⁻¹) * v := by
      intro v hv
      obtain ⟨d, hd⟩ : ∃ d, d = y⁻¹ * (v⁻¹ * y * v) := ⟨_, rfl⟩
      have hdD : d ∈ D := hd ▸ hy.2.2 v hv
      have hvy : v⁻¹ * y * v = y * d := by rw [hd]; group
      have hvo : v⁻¹ * o * v = o := by
        have hc := (Subgroup.mem_centralizer_iff.mp (hKC ho.1)) v (F.V_le_E hv)
        rw [mul_assoc, ← hc]; group
      have hdo : d * o = o * d := (Subgroup.mem_centralizer_iff.mp ho.2) d hdD
      symm
      calc y * o * y⁻¹ * v = v * ((v⁻¹ * y * v) * (v⁻¹ * o * v) * (v⁻¹ * y * v)⁻¹) := by group
        _ = v * (y * (d * o) * d⁻¹ * y⁻¹) := by rw [hvy, hvo]; group
        _ = v * (y * (o * d) * d⁻¹ * y⁻¹) := by rw [hdo]
        _ = v * (y * o * y⁻¹) := by group
    refine ⟨(hKiff _).2 ⟨hT.mem_centralizer_E hcD (hcommV _ F.uv_mem_V)
      (hcommV _ F.t_mem_V), ?_⟩, hcD⟩
    rw [show y * o * y⁻¹ = MulAut.conj y o by rfl, MulEquiv.orderOf_eq]
    exact ((hKiff o).1 ho.1).2
  have hpow : ∀ y ∈ W, ∃ n : ℕ, y ^ (2 ^ n) ∈ O := by
    intro y hy
    have hyM : y ∈ ((X ⊔ Z : Subgroup G) : Set G) := hy.1
    rw [hsplit] at hyM
    obtain ⟨x, hx, k, hk, hxk⟩ := hyM
    obtain ⟨a, ha⟩ := hXp ⟨x, hx⟩
    have ha' : x ^ (2 ^ a) = 1 := congrArg Subtype.val ha
    have hyZ : y ^ (2 ^ a) ∈ Z := by
      obtain ⟨k', hk', e⟩ := S223X.exists_pow_mul_eq (hXZ hx) hk (2 ^ a)
      rw [← hxk, e, ha', one_mul]
      exact hk'
    have hyX : y ^ (2 ^ a) ∈ S223.commX D F.V := ⟨hyZ, (pow_mem hy (2 ^ a)).2.2⟩
    obtain ⟨n, hn⟩ := hT.pow_mem_odd_of_mem_commX hKC hKiff hdec hyX
    exact ⟨a + n, by rw [pow_add, pow_mul]; exact hn⟩
  obtain ⟨o, hoE, hoD, hoodd, hρodd, hu, hρC, hρ3C⟩ :=
    hT.exists_rho_change_of_isSylowIn hKC hKodd hKiff hCsyl hOW hWO hpow hρW huC
  exact ⟨o, hoE, hoD, hoodd, hρodd, hu, hnormC _ F.uv_mem_S huvW, hnormC _ F.t_mem_S htW, huC,
    hρC, hρ3C⟩

end StrothFrame.IsD

end CFSG.CGT.Stroth77
