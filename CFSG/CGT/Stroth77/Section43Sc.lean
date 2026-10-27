module

public import CFSG.CGT.Stroth77.Section42
public import CFSG.CGT.Stroth77.Section43CoreIV
public import CFSG.CGT.Stroth77.Section43Fus
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.CGT.Stroth77

open CFSG.ABGLocalTools (IsSylowOf)

namespace Stroth43Sc

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowOf_le {Q K : Subgroup G} (hQK : Q ≤ K) (hQ : IsPGroup 2 Q) :
    ∃ P : Subgroup G, IsSylowOf 2 P K ∧ Q ≤ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ' : IsPGroup 2 (Q.subgroupOf K) := hQ.comap_subtype
  obtain ⟨R, hR⟩ := hQ'.exists_le_sylow
  refine ⟨(R : Subgroup K).map K.subtype, ⟨R, rfl⟩, fun q hq => ?_⟩
  exact ⟨⟨q, hQK hq⟩, hR (Subgroup.mem_subgroupOf.mpr hq), rfl⟩

theorem exists_conj_le_of_isSylowOf {P Q K : Subgroup G} (hP : IsSylowOf 2 P K) (hQK : Q ≤ K)
    (hQ : IsPGroup 2 Q) : ∃ c ∈ K, ∀ q ∈ Q, c⁻¹ * q * c ∈ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P', hP', hQP'⟩ := exists_isSylowOf_le hQK hQ
  obtain ⟨c, hc, hcP⟩ := hP.exists_mem_conj hP'
  exact ⟨c, hc, fun q hq => (hcP q).mp (hQP' hq)⟩

@[instance_reducible]
private def conjMulAction (N : Subgroup G) : MulAction ↥N G :=
  letI : SMul ↥N G := ⟨fun x g => (x : G) * g * (x : G)⁻¹⟩
  { one_smul := fun g => by
      show (1 : G) * g * (1 : G)⁻¹ = g
      simp
    mul_smul := fun x y g => by
      show ((x * y : ↥N) : G) * g * ((x * y : ↥N) : G)⁻¹ =
        (x : G) * ((y : G) * g * (y : G)⁻¹) * (x : G)⁻¹
      simp [mul_assoc] }

theorem card_eq_card_conj_mul (N : Subgroup G) (g : G) :
    Nat.card N = Nat.card {x : G | ∃ n ∈ N, n * g * n⁻¹ = x} *
      Nat.card ↥(N ⊓ Subgroup.centralizer {g}) := by
  letI : MulAction ↥N G := conjMulAction N
  have horbit : MulAction.orbit ↥N g = {x : G | ∃ n ∈ N, n * g * n⁻¹ = x} := by
    ext x
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, n.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
  have hstab : MulAction.stabilizer ↥N g =
      (N ⊓ Subgroup.centralizer ({g} : Set G)).subgroupOf N := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    change (x : G) * g * (x : G)⁻¹ = g ↔ (x : G) ∈ N ∧ (x : G) * g = g * (x : G)
    exact ⟨fun h => ⟨x.2, mul_inv_eq_iff_eq_mul.mp h⟩,
      fun h => mul_inv_eq_iff_eq_mul.mpr h.2⟩
  have h := (Subgroup.card_mul_index (MulAction.stabilizer ↥N g)).symm
  rw [MulAction.index_stabilizer, horbit, hstab,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : N ⊓
      Subgroup.centralizer ({g} : Set G) ≤ N)).toEquiv] at h
  rw [h, Nat.card_coe_set_eq, mul_comm]

theorem conj_pow_eq (g x : G) (k : ℕ) : (g⁻¹ * x * g) ^ k = g⁻¹ * x ^ k * g := by
  simpa using conj_pow (a := g⁻¹) (b := x) (i := k)

theorem conj_mem_iff_of_map_eq {D : Subgroup G} {k : G}
    (hk : D.map (MulAut.conj k⁻¹).toMonoidHom = D) {x : G} : k⁻¹ * x * k ∈ D ↔ x ∈ D := by
  constructor
  · intro hx
    rw [← hk] at hx
    obtain ⟨d, hd, hdx⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hdx
    have : d = x := by
      have := congrArg (fun y => k * y * k⁻¹) hdx
      simpa [mul_assoc] using this
    exact this ▸ hd
  · intro hx
    rw [← hk]
    exact ⟨x, hx, by simp⟩

theorem mem_normalizer_of_conj_mem {D : Subgroup G} {n : G} (hn : ∀ d ∈ D, n⁻¹ * d * n ∈ D) :
    n ∈ Subgroup.normalizer (D : Set G) := by
  have hle : D.map (MulAut.conj n⁻¹).toMonoidHom ≤ D := by
    rintro _ ⟨d, hd, rfl⟩
    simpa using hn d hd
  have heq : D.map (MulAut.conj n⁻¹).toMonoidHom = D :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective).ge
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : x ∈ D.map (MulAut.conj n⁻¹).toMonoidHom := heq.symm ▸ hx
    obtain ⟨d, hd, rfl⟩ := hx'
    simpa [mul_assoc] using hd
  · intro hx
    simpa [mul_assoc] using hn _ hx

section Config

variable {F : StrothFrame G} {D : Subgroup G} {m : ℕ} {dD : StrothWeakTypeData D (.t100 m)}
  {e : G}

theorem c₂_sq (dD : StrothWeakTypeData D (.t100 m)) (hm : 2 ≤ m) :
    (dD.c : G) ^ 2 ^ (m - 2) * (dD.c : G) ^ 2 ^ (m - 2) = (dD.c : G) ^ 2 ^ (m - 1) := by
  rw [← pow_add, ← two_mul, ← pow_succ', show m - 2 + 1 = m - 1 by omega]

variable (h : F.IsD D dD) (hm : 2 ≤ m)
  (hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
    orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y)
  (heN : e ∈ Subgroup.normalizer (D : Set G))
  (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
  (heuv : e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv)
  (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t) (hue : e⁻¹ * dD.u * e = dD.u)
  (hce : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹)
  (hae : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ m)
  (hbe : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ m)
  (he : e * e = (dD.c : G) ^ 2 ^ (m - 1))

include h hm hnc heN hS heuv het hue hce hae hbe he in
theorem conj_le_S {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQz : Q ≤ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) :
    ∃ k ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}, ∀ q ∈ Q,
      k⁻¹ * q * k ∈ (F.S : Subgroup G) := by
  set P := Subgroup.closure {dD.uv, dD.t, dD.u} with hP
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  have hPN : P ≤ Subgroup.normalizer (D : Set G) := by
    rw [hP, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    exacts [dD.uv_mem, dD.t_mem, dD.u_mem]
  have hSD : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) := by
    rw [hS]
    exact sup_le (sup_le Subgroup.le_normalizer hPN) ((Subgroup.zpowers_le).2 heN)
  have hPS : P ≤ (F.S : Subgroup G) := by rw [hS]; exact le_sup_right.trans le_sup_left
  have hz2 : z * z = 1 := Stroth43Fus.t100_c₁_mul_self dD (by omega)
  have hz1 : z ≠ 1 := Stroth43Fus.t100_c₁_ne_one dD (by omega)
  have hzD : z ∈ D := D.pow_mem dD.c.2 _
  have h3 := dD.t100_h3 hm
  have hza := h.not_isConj_of_omega hnc h3
  have h3' : ∀ y ∈ D, y * y = 1 → y ≠ 1 → IsConj y z → ∃ p ∈ P, p⁻¹ * y * p = z := by
    intro y hyD hy2 hy1 hyz
    rcases h3 y hyD hy2 hy1 with hp | ⟨g, -, hg⟩
    · exact hp
    · exact absurd (hyz.symm.trans (Stroth42.isConj_of_conj_eq hg).symm) hza
  have h9 := dD.iv_h9 hm heuv het hue hce hae hbe he
  rw [← hS] at h9
  exact Stroth42.exists_conj_le_centralizer F.S dD.isMulCommutative h.le_S hSD hPS hzD h3' hz2
    hz1 h9 hQ hQz

include hm hS heuv het hue hce hae hbe he in
theorem map_conj_eq {k : G}
    (hk : ∀ d ∈ D, k⁻¹ * d * k ∈ (F.S : Subgroup G) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) :
    D.map (MulAut.conj k⁻¹).toMonoidHom = D := by
  have h9 := dD.iv_h9 hm heuv het hue hce hae hbe he
  rw [← hS] at h9
  refine h9 _ ?_ ?_ (Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective)
  · rintro _ ⟨d, hd, rfl⟩
    simpa using hk d hd
  · haveI := dD.isMulCommutative
    exact Subgroup.map_isMulCommutative D _

include hm hS heuv het hue hce hae hbe he in
theorem nf_of_mem {y : G} (hyS : y ∈ (F.S : Subgroup G))
    (hyz : y ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) :
    ∃ (v : Torus (StrothTypeIndex.t100 m).k) (l k : Bool),
      y = dD.ofTorus v * dD.d8 false false l * Stroth42Core.bpow e k := by
  set hE := dD.ivAction heuv het hue hce hae hbe he with hEdef
  have hm1 : 1 ≤ m := by omega
  rw [hS] at hyS
  obtain ⟨v, i, j, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hyS
  have hφ : hE.φe (Stroth42Core.om100 m ![1, 0, 0]) = Stroth42Core.om100 m ![1, 0, 0] := by
    rw [hEdef, dD.ivAction_φe heuv het hue hce hae hbe he]
    exact StrothWeakTypeData.torusDiag_om100_of_odd hm1 (by norm_num)
      (StrothWeakTypeData.neg_one_add_two_pow_emod_two hm1)
      (StrothWeakTypeData.neg_one_add_two_pow_emod_two hm1) _
  rw [Subgroup.mem_centralizer_iff] at hyz
  obtain ⟨rfl, rfl⟩ :=
    StrothWeakTypeData.EAction.t100_comm_c₁ dD hE hm1 hφ (hyz _ (Set.mem_singleton _)).symm
  exact ⟨v, l, k, rfl⟩

include hm hS heuv het hue hce hae hbe he in
theorem card_CSz_le :
    Nat.card ↥((F.S : Subgroup G) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) ≤
      4 * Nat.card D := by
  have hcov := Stroth42Core.natCard_le_of_subset_range
    (E := (F.S : Subgroup G) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)})
    (fun p : Torus (StrothTypeIndex.t100 m).k × Bool × Bool =>
      dD.ofTorus p.1 * dD.d8 false false p.2.1 * Stroth42Core.bpow e p.2.2)
    (fun y hy => by
      obtain ⟨v, l, k, rfl⟩ := nf_of_mem hm hS heuv het hue hce hae hbe he
        (Subgroup.mem_inf.mp hy).1 (Subgroup.mem_inf.mp hy).2
      exact ⟨(v, l, k), rfl⟩)
  have hT : Nat.card D = Nat.card (Torus (StrothTypeIndex.t100 m).k) :=
    Nat.card_congr (Additive.ofMul.trans dD.e.toEquiv)
  calc _ ≤ Nat.card (Torus (StrothTypeIndex.t100 m).k × Bool × Bool) := hcov
    _ = 4 * Nat.card D := by
      rw [Nat.card_prod, Nat.card_prod, ← hT, Nat.card_eq_fintype_card (α := Bool),
        Fintype.card_bool]
      ring

theorem nf_comm_c₂ (dD : StrothWeakTypeData D (.t100 m)) (v : Torus (StrothTypeIndex.t100 m).k)
    (l : Bool) :
    dD.ofTorus v * dD.d8 false false l * (dD.c : G) ^ 2 ^ (m - 2) =
      (dD.c : G) ^ 2 ^ (m - 2) * (dD.ofTorus v * dD.d8 false false l) := by
  rw [show (dD.c : G) ^ 2 ^ (m - 2) = dD.ofTorus ((2 ^ (m - 2)) • Torus.c) by
    rw [StrothWeakTypeData.ofTorus_nsmul, ← StrothWeakTypeData.c_eq]]
  refine (dD.nf_commute_iff v _ false false l).mpr ?_
  cases l <;> simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply, map_nsmul, StrothWeakTypeData.t100_φu_c]

include hm hS heuv het hue hce hae hbe he in
theorem nf_of_comm_c₂ {y : G} (hyS : y ∈ (F.S : Subgroup G))
    (hyz : y ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)})
    (hyc : y * (dD.c : G) ^ 2 ^ (m - 2) = (dD.c : G) ^ 2 ^ (m - 2) * y) :
    ∃ (v : Torus (StrothTypeIndex.t100 m).k) (l : Bool),
      y = dD.ofTorus v * dD.d8 false false l := by
  obtain ⟨v, l, k, rfl⟩ := nf_of_mem hm hS heuv het hue hce hae hbe he hyS hyz
  cases k
  · exact ⟨v, l, by simp [Stroth42Core.bpow]⟩
  · exfalso
    set c₂ := (dD.c : G) ^ 2 ^ (m - 2) with hc₂
    set X := dD.ofTorus v * dD.d8 false false l with hX
    have hw : X * c₂ = c₂ * X := nf_comm_c₂ dD v l
    simp only [Stroth42Core.bpow, ↓reduceIte] at hyc
    have hec : e * c₂ = c₂ * e := by
      have h1 : X * (e * c₂) = X * (c₂ * e) := by
        calc X * (e * c₂) = X * e * c₂ := by group
          _ = c₂ * (X * e) := hyc
          _ = (c₂ * X) * e := by group
          _ = (X * c₂) * e := by rw [hw]
          _ = X * (c₂ * e) := by group
      exact mul_left_cancel h1
    have hinv : e⁻¹ * c₂ * e = c₂⁻¹ := by
      rw [hc₂, ← conj_pow_eq, hce, inv_pow]
    have h2 : c₂ = c₂⁻¹ := by
      rw [← hinv, mul_assoc, ← hec, ← mul_assoc, inv_mul_cancel, one_mul]
    apply Stroth43Fus.t100_c₁_ne_one dD (by omega : 1 ≤ m)
    rw [← c₂_sq dD hm, ← hc₂]
    calc c₂ * c₂ = c₂ * c₂⁻¹ := by rw [← h2]
      _ = 1 := mul_inv_cancel c₂

theorem nf_mul_self_mem (dD : StrothWeakTypeData D (.t100 m))
    (v : Torus (StrothTypeIndex.t100 m).k) (l : Bool) :
    dD.ofTorus v * dD.d8 false false l * (dD.ofTorus v * dD.d8 false false l) ∈ D := by
  rw [dD.nf_mul_self_of_false v (by cases l <;> rfl)]
  exact dD.ofTorus_mem _

theorem e_mem_centralizer (he : e * e = (dD.c : G) ^ 2 ^ (m - 1)) :
    e ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} :=
  Subgroup.mem_centralizer_singleton_iff.2 (by rw [← he, mul_assoc])

theorem rho_mul_c (dD : StrothWeakTypeData D (.t100 m)) :
    dD.ρ * (dD.c : G) = (dD.c : G) * dD.ρ := by
  have h := dD.conj_ofTorus dD.ρ_mem dD.ρ_conj Torus.c
  rw [show (StrothTypeIndex.t100 m).action.φρ Torus.c = Torus.c from
    (Type100.rho_c m).trans (one_zsmul _), ← StrothWeakTypeData.c_eq] at h
  calc dD.ρ * (dD.c : G) = dD.ρ * (dD.ρ⁻¹ * (dD.c : G) * dD.ρ) := by rw [h]
    _ = (dD.c : G) * dD.ρ := by group

theorem rho_mem_centralizer (dD : StrothWeakTypeData D (.t100 m)) :
    dD.ρ ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} :=
  Subgroup.mem_centralizer_singleton_iff.2 (Commute.pow_right (rho_mul_c dD) _).eq

include h hm hnc heN hS heuv het hue hce hae hbe he in
theorem exists_normalizer_conj_eq {g y : G}
    (hg : g ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) (hyD : y ∈ D)
    (hgy : g⁻¹ * y * g ∈ D) :
    ∃ n ∈ Subgroup.normalizer (D : Set G) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
      n⁻¹ * y * n = g⁻¹ * y * g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  set y' := g⁻¹ * y * g with hy'
  set Z := Subgroup.centralizer ({z} : Set G) with hZ
  set H := Z ⊓ Subgroup.centralizer {y'} with hH
  have hzD : z ∈ D := D.pow_mem dD.c.2 _
  have hcommD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hDz : D ≤ Z := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcommD d hd z hzD)
  have hDH : D ≤ H := le_inf hDz (fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcommD d hd y' hgy))
  have hDp : IsPGroup 2 D := F.S.isPGroup'.to_le h.le_S
  obtain ⟨P, hP, hDP⟩ := exists_isSylowOf_le hDH hDp
  set Q₀ := D.map (MulAut.conj g⁻¹).toMonoidHom with hQ₀
  have hQ₀H : Q₀ ≤ H := by
    rintro _ ⟨d, hd, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine Subgroup.mem_inf.2 ⟨Z.mul_mem (Z.mul_mem (Z.inv_mem hg) (hDz hd)) hg, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hcommD d hd y hyD
    calc g⁻¹ * d * g * (g⁻¹ * y * g) = g⁻¹ * (d * y) * g := by group
      _ = g⁻¹ * (y * d) * g := by rw [this]
      _ = g⁻¹ * y * g * (g⁻¹ * d * g) := by group
  obtain ⟨c, hcH, hcQ⟩ := exists_conj_le_of_isSylowOf hP hQ₀H (hDp.map _)
  have hcz : c ∈ Z := (Subgroup.mem_inf.1 hcH).1
  obtain ⟨k, hkz, hkP⟩ := conj_le_S h hm hnc heN hS heuv het hue hce hae hbe he hP.isPGroup
    (hP.le.trans inf_le_left)
  have hk : D.map (MulAut.conj k⁻¹).toMonoidHom = D :=
    map_conj_eq hm hS heuv het hue hce hae hbe he (fun d hd => Subgroup.mem_inf.2
      ⟨hkP d (hDP hd), Z.mul_mem (Z.mul_mem (Z.inv_mem hkz) (hDz hd)) hkz⟩)
  have hgck : D.map (MulAut.conj (g * c * k)⁻¹).toMonoidHom = D := by
    refine map_conj_eq hm hS heuv het hue hce hae hbe he (fun d hd => ?_)
    have hq : g⁻¹ * d * g ∈ Q₀ := ⟨d, hd, by simp⟩
    rw [show (g * c * k)⁻¹ * d * (g * c * k) = k⁻¹ * (c⁻¹ * (g⁻¹ * d * g) * c) * k by group]
    refine Subgroup.mem_inf.2 ⟨hkP _ (hcQ _ hq), ?_⟩
    exact Z.mul_mem (Z.mul_mem (Z.inv_mem hkz) (Z.mul_mem (Z.mul_mem (Z.inv_mem hcz)
      (Z.mul_mem (Z.mul_mem (Z.inv_mem hg) (hDz hd)) hg)) hcz)) hkz
  refine ⟨g * c, Subgroup.mem_inf.2 ⟨?_, Z.mul_mem hg hcz⟩, ?_⟩
  · apply mem_normalizer_of_conj_mem
    intro d hd
    have h1 : (g * c * k)⁻¹ * d * (g * c * k) ∈ D := (conj_mem_iff_of_map_eq hgck).mpr hd
    rw [show (g * c * k)⁻¹ * d * (g * c * k) = k⁻¹ * ((g * c)⁻¹ * d * (g * c)) * k by group] at h1
    exact (conj_mem_iff_of_map_eq hk).mp h1
  · have hcy := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hcH).2
    calc (g * c)⁻¹ * y * (g * c) = c⁻¹ * (y' * c) := by rw [hy']; group
      _ = c⁻¹ * (c * y') := by rw [hcy]
      _ = g⁻¹ * y * g := by rw [hy']; group

theorem eq_toNat_decide {x : ℤ} (hx : x = 0 ∨ x = 1) : x = ((decide (x = 1)).toNat : ℤ) := by
  rcases hx with rfl | rfl <;> rfl

theorem om100_bool_eq_iff (hm1 : 1 ≤ m) (b₀ b₁ b₂ c₀ c₁ c₂ : Bool) :
    Stroth42Core.om100 m ![(b₀.toNat : ℤ), (b₁.toNat : ℤ), (b₂.toNat : ℤ)] =
        Stroth42Core.om100 m ![(c₀.toNat : ℤ), (c₁.toNat : ℤ), (c₂.toNat : ℤ)] ↔
      b₀ = c₀ ∧ b₁ = c₁ ∧ b₂ = c₂ := by
  rw [Stroth42Core.om100_eq_iff hm1]
  cases b₀ <;> cases b₁ <;> cases b₂ <;> cases c₀ <;> cases c₁ <;> cases c₂ <;> decide

include h hm hnc heN hS heuv het hue hce hae hbe he in
theorem normalizer_conj_c₂ {n : G}
    (hn : n ∈ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) :
    n⁻¹ * (dD.c : G) ^ 2 ^ (m - 2) * n = (dD.c : G) ^ 2 ^ (m - 2) ∨
      n⁻¹ * (dD.c : G) ^ 2 ^ (m - 2) * n = ((dD.c : G) ^ 2 ^ (m - 2))⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hne1, hne2⟩ := hne
  have hm1 : 1 ≤ m := by omega
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  set c₂ := (dD.c : G) ^ 2 ^ (m - 2) with hc₂
  set Z := Subgroup.centralizer ({z} : Set G) with hZ
  set N := Subgroup.normalizer (D : Set G) ⊓ Z with hN
  have hzD : z ∈ D := D.pow_mem dD.c.2 _
  have hc₂D : c₂ ∈ D := D.pow_mem dD.c.2 _
  have hcommD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hc₂sq : c₂ * c₂ = z := c₂_sq dD hm
  have hz2 : z * z = 1 := Stroth43Fus.t100_c₁_mul_self dD hm1
  have hz1 : z ≠ 1 := Stroth43Fus.t100_c₁_ne_one dD hm1
  have hc₂z : c₂ * z = c₂⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← hc₂sq]
    calc c₂ * (c₂ * c₂) * c₂ = (c₂ * c₂) * (c₂ * c₂) := by group
      _ = 1 := by rw [hc₂sq, hz2]
  have hzom : z = dD.ofTorus (Stroth42Core.om100 m ![1, 0, 0]) := dD.t100_c_pow
  have heNz : e ∈ N := Subgroup.mem_inf.2 ⟨heN, e_mem_centralizer he⟩
  have hρN : dD.ρ ∈ N := Subgroup.mem_inf.2 ⟨dD.ρ_mem, rho_mem_centralizer dD⟩
  set O : Set G := {x | ∃ n' ∈ N, n' * c₂ * n'⁻¹ = x} with hO
  have hO_conj : ∀ x ∈ O, ∀ n' ∈ N, n'⁻¹ * x * n' ∈ O := by
    rintro x ⟨n₀, hn₀, rfl⟩ n' hn'
    exact ⟨n'⁻¹ * n₀, N.mul_mem (N.inv_mem hn') hn₀, by group⟩
  have hc₂O : c₂ ∈ O := ⟨1, N.one_mem, by group⟩
  have he_om : ∀ ε : Fin 3 → ℤ, e⁻¹ * (c₂ * dD.ofTorus (Stroth42Core.om100 m ε)) * e =
      c₂ * dD.ofTorus (Stroth42Core.om100 m (![1, 0, 0] + ε)) := by
    intro ε
    have h1 : e⁻¹ * c₂ * e = c₂ * z := by rw [hc₂z, hc₂, ← conj_pow_eq, hce, inv_pow]
    have h2 : e⁻¹ * dD.ofTorus (Stroth42Core.om100 m ε) * e =
        dD.ofTorus (Stroth42Core.om100 m ε) := by
      rw [(dD.ivAction heuv het hue hce hae hbe he).conj_ofTorus,
        dD.ivAction_φe heuv het hue hce hae hbe he,
        StrothWeakTypeData.torusDiag_om100_of_odd hm1 (by norm_num)
          (StrothWeakTypeData.neg_one_add_two_pow_emod_two hm1)
          (StrothWeakTypeData.neg_one_add_two_pow_emod_two hm1)]
    rw [show e⁻¹ * (c₂ * dD.ofTorus (Stroth42Core.om100 m ε)) * e =
        (e⁻¹ * c₂ * e) * (e⁻¹ * dD.ofTorus (Stroth42Core.om100 m ε) * e) by group, h1, h2, hzom,
      mul_assoc, ← dD.ofTorus_add, Stroth43Fus.om100_add]
  have hρ_om : ∀ ε : Fin 3 → ℤ, dD.ρ⁻¹ * (c₂ * dD.ofTorus (Stroth42Core.om100 m ε)) * dD.ρ =
      c₂ * dD.ofTorus (Stroth42Core.om100 m ![ε 0 - 4 * ε 2, -ε 2, ε 1 - ε 2]) := by
    intro ε
    have h1 : dD.ρ⁻¹ * c₂ * dD.ρ = c₂ := by
      have hρc₂ : dD.ρ * c₂ = c₂ * dD.ρ := (Commute.pow_right (rho_mul_c dD) _).eq
      calc dD.ρ⁻¹ * c₂ * dD.ρ = dD.ρ⁻¹ * (c₂ * dD.ρ) := by group
        _ = dD.ρ⁻¹ * (dD.ρ * c₂) := by rw [hρc₂]
        _ = c₂ := by group
    rw [show dD.ρ⁻¹ * (c₂ * dD.ofTorus (Stroth42Core.om100 m ε)) * dD.ρ =
        (dD.ρ⁻¹ * c₂ * dD.ρ) * (dD.ρ⁻¹ * dD.ofTorus (Stroth42Core.om100 m ε) * dD.ρ) by group,
      h1, dD.conj_ofTorus dD.ρ_mem dD.ρ_conj, Stroth42Core.t100_φρ_om hm1]
  have hQe : ∀ b₀ b₁ b₂ : Bool,
      c₂ * dD.ofTorus (Stroth42Core.om100 m ![(b₀.toNat : ℤ), (b₁.toNat : ℤ), (b₂.toNat : ℤ)])
        ∈ O →
      c₂ * dD.ofTorus (Stroth42Core.om100 m ![((!b₀).toNat : ℤ), (b₁.toNat : ℤ), (b₂.toNat : ℤ)])
        ∈ O := by
    intro b₀ b₁ b₂ hq
    have h1 := hO_conj _ hq e heNz
    rw [he_om] at h1
    convert h1 using 3
    exact (Stroth42Core.om100_eq_iff hm1 _ _).mpr (by cases b₀ <;> cases b₁ <;> cases b₂ <;> decide)
  have hQρ : ∀ b₀ b₁ b₂ : Bool,
      c₂ * dD.ofTorus (Stroth42Core.om100 m ![(b₀.toNat : ℤ), (b₁.toNat : ℤ), (b₂.toNat : ℤ)])
        ∈ O →
      c₂ * dD.ofTorus (Stroth42Core.om100 m
        ![(b₀.toNat : ℤ), (b₂.toNat : ℤ), ((xor b₁ b₂).toNat : ℤ)]) ∈ O := by
    intro b₀ b₁ b₂ hq
    have h1 := hO_conj _ hq dD.ρ hρN
    rw [hρ_om] at h1
    convert h1 using 3
    exact (Stroth42Core.om100_eq_iff hm1 _ _).mpr (by cases b₀ <;> cases b₁ <;> cases b₂ <;> decide)
  have hkey : ∀ b₀ b₁ b₂ : Bool, (b₁ || b₂) = true →
      c₂ * dD.ofTorus (Stroth42Core.om100 m ![(b₀.toNat : ℤ), (b₁.toNat : ℤ), (b₂.toNat : ℤ)])
        ∈ O →
      ∀ d₀ d₁ d₂ : Bool, (d₁ || d₂) = true →
        c₂ * dD.ofTorus (Stroth42Core.om100 m ![(d₀.toNat : ℤ), (d₁.toNat : ℤ), (d₂.toNat : ℤ)])
          ∈ O := by
    intro b₀ b₁ b₂ hb hq d₀ d₁ d₂ hd
    have q1 := hQρ _ _ _ hq
    have q2 := hQρ _ _ _ q1
    have q3 := hQe _ _ _ hq
    have q4 := hQe _ _ _ q1
    have q5 := hQe _ _ _ q2
    cases b₀ <;> cases b₁ <;> cases b₂ <;> cases d₀ <;> cases d₁ <;> cases d₂ <;>
      simp only [Bool.or_false, Bool.or_true, Bool.false_eq_true, Bool.xor_false,
        Bool.xor_true, Bool.not_false, Bool.not_true, Bool.false_or] at hb hd q1 q2 q3 q4 q5 ⊢ <;>
      first | assumption | exact absurd hb (by decide) | exact absurd hd (by decide)
  have hx₀O : n⁻¹ * c₂ * n ∈ O := ⟨n⁻¹, N.inv_mem hn, by group⟩
  have hx₀D : n⁻¹ * c₂ * n ∈ D :=
    (Subgroup.mem_normalizer_iff''.mp (Subgroup.mem_inf.1 hn).1 c₂).mp hc₂D
  have hx₀sq : n⁻¹ * c₂ * n * (n⁻¹ * c₂ * n) = z := by
    have hnz := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hn).2
    calc n⁻¹ * c₂ * n * (n⁻¹ * c₂ * n) = n⁻¹ * (c₂ * c₂) * n := by group
      _ = n⁻¹ * (z * n) := by rw [hc₂sq]; group
      _ = n⁻¹ * (n * z) := by rw [hnz]
      _ = z := by group
  have hs₀D : c₂⁻¹ * (n⁻¹ * c₂ * n) ∈ D := D.mul_mem (D.inv_mem hc₂D) hx₀D
  have hs₀sq : c₂⁻¹ * (n⁻¹ * c₂ * n) * (c₂⁻¹ * (n⁻¹ * c₂ * n)) = 1 := by
    have hc := hcommD _ hx₀D _ (D.inv_mem hc₂D)
    calc c₂⁻¹ * (n⁻¹ * c₂ * n) * (c₂⁻¹ * (n⁻¹ * c₂ * n))
        = c₂⁻¹ * ((n⁻¹ * c₂ * n) * c₂⁻¹) * (n⁻¹ * c₂ * n) := by group
      _ = c₂⁻¹ * (c₂⁻¹ * (n⁻¹ * c₂ * n)) * (n⁻¹ * c₂ * n) := by rw [hc]
      _ = (c₂ * c₂)⁻¹ * (n⁻¹ * c₂ * n * (n⁻¹ * c₂ * n)) := by group
      _ = 1 := by rw [hc₂sq, hx₀sq, inv_mul_cancel]
  obtain ⟨δ, hδ, hδs⟩ := dD.t100_eq_om_of_mul_self hm1 hs₀D hs₀sq
  have hδb : δ = ![((decide (δ 0 = 1)).toNat : ℤ), ((decide (δ 1 = 1)).toNat : ℤ),
      ((decide (δ 2 = 1)).toNat : ℤ)] := by
    funext i
    fin_cases i
    · exact eq_toNat_decide (hδ 0)
    · exact eq_toNat_decide (hδ 1)
    · exact eq_toNat_decide (hδ 2)
  have hx₀ : n⁻¹ * c₂ * n = c₂ * dD.ofTorus (Stroth42Core.om100 m ![((decide (δ 0 = 1)).toNat : ℤ),
      ((decide (δ 1 = 1)).toNat : ℤ), ((decide (δ 2 = 1)).toNat : ℤ)]) := by
    rw [← hδb, ← hδs]; group
  have hb12 : (decide (δ 1 = 1) || decide (δ 2 = 1)) = true := by
    by_contra hb
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hb
    have hδ1 : δ 1 = 0 := (hδ 1).resolve_right hb.1
    have hδ2 : δ 2 = 0 := (hδ 2).resolve_right hb.2
    rcases hδ 0 with h0 | h0
    · apply hne1
      rw [hx₀, show (![((decide (δ 0 = 1)).toNat : ℤ), ((decide (δ 1 = 1)).toNat : ℤ),
        ((decide (δ 2 = 1)).toNat : ℤ)] : Fin 3 → ℤ) = 0 by
          funext i; fin_cases i <;> simp [h0, hδ1, hδ2], Stroth42Core.om100_zero,
        dD.ofTorus_zero, mul_one]
    · apply hne2
      rw [hx₀, show (![((decide (δ 0 = 1)).toNat : ℤ), ((decide (δ 1 = 1)).toNat : ℤ),
        ((decide (δ 2 = 1)).toNat : ℤ)] : Fin 3 → ℤ) = ![1, 0, 0] by
          funext i; fin_cases i <;> simp [h0, hδ1, hδ2], ← hzom, hc₂z]
  rw [hx₀] at hx₀O
  have hall := hkey _ _ _ hb12 hx₀O
  set f : Bool × Bool × Bool → G := fun b =>
    c₂ * dD.ofTorus (Stroth42Core.om100 m ![(b.1.toNat : ℤ), (b.2.1.toNat : ℤ),
      (b.2.2.toNat : ℤ)]) with hf
  have hfO : ∀ b, f b ∈ O := by
    rintro ⟨b₀, b₁, b₂⟩
    by_cases hb : (b₁ || b₂) = true
    · exact hall b₀ b₁ b₂ hb
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hb
      obtain ⟨rfl, rfl⟩ := hb
      cases b₀
      · simp only [hf]
        rw [show (![((false).toNat : ℤ), ((false).toNat : ℤ), ((false).toNat : ℤ)] : Fin 3 → ℤ)
          = 0 by funext i; fin_cases i <;> rfl, Stroth42Core.om100_zero, dD.ofTorus_zero,
          mul_one]
        exact hc₂O
      · simp only [hf]
        rw [show (![((true).toNat : ℤ), ((false).toNat : ℤ), ((false).toNat : ℤ)] : Fin 3 → ℤ)
          = ![1, 0, 0] by funext i; fin_cases i <;> rfl, ← hzom, hc₂z]
        have := hO_conj _ hc₂O e heNz
        rwa [hc₂, ← conj_pow_eq, hce, inv_pow] at this
  have hfinj : Function.Injective f := by
    rintro ⟨b₀, b₁, b₂⟩ ⟨d₀, d₁, d₂⟩ hbd
    simp only [hf, mul_right_inj] at hbd
    obtain ⟨rfl, rfl, rfl⟩ := (om100_bool_eq_iff hm1 _ _ _ _ _ _).mp (dD.ofTorus_inj hbd)
    rfl
  have hO8 : 8 ≤ Nat.card O := by
    have := Nat.card_le_card_of_injective (fun b => (⟨f b, hfO b⟩ : O))
      (fun b b' hbb' => hfinj (congrArg Subtype.val hbb'))
    simpa [Nat.card_eq_fintype_card] using this
  have hO8' : Nat.card O ≤ 8 := by
    have hΩ : Nat.card (omegaIn 1 D) = 8 := by rw [h.omegaIn_one_eq]; exact F.card_omegaIn_one_A
    rw [← hΩ]
    refine Nat.card_le_card_of_injective (fun x : O => (⟨c₂⁻¹ * x, ?_⟩ : omegaIn 1 D)) ?_
    · obtain ⟨n', hn', hx⟩ := x.2
      have hxD : (x : G) ∈ D := by
        rw [← hx]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.1 hn').1 c₂).mp hc₂D
      have hxsq : (x : G) * x = z := by
        have hnz := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hn').2
        rw [← hx]
        calc n' * c₂ * n'⁻¹ * (n' * c₂ * n'⁻¹) = n' * (c₂ * c₂) * n'⁻¹ := by group
          _ = (n' * z) * n'⁻¹ := by rw [hc₂sq]
          _ = (z * n') * n'⁻¹ := by rw [hnz]
          _ = z := by group
      refine mem_omegaIn_one_of_mul_self (D.mul_mem (D.inv_mem hc₂D) hxD) ?_
      have hc := hcommD _ hxD _ (D.inv_mem hc₂D)
      calc c₂⁻¹ * x * (c₂⁻¹ * x) = c₂⁻¹ * ((x : G) * c₂⁻¹) * x := by group
        _ = c₂⁻¹ * (c₂⁻¹ * x) * x := by rw [hc]
        _ = (c₂ * c₂)⁻¹ * ((x : G) * x) := by group
        _ = 1 := by rw [hc₂sq, hxsq, inv_mul_cancel]
    · intro x x' hxx'
      have := congrArg Subtype.val hxx'
      simp only [mul_right_inj] at this
      exact Subtype.ext this
  have hOcard : Nat.card O = 8 := le_antisymm hO8' hO8
  have hOS := card_eq_card_conj_mul N c₂
  rw [show {x : G | ∃ n ∈ N, n * c₂ * n⁻¹ = x} = O from rfl, hOcard] at hOS
  have hDle : D ≤ N ⊓ Subgroup.centralizer {c₂} := fun d hd =>
    Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer hd,
      Subgroup.mem_centralizer_singleton_iff.2 (hcommD d hd z hzD)⟩,
      Subgroup.mem_centralizer_singleton_iff.2 (hcommD d hd c₂ hc₂D)⟩
  have hDcard : Nat.card D = 2 ^ (m + (m + 1) + (m + 1)) := dD.card
  have hdvd : 2 ^ (m + (m + 1) + (m + 1) + 3) ∣ Nat.card N := by
    rw [hOS, pow_add, hDcard.symm, mul_comm (Nat.card D)]
    exact Nat.mul_dvd_mul (by norm_num) (Subgroup.card_dvd_of_le hDle)
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 N
  have hPcard : 2 ^ (m + (m + 1) + (m + 1) + 3) ≤ Nat.card P := by
    rw [hP.card_eq]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
  obtain ⟨k, hkz, hkP⟩ := conj_le_S h hm hnc heN hS heuv het hue hce hae hbe he hP.isPGroup
    (hP.le.trans inf_le_right)
  have hle : P.map (MulAut.conj k⁻¹).toMonoidHom ≤
      (F.S : Subgroup G) ⊓ Subgroup.centralizer {z} := by
    rintro _ ⟨q, hq, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact Subgroup.mem_inf.2 ⟨hkP q hq, Z.mul_mem (Z.mul_mem (Z.inv_mem hkz)
      ((hP.le.trans inf_le_right) hq)) hkz⟩
  have h4 := card_CSz_le hm hS heuv het hue hce hae hbe he
  have hPle : Nat.card P ≤ 4 * Nat.card D := by
    have hcm : Nat.card (P.map (MulAut.conj k⁻¹).toMonoidHom) = Nat.card P :=
      Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective
    rw [← hcm]
    exact (Subgroup.card_le_of_le hle).trans h4
  rw [hDcard] at hPle
  have : 2 ^ (m + (m + 1) + (m + 1) + 3) ≤ 4 * 2 ^ (m + (m + 1) + (m + 1)) :=
    hPcard.trans hPle
  rw [pow_add] at this
  have hpos : 0 < 2 ^ (m + (m + 1) + (m + 1)) := by positivity
  nlinarith

theorem w₀_ne_one (dD : StrothWeakTypeData D (.t100 m)) (hm1 : 1 ≤ m) :
    (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m ≠ 1 := by
  rw [dD.t100_a_pow, dD.t100_b_pow, ← dD.ofTorus_add, Stroth43Fus.om100_add, Ne,
    dD.ofTorus_eq_one_iff, ← Stroth42Core.om100_zero, Stroth42Core.om100_eq_iff hm1]
  decide

theorem isConj_w₀_a₁ (dD : StrothWeakTypeData D (.t100 m)) (hm1 : 1 ≤ m) :
    IsConj ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) ((dD.a : G) ^ 2 ^ m) :=
  Stroth42.isConj_of_conj_eq (g := dD.ρ * dD.ρ) (by
    rw [show (dD.ρ * dD.ρ)⁻¹ * (dD.a : G) ^ 2 ^ m * (dD.ρ * dD.ρ) =
        dD.ρ⁻¹ * (dD.ρ⁻¹ * (dD.a : G) ^ 2 ^ m * dD.ρ) * dD.ρ by group,
      Stroth43Fus.t100_rho_a₁ dD hm1, Stroth43Fus.t100_rho_b₁ dD hm1])

theorem d₂_sq (dD : StrothWeakTypeData D (.t100 m)) (hm1 : 1 ≤ m) :
    (dD.a : G) ^ 2 ^ (m - 1) * (dD.b : G) ^ 2 ^ (m - 1) *
        ((dD.a : G) ^ 2 ^ (m - 1) * (dD.b : G) ^ 2 ^ (m - 1)) =
      (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m := by
  have hab : (dD.b : G) ^ 2 ^ (m - 1) * (dD.a : G) ^ 2 ^ (m - 1) =
      (dD.a : G) ^ 2 ^ (m - 1) * (dD.b : G) ^ 2 ^ (m - 1) :=
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm (dD.b ^ 2 ^ (m - 1))
      (dD.a ^ 2 ^ (m - 1)))
  have hp : ∀ x : G, x ^ 2 ^ (m - 1) * x ^ 2 ^ (m - 1) = x ^ 2 ^ m := fun x => by
    rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel hm1]
  calc (dD.a : G) ^ 2 ^ (m - 1) * (dD.b : G) ^ 2 ^ (m - 1) *
        ((dD.a : G) ^ 2 ^ (m - 1) * (dD.b : G) ^ 2 ^ (m - 1))
      = (dD.a : G) ^ 2 ^ (m - 1) * ((dD.b : G) ^ 2 ^ (m - 1) * (dD.a : G) ^ 2 ^ (m - 1)) *
          (dD.b : G) ^ 2 ^ (m - 1) := by group
    _ = (dD.a : G) ^ 2 ^ (m - 1) * ((dD.a : G) ^ 2 ^ (m - 1) * (dD.b : G) ^ 2 ^ (m - 1)) *
          (dD.b : G) ^ 2 ^ (m - 1) := by rw [hab]
    _ = ((dD.a : G) ^ 2 ^ (m - 1) * (dD.a : G) ^ 2 ^ (m - 1)) *
          ((dD.b : G) ^ 2 ^ (m - 1) * (dD.b : G) ^ 2 ^ (m - 1)) := by group
    _ = (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m := by rw [hp, hp]

theorem u_conj_ab_pow (dD : StrothWeakTypeData D (.t100 m)) (j : ℕ) :
    dD.u⁻¹ * ((dD.a : G) ^ j * (dD.b : G) ^ j) * dD.u = (dD.a : G) ^ j * (dD.b : G) ^ j := by
  rw [show dD.u⁻¹ * ((dD.a : G) ^ j * (dD.b : G) ^ j) * dD.u =
      (dD.u⁻¹ * (dD.a : G) * dD.u) ^ j * (dD.u⁻¹ * (dD.b : G) * dD.u) ^ j by
    rw [conj_pow_eq, conj_pow_eq]; group,
    Stroth43Fus.t100_u_conj_a, Stroth43Fus.t100_u_conj_b]
  exact congrArg Subtype.val (dD.isMulCommutative.is_comm.comm (dD.b ^ j) (dD.a ^ j))

theorem false_of_mul_eq (dD : StrothWeakTypeData D (.t100 m)) (hm : 2 ≤ m)
    (hza : ¬ IsConj ((dD.c : G) ^ 2 ^ (m - 1)) ((dD.a : G) ^ 2 ^ m)) {k y : G}
    (hy : y = (dD.c : G) ^ 2 ^ (m - 2) ∨ y = ((dD.c : G) ^ 2 ^ (m - 2))⁻¹)
    (hyx : y * (k⁻¹ * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) * k) =
        (dD.c : G) ^ 2 ^ (m - 2) ∨
      y * (k⁻¹ * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) * k) =
        ((dD.c : G) ^ 2 ^ (m - 2))⁻¹) : False := by
  have hm1 : 1 ≤ m := by omega
  set c₂ := (dD.c : G) ^ 2 ^ (m - 2) with hc₂
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  set w₀ := (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m with hw₀
  set x := k⁻¹ * w₀ * k with hx
  have hc₂sq : c₂ * c₂ = z := c₂_sq dD hm
  have hz2 : z * z = 1 := Stroth43Fus.t100_c₁_mul_self dD hm1
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hx1 : x = 1 ∨ x = z := by
    rcases hy with rfl | rfl <;> rcases hyx with h2 | h2
    · left
      calc x = c₂⁻¹ * (c₂ * x) := by group
        _ = 1 := by rw [h2]; group
    · right
      calc x = c₂⁻¹ * (c₂ * x) := by group
        _ = (c₂ * c₂)⁻¹ := by rw [h2]; group
        _ = z := by rw [hc₂sq, hzinv]
    · right
      calc x = c₂ * (c₂⁻¹ * x) := by group
        _ = c₂ * c₂ := by rw [h2]
        _ = z := hc₂sq
    · left
      calc x = c₂ * (c₂⁻¹ * x) := by group
        _ = 1 := by rw [h2]; group
  rcases hx1 with hx1 | hx1
  · apply w₀_ne_one dD hm1
    rw [← hw₀]
    calc w₀ = k * x * k⁻¹ := by rw [hx]; group
      _ = 1 := by rw [hx1]; group
  · exact hza ((Stroth42.isConj_of_conj_eq hx1).trans (isConj_w₀_a₁ dD hm1))

include h hm hnc heN hS heuv het hue hce hae hbe he in
theorem conj_c₂_of_mem_D {g : G} (hg : g ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)})
    (hgD : g⁻¹ * (dD.c : G) ^ 2 ^ (m - 2) * g ∈ D) :
    g⁻¹ * (dD.c : G) ^ 2 ^ (m - 2) * g = (dD.c : G) ^ 2 ^ (m - 2) ∨
      g⁻¹ * (dD.c : G) ^ 2 ^ (m - 2) * g = ((dD.c : G) ^ 2 ^ (m - 2))⁻¹ := by
  obtain ⟨n, hn, hng⟩ := exists_normalizer_conj_eq h hm hnc heN hS heuv het hue hce hae hbe he hg
    (D.pow_mem dD.c.2 _) hgD
  rw [← hng]
  exact normalizer_conj_c₂ h hm hnc heN hS heuv het hue hce hae hbe he hn

include h hm hnc heN hS heuv het hue hce hae hbe he in
theorem exists_extremal {g : G} (hg : g ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)})
    (hgS : g⁻¹ * (dD.c : G) ^ 2 ^ (m - 2) * g ∈ (F.S : Subgroup G)) :
    ∃ k ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
      (k⁻¹ * (g⁻¹ * (dD.c : G) ^ 2 ^ (m - 2) * g) * k = (dD.c : G) ^ 2 ^ (m - 2) ∨
        k⁻¹ * (g⁻¹ * (dD.c : G) ^ 2 ^ (m - 2) * g) * k = ((dD.c : G) ^ 2 ^ (m - 2))⁻¹) ∧
      ∀ s ∈ (F.S : Subgroup G), s ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} →
        s * (g⁻¹ * (dD.c : G) ^ 2 ^ (m - 2) * g) = (g⁻¹ * (dD.c : G) ^ 2 ^ (m - 2) * g) * s →
        k⁻¹ * s * k ∈ (F.S : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  set c₂ := (dD.c : G) ^ 2 ^ (m - 2) with hc₂
  set y := g⁻¹ * c₂ * g with hy
  set Z := Subgroup.centralizer ({z} : Set G) with hZ
  set H := Z ⊓ Subgroup.centralizer {y} with hH
  set Ty := (F.S : Subgroup G) ⊓ Z ⊓ Subgroup.centralizer {y} with hTy
  have hzD : z ∈ D := D.pow_mem dD.c.2 _
  have hc₂D : c₂ ∈ D := D.pow_mem dD.c.2 _
  have hcommD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hDz : D ≤ Z := fun d hd => Subgroup.mem_centralizer_singleton_iff.2 (hcommD d hd z hzD)
  have hyZ : y ∈ Z := Z.mul_mem (Z.mul_mem (Z.inv_mem hg) (hDz hc₂D)) hg
  have hTyH : Ty ≤ H := fun x hx =>
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2, (Subgroup.mem_inf.1 hx).2⟩
  have hTyp : IsPGroup 2 Ty := F.S.isPGroup'.to_le (inf_le_left.trans inf_le_left)
  obtain ⟨R, hR, hTyR⟩ := exists_isSylowOf_le hTyH hTyp
  set Q₀ := D.map (MulAut.conj g⁻¹).toMonoidHom with hQ₀
  have hQ₀H : Q₀ ≤ H := by
    rintro _ ⟨d, hd, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine Subgroup.mem_inf.2 ⟨Z.mul_mem (Z.mul_mem (Z.inv_mem hg) (hDz hd)) hg, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hcommD d hd c₂ hc₂D
    calc g⁻¹ * d * g * (g⁻¹ * c₂ * g) = g⁻¹ * (d * c₂) * g := by group
      _ = g⁻¹ * (c₂ * d) * g := by rw [this]
      _ = g⁻¹ * c₂ * g * (g⁻¹ * d * g) := by group
  have hDp : IsPGroup 2 D := F.S.isPGroup'.to_le h.le_S
  obtain ⟨c, hcH, hcQ⟩ := exists_conj_le_of_isSylowOf hR hQ₀H (hDp.map _)
  have hcz : c ∈ Z := (Subgroup.mem_inf.1 hcH).1
  obtain ⟨k, hkz, hkR⟩ := conj_le_S h hm hnc heN hS heuv het hue hce hae hbe he hR.isPGroup
    (hR.le.trans inf_le_left)
  have hgck : D.map (MulAut.conj (g * c * k)⁻¹).toMonoidHom = D := by
    refine map_conj_eq hm hS heuv het hue hce hae hbe he (fun d hd => ?_)
    have hq : g⁻¹ * d * g ∈ Q₀ := ⟨d, hd, by simp⟩
    rw [show (g * c * k)⁻¹ * d * (g * c * k) = k⁻¹ * (c⁻¹ * (g⁻¹ * d * g) * c) * k by group]
    refine Subgroup.mem_inf.2 ⟨hkR _ (hcQ _ hq), ?_⟩
    exact Z.mul_mem (Z.mul_mem (Z.inv_mem hkz) (Z.mul_mem (Z.mul_mem (Z.inv_mem hcz)
      (Z.mul_mem (Z.mul_mem (Z.inv_mem hg) (hDz hd)) hg)) hcz)) hkz
  have hyR : y ∈ R := hTyR (Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hgS, hyZ⟩,
    Subgroup.mem_centralizer_singleton_iff.2 rfl⟩)
  have hykD : k⁻¹ * y * k ∈ D := by
    rw [← h.cent]
    refine Subgroup.mem_inf.2 ⟨hkR y hyR, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hd' : d ∈ D.map (MulAut.conj (g * c * k)⁻¹).toMonoidHom := hgck.symm ▸ hd
    obtain ⟨d', hd'D, rfl⟩ := hd'
    have hq : c⁻¹ * (g⁻¹ * d' * g) * c ∈ R := hcQ _ ⟨d', hd'D, by simp⟩
    have hqy : c⁻¹ * (g⁻¹ * d' * g) * c * y = y * (c⁻¹ * (g⁻¹ * d' * g) * c) :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hR.le hq)).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc (g * c * k)⁻¹ * d' * (g * c * k) * (k⁻¹ * y * k) =
        k⁻¹ * (c⁻¹ * (g⁻¹ * d' * g) * c * y) * k := by group
      _ = k⁻¹ * (y * (c⁻¹ * (g⁻¹ * d' * g) * c)) * k := by rw [hqy]
      _ = k⁻¹ * y * k * ((g * c * k)⁻¹ * d' * (g * c * k)) := by group
  refine ⟨k, hkz, ?_, fun s hsS hsZ hsy => hkR s (hTyR (Subgroup.mem_inf.2
    ⟨Subgroup.mem_inf.2 ⟨hsS, hsZ⟩, Subgroup.mem_centralizer_singleton_iff.2 hsy⟩))⟩
  have hgk : (g * k)⁻¹ * c₂ * (g * k) = k⁻¹ * y * k := by rw [hy]; group
  have := conj_c₂_of_mem_D h hm hnc heN hS heuv het hue hce hae hbe he (Z.mul_mem hg hkz)
    (by rw [hgk]; exact hykD)
  rwa [hgk] at this

include h hm hnc heN hS heuv het hue hce hae hbe he in
theorem conj_c₂_ne_Du {g : G} (hg : g ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)})
    (v : Torus (StrothTypeIndex.t100 m).k) :
    g⁻¹ * (dD.c : G) ^ 2 ^ (m - 2) * g ≠ dD.ofTorus v * dD.u := by
  intro hy
  have hm1 : 1 ≤ m := by omega
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  set c₂ := (dD.c : G) ^ 2 ^ (m - 2) with hc₂
  set Z := Subgroup.centralizer ({z} : Set G) with hZ
  set a₁ := (dD.a : G) ^ 2 ^ m with ha₁
  set b₁ := (dD.b : G) ^ 2 ^ m with hb₁
  set w₀ := a₁ * b₁ with hw₀
  set d₂ := (dD.a : G) ^ 2 ^ (m - 1) * (dD.b : G) ^ 2 ^ (m - 1) with hd₂
  set X := dD.ofTorus v with hX
  have hcommD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hzD : z ∈ D := D.pow_mem dD.c.2 _
  have hc₂D : c₂ ∈ D := D.pow_mem dD.c.2 _
  have hDz : D ≤ Z := fun d hd => Subgroup.mem_centralizer_singleton_iff.2 (hcommD d hd z hzD)
  have hXD : X ∈ D := dD.ofTorus_mem v
  have ha₁D : a₁ ∈ D := D.pow_mem dD.a.2 _
  have hb₁D : b₁ ∈ D := D.pow_mem dD.b.2 _
  have hd₂D : d₂ ∈ D := D.mul_mem (D.pow_mem dD.a.2 _) (D.pow_mem dD.b.2 _)
  have hu_inv : dD.u⁻¹ = dD.u := inv_eq_of_mul_eq_one_right dD.u_sq
  have ha₁inv : a₁⁻¹ = a₁ := inv_eq_of_mul_eq_one_right (Stroth43Fus.t100_a₁_mul_self dD hm1)
  have hza := h.not_isConj_of_omega hnc (dD.t100_h3 hm)
  have hyS : g⁻¹ * c₂ * g ∈ (F.S : Subgroup G) := by
    rw [hy, hS]
    refine Subgroup.mem_sup_left ?_
    have := dD.nf_mem v false false true
    rwa [dD.d8_fft] at this
  have hud₂ : dD.u * d₂ = d₂ * dD.u := by
    have h1 := u_conj_ab_pow dD (2 ^ (m - 1))
    calc dD.u * d₂ = dD.u * (dD.u⁻¹ * d₂ * dD.u) := by rw [h1]
      _ = d₂ * dD.u := by group
  have huw₀ : dD.u * w₀ = w₀ * dD.u := by
    have h1 := u_conj_ab_pow dD (2 ^ m)
    calc dD.u * w₀ = dD.u * (dD.u⁻¹ * w₀ * dD.u) := by rw [h1]
      _ = w₀ * dD.u := by group
  have hd₂y : d₂ * (g⁻¹ * c₂ * g) = (g⁻¹ * c₂ * g) * d₂ := by
    rw [hy]
    calc d₂ * (X * dD.u) = (d₂ * X) * dD.u := by group
      _ = (X * d₂) * dD.u := by rw [hcommD _ hd₂D _ hXD]
      _ = X * (d₂ * dD.u) := by group
      _ = X * (dD.u * d₂) := by rw [hud₂]
      _ = X * dD.u * d₂ := by group
  have hua : dD.u * a₁ = b₁ * dD.u := by
    have h1 := Stroth43Fus.t100_u_a₁ dD
    calc dD.u * a₁ = (dD.u⁻¹ * a₁ * dD.u) * dD.u := by
          rw [mul_assoc (dD.u⁻¹ * a₁) dD.u dD.u, dD.u_sq, mul_one, hu_inv]
      _ = b₁ * dD.u := by rw [h1]
  have hya : a₁⁻¹ * (g⁻¹ * c₂ * g) * a₁ = (g⁻¹ * c₂ * g) * w₀ := by
    rw [hy]
    calc a₁⁻¹ * (X * dD.u) * a₁ = a₁⁻¹ * X * (dD.u * a₁) := by group
      _ = a₁⁻¹ * X * (b₁ * dD.u) := by rw [hua]
      _ = (X * a₁⁻¹) * b₁ * dD.u := by rw [hcommD _ (D.inv_mem ha₁D) _ hXD]; group
      _ = X * w₀ * dD.u := by rw [ha₁inv, hw₀]; group
      _ = X * dD.u * w₀ := by rw [mul_assoc X w₀, ← huw₀]; group
  obtain ⟨k, hkz, hk1, hkC⟩ :=
    exists_extremal h hm hnc heN hS heuv het hue hce hae hbe he hg hyS
  have hd₂k := hkC d₂ (h.le_S hd₂D) (hDz hd₂D) hd₂y
  have hd₂kZ : k⁻¹ * d₂ * k ∈ Z := Z.mul_mem (Z.mul_mem (Z.inv_mem hkz) (hDz hd₂D)) hkz
  have hcomm_k : k⁻¹ * d₂ * k * (k⁻¹ * (g⁻¹ * c₂ * g) * k) =
      k⁻¹ * (g⁻¹ * c₂ * g) * k * (k⁻¹ * d₂ * k) := by
    calc k⁻¹ * d₂ * k * (k⁻¹ * (g⁻¹ * c₂ * g) * k) = k⁻¹ * (d₂ * (g⁻¹ * c₂ * g)) * k := by group
      _ = k⁻¹ * ((g⁻¹ * c₂ * g) * d₂) * k := by rw [hd₂y]
      _ = k⁻¹ * (g⁻¹ * c₂ * g) * k * (k⁻¹ * d₂ * k) := by group
  have hd₂kc : k⁻¹ * d₂ * k * c₂ = c₂ * (k⁻¹ * d₂ * k) := by
    rcases hk1 with h2 | h2 <;> rw [h2] at hcomm_k
    · exact hcomm_k
    · calc k⁻¹ * d₂ * k * c₂ = c₂ * (c₂⁻¹ * (k⁻¹ * d₂ * k)) * c₂ := by group
        _ = c₂ * (k⁻¹ * d₂ * k * c₂⁻¹) * c₂ := by rw [hcomm_k]
        _ = c₂ * (k⁻¹ * d₂ * k) := by group
  obtain ⟨v', l', hv'⟩ := nf_of_comm_c₂ hm hS heuv het hue hce hae hbe he hd₂k hd₂kZ hd₂kc
  have hsq : d₂ * d₂ = w₀ := d₂_sq dD hm1
  have hw₀k : k⁻¹ * w₀ * k ∈ D := by
    rw [show k⁻¹ * w₀ * k = (k⁻¹ * d₂ * k) * (k⁻¹ * d₂ * k) by rw [← hsq]; group, hv']
    exact nf_mul_self_mem dD v' l'
  have hga : (g * a₁ * k)⁻¹ * c₂ * (g * a₁ * k) =
      (k⁻¹ * (g⁻¹ * c₂ * g) * k) * (k⁻¹ * w₀ * k) := by
    rw [show (g * a₁ * k)⁻¹ * c₂ * (g * a₁ * k) = k⁻¹ * (a₁⁻¹ * (g⁻¹ * c₂ * g) * a₁) * k by
      group, hya]
    group
  have hgaZ : g * a₁ * k ∈ Z := Z.mul_mem (Z.mul_mem hg (hDz ha₁D)) hkz
  have hmemD : (g * a₁ * k)⁻¹ * c₂ * (g * a₁ * k) ∈ D := by
    rw [hga]
    rcases hk1 with h2 | h2 <;> rw [h2]
    · exact D.mul_mem hc₂D hw₀k
    · exact D.mul_mem (D.inv_mem hc₂D) hw₀k
  have hfin := conj_c₂_of_mem_D h hm hnc heN hS heuv het hue hce hae hbe he hgaZ hmemD
  rw [hga] at hfin
  exact false_of_mul_eq dD hm hza hk1 hfin

include hm heuv het hue hce hae hbe he in
theorem e_conj_d₂ :
    e * ((dD.a : G) ^ 2 ^ (m - 1) * (dD.b : G) ^ 2 ^ (m - 1)) * e⁻¹ =
      ((dD.a : G) ^ 2 ^ (m - 1) * (dD.b : G) ^ 2 ^ (m - 1))⁻¹ := by
  obtain ⟨m'', rfl⟩ : ∃ m'', m = m'' + 2 := ⟨m - 2, by omega⟩
  rw [show m'' + 2 - 1 = m'' + 1 by omega, Stroth43Fus.t100_d₂_eq (m'' + 1) dD,
    (dD.ivAction heuv het hue hce hae hbe he).conj_inv_ofTorus,
    dD.ivAction_φe heuv het hue hce hae hbe he, torusDiag_ofInt, ← dD.ofTorus_neg,
    ← Torus.ofInt_neg]
  congr 1
  rw [Stroth42Core.t100_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Pi.neg_apply]
  refine ⟨⟨0, by ring⟩, ⟨-(2 ^ m''), by ring⟩, ⟨-(2 ^ m''), by ring⟩⟩

include hm heuv het hue hce hae hbe he in
theorem e_comm_w₀ :
    e * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) =
      ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) * e := by
  have hm1 : 1 ≤ m := by omega
  have h1 : e⁻¹ * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) * e =
      (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m := by
    rw [dD.t100_a_pow, dD.t100_b_pow, ← dD.ofTorus_add, Stroth43Fus.om100_add,
      (dD.ivAction heuv het hue hce hae hbe he).conj_ofTorus,
      dD.ivAction_φe heuv het hue hce hae hbe he,
      StrothWeakTypeData.torusDiag_om100_of_odd hm1 (by norm_num)
        (StrothWeakTypeData.neg_one_add_two_pow_emod_two hm1)
        (StrothWeakTypeData.neg_one_add_two_pow_emod_two hm1)]
  calc e * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) =
      e * (e⁻¹ * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) * e) := by rw [h1]
    _ = ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) * e := by group

include h hm hnc heN hS heuv het hue hce hae hbe he in
theorem conj_c₂_ne_e {g : G} (hg : g ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)})
    (v : Torus (StrothTypeIndex.t100 m).k) (l : Bool) :
    g⁻¹ * (dD.c : G) ^ 2 ^ (m - 2) * g ≠ dD.ofTorus v * dD.d8 false false l * e := by
  intro hy
  have hm1 : 1 ≤ m := by omega
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  set c₂ := (dD.c : G) ^ 2 ^ (m - 2) with hc₂
  set Z := Subgroup.centralizer ({z} : Set G) with hZ
  set w₀ := (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m with hw₀
  set d₂ := (dD.a : G) ^ 2 ^ (m - 1) * (dD.b : G) ^ 2 ^ (m - 1) with hd₂
  set X := dD.ofTorus v with hX
  set W := dD.d8 false false l with hW
  have hcommD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hzD : z ∈ D := D.pow_mem dD.c.2 _
  have hc₂D : c₂ ∈ D := D.pow_mem dD.c.2 _
  have hDz : D ≤ Z := fun d hd => Subgroup.mem_centralizer_singleton_iff.2 (hcommD d hd z hzD)
  have hXD : X ∈ D := dD.ofTorus_mem v
  have hw₀D : w₀ ∈ D := D.mul_mem (D.pow_mem dD.a.2 _) (D.pow_mem dD.b.2 _)
  have hd₂D : d₂ ∈ D := D.mul_mem (D.pow_mem dD.a.2 _) (D.pow_mem dD.b.2 _)
  have hza := h.not_isConj_of_omega hnc (dD.t100_h3 hm)
  have hyS : g⁻¹ * c₂ * g ∈ (F.S : Subgroup G) := by
    rw [hy, hS]
    have := (dD.ivAction heuv het hue hce hae hbe he).nfe_mem v false false l true
    simpa [Stroth42Core.bpow] using this
  have hcomm_u : ∀ x : G, dD.u⁻¹ * x * dD.u = x → dD.u * x = x * dD.u := fun x hx => by
    calc dD.u * x = dD.u * (dD.u⁻¹ * x * dD.u) := by rw [hx]
      _ = x * dD.u := by group
  have hWd₂ : W * d₂ = d₂ * W := by
    cases l
    · simp [hW, StrothWeakTypeData.d8]
    · rw [hW, dD.d8_fft]; exact hcomm_u _ (u_conj_ab_pow dD _)
  have hWw₀ : W * w₀ = w₀ * W := by
    cases l
    · simp [hW, StrothWeakTypeData.d8]
    · rw [hW, dD.d8_fft]; exact hcomm_u _ (u_conj_ab_pow dD _)
  have hew₀ := e_comm_w₀ hm heuv het hue hce hae hbe he
  have hw₀y : w₀ * (g⁻¹ * c₂ * g) = (g⁻¹ * c₂ * g) * w₀ := by
    rw [hy]
    calc w₀ * (X * W * e) = (w₀ * X) * W * e := by group
      _ = (X * w₀) * W * e := by rw [hcommD _ hw₀D _ hXD]
      _ = X * (w₀ * W) * e := by group
      _ = X * (W * w₀) * e := by rw [hWw₀]
      _ = X * W * (w₀ * e) := by group
      _ = X * W * (e * w₀) := by rw [hew₀]
      _ = X * W * e * w₀ := by group
  have hyd : d₂⁻¹ * (g⁻¹ * c₂ * g) * d₂ = (g⁻¹ * c₂ * g) * w₀ := by
    rw [hy]
    have he_d₂ : e * d₂ = d₂⁻¹ * e := by
      have h1 := e_conj_d₂ hm heuv het hue hce hae hbe he
      calc e * d₂ = (e * d₂ * e⁻¹) * e := by group
        _ = d₂⁻¹ * e := by rw [h1]
    have hsq : d₂ * d₂ = w₀ := d₂_sq dD hm1
    have hw₀2 : w₀ * w₀ = 1 := by
      rw [← hsq]
      calc d₂ * d₂ * (d₂ * d₂) = (dD.a : G) ^ 2 ^ (m - 1) * (dD.b : G) ^ 2 ^ (m - 1) *
          ((dD.a : G) ^ 2 ^ (m - 1) * (dD.b : G) ^ 2 ^ (m - 1)) *
          ((dD.a : G) ^ 2 ^ (m - 1) * (dD.b : G) ^ 2 ^ (m - 1) *
            ((dD.a : G) ^ 2 ^ (m - 1) * (dD.b : G) ^ 2 ^ (m - 1))) := rfl
        _ = w₀ * w₀ := by rw [d₂_sq dD hm1]
        _ = (dD.a : G) ^ 2 ^ m * (dD.a : G) ^ 2 ^ m *
            ((dD.b : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) := by
          rw [hw₀]
          have hab := hcommD _ (D.pow_mem dD.b.2 (2 ^ m)) _ (D.pow_mem dD.a.2 (2 ^ m))
          calc (dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m)
              = (dD.a : G) ^ 2 ^ m * ((dD.b : G) ^ 2 ^ m * (dD.a : G) ^ 2 ^ m) *
                (dD.b : G) ^ 2 ^ m := by group
            _ = (dD.a : G) ^ 2 ^ m * ((dD.a : G) ^ 2 ^ m * (dD.b : G) ^ 2 ^ m) *
                (dD.b : G) ^ 2 ^ m := by rw [hab]
            _ = _ := by group
        _ = 1 := by
          rw [Stroth43Fus.t100_a₁_mul_self dD hm1, Stroth43Fus.t100_b₁_mul_self dD hm1, one_mul]
    have hw₀inv : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_right hw₀2
    have hWd₂' : d₂⁻¹ * W = W * d₂⁻¹ := by
      calc d₂⁻¹ * W = d₂⁻¹ * (W * d₂) * d₂⁻¹ := by group
        _ = d₂⁻¹ * (d₂ * W) * d₂⁻¹ := by rw [hWd₂]
        _ = W * d₂⁻¹ := by group
    calc d₂⁻¹ * (X * W * e) * d₂ = (d₂⁻¹ * X) * W * (e * d₂) := by group
      _ = (X * d₂⁻¹) * W * (d₂⁻¹ * e) := by rw [hcommD _ (D.inv_mem hd₂D) _ hXD, he_d₂]
      _ = X * (d₂⁻¹ * W) * d₂⁻¹ * e := by group
      _ = X * (W * d₂⁻¹) * d₂⁻¹ * e := by rw [hWd₂']
      _ = X * W * (d₂ * d₂)⁻¹ * e := by group
      _ = X * W * w₀ * e := by rw [hsq, hw₀inv]
      _ = X * W * (e * w₀) := by rw [mul_assoc (X * W) w₀ e, hew₀]
      _ = X * W * e * w₀ := by group
  obtain ⟨k, hkz, hk1, hkC⟩ :=
    exists_extremal h hm hnc heN hS heuv het hue hce hae hbe he hg hyS
  have hw₀k := hkC w₀ (h.le_S hw₀D) (hDz hw₀D) hw₀y
  have hw₀kZ : k⁻¹ * w₀ * k ∈ Z := Z.mul_mem (Z.mul_mem (Z.inv_mem hkz) (hDz hw₀D)) hkz
  have hcomm_k : k⁻¹ * w₀ * k * (k⁻¹ * (g⁻¹ * c₂ * g) * k) =
      k⁻¹ * (g⁻¹ * c₂ * g) * k * (k⁻¹ * w₀ * k) := by
    calc k⁻¹ * w₀ * k * (k⁻¹ * (g⁻¹ * c₂ * g) * k) = k⁻¹ * (w₀ * (g⁻¹ * c₂ * g)) * k := by group
      _ = k⁻¹ * ((g⁻¹ * c₂ * g) * w₀) * k := by rw [hw₀y]
      _ = k⁻¹ * (g⁻¹ * c₂ * g) * k * (k⁻¹ * w₀ * k) := by group
  have hw₀kc : k⁻¹ * w₀ * k * c₂ = c₂ * (k⁻¹ * w₀ * k) := by
    rcases hk1 with h2 | h2 <;> rw [h2] at hcomm_k
    · exact hcomm_k
    · calc k⁻¹ * w₀ * k * c₂ = c₂ * (c₂⁻¹ * (k⁻¹ * w₀ * k)) * c₂ := by group
        _ = c₂ * (k⁻¹ * w₀ * k * c₂⁻¹) * c₂ := by rw [hcomm_k]
        _ = c₂ * (k⁻¹ * w₀ * k) := by group
  obtain ⟨v', l', hv'⟩ := nf_of_comm_c₂ hm hS heuv het hue hce hae hbe he hw₀k hw₀kZ hw₀kc
  have hgd : (g * d₂ * k)⁻¹ * c₂ * (g * d₂ * k) =
      (k⁻¹ * (g⁻¹ * c₂ * g) * k) * (k⁻¹ * w₀ * k) := by
    rw [show (g * d₂ * k)⁻¹ * c₂ * (g * d₂ * k) = k⁻¹ * (d₂⁻¹ * (g⁻¹ * c₂ * g) * d₂) * k by
      group, hyd]
    group
  have hgdZ : g * d₂ * k ∈ Z := Z.mul_mem (Z.mul_mem hg (hDz hd₂D)) hkz
  have hcD : k⁻¹ * (g⁻¹ * c₂ * g) * k ∈ D := by
    rcases hk1 with h2 | h2 <;> rw [h2]
    · exact hc₂D
    · exact D.inv_mem hc₂D
  cases l'
  · have hw₀kD : k⁻¹ * w₀ * k ∈ D := by
      rw [hv', dD.d8_fff, mul_one]; exact dD.ofTorus_mem v'
    have hfin := conj_c₂_of_mem_D h hm hnc heN hS heuv het hue hce hae hbe he hgdZ
      (by rw [hgd]; exact D.mul_mem hcD hw₀kD)
    rw [hgd] at hfin
    exact false_of_mul_eq dD hm hza hk1 hfin
  · obtain ⟨v'', hv''⟩ := dD.exists_ofTorus (D.mul_mem hcD (dD.ofTorus_mem v'))
    apply conj_c₂_ne_Du h hm hnc heN hS heuv het hue hce hae hbe he hgdZ v''
    rw [hgd, hv', dD.d8_fft, ← mul_assoc, ← hv'']

include h hm hnc heN hS heuv het hue hce hae hbe he in
theorem strongly_closed :
    ∀ g ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
      ∀ y ∈ Subgroup.zpowers ((dD.c : G) ^ 2 ^ (m - 2)), g⁻¹ * y * g ∈ (F.S : Subgroup G) →
        g⁻¹ * y * g ∈ Subgroup.zpowers ((dD.c : G) ^ 2 ^ (m - 2)) := by
  intro g hg y hy hyS
  have hm1 : 1 ≤ m := by omega
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  set c₂ := (dD.c : G) ^ 2 ^ (m - 2) with hc₂
  set Z := Subgroup.centralizer ({z} : Set G) with hZ
  have hzD : z ∈ D := D.pow_mem dD.c.2 _
  have hc₂D : c₂ ∈ D := D.pow_mem dD.c.2 _
  have hcommD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hDz : D ≤ Z := fun d hd => Subgroup.mem_centralizer_singleton_iff.2 (hcommD d hd z hzD)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  set x := g⁻¹ * c₂ * g with hx
  have hxj : g⁻¹ * c₂ ^ j * g = x ^ j := by
    calc g⁻¹ * c₂ ^ j * g = MulAut.conj g⁻¹ (c₂ ^ j) := by simp [MulAut.conj_apply]
      _ = (MulAut.conj g⁻¹ c₂) ^ j := map_zpow _ _ _
      _ = x ^ j := by simp [MulAut.conj_apply, hx]
  rw [hxj] at hyS ⊢
  have hxZ : x ∈ Z := Z.mul_mem (Z.mul_mem (Z.inv_mem hg) (hDz hc₂D)) hg
  have hc₂sq : c₂ * c₂ = z := c₂_sq dD hm
  have hxx : x * x = z := by
    have hgz := Subgroup.mem_centralizer_singleton_iff.1 hg
    calc x * x = g⁻¹ * (c₂ * c₂) * g := by rw [hx]; group
      _ = g⁻¹ * (z * g) := by rw [hc₂sq, mul_assoc]
      _ = g⁻¹ * (g * z) := by rw [hgz]
      _ = z := by group
  have hzc : z = c₂ ^ (2 : ℤ) := by rw [zpow_two]; exact hc₂sq.symm
  have hsplit : x ^ j = c₂ ^ (2 * (j / 2)) * x ^ (j % 2) := by
    have hj : j = 2 * (j / 2) + j % 2 := by omega
    have hx2 : x ^ (2 : ℤ) = z := by rw [zpow_two]; exact hxx
    conv_lhs => rw [hj]
    rw [zpow_add, zpow_mul, hx2, hzc, ← zpow_mul]
  have hc₂pow : c₂ ^ (2 * (j / 2)) ∈ Subgroup.zpowers c₂ := Subgroup.zpow_mem_zpowers c₂ _
  have hmain : x ∈ (F.S : Subgroup G) → x ∈ Subgroup.zpowers c₂ := by
    intro hxS
    obtain ⟨v, l, k, hv⟩ := nf_of_mem hm hS heuv het hue hce hae hbe he hxS hxZ
    cases k
    · cases l
      · have hxD : x ∈ D := by
          rw [hv]; simpa [Stroth42Core.bpow, StrothWeakTypeData.d8] using dD.ofTorus_mem v
        rcases conj_c₂_of_mem_D h hm hnc heN hS heuv het hue hce hae hbe he hg hxD with h2 | h2
        · rw [show x = c₂ from h2]; exact Subgroup.mem_zpowers c₂
        · rw [show x = c₂⁻¹ from h2]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers c₂)
      · exact absurd (by simpa [Stroth42Core.bpow, StrothWeakTypeData.d8_fft] using hv)
          (conj_c₂_ne_Du h hm hnc heN hS heuv het hue hce hae hbe he hg v)
    · exact absurd (by simpa [Stroth42Core.bpow] using hv)
        (conj_c₂_ne_e h hm hnc heN hS heuv het hue hce hae hbe he hg v l)
  rcases Int.emod_two_eq_zero_or_one j with hr | hr
  · rw [hsplit, hr, zpow_zero, mul_one]
    exact hc₂pow
  · rw [hsplit, hr, zpow_one] at hyS ⊢
    have hxS : x ∈ (F.S : Subgroup G) := by
      have hc₂S : c₂ ^ (2 * (j / 2)) ∈ (F.S : Subgroup G) := (F.S : Subgroup G).zpow_mem
        (h.le_S hc₂D) _
      have := (F.S : Subgroup G).mul_mem ((F.S : Subgroup G).inv_mem hc₂S) hyS
      rwa [inv_mul_cancel_left] at this
    exact Subgroup.mul_mem _ hc₂pow (hmain hxS)

end Config

end Stroth43Sc

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

theorem stroth_4_3_scIV :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
      (dD : StrothWeakTypeData D (.t100 m)) {e : G},
      F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (∀ (D' : Subgroup G) (τ' : StrothTypeIndex) (dD' : StrothWeakTypeData D' τ'),
        F.IsD D' dD' → IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)) → Nat.card D' ≤ Nat.card D) →
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
      (∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
        orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y) →
      2 ^ 11 ∣ Nat.card G →
      2 ≤ m → e ∈ Subgroup.normalizer (D : Set G) →
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
      e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv →
      e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t → e⁻¹ * dD.u * e = dD.u →
      e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ →
      e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ m →
      e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ m →
      e * e = (dD.c : G) ^ 2 ^ (m - 1) →
      ∀ g ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
        ∀ y ∈ Subgroup.zpowers ((dD.c : G) ^ 2 ^ (m - 2)), g⁻¹ * y * g ∈ (F.S : Subgroup G) →
          g⁻¹ * y * g ∈ Subgroup.zpowers ((dD.c : G) ^ 2 ^ (m - 2)) := by
  intro G _ _ F D m dD e h _ _ _ hnc _ hm heN hS heuv het hue hce hae hbe he
  exact Stroth43Sc.strongly_closed h hm hnc heN hS heuv het hue hce hae hbe he

end CFSG.CGT.Stroth77
