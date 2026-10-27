module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourU3Nat
public import CFSG.CGT.PushingUpLit.CGT6.SixFourU3Gen
public import CFSG.CGT.PushingUpLit.CGT6.SixFourMod

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement Pointwise MatrixGroups

theorem exists_hom_extend {V A : Type*} [Group V] [CommGroup A] (hc : ∀ a b : V, a * b = b * a)
    (C U : Subgroup V) (ψ : ↥U →* A) (hψ : Function.Surjective ψ)
    (hker : ∀ u : ↥U, ψ u = 1 ↔ (u : V) ∈ C) (hUC : ∀ v : V, ∃ u : ↥U, ∃ c ∈ C, v = (u : V) * c) :
    ∃ Ψ : V →* A, Function.Surjective Ψ ∧ Ψ.ker = C ∧ ∀ u : ↥U, Ψ (u : V) = ψ u := by
  classical
  choose u₀ c₀ hc₀ hv₀ using hUC
  have key : ∀ (v : V) (u : ↥U) (c : V), c ∈ C → v = (u : V) * c → ψ (u₀ v) = ψ u := by
    intro v u c hcC hvuc
    have hmem : (((u₀ v)⁻¹ * u : ↥U) : V) ∈ C := by
      have e1 : (u : V) = (u₀ v : V) * (c₀ v * c⁻¹) := by
        calc (u : V) = v * c⁻¹ := by rw [hvuc]; group
          _ = ((u₀ v : V) * c₀ v) * c⁻¹ := by rw [← hv₀ v]
          _ = (u₀ v : V) * (c₀ v * c⁻¹) := by group
      have : (((u₀ v)⁻¹ * u : ↥U) : V) = c₀ v * c⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [e1]
        group
      rw [this]
      exact C.mul_mem (hc₀ v) (C.inv_mem hcC)
    have h1 := (hker _).mpr hmem
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  let Ψ : V →* A := MonoidHom.mk' (fun v => ψ (u₀ v)) (fun v w => by
    have e1 : v * w = ((u₀ v * u₀ w : ↥U) : V) * (c₀ v * c₀ w) := by
      calc v * w = ((u₀ v : V) * c₀ v) * ((u₀ w : V) * c₀ w) := by rw [← hv₀ v, ← hv₀ w]
        _ = (u₀ v : V) * ((c₀ v * (u₀ w : V)) * c₀ w) := by group
        _ = (u₀ v : V) * (((u₀ w : V) * c₀ v) * c₀ w) := by rw [hc (c₀ v) (u₀ w)]
        _ = ((u₀ v * u₀ w : ↥U) : V) * (c₀ v * c₀ w) := by simp only [Subgroup.coe_mul]; group
    have := key (v * w) (u₀ v * u₀ w) (c₀ v * c₀ w) (C.mul_mem (hc₀ v) (hc₀ w)) e1
    simpa only [map_mul] using this)
  have hΨ : ∀ u : ↥U, Ψ (u : V) = ψ u := fun u =>
    key (u : V) u 1 C.one_mem (by simp)
  refine ⟨Ψ, fun a => ?_, ?_, hΨ⟩
  · obtain ⟨u, rfl⟩ := hψ a
    exact ⟨u, hΨ u⟩
  · ext v
    rw [MonoidHom.mem_ker]
    constructor
    · intro hv
      have h1 : (u₀ v : V) ∈ C := (hker _).mp hv
      rw [hv₀ v]
      exact C.mul_mem h1 (hc₀ v)
    · intro hv
      have := key v 1 v hv (by simp)
      rw [map_one] at this
      exact this

section Facts

variable {G : Type} [Group G] [Finite G] {Y R : Subgroup G} {T : Sylow 2 G}

theorem eight_jBar_card_le [R.Normal] (h : EightCtx Y T R) {n : ℕ} (hn : 1 ≤ n)
    (hnat : IsNaturalSLTwoModule ↥Y n) {K : Subgroup (G ⧸ R)} (hJbK : jBar R T ≤ K)
    (ρ : ↥Y →* ↥K) (hρval : ∀ z : ↥Y, ((ρ z : ↥K) : G ⧸ R) = QuotientGroup.mk' R z) :
    Nat.card ((jBar R T).subgroupOf K) = 2 ^ n ∧ (jBar R T).subgroupOf K ≤ ρ.range := by
  classical
  have hn0 : n ≠ 0 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA, hnot, hJA, hJY, hrel, -⟩ := eight_sl_nine h hn hnat
  have hAJ : A ≤ jIn (T : Subgroup G) := by
    rw [jIn_eq_thompsonJ]
    exact le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian (T : Subgroup G) A) => A) A hA
  have hcardJb : Nat.card (jBar R T) = 2 ^ n := by
    rw [jBar, (card_map_jIn_eq hAJ hJA).2, hrel, GaloisField.card 2 n hn0]
  refine ⟨?_, ?_⟩
  · rw [← hcardJb]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJbK).toEquiv
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨j, hj, hjx⟩ := hx
    obtain ⟨y, hy, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hJY hj)
    have hr1 : QuotientGroup.mk' R r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    rw [hρval]
    show QuotientGroup.mk' R y = _
    rw [← hjx, map_mul, hr1, mul_one]

end Facts

section Natural

variable {G : Type} [Group G] [Finite G] {Y R : Subgroup G} {T : Sylow 2 G}

theorem natQ_of_eight [R.Normal] (h : EightCtx Y T R) {n : ℕ} (hn : 2 ≤ n)
    (hnat : IsNaturalSLTwoModule ↥Y n) {K : Subgroup (G ⧸ R)} (hJbK : jBar R T ≤ K)
    (ρ : ↥Y →* ↥K) (hρval : ∀ z : ↥Y, ((ρ z : ↥K) : G ⧸ R) = QuotientGroup.mk' R z)
    (hρker : ∀ y : ↥Y, ρ y = 1 ↔ y ∈ pCore 2 ↥Y) :
    NatQ (h.vAct.comp K.subtype) ρ.range (2 ^ n - 1) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnat0 := hnat
  obtain ⟨φ, ψ, hψs, hψk, hψe⟩ := hnat
  let θK : ↥K →* MulAut ↥(omegaOneCenterIn R) := h.vAct.comp K.subtype
  have hθρ : ∀ y : ↥Y, θK (ρ y) = h.vAct (QuotientGroup.mk (y : G)) := fun y => by
    show h.vAct ((ρ y : ↥K) : G ⧸ R) = _
    rw [hρval]
    rfl
  have hVc := omegaOneCenterIn_comm R
  have hkerρ : ρ.ker = pCore 2 ↥Y := by
    ext y
    rw [MonoidHom.mem_ker]
    exact hρker y
  let eQ : (↥Y ⧸ pCore 2 ↥Y) ≃* ↥ρ.range :=
    (QuotientGroup.quotientMulEquivOfEq hkerρ.symm).trans (QuotientGroup.quotientKerEquivRange ρ)
  let φ₀ : ↥ρ.range ≃* SL(2, GaloisField 2 n) := eQ.symm.trans φ
  have hφ₀ : ∀ y : ↥Y, φ₀ (ρ.rangeRestrict y) = φ (QuotientGroup.mk y) := by
    intro y
    have h1 : eQ (QuotientGroup.mk y) = ρ.rangeRestrict y := rfl
    show φ (eQ.symm (ρ.rangeRestrict y)) = _
    rw [← h1, MulEquiv.symm_apply_apply]
  have hUV : blockU Y ≤ omegaOneCenterIn R := h.blockU_le_V
  let UV : Subgroup ↥(omegaOneCenterIn R) := (blockU Y).subgroupOf (omegaOneCenterIn R)
  let e₁ : ↥UV ≃* ↥(shortU ↥Y) := (Subgroup.subgroupOfEquivOfLe hUV).trans (blockUEquiv Y).symm
  let ψ' : ↥UV →* Multiplicative (Fin 2 → GaloisField 2 n) := ψ.comp e₁.toMonoidHom
  have hψ's : Function.Surjective ψ' := hψs.comp e₁.surjective
  have he₁ : ∀ u : ↥UV, (((e₁ u : ↥(shortU ↥Y)) : ↥Y) : G) = ((u : ↥(omegaOneCenterIn R)) : G) := by
    intro u
    have h1 : blockUEquiv Y (e₁ u) = Subgroup.subgroupOfEquivOfLe hUV u :=
      (blockUEquiv Y).apply_symm_apply _
    have h2 := blockUEquiv_coe Y (e₁ u)
    rw [h1] at h2
    exact h2.symm
  have hmemUV : ∀ (y : ↥Y) (u : ↥UV), θK (ρ y) (u : ↥(omegaOneCenterIn R)) ∈ UV := by
    intro y u
    rw [hθρ, Subgroup.mem_subgroupOf, h.vAct_mk]
    exact conj_mem_blockU (Subgroup.le_normalizer y.2) u.2
  let act : ↥Y → ↥UV → ↥UV := fun y u => ⟨θK (ρ y) (u : ↥(omegaOneCenterIn R)), hmemUV y u⟩
  have hactG : ∀ (y : ↥Y) (u : ↥UV), (((act y u : ↥UV) : ↥(omegaOneCenterIn R)) : G) =
      (y : G) * ((u : ↥(omegaOneCenterIn R)) : G) * (y : G)⁻¹ := by
    intro y u
    show ((θK (ρ y) (u : ↥(omegaOneCenterIn R)) : ↥(omegaOneCenterIn R)) : G) = _
    rw [hθρ, h.vAct_mk]
  have hshortN : (shortU ↥Y).Normal := by
    unfold shortU
    infer_instance
  have hψ'e : ∀ (y : ↥Y) (u : ↥UV), ψ' (act y u) = Multiplicative.ofAdd
      (((φ (QuotientGroup.mk y) : SL(2, GaloisField 2 n)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd (ψ' u))) := by
    intro y u
    have hu' : y * ((e₁ u : ↥(shortU ↥Y)) : ↥Y) * y⁻¹ ∈ shortU ↥Y :=
      Subgroup.Normal.conj_mem hshortN _ (e₁ u).2 y
    have h1 := hψe y ((e₁ u : ↥(shortU ↥Y)) : ↥Y) (e₁ u).2 hu'
    have h2 : e₁ (act y u) = ⟨y * ((e₁ u : ↥(shortU ↥Y)) : ↥Y) * y⁻¹, hu'⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      show (((e₁ (act y u) : ↥(shortU ↥Y)) : ↥Y) : G) =
        (y : G) * ((((e₁ u : ↥(shortU ↥Y)) : ↥Y)) : G) * (y : G)⁻¹
      rw [he₁ (act y u), he₁ u, hactG]
    show ψ (e₁ (act y u)) = _
    rw [h2]
    exact h1
  let C : Subgroup ↥(omegaOneCenterIn R) := fixQ θK ρ.range
  have hCn : C.Normal := ⟨fun n hn g => by rw [hVc g n, mul_inv_cancel_right]; exact hn⟩
  have hCU : ∀ u : ↥UV, (u : ↥(omegaOneCenterIn R)) ∈ C → ψ' u = 1 := by
    intro u hu
    have hfix : ∀ y : ↥Y, act y u = u := by
      intro y
      apply Subtype.ext
      exact mem_fixQ.mp hu (ρ y) ⟨y, rfl⟩
    have hw : ∀ g : SL(2, GaloisField 2 n),
        (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd (ψ' u)) =
          Multiplicative.toAdd (ψ' u) := by
      intro g
      obtain ⟨y, hy⟩ := (φ.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 ↥Y))) g
      have h1 := hψ'e y u
      rw [hfix y] at h1
      have h2 := congrArg Multiplicative.toAdd h1
      rw [toAdd_ofAdd] at h2
      have hy' : φ (QuotientGroup.mk y) = g := hy
      rw [hy'] at h2
      exact h2.symm
    have h1 := hw (slUpper 1)
    have h2 := hw (slLower 1)
    rw [slUpper_mulVec] at h1
    rw [slLower_mulVec] at h2
    have hw1 : Multiplicative.toAdd (ψ' u) 1 = 0 := by
      have := congrFun h1 0
      simpa using this
    have hw0 : Multiplicative.toAdd (ψ' u) 0 = 0 := by
      have := congrFun h2 1
      simpa using this
    have : Multiplicative.toAdd (ψ' u) = 0 := by
      funext i
      fin_cases i
      · exact hw0
      · exact hw1
    rw [← ofAdd_toAdd (ψ' u), this]
    rfl
  obtain ⟨hJbcard, hJbYb⟩ := eight_jBar_card_le h hn1 hnat0 hJbK ρ hρval
  obtain ⟨g, hg, hgen⟩ := l2_gen_facts hn hJbYb hJbcard φ₀
  have hJbmap : ((jBar R T).subgroupOf K).map K.subtype = jBar R T := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hJbK]
  have hfixJ : fixQ θK ((jBar R T).subgroupOf K) = h.cV (jBar R T) := by
    show autFixGrp (((jBar R T).subgroupOf K).map θK) = autFixGrp ((jBar R T).map h.vAct)
    congr 1
    show ((jBar R T).subgroupOf K).map (h.vAct.comp K.subtype) = _
    rw [← Subgroup.map_map, hJbmap]
  have hCindex : C.index ≤ (2 ^ n) ^ 2 := by
    have hC : C = fixQ θK ((jBar R T).subgroupOf K) ⊓
        fixQ θK (((jBar R T).subgroupOf K).map (MulAut.conj g).toMonoidHom) := by
      show fixQ θK ρ.range = _
      rw [← hgen, fixQ_sup]
    rw [hC]
    refine Subgroup.index_inf_le.trans ?_
    rw [index_fixQ_conj, hfixJ, h.index_cV_jBar hn1 hnat0, sq]
  have hNcard : Nat.card (Multiplicative (Fin 2 → GaloisField 2 n)) = (2 ^ n) ^ 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2),
      Fintype.card_fin, GaloisField.card 2 n hn0]
  have hkerIdx : ψ'.ker.index = (2 ^ n) ^ 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hψ's, Subgroup.card_top, hNcard]
  let f : ↥UV →* ↥(omegaOneCenterIn R) ⧸ C := (QuotientGroup.mk' C).comp UV.subtype
  have hfker : f.ker = C.subgroupOf UV := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff _
  have hle : C.subgroupOf UV ≤ ψ'.ker := fun u hu => hCU u hu
  have hidx1 : ψ'.ker.index ≤ (C.subgroupOf UV).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hle)
  have hidx2 : (C.subgroupOf UV).index = Nat.card f.range := by
    rw [← hfker, Subgroup.index_ker]
  have hidx3 : Nat.card f.range ≤ C.index :=
    Nat.card_le_card_of_injective (fun x : f.range => (x : ↥(omegaOneCenterIn R) ⧸ C))
      Subtype.val_injective
  have hEq1 : Nat.card f.range = C.index := by
    have h1 : (2 ^ n) ^ 2 ≤ Nat.card f.range := by
      rw [← hkerIdx, ← hidx2]
      exact hidx1
    omega
  have hf : Function.Surjective f := by
    have : f.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hEq1]; rfl)
    exact MonoidHom.range_eq_top.mp this
  have hidxEq : (C.subgroupOf UV).index = ψ'.ker.index := by omega
  have hkerEq : ψ'.ker = C.subgroupOf UV := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hle
    have h1 := Subgroup.card_mul_index ψ'.ker
    have h2 := Subgroup.card_mul_index (C.subgroupOf UV)
    rw [hidxEq] at h2
    have hpos : 0 < ψ'.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have : Nat.card ψ'.ker = Nat.card (C.subgroupOf UV) :=
      Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
    exact this.le
  have hker' : ∀ u : ↥UV, ψ' u = 1 ↔ (u : ↥(omegaOneCenterIn R)) ∈ C := by
    intro u
    constructor
    · intro hu
      have : u ∈ ψ'.ker := hu
      rw [hkerEq] at this
      exact this
    · exact hCU u
  have hUC : ∀ v : ↥(omegaOneCenterIn R), ∃ u : ↥UV, ∃ c ∈ C,
      v = (u : ↥(omegaOneCenterIn R)) * c := by
    intro v
    obtain ⟨u, hu⟩ := hf (QuotientGroup.mk v)
    have hu' : (QuotientGroup.mk (u : ↥(omegaOneCenterIn R)) : ↥(omegaOneCenterIn R) ⧸ C) =
        QuotientGroup.mk v := hu
    have hc := QuotientGroup.eq.mp hu'
    refine ⟨u, (u : ↥(omegaOneCenterIn R))⁻¹ * v, hc, ?_⟩
    group
  obtain ⟨Ψ, hΨs, hΨk, hΨU⟩ := exists_hom_extend hVc C UV ψ' hψ's hker' hUC
  have hequiv : ∀ (x : ↥ρ.range) (v : ↥(omegaOneCenterIn R)), Ψ (θK (x : ↥K) v) =
      Multiplicative.ofAdd
        (((φ₀ x : SL(2, GaloisField 2 n)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
          (Multiplicative.toAdd (Ψ v))) := by
    intro x v
    obtain ⟨y, rfl⟩ := ρ.rangeRestrict_surjective x
    obtain ⟨u, c, hcC, rfl⟩ := hUC v
    have hcfix : θK (ρ y) c = c := mem_fixQ.mp hcC (ρ y) ⟨y, rfl⟩
    have hΨc : Ψ c = 1 := by
      rw [← MonoidHom.mem_ker, hΨk]
      exact hcC
    have hcoe : ((ρ.rangeRestrict y : ↥ρ.range) : ↥K) = ρ y := rfl
    have hL : Ψ (θK ((ρ.rangeRestrict y : ↥ρ.range) : ↥K) ((u : ↥(omegaOneCenterIn R)) * c)) =
        ψ' (act y u) := by
      rw [hcoe, map_mul, hcfix, map_mul, hΨc, mul_one]
      exact hΨU (act y u)
    have hR : Ψ ((u : ↥(omegaOneCenterIn R)) * c) = ψ' u := by
      rw [map_mul, hΨc, mul_one]
      exact hΨU u
    rw [hL, hR, hφ₀, hψ'e]
  exact NatQData.natQ ⟨φ₀, Ψ, hΨs, hΨk, hequiv⟩ hn0

end Natural

end CFSG.CGT.PushingUpLit.CGT6
