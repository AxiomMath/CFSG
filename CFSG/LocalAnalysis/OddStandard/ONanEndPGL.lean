module

public import Certificates.Data.ONanF2PGL
public import CFSG.GH74.KGroups.L34Tables
public import CFSG.Literature.GL52Group

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Certificates CFSG.Sporadic.Schreier F2
  CFSG.Blueprint

theorem pglCheck_parts (h : pglCheck = true) :
    factPglCount ∧ factPglCent ∧ factPglCosets := by
  simp only [pglCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem card_order_four_P (h : factPglCount) :
    Nat.card {g : QP.originalSubgroup // orderOf g = 4} = 3780 := by
  have h1 := card_filter QP QP_ok (fun g => orderIs g 4 = true)
  have h2 : Nat.card {g : QP.originalSubgroup // orderOf g = 4} =
      Nat.card {g : QP.originalSubgroup // orderIs (g : Equiv.Perm (Fin 42)) 4 = true} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun g => by
      rw [orderIs_iff _ (by norm_num), Subgroup.orderOf_coe])
  rw [h2, h1]
  exact h

theorem card_cent_PB (h : factPglCent) :
    Nat.card ↥(QP.originalSubgroup ⊓ centralizer ({PB} : Set (Equiv.Perm (Fin 42)))) = 16 := by
  rw [card_inf_centralizer QP QP_ok PB]
  exact h

theorem outer_sound
    (h : factPglCosets) (hPA : QP.originalSubgroup ≤ QA.originalSubgroup)
    (hnorm : ∀ a ∈ QA.originalSubgroup, ∀ p ∈ QP.originalSubgroup,
      a * p * a⁻¹ ∈ QP.originalSubgroup)
    {a : Equiv.Perm (Fin 42)} (ha : a ∈ QA.originalSubgroup) (hc : a * PB = PB * a)
    (h3 : a ^ 3 ∈ QP.originalSubgroup) : a ∈ QP.originalSubgroup := by
  classical
  obtain ⟨hmemA, hdist, hcase⟩ := h
  have hrepA : ∀ i, rep i ∈ QA.originalSubgroup := fun i =>
    (mem_iff_sift QA QA_ok _).2 (hmemA i)
  let P' : Subgroup ↥QA.originalSubgroup := QP.originalSubgroup.subgroupOf QA.originalSubgroup
  have hcardQ : Nat.card (↥QA.originalSubgroup ⧸ P') = 12 := by
    have h1 := Subgroup.index_mul_card P'
    have h2 : Nat.card P' = 20160 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPA).toEquiv, card_group QP QP_ok,
        QP_valid.2]
    have h3' : Nat.card ↥QA.originalSubgroup = 241920 := by
      rw [card_group QA QA_ok, QA_valid.2]
    rw [h2, h3'] at h1
    rw [← Subgroup.index_eq_card]
    omega
  let g : Fin 12 → ↥QA.originalSubgroup ⧸ P' := fun i => QuotientGroup.mk ⟨rep i, hrepA i⟩
  have hginj : Function.Injective g := by
    intro i j hij
    by_contra hne
    have h1 : QP.sift ((rep i)⁻¹ * rep j) 0 = false := hdist i j hne
    have h2 := QuotientGroup.eq.1 hij
    have h4 : (rep i)⁻¹ * rep j ∈ QP.originalSubgroup := Subgroup.mem_subgroupOf.1 h2
    rw [(mem_iff_sift QP QP_ok _).1 h4] at h1
    exact Bool.noConfusion h1
  have hgbij : Function.Bijective g :=
    hginj.bijective_of_nat_card_le (by rw [hcardQ, Nat.card_eq_fintype_card, Fintype.card_fin])
  obtain ⟨i, hi⟩ := hgbij.2 (QuotientGroup.mk ⟨a, ha⟩)
  have hp : (rep i)⁻¹ * a ∈ QP.originalSubgroup :=
    Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hi)
  rcases hcase i with h1 | h1 | h1
  ·
    have hrP : rep i ∈ QP.originalSubgroup := (mem_iff_sift QP QP_ok _).2 h1
    have := QP.originalSubgroup.mul_mem hrP hp
    simpa using this
  ·
    exfalso
    set p : Equiv.Perm (Fin 42) := (rep i)⁻¹ * a with hpdef
    have hp' : p⁻¹ ∈ QP.originalSubgroup := QP.originalSubgroup.inv_mem hp
    have c1 : a⁻¹ * p⁻¹ * a ∈ QP.originalSubgroup := by
      simpa using hnorm a⁻¹ (QA.originalSubgroup.inv_mem ha) p⁻¹ hp'
    have c2 : a⁻¹ * (a⁻¹ * p⁻¹ * a) * a ∈ QP.originalSubgroup := by
      simpa using hnorm a⁻¹ (QA.originalSubgroup.inv_mem ha) _ c1
    have hrr : rep i = a * p⁻¹ := by rw [hpdef]; group
    have h5 : rep i ^ 3 = a ^ 3 * ((a⁻¹ * (a⁻¹ * p⁻¹ * a) * a) * (a⁻¹ * p⁻¹ * a) * p⁻¹) := by
      rw [hrr]
      simp only [pow_succ, pow_zero, one_mul]
      group
    have h6 : rep i ^ 3 ∈ QP.originalSubgroup := by
      rw [h5]
      exact QP.originalSubgroup.mul_mem h3
        (QP.originalSubgroup.mul_mem (QP.originalSubgroup.mul_mem c2 c1) hp')
    have h7 := (mem_iff_sift QP QP_ok _).1 h6
    rw [h1] at h7
    exact Bool.noConfusion h7
  ·
    exfalso
    have hpe : (rep i)⁻¹ * a ∈ pElems := (mem_elemsT QP QP_ok _).2 hp
    have h5 := of_decide_eq_true (List.all_eq_true.1 h1 _ hpe)
    apply h5
    have h6 : rep i * ((rep i)⁻¹ * a) = a := by group
    rw [h6]
    exact hc

theorem mem_of_coprime_orderOf {X : Type*} [Group X] (K : Subgroup X) [K.Normal] [Finite X]
    {x : X} (h : Nat.Coprime (orderOf x) K.index) : x ∈ K := by
  have h1 : orderOf (QuotientGroup.mk' K x) ∣ orderOf x := orderOf_map_dvd _ x
  have h2 : orderOf (QuotientGroup.mk' K x) ∣ K.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (QuotientGroup.mk' K x) ∣ Nat.gcd (orderOf x) K.index := Nat.dvd_gcd h1 h2
  rw [h.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff x).1 h3

theorem pow_three_mem_of_index_three {X : Type*} [Group X] [Finite X] (K : Subgroup X) [K.Normal]
    (hidx : K.index = 3) (x : X) : x ^ 3 ∈ K := by
  have h1 : (QuotientGroup.mk' K x) ^ Nat.card (X ⧸ K) = 1 := pow_card_eq_one'
  rw [← Subgroup.index_eq_card, hidx, ← map_pow] at h1
  exact (QuotientGroup.eq_one_iff _).1 h1

theorem isConj_of_order_four_of_index_three
    (h : pglCheck = true) {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal]
    (hN : centralizer (K : Set X) = ⊥) (hidx : K.index = 3)
    (e : ↥K ≃* QP.originalSubgroup) {u v : X} (hu : orderOf u = 4) (hv : orderOf v = 4) :
    IsConj u v := by
  classical
  obtain ⟨hcount, hcent, hcos⟩ := pglCheck_parts h
  obtain ⟨M, hP, hA⟩ := autModel e
  have hPA : QP.originalSubgroup ≤ QA.originalSubgroup := P_le_A
  have hnorm : ∀ a ∈ QA.originalSubgroup, ∀ p ∈ QP.originalSubgroup,
      a * p * a⁻¹ ∈ QP.originalSubgroup := by
    intro a ha p hp
    rw [← hA] at ha
    rw [← hP] at hp ⊢
    obtain ⟨φ, hφ⟩ := M.Φ.surjective ⟨a, ha⟩
    obtain ⟨x, hx⟩ := M.e.surjective ⟨p, hp⟩
    have h1 := M.spec φ x
    have ha' : (M.Φ φ : Equiv.Perm (Fin 42)) = a := congrArg Subtype.val hφ
    have hp' : (M.e x : Equiv.Perm (Fin 42)) = p := congrArg Subtype.val hx
    rw [ha', hp'] at h1
    rw [← h1]
    exact (M.e (φ x)).2
  have hψinj : Function.Injective (M.actHom K) := M.actHom_injective K hN
  have hψK : ∀ k : K, M.actHom K (k : X) = ((M.e k : M.P) : Equiv.Perm (Fin 42)) := by
    intro k
    have hσA : (M.actHom K (k : X))⁻¹ * ((M.e k : M.P) : Equiv.Perm (Fin 42)) ∈ M.A := by
      refine M.A.mul_mem (M.A.inv_mem (M.actHom_mem K _)) ?_
      rw [hA]
      exact hPA (by rw [← hP]; exact (M.e k).2)
    have hσ : (M.actHom K (k : X))⁻¹ * ((M.e k : M.P) : Equiv.Perm (Fin 42)) = 1 := by
      refine M.centralizer_trivial hσA fun y hy => ?_
      obtain ⟨z, hz⟩ := M.e.surjective ⟨y, hy⟩
      have hy' : ((M.e z : M.P) : Equiv.Perm (Fin 42)) = y := congrArg Subtype.val hz
      have hspec := M.actHom_spec K (k : X) z
      have hconj : MulAut.conjNormal (H := K) (k : X) z = k * z * k⁻¹ :=
        Subtype.ext (by simp [MulAut.conjNormal_apply])
      rw [hconj, map_mul, map_mul, map_inv] at hspec
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hspec
      rw [← hy']
      set a : Equiv.Perm (Fin 42) := ((M.e k : M.P) : Equiv.Perm (Fin 42))
      set b : Equiv.Perm (Fin 42) := M.actHom K (k : X)
      set y' : Equiv.Perm (Fin 42) := ((M.e z : M.P) : Equiv.Perm (Fin 42))
      have h4 : a * y' = b * y' * b⁻¹ * a := by
        calc a * y' = (a * y' * a⁻¹) * a := by group
          _ = (b * y' * b⁻¹) * a := by rw [hspec]
      calc b⁻¹ * a * y' = b⁻¹ * (a * y') := by rw [mul_assoc]
        _ = b⁻¹ * (b * y' * b⁻¹ * a) := by rw [h4]
        _ = y' * (b⁻¹ * a) := by group
    exact inv_mul_eq_one.1 hσ
  have hψmem : ∀ x : X, M.actHom K x ∈ M.P → x ∈ K := by
    intro x hx
    obtain ⟨k, hk⟩ := M.inner_of_mem (MulAut.conjNormal (H := K) x) hx
    have hc : (k : X)⁻¹ * x ∈ centralizer (K : Set X) := by
      rw [mem_centralizer_iff]
      intro y hy
      have h5 := congrArg Subtype.val (hk ⟨y, hy⟩)
      simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h5
      have h6 : x * y = k * y * (k : X)⁻¹ * x := by
        calc x * y = (x * y * x⁻¹) * x := by group
          _ = ((k : X) * y * (k : X)⁻¹) * x := by rw [h5]
      calc y * ((k : X)⁻¹ * x) = (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹ * x) := by group
        _ = (k : X)⁻¹ * (x * y) := by rw [h6]
        _ = (k : X)⁻¹ * x * y := by rw [mul_assoc]
    rw [hN, Subgroup.mem_bot] at hc
    have hxk : x = k := (inv_mul_eq_one.1 hc).symm
    rw [hxk]
    exact k.2
  have hPB : PB ∈ M.P := by
    rw [hP]
    exact gens_mem PB (by simp)
  set u₁ : K := M.e.symm ⟨PB, hPB⟩ with hu₁
  have hu₁e : ((M.e u₁ : M.P) : Equiv.Perm (Fin 42)) = PB := by simp [hu₁]
  have hψu : M.actHom K (u₁ : X) = PB := (hψK u₁).trans hu₁e
  have hcentle : centralizer ({(u₁ : X)} : Set X) ≤ K := by
    intro x hx
    refine hψmem x ?_
    rw [hP]
    have hcomm : M.actHom K x * PB = PB * M.actHom K x := by
      calc M.actHom K x * PB = M.actHom K x * M.actHom K (u₁ : X) := by rw [hψu]
        _ = M.actHom K (x * (u₁ : X)) := (map_mul _ _ _).symm
        _ = M.actHom K ((u₁ : X) * x) := congrArg _ (mem_centralizer_singleton_iff.1 hx)
        _ = M.actHom K (u₁ : X) * M.actHom K x := map_mul _ _ _
        _ = PB * M.actHom K x := by rw [hψu]
    refine outer_sound hcos hPA hnorm (by rw [← hA]; exact M.actHom_mem K x) hcomm ?_
    rw [← map_pow]
    have h5 := hψK ⟨x ^ 3, pow_three_mem_of_index_three K hidx x⟩
    rw [show M.actHom K (x ^ 3) = M.actHom K (((⟨x ^ 3, pow_three_mem_of_index_three K hidx x⟩ : K)
      : X)) from rfl, h5, ← hP]
    exact (M.e _).2
  have hcardK : Nat.card K = 20160 := by
    rw [Nat.card_congr M.e.toEquiv, hP, card_group QP QP_ok, QP_valid.2]
  have hcardX : Nat.card X = 60480 := by
    have h5 := Subgroup.index_mul_card K
    rw [hidx, hcardK] at h5
    omega
  have hcardC : Nat.card ↥(centralizer ({(u₁ : X)} : Set X)) = 16 := by
    have e1 : centralizer ({(u₁ : X)} : Set X) ⊓ K = centralizer ({(u₁ : X)} : Set X) :=
      inf_eq_left.2 hcentle
    have e2 := card_centralizer_inf_normal K M.P M.e u₁
    rw [e1, hu₁e] at e2
    rw [e2, hP]
    exact card_cent_PB hcent
  have hu₀ord : orderOf (u₁ : X) = 4 := by
    have h4 : orderOf PB = 4 := (orderIs_iff PB (by norm_num)).1 orders_ok.2.1
    calc orderOf (u₁ : X) = orderOf u₁ := Subgroup.orderOf_coe u₁
      _ = orderOf (M.e u₁) := (MulEquiv.orderOf_eq M.e u₁).symm
      _ = orderOf (((M.e u₁ : M.P) : Equiv.Perm (Fin 42))) := (Subgroup.orderOf_coe _).symm
      _ = 4 := by rw [hu₁e]; exact h4
  have hcls : Nat.card {y : X // IsConj (u₁ : X) y} = 3780 := by
    have h5 := CFSG.Literature.GL52.card_isConj_mul_card_centralizer (u₁ : X)
    rw [hcardC, hcardX] at h5
    omega
  have hmemK : ∀ x : X, orderOf x = 4 → x ∈ K := fun x hx =>
    mem_of_coprime_orderOf K (by rw [hx, hidx]; norm_num)
  have hS : Nat.card {y : X // orderOf y = 4} ≤ 3780 := by
    have hcountP : Nat.card {g : M.P // orderOf g = 4} = 3780 := by
      rw [hP]
      exact card_order_four_P hcount
    rw [← hcountP]
    refine Nat.card_le_card_of_injective
      (fun y => ⟨M.e ⟨y.1, hmemK y.1 y.2⟩, ?_⟩) ?_
    · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact y.2
    · intro y y' hyy'
      have h5 := M.e.injective (congrArg Subtype.val hyy')
      exact Subtype.ext (show y.1 = y'.1 from congrArg (fun z : K => (z : X)) h5)
  have hconj : ∀ g y : X, orderOf y = 4 → orderOf (g * y * g⁻¹) = 4 := by
    intro g y hy
    have h5 := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
    simpa [MulAut.conj_apply] using h5.trans hy
  have key := CFSG.Literature.GL52.isConj_of_card_le (u₁ : X) (fun y => orderOf y = 4) hu₀ord
    hconj (by rw [hcls]; exact hS)
  exact (key u hu).symm.trans (key v hv)

theorem centralizer_eq_bot_of_odd_index
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore 2 X = ⊥) (K : Subgroup X) [K.Normal]
    (hodd : ¬ 2 ∣ K.index) (e : ↥K ≃* QP.originalSubgroup) :
    centralizer (K : Set X) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.pPrimeCore_eq_bot_iff.1 hO _ inferInstance ?_
  by_contra hcop
  have h2 : 2 ∣ Nat.card (centralizer (K : Set X)) :=
    not_not.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).not.1 hcop)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hgX : orderOf (g : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hg
  have hgK : (g : X) ∈ K := mem_of_coprime_orderOf K (by
    rw [hgX]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
  have hk : (⟨(g : X), hgK⟩ : K) = 1 :=
    center_trivial e _ fun n => Subtype.ext ((mem_centralizer_iff.1 g.2) n n.2)
  have h1 : (g : X) = 1 := congrArg Subtype.val hk
  rw [h1, orderOf_one] at hgX
  omega

theorem eq_top_of_not_isConj_order_four
    (h : pglCheck = true) {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore 2 X = ⊥)
    {K : Subgroup X} (hK : K.Normal) (hL : LieModel K .PSL 3 2 2) (hidx : K.index ∣ 3)
    {u v : X} (hu : orderOf u = 4) (hv : orderOf v = 4) (hnc : ¬ IsConj u v) : K = ⊤ := by
  have := hK
  by_contra hne
  have h3 : K.index = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hidx with h1 | h1
    · exact absurd (Subgroup.index_eq_one.1 h1) hne
    · exact h1
  obtain ⟨e⟩ := equiv_of_lieModel hL
  have hodd : ¬ 2 ∣ K.index := by
    rw [h3]
    norm_num
  exact hnc (isConj_of_order_four_of_index_three h K
    (centralizer_eq_bot_of_odd_index hO K hodd e) h3 e hu hv)

end CFSG.OddStandard.ONanRec
