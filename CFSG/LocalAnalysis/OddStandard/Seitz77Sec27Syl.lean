module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LocalAnalysis.OddStandard.Seitz77WBridgeSylow
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem mem_sup_zpowers_of_sq_one {W : Subgroup G} {t : G} (ht2 : t * t = 1)
    (htW : ∀ w ∈ W, t * w * t⁻¹ ∈ W) {x : G} :
    x ∈ W ⊔ zpowers t ↔ x ∈ W ∨ ∃ w ∈ W, x = w * t := by
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  let K : Subgroup G :=
    { carrier := {x | x ∈ W ∨ ∃ w ∈ W, x = w * t}
      one_mem' := Or.inl W.one_mem
      mul_mem' := by
        rintro a b (ha | ⟨u, hu, rfl⟩) (hb | ⟨v, hv, rfl⟩)
        · exact Or.inl (W.mul_mem ha hb)
        · exact Or.inr ⟨a * v, W.mul_mem ha hv, by rw [mul_assoc]⟩
        · refine Or.inr ⟨u * (t * b * t⁻¹), W.mul_mem hu (htW b hb), ?_⟩
          group
        · refine Or.inl ?_
          have h : u * t * (v * t) = u * (t * v * t⁻¹) := by
            calc u * t * (v * t) = u * (t * v * t⁻¹) * (t * t) := by group
              _ = u * (t * v * t⁻¹) := by rw [ht2, mul_one]
          rw [h]
          exact W.mul_mem hu (htW v hv)
      inv_mem' := by
        rintro a (ha | ⟨u, hu, rfl⟩)
        · exact Or.inl (W.inv_mem ha)
        · refine Or.inr ⟨t * u⁻¹ * t⁻¹, htW _ (W.inv_mem hu), ?_⟩
          calc (u * t)⁻¹ = t⁻¹ * u⁻¹ := mul_inv_rev _ _
            _ = t * u⁻¹ := by rw [ht1]
            _ = t * u⁻¹ * t⁻¹ * t := by group }
  constructor
  · intro hx
    have hle : W ⊔ zpowers t ≤ K :=
      sup_le (fun w hw => Or.inl hw)
        ((zpowers_le).mpr (Or.inr ⟨1, W.one_mem, (one_mul t).symm⟩))
    exact hle hx
  · rintro (hx | ⟨w, hw, rfl⟩)
    · exact mem_sup_left hx
    · exact mul_mem (mem_sup_left hw) (mem_sup_right (mem_zpowers t))

theorem exists_mem_normalizer_sdiff [Finite G] {Y Z : Subgroup G} (hZ : IsPGroup 2 Z)
    (hYZ : Y ≤ Z) (hne : Y ≠ Z) : ∃ g ∈ Z, g ∈ normalizer (Y : Set G) ∧ g ∉ Y := by
  have hI : Y.subgroupOf Z < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hne (le_antisymm hYZ fun x hx => ?_)
    have hx' : (⟨x, hx⟩ : Z) ∈ Y.subgroupOf Z := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp hx'
  have : Group.IsNilpotent Z := hZ.isNilpotent
  have hnc : NormalizerCondition Z := Group.normalizerCondition_of_isNilpotent (G := Z)
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt (hnc _ hI)
  have hgN : (x : G) ∈ normalizer (Y : Set G) := by
    have hxsub : x ∈ (normalizer (Y : Set G)).subgroupOf Z := by
      rw [subgroupOf_normalizer_eq hYZ]
      exact hxN
    exact mem_subgroupOf.mp hxsub
  exact ⟨x, x.2, hgN, fun hx => hxnot (mem_subgroupOf.mpr hx)⟩

end Generic

namespace IsSetting25

variable {G : Type} [Group G] [Finite G] {A R X O : Subgroup G} {t : G}
  (S : IsSetting25 A R t X O)

section Basic

include S

theorem two_elt_mem_E {x : G} (hx : x ∈ centralizer ((R ⊔ zpowers t : Subgroup G) : Set G))
    (h2 : ∃ n : ℕ, orderOf x = 2 ^ n) : x ∈ R ⊔ zpowers t := by
  rw [← S.O_sup] at hx
  obtain ⟨o, ho, e, he, rfl⟩ := mem_sup_of_forall_comm (fun o ho _ he => S.O_comm ho he) hx
  have hoe : e * o = o * e := (S.O_comm ho he).symm
  have he2 : ∃ n : ℕ, orderOf e = 2 ^ n := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp S.isPGroup_E ⟨e, he⟩
    exact ⟨n, by rwa [Subgroup.orderOf_mk] at hn⟩
  have h2' : ∃ m : ℕ, orderOf (e * o) = 2 ^ m := by
    rw [hoe]
    exact h2
  have := S.eq_one_of_two_power ho hoe he2 h2'
  rw [this, one_mul]
  exact he

theorem O_le_centralizer_A (F : ActionFacts A R) : O ≤ centralizer (A : Set G) := by
  intro o ho
  have hoE : o ∈ centralizer ((R ⊔ zpowers t : Subgroup G) : Set G) := S.O_le_centralizer ho
  have hot : o * t = t * o :=
    (mem_centralizer_iff.mp hoE t (mem_sup_right (mem_zpowers t))).symm
  have hoN : o ∈ normalizer (A : Set G) :=
    S.cent_t (mem_centralizer_singleton_iff.mpr hot)
  have hoR : ∀ w ∈ R, o * w = w * o := fun w hw =>
    (mem_centralizer_iff.mp hoE w (mem_sup_left hw)).symm
  obtain ⟨r, hr, k, hk, rfl⟩ := mem_sup_centralizer S.W_le_A (F.cent o hoN hoR)
  have hrk : Commute r k := mem_centralizer_iff.mp hk r (S.W_le_A hr)
  have hodd := S.odd_orderOf_of_mem_O ho
  obtain ⟨a, ha⟩ := hodd
  have hr2 : r * r = 1 := by
    have := S.W_elem.2 r hr
    rwa [sq] at this
  have h1 : (r * k) ^ (orderOf (r * k)) = 1 := pow_orderOf_eq_one _
  rw [hrk.mul_pow, ha] at h1
  have hrpow : r ^ (2 * a + 1) = r := by
    rw [pow_succ, pow_mul, sq, hr2, one_pow, one_mul]
  rw [hrpow] at h1
  have hrk' : r = (k ^ (2 * a + 1))⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hrC : r ∈ centralizer (A : Set G) := by
    rw [hrk']
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hk _)
  have hrAC : r ∈ A ⊓ centralizer (A : Set G) := mem_inf.mpr ⟨S.W_le_A hr, hrC⟩
  have hord : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hr2)
  have hord' : orderOf r ∣ Nat.card ↥(A ⊓ centralizer (A : Set G)) := by
    exact Subgroup.orderOf_dvd_natCard (A ⊓ centralizer (A : Set G)) hrAC
  have hodd' := S.odd_inf.of_dvd_nat hord'
  have hr1 : r = 1 := by
    have : orderOf r = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
      · exact h
      · exfalso
        rw [h] at hodd'
        exact absurd hodd' (by decide)
    exact orderOf_eq_one_iff.mp this
  rw [hr1, one_mul]
  exact hk

theorem inf_centralizer_A_le_O : A ⊓ centralizer (A : Set G) ≤ O := by
  intro z hz
  obtain ⟨hzA, hzC⟩ := mem_inf.mp hz
  have hzE : z ∈ centralizer ((R ⊔ zpowers t : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro e he
    have hEA : (R ⊔ zpowers t : Subgroup G) ≤ centralizer (A : Set G) ⊔ A := by
      refine sup_le (fun r hr => mem_sup_right (S.W_le_A hr)) (zpowers_le.mpr ?_)
      exact mem_sup_left S.t_cent
    have hcomm : ∀ x ∈ (R ⊔ zpowers t : Subgroup G), x * z = z * x := by
      intro x hx
      have hx' : x ∈ centralizer ({z} : Set G) := by
        have hle : (R ⊔ zpowers t : Subgroup G) ≤ centralizer ({z} : Set G) := by
          refine sup_le (fun r hr => ?_) (zpowers_le.mpr ?_)
          · rw [mem_centralizer_singleton_iff]
            exact mem_centralizer_iff.mp hzC r (S.W_le_A hr)
          · rw [mem_centralizer_singleton_iff]
            exact (mem_centralizer_iff.mp S.t_cent z hzA).symm
        exact hle hx
      exact mem_centralizer_singleton_iff.mp hx'
    exact hcomm e he
  rw [← S.O_sup] at hzE
  obtain ⟨o, ho, e, he, rfl⟩ := mem_sup_of_forall_comm (fun o ho _ he => S.O_comm ho he) hzE
  have hoe : o * e = e * o := S.O_comm ho he
  have hodd : Odd (orderOf (o * e)) :=
    S.odd_inf.of_dvd_nat (Subgroup.orderOf_dvd_natCard (A ⊓ centralizer (A : Set G)) hz)
  have hcomm : Commute o e := hoe
  have h1 : o ^ (orderOf (o * e)) * e ^ (orderOf (o * e)) = 1 := by
    rw [← hcomm.mul_pow]
    exact pow_orderOf_eq_one _
  have h2 : e ^ (orderOf (o * e)) = 1 := by
    have hO : e ^ (orderOf (o * e)) ∈ O := by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ ho _)
    have hE : e ^ (orderOf (o * e)) ∈ (R ⊔ zpowers t : Subgroup G) := Subgroup.pow_mem _ he _
    exact Subgroup.disjoint_def.mp S.disjoint_O_E hO hE
  have he1 : e = 1 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp S.isPGroup_E ⟨e, he⟩
    rw [Subgroup.orderOf_mk] at hn
    have hdvd : orderOf e ∣ orderOf (o * e) := orderOf_dvd_of_pow_eq_one h2
    rcases n with _ | n
    · exact orderOf_eq_one_iff.mp (by rw [hn]; norm_num)
    · exfalso
      rw [hn] at hdvd
      have h2dvd : 2 ∣ orderOf (o * e) :=
        (dvd_pow_self 2 (Nat.succ_ne_zero n)).trans hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)
  rw [he1, mul_one]
  exact ho

end Basic

section Wt

variable {Sy Wt : Subgroup G}
  (hSy : IsSylowOf 2 Sy (normalizer ((R ⊔ zpowers t : Subgroup G) : Set G)))
  (hWt : WtSpec R t X O Wt)

include S hSy hWt

theorem t_conj_mem_inf_Wt {w : G} (hw : w ∈ Sy ⊓ Wt) : t * w * t⁻¹ ∈ Sy ⊓ Wt := by
  have htSy : t ∈ Sy := S.E_le_sylow hSy (mem_sup_right (mem_zpowers t))
  have h := (normal_inf_Wt hSy hWt).conj_mem ⟨w, (mem_inf.mp hw).1⟩ (mem_subgroupOf.mpr hw)
    ⟨t, htSy⟩
  exact mem_subgroupOf.mp h

theorem exists_commutator_eq {v : G} (hv : v ∈ R) :
    ∃ w ∈ Sy ⊓ Wt, t * w * t⁻¹ * w⁻¹ = v := by
  have hdisj : Disjoint O R := S.disjoint_O_of_isPGroup S.isPGroup_W
  have hPO : Sy ⊓ Wt ≤ normalizer (O : Set G) := fun x hx =>
    Subgroup.mem_normalizer_fintype fun o ho =>
      S.O_norm x (hSy.le (Subgroup.mem_inf.mp hx).1) o ho
  obtain ⟨w, hwWt, hwO⟩ := hWt.comm_onto v hv
  obtain ⟨o, ho, w₂, hw₂, rfl⟩ :=
    S.eq_mul_of_card (Z := Wt) (P := Sy ⊓ Wt) (k := 8) hWt.O_le inf_le_right
      (S.card_inf_Wt hSy hWt) hWt.card hPO w hwWt
  have hc := S.commutator_t_mem_W (hSy.le (Subgroup.mem_inf.mp hw₂).1)
  have hcE : t * w₂ * t⁻¹ * w₂⁻¹ ∈ R ⊔ zpowers t := Subgroup.mem_sup_left hc
  have ht : o * t = t * o := S.O_comm ho (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have hcomm : t * (o * w₂) * t⁻¹ * (o * w₂)⁻¹ = t * w₂ * t⁻¹ * w₂⁻¹ :=
    calc t * (o * w₂) * t⁻¹ * (o * w₂)⁻¹
        = (t * o) * w₂ * t⁻¹ * w₂⁻¹ * o⁻¹ := by group
      _ = (o * t) * w₂ * t⁻¹ * w₂⁻¹ * o⁻¹ := by rw [ht]
      _ = o * (t * w₂ * t⁻¹ * w₂⁻¹) * o⁻¹ := by group
      _ = t * w₂ * t⁻¹ * w₂⁻¹ := by rw [S.O_comm ho hcE, mul_inv_cancel_right]
  rw [hcomm] at hwO
  have h1 : v⁻¹ * (t * w₂ * t⁻¹ * w₂⁻¹) = 1 :=
    Subgroup.disjoint_def.mp hdisj hwO (R.mul_mem (R.inv_mem hv) hc)
  exact ⟨w₂, hw₂, (inv_mul_eq_one.mp h1).symm⟩

theorem exists_conj_eq {v : G} (hv : v ∈ R) :
    ∃ w ∈ Sy ⊓ Wt, w * t * w⁻¹ = t * v := by
  obtain ⟨w, hw, h⟩ := S.exists_commutator_eq hSy hWt hv
  refine ⟨w, hw, ?_⟩
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right S.t_sq
  rw [← h, ht1]
  calc w * t * w⁻¹ = (t * t) * w * t * w⁻¹ := by rw [S.t_sq, one_mul]
    _ = t * (t * w * t * w⁻¹) := by group

theorem eq_of_elemAbelian_card {B : Subgroup G} (hB : B ≤ (Sy ⊓ Wt) ⊔ zpowers t)
    (hBe : IsElemAbelian 2 B) (hBc : Nat.card B = 2 ^ 8) : B = Sy ⊓ Wt := by
  have hWcard : Nat.card ↥(Sy ⊓ Wt) = 2 ^ 8 := S.card_inf_Wt hSy hWt
  have htW : ∀ w ∈ Sy ⊓ Wt, t * w * t⁻¹ ∈ Sy ⊓ Wt := fun w hw =>
    S.t_conj_mem_inf_Wt hSy hWt hw
  have htnot : t ∉ Sy ⊓ Wt := t_not_mem_inf_Wt hWt
  by_cases hBW : B ≤ Sy ⊓ Wt
  · exact eq_of_le_of_card_ge hBW (by rw [hBc, hWcard])
  · exfalso
    obtain ⟨b, hbB, hbW⟩ := Set.not_subset.mp hBW
    obtain ⟨w₁, hw₁, rfl⟩ : ∃ w₁ ∈ Sy ⊓ Wt, b = w₁ * t :=
      ((mem_sup_zpowers_of_sq_one S.t_sq htW).mp (hB hbB)).resolve_left hbW
    have hWab := S.elem_inf_Wt hSy hWt
    have hidx : ((Sy ⊓ Wt).subgroupOf B).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨w₁ * t, hbB⟩, fun x => ?_⟩
      have hx := hB x.2
      rcases (mem_sup_zpowers_of_sq_one S.t_sq htW).mp hx with hxW | ⟨w, hw, hxw⟩
      · have h1 : x ∈ (Sy ⊓ Wt).subgroupOf B := mem_subgroupOf.mpr hxW
        have h2 : x * ⟨w₁ * t, hbB⟩ ∉ (Sy ⊓ Wt).subgroupOf B := by
          intro h
          have h' : (x : G) * (w₁ * t) ∈ Sy ⊓ Wt := mem_subgroupOf.mp h
          apply htnot
          have := (Sy ⊓ Wt).mul_mem ((Sy ⊓ Wt).inv_mem ((Sy ⊓ Wt).mul_mem hxW hw₁)) h'
          simpa [mul_assoc] using this
        exact Or.inr ⟨h1, h2⟩
      · have h1 : x ∉ (Sy ⊓ Wt).subgroupOf B := by
          intro h
          have h' : (x : G) ∈ Sy ⊓ Wt := mem_subgroupOf.mp h
          apply htnot
          rw [hxw] at h'
          have := (Sy ⊓ Wt).mul_mem ((Sy ⊓ Wt).inv_mem hw) h'
          simpa [mul_assoc] using this
        have h2 : x * ⟨w₁ * t, hbB⟩ ∈ (Sy ⊓ Wt).subgroupOf B := by
          rw [mem_subgroupOf]
          show (x : G) * (w₁ * t) ∈ Sy ⊓ Wt
          rw [hxw]
          have : w * t * (w₁ * t) = w * (t * w₁ * t⁻¹) * (t * t) := by group
          rw [this, S.t_sq, mul_one]
          exact (Sy ⊓ Wt).mul_mem hw (htW w₁ hw₁)
        exact Or.inl ⟨h2, h1⟩
    have hcard1 : Nat.card B = 2 * Nat.card ↥((Sy ⊓ Wt) ⊓ B) := by
      have h := Subgroup.relIndex_mul_card (Sy ⊓ Wt) B
      rw [show (Sy ⊓ Wt).relIndex B = 2 from hidx] at h
      omega
    have hle : (Sy ⊓ Wt) ⊓ B ≤ R := by
      intro x hx
      obtain ⟨hxW, hxB⟩ := mem_inf.mp hx
      have hc1 : x * (w₁ * t) = (w₁ * t) * x := L34.comm_of_isElemAbelian hBe hxB hbB
      have hc2 : x * w₁ = w₁ * x := L34.comm_of_isElemAbelian hWab hxW hw₁
      have hc3 : x * t = t * x := by
        have : w₁ * (x * t) = w₁ * (t * x) := by
          calc w₁ * (x * t) = (w₁ * x) * t := by rw [mul_assoc]
            _ = (x * w₁) * t := by rw [hc2]
            _ = x * (w₁ * t) := by rw [mul_assoc]
            _ = (w₁ * t) * x := hc1
            _ = w₁ * (t * x) := by rw [mul_assoc]
        exact mul_left_cancel this
      rw [← S.inf_Wt_inf_centralizer_t hSy hWt]
      exact mem_inf.mpr ⟨hxW, mem_centralizer_singleton_iff.mpr hc3⟩
    have hRcard : Nat.card ↥R = 16 := S.W_card
    have := Subgroup.card_le_of_le hle
    have h2 : Nat.card B = 2 ^ 8 := hBc
    omega

theorem isSylowOf_Y_centralizer :
    IsSylowOf 2 ((Sy ⊓ Wt) ⊔ zpowers t) (centralizer (R : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYeq : (Sy ⊓ Wt) ⊔ zpowers t = Sy ⊓ centralizer (R : Set G) :=
    (S.Sy_inf_centralizer_W hSy hWt).symm
  have hWab := S.elem_inf_Wt hSy hWt
  have htW : ∀ w ∈ Sy ⊓ Wt, t * w * t⁻¹ ∈ Sy ⊓ Wt := fun w hw =>
    S.t_conj_mem_inf_Wt hSy hWt hw
  have htnot : t ∉ Sy ⊓ Wt := t_not_mem_inf_Wt hWt
  have hRW : R ≤ Sy ⊓ Wt := S.W_le_inf_Wt hSy hWt
  have hY2 : IsPGroup 2 ↥((Sy ⊓ Wt) ⊔ zpowers t) := hYeq ▸ hSy.isPGroup.to_inf_left
  have hYC : (Sy ⊓ Wt) ⊔ zpowers t ≤ centralizer (R : Set G) := hYeq ▸ inf_le_right
  obtain ⟨Q, hQ⟩ := (hY2.comap_subtype :
    IsPGroup 2 (((Sy ⊓ Wt) ⊔ zpowers t).subgroupOf (centralizer (R : Set G)))).exists_le_sylow
  have hZsyl : IsSylowOf 2 ((Q : Subgroup (centralizer (R : Set G))).map
      (centralizer (R : Set G)).subtype) (centralizer (R : Set G)) := ⟨Q, rfl⟩
  set Z : Subgroup G := (Q : Subgroup (centralizer (R : Set G))).map
      (centralizer (R : Set G)).subtype with hZdef
  have hYZ : (Sy ⊓ Wt) ⊔ zpowers t ≤ Z := fun y hy =>
    ⟨⟨y, hYC hy⟩, hQ (mem_subgroupOf.mpr hy), rfl⟩
  have hZY : Z = (Sy ⊓ Wt) ⊔ zpowers t := by
    by_contra hne
    obtain ⟨g, hgZ, hgN, hgY⟩ := exists_mem_normalizer_sdiff hZsyl.isPGroup hYZ (Ne.symm hne)
    have hgC : g ∈ centralizer (R : Set G) := hZsyl.le hgZ
    have hB : Subgroup.map (MulAut.conj g).toMonoidHom (Sy ⊓ Wt) = Sy ⊓ Wt := by
      apply S.eq_of_elemAbelian_card hSy hWt
      · rintro _ ⟨w, hw, rfl⟩
        exact (mem_normalizer_iff.mp hgN w).mp (mem_sup_left hw)
      · exact L34.isElemAbelian_map _ hWab
      · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, S.card_inf_Wt hSy hWt]
    have hgW : ∀ w ∈ Sy ⊓ Wt, g * w * g⁻¹ ∈ Sy ⊓ Wt := fun w hw => by
      rw [← hB]
      exact ⟨w, hw, rfl⟩
    have hgW' : ∀ w ∈ Sy ⊓ Wt, g⁻¹ * w * g ∈ Sy ⊓ Wt := fun w hw => by
      rw [← hB] at hw
      obtain ⟨w', hw', rfl⟩ := hw
      have : g⁻¹ * (g * w' * g⁻¹) * g = w' := by group
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [this]
      exact hw'
    have ht'Y : g * t * g⁻¹ ∈ (Sy ⊓ Wt) ⊔ zpowers t :=
      (mem_normalizer_iff.mp hgN t).mp (mem_sup_right (mem_zpowers t))
    have ht'sq : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
      calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [S.t_sq]; group
    have ht'W : g * t * g⁻¹ ∉ Sy ⊓ Wt := fun h => htnot (by
      have := hgW' _ h
      simpa [mul_assoc] using this)
    obtain ⟨w₁, hw₁, ht'eq⟩ :=
      ((mem_sup_zpowers_of_sq_one S.t_sq htW).mp ht'Y).resolve_left ht'W
    have hsq : w₁ * w₁ = 1 := by
      have := hWab.2 w₁ hw₁
      rwa [sq] at this
    have hw₁R : w₁ ∈ R := by
      have h1 : w₁ * t * (w₁ * t) = 1 := by rw [← ht'eq]; exact ht'sq
      have h2 : w₁ * (t * w₁ * t⁻¹) = 1 := by
        have : w₁ * t * (w₁ * t) = w₁ * (t * w₁ * t⁻¹) * (t * t) := by group
        rw [this, S.t_sq, mul_one] at h1
        exact h1
      have h3 : t * w₁ * t⁻¹ = w₁ := by
        rw [eq_inv_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right hsq]
      rw [← S.inf_Wt_inf_centralizer_t hSy hWt]
      refine mem_inf.mpr ⟨hw₁, mem_centralizer_singleton_iff.mpr ?_⟩
      calc w₁ * t = (t * w₁ * t⁻¹) * t := by rw [h3]
        _ = t * w₁ := by group
    obtain ⟨w₀, hw₀, hw₀t⟩ := S.exists_conj_eq hSy hWt hw₁R
    have htw₁ : t * w₁ = w₁ * t := S.t_comm_W hw₁R
    have hg'C : w₀⁻¹ * g ∈ centralizer ((R ⊔ zpowers t : Subgroup G) : Set G) := by
      have hle : (R ⊔ zpowers t : Subgroup G) ≤ centralizer ({w₀⁻¹ * g} : Set G) := by
        refine sup_le (fun r hr => ?_) ?_
        · rw [mem_centralizer_singleton_iff]
          have h1 : r * g = g * r := mem_centralizer_iff.mp hgC r hr
          have h2 : r * w₀⁻¹ = w₀⁻¹ * r :=
            L34.comm_of_isElemAbelian hWab (hRW hr) ((Sy ⊓ Wt).inv_mem hw₀)
          calc r * (w₀⁻¹ * g) = (r * w₀⁻¹) * g := by rw [mul_assoc]
            _ = (w₀⁻¹ * r) * g := by rw [h2]
            _ = w₀⁻¹ * (r * g) := by rw [mul_assoc]
            _ = w₀⁻¹ * (g * r) := by rw [h1]
            _ = (w₀⁻¹ * g) * r := by rw [mul_assoc]
        · rw [zpowers_le, mem_centralizer_singleton_iff]
          have h1 : g * t * g⁻¹ = w₀ * t * w₀⁻¹ := by
            rw [ht'eq, hw₀t, ← htw₁]
          calc t * (w₀⁻¹ * g) = w₀⁻¹ * (w₀ * t * w₀⁻¹) * g := by group
            _ = w₀⁻¹ * (g * t * g⁻¹) * g := by rw [h1]
            _ = (w₀⁻¹ * g) * t := by group
      intro e he
      exact mem_centralizer_singleton_iff.mp (hle he)
    have hg'Z : w₀⁻¹ * g ∈ Z := Z.mul_mem (Z.inv_mem (hYZ (mem_sup_left hw₀))) hgZ
    have hg'2 : ∃ n : ℕ, orderOf (w₀⁻¹ * g) = 2 ^ n := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hZsyl.isPGroup ⟨w₀⁻¹ * g, hg'Z⟩
      exact ⟨n, by rwa [Subgroup.orderOf_mk] at hn⟩
    have hg'E := S.two_elt_mem_E hg'C hg'2
    have hEY : (R ⊔ zpowers t : Subgroup G) ≤ (Sy ⊓ Wt) ⊔ zpowers t :=
      sup_le_sup_right hRW _
    apply hgY
    have : g = w₀ * (w₀⁻¹ * g) := by group
    rw [this]
    exact ((Sy ⊓ Wt) ⊔ zpowers t).mul_mem (mem_sup_left hw₀) (hEY hg'E)
  rw [hZY] at hZsyl
  exact hZsyl

theorem isSylowOf_centralizer_W :
    IsSylowOf 2 (Sy ⊓ Wt) (centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY := S.isSylowOf_Y_centralizer hSy hWt
  have hWab := S.elem_inf_Wt hSy hWt
  have htW : ∀ w ∈ Sy ⊓ Wt, t * w * t⁻¹ ∈ Sy ⊓ Wt := fun w hw =>
    S.t_conj_mem_inf_Wt hSy hWt hw
  have hRW : R ≤ Sy ⊓ Wt := S.W_le_inf_Wt hSy hWt
  have hW2 : IsPGroup 2 ↥(Sy ⊓ Wt) := hSy.isPGroup.to_inf_left
  have hWK : Sy ⊓ Wt ≤ centralizer ((Sy ⊓ Wt : Subgroup G) : Set G) := fun w hw =>
    mem_centralizer_iff.mpr fun x hx => L34.comm_of_isElemAbelian hWab hx hw
  have hKC : centralizer ((Sy ⊓ Wt : Subgroup G) : Set G) ≤ centralizer (R : Set G) :=
    Subgroup.centralizer_le hRW
  obtain ⟨Q, hQ⟩ := (hW2.comap_subtype : IsPGroup 2
    ((Sy ⊓ Wt).subgroupOf (centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)))).exists_le_sylow
  have hZ'syl : IsSylowOf 2 ((Q : Subgroup (centralizer ((Sy ⊓ Wt : Subgroup G) : Set G))).map
      (centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)).subtype)
      (centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)) := ⟨Q, rfl⟩
  set Z' : Subgroup G := (Q : Subgroup (centralizer ((Sy ⊓ Wt : Subgroup G) : Set G))).map
      (centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)).subtype with hZ'def
  have hWZ' : Sy ⊓ Wt ≤ Z' := fun w hw =>
    ⟨⟨w, hWK hw⟩, hQ (mem_subgroupOf.mpr hw), rfl⟩
  have hZ'C : Z' ≤ centralizer (R : Set G) := hZ'syl.le.trans hKC
  obtain ⟨Q', hQ'⟩ := (hZ'syl.isPGroup.comap_subtype :
    IsPGroup 2 (Z'.subgroupOf (centralizer (R : Set G)))).exists_le_sylow
  have hZ''syl : IsSylowOf 2 ((Q' : Subgroup (centralizer (R : Set G))).map
      (centralizer (R : Set G)).subtype) (centralizer (R : Set G)) := ⟨Q', rfl⟩
  have hZ'Z'' : ∀ x ∈ Z', x ∈ (Q' : Subgroup (centralizer (R : Set G))).map
      (centralizer (R : Set G)).subtype := fun x hx =>
    ⟨⟨x, hZ'C hx⟩, hQ' (mem_subgroupOf.mpr hx), rfl⟩
  obtain ⟨c, -, hc⟩ := hY.exists_mem_conj hZ''syl
  have hZ'Y : ∀ x ∈ Z', c⁻¹ * x * c ∈ (Sy ⊓ Wt) ⊔ zpowers t := fun x hx =>
    (hc x).mp (hZ'Z'' x hx)
  have hB : Subgroup.map (MulAut.conj c⁻¹).toMonoidHom (Sy ⊓ Wt) = Sy ⊓ Wt := by
    apply S.eq_of_elemAbelian_card hSy hWt
    · rintro _ ⟨w, hw, rfl⟩
      have := hZ'Y w (hWZ' hw)
      simpa using this
    · exact L34.isElemAbelian_map _ hWab
    · rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, S.card_inf_Wt hSy hWt]
  have hconj1 : ∀ w ∈ Sy ⊓ Wt, c⁻¹ * w * c ∈ Sy ⊓ Wt := fun w hw => by
    have : c⁻¹ * w * c ∈ Subgroup.map (MulAut.conj c⁻¹).toMonoidHom (Sy ⊓ Wt) :=
      ⟨w, hw, by simp⟩
    rwa [hB] at this
  have hconj2 : ∀ w ∈ Sy ⊓ Wt, c * w * c⁻¹ ∈ Sy ⊓ Wt := fun w hw => by
    rw [← hB] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    have : c * (c⁻¹ * w' * c) * c⁻¹ = w' := by group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [this]
    exact hw'
  have hZ'W : Z' ≤ Sy ⊓ Wt := by
    intro z hz
    have hzK : z ∈ centralizer ((Sy ⊓ Wt : Subgroup G) : Set G) := hZ'syl.le hz
    rcases (mem_sup_zpowers_of_sq_one S.t_sq htW).mp (hZ'Y z hz) with hzW | ⟨w, hw, hzw⟩
    · have : c * (c⁻¹ * z * c) * c⁻¹ = z := by group
      rw [← this]
      exact hconj2 _ hzW
    · exfalso
      have hWR : Sy ⊓ Wt ≤ R := by
        intro y hy
        have hy' := hconj2 y hy
        have h1 : (c * y * c⁻¹) * z = z * (c * y * c⁻¹) := mem_centralizer_iff.mp hzK _ hy'
        have h2 : y * (w * t) = (w * t) * y := by
          have h3 : c⁻¹ * (c * y * c⁻¹) * c = y := by group
          calc y * (w * t) = c⁻¹ * (c * y * c⁻¹) * c * (c⁻¹ * z * c) := by rw [h3, hzw]
            _ = c⁻¹ * ((c * y * c⁻¹) * z) * c := by group
            _ = c⁻¹ * (z * (c * y * c⁻¹)) * c := by rw [h1]
            _ = (c⁻¹ * z * c) * (c⁻¹ * (c * y * c⁻¹) * c) := by group
            _ = (w * t) * y := by rw [h3, hzw]
        have h5 : y * t = t * y := by
          have hwy : y * w = w * y := L34.comm_of_isElemAbelian hWab hy hw
          have : w * (y * t) = w * (t * y) := by
            calc w * (y * t) = (w * y) * t := by rw [mul_assoc]
              _ = (y * w) * t := by rw [hwy]
              _ = y * (w * t) := by rw [mul_assoc]
              _ = (w * t) * y := h2
              _ = w * (t * y) := by rw [mul_assoc]
          exact mul_left_cancel this
        rw [← S.inf_Wt_inf_centralizer_t hSy hWt]
        exact mem_inf.mpr ⟨hy, mem_centralizer_singleton_iff.mpr h5⟩
      have h6 := Subgroup.card_le_of_le hWR
      rw [S.card_inf_Wt hSy hWt, S.W_card] at h6
      omega
  have hZ'eq : Z' = Sy ⊓ Wt := le_antisymm hZ'W hWZ'
  rw [hZ'eq] at hZ'syl
  exact hZ'syl

omit hWt in
theorem centralizes_of_mem_O_normalizer {o : G} (ho : o ∈ O)
    (hoN : o ∈ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G)) :
    o ∈ centralizer ((Sy ⊓ Wt : Subgroup G) : Set G) := by
  rw [mem_centralizer_iff]
  intro w hw
  have h1 : o * w * o⁻¹ ∈ Sy ⊓ Wt := (mem_normalizer_iff.mp hoN w).mp hw
  have h2 : w * o * w⁻¹ ∈ O := S.O_norm w (hSy.le (mem_inf.mp hw).1) o ho
  have h3 : o * w * o⁻¹ * w⁻¹ ∈ Sy ⊓ Wt := (Sy ⊓ Wt).mul_mem h1 ((Sy ⊓ Wt).inv_mem hw)
  have h4 : o * w * o⁻¹ * w⁻¹ ∈ O := by
    have : o * w * o⁻¹ * w⁻¹ = o * (w * o * w⁻¹)⁻¹ := by group
    rw [this]
    exact O.mul_mem ho (O.inv_mem h2)
  have h5 : o * w * o⁻¹ * w⁻¹ = 1 :=
    Subgroup.disjoint_def.mp (S.disjoint_O_inf_Wt hSy) h4 h3
  have h6 : o * w = w * o :=
    commutatorElement_eq_one_iff_mul_comm.mp (by rw [commutatorElement_def]; exact h5)
  exact h6.symm

theorem sup_O_inf_Wt : O ⊔ (Sy ⊓ Wt) = Wt := by
  have hle : O ⊔ (Sy ⊓ Wt) ≤ Wt := sup_le hWt.O_le inf_le_right
  have hnorm : (Sy ⊓ Wt) ≤ normalizer (O : Set G) := fun x hx =>
    Subgroup.mem_normalizer_fintype fun o ho =>
      S.O_norm x (hSy.le (Subgroup.mem_inf.mp hx).1) o ho
  have hcard : Nat.card ↥(O ⊔ (Sy ⊓ Wt)) = Nat.card O * 2 ^ 8 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer O (Sy ⊓ Wt) hnorm
      (S.disjoint_O_inf_Wt hSy), S.card_inf_Wt hSy hWt]
  exact eq_of_le_of_card_ge hle (by rw [hcard, hWt.card])

theorem not_two_dvd_relIndex_centralizer_W :
    ¬ 2 ∣ (Sy ⊓ Wt).relIndex (centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isSylowOf_iff.mp (S.isSylowOf_centralizer_W hSy hWt)).2.2

end Wt

end IsSetting25

end CFSG.OddStandard.Seitz77
