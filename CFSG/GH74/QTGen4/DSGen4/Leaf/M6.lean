module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyNorm
public import CFSG.GH74.QTGen4.DSGen4.Leaf.M6Quad
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5Classify
public import CFSG.GH74.QTGen4.DSGen4.OpenLeaves

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open Certificates.A5GL42 (Mat4 Vec4 HO OrthForms Qab ThirdDiff NonAdd vecOfCode O1 O2)
open scoped commutatorElement Matrix

section Core

variable {W : Type*} [Group W] [Finite W]

theorem zmod2_eq_of_iff {a b : ZMod 2} (h : a = 0 ↔ b = 0) : a = b := by
  revert a b; decide

theorem m6_core {Zw : Subgroup W} (hZ2 : Nat.card Zw = 2) (hcomm : ∀ x y : W, ⁅x, y⁆ ∈ Zw)
    (hsq : ∀ x : W, x ^ 2 ∈ Zw) (hcent : ∀ z ∈ Zw, ∀ w : W, z * w = w * z)
    (hnab : ∃ x y : W, ⁅x, y⁆ ≠ 1) (φ : W →* Multiplicative Vec4)
    (hsurj : Function.Surjective φ) (hker : ∀ e : W, φ e = 1 ↔ e ∈ Zw)
    (hinv : ∀ m ∈ HO, ∀ x : W, ∃ x' : W,
      Multiplicative.toAdd (φ x') = m *ᵥ Multiplicative.toAdd (φ x) ∧ (x' ^ 2 = 1 ↔ x ^ 2 = 1))
    (hO : OrthForms) : Nat.card {x : W | x ^ 2 = 1} = 12 := by
  classical
  choose lift hlift using fun u : Vec4 => hsurj (Multiplicative.ofAdd u)
  have hlift' : ∀ u : Vec4, Multiplicative.toAdd (φ (lift u)) = u := fun u => by
    rw [hlift u]; rfl
  have hsqb_eq : ∀ x x' : W, φ x = φ x' → sqb x = sqb x' := by
    intro x x' hxx'
    have hz : x⁻¹ * x' ∈ Zw := by
      rw [← hker, map_mul, map_inv, hxx']
      exact inv_mul_cancel _
    have hx' : x' = x * (x⁻¹ * x') := by group
    have hz2 : (x⁻¹ * x') ^ 2 = 1 := by
      rw [pow_two]; exact mul_self_eq_one_of_card_two hZ2 hz
    have hcb : cb x (x⁻¹ * x') = 0 := by
      unfold cb
      rw [bit_eq_zero_iff, commutatorElement_eq_one_iff_mul_comm]
      exact (hcent _ hz x).symm
    have hsb : sqb (x⁻¹ * x') = 0 := by
      unfold sqb; rw [hz2]; exact bit_one
    rw [hx', sqb_mul hZ2 hcomm hsq hcent, hcb, hsb]
    simp
  let Qf : Vec4 → ZMod 2 := fun u => sqb (lift u)
  have hQf : ∀ x : W, Qf (Multiplicative.toAdd (φ x)) = sqb x := by
    intro x
    apply hsqb_eq
    rw [hlift]; rfl
  have hQ0 : Qf 0 = 0 := by
    have := hQf 1
    rw [map_one, toAdd_one] at this
    rw [this]
    unfold sqb
    rw [one_pow]; exact bit_one
  have hQ3 : ThirdDiff Qf := by
    intro u v w
    have e := sqb_third_diff hZ2 hcomm hsq hcent (lift u) (lift v) (lift w)
    have eu := hlift' u
    have ev := hlift' v
    have ew := hlift' w
    have a1 := hQf (lift u * lift v * lift w)
    have a2 := hQf (lift u * lift v)
    have a3 := hQf (lift u * lift w)
    have a4 := hQf (lift v * lift w)
    have a5 := hQf (lift u)
    have a6 := hQf (lift v)
    have a7 := hQf (lift w)
    simp only [map_mul, toAdd_mul, eu, ev, ew] at a1 a2 a3 a4 a5 a6 a7
    rw [a1, a2, a3, a4, a5, a6, a7]
    exact e
  have hQinv : ∀ m ∈ HO, ∀ u : Vec4, Qf (m *ᵥ u) = Qf u := by
    intro m hm u
    obtain ⟨x', hx'1, hx'2⟩ := hinv m hm (lift u)
    rw [hlift' u] at hx'1
    rw [← hx'1, hQf x']
    show sqb x' = sqb (lift u)
    unfold sqb
    apply zmod2_eq_of_iff
    rw [bit_eq_zero_iff, bit_eq_zero_iff]
    exact hx'2
  have hQnon : NonAdd Qf := by
    by_contra hna
    unfold NonAdd at hna
    push Not at hna
    obtain ⟨x, y, hxy⟩ := hnab
    apply hxy
    have h1 := sqb_mul hZ2 hcomm hsq hcent x y
    have h2 := hna (Multiplicative.toAdd (φ x)) (Multiplicative.toAdd (φ y))
    rw [← toAdd_mul, ← map_mul, hQf, hQf, hQf, h1] at h2
    have h3 : cb x y = 0 := by
      have : sqb x + sqb y + cb x y = sqb x + sqb y + 0 := by rw [add_zero]; exact h2
      exact add_left_cancel this
    exact bit_eq_zero_iff.mp h3
  have hfun : Qf = Qab (Qf (vecOfCode 1)) (Qf (vecOfCode 7)) := by
    funext v
    rcases hO.cover v with h0 | h1 | h2
    · subst h0
      rw [hQ0]
      unfold Qab
      rw [if_neg hO.zero_o1, if_neg hO.zero_o2]
    · obtain ⟨m, hm, hmv⟩ := hO.trans1 v h1
      rw [← hmv, hQinv m hm]
      unfold Qab
      rw [if_pos (hmv ▸ h1)]
    · obtain ⟨m, hm, hmv⟩ := hO.trans2 v h2
      have hn1 : v ∉ O1 := fun h => hO.disj v h h2
      rw [← hmv, hQinv m hm]
      unfold Qab
      rw [if_neg (hmv ▸ hn1), if_pos (hmv ▸ h2)]
  have hab := hO.unique _ _ (hfun ▸ hQ3) (hfun ▸ hQnon)
  have hfun2 : Qf = Qab 1 0 := by rw [hfun, hab.1, hab.2]
  have hcard6 : (Finset.univ.filter fun v : Vec4 => Qf v = 0).card = 6 := by
    rw [hfun2]; exact hO.count
  haveI : Fintype W := Fintype.ofFinite W
  have hfiber : ∀ b : Vec4,
      (Finset.univ.filter fun x : W => Multiplicative.toAdd (φ x) = b).card = 2 := by
    intro b
    let e : {x : W // Multiplicative.toAdd (φ x) = b} ≃ Zw :=
      { toFun := fun x => ⟨(lift b)⁻¹ * x.1, by
          rw [← hker, map_mul, map_inv]
          have h1 : φ x.1 = φ (lift b) := by
            rw [hlift b]; exact Multiplicative.toAdd.injective (by simpa using x.2)
          rw [h1]
          exact inv_mul_cancel _⟩
        invFun := fun z => ⟨lift b * z.1, by
          have := (hker z.1).mpr z.2
          rw [map_mul, this, mul_one]; exact hlift' b⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun z => Subtype.ext (by simp) }
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Nat.card_congr e, hZ2]
  have hS : Nat.card {x : W | x ^ 2 = 1} =
      (Finset.univ.filter fun x : W => x ^ 2 = 1).card := by
    rw [Nat.card_eq_fintype_card]
    simp [Fintype.card_subtype]
  rw [hS, Finset.card_eq_sum_card_fiberwise (f := fun x : W => Multiplicative.toAdd (φ x))
    (t := Finset.univ.filter fun v : Vec4 => Qf v = 0)]
  · have hterm : ∀ b ∈ Finset.univ.filter (fun v : Vec4 => Qf v = 0),
        ((Finset.univ.filter fun x : W => x ^ 2 = 1).filter
          fun x => Multiplicative.toAdd (φ x) = b).card = 2 := by
      intro b hb
      refine Eq.trans ?_ (hfiber b)
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro hx
        refine ⟨?_, hx⟩
        have hb0 : Qf b = 0 := by simpa using hb
        rw [← hx, hQf] at hb0
        exact (bit_eq_zero_iff.mp hb0)
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, hcard6]
    simp
  · intro x hx
    rw [Finset.mem_coe] at hx ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hQf]
    unfold sqb
    rw [hx]
    exact bit_one

end Core

theorem leafM6 : LeafM6 := by
  intro G _ _ P L V Z h hn hZ hV
  have hpre := h.toPre
  have hF := a5Facts
  have hF2 := a5Facts2
  rcases hpre.exists_model hF with ⟨hnat, _⟩ | ⟨_, ⟨M⟩⟩
  · exact absurd hnat hn
  have hZV : Z ≤ V := h.sec.1
  have hZ2 : Nat.card (Z.subgroupOf V) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv]; exact hZ
  refine m6_core (W := ↥V) (Zw := Z.subgroupOf V) hZ2 ?_ ?_ ?_ ?_ M.F.φ M.F.surj ?_ ?_ hF2.forms
  · intro x y
    rw [Subgroup.mem_subgroupOf]
    have : ((⁅x, y⁆ : ↥V) : G) = ⁅(x : G), (y : G)⁆ := by simp [commutatorElement_def]
    rw [this]
    exact h.sec.2.1 (Subgroup.commutator_mem_commutator x.2 y.2)
  · intro x
    rw [Subgroup.mem_subgroupOf]
    have : (((x ^ 2 : ↥V)) : G) = (x : G) ^ 2 := by simp
    rw [this]
    exact h.sec.2.2 x x.2
  · intro z hz w
    rw [Subgroup.mem_subgroupOf] at hz
    have hw : (w : G) * (z : G) * (w : G)⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (h.norm_K (h.E_le w.2)) (z : G)).mp hz
    have := comm_of_card_two hZ hz (w : G) hw
    exact Subtype.ext this.symm
  · by_contra hcon
    push Not at hcon
    apply hV
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    have := hcon ⟨a, ha⟩ ⟨b, hb⟩
    have h1 : ((⁅(⟨a, ha⟩ : ↥V), (⟨b, hb⟩ : ↥V)⁆ : ↥V) : G) = ⁅a, b⁆ := by
      simp [commutatorElement_def]
    rw [this] at h1
    simpa using h1.symm
  · intro e
    rw [M.F.ker e, Subgroup.mem_subgroupOf]
  · intro m hm x
    obtain ⟨l, hlL, hlm⟩ := M.surjL m hm
    refine ⟨conjE h.norm_E l x, ?_, ?_⟩
    · have := M.F.act l x (conjE h.norm_E l x) (coe_conjE h.norm_E l x)
      rw [hlm] at this
      exact this.symm
    · rw [← map_pow]
      exact EmbeddingLike.map_eq_one_iff

end CFSG.GH74.QTGen4.DSGen4
