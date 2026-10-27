module

public import CFSG.GH74.GLS.Stage4.HexCNBru
public import CFSG.GH74.GLS.Stage4.HexCLocal
public import CFSG.GH74.GLS.Stage4.HexCNondeg
public import CFSG.GH74.GLS.Stage4.HexCNondeg2
public import CFSG.GH74.GLS.Stage4.HexCD4Nondeg
public import CFSG.GH74.GLS.Stage4.LocalCor97

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4 CFSG.LieType.Steinberg
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G}

theorem exists_ne_one_root (R : RGD2 6 H r₁ r₂ U root) {k : ℤ} (hk1 : 1 ≤ k) (hk6 : k ≤ 6) :
    ∃ x ∈ root k, x ≠ 1 := by
  have h := R.ne_bot k (isRoot_of_pos_le hk1 hk6)
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h
  exact ⟨x, hx, fun h' => hx1 (Subtype.ext h')⟩

theorem nondegG2_of_rgd2 (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 1)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a) :
    NondegG2 root := by
  intro hall
  obtain ⟨x, hx, hx1⟩ := exists_ne_one_root R (k := 6) (by norm_num) le_rfl
  obtain ⟨a, ha, ha1⟩ := exists_ne_one_root R (k := 1) le_rfl (by norm_num)
  refine bru_comm16_not_mem_V35 R E hO ha ha1 hx hx1 ?_
  have h := hall x hx a ha
  have hle : root 3 ⊔ root 4 ⊔ root 5 ≤ Vsub root 3 5 :=
    sup_le (sup_le (root_le_Vsub (by norm_num) (by norm_num))
      (root_le_Vsub (by norm_num) (by norm_num))) (root_le_Vsub (by norm_num) (by norm_num))
  have e : ⁅a, x⁆ = ⁅x, a⁆⁻¹ := (commutatorElement_inv x a).symm
  rw [e]
  exact (Vsub root 3 5).inv_mem (hle h)

theorem nondegX15_of_rgd2 (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 1)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a) :
    NondegX15 root := by
  intro x hx y hy hxy
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  by_cases hy1 : y = 1
  · exact Or.inr hy1
  exact (bru_comm15_ne_one R E hO hx hx1 hy hy1 hxy).elim


theorem root1_norm_Vsub35
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a)
    (hY3 : ∀ v ∈ root 3, ∀ x ∈ root 1, ⁅x, v⁆ = 1)
    (hY5 : ∀ a ∈ root 1, ∀ t ∈ root 5, ⁅a, t⁆ ∈ Vsub root 3 5) {a : G} (ha : a ∈ root 1) {v : G}
    (hv : v ∈ Vsub root 3 5) : a * v * a⁻¹ ∈ Vsub root 3 5 := by
  refine conj_mem_of_forall_mem (P := {m | m ∈ intList 3 5}) (X := root)
    (M := Vsub root 3 5) (fun m hm y hy => ?_) hv
  have hm' := mem_intList_iff.1 hm
  have hm3 : m = 3 ∨ m = 4 ∨ m = 5 := by omega
  rcases hm3 with rfl | rfl | rfl
  · have h := commutatorElement_eq_one_iff_mul_comm.1 (hY3 y hy a ha)
    have : a * y * a⁻¹ = y := by rw [mul_inv_eq_iff_eq_mul]; exact h
    rw [this]; exact root_le_Vsub (by norm_num) (by norm_num) hy
  · have h := hO a (Subgroup.mem_sup_left ha) y (Subgroup.mem_sup_left hy)
    have : a * y * a⁻¹ = y := by rw [mul_inv_eq_iff_eq_mul]; exact h
    rw [this]; exact root_le_Vsub (by norm_num) (by norm_num) hy
  · have e : a * y * a⁻¹ = ⁅a, y⁆ * y := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact Subgroup.mul_mem _ (hY5 a ha y hy) (root_le_Vsub (by norm_num) (by norm_num) hy)

theorem card_root1_le_root2 [Finite G] (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 1)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a)
    (hY3 : ∀ v ∈ root 3, ∀ x ∈ root 1, ⁅x, v⁆ = 1)
    (hY5 : ∀ a ∈ root 1, ∀ t ∈ root 5, ⁅a, t⁆ ∈ Vsub root 3 5) {x₀ : G} (hx₀ : x₀ ∈ root 6)
    (hx₀1 : x₀ ≠ 1) : Nat.card (root 1) ≤ Nat.card (root 2) := by
  obtain ⟨c, hc⟩ := exists_comp2 R
  have hcomm : ∀ a ∈ root 1, ⁅a, x₀⁆ ∈ Vsub root 2 5 := by
    intro a ha
    have h := (rgd2_octComm R) 1 6 (by norm_num) (by norm_num) (by norm_num) a ha x₀ hx₀
    refine (iSup₂_le (fun k hk => ?_) : (⨆ c ∈ Set.Ioo (1 : ℤ) 6, root c) ≤ Vsub root 2 5) h
    have hk' := Set.mem_Ioo.1 hk
    exact root_le_Vsub (by omega) (by omega)
  let ε : root 1 → root 2 := fun a => ⟨c ⁅a.1, x₀⁆, (hc _ (hcomm a.1 a.2)).1⟩
  have hinj : Function.Injective ε := by
    intro a a' h
    have hceq : c ⁅a.1, x₀⁆ = c ⁅a'.1, x₀⁆ := congrArg Subtype.val h
    have hwa := hc _ (hcomm a.1 a.2)
    have hwa' := hc _ (hcomm a'.1 a'.2)
    rw [← hceq] at hwa'
    set c₀ := c ⁅a.1, x₀⁆ with hc₀
    have hv := hwa.2
    have hv' := hwa'.2
    have hm : ⁅a.1, x₀⁆⁻¹ * ⁅a'.1, x₀⁆ ∈ Vsub root 3 5 := by
      have e : ⁅a.1, x₀⁆⁻¹ * ⁅a'.1, x₀⁆ = (c₀⁻¹ * ⁅a.1, x₀⁆)⁻¹ * (c₀⁻¹ * ⁅a'.1, x₀⁆) := by group
      rw [e]
      exact Subgroup.mul_mem _ ((Vsub root 3 5).inv_mem hv) hv'
    have hm2 : ⁅a'.1, x₀⁆ * ⁅a.1, x₀⁆⁻¹ ∈ Vsub root 3 5 := by
      have e : ⁅a'.1, x₀⁆ * ⁅a.1, x₀⁆⁻¹ =
          c₀ * ((c₀⁻¹ * ⁅a'.1, x₀⁆) * (c₀⁻¹ * ⁅a.1, x₀⁆)⁻¹) * c₀⁻¹ := by
        group
      rw [e]
      exact Vsub_norm_left R (i := 3) (j := 5) (by norm_num) (by norm_num)
        (by simpa using hwa.1) (Subgroup.mul_mem _ hv' ((Vsub root 3 5).inv_mem hv))
    have hmem : ⁅a.1⁻¹ * a'.1, x₀⁆ ∈ Vsub root 3 5 := by
      have e : ⁅a.1⁻¹ * a'.1, x₀⁆ = a.1⁻¹ * (⁅a'.1, x₀⁆ * ⁅a.1, x₀⁆⁻¹) * a.1⁻¹⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact root1_norm_Vsub35 hO hY3 hY5 ((root 1).inv_mem a.2) hm2
    by_contra hne
    have hne' : a.1⁻¹ * a'.1 ≠ 1 := by
      intro h1
      apply hne
      apply Subtype.ext
      have : a.1 = a'.1 := by
        have := congrArg (fun y => a.1 * y) h1
        simpa using this.symm
      exact this
    exact bru_comm16_not_mem_V35 R E hO ((root 1).mul_mem ((root 1).inv_mem a.2) a'.2) hne'
      hx₀ hx₀1 hmem
  exact Nat.card_le_card_of_injective ε hinj


theorem root3_comm_root1 [Finite G] {p : ℕ} (D : Cor97 p H r₁ r₂ U root) {u : G} (hu : u ∈ root 3)
    (hu1 : u ≠ 1) (hcomm : ∀ x ∈ root 1, ⁅x, u⁆ = 1) :
    ∀ v ∈ root 3, ∀ x ∈ root 1, ⁅x, v⁆ = 1 := by
  classical
  have R := D.toRGD2
  set Z : Subgroup G := root 3 ⊓ Subgroup.centralizer (root 1 : Set G) with hZ
  have hZU : Z ≤ U := le_trans inf_le_left (R.root_le_U (by norm_num) (by norm_num))
  have hZH : ∀ h ∈ H, ∀ z ∈ Z, h * z * h⁻¹ ∈ Z := by
    intro h hh z hz
    refine ⟨D.invariant 3 (isRoot_of_pos_le (by norm_num) (by norm_num)) h hh z hz.1, ?_⟩
    show h * z * h⁻¹ ∈ Subgroup.centralizer (root 1 : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : h⁻¹ * x * h⁻¹⁻¹ ∈ root 1 :=
      D.invariant 1 (isRoot_of_pos_le le_rfl (by norm_num)) h⁻¹ (H.inv_mem hh) x hx
    have h2 := Subgroup.mem_centralizer_iff.1 hz.2 _ hx'
    simp only [inv_inv] at h2
    calc x * (h * z * h⁻¹) = h * ((h⁻¹ * x * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * x * h)) * h⁻¹ := by rw [h2]
      _ = (h * z * h⁻¹) * x := by group
  by_cases hle : root 3 ≤ Z
  · intro v hv x hx
    have := Subgroup.mem_centralizer_iff.1 (hle hv).2 x hx
    exact commutatorElement_eq_one_iff_mul_comm.2 this
  · exfalso
    have hL := (D.L92 Z hZU hZH [] List.nodup_nil (fun i => ⟨fun h => absurd h (List.not_mem_nil),
      fun ⟨hi, hZi⟩ => ?_⟩)).1
    · have huZ : u ∈ Z := ⟨hu, Subgroup.mem_centralizer_iff.2 fun x hx =>
        commutatorElement_eq_one_iff_mul_comm.1 (hcomm x hx)⟩
      have : u ∈ (Z : Set G) := huZ
      rw [hL] at this
      exact hu1 (by simpa [chainProd] using this)
    · exfalso
      by_cases hb : root i = ⊥
      · exact D.ne_bot i hi hb
      · obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hb
        have hx1' : x ≠ 1 := fun h' => hx1 (Subtype.ext h')
        have hx3 : x ∈ root 3 := (hZi hx).1
        have := root_inter_six R hi (isRoot_of_pos_le (by norm_num) (by norm_num) : IsRoot 6 3)
          hx hx3 hx1'
        subst this
        exact hle hZi

theorem bru_comm15_inv_mem_V35 (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 1)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a)
    (hY3 : ∀ v ∈ root 3, ∀ x ∈ root 1, ⁅x, v⁆ = 1) {a t : G} (ha : a ∈ root 1) (ha1 : a ≠ 1)
    (ht : t ∈ root 5) : ⁅a⁻¹, t⁆ ∈ Vsub root 3 5 := by
  obtain ⟨b, hb, h, hh, hbru⟩ := exists_bruhat_root1 E ha ha1
  set n := E.φ (sl2W E.F) with hn
  have ht0 : h⁻¹ * t * h ∈ root 5 := by
    have := R.invariant 5 (isRoot_of_pos_le (by norm_num) (by norm_num)) h⁻¹ (H.inv_mem hh) t ht
    simpa using this
  set u₃ := n⁻¹ * (h⁻¹ * t * h) * n with hu₃def
  have hu₃ : u₃ ∈ root 3 := by
    have := weylOne_conj_inv R E hO (i := 5) (by norm_num) (by norm_num) ht0
    simpa using this
  have e0 : n * u₃ * n⁻¹ = h⁻¹ * t * h := by rw [hu₃def]; group
  have e1 : (a * b * a) * u₃ * (a * b * a)⁻¹ = t := by
    rw [bruhat_conj hbru u₃, e0]; group
  have hau : a * u₃ * a⁻¹ = u₃ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact commutatorElement_eq_one_iff_mul_comm.1 (hY3 u₃ hu₃ a ha)
  have e2 : a * (b * u₃ * b⁻¹) * a⁻¹ = t := by
    calc a * (b * u₃ * b⁻¹) * a⁻¹ = a * (b * (a * u₃ * a⁻¹) * b⁻¹) * a⁻¹ := by rw [hau]
      _ = (a * b * a) * u₃ * (a * b * a)⁻¹ := by group
      _ = t := e1
  have e3 : a⁻¹ * t * a = b * u₃ * b⁻¹ := by
    calc a⁻¹ * t * a = a⁻¹ * (a * (b * u₃ * b⁻¹) * a⁻¹) * a := by rw [e2]
      _ = b * u₃ * b⁻¹ := by group
  have h36 : b * u₃ * b⁻¹ ∈ Vsub root 3 6 :=
    Vsub_norm_negOne R (k := 3) (by norm_num) (by norm_num) hb
      (root_le_Vsub (by norm_num) (by norm_num) hu₃)
  have hc : ⁅a⁻¹, t⁆ ∈ Vsub root 2 4 := by
    have h := (rgd2_octComm R) 1 5 (by norm_num) (by norm_num) (by norm_num) a⁻¹
      ((root 1).inv_mem ha) t ht
    refine (iSup₂_le (fun k hk => ?_) : (⨆ c ∈ Set.Ioo (1 : ℤ) 5, root c) ≤ Vsub root 2 4) h
    have hk' := Set.mem_Ioo.1 hk
    exact root_le_Vsub (by omega) (by omega)
  have hz : ⁅a⁻¹, t⁆ ∈ Vsub root 3 6 := by
    have e : ⁅a⁻¹, t⁆ = (a⁻¹ * t * a) * t⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [e, e3]
    exact Subgroup.mul_mem _ h36 ((Vsub root 3 6).inv_mem
      (root_le_Vsub (by norm_num) (by norm_num) ht))
  exact Vsub_mono (by norm_num) (by norm_num) (mem_Vsub34_of_mem_Vsub24_Vsub36 R hc hz)

theorem bru_comm15_mem_V35 (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 1)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a)
    (hY3 : ∀ v ∈ root 3, ∀ x ∈ root 1, ⁅x, v⁆ = 1) :
    ∀ a ∈ root 1, ∀ t ∈ root 5, ⁅a, t⁆ ∈ Vsub root 3 5 := by
  intro a ha t ht
  by_cases ha1 : a = 1
  · subst ha1
    have : ⁅(1 : G), t⁆ = 1 := by simp [commutatorElement_def]
    rw [this]
    exact (Vsub root 3 5).one_mem
  · have := bru_comm15_inv_mem_V35 R E hO hY3 ((root 1).inv_mem ha) (by simpa using ha1) ht
    simpa using this

theorem nondegD4X13_of_cor97 [Finite G] {p q : ℕ} (D : Cor97 p H r₁ r₂ U root)
    (E : SL2Pos H D.toRGD2.N root 1)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a) (hq3 : 3 ≤ q)
    (hord : RootOrdersD4a root q) : NondegD4X13 root := by
  intro u hu hcomm
  by_contra hu1
  have hY3 := root3_comm_root1 D hu hu1 hcomm
  have hY5 := bru_comm15_mem_V35 D.toRGD2 E hO hY3
  obtain ⟨x₀, hx₀, hx₀1⟩ := exists_ne_one_root D.toRGD2 (k := 6) (by norm_num) le_rfl
  have hle := card_root1_le_root2 D.toRGD2 E hO hY3 hY5 hx₀ hx₀1
  rw [hord 1 le_rfl (by norm_num), hord 2 (by norm_num) (by norm_num)] at hle
  have h1 : (1 : ℤ) % 2 = 1 := by norm_num
  have h2 : ¬ ((2 : ℤ) % 2 = 1) := by norm_num
  simp only [h1, h2, ite_true, ite_false] at hle
  have : q < q ^ 3 := by
    calc q = q ^ 1 := (pow_one q).symm
      _ < q ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega


end CFSG.GH74.GLS.Stage4.Hex
