module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step110Conf

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

section Helpers

variable {K : Type} [Group K]

theorem mem_centralizer_sup {A B : Subgroup K} {y : K} (hA : y ∈ centralizer (A : Set K))
    (hB : y ∈ centralizer (B : Set K)) : y ∈ centralizer ((A ⊔ B : Subgroup K) : Set K) := by
  have h : A ⊔ B ≤ centralizer ({y} : Set K) := sup_le
    (fun a ha => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hA a ha))
    (fun b hb => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hB b hb))
  exact mem_centralizer_iff.mpr fun w hw => mem_centralizer_singleton_iff.mp (h hw)

theorem commutator_mem_of_mem {H : Subgroup K} {a b : K} (ha : a ∈ H) (hb : b ∈ H) :
    a * b * a⁻¹ * b⁻¹ ∈ H :=
  H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem commute_of_mem_centralizer_singleton {i y c : K} (hy : y ∈ centralizer ({i} : Set K))
    (hc : c ∈ zpowers i) : y * c = c * y := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
  exact ((Commute.zpow_right (show Commute y i from mem_centralizer_singleton_iff.mp hy) k)).eq

theorem mem_comap_centralizer_barMap {z : K} [(zpowers z).Normal] {x d : K} :
    x ∈ (centralizer ({barMap z d} : Set (K ⧸ zpowers z))).comap (barMap z) ↔
      x * d * x⁻¹ * d⁻¹ ∈ zpowers z := by
  have key : barMap z (x * d * x⁻¹ * d⁻¹) = 1 ↔ x * d * x⁻¹ * d⁻¹ ∈ zpowers z := by
    rw [← MonoidHom.mem_ker, ker_barMap]
  rw [← key, mem_comap, mem_centralizer_singleton_iff, map_mul, map_mul, map_mul, map_inv,
    map_inv]
  constructor
  · intro h
    rw [h]
    group
  · intro h
    calc barMap z x * barMap z d
        = (barMap z x * barMap z d * (barMap z x)⁻¹ * (barMap z d)⁻¹) *
            (barMap z d * barMap z x) := by group
      _ = barMap z d * barMap z x := by rw [h, one_mul]

theorem relIndex_inf_eq_two [Finite K] {X B C : Subgroup K} (hBX : B ≤ X)
    (hB : 2 * Nat.card B = Nat.card X) (hYB : ¬ X ⊓ C ≤ B) :
    (B ⊓ C).relIndex (X ⊓ C) = 2 ∧ 2 * Nat.card (B ⊓ C : Subgroup K) = Nat.card (X ⊓ C : Subgroup K) := by
  have hsub : (B ⊓ C).subgroupOf (X ⊓ C) = B.subgroupOf (X ⊓ C) := by
    ext ⟨y, hy⟩
    simp only [mem_subgroupOf, mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, hy.2⟩⟩
  have hrel : (B ⊓ C).relIndex (X ⊓ C) = B.relIndex (X ⊓ C) := by
    rw [relIndex, relIndex, hsub]
  have hBX2 : B.relIndex X = 2 := by
    have h := relIndex_mul_card B X
    rw [inf_eq_left.mpr hBX] at h
    have hpos : 0 < Nat.card B := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h.trans hB.symm)
  have hle : B.relIndex (X ⊓ C) ≤ 2 :=
    hBX2 ▸ relIndex_le_of_le_right inf_le_left (by rw [hBX2]; norm_num)
  have hne1 : B.relIndex (X ⊓ C) ≠ 1 := fun h => hYB (relIndex_eq_one.mp h)
  have hne0 : B.relIndex (X ⊓ C) ≠ 0 := by
    intro h0
    have h := relIndex_mul_card B (X ⊓ C)
    rw [h0, zero_mul] at h
    exact (Nat.card_pos (α := ↥(X ⊓ C))).ne h
  have h2 : (B ⊓ C).relIndex (X ⊓ C) = 2 := by omega
  refine ⟨h2, ?_⟩
  have h := relIndex_mul_card (B ⊓ C) (X ⊓ C)
  rw [h2, inf_eq_left.mpr (inf_le_inf_right C hBX)] at h
  exact h

end Helpers

section Dih

variable {K : Type} [Group K] [Finite K] {z : K} {X : Subgroup K} {g : K}

namespace Conf110

variable (hc : Conf110 z X g)
include hc

omit [Finite K] in
theorem card_zpowers_z : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hc.extra.order]

theorem card_D_le_of_Z2 (hI : tim77I X g ≤ zpowers z)
    (hB : 2 * Nat.card (tim77B X g) = Nat.card X) : Nat.card (tim77D X g) ≤ 4 := by
  have hBX : tim77B X g ≤ X := inf_le_left
  have hidx : (tim77B X g).relIndex X = 2 := by
    have h := relIndex_mul_card (tim77B X g) X
    rw [inf_eq_left.mpr hBX] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h.trans hB.symm)
  have hC4 : Nat.card (X ⊓ centralizer (tim77B X g : Set K) : Subgroup K) ≤
      2 * Nat.card (zpowers z) := by
    have h := hc.extra.card_centralizer hBX hc.z_mem_B
    rw [hc.card_zpowers_z]
    have hpos : 0 < Nat.card (tim77B X g) := Nat.card_pos
    have h2 : Nat.card (X ⊓ centralizer (tim77B X g : Set K) : Subgroup K) *
        Nat.card (tim77B X g) = 4 * Nat.card (tim77B X g) := by linarith
    have h3 := Nat.eq_of_mul_eq_mul_right hpos h2
    omega
  have h := card_le_two_mul_of_transvection hBX (zpowers_le.mpr hc.z_mem_B) hidx
    (fun c hc' y _ => hc.commute_of_mem_zpowers hc' y)
    (fun a ha b hb => hc.extra.commutator_mem ha hb) hC4
    (fun d _ c hc' => hc.conj_of_mem_zpowers hc' d)
    (fun d hd y hy => hc.comm_X_D hy hd)
    (fun d hd u hu => hI (comm_tim77B_tim77D hu hd)) (tim77I X g)
    (fun d hd h => hc.mem_I_of_comm hd h)
  have h2 : Nat.card (tim77D X g ⊓ tim77I X g : Subgroup K) ≤ 2 := by
    have := card_le_of_le (inf_le_right.trans hI : tim77D X g ⊓ tim77I X g ≤ zpowers z)
    rwa [hc.card_zpowers_z] at this
  omega

theorem comm_mem_centralizer {i d x : K} (hiX : i ∈ X) (hdi : d * i = i * d) (hx : x ∈ X) :
    x * d * x⁻¹ * d⁻¹ ∈ centralizer ({i} : Set K) := by
  have he : x⁻¹ * i * x * i⁻¹ ∈ zpowers z := by
    have := hc.extra.commutator_mem (X.inv_mem hx) hiX
    simpa using this
  have h1 : d * (x⁻¹ * i * x * i⁻¹) * d⁻¹ = x⁻¹ * i * x * i⁻¹ := hc.conj_of_mem_zpowers he d
  have hdi1 : d⁻¹ * i * d = i := by
    calc d⁻¹ * i * d = d⁻¹ * (i * d) := by group
      _ = d⁻¹ * (d * i) := by rw [hdi]
      _ = i := by group
  have hdi2 : d * i * d⁻¹ = i := by rw [hdi, mul_inv_cancel_right]
  have key : (x * d * x⁻¹ * d⁻¹) * i * (x * d * x⁻¹ * d⁻¹)⁻¹ = i := by
    calc (x * d * x⁻¹ * d⁻¹) * i * (x * d * x⁻¹ * d⁻¹)⁻¹
        = x * d * x⁻¹ * (d⁻¹ * i * d) * x * d⁻¹ * x⁻¹ := by group
      _ = x * d * x⁻¹ * i * x * d⁻¹ * x⁻¹ := by rw [hdi1]
      _ = x * (d * (x⁻¹ * i * x * i⁻¹) * d⁻¹) * (d * i * d⁻¹) * x⁻¹ := by group
      _ = x * (x⁻¹ * i * x * i⁻¹) * i * x⁻¹ := by rw [h1, hdi2]
      _ = i := by group
  rw [mem_centralizer_singleton_iff]
  calc (x * d * x⁻¹ * d⁻¹) * i
      = (x * d * x⁻¹ * d⁻¹) * i * (x * d * x⁻¹ * d⁻¹)⁻¹ * (x * d * x⁻¹ * d⁻¹) := by group
    _ = i * (x * d * x⁻¹ * d⁻¹) := by rw [key]

omit [Finite K] in
theorem not_mem_of_Z4 {i : K} (hii : i * i = z) : i ∉ zpowers z := fun h => by
  rcases (ExtraIn.mem_zpowers_iff_of_order hc.extra.order).mp h with h3 | h3
  · rw [h3, one_mul] at hii
    exact hc.z_ne_one hii.symm
  · rw [h3, hc.z_mul_self] at hii
    exact hc.z_ne_one hii.symm

theorem card_I_of_Z4 {i : K} (hiI : i ∈ tim77I X g) (hii : i * i = z)
    (hIi : tim77I X g = zpowers i) : Nat.card (tim77I X g) = 4 := by
  rw [hIi, Nat.card_zpowers, hc.orderOf_eq_four hiI (hc.not_mem_of_Z4 hii)]

theorem card_centralizer_of_Z4 {i : K} (hiI : i ∈ tim77I X g) (hii : i * i = z)
    (hIi : tim77I X g = zpowers i) :
    2 * Nat.card (X ⊓ centralizer ({i} : Set K) : Subgroup K) = Nat.card X := by
  have h : Nat.card (X ⊓ centralizer (tim77I X g : Set K) : Subgroup K) *
      Nat.card (tim77I X g) = 2 * Nat.card X :=
    hc.extra.card_centralizer (inf_le_left : tim77I X g ≤ X) hc.z_mem_I
  rw [hc.card_I_of_Z4 hiI hii hIi] at h
  rw [hIi, zpowers_eq_closure, centralizer_closure] at h
  omega

theorem exists_D₁_of_Z4 {i : K} (hiI : i ∈ tim77I X g) (hii : i * i = z)
    (hIi : tim77I X g = zpowers i) (hB : 2 * Nat.card (tim77B X g) = Nat.card X) :
    ∃ D₁ : Subgroup K, D₁ ≤ tim77D X g ⊓ centralizer ({i} : Set K) ∧
      Nat.card (tim77D X g ⊓ centralizer ({i} : Set K) : Subgroup K) ≤ 2 * Nat.card D₁ ∧
      ∀ d ∈ D₁, ∀ y ∈ X ⊓ centralizer ({i} : Set K), y * d * y⁻¹ * d⁻¹ ∈ tim77I X g := by
  have hBX : tim77B X g ≤ X := inf_le_left
  by_cases hYB : X ⊓ centralizer ({i} : Set K) ≤ tim77B X g
  · exact ⟨_, le_rfl, by omega, fun d hd y hy =>
      comm_tim77B_tim77D (hYB hy) (mem_inf.mp hd).1⟩
  obtain ⟨hidx, hUcard⟩ := relIndex_inf_eq_two hBX hB hYB
  have hYcard := hc.card_centralizer_of_Z4 hiI hii hIi
  have hiC : i ∈ centralizer ({i} : Set K) := mem_centralizer_singleton_iff.mpr rfl
  have hIC : tim77I X g ≤ centralizer ({i} : Set K) := by
    rw [hIi]
    exact zpowers_le.mpr hiC
  have hzC : z ∈ centralizer ({i} : Set K) := hIC hc.z_mem_I
  have hUX : tim77B X g ⊓ centralizer ({i} : Set K) ≤ X := inf_le_left.trans hBX
  have hC4 : Nat.card ((X ⊓ centralizer ({i} : Set K)) ⊓
      centralizer ((tim77B X g ⊓ centralizer ({i} : Set K) : Subgroup K) : Set K) :
        Subgroup K) ≤ 2 * Nat.card (tim77I X g) := by
    have h := hc.extra.card_centralizer hUX ⟨hc.z_mem_B, hzC⟩
    have h1 := card_le_of_le (inf_le_inf_right (centralizer ((tim77B X g ⊓
      centralizer ({i} : Set K) : Subgroup K) : Set K))
        (inf_le_left : X ⊓ centralizer ({i} : Set K) ≤ X))
    rw [hc.card_I_of_Z4 hiI hii hIi]
    have hpos : 0 < Nat.card (tim77B X g ⊓ centralizer ({i} : Set K) : Subgroup K) :=
      Nat.card_pos
    have h2 : Nat.card (X ⊓ centralizer ((tim77B X g ⊓ centralizer ({i} : Set K) :
        Subgroup K) : Set K) : Subgroup K) *
        Nat.card (tim77B X g ⊓ centralizer ({i} : Set K) : Subgroup K) =
        8 * Nat.card (tim77B X g ⊓ centralizer ({i} : Set K) : Subgroup K) := by
      linarith
    have h3 := Nat.eq_of_mul_eq_mul_right hpos h2
    omega
  exact exists_le_of_transvection (Y := X ⊓ centralizer ({i} : Set K))
    (U := tim77B X g ⊓ centralizer ({i} : Set K)) (Z₀ := tim77I X g)
    (D' := tim77D X g ⊓ centralizer ({i} : Set K))
    (inf_le_inf_right _ hBX) (le_inf tim77I_le_tim77B hIC) hidx
    (fun c hc' y hy => commute_of_mem_centralizer_singleton (mem_inf.mp hy).2 (hIi ▸ hc'))
    (fun a ha b hb => hc.zpowers_le_I
      (hc.extra.commutator_mem (mem_inf.mp ha).1 (mem_inf.mp hb).1)) hC4
    (fun d hd c hc' => by
      rw [commute_of_mem_centralizer_singleton (mem_inf.mp hd).2 (hIi ▸ hc'),
        mul_inv_cancel_right])
    (fun d hd y hy => ⟨hc.comm_X_D (mem_inf.mp hy).1 (mem_inf.mp hd).1,
      commutator_mem_of_mem (mem_inf.mp hy).2 (mem_inf.mp hd).2⟩)
    (fun d hd u hu => comm_tim77B_tim77D (mem_inf.mp hu).1 (mem_inf.mp hd).1)

theorem comm_mem_zpowers_of_Z4 {i : K} (hIi : tim77I X g = zpowers i) {d y : K}
    (hy : y ∈ X ⊓ centralizer ({i} : Set K)) (hcI : y * d * y⁻¹ * d⁻¹ ∈ tim77I X g) :
    y * d * y⁻¹ * d⁻¹ ∈ zpowers z := by
  have hyX := (mem_inf.mp hy).1
  have hyC := (mem_inf.mp hy).2
  have hcy : y⁻¹ * (y * d * y⁻¹ * d⁻¹) = (y * d * y⁻¹ * d⁻¹) * y⁻¹ :=
    commute_of_mem_centralizer_singleton ((centralizer ({i} : Set K)).inv_mem hyC) (hIi ▸ hcI)
  have he : y * y ∈ zpowers z := by
    rw [← sq]
    exact hc.extra.sq_mem hyX
  have key2 : (d * y⁻¹ * d⁻¹) * (d * y⁻¹ * d⁻¹) = (y * y)⁻¹ := by
    calc (d * y⁻¹ * d⁻¹) * (d * y⁻¹ * d⁻¹) = d * (y * y)⁻¹ * d⁻¹ := by group
      _ = (y * y)⁻¹ := hc.conj_of_mem_zpowers (inv_mem he) d
  have hdy : d * y⁻¹ * d⁻¹ = y⁻¹ * (y * d * y⁻¹ * d⁻¹) := by group
  rw [hdy] at key2
  have key3 : y⁻¹ * (y * d * y⁻¹ * d⁻¹) * (y⁻¹ * (y * d * y⁻¹ * d⁻¹)) =
      (y * y)⁻¹ * ((y * d * y⁻¹ * d⁻¹) * (y * d * y⁻¹ * d⁻¹)) := by
    calc y⁻¹ * (y * d * y⁻¹ * d⁻¹) * (y⁻¹ * (y * d * y⁻¹ * d⁻¹))
        = y⁻¹ * ((y * d * y⁻¹ * d⁻¹) * y⁻¹) * (y * d * y⁻¹ * d⁻¹) := by group
      _ = y⁻¹ * (y⁻¹ * (y * d * y⁻¹ * d⁻¹)) * (y * d * y⁻¹ * d⁻¹) := by rw [hcy]
      _ = (y * y)⁻¹ * ((y * d * y⁻¹ * d⁻¹) * (y * d * y⁻¹ * d⁻¹)) := by group
  rw [key3] at key2
  have h1 : (y * d * y⁻¹ * d⁻¹) * (y * d * y⁻¹ * d⁻¹) = 1 :=
    mul_left_cancel (key2.trans (mul_one _).symm)
  exact hc.uniq _ hcI h1

theorem card_D₁_le_of_Z4 {i : K} (hiI : i ∈ tim77I X g) (hii : i * i = z)
    (hIi : tim77I X g = zpowers i) {D₁ : Subgroup K}
    (hD₁ : D₁ ≤ tim77D X g ⊓ centralizer ({i} : Set K))
    (hD₁Y : ∀ d ∈ D₁, ∀ y ∈ X ⊓ centralizer ({i} : Set K), y * d * y⁻¹ * d⁻¹ ∈ zpowers z) :
    Nat.card D₁ ≤ 8 := by
  have hYcard := hc.card_centralizer_of_Z4 hiI hii hIi
  have hzY : z ∈ X ⊓ centralizer ({i} : Set K) :=
    ⟨hc.extra.mem, mem_centralizer_singleton_iff.mpr (hc.commute_z i).symm⟩
  have hidxY : (X ⊓ centralizer ({i} : Set K)).relIndex X = 2 := by
    have h := relIndex_mul_card (X ⊓ centralizer ({i} : Set K)) X
    rw [inf_eq_left.mpr (inf_le_left : X ⊓ centralizer ({i} : Set K) ≤ X)] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h.trans hYcard.symm)
  have hC4 : Nat.card (X ⊓ centralizer ((X ⊓ centralizer ({i} : Set K) : Subgroup K) : Set K) :
      Subgroup K) ≤ 2 * Nat.card (zpowers z) := by
    have h := hc.extra.card_centralizer (inf_le_left : X ⊓ centralizer ({i} : Set K) ≤ X) hzY
    rw [hc.card_zpowers_z]
    have hpos : 0 < Nat.card (X ⊓ centralizer ({i} : Set K) : Subgroup K) := Nat.card_pos
    have h2 : Nat.card (X ⊓ centralizer ((X ⊓ centralizer ({i} : Set K) : Subgroup K) :
        Set K) : Subgroup K) * Nat.card (X ⊓ centralizer ({i} : Set K) : Subgroup K) =
        4 * Nat.card (X ⊓ centralizer ({i} : Set K) : Subgroup K) := by linarith
    have h3 := Nat.eq_of_mul_eq_mul_right hpos h2
    omega
  have h := card_le_two_mul_of_transvection (Y := X) (U := X ⊓ centralizer ({i} : Set K))
    (Z₀ := zpowers z) (D' := D₁) inf_le_left (zpowers_le.mpr hzY) hidxY
    (fun c hc' y _ => hc.commute_of_mem_zpowers hc' y)
    (fun a ha b hb => hc.extra.commutator_mem ha hb) hC4
    (fun d _ c hc' => hc.conj_of_mem_zpowers hc' d)
    (fun d hd x hx => by
      have hdD := (mem_inf.mp (hD₁ hd)).1
      have hdC := (mem_inf.mp (hD₁ hd)).2
      refine ⟨?_, hc.comm_mem_centralizer hiI.1 (mem_centralizer_singleton_iff.mp hdC) hx⟩
      have : d * x⁻¹ * d⁻¹ ∈ X :=
        (mem_normalizer_iff.mp (mem_inf.mp hdD).2 _).mp (X.inv_mem hx)
      have h := X.mul_mem hx this
      simpa [mul_assoc] using h)
    hD₁Y (tim77I X g) (fun d hd h => hc.mem_I_of_comm (mem_inf.mp (hD₁ hd)).1 h)
  have h3 : Nat.card (D₁ ⊓ tim77I X g : Subgroup K) ≤ 4 :=
    hc.card_I_of_Z4 hiI hii hIi ▸ card_le_of_le inf_le_right
  omega

theorem card_D_le_of_Z4 {i : K} (hiI : i ∈ tim77I X g) (hii : i * i = z)
    (hIi : tim77I X g = zpowers i) (hB : 2 * Nat.card (tim77B X g) = Nat.card X) :
    Nat.card (tim77D X g) ≤ 32 := by
  have ha : Nat.card (tim77D X g) ≤
      2 * Nat.card (tim77D X g ⊓ centralizer ({i} : Set K) : Subgroup K) :=
    card_le_two_mul_inf_centralizer_of_comm hc.extra.order (fun h _ => hc.commute_z h)
      (fun d hd => hc.comm_I_D hiI hd)
  obtain ⟨D₁, hD₁, hD₁card, hD₁Y⟩ := hc.exists_D₁_of_Z4 hiI hii hIi hB
  have h := hc.card_D₁_le_of_Z4 hiI hii hIi hD₁
    fun d hd y hy => hc.comm_mem_zpowers_of_Z4 hIi hy (hD₁Y d hd y hy)
  omega

theorem card_D_le_of_Q8_gens (h8 : Nat.card (tim77I X g) = 8) :
    Nat.card (tim77D X g) ≤
      4 * Nat.card (tim77D X g ⊓ centralizer (tim77I X g : Set K) : Subgroup K) := by
  obtain ⟨a, ha, b, hb, hab⟩ := hc.exists_gens h8
  have e1 := card_le_two_mul_inf_centralizer_of_comm (H := tim77D X g) (a := a)
    hc.extra.order (fun h _ => hc.commute_z h) (fun d hd => hc.comm_I_D ha hd)
  have e2 := card_le_two_mul_inf_centralizer_of_comm
    (H := tim77D X g ⊓ centralizer ({a} : Set K)) (a := b) hc.extra.order
    (fun h _ => hc.commute_z h) (fun d hd => hc.comm_I_D hb (mem_inf.mp hd).1)
  have e3 : tim77D X g ⊓ centralizer ({a} : Set K) ⊓ centralizer ({b} : Set K) ≤
      tim77D X g ⊓ centralizer (tim77I X g : Set K) := by
    intro d hd
    obtain ⟨hd', hdb⟩ := mem_inf.mp hd
    obtain ⟨hdD, hda⟩ := mem_inf.mp hd'
    refine ⟨hdD, mem_centralizer_iff.mpr fun j hj => ?_⟩
    have hle : zpowers a ⊔ zpowers b ≤ centralizer ({d} : Set K) := sup_le
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp hda).symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp hdb).symm))
    exact mem_centralizer_singleton_iff.mp (hle (hab hj))
  have e4 := card_le_of_le e3
  omega

theorem sup_eq_of_eight (h8 : Nat.card (tim77I X g) = 8) :
    tim77I X g ⊔ (X ⊓ centralizer (tim77I X g : Set K)) = X := by
  have hle : tim77I X g ⊔ (X ⊓ centralizer (tim77I X g : Set K)) ≤ X :=
    sup_le inf_le_left inf_le_left
  have hY : Nat.card (X ⊓ centralizer (tim77I X g : Set K) : Subgroup K) *
      Nat.card (tim77I X g) = 2 * Nat.card X :=
    hc.extra.card_centralizer (inf_le_left : tim77I X g ≤ X) hc.z_mem_I
  rw [h8] at hY
  have hprod := card_sup_mul_card_inf (H := tim77I X g)
    (R := X ⊓ centralizer (tim77I X g : Set K))
    (inf_le_right.trans (centralizer_le_normalizer _))
  have hinf : tim77I X g ⊓ (X ⊓ centralizer (tim77I X g : Set K)) ≤ zpowers z := by
    intro c hc'
    obtain ⟨hcI, hcY⟩ := mem_inf.mp hc'
    exact hc.center_I_le h8 hcI fun j hj => mem_centralizer_iff.mp (mem_inf.mp hcY).2 j hj
  have hinf2 := card_le_of_le hinf
  rw [hc.card_zpowers_z] at hinf2
  rw [h8] at hprod
  refine eq_of_le_of_card_ge hle ?_
  have h1 := Nat.mul_le_mul_left (Nat.card (tim77I X g ⊔ (X ⊓ centralizer (tim77I X g : Set K)) :
    Subgroup K)) hinf2
  linarith

theorem card_centralizer_le_of_Q8 (h8 : Nat.card (tim77I X g) = 8)
    (hB : 2 * Nat.card (tim77B X g) = Nat.card X)
    (hYB : ¬ X ⊓ centralizer (tim77I X g : Set K) ≤ tim77B X g) :
    Nat.card ((X ⊓ centralizer (tim77I X g : Set K)) ⊓
      centralizer ((tim77B X g ⊓ centralizer (tim77I X g : Set K) : Subgroup K) : Set K) :
        Subgroup K) ≤ 2 * Nat.card (zpowers z) := by
  have hBX : tim77B X g ≤ X := inf_le_left
  obtain ⟨-, hUcard⟩ := relIndex_inf_eq_two hBX hB hYB
  have hYcard : 4 * Nat.card (X ⊓ centralizer (tim77I X g : Set K) : Subgroup K) =
      Nat.card X := by
    have h : Nat.card (X ⊓ centralizer (tim77I X g : Set K) : Subgroup K) *
        Nat.card (tim77I X g) = 2 * Nat.card X :=
      hc.extra.card_centralizer (inf_le_left : tim77I X g ≤ X) hc.z_mem_I
    rw [h8] at h
    omega
  have hUX : tim77B X g ⊓ centralizer (tim77I X g : Set K) ≤ X := inf_le_left.trans hBX
  have hIU : tim77I X g ⊔ (tim77B X g ⊓ centralizer (tim77I X g : Set K)) ≤ X :=
    sup_le inf_le_left hUX
  have h := hc.extra.card_centralizer hIU ((le_sup_left : tim77I X g ≤ _) hc.z_mem_I)
  have hprod := card_sup_mul_card_inf (H := tim77I X g)
    (R := tim77B X g ⊓ centralizer (tim77I X g : Set K))
    (inf_le_right.trans (centralizer_le_normalizer _))
  have hinf : tim77I X g ⊓ (tim77B X g ⊓ centralizer (tim77I X g : Set K)) ≤ zpowers z := by
    intro c hc'
    obtain ⟨hcI, hcU⟩ := mem_inf.mp hc'
    exact hc.center_I_le h8 hcI fun j hj => mem_centralizer_iff.mp (mem_inf.mp hcU).2 j hj
  have hinf2 := card_le_of_le hinf
  rw [hc.card_zpowers_z] at hinf2
  rw [h8] at hprod
  have hle : (X ⊓ centralizer (tim77I X g : Set K)) ⊓
      centralizer ((tim77B X g ⊓ centralizer (tim77I X g : Set K) : Subgroup K) : Set K) ≤
      X ⊓ centralizer ((tim77I X g ⊔ (tim77B X g ⊓ centralizer (tim77I X g : Set K)) :
        Subgroup K) : Set K) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := mem_inf.mp hy
    exact ⟨(mem_inf.mp hy1).1, mem_centralizer_sup (mem_inf.mp hy1).2 hy2⟩
  have h1 := card_le_of_le hle
  rw [hc.card_zpowers_z]
  have hpos2 : 0 < Nat.card (tim77I X g ⊔ (tim77B X g ⊓ centralizer (tim77I X g : Set K)) :
    Subgroup K) := Nat.card_pos
  have e1 := Nat.mul_le_mul_left (Nat.card (tim77I X g ⊔ (tim77B X g ⊓
    centralizer (tim77I X g : Set K)) : Subgroup K)) hinf2
  have e2 : Nat.card X ≤ 2 * Nat.card (tim77I X g ⊔ (tim77B X g ⊓
      centralizer (tim77I X g : Set K)) : Subgroup K) := by linarith
  have e3 : Nat.card (X ⊓ centralizer ((tim77I X g ⊔ (tim77B X g ⊓
      centralizer (tim77I X g : Set K)) : Subgroup K) : Set K) : Subgroup K) *
      Nat.card (tim77I X g ⊔ (tim77B X g ⊓ centralizer (tim77I X g : Set K)) : Subgroup K) ≤
      4 * Nat.card (tim77I X g ⊔ (tim77B X g ⊓ centralizer (tim77I X g : Set K)) :
        Subgroup K) := by
    linarith
  have e4 := Nat.le_of_mul_le_mul_right e3 hpos2
  omega

theorem card_D_le_of_Q8 (h8 : Nat.card (tim77I X g) = 8)
    (hB : 2 * Nat.card (tim77B X g) = Nat.card X) : Nat.card (tim77D X g) ≤ 16 := by
  have hBX : tim77B X g ≤ X := inf_le_left
  have hZI : ∀ c ∈ tim77I X g, c ∈ centralizer (tim77I X g : Set K) → c ∈ zpowers z :=
    fun c hcI hcC => hc.center_I_le h8 hcI fun j hj => mem_centralizer_iff.mp hcC j hj
  have hD := hc.card_D_le_of_Q8_gens h8
  have hsup := hc.sup_eq_of_eight h8
  have hzC : z ∈ centralizer (tim77I X g : Set K) :=
    mem_centralizer_iff.mpr fun j _ => hc.commute_z j
  have hYB : ¬ X ⊓ centralizer (tim77I X g : Set K) ≤ tim77B X g := by
    intro hYB
    have h1 : X ≤ tim77B X g := hsup.symm.le.trans (sup_le tim77I_le_tim77B hYB)
    have h2 := card_le_of_le h1
    have hpos : 0 < Nat.card X := Nat.card_pos
    omega
  obtain ⟨hidx, -⟩ := relIndex_inf_eq_two hBX hB hYB
  have h := card_le_two_mul_of_transvection (Y := X ⊓ centralizer (tim77I X g : Set K))
    (U := tim77B X g ⊓ centralizer (tim77I X g : Set K)) (Z₀ := zpowers z)
    (D' := tim77D X g ⊓ centralizer (tim77I X g : Set K)) (inf_le_inf_right _ hBX)
    (zpowers_le.mpr ⟨hc.z_mem_B, hzC⟩) hidx
    (fun c hc' y _ => hc.commute_of_mem_zpowers hc' y)
    (fun a ha b hb => hc.extra.commutator_mem (mem_inf.mp ha).1 (mem_inf.mp hb).1)
    (hc.card_centralizer_le_of_Q8 h8 hB hYB)
    (fun d _ c hc' => hc.conj_of_mem_zpowers hc' d)
    (fun d hd y hy => ⟨hc.comm_X_D (mem_inf.mp hy).1 (mem_inf.mp hd).1,
      commutator_mem_of_mem (mem_inf.mp hy).2 (mem_inf.mp hd).2⟩)
    (fun d hd u hu => hZI _ (comm_tim77B_tim77D (mem_inf.mp hu).1 (mem_inf.mp hd).1)
      (commutator_mem_of_mem (mem_inf.mp hu).2 (mem_inf.mp hd).2))
    (zpowers z) (fun d hd hYd => by
      have := zpowers_normal_of_mem_center hc.center
      have hW : X ≤ (centralizer ({barMap z d} : Set (K ⧸ zpowers z))).comap (barMap z) := by
        refine hsup.symm.le.trans (sup_le (fun i hi => mem_comap_centralizer_barMap.mpr ?_)
          (fun y hy => mem_comap_centralizer_barMap.mpr (hYd y hy)))
        have hid : i * d = d * i := mem_centralizer_iff.mp (mem_inf.mp hd).2 i hi
        rw [hid, mul_inv_cancel_right, mul_inv_cancel]
        exact one_mem _
      have hdI := hc.mem_I_of_comm (mem_inf.mp hd).1
        fun x hx => mem_comap_centralizer_barMap.mp (hW hx)
      exact hZI d hdI (mem_inf.mp hd).2)
  have h2 : Nat.card ((tim77D X g ⊓ centralizer (tim77I X g : Set K)) ⊓ zpowers z :
      Subgroup K) ≤ 2 := hc.card_zpowers_z ▸ card_le_of_le inf_le_right
  omega

theorem card_D_le_of_dihedral (hB : 2 * Nat.card (tim77B X g) = Nat.card X) :
    Nat.card (tim77D X g) ≤ 32 := by
  rcases hc.cases_I with hI | ⟨i, hiI, hii, hIi⟩ | h8
  · have := hc.card_D_le_of_Z2 hI hB
    omega
  · exact hc.card_D_le_of_Z4 hiI hii hIi hB
  · have := hc.card_D_le_of_Q8 h8 hB
    omega

theorem false_of_dihedral (hX : 128 ≤ Nat.card X) (hB : 2 * Nat.card (tim77B X g) = Nat.card X)
    (hD : 2 * Nat.card (tim77D X g) = Nat.card X) : False := by
  have := hc.card_D_le_of_dihedral hB
  omega

end Conf110

end Dih

end CFSG.ComponentClassification.AS81
