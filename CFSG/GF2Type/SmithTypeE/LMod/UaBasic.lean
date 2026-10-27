module

public import CFSG.GF2Type.SmithTypeE.LMod.UaCert
public import CFSG.GF2Type.SmithTypeE.LMod.UaOrbit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6
open scoped Pointwise

attribute [local irreducible] stabGens elemGens planeImg meetCard dRoot tvIdxTab tvTab tvImg tvList

section Bits

variable {G : Type*} [Group G]

@[expose] def bitProd (g : ℕ → G) (a : ℕ) : ℕ → G
  | 0 => 1
  | n + 1 => bitProd g a n * if a.testBit n then g n else 1

theorem bitProd_zero (g : ℕ → G) (a : ℕ) : bitProd g a 0 = 1 := rfl

theorem bitProd_succ (g : ℕ → G) (a n : ℕ) :
    bitProd g a (n + 1) = bitProd g a n * if a.testBit n then g n else 1 := rfl

theorem bitProd_zero_left (g : ℕ → G) (n : ℕ) : bitProd g 0 n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bitProd_succ, ih]

theorem bitProd_mem {H : Subgroup G} {g : ℕ → G} (a : ℕ) {N : ℕ} (hg : ∀ j < N, g j ∈ H) :
    ∀ n ≤ N, bitProd g a n ∈ H := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [bitProd_zero]
    exact H.one_mem
  | succ n ih =>
    intro hn
    rw [bitProd_succ]
    refine H.mul_mem (ih (by omega)) ?_
    split
    · exact hg n (by omega)
    · exact H.one_mem

theorem commute_bitProd {g : ℕ → G} {c : G} (a : ℕ) {N : ℕ} (hc : ∀ j < N, Commute c (g j)) :
    ∀ n ≤ N, Commute c (bitProd g a n) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [bitProd_zero]
    exact Commute.one_right c
  | succ n ih =>
    intro hn
    rw [bitProd_succ]
    refine (ih (by omega)).mul_right ?_
    split
    · exact hc n (by omega)
    · exact Commute.one_right c

theorem bitProd_xor {g : ℕ → G} {N : ℕ} (hsq : ∀ j < N, g j * g j = 1)
    (hcomm : ∀ j < N, ∀ k < N, Commute (g j) (g k)) (a b : ℕ) :
    ∀ n ≤ N, bitProd g (a ^^^ b) n = bitProd g a n * bitProd g b n := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [bitProd_zero]
  | succ n ih =>
    intro hn
    have hB : Commute (g n) (bitProd g b n) :=
      commute_bitProd b (fun j hj => hcomm n (by omega) j (by omega)) n le_rfl
    have hx : Commute (if a.testBit n then g n else 1) (bitProd g b n) := by
      split
      · exact hB
      · exact Commute.one_left _
    have key : (if (a.testBit n ^^ b.testBit n) then g n else 1) =
        (if a.testBit n then g n else 1) * (if b.testBit n then g n else 1) := by
      cases a.testBit n <;> cases b.testBit n <;> simp [hsq n (by omega)]
    rw [bitProd_succ, bitProd_succ, bitProd_succ, ih (by omega), Nat.testBit_xor, key]
    calc bitProd g a n * bitProd g b n * ((if a.testBit n then g n else 1) *
          (if b.testBit n then g n else 1)) =
        bitProd g a n * (bitProd g b n * (if a.testBit n then g n else 1)) *
          (if b.testBit n then g n else 1) := by group
      _ = bitProd g a n * ((if a.testBit n then g n else 1) * bitProd g b n) *
          (if b.testBit n then g n else 1) := by rw [hx.eq]
      _ = _ := by group

theorem conj_bitProd (c : G) (g : ℕ → G) (a : ℕ) :
    ∀ n, c * bitProd g a n * c⁻¹ = bitProd (fun j => c * g j * c⁻¹) a n := by
  intro n
  induction n with
  | zero => simp [bitProd_zero]
  | succ n ih =>
    rw [bitProd_succ, bitProd_succ, ← ih]
    split <;> group

theorem bitProd_hom {ψ : ℕ → G} (h0 : ψ 0 = 1) (hψ : ∀ x y, ψ (x ^^^ y) = ψ x * ψ y)
    (v : ℕ → ℕ) (a : ℕ) :
    ∀ n, bitProd (fun j => ψ (v j)) a n =
      ψ ((List.range n).foldl (fun acc j => if a.testBit j then acc ^^^ v j else acc) 0) := by
  intro n
  induction n with
  | zero => simp [bitProd_zero, h0]
  | succ n ih =>
    have hr : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    rw [bitProd_succ, ih, hr, List.foldl_append]
    by_cases hb : a.testBit n
    · simp [hb, hψ]
    · simp [hb, h0]

end Bits

section Zero

@[expose] def gen0 (j : ℕ) : Fin 1953 :=
  if h : ugens[j]! < 1953 then ⟨ugens[j]!, h⟩ else 0

@[expose] def pt0 (k : ℕ) : Fin 1953 :=
  if h : (planePtsArr[0]!)[k]! < 1953 then ⟨(planePtsArr[0]!)[k]!, h⟩ else 0

@[expose] noncomputable def psi0 (a : ℕ) : Equiv.Perm (Fin 1953) := bitProd (fun j => tvP (gen0 j)) a 9

theorem getElem!_of_lt {P : Array ℕ} {k : ℕ} (h : k < P.size) : P[k]! = P[k]'h :=
  getElem!_pos P k h

theorem gen0_val {j : ℕ} (hj : j < 9) : (gen0 j).val = ugens[j]! := by
  have h : ugens[j]! < 1953 := (UaFacts.ugens_lt uaFacts j hj).1
  unfold gen0
  rw [dif_pos h]

theorem planePtsArr0 : planePtsArr[0]! = planePts 0 := planePtsArr_get (by norm_num)

theorem planePtsArr0_size : (planePtsArr[0]!).size = 49 := by
  rw [planePtsArr0, ← card_planeSet_eq 0]
  exact card_planeSet (i := 0) (by norm_num)

theorem planePts0_mem {k : ℕ} (hk : k < 49) :
    (planePtsArr[0]!)[k]! < 1953 ∧ inPlane 0 ((planePtsArr[0]!)[k]!) = true := by
  have hsz : k < (planePtsArr[0]!).size := by have := planePtsArr0_size; omega
  have hmem : (planePtsArr[0]!)[k]! ∈ planePtsArr[0]! := by
    rw [getElem!_of_lt hsz]
    exact Array.getElem_mem hsz
  rw [planePtsArr0] at hmem ⊢
  exact mem_planePts.1 hmem

theorem pt0_val {k : ℕ} (hk : k < 49) : (pt0 k).val = (planePtsArr[0]!)[k]! := by
  have hlt := (planePts0_mem hk).1
  unfold pt0
  rw [dif_pos hlt]

theorem pt0_mem {k : ℕ} (hk : k < 49) : pt0 k ∈ wPlane 0 :=
  mem_wPlane.2 (by rw [pt0_val hk]; exact (planePts0_mem hk).2)

theorem mem_P0 {p : Fin 1953} (hp : p ∈ wPlane 0) : p.val ∈ planePtsArr[0]! := by
  rw [planePtsArr0]
  exact mem_planePts.2 ⟨p.isLt, mem_wPlane.1 hp⟩

theorem exists_pt0 {p : Fin 1953} (hp : p ∈ wPlane 0) : ∃ k < 49, pt0 k = p := by
  obtain ⟨k, hk, hkp⟩ := Array.mem_iff_getElem.1 (mem_P0 hp)
  have hk49 : k < 49 := by have := planePtsArr0_size; omega
  refine ⟨k, hk49, Fin.ext ?_⟩
  rw [pt0_val hk49, getElem!_of_lt hk]
  exact hkp

theorem gen0_mem (j : ℕ) (hj : j < 9) : gen0 j ∈ wPlane 0 :=
  mem_wPlane.2 (by rw [gen0_val hj]; exact (UaFacts.ugens_lt uaFacts j hj).2)

theorem psi0_zero : psi0 0 = 1 := bitProd_zero_left _ _

theorem commute_tvP_of_fix {p q : Fin 1953} (h : tvP p q = q) :
    Commute (tvP p) (tvP q) := by
  have e := mul_tvP_mul_inv (tvP_mem p) q
  rw [h] at e
  exact mul_inv_eq_iff_eq_mul.1 e

theorem tvP_gen0_comm {j k : ℕ} (hj : j < 9) (hk : k < 9) :
    Commute (tvP (gen0 j)) (tvP (gen0 k)) := by
  apply commute_tvP_of_fix
  refine Fin.ext ?_
  have h1 := UaFacts.commute uaFacts _ (mem_P0 (gen0_mem j hj)) _
    (mem_P0 (gen0_mem k hk))
  rw [tvTab_get (gen0 j).isLt (gen0 k).isLt] at h1
  exact (tvP_apply _ _).trans h1

theorem psi0_xor (a b : ℕ) : psi0 (a ^^^ b) = psi0 a * psi0 b :=
  bitProd_xor (g := fun j => tvP (gen0 j)) (N := 9)
    (fun j _ => tvP_mul_self _) (fun _ hj _ hk => tvP_gen0_comm hj hk) a b 9 le_rfl

theorem psi0_mul_self (a : ℕ) : psi0 a * psi0 a = 1 := by
  rw [← psi0_xor, Nat.xor_self, psi0_zero]

theorem psi0_mem_UA (a : ℕ) : psi0 a ∈ UA 0 :=
  bitProd_mem (H := UA 0) (g := fun j => tvP (gen0 j)) a (N := 9)
    (fun j hj => tvP_mem_UA (gen0_mem j hj)) 9 le_rfl

theorem psi0_apply_aux (a : ℕ) : ∀ n, n ≤ 9 → ∀ x : Fin 1953,
    ((bitProd (fun j => tvP (gen0 j)) a n x : Fin 1953) : ℕ) =
      (List.range n).foldr (fun j y => if a.testBit j then (tvTab[ugens[j]!]!)[y]! else y)
        x.val
  | 0, _, x => by simp [bitProd_zero]
  | n + 1, hn, x => by
    have hn9 : n < 9 := by omega
    have ih := psi0_apply_aux a n (by omega)
    have hlt : ugens[n]! < 1953 := (UaFacts.ugens_lt uaFacts n hn9).1
    have hval : ((tvP (gen0 n) x : Fin 1953) : ℕ) = (tvTab[ugens[n]!]!)[x.val]! := by
      rw [tvP_apply, gen0_val hn9, tvTab_get hlt x.isLt]
    rw [bitProd_succ, List.range_succ, List.foldr_append]
    by_cases ha : a.testBit n
    · simp only [ha, ↓reduceIte, Equiv.Perm.mul_apply, List.foldr_cons, List.foldr_nil]
      rw [ih, hval]
    · simp only [ha, ↓reduceIte, Equiv.Perm.mul_apply, mul_one, List.foldr_cons,
        List.foldr_nil]
      exact ih x

theorem psi0_apply (a : ℕ) (x : Fin 1953) : ((psi0 a x : Fin 1953) : ℕ) = uaWord a x.val :=
  psi0_apply_aux a 9 le_rfl x

theorem tvP_pt0 {k : ℕ} (hk : k < 49) : tvP (pt0 k) = psi0 (uco[k]!) := by
  have hlt : (planePtsArr[0]!)[k]! < 1953 := (planePts0_mem hk).1
  refine Equiv.ext fun x => Fin.ext ?_
  rw [tvP_apply, pt0_val hk, psi0_apply, UaFacts.word uaFacts k hk x.val x.isLt,
    tvTab_get hlt x.isLt]

theorem psi0_ne_one {a : ℕ} (ha0 : 0 < a) (ha : a < 512) : psi0 a ≠ 1 := by
  intro h
  obtain ⟨x, hx, hne⟩ := UaFacts.faithful uaFacts a ha ha0.ne'
  have h1 := psi0_apply a ⟨x, hx⟩
  rw [h, Equiv.Perm.one_apply] at h1
  exact hne h1.symm

theorem psi0_inj {a b : ℕ} (ha : a < 512) (hb : b < 512) (h : psi0 a = psi0 b) : a = b := by
  by_contra hab
  have hx : 0 < a ^^^ b := by
    refine Nat.pos_of_ne_zero fun h0 => hab ?_
    calc a = a ^^^ 0 := (Nat.xor_zero a).symm
      _ = a ^^^ (b ^^^ b) := by rw [Nat.xor_self]
      _ = (a ^^^ b) ^^^ b := (Nat.xor_assoc a b b).symm
      _ = b := by rw [h0, Nat.zero_xor]
  apply psi0_ne_one hx (Nat.xor_lt_two_pow (n := 9) ha hb)
  rw [psi0_xor, h, psi0_mul_self]

theorem hd3_mem_planePtsArr_zero {p : ℕ} :
    p ∈ planePtsArr[0]! ↔ p < 1953 ∧ inPlane 0 p = true := by
  rw [planePtsArr_get (by norm_num : (0 : ℕ) < 1395), mem_planePts]

theorem hd3_tvP_fix {q p : Fin 1953} (hq : q ∈ wPlane 0) (hp : p ∈ wPlane 0) :
    tvP q p = p := by
  apply Fin.ext
  rw [tvP_apply, ← tvTab_get q.2 p.2]
  exact uaFacts.commute (q : ℕ) (hd3_mem_planePtsArr_zero.2 ⟨q.2, mem_wPlane.1 hq⟩) (p : ℕ)
    (hd3_mem_planePtsArr_zero.2 ⟨p.2, mem_wPlane.1 hp⟩)

theorem mem_UA_zero {u : Equiv.Perm (Fin 1953)} : u ∈ UA 0 ↔ ∃ a < 512, psi0 a = u := by
  constructor
  · intro hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨p, hp, rfl⟩ := hx
      obtain ⟨k, hk, rfl⟩ := exists_pt0 hp
      exact ⟨uco[k]!, (uaFacts.uco_parts k hk).2, (tvP_pt0 hk).symm⟩
    | one => exact ⟨0, by norm_num, psi0_zero⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a ^^^ b, Nat.xor_lt_two_pow (n := 9) ha hb, psi0_xor a b⟩
    | inv x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨a, ha, (inv_eq_of_mul_eq_one_right (psi0_mul_self a)).symm⟩
  · rintro ⟨a, -, rfl⟩
    exact psi0_mem_UA a

theorem card_UA_zero : Nat.card (UA 0) = 2 ^ 9 := by
  have hbij : Function.Bijective
      (fun a : Fin 512 => (⟨psi0 a.val, psi0_mem_UA a.val⟩ : UA 0)) := by
    refine ⟨fun a b h => Fin.ext (psi0_inj a.2 b.2 (congrArg Subtype.val h)), ?_⟩
    rintro ⟨u, hu⟩
    obtain ⟨a, ha, rfl⟩ := mem_UA_zero.1 hu
    exact ⟨⟨a, ha⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_fin]
  norm_num

theorem UA_apply_of_mem_zero {u : Equiv.Perm (Fin 1953)} (hu : u ∈ UA 0) {p : Fin 1953}
    (hp : p ∈ wPlane 0) : u p = p := by
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨q, hq, rfl⟩ := hx
    exact hd3_tvP_fix hq hp
  | one => rfl
  | mul x y _ _ hx hy => rw [Equiv.Perm.mul_apply, hy, hx]
  | inv x _ hx => exact Equiv.Perm.inv_eq_iff_eq.2 hx.symm

theorem mem_wPlane_zero_of_comm {q : Fin 1953} (h : ∀ p ∈ wPlane 0, tvP p q = q) :
    q ∈ wPlane 0 := by
  have H : ∀ p ∈ planePtsArr[0]!, (tvTab[p]!)[q.val]! = q.val := by
    intro p hp
    obtain ⟨hp1, hpW⟩ := hd3_mem_planePtsArr_zero.1 hp
    have hmem : (⟨p, hp1⟩ : Fin 1953) ∈ wPlane 0 := mem_wPlane.2 hpW
    have e := congrArg Fin.val (h _ hmem)
    rw [tvP_apply] at e
    rw [tvTab_get hp1 q.2]
    exact e
  exact mem_wPlane.2 (uaFacts.cent q.val q.2 H)

theorem fix_UA_zero {j : ℕ} (hj : j < 1395) (h : ∀ u ∈ UA 0, ⇑u '' wPlane j = wPlane j) :
    j = 0 := by
  by_contra hj0
  obtain ⟨p, hp, hne⟩ := uaFacts.onlyW j hj hj0
  obtain ⟨hp1, hpW⟩ := hd3_mem_planePtsArr_zero.1 hp
  have hmem : (⟨p, hp1⟩ : Fin 1953) ∈ wPlane 0 := mem_wPlane.2 hpW
  have hT := h (tvP ⟨p, hp1⟩) (tvP_mem_UA hmem)
  rw [image_wPlane_tvP hj] at hT
  exact hne (wPlane_injective (tw_parts hp1 hj).1 hj hT)

end Zero

section Conj

theorem conj_mem_UA {g : Equiv.Perm (Fin 1953)} (hg : IsTvAut g) {i j : ℕ}
    (h : ⇑g '' wPlane i = wPlane j) {u : Equiv.Perm (Fin 1953)} (hu : u ∈ UA i) :
    g * u * g⁻¹ ∈ UA j := by
  change u ∈ Subgroup.closure (tvP '' wPlane i) at hu
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    have hgp : g p ∈ wPlane j := by
      rw [← h]
      exact Set.mem_image_of_mem _ hp
    rw [hg p]
    exact tvP_mem_UA hgp
  | one =>
    have e : g * 1 * g⁻¹ = 1 := by group
    rw [e]
    exact one_mem _
  | mul x y hx hy ihx ihy =>
    have e : g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
    rw [e]
    exact mul_mem ihx ihy
  | inv x hx ih =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ih

theorem mem_UA_iff_conj {x : Equiv.Perm (Fin 1953)} (hx : x ∈ T6) {i : ℕ}
    (hW : ⇑x '' wPlane 0 = wPlane i) {u : Equiv.Perm (Fin 1953)} :
    u ∈ UA i ↔ x⁻¹ * u * x ∈ UA 0 := by
  constructor
  · intro hu
    have h1 := conj_mem_UA (IsTvAut.inv (isTvAut_of_mem hx)) (image_wPlane_inv hW) hu
    rwa [inv_inv] at h1
  · intro hv
    have h1 := conj_mem_UA (isTvAut_of_mem hx) hW hv
    rwa [show x * (x⁻¹ * u * x) * x⁻¹ = u by group] at h1

end Conj

section General

theorem card_UA {i : ℕ} (hi : i < 1395) : Nat.card (UA i) = 2 ^ 9 := by
  obtain ⟨x, hx, hW⟩ := exists_image_wPlane_zero hi
  have key : ∀ v ∈ UA 0, x * v * x⁻¹ ∈ UA i := fun v hv => by
    refine (mem_UA_iff_conj hx hW).2 ?_
    rw [show x⁻¹ * (x * v * x⁻¹) * x = v by group]
    exact hv
  let e : UA i ≃ UA 0 :=
    { toFun := fun u => ⟨x⁻¹ * (u : Equiv.Perm (Fin 1953)) * x, (mem_UA_iff_conj hx hW).1 u.2⟩
      invFun := fun v => ⟨x * (v : Equiv.Perm (Fin 1953)) * x⁻¹, key v v.2⟩
      left_inv := fun u => Subtype.ext
        (show x * (x⁻¹ * (u : Equiv.Perm (Fin 1953)) * x) * x⁻¹ = u by group)
      right_inv := fun v => Subtype.ext
        (show x⁻¹ * (x * (v : Equiv.Perm (Fin 1953)) * x⁻¹) * x = v by group) }
  exact (Nat.card_congr e).trans card_UA_zero

theorem commute_of_mem_UA {i : ℕ} (hi : i < 1395) {u v : Equiv.Perm (Fin 1953)}
    (hu : u ∈ UA i) (hv : v ∈ UA i) : Commute u v := by
  obtain ⟨x, hx, hW⟩ := exists_image_wPlane_zero hi
  obtain ⟨a, -, ha⟩ := mem_UA_zero.1 ((mem_UA_iff_conj hx hW).1 hu)
  obtain ⟨b, -, hb⟩ := mem_UA_zero.1 ((mem_UA_iff_conj hx hW).1 hv)
  have hab : psi0 a * psi0 b = psi0 b * psi0 a := by
    rw [← psi0_xor a b, ← psi0_xor b a, Nat.xor_comm a b]
  have hc : x⁻¹ * u * x * (x⁻¹ * v * x) = x⁻¹ * v * x * (x⁻¹ * u * x) := by
    rw [← ha, ← hb]
    exact hab
  show u * v = v * u
  calc u * v = x * (x⁻¹ * u * x * (x⁻¹ * v * x)) * x⁻¹ := by group
    _ = x * (x⁻¹ * v * x * (x⁻¹ * u * x)) * x⁻¹ := by rw [hc]
    _ = v * u := by group

theorem UA_apply_of_mem {i : ℕ} (hi : i < 1395) {u : Equiv.Perm (Fin 1953)} (hu : u ∈ UA i)
    {p : Fin 1953} (hp : p ∈ wPlane i) : u p = p := by
  obtain ⟨x, hx, hW⟩ := exists_image_wPlane_zero hi
  have hp' : x⁻¹ p ∈ wPlane 0 := by
    rw [← image_wPlane_inv hW]
    exact Set.mem_image_of_mem _ hp
  have h := UA_apply_of_mem_zero ((mem_UA_iff_conj hx hW).1 hu) hp'
  have hai : x (x⁻¹ p) = p := Equiv.Perm.eq_inv_iff_eq.1 rfl
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hai] at h
  exact Equiv.injective x⁻¹ h

theorem fix_UA {i : ℕ} (hi : i < 1395) {j : ℕ} (hj : j < 1395)
    (h : ∀ u ∈ UA i, ⇑u '' wPlane j = wPlane j) : j = i := by
  obtain ⟨x, hx, hW⟩ := exists_image_wPlane_zero hi
  have key : ∀ v ∈ UA 0, x * v * x⁻¹ ∈ UA i := fun v hv => by
    refine (mem_UA_iff_conj hx hW).2 ?_
    rw [show x⁻¹ * (x * v * x⁻¹) * x = v by group]
    exact hv
  obtain ⟨j', hj', hj'eq⟩ := exists_image_wPlane (inv_mem hx) hj
  have comp : ∀ (a b : Equiv.Perm (Fin 1953)) (S : Set (Fin 1953)),
      ⇑(a * b) '' S = ⇑a '' (⇑b '' S) := fun a b S => by
    rw [Equiv.Perm.coe_mul, Set.image_comp]
  have H : ∀ v ∈ UA 0, ⇑v '' wPlane j' = wPlane j' := by
    intro v hv
    have h1 := h _ (key v hv)
    rw [← hj'eq]
    calc ⇑v '' (⇑x⁻¹ '' wPlane j) = ⇑(v * x⁻¹) '' wPlane j := (comp v x⁻¹ _).symm
      _ = ⇑(x⁻¹ * (x * v * x⁻¹)) '' wPlane j := by
          rw [show x⁻¹ * (x * v * x⁻¹) = v * x⁻¹ by group]
      _ = ⇑x⁻¹ '' (⇑(x * v * x⁻¹) '' wPlane j) := comp x⁻¹ _ _
      _ = ⇑x⁻¹ '' wPlane j := by rw [h1]
  have h0 : j' = 0 := fix_UA_zero hj' H
  rw [h0] at hj'eq
  have h2 : ⇑x '' wPlane 0 = wPlane j := by
    have h3 := image_wPlane_inv hj'eq
    rwa [inv_inv] at h3
  exact wPlane_injective hj hi (h2.symm.trans hW)

theorem UA_injective {i : ℕ} (hi : i < 1395) {j : ℕ} (hj : j < 1395) (h : UA i = UA j) :
    i = j := by
  refine fix_UA hj hi (fun u hu => ?_)
  have hu' : u ∈ UA i := by
    rw [h]
    exact hu
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    rw [UA_apply_of_mem hi hu' hp]
    exact hp
  · intro y hy
    exact ⟨y, hy, UA_apply_of_mem hi hu' hy⟩

end General

end CFSG.GF2Type.SmithTypeE.LMod
