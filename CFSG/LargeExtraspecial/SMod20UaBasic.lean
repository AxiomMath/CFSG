module

public import CFSG.LargeExtraspecial.SMod20UaCert
public import Certificates.Data.SMod20CollCheck

public section

namespace CFSG.LargeExtraspecial.SMod20

open CFSG.Fischer CFSG.SmithE CFSG.F4.Native CFSG.Fischer.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native

open scoped Pointwise

attribute [local irreducible] uaPts uPts uPos

section Bits

variable {G : Type*} [Group G]

theorem bitProd_succ (g : ℕ → G) (a n : ℕ) :
    bitProd g a (n + 1) = bitProd g a n * if a.testBit n then g n else 1 := rfl

theorem bitProd_zero_left (g : ℕ → G) (n : ℕ) : bitProd g 0 n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bitProd_succ, ih]

theorem bitProd_mem {H : Subgroup G} {g : ℕ → G} (a : ℕ) {N : ℕ} (hg : ∀ j < N, g j ∈ H) :
    ∀ n ≤ N, bitProd g a n ∈ H
  | 0, _ => H.one_mem
  | n + 1, hn => by
    rw [bitProd_succ]
    refine H.mul_mem (bitProd_mem a hg n (by omega)) ?_
    split
    · exact hg n (by omega)
    · exact H.one_mem

theorem commute_bitProd {g : ℕ → G} {c : G} (a : ℕ) {N : ℕ} (hc : ∀ j < N, Commute c (g j)) :
    ∀ n ≤ N, Commute c (bitProd g a n)
  | 0, _ => Commute.one_right c
  | n + 1, hn => by
    rw [bitProd_succ]
    refine (commute_bitProd a hc n (by omega)).mul_right ?_
    split
    · exact hc n (by omega)
    · exact Commute.one_right c

theorem bitProd_xor {g : ℕ → G} {N : ℕ} (hsq : ∀ j < N, g j * g j = 1)
    (hcomm : ∀ j < N, ∀ k < N, Commute (g j) (g k)) (a b : ℕ) :
    ∀ n ≤ N, bitProd g (a ^^^ b) n = bitProd g a n * bitProd g b n
  | 0, _ => by simp [bitProd]
  | n + 1, hn => by
    have hB : Commute (g n) (bitProd g b n) :=
      commute_bitProd b (fun j hj => hcomm n (by omega) j (by omega)) n le_rfl
    have hx : Commute (if a.testBit n then g n else 1) (bitProd g b n) := by
      split
      · exact hB
      · exact Commute.one_left _
    have key : (if (a.testBit n ^^ b.testBit n) then g n else 1) =
        (if a.testBit n then g n else 1) * (if b.testBit n then g n else 1) := by
      cases a.testBit n <;> cases b.testBit n <;> simp [hsq n (by omega)]
    rw [bitProd_succ, bitProd_succ, bitProd_succ, bitProd_xor hsq hcomm a b n (by omega),
      Nat.testBit_xor, key]
    calc bitProd g a n * bitProd g b n * ((if a.testBit n then g n else 1) *
          (if b.testBit n then g n else 1)) =
        bitProd g a n * (bitProd g b n * (if a.testBit n then g n else 1)) *
          (if b.testBit n then g n else 1) := by group
      _ = bitProd g a n * ((if a.testBit n then g n else 1) * bitProd g b n) *
          (if b.testBit n then g n else 1) := by rw [hx.eq]
      _ = _ := by group

theorem conj_bitProd (c : G) (g : ℕ → G) (a : ℕ) :
    ∀ n, c * bitProd g a n * c⁻¹ = bitProd (fun j => c * g j * c⁻¹) a n
  | 0 => by simp [bitProd]
  | n + 1 => by
    rw [bitProd_succ, bitProd_succ, ← conj_bitProd c g a n]
    split <;> group

theorem bitProd_hom {ψ : ℕ → G} (h0 : ψ 0 = 1) (hψ : ∀ x y, ψ (x ^^^ y) = ψ x * ψ y)
    (v : ℕ → ℕ) (a : ℕ) : ∀ n, bitProd (fun j => ψ (v j)) a n = ψ (bitSum v a n)
  | 0 => h0.symm
  | n + 1 => by
    rw [bitProd_succ, bitProd_hom h0 hψ v a n, bitSum, hψ]
    split
    · rfl
    · rw [h0]

end Bits

theorem bitSum_succ (v : ℕ → ℕ) (a n : ℕ) :
    bitSum v a (n + 1) = bitSum v a n ^^^ if a.testBit n then v n else 0 := rfl

theorem bitSum_lt {v : ℕ → ℕ} {m : ℕ} (a : ℕ) {N : ℕ} (hv : ∀ j < N, v j < 2 ^ m) :
    ∀ n ≤ N, bitSum v a n < 2 ^ m
  | 0, _ => Nat.two_pow_pos m
  | n + 1, hn => by
    rw [bitSum_succ]
    refine Nat.xor_lt_two_pow (bitSum_lt a hv n (by omega)) ?_
    split
    · exact hv n (by omega)
    · exact Nat.two_pow_pos m

theorem bitSum_xor (v : ℕ → ℕ) (a b : ℕ) :
    ∀ n, bitSum v (a ^^^ b) n = bitSum v a n ^^^ bitSum v b n
  | 0 => by simp [bitSum]
  | n + 1 => by
    have key : (if (a.testBit n ^^ b.testBit n) then v n else 0) =
        (if a.testBit n then v n else 0) ^^^ (if b.testBit n then v n else 0) := by
      cases a.testBit n <;> cases b.testBit n <;> simp
    rw [bitSum_succ, bitSum_succ, bitSum_succ, bitSum_xor v a b n, Nat.testBit_xor, key]
    ac_rfl

theorem collAmatN_eq (s : Array ℕ) (a : ℕ) :
    ∀ n, collAmatN s a n = bitSum (fun j => uaCo[s[j]!]!) a n
  | 0 => rfl
  | n + 1 => by rw [collAmatN, bitSum_succ, collAmatN_eq s a n]

theorem bitProd_congr {G : Type*} [Group G] {g g' : ℕ → G} (a : ℕ) :
    ∀ n, (∀ j < n, g j = g' j) → bitProd g a n = bitProd g' a n
  | 0, _ => rfl
  | n + 1, h => by
    rw [bitProd_succ, bitProd_succ, bitProd_congr a n fun j hj => h j (by omega), h n (by omega)]

theorem xor_eq_zero_iff {a b : ℕ} : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congrArg (a ^^^ ·) h
    simpa [← Nat.xor_assoc] using this.symm
  · rintro rfl
    exact Nat.xor_self a

theorem uaCo_lt {k : ℕ} (hk : k < 21) : uaCo[k]! < 512 := by
  revert k
  decide

theorem find?_range_eq_some {p : ℕ → Bool} {n m : ℕ} (hm : m < n)
    (h : ∀ k < n, p k = true ↔ k = m) : (List.range n).find? p = some m := by
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨(h m hm).2 rfl, m, by simpa using hm, by simp, fun j hj => ?_⟩
  have hjn : j < n := by omega
  simp only [List.getElem_range, Bool.not_eq_true']
  exact Bool.eq_false_iff.2 fun hj' => by have := (h j hjn).1 hj'; omega

@[expose] noncomputable def UA (i : ℕ) :
    Subgroup (Equiv.Perm (Fin 693)) :=
  Subgroup.closure (tvP '' wPlane i)

@[expose] noncomputable def PA (i : ℕ) :
    Subgroup (Equiv.Perm (Fin 693)) :=
  T46 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 693)) (wPlane i)

@[expose] def sArr (i : ℕ) (g : Equiv.Perm (Fin 693)) : Array ℕ :=
  Array.ofFn (n := 21) fun k => uaPos (uaPts[i]!) (g (wPt i k.val)).val

theorem mem_stabilizer_wPlane {i : ℕ} {g : Equiv.Perm (Fin 693)} :
    g ∈ MulAction.stabilizer (Equiv.Perm (Fin 693)) (wPlane i) ↔ ⇑g '' wPlane i = wPlane i := by
  rw [MulAction.mem_stabilizer_iff]
  exact Iff.rfl

section Psi

variable
  {i : ℕ}

theorem uaGen_mul_self (i k : ℕ) : uaGen i k * uaGen i k = 1 := tvP_mul_self _

theorem commute_uaGen (hi : i < 891) {k l : ℕ} (hk : k < 21) (hl : l < 21) :
    Commute (uaGen i k) (uaGen i l) :=
  (tvP_comm_iff_perp _ _).2 (perp_wPt hi hk hl)

theorem uaPsi_xor (hi : i < 891) (a b : ℕ) : uaPsi i (a ^^^ b) = uaPsi i a * uaPsi i b :=
  bitProd_xor (N := 21) (fun j _ => uaGen_mul_self i j)
    (fun _ hj _ hk => commute_uaGen hi hj hk) a b 9 (by norm_num)

theorem uaPsi_zero (i : ℕ) : uaPsi i 0 = 1 := bitProd_zero_left _ _

theorem uaPsi_mul_self (hi : i < 891) (a : ℕ) : uaPsi i a * uaPsi i a = 1 := by
  rw [← uaPsi_xor hi, Nat.xor_self, uaPsi_zero]

theorem bitProd_uaGen_apply (hi : i < 891) (a : ℕ) (n : ℕ) (hn : n ≤ 21) (x : Fin 693) :
    (bitProd (uaGen i) a n x).val = uaAp tvTabs (uaPts[i]!) a n x.val := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [bitProd_succ, Equiv.Perm.mul_apply, ih (by omega)]
    have hn' : n < 21 := by omega
    show _ = uaAp tvTabs (uaPts[i]!) a n
      (if a.testBit n then ap (tvTabs[(uaPts[i]!)[n]!]!) x.val else x.val)
    congr 1
    split
    · rw [uaGen, ← wPt_val hi hn', rep_tvP _ x.val x.2, idx_of_lt _ x.2]
      rfl
    · rfl

theorem uaPsi_apply (hi : i < 891) (a : ℕ) (x : Fin 693) :
    (uaPsi i a x).val = uaAp tvTabs (uaPts[i]!) a 9 x.val :=
  bitProd_uaGen_apply hi a 9 (by norm_num) x

theorem uaPsi_co (hi : i < 891) {k : ℕ} (hk : k < 21) : uaPsi i uaCo[k]! = uaGen i k := by
  ext x
  rw [uaPsi_apply hi, (uaPlane_parts hi).2.2.2.2.2.1 k hk x.val x.2, uaGen, ← wPt_val hi hk,
    rep_tvP _ x.val x.2, idx_of_lt _ x.2]
  rfl

theorem uaPsi_ne_one (hi : i < 891) {a : ℕ} (ha0 : 0 < a) (ha : a < 512) : uaPsi i a ≠ 1 := by
  intro h
  obtain ⟨x, hx, hne⟩ := (uaPlane_parts hi).2.2.2.2.2.2 a ha0 ha
  apply hne
  have := uaPsi_apply hi a ⟨x, hx⟩
  rw [h] at this
  exact this.symm

theorem uaPsi_inj (hi : i < 891) {a b : ℕ} (ha : a < 512) (hb : b < 512)
    (h : uaPsi i a = uaPsi i b) : a = b := by
  by_contra hab
  have hx : 0 < a ^^^ b := Nat.pos_of_ne_zero fun h0 => hab (xor_eq_zero_iff.1 h0)
  apply uaPsi_ne_one hi hx (Nat.xor_lt_two_pow (n := 9) ha hb)
  rw [uaPsi_xor hi, h, uaPsi_mul_self hi]

theorem tvP_mem_UA {p : Fin 693} (hp : p ∈ wPlane i) : tvP p ∈ UA i :=
  Subgroup.subset_closure ⟨p, hp, rfl⟩

theorem uaGen_mem_UA {k : ℕ} (hk : k < 21) : uaGen i k ∈ UA i := tvP_mem_UA (wPt_mem i hk)

theorem uaPsi_mem_UA (a : ℕ) : uaPsi i a ∈ UA i :=
  bitProd_mem a (N := 21) (fun _ hj => uaGen_mem_UA hj) 9 (by norm_num)

theorem mem_UA (hi : i < 891) {u : Equiv.Perm (Fin 693)} :
    u ∈ UA i ↔ ∃ a < 512, uaPsi i a = u := by
  constructor
  · intro hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨p, ⟨k, hk, rfl⟩, rfl⟩ := hx
      exact ⟨uaCo[k]!, uaCo_lt hk, uaPsi_co hi hk⟩
    | one => exact ⟨0, by norm_num, uaPsi_zero i⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a ^^^ b, Nat.xor_lt_two_pow (n := 9) ha hb, uaPsi_xor hi a b⟩
    | inv x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨a, ha, (inv_eq_of_mul_eq_one_right (uaPsi_mul_self hi a)).symm⟩
  · rintro ⟨a, -, rfl⟩
    exact uaPsi_mem_UA a

theorem card_UA (hi : i < 891) : Nat.card (UA i) = 2 ^ 9 := by
  have hbij : Function.Bijective
      (fun a : Fin 512 => (⟨uaPsi i a.val, uaPsi_mem_UA a.val⟩ : UA i)) := by
    refine ⟨fun a b h => Fin.ext (uaPsi_inj hi a.2 b.2 (congrArg Subtype.val h)), ?_⟩
    rintro ⟨u, hu⟩
    obtain ⟨a, ha, rfl⟩ := (mem_UA hi).1 hu
    exact ⟨⟨a, ha⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_fin]
  norm_num

theorem commute_of_mem_UA (hi : i < 891) {u v : Equiv.Perm (Fin 693)} (hu : u ∈ UA i)
    (hv : v ∈ UA i) : Commute u v := by
  obtain ⟨a, -, rfl⟩ := (mem_UA hi).1 hu
  obtain ⟨b, -, rfl⟩ := (mem_UA hi).1 hv
  show uaPsi i a * uaPsi i b = uaPsi i b * uaPsi i a
  rw [← uaPsi_xor hi, ← uaPsi_xor hi, Nat.xor_comm]

theorem UA_le_T46 : UA i ≤ T46 := by
  rw [UA, Subgroup.closure_le]
  rintro _ ⟨p, -, rfl⟩
  exact tvP_mem p

theorem UA_apply_of_mem (hi : i < 891) {u : Equiv.Perm (Fin 693)} (hu : u ∈ UA i)
    {q : Fin 693} (hq : q ∈ wPlane i) : u q = q := by
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    exact tvP_apply_eq_self_iff.2 (perp_of_mem_wPlane hi hp hq)
  | one => rfl
  | mul x y _ _ hx hy => rw [Equiv.Perm.mul_apply, hy, hx]
  | inv x _ hx => exact Equiv.Perm.inv_eq_iff_eq.2 hx.symm

theorem fix_UA (hi : i < 891) {j : ℕ} (hj : j < 891)
    (h : ∀ u ∈ UA i, ⇑u '' wPlane j = wPlane j) : j = i := by
  have hsub : wPlane i ⊆ wPlane j := by
    intro p hp
    by_contra hpj
    have hex : ¬ ∀ q ∈ wPlane j, perp q p := fun H => hpj (mem_wPlane_of_perp hj H)
    simp only [not_forall] at hex
    obtain ⟨q, hq, hqp⟩ := hex
    have himg : tvP p q ∈ wPlane j := by
      rw [← h _ (tvP_mem_UA hp)]
      exact ⟨q, hq, rfl⟩
    exact not_perp_tvP (fun h' => hqp (perp_comm.1 h')) (perp_of_mem_wPlane hj hq himg)
  have hsup : wPlane j ⊆ wPlane i := fun q hq =>
    mem_wPlane_of_perp hi fun _ hp => perp_of_mem_wPlane hj (hsub hp) hq
  exact wPlane_injective hj hi (Set.Subset.antisymm hsup hsub)

theorem UA_injective (hi : i < 891) {j : ℕ} (hj : j < 891) (h : UA i = UA j) : i = j := by
  refine fix_UA hj hi fun u hu => ?_
  rw [← h] at hu
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rwa [UA_apply_of_mem hi hu hq]
  · intro hp
    exact ⟨p, hp, UA_apply_of_mem hi hu hp⟩

end Psi

section Conj

variable
  {i : ℕ}

theorem conj_mem_UA {g : Equiv.Perm (Fin 693)} (hg : IsPolarAut g) {j : ℕ}
    (hW : ⇑g '' wPlane i = wPlane j) {h : Equiv.Perm (Fin 693)} (hh : h ∈ UA i) :
    g * h * g⁻¹ ∈ UA j := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    rw [hg.mul_tvP_mul_inv]
    exact tvP_mem_UA (hW ▸ ⟨p, hp, rfl⟩)
  | one => simp [(UA j).one_mem]
  | mul x y _ _ hx hy =>
    have := (UA j).mul_mem hx hy
    rwa [show g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ by group] at this
  | inv x _ hx =>
    have := (UA j).inv_mem hx
    rwa [show (g * x * g⁻¹)⁻¹ = g * x⁻¹ * g⁻¹ by group] at this

theorem image_wPlane_inv {g : Equiv.Perm (Fin 693)} {j : ℕ}
    (hW : ⇑g '' wPlane i = wPlane j) : ⇑g⁻¹ '' wPlane j = wPlane i := by
  rw [← hW, Set.image_image]
  simp [perm_inv_apply_self]

theorem uaPos_wPt (hi : i < 891) {m : ℕ} (hm : m < 21) : uaPos (uaPts[i]!) (wPt i m).val = m := by
  unfold uaPos
  rw [find?_range_eq_some hm fun k hk => ?_]
  · rfl
  rw [beq_iff_eq, ← wPt_val hi hk]
  exact ⟨fun h => wPt_inj hi hk hm (Fin.ext h), fun h => by rw [h]⟩

theorem sArr_size (i : ℕ) (g : Equiv.Perm (Fin 693)) : (sArr i g).size = 21 := by
  rw [sArr, Array.size_ofFn]

theorem sArr_get {g : Equiv.Perm (Fin 693)} {k : ℕ} (hk : k < 21) :
    (sArr i g)[k]! = uaPos (uaPts[i]!) (g (wPt i k)).val := by
  unfold sArr
  rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]

theorem sArr_spec (hi : i < 891) {g : Equiv.Perm (Fin 693)} (hW : ⇑g '' wPlane i = wPlane i)
    {k : ℕ} (hk : k < 21) : (sArr i g)[k]! < 21 ∧ wPt i (sArr i g)[k]! = g (wPt i k) := by
  obtain ⟨m, hm, hme⟩ : g (wPt i k) ∈ wPlane i := hW ▸ ⟨_, wPt_mem i hk, rfl⟩
  rw [sArr_get hk, ← hme, uaPos_wPt hi hm]
  exact ⟨hm, rfl⟩

theorem conj_uaGen (hi : i < 891) {g : Equiv.Perm (Fin 693)} (hg : IsPolarAut g)
    (hW : ⇑g '' wPlane i = wPlane i) {k : ℕ} (hk : k < 21) :
    g * uaGen i k * g⁻¹ = uaGen i (sArr i g)[k]! := by
  rw [uaGen, hg.mul_tvP_mul_inv, ← (sArr_spec hi hW hk).2]
  rfl

theorem collAmat_lt {s : Array ℕ} (hs : ∀ j < 9, s[j]! < 21) (a : ℕ) : collAmat s a < 512 := by
  rw [collAmat, collAmatN_eq]
  exact bitSum_lt (m := 9) a (N := 9) (fun j hj => uaCo_lt (hs j hj)) 9 le_rfl

theorem conj_uaPsi (hi : i < 891) {g : Equiv.Perm (Fin 693)} (hg : IsPolarAut g)
    (hW : ⇑g '' wPlane i = wPlane i) (a : ℕ) :
    g * uaPsi i a * g⁻¹ = uaPsi i (collAmat (sArr i g) a) := by
  rw [uaPsi, conj_bitProd, collAmat, collAmatN_eq,
    bitProd_congr a 9 (g' := fun j => uaPsi i uaCo[(sArr i g)[j]!]!) fun j hj => by
      rw [conj_uaGen hi hg hW (by omega), uaPsi_co hi (sArr_spec hi hW (by omega)).1]]
  exact bitProd_hom (uaPsi_zero i) (uaPsi_xor hi) _ a 9

theorem collAdm_sArr (hi : i < 891) {g : Equiv.Perm (Fin 693)} (hg : IsPolarAut g)
    (hW : ⇑g '' wPlane i = wPlane i) : collAdm (sArr i g) = true := by
  unfold collAdm
  simp only [Bool.and_eq_true, beq_iff_eq, allIn_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    bne_iff_ne]
  refine ⟨⟨⟨sArr_size i g, fun k _ hk => (sArr_spec hi hW hk).1⟩, fun k _ hk l _ hl => ?_⟩,
    fun k _ hk => ?_⟩
  · by_cases hkl : k = l
    · exact Or.inl hkl
    · refine Or.inr fun he => hkl ?_
      have := (sArr_spec hi hW hk).2
      rw [he, (sArr_spec hi hW hl).2] at this
      exact wPt_inj hi hk hl (g.injective this.symm)
  · refine uaPsi_inj hi (collAmat_lt (fun j hj => (sArr_spec hi hW (by omega)).1) _)
      (uaCo_lt (sArr_spec hi hW hk).1) ?_
    rw [← conj_uaPsi hi hg hW, uaPsi_co hi hk, conj_uaGen hi hg hW hk,
      uaPsi_co hi (sArr_spec hi hW hk).1]

theorem sArr_getElem {g : Equiv.Perm (Fin 693)} {k : ℕ} (hk : k < (sArr i g).size) :
    (sArr i g)[k] = uaPos (uaPts[i]!) (g (wPt i k)).val := by
  simp only [sArr, Array.getElem_ofFn]

theorem collComp_getElem {s t : Array ℕ} {k : ℕ} (hk : k < (collComp s t).size) :
    (collComp s t)[k] = s[t[k]!]! := by
  simp only [collComp, Array.getElem_ofFn]

theorem collComp_size (s t : Array ℕ) : (collComp s t).size = 21 := by
  rw [collComp, Array.size_ofFn]

theorem sArr_mul (hi : i < 891) (g : Equiv.Perm (Fin 693)) {h : Equiv.Perm (Fin 693)}
    (hh : ⇑h '' wPlane i = wPlane i) : sArr i (g * h) = collComp (sArr i g) (sArr i h) := by
  refine Array.ext (by rw [sArr_size, collComp_size]) fun k hk _ => ?_
  have hk' : k < 21 := by rwa [sArr_size] at hk
  rw [sArr_getElem, collComp_getElem, sArr_get (sArr_spec hi hh hk').1,
    (sArr_spec hi hh hk').2, Equiv.Perm.mul_apply]

theorem sArr_one (hi : i < 891) : sArr i 1 = collId := by
  refine Array.ext (by rw [sArr_size, collId, Array.size_ofFn]) fun k hk _ => ?_
  have hk' : k < 21 := by rwa [sArr_size] at hk
  rw [sArr_getElem, Equiv.Perm.one_apply, uaPos_wPt hi hk']
  simp only [collId, Array.getElem_ofFn]

theorem sArr_eq_iff (hi : i < 891) {g h : Equiv.Perm (Fin 693)}
    (hg : ⇑g '' wPlane i = wPlane i) (hh : ⇑h '' wPlane i = wPlane i) :
    sArr i g = sArr i h ↔ ∀ p ∈ wPlane i, g p = h p := by
  constructor
  · rintro he _ ⟨k, hk, rfl⟩
    rw [← (sArr_spec hi hg hk).2, ← (sArr_spec hi hh hk).2, he]
  · intro H
    refine Array.ext (by rw [sArr_size, sArr_size]) fun k hk _ => ?_
    have hk' : k < 21 := by rwa [sArr_size] at hk
    rw [sArr_getElem, sArr_getElem, H _ (wPt_mem i hk')]

end Conj

end CFSG.LargeExtraspecial.SMod20
