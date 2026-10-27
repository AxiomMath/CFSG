module

public import CFSG.Certificates.Kernel.Hall82K.Linear
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import Certificates.Data.Kernel.Hall82K.Enum
public import Certificates.Data.Kernel.Hall82K.PermK
public import Certificates.Data.Kernel.Hall82K.Bridge

public section

namespace CFSG.KC.Hall82K

open CFSG.ComponentClassification.AS81.Hexa CFSG.ComponentClassification.AS81.HeSylow
open CFSG.Monster.B.Co2 CFSG.RankThree.Native CFSG.KC.Misc.Clos

def addSub : Subgroup (Equiv.Perm (Fin 64)) where
  carrier := {g | ∀ v w, g (xorF v w) = xorF (g v) (g w)}
  mul_mem' {a b} ha hb v w := by
    change a (b (xorF v w)) = xorF (a (b v)) (a (b w))
    rw [hb v w, ha (b v) (b w)]
  one_mem' _ _ := rfl
  inv_mem' {a} ha v w := by
    change a⁻¹ (xorF v w) = xorF (a⁻¹ v) (a⁻¹ w)
    apply a.injective
    rw [ha (a⁻¹ v) (a⁻¹ w)]
    simp

theorem mem_addSub {g : Equiv.Perm (Fin 64)} :
    g ∈ addSub ↔ ∀ v w, g (xorF v w) = xorF (g v) (g w) :=
  Iff.rfl

theorem closEnc : ClosEnc (fun g : addSub => codeL g.1) compL idK where
  enc_one := rfl
  enc_mul a b := by
    change codeL (fun v => a.1 (b.1 v)) = compL (codeL a.1) (codeL b.1)
    rw [compL_codeL a.2]
  inj a b h := by
    refine Subtype.ext (Equiv.ext fun v => Fin.ext ?_)
    have h' : codeL a.1 = codeL b.1 := h
    rw [← apL_codeL a.2 v, h', apL_codeL b.2 v]

theorem band_eq_true82 {a b : Bool} (h : band a b = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem allN_spec82 {p : ℕ → Bool} : ∀ {n : ℕ}, allN p n = true → ∀ k < n, p k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    have h' : band (p n) (allN p n) = true := h
    obtain ⟨h1, h2⟩ := band_eq_true82 h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact allN_spec82 h2 k hk
    · exact h1

theorem permK_spec {c : ℕ} (h : permK c = true) :
    compL c idK = c ∧ (∀ i < 64, apL c i < 64) ∧
      (∀ i < 64, ∀ j < 64, apL c i = apL c j → i = j) ∧
      ∀ i < 64, ∀ j < 64, apL c (i ^^^ j) = apL c i ^^^ apL c j := by
  obtain ⟨h0, h1⟩ := andB_eq_true h
  have h1' := (allN_iff _ _).1 h1
  refine ⟨Nat.eq_of_beq_eq_true h0, fun i hi => Nat.blt_eq.mp (andB_eq_true (h1' i hi)).1,
    fun i hi j hj hij => ?_, fun i hi j hj => ?_⟩
  · have h2 := (allN_iff _ _).1 (andB_eq_true (h1' i hi)).2 j hj
    exact Nat.eq_of_beq_eq_true
      (impB_eq_true (andB_eq_true h2).1 (by rw [hij]; exact Nat.beq_refl _))
  · have h2 := (allN_iff _ _).1 (andB_eq_true (h1' i hi)).2 j hj
    exact Nat.eq_of_beq_eq_true (andB_eq_true h2).2

theorem compL_idK_eq (c : ℕ) (hb : ∀ i < 64, apL c i < 64) :
    compL c idK =
      enc6 (apL c 1) (apL c 2) (apL c 4) (apL c 8) (apL c 16) (apL c 32) := by
  have hf : ∀ s, fld idK s = Nat.land (Nat.shiftRight idK s) 63 := fun _ => rfl
  have e0 : fld idK 0 = 1 := by decide
  have e1 : fld idK 6 = 2 := by decide
  have e2 : fld idK 12 = 4 := by decide
  have e3 : fld idK 18 = 8 := by decide
  have e4 : fld idK 24 = 16 := by decide
  have e5 : fld idK 30 = 32 := by decide
  unfold compL
  rw [e0, e1, e2, e3, e4, e5]
  exact lorTree_eq_enc6 (hb 1 (by norm_num)) (hb 2 (by norm_num)) (hb 4 (by norm_num))
    (hb 8 (by norm_num)) (hb 16 (by norm_num))

theorem permK_sound {c : ℕ} {a : Array ℕ} (hp : permK c = true) (ha : codeArrK c a = true) :
    Rep 64 a (permOfArr 64 a) ∧ permOfArr 64 a ∈ addSub ∧ codeL (permOfArr 64 a) = c ∧
      ∀ v : Fin 64, (permOfArr 64 a v).val = apL c v.val := by
  obtain ⟨hcode, hb, hinj, hadd⟩ := permK_spec hp
  obtain ⟨hs, hv⟩ := band_eq_true82 ha
  have hsz : a.size = 64 := Nat.eq_of_beq_eq_true hs
  have hget : ∀ i < 64, a[i]! = apL c i := by
    intro i hi
    have h := Nat.eq_of_beq_eq_true (allN_spec82 hv i hi)
    rw [← h, getElem!_pos a i (by omega), Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by omega), Option.getD_some]
  have hc : (∀ i < 64, a[i]! < 64) ∧ ∀ i < 64, ∀ j < 64, a[i]! = a[j]! → i = j :=
    ⟨fun i hi => by rw [hget i hi]; exact hb i hi,
      fun i hi j hj hij => hinj i hi j hj (by rw [← hget i hi, ← hget j hj, hij])⟩
  have hrep : Rep 64 a (permOfArr 64 a) := fun x => by
    rw [permOfArr, dite_eq_left hc]
    rfl
  have hval : ∀ v : Fin 64, (permOfArr 64 a v).val = apL c v.val := fun v =>
    (hrep v).symm.trans (hget v.val v.2)
  refine ⟨hrep, fun v w => Fin.ext ?_, ?_, hval⟩
  · rw [hval, val_xorF, val_xorF, hval, hval, hadd _ v.2 _ w.2]
  · rw [codeL, hval, hval, hval, hval, hval, hval]
    exact (compL_idK_eq c hb).symm.trans hcode

theorem enum_sound {a0 a1 : Array ℕ} {g0 g1 N : ℕ} {E PA SG CT : ℕ → ℕ}
    (hz : zipArrK [g0, g1] [a0, a1] = true) (hp0 : permK g0 = true) (hp1 : permK g1 = true)
    (hN : 0 < N) (hchk : ∀ k < N, enumAt g0 g1 N E PA SG CT k = true) :
    Nat.card (grpN 64 [a0, a1]) = N ∧
      (∀ g ∈ grpN 64 [a0, a1], g ∈ addSub ∧ ∃ k < N, codeL g = E k) ∧
      ∀ k < N, ∃ g ∈ grpN 64 [a0, a1], codeL g = E k := by
  have hz' : band (codeArrK g0 a0) (band (codeArrK g1 a1) true) = true := hz
  obtain ⟨hc0, hz1⟩ := band_eq_true82 hz'
  obtain ⟨hc1, -⟩ := band_eq_true82 hz1
  obtain ⟨-, hm0, he0, -⟩ := permK_sound hp0 hc0
  obtain ⟨-, hm1, he1, -⟩ := permK_sound hp1 hc1
  let x0 : addSub := ⟨permOfArr 64 a0, hm0⟩
  let x1 : addSub := ⟨permOfArr 64 a1, hm1⟩
  have hG : ∀ j < [x0, x1].length, gen2 g0 g1 j = codeL ([x0, x1].getD j 1).1 := by
    intro j hj
    rcases j with _ | _ | j
    · exact he0.symm
    · exact he1.symm
    · exact absurd hj (by simp)
  have ht : ∀ k < N, treeAt compL idK (gen2 g0 g1) [x0, x1].length E PA k = true :=
    fun k hk => (andB_eq_true (hchk k hk)).1
  have hs : ∀ k < N, sortAt N E SG k = true :=
    fun k hk => (andB_eq_true (andB_eq_true (hchk k hk)).2).1
  have hcl : ∀ k < N, closedAt compL (gen2 g0 g1) [x0, x1].length N E CT k = true :=
    fun k hk => (andB_eq_true (andB_eq_true (hchk k hk)).2).2
  obtain ⟨-, -, hfull⟩ := clos_card closEnc [x0, x1] hG hN ht hs
  obtain ⟨hcard, hall⟩ := hfull hcl
  have hpart := (clos_card closEnc [x0, x1] hG hN ht hs).1
  set C := Subgroup.closure {g | g ∈ [x0, x1]}
  have hmap : C.map addSub.subtype = grpN 64 [a0, a1] := by
    rw [MonoidHom.map_closure]
    unfold grpN
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_cons, List.mem_nil_iff, or_false,
      permsA]
    constructor
    · rintro ⟨y, hy | hy, rfl⟩
      · exact ⟨0, by simp, by rw [hy]; rfl⟩
      · exact ⟨1, by simp, by rw [hy]; rfl⟩
    · rintro ⟨k, hk, rfl⟩
      have hk' : k < 2 := by simpa using hk
      rcases k with _ | _ | k
      · exact ⟨x0, Or.inl rfl, rfl⟩
      · exact ⟨x1, Or.inr rfl, rfl⟩
      · omega
  refine ⟨?_, ?_, ?_⟩
  · rw [← hmap, Subgroup.card_map_of_injective addSub.subtype_injective, hcard]
  · intro g hg
    rw [← hmap] at hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨k, hk, he⟩ := hall y hy
    exact ⟨y.2, k, hk, he⟩
  · intro k hk
    obtain ⟨y, hy, he⟩ := hpart k hk
    exact ⟨y.1, hmap ▸ Subgroup.mem_map_of_mem _ hy, he⟩

end CFSG.KC.Hall82K
