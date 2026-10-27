module

public import CFSG.ClassicalInvolution.Q3.TL3T43
public import CFSG.ClassicalInvolution.Q3.AE.Conj
import CFSG.ClassicalInvolution.Q3.TL4SecIdAE5A
import CFSG.ClassicalInvolution.Q3.TL4Mdl117Brg

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE

namespace AE5Q8

open CFSG.ClassicalInvolution.Q3.AE.Wr

private theorem natCard_aeSub_five : Nat.card (aeSub 5) = 960 := by
  have h : Nat.card (aeSub 5) = (Finset.univ.filter fun a : Wr 5 =>
      wsum a = 0 ∧ Equiv.Perm.sign a.perm = 1).card := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    rfl
  rw [h]
  decide +kernel

theorem card_aeModel_five : Nat.card (TL4.aeModel 5) = 960 := by
  have hinj : Set.InjOn (mkQ 5) (aeSub 5 : Set (Wr 5)) := fun a ha b hb h =>
    TL4.AE5.eq_of_mkQ_eq (by rw [ha.1, hb.1]) h
  have h1 : Nat.card (TL4.aeModel 5) = Nat.card ↑((mkQ 5) '' (aeSub 5 : Set (Wr 5))) := by
    rw [TL4.aeModel, ← Subgroup.coe_map]
    rfl
  rw [h1, Nat.card_image_of_injOn hinj]
  exact natCard_aeSub_five

private theorem comm_of_mem {G : Type*} [Group G] {X : Subgroup G} {z : G}
    (hz : IsUniqueInvolution X z) {g : G} (hg : g ∈ X) : g * z = z * g := by
  have hw : g * z * g⁻¹ ∈ X := X.mul_mem (X.mul_mem hg hz.mem) (X.inv_mem hg)
  have hsq : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  rcases hz.unique _ hw hsq with h | h
  · exact absurd (by simpa using h) hz.ne_one
  · calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [h]

private theorem sq_eq_of_noncomm {G : Type*} [Group G] {X : Subgroup G} {z : G}
    (hz : IsUniqueInvolution X z) (h8 : Nat.card X = 8) {w u : G} (hw : w ∈ X) (hu : u ∈ X)
    (hwu : w * u ≠ u * w) : w * w = z := by
  haveI : Finite X := Nat.finite_of_card_ne_zero (by omega)
  have hw1 : w ≠ 1 := fun h => hwu (by rw [h, one_mul, mul_one])
  have hwz : w ≠ z := fun h => hwu (by rw [h]; exact (comm_of_mem hz hu).symm)
  have h8w : w ^ 8 = 1 := by
    have h1 : (⟨w, hw⟩ : X) ^ Nat.card X = 1 := pow_card_eq_one'
    rw [h8] at h1
    exact congrArg Subtype.val h1
  have h44 : w ^ 4 * w ^ 4 = 1 := by rw [← pow_add]; exact h8w
  rcases hz.unique _ (X.pow_mem hw 4) h44 with h4 | h4
  · have hww : (w * w) * (w * w) = 1 := by
      calc (w * w) * (w * w) = w ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := h4
    rcases hz.unique _ (X.mul_mem hw hw) hww with h | h
    · rcases hz.unique w hw h with h' | h'
      · exact absurd h' hw1
      · exact absurd h' hwz
    · exact h
  · exfalso
    have hn : ¬ w ^ 2 ^ 2 = 1 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, h4]
      exact hz.ne_one
    have hf : w ^ 2 ^ (2 + 1) = 1 := by
      rw [show (2 : ℕ) ^ (2 + 1) = 8 by norm_num]
      exact h8w
    have hord : orderOf w = 8 := by
      rw [orderOf_eq_prime_pow (p := 2) (n := 2) hn hf]
      norm_num
    have hle : Subgroup.zpowers w ≤ X := (Subgroup.zpowers_le).mpr hw
    have heq : Subgroup.zpowers w = X :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [Nat.card_zpowers, hord, h8]))
    have hu' : u ∈ Subgroup.zpowers w := by rw [heq]; exact hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu'
    exact hwu (Commute.self_zpow w k).eq

private theorem eq_of_mem_inf {G : Type*} [Group G] {X Y : Subgroup G} (hX : Nat.card X = 8)
    (hY : Nat.card Y = 8) {x y : G} (hxX : x ∈ X) (hyX : y ∈ X) (hxY : x ∈ Y) (hyY : y ∈ Y)
    (hx4 : x ^ 4 = 1) (hx2 : x ^ 2 ≠ 1) (hxy : x * y ≠ y * x) : X = Y := by
  haveI : Finite X := Nat.finite_of_card_ne_zero (by omega)
  haveI : Finite Y := Nat.finite_of_card_ne_zero (by omega)
  have hn : ¬ x ^ 2 ^ 1 = 1 := by
    rw [show (2 : ℕ) ^ 1 = 2 by norm_num]
    exact hx2
  have hf : x ^ 2 ^ (1 + 1) = 1 := by
    rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]
    exact hx4
  have hord : orderOf x = 4 := by
    rw [orderOf_eq_prime_pow (p := 2) (n := 1) hn hf]
    norm_num
  have hKX : X ⊓ Y ≤ X := inf_le_left
  have hKY : X ⊓ Y ≤ Y := inf_le_right
  have hxK : x ∈ X ⊓ Y := ⟨hxX, hxY⟩
  have hyK : y ∈ X ⊓ Y := ⟨hyX, hyY⟩
  haveI : Finite (X ⊓ Y : Subgroup G) :=
    Finite.of_injective (Subgroup.inclusion hKX) (Subgroup.inclusion_injective hKX)
  have h4K : 4 ∣ Nat.card (X ⊓ Y : Subgroup G) := by
    have h1 : orderOf (⟨x, hxK⟩ : (X ⊓ Y : Subgroup G)) = 4 := by
      rw [← hord]
      exact Subgroup.orderOf_mk x hxK
    rw [← h1]
    exact orderOf_dvd_natCard _
  have hKle : Nat.card (X ⊓ Y : Subgroup G) ≤ 8 := by
    rw [← hX]
    exact Nat.le_of_dvd (by omega) (Subgroup.card_dvd_of_le hKX)
  have hKpos : 0 < Nat.card (X ⊓ Y : Subgroup G) := Nat.card_pos
  have hK : Nat.card (X ⊓ Y : Subgroup G) = 4 ∨ Nat.card (X ⊓ Y : Subgroup G) = 8 := by
    obtain ⟨k, hk⟩ := h4K
    omega
  rcases hK with hK | hK
  · exfalso
    have hle : Subgroup.zpowers x ≤ X ⊓ Y := (Subgroup.zpowers_le).mpr hxK
    have heq : Subgroup.zpowers x = X ⊓ Y :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hK, Nat.card_zpowers, hord]))
    have hy' : y ∈ Subgroup.zpowers x := by rw [heq]; exact hyK
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
    exact hxy (Commute.self_zpow x k).eq
  · have e1 : X ⊓ Y = X := Subgroup.eq_of_le_of_card_ge hKX (le_of_eq (by rw [hK, hX]))
    have e2 : X ⊓ Y = Y := Subgroup.eq_of_le_of_card_ge hKY (le_of_eq (by rw [hK, hY]))
    exact e1.symm.trans e2

private def vecOfNat (k : ℕ) : Fin 5 → ZMod 2 := fun i => if (k / 2 ^ i.val) % 2 = 1 then 1 else 0

private def evenVecs : List (Fin 5 → ZMod 2) :=
  ((List.range 32).map vecOfNat).filter fun v => decide (∑ i, v i = 0)

private def permAll : List (Equiv.Perm (Fin 5)) :=
  [0, 1, 2, 3, 4].flatMap fun a => [1, 2, 3, 4].flatMap fun b => [2, 3, 4].flatMap fun c =>
    [3, 4].map fun d => Equiv.swap 0 a * Equiv.swap 1 b * Equiv.swap 2 c * Equiv.swap 3 d

private def permA5 : List (Equiv.Perm (Fin 5)) :=
  permAll.filter fun σ => decide (Equiv.Perm.sign σ = 1)

private def aeList : List (Wr 5) := permA5.flatMap fun σ => evenVecs.map fun v => ⟨v, σ⟩

private def o4List : List (Wr 5) :=
  aeList.filter fun x => decide (x * x ≠ 1) && decide ((x * x) * (x * x) = 1)

private def memP (p : Fin 5) (b : Bool) : List (Wr 5) :=
  Certificates.AE117.memLC (p.succAbove 0) (p.succAbove 1) (p.succAbove 2) (p.succAbove 3) b

private theorem evenVecs_complete : ∀ v : Fin 5 → ZMod 2, ∑ i, v i = 0 → v ∈ evenVecs := by
  decide +kernel

private theorem permA5_complete :
    ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → σ ∈ permA5 := by
  decide +kernel

private theorem mem_aeList {x : Wr 5} (hx : x ∈ aeSub 5) : x ∈ aeList := by
  have h1 := evenVecs_complete x.vec hx.1
  have h2 := permA5_complete x.perm hx.2
  simp only [aeList, List.mem_flatMap, List.mem_map]
  exact ⟨x.perm, h2, x.vec, h1, rfl⟩

private theorem mem_o4List {x : Wr 5} (hx : x ∈ aeSub 5) (h1 : x * x ≠ 1)
    (h2 : (x * x) * (x * x) = 1) : x ∈ o4List := by
  refine List.mem_filter.mpr ⟨mem_aeList hx, ?_⟩
  simp [h1, h2]

private def pairCheck : Bool :=
  o4List.all fun x => o4List.all fun y =>
    !(decide (x * x = y * y) && decide ((x * y) * (x * y) = x * x) && decide (x * y ≠ y * x)) ||
      (List.finRange 5).any fun p => [true, false].any fun b =>
        decide (x ∈ memP p b) && decide (y ∈ memP p b)

set_option maxHeartbeats 0 in
private theorem pairCheck_true : pairCheck = true := by
  decide +kernel

private theorem q8_check : ∀ x ∈ o4List, ∀ y ∈ o4List, x * x = y * y →
    (x * y) * (x * y) = x * x → x * y ≠ y * x →
    ∃ p : Fin 5, ∃ b : Bool, x ∈ memP p b ∧ y ∈ memP p b := by
  intro x hx y hy h1 h2 h3
  have h := pairCheck_true
  simp only [pairCheck, List.all_eq_true] at h
  have h' := h x hx y hy
  rw [Bool.or_eq_true] at h'
  rcases h' with h' | h'
  · rw [decide_eq_true h1, decide_eq_true h2, decide_eq_true h3] at h'
    exact absurd h' (by decide)
  · rw [List.any_eq_true] at h'
    obtain ⟨p, -, hp⟩ := h'
    rw [List.any_eq_true] at hp
    obtain ⟨b, -, hb⟩ := hp
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hb
    exact ⟨p, b, hb.1, hb.2⟩

private theorem card_erase_univ (p : Fin 5) : (Finset.univ.erase p).card = 4 := by
  simp

private theorem mem_memAt_of_mem_memP (p : Fin 5) (b : Bool) {x : Wr 5} (hx : x ∈ memP p b) :
    x ∈ memAt (Finset.univ.erase p) (card_erase_univ p) b := by
  have h := card_erase_univ p
  have hemb : ∀ i, emb (Finset.univ.erase p) h i = p.succAbove i := fun i =>
    (congrFun (Finset.orderEmbOfFin_unique h (f := p.succAbove)
      (fun x => by simp [Fin.succAbove_ne]) (Fin.strictMono_succAbove p)) i).symm
  unfold memP at hx
  rw [← hemb 0, ← hemb 1, ← hemb 2, ← hemb 3, TL4.Mdl117.memLC_eq] at hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  refine (TL4.AE5.mem_memAt_iff _ h).mpr ⟨a, ?_, rfl⟩
  cases b <;> simpa [TL4.AE5.localList] using ha

theorem eq_memBar_of_q8 {X : Subgroup (AEQ 5)} (hX : X ≤ TL4.aeModel 5) (h8 : Nat.card X = 8)
    {z : AEQ 5} (hz : IsUniqueInvolution X z) (hnab : ∃ x ∈ X, ∃ y ∈ X, x * y ≠ y * x) :
    ∃ (α : Finset (Fin 5)) (h : α.card = 4) (b : Bool), X = memBar α h b := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hnab
  have hxx : x * x = z := sq_eq_of_noncomm hz h8 hx hy hxy
  have hyy : y * y = z := sq_eq_of_noncomm hz h8 hy hx (Ne.symm hxy)
  have hxyxy : (x * y) * (x * y) = z := by
    refine sq_eq_of_noncomm hz h8 (X.mul_mem hx hy) hx ?_
    intro h
    apply hxy
    have h' : x * (y * x) = x * (x * y) := by rw [← mul_assoc]; exact h
    exact (mul_left_cancel h').symm
  obtain ⟨a, ha, rfl⟩ := hX hx
  obtain ⟨b, hb, rfl⟩ := hX hy
  have e1 : a * a = b * b := by
    apply TL4.AE5.eq_of_mkQ_eq
    · rw [wsum_mul, wsum_mul, ha.1, hb.1]
    · rw [map_mul, map_mul, hxx, hyy]
  have e2 : (a * b) * (a * b) = a * a := by
    apply TL4.AE5.eq_of_mkQ_eq
    · simp [wsum_mul, ha.1, hb.1]
    · calc mkQ 5 ((a * b) * (a * b)) = z := by simpa only [map_mul] using hxyxy
        _ = mkQ 5 (a * a) := by simpa only [map_mul] using hxx.symm
  have e3 : a * a ≠ 1 := by
    intro h
    apply hz.ne_one
    rw [← hxx, ← map_mul, h, map_one]
  have e4 : (a * a) * (a * a) = 1 := by
    apply TL4.AE5.eq_of_mkQ_eq
    · simp [wsum_mul, ha.1, wsum_one]
    · rw [map_mul, map_mul, hxx, hz.sq, map_one]
  have e5 : a * b ≠ b * a := fun h => hxy (by rw [← map_mul, ← map_mul, h])
  obtain ⟨p, c, hap, hbp⟩ := q8_check a (mem_o4List ha e3 e4) b
    (mem_o4List hb (by rw [← e1]; exact e3) (by rw [← e1]; exact e4)) e1 e2 e5
  have h := card_erase_univ p
  refine ⟨Finset.univ.erase p, h, c, ?_⟩
  refine eq_of_mem_inf h8 (natCard_memBar (by norm_num) _ h c) hx hy
    ⟨a, mem_memAt_of_mem_memP p c hap, rfl⟩ ⟨b, mem_memAt_of_mem_memP p c hbp, rfl⟩ ?_ ?_ hxy
  · rw [show mkQ 5 a ^ 4 = (mkQ 5 a * mkQ 5 a) * (mkQ 5 a * mkQ 5 a) by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc], hxx, hz.sq]
  · rw [pow_two, hxx]
    exact hz.ne_one

private theorem exists_conj_twin (β : Finset (Fin 5)) (hβ : β.card = 4) (c b' : Bool) :
    ∃ g ∈ TL4.aeModel 5, conjSub g (memBar β hβ c) = memBar β hβ b' := by
  obtain ⟨w, hw, hmap⟩ := exists_conj_memBar (by norm_num : 5 ≤ 5) β hβ ⊤
  have hmem : mkQ 5 w ∈ TL4.aeModel 5 := ⟨w, hw.1, rfl⟩
  have hmap' : conjSub (mkQ 5 w) (memBar β hβ true) = memBar β hβ false := hmap
  cases c <;> cases b'
  · exact ⟨1, one_mem _, conjSub_one _⟩
  · refine ⟨(mkQ 5 w)⁻¹, inv_mem hmem, ?_⟩
    rw [← hmap', conjSub_inv_conjSub]
  · exact ⟨mkQ 5 w, hmem, hmap'⟩
  · exact ⟨1, one_mem _, conjSub_one _⟩

private theorem alt_trans_four : ∀ α α' : Finset (Fin 5), α.card = 4 → α'.card = 4 →
    ∃ σ : alternatingGroup (Fin 5), α.map (σ : Equiv.Perm (Fin 5)).toEmbedding = α' := by
  decide +kernel

theorem exists_conj_memBar_memBar (α : Finset (Fin 5)) (h : α.card = 4) (b : Bool)
    (α' : Finset (Fin 5)) (h' : α'.card = 4) (b' : Bool) :
    ∃ x ∈ TL4.aeModel 5, (memBar α h b).map (MulAut.conj x).toMonoidHom = memBar α' h' b' := by
  obtain ⟨σ, hσ⟩ := alt_trans_four α α' h h'
  obtain ⟨c, hc⟩ := exists_conj_ofPerm_memBar (σ : Equiv.Perm (Fin 5)) α h b
  have hσe : ofPerm (σ : Equiv.Perm (Fin 5)) ∈ aeSub 5 :=
    (ofPerm_mem_aeSubOver (A := ⊤) (Subgroup.mem_top _)
      (Equiv.Perm.mem_alternatingGroup.mp σ.2)).1
  have hσm : mkQ 5 (ofPerm (σ : Equiv.Perm (Fin 5))) ∈ TL4.aeModel 5 := ⟨_, hσe, rfl⟩
  subst hσ
  obtain ⟨g, hg, hgc⟩ := exists_conj_twin _ h' c b'
  refine ⟨g * mkQ 5 (ofPerm (σ : Equiv.Perm (Fin 5))), mul_mem hg hσm, ?_⟩
  have h1 : conjSub (mkQ 5 (ofPerm (σ : Equiv.Perm (Fin 5)))) (memBar α h b) =
      memBar _ h' c := hc
  show conjSub (g * mkQ 5 (ofPerm (σ : Equiv.Perm (Fin 5)))) (memBar α h b) = _
  rw [conjSub_mul, h1, hgc]

end AE5Q8

namespace A5

private theorem existsUnique_fixed_ex : ∀ u v : alternatingGroup (Fin 5), u ≠ 1 → v ≠ 1 →
    u ≠ v → u * u = 1 → v * v = 1 → u * v = v * u →
    ∃ γ : Fin 5, (u : Equiv.Perm (Fin 5)) γ = γ ∧ (v : Equiv.Perm (Fin 5)) γ = γ := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
private theorem existsUnique_fixed_uniq : ∀ u v : alternatingGroup (Fin 5), u ≠ 1 → v ≠ 1 →
    u ≠ v → u * u = 1 → v * v = 1 → u * v = v * u →
    ∀ γ δ : Fin 5, ((u : Equiv.Perm (Fin 5)) γ = γ ∧ (v : Equiv.Perm (Fin 5)) γ = γ) →
      ((u : Equiv.Perm (Fin 5)) δ = δ ∧ (v : Equiv.Perm (Fin 5)) δ = δ) → γ = δ := by
  decide +kernel

theorem existsUnique_fixed (u v : alternatingGroup (Fin 5)) (hu : u ≠ 1) (hv : v ≠ 1)
    (huv : u ≠ v) (hu2 : u * u = 1) (hv2 : v * v = 1) (hc : u * v = v * u) :
    ∃! γ : Fin 5, (u : Equiv.Perm (Fin 5)) γ = γ ∧ (v : Equiv.Perm (Fin 5)) γ = γ := by
  obtain ⟨γ, hγ⟩ := existsUnique_fixed_ex u v hu hv huv hu2 hv2 hc
  exact ⟨γ, hγ, fun δ hδ => existsUnique_fixed_uniq u v hu hv huv hu2 hv2 hc δ γ hδ hγ⟩

private theorem exists_cycle_aux : ∀ u v : alternatingGroup (Fin 5), u ≠ 1 → v ≠ 1 →
    u ≠ v → u * u = 1 → v * v = 1 → u * v = v * u →
    ∃ c : alternatingGroup (Fin 5), c * u * c⁻¹ = v ∧ c * v * c⁻¹ = u * v := by
  decide +kernel

theorem exists_cycle (u v : alternatingGroup (Fin 5)) (hu : u ≠ 1) (hv : v ≠ 1)
    (huv : u ≠ v) (hu2 : u * u = 1) (hv2 : v * v = 1) (hc : u * v = v * u) :
    ∃ c : alternatingGroup (Fin 5), c * u * c⁻¹ = v ∧ c * v * c⁻¹ = u * v :=
  exists_cycle_aux u v hu hv huv hu2 hv2 hc

private theorem exists_two_trans_aux : ∀ γ δ γ' δ' : Fin 5, γ ≠ δ → γ' ≠ δ' →
    ∃ g : alternatingGroup (Fin 5), (g : Equiv.Perm (Fin 5)) γ = γ' ∧
      (g : Equiv.Perm (Fin 5)) δ = δ' := by
  decide +kernel

theorem exists_two_trans (γ δ γ' δ' : Fin 5) (h : γ ≠ δ) (h' : γ' ≠ δ') :
    ∃ g : alternatingGroup (Fin 5), (g : Equiv.Perm (Fin 5)) γ = γ' ∧
      (g : Equiv.Perm (Fin 5)) δ = δ' :=
  exists_two_trans_aux γ δ γ' δ' h h'

theorem card_filter_inv_fix (γ : Fin 5) :
    (Finset.univ.filter fun u : alternatingGroup (Fin 5) =>
      u * u = 1 ∧ (u : Equiv.Perm (Fin 5)) γ = γ).card = 4 := by
  revert γ
  decide +kernel

end A5

end CFSG.ClassicalInvolution.Q3.Sec13
