module

public import CFSG.Certificates.Kernel.LocalQTBaseSProved

public section

namespace CFSG.KC.LQT.BS.Cl

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.BS
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.BS.Pf
open CFSG.QuasithinUnique.K1.SporadicPerm

theorem bfs_closed {n L : Nat} {B : List Nat} {G Gi : List (Array Nat)} {Ul : List (List Nat)}
    (fuel : Nat) (hGil : Gi.length = G.length)
    (hinv : ∀ j < G.length, ∀ q < n, img Gi[j]! (img G[j]! q) = q)
    (hUv : ∀ T ∈ Ul, Val n L T) (hclo : ∀ T ∈ Ul, ∀ s ∈ G, applyTab s T ∈ Ul)
    (hkey : ∀ T ∈ Ul, ∀ V ∈ Ul, keyNat n B.length T = keyNat n B.length V → T = V)
    (hoU : ptsOf B G ∈ Ul) (hUnd : Ul.Nodup)
    (hreach : ∀ A : List (List Nat), ptsOf B G ∈ A →
      (∀ T ∈ A, T ∈ Ul → ∀ s ∈ G, applyTab s T ∈ A) → ∀ T ∈ Ul, T ∈ A)
    (hfuel : Ul.length ≤ fuel) :
    BaseEnumOK n B G Gi (bfsEnumB n B G Gi fuel).1 (bfsEnumB n B G Gi fuel).2.1
      (bfsEnumB n B G Gi fuel).2.2 ∧
    (bfsEnumB n B G Gi fuel).1.size = Ul.length ∧
    ∀ T, T ∈ (bfsEnumB n B G Gi fuel).1.toList ↔ T ∈ Ul := by
  have hS0 : BInv n B.length G Ul (ptsOf B G) (#[ptsOf B G], #[0],
      (∅ : Std.HashMap Nat Nat).insert (keyNat n B.length (ptsOf B G)) 0) := by
    have hget : ∀ i < 1, (#[ptsOf B G] : Array (List Nat))[i]! = ptsOf B G := by
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      rfl
    refine ⟨rfl, by simp, rfl, fun T' hT' => ?_, fun y => ?_, fun i hi => ?_, fun i hi hi0 => ?_⟩
    · simp only [List.mem_singleton] at hT'
      rw [hT']
      exact hoU
    · simp only [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false,
        beq_iff_eq]
      constructor
      · rintro rfl
        exact ⟨0, by simp, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        rfl
    · have hi' : i < 1 := by simpa using hi
      rw [hget i hi']
      simp only [Std.HashMap.getD_insert, beq_self_eq_true, ite_true]
      omega
    · have hi' : i < 1 := by simpa using hi
      omega
  obtain ⟨hcf, hdone⟩ := loop_done hclo fuel 0 _ hS0 (Nat.zero_le _)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (by omega)
  generalize hSf : bfsLoopB n B.length G fuel 0 (#[ptsOf B G], #[0],
    (∅ : Std.HashMap Nat Nat).insert (keyNat n B.length (ptsOf B G)) 0) = S at hcf hdone
  have hbe : bfsEnumB n B G Gi fuel = (S.1, S.2.1, (List.range S.1.size).foldl (fun acc i =>
      (G ++ Gi).foldl (fun acc' s =>
        acc'.push (S.2.2.getD (keyNat n B.length (applyTab s S.1[i]!)) 0)) acc) #[]) := by
    simp only [bfsEnumB, hSf]
  have hcf' := hcf
  obtain ⟨hps, hpos, h0, hSU, hmc, hmgS, hpar⟩ := hcf'
  have hv : ∀ T' ∈ S.1.toList, Val n L T' := fun T' hT' => hUv T' (hSU T' hT')
  have hfind : ∀ i < S.1.size, ∀ s ∈ G, ∃ k' < S.1.size, S.1[k']! = applyTab s S.1[i]! := by
    intro i hi s hs
    obtain ⟨k', hk', e⟩ := (hmc _).1 (hdone i hi _ hs)
    exact ⟨k', hk', hkey _ (hSU _ (get_mem hk')) _ (hclo _ (hSU _ (get_mem hi)) _ hs) e⟩
  have hall : ∀ T ∈ Ul, T ∈ S.1.toList := by
    apply hreach
    · rw [← h0]
      exact get_mem hpos
    · intro T hT _ s hs
      obtain ⟨i, hi, rfl⟩ := mem_idx hT
      obtain ⟨k', hk', e⟩ := hfind i hi s hs
      rw [← e]
      exact get_mem hk'
  have hsize : S.1.size = Ul.length := by
    apply Nat.le_antisymm (size_le hcf)
    have := (hUnd.subperm hall).length_le
    simpa using this
  rw [hbe]
  dsimp only
  have hclget : ∀ i < S.1.size, ∀ j < (G ++ Gi).length,
      ((List.range S.1.size).foldl (fun acc i => (G ++ Gi).foldl (fun acc' s =>
        acc'.push (S.2.2.getD (keyNat n B.length (applyTab s S.1[i]!)) 0)) acc)
        (#[] : Array Nat))[i * (G.length + Gi.length) + j]! =
      S.2.2.getD (keyNat n B.length (applyTab (G ++ Gi)[j]! S.1[i]!)) 0 := by
    intro i hi j hj
    rw [arr_getN, cl_fold, ← List.length_append]
    exact (flatMap_getD (G ++ Gi) _ S.1.size).2 i hi j hj
  have hidx : ∀ i < S.1.size, ∀ {s : Array Nat} {k' : Nat}, k' < S.1.size →
      S.1[k']! = applyTab s S.1[i]! →
      S.2.2.getD (keyNat n B.length (applyTab s S.1[i]!)) 0 = k' := by
    intro i _ s k' hk' e
    rw [← e]
    exact hmgS k' hk'
  refine ⟨⟨hpos, h0, hps, hpar, keys_nodupB hcf, fun i hi j hj => ?_, fun i hi j hj => ?_⟩,
    hsize, fun T => ⟨fun h => hSU T h, fun h => hall T h⟩⟩
  · have hs : G[j]! ∈ G := by rw [getElem!_pos G j hj]; exact List.getElem_mem _
    obtain ⟨k', hk', e⟩ := hfind i hi _ hs
    rw [hclget i hi j (by simp; omega), getBang_append_left hj, hidx i hi hk' e]
    exact ⟨hk', e⟩
  · have hjG : j < G.length := by omega
    have hs : G[j]! ∈ G := by rw [getElem!_pos G j hjG]; exact List.getElem_mem _
    have hmem : applyTab Gi[j]! S.1[i]! ∈ S.1.toList := by
      apply closed_inv (s := G[j]!) (n := n)
      · exact hinv j hjG
      · exact fun U hU => (hv U hU).2
      · intro U hU
        obtain ⟨i', hi', rfl⟩ := mem_idx hU
        obtain ⟨k', hk', e⟩ := hfind i' hi' _ hs
        rw [← e]
        exact get_mem hk'
      · exact get_mem hi
    obtain ⟨k', hk', e⟩ := mem_idx hmem
    rw [Nat.add_assoc, hclget i hi _ (by simp; omega), getBang_append_right hj,
      hidx i hi hk' e]
    exact ⟨hk', e⟩

end CFSG.KC.LQT.BS.Cl

end
