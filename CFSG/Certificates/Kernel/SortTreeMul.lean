module

public import CFSG.Certificates.Kernel.SortTreeArr

public section

namespace CFSG.KC.SortTree

open CFSG.KC.Bfs CFSG.Monster.B.TwoA.Census CFSG.KLie.CT

@[expose] noncomputable def mapDig (G : ℕ) (m : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => nat_lit 0)
    (fun _ ih c p =>
      Nat.add (Nat.mul p (fget G (Nat.mod c 24) 5)) (ih (Nat.div c 24) (Nat.mul p 24)))
    m

@[expose] noncomputable def amulK (G c : ℕ) : ℕ := mapDig G 24 c 1

theorem mapDig_ofDigits (G : ℕ) : ∀ L : List ℕ, (∀ x ∈ L, x < 24) → ∀ p,
    mapDig G L.length (Nat.ofDigits 24 L) p = p * Nat.ofDigits 24 (L.map fun d => fget G d 5)
  | [], _, p => by simp [mapDig]
  | d :: L, h, p => by
    have hd : d < 24 := h d (by simp)
    change Nat.add (Nat.mul p (fget G (Nat.mod (Nat.ofDigits 24 (d :: L)) 24) 5))
      (mapDig G L.length (Nat.div (Nat.ofDigits 24 (d :: L)) 24) (Nat.mul p 24)) = _
    have e1 : Nat.mod (Nat.ofDigits 24 (d :: L)) 24 = d := by
      change (d + 24 * Nat.ofDigits 24 L) % 24 = d
      omega
    have e2 : Nat.div (Nat.ofDigits 24 (d :: L)) 24 = Nat.ofDigits 24 L := by
      change (d + 24 * Nat.ofDigits 24 L) / 24 = _
      omega
    rw [e1, e2, mapDig_ofDigits G L (fun x hx => h x (by simp [hx])), List.map_cons,
      Nat.ofDigits_cons]
    simp only [Nat.add_eq, Nat.mul_eq]
    ring

theorem amulK_eq {g x : Array ℕ} (hg : PermArr g = true) (hx : PermArr x = true) :
    amulK (CFSG.KC.U6Orb.packL 5 g.toList) (akey x) = akey (amul g x) := by
  have hl := PermArr_toList_lt hx
  have hlen : x.toList.length = 24 := by rw [Array.length_toList, PermArr_size hx]
  have e := mapDig_ofDigits (CFSG.KC.U6Orb.packL 5 g.toList) x.toList hl 1
  rw [hlen, one_mul] at e
  have e2 : amulK (CFSG.KC.U6Orb.packL 5 g.toList) (akey x) =
      mapDig (CFSG.KC.U6Orb.packL 5 g.toList) 24 (Nat.ofDigits 24 x.toList) 1 := rfl
  rw [e2, e, akey, amul, Array.toList_map]
  exact congrArg (Nat.ofDigits 24) (List.map_congr_left fun d hd => fget_perm hg (hl d hd))

theorem bfsCert_tree_mem {act : Array ℕ → Array ℕ → Array ℕ} {gens : Array (Array ℕ)}
    {root : Array ℕ} {actN : ℕ → ℕ → ℕ} {rec : ℕ → ℕ} {E : ℕ → ℕ → ℕ}
    {n wv wl wp B C B' C' fuel : ℕ}
    (hact : ∀ k < gens.size, ∀ x, PermArr x = true → PermArr (act gens[k]! x) = true)
    (hcode : ∀ k < gens.size, ∀ x, PermArr x = true → actN k (akey x) = akey (act gens[k]! x))
    (hroot : PermArr root = true) (hn : 0 < n) (hfuel : n ≤ fuel)
    (hT : treeOK actN gens.size (fun _ => true) (akey root) rec n wv wl wp B C = true)
    (hE : closeOK actN gens.size rec E n wv B' C' = true) :
    certOK act gens root (bfsCert act gens root fuel) = true ∧
      (bfsCert act gens root fuel).pts.size = n ∧
      (∀ x, x ∈ (bfsCert act gens root fuel).pts ↔
        PermArr x = true ∧ ∃ i < n, valF wv (rec i) = akey x) ∧
      ((bfsCert act gens root fuel).pts.toList.map akey).Nodup := by
  obtain ⟨S', hS', hcard, -, -, hmem⟩ := orbit_sound hn hT hE
  obtain ⟨hS, hc, hv⟩ := orbit_code (act := fun k x => act gens[k]! x)
    (valid := fun x => PermArr x = true) (key := akey) (dec := decK)
    (fun a ha => decK_akey ha) hact hcode hroot hS'
  obtain ⟨h1, h2, h3, h4⟩ := bfsCert_spec (fuel := fuel) _ hS hv (by rw [hc, hcard]; exact hfuel)
  refine ⟨h1, h3.trans (hc.trans hcard), fun x => ?_, h4⟩
  rw [h2]
  constructor
  · intro h
    obtain ⟨c, hcS, rfl⟩ := Finset.mem_image.1 h
    have hrc := reach_code (act := fun k x => act gens[k]! x) (valid := fun x => PermArr x = true)
      (fun a ha => decK_akey ha) hact hcode hroot ((hS' c).2 hcS)
    obtain ⟨i, hi, e⟩ := (hmem c).1 hcS
    exact ⟨hrc.1, i, hi, e.trans hrc.2.2.symm⟩
  · rintro ⟨hx, i, hi, e⟩
    exact Finset.mem_image.2 ⟨akey x, (hmem _).2 ⟨i, hi, e⟩, decK_akey hx⟩

end CFSG.KC.SortTree

end
