module

public import CFSG.Certificates.Kernel.Spor.NFDecode
public import CFSG.Certificates.Kernel.Spor.ConjSearch3Spec

public section

namespace CFSG.KS.Raw.CS3

open CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KS.Raw.Dec

theorem toList_get (base : Array Nat) (t : Nat) : base.toList[t]! = base[t]! := by
  by_cases ht : t < base.size
  · rw [getElem!_pos base.toList t (by simpa using ht), getElem!_pos base t ht, Array.getElem_toList]
  · rw [getElem!_neg base.toList t (by simpa using ht), getElem!_neg base t ht]

theorem coords3_of_agr {n : Nat} {L : Array Level} {base : Array Nat}
    (hL : LvOK n L base.toList) (h3 : 3 ≤ L.size) {g : Array Nat} {x : Tri} (hx : InR L x)
    (hg : Agr n L g x) : coords3 n L base g = x := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨ha, hb, hc⟩ := hx
  simp only at ha hb hc
  have bs : ∀ t, base.toList[t]! = base[t]! := toList_get base
  have hbl : ∀ t < 3, base[t]! < n := fun t ht => by
    simpa only [bs] using hL.blt t (by omega)
  have fix : ∀ i < 3, ∀ k < L[i]!.pts.size, ∀ m < i, (L[i]!.tr[k]!)[base[m]!]! = base[m]! :=
    fun i hi k hk m hm => by
      have := hL.fix i (by omega) k hk m hm
      simpa only [bs] using this
  have root : ∀ i < 3, ∀ k < L[i]!.pts.size, (L[i]!.tr[k]!)[base[i]!]! = L[i]!.pts[k]! :=
    fun i hi k hk => by
      have := hL.root i (by omega) k hk
      simpa only [bs] using this
  have trlt : ∀ i < 3, ∀ k < L[i]!.pts.size, ∀ y < n, (L[i]!.tr[k]!)[y]! < n :=
    fun i hi k hk y hy => hL.trlt i (by omega) k hk y hy
  have inv : ∀ i < 3, ∀ k < L[i]!.pts.size, ∀ y < n, (L[i]!.trInv[k]!)[(L[i]!.tr[k]!)[y]!]! = y :=
    fun i hi k hk y hy => hL.inv i (by omega) k hk y hy
  have pos : ∀ i < 3, ∀ k < L[i]!.pts.size, L[i]!.pos[L[i]!.pts[k]!]! = k :=
    fun i hi k hk => hL.pos i (by omega) k hk
  have g0 : g[base[0]!]! = L[0]!.pts[a]! := by
    rw [hg _ (hbl 0 (by norm_num)), tr3, fix 2 (by norm_num) c hc 0 (by norm_num),
      fix 1 (by norm_num) b hb 0 (by norm_num), root 0 (by norm_num) a ha]
  have hc1 := trlt 2 (by norm_num) c hc _ (hbl 1 (by norm_num))
  have hc2 := trlt 2 (by norm_num) c hc _ (hbl 2 (by norm_num))
  have hb2 := trlt 1 (by norm_num) b hb _ hc2
  have g1 : (compA n L[0]!.trInv[a]! g)[base[1]!]! = L[1]!.pts[b]! := by
    rw [compA_get (hbl 1 (by norm_num)), hg _ (hbl 1 (by norm_num)), tr3,
      inv 0 (by norm_num) a ha _ (trlt 1 (by norm_num) b hb _ hc1),
      fix 2 (by norm_num) c hc 1 (by norm_num), root 1 (by norm_num) b hb]
  have g2 : (compA n L[1]!.trInv[b]! (compA n L[0]!.trInv[a]! g))[base[2]!]! = L[2]!.pts[c]! := by
    rw [compA_get (hbl 2 (by norm_num)), compA_get (hbl 2 (by norm_num)), hg _ (hbl 2 (by norm_num)),
      tr3, inv 0 (by norm_num) a ha _ hb2, inv 1 (by norm_num) b hb _ hc2, root 2 (by norm_num) c hc]
  unfold coords3
  simp only
  rw [g0, pos 0 (by norm_num) a ha, g1, pos 1 (by norm_num) b hb, g2, pos 2 (by norm_num) c hc]

end CFSG.KS.Raw.CS3

end
