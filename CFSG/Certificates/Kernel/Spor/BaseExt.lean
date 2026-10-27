module

public import CFSG.Certificates.NativeSchreierArrays
public import CFSG.Certificates.Kernel.Spor.RawTreeDefs

public section

namespace CFSG.KS.Raw

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem mem_take_iff_get {n : Nat} {L : List (Fin n)} {i : Nat} {b : Fin n} :
    b ∈ L.take i ↔ ∃ t < i, ∃ h : t < L.length, L[t] = b := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [List.length_take] at ht
    exact ⟨t, by omega, by omega, by rw [List.getElem_take]⟩
  · rintro ⟨t, hti, htl, rfl⟩
    exact ⟨t, by rw [List.length_take]; omega, by rw [List.getElem_take]⟩

theorem sep_of_ext {n : Nat} (hn : 1 ≤ n) {S : Array (Array Nat)} {k : Nat} (hk : k ≤ S.size)
    {W : Array (List Int)} {c : Nat} (hc : 0 < c) {base ext : List (Fin n)} (hext : ext.Nodup)
    {baseArr extArr : Array Nat} (hB : (base.map Fin.val).toArray = baseArr)
    (hE : (ext.map Fin.val).toArray = extArr) (hpre : ext.take base.length = base)
    (hok : rawChainOK n (S.extract 0 k) S extArr W c = true)
    (htriv : ∀ i, base.length ≤ i → i < ext.length → ((rawLevels n S extArr)[i]!).pts.size = 1)
    (hsep : Sep n S extArr) : Sep n S baseArr := by
  set Q := RawSchreierDatum.ofArrays n hn S k hk ext hext W
  have hA := chainArrays_ofArrays (n := n) (hn := hn) (k := k) (hk := hk) (base := ext) (hb := hext)
    (W := W) (chainCheckFacts (hE ▸ hok)).strong_inv
  rw [hE] at hA
  have hv := validSchreier_of_chainOK hA hc hok
  have hbase : Q.base.toList = ext := RawSchreierDatum.ofArrays_base_toList
  intro G hG hfix
  have hGQ : G ∈ Q.originalSubgroup := by
    refine (Subgroup.closure_le _).2 ?_ hG
    rintro _ ⟨j, hj, rfl⟩
    have h := RawSchreierDatum.strong_get_mem_originalSubgroup Q hv.1 ⟨j, hj⟩
    rwa [RawSchreierDatum.ofArrays_strong_get] at h
  have hfixB : ∀ t (ht : t < base.length), G base[t] = base[t] := by
    intro t ht
    have hv' : (base[t] : Nat) = baseArr[t]! := by
      rw [← hB, getElem!_pos _ t (by simpa using ht)]
      simp
    have hts : t < baseArr.size := by
      rw [← hB]
      simpa using ht
    have hlt : baseArr[t]! < n := hv' ▸ base[t].2
    have h := hfix t hts hlt
    have e : (⟨baseArr[t]!, hlt⟩ : Fin n) = base[t] := Fin.ext hv'.symm
    rw [e] at h
    exact h
  have key : ∀ i ≤ ext.length, ∀ b ∈ ext.take i, G b = b := by
    intro i
    induction i with
    | zero => intro _ b hb; simp at hb
    | succ i ih =>
      intro hi b hb
      rw [mem_take_iff_get] at hb
      obtain ⟨t, hti, htl, rfl⟩ := hb
      rcases Nat.lt_or_ge t i with h | h
      · exact ih (by omega) _ (mem_take_iff_get.2 ⟨t, h, htl, rfl⟩)
      have hti' : t = i := by omega
      subst hti'
      rcases Nat.lt_or_ge t base.length with hb | hb
      · have e : ext[t] = base[t] := by
          have := congrArg (fun L => L[t]?) hpre
          simp only [List.getElem?_take, hb, ↓reduceIte] at this
          rw [List.getElem?_eq_getElem htl, List.getElem?_eq_getElem hb] at this
          exact Option.some.inj this
        rw [e]
        exact hfixB t hb
      · have hmem : G ∈ Q.levelSubgroup t :=
          (Q.mem_levelSubgroup_iff hv.1 t (by
            change t ≤ ext.length
            omega) G).2 ⟨hGQ, fun b hb' => ih (by omega) b (by rwa [hbase] at hb')⟩
        let it : Fin Q.baseCount := ⟨t, htl⟩
        have hcard : Nat.card (Q.orbitPoints it) = 1 := by
          rw [← RawSchreierDatum.orbitSize_eq_card, hv.2 it]
          exact htriv t hb htl
        have hsub : Subsingleton (Q.orbitPoints it) := (Nat.card_eq_one_iff_unique.1 hcard).1
        rw [RawSchreierDatum.orbitPoints_eq_orbit] at hsub
        have h1 : (⟨G, hmem⟩ : Q.levelSubgroup t) • Q.base.get it ∈
            MulAction.orbit (Q.levelSubgroup it.val) (Q.base.get it) := MulAction.mem_orbit _ _
        have h2 : Q.base.get it ∈ MulAction.orbit (Q.levelSubgroup it.val) (Q.base.get it) :=
          MulAction.mem_orbit_self _
        have e := congrArg Subtype.val (Subsingleton.elim (α := MulAction.orbit
          (Q.levelSubgroup it.val) (Q.base.get it)) ⟨_, h1⟩ ⟨_, h2⟩)
        have hg : Q.base.get it = ext[t] := by
          change (⟨ext.toArray, _⟩ : Vector (Fin n) ext.length).get ⟨t, htl⟩ = ext[t]
          simp [Vector.get]
        rw [← hg]
        exact e
  refine hsep G hG fun t ht h => ?_
  have hlen : t < ext.length := by rw [← hE] at ht; simpa using ht
  have hv' : (ext[t] : Nat) = extArr[t]! := by
    rw [← hE, getElem!_pos _ t (by simpa using hlen)]
    simp
  have e : (⟨extArr[t]!, h⟩ : Fin n) = ext[t] := Fin.ext hv'.symm
  rw [e]
  exact key ext.length le_rfl _ (by rw [List.take_length]; exact List.getElem_mem hlen)

end CFSG.KS.Raw

end
