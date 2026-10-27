module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eOrbit

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e

open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.AE.Wr
open Finset

theorem zBar_eq_vq (α : Finset (Fin 8)) (h : α.card = 4) : zBar α h = vq α := by
  unfold zBar vq
  congr 1
  refine Wr.ext (funext fun z => ?_) (zOf_perm _)
  rw [zOf_vec_apply]
  show (if z ∈ Set.range (emb α h) then (1 : ZMod 2) else 0) = ind α z
  have : z ∈ Set.range (emb α h) ↔ z ∈ α := by rw [range_emb]; simp
  unfold ind
  by_cases hz : z ∈ α
  · rw [if_pos (this.2 hz), if_pos hz]
  · rw [if_neg (mt this.1 hz), if_neg hz]

@[expose] def V4l : Finset (Equiv.Perm (Fin 4)) := {1, d₁, d₂, d₃}

theorem V4l_mul : ∀ a ∈ V4l, ∀ b ∈ V4l, a * b ∈ V4l := by decide +kernel

theorem V4l_fpf : ∀ d ∈ V4l, d ≠ 1 → d * d = 1 ∧ ∀ i, d i ≠ i := by decide +kernel

theorem kList_perm : ∀ k ∈ kList, k.perm ∈ V4l := by decide +kernel

theorem kStarList_perm : ∀ k ∈ kStarList, k.perm ∈ V4l := by decide +kernel

@[expose] def V4set (α : Finset (Fin 8)) (h : α.card = 4) : Set (Equiv.Perm (Fin 8)) :=
  {σ | ∃ d ∈ V4l, σ = embedPerm (emb α h) d}

theorem permQ_mem_V4set {α : Finset (Fin 8)} {h : α.card = 4} {b : Bool} {x : AEQ 8}
    (hx : x ∈ memBar α h b) : permQ 8 x ∈ V4set α h := by
  obtain ⟨w, hw, rfl⟩ := hx
  rw [permQ_mkQ]
  cases b
  · have hw' : w ∈ memKStar (emb α h) := hw
    obtain ⟨k, hk, rfl⟩ := hw'
    exact ⟨k.perm, kStarList_perm k hk, rfl⟩
  · have hw' : w ∈ memK (emb α h) := hw
    obtain ⟨k, hk, rfl⟩ := hw'
    exact ⟨k.perm, kList_perm k hk, rfl⟩

theorem V4set_mul {α : Finset (Fin 8)} {h : α.card = 4} {σ τ : Equiv.Perm (Fin 8)}
    (hσ : σ ∈ V4set α h) (hτ : τ ∈ V4set α h) : σ * τ ∈ V4set α h := by
  obtain ⟨d, hd, rfl⟩ := hσ
  obtain ⟨e, he, rfl⟩ := hτ
  exact ⟨d * e, V4l_mul d hd e he, (embedPerm_mul _ d e).symm⟩

theorem V4set_fpf {α : Finset (Fin 8)} {h : α.card = 4} {σ : Equiv.Perm (Fin 8)}
    (hσ : σ ∈ V4set α h) (h1 : σ ≠ 1) : σ * σ = 1 ∧ ∀ z, (z ∈ α ↔ σ z ≠ z) := by
  obtain ⟨d, hd, rfl⟩ := hσ
  have hd1 : d ≠ 1 := fun e => h1 (by rw [e, embedPerm_one])
  obtain ⟨hdd, hdi⟩ := V4l_fpf d hd hd1
  refine ⟨by rw [← embedPerm_mul, hdd, embedPerm_one], fun z => ?_⟩
  constructor
  · intro hz
    have hz' : z ∈ Set.range (emb α h) := by rw [range_emb]; exact hz
    obtain ⟨i, rfl⟩ := hz'
    rw [embedPerm_apply]
    exact fun e => hdi i ((emb α h).injective e)
  · intro hne
    by_contra hz
    have hz' : z ∉ Set.range (emb α h) := by rw [range_emb]; exact hz
    exact hne (embedPerm_of_not_mem _ _ hz')

namespace E8Pkg

variable {Y : Type} [Group Y] {I D : Subgroup Y} (P : E8Pkg I D)

theorem exists_conj_two {d d' : Y} (hd : d ∈ I) (hd' : d' ∈ I) {S S' : Finset (Fin 8)}
    (hS : S.card = 2) (hS' : S'.card = 2) (h : P.ph d = vq S) (h' : P.ph d' = vq S') :
    ∃ i ∈ I, i * d * i⁻¹ = d' := by
  obtain ⟨g, hg, hgS⟩ := exists_even_perm_card (k := 2) (by norm_num) hS hS'
  obtain ⟨i, hi, hρ⟩ := P.exists_lift hg
  refine ⟨i, hi, P.ph_inj (I.mul_mem (I.mul_mem hi hd) (I.inv_mem hi)) hd' ?_⟩
  rw [P.conj_vec hi hd h, hρ, map_eq_of_iff hgS, h']

theorem w2 {J J' : Subgroup Y} {a : Finset (Fin 8)} {ha : a.card = 4} {b b' : Bool}
    (hJI : J ≤ I) (hJ'I : J' ≤ I) (hl : ∀ k ∈ I, k ∈ J ↔ P.ph k ∈ memBar a ha b)
    (hl' : ∀ k ∈ I, k ∈ J' ↔ P.ph k ∈ memBar a ha b') {k k' : Y} (hk : k ∈ J) (hk' : k' ∈ J')
    (hD : k * k' ∈ D) (hne1 : k * k' ≠ 1) (hnea : P.ph (k * k') ≠ vq a) :
    ∃ S : Finset (Fin 8), S ⊆ a ∧ S.card = 2 ∧ P.ph (k * k') = vq S := by
  have hkI := hJI hk
  have hk'I := hJ'I hk'
  obtain ⟨w, hw, hwe⟩ := (hl k hkI).1 hk
  obtain ⟨w', hw', hwe'⟩ := (hl' k' hk'I).1 hk'
  have hs := supportedOn_of_mem_memAt hw
  have hs' := supportedOn_of_mem_memAt hw'
  have hph : P.ph (k * k') = mkQ 8 (w * w') := by
    rw [P.ph_mul hkI hk'I, ← hwe, ← hwe', map_mul]
  have hperm : (w * w').perm = 1 := by
    have h1 := P.rho_eq_one_of_mem_D hD
    unfold E8Pkg.rho at h1
    rw [hph, permQ_mkQ] at h1
    exact h1
  have hww : w * w' = ofVec (w * w').vec := Wr.ext rfl hperm
  have hsupp : ∀ z, z ∉ a → (w * w').vec z = 0 := fun z hz =>
    ((hs.mul hs') z (by rw [range_emb]; exact hz)).1
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin 8), S = Finset.univ.filter (fun z => (w * w').vec z = 1) :=
    ⟨_, rfl⟩
  have hSa : S ⊆ a := by
    intro z hz
    by_contra hza
    rw [hS, Finset.mem_filter] at hz
    rw [hsupp z hza] at hz
    exact absurd hz.2 (by decide)
  have hvec : ∀ z, (w * w').vec z = ind S z := by
    intro z
    have h01 : (w * w').vec z = 0 ∨ (w * w').vec z = 1 := by
      generalize (w * w').vec z = c
      revert c
      decide
    unfold ind
    rcases h01 with h0 | h1
    · have : z ∉ S := by rw [hS, Finset.mem_filter]; simp [h0]
      simp [this, h0]
    · have : z ∈ S := by rw [hS, Finset.mem_filter]; simp [h1]
      simp [this, h1]
  have hphS : P.ph (k * k') = vq S := by
    rw [hph, hww]
    unfold vq
    congr 2
    funext z
    exact hvec z
  obtain ⟨S', hS'e, hS'⟩ := P.vec_of_mem_D hD
  have hSe : Even S.card := by
    rcases vq_eq_iff.mp (hphS.symm.trans hS') with h | h
    · rw [← h]
      exact hS'e
    · have hc : S'.card = 8 - S.card := by
        rw [h, Finset.card_compl]
        simp
      have hle : S.card ≤ 8 := by
        have := Finset.card_le_univ S
        simpa using this
      obtain ⟨m, hm⟩ := hS'e
      exact ⟨4 - m, by omega⟩
  have hle4 : S.card ≤ 4 := by
    have := Finset.card_le_card hSa
    omega
  have hcard : S.card = 0 ∨ S.card = 2 ∨ S.card = 4 := by
    obtain ⟨m, hm⟩ := hSe
    omega
  rcases hcard with h0 | h2 | h4
  · exfalso
    apply hne1
    have hS0 : S = ∅ := Finset.card_eq_zero.mp h0
    rw [hS0, vq_empty] at hphS
    exact P.ph_inj (I.mul_mem hkI hk'I) I.one_mem (by rw [hphS, P.ph_one])
  · exact ⟨S, hSa, h2, hphS⟩
  · exfalso
    apply hnea
    have hSeq : S = a := Finset.eq_of_subset_of_card_le hSa (by rw [h4, ha])
    rw [hphS, hSeq]

end E8Pkg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
