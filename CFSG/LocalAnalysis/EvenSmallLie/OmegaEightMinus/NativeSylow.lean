
module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeSylowBase

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeBridge

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEightMinus

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.OmegaEight (matApp matMulM idCode matApp_lt matApp_matMulM matApp_idCode
  eq_of_cols matApp_pow matApp_xor)

theorem nsList_length : nsList.length = 136 := by
  have h := ns_ok.1
  rwa [nsArr, List.size_toArray] at h

theorem qNat_of_nsIdx_lt {v : ℕ} (hv : v < 256)
    (h : nsIdx[v]! < 136) : qNat v = true := by
  rw [nsIdx, getElem!_ofFn_nat _ hv, ← nsList_length] at h
  have hm := List.idxOf_lt_length_iff.1 h
  exact (List.mem_filter.1 hm).2

theorem nsArr_nsIdx {v : ℕ} (hv : v < 256)
    (h : nsIdx[v]! < 136) : nsArr[nsIdx[v]!]! = v :=
  (ns_ok.2.2.2 v hv (qNat_of_nsIdx_lt hv h)).2

theorem acts_mul {g h : Equiv.Perm (Fin 136)} {A B : ℕ}
    (hg : Acts g A) (hh : Acts h B) : Acts (g * h) (matMulM A B) := fun p hp => by
  have h2 := hh p hp
  have hk : nsIdx[matApp B nsArr[p]!]! < 136 := h2 ▸ (h ⟨p, hp⟩).2
  have e : h ⟨p, hp⟩ = ⟨_, hk⟩ := Fin.ext h2
  have g2 := hg _ hk
  rw [nsArr_nsIdx (matApp_lt B nsArr[p]!) hk] at g2
  rw [Equiv.Perm.mul_apply, e, matApp_matMulM]
  exact g2

theorem acts_one : Acts 1 idCode := fun p hp => by
  obtain ⟨h1, -, h3⟩ := ns_ok.2.2.1 p hp
  rw [matApp_idCode _ h1, h3]
  rfl

theorem acts_unique (hs : SAFacts) {g : Equiv.Perm (Fin 136)}
    {M M' : ℕ} (hM : M < 2 ^ 64) (hM' : M' < 2 ^ 64) (h : Acts g M) (h' : Acts g M') :
    M = M' := by
  have key : ∀ p < 136, matApp M nsArr[p]! = matApp M' nsArr[p]! := fun p hp => by
    have e : nsIdx[matApp M nsArr[p]!]! = nsIdx[matApp M' nsArr[p]!]! := (h p hp).symm.trans (h' p hp)
    have l1 : nsIdx[matApp M nsArr[p]!]! < 136 := h p hp ▸ (g ⟨p, hp⟩).2
    have l2 : nsIdx[matApp M' nsArr[p]!]! < 136 := e ▸ l1
    rw [← nsArr_nsIdx (matApp_lt _ _) l1, e, nsArr_nsIdx (matApp_lt _ _) l2]
  have atNs : ∀ x < 256, qNat x = true → matApp M x = matApp M' x := fun x hx hq => by
    obtain ⟨l, e⟩ := ns_ok.2.2.2 x hx hq
    have := key _ l
    rwa [e] at this
  refine eq_of_span hM hM' (fun c hc => (hs.span c hc).2.2.2.2) fun c hc => ?_
  obtain ⟨a1, b1, a2, b2, -⟩ := hs.span c hc
  exact ⟨atNs _ a1 a2, atNs _ b1 b2⟩

theorem acts_gen (hs : SAFacts) {l : ℕ} (hl : l < 6) :
    Acts (gen (sylowIdx.getD l 0)) (saMat (saGen l)) := by
  have h := (hs.gens l hl).2
  rw [sylowGens_getElem! hl] at h
  exact acts_of_rep (rep_gen (sylowIdx_lt hl)) h

theorem saElt_spec (hs : SAFacts) :
    ∀ i < 8192, saElt i ∈ sylowT ∧ Acts (saElt i) (saMat i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [saElt]
      split
      · next h => exact absurd h.1 (Nat.lt_irrefl 0)
      · rw [hs.id0]
        exact ⟨sylowT.one_mem, acts_one⟩
    · obtain ⟨hp, hl, he⟩ := hs.tree i hi hpos
      rw [saElt]
      split
      swap
      · next h => exact absurd ⟨hpos, hp⟩ h
      obtain ⟨m1, a1⟩ := ih _ hp (hp.trans hi)
      refine ⟨sylowT.mul_mem (gen_mem_sylowT hl) m1, ?_⟩
      have h := acts_mul (acts_gen hs hl) a1
      rwa [hs.closed _ (hp.trans hi) _ hl, he] at h

theorem saElt_inj (hs : SAFacts) {i k : ℕ} (hi : i < 8192)
    (hk : k < 8192) (h : saElt i = saElt k) : i = k := by
  have a := (saElt_spec hs i hi).2
  rw [h] at a
  exact hs.distinct i hi k hk (acts_unique hs (saMat_lt i) (saMat_lt k) a (saElt_spec hs k hk).2)

theorem exists_saElt (hs : SAFacts) {u : Equiv.Perm (Fin 136)}
    (hu : u ∈ sylowT) : ∃ i < 8192, saElt i = u := by
  let f : Fin 8192 → sylowT := fun i => ⟨saElt i, (saElt_spec hs i i.2).1⟩
  have hf : Function.Injective f := fun i k h =>
    Fin.ext (saElt_inj hs i.2 k.2 (congrArg Subtype.val h))
  have hb : Function.Bijective f := by
    refine hf.bijective_of_nat_card_le ?_
    rw [card_sylowT, Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨i, hi⟩ := hb.2 ⟨u, hu⟩
  exact ⟨i, i.2, congrArg Subtype.val hi⟩

theorem exists_acts (hs : SAFacts) {u : Equiv.Perm (Fin 136)}
    (hu : u ∈ sylowT) : ∃ i < 8192, saElt i = u ∧ Acts u (saMat i) := by
  obtain ⟨i, hi, rfl⟩ := exists_saElt hs hu
  exact ⟨i, hi, rfl, (saElt_spec hs i hi).2⟩

theorem eq_of_acts (hs : SAFacts) {u v : Equiv.Perm (Fin 136)}
    (hu : u ∈ sylowT) (hv : v ∈ sylowT) {M : ℕ} (hM : M < 2 ^ 64) (au : Acts u M)
    (av : Acts v M) : u = v := by
  obtain ⟨i, hi, rfl, ai⟩ := exists_acts hs hu
  obtain ⟨k, hk, rfl, ak⟩ := exists_acts hs hv
  have e1 := acts_unique hs hM (saMat_lt i) au ai
  have e2 := acts_unique hs hM (saMat_lt k) av ak
  rw [hs.distinct i hi k hk (e1.symm.trans e2)]

end CFSG.EvenSmallLie.OmegaEightMinus

end
