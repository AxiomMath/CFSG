module

public import Certificates.Data.Kernel.LyDce.CoverWalkCut
public import CFSG.Certificates.Kernel.LyDce.CoverWalkSound

public section

namespace CFSG.KC.LyDce

open CFSG.KC CFSG.KC.Loop

def TriInv (Nc Nd : Nat) (st : List (Nat × Nat × Nat)) : Prop := ∀ t ∈ st, t = tri Nc Nd t.1

theorem triInv_map (Nc Nd : Nat) (Xs : List Nat) : TriInv Nc Nd (Xs.map (tri Nc Nd)) := by
  intro t ht
  obtain ⟨X, -, rfl⟩ := List.mem_map.1 ht
  rfl

theorem eqNL_eq : ∀ (L M : List Nat), eqNL L M = true → L = M
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [eqNL] at h
  | _ :: _, [], h => by simp [eqNL] at h
  | a :: L, b :: M, h => by
    have h' : andB (Nat.beq a b) (eqNL L M) = true := h
    obtain ⟨h1, h2⟩ := cwS_andB h'
    rw [Nat.eq_of_beq_eq_true h1, eqNL_eq _ _ h2]

theorem eq_map_tri {Nc Nd : Nat} : ∀ {st : List (Nat × Nat × Nat)}, TriInv Nc Nd st →
    st = (st.map Prod.fst).map (tri Nc Nd)
  | [], _ => rfl
  | t :: st, h => by
    have ht := h t List.mem_cons_self
    have hs : TriInv Nc Nd st := fun u hu => h u (List.mem_cons_of_mem _ hu)
    simp only [List.map_cons]
    rw [← eq_map_tri hs, ← ht]

theorem walkS_append {Nc Nd P K Tc Td : Nat} :
    ∀ (es1 es2 : List (Nat × Nat × Nat)) (st : List (Nat × Nat × Nat)) (Xs : List Nat),
      TriInv Nc Nd st → walkSTo Nc Nd P K Tc Td es1 st Xs = true →
      walkS Nc Nd P K Tc Td es2 (Xs.map (tri Nc Nd)) = true →
      walkS Nc Nd P K Tc Td (es1 ++ es2) st = true
  | [], es2, st, Xs, hI, h1, h2 => by
    have e : st.map Prod.fst = Xs := eqNL_eq _ _ h1
    rw [List.nil_append, eq_map_tri hI, e]
    exact h2
  | e :: es1, es2, st, Xs, hI, h1, h2 => by
    unfold walkSTo at h1
    dsimp only at h1
    rw [List.cons_append]
    unfold walkS
    dsimp only
    cases hdr : st.drop e.2.1 with
    | nil =>
      rw [hdr] at h1
      exact absurd h1 Bool.false_ne_true
    | cons top rest =>
      rw [hdr] at h1
      dsimp only at h1 ⊢
      rw [cwS_strictBN] at h1
      beta_reduce at h1
      rw [cwS_strictBN] at h1
      beta_reduce at h1
      rw [cwS_strictBN] at h1
      beta_reduce at h1
      rw [cwS_strictBN]
      beta_reduce
      rw [cwS_strictBN]
      beta_reduce
      rw [cwS_strictBN]
      beta_reduce
      obtain ⟨hl, hr⟩ := cwS_andB h1
      have hmem : ∀ t ∈ top :: rest, t ∈ st := fun t ht => List.mem_of_mem_drop (hdr ▸ ht)
      have hpop : ∀ t ∈ popG e.2.2 (top :: rest), t ∈ top :: rest := by
        unfold popG
        cases Nat.beq e.2.2 2
        · exact fun t ht => ht
        · exact fun t ht => List.mem_of_mem_tail ht
      have hI' : TriInv Nc Nd ((selG e.2.2 top, net2 Nc (selG e.2.2 top), net2 Nd (selG e.2.2 top)) ::
          popG e.2.2 (top :: rest)) := by
        intro t ht
        rcases List.mem_cons.1 ht with rfl | ht
        · rfl
        · exact hI t (hmem t (hpop t ht))
      have hw := walkS_append (Nc := Nc) (Nd := Nd) (P := P) (K := K) (Tc := Tc) (Td := Td)
        es1 es2 _ Xs hI' hr h2
      have htrue : ∀ b : Bool, andB true b = b := fun b => by cases b <;> rfl
      rw [hl, htrue]
      exact hw

theorem walkS_cut {Nc Nd P K Tc Td : Nat} {es : List (Nat × Nat × Nat)}
    {st : List (Nat × Nat × Nat)} {Xs : List Nat} {a b : Nat} (hI : TriInv Nc Nd st) (hab : a ≤ b)
    (h1 : walkSTo Nc Nd P K Tc Td ((es.drop a).take (b - a)) st Xs = true)
    (h2 : walkS Nc Nd P K Tc Td (es.drop b) (Xs.map (tri Nc Nd)) = true) :
    walkS Nc Nd P K Tc Td (es.drop a) st = true := by
  have e2 : (es.drop a).drop (b - a) = es.drop b := by
    rw [List.drop_drop]
    congr 1
    omega
  have e : es.drop a = (es.drop a).take (b - a) ++ es.drop b := by
    rw [← e2]
    exact (List.take_append_drop _ _).symm
  rw [e]
  exact walkS_append _ _ st Xs hI h1 h2

theorem walkSFrom_cut {Nc Nd P K Tc Td M₀ : Nat} {es : List (Nat × Nat × Nat)} {Xs : List Nat}
    {b : Nat} (h1 : walkSFromTo Nc Nd P K Tc Td M₀ ((es.drop 0).take (b - 0)) Xs = true)
    (h2 : walkS Nc Nd P K Tc Td (es.drop b) (Xs.map (tri Nc Nd)) = true) :
    walkSFrom Nc Nd P K Tc Td M₀ es = true := by
  unfold walkSFromTo at h1
  unfold walkSFrom
  rw [cwS_strictBN] at h1
  rw [cwS_strictBN]
  have hI : TriInv Nc Nd [(saltOf M₀, net2 Nc (saltOf M₀), net2 Nd (saltOf M₀))] := by
    intro t ht
    rcases List.mem_singleton.1 ht with rfl
    rfl
  have := walkS_cut (es := es) (a := 0) hI (Nat.zero_le b) h1 h2
  rwa [List.drop_zero] at this

end CFSG.KC.LyDce

end
