module

public import CFSG.Certificates.Kernel.LocalQTCoreCSnd.Elt
public import CFSG.Certificates.Kernel.LocalQTLatCSound

public section

namespace CFSG.KC.LQT.Syl.CoreSnd

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

variable {n : ℕ}

private theorem kpw_card_of_list {X : Type*} [Group X] (H : Subgroup X) {L : List X}
    (hL : L.Nodup) (h : ∀ x, x ∈ H ↔ x ∈ L) : Nat.card H = L.length := by
  classical
  have h1 : Nat.card H = Nat.card {x // x ∈ L.toFinset} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (h x).trans List.mem_toFinset.symm)
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hL]

theorem es_mem {B : List (Perm (Fin n))} (h : EFacts B) (r : RN n) :
    r ∈ bfsSet (B.map RN.enc) 16 ↔ ∃ σ ∈ lst B, RN.enc σ = r := by
  constructor
  · intro hr
    obtain ⟨x, hx, rfl⟩ := bfsSet_sound (rawIsEnc n) B 16 r hr
    exact ⟨x, (mem_closure_iff_lst h x).1 hx, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨l, hl, hlen, hprod⟩ := exists_word_lst h hσ
    have hmem := CFSG.KC.LQT.CM.mem_bfsSet_prod RN.enc_mul RN.enc_one B 16 l hl (by omega)
    rw [hprod] at hmem
    exact hmem

theorem es_closed {B : List (Perm (Fin n))} (h : EFacts B) :
    closedH (B.map RN.enc) (bfsSet (B.map RN.enc) 16) = true :=
  CFSG.KC.LQT.CM.closedH_of_grp B 16 (· ∈ lst B) (es_mem h) (one_mem_lst B)
    (fun σ hσ g hg => lst_mul h hσ (mem_lst_of_mem h hg))

theorem es_size {B : List (Perm (Fin n))} (h : EFacts B) :
    (bfsSet (B.map RN.enc) 16).size = 16 := by
  have hc := card_closure_of_closedH (rawIsEnc n) B 16 (es_closed h)
  have hk := kpw_card_of_list (Subgroup.closure {b | b ∈ B}) h.nodup (mem_closure_iff_lst h)
  exact hc.symm.trans (hk.trans (lst_length B))

end CFSG.KC.LQT.Syl.CoreSnd

end
