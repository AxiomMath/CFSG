module

public import CFSG.Certificates.Kernel.He7222.ClsSound
public import CFSG.Certificates.Kernel.He7222.KChSound
public import CFSG.Certificates.Kernel.He7222.KeyGrp
public import CFSG.Certificates.Kernel.He7222.ChainPRep
import CFSG.Certificates.Kernel.OrbRow.LevelSound

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KS.PF CFSG.KC.OrbRow CFSG.Sporadic.Schreier

variable {n w : ℕ}

theorem class_conj (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (h5 : 5 ≤ n)
    {H P : Subgroup (Equiv.Perm (Fin n))} (hH : BaseFaithful H [0, 1, 2, 3, 4]) (hPH : P ≤ H)
    {Ts TIs : List (List ℕ)} (hTI : TIs.length = Ts.length)
    (hrep : ∀ t < Ts.length, ∀ j < (Ts.getD t []).length,
      recP n w ((Ts.getD t []).getD j 0) ∈ P ∧
      PRep n w ((Ts.getD t []).getD j 0) (recP n w ((Ts.getD t []).getD j 0)))
    (hshr : ∀ t < Ts.length, ∀ j < (Ts.getD t []).length, (Ts.getD t []).getD j 0 >>> (n * w) = 0)
    (hinv : ∀ t < Ts.length,
      invLK n w (mask w) (pidn n w) (Ts.getD t []) (TIs.getD t []) = true)
    {rs : List ℕ} {rr : Equiv.Perm (Fin n)} (hrs : ∀ p : Fin n, evK w (mask w) rs p = rr p)
    (hrr : rr ∈ P) {KC : List (List ℕ)} {keys : List ℕ}
    (hcls : clsK w (mask w) Ts TIs rs KC keys = true)
    {x : Equiv.Perm (Fin n)} (hx : x ∈ P) {F : ℕ → ℕ} (hF : ∀ p : Fin n, (p : ℕ) < 5 → F p = x p)
    {pos : ℕ} (hk : keyF w F 5 = getS keys pos) :
    ∃ c ∈ P, x = c * rr * c⁻¹ := by
  have hnw : n ≤ 2 ^ w := by omega
  obtain ⟨hlen, hall⟩ := clsK_sound hcls
  rcases Nat.lt_or_ge pos keys.length with hpos | hpos
  swap
  · exfalso
    rw [getS_eq, List.getD_eq_default _ _ hpos] at hk
    exact keyF_ne_zero hnw h5 hF hk
  have hposK : pos < KC.length := by omega
  obtain ⟨htup, hkey⟩ := hall pos hposK
  set ix := KC.getD pos [] with hix
  obtain ⟨hixl, hixb⟩ := tupOK_spec htup
  set rec : ℕ → ℕ → Equiv.Perm (Fin n) := fun t j => recP n w ((Ts.getD t []).getD j 0)
  have hst := stkK_rep (n := n) (w := w) rec htup (fun t ht j hj => (hrep t ht j hj).2)
  set cl := tupL rec Ts.length ix with hcl
  have hinvr : ∀ t < TIs.length, PRep n w ((TIs.getD t []).getD (ix.getD t 0) 0)
      ((fun t j => (rec t j)⁻¹) t (ix.getD t 0)) := by
    intro t ht
    have ht' : t < Ts.length := by omega
    obtain ⟨hl2, hi2⟩ := invLK_sound (hinv t ht')
    have hj := hixb t ht'
    exact invK_rep hn hw (hi2 _ hj) (hrep t ht' _ hj).2 (hshr t ht' _ hj)
  have hsti := stkIK_rep (n := n) (w := w) (fun t j => (rec t j)⁻¹) (acc := [])
    (accg := []) (by omega) hinvr List.Forall₂.nil
  rw [List.append_nil, hTI] at hsti
  have hci : (tupL (fun t j => (rec t j)⁻¹) Ts.length ix).reverse.prod = cl.prod⁻¹ := by
    rw [hcl, List.prod_inv_reverse]
    simp only [tupL, List.map_map]
    rfl
  have hcP : cl.prod ∈ P := by
    refine Subgroup.list_prod_mem (K := P) fun g hg => ?_
    simp only [hcl, tupL, List.mem_map, List.mem_range] at hg
    obtain ⟨t, ht, rfl⟩ := hg
    exact (hrep t ht _ (hixb t ht)).1
  refine ⟨cl.prod, hcP, ?_⟩
  refine eq_of_keyF (f' := cjEv w (mask w) (stkK Ts ix) rs (stkIK TIs ix [])) hH hnw (hPH hx)
    (hPH (P.mul_mem (P.mul_mem hcP hrr) (P.inv_mem hcP))) hF (fun p _ => ?_) h5 (hk.trans ?_)
  · change evK w (mask w) _ (evK w (mask w) rs (evK w (mask w) _ p)) = _
    rw [evK_rep hsti p, hci, hrs, evK_rep hst, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  · rw [getS_eq, ← hkey]

end CFSG.KC.HeChain

end
