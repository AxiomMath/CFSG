module

public import CFSG.Certificates.Kernel.J2EnumSound
public import CFSG.Certificates.Kernel.J2Enum.Group
public import CFSG.Sporadic.Th.TableSpec
import all CFSG.Certificates.Kernel.J2Enum.Count
import all CFSG.Certificates.Kernel.J2Enum.Classes
import CFSG.Certificates.Kernel.J2CoverSnd.Chain

public section

namespace CFSG.KC.J2Enum.CntPf

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover CFSG.KC.J2Enum
open CFSG.Sporadic.Th (Rep Rep.compT Rep.idT)

theorem rep_tabP_of_prep {n w X : ℕ} {γ : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32)
    (h : Raw.Orb.PRep n w X γ) : Rep n (arrTable n (unpack n w X)) γ :=
  rep_of_prep hn h

theorem chain_products {n w kS kO BP NS CH : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}
    {D : List (List ℤ)} {S : Array (Array ℕ)} {base : Array ℕ}
    (hc : ChainOK3 n w kS kO BP NS CH PS PSI LR TR TRI D S base) :
    ∃ L : List (Equiv.Perm (Fin n)), L.Nodup ∧ (∀ x, x ∈ L ↔ x ∈ Raw.Orb.Gen n S kO) ∧
      ∀ (f : Table → Bool) (q : Equiv.Perm (Fin n) → Bool),
        (∀ T x, Rep n T x → (f T = true ↔ q x = true)) →
        List.Forall₂ (Rep n) (filterProducts n f (chainTables n S base) (idT n) [])
          (L.filter q).reverse := by
  obtain ⟨hb, hh, hl, hNS, hs, hp⟩ := hc
  obtain ⟨hT, hsurj, hinj⟩ := GrpPf.enum3 hb hh hl hNS hs
  have hn32 : n < 2 ^ 32 := by have := hb.2.2.1; omega
  refine ⟨trip (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) fun a b c =>
      CFSG.Certificates.ChainArrays.levT n S base 0 a *
        CFSG.Certificates.ChainArrays.levT n S base 1 b *
        CFSG.Certificates.ChainArrays.levT n S base 2 c,
    trip_nodup hinj, fun x => ?_, fun f q hfq => ?_⟩
  · rw [mem_trip]
    constructor
    · rintro ⟨a, ha, b, hb', c, hc, rfl⟩
      exact mul_mem (mul_mem (hT 0 (by norm_num) a ha).1 (hT 1 (by norm_num) b hb').1)
        (hT 2 (by norm_num) c hc).1
    · exact hsurj x
  · obtain ⟨hct, -⟩ := CFSG.KC.J2Cover.Snd.chainTables_eq_lvTab hb hp hl
    have hA : List.Forall₂ (Rep n) (allProd n (chainTables n S base) (idT n))
        (trip (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) fun a b c =>
          CFSG.Certificates.ChainArrays.levT n S base 0 a *
            CFSG.Certificates.ChainArrays.levT n S base 1 b *
            CFSG.Certificates.ChainArrays.levT n S base 2 c) := by
      rw [hct, allProd3]
      refine forall₂_trip fun a ha b hb' c hc => ?_
      have := ((Rep.idT hn32).compT (rep_of_prep hn32 (hT 0 (by norm_num) a ha).2)).compT
        (rep_of_prep hn32 (hT 1 (by norm_num) b hb').2) |>.compT
        (rep_of_prep hn32 (hT 2 (by norm_num) c hc).2)
      rwa [one_mul] at this
    rw [filterProducts_eq, List.append_nil, List.forall₂_reverse_iff]
    exact List.rel_filter (fun T x hTx => hfq T x hTx) hA

end CFSG.KC.J2Enum.CntPf

end
