module

public import CFSG.Certificates.Kernel.Co1Three.TermSound
public import CFSG.Certificates.Kernel.Misc.PermClosSound
import CFSG.Certificates.Kernel.SporSch.Co1RankGrpSound

public section

namespace CFSG.KC.Co1Cl

open CFSG.KC.Co1B CFSG.Sporadic.Co1Schreier CFSG.KC.Misc.Clos

theorem matK_fin_bij :
    Function.Bijective fun W : Fin (2 ^ (24 * 24)) => matK W.val := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun a b h => Fin.ext (CFSG.KS.SporSch.Co1Rank.matK_inj_rk a.isLt b.isLt h), ?_⟩
  have hM : Fintype.card (Matrix (Fin 24) (Fin 24) (ZMod 2)) =
      Fintype.card (Fin 24 → Fin 24 → ZMod 2) := Fintype.card_congr (Equiv.refl _)
  rw [Fintype.card_fin, hM, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ZMod.card,
    ← pow_mul]

@[expose] noncomputable def codeW (M : Matrix (Fin 24) (Fin 24) (ZMod 2)) : Nat :=
  (matK_fin_bij.2 M).choose.val

theorem codeW_lt (M : Matrix (Fin 24) (Fin 24) (ZMod 2)) : codeW M < 2 ^ (24 * 24) :=
  (matK_fin_bij.2 M).choose.isLt

theorem matK_codeW (M : Matrix (Fin 24) (Fin 24) (ZMod 2)) : matK (codeW M) = M :=
  (matK_fin_bij.2 M).choose_spec

theorem codeW_matK {W : Nat} (hW : W < 2 ^ (24 * 24)) : codeW (matK W) = W :=
  CFSG.KS.SporSch.Co1Rank.matK_inj_rk (codeW_lt _) hW (matK_codeW _)

theorem codeW_enc {G : Type*} [Group G] (φ : G →* Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hφ : Function.Injective φ) : ClosEnc (fun g => codeW (φ g)) mulWK oneK where
  enc_one := by
    rw [map_one, ← matK_oneK, codeW_matK CFSG.KS.SporSch.Co1Rank.oneK_lt_rk]
  enc_mul a b := by
    refine CFSG.KS.SporSch.Co1Rank.matK_inj_rk (codeW_lt _)
      (CFSG.KS.SporSch.Co1Rank.mulWK_lt_rk _ _) ?_
    rw [matK_codeW, matK_mulWK, matK_codeW, matK_codeW, map_mul]
  inj a b h := by
    have h' : codeW (φ a) = codeW (φ b) := h
    apply hφ
    rw [← matK_codeW (φ a), h', matK_codeW]

@[expose] noncomputable def matHom (H : Subgroup GL24) : ↥H →* Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  (Units.coeHom (Matrix (Fin 24) (Fin 24) (ZMod 2))).comp H.subtype

theorem matHom_injective (H : Subgroup GL24) : Function.Injective (matHom H) :=
  fun _ _ h => Subtype.ext (Units.ext h)

end CFSG.KC.Co1Cl

end
