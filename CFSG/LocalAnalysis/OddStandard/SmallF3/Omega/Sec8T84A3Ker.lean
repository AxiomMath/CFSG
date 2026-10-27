module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Dich
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3KerZ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4SlcProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace A3

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G}
  {B K L1 : Subgroup G}

@[expose] noncomputable def fHom (L B : Subgroup G) :
    ↥(L.subgroupOf (normalizer (B : Set G))) →* MulAut ↥B :=
  B.normalizerMonoidHom.comp (L.subgroupOf (normalizer (B : Set G))).subtype

theorem fHom_range (L B : Subgroup G) : (fHom L B).range = autIn L B := by
  unfold fHom autIn
  rw [MonoidHom.range_comp, Subgroup.range_subtype]

theorem fHom_apply_coe (L B : Subgroup G) (m : ↥(L.subgroupOf (normalizer (B : Set G))))
    (x : ↥B) : ((fHom L B m x : ↥B) : G) =
      ((m : ↥(normalizer (B : Set G))) : G) * x * ((m : ↥(normalizer (B : Set G))) : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe B (m : ↥(normalizer (B : Set G))) x

@[expose] noncomputable def toN (hctx : Sec8Ctx G t L S z g B) :
    ↥(L.subgroupOf (normalizer (B : Set G))) →* ↥(Nsub8 t B) :=
  ((normalizer (B : Set G)).subtype.comp
      (L.subgroupOf (normalizer (B : Set G))).subtype).codRestrict (Nsub8 t B)
    fun m => (sec8t84a1_L_norm_le hctx ⟨Subgroup.mem_subgroupOf.mp m.2, m.1.2⟩).1

@[expose] noncomputable def gHom (hctx : Sec8Ctx G t L S z g B)
    (h : Sec8T84L1 G t L S z g B K L1) :
    ↥(L.subgroupOf (normalizer (B : Set G))) →* MulAut ↥L1 :=
  (RedAct.redHom (setup hctx h)).comp (toN hctx)

theorem gHom_coe_B (hctx : Sec8Ctx G t L S z g B) (h : Sec8T84L1 G t L S z g B K L1)
    (m : ↥(L.subgroupOf (normalizer (B : Set G)))) {b : ↥L1} (hb : (b : G) ∈ B) :
    ((gHom hctx h m b : ↥L1) : G) =
      ((m : ↥(normalizer (B : Set G))) : G) * b * ((m : ↥(normalizer (B : Set G))) : G)⁻¹ :=
  rho_on_B hctx h (toN hctx m) m.1.2 b hb

theorem ker_g_le (hctx : Sec8Ctx G t L S z g B) (h : Sec8T84L1 G t L S z g B K L1)
    (m : ↥(L.subgroupOf (normalizer (B : Set G)))) (hm : gHom hctx h m = 1) :
    fHom L B m = 1 := by
  ext x
  have h1 : (x : G) =
      ((m : ↥(normalizer (B : Set G))) : G) * x * ((m : ↥(normalizer (B : Set G))) : G)⁻¹ := by
    have h2 := gHom_coe_B hctx h m (b := ⟨(x : G), h.B_le x.2⟩) x.2
    rwa [hm, MulAut.one_apply] at h2
  rw [fHom_apply_coe]
  simpa using h1.symm

theorem exists_mul_of_comm {H K : Subgroup G} (hHK : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) {x : G}
    (hx : x ∈ H ⊔ K) : ∃ a ∈ H, ∃ b ∈ K, x = a * b :=
  sec4_mem_sup_of_commute hHK hx

theorem ker_f_le (F : Sec8T84Base) (hctx : Sec8Ctx G t L S z g B)
    (h : Sec8T84L1 G t L S z g B K L1) (m : ↥(L.subgroupOf (normalizer (B : Set G))))
    (hm : fHom L B m = 1) : gHom hctx h m = 1 := by
  let mg : G := ((m : ↥(normalizer (B : Set G))) : G)
  have hmL : mg ∈ L := Subgroup.mem_subgroupOf.mp m.2
  have hcent : mg ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 : mg * b * mg⁻¹ = b := by
      have h2 := fHom_apply_coe L B m ⟨b, hb⟩
      rw [hm] at h2
      simpa [mg] using h2.symm
    calc b * mg = (mg * b * mg⁻¹) * mg := by rw [h1]
      _ = mg * b := by group
  have hmem : mg ∈ B ⊔ centerIn L := by
    rw [← (aut_B_of F hctx).2.2]
    exact ⟨hmL, hcent⟩
  have hcomm : ∀ x ∈ B, ∀ y ∈ centerIn L, x * y = y * x := by
    intro x hx y hy
    exact (((sec4_mem_centerIn_iff y).mp hy).2 x (hctx.B_le hx).1).symm
  obtain ⟨b, hb, c, hc, hbc⟩ := exists_mul_of_comm hcomm hmem
  have hcO : c ∈ oddCoreIn (Nsub8 t B) :=
    centerIn_le_oddCoreIn_N F.h8A hctx (isOm6M_ctx hctx) hc
  let nb : ↥(Nsub8 t B) := ⟨b, sec8t84a1_A_le_N (sec8t84a1_B_le_A hb)⟩
  let nc : ↥(Nsub8 t B) := ⟨c, (oddCoreIn_normal (Nsub8 t B)).1 hcO⟩
  have htoN : toN hctx m = nb * nc := by
    apply Subtype.ext
    show ((m : ↥(normalizer (B : Set G))) : G) = b * c
    simpa [mg] using hbc
  have hnb : RedAct.redHom (setup hctx h) nb = 1 := by
    ext v
    have ho : (nb : G) * (v : G) * (nb : G)⁻¹ = (v : G) * 1 := by
      have hcommK : (v : G) * b = b * (v : G) :=
        (cl2_of h.K_data).central (v : G) (h.le v.2) b hb
      have hbv : b * (v : G) * b⁻¹ = (v : G) := by
        rw [← hcommK]
        group
      simpa [nb] using hbv
    simpa using RedAct.redHom_eq_of (setup hctx h) nb v v
      (oddCoreIn (Nsub8 t B)).one_mem ho
  have hnc : RedAct.redHom (setup hctx h) nc = 1 :=
    RedAct.redHom_of_mem_O (setup hctx h) nc (by simpa [nc] using hcO)
  change RedAct.redHom (setup hctx h) (toN hctx m) = 1
  rw [htoN, map_mul, hnb, hnc, mul_one]

end A3

end CFSG.OddStandard.SmallF3.Omega
