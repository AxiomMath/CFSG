module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C1Set
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C6Str

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B E : Subgroup G}

theorem Abar_le_range (F : Sec8T84Base) (hE : Sec8E G t L S z g B E) :
    B89.Abar hE ≤ E.normalizerMonoidHom.range := by
  intro a ha
  obtain ⟨m, hmL, hmB, rfl⟩ := B89.exists_of_mem_Abar hE ha
  have hLt : L ≤ centralizer ({t} : Set G) := hE.ctx.toSec3SettingLB.component.le
  have hind_m : B89.Induces B m (sec1011_conjAut B m hmB) := B89.induces_conjAut B hmB
  have hαL : sec1011_conjAut B m hmB ∈ autIn L B := B89.mem_autIn_of_induces hmL hind_m
  have hαC : sec1011_conjAut B m hmB ∈ autIn (centralizer ({t} : Set G)) B :=
    B89.autIn_mono hLt hαL
  obtain ⟨x, hx, hind_x⟩ := B89.exists_lift F.h8A hE hαC
  have hxX : x ∈ normalizer (E : Set G) := hx.1
  have hxN : x ∈ Nsub8 t B := B89.XCt_le_N hE hx
  have hind : ∀ b ∈ B, x * b * x⁻¹ = m * b * m⁻¹ := by
    intro b hb
    have h1 := hind_x ⟨b, hb⟩
    have h2 := hind_m ⟨b, hb⟩
    rw [h2] at h1
    exact h1.symm
  have hx_range : B89.rhoG hE x ∈ E.normalizerMonoidHom.range :=
    MonoidHom.mem_range.mpr ⟨⟨x, hxX⟩, kappa_eq_rhoG hE hxX hxN⟩
  have ht_range : B89.rhoG hE t ∈ E.normalizerMonoidHom.range :=
    MonoidHom.mem_range.mpr ⟨⟨t, B89.t_mem_X hE⟩, kappa_t hE⟩
  rcases rhoG_eq_or F hE hx hmL hmB hind with h | h
  · rw [← h]
    exact hx_range
  · have hm_eq : B89.rhoG hE m = (B89.rhoG hE t)⁻¹ * B89.rhoG hE x := by
      rw [h]
      group
    rw [hm_eq]
    exact (E.normalizerMonoidHom.range).mul_mem
      ((E.normalizerMonoidHom.range).inv_mem ht_range) hx_range

theorem autIn_eq (F : Sec8T84Base) (h89 : Asc82Lemma89) (hE : Sec8E G t L S z g B E) :
    autIn L B = autIn (centralizer ({t} : Set G)) B := by
  have hLt : L ≤ centralizer ({t} : Set G) := hE.ctx.toSec3SettingLB.component.le
  have hcardL : Nat.card ↥(autIn L B) = 360 := by
    obtain ⟨φ⟩ := (A3.aut_B_of F hE.ctx).1
    rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hcardC : Nat.card ↥(autIn (centralizer ({t} : Set G)) B) = 360 := by
    obtain ⟨φ⟩ := h89 G t L S z g B hE.ctx
    rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  haveI : Finite ↥(autIn (centralizer ({t} : Set G)) B) :=
    Nat.finite_of_card_ne_zero (by rw [hcardC]; norm_num)
  exact Subgroup.eq_of_le_of_card_ge (B89.autIn_mono hLt)
    (le_of_eq (by rw [hcardC, hcardL]))

theorem cent_range (F : Sec8T84Base) (h89 : Asc82Lemma89) (hE : Sec8E G t L S z g B E) :
    ∀ c ∈ E.normalizerMonoidHom.range, c * B89.rhoG hE t = B89.rhoG hE t * c →
      c ∈ B89.Abar hE ⊔ zpowers (B89.rhoG hE t) := by
  intro c hc hcomm
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hc
  let xt : ↥(normalizer (E : Set G)) := ⟨t, B89.t_mem_X hE⟩
  have hκt : E.normalizerMonoidHom xt = B89.rhoG hE t := kappa_t hE
  have hcomm1 : E.normalizerMonoidHom (x * xt * x⁻¹ * xt⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hκt, hcomm]
    group
  have hcm : (x : G) * t * (x : G)⁻¹ * t⁻¹ ∈ centralizer (E : Set G) := by
    have h := (kappa_eq_one_iff E (x * xt * x⁻¹ * xt⁻¹)).mp hcomm1
    simpa [xt] using h
  obtain ⟨c', hc'cent, hc'comm⟩ := F.hCX G t L S z g B E hE (x : G) x.2 hcm
  have hc'n : c' ∈ normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer (E : Set G) hc'cent
  let y : G := (x : G) * c'
  have hyct : y * t = t * y := hc'comm
  have hyX : y ∈ normalizer (E : Set G) := (normalizer (E : Set G)).mul_mem x.2 hc'n
  have hy_inf : y ∈ normalizer (E : Set G) ⊓ centralizer ({t} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hyX, Subgroup.mem_centralizer_singleton_iff.mpr hyct⟩
  have hyN : y ∈ Nsub8 t B := B89.XCt_le_N hE hy_inf
  have hyB : y ∈ normalizer (B : Set G) := B89.XCt_le_NB hE hy_inf
  let yN : ↥(normalizer (E : Set G)) := ⟨y, hyX⟩
  have hκy : E.normalizerMonoidHom yN = E.normalizerMonoidHom x := by
    have h : yN = x * ⟨c', hc'n⟩ := Subtype.ext rfl
    rw [h, map_mul, (kappa_eq_one_iff E ⟨c', hc'n⟩).mpr hc'cent, mul_one]
  have hβ : sec1011_conjAut B y hyB ∈ autIn L B := by
    have h1 : sec1011_conjAut B y hyB ∈ autIn (centralizer ({t} : Set G)) B :=
      B89.mem_autIn_of_induces (Subgroup.mem_centralizer_singleton_iff.mpr hyct)
        (B89.induces_conjAut B hyB)
    rwa [← autIn_eq F h89 hE] at h1
  obtain ⟨m, hmL, hInd_m⟩ := B89.exists_induces hβ
  have hmB : m ∈ normalizer (B : Set G) := hInd_m.mem_normalizer
  have hind : ∀ b ∈ B, y * b * y⁻¹ = m * b * m⁻¹ := by
    intro b hb
    have h1 := (B89.induces_conjAut B hyB) ⟨b, hb⟩
    have h2 := hInd_m ⟨b, hb⟩
    rw [h2] at h1
    exact h1.symm
  rcases rhoG_eq_or F hE hy_inf hmL hmB hind with h | h
  · have hxeq : E.normalizerMonoidHom x = B89.rhoG hE m := by
      rw [← hκy, kappa_eq_rhoG hE hyX hyN, h]
    rw [hxeq]
    exact Subgroup.mem_sup_left (B89.rhoG_mem_Abar hE hmL hmB)
  · have hxeq : E.normalizerMonoidHom x = B89.rhoG hE t * B89.rhoG hE m := by
      rw [← hκy, kappa_eq_rhoG hE hyX hyN, h]
    rw [hxeq, sup_comm]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers _) (B89.rhoG_mem_Abar hE hmL hmB)

theorem hctx_of (F : Sec8T84Base) (h89 : Asc82Lemma89) (hE : Sec8E G t L S z g B E) :
    HCtx E B (B89.rhoG hE t) (B89.Abar hE) E.normalizerMonoidHom.range :=
  { hE := hE.elem
    hB := hE.ctx.B_e16
    hBE := B89.B_le_E hE
    u_sq := B89.rhoG_t_mul_self hE
    fix := B89.rhoG_t_fix_iff hE
    A_iso := B89.Abar_equiv_A6 F hE
    A_comm := fun a ha => B89.Abar_comm_u hE ha
    A_faith := fun a ha h => B89.Abar_faithful F hE ha h
    u_H := MonoidHom.mem_range.mpr ⟨⟨t, B89.t_mem_X hE⟩, kappa_t hE⟩
    A_H := Abar_le_range F hE
    u_A := B89.u_not_mem_Abar F hE
    cent := cent_range F h89 hE }

end C10

end CFSG.OddStandard.SmallF3.Omega
