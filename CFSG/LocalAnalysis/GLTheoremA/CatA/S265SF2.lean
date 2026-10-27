module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04LUGen
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.GroupTheory.PLayer.Transport
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerComponentDvd
import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Component
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

namespace SF

section Layer

variable {R : Type} [Group R] [Finite R] {p : ℕ}

theorem glaPLayer_ne_bot_of_luCore (hp : p.Prime) {α : MulAut R} {L : Subgroup R}
    (hL : LUCore p α L) : GLAPLayer p (fixSubgroup α) ≠ ⊥ := by
  obtain ⟨hLf, hs, hna, hpL, hn⟩ := hL
  have hLf' : L ≤ fixSubgroup α := hLf
  have hnorm : (L.subgroupOf (fixSubgroup α)).Normal := ⟨fun y hy g => by
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    simpa using hn g g.2 y hy⟩
  have hc := GL83.PiGen.glaPComponent_of_normal_simple hp hLf' hnorm hna hpL
  intro hbot
  have hle : L ≤ GLAPLayer p (fixSubgroup α) := le_sSup hc
  rw [hbot] at hle
  obtain ⟨a, b, hab⟩ := hna
  have h1 : ∀ y : ↥L, y = 1 := fun y => Subtype.ext (Subgroup.mem_bot.1 (hle y.2))
  exact hab (by rw [h1 a, h1 b])

theorem glaPLayer_ne_bot_of_le_glaLayer (hp : p.Prime) {C P : Subgroup R}
    (hP : P ≤ GLALayer C) (hpP : p ∣ Nat.card P) : GLAPLayer p C ≠ ⊥ := by
  obtain ⟨J, hJ, hpJ⟩ := CFSG.exists_glaPComponent_dvd_card_of_dvd_card_glaLayer hp
    (hpP.trans (Subgroup.card_dvd_of_le hP))
  intro hbot
  have hle : J ≤ GLAPLayer p C := le_sSup hJ
  rw [hbot, le_bot_iff] at hle
  rw [hle, Subgroup.card_bot] at hpJ
  exact hp.one_lt.ne' (Nat.dvd_one.1 hpJ)

end Layer

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem exists_aut_nl {p : ℕ} {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSNL p S B T x D K) {R : Type} [Group R] (θ : ↥K ⧸ Subgroup.center ↥K ≃* R) :
    ∃ X : Subgroup (MulAut R), IsElemAbelian p X ∧ Nat.card B = Nat.card D * Nat.card X ∧
      ∀ α ∈ X, α ≠ 1 → GLAPLayer p (fixSubgroup α) = ⊥ := by
  obtain ⟨hDB, -, -, -, -, hKcomp, hDK⟩ := h.cfg.std
  have hperf : Group.IsPerfect ↥K := ⟨hKcomp.2.2.1⟩
  haveI : Finite R := Finite.of_equiv _ θ.toEquiv
  have hSN : B ≤ Subgroup.normalizer (S : Set Ω) := fun g _ =>
    (Subgroup.normalizer_eq_top_iff.2 h.cfg.normal) ▸ Subgroup.mem_top g
  have hBN := S171.B_norm_K h.cfg.elem hSN h.cfg.std
  obtain ⟨φ, hφ1, hφc, hφl⟩ : ∃ φ : ↥B →* MulAut (↥K ⧸ Subgroup.center ↥K),
      (∀ b : ↥B, φ b = 1 ↔ (b : Ω) ∈ D) ∧ Nat.card φ.range = D.relIndex B ∧
      ∀ b : ↥B, (b : Ω) ∉ D → GLAPLayer p (fixSubgroup (φ b)) = ⊥ := by
    refine ⟨CFSG.normalizerToCenterQuotientAut K B hBN, fun b => ?_, ?_, fun b hb => ?_⟩
    · rw [CFSG.normalizerToCenterQuotientAut_eq_one_iff hperf hBN b, ← hDK]
    · rw [CFSG.card_range_normalizerToCenterQuotientAut hperf hBN, ← hDK]
    · exact (CFSG.glaPLayer_inf_centralizer_eq_bot_iff h.cfg.prime hBN b).1 (h.nl b b.2 hb)
  have hcomm : ∀ a c : ↥B, a * c = c * a := fun a c => h.cfg.elem.1.is_comm.comm a c
  refine ⟨((MulAut.congr θ).toMonoidHom.comp φ).range, ⟨⟨⟨fun a c => ?_⟩⟩, ?_⟩, ?_, ?_⟩
  · obtain ⟨_, b, rfl⟩ := a
    obtain ⟨_, c, rfl⟩ := c
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← map_mul, ← map_mul, hcomm])
  · rintro _ ⟨b, rfl⟩
    have hb : b ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h.cfg.elem.2 _ b.2)
    rw [← map_pow, hb, map_one]
  · have hX : Nat.card ((MulAut.congr θ).toMonoidHom.comp φ).range = D.relIndex B := by
      rw [MonoidHom.range_comp, Subgroup.card_map_of_injective
        (f := (MulAut.congr θ).toMonoidHom) (MulAut.congr θ).injective, hφc]
    have h1 := (Subgroup.relIndex_mul_card (H := D) (K := B)).symm
    rwa [inf_of_le_left hDB, mul_comm, ← hX] at h1
  · rintro _ ⟨b, rfl⟩ hb1
    have hbD : (b : Ω) ∉ D := fun hmem => hb1 (by
      change MulAut.congr θ (φ b) = 1
      rw [(hφ1 b).2 hmem, map_one])
    change GLAPLayer p (fixSubgroup (MulAut.congr θ (φ b))) = ⊥
    rw [CFSG.glaPLayer_fixSubgroup_congr h.cfg.prime θ (φ b), hφl b hbD, Subgroup.map_bot]

end SF

end CFSG.LocalAnalysis.GLTheoremA.S265

end
