module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F0B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8_SL_le_N (h36 : Asc82Lemma36) (hM : Asc82Tab6M) {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G} (hctx : Sec8Ctx G t L S z g B) :
    S ⊓ L ≤ Nsub8 t B := by
  have hLcent : L ≤ centralizer ({t} : Set G) := hctx.component.le
  have hNmem : ∀ c ∈ centralizer ({t} : Set G), c ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 hctx.toSec3SettingLB
  have hP : IsSylow2Of (S ⊓ L) L :=
    sec4_isSylow2Of_inf hLcent hNmem hctx.sylow
  have hLM : IsOm6M L := ⟨hctx.component.isQuasisimple, hctx.omega6m⟩
  obtain ⟨B₁, B₂, _hBne, hB₁n, hB₂n, huniq⟩ :=
    hM.sylow_E16 G L hLM (S ⊓ L) hP
  have hBle : B ≤ S ⊓ L := by
    rw [inf_comm]
    exact hctx.B_le
  have hBeq : B = B₁ ∨ B = B₂ := huniq B hBle hctx.B_e16
  have hnormB : S ⊓ L ≤ normalizer (B : Set G) := by
    rcases hBeq with h | h
    · rw [h]
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hB₁n.1).mp hB₁n.2.2
    · rw [h]
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hB₂n.1).mp hB₂n.2.2
  intro x hx
  have hxnT : x ∈ normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    have h1 : x ∈ normalizer ({t} : Set G) :=
      Subgroup.centralizer_le_normalizer {t} (hLcent hx.2)
    have h2 : x ∈ normalizer ((Subgroup.closure {t} : Subgroup G) : Set G) :=
      Subgroup.normalizer_le_normalizer_closure {t} h1
    rwa [← Subgroup.zpowers_eq_closure] at h2
  have hxnB : x ∈ normalizer (B : Set G) := hnormB hx
  exact Subgroup.inf_normalizer_le_normalizer_sup (Subgroup.zpowers t) B ⟨hxnT, hxnB⟩

theorem sec8_goodE (h36 : Asc82Lemma36) (hM : Asc82Tab6M) (h8A : Asc82Lemma8A) {G : Type}
    [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B E : Subgroup G}
    (hE : Sec8E G t L S z g B E) :
    ∃ E' : Subgroup G, Sec8E G t L S z g B E' ∧ S ⊓ L ≤ normalizer (E' : Set G) := by
  have hQN : S ⊓ L ≤ Nsub8 t B := sec8_SL_le_N h36 hM hE.ctx
  have hMN : E ⊔ oddCoreIn (Nsub8 t B) ≤ Nsub8 t B :=
    sup_le hE.le_N (CFSG.ClassicalInvolution.Balance.oddCoreIn_le (Nsub8 t B))
  have hNnormM : Nsub8 t B ≤
      normalizer ((E ⊔ oddCoreIn (Nsub8 t B) : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMN).mp hE.normal
  have hQM : ∀ q ∈ S ⊓ L, ∀ m ∈ E ⊔ oddCoreIn (Nsub8 t B),
      q * m * q⁻¹ ∈ E ⊔ oddCoreIn (Nsub8 t B) :=
    Subgroup.le_normalizer_iff.mp (hQN.trans hNnormM)
  have hOn : ∀ m ∈ E ⊔ oddCoreIn (Nsub8 t B), ∀ o ∈ oddCoreIn (Nsub8 t B),
      m * o * m⁻¹ ∈ oddCoreIn (Nsub8 t B) :=
    fun m hm o ho => CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn (hMN hm) ho
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 8) hE.elem.2
  have hQ2 : IsPGroup 2 ↥(S ⊓ L) := (hE.ctx.sylow.2.1).to_le inf_le_left
  obtain ⟨u, huO, hunorm⟩ :=
    exists_odd_conj_normalized (M := E ⊔ oddCoreIn (Nsub8 t B))
      (O := oddCoreIn (Nsub8 t B)) (Q := S ⊓ L) (E := E)
      le_sup_right hOn (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (Nsub8 t B))
      le_sup_left hE2 rfl hQ2 hQM
  exact ⟨E.map (MulAut.conj u).toMonoidHom, sec8E_conj_oddCore h8A hE huO,
    fun q hq => hunorm q hq⟩

end CFSG.OddStandard.SmallF3.Omega
