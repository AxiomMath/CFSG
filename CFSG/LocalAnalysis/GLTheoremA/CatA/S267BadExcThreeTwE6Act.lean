module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6Vad
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcE6OneAct
import CFSG.GH74.Uniqueness.SU.SU13TA3Gen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

section Abstract

variable {Ω X : Type} [Group Ω] [Group X]

theorem actData_of_distinguished {p : ℕ} (hp : p.Prime) {B : Subgroup Ω} (hB : IsElemAbelian p B)
    (Γ : Ω →* MulAut X) (hBker : Nat.card ↥(B ⊓ Γ.ker) = p) (hB4 : p ^ 4 ≤ Nat.card B)
    {d₁ v₁ : MulAut X} (hd₁ : d₁ ∈ B.map Γ) (hd₁1 : d₁ ≠ 1) (hv₁ : v₁ ∈ B.map Γ)
    (hv₁d : v₁ ∉ Subgroup.zpowers d₁) {J : Subgroup X} {t : X}
    (hJ : GLAPComponent p (fixSubgroup d₁) J)
    (hJB : ∀ x ∈ B, J.map (Γ x).toMonoidHom = J)
    (hJk : ∀ x ∈ B, (∀ j ∈ J, j * (Γ x j)⁻¹ ∈ GLAPPrimeCoreOf p J) →
      Γ x ∈ Subgroup.zpowers d₁)
    (hJE : GLAPLayer p (J ⊓ fixSubgroup v₁) ≠ ⊥) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (htJ : J ≤ Subgroup.centralizer ({t} : Set X)) (htd : d₁ t = t) :
    ModelGen.ActData p B (fun x => Γ x) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hexp : ∀ a ∈ B.map Γ, a ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hB.2 x hx, map_one]
  have hcomm : ∀ a ∈ B.map Γ, ∀ b ∈ B.map Γ, Commute a b := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have h := congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    simp only [Subgroup.coe_mul] at h
    change Γ x * Γ y = Γ y * Γ x
    rw [← map_mul, ← map_mul, h]
  set U₁ := Subgroup.zpowers d₁ with hU₁
  set U₂ := Subgroup.zpowers d₁ ⊔ Subgroup.zpowers v₁ with hU₂
  have hU₁B : U₁ ≤ B.map Γ := Subgroup.zpowers_le.2 hd₁
  have hV₁B : Subgroup.zpowers v₁ ≤ B.map Γ := Subgroup.zpowers_le.2 hv₁
  have hU₂B : U₂ ≤ B.map Γ := sup_le hU₁B hV₁B
  have hv₁1 : v₁ ≠ 1 := fun h => hv₁d (h ▸ one_mem _)
  have hU₁c : Nat.card U₁ = p := by
    rw [hU₁, Nat.card_zpowers]
    exact orderOf_eq_prime (hexp _ hd₁) hd₁1
  have hV₁c : Nat.card (Subgroup.zpowers v₁) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hexp _ hv₁) hv₁1
  have hfinV : Finite ↥(Subgroup.zpowers v₁) :=
    Nat.finite_of_card_ne_zero (by rw [hV₁c]; exact hp.ne_zero)
  have hdisj : Disjoint (Subgroup.zpowers d₁) (Subgroup.zpowers v₁) := by
    rw [disjoint_iff]
    have hle : Subgroup.zpowers d₁ ⊓ Subgroup.zpowers v₁ ≤ Subgroup.zpowers v₁ := inf_le_right
    have hdvd : Nat.card ↥(Subgroup.zpowers d₁ ⊓ Subgroup.zpowers v₁) ∣ p :=
      hV₁c ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | hpc
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers d₁ ⊓ Subgroup.zpowers v₁ = Subgroup.zpowers v₁ :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hpc, hV₁c])
      have hv : v₁ ∈ Subgroup.zpowers d₁ ⊓ Subgroup.zpowers v₁ := by
        rw [heq]
        exact Subgroup.mem_zpowers v₁
      exact hv₁d hv.1
  have hU₂c : Nat.card U₂ = p ^ 2 := by
    rw [hU₂, CFSG.GH74.Uniqueness.SU.SU13.TA.card_sup_of_commute
      (fun a ha b hb => hcomm a (hU₁B ha) b (hV₁B hb)) hdisj, hU₁c, hV₁c, sq]
  set D := B ⊓ U₁.comap Γ with hD
  set E := B ⊓ U₂.comap Γ with hE
  have hDc : Nat.card D = p ^ 2 := by
    rw [hD, E6One.card_inf_comap_eq Γ hU₁B, hU₁c, hBker, sq]
  have hEc : Nat.card E = p ^ 3 := by
    rw [hE, E6One.card_inf_comap_eq Γ hU₂B, hU₂c, hBker]
    ring
  have hDE : D ≤ E := inf_le_inf_left _ (Subgroup.comap_mono le_sup_left)
  set α : ↥B → MulAut X := fun x => Γ x with hα
  have hfixD : ModelGen.actFix α D = fixSubgroup d₁ := by
    ext g
    rw [ModelGen.mem_actFix, mem_fixSubgroup]
    constructor
    · intro h
      obtain ⟨x, hx, hxd⟩ := hd₁
      have h1 := h ⟨x, hx⟩ ⟨hx, Subgroup.mem_comap.2 (hxd ▸ Subgroup.mem_zpowers _)⟩
      rwa [show α ⟨x, hx⟩ = d₁ from hxd] at h1
    · rintro h ⟨x, hxB⟩ ⟨-, hxU⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_comap.1 hxU)
      change Γ x g = g
      rw [← hk]
      exact (MulAction.stabilizer (MulAut X) g).zpow_mem (show d₁ • g = g from h) k
  have hfixE : ModelGen.actFix α E = fixSubgroup d₁ ⊓ fixSubgroup v₁ := by
    ext g
    rw [ModelGen.mem_actFix, Subgroup.mem_inf, mem_fixSubgroup, mem_fixSubgroup]
    constructor
    · intro h
      obtain ⟨x, hx, hxd⟩ := hd₁
      obtain ⟨y, hy, hyv⟩ := hv₁
      refine ⟨?_, ?_⟩
      · have h1 := h ⟨x, hx⟩ ⟨hx, Subgroup.mem_comap.2
          (hxd ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers _))⟩
        rwa [show α ⟨x, hx⟩ = d₁ from hxd] at h1
      · have h1 := h ⟨y, hy⟩ ⟨hy, Subgroup.mem_comap.2
          (hyv ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _))⟩
        rwa [show α ⟨y, hy⟩ = v₁ from hyv] at h1
    · rintro ⟨h1, h2⟩ ⟨x, hxB⟩ ⟨-, hxU⟩
      have hU : U₂ ≤ MulAction.stabilizer (MulAut X) g :=
        sup_le (Subgroup.zpowers_le.2 h1) (Subgroup.zpowers_le.2 h2)
      exact hU (Subgroup.mem_comap.1 hxU)
  have hJfix : J ≤ fixSubgroup d₁ := hJ.1
  have hJcomp : GLAPComponent p (ModelGen.actFix α D) J := by
    rw [hfixD]
    exact hJ
  have hJE' : Nat.card D = p ^ 2 → GLAPLayer p (J ⊓ ModelGen.actFix α E) ≠ ⊥ := by
    intro _
    rwa [hfixE, ← inf_assoc, inf_eq_left.2 hJfix]
  have htD : ∀ x : ↥B, (x : Ω) ∈ D → α x t = t := by
    rintro ⟨x, hxB⟩ ⟨-, hxU⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_comap.1 hxU)
    change Γ x t = t
    rw [← hk]
    exact (MulAction.stabilizer (MulAut X) t).zpow_mem (show d₁ • t = t from htd) k
  have hDBc : p ^ 2 * Nat.card D ≤ Nat.card B := by
    rw [hDc, ← pow_add]
    exact hB4
  exact ⟨D, E, J, t, inf_le_left, inf_le_left, hDE, hDc.ge, hDBc, fun _ => hEc, hJcomp,
    fun x => hJB x x.2, fun x hx => ⟨x.2, Subgroup.mem_comap.2 (hJk x x.2 hx)⟩, hJE', ht1, ht2,
    htJ, htD⟩

end Abstract

section Unique


open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.TableBExc.E6Three

theorem eq_of_le_of_isPGroup_twInndiag {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (h3 : ¬ 3 ∣ ℓ ^ f)
    {P : Subgroup (MulAut ↥(twistedE6RootGroup K σ))} (hP : IsPGroup 3 P)
    {X Y : Subgroup (MulAut ↥(twistedE6RootGroup K σ))}
    (hXI : X ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (hYI : Y ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) (hXP : X ≤ P) (hYP : Y ≤ P)
    (hX : IsElemAbelian 3 X) (hY : IsElemAbelian 3 Y) (hXc : Nat.card X = 3 ^ 6)
    (hYc : Nat.card Y = 3 ^ 6) : X = Y := by
  set φ := twistedE6InndiagConj K σ with hφdef
  have hφ : Function.Injective φ := twistedE6InndiagConj_injective hℓ hf hK σ hσ
  have hrange : φ.range = twistedE6Inn K σ ⊔ twistedE6Diag K σ := range_twistedE6InndiagConj K σ
  have hψ : Function.Injective (twInndiagHom K σ) :=
    twInndiagHom_injective (four_le_card_of_card_eq_sq hℓ hf hK) σ
  have hK3 : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    have h : (ℓ ^ f) ^ 2 % 3 = 1 := by
      rcases (by omega : ℓ ^ f % 3 = 1 ∨ ℓ ^ f % 3 = 2) with h | h <;> rw [Nat.pow_mod, h]
    have h1 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hP' : IsPGroup 3 (P.comap φ) := hP.comap_of_injective φ hφ
  have hlift : ∀ {Z : Subgroup (MulAut ↥(twistedE6RootGroup K σ))}, Z ≤ P →
      twInndiagLift K σ Z ≤ (P.comap φ).map (twInndiagHom K σ) := fun hZP =>
    Subgroup.map_mono (Subgroup.comap_mono hZP)
  have heq := E6One.eq_of_le_of_isPGroup hK3 (hP'.map (twInndiagHom K σ))
    (twInndiagLift_le_hatAut_range K σ X) (twInndiagLift_le_hatAut_range K σ Y) (hlift hXP)
    (hlift hYP) (isElemAbelian_twInndiagLift hℓ hf hK σ hσ hX)
    (isElemAbelian_twInndiagLift hℓ hf hK σ hσ hY)
    (by rw [card_twInndiagLift hℓ hf hK σ hσ hXI, hXc])
    (by rw [card_twInndiagLift hℓ hf hK σ hσ hYI, hYc])
  have hXr : X ≤ φ.range := hrange ▸ hXI
  have hYr : Y ≤ φ.range := hrange ▸ hYI
  have h1 : X.comap φ = Y.comap φ := Subgroup.map_injective hψ heq
  rw [← Subgroup.map_comap_eq_self hXr, ← Subgroup.map_comap_eq_self hYr, h1]

end Unique

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
