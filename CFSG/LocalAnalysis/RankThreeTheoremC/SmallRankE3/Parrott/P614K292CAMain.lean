module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292CAParity

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
open P614K292

namespace P614K292CA

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X} {Px B : Subgroup X}
  {p f : ℕ} {K : Type} [Field K] {y : GL (Fin 3) K}

theorem commute_of_inf_eq_bot {π : Bool} {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}
    (S : ShapeThree L x B π p f K ν y) {T : Subgroup X} (hT : IsPGroup 2 T)
    (hxT : x ∈ normalizer (T : Set X)) (hTL : T ⊓ L = ⊥) {t : X} (ht : t ∈ T) :
    t * x = x * t := by
  have hcT : t * x * t⁻¹ * x⁻¹ ∈ T := by
    have h1 : x * t⁻¹ * x⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hxT t⁻¹).1 (inv_mem ht)
    simpa only [mul_assoc] using mul_mem ht h1
  have hc2 : IsPGroup 2 (zpowers (t * x * t⁻¹ * x⁻¹)) := hT.to_le (Subgroup.zpowers_le.2 hcT)
  obtain ⟨c, hc⟩ := S.comm t x
  have hc1 : t * x * t⁻¹ * x⁻¹ = 1 := by
    have h : t * x * t⁻¹ * x⁻¹ ∈ T ⊓ L := Subgroup.mem_inf.2 ⟨hcT, S.two_mem _ hc2 c hc⟩
    rw [hTL] at h
    exact h
  calc t * x = (t * x * t⁻¹ * x⁻¹) * (x * t) := by group
    _ = x * t := by rw [hc1, one_mul]

theorem caseA_uni (hUni : KD292UniOuter3) {ν : ↥(slPi false 3 (p ^ f) K) →* ↥L}
    (cfg : LinUniCfgThree L x Px B) (S : ShapeThree L x B false p f K ν y) {T : Subgroup X}
    (hT : IsPGroup 2 T) (hcomm : ∀ t ∈ T, t * x = x * t) (hTL : T ⊓ L = ⊥) : T = ⊥ := by
  haveI : L.Normal := cfg.setup.normal
  have M := S.model
  let e : ↥(slPi false 3 (p ^ f) K) ≃* ↥L := MulEquiv.ofBijective ν ⟨S.inj, M.surj⟩
  let Φ : X →* MulAut ↥(slPi false 3 (p ^ f) K) :=
    (MulAut.congr e.symm).toMonoidHom.comp MulAut.conjNormal
  have hΦ : ∀ (t : X) (s : ↥(slPi false 3 (p ^ f) K)),
      ((ν (Φ t s) : ↥L) : X) = t * ((ν s : ↥L) : X) * t⁻¹ := by
    intro t s
    change ((e (e.symm (MulAut.conjNormal t (e s))) : ↥L) : X) = t * ((e s : ↥L) : X) * t⁻¹
    rw [MulEquiv.apply_symm_apply, MulAut.conjNormal_apply]
  rw [eq_bot_iff]
  intro t ht
  obtain ⟨n, hn⟩ := hT ⟨t, ht⟩
  have htn : t ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hα : Φ t ^ 2 ^ n = 1 := by rw [← map_pow, htn, map_one]
  have hαy : ∀ s s' : ↥(slPi false 3 (p ^ f) K), (s' : GL (Fin 3) K) = y * s * y⁻¹ →
      ((Φ t s' : ↥(slPi false 3 (p ^ f) K)) : GL (Fin 3) K) = y * Φ t s * y⁻¹ := by
    intro s s' hs'
    have h1 := S.lift.act s s' hs'
    have h2 := S.lift.act (Φ t s) (M.conjBy S.lift.mem (Φ t s)) (M.coe_conjBy S.lift.mem _)
    have h3 : Φ t s' = M.conjBy S.lift.mem (Φ t s) := by
      apply S.inj
      apply Subtype.ext
      rw [hΦ, ← h2, hΦ, ← h1]
      have hx' : x⁻¹ * t⁻¹ = t⁻¹ * x⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hcomm t ht]
      calc t * (x * ((ν s : ↥L) : X) * x⁻¹) * t⁻¹
          = (t * x) * ((ν s : ↥L) : X) * (x⁻¹ * t⁻¹) := by group
        _ = (x * t) * ((ν s : ↥L) : X) * (t⁻¹ * x⁻¹) := by rw [hcomm t ht, hx']
        _ = x * (t * ((ν s : ↥L) : X) * t⁻¹) * x⁻¹ := by group
    rw [h3, M.coe_conjBy]
  obtain ⟨g, hg, hgα⟩ :=
    hUni p f K y M.piField M.modThree M.two_lt S.typeThree (Φ t) ⟨n, hα⟩ hαy
  have hlift : IsLiftAt ν t g := by
    refine ⟨hg, fun s s' hs' => ?_⟩
    have h1 : s' = Φ t s := Subtype.ext (by rw [hs', hgα])
    rw [h1, hΦ]
  have h : t ∈ T ⊓ L :=
    Subgroup.mem_inf.2 ⟨ht, S.two_mem t (hT.to_le (Subgroup.zpowers_le.2 ht)) g hlift⟩
  rwa [hTL] at h

theorem caseA_lin (hLin : KD292ThreeFrameLin3) {ν : ↥(slPi true 3 (p ^ f) K) →* ↥L}
    (cfg : LinUniCfgThree L x Px B) (S : ShapeThree L x B true p f K ν y) {T : Subgroup X}
    (hT : IsPGroup 2 T) (hcomm : ∀ t ∈ T, t * x = x * t) :
    ∃ v : Fin 3 → K, v ≠ 0 ∧ T ≤ normalizer (threeFrameIn ν y v : Set X) := by
  haveI : L.Normal := cfg.setup.normal
  obtain ⟨ha, hodd⟩ :=
    hLin p f K y S.model.piField S.model.modThree S.model.two_lt S.typeThree
  rw [← card_candsX S.model S.inj S.lift] at hodd
  obtain ⟨E, hE, hTE⟩ := exists_cand_le_normalizer hT hcomm hodd
  rw [candsX_eq_image S.model S.inj S.lift] at hE
  obtain ⟨E', hE', rfl⟩ := hE
  obtain ⟨v, hv, rfl⟩ := ha E' hE'
  rw [← threeFrameIn_eq_transp] at hTE
  exact ⟨v, hv, hTE⟩

end P614K292CA

theorem kD292CaseA3_holds : KD292CaseA3 := by
  intro hLin hUni X _ _ L x Px B π p f K _ ν y cfg S T hT hxT hTL
  have hcomm : ∀ t ∈ T, t * x = x * t := fun t ht =>
    P614K292CA.commute_of_inf_eq_bot S hT hxT hTL ht
  refine ⟨fun hπ => ?_, fun hπ => ?_⟩
  · subst hπ
    exact P614K292CA.caseA_lin hLin cfg S hT hcomm
  · subst hπ
    exact P614K292CA.caseA_uni hUni cfg S hT hcomm hTL

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
