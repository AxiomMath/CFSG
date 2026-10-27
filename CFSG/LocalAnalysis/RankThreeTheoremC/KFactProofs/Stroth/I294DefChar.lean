module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Out
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeDefChar

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup

private theorem pPrimeCore_eq_bot_of_bijective {p : ℕ} {A B : Type*} [Group A] [Group B]
    {C : Subgroup A} {T : Subgroup B} (f : C →* T) (hf : Function.Bijective f)
    (hT : GLAPPrimeCoreOf p T = ⊥) : GLAPPrimeCoreOf p C = ⊥ := by
  have hN : CFSG.pPrimeCore p ↥C = ⊥ := by
    rw [eq_bot_iff]
    unfold CFSG.pPrimeCore
    apply sSup_le
    rintro K ⟨hKn, hKc⟩
    have h1 : (K.map f).Normal := Subgroup.Normal.map hKn f hf.2
    have h2 : Nat.Coprime p (Nat.card (K.map f)) := by
      rw [Subgroup.card_map_of_injective hf.1]
      exact hKc
    have h3 : K.map f ≤ CFSG.pPrimeCore p ↥T := le_sSup ⟨h1, h2⟩
    have h4 : CFSG.pPrimeCore p ↥T = ⊥ := by
      have h5 : (CFSG.pPrimeCore p ↥T).map T.subtype = ⊥ := hT
      exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective T)).1 h5
    rw [h4, le_bot_iff] at h3
    exact ((Subgroup.map_eq_bot_iff_of_injective K hf.1).1 h3).le
  show (CFSG.pPrimeCore p ↥C).map C.subtype = ⊥
  rw [hN, Subgroup.map_bot]

private theorem pPrimeCore_centralizer_eq_bot_of_injective {p : ℕ} {Y G' : Type*} [Group Y]
    [Group G'] {ρ : Y →* G'} (hρ : Function.Injective ρ) (w : Y)
    (hcore : GLAPPrimeCoreOf p (ρ.range ⊓ Subgroup.centralizer ({ρ w} : Set G')) = ⊥) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({w} : Set Y)) = ⊥ := by
  have hmemT : ∀ c : Subgroup.centralizer ({w} : Set Y),
      ρ (c : Y) ∈ ρ.range ⊓ Subgroup.centralizer ({ρ w} : Set G') := by
    intro c
    have hc : (c : Y) * w = w * (c : Y) := Subgroup.mem_centralizer_singleton_iff.1 c.2
    refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_range.2 ⟨(c : Y), rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hc]
  refine pPrimeCore_eq_bot_of_bijective
    ((ρ.comp (Subgroup.centralizer ({w} : Set Y)).subtype).codRestrict
      (ρ.range ⊓ Subgroup.centralizer ({ρ w} : Set G')) hmemT) ⟨?_, ?_⟩ hcore
  · intro c₁ c₂ h12
    apply Subtype.ext
    apply hρ
    exact congrArg Subtype.val h12
  · intro t
    obtain ⟨hint, hcent⟩ := Subgroup.mem_inf.1 t.2
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hint
    have hcent' : (t : G') * ρ w = ρ w * (t : G') :=
      Subgroup.mem_centralizer_singleton_iff.1 hcent
    rw [← hc, ← map_mul, ← map_mul] at hcent'
    have hcC : c ∈ Subgroup.centralizer ({w} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.2 (hρ hcent')
    exact ⟨⟨c, hcC⟩, Subtype.ext hc⟩

theorem pPrimeCore_centralizer_eq_bot_of_charP
    (hCore : CFSG.HardMathSupport.Timmesfeld.Coordinator.DefCharInnerCoreFree)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    [L.Normal] (hLs : IsSimpleGroup L) (hLn : ∃ a b : L, a * b ≠ b * a)
    (hC : centralizer (L : Set Y) = ⊥) (d : TauCeti.ValidLieTypeIndex)
    (hch : d.1.characteristic = p) (e : Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie d).Group))
    {w : Y} (hwL : w ∈ L) (hwo : orderOf w = p) :
    GLAPPrimeCoreOf p (centralizer ({w} : Set Y)) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hρ : Function.Injective (MulAut.conjNormal : Y →* MulAut ↥L) :=
    i294_conjNormal_injective hC
  have hxval : (MulAut.conjNormal : Y →* MulAut ↥L) w = MulAut.conj (⟨w, hwL⟩ : ↥L) :=
    MulAut.conjNormal_val (h := (⟨w, hwL⟩ : ↥L))
  have hxI : (MulAut.conjNormal : Y →* MulAut ↥L) w ∈ (MulAut.conj : ↥L →* MulAut ↥L).range :=
    MonoidHom.mem_range.2 ⟨⟨w, hwL⟩, hxval.symm⟩
  have hxo : orderOf ((MulAut.conjNormal : Y →* MulAut ↥L) w) = p :=
    (orderOf_injective _ hρ w).trans hwo
  have hH : (MulAut.conj : ↥L →* MulAut ↥L).range ≤
      (MulAut.conjNormal : Y →* MulAut ↥L).range := by
    rintro β ⟨l, rfl⟩
    exact MonoidHom.mem_range.2 ⟨(l : Y), MulAut.conjNormal_val (h := l)⟩
  have hcore := hCore ↥L hLs hLn d e p hp hp2 hch
    ((MulAut.conjNormal : Y →* MulAut ↥L) w) hxI hxo
    (MulAut.conjNormal : Y →* MulAut ↥L).range hH
  exact pPrimeCore_centralizer_eq_bot_of_injective hρ w hcore

theorem I294Cfg.pPrimeCore_eq_bot_of_defCharInnerCoreFree
    (hCore : CFSG.HardMathSupport.Timmesfeld.Coordinator.DefCharInnerCoreFree)
    {p : ℕ} {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal] {z g : Y}
    {D : Subgroup Y} (h : I294Cfg p L z g D) (hDL : D ≤ L) (d : TauCeti.ValidLieTypeIndex)
    (hch : d.1.characteristic = p)
    (e : Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie d).Group)) {w : Y} (hw : w ∈ D) (hw1 : w ≠ 1) :
    GLAPPrimeCoreOf p (centralizer ({w} : Set Y)) = ⊥ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  exact pPrimeCore_centralizer_eq_bot_of_charP hCore h.prime h.odd h.simple h.nonab h.cent d hch e
    (hDL hw) (orderOf_eq_prime (h.elem.2 w hw) hw1)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
