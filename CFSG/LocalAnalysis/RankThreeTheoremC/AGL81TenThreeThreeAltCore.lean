module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SylNormSymProd
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineOddInnWPerm
public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.Action
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ExtensionPCore
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairModelCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open CFSG.Open CFSG.AGLEmbedding Subgroup Equiv
open CFSG.HardMathSupport.RichardWeiss.Coordinator (ConjSpec eq_one_of_commute_alternatingGroup)
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (pCore_eq_ker_of_pCore_eq_bot
  sectionEquiv sectionEquiv_coe)

theorem eq_one_of_centralizes_wSup {Q T : Type} [Group Q] [Group T] [Finite Q] {P : Subgroup Q}
    (f : ↥P →* T) (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker)
    (hT2 : CFSG.pCore 2 T = ⊥) (hC : ∀ t : T, (∀ u ∈ wSup T, t * u = u * t) → t = 1)
    {p₀ : Q} (hp₀ : p₀ ∈ P) (hodd : Odd (orderOf p₀))
    (hW : ∀ w (hw : w ∈ P), QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∈
      wSup (↥P ⧸ CFSG.pCore 2 ↥P) → p₀ * w * p₀⁻¹ * w⁻¹ ∈ pCoreOf 2 P) : p₀ = 1 := by
  have hcore : CFSG.pCore 2 ↥P = f.ker := pCore_eq_ker_of_pCore_eq_bot hT2 f hf hker
  let e : (↥P ⧸ CFSG.pCore 2 ↥P) ≃* T :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he : ∀ w : ↥P, e (QuotientGroup.mk' (CFSG.pCore 2 ↥P) w) = f w := fun w => rfl
  set x : ↥P := ⟨p₀, hp₀⟩ with hx
  have hfx : f x = 1 := by
    refine hC _ fun u hu => ?_
    obtain ⟨w, rfl⟩ := hf u
    have hmk : QuotientGroup.mk' (CFSG.pCore 2 ↥P) w ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P) := by
      rw [← map_wSup_eq e.symm]
      exact ⟨f w, hu, by rw [← he w]; exact e.symm_apply_apply _⟩
    obtain ⟨c, hc, hce⟩ := hW w w.2 hmk
    have hc' : c = x * w * x⁻¹ * w⁻¹ := Subtype.ext (by simpa [x] using hce)
    rw [hcore, hc'] at hc
    have hc2 : f (x * w * x⁻¹ * w⁻¹) = 1 := hc
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hc2
    calc f x * f w = (f x * f w * (f x)⁻¹ * (f w)⁻¹) * (f w * f x) := by group
      _ = f w * f x := by rw [hc2, one_mul]
  obtain ⟨k, hk⟩ := hker ⟨x, hfx⟩
  have hdvd : orderOf p₀ ∣ 2 ^ k := by
    refine orderOf_dvd_of_pow_eq_one ?_
    have := congrArg (fun y : ↥f.ker => ((y : ↥P) : Q)) hk
    simpa [x] using this
  have h2 : Nat.Coprime (orderOf p₀) 2 := Nat.coprime_comm.mp
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr fun ⟨c, hc⟩ => by
      obtain ⟨d, hd⟩ := hodd
      omega)
  have hcop : Nat.Coprime (orderOf p₀) (2 ^ k) := Nat.Coprime.pow_right k h2
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem centralizer_wSup_perm {n : ℕ} (hn : n = 1 ∨ n = 3 ∨ 5 ≤ n) (t : Perm (Fin n))
    (h : ∀ u ∈ wSup (Perm (Fin n)), t * u = u * t) : t = 1 := by
  rcases hn with rfl | rfl | hn
  · exact Subsingleton.elim _ _
  · have hW : (⊤ : Subgroup (Perm (Fin 3))) ≤ wSup (Perm (Fin 3)) :=
      le_wSup_of_normal_symThree inferInstance Subgroup.topEquiv
    have h1 := h (swap 0 1) (hW (mem_top _))
    have h2 := h (finRotate 3) (hW (mem_top _))
    clear h hW
    revert t
    decide
  · exact eq_one_of_commute_alternatingGroup (by simpa using hn) fun a ha =>
      h a (alternatingGroup_le_wSup hn ha)

theorem centralizer_wSup_perm_prod {r s : ℕ} (hr : r = 1 ∨ r = 3 ∨ 5 ≤ r) (hs : 5 ≤ s)
    (t : Perm (Fin r) × Perm (Fin s))
    (h : ∀ u ∈ wSup (Perm (Fin r) × Perm (Fin s)), t * u = u * t) : t = 1 := by
  obtain ⟨a, c⟩ := t
  have hc : c = 1 := eq_one_of_commute_alternatingGroup (by simpa using hs) fun u hu => by
    have := h (1, u) (bot_prod_alternatingGroup_le_wSup hs ⟨one_mem _, hu⟩)
    exact congrArg Prod.snd this
  have ha : a = 1 := by
    rcases hr with rfl | rfl | hr
    · exact Subsingleton.elim _ _
    · exact centralizer_wSup_perm (Or.inr (Or.inl rfl)) a fun u _ =>
        congrArg Prod.fst (h (u, 1) (perm_three_prod_bot_le_wSup ⟨mem_top _, one_mem _⟩))
    · exact eq_one_of_commute_alternatingGroup (by simpa using hr) fun u hu =>
        congrArg Prod.fst (h (u, 1) (alternatingGroup_prod_bot_le_wSup hr ⟨hu, one_mem _⟩))
  rw [ha, hc]
  rfl

theorem centralizes_of_model {Q : Type} [Group Q] [Finite Q] {Lb P : Subgroup Q} (hPL : P ≤ Lb)
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (φ : ↥Lb ≃* ↥(alternatingGroup Ω))
    {R : Subgroup ↥(alternatingGroup Ω)} (hR : (P.subgroupOf Lb).map φ.toMonoidHom = R)
    {T : Type} [Group T] (g : ↥R →* T) (hg : Function.Surjective g) (hker : IsPGroup 2 g.ker)
    (hT2 : CFSG.pCore 2 T = ⊥) (hC : ∀ t : T, (∀ u ∈ wSup T, t * u = u * t) → t = 1)
    {β : Q} (hβ : β ∈ normalizer (Lb : Set Q)) {σ : Perm Ω} (hσ : ConjSpec φ β σ)
    (hσA : σ ∈ alternatingGroup Ω) (hσR : (⟨σ, hσA⟩ : ↥(alternatingGroup Ω)) ∈ R)
    (hodd : Odd (orderOf σ))
    (hW : ∀ w (hw : w ∈ P), QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∈
      wSup (↥P ⧸ CFSG.pCore 2 ↥P) → β * w * β⁻¹ * w⁻¹ ∈ pCoreOf 2 P) :
    ∀ y ∈ Lb, β * y = y * β := by
  set σ' : ↥(alternatingGroup Ω) := ⟨σ, hσA⟩ with hσ'
  set l₀ : ↥Lb := φ.symm σ' with hl₀
  have hact : ∀ c : ↥Lb, β * (c : Q) * β⁻¹ = (l₀ : Q) * c * (l₀ : Q)⁻¹ := by
    intro c
    have hcm : β * (c : Q) * β⁻¹ ∈ Lb := (mem_normalizer_iff.1 hβ c).1 c.2
    have h1 := hσ c ⟨_, hcm⟩ rfl
    have h2 : φ ⟨_, hcm⟩ = φ (l₀ * c * l₀⁻¹) := by
      apply Subtype.ext
      rw [h1, map_mul, map_mul, map_inv, hl₀, MulEquiv.apply_symm_apply]
      rfl
    have := congrArg Subtype.val (φ.injective h2)
    simpa using this
  have hl₀P : (l₀ : Q) ∈ P := by
    rw [← hR] at hσR
    obtain ⟨l, hl, hle⟩ := hσR
    have : l = l₀ := by
      rw [hl₀, ← hle]
      exact (φ.symm_apply_apply l).symm
    rw [← this]
    exact hl
  have hodd₀ : Odd (orderOf (l₀ : Q)) := by
    rw [Subgroup.orderOf_coe, hl₀, MulEquiv.orderOf_eq, hσ', Subgroup.orderOf_mk]
    exact hodd
  set e := sectionEquiv hPL φ R hR
  have h1 : (l₀ : Q) = 1 := by
    refine eq_one_of_centralizes_wSup (g.comp e.toMonoidHom) (hg.comp e.surjective) ?_ hT2 hC
      hl₀P hodd₀ fun w hw hwW => ?_
    · rw [← MonoidHom.comap_ker]
      exact hker.comap_of_injective _ e.injective
    · rw [← hact ⟨w, hPL hw⟩]
      exact hW w hw hwW
  intro y hy
  have h2 := hact ⟨y, hy⟩
  rw [h1] at h2
  simp only [one_mul, inv_one, mul_one] at h2
  calc β * y = (β * y * β⁻¹) * β := by group
    _ = y * β := by rw [h2]

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
