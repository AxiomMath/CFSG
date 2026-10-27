module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshModelSub
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshESModel

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.EvenSporadicStandard.Fin76b
open scoped commutatorElement

section Model

variable {α k : ℕ}

structure ESModel (α k : ℕ) : Prop where
  cardE : Nat.card (tsub (wgens α k eWords)) = 128
  cardS : Nat.card (tsub (wgens α k sWords)) = 1024
  ELe : tsub (wgens α k eWords) ≤ NG α k
  SLe : tsub (wgens α k sWords) ≤ NG α k
  ES : tsub (wgens α k eWords) ≤ tsub (wgens α k sWords)
  SN : ∀ s ∈ tsub (wgens α k sWords), ∀ x ∈ tsub (wgens α k eWords),
    s * x * s⁻¹ ∈ tsub (wgens α k eWords)
  EN : ∀ n ∈ NG α k, ∀ x ∈ tsub (wgens α k eWords), n * x * n⁻¹ ∈ tsub (wgens α k eWords)
  cE : wp α k (swN cWord) ∈ tsub (wgens α k eWords)
  sq : ∀ x ∈ tsub (wgens α k eWords), x * x = 1 ∨ x * x = wp α k (swN cWord)
  comm : ∀ x ∈ tsub (wgens α k eWords), ∀ y ∈ tsub (wgens α k eWords),
    ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = wp α k (swN cWord)
  uniq : ∀ D : Subgroup (Equiv.Perm (Fin 16)), D ≤ tsub (wgens α k sWords) → Nat.card D = 128 →
    (∀ x ∈ D, x * x = 1 ∨ x * x = wp α k (swN cWord)) →
    (∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = wp α k (swN cWord)) →
    D = tsub (wgens α k eWords)
  cSZ : ∀ s ∈ tsub (wgens α k sWords), s * wp α k (swN cWord) = wp α k (swN cWord) * s
  ZS : ∀ z ∈ tsub (wgens α k sWords), (∀ s ∈ tsub (wgens α k sWords), z * s = s * z) →
    z = 1 ∨ z = wp α k (swN cWord)
  ZE : ∀ z ∈ tsub (wgens α k eWords), (∀ s ∈ tsub (wgens α k eWords), z * s = s * z) →
    z = 1 ∨ z = wp α k (swN cWord)

theorem esModel (D : FusionData α k) (hue : ueCheck α k = true) (hes : esCheck α k = true) :
    ESModel α k := by
  have hc : Rep 16 (nwT α k cWord) (wp α k (swN cWord)) := rep_nwT D cWord
  have hue' := hue
  unfold ueCheck ueCheckG at hue'
  simp only [Bool.and_eq_true] at hue'
  obtain ⟨⟨h1, h2⟩, h3⟩ := hue'
  obtain ⟨hEs, -⟩ := tsub_spec h1
  obtain ⟨hSs, -⟩ := tsub_spec h2
  obtain ⟨hE, hS, hES, hSN, hcE, hsq, hcomm, huniq⟩ := ueCheckG_spec hc hue
  have hgN : ∀ T ∈ nGens α k, permOK 16 T = true := (nEnum_spec D.hnC).perm
  obtain ⟨hcS, hZS, hZE, hEN⟩ := esEnumCheck_spec hEs hSs hc hgN hes
  refine ⟨hE, hS, ?_, ?_, hES, hSN, ?_, hcE, hsq, hcomm, huniq, hcS, hZS, hZE⟩
  · exact tsub_wgens_le D hEs.perm
  · exact tsub_wgens_le D hSs.perm
  · rw [closure_nGens_eq D.hsz] at hEN
    exact hEN

end Model

section Image

variable {G : Type} [Group G] {e : G}
variable {e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12}


set_option linter.unusedSectionVars false

variable {d : G} {α k : ℕ}

theorem val_c : val e₀ d α (swN cWord) = cG e₀ := by
  have h : swN cWord = [((0 : Fin 9), true)] ++ [((0 : Fin 9), true)] := by decide
  rw [h, val, lift_mk_append, lift_mk_single, gen5_a1]
  exact (sAct_facts e₀).2.2.2.2.2.2.2

theorem ψ_c (E : NEmb e₀ d α k) : ψ E (wp α k (swN cWord)) = cG e₀ := by
  rw [ψ_wp, val_c]

noncomputable abbrev EG (E : NEmb e₀ d α k) : Subgroup G :=
  img E (tsub (wgens α k eWords))

noncomputable abbrev SG (E : NEmb e₀ d α k) : Subgroup G :=
  img E (tsub (wgens α k sWords))

structure ESFacts (E : NEmb e₀ d α k) : Prop where
  cardE : Nat.card (EG E) = 128
  cardS : Nat.card (SG E) = 1024
  EleN : EG E ≤ Nn e₀
  SleN : SG E ≤ Nn e₀
  ES : EG E ≤ SG E
  SN : ∀ s ∈ SG E, ∀ x ∈ EG E, s * x * s⁻¹ ∈ EG E
  EN : ∀ n ∈ Nn e₀, ∀ x ∈ EG E, n * x * n⁻¹ ∈ EG E
  cE : cG e₀ ∈ EG E
  sq : ∀ x ∈ EG E, x * x = 1 ∨ x * x = cG e₀
  comm : ∀ x ∈ EG E, ∀ y ∈ EG E, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = cG e₀
  uniq : ∀ D : Subgroup G, D ≤ SG E → Nat.card D = 128 → (∀ x ∈ D, x * x = 1 ∨ x * x = cG e₀) →
    (∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = cG e₀) → D = EG E
  cSZ : ∀ s ∈ SG E, s * cG e₀ = cG e₀ * s
  ZS : ∀ z ∈ SG E, (∀ s ∈ SG E, z * s = s * z) → z = 1 ∨ z = cG e₀
  ZE : ∀ z ∈ EG E, (∀ s ∈ EG E, z * s = s * z) → z = 1 ∨ z = cG e₀

theorem img_sq_comm (E : NEmb e₀ d α k) {K : Subgroup (Equiv.Perm (Fin 16))} (hK : K ≤ NG α k)
    (hsq : ∀ x ∈ K, x * x = 1 ∨ x * x = wp α k (swN cWord))
    (hcomm : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = wp α k (swN cWord)) :
    (∀ x ∈ img E K, x * x = 1 ∨ x * x = cG e₀) ∧
      ∀ x ∈ img E K, ∀ y ∈ img E K, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = cG e₀ := by
  have hc := wp_mem α k (swN cWord)
  constructor
  · rw [forall_mem_img' E]
    intro g hg hgK
    rw [← ψ_mul E hg hg]
    rcases hsq g hgK with h | h
    · left; rw [h, ψ_one]
    · right; rw [h, ψ_c]
  · rw [forall_mem_img' E]
    intro g hg hgK
    rw [forall_mem_img' E]
    intro h hh hhK
    rw [← ψ_comm E hg hh]
    rcases hcomm g hgK h hhK with h' | h'
    · left; rw [h', ψ_one]
    · right; rw [h', ψ_c]

theorem esFacts (D : FusionData α k) (E : NEmb e₀ d α k) (hue : ueCheck α k = true)
    (hes : esCheck α k = true) : ESFacts E := by
  obtain ⟨hcE', hcS', hELe, hSLe, hES, hSN, hEN, hcE, hsq, hcomm, huniq, hcSZ, hZS, hZE⟩ :=
    esModel D hue hes
  have hcm := wp_mem α k (swN cWord)
  have hcard : ∀ {K : Subgroup (Equiv.Perm (Fin 16))}, K ≤ NG α k →
      Nat.card (img E K) = Nat.card K := fun hK => card_img E hK
  refine ⟨(hcard hELe).trans hcE', (hcard hSLe).trans hcS', img_le_Nn E _, img_le_Nn E _,
    img_mono E hES, ?_, ?_, ?_, (img_sq_comm E hELe hsq hcomm).1,
    (img_sq_comm E hELe hsq hcomm).2, ?_, ?_, ?_, ?_⟩
  ·
    rw [forall_mem_img' E]
    intro s hs hsK
    rw [forall_mem_img' E]
    intro x hx hxK
    rw [← ψ_conj E hs hx]
    exact ψ_mem_img E ((NG α k).mul_mem ((NG α k).mul_mem hs hx) ((NG α k).inv_mem hs))
      (hSN s hsK x hxK)
  ·
    intro n hn
    obtain ⟨m, hm, rfl⟩ := exists_ψ E hn
    rw [forall_mem_img' E]
    intro x hx hxK
    rw [← ψ_conj E hm hx]
    exact ψ_mem_img E ((NG α k).mul_mem ((NG α k).mul_mem hm hx) ((NG α k).inv_mem hm))
      (hEN m hm x hxK)
  · rw [← ψ_c E]
    exact ψ_mem_img E hcm hcE
  ·
    intro D' hDS hDcard hDsq hDcomm
    have hDN : D' ≤ Nn e₀ := hDS.trans (img_le_Nn E _)
    have hle : pull E D' ≤ tsub (wgens α k sWords) := pull_le_of_le_img E hDS
    have hcP : Nat.card (pull E D') = 128 := (card_pull E hDN).trans hDcard
    have hP := huniq (pull E D') hle hcP ?_ ?_
    · rw [← img_pull E hDN, hP]
    · intro x hx
      obtain ⟨hxN, hxD⟩ := (mem_pull E).1 hx
      rw [← ψ_of_mem E hxN] at hxD
      have h1 := hDsq _ hxD
      rw [← ψ_mul E hxN hxN, ← ψ_c E] at h1
      rcases h1 with h1 | h1
      · left; exact ψ_inj E ((NG α k).mul_mem hxN hxN) ((NG α k).one_mem) (h1.trans (ψ_one E).symm)
      · right; exact ψ_inj E ((NG α k).mul_mem hxN hxN) hcm h1
    · intro x hx y hy
      obtain ⟨hxN, hxD⟩ := (mem_pull E).1 hx
      obtain ⟨hyN, hyD⟩ := (mem_pull E).1 hy
      rw [← ψ_of_mem E hxN] at hxD
      rw [← ψ_of_mem E hyN] at hyD
      have h1 := hDcomm _ hxD _ hyD
      have hxy : ⁅x, y⁆ ∈ NG α k := by
        simp only [commutatorElement_def]
        exact (NG α k).mul_mem ((NG α k).mul_mem ((NG α k).mul_mem hxN hyN) ((NG α k).inv_mem hxN))
          ((NG α k).inv_mem hyN)
      rw [← ψ_comm E hxN hyN, ← ψ_c E] at h1
      rcases h1 with h1 | h1
      · left; exact ψ_inj E hxy ((NG α k).one_mem) (h1.trans (ψ_one E).symm)
      · right; exact ψ_inj E hxy hcm h1
  ·
    rw [forall_mem_img' E]
    intro s hs hsK
    rw [← ψ_c E, ← ψ_mul E hs hcm, ← ψ_mul E hcm hs, hcSZ s hsK]
  ·
    intro z hz hzs
    obtain ⟨g, hg, hgK, rfl⟩ := (mem_img' E).1 hz
    have hgz : ∀ s ∈ tsub (wgens α k sWords), g * s = s * g := by
      intro s hs
      have hsN := hSLe hs
      have := hzs (ψ E s) (ψ_mem_img E hsN hs)
      rw [← ψ_mul E hg hsN, ← ψ_mul E hsN hg] at this
      exact ψ_inj E ((NG α k).mul_mem hg hsN) ((NG α k).mul_mem hsN hg) this
    rcases hZS g hgK hgz with h | h
    · left; rw [h, ψ_one]
    · right; rw [h, ψ_c]
  ·
    intro z hz hzs
    obtain ⟨g, hg, hgK, rfl⟩ := (mem_img' E).1 hz
    have hgz : ∀ s ∈ tsub (wgens α k eWords), g * s = s * g := by
      intro s hs
      have hsN := hELe hs
      have := hzs (ψ E s) (ψ_mem_img E hsN hs)
      rw [← ψ_mul E hg hsN, ← ψ_mul E hsN hg] at this
      exact ψ_inj E ((NG α k).mul_mem hg hsN) ((NG α k).mul_mem hsN hg) this
    rcases hZE g hgK hgz with h | h
    · left; rw [h, ψ_one]
    · right; rw [h, ψ_c]

end Image

end CFSG.EvenSporadicStandard.M12Std.Yosh
