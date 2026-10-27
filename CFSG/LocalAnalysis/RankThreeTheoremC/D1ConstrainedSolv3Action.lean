module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.ResidualToolsAux
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic
import CFSG.SignalizerFunctorTheorem.Inheritance.CosetFixed

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem le_of_barM_centralizes {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M L N : Subgroup G}
    {z : G} (hLM : L ≤ M) (hzM : z ∈ M) (hzp : z ^ p = 1) (hQN : pCoreOf 2 M ≤ N)
    (hCN : Subgroup.centralizer ({z} : Set G) ≤ N)
    (hcent : ∀ y ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ * y =
      y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩) : L ≤ N := by
  intro ℓ hℓ
  set a : ↥M := ⟨z, hzM⟩ with ha
  set w : ↥M := ⟨ℓ, hLM hℓ⟩ with hw
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime p (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hwbar : QuotientGroup.mk' (CFSG.pCore 2 ↥M) w ∈ barM M L :=
    ⟨w, Subgroup.mem_subgroupOf.mpr hℓ, rfl⟩
  have hcomm : a * w * a⁻¹ * w⁻¹ ∈ CFSG.pCore 2 ↥M := by
    rw [← QuotientGroup.eq_one_iff]
    have h := hcent _ hwbar
    change QuotientGroup.mk' (CFSG.pCore 2 ↥M) (a * w * a⁻¹ * w⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [h]
    group
  have hap : a ^ p = 1 := Subtype.ext hzp
  obtain ⟨x, hx1, hx2⟩ := CFSG.SignalizerFunctorTheorem.exists_fixed_of_coprime hp
    hap (CFSG.pCore 2 ↥M) hcop hcomm
  have hxC : (x : G) ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (Subtype.val : ↥M → G) hx2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hxw : ((x * w⁻¹ : ↥M) : G) ∈ pCoreOf 2 M :=
    coe_mem_pCoreOf_two_of_mk_eq_one _ ((QuotientGroup.eq_one_iff _).mpr hx1)
  have hℓx : ℓ = ((x * w⁻¹ : ↥M) : G)⁻¹ * (x : G) := by
    simp [hw]
  rw [hℓx]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hQN hxw)) (hCN hxC)

omit [Finite G] in
theorem mk_mem_normalizer_barM {M L : Subgroup G} {x : G} (hxM : x ∈ M)
    (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈
      Subgroup.normalizer ((barM M L : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h1 := barM_map_conj hxM L
  have h2 : L.map (MulAut.conj x).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  rw [h2] at h1
  exact h1.symm

omit [Finite G] in
theorem exists_action_barM {M L P : Subgroup G} (hPM : P ≤ M)
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) :
    ∃ φ : ↥P →* MulAut ↥(barM M L), ∀ x : ↥P, φ x = 1 ↔
      ∀ y ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hPM x.2⟩ * y =
        y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hPM x.2⟩ := by
  let f : ↥P →* ↥M ⧸ CFSG.pCore 2 ↥M :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hPM)
  have hf : ∀ x : ↥P, f x ∈
      Subgroup.normalizer ((barM M L : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _) := fun x =>
    mk_mem_normalizer_barM (hPM x.2) (hPL x.2)
  refine ⟨(barM M L).normalizerMonoidHom.comp (f.codRestrict _ hf), fun x => ?_⟩
  rw [MonoidHom.comp_apply, ← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker,
    Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  exact forall₂_congr fun y _ => eq_comm

theorem mem_of_normal_ne_bot {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hP : IsPGroup p P) {z : G}
    (hzP : z ∈ P) (hz : orderOf z = p)
    (huniq : ∀ y ∈ Subgroup.centralizer (P : Set G), y ∈ P → orderOf y = p →
      y ∈ Subgroup.zpowers z) {K : Subgroup ↥P} [K.Normal] (hK : K ≠ ⊥) :
    (⟨z, hzP⟩ : ↥P) ∈ K := by
  classical
  have hnil : Group.IsNilpotent ↥P := hP.isNilpotent
  have hCne : K ⊓ Subgroup.center ↥P ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hK
  have hCp : IsPGroup p ↥(K ⊓ Subgroup.center ↥P) := hP.to_subgroup _
  have hC : p ∣ Nat.card ↥(K ⊓ Subgroup.center ↥P) := by
    rcases hCp.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hCne
    · exact h
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hC
  set c' : ↥P := (c : ↥P) with hc'
  have hc'ord : orderOf c' = p := by rw [hc', Subgroup.orderOf_coe, hc]
  have hc'K : c' ∈ K := c.2.1
  have hc'Z : c' ∈ Subgroup.center ↥P := c.2.2
  have hcG : (c' : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg (Subtype.val : ↥P → G) (Subgroup.mem_center_iff.mp hc'Z ⟨g, hg⟩)
  have hcz : (c' : G) ∈ Subgroup.zpowers z :=
    huniq _ hcG c'.2 (by rw [Subgroup.orderOf_coe]; exact hc'ord)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcz
  set zP : ↥P := ⟨z, hzP⟩ with hzPdef
  have hzPord : orderOf zP = p := by rw [hzPdef, ← Subgroup.orderOf_coe]; exact hz
  have hc'zP : c' ∈ Subgroup.zpowers zP :=
    Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
  have hle : Subgroup.zpowers c' ≤ Subgroup.zpowers zP := (Subgroup.zpowers_le).mpr hc'zP
  have heq : Subgroup.zpowers c' = Subgroup.zpowers zP := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hc'ord, hzPord]
  have : zP ∈ Subgroup.zpowers c' := by rw [heq]; exact Subgroup.mem_zpowers zP
  exact (Subgroup.zpowers_le (H := K)).mpr hc'K this

theorem injective_action_barM {p : ℕ} [Fact p.Prime] {M L P : Subgroup G} (hP : IsPGroup p P)
    (hPM : P ≤ M) {z : G} (hzP : z ∈ P) (hz : orderOf z = p)
    (huniq : ∀ y ∈ Subgroup.centralizer (P : Set G), y ∈ P → orderOf y = p →
      y ∈ Subgroup.zpowers z) {φ : ↥P →* MulAut ↥(barM M L)}
    (hφ : ∀ x : ↥P, φ x = 1 ↔
      ∀ y ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hPM x.2⟩ * y =
        y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hPM x.2⟩)
    (hnot : ¬ ∀ y ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hPM hzP⟩ * y =
      y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hPM hzP⟩) :
    Function.Injective φ := by
  rw [injective_iff_map_eq_one]
  intro x hx
  by_contra hx1
  have hKne : φ.ker ≠ ⊥ := fun h => hx1 (by simpa [h] using (MonoidHom.mem_ker.mpr hx))
  exact hnot ((hφ ⟨z, hzP⟩).mp
    (MonoidHom.mem_ker.mp (mem_of_normal_ne_bot hP hzP hz huniq hKne)))

end CFSG.LocalAnalysis.RankThreeTheoremC
