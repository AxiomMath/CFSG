module

public import Mathlib.GroupTheory.Sylow
import CFSG.GroupTheory.OmegaCentral.Fusion
import CFSG.GroupTheory.OmegaCentral.Normalizer
import CFSG.Mathlib.GroupTheory.InvertedCommute

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped commutatorElement

variable {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]

private lemma ocCycAux_exists_lt_of_le {S : Subgroup K} (hS : IsPGroup p ↥S)
    {N : Subgroup K} (hNS : N ≤ S) (hne : N ≠ S) :
    ∃ M : Subgroup K, N ≤ M ∧ M < S ∧ ∀ a ∈ S, ∀ b ∈ S, ⁅a, b⁆ ∈ M := by
  let K' : Subgroup ↥S := N.subgroupOf S
  have hK'ne : K' ≠ ⊤ := by
    intro htop
    exact hne (le_antisymm hNS (Subgroup.subgroupOf_eq_top.mp htop))
  obtain ⟨M', hK'M', hM'lt, -, hcomm⟩ :=
    exists_lt_pow_mem_commutator_mem hS (H := ⊤) (K := K') le_top hK'ne
  refine ⟨M'.map S.subtype, ?_, ?_, ?_⟩
  · intro n hn
    exact Subgroup.mem_map.mpr ⟨⟨n, hNS hn⟩, hK'M' (Subgroup.mem_subgroupOf.mpr hn), rfl⟩
  · have htop : (⊤ : Subgroup ↥S).map S.subtype = S := by
      rw [← Subgroup.subgroupOf_self (H := S), Subgroup.map_subgroupOf_eq_of_le le_rfl]
    refine lt_of_le_of_ne (Subgroup.map_subtype_le M') ?_
    intro hM'S
    have hmap : M'.map S.subtype = (⊤ : Subgroup ↥S).map S.subtype := by rw [hM'S, htop]
    exact hM'lt.ne (Subgroup.map_subtype_inj.mp hmap)
  · intro a ha b hb
    exact Subgroup.mem_map.mpr
      ⟨⁅(⟨a, ha⟩ : ↥S), ⟨b, hb⟩⁆, hcomm ⟨a, ha⟩ trivial ⟨b, hb⟩ trivial, by simp⟩

omit [Finite K] in
private lemma ocCycAux_conj_of_centralizes {S : Subgroup K} {z : K}
    (hz : z ∈ centralizer (S : Set K)) {y : K} (hy : y ∈ S) : z⁻¹ * y * z = y := by
  have hzy : y * z = z * y := by
    rw [Subgroup.mem_centralizer_iff] at hz
    exact hz y hy
  calc z⁻¹ * y * z = z⁻¹ * (y * z) := by group
    _ = z⁻¹ * (z * y) := by rw [hzy]
    _ = y := by group

omit [Finite K] in
private lemma ocCycAux_gen_eq_commutator {S : Subgroup K} {c s z x : K}
    (hs : s ∈ S) (hz : z ∈ centralizer (S : Set K))
    (hc : c = s * z) (hx : x ∈ S) :
    x⁻¹ * (c⁻¹ * x * c) = ⁅x⁻¹, s⁻¹⁆ := by
  have hy : s⁻¹ * x * s ∈ S := S.mul_mem (S.mul_mem (S.inv_mem hs) hx) hs
  have hcc : c⁻¹ * x * c = s⁻¹ * x * s := by
    rw [hc]
    calc (s * z)⁻¹ * x * (s * z) = z⁻¹ * (s⁻¹ * x * s) * z := by group
      _ = s⁻¹ * x * s := ocCycAux_conj_of_centralizes hz hy
  rw [hcc, commutatorElement_def]
  group

private lemma ocCycAux_fix_gen (hp2 : p ≠ 2) (S : Sylow p K) {c x : K}
    (hc : c ∈ normalizer ((S : Subgroup K) : Set K))
    (hfix : ∀ w ∈ (S : Subgroup K), w ^ p = 1 → c * w * c⁻¹ = w)
    (hx : x ∈ (S : Subgroup K)) :
    ∃ s ∈ (S : Subgroup K), x⁻¹ * (c⁻¹ * x * c) = ⁅x⁻¹, s⁻¹⁆ := by
  obtain ⟨s, hs, z, hz, hc_eq⟩ := mem_sylow_mul_centralizer_of_fix_omega hp2 S hc hfix
  exact ⟨s, hs, ocCycAux_gen_eq_commutator hs hz hc_eq hx⟩

private lemma ocCycAux_mul_inv_fix (hp2 : p ≠ 2) (S : Sylow p K) {c n : K}
    (hc : c ∈ normalizer ((S : Subgroup K) : Set K))
    (hn : n ∈ normalizer ((S : Subgroup K) : Set K))
    (hact : ∀ w ∈ (S : Subgroup K), w ^ p = 1 → c * w * c⁻¹ = n * w * n⁻¹) :
    ∃ s ∈ (S : Subgroup K), ∃ z ∈ centralizer ((S : Subgroup K) : Set K),
      c * n⁻¹ = s * z := by
  refine mem_sylow_mul_centralizer_of_fix_omega hp2 S ?_ ?_
  · exact (normalizer ((S : Subgroup K) : Set K)).mul_mem hc
      ((normalizer ((S : Subgroup K) : Set K)).inv_mem hn)
  · intro w hw hwp
    have hw' : c⁻¹ * w * c ∈ (S : Subgroup K) := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((normalizer ((S : Subgroup K) : Set K)).inv_mem hc)) w
      simpa using this.mp hw
    have hwp' : (c⁻¹ * w * c) ^ p = 1 := by
      have hconj : c⁻¹ * w * c = MulAut.conj c⁻¹ w := by
        rw [MulAut.conj_apply]; group
      rw [hconj, ← map_pow, hwp, map_one]
    have h := hact (c⁻¹ * w * c) hw' hwp'
    have hw_eq : w = n * (c⁻¹ * w * c) * n⁻¹ := by
      rw [← h]; group
    have hnw : n⁻¹ * w * n = c⁻¹ * w * c := by
      calc n⁻¹ * w * n = n⁻¹ * (n * (c⁻¹ * w * c) * n⁻¹) * n :=
            congrArg (fun t => n⁻¹ * t * n) hw_eq
        _ = c⁻¹ * w * c := by group
    calc (c * n⁻¹) * w * (c * n⁻¹)⁻¹ = c * (n⁻¹ * w * n) * c⁻¹ := by group
      _ = c * (c⁻¹ * w * c) * c⁻¹ := by rw [hnw]
      _ = w := by group

private lemma ocCycAux_eq_mul_inv_of_act (hp2 : p ≠ 2) (S : Sylow p K) {c n : K}
    (hc : c ∈ normalizer ((S : Subgroup K) : Set K))
    (hn : n ∈ normalizer ((S : Subgroup K) : Set K))
    (hact : ∀ w ∈ (S : Subgroup K), w ^ p = 1 → c * w * c⁻¹ = n * w * n⁻¹) :
    ∃ s ∈ (S : Subgroup K), ∃ z ∈ centralizer ((S : Subgroup K) : Set K),
      c = s * z * n := by
  obtain ⟨s, hs, z, hz, hd⟩ := ocCycAux_mul_inv_fix hp2 S hc hn hact
  refine ⟨s, hs, z, hz, ?_⟩
  calc c = (c * n⁻¹) * n := by group
    _ = (s * z) * n := by rw [hd]

omit [Finite K] in
private lemma ocCycAux_inv_conj_eq {S : Subgroup K} {n y : K} (hy : y ∈ S)
    (hninv : ∀ y ∈ S, n * (n * y * n⁻¹) * n⁻¹ = y) :
    n⁻¹ * y * n = n * y * n⁻¹ := by
  have h := hninv y hy
  calc n⁻¹ * y * n = n⁻¹ * (n * (n * y * n⁻¹) * n⁻¹) * n := by rw [h]
    _ = n * y * n⁻¹ := by group

omit [Finite K] in
private lemma ocCycAux_act_gen_eq {S : Subgroup K} (n s z c x : K)
    (hs : s ∈ S) (hz : z ∈ centralizer (S : Set K)) (hc : c = s * z * n)
    (hninv : ∀ y ∈ S, n * (n * y * n⁻¹) * n⁻¹ = y)
    (hx : x ∈ S) :
    x⁻¹ * (c⁻¹ * x * c) =
      (x⁻¹ * (n * x * n⁻¹)) * (n * (x⁻¹ * s⁻¹ * x * s) * n⁻¹) := by
  have hy : s⁻¹ * x * s ∈ S := S.mul_mem (S.mul_mem (S.inv_mem hs) hx) hs
  have hcc : c⁻¹ * x * c = n * (s⁻¹ * x * s) * n⁻¹ := by
    rw [hc]
    calc (s * z * n)⁻¹ * x * (s * z * n)
        = n⁻¹ * (z⁻¹ * (s⁻¹ * x * s) * z) * n := by group
      _ = n⁻¹ * (s⁻¹ * x * s) * n := by rw [ocCycAux_conj_of_centralizes hz hy]
      _ = n * (s⁻¹ * x * s) * n⁻¹ := ocCycAux_inv_conj_eq hy hninv
  rw [hcc]
  group

private lemma ocCycAux_closure_eq_of_gens (hp2 : p ≠ 2) (S : Sylow p K)
    (hcen : ∀ w ∈ (S : Subgroup K), w ^ p = 1 → ∀ s ∈ (S : Subgroup K), s * w = w * s)
    (hperf : commutator K = ⊤) (Nt : Subgroup K) (hNtS : Nt ≤ (S : Subgroup K))
    (hgens : {z : K | ∃ x ∈ (S : Subgroup K), ∃ c ∈ normalizer ((S : Subgroup K) : Set K),
        z = x⁻¹ * (c⁻¹ * x * c)} ⊆
        (Nt ⊔ ⁅(S : Subgroup K), (S : Subgroup K)⁆ : Subgroup K)) :
    Nt = (S : Subgroup K) := by
  by_cases hne : Nt = (S : Subgroup K)
  · exact hne
  · obtain ⟨M, hNtM, hMlt, hcomm⟩ :=
      ocCycAux_exists_lt_of_le S.isPGroup' hNtS hne
    have hcommLe : ⁅(S : Subgroup K), (S : Subgroup K)⁆ ≤ M :=
      Subgroup.commutator_le.mpr hcomm
    have hLM : Nt ⊔ ⁅(S : Subgroup K), (S : Subgroup K)⁆ ≤ M := sup_le hNtM hcommLe
    have hSle : (S : Subgroup K) ≤ M := by
      rw [sylow_eq_closure_of_omega_central hp2 S hcen hperf]
      exact ((Subgroup.closure_le _).mpr hgens).trans hLM
    exact absurd hSle hMlt.2

theorem isCyclic_sylow_of_omega_central (hp2 : p ≠ 2) (S : Sylow p K)
    (hperf : commutator K = ⊤)
    (hcen : ∀ w ∈ (S : Subgroup K), w ^ p = 1 → ∀ s ∈ (S : Subgroup K), s * w = w * s)
    (hact : ∀ c₁ ∈ normalizer ((S : Subgroup K) : Set K),
      ∀ c₂ ∈ normalizer ((S : Subgroup K) : Set K),
      (∀ w ∈ (S : Subgroup K), w ^ p = 1 → c₁ * w * c₁⁻¹ = w) ∨
      (∀ w ∈ (S : Subgroup K), w ^ p = 1 → c₂ * w * c₂⁻¹ = w) ∨
      ∀ w ∈ (S : Subgroup K), w ^ p = 1 → c₁ * w * c₁⁻¹ = c₂ * w * c₂⁻¹)
    (U : Subgroup K) (hU : Nat.card U ≤ p)
    (hUinv : ∀ c ∈ normalizer ((S : Subgroup K) : Set K), ∀ w ∈ (S : Subgroup K), w ^ p = 1 →
      c * w * c⁻¹ = w⁻¹ → w ∈ U) :
    IsCyclic (S : Subgroup K) := by
  by_cases hfixall : ∀ c ∈ normalizer ((S : Subgroup K) : Set K),
      ∀ w ∈ (S : Subgroup K), w ^ p = 1 → c * w * c⁻¹ = w
  · have hgens : {z : K | ∃ x ∈ (S : Subgroup K), ∃ c ∈ normalizer ((S : Subgroup K) : Set K),
        z = x⁻¹ * (c⁻¹ * x * c)} ⊆
        ((⊥ : Subgroup K) ⊔ ⁅(S : Subgroup K), (S : Subgroup K)⁆ : Subgroup K) := by
      rintro z ⟨x, hx, c, hc, rfl⟩
      obtain ⟨s, hs, hgen⟩ := ocCycAux_fix_gen hp2 S hc (hfixall c hc) hx
      rw [hgen]
      exact Subgroup.mem_sup_right
        (Subgroup.commutator_mem_commutator (S.inv_mem hx) (S.inv_mem hs))
    have hbot : (⊥ : Subgroup K) = (S : Subgroup K) :=
      ocCycAux_closure_eq_of_gens hp2 S hcen hperf ⊥ bot_le hgens
    have hSbot : (S : Subgroup K) = ⊥ := hbot.symm
    have hsub : Subsingleton ↥(S : Subgroup K) := by rw [hSbot]; infer_instance
    exact @isCyclic_of_subsingleton ↥(S : Subgroup K) _ hsub
  · push Not at hfixall
    obtain ⟨c₀, hc₀, w₀, hw₀, hw₀p, hc₀ne⟩ := hfixall
    have hnc : ¬ ∀ w ∈ (S : Subgroup K), w ^ p = 1 → c₀ * w * c₀⁻¹ = w := by
      intro h
      exact hc₀ne (h w₀ hw₀ hw₀p)
    obtain ⟨n, hn, hnacts, hninv⟩ := exists_normalizer_involution_of_omega hp2 S hact hc₀ hnc
    have hn_notfix : ¬ ∀ w ∈ (S : Subgroup K), w ^ p = 1 → n * w * n⁻¹ = w := by
      intro h
      exact hnc (fun w hw hwp => by rw [← hnacts w hw hwp]; exact h w hw hwp)
    let t : MulAut ↥(S : Subgroup K) := (S : Subgroup K).normalizerMonoidHom ⟨n, hn⟩
    have ht : ∀ y : ↥(S : Subgroup K), (t y : K) = n * y * n⁻¹ := fun y =>
      Subgroup.normalizerMonoidHom_apply_apply_coe ((S : Subgroup K)) ⟨n, hn⟩ y
    have ht2 : ∀ y : ↥(S : Subgroup K), t (t y) = y := by
      intro y
      apply Subtype.ext
      rw [ht (t y), ht y]
      exact hninv (y : K) y.2
    let Nt : Subgroup K := (Subgroup.closure
      {g : ↥(S : Subgroup K) | ∃ y : ↥(S : Subgroup K), g = y⁻¹ * t y}).map
      (S : Subgroup K).subtype
    have hgens2 : {z : K | ∃ x ∈ (S : Subgroup K), ∃ c ∈ normalizer ((S : Subgroup K) : Set K),
        z = x⁻¹ * (c⁻¹ * x * c)} ⊆
        (Nt ⊔ ⁅(S : Subgroup K), (S : Subgroup K)⁆ : Subgroup K) := by
      rintro z ⟨x, hx, c, hc, rfl⟩
      rcases hact c hc n hn with hfixc | hfixn | hactcn
      · obtain ⟨s, hs, hgen⟩ := ocCycAux_fix_gen hp2 S hc hfixc hx
        rw [hgen]
        exact Subgroup.mem_sup_right
          (Subgroup.commutator_mem_commutator (S.inv_mem hx) (S.inv_mem hs))
      · exact absurd hfixn hn_notfix
      · obtain ⟨s, hs, z, hz, hc_eq⟩ := ocCycAux_eq_mul_inv_of_act hp2 S hc hn hactcn
        rw [ocCycAux_act_gen_eq n s z c x hs hz hc_eq hninv hx]
        refine (Nt ⊔ ⁅(S : Subgroup K), (S : Subgroup K)⁆).mul_mem ?_ ?_
        · have hmem : (⟨x, hx⟩⁻¹ * t ⟨x, hx⟩ : ↥(S : Subgroup K)) ∈
              Subgroup.closure {g : ↥(S : Subgroup K) | ∃ y, g = y⁻¹ * t y} :=
            Subgroup.subset_closure ⟨⟨x, hx⟩, rfl⟩
          have hmap : ((⟨x, hx⟩⁻¹ * t ⟨x, hx⟩ : ↥(S : Subgroup K)) : K) ∈ Nt :=
            Subgroup.mem_map.mpr ⟨⟨x, hx⟩⁻¹ * t ⟨x, hx⟩, hmem, rfl⟩
          have hcoe : ((⟨x, hx⟩⁻¹ * t ⟨x, hx⟩ : ↥(S : Subgroup K)) : K) =
              x⁻¹ * (n * x * n⁻¹) := by
            simp [ht]
          rw [← hcoe]
          exact Subgroup.mem_sup_left hmap
        · have hnx : n * x⁻¹ * n⁻¹ ∈ (S : Subgroup K) :=
            ((Subgroup.mem_normalizer_iff.mp hn) x⁻¹).mp (S.inv_mem hx)
          have hns : n * s⁻¹ * n⁻¹ ∈ (S : Subgroup K) :=
            ((Subgroup.mem_normalizer_iff.mp hn) s⁻¹).mp (S.inv_mem hs)
          have hcomm : n * (x⁻¹ * s⁻¹ * x * s) * n⁻¹ =
              ⁅n * x⁻¹ * n⁻¹, n * s⁻¹ * n⁻¹⁆ := by
            rw [commutatorElement_def]
            group
          rw [hcomm]
          exact Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hnx hns)
    have hNtS : Nt ≤ (S : Subgroup K) := Subgroup.map_subtype_le _
    have hNt : Nt = (S : Subgroup K) :=
      ocCycAux_closure_eq_of_gens hp2 S hcen hperf Nt hNtS hgens2
    have hU' : Nat.card (U.comap (S : Subgroup K).subtype) ≤ p := by
      let f : ↥(U.comap (S : Subgroup K).subtype) → ↥U := fun x =>
        ⟨(x : K), by
          have hx := x.2
          rw [Subgroup.mem_comap] at hx
          simpa using hx⟩
      have hfinj : Function.Injective f := by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : ↥U => (z : K)) hxy
      exact le_trans (Nat.card_le_card_of_injective f hfinj) hU
    have hcen' : ∀ g : ↥(S : Subgroup K), g ^ p = 1 →
        g ∈ Subgroup.center ↥(S : Subgroup K) := by
      intro g hg
      rw [Subgroup.mem_center_iff]
      intro h
      have hgK : (g : K) ^ p = 1 := by
        simpa using congrArg (fun z : ↥(S : Subgroup K) => (z : K)) hg
      exact Subtype.ext (hcen (g : K) g.2 hgK (h : K) h.2)
    have hUinv' : ∀ g : ↥(S : Subgroup K), g ^ p = 1 → t g = g⁻¹ →
        g ∈ U.comap (S : Subgroup K).subtype := by
      intro g hg hgt
      rw [Subgroup.mem_comap]
      have hgK : (g : K) ^ p = 1 := by
        simpa using congrArg (fun z : ↥(S : Subgroup K) => (z : K)) hg
      apply hUinv n hn (g : K) g.2 hgK
      have h := congrArg (fun z : ↥(S : Subgroup K) => (z : K)) hgt
      rwa [ht g] at h
    have hcyc : IsCyclic (Subgroup.closure {g : ↥(S : Subgroup K) | t g = g⁻¹}) :=
      isCyclic_closure_inv hp2 S.isPGroup' t ht2 hcen'
        (U.comap (S : Subgroup K).subtype) hU' hUinv'
    have hgenle : Subgroup.closure {g : ↥(S : Subgroup K) | ∃ y : ↥(S : Subgroup K),
        g = y⁻¹ * t y} ≤ Subgroup.closure {g : ↥(S : Subgroup K) | t g = g⁻¹} := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro g ⟨y, rfl⟩
      refine Subgroup.subset_closure ?_
      change t (y⁻¹ * t y) = (y⁻¹ * t y)⁻¹
      have h : t (y⁻¹ * t y) = (t y)⁻¹ * y := by
        rw [map_mul, map_inv, ht2 y]
      simp [h, mul_inv_rev]
    have hmapGen : (Subgroup.closure {g : ↥(S : Subgroup K) | ∃ y : ↥(S : Subgroup K),
        g = y⁻¹ * t y}).map (S : Subgroup K).subtype = (S : Subgroup K) := hNt
    have htop : (⊤ : Subgroup ↥(S : Subgroup K)).map (S : Subgroup K).subtype =
        (S : Subgroup K) := by
      rw [← Subgroup.subgroupOf_self (H := (S : Subgroup K)),
        Subgroup.map_subgroupOf_eq_of_le le_rfl]
    have hA : Subgroup.closure {g : ↥(S : Subgroup K) | t g = g⁻¹} = ⊤ := by
      refine Subgroup.map_subtype_inj.mp ?_
      calc (Subgroup.closure {g : ↥(S : Subgroup K) | t g = g⁻¹}).map
            (S : Subgroup K).subtype
          = (S : Subgroup K) := le_antisymm (Subgroup.map_subtype_le _)
            ((le_of_eq hmapGen.symm).trans (Subgroup.map_mono hgenle))
        _ = (⊤ : Subgroup ↥(S : Subgroup K)).map (S : Subgroup K).subtype := htop.symm
    have hcycTop : IsCyclic (⊤ : Subgroup ↥(S : Subgroup K)) := hA ▸ hcyc
    exact isCyclic_of_surjective
      (Subgroup.topEquiv (G := ↥(S : Subgroup K)) :
        ↥(⊤ : Subgroup ↥(S : Subgroup K)) →* ↥(S : Subgroup K))
      (MulEquiv.surjective _)

end CFSG.GroupTheory

end
