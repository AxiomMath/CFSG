module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Weak
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma63
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Suzuki

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup
open scoped Pointwise

namespace OuterConfig

variable {G : Type} [Group G] {A : Subgroup G} {z t : G} {T : Subgroup G}
  (h : OuterConfig G A z t T)

include h in
@[expose] noncomputable def sylowH [Finite G] : Sylow 2 ↥(centralizer ({z} : Set G)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  { toSubgroup := T.subgroupOf (centralizer ({z} : Set G))
    isPGroup' := h.T_pgroup.comap_subtype
    is_maximal' := by
      intro Q hQ hTQ
      refine le_antisymm (fun q hq => ?_) hTQ
      have hQ' : IsPGroup 2 (Q.map (centralizer ({z} : Set G)).subtype) := hQ.map _
      have hle : Q.map (centralizer ({z} : Set G)).subtype ≤ centralizer ({z} : Set G) := by
        rintro _ ⟨x, -, rfl⟩
        exact x.2
      have hTle : T ≤ Q.map (centralizer ({z} : Set G)).subtype := fun x hx =>
        ⟨⟨x, h.T_le hx⟩, hTQ (mem_subgroupOf.2 hx), rfl⟩
      have := h.T_max _ hle hQ' hTle
      exact mem_subgroupOf.2 (this ⟨q, hq, rfl⟩) }

include h in
theorem exists_conj_into_T [Finite G] {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXH : X ≤ centralizer ({z} : Set G)) :
    ∃ k ∈ centralizer ({z} : Set G), ∀ x ∈ X, k⁻¹ * x * k ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXp : IsPGroup 2 (X.subgroupOf (centralizer ({z} : Set G))) := hX.comap_subtype
  obtain ⟨P, hP⟩ := hXp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (centralizer ({z} : Set G)) h.sylowH P
  refine ⟨k, k.2, fun x hx => ?_⟩
  have hxP : (⟨x, hXH hx⟩ : centralizer ({z} : Set G)) ∈
      (P : Subgroup (centralizer ({z} : Set G))) := hP (mem_subgroupOf.2 hx)
  rw [← hk, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxP
  obtain ⟨s, hs, hsx⟩ := hxP
  have hs' : (s : G) ∈ T := mem_subgroupOf.1 hs
  have e1 : (k : G)⁻¹ * x * (k : G) = s := by
    have hx' : (k : G) * s * (k : G)⁻¹ = x := by
      have := congrArg Subtype.val hsx
      simpa [MulAut.smul_def, MulAut.conj_apply] using this
    rw [← hx']
    group
  rw [e1]
  exact hs'

end OuterConfig

namespace OuterE

variable {G : Type} [Group G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  (h : OuterE G L z t T E)

include h in
theorem t_order : orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact h.cfg.t_sq) h.cfg.t_ne

include h in
theorem t_comm_E {e : G} (he : e ∈ E) : e * t = t * e := h.cfg.t_central e (h.E_le_T he)

include h in
theorem le_of_two_group [Finite G] (hzt : ∃ x : G, x * z * x⁻¹ = z * t) {R : Subgroup G}
    (hR : IsPGroup 2 R) (hRE : R ≤ centralizer (E : Set G))
    (hRz : R ≤ centralizer ({z} : Set G)) : R ≤ zpowers z ⊔ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 E := h.cfg.T_pgroup.to_le h.E_le_T
  have hREn : R ≤ normalizer (E : Set G) := hRE.trans (centralizer_le_normalizer E)
  have hRE2 : IsPGroup 2 (R ⊔ E : Subgroup G) := hR.to_sup_of_normal_right' hE2 hREn
  have hEH : E ≤ centralizer ({z} : Set G) := fun e he =>
    mem_centralizer_singleton_iff.2 (h.cfg.z_comm_of_mem_A (h.E_le_L he))
  obtain ⟨k, hkH, hk⟩ := h.cfg.exists_conj_into_T hRE2 (sup_le hRz hEH)
  have hkz : k * z * k⁻¹ = z := by
    have := mem_centralizer_singleton_iff.1 hkH
    calc k * z * k⁻¹ = z * k * k⁻¹ := by rw [this]
      _ = z := by group
  have hEk : E.map (MulAut.conj k⁻¹).toMonoidHom ≤ T := by
    rintro _ ⟨e, he, rfl⟩
    have := hk e (mem_sup_right he)
    simpa [MulAut.conj_apply] using this
  have heq := h.map_conj_eq_of_le hzt hEk
  have hkE : ∀ e ∈ E, k * e * k⁻¹ ∈ E := by
    intro e he
    have hmem : e ∈ E.map (MulAut.conj k⁻¹).toMonoidHom := by rw [heq]; exact he
    obtain ⟨e', he', hee'⟩ := hmem
    have : e' = k * e * k⁻¹ := by
      have h1 : k⁻¹ * e' * k = e := by simpa [MulAut.conj_apply] using hee'
      rw [← h1]; group
    rwa [← this]
  have hkt : k * t * k⁻¹ = t := by
    have hu : k * t * k⁻¹ ∈ E := hkE t h.econfig.t_mem
    have hc : ∀ f ∈ E, f * (k * t * k⁻¹) = (k * t * k⁻¹) * f := by
      intro f hf
      have hf' : k⁻¹ * f * k ∈ E := by
        have hmem : k⁻¹ * f * k ∈ E.map (MulAut.conj k⁻¹).toMonoidHom :=
          ⟨f, hf, by simp⟩
        rwa [heq] at hmem
      have h1 := h.t_comm_E hf'
      calc f * (k * t * k⁻¹) = k * ((k⁻¹ * f * k) * t) * k⁻¹ := by group
        _ = k * (t * (k⁻¹ * f * k)) * k⁻¹ := by rw [h1]
        _ = (k * t * k⁻¹) * f := by group
    rcases h.econfig.center _ hu hc with h1 | h1
    · exfalso
      apply h.cfg.t_ne
      calc t = k⁻¹ * (k * t * k⁻¹) * k := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  intro r hr
  have hr' : k⁻¹ * r * k ∈ T := hk r (mem_sup_left hr)
  have hcent : ∀ e ∈ E, (k⁻¹ * r * k) * e = e * (k⁻¹ * r * k) := by
    intro e he
    have he₁ := hkE e he
    have h1 : (k * e * k⁻¹) * r = r * (k * e * k⁻¹) := mem_centralizer_iff.1 (hRE hr) _ he₁
    calc (k⁻¹ * r * k) * e = k⁻¹ * (r * (k * e * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * e * k⁻¹) * r) * k := by rw [h1]
      _ = e * (k⁻¹ * r * k) := by group
  have hrr : r = k * (k⁻¹ * r * k) * k⁻¹ := by group
  have hzt' : k * (z * t) * k⁻¹ = z * t := by
    calc k * (z * t) * k⁻¹ = (k * z * k⁻¹) * (k * t * k⁻¹) := by group
      _ = z * t := by rw [hkz, hkt]
  have hzmem : z ∈ zpowers z ⊔ zpowers t := mem_sup_left (mem_zpowers z)
  have htmem : t ∈ zpowers z ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  rcases h.C _ hr' hcent with h1 | h1 | h1 | h1
  · rw [hrr, h1]; simp
  · rw [hrr, h1, hkz]; exact hzmem
  · rw [hrr, h1, hkt]; exact htmem
  · rw [hrr, h1, hzt']; exact mul_mem hzmem htmem

include h in
theorem sylow_centralizer_shape [Finite G] (hzt : ∃ x : G, x * z * x⁻¹ = z * t) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSC : S ≤ centralizer (E : Set G))
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S)
    (hzS : z ∈ S) :
    S = zpowers z ⊔ zpowers t ∨ (∃ k : ℕ, 2 ≤ k ∧ Nonempty (S ≃* DihedralGroup (2 ^ k))) ∨
      ∃ n : ℕ, 4 ≤ n ∧ Nonempty (S ≃* CFSG.Open.SemidihedralGroup n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC : t ∈ centralizer (E : Set G) := by
    rw [mem_centralizer_iff]
    intro e he
    exact h.t_comm_E he
  have hz2 : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, h.cfg.z_order]; norm_num)
  have ht2 : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, h.t_order]; norm_num)
  have htS : t ∈ S := by
    have hSt : S ≤ centralizer (zpowers t : Set G) := fun s hs => by
      rw [mem_centralizer_iff]
      rintro x hx
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
      exact ((show Commute t s from mem_centralizer_iff.1 (hSC hs) t h.econfig.t_mem).zpow_left
        k).eq
    have hS2' : IsPGroup 2 (S ⊔ zpowers t : Subgroup G) :=
      hS2.to_sup_of_normal_right' ht2 (hSt.trans (centralizer_le_normalizer _))
    have := hSmax _ hS2' (sup_le hSC (zpowers_le.2 hC)) le_sup_left
    rw [← this]
    exact mem_sup_right (mem_zpowers t)
  set U : Subgroup G := zpowers z ⊔ zpowers t with hUdef
  have hUS : U ≤ S := sup_le (zpowers_le.2 hzS) (zpowers_le.2 htS)
  have hzt_cent : zpowers t ≤ centralizer (zpowers z : Set G) := by
    rw [zpowers_le]
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    exact ((show Commute z t from h.cfg.t_comm_z.symm).zpow_left k).eq
  have hdisj : Disjoint (zpowers z) (zpowers t) := by
    rw [Subgroup.disjoint_def]
    intro x hxz hxt
    rcases mem_zpowers_sq_eq_one h.cfg.z_sq hxz with h1 | h1
    · exact h1
    · rcases mem_zpowers_sq_eq_one h.cfg.t_sq hxt with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) h.cfg.z_ne_t
  have hU4 : Nat.card U = 4 := by
    have e := Nat.card_congr (prodSupEquiv hzt_cent hdisj).toEquiv
    rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, h.cfg.z_order, h.t_order] at e
    exact e.symm
  have hUexp : ∀ u ∈ U, u ^ 2 = 1 := by
    intro u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hzt_cent hu
    have hab : a * b = b * a := mem_centralizer_iff.1 (hzt_cent hb) a ha
    have ha2 : a * a = 1 := by
      rcases mem_zpowers_sq_eq_one h.cfg.z_sq ha with h1 | h1
      · rw [h1, one_mul]
      · rw [h1]; exact h.cfg.z_sq
    have hb2 : b * b = 1 := by
      rcases mem_zpowers_sq_eq_one h.cfg.t_sq hb with h1 | h1
      · rw [h1, one_mul]
      · rw [h1]; exact h.cfg.t_sq
    calc (a * b) ^ 2 = a * b * (a * b) := pow_two _
      _ = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  have hCU : S ⊓ centralizer (U : Set G) ≤ U := by
    rintro s ⟨hsS, hsU⟩
    have hzU : z ∈ U := mem_sup_left (mem_zpowers z)
    have hsz : s ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.1 hsU z hzU).symm
    have hR2 : IsPGroup 2 (zpowers s) := hS2.to_le (zpowers_le.2 hsS)
    have hRE : zpowers s ≤ centralizer (E : Set G) := zpowers_le.2 (hSC hsS)
    have hRz : zpowers s ≤ centralizer ({z} : Set G) := zpowers_le.2 hsz
    exact h.le_of_two_group hzt hR2 hRE hRz (mem_zpowers s)
  by_cases hUeq : U = S
  · exact Or.inl hUeq.symm
  · exact Or.inr (CFSG.QuasithinUnique.suzuki_selfCentralizing_four hS2 hUS hU4 hUexp hCU hUeq)

end OuterE

end CFSG.EvenSporadicStandard.Fin76b
