module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma63
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Suzuki
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralCentralOddComplement

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} {z t : G} {T₀ E : Subgroup G}

theorem EConfig.le_zpowers_t (h : InnerConfig G A z t T₀) (hE : EConfig A T₀ E t)
    {R : Subgroup G} (hR : IsPGroup 2 R) (hRA : R ≤ A) (hRE : R ≤ centralizer (E : Set G)) :
    R ≤ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 E := h.T₀_pgroup.to_le hE.le
  have hREn : R ≤ normalizer (E : Set G) := hRE.trans (centralizer_le_normalizer E)
  have hRE2 : IsPGroup 2 (R ⊔ E : Subgroup G) := hR.to_sup_of_normal_right' hE2 hREn
  have hRE_A : R ⊔ E ≤ A := sup_le hRA (hE.le.trans h.T₀_le)
  obtain ⟨m, hm, hAm⟩ := h.T₀_odd
  have hT0A : IsPGroup 2 (T₀.subgroupOf A) := h.T₀_pgroup.comap_subtype
  have hidx : ¬ 2 ∣ (T₀.subgroupOf A).index := by
    have h1 := Subgroup.index_mul_card (H := T₀.subgroupOf A)
    rw [Nat.card_congr (subgroupOfEquivOfLe h.T₀_le).toEquiv, hAm] at h1
    have hpos : 0 < Nat.card T₀ := Nat.card_pos
    have : (T₀.subgroupOf A).index = m := Nat.eq_of_mul_eq_mul_right hpos (h1.trans (mul_comm _ _))
    rw [this]
    exact fun hd => (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 hd)
  let T0S : Sylow 2 A := hT0A.toSylow hidx
  have hRt : IsPGroup 2 ((R ⊔ E).subgroupOf A) := hRE2.comap_subtype
  obtain ⟨Q', hQ'⟩ := hRt.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A T0S Q'
  have hconj : ∀ p ∈ R ⊔ E, (g : G)⁻¹ * p * (g : G) ∈ T₀ := by
    intro p hp
    have hpQ : (⟨p, hRE_A hp⟩ : A) ∈ (Q' : Subgroup A) := hQ' (mem_subgroupOf.2 hp)
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hpQ
    obtain ⟨s, hs, hsp⟩ := hpQ
    have hs' : (s : G) ∈ T₀ := mem_subgroupOf.1 hs
    have e1 : g⁻¹ * ⟨p, hRE_A hp⟩ * g = s := by
      rw [← hsp, MulAut.smul_def, MulAut.conj_apply]
      group
    have e2 := congrArg Subtype.val e1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e2
    rw [e2]
    exact hs'
  set f : G →* G := (MulAut.conj (g : G)⁻¹).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj (g : G)⁻¹).injective
  have hf_apply : ∀ p, f p = (g : G)⁻¹ * p * (g : G) := fun p => by
    simp [f]
  have hE'le : E.map f ≤ T₀ := by
    rintro _ ⟨e, he, rfl⟩
    rw [hf_apply]
    exact hconj e (mem_sup_right he)
  have hE'E : E.map f = E := hE.unique _ hE'le ⟨E.equivMapOfInjective f hfinj⟩
  have hsurjE : ∀ e ∈ E, ∃ e' ∈ E, (g : G)⁻¹ * e' * (g : G) = e := by
    intro e he
    have : e ∈ E.map f := by rw [hE'E]; exact he
    obtain ⟨e', he', hfe⟩ := this
    exact ⟨e', he', by rw [← hf_apply]; exact hfe⟩
  have hgE : ∀ e ∈ E, (g : G)⁻¹ * e * (g : G) ∈ E := fun e he => by
    have : f e ∈ E.map f := ⟨e, he, rfl⟩
    rw [hE'E, hf_apply] at this
    exact this
  intro r hr
  have hsT : (g : G)⁻¹ * r * (g : G) ∈ T₀ := hconj r (mem_sup_left hr)
  have hcomm : ∀ e' ∈ E, ((g : G)⁻¹ * r * (g : G)) * e' = e' * ((g : G)⁻¹ * r * (g : G)) := by
    intro e' he'
    obtain ⟨e, he, rfl⟩ := hsurjE e' he'
    have hre : r * e = e * r := (mem_centralizer_iff.1 (hRE hr) e he).symm
    calc (g : G)⁻¹ * r * (g : G) * ((g : G)⁻¹ * e * (g : G)) = (g : G)⁻¹ * (r * e) * (g : G) := by
          group
      _ = (g : G)⁻¹ * (e * r) * (g : G) := by rw [hre]
      _ = (g : G)⁻¹ * e * (g : G) * ((g : G)⁻¹ * r * (g : G)) := by group
  rcases hE.cent _ hsT hcomm with h1 | h1
  · have : r = 1 := by
      calc r = (g : G) * ((g : G)⁻¹ * r * (g : G)) * (g : G)⁻¹ := by group
        _ = 1 := by rw [h1]; group
    rw [this]
    exact one_mem _
  · obtain ⟨e', he', hee'⟩ := hsurjE t hE.t_mem
    have he't : e' = (g : G) * t * (g : G)⁻¹ := by
      calc e' = (g : G) * ((g : G)⁻¹ * e' * (g : G)) * (g : G)⁻¹ := by group
        _ = (g : G) * t * (g : G)⁻¹ := by rw [hee']
    have hcen' : ∀ f' ∈ E, f' * e' = e' * f' := by
      intro f' hf'
      have hf'' := hgE f' hf'
      have hft : ((g : G)⁻¹ * f' * (g : G)) * t = t * ((g : G)⁻¹ * f' * (g : G)) :=
        h.t_central _ (hE.le hf'')
      calc f' * e' = (g : G) * (((g : G)⁻¹ * f' * (g : G)) * t) * (g : G)⁻¹ := by
            rw [he't]; group
        _ = (g : G) * (t * ((g : G)⁻¹ * f' * (g : G))) * (g : G)⁻¹ := by rw [hft]
        _ = e' * f' := by rw [he't]; group
    have hr_eq : r = e' := by
      calc r = (g : G) * ((g : G)⁻¹ * r * (g : G)) * (g : G)⁻¹ := by group
        _ = (g : G) * t * (g : G)⁻¹ := by rw [h1]
        _ = e' := he't.symm
    rcases hE.center e' he' hcen' with h2 | h2
    · exfalso
      apply h.t_ne
      rw [← hee', h2]
      group
    · rw [hr_eq, h2]
      exact mem_zpowers t

omit [Finite G] in
theorem EConfig.z_mem_centralizer (h : InnerConfig G A z t T₀) (hE : EConfig A T₀ E t) :
    z ∈ centralizer (E : Set G) := by
  rw [mem_centralizer_iff]
  intro e he
  exact h.z_comm_of_mem_A (h.T₀_le (hE.le he))

omit [Finite G] in
theorem EConfig.t_mem_centralizer (h : InnerConfig G A z t T₀) (hE : EConfig A T₀ E t) :
    t ∈ centralizer (E : Set G) := by
  rw [mem_centralizer_iff]
  intro e he
  exact h.t_central e (hE.le he)

theorem EConfig.sylow_centralizer_shape (h : InnerConfig G A z t T₀) (hE : EConfig A T₀ E t)
    {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSC : S ≤ centralizer (E : Set G))
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S)
    (hzS : z ∈ S) :
    S = zpowers z ⊔ zpowers t ∨ (∃ k : ℕ, 2 ≤ k ∧ Nonempty (S ≃* DihedralGroup (2 ^ k))) ∨
      ∃ n : ℕ, 4 ≤ n ∧ Nonempty (S ≃* CFSG.Open.SemidihedralGroup n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := hE.t_mem_centralizer h
  have hz2 : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, h.z_order]; norm_num)
  have ht2 : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, h.t_order]; norm_num)
  have htS : t ∈ S := by
    have hSt : S ≤ centralizer (zpowers t : Set G) := fun s hs => by
      rw [mem_centralizer_iff]
      rintro x hx
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
      exact ((show Commute t s from mem_centralizer_iff.1 (hSC hs) t hE.t_mem).zpow_left k).eq
    have hS2' : IsPGroup 2 (S ⊔ zpowers t : Subgroup G) :=
      hS2.to_sup_of_normal_right' ht2 (hSt.trans (centralizer_le_normalizer _))
    have := hSmax _ hS2' (sup_le hSC (zpowers_le.2 hC)) le_sup_left
    rw [← this]
    exact mem_sup_right (mem_zpowers t)
  set U : Subgroup G := zpowers z ⊔ zpowers t with hUdef
  have hUS : U ≤ S := sup_le (zpowers_le.2 hzS) (zpowers_le.2 htS)
  have hzt : zpowers t ≤ centralizer (zpowers z : Set G) := by
    rw [zpowers_le]
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    exact ((show Commute z t from h.t_comm_z.symm).zpow_left k).eq
  have hdisj : Disjoint (zpowers z) (zpowers t) := by
    rw [Subgroup.disjoint_def]
    intro x hxz hxt
    rcases mem_zpowers_sq_eq_one h.z_sq hxz with h1 | h1
    · exact h1
    · rcases mem_zpowers_sq_eq_one h.t_sq hxt with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) h.z_ne_t
  have hU4 : Nat.card U = 4 := by
    have e := Nat.card_congr (prodSupEquiv hzt hdisj).toEquiv
    rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, h.z_order, h.t_order] at e
    exact e.symm
  have hUexp : ∀ u ∈ U, u ^ 2 = 1 := by
    intro u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hzt hu
    have hab : a * b = b * a := mem_centralizer_iff.1 (hzt hb) a ha
    have ha2 : a * a = 1 := by
      rcases mem_zpowers_sq_eq_one h.z_sq ha with h1 | h1
      · rw [h1, one_mul]
      · rw [h1]; exact h.z_sq
    have hb2 : b * b = 1 := by
      rcases mem_zpowers_sq_eq_one h.t_sq hb with h1 | h1
      · rw [h1, one_mul]
      · rw [h1]; exact h.t_sq
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
    rw [h.cent_eq] at hsz
    obtain ⟨a, ha, c, hc, hsac⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (zpowers_le.2 h.z_cent) hsz
    have haS : a ∈ S := by
      have : a = s * c⁻¹ := by rw [hsac]; group
      rw [this]
      exact mul_mem hsS (inv_mem (zpowers_le.2 hzS hc))
    have hat : a ∈ zpowers t :=
      EConfig.le_zpowers_t h hE (hS2.to_le (zpowers_le.2 haS)) (zpowers_le.2 ha)
        (zpowers_le.2 (hSC haS)) (mem_zpowers a)
    rw [hsac]
    exact mul_mem (mem_sup_right hat) (mem_sup_left hc)
  by_cases hUeq : U = S
  · exact Or.inl hUeq.symm
  · exact Or.inr (CFSG.QuasithinUnique.suzuki_selfCentralizing_four hS2 hUS hU4 hUexp hCU hUeq)

theorem EConfig.centralizer_oddCore_dihedral (h : InnerConfig G A z t T₀) (hE : EConfig A T₀ E t)
    {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSC : S ≤ centralizer (E : Set G))
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S)
    {k : ℕ} (hk : 2 ≤ k) (hS : Nonempty (S ≃* DihedralGroup (2 ^ k))) :
    ∃ N : Subgroup (centralizer (E : Set G)), N.Normal ∧ (∀ x, x ∈ N ↔ Odd (orderOf x)) ∧
      N ⊓ S.subgroupOf (centralizer (E : Set G)) = ⊥ ∧
      (N : Set (centralizer (E : Set G))) *
        (S.subgroupOf (centralizer (E : Set G)) : Set (centralizer (E : Set G))) = Set.univ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := hE.t_mem_centralizer h
  let Ssyl : Sylow 2 (centralizer (E : Set G)) :=
    { toSubgroup := S.subgroupOf (centralizer (E : Set G))
      isPGroup' := hS2.comap_subtype
      is_maximal' := by
        intro Q hQ hSQ
        have hR : Q.map (centralizer (E : Set G)).subtype = S := by
          refine hSmax _ (hQ.map _) (by rintro _ ⟨q, -, rfl⟩; exact q.2) ?_
          intro s hs
          exact ⟨⟨s, hSC hs⟩, hSQ (mem_subgroupOf.2 hs), rfl⟩
        ext x
        constructor
        · intro hx
          show (x : G) ∈ S
          rw [← hR]
          exact ⟨x, hx, rfl⟩
        · intro hx
          exact hSQ hx }
  have hS' : Nonempty (DihedralGroup (2 ^ (k + 1 - 1)) ≃*
      (Ssyl : Subgroup (centralizer (E : Set G)))) := by
    obtain ⟨e⟩ := hS
    rw [Nat.add_sub_cancel]
    exact ⟨e.symm.trans (subgroupOfEquivOfLe hSC).symm⟩
  have ht : ∃ t' ∈ Subgroup.center (centralizer (E : Set G)), orderOf t' = 2 := by
    refine ⟨⟨t, hC⟩, ?_, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.1 g.2 t hE.t_mem).symm
    · rw [Subgroup.orderOf_mk, h.t_order]
  obtain ⟨N, hN, -, -, -, hmem, hprod, hinf, -⟩ :=
    CFSG.Semidihedral.Principal.dihedral_central_involution_normal_odd_complement Ssyl
      (n := k + 1) (by omega) hS' ht
  exact ⟨N, hN, hmem, hinf, hprod⟩

theorem EConfig.t_central_Q (h : InnerConfig G A z t T₀) (hE : EConfig A T₀ E t)
    {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hTQ : T₀ ⊔ zpowers z ≤ Q) {x : G} (hxQ : x ∈ Q)
    (hxz : x * z * x⁻¹ = z * t) (hxt : x * t * x⁻¹ = t) : ∀ q ∈ Q, q * t = t * q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzQ : z ∈ Q := hTQ (mem_sup_right (mem_zpowers z))
  have hEQ : E ≤ Q := (hE.le.trans le_sup_left).trans hTQ
  have hzE : zpowers z ≤ centralizer (E : Set G) := zpowers_le.2 (hE.z_mem_centralizer h)
  have hcen : ∀ q ∈ Q, (∀ y ∈ Q, y * q = q * y) → q = 1 ∨ q = t := by
    intro q hq hc
    have hqE : q ∈ centralizer (E : Set G) := by
      rw [mem_centralizer_iff]
      intro e he
      exact hc e (hEQ he)
    have hqz : q ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      exact (hc z hzQ).symm
    rw [h.cent_eq] at hqz
    obtain ⟨a, ha, c, hcz, hqac⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (zpowers_le.2 h.z_cent) hqz
    have haq : a = q * c⁻¹ := by rw [hqac]; group
    have haQ : a ∈ Q := by
      rw [haq]
      exact mul_mem hq (inv_mem (zpowers_le.2 hzQ hcz))
    have haE : a ∈ centralizer (E : Set G) := by
      rw [haq]
      exact mul_mem hqE (inv_mem (hzE hcz))
    have hat : a ∈ zpowers t :=
      EConfig.le_zpowers_t h hE (hQ.to_le (zpowers_le.2 haQ)) (zpowers_le.2 ha)
        (zpowers_le.2 haE) (mem_zpowers a)
    have hxq : x * q * x⁻¹ = q := by
      have := hc x hxQ
      calc x * q * x⁻¹ = q * x * x⁻¹ := by rw [this]
        _ = q := by group
    rcases mem_zpowers_sq_eq_one h.t_sq hat with ha1 | ha1 <;>
      rcases mem_zpowers_sq_eq_one h.z_sq hcz with hc1 | hc1
    · left; rw [hqac, ha1, hc1, one_mul]
    · exfalso
      rw [hqac, ha1, hc1, one_mul] at hxq
      rw [hxz] at hxq
      exact h.t_ne (mul_left_cancel (hxq.trans (mul_one z).symm))
    · right; rw [hqac, ha1, hc1, mul_one]
    · exfalso
      rw [hqac, ha1, hc1] at hxq
      have h1 : x * (t * z) * x⁻¹ = (x * t * x⁻¹) * (x * z * x⁻¹) := by group
      rw [h1, hxt, hxz] at hxq
      exact h.t_ne (mul_left_cancel ((mul_left_cancel hxq).trans (mul_one z).symm))
  have hnt : Nontrivial Q := ⟨⟨1, ⟨z, hzQ⟩, fun h' => h.z_ne (congrArg Subtype.val h'.symm)⟩⟩
  have hcnt : Nontrivial (Subgroup.center Q) := hQ.center_nontrivial
  obtain ⟨⟨c, hcc⟩, hc1⟩ := exists_ne (1 : Subgroup.center Q)
  have hq1 : (c : G) ≠ 1 := fun h' => hc1 (Subtype.ext (Subtype.ext h'))
  have hcc' : ∀ y ∈ Q, y * (c : G) = (c : G) * y := fun y hy =>
    congrArg Subtype.val ((Subgroup.mem_center_iff.1 hcc) ⟨y, hy⟩)
  have hct : (c : G) = t := (hcen c c.2 hcc').resolve_left hq1
  intro q hq
  have := hcc' q hq
  rwa [hct] at this

end CFSG.EvenSporadicStandard.Fin76b
