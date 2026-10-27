module

public import CFSG.GF2Type.Aschbacher1976Full.HSCruxL4
public import CFSG.GF2Type.Aschbacher1976Full.HSCruxClass2

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint Subgroup PartC
open scoped commutatorElement

theorem Fz_le_sylow_H {G : Type} [Group G] [Finite G] {z : G} {T : Sylow 2 G}
    (hF2 : IsPGroup 2 ↥(Fz z)) (hTH : (T : Subgroup G) ≤ Hz z) : Fz z ≤ (T : Subgroup G) := by
  have hnorm : (T : Subgroup G) ≤ normalizer (Fz z : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro f
    constructor
    · exact fun hf => Width.Fz_conj_mem (hTH ht) hf
    · intro hf
      have h := Width.Fz_conj_mem ((Hz z).inv_mem (hTH ht)) hf
      have e : t⁻¹ * (t * f * t⁻¹) * t⁻¹⁻¹ = f := by group
      rwa [e] at h
  have hsup : IsPGroup 2 ↥((T : Subgroup G) ⊔ Fz z) :=
    T.isPGroup'.to_sup_of_normal_right' hF2 hnorm
  exact le_sup_right.trans (T.is_maximal' hsup le_sup_left).le

theorem cruxL5_holds : CruxL5Stmt := by
  intro G _ _ z T hbad hfib k hk E hE htb
  obtain ⟨u, hu, huT⟩ := exists_dinv_le_T hbad
  obtain ⟨hset, hti, hTH, -⟩ := hbad
  have hset' := hset
  obtain ⟨⟨_, _, hz, hsymp⟩, hZ4⟩ := hset
  have hF2 : IsPGroup 2 ↥(Fz z) := hsymp.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ4
  obtain ⟨y, hy⟩ := exists_gen hD hz hF2 hu.1
  obtain ⟨-, hy2⟩ := gen_props hD hz hF2 hu.1 hy
  obtain ⟨-, hk2⟩ := gen_props hD hz hF2 (IsConj.refl z) hk
  have hE0 := hE
  obtain ⟨hEF, hEn, hzE, hkE, -, hDE⟩ := hE
  have hkF : k ∈ Fz z := by
    rw [← hD.sup_eq]
    exact Subgroup.mem_sup_left (by rw [← ZF_z hD hz hF2, hk]; exact mem_zpowers k)
  have hkk : k * k ∈ E := by rw [← pow_two, hk2]; exact hzE
  have huE : u ∈ E := hDE hu
  have hFT : Fz z ≤ (T : Subgroup G) := Fz_le_sylow_H hF2 hTH
  have hkT : k ∈ (T : Subgroup G) := hFT hkF
  have hyT : y ∈ (T : Subgroup G) := huT (hy ▸ mem_zpowers y)
  have hyH : y ∈ Hz z := hTH hyT
  have hyF : y ∉ Fz z := (hti.2 u hu).2 y hy
  haveI hEN : (E.subgroupOf (T : Subgroup G)).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hEn _ (hTH g.2) _ hn⟩
  obtain ⟨π, hπ⟩ : ∃ π : ↥(T : Subgroup G) →* ↥(T : Subgroup G) ⧸ E.subgroupOf (T : Subgroup G),
      ∀ a, π a = QuotientGroup.mk a := ⟨QuotientGroup.mk' _, fun a => rfl⟩
  have hπsurj : ∀ x, ∃ g, π g = x := fun x => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨g, hπ g⟩
  have hπ1 : ∀ a : ↥(T : Subgroup G), π a = 1 ↔ (a : G) ∈ E := fun a => by
    rw [hπ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hπeq : ∀ a b : ↥(T : Subgroup G), π a = π b ↔ (a : G)⁻¹ * (b : G) ∈ E := fun a b => by
    rw [hπ, hπ, QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  obtain ⟨κ, hκ⟩ : ∃ c, c = π ⟨k, hkT⟩ := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ c, c = π ⟨y, hyT⟩ := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ↥(T : Subgroup G) →* Qbar z,
      ∀ a, q a = qmk z (Subgroup.inclusion hTH a) :=
    ⟨(qmk z).comp (Subgroup.inclusion hTH), fun a => rfl⟩
  have hq1 : ∀ a : ↥(T : Subgroup G), q a = 1 ↔ (a : G) ∈ Fz z := fun a => by
    rw [hq]; exact qmk_eq_one_iff z _
  obtain ⟨S, hS⟩ : ∃ S : Subgroup (Qbar z), S = ((T : Subgroup G).subgroupOf (Hz z)).map (qmk z) :=
    ⟨_, rfl⟩
  have hSmem : ∀ a : ↥(T : Subgroup G), q a ∈ S := fun a => by
    rw [hS, hq]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr a.2)
  have hSp : IsPGroup 2 ↥S := by
    have hT₀ : IsPGroup 2 ↥((T : Subgroup G).subgroupOf (Hz z)) :=
      T.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
    rw [hS]
    exact hT₀.map (qmk z)
  have hyq : yBar z u = q ⟨y, hyT⟩ := by
    rw [hq]
    exact yBar_eq hD hz hF2 hti hu (y := ⟨y, hyH⟩) hy
  have hYS : yBar z u ∈ S := by
    rw [hyq]
    exact hSmem _
  have hY1 : yBar z u ≠ 1 := yBar_ne_one hD hz hF2 hti hu
  have hY2 : yBar z u ^ 2 = 1 := yBar_sq hD hz hF2 hti hu
  obtain ⟨-, c2, c3⟩ := htb S hSp (yBar z u) ⟨u, hu, rfl⟩ hYS
  have c2' : ∀ x ∈ S, ∀ w ∈ S, ⁅x, w⁆ = 1 ∨ ⁅x, w⁆ = yBar z u := by
    intro x hx w hw
    rw [commutatorElement_def]
    exact c2 x hx w hw
  have hCC : ∀ a : ↥(T : Subgroup G), q a * yBar z u = yBar z u * q a := by
    intro a
    rcases c2' (q a) (hSmem a) (yBar z u) hYS with h | h
    · exact commutatorElement_eq_one_iff_mul_comm.mp h
    · exfalso
      apply hY1
      rw [commutatorElement_def] at h
      have key : q a * yBar z u * (q a)⁻¹ = 1 := by
        calc q a * yBar z u * (q a)⁻¹ = (q a * yBar z u * (q a)⁻¹ * (yBar z u)⁻¹) * yBar z u := by
              group
          _ = yBar z u * yBar z u := by rw [h]
          _ = 1 := by rw [← pow_two]; exact hY2
      calc yBar z u = (q a)⁻¹ * (q a * yBar z u * (q a)⁻¹) * q a := by group
        _ = 1 := by rw [key]; group
  have hκc : ∀ x : ↥(T : Subgroup G) ⧸ E.subgroupOf (T : Subgroup G), x * κ = κ * x := by
    intro x
    obtain ⟨g, rfl⟩ := hπsurj x
    rw [hκ, ← map_mul, ← map_mul, hπeq]
    have := inv_conj_mem hE0 hkF hkk ((Hz z).inv_mem (hTH g.2)) hkF
    convert this using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hηc : ∀ x : ↥(T : Subgroup G) ⧸ E.subgroupOf (T : Subgroup G), x * η = η * x := by
    intro x
    obtain ⟨g, rfl⟩ := hπsurj x
    rw [hη, ← map_mul, ← map_mul, hπeq]
    have hcc : qmk z (Subgroup.inclusion hTH g⁻¹) * yBar z u
        = yBar z u * qmk z (Subgroup.inclusion hTH g⁻¹) := by
      have := hCC g⁻¹
      rw [hq] at this
      exact this
    have hcomm : qmk z (Subgroup.inclusion hTH g⁻¹) * yBar z u
        * (qmk z (Subgroup.inclusion hTH g⁻¹))⁻¹ = yBar z u := by
      rw [hcc, mul_inv_cancel_right]
    have hconj := cruxL4_holds hset' hti hfib k hk E hE0 u hu y hy
      (Subgroup.inclusion hTH g⁻¹) hcomm
    convert hconj using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    group
  have hκ1 : κ ≠ 1 := by
    rw [hκ, Ne, hπ1]
    exact hkE
  have hη1 : η ≠ 1 := by
    rw [hη, Ne, hπ1]
    exact fun h => hyF (hEF h)
  have hη2 : η * η = 1 := by
    rw [hη, ← map_mul, hπ1]
    show y * y ∈ E
    rw [← pow_two, hy2]
    exact huE
  have hκ2 : κ * κ = 1 := by
    rw [hκ, ← map_mul, hπ1]
    exact hkk
  have hηκ : η ≠ κ := by
    rw [hη, hκ, Ne, hπeq]
    intro h
    apply hyF
    have h' : y⁻¹ * k ∈ E := h
    have e : y = k * (y⁻¹ * k)⁻¹ := by group
    rw [e]
    exact (Fz z).mul_mem hkF (hEF (E.inv_mem h'))
  have hV0F : ∀ b : ↥(T : Subgroup G), (b : G) ∈ Fz z → π b = 1 ∨ π b = κ := by
    intro b hb
    rcases mem_E_or_kE hE0 hkF hkk hb with h | h
    · exact Or.inl ((hπ1 b).mpr h)
    · right
      rw [hκ, eq_comm, hπeq]
      exact h
  have hV0 : ∀ a : ↥(T : Subgroup G), ((a : G) ∈ Fz z ∨ y⁻¹ * (a : G) ∈ Fz z) →
      π a = 1 ∨ π a = κ ∨ π a = η ∨ π a = η * κ := by
    rintro a (ha | ha)
    · rcases hV0F a ha with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have hbF : (((⟨y, hyT⟩ : ↥(T : Subgroup G))⁻¹ * a : ↥(T : Subgroup G)) : G) ∈ Fz z := ha
      have hab : π a = η * π ((⟨y, hyT⟩ : ↥(T : Subgroup G))⁻¹ * a) := by
        rw [hη, ← map_mul, mul_inv_cancel_left]
      rcases hV0F _ hbF with h | h
      · exact Or.inr (Or.inr (Or.inl (hab.trans (by rw [h, mul_one]))))
      · exact Or.inr (Or.inr (Or.inr (hab.trans (by rw [h]))))
  have hcV : ∀ a : ↥(T : Subgroup G), (q a = 1 ∨ q a = yBar z u) →
      ∀ x : ↥(T : Subgroup G) ⧸ E.subgroupOf (T : Subgroup G), x * π a = π a * x := by
    intro a ha x
    have hm : π a = 1 ∨ π a = κ ∨ π a = η ∨ π a = η * κ := by
      rcases ha with h | h
      · exact hV0 a (Or.inl ((hq1 a).mp h))
      · refine hV0 a (Or.inr ?_)
        have h1 : q ((⟨y, hyT⟩ : ↥(T : Subgroup G))⁻¹ * a) = 1 := by
          rw [map_mul, map_inv, ← hyq, h, inv_mul_cancel]
        exact (hq1 _).mp h1
    exact Class2.central_of_mem hκc hηc hm x
  have hcomm_of_mul : ∀ a b : ↥(T : Subgroup G),
      (q (a⁻¹ * b) = 1 ∨ q (a⁻¹ * b) = yBar z u) → π a * π b = π b * π a := by
    intro a b h
    have hc := hcV (a⁻¹ * b) h (π a)
    have hb : π b = π a * π (a⁻¹ * b) := by
      rw [← map_mul, mul_inv_cancel_left]
    rw [hb]
    calc π a * (π a * π (a⁻¹ * b)) = π a * (π (a⁻¹ * b) * π a) := by rw [hc]
      _ = (π a * π (a⁻¹ * b)) * π a := (mul_assoc _ _ _).symm
  have hR3 : ∀ a b : ↥(T : Subgroup G),
      (q a = 1 ∨ q a = yBar z u ∨ q b = 1 ∨ q b = yBar z u ∨ q b = q a ∨ q b = q a * yBar z u) →
      π a * π b = π b * π a := by
    intro a b h
    rcases h with h | h | h | h | h | h
    · exact (hcV a (Or.inl h) (π b)).symm
    · exact (hcV a (Or.inr h) (π b)).symm
    · exact hcV b (Or.inl h) (π a)
    · exact hcV b (Or.inr h) (π a)
    · exact hcomm_of_mul a b (Or.inl (by rw [map_mul, map_inv, h, inv_mul_cancel]))
    · exact hcomm_of_mul a b (Or.inr (by rw [map_mul, map_inv, h, inv_mul_cancel_left]))
  have hCL : ∀ a b : ↥(T : Subgroup G), π ⁅a, b⁆ = 1 ∨ π ⁅a, b⁆ = η ∨ π ⁅a, b⁆ = η * κ := by
    intro a b
    have hqc : q ⁅a, b⁆ = 1 ∨ q ⁅a, b⁆ = yBar z u := by
      rw [map_commutatorElement]
      exact c2' _ (hSmem a) _ (hSmem b)
    rcases hqc with h | h
    · left
      have hcomm : q a * q b = q b * q a := by
        apply commutatorElement_eq_one_iff_mul_comm.mp
        rw [← map_commutatorElement]
        exact h
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hR3 a b (c3 _ (hSmem a) _ (hSmem b) hcomm)
    · right
      have hc : q ((⟨y, hyT⟩ : ↥(T : Subgroup G))⁻¹ * ⁅a, b⁆) = 1 := by
        rw [map_mul, map_inv, ← hyq, h, inv_mul_cancel]
      have hpc : π ⁅a, b⁆ = η * π ((⟨y, hyT⟩ : ↥(T : Subgroup G))⁻¹ * ⁅a, b⁆) := by
        rw [hη, ← map_mul, mul_inv_cancel_left]
      rcases hV0F _ ((hq1 _).mp hc) with h' | h'
      · left
        rw [hpc, h', mul_one]
      · right
        rw [hpc, h']
  have hV : ∀ x x' : ↥(T : Subgroup G) ⧸ E.subgroupOf (T : Subgroup G),
      ⁅x, x'⁆ = 1 ∨ ⁅x, x'⁆ = κ ∨ ⁅x, x'⁆ = η ∨ ⁅x, x'⁆ = η * κ := by
    intro x x'
    obtain ⟨a, rfl⟩ := hπsurj x
    obtain ⟨b, rfl⟩ := hπsurj x'
    rw [← map_commutatorElement]
    rcases hCL a b with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hne : ∀ x x' : ↥(T : Subgroup G) ⧸ E.subgroupOf (T : Subgroup G), ⁅x, x'⁆ ≠ κ := by
    intro x x' h
    obtain ⟨a, rfl⟩ := hπsurj x
    obtain ⟨b, rfl⟩ := hπsurj x'
    rw [← map_commutatorElement] at h
    rcases hCL a b with h' | h' | h'
    · exact hκ1 (h.symm.trans h')
    · exact hηκ (h'.symm.trans h)
    · apply hη1
      have e : η * κ = κ := h'.symm.trans h
      calc η = η * κ * κ := by rw [mul_assoc, hκ2, mul_one]
        _ = κ * κ := by rw [e]
        _ = 1 := hκ2
  obtain ⟨C, hκC, hC⟩ := Class2.exists_subgroup_not_mem hκc hηc hη2 hκ1 hη1 hηκ hV hne hκ2
  have hN : ⁅(T : Subgroup G), (T : Subgroup G)⁆ ⊔ E ≤
      (C.comap π).map (T : Subgroup G).subtype := by
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      refine ⟨⁅(⟨g₁, hg₁⟩ : ↥(T : Subgroup G)), ⟨g₂, hg₂⟩⁆, ?_, ?_⟩
      · show π _ ∈ C
        rw [map_commutatorElement]
        exact hC _ _
      · exact map_commutatorElement (T : Subgroup G).subtype _ _
    · intro e he
      refine ⟨⟨e, hFT (hEF he)⟩, ?_, rfl⟩
      show π _ ∈ C
      rw [(hπ1 ⟨e, hFT (hEF he)⟩).mpr he]
      exact C.one_mem
  intro hmem
  obtain ⟨w, hw, hwk⟩ := Subgroup.mem_map.mp (hN hmem)
  have hw' : w = ⟨k, hkT⟩ := Subtype.ext hwk
  apply hκC
  rw [hκ, ← hw']
  exact hw

end CFSG.GF2Type.Aschbacher1976Full.HS
