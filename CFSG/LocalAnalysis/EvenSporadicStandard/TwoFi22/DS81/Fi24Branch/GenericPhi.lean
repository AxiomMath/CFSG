module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Facts

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem commutator_commutator_eq (x y : G) :
    ⁅⁅x, y⁆, y⁆ =
      (y ^ 2 * x * (y ^ 2)⁻¹ * x⁻¹) *
        ⁅(y ^ 2 * x * (y ^ 2)⁻¹ * x⁻¹)⁻¹, ⁅x, y⁆⁆ * ⁅x, y⁆ ^ 2 := by
  simp only [commutatorElement_def, pow_two, mul_inv_rev, inv_inv]
  group

theorem phi_card_le {R O V Y : Subgroup G} (hOR : O ≤ R) (hidx : O.relIndex R = 2)
    (hcardO : Nat.card ↥O = 2 ^ 12) (hVO : V ≤ O) (hcardV : Nat.card ↥V = 4)
    (hRV : ∀ r ∈ R, ∀ v ∈ V, r * v * r⁻¹ ∈ V) (hRO : ∀ r ∈ R, ∀ o ∈ O, r * o * r⁻¹ ∈ O)
    (hsq : ∀ x ∈ O, x ^ 2 ∈ V) (hcomm : ∀ x ∈ O, ∀ y ∈ O, x * y * x⁻¹ * y⁻¹ ∈ V)
    (hYO : ∀ y ∈ Y, ∀ o ∈ O, y * o * y⁻¹ ∈ O) (hYV : ∀ y ∈ Y, ∀ v ∈ V, y * v * y⁻¹ ∈ V)
    (hcen : ∀ y ∈ Y, ∀ r ∈ R, y * r * y⁻¹ * r⁻¹ ∈ O)
    (hlat : ∀ U : Subgroup G, V ≤ U → U ≤ O → InvUnder Y U →
      Nat.card ↥U = 2 ^ 2 ∨ Nat.card ↥U = 2 ^ 3 ∨ Nat.card ↥U = 2 ^ 11 ∨
        Nat.card ↥U = 2 ^ 12) :
    Nat.card ↥(Phi2 R) ≤ 16 := by
  obtain ⟨y₀, hy₀R, hy₀O, hcover⟩ :=
    (Subgroup.relIndex_eq_two_iff_exists_notMem_and).mp hidx
  have hy₀2O : y₀ ^ 2 ∈ O := by
    rcases hcover y₀ hy₀R with h | h
    · simpa [pow_two] using h
    · exact absurd h hy₀O
  have hy₀2invO : (y₀ ^ 2)⁻¹ ∈ O := O.inv_mem hy₀2O
  have hcoverL : ∀ b ∈ R, b ∈ O ∨ ∃ o ∈ O, b = y₀ * o := by
    intro b hbR
    rcases hcover b hbR with hb | hb
    · have hyb : y₀ * b ∈ O := by
        have h := hRO y₀ hy₀R (b * y₀) hb
        simpa [mul_assoc] using h
      exact Or.inr ⟨(y₀ ^ 2)⁻¹ * (y₀ * b), O.mul_mem hy₀2invO hyb, by group⟩
    · exact Or.inl hb
  have hcoverR : ∀ b ∈ R, b ∈ O ∨ ∃ o ∈ O, b = o * y₀ := by
    intro b hbR
    rcases hcover b hbR with hb | hb
    · exact Or.inr ⟨(b * y₀) * (y₀ ^ 2)⁻¹, O.mul_mem hb hy₀2invO, by group⟩
    · exact Or.inl hb
  have hV'normal : (V.subgroupOf O).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hVO]
    intro h k hh hk
    have hmem : k * h * k⁻¹ * h⁻¹ ∈ V := hcomm k hk h (hVO hh)
    have : k * h * k⁻¹ = (k * h * k⁻¹ * h⁻¹) * h := by group
    rw [this]
    exact V.mul_mem hmem hh
  letI : (V.subgroupOf O).Normal := hV'normal
  let q : ↥O →* (↥O ⧸ V.subgroupOf O) := QuotientGroup.mk' _
  have hq1 : ∀ y : ↥O, q y = 1 ↔ (y : G) ∈ V := by
    intro y
    change (y : ↥O ⧸ V.subgroupOf O) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  haveI hQcomm : IsMulCommutative (↥O ⧸ V.subgroupOf O) := by
    rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
    change ⁅(⊤ : Subgroup ↥O), (⊤ : Subgroup ↥O)⁆ ≤ V.subgroupOf O
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_subgroupOf]
    simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using
      hcomm (a : G) a.2 (b : G) b.2
  let σ : ↥O →* ↥O :=
    { toFun := fun x => ⟨y₀ * (x : G) * y₀⁻¹, hRO y₀ hy₀R x x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x z; ext; simp only [Subgroup.coe_mul]; group }
  have hσ : ∀ x : ↥O, ((σ x : ↥O) : G) = y₀ * (x : G) * y₀⁻¹ := fun x => rfl
  let φ : ↥O →* (↥O ⧸ V.subgroupOf O) :=
    { toFun := fun x => q x * (q (σ x))⁻¹
      map_one' := by simp
      map_mul' := by
        intro x z
        simp only [map_mul]
        rw [mul_inv_rev]
        ac_rfl }
  let C : Subgroup G := φ.ker.map O.subtype
  let S : Set G := {d | ∃ x ∈ O, d = ⁅x, y₀⁆}
  let D : Subgroup G := closure (S ∪ (V : Set G))
  have hSO : S ⊆ (O : Set G) := by
    rintro d ⟨x, hx, rfl⟩
    have h : x * (y₀ * x * y₀⁻¹)⁻¹ ∈ O := O.mul_mem hx (O.inv_mem (hRO y₀ hy₀R x hx))
    rwa [show x * (y₀ * x * y₀⁻¹)⁻¹ = ⁅x, y₀⁆ by rw [commutatorElement_def]; group] at h
  have hDO : D ≤ O := (Subgroup.closure_le _).2 (Set.union_subset hSO hVO)
  have hSD : ∀ x ∈ O, ⁅x, y₀⁆ ∈ D := fun x hx => Subgroup.subset_closure (Or.inl ⟨x, hx, rfl⟩)
  have hVD : V ≤ D := fun v hv => Subgroup.subset_closure (Or.inr hv)
  have hCO : C ≤ O := Subgroup.map_subtype_le _
  have mem_C : ∀ c : G, c ∈ C ↔ c ∈ O ∧ ⁅c, y₀⁆ ∈ V := by
    intro c
    constructor
    · intro hc
      rcases Subgroup.mem_map.mp hc with ⟨x, hxker, rfl⟩
      refine ⟨x.2, ?_⟩
      have hx1 : φ x = 1 := MonoidHom.mem_ker.mp hxker
      have hx2 : q (x * (σ x)⁻¹) = 1 := by
        rw [map_mul, map_inv]
        exact hx1
      have hxV : ((x * (σ x)⁻¹ : ↥O) : G) ∈ V := (hq1 _).mp hx2
      have hxu : ((x * (σ x)⁻¹ : ↥O) : G) = ⁅(x : G), y₀⁆ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hσ, commutatorElement_def]
        group
      rwa [hxu] at hxV
    · rintro ⟨hcO, hcV⟩
      refine Subgroup.mem_map.mpr ⟨⟨c, hcO⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      show q ⟨c, hcO⟩ * (q (σ ⟨c, hcO⟩))⁻¹ = 1
      rw [← map_inv, ← map_mul]
      refine (hq1 _).mpr ?_
      convert hcV using 1
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hσ, commutatorElement_def]
      group
  have hVC : V ≤ C := by
    intro v hv
    rw [mem_C]
    refine ⟨hVO hv, ?_⟩
    have h1 : y₀⁻¹ * v * y₀ * v⁻¹ ∈ V :=
      V.mul_mem (by simpa using hRV y₀⁻¹ (R.inv_mem hy₀R) v hv) (V.inv_mem hv)
    have h2 : y₀ * (y₀⁻¹ * v * y₀ * v⁻¹) * y₀⁻¹ ∈ V := hRV y₀ hy₀R _ h1
    convert h2 using 1
    group
  have hCD : D ≤ C := by
    change closure (S ∪ (V : Set G)) ≤ C
    refine (Subgroup.closure_le _).2 ?_
    rintro d (hd | hd)
    · rcases hd with ⟨x, hx, rfl⟩
      refine (mem_C _).mpr ⟨?_, ?_⟩
      · have h : x * (y₀ * x * y₀⁻¹)⁻¹ ∈ O := O.mul_mem hx (O.inv_mem (hRO y₀ hy₀R x hx))
        rwa [show x * (y₀ * x * y₀⁻¹)⁻¹ = ⁅x, y₀⁆ by rw [commutatorElement_def]; group] at h
      have he : y₀ ^ 2 * (x : G) * (y₀ ^ 2)⁻¹ * (x : G)⁻¹ ∈ V :=
        hcomm (y₀ ^ 2) hy₀2O x hx
      have hdO : ⁅(x : G), y₀⁆ ∈ O := by
        have h : x * (y₀ * x * y₀⁻¹)⁻¹ ∈ O := O.mul_mem hx (O.inv_mem (hRO y₀ hy₀R x hx))
        rwa [show x * (y₀ * x * y₀⁻¹)⁻¹ = ⁅x, y₀⁆ by rw [commutatorElement_def]; group] at h
      have hu2 : ⁅(x : G), y₀⁆ ^ 2 ∈ V := hsq _ hdO
      have hmid : ⁅(y₀ ^ 2 * (x : G) * (y₀ ^ 2)⁻¹ * (x : G)⁻¹)⁻¹, ⁅(x : G), y₀⁆⁆ ∈ V :=
        hcomm _ (hVO (V.inv_mem he)) _ hdO
      have hprod : (y₀ ^ 2 * (x : G) * (y₀ ^ 2)⁻¹ * (x : G)⁻¹) *
          ⁅(y₀ ^ 2 * (x : G) * (y₀ ^ 2)⁻¹ * (x : G)⁻¹)⁻¹, ⁅(x : G), y₀⁆⁆ *
          ⁅(x : G), y₀⁆ ^ 2 ∈ V := V.mul_mem (V.mul_mem he hmid) hu2
      rw [commutator_commutator_eq]
      exact hprod
    · exact hVC hd
  have hynorm : ∀ d ∈ D, y₀ * d * y₀⁻¹ ∈ D := by
    have hmap : D.map (MulAut.conj y₀ : G →* G) ≤ D := by
      change (closure (S ∪ (V : Set G))).map (MulAut.conj y₀ : G →* G) ≤ D
      rw [MonoidHom.map_closure]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨z, hz, rfl⟩
      rcases hz with hz | hz
      · rcases hz with ⟨x, hx, rfl⟩
        have h1 : (MulAut.conj y₀ : G →* G) ⁅x, y₀⁆ = ⁅y₀ * x * y₀⁻¹, y₀⁆ := by
          change y₀ * ⁅x, y₀⁆ * y₀⁻¹ = _
          rw [conjugate_commutatorElement]
          simp
        rw [h1]
        exact Subgroup.subset_closure (Or.inl ⟨y₀ * x * y₀⁻¹, hRO y₀ hy₀R x hx, rfl⟩)
      · exact Subgroup.subset_closure (Or.inr (hRV y₀ hy₀R z hz))
    intro d hd
    have : (MulAut.conj y₀ : G →* G) d = y₀ * d * y₀⁻¹ := rfl
    rw [← this]
    exact hmap (Subgroup.mem_map_of_mem _ hd)
  have honorm : ∀ c ∈ O, ∀ d ∈ D, c * d * c⁻¹ ∈ D := by
    intro c hc d hd
    have hdO : d ∈ O := hDO hd
    have h1 : ⁅c, d⁆ ∈ V := by
      simpa only [commutatorElement_def] using hcomm c hc d hdO
    have h2 : c * d * c⁻¹ = ⁅c, d⁆ * d := by rw [commutatorElement_def]; group
    rw [h2]
    exact D.mul_mem (hVD h1) hd
  have hYC : InvUnder Y C := by
    intro y hy c hc
    rw [mem_C] at hc ⊢
    obtain ⟨hcO, hcV⟩ := hc
    refine ⟨hYO y hy c hcO, ?_⟩
    have hc1 : ⁅y₀, y⁆ ∈ O := by
      have h := hcen y hy y₀ hy₀R
      rw [commutatorElement_def]
      convert O.inv_mem h using 1
      group
    have hc'O : y⁻¹ * ⁅y₀, y⁆ * y ∈ O := by
      have h := hYO y⁻¹ (Y.inv_mem hy) _ hc1
      simpa using h
    set c' : G := y⁻¹ * y₀ * y * y₀⁻¹ with hc'def
    have hc' : c' ∈ O := by
      rw [hc'def]
      convert hc'O using 1
      rw [commutatorElement_def]
      group
    have hcc : ⁅c, y⁻¹ * y₀ * y⁆ ∈ V := by
      have hmul : y⁻¹ * y₀ * y = c' * y₀ := by rw [hc'def]; group
      rw [hmul, commutatorElement_mul_right_eq_mul_conj]
      have h2 : ⁅c, c'⁆ ∈ V := hcomm c hcO c' hc'
      have h3 : c' * ⁅c, y₀⁆ * c'⁻¹ ∈ V := hRV c' (hOR hc') _ hcV
      have : ⁅c, c'⁆ * c' * ⁅c, y₀⁆ * c'⁻¹ ∈ V := by
        convert V.mul_mem h2 h3 using 1
        group
      exact this
    have h4 : ⁅y * c * y⁻¹, y₀⁆ = y * ⁅c, y⁻¹ * y₀ * y⁆ * y⁻¹ := by
      rw [conjugate_commutatorElement]
      group
    rw [h4]
    exact hYV y hy _ hcc
  have hYD : InvUnder Y D := by
    intro y hy
    have hmap : D.map (MulAut.conj y : G →* G) ≤ D := by
      change (closure (S ∪ (V : Set G))).map (MulAut.conj y : G →* G) ≤ D
      rw [MonoidHom.map_closure]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨z, hz, rfl⟩
      rcases hz with hz | hz
      · rcases hz with ⟨x, hx, rfl⟩
        have hcy : ⁅y, y₀⁆ ∈ O := by
          have h := hcen y hy y₀ hy₀R
          simpa only [commutatorElement_def] using h
        have h1 : (MulAut.conj y : G →* G) ⁅x, y₀⁆ = ⁅y * x * y⁻¹, y * y₀ * y⁻¹⁆ := by
          change y * ⁅x, y₀⁆ * y⁻¹ = _
          exact conjugate_commutatorElement x y₀ y
        have h2 : y * y₀ * y⁻¹ = ⁅y, y₀⁆ * y₀ := by
          rw [commutatorElement_def]; group
        have h3 : y * x * y⁻¹ ∈ O := hYO y hy x hx
        rw [h1, h2, commutatorElement_mul_right_eq_mul_conj]
        have h5 : ⁅y * x * y⁻¹, ⁅y, y₀⁆⁆ ∈ V := hcomm _ h3 _ hcy
        have h6 : ⁅y, y₀⁆ * ⁅y * x * y⁻¹, y₀⁆ * ⁅y, y₀⁆⁻¹ ∈ D :=
          honorm _ hcy _ (hSD _ h3)
        have hid : ⁅y * x * y⁻¹, ⁅y, y₀⁆⁆ * ⁅y, y₀⁆ * ⁅y * x * y⁻¹, y₀⁆ * ⁅y, y₀⁆⁻¹ =
            ⁅y * x * y⁻¹, ⁅y, y₀⁆⁆ * (⁅y, y₀⁆ * ⁅y * x * y⁻¹, y₀⁆ * ⁅y, y₀⁆⁻¹) := by
          group
        rw [hid]
        exact D.mul_mem (hVD h5) h6
      · exact Subgroup.subset_closure (Or.inr (hYV y hy z hz))
    intro d hd
    have : (MulAut.conj y : G →* G) d = y * d * y⁻¹ := rfl
    rw [← this]
    exact hmap (Subgroup.mem_map_of_mem _ hd)
  have hClat := hlat C hVC hCO hYC
  have hDlat := hlat D hVD hDO hYD
  have hDleC : Nat.card ↥D ≤ Nat.card ↥C := Subgroup.card_le_of_le hCD
  let f : ↥D →* (↥O ⧸ V.subgroupOf O) := q.comp (Subgroup.inclusion hDO)
  have hfker : f.ker = V.subgroupOf D := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : q (Subgroup.inclusion hDO x) = 1 := hx
      simpa [Subgroup.coe_inclusion] using (hq1 _).mp hx'
    · intro hx
      show q (Subgroup.inclusion hDO x) = 1
      exact (hq1 _).mpr (by simpa [Subgroup.coe_inclusion] using hx)
  have hmapD : (D.subgroupOf O).map q = φ.range := by
    have hle : D ≤ (φ.range.comap q).map O.subtype := by
      change closure (S ∪ (V : Set G)) ≤ _
      refine (Subgroup.closure_le _).2 ?_
      rintro z (hz | hz)
      · rcases hz with ⟨x, hx, rfl⟩
        refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩ * (σ ⟨x, hx⟩)⁻¹, ?_, ?_⟩
        · rw [Subgroup.mem_comap]
          exact ⟨⟨x, hx⟩, by rw [map_mul, map_inv]; rfl⟩
        · change ((⟨x, hx⟩ * (σ ⟨x, hx⟩)⁻¹ : ↥O) : G) = ⁅x, y₀⁆
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hσ, commutatorElement_def]
          group
      · exact Subgroup.mem_map.mpr ⟨⟨z, hVO hz⟩, by
            rw [Subgroup.mem_comap, (hq1 ⟨z, hVO hz⟩).mpr hz]
            exact φ.range.one_mem, rfl⟩
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      intro x hx
      have hx' : (x : G) ∈ (φ.range.comap q).map O.subtype := hle (by
        rwa [Subgroup.mem_subgroupOf] at hx)
      rcases Subgroup.mem_map.mp hx' with ⟨w, hw, hwG⟩
      have : w = x := Subtype.ext hwG
      rwa [this] at hw
    · rintro y ⟨x, rfl⟩
      refine Subgroup.mem_map.mpr ⟨x * (σ x)⁻¹, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        have h : ((x * (σ x)⁻¹ : ↥O) : G) = ⁅(x : G), y₀⁆ := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hσ, commutatorElement_def]
          group
        rw [h]
        exact hSD x x.2
      · rw [map_mul, map_inv]
        rfl
  have hfrange : f.range = (D.subgroupOf O).map q := by
    ext y
    constructor
    · rintro ⟨d, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨d.1, hDO d.2⟩, d.2, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      refine ⟨⟨w.1, hw⟩, ?_⟩
      change q (Subgroup.inclusion hDO ⟨w.1, hw⟩) = q w
      have : Subgroup.inclusion hDO ⟨w.1, hw⟩ = w := Subtype.ext rfl
      rw [this]
  have hcardD : Nat.card ↥D = Nat.card ↥V * Nat.card φ.range := by
    have h1 := Subgroup.card_ker_mul_card_range f
    rw [hfker, hfrange, hmapD] at h1
    rw [← h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVD).toEquiv]
  have hrelC : C.relIndex O = Nat.card φ.range := by
    have h1 : C.subgroupOf O = φ.ker := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf] at hx
        rcases Subgroup.mem_map.mp hx with ⟨w, hw, hwG⟩
        have : w = x := Subtype.ext hwG
        rwa [this] at hw
      · intro hx
        rw [Subgroup.mem_subgroupOf]
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    change (C.subgroupOf O).index = Nat.card φ.range
    rw [h1, Subgroup.index_ker]
  have hrelD : V.relIndex D = C.relIndex O := by
    have h1 : V.relIndex D * Nat.card ↥V = Nat.card ↥D := by
      have := Subgroup.relIndex_mul_card (H := V) (K := D)
      rwa [inf_eq_left.mpr hVD] at this
    have h2 : Nat.card ↥V * C.relIndex O = Nat.card ↥D := by
      rw [hrelC]
      exact hcardD.symm
    have h3 : V.relIndex D * Nat.card ↥V = C.relIndex O * Nat.card ↥V := by
      rw [h1, ← h2, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right (by rw [hcardV]; norm_num) h3
  have hprod : Nat.card ↥C * Nat.card ↥D = 2 ^ 14 := by
    have h1 : C.relIndex O * Nat.card ↥C = Nat.card ↥O := by
      have := Subgroup.relIndex_mul_card (H := C) (K := O)
      rwa [inf_eq_left.mpr hCO] at this
    have h2 : V.relIndex D * Nat.card ↥V = Nat.card ↥D := by
      have := Subgroup.relIndex_mul_card (H := V) (K := D)
      rwa [inf_eq_left.mpr hVD] at this
    calc Nat.card ↥C * Nat.card ↥D
        = Nat.card ↥C * (V.relIndex D * Nat.card ↥V) := by rw [h2]
      _ = (C.relIndex O * Nat.card ↥C) * Nat.card ↥V := by rw [hrelD]; ring
      _ = Nat.card ↥O * Nat.card ↥V := by rw [h1]
      _ = 2 ^ 14 := by rw [hcardO, hcardV]; norm_num
  have hDle8 : Nat.card ↥D ≤ 8 := by
    have hClat' : Nat.card ↥C = 4 ∨ Nat.card ↥C = 8 ∨ Nat.card ↥C = 2048 ∨
        Nat.card ↥C = 4096 := by simpa using hClat
    have hDlat' : Nat.card ↥D = 4 ∨ Nat.card ↥D = 8 ∨ Nat.card ↥D = 2048 ∨
        Nat.card ↥D = 4096 := by simpa using hDlat
    have hprod' : Nat.card ↥C * Nat.card ↥D = 16384 := by simpa using hprod
    rcases hClat' with h | h | h | h <;> rcases hDlat' with h' | h' | h' | h' <;>
      rw [h, h'] at hprod' hDleC <;> omega
  let D' : Subgroup G := D ⊔ zpowers (y₀ ^ 2)
  have hy₀2mem : y₀ ^ 2 ∈ D' := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hg2D : (y₀ ^ 2) ^ 2 ∈ D := hVD (hsq (y₀ ^ 2) hy₀2O)
  have hgnorm : ∀ d ∈ D, y₀ ^ 2 * d * (y₀ ^ 2)⁻¹ ∈ D := by
    intro d hd
    have hdO : d ∈ O := hDO hd
    have h1 : ⁅y₀ ^ 2, d⁆ ∈ V := by
      simpa only [commutatorElement_def] using hcomm (y₀ ^ 2) hy₀2O d hdO
    have h2 : y₀ ^ 2 * d * (y₀ ^ 2)⁻¹ = ⁅y₀ ^ 2, d⁆ * d := by
      rw [commutatorElement_def]; group
    rw [h2]
    exact D.mul_mem (hVD h1) hd
  have hgnorm_inv : ∀ d ∈ D, (y₀ ^ 2)⁻¹ * d * (y₀ ^ 2) ∈ D := by
    intro d hd
    have hdO : d ∈ O := hDO hd
    have h1 : ⁅(y₀ ^ 2)⁻¹, d⁆ ∈ V := by
      simpa only [commutatorElement_def] using hcomm (y₀ ^ 2)⁻¹ hy₀2invO d hdO
    have h2 : (y₀ ^ 2)⁻¹ * d * (y₀ ^ 2) = ⁅(y₀ ^ 2)⁻¹, d⁆ * d := by
      rw [commutatorElement_def]; group
    rw [h2]
    exact D.mul_mem (hVD h1) hd
  have hRR : ⁅R, R⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro a haR b hbR
    rcases hcoverL a haR with haO | ⟨o₁, ho₁, rfl⟩
    · rcases hcoverL b hbR with hbO | ⟨o₂, ho₂, rfl⟩
      · rw [commutatorElement_def]
        exact hVD (hcomm a haO b hbO)
      · rw [commutatorElement_mul_right_eq_mul_conj]
        have h1 : y₀ * ⁅a, o₂⁆ * y₀⁻¹ ∈ V := hRV y₀ hy₀R _ (hcomm a haO o₂ ho₂)
        have h2 : ⁅a, y₀⁆ * (y₀ * ⁅a, o₂⁆ * y₀⁻¹) ∈ D :=
          D.mul_mem (hSD a haO) (hVD h1)
        convert h2 using 1
        group
    · rcases hcoverL b hbR with hbO | ⟨o₂, ho₂, rfl⟩
      · rw [commutatorElement_mul_left_eq_conj_mul]
        have h1 : y₀ * ⁅o₁, b⁆ * y₀⁻¹ ∈ V := hRV y₀ hy₀R _ (hcomm o₁ ho₁ b hbO)
        have h2 : ⁅y₀, b⁆ ∈ D := by
          rw [← commutatorElement_inv]
          exact D.inv_mem (hSD b hbO)
        exact D.mul_mem (hVD h1) h2
      · rw [commutatorElement_mul_left_eq_conj_mul]
        have h1 : ⁅o₁, y₀ * o₂⁆ ∈ D := by
          rw [commutatorElement_mul_right_eq_mul_conj]
          have h1a : y₀ * ⁅o₁, o₂⁆ * y₀⁻¹ ∈ V := hRV y₀ hy₀R _ (hcomm o₁ ho₁ o₂ ho₂)
          have h1b : ⁅o₁, y₀⁆ * (y₀ * ⁅o₁, o₂⁆ * y₀⁻¹) ∈ D :=
            D.mul_mem (hSD o₁ ho₁) (hVD h1a)
          convert h1b using 1
          group
        have h2 : ⁅y₀, y₀ * o₂⁆ ∈ D := by
          rw [commutatorElement_mul_right_eq_mul_conj, commutatorElement_self, one_mul,
            ← commutatorElement_inv]
          exact hynorm _ (D.inv_mem (hSD o₂ ho₂))
        exact D.mul_mem (hynorm _ h1) h2
  have hsqD' : closure {x | ∃ y ∈ R, x = y ^ 2} ≤ D' := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨a, haR, rfl⟩
    rcases hcoverR a haR with haO | ⟨o, ho, rfl⟩
    · exact (le_sup_left : D ≤ D') (hVD (hsq a haO))
    · have h1 : o * y₀ * o * y₀⁻¹ ∈ D := by
        have hid : o * y₀ * o * y₀⁻¹ = ⁅o, y₀⁆ * (y₀ * o ^ 2 * y₀⁻¹) := by
          rw [commutatorElement_def]; group
        rw [hid]
        exact D.mul_mem (hSD o ho) (hVD (hRV y₀ hy₀R _ (hsq o ho)))
      have h2 : (o * y₀) ^ 2 = (o * y₀ * o * y₀⁻¹) * y₀ ^ 2 := by
        simp only [pow_two]; group
      rw [h2]
      exact D'.mul_mem ((le_sup_left : D ≤ D') h1) hy₀2mem
  have hPhi_le : Phi2 R ≤ D' := by
    rw [Phi2]
    exact sup_le (hRR.trans (le_sup_left : D ≤ D')) hsqD'
  have hD'eq : D' = closure ((D : Set G) ∪ {y₀ ^ 2}) := by
    apply le_antisymm
    · change D ⊔ zpowers (y₀ ^ 2) ≤ closure ((D : Set G) ∪ {y₀ ^ 2})
      apply sup_le
      · exact fun x hx => Subgroup.subset_closure (Set.subset_union_left hx)
      · apply Subgroup.zpowers_le.2
        exact Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton _))
    · refine (Subgroup.closure_le _).2 ?_
      rintro x (hx | hx)
      · exact (le_sup_left : D ≤ D') hx
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hy₀2mem
  have hred : ∀ b ∈ D', b * (y₀ ^ 2) ∈ D ∨ b ∈ D := by
    intro b hb
    rw [hD'eq] at hb
    induction hb using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hxD | hx
      · exact Or.inr hxD
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Or.inl (by simpa [pow_two] using hg2D)
    | one => exact Or.inr (D.one_mem)
    | mul x z hx hz ihx ihz =>
      rcases ihx with ihx | ihx <;> rcases ihz with ihz | ihz
      · refine Or.inr ?_
        have h : x * z = (x * (y₀ ^ 2)) * ((y₀ ^ 2)⁻¹ * (z * (y₀ ^ 2)) * (y₀ ^ 2)) *
            ((y₀ ^ 2) ^ 2)⁻¹ := by group
        rw [h]
        exact D.mul_mem (D.mul_mem ihx (hgnorm_inv _ ihz)) (D.inv_mem hg2D)
      · refine Or.inl ?_
        have h : (x * z) * (y₀ ^ 2) =
            (x * (y₀ ^ 2)) * ((y₀ ^ 2)⁻¹ * z * (y₀ ^ 2)) := by group
        rw [h]
        exact D.mul_mem ihx (hgnorm_inv z ihz)
      · refine Or.inl ?_
        have h : (x * z) * (y₀ ^ 2) = x * (z * (y₀ ^ 2)) := by group
        rw [h]
        exact D.mul_mem ihx ihz
      · exact Or.inr (D.mul_mem ihx ihz)
    | inv x hx ih =>
      rcases ih with ih | ih
      · refine Or.inl ?_
        have h : x⁻¹ * (y₀ ^ 2) =
            ((y₀ ^ 2) * (x * (y₀ ^ 2))⁻¹ * (y₀ ^ 2)⁻¹) * (y₀ ^ 2) ^ 2 := by group
        rw [h]
        exact D.mul_mem (hgnorm _ (D.inv_mem ih)) hg2D
      · exact Or.inr (D.inv_mem ih)
  have hD'card : Nat.card ↥D' ≤ 2 * Nat.card ↥D := by
    have hdvd : D.relIndex D' ∣ 2 := by
      rw [Subgroup.relIndex_dvd_two_iff]
      refine ⟨y₀ ^ 2, hy₀2mem, ?_⟩
      intro b hb
      exact hred b hb
    have hle : D.relIndex D' ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hle' : D ≤ D' := le_sup_left
    have h1 : D.relIndex D' * Nat.card ↥D = Nat.card ↥D' := by
      have h := Subgroup.relIndex_mul_card (H := D) (K := D')
      rwa [show D ⊓ D' = D from inf_eq_left.mpr hle'] at h
    rw [← h1]
    exact Nat.mul_le_mul_right _ hle
  calc Nat.card ↥(Phi2 R) ≤ Nat.card ↥D' := Subgroup.card_le_of_le hPhi_le
    _ ≤ 2 * Nat.card ↥D := hD'card
    _ ≤ 2 * 8 := by exact Nat.mul_le_mul_left _ hDle8
    _ = 16 := by norm_num

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
