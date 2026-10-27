module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Transfer
public import CFSG.GH74.GLS.Stage1.Thm6.Adapters
public import CFSG.GH74.GLS.Bg.Local.Prop1620
public import CFSG.GH74.GLS.C3.Layer2.L4PartB6
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b

variable {G : Type} [Group G]

theorem exists_conj_involution_mem_sylow [Finite G] {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) {t : G}
    (ht : t * t = 1) : ∃ g : G, g * t * g⁻¹ ∈ S := by
  obtain ⟨S₁, hS₁⟩ := L4.PartB6.exists_sylow_eq_of_isSylowOf_top hS
  have hpg : IsPGroup 2 (Subgroup.zpowers t) := by
    intro z
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 z.2
    refine ⟨1, Subtype.ext ?_⟩
    have h2 : t ^ 2 = 1 := by rw [pow_two]; exact ht
    show (z : G) ^ (2 ^ 1) = 1
    rw [← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h2,
      one_zpow]
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G Q S₁
  refine ⟨c, ?_⟩
  have htQ : t ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers t)
  have : c * t * c⁻¹ ∈ ((c • Q : Sylow 2 G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.inv_apply, mul_assoc] using htQ
  rw [hc, hS₁] at this
  exact this

section Coset

variable {S R : Subgroup G}

theorem comm_mem_R (hRn : ∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R) (hsq : ∀ s ∈ S, s * s ∈ R) {s u : G}
    (hs : s ∈ S) (hu : u ∈ S) : s * u * s⁻¹ * u⁻¹ ∈ R := by
  have h1 : s * u * s * u ∈ R := by
    have := hsq (s * u) (S.mul_mem hs hu)
    simpa [mul_assoc] using this
  have h2 : u⁻¹ * (s * s)⁻¹ * u ∈ R := by
    have := hRn u⁻¹ (S.inv_mem hu) (s * s)⁻¹ (R.inv_mem (hsq s hs))
    simpa using this
  have h3 : (u * u)⁻¹ ∈ R := R.inv_mem (hsq u hu)
  have : s * u * s⁻¹ * u⁻¹ = (s * u * s * u) * ((u⁻¹ * (s * s)⁻¹ * u) * (u * u)⁻¹) := by group
  rw [this]
  exact R.mul_mem h1 (R.mul_mem h2 h3)

@[expose] def Rext (R : Subgroup G) (u : G) (hu : u * u = 1) (hn : ∀ r ∈ R, u * r * u⁻¹ ∈ R) :
    Subgroup G where
  carrier := {g | g ∈ R ∨ g * u ∈ R}
  one_mem' := Or.inl R.one_mem
  mul_mem' := by
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (R.mul_mem ha hb)
    · refine Or.inr ?_
      have : a * b * u = a * (b * u) := by group
      rw [this]; exact R.mul_mem ha hb
    · refine Or.inr ?_
      have h1 : u * b * u⁻¹ ∈ R := hn b hb
      rw [huinv] at h1
      have : a * b * u = (a * u) * (u * b * u) := by
        calc a * b * u = a * (u * u) * b * u := by rw [hu, mul_one]
          _ = (a * u) * (u * b * u) := by group
      rw [this]; exact R.mul_mem ha h1
    · refine Or.inl ?_
      have h1 : u * (b * u) * u⁻¹ ∈ R := hn _ hb
      rw [huinv] at h1
      have : a * b = (a * u) * (u * (b * u) * u) := by
        calc a * b = a * (u * u) * b * (u * u) := by rw [hu, mul_one, mul_one]
          _ = (a * u) * (u * (b * u) * u) := by group
      rw [this]; exact R.mul_mem ha h1
  inv_mem' := by
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
    rintro a (ha | ha)
    · exact Or.inl (R.inv_mem ha)
    · refine Or.inr ?_
      have h1 : u * (a * u)⁻¹ * u⁻¹ ∈ R := hn _ (R.inv_mem ha)
      rw [huinv] at h1
      have : a⁻¹ * u = u * (a * u)⁻¹ * u := by group
      rw [this]; exact h1

theorem mem_Rext {u : G} {hu : u * u = 1} {hn : ∀ r ∈ R, u * r * u⁻¹ ∈ R} {g : G} :
    g ∈ Rext R u hu hn ↔ g ∈ R ∨ g * u ∈ R := Iff.rfl

theorem R_le_Rext {u : G} {hu : u * u = 1} {hn : ∀ r ∈ R, u * r * u⁻¹ ∈ R} :
    R ≤ Rext R u hu hn := fun _ hr => Or.inl hr

theorem u_mem_Rext {u : G} {hu : u * u = 1} {hn : ∀ r ∈ R, u * r * u⁻¹ ∈ R} :
    u ∈ Rext R u hu hn := Or.inr (by rw [hu]; exact R.one_mem)

theorem Rext_le (hRS : R ≤ S) {u : G} (huS : u ∈ S) {hu : u * u = 1}
    {hn : ∀ r ∈ R, u * r * u⁻¹ ∈ R} : Rext R u hu hn ≤ S := by
  rintro g (hg | hg)
  · exact hRS hg
  · have : g = (g * u) * u⁻¹ := by group
    rw [this]
    exact S.mul_mem (hRS hg) (S.inv_mem huS)

theorem Rext_norm (hRn : ∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R) (hsq : ∀ s ∈ S, s * s ∈ R) {u : G}
    (huS : u ∈ S) {hu : u * u = 1} {hn : ∀ r ∈ R, u * r * u⁻¹ ∈ R} :
    ∀ s ∈ S, ∀ q ∈ Rext R u hu hn, s * q * s⁻¹ ∈ Rext R u hu hn := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  intro s hs q hq
  rcases hq with hq | hq
  · exact Or.inl (hRn s hs q hq)
  · refine Or.inr ?_
    have h1 : s * (q * u) * s⁻¹ ∈ R := hRn s hs _ hq
    have h2 : s * u * s⁻¹ * u⁻¹ ∈ R := comm_mem_R hRn hsq hs huS
    rw [huinv] at h2
    have : s * q * s⁻¹ * u = (s * (q * u) * s⁻¹) * (s * u * s⁻¹ * u) := by
      calc s * q * s⁻¹ * u = s * q * (u * u) * s⁻¹ * u := by rw [hu, mul_one]
        _ = (s * (q * u) * s⁻¹) * (s * u * s⁻¹ * u) := by group
    rw [this]
    exact R.mul_mem h1 h2

theorem relIndex_Rext {u : G} (hu1 : u ∉ R) {hu : u * u = 1} {hn : ∀ r ∈ R, u * r * u⁻¹ ∈ R} :
    R.relIndex (Rext R u hu hn) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨u, u_mem_Rext, ?_⟩
  intro b hb
  rcases mem_Rext.1 hb with hb | hb
  · exact Or.inr ⟨hb, fun hbu => hu1 ((Subgroup.mul_mem_cancel_left R hb).1 hbu)⟩
  · exact Or.inl ⟨hb, fun hbR => hu1 ((Subgroup.mul_mem_cancel_left R hbR).1 hb)⟩

theorem inv_mul_mem_of_relIndex_two {N : Subgroup G} (h : N.relIndex S = 2) {a b : G} (ha : a ∈ S)
    (hb : b ∈ S) (ha' : a ∉ N) (hb' : b ∉ N) : a⁻¹ * b ∈ N := by
  have h2 : (N.subgroupOf S).index = 2 := h
  have := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨a, ha⟩ : S)⁻¹) (b := ⟨b, hb⟩)).2 (by
    have e1 : (⟨a, ha⟩ : S)⁻¹ ∉ N.subgroupOf S := by
      intro hh
      exact ha' (N.inv_mem_iff.1 hh)
    have e2 : (⟨b, hb⟩ : S) ∉ N.subgroupOf S := hb'
    exact iff_of_false e1 e2)
  exact this

theorem relIndex_Rext_S (hR4 : R.relIndex S = 4) (hRS : R ≤ S) {u : G} (hu1 : u ∉ R)
    {hu : u * u = 1} {hn : ∀ r ∈ R, u * r * u⁻¹ ∈ R} (huS : u ∈ S) :
    (Rext R u hu hn).relIndex S = 2 := by
  have h1 := Subgroup.relIndex_mul_relIndex R (Rext R u hu hn) S (R_le_Rext (hu := hu) (hn := hn))
    (Rext_le hRS huS (hu := hu) (hn := hn))
  rw [relIndex_Rext hu1, hR4] at h1
  omega

end Coset

open CFSG.GH74.GLS.Stage1.Thm6.Sec13 in
theorem iv2_3_3 [Finite G] (hsimple : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {S R : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hRS : R ≤ S)
    (hRn : ∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R) (hR4 : R.relIndex S = 4)
    (hsq : ∀ s ∈ S, s * s ∈ R)
    (hfree : ∀ u ∈ S, u ∉ R → u * u = 1 → ∀ t ∈ S, t * u ∈ R → t * t = 1 →
      ∃ g : G, g * u * g⁻¹ = t) :
    (∀ t : G, t * t = 1 → t ≠ 1 → ∃ g : G, g * t * g⁻¹ ∈ R) ∨
      ((∀ u ∈ S, u ∉ R → u * u = 1 → ∀ g : G, g * u * g⁻¹ ∉ R) ∧
        (∀ u ∈ S, ∀ v ∈ S, u ∉ R → v ∉ R → u * u = 1 → v * v = 1 →
          ∃ g : G, g * u * g⁻¹ = v) ∧
        ((∀ r ∈ R, r * r = 1) → (∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r) →
          ∀ u ∈ S, ∀ v ∈ S, u ∉ R → v ∉ R → u * u = 1 → v * v = 1 →
            ∃ n ∈ normalizer (R : Set G), n * u * n⁻¹ = v)) := by
  by_cases ha : ∀ t : G, t * t = 1 → t ≠ 1 → ∃ g : G, g * t * g⁻¹ ∈ R
  · exact Or.inl ha
  right
  push Not at ha
  obtain ⟨t₀, ht₀, ht₀1, ht₀R⟩ := ha
  obtain ⟨g₀, hg₀⟩ := exists_conj_involution_mem_sylow hS ht₀
  obtain ⟨t, htdef⟩ : ∃ t : G, t = g₀ * t₀ * g₀⁻¹ := ⟨_, rfl⟩
  have htS : t ∈ S := htdef ▸ hg₀
  have htt : t * t = 1 := by
    rw [htdef]
    calc g₀ * t₀ * g₀⁻¹ * (g₀ * t₀ * g₀⁻¹) = g₀ * (t₀ * t₀) * g₀⁻¹ := by group
      _ = 1 := by rw [ht₀]; group
  have ht1 : t ≠ 1 := by
    intro h1
    apply ht₀1
    have h2 : g₀ * t₀ * g₀⁻¹ = 1 := htdef ▸ h1
    calc t₀ = g₀⁻¹ * (g₀ * t₀ * g₀⁻¹) * g₀ := by group
      _ = 1 := by rw [h2]; group
  have havoid : ∀ h : G, h * t * h⁻¹ ∉ R := by
    intro h hh
    apply ht₀R (h * g₀)
    have : h * g₀ * t₀ * (h * g₀)⁻¹ = h * t * h⁻¹ := by rw [htdef]; group
    rw [this]; exact hh
  have htR : t ∉ R := by
    intro hh
    have := havoid 1
    simp only [one_mul, inv_one, mul_one] at this
    exact this hh
  have hconj : ∀ u ∈ S, u ∉ R → u * u = 1 → ∃ h : G, h * t * h⁻¹ = u := by
    intro u huS huR huu
    by_cases hut : u * t ∈ R
    · exact hfree t htS htR htt u huS hut huu
    · have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
      have hn : ∀ r ∈ R, u * r * u⁻¹ ∈ R := fun r hr => hRn u huS r hr
      have hNS : Rext R u huu hn ≤ S := Rext_le hRS huS
      have hNnorm : ∀ s ∈ S, ∀ q ∈ Rext R u huu hn, s * q * s⁻¹ ∈ Rext R u huu hn :=
        Rext_norm hRn hsq huS
      have hidx : (Rext R u huu hn).relIndex S = 2 := relIndex_Rext_S hR4 hRS huR huS
      have htN : t ∉ Rext R u huu hn := by
        intro h
        rcases mem_Rext.1 h with h | h
        · exact htR h
        · apply hut
          have h' := R.inv_mem h
          rwa [mul_inv_rev, huinv, htinv] at h'
      have hne : Rext R u huu hn ≠ S := fun h => htN (h ▸ htS)
      have hcyc : ∃ b ∈ S, ∀ s ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ Rext R u huu hn := by
        refine ⟨t, htS, fun s hs => ?_⟩
        by_cases hsN : s ∈ Rext R u huu hn
        · exact ⟨0, by simpa using hsN⟩
        · exact ⟨1, by simpa using inv_mul_mem_of_relIndex_two hidx htS hs htN hsN⟩
      have hord : ∀ v ∈ S, v ∉ Rext R u huu hn → orderOf t ≤ orderOf v := by
        intro v hvS hvN
        have h1 : v ≠ 1 := fun h => hvN (h ▸ (Rext R u huu hn).one_mem)
        have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
        rw [ht2]
        have h3 : orderOf v ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
        have h4 := orderOf_pos v
        omega
      have hext : ∀ y ∈ S, (∃ g : G, g⁻¹ * t * g = y) → IsExtremal S y →
          y ∈ Rext R u huu hn ∨ t⁻¹ * y ∈ Rext R u huu hn := by
        intro y hyS _ _
        by_cases hyN : y ∈ Rext R u huu hn
        · exact Or.inl hyN
        · exact Or.inr (inv_mul_mem_of_relIndex_two hidx htS hyS htN hyN)
      have hS' : IsSylow2In S ⊤ := isSylowOf_iff.1 hS
      obtain ⟨g, hgN, -⟩ := transfer_conj ig_15_15 hsimple hnab hS' hNS hNnorm hne hcyc htS htN
        hord hext
      have ht'S : g⁻¹ * t * g ∈ S := hNS hgN
      have ht'R : g⁻¹ * t * g ∉ R := by
        have := havoid g⁻¹
        rwa [inv_inv] at this
      have ht'u : g⁻¹ * t * g * u ∈ R := (mem_Rext.1 hgN).resolve_left ht'R
      have ht't' : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
        calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
          _ = 1 := by rw [htt]; group
      obtain ⟨g', hg'⟩ := hfree u huS huR huu _ ht'S ht'u ht't'
      refine ⟨(g * g')⁻¹, ?_⟩
      calc (g * g')⁻¹ * t * ((g * g')⁻¹)⁻¹ = g'⁻¹ * (g⁻¹ * t * g) * g' := by group
        _ = g'⁻¹ * (g' * u * g'⁻¹) * g' := by rw [hg']
        _ = u := by group
  refine ⟨?_, ?_, ?_⟩
  · intro u huS huR huu g hg
    obtain ⟨h, hh⟩ := hconj u huS huR huu
    apply havoid (g * h)
    have : g * h * t * (g * h)⁻¹ = g * (h * t * h⁻¹) * g⁻¹ := by group
    rw [this, hh]; exact hg
  · intro u hu v hv huR hvR huu hvv
    obtain ⟨h, hh⟩ := hconj u hu huR huu
    obtain ⟨h', hh'⟩ := hconj v hv hvR hvv
    refine ⟨h' * h⁻¹, ?_⟩
    calc h' * h⁻¹ * u * (h' * h⁻¹)⁻¹ = h' * (h⁻¹ * u * h) * h'⁻¹ := by group
      _ = h' * t * h'⁻¹ := by rw [← hh]; group
      _ = v := hh'
  · intro hRsq hRab u hu v hv huR hvR huu hvv
    have hclosed : ∀ a ∈ R, ∀ g : G, g * a * g⁻¹ ∈ S → g * a * g⁻¹ ∈ R := by
      intro a ha g hg
      by_contra hnot
      have hvv : g * a * g⁻¹ * (g * a * g⁻¹) = 1 := by
        calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
          _ = 1 := by rw [hRsq a ha]; group
      obtain ⟨h, hh⟩ := hconj _ hg hnot hvv
      apply havoid (g⁻¹ * h)
      have : g⁻¹ * h * t * (g⁻¹ * h)⁻¹ = g⁻¹ * (h * t * h⁻¹) * g := by group
      rw [this, hh]
      have : g⁻¹ * (g * a * g⁻¹) * g = a := by group
      rw [this]; exact ha
    have hS2 : Sylow2In S ⊤ := isSylowOf_iff.1 hS
    obtain ⟨g, hg⟩ : ∃ g : G, g * u * g⁻¹ = v := by
      obtain ⟨h, hh⟩ := hconj u hu huR huu
      obtain ⟨h', hh'⟩ := hconj v hv hvR hvv
      refine ⟨h' * h⁻¹, ?_⟩
      calc h' * h⁻¹ * u * (h' * h⁻¹)⁻¹ = h' * (h⁻¹ * u * h) * h'⁻¹ := by group
        _ = h' * t * h'⁻¹ := by rw [← hh]; group
        _ = v := hh'
    obtain ⟨n, hn, hnu⟩ := CFSG.GH74.GLS.Bg.ig_16_20 G S R hS2 hRS hRab hclosed u hu g (hg ▸ hv)
    exact ⟨n, hn, hnu.trans hg⟩

end CFSG.GH74.GLS.C3.Layer2.L5
