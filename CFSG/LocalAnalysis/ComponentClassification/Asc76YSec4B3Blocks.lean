module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D18

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

theorem perm_three_conj_eq_third (σ τ ρ : Equiv.Perm (Fin 3)) (h1 : σ ≠ 1) (h2 : σ * σ = 1)
    (h3 : τ ≠ 1) (h4 : τ * τ = 1) (h5 : ρ ≠ 1) (h6 : ρ * ρ = 1) (h7 : σ ≠ τ) (h8 : ρ ≠ σ)
    (h9 : ρ ≠ τ) : τ * σ * τ = ρ := by
  have key : ∀ σ τ ρ : Equiv.Perm (Fin 3), σ = 1 ∨ σ * σ ≠ 1 ∨ τ = 1 ∨ τ * τ ≠ 1 ∨ ρ = 1 ∨
      ρ * ρ ≠ 1 ∨ σ = τ ∨ ρ = σ ∨ ρ = τ ∨ τ * σ * τ = ρ := by decide
  rcases key σ τ ρ with h | h | h | h | h | h | h | h | h | h
  · exact absurd h h1
  · exact absurd h2 h
  · exact absurd h h3
  · exact absurd h4 h
  · exact absurd h h5
  · exact absurd h6 h
  · exact absurd h h7
  · exact absurd h h8
  · exact absurd h h9
  · exact h

theorem perm_three_conj_conj (σ δ : Equiv.Perm (Fin 3)) (h1 : σ ≠ 1) (h2 : σ * σ = 1)
    (h3 : δ ≠ 1) (h4 : δ * δ = 1) (h5 : σ ≠ δ) : δ * (σ * δ * σ) * δ = σ := by
  have key : ∀ σ δ : Equiv.Perm (Fin 3), σ = 1 ∨ σ * σ ≠ 1 ∨ δ = 1 ∨ δ * δ ≠ 1 ∨ σ = δ ∨
      δ * (σ * δ * σ) * δ = σ := by decide
  rcases key σ δ with h | h | h | h | h | h
  · exact absurd h h1
  · exact absurd h2 h
  · exact absurd h h3
  · exact absurd h4 h
  · exact absurd h h5
  · exact h

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {S : Subgroup G}

theorem DBar.conj_mem' (hΩ : Assumption41 Ω) (hS : IsSylowOf 2 S ⊤)
    {d e : NBar (sec4W Ω S)} (hd : d ∈ DBar Ω (sec4W Ω S)) (he : e ∈ DBar Ω (sec4W Ω S)) :
    e * d * e ∈ DBar Ω (sec4W Ω S) := by
  have h := DBar.conj_mem hΩ hd e
  rwa [inv_eq_of_mul_eq_one_right (DBar.mul_self hΩ hS he)] at h

theorem DBar.braid (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) {d e : NBar (sec4W Ω S)}
    (hd : d ∈ DBar Ω (sec4W Ω S)) (he : e ∈ DBar Ω (sec4W Ω S)) (hne : d * e ≠ e * d) :
    d * e * d = e * d * e := by
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right (DBar.mul_self H.hΩ hS hd)
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right (DBar.mul_self H.hΩ hS he)
  have h3 := DBar.orderOf_mul_le_three H.h22 H.hΩ H.hnil hS hd he
  have hpos : 0 < orderOf (d * e) := orderOf_pos (d * e)
  have hpow := pow_orderOf_eq_one (d * e)
  interval_cases h : orderOf (d * e)
  · exfalso
    apply hne
    rw [pow_one, mul_eq_one_iff_eq_inv, heinv] at hpow
    rw [hpow]
  · exfalso
    apply hne
    rw [pow_two, mul_eq_one_iff_eq_inv, mul_inv_rev, hdinv, heinv] at hpow
    exact hpow
  · have e1 : (d * e * d) * (e * d * e) = 1 := by
      rw [← hpow, pow_three]
      group
    rw [mul_eq_one_iff_eq_inv] at e1
    rw [e1]
    simp only [mul_inv_rev, hdinv, heinv, mul_assoc]

theorem DBar.exists_blockMap (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) (hΩne : Ω.Nonempty)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected) :
    ∃ ψ : NBar (sec4W Ω S) → Equiv.Perm (Fin 3),
      (∀ d ∈ DBar Ω (sec4W Ω S), ∀ e ∈ DBar Ω (sec4W Ω S), ψ (e * d * e) = ψ e * ψ d * ψ e) ∧
      (∀ d ∈ DBar Ω (sec4W Ω S), ψ d ≠ 1 ∧ ψ d * ψ d = 1) ∧
      ∀ d ∈ DBar Ω (sec4W Ω S), ∀ e ∈ DBar Ω (sec4W Ω S), (d * e = e * d ↔ ψ d = ψ e) := by
  classical
  obtain ⟨φ, -, -, hφ1, hcomm, -⟩ := DBar.exists_hom_perm_three H hS hΩne hdis
  refine ⟨fun x => if h : x ∈ MBar Ω (sec4W Ω S) then φ ⟨x, h⟩ else 1, ?_, ?_, ?_⟩
  · intro d hd e he
    have hd' : d ∈ MBar Ω (sec4W Ω S) := subset_closure hd
    have he' : e ∈ MBar Ω (sec4W Ω S) := subset_closure he
    have hede : e * d * e ∈ MBar Ω (sec4W Ω S) := mul_mem (mul_mem he' hd') he'
    simp only [hd', he', hede, ↓reduceDIte]
    rw [← map_mul, ← map_mul]
    rfl
  · intro d hd
    have hd' : d ∈ MBar Ω (sec4W Ω S) := subset_closure hd
    simp only [hd', ↓reduceDIte]
    exact hφ1 ⟨d, hd'⟩ hd
  · intro d hd e he
    have hd' : d ∈ MBar Ω (sec4W Ω S) := subset_closure hd
    have he' : e ∈ MBar Ω (sec4W Ω S) := subset_closure he
    simp only [hd', he', ↓reduceDIte]
    rw [← hcomm ⟨d, hd'⟩ ⟨e, he'⟩ hd he, Subtype.ext_iff]
    rfl

theorem DBar.commute_of_three (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) (hΩne : Ω.Nonempty)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {d e f : NBar (sec4W Ω S)} (hd : d ∈ DBar Ω (sec4W Ω S)) (he : e ∈ DBar Ω (sec4W Ω S))
    (hf : f ∈ DBar Ω (sec4W Ω S)) (hde : d * e ≠ e * d) (hfd : f * d ≠ d * f)
    (hfe : f * e ≠ e * f) : f * (e * d * e) = (e * d * e) * f := by
  obtain ⟨ψ, hψ, hψ1, hψc⟩ := DBar.exists_blockMap H hS hΩne hdis
  rw [hψc f hf _ (DBar.conj_mem' H.hΩ hS hd he), hψ d hd e he]
  exact (perm_three_conj_eq_third (ψ d) (ψ e) (ψ f) (hψ1 d hd).1 (hψ1 d hd).2 (hψ1 e he).1
    (hψ1 e he).2 (hψ1 f hf).1 (hψ1 f hf).2 (fun h => hde ((hψc d hd e he).mpr h))
    (fun h => hfd ((hψc f hf d hd).mpr h)) (fun h => hfe ((hψc f hf e he).mpr h))).symm

omit [Finite G] in
theorem DBar.exists_not_commute {W : Subgroup G}
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω W)).Connected) {d : NBar W}
    (hd : d ∈ DBar Ω W) : ∃ e ∈ DBar Ω W, d * e ≠ e * d := by
  by_contra hcon
  push Not at hcon
  apply hdis
  refine (SimpleGraph.connected_iff_exists_forall_reachable _).2 ⟨⟨d, hd⟩, fun v => ?_⟩
  exact CFSG.Fischer.commGraph_reachable_of_commute (hcon v v.2)

theorem DBar.eq_of_conj_eq (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) {d₀ x y : NBar (sec4W Ω S)}
    (hd₀ : d₀ ∈ DBar Ω (sec4W Ω S)) (hx : x ∈ DBar Ω (sec4W Ω S))
    (hy : y ∈ DBar Ω (sec4W Ω S)) (hxd : x * d₀ ≠ d₀ * x) (hyd : y * d₀ ≠ d₀ * y)
    (h : x * d₀ * x = y * d₀ * y) : x = y := by
  rw [DBar.braid H hS hx hd₀ hxd, DBar.braid H hS hy hd₀ hyd] at h
  have h1 : d₀ * x = d₀ * y := mul_right_cancel h
  exact mul_left_cancel h1

theorem DBar.exists_fourth (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) (hΩne : Ω.Nonempty)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {r d₀ a b c : NBar (sec4W Ω S)} (hr : r ∈ DBar Ω (sec4W Ω S))
    (hd₀ : d₀ ∈ DBar Ω (sec4W Ω S)) (ha : a ∈ DBar Ω (sec4W Ω S))
    (hb : b ∈ DBar Ω (sec4W Ω S)) (hc : c ∈ DBar Ω (sec4W Ω S)) (hrd : d₀ * r ≠ r * d₀)
    (har : a * r = r * a) (hbr : b * r = r * b) (hcr : c * r = r * c) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ τ ∈ DBar Ω (sec4W Ω S), τ * r = r * τ ∧ τ ≠ a ∧ τ ≠ b ∧ τ ≠ c ∧
      (b * c * a * τ)⁻¹ * d₀ * (b * c * a * τ) = d₀ := by
  obtain ⟨ψ, hψ, hψ1, hψc⟩ := DBar.exists_blockMap H hS hΩne hdis
  have hΩ := H.hΩ
  have hdd : ∀ {x : NBar (sec4W Ω S)}, x ∈ DBar Ω (sec4W Ω S) → x * x = 1 :=
    fun hx => DBar.mul_self hΩ hS hx
  have hinv : ∀ {x : NBar (sec4W Ω S)}, x ∈ DBar Ω (sec4W Ω S) → x⁻¹ = x :=
    fun hx => inv_eq_of_mul_eq_one_right (hdd hx)
  have hψa : ψ a = ψ r := (hψc a ha r hr).mp har
  have hψb : ψ b = ψ r := (hψc b hb r hr).mp hbr
  have hψcc : ψ c = ψ r := (hψc c hc r hr).mp hcr
  have hσδ : ψ r ≠ ψ d₀ := fun h => hrd ((hψc d₀ hd₀ r hr).mpr h.symm)
  have hnc : ∀ {x : NBar (sec4W Ω S)}, x ∈ DBar Ω (sec4W Ω S) → x * r = r * x →
      x * d₀ ≠ d₀ * x := by
    intro x hx hxr h
    apply hrd
    have h1 := DBar.commute_trans H hS hΩne hdis hd₀ hx hr h.symm hxr
    exact h1
  obtain ⟨f, hf⟩ : ∃ f, f = c * (b * d₀ * b) * c := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p = a * d₀ * a := ⟨_, rfl⟩
  have hbd : b * d₀ * b ∈ DBar Ω (sec4W Ω S) := DBar.conj_mem' hΩ hS hd₀ hb
  have hfD : f ∈ DBar Ω (sec4W Ω S) := hf ▸ DBar.conj_mem' hΩ hS hbd hc
  have hpD : p ∈ DBar Ω (sec4W Ω S) := hp ▸ DBar.conj_mem' hΩ hS hd₀ ha
  have hψf : ψ f = ψ d₀ := by
    rw [hf, hψ _ hbd c hc, hψ d₀ hd₀ b hb, hψb, hψcc]
    have h2 := (hψ1 r hr).2
    calc ψ r * (ψ r * ψ d₀ * ψ r) * ψ r = (ψ r * ψ r) * ψ d₀ * (ψ r * ψ r) := by group
      _ = ψ d₀ := by rw [h2, one_mul, mul_one]
  have hψp : ψ p = ψ r * ψ d₀ * ψ r := by rw [hp, hψ d₀ hd₀ a ha, hψa]
  have hfp : f * p ≠ p * f := by
    intro h
    have h1 := (hψc f hfD p hpD).mp h
    rw [hψf, hψp] at h1
    exact perm_three_conj_ne (ψ d₀) (ψ r) (hψ1 d₀ hd₀).1 (hψ1 d₀ hd₀).2 (hψ1 r hr).1
      (hψ1 r hr).2 hσδ.symm h1.symm
  have hbraid : f * p * f = p * f * p := DBar.braid H hS hfD hpD hfp
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = f * p * f := ⟨_, rfl⟩
  have hτD : τ ∈ DBar Ω (sec4W Ω S) := hτ ▸ DBar.conj_mem' hΩ hS hpD hfD
  have hψτ : ψ τ = ψ r := by
    rw [hτ, hψ p hpD f hfD, hψf, hψp]
    exact perm_three_conj_conj (ψ r) (ψ d₀) (hψ1 r hr).1 (hψ1 r hr).2 (hψ1 d₀ hd₀).1
      (hψ1 d₀ hd₀).2 hσδ
  have hτr : τ * r = r * τ := (hψc τ hτD r hr).mpr hψτ
  have hτpτ : τ * p * τ = f := by
    have hpp := hdd hpD
    have hff := hdd hfD
    calc τ * p * τ = (f * p * f) * p * (f * p * f) := by rw [hτ]
      _ = (p * f * p) * p * (p * f * p) := by rw [hbraid]
      _ = p * (f * p * f) * p := by
          rw [show (p * f * p) * p * (p * f * p) = p * f * (p * p) * (p * f * p) by group,
            hpp, mul_one]
          group
      _ = p * (p * f * p) * p := by rw [hbraid]
      _ = f := by
          rw [show p * (p * f * p) * p = (p * p) * f * (p * p) by group, hpp, one_mul,
            mul_one]
  have hcomm : ∀ {x y : NBar (sec4W Ω S)}, x ∈ DBar Ω (sec4W Ω S) →
      y ∈ DBar Ω (sec4W Ω S) → x * r = r * x → y * r = r * y → x * y = y * x :=
    fun hx hy hxr hyr => DBar.commute_trans H hS hΩne hdis hx hr hy hxr hyr.symm
  have haτ : a * τ = τ * a := hcomm ha hτD har hτr
  have hbc' : b * c = c * b := hcomm hb hc hbr hcr
  have hτa : τ ≠ a := by
    intro h
    apply hbc
    apply DBar.eq_of_conj_eq H hS hd₀ hb hc (hnc hb hbr) (hnc hc hcr)
    have h1 : f = d₀ := by
      rw [← hτpτ, h, hp]
      rw [show a * (a * d₀ * a) * a = (a * a) * d₀ * (a * a) by group, hdd ha, one_mul,
        mul_one]
    have h2 : c * (c * (b * d₀ * b) * c) * c = c * d₀ * c := by rw [← hf, h1]
    rw [show c * (c * (b * d₀ * b) * c) * c = (c * c) * (b * d₀ * b) * (c * c) by group,
      hdd hc, one_mul, mul_one] at h2
    exact h2
  have hτb : τ ≠ b := by
    intro h
    apply hac
    apply DBar.eq_of_conj_eq H hS hd₀ ha hc (hnc ha har) (hnc hc hcr)
    have h1 : b * p * b = f := by rw [← h, hτpτ]
    have h2 : b * (b * p * b) * b = b * f * b := by rw [h1]
    rw [show b * (b * p * b) * b = (b * b) * p * (b * b) by group, hdd hb, one_mul,
      mul_one] at h2
    have hbcb : b * c * b = c := by rw [hbc', mul_assoc, hdd hb, mul_one]
    rw [← hp, h2, hf]
    calc b * (c * (b * d₀ * b) * c) * b = (b * c * b) * d₀ * (b * c * b) := by group
      _ = c * d₀ * c := by rw [hbcb]
  have hτc : τ ≠ c := by
    intro h
    apply hab
    apply DBar.eq_of_conj_eq H hS hd₀ ha hb (hnc ha har) (hnc hb hbr)
    have h1 : c * p * c = f := by rw [← h, hτpτ]
    have h2 : c * (c * p * c) * c = c * f * c := by rw [h1]
    rw [show c * (c * p * c) * c = (c * c) * p * (c * c) by group, hdd hc, one_mul,
      mul_one] at h2
    rw [← hp, h2, hf, show c * (c * (b * d₀ * b) * c) * c = (c * c) * (b * d₀ * b) * (c * c) by
      group, hdd hc, one_mul, mul_one]
  refine ⟨τ, hτD, hτr, hτa, hτb, hτc, ?_⟩
  have e1 : (b * c * a * τ)⁻¹ * d₀ * (b * c * a * τ) = τ * a * f * a * τ := by
    rw [hf]
    simp only [mul_inv_rev, hinv hτD, hinv ha, hinv hb, hinv hc]
    group
  rw [e1, ← hτpτ, hp]
  have hτa' : τ * a * τ * a = 1 := by
    rw [mul_assoc τ a τ, haτ, ← mul_assoc, hdd hτD, one_mul, hdd ha]
  have hτa'' : a * τ * a * τ = 1 := by
    rw [mul_assoc a τ a, ← haτ, ← mul_assoc, hdd ha, one_mul, hdd hτD]
  calc τ * a * (τ * (a * d₀ * a) * τ) * a * τ = (τ * a * τ * a) * d₀ * (a * τ * a * τ) := by
        group
    _ = d₀ := by rw [hτa', hτa'', one_mul, mul_one]

theorem conj_conj_eq_of_braid {X : Type*} [Group X] {f p : X} (hp : p * p = 1)
    (hbr : f * p * f = p * f * p) : (f * p * f) * p * (f * p * f) = f := by
  calc (f * p * f) * p * (f * p * f) = (p * f * p) * p * (p * f * p) := by rw [hbr]
    _ = p * f * (p * p) * (p * f * p) := by group
    _ = p * (f * p * f) * p := by rw [hp, mul_one]; group
    _ = p * (p * f * p) * p := by rw [hbr]
    _ = (p * p) * f * (p * p) := by group
    _ = f := by rw [hp, one_mul, mul_one]

theorem DBar.conj_eq_of_third (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) (hΩne : Ω.Nonempty)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {r d₀ f : NBar (sec4W Ω S)} (hr : r ∈ DBar Ω (sec4W Ω S)) (hd₀ : d₀ ∈ DBar Ω (sec4W Ω S))
    (hf : f ∈ DBar Ω (sec4W Ω S)) (hrd : d₀ * r ≠ r * d₀) (hfr : f * r ≠ r * f)
    (hfd : f * d₀ ≠ d₀ * f) :
    d₀ * f * d₀ ∈ DBar Ω (sec4W Ω S) ∧ (d₀ * f * d₀) * r = r * (d₀ * f * d₀) ∧
      (d₀ * f * d₀)⁻¹ * d₀ * (d₀ * f * d₀) = f := by
  have hd2 := DBar.mul_self H.hΩ hS hd₀
  have hf2 := DBar.mul_self H.hΩ hS hf
  have hdinv : d₀⁻¹ = d₀ := inv_eq_of_mul_eq_one_right hd2
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf2
  refine ⟨DBar.conj_mem' H.hΩ hS hf hd₀, (DBar.commute_of_three H hS hΩne hdis hf hd₀ hr hfd
    (fun h => hfr h.symm) (fun h => hrd h.symm)).symm, ?_⟩
  have hbr := DBar.braid H hS hf hd₀ hfd
  calc (d₀ * f * d₀)⁻¹ * d₀ * (d₀ * f * d₀) = d₀ * f * (d₀ * d₀) * d₀ * f * d₀ := by
        rw [mul_inv_rev, mul_inv_rev, hdinv, hfinv]; group
    _ = d₀ * (f * d₀ * f) * d₀ := by rw [hd2, mul_one]; group
    _ = f := by rw [hbr, show d₀ * (d₀ * f * d₀) * d₀ = (d₀ * d₀) * f * (d₀ * d₀) by group, hd2,
          one_mul, mul_one]

theorem DBar.conj_eq_of_second (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) (hΩne : Ω.Nonempty)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {r d₀ f : NBar (sec4W Ω S)} (hr : r ∈ DBar Ω (sec4W Ω S)) (hd₀ : d₀ ∈ DBar Ω (sec4W Ω S))
    (hf : f ∈ DBar Ω (sec4W Ω S)) (hrd : d₀ * r ≠ r * d₀) (hfd : f * d₀ = d₀ * f) :
    f * (r * d₀ * r) * f ∈ DBar Ω (sec4W Ω S) ∧
      (f * (r * d₀ * r) * f) * r = r * (f * (r * d₀ * r) * f) ∧
      (r * (f * (r * d₀ * r) * f))⁻¹ * d₀ * (r * (f * (r * d₀ * r) * f)) = f := by
  have hr2 := DBar.mul_self H.hΩ hS hr
  have hd2 := DBar.mul_self H.hΩ hS hd₀
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  obtain ⟨p, hp⟩ : ∃ p, p = r * d₀ * r := ⟨_, rfl⟩
  rw [← hp]
  have hpD : p ∈ DBar Ω (sec4W Ω S) := hp ▸ DBar.conj_mem' H.hΩ hS hd₀ hr
  have hp2 := DBar.mul_self H.hΩ hS hpD
  have hpinv : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp2
  have hpr : p * r ≠ r * p := by
    intro h
    apply hrd
    rw [hp] at h
    have e1 : r * d₀ * r * r = r * d₀ := by rw [mul_assoc, hr2, mul_one]
    have e2 : r * (r * d₀ * r) = d₀ * r := by rw [← mul_assoc, ← mul_assoc, hr2, one_mul]
    rw [e1, e2] at h
    exact h.symm
  have hpd : p * d₀ ≠ d₀ * p := by
    intro h
    apply hrd
    have hbr := DBar.braid H hS hr hd₀ (fun h' => hrd h'.symm)
    rw [hp, hbr] at h
    have e1 : d₀ * r * d₀ * d₀ = d₀ * r := by rw [mul_assoc, hd2, mul_one]
    have e2 : d₀ * (d₀ * r * d₀) = r * d₀ := by rw [← mul_assoc, ← mul_assoc, hd2, one_mul]
    rw [e1, e2] at h
    exact h
  have hfr : f * r ≠ r * f := fun h => hrd (DBar.commute_trans H hS hΩne hdis hd₀ hf hr hfd.symm h)
  have hfp : f * p ≠ p * f := fun h => hpd (DBar.commute_trans H hS hΩne hdis hpD hf hd₀ h.symm hfd)
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right (DBar.mul_self H.hΩ hS hf)
  refine ⟨DBar.conj_mem' H.hΩ hS hpD hf, (DBar.commute_of_three H hS hΩne hdis hpD hf hr
    (fun h => hfp h.symm) (fun h => hpr h.symm) (fun h => hfr h.symm)).symm, ?_⟩
  have hbr := DBar.braid H hS hf hpD hfp
  calc (r * (f * p * f))⁻¹ * d₀ * (r * (f * p * f))
      = (f * p * f) * (r * d₀ * r) * (f * p * f) := by
        simp only [mul_inv_rev, hpinv, hrinv, hfinv]; group
    _ = f := by rw [← hp]; exact conj_conj_eq_of_braid hp2 hbr

end CFSG.ComponentClassification.Asc76.Sec4
