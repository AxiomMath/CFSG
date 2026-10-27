module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S4Act
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S4Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.Wreath

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath
open scoped commutatorElement

section TAct

variable {C : Type*} [Group C]

theorem t_comm_mem_actKer {O Y : Subgroup C} (hY : Y ≤ center C)
    (hO : ∀ c : C, ∀ o ∈ O, c * o * c⁻¹ ∈ O) {t : C} (htt : t * t = 1)
    (hOinv : ∀ o ∈ O, t * o * t⁻¹ * o ∈ Y) (c : C) :
    t * c * t⁻¹ * c⁻¹ ∈ actKer O Y hY := by
  intro o ho
  have : Y.Normal := ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.1 (hY hn) g
    rw [this, mul_inv_cancel_right]; exact hn⟩
  let q : C →* C ⧸ Y := QuotientGroup.mk' Y
  rw [← QuotientGroup.eq_one_iff]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hq : ∀ x ∈ O, q t * q x * q t = (q x)⁻¹ := by
    intro x hx
    have h1 := hOinv x hx
    have h2 : q (t * x * t⁻¹ * x) = 1 := (QuotientGroup.eq_one_iff _).2 h1
    rw [htinv] at h2
    simp only [map_mul] at h2
    exact eq_inv_of_mul_eq_one_left h2
  have htq : (q t)⁻¹ = q t := by rw [← map_inv, htinv]
  have h1 := hq o ho
  have h2 := hq (c⁻¹ * o * c) (by simpa using hO c⁻¹ o ho)
  simp only [map_mul, map_inv] at h2
  show q ⁅t * c * t⁻¹ * c⁻¹, o⁆ = 1
  rw [commutatorElement_def, htinv]
  simp only [map_mul, map_inv]
  calc q t * q c * q t * (q c)⁻¹ * q o * (q t * q c * q t * (q c)⁻¹)⁻¹ * (q o)⁻¹
      = q t * q c * (q t * ((q c)⁻¹ * q o * q c) * q t) * (q c)⁻¹ * q t * (q o)⁻¹ := by
        rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, htq, inv_inv]
        group
    _ = q t * q c * ((q c)⁻¹ * q o * q c)⁻¹ * (q c)⁻¹ * q t * (q o)⁻¹ := by rw [h2]
    _ = q t * (q o)⁻¹ * q t * (q o)⁻¹ := by group
    _ = (q t * q o * q t)⁻¹ * (q o)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, htq]
      group
    _ = 1 := by rw [h1]; group

end TAct

section Beta

@[expose] def betaHom : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →*
    Wr2 (Equiv.Perm (Fin 5)) :=
  (SemidirectProduct.inl : (Equiv.Perm (Fin 5)) × (Equiv.Perm (Fin 5)) →* _).comp
    (MonoidHom.prodMap (alternatingGroup (Fin 5)).subtype (alternatingGroup (Fin 5)).subtype)

theorem betaHom_apply (a b : alternatingGroup (Fin 5)) :
    betaHom (a, b) = base (a : Equiv.Perm (Fin 5)) (b : Equiv.Perm (Fin 5)) := rfl

theorem betaHom_injective : Function.Injective betaHom := by
  intro x y h
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  rw [betaHom_apply, betaHom_apply, base_injective] at h
  exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)

theorem tau_betaHom (x : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :
    tau * betaHom x * tau⁻¹ = betaHom x.swap := by
  obtain ⟨a, b⟩ := x
  rw [betaHom_apply, tau_inv, tau_mul_base, mul_assoc, tau_mul_tau, mul_one]
  rfl

theorem commutator_alt_five_prod :
    ⁅(⊤ : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))),
      (⊤ : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)))⁆ = ⊤ := by
  have hA : ⁅(⊤ : Subgroup (alternatingGroup (Fin 5))), (⊤ : Subgroup (alternatingGroup (Fin 5)))⁆ =
      ⊤ := by
    have := commutator_alternatingGroup_eq_top (α := Fin 5) (by simp)
    rwa [commutator_def] at this
  have := commutator_prod_prod (H₁ := (⊤ : Subgroup (alternatingGroup (Fin 5))))
    (H₂ := (⊤ : Subgroup (alternatingGroup (Fin 5))))
    (⊤ : Subgroup (alternatingGroup (Fin 5))) (⊤ : Subgroup (alternatingGroup (Fin 5)))
  rw [hA, Subgroup.top_prod_top] at this
  exact this

end Beta

section Perf

variable {C K H : Type*} [Group C] [Group K] [Group H]

theorem map_comap_commutator (f : C →* H) (B : Subgroup H) (hB : B ≤ f.range)
    (hperf : ⁅B, B⁆ = B) : (⁅B.comap f, B.comap f⁆).map f = B := by
  have h : (B.comap f).map f = B := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hB
  rw [map_commutator, h, hperf]

theorem commutator_range_eq (hK : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤) (β : K →* H) :
    ⁅β.range, β.range⁆ = β.range := by
  rw [MonoidHom.range_eq_map, ← map_commutator, hK]

end Perf

section Core

theorem s4_core {C : Type} [Group C] [Finite C]
    (O Y : Subgroup C) [O.Normal] (hOodd : Odd (Nat.card O)) (hYc : Y ≤ center C)
    (hOcomm : ∀ o₁ ∈ O, ∀ o₂ ∈ O, ⁅o₁, o₂⁆ ∈ Y) {t : C} (htt : t * t = 1)
    (hOinv : ∀ o ∈ O, t * o * t⁻¹ * o ∈ Y) (f : C →* Wr2 (Equiv.Perm (Fin 5)))
    (hker : ∀ g, f g = 1 ↔ g ∈ O) (ht : f t = tau)
    (hbase : ∀ x : alternatingGroup (Fin 5) × alternatingGroup (Fin 5), ∃ g, f g = betaHom x) :
    ∃ R : Subgroup C, (∀ r ∈ R, ∀ o ∈ O, r * o = o * r) ∧ (∀ r ∈ R, t * r * t⁻¹ ∈ R) ∧
      (∀ r ∈ R, r ∈ O → r = 1) ∧ (∀ r ∈ R, ∃ x, f r = betaHom x) ∧
      (∀ x, ∃ r ∈ R, f r = betaHom x) := by
  have hOC : ∀ c : C, ∀ o ∈ O, c * o * c⁻¹ ∈ O := fun c o ho => Normal.conj_mem inferInstance o ho c
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  set S := actKer O Y hYc with hSdef
  have hOS : O ≤ S := le_actKer hYc hOcomm
  have : S.Normal := ⟨fun n hn g => actKer_conj hYc hOC hn g⟩
  set B : Subgroup (Wr2 (Equiv.Perm (Fin 5))) := betaHom.range with hB
  have hBf : B ≤ f.range := by
    rintro _ ⟨x, rfl⟩
    exact hbase x
  have hBperf : ⁅B, B⁆ = B := commutator_range_eq commutator_alt_five_prod betaHom
  have hA5perf : ⁅(⊤ : Subgroup (alternatingGroup (Fin 5))),
      (⊤ : Subgroup (alternatingGroup (Fin 5)))⁆ = ⊤ := by
    have := commutator_alternatingGroup_eq_top (α := Fin 5) (by simp)
    rwa [commutator_def] at this
  let β₁ : alternatingGroup (Fin 5) →* Wr2 (Equiv.Perm (Fin 5)) :=
    betaHom.comp (MonoidHom.inl _ _)
  let β₂ : alternatingGroup (Fin 5) →* Wr2 (Equiv.Perm (Fin 5)) :=
    betaHom.comp (MonoidHom.inr _ _)
  have hB1f : β₁.range ≤ f.range := by
    rintro _ ⟨a, rfl⟩
    exact hbase (a, 1)
  have hB2f : β₂.range ≤ f.range := by
    rintro _ ⟨a, rfl⟩
    exact hbase (1, a)
  set A1 : Subgroup C := β₁.range.comap f with hA1
  set A2 : Subgroup C := β₂.range.comap f with hA2
  have hconjf : ∀ g : C, f (t * g * t⁻¹) = tau * f g * tau⁻¹ := by
    intro g
    rw [map_mul, map_mul, map_inv, ht]
  have hcommA1 : ⁅A1, A1⁆ ≤ S := by
    rw [commutator_le]
    intro g hg h hh
    obtain ⟨a, ha⟩ := (Subgroup.mem_comap.1 hg : f g ∈ β₁.range)
    obtain ⟨b, hb⟩ := (Subgroup.mem_comap.1 hh : f h ∈ β₁.range)
    have hf2 : f (t * h * t⁻¹) = betaHom (1, b) := by
      rw [hconjf, ← hb]
      exact tau_betaHom (b, 1)
    have hgh2 : ⁅g, t * h * t⁻¹⁆ ∈ O := by
      rw [← hker, map_commutatorElement, hf2, ← ha]
      have h1 : ⁅(((a, 1) : alternatingGroup (Fin 5) × alternatingGroup (Fin 5))),
          ((1, b) : alternatingGroup (Fin 5) × alternatingGroup (Fin 5))⁆ = 1 :=
        Prod.ext (by simp [commutatorElement_def]) (by simp [commutatorElement_def])
      change ⁅betaHom (a, 1), betaHom (1, b)⁆ = 1
      rw [← map_commutatorElement, h1, map_one]
    let q : C →* C ⧸ S := QuotientGroup.mk' S
    have hq1 : q (t * h * t⁻¹) = q h := by
      have h1 : t * h * t⁻¹ * h⁻¹ ∈ S := t_comm_mem_actKer hYc hOC htt hOinv h
      have h2 : q (t * h * t⁻¹ * h⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 h1
      rw [map_mul, map_inv] at h2
      exact mul_inv_eq_one.1 h2
    have h3 : q ⁅g, t * h * t⁻¹⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (hOS hgh2)
    rw [map_commutatorElement, hq1, ← map_commutatorElement] at h3
    exact (QuotientGroup.eq_one_iff _).1 h3
  have hA1S : A1 ≤ S := by
    intro g hg
    have hmap := map_comap_commutator f β₁.range hB1f (commutator_range_eq hA5perf β₁)
    have hfg : f g ∈ (⁅A1, A1⁆).map f := hmap ▸ (Subgroup.mem_comap.1 hg)
    obtain ⟨d, hd, hdg⟩ := hfg
    have hgd : g * d⁻¹ ∈ O := by
      rw [← hker, map_mul, map_inv, hdg, mul_inv_cancel]
    have : g = (g * d⁻¹) * d := by group
    rw [this]
    exact S.mul_mem (hOS hgd) (hcommA1 hd)
  have hA2S : A2 ≤ S := by
    intro g hg
    obtain ⟨b, hb⟩ := (Subgroup.mem_comap.1 hg : f g ∈ β₂.range)
    have hf1 : f (t * g * t⁻¹) = β₁ b := by
      rw [hconjf, ← hb]
      exact tau_betaHom (1, b)
    have h1 : t * g * t⁻¹ ∈ S := hA1S (Subgroup.mem_comap.2 ⟨b, hf1.symm⟩)
    have h2 := actKer_conj hYc hOC h1 t⁻¹
    rw [inv_inv] at h2
    simpa [mul_assoc] using h2
  set P₁ : Subgroup C := B.comap f with hP₁
  have hP₁S : P₁ ≤ S := by
    intro g hg
    obtain ⟨⟨a, b⟩, hab⟩ := (Subgroup.mem_comap.1 hg : f g ∈ betaHom.range)
    obtain ⟨g₁, hg₁⟩ := hbase (a, 1)
    obtain ⟨g₂, hg₂⟩ := hbase (1, b)
    have hg₁A : g₁ ∈ A1 := Subgroup.mem_comap.2 ⟨a, hg₁.symm⟩
    have hg₂A : g₂ ∈ A2 := Subgroup.mem_comap.2 ⟨b, hg₂.symm⟩
    have hprod : f (g * (g₁ * g₂)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, hg₁, hg₂, ← hab, ← map_mul]
      have : ((a, 1) : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) * (1, b) = (a, b) := by
        simp
      rw [this, mul_inv_cancel]
    have : g = (g * (g₁ * g₂)⁻¹) * g₁ * g₂ := by group
    rw [this]
    exact S.mul_mem (S.mul_mem (hOS ((hker _).1 hprod)) (hA1S hg₁A)) (hA2S hg₂A)
  set Q₀ : Subgroup C := P₁ ⊓ centralizer (O : Set C) with hQ₀
  have hBP : P₁.map f = B := by
    rw [hP₁, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hBf
  have hDp : ⁅P₁, P₁⁆ ≤ Q₀ := by
    refine le_inf (commutator_le_self P₁) ((commutator_le).2 ?_)
    intro g hg h hh o ho
    have := commutator_actKer_centralizes hYc P₁ hP₁S hg hh ho
    exact (commutatorElement_eq_one_iff_mul_comm.1 this).symm
  have hQ0map : Q₀.map f = B := by
    refine le_antisymm (hBP ▸ Subgroup.map_mono inf_le_left) ?_
    calc B = ⁅B, B⁆ := hBperf.symm
      _ = (⁅P₁, P₁⁆).map f := by rw [map_commutator, hBP]
      _ ≤ Q₀.map f := Subgroup.map_mono hDp
  have hcen : ∀ z ∈ Q₀, f z = 1 → ∀ g ∈ Q₀, g * z = z * g := fun z _ hz g hg =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hg).2 z ((hker z).1 hz)).symm
  obtain ⟨hRperf, hRmap⟩ := commutator_perfect_of_central f Q₀ hcen (by rw [hQ0map, hBperf])
  set R : Subgroup C := ⁅Q₀, Q₀⁆ with hR
  have hRB : R.map f = B := by rw [hRmap, hQ0map]
  have hRQ : R ≤ Q₀ := commutator_le_self Q₀
  have ht0 : ∀ g ∈ Q₀, t * g * t⁻¹ ∈ Q₀ := by
    intro g hg
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hg).1 : f g ∈ betaHom.range)
      refine Subgroup.mem_comap.2 ⟨x.swap, ?_⟩
      rw [hconjf, ← hx]
      exact (tau_betaHom x).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro o ho
      have hg' : (t⁻¹ * o * t) * g = g * (t⁻¹ * o * t) := by
        have := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hg).2 (t⁻¹ * o * t)
          (by simpa using hOC t⁻¹ o ho)
        exact this
      calc o * (t * g * t⁻¹) = t * ((t⁻¹ * o * t) * g) * t⁻¹ := by group
        _ = t * (g * (t⁻¹ * o * t)) * t⁻¹ := by rw [hg']
        _ = (t * g * t⁻¹) * o := by group
  refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr o ho
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hRQ hr)).2 o ho).symm
  · intro r hr
    let φ : C →* C := (MulAut.conj t).toMonoidHom
    have h1 : Q₀.map φ ≤ Q₀ := by
      rintro _ ⟨g, hg, rfl⟩
      exact ht0 g hg
    have h2 : R.map φ ≤ R := by
      rw [hR, map_commutator]
      exact commutator_mono h1 h1
    exact h2 ⟨r, hr, rfl⟩
  · intro r hr hrO
    have hmem : ∀ x : ↥R, f (x : C) ∈ B := fun x => hRB ▸ ⟨x, x.2, rfl⟩
    let π : ↥R →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5) :=
      (MonoidHom.ofInjective betaHom_injective).symm.toMonoidHom.comp
        (MonoidHom.codRestrict (f.comp R.subtype) betaHom.range hmem)
    have hπ : ∀ x : ↥R, betaHom (π x) = f (x : C) := by
      intro x
      have e := congrArg Subtype.val
        ((MonoidHom.ofInjective betaHom_injective).apply_symm_apply ⟨f (x : C), hmem x⟩)
      rw [MonoidHom.ofInjective_apply] at e
      exact e
    have hs : Function.Surjective π := by
      intro y
      have : betaHom y ∈ R.map f := by rw [hRB]; exact ⟨y, rfl⟩
      obtain ⟨r', hr', hr'y⟩ := this
      refine ⟨⟨r', hr'⟩, betaHom_injective ?_⟩
      rw [hπ]
      exact hr'y
    have hk : π.ker ≤ center ↥R := by
      intro x hx
      have h1 : f (x : C) = 1 := by
        rw [← hπ, MonoidHom.mem_ker.1 hx, map_one]
      have h2 : (x : C) ∈ O := (hker _).1 h1
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.1
        (Subgroup.mem_inf.1 (hRQ g.2)).2 _ h2).symm)
    have hodd : Odd (Nat.card π.ker) := by
      refine Odd.of_dvd_nat hOodd ?_
      refine Subgroup.card_dvd_of_injective
        (f := (R.subtype.comp π.ker.subtype).codRestrict O ?_) ?_
      · intro x
        have h1 : f ((x : ↥R) : C) = 1 := by
          rw [← hπ, MonoidHom.mem_ker.1 x.2, map_one]
        exact (hker _).1 h1
      · intro a b hab
        have := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext this)
    have hperf : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.2 hRperf
    have hbot := ker_eq_bot_of_odd_five_sq hperf hs hk hodd
    have h1 : (⟨r, hr⟩ : ↥R) ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      apply betaHom_injective
      rw [hπ, map_one]
      exact (hker _).2 hrO
    rw [hbot] at h1
    exact congrArg Subtype.val (Subgroup.mem_bot.1 h1)
  · intro r hr
    have : f r ∈ R.map f := ⟨r, hr, rfl⟩
    rw [hRB] at this
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx.symm⟩
  · intro x
    have : betaHom x ∈ R.map f := by rw [hRB]; exact ⟨x, rfl⟩
    obtain ⟨r, hr, hrx⟩ := this
    exact ⟨r, hr, hrx⟩

end Core

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
