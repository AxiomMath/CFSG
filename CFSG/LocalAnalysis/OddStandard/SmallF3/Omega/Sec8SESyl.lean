module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Fink
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L68a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8SSup
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec8s_mem_sup {t : G} {E : Subgroup G} (ht2 : t * t = 1)
    (htn : ∀ e ∈ E, t * e * t⁻¹ ∈ E) {y : G} (hy : y ∈ zpowers t ⊔ E) :
    y ∈ E ∨ ∃ e ∈ E, y = t * e :=
  sec8s_mem_sup_zpowers ht2 htn hy

private theorem sec8s_comm_ne {t : G} {B E : Subgroup G}
    (hBcard : Nat.card B = 2 ^ 4)
    (hcomm_onto : ∀ b ∈ B, ∃ e ∈ E, e * t * e⁻¹ * t⁻¹ = b) :
    ∃ e ∈ E, t * e ≠ e * t := by
  have hb_exists : ∃ b ∈ B, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : B = ⊥ := by
      ext b
      simp only [Subgroup.mem_bot]
      exact ⟨fun hb => hcon b hb, fun hb => by rw [hb]; exact B.one_mem⟩
    have h1 : Nat.card B = 1 := by rw [hbot, Subgroup.card_bot]
    have h16 : (2 : ℕ) ^ 4 = 16 := by norm_num
    omega
  obtain ⟨b, hb, hb1⟩ := hb_exists
  obtain ⟨e, heE, hee⟩ := hcomm_onto b hb
  refine ⟨e, heE, ?_⟩
  intro hcomm
  apply hb1
  have h1 : e * t * e⁻¹ * t⁻¹ = 1 := by
    rw [← hcomm]
    group
  rw [← hee, h1]

private theorem sec8s_conj_le [Finite G] {t : G} {B E P K' : Subgroup G} {a : G}
    (hEel : IsElemAb2 E 8) (hcent : E ⊓ centralizer ({t} : Set G) = B)
    (hBcard : Nat.card B = 2 ^ 4)
    (ht2 : t * t = 1) (htn : ∀ e ∈ E, t * e * t⁻¹ ∈ E)
    (hEP : E ≤ P) (hPK' : P ≤ K') (haB : a ∈ centralizer (B : Set G))
    (haK : ∀ x : G, x ∈ K' ↔ a⁻¹ * x * a ∈ zpowers t ⊔ E) :
    ∀ e ∈ E, a⁻¹ * e * a ∈ E ∧ a * e * a⁻¹ ∈ E := by
  classical
  haveI : Finite ↥E := Finite.of_injective (Subtype.val : ↥E → G) Subtype.val_injective
  haveI : Finite ↥B := Finite.of_injective (Subtype.val : ↥B → G) Subtype.val_injective
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x :=
    fun x hx y hy => CFSG.Open.IsElemAbelian.comm hEel.1 hx hy
  have hEK' : E ≤ K' := le_trans hEP hPK'
  have hA : ∀ e ∈ E, a⁻¹ * e * a ∈ E := by
    by_contra hcon
    push Not at hcon
    obtain ⟨e₂, he₂E, he₂ne⟩ := hcon
    have he₂Ka : a⁻¹ * e₂ * a ∈ zpowers t ⊔ E := (haK e₂).mp (hEK' he₂E)
    rcases sec8s_mem_sup ht2 htn he₂Ka with he₂E' | ⟨e₁, he₁E, he₂eq⟩
    · exact he₂ne he₂E'
    · let D : Subgroup G := E ⊓ E.comap (MulAut.conj a⁻¹).toMonoidHom
      haveI : Finite ↥D := Finite.of_injective (Subtype.val : ↥D → G) Subtype.val_injective
      have hmemD : ∀ x : G, x ∈ D ↔ x ∈ E ∧ a⁻¹ * x * a ∈ E := by
        intro x
        simp only [D, Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply, inv_inv]
      have hDleB : D ≤ B := by
        intro x hx
        obtain ⟨hxE, hxD⟩ := (hmemD x).mp hx
        have hcommx :
            (a⁻¹ * x * a) * (a⁻¹ * e₂ * a) = (a⁻¹ * e₂ * a) * (a⁻¹ * x * a) := by
          have hxe : x * e₂ = e₂ * x := hcommE x hxE e₂ he₂E
          calc (a⁻¹ * x * a) * (a⁻¹ * e₂ * a) = a⁻¹ * (x * e₂) * a := by group
            _ = a⁻¹ * (e₂ * x) * a := by rw [hxe]
            _ = (a⁻¹ * e₂ * a) * (a⁻¹ * x * a) := by group
        rw [he₂eq] at hcommx
        have hcomme : (a⁻¹ * x * a) * e₁ = e₁ * (a⁻¹ * x * a) :=
          hcommE (a⁻¹ * x * a) hxD e₁ he₁E
        have hcommt : (a⁻¹ * x * a) * t = t * (a⁻¹ * x * a) := by
          calc (a⁻¹ * x * a) * t
              = (a⁻¹ * x * a) * ((t * e₁) * e₁⁻¹) := by group
            _ = ((a⁻¹ * x * a) * (t * e₁)) * e₁⁻¹ := by group
            _ = ((t * e₁) * (a⁻¹ * x * a)) * e₁⁻¹ := by rw [hcommx]
            _ = t * ((e₁ * (a⁻¹ * x * a)) * e₁⁻¹) := by group
            _ = t * (((a⁻¹ * x * a) * e₁) * e₁⁻¹) := by rw [← hcomme]
            _ = t * (a⁻¹ * x * a) := by group
        have hmemcent : a⁻¹ * x * a ∈ centralizer ({t} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact hcommt.symm
        have hb : a⁻¹ * x * a ∈ B := by
          rw [← hcent]
          exact ⟨hxD, hmemcent⟩
        have hcomm_a : a * (a⁻¹ * x * a) * a⁻¹ = a⁻¹ * x * a := by
          have h := (Subgroup.mem_centralizer_iff.mp haB) (a⁻¹ * x * a) hb
          calc a * (a⁻¹ * x * a) * a⁻¹ = ((a⁻¹ * x * a) * a) * a⁻¹ := by rw [← h]
            _ = a⁻¹ * x * a := by group
        have hxeq : x = a⁻¹ * x * a := by
          calc x = a * (a⁻¹ * x * a) * a⁻¹ := by group
            _ = a⁻¹ * x * a := hcomm_a
        rw [hxeq]
        exact hb
      have hcover : ∀ x ∈ E, x ∈ D ∨ ∃ d ∈ D, x = d * e₂ := by
        intro x hxE
        have hxaK : a⁻¹ * x * a ∈ zpowers t ⊔ E := (haK x).mp (hEK' hxE)
        rcases sec8s_mem_sup ht2 htn hxaK with hxE' | ⟨e', he'E, he'eq⟩
        · exact Or.inl ((hmemD x).mpr ⟨hxE, hxE'⟩)
        · refine Or.inr ⟨x * e₂⁻¹, ?_, by group⟩
          refine (hmemD (x * e₂⁻¹)).mpr ⟨E.mul_mem hxE (E.inv_mem he₂E), ?_⟩
          have heq : a⁻¹ * (x * e₂⁻¹) * a = t * (e' * e₁⁻¹) * t⁻¹ := by
            rw [show a⁻¹ * (x * e₂⁻¹) * a =
              (a⁻¹ * x * a) * (a⁻¹ * e₂ * a)⁻¹ by group, he'eq, he₂eq]
            group
          rw [heq]
          exact htn _ (E.mul_mem he'E (E.inv_mem he₁E))
      have hcardED : Nat.card E ≤ 2 * Nat.card D := by
        let f : D ⊕ D → ↥E := fun s => match s with
          | Sum.inl d => ⟨(d : G), d.2.1⟩
          | Sum.inr d => ⟨(d : G) * e₂, E.mul_mem d.2.1 he₂E⟩
        have hf : Function.Surjective f := by
          rintro ⟨x, hxE⟩
          rcases hcover x hxE with hxD | ⟨d, hdD, hxd⟩
          · exact ⟨Sum.inl ⟨x, hxD⟩, by apply Subtype.ext; simp [f]⟩
          · exact ⟨Sum.inr ⟨d, hdD⟩, by apply Subtype.ext; simpa [f] using hxd.symm⟩
        calc Nat.card ↥E ≤ Nat.card (D ⊕ D) := Nat.card_le_card_of_surjective f hf
          _ = Nat.card D + Nat.card D := Nat.card_sum
          _ = 2 * Nat.card D := by omega
      have hcardDB : Nat.card D ≤ Nat.card B :=
        Nat.card_le_card_of_injective (f := fun d : D => (⟨(d : G), hDleB d.2⟩ : B))
          (fun x y h => Subtype.ext (congrArg (fun z : B => (z : G)) h))
      have hle : 2 ^ 8 ≤ 2 * 2 ^ 4 := by
        calc 2 ^ 8 = Nat.card E := hEel.2.symm
          _ ≤ 2 * Nat.card D := hcardED
          _ ≤ 2 * Nat.card B := Nat.mul_le_mul_left 2 hcardDB
          _ = 2 * 2 ^ 4 := by rw [hBcard]
      norm_num at hle
  have hB : ∀ e ∈ E, a * e * a⁻¹ ∈ E := by
    intro e he
    have hsurj : Function.Surjective
        (fun x : ↥E => (⟨a⁻¹ * (x : G) * a, hA x x.2⟩ : ↥E)) :=
      Finite.surjective_of_injective (fun x y h => by
        have hv : a⁻¹ * (x : G) * a = a⁻¹ * (y : G) * a := congrArg Subtype.val h
        have hxy : (x : G) = (y : G) := by
          have h' := congrArg (fun z => a * z * a⁻¹) hv
          simpa [mul_assoc] using h'
        exact Subtype.ext hxy)
    obtain ⟨x, hx⟩ := hsurj ⟨e, he⟩
    have hxe : a⁻¹ * (x : G) * a = e := congrArg Subtype.val hx
    have heq : a * e * a⁻¹ = (x : G) := by
      rw [← hxe]
      group
    rw [heq]
    exact x.2
  exact fun e he => ⟨hA e he, hB e he⟩

private theorem sec8s_P_le_E [Finite G] {t : G} {E P K' : Subgroup G} {a : G}
    (hconj : ∀ e ∈ E, a⁻¹ * e * a ∈ E ∧ a * e * a⁻¹ ∈ E)
    (ht2 : t * t = 1) (htn : ∀ e ∈ E, t * e * t⁻¹ ∈ E)
    (hPK' : P ≤ K') (haK : ∀ x : G, x ∈ K' ↔ a⁻¹ * x * a ∈ zpowers t ⊔ E)
    (hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hcentE : ∀ p ∈ P, ∀ x ∈ E, p * x = x * p)
    (hne : ∃ e₀ ∈ E, t * e₀ ≠ e₀ * t) :
    P ≤ E := by
  classical
  haveI : Finite ↥E := Finite.of_injective (Subtype.val : ↥E → G) Subtype.val_injective
  have hsurj : ∀ y ∈ E, ∃ x ∈ E, a⁻¹ * x * a = y := by
    intro y hy
    have hsurj' : Function.Surjective
        (fun x : ↥E => (⟨a⁻¹ * (x : G) * a, (hconj x x.2).1⟩ : ↥E)) :=
      Finite.surjective_of_injective (fun x y h => by
        have hv : a⁻¹ * (x : G) * a = a⁻¹ * (y : G) * a := congrArg Subtype.val h
        have hxy : (x : G) = (y : G) := by
          have h' := congrArg (fun z => a * z * a⁻¹) hv
          simpa [mul_assoc] using h'
        exact Subtype.ext hxy)
    obtain ⟨x, hx⟩ := hsurj' ⟨y, hy⟩
    exact ⟨x, x.2, congrArg Subtype.val hx⟩
  intro p hp
  have hpaK : a⁻¹ * p * a ∈ zpowers t ⊔ E := (haK p).mp (hPK' hp)
  rcases sec8s_mem_sup ht2 htn hpaK with hpaE | ⟨e, heE, hpeq⟩
  · have hp' : a * (a⁻¹ * p * a) * a⁻¹ ∈ E := (hconj _ hpaE).2
    rwa [show a * (a⁻¹ * p * a) * a⁻¹ = p by group] at hp'
  · exfalso
    have hcomm1 : ∀ x ∈ E, (t * e) * (a⁻¹ * x * a) = (a⁻¹ * x * a) * (t * e) := by
      intro x hx
      have hpx : p * x = x * p := hcentE p hp x hx
      have h' : (a⁻¹ * p * a) * (a⁻¹ * x * a) = (a⁻¹ * x * a) * (a⁻¹ * p * a) := by
        calc (a⁻¹ * p * a) * (a⁻¹ * x * a) = a⁻¹ * (p * x) * a := by group
          _ = a⁻¹ * (x * p) * a := by rw [hpx]
          _ = (a⁻¹ * x * a) * (a⁻¹ * p * a) := by group
      rwa [hpeq] at h'
    have hcomm2 : ∀ y ∈ E, (t * e) * y = y * (t * e) := by
      intro y hy
      obtain ⟨x, hxE, hxy⟩ := hsurj y hy
      rw [← hxy]
      exact hcomm1 x hxE
    have htcomm : ∀ y ∈ E, t * y = y * t := by
      intro y hy
      have h1 : (t * e) * y = y * (t * e) := hcomm2 y hy
      have h2 : e * y = y * e := hcommE e heE y hy
      have hinv : e⁻¹ * y = y * e⁻¹ := by
        have h := congrArg (fun z => e⁻¹ * z * e⁻¹) h2
        simpa [mul_assoc] using h.symm
      calc t * y = ((t * e) * e⁻¹) * y := by group
        _ = (t * e) * (e⁻¹ * y) := by group
        _ = (t * e) * (y * e⁻¹) := by rw [hinv]
        _ = ((t * e) * y) * e⁻¹ := by group
        _ = (y * (t * e)) * e⁻¹ := by rw [h1]
        _ = y * ((t * e) * e⁻¹) := by group
        _ = y * t := by group
    obtain ⟨e₀, he₀E, he₀ne⟩ := hne
    exact he₀ne (htcomm e₀ he₀E)

theorem sec8s_E_sylow [Finite G] (hSyl : Asc82FinkSylow) {t : G} {L S : Subgroup G} {z g : G}
    {B E : Subgroup G} (hE : Sec8E G t L S z g B E) :
    IsSylow2Of E (centralizer (E : Set G)) := by
  classical
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hE.ctx.involution, pow_orderOf_eq_one]
  have hEel : IsElemAb2 E 8 := hE.elem
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (p := 2) (n := 8) hEel.2
  have hEC : E ≤ centralizer (E : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (CFSG.Open.IsElemAbelian.comm hEel.1 he hx).symm
  obtain ⟨P, hP, hEP⟩ := sec68_exists_sylow_ge (H := centralizer (E : Set G)) hE2 hEC
  have hBE : B ≤ E := by
    rw [← hE.cent_t]
    exact inf_le_left
  have hPB : P ≤ centralizer (B : Set G) :=
    hP.1.trans (Subgroup.centralizer_le (s := (B : Set G)) (t := (E : Set G)) hBE)
  obtain ⟨K', hK', hPK'⟩ :=
    sec68_exists_sylow_ge (H := centralizer (B : Set G)) hP.2.1 hPB
  have hK : IsSylow2Of (zpowers t ⊔ E) (centralizer (B : Set G)) :=
    hSyl G t L S z g B E hE
  obtain ⟨a, ha, haK⟩ := IsSylow2Of.exists_conj_mem (H := centralizer (B : Set G)) hK hK'
  have hconj : ∀ e ∈ E, a⁻¹ * e * a ∈ E ∧ a * e * a⁻¹ ∈ E :=
    sec8s_conj_le hEel hE.cent_t hE.ctx.B_e16.2 ht2 hE.t_norm hEP hPK' ha haK
  have hne : ∃ e₀ ∈ E, t * e₀ ≠ e₀ * t :=
    sec8s_comm_ne hE.ctx.B_e16.2 hE.comm_onto
  have hPleE : P ≤ E :=
    sec8s_P_le_E hconj ht2 hE.t_norm hPK' haK
      (fun x hx y hy => CFSG.Open.IsElemAbelian.comm hEel.1 hx hy)
      (fun p hp x hx => ((Subgroup.mem_centralizer_iff.mp (hP.1 hp)) x hx).symm) hne
  have hPE : P = E := le_antisymm hPleE hEP
  rw [hPE] at hP
  exact hP

end CFSG.OddStandard.SmallF3.Omega
