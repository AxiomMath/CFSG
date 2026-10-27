module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eComm

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e

open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.AE.Wr
open Finset
open scoped commutatorElement

theorem map_eq_of_iff {g : Equiv.Perm (Fin 8)} {T T' : Finset (Fin 8)}
    (h : ∀ z, g z ∈ T' ↔ z ∈ T) : T.map g.toEmbedding = T' := by
  ext w
  rw [Finset.mem_map_equiv]
  have := h (g.symm w)
  simpa using this.symm

theorem vq_ne_one_of_card_four {S : Finset (Fin 8)} (hS : S.card = 4) : vq S ≠ 1 := by
  intro h
  rw [← vq_empty] at h
  rcases vq_eq_iff.mp h with h1 | h1
  · rw [← h1] at hS
    simp at hS
  · have h2 := congrArg Finset.card h1
    simp [Finset.card_compl, hS] at h2

namespace E8Pkg

variable {Y : Type} [Group Y] {I D : Subgroup Y} (P : E8Pkg I D)

@[expose] def W4 (s : Y) : Prop :=
  s ∈ D ∧ ∃ S : Finset (Fin 8), S.card = 4 ∧ P.ph s = vq S

theorem W4.conj {P : E8Pkg I D} {s i : Y} (hs : P.W4 s) (hi : i ∈ I) : P.W4 (i * s * i⁻¹) := by
  obtain ⟨hsD, S, hS, hph⟩ := hs
  refine ⟨P.conj_mem_D hi hsD, S.map (P.rho i).toEmbedding, by rw [Finset.card_map]; exact hS, ?_⟩
  exact P.conj_vec hi (P.le hsD) hph

theorem w4_of_conj {t d : Y}
    (hno2 : ∀ d ∈ D, ∀ S : Finset (Fin 8), S.card = 2 → P.ph d = vq S →
      ∀ g : Y, g * t * g⁻¹ ≠ d)
    (hd : d ∈ D) (hd1 : d ≠ 1) (hG : ∃ g : Y, g * t * g⁻¹ = d) : P.W4 d := by
  obtain ⟨S, hSe, hS⟩ := P.vec_of_mem_D hd
  obtain ⟨T, hT, hTc⟩ := exists_small S hSe
  have hvT : vq T = vq S := by
    rcases hT with rfl | rfl
    · rfl
    · exact vq_compl S
  have hphT : P.ph d = vq T := by rw [hS, hvT]
  rcases hTc with h0 | h2 | h4
  · exfalso
    apply hd1
    have hT0 : T = ∅ := Finset.card_eq_zero.mp h0
    rw [hT0, vq_empty] at hphT
    exact P.ph_inj (P.le hd) I.one_mem (by rw [hphT, P.ph_one])
  · exfalso
    obtain ⟨g, hg⟩ := hG
    exact hno2 d hd T h2 hphT g hg
  · exact ⟨hd, T, h4, hphT⟩

theorem exists_conj_cross {t τ : Y} (ht : t ∈ I) (hτ : τ ∈ I) {A B A' B' : Finset (Fin 8)}
    (hA : A.card = 4) (hB : B.card = 4) (hAB : (A ∩ B).card = 2) (hA' : A'.card = 4)
    (hB' : B'.card = 4) (hAB' : (A' ∩ B').card = 2) (htA : P.ph t = vq A) (hτB : P.ph τ = vq B) :
    ∃ i ∈ I, P.ph (i * t * i⁻¹) = vq A' ∧ P.ph (i * τ * i⁻¹) = vq B' := by
  obtain ⟨g, hg, hgA, hgB⟩ := exists_even_perm_cross hA hB hAB hA' hB' hAB'
  obtain ⟨i, hi, hρ⟩ := P.exists_lift hg
  refine ⟨i, hi, ?_, ?_⟩
  · rw [P.conj_vec hi ht htA, hρ, map_eq_of_iff hgA]
  · rw [P.conj_vec hi hτ hτB, hρ, map_eq_of_iff hgB]

theorem exists_conj_four {t : Y} (ht : t ∈ I) {A T : Finset (Fin 8)} (hA : A.card = 4)
    (hT : T.card = 4) (htA : P.ph t = vq A) : ∃ i ∈ I, P.ph (i * t * i⁻¹) = vq T := by
  obtain ⟨g, hg, hgA⟩ := exists_even_perm_card (k := 4) (by norm_num) hA hT
  obtain ⟨i, hi, hρ⟩ := P.exists_lift hg
  refine ⟨i, hi, ?_⟩
  rw [P.conj_vec hi ht htA, hρ, map_eq_of_iff hgA]

theorem conj_W4_of_cent {t τ : Y} (ht : t ∈ D) (hτ : τ ∈ D) {A B : Finset (Fin 8)}
    (hA : A.card = 4) (hB : B.card = 4) (hAB : (A ∩ B).card = 2) (htA : P.ph t = vq A)
    (hτB : P.ph τ = vq B) (hτG : ∃ y : Y, y * t * y⁻¹ = τ)
    (hno2 : ∀ d ∈ D, ∀ S : Finset (Fin 8), S.card = 2 → P.ph d = vq S →
      ∀ g : Y, g * t * g⁻¹ ≠ d)
    (hH : ∀ c : Y, c * t * c⁻¹ = t → c * τ * c⁻¹ ∈ D)
    {c : Y} (hc : c * t * c⁻¹ = t) {s : Y} (hs : P.W4 s) : P.W4 (c * s * c⁻¹) := by
  have htI : t ∈ I := P.le ht
  have hτI : τ ∈ I := P.le hτ
  obtain ⟨y, hy⟩ := hτG
  have hτ1 : τ ≠ 1 := fun h => vq_ne_one_of_card_four hB (by rw [← hτB, h, P.ph_one])
  have hcl : ∀ k : Y, k * t * k⁻¹ = t → P.W4 (k * τ * k⁻¹) := by
    intro k hk
    refine P.w4_of_conj hno2 (hH k hk) ?_ ⟨k * y, ?_⟩
    · intro h1
      apply hτ1
      have h2 : τ = k⁻¹ * (k * τ * k⁻¹) * k := by group
      rw [h2, h1]
      group
    · rw [← hy]
      group
  have cross : ∀ (s' : Y) (S' : Finset (Fin 8)), s' ∈ I → S'.card = 4 → P.ph s' = vq S' →
      (A ∩ S').card = 2 → P.W4 (c * s' * c⁻¹) := by
    intro s' S' hs'I hS' hph' hcr
    obtain ⟨i, hi, hit, hiτ⟩ := P.exists_conj_cross htI hτI hA hB hAB hA hS' hcr htA hτB
    have hit' : i * t * i⁻¹ = t := P.ph_inj (I.mul_mem (I.mul_mem hi htI) (I.inv_mem hi)) htI
      (by rw [hit, htA])
    have hsτ : s' = i * τ * i⁻¹ := P.ph_inj hs'I (I.mul_mem (I.mul_mem hi hτI) (I.inv_mem hi))
      (by rw [hiτ, hph'])
    have : c * s' * c⁻¹ = (c * i) * τ * (c * i)⁻¹ := by rw [hsτ]; group
    rw [this]
    exact hcl (c * i) (by
      calc c * i * t * (c * i)⁻¹ = c * (i * t * i⁻¹) * c⁻¹ := by group
        _ = t := by rw [hit', hc])
  obtain ⟨hsD, S, hS, hph⟩ := hs
  have hsI : s ∈ I := P.le hsD
  by_cases hSA : S = A ∨ S = Aᶜ
  ·
    have : s = t := by
      apply P.ph_inj hsI htI
      rw [hph, htA]
      rcases hSA with rfl | rfl
      · rfl
      · exact vq_compl _
    rw [this, hc]
    exact ⟨ht, A, hA, htA⟩
  push Not at hSA
  by_cases hcross : (A ∩ S).card = 2
  · exact cross s S hsI hS hph hcross
  ·
    obtain ⟨R, hR, hAR, hSR⟩ := exists_mid hA hS hcross hSA.1 hSA.2
    obtain ⟨r, hrD, hrph⟩ := P.exists_vec (S := R) (by rw [hR]; decide)
    have hrI := P.le hrD
    obtain ⟨j, hj, hjt, hjτ⟩ := P.exists_conj_cross htI hτI hA hB hAB hR hS
      (by rw [Finset.inter_comm]; exact hSR) htA hτB
    have hjt' : j * t * j⁻¹ = r := P.ph_inj (I.mul_mem (I.mul_mem hj htI) (I.inv_mem hj)) hrI
      (by rw [hjt, hrph])
    have hjs : j * τ * j⁻¹ = s := P.ph_inj (I.mul_mem (I.mul_mem hj hτI) (I.inv_mem hj)) hsI
      (by rw [hjτ, hph])
    have hcr := cross r R hrI hR hrph hAR
    obtain ⟨hcrD, S₃, hS₃, hph₃⟩ := hcr
    have hcrI : c * r * c⁻¹ ∈ I := P.le hcrD
    obtain ⟨k, hk, hkph⟩ := P.exists_conj_four htI hA hS₃ htA
    have hkt : k * t * k⁻¹ = c * r * c⁻¹ :=
      P.ph_inj (I.mul_mem (I.mul_mem hk htI) (I.inv_mem hk)) hcrI (by rw [hkph, hph₃])
    have hcent : (k⁻¹ * c * j) * t * (k⁻¹ * c * j)⁻¹ = t := by
      calc (k⁻¹ * c * j) * t * (k⁻¹ * c * j)⁻¹ = k⁻¹ * (c * (j * t * j⁻¹) * c⁻¹) * k := by group
        _ = k⁻¹ * (k * t * k⁻¹) * k := by rw [hjt', hkt]
        _ = t := by group
    have hfin : c * s * c⁻¹ = k * ((k⁻¹ * c * j) * τ * (k⁻¹ * c * j)⁻¹) * k⁻¹ := by
      rw [← hjs]
      group
    rw [hfin]
    exact (hcl _ hcent).conj hk

theorem step2 {t τ : Y} (ht : t ∈ D) (hτ : τ ∈ D) {A B : Finset (Fin 8)}
    (hA : A.card = 4) (hB : B.card = 4) (hAB : (A ∩ B).card = 2) (htA : P.ph t = vq A)
    (hτB : P.ph τ = vq B) (hτG : ∃ y : Y, y * t * y⁻¹ = τ)
    (hno2 : ∀ d ∈ D, ∀ S : Finset (Fin 8), S.card = 2 → P.ph d = vq S →
      ∀ g : Y, g * t * g⁻¹ ≠ d)
    (hH : ∀ c : Y, c * t * c⁻¹ = t → c * τ * c⁻¹ ∈ D) :
    ∀ g ∈ I ⊔ Subgroup.centralizer ({t} : Set Y), g * t * g⁻¹ ∈ D := by
  let Q : Subgroup Y :=
    { carrier := {g | ∀ s, P.W4 s → P.W4 (g * s * g⁻¹) ∧ P.W4 (g⁻¹ * s * g)}
      mul_mem' := fun {a b} ha hb s hs => by
        refine ⟨?_, ?_⟩
        · have h := (ha _ (hb s hs).1).1
          have e : a * (b * s * b⁻¹) * a⁻¹ = a * b * s * (a * b)⁻¹ := by group
          rwa [e] at h
        · have h := (hb _ (ha s hs).2).2
          have e : b⁻¹ * (a⁻¹ * s * a) * b = (a * b)⁻¹ * s * (a * b) := by group
          rwa [e] at h
      one_mem' := fun s hs => by
        refine ⟨?_, ?_⟩ <;> simpa using hs
      inv_mem' := fun {a} ha s hs => ⟨by simpa using (ha s hs).2, by simpa using (ha s hs).1⟩ }
  have hI : I ≤ Q := fun i hi s hs => ⟨hs.conj hi, by simpa using hs.conj (I.inv_mem hi)⟩
  have hC : Subgroup.centralizer ({t} : Set Y) ≤ Q := by
    intro c hc s hs
    have hc' : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hc1 : c * t * c⁻¹ = t := by rw [hc']; group
    have hc2 : c⁻¹ * t * c⁻¹⁻¹ = t := by
      calc c⁻¹ * t * c⁻¹⁻¹ = c⁻¹ * (t * c) * c⁻¹ * c⁻¹⁻¹ * c⁻¹⁻¹⁻¹ * c⁻¹⁻¹ := by group
        _ = t := by rw [← hc']; group
    refine ⟨P.conj_W4_of_cent ht hτ hA hB hAB htA hτB hτG hno2 hH hc1 hs, ?_⟩
    have := P.conj_W4_of_cent ht hτ hA hB hAB htA hτB hτG hno2 hH hc2 hs
    simpa using this
  intro g hg
  have hgQ : g ∈ Q := (sup_le hI hC) hg
  exact ((hgQ t ⟨ht, A, hA, htA⟩).1).1

theorem commutator_conj_eq {i : Y} (hD : ∀ d ∈ D, i * d * i⁻¹ ∈ D) (hD' : ∀ d ∈ D, i⁻¹ * d * i ∈ D)
    (x : Y) :
    ⁅D, Subgroup.zpowers (i * x * i⁻¹)⁆ = (⁅D, Subgroup.zpowers x⁆).map (MulAut.conj i).toMonoidHom := by
  rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
  have hDm : D.map (MulAut.conj i).toMonoidHom = D := by
    apply le_antisymm
    · rintro _ ⟨d, hd, rfl⟩
      exact hD d hd
    · intro d hd
      refine ⟨i⁻¹ * d * i, hD' d hd, ?_⟩
      show i * (i⁻¹ * d * i) * i⁻¹ = d
      group
  rw [hDm]
  rfl

theorem exists_conj_comm {x t τ : Y} {A β : Finset (Fin 8)} (hx : x ∈ I) (hxx : x * x = 1)
    (hA : A.card = 4) (hβ : β.card = 4) (hAβ : (A ∩ β).card = 2)
    (hfix : ∀ z, P.rho x z ≠ z) (hpres : ∀ z, P.rho x z ∈ A ↔ z ∈ A)
    (ht : t ∈ D) (htA : P.ph t = vq A) (hτ : τ ∈ D) (hτβ : P.ph τ = vq β) :
    ∃ i ∈ I, i * t * i⁻¹ = t ∧
      ⁅D, Subgroup.zpowers (i * x * i⁻¹)⁆ = Subgroup.closure ({t, τ} : Set Y) := by
  obtain ⟨B, hB, hAB, hcomm⟩ := P.comm_eq hx hxx hA hfix hpres
  obtain ⟨s₂, hs₂, hs₂B⟩ := P.exists_vec (S := B) (by rw [hB]; decide)
  have hE := hcomm t ht s₂ hs₂ htA hs₂B
  have htI : t ∈ I := P.le ht
  have hs₂I : s₂ ∈ I := P.le hs₂
  obtain ⟨i, hi, hit, hiB⟩ := P.exists_conj_cross htI hs₂I hA hB hAB hA hβ hAβ htA hs₂B
  have hit' : i * t * i⁻¹ = t := P.ph_inj (I.mul_mem (I.mul_mem hi htI) (I.inv_mem hi)) htI
    (by rw [hit, htA])
  have hiτ : i * s₂ * i⁻¹ = τ := P.ph_inj (I.mul_mem (I.mul_mem hi hs₂I) (I.inv_mem hi))
    (P.le hτ) (by rw [hiB, hτβ])
  refine ⟨i, hi, hit', ?_⟩
  rw [commutator_conj_eq (fun d hd => P.conj_mem_D hi hd)
    (fun d hd => by simpa using P.conj_mem_D (I.inv_mem hi) hd), hE, MonoidHom.map_closure]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, rfl | rfl, rfl⟩
    · left
      exact hit'
    · right
      exact hiτ
  · rintro (h | h)
    · exact ⟨t, Or.inl rfl, by rw [h]; exact hit'⟩
    · exact ⟨s₂, Or.inr rfl, by rw [h]; exact hiτ⟩

end E8Pkg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
