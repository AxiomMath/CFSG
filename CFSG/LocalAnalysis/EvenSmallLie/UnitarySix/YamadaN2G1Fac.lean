module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2G1L
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Std

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Subgroup CFSG.ABGLocalTools CFSG.EvenSmallLie.UnitarySix.YamadaEnd
  CFSG.EvenSmallLie.UnitarySix.YamadaPar
open scoped MatrixGroups

section Transfer

variable {M Γ : Type*} [Group M] [Group Γ] (f : M →* Γ) (hf : Function.Injective f)
  {Pm Dm : Subgroup M}
include hf

theorem mem_map_iff_of_inj {H : Subgroup M} {m : M} : f m ∈ H.map f ↔ m ∈ H :=
  ⟨fun ⟨_, hm', he⟩ => hf he ▸ hm', fun h => ⟨m, h, rfl⟩⟩

omit hf in
theorem transfer_normalizer (h : Pm ≤ normalizer (Dm : Set M)) :
    Pm.map f ≤ normalizer ((Dm.map f : Subgroup Γ) : Set Γ) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨_, (mem_normalizer_iff.mp (h hx) d).mp hd, by simp⟩
  · rintro ⟨d, hd, he⟩
    refine ⟨x⁻¹ * d * x, ?_, ?_⟩
    · have := (mem_normalizer_iff.mp (h (inv_mem hx)) d).mp hd
      simpa using this
    · rw [map_mul, map_mul, map_inv, he]; group

omit hf in
theorem transfer_comm (h : ∀ x ∈ Pm, ∀ y ∈ Pm, x * y * x⁻¹ * y⁻¹ ∈ Dm) :
    ∀ x ∈ Pm.map f, ∀ y ∈ Pm.map f, x * y * x⁻¹ * y⁻¹ ∈ Dm.map f := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact ⟨_, h x hx y hy, by simp⟩

omit hf in
theorem transfer_sq (h : ∀ x ∈ Pm, x * x ∈ Dm) : ∀ x ∈ Pm.map f, x * x ∈ Dm.map f := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨_, h x hx, by simp⟩

omit hf in
theorem transfer_g_normalizer {g : M} (h : g ∈ normalizer (Pm : Set M)) :
    f g ∈ normalizer ((Pm.map f : Subgroup Γ) : Set Γ) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, (mem_normalizer_iff.mp h x).mp hx, by simp⟩
  · rintro ⟨x, hx, he⟩
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have := (mem_normalizer_iff.mp (inv_mem h) x).mp hx
      simpa using this
    · rw [map_mul, map_mul, map_inv, he]; group

theorem transfer_fix {g : M} (h : ∀ x ∈ Pm, g * x * g⁻¹ * x⁻¹ ∈ Dm → x ∈ Dm) :
    ∀ x ∈ Pm.map f, f g * x * (f g)⁻¹ * x⁻¹ ∈ Dm.map f → x ∈ Dm.map f := by
  rintro _ ⟨x, hx, rfl⟩ hd
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, mem_map_iff_of_inj f hf] at hd
  exact ⟨x, h x hx hd, rfl⟩

end Transfer

theorem radR_conj {y r : SL(4, CFSG.Fischer.F4)} (hy : y ∈ pstd CFSG.Fischer.F4) (hr : r ∈ radR) :
    y * r * y⁻¹ ∈ radR := by
  have := comm_mem_radR hy (radR_le hr)
  have e : y * r * y⁻¹ = (y * r * y⁻¹ * r⁻¹) * r := by group
  rw [e]
  exact mul_mem this hr

theorem pstd_le_normalizer_radR :
    pstd CFSG.Fischer.F4 ≤ normalizer ((radR : Subgroup _) : Set SL(4, CFSG.Fischer.F4)) := by
  intro y hy
  rw [mem_normalizer_iff]
  intro r
  refine ⟨radR_conj hy, fun h => ?_⟩
  have := radR_conj (inv_mem hy) h
  simpa [mul_assoc] using this

structure G1Facts {Γ : Type*} [Group Γ] (τ : Γ →* Γ) (χb : msigma CFSG.Fischer.F4 →* Γ)
    (Pb Db : Subgroup Γ) : Prop where
  norm : Pb ≤ normalizer (Db : Set Γ)
  comm : ∀ x ∈ Pb, ∀ y ∈ Pb, x * y * x⁻¹ * y⁻¹ ∈ Db
  sq : ∀ x ∈ Pb, x * x ∈ Db
  tfix : ∀ x ∈ Pb, x * (τ x)⁻¹ ∈ Db → ∃ A ∈ pSig CFSG.Fischer.F4, (χb A)⁻¹ * x ∈ Db
  jnorm : χb ⟨dω, dω_mem_msigma⟩ ∈ normalizer (Pb : Set Γ)
  jfix : ∀ x ∈ Pb, χb ⟨dω, dω_mem_msigma⟩ * x * (χb ⟨dω, dω_mem_msigma⟩)⁻¹ * x⁻¹ ∈ Db →
    x ∈ Db

theorem eq_map_radR {Γ : Type*} [Group Γ] (Φ : SL(4, CFSG.Fischer.F4) ≃* Γ) {Pb Db : Subgroup Γ}
    (hPΦ : (pstd CFSG.Fischer.F4).map Φ.toMonoidHom = Pb) (hDP : Db ≤ Pb)
    (hDc : ∀ x ∈ Db, ∀ y ∈ Db, x * y = y * x) (hDcard : 2 ^ 8 ≤ Nat.card Db) :
    Db = radR.map Φ.toMonoidHom := by
  set f := Φ.toMonoidHom
  have hf : Function.Injective f := Φ.injective
  have hDb : Db = (Db.comap f).map f :=
    (Subgroup.map_comap_eq_self_of_surjective Φ.surjective Db).symm
  have hE : Db.comap f ≤ pstd CFSG.Fischer.F4 := fun y hy => by
    have : f y ∈ (pstd CFSG.Fischer.F4).map f := hPΦ ▸ hDP hy
    exact (mem_map_iff_of_inj f hf).mp this
  have hEc : ∀ x ∈ Db.comap f, ∀ y ∈ Db.comap f, x * y = y * x := fun x hx y hy =>
    hf (by rw [map_mul, map_mul]; exact hDc _ hx _ hy)
  have hEcard : 2 ^ 8 ≤ Nat.card (Db.comap f) := by
    rw [← Subgroup.card_map_of_injective hf, ← hDb]; exact hDcard
  rw [hDb, jUnique_pstd hE hEc hEcard]

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem facts_linear (hL44 : L44Input) (ψ : SL(4, CFSG.Fischer.F4) →* Γ)
    (hψ : Function.Bijective ψ) (τ : Γ →* Γ) (hττ : ∀ g, τ (τ g) = g)
    (χb : msigma CFSG.Fischer.F4 →* Γ) (hχb : Function.Injective χb)
    (hfix : ∀ γ, τ γ = γ ↔ γ ∈ χb.range) {Pb Db : Subgroup Γ} (hPS : IsSylowOf 2 Pb ⊤)
    (hPσ : ∀ A ∈ pSig CFSG.Fischer.F4, χb A ∈ Pb) (hDP : Db ≤ Pb)
    (hDc : ∀ x ∈ Db, ∀ y ∈ Db, x * y = y * x) (hDcard : 2 ^ 8 ≤ Nat.card Db) :
    G1Facts τ χb Pb Db := by
  obtain ⟨Φ, hPΦ, hΦχ, hΦτ⟩ := std_coords_linear hL44 ψ hψ τ hττ χb hχb hfix hPS hPσ
  set f := Φ.toMonoidHom
  have hf : Function.Injective f := Φ.injective
  have hDb := eq_map_radR Φ hPΦ hDP hDc hDcard
  have hPb := hPΦ.symm
  have hj : χb ⟨dω, dω_mem_msigma⟩ = f dω := (hΦχ _).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hPb, hDb]; exact transfer_normalizer f pstd_le_normalizer_radR
  · rw [hPb, hDb]; exact transfer_comm f fun x hx y hy => comm_mem_radR hx hy
  · rw [hPb, hDb]; exact transfer_sq f fun x hx => sq_mem_radR hx
  · intro x hx hxt
    rw [hPb] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 : f y * (τ (f y))⁻¹ = f (y * (sigmaSL CFSG.Fischer.F4 y)⁻¹) := by
      rw [map_mul, map_inv]
      congr 2
      exact hΦτ y
    rw [h1, hDb, mem_map_iff_of_inj f hf] at hxt
    obtain ⟨z, ⟨hzσ, hzP⟩, hzy⟩ := exists_msigma_of_sigma_mem_radR hy hxt
    refine ⟨⟨z, hzσ⟩, Subgroup.mem_subgroupOf.mpr hzP, ?_⟩
    rw [← hΦχ, hDb]
    have : (Φ z)⁻¹ * f y = f (z⁻¹ * y) := by
      rw [map_mul, map_inv]; rfl
    change (Φ z)⁻¹ * f y ∈ _
    rw [this]
    exact ⟨_, hzy, rfl⟩
  · rw [hj, hPb]; exact transfer_g_normalizer f dω_mem_normalizer
  · rw [hj, hPb, hDb]; exact transfer_fix f hf fun x hx h => mem_radR_of_dω hx h

noncomputable abbrev rSig : Subgroup (msigma CFSG.Fischer.F4) :=
  radR.subgroupOf (msigma CFSG.Fischer.F4)

theorem card_rSig : Nat.card rSig = 2 ^ 4 := by
  rw [← card_map_inj _ (msigma CFSG.Fischer.F4).subtype_injective, Subgroup.subgroupOf_map_subtype,
    inf_comm, card_msigma_radR]

theorem jUnique_rSig {E : Subgroup (msigma CFSG.Fischer.F4)} (hE : E ≤ pSig CFSG.Fischer.F4)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcard : 2 ^ 4 ≤ Nat.card E) : E = rSig := by
  set f := (msigma CFSG.Fischer.F4).subtype
  have hf : Function.Injective f := (msigma CFSG.Fischer.F4).subtype_injective
  have hE' : E.map f ≤ msigma CFSG.Fischer.F4 ⊓ pstd CFSG.Fischer.F4 := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x.2, hE hx⟩
  have hc' : ∀ x ∈ E.map f, ∀ y ∈ E.map f, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hc x hx y hy]
  have h := jUnique_pSig hE' hc' (by rw [card_map_inj _ hf]; exact hcard)
  ext x
  have := congrArg (fun H : Subgroup SL(4, CFSG.Fischer.F4) => f x ∈ H) h
  simp only [mem_map_iff_of_inj f hf] at this
  rw [this]
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

theorem pSig_le_normalizer_rSig :
    pSig CFSG.Fischer.F4 ≤ normalizer ((rSig : Subgroup _) : Set (msigma CFSG.Fischer.F4)) := by
  intro y hy
  rw [mem_normalizer_iff]
  intro r
  exact (mem_normalizer_iff.mp (pstd_le_normalizer_radR hy) r).trans Iff.rfl

theorem pSig_comm : ∀ x ∈ pSig CFSG.Fischer.F4, ∀ y ∈ pSig CFSG.Fischer.F4,
    x * y * x⁻¹ * y⁻¹ ∈ rSig := fun _ hx _ hy => comm_mem_radR hx hy

theorem pSig_sq : ∀ x ∈ pSig CFSG.Fischer.F4, x * x ∈ rSig := fun _ hx => sq_mem_radR hx

noncomputable abbrev dωS : msigma CFSG.Fischer.F4 := ⟨dω, dω_mem_msigma⟩

theorem dωS_normalizer : dωS ∈ normalizer ((pSig CFSG.Fischer.F4 : Subgroup _) :
    Set (msigma CFSG.Fischer.F4)) := by
  rw [mem_normalizer_iff]
  intro x
  exact mem_normalizer_iff.mp dω_mem_normalizer x

theorem dωS_fix : ∀ x ∈ pSig CFSG.Fischer.F4, dωS * x * dωS⁻¹ * x⁻¹ ∈ rSig → x ∈ rSig :=
  fun _ hx h => mem_radR_of_dω hx h

section Prod

variable {H : Type*} [Group H] {U J : Subgroup H}

theorem prod_normalizer (h : U ≤ normalizer (J : Set H)) :
    U.prod U ≤ normalizer ((J.prod J : Subgroup (H × H)) : Set (H × H)) := by
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  rw [mem_normalizer_iff]
  rintro ⟨a, b⟩
  simp only [Subgroup.mem_prod, Prod.mk_mul_mk, Prod.inv_mk]
  exact and_congr (mem_normalizer_iff.mp (h hu) a) (mem_normalizer_iff.mp (h hv) b)

theorem prod_comm (h : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ J) :
    ∀ p ∈ U.prod U, ∀ q ∈ U.prod U, p * q * p⁻¹ * q⁻¹ ∈ J.prod J := by
  rintro ⟨u, v⟩ ⟨hu, hv⟩ ⟨u', v'⟩ ⟨hu', hv'⟩
  exact ⟨h u hu u' hu', h v hv v' hv'⟩

theorem prod_sq (h : ∀ x ∈ U, x * x ∈ J) : ∀ p ∈ U.prod U, p * p ∈ J.prod J := by
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  exact ⟨h u hu, h v hv⟩

theorem prod_g_normalizer {g : H} (h : g ∈ normalizer (U : Set H)) :
    (g, g) ∈ normalizer ((U.prod U : Subgroup (H × H)) : Set (H × H)) := by
  rw [mem_normalizer_iff]
  rintro ⟨a, b⟩
  simp only [Subgroup.mem_prod, Prod.mk_mul_mk, Prod.inv_mk]
  exact and_congr (mem_normalizer_iff.mp h a) (mem_normalizer_iff.mp h b)

theorem prod_fix {g : H} (h : ∀ x ∈ U, g * x * g⁻¹ * x⁻¹ ∈ J → x ∈ J) :
    ∀ p ∈ U.prod U, (g, g) * p * (g, g)⁻¹ * p⁻¹ ∈ J.prod J → p ∈ J.prod J := by
  rintro ⟨u, v⟩ ⟨hu, hv⟩ ⟨h1, h2⟩
  exact ⟨h u hu h1, h v hv h2⟩

end Prod

section Unitary

omit [Finite Γ] in
theorem facts_unitary (ψ : SU42b × SU42b ≃* Γ) (τ : Γ →* Γ)
    (hτ : ∀ p, τ (ψ p) = ψ p.swap) (χb : msigma CFSG.Fischer.F4 →* Γ)
    (hχb : Function.Injective χb) (hfix : ∀ A, τ (χb A) = χb A) {Pb Db : Subgroup Γ}
    (hP2 : IsPGroup 2 Pb) (hPc : Nat.card Pb = 2 ^ 12)
    (hPσ : ∀ A ∈ pSig CFSG.Fischer.F4, χb A ∈ Pb) (hDP : Db ≤ Pb)
    (hDc : ∀ x ∈ Db, ∀ y ∈ Db, x * y = y * x) (hDcard : 2 ^ 8 ≤ Nat.card Db) :
    G1Facts τ χb Pb Db := by
  obtain ⟨β, hβ, hdiag, hQ⟩ := std_coords_unitary ψ τ hτ χb hχb hfix hP2 hPc hPσ
  set U := (pSig CFSG.Fischer.F4).map β
  set J := rSig.map β
  have hJ : Nat.card J = 2 ^ 4 := by rw [card_map_inj _ hβ, card_rSig]
  have huniq : ∀ F : Subgroup SU42b, F ≤ U → (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) →
      2 ^ 4 ≤ Nat.card F → F = J := by
    intro F hF hFc hFcard
    have hFr : F ≤ β.range := hF.trans (Subgroup.map_le_range β _)
    have hFe : F = (F.comap β).map β := (Subgroup.map_comap_eq_self hFr).symm
    have hE : F.comap β ≤ pSig CFSG.Fischer.F4 := fun y hy =>
      (mem_map_iff_of_inj β hβ).mp (hF hy)
    have hEc : ∀ x ∈ F.comap β, ∀ y ∈ F.comap β, x * y = y * x := fun x hx y hy =>
      hβ (by rw [map_mul, map_mul]; exact hFc _ hx _ hy)
    rw [hFe, jUnique_rSig hE hEc (by rw [← card_map_inj _ hβ, ← hFe]; exact hFcard)]
  have hle16 : ∀ F : Subgroup SU42b, F ≤ U → (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) →
      Nat.card F ≤ 2 ^ 4 := by
    intro F hF hFc
    by_contra hlt
    have := huniq F hF hFc (by omega)
    rw [this, hJ] at hlt
    exact hlt le_rfl
  set f := ψ.toMonoidHom
  have hf : Function.Injective f := ψ.injective
  have hPb : Pb = (U.prod U).map f := by
    rw [← hQ, Subgroup.map_map]
    ext x
    simp [f]
  set D' := Db.map ψ.symm.toMonoidHom
  have hD'c : Nat.card D' = Nat.card Db :=
    card_map_inj ψ.symm.toMonoidHom ψ.symm.injective Db
  have hD'le : D' ≤ U.prod U := hQ ▸ Subgroup.map_mono hDP
  have hD'comm : ∀ x ∈ D', ∀ y ∈ D', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hDc x hx y hy]
  set F₁ := D'.map (MonoidHom.fst SU42b SU42b)
  set F₂ := D'.map (MonoidHom.snd SU42b SU42b)
  have hF₁U : F₁ ≤ U := by rintro _ ⟨p, hp, rfl⟩; exact (hD'le hp).1
  have hF₂U : F₂ ≤ U := by rintro _ ⟨p, hp, rfl⟩; exact (hD'le hp).2
  have hF₁c : ∀ x ∈ F₁, ∀ y ∈ F₁, x * y = y * x := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    exact congrArg Prod.fst (hD'comm p hp q hq)
  have hF₂c : ∀ x ∈ F₂, ∀ y ∈ F₂, x * y = y * x := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    exact congrArg Prod.snd (hD'comm p hp q hq)
  have hD'F : D' ≤ F₁.prod F₂ := fun p hp => ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩
  have hcardF : 2 ^ 8 ≤ Nat.card F₁ * Nat.card F₂ := by
    rw [← card_prod']
    exact (hD'c ▸ hDcard).trans (Subgroup.card_le_of_le hD'F)
  have h1 := hle16 F₁ hF₁U hF₁c
  have h2 := hle16 F₂ hF₂U hF₂c
  have hF₁16 : 2 ^ 4 ≤ Nat.card F₁ := by
    by_contra h
    have := Nat.mul_le_mul (show Nat.card F₁ ≤ 2 ^ 4 - 1 by omega) h2
    omega
  have hF₂16 : 2 ^ 4 ≤ Nat.card F₂ := by
    by_contra h
    have := Nat.mul_le_mul h1 (show Nat.card F₂ ≤ 2 ^ 4 - 1 by omega)
    omega
  have hF₁J := huniq F₁ hF₁U hF₁c hF₁16
  have hF₂J := huniq F₂ hF₂U hF₂c hF₂16
  have hD'J : D' = J.prod J := by
    have h' := hD'F
    rw [hF₁J, hF₂J] at h'
    refine Subgroup.eq_of_le_of_card_ge h' ?_
    rw [card_prod', hJ, hD'c]
    exact hDcard
  have hDb : Db = (J.prod J).map f := by
    rw [← hD'J, Subgroup.map_map]
    ext x
    simp [f]
  have hUJ : U ≤ normalizer (J : Set SU42b) := transfer_normalizer β pSig_le_normalizer_rSig
  have hUc := transfer_comm β pSig_comm
  have hUs := transfer_sq β pSig_sq
  have hj : χb dωS = f (β dωS, β dωS) := by
    have := hdiag dωS
    rw [← this]; simp [f]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hPb, hDb]; exact transfer_normalizer f (prod_normalizer hUJ)
  · rw [hPb, hDb]; exact transfer_comm f (prod_comm hUc)
  · rw [hPb, hDb]; exact transfer_sq f (prod_sq hUs)
  · intro x hx hxt
    rw [hPb] at hx
    obtain ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩ := hx
    have hτx : τ (f (u, v)) = f (v, u) := hτ (u, v)
    rw [hτx, ← map_inv, ← map_mul, hDb, mem_map_iff_of_inj f hf] at hxt
    obtain ⟨huv, -⟩ := hxt
    simp only [Prod.inv_mk, Prod.mk_mul_mk] at huv
    obtain ⟨A, hA, rfl⟩ := hu
    refine ⟨A, hA, ?_⟩
    have hχA : χb A = f (β A, β A) := by rw [← hdiag A]; simp [f]
    rw [hχA, ← map_inv, ← map_mul, hDb]
    refine ⟨_, ⟨?_, ?_⟩, rfl⟩
    · simp
    · show (β A)⁻¹ * v ∈ J
      have h1 := (mem_normalizer_iff.mp (hUJ (inv_mem (show β A ∈ U from ⟨A, hA, rfl⟩))) _).mp
        (inv_mem huv)
      have e : (β A)⁻¹ * v = (β A)⁻¹ * (β A * v⁻¹)⁻¹ * (β A)⁻¹⁻¹ := by group
      rw [e]
      exact h1
  · rw [hj, hPb]
    exact transfer_g_normalizer f (prod_g_normalizer (transfer_g_normalizer β dωS_normalizer))
  · rw [hj, hPb, hDb]
    exact transfer_fix f hf (prod_fix (transfer_fix β hβ dωS_fix))

end Unitary

section Both

theorem gamma1_facts (hL44 : L44Input) (τ : Γ →* Γ) (hττ : ∀ g, τ (τ g) = g)
    (χb : msigma CFSG.Fischer.F4 →* Γ) (hχb : Function.Injective χb)
    (hfix : ∀ γ, τ γ = γ ↔ γ ∈ χb.range)
    (hcase : Nonempty (SL(4, CFSG.Fischer.F4) ≃* Γ) ∨
      ∃ ψ : SU42b × SU42b ≃* Γ, ∀ p, τ (ψ p) = ψ p.swap)
    {Pb Db : Subgroup Γ} (hP2 : IsPGroup 2 Pb) (hPc : Nat.card Pb = 2 ^ 12)
    (hPσ : ∀ A ∈ pSig CFSG.Fischer.F4, χb A ∈ Pb) (hDP : Db ≤ Pb)
    (hDc : ∀ x ∈ Db, ∀ y ∈ Db, x * y = y * x) (hDcard : 2 ^ 8 ≤ Nat.card Db) :
    G1Facts τ χb Pb Db := by
  rcases hcase with ⟨⟨ψ⟩⟩ | ⟨ψ, hτ⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hΓ : Nat.card Γ = 2 ^ 12 * 240975 := by
      rw [← Nat.card_congr ψ.toEquiv, card_SL4]; norm_num
    have hPS : IsSylowOf 2 Pb ⊤ := isSylowOf_of_card le_top (by
      rw [hPc, Subgroup.card_top, hΓ, factorization_two_mul (by norm_num)])
    exact facts_linear hL44 ψ.toMonoidHom ψ.bijective τ hττ χb hχb hfix hPS hPσ hDP hDc hDcard
  · exact facts_unitary ψ τ hτ χb hχb (fun A => (hfix _).mpr ⟨A, rfl⟩) hP2 hPc hPσ hDP hDc
      hDcard

end Both

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
