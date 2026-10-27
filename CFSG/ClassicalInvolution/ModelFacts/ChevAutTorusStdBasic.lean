module

public import CFSG.LieType.Steinberg.Bridge
public import CFSG.LieType.Steinberg.Bruhat
public import CFSG.LieType.Steinberg.Collection

public section

namespace CFSG.ClassicalInvolution.ModelFacts.ChevAut

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg
open scoped commutatorElement

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

section Pos

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
include hct hext

theorem eq_one_of_mem_posUnipotent_of_forall_conj_of_le {S : Subgroup K} (hS : S ≤ ⨆ i, H i)
    (hno : ∀ γ ∈ D.roots, ∃ t ∈ S, ∀ y ∈ D.rootGroup γ, t * y * t⁻¹ = y → y = 1)
    {u : K} (hu : u ∈ posUnipotent D) (hcomm : ∀ t ∈ S, t * u * t⁻¹ = u) : u = 1 := by
  obtain ⟨L, hnd, hL, hs, hinj⟩ := (isSteinberg_of hct hext).exists_posList
  have hr : ∀ γ ∈ L, γ ∈ D.roots := fun γ hγ => ((hL γ).1 hγ).1.1
  have hT : ∀ t ∈ ⨆ i, H i, ∀ γ ∈ D.roots, ∀ y ∈ D.rootGroup γ, t * y * t⁻¹ ∈ D.rootGroup γ := by
    intro t ht γ hγ y hy
    exact (Subgroup.mem_normalizer_iff.1 (iSup_le_normalizer_rootGroup hct hγ ht) y).1 hy
  have hle : posUnipotent D ≤ ⨆ v ∈ L, D.rootGroup v := by
    refine iSup₂_le fun γ hγ => ?_
    by_cases hind : (RootSystem.ofCartan D.isFiniteType D.divisible).IsIndiv γ
    · exact le_iSup₂_of_le γ ((hL γ).2 ⟨hγ, hind⟩) le_rfl
    · obtain ⟨δ, hδ, hδ', rfl⟩ :=
        (RootSystem.ofCartan D.isFiniteType D.divisible).exists_eq_two_smul hγ.1 hind
      exact (hext.two_smul_le δ hδ hγ.1).trans (le_iSup₂_of_le δ ((hL δ).2 ⟨
        (RootSystem.ofCartan D.isFiniteType D.divisible).mem_pos_of_two_smul_mem_pos hγ hδ,
        hδ'⟩) le_rfl)
  have hc : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → ∀ x ∈ D.rootGroup a, ∀ y ∈ D.rootGroup b,
      ⁅x, y⁆ ∈ ⨆ c ∈ L, ⨆ (_ : min (ht a) (ht b) < ht c), D.rootGroup c := by
    intro a ha b hb hab x hx y hy
    have hxy := hext.commutator_mem a (hr a ha) b (hr b hb)
      ((RootSystem.ofCartan D.isFiniteType D.divisible).linIndepPair_of_mem_pos ((hL a).1 ha).1
        ((hL a).1 ha).2 ((hL b).1 hb).1 ((hL b).1 hb).2 hab) x hx y hy
    have hle' : (⨆ ε ∈ openCone D.roots a b, D.rootGroup ε) ≤
        ⨆ c ∈ L, ⨆ (_ : min (ht a) (ht b) < ht c), D.rootGroup c := by
      refine iSup₂_le fun ε hε => ?_
      obtain ⟨c, hc, hlt, hcε⟩ :=
        (RootSystem.ofCartan D.isFiniteType D.divisible).exists_of_mem_openCone_pos
          ((hL a).1 ha).1 ((hL a).1 ha).2 ((hL b).1 hb).1 ((hL b).1 hb).2 hab hε
      have hcL : c ∈ L := (hL c).2 hc
      have hle : D.rootGroup ε ≤ D.rootGroup c := by
        rcases hcε with rfl | rfl
        · exact le_rfl
        · exact hext.two_smul_le c (hr c hcL) hε.1
      exact hle.trans (le_iSup₂_of_le c hcL (le_iSup_of_le hlt le_rfl))
    exact hle' hxy
  obtain ⟨f, hf, rfl⟩ := exists_prod_eq_of_commutator_mem D.rootGroup (fun γ => ht γ) hnd hs hc
    u (hle hu)
  have hfix : ∀ t ∈ S, ∀ γ ∈ L, t * f γ * t⁻¹ = f γ := by
    intro t ht
    have hmap : (L.map fun γ => t * f γ * t⁻¹).prod = t * (L.map f).prod * t⁻¹ := by
      have := map_list_prod (MulAut.conj t).toMonoidHom (L.map f)
      simpa [List.map_map, Function.comp_def] using this.symm
    exact hinj (fun γ => t * f γ * t⁻¹) f (fun γ hγ => hT t (hS ht) γ (hr γ hγ) _ (hf γ hγ)) hf
      (by rw [hmap]; exact hcomm t ht)
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hx
  obtain ⟨t, ht, hno'⟩ := hno γ (hr γ hγ)
  exact hno' (f γ) (hf γ hγ) (hfix t ht γ hγ)


variable (hBU : BruhatExtras D H)
include hBU

theorem exists_mem_mul_nrep_of_forall_conj_mem_of_le {S : Subgroup K} (hS : S ≤ ⨆ i, H i)
    (hno : ∀ γ ∈ D.roots, ∃ t ∈ S, ∀ y ∈ D.rootGroup γ, t * y * t⁻¹ = y → y = 1)
    {g : K} (hg : ∀ t ∈ S, g * t * g⁻¹ ∈ ⨆ i, H i) :
    ∃ h ∈ ⨆ i, H i, ∃ w, g = h * nrep hct w := by
  obtain ⟨⟨w, b, u⟩, ⟨⟨hb, hu⟩, hgbu⟩, -⟩ := existsUnique_bruhat_normalForm hct hext hBU g
  simp only at hb hu hgbu
  have hTU : ∀ t ∈ ⨆ i, H i, ∀ v ∈ inversionUnipotent D w,
      t⁻¹ * v * t ∈ inversionUnipotent D w := by
    have hle : (⨆ i, H i) ≤ Subgroup.normalizer (inversionUnipotent D w : Set K) :=
      le_normalizer_iSup₂ fun x hx γ hγ y hy =>
        (le_iSup₂ (f := fun γ (_ : γ ∈ {γ | γ ∈ D.roots ∧ 0 < ht γ ∧
          ht (weylAction D.isFiniteType w γ) < 0}) => D.rootGroup γ) γ hγ)
          ((Subgroup.mem_normalizer_iff.1 (iSup_le_normalizer_rootGroup hct hγ.1 hx) y).1 hy)
    intro t ht v hv
    have := (Subgroup.mem_normalizer_iff.1 (hle (inv_mem ht)) v).1 hv
    simpa using this
  have hn : ∀ t ∈ ⨆ i, H i, nrep hct w * t * (nrep hct w)⁻¹ ∈ ⨆ i, H i := fun t ht =>
    conj_mem_iSup_of_mem_weylN hct (nrep_mem_weylN hct w) ht
  have key : ∀ t ∈ S, t⁻¹ * u * t = u := by
    intro t ht
    have hτ := hg t ht
    have hu₁ := hTU t (hS ht) u hu
    have hv : nrep hct w * (t⁻¹ * u * t * u⁻¹) * (nrep hct w)⁻¹ ∈ negUnipotent D :=
      nrep_conj_mem_negUnipotent hct (mul_mem hu₁ (inv_mem hu))
    have e1 : nrep hct w * (t⁻¹ * u * t * u⁻¹) * (nrep hct w)⁻¹ =
        (nrep hct w * t * (nrep hct w)⁻¹)⁻¹ * (b⁻¹ * (g * t * g⁻¹) * b) := by
      rw [hgbu]; group
    have hvB : nrep hct w * (t⁻¹ * u * t * u⁻¹) * (nrep hct w)⁻¹ ∈ borel D H := by
      rw [e1]
      exact mul_mem (inv_mem (iSup_le_borel (hn t (hS ht))))
        (mul_mem (mul_mem (inv_mem hb) (iSup_le_borel hτ)) hb)
    have h1 : nrep hct w * (t⁻¹ * u * t * u⁻¹) * (nrep hct w)⁻¹ = 1 := by
      have := Subgroup.mem_inf.2 ⟨hvB, hv⟩
      rwa [hBU.borel_inf_negUnipotent, Subgroup.mem_bot] at this
    have h3 : t⁻¹ * u * t * u⁻¹ = 1 := by
      calc t⁻¹ * u * t * u⁻¹ = (nrep hct w)⁻¹ * (nrep hct w * (t⁻¹ * u * t * u⁻¹) *
          (nrep hct w)⁻¹) * nrep hct w := by group
        _ = 1 := by rw [h1]; group
    exact mul_inv_eq_one.1 h3
  have huU : u ∈ posUnipotent D := inversionUnipotent_le_posUnipotent w hu
  have hu1 : u = 1 := by
    refine eq_one_of_mem_posUnipotent_of_forall_conj_of_le hct hext hS hno huU fun t ht => ?_
    have := key t⁻¹ (inv_mem ht)
    simpa using this
  rw [hu1, mul_one] at hgbu
  set S' : Subgroup K := S.map (MulAut.conj (nrep hct w)).toMonoidHom with hS'def
  have hS' : S' ≤ ⨆ i, H i := by
    rintro _ ⟨s, hs, rfl⟩
    exact hn s (hS hs)
  have hno' : ∀ γ ∈ D.roots, ∃ t ∈ S', ∀ y ∈ D.rootGroup γ, t * y * t⁻¹ = y → y = 1 := by
    intro γ hγ
    have hγ' : weylAction D.isFiniteType w⁻¹ γ ∈ D.roots := weylAction_mem_roots _ _ hγ
    obtain ⟨t, ht, hnot⟩ := hno _ hγ'
    refine ⟨nrep hct w * t * (nrep hct w)⁻¹, ⟨t, ht, rfl⟩, fun y hy hfix => ?_⟩
    have hy' : (nrep hct w)⁻¹ * y * nrep hct w ∈
        D.rootGroup (weylAction D.isFiniteType w⁻¹ γ) :=
      (actsAs_nrep hct w).inv_conj_mem hγ hy
    have h1 := hnot _ hy' (by
      calc t * ((nrep hct w)⁻¹ * y * nrep hct w) * t⁻¹
          = (nrep hct w)⁻¹ * ((nrep hct w * t * (nrep hct w)⁻¹) * y *
              (nrep hct w * t * (nrep hct w)⁻¹)⁻¹) * nrep hct w := by group
        _ = (nrep hct w)⁻¹ * y * nrep hct w := by rw [hfix])
    calc y = nrep hct w * ((nrep hct w)⁻¹ * y * nrep hct w) * (nrep hct w)⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hbT : ∀ s ∈ S', b * s * b⁻¹ ∈ ⨆ i, H i := by
    rintro _ ⟨s, hs, rfl⟩
    have e : b * (nrep hct w * s * (nrep hct w)⁻¹) * b⁻¹ = g * s * g⁻¹ := by
      rw [hgbu]; group
    change b * (nrep hct w * s * (nrep hct w)⁻¹) * b⁻¹ ∈ ⨆ i, H i
    rw [e]
    exact hg s hs
  rw [← SetLike.mem_coe, coe_borel hct, Set.mem_mul] at hb
  obtain ⟨h₀, hh₀, u₀, hu₀, rfl⟩ := hb
  have hu₀1 : u₀ = 1 := by
    refine eq_one_of_mem_posUnipotent_of_forall_conj_of_le hct hext hS' hno' hu₀ fun s hs => ?_
    have h1 := hbT s hs
    have h2 : u₀ * s * u₀⁻¹ ∈ ⨆ i, H i := by
      have := mul_mem (mul_mem (inv_mem hh₀) h1) hh₀
      simpa [mul_assoc] using this
    have h3 : u₀ * s * u₀⁻¹ * s⁻¹ ∈ posUnipotent D := by
      have hsU : s * u₀⁻¹ * s⁻¹ ∈ posUnipotent D := by
        have := (Subgroup.mem_normalizer_iff.1
          (borel_le_normalizer_posUnipotent hct (iSup_le_borel (hS' hs))) u₀⁻¹).1 (inv_mem hu₀)
        exact this
      simpa [mul_assoc] using mul_mem hu₀ hsU
    have h4 : u₀ * s * u₀⁻¹ * s⁻¹ ∈ ⨆ i, H i := mul_mem h2 (inv_mem (hS' hs))
    have h5 : u₀ * s * u₀⁻¹ * s⁻¹ = 1 := by
      have h0 : (⨆ i, H i) ⊓ posUnipotent D = ⊥ := hext.torus_inf_posPart
      have := Subgroup.mem_inf.2 ⟨h4, h3⟩
      rwa [h0, Subgroup.mem_bot] at this
    have h6 : u₀ * s = s * u₀ :=
      calc u₀ * s = (u₀ * s * u₀⁻¹ * s⁻¹) * (s * u₀) := by group
        _ = s * u₀ := by rw [h5, one_mul]
    calc s * u₀ * s⁻¹ = u₀ * s * s⁻¹ := by rw [← h6]
      _ = u₀ := by group
  rw [hu₀1, mul_one] at hgbu
  exact ⟨h₀, hh₀, w, hgbu⟩

end Pos

end CFSG.ClassicalInvolution.ModelFacts.ChevAut
