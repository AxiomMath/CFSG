module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.SymThreeCoord
public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.OddW
public import CFSG.LocalAnalysis.AGLEmbedding.SymThreeCentralExt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.Open CFSG.AGLEmbedding Subgroup

variable {R : Type} [Group R] [Finite R]

theorem HasLeviCensus.exists_levi_quotient (h : HasLeviCensus R IsWBlock) :
    ∃ (k : ℕ) (G : Fin k → Type) (_ : ∀ j, Group (G j)) (_ : ∀ j, Finite (G j))
      (S : ∀ j, Subgroup (G j)) (Λ : Subgroup (∀ j, G j)) (ψ : ↥Λ →* R ⧸ CFSG.pCore 2 R),
      Function.Surjective ψ ∧ ψ.ker ≤ center ↥Λ ∧ Odd (Nat.card ψ.ker) ∧
      Subgroup.pi Set.univ S ≤ Λ ∧
      Λ ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ j, G j)) ∧
      ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex Λ ∧ ∀ j, S j = ⊥ ∨ IsWBlock ↥(S j) := by
  classical
  obtain ⟨Q, hQgroup, hQfin, σ, k, G, hGgroup, hGfin, S, β, hσ, hc, ho, hβ, hle, hn, hi, hS,
    hZ⟩ := h
  letI : Group Q := hQgroup
  letI : Finite Q := hQfin
  letI : ∀ j, Group (G j) := hGgroup
  letI : ∀ j, Finite (G j) := hGfin
  let Λ : Subgroup (∀ j, G j) := β.range
  let Rhat := R ⧸ CFSG.pCore 2 R
  have hodd : Odd ((Subgroup.pi Set.univ S).relIndex Λ) := by
    rw [← Nat.not_even_iff_odd]
    intro he
    exact hi (Nat.dvd_iff_mod_eq_zero.mpr (Nat.even_iff.mp he))
  have hpcΛ : CFSG.pCore 2 ↥Λ = ⊥ :=
    pCore_two_eq_bot_of_le_normalizer_of_odd_relIndex hle hn hodd hS
  obtain ⟨ψ, hψsurj, -, hψker⟩ :=
    exists_levi_quotient_of_pCore_eq_bot hσ hc ho β hβ hpcΛ
  refine ⟨k, G, hGgroup, hGfin, S, Λ, ψ, hψsurj, ?_, ?_, hle, hn, hi, hS⟩
  ·
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    obtain ⟨z, hz, hzx⟩ := hψker hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨q, hq⟩ := y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [show (x : ∀ j, G j) = β z from (congrArg Subtype.val hzx).symm, ← hq]
    rw [← map_mul, ← map_mul]
    congr 1
    exact (Subgroup.mem_center_iff.mp (hc hz) q)
  ·
    have hD : Nat.card ((σ.ker).map β.rangeRestrict) ∣ Nat.card σ.ker :=
      Subgroup.card_map_dvd (σ.ker) β.rangeRestrict
    have hker : Nat.card ψ.ker ∣ Nat.card ((σ.ker).map β.rangeRestrict) :=
      Subgroup.card_dvd_of_le hψker
    exact ho.of_dvd_nat (hker.trans hD)

theorem HasLeviCensus.normal_of_subnormal_symThree (h : HasLeviCensus R IsWBlock)
    {X : Subgroup (R ⧸ CFSG.pCore 2 R)} (hXs : IsSubnormal X ⊤)
    (hX : TwelveNotLe.Sym.IsSymThree X) : X.Normal := by
  classical
  obtain ⟨k, G, hGgroup, hGfin, S, Λ, ψ, hψsurj, hψcen, hψodd, hSΛ, hΛS, hoddS, hS⟩ :=
    h.exists_levi_quotient
  letI : ∀ j, Group (G j) := hGgroup
  letI : ∀ j, Finite (G j) := hGfin
  obtain ⟨eX⟩ := hX
  let V : Subgroup ↥Λ := X.comap ψ
  have hVs : IsSubnormal V ⊤ := by
    have h' := hXs.comap ψ
    rwa [Subgroup.comap_top] at h'
  let f : ↥V →* Equiv.Perm (Fin 3) := eX.toMonoidHom.comp (ψ.subgroupComap X)
  have hf : Function.Surjective f :=
    eX.surjective.comp (ψ.subgroupComap_surjective_of_surjective X hψsurj)
  have hfker : ∀ x : ↥V, x ∈ f.ker ↔ (x : ↥Λ) ∈ ψ.ker := by
    intro x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact Subtype.ext_iff
  have hkerV : ψ.ker ≤ V := by
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact X.one_mem
  have hc : ∀ k ∈ f.ker, ∀ q : ↥V, k * q = q * k := by
    intro x hx y
    have hxc : (x : ↥Λ) ∈ Subgroup.center ↥Λ := hψcen ((hfker x).mp hx)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (Subgroup.mem_center_iff.mp hxc (y : ↥Λ)).symm
  have hodd : Odd (Nat.card f.ker) := by
    have hfk : f.ker = ψ.ker.subgroupOf V := by
      ext x
      rw [hfker, Subgroup.mem_subgroupOf]
    rw [hfk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerV).toEquiv]
    exact hψodd
  obtain ⟨U₀, hU₀n, ⟨e₀⟩, -⟩ :=
    CFSG.AGLEmbedding.SymThreeCentralExt.exists_normal_symThree f hf hc hodd
  let U₀' : Subgroup ↥Λ := U₀.map V.subtype
  let U : Subgroup (∀ j, G j) := U₀'.map Λ.subtype
  have hU₀'le : U₀' ≤ V := Subgroup.map_subtype_le U₀
  have hU₀'normalV : (U₀'.subgroupOf V).Normal := by
    rw [show U₀'.subgroupOf V = U₀ from
      Subgroup.comap_map_eq_self_of_injective V.subtype_injective U₀]
    exact hU₀n
  have hU₀'sub : IsSubnormal U₀' ⊤ :=
    IsSubnormal.step hU₀'le hU₀'normalV hVs
  have hUs : IsSubnormal U Λ := by
    have h' := hU₀'sub.map Λ.subtype
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h'
  have eU : ↥U ≃* Equiv.Perm (Fin 3) :=
    ((U₀'.equivMapOfInjective Λ.subtype Λ.subtype_injective).symm.trans
      (U₀.equivMapOfInjective V.subtype V.subtype_injective).symm).trans e₀
  have hUleΛ : U ≤ Λ := Subgroup.map_subtype_le U₀'
  have hΛN : Λ ≤ normalizer (U : Set (∀ j, G j)) :=
    le_normalizer_of_subnormal_symThree hSΛ hΛS hoddS hS hUs ⟨eU⟩
  have hU₀'normal : U₀'.Normal := by
    have h := (Subgroup.normal_subgroupOf_iff_le_normalizer hUleΛ).mpr hΛN
    rwa [show U.subgroupOf Λ = U₀' from
      Subgroup.comap_map_eq_self_of_injective Λ.subtype_injective U₀'] at h
  have hCbot : Subgroup.center ↥U₀' = ⊥ := by
    have hpermbot : Subgroup.center (Equiv.Perm (Fin 3)) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hdec : ∀ x : Equiv.Perm (Fin 3),
          x ∈ Subgroup.center (Equiv.Perm (Fin 3)) → x = 1 := by decide
      exact Subgroup.mem_bot.mpr (hdec x hx)
    let e : ↥U₀' ≃* Equiv.Perm (Fin 3) :=
      (U₀.equivMapOfInjective V.subtype V.subtype_injective).symm.trans e₀
    rw [eq_bot_iff]
    intro x hx
    have hx' : e x ∈ Subgroup.center (Equiv.Perm (Fin 3)) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul]
      exact congrArg e (hx z)
    rw [hpermbot, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    exact e.injective (by rw [hx', map_one])
  have hker_bot : (ψ.comp U₀'.subtype).ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxψ : (x : ↥Λ) ∈ ψ.ker := hx
    have hxc : x ∈ Subgroup.center ↥U₀' := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (Subgroup.mem_center_iff.mp (hψcen hxψ) (w : ↥Λ))
    rwa [hCbot, Subgroup.mem_bot] at hxc
  have hinj : Function.Injective (ψ.comp U₀'.subtype) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker_bot
  have hcardmap : Nat.card (U₀'.map ψ) = 6 := by
    have hr : (ψ.comp U₀'.subtype).range = U₀'.map ψ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hr, (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm]
    rw [← Nat.card_congr (U₀.equivMapOfInjective V.subtype V.subtype_injective).toEquiv,
      Nat.card_congr e₀.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
    rfl
  have hUX : U₀'.map ψ = X := by
    have hle : U₀'.map ψ ≤ X := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_comap.mp (hU₀'le hx)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcardmap, TwelveNotLe.Sym.card_symThree ⟨eX⟩]
  rw [← hUX]
  exact Subgroup.Normal.map hU₀'normal ψ hψsurj

end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
